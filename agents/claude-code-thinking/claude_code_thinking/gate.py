"""Gated agent loop: a trial ends only on an accepted submission or a cap.

After each agent turn the loop checks for /logs/agent/gate/accepted, which
the in-sandbox `submit` command writes when the comparator accepts a proof. If
the flag is absent and no cap is reached, the loop resumes the same agent
session with one fixed message and the agent continues. `submit` reports
rejections to the agent itself, so the loop has a single message.

A run can also stop early when the agent has gone idle: a run of cycles that
make no tool call and produce little output, which is an agent repeating a
refusal to the continue message rather than working. That guard is off unless
gate_idle_cycles is set.

Built on Harbor's agent contract only: `run()` for the first turn and the
agent's native resume flag for every later one, so the mixin composes with any
installed agent that sets SUPPORTS_RESUME.
"""
from __future__ import annotations

import base64
import json
import time
from collections import namedtuple
from typing import Any

from harbor.agents.installed.base import NonZeroAgentExitCodeError
from tenacity import (
    retry,
    retry_if_exception_type,
    stop_after_attempt,
    wait_exponential,
)

# Transient environment errors worth retrying, mirroring how Harbor's own Daytona
# calls retry. Imported softly so the mixin still loads without Daytona (the empty
# tuple simply makes the retry a no-op for other environments). Permanent errors
# (bad request, not found, auth) are deliberately excluded so we never retry a
# failure that cannot succeed, e.g. the disk-limit rejection.
try:
    from daytona.common.errors import (
        DaytonaBadGatewayError,
        DaytonaConnectionError,
        DaytonaInternalServerError,
        DaytonaServiceUnavailableError,
        DaytonaTimeoutError,
    )

    _TRANSIENT_ENV_ERRORS: tuple[type[BaseException], ...] = (
        DaytonaBadGatewayError,
        DaytonaServiceUnavailableError,
        DaytonaInternalServerError,
        DaytonaConnectionError,
        DaytonaTimeoutError,
    )
except Exception:  # pragma: no cover - Daytona not installed
    _TRANSIENT_ENV_ERRORS = ()

GATE_DIR = "/logs/agent/gate"
DEFAULT_CONTINUE_MESSAGE = (
    "Continue working on the problem. "
    "What is the most promising next step you have not yet tried? "
    "When you have a complete proof, run `submit pos` or `submit neg`."
)
# Result subtype Claude Code emits when an invocation stops on --max-budget-usd.
# The process exits nonzero in that case, like every error result; the loop
# treats this one as the expected end of a run rather than a failure.
BUDGET_SUBTYPE = "error_max_budget_usd"

# One cycle's reading of the just-finished invocation's stream.
Snap = namedtuple("Snap", "cost subtype output_tokens root_tools accepted")


class GateMixin:
    """Compose as `class Gated(GateMixin, SomeInstalledAgent)`.

    Kwargs (all optional): gate_cap_usd, gate_time_limit_sec, gate_max_cycles,
    gate_continue_message, gate_idle_cycles, gate_idle_max_output_tokens.
    """

    STREAM_FILENAME = "claude-code.txt"

    def __init__(
        self,
        *args: Any,
        gate_cap_usd: float | str | None = None,
        gate_time_limit_sec: float | str | None = None,
        gate_max_cycles: int | str = 100_000,
        gate_continue_message: str | None = None,
        gate_idle_cycles: int | str = 0,
        gate_idle_max_output_tokens: int | str = 2000,
        **kwargs: Any,
    ):
        self._gate_cap_usd = float(gate_cap_usd) if gate_cap_usd is not None else None
        self._gate_time_limit_sec = (
            float(gate_time_limit_sec) if gate_time_limit_sec is not None else None
        )
        self._gate_max_cycles = int(gate_max_cycles)
        self._gate_continue_message = gate_continue_message or DEFAULT_CONTINUE_MESSAGE
        # gate_idle_cycles == 0 disables the idle guard entirely.
        self._gate_idle_cycles = int(gate_idle_cycles)
        self._gate_idle_max_output_tokens = int(gate_idle_max_output_tokens)
        self._gate_idle_streak = 0
        self._gate_total_cost: float | None = None
        super().__init__(*args, **kwargs)

    async def run(self, instruction, environment, context) -> None:  # type: ignore[override]
        if not getattr(self, "SUPPORTS_RESUME", False):
            raise ValueError(
                f"{type(self).__name__}: the gated loop needs an agent with SUPPORTS_RESUME"
            )
        started = time.monotonic()
        self._gate_total_cost = 0.0
        self._gate_idle_streak = 0
        await self._gate_exec(environment, f"mkdir -p {GATE_DIR}/attempts", user="root")
        error = await self._gate_turn(super().run(instruction, environment, context))

        cycle = 0
        while True:
            cycle += 1
            snap = await self._gate_snapshot(environment, cycle)
            self._gate_total_cost += snap.cost
            idle = snap.root_tools == 0 and snap.output_tokens <= self._gate_idle_max_output_tokens
            self._gate_idle_streak = self._gate_idle_streak + 1 if idle else 0
            elapsed = time.monotonic() - started
            reason = self._gate_stop_reason(
                snap, self._gate_total_cost, elapsed, cycle, error
            )
            await self._gate_log(
                environment, cycle, snap, self._gate_total_cost, elapsed, reason
            )
            if reason:
                # An exit that is neither an accepted submission nor the budget
                # flag is a real failure; it is logged above, then propagated.
                if error is not None and snap.subtype != BUDGET_SUBTYPE:
                    raise error
                break
            self._gate_apply_remaining_budget(self._gate_total_cost)
            error = await self._gate_turn(self._gate_resume(environment, context))

    @staticmethod
    async def _gate_turn(turn) -> NonZeroAgentExitCodeError | None:
        """Await one agent invocation; a nonzero exit is returned, not raised, so
        the turn is still snapshotted and logged."""
        try:
            await turn
        except NonZeroAgentExitCodeError as exc:
            return exc
        return None

    async def _gate_resume(self, environment, context) -> None:
        """Run one continue turn in the same session, bypassing the prompt template."""
        saved_template = self._prompt_template_path
        self._prompt_template_path = None
        self._resume = True
        try:
            await super().run(self._gate_continue_message, environment, context)
        finally:
            self._resume = False
            self._prompt_template_path = saved_template

    @retry(
        retry=retry_if_exception_type(_TRANSIENT_ENV_ERRORS),
        stop=stop_after_attempt(5),
        wait=wait_exponential(multiplier=1, min=1, max=30),
        reraise=True,
    )
    async def _gate_exec(self, environment, command, **kwargs):
        """Run one loop-bookkeeping command, retrying transient environment errors
        the way Harbor's own Daytona calls do. These commands are quick and
        idempotent, so a retry is always safe; non-transient errors propagate
        unchanged. When Daytona is absent the retry predicate never matches, so
        this is a plain passthrough."""
        return await environment.exec(command, **kwargs)

    async def _gate_snapshot(self, environment, cycle: int) -> Snap:
        """Copy this invocation's stream to claude-code.NNN.txt (the next run
        overwrites the live file) and read, in one command, its root tool-call
        count, the accepted flag, and its last result record. `tee` leaves only
        the current invocation in the live file, so every count is this cycle's."""
        stream = (self.environment_logs_dir / self.STREAM_FILENAME).as_posix()
        snap = (self.environment_logs_dir / f"claude-code.{cycle:03d}.txt").as_posix()
        cmd = (
            f"cp -f {stream} {snap} 2>/dev/null || true; "
            f"printf 'TOOLS=%s\\n' \"$(grep -a '\"type\":\"tool_use\"' {stream} 2>/dev/null "
            f"| grep -c '\"parent_tool_use_id\":null')\"; "
            f"printf 'ACCEPTED=%s\\n' \"$(cat {GATE_DIR}/accepted 2>/dev/null)\"; "
            f"grep -a '\"type\":\"result\"' {stream} 2>/dev/null | tail -n 1"
        )
        res = await self._gate_exec(environment, cmd)
        root_tools, accepted, result_line = 0, "", ""
        for ln in (res.stdout or "").splitlines():
            if ln.startswith("TOOLS="):
                try:
                    root_tools = int(ln[len("TOOLS="):].strip() or 0)
                except ValueError:
                    root_tools = 0
            elif ln.startswith("ACCEPTED="):
                accepted = ln[len("ACCEPTED="):].strip()
            elif ln.lstrip().startswith("{"):
                result_line = ln
        cost, subtype, output_tokens = 0.0, None, 0
        if result_line:
            try:
                rec = json.loads(result_line)
                c = rec.get("total_cost_usd")
                cost = float(c) if isinstance(c, (int, float)) else 0.0
                st = rec.get("subtype")
                subtype = st if isinstance(st, str) else None
                ot = (rec.get("usage") or {}).get("output_tokens")
                output_tokens = int(ot) if isinstance(ot, int) else 0
            except (ValueError, TypeError):
                pass
        return Snap(cost, subtype, output_tokens, root_tools, accepted)

    def _gate_stop_reason(
        self,
        snap: Snap,
        total_cost: float,
        elapsed: float,
        cycle: int,
        error: Exception | None,
    ) -> str | None:
        if snap.accepted:
            return f"accepted:{snap.accepted}"
        if error is not None:
            if snap.subtype == BUDGET_SUBTYPE:
                return f"budget_flag:{total_cost:.2f}"
            return f"agent_error:{type(error).__name__}"
        if self._gate_cap_usd is not None and total_cost >= self._gate_cap_usd:
            return f"cost_cap:{total_cost:.2f}>={self._gate_cap_usd:.2f}"
        if self._gate_time_limit_sec is not None and elapsed >= self._gate_time_limit_sec:
            return f"time_limit:{elapsed:.0f}s"
        if self._gate_idle_cycles and self._gate_idle_streak >= self._gate_idle_cycles:
            return f"idle:{self._gate_idle_streak}"
        if cycle >= self._gate_max_cycles:
            return f"max_cycles:{cycle}"
        return None

    def _gate_apply_remaining_budget(self, total_cost: float) -> None:
        """Set the CLI's own budget flag to the remaining cap for the next invocation."""
        if self._gate_cap_usd is None:
            return
        flags = getattr(self, "_resolved_flags", None)
        if not isinstance(flags, dict) or "max_budget_usd" not in flags:
            return
        remaining = max(self._gate_cap_usd - total_cost, 1.0)
        flags["max_budget_usd"] = f"{remaining:.2f}"

    async def _gate_log(
        self, environment, cycle, snap: Snap, total_cost, elapsed, reason
    ) -> None:
        line = json.dumps(
            {
                "cycle": cycle,
                "invocation_cost_usd": round(snap.cost, 4),
                "total_cost_usd": round(total_cost, 4),
                "elapsed_sec": round(elapsed, 1),
                "root_tool_calls": snap.root_tools,
                "output_tokens": snap.output_tokens,
                "idle_streak": self._gate_idle_streak,
                "stop": reason,
            }
        )
        # Passed through base64 so no character of the record meets the shell.
        payload = base64.b64encode((line + "\n").encode()).decode()
        await self._gate_exec(
            environment, f"printf %s {payload} | base64 -d >> {GATE_DIR}/cycles.jsonl"
        )

    def _parse_total_cost_from_stream_json(self) -> float | None:
        """The stream file holds only the last invocation; the trajectory's final
        metrics should carry the loop's total across all of them."""
        if self._gate_total_cost is not None:
            return self._gate_total_cost
        return super()._parse_total_cost_from_stream_json()

    def populate_context_post_run(self, context) -> None:  # type: ignore[override]
        super().populate_context_post_run(context)
        if self._gate_total_cost is not None:
            context.cost_usd = round(self._gate_total_cost, 6)
