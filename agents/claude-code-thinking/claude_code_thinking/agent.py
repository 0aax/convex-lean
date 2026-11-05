from __future__ import annotations

from harbor.agents.installed.base import CliFlag
from harbor.agents.installed.claude_code import ClaudeCode

from .gate import GateMixin

class ClaudeCodeThinking(ClaudeCode):

    CLI_FLAGS = ClaudeCode.CLI_FLAGS + [
        CliFlag(
            "thinking_display",
            cli="--thinking-display",
            type="enum",
            choices=["summarized", "omitted"],
        ),
    ]

    @staticmethod
    def name() -> str:
        return "claude-code-thinking"


class GatedClaudeCodeThinking(GateMixin, ClaudeCodeThinking):
    """ClaudeCodeThinking under the gated loop (see gate.py): the trial ends
    only on an accepted `submit`, the cost cap, or the time limit."""

    @staticmethod
    def name() -> str:
        return "claude-code-thinking-gated"
