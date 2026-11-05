"""Extract the writing-profile dataset from the open-problem histories.

Reads the histories in jobs/open-problems-final/ and writes data/events.jsonl and data/trials.json, the inputs of the plots here. A
history is the trials of one problem under one budget (<budget>/<problem>__<id>/),
ordered by the agent execution window in their result.json; two trials mean the
first stopped early and the second resumed it.

An event is one literal write or edit the agent made in a tool call: a `Write`,
the replacement text of an `Edit`, or, in a `Bash` command, a heredoc piped to
cat/tee, a literal string written by an inline Python script, or the added
lines of an apply_patch. Payloads are recovered statically from the Claude Code
session logs (agent/sessions/**/*.jsonl); nothing is executed. Each event gets
the file's category (Writeups: .md/.markdown/.tex; Lean: .lean; Code: the
CODE_EXTS) and `first_seen_lines`, the nonblank lines not previously written to
that path in that history. Lines in imported environments (.lake, venvs,
node_modules, ...) are skipped.

Time is the history's observed clock: for each phase (one trial, or the
original trial and its resume) the window runs from the agent's start to its
last logged event, and the phases are concatenated, so resume gaps and the
unobserved tail after the last log line are excluded. A resumed trial's logs
carry the whole session, so logs are read from every phase and tool calls are
deduplicated by id.

The parser is the one the paper's figures were made with; the self-test
exercises its shell and Python forms.

    uv run python scripts/open-problems/profile_plots/extract_events.py
    uv run python scripts/open-problems/profile_plots/extract_events.py --self-test
"""
import argparse
import ast
from collections import Counter, defaultdict
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import warnings

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FINAL = ROOT / "jobs" / "open-problems-final"
DATA = HERE / "data"

CATS = ("Writeups", "Lean", "Code")
CODE_EXTS = {".py", ".sage", ".jl", ".c", ".cpp", ".cc", ".h", ".hpp",
             ".js", ".ts", ".sh", ".bash", ".r", ".rs", ".m"}
SKIP_PARTS = {".lake", ".git", "node_modules", "site-packages", "venv", ".venv", "__pycache__"}
DEFAULT_CWD = "/app/open-eval"


def dt(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def category(path):
    p = PurePosixPath(path)
    if any(part in SKIP_PARTS for part in p.parts):
        return None
    ext = p.suffix.lower()
    return "Lean" if ext == ".lean" else "Writeups" if ext in {".md", ".markdown", ".tex"} else "Code" if ext in CODE_EXTS else None


def normpath(path, cwd):
    if not isinstance(path, str) or not path or any(c in path for c in "$`\n"):
        return None
    if not path.startswith("/"):
        path = cwd.rstrip("/") + "/" + path
    return os.path.normpath(path)


def cwd_after(header, cwd):
    # Only literal cd operands; no execution, substitutions, or shell expansion.
    for m in re.finditer(r"(?:^|&&|;|\n)\s*cd\s+(\"[^\"]*\"|'[^']*'|[^\s;&|]+)", header):
        try:
            new = normpath(shlex.split(m[1])[0], cwd)
            if new:
                cwd = new
        except ValueError:
            pass
    return cwd


def python_payloads(source, cwd):
    """Recover literal writes/replacement RHS strings using static AST inspection.

    We deliberately do not evaluate imported code, loops, format expressions,
    computed filenames, generated data, or arbitrary Python expressions.
    """
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", SyntaxWarning)
            tree = ast.parse(source)
    except (SyntaxError, ValueError):
        return []
    values, origins, handles = {}, {}, {}
    replacements, writes = [], []

    def literal(n):
        if isinstance(n, ast.Constant) and isinstance(n.value, str):
            return n.value
        if isinstance(n, ast.Name):
            return values.get(n.id)
        if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Add):
            a, b = literal(n.left), literal(n.right)
            return a + b if a is not None and b is not None else None
        return None

    def file_expr(n):
        if isinstance(n, ast.Name):
            return handles.get(n.id) or origins.get(n.id)
        if isinstance(n, ast.Call):
            f = n.func
            if isinstance(f, ast.Name) and f.id in {"open", "Path"} and n.args:
                return normpath(literal(n.args[0]), cwd)
            if isinstance(f, ast.Attribute):
                if f.attr == "Path" and n.args:
                    return normpath(literal(n.args[0]), cwd)
                return file_expr(f.value)
        return None

    # ast.walk is breadth-first; source ordering is needed for literal bindings.
    nodes = sorted(ast.walk(tree), key=lambda n: (getattr(n, "lineno", 0), getattr(n, "col_offset", 0)))
    for n in nodes:
        if isinstance(n, ast.With):
            for item in n.items:
                if isinstance(item.optional_vars, ast.Name):
                    p = file_expr(item.context_expr)
                    if p:
                        handles[item.optional_vars.id] = p
        if isinstance(n, (ast.Assign, ast.AnnAssign)):
            targets = n.targets if isinstance(n, ast.Assign) else [n.target]
            for target in targets:
                if isinstance(target, ast.Name):
                    val = literal(n.value)
                    if val is not None:
                        values[target.id] = val
                    else:
                        values.pop(target.id, None)
                    p = file_expr(n.value)
                    if p:
                        origins[target.id] = p
        if not isinstance(n, ast.Call) or not isinstance(n.func, ast.Attribute):
            continue
        p = file_expr(n.func.value)
        if not p:
            continue
        if n.func.attr == "replace" and len(n.args) >= 2:
            val = literal(n.args[1])
            if val is not None:
                replacements.append((p, val, "python_literal_replacement"))
        elif n.func.attr in {"write", "write_text"} and n.args:
            val = literal(n.args[0])
            writes.append((p, val))
    out = []
    for p, val in writes:
        if val is not None:
            out.append((p, val, "python_literal_write"))
        else:
            out.extend(r for r in replacements if r[0] == p)
    # One replacement can appear before several write calls; avoid parser duplicates.
    return list(dict.fromkeys(out))


def shell_payloads(command, cwd):
    result = []
    lines = command.splitlines(keepends=True)
    i = 0
    while i < len(lines):
        header = lines[i]
        cwd = cwd_after(header, cwd)
        m = re.search(r"<<(-?)\s*(['\"]?)([A-Za-z_][\w-]*)\2", header)
        if not m:
            # Handle simple inline Python scripts, not arbitrary shell execution.
            if re.search(r"\bpython[\d.]*\s+-c\s", header):
                try:
                    words = shlex.split(header)
                    for k, word in enumerate(words[:-2]):
                        if re.fullmatch(r"(?:.*/)?python[\d.]*", word) and words[k+1] == "-c":
                            result.extend(python_payloads(words[k+2], cwd))
                except ValueError:
                    pass
            i += 1
            continue
        j = i + 1
        while j < len(lines) and lines[j].rstrip("\r\n").lstrip("\t" if m[1] else "") != m[3]:
            j += 1
        if j == len(lines):
            i += 1
            continue
        body = "".join(lines[i+1:j])
        if m[1]:
            body = "\n".join(x.lstrip("\t") for x in body.splitlines())
        clean_header = header[:m.start()] + header[m.end():]
        if re.search(r"(?:^|[\s;&|])(?:cat|tee)\b", clean_header):
            targets = re.findall(r"(?<![<>\d])>>?(?![>&])\s*(\"[^\"]*\"|'[^']*'|[^\s;&|]+)", clean_header)
            if not targets and re.search(r"\btee\b", clean_header):
                tm = re.search(r"\btee\s+(?:-a\s+)?(\"[^\"]*\"|'[^']*'|[^\s;&|]+)", clean_header)
                targets = [tm[1]] if tm else []
            for target in targets:
                try:
                    p = normpath(shlex.split(target)[0], cwd)
                    if p:
                        result.append((p, body, "shell_heredoc"))
                except (ValueError, IndexError):
                    pass
        elif re.search(r"\bpython[\d.]*\b", clean_header):
            result.extend(python_payloads(body, cwd))
        elif "apply_patch" in clean_header:
            path, additions = None, []
            for line in body.splitlines() + ["*** End Patch"]:
                if line.startswith(("*** Add File: ", "*** Update File: ", "*** End Patch")):
                    if path and additions:
                        result.append((path, "\n".join(additions), "patch_added_lines"))
                    path = normpath(line.split(": ", 1)[1], cwd) if ": " in line else None
                    additions = []
                elif line.startswith("+") and not line.startswith("+++"):
                    additions.append(line[1:])
        i = j + 1
    return result


def payloads(name, args, cwd):
    if name == "Write":
        p = normpath(args.get("file_path"), cwd)
        return [(p, args.get("content", ""), "Write")] if p else []
    if name == "Edit":
        p = normpath(args.get("file_path"), cwd)
        return [(p, args.get("new_string", ""), "Edit_rhs")] if p else []
    return shell_payloads(args.get("command", ""), cwd) if name == "Bash" else []


def self_test():
    cases = [
        ("cat > /app/scratch/a.md <<'EOF'\nabc\nEOF", [("/app/scratch/a.md", "abc\n")]),
        ("cat <<'EOF' >> a.lean\nlemma a : True := by trivial\nEOF", [("/app/open-eval/a.lean", "lemma a : True := by trivial\n")]),
        ("cd /app/scratch && cat > a.py <<'PY'\nprint(1)\nPY", [("/app/scratch/a.py", "print(1)\n")]),
        ("python3 - <<'PY'\np='/app/scratch/a.md'\nopen(p,'w').write('hello')\nPY", [("/app/scratch/a.md", "hello")]),
        ("python3 - <<'PY'\np='/app/scratch/a.lean'\ns=open(p).read()\ns=s.replace('sorry','by trivial')\nopen(p,'w').write(s)\nPY", [("/app/scratch/a.lean", "by trivial")]),
        ("python3 - <<'PY'\nfrom pathlib import Path\nPath('/app/scratch/a.md').write_text('hello')\nPY", [("/app/scratch/a.md", "hello")]),
        ("cat a.md", []),
        ("python3 - <<'PY'\nprint('cat > a.md')\nPY", []),
        ("cat > /app/scratch/a.md <<'EOF'\nabc\n", []),
    ]
    for cmd, expected in cases:
        actual = [(p, s) for p, s, _ in shell_payloads(cmd, DEFAULT_CWD)]
        assert actual == expected, (cmd, actual, expected)
    assert category("/app/scratch/venv/a.py") is None
    assert category("/app/scratch/result.txt") is None
    print(f"Parser checks passed: {len(cases)+2}")


def read_calls(files):
    """Tool calls and their outcomes from Claude Code session logs, deduplicated by id."""
    calls, outcomes, stamps, bad = {}, {}, [], 0
    for path in files:
        for number, line in enumerate(path.read_bytes().splitlines(), 1):
            try:
                rec = json.loads(line)
            except (ValueError, UnicodeDecodeError):
                bad += 1
                continue
            if rec.get("type") not in {"assistant", "user"}:
                continue
            stamp = rec.get("timestamp")
            if stamp:
                stamps.append(stamp)
            blocks = (rec.get("message") or {}).get("content", [])
            if not isinstance(blocks, list):
                continue
            for b in blocks:
                if not isinstance(b, dict):
                    continue
                if b.get("type") == "tool_use" and stamp:
                    item = {"id": b["id"], "timestamp": stamp, "name": b["name"],
                            "args": b.get("input", {}), "cwd": rec.get("cwd", DEFAULT_CWD),
                            "member": str(path.relative_to(FINAL)), "line": number,
                            "sidechain": rec.get("isSidechain", False)}
                    if b["id"] not in calls or len(json.dumps(item["args"])) > len(json.dumps(calls[b["id"]]["args"])):
                        calls[b["id"]] = item
                elif b.get("type") == "tool_result":
                    outcomes[b.get("tool_use_id")] = bool(b.get("is_error", False))
    return calls, outcomes, stamps, bad


def histories():
    """The histories in the folder: budget, problem, selected trial and ordered phases."""
    out = []
    for budget in (100, 1000):
        by_problem = defaultdict(list)
        for d in sorted((FINAL / str(budget)).iterdir()):
            if d.is_dir() and "__" in d.name and (d / "result.json").exists():
                span = json.loads((d / "result.json").read_text()).get("agent_execution") or {}
                if not span.get("started_at") or not span.get("finished_at"):
                    raise SystemExit(f"{d}: no agent execution window in result.json")
                by_problem[d.name.rsplit("__", 1)[0]].append(
                    {"trial": d.name, "start": span["started_at"], "end": span["finished_at"]})
        if len(by_problem) != 20:
            raise SystemExit(f"{FINAL / str(budget)}: {len(by_problem)} problems, expected 20")
        for problem, phases in sorted(by_problem.items()):
            phases.sort(key=lambda p: dt(p["start"]))
            out.append({"budget": budget, "problem": problem, "trial": phases[-1]["trial"],
                        "is_resume": len(phases) > 1, "phases": phases})
    return out


def extract():
    manifest = histories()
    assert len(manifest) == 40 and Counter(h["budget"] for h in manifest) == {100: 20, 1000: 20}
    summaries, events = [], []
    for h in manifest:
        trial, problem, budget = h["trial"], h["problem"], h["budget"]
        files = sorted(f for p in h["phases"]
                       for f in (FINAL / str(budget) / p["trial"] / "agent" / "sessions").glob("**/*.jsonl"))
        assert files, trial
        calls, outcomes, stamps, bad = read_calls(files)
        phases = []
        for p in h["phases"]:
            start, end = dt(p["start"]), dt(p["end"])
            observed = [dt(t) for t in stamps if start <= dt(t) <= end]
            assert observed, (trial, p["trial"])
            phases.append({"trial": p["trial"], "start": p["start"], "end": p["end"],
                           "observed_end": max(observed).isoformat()})

        def clock(stamp):
            t, elapsed = dt(stamp), 0.0
            for p in phases:
                start, end = dt(p["start"]), dt(p["observed_end"])
                if start <= t <= end:
                    return (elapsed + (t - start).total_seconds()) / 3600
                elapsed += (end - start).total_seconds()
            return None

        duration = sum((dt(p["observed_end"]) - dt(p["start"])).total_seconds() / 3600 for p in phases)
        tails = sum((dt(p["end"]) - dt(p["observed_end"])).total_seconds() / 3600 for p in phases)
        seen = defaultdict(set)
        fresh_total = Counter()
        skipped = []
        for call in sorted(calls.values(), key=lambda c: (c["timestamp"], c["id"])):
            args = call["args"]
            if not isinstance(args, dict):
                continue
            found = payloads(call["name"], args, call["cwd"])
            elapsed = clock(call["timestamp"])
            if elapsed is None:
                if found:
                    skipped.append({"timestamp": call["timestamp"], "tool_id": call["id"]})
                continue
            for index, (path, content, method) in enumerate(found):
                cat = category(path)
                if not cat or not isinstance(content, str):
                    continue
                lines = [s.strip() for s in content.splitlines() if s.strip()]
                fresh = [s for s in dict.fromkeys(lines) if s not in seen[path]]
                seen[path].update(fresh)
                events.append({"trial": trial, "problem": problem, "budget": budget,
                               "timestamp": call["timestamp"], "elapsed_hours": elapsed, "category": cat,
                               "path": path, "method": method, "tool_id": call["id"], "payload_index": index,
                               "nonblank_lines": len(lines), "first_seen_lines": len(fresh),
                               "words": len(content.split()),
                               "payload_sha256": hashlib.sha256(content.encode()).hexdigest(),
                               "member": call["member"], "source_line": call["line"], "sidechain": call["sidechain"],
                               "tool_reported_error": outcomes.get(call["id"])})
                fresh_total[cat] += len(fresh)
        assert not skipped, (trial, "writing outside phase windows", skipped)
        summaries.append({"trial": trial, "problem": problem, "budget": budget, "is_resume": h["is_resume"],
                          "observed_hours": duration, "phases": phases,
                          "first_seen_lines": {c: fresh_total[c] for c in CATS}})
        print(budget, problem, {c: fresh_total[c] for c in CATS}, f"{duration:.2f} h", flush=True)
    for s in summaries:
        ev = [e for e in events if e["trial"] == s["trial"]]
        for c in CATS:
            assert sum(e["first_seen_lines"] for e in ev if e["category"] == c) == s["first_seen_lines"][c]
        assert all(-1e-7 <= e["elapsed_hours"] <= s["observed_hours"] + 1e-7 for e in ev)
        assert len({(e["tool_id"], e["payload_index"]) for e in ev}) == len(ev)
    events.sort(key=lambda e: (e["trial"], e["timestamp"], e["tool_id"], e["payload_index"]))
    DATA.mkdir(exist_ok=True)
    (DATA / "trials.json").write_text(json.dumps(summaries, indent=2) + "\n")
    (DATA / "events.jsonl").write_text("".join(json.dumps(e) + "\n" for e in events))
    print(f"{len(events)} events from {len(summaries)} histories")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true", help="run the parser checks only")
    a = ap.parse_args()
    self_test() if a.self_test else extract()
