"""Text checks used to grade a Lean file Aristotle returned, in-process.

`grade_text(submission, reference, name)` returns the FAIL reasons, empty when
the text checks pass: no sorry/admit/sorryAx token, axiom or native_decide in
the comment-stripped code; every given declaration of the issued file
preserved verbatim and in order (insertions between them are allowed); and the
theorem statement preserved up to its `:=`. Compilation is the other half of
the verdict and needs Lean (see run_aristotle.py --verify-lean).
"""

from __future__ import annotations

import re

# A declaration the task leaves for the agent to fill (none of the convex-eval
# tasks has one): only its head, name and type up to the `:=`, is pinned.
OPEN_DECL = re.compile(
    r"(?m)^(?:noncomputable\s+)?(?P<head>abbrev\s+\w+_solution\s*:\s*.+?:=)\s*sorry\s*$"
)


def strip_comments(t: str) -> str:
    """Drop Lean line and (nesting) block comments, keeping code only."""
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if depth:
            if t.startswith("/-", i):
                depth += 1; i += 2; continue
            if t.startswith("-/", i):
                depth -= 1; i += 2; continue
            i += 1; continue
        if t.startswith("/-", i):
            depth = 1; i += 2; continue
        if t.startswith("--", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(t[i]); i += 1
    return "".join(out)


def lines_of(t: str) -> list[str]:
    """Significant code lines: comments and blank lines dropped."""
    t = strip_comments(t).replace("\r\n", "\n")
    return [l.rstrip() for l in t.split("\n") if l.strip()]


def chunks(t: str) -> list[list[str]]:
    """Top-level blocks: a new one starts at column 0, continuation lines are indented."""
    out, cur = [], []
    for l in lines_of(t):
        if l[:1] not in (" ", "\t") and cur:
            out.append(cur)
            cur = []
        cur.append(l)
    if cur:
        out.append(cur)
    return out


def split_lean(text: str, name: str) -> tuple[str, str, str]:
    """(preamble, open declaration head, theorem signature before `:=`) of the issued file."""
    m = re.search(rf"(?m)^(?:theorem|lemma)\s+{re.escape(name)}\b", text)
    assert m, f"{name}: no theorem declaration found"
    preamble = text[: m.start()].rstrip("\n")
    rest = text[m.start():]
    a = rest.rfind(":=")
    assert a > 0, f"{name}: no ':=' terminating the statement"
    statement = rest[:a].rstrip()

    solution = ""
    o = OPEN_DECL.search(preamble)
    if o:
        assert not OPEN_DECL.search(preamble[o.end():]), f"{name}: more than one open declaration"
        solution = o.group("head").strip()
        preamble = (preamble[: o.start()] + preamble[o.end():]).strip("\n")
    return preamble, solution, statement


def grade_text(submission: str, reference: str, name: str) -> list[str]:
    """FAIL reasons for `submission` against the issued `reference` file; empty when it passes."""
    preamble, solution, statement = split_lean(reference, name)
    code = strip_comments(submission)
    bad: list[str] = []

    if re.search(r"(^|[^A-Za-z0-9_'])(sorry|admit|sorryAx)([^A-Za-z0-9_']|$)", code):
        bad.append("sorry/admit/sorryAx token in code")
    if re.search(r"(?m)^\s*axiom\s", code):
        bad.append("axiom declaration")
    if "native_decide" in code:
        bad.append("native_decide")

    # Every given declaration must survive verbatim, in order, as live code.
    got = lines_of(submission)
    at = 0
    for ch in chunks(preamble):
        hit = -1
        for i in range(at, len(got) - len(ch) + 1):
            if got[i:i + len(ch)] == ch:
                hit = i
                break
        if hit < 0:
            bad.append(f"given declaration modified, removed or reordered: {ch[0][:70]}")
            break
        at = hit + len(ch)

    # The signature is matched as text: cut before the `:=`, its last line is a
    # prefix of the submitted one.
    flat = "\n".join(got)
    stmt = "\n".join(lines_of(statement))
    if stmt and stmt not in flat:
        bad.append("theorem statement was modified or removed")
    sol = "\n".join(lines_of(solution))
    if sol and sol not in flat:
        bad.append("solution declaration was renamed or retyped")
    return bad
