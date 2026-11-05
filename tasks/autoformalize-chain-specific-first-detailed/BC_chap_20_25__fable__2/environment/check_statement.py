#!/usr/bin/env python3
"""Format check for an autoformalization submission.

Usage: check_statement.py <lean file> <theorem name>

Exit 0 when all of the following hold, else 1, printing one reason per line:
  * the file declares a theorem named <theorem name>;
  * its proof is `sorry`, and that is the only `sorry` in the file (so every
    definition and auxiliary lemma is complete);
  * the placeholder statement `: True` has been replaced;
  * the file declares no `axiom` and no `opaque`.
Compilation is checked separately by the caller (`lake build`). The check is
purely textual, on the source with comments removed, so it cannot be fooled by
`sorry` inside a comment or a string.
"""
import re
import sys


def strip_comments(text: str) -> str:
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            out.append(" ")
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(" ")
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque|example)"
    r"\b\s*([^\s:({\[⦃]*)",
    re.M,
)


def main() -> int:
    path, name = sys.argv[1], sys.argv[2]
    with open(path, encoding="utf-8") as fh:
        raw = fh.read()
    text = strip_comments(raw)
    reasons = []

    decls = [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(text)]
    for _, kind, ident in decls:
        if kind in ("axiom", "opaque"):
            reasons.append(f"declares `{kind} {ident}`; axioms and opaque constants are not allowed")

    targets = [d for d in decls if d[1] in ("theorem", "lemma") and d[2] == name]
    if not targets:
        reasons.append(f"no theorem named `{name}` found")
    else:
        start = targets[0][0]
        later = [d[0] for d in decls if d[0] > start]
        end = min(later) if later else len(text)
        body = text[start:end]
        if re.search(r":\s*True\s*:=", body):
            reasons.append(f"`{name}` still has the placeholder statement `True`")
        if not re.search(r"\bsorry\b", body):
            reasons.append(f"the proof of `{name}` must be `sorry` (the statement, not a proof, is assessed)")

    sorries = [m.start() for m in re.finditer(r"\bsorry\b", text)]
    if targets:
        start = targets[0][0]
        later = [d[0] for d in decls if d[0] > start]
        end = min(later) if later else len(text)
        outside = [s for s in sorries if not (start <= s < end)]
        if outside:
            reasons.append(
                f"{len(outside)} `sorry` outside the theorem `{name}`: every definition and "
                "auxiliary lemma must be complete"
            )
        inside = [s for s in sorries if start <= s < end]
        if len(inside) > 1:
            reasons.append(f"more than one `sorry` in `{name}`; its proof must be exactly `sorry`")
    elif sorries:
        reasons.append(f"{len(sorries)} `sorry` found but no theorem named `{name}`")

    for r in reasons:
        print(r)
    return 1 if reasons else 0


if __name__ == "__main__":
    sys.exit(main())
