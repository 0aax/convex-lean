"""Copy the source PDFs into every autoformalization task's build context.

The autoformalization tasks give the agent the books and papers the project was
formalized from, as PDFs under /app/corpus/ in the sandbox. Each task's
environment/INDEX.md lists those files with their paths relative to the corpus,
and the task Dockerfile copies environment/corpus/ into the image. The PDFs are
not redistributed with this repository, so obtain them and place them under
textbooks/ at the repo root, with the relative paths INDEX.md lists, for example

    textbooks/fundamentals_of_convex_analysis.pdf
    textbooks/Duchi/duchiex1.pdf
    textbooks/SAG_SAGA/1309.2388v2.pdf

then run

    uv run python scripts/autoformalize/install_corpus.py

which copies them into tasks/autoformalize*/<task>/environment/corpus/. The
script fails, listing the missing files, if any file INDEX.md names is absent
from textbooks/. Both textbooks/ and the corpus copies are gitignored.
"""
import argparse
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEXTBOOKS = ROOT / "textbooks"
INDEX_LINE = re.compile(r"^- `([^`]+)`", re.M)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--textbooks", type=Path, default=TEXTBOOKS,
                    help=f"folder holding the PDFs (default {TEXTBOOKS.relative_to(ROOT)}/)")
    args = ap.parse_args()
    indexes = sorted(ROOT.glob("tasks/autoformalize*/*/environment/INDEX.md"))
    if not indexes:
        sys.exit("no autoformalization tasks found under tasks/")
    needed = set()
    for idx in indexes:
        needed.update(INDEX_LINE.findall(idx.read_text(encoding="utf-8")))
    missing = sorted(p for p in needed if not (args.textbooks / p).is_file())
    if missing:
        sys.exit(f"{len(missing)} of {len(needed)} corpus files are missing from {args.textbooks}/:\n  "
                 + "\n  ".join(missing))
    for idx in indexes:
        corpus = idx.parent / "corpus"
        for rel in INDEX_LINE.findall(idx.read_text(encoding="utf-8")):
            dst = corpus / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(args.textbooks / rel, dst)
    print(f"copied {len(needed)} files into {len(indexes)} tasks")


if __name__ == "__main__":
    main()
