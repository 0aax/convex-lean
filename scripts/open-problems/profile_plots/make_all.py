"""Regenerate every open-problem profile figure into figures/open-problems/.

    uv run --with matplotlib --with numpy python scripts/open-problems/profile_plots/make_all.py

Needs a LaTeX install on PATH (latex, and dvipng for the PNGs).
"""
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

if not shutil.which("latex") or not shutil.which("dvipng"):
    sys.exit("latex and dvipng must be on PATH")
for args in (["--budget", "100"], ["--budget", "1000"]):
    subprocess.run([sys.executable, str(HERE / "plot_lines_per_task.py"), *args], check=True)
