#!/usr/bin/env python3
"""Run the solver with several settings and keep the shortest program per puzzle.

Usage: python3 tools/portfolio.py puzzles.csv out/submission.csv [--quick]
"""
import csv
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONFIGS = [
    "--pick 16 --nodes 100",
    "--pick 16 --nodes 100 --rate 6.5 --minrate 1.5",
    "--pick 16 --nodes 100 --bitw 5 --vote 0",
    "--pick 16 --nodes 100 --effort 1 --usew 5",
]
QUICK = ["--pick 1 --nodes 100"]


def main():
    puzzles, out = sys.argv[1], Path(sys.argv[2])
    configs = QUICK if "--quick" in sys.argv else CONFIGS
    out.parent.mkdir(parents=True, exist_ok=True)
    best = {}
    for n, cfg in enumerate(configs):
        part = out.with_suffix(f".part{n}.csv")
        subprocess.run([str(ROOT / "solver"), puzzles, str(part), *cfg.split()], check=True)
        total = 0
        for row in csv.DictReader(open(part)):
            size = len(json.loads(row["program"]))
            total += size
            if row["id"] not in best or size < best[row["id"]][0]:
                best[row["id"]] = (size, row["program"])
        print(f"config {n}: {total}  best-so-far: {sum(v[0] for v in best.values())}", flush=True)
    order = [r["id"] for r in csv.DictReader(open(puzzles))]
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["id", "program"])
        for pid in order:
            w.writerow([pid, best[pid][1]])
    subprocess.run([sys.executable, str(ROOT / "src" / "verify.py"), puzzles, str(out)], check=False)


if __name__ == "__main__":
    main()
