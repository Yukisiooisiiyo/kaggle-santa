#!/usr/bin/env python3
"""Independent checker for Elf Calculator submissions.

Usage: python3 src/verify.py puzzles.csv submission.csv

Replays every program and enforces the rules as we understand them:
  * registers 0..k-1 hold the starting values, the rest are undefined
  * an instruction is [op, src_i, src_j, dst]; both sources are read first
  * every result is an integer with 1 <= result <= value_limit
  * division must be exact
  * every target must appear at least once (starting values count)
  * at most 4096 instructions and 128 KiB per program cell
Prints the total instruction count (the competition score).
"""
import csv
import json
import sys
from collections import defaultdict

MAX_INSTR = 4096
MAX_CELL = 128 * 1024


def run(puzzle, program):
    start = json.loads(puzzle["starting_values"])
    targets = set(json.loads(puzzle["targets"]))
    limit = int(puzzle["value_limit"])
    nreg = int(puzzle["registers"])
    reg = [None] * nreg
    reg[: len(start)] = start
    seen = set(start)
    if len(program) > MAX_INSTR:
        return "too many instructions"
    for n, ins in enumerate(program):
        op, i, j, d = ins
        if not all(isinstance(x, int) and 0 <= x < nreg for x in (i, j, d)):
            return f"step {n}: bad register"
        a, b = reg[i], reg[j]
        if a is None or b is None:
            return f"step {n}: undefined source"
        if op == "+":
            r = a + b
        elif op == "-":
            r = a - b
        elif op == "*":
            r = a * b
        elif op == "/":
            if a % b:
                return f"step {n}: inexact division"
            r = a // b
        else:
            return f"step {n}: bad operator {op!r}"
        if r < 1 or r > limit:
            return f"step {n}: value {r} out of range"
        reg[d] = r
        seen.add(r)
    missing = targets - seen
    if missing:
        return f"{len(missing)} targets missing"
    return None


def main():
    puzzles = {r["id"]: r for r in csv.DictReader(open(sys.argv[1]))}
    total = 0
    fam = defaultdict(int)
    bad = 0
    ids = set()
    for row in csv.DictReader(open(sys.argv[2])):
        pid = row["id"]
        ids.add(pid)
        if len(row["program"].encode()) > MAX_CELL:
            print(pid, "cell too large")
            bad += 1
        program = json.loads(row["program"])
        err = run(puzzles[pid], program)
        if err:
            print(pid, "INVALID:", err)
            bad += 1
        total += len(program)
        fam[puzzles[pid].get("family", "")] += len(program)
    if ids != set(puzzles):
        print("missing puzzles:", len(set(puzzles) - ids))
        bad += 1
    for k in sorted(fam):
        print(f"{k:15s} {fam[k]}")
    print("score", total, "INVALID" if bad else "valid")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
