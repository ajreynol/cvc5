#!/usr/bin/env python3
"""Run several solver configurations over a benchmark list and compare them.

  eval-solvers.py <benchmark-list> [--timeout N] [--jobs N] [--csv FILE]

The configurations are given as NAME=COMMAND arguments after the list, e.g.

  eval-solvers.py list.txt 'z3=/path/z3' 'cvc5=/path/cvc5 --no-cbqi'

Reports how many each configuration solves, how many it uniquely solves relative
to the first configuration, any answer that contradicts the benchmark's own
(set-info :status ...), and the time each takes on the benchmarks every
configuration solved.
"""
import argparse
import csv
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

STATUS = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")


def expected(path):
    try:
        with open(path, errors="replace") as f:
            m = STATUS.search(f.read(20000))
        return m.group(1) if m else ""
    except OSError:
        return ""


def run(cmd, bench, timeout):
    t0 = time.time()
    try:
        r = subprocess.run(cmd + [bench], capture_output=True, text=True,
                           timeout=timeout)
        out = r.stdout.strip().split("\n")[0].strip() if r.stdout.strip() else "error"
    except subprocess.TimeoutExpired:
        return "timeout", timeout
    except OSError:
        return "error", time.time() - t0
    return (out if out in ("sat", "unsat", "unknown") else "error"), time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("list")
    ap.add_argument("configs", nargs="+", help="NAME=COMMAND")
    ap.add_argument("--timeout", type=float, default=10.0)
    ap.add_argument("--jobs", type=int, default=12)
    ap.add_argument("--csv", default=None)
    a = ap.parse_args()

    configs = []
    for c in a.configs:
        name, _, cmd = c.partition("=")
        configs.append((name, cmd.split()))
    benches = [l.strip() for l in open(a.list) if l.strip()]

    def one(b):
        row = {"benchmark": b, "expected": expected(b)}
        for name, cmd in configs:
            res, t = run(cmd, b, a.timeout)
            row[name] = res
            row[name + "_time"] = t
        return row

    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        rows = list(ex.map(one, benches))

    if a.csv:
        cols = ["benchmark", "expected"]
        for name, _ in configs:
            cols += [name, name + "_time"]
        with open(a.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=cols)
            w.writeheader()
            for r in rows:
                w.writerow({k: (("%.3f" % v) if k.endswith("_time") else v)
                            for k, v in r.items()})

    solved = lambda r, n: r[n] in ("sat", "unsat")
    allsolved = [r for r in rows if all(solved(r, n) for n, _ in configs)]
    first = configs[0][0]
    print("benchmarks %d, timeout %gs, %d solved by all"
          % (len(rows), a.timeout, len(allsolved)))
    print("%-22s %7s %9s %9s %7s" % ("configuration", "solved", "only-it",
                                     "missed", "time"))
    for name, _ in configs:
        n = sum(1 for r in rows if solved(r, name))
        onlyit = sum(1 for r in rows
                     if solved(r, name) and not solved(r, first)) if name != first else 0
        missed = sum(1 for r in rows
                     if solved(r, first) and not solved(r, name)) if name != first else 0
        t = sum(r[name + "_time"] for r in allsolved)
        print("%-22s %7d %9s %9s %6.1fs" % (name, n,
                                            "-" if name == first else onlyit,
                                            "-" if name == first else missed, t))
    for name, _ in configs:
        bad = [r for r in rows if r["expected"] in ("sat", "unsat")
               and solved(r, name) and r[name] != r["expected"]]
        if bad:
            print("WRONG vs :status, %s: %d" % (name, len(bad)))
            for r in bad[:3]:
                print("   %s expected=%s got=%s" % (r["benchmark"], r["expected"], r[name]))
    return 0


sys.exit(main())
