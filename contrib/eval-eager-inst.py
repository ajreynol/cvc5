#!/usr/bin/env python3
"""Evaluate eager E-matching against a baseline on a set of benchmarks.

  eval-eager-inst.py <benchmark-list> [--timeout N] [--jobs N] [--csv FILE]
                     [--base "OPTS"] [--test "OPTS"] [--cvc5 PATH]

Each benchmark is run under the baseline options and then under the baseline
plus the options under test, back to back in the same worker so that both see
similar machine conditions. The expected status is read from
(set-info :status ...) when the benchmark states one, and a disagreement with it
is reported as a soundness error rather than a performance difference.
"""
import argparse
import csv
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

STATUS = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")


def expected_status(path):
    try:
        with open(path, errors="replace") as f:
            m = STATUS.search(f.read(20000))
        return m.group(1) if m else None
    except OSError:
        return None


def run(cvc5, opts, bench, timeout):
    t0 = time.time()
    try:
        r = subprocess.run([cvc5] + opts + [bench],
                           capture_output=True, text=True, timeout=timeout)
        out = r.stdout.strip().split("\n")[0].strip() if r.stdout.strip() else "error"
    except subprocess.TimeoutExpired:
        return "timeout", timeout
    except OSError as e:
        return "error:%s" % e, time.time() - t0
    if out not in ("sat", "unsat", "unknown"):
        out = "error"
    return out, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("list")
    ap.add_argument("--timeout", type=float, default=15.0)
    ap.add_argument("--jobs", type=int, default=10)
    ap.add_argument("--csv", default=None)
    ap.add_argument("--base", default="--no-cbqi --user-pat=strict")
    ap.add_argument("--test", default="--eager-inst")
    ap.add_argument("--cvc5", default=os.path.expanduser("~/build-cvc5/pr-ajr/prod/bin/cvc5"))
    a = ap.parse_args()

    base = a.base.split()
    test = base + a.test.split()
    benches = [l.strip() for l in open(a.list) if l.strip()]

    def one(b):
        exp = expected_status(b)
        rb, tb = run(a.cvc5, base, b, a.timeout)
        rt, tt = run(a.cvc5, test, b, a.timeout)
        return (b, exp, rb, tb, rt, tt)

    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        rows = list(ex.map(one, benches))

    if a.csv:
        with open(a.csv, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["benchmark", "expected", "base", "base_time",
                        "test", "test_time"])
            for r in rows:
                w.writerow([r[0], r[1] or "", r[2], "%.3f" % r[3],
                            r[4], "%.3f" % r[5]])

    def solved(r):
        return r in ("sat", "unsat")

    nb = sum(1 for r in rows if solved(r[2]))
    nt = sum(1 for r in rows if solved(r[4]))
    only_t = [r for r in rows if solved(r[4]) and not solved(r[2])]
    only_b = [r for r in rows if solved(r[2]) and not solved(r[4])]
    disagree = [r for r in rows if solved(r[2]) and solved(r[4]) and r[2] != r[4]]
    wrong = [r for r in rows if r[1] in ("sat", "unsat")
             and ((solved(r[2]) and r[2] != r[1]) or (solved(r[4]) and r[4] != r[1]))]
    both = [r for r in rows if solved(r[2]) and solved(r[4])]
    tb = sum(r[3] for r in both)
    tt = sum(r[5] for r in both)

    print("benchmarks           %d" % len(rows))
    print("timeout              %gs, jobs %d" % (a.timeout, a.jobs))
    print("baseline options     %s" % " ".join(base))
    print("test options         %s" % " ".join(test))
    print("baseline solved      %d" % nb)
    print("test solved          %d  (%+d)" % (nt, nt - nb))
    print("  solved only by test     %d" % len(only_t))
    print("  solved only by baseline %d" % len(only_b))
    print("answer disagreements %d" % len(disagree))
    print("wrong vs :status     %d" % len(wrong))
    if both:
        print("commonly solved      %d, baseline %.1fs, test %.1fs (%+.0f%%)"
              % (len(both), tb, tt, 100.0 * (tt - tb) / max(tb, 1e-9)))
    for r in only_b[:10]:
        print("  lost: %s" % r[0])
    for r in disagree[:10]:
        print("  DISAGREE %s: base=%s test=%s" % (r[0], r[2], r[4]))
    for r in wrong[:10]:
        print("  WRONG %s: expected=%s base=%s test=%s" % (r[0], r[1], r[2], r[4]))
    return 1 if (disagree or wrong) else 0


sys.exit(main())
