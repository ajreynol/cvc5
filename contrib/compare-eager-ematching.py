#!/usr/bin/env python3
"""Compare the E-matching instances of z3 and of cvc5's eager E-matching.

See src/theory/quantifiers/eager/README.md section 9.1. Both solvers log the
bindings of a match after canonicalizing them to the representative of their
equivalence class, so the comparison is exact as long as the two solvers agree
on the representatives, which they do when the relevant classes are singletons.

  compare-eager-ematching.py <benchmark.smt2> [--default-cvc5]

By default cvc5's own instantiation strategies are disabled, so that the
instances on each side come only from that solver's matcher. Set the Z3 and
CVC5 environment variables to point at the binaries.
"""
import os as _os
import re, subprocess, sys, os, tempfile, collections

Z3 = os.environ.get("Z3", os.path.expanduser("~/z3/build/z3"))
CVC5 = os.environ.get("CVC5", "cvc5")


def z3_matches(bench, extra):
    d = tempfile.mkdtemp()
    subprocess.run([Z3, "trace=true", "smt.mbqi=false", os.path.abspath(bench)] + extra,
                   cwd=d, capture_output=True, text=True, timeout=120)
    log = os.path.join(d, "z3.log")
    if not os.path.exists(log):
        return None, {}
    terms = {}
    qname = {}
    matches = []
    for line in open(log):
        line = line.rstrip("\n")
        if line.startswith("[mk-app] "):
            parts = line[len("[mk-app] "):].split()
            tid = parts[0][1:]
            decl = parts[1]
            args = [terms.get(a[1:], a) for a in parts[2:]]
            terms[tid] = decl if not args else "(" + decl + " " + " ".join(args) + ")"
        elif line.startswith("[mk-var] "):
            parts = line[len("[mk-var] "):].split()
            terms[parts[0][1:]] = parts[1]
        elif line.startswith("[mk-quant] "):
            parts = line[len("[mk-quant] "):].split()
            qname[parts[0][1:]] = parts[1]
            terms[parts[0][1:]] = parts[1]
        elif line.startswith("[new-match] "):
            parts = line[len("[new-match] "):].split()
            # <hash> #qid #patid <bindings...> ; <used enodes>
            qid = parts[1][1:]
            rest = parts[3:]
            bindings = []
            for p in rest:
                if p == ";":
                    break
                bindings.append(terms.get(p[1:], p))
            # z3 prints the bindings in reverse order of the variable index
            bindings.reverse()
            matches.append((qname.get(qid, qid), tuple(bindings)))
    return matches, qname


def cvc5_matches(bench, extra):
    r = subprocess.run([CVC5, "--eager-inst", "--eager-inst-output=lemma",
                        "-t", "eager-inst-match", os.path.abspath(bench)] + extra,
                       capture_output=True, text=True, timeout=120)
    qname = {}
    matches = []
    for line in r.stdout.splitlines():
        if line.startswith("QUANT "):
            parts = line.split()
            qname[parts[1]] = parts[2]
        elif line.startswith("MATCH "):
            parts = line.split(None, 2)
            qid = parts[1]
            bindings = tuple(split_sexprs(parts[2])) if len(parts) > 2 else ()
            matches.append((qname.get(qid, qid), bindings))
    return matches, qname


def split_sexprs(s):
    """Split a line into top-level s-expressions."""
    out = []
    depth = 0
    curr = ""
    for ch in s:
        if ch.isspace() and depth == 0:
            if curr:
                out.append(curr)
                curr = ""
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        curr += ch
    if curr:
        out.append(curr)
    return out


def summarize(matches):
    per_q = collections.Counter(m[0] for m in matches)
    # The quantifier labels only align when the input gives every quantifier a
    # :qid, so the set comparison ignores them.
    return per_q, collections.Counter(m[1] for m in matches)


def main():
    bench = sys.argv[1]
    extra_z3 = []
    # Disable cvc5's own instantiation strategies, so that the only instances on
    # the cvc5 side come from eager E-matching, as on the z3 side they come only
    # from its matcher (smt.mbqi=false).
    extra_cvc5 = ["--no-e-matching", "--no-cegqi", "--no-enum-inst",
                  "--no-cbqi", "--no-mbqi"]
    if len(sys.argv) > 2 and sys.argv[2] == "--default-cvc5":
        extra_cvc5 = []
    zm, _ = z3_matches(bench, extra_z3)
    cm, _ = cvc5_matches(bench, extra_cvc5)
    if zm is None:
        print("z3 produced no trace")
        return 1
    zq, zs = summarize(zm)
    cq, cs = summarize(cm)
    print("%-40s z3=%-4d cvc5=%-4d" % (os.path.basename(bench), len(zm), len(cm)))
    named = all(q != "?" for q in cq) and bool(cq)
    if named:
        for q in sorted(set(zq) | set(cq)):
            flag = "" if zq[q] == cq[q] else "   <-- differs"
            print("   %-20s z3=%-4d cvc5=%-4d%s" % (q, zq[q], cq[q], flag))
    only_z3 = zs - cs
    only_cvc5 = cs - zs
    if only_z3 or only_cvc5:
        print("   bindings only in z3: %d, only in cvc5: %d" % (
            sum(only_z3.values()), sum(only_cvc5.values())))
        for m, n in sorted(only_z3.items())[:5]:
            print("     only z3   x%d: %s" % (n, " ".join(m)))
        for m, n in sorted(only_cvc5.items())[:5]:
            print("     only cvc5 x%d: %s" % (n, " ".join(m)))
    else:
        print("   identical match sets")
    return 0


sys.exit(main())
