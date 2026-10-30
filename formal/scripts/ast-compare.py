#!/usr/bin/env python3
"""ast-compare.py — compare two refs' reachability dumps (MERGE.md §6, plan 0.132).

Each ref has a PROVED dump (`ast-once-certified-<ref>-<sha>.json`, what the apex
proof depends on) and, from plan 0.132 on, a RUNS dump (`ast-runs-<ref>-<sha>.json`,
what the CLI runs: `Once.Extract.Root.runs`). Both come from `run-ast-dumps.sh`.

    ast-compare.py BASE_PROVED [BASE_RUNS] -- HEAD_PROVED [HEAD_RUNS]
    ast-compare.py --census PROVED RUNS          # one ref: RUNS ∖ PROVED, classified

Reports
  * the trust base: assumptions added and removed (by site);
  * PROVED: modules that left or joined the reachable set;
  * RUNS ∖ PROVED ("runs but unproved"), by module, each declaration classified
    by `runs-unproved.allow` as *declared* (a decision says it carries no
    theorem) or a *gap*;
  * the assumptions reachable from RUNS (run code that rests on one).

Exit status 1 when HEAD has a gap declaration BASE does not (a new unproved run
declaration needs a decision entry and an allow line), or a new assumption.
"""

import json
import os
import sys
from collections import Counter, defaultdict

ALLOW = os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs-unproved.allow")


def load(path):
    return json.load(open(path)) if path else None


def decls(d):
    """Declaration name -> source module path."""
    return {e["name"]: e["source"] for e in d["reachable"]}


def modules(d):
    return {e["source"] for e in d["reachable"]}


def trust(d):
    return Counter((t["site"], t["assumption"]) for t in d["trustBase"])


def read_allow(path=ALLOW):
    """Lines `PREFIX  DECISION  reason…`: a declaration whose qualified name
    starts with PREFIX runs without a theorem by that decision."""
    rules = []
    if not os.path.exists(path):
        return rules
    for line in open(path):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split(None, 2)
        rules.append((parts[0], parts[1] if len(parts) > 1 else "?", parts[2] if len(parts) > 2 else ""))
    # longest prefix first
    return sorted(rules, key=lambda r: -len(r[0]))


def classify(name, rules):
    for prefix, decision, _ in rules:
        if name.startswith(prefix):
            return decision
    return None


def unproved(proved, runs):
    p = decls(proved)
    return {n: s for n, s in decls(runs).items() if n not in p}


def by_module(names_to_src):
    out = defaultdict(list)
    for n, s in names_to_src.items():
        out[s].append(n)
    return out


def census(proved, runs, rules, label):
    u = unproved(proved, runs)
    gaps = {n: s for n, s in u.items() if classify(n, rules) is None}
    print(f"== {label}: RUNS {len(decls(runs))}, PROVED {len(decls(proved))}, "
          f"RUNS ∖ PROVED {len(u)} ({len(u) - len(gaps)} declared, {len(gaps)} gap)")
    for src, ns in sorted(by_module(u).items()):
        g = [n for n in ns if n in gaps]
        tag = "gap" if len(g) == len(ns) else ("declared" if not g else "mixed")
        dec = sorted({classify(n, rules) or "-" for n in ns})
        print(f"  {tag:8} {len(ns):5}  {src}  [{', '.join(dec)}]")
    ta = [t for t in runs["trustBase"]]
    print(f"  assumptions reachable from RUNS: {len(ta)}")
    for t in sorted(ta, key=lambda t: t["site"]):
        print(f"    {t['assumption']:20} {t['site']}")
    return gaps


def main(argv):
    rules = read_allow()
    if argv[:1] == ["--census"]:
        census(load(argv[1]), load(argv[2]), rules, "census")
        return 0
    if "--" not in argv:
        print(__doc__)
        return 2
    i = argv.index("--")
    base, head = argv[:i], argv[i + 1:]
    bp, br = load(base[0]), load(base[1]) if len(base) > 1 else None
    hp, hr = load(head[0]), load(head[1]) if len(head) > 1 else None
    status = 0

    a, b = trust(bp), trust(hp)
    print(f"== trust base: {sum(a.values())} -> {sum(b.values())}")
    for k, n in sorted((a - b).items()):
        print(f"  - {k[1]:20} {k[0]}")
    for k, n in sorted((b - a).items()):
        print(f"  + {k[1]:20} {k[0]}")
        status = 1

    ma, mb = modules(bp), modules(hp)
    print(f"== PROVED modules: {len(ma)} -> {len(mb)}")
    for m in sorted(ma - mb):
        print(f"  left   {m}")
    for m in sorted(mb - ma):
        print(f"  joined {m}")

    if hr is None:
        print("== RUNS: no dump for HEAD")
        return status
    head_gaps = census(hp, hr, rules, "HEAD")
    if br is None:
        print("== RUNS: no dump for BASE (older than plan 0.132); HEAD's gaps are listed above")
        return status
    base_gaps = census(bp, br, rules, "BASE")
    new = sorted(set(head_gaps) - set(base_gaps))
    gone = sorted(set(base_gaps) - set(head_gaps))
    print(f"== gaps: {len(base_gaps)} -> {len(head_gaps)}")
    for n in gone:
        print(f"  closed {n}")
    for n in new:
        print(f"  NEW    {n}  ({head_gaps[n]})")
        status = 1
    ta = Counter(t["site"] for t in br["trustBase"])
    tb = Counter(t["site"] for t in hr["trustBase"])
    for s in sorted(tb - ta):
        print(f"  NEW assumption reachable from RUNS: {s}")
        status = 1
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
