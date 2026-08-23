#!/usr/bin/env python3
"""
gen-clauses.py — derive indexed clauses from their non-indexed twins.

⚠ WHY THIS IS A FILE AND NOT AN AD-HOC SCRIPT.  Running two ad-hoc
  generators over the same function produced FIVE DUPLICATE CLAUSES that
  Agda accepted with only a warning.  Duplicates are SILENT: Agda takes the
  first and warns.  If the copies ever DIFFER — one generated before a fix
  and one after — the stale clause wins and the module still compiles.

THREE INVARIANTS, enforced on every batch:
  1. NEVER emit a line already present in the file        (no duplicates)
  2. every emitted line has balanced parentheses          (no greedy-regex
     damage — `[^\s)]+`, never `\S+`, or a nested pattern loses its paren)
  3. insert in REVERSE line order                         (earlier indices
     stay valid; forward insertion corrupted Confluence twice)
"""
import re, sys
from collections import Counter

# con → icon, elim → ielim (index inserted), ⌜Mu⌝ → ⌜IMu⌝
PAT = {
 "con":      (r'\(con\s+([^\s)]+)\s+([^\s)]+)\)',
              lambda g: f"(icon {g[0]} {g[1]})"),
 "elim":     (r'\(elim\s+([^\s)]+)\s+([^\s)]+)\s+([^\s)]+)\)',
              lambda g: f"(ielim {g[0]} iˣ {g[1]} {g[2]})"),
 "⌜Mu⌝":    (r'\(⌜Mu⌝\s+([^\s)]+)\)',
              lambda g: "(⌜IMu⌝ Dˣ Iˣ iˣ)"),
 "ξ-con":    (r'\(ξ-con\s+([^\s)]+)\)',
              lambda g: f"(ξ-icon {g[0]})"),
 "ι-elim":   (r'\(ι-elim\s+([^\s)]+)\s+([^\s)]+)\s+([^\s)]+)\s+([^\s)]+)\)',
              lambda g: f"(ι-ielim {g[0]} iˣ {g[1]} {g[2]} {g[3]})"),
 "ξ-elimᵐ": (r'\(ξ-elimᵐ\s+([^\s)]+)\)',
              lambda g: f"(ξ-ielimᵐ {g[0]})"),
 "ξ-elimᵗ": (r'\(ξ-elimᵗ\s+([^\s)]+)\)',
              lambda g: f"(ξ-ielimᵗ {g[0]})"),
}

def generate(path, fns, extra_rows=True):
    L = open(path).read().split("\n")
    # ⚠ dedup UP TO PATTERN-VARIABLE RENAMING.  Textual equality missed
    #   `(ι-ielim D iˣ ms k p) ()` vs `(ι-ielim D i ms k p) ()` — the same
    #   clause with a different binder name — and Agda accepted the second
    #   as an unreachable clause with only a warning.
    def norm(line):
        head = line.split(" = ")[0]
        return re.sub(r'\b[a-zA-Zι-ϕ][A-Za-z0-9ˣ₀-₉\'-]*\b',
                      lambda m: m.group(0) if m.group(0)[0] in "ξι⌜" or "-" in m.group(0)
                      else "·", head)
    present = set(L); present_norm = {norm(l) for l in L}   # invariant 1
    ins = {}
    made = Counter(); skipped = Counter()
    for i, l in enumerate(L):
        fn = next((f for f in fns if l.startswith(f + " ")), None)
        if fn is None: continue
        eq = l.find(" = ")
        for key, (rx, mk) in PAT.items():
            m = re.search(rx, l)
            if not m: continue
            if eq != -1 and m.start() > eq: continue        # LHS only
            rhs = l[eq+3:] if eq != -1 else ""
            if key == "⌜Mu⌝" and re.search(r'\b'+re.escape(m.group(1))+r'\b', rhs):
                skipped[fn] += 1; continue                  # binder used on RHS
            new = l[:m.start()] + mk(m.groups()) + l[m.end():]
            if new in present or norm(new) in present_norm:  # invariant 1
                skipped[fn] += 1; continue
            if new.count("(") != new.count(")"):            # invariant 2
                skipped[fn] += 1; continue
            present.add(new); present_norm.add(norm(new))
            ins.setdefault(i, []).append(new); made[fn] += 1
    for i in sorted(ins, reverse=True):                     # invariant 3
        L[i+1:i+1] = ins[i]
    open(path, "w").write("\n".join(L))
    return made, skipped

if __name__ == "__main__":
    made, skipped = generate(sys.argv[1], sys.argv[2:])
    for fn in sys.argv[2:]:
        print(f"  {fn:<20} +{made[fn]:<3} (skipped {skipped[fn]})")
    print(f"  total {sum(made.values())}")
