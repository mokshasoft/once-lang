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
  ⚠ BLIND SPOT, not yet handled: clauses INSIDE a `where` block are
    INDENTED, so the `startswith(fn + " ")` match misses them entirely and
    the function looks like it has no rows to mirror.  `payT-bwd₀` had to
    be done by hand.  If a function reports "SKIP — no rows found" but you
    can see its clauses, check the indentation before believing it.

  4. a `with` HEAD OWNS THE `...` LINES BELOW IT.  Inserting immediately
     after such a head SPLITS the clause: the original loses its body and
     the new head steals it.  Agda then reports "Missing with-clauses" for
     the VICTIM, not for the line that caused it.  Insert past the whole
     block, and copy the continuations too (renamed).
     ⚠ And when the copied continuation matches on `Mu-nf`'s `refl`, the
     `IMu` twin needs `mkIMuRed _ refl _` — `IMu-reduct` returns a RECORD,
     because `IMu` is inert-SHAPED, not inert.
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

# ── the ⊩ RULE SET ────────────────────────────────────────────────────
# Mirrors a `⊩₀Mu`/`⊩₁Mu` clause to its indexed twin.  ⚠ the Mu-specific
# helpers must be renamed IN THE RHS TOO — `mm-exp` is not `imm-exp`, and a
# clause that kept the non-indexed helper would be about the wrong family.
SEM = [(r'⊩₀Mu', '⊩₀IMu'), (r'⊩₁Mu', '⊩₁IMu'),
       (r'\bMuMem\b', 'IMuMem'), (r'\bpredsOf\b', 'ipredsOf'),
       (r'\bmm-ne\b', 'imm-ne'), (r'\bmm-con\b', 'imm-icon'),
       (r'\bmm-exp\b', 'imm-exp'), (r'\bmumem-whred\b', 'imumem-whred'),
       (r'\bDInterp\b', 'IDInterp'), (r'\bKInterp\b', 'IKInterp'),
       # ⚠ the STUCK-HEAD constructor too — a generated clause that kept
       #   `sh-Mu` claims `StkHd (Mu …)` where `StkHd (IMu …)` is needed.
       (r'\bsh-Mu\b', 'sh-IMu'), (r'\bnn-Mu\b', 'nn-IMu'),
       (r'\bst-Mu\b', 'st-IMu'), (r'\birrelMu\b', 'irrelIMu'),
       (r'\bliftK\b', 'iliftK'), (r'\birrelAtK\b', 'irrelIAtK')]

def generate_sem(path, fns):
    L = open(path).read().split("\n")
    heads = {l for l in L if l and not l[0].isspace() and not l.startswith("...")}
    ins = {}; made = Counter(); skipped = Counter()
    for i, l in enumerate(L):
        fn = next((f for f in fns if l.startswith(f + " ")), None)
        if fn is None: continue
        if not re.search(r'⊩[₀₁]Mu', l): continue
        # invariant 4: a `with` head owns the `...` lines below it
        j = i + 1
        while j < len(L) and L[j].startswith("..."): j += 1
        block = L[i:j]
        nb = []
        for x in block:
            n = x
            for rx, rep in SEM: n = re.sub(rx, rep, n)
            if "IMu-reduct" in " ".join(nb + [n]):
                n = re.sub(r'\|\s*refl\s*=', '| mkIMuRed _ refl _ =', n)
            nb.append(n)
        if nb == block or nb[0] in heads:      # invariant 1, on the HEAD
            skipped[fn] += 1; continue
        if any(x.count("(") != x.count(")") for x in nb):   # invariant 2
            skipped[fn] += 1; continue
        heads.add(nb[0])
        ins.setdefault(j - 1, []).extend(nb); made[fn] += 1   # past the block
    for i in sorted(ins, reverse=True):
        L[i+1:i+1] = ins[i]
    open(path, "w").write("\n".join(L))
    return made, skipped

if __name__ == "__main__":
    mode = generate_sem if sys.argv[1] == "--sem" else generate
    args = sys.argv[2:] if sys.argv[1] == "--sem" else sys.argv[1:]
    made, skipped = mode(args[0], args[1:])
    for fn in args[1:]:
        print(f"  {fn:<20} +{made[fn]:<3} (skipped {skipped[fn]})")
    print(f"  total {sum(made.values())}")
