#!/usr/bin/env python3
"""★★★ "GIVE ME EVERY DECLARATION WITH THE SAME TYPE AS THIS ONE" —
   BUT MODULO ANTI-UNIFICATION, WHICH IS THE WHOLE POINT.

Usage:  tools/find-dup-lemmas.py <name> [max-holes]     one query
        tools/find-dup-lemmas.py --families [min-size]  the whole tree

⚠⚠ EXACT SAME-TYPE LOOKUP FINDS NOTHING HERE, and Agda already ships it
  (`C-c C-z` search-about; Mimer `C-c C-a` will even fill the hole).
  The lemmas this project writes twice NEVER share a type: `towerA` /
  `towerJ` / `towerJ⁵` / `tower⁶` differ in DEPTH, `nat4₂` / `nat5₂` /
  `nat7` differ in FOLD COUNT, `wkTyK-sub` / `wkAtK-sub` differ in the
  PROGRAM.  In every case the differing thing is the parameter that
  should have been an argument — so the useful key is the type with
  those spans replaced by holes, and THE NUMBER OF HOLES IS THE VERDICT:

      0 holes   a literal duplicate — delete one
      1-2       the same theorem with a parameter frozen; this is the
                lemma that should have taken it as an argument
      many      unrelated; shared shape only

★ MEASURED, THE DAY IT WAS WRITTEN.  `tower⁶` in `Knot/IihsAgree` is
  `towerJ⁵`'s next rung and was written a THIRD time by hand before this
  query was run.  `Lib/Wk`'s own note says "three customers now; at a
  fourth, stop and write `tower^`" — written by someone who could not
  see that rungs six and seven already existed two directories away.
  ⇒ the failure is not that nobody noticed; it is that NOTICING DOES NOT
    SCALE PAST ONE MODULE.

⚠ KNOWN WEAKNESS, and it is the depth families.  Flat token
  anti-unification is strong on "same shape, different program"
  (`wkTyK-sub` finds its four siblings at 3 holes) and weak on "same
  shape, different DEPTH" (`towerJ⁵` needs 12 before `tower⁶` appears),
  because another rung changes the term SIZE, not one span.  For those
  the key wants run-length compression of the repeating motif first.

Original docstring:

  query(name) -> every declaration whose TYPE is the same as `name`'s
                 after replacing at most K differing spans by holes.

The count of holes is the answer to "should this have been a library
lemma": 0 holes = literal duplicate; 1-2 holes = the SAME theorem with a
parameter frozen, i.e. exactly the lemma that should have taken it as an
argument; many holes = unrelated.
"""
import os, re, io, sys, difflib

ROOT, SKIP = ".", ("/Negative/", "/Trust/", "/Comparison/", "/_build")
sig_re = re.compile(r"(?m)^([^\s\-{(][^\s:]*)\s*:\s")

def decls():
    for dp, dn, fn in os.walk(ROOT):
        if any(s in dp + "/" for s in SKIP): continue
        for f in sorted(fn):
            if not f.endswith(".agda"): continue
            p = os.path.join(dp, f)
            t = io.open(p, encoding="utf-8").read()
            t = re.sub(r"(?m)^\s*--.*$", "", t)
            lines = t.split("\n")
            for k, ln in enumerate(lines):
                m = sig_re.match(ln)
                if not m: continue
                body = [ln[m.end():]]
                for nx in lines[k+1:]:
                    if nx[:1].strip() and not nx.startswith(" "): break
                    body.append(nx.strip())
                    if len(body) > 25: break
                # ★ AND THE PROOF BODY — the SIZE is what makes a hit
                #   interesting: a 1-line proof that matches a library
                #   lemma is fine, a 20-line one is the finding.
                nb, seenhd = 0, False
                for nx in lines[k+1:]:
                    if nx.startswith(m.group(1) + " ") or nx.startswith(m.group(1) + "\n"):
                        seenhd = True
                    if seenhd and nx[:1].strip() and not nx.startswith(m.group(1)):
                        break
                    if seenhd and nx.strip(): nb += 1
                    if nb > 400: break
                yield m.group(1), re.sub(r"\s+", " ", " ".join(body)).strip(), p[2:], nb

def toks(s): return re.findall(r"[A-Za-z0-9₀-₉⁰-⁹'ᵀ_\-]+|\S", s)

def holes(a, b):
    """number of differing spans between two token lists (anti-unification)."""
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    n = sum(1 for op, *_ in sm.get_opcodes() if op != "equal")
    return n, sm.ratio()

ALL = list(decls())
if sys.argv[1:2] == ["--vs-lib"]:
    # ★★★ "WHICH PROOFS WOULD A LIBRARY CALL HAVE CLOSED?"
    #   target  = every declaration OUTSIDE Lib/ whose proof is more than
    #             a couple of lines (a one-liner is already a call)
    #   library = every declaration IN Lib/
    #   report  = pairs within K holes, BIGGEST WASTED PROOF FIRST.
    # ⚠ BUCKETED, or this is 4000² anti-unifications.  The bucket key is
    #   the relation and the arrow count, both of which anti-unification
    #   can never change.
    K    = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    MINB = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    # ★★★ THE PRECISION FIX, AND IT IS THE WHOLE TOOL.
    #   Without it `⊢monusLeZ` "matches" 28 unrelated derivations: every
    #   `Γ ⊢ t ∷ A` shares one skeleton, so anti-unifying a three-place
    #   relation whose slots are all holes matches EVERYTHING.  Shape
    #   alone is worthless on a judgement.
    #   ⇒ require the pair to share a RARE token — an identifier that
    #     appears in few declarations.  `ren-as-sub`/`ren-sub` share
    #     `renTm`+`subTm`; `⊢monusLeZ` and `⊢ihsKap` share only `⊢`, `∷`
    #     and context names, which every derivation has.
    import collections as _c
    _df = _c.Counter()
    for _n, _t, _m, _b in ALL: _df.update(set(toks(_t)))
    _NTOT = len(ALL)
    def rare(t):
        return {w for w in toks(t)
                if _df[w] <= max(3, _NTOT // 60) and len(w) > 2}
    def rel(t): return "≡" if "≡" in t else ("⟶*" if "⟶*" in t else "·")
    def key(t): return (rel(t), t.count("→") // 2)
    lib, tgt_ = [], []
    for d in ALL:
        (lib if d[2].startswith("Lib/") else tgt_).append(d)
    buck = {}
    for d in lib: buck.setdefault(key(d[1]), []).append(d)
    hits = []
    for nm, ty, mod, nb in tgt_:
        if nb < MINB or len(ty) < 30: continue
        for ln, lt, lm, _ in buck.get(key(ty), ()):
            h, r = holes(toks(ty), toks(lt))
            if h > K or r <= 0.62: continue
            sh = rare(ty) & rare(lt)
            if not sh: continue          # ← shape without substance
            hits.append((-nb, h, nm, mod, ln, lm, ",".join(sorted(sh)[:3]))); break
    hits.sort()
    print("== PROOFS A `Lib/` LEMMA MAY HAVE CLOSED ==")
    print("   %d candidate(s), <=%d hole(s), proof >=%d lines."
          % (len(hits), K, MINB))
    print("   ⚠ CANDIDATES, NOT DEFECTS — same shape is not same theorem.")
    print("     Confirm by putting the body in a hole and calling the")
    print("     library lemma; if it type-checks, the proof was the")
    print("     library lemma.\n")
    print("   %-5s %-24s %-30s %-20s %s"
          % ("lines", "proof", "in", "library lemma", "shared rare tokens"))
    for nb, h, nm, mod, ln, lm, sh in hits[:30]:
        print("   %-5d %-24s %-30s %-20s %s" % (-nb, nm[:24], mod[:30], ln[:20], sh))
    sys.exit(0)

if sys.argv[1:2] == ["--families"]:
    import collections
    MIN = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    seen, fams = set(), []
    for nm, ty, mod, _nb in ALL:
        if nm in seen or len(ty) < 30: continue
        grp = [(nm, mod)]
        for n2, t2, m2, _n2b in ALL:
            if n2 == nm or n2 in seen: continue
            h, r = holes(toks(ty), toks(t2))
            if h <= 3 and r > 0.6: grp.append((n2, m2)); seen.add(n2)
        if len(grp) >= MIN:
            seen.add(nm); fams.append((len({m for _, m in grp}), len(grp), nm, ty, grp))
    fams.sort(reverse=True)
    print("== FAMILIES: one theorem, written N times, across M modules ==")
    print("   (sorted by MODULE spread — same-module families are usually")
    print("    a generated block, cross-module ones are the real finding)\n")
    for M, N, nm, ty, grp in fams[:10]:
        if M < 2: continue
        print("%2d module(s), %2d member(s)   %s" % (M, N, ty[:72]))
        for n2, m2 in sorted(grp): print("      %-20s %s" % (n2, m2))
        print()
    sys.exit(0)

target = sys.argv[1]; K = int(sys.argv[2]) if len(sys.argv) > 2 else 3
tgt = [d for d in ALL if d[0] == target]
if not tgt: sys.exit("no declaration named %s" % target)
_, ty, mod = tgt[0][0:3][0], tgt[0][1], tgt[0][2]
print("QUERY  %s   (%s)\n       %s\n" % (target, mod, ty[:100]))
hits = []
for nm, t2, m2, _x in ALL:
    if nm == target: continue
    h, r = holes(toks(ty), toks(t2))
    if h <= K and r > 0.55: hits.append((h, -r, nm, m2, t2))
hits.sort()
print("SAME TYPE MODULO <=%d HOLES — %d hit(s)\n" % (K, len(hits)))
for h, nr, nm, m2, t2 in hits[:14]:
    print("  %d hole(s)  %-14s %-38s" % (h, nm, m2))
