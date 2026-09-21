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
                nb, seenhd, btxt = 0, False, []
                for nx in lines[k+1:]:
                    if nx.startswith(m.group(1) + " ") or nx.startswith(m.group(1) + "\n"):
                        seenhd = True
                    if seenhd and nx[:1].strip() and not nx.startswith(m.group(1)):
                        break
                    if seenhd and nx.strip(): nb += 1; btxt.append(nx)
                    if nb > 400: break
                yield (m.group(1), re.sub(r"\s+", " ", " ".join(body)).strip(),
                       p[2:], nb, " ".join(btxt))

def toks(s): return re.findall(r"[A-Za-z0-9₀-₉⁰-⁹'ᵀ_\-]+|\S", s)

def holes(a, b):
    """number of differing spans between two token lists (anti-unification)."""
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    n = sum(1 for op, *_ in sm.get_opcodes() if op != "equal")
    return n, sm.ratio()

ALL = list(decls())
# ⚠⚠ EVERY MODE UNPACKS THIS TUPLE.  Twice now a field has been added
#   for one mode and the others left unpacking the old arity — the bug
#   is silent until that mode is run, and the mode being worked on is
#   the one that gets run.  Assert the shape once, here.
assert all(len(d) == 5 for d in ALL), "decls() arity changed — fix EVERY mode"
if sys.argv[1:2] == ["--same-name"]:
    # ★★★ THE CHEAPEST DETECTOR, AND IT WAS ADDED LAST — which is the
    #   lesson.  Three modes of anti-unification were built before
    #   anyone asked the trivial question: **is this name defined in more
    #   than one module?**  Exact, no heuristics, no tuning, O(n).
    #
    # ⚠ IT FOUND WHAT THE CLEVER MODES MISSED.  `--vs-lib` at its first
    #   (stricter) settings reported 7 duplicates in `Examples/AmrecT`;
    #   this reports ELEVEN, including `aIHT-fit` and `aStepT-ren`, both
    #   byte-identical to `Lib/Rec` and `Lib/Amrec`.  Recall beat
    #   precision, exactly as the user argued.
    #
    # ⚠⚠ A NAME COLLISION IS NOT A DUPLICATE.  Same name ≠ same type ≠
    #   same proof, and this repository has DELIBERATE parallel families
    #   — `row-lam` in `RenAgree` and `SubAgreeRows` are the renaming and
    #   substitution twins and must both exist.  ⇒ default to the pairs
    #   that involve a `Lib/` module, where a collision is much more
    #   likely to mean "the example re-derived the library"; `--all`
    #   shows the rest.
    # ⚠⚠⚠ A DUPLICATE CAN BE LOAD-BEARING, AND THE TOP-RANKED ONE IS.
    #   `cong₃` in `Spec/Syntax.agda` is BYTE-IDENTICAL to `Lib/Wk.agda`
    #   and MUST NOT BE DELETED: `tools/sweep.sh` asserts *"KERNEL IS
    #   INDEPENDENT: Spec/ and Metatheory/ import no Lib/ or Examples/"*,
    #   whose whole point is that a defect in a library cannot reach
    #   consistency, canonicity or SN.  Removing the copy would make the
    #   kernel depend on a library and silently void that guarantee.
    #   ⚠ AND THE DIRECTION IS THE OPPOSITE OF THE OBVIOUS ONE.  The ban
    #     is one-way: `Lib/` MAY import `Spec/` and `Metatheory/`, only
    #     the reverse is forbidden.  So the KERNEL copy is the one that
    #     must stay, and the LIB copy is the deletion candidate — e.g.
    #     `Lib/DvdArith`'s `⟶*-⌜Id⌝ʳ` duplicates `Metatheory/RedCong`'s
    #     and could import it instead.  The first version of this flag
    #     said "do not delete" for BOTH sides and would have sent a
    #     reader the wrong way.
    #   ⇒ the kernel is FLAGGED, not filtered — the collision is real and
    #     worth seeing; what is wrong is which side you remove.
    # ★ Third instance of the same lesson: the tool finds candidates, and
    #   the decision needs context no type-level analysis can supply
    #   (see `--could-simplify`'s +34% result, and the deliberate
    #   `row-lam` ren/sub twins below).
    KERNEL = ("Spec/", "Metatheory/")
    ALLM = len(sys.argv) > 2 and sys.argv[2] == "--all"
    import collections as _c
    where = _c.defaultdict(list)
    for nm, ty, mod, nb, bt in ALL: where[nm].append(mod)
    dups = {n: sorted(set(v)) for n, v in where.items() if len(set(v)) > 1}
    lib  = {n: v for n, v in dups.items()
            if any(m.startswith("Lib/") for m in v)}
    show = dups if ALLM else lib
    print("== SAME NAME DEFINED IN MORE THAN ONE MODULE ==")
    print("   %d collision(s) total; %d involve a Lib/ module.%s\n"
          % (len(dups), len(lib), "" if ALLM else "  (--all for the rest)"))
    nk = 0
    for n, v in sorted(show.items()):
        kern = [m for m in v if m.startswith(KERNEL)]
        tag = ""
        if kern and any(m.startswith("Lib/") for m in v):
            tag = ("   ⚠ KEEP %s/ — kernel may not import Lib/; the Lib/ copy is the candidate"
                   % kern[0].split("/")[0])
            nk += 1
        print("   %-22s %s%s" % (n, "   ".join(v), tag))
    if nk:
        print("\n   ⚠ %d collision(s) involve the kernel: keep the kernel side,"
              "\n     consider removing the Lib/ side (the import ban is ONE-WAY)." % nk)
    sys.exit(0)

if sys.argv[1:2] == ["--could-simplify"]:
    # ★★★ THE LIBRARY AUTHOR'S QUESTION, AND IT IS THE USEFUL ONE:
    #   "does THIS lemma prove something that could have simplified
    #    these proofs?"
    #
    # ⚠ THE INVERSE OF `--vs-lib`, AND NOT A COSMETIC ONE.  With the
    #   lemma FIXED this is n comparisons, not n², so it can afford to
    #   be generous — and it catches the case `--vs-lib` structurally
    #   cannot: a lemma that belonged as a STEP INSIDE a proof,
    #   shortening it, rather than one that replaces the proof whole.
    #   That is the common case.
    #
    # ★ RECALL OVER PRECISION, DELIBERATELY.  No filter — every
    #   candidate is reported, RANKED.  A missed lemma is invisible
    #   forever; a false positive costs a reader thirty seconds.
    #   ⇒ the IDF weight is a SORT KEY here, never a gate.
    #
    # THE SIGNAL: a proof that manipulates exactly the constants this
    # lemma is about, and never calls it.
    import collections as _c
    L = sys.argv[2]; MINB = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    lem = [d for d in ALL if d[0] == L]
    if not lem: sys.exit("no declaration named %s" % L)
    _, lty, lmod, _, _ = lem[0]
    _df = _c.Counter()
    for _n, _t, _m, _b, _x in ALL: _df.update(set(toks(_t)))
    N = len(ALL)
    import math
    # the lemma's vocabulary, each weighted by how DISTINCTIVE it is
    voc = {w: math.log(N / max(1, _df[w]))
           for w in set(toks(lty)) if len(w) > 2 and not w[0].isupper()}

    # ★★ THE STRONG SIGNAL IS THE LEMMA'S **LHS SHAPE**, NOT ITS
    #   VOCABULARY.  Ranking on vocabulary alone put every 100-line
    #   substitution lemma at the top: of course a big proof about
    #   substitution mentions `subTm`, `renTm` and `single`.  That is a
    #   statement about proof LENGTH, not about whether this lemma
    #   applies.
    #   ⇒ take the lemma's left-hand side, turn its identifiers into
    #     literals and everything else into gaps, and look for THAT in
    #     the proof text.  A proof that writes `subTm (single v)
    #     (renTm vs t)` by hand is re-deriving `wk-single` in place.
    # ⚠ VOCABULARY IS KEPT AS A WEAK TIER, not dropped — recall first.
    #   A shape hit outranks any amount of vocabulary; vocabulary-only
    #   hits are still reported, below.
    lhs = re.split(r"≡|⟶\*", lty.split("→")[-1])[0].strip()
    idents = [w for w in re.findall(r"[A-Za-zΓΔΘ_][A-Za-z0-9₀-₉'ᵀ\-]*", lhs)
              if len(w) > 2 and _df[w] < N // 3]
    shape = re.compile(r"[\s\S]{0,40}?".join(map(re.escape, idents[:4]))) \
            if len(idents) >= 2 else None
    hits = []
    for nm, ty, mod, nb, bt in ALL:
        if nm == L or nb < MINB: continue
        if re.search(r"(?<![A-Za-z0-9])" + re.escape(L) + r"(?![A-Za-z0-9])", bt):
            continue                      # already calls it
        btk = set(toks(bt))
        sh = {w for w in voc if w in btk}
        if not sh: continue
        nshape = len(shape.findall(bt)) if shape else 0
        # ⚠ LENGTH IS PAYOFF, NOT LIKELIHOOD.  It is shown, not
        #   multiplied in — otherwise the longest proof always wins.
        score = nshape * 1000 + sum(voc[w] for w in sh)
        closes = holes(toks(ty), toks(lty))[0] <= 2
        hits.append((-score, -nb, nm, mod,
                     sorted(sh, key=lambda w: -voc[w])[:4], closes, nshape))
    hits.sort()
    print("== COULD `%s` HAVE SIMPLIFIED THESE?  (%s)" % (L, lmod))
    print("   %s" % lty[:96])
    print("   %d proof(s) manipulate its vocabulary and never call it."
          % len(hits))
    print("   ⚠ RANKED, NOT FILTERED — recall first.  Triage from the top;")
    print("     the tail is expected to be noise, and that is the trade.\n")
    nsh = sum(1 for h in hits if h[6])
    print("   ★ %d of them WRITE ITS LEFT-HAND SIDE BY HAND — those first.\n"
          % nsh)
    print("   %-4s %-5s %-24s %-28s %s" % ("LHS", "lines", "proof", "in", "shared vocabulary"))
    for sc, nnb, nm, mod, sh, closes, nshape in hits[:25]:
        print("   %-4s %-5d %-24s %-28s %s%s"
              % (("×%d" % nshape) if nshape else "-", -nnb, nm[:24], mod[:28],
                 ",".join(sh),
                 "   ★ SAME TYPE — may close it outright" if closes else ""))
    sys.exit(0)

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
    for _n, _t, _m, _b, _x in ALL: _df.update(set(toks(_t)))
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
    for nm, ty, mod, nb, _bt in tgt_:
        if nb < MINB or len(ty) < 30: continue
        for ln, lt, lm, _, _ in buck.get(key(ty), ()):
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
    # ⚠⚠ BUCKET, OR THIS IS 4000² ANTI-UNIFICATIONS.  The first version
    #   shipped unbucketed and was killed at 600s — `--vs-lib` had the
    #   bucketing and this mode did not, which is the hazard of two
    #   modes sharing a matcher but not its index.
    import collections as _c
    _df = _c.Counter()
    for _n, _t, _m, _b, _x in ALL: _df.update(set(toks(_t)))
    _NTOT = len(ALL)
    # ⚠ STRICTER THAN `--vs-lib`'s, and it has to be.  That mode gets
    #   free signal from the Lib/ vs non-Lib/ split; this one compares
    #   everything to everything, so structural vocabulary leaks through.
    #   At df<=66 the top "family" was 39 method typings sharing
    #   `imethTy KnotD IPair` — one SHAPE, 39 different theorems.
    def rare(t):
        return {w for w in toks(t) if _df[w] <= 5 and len(w) > 2}
    def rel(t): return "≡" if "≡" in t else ("⟶*" if "⟶*" in t else "·")
    def key(t): return (rel(t), t.count("→") // 2)
    buck = {}
    for d in ALL: buck.setdefault(key(d[1]), []).append(d)
    seen, fams = set(), []
    for nm, ty, mod, _nb, _bt in ALL:
        if nm in seen or len(ty) < 30: continue
        grp, rt = [(nm, mod)], rare(ty)
        if not rt: continue
        for n2, t2, m2, _n2b, _b2 in buck.get(key(ty), ()):
            if n2 == nm or n2 in seen: continue
            if not (rt & rare(t2)): continue
            h, r = holes(toks(ty), toks(t2))
            if h <= 3 and r > 0.6: grp.append((n2, m2)); seen.add(n2)
        if len(grp) >= MIN:
            seen.add(nm); fams.append((len({m for _, m in grp}), len(grp), nm, ty, grp))
    fams.sort(reverse=True)
    print("== SHAPE FAMILIES — candidates for GENERATION, not deletion ==")
    print("   ⚠ A FAMILY HERE IS NOT A DUPLICATE.  `--vs-lib` finds proofs")
    print("     a library lemma would have closed; this finds N theorems")
    print("     sharing ONE shape, which is a GENERATOR opportunity —")
    print("     `Variance`'s 22 `?-red` and 15 `?-ren` lemmas are 22 and 15")
    print("     genuinely different predicates, not copies.")
    print("   (sorted by module spread: same-module families are usually")
    print("    already a generated block)\n")
    for M, N, nm, ty, grp in fams[:10]:
        if M < 2: continue
        print("%2d module(s), %2d member(s)   %s" % (M, N, ty[:72]))
        for n2, m2 in sorted(grp): print("      %-20s %s" % (n2, m2))
        print()
    sys.exit(0)

target = sys.argv[1]; K = int(sys.argv[2]) if len(sys.argv) > 2 else 3
tgt = [d for d in ALL if d[0] == target]
if not tgt: sys.exit("no declaration named %s" % target)
_, ty, mod = tgt[0][0], tgt[0][1], tgt[0][2]
print("QUERY  %s   (%s)\n       %s\n" % (target, mod, ty[:100]))
hits = []
for nm, t2, m2, _nb2, _bt2 in ALL:
    if nm == target: continue
    h, r = holes(toks(ty), toks(t2))
    if h <= K and r > 0.55: hits.append((h, -r, nm, m2, t2))
hits.sort()
print("SAME TYPE MODULO <=%d HOLES — %d hit(s)\n" % (K, len(hits)))
for h, nr, nm, m2, t2 in hits[:14]:
    print("  %d hole(s)  %-14s %-38s" % (h, nm, m2))
