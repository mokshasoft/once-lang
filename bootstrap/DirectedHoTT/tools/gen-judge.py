#!/usr/bin/env python3
"""
gen-judge.py — the `⊢` ROWS of the Knot's typing judgement (D077), from a
rule table.  Emits `Examples/Knot/JudgeRowsGen.agda`.

★ ONE SCHEME PER ROW (the hand-written ⊢lam/⊢app/⊢var are its templates,
  `Examples/Knot/JudgeRowsTm.agda`):

  * the premises are a PARAMETRIC telescope `T⊢xI Ps` over the positions it
    mentions (depth `J`, context `G`, conclusion `X`, the subject's fields
    `F…`, the type pattern's fields `Q…`, the existentials `E…`), with
      - its law `T⊢xI-sub` — one congruence (`T⊢xA-cong`, explicit
        arguments) over the telescope's ATOMS (`sub0`, `wk`, `DF`, a Ford
        code), each atom's own `-sub` lemma;
      - its congruence `T⊢xI-cong` (all positions);
      - its typing `okT⊢xI` at ANY context and positions;
  * the row's telescope `T⊢x j a b` puts the EXISTENTIALS in front as
    σ-fields (the positions are weakened past them; `JudgeCase.w1…w3`) —
    its law chains the σ-codes' laws with `T⊢xI-sub` and `T⊢xI-cong`;
  * a PLAIN row (`a b = p c`) is `defRow`; a CASE row (`a b = q (Γ , p)`,
    the conclusion type a pattern with fresh variables) is a `CaseRow`
    on the type's head.

★ WHEN A CASE, WHEN A FORD (D077): the conclusion type is a CASE when it is
  a constructor pattern whose variables are fresh (they are bound by the
  case — no existential, no equation); it is ONE FORD field when it is
  determined by the subject or computed (`El c`, `Hom (El c) t t`, `B[u]`).

The DSL — expressions:
  'J' 'G' 'X'            depth, context, conclusion type
  ('f', i) ('q', i)      the subject's / the type pattern's i-th field
  ('e', i)               the i-th existential
  ('k', name, a…)        a Knot former `k<name>` (`Sig`), fields by shape
  ('sub0', s, d, t, u)   t[u/0]            ('wk', s, d, t)  weakening
  ('DF', d, I)           DescF I           ('cext', g, A)   Γ ▹ A
  depths: 'J' | 'J+1' | 'J+2'
entries (in order; a Ford `id` last):
  ('ty', d, g, A)   ('tm', d, g, t, A)   ('id', ('Ty'|'Tm', d), a, b)
existentials: ('Ty', d) | ('Tm', d) | ('Nat',)

Usage:  python3 tools/gen-judge.py [--check]
"""
import re
import os, sys, importlib.util

# the licence header every Agda file in bootstrap/ carries
COPYRIGHT = "-- SPDX-License-Identifier: AGPL-3.0-or-later\n-- Copyright (C) 2025-2026 Jonas Claesson\n\n"

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("genknot", os.path.join(HERE, "gen-knot.py"))
gk = importlib.util.module_from_spec(spec); spec.loader.exec_module(gk)

ROOT = gk.ROOT
OUT = os.path.join(ROOT, "Examples", "Knot", "JudgeRowsGen.agda")

# ------------------------------------------------------------ the signature
SIG = {}          # 'Pi' -> (sort, fields, index-in-sort)
TMHEADS = []      # term constructor names, in order
TYHEADS = []
def load_sig():
    idx = {"RTy": 0, "RTm": 0}
    for data, name, fs in gk.parse():
        n = gk.kname(name)[1:]
        SIG[n] = (gk.SORTS[data], fs, idx[data])
        (TYHEADS if data == "RTy" else TMHEADS).append(n)
        idx[data] += 1

def shape_name(n): return "sh-k" + n
def ok_name(n): return "ok-k" + n

# ------------------------------------------------------------ the rule table
S0, S1 = 0, 1
def tm(d, g, t, A): return ("tm", d, g, t, A)
def ty(d, g, A): return ("ty", d, g, A)
def k(n, *a): return ("k", n) + a
F = lambda i: ("f", i)
Q = lambda i: ("q", i)
E = lambda i: ("e", i)
U = k("U"); BASE = k("base"); NAT = k("Nat")
def El(c): return k("El", c)

RULES = {
  # head: dict(case=type-head | None, ex=[…], ents=[…])
  "pair":   dict(case="Sg", ents=[ty("J+1", ("cext", "G", Q(0)), Q(1)), tm("J", "G", F(0), Q(0)),
                                  tm("J", "G", F(1), ("sub0", 0, "J", Q(1), F(0)))]),
  "absurd": dict(ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), BASE), ("id", ("Ty", "J"), "X", El(F(0)))]),
  "ordtr":  dict(ents=[tm("J", "G", F(0), NAT), tm("J", "G", F(1), NAT), tm("J", "G", F(2), NAT),
                       tm("J", "G", F(3), k("Hom", NAT, F(0), F(1))), tm("J", "G", F(4), k("Hom", NAT, F(1), F(2))),
                       ("id", ("Ty", "J"), "X", k("Hom", NAT, F(0), F(2)))]),
  "fst":    dict(ex=[("Ty", "J+1")], ents=[tm("J", "G", F(0), k("Sg", "X", E(0)))]),
  "snd":    dict(ex=[("Ty", "J"), ("Ty", "J+1")],
                 ents=[tm("J", "G", F(0), k("Sg", E(0), E(1))), ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(1), k("fst", F(0))))]),
  "cbase":  dict(case="U", ents=[]),
  "cPi":    dict(case="U", ents=[tm("J", "G", F(0), U), tm("J+1", ("cext", "G", El(F(0))), F(1), U)]),
  "cSg":    dict(case="U", ents=[tm("J", "G", F(0), U), tm("J+1", ("cext", "G", El(F(0))), F(1), U)]),
  "cHom":   dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), tm("J", "G", F(2), El(F(0)))]),
  "hrefl":  dict(ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), ("id", ("Ty", "J"), "X", k("Hom", El(F(0)), F(1), F(1)))]),
  "cId":    dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), tm("J", "G", F(2), El(F(0)))]),
  "idrefl": dict(ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), El(F(0))), ("id", ("Ty", "J"), "X", k("Id", El(F(0)), F(1), F(1)))]),
  "jsub":   dict(ex=[("Ty", "J"), ("Tm", "J"), ("Tm", "J")],
                 ents=[tm("J+1", ("cext", "G", E(0)), F(0), U), tm("J", "G", E(1), E(0)), tm("J", "G", E(2), E(0)),
                       tm("J", "G", F(1), k("Id", E(0), E(1), E(2))), tm("J", "G", F(2), El(("sub0", 1, "J", F(0), E(1)))),
                       ("id", ("Ty", "J"), "X", El(("sub0", 1, "J", F(0), E(2))))]),
  "unit":   dict(case="Unit", ents=[]),
  "nzero":  dict(case="Nat", ents=[]),
  "nsuc":   dict(case="Nat", ents=[tm("J", "G", F(0), NAT)]),
  "con":    dict(case="IMu", ents=[tm("J", "G", Q(0), U), tm("J", "G", Q(1), ("DF", "J", Q(0))), tm("J", "G", Q(2), El(Q(0))),
                                   tm("J", "G", F(0), El(k("dpay", Q(0), Q(1), k("app", Q(1), Q(2)))))]),
  "dI":     dict(case="Desc", ents=[tm("J", "G", Q(0), U)]),
  "dS":     dict(case="Desc", ents=[tm("J", "G", Q(0), U), tm("J", "G", F(0), U),
                                    tm("J", "G", F(1), k("Pi", El(F(0)), k("Desc", ("wk", 1, "J", Q(0)))))]),
  "dR":     dict(case="Desc", ents=[tm("J", "G", Q(0), U), tm("J", "G", F(0), El(Q(0))), tm("J", "G", F(1), k("Desc", Q(0)))]),
  "dpay":   dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), ("DF", "J", F(0))), tm("J", "G", F(2), k("Desc", F(0)))]),
  "cNat":   dict(case="U", ents=[]),
  "cIMu":   dict(case="U", ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), ("DF", "J", F(0))), tm("J", "G", F(2), El(F(0)))]),
  "cFin":   dict(case="U", ents=[tm("J", "G", F(0), NAT)]),
  "cUnit":  dict(case="U", ents=[]),
}
# the opaque operations (`Knot/SubEnv`): result `K sort (d + out)` (sort 0 unless given), argument sorts and depth offsets
OPS = {
  "iinstTmK": dict(sort=1, out=0, args=[(1, 0), (1, 0), (1, 2)]),
  "pwShK":    dict(sort=1, out=2, args=[(1, 2)]),
  "wk2uK":    dict(out=3, args=[(0, 2)]),
  "nrsK":    dict(out=2, args=[(0, 1)]),
  "pairSK":  dict(out=2, args=[(0, 1)]),
  "fsucSK":  dict(out=1, args=[(0, 1)]),
  "iinstK":  dict(out=0, args=[(1, 0), (1, 0), (0, 2)]),
  "MethTyK": dict(out=0, args=[(1, 0), (1, 0), (0, 2)]),
}
def MC(d, g, I, D): return ("mc", d, g, I, D)
# `Fin`'s index is a Nat TERM (S7b step 2): its numerals are Knot terms
NSUC = lambda e: k("nsuc", e)
NZERO = k("nzero")

RULES.update({
  "natrec": dict(ex=[("Ty", "J+1")],
                 ents=[ty("J+1", ("cext", "G", NAT), E(0)), tm("J", "G", F(0), ("sub0", 0, "J", E(0), k("nzero"))),
                       tm("J+2", ("cext", ("cext", "G", NAT), E(0)), F(1), ("nrsK", "J", E(0))), tm("J", "G", F(2), NAT),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(0), F(2)))]),
  "fcase":  dict(ex=[("Tm", "J"), ("Ty", "J+1")],
                 ents=[ty("J+1", ("cext", "G", k("Fin", NSUC(E(0)))), E(1)), tm("J", "G", F(0), k("Fin", NSUC(E(0)))),
                       tm("J", "G", F(1), ("sub0", 0, "J", E(1), k("fzero"))),
                       tm("J+1", ("cext", "G", k("Fin", E(0))), F(2), ("fsucSK", "J", E(1))),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(1), F(0)))]),
  "fcase0": dict(ex=[("Ty", "J+1")],
                 ents=[ty("J+1", ("cext", "G", k("Fin", NZERO)), E(0)), tm("J", "G", F(0), k("Fin", NZERO)),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(0), F(0)))]),
  "psplit": dict(ex=[("Ty", "J"), ("Ty", "J+1"), ("Ty", "J+1")],
                 ents=[ty("J", "G", E(0)), ty("J+1", ("cext", "G", E(0)), E(1)), ty("J+1", ("cext", "G", k("Sg", E(0), E(1))), E(2)),
                       tm("J", "G", F(1), k("Sg", E(0), E(1))),
                       tm("J+2", ("cext", ("cext", "G", E(0)), E(1)), F(0), ("pairSK", "J", E(2))),
                       ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(2), F(1)))]),
  "ielim":  dict(ex=[("Tm", "J"), ("Ty", "J+2")],
                 ents=[tm("J", "G", E(0), U), tm("J", "G", F(0), ("DF", "J", E(0))), ty("J+2", MC("J", "G", E(0), F(0)), E(1)),
                       tm("J", "G", F(2), ("MethTyK", "J", E(0), F(0), E(1))), tm("J", "G", F(1), El(E(0))),
                       tm("J", "G", F(3), k("IMu", E(0), F(0), F(1))),
                       ("id", ("Ty", "J"), "X", ("iinstK", "J", F(1), F(3), E(1)))]),
  "dih":    dict(ex=[("Tm", "J"), ("Ty", "J+2")],
                 ents=[tm("J", "G", E(0), U), tm("J", "G", F(0), ("DF", "J", E(0))), ty("J+2", MC("J", "G", E(0), F(0)), E(1)),
                       tm("J", "G", F(1), ("MethTyK", "J", E(0), F(0), E(1))), tm("J", "G", F(2), k("Desc", E(0))),
                       tm("J", "G", F(3), El(k("dpay", E(0), F(0), F(2)))),
                       ("id", ("Ty", "J"), "X", k("DIh", F(0), E(1), F(2), F(3)))]),
})

V0 = ("v0",)
V1 = ("v1",)
RULES.update({
  # flat? cA ≡ true is a σ-field of the `Flat` family (a lower stratum)
  "ap": dict(ex=[("Tm", "J"), ("Pred", "Flat", "J", E(0)), ("Tm", "J"), ("Tm", "J")],
             ents=[tm("J", "G", E(0), U), tm("J", "G", F(0), U), tm("J+1", ("cext", "G", El(E(0))), F(1), El(("wk", 1, "J", F(0)))),
                   tm("J", "G", E(2), El(E(0))), tm("J", "G", E(3), El(E(0))), tm("J", "G", F(2), k("Hom", El(E(0)), E(2), E(3))),
                   ("id", ("Ty", "J"), "X", k("Hom", El(F(0)), ("sub0", 1, "J", F(1), E(2)), ("sub0", 1, "J", F(1), E(3))))]),
  # two rules on one head; the motive is a pattern UNDER A BINDER, so it Fords
  # (a case's convoy cannot be re-based from `j+1` to `j`); `occTm vz c ≡ false`
  # is `c = wk c₀` (strengthening), and NoNatC is renaming-invariant
  "tr": dict(alts=[
      dict(ex=[("Tm", "J"), ("Tm", "J"), ("IdC", ("Tm", "J+1"), F(0), V0)],
           ents=[tm("J", "G", E(0), U), tm("J", "G", E(1), U), tm("J", "G", F(1), k("Hom", U, E(0), E(1))),
                 tm("J", "G", F(2), El(E(0))), ("id", ("Ty", "J"), "X", El(E(1)))]),
      dict(ex=[("Ty", "J"), ("Tm", "J"), ("Tm", "J"), ("Pred", "NNC", "J", E(1)),
               ("IdC", ("Tm", "J+1"), F(0), k("cHom", ("wk", 1, "J", E(1)), ("wk", 1, "J", E(2)), V0)), ("Tm", "J"), ("Tm", "J")],
           ents=[tm("J+1", ("cext", "G", E(0)), ("wk", 1, "J", E(1)), U),
                 tm("J+1", ("cext", "G", E(0)), ("wk", 1, "J", E(2)), El(("wk", 1, "J", E(1)))),
                 tm("J+1", ("cext", "G", E(0)), V0, El(("wk", 1, "J", E(1)))),
                 tm("J", "G", E(5), E(0)), tm("J", "G", E(6), E(0)), tm("J", "G", F(1), k("Hom", E(0), E(5), E(6))),
                 tm("J", "G", F(2), El(k("cHom", E(1), E(2), E(5)))),
                 ("id", ("Ty", "J"), "X", El(k("cHom", E(1), E(2), E(6))))])]),
})

TESTRULES = {
  "trNoEq": dict(ex=[("Ty", "J"), ("Tm", "J"), ("Tm", "J"), ("Pred", "NNC", "J", E(1)), ("Tm", "J"), ("Tm", "J")],
           ents=[tm("J+1", ("cext", "G", E(0)), ("wk", 1, "J", E(1)), U),
                 tm("J", "G", E(4), E(0)), tm("J", "G", E(5), E(0)), tm("J", "G", F(1), k("Hom", E(0), E(4), E(5))),
                 ("id", ("Ty", "J"), "X", El(k("cHom", E(1), E(2), E(5))))]),
}

RULES.update({
  "var": dict(ex=[("NiC", "J", "G", F(0), "X")], ents=[]),
  "lam": dict(case="Pi", ents=[ty("J", "G", Q(0)), tm("J+1", ("cext", "G", Q(0)), F(0), Q(1))]),
  "app": dict(ex=[("Ty", "J"), ("Ty", "J+1")],
              ents=[tm("J", "G", F(0), k("Pi", E(0), E(1))), tm("J", "G", F(1), E(0)),
                    ("id", ("Ty", "J"), "X", ("sub0", 0, "J", E(1), F(1)))]),
})
RULES.update({
  # the index of `Fin (nsuc n)` is a term: an ordinary Ford, no case on the type
  "fzero": dict(ex=[("Tm", "J")], ents=[tm("J", "G", E(0), NAT), ("id", ("Ty", "J"), "X", k("Fin", NSUC(E(0))))]),
  "fsuc":  dict(ex=[("Tm", "J")], ents=[tm("J", "G", F(0), k("Fin", E(0))), ("id", ("Ty", "J"), "X", k("Fin", NSUC(E(0))))]),
})
# ★ rows written BY HAND (`Knot/Ref`: definitions, PLAN-BIDI §2-ter) — the
#   table only references them
HANDROWS = {("⟶", "ref"): ("rδ", "okδ"), ("⊢", "ref"): ("r⊢ref", "ok⊢ref")}
HAND = {}

# ------------------------------------------------------------ the family being generated
FAMS = {
  "⊢":  dict(J="JT", dJ="⊢JT", okσ="okσJ", RowOK="RowOK", S=1, X="(⊢tyOf dc)", XK="K 0 J",
             csig="Ξ ⊢ c ∷ El (CTat (pair (tag 1) j))", ix=None, dix=None),
  "⟶":  dict(J="Redₘ.J", dJ="Redₘ.⊢J", okσ="Redₘ.okσ", RowOK="Redₘ.RowOK", S=1, X="(⊢tgt {s = 1} dc)", XK="K 1 J",
             csig="Ξ ⊢ c ∷ El (Redₘ.Cat (pair (tag 1) j))", ix="ix⟶", dix="⊢ix⟶"),
  "⟶ᵀ": dict(J="RedTₘ.J", dJ="RedTₘ.⊢J", okσ="RedTₘ.okσ", RowOK="RedTₘ.RowOK", S=0, X="(⊢tgt {s = 0} dc)", XK="K 0 J",
             csig="Ξ ⊢ c ∷ El (RedTₘ.Cat (pair (tag 0) j))", ix="ix⟶ᵀ", dix="⊢ix⟶ᵀ"),
  "Pw": dict(J="Pwₘ.J", dJ="Pwₘ.⊢J", okσ="Pwₘ.okσ", RowOK="Pwₘ.RowOK", S=1, X="(⊢pwTgt dc)", XK="K 1 (nsuc J)", Xd=1,
             csig="Ξ ⊢ c ∷ El (Pwₘ.Cat (pair (tag 1) j))", ix="ixPw", dix="⊢ixPw"),
  "≅":  dict(J="Convₘ.J", dJ="Convₘ.⊢J", okσ="Convₘ.okσ", RowOK="Convₘ.RowOK", S=1, X="(⊢tgt {s = 1} dc)", XK="K 1 J",
             csig="Ξ ⊢ c ∷ El (Convₘ.Cat (pair (tag 1) j))", ix="ix≅", dix="⊢ix≅"),
  "≅ᵀ": dict(J="ConvTₘ.J", dJ="ConvTₘ.⊢J", okσ="ConvTₘ.okσ", RowOK="ConvTₘ.RowOK", S=0, X="(⊢tgt {s = 0} dc)", XK="K 0 J",
             csig="Ξ ⊢ c ∷ El (ConvTₘ.Cat (pair (tag 0) j))", ix="ix≅ᵀ", dix="⊢ix≅ᵀ"),
}
FAMS["⊢"].update(D="D⊢", dD="⊢D⊢", fib="fibK")
for _f, _m in (("⟶", "⟶F"), ("⟶ᵀ", "⟶ᵀF"), ("Pw", "PwF")):
    FAMS[_f].update(D=_m + ".DF", dD=_m + ".⊢DF", fib=_m + ".fibF", toC="⊢toCP" if _f == "Pw" else "⊢toCR")
FAMS["⊢ty"] = dict(FAMS["⊢"], S=0, csig="Ξ ⊢ c ∷ El (CTat (pair (tag 0) j))")
# ★ the `⊢ty` rules (sort 0): one per type former, the premises at their indices
TYRULES = {
  "base": dict(ents=[]), "U": dict(ents=[]), "Unit": dict(ents=[]), "Nat": dict(ents=[]), "Fin": dict(ents=[tm("J", "G", F(0), NAT)]),
  "Pi":   dict(ents=[ty("J", "G", F(0)), ty("J+1", ("cext", "G", F(0)), F(1))]),
  "Sg":   dict(ents=[ty("J", "G", F(0)), ty("J+1", ("cext", "G", F(0)), F(1))]),
  "El":   dict(ents=[tm("J", "G", F(0), U)]),
  "Hom":  dict(ents=[ty("J", "G", F(0)), tm("J", "G", F(1), F(0)), tm("J", "G", F(2), F(0))]),
  "Id":   dict(ents=[ty("J", "G", F(0)), tm("J", "G", F(1), F(0)), tm("J", "G", F(2), F(0))]),
  "IMu":  dict(ents=[tm("J", "G", F(0), U), tm("J", "G", F(1), ("DF", "J", F(0))), tm("J", "G", F(2), El(F(0)))]),
  "Desc": dict(ents=[tm("J", "G", F(0), U)]),
  # the index code is a σ-field (it is not a field of `DIh`)
  "DIh":  dict(ex=[("Tm", "J")],
               ents=[tm("J", "G", E(0), U), tm("J", "G", F(0), ("DF", "J", E(0))), ty("J+2", MC("J", "G", E(0), F(0)), F(1)),
                     tm("J", "G", F(2), k("Desc", E(0))), tm("J", "G", F(3), El(k("dpay", E(0), F(0), F(2))))]),
}
FAM = FAMS["⊢"]
FAMKEY = "⊢"
CONL = []          # the generated constructors (their own module: they cite `Knot/Judge`)
REDCONL = {"⟶": [], "⟶β": [], "⟶ᵀ": [], "Pw": []}   # …of the ⟶/⟶ᵀ/Pw families, one module each (split by consumption)

# ------------------------------------------------------------ rendering
DEPTHS = ["J", "J+1", "J+2", "J+3", "J+4"]
def dnum(d): return DEPTHS.index(d)
def plus(d, n): return DEPTHS[dnum(d) + n]
def minus1(d): return DEPTHS[dnum(d) - 1]
def nsucs(k, x):
    for _ in range(k): x = "(nsuc %s)" % x
    return x
def dep(d, J="J"): return nsucs(dnum(d), J)
def dty(d, dJ="dJ"):
    t = dJ
    for _ in range(dnum(d)): t = "(⊢isuc %s)" % t
    return t
def pname(p):
    if p in ("J", "G", "X"): return p
    if p[0] == "r": return "R%dᵢ%d" % (p[1], p[2])
    return {"f": "F", "q": "Q", "e": "E"}[p[0]] + str(p[1])
def is_param(e): return e in ("J", "G", "X") or (isinstance(e, tuple) and e[0] in ("f", "q", "e", "r"))
def var(m):
    t = "vz"
    for _ in range(m): t = "(vs %s)" % t
    return t
def wN(i, x): return x if i == 0 else "(w%d %s)" % (i, x)
def extS(i, sig="σ"):
    t = sig
    for _ in range(i): t = "(extS %s)" % t
    return t
def fieldexpr(P, i):
    t = P
    for _ in range(i): t = "(snd %s)" % t
    return "(fst %s)" % t
def shape_expr(fs): return "(" + gk.shape(fs) + ")"

# ------------------------------------------------------------ a parametric object
class PObj:
    """A telescope (`kind = 'tel'`, a list of entries) or a code (`kind = 'code'`),
    parametric in the positions it mentions; its atoms abstracted for the law."""
    def __init__(self, rc, name, kind, body):
        self.rc, self.name, self.kind, self.body = rc, name, kind, body
        self.atoms, used = [], []
        self.used = used
        if kind == "tel":
            for ent in body: self.collect(ent)
        else:
            self.collect_code(body)
        order = ["J", "G", "X"] + [("f", i) for i in range(len(rc.fields))] \
              + [("q", i) for i in range(len(rc.tfields))] \
              + [("r", m, i) for m, (_, hh) in enumerate(rc.nest) for i in range(len(SIG[hh][1]))] \
              + [("e", i) for i in range(len(rc.ex))]
        self.params = [p for p in order if p in used]
        self.order = order

    def use(self, p):
        if p not in self.used: self.used.append(p)

    def collect_code(self, c):
        t = c[0]
        if t in ("Ty", "Tm"):
            self.collect(c[1]); self.add_atom((t, (c[1],)))
        elif t == "Nat":
            pass
        elif t == "Pred":
            self.collect(c[2]); self.collect(c[3]); self.add_atom(("Pred:" + c[1], (c[2], c[3])))
        elif t == "IdC":
            self.collect_code(c[1]); self.collect(c[2]); self.collect(c[3])
        elif t in ("RedC", "PwC"):
            for y in c[1:]: self.collect(y)
            self.add_atom((t, c[1:]))
        elif t == "NiC":
            for y in c[1:]: self.collect(y)
            self.add_atom(("NiC", c[1:]))
        else:
            raise ValueError(c)

    def collect(self, x):
        if is_param(x):
            self.use(x); return
        if isinstance(x, str) and x.startswith("J"):
            self.use("J"); return
        tag = x[0]
        if tag in ("ty", "tm", "red"):
            for y in x[1:]: self.collect(y)
        elif tag == "id":
            self.collect(x[1][1]); self.collect(x[2]); self.collect(x[3]); self.add_atom((x[1][0], (x[1][1],)))
        elif tag == "k":
            for y in x[2:]: self.collect(y)
        elif tag == "cext":
            self.collect(x[1]); self.collect(x[2])
        elif tag in ("sub0", "wk"):
            for y in x[2:]: self.collect(y)
            self.add_atom((tag, x[1:]))
        elif tag in OPS or tag in ("mc", "DF"):
            for y in x[1:]: self.collect(y)
            self.add_atom((tag, x[1:]))
        elif tag == "nsuc":
            self.collect(x[1])
        elif tag in ("nzero", "v0", "v1"):
            pass
        else:
            raise ValueError(x)

    def add_atom(self, a):
        if a not in self.atoms: self.atoms.append(a)

    def expr(self, x, env, atoms=False):
        if is_param(x): return env[x]
        if isinstance(x, str): return dep(x, env["J"])
        tag = x[0]
        if tag == "k":
            args = " ".join(self.expr(y, env, atoms) for y in x[2:])
            return "(k%s%s)" % (x[1], (" " + args) if args else "")
        if tag == "cext": return "(cext %s %s)" % (self.expr(x[1], env, atoms), self.expr(x[2], env, atoms))
        if tag == "nsuc": return "(nsuc %s)" % self.expr(x[1], env, atoms)
        if tag == "nzero": return "nzero"
        if tag == "v0": return "(kvar ffz)"
        if tag == "v1": return "(kvar (ffs ffz))"
        if tag in ("sub0", "wk", "DF", "mc") or tag in OPS:
            key = (tag, x[1:])
            if atoms: return "A%d" % self.atoms.index(key)
            return self.atom_expr(key, env)
        raise ValueError(x)

    def atom_expr(self, a, env):
        kind, args = a
        r = lambda y: self.expr(y, env)
        if kind == "sub0": return "(sub0 %d %s %s %s)" % (args[0], r(args[1]), r(args[2]), r(args[3]))
        if kind == "wk":   return "(wk %d %s %s)" % (args[0], r(args[1]), r(args[2]))
        if kind == "DF":   return "(DF %s %s)" % (r(args[0]), r(args[1]))
        if kind in ("Ty", "Tm"): return "(⌜%s⌝ %s)" % (kind, r(args[0]))
        if kind.startswith("Pred:"): return "(⌜%s⌝ %s %s)" % (kind[5:], r(args[0]), r(args[1]))
        if kind == "RedC": return "(⌜⟶⌝ %s)" % " ".join(r(y) for y in args)
        if kind == "PwC": return "(⌜Pw⌝ %s)" % " ".join(r(y) for y in args)
        if kind == "NiC": return "(⌜∋⌝ %s)" % " ".join(r(y) for y in args)
        if kind in OPS or kind == "mc": return "(%s %s)" % (kind, " ".join(r(y) for y in args))
        raise ValueError(a)

    def atom_sub(self, a, env, sigma):
        kind, args = a
        r = lambda y: self.expr(y, env)
        if kind == "sub0": return "(sub0-sub %s %d %s %s %s)" % (sigma, args[0], r(args[1]), r(args[2]), r(args[3]))
        if kind == "wk":   return "(wk-sub %s %d %s %s)" % (sigma, args[0], r(args[1]), r(args[2]))
        if kind == "DF":   return "(DF-sub %s %s %s)" % (sigma, r(args[0]), r(args[1]))
        if kind in ("Ty", "Tm"): return "(⌜%s⌝-sub %s %s)" % (kind, sigma, r(args[0]))
        if kind.startswith("Pred:"): return "(⌜%s⌝-sub %s %s %s)" % (kind[5:], sigma, r(args[0]), r(args[1]))
        if kind == "RedC": return "(⌜⟶⌝-sub %s %s)" % (sigma, " ".join(r(y) for y in args))
        if kind == "PwC": return "(⌜Pw⌝-sub %s %s)" % (sigma, " ".join(r(y) for y in args))
        if kind == "NiC": return "(⌜∋⌝-sub %s %s)" % (sigma, " ".join(r(y) for y in args))
        if kind in OPS or kind == "mc": return "(%s-sub %s %s)" % (kind, sigma, " ".join(r(y) for y in args))
        raise ValueError(a)

    def code_render(self, c, env, atoms):
        t = c[0]
        if t in ("Ty", "Tm"):
            key = (t, (c[1],))
            return ("A%d" % self.atoms.index(key)) if atoms else self.atom_expr(key, env)
        if t == "Nat": return "⌜Nat⌝"
        if t == "Pred":
            key = ("Pred:" + c[1], (c[2], c[3]))
            return ("A%d" % self.atoms.index(key)) if atoms else self.atom_expr(key, env)
        if t == "IdC":
            return "(⌜Id⌝ %s %s %s)" % (self.code_render(c[1], env, atoms), self.expr(c[2], env, atoms), self.expr(c[3], env, atoms))
        if t in ("RedC", "NiC", "PwC"):
            key = (t, c[1:])
            return ("A%d" % self.atoms.index(key)) if atoms else self.atom_expr(key, env)
        raise ValueError(c)

    def render(self, env, atoms):
        if self.kind == "code": return self.code_render(self.body, env, atoms)
        out = "tι"
        for ent in reversed(self.body):
            if ent[0] == "ty":
                _, d, g, A = ent
                out = "tρ (tyIx %s %s %s) (%s)" % (self.expr(d, env, atoms), self.expr(g, env, atoms), self.expr(A, env, atoms), out)
            elif ent[0] == "tm":
                _, d, g, t, A = ent
                out = "tρ (tmIx %s %s %s %s) (%s)" % (self.expr(d, env, atoms), self.expr(g, env, atoms),
                                                      self.expr(t, env, atoms), self.expr(A, env, atoms), out)
            elif ent[0] == "red":
                _, d, t, u = ent
                out = "tρ (%s %s %s %s) (%s)" % (FAM["ix"], self.expr(d, env, atoms), self.expr(t, env, atoms), self.expr(u, env, atoms), out)
            elif ent[0] == "id":
                _, code, a, b = ent
                assert out == "tι", "a Ford field is last"
                key = (code[0], (code[1],))
                c = ("A%d" % self.atoms.index(key)) if atoms else self.atom_expr(key, env)
                out = "tσ (⌜Id⌝ %s %s %s) tι" % (c, self.expr(a, env, atoms), self.expr(b, env, atoms))
        return out

    # ---- typing
    def typ(self, x, s, d, denv):
        if is_param(x): return denv[x]
        tag = x[0]
        if tag == "v0":
            assert s == 1 and dnum(d) >= 1
            return "(⊢kvar %s (⊢ffz %s))" % (dty(d, denv["J"]), dty(minus1(d), denv["J"]))
        if tag == "v1":
            assert s == 1 and dnum(d) >= 2
            return "(⊢kvar %s (⊢ffs %s (⊢ffz %s)))" % (dty(d, denv["J"]), dty(minus1(d), denv["J"]), dty(minus1(minus1(d)), denv["J"]))
        if tag == "k":
            srt, fs, _ = SIG[x[1]]
            assert srt == s, (x, s)
            ds = []
            for f, y in zip(fs, x[2:]):
                if f[0] == "nat":
                    ds.append(self.nattyp(y, denv)); continue
                assert f[0] == "rec", (x, f)
                ds.append(self.typ(y, f[1], plus(d, f[2]), denv))
            return "(⊢k%s %s%s)" % (x[1], dty(d, denv["J"]), "".join(" " + q for q in ds))
        if tag == "sub0":
            _, s0, d0, t, u = x
            assert s0 == s and d0 == d, (x, s, d)
            return "(⊢sub0 %s %s %s %s)" % (gk.lt(s0), dty(d0, denv["J"]), self.typ(t, s0, plus(d0, 1), denv), self.typ(u, 1, d0, denv))
        if tag == "wk":
            _, s0, d0, t = x
            assert s0 == s and plus(d0, 1) == d, (x, s, d)
            return "(⊢wkS %s %s %s)" % (gk.lt(s0), dty(d0, denv["J"]), self.typ(t, s0, d0, denv))
        if tag == "DF":
            _, d0, I = x
            assert s == 0 and d0 == d
            return "(⊢DF %s %s)" % (dty(d0, denv["J"]), self.typ(I, 1, d0, denv))
        if tag in OPS:
            sg = OPS[tag]
            d0 = x[1]
            assert s == sg.get("sort", 0) and plus(d0, sg["out"]) == d, (x, s, d)
            ds = [self.typ(y, srt, plus(d0, kk), denv) for y, (srt, kk) in zip(x[2:], sg["args"])]
            return "(⊢%s %s%s)" % (tag, dty(d0, denv["J"]), "".join(" " + q for q in ds))
        raise ValueError(x)

    def nattyp(self, x, denv):
        if is_param(x): return denv[x]
        if x[0] == "nsuc": return "(⊢isuc %s)" % self.nattyp(x[1], denv)
        if x[0] == "nzero": return "(toI ⊢nzero)"
        raise ValueError(x)

    def ctxtyp(self, g, d, denv):
        if g == "G": return denv["G"]
        if g[0] == "mc":
            _, d0, g0, I, D = g
            assert plus(d0, 2) == d
            return "(⊢mc %s %s %s %s)" % (dty(d0, denv["J"]), self.ctxtyp(g0, d0, denv), self.typ(I, 1, d0, denv), self.typ(D, 1, d0, denv))
        assert g[0] == "cext"
        dm = minus1(d)
        return "(⊢cext %s %s %s)" % (dty(dm, denv["J"]), self.ctxtyp(g[1], dm, denv), self.typ(g[2], 0, dm, denv))

    def codetyp(self, c, denv):
        t = c[0]
        if t in ("Ty", "Tm"): return "(⊢⌜%s⌝ %s)" % (t, dty(c[1], denv["J"]))
        if t == "Nat": return "⊢⌜Nat⌝"
        if t == "Pred": return "(⊢⌜%s⌝ %s %s)" % (c[1], dty(c[2], denv["J"]), self.typ(c[3], 1, c[2], denv))
        if t == "IdC":
            k0, d0 = c[1]
            srt = 0 if k0 == "Ty" else 1
            to = "toTy" if srt == 0 else "toTm"
            return "(⊢⌜Id⌝ %s (%s %s) (%s %s))" % (self.codetyp(c[1], denv), to, self.typ(c[2], srt, d0, denv), to, self.typ(c[3], srt, d0, denv))
        if t == "RedC":
            _, d0, a, b = c
            return "(⊢⌜⟶⌝ %s %s %s)" % (dty(d0, denv["J"]), self.typ(a, 1, d0, denv), self.typ(b, 1, d0, denv))
        if t == "PwC":
            _, d0, a, b = c
            return "(⊢⌜Pw⌝ %s %s %s)" % (dty(d0, denv["J"]), self.typ(a, 1, d0, denv), self.typ(b, 1, plus(d0, 1), denv))
        if t == "NiC":
            _, d0, g, x, a = c
            return "(⊢⌜∋⌝ %s %s %s %s)" % (dty(d0, denv["J"]), self.ctxtyp(g, d0, denv), denv[x], self.typ(a, 0, d0, denv))
        raise ValueError(c)

    def typing(self, denv):
        if self.kind == "code": return self.codetyp(self.body, denv)
        body = "ok-ι"
        for ent in reversed(self.body):
            if ent[0] == "ty":
                _, d, g, Aa = ent
                body = "ok-ρ (⊢tyIx %s %s %s) (%s)" % (dty(d, denv["J"]), self.ctxtyp(g, d, denv), self.typ(Aa, 0, d, denv), body)
            elif ent[0] == "tm":
                _, d, g, t, Aa = ent
                body = "ok-ρ (⊢tmIx %s %s %s %s) (%s)" % (dty(d, denv["J"]), self.ctxtyp(g, d, denv), self.typ(t, 1, d, denv),
                                                           self.typ(Aa, 0, d, denv), body)
            elif ent[0] == "red":
                _, d, t, u = ent
                body = "ok-ρ (%s %s %s %s) (%s)" % (FAM["dix"], dty(d, denv["J"]), self.typ(t, FAM["S"], d, denv),
                                                    self.typ(u, FAM["S"], plus(d, FAM.get("Xd", 0)), denv), body)
            elif ent[0] == "id":
                _, code, a, b = ent
                srt = 0 if code[0] == "Ty" else 1
                to = "toTy" if srt == 0 else "toTm"
                body = "ok-σ (⊢⌜Id⌝ (⊢⌜%s⌝ %s) (%s %s) (%s %s)) ok-ι" % (code[0], dty(code[1], denv["J"]),
                    to, self.typ(a, srt, code[1], denv), to, self.typ(b, srt, code[1], denv))
        return body

def pty(rc, p):
    """a position's type, for the generic typing"""
    if p == "J": return "El ⌜Nat⌝"
    if p == "G": return "KCtx J"
    if p == "X": return FAM["XK"]
    if p[0] == "r":
        f = SIG[rc.nest[p[1]][1]][1][p[2]]
        if f[0] == "nat": return "El ⌜Nat⌝"
        if f[0] == "var": return "FinI J"
        return "K %d %s" % (f[1], dep(DEPTHS[f[2]]))
    if p[0] in ("f", "q"):
        fs = rc.fields if p[0] == "f" else rc.tfields
        f = fs[p[1]]
        if f[0] == "var": return "FinI J"
        assert f[0] == "rec", (rc.n, p, f)
        return "K %d %s" % (f[1], dep(DEPTHS[f[2]]))
    if p[0] == "e":
        c = rc.ex[p[1]]
        if c[0] == "Ty": return "K 0 %s" % dep(c[1])
        if c[0] == "Tm": return "K 1 %s" % dep(c[1])
        if c[0] == "Nat": return "El ⌜Nat⌝"
        raise ValueError("a witness is not a position: %r" % (c,))
    raise ValueError(p)

def gen_pobj(po):
    L = []
    rc = po.rc
    P = po.params
    pn = [pname(p) for p in P]
    env = {p: pname(p) for p in P}
    env.setdefault("J", "J")
    na = len(po.atoms)
    an = ["A%d" % i for i in range(na)]
    I, A = po.name + "I", po.name + "A"
    tel = po.kind == "tel"
    Ret = "Tel Δ" if tel else "RTm Δ"
    q = (lambda x: "⌜ %s ⌝ᵗ" % x) if tel else (lambda x: "(%s)" % x)
    L.append("%s : %s%s" % (A, "RTm Δ → " * (len(P) + na), Ret))
    L.append("%s = %s" % (" ".join([A] + pn + an), po.render(env, True)))
    L.append("")
    L.append("%s : %s%s" % (I, "RTm Δ → " * len(P), Ret))
    L.append("%s = %s" % (" ".join([I] + pn), " ".join([A] + pn + [po.atom_expr(a, env) for a in po.atoms])))
    L.append("")
    L.append("%s-cong : {Δ : Cx} → %s%s%s ≡ %s" % (A,
        "".join("(%s : RTm Δ) → " % x for x in pn) + "".join("(%s %s' : RTm Δ) → " % (a, a) for a in an),
        "".join("%s ≡ %s' → " % (a, a) for a in an),
        q(" ".join([A + " {Δ}"] + pn + an)), q(" ".join([A] + pn + [a + "'" for a in an]))))
    L.append("%s-cong %s%s = refl" % (A, " ".join(pn + [x for a in an for x in (a, a + "'")]), "".join(" refl" for _ in an)))
    L.append("")
    L.append("%s-sub : (σ : Sub Δ Θ)%s → subTm σ %s ≡ %s" % (I,
        "".join(" (%s : RTm Δ)" % x for x in pn), q(" ".join([I] + pn)), q(" ".join([I] + ["(subTm σ %s)" % x for x in pn]))))
    if na:
        senv = {p: "(subTm σ %s)" % pname(p) for p in P}
        senv.setdefault("J", "J")
        L.append("%s-sub σ%s = %s-cong %s %s %s" % (I, "".join(" " + x for x in pn), A,
            " ".join("(subTm σ %s)" % x for x in pn),
            " ".join("(subTm σ %s) %s" % (po.atom_expr(a, env), po.atom_expr(a, senv)) for a in po.atoms),
            " ".join(po.atom_sub(a, env, "σ") for a in po.atoms)))
    else:
        L.append("%s-sub σ%s = refl" % (I, "".join(" " + x for x in pn)))
    L.append("")
    L.append("%s-cong : {Δ : Cx} → %s%s ≡ %s" % (I,
        "".join("(%s %s' : RTm Δ) → " % (x, x) for x in pn) + "".join("%s ≡ %s' → " % (x, x) for x in pn),
        q(" ".join([I + " {Δ}"] + pn)), q(" ".join([I] + [x + "'" for x in pn]))))
    L.append("%s-cong %s%s = refl" % (I, " ".join(x for y in pn for x in (y, y + "'")), "".join(" refl" for _ in pn)))
    L.append("")
    denv = {p: "d" + pname(p) for p in P}
    denv.setdefault("J", "dJ")
    concl = (("TelOK Ξ %s (%%s)" % FAM["J"]) if tel else "Ξ ⊢ %s ∷ U") % " ".join([I] + pn)
    L.append("ok%s : {Ξ : Ctx}%s → %s%s" % (I, (" {%s : RTm ⌊ Ξ ⌋}" % " ".join(pn)) if pn else "",
        "".join("Ξ ⊢ %s ∷ %s → " % (pname(p), pty(rc, p)) for p in P), concl))
    L.append("%s = %s" % (" ".join(["ok" + I] + ["d" + x for x in pn]), po.typing(denv)))
    L.append("")
    return L

# ------------------------------------------------------------ a row: its alternatives
class RowCtx:
    def __init__(self, name, case, ex, nest=()):
        self.n = name
        self.case = case
        self.ex = ex
        self.nest = list(nest)     # [(scrutinee, head)] of the nested cases above the telescope
        self.sort, self.fields, self.idx = SIG[name]
        self.tfields = SIG[case][1] if case else []

class Alt:
    """one rule: its existentials (σ-prefix codes) and its premises"""
    def __init__(self, name, tag, case, spec):
        self.rc = RowCtx(name, case, spec.get("ex", []), spec.get("nest", ()))
        self.n = name
        self.case = case
        self.pfx = "T" + FAMKEY + name + tag
        self.codes = [PObj(self.rc, "C%s%s%s_%d" % (FAMKEY, name, tag, i), "code", c) for i, c in enumerate(self.rc.ex)]
        for i, co in enumerate(self.codes):
            for p in co.params:
                assert not (isinstance(p, tuple) and p[0] == "e" and p[1] >= i), (name, i, p)
        self.body = PObj(self.rc, self.pfx, "tel", spec["ents"])
        self.comp = spec.get("comp", False)       # a computation rule (vs a congruence)
        used = [p for po in self.codes + [self.body] for p in po.params if not (isinstance(p, tuple) and p[0] == "e")]
        self.xparams = [p for p in self.body.order if p in used]

# ------------------------------------------------------------ nested subject cases (NestIx)
def lt_of(sort): return "lt-z" if sort == 0 else "(lt-s lt-z)"
def fld_of(rc, scr):
    """the field a scrutinee names: ('f', i) a subject field, ('r', m, i) the m-th pattern's"""
    if scr[0] == "f": return rc.fields[scr[1]]
    return SIG[rc.nest[scr[1]][1]][1][scr[2]]
def nest_sort(rc, m):
    f = fld_of(rc, rc.nest[m][0])
    assert f[0] == "rec" and f[2] == 0, ("a nested case is on a field at the SAME depth", rc.n, m, f)
    return f[1]
def stack_of(rc, m):
    """the stack below level m: the subject's payload, then patterns 0 … m-1"""
    return [(FAM["S"], rc.n)] + [(nest_sort(rc, k), rc.nest[k][1]) for k in range(m)]
def stk_expr(st):
    t = "[]ˢ"
    for (s0, h) in reversed(st): t = "(%d , %s ∷ˢ %s)" % (s0, shape_name(h), t)
    return t
def stkok_expr(st):
    t = "[]ᵒ"
    for (s0, h) in reversed(st): t = "(ok∷ %s %s %s)" % (lt_of(s0), ok_name(h), t)
    return t
def elem_expr(cc, k):
    t = "(snd %s)" % cc
    for _ in range(k): t = "(snd %s)" % t
    return "(fst %s)" % t
def elem_typ(st, k, base):
    """the k-th stack element's typing, from the stack's typing"""
    d = base
    for t in range(k):
        s0, h = st[t]
        d = "(⊢psTl {s = %d} {sh = %s} {st = %s} {d = j} %s)" % (s0, shape_name(h), stk_expr(st[t + 1:]), d)
    s0, h = st[k]
    return "(⊢psHd {s = %d} {sh = %s} {st = %s} {d = j} %s)" % (s0, shape_name(h), stk_expr(st[k + 1:]), d)

def gen_alt(al):
    L = []
    for co in al.codes: L += gen_pobj(co)
    L += gen_pobj(al.body)
    rc = al.rc
    n = len(rc.ex)
    N, I = al.pfx, al.pfx + "I"
    case = al.case is not None
    L_ = len(rc.nest)
    a = "q" if (case or L_) else "p"
    payload = "(snd c)" if case else "p"
    def src(p, sub=False):
        cc = "(subTm σ c)" if sub else "c"
        if L_:
            qq = "(subTm σ q)" if sub else "q"
            if p == "J": return "(subTm σ j)" if sub else "j"
            if p == "X": return "(fst %s)" % cc
            if p[0] == "f": return fieldexpr(elem_expr(cc, 0), p[1])
            if p[0] == "r": return fieldexpr(qq, p[2]) if p[1] == L_ - 1 else fieldexpr(elem_expr(cc, p[1] + 1), p[2])
            raise ValueError(p)
        if p == "J": return "(subTm σ j)" if sub else "j"
        if p == "G": return "(fst %s)" % cc
        if p == "X": return ("(snd %s)" % cc) if FAMKEY == "⊢" else cc
        if p[0] == "f": return fieldexpr("(snd %s)" % cc if case else ("(subTm σ p)" if sub else "p"), p[1])
        if p[0] == "q": return fieldexpr("(subTm σ q)" if sub else "q", p[1])
        raise ValueError(p)
    def arg(p, lvl, sub=False):
        if isinstance(p, tuple) and p[0] == "e": return "(var %s)" % var(lvl - 1 - p[1])
        return wN(lvl, src(p, sub))
    def inst(po, lvl, sub=False):
        return "(%s)" % " ".join([po.name + "I"] + [arg(p, lvl, sub) for p in po.params]) if po.params else po.name + "I"
    def tel_from(i, sub=False):
        body = inst(al.body, n, sub)
        for m in reversed(range(i, n)):
            body = "(tσ %s %s)" % (inst(al.codes[m], m, sub), body)
        return body
    # ★ the TAILS: `N⁽ᵏ⁾ xs e₀ … eₖ₋₁`, the telescope after k σ-fields, its
    #   positions and the first k existentials EXPLICIT — each with its own
    #   law and congruence.  The row is `N⁽⁰⁾` at the sources; a
    #   constructor instantiates the tails at VALUES.
    XP = al.xparams
    xn = [pname(p) for p in XP]
    tn = lambda kk: "%s⁽%d⁾" % (N, kk)
    en = lambda kk: ["E%d" % i for i in range(kk)]
    def targ(p, xs, es):
        if isinstance(p, tuple) and p[0] == "e": return es[p[1]]
        return xs[XP.index(p)]
    def tinst(po, xs, es):
        return "(%s)" % " ".join([po.name + "I"] + [targ(p, xs, es) for p in po.params]) if po.params else po.name + "I"
    for kk in reversed(range(n + 1)):
        args = xn + en(kk)
        L.append("%s : %sTel Δ" % (tn(kk), "RTm Δ → " * len(args)))
        if kk == n:
            L.append("%s = %s" % (" ".join([tn(kk)] + args), tinst(al.body, xn, en(kk))))
        else:
            nxt = ["(w1 %s)" % x for x in args] + ["(var vz)"]
            L.append("%s = tσ %s (%s)" % (" ".join([tn(kk)] + args), tinst(al.codes[kk], xn, en(kk)), " ".join([tn(kk + 1)] + nxt)))
        L.append("")
        L.append("%s-cong : {Δ : Cx} → %s%s ≡ %s" % (tn(kk),
            "".join("(%s %s' : RTm Δ) → " % (x, x) for x in args) + "".join("%s ≡ %s' → " % (x, x) for x in args),
            "⌜ %s ⌝ᵗ" % " ".join([tn(kk) + " {Δ}"] + args), "⌜ %s ⌝ᵗ" % " ".join([tn(kk)] + [x + "'" for x in args])))
        L.append("%s-cong %s%s = refl" % (tn(kk), " ".join(y for x in args for y in (x, x + "'")), "".join(" refl" for _ in args)))
        L.append("")
        sa = ["(subTm σ %s)" % x for x in args]
        L.append("%s-sub : (σ : Sub Δ Θ)%s → subTm σ ⌜ %s ⌝ᵗ ≡ ⌜ %s ⌝ᵗ" % (tn(kk), "".join(" (%s : RTm Δ)" % x for x in args),
            " ".join([tn(kk)] + args), " ".join([tn(kk)] + sa)))
        def osub(po, xs, es):
            if not po.params: return "(%s-sub σ)" % (po.name + "I")
            return "(%s-sub σ %s)" % (po.name + "I", " ".join(targ(p, xs, es) for p in po.params))
        if kk == n:
            L.append("%s-sub σ %s = %s" % (tn(kk), " ".join(args), osub(al.body, xn, en(kk))))
        else:
            co = al.codes[kk]
            nxt = ["(w1 %s)" % x for x in args] + ["(var vz)"]
            nxt_s = ["(w1 (subTm σ %s))" % x for x in args] + ["(var vz)"]
            lhsZ = "(subTm (extS σ) ⌜ %s ⌝ᵗ)" % " ".join([tn(kk + 1)] + nxt)
            rhsZ = "⌜ %s ⌝ᵗ" % " ".join([tn(kk + 1)] + nxt_s)
            X0 = "(subTm σ %s)" % tinst(co, xn, en(kk))
            X0s = tinst(co, sa[:len(xn)], sa[len(xn):])
            inner = "(trans (%s-sub (extS σ) %s) (%s-cong %s %s))" % (tn(kk + 1), " ".join(nxt), tn(kk + 1),
                " ".join("(subTm (extS σ) %s) %s" % (u, v) for u, v in zip(nxt, nxt_s)),
                " ".join(["(w1-sub σ %s)" % x for x in args] + ["refl"]))
            L.append("%s-sub σ %s =" % (tn(kk), " ".join(args)))
            L.append("  dσ-cong1 %s %s %s %s %s %s" % (X0, X0s, lhsZ, rhsZ, osub(co, xn, en(kk)), inner))
        L.append("")
    srcs = [src(p) for p in XP]
    L.append("%s : RTm Δ → RTm Δ → RTm Δ → Tel Δ" % N)
    L.append("%s j %s c = %s" % (N, a, " ".join([tn(0)] + srcs)))
    L.append("")
    L.append("%s-law : TelLaw %s" % (N, N))
    L.append("%s-law σ j %s c = %s-sub σ %s" % (N, a, tn(0), " ".join(srcs)))
    L.append("")
    # the typing, at the row's sources
    ctx = ["Ξ"]
    for i in range(n): ctx.append("(%s ▹ El %s)" % (ctx[-1], inst(al.codes[i], i)))
    S = "(pair (tag %d) j)" % FAM["S"]
    dP = "(⊢pI %s dc)" % shape_name(al.n) if case else "dp"
    def fieldtyp(fs, base, S_, i):
        if fs[i][0] == "var":
            return "(⊢varOf {j = j} %s)" % base
        d = base
        for m in range(i):
            f = fs[m]
            if f[0] == "nat":
                d = "(⊢natSnd {i = pair (tag %d) j} {I = SI 2} {D = SD KSig} {sh = %s} %s)" % (S_, shape_expr(fs[m + 1:]), d)
            else:
                d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (f[1], f[2], shape_expr(fs[m + 1:]), d)
        if fs[i][0] == "nat":
            return "(⊢natFst {i = pair (tag %d) j} {I = SI 2} {D = SD KSig} {sh = %s} %s)" % (S_, shape_expr(fs[i + 1:]), d)
        f = fs[i]
        assert f[0] == "rec", (al.n, fs, i)
        return "(⊢atDepthSK {sg = KSig} {a = tag %d} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
            S_, f[1], f[2], f[1], f[2], shape_expr(fs[i + 1:]), d)
    def styp(p):
        if L_:
            st = stack_of(rc, L_ - 1)
            sL = nest_sort(rc, L_ - 1)
            stk = "(⊢ncStk %d %d %s dc)" % (FAM["S"], sL, stk_expr(st))
            if p == "J": return "dj"
            if p == "X": return "(⊢ncTgt %d %d %s dc)" % (FAM["S"], sL, stk_expr(st))
            if p[0] == "f": return fieldtyp(rc.fields, elem_typ(st, 0, stk), FAM["S"], p[1])
            if p[0] == "r":
                fsm = SIG[rc.nest[p[1]][1]][1]
                base = "dq" if p[1] == L_ - 1 else elem_typ(st, p[1] + 1, stk)
                return fieldtyp(fsm, base, nest_sort(rc, p[1]), p[2])
            raise ValueError(p)
        if p == "J": return "dj"
        if p == "G": return "(⊢gI %s dc)" % shape_name(al.n) if case else "(⊢ctxOf dc)"
        if p == "X": return FAM["X"]
        if p[0] == "f": return fieldtyp(rc.fields, dP, FAM["S"], p[1])
        if p[0] == "q": return fieldtyp(rc.tfields, "dq", 0, p[1])
    def kind(p):
        if p == "J": return ("nat",)
        if p == "G": return ("ctx",)
        if p == "X": return ("K", 0 if FAM["XK"].startswith("K 0") else 1, nsucs(FAM.get("Xd", 0), "j"))
        if p[0] == "r":
            f = SIG[rc.nest[p[1]][1]][1][p[2]]
            if f[0] == "nat": return ("nat",)
            return ("K", f[1], nsucs(f[2], "j"))
        fs = rc.fields if p[0] == "f" else rc.tfields
        f = fs[p[1]]
        if f[0] == "var": return ("fin",)
        return ("K", f[1], nsucs(f[2], "j"))
    def weaken(kd, term, typ, frm, to, termlvl=None):
        # goal-directed: the contexts are inferred; only the TERMS are pinned
        for i in range(frm, to):
            t_i = wN(i, term) if termlvl is None else termlvl(i)
            if kd[0] == "nat":
                typ = "(wkN {t = %s} %s)" % (t_i, typ)
            elif kd[0] == "ctx":
                typ = "(wkG {d = %s} {g = %s} %s)" % (wN(i, "j"), t_i, typ)
            else:
                dd = wN(i, kd[2]) if termlvl is None else kd[3](i)
                typ = "(wkK {s = %d} {d = %s} {t = %s} %s)" % (kd[1], dd, t_i, typ)
        return typ
    def ptyp(p, lvl):
        if isinstance(p, tuple) and p[0] == "e":
            m = p[1]; c = rc.ex[m]
            vt = lambda i: "(var %s)" % var(i - m - 1)
            if c[0] == "Nat":
                return weaken(("nat",), None, "(⊢var here)", m + 1, lvl, termlvl=vt)
            dd0 = dep(c[1], wN(m, "j"))
            here = "(here%s {m = %s})" % (c[0], dd0)
            srt = 0 if c[0] == "Ty" else 1
            dl = lambda i: wN(i - m - 1, "(renTm vs %s)" % dd0) if i > m + 1 else "(renTm vs %s)" % dd0
            return weaken(("K", srt, None, dl), None, here, m + 1, lvl, termlvl=vt)
        return weaken(kind(p), src(p), styp(p), 0, lvl)
    def okinst(po, lvl):
        return "(ok%s {_}%s%s)" % (po.name + "I", "".join(" {%s}" % arg(p, lvl) for p in po.params),
                                   "".join(" " + ptyp(p, lvl) for p in po.params))
    if L_:
        st = stack_of(rc, L_ - 1)
        sL = nest_sort(rc, L_ - 1)
        sig = "Ξ ⊢ q ∷ PayV %s (pair (tag %d) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (NCat %d %s (pair (tag %d) j))" % (
            shape_name(rc.nest[L_ - 1][1]), sL, FAM["S"], stk_expr(st), sL)
        srcs = "dj dq dc"
    elif case:
        sig = "Ξ ⊢ q ∷ PayV %s (pair (tag 0) j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CIat %s (pair (tag 0) j))" % (
            shape_name(al.case), shape_name(al.n))
        srcs = "dj dq dc"
    else:
        sig = "Ξ ⊢ p ∷ PayV %s %s (SI 2) (SD KSig) → %s" % (shape_name(al.n), S, FAM["csig"])
        srcs = "dj dp dc"
    L.append("ok%s : {Ξ : Ctx} {j %s c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → %s → TelOK Ξ %s (%s j %s c)" % (N, a, sig, FAM["J"], N, a))
    def T_at(i):
        body = inst(al.body, n)
        for m in reversed(range(i, n)):
            body = "(tσ %s %s)" % (inst(al.codes[m], m), body)
        return body
    expr = okinst(al.body, n)
    for i in reversed(range(n)):
        expr = "(%s %s %s)" % (FAM["okσ"], okinst(al.codes[i], i), expr)
    L.append("ok%s {Ξ} {j} {%s} {c} %s = %s" % (N, a, srcs, expr))
    L.append("")
    al.ctx = dict(kind=kind, weaken=weaken, src=src, tn=tn, XP=XP)
    return L

# ------------------------------------------------------------ a row's CONSTRUCTOR
def nth_expr(i, z="nth-z", s_="nth-s"):
    if z == "nth-z": return "(atᶜ %d)" % i   # an entry by its number (Lib/Sugar.atᶜ)
    t = z
    for _ in range(i): t = "(%s %s)" % (s_, t)
    return t

def gen_con(al, ci, nc, R, csf):
    """the constructor of a plain (no case, no nest) row: the payload built at
    the VALUES through the tails, read back at the sources by one `mono-by`"""
    rc, ctx = al.rc, al.ctx
    kind, weaken, src, tn, XP = ctx["kind"], ctx["weaken"], ctx["src"], ctx["tn"], ctx["XP"]
    n = len(rc.ex)
    h = al.n
    fs = rc.fields
    body = al.body.body
    S = FAM["S"]
    Jn, Dn, dJn, dDn = FAM["J"], FAM["D"], FAM["dJ"], FAM["dD"]
    ford = body[-1] if body and body[-1][0] == "id" and body[-1][2] == "X" else None
    # the values and their typings
    val, vty = {"J": "j", "G": "g", "X": "x"}, {"J": "dj", "G": "dg", "X": "dx"}
    for i in range(len(fs)): val[("f", i)], vty[("f", i)] = "f%d" % i, "df%d" % i
    for i in range(n): val[("e", i)], vty[("e", i)] = "e%d" % i, "de%d" % i
    # a NESTED subject: each scrutinised position is its pattern (innermost first)
    nest = list(rc.nest)
    Ln = len(nest)
    scrut, pat = set(), {}
    for m in range(Ln):
        for i in range(len(SIG[nest[m][1]][1])): val[("r", m, i)], vty[("r", m, i)] = "a%dᵢ%d" % (m, i), "da%dᵢ%d" % (m, i)
    for m in reversed(range(Ln)):
        scr, hm = nest[m]
        fsm = SIG[hm][1]
        pat[m] = "(k%s%s)" % (hm, "".join(" " + val[("r", m, i)] for i in range(len(fsm))))
        key = ("f", scr[1]) if scr[0] == "f" else ("r", scr[1], scr[2])
        val[key], vty[key] = pat[m], "(⊢k%s dj%s)" % (hm, "".join(" " + vty[("r", m, i)] for i in range(len(fsm))))
        scrut.add(key)
    rs = [i for i, e in enumerate(body) if e[0] in ("ty", "tm", "red")]
    Xv = "x"
    case = al.case
    qf = SIG[case][1] if case else []
    for i in range(len(qf)): val[("q", i)], vty[("q", i)] = "q%d" % i, "dq%d" % i
    qv = ["q%d" % i for i in range(len(qf))]
    if case:
        assert not ford
        Xv = "(k%s%s)" % (case, "".join(" " + x for x in qv))
        val["X"], vty["X"] = Xv, "(⊢k%s dj%s)" % (case, "".join(" dq%d" % i for i in range(len(qf))))
    if ford:
        Xv = "(%s)" % al.body.expr(ford[3], val)
        vty["X"] = al.body.typ(ford[3], 0 if FAM["XK"].startswith("K 0") else 1, ford[1][1], vty)
        val["X"] = Xv
    def ekind(i):
        c = rc.ex[i]
        if c[0] in ("Ty", "Tm"): return ("K", 0 if c[0] == "Ty" else 1, dep(c[1], "j"))
        if c[0] == "Nat": return ("nat",)
        return ("raw",)
    def ehyp(i):
        c = rc.ex[i]; kd = ekind(i)
        if kd[0] == "K": return "K %d %s" % (kd[1], kd[2])
        if kd[0] == "nat": return "El ⌜Nat⌝"
        return "El %s" % al.codes[i].render(val, False)
    def vkind(p):
        kd = kind(p)
        return kd
    # arguments / typings of an object at tail level k, object level lvl
    def arg_v(p, lvl, k):
        if isinstance(p, tuple) and p[0] == "e":
            if p[1] >= k: return "(var %s)" % var(lvl - 1 - p[1])
            return wN(lvl - k, val[p])
        return wN(lvl - k, val[p])
    def ptyp_v(p, lvl, k):
        L_ = lvl - k
        if isinstance(p, tuple) and p[0] == "e":
            m = p[1]
            if m < k:
                kd = ekind(m)
                assert kd[0] != "raw", ("a raw existential cited later", al.n, m)
                return weaken(kd, val[p], vty[p], 0, L_)
            m_ = m - k
            c = rc.ex[m]
            vt = lambda i: "(var %s)" % var(i - m_ - 1)
            if c[0] == "Nat":
                return weaken(("nat",), None, "(⊢var here)", m_ + 1, L_, termlvl=vt)
            dd0 = dep(c[1], wN(m_, "j"))
            here = "(here%s {m = %s})" % (c[0], dd0)
            srt = 0 if c[0] == "Ty" else 1
            dl = lambda i: wN(i - m_ - 1, "(renTm vs %s)" % dd0) if i > m_ + 1 else "(renTm vs %s)" % dd0
            return weaken(("K", srt, None, dl), None, here, m_ + 1, L_, termlvl=vt)
        return weaken(vkind(p), val[p], vty[p], 0, L_)
    def okinst_v(po, lvl, k):
        return "(ok%s {_}%s%s)" % (po.name + "I", "".join(" {%s}" % arg_v(p, lvl, k) for p in po.params),
                                   "".join(" " + ptyp_v(p, lvl, k) for p in po.params))
    def okt(k):
        expr = okinst_v(al.body, n, k)
        for i in reversed(range(k, n)):
            expr = "(%s %s %s)" % (FAM["okσ"], okinst_v(al.codes[i], i, k), expr)
        return expr
    xs = [val[p] for p in XP]
    es = ["e%d" % i for i in range(n)]
    # the payload, and its typing at the values
    items = es + []
    for e in body:
        if e[0] in ("ty", "tm", "red"): items.append("r%d" % len([x for x in items if x.startswith("r")]))
        elif e[0] == "id":
            items.append("(idrefl %s %s)" % (al.body.atom_expr((e[1][0], (e[1][1],)), val), al.body.expr(e[3], val)))
    P = "unit"
    for it in reversed(items): P = "(pair %s %s)" % (it, P)
    def rest_from(t):
        q = "unit"
        for it in reversed(items[t:]): q = "(pair %s %s)" % (it, q)
        return q
    pay = "⊢pay%s {Ξ} {%s} {%s} %s %s" % ("%s", Jn, Dn, dJn, dDn)
    # the body entries
    tail = "(⊢payι {Ξ} {%s} {%s} %s %s {unit} ⊢unit)" % (Jn, Dn, dJn, dDn)
    oks = ["okB"]
    for t in range(1, len(body)): oks.append("(okRest %s)" % oks[-1])
    ri = len(rs) - 1
    for t in reversed(range(len(body))):
        e = body[t]
        pos = n + t
        if e[0] == "id":
            code = e[1]; srt = 0 if code[0] == "Ty" else 1
            to = "toTy" if srt == 0 else "toTm"
            bv = al.body.expr(e[3], val)
            dE = "(⊢conv (⊢idrefl (⊢⌜%s⌝ %s) (%s %s)) (csymᵀ (credᵀ (El-⌜Id⌝ (⌜%s⌝ %s) (%s) (%s)))))" % (
                code[0], dty(code[1], "dj"), to, al.body.typ(e[3], srt, code[1], vty), code[0], dep(code[1], "j"), bv, bv)
            tail = "(%s {a = %s} {p = %s} %s %s %s)" % (pay % "σ", items[pos], rest_from(pos + 1), oks[t], dE, tail)
        else:
            tail = "(%s {r = r%d} {p = %s} %s dr%d %s)" % (pay % "ρ", ri, rest_from(pos + 1), oks[t], ri, tail)
            ri -= 1
    for k in reversed(range(n)):
        args = xs + es[:k]
        nxt = ["(w1 %s)" % x for x in args] + ["(var vz)"]
        eq = "(trans (%s-sub (single e%d) %s) (%s-cong %s %s))" % (tn(k + 1), k, " ".join(nxt), tn(k + 1),
             " ".join("(subTm (single e%d) %s) %s" % (k, u, v) for u, v in zip(nxt, args + ["e%d" % k])),
             " ".join(["(wk-cancel-tm e%d %s)" % (k, x) for x in args] + ["refl"]))
        cast = "(⊢-cast {Ξ} {%s} {El (dpay %s %s ⌜ %s ⌝ᵗ)} {El (dpay %s %s (subTm (single e%d) ⌜ %s ⌝ᵗ))} (cong (λ Z → El (dpay %s %s Z)) (sym %s)) %s)" % (
            rest_from(k + 1), Jn, Dn, " ".join([tn(k + 1)] + args + ["e%d" % k]), Jn, Dn, k, " ".join([tn(k + 1)] + nxt), Jn, Dn, eq, tail)
        c = rc.ex[k]
        de = {"Ty": "(toTy de%d)" % k, "Tm": "(toTm de%d)" % k}.get(c[0], "de%d" % k)
        tail = "(%s {a = e%d} {p = %s} %s %s %s)" % (pay % "σ", k, rest_from(k + 1), "(okT%d)" % k, de, cast)
    # the subject and convoy
    fv = [val[("f", i)] for i in range(len(fs))]
    fd = [vty[("f", i)] for i in range(len(fs))]
    if len(fs) == 1 and fs[0][0] == "var":
        p_ = "(pair %s unit)" % fv[0]; args_ = "(a-v %s)" % fd[0]
    else:
        p_ = "unit"; args_ = "a[]"
        for i in reversed(range(len(fs))):
            p_ = "(pair %s %s)" % (fv[i], p_)
            args_ = "(%s %s %s)" % ("a-nat" if fs[i][0] == "nat" else "a-rec", fd[i], args_)
    subj = "(k%s%s)" % (h, "".join(" " + x for x in fv))
    dsubj = "(⊢k%s dj%s)" % (h, "".join(" " + x for x in fd))
    ty_ = FAMKEY == "⊢ty"
    fam_ = FAMKEY not in ("⊢", "⊢ty")      # a family whose convoy IS its computed output
    if ty_:
        concl, dconcl = "tyIx j g %s" % subj, "(⊢tyIx dj dg %s)" % dsubj
        Xv, vty["X"] = "unit", "⊢unit"
    elif fam_:
        concl, dconcl = "%s j %s %s" % (FAM["ix"], subj, Xv), "(%s dj %s %s)" % (FAM["dix"], dsubj, vty["X"])
    else:
        assert FAMKEY == "⊢" and S == 1
        concl = "tmIx j g %s %s" % (subj, Xv)
        dconcl = "(⊢tmIx dj dg %s %s)" % (dsubj, vty["X"])
    # the hypotheses
    hyps = [("j", "El ⌜Nat⌝")] + ([] if fam_ else [("g", "KCtx j")])
    if not ford and not case and not ty_: hyps.append(("x", FAM["XK"].replace("J", "j") if fam_ else "K 0 j"))
    fty = lambda f: "FinI j" if f[0] == "var" else ("El ⌜Nat⌝" if f[0] == "nat" else "K %d %s" % (f[1], nsucs(f[2], "j")))
    for i, f in enumerate(fs):
        if ("f", i) not in scrut: hyps.append(("f%d" % i, fty(f)))
    for m in range(Ln):
        for i, f in enumerate(SIG[nest[m][1]][1]):
            if ("r", m, i) not in scrut: hyps.append((val[("r", m, i)], fty(f)))
    for i, f in enumerate(qf):
        hyps.append(("q%d" % i, "FinI j" if f[0] == "var" else ("El ⌜Nat⌝" if f[0] == "nat" else "K %d %s" % (f[1], nsucs(f[2], "j")))))
    for i in range(n): hyps.append(("e%d" % i, ehyp(i)))
    for t, ri in enumerate(rs):
        e = body[ri]
        if e[0] == "ty": ix = "tyIx %s %s %s" % tuple(al.body.expr(y, val) for y in e[1:])
        elif e[0] == "tm": ix = "tmIx %s %s %s %s" % tuple(al.body.expr(y, val) for y in e[1:])
        else: ix = "%s %s %s %s" % ((FAM["ix"],) + tuple(al.body.expr(y, val) for y in e[1:]))
        hyps.append(("r%d" % t, "IMu %s %s (%s)" % (Jn, Dn, ix)))
    L = []
    cn = "con" + al.pfx[1:]
    L.append("%s : {Ξ : Ctx} {%s : RTm ⌊ Ξ ⌋} → %s" % (cn, " ".join(x for x, _ in hyps), "".join("Ξ ⊢ %s ∷ %s → " % (x, t) for x, t in hyps)))
    L.append("  Ξ ⊢ conₗ %d %s ∷ IMu %s %s (%s)" % (ci, P, Jn, Dn, concl))
    L.append("%s {Ξ} {%s} %s =" % (cn, "} {".join(x for x, _ in hyps), " ".join("d" + x for x, _ in hyps)))
    comp = csf[ci][0]("j", "p", "c")
    cs = " ∷ ".join(d("j", "p", "c") for d, _, _ in csf) + " ∷ []"
    ng = "(atᵍ %d)" % S
    L.append("  ⊢conRowₖ {Ξ} {%d} {%d} {%s} {%s} {%s} {%s} {%s} {%s} %s %s %s %s" % (nc, ci, Jn, Dn, concl, comp, P, cs,
             nth_expr(ci), dJn, dDn, dconcl))
    # ⚠ `all…`'s implicits are PINNED to the where-bound `p`/`c`: inferred, they
    #   are the raw terms, so the row list `⊢conRowₖ` is given (written with the
    #   names) misses syntactically and Agda reduces every row telescope of the
    #   head to compare them — measured 3.4 s per constructor (2026-10-01).
    L.append("    (%s {s = %d} {k = %d} {j = j} {p = p} {c = c} %s %s) (all%s {j = j} {p = p} {c = c} dj dp dc)" % (FAM["fib"], S, SIG[h][2], ng, "(atʰ %d)" % (SIG[h][2]), R))
    L.append("    (⊢conv dPv (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R₀)))))")
    L.append("  where")
    L.append("    p c : RTm ⌊ Ξ ⌋")
    L.append("    p = %s" % p_)
    L.append("    c = %s" % (Xv if fam_ else "pair g %s" % Xv))
    L.append("    dp = ⊢payK %s ok-k%s dj %s" % (lt_of(S), h, args_))
    L.append("    dc = %s" % ("⊢cTy dj dg" if ty_ else ("%s %s" % (FAM["toC"], vty["X"]) if fam_ else "⊢cTm dj dg %s" % vty["X"])))
    # sources → values
    if case:
        srcs = [{"J": "j", "G": "(fst c')"}[p] if isinstance(p, str) else
                (fieldexpr("(snd c')", p[1]) if p[0] == "f" else fieldexpr("q", p[1])) for p in XP]
    elif Ln:
        import re as _re
        at = lambda t, k: _re.sub(r"(?<![\w'])q(?![\w'])", "q%d" % k, _re.sub(r"(?<![\w'])c(?![\w'])", "cv%d" % k, t))
        srcs = [at(src(p), Ln - 1) for p in XP]
    else:
        srcs = [src(p) for p in XP]
    hs = []
    if Ln:
        qn = ["q%d" % m for m in range(Ln)]
        CW = lambda k: ["c", "p"] + qn[:k]                 # the convoy's elements at level k
        AS = lambda m: [val[("r", m, i)] for i in range(len(SIG[nest[m][1]][1]))]
        def wl(xs): return "(%s)" % " ∷ ".join(xs + ["[]"])
        def red_pos(p, k):
            """position p read at level k (convoy cv_k, pattern q_k) reduces to its value"""
            if p == "J": return "done"
            if p == "X": return "(prj-tup {ws = %s} unit nth-z)" % wl(CW(k))
            if p[0] == "f":
                if k < 0: return "(prj-tup {ws = %s} unit %s)" % (wl(fv), nth_expr(p[1]))
                return "(⟶*-trans (prj-mono %d (prj-tup {ws = %s} unit %s)) (prj-tup {ws = %s} unit %s))" % (
                    p[1], wl(CW(k)), nth_expr(1), wl(fv), nth_expr(p[1]))
            m, i = p[1], p[2]
            if m == k: return "(prj-tup {ws = %s} unit %s)" % (wl(AS(m)), nth_expr(i))
            return "(⟶*-trans (prj-mono %d (prj-tup {ws = %s} unit %s)) (prj-tup {ws = %s} unit %s))" % (
                i, wl(CW(k)), nth_expr(m + 2), wl(AS(m)), nth_expr(i))
        for p in XP: hs.append(red_pos(p, Ln - 1))
    for p in ([] if Ln else XP):
        if p == "J": hs.append("done")
        elif p == "G" and case: hs.append("(prj-tup {ws = %s} unit nth-z)" % " ∷ ".join(["g"] + fv + ["[]"]))
        elif p == "G": hs.append("(prj-tup {ws = g ∷ []} %s nth-z)" % Xv)
        elif p == "X": hs.append("done" if fam_ else "(step (βsnd g %s) done)" % Xv)
        elif p[0] == "f" and case: hs.append("(prj-tup {ws = %s} unit %s)" % (" ∷ ".join(["g"] + fv + ["[]"]), nth_expr(p[1] + 1)))
        elif p[0] == "f": hs.append("(prj-tup {ws = %s} unit %s)" % (" ∷ ".join(fv + ["[]"]), nth_expr(p[1])))
        elif p[0] == "q": hs.append("(prj-tup {ws = %s} unit %s)" % (" ∷ ".join(qv + ["[]"]), nth_expr(p[1])))
        else: raise ValueError(p)
    m = len(XP)
    vars_ = ["(var %s)" % var(i) for i in range(m)]
    if case:
        PN = "P" + al.pfx
        tgt = "⌜ %s ⌝ᵗ" % " ".join([tn(0)] + xs)
        u1 = "%s.CASE j %s (pair (fst c) p)" % (PN, Xv)
        u2 = "%s.CASE j %s c'" % (PN, Xv)
        u3 = "⌜ %s j q c' ⌝ᵗ" % al.pfx
        L.append("    q c' : RTm ⌊ Ξ ⌋")
        L.append("    q = %s" % ("".join("(pair %s " % x for x in qv) + "unit" + ")" * len(qv)))
        L.append("    c' = pair g p")
        R1 = "R₁"
    else:
        R1 = "R₁" if Ln else "R₀"
    L.append("    %s : ⌜ %s ⌝ᵗ ⟶* ⌜ %s ⌝ᵗ" % (R1, " ".join([tn(0)] + srcs), " ".join([tn(0)] + xs)))
    L.append(("    %s = mono-by" % R1) + " {Δ = ⌊ Ξ ⌋} {n = %d} {as = %s} {as' = %s} ⌜ %s ⌝ᵗ (%s-sub (σₗ (%s)) %s) (%s-sub (σₗ (%s)) %s) (%s)" % (
        m, "(%s)" % " ∷ ".join(srcs + ["[]"]), "(%s)" % " ∷ ".join(xs + ["[]"]), " ".join([tn(0)] + vars_),
        tn(0), " ∷ ".join(srcs + ["[]"]), " ".join(vars_), tn(0), " ∷ ".join(xs + ["[]"]), " ".join(vars_),
        " ∷ʳ ".join(hs + ["[]ʳ"])))
    if Ln:
        nc = al.nctx
        ngf = lambda m: "(atᵍ %d)" % nest_sort(rc, m)
        nhf = lambda m: "(atʰ %d)" % (SIG[nest[m][1]][2])
        skey = lambda m: ("f", nest[m][0][1]) if nest[m][0][0] == "f" else ("r", nest[m][0][1], nest[m][0][2])
        tgt = "⌜ %s ⌝ᵗ" % " ".join([tn(0)] + xs)
        steps = []
        P0 = nc["Pn"](0)
        cur = csf[ci][0]("j", "p", "c")
        u = "%s.CASE j %s (pair c (pair p unit))" % (P0, pat[0])
        steps.append((cur, u, "(%s.CASE-⟶ᵃ %s)" % (P0, red_pos(skey(0), -1))))
        for k in range(1, Ln + 1):
            if k < Ln:
                Pk = nc["Pn"](k)
                land = "%s.CASE j %s %s" % (Pk, at(nc["scrut_at"](k, nest[k][0]), k - 1), at(nc["convoy_at"](k), k - 1))
            else:
                land = "⌜ %s j q%d cv%d ⌝ᵗ" % (al.pfx, Ln - 1, Ln - 1)
            steps.append((u, land, "(%s.case-β {j = j} {q = q%d} {c = cv%d} %s %s)" % (nc["Pn"](k - 1), k - 1, k - 1, ngf(k - 1), nhf(k - 1))))
            if k < Ln:
                u1 = "%s.CASE j %s %s" % (Pk, pat[k], at(nc["convoy_at"](k), k - 1))
                steps.append((land, u1, "(%s.CASE-⟶ᵃ %s)" % (Pk, red_pos(skey(k), k - 1))))
                u2 = "%s.CASE j %s cv%d" % (Pk, pat[k], k)
                pw = ["(prj-tup {ws = %s} unit %s)" % (wl(CW(k - 1)), nth_expr(t)) for t in range(len(CW(k - 1)))] + ["done"]
                steps.append((u1, u2, "(%s.CASE-⟶ᶜ (tup-mono {w = unit} (%s)))" % (Pk, " ∷ʳ ".join(pw + ["[]ʳ"]))))
                u = u2
            else:
                steps.append((land, tgt, "R₁"))
        pr = steps[-1][2]
        for (t_, u_, p_r) in reversed(steps[:-1]):
            pr = "(⟶*-trans {t = %s} {u = %s} {v = %s} %s %s)" % (t_, u_, tgt, p_r, pr)
        pre = ["    q%d = %s" % (m, "".join("(pair %s " % x for x in AS(m)) + "unit" + ")" * len(AS(m))) for m in range(Ln)]
        pre += ["    cv%d = %s" % (k, "".join("(pair %s " % x for x in CW(k)) + "unit" + ")" * len(CW(k))) for k in range(Ln)]
        i1 = max(i for i, l in enumerate(L) if l.startswith("    R₁ : "))
        L[i1:i1] = ["    %s : RTm ⌊ Ξ ⌋" % " ".join(["q%d" % m for m in range(Ln)] + ["cv%d" % k for k in range(Ln)])] + pre
        L.append("    R₀ : %s ⟶* %s" % (cur, tgt))
        L.append("    R₀ = %s" % pr)
    if case:
        L.append("    R₀ : %s.CX j p c ⟶* %s" % (PN, tgt))
        L.append("    R₀ = ⟶*-trans {t = %s.CX j p c} {u = %s} {v = %s} (%s.CASE-⟶ᵃ (step (βsnd g %s) done))" % (PN, u1, tgt, PN, Xv))
        L.append("           (⟶*-trans {t = %s} {u = %s} {v = %s} (%s.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g %s) done)))" % (u1, u2, tgt, PN, Xv))
        L.append("           (⟶*-trans {t = %s} {u = %s} {v = %s} (%s.case-β {j = j} {q = q} {c = c'} (atᵍ 0) %s) R₁))" % (
            u2, u3, tgt, PN, "(atʰ %d)" % (SIG[case][2])))

    L.append("    okRest : {J' : RTm ⌊ Ξ ⌋} {T : Tel ⌊ Ξ ⌋} → TelOK Ξ %s (tρ J' T) → TelOK Ξ %s T" % (Jn, Jn))
    L.append("    okRest (ok-ρ _ o) = o")
    for k in range(n):
        L.append("    okT%d : TelOK Ξ %s (%s)" % (k, Jn, " ".join([tn(k)] + xs + es[:k])))
        L.append("    okT%d = %s" % (k, okt(k)))
    L.append("    okB : TelOK Ξ %s (%s)" % (Jn, " ".join([tn(n)] + xs + es)))
    L.append("    okB = %s" % okt(n))
    L.append("    dPv : Ξ ⊢ %s ∷ El (dpay %s %s ⌜ %s ⌝ᵗ)" % (P, Jn, Dn, " ".join([tn(0)] + xs)))
    L.append("    dPv = %s" % tail)
    L.append("")
    # ★ F6: the decoder reads this rule back along the same state
    if True:
        xi = None
        if FAMKEY in ("⟶", "⟶ᵀ") and not al.comp:
            for e_ in body:
                if e_[0] == "red": xi = e_[2][1]
            if xi is None and len(rc.ex) > 1 and rc.ex[1][0] == "RedC": xi = rc.ex[1][2][1]
        DECREC.setdefault((FAMKEY, h), {})[ci] = dict(al=al, rc=rc, nc=nc, csf=csf, n=n, body=body, val=dict(val),
            XP=list(XP), srcs=list(srcs), hs=list(hs), tn=tn, p_=p_, Ln=Ln, case=case, xi=xi,
            hyps=[x for x, _ in hyps], ford=ford, nest=list(rc.nest), fs=list(fs))
    return L

def fieldtyp_g(fs, base, S_, i):
    """a payload field's typing through the payload's view (`base` types the payload at `(S_ , j)`)"""
    if fs[i][0] == "var":
        return "(⊢varOf {j = j} %s)" % base
    d = base
    for m in range(i):
        f = fs[m]
        if f[0] == "nat":
            d = "(⊢natSnd {i = pair (tag %d) j} {I = SI 2} {D = SD KSig} {sh = %s} %s)" % (S_, shape_expr(fs[m + 1:]), d)
        else:
            d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (f[1], f[2], shape_expr(fs[m + 1:]), d)
    f = fs[i]
    if f[0] == "nat":
        return "(⊢natFst {i = pair (tag %d) j} {I = SI 2} {D = SD KSig} {sh = %s} %s)" % (S_, shape_expr(fs[i + 1:]), d)
    return "(⊢atDepthSK {sg = KSig} {a = tag %d} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
        S_, f[1], f[2], f[1], f[2], shape_expr(fs[i + 1:]), d)

def gen_nest(al):
    """a rule whose SUBJECT has a nested pattern: one case per level; returns (lines, outer component)"""
    rc = al.rc
    L = len(rc.nest)
    S = FAM["S"]
    Jn, dJn = FAM["J"], FAM["dJ"]
    Jsub = Jn.replace(".J", ".J-sub")
    N = al.pfx
    out = gen_alt(al)
    Pn = lambda m: "P%sᶜ%d" % (N, m)          # the case on scrutinee m (its row is level m+1)
    Rn = lambda k: "r%sL%d" % (N, k)           # the row at level k (k ≥ 1)
    OKn = lambda k: "okr%sL%d" % (N, k)
    def scrut_at(k, scr):
        """scrutinee `scr` as a term at level k (k = 0: the outer row's `p`)"""
        if k == 0:
            assert scr[0] == "f"
            return fieldexpr("p", scr[1])
        if scr[0] == "f": return fieldexpr(elem_expr("c", 0), scr[1])
        return fieldexpr("q", scr[2]) if scr[1] == k - 1 else fieldexpr(elem_expr("c", scr[1] + 1), scr[2])
    def scrut_typ(k, scr):
        if k == 0:
            return fieldtyp_g(rc.fields, "dp", S, scr[1])
        st = stack_of(rc, k - 1)
        stk = "(⊢ncStk %d %d %s dc)" % (S, nest_sort(rc, k - 1), stk_expr(st))
        if scr[0] == "f": return fieldtyp_g(rc.fields, elem_typ(st, 0, stk), S, scr[1])
        fsm = SIG[rc.nest[scr[1]][1]][1]
        base = "dq" if scr[1] == k - 1 else elem_typ(st, scr[1] + 1, stk)
        return fieldtyp_g(fsm, base, nest_sort(rc, scr[1]), scr[2])
    def convoy_at(k):
        """the convoy handed to the case at level k"""
        if k == 0: return "(pair c (pair p unit))"
        st = stack_of(rc, k - 1)
        els = [elem_expr("c", t) for t in range(len(st))] + ["q"]
        v = "unit"
        for e in reversed(els): v = "(pair %s %s)" % (e, v)
        return "(pair (fst c) %s)" % v
    def convoy_typ(k):
        sk = nest_sort(rc, k)
        stk_k = stack_of(rc, k)
        if k == 0:
            v = "(⊢psCons {s = %d} {sh = %s} []ᵒ dj dp (⊢psNil {d = j}))" % (S, shape_name(rc.n))
            X = FAM["X"]
        else:
            st = stack_of(rc, k - 1)
            sp = nest_sort(rc, k - 1)
            stk = "(⊢ncStk %d %d %s dc)" % (S, sp, stk_expr(st))
            els = [elem_typ(st, t, stk) for t in range(len(st))] + ["dq"]
            v = "(⊢psNil {d = j})"
            for t in reversed(range(len(els))):
                v = "(⊢psCons {s = %d} {sh = %s} %s dj %s %s)" % (stk_k[t][0], shape_name(stk_k[t][1]), stkok_expr(stk_k[t + 1:]), els[t], v)
            X = "(⊢ncTgt %d %d %s dc)" % (S, sp, stk_expr(st))
        return "(⊢ncMkC %d %d %s %s %s dj %s %s)" % (S, sk, stk_expr(stk_k), lt_of(sk), stkok_expr(stk_k), X, v)
    # the innermost row: the telescope
    out.append("%s : Row" % Rn(L))
    out.append("%s = defRow₀ %s %s-law" % (Rn(L), N, N))
    for m in reversed(range(L)):
        sm, hm = nest_sort(rc, m), rc.nest[m][1]
        st = stack_of(rc, m)
        k = m + 1
        if k < L:
            # an intermediate row: the next case
            scr = rc.nest[k][0]
            desc = "%s.CASE j %s %s" % (Pn(k), scrut_at(k, scr), convoy_at(k))
            out.append("%s : Row" % Rn(k))
            out.append("%s = record { R = λ j q c → %s ; R-sub = λ σ j q c → %s.CASE-sub σ j %s %s }" % (
                Rn(k), desc, Pn(k), scrut_at(k, scr), convoy_at(k)))
        out.append("module %s = Pat KOK %s %s %s (NC %d %s) (NC-sub %d %s) (⊢NC %s %s) %d %d %s" % (
            Pn(m), Jn, Jsub, dJn, S, stk_expr(st), S, stk_expr(st), lt_of(S), stkok_expr(st), sm, SIG[hm][2], Rn(k)))
        out.append("%s : %s.RowOK %d %s %s" % (OKn(k), Pn(m), sm, shape_name(hm), Rn(k)))
        if k == L:
            out.append("%s {Ξ} {j} {q} {c} dj dq dc = ⊢tel {Ξ} {%s} {%s j q c} %s (ok%s dj dq dc)" % (OKn(k), Jn, N, dJn, N))
        else:
            scr = rc.nest[k][0]
            out.append("%s {Ξ} {j} {q} {c} dj dq dc = %s.⊢CASE {Ξ} {j} {%s} {%s} %s %s dj %s %s" % (
                OKn(k), Pn(k), scrut_at(k, scr), convoy_at(k), OKn(k + 1), lt_of(nest_sort(rc, k)), scrut_typ(k, scr), convoy_typ(k)))
        out.append("")
    al.nctx = dict(Pn=Pn, scrut_at=scrut_at, convoy_at=convoy_at)
    scr0 = rc.nest[0][0]
    comp = ((lambda P, i0: lambda j, p, c: "(%s.CASE %s %s (pair %s (pair %s unit)))" % (P, j, fieldexpr(p, i0), c, p))(Pn(0), scr0[1]),
            "(%s.CASE-sub σ j %s %s)" % (Pn(0), scrut_at(0, scr0), convoy_at(0)),
            "%s.⊢CASE {Ξ} {j} {%s} {%s} %s %s dj %s %s" % (Pn(0), scrut_at(0, scr0), convoy_at(0), OKn(1), lt_of(nest_sort(rc, 0)),
                                                        scrut_typ(0, scr0), convoy_typ(0)))
    return out, comp

def conv_comp(name):
    ki = SIG[name][2]
    nh = "(atʰ %d)" % ki
    return (lambda j, p, c: "⌜ TCVat %d %s %s %s ⌝ᵗ" % (ki, j, p, c), "(TCVat-law %d σ j p c)" % ki,
            "⊢tel {Ξ} {JT} {TCVat %d j p c} ⊢JT (okTCVat (atᵍ 1) %s dj dp dc)" % (ki, nh))

def gen_head(name, spec):
    L = ["-- %s%s" % (FAMKEY, name)]
    sh = shape_name(name)
    R, OK = "r" + FAMKEY + name, "ok" + FAMKEY + name
    comps = []
    plain = []
    case = spec.get("case")
    alts = spec.get("alts", [spec])
    tags = [""] if len(alts) == 1 else ["".join("₀₁₂₃₄₅₆₇₈₉"[int(ch)] for ch in str(i + 1)) for i in range(len(alts))]
    As = [Alt(name, t, case, a) for t, a in zip(tags, alts)]
    for al in As:
        if not al.rc.nest: L += gen_alt(al)
    if case:
        assert len(As) == 1 and FAMKEY == "⊢"
        N = As[0].pfx
        h = SIG[case][2]
        L.append("r%sI : Row" % N)
        L.append("r%sI = defRow₀ %s %s-law" % (N, N, N))
        L.append("module P%s = CaseRow %s %s %d r%sI" % (N, sh, ok_name(name), h, N))
        L.append("okC%sI : P%s.RowOK 0 %s r%sI" % (N[1:], N, shape_name(case), N))
        L.append("okC%sI {Ξ} {j} {q} {c} dj dq dc = ⊢tel {Ξ} {JT} {%s j q c} ⊢JT (ok%s dj dq dc)" % (N[1:], N, N))
        plain.append((len(comps), As[0]))
        comps.append(((lambda N: lambda j, p, c: "(P%s.CX %s %s %s)" % (N, j, p, c))(N), "(P%s.CASE-sub σ j (snd c) (pair (fst c) p))" % N,
                      "P%s.⊢CX okC%sI {Ξ} {j} {p} {c} dj dp dc" % (N, N[1:])))
    else:
        for al in As:
            N = al.pfx
            if al.rc.nest:
                ls, comp = gen_nest(al)
                L += ls
                plain.append((len(comps), al))
                comps.append(comp)
                continue
            plain.append((len(comps), al))
            comps.append(((lambda N: lambda j, p, c: "⌜ %s %s %s %s ⌝ᵗ" % (N, j, p, c))(N), "(%s-law σ j p c)" % N,
                          "⊢tel {Ξ} {%s} {%s j p c} %s (ok%s dj dp dc)" % (FAM["J"], N, FAM["dJ"], N)))
    if FAMKEY == "⊢" and SIG[name][0] == 1:
        comps.append(conv_comp(name))
    cs = " ∷ ".join(d("j", "p", "c") for d, _, _ in comps) + " ∷ []"
    # both sides of every component PINNED (metas here meet two context forms)
    pins = " ".join("(subTm σ (%s)) (%s) %s" % (d("j", "p", "c"), d("(subTm σ j)", "(subTm σ p)", "(subTm σ c)"), l) for d, l, _ in comps)
    L.append("%s : Row" % R)
    if len(comps) == 1:
        d0 = comps[0][0]
        L.append("%s = record { R = λ j p c → rows (%s) ; R-sub = λ σ j p c → trans (rows-sub' σ (%s)) (cong (λ X → rows (X ∷ [])) {x = subTm σ (%s)} {y = %s} %s) }"
                 % (R, cs, cs, d0("j", "p", "c"), d0("(subTm σ j)", "(subTm σ p)", "(subTm σ c)"), comps[0][1]))
    else:
        L.append("%s = record { R = λ j p c → rows (%s)" % (R, cs))
        L.append("  ; R-sub = λ σ j p c → trans (rows-sub' σ (%s)) (cong (λ X → rows X) (∷-cong%d %s)) }"
                 % (cs, len(comps), pins))
    L.append("all%s : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ p ∷ PayV %s (pair (tag %d) j) (SI 2) (SD KSig) → %s → AllD Ξ %s (%s)" % (
        R, sh, FAM["S"], FAM["csig"], FAM["J"], cs))
    L.append("all%s {Ξ} {j} {p} {c} dj dp dc = %s[]ᵈ" % (R, "".join("(%s) ∷ᵈ " % o for _, _, o in comps)))
    L.append("%s : %s %d %s %s" % (OK, FAM["RowOK"], FAM["S"], sh, R))
    L.append("%s {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {%s} {%d} {%s} %s (all%s dj dp dc)" % (
        OK, FAM["J"], len(comps), cs, FAM["dJ"], R))
    L.append("")
    for ci, al in plain:
        key = FAMKEY + ("β" if FAMKEY == "⟶" and al.comp else "")
        (CONL if FAMKEY in ("⊢", "⊢ty") else REDCONL[key]).extend(gen_con(al, ci, len(comps), R, comps))
    if FAMKEY == "⊢" and SIG[name][0] == 1:
        CONL.extend(gen_conv_con(name, len(comps), R, comps))
    return L

def subject_parts(h):
    """a head's subject at field values: payload, its Args typing, the term, its typing"""
    fs = SIG[h][1]
    fv = ["f%d" % i for i in range(len(fs))]
    if len(fs) == 1 and fs[0][0] == "var":
        p_, args_ = "(pair f0 unit)", "(a-v df0)"
    else:
        p_, args_ = "unit", "a[]"
        for i in reversed(range(len(fs))):
            p_ = "(pair f%d %s)" % (i, p_)
            args_ = "(%s df%d %s)" % ("a-nat" if fs[i][0] == "nat" else "a-rec", i, args_)
    hyps = [("f%d" % i, "FinI j" if f[0] == "var" else ("El ⌜Nat⌝" if f[0] == "nat" else "K %d %s" % (f[1], nsucs(f[2], "j"))))
            for i, f in enumerate(fs)]
    return p_, args_, "(k%s%s)" % (h, "".join(" " + x for x in fv)), "(⊢k%s dj%s)" % (h, "".join(" df%d" % i for i in range(len(fs)))), hyps

def gen_conv_con(h, nc, R, csf):
    """⊢conv's constructor at head h: the last component; its payload typed once (`JudgeConv.⊢payTCVat`)"""
    p_, args_, subj, dsubj, fh = subject_parts(h)
    hyps = [("j", "El ⌜Nat⌝"), ("g", "KCtx j")] + fh + [("A", "K 0 j"), ("B", "K 0 j"),
            ("r", "IMu JT D⊢ (tmIx j g %s A)" % subj), ("e", "El (⌜≅ᵀ⌝ j A B)")]
    P = "(pair A (pair r (pair e unit)))"
    cs = " ∷ ".join(d("j", "p", "c") for d, _, _ in csf) + " ∷ []"
    cn = "conv⊢" + h
    L = []
    L.append("%s : {Ξ : Ctx} {%s : RTm ⌊ Ξ ⌋} → %s" % (cn, " ".join(x for x, _ in hyps), "".join("Ξ ⊢ %s ∷ %s → " % (x, t) for x, t in hyps)))
    L.append("  Ξ ⊢ conₗ %d %s ∷ IMu JT D⊢ (tmIx j g %s B)" % (nc - 1, P, subj))
    L.append("%s {Ξ} {%s} %s =" % (cn, "} {".join(x for x, _ in hyps), " ".join("d" + x for x, _ in hyps)))
    L.append("  ⊢conRowₖ {Ξ} {%d} {%d} {JT} {D⊢} {tmIx j g %s B} {%s} {%s} {%s} %s ⊢JT ⊢D⊢ (⊢tmIx dj dg %s dB)" % (
        nc, nc - 1, subj, csf[nc - 1][0]("j", "p", "c"), P, cs, nth_expr(nc - 1), dsubj))
    L.append("    (fibK {s = 1} {k = %d} {j = j} {p = p} {c = c} (atᵍ 1) %s) (all%s {j = j} {p = p} {c = c} dj dp dc)" % (
        SIG[h][2], "(atʰ %d)" % (SIG[h][2]), R))
    L.append("    (⊢payTCVat ⊢D⊢ {k = %d} dj dg %s dA dB dr de)" % (SIG[h][2], dsubj))
    L.append("  where")
    L.append("    p c : RTm ⌊ Ξ ⌋")
    L.append("    p = %s" % p_)
    L.append("    c = pair g B")
    L.append("    dp = ⊢payK (lt-s lt-z) ok-k%s dj %s" % (h, args_))
    L.append("    dc = ⊢cTm dj dg dB")
    L.append("")
    return L

def gen_helpers(maxn):
    """the weakenings past 3 binders, and the σ-prefix congruences (explicit arguments)"""
    L = []
    for kk in range(4, maxn + 1):
        L.append("w%d : RTm Δ → RTm _" % kk)
        L.append("w%d x = renTm vs (w%d x)" % (kk, kk - 1))
        L.append("w%d-sub : (σ : Sub Δ Θ) (x : RTm Δ) → subTm %s (w%d x) ≡ w%d (subTm σ x)" % (kk, extS(kk), kk, kk))
        L.append("w%d-sub σ x = trans (wkS %s (w%d x)) (cong w1 (w%d-sub σ x))" % (kk, extS(kk - 1), kk - 1, kk - 1))
        L.append("")
    for kk in range(2, 17):
        xs = ["X%d" % i for i in range(kk)]
        L.append("∷-cong%d : {Δ : Cx} → %s(%s ∷ []) ≡ (%s ∷ [])" % (kk,
            "".join("(%s %s' : RTm Δ) → %s ≡ %s' → " % (x, x, x, x) for x in xs),
            " ∷ ".join(xs), " ∷ ".join(x + "'" for x in xs)))
        L.append("∷-cong%d %s = refl" % (kk, " ".join("%s %s' refl" % (x, x) for x in xs)))
        L.append("")
    for kk in range(1, maxn + 1):
        ctxs = ["Δ"]
        for _ in range(kk): ctxs.append("(%s ∙)" % ctxs[-1])
        names = ["X%d" % i for i in range(kk)]
        args = "".join("(%s %s' : RTm %s) " % (x, x, ctxs[i]) for i, x in enumerate(names)) + "(Z Z' : RTm %s)" % ctxs[kk]
        def nest(prime):
            t = "Z" + prime
            for x in reversed(names): t = "dσ %s%s (lam (%s))" % (x, prime, t)
            return t
        L.append("dσ-cong%d : %s → %s%s ≡ %s" % (kk, args, "".join("%s ≡ %s' → " % (x, x) for x in names + ["Z"]), nest(""), nest("'")))
        L.append("dσ-cong%d %s Z Z' %s = refl" % (kk, " ".join("%s %s'" % (x, x) for x in names), " ".join("refl" for _ in names + ["Z"])))
        L.append("")
    return L

def gen_table():
    L = ["------------------------------------------------------------------------",
         "-- ★ THE JUDGEMENT'S TABLE: each Knot constructor's row and its typing, in",
         "--   KSig's order — `⊢ty` by type head (sort 0), `⊢` by term head (sort 1;",
         "--   `rNone` = not yet a row)",
         "------------------------------------------------------------------------", "",
         "rows⊢ty : RowsOK 0 TyShs", "rows⊢ty ="]
    for h in TYHEADS:
        L.append("  ⟨ r⊢ty%s ∣ ok⊢ty%s ⟩∷  -- %s" % (h, h, shape_name(h)))
    L += ["  []ᴿ", "", "rows⊢ : RowsOK 1 TmShs", "rows⊢ ="]
    for h in TMHEADS:
        if ("⊢", h) in HANDROWS:     L.append("  ⟨ %s ∣ %s ⟩∷  -- %s" % (HANDROWS[("⊢", h)] + (shape_name(h),)))
        elif h in RULES: L.append("  ⟨ r⊢%s ∣ ok⊢%s ⟩∷  -- %s" % (h, h, shape_name(h)))
        else:                        L.append("  ⟨ rNone ∣∀ okNone ⟩∷  -- %s" % shape_name(h))
    L.append("  []ᴿ")
    return L

# ------------------------------------------------------------ the side-condition families
# A predicate on codes (sort 1), fibred by the code's head; a row is a list of
# recursive premises `(field, depth-offset)` into the same predicate.
PREDS = {
  "NNC":  dict(doc="NoNatC c — no ⌜Nat⌝ along the Π-codomain / Hom-ambient spine (Spec/Variance)",
               rows={"cbase": [], "cUnit": [], "cFin": [], "cSg": [], "cId": [],
                     "cPi": [(1, 1)], "cHom": [(0, 0)]}),
  "StkA": dict(doc="stkA? c ≡ true — a stable ambient (Spec/Variance)",
               rows={"cbase": [], "cSg": [], "cId": [], "cUnit": [], "cFin": [], "cNat": [], "cIMu": [],
                     "cHom": [(0, 0)]}),
  "StkC": dict(doc="stkC? c ≡ true — J-able: stkA? minus the literal ⌜Nat⌝; at ⌜Hom⌝ it is stkA? of the ambient",
               rows={"cbase": [], "cSg": [], "cId": [], "cUnit": [], "cFin": [], "cIMu": [],
                     "cHom": [("σ", "StkA", 0)]}),
  "Flat": dict(doc="flat? c ≡ true — ⌜base⌝, or ⌜Hom⌝ at a J-able ambient (Spec/Variance)",
               rows={"cbase": [], "cHom": [("σ", "StkC", 0)]}),
}

PCONL = []   # the side-condition families' constructors (their own module: they cite each `Family`)

def gen_pred_con(P, h, prems):
    """a side-condition row's constructor: the payload (its premises) at the
    values, the row read at the sources by one `mono-by`"""
    fs = SIG[h][1]
    nm = "%s⊢%s" % (P, h)
    n = len(fs)
    fv = ["f%d" % i for i in range(n)]
    def dep(k, j="j"):
        t = j
        for _ in range(k): t = "(nsuc %s)" % t
        return t
    def ddep(k):
        t = "dj"
        for _ in range(k): t = "(⊢isuc %s)" % t
        return t
    # the telescope at values, and its law
    def telv(xs):
        tel = "tι"
        for pr in reversed(prems):
            if pr[0] == "σ": tel = "tσ (⌜%s⌝ %s %s) tι" % (pr[1], xs[0], xs[1 + pr[2]])
            else: tel = "tρ (ix%s %s %s) (%s)" % (P, dep(pr[1], xs[0]), xs[1 + pr[0]], tel)
        return tel
    TV = "TV" + nm
    args = ["J"] + ["F%d" % i for i in range(n)]
    L = []
    L.append("%s : %sTel Δ" % (TV, "RTm Δ → " * len(args)))
    L.append("%s %s = %s" % (TV, " ".join(args), telv(args)))
    L.append("")
    L.append("%s-sub : (σ : Sub Δ Θ)%s → subTm σ ⌜ %s ⌝ᵗ ≡ ⌜ %s ⌝ᵗ" % (TV, "".join(" (%s : RTm Δ)" % a for a in args),
             " ".join([TV] + args), " ".join([TV] + ["(subTm σ %s)" % a for a in args])))
    sp = [pr for pr in prems if pr[0] == "σ"]
    if sp:
        L.append("%s-sub σ %s = cong (λ Z → dσ Z (lam dι)) (⌜%s⌝-sub σ J F%d)" % (TV, " ".join(args), sp[0][1], sp[0][2]))
    else:
        L.append("%s-sub σ %s = refl" % (TV, " ".join(args)))
    L.append("")
    # the constructor
    hyps = [("j", "El ⌜Nat⌝")] + [(fv[i], "El ⌜Nat⌝" if fs[i][0] == "nat" else "K %d %s" % (fs[i][1], dep(fs[i][2]))) for i in range(n)]
    items = []
    for t, pr in enumerate(prems):
        if pr[0] == "σ":
            hyps.append(("e%d" % t, "El (⌜%s⌝ j %s)" % (pr[1], fv[pr[2]]))); items.append("e%d" % t)
        else:
            hyps.append(("r%d" % t, "K%s %s %s" % (P, dep(pr[1]), fv[pr[0]]))); items.append("r%d" % t)
    Pay = "unit"
    for it in reversed(items): Pay = "(pair %s %s)" % (it, Pay)
    subj = "(k%s%s)" % (h, "".join(" " + x for x in fv))
    dsubj = "(⊢k%s dj%s)" % (h, "".join(" d" + x for x in fv))
    p_ = "unit"; args_ = "a[]"
    for i in reversed(range(n)):
        p_ = "(pair %s %s)" % (fv[i], p_); args_ = "(%s d%s %s)" % ("a-nat" if fs[i][0] == "nat" else "a-rec", fv[i], args_)
    # the payload's typing at the values
    def rest(t):
        q = "unit"
        for it in reversed(items[t:]): q = "(pair %s %s)" % (it, q)
        return q
    def okv(t):
        o = "ok-ι"
        for pr in reversed(prems[t:]):
            if pr[0] == "σ": o = "ok-σ (⊢⌜%s⌝ dj d%s) ok-ι" % (pr[1], fv[pr[2]])
            else: o = "ok-ρ (⊢ix%s %s d%s) (%s)" % (P, ddep(pr[1]), fv[pr[0]], o)
        return "(%s)" % o
    pay = "(⊢payι %sₘ.⊢J %sF.⊢DF ⊢unit)" % (P, P)
    for t in reversed(range(len(prems))):
        pr = prems[t]
        if pr[0] == "σ":
            pay = "(⊢payσ %sₘ.⊢J %sF.⊢DF {a = e%d} {p = unit} %s de%d %s)" % (P, P, t, okv(t), t, pay)
        else:
            pay = "(⊢payρ %sₘ.⊢J %sF.⊢DF {r = r%d} {p = %s} %s dr%d %s)" % (P, P, t, rest(t + 1), okv(t), t, pay)
    cn = "con" + nm
    L.append("%s : {Ξ : Ctx} {%s : RTm ⌊ Ξ ⌋} → %s" % (cn, " ".join(x for x, _ in hyps), "".join("Ξ ⊢ %s ∷ %s → " % (x, ty) for x, ty in hyps)))
    L.append("  Ξ ⊢ conₗ 0 %s ∷ K%s j %s" % (Pay, P, subj))
    L.append("%s {Ξ} {%s} %s =" % (cn, "} {".join(x for x, _ in hyps), " ".join("d" + x for x, _ in hyps)))
    L.append("  ⊢conRowₖ {Ξ} {1} {0} {%sₘ.J} {%sF.DF} {ix%s j %s} {⌜ T%s j p unit ⌝ᵗ} {%s} {⌜ T%s j p unit ⌝ᵗ ∷ []} nth-z %sₘ.⊢J %sF.⊢DF (⊢ix%s dj %s)" % (
        P, P, P, subj, nm, Pay, nm, P, P, P, dsubj))
    L.append("    (%sF.fibF {s = 1} {k = %d} {j = j} {p = p} {c = unit} (atᵍ 1) %s)" % (P, SIG[h][2], "(atʰ %d)" % (SIG[h][2])))
    L.append("    (⊢tel %sₘ.⊢J (tok%s {c = unit} dj dp) ∷ᵈ []ᵈ) (⊢conv dPv (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))))" % (P, nm))
    L.append("  where")
    L.append("    p : RTm ⌊ Ξ ⌋")
    L.append("    p = %s" % p_)
    L.append("    dp = ⊢payK (lt-s lt-z) ok-k%s dj %s" % (h, args_))
    srcs = ["j"] + [fieldexpr("p", i) for i in range(n)]
    vals = ["j"] + fv
    vars_ = ["(var %s)" % var(i) for i in range(len(args))]
    hs = ["done"] + ["(prj-tup {ws = %s} unit %s)" % (" ∷ ".join(fv + ["[]"]), nth_expr(i)) for i in range(n)]
    L.append("    R : ⌜ %s ⌝ᵗ ⟶* ⌜ %s ⌝ᵗ" % (" ".join([TV] + srcs), " ".join([TV] + vals)))
    L.append("    R = mono-by {Δ = ⌊ Ξ ⌋} {n = %d} {as = %s} {as' = %s} ⌜ %s ⌝ᵗ (%s-sub (σₗ (%s)) %s) (%s-sub (σₗ (%s)) %s) (%s)" % (
        len(args), "(%s)" % " ∷ ".join(srcs + ["[]"]), "(%s)" % " ∷ ".join(vals + ["[]"]), " ".join([TV] + vars_),
        TV, " ∷ ".join(srcs + ["[]"]), " ".join(vars_), TV, " ∷ ".join(vals + ["[]"]), " ".join(vars_), " ∷ʳ ".join(hs + ["[]ʳ"])))
    L.append("    dPv : Ξ ⊢ %s ∷ El (dpay %sₘ.J %sF.DF ⌜ %s ⌝ᵗ)" % (Pay, P, P, " ".join([TV] + vals)))
    L.append("    dPv = %s" % pay)
    L.append("")
    return L


def emit_table(L, M, fam, none, S, entry):
    """★ a family AS ITS TABLE (Lib/SynFib.RowsOK): each constructor's row and
    its typing, in KSig's order; `entry(h)` gives (row, ok) for a head with a
    rule, None for the family's "no rule here" row (typed at every shape)."""
    L.append("ok%s : (s : ℕ) (sh : Shape) → %s.RowOK s sh %s" % (none, M, none))
    L.append("ok%s s sh dj dp dc = ⊢rows {I = %s.J} {Cs = []} %s.⊢J []ᵈ" % (none, M, M))
    L.append("")
    L.append("-- ★ THE FAMILY, as its table: each Knot constructor's row and its typing,")
    L.append("--   in KSig's order (sort 0: types; sort 1: terms).")
    # the table syntax is opened LOCALLY: several families share one module
    # application (Preds), and their constructors would be ambiguous
    L.append("module _ where")
    L.append("  open %s using ( ⟨_∣_⟩∷_; ⟨_∣∀_⟩∷_; []ᴿ; _∷ᴳ_; []ᴳ )" % M)
    L.append("")
    for srt, heads, tag in ((0, TYHEADS, "Ty"), (1, TMHEADS, "Tm")):
        L.append("  rows%s%s : %s.RowsOK %d %s" % (fam, tag, M, srt, "TyShs" if srt == 0 else "TmShs"))
        L.append("  rows%s%s =" % (fam, tag))
        for h in heads:
            e = entry(h) if srt == S else None
            if e is None: L.append("    ⟨ %s ∣∀ ok%s ⟩∷  -- %s" % (none, none, shape_name(h)))
            else:         L.append("    ⟨ %s ∣ %s ⟩∷  -- %s" % (e[0], e[1], shape_name(h)))
        L.append("    []ᴿ")
        L.append("")
    L.append("  rows%s : %s.RowsOKG zero KSig" % (fam, M))
    L.append("  rows%s = rows%sTy ∷ᴳ rows%sTm ∷ᴳ []ᴳ" % (fam, fam, fam))
    L.append("")
    L.append("module %sF = %s.FamilyT rows%s" % (fam, M, fam))


def gen_preds():
    L = [PHDR]
    for P, spec in PREDS.items():
        L.append("------------------------------------------------------------------------")
        L.append("-- ★ %s" % spec["doc"])
        L.append("------------------------------------------------------------------------")
        L.append("")
        L.append("module %sₘ = SynFam KOK (λ {Δ} → ⌜Unit⌝ {Δ ∙}) (λ σ → refl) ⊢⌜Unit⌝" % P)
        L.append("")
        # the index of a recursive premise at depth `j + k`
        L.append("ix%s : RTm Δ → RTm Δ → RTm Δ" % P)
        L.append("ix%s d c = %sₘ.ixJ (pair (tag 1) d) c unit" % (P, P))
        L.append("")
        L.append("⊢ix%s : {Ξ : Ctx} {d c : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ c ∷ K 1 d → Ξ ⊢ ix%s d c ∷ El %sₘ.J" % (P, P, P))
        L.append("⊢ix%s dd dc = %sₘ.⊢ixJ (⊢ix (lt-s lt-z) dd) (⊢SK→IMu {sg = KSig} dc) (⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝)))" % (P, P))
        L.append("")
        for h, prems in spec["rows"].items():
            sh = shape_name(h)
            fs = SIG[h][1]
            nm = "%s⊢%s" % (P, h)
            def fld(i):
                t = "p"
                for _ in range(i): t = "(snd %s)" % t
                return "(fst %s)" % t
            def dep(k):
                t = "j"
                for _ in range(k): t = "(nsuc %s)" % t
                return t
            tel = "tι"
            for pr in reversed(prems):
                if pr[0] == "σ":
                    assert tel == "tι", "a σ-premise is last"
                    tel = "tσ (⌜%s⌝ j %s) tι" % (pr[1], fld(pr[2]))
                else:
                    f, kk = pr
                    tel = "tρ (ix%s %s %s) (%s)" % (P, dep(kk), fld(f), tel)
            L.append("T%s : RTm Δ → RTm Δ → RTm Δ → Tel Δ" % nm)
            L.append("T%s j p c = %s" % (nm, tel))
            L.append("")
            L.append("r%s : Row" % nm)
            sp = [pr for pr in prems if pr[0] == "σ"]
            if sp:
                L.append("r%s = defRow T%s (λ σ j p c → cong (λ Z → dσ Z (lam dι)) (⌜%s⌝-sub σ j %s))" % (nm, nm, sp[0][1], fld(sp[0][2])))
            else:
                L.append("r%s = defRow T%s (λ σ j p c → refl)" % (nm, nm))
            L.append("")
            L.append("ok%s : %sₘ.RowOK 1 %s r%s" % (nm, P, sh, nm))
            body = "ok-ι"
            def ftyping(f):
                d = "dp"
                for m in range(f):
                    d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (fs[m][1], fs[m][2], shape_expr(fs[m + 1:]), d)
                return "(⊢atDepthSK {sg = KSig} {a = tag 1} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
                    fs[f][1], fs[f][2], fs[f][1], fs[f][2], shape_expr(fs[f + 1:]), d)
            for pr in reversed(prems):
                if pr[0] == "σ":
                    body = "ok-σ (⊢⌜%s⌝ dj %s) ok-ι" % (pr[1], ftyping(pr[2]))
                    continue
                (f, k) = pr
                ftyp = "(g0 {j = j} {p = p} %d %d %s %s)" % (fs[f][1], fs[f][2], "[]ʰ", "dp") if f == 0 and len(fs) == 1 else None
                # the field's typing, through the payload's view
                d = "dp"
                for m in range(f):
                    d = "(⊢recSnd {s = %d} {k = %d} {sh = %s} %s)" % (fs[m][1], fs[m][2], shape_expr(fs[m + 1:]), d)
                ftyp = "(⊢atDepthSK {sg = KSig} {a = tag 1} {j = j} {s = %d} {k = %d} (⊢recFst {s = %d} {k = %d} {sh = %s} %s))" % (
                    fs[f][1], fs[f][2], fs[f][1], fs[f][2], shape_expr(fs[f + 1:]), d)
                ddep = "dj"
                for _ in range(k): ddep = "(⊢isuc %s)" % ddep
                body = "ok-ρ (⊢ix%s %s %s) (%s)" % (P, ddep, ftyp, body)
            L.append("tok%s : {Ξ : Ctx} {j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ p ∷ PayV %s (pair (tag 1) j) (SI 2) (SD KSig) → TelOK Ξ %sₘ.J (T%s j p c)" % (nm, sh, P, nm))
            L.append("tok%s {Ξ} {j} {p} {c} dj dp = %s" % (nm, body))
            L.append("")
            L.append("ok%s {Ξ} {j} {p} {c} dj dp dc = ⊢rows {Ξ} {%sₘ.J} {1} {⌜ T%s j p c ⌝ᵗ ∷ []} %sₘ.⊢J (⊢tel {Ξ} {%sₘ.J} {T%s j p c} %sₘ.⊢J (tok%s {c = c} dj dp) ∷ᵈ []ᵈ)" % (
                nm, P, nm, P, P, nm, P, nm))
            L.append("")
            PCONL.extend(gen_pred_con(P, h, prems))
        # the table
        L.append("%sNone : Row" % P)
        L.append("%sNone = record { R = λ j p c → rows [] ; R-sub = λ σ j p c → refl }" % P)
        L.append("")
        emit_table(L, "%sₘ" % P, P, "%sNone" % P, 1, lambda h: ("r%s⊢%s" % (P, h), "ok%s⊢%s" % (P, h)) if h in spec["rows"] else None)
        L.append("")
        L.append("-- the predicate at a code `c : K 1 d`")
        L.append("K%s : RTm Δ → RTm Δ → RTy Δ" % P)
        L.append("K%s d c = %sF.KF (ix%s d c)" % (P, P, P))
        L.append("")
        L.append("-- ★ …and as a CODE (a premise of a higher stratum is a σ-field of it), OPAQUE")
        L.append("opaque")
        L.append("  ⌜%s⌝ : RTm Δ → RTm Δ → RTm Δ" % P)
        L.append("  ⌜%s⌝ d c = ⌜IMu⌝ %sₘ.J %sF.DF (ix%s d c)" % (P, P, P, P))
        L.append("")
        L.append("  ⊢⌜%s⌝ : {Ξ : Ctx} {d c : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ c ∷ K 1 d → Ξ ⊢ ⌜%s⌝ d c ∷ U" % (P, P))
        L.append("  ⊢⌜%s⌝ dd dc = ⊢⌜IMu⌝ %sₘ.⊢J %sF.⊢DF (⊢ix%s dd dc)" % (P, P, P, P))
        L.append("")
        L.append("  ⌜%s⌝-sub : (σ : Sub Δ Θ) (d c : RTm Δ) → subTm σ (⌜%s⌝ d c) ≡ ⌜%s⌝ (subTm σ d) (subTm σ c)" % (P, P, P))
        L.append("  ⌜%s⌝-sub σ d c = cong₂ (λ I D → ⌜IMu⌝ I D (ix%s (subTm σ d) (subTm σ c))) (%sₘ.J-sub σ) (%sF.DF-sub σ)" % (P, P, P, P))
        L.append("")
        L.append("  El-⌜%s⌝ : {d c : RTm Δ} → El (⌜%s⌝ d c) ≅ᵀ K%s d c" % (P, P, P))
        L.append("  El-⌜%s⌝ = credᵀ El-⌜IMu⌝" % P)
        L.append("")
    return L

PHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The side conditions of the kernel's rules as LOWER-STRATUM families
-- (D077): predicates on codes, fibred by the code's head (`Lib/SynFam`,
-- trivial convoy).  A premise `NoNatC c` is a σ-field of its code.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Preds where

open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; lt-z; lt-s; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepthSK )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Lib.SynFam using ( module SynFam )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( defRow )

private
  variable
    Δ Θ : Cx
"""

# ------------------------------------------------------------ the reduction families
def xi_rules(fam):
    """one congruence rule per recursive field of every former of the family's sort"""
    heads = TMHEADS if fam == "⟶" else TYHEADS
    out = {}
    for h in heads:
        srt, fs, _ = SIG[h]
        alts = []
        for i, f in enumerate(fs):
            if f[0] != "rec": continue
            D = DEPTHS[f[2]]
            args = [E(0) if m == i else F(m) for m in range(len(fs))]
            concl = ("id", ("Tm" if fam == "⟶" else "Ty", "J"), "X", k(h, *args))
            if f[1] == FAMS[fam]["S"]:
                alts.append(dict(ex=[("Tm" if f[1] == 1 else "Ty", D)], ents=[("red", D, F(i), E(0)), concl]))
            else:
                assert fam == "⟶ᵀ" and f[1] == 1, (fam, h, f)
                alts.append(dict(ex=[("Tm", D), ("RedC", D, F(i), E(0))], ents=[concl]))
        if alts: out[h] = alts
    return out

R2 = lambda m, i: ("r", m, i)
W1 = lambda x: ("wk", 1, "J", x)
TO = lambda t: ("id", ("Tm", "J"), "X", t)
TOT = lambda A: ("id", ("Ty", "J"), "X", A)
# `tr`'s motive is under a binder: it Fords (`cHom c a m`, D078); its path is a nested case
TRM = [("Tm", "J+1"), ("Tm", "J+1"), ("Tm", "J+1"), ("IdC", ("Tm", "J+1"), F(0), k("cHom", E(0), E(1), E(2)))]
def trJ(h, ex=()): return dict(ex=TRM + list(ex), nest=[(F(1), "hrefl"), (R2(0, 0), h)], ents=[TO(F(2))])
COMP = {"⟶": {
  "app":    [dict(nest=[(F(0), "lam")], ents=[TO(("sub0", 1, "J", R2(0, 0), F(1)))])],                      # β
  "fst":    [dict(nest=[(F(0), "pair")], ents=[TO(R2(0, 0))])],                                              # βfst
  "snd":    [dict(nest=[(F(0), "pair")], ents=[TO(R2(0, 1))])],                                              # βsnd
  "ordtr":  [dict(nest=[(F(0), "nzero")], ents=[TO(k("unit"))]),                                            # ordtr-z
             dict(nest=[(F(0), "nsuc"), (F(1), "nzero"), (F(2), "nzero")], ents=[TO(F(3))]),                 # ordtr-szz
             dict(nest=[(F(0), "nsuc"), (F(1), "nsuc"), (F(2), "nzero")], ents=[TO(F(4))]),                  # ordtr-ssz
             dict(nest=[(F(0), "nsuc"), (F(1), "nzero"), (F(2), "nsuc")],                                    # ordtr-szs
                  ents=[TO(k("absurd", k("cHom", k("cNat"), R2(0, 0), R2(2, 0)), F(3)))]),
             dict(nest=[(F(0), "nsuc"), (F(1), "nsuc"), (F(2), "nsuc")],                                     # ordtr-sss
                  ents=[TO(k("ordtr", R2(0, 0), R2(1, 0), R2(2, 0), F(3), F(4)))])],
  "tr":     [trJ("cbase"), trJ("cSg"), trJ("cUnit"), trJ("cId"), trJ("cIMu"), trJ("cFin"),                  # tr-J-*
             trJ("cHom", [("Pred", "StkA", "J", R2(1, 0))]),                                                 # tr-J-Hom
             dict(ex=[("IdC", ("Tm", "J+1"), F(0), V0)], nest=[(F(1), "lam")], ents=[TO(k("app", F(1), F(2)))]),  # tr-taut
             dict(ex=[("Tm", "J+1"), ("Tm", "J+1"), ("IdC", ("Tm", "J+1"), F(0), k("cHom", E(0), E(1), V0)),      # tr-pw
                      ("Tm", "J+2"), ("PwC", "J+1", E(0), E(3))], nest=[(F(1), "lam")],
                  ents=[TO(k("lam", k("tr", k("cHom", ("pwShK", "J", E(3)), k("app", ("wk", 1, "J+1", E(1)), V1), V0),
                                          R2(0, 0), k("app", W1(F(2)), V0))))])],
  "hrefl":  [dict(ex=[("Tm", "J+1"), ("PwC", "J", F(0), E(0))],                                              # hrefl-pw
                  ents=[TO(k("lam", k("hrefl", E(0), k("app", W1(F(1)), V0))))]),
             dict(nest=[(F(0), "cNat"), (F(1), "nzero")], ents=[TO(k("unit"))]),                             # hrefl-Nat-z
             dict(nest=[(F(0), "cNat"), (F(1), "nsuc")], ents=[TO(k("hrefl", k("cNat"), R2(1, 0)))])],       # hrefl-Nat-s
  "ap":     [dict(ex=[("Pred", "StkC", "J", R2(0, 0))], nest=[(F(2), "hrefl")],                              # ap-J
                  ents=[TO(k("hrefl", F(0), ("sub0", 1, "J", F(1), R2(0, 1))))])],
  "jsub":   [dict(nest=[(F(1), "idrefl")], ents=[TO(F(2))])],                                                # jsub-refl
  "natrec": [dict(nest=[(F(2), "nzero")], ents=[TO(F(0))]),                                                  # natrec-zero
             dict(nest=[(F(2), "nsuc")],                                                                     # natrec-suc
                  ents=[TO(("iinstTmK", "J", R2(0, 0), k("natrec", F(0), F(1), R2(0, 0)), F(1)))])],
  "ielim":  [dict(nest=[(F(3), "con")],                                                                      # ι
                  ents=[TO(k("app", k("app", k("app", F(2), F(1)), R2(0, 0)), k("dih", F(0), F(2), k("app", F(0), F(1)), R2(0, 0))))])],
  "dpay":   [dict(nest=[(F(2), "dI")], ents=[TO(k("cUnit"))]),                                               # dpay-ι
             dict(nest=[(F(2), "dS")],                                                                       # dpay-σ
                  ents=[TO(k("cSg", R2(0, 0), k("dpay", W1(F(0)), W1(F(1)), k("app", W1(R2(0, 1)), V0))))]),
             dict(nest=[(F(2), "dR")],                                                                       # dpay-ρ
                  ents=[TO(k("cSg", k("cIMu", F(0), F(1), R2(0, 0)), k("dpay", W1(F(0)), W1(F(1)), W1(R2(0, 1)))))])],
  "dih":    [dict(nest=[(F(2), "dI")], ents=[TO(k("unit"))]),                                                # dih-ι
             dict(nest=[(F(2), "dS")], ents=[TO(k("dih", F(0), F(1), k("app", R2(0, 1), k("fst", F(3))), k("snd", F(3))))]),  # dih-σ
             dict(nest=[(F(2), "dR")],                                                                       # dih-ρ
                  ents=[TO(k("pair", k("ielim", F(0), R2(0, 0), F(1), k("fst", F(3))), k("dih", F(0), F(1), R2(0, 1), k("snd", F(3)))))])],
  "fcase":  [dict(nest=[(F(0), "fzero")], ents=[TO(F(1))]),                                                  # fcase-z
             dict(nest=[(F(0), "fsuc")], ents=[TO(("sub0", 1, "J", F(2), R2(0, 0)))])],                      # fcase-s
  "psplit": [dict(nest=[(F(1), "pair")], ents=[TO(("iinstTmK", "J", R2(0, 0), R2(0, 1), F(0)))])],           # psplit-β
}, "⟶ᵀ": {
  "El":     [dict(nest=[(F(0), h)], ents=[TOT(t)]) for h, t in [                                            # El-⌜code⌝
               ("cbase", BASE), ("cPi", k("Pi", El(R2(0, 0)), El(R2(0, 1)))), ("cSg", k("Sg", El(R2(0, 0)), El(R2(0, 1)))),
               ("cHom", k("Hom", El(R2(0, 0)), R2(0, 1), R2(0, 2))), ("cId", k("Id", El(R2(0, 0)), R2(0, 1), R2(0, 2))),
               ("cNat", NAT), ("cIMu", k("IMu", R2(0, 0), R2(0, 1), R2(0, 2))), ("cFin", k("Fin", R2(0, 0))), ("cUnit", k("Unit"))]],
  "DIh":    [dict(nest=[(F(2), "dI")], ents=[TOT(k("Unit"))]),                                               # DIh-ι
             dict(nest=[(F(2), "dS")], ents=[TOT(k("DIh", F(0), F(1), k("app", R2(0, 1), k("fst", F(3))), k("snd", F(3))))]),  # DIh-σ
             dict(nest=[(F(2), "dR")],                                                                       # DIh-ρ
                  ents=[TOT(k("Sg", ("iinstK", "J", R2(0, 0), k("fst", F(3)), F(1)),
                              k("DIh", W1(F(0)), ("wk2uK", "J", F(1)), W1(R2(0, 1)), k("snd", W1(F(3))))))])],
  "Hom":    [dict(nest=[(F(0), "Nat"), (F(1), "nzero")], ents=[TOT(k("Unit"))]),                             # Hom-Nat-z
             dict(nest=[(F(0), "Nat"), (F(1), "nsuc"), (F(2), "nzero")], ents=[TOT(BASE)]),                  # Hom-Nat-sz
             dict(nest=[(F(0), "Nat"), (F(1), "nsuc"), (F(2), "nsuc")], ents=[TOT(k("Hom", NAT, R2(1, 0), R2(2, 0)))]),  # Hom-Nat-ss
             dict(nest=[(F(0), "U")], ents=[TOT(k("Pi", El(F(1)), El(W1(F(2)))))]),                          # Hom-U
             dict(nest=[(F(0), "Pi")],                                                                       # Hom-Π
                  ents=[TOT(k("Pi", R2(0, 0), k("Hom", R2(0, 1), k("app", W1(F(1)), V0), k("app", W1(F(2)), V0))))])],
}}

# `pwBody`'s graph on the codes `pw?` accepts: the body in the convoy, one binder deeper
PWRULES = {
  "cPi":  [dict(ents=[("id", ("Tm", "J+1"), "X", F(1))])],
  "cHom": [dict(ex=[("Tm", "J+1")],
                ents=[("red", "J", F(0), E(0)),
                      ("id", ("Tm", "J+1"), "X", k("cHom", E(0), k("app", W1(F(1)), V0), k("app", W1(F(2)), V0)))])],
}
REDMOD = {"⟶": ("Red", "Redₘ"), "⟶ᵀ": ("RedT", "RedTₘ"), "Pw": ("Pw", "Pwₘ")}
REDEXTRA = {"⟶": "open import DirectedHoTT.Examples.Knot.Pw using ( ⌜Pw⌝; ⊢⌜Pw⌝; ⌜Pw⌝-sub )\n"
                  "open import DirectedHoTT.Examples.Knot.Ref using ( rδ; okδ )\n",
            "⟶ᵀ": "open import DirectedHoTT.Examples.Knot.Red using ( ⌜⟶⌝; ⊢⌜⟶⌝; ⌜⟶⌝-sub )\n", "Pw": ""}

def gen_red(fam, only=None):
    global FAM, FAMKEY
    FAM, FAMKEY = FAMS[fam], fam
    if fam == "Pw":
        rules = {h: list(a) for h, a in PWRULES.items()}
    else:
        rules = xi_rules(fam)
        for h, alts in COMP[fam].items(): rules.setdefault(h, []).extend(dict(a, comp=True) for a in alts)
    S = FAMS[fam]["S"]
    heads = TYHEADS if fam == "⟶ᵀ" else TMHEADS
    modname, m = REDMOD[fam]
    hdr = RHDR.replace(RDOC, PWDOC + "\n") if fam == "Pw" else RHDR
    L = [hdr.replace("MODNAME", modname).replace("FAMNAME", fam).replace("EXTRA", REDEXTRA[fam])]
    for h in heads:
        if h in rules and (only is None or h in only):
            L += gen_head(h, dict(alts=rules[h]))
    if only is not None:
        FAM, FAMKEY = FAMS["⊢"], "⊢"
        return [l.replace("module DirectedHoTT.Examples.Knot.%s where" % modname,
                          "module DirectedHoTT.tmp.RedOne where") for l in L]
    none = "%sNone" % fam
    L.append("%s : Row" % none)
    L.append("%s = record { R = λ j p c → rows [] ; R-sub = λ σ j p c → refl }" % none)
    L.append("")
    emit_table(L, m, fam, none, S, lambda h: HANDROWS.get((fam, h)) or (("r%s%s" % (fam, h), "ok%s%s" % (fam, h)) if h in rules else None))
    L.append("")
    ix = FAMS[fam]["ix"]
    L.append("K%s : RTm Δ → RTm Δ → RTm Δ → RTy Δ" % fam)
    L.append("K%s d t u = %sF.KF (%s d t u)" % (fam, fam, ix))
    L.append("")
    L.append("-- ★ as a CODE (a premise of a higher stratum is a σ-field of it), OPAQUE")
    L.append("opaque")
    L.append("  ⌜%s⌝ : RTm Δ → RTm Δ → RTm Δ → RTm Δ" % fam)
    L.append("  ⌜%s⌝ d t u = ⌜IMu⌝ %s.J %sF.DF (%s d t u)" % (fam, m, fam, ix))
    L.append("")
    srtK = "K %d d" % S
    srtU = "K %d %s" % (S, nsucs(FAM.get("Xd", 0), "d"))
    L.append("  ⊢⌜%s⌝ : {Ξ : Ctx} {d t u : RTm ⌊ Ξ ⌋} → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ t ∷ %s → Ξ ⊢ u ∷ %s → Ξ ⊢ ⌜%s⌝ d t u ∷ U" % (fam, srtK, srtU, fam))
    L.append("  ⊢⌜%s⌝ dd dt du = ⊢⌜IMu⌝ %s.⊢J %sF.⊢DF (%s dd dt du)" % (fam, m, fam, FAMS[fam]["dix"]))
    L.append("")
    L.append("  ⌜%s⌝-sub : (σ : Sub Δ Θ) (d t u : RTm Δ) → subTm σ (⌜%s⌝ d t u) ≡ ⌜%s⌝ (subTm σ d) (subTm σ t) (subTm σ u)" % (fam, fam, fam))
    L.append("  ⌜%s⌝-sub σ d t u = cong₂ (λ I D → ⌜IMu⌝ I D (%s (subTm σ d) (subTm σ t) (subTm σ u))) (%s.J-sub σ) (%sF.DF-sub σ)" % (fam, ix, m, fam))
    L.append("")
    L.append("  El-⌜%s⌝ : {d t u : RTm Δ} → El (⌜%s⌝ d t u) ≅ᵀ K%s d t u" % (fam, fam, fam))
    L.append("  El-⌜%s⌝ = credᵀ El-⌜IMu⌝" % fam)
    L.append("")
    FAM, FAMKEY = FAMS["⊢"], "⊢"
    return L

RDOC = """-- The reduction judgement `FAMNAME` as a family fibred by its SUBJECT (the
-- source; D077), the target in the convoy (`RedIx`): per head, one ξ row
-- per recursive field (the reduct a σ-field, the premise a row of the
-- same stratum or a σ-field of the lower one, the target Forded) and the
-- head's computation rules.
"""
PWDOC = """-- `pwBody c ≡ b` on the codes `pw? c` accepts (`Spec/Variance`), the
-- premise of `hrefl-pw` and `tr-pw`, as a LOWER-STRATUM family (D077/D078)
-- fibred by the code, the body one binder deeper in the convoy (`RedIx`):
-- a ⌜Π⌝ is its own codomain, a ⌜Hom⌝ recurses on its ambient."""
RHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The reduction judgement `FAMNAME` as a family fibred by its SUBJECT (the
-- source; D077), the target in the convoy (`RedIx`): per head, one ξ row
-- per recursive field (the reduct a σ-field, the premise a row of the
-- same stratum or a σ-field of the lower one, the target Forded) and the
-- head's computation rules.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MODNAME where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; Lt; lt-z; lt-s; []ᵈ; _∷ᵈ_; AllD )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepthSK; ⊢natFst; ⊢natSnd )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc; toI; ffz; ⊢ffz; ffs; ⊢ffs )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows; toTy; hereTy )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0; sub0-sub )
open import DirectedHoTT.Examples.Knot.Ren using ( wk; ⊢wkS; wk-sub )
open import DirectedHoTT.Examples.Knot.SubEnv
open import DirectedHoTT.Examples.Knot.JudgeIx using ( defRow; rows-sub'; ⌜Tm⌝; ⌜Tm⌝-sub; ⊢⌜Tm⌝; TelLaw )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2; w3; w1-sub; w2-sub; w3-sub; hereTm; toTm; wkN; wkK; wkG )
open import DirectedHoTT.Examples.Knot.GenHelpers
open import DirectedHoTT.Examples.Knot.Preds using ( ⌜StkA⌝; ⊢⌜StkA⌝; ⌜StkA⌝-sub; ⌜StkC⌝; ⊢⌜StkC⌝; ⌜StkC⌝-sub )
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.NestIx
open import DirectedHoTT.Lib.SynPat using ( module Pat )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( defRow₀ )
EXTRA
private
  variable
    Δ Θ : Cx
"""

def main():
    load_sig()
    if "--red" in sys.argv:
        fam, hs = sys.argv[sys.argv.index("--red") + 1].split("=")
        txt = "\n".join(gen_red(fam, hs.split(","))) + "\n"
        open(os.path.join(ROOT, "tmp", "RedOne.agda"), "w", encoding="utf-8").write(txt)
        print("wrote tmp/RedOne.agda"); return
    if "--only" in sys.argv:
        names = sys.argv[sys.argv.index("--only") + 1].split(",")
        L = [HDR.replace("module DirectedHoTT.Examples.Knot.JudgeRowsGen where", "module DirectedHoTT.tmp.JudgeRowsOne where")]
        pass
        for nm in names:
            if nm in TESTRULES:
                al = Alt("tr", "", None, TESTRULES[nm])
                L += gen_alt(al)
            elif "#" in nm:
                base, ix = nm.split("#")
                al = Alt(base, "", RULES[base].get("case"), RULES[base]["alts"][int(ix)])
                out = gen_alt(al)
                if "--notyping" in sys.argv:
                    cut = [i for i, l in enumerate(out) if l.startswith("ok" + al.pfx + " ")]
                    out = out[:cut[0]] if cut else out
                L += out
            else:
                L += gen_head(nm, RULES[nm])
        open(os.path.join(ROOT, "tmp", "JudgeRowsOne.agda"), "w", encoding="utf-8").write("\n".join(L) + "\n")
        print("wrote tmp/JudgeRowsOne.agda"); return
    L = [HDR]
    HL = [GHDR] + gen_helpers(8)
    hlp = "\n".join(HL) + "\n"
    HOUT = os.path.join(ROOT, "Examples", "Knot", "GenHelpers.agda")
    global FAM, FAMKEY
    FAM, FAMKEY = FAMS["⊢ty"], "⊢ty"
    for name in TYHEADS:
        L += gen_head(name, TYRULES[name])
    FAM, FAMKEY = FAMS["⊢"], "⊢"
    for name in TMHEADS:
        if name in RULES:
            L += gen_head(name, RULES.get(name, {}))
    L += gen_table()
    txt = "\n".join(L) + "\n"
    ptxt = "\n".join(gen_preds()) + "\n"
    POUT = os.path.join(ROOT, "Examples", "Knot", "Preds.agda")
    K = lambda n: os.path.join(ROOT, "Examples", "Knot", n + ".agda")
    outs = {OUT: txt, POUT: ptxt, HOUT: hlp, K("JudgeConGen"): CHDR + "\n".join(CONL) + "\n",
            K("PredsCon"): PCHDR + "\n".join(PCONL) + "\n",
            K("PredsAgree"): "\n".join(gen_preds_agree()) + "\n",
            K("PredsDecode"): "\n".join(gen_preds_dec()) + "\n",
            K("PwAgree"): "\n".join(gen_pw_agree()) + "\n",
            K("RedAgree"): "\n".join(gen_enred()) + "\n",
            K("RedTAgree"): "\n".join(gen_enredT()) + "\n"}
    for fam in ("⟶", "⟶ᵀ", "Pw"):
        outs[K(REDMOD[fam][0])] = "\n".join(gen_red(fam)) + "\n"
    outs[K("RedDecode")] = "\n".join(gen_red_dec()) + "\n"
    outs[K("RedTDecode")] = "\n".join(gen_red_dec(("⟶ᵀ",), "RedTDecode")) + "\n"
    for _m, _L in GEN_EXTRA.items(): outs[K(_m)] = "\n".join(_L) + "\n"
    outs[K("RedCompDecode")] = "\n".join(gen_comp_decs()) + "\n"
    for _m, _L in gen_judge_decs().items(): outs[K(_m)] = "\n".join(_L) + "\n"
    outs[K("JudgeDecode")] = "\n".join(gen_judge_dispatch()) + "\n"
    for fam in ("⟶", "⟶β", "⟶ᵀ", "Pw"):
        mod = {"⟶": "RedXiConGen", "⟶β": "RedCompConGen"}[fam] if fam in ("⟶", "⟶β") else REDMOD[fam][0] + "ConGen"
        hdr = RCHDR.replace("module DirectedHoTT.Examples.Knot.RedConGen where", "module DirectedHoTT.Examples.Knot.%s where" % mod)
        hdr = hdr.replace("CONSTRUCTORS of the generated ⟶ / ⟶ᵀ / Pw rows", "CONSTRUCTORS of the generated %s rows" % {
            "⟶": "⟶ congruence (ξ)", "⟶β": "⟶ computation"}.get(fam, fam))
        hdr = hdr.replace("RCIMPORTS", RCIMPORTS[fam])
        outs[K(mod)] = hdr + "\n".join(REDCONL[fam]) + "\n"
    outs = {f: COPYRIGHT + t for f, t in outs.items()}
    # the object-term notation (v₃, e ,ₚ …) — pattern synonyms, see tools/notation.py
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import notation
    outs = {f: notation.notate(t) for f, t in outs.items()}
    if "--check" in sys.argv:
        stale = [f for f, t in outs.items() if not os.path.exists(f) or open(f, encoding="utf-8").read() != t]
        # ★ the deletion pass: a module this generator wrote once and no longer writes
        import glob as _g
        for f in _g.glob(os.path.join(ROOT, "Examples", "Knot", "*.agda")):
            if f not in outs and "GENERATED by tools/gen-judge.py" in open(f, encoding="utf-8").read(600):
                stale.append(f + " (no longer generated: delete it)")
        if stale:
            print("STALE: %s" % ", ".join(os.path.relpath(f, ROOT) for f in stale)); sys.exit(1)
        print("ok"); return
    for f, t in outs.items(): open(f, "w", encoding="utf-8").write(t)
    print("wrote %s" % ", ".join(os.path.relpath(f, ROOT) for f in outs))

GHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The generated rows' shared helpers: the weakenings past 3 binders and
-- their commutation, the σ-prefix congruences and the row-list
-- congruences (explicit arguments: metas here cost minutes).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.GenHelpers where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2; w3; w1-sub; w2-sub; w3-sub )

private
  variable
    Δ Θ : Cx

"""

HDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The Knot's `⊢ty` and `⊢` rows (D077), one scheme per row; see the
-- generator's header.  Each telescope is a chain of TAILS `N⁽ᵏ⁾` (its
-- positions and first k existentials explicit), each with its own law —
-- what the constructors (`JudgeConGen`) instantiate at values.  Only
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeRowsGen where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; Lt; lt-z; lt-s; []ᵈ; _∷ᵈ_; AllD )
open import DirectedHoTT.Lib.SynView using ( PayV; ⊢recFst; ⊢recSnd; ⊢atDepthSK )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc; toI; ffz; ⊢ffz; ffs; ⊢ffs )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynFib using ( Row )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( rows; ⊢rows; toTy; hereTy )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0; sub0-sub )
open import DirectedHoTT.Examples.Knot.Ren using ( wk; ⊢wkS; wk-sub )
open import DirectedHoTT.Examples.Knot.SubEnv using ( nrsK; ⊢nrsK; nrsK-sub; pairSK; ⊢pairSK; pairSK-sub; fsucSK; ⊢fsucSK; fsucSK-sub; iinstK; ⊢iinstK; iinstK-sub; MethTyK; ⊢MethTyK; MethTyK-sub )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeCase
open import DirectedHoTT.Examples.Knot.GenHelpers
open import DirectedHoTT.Examples.Knot.JudgeFib using ( RowOK; okNone; RowsOK; ⟨_∣_⟩∷_; ⟨_∣∀_⟩∷_; []ᴿ )
open import DirectedHoTT.Examples.Knot.Preds using ( ⌜Flat⌝; ⊢⌜Flat⌝; ⌜Flat⌝-sub; ⌜NNC⌝; ⊢⌜NNC⌝; ⌜NNC⌝-sub )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Examples.Knot.JudgeRowsTm using ( ⊢varOf )
open import DirectedHoTT.Examples.Knot.JudgeConv using ( TCVat; TCVat-law; okTCVat; ⌜∋⌝; ⊢⌜∋⌝; ⌜∋⌝-sub )
open import DirectedHoTT.Examples.Knot.RefJudge using ( r⊢ref; ok⊢ref )
open import DirectedHoTT.Lib.FinFam using ( FinI )

private
  variable
    Δ Θ : Cx
"""

CHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The CONSTRUCTORS of the generated `⊢` rows: a rule's derivation as a Knot
-- term, at VALUES.  The payload is built through the row's tails (one tail
-- law + `wk-cancel` per σ-field); the row, written at the fibre's sources,
-- reduces to it by ONE `mono-by` (`Lib/SynRed`), fed by `prj-tup` per
-- position.  `⊢conv`'s payload is typed once (`JudgeConv.⊢payTCVat`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeConGen where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; conₗ; lt-z; lt-s; nth-z; nth-s; atᶜ )
open import DirectedHoTT.Lib.SynFib using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.FinFam using ( FinI; ⊢isuc; toI; ffz; ⊢ffz; ffs; ⊢ffs )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( toTy; hereTy )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0 )
open import DirectedHoTT.Examples.Knot.Ren using ( wk; ⊢wkS )
open import DirectedHoTT.Examples.Knot.SubEnv using ( nrsK; ⊢nrsK; pairSK; ⊢pairSK; fsucSK; ⊢fsucSK; iinstK; ⊢iinstK; MethTyK; ⊢MethTyK )
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeTmIx
open import DirectedHoTT.Examples.Knot.JudgeCase
open import DirectedHoTT.Examples.Knot.Preds using ( ⌜Flat⌝; ⊢⌜Flat⌝; ⌜NNC⌝; ⊢⌜NNC⌝ )
open import DirectedHoTT.Examples.Knot.JudgeConv using ( TCVat; ⌜∋⌝; ⊢⌜∋⌝; ⊢payTCVat )
open import DirectedHoTT.Examples.Knot.Conv using ( ⌜≅ᵀ⌝ )
open import DirectedHoTT.Examples.Knot.GenHelpers
open import DirectedHoTT.Examples.Knot.JudgeRowsGen
open import DirectedHoTT.Examples.Knot.Judge using ( D⊢; ⊢D⊢; fibK )

"""

# ------------------------------------------------------------ side conditions are COMPLETE (PLAN-FAITHFUL F4)
NNC_CTORS = {"cbase": "nnc-base", "cUnit": "nnc-Unit", "cFin": "nnc-Fin", "cSg": "nnc-Σ", "cId": "nnc-Id",
             "cPi": "nnc-Π", "cHom": "nnc-Hom"}
BOOLPREDS = [("StkA", "stkA?", "stkAC"), ("StkC", "stkC?", "stkCC"), ("Flat", "flat?", "flatC")]

def gen_preds_agree():
    inv = {v: k for k, v in gk.NAMES.items()}
    spec = lambda h: inv.get(h, h)
    def fty(f, a):
        if f[0] == "rec": return "(⊢quote%s %s)" % ("Ty" if f[1] == 0 else "Tm", a)
        if f[0] == "nat": return "(⊢quoteℕ %s)" % a
        return "(⊢quoteVar %s)" % a
    L = [PAHDR]
    # NoNatC: an inductive proof, mapped constructor by constructor
    L.append("nncC : {Γ : Cx} {c : RTm Γ} → NoNatC c → {Θ : Cx} → RTm Θ")
    L.append("⊢nncC : {Γ : Cx} {c : RTm Γ} (w : NoNatC c) {Θ : Ctx} → Θ ⊢ nncC w ∷ KNNC (dep Γ) (quoteTm c)")
    for h, prems in PREDS["NNC"]["rows"].items():
        rec = [pr for pr in prems if pr[0] != "σ"]
        L.append("nncC %s = conₗ 0 %s" % ("(%s w)" % NNC_CTORS[h] if rec else NNC_CTORS[h], "(pair (nncC w) unit)" if rec else "unit"))
    for h, prems in PREDS["NNC"]["rows"].items():
        fs = SIG[h][1]
        args = ["a%d" % i for i in range(len(fs))]
        rec = [pr for pr in prems if pr[0] != "σ"]
        pat = "(%s%s%s)" % (NNC_CTORS[h], "".join(" {%s}" % a for a in args), " w" if rec else "")
        L.append("⊢nncC {Γ} %s = conNNC⊢%s (⊢dep' Γ)%s%s" % (pat, h, "".join(" " + fty(f, a) for f, a in zip(fs, args)),
                                                              " (⊢nncC w)" if rec else ""))
    L.append("")
    # the Boolean ones: by the code's head; a false head is absurd
    for P, fn, cn in BOOLPREDS:
        rows = PREDS[P]["rows"]
        L.append("%s : {Γ : Cx} (c : RTm Γ) → %s c ≡ true → {Θ : Cx} → RTm Θ" % (cn, fn))
        L.append("⊢%s : {Γ : Cx} (c : RTm Γ) (e : %s c ≡ true) {Θ : Ctx} → Θ ⊢ %s c e ∷ K%s (dep Γ) (quoteTm c)" % (cn, fn, cn, P))
        for h in TMHEADS:
            fs = SIG[h][1]
            args = ["a%d" % i for i in range(len(fs))]
            pat = "(%s)" % " ".join([spec(h)] + args) if args else spec(h)
            if h not in rows:
                L.append("%s %s ()" % (cn, pat)); continue
            items = []
            for pr in rows[h]:
                if pr[0] == "σ":
                    q = [b for b in BOOLPREDS if b[0] == pr[1]][0][2]
                    items.append("(%s %s e)" % (q, args[pr[2]]))
                else:
                    items.append("(%s %s e)" % (cn, args[pr[0]]))
            pay = "unit"
            for it in reversed(items): pay = "(pair %s %s)" % (it, pay)
            L.append("%s %s e = conₗ 0 %s" % (cn, pat, pay))
        for h in TMHEADS:
            fs = SIG[h][1]
            args = ["a%d" % i for i in range(len(fs))]
            pat = "(%s)" % " ".join([spec(h)] + args) if args else spec(h)
            if h not in rows:
                L.append("⊢%s %s ()" % (cn, pat)); continue
            prs = []
            for pr in rows[h]:
                if pr[0] == "σ":
                    q = [b for b in BOOLPREDS if b[0] == pr[1]][0][2]
                    prs.append("(⊢conv (⊢%s %s e) (csymᵀ El-⌜%s⌝))" % (q, args[pr[2]], pr[1]))
                else:
                    prs.append("(⊢%s %s e)" % (cn, args[pr[0]]))
            L.append("⊢%s {Γ} %s e = con%s⊢%s (⊢dep' Γ)%s%s" % (cn, pat, P, h, "".join(" " + fty(f, a) for f, a in zip(fs, args)),
                                                            "".join(" " + x for x in prs)))
        L.append("")
    return L

# ------------------------------------------------------------ F6: the side conditions, decoded
PDHDR = """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PredsDecode where

------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- ★ PLAN-FAITHFUL F6 — the side-condition families are EXACT: the converse
-- of `PredsAgree`.  A closed normal inhabitant at a quoted code gives the
-- Spec's side condition (`NoNatC c`, `stkA? c ≡ true`, `stkC? c ≡ true`,
-- `flat? c ≡ true`).  Each row is read along its constructor
-- (`PredsCon`): the row's telescope reduced to its values by the same
-- `mono-by`, the premise peeled and decoded by recursion on the code; a
-- head with no row has an EMPTY fibre (`rows-none`).  No `with` (memory:
-- with-over-knot-contexts-ooms) — one helper per step.
------------------------------------------------------------------------

open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_; _×_; ⊥; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; stkA?; stkC?; flat?; NoNatC; nnc-base; nnc-Unit; nnc-Fin; nnc-Σ; nnc-Id; nnc-Π; nnc-Hom )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; atᶜ; v₀; v₁; v₂; v₃; v₄; _,ₚ_; nth-z )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Preds
open import DirectedHoTT.Examples.Knot.PredsCon

"""

def gen_preds_dec():
    inv = {v: k for k, v in gk.NAMES.items()}
    spec = lambda h: inv.get(h, h)
    FAMS_ = [("NNC", None, "decNNC"), ("StkA", "stkA?", "decStkA"), ("StkC", "stkC?", "decStkC"), ("Flat", "flat?", "decFlat")]
    DEC = {P: dn for P, _, dn in FAMS_}
    def qf(f, a):
        if f[0] in ("rec", "cls"): return "(quote%s %s)" % ("Ty" if f[1] == 0 else "Tm", a)
        if f[0] == "nat": return "(quoteℕ %s)" % a
        return "(quoteVar %s)" % a
    def fty(f):
        if f[0] == "nat": return "ℕ"
        if f[0] == "cls": return "%s ε" % ("RTy" if f[1] == 0 else "RTm")
        return "%s (Γ%s)" % ("RTy" if f[1] == 0 else "RTm", " ∙" * f[2])
    def depv(k):
        t = "(dep Γ)"
        for _ in range(k): t = "(nsuc %s)" % t
        return t
    L = [PDHDR]
    # signatures
    for P, fn, dn in FAMS_:
        res = "NoNatC c" if fn is None else "%s c ≡ true" % fn
        L.append("%s : {Γ : Cx} (c : RTm Γ) {x : RTm ε} → ◇ ⊢ x ∷ K%s (dep Γ) (quoteTm c) → IsNormal x → %s" % (dn, P, res))
    L.append("")
    L.append("private")
    body = []
    for P, fn, dn in FAMS_:
        for h, prems in PREDS[P]["rows"].items():
            fs = SIG[h][1]; n = len(fs)
            args = ["a%d" % i for i in range(n)]
            hasrec = any(f[0] in ("rec", "cls") for f in fs)
            subj = "(%s)" % " ".join([spec(h) + ("" if hasrec else " {Γ}")] + args)
            res = ("NoNatC %s" % subj) if fn is None else ("%s %s ≡ true" % (fn, subj))
            PP = "unit"
            for f, a in reversed(list(zip(fs, args))): PP = "(%s ,ₚ %s)" % (qf(f, a), PP)
            nm = "%s⊢%s" % (P, h)
            TV = "TV" + nm
            binds = "".join(" (%s : %s)" % (a, fty(f)) for f, a in zip(fs, args))
            h1 = "d%s₁" % nm
            L.append("  %s : {Γ : Cx}%s {x : RTm ε} →" % (h1, binds))
            L.append("       RowsDec %sₘ.J %sF.DF (⌜ T%s (dep Γ) %s unit ⌝ᵗ ∷ []) x → %s" % (P, P, nm, PP, res))
            if not prems:
                ctor = "refl" if fn is not None else NNC_CTORS[h]
                body.append("  %s%s _ = %s" % (h1, "".join(" " + a for a in args), ctor))
            else:
                assert len(prems) == 1, (P, h)
                pr = prems[0]
                # the value telescope's reduction
                Rn = "R" + nm
                srcs = ["(dep Γ)"] + [fieldexpr("p", i) for i in range(n)]
                vals = ["(dep Γ)"] + [qf(f, a) for f, a in zip(fs, args)]
                vars_ = ["(var %s)" % var(i) for i in range(n + 1)]
                hs = ["done"] + ["(prj-tup {ws = %s} unit %s)" % (" ∷ ".join([qf(f, a) for f, a in zip(fs, args)] + ["[]"]), nth_expr(i)) for i in range(n)]
                L.append("  %s : {Γ : Cx}%s → ⌜ T%s (dep Γ) %s unit ⌝ᵗ ⟶* ⌜ %s ⌝ᵗ" % (Rn, binds, nm, PP, " ".join([TV] + vals)))
                body.append("  %s {Γ}%s = mono-by {Δ = ε} {n = %d} {as = %s} {as' = %s} ⌜ %s ⌝ᵗ (%s-sub (σₗ (%s)) %s) (%s-sub (σₗ (%s)) %s) (%s)" % (
                    Rn, "".join(" " + a for a in args), n + 1, "(%s)" % " ∷ ".join(srcs + ["[]"]), "(%s)" % " ∷ ".join(vals + ["[]"]),
                    " ".join([TV] + vars_), TV, " ∷ ".join(srcs + ["[]"]), " ".join(vars_), TV, " ∷ ".join(vals + ["[]"]),
                    " ".join(vars_), " ∷ʳ ".join(hs + ["[]ʳ"])))
                body.append("    where")
                body.append("      p : RTm ε")
                body.append("      p = %s" % PP)
                h2 = "d%s₂" % nm
                C = "⌜ %s ⌝ᵗ" % " ".join([TV] + vals)
                if pr[0] == "σ":
                    Q, i = pr[1], pr[2]
                    S = "⌜%s⌝ (dep Γ) %s" % (Q, qf(fs[i], args[i]))
                    L.append("  %s : {Γ : Cx}%s {q : RTm ε} → PayΣ %sₘ.J %sF.DF (%s) (lam dι) q → %s" % (h2, binds, P, P, S, res))
                    body.append("  %s {Γ}%s (_ , (_ , (q , (nth-z , (_ , (dq , nq)))))) =" % (h1, "".join(" " + a for a in args)))
                    body.append("    %s {Γ = Γ}%s (pay-σ {I = %sₘ.J} {D = %sF.DF} {C = %s} {S = %s} {f = lam dι} (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (%s {Γ = Γ}%s))))) done nq)" % (
                        h2, "".join(" " + a for a in args), P, P, C, S, Rn, "".join(" " + a for a in args)))
                    body.append("  %s%s (e , (_ , (_ , ((de , _) , (ne , _))))) = %s %s (⊢conv de El-⌜%s⌝) ne" % (
                        h2, "".join(" " + a for a in args), DEC[Q], args[i], Q))
                else:
                    i, k = pr
                    J = "ix%s %s %s" % (P, depv(k), qf(fs[i], args[i]))
                    L.append("  %s : {Γ : Cx}%s {q : RTm ε} → PayΡ %sₘ.J %sF.DF (%s) dι q → %s" % (h2, binds, P, P, J, res))
                    body.append("  %s {Γ}%s (_ , (_ , (q , (nth-z , (_ , (dq , nq)))))) =" % (h1, "".join(" " + a for a in args)))
                    body.append("    %s {Γ = Γ}%s (pay-ρ {I = %sₘ.J} {D = %sF.DF} {C = %s} {j = %s} {C' = dι} (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (%s {Γ = Γ}%s))))) done nq)" % (
                        h2, "".join(" " + a for a in args), P, P, C, J, Rn, "".join(" " + a for a in args)))
                    rec = "%s %s dr nr" % (DEC[P], args[i])
                    out = rec if fn is not None else "%s (%s)" % (NNC_CTORS[h], rec)
                    body.append("  %s%s (r , (_ , (_ , ((dr , _) , (nr , _))))) = %s" % (h2, "".join(" " + a for a in args), out))
    L.append("")
    L += body
    L.append("")
    for P, fn, dn in FAMS_:
        rows = PREDS[P]["rows"]
        for h in TMHEADS:
            fs = SIG[h][1]; n = len(fs)
            args = ["a%d" % i for i in range(n)]
            pat = "(%s)" % " ".join([spec(h)] + args) if args else spec(h)
            hasrec = any(f[0] in ("rec", "cls") for f in fs)
            subjE = "(%s)" % " ".join([spec(h) + ("" if hasrec else " {Γ}")] + args)
            K = SIG[h][2]
            if h not in rows:
                L.append("%s {Γ} %s dx nrm = ⊥-elim (rows-none (%sF.fibF {s = 1} {k = %d} {j = dep Γ} {c = unit} (atᵍ 1) (atʰ %d)) dx nrm)" % (dn, pat, P, K, K))
                continue
            PP = "unit"
            for f, a in reversed(list(zip(fs, args))): PP = "(%s ,ₚ %s)" % (qf(f, a), PP)
            nm = "%s⊢%s" % (P, h)
            L.append("%s {Γ} %s dx nrm =" % (dn, pat))
            L.append("  d%s₁ {Γ = Γ}%s (rows-dec {I = %sₘ.J} {D = %sF.DF} {i = ix%s (dep Γ) (quoteTm %s)} {m = 1} {Cs = ⌜ T%s (dep Γ) %s unit ⌝ᵗ ∷ []}" % (
                nm, "".join(" " + a for a in args), P, P, P, subjE, nm, PP))
            L.append("    (%sF.fibF {s = 1} {k = %d} {j = dep Γ} {p = %s} {c = unit} (atᵍ 1) (atʰ %d)) dx nrm)" % (P, K, PP, K))
        L.append("")
    return L

# ------------------------------------------------------------ F6: the reduction families, decoded
DECREC = {}   # (fam, head) → {rule index → the constructor generator's state}

RDHDR = """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedDecode where

------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- ★ PLAN-FAITHFUL F6 — THE REDUCTION JUDGEMENTS ARE EXACT: the converse of
-- `RedAgree`/`RedTAgree`.  A closed normal inhabitant at a quoted judgement
-- `K⟶ ⌜Γ⌝ ⌜t⌝ ⌜u⌝` is one of the subject's rules (`rows-dec`), and each rule
-- is decoded along ITS OWN CONSTRUCTOR's state (`gen_con`): the row's
-- telescope reduced to the values by the same `mono-by`, the payload
-- peeled field by field, existentials unquoted, premises decoded by
-- recursion, the Ford closed by `nf-≅` + quote injectivity.  Chained with
-- `▷` (no `with`: with-over-knot-contexts-ooms).
------------------------------------------------------------------------

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊥; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; pw?; pwBody; stkA?; stkC? )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; atᶜ; v₀; v₁; v₂; v₃; v₄; v₅; v₆; v₇; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Lib.PatDecode
open import DirectedHoTT.Lib.FinFam using ( FinI; ffz; ffs )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Unquote
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⌜Tm⌝; ⌜Ty⌝; El-⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2; w3 )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0 )
open import DirectedHoTT.Examples.Knot.Ren using ( wk )
open import DirectedHoTT.Examples.Knot.SubEnv
open import DirectedHoTT.Examples.Knot.GenHelpers
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.NestIx
open import DirectedHoTT.Examples.Knot.Pw
open import DirectedHoTT.Examples.Knot.Preds
open import DirectedHoTT.Examples.Knot.Red
open import DirectedHoTT.Examples.Knot.RedT
open import DirectedHoTT.Examples.Knot.OpAgree
open import DirectedHoTT.Examples.Knot.PwDecode using ( decPw )
open import DirectedHoTT.Examples.Knot.PredsDecode
open import DirectedHoTT.Lib.RowsElim
open import DirectedHoTT.Examples.Knot.RedCompDecode
open import DirectedHoTT.Examples.Knot.Ref using ( Tδ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-natrecᶻ )

"""

def _depth(dstr):
    """an existential's depth `J`, `J+1`, … as a number of binders"""
    return 0 if dstr == "J" else int(dstr.split("+")[1])

def _tokrep(text, name, by):
    return re.sub(r"(?<![\w'ᵢ₀-₉⁰-⁹])%s(?![\w'ᵢ₀-₉⁰-⁹])" % re.escape(name), by, text)

def gen_red_dec(fams=("⟶",), mod="RedDecode"):
    inv = {v: k for k, v in gk.NAMES.items()}
    spec = lambda h: "RTy.Fin" if h == "Fin" else inv.get(h, h)
    # the ξ rules, parsed as `gen_enred` parses them: (fam, head, field) → name
    ximap = {}
    for fam, rel in (("⟶", "_⟶_"), ("⟶ᵀ", "_⟶ᵀ_")):
        for name, ty in spec_ctors(rel):
            if not name.startswith("ξ-"): continue
            if fam == "⟶":
                m = re.search(r"→\s*(\S+)\s*⟶\s*(\S+)\s*→\s*(.+?)\s*⟶\s*(.+)$", ty); g3, g4 = 3, 4
            else:
                m = re.search(r"→\s*(\S+)\s*(⟶ᵀ|⟶)\s*(\S+)\s*→\s*(.+?)\s*⟶ᵀ\s*(.+)$", ty); g3, g4 = 4, 5
            lt, rt = m.group(g3).split(), m.group(g4).split()
            h = gk.NAMES.get(lt[0], lt[0])
            i = [k for k in range(len(lt) - 1) if lt[1 + k] != rt[1 + k]][0]
            ximap[(fam, h, i)] = name
    QT = {0: "quoteTy", 1: "quoteTm"}
    def qf(f, a):
        if f[0] in ("rec", "cls"): return "(%s %s)" % (QT[f[1]], a)
        if f[0] == "nat": return "(quoteℕ %s)" % a
        return "(quoteVar %s)" % a
    def fty(f):
        if f[0] == "nat": return "ℕ"
        if f[0] == "var": return "Var Γ"
        if f[0] == "cls": return "%s ε" % ("RTy" if f[1] == 0 else "RTm")
        return "%s (Γ%s)" % ("RTy" if f[1] == 0 else "RTm", " ∙" * f[2])
    hdr = RDHDR.replace("module DirectedHoTT.Examples.Knot.RedDecode where", "module DirectedHoTT.Examples.Knot.%s where" % mod)
    if mod != "RedDecode": hdr = hdr.replace("open import DirectedHoTT.Examples.Knot.RedCompDecode\n", "open import DirectedHoTT.Examples.Knot.RedCompDecode\nopen import DirectedHoTT.Examples.Knot.RedDecode using ( decRed )\n")
    L = [hdr]
    FAMSPEC = {"⟶": ("decRed", "RTm", "quoteTm", "_⟶_", "⟶"), "⟶ᵀ": ("decRedT", "RTy", "quoteTy", "_⟶ᵀ_", "⟶ᵀ")}
    for fam in fams:
        dn, RT, Q, _, arr = FAMSPEC[fam]
        F = FAMS[fam]
        L.append("%s : {Γ : Cx} (t : %s Γ) {u : %s Γ} {k : RTm ε} →" % (dn, RT, RT))
        L.append("  ◇ ⊢ k ∷ IMu %s %s (%s (dep Γ) (%s t) (%s u)) → IsNormal k → t %s u" % (F["J"], F["D"], F["ix"], Q, Q, arr))
    L.append("")
    helpers, clauses = [], []
    for fam in fams:
        dn, RT, Q, _, arr = FAMSPEC[fam]
        F = FAMS[fam]
        Jn, Dn = F["J"], F["D"]
        S = F["S"]
        heads = TYHEADS if fam == "⟶ᵀ" else TMHEADS
        for h in heads:
            fs = SIG[h][1]; K = SIG[h][2]
            args = ["a%d" % i for i in range(len(fs))]
            pat = "(%s)" % " ".join([spec(h)] + args) if args else spec(h)
            hasrec = any(f[0] in ("rec", "cls") for f in fs)
            subjE = "(%s)" % " ".join([spec(h) + ("" if hasrec else " {Γ}")] + args)
            recs = DECREC.get((fam, h))
            if recs is None:
                if (fam, h) == ("⟶", "ref"):
                    # ★ δ (hand row `Knot/Ref`): one row, its Ford against `εwk-agree`
                    PPr = "(pair (quoteℕ a0) (pair (quoteTm a1) unit))"
                    clauses += ["%s {Γ} %s {u} dk nrm =" % (dn, pat),
                        "  rows-dec {I = %s} {D = %s} {i = %s (dep Γ) (quoteTm (ref {Γ} a0 a1)) (quoteTm u)} {m = 1} {Cs = ⌜ Tδ (dep Γ) %s (quoteTm u) ⌝ᵗ ∷ []}" % (Jn, Dn, F["ix"], PPr),
                        "    (%s {s = %d} {k = %d} {j = dep Γ} {p = %s} {c = quoteTm u} (atᵍ %d) (atʰ %d)) dk nrm" % (F["fib"], S, K, PPr, S, K),
                        "  ▷ λ { (_ , (_ , (_ , (nth-z , (_ , (dq , nq)))))) → dδ a0 a1 u dq nq }"]
                    helpers.append(["dδ : {Γ : Cx} (a0 : ℕ) (a1 : RTm ε) (u : RTm Γ) {q : RTm ε} →",
                        "  ◇ ⊢ q ∷ El (dpay %s %s ⌜ Tδ (dep Γ) %s (quoteTm u) ⌝ᵗ) → IsNormal q → ref a0 a1 ⟶ u" % (Jn, Dn, PPr),
                        "dδ {Γ} a0 a1 u dq nq =",
                        "  pay-σ dq done nq",
                        "  ▷ λ { (_ , (_ , (_ , ((dF , _) , (nF , _))))) →",
                        "  close (δref {Γ} a0 a1) (ctrn (idrefl-decᶜ dF nF) (⟶*→≅ (⟶*-trans (⟶*-natrecᶻ (prj-tup {ws = quoteℕ a0 ∷ quoteTm a1 ∷ []} unit (atᶜ 1))) (εwk-agree Γ a1)))) }",
                        ""])
                    continue
                if (fam, h) in HANDROWS:
                    clauses.append("%s {Γ} %s {u} dk nrm = {!!}" % (dn, pat)); continue
                clauses.append("%s {Γ} %s {u} dk nrm = ⊥-elim (rows-none (%s {s = %d} {k = %d} {j = dep Γ} {c = %s u} (atᵍ %d) (atʰ %d)) dk nrm)"
                               % (dn, pat, F["fib"], S, K, Q, S, K))
                continue
            PP = "unit"
            for f, a in reversed(list(zip(fs, args))): PP = "(pair %s %s)" % (qf(f, a), PP)
            rec0 = recs[min(recs)]
            csf = rec0["csf"]; nc = rec0["nc"]
            ent = lambda r: csf[r][0]("(dep Γ)", PP, "(%s u)" % Q)
            ENTRIES = " ∷ ".join(ent(r) for r in range(nc)) + " ∷ []"
            cl = ["%s {Γ} %s {u} dk nrm =" % (dn, pat),
                  "  rows-elim (rows-dec {I = %s} {D = %s} {i = %s (dep Γ) (%s %s) (%s u)} {m = %d} {Cs = %s}" % (Jn, Dn, F["ix"], Q, subjE, Q, nc, ENTRIES),
                  "    (%s {s = %d} {k = %d} {j = dep Γ} {p = %s} {c = %s u} (atᵍ %d) (atʰ %d)) dk nrm)" % (F["fib"], S, K, PP, Q, S, K)]
            alts_ = []
            for r in range(nc):
                nth = "nth-z"
                for _ in range(r): nth = "(nth-s %s)" % nth
                hn = "d%s%s₍%d₎" % (fam, h, r)
                if recs.get(r) is not None and recs[r]["al"].comp: hn = comp_name(fam, h, r)
                else: helpers.append(gen_rule_dec(fam, h, r, recs.get(r), hn, fs, args, pat, subjE, PP, ent(r), ximap, qf, fty))
                ihf = rule_ih(recs.get(r)) if not (recs.get(r) is not None and recs[r]["al"].comp) else None
                ihA = " (%s %s)" % (dn, args[ihf]) if ihf is not None else ""
                alts_.append("%s%s%s u" % (hn, "".join(" " + a for a in args), ihA))
            # ★ one handler per row (`rows-elim`), not a pattern lambda over `Nth`: half the cost (measured)
            hs_ = "tt"
            for a_ in reversed(alts_): hs_ = "(%s , %s)" % (a_, hs_)
            cl.append("    " + hs_)
            clauses += cl
    # ★ split by consumption: the (non-recursive) rule helpers in their own module
    H = [hdr.replace("module DirectedHoTT.Examples.Knot.%s where" % mod, "module DirectedHoTT.Examples.Knot.%sXi where" % mod)
            .replace("open import DirectedHoTT.Lib.RowsElim\n", "")]
    for fam in fams:
        dn, RT, Q, _, arr = FAMSPEC[fam]
        F = FAMS[fam]
        H += ["-- the induction hypothesis a ξ helper receives: the caller's decoder at the field",
              "IH%s : {Γ : Cx} → %s Γ → Set" % (arr, RT),
              "IH%s {Γ} t = {u : %s Γ} {k : RTm ε} → ◇ ⊢ k ∷ IMu %s %s (%s (dep Γ) (%s t) (%s u)) → IsNormal k → t %s u" % (
                  arr, RT, F["J"], F["D"], F["ix"], Q, Q, arr), ""]
    for hl in helpers: H += hl
    L.insert(1, "open import DirectedHoTT.Examples.Knot.%sXi\n" % mod)
    L += clauses
    GEN_EXTRA[mod + "Xi"] = H
    return L

GEN_EXTRA = {}

def rule_ih(rec):
    """a ξ rule whose premise is a body row of its OWN family: the field it recurses on"""
    if rec is None or rec["Ln"] or rec["case"] or rec["al"].comp or rec.get("xi") is None: return None
    return rec["xi"] if any(e[0] == "red" for e in rec["body"]) else None

def gen_rule_dec(fam, h, r, rec, hn, fs, args, pat, subjE, PP, entry, ximap, qf, fty):
    """one rule's decoder: its signature and its ▷ chain"""
    dn, RT, Q, arr = ("decRed", "RTm", "quoteTm", "⟶") if fam == "⟶" else ("decRedT", "RTy", "quoteTy", "⟶ᵀ")
    F = FAMS[fam]; Jn, Dn = F["J"], F["D"]
    binds = "".join(" (%s : %s)" % (a, fty(f)) for f, a in zip(fs, args))
    ihf = rule_ih(rec)
    if ihf is not None: binds += " (ih : IH%s %s)" % (arr, args[ihf])
    sig = ["%s : {Γ : Cx}%s (u : %s Γ) {q : RTm ε} →" % (hn, binds, RT),
           "  ◇ ⊢ q ∷ El (dpay %s %s %s) → IsNormal q → %s %s u" % (Jn, Dn, entry, subjE, arr)]
    if rec is None or rec["Ln"] or rec["case"] or rec["al"].comp or rec.get("xi") is None:
        return sig + ["%s {Γ}%s u dq nq = {!!}" % (hn, "".join(" " + a for a in args)), ""]
    # ── a ξ rule: field i, the new value an existential, the premise a body row or a RedC code
    i = rec["xi"]
    al, n, body, val, XP, tn = rec["al"], rec["n"], rec["body"], rec["val"], rec["XP"], rec["tn"]
    xs = ["c" if p == "X" else val[p] for p in XP]
    m = len(XP)
    vars_ = ["(var %s)" % var(k) for k in range(m)]
    srcs, hs = rec["srcs"], rec["hs"]
    R = "mono-by {Δ = ε} {n = %d} {as = %s} {as' = %s} ⌜ %s ⌝ᵗ (%s-sub (σₗ (%s)) %s) (%s-sub (σₗ (%s)) %s) (%s)" % (
        m, "(%s)" % " ∷ ".join(srcs + ["[]"]), "(%s)" % " ∷ ".join(xs + ["[]"]), " ".join([tn(0)] + vars_),
        tn(0), " ∷ ".join(srcs + ["[]"]), " ".join(vars_), tn(0), " ∷ ".join(xs + ["[]"]), " ".join(vars_),
        " ∷ʳ ".join(hs + ["[]ʳ"]))
    es = ["e%d" % k for k in range(n)]
    def cast(k, dq):
        a_ = xs + es[:k]
        nxt = ["(w1 %s)" % x for x in a_] + ["(var vz)"]
        eq = "(trans (%s-sub (single e%d) %s) (%s-cong %s %s))" % (tn(k + 1), k, " ".join(nxt), tn(k + 1),
             " ".join("(subTm (single e%d) %s) %s" % (k, u_, v_) for u_, v_ in zip(nxt, a_ + ["e%d" % k])),
             " ".join(["(wk-cancel-tm e%d %s)" % (k, x) for x in a_] + ["refl"]))
        return "(⊢-cast (cong (λ Z → El (dpay %s %s Z)) %s) (⊢conv %s (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ e%d) done))))))" % (
            Jn, Dn, eq, dq, k)
    lines = ["%s {Γ}%s%s u dq nq =" % (hn, "".join(" " + a for a in args), " ih" if ihf is not None else ""),
             "  pay-σ (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R)))) done nq"]
    depth = 0
    cur = "dq"
    for k in range(n):
        lines.append("  ▷ λ { (e%d , (_ , (_ , ((de%d , dq%d) , (ne%d , nq%d))))) →" % (k, k, k + 1, k, k + 1))
        if k + 1 < n:
            lines.append("  pay-σ %s done nq%d" % (cast(k, "dq%d" % (k + 1)), k + 1))
        cur = cast(k, "dq%d" % (k + 1)) if k == n - 1 else cur
    # the body rows after the existentials
    prem = None; idrow = None
    t_ = 0; nqn = "nq%d" % n
    for t, e in enumerate(body):
        if e[0] in ("ty", "tm", "red"):
            lines.append("  pay-ρ %s done %s" % (cur, nqn))
            lines.append("  ▷ λ { (r%d , (_ , (_ , ((dr%d , dqb%d) , (nr%d , nqb%d))))) →" % (t, t, t, t, t))
            prem = (t, e); cur, nqn = "dqb%d" % t, "nqb%d" % t
        elif e[0] == "id":
            lines.append("  pay-σ %s done %s" % (cur, nqn))
            lines.append("  ▷ λ { (_ , (_ , (_ , ((did%d , dqb%d) , (nid%d , nqb%d))))) →" % (t, t, t, t))
            idrow = (t, e); cur, nqn = "dqb%d" % t, "nqb%d" % t
    # ── the Spec side
    f = fs[i]
    dz = _depth(rec["rc"].ex[0][1])
    srt = 0 if rec["rc"].ex[0][0] == "Ty" else 1
    unq = "unqTy" if srt == 0 else "unqTm"
    elq = "El-⌜Ty⌝" if srt == 0 else "El-⌜Tm⌝"
    tgt = al.body.expr(idrow[1][3], dict(val, X="c"))
    rhs = "(%s)" % " ".join([spec_name(h)] + [("E" if k == i else args[k]) for k in range(len(fs))])
    Qr = "quoteTy" if fam == "⟶ᵀ" else "quoteTm"
    eqU = "(%s-inj u %s (nf-≅ (%s-normal u) (%s-normal %s) (subst (λ z → c ≅ %s) eqE (idrefl-decᶜ did%d nid%d))))" % (
        Qr, rhs, Qr, Qr, rhs, _tokrep(tgt, "e0", "z"), idrow[0], idrow[0])
    if prem is not None:
        tp, e = prem
        ix = "%s %s" % (F["ix"], " ".join("(%s)" % al.body.expr(y, val) for y in e[1:]))
        # ★ the recursion is the CALLER's (`ih = decRed aᵢ`): the helper is not in decRed's mutual block
        ih = "(ih {E} (subst (λ z → ◇ ⊢ r%d ∷ IMu %s %s (%s)) eqE dr%d) nr%d)" % (
            tp, Jn, Dn, _tokrep(ix, "e0", "z"), tp, tp)
    else:
        # the premise is the existential `e1`, a code of the term reduction (`RedC`)
        dd = "(%s)" % ("j" if dz == 0 else ("(nsuc j)" if dz == 1 else "(nsuc (nsuc j))"))
        ih = "(decRed %s {E} (subst (λ z → ◇ ⊢ e1 ∷ IMu Redₘ.J ⟶F.DF (ix⟶ %s %s z)) eqE (⊢conv de1 El-⌜⟶⌝)) ne1)" % (
            args[i], dd, "f%d" % i)
    lines.append("  %s {Γ = Γ%s} (⊢conv de0 (credᵀ %s)) ne0" % (unq, " ∙" * dz, elq))
    lines.append("  ▷ λ { (E , eqE) →")
    lines.append("  subst (λ v → %s %s v) (sym %s) (%s %s) }%s" % (subjE, arr, eqU, ximap[(fam, h, i)], ih, " }" * (n + len(body))))
    lines.append("  where")
    lines.append("    %s : RTm ε" % " ".join(["j"] + ["f%d" % k for k in range(len(args))] + ["p", "c"]))
    lines.append("    j = dep Γ")
    for k, a in enumerate(args):
        lines.append("    f%d = %s" % (k, qf(fs[k], a)))
    lines.append("    p = %s" % rec["p_"])
    lines.append("    c = %s u" % Qr)
    lines.append("    R = %s" % R)
    return sig + lines + [""]

# ------------------------------------------------------------ F6: the computation rules, decoded
RCDHDR = """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedCompDecode where

------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- ★ PLAN-FAITHFUL F6 — the ⟶ / ⟶ᵀ COMPUTATION rules, decoded (`RedDecode`
-- dispatches to these).  A nested subject pattern is read level by level,
-- along the constructor's own steps (`gen_con`): the payload is carried
-- to the level's CASE, `case-any` + `pat-hit` force the scrutinee's head,
-- `is⟨H⟩` reads it back as the Spec constructor, and the payload is
-- transported to the next level.  At the last level the telescope is
-- reduced to its values (`R₁`), the existentials are unquoted (a motive's
-- Ford `IdC` is one more pattern, `Pw`/`Stk` premises are decoded), and
-- the rule's Ford is closed against its F3 agreement (`close`).
------------------------------------------------------------------------

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; pw?; pwBody; stkA?; stkC? )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; atᶜ; v₀; v₁; v₂; v₃; v₄; v₅; v₆; v₇; v₈; v₉; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Lib.PatDecode
open import DirectedHoTT.Lib.FinFam using ( FinI; ffz; ffs )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Unquote
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⌜Tm⌝; ⌜Ty⌝; El-⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2; w3 )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0 )
open import DirectedHoTT.Examples.Knot.Ren using ( wk )
open import DirectedHoTT.Examples.Knot.SubEnv
open import DirectedHoTT.Examples.Knot.GenHelpers
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.NestIx
open import DirectedHoTT.Examples.Knot.Pw
open import DirectedHoTT.Examples.Knot.Preds
open import DirectedHoTT.Examples.Knot.Red
open import DirectedHoTT.Examples.Knot.RedT
open import DirectedHoTT.Examples.Knot.OpAgree
open import DirectedHoTT.Examples.Knot.PwDecode using ( decPw )
open import DirectedHoTT.Examples.Knot.PredsDecode

private
  ⟶≡ : {Θ : Cx} {t u u' : RTm Θ} → u ≡ u' → t ⟶* u → t ⟶* u'
  ⟶≡ refl r = r

-- ★ a Ford closed: the rule's own reduct, the target read back
close : {Γ : Cx} {t u v : RTm Γ} → t ⟶ v → quoteTm u {ε} ≅ quoteTm v → t ⟶ u
close {u = u} {v} r e = subst (λ w → _ ⟶ w) (sym (quoteTm-inj u v (nf-≅ (quoteTm-normal u) (quoteTm-normal v) e))) r

closeᵀ : {Γ : Cx} {t u v : RTy Γ} → t ⟶ᵀ v → quoteTy u {ε} ≅ quoteTy v → t ⟶ᵀ u
closeᵀ {u = u} {v} r e = subst (λ w → _ ⟶ᵀ w) (sym (quoteTy-inj u v (nf-≅ (quoteTy-normal u) (quoteTy-normal v) e))) r

"""

def comp_name(fam, h, r): return "cd%s%s₍%d₎" % (fam, h, r)

def gen_comp_decs():
    L = [RCDHDR]
    for fam, TAB in (("⟶", RED_COMP), ("⟶ᵀ", REDT_COMP)):
        alts = red_alts(fam)
        for spat, h, k, shyps, red in TAB:
            r = alts[h][0] + k
            L += comp_dec(fam, h, r, DECREC[(fam, h)][r], spat, shyps, red)
    return L

def comp_dec(fam, h, r, rec, spat, shyps, red):
    import re as _re
    S = 1 if fam == "⟶" else 0
    QT = {0: "quoteTy", 1: "quoteTm"}
    Q = QT[S]
    arr, RT, close_ = ("⟶", "RTm", "close") if S else ("⟶ᵀ", "RTy", "closeᵀ")
    F = FAMS[fam]; Jn, Dn = F["J"], F["D"]
    al, rc, nc, csf, n, val, XP, tn = rec["al"], rec["rc"], rec["nc"], rec["csf"], rec["n"], rec["val"], rec["XP"], rec["tn"]
    fs, nest = rec["fs"], rec["nest"]
    Ln = len(nest)
    ex = rc.ex
    base = comp_name(fam, h, r)
    # ── positions: ('f', i) subject field i, ('r', m, i) pattern m's field i
    def fld(pos): return fs[pos[1]] if pos[0] == "f" else SIG[nest[pos[1]][1]][1][pos[2]]
    def svar(pos): return "a%d" % pos[1] if pos[0] == "f" else "x%dᵢ%d" % (pos[1], pos[2])
    def kname(pos): return "f%d" % pos[1] if pos[0] == "f" else "a%dᵢ%d" % (pos[1], pos[2])
    def vty(f):
        if f[0] == "nat": return "ℕ"
        if f[0] == "var": return "Var Γ"
        if f[0] == "cls": return "%s ε" % ("RTy" if f[1] == 0 else "RTm")
        return "%s (Γ%s)" % ("RTy" if f[1] == 0 else "RTm", " ∙" * f[2])
    def qf(f, e):
        if f[0] in ("rec", "cls"): return "(%s %s)" % (QT[f[1]], e)
        if f[0] == "nat": return "(quoteℕ %s)" % e
        return "(quoteVar %s)" % e
    def sp(H):
        hasrec = any(f[0] in ("rec", "cls") for f in SIG[H][1])
        return spec_name(H) + ("" if hasrec else " {Γ}")
    env = {}                                   # a scrutinised Spec variable → its pattern
    def resolve(v, ov):
        if v in ov: return ov[v]
        if v not in env: return v
        H, ch = env[v]
        return "(%s)" % " ".join([sp(H)] + [resolve(x, ov) for x in ch]) if ch else "(%s)" % sp(H)
    def subj(ov={}):
        return "(%s)" % " ".join([sp(h)] + [resolve("a%d" % i, ov) for i in range(len(fs))]) if fs else "(%s)" % sp(h)
    def entry(ov={}):
        PP = "unit"
        for i in reversed(range(len(fs))): PP = "(pair %s %s)" % (qf(fs[i], resolve("a%d" % i, ov)), PP)
        return csf[r][0]("(dep Γ)", PP, "(%s u)" % Q)
    def wl(xs): return "(%s)" % " ∷ ".join(xs + ["[]"])
    fvn = ["f%d" % i for i in range(len(fs))]
    AS = lambda m: ["a%dᵢ%d" % (m, i) for i in range(len(SIG[nest[m][1]][1]))]
    CW = lambda k: ["c", "p"] + ["q%d" % m for m in range(k)]
    at = lambda t, k: _re.sub(r"(?<![\w'])q(?![\w'])", "q%d" % k, _re.sub(r"(?<![\w'])c(?![\w'])", "cv%d" % k, t))
    def red_pos(p, k):
        if p == "J": return "done"
        if p == "X": return "(prj-tup {ws = %s} unit nth-z)" % wl(CW(k))
        if p[0] == "f":
            if k < 0: return "(prj-tup {ws = %s} unit %s)" % (wl(fvn), nth_expr(p[1]))
            return "(⟶*-trans (prj-mono %d (prj-tup {ws = %s} unit %s)) (prj-tup {ws = %s} unit %s))" % (
                p[1], wl(CW(k)), nth_expr(1), wl(fvn), nth_expr(p[1]))
        m, i = p[1], p[2]
        if m == k: return "(prj-tup {ws = %s} unit %s)" % (wl(AS(m)), nth_expr(i))
        return "(⟶*-trans (prj-mono %d (prj-tup {ws = %s} unit %s)) (prj-tup {ws = %s} unit %s))" % (
            i, wl(CW(k)), nth_expr(m + 2), wl(AS(m)), nth_expr(i))
    skey = lambda m: nest[m][0]
    pat = lambda m: "(k%s%s)" % (nest[m][1], "".join(" " + x for x in AS(m)))
    ngf = lambda m: "(atᵍ %d)" % nest_sort(rc, m)
    nhf = lambda m: "(atʰ %d)" % SIG[nest[m][1]][2]
    cv_lit = lambda k: "(pair c (pair p unit))" if k == 0 else "cv%d" % k
    def chain(steps, tgt):
        pr = steps[-1][2]
        for (t_, u_, p_) in reversed(steps[:-1]):
            pr = "(⟶*-trans {t = %s} {u = %s} {v = %s} %s %s)" % (t_, u_, tgt, p_, pr)
        return pr
    def walk(k):
        """the steps through levels 0 … k-1, landing at level k's CASE (or the values' telescope, k = Ln)"""
        steps, cur = [], csf[r][0]("j", "p", "c")
        for m in range(k):
            Pm = nc["Pn"](m)
            conv0 = "(pair c (pair p unit))" if m == 0 else at(nc["convoy_at"](m), m - 1)
            u1 = "%s.CASE j %s %s" % (Pm, pat(m), conv0)
            steps.append((cur, u1, "(%s.CASE-⟶ᵃ %s)" % (Pm, red_pos(skey(m), m - 1)))); cur = u1
            if m >= 1:
                u2 = "%s.CASE j %s cv%d" % (Pm, pat(m), m)
                pw = ["(prj-tup {ws = %s} unit %s)" % (wl(CW(m - 1)), nth_expr(t)) for t in range(len(CW(m - 1)))] + ["done"]
                steps.append((cur, u2, "(%s.CASE-⟶ᶜ (tup-mono {w = unit} (%s)))" % (Pm, " ∷ʳ ".join(pw + ["[]ʳ"])))); cur = u2
            if m + 1 < Ln:
                land = "%s.CASE j %s %s" % (nc["Pn"](m + 1), at(nc["scrut_at"](m + 1, nest[m + 1][0]), m), at(nc["convoy_at"](m + 1), m))
            else:
                land = "⌜ %s j q%d cv%d ⌝ᵗ" % (al.pfx, m, m)
            steps.append((cur, land, "(%s.case-β {j = j} {q = q%d} {c = cv%d} %s %s)" % (Pm, m, m, ngf(m), nhf(m)))); cur = land
        return steps, cur
    def where_block(k, extra=(), ncv=None):
        ncv = k if ncv is None else ncv
        names = ["j"] + fvn + [a for m in range(k) for a in AS(m)] + ["p", "c"] + ["q%d" % m for m in range(k)] + ["cv%d" % m for m in range(ncv)]
        L = ["  where", "    %s : RTm ε" % " ".join(names), "    j = dep Γ"]
        L += ["    f%d = %s" % (i, qf(fs[i], resolve("a%d" % i, {}))) for i in range(len(fs))]
        for m in range(k):
            for i, a in enumerate(AS(m)): L.append("    %s = %s" % (a, qf(fld(("r", m, i)), resolve("x%dᵢ%d" % (m, i), {}))))
        L.append("    p = %s" % ("".join("(pair %s " % x for x in fvn) + "unit" + ")" * len(fvn)))
        L.append("    c = %s u" % Q)
        for m in range(k): L.append("    q%d = %s" % (m, "".join("(pair %s " % x for x in AS(m)) + "unit" + ")" * len(AS(m))))
        for m in range(ncv): L.append("    cv%d = %s" % (m, "".join("(pair %s " % x for x in CW(m)) + "unit" + ")" * len(CW(m))))
        return L + list(extra)
    live = [("a%d" % i, vty(f)) for i, f in enumerate(fs)]
    def sig_(hn):
        return ["%s : {Γ : Cx}%s (u : %s Γ) {q : RTm ε} →" % (hn, "".join(" (%s : %s)" % vt for vt in live), RT),
                "  ◇ ⊢ q ∷ El (dpay %s %s %s) → IsNormal q → %s %s u" % (Jn, Dn, entry(), subj(), arr),
                "%s {Γ}%s u {q} dq nq =" % (hn, "".join(" " + v for v, _ in live))]
    out, blocks = [], []
    # ── the levels (emitted deepest first: a helper calls the next level's)
    for k in range(Ln):
        hn = base if k == 0 else "%sᴸ%d" % (base, k)
        nxt = "%sᴸ%d" % (base, k + 1)
        out += sig_(hn)
        pos = nest[k][0]; v = svar(pos); H = nest[k][1]
        srt = fld(pos)[1]; Ty_ = "Ty" if srt == 0 else "Tm"
        steps, cur = walk(k)
        Pk = nc["Pn"](k)
        conv = "(pair c (pair p unit))" if k == 0 else at(nc["convoy_at"](k), k - 1)
        u1 = "%s.CASE j %s %s" % (Pk, kname(pos), conv)
        steps.append((cur, u1, "(%s.CASE-⟶ᵃ %s)" % (Pk, red_pos(pos, k - 1))))
        if k >= 1:
            u2 = "%s.CASE j %s cv%d" % (Pk, kname(pos), k)
            pw = ["(prj-tup {ws = %s} unit %s)" % (wl(CW(k - 1)), nth_expr(t)) for t in range(len(CW(k - 1)))] + ["done"]
            steps.append((u1, u2, "(%s.CASE-⟶ᶜ (tup-mono {w = unit} (%s)))" % (Pk, " ∷ʳ ".join(pw + ["[]ʳ"]))))
            u1 = u2
        xv = ["x%dᵢ%d" % (k, i) for i in range(len(SIG[H][1]))]
        ispat = "eqv"
        for x_ in reversed(xv): ispat = "(%s , %s)" % (x_, ispat)
        motE = entry({v: "z"}); motS = subj({v: "z"})
        live_n = [(a, t) for a, t in live if a != v] + [(x_, vty(f)) for x_, f in zip(xv, SIG[H][1])]
        out += ["  pat-hit %d %d (hd%s %s) dq₃ nq" % (nest_sort(rc, k), SIG[H][2], Ty_, v),
                "  ▷ λ e → is%s %s e" % (H, v),
                "  ▷ λ { %s → subst (λ z → %s %s u) (sym eqv) (%s%s u (subst (λ z → ◇ ⊢ q ∷ El (dpay %s %s %s)) eqv dq) nq) }" % (
                    ispat, motS, arr, nxt, "".join(" " + a for a, _ in live_n), Jn, Dn, motE)]
        cvk = cv_lit(k)
        out += where_block(k, [
            "    dq₁ = ⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ %s)))" % chain(steps, u1),
            "    dq₂ = subst (λ z → ◇ ⊢ q ∷ El (dpay %s %s (%s.CASE j z %s))) (quote-hd%s %s) dq₁" % (Jn, Dn, Pk, cvk, Ty_, v),
            "    dq₃ = ⊢conv dq₂ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (%s.case-any {j = j} {q = pf%s %s} {c = %s} %s (nh%s %s)))))" % (
                Pk, Ty_, v, cvk, ngf(k), Ty_, v)], ncv=k + 1 if k >= 1 else 0)
        out.append("")
        blocks.append(out); out = []
        env[v] = (H, xv)
        live = live_n
    # ── the last level: the values, the existentials, the Ford
    hn = base if Ln == 0 else "%sᴸ%d" % (base, Ln)
    out += sig_(hn)
    xs = [{"J": "j", "X": "c"}[p] if isinstance(p, str) else kname(p) for p in XP]
    m_ = len(XP)
    vars_ = ["(var %s)" % var(t) for t in range(m_)]
    srcs, hs = rec["srcs"], rec["hs"]
    tgt = "⌜ %s ⌝ᵗ" % " ".join([tn(0)] + xs)
    R1 = "mono-by {Δ = ε} {n = %d} {as = %s} {as' = %s} ⌜ %s ⌝ᵗ (%s-sub (σₗ %s) %s) (%s-sub (σₗ %s) %s) (%s)" % (
        m_, wl(srcs), wl(xs), " ".join([tn(0)] + vars_), tn(0), wl(srcs), " ".join(vars_), tn(0), wl(xs), " ".join(vars_),
        " ∷ʳ ".join(hs + ["[]ʳ"]))
    steps, cur = walk(Ln)
    steps.append((cur, tgt, "R₁"))
    es = ["e%d" % t for t in range(n)]
    def cast(k, dq):
        a_ = xs + es[:k]
        nx = ["(w1 %s)" % x for x in a_] + ["(var vz)"]
        eq = "(trans (%s-sub (single e%d) %s) (%s-cong %s %s))" % (tn(k + 1), k, " ".join(nx), tn(k + 1),
             " ".join("(subTm (single e%d) %s) %s" % (k, u_, v_) for u_, v_ in zip(nx, a_ + ["e%d" % k])),
             " ".join(["(wk-cancel-tm e%d %s)" % (k, x) for x in a_] + ["refl"]))
        return "(⊢-cast (cong (λ Z → El (dpay %s %s Z)) %s) (⊢conv %s (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ e%d) done))))))" % (
            Jn, Dn, eq, dq, k)
    body = ["  pay-σ (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R₀)))) done nq"]
    closers = 0
    for k in range(n):
        body.append("  ▷ λ { (e%d , (_ , (_ , ((de%d , dq%d) , (ne%d , nq%d))))) →" % (k, k, k + 1, k, k + 1))
        body.append("  pay-σ %s done nq%d" % (cast(k, "dq%d" % (k + 1)), k + 1))
        closers += 1
    body.append("  ▷ λ { (_ , (_ , (_ , ((dF , _) , (nF , _))))) →"); closers += 1
    # ── the Spec side
    # e_k's current Knot text, as the equations are pushed in
    def specx(a, ov):
        """an existential code argument (Knot) → its Spec term"""
        if a == ("v0",): return "(var vz)"
        if a[0] == "e": return "E%d" % a[1]
        if a[0] == "k": return "(%s)" % " ".join([sp(a[1])] + [specx(b, ov) for b in a[2:]])
        if a[0] in ("f", "r"): return resolve(svar(a), ov)
        raise ValueError(a)
    ov = {}
    # 1. unquote the term/type existentials
    for k in range(n):
        c_ = ex[k]
        if c_[0] in ("Tm", "Ty"):
            d = _depth(c_[1])
            body.append("  %s {Γ = Γ%s} (⊢conv de%d (credᵀ El-⌜%s⌝)) ne%d" % ("unqTm" if c_[0] == "Tm" else "unqTy", " ∙" * d, k, c_[0], k))
            body.append("  ▷ λ { (E%d , eqE%d) →" % (k, k)); closers += 1
    QE = lambda k: "(%s E%d)" % ("quoteTm" if ex[k][0] == "Tm" else "quoteTy", k)
    def subst_es(ty, proof, extra=()):
        """`proof : ty` (with e_k) ↦ the same at `quote E_k` (and the PwC bodies)"""
        done_ = {}
        for k in range(n):
            if ex[k][0] not in ("Tm", "Ty"): continue
            en = "e%d" % k
            if not _re.search(r"(?<![\w'ᵢ])%s(?![\w'ᵢ₀-₉])" % en, ty): continue
            mot = ty
            for k2, rep in done_.items(): mot = _tokrep(mot, "e%d" % k2, rep)
            mot = _tokrep(mot, en, "z")
            proof = "(subst (λ z → %s) eqE%d %s)" % (mot, k, proof)
            done_[k] = QE(k)
        for (k, eqn, rep) in extra:              # E_k ≡ rep (a Spec equation, from a premise)
            en = "e%d" % k
            if not _re.search(r"(?<![\w'ᵢ])%s(?![\w'ᵢ₀-₉])" % en, ty): continue
            mot = ty
            for k2, rp in done_.items(): mot = _tokrep(mot, "e%d" % k2, "(%s z)" % ("quoteTm" if ex[k][0] == "Tm" else "quoteTy") if k2 == k else rp)
            proof = "(subst (λ z → %s) %s %s)" % (mot, eqn, proof)
            done_[k] = "(%s %s)" % ("quoteTm" if ex[k][0] == "Tm" else "quoteTy", rep)
        return proof
    def kexpr(a): return al.body.expr(a, val)
    def dexpr(d): return "j" if d == "J" else nsucs(_depth(d), "j")
    def ctxd(d): return "Γ" + " ∙" * _depth(d)
    # 2. the motive Fords (IdC): one more pattern
    eqM = []
    for k in range(n):
        c_ = ex[k]
        if c_[0] != "IdC": continue
        lhs_pos, rhs = c_[2], c_[3]
        ty = "%s ≅ %s" % (kexpr(lhs_pos), kexpr(rhs))
        srt_ = c_[1][0]
        qi, qn = ("quoteTm-inj", "quoteTm-normal") if srt_ == "Tm" else ("quoteTy-inj", "quoteTy-normal")
        L_ = resolve(svar(lhs_pos), ov); R_ = specx(rhs, ov)
        g_ = ctxd(c_[1][1])
        body.append("  %s %s %s (nf-≅ (%s {Γ = %s} %s) (%s {Γ = %s} %s) %s)" % (qi, L_, R_, qn, g_, L_, qn, g_, R_, subst_es(ty, "(idrefl-decᶜ de%d ne%d)" % (k, k))))
        body.append("  ▷ λ eqM%d →" % k)
        eqM.append((svar(lhs_pos), L_, "eqM%d" % k))
        ov[svar(lhs_pos)] = R_
    # 3. the premises
    prem, pweqs = [], []
    for k in range(n):
        c_ = ex[k]
        if c_[0] == "Pred":
            X_ = specx(c_[3], ov)
            ty = "◇ ⊢ e%d ∷ K%s %s %s" % (k, c_[1], dexpr(c_[2]), kexpr(c_[3]))
            body.append("  dec%s {Γ = %s} %s %s ne%d" % (c_[1], ctxd(c_[2]), X_,
                        subst_es(ty, "(⊢conv de%d El-⌜%s⌝)" % (k, c_[1])), k))
            body.append("  ▷ λ pr%d →" % k)
            prem.append("pr%d" % k)
        elif c_[0] == "PwC":
            C_ = specx(c_[2], ov); B_ = specx(c_[3], ov)
            ty = "◇ ⊢ e%d ∷ KPw %s %s %s" % (k, dexpr(c_[1]), kexpr(c_[2]), kexpr(c_[3]))
            body.append("  decPw {Γ = %s} %s {%s} %s ne%d" % (ctxd(c_[1]), C_, B_, subst_es(ty, "(⊢conv de%d El-⌜Pw⌝)" % k), k))
            body.append("  ▷ λ { (pr%d , eqP%d) →" % (k, k)); closers += 1
            prem.append("pr%d" % k)
            assert c_[3][0] == "e"
            pweqs.append((c_[3][1], "eqP%d" % k, "(pwBody %s)" % C_))
        elif c_[0] not in ("Tm", "Ty", "IdC"):
            raise ValueError(("an existential the decoder cannot read", fam, h, c_))
    # 4. the Spec rule, its names mapped: constructor hypotheses ↔ the rule's hypothesis typings
    hy = [x for x in rec["hyps"] if x != "j"]
    assert len(hy) == len(shyps), (spat, hy, shyps)
    nm = {}
    for hname, st in zip(hy, shyps):
        mm = _re.match(r"^\(⊢quote(?:Tm|Ty|ℕ) ([^\s()]+)\)$", st)
        if not mm: continue
        if hname.startswith("f"): e_ = resolve("a%s" % hname[1:], ov)
        elif hname.startswith("e"): e_ = "E%s" % hname[1:]
        else:
            mi = _re.match(r"a(\d+)ᵢ(\d+)$", hname); e_ = resolve("x%sᵢ%s" % mi.groups(), ov)
        nm[mm.group(1)] = e_
    toks = hidΓ(spat).split()
    args, pq = [], list(prem)
    for t in toks[1:]:
        imp = t.startswith("{")
        b = t.strip("{}")
        if b == "_": args.append(t); continue
        if b in nm: args.append("{%s}" % nm[b] if imp else nm[b])
        else: args.append(pq.pop(0))
    assert not pq, (spat, pq)
    rule = "(%s)" % " ".join([toks[0]] + args) if args else toks[0]
    def ren(text):
        if not nm: return text
        rx = _re.compile(r"(?<![\w'ᵢ₀-₉])(%s)(?![\w'ᵢ₀-₉])" % "|".join(_re.escape(x) for x in sorted(nm, key=len, reverse=True)))
        return rx.sub(lambda mo: nm[mo.group(1)], text)
    ford = rec["ford"]
    fty = "c ≅ %s" % al.body.expr(ford[3], dict(val, X="c"))
    fd = subst_es(fty, "(idrefl-decᶜ dF nF)", extra=pweqs)
    if red: fd = "(ctrn %s (⟶*→≅ %s))" % (fd, ren(red))
    res = "(%s %s %s)" % (close_, rule, fd)
    for (v_, L_, eq_) in reversed(eqM):
        o2 = dict(ov); o2[v_] = "z"
        res = "(subst (λ z → %s %s u) (sym %s) %s)" % (subj(o2), arr, eq_, res)
    body.append("  %s%s" % (res, " }" * closers))
    out += body
    out += where_block(Ln, ["    R₁ = %s" % R1, "    R₀ : %s ⟶* %s" % (csf[r][0]("j", "p", "c"), tgt),
                            "    R₀ = %s" % chain(steps, tgt)])
    out.append("")
    for bl in reversed(blocks): out += bl
    return out

# ------------------------------------------------------------ F6: the typing judgements, decoded
JDHDR = """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MODNAME where

------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- ★ PLAN-FAITHFUL F6 — the TYPING rows, decoded (`JudgeDecode` dispatches
-- to these).  Each row is decoded along its own constructor's state
-- (`gen_con`): the telescope reduced to its values, the payload peeled,
-- the existentials unquoted, each premise decoded by the induction
-- hypothesis at its Spec index (the Knot index reduced to it by the F3
-- agreements), the Fords closed by `nf-≅` + quote injectivity.  A row
-- that cases on the type (`⊢lam`'s Π, …) reads the head back first.
-- A premise is a strict subterm of the payload: its bound is `<ˡ`/`<ʳ`.
------------------------------------------------------------------------

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( NoNatC; nonatc-ren; occ-ren-tm; avoids-wk )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity using ( sz )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; atᶜ; v₀; v₁; v₂; v₃; v₄; v₅; v₆; v₇; v₈; v₉; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Lib.PatDecode
open import DirectedHoTT.Lib.Size using ( _<_; <ˡ; <ʳ )
open import DirectedHoTT.Lib.SynUnq using ( nat-unq )
open import DirectedHoTT.Lib.FinFam using ( FinI; ffz; ffs )
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Unquote
open import DirectedHoTT.Examples.Knot.JudgeIx
open import DirectedHoTT.Examples.Knot.JudgeCase
open import DirectedHoTT.Examples.Knot.Judge using ( D⊢ )
open import DirectedHoTT.Examples.Knot.JudgeConv using ( ⌜∋⌝; El-⌜∋⌝ )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0 )
open import DirectedHoTT.Examples.Knot.Ren using ( wk )
open import DirectedHoTT.Examples.Knot.SubEnv
open import DirectedHoTT.Examples.Knot.GenHelpers
open import DirectedHoTT.Examples.Knot.JudgeRowsGen
open import DirectedHoTT.Examples.Knot.Preds
open import DirectedHoTT.Examples.Knot.OpAgree
open import DirectedHoTT.Examples.Knot.PredsDecode
open import DirectedHoTT.Examples.Knot.LookupDecode using ( decLk )
open import DirectedHoTT.Examples.Knot.JudgeDecodeBase

"""

JTYCTOR = {"base": "ty-base", "U": "ty-U", "Pi": "ty-Π", "Sg": "ty-Σ", "El": "ty-El", "Hom": "ty-Hom", "Unit": "ty-Unit",
           "Nat": "ty-Nat", "Id": "ty-Id", "IMu": "ty-IMu", "Desc": "ty-Desc", "DIh": "ty-DIh", "Fin": "ty-Fin"}
# explicit-argument overrides: D<t> the t-th premise row (body order), P<k> the k-th existential's proof
JARGS = {("⊢", "var", 0): "P0", ("⊢", "ap", 0): "D0 P1 D1 D2 D3 D4 D5"}

def jdec_name(fam, h, r): return "jd%s%s₍%d₎" % ("ᵀ" if fam == "⊢ty" else "", h, r)

def judge_dec(fam, h, r, rec):
    import re as _re
    S = 0 if fam == "⊢ty" else 1
    al, rc, csf, n, val, XP, tn = rec["al"], rec["rc"], rec["csf"], rec["n"], rec["val"], rec["XP"], rec["tn"]
    fs, body, ex, case = rec["fs"], rec["body"], rc.ex, rec["case"]
    ford = rec["ford"]
    base = jdec_name(fam, h, r)
    QT = {0: "quoteTy", 1: "quoteTm"}
    def vty(f):
        if f[0] == "nat": return "ℕ"
        if f[0] == "var": return "Var ⌊ Γ ⌋"
        if f[0] == "cls": return "%s ε" % ("RTy" if f[1] == 0 else "RTm")
        return "%s (⌊ Γ ⌋%s)" % ("RTy" if f[1] == 0 else "RTm", " ∙" * f[2])
    def qf(f, e):
        if f[0] in ("rec", "cls"): return "(%s %s)" % (QT[f[1]], e)
        if f[0] == "nat": return "(quoteℕ %s)" % e
        return "(quoteVar %s)" % e
    def sp(H):
        hasrec = any(f[0] in ("rec", "cls") for f in SIG[H][1])
        return spec_name(H) + ("" if hasrec else " {⌊ Γ ⌋}")
    fvars = ["a%d" % i for i in range(len(fs))]
    subj = "(%s)" % " ".join([sp(h)] + fvars) if fs else "(%s)" % sp(h)
    Avar = ["A"]                                  # the target type, resolved by a case
    def PPs():
        t = "unit"
        for i in reversed(range(len(fs))): t = "(pair %s %s)" % (qf(fs[i], fvars[i]), t)
        return t
    def Cs(A_):
        return "(pair (quoteCtx Γ) %s)" % ("unit" if S == 0 else "(quoteTy %s)" % A_)
    def entry(A_): return csf[r][0]("(dep ⌊ Γ ⌋)", PPs(), Cs(A_))
    def concl(A_): return ("Γ ⊢ty %s" % subj) if S == 0 else ("Γ ⊢ %s ∷ %s" % (subj, A_))
    def wl(xs): return "(%s)" % " ∷ ".join(xs + ["[]"])
    fvn = ["f%d" % i for i in range(len(fs))]
    binds = "".join(" (%s : %s)" % (a, vty(f)) for a, f in zip(fvars, fs))
    def sig_(hn, qbinds, A_):
        Ab = " (A : RTy ⌊ Γ ⌋)" if (S == 1 and A_ == "A") else ""
        return ["%s : {N : ℕ} → IHTy N → IHTm N → (Γ : Ctx)%s%s%s {w : RTm ε} → sz w < N →" % (hn, binds, qbinds, Ab),
                "  ◇ ⊢ w ∷ El (dpay JT D⊢ %s) → IsNormal w → %s" % (entry(A_), concl(A_)),
                "%s ihTy ihTm Γ%s%s%s {w} hq dq nq =" % (hn, "".join(" " + a for a in fvars),
                    "".join(" " + x for x in _re.findall(r"\((Q\d+) :", qbinds)), " A" if Ab else "")]
    out = []
    # ── a case on the type: read its head back, then the row at the resolved type
    qn = []
    if case:
        cf = SIG[case][1]
        qn = ["Q%d" % i for i in range(len(cf))]
        Ares = "(%s)" % " ".join([sp(case)] + qn) if qn else "(%s)" % sp(case)
        qbinds = "".join(" (%s : %s)" % (x, vty(f)) for x, f in zip(qn, cf))
        hn1 = base + "ᴸ"
        L0 = sig_(base, "", "A")
        PN = "P" + al.pfx
        u0 = csf[r][0]("j", "p", "c")
        u1 = "%s.CASE j X0 (pair (fst c) p)" % PN
        u2 = "%s.CASE j X0 c'" % PN
        chain0 = "(⟶*-trans {t = %s} {u = %s} {v = %s} (%s.CASE-⟶ᵃ (step (βsnd g X0) done)) (%s.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X0) done))))" % (
            u0, u1, u2, PN, PN)
        ispat = "eqv"
        for x_ in reversed(qn): ispat = "(%s , %s)" % (x_, ispat)
        L0 += ["  pat-hit 0 %d (hdTy A) dq₃ nq" % SIG[case][2],
               "  ▷ λ e → is%s A e" % case,
               "  ▷ λ { %s → subst (λ z → Γ ⊢ %s ∷ z) (sym eqv) (%s ihTy ihTm Γ%s%s hq (subst (λ z → ◇ ⊢ w ∷ El (dpay JT D⊢ %s)) eqv dq) nq) }" % (
                   ispat, subj, hn1, "".join(" " + a for a in fvars), "".join(" " + x for x in qn), entry("z")),
               "  where",
               "    %s : RTm ε" % " ".join(["j", "g"] + fvn + ["X0", "p", "c", "c'"]),
               "    j = dep ⌊ Γ ⌋", "    g = quoteCtx Γ"]
        L0 += ["    f%d = %s" % (i, qf(fs[i], fvars[i])) for i in range(len(fs))]
        L0 += ["    X0 = quoteTy A", "    p = %s" % PPs().replace("(quoteTm ", "(quoteTm ") , "    c = pair g X0", "    c' = pair g p",
               "    dq₁ = ⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ %s)))" % chain0,
               "    dq₂ = subst (λ z → ◇ ⊢ w ∷ El (dpay JT D⊢ (%s.CASE j z c'))) (quote-hdTy A) dq₁" % PN,
               "    dq₃ = ⊢conv dq₂ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (%s.case-any {j = j} {q = pfTy A} {c = c'} (atᵍ 0) (nhTy A)))))" % PN, ""]
        # the p line above must use the where-names
        L0 = [l if not l.startswith("    p = ") else "    p = %s" % ("".join("(pair %s " % x for x in fvn) + "unit" + ")" * len(fvn)) for l in L0]
        A_ = Ares
        out_pre = L0
        hn = hn1
        L1 = sig_(hn, qbinds, A_)
    else:
        A_ = "A"
        out_pre = []
        hn = base
        L1 = sig_(hn, "", "A")
    # ── the row at its values
    XN = {"J": "j", "G": "g", "X": "X0"}
    xs = [XN[p] if isinstance(p, str) else ("f%d" % p[1] if p[0] == "f" else "q%d" % p[1]) for p in XP]
    m_ = len(XP)
    vars_ = ["(var %s)" % var(t) for t in range(m_)]
    srcs = rec["srcs"]
    if case: hs = rec["hs"]
    else:
        hs = []
        for p, h0 in zip(XP, rec["hs"]):
            if p == "G": hs.append("(prj-tup {ws = g ∷ []} %s nth-z)" % ("X0" if S else "unit"))
            elif p == "X": hs.append("(step (βsnd g X0) done)")
            else: hs.append(h0)
    tgt = "⌜ %s ⌝ᵗ" % " ".join([tn(0)] + xs)
    R1 = "mono-by {Δ = ε} {n = %d} {as = %s} {as' = %s} ⌜ %s ⌝ᵗ (%s-sub (σₗ %s) %s) (%s-sub (σₗ %s) %s) (%s)" % (
        m_, wl(srcs), wl(xs), " ".join([tn(0)] + vars_), tn(0), wl(srcs), " ".join(vars_), tn(0), wl(xs), " ".join(vars_),
        " ∷ʳ ".join(hs + ["[]ʳ"]))
    es = ["e%d" % t for t in range(n)]
    def cast(k, dq):
        a_ = xs + es[:k]
        nx = ["(w1 %s)" % x for x in a_] + ["(var vz)"]
        eq = "(trans (%s-sub (single e%d) %s) (%s-cong %s %s))" % (tn(k + 1), k, " ".join(nx), tn(k + 1),
             " ".join("(subTm (single e%d) %s) %s" % (k, u_, v_) for u_, v_ in zip(nx, a_ + ["e%d" % k])),
             " ".join(["(wk-cancel-tm e%d %s)" % (k, x) for x in a_] + ["refl"]))
        return "(⊢-cast (cong (λ Z → El (dpay JT D⊢ Z)) %s) (⊢conv %s (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ e%d) done))))))" % (eq, dq, k)
    kval = dict(val, X="X0")
    kexpr = lambda a: al.body.expr(a, kval)
    # ── Spec side of a Knot expression, and its F3 agreement (Knot ⟶* quote Spec)
    ov = {}
    def sx(a):
        if a == "X": return A_
        if a == ("v0",): return "(var vz)"
        if a == ("nzero",): return "zero"
        if isinstance(a, tuple) and a[0] == "nsuc": return "(suc %s)" % sx(a[1])
        if a[0] == "f": return ov.get("a%d" % a[1], "a%d" % a[1])
        if a[0] == "q": return "Q%d" % a[1]
        if a[0] == "e": return "E%d" % a[1]
        if a[0] == "k": return "(%s)" % " ".join([spec_name(a[1])] + [sx(b) for b in a[2:]]) if len(a) > 2 else spec_name(a[1])
        if a[0] == "sub0": return "(%s (single %s) %s)" % ("subTy" if a[1] == 0 else "subTm", sx(a[4]), sx(a[3]))
        if a[0] == "wk": return "(%s vs %s)" % ("renTy" if a[1] == 0 else "renTm", sx(a[3]))
        if a[0] == "DF": return "(DescF %s)" % sx(a[2])
        if a[0] == "nrsK": return "(subTy nrs %s)" % sx(a[2])
        if a[0] == "pairSK": return "(subTy pairS %s)" % sx(a[2])
        if a[0] == "fsucSK": return "(subTy fsucS %s)" % sx(a[2])
        if a[0] == "MethTyK": return "(MethTy %s %s %s)" % (sx(a[2]), sx(a[3]), sx(a[4]))
        if a[0] == "iinstK": return "(iinst %s %s %s)" % (sx(a[2]), sx(a[3]), sx(a[4]))
        raise ValueError(("sx", a))
    def ag(a):
        if isinstance(a, str) or a[0] in ("f", "q", "e", "v0", "nzero", "nsuc"): return None
        if a[0] == "k":
            prs = []
            for i, b in enumerate(a[2:]):
                g_ = ag(b)
                if g_: prs.append("(node-%d %s)" % (i + 1, g_))
            if not prs: return None
            t = prs[-1]
            for p_ in reversed(prs[:-1]): t = "(⟶*-trans %s %s)" % (p_, t)
            return t
        if a[0] == "sub0":
            assert not ag(a[3]) and not ag(a[4]), a
            return "(sub0-agree-%s %s %s)" % ("ty" if a[1] == 0 else "tm", sx(a[3]), sx(a[4]))
        if a[0] == "wk":
            assert not ag(a[3]), a
            return "(wk-agree-%s %s)" % ("ty" if a[1] == 0 else "tm", sx(a[3]))
        if a[0] == "DF": return "(DF-agree %s)" % sx(a[2])
        if a[0] == "nrsK": return "(nrs-agree %s)" % sx(a[2])
        if a[0] == "pairSK": return "(pairS-agree %s)" % sx(a[2])
        if a[0] == "fsucSK": return "(fsucS-agree %s)" % sx(a[2])
        if a[0] == "MethTyK": return "(MethTy-agree %s %s %s)" % (sx(a[2]), sx(a[3]), sx(a[4]))
        if a[0] == "iinstK": return "(iinst-agree %s %s %s)" % (sx(a[2]), sx(a[3]), sx(a[4]))
        raise ValueError(("ag", a))
    def sctx(g):
        if g == "G": return "Γ"
        if g[0] == "cext": return "(%s ▹ %s)" % (sctx(g[1]), sx(g[2]))
        if g[0] == "mc": return "(motCtx %s %s %s)" % (sctx(g[2]), sx(g[3]), sx(g[4]))
        raise ValueError(g)
    def agctx(g):
        if g == "G": return None
        if g[0] == "cext":
            prs = []
            if agctx(g[1]): prs.append("(node-1 %s)" % agctx(g[1]))
            if ag(g[2]): prs.append("(node-2 %s)" % ag(g[2]))
            if not prs: return None
            return prs[0] if len(prs) == 1 else "(⟶*-trans %s %s)" % tuple(prs)
        if g[0] == "mc": return "(mc-agree %s %s %s)" % (sctx(g[2]), sx(g[3]), sx(g[4]))
        raise ValueError(g)
    def ctxd(d): return "⌊ Γ ⌋" + " ∙" * _depth(d)
    # ── peel: the existentials, then the body rows
    closers = 0
    hcur = "hq"
    lines = []
    peels = []                                      # what each peel binds
    first = True
    cur_dq, cur_nq = "dq", "nq"
    items = [("ex", k) for k in range(n)] + [("body", t) for t in range(len(body))]
    for idx, (kind, k) in enumerate(items):
        if kind == "ex":
            src = "(⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R₀))))" if idx == 0 else cast(k - 1, cur_dq)
            lines.append("  pay-σ %s done %s" % (src, cur_nq))
            lines.append("  ▷ λ { (e%d , (b%d , (eq%d , ((de%d , dq%d) , (ne%d , nq%d))))) →" % (k, idx, idx, k, idx + 1, k, idx + 1))
            peels.append(("e", k, "(<ˡ eq%d %s)" % (idx, hcur)))
        else:
            e = body[k]
            if idx == 0: src = "(⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R₀))))"
            elif items[idx - 1][0] == "ex": src = cast(items[idx - 1][1], cur_dq)
            else: src = cur_dq
            if e[0] in ("ty", "tm"):
                lines.append("  pay-ρ %s done %s" % (src, cur_nq))
                lines.append("  ▷ λ { (r%d , (b%d , (eq%d , ((dr%d , dq%d) , (nr%d , nq%d))))) →" % (k, idx, idx, k, idx + 1, k, idx + 1))
                peels.append(("r", k, "(<ˡ eq%d %s)" % (idx, hcur)))
            elif e[0] == "id":
                lines.append("  pay-σ %s done %s" % (src, cur_nq))
                lines.append("  ▷ λ { (_ , (b%d , (eq%d , ((dF , dq%d) , (nF , nq%d))))) →" % (idx, idx, idx + 1, idx + 1))
            else: raise ValueError(e)
        closers += 1
        hcur = "(<ʳ eq%d %s)" % (idx, hcur)
        cur_dq, cur_nq = "dq%d" % (idx + 1), "nq%d" % (idx + 1)
    if not items:
        lines.append("  pay-ι (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ R₀)))) done nq")
        lines.append("  ▷ λ _ →")
    # ── the Spec side
    pushed = []                                    # (k, rep): e_k is now `rep` (a quote of a Spec term)
    def subst_es(ty, proof, extra=()):
        done_ = {}
        for k in range(n):
            c_ = ex[k]
            if c_[0] not in ("Tm", "Ty", "Nat"): continue
            en = "e%d" % k
            if not _re.search(r"(?<![\w'ᵢ])%s(?![\w'ᵢ₀-₉])" % en, ty): continue
            mot = ty
            for k2, rep in done_.items(): mot = _tokrep(mot, "e%d" % k2, rep)
            mot = _tokrep(mot, en, "z")
            proof = "(subst (λ z → %s) eqE%d %s)" % (mot, k, proof)
            done_[k] = {"Tm": "(quoteTm E%d)", "Ty": "(quoteTy E%d)", "Nat": "(quoteℕ E%d)"}[c_[0]] % k
        return proof
    for k in range(n):
        c_ = ex[k]
        if c_[0] in ("Tm", "Ty"):
            lines.append("  %s {Γ = %s} (⊢conv de%d (credᵀ El-⌜%s⌝)) ne%d" % ("unqTm" if c_[0] == "Tm" else "unqTy", ctxd(c_[1]), k, c_[0], k))
            lines.append("  ▷ λ { (E%d , eqE%d) →" % (k, k)); closers += 1
        elif c_[0] == "Nat":
            lines.append("  nat-unq de%d ne%d" % (k, k))
            lines.append("  ▷ λ { (E%d , eqN%d) →" % (k, k)); closers += 1
            lines.append("  trans eqN%d (num-quoteℕ E%d)" % (k, k))
            lines.append("  ▷ λ eqE%d →" % k)
    eqM = []
    for k in range(n):
        c_ = ex[k]
        if c_[0] != "IdC": continue
        lhs, rhs = c_[2], c_[3]
        ty = "%s ≅ %s" % (kexpr(lhs), kexpr(rhs))
        pr = subst_es(ty, "(idrefl-decᶜ de%d ne%d)" % (k, k))
        if ag(rhs): pr = "(ctrn %s (⟶*→≅ %s))" % (pr, ag(rhs))
        g_ = ctxd(c_[1][1])
        L_ = sx(lhs); R_ = sx(rhs)
        lines.append("  quoteTm-inj %s %s (nf-≅ (quoteTm-normal {Γ = %s} %s) (quoteTm-normal {Γ = %s} %s) %s)" % (L_, R_, g_, L_, g_, R_, pr))
        lines.append("  ▷ λ eqM%d →" % k)
        eqM.append(("a%d" % lhs[1], "eqM%d" % k))
        ov["a%d" % lhs[1]] = R_
    prem = {}
    for k in range(n):
        c_ = ex[k]
        if c_[0] == "Pred":
            ty = "◇ ⊢ e%d ∷ K%s %s %s" % (k, c_[1], dep(c_[2], "j"), kexpr(c_[3]))
            lines.append("  dec%s {Γ = %s} %s %s ne%d" % (c_[1], ctxd(c_[2]), sx(c_[3]), subst_es(ty, "(⊢conv de%d El-⌜%s⌝)" % (k, c_[1])), k))
            lines.append("  ▷ λ P%d →" % k)
        elif c_[0] == "NiC":
            lines.append("  decLk {Γ = Γ} %s {A = %s} (⊢conv de%d (credᵀ El-⌜∋⌝)) ne%d" % (sx(c_[3]), A_, k, k))
            lines.append("  ▷ λ P%d →" % k)
        elif c_[0] not in ("Tm", "Ty", "Nat", "IdC"):
            raise ValueError(("existential", fam, h, c_))
    # the premises, by the hypotheses
    rows = [t for t, e in enumerate(body) if e[0] in ("ty", "tm")]
    bound = {k: b for (kd, k, b) in peels if kd == "r"}
    for di, t in enumerate(rows):
        e = body[t]
        if e[0] == "ty":
            _, d, g, T = e
            ix = "tyIx %s %s %s" % (kexpr(d), kexpr(g), kexpr(T))
            pr = subst_es("◇ ⊢ r%d ∷ IMu JT D⊢ (%s)" % (t, ix), "dr%d" % t)
            if agctx(g) or ag(T): pr = "(⊢conv %s (tyIx≅ %s %s))" % (pr, agctx(g) or "done", ag(T) or "done")
            lines.append("  ihTy %s %s %s %s nr%d" % (sctx(g), sx(T), bound[t], pr, t))
        else:
            _, d, g, s_, T = e
            ix = "tmIx %s %s %s %s" % (kexpr(d), kexpr(g), kexpr(s_), kexpr(T))
            pr = subst_es("◇ ⊢ r%d ∷ IMu JT D⊢ (%s)" % (t, ix), "dr%d" % t)
            if agctx(g) or ag(s_) or ag(T):
                pr = "(⊢conv %s (tmIx≅ %s %s %s))" % (pr, agctx(g) or "done", ag(s_) or "done", ag(T) or "done")
            lines.append("  ihTm %s %s %s %s %s nr%d" % (sctx(g), sx(s_), sx(T), bound[t], pr, t))
        lines.append("  ▷ λ D%d →" % di)
    # the Ford on the type
    if ford:
        T = ford[3]
        pr = subst_es("X0 ≅ %s" % kexpr(T), "(idrefl-decᶜ dF nF)")
        if ag(T): pr = "(ctrn %s (⟶*→≅ %s))" % (pr, ag(T))
        lines.append("  quoteTy-inj %s %s (nf-≅ (quoteTy-normal {Γ = ⌊ Γ ⌋} %s) (quoteTy-normal {Γ = ⌊ Γ ⌋} %s) %s)" % (A_, sx(T), A_, sx(T), pr))
        lines.append("  ▷ λ eqA →")
    # the Spec rule
    if fam == "⊢ty": ctor = JTYCTOR[h]
    elif h == "pair": ctor = "⊢pair"
    elif h == "tr": ctor = "⊢trU" if r == 0 else "⊢tr"
    else: ctor = "⊢" + spec_name(h)
    args = JARGS.get((fam, h, r), " ".join("D%d" % i for i in range(len(rows))))
    app = "(%s %s)" % (ctor, args) if args else ctor
    if (fam, h, r) == ("⊢", "tr", 1):
        app = ("(subst (λ z → Γ ⊢ %s ∷ z) (cong₂ (λ C D → El (⌜Hom⌝ C D E6)) (wk-cancel-tm E6 E1) (wk-cancel-tm E6 E2))"
               " (⊢tr D0 D1 D2 (nonatc-ren vs P3) (occ-ren-tm avoids-wk E1) (occ-ren-tm avoids-wk E2) D3 D4 D5"
               " (subst (λ z → Γ ⊢ a2 ∷ z) (sym (cong₂ (λ C D → El (⌜Hom⌝ C D E5)) (wk-cancel-tm E5 E1) (wk-cancel-tm E5 E2))) D6)))") % (
               "(tr %s a1 a2)" % ov["a0"])
    res = app
    if ford:
        res = "(subst (λ z → %s) (sym eqA) %s)" % (concl("z").replace(subj, subj_ov(subj, ov, sp, h, fvars)), res)
    for (v_, eq_) in reversed(eqM):
        o2 = dict(ov); o2[v_] = "z"
        res = "(subst (λ z → %s) (sym %s) %s)" % (concl(A_).replace(subj, subj_ov(subj, o2, sp, h, fvars)), eq_, res)
    lines.append("  %s%s" % (res, " }" * closers))
    wh = ["  where", "    %s : RTm ε" % " ".join(["j", "g"] + fvn + (["X0"] if S else []) + ["p", "c"] + (["q%d" % i for i in range(len(qn))] + ["q", "c'"] if case else [])),
          "    j = dep ⌊ Γ ⌋", "    g = quoteCtx Γ"]
    wh += ["    f%d = %s" % (i, qf(fs[i], fvars[i])) for i in range(len(fs))]
    if S: wh.append("    X0 = quoteTy %s" % A_)
    wh.append("    p = %s" % ("".join("(pair %s " % x for x in fvn) + "unit" + ")" * len(fvn)))
    wh.append("    c = pair g %s" % ("X0" if S else "unit"))
    if case:
        wh += ["    q%d = quoteTy Q%d" % (i, i) if SIG[case][1][i][1] == 0 else "    q%d = %s" % (i, qf(SIG[case][1][i], "Q%d" % i)) for i in range(len(qn))]
        wh.append("    q = %s" % ("".join("(pair q%d " % i for i in range(len(qn))) + "unit" + ")" * len(qn)))
        wh.append("    c' = pair g p")
    wh.append("    R₁ = %s" % R1)
    if case:
        PN = "P" + al.pfx
        u0 = csf[r][0]("j", "p", "c")
        u1 = "%s.CASE j X0 (pair (fst c) p)" % PN
        u2 = "%s.CASE j X0 c'" % PN
        u3 = "⌜ %s j q c' ⌝ᵗ" % al.pfx
        wh.append("    R₀ : %s ⟶* %s" % (u0, tgt))
        wh.append("    R₀ = ⟶*-trans {t = %s} {u = %s} {v = %s} (%s.CASE-⟶ᵃ (step (βsnd g X0) done))" % (u0, u1, tgt, PN))
        wh.append("           (⟶*-trans {t = %s} {u = %s} {v = %s} (%s.CASE-⟶ᶜ (⟶*-pairˡ (step (βfst g X0) done)))" % (u1, u2, tgt, PN))
        wh.append("           (⟶*-trans {t = %s} {u = %s} {v = %s} (%s.case-β {j = j} {q = q} {c = c'} (atᵍ 0) (atʰ %d)) R₁))" % (
            u2, u3, tgt, PN, SIG[case][2]))
    else:
        wh.append("    R₀ = R₁")
    return L1 + lines + wh + [""] + out_pre      # the case level calls the row: row first

def subj_ov(subj, ov, sp, h, fvars):
    if not ov: return subj
    return "(%s)" % " ".join([sp(h)] + [ov.get(a, a) for a in fvars])

def gen_judge_decs():
    """the row decoders, split by consumption: types / terms"""
    mods = {}
    for fam, heads, mod in (("⊢ty", TYHEADS, "JudgeDecodeTy"), ("⊢", TMHEADS, "JudgeDecodeTm")):
        L = [JDHDR.replace("MODNAME", mod)]
        for h in heads:
            recs = DECREC.get((fam, h))
            if not recs: continue
            for r in sorted(recs):
                L += judge_dec(fam, h, r, recs[r])
        mods[mod] = L
    return mods

JDMHDR = """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.JudgeDecode where

------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- ★ PLAN-FAITHFUL F6 — THE TYPING JUDGEMENTS ARE EXACT: the converse of
-- `TypingAgree`.  A closed normal inhabitant of the Knot's typing family
-- at a quoted judgement `⌜Γ⌝ ⊢ ⌜t⌝ ∷ ⌜A⌝` (or `⌜Γ⌝ ⊢ty ⌜A⌝`) is one of the
-- subject's rows (`rows-dec`), and each row is its Spec rule
-- (`JudgeDecodeTy`/`JudgeDecodeTm`/`JudgeDecodeHand`, the `⊢conv` row
-- `dconv`).  The recursion is well-founded on the inhabitant's size: a
-- premise is a strict subterm (`Lib/Size`).
------------------------------------------------------------------------

open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.LogicalRelation using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity using ( sz; _≤_; ≤-refl )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; _,ₚ_; nth-z; nth-s )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Decode
open import DirectedHoTT.Lib.Size using ( Acc; acc; <-wf )
open import DirectedHoTT.Lib.RowsElim
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ctx using ( quoteCtx )
open import DirectedHoTT.Examples.Knot.JudgeIx using ( JT; tyIx; tmIx )
open import DirectedHoTT.Examples.Knot.Judge using ( D⊢; fibK )
open import DirectedHoTT.Examples.Knot.JudgeConv using ( TCVat )
open import DirectedHoTT.Examples.Knot.JudgeRowsGen
open import DirectedHoTT.Examples.Knot.RefJudge using ( T⊢ref )
open import DirectedHoTT.Examples.Knot.JudgeDecodeBase
open import DirectedHoTT.Examples.Knot.JudgeDecodeTy
open import DirectedHoTT.Examples.Knot.JudgeDecodeTm
open import DirectedHoTT.Examples.Knot.JudgeDecodeHand

decTyW : {N : ℕ} → Acc N → (Γ : Ctx) (A : RTy ⌊ Γ ⌋) {k : RTm ε} → sz k ≤ N →
         ◇ ⊢ k ∷ IMu JT D⊢ (tyIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy A)) → IsNormal k → Γ ⊢ty A
decTmW : {N : ℕ} → Acc N → (Γ : Ctx) (t : RTm ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) {k : RTm ε} → sz k ≤ N →
         ◇ ⊢ k ∷ IMu JT D⊢ (tmIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTm t) (quoteTy A)) → IsNormal k → Γ ⊢ t ∷ A

"""

def gen_judge_dispatch():
    L = [JDMHDR]
    QT = {0: "quoteTy", 1: "quoteTm"}
    def qf(f, a):
        if f[0] in ("rec", "cls"): return "(%s %s)" % (QT[f[1]], a)
        if f[0] == "nat": return "(quoteℕ %s)" % a
        return "(quoteVar %s)" % a
    IH = ["    ihTy : IHTy _", "    ihTy Γ' A' {r} lt dr nr = decTyW (rs (sz r) lt) Γ' A' ≤-refl dr nr",
          "    ihTm : IHTm _", "    ihTm Γ' t' A' {r} lt dr nr = decTmW (rs (sz r) lt) Γ' t' A' ≤-refl dr nr"]
    for fam, heads, dn in (("⊢ty", TYHEADS, "decTyW"), ("⊢", TMHEADS, "decTmW")):
        S = 0 if fam == "⊢ty" else 1
        for h in heads:
            fs = SIG[h][1]; K = SIG[h][2]
            args = ["a%d" % i for i in range(len(fs))]
            pat = "(%s)" % " ".join([spec_name(h)] + args) if args else spec_name(h)
            hasrec = any(f[0] == "rec" for f in fs)     # a closed (`cls`) field does not fix the context
            patE = "(%s)" % " ".join([spec_name(h) + ("" if hasrec else " {⌊ Γ ⌋}")] + args)
            PP = "unit"
            for f, a in reversed(list(zip(fs, args))): PP = "(pair %s %s)" % (qf(f, a), PP)
            C = "(pair (quoteCtx Γ) %s)" % ("unit" if S == 0 else "(quoteTy A)")
            j = "(dep ⌊ Γ ⌋)"
            recs = DECREC.get((fam, h))
            if recs:
                rec0 = recs[min(recs)]
                nc = rec0["nc"]
                ents = [rec0["csf"][r][0](j, PP, C) for r in range(nc)]
                hands = None
            elif (fam, h) == ("⊢", "ref"):
                nc = 2; ents = ["⌜ T⊢ref %s %s %s ⌝ᵗ" % (j, PP, C), "⌜ TCVat %d %s %s %s ⌝ᵗ" % (K, j, PP, C)]
                hands = "jdref ihTy ihTm Γ a0 a1 A"
            else:
                raise ValueError(("no rows", fam, h))
            ix = "tyIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy %s)" % patE if S == 0 else "tmIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTm %s) (quoteTy A)" % patE
            hdr = "%s (acc rs) Γ %s%s {k} hk dk nk =" % (dn, pat, "" if S == 0 else " A")
            cl = [hdr,
                  "  rows-elim< (rows-dec {I = JT} {D = D⊢} {i = %s} {m = %d} {Cs = %s}" % (ix, nc, " ∷ ".join(ents + ["[]"])),
                  "    (fibK {s = %d} {k = %d} {j = dep ⌊ Γ ⌋} {p = %s} {c = %s} (atᵍ %d) (atʰ %d)) dk nk)" % (S, K, PP, C, S, K)]
            alts_ = []
            for r in range(nc):
                nth = "nth-z"
                for _ in range(r): nth = "(nth-s %s)" % nth
                if S == 1 and r == nc - 1:
                    call = "dconv ihTm Γ %s A" % patE
                elif hands:
                    call = hands
                else:
                    call = "%s ihTy ihTm Γ%s%s" % (jdec_name(fam, h, r), "".join(" " + a for a in args), "" if S == 0 else " A")
                alts_.append(call)
            hs_ = "tt"
            for a_ in reversed(alts_): hs_ = "(%s , %s)" % (a_, hs_)
            cl.append("    hk " + hs_)
            cl.append("  where")
            cl += IH
            L += cl + [""]
    L += ["-- ★ the theorems",
          "decTy : (Γ : Ctx) (A : RTy ⌊ Γ ⌋) {k : RTm ε} →",
          "        ◇ ⊢ k ∷ IMu JT D⊢ (tyIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTy A)) → IsNormal k → Γ ⊢ty A",
          "decTy Γ A {k} dk nk = decTyW (<-wf (sz k)) Γ A ≤-refl dk nk", "",
          "decTm : (Γ : Ctx) (t : RTm ⌊ Γ ⌋) (A : RTy ⌊ Γ ⌋) {k : RTm ε} →",
          "        ◇ ⊢ k ∷ IMu JT D⊢ (tmIx (dep ⌊ Γ ⌋) (quoteCtx Γ) (quoteTm t) (quoteTy A)) → IsNormal k → Γ ⊢ t ∷ A",
          "decTm Γ t A {k} dk nk = decTmW (<-wf (sz k)) Γ t A ≤-refl dk nk"]
    return L

def spec_name(h):
    inv = {v: k for k, v in gk.NAMES.items()}
    return "RTy.Fin" if h == "Fin" else inv.get(h, h)

def gen_pw_agree():
    inv = {v: k for k, v in gk.NAMES.items()}
    spec = lambda h: inv.get(h, h)
    L = [PWAHDR]
    L.append("pwC : {Γ : Cx} (c : RTm Γ) → pw? c ≡ true → {Θ : Cx} → RTm Θ")
    L.append("⊢pwC : {Γ : Cx} (c : RTm Γ) (e : pw? c ≡ true) {Θ : Ctx} → Θ ⊢ pwC c e ∷ KPw (dep Γ) (quoteTm c) (quoteTm (pwBody c))")
    for h in TMHEADS:
        fs = SIG[h][1]
        args = ["a%d" % i for i in range(len(fs))]
        pat = "(%s)" % " ".join([spec(h)] + args) if args else spec(h)
        if h == "cPi":
            L.append("pwC {Γ} %s e = conₗ 0 (pair (idrefl (⌜Tm⌝ (nsuc (dep Γ))) (quoteTm a1)) unit)" % pat)
        elif h == "cHom":
            L.append("pwC {Γ} %s e = conₗ 0 (pair (quoteTm (pwBody a0)) (pair (pwC a0 e) (pair (idrefl (⌜Tm⌝ (nsuc (dep Γ))) (Xh Γ a0 a1 a2)) unit)))" % pat)
        else:
            L.append("pwC %s ()" % pat)
    for h in TMHEADS:
        fs = SIG[h][1]
        args = ["a%d" % i for i in range(len(fs))]
        pat = "(%s)" % " ".join([spec(h)] + args) if args else spec(h)
        if h == "cPi":
            L.append("⊢pwC {Γ} %s e = conPwcPi (⊢dep' Γ) (⊢quoteTm a0) (⊢quoteTm a1)" % pat)
        elif h == "cHom":
            L.append("⊢pwC {Γ} %s e =" % pat)
            L.append("  ⊢conv (conPwcHom (⊢dep' Γ) (⊢quoteTm a0) (⊢quoteTm a1) (⊢quoteTm a2) (⊢quoteTm (pwBody a0)) (⊢pwC a0 e))")
            L.append("         (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairʳ (Xh-agree a0 a1 a2)))))")
        else:
            L.append("⊢pwC %s ()" % pat)
    return L

PWAHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- `pw? c ≡ true` is COMPLETE for the Knot's `Pw` family, AT THE QUOTED BODY
-- `pwBody c` (PLAN-FAITHFUL F4): a ⌜Π⌝ is its own codomain; a ⌜Hom⌝'s body
-- is written with the Knot's `wk`, and agrees with `renTm vs` (F3).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PwAgree where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; pw?; pwBody )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶*-pairʳ; ⟶*-trans )
open import DirectedHoTT.Lib.Sugar using ( conₗ )
open import DirectedHoTT.Lib.FinFam using ( ffz )
open import DirectedHoTT.Examples.Knot.Sig using ( kcHom; kapp; kvar )
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.Ren using ( wk )
open import DirectedHoTT.Examples.Knot.Pw using ( KPw )
open import DirectedHoTT.Examples.Knot.PwConGen
open import DirectedHoTT.Examples.Knot.OpAgree using ( wk-agree-tm; node-2; node-3; node-1 )

-- a ⌜Hom⌝'s pointwise body, as the Knot writes it (with `wk`)
Xh : {Θ : Cx} (Γ : Cx) (C a b : RTm Γ) → RTm Θ
Xh Γ C a b = kcHom (quoteTm (pwBody C)) (kapp (wk 1 (dep Γ) (quoteTm a)) (kvar ffz)) (kapp (wk 1 (dep Γ) (quoteTm b)) (kvar ffz))

-- …which is the quoted Spec body
Xh-agree : {Γ Θ : Cx} (C a b : RTm Γ) → Xh {Θ} Γ C a b ⟶* quoteTm (pwBody (⌜Hom⌝ C a b))
Xh-agree C a b = ⟶*-trans (node-2 (node-1 (wk-agree-tm a))) (node-3 (node-1 (wk-agree-tm b)))

"""

PAHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The side-condition families are COMPLETE (PLAN-FAITHFUL F4): every
-- kernel side condition — `NoNatC c`, `stkA? c ≡ true`, `stkC? c ≡ true`,
-- `flat? c ≡ true` — maps to a Knot inhabitant AT THE QUOTED CODE.  The
-- rows mirror `Spec/Variance` clause by clause, and this module is that
-- claim checked: a true head builds its row, a false head is absurd.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PredsAgree where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; NoNatC; nnc-base; nnc-Unit; nnc-Fin; nnc-Σ; nnc-Id; nnc-Π; nnc-Hom; stkA?; stkC?; flat? )
open import DirectedHoTT.Lib.Sugar using ( conₗ )
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Preds using ( KNNC; KStkA; KStkC; KFlat; El-⌜StkA⌝; El-⌜StkC⌝ )
open import DirectedHoTT.Examples.Knot.PredsCon

"""


# ------------------------------------------------------------ the adequacy map for ⟶ (PLAN-FAITHFUL F5)
def spec_ctors(data):
    """the constructors of a Spec data block: [(name, type-text)]"""
    txt = open(os.path.join(ROOT, "Spec", "Typing.agda"), encoding="utf-8").read()
    i = txt.index("data %s " % data)
    lines = txt[i:].split("\n")[1:]
    out, cur = [], None
    for l in lines:
        if l and not l.startswith(" "): break
        l = l.split("--")[0].rstrip()
        if not l.strip(): continue
        m = re.match(r"^  (\S+)\s+:\s*(.*)$", l)
        if m and not l.startswith("   "):
            if cur: out.append(cur)
            cur = [m.group(1), m.group(2)]
        elif cur: cur[1] += " " + l.strip()
    if cur: out.append(cur)
    return out

def binders(ty):
    """implicit binder names in order, from the leading `{…}` groups"""
    names = []
    for g in re.findall(r"\{([^{}:]+):", ty):
        names += g.split()
    return names

SUB = "₀₁₂₃₄₅₆₇₈₉"
def alt_tag(h, i, n):
    return "" if n == 1 else "".join(SUB[int(c)] for c in str(i))

def red_alts(fam):
    """per Knot head: [(kind, data)] in fibre order — ξ alts then computation alts"""
    xi = xi_rules(fam)
    out = {}
    for h in (TMHEADS if fam == "⟶" else TYHEADS):
        n_xi = len(xi.get(h, []))
        n_comp = len(COMP[fam].get(h, []))
        out[h] = (n_xi, n_comp)
    return out

# ⟶ computation rules: Spec pattern → (Knot head, alt among the head's computation rules, hypothesis typings, target reduction)
def _q(x): return "(⊢quoteTm %s)" % x
IDP = lambda M: "(⊢conv (⊢idrefl (⊢⌜Tm⌝ (⊢isuc dj)) (toTm (⊢quoteTm %s))) (csymᵀ (credᵀ (El-⌜Id⌝ _ _ _))))" % M
STKA = lambda c: "(⊢conv (⊢stkAC %s st) (csymᵀ El-⌜StkA⌝))" % c
STKC = lambda c: "(⊢conv (⊢stkCC %s st) (csymᵀ El-⌜StkC⌝))" % c
PWP = lambda c: "(⊢conv (⊢pwC %s pc) (csymᵀ El-⌜Pw⌝))" % c
WK = lambda x: "(wk-agree-tm %s)" % x
TRM = lambda c, a, m: "(⌜Hom⌝ %s %s %s)" % (c, a, m)
RED_COMP = [
  ("β t u", "app", 0, [_q("u"), _q("t")], "(sub0-agree-tm t u)"),
  ("βfst a b", "fst", 0, [_q("a"), _q("b")], None),
  ("βsnd a b", "snd", 0, [_q("a"), _q("b")], None),
  ("ordtr-z t u p q", "ordtr", 0, [_q("t"), _q("u"), _q("p"), _q("q")], None),
  ("ordtr-szz a p q", "ordtr", 1, [_q("p"), _q("q"), _q("a")], None),
  ("ordtr-ssz a t p q", "ordtr", 2, [_q("p"), _q("q"), _q("a"), _q("t")], None),
  ("ordtr-szs a u p q", "ordtr", 3, [_q("p"), _q("q"), _q("a"), _q("u")], None),
  ("ordtr-sss a t u p q", "ordtr", 4, [_q("p"), _q("q"), _q("a"), _q("t"), _q("u")], None),
  ("tr-J-base c a m s e", "tr", 0, [_q(TRM("c","a","m")), _q("e"), _q("s"), _q("c"), _q("a"), _q("m"), IDP(TRM("c","a","m"))], None),
  ("tr-J-Σ c a m c₁ c₂ s e", "tr", 1, [_q(TRM("c","a","m")), _q("e"), _q("s"), _q("c₁"), _q("c₂"), _q("c"), _q("a"), _q("m"), IDP(TRM("c","a","m"))], None),
  ("tr-J-Unit c a m s e", "tr", 2, [_q(TRM("c","a","m")), _q("e"), _q("s"), _q("c"), _q("a"), _q("m"), IDP(TRM("c","a","m"))], None),
  ("tr-J-Id c a m c₁ a₁ b₁ s e", "tr", 3, [_q(TRM("c","a","m")), _q("e"), _q("s"), _q("c₁"), _q("a₁"), _q("b₁"), _q("c"), _q("a"), _q("m"), IDP(TRM("c","a","m"))], None),
  ("tr-J-IMu {I} {D} {iˣ} c a m s e", "tr", 4, [_q(TRM("c","a","m")), _q("e"), _q("s"), _q("I"), _q("D"), _q("iˣ"), _q("c"), _q("a"), _q("m"), IDP(TRM("c","a","m"))], None),
  ("tr-J-Fin {n} c a m s e", "tr", 5, [_q(TRM("c","a","m")), _q("e"), _q("s"), _q("n"), _q("c"), _q("a"), _q("m"), IDP(TRM("c","a","m"))], None),
  ("tr-J-Hom c a m c₁ a₁ b₁ s e st", "tr", 6, [_q(TRM("c","a","m")), _q("e"), _q("s"), _q("c₁"), _q("a₁"), _q("b₁"), _q("c"), _q("a"), _q("m"), IDP(TRM("c","a","m")), STKA("c₁")], None),
  ("tr-taut f e", "tr", 7, [_q("(var vz)"), _q("e"), _q("f"), IDP("(var vz)")], None),
  ("tr-pw c a f e pc", "tr", 8, [_q(TRM("c","a","(var vz)")), _q("e"), _q("f"), _q("c"), _q("a"), IDP(TRM("c","a","(var vz)")), _q("(pwBody c)"), PWP("c")],
     "(node-1 (⟶*-trans (node-1 (⟶*-trans (node-1 (pwSh-agree (pwBody c))) (node-2 (node-1 %s)))) (node-3 (node-1 %s))))" % (WK("a"), WK("e"))),
  ("hrefl-pw C s pc", "hrefl", 0, [_q("C"), _q("s"), _q("(pwBody C)"), PWP("C")], "(node-1 (node-2 (node-1 %s)))" % WK("s")),
  ("hrefl-Nat-z", "hrefl", 1, [], None),
  ("hrefl-Nat-s m", "hrefl", 2, [_q("m")], None),
  ("ap-J cB b c₁ s st", "ap", 0, [_q("cB"), _q("b"), _q("c₁"), _q("s"), STKC("c₁")], "(node-2 (sub0-agree-tm b s))"),
  ("jsub-refl d c s e", "jsub", 0, [_q("d"), _q("e"), _q("c"), _q("s")], None),
  ("natrec-zero z s", "natrec", 0, [_q("z"), _q("s")], None),
  ("natrec-suc z s n", "natrec", 1, [_q("z"), _q("s"), _q("n")], "(inst-agree n (natrec z s n) s)"),
  ("ι D i e p", "ielim", 0, [_q("D"), _q("i"), _q("e"), _q("p")], None),
  ("dpay-ι I D", "dpay", 0, [_q("I"), _q("D")], None),
  ("dpay-σ I D S f", "dpay", 1, [_q("I"), _q("D"), _q("S"), _q("f")],
     "(node-2 (⟶*-trans (node-1 %s) (⟶*-trans (node-2 %s) (node-3 (node-1 %s)))))" % (WK("I"), WK("D"), WK("f"))),
  ("dpay-ρ I D j C", "dpay", 2, [_q("I"), _q("D"), _q("j"), _q("C")],
     "(node-2 (⟶*-trans (node-1 %s) (⟶*-trans (node-2 %s) (node-3 %s))))" % (WK("I"), WK("D"), WK("C"))),
  ("dih-ι D e p", "dih", 0, [_q("D"), _q("e"), _q("p")], None),
  ("dih-σ D e S f p", "dih", 1, [_q("D"), _q("e"), _q("p"), _q("S"), _q("f")], None),
  ("dih-ρ D e j C p", "dih", 2, [_q("D"), _q("e"), _q("p"), _q("j"), _q("C")], None),
  ("fcase-z a b", "fcase", 0, [_q("a"), _q("b")], None),
  ("fcase-s t a b", "fcase", 1, [_q("a"), _q("b"), _q("t")], "(sub0-agree-tm b t)"),
  ("psplit-β b x y", "psplit", 0, [_q("b"), _q("x"), _q("y")],
     "(⟶≡ (cong (λ X → quoteTm X) (inst-single2 x y b)) (inst-agree x y b))"),
]

# the reduction constructors' FIRST implicit is the generalised `Γ`
# (`variable Γ : Cx` in Spec/Typing): a positional `{x}` would bind it
def hidΓ(spat):
    h, _, rest = spat.partition(" ")
    return "%s {_} %s" % (h, rest) if rest.startswith("{") else spat

def gen_enred():
    fam = "⟶"
    alts = red_alts(fam)
    xi = xi_rules(fam)
    inv = {v: k for k, v in gk.NAMES.items()}
    L = [ENRED_HDR]
    seen = set()
    # ξ: parsed from the Spec
    for name, ty in spec_ctors("_⟶_"):
        if not name.startswith("ξ-"): continue
        m = re.search(r"→\s*(\S+)\s*⟶\s*(\S+)\s*→\s*(.+?)\s*⟶\s*(.+)$", ty)
        assert m, (name, ty)
        lt, rt = m.group(3).split(), m.group(4).split()
        H, largs, rargs = lt[0], lt[1:], rt[1:]
        h = gk.NAMES.get(H, H)
        fs = SIG[h][1]
        i = [k for k in range(len(largs)) if largs[k] != rargs[k]]
        assert len(i) == 1 and len(largs) == len(fs), (name, lt, rt)
        i = i[0]
        n_xi, n_comp = alts[h]
        rank = [k for k, f in enumerate(fs) if f[0] == "rec"].index(i) + 1
        con = "con⟶%s%s" % (h, alt_tag(h, rank, n_xi + n_comp))
        bs = binders(ty)
        pat = "(%s {_} %s r)" % (name, " ".join("{%s}" % b for b in bs))
        fty = lambda k, x: "(⊢quoteTm %s)" % x if fs[k][0] == "rec" else "(⊢quoteℕ %s)" % x
        args = " ".join([fty(k, largs[k]) for k in range(len(fs))] + ["(⊢quoteTm %s)" % rargs[i], "(Σ.snd (enRed r))"])
        L.append("enRed {Γ} %s = _ , %s (⊢dep' Γ) %s" % (pat, con, args))
        seen.add(name)
    # the computation rules
    for spat, h, k, hyps, red in RED_COMP:
        n_xi, n_comp = alts[h]
        con = "con⟶%s%s" % (h, alt_tag(h, n_xi + k + 1, n_xi + n_comp))
        app = "%s dj %s" % (con, " ".join(hyps))
        body = app if red is None else "⊢conv (%s) (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairʳ %s))))" % (app, red)
        L.append("enRed {Γ} (%s) = _ , %s" % (hidΓ(spat), body))
        L.append("  where dj = ⊢dep' Γ")
        seen.add(spat.split()[0])
    # δ: the hand-written row of `Knot/Ref` (PLAN-BIDI §2-ter, option 3)
    L.append("enRed {Γ} (δref n b) = _ , ⊢conv (con⟶δ (⊢dep' Γ) (⊢quoteℕ n) (⊢quoteTm b)) "
             "(red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairʳ (εwk-agree Γ b)))))")
    seen.add("δref")
    return L

ENRED_HDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- ★ THE REDUCTION JUDGEMENT IS FAITHFUL (PLAN-FAITHFUL F5, `⟶`): every Spec
-- reduction `t ⟶ u` maps to a Knot inhabitant AT THE QUOTED JUDGEMENT
-- `K⟶ ⌜Γ⌝ ⌜t⌝ ⌜u⌝` — the type names the index, so a row encoding the wrong
-- rule is a type error here.  ξ rules are parsed from `Spec/Typing`; a
-- computation rule's Knot target meets the Spec's by F3's agreements.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedAgree where

open import normalizer.Syntax.Types using ( _≡_; refl; cong; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Variance using ( pwBody )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶*-pairʳ; ⟶*-trans )
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⊢⌜Tm⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( toTm )
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.Red using ( K⟶ )
open import DirectedHoTT.Examples.Knot.Preds using ( El-⌜StkA⌝; El-⌜StkC⌝ )
open import DirectedHoTT.Examples.Knot.Pw using ( El-⌜Pw⌝ )
open import DirectedHoTT.Examples.Knot.PredsAgree using ( ⊢stkAC; ⊢stkCC )
open import DirectedHoTT.Examples.Knot.PwAgree using ( ⊢pwC )
open import DirectedHoTT.Examples.Knot.OpAgree
open import DirectedHoTT.Examples.Knot.RedXiConGen
open import DirectedHoTT.Examples.Knot.RedCompConGen
open import DirectedHoTT.Examples.Knot.RefCon using ( con⟶δ )

private
  ⟶≡ : {Θ : Cx} {t u u' : RTm Θ} → u ≡ u' → t ⟶* u → t ⟶* u'
  ⟶≡ refl r = r

enRed : {Γ : Cx} {t u : RTm Γ} → t ⟶ u → {Θ : Ctx} → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K⟶ (dep Γ) (quoteTm t) (quoteTm u))
"""


def _qT(x): return "(⊢quoteTy %s)" % x
REDT_COMP = [
  ("El-⌜base⌝", "El", 0, [], None),
  ("El-⌜Π⌝ c d", "El", 1, [_q("c"), _q("d")], None),
  ("El-⌜Σ⌝ c d", "El", 2, [_q("c"), _q("d")], None),
  ("El-⌜Hom⌝ c a b", "El", 3, [_q("c"), _q("a"), _q("b")], None),
  ("El-⌜Id⌝ c a b", "El", 4, [_q("c"), _q("a"), _q("b")], None),
  ("El-⌜Nat⌝", "El", 5, [], None),
  ("El-⌜IMu⌝ {I} {D} {i}", "El", 6, [_q("I"), _q("D"), _q("i")], None),
  ("El-⌜Fin⌝ {n}", "El", 7, ["(⊢quoteℕ n)"], None),
  ("El-⌜Unit⌝", "El", 8, [], None),
  ("DIh-ι D M p", "DIh", 0, [_q("D"), _qT("M"), _q("p")], None),
  ("DIh-σ D M S f p", "DIh", 1, [_q("D"), _qT("M"), _q("p"), _q("S"), _q("f")], None),
  ("DIh-ρ D M j C p", "DIh", 2, [_q("D"), _qT("M"), _q("p"), _q("j"), _q("C")],
     "(⟶*-trans (node-1 (iinst-agree j (fst p) M)) (node-2 (⟶*-trans (node-1 %s) (⟶*-trans (node-2 (wk2u-agree M)) (⟶*-trans (node-3 %s) (node-4 (node-1 %s)))))))" % (WK("D"), WK("C"), WK("p"))),
  ("Hom-Nat-z n", "Hom", 0, [_q("n")], None),
  ("Hom-Nat-sz m", "Hom", 1, [_q("m")], None),
  ("Hom-Nat-ss m n", "Hom", 2, [_q("m"), _q("n")], None),
  ("Hom-U c d", "Hom", 3, [_q("c"), _q("d")], "(node-2 (node-1 %s))" % WK("d")),
  ("Hom-Π A B f g", "Hom", 4, [_q("f"), _q("g"), _qT("A"), _qT("B")],
     "(node-2 (⟶*-trans (node-2 (node-1 %s)) (node-3 (node-1 %s))))" % (WK("f"), WK("g"))),
]

def gen_enredT():
    fam = "⟶ᵀ"
    alts = red_alts(fam)
    L = [ENREDT_HDR]
    for name, ty in spec_ctors("_⟶ᵀ_"):
        if not name.startswith("ξ-"): continue
        m = re.search(r"→\s*(\S+)\s*(⟶ᵀ|⟶)\s*(\S+)\s*→\s*(.+?)\s*⟶ᵀ\s*(.+)$", ty)
        assert m, (name, ty)
        lt, rt = m.group(4).split(), m.group(5).split()
        H, largs, rargs = lt[0], lt[1:], rt[1:]
        h = gk.NAMES.get(H, H)
        fs = SIG[h][1]
        i = [k for k in range(len(largs)) if largs[k] != rargs[k]]
        assert len(i) == 1 and len(largs) == len(fs), (name, lt, rt)
        i = i[0]
        n_xi, n_comp = alts[h]
        rank = [k for k, f in enumerate(fs) if f[0] == "rec"].index(i) + 1
        con = "con⟶ᵀ%s%s" % (h, alt_tag(h, rank, n_xi + n_comp))
        pat = "(%s {_} %s r)" % (name, " ".join("{%s}" % b for b in binders(ty)))
        fty = lambda k, x: ("(⊢quoteTy %s)" if fs[k][1] == 0 else "(⊢quoteTm %s)") % x if fs[k][0] == "rec" else "(⊢quoteℕ %s)" % x
        if fs[i][1] == 0:
            tail = ["(⊢quoteTy %s)" % rargs[i], "(Σ.snd (enRedT r))"]
        else:
            tail = ["(⊢quoteTm %s)" % rargs[i], "(⊢conv (Σ.snd (enRed r)) (csymᵀ El-⌜⟶⌝))"]
        L.append("enRedT {Γ} %s = _ , %s (⊢dep' Γ) %s" % (pat, con, " ".join([fty(k, largs[k]) for k in range(len(fs))] + tail)))
    for spat, h, k, hyps, red in REDT_COMP:
        n_xi, n_comp = alts[h]
        con = "con⟶ᵀ%s%s" % (h, alt_tag(h, n_xi + k + 1, n_xi + n_comp))
        app = "%s dj%s" % (con, "".join(" " + x for x in hyps))
        body = app if red is None else "⊢conv (%s) (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairʳ %s))))" % (app, red)
        pat = "(%s)" % hidΓ(spat) if " " in spat else spat
        L.append("enRedT {Γ} %s = _ , %s" % (pat, body))
        L.append("  where dj = ⊢dep' Γ")
    return L

ENREDT_HDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- ★ THE TYPE REDUCTION IS FAITHFUL (PLAN-FAITHFUL F5, `⟶ᵀ`): every Spec
-- `A ⟶ᵀ B` maps to a Knot inhabitant at `K⟶ᵀ ⌜Γ⌝ ⌜A⌝ ⌜B⌝`; a ξ rule on a
-- term field cites `enRed` through the lower stratum's code `⌜⟶⌝`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedTAgree where

open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶*-pairʳ; ⟶*-trans )
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.Red using ( El-⌜⟶⌝ )
open import DirectedHoTT.Examples.Knot.RedT using ( K⟶ᵀ )
open import DirectedHoTT.Examples.Knot.OpAgree
open import DirectedHoTT.Examples.Knot.RedAgree using ( enRed )
open import DirectedHoTT.Examples.Knot.RedTConGen

enRedT : {Γ : Cx} {A B : RTy Γ} → A ⟶ᵀ B → {Θ : Ctx} → Σ (RTm ⌊ Θ ⌋) (λ c → Θ ⊢ c ∷ K⟶ᵀ (dep Γ) (quoteTy A) (quoteTy B))
"""

PCHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The CONSTRUCTORS of the side-condition families (`Knot/Preds`): a row's
-- premises at the values, the row (at the fibre's sources) read there by
-- one `mono-by` — the scheme of `JudgeConGen`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PredsCon where

open import normalizer.Syntax.Types using ( _≡_; refl; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; conₗ; lt-z; lt-s; nth-z; nth-s; atᶜ; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.SynFib using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.FinFam using ( ⊢isuc )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⊢payK )
open import DirectedHoTT.Examples.Knot.Preds

private
  variable
    Δ Θ : Cx

"""

RCHDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-judge.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The CONSTRUCTORS of the generated ⟶ / ⟶ᵀ / Pw rows, at VALUES — the
-- scheme of `JudgeConGen`: the payload through the row's tails, the row
-- read at the sources by one `mono-by`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedConGen where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; ⟶ᵀ*-El; ⟶*-dpayᶜ; ⟶*-trans; ⟶*-pairˡ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; tag; conₗ; lt-z; lt-s; nth-z; nth-s; atᶜ )
open import DirectedHoTT.Lib.SynFib using ( ⊢conRowₖ )
open import DirectedHoTT.Lib.SynRed
open import DirectedHoTT.Lib.FinFam using ( FinI; ⊢isuc; toI; ffz; ⊢ffz; ffs; ⊢ffs )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Lookup using ( toTy; hereTy )
open import DirectedHoTT.Examples.Knot.Sub using ( sub0; ⊢sub0 )
open import DirectedHoTT.Examples.Knot.Ren using ( wk; ⊢wkS )
open import DirectedHoTT.Examples.Knot.SubEnv
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⌜Tm⌝; ⊢⌜Tm⌝; ⌜Ty⌝; ⊢⌜Ty⌝ )
open import DirectedHoTT.Examples.Knot.JudgeCase using ( w1; w2; w3; hereTm; toTm; wkN; wkK; wkG )
open import DirectedHoTT.Examples.Knot.GenHelpers
open import DirectedHoTT.Examples.Knot.Preds using ( ⌜StkA⌝; ⊢⌜StkA⌝; ⌜StkC⌝; ⊢⌜StkC⌝ )
open import DirectedHoTT.Examples.Knot.RedIx
open import DirectedHoTT.Examples.Knot.NestIx
open import DirectedHoTT.Examples.Knot.JudgeIx using ( ⊢payK )
RCIMPORTS
"""
RCIMPORTS = {
  "⟶β": "open import DirectedHoTT.Examples.Knot.Pw using ( ⌜Pw⌝; ⊢⌜Pw⌝ )\nopen import DirectedHoTT.Examples.Knot.Red\n",
  "⟶":  "open import DirectedHoTT.Examples.Knot.Pw using ( ⌜Pw⌝; ⊢⌜Pw⌝ )\nopen import DirectedHoTT.Examples.Knot.Red\n",
  "⟶ᵀ": "open import DirectedHoTT.Examples.Knot.Red using ( ⌜⟶⌝; ⊢⌜⟶⌝ )\nopen import DirectedHoTT.Examples.Knot.RedT\n",
  "Pw":  "open import DirectedHoTT.Examples.Knot.Pw\n",
}

if __name__ == "__main__":
    main()
