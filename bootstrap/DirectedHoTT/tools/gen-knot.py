#!/usr/bin/env python3
"""
gen-knot.py — the RTm/RTy knot as ONE indexed description.

★ WHY A GENERATOR AND NOT 53 HAND-WRITTEN ROWS.  PLAN-INDEXED §5 item 7
  needs the whole mutual knot — 7 families, 53 constructors — encoded as a
  single `IDesc` over `I = Σ' Nat Nat`.  Each constructor needs an `ICon`,
  an `IConWf`, and (step 3) an `sz` method: ~159 clauses whose ONLY content
  is de Bruijn bookkeeping.  Hand-writing them is not work, it is a
  transcription error waiting to happen; `tools/gen-clauses.py`'s header
  records what happened the last time clause families were produced ad hoc.

★★ THE ENCODING, in one paragraph.  The index is a PAIR: `fst` is a SORT
  TAG (0 RTy · 1 RTm · 2 Desc · 3 DCon · 4 IDesc · 5 ICon · 6 Var), `snd`
  is a CONTEXT DEPTH.  Every constructor FORDS ITS TAG — `Id Nat
  (fst ⟨i⟩) t` — and, bar the two `Var` rows, the depth RIDES
  unconstrained (PLAN-INDEXED §14).  A recursive
  field names its own index outright: `lam`'s field is
  `pair 1 (suc (snd ⟨i⟩))` (same sort, depth pushed), `El`'s is
  `pair 1 (snd ⟨i⟩)` (other sort, depth held).

⚠ THE TWO EXCEPTIONS, and they are real.  `Var`'s `vz`/`vs` are the only
  constructors whose TARGET depth is constrained — they exist only at
  `suc m` — so they bind an `m : Nat` and Ford the SECOND component too.
  That is Fording used exactly as `Examples/Scoped`'s `Fin` uses it, and it
  is why "Ford the component, not the pair" is the right rule rather than
  "Ford the tag": BOTH components can need it, INDEPENDENTLY.

⛔ AND `Ctx` IS NOT ONE OF THESE ROWS — it was, for one day, and the
  reason it is not is worth keeping.  `_▹_` carries an `RTy ⌊ Γ ⌋`, so
  `Ctx` DEPENDS on the syntax and the syntax never depends back: a
  one-directional dependency is a STRATUM, not a member.  Encoded as an
  8th sort it type-checked, and then made the first knot-wide traversal
  FABRICATE (`Negative/WkEmp`).  It lives in `Examples/Knot/CtxD` as its
  own 2-row family over a BARE DEPTH, and needs no tag ford at all.
  See `HANDOFF-2026-08-27` §A′.

⚠ DEPTH IS DEGENERATE FOR THE THREE CLOSED SORTS.  `Desc`/`DCon`/`IDesc`
  carry no context, so nothing constrains their depth and `K (2,d)` is the
  same set for every `d`.  Harmless (a family with unused index), and
  strictly cheaper than Fording them to 0 — which would cost 7 extra
  constraint fields and buy nothing.  Where a closed sort's depth MATTERS
  it is written literally: `dκ`'s `RTy ε` field is at `pair 0 0`, and
  `_◂_`'s `ICon (ε ∙)` field is at `pair 5 1`.

THE FIELD DSL.  Each constructor is a list of fields, in the source
constructor's own argument order, with the Ford(s) appended:
    ('rec',  sort, depth)   a recursive field at `pair sort depth`
    ('nat',)                a `κ` field of type `El ⌜Nat⌝` (a `ℕ` tag, or
                            the `m` a depth-Ford needs)
    ('ford', comp, rhs)     `iκ (⌜Id⌝ ⌜Nat⌝ (comp ⟨i⟩) rhs)`
depth expressions:
    ('D',)        `snd ⟨i⟩`            ('sucD', n)  `suc^n (snd ⟨i⟩)`
    ('lit', n)    the numeral `n`      ('fld', j)   field `j`, as a Nat
"""
import sys, os, re

# ---------------------------------------------------------------- the sorts
SORTS = ["sTy", "sTm", "sDesc", "sDCon", "sIDesc", "sICon", "sVar"]

D      = ('D',)
def sucD(n=1): return ('sucD', n)
def lit(n):    return ('lit', n)
def fld(j):    return ('fld', j)
def rec(s, d): return ('rec', s, d)
NAT    = ('nat',)
def ford(comp, rhs): return ('ford', comp, rhs)

FORD_TY    = ford('fst', ('sortlit', 'sTy'))
FORD_TM    = ford('fst', ('sortlit', 'sTm'))
FORD_DESC  = ford('fst', ('sortlit', 'sDesc'))
FORD_DCON  = ford('fst', ('sortlit', 'sDCon'))
FORD_IDESC = ford('fst', ('sortlit', 'sIDesc'))
FORD_ICON  = ford('fst', ('sortlit', 'sICon'))
FORD_VAR   = ford('fst', ('sortlit', 'sVar'))

# ------------------------------------------------------- the 53 constructors
# (agda name, source constructor, [fields])
KNOT = [
 # --- RTy, 11 -------------------------------------------------------------
 ("cTy-base",  "base : RTy Γ",                         [FORD_TY]),
 ("cTy-U",     "U : RTy Γ",                            [FORD_TY]),
 ("cTy-Pi",    "Π : RTy Γ → RTy (Γ ∙) → RTy Γ",        [rec("sTy", D), rec("sTy", sucD()), FORD_TY]),
 ("cTy-Sg",    "Σ' : RTy Γ → RTy (Γ ∙) → RTy Γ",       [rec("sTy", D), rec("sTy", sucD()), FORD_TY]),
 ("cTy-El",    "El : RTm Γ → RTy Γ",                   [rec("sTm", D), FORD_TY]),
 ("cTy-Hom",   "Hom : RTy Γ → RTm Γ → RTm Γ → RTy Γ",  [rec("sTy", D), rec("sTm", D), rec("sTm", D), FORD_TY]),
 ("cTy-Unit",  "Unit : RTy Γ",                         [FORD_TY]),
 ("cTy-Nat",   "Nat : RTy Γ",                          [FORD_TY]),
 ("cTy-Id",    "Id : RTy Γ → RTm Γ → RTm Γ → RTy Γ",   [rec("sTy", D), rec("sTm", D), rec("sTm", D), FORD_TY]),
 ("cTy-Mu",    "Mu : Desc → RTy Γ",                    [rec("sDesc", D), FORD_TY]),
 ("cTy-IMu",   "IMu : IDesc → RTy ε → RTm Γ → RTy Γ",  [rec("sIDesc", D), rec("sTy", lit(0)), rec("sTm", D), FORD_TY]),
 # --- RTm, 30 -------------------------------------------------------------
 ("cTm-var",   "var : Var Γ → RTm Γ",                  [rec("sVar", D), FORD_TM]),
 ("cTm-lam",   "lam : RTm (Γ ∙) → RTm Γ",              [rec("sTm", sucD()), FORD_TM]),
 ("cTm-app",   "app : RTm Γ → RTm Γ → RTm Γ",          [rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-pair",  "pair : RTm Γ → RTm Γ → RTm Γ",         [rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-absurd","absurd : RTm Γ → RTm Γ → RTm Γ",       [rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-ordtr", "ordtr : (5 × RTm Γ) → RTm Γ",          [rec("sTm", D)] * 5 + [FORD_TM]),
 ("cTm-fst",   "fst : RTm Γ → RTm Γ",                  [rec("sTm", D), FORD_TM]),
 ("cTm-snd",   "snd : RTm Γ → RTm Γ",                  [rec("sTm", D), FORD_TM]),
 ("cTm-cbase", "⌜base⌝ : RTm Γ",                       [FORD_TM]),
 ("cTm-cPi",   "⌜Π⌝ : RTm Γ → RTm (Γ ∙) → RTm Γ",      [rec("sTm", D), rec("sTm", sucD()), FORD_TM]),
 ("cTm-cSg",   "⌜Σ⌝ : RTm Γ → RTm (Γ ∙) → RTm Γ",      [rec("sTm", D), rec("sTm", sucD()), FORD_TM]),
 ("cTm-cHom",  "⌜Hom⌝ : (3 × RTm Γ) → RTm Γ",          [rec("sTm", D)] * 3 + [FORD_TM]),
 ("cTm-hrefl", "hrefl : RTm Γ → RTm Γ → RTm Γ",        [rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-tr",    "tr : RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ",
                                                       [rec("sTm", sucD()), rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-ap",    "ap : RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ",
                                                       [rec("sTm", D), rec("sTm", sucD()), rec("sTm", D), FORD_TM]),
 ("cTm-cId",   "⌜Id⌝ : (3 × RTm Γ) → RTm Γ",           [rec("sTm", D)] * 3 + [FORD_TM]),
 ("cTm-idrefl","idrefl : RTm Γ → RTm Γ → RTm Γ",       [rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-jsub",  "jsub : RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ",
                                                       [rec("sTm", sucD()), rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-unit",  "unit : RTm Γ",                         [FORD_TM]),
 ("cTm-nzero", "nzero : RTm Γ",                        [FORD_TM]),
 ("cTm-nsuc",  "nsuc : RTm Γ → RTm Γ",                 [rec("sTm", D), FORD_TM]),
 ("cTm-natrec","natrec : RTm Γ → RTm ((Γ ∙) ∙) → RTm Γ → RTm Γ",
                                                       [rec("sTm", D), rec("sTm", sucD(2)), rec("sTm", D), FORD_TM]),
 ("cTm-con",   "con : ℕ → RTm Γ → RTm Γ",              [NAT, rec("sTm", D), FORD_TM]),
 ("cTm-elim",  "elim : Desc → RTm Γ → RTm Γ → RTm Γ",  [rec("sDesc", D), rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-icon",  "icon : ℕ → RTm Γ → RTm Γ",             [NAT, rec("sTm", D), FORD_TM]),
 ("cTm-ielim", "ielim : IDesc → RTm Γ → RTm Γ → RTm Γ → RTm Γ",
                                                       [rec("sIDesc", D), rec("sTm", D), rec("sTm", D), rec("sTm", D), FORD_TM]),
 ("cTm-cNat",  "⌜Nat⌝ : RTm Γ",                        [FORD_TM]),
 ("cTm-cMu",   "⌜Mu⌝ : Desc → RTm Γ",                  [rec("sDesc", D), FORD_TM]),
 ("cTm-cIMu",  "⌜IMu⌝ : IDesc → RTy ε → RTm Γ → RTm Γ",[rec("sIDesc", D), rec("sTy", lit(0)), rec("sTm", D), FORD_TM]),
 ("cTm-cUnit", "⌜Unit⌝ : RTm Γ",                       [FORD_TM]),
 # --- Desc, 2 -------------------------------------------------------------
 ("cDesc-nil", "dnil : Desc",                          [FORD_DESC]),
 ("cDesc-cons","_◃_ : DCon → Desc → Desc",             [rec("sDCon", D), rec("sDesc", D), FORD_DESC]),
 # --- DCon, 3 -------------------------------------------------------------
 ("cDCon-i",   "dι : DCon",                            [FORD_DCON]),
 ("cDCon-rho", "dρ : DCon → DCon",                     [rec("sDCon", D), FORD_DCON]),
 ("cDCon-kap", "dκ : RTy ε → DCon → DCon",             [rec("sTy", lit(0)), rec("sDCon", D), FORD_DCON]),
 # --- IDesc, 2 ------------------------------------------------------------
 ("cIDesc-nil","inil : IDesc",                         [FORD_IDESC]),
 ("cIDesc-cons","_◂_ : ICon (ε ∙) → IDesc → IDesc",    [rec("sICon", lit(1)), rec("sIDesc", D), FORD_IDESC]),
 # --- ICon, 3 -------------------------------------------------------------
 ("cICon-i",   "iι : ICon Δ",                          [FORD_ICON]),
 ("cICon-rho", "iρ : RTm Δ → ICon (Δ ∙) → ICon Δ",     [rec("sTm", D), rec("sICon", sucD()), FORD_ICON]),
 ("cICon-kap", "iκ : RTm Δ → ICon (Δ ∙) → ICon Δ",     [rec("sTm", D), rec("sICon", sucD()), FORD_ICON]),
 # --- Var, 2.  ⚠ THE ONLY DEPTH-FORDED ROWS. ------------------------------
 ("cVar-vz",   "vz : Var (Γ ∙)",                       [NAT, FORD_VAR, ford('snd', ('sucfld', 0))]),
 ("cVar-vs",   "vs : Var Γ → Var (Γ ∙)",               [NAT, rec("sVar", fld(0)), FORD_VAR, ford('snd', ('sucfld', 0))]),
]

# ------------------------------------------------------------------ emitters
def dbv(k):
    "the TERM for the variable `k` slots in from the top of the telescope"
    return "var " + ("(vs " * k) + "vz" + (")" * k)

def dbd(k):
    "…and the LOOKUP derivation for it"
    return "⊢var " + ("(there " * k) + "here" + (")" * k)

def amb(k):   return dbv(k)          # the ambient index, k fields bound
def damb(k):  return dbd(k)

def nsucs(n, inner):
    return ("nsuc (" * n) + inner + (")" * n) if n else inner

def dnsucs(n, inner):
    return ("⊢nsuc (" * n) + inner + (")" * n) if n else inner

def numeral(n):
    return nsucs(n, "nzero")

def dnumeral(n):
    return dnsucs(n, "⊢nzero")

def dexpr(e, k, nfields):
    """(term, derivation-at-Nat) for a depth expression, k fields bound"""
    kind = e[0]
    if kind == 'D':
        return f"snd ({amb(k)})", f"⊢snd ({damb(k)})"
    if kind == 'sucD':
        t, d = dexpr(D, k, nfields)
        return nsucs(e[1], t), dnsucs(e[1], d)
    if kind == 'lit':
        return numeral(e[1]), dnumeral(e[1])
    if kind == 'fld':
        # field j, counted from the BOTTOM; k fields are bound, so it sits
        # k-1-j slots in.  ⚠ it is a `nat` field, typed `El ⌜Nat⌝` — `fromI`.
        back = k - 1 - e[1]
        return dbv(back), f"fromI ({dbd(back)})"
    if kind == 'sortlit':
        return e[1], "⊢" + e[1]
    if kind == 'sucfld':
        t, d = dexpr(fld(e[1]), k, nfields)
        return f"nsuc ({t})", f"⊢nsuc ({d})"
    raise ValueError(e)

def emit_icon(fields):
    """the ICon term, as a list of (open-text) layers"""
    out, k = [], 0
    for f in fields:
        if f[0] == 'rec':
            s, dd = f[1], f[2]
            dt, _ = dexpr(dd, k, len(fields))
            out.append(f"iρ (pair {s} {par(dt)})")
        elif f[0] == 'nat':
            out.append("iκ ⌜Nat⌝")
        elif f[0] == 'ford':
            comp, rhs = f[1], f[2]
            rt, _ = dexpr(rhs, k, len(fields))
            out.append(f"iκ (⌜Id⌝ ⌜Nat⌝ ({comp} ({amb(k)})) {par(rt)})")
        k += 1
    return out

def emit_iconwf(fields):
    out, k = [], 0
    for f in fields:
        if f[0] == 'rec':
            s, dd = f[1], f[2]
            dt, dv = dexpr(dd, k, len(fields))
            out.append(f"iwf-ρ (pair {s} {par(dt)}) (⊢ixP ⊢{s} {par(dv)})")
        elif f[0] == 'nat':
            out.append("iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝")
        elif f[0] == 'ford':
            comp, rhs = f[1], f[2]
            rt, rv = dexpr(rhs, k, len(fields))
            proj = "⊢fst" if comp == 'fst' else "⊢snd"
            out.append(
              f"iwf-κ (⌜Id⌝ ⌜Nat⌝ ({comp} ({amb(k)})) {par(rt)})"
              f" (icw-ford ⌜Nat⌝ ({comp} ({amb(k)})) {par(rt)})"
              f" (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI ({proj} ({damb(k)}))) (toI {par(rv)}))")
        k += 1
    return out

def par(t):
    "parenthesise only when it is not already an atom"
    return t if (" " not in t) else f"({t})"

def nest(layers, base, indent):
    """layer0 (layer1 (… (layer_{n-1} base)))  — one layer per line.

    ⚠ n-1 OPEN PARENS, NOT n.  The first layer's argument is the whole
      rest; only layers 1… are themselves parenthesised.  Getting this
      off by one produced 53 files that scope-checked as far as the first
      `iι` and then reported an unmatched `)` somewhere else entirely.
    """
    n = len(layers)
    if n == 0:
        return " " * indent + base
    lines = [" " * indent + layers[0]]
    for i in range(1, n):
        lines.append(" " * (indent + i) + "(" + layers[i])
    lines.append(" " * (indent + n) + base + ")" * (n - 1))
    return "\n".join(lines)

BANNER = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED BY `tools/gen-knot.py` — DO NOT EDIT BY HAND. ⚠⚠
--
-- Regenerate with:  python3 tools/gen-knot.py
--
-- 53 constructors over 7 sorts, one description, index `Σ' Nat Nat`.
-- The table, the encoding decisions and the two exceptions (`Var`'s
-- depth-Fording) are documented in the generator's header — read that,
-- not this file, to understand the encoding.
--
-- ⛔ `Ctx` IS DELIBERATELY NOT HERE.  `Examples/Knot/CtxD`, and the
--    generator's header says why.
------------------------------------------------------------------------
"""

def gen_desc():
    L = [BANNER, "", "{-# OPTIONS --safe #-}",
         "module DirectedHoTT.Examples.Knot.Desc where",
         "open import DirectedHoTT.Spec.Syntax",
         "  using ( Cx; ε; _∙; vz; vs",
         "        ; RTy; RTm; var; pair; fst; snd; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝",
         "        ; IMu; ICon; IDesc; iι; iρ; iκ; inil; _◂_ )",
         "open import DirectedHoTT.Examples.Knot.Sorts",
         "  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar )",
         ""]
    for name, src, fields in KNOT:
        L.append(f"-- {src}")
        L.append(f"{name} : ICon (ε ∙)")
        L.append(f"{name} =")
        L.append(nest(emit_icon(fields), "iι", 2))
        L.append("")
    L.append(f"-- ★ the description: {len(KNOT)} constructors, in table order.")
    L.append("KnotD : IDesc")
    L.append("KnotD =")
    body = " ◂ ".join(n for n, _, _ in KNOT) + " ◂ inil"
    # wrap
    line, out = "  ", []
    for tok in body.split(" "):
        if len(line) + len(tok) > 72:
            out.append(line); line = "  "
        line += tok + " "
    out.append(line.rstrip())
    L += out
    L.append("")
    L.append("-- `K (sort, depth)` — the whole knot as ONE family.")
    L.append("K : {Γ : Cx} → RTm Γ → RTy Γ")
    L.append("K i = IMu KnotD IPair i")
    return "\n".join(L) + "\n"

def gen_wf():
    L = [BANNER,
         "-- \u26a0\u26a0 THIS MODULE NEEDS THE **COMPACTING COLLECTOR**.",
         "--",
         "--   53 `IConWf`s in one module, measured cold on a 7.7 GB box.",
         "--   RE-MEASURED 2026-08-27 at 55 rows (`Ctx` was briefly a sort",
         "--   here) and the marker held:  -A64m OOM at 80s · -A64m -c 99s,",
         "--   against 76s / 104s at 53.  ⇒ ±2 rows is inside the ±12% noise",
         "--   floor: the cost is a row's TELESCOPE DEPTH, not the count.",
         "--",
         "--   `tools/sweep.sh` greps this header for the phrase above and",
         "--   switches collectors on its own (`needs_c`), which is why the",
         "--   words are spelled out rather than described.",
         "--",
         "-- \u2605 AND THE COST IS THE 53 ROWS, NOT THE ASSEMBLY.  Dropping",
         "--   `KnotWf` and keeping only the individual `IConWf`s does not",
         "--   move the number.  Splitting the module would not either",
         "--   (`agda-oom-is-a-gc-choice`: splitting measured cost-neutral);",
         "--   the driver is TELESCOPE DEPTH per row — `ordtr` alone binds",
         "--   six slots, and `agda-cost-is-context-depth` prices that at",
         "--   ~1.7\u00d7 per slot.",
         "", "{-# OPTIONS --safe #-}",
         "module DirectedHoTT.Examples.Knot.Wf where",
         "open import DirectedHoTT.Spec.Syntax",
         "  using ( Cx; ε; _∙; vz; vs",
         "        ; RTm; var; pair; fst; snd; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝",
         "        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_ )",
         "open import DirectedHoTT.Spec.Typing",
         "  using ( Ctx; ◇; _▹_",
         "        ; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝",
         "        ; IConWf; iwf-ι; iwf-ρ; iwf-κ",
         "        ; ICodeWf; icw-clo; icw-ford",
         "        ; IDescWf; idwf-nil; idwf-cons )",
         "open import DirectedHoTT.Examples.Knot.Sorts",
         "  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar",
         "        ; ⊢sTy; ⊢sTm; ⊢sDesc; ⊢sDCon; ⊢sIDesc; ⊢sICon; ⊢sVar",
         "        ; toI; fromI; ⊢ixP )",
         "open import DirectedHoTT.Examples.Knot.Desc",
         "  using ( KnotD",
         "        ; " + "\n        ; ".join(n for n, _, _ in KNOT) + " )",
         ""]
    for name, src, fields in KNOT:
        L.append(f"{name}Wf : IConWf KnotD IPair (◇ ▹ IPair) {name}")
        L.append(f"{name}Wf =")
        L.append(nest(emit_iconwf(fields), "iwf-ι", 2))
        L.append("")
    L.append("-- ★★★ …AND THE WHOLE KNOT IS WELL-FORMED.")
    L.append("KnotWf : IDescWf IPair KnotD")
    L.append("KnotWf =")
    L.append(nest([f"idwf-cons {n}Wf" for n, _, _ in KNOT], "idwf-nil", 2))
    return "\n".join(L) + "\n"


def gen_tags():
    """the constructor TAGS and their `∈ID` membership proofs.

    ⚠ SEPARATE MODULE, deliberately.  `⊢icon`'s `k ∈ID D` premise is a
      POSITION in the description, so the 53rd proof is 52 nested
      `thereID`s and the family costs O(n²) nodes.  Isolated here, that
      cost is paid once and by whoever needs it.
    """
    L = [BANNER, "", "{-# OPTIONS --safe #-}",
         "module DirectedHoTT.Examples.Knot.Tags where",
         "open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to \u2115 )",
         "open import DirectedHoTT.Spec.Syntax using ( _\u2208ID_; hereID; thereID )",
         "open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )",
         "",
         "-- \u2605 the tags, CHAINED — `tagTm-lam = suc tagTm-var`, so each is one",
         "--   symbol rather than a numeral spelled out.",
         ""]
    names = [n for n, _, _ in KNOT]
    L.append("tag" + " tag".join(n[1:] for n in names) + " : \u2115")
    prev = None
    for n in names:
        t = "tag" + n[1:]
        L.append(f"{t} = " + ("zero" if prev is None else f"suc {prev}"))
        prev = t
    L.append("")
    L.append("-- \u2605 …and the membership proofs `\u22a2icon` asks for.")
    for i, n in enumerate(names):
        t, m = "tag" + n[1:], "mem" + n[1:]
        L.append(f"{m} : {t} \u2208ID KnotD")
        L.append(f"{m} = " + "thereID (" * i + "hereID" + ")" * i)
    return "\n".join(L) + "\n"


# --------------------------------------------------------------- COVERAGE
# ⚠⚠ A MISSING ROW WOULD BE COMPLETELY SILENT.  `agda-coverage-checks-
#   functions-not-datatypes`: nothing in Agda relates this table to the
#   datatypes it encodes, so `Desc.agda`/`Wf.agda` would compile perfectly
#   with 52 rows and the encoding would simply not cover the language.
#   `tools/check-formers.sh` exists for the same hazard on the SN layer.
#   This check is that check, for this table.

FAMILY_OF = {"cTy": "RTy", "cTm": "RTm", "cDesc": "Desc", "cDCon": "DCon",
             "cIDesc": "IDesc", "cICon": "ICon", "cVar": "Var"}

def source_constructors(syntax_path):
    """the constructor names Agda actually declares, per family"""
    out, cur = {}, None
    for line in open(syntax_path):
        st = line.rstrip("\n")
        if st.startswith("data ") and st.rstrip().endswith(" where"):
            cur = st.split()[1]
            out.setdefault(cur, [])
            continue
        if st and not st[0].isspace():
            cur = None                       # left the block
            continue
        if cur is None or not st.strip() or st.strip().startswith("--"):
            continue
        head = st.strip()
        if " : " not in head:
            continue                         # a continuation line
        name = head.split(" : ")[0].strip()
        if " " in name:
            continue                         # not a constructor signature
        out[cur].append(name)
    return out

def verify(syntax_path):
    # ⚠ `Ctx` IS NOT CHECKED HERE, AND IT IS NOT UNCHECKED.  It is not a
    #   `Spec/Syntax` datatype and it is not in this table; its family
    #   lives in `Examples/Knot/CtxD`, HAND-written, and its coverage is
    #   enforced by `enCtx`'s clauses — Agda's coverage checker checks
    #   FUNCTIONS, so a hand-written table with a hand-written map is
    #   already guarded.  This check exists because a GENERATED table and
    #   a GENERATED map would omit a row in both at once, silently.
    src = source_constructors(syntax_path)
    mine = {}
    for name, decl, _ in KNOT:
        fam = FAMILY_OF[name.split("-")[0]]
        mine.setdefault(fam, []).append(decl.split(" : ")[0].strip())
    bad = 0
    for fam in ["RTy", "RTm", "Desc", "DCon", "IDesc", "ICon", "Var"]:
        have, want = set(mine.get(fam, [])), set(src.get(fam, []))
        if have != want:
            bad = 1
            print(f"  ✗ {fam}: missing {sorted(want - have)} "
                  f"· extra {sorted(have - want)}")
        else:
            print(f"  ok {fam:6s} — {len(want)} constructor(s)")
    return bad


# ============================ LAYER 1: SMART CONSTRUCTORS ==================
# ★ For each row, the object-level term and a typing lemma at an ARBITRARY
#   depth `num n`.  See `Examples/Knot/Build`'s header for why the depth is a
#   NUMERAL and what the three cast helpers do.
#
# ⚠ THE TWO `Var` ROWS ARE NOT EMITTED HERE.  They Ford the DEPTH as well as
#   the tag, so their ambient is `num (suc n)` and their second constraint
#   names a BOUND FIELD — neither of which this emitter models.  Hand-written
#   in `Knot/Build`.
SORT = {"cTy":"sTy","cTm":"sTm","cDesc":"sDesc","cDCon":"sDCon",
        "cIDesc":"sIDesc","cICon":"sICon","cVar":"sVar"}

def dnsucs(t, inner): return ("⊢nsuc (" * t) + inner + (")" * t)

def actions(level, j):
    # ⚠ the extS exponent is keyed to the FIELD, not the level: a
    #   substitution hitting a term at depth p needs extS^(p-1), and the
    #   term starts at depth j and loses one per substitution.  Keying it
    #   to the level type-checks for k=0/k=1 and then goes wrong.
    return [("sub", i, j - 1 - i) for i in range(level - 1, -1, -1)] + [("ren",)] * j

def sigma(i, e):
    s = f"single a{i}"
    for _ in range(e): s = f"extS ({s})"
    return s

def term_of(acts, NN="n", V=False):
    t = "d" if V else f"num {NN}"
    for a in reversed(acts):
        t = f"renTm vs ({t})" if a[0] == "ren" else f"subTm ({sigma(a[1],a[2])}) ({t})"
    return t

def eq_of(acts, NN="n"):
    if not acts: return "refl"
    a, rest = acts[0], acts[1:]
    if a[0] == "ren":
        return f"trans (cong (renTm vs) ({eq_of(rest, NN)})) (num-ren vs {NN})"
    s = sigma(a[1], a[2])
    return f"trans (cong (subTm ({s})) ({eq_of(rest, NN)})) (num-sub ({s}) {NN})"

def depth_expr(E, V=False):
    """the depth a field's index sits at.

    ⚠⚠ THE TWO MODES DIFFER IN WHAT THEY CAN SAY, not merely in syntax.
      `num n` is renaming-INVARIANT, so every position under a binder has
      to be RECOGNISED as still being `num n` — that is what the
      `num-ren`/`num-sub` chains do.  `var x` is renaming-COVARIANT: it
      simply MOVES, and moving is what `⊢wk` already does.
      ⇒ so the variable form needs no equations at all, and a
        substitution `single a` applied to `var (vs x)` COMPUTES back to
        `var x`.  Every chain the numeral form pays for collapses.
    ⚠ A `lit` depth stays a NUMERAL in both modes — it is a fixed depth,
      not the row's own."""
    if E[0] == "lit":  return f"num {E[1]}"
    if not V:
        if E[0] == "D":    return "num n"
        if E[0] == "sucD": return "num (" + "suc (" * E[1] + "n" + ")" * E[1] + ")"
        raise ValueError(E)
    if E[0] == "D":    return "d"
    if E[0] == "sucD": return "nsuc (" * E[1] + "d" + ")" * E[1]
    raise ValueError(E)

def _dwk(r):
    "the depth derivation `r` weakenings in"
    return "⊢wk (" * r + "dd" + ")" * r

def _surplus(acts):
    "renamings that survive the substitutions"
    return max(sum(1 for a in acts if a[0] == "ren")
               - sum(1 for a in acts if a[0] == "sub"), 0)

def depderiv(acts, en, V):
    """the DEPTH's derivation at a position reached by `acts`.

    ★ numeral: RECOGNISE it — `num n` is renaming-invariant, so every
      position is still `num n` and `⊢numAt` cashes the chain.
    ★ general: MOVE it — `⊢wk` per surviving renaming, and the chain
      says the substitutions cancelled the rest."""
    if not V: return "⊢num n" if en == "refl" else f"⊢numAt n {en}"
    if en == "refl": return _dwk(_surplus(acts))
    return f"⊢natAt {en} ({_dwk(_surplus(acts))})"

def wtimes(r, t):
    return "w (" * r + t + ")" * r

def eq_gen(acts):
    """`term_of(acts)` ≡ `wʳ d`, for an ARBITRARY depth `d`.

    ⚠⚠ THIS IS WHERE A GENERAL DEPTH COSTS WHAT A NUMERAL DOES NOT.
      `num-sub σ n` cancels a substitution at ANY `σ`, because `num n` is
      closed.  For a general `d` the cancellation depends on `σ`'s
      SHAPE — `subTm (extSᵉ (single a)) (wᵉ⁺¹ d) ≡ wᵉ d` — so it is the
      `sub-wᵉ` ladder, one rung per binder crossed.  ★ Measured: the
      deepest exponent the table needs is 4, and `Lib/Wk` stops at
      `sub-w⁴`.  Exactly deep enough, which is not luck: both are
      bounded by the widest row's field count."""
    # ⚠ NEVER EMIT `cong f refl`.  A bare `refl` under a `cong` has
    #   nothing to fix its type, so the metas never solve — and the error
    #   surfaces far from here, as an unsolved constraint on a
    #   `subTm (single a0) (renTm vs _x)`.  A pure-renaming prefix IS
    #   `refl`, because `w` is `renTm vs`.
    if not acts or all(a[0] == "ren" for a in acts): return "refl"
    a, rest = acts[0], acts[1:]
    inner = eq_gen(rest)
    if a[0] == "ren":
        return "refl" if inner == "refl" else f"cong (renTm vs) ({inner})"
    i, e = a[1], a[2]
    sw = "wk-single {v = a%d} d" % i
    if e > 0:
        lad = "sub-w" + ("" if e == 1 else "\u00b2\u00b3\u2074"[e - 2])
        sw = (f"trans ({lad} {{σ = single a{i}}} (w d)) "
              f"({'cong w (' * e}{sw}{')' * e})")
    if inner == "refl": return sw
    return f"trans (cong (subTm ({sigma(i, e)})) ({inner})) ({sw})"

def entry_ty(f, sX, dd, NN="n", dd0=None):
    "⚠ `dd`/`dd0` are the DEPTH DERIVATIONS, already built for the mode."
    if f[0] == "nat":  return "ty-El ⊢⌜Nat⌝"
    if f[0] == "ford":
        if f[1] == "snd":            # the DEPTH ford — `Var` only
            return (f"ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢snd (⊢ixP ⊢{sX} ({dd}))))"
                    f" (toI (⊢nsuc ({dd0}))))")
        return (f"ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢{sX} ({dd})))) (toI ⊢{sX}))")
    s, E = f[1], f[2]
    if E[0] == "lit": return f"ty-IMu KnotWf (⊢ixP ⊢{s} (⊢num {E[1]}))"
    if E[0] == "fld": return f"ty-IMu KnotWf (⊢ixP ⊢{s} ({dd0}))"
    inner = f"⊢snd (⊢ixP ⊢{sX} ({dd}))"
    if E[0] == "sucD": inner = dnsucs(E[1], inner)
    return f"ty-IMu KnotWf (⊢ixP ⊢{s} ({inner}))"

def component(f, j, sX, en, mangled, en0=None, eA=None):
    if f[0] == "nat":  return f"toI d{j}"
    if f[0] == "ford":
        if f[1] == "snd":
            return (f"⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (snd (pair {sX} z))"
                    f" (nsuc (num n)))) (sym {eA}))"
                    f" (fordSnd (⊢num n))")
        return f"fordFst ⊢{sX}"
    E = f[2]
    if E[0] == "lit":  return f"d{j}"
    if E[0] == "fld":  return (f"d{j}" if en0 == "refl" else f"kCast (sym {en0}) d{j}")
    red = f"βsnd {sX} ({mangled})"
    t = E[1] if E[0] == "sucD" else 0
    red = "ξ-nsuc (" * t + red + ")" * t
    if en == "refl":
        cast = f"d{j}"
    else:
        inner = en if t == 0 else "(" + "cong nsuc (" * t + en + ")" * t + ")"
        cast = f"kCast (sym {inner}) d{j}"
    return f"ixConv (ξ-pairʳ ({red})) ({cast})"

def emit_row(name, decl, fields, V=False):
    """one constructor and its typing.

    ⚠⚠ `V=True` emits the VARIABLE-DEPTH twin, and it is not cosmetic:
      a judgement row's depth is a BOUND FIELD, so every constructor a
      rule mentions needs this form.  See `depth_expr` for why the two
      cannot be one lemma."""
    sX, m = SORT[name.split("-")[0]], len(fields)
    nm = name[1:]
    nargs = [j for j, f in enumerate(fields) if f[0] in ("rec", "nat")]
    L = [f"-- {decl}"]
    if not V:
        L.append(f"{nm}K : {{Γ : Cx}} → " + "RTm Γ → " * len(nargs) + "RTm Γ")
        pay = "unit"
        for j in reversed(range(m)):
            c = f"a{j}" if fields[j][0] in ("rec","nat") else f"(idrefl ⌜Nat⌝ {sX})"
            pay = f"pair {c} ({pay})" if pay != "unit" else f"pair {c} unit"
        L.append(f"{nm}K " + " ".join(f"a{j}" for j in nargs) + f" = icon tag{nm} ({pay})")
        L.append("")
    eqs = {}
    def en(acts):
        if not acts: return "refl"
        t = term_of(acts, V=V)
        if t not in eqs: eqs[t] = (f"e{len(eqs)}", acts)
        return eqs[t][0]
    def dd(acts):
        return depderiv(acts, en(acts), V)
    def needs_eq(f):
        return f[0] == "ford" or (f[0] == "rec" and f[2][0] in ("D", "sucD"))
    def B_of(k):
        if k == m - 1: return "ty-Unit"
        B = "ty-Unit"
        for j in reversed(range(k + 1, m)):
            d = dd(actions(k, j)) if needs_eq(fields[j]) else depderiv([], "refl", V)
            B = f"ty-Σ ({entry_ty(fields[j], sX, d, dd0=d)}) ({B})"
        return B
    Bs, cs = [], []
    for k in range(m):
        Bs.append(B_of(k))
        a = actions(k, k)
        e = (en(a) if (fields[k][0] == "rec" and fields[k][2][0] in ("D", "sucD"))
             else "refl")
        cs.append(component(fields[k], k, sX, e, term_of(a, V=V)))
    prem = ["Δ ⊢ a{} ∷ Nat".format(j) if fields[j][0] == "nat"
            else f"Δ ⊢ a{j} ∷ K (pair {fields[j][1]} ({depth_expr(fields[j][2], V)}))"
            for j in nargs]
    imp = " ".join(f"a{j}" for j in nargs)
    sig = "⊢%sK%s" % (nm, "v" if V else "")
    if V:
        # ⚠ THE DEPTH IS AN EXPLICIT ARGUMENT, not an implicit to be
        #   unified.  `sucs j (var x)` would not unify against
        #   `nsuc (var y)` — `sucs` is a recursive function — and that is
        #   what made the `var x` form unusable under a binder.
        L.append(f"{sig} : {{Δ : Ctx}} (d : RTm ⌊ Δ ⌋)"
                 + (f" {{{imp} : RTm ⌊ Δ ⌋}}" if nargs else "") + " →")
        L.append("        Δ ⊢ d ∷ Nat →")
    else:
        L.append(f"{sig} : {{Δ : Ctx}} (n : ℕ)"
                 + (f" {{{imp} : RTm ⌊ Δ ⌋}}" if nargs else "") + " →")
    for p in prem: L.append(f"        {p} →")
    L.append(f"        Δ ⊢ {nm}K " + " ".join(f"a{j}" for j in nargs)
             + f" ∷ K (pair {sX} ({depth_expr(('D',), V)}))")
    # ⚠ ALL IMPLICITS FIRST.  The variable form binds `x` alongside the
    #   field implicits, so its explicit arguments (`dx`, then the
    #   premises) all come after them — unlike the numeral form, whose
    #   `n` is explicit and precedes the field implicits.
    flds = [f"{{a{j} = a{j}}}" for j in nargs]
    ds   = [f"d{j}" for j in nargs]
    lhs  = (["d"] + flds + ["dd"] + ds) if V else (["n"] + flds + ds)
    L.append(f"{sig} " + " ".join(lhs) + " =")
    L.append(f"  ⊢icon KnotWf mem{nm} (⊢ixP ⊢{sX} ({depderiv([], 'refl', V)}))")
    ind = "    "
    for k in range(m):
        L.append(f"{ind}(⊢pair ({Bs[k]})")
        L.append(f"{ind}       ({cs[k]})")
        ind += " "
    L.append(f"{ind}⊢unit" + ")" * m)
    if eqs:
        L.append("  where")
        for t, (e, acts) in eqs.items():
            if V:
                L.append(f"    {e} : {t} ≡ {wtimes(_surplus(acts), 'd')}")
                L.append(f"    {e} = {eq_gen(acts)}")
            else:
                L.append(f"    {e} : {t} ≡ num n")
                L.append(f"    {e} = {eq_of(acts)}")
    L.append("")
    return L


CTORS_HDR = """""" + BANNER + """-- \u2605\u2605\u2605 THE KNOT'S CONSTRUCTORS AS DERIVED RULES.
--
--     \u22a2Tm-lamK : (n : \u2115) \u2192 \u0394 \u22a2 b \u2237 K (1 , num (suc n))
--                        \u2192 \u0394 \u22a2 Tm-lamK b \u2237 K (1 , num n)
--
-- \u26a0 THE TWO `Var` ROWS ARE NOT HERE.  They Ford the DEPTH as well as the
--   tag, so their ambient index is `num (suc n)` and their constraint names
--   a BOUND FIELD.  Hand-written in `Knot/Build`.
--
-- Read `Knot/Build`'s header for why the depth is a NUMERAL and what the
-- three cast helpers are for.

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Ctors where
open import normalizer.Syntax.Types using ( _\u2261_; refl; sym; trans; cong; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to \u2115 )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; \u03b5; _\u2219; vz; vs
        ; RTy; RTm; El; Unit; Nat; \u03a3'; IMu
        ; var; pair; fst; snd; unit; nzero; nsuc; \u231cNat\u231d; \u231cId\u231d; idrefl; icon
        ; Ren; Sub; renTm; subTm; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; \u25c7; _\u25b9_; \u230a_\u230b; single
        ; _\u22a2_\u2237_; _\u22a2ty_; \u22a2var; here; there; \u22a2conv
        ; \u22a2pair; \u22a2fst; \u22a2snd; \u22a2unit; \u22a2nzero; \u22a2nsuc; \u22a2\u231cNat\u231d; \u22a2\u231cId\u231d; \u22a2idrefl; \u22a2icon
        ; ty-El; ty-Unit; ty-Nat; ty-\u03a3; ty-IMu
        ; _\u27f6_; \u03b2fst; \u03b2snd; \u03be-pair\u02b3; \u03be-nsuc
        ; _\u2245\u1d40_; csym\u1d40; ctrn\u1d40; cred\u1d40; El-\u231cId\u231d; \u03be-El; \u03be-IMu; \u03be-\u231cId\u231d\u02e1 )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; \u22a2sTy; \u22a2sTm; \u22a2sDesc; \u22a2sDCon; \u22a2sIDesc; \u22a2sICon; \u22a2sVar
        ; toI; fromI; \u22a2ixP; num; \u22a2num; num-ren; num-sub )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Tags
open import DirectedHoTT.Examples.Knot.Terms using ( ixConv; fordFst; tyFordFst )
open import DirectedHoTT.Examples.Knot.Build using ( tyCast; \u22a2numAt; kCast )

"""

CTORSV_HDR = """""" + BANNER + """-- \u2605\u2605\u2605 THE SAME CONSTRUCTORS AT A **VARIABLE** DEPTH.
--
--     \u22a2Tm-lamKv : \u0394 \u22a2 var x \u2237 Nat \u2192 \u0394 \u22a2 b \u2237 K (sTm , nsuc (var x))
--                          \u2192 \u0394 \u22a2 Tm-lamK b \u2237 K (sTm , var x)
--
-- \u26a0\u26a0 WHY BOTH FORMS EXIST, and it is not a duplication.  A JUDGEMENT
--   ROW's depth is a BOUND FIELD \u2014 a variable \u2014 while the adequacy map's
--   is an Agda NUMERAL.  Neither subsumes the other:
--
--     `num n` is renaming-INVARIANT, so every position under a binder has
--     to be RECOGNISED as still being `num n`.  That is what `Knot/Ctors`'
--     `num-ren`/`num-sub` chains do, and there is one per field position.
--
--     `var x` is renaming-COVARIANT: it simply MOVES, which is what `\u22a2wk`
--     already does.  And a substitution `single a` applied to `var (vs x)`
--     COMPUTES back to `var x`.
--
--   \u2605 \u21d2 EVERY CHAIN THE NUMERAL FORM PAYS FOR COLLAPSES HERE.  These
--     derivations carry no `where` block at all.  `\u22a2Var-vzKv` in
--     `Knot/Build` was the first sighting; this module is that observation
--     applied to all 51 rows.
--
-- \u26a0 THE TWO `Var` ROWS ARE STILL NOT HERE \u2014 they Ford the DEPTH as well
--   as the tag.  `Knot/Build` has them, and has had the `v` forms since
--   before this module existed.
--
-- \u2605 GENERATED FROM THE SAME TABLE by the same emitter, with one flag.
--   The numeral output is byte-identical to what it was before the flag
--   existed, which is the control that the refactor changed nothing.

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.CtorsV where
open import normalizer.Syntax.Types using ( _\u2261_; refl; sym; trans; cong; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to \u2115 )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; \u03b5; _\u2219; vz; vs; Var
        ; RTy; RTm; El; Unit; Nat; \u03a3'; IMu
        ; var; pair; fst; snd; unit; nzero; nsuc; \u231cNat\u231d; \u231cId\u231d; idrefl; icon
        ; Ren; Sub; renTm; subTm; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; \u25c7; _\u25b9_; \u230a_\u230b; single
        ; _\u22a2_\u2237_; _\u22a2ty_; \u22a2var; here; there; \u22a2conv; wk-single
        ; \u22a2pair; \u22a2fst; \u22a2snd; \u22a2unit; \u22a2nzero; \u22a2nsuc; \u22a2\u231cNat\u231d; \u22a2\u231cId\u231d; \u22a2idrefl; \u22a2icon
        ; ty-El; ty-Unit; ty-Nat; ty-\u03a3; ty-IMu
        ; _\u27f6_; \u03b2fst; \u03b2snd; \u03be-pair\u02b3; \u03be-nsuc
        ; _\u2245\u1d40_; csym\u1d40; ctrn\u1d40; cred\u1d40; El-\u231cId\u231d; \u03be-El; \u03be-IMu; \u03be-\u231cId\u231d\u02e1 )
open import DirectedHoTT.Metatheory.SubjectReduction using ( \u22a2wk )
open import DirectedHoTT.Lib.Wk using ( w; sub-w; sub-w\u00b2; sub-w\u00b3; sub-w\u2074 )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; \u22a2sTy; \u22a2sTm; \u22a2sDesc; \u22a2sDCon; \u22a2sIDesc; \u22a2sICon; \u22a2sVar
        ; toI; fromI; \u22a2ixP; num; \u22a2num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Tags
open import DirectedHoTT.Examples.Knot.Terms using ( ixConv; fordFst; tyFordFst )
open import DirectedHoTT.Examples.Knot.Build using ( tyCast; kCast )
open import DirectedHoTT.Examples.Knot.Ctors
  using ( """ + "; ".join(n[1:] + "K" for n, _, _ in KNOT if not n.startswith("cVar-")) + """ )

-- ★ the depth, RECOGNISED at a position it was moved to.  `\u22a2numAt`'s
--   general twin: `Knot/Build`'s version bakes in `\u22a2num`, which only a
--   numeral depth has.
\u22a2natAt : {\u0393 : Ctx} {t u : RTm \u230a \u0393 \u230b} \u2192 t \u2261 u \u2192 \u0393 \u22a2 u \u2237 Nat \u2192 \u0393 \u22a2 t \u2237 Nat
\u22a2natAt eq d = subst (\u03bb z \u2192 _ \u22a2 z \u2237 Nat) (sym eq) d

"""

def gen_ctorsv():
    out = [CTORSV_HDR]
    for nm, d, f in KNOT:
        if nm.startswith("cVar-"): continue
        out += emit_row(nm, d, f, V=True)
    return "\n".join(out) + "\n"


def gen_ctors():
    out = [CTORS_HDR]
    for nm, d, f in KNOT:
        if nm.startswith("cVar-"): continue
        out += emit_row(nm, d, f)
    return "\n".join(out) + "\n"


MAP_HDR = """""" + BANNER + """-- \u2605\u2605\u2605 THE ADEQUACY MAP.
--
--     enTm  : RTm \u0393 \u2192 RTm \u0393\'
--     \u22a2enTm : (t : RTm \u0393) \u2192 \u0394 \u22a2 enTm t \u2237 K (sTm , num (len \u0393))
--
-- \u2605 WHAT IT IS FOR.  `Knot/Wf` says the 53 rows are well formed;
--   `Knot/Terms` says ONE term encodes, by hand.  Neither says the
--   description IS the knot.  These clauses do: a row with a swapped field
--   order or a wrong index stays well-formed and inhabited, and simply
--   encodes a DIFFERENT language \u2014 invisible until something has to map
--   every constructor through it.
--
-- \u26a0 THE THREE CLOSED SORTS take the depth as a PARAMETER.  `Desc`,
--   `DCon` and `IDesc` carry no context, so there is no Agda type to read a
--   depth off; they are inhabited at EVERY depth and the caller says which.
--
-- \u2605\u2605 MEASURED, NOT ASSERTED.  Set `natrec`'s step field to `sucD 1`
--   instead of `sucD 2` \u2014 one wrong index in the table \u2014 and:
--     `Knot/Wf`     still passes (rc 0): a wrong index is WELL-FORMED;
--     `Knot/Ctors`  still passes (rc 0): its constructors still derive;
--     `Knot/Map`    FAILS: `nsuc (num (len \u0393)) != num (num (len \u0393))`.
--   So the map catches exactly what nothing before it could.
--
-- \u26a0 THE `Var` CLAUSES MATCH ON THE CONTEXT.  `vz : Var (\u0393 \u2219)` exists only
--   at a successor depth, so its clause splits the implicit `\u0393` \u2014 which is
--   exactly the depth-Fording of `cVar-vz`, on the Agda side.

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Map where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to \u2115 )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing
  using ( Ctx; \u25c7; _\u25b9_; \u230a_\u230b; _\u22a2_\u2237_ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar; num; \u22a2num; len )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Build
  using ( Var-vzK; \u22a2Var-vzK; Var-vsK; \u22a2Var-vsK )

"""

# ============================ THE JUDGEMENT-RULE TRANSLATOR ================
# ★★★ THE RULES ARE PARSED OUT OF `Spec/Typing.agda`, NOT TRANSCRIBED.
#
# ⚠ 166 hand-written table entries is 166 chances to name the wrong
#   variable — the exact error class `LookupGen` exists to catch, and the
#   one the generator's header already argues is "a transcription error
#   waiting to happen".  The Agda-former → knot-constructor map is
#   derived from `KNOT`'s own `decl` strings, so nothing is typed twice.
#
# ⚠⚠ AND THE COVERAGE REPORT IS THE POINT.  A rule this cannot translate
#   is NAMED, in the generator's output and in the generated file's
#   header.  Silently emitting 65 of 73 rows would be
#   `verification-that-covers-less-than-it-claims`.

# a binder's type → (knot sort, how many binders deeper than the row)
BINDER_SORT = {
    "RTm Γ":          ("sTm", 0),
    "RTm (Γ ∙)":      ("sTm", 1),
    "RTm ((Γ ∙) ∙)":  ("sTm", 2),
    # ★ the TYPE-level judgements bind `RTy`, at the same depths.
    "RTy Γ":          ("sTy", 0),
    "RTy (Γ ∙)":      ("sTy", 1),
    "RTy ((Γ ∙) ∙)":  ("sTy", 2),
    "Desc":           ("sDesc", 0),
    "DCon":           ("sDCon", 0),
    "IDesc":          ("sIDesc", 0),
    # ⚠ `RTy ε` is a CLOSED type — sort `sTy` at depth ZERO, not at the
    #   row's depth.  Typing it as the row's depth compiles and means
    #   something else.
    "RTy ε":          ("sTy", "closed"),
    # ⚠ `ICon (ε ∙)` is at an ABSOLUTE depth 1, not one deeper than the
    #   row.  Without it `_∈ID_`'s two rows silently did not translate and
    #   `InIDD` shipped as `inil` — a WELL-FORMED EMPTY DESCRIPTION, which
    #   is exactly the hazard `⊢lkVz`'s note names.
    "ICon (ε ∙)":     ("sICon", ("abs", 1)),
}
NAT_BINDER = {"ℕ"}

def _agda_ctor_map():
    "Agda term former → knot smart constructor, from the table itself"
    return {d.split(":")[0].strip(): n[1:] + "K" for n, _, _ in KNOT
            for d in [next(dd for nn, dd, _ in KNOT if nn == n)]}

def rules_of(path, dataname):
    src = open(path, encoding="utf-8").read().split("\n")
    i = next(k for k, l in enumerate(src) if l.startswith("data " + dataname))
    out, j, cur = [], i + 1, None
    while j < len(src):
        l = src[j]
        if l and not l[0].isspace(): break
        if re.match(r"^  [^ \-]", l):
            if cur: out.append(cur)
            cur = l.strip()
        elif cur is not None and l.startswith("    ") and not l.strip().startswith("--"):
            cur += " " + l.strip()
        j += 1
    if cur: out.append(cur)
    return [r for r in out if ":" in r]

def _split_top(s, sep="→"):
    d, parts, cur = 0, [], ""
    for ch in s:
        if ch in "({": d += 1
        elif ch in ")}": d -= 1
        if ch == sep and d == 0: parts.append(cur); cur = ""
        else: cur += ch
    parts.append(cur)
    return [p.strip() for p in parts]

def _groups(p):
    """balanced (…)/{…} groups, or None if `p` is not purely binders.
    ⚠ A REGEX CANNOT DO THIS: `RTm (Γ ∙)` has nested parens, and a
      `[^)}]` class stops at the inner one.  Two attempts reported 31/73
      and 39/73 coverage — both were the regex, not the rules."""
    out, i = [], 0
    while i < len(p):
        if p[i].isspace(): i += 1; continue
        if p[i] not in "({": return None
        d, j = 0, i
        while j < len(p):
            if p[j] in "({": d += 1
            elif p[j] in ")}":
                d -= 1
                if d == 0: break
            j += 1
        if j >= len(p): return None
        out.append(p[i+1:j]); i = j + 1
    return out

def _tokens(s):
    # ⚠ DROP EXPLICIT IMPLICIT ARGUMENTS.  `⌜base⌝ {Γ}` is the same term
    #   as `⌜base⌝`; left in, `{Γ}` reads as an unmapped constructor and
    #   four rules look like a missing library.
    s = re.sub(r"\{[^{}]*\}", " ", s)
    return re.findall(r"[()]|[^\s()]+", s)

def _parse_spine(ts):
    def atom(i):
        if ts[i] == "(":
            e, i = spine(i + 1)
            return e, i + 1
        return ("a", ts[i]), i + 1
    def spine(i):
        args = []
        while i < len(ts) and ts[i] != ")":
            e, i = atom(i); args.append(e)
        return (args[0] if len(args) == 1 else ("ap", args)), i
    e, _ = spine(0)
    return e

# ★★★ A PREMISE THAT IS A **BOOLEAN FUNCTION OF THE SYNTAX**.
#
#     hrefl-pw : … → pw? C ≡ true → …
#
# ⚠ IT IS NOT A JUDGEMENT, so it is not an `iρ` and not a `FOREIGN_RELS`
#   κ field.  It is a FORD: a κ field carrying `⌜Id⌝ ⌜Nat⌝ (fK ⟨i⟩ c) 1`,
#   which is exactly the shape the row's own DEPTH ford already has —
#   `icw-ford : (c a b : RTm Θ) → ICodeWf (⌜Id⌝ c a b)` is general, so
#   nothing new is needed on the well-formedness side.
#
# ★ booleans are `0`/`1` at the object level, matching `Knot/Pw`'s
#   constant-`Nat` motive.
# name → (object-level function, its typing lemma, the argument's sort)
BOOL_PREM = {"pw?":   ("pwK",   "⊢pwK",   "sTm"),
             "stkA?": ("stkAK", "⊢stkAK", "sTm"),
             "stkC?": ("stkCK", "⊢stkCK", "sTm"),
             "flat?": ("flatK", "⊢flatK", "sTm")}

def TBOOL(app, lit): return ('tbool', app, lit)

# ★★★ THE MERGED BLOCK — seven judgements, ONE description.  `Spec/Typing`
#   forward-declares all of them together (663–712) and defines them at
#   714–1031; the cycle is real (`⊢con → DescWf → dwf-κ → ◇ ⊢ c ∷ U`), so
#   this is not a choice.  See JUDGEMENT-ATTEMPTS §10.1.
# tag → (Agda name, arity of its SUBJECT list)
MERGED = [(0, "_⊢ty_", None), (1, "_⊢_∷_", None),
          (2, "DConWf", 1), (3, "DescWf", 1), (4, "IConWf", 4),
          (5, "ICodeWf", 1), (6, "IDescWfFrom", 3)]
WF_HEADS = {n: a for _, n, a in MERGED if a is not None}
WF_TAG   = {n: t for t, n, _ in MERGED}

# ★★★ AND THE `Wf` JUDGEMENTS BIND DESCRIPTIONS **CLOSED**, at absolute 0.
#
# ⚠⚠ `KNOT` carries `Desc`/`DCon`/`IDesc` FIELDS at the AMBIENT depth, so
#   the two conventions collide and they are NOT symmetric — `Knot/IxD`'s
#   header has the table.  Short version: under the ambient convention
#   `idwf-cons` reads one `D` at its premise's depth 1 AND at the row's
#   variable, needing a STRENGTHENING that does not exist; under this one
#   the knot's ambient copy is recovered by `εwkK` (`0 → n`), which does.
# ⚠ SCOPED TO THIS BLOCK.  `BINDER_SORT`'s ambient entries stay, because
#   the `_⟶_` family's 71 green rows are written against them.
WF_BINDER_SORT = {
    "DCon":           ("sDCon",  "closed"),
    "Desc":           ("sDesc",  "closed"),
    "IDesc":          ("sIDesc", "closed"),
    "RTy ε":          ("sTy",    "closed"),
    "RTm ε":          ("sTm",    "closed"),
    "Ctx":            ("ctx",    0),
    "ICon (⌊ Θ ⌋ ∙)": ("sICon",  1),
    "ICon (ε ∙)":     ("sICon",  ("abs", 1)),
    "RTm ⌊ Θ ⌋":      ("sTm",    0),
    "RTm Θ":          ("sTm",    0),
    "Cx":             ("ctx",    0),
}
# ★ `{Θ : Cx}` — `ICodeWf`'s ambient SCOPE — becomes the flat `Ctx` slot.
#
# ⚠ THAT IS A STRENGTHENING, AND IT IS DELIBERATE.  The rule is indexed by
#   an ERASED scope; the encoding indexes it by a TYPED context whose
#   erasure is that scope.  Nothing in `ICodeWf`'s three rows reads the
#   types, so the family is UNIFORM in them and inhabitation is unchanged
#   — and it is what lets `iwf-κ`'s premise `ICodeWf κ` hand over the very
#   `Θ` it already has in scope, instead of inventing one.
WF_SKIP = set()

# ⚠⚠ WHICH `Wf` ARGUMENT IS A **CONTEXT** and not a term.  Reading
#   `IConWf`'s `Θ` as a term emits `▹` as an unmapped head — and, before
#   the `chk` fix below, emitted NOTHING and said nothing.
WF_CTXARG = {"IConWf": 2}

def _infix(args, CT):
    """`a ⊕ b` → `_⊕_ a b` when `_⊕_` is a knot constructor.

    ⚠⚠ WITHOUT THIS `dwf-cons` EMITTED `DescWf C` FOR `DescWf (C ◃ E)`.
      `_parse_spine` makes the LEFT operand the head, `_val`'s fallback
      returned it as a bare binder, and the row TYPECHECKED — a different
      judgement, silently.  The `chk` walk did not catch it because it
      never looked at a `wf` part's subjects at all."""
    if len(args) == 3 and args[1][0] == "a":
        nm = "_%s_" % args[1][1]
        if nm in CT: return [("a", nm), args[0], args[2]]
    return args

def _argsplit(p):
    "a spine at TOP-LEVEL whitespace, respecting (…) and {…}"
    out, cur, d = [], "", 0
    for ch in p.strip():
        if ch in "({": d += 1
        elif ch in ")}": d -= 1
        if ch.isspace() and d == 0:
            if cur: out.append(cur); cur = ""
        else: cur += ch
    if cur: out.append(cur)
    return out

def _wf_rule(r):
    """a `Wf` rule → (name, sorts, deps, body-parts).

    ★ Unlike `_⊢_∷_`, these judgements TYPE their binders (`{C : DCon}`),
      so nothing has to be inferred — and nothing may be guessed."""
    name, ty = r.split(":", 1)
    sorts, deps, body = {}, {}, []
    for part in _split_top(ty):
        g = _groups(part.strip())
        if g is None:
            body.append(part.strip()); continue
        for grp in g:
            if ":" not in grp: return (name.strip(), None, "binder %r" % grp)
            nms, t = grp.split(":", 1); t = t.strip()
            if t in WF_SKIP: continue
            if t not in WF_BINDER_SORT:
                return (name.strip(), None, "binder type %r" % t)
            srt, dp = WF_BINDER_SORT[t]
            for nm in nms.split(): sorts[nm], deps[nm] = srt, dp
    return (name.strip(), sorts, deps, body)

# ★★★ A PREMISE THAT IS A **UNARY FOREIGN JUDGEMENT**.
#
#     ⊢tr : … → NoNatC c → …
#
# ⚠ AND IT IS NOT A `BOOL_PREM`.  `NoNatC` looks like `pw?` at the call
#   site — one argument, no relation symbol — but it is an inductive
#   PREDICATE, so it is an `iκ` carrying a `⌜IMu⌝` of its OWN
#   description, exactly as a `≅ᵀ` premise is.  Reading it as a boolean
#   would owe a proof that the two agree, which the rule never asked for.
# Agda name → its description in `FOREIGN`
UNARY_PREM = {"NoNatC": "NoNatCD"}

# ★ A BINARY foreign judgement written INFIX — `k ∈D D`.  Its subjects are
#   CLOSED (a numeral and a description), so the citation is at depth 0.
# Agda symbol → its description in `FOREIGN`
BINARY_PREM = {"∈D": "InDD", "∈ID": "InIDD"}

# ★★★ DEFINED ALIASES, EXPANDED BEFORE TRANSLATION.
#
# ⚠ `iinst` is not a primitive — `Spec/Typing:155` defines it as TWO
#   substitutions, and the object level already has all three pieces
#   (`subTyAtK`, `singleK`, `extNK`).  Reading it as an unmapped head made
#   `⊢ielim` look like it needed a NEW function when it needed a LOOKUP.
# ⚠ Same shape as `IDescWf I D = IDescWfFrom D I D`, which cost a silent
#   argument SWAP when it was read positionally.  ⇒ expansions live here,
#   spelled out, so the definition is written down once.
# name → (arity, template over %s)
_ALIAS = {
    "iinst":   (3, "subTy (single %s) (subTy (extS (single %s)) %s)",
                (1, 0, 2)),          # iinst j t M
    "methsTy": (3, "methsTyFrom %s %s zero %s", (0, 1, 2)),
}

def _expand(txt):
    """expand a defined alias at the HEAD of an expression, once."""
    a = _argsplit(txt)
    if not a or a[0] not in _ALIAS: return txt
    n, tpl, order = _ALIAS[a[0]]
    if len(a) - 1 != n: return txt
    args = ["(%s)" % x for x in a[1:]]
    return tpl % tuple(args[i] for i in order)

def translate_rule(r, CT, REL="⟶", FOREIGN_RELS=(), arity=2):
    """(name, binders, prems, lhs, rhs) or (name, None, reason).

    ⚠ THE RELATION SYMBOL IS A PARAMETER.  Splitting on `⟶` when the
      judgement is `_⟶ᵀ_` leaves a stray `ᵀ` in the right-hand side, and
      the failure reads as an unmapped constructor — 26 of them, which
      looks like a missing library and is a one-character bug."""
    name, ty = r.split(":", 1)
    name = name.strip()
    parts = _split_top(ty)
    binders, prems, foreign, bools = [], [], [], []

    # ★★★ A UNARY JUDGEMENT IS WRITTEN PREFIX, NOT INFIX.  `NoNatC c` has
    #   no relation symbol BETWEEN two subjects — the name IS the head.
    #   ⚠ Everything downstream is arity-agnostic already (the index is a
    #     telescope, and `_jrows` builds it from a list), so this is the
    #     only place that had to learn the difference.
    def _un(p):
        "the single subject of `REL t`, or None"
        q = p.strip()
        if arity != 1 or not q.startswith(REL): return None
        r_ = q[len(REL):]
        return r_.strip() if (r_ == "" or r_[0].isspace()) else None

    for p in parts[:-1]:
        gs = _groups(p)
        if gs is None:
            if arity == 1:
                u = _un(p)
                if u is not None: prems.append((u,)); continue
            elif REL in p:
                a, b = [x.strip() for x in p.split(REL)]
                prems.append((a, b)); continue
            # ⚠ LONGEST RELATION FIRST: `⟶ᵀ` contains `⟶`, so testing the
            #   short one first mis-reads a type-level premise as a
            #   term-level one — silently, and the row still typechecks.
            # ★ a BOOLEAN premise, before the relation search: it
            #   contains no relation symbol at all.
            mb = re.match(r"^\s*([A-Za-z?]+)\s+(.+?)\s*≡\s*(true|false)\s*$", p)
            if mb and mb.group(1) in BOOL_PREM:
                bools.append((mb.group(1), mb.group(2),
                              1 if mb.group(3) == "true" else 0))
                continue
            hit = None
            for rel, comp in sorted(FOREIGN_RELS, key=lambda x: -len(x[0])):
                if rel in p: hit = (rel, comp); break
            if hit:
                rel, comp = hit
                a, b = [x.strip() for x in p.split(rel)]
                foreign.append((a, b, comp)); continue
            return (name, None, "premise %r" % p)
        for g in gs:
            if ":" not in g: return (name, None, "binder %r" % g)
            nms, t = g.split(":", 1); t = t.strip()
            if t in NAT_BINDER:
                for nm in nms.split(): binders.append((nm, "nat", 0))
            elif t in BINDER_SORT:
                srt, dp = BINDER_SORT[t]
                for nm in nms.split(): binders.append((nm, srt, dp))
            else:
                return (name, None, "binder type %r" % t)
    concl = parts[-1]
    if arity == 1:
        lhs, rhs = _un(concl), None
        if lhs is None: return (name, None, "conclusion %r" % concl)
    else:
        if REL not in concl: return (name, None, "conclusion %r" % concl)
        lhs, rhs = [x.strip() for x in concl.split(REL)]
    known = {b[0] for b in binders}
    unk = []
    def walk(e):
        if e[0] == "a":
            if (e[1] not in CT and e[1] not in known
                    and e[1] not in ("renTm", "vs", "pwShift", "zero", "suc")):
                unk.append(e[1])
            return
        # ⚠ THE SAME INFIX BLIND SPOT the `wf` parts had — `C ◃ E` parses
        #   with the LEFT OPERAND as head, so `◃` reads as unmapped here
        #   and as a dropped constructor there.  One rewrite, both readers.
        for x in _infix(e[1], CT): walk(x)
    walk(_parse_spine(_tokens(lhs)))
    if rhs is not None: walk(_parse_spine(_tokens(rhs)))
    if unk: return (name, None, "unmapped %s" % sorted(set(unk)))
    return (name, binders, prems, lhs, rhs, foreign, bools)


# ============================ SORT INFERENCE ==============================
# ★★★ THE MUTUAL PAIR BINDS `∀ {Γ A B t}` — NO TYPES AT ALL.
#
# Every judgement so far said what its binders were (`{t t' : RTm Γ}`).
# `_⊢_∷_` and `_⊢ty_` do not, so the sort has to be inferred from USE:
#   · `Γ ⊢ty A`      ⇒ Γ a context, A a TYPE
#   · `Γ ⊢ t ∷ A`    ⇒ t a TERM, A a TYPE
#   · `Γ ∋ x ∷ A`    ⇒ x a VARIABLE
#   · an argument of a knot constructor ⇒ THAT FIELD's sort, from `KNOT`
#
# ⚠⚠ AND IT IS CHECKED, NOT TRUSTED.  A binder must get ONE sort from all
#   its occurrences; a conflict or an unassigned binder is a REFUSAL.  A
#   wrong sort produces a row that type-checks and means something else —
#   which `{D : Desc}` already did once in this layer.
#
# ⚠ AN UNKNOWN HEAD CARRIES NO INFORMATION.  The first version propagated
#   the ambient sort into unknown applications, so `subTy (single u) B`
#   typed `u` as a TYPE and seven rules "conflicted".  Measured 36/43;
#   with unknown heads contributing nothing it is 42/43, and the one
#   refusal (`⊢ielim`'s motive `M`) is real.

def _rule_lines(path, dataname):
    "…for a judgement written as `data X where`, not `data X : … where`"
    src = open(path, encoding="utf-8").read().split("\n")
    i = next(k for k, l in enumerate(src) if l.startswith("data " + dataname + " where"))
    out, j, cur = [], i + 1, None
    while j < len(src):
        l = src[j]
        if l and not l[0].isspace(): break
        if re.match(r"^  [^ \-]", l):
            if cur: out.append(cur)
            cur = l.strip()
        elif cur is not None and l.startswith("    ") and not l.strip().startswith("--"):
            cur += " " + l.strip()
        j += 1
    if cur: out.append(cur)
    return [r for r in out if ":" in r]

def infer_sorts(rule, CT, FSORT):
    "(name, {binder: sort}) or (name, None, why) — see the note above"
    name, ty = rule.split(":", 1)
    m = re.match(r"\s*∀\s*\{([^}]*)\}\s*→(.*)", ty, re.S)
    if not m: return (name.strip(), None, "no ∀-telescope")
    names, body = m.group(1).split(), m.group(2)
    sorts, conflict = {}, []
    def put(v, srt):
        v = v.strip()
        if v not in names or srt is None: return
        if v in sorts and sorts[v] != srt: conflict.append((v, sorts[v], srt))
        else: sorts[v] = srt
    def scan(e, srt):
        if e[0] == "a": put(e[1], srt); return
        h = e[1][0]
        if h[0] == "a" and h[1] in CT:
            fs = FSORT[CT[h[1]]]
            for i, x in enumerate(e[1][1:]):
                scan(x, fs[i] if i < len(fs) else None)
        else:
            for x in e[1][1:]: scan(x, None)
    # ★★★ ONE PARSER FOR THE PARTS, shared with the emitter.
    #
    # ⚠⚠ THIS HELD ITS OWN REGEXES AND THEY TOOK ONE `▹` AND NO NESTING
    #   — `[^()⊢∋]+?` for the context stops at the first paren.  So
    #   `⊢ielim`'s `((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M` matched
    #   NOTHING, the part contributed no sort, and the rule was refused
    #   as `unassigned ['M']` — which named the SYMPTOM and hid the real
    #   blocker (`IDescWf I D`, the same one seven other rules have).
    #   `_parse_jpart`/`_splitctx` already did nesting properly.
    #   ⇒ the fourth time two readers of the same shape drifted here.
    for part in _split_top(body):
        q = _parse_jpart(part.strip())
        if q is None: continue
        if q[0] in ("ty", "tm"):
            put(q[1], "ctx")
            for e in (q[2] or []): scan(_parse_spine(_tokens(e)), "sTy")
            if q[0] == "tm": scan(_parse_spine(_tokens(q[3])), "sTm")
            scan(_parse_spine(_tokens(q[-1])), "sTy"); continue
        if q[0] == "lk":
            put(q[1], "ctx"); put(q[2], "sVar")
            scan(_parse_spine(_tokens(q[3])), "sTy"); continue
        # ★ a `bool`/`fu` premise contributes NOTHING, by the same rule
        #   an unknown head does: its argument's sort is already fixed by
        #   the typing premise that binds it, and guessing here is how a
        #   wrong sort gets in.
        continue
    if conflict: return (name.strip(), None, "conflicting sorts %s" % conflict)
    miss = [n for n in names if n not in sorts]
    if miss: return (name.strip(), None, "unassigned %s" % miss)
    return (name.strip(), sorts, None)

FIELD_SORT = {("%sK" % n[1:]): [(f[1] if f[0] == "rec" else "nat")
                                for f in fs if f[0] in ("rec", "nat")]
              for n, _, fs in KNOT}

# ★ …and the wrappers' fields.  ⚠ `None` for the SUBSTITUTION argument:
#   it is not a knot term at any sort, and claiming one would propagate
#   a wrong sort outward through `scan`.  The sort that matters is the
#   SUBSTITUTED term's, and it is the whole difference between
#   `subTmAtK` and `subTyAtK`.
FIELD_SORT.update({
    # ★ `isingleK i` — its one argument is the AMBIENT INDEX, a `Tm`.
    "isingleK": ["sTm"],
    "singleK":  ["sTm"],
    "subTmAtK": [None, "sTm"],
    "subTyAtK": [None, "sTy"],
    "extNK":    [None],
    "pwBodyK":  ["sTm"],
})

# ============================ THE MUTUAL PAIR =============================
# ★★★ `_⊢ty_` AND `_⊢_∷_` ARE ONE DESCRIPTION OVER A TAGGED INDEX.
#
#     (depth , Ctx , Tm , Ty , tag)
#
# ⚠ THE TAG IS NOT DECORATION.  Without it the two judgements COLLIDE:
#   a `⊢ty` row pads its `Tm` slot with a dummy, and `⊢unit : Γ ⊢ unit ∷
#   Unit` is a `⊢_∷_` rule whose subject IS that dummy.  The tag is what
#   keeps `Γ ⊢ty Unit` and `Γ ⊢ unit ∷ Unit` apart.
#
# ⚠ AND THE PADDING IS WHAT A UNIFORM TELESCOPE COSTS.  The `Tm` slot
#   cannot change SORT with the tag — a component's sort is fixed — so a
#   `⊢ty` row carries a meaningless term.  The alternative (two mutually
#   citing descriptions) needs a `mutual` block over both `IDesc`s and
#   both `IDescWf`s and is UNTRIED, not impossible; see
#   JUDGEMENT-ATTEMPTS.md §4.
#
# ⚠ THE DEPTH IS INFERRED TOO, not just the sort.  `⊢lam` binds `t` and
#   `B` in `(Γ ▹ A)`, i.e. one deeper, and nothing in `∀ {Γ A B t}` says
#   so — it is read off the PREMISE's context, exactly as the sort is
#   read off the premise's shape.
TEL_JUDGE = None          # built in the main block, once `TCTX` exists

def _splitctx(c):
    """`((Γ ▹ Nat) ▹ M)` → ("Γ", ["Nat", "M"]), outermost extension LAST.

    ⚠ THE REGEXES TOOK EXACTLY ONE `▹`, and the nesting parens defeated
      them anyway.  `⊢natrec`'s middle premise has TWO —
      `((Γ ▹ Nat) ▹ M) ⊢ s ∷ …` — and the whole rule was skipped for it.
      A depth-counting split handles any number."""
    c = c.strip()
    while c.startswith("(") and c.endswith(")"):
        d, ok = 0, True
        for i, ch in enumerate(c):
            if ch == "(": d += 1
            elif ch == ")":
                d -= 1
                if d == 0 and i != len(c) - 1: ok = False; break
        if not ok: break
        c = c[1:-1].strip()
    parts, d, cur = [], 0, ""
    for ch in c:
        if ch == "(": d += 1
        elif ch == ")": d -= 1
        if ch == "▹" and d == 0: parts.append(cur); cur = ""
        else: cur += ch
    parts.append(cur)
    # ⚠ THE BASE MAY ITSELF BE A CONTEXT.  Stripping the outer parens of
    #   `((Γ ▹ Nat) ▹ M)` leaves `(Γ ▹ Nat) ▹ M`, whose first part is
    #   `(Γ ▹ Nat)` — a context, not a name.  Without recursing this
    #   reports ONE extension where there are two, and `⊢natrec`'s `M`
    #   lands a binder too shallow.
    if "▹" in parts[0]:
        _b, _e = _splitctx(parts[0])
        return _b, _e + [x.strip() for x in parts[1:]]
    return parts[0].strip(), [x.strip() for x in parts[1:]]

def _parse_jpart(p):
    """one premise or conclusion of the mutual pair.
    → ('ty', ctx, ext, A) | ('tm', ctx, ext, t, A) | ('lk', ctx, x, A) | None"""
    mm = re.match(r"^([^⊢∋]*?)\s*⊢ty\s+(.*)$", p)
    if mm:
        _c, _x = _splitctx(mm.group(1))
        return ("ty", _c, _x, mm.group(2))
    mm = re.match(r"^([^⊢∋]*?)\s*⊢\s+(.*?)\s*∷\s*(.*)$", p)
    if mm:
        _c, _x = _splitctx(mm.group(1))
        return ("tm", _c, _x, mm.group(2), mm.group(3))
    mm = re.match(r"^\(?\s*([^()⊢∋▹]+?)\s*\)?\s*∋\s+(.*?)\s*∷\s*(.*)$", p)
    if mm: return ("lk", mm.group(1).strip(), mm.group(2), mm.group(3))
    # ★★★ A BOOLEAN PREMISE, here too.
    #
    # ⚠⚠ I BUILT THIS MECHANISM ON THE **REDUCTION** PATH and said it was
    #   general — "those premises will parse the moment their functions
    #   exist, without touching the emitter again".  True for `tr-J-Hom`
    #   and `ap-J`, which are `_⟶_` rules; FALSE for `⊢ap`, which is a
    #   judgement rule and comes through here.  The mutual path has its
    #   own premise parser and had never heard of `BOOL_PREM`.
    #   ⇒ "the mechanism is general" is a claim about EVERY caller, and
    #     this one had exactly one.
    mm = re.match(r"^\s*([A-Za-z?]+)\s+(.+?)\s*≡\s*(true|false)\s*$", p)
    if mm and mm.group(1) in BOOL_PREM:
        return ("bool", mm.group(1), mm.group(2).strip(),
                1 if mm.group(3) == "true" else 0)
    # ★★★ A JUDGEMENT OF THE MERGED BLOCK, applied PREFIX.
    #
    # ⚠ `IDescWf I D` IS AN ALIAS — `IDescWf I D = IDescWfFrom D I D`
    #   (`Spec/Typing:711`) — and its arguments are SWAPPED.  A reader
    #   that matched it positionally would build a row meaning something
    #   else, and it would typecheck.
    # ⚠ LONGEST FIRST: `∈ID` contains `∈D`, and testing the short one
    #   first reads `k ∈ID D` as a `∈D` premise about `I D` — silently.
    for _r in sorted(BINARY_PREM, key=lambda x: -len(x)):
        if _r in p:
            _a, _b = [x.strip() for x in p.split(_r)]
            return ("fb", _r, _a, _b)
    _as = _argsplit(p)
    if _as and _as[0] == "IDescWf" and len(_as) == 3:
        return ("wf", "IDescWfFrom", _as[2], _as[1], _as[2])
    if _as and _as[0] in WF_HEADS and len(_as) - 1 == WF_HEADS[_as[0]]:
        return ("wf",) + tuple(_as)
    # ★ a UNARY foreign judgement — `NoNatC c`.  Last, because it is the
    #   loosest pattern here and would otherwise swallow the others.
    mm = re.match(r"^\s*([A-Za-z?]+)\s+(.+?)\s*$", p)
    if mm and mm.group(1) in UNARY_PREM:
        return ("fu", mm.group(1), mm.group(2).strip())
    return None

def _shiftk(k, E):
    "a child's depth from its parent's, through one `FIELD_DEPTH` entry"
    if E[0] == "lit": return "closed" if E[1] == 0 else ("abs", E[1])
    if not isinstance(k, int): return None      # already absolute: says nothing
    if E[0] == "sucD":  return k + E[1]
    if E[0] == "predD": return k - 1
    return k

def infer_depths(rule, names, CT):
    """{binder: k} — how many binders deep each one lives.

    ⚠⚠ IT MUST WALK STRUCTURALLY, exactly as the SORT inference does.  A
      regex over the conclusion types `B` in `Γ ⊢ty Π A B` at depth 0,
      while the premise `(Γ ▹ A) ⊢ty B` types it at 1 — and the two
      "conflict".  ★ `Π`'s SECOND FIELD IS AT `sucD 1`, and `KNOT` says
      so; the conclusion is not evidence of depth 0, it is evidence of
      depth 1 read through the constructor.  Measured: crude 31/43,
      structural 43/43.
    ⚠ A genuine conflict is still a REFUSAL."""
    body = re.match(r"\s*∀\s*\{[^}]*\}\s*→(.*)", rule.split(":", 1)[1], re.S).group(1)
    d, bad = {}, []
    def put(v, k):
        v = v.strip()
        if v not in names: return
        if v in d and d[v] != k: bad.append((v, d[v], k))
        else: d[v] = k
    def scan(e, k):
        # ⚠ `k is None` means NO INFORMATION.  An unknown head — `subTy
        #   (single u) B` — says nothing about how deep its children sit,
        #   and assuming "the same depth" makes `B` conflict with the
        #   `Π A B` that binds it.  Third sighting of this default in one
        #   sub-task; the rule is uniform now.
        if e[0] == "a": put(e[1], k) if k is not None else None; return
        h = e[1][0]
        if h[0] == "a" and h[1] in CT:
            _c = CT[h[1]]
            fds = FIELD_DEPTH.get(_c, [])
            # ★ THE THIRD READER of this table, and it walks SOURCE spines
            #   like `_val` — so it needs the same prepend offset.  ⚠ The
            #   ratchet caught this one: making the table emitted-indexed
            #   without adjusting here silently dropped `⊢app`/`⊢pair`/
            #   `⊢snd`/`⊢jsub` back to `conflicting depths`, which is the
            #   EXACT regression of 2026-08-31.
            _o = (1 if (_c in _DEPTH_ARG or _c in _IX_PRE) else _PRE_N.get(_c, 0))
            _sg = e[1][1] if len(e[1]) > 1 else None
            for i, x in enumerate(e[1][1:]):
                E = _argshift(_c, i + _o, _sg)
                # ⚠ `predD` IS A DECREMENT.  This computed `k + n` for
                #   `sucD` and `+0` for everything else, so a RAISING
                #   substitution (`nrs`) read as depth-neutral and
                #   `⊢natrec`'s `M` came out a binder too deep.
                # ⚠⚠ `lit` IS AN **ABSOLUTE** DEPTH, and reading it as a
                #   shift of the ambient one is why `ty-IMu`'s `I : RTy ε`
                #   came out at the row's depth.  `KNOT` writes
                #   `rec("sTy", lit(0))` for exactly the fields whose Agda
                #   type names `ε`; those binders are CLOSED.
                scan(x, _shiftk(k, E))
        else:
            for x in e[1][1:]: scan(x, None)
    for part in _split_top(body):
        q = _parse_jpart(part.strip())
        if q is None: continue
        # ⚠ ONLY `ty`/`tm` PARTS CARRY A CONTEXT EXTENSION AT SLOT 2.
        #   For a `∋` part slot 2 is the VARIABLE, and reading it as an
        #   extension puts every lookup premise one binder too deep.
        # ★ a `bool` part binds nothing and carries an INT literal — its
        #   only term is the ARGUMENT, at the ambient depth.
        if q[0] == "bool":
            scan(_parse_spine(_tokens(q[2])), 0); continue
        # ★★★ A `wf` PART CARRIES NO DEPTH INFORMATION — the same rule an
        #   unknown head follows.  Its subjects' depths are dictated by
        #   `IxD`'s FIELD CODES (closed, or the row's), not by where they
        #   appear here; scanning them at 0 claimed `ty-IMu`'s `I : RTy ε`
        #   was ambient and conflicted with the `lit 0` the knot gives it.
        if q[0] in ("wf", "fb"): continue
        ext = q[2] if q[0] in ("ty", "tm") else None
        deep = len(ext) if ext else 0
        put(q[1], 0)
        # ⚠ THE i-TH EXTENSION IS i BINDERS DEEP.  Recording them all at 0
        #   was right while there was only ever one; with two it claims
        #   `⊢natrec`'s `M` lives at 0 when `(Γ ▹ Nat) ⊢ty M` says 1.
        for _i, _e in enumerate(ext or []): put(_e, _i)
        for t in (q[3:] if q[0] != "lk" else q[2:]):
            scan(_parse_spine(_tokens(t)), deep)
    if bad: return None, "conflicting depths %s" % bad
    miss = [n for n in names if n not in d]
    if miss: return None, "unassigned depths %s" % miss
    return d, None


def _wfctx(t, CT):
    """a `Wf` rule's context argument → (its DEPTH, its value).
    ★ `◇` pins the depth to a NUMERAL — `idwf-cons`'s premise is at 1,
      not at the row's variable, and the `Ctx` slot's type reads it."""
    b, ext = _splitctx(t)
    if b.strip() == "◇":
        e = AP("Ctx-empK")
        for i, x in enumerate(ext):
            d = RAW("num %d" % i)
            e = AP("Ctx-extK", d, e, _val(_parse_spine(_tokens(x)), CT, d))
        return RAW("num %d" % len(ext)), e
    e = V(b)
    for i, x in enumerate(ext):
        d = _depth_at(i)
        e = AP("Ctx-extK", d, e, _val(_parse_spine(_tokens(x)), CT, d))
    return _depth_at(len(ext)), e

def _ctxval(ctxname, ext, dep, CT):
    """the premise's `Ctx` component: `Γ`, or `Ctx-extK m Γ A`.

    ⚠ THE EXTENSION IS AN EXPRESSION, not a binder name.  `⊢lam`'s is
      `(Γ ▹ A)` but `ty-El`'s is `(Γ ▹ El c)` — treating it as a name
      dies with a `KeyError` on the string `"El c"`."""
    # ⚠ `ext` IS A LIST NOW, innermost first.  Each extension sits one
    #   binder deeper than the last, so the depth climbs with it.
    e = V(ctxname)
    for i, x in enumerate(ext or []):
        d = _depth_at(i) if i else dep
        e = AP("Ctx-extK", d, e, _val(_parse_spine(_tokens(x)), CT, d))
    return e

_ADQ = []

def _subjects(q):
    "the conclusion's (source expression, sort) pairs"
    if q[0] == "ty": return [(q[-1], "sTy")]
    if q[0] == "tm": return [(q[3], "sTm"), (q[4], "sTy")]
    if q[0] == "wf":
        j, a = q[1], q[2:]
        if j == "DConWf":     return [(a[0], "sDCon")]
        if j == "DescWf":     return [(a[0], "sDesc")]
        if j == "ICodeWf":    return [(a[0], "sTm")]
        if j == "IConWf":     return [(a[0], "sIDesc"), (a[1], "sTy"),
                                      (a[3], "sICon")]
        if j == "IDescWfFrom":return [(a[0], "sIDesc"), (a[1], "sTy"),
                                      (a[2], "sIDesc")]
    return []

def _mutual_rows(CT, TEL, dummy):
    """the 43 rules of `_⊢ty_` + `_⊢_∷_`, as ONE tagged description."""
    src = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "Spec", "Typing.agda")
    rows, skipped = [], []
    for tag, dn, _ar in MERGED:
        for r in _rule_lines(src, dn):
            if _ar is None:
                nm, sorts, why = infer_sorts(r, CT, FIELD_SORT)
                if sorts is None: skipped.append((nm, why)); continue
                deps, why = infer_depths(r, list(sorts), CT)
                if deps is None: skipped.append((nm, why)); continue
                body = re.match(r"\s*∀\s*\{[^}]*\}\s*→(.*)",
                                r.split(":", 1)[1], re.S).group(1)
                raw = [x.strip() for x in _split_top(body)]
                # ★★★ A DESCRIPTION SUBJECT IS **CLOSED**, in the ⊢-rules
                #   too — `infer_depths` reads `Mu D`'s field, which the
                #   knot puts at the AMBIENT depth, but a `DescWf D`
                #   premise carries `D` at 0 and the two must be one
                #   binder.  ⚠ `sICon` is NOT in this list: an `ICon ⌊Θ⌋`
                #   genuinely lives at the scope's depth.
                for _b, _s in sorts.items():
                    if _s in ("sDesc", "sDCon", "sIDesc"): deps[_b] = "closed"
            else:
                # ★ the `Wf` rules TYPE their binders, so nothing is inferred
                _t = _wf_rule(r)
                if _t[1] is None: skipped.append((_t[0], _t[2])); continue
                nm, sorts, deps, raw = _t
            parts, fconv = [], []
            for x in raw:
                q = _parse_jpart(x)
                if q is not None: parts.append(q); continue
                # ★ a CONVERSION premise is foreign, at `_≅ᵀ_`
                if "≅ᵀ" in x:
                    a, b = [y.strip() for y in x.split("≅ᵀ")]
                    fconv.append((a, b)); continue
                parts.append(None)
            if any(q is None for q in parts):
                # ★ NAME THE PREMISE.  "unparsed premise" was the reason on
                #   TEN rules and told nobody which one — a report that
                #   cannot be acted on.  The reduction path has always
                #   named it (`premise %r`); this path did not, and I read
                #   "10 rules, one cause" off it twice and was wrong both
                #   times.  ⇒ same contract as the emitters: say what you
                #   could not do, BY NAME.
                _bad = [x for x, q in zip(raw, parts) if q is None]
                skipped.append((nm, "premise %r" % _bad[0].strip())); continue
            # ⚠ A RULE CAN FAIL IN ITS VALUES, NOT ONLY ITS PREMISES.
            #   `⊢app`'s conclusion is `subTy (single u) B`; the premises
            #   all parse, and without this the emitter dies with a
            #   `KeyError` deep in the value translator instead of
            #   reporting an honest skip.
            unk = []
            def chk(e):
                if e[0] == "a":
                    if (e[1] not in CT and e[1] not in sorts
                            and e[1] not in ("renTm", "vs", "εwkTm", "εwkTy",
                                             "zero", "suc")):
                        unk.append(e[1])
                    return
                for x in _infix(e[1], CT): chk(x)
            for q in parts:
                # ⚠ a `bool` part's last component is an INT (the literal),
                #   not a term — tokenising it is a `TypeError` deep in the
                #   parser rather than an honest skip.
                # ⚠⚠ A `wf` PART'S SUBJECTS WERE NOT CHECKED AT ALL — the
                #   slice `q[3:]` skipped them, which is how `dwf-cons`
                #   shipped a dropped `◃`.  Its CONTEXT argument is checked
                #   through its EXTENSIONS, not as a term.
                if q[0] == "fb":
                    for _t in q[2:]: chk(_parse_spine(_tokens(_t)))
                    continue
                if q[0] == "wf":
                    _ci = WF_CTXARG.get(q[1])
                    for _i, _t in enumerate(q[2:]):
                        if _i == _ci:
                            for _x in _splitctx(_t)[1]:
                                chk(_parse_spine(_tokens(_x)))
                        else: chk(_parse_spine(_tokens(_t)))
                    continue
                _ts = (q[2:3] if q[0] in ("bool", "fu")
                       else (q[2:] if q[0] == "lk" else q[3:]))
                for t in _ts:
                    chk(_parse_spine(_tokens(_expand(t))))
                if q[0] in ("ty", "tm") and q[2]:
                    for _e in q[2]: chk(_parse_spine(_tokens(_e)))
            if unk:
                skipped.append((nm, "unmapped %s" % sorted(set(unk)))); continue
            _BSORT.clear()
            bs = [(_DEPTH, _code(TNAT(), None))]
            _BDEP.clear()
            for b, srt in sorts.items():
                _BSORT[b] = srt
                _BDEP[b] = deps[b]
                if srt == "ctx":
                    bs.append((b, _code(TCTX(), _depth_at(deps[b]))))
                elif srt == "nat":
                    # ⚠ `⊢con`'s `k` is a ℕ FIELD of the knot's `con`, so
                    #   `infer_sorts` gives it the sort "nat" — a bare
                    #   `Nat` slot, not `⌜IMu⌝ … (pair nat …)`.
                    bs.append((b, _code(TNAT(), None)))
                else:
                    bs.append((b, _code(TKNOT(srt), _depth_at(deps[b]))))
            for i, (a, b) in enumerate(fconv):
                bs.append(("fc%d" % i, _code(FOREIGN["ConvD"],
                    TUP(V(_DEPTH),
                        _val(_parse_spine(_tokens(a)), CT, V(_DEPTH)),
                        _val(_parse_spine(_tokens(b)), CT, V(_DEPTH))))))
            def _v0(x):
                return _val(_parse_spine(_tokens(_expand(x))), CT, RAW("num 0"))

            def ix_of(q):
                "the (depth, Ctx, Tm, Ty, tag, payload) tuple a part denotes"
                # ★★★ THE FIVE `Wf` JUDGEMENTS.  Each uses the flat slots
                #   its subjects actually need and puts the rest — never
                #   more than three fields — in ONE payload.  §11.6.
                _z, _e = RAW("num 0"), AP("Ctx-empK")
                if q[0] == "wf":
                    j, a = q[1], q[2:]
                    def _v(x, dp): return _val(_parse_spine(_tokens(x)), CT, dp)
                    if j == "DConWf":
                        return TUP(_z, _e, dummy, AP("Ty-NatK"), RAW("num 2"),
                                   AP("IxDConK", _z, _v(a[0], _z)))
                    if j == "DescWf":
                        return TUP(_z, _e, dummy, AP("Ty-NatK"), RAW("num 3"),
                                   AP("IxDescK", _z, _v(a[0], _z)))
                    if j == "IConWf":
                        # ⚠ the DEPTH IS `Θ`'s — the `Ctx` slot's type reads
                        #   it, so it is not free.
                        _d, _cx = _wfctx(a[2], CT)
                        return TUP(_d, _cx, dummy, AP("Ty-NatK"),
                                   RAW("num 4"),
                                   AP("IxIConK", _d, _v(a[0], _z), _v(a[1], _z),
                                      _v(a[3], _d)))
                    if j == "ICodeWf":
                        _d = V(_DEPTH)
                        return TUP(_d, V("Θ"), _v(a[0], _d), AP("Ty-NatK"),
                                   RAW("num 5"), AP("IxNoneK", _d))
                    if j == "IDescWfFrom":
                        return TUP(_z, _e, dummy, AP("Ty-NatK"), RAW("num 6"),
                                   AP("IxIDescK", _z, _v(a[0], _z), _v(a[1], _z),
                                      _v(a[2], _z)))
                    raise ValueError("no index shape for %r" % (j,))
                ext = q[2] if q[0] in ("ty", "tm") else None
                # ★ `◇` is a LITERAL context, at depth 0 — `dwf-κ`'s premise
                #   `◇ ⊢ c ∷ U` is the only place a rule names one.
                _emp = q[1].strip() == "◇" and not ext
                d = _z if _emp else _depth_at(len(ext) if ext else 0)
                cx = _e if _emp else _ctxval(q[1], ext, V(_DEPTH), CT)
                if q[0] == "ty":
                    tm, ty, tg = dummy, q[3], 0
                else:
                    tm, ty, tg = q[3], q[4], 1
                _slots = [d, cx,
                          _val(_parse_spine(_tokens(_expand(tm))), CT, d)
                            if tm is not dummy else dummy,
                          _val(_parse_spine(_tokens(_expand(ty))), CT, d)]
                # ⚠ A PADDED SLOT NEEDS A DUMMY **AT ITS OWN SORT**.  The
                #   first attempt padded all three with `Tm-unitK` — the
                #   `sTm` dummy a `⊢ty` row uses — and every module failed
                #   `nzero != nsuc …` on the sort ford.  ⇒ the nullary
                #   former of each sort, which exists at every depth.
                if SPIKE_WIDE:
                    _slots += [AP("IDesc-nilK"), AP("ICon-iK"), AP("DCon-iK")]
                # ★ the per-tag payload, AFTER the tag.  A `⊢ty`/`⊢_∷_`
                #   row carries the nullary one — ONE dummy, where the flat
                #   union would have wanted six at six different sorts.
                return TUP(*(_slots + [RAW("num %d" % tg), AP("IxNoneK", d)]))
            # ★ a `∋` premise is foreign too, at `_∋_∷_` — the judgement
            #   `Knot/Lookup` built by hand, and the first one there was.
            ps = []
            for i, q in enumerate(parts[:-1]):
                if q[0] == "bool":
                    # ★★★ THE SAME FORD the reduction path emits —
                    #   `⌜Id⌝ ⌜Nat⌝ (fK ⟨i⟩ c) n`.  A boolean premise is
                    #   not a judgement, so it is a κ field and not an
                    #   `ih`; `icw-ford` discharges its `ICodeWf`.
                    _fn, _arg, _lit = q[1], q[2], q[3]
                    _fnK, _dfn, _srt = BOOL_PREM[_fn]
                    _bd = _depth_at(deps.get(_arg, 0))
                    bs.append(("bp%d" % i,
                               AP("⌜Id⌝", RAW("⌜Nat⌝"),
                                  AP(_fnK, PAIR(RAW(_srt), _bd),
                                     _val(_parse_spine(_tokens(_arg)), CT, _bd)),
                                  RAW("num %d" % _lit))))
                    continue
                if q[0] == "fb":
                    # ★ closed subjects ⇒ the citation sits at depth 0
                    bs.append(("fb%d" % i,
                               _code(FOREIGN[BINARY_PREM[q[1]]],
                                     TUP(RAW("num 0"),
                                         _v0(q[2]), _v0(q[3])))))
                    continue
                if q[0] == "fu":
                    # ★ THE PREMISE'S OWN DEPTH, not the row's: `⊢tr`
                    #   binds `c : RTm (Γ ∙)`, so `NoNatC c` is a fact
                    #   about a code ONE BINDER IN.
                    _fd = _depth_at(deps.get(q[2], 0))
                    bs.append(("fu%d" % i,
                               _code(FOREIGN[UNARY_PREM[q[1]]],
                                     TUP(_fd, _val(_parse_spine(_tokens(q[2])),
                                                   CT, _fd)))))
                    continue
                if q[0] == "lk":
                    bs.append(("lk%d" % i, _code(FOREIGN["LkD"],
                        TUP(V(_DEPTH), V(q[1]),
                            _val(_parse_spine(_tokens(q[2])), CT, V(_DEPTH)),
                            _val(_parse_spine(_tokens(q[3])), CT, V(_DEPTH))))))
                    continue
                ps.append(("ih%d" % i, ix_of(q)))
            concl = parts[-1]
            vals = _tupcomps(ix_of(concl))
            # ★ the conclusion's SUBJECTS and their sorts, for the adequacy
            #   check.  ⚠ Only the conclusion: a premise's subject is
            #   translated by the same `_val`, so the coverage is the same
            #   and the assertions would be duplicates.
            _ADQ.append((nm, sorts, deps, _subjects(concl)))
            rows.append((nm, JRow("jd" + nm, bs, ps, vals)))
    return rows, skipped

# ============================ A JUDGEMENT, END TO END ======================
# ★★★ ONE FUNCTION PER JUDGEMENT WOULD BE FIVE COPIES.  The judgements
#   differ in four things — the datatype's name, its relation symbol, its
#   index telescope, and which OTHER judgements it may cite — so those
#   are parameters and the pipeline is written once.
#
# ★ AND THE MODULE SIZE IS CHOSEN FROM A MEASUREMENT, not a guess:
#   bisected at ~1.8 s/row with the OOM cliff above ~50 rows on a 5.5 GB
#   cap, so `SPLIT_AT` is 34 and anything larger is emitted in halves.
SPLIT_AT = 34

class Judgement:
    def __init__(self, data, rel, tel, ity, ixdef, desc, mod, wf, cites=(), extra="",
                 arity=2, src="Typing"):
        self.data, self.rel, self.tel, self.ity = data, rel, tel, ity
        self.ixdef, self.desc, self.mod, self.wf = ixdef, desc, mod, wf
        self.cites, self.extra = cites, extra
        # ⚠ NOT EVERY JUDGEMENT LIVES IN `Spec/Typing`.  `NoNatC` is in
        #   `Spec/Variance` — it is a property of CODES, not a typing
        #   rule, and `⊢tr` imports it as a premise.
        self.arity, self.src = arity, src

def _jrows(J, CT):
    "the translated rows, and the rules that did not translate"
    rows, skipped = [], []
    src = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "Spec", "Typing.agda")
    src = os.path.join(os.path.dirname(src), J.src + ".agda")
    for r in rules_of(src, J.data):
        t = translate_rule(r, CT, J.rel, J.cites, J.arity)
        if t[1] is None: skipped.append((t[0], t[2])); continue
        nm, binders, prems, lhs, rhs, foreign, bools = t
        bs, dep = [(_DEPTH, _code(TNAT(), None))], {}
        _BSORT.clear()
        for b, srt, dp in binders:
            _BSORT[b] = srt
            dep[b] = dp
            bs.append((b, _code(TNAT(), None) if srt == "nat"
                          else _code(TKNOT(srt), _depth_at(dp))))
        for i, (a, b, fcomp) in enumerate(foreign):
            bs.append(("fp%d" % i,
                       _code(fcomp, TUP(V(_DEPTH),
                             _val(_parse_spine(_tokens(a)), CT, V(_DEPTH)),
                             _val(_parse_spine(_tokens(b)), CT, V(_DEPTH))))))
        ps = []
        for i, pr in enumerate(prems):
            a = pr[0]
            d = dep.get(a.strip(), 0)
            ps.append(("ih%d" % i, TUP(_depth_at(d),
                       *[_val(_parse_spine(_tokens(x)), CT, _depth_at(d))
                         for x in pr])))
        rows.append((nm, JRow("rd" + nm, bs, ps,
                     [V(_DEPTH)] + [_val(_parse_spine(_tokens(x)), CT, V(_DEPTH))
                                    for x in ((lhs,) if rhs is None
                                              else (lhs, rhs))])))
    return rows, skipped

GC_NOTE = """-- ⚠⚠ THIS MODULE NEEDS THE **COMPACTING COLLECTOR**.
--
--   MEASURED 2026-08-31, the commit that added `⊢app`/`⊢pair`/`⊢snd`/
--   `⊢jsub`: `JudgeWfA` OOM-KILLED (143) on the default `-A64m` and
--   passed on `-A64m -c` at 179s.  `JudgeWfB` passed either way at 74s.
--   ⚠ Four rows moved it across the cap — and the two halves hold the
--     SAME number of rows, so the count is not what separates them.
--     `_⊢ty_`/`_⊢_∷_`'s index has FIVE components and the A half's rows
--     carry the deeper telescopes.
--
--   ⚠ BEFORE THIS MARKER THE MODULE WAS GREEN ONLY BY THE SWEEP'S
--     RETRY: `tools/sweep.sh` takes the OOM kill, then re-runs with
--     `-c`.  That is a pass, but it costs an OOM every sweep and it
--     hides the cost from anyone checking the module directly.
--
--   `tools/sweep.sh` greps this header for the phrase above and
--   switches collectors on its own (`needs_c`), which is why the words
--   are spelled out rather than described.
--
"""

JHDR = """--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `%(data)s`%(what)s
--
%(gc)s-- ⚠⚠ THE RULES ARE **PARSED OUT OF `Spec/Typing.agda`**, not transcribed.
--   A hand-written table is one chance per row to name the wrong
--   variable — the error class `Knot/LookupGen` exists to catch, and one
--   an `ICon` never reveals, because it type-checks with ANY in-scope
--   variable of the right type.  The Agda-former → knot-constructor map
--   comes from `KNOT`'s own `decl` strings, so nothing is typed twice.
--
-- ★ ANY RULE THAT DID NOT TRANSLATE IS NAMED BELOW.  Emitting a subset
--   silently is `verification-that-covers-less-than-it-claims`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.%(mod)s where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; var; vz; vs; pair; fst; snd; nsuc; nzero
        ; El; IMu; Σ'; Nat
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub; ICon; IDesc; iι; iρ; iκ; inil; _◂_; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_
        ; IConWf; iwf-ι; iwf-κ; iwf-ρ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; idwf-nil; idwf-cons
        ; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nsuc; ⊢nzero
        ; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ⊢pair; ty-Σ; ty-Nat; ty-IMu
        ; ξ-pairˡ; ξ-pairʳ; ξ-nsuc; βfst; βsnd )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; toI; fromI; ⊢ixP; ⊢sTy; ⊢sTm; ⊢sDesc; ⊢sDCon; ⊢sIDesc; ⊢sICon; ⊢sVar
        ; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.CtorsV
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK; ⊢wkTmK; wkTyK; ⊢wkTyK )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Single using ( singleK; ⊢singleK )
open import DirectedHoTT.Examples.Knot.SubApp
  using ( subTmAtK; subTyAtK; ⊢subTmAtK; ⊢subTyAtK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK; ⊢extNK )
open import DirectedHoTT.Examples.Knot.Pw using ( pwK; ⊢pwK )
open import DirectedHoTT.Examples.Knot.Stk
  using ( stkAK; ⊢stkAK; stkCK; ⊢stkCK; flatK; ⊢flatK )
open import DirectedHoTT.Examples.Knot.Nrs using ( nrsSubK; ⊢nrsSubK )
open import DirectedHoTT.Examples.Knot.PwBody using ( pwBodyK; ⊢pwBodyK )
%(extra)s
"""

def gen_j_rows(J, CT):
    rows, skipped = _jrows(J, CT)
    _JCACHE[J.mod] = rows
    _CENSUS.append((J.desc, [J.data], len(skipped), J.src))
    L = [JHDR % dict(gc="", data=J.data, what=", THE ROWS.", mod=J.mod + "Rows",
                     extra=J.extra)]
    L.append("%s : RTy ε" % J.ity)
    L.append("%s = %s" % (J.ity, J.ixdef))
    L.append("")
    L.append("-- ⚠ NOT EMITTED — %d of %d rules:" % (len(skipped), len(skipped) + len(rows)))
    for n, w in skipped: L.append("--     %-12s %s" % (n, w))
    L.append("")
    for i, (nm, row) in enumerate(rows):
        tag = J.mod + _tagof(i)
        L.append("-- %s" % nm)
        L.append(emit_jrow(row, J.tel, (tag, "k" + tag), J.ity, J.desc))
        L.append("")
    L.append("-" * 72)
    L.append("-- ★★★ …AND THE JUDGEMENT ITSELF.")
    L.append("-" * 72)
    L.append("%s : IDesc" % J.desc)
    L.append("%s =" % J.desc)
    line, body = "  ", []
    for nm, _ in rows:
        if len(line) > 62: body.append(line); line = "  "
        line += "rd%s ◂ " % nm
    body.append(line + "inil")
    L.append("\n".join(body))
    return "\n".join(L) + "\n"

_JCACHE = {}

# ★★★ EVERY FAMILY REGISTERS ITSELF WHERE IT IS BUILT, and `Knot/Census`
#   is GENERATED from this list.
#
# ⚠⚠ THE REASON: `InIDD` shipped as `inil` — a WELL-FORMED EMPTY
#   DESCRIPTION — because a binder type was missing and both its rows
#   silently failed to translate.  `Census` would have caught it the same
#   day, and did not, because the family had been ADDED WITHOUT ADDING ITS
#   CENSUS ROW.  A hand-maintained list of invariants rots exactly like
#   any other parallel list.
# ⇒ so there is now ONE place to add a family, and the check follows.
#   (entry: description name · the Agda datatypes it encodes · skips · src)
_CENSUS = []

def gen_j_wf(J, part, lo, hi, last):
    rows = _JCACHE[J.mod]
    imp = ("open import DirectedHoTT.Examples.Knot.%sRows\n" % J.mod
           + ("open import DirectedHoTT.Examples.Knot.%sWfA\n" % J.mod
              if part == "B" else "") + J.extra)
    L = [JHDR % dict(gc="", data=J.data, what=" IS A WELL-FORMED DESCRIPTION.",
                     mod=J.mod + "Wf" + part, extra=imp)]
    for nm, row in rows[lo:hi]:
        tag = J.mod + _tagof(rows.index((nm, row)))
        L.append("-- %s" % nm)
        L.append(emit_jrowwf(row, J.tel, (tag, "k" + tag), J.ity,
                             "rd%sWf" % nm, J.desc))
        L.append("")
    if last:
        L.append("-" * 72)
        L.append("-- ★★★ …AND IT IS WELL FORMED.")
        L.append("-" * 72)
        L.append("%s : IDescWf %s %s" % (J.wf, J.ity, J.desc))
        L.append("%s =" % J.wf)
        L.append(nest(["idwf-cons (rd%sWf %s)" % (nm, J.desc) if not row.prems
                       else "idwf-cons rd%sWf" % nm
                       for nm, row in rows], "idwf-nil", 2))
    return "\n".join(L) + "\n"

def write_judgement(J, out, CT):
    "…sized from the measured cost model."
    open(os.path.join(out, J.mod + "Rows.agda"), "w").write(gen_j_rows(J, CT))
    n = len(_JCACHE[J.mod])
    if n <= SPLIT_AT:
        open(os.path.join(out, J.mod + "Wf.agda"), "w").write(
            gen_j_wf(J, "", 0, n, True))
        return [J.mod + "Wf"]
    h = (n + 1) // 2
    open(os.path.join(out, J.mod + "WfA.agda"), "w").write(
        gen_j_wf(J, "A", 0, h, False))
    open(os.path.join(out, J.mod + "WfB.agda"), "w").write(
        gen_j_wf(J, "B", h, n, True))
    return [J.mod + "WfA", J.mod + "WfB"]

# ★★★ WIDTH SPIKE (`SPIKE_WIDE=1`) — MEASUREMENT ONLY, NEVER COMMITTED.
#
# The merge must carry `IConWf`'s subjects too — an `IDesc`, an `ICon`
# and a `DCon` beyond what `IJudge` holds.  Before transcribing ~40 rows
# against a wider index, measure what the WIDTH alone costs: re-emit the
# SAME 33 rules with three extra slots, padded with the same dummy a
# `⊢ty` row already uses for its `Tm`.  Any delta is attributable to
# width, because nothing else changed.
SPIKE_WIDE = bool(os.environ.get("SPIKE_WIDE"))

IJUDGE_WIDE = """Σ' Nat
    (Σ' (IMu CtxD INat (var vz))
      (Σ' (IMu KnotD IPair (pair sTm (var (vs vz))))
        (Σ' (IMu KnotD IPair (pair sTy (var (vs (vs vz)))))
          (Σ' (IMu KnotD IPair (pair sIDesc (var (vs (vs (vs vz))))))
            (Σ' (IMu KnotD IPair (pair sICon (var (vs (vs (vs (vs vz)))))))
              (Σ' (IMu KnotD IPair (pair sDCon (var (vs (vs (vs (vs (vs vz))))))))
                  Nat))))))"""

# ★★★ THE PER-TAG-PAYLOAD SPIKE (`SPIKE_SUM=1`) — MEASUREMENT ONLY.
#
# `JUDGEMENT-ATTEMPTS` §10.5 recommends keeping the five slots consumers
# PROJECT flat, and putting the merge-only subjects behind ONE per-tag
# payload — width 5 → 6 rather than 5 → 11.  §10.6 left its cost
# unmeasured; this emits the SAME 33 rules at width 6 with the payload
# padded by `Knot/IxD`'s nullary dummy, which is exactly what the 43
# typing rows would carry.
#
# ⚠ THE SPIKE INDEXES THE PAYLOAD BY THE **DEPTH**, not the tag.  In the
#   real design it is indexed by the tag, which is a NUMERAL in every
#   row; the depth is a VARIABLE, so this is the harder index and the
#   measurement is an UPPER bound, not an under-estimate.
IJUDGE_SUM = """Σ' Nat
    (Σ' (IMu CtxD INat (var vz))
      (Σ' (IMu KnotD IPair (pair sTm (var (vs vz))))
        (Σ' (IMu KnotD IPair (pair sTy (var (vs (vs vz)))))
          (Σ' Nat
              (IMu IxD INat (var (vs (vs (vs (vs vz))))))))))"""

SPIKE_SUM = bool(os.environ.get("SPIKE_SUM"))

# ★★★ SIX SLOTS, AND THE SIXTH IS THE PER-TAG PAYLOAD.  §10.5/§11.6:
# five slots consumers PROJECT, then everything a merged judgement needs
# that they do not.  ⚠ A NEW JUDGEMENT ADDS AN `IxD` CONSTRUCTOR, NOT A
# SLOT — that is the whole reason this shape and not the flat union.
IJUDGE_DEF = """Σ' Nat
    (Σ' (IMu CtxD INat (var vz))
      (Σ' (IMu KnotD IPair (pair sTm (var (vs vz))))
        (Σ' (IMu KnotD IPair (pair sTy (var (vs (vs vz)))))
          (Σ' Nat
              (IMu IxD INat (var (vs (vs (vs (vs vz))))))))))"""

MUT_EXTRA = """open import DirectedHoTT.Examples.Knot.CtxD
  using ( CtxD; INat; CtxWf; Ctx-extK; ⊢Ctx-extKt; Ctx-empK; ⊢Ctx-empK )
open import DirectedHoTT.Examples.Knot.EWk using ( εwkK; ⊢εwkK; isingleK; ⊢isingleK )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( sortMap-ty; sortMap-tm; sortMap-desc; sortMap-dcon
        ; sortMap-idesc; sortMap-icon; sortMap-var )
open import DirectedHoTT.Examples.Knot.Lookup using ( LkD; ILk; LkWf )
open import DirectedHoTT.Examples.Knot.ConvRows using ( ConvD; IConv )
open import DirectedHoTT.Examples.Knot.ConvWf using ( ConvWf )
open import DirectedHoTT.Examples.Knot.NoNatCRows using ( NoNatCD; INoNatC )
open import DirectedHoTT.Examples.Knot.NoNatCWf using ( NoNatCWf )
open import DirectedHoTT.Examples.Knot.InDRows using ( InDD; IInD )
open import DirectedHoTT.Examples.Knot.InDWf using ( InDWf )
open import DirectedHoTT.Examples.Knot.InIDRows using ( InIDD; IInID )
open import DirectedHoTT.Examples.Knot.InIDWf using ( InIDWf )
open import DirectedHoTT.Examples.Knot.IxD
  using ( IxD; IxWf; IxNoneK; ⊢IxNoneK; IxDConK; ⊢IxDConK; IxDescK; ⊢IxDescK
        ; IxIConK; ⊢IxIConK; IxIDescK; ⊢IxIDescK )"""

JWFTOP = """
------------------------------------------------------------------------
-- ★★★ THE SHARED TOP OF EVERY ROW'S `IConWf` CHAIN.
--
-- Every judgement row begins with the same two κ fields — the DEPTH and
-- the CONTEXT — and so with the same two `iwf-κ` rungs.  They are the
-- OUTERMOST rungs, so each row's copy wraps that row's own inner chain:
-- unshareable as a VALUE, shareable as a FUNCTION over the tail.
--
-- ⚠ THAT DISTINCTION IS THE WHOLE POINT.  Hoisting the shared CONTEXTS
--   and CODES (`JS0`, `kJS0`, …) saves nothing — they are shape, and
--   `shape-is-free-payload-is-the-cost` measured shape at ZERO.  What
--   this lemma moves is the PAYLOAD: the `⊢ty` obligations
--   `⊢⌜Nat⌝` and `⊢⌜IMu⌝ CtxWf (toI (fromI (⊢var here)))` were
--   re-discharged once per row, and are now discharged ONCE.
------------------------------------------------------------------------

JS0 : Ctx
JS0 = ◇ ▹ εwkTy IJudge

kJS0 : RTm ⌊ JS0 ⌋
kJS0 = ⌜Nat⌝

JS1 : Ctx
JS1 = JS0 ▹ El kJS0

kJS1 : RTm ⌊ JS1 ⌋
kJS1 = ⌜IMu⌝ CtxD INat (var vz)

JS2 : Ctx
JS2 = JS1 ▹ El kJS1

jwfTop : {C : ICon ⌊ JS2 ⌋} (D : IDesc) → IConWf D IJudge JS2 C →
         IConWf D IJudge JS0 (iκ kJS0 (iκ kJS1 C))
jwfTop D w =
  iwf-κ kJS0 (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
    (iwf-κ kJS1 (icw-imu (var vz) CtxWf)
      (⊢⌜IMu⌝ CtxWf (toI (fromI (⊢var here))))
      w)

"""

def write_mutual(out, CT):
    """`_⊢ty_` + `_⊢_∷_`, ONE description over a TAGGED index."""
    TEL = ([TNAT(), TCTX(), TKNOT("sTm"), TKNOT("sTy"),
            TKNOT("sIDesc"), TKNOT("sICon"), TKNOT("sDCon"), TNAT()]
           if SPIKE_WIDE else
           [TNAT(), TCTX(), TKNOT("sTm"), TKNOT("sTy"), TNAT(), TIX()])
    rows, skipped = _mutual_rows(CT, TEL, AP("Tm-unitK"))
    _CENSUS.append(("JudgeD", [d for _, d, _ in MERGED], len(skipped), "Typing"))
    # ⚠⚠ THE CAP MUST BITE **BEFORE** `JudgeD` IS BUILT.  Truncating only
    #   the well-formedness rows leaves the DESCRIPTION at full length, so
    #   the final `idwf-cons` chain ends in `idwf-nil` against a `JudgeD`
    #   that still has rows left: `inil != (jd⊢snd ◂ …)`.  ⚠ That error
    #   hides unless the LAST part is checked — the assembly lives only
    #   there, and every earlier timing checked `JudgeWfA` alone.
    _cap = os.environ.get("JUDGE_MAX_ROWS")
    if _cap: rows = rows[:int(_cap)]
    L = [JHDR % dict(gc="", data="_⊢ty_ / _⊢_∷_", what=", ONE TAGGED DESCRIPTION.",
                     mod="JudgeRows", extra=MUT_EXTRA)]
    L += ["-- ★★★ THE INDEX IS TAGGED, and the tag is not decoration: a",
          "--   `⊢ty` row PADS its `Tm` slot with a dummy, and `⊢unit :`",
          "--   `Γ ⊢ unit ∷ Unit` is a `⊢_∷_` rule whose subject IS that",
          "--   dummy.  The tag is what keeps `Γ ⊢ty Unit` and",
          "--   `Γ ⊢ unit ∷ Unit` apart.",
          "--",
          "-- ⚠ AND THE PADDING IS WHAT A UNIFORM TELESCOPE COSTS: the slot",
          "--   cannot change SORT with the tag.",
          "IJudge : RTy ε", "IJudge =",
          "  " + (IJUDGE_WIDE if SPIKE_WIDE else IJUDGE_DEF), ""]
    L.append("-- ⚠ NOT EMITTED — %d of %d rules:" % (len(skipped), len(skipped) + len(rows)))
    for n, w in skipped: L.append("--     %-10s %s" % (n, w))
    L.append("")
    for i, (nm, row) in enumerate(rows):
        tag = "J" + _tagof(i)
        L.append("-- %s" % nm)
        L.append(emit_jrow(row, TEL, (tag, "k" + tag), "IJudge", "JudgeD"))
        L.append("")
    L.append("-" * 72)
    L.append("-- ★★★ …AND THE MUTUAL PAIR IS ONE DESCRIPTION.")
    L.append("-" * 72)
    L.append("JudgeD : IDesc")
    L.append("JudgeD =")
    line, body = "  ", []
    for nm, _ in rows:
        if len(line) > 62: body.append(line); line = "  "
        line += "jd%s ◂ " % nm
    body.append(line + "inil")
    L.append("\n".join(body))
    open(os.path.join(out, "JudgeRows.agda"), "w").write("\n".join(L) + "\n")

    # ---- and its well-formedness, sized by the measured cost model
    # ⚠⚠ SPLIT IN HALVES, AND THE ROW COUNT ALONE WAS THE WRONG MODEL.
    #   `SPLIT_AT = 34` was calibrated on `_⟶_`'s THREE-component index;
    #   this judgement's is FIVE, and 28 rows OOMed as one module.  The
    #   cost scales with the telescope's WIDTH as well as its length —
    #   each extra component is another ford, another transport, another
    #   `⊢pair` rung per premise.
    # ★★★ SPLIT BY **ROWS PER MODULE** — MEASURED AT FULL SIZE, 32 rows.
    #
    #       split      parts   total   slowest
    #       2 × 16       2      265s     141s      ← was
    #       4 ×  8       4      224s      77s
    #       8 ×  4       8      232s      45s      ← is
    #
    # ⚠⚠ AND THE ROWS ARE NOT INTERCHANGEABLE.  At EIGHT rows each,
    #   `JudgeWfA` costs 38s and `JudgeWfB` costs 77s — same count, double
    #   the cost.  A per-row-count model projected 152s/168s for these two
    #   splits; the truth is 224s/232s.  ⇒ row COUNT is a weak predictor
    #   and the spread across equal-sized parts (17s … 45s, 2.6×) says a
    #   HANDFUL OF ROWS dominate.
    #
    # ★ `JWF_ROWS = 4` is chosen for the SLOWEST module (45s vs 141s, a 3×
    #   cut in what a developer waits on).  Total is a wash between the two
    #   splits (224s vs 232s, inside the ±12% floor).
    # ⚠ IT DOES NOT REACH 10–20s.  Splitting cannot: the intercept is ~7s
    #   and the expensive rows stay expensive wherever they are put.
    #
    # ⬜ THE REMAINING LEVER IS **WHICH ROWS**, not how many — bisect the
    #   2.6× spread.  ⬜ A hoist of the shared top rungs was tried first and
    #   MEASURED AT ZERO (40s vs a 38s baseline); see `emit_jrowwf`'s call.
    # ⚠ MEASUREMENT KNOB, same contract as `JUDGE_MAX_ROWS`: the spikes
    #   vary rows-per-module to find where a width fits.
    # ★★★ TWO, NOT FOUR — MEASURED (§10.6).  At the six-slot index
    #   `JudgeWfD` reaches 5.60 GB against a 5.5 GB cap and `JudgeWfF` is
    #   SIGTERM-killed at 338s under `-c`; at two rows all 17 are green.
    #   ⚠ The worst is still 170.8s at 5.59 GB — "fits", not "fits
    #     comfortably".
    # ⚠⚠ ONE, NOT TWO — MEASURED AGAIN once the `Wf` rows landed.  At two
    #   rows `JudgeWfM`–`P` were SIGTERM-killed under `-c` and `JudgeWfQ`
    #   took 439s.  §10.6 had already said the six-slot index "fits, not
    #   fits comfortably" at 5.59 GB against a 5.5 GB cap; twelve more rows
    #   is what crossed it.
    JWF_ROWS = int(os.environ.get("JWF_ROWS", 1))
    _n = len(rows)
    _bounds = [(i, min(i + JWF_ROWS, _n)) for i in range(0, _n, JWF_ROWS)]
    # ⚠ MORE THAN 26 PARTS RUNS PAST `Z` into `[`, `\\`, `]` — real files
    #   with those names, which the next run does not overwrite and the
    #   sweep would then check as STALE.  The width spike at one row per
    #   module produced 33 parts and 24 such strays.
    # ★★★ A–Z, THEN AA–ZZ.  The merged judgement does not fit at two rows
    #   per module (four OOM-killed under `-c`), and one row per module is
    #   51 parts — past `Z`.  ⚠ The first 26 keep their single letters, so
    #   only the tail churns.
    def _pn(i):
        return (chr(ord("A") + i) if i < 26
                else chr(ord("A") + i // 26 - 1) + chr(ord("A") + i % 26))
    if len(_bounds) > 26 * 27:
        sys.exit("  ⇒ %d parts: even AA–ZZ is exhausted." % len(_bounds))
    _parts = [_pn(i) for i in range(len(_bounds))]
    # ★★★ AND REMOVE THE PARTS A PREVIOUS RUN LEFT BEHIND.
    #
    # ⚠⚠ THE `>26` GUARD ABOVE DOES NOT COVER THIS, and I found out by
    #   tripping it: `JWF_ROWS=2` writes A–Q, the next clean run writes
    #   A–I, and J–Q survive as REAL FILES holding a stale index — which
    #   `sweep.sh` then checks, because it globs `*.agda`.  It is the
    #   same failure the `>26` guard exists for (files nothing rewrites),
    #   arriving from the other direction: FEWER parts, not more.
    # ★ `verification-that-covers-less-than-it-claims`: a sweep that
    #   checks a stale module is not a weaker check, it is a WRONG one —
    #   it would have gone green on a width the tree no longer uses.
    # ⚠ GLOB, don't enumerate: with two-letter parts the unused names are
    #   no longer a contiguous tail of the alphabet.
    _keep = set("JudgeWf%s.agda" % q for q in _parts)
    for _f in sorted(os.listdir(out)):
        if _f.startswith("JudgeWf") and _f.endswith(".agda") and _f not in _keep:
            os.remove(os.path.join(out, _f)); print("  removed stale", _f[:-5])
    for _pi, (part, (lo, hi)) in enumerate(zip(_parts, _bounds)):
        # ⚠ EACH PART IMPORTS EVERY EARLIER PART, not just its predecessor:
        #   Agda's `open import` does not RE-EXPORT, so the final assembly
        #   would not see the names of parts before the last one.
        _prev = "".join("\nopen import DirectedHoTT.Examples.Knot.JudgeWf%s" % q
                        for q in _parts[:_pi])
        W = [JHDR % dict(gc=GC_NOTE, data="_⊢ty_ / _⊢_∷_",
                         what=" IS A WELL-FORMED DESCRIPTION.",
                         mod="JudgeWf" + part,
                         extra=MUT_EXTRA
                         + "\nopen import DirectedHoTT.Examples.Knot.JudgeRows"
                         + _prev)]
        for i in range(lo, hi):
            nm, row = rows[i]
            tag = "J" + _tagof(i)
            W.append("-- %s" % nm)
            W.append(emit_jrowwf(row, TEL, (tag, "k" + tag), "IJudge",
                                 # ⚠⚠ `share=2, topname="jwfTop"` — TRIED AND
                                 #   MEASURED AT ZERO, 2026-08-31.  Hoisting
                                 #   the two identical top rungs into a lemma
                                 #   over the tail (the `⊢methLam` move) gave
                                 #   40s against a 38s baseline at cap=16 —
                                 #   inside the ±12% noise floor.
                                 #   ⇒ the `⊢ty` obligations in those rungs
                                 #     (`⊢⌜Nat⌝`, `⊢⌜IMu⌝ CtxWf …`) are CHEAP;
                                 #     discharging them once per row costs
                                 #     nothing measurable.  This is
                                 #     `shape-is-free-payload-is-the-cost`
                                 #     again — the argument that these rungs
                                 #     were payload rather than shape was
                                 #     WRONG.  Mechanism kept, disabled.
                                 "jd%sWf" % nm, "JudgeD"))
            W.append("")
        if _pi == len(_bounds) - 1:
            W.append("-" * 72)
            W.append("-- ★★★ …AND IT IS WELL FORMED.")
            W.append("-" * 72)
            W.append("JudgeWf : IDescWf IJudge JudgeD")
            W.append("JudgeWf =")
            W.append(nest(["idwf-cons (jd%sWf JudgeD)" % nm if not row.prems
                           else "idwf-cons jd%sWf" % nm
                           for nm, row in rows], "idwf-nil", 2))
        open(os.path.join(out, "JudgeWf%s.agda" % part), "w").write(
            "\n".join(W) + "\n")
    return rows

# ============================ LAYER 3: THE ADEQUACY MAP ====================
# ★★★ `⌈_⌉ : RTm Γ → RTm ε` and its typing — the theorem that makes the
#   encoding MEAN something.  `Knot/Terms` shows ONE term encodes, by hand;
#   these 53 clauses show EVERY term does, and each clause is precisely the
#   check that its row's field structure matches the constructor it claims to
#   encode.  A swapped field order or a wrong index is well-formed,
#   inhabited, and simply encodes a different language — invisible without
#   this.
ENC   = {"sTy":"enTy","sTm":"enTm","sDesc":"enDesc","sDCon":"enDCon",
         "sIDesc":"enIDesc","sICon":"enICon","sVar":"enVar"}
FAMS  = {"cTy":"sTy","cTm":"sTm","cDesc":"sDesc","cDCon":"sDCon",
         "cIDesc":"sIDesc","cICon":"sICon","cVar":"sVar"}
# the three CLOSED sorts carry no context, so their lemmas take the depth
# as a parameter instead of reading it off an Agda type.
CLOSED = {"sDesc", "sDCon", "sIDesc"}
CARRIER = {"sTy":"Γ", "sTm":"Γ", "sVar":"Γ", "sICon":"Θ"}

def _ctor(decl): return decl.split(" : ")[0].strip()

def _names(c, nargs):
    if c == "_◃_": return {nargs[0]: "c", nargs[1]: "d"}
    if c == "_◂_": return {nargs[0]: "c", nargs[1]: "e"}
    return {j: f"y{j}" for j in nargs}

def _pat(c, nargs, an):
    if c in ("_◃_", "_◂_"): return f"({an[nargs[0]]} {c[1]} {an[nargs[1]]})"
    if not nargs: return c
    return "(" + c + " " + " ".join(an[j] for j in nargs) + ")"

def gen_map():
    L = [MAP_HDR]
    sigs_t, sigs_d = [], []
    for s, e in [("sTy","enTy"),("sTm","enTm"),("sDesc","enDesc"),
                 ("sDCon","enDCon"),("sIDesc","enIDesc"),("sICon","enICon"),
                 ("sVar","enVar")]:
        src = {"sTy":"RTy Γ","sTm":"RTm Γ","sDesc":"Desc","sDCon":"DCon",
               "sIDesc":"IDesc","sICon":"ICon Θ","sVar":"Var Γ"}[s]
        bind = ("{Γ Γ' : Cx}" if s in ("sTy","sTm","sVar")
                else "{Θ Γ' : Cx}" if s == "sICon" else "{Γ' : Cx}")
        sigs_t.append(f"{e} : {bind} → {src} → RTm Γ'")
        if s in CLOSED:
            sigs_d.append(f"⊢{e} : {{Δ : Ctx}} (n : ℕ) (u : {src}) →\n"
                          f"        Δ ⊢ {e} u ∷ K (pair {s} (num n))")
        else:
            car = CARRIER[s]
            sigs_d.append(f"⊢{e} : {{Δ : Ctx}} {{{car} : Cx}} (u : {src}) →\n"
                          f"        Δ ⊢ {e} u ∷ K (pair {s} (num (len {car})))")
    L += sigs_t + [""] + sigs_d + [""]
    # ---- the term clauses -------------------------------------------------
    for nm, decl, f in KNOT:
        sX = FAMS[nm.split("-")[0]]; e = ENC[sX]; c = _ctor(decl)
        nargs = [j for j, x in enumerate(f) if x[0] in ("rec", "nat")]
        an = _names(c, nargs)
        if nm == "cVar-vz":
            L.append("enVar {Γ = Γ ∙} vz = Var-vzK (num (len Γ))"); continue
        if nm == "cVar-vs":
            L.append("enVar {Γ = Γ ∙} (vs x) = Var-vsK (num (len Γ)) (enVar x)"); continue
        args = " ".join(f"(num {an[j]})" if f[j][0] == "nat"
                        else f"({ENC[f[j][1]]} {an[j]})" for j in nargs)
        L.append(f"{e} {_pat(c, nargs, an)} = {nm[1:]}K" + (" " + args if args else ""))
    L.append("")
    # ---- the typing clauses ----------------------------------------------
    for nm, decl, f in KNOT:
        sX = FAMS[nm.split("-")[0]]; e = ENC[sX]; c = _ctor(decl)
        nargs = [j for j, x in enumerate(f) if x[0] in ("rec", "nat")]
        an = _names(c, nargs)
        if nm == "cVar-vz":
            L.append("⊢enVar {Γ = Γ ∙} vz = ⊢Var-vzK (len Γ)"); continue
        if nm == "cVar-vs":
            L.append("⊢enVar {Γ = Γ ∙} (vs x) = ⊢Var-vsK (len Γ) (⊢enVar x)"); continue
        n_here = "n" if sX in CLOSED else f"(len {CARRIER[sX]})"
        ds = []
        for j in nargs:
            fl = f[j]
            if fl[0] == "nat": ds.append(f"(⊢num {an[j]})")
            elif fl[1] in CLOSED:
                sub = "n" if sX in CLOSED else f"(len {CARRIER[sX]})"
                if fl[2][0] == "lit": sub = str(fl[2][1])
                ds.append(f"(⊢{ENC[fl[1]]} {sub} {an[j]})")
            else: ds.append(f"(⊢{ENC[fl[1]]} {an[j]})")
        pre = f"⊢{e} " + ("n " if sX in CLOSED
                          else "{" + CARRIER[sX] + " = " + CARRIER[sX] + "} ")
        L.append(f"{pre}{_pat(c, nargs, an)} = ⊢{nm[1:]}K {n_here}"
                 + (" " + " ".join(ds) if ds else ""))
    return "\n".join(L) + "\n"


# ============================ STEP 3: `sz` — NO LONGER GENERATED ===========
# ⚠⚠ THE `sz` EMITTERS WERE DELETED 2026-08-26, and that is the result.
#   They produced ~1300 lines: 53 methods, 53 method ⊢ty's, 53 tuple rungs.
#   Enumerated, that cost 147s and TWO attempts to speed it up made it worse
#   (a naturality cast: 350s; a generic lemma at the rung: OOM), because the
#   enumeration lived in the CONSUMER and no better rung could remove it.
#
# ★★★ `Lib/ISz` removes it instead, by observing that the methods are not
#   arbitrary data: every one is `lam (lam (lam (suc <sum of IH entries>)))`
#   and the sum is fixed by the `ICon`'s RECURSIVE fields.  So the method is
#   COMPUTED from the constructor and the tuple from the description, both
#   by one induction at an ABSTRACT description.
#
#     enumerated (generated)   SzM 12s + Sz 135s = 147s
#     computed (`Lib/ISz`)     ISz  3s + Sz   2s =   5s      ~30×
#
#   `Examples/Knot/Sz.agda` is now 25 hand-written lines.

# ======================= STEP 4: the `sz` AGREEMENT, GENERATED ==============
# ⚠⚠ THE `sz` METHODS ARE **NOT** GENERATED (see the note above) — `Lib/ISz`
#   computes them.  What IS generated here is the AGREEMENT between the
#   encoded fold and `Metatheory/Canonicity`'s `szb`:
#
#       agree : szsTm i ⌈ t ⌉ ⟶* num (sz t)
#
#   one clause per `RTm` row.  The PLUMBING of each clause is proved once in
#   `Lib/ISzRed`; what is left is per-row and mechanical — for each field,
#   which peel reaches it and whether it is counted — which is exactly the
#   data this table already holds.  Written by hand it is 30 chances to get
#   a `βsnd` count wrong, and a wrong count still type-checks as long as it
#   happens to reach A field.

SZAGREE_HDR = """--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE `sz` AGREEMENT, ALL 30 `RTm` ROWS.
--
--     agree : szsTm i ⌈ t ⌉  ⟶*  num (sz t)
--
-- The encoded same-sort fold and `Metatheory/Canonicity`'s `szb` compute
-- the same number, AND the encoded one reduces to it.
--
-- ⚠ WHY THE SAME-SORT FOLD AND NOT `Lib/ISz`.  The knot's seven sorts
--   are ONE `IMu`, so a fold over it descends into all of them; `szb` is
--   a function on `RTm` and treats the other six as ATOMS.  Against
--   `Lib/ISz` this statement is FALSE on 5 of the 30 rows.  `Lib/ISzSort`
--   counts only same-sort children, and `Examples/Knot/SzProbe` checks
--   row by row that this reproduces `szb`.
--
-- ★★★ AND THE INDUCTION IS OVER `RTm` ALONE.  A cross-sort child — the
--   `Var` under `var`, the `Desc` under `⌜Mu⌝`, the `IDesc` and `RTy`
--   under `⌜IMu⌝` — is stepped PAST (`aih-ρ 0 ok`), never eliminated.
--   Nothing here needs the agreement at any other sort.
--
-- ⚠ TWO PEELS PER FIELD, AT DIFFERENT DEPTHS, AND THEY ARE NOT THE SAME
--   NUMBER.  `iihs` builds a tuple entry as `ielim … (fst p)`, so a
--   field is reached by projecting its entry out of the IH TUPLE — where
--   only RECURSIVE fields have slots — and separately reducing that
--   entry's SCRUTINEE down through the PAYLOAD, where EVERY field has a
--   slot.  For `con`/`icon` (a `ℕ` first) and `elim`/`ielim`/`⌜IMu⌝` (a
--   cross-sort field first) the two counts differ, and a wrong one still
--   type-checks whenever it happens to land on some other field.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SzAgree where
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; icon; ielim; app; iihs; ilookupD; isingle; _∈ID_
%s        )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; ι-ielim; β; βfst; βsnd )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-trans; ⟶*-appˡ; ⟶*-fst; ⟶*-snd; ⟶*-nsuc; ⟶*-ielimᵗ )
open import DirectedHoTT.Metatheory.Canonicity using ( sz )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.IFold using ( rowSort )
open import DirectedHoTT.Lib.ISzSort using ( szsMethod; szsMeths-sel )
open import DirectedHoTT.Lib.ISzRed
  using ( AllIH; aih-ι; aih-κ; aih-ρ; OK; ok; szsSum-red )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD
%s        )
open import DirectedHoTT.Examples.Knot.Tags
  using ( %s )
open import DirectedHoTT.Examples.Knot.Map using ( enTm )
open import DirectedHoTT.Examples.Knot.SzS using ( szsTm; szsMethsK )

-- chaining, so a row reads as the sequence of steps it is
infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
_»_ = ⟶*-trans

------------------------------------------------------------------------
-- ★ EVERY ROW OPENS THE SAME WAY, so this much is proved ONCE: the
--   ι-rule fires, and the row's method is selected out of the 53-tuple
--   in ONE step per row (`szsMeths-sel`).
--
-- ⚠ THE THREE βs CANNOT JOIN IT.  They substitute into the METHOD's
--   body, and at an abstract row that body is a stuck `szsSum` — the
--   substitution only computes once the `ICon` is concrete.  So they are
--   emitted per row, where they are three lines that always look alike.
------------------------------------------------------------------------

head-red : {Γ' : Cx} (k : ℕ) → k ∈ID KnotD → (i p : RTm Γ') {u : RTm Γ'} →
           app (app (app (szsMethod (ilookupD KnotD k)) i) p)
               (iihs KnotD szsMethsK (isingle i) (ilookupD KnotD k) p) ⟶* u →
           szsTm i (icon k p) ⟶* u
head-red k mem i p h =
  step (ι-ielim KnotD i szsMethsK k p)
       (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (szsMeths-sel KnotD k mem))) » h)

agree : {Γ Γ' : Cx} (i : RTm Γ') (t : RTm Γ) →
        szsTm i (enTm {Γ} {Γ'} t) ⟶* num (sz t)
"""

def _peel(k):
    "reduce `sndᵏ X` to the k-th tail of a literal right-nested pair"
    return "done" if k == 0 else \
        "(⟶*-snd %s » step (βsnd _ _) done)" % _peel(k - 1)

def _fstat(k):
    "reduce `fst (sndᵏ X)` to the k-th component"
    return "(⟶*-fst %s » step (βfst _ _) done)" % _peel(k)

RENAGREE_HDR = r"""--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ren-agree`, THE 25 SAME-SORT `RTm` ROWS.
--
--     renTmAtK sTm ⌈Γ⌉ ⌈Δ⌉ r ⌈t⌉  ⟶*  ⌈ renTm ρ t ⌉      given  RepresentsR ρ r
--
-- ⚠ PER-ROW LEMMAS, NOT ONE `agree` FUNCTION.  Five of the 30 `cTm-` rows
--   have CROSS-SORT recursive fields (`var`→sVar, `elim`/`cMu`→sDesc,
--   `ielim`/`cIMu`→sIDesc, `cIMu`→sTy) and need agreement at another sort,
--   i.e. a mutual statement.  A partial `agree` would not be exhaustive,
--   so each row is its own lemma and the knot is tied separately.
--   ★ `Knot/SzAgree` never faced this: it steps a cross-sort child PAST
--     (`aih-ρ 0 ok`) because the measure does not count it — but `renTm`
--     genuinely renames it.
--
-- ★★★ THE `SubCon` IS NOT EMITTED HERE.  `Knot/RenRed.wOf` reads each
--   row's classification off `decSubCon`, so a row is
--   `ren-head-red k ttsd ttsd refl` and there is no ford tag to get wrong.
--   ⚠ THAT IS NOT TIDINESS.  At the RENAMING instantiation `renFordMap fi
--     b p = p` IGNORES the tag while `fordMapK` uses it three times, so a
--     WRONG tag was MEASURED to leave a row GREEN and would have broken
--     only at `sub-agree`, one instantiation later — `FUTURE.md` D′.
--
-- ★ THREE SHAPES COVER THE TABLE, and depth is not a case split:
--     ford / ℕ field   — one projection
--     `rec` at depth 0 — IH at the SAME renaming (`extsN 0 d n σ = σ`)
--     `rec` at depth k — IH under `extR-Represents`, k times
--
-- ⚠ AND EACH ROW REDUCES THE ELIMINATOR'S **INDEX**, not just its
--   scrutinee: `subTm (isingle i) (var vz)` is `i`, so `snd i` is one
--   `βsnd` (under k `nsuc`s) from the depth the IH is stated at.  That is
--   a THIRD peel beyond the two `Knot/SzAgree`'s header warns about, and
--   it exists only because `ren-agree` is indexed by a depth `sz` has not.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenAgree%s where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; vz; vs; Ren; app; pair; icon; renTm; extR
        ; nzero; idrefl; ⌜Nat⌝; unit; snd; ilookupD
%s        )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; βfst; βsnd )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-ielimᵗ; ⟶*-ielimⁱ
        ; ⟶*-fst; ⟶*-snd; ⟶*-nsuc )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Examples.Knot.Map using ( enTm )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len; sTm; sTy; sDesc; sDCon; sIDesc; sICon; sVar )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK )
open import DirectedHoTT.Examples.Knot.RenRed using ( ren-head-red )
open import DirectedHoTT.Examples.Knot.SubAgree using ( RepresentsR; extR-Represents )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)
"""

# ====================== ren-agree ROWS, GENERATED =========================
# ⚠⚠ THE `SubCon` IS NOT EMITTED.  `Knot/RenRed.wOf` reads it off
#   `decSubCon`, so a row is `ren-head-red k ttsd ttsd refl` and there is no
#   ford tag for this emitter to get wrong.  That is deliberate: at the
#   RENAMING instantiation `renFordMap` IGNORES the tag (`fordMapK` uses it
#   three times), so a wrong tag was MEASURED to leave a row green and
#   would have surfaced only at `sub-agree`.  D′, designed out.
#
# ★ SCOPE: the 25 `cTm-` rows whose recursive fields are ALL `sTm`.  The
#   other five (`var`, `elim`, `ielim`, `cMu`, `cIMu`) need agreement at
#   another sort — a mutual statement `Knot/SzAgree` never needed, because
#   a fold steps a cross-sort child PAST while `renTm` renames it.

def _peelR(k):
    return "done" if k == 0 else "(⟶*-snd %s » step (βsnd _ _) done)" % _peelR(k - 1)

def _fstatR(k):
    return "(⟶*-fst %s » step (βfst _ _) done)" % _peelR(k)

def _depth(d):
    "field depth: D is 0, sucD(n) is n"
    return 0 if d == D else d[1]

def _extR(d):
    return "ρ" if d == 0 else "(extR " * d + "ρ" + ")" * d

def _cx(base, d):
    return base if d == 0 else "(" + base + " ∙" * d + ")"

def _repArg(d):
    "the `RepresentsR` witness at depth d — `extR-Represents` nested"
    return "h" if d == 0 else "(extR-Represents _ " * d + "h" + ")" * d

# ⚠ BIND EVERY PATTERN ARGUMENT, NOT JUST THE RECURSIVE ONES.  `con`/`icon`
#   take a `ℕ` FIRST, so a signature that binds only the `rec` fields uses
#   `y0` in the type without binding it.  ★ `Knot/SzAgree`'s header names
#   exactly these two rows as the place where the recursive index and the
#   field index diverge — the warning was accurate, and this is a second
#   way the same divergence bites.
def gen_renagree(tag, lo, hi):
    rows = []
    for k, (nm, decl, f) in enumerate(KNOT):
        if not nm.startswith("cTm-"): continue
        if any(x[0] == "rec" and x[1] != "sTm" for x in f): continue   # cross-sort
        rows.append((k, nm, decl, f))
    assert len(rows) == 25, f"expected 25 same-sort RTm rows, got {len(rows)}"
    rows = rows[lo:hi]
    L = [RENAGREE_HDR % (tag, "".join("        ; %s\n" % _ctor(d) for _, _, d, _ in rows))]
    for k, nm, decl, f in rows:
        c = _ctor(decl)
        nargs = [j for j, x in enumerate(f) if x[0] in ("rec", "nat")]
        an = _names(c, nargs)
        recs = [j for j, x in enumerate(f) if x[0] == "rec"]
        # ---- payload, right-nested -------------------------------------
        ent = []
        for j, fl in enumerate(f):
            if fl[0] == "rec":  ent.append("(enTm %s)" % an[j])
            elif fl[0] == "nat": ent.append("(num %s)" % an[j])
            else:               ent.append("(idrefl ⌜Nat⌝ %s)" % fl[2][1])
        pay = "unit"
        for e in reversed(ent): pay = "(pair %s %s)" % (e, pay)
        # ---- IH hypotheses ---------------------------------------------
        ihs = []
        for r, j in enumerate(recs):
            d = _depth(f[j][2])
            ihs.append(
                "          ({Θ' : Cx} {r' : RTm Θ'} → RepresentsR %s r' →\n"
                "             renTmAtK sTm (num (len %s)) (num (len %s)) r' (enTm %s)\n"
                "             ⟶* enTm (renTm %s %s)) →"
                % (_extR(d), _cx("Γ", d), _cx("Δ", d), an[j], _extR(d), an[j]))
        # ---- per-slot chains -------------------------------------------
        chains = []
        for j, fl in enumerate(f):
            if fl[0] == "rec":
                r = recs.index(j); d = _depth(fl[2])
                nsucs = "(⟶*-nsuc " * d + "(step (βsnd _ _) done)" + ")" * d
                body = ("(⟶*-appˡ (⟶*-appˡ %s) »\n"
                        "     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ %s)) »\n"
                        "     ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ %s))) »\n"
                        "     ih%d %s)" % (_fstatR(r), _fstatR(j), nsucs, r, _repArg(d)))
            else:
                body = _fstatR(j)
            wrap = "⟶*-icon (" + "⟶*-pairʳ (" * j + "⟶*-pairˡ\n    " + body + ")" * (j + 1)
            chains.append("  " + wrap)
        ihn = " ".join("ih%d" % r for r in range(len(recs)))
        L.append(
            "row-%s : {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} →\n"
            "          RepresentsR ρ r →%s\n"
            "%s"
            "          renTmAtK sTm (num (len Γ)) (num (len Δ)) r (enTm {Γ} {Θ} %s)\n"
            "          ⟶* enTm {Δ} {Θ} (renTm ρ %s)\n"
            "row-%s {Γ} {Δ} h %s%s =\n"
            "  ren-head-red %d ttsd ttsd refl\n"
            "               sTm (num (len Γ)) (num (len Δ)) _ %s »\n"
            "%s\n"
            % (nm[4:], "".join(" (%s : %s) →" % (an[j],
                       "ℕ" if f[j][0] == "nat"
                       else "RTm " + _cx("Γ", _depth(f[j][2])))
                       for j in nargs),
               "".join(x + "\n" for x in ihs),
               _pat(c, nargs, an), _pat(c, nargs, an),
               nm[4:], " ".join(an[j] for j in nargs), (" " + ihn) if ihn else "",
               k, pay, " »\n".join(chains)))
    return "\n".join(L) + "\n"

def gen_szagree():
    rows = [(nm, decl, f) for nm, decl, f in KNOT if nm.startswith("cTm-")]
    assert len(rows) == 30, f"expected 30 RTm rows, got {len(rows)}"
    ctors = sorted({_ctor(d) for _, d, _ in rows})
    imp_c = "".join("        ; %s\n" % c for c in ctors)
    imp_r = "".join("        ; %s\n" % nm for nm, _, _ in rows)
    tags  = "; ".join("tag%s; mem%s" % (nm[1:], nm[1:]) for nm, _, _ in rows)
    L = [SZAGREE_HDR % (imp_c, imp_r, tags)]
    for nm, decl, f in rows:
        c = _ctor(decl)
        nargs = [j for j, x in enumerate(f) if x[0] in ("rec", "nat")]
        an = _names(c, nargs)
        # ---- the AllIH witness, built from the INSIDE OUT ------------------
        aih, r = "aih-ι", sum(1 for x in f if x[0] == "rec")
        for j in range(len(f) - 1, -1, -1):
            fl = f[j]
            if fl[0] in ("nat", "ford"):
                aih = "(aih-κ %s)" % aih
            else:
                r -= 1                       # this field's index among the ρs
                if fl[1] == "sTm":           # COUNTED: owes a reduction
                    v = an[j]
                    aih = ("(aih-ρ (sz %s)\n     (%s » ⟶*-ielimᵗ %s » agree _ %s)\n     %s)"
                           % (v, _fstat(r), _fstat(j), v, aih))
                else:                        # CROSS-SORT: owes nothing
                    aih = "(aih-ρ 0 ok %s)" % aih
        # ⚠ A ROW WITH NO COUNTED FIELD NEEDS NO LEMMA — AND CANNOT USE ONE.
        #   `szsSum` at such a row reduces to `nzero` whatever the IH tuple
        #   is, so the tuple never appears in the goal and `szsSum-red`'s
        #   `ihs` is a meta with nothing to solve it.  The three βs already
        #   land on `nsuc nzero`, which IS `num (sz t)` here.
        counted = any(x[0] == "rec" and x[1] == "sTm" for x in f)
        tail = ("     step (β _ _) done)" if not counted else
                "     step (β _ _) done »\n"
                "     ⟶*-nsuc (szsSum-red (rowSort %s) %s\n     %s))" % (nm, nm, aih))
        L.append("agree i %s =\n"
                 "  head-red tag%s mem%s i _\n"
                 "    (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »\n"
                 "     ⟶*-appˡ (step (β _ _) done) »\n"
                 "%s"
                 % (_pat(c, nargs, an), nm[1:], nm[1:], tail))
    return "\n".join(L) + "\n"

# ====================== STEP 3: JUDGEMENT ROWS, GENERATED ==================
# ⚠⚠ MEASURED ON STEP 1: HAND-WRITING DOES NOT SCALE HERE.  `_∋_∷_`'s TWO
#   rows — 7 and 10 fields — cost a long session, and most of it was de
#   Bruijn bookkeeping reducible to ONE rule:
#
#       at `k` fields bound, field `j` sits at `vs^(k-1-j) vz`,
#       and the ambient index at `vs^k vz`.
#
#   ★★ AND A WRONG INDEX IS INVISIBLE AT THE `ICon` LEVEL.  An `ICon`
#   type-checks with ANY in-scope variable of the right type — the bug
#   found on 2026-08-26 (`λ₈` naming `Γ` where it meant `x`) was caught
#   only by the `IConWf`, and it surfaced there as the Wf demanding a slot
#   matching the WRONG term, which reads like a Wf bug.  So this is not
#   tedium: it is a transcription error waiting to happen, in the one
#   place where the error does not look like itself.
#
# ⇒ a row is DESCRIBED (binders · recursive premises · one value per index
#   component) and the positions are COMPUTED.

# ---- expressions -----------------------------------------------------------
def V(name):      return ('v', name)      # a binder, BY NAME — never by index
AMB             = ('amb',)                # the ambient index variable ⟨i⟩
def RAW(t):       return ('raw', t)
def AP(f, *a):    return ('ap', f, a)
def PAIR(a, b):   return ('pair', a, b)
def NSUC(a):      return ('nsuc', a)
def TUP(*a):
    e = a[-1]
    for x in reversed(a[:-1]): e = PAIR(x, e)
    return e

# ---- the index telescope ---------------------------------------------------
# each component is the CODE of its type, as a function of a depth expression
def TNAT():        return ('tnat',)
# ★★★ A COMPONENT THAT IS ANOTHER JUDGEMENT.
#
# ⚠ THE JUDGEMENTS ARE A CHAIN — `ξ-El : t ⟶ t' → El t ⟶ᵀ El t'` — and a
#   premise at a DIFFERENT judgement is NOT an `iρ` field.  `iρ` means
#   "recursive in the description being defined"; this is a value of a
#   FOREIGN family, which is a κ field carrying an `⌜IMu⌝` code, exactly
#   as `_∋_∷_`'s `Ctx` and `Var` components are.
#   ⇒ so `PLAN-JUDGEMENT`'s "the judgements form a chain" is, in the
#     encoding, the difference between `iρ` and `icw-imu`.
def TJ(desc, ity, wf, tel): return ('tj', desc, ity, wf, tel)
def TCTX():        return ('tctx',)
def TKNOT(sort):   return ('tknot', sort)
# ★ THE PER-TAG PAYLOAD SLOT (`SPIKE_SUM`) — an `IMu` over `Knot/IxD` at a
#   Nat index, i.e. structurally the same shape as the `Ctx` slot.
def TIX():         return ('tix',)

def _code(comp, d):
    """the object-level code for telescope component `comp` at depth `d`.
    ⚠ For a `tj` component `d` is the WHOLE index tuple, not a depth."""
    if comp[0] == 'tbool': return d
    if comp[0] == 'tj':    return AP("⌜IMu⌝", RAW(comp[1]), RAW(comp[2]), d)
    if comp[0] == 'tnat':  return RAW("⌜Nat⌝")
    if comp[0] == 'tctx':  return AP("⌜IMu⌝", RAW("CtxD"), RAW("INat"), d)
    if comp[0] == 'tix':   return AP("⌜IMu⌝", RAW("IxD"), RAW("INat"), d)
    return AP("⌜IMu⌝", RAW("KnotD"), RAW("IPair"), PAIR(RAW(comp[1]), d))

def _proj(c, n, e):
    """component `c` of an `n`-component right-nested telescope value `e`.
    ⚠ THE LAST ONE IS `snd`, NOT `fst (snd …)` — a right-nested Σ has no
      wrapper on its final component, and off by one here is a term that
      still type-checks at a DIFFERENT component."""
    for _ in range(c): e = AP("snd", e)
    return e if c == n - 1 else AP("fst", e)

def rend(e, k, ix):
    """`e` at a point where `k` fields are bound.  ★ THE ONLY PLACE THE
    de Bruijn RULE IS WRITTEN."""
    t = e[0]
    if t == 'v':    return dbv(k - 1 - ix[e[1]])
    if t == 'amb':  return dbv(k)
    if t == 'raw':  return e[1]
    if t == 'ap':   return e[1] + "".join(" " + par(rend(x, k, ix)) for x in e[2])
    if t == 'pair': return "pair %s %s" % (par(rend(e[1], k, ix)), par(rend(e[2], k, ix)))
    if t == 'nsuc': return "nsuc " + par(rend(e[1], k, ix))
    raise ValueError(e)

# ---- a row -----------------------------------------------------------------
class JRow:
    def __init__(self, name, binders, prems, vals):
        self.name, self.binders, self.prems, self.vals = name, binders, prems, vals

def jrow_fields(row, tel):
    """the row's fields, in order, as (kind, expression).  ★ BINDERS, THEN
    RECURSIVE PREMISES, THEN ONE FORD PER INDEX COMPONENT."""
    ix, out = {}, []
    for nm, code in row.binders:
        ix[nm] = len(out); out.append(('κ', code))
    for nm, tup in row.prems:
        ix[nm] = len(out); out.append(('ρ', tup))
    n = len(tel)
    depth_at = None
    for c in range(n):
        if c == 0:
            # the DEPTH ford: no transport, nothing to transport ALONG yet
            f = AP("⌜Id⌝", RAW("⌜Nat⌝"), AP("fst", AMB), row.vals[0])
            depth_at = len(out)
        else:
            # ★ every later component is stated at `fst ⟨i⟩` but BUILT at the
            #   row's own depth, so it is transported along the depth ford.
            ty_amb = _code(tel[c], AP("fst", AMB))
            ty_var = _code(tel[c], RAW("var vz"))
            f = AP("⌜Id⌝", ty_amb, _proj(c, n, AMB),
                   AP("jsub", ty_var,
                      AP("symN", AP("fst", AMB), V('#depth')),
                      row.vals[c]))
            ix['#depth'] = depth_at
        out.append(('κ', f))
    return ix, out


# ---- the Wf TWIN -----------------------------------------------------------
#
# ★★★ A SECOND EMITTER OVER THE SAME DESCRIPTION — the pair
#   `emit_icon`/`emit_iconwf` already is for the syntax rows, one level up.
#   The row description gains NOTHING: a binder's telescope component is
#   RECOVERED from the code expression it already carries.
#
# ⚠⚠ AND IT IS A TWIN OF `jrow_fields`, **NOT** OF `rend`.  Two nodes drop
#   information the derivation needs: `jsub d p e` takes three arguments
#   where `⊢jsub` takes FIVE, and `symN a p` takes two where `⊢symN` takes
#   THREE — the missing ones are the transport's ENDPOINTS.  Recovering
#   them from a finished expression is guesswork; building the derivation
#   where `row.vals[0]` and `fst ⟨i⟩` are still in hand is not.
#
# ⚠ THE CONTROL IS THAT IT TYPECHECKS, not that it equals the
#   hand-written proof.  Any inhabitant of `IConWf D I Θ C` is as good as
#   any other, and this emitter deliberately produces a DIFFERENT one —
#   `toI (fromI d)` where `Knot/Lookup` writes `d`, for instance.
#   Demanding proof-term equality would be a STRONGER demand than
#   correctness, and one a stray coercion would break.

# a smart constructor's typing lemma: (head, arg roles, post-conversion)
#   N  — coerce the argument to native `Nat`
#   MU — coerce it to a native `IMu`
#   IX — the argument is a `pair`; emit `⊢ixP` over it
# ⚠⚠ THE KNOT'S OWN CONSTRUCTORS TAKE NO TERM-LEVEL DEPTH, so their
#   typing lemma needs the ROW's depth derivation injected as its first
#   explicit argument.  That is the `DX` role, and it is why this table
#   is GENERATED from `KNOT` rather than written: 51 entries whose roles
#   are read straight off each row's field list.
WF_CTOR = {
    ("%sK" % n[1:]): ("⊢%sKv" % n[1:],
                      ["DX"] + ["N" if f[0] == "nat" else "MU"
                                for f in fs if f[0] in ("rec", "nat")],
                      None)
    for n, _, fs in KNOT if not n.startswith("cVar-")
}
WF_CTOR.update({
    # ★ THE TWO `Var` ROWS ALREADY HAD THEIR ARBITRARY-DEPTH FORM.
    #   `⊢Var-vzKt`/`⊢Var-vsKt` (`Knot/Build`) take the depth as an
    #   IMPLICIT term, solved from `Var-vzK d`'s own argument — so they
    #   need only its DERIVATION (`DD`), not the term again.
    #   ⚠ The table pointed at `⊢Var-vzKv` (`var x`) for two commits.
    #   The narrow twin was written first and shadowed the general one.
    "Var-vzK":  ("⊢Var-vzKt", ["DD"],       None),
    "Var-vsK":  ("⊢Var-vsKt", ["DD", "MU"], None),
    # ⚠ AND THE SAME NARROW-TWIN TRAP, a second time.  This pointed at
    #   `⊢Ctx-extKv` (`var x`) until `⊢natrec`, whose premise extends the
    #   context TWICE and so lands the outer `Ctx-extK` at `nsuc (var x)`
    #   — neither a numeral nor a variable, and no emitted row had ever
    #   needed one before.  `Knot/CtxD.⊢Ctx-extKt` is now the general
    #   form and the two narrow twins are one-liners over it.
    "Ctx-extK": ("⊢Ctx-extKt", ["N", "MU", "MU"], None),
    # ★ `wkK` lands at `sh (pair s m)` while the ford wants
    #   `pair s (nsuc m)` — the same two β-steps every time.
    "wkK":      ("⊢wkK",       ["IX", "MU"],      "WK"),
    # ★ `Knot/WkSub`'s pair — and they need NO post-conversion.  `wkK`
    #   lands at `sh (pair s m)` and owes two β-steps; these land at
    #   `pair s (nsuc m)` on the nose, because a `subTyAtK` result is
    #   already indexed by its TARGET depth.
    "wkTmK":    ("⊢wkTmK",     ["N", "MU"],       None),
    "wkTyK":    ("⊢wkTyK",     ["N", "MU"],       None),
    # ★★★ THE SUBSTITUTION WRAPPERS.  `Knot/SubApp` proved these; the
    #   roles say only WHERE each argument comes from.
    # ⚠ `DD`, NOT a fresh "current depth" role.  `_val` PREPENDS the
    #   depth, so by the time the derivation emitter walks the tree the
    #   depth is `args[0]` — synthesising it again from `DEPTHD` emits
    #   it twice and drops the last real argument off the end.
    "singleK":  ("⊢singleK",  ["DD", "MU"],       None),
    # ★ TWO depths — source then target.  `⊢subAtK` takes them apart
    #   because `nrs` RAISES; see `Knot/SubApp`.
    "subTmAtK": ("⊢subTmAtK", ["DD", "DD", "IX", "MU"], None),
    "subTyAtK": ("⊢subTyAtK", ["DD", "DD", "IX", "MU"], None),
    # ★ two depths consumed, then the substitution being extended.
    "extNK":    ("⊢extNK",    ["DD", "DD", "IX"],  None),
    # ★ lands at `sh ⟨i⟩` exactly as `wkK` does, so it needs the same two
    #   β-steps afterwards — the `WK` post.
    "pwBodyK":  ("⊢pwBodyK",  ["IX", "MU"],        "WK"),
    "nrsSubK":  ("⊢nrsSubK",  ["DD"],              None),
    "isingleK": ("⊢isingleK", ["DX", "MU"],        None),
    # ★★★ THE PER-TAG PAYLOAD (`Knot/IxD`).  `DX` hands each one the
    #   index TERM and then its derivation — the shape every nullary
    #   `…Kv` lemma takes — and the `MU`s are the merge-only subjects.
    # ⚠ `IxIConK`'s LAST subject is the only one at the row's depth; the
    #   rest are CLOSED, at absolute 0.  See `Knot/IxD`'s header for why
    #   that direction and not the ambient one.
    # ★ the empty context — `dwf-κ`'s `◇ ⊢ c ∷ U`, and the `Ctx` slot of
    #   every judgement that HAS no context.
    "Ctx-empK": ("⊢Ctx-empK", [],                        None),
    # ★★★ OBJECT-LEVEL `εwkTm` (`Knot/EWk`).  `SORT` is two arguments in
    #   one role: the sort's own derivation and the `sortMap s ⟶* s` that
    #   `⊢subAtK` asks for — both determined by the literal sort.
    "εwkK":     ("⊢εwkK",     ["SORT", "DD", "MU"],      None),
    "IxNoneK":  ("⊢IxNoneK",  ["DD"],                    None),
    "IxDConK":  ("⊢IxDConK",  ["DD", "MU"],              None),
    "IxDescK":  ("⊢IxDescK",  ["DD", "MU"],              None),
    "IxIConK":  ("⊢IxIConK",  ["DD", "MU", "MU", "MU"],  None),
    "IxIDescK": ("⊢IxIDescK", ["DD", "MU", "MU", "MU"],  None),
})

def _telty(comp):
    return ('nat',) if comp[0] == 'tnat' else ('mu', comp)

def _famwf(comp):
    if comp[0] == 'tj':   return comp[3]
    if comp[0] == 'tix':  return "IxWf"
    return "CtxWf" if comp[0] == 'tctx' else "KnotWf"

def _ixderiv(comp, dnat):
    """the family's INDEX derivation, from one at native `Nat`.
    ⚠ `CtxD`'s index is `INat` — already `El ⌜Nat⌝` — and `KnotD`'s is
      `Σ' Nat Nat`.  The two want OPPOSITE coercions, and this is the
      only place that difference is written down."""
    # ⚠ `tix` INDEXES BY A BARE `Nat`, exactly as `tctx` does — so it
    #   takes `toI`, and reading it as a knot sort emits `⊢ixP ⊢tix`.
    if comp[0] in ('tctx', 'tix'): return "toI " + par(dnat)
    return "⊢ixP ⊢%s %s" % (comp[1], par(dnat))

def _codewf(comp, dnat):
    "…and that the CODE itself is in `U`"
    if comp[0] == 'tnat': return "⊢⌜Nat⌝"
    return "⊢⌜IMu⌝ %s %s" % (_famwf(comp), par(_ixderiv(comp, dnat)))

# foreign judgements a row may cite, by their description name
FOREIGN = {}

def _binder_comp(code):
    """(component, depth-expression) recovered from a binder's CODE.
    ★ So the description does not have to say twice what it already says
      once — and the two emitters cannot drift apart about it."""
    if code[0] == 'raw':                       # ⌜Nat⌝
        return TNAT(), None
    _, h, args = code
    # ★ a BOOLEAN-PREMISE ford — `⌜Id⌝ ⌜Nat⌝ (fK ⟨i⟩ c) n`.  Carries the
    #   APPLICATION so the wf emitter can re-derive it.
    if h == "⌜Id⌝": return TBOOL(args[1], args[2]), None
    assert h == "⌜IMu⌝", code
    fam = args[0][1]
    if fam in FOREIGN: return FOREIGN[fam], args[2]
    if fam == "CtxD": return TCTX(), args[2]
    if fam == "IxD":  return TIX(), args[2]
    return TKNOT(args[2][1][1]), args[2][2]    # PAIR(RAW(sort), depth)

# ★★★ THE DEPTH IS THREADED THROUGH THE CONSTRUCTOR TREE, not guessed.
#
# ⚠⚠ A KNOT CONSTRUCTOR CARRIES NO TERM-LEVEL DEPTH, so its typing lemma
#   needs one injected — and it is NOT uniform down the tree.
#   `Tm-lamK (Tm-fstK x)` has its `lam` at the row's depth and its `fst`
#   one BINDER DEEPER.  Guessing "the row's depth" everywhere is right
#   for flat terms and silently wrong under a binder.
#
# ★ And the adjustment is already in the table: each field records its
#   index depth as `D` (same), `sucD k` (k deeper) or `lit k` (fixed).
DEPTHD = [None]

FIELD_DEPTH = {
    # ⚠ a `nat` field is a plain `Nat` binder with no index depth of its
    #   own; `('D',)` keeps the walk at the ambient one.
    ("%sK" % n[1:]): [(f[2] if f[0] == "rec" else ('D',))
                      for f in fs if f[0] in ("rec", "nat")]
    for n, _, fs in KNOT if not n.startswith("cVar-")
}

# ★★★ THE SUBSTITUTION WRAPPERS, and their SECOND argument sits one
#   binder deeper.  `subTm σ t` reads `t` under the binder the
#   substitution consumes — that is the whole content of "a substitution
#   lowers the depth by one", and it is the only thing the walk needs to
#   be told about them.
# ⚠⚠ INDEXED BY THE **SOURCE** POSITION — the same convention as
#   `FIELD_SORT`, and the one `infer_depths` reads.  THREE readers share
#   this table and only ONE of them walks the emitted tree:
#
#     `_val`          source args     → source index
#     `infer_depths`  source spines   → source index
#     `jd`            EMITTED tree    → source index MINUS the prepend
#
#   ⚠ I first resolved that collision the other way — moved the table to
#     emitted indexing and shifted `_val`.  That fixed the `_⟶_` path I
#     was looking at and broke `infer_depths`, which silently dropped
#     `⊢app`/`⊢pair`/`⊢snd`/`⊢jsub` back to `conflicting depths`: `B`
#     sits one binder deeper and inferred depth 0.  ⇒ the offset belongs
#     at the ONE reader that is different, not in the shared table.
FIELD_DEPTH.update({
    # ⚠ EMITTED positions: slot 0 is the prepended depth/index.
    "isingleK": [('D',)],
    "singleK":  [('D',), ('D',)],
    # ⚠ FOUR emitted slots since the wrappers took their SOURCE depth
    #   too: 0 source, 1 target, 2 the substitution, 3 the term.  The
    #   term's entry here is the DEFAULT — `_argshift` overrides it
    #   from the substitution, which is the only thing that knows.
    "subTmAtK": [('D',), ('D',), ('D',), ('sucD', 1)],
    "subTyAtK": [('D',), ('D',), ('D',), ('sucD', 1)],
    # ⚠ `extNK`'s substitution argument lives one binder SHALLOWER than
    #   the position `extS` appears at — it is the σ being extended.
    "extNK":    [('D',), ('D',), ('predD',)],
    # ★ `Var-vsK d x : K (sVar , nsuc d)` with `x` at `d` — its argument
    #   is one BELOW it.  Never stated before because no rule nested two
    #   variable constructors until `tr-pw`'s `var (vs vz)`.
    "Var-vsK":  [('D',), ('predD',)],
    # ⚠⚠ `wkK`'s BOTH arguments sit at the SOURCE depth — `wkK i t : K (sh i)`
    #   — so the derivation emitter must descend at `pred` of the ambient
    #   one.  Without this it read them at the RESULT depth, which was
    #   invisible while every `renTm vs X` had a bare binder for `X`
    #   (a binder's derivation ignores the threaded depth) and surfaced
    #   the moment `tr-pw` put a CONSTRUCTOR there.
    "wkK":      [('predD',), ('predD',)],
    # ★ the same two slots, and the same source depth — only the first
    #   argument changed shape, from a PAIR index to a bare depth.
    # ⚠ NOT `wkK`'s SHIFTS, though the two differ by one argument only.
    #   `wkK`'s slot 0 is a PAIR whose depth component is read at
    #   `pred dep`; `wkTmK`'s is that depth ITSELF, so it takes no shift —
    #   `singleK`/`subTmAtK` spell their depth arguments the same way.
    #   Only the weakened TERM sits at the source depth.
    "wkTmK":    [('D',), ('D',)],
    "wkTyK":    [('D',), ('D',)],
    "pwBodyK":  [('predD',), ('predD',)],
})

# ★★★ THE THREADED DEPTH IS STRUCTURED, NOT A STRING: `(base term, base
#   derivation, how many `nsuc`s)`.
#
# ⚠⚠ IT HAS TO BE.  Three consumers want different things of it — the
#   value emitter wants the TERM, the derivation emitter wants the
#   DERIVATION, and `Var-vzK`/`Var-vsK` want the PREDECESSOR of both,
#   because their argument is their SOURCE depth.  Carrying only the two
#   rendered strings makes the predecessor un-takeable, and adjusting one
#   string without the other puts them out of step — which surfaces as a
#   mismatch in the constructor's index, far from the cause.
def _dep_t(dep):  return nsucs(dep[2], dep[0])
def _dep_d(dep):  return dnsucs(dep[2], dep[1])

def _dep_pred(dep):
    if dep[2] == 0:
        raise ValueError("a Var at a non-successor depth: %r" % (dep,))
    return (dep[0], dep[1], dep[2] - 1)

def _deepen(dep, E):
    "the depth for a field whose index sits at `E`"
    if E[0] == "predD": return _dep_pred(dep)
    if E[0] == "lit":  return ("num %d" % E[1], "⊢num %d" % E[1], 0)
    if E[0] == "D":    return dep
    if E[0] == "sucD": return (dep[0], dep[1], dep[2] + E[1])
    return dep                      # `fld` — the field names another field

def jd(e, k, ix, binders, tel):
    """(text, ty) — `e`'s derivation at `k` bound fields, at its NATIVE
    type.  ty is ('nat',) | ('mu', comp) | ('tel', c) | ('u',)."""
    t = e[0]
    if t == 'v':
        comp = binders[e[1]]
        txt = dbd(k - 1 - ix[e[1]])
        if comp[0] == 'tnat': return ("fromI (%s)" % txt, ('nat',))
        return ("fromMu (%s)" % txt, ('mu', comp))
    if t == 'amb':
        return (dbd(k), ('tel', 0))
    if t == 'raw':
        if e[1] == "⌜Nat⌝": return ("⊢⌜Nat⌝", ('u',))
        return ("⊢" + e[1], ('nat',))
    if t == 'nsuc':
        return ("⊢nsuc " + par(jdAt(e[1], k, ix, binders, tel, 'nat')), ('nat',))
    if t == 'pair':
        return ("⊢ixP %s %s" % (par(jdAt(e[1], k, ix, binders, tel, 'nat')),
                                par(jdAt(e[2], k, ix, binders, tel, 'nat'))),
                ('ipair',))
    if t == 'ap':
        h, args = e[1], e[2]
        if h in ('fst', 'snd'):
            inner, ity = jd(args[0], k, ix, binders, tel)
            assert ity[0] == 'tel', ("projection off a non-telescope", e)
            c = ity[1]
            if h == 'fst':
                return ("⊢fst " + par(inner), _telty(tel[c]))
            # ⚠ THE LAST COMPONENT HAS NO `fst`.  A right-nested Σ ends
            #   bare, and off by one here is a derivation that still
            #   typechecks — at a DIFFERENT component.
            nxt = ('tel', c + 1) if c + 2 < len(tel) else _telty(tel[c + 1])
            return ("⊢snd " + par(inner), nxt)
        if h in WF_CTOR:
            head, roles, post = WF_CTOR[h]
            # ★★★ A CONSTRUCTOR THAT TAKES ITS DEPTH EXPLICITLY RESETS
            #   THE THREAD.  `Ctx-extK m Γ A : Ctx (nsuc m)` — its
            #   CONTENTS live at `m`, not at the `nsuc m` the enclosing
            #   index sits at.  It is not a `KNOT` row, so `FIELD_DEPTH`
            #   has nothing to say and its children were inheriting the
            #   ambient depth.
            _saved = DEPTHD[0]
            if roles and roles[0] == "N" and args:
                _b, _n = args[0], 0
                while _b[0] == "nsuc": _b, _n = _b[1], _n + 1
                DEPTHD[0] = (rend(_b, k, ix),
                             jdAt(_b, k, ix, binders, tel, 'nat'), _n)
            ds, ai = [], 0
            for r in roles:
                if r == 'DD':
                    # ★ CONSUME the depth the TERM already carries, and
                    #   emit its derivation.  ⚠ Synthesising it from the
                    #   threaded depth instead double-counts: `Var-vsK`'s
                    #   first argument IS its source depth, whether the
                    #   row was hand-written or parsed.
                    a = args[ai]; ai += 1
                    ds.append(par(jdAt(a, k, ix, binders, tel, 'nat')))
                    continue
                if r == 'SORT':
                    a = args[ai]; ai += 1
                    _s = a[1]
                    ds.append("⊢" + _s); ds.append(SORTMAP_LEM[_s])
                    continue
                if r == 'DX':
                    # ★ the ROW's depth — the TERM and then its
                    #   derivation, in that order.
                    ds.append(par(_dep_t(DEPTHD[0])))
                    ds.append(par(_dep_d(DEPTHD[0])))
                    continue
                a = args[ai]
                # ★ descend at the field's OWN depth
                # ★★★ ONE CONVENTION: `FIELD_DEPTH` is indexed by the
                #   EMITTED position, which is what `ai` counts.  ⚠ It used
                #   to be SOURCE-indexed with the offset applied here, and
                #   the two readers drifted FOUR times in two days
                #   (`FIELD_DEPTH` vs `infer_depths`, `DDEP`, `_IX_PRE`,
                #   and `wkK`/`Var-vsK` which had been wrong since they
                #   were written).  ⇒ the emitters agree by construction
                #   now; `_val` adds the offset instead, once.
                _si = ai
                # ⚠ THE SUBSTITUTION MOVED.  It is at emitted slot
                #   `_PRE_N[h]`, which stopped being 1 when the two
                #   `subAtK` wrappers took their source depth as well.
                _sgi = _PRE_N.get(h, 1)
                _sg = args[_sgi] if len(args) > _sgi else None
                sub = _deepen(DEPTHD[0], _argshift(h, _si, _sg))
                ai += 1
                keep = DEPTHD[0]; DEPTHD[0] = sub
                ds.append(par(jd(a, k, ix, binders, tel)[0]) if r == 'IX'
                          else par(jdAt(a, k, ix, binders, tel,
                                        'nat' if r == 'N' else 'mu')))
                DEPTHD[0] = keep
            DEPTHD[0] = _saved
            txt = head + "".join(" " + d for d in ds)
            if post == 'WK':
                txt = ("muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _))) "
                       "(muFwd (ξ-pairˡ (βfst _ _)) (%s))" % txt)
            return (txt, ('mu', ('opaque',)))
        raise ValueError("no Wf rule for head %r" % (h,))
    raise ValueError(e)

def jdAt(e, k, ix, binders, tel, want):
    "…coerced to `want` ∈ {'nat', 'mu', 'el'}"
    txt, ty = jd(e, k, ix, binders, tel)
    if ty[0] == 'tel': ty = _telty(tel[ty[1]])
    if want != 'el': return txt
    return ("toI " if ty[0] == 'nat' else "toMu ") + par(txt)

def _codety(comp, dnat):
    "the index component's TYPE is well formed"
    if comp[0] == 'tnat': return "ty-Nat"
    return "ty-IMu %s %s" % (_famwf(comp), par(_ixderiv(comp, dnat)))

def _tailty(c, t, tel, depfn):
    """the ⊢ty of the index telescope's TAIL from component `c`, `t` Σ
    binders deep.  ⚠ `⊢pair`'s FIRST argument is the ⊢ty of the TAIL, not
    of the head — and each component sits one binder deeper than the
    last, which is what `t` counts."""
    head = _codety(tel[c], depfn(t))
    if c == len(tel) - 1: return head
    return "ty-Σ %s %s" % (par(head), par(_tailty(c + 1, t + 1, tel, depfn)))

def _wks(t, txt):
    return ("⊢wk (" * t) + txt + (")" * t)

def _tupcomps(e):
    "a right-nested `pair` tuple, flattened"
    out = []
    while e[0] == 'pair':
        out.append(e[1]); e = e[2]
    out.append(e)
    return out

def _tupderiv(comps, tel, k, vis, bty):
    """the index TUPLE's typing — a right-nested `⊢pair`, each carrying
    the ⊢ty of its TAIL.

    ★ SHARED by the `iρ` rung and by a FOREIGN-JUDGEMENT κ field, because
      they need the same thing: a value of a family indexed by a
      telescope.  The only difference is which description it belongs to,
      and that is the caller's `tel`."""
    # ⚠⚠ SET THE THREADED DEPTH FROM *THIS* TUPLE.  `DEPTHD` is global
    #   mutable state, set by the ford branch; a premise's values are
    #   derived here, so without this they read the depth of whichever
    #   ford rung ran last.  The symptom is a constructor applied to the
    #   AMBIENT INDEX where its depth belongs, and it surfaces as an
    #   unsolved context meta — nowhere near the cause.
    _b, _n = comps[0], 0
    while _b[0] == "nsuc": _b, _n = _b[1], _n + 1
    _keep = DEPTHD[0]
    DEPTHD[0] = (rend(_b, k, vis), jdAt(_b, k, vis, bty, tel, 'nat'), _n)
    m = len(tel)
    body = None
    for j in range(m - 2, -1, -1):
        if j == 0:
            depfn = lambda t: dbd(t)
        else:
            d0 = jdAt(comps[0], k, vis, bty, tel, 'nat')
            depfn = (lambda d0: (lambda t: _wks(t, d0)))(d0)
        ty = _tailty(j + 1, 0 if j == 0 else 1, tel, depfn)
        head = par(jdAt(comps[j], k, vis, bty, tel, 'nat' if j == 0 else 'mu'))
        if body is None:
            body = "⊢pair %s %s %s" % (par(ty), head,
                     par(jdAt(comps[m - 1], k, vis, bty, tel, 'mu')))
        else:
            body = "⊢pair %s %s\n      (%s)" % (par(ty), head, body)
    DEPTHD[0] = _keep
    return body

def emit_jrowwf(row, tel, pre, ity, wfname, idesc=None, share=0, topname=None):
    """the `IConWf` chain for one row — one lemma per field, innermost
    first, exactly as `Knot/Lookup` writes them by hand.

    ⚠⚠ `D` STAYS A PARAMETER ONLY FOR A ROW WITH NO RECURSIVE PREMISE.
      `IConWf` mentions `D` only at `iwf-ρ` — but the row's TELESCOPE
      mentions it too, from the premise onwards: that field extends the
      context by `IMu D I ρ`.  ⇒ a row with a premise is proved at the
      CONCRETE description, and its post-premise contexts have to be
      re-declared at `Ctx` level, because `emit_jrow` had to drop to a
      bare `Cx` there to stay writable before `D` existed."""
    ix, fs = jrow_fields(row, tel)
    T, F = pre
    bty = {nm: _binder_comp(code)[0] for nm, code in row.binders}
    bdep = {nm: _binder_comp(code)[1] for nm, code in row.binders}
    n, nb, npr = len(tel), len(row.binders), len(row.prems)
    depth_at = ix.get('#depth')
    L, W = [], "W_" + T
    para = (npr == 0)
    if not para:
        assert idesc is not None, "a row with a premise needs its description"
        rho = next(j for j, (kd, _) in enumerate(fs) if kd == 'ρ')
        names = ["%s%d" % (T, j) for j in range(rho + 1, len(fs) + 1)]
        L.append("-- ★ the telescope, back at `Ctx` level: `emit_jrow` had to")
        L.append("--   drop to a bare `Cx` at the premise to stay writable")
        L.append("--   before `%s` existed." % idesc)
        L.append("%s : Ctx" % " ".join(names))
        # ⚠ EXTEND BY FIELD KIND, NOT BY POSITION.  `ctrnᵀ` has TWO
        #   recursive premises, and assuming "the first is `iρ`, the rest
        #   are `iκ`" gives the second one an `El` where it needs an
        #   `IMu` — a context that is wrong only from that field on.
        for j in range(rho, len(fs)):
            ext = ("IMu %s %s %s%d" % (idesc, ity, F, j)) if fs[j][0] == 'ρ' \
                  else ("El %s%d" % (F, j))
            L.append("%s%d = %s%d ▹ %s" % (T, j + 1, T, j, ext))
        L.append("")
    for k in range(len(fs) - 1, -1, -1):
        # ★★★ THE SHARED TOP RUNGS ARE NOT EMITTED — see `topname`.
        if share and k < share: continue
        kind, e = fs[k]
        vis = {nm: j for nm, j in ix.items() if j < k or nm == '#depth'}
        damb = dbd(k)
        inner = ("iwf-ι" if k == len(fs) - 1
                 else ("%s%d" % (W, k + 1)) + ("" if npr == 0 else ""))
        if k < len(fs) - 1 and npr == 0: inner = "%s%d" % (W, k + 1)
        if kind == 'ρ':
            # ★★★ THE RECURSIVE PREMISE.  Its derivation is the index
            #   TUPLE's typing: a right-nested `⊢pair`, each carrying the
            #   ⊢ty of its TAIL.
            body = _tupderiv(_tupcomps(e), tel, k, vis, bty)
            rung = "iwf-ρ %s%d\n    (%s)" % (F, k, body)
            C = "C" + T
            L.append("%s%d : ICon ⌊ %s%d ⌋" % (C, k, T, k))
            L.append("%s%d = iρ %s%d %s" % (C, k, F, k,
                     "iι" if k == len(fs) - 1 else "%s%d" % (C, k + 1)))
            L.append("%s%d : IConWf %s %s %s%d %s%d"
                     % (W, k, idesc, ity, T, k, C, k))
            L.append("%s%d =\n  %s\n    %s" % (W, k, rung, inner))
            L.append("")
            continue
        if k < nb:
            comp = bty[row.binders[k][0]]
            if comp[0] == 'tnat':
                rung = "iwf-κ %s%d (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝" % (F, k)
            elif comp[0] == 'tj':
                # ★ A FOREIGN JUDGEMENT'S ELEMENT — a κ field carrying an
                #   `⌜IMu⌝` code over ANOTHER description, and its
                #   well-formedness is that description's `IDescWf`.
                dep = bdep[row.binders[k][0]]
                rung = ("iwf-κ %s%d (icw-imu %s %s)\n    (⊢⌜IMu⌝ %s %s)"
                        % (F, k, par(rend(dep, k, vis)), _famwf(comp),
                           _famwf(comp),
                           par(_tupderiv(_tupcomps(dep), comp[4], k, vis, bty))))
            elif comp[0] == 'tbool':
                # ★★★ A BOOLEAN-PREMISE FORD.  The code is
                #   `⌜Id⌝ ⌜Nat⌝ (fK ⟨i⟩ c) n`, so `icw-ford` discharges the
                #   `ICodeWf` outright and the ⊢ty obligation is the
                #   function's own typing lemma at the argument.
                # ⚠ `bdep` HAS NO ENTRY for this binder — its depth is not
                #   an index component — which is why the generic branch
                #   below crashed on `None` before this case existed.
                _app = comp[1]                      # AP(fnK, ix, arg)
                _fn  = _app[1]
                _dfn = next(d for (f, d, _sr) in BOOL_PREM.values() if f == _fn)
                _ixe, _arge = _app[2][0], _app[2][1]
                # ⚠ the LITERAL comes from the code, not from a constant
                #   here: `≡ true` and `≡ false` are both legal premises
                #   and they differ only in this numeral.
                _lit = comp[2][1]                   # RAW("num n")
                rung = ("iwf-κ %s%d (icw-ford _ _ _)\n"
                        "    (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (%s %s %s)) (toI (⊢%s)))"
                        % (F, k, _dfn,
                           par(jd(_ixe, k, vis, bty, tel)[0]),
                           par(jdAt(_arge, k, vis, bty, tel, 'mu')),
                           _lit))
            else:
                dep = bdep[row.binders[k][0]]
                dnat = jdAt(dep, k, vis, bty, tel, 'nat')
                rung = ("iwf-κ %s%d (icw-imu %s %s)\n    %s"
                        % (F, k, par(rend(_ixterm(comp, dep), k, vis)),
                           _famwf(comp), par(_codewf(comp, dnat))))
        else:
            c = k - nb - npr
            d0 = jdAt(row.vals[0], k, vis, bty, tel, 'nat')
            if c == 0:
                rung = ("iwf-κ %s%d (icw-ford _ _ _)\n"
                        "    (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (%s))) (toI %s))"
                        % (F, k, damb, par(d0)))
            else:
                comp = tel[c]
                # ★★★ DEF-LIFT THE AMBIENT PROJECTION.  `⊢fst ⟨i⟩` appears
                #   three times in every ford rung and its term appears
                #   twice more.  A named `Def` is SHARED by Agda's term
                #   traversals; an inline copy is walked once per
                #   occurrence, by every phase.  `check.sh`'s own header
                #   makes this argument about `⊢strong-base'`.
                A = "a%s%d" % (T, k)
                L.append("%s : %s%d ⊢ fst (%s) ∷ Nat" % (A, T, k, amb(k)))
                L.append("%s = ⊢fst (%s)" % (A, damb))
                # ★ the row's depth — TERM and derivation — for the tree
                #   below.
                # ⚠ THE ROW'S OWN DEPTH CAN ALREADY CARRY `nsuc`s — a
                #   rule whose conclusion is at `nsuc m` is ordinary.
                #   Peel them into the counter, or a `Var` inside such a
                #   row has no predecessor to take.
                _b, _n = row.vals[0], 0
                while _b[0] == "nsuc": _b, _n = _b[1], _n + 1
                DEPTHD[0] = (rend(_b, k, vis),
                             jdAt(_b, k, vis, bty, tel, 'nat'), _n)
                rung = ("iwf-κ %s%d (icw-ford _ _ _)\n"
                        "    (⊢⌜Id⌝ %s\n"
                        "           %s\n"
                        "           (⊢jsub %s\n"
                        "                  (toI %s)\n"
                        "                  (toI %s)\n"
                        "                  (⊢symN %s %s\n"
                        "                         (fordAs (%s)))\n"
                        "                  %s))"
                        % (F, k,
                           par(_codewf(comp, A)),
                           par(jdAt(_proj(c, n, AMB), k, vis, bty, tel, 'el')),
                           par(_codewf(comp, "fromI (⊢var here)")),
                           par(d0), A, A, par(d0),
                           dbd(k - 1 - depth_at),
                           par(jdAt(row.vals[c], k, vis, bty, tel, 'el'))))
        # ★ NAME THE SUFFIX and build it from the next one in — linear,
        #   the way `Knot/Lookup` writes it by hand.
        C = "C" + T
        L.append("%s%d : ICon ⌊ %s%d ⌋" % (C, k, T, k))
        L.append("%s%d = %s %s%d %s" % (C, k, 'iκ' if kind == 'κ' else 'iρ',
                                        F, k,
                                        "iι" if k == len(fs) - 1
                                        else "%s%d" % (C, k + 1)))
        if para:
            L.append("%s%d : (D : IDesc) → IConWf D %s %s%d %s%d"
                     % (W, k, ity, T, k, C, k))
            L.append("%s%d D =\n  %s\n    (%s)" % (W, k, rung,
                     inner if inner == "iwf-ι" else inner + " D"))
        else:
            L.append("%s%d : IConWf %s %s %s%d %s%d"
                     % (W, k, idesc, ity, T, k, C, k))
            L.append("%s%d =\n  %s\n    %s" % (W, k, rung, inner))
        L.append("")
    if share:
        # ★★★ THE TOP OF THE CHAIN IS A LEMMA, NOT A COPY.  Rungs 0..n-1
        #   are identical in EVERY row — the depth binder and the context
        #   binder — but they are the OUTERMOST rungs, so each row's copy
        #   wraps that row's own inner chain and is a different TERM.
        #   ⇒ unshareable as a VALUE, shareable as a FUNCTION over the
        #     tail.  Same move as `Lib/IPay`'s `⊢methLam`.
        # ★ AND THE POINT IS THE PAYLOAD, NOT THE SHAPE: the `⊢ty`
        #   obligations in those rungs (`⊢⌜Nat⌝`, `⊢⌜IMu⌝ CtxWf …`) were
        #   re-discharged once per row and are now discharged ONCE.
        if para:
            L.append("%s : (D : IDesc) → IConWf D %s %s0 %s"
                     % (wfname, ity, T, row.name))
            L.append("%s D = %s D (%s%d D)" % (wfname, topname, W, share))
        else:
            L.append("%s : IConWf %s %s %s0 %s"
                     % (wfname, idesc, ity, T, row.name))
            L.append("%s = %s %s (%s%d)" % (wfname, topname, idesc, W, share))
    elif para:
        L.append("%s : (D : IDesc) → IConWf D %s %s0 %s" % (wfname, ity, T, row.name))
        L.append("%s = %s0" % (wfname, W))
    else:
        L.append("%s : IConWf %s %s %s0 %s" % (wfname, idesc, ity, T, row.name))
        L.append("%s = %s0" % (wfname, W))
    return "\n".join(reversed_blocks(L))

def reversed_blocks(L):
    "the rungs come out innermost-first; Agda wants them declared that way"
    return L

def _ixterm(comp, dep):
    "the index TERM an `icw-imu` names"
    return dep if comp[0] == 'tctx' else PAIR(RAW(comp[1]), dep)

def _conFrom(fs, F, k):
    """the ICon suffix from field `k` on, INLINE.

    ⚠⚠ QUADRATIC, AND THAT IS WHY IT IS NO LONGER USED.  Rung 0 spells
      out all n fields, rung 1 all n-1, … — n(n+1)/2 `iκ` nodes where n
      would do.  `Knot/Lookup` names each suffix by hand
      (`C₅ = iκ κ₅ C₆`) and is LINEAR; the emitter inlining them is a
      specialisation of exactly the kind this project keeps paying for.
      Kept only to document the shape."""
    body = "iι"
    for j in range(len(fs) - 1, k - 1, -1):
        body = "%s %s%d (%s)" % ('iκ' if fs[j][0] == 'κ' else 'iρ', F, j, body)
    return "(%s)" % body

def emit_jrow(row, tel, pre, ity, idesc):
    """the Θ/κ/ICon chain for one row.  `pre` names the row's telescope
    variables (`Θ`/`κ` for one row, `Ξ`/`λ` for the next…).

    ⚠ THE TELESCOPE STOPS BEING A `Ctx` AT THE FIRST RECURSIVE PREMISE.
      That field extends by `IMu D I …`, which mentions the description
      being DEFINED.  `⌊_⌋` only COUNTS, so everything after it is typed
      at a plain `Cx` and the row stays writable before `D` exists; the
      `Ctx`-level telescope comes back where the Wf is proved."""
    ix, fs = jrow_fields(row, tel)
    T, F = pre
    X = "X" + T
    L = [f"{T}0 : Ctx", f"{T}0 = ◇ ▹ εwkTy {ity}", ""]
    cur, is_ctx = f"{T}0", True
    for k, (kind, e) in enumerate(fs):
        vis = {n: j for n, j in ix.items() if j < k or n == '#depth'}
        L.append(f"{F}{k} : RTm {('⌊ ' + cur + ' ⌋') if is_ctx else cur}")
        L.append(f"{F}{k} = {rend(e, k, vis)}")
        L.append("")
        nxt = (f"{T}{k+1}" if is_ctx and kind == 'κ' else f"{X}{k+1}")
        if is_ctx and kind == 'κ':
            L += [f"{nxt} : Ctx", f"{nxt} = {cur} ▹ El {F}{k}", ""]
        elif is_ctx:
            L += [f"{nxt} : Cx", f"{nxt} = ⌊ {cur} ⌋ ∙", ""]
            is_ctx = False
        else:
            L += [f"{nxt} : Cx", f"{nxt} = {cur} ∙", ""]
        cur = nxt
    body = "iι"
    for k in range(len(fs) - 1, -1, -1):
        body = f"{'iκ' if fs[k][0] == 'κ' else 'iρ'} {F}{k} ({body})"
    L.append(f"{row.name} : ICon (ε ∙)")
    L.append(f"{row.name} = {body}")
    return "\n".join(L)

LOOKUPGEN_HDR = """--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE JUDGEMENT-ROW EMITTER'S **CONTROL**.
--
-- `Examples/Knot/Lookup` writes `_∋_∷_`'s two rows BY HAND — 7 and 10
-- fields, four transported Forded components each.  This module has the
-- generator emit the same two rows from a DESCRIPTION (binders ·
-- recursive premises · one value per index component) and checks the
-- results are `refl`-equal to the hand-written ones.
--
-- ★★ WHY A CONTROL AND NOT A REPLACEMENT.  Same role `Examples/Knot/
--   WkRows` plays for `Lib/IWk`: the hand-written rows were derived
--   independently, so agreement is evidence.  Delete them and the
--   generator is only checked against itself.
--
-- ⚠⚠ AND THE ERROR THIS CATCHES IS INVISIBLE OTHERWISE.  An `ICon`
--   type-checks with ANY in-scope variable of the right type, so a field
--   naming the wrong binder is well-typed.  The real bug of 2026-08-26
--   — `λ₈` naming `Γ` where it meant `x` — surfaced only in the
--   `IConWf`, and there it looked like a Wf bug.  The one rule the
--   generator centralises is exactly the one that was got wrong:
--
--       at `k` fields bound, field `j` sits at `vs^(k-1-j) vz`,
--       and the ambient index at `vs^k vz`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.LookupGen where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; var; vz; vs; pair; fst; snd; nsuc; El; IMu; Nat
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub; ICon; IDesc; iι; iρ; iκ; εwkTy )
open import DirectedHoTT.Spec.Typing using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_ )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; sTy; sVar )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.CtxD using ( CtxD; INat; Ctx-extK )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK; wkTyK )
open import DirectedHoTT.Lib.ArithComm using ( symN )
open import DirectedHoTT.Spec.Typing
  using ( IConWf; iwf-ι; iwf-κ; iwf-ρ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; ⊢pair; ty-Σ; ty-Nat; ty-IMu
        ; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nsuc
        ; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ξ-pairˡ; ξ-pairʳ; ξ-nsuc; βfst; βsnd )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( toI; fromI; ⊢ixP; ⊢sTy; ⊢sVar )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.CtxD using ( CtxWf; ⊢Ctx-extKt )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Wk using ( ⊢wkK )
open import DirectedHoTT.Examples.Knot.WkSub using ( ⊢wkTmK; ⊢wkTyK )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( ⊢symN )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Lookup
  using ( ILk; LkD; lkHere; lkThere )

"""

REDROWS_HDR = """--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `_⟶_`, THE REDUCTION JUDGEMENT.
--
-- ⚠⚠ THE RULES ARE **PARSED OUT OF `Spec/Typing.agda`**, not transcribed.
--   166 hand-written table entries is 166 chances to name the wrong
--   variable — the error class `Knot/LookupGen` exists to catch, and one
--   an `ICon` never reveals because it type-checks with ANY in-scope
--   variable of the right type.  The Agda-former → knot-constructor map
--   comes from `KNOT`'s own `decl` strings, so nothing is typed twice.
--
-- ★ AND THE SKIPPED RULES ARE NAMED BELOW.  Emitting 65 of 73 rows
--   without saying so would be exactly
--   `verification-that-covers-less-than-it-claims`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedRows where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; var; vz; vs; pair; fst; snd; nsuc; nzero
        ; El; IMu; Σ'; Nat
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub; ICon; IDesc; iι; iρ; iκ; inil; _◂_; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_
        ; IConWf; iwf-ι; iwf-κ; iwf-ρ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nsuc; ⊢nzero
        ; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ⊢pair; ty-Σ; ty-Nat; ty-IMu
        ; ξ-pairˡ; ξ-pairʳ; ξ-nsuc; βfst; βsnd )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; toI; fromI; ⊢ixP; ⊢sTy; ⊢sTm; ⊢sDesc; ⊢sDCon; ⊢sIDesc; ⊢sICon; ⊢sVar
        ; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.CtorsV
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Single using ( singleK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK; subTyAtK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK )
open import DirectedHoTT.Examples.Knot.Pw using ( pwK )
open import DirectedHoTT.Examples.Knot.Stk using ( stkAK; stkCK; flatK )
open import DirectedHoTT.Examples.Knot.Nrs using ( nrsSubK )
open import DirectedHoTT.Examples.Knot.PwBody using ( pwBodyK )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK; wkTyK )

-- ★ the judgement's index: a depth and two terms at it.
IRed : RTy ε
IRed = Σ' Nat (Σ' (IMu KnotD IPair (pair sTm (var vz)))
                  (IMu KnotD IPair (pair sTm (var (vs vz)))))

"""

_GREEK = "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ"
_ROWS, _SKIP = [], []

def _tagof(i):
    return _GREEK[i % len(_GREEK)] + ("" if i < len(_GREEK)
                                      else _GREEK[i // len(_GREEK)])

# ⚠⚠ THE DEPTH BINDER'S KEY MUST NOT BE AN AGDA IDENTIFIER.  `tr-J-Mu`
#   binds its own `m`, and a row whose depth variable is also called `m`
#   either crashes the emitter (if the orders differ) or — worse —
#   silently resolves to the RULE's `m`.  `#m` cannot collide because no
#   Agda name contains `#`.
_DEPTH = "#m"

def _depth_at(dp):
    if dp == "closed": return RAW("nzero")
    # ★ an ABSOLUTE depth — `ICon (ε ∙)` is at 1 whatever the row's is.
    if isinstance(dp, tuple) and dp[0] == "abs": return RAW("num %d" % dp[1])
    e = V(_DEPTH)
    for _ in range(dp): e = NSUC(e)
    return e

# ⚠⚠ THE TWO `Var` CONSTRUCTORS TAKE THEIR DEPTH AT THE TERM LEVEL.
#   Every other knot constructor carries none — `Var` Fords the DEPTH as
#   well as the tag, which is the exception `Knot/Build` exists for.  So
#   the depth has to be threaded through the value tree as well as
#   through the derivation tree, and by the same field table.
# ⚠⚠ AND THE DEPTH THEY TAKE IS THEIR **SOURCE**, NOT THEIR RESULT.
#   `Var-vzK d : K (sVar , nsuc d)` — the depth ford is what makes a
#   variable exist only at a SUCCESSOR depth.  So the value emitter must
#   hand these the PREDECESSOR of the depth at that position, and a `vz`
#   at a non-successor depth is ill-typed anyway.
# ⚠ `nrsSubK d : SubTy d (nsuc d)` — it RAISES, so where a substitution
#   landing at depth `n` is wanted its own `d` is `pred n`.  Same rule as
#   the `Var` constructors': the depth taken is the SOURCE.
_DEPTH_ARG = {"Var-vzK", "Var-vsK", "nrsSubK"}

# ★★★ …AND THE SUBSTITUTION WRAPPERS TAKE THE AMBIENT DEPTH, NOT ITS
#   PREDECESSOR.  `subTmAtK n σ t : Tm n` with `t : Tm (nsuc n)` — the
#   wrapper is named for where it LANDS, so `n` is the depth at the
#   position, unshifted.  ⚠ `_DEPTH_ARG`'s rule is the opposite one and
#   using it here silently builds a term one binder too shallow.
_DEPTH_PRE = {"singleK", "subTmAtK", "subTyAtK", "extNK"}

# ★★★ HOW MANY DEPTHS EACH WRAPPER TAKES BEFORE ITS SOURCE ARGUMENTS.
#
# ⚠ `extNK` TAKES **TWO**: `extNK d n σ : SubTy (nsuc d) (nsuc n)` with
#   `σ : SubTy d n`.  At an ambient depth `d'` a rule's `extS σ` must land
#   at `SubTy (nsuc d') d'`, so `d = d'` and `n = pred d'`.  The wrapper
#   is named for its SOURCE and its TARGET and a rule writes neither.
# ⚠ `subTmAtK`/`subTyAtK` TAKE TWO as well, and NOT `(d, pred d)` the
#   way `extNK` does: their source is whatever the SUBSTITUTION takes
#   its argument from, which `_argshift` is the one place that knows.
_PRE_N = {"singleK": 1, "subTmAtK": 2, "subTyAtK": 2, "extNK": 2,
          "wkTmK": 1, "wkTyK": 1}

# ★ what a rule NAMES → what the object level CALLS it.  `single`,
#   `subTm` and `subTy` are the three the judgement rules mention, and
#   `Knot/SubApp` supplies all three with the index and target depth
#   that the rule does not write down.
_SUBST_CT = {"single": "singleK", "subTm": "subTmAtK",
             "subTy": "subTyAtK", "extS": "extNK",
             "pwBody": "pwBodyK", "nrs": "nrsSubK",
             # ★ `isingle i : Sub (ε ∙) Γ` — a `lam` ignoring its
             #   variable; `Knot/EWk` builds it in three lines.
             "isingle": "isingleK"}

# ★★★ WRAPPERS THAT TAKE THE ARGUMENT'S **INDEX**, not just its depth.
#
# ⚠ `pwBodyK i t` is an `ielim`, so it wants `⟨i⟩ = (sort , d)` — a PAIR,
#   where `_PRE_N`'s entries take a bare depth.  Same shape `renTm`'s
#   translation to `wkK` already builds by hand.
# name → the argument's sort
_IX_PRE = {"pwBodyK": "sTm"}

# ⚠ `nrsK` IS NOT USED AS A FUNCTION APPLIED TO A TERM — it is a
#   SUBSTITUTION, named where `subTy nrs M` expects one, so the emitter
#   never applies it to an argument.  Its entry exists so the name maps;
#   `_argshift` already knows `nrs` RAISES.

def _pred(dep):
    if dep[0] == "nsuc": return dep[1]
    raise ValueError("a Var at a non-successor depth: %r" % (dep,))

# ★★★ THE DEPTH OF AN ARGUMENT, RELATIVE TO THE RESULT — ONE FUNCTION,
#   THREE READERS (`_val`, `infer_depths`, `jd`).
#
# ⚠⚠ `FIELD_DEPTH` RECORDS A SHIFT PER FUNCTION NAME, and for the
#   substitution wrappers that is WRONG: the shift belongs to the
#   SUBSTITUTION, not to `subTy`/`subTm`.
#
#     subTy (single u) M   `single u : Sub (Γ ∙) Γ`         LOWERS
#                          ⇒ `M` sits one deeper than the result
#     subTy nrs M          `nrs : Sub (Γ ∙) ((Γ ∙) ∙)`      RAISES
#                          ⇒ `M` sits one SHALLOWER
#
#   `⊢natrec` uses BOTH and the single-entry table reported it as
#   `conflicting depths` — a real disagreement the table could not
#   express.  ⇒ dispatch on the substitution's head.
#
# ★ This is the fix for the class that produced four bugs in three days
#   (`FIELD_DEPTH` vs `infer_depths`, `DDEP`, `_IX_PRE`, `wkK`/`Var-vsK`):
#   the shift is READ OFF what the wrapper does, in ONE place, instead of
#   being restated per table and per reader.
SUBST_SHIFT = {"single": ('sucD', 1), "extS": ('sucD', 1),
               "nrs": ('predD',)}

def _headname(e):
    "the head symbol of a parsed spine, or None"
    if e is None: return None
    if e[0] == 'a':  return e[1]
    if e[0] == 'ap': return e[1][0][1] if e[1][0][0] == 'a' else None
    return None

def _argshift(c, i, sub=None):
    """emitted argument `i` of wrapper `c`, as a shift from the result."""
    if c in ("subTmAtK", "subTyAtK") and i == 3:
        return SUBST_SHIFT.get(_headname(sub), ('sucD', 1))
    fds = FIELD_DEPTH.get(c, [])
    return fds[i] if i < len(fds) else ('D',)

def _shift(dep, E):
    if E[0] == "predD": return _pred(dep)
    if E[0] == "lit":  return RAW("num %d" % E[1])
    if E[0] == "sucD":
        e = dep
        for _ in range(E[1]): e = NSUC(e)
        return e
    return dep

# ★ the SORT of each binder, for `renTm`'s translation.  Set per row.
_BSORT = {}
# ★ …and its DECLARED DEPTH, which `_val` needs for exactly one thing:
#   spotting a CLOSED binder used where the knot's field wants the
#   AMBIENT depth, and inserting the object-level `εwkTm` (`Knot/EWk`).
_BDEP = {}

def _iszero(d):
    return d[0] == 'raw' and d[1] in ("nzero", "num 0")

# sort → the `sortMap s ⟶* s` lemma `⊢subAtK` asks for.  ⚠ Only the
#   CONCRETE instances are context-generic; `Knot/SubMot` proves all seven.
SORTMAP_LEM = {"sTy": "sortMap-ty", "sTm": "sortMap-tm",
               "sDesc": "sortMap-desc", "sDCon": "sortMap-dcon",
               "sIDesc": "sortMap-idesc", "sICon": "sortMap-icon",
               "sVar": "sortMap-var"}

def _val(e, CT, dep):
    """a parsed Agda spine → the row description's value language.

    ⚠ `renTm vs X` IS OBJECT-LEVEL WEAKENING, i.e. `wkK`.  It appears in
      `Hom-U`/`Hom-Π`, whose right-hand sides push a term under the Π
      they introduce.  ★ `wkK` and its `⊢wkK` already existed — they are
      what `_∋_∷_`'s `A` component uses — so this is a translation gap,
      not a missing lemma, and the third time that has been the answer.
    ⚠ Its index argument is the SOURCE index, so it takes the PREDECESSOR
      of the depth at that position — the same rule as `Var-vzK`."""
    if e[0] == "a":
        h = e[1]
        # ★ `zero`/`suc` are ℕ CONSTRUCTORS, not `RTm` formers — `_∈D_`'s
        #   index carries a bare `Nat`, so they translate to the object
        #   level's own `nzero`/`nsuc` and NOT to `Tm-nzeroK`/`Tm-nsucK`.
        if h == "zero": return RAW("nzero")
        if h in CT:
            c = CT[h]
            return AP(c, _pred(dep)) if c in _DEPTH_ARG else AP(c)
        # ★★★ A CLOSED BINDER, USED AT THE AMBIENT DEPTH.  `iwf-ρ`'s
        #   premise extends by `IMu D I j` and `icw-imu` concludes at
        #   `⌜IMu⌝ D' I' i`; both are knot constructors whose description
        #   field sits at the AMBIENT depth, while the `Wf` rules bind
        #   `D` CLOSED.  `εwkK` is that `0 → n`, and it is the direction
        #   that decided the convention (`Knot/IxD`'s header).
        if _BDEP.get(h) == "closed" and not _iszero(dep):
            return AP("εwkK", RAW(_BSORT[h]), dep, V(h))
        return V(h)
    args = _infix(e[1], CT)
    h = args[0]
    assert h[0] == "a", h
    if h[1] == "suc" and len(args) == 2:
        return NSUC(_val(args[1], CT, dep))
    # ★ `εwkTm {Θ} c` — `icw-clo`'s SUBJECT.  Its argument is closed, so
    #   the object-level form takes it at 0 and lands at `dep`.
    if h[1] in ("εwkTm", "εwkTy") and len(args) == 2:
        _x = args[1]
        _srt = ("sTy" if h[1] == "εwkTy"
                else _BSORT.get(_x[1] if _x[0] == "a" else None, "sTm"))
        return AP("εwkK", RAW(_srt), dep, _val(_x, CT, RAW("nzero")))
    if h[1] == "renTm" and len(args) == 3:
        x, rho = args[2], args[1]
        srt = _BSORT.get(x[1] if x[0] == "a" else None, "sTm")
        p = _pred(dep)
        # ★★★ `renTm pwShift` — AND IT NEEDS NO NEW OBJECT-LEVEL FUNCTION.
        #
        #   pwShift vz = vs vz · pwShift (vs y) = vs y
        #
        # sends BOTH top variables to `vs vz`, which factors as
        #
        #   renTm pwShift  ≡  renTm vs ∘ subTm (single (var vz))
        #
        # — the substitution identifies the two, the weakening re-opens
        # the slot.  Both halves already exist as `wkK` and `singleK`.
        # ⚠ It is DEPTH-PRESERVING, so the inner substitution lands at
        #   `pred dep` and the weakening puts it back.
        if rho[0] == "a" and rho[1] == "pwShift":
            return AP("wkTyK" if srt == "sTy" else "wkTmK", p,
                      AP("subTmAtK", NSUC(p), p,
                         AP("singleK", p,
                            AP("Tm-varK", AP("Var-vzK", _pred(p)))),
                         _val(x, CT, dep)))
        # ⚠ THE RENAMING ARGUMENT WAS BEING IGNORED.  Every `renTm ρ x`
        #   translated to `wkK` whatever `ρ` was; only the `unmapped`
        #   check kept a non-`vs` renaming from being emitted as a
        #   weakening SILENTLY.  Now it is the branch's condition.
        assert rho[0] == "a" and rho[1] == "vs", ("renTm at %r" % (rho,))
        # ★★★ `wkTmK`/`wkTyK`, NOT `wkK`.  ⚠⚠ THIS LINE SAID `wkK` AND WAS
        #   WRONG.  `Knot/Wk.wkK` is derived by `Lib/IWk` as a generic
        #   depth-bumping fold, and such a fold keeps each row's TAG — so
        #   it maps `var vz` to `var vz`, the IDENTITY on de Bruijn
        #   indices, which is the weakening that appends at the OUTERMOST
        #   end.  `renTm vs` appends at the innermost and shifts.  The two
        #   agree on CLOSED terms and only there, which is why this stood
        #   for as long as every `renTm vs X` had a closed or bare `X`.
        # ★ `Knot/WkSub` is the correct translation: `subTm` already
        #   handles binders, so `renTm vs` is `subTm` at `x ↦ var (vs x)`.
        return AP("wkTyK" if srt == "sTy" else "wkTmK", p, _val(x, CT, p))
    if h[1] in CT:
        c = CT[h[1]]
        # ★ how many arguments this wrapper PREPENDS, so a source
        #   position maps to its emitted one.
        _off = (1 if (c in _DEPTH_ARG or c in _IX_PRE) else _PRE_N.get(c, 0))
        _sg = args[1] if len(args) > 1 else None      # the substitution
        sub = [_val(x, CT, _shift(dep, _argshift(c, i + _off, _sg)))
               for i, x in enumerate(args[1:])]
        if c in _IX_PRE:
            # ⚠ THE **SOURCE** INDEX, NOT THE AMBIENT ONE.  `pwBodyK i t`
            #   takes `t` at `i` and lands at `sh i`, so where a term one
            #   binder deeper is wanted the ARGUMENT still sits at the
            #   predecessor — `hrefl-pw` puts `pwBody C` inside the new
            #   `lam` while `C` itself never moves.  Same rule as
            #   `_DEPTH_ARG` and as `renTm`'s translation to `wkK`.
            _p = _pred(dep)
            return AP(c, PAIR(RAW(_IX_PRE[c]), _p),
                      *[_val(x, CT, _p) for x in args[1:]])
        if c in _DEPTH_ARG: return AP(c, *([_pred(dep)] + sub))
        if c in ("subTmAtK", "subTyAtK"):
            # ★ SOURCE then TARGET.  The source is where the term being
            #   substituted lives — `_argshift`'s answer for that very
            #   argument, so the two cannot disagree.
            return AP(c, _shift(dep, _argshift(c, 3, _sg)), dep, *sub)
        if _PRE_N.get(c) == 1: return AP(c, *([dep] + sub))
        if _PRE_N.get(c) == 2: return AP(c, *([dep, _pred(dep)] + sub))
        return AP(c, *sub)
    return V(h[1])

def gen_redrows():
    CT = {d.split(":")[0].strip(): n[1:] + "K" for n, d, _ in KNOT}
    CT.update(_SUBST_CT)
    TEL = [TNAT(), TKNOT("sTm"), TKNOT("sTm")]
    rows, skipped = [], []
    for r in rules_of(os.path.join(os.path.dirname(os.path.dirname(
                        os.path.abspath(__file__))), "Spec", "Typing.agda"), "_⟶_"):
        t = translate_rule(r, CT)
        if t[1] is None: skipped.append((t[0], t[2])); continue
        nm, binders, prems, lhs, rhs, foreign, bools = t
        bs = [(_DEPTH, _code(TNAT(), None))]
        dep = {}
        for b, srt, dp in binders:
            dep[b] = dp
            bs.append((b, _code(TNAT(), None) if srt == "nat"
                          else _code(TKNOT(srt), _depth_at(dp))))
        # ★★★ A BOOLEAN premise is a κ BINDER carrying a FORD.
        #
        #   `pw? C ≡ true`  ↦  `⌜Id⌝ ⌜Nat⌝ (pwK (sTm , d) C) (num 1)`
        #
        # ⚠ THE FUNCTION NEEDS THE ARGUMENT'S **INDEX**, which the rule
        #   does not write: `pwK` is an `ielim` and so takes `⟨i⟩` before
        #   the term.  The binder's sort and depth supply it — the same
        #   two facts `_binder_comp` recovers everywhere else.
        for i, (fn, arg, val) in enumerate(bools):
            fnK, _dfn, _srt = BOOL_PREM[fn]
            _a = arg.strip()
            _d = _depth_at(dep.get(_a, 0))
            bs.append(("bp%d" % i,
                       AP("⌜Id⌝", RAW("⌜Nat⌝"),
                          AP(fnK, PAIR(RAW(_srt), _d),
                             _val(_parse_spine(_tokens(_a)), CT, _d)),
                          RAW("num %d" % val))))
        # ★ a FOREIGN premise is a κ BINDER, not an `iρ` field.
        for i, (a, b, fcomp) in enumerate(foreign):
            fdep = TUP(V(_DEPTH),
                       _val(_parse_spine(_tokens(a)), CT, V(_DEPTH)),
                       _val(_parse_spine(_tokens(b)), CT, V(_DEPTH)))
            bs.append(("fp%d" % i, _code(fcomp, fdep)))
        ps = []
        for i, (a, b) in enumerate(prems):
            d = dep.get(a.strip(), 0)
            ps.append((f"ih{i}", TUP(_depth_at(d),
                                     _val(_parse_spine(_tokens(a)), CT, _depth_at(d)),
                                     _val(_parse_spine(_tokens(b)), CT, _depth_at(d)))))
        rows.append((nm, JRow("rd" + nm, bs, ps,
                              [V(_DEPTH),
                               _val(_parse_spine(_tokens(lhs)), CT, V(_DEPTH)),
                               _val(_parse_spine(_tokens(rhs)), CT, V(_DEPTH))])))
    _ROWS[:] = [(nm, row, _tagof(i)) for i, (nm, row) in enumerate(rows)]
    _SKIP[:] = skipped
    L = [REDROWS_HDR]
    L.append("-- ⚠ NOT EMITTED — %d of %d rules, in two classes:" % (len(skipped), len(skipped) + len(rows)))
    for n, w in skipped: L.append("--     %-12s %s" % (n, w))
    L.append("")
    for i, (nm, row) in enumerate(rows):
        # ⚠ AGDA REJECTS A DIGIT AFTER `_` IN A NAME (`y0_0` — "the part
        #   0 is not valid because it is a literal"), so the per-row
        #   prefix is letters only.
        tag = _tagof(i)
        pre = (tag, "k" + tag)
        L.append("-- %s" % nm)
        L.append(emit_jrow(row, TEL, pre, "IRed", "RedD"))
        L.append("")
    L.append("-" * 72)
    L.append("-- ★★★ …AND THE JUDGEMENT ITSELF.")
    L.append("-" * 72)
    L.append("RedD : IDesc")
    L.append("RedD =")
    # ⚠ `_◂_` is INFIX; the prefix form does not parse in a chain.
    line, body = "  ", []
    for nm, _ in rows:
        if len(line) > 62: body.append(line); line = "  "
        line += "rd%s ◂ " % nm
    body.append(line + "inil")
    L.append("\n".join(body))
    return "\n".join(L) + "\n"


REDWF_HDR = """--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `_⟶_` IS A WELL-FORMED DESCRIPTION.
--
-- ⚠ SPLIT FROM `Knot/RedRows` DELIBERATELY.  `Knot/Wf`'s 53 `IConWf`s
--   already cost 104s and need the compacting collector; these are 65
--   rows over a THREE-component index with a transport per component.
--   The rows and their well-formedness are independent artifacts, so
--   there is no reason to make one module carry both.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RedWf%s where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; var; vz; vs; pair; fst; snd; nsuc; nzero
        ; El; IMu; Σ'; Nat
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub; ICon; IDesc; iι; iρ; iκ; inil; _◂_; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_
        ; IConWf; iwf-ι; iwf-κ; iwf-ρ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; idwf-nil; idwf-cons
        ; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nsuc; ⊢num; ⊢nzero
        ; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ⊢pair; ty-Σ; ty-Nat; ty-IMu
        ; ξ-pairˡ; ξ-pairʳ; ξ-nsuc; βfst; βsnd )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; toI; fromI; ⊢ixP; ⊢sTy; ⊢sTm; ⊢sDesc; ⊢sDCon; ⊢sIDesc; ⊢sICon; ⊢sVar
        ; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.CtorsV
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Single using ( singleK; ⊢singleK )
open import DirectedHoTT.Examples.Knot.SubApp
  using ( subTmAtK; subTyAtK; ⊢subTmAtK; ⊢subTyAtK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK; ⊢extNK )
open import DirectedHoTT.Examples.Knot.Pw using ( pwK; ⊢pwK )
open import DirectedHoTT.Examples.Knot.Stk
  using ( stkAK; ⊢stkAK; stkCK; ⊢stkCK; flatK; ⊢flatK )
open import DirectedHoTT.Examples.Knot.Nrs using ( nrsSubK; ⊢nrsSubK )
open import DirectedHoTT.Examples.Knot.PwBody using ( pwBodyK; ⊢pwBodyK )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK; ⊢wkTmK; wkTyK; ⊢wkTyK )
open import DirectedHoTT.Examples.Knot.RedRows
%s
"""

def gen_redwf(part, lo, hi):
    """one HALF of the well-formedness.

    ⚠⚠ SPLIT BECAUSE OF A MEASURED CLIFF, NOT A GUESS.  Bisected on this
      box (5.5 GB cgroup cap): 8 rows 10s · 16 rows 25s · 32 rows 50s ·
      48 rows 87s — LINEAR at ~1.8s/row — and then 56/64/65 OOM.
      ★ But 52 OOMed while 54 PASSED, at the same runtime, so the cliff
      is not a bad row: the module simply sits near the cap and whether
      it trips is noise.  `exit-143-is-not-evidence-about-cost` again.
      ⇒ two halves of ~33 sit well inside the linear region."""
    TEL = [TNAT(), TKNOT("sTm"), TKNOT("sTm")]
    L = [REDWF_HDR % (part, "open import DirectedHoTT.Examples.Knot.RedWfA"
                      if part == "B" else "")]
    for nm, row, tag in _ROWS[lo:hi]:
        L.append("-- %s" % nm)
        L.append(emit_jrowwf(row, TEL, (tag, "k" + tag), "IRed",
                             "rd%sWf" % nm, "RedD"))
        L.append("")
    if part != "B":
        return "\n".join(L) + "\n"
    L.append("-" * 72)
    L.append("-- ★★★ …AND `_⟶_` IS A WELL-FORMED DESCRIPTION.")
    L.append("-" * 72)
    L.append("RedWf : IDescWf IRed RedD")
    L.append("RedWf =")
    # ⚠ A ROW WITH NO RECURSIVE PREMISE IS `D`-PARAMETRIC and must be
    #   APPLIED here; one with a premise is already at `RedD`.  The two
    #   shapes are not interchangeable — see `emit_jrowwf`.
    L.append(nest(["idwf-cons (rd%sWf RedD)" % nm if not row.prems
                   else "idwf-cons rd%sWf" % nm
                   for nm, row, _ in _ROWS], "idwf-nil", 2))
    return "\n".join(L) + "\n"


def gen_lookupgen():
    TEL = [TNAT(), TCTX(), TKNOT("sVar"), TKNOT("sTy")]
    here = JRow("lkHereG",
      [("m", _code(TNAT(), None)),
       ("G", _code(TCTX(), V("m"))),
       ("A", _code(TKNOT("sTy"), V("m")))],
      [],
      [NSUC(V("m")),
       AP("Ctx-extK", V("m"), V("G"), V("A")),
       AP("Var-vzK", V("m")),
       # ⚠⚠ `wkTyK`, NOT `wkK`.  `_∋_∷_`'s type component is `renTy vs A`
       #   with `A` a bound FIELD — an arbitrary type, hence OPEN — and
       #   `Knot/Wk.wkK` is the identity on de Bruijn indices, not
       #   `renTy vs`.  See `PLAN-RENAMING.md` §0.
       AP("wkTyK", V("m"), V("A"))])
    there = JRow("lkThereG",
      [("m", _code(TNAT(), None)),
       ("G", _code(TCTX(), V("m"))),
       ("x", _code(TKNOT("sVar"), V("m"))),
       ("A", _code(TKNOT("sTy"), V("m"))),
       ("B", _code(TKNOT("sTy"), V("m")))],
      [("ih", TUP(V("m"), V("G"), V("x"), V("A")))],
      [NSUC(V("m")),
       AP("Ctx-extK", V("m"), V("G"), V("B")),
       AP("Var-vsK", V("m"), V("x")),
       # ⚠⚠ `wkTyK`, NOT `wkK`.  `_∋_∷_`'s type component is `renTy vs A`
       #   with `A` a bound FIELD — an arbitrary type, hence OPEN — and
       #   `Knot/Wk.wkK` is the identity on de Bruijn indices, not
       #   `renTy vs`.  See `PLAN-RENAMING.md` §0.
       AP("wkTyK", V("m"), V("A"))])
    L = [LOOKUPGEN_HDR,
         emit_jrow(here, TEL, ("Θ", "κ"), "ILk", "LkD"), "",
         "-" * 72,
         "-- ★★★ AND ITS WELL-FORMEDNESS, FROM THE SAME DESCRIPTION.",
         "--",
         "-- ⚠ THE CONTROL HERE IS THAT IT TYPECHECKS, not that it equals",
         "--   `Knot/Lookup`'s hand-written chain.  Any inhabitant of",
         "--   `IConWf D I Θ C` is as good as any other, and this one is",
         "--   deliberately different (`toI (fromI d)` where the hand-written",
         "--   proof writes `d`).  Proof-term equality would be a STRONGER",
         "--   demand than correctness.",
         "-" * 72, "",
         emit_jrowwf(here, TEL, ("Θ", "κ"), "ILk", "lkHereWfG"), "",
         emit_jrow(there, TEL, ("Ξ", "λ"), "ILk", "LkD"), "",
         emit_jrowwf(there, TEL, ("Ξ", "λ"), "ILk", "lkThereWfG", "LkD"), "",
         "------------------------------------------------------------------------",
         "-- ★★★ THE CONTROL: generated ≡ hand-written, both rows.",
         "------------------------------------------------------------------------",
         "", "_ : lkHereG ≡ lkHere", "_ = refl", "",
         "_ : lkThereG ≡ lkThere", "_ = refl"]
    return "\n".join(L) + "\n"

TEL_RED = [TNAT(), TKNOT("sTm"), TKNOT("sTm")]
TEL_TYR = [TNAT(), TKNOT("sTy"), TKNOT("sTy")]

# ★ registered so `_binder_comp` recognises a foreign judgement's code
FOREIGN["RedD"] = TJ("RedD", "IRed", "RedWf", TEL_RED)

J_TYRED = Judgement(
    "_⟶ᵀ_", "⟶ᵀ", TEL_TYR, "ITyRed",
    "Σ' Nat (Σ' (IMu KnotD IPair (pair sTy (var vz)))\n"
    "                  (IMu KnotD IPair (pair sTy (var (vs vz)))))",
    "TyRedD", "TyRed", "TyRedWf",
    cites=[("⟶", FOREIGN["RedD"])],
    extra=("open import DirectedHoTT.Examples.Knot.RedRows using ( RedD; IRed )\n"
           "open import DirectedHoTT.Examples.Knot.RedWfB using ( RedWf )"))


FOREIGN["TyRedD"] = TJ("TyRedD", "ITyRed", "TyRedWf", TEL_TYR)

J_CONV = Judgement(
    "_≅ᵀ_", "≅ᵀ", TEL_TYR, "IConv",
    "Σ' Nat (Σ' (IMu KnotD IPair (pair sTy (var vz)))\n"
    "                  (IMu KnotD IPair (pair sTy (var (vs vz)))))",
    "ConvD", "Conv", "ConvWf",
    cites=[("⟶ᵀ", FOREIGN["TyRedD"])],
    extra=("open import DirectedHoTT.Examples.Knot.TyRedRows using ( TyRedD; ITyRed )\n"
           "open import DirectedHoTT.Examples.Knot.TyRedWf using ( TyRedWf )"))


ADQ_HDR = """--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE VALUE TRANSLATION IS **ADEQUATE**.
--
-- ⚠⚠ WHY: `dwf-cons` shipped `DescWf C` for `DescWf (C ◃ E)` and it
--   TYPECHECKED.  `_val` returned the left operand of an infix
--   application as a bare binder and the `◃` vanished.  Nothing could
--   see it, because nothing related the emitted term to the RULE.
--
-- ★ EACH LINE BELOW RELATES THEM, BY `refl`.  `Knot/Map`'s `en…` maps are
--   the adequacy map from REAL syntax to encoded terms, produced by a
--   DIFFERENT emitter than `_val`.  So the translation is right exactly
--   when, for a rule subject `e` with meta-level binders `b`,
--
--       _val(e)[ b := en b ]   ≡   en (e)
--
--   holds definitionally.  Drop a constructor on either side and the two
--   stop agreeing.
--
-- ⚠ THIS IS TIER 3 OF `JUDGEMENT-ATTEMPTS` §13.4, FOR THE VALUES ONLY.
--   It does NOT check that a row's FIELD STRUCTURE or FORDS are right —
--   only that each subject it builds is the one the rule names.  A full
--   `enDeriv` would subsume it.
--
-- ★ %(ok)d checks.  ⚠ %(skip)d subject(s) SKIPPED and named — a
--   translation mentioning the row's DEPTH has no meta-level depth to be
--   instantiated at, and an `ICon` binder's scope is not named by its
--   rule:
%(named)s
--
-- ★★★ AND A SKIP THAT SAYS `applies X` OWES SOMETHING.  For a WRAPPER,
--   `enTy (subTy σ B) ≡ subTyAtK … (enTy B)` is a COMMUTATION LEMMA and
--   not `refl`, so refusing it here is correct — but the obligation it
--   creates was never anything's job.  `Knot/SzAgree` is one such lemma,
--   written for `sz` and for nothing else.
--
-- ⚠⚠ THAT IS EXACTLY WHERE `wkK` HID.  It is not `renTm vs` — it keeps
--   the de Bruijn index where `renTm vs` shifts it — and every rule
--   applying it was reported as `_Undepthed`, which reads like depth
--   bookkeeping.  The coverage gap and the bug had the SAME CAUSE: a
--   depth argument.  ⇒ the ledger below, checked BOTH WAYS at generation
--   time, so a new wrapper cannot arrive without an entry.
--
-- ⚠⚠ AND IT COVERS THE HAND-WRITTEN ELIMINATORS TOO, which the
--   emitted-row scan cannot see: `payTyK`, `ihTyK`, `ipayTyK`,
--   `lookupDK`, `subTmK`, … are DEFINED in `Examples/Knot` and mostly
--   used by no emitted row yet.  ★ `sz` is the ONLY one discharged, and
--   the reason is worth stating: a wrapper gets an agreement exactly
--   when some caller needs it to COMPUTE.  Canonicity needs `sz`'s
--   NUMBER; the judgement rows need only a term of the right INDEX.
--   That is why the arithmetic library (`plus-num : plusTm (num a)
--   (num b) ⟶* num (a + b)`) has its agreements and the syntax layer
--   does not.
%(ledger)s
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Adequacy where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Examples.Knot.Ctors
open import DirectedHoTT.Examples.Knot.Map
  using ( enTy; enTm; enDesc; enDCon; enIDesc; enICon; enVar )

"""

TEL_NNC = [TNAT(), TKNOT("sTm")]

# ★★★ `NoNatC` — THE FIRST **UNARY** JUDGEMENT, and the first parsed out
#   of a file other than `Spec/Typing`.
#
# ⚠ IT IS NOT A BOOLEAN PREMISE, which is what `pw?`/`stkA?`/`flat?` are.
#   `NoNatC` is an inductive PREDICATE with seven rows, two of them
#   recursive (`nnc-Π` descends UNDER A BINDER, `nnc-Hom` does not) — so
#   it is a description like `_⟶ᵀ_`, cited by `⊢tr` the way `⊢conv`
#   cites `_≅ᵀ_`.  Encoding it as a boolean would have meant proving the
#   boolean AGREES with the predicate, which is a second obligation the
#   rule never asked for.
#
# ★ ITS INDEX IS TWO COMPONENTS, not three: a depth and the CODE.
# ★★★ THE MEMBERSHIP JUDGEMENTS — `⊢con`'s and `⊢icon`'s last blockers.
#
# ⚠ They live in `Spec/Syntax`, NOT in the mutual block: `_∈D_` mentions
#   only `Desc`, so nothing in it cites the typing judgements and it needs
#   no merge.  Same standing as `ConvD`/`NoNatCD`.
# ★ TWO rows each, and the `k` slot is a BARE `Nat` — the rules say
#   `zero`/`suc k`, ℕ constructors, which the object level spells
#   `nzero`/`nsuc`.
J_IND = Judgement(
    "_∈D_", "∈D", [TNAT(), TNAT(), TKNOT("sDesc")], "IInD",
    "Σ' Nat (Σ' Nat (IMu KnotD IPair (pair sDesc (var (vs vz)))))",
    "InDD", "InD", "InDWf", src="Syntax")

J_IIND = Judgement(
    "_∈ID_", "∈ID", [TNAT(), TNAT(), TKNOT("sIDesc")], "IInID",
    "Σ' Nat (Σ' Nat (IMu KnotD IPair (pair sIDesc (var (vs vz)))))",
    "InIDD", "InID", "InIDWf", src="Syntax")

J_NONATC = Judgement(
    "NoNatC", "NoNatC", TEL_NNC, "INoNatC",
    "Σ' Nat (IMu KnotD IPair (pair sTm (var vz)))",
    "NoNatCD", "NoNatC", "NoNatCWf",
    arity=1, src="Variance")


# ============================ ADEQUACY OF THE VALUE MAP ====================
# ★★★ CATEGORY D, CLOSED FOR THE VALUE TRANSLATION.
#
# ⚠⚠ `dwf-cons` SHIPPED `DescWf C` FOR `DescWf (C ◃ E)` AND IT TYPECHECKED.
#   `_val` returned the left operand of an infix application as a bare
#   binder and the `◃` vanished.  Nothing could see it, because nothing
#   related the emitted term to the RULE it came from.
#
# ★ THIS RELATES THEM, BY `refl`.  `Knot/Map`'s `enTy`/`enTm`/`enDesc`/… are
#   the adequacy map from REAL syntax to encoded terms, written from the
#   KNOT table by a DIFFERENT emitter than `_val`.  So for a rule subject
#   `e` with binders `b : T`, the value translation is right exactly when
#
#       _val(e)[ b |-> enT b ]   ==   enSort(e)
#
#   is `refl` — the left side is what the GENERATOR chose, the right what
#   `Map.agda` says the answer is.  Drop a constructor and they differ.
#
# ⚠ SKIPPED, AND NAMED: any subject whose translation mentions the row's
#   DEPTH (the `Var`/`wk`/substitution wrappers) — there is no meta-level
#   depth to instantiate it at — and any binder whose meta-level type the
#   rule does not pin (`ICon`, whose scope is not named).  Those keep only
#   the weaker guarantees of tiers 1-2.
_EN = {"sTy": "enTy", "sTm": "enTm", "sDesc": "enDesc", "sDCon": "enDCon",
       "sIDesc": "enIDesc", "sICon": "enICon", "sVar": "enVar"}

_KNOTK = set()          # filled from `KNOT` in the main block

class _Undepthed(Exception): pass


# ★★★ A SKIP THAT OWES SOMETHING, SEPARATED FROM ONE THAT DOES NOT.
#
# ⚠⚠ `wkK` WAS NOT `renTm vs` AND THIS IS WHERE IT HID.  Both reasons a
#   subject can be skipped used to raise `_Undepthed`, so `⊢ap` — a row
#   that APPLIES `wkK` — was reported as a depth-bookkeeping detail.  It
#   is not: it means the wrapper is UNCHECKED, and the obligation is a
#   commutation lemma (`Knot/SzAgree`'s shape) that nobody had written.
#
# ⇒ the two are now different exceptions, and a wrapper skip must name a
#   LEDGER ENTRY.  Adding a wrapper without one fails GENERATION.
class _Wrapper(Exception):
    def __init__(self, head): self.head = head


def _wrap_heads(v, acc):
    """every non-constructor head in an EMITTED value — i.e. every wrapper
    the translation produced.

    ⚠⚠ IT WALKS THE EMITTED TERM, NOT THE CHECKABLE ONES.  Scanning only
      subjects that survive `_radq` misses the wrappers that made the
      subject uncheckable — which is every one of them, and is how `wkK`
      stayed off the ledger on the first attempt."""
    if not isinstance(v, tuple): return acc
    t = v[0]
    if t == 'ap':
        if v[1] not in _KNOTK or v[1] in _DEPTH_ARG: acc.add(v[1])
        for a in v[2]: _wrap_heads(a, acc)
    elif t == 'nsuc': _wrap_heads(v[1], acc)
    elif t == 'pair': _wrap_heads(v[1], acc); _wrap_heads(v[2], acc)
    return acc


# ★ THE LEDGER.  For each wrapper that appears in a translated subject:
#   what discharges the adequacy obligation, or why it is not owed.
#
#   `enTy (subTy σ B) ≡ subTyAtK … (enTy B)` is a COMMUTATION LEMMA, not
#   `refl` — `gen_adequacy` is right to refuse it.  What it cannot do is
#   notice that the lemma was never written.  This table is that notice.
_WRAP_LEDGER = {
    # ★★★ DISCHARGED 2026-09-05 — the renaming layer.
    "extRNK":   "✅ DISCHARGED — `Knot/SubAgree.extR-Represents`:\n--                `RepresentsR ρ r → RepresentsR (extR ρ) (extRNK d ⌈Δ⌉ r)`.\n--                ⚠ POLYMORPHIC in `d`, and that is load-bearing three\n--                layers up — see `Knot/RenAgree`'s binder rows.",
    "extRK":    "✅ DISCHARGED via `extRNK` — `extRK` is its eliminator, and\n--                `Knot/RenSpec.extRK-vz`/`-vs` are the two clauses.",
    "renTmK":   "◐ IN PROGRESS — `Knot/RenAgree` proves it for the 25 SAME-SORT\n--                `RTm` rows.  The five cross-sort rows (`var`, `elim`,\n--                `ielim`, `cMu`, `cIMu`) need agreement at another sort,\n--                i.e. a mutual statement; `Knot/SzAgree` never did,\n--                because a fold steps a cross-sort child PAST.",
    "renTmAtK": "◐ IN PROGRESS — the applied form of `renTmK`; same status.",
    # ⚠ THE SCANNER OVER-APPROXIMATES, AND THAT IS THE SAFE DIRECTION.  It
    #   flags any top-level definition whose body mentions `ielim KnotD`,
    #   which catches REDUCTION LEMMAS as well as programs.  A lemma about
    #   an eliminator owes no adequacy lemma of its own — it IS one, or a
    #   step of one.  Listed rather than special-cased in the scanner, so
    #   that a genuinely new PROGRAM cannot hide behind a loosened rule.
    "ren-head-red": "✅ not a program — the per-row head reduction INSIDE\n--                `Knot/RenRed`, i.e. a step of `renTmK`'s own adequacy.",
    "extRK-vz":  "✅ not a program — a clause of `extRK`'s adequacy.",
    "extRK-vs":  "✅ not a program — the other clause.",
    "extRK-sub": "✅ not a program — `extRK`'s substitution naturality\n--                (`Knot/RenNat`), the hypothesis `isubMethod-red` takes.",
    "singleSK-vz": "✅ not a program — a clause of `singleK`'s adequacy.",
    "singleSK-vs": "✅ not a program — the other clause.",
    "nrsSK-vz":  "✅ not a program — a clause of `nrsSubK`'s adequacy.",
    "nrsSK-vs":  "✅ not a program — the other clause.",
    "extRNK-vz": "✅ not a program — a clause of `extRNK`'s adequacy\n--                (`Knot/RenSpec`), which `extR-Represents` assembles.",
    "extRNK-vs": "✅ not a program — the other clause.",
    "pwDefault": "⬜ OWED — the default method of `Knot/PwBody`'s tuple.  It\n--                REBUILDS `icon k p` and renames, so its adequacy is a\n--                corollary of `renTmK`'s; blocked on the same five\n--                cross-sort rows.",
    # ⬜ OWED — a commutation lemma, `Knot/SzAgree`'s shape.
    "wkK":      "⬜ OWED, AND FALSE AS STATED — `wkK` is NOT `renTm vs`; it keeps\n--                the de Bruijn index.  `Knot/WkSub.wkTmK`/`wkTyK` are the\n--                correct translation and the emitter must move to them.",
    "wkTmK":    "⬜ OWED — `renTm vs`, done PROPERLY (`Knot/WkSub`): `subTm` at\n--                the substitution `x ↦ var (vs x)`.  Replaces `wkK` here.",
    "wkTyK":    "⬜ OWED — `renTy vs`, likewise.  ⚠ DEFINED but not yet\n--                EMITTED: no rule so far weakens a TYPE.",
    "subTmAtK": "⬜ OWED — `enTm (subTm σ t) ≡ subTmAtK … (enTm t)`.",
    "subTyAtK": "⬜ OWED — `enTy (subTy σ A) ≡ subTyAtK … (enTy A)`.",
    "singleK":  "⬜ OWED — `single`'s half of the substitution agreement.",
    "extNK":    "⬜ OWED — `extS`'s half.",
    "nrsSubK":  "⬜ OWED — `nrs`'s half.",
    # ⬜ boolean/predicate functions over syntax: the SAME obligation `sz`
    #   discharges, and `Knot/SzAgree` is the only one discharged.
    "flatK":    "⬜ OWED — agreement with `flat?`.",
    "pwK":      "⬜ OWED — agreement with `pw?`.",
    "pwBodyK":  "⬜ OWED — agreement with `pw?`'s body case.",
    "stkAK":    "⬜ OWED — agreement with `stkA?`.",
    "stkCK":    "⬜ OWED — agreement with `stkC?`.",
    # ✅ NOT OWED, and each for a stated reason.
    "εwkK":     "✅ not owed — its argument is CLOSED, and every weakening\n--                agrees on a closed term.  This is exactly why `Knot/PayTy`\n--                may use `wkK` and `Knot/IhTyRho` may not.",
    "Ctx-empK": "✅ not owed — a CONSTRUCTOR of `CtxD`, not a wrapper.",
    "Ctx-extK": "✅ not owed — a constructor of `CtxD`.",
    "IxNoneK":  "✅ not owed — a constructor of `IxD`.",
    "IxDConK":  "✅ not owed — a constructor of `IxD`.",
    "IxDescK":  "✅ not owed — a constructor of `IxD`.",
    "IxIConK":  "✅ not owed — a constructor of `IxD`.",
    "IxIDescK": "✅ not owed — a constructor of `IxD`.",

    # ── DEFINED object-level programs (`scan_object_programs`) ──────────
    # ★ `sz` IS THE ONLY ONE DISCHARGED, and it is discharged twice.
    "szsTm":     "✅ `Knot/SzAgree` — `szsTm i ⌈t⌉ ⟶* num (sz t)`, all 30 rows,\n--                GENERATED.  THE model for every ⬜ below.",
    "szTm":      "✅ `Knot/SzProbe` — same-sort counts, per row, by `refl`.",
    "head-red":  "✅ not owed — a lemma INSIDE `Knot/SzAgree`, not a program.",
    # ✅ METHOD ROWS of a program above: covered by that program's own
    #   agreement, not owed one each.
    "ihTyRho":   "✅ not owed — a method row of `ihTyK`.",
    "ipayTyRho": "✅ not owed — a method row of `ipayTyK`.",
    "ipayTyKap": "✅ not owed — a method row of `ipayTyK`.",
    "atConK":    "⬜ OWED — agreement with `atCon`.",
    "wkTyUnderK":"⬜ OWED — agreement with `renTy (extR vs)`.",
    # ⬜ the eliminators the wrappers above are built from.
    "subTmK":    "⬜ OWED — `subTmK`'s agreement with `subTm`; `subTmAtK`'s core.",
    "extSK":     "⬜ OWED — with `subTmK`.",
    "singleSK":  "⬜ OWED — `singleK`'s core.",
    "nrsK":      "⬜ OWED — `nrsSubK`'s core.",
    "conSSK":    "⬜ OWED — `conSK`/`atConK`'s core.",
    # ⬜ functions over syntax with NO emitted-row customer yet — which is
    #   exactly why none has an agreement: nothing has needed them to
    #   COMPUTE, only to TYPE.
    "lookupDK":  "⬜ OWED — agreement with `lookupD`.",
    "ilookupDK": "⬜ OWED — agreement with `ilookupD`.",
    "payTyK":    "⬜ OWED — agreement with `payTy`.",
    "ihTyK":     "⬜ OWED — agreement with `ihTy`.",
    "ipayTyK":   "⬜ OWED — agreement with `ipayTy`.",
}


def scan_object_programs(out):
    """every DEFINED object-level program over the knot: a top-level
    definition whose body applies `ielim KnotD`.

    ⚠⚠ THE EMITTED-ROW SCAN CANNOT SEE THESE.  It finds the wrappers a
      generated row APPLIES; these are the functions the hand-written
      modules DEFINE, and most are not used by any emitted row yet.
      `payTy`/`ihTy`/`ipayTy`/`atCon` were all written without one, and
      each owes exactly the lemma `wkK` fails."""
    import os, re, io
    progs = {}
    for f in sorted(os.listdir(out)):
        if not f.endswith(".agda"): continue
        t = io.open(os.path.join(out, f), encoding="utf-8").read()
        t = re.sub(r"(?m)^--.*$", "", t)
        for m in re.finditer(r"(?m)^([A-Za-zε][A-Za-z0-9\u1d40\u1d57'\-]*)\s+[^=\n]*=\s*(.*)$", t):
            nm, start = m.group(1), m.end()
            nxt = re.search(r"(?m)^\S", t[start:])
            body = m.group(2) + "\n" + t[start:start + (nxt.start() if nxt else 0)]
            # ⚠ NOT JUST `ielim KnotD`.  `Knot/WkSub`'s programs and
            #   `atConK` are built from `subTyAtK`, not from a bare
            #   eliminator, and a scan keyed on `ielim` alone misses
            #   exactly the module written to FIX this bug class.
            # ⚠⚠ AND `renTmAtK`/`renTmK`/`extRK` TOO — 2026-09-05.  The
            #   pattern above knew only `sub…AtK`, from before step 1c moved
            #   `Knot/WkSub` onto `renTmAtK`; after that move `wkTyK`,
            #   `wkTyUnderK`, `extRNK` and `renTmAtK` were DEFINED and NOT
            #   SCANNED, so the ledger's stale-name check fired on them
            #   instead.  ★ That check is the only reason the gap was
            #   visible at all — a one-directional ledger would have gone on
            #   silently exempting them.
            if re.search(r"\bielim KnotD\b|\b(sub|ren)(Ty|Tm)?AtK\b"
                         r"|\brenTmK\b|\bextRK\b", body):
                progs.setdefault(nm, set()).add(f)
    return progs


def scan_emitted_wrappers(out):
    """every non-constructor `…K` head the emitter actually produced.

    ⚠⚠ IT SCANS THE EMITTED FILES, NOT THE ADEQUACY SUBJECTS, AND THAT IS
      THE WHOLE POINT.  `Knot/Adequacy` checks a rule's CONCLUSION
      SUBJECTS; `wkK`'s three uses are all in PREMISES and INDEX
      components, which no tier looks at.  A ledger fed by the adequacy
      pass would have listed five wrappers and not the one that was
      wrong."""
    import os, re, io
    heads = {}
    for f in sorted(os.listdir(out)):
        if not (f.endswith("Rows.agda") or f.startswith("JudgeWf")
                or f.startswith("RedWf") or f.endswith("Wf.agda")):
            continue
        t = io.open(os.path.join(out, f), encoding="utf-8").read()
        # ⚠ AFTER THE IMPORTS.  Module names (`JudgeWfK`) end in `K` too.
        k = t.find("\nmodule ")
        body = t[t.index("\n\n", k):] if k >= 0 and "\n\n" in t[k:] else t
        body = re.sub(r"(?m)^open import .*$", "", body)
        for m in re.finditer(
                r"(?<![A-Za-z0-9\-])([A-Za-zε][A-Za-z0-9\-]*K)(?![A-Za-z0-9])", body):
            heads.setdefault(m.group(1), set()).add(f)
    return {h: v for h, v in heads.items() if h not in _KNOTK}
def _radq(e, benv):
    "render an emitted value with binders replaced by their `en` images"
    t = e[0]
    if t == 'v':
        if e[1] not in benv: raise _Undepthed()
        return "(%s {Γ' = Δ} %s)" % (benv[e[1]], e[1])
    if t == 'raw':  return e[1]
    if t == 'nsuc': return "(nsuc %s)" % _radq(e[1], benv)
    if t == 'pair': return "(pair %s %s)" % (_radq(e[1], benv), _radq(e[2], benv))
    if t == 'ap':
        # ⚠⚠ ONLY A KNOT CONSTRUCTOR IS DEFINITIONALLY WHAT `en…` SAYS.
        #   A WRAPPER (`subTyAtK`, `wkK`, `singleK`, `εwkK`, …) is not:
        #   `enTy (subTy σ B)` is the encoding of the SUBSTITUTED type,
        #   and relating it to `subTyAtK … (enTy B)` is a COMMUTATION
        #   LEMMA, not `refl`.  Asserting it here would be a false claim
        #   that happens to be about the right subject.
        # ⚠ AND A CONSTRUCTOR THAT TAKES A DEPTH IS OUT TOO.  `enVar`
        #   writes `Var-vzK (num (len Γ))` — a META-level length — where
        #   `_val` writes the row's schematic depth.  They agree only
        #   under an instantiation this check does not make.
        # ⚠ A WRAPPER AND A DEPTH-TAKING CONSTRUCTOR ARE DIFFERENT SKIPS.
        #   The first OWES a commutation lemma; the second does not.
        if e[1] not in _KNOTK: raise _Wrapper(e[1])
        if e[1] in _DEPTH_ARG: raise _Wrapper(e[1])
        return "(%s%s)" % (e[1], "".join(" " + _radq(a, benv) for a in e[2]))
    raise _Undepthed()

def _mety(srt, dp):
    "the META-level Agda type of a binder at this sort and depth"
    if srt == "sDesc":  return "Desc"
    if srt == "sDCon":  return "DCon"
    if srt == "sIDesc": return "IDesc"
    if srt in ("sTy", "sTm"):
        h = "RTy" if srt == "sTy" else "RTm"
        if dp == "closed": return h + " ε"
        if isinstance(dp, int) and dp >= 0:
            return h + " " + ("Γ" if dp == 0 else "(Γ" + " ∙" * dp + ")")
    raise _Undepthed()

def gen_adequacy(rows, CT):
    """one `refl` per translated subject, against `Knot/Map`."""
    L, ok, skipped, wraps = [], 0, [], set()
    # ★★★ THE WRAPPER SCAN IS ITS OWN PASS, AND THAT IS THE WHOLE POINT.
    #
    # ⚠⚠ FOLDING IT INTO THE CHECK LOOP FINDS NOTHING.  That loop builds a
    #   rule's TELESCOPE first and abandons the rule if any binder's
    #   meta-level type is unpinned — so for `⊢ap` it never reaches the
    #   subject that applies `wkK`.  A scan that runs only where the check
    #   succeeds cannot see what the check is missing; it has to walk
    #   EVERY emitted subject, checkable or not.
    for nm, sorts, deps, subs in rows:
        for expr, srt in subs:
            try:
                e = _parse_spine(_tokens(expr))
                if e[0] == "a": continue
                _wrap_heads(_val(e, CT, RAW("nzero")), wraps)
            except Exception:
                continue
    for nm, sorts, deps, subs in rows:
        try:
            benv, tel = {}, []
            for b, srt in sorts.items():
                if srt == "ctx": continue
                tel.append("{%s : %s}" % (b, _mety(srt, deps[b])))
                benv[b] = _EN[srt]
            body = []
            for expr, srt in subs:
                e = _parse_spine(_tokens(expr))
                if e[0] == "a": continue          # a bare binder proves nothing
                # ⚠ STRIP EXPLICIT IMPLICITS ON THE RIGHT TOO.  `_tokens`
                #   drops `{Γ}` when parsing — `⌜Mu⌝ {⌊ Γ ⌋} D` IS `⌜Mu⌝ D`
                #   — so the source text has to be normalised the same way
                #   or the two sides are not even the same expression.
                body.append((_radq(_val(e, CT, RAW("nzero")), benv),
                             # ⚠ `Mu D` PINS NO SOURCE SCOPE — nothing in
                             #   the expression determines `Γ`, so a
                             #   `RTy`/`RTm` subject must name it too.
                             #   `enDesc`/`enDCon`/`enIDesc` take a closed
                             #   argument and have no source scope at all.
                             "%s %s{Γ' = Δ} (%s)"
                             % (_EN[srt],
                                "{Γ = Γ} " if srt in ("sTy", "sTm", "sVar") else "",
                                          re.sub(r"\{[^{}]*\}", " ", expr).strip())))
            if not body: continue
        except _Wrapper as ex:
            skipped.append((nm, "applies %s" % ex.head)); wraps.add(ex.head); continue
        except Exception as ex:
            skipped.append((nm, type(ex).__name__)); continue
        L.append("-- %s" % nm)
        for lhs, rhs in body:
            L.append("_ : {Γ Δ : Cx} %s→ %s ≡ %s"
                     % ("".join(t + " " for t in tel), lhs, rhs))
            L.append("_ = refl")
            ok += 1
        L.append("")
    return L, ok, skipped, sorted(wraps)


CENSUS_HDR = """--- GENERATED by tools/gen-knot.py — do not edit.
------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE ROW CENSUS, AS A **TYPE-CHECKED**
--                       INVARIANT, AND IT IS GENERATED.
--
-- ① HOW MANY RULES THE SOURCE HAS is read at TYPE-CHECK TIME by
--   REFLECTION — `getDefinition` on a `data-type` yields its constructor
--   list, and `Agda.Builtin.Reflection` works under `--safe` (measured
--   2026-09-01).  Nothing here is a script.
-- ② HOW MANY ROWS THE ENCODING HAS is ordinary Agda: `IDesc` is a
--   first-order list, so `ilen` is three lines and `refl` decides it.
-- ③ …and the two are RELATED by an equation, per family, with the
--   generator's OWN skip count in the middle.  ⚠ That is what makes it
--   test something: `rules` counts the DATATYPE, independently of the
--   generator, so a rule the text parser never SAW makes the sum fall
--   short — which is the `⊢ielim` regex class, caught arithmetically.
--
-- ★★★ AND IT IS GENERATED FROM THE FAMILY TABLE, which is the point.
--   `InIDD` once shipped as `inil` — a WELL-FORMED EMPTY DESCRIPTION —
--   because a binder type was missing and both its rows silently failed
--   to translate.  The census would have caught it that day and did not,
--   because the family had been ADDED WITHOUT ADDING ITS CENSUS ROW.
--   ⇒ a hand-maintained list of invariants rots exactly like any other
--     parallel list.  There is now ONE place to add a family.
--
-- ⚠ WHAT THIS DOES NOT CATCH: a row that is well-formed but encodes the
--   WRONG RULE.  Counting is the cheap SHADOW of the correspondence;
--   `Knot/Adequacy` checks the values and a full `enDeriv` would subsume
--   both.  See JUDGEMENT-ATTEMPTS §13.4.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Census where
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat renaming ( Nat to ℕ )
open import Agda.Builtin.Equality
open import DirectedHoTT.Spec.Syntax using ( IDesc; inil; _◂_ )
%(imports)s

len : {A : Set} → List A → ℕ
len []       = 0
len (_ ∷ xs) = suc (len xs)

conList : Name → TC (List Name)
conList n = bindTC (getDefinition n) λ where
  (data-type _ cs) → returnTC cs
  _                → returnTC []

macro
  rules : Name → Term → TC ⊤
  rules n hole = bindTC (conList n) λ cs → unify hole (lit (nat (len cs)))

ilen : IDesc → ℕ
ilen inil    = 0
ilen (_ ◂ D) = suc (ilen D)

"""

# where each judgement's Agda datatype lives
_SRCMOD = {"Typing": "DirectedHoTT.Spec.Typing",
           "Syntax": "DirectedHoTT.Spec.Syntax",
           "Variance": "DirectedHoTT.Spec.Variance"}

# ★★★ HOW MANY RULES EACH FAMILY IS ALLOWED NOT TO TRANSLATE.
#
# ⚠⚠ THIS MUST BE HAND-MAINTAINED, AND THE FIRST VERSION OF THE GENERATED
#   CENSUS WAS WEAKER THAN THE HAND-WRITTEN ONE IT REPLACED BECAUSE IT WAS
#   NOT.  Emitting the generator's OWN skip count makes the equation
#   `ilen D + skips ≡ rules X` true BY CONSTRUCTION: when both `_∈ID_`
#   rows silently failed to translate, `skips` became 2, `ilen InIDD`
#   became 0, and `0 + 2 ≡ 2` PASSED.  The check was insensitive to
#   exactly the failure it exists for.  ⇒ CONTROL RUN, and it did not fire.
#
# ★ So the number below is a CLAIM, checked against reality here, and the
#   Agda equation then pins it exactly.  Raising one is a deliberate act,
#   the same contract as `_FLOOR`.
_SKIP_EXPECT = {"RedD": 2, "TyRedD": 0, "ConvD": 0, "NoNatCD": 0,
                "InDD": 0, "InIDD": 0, "JudgeD": 5}

def gen_census(out):
    """one equation per family, from `_CENSUS` — so a family cannot be
    added without its check."""
    for desc, _, nskip, _ in _CENSUS:
        want = _SKIP_EXPECT.get(desc)
        if want is None:
            sys.exit("  ⇒ %s has no `_SKIP_EXPECT` entry.  Add one — a family "
                     "without a claimed skip count is unchecked." % desc)
        if nskip != want:
            sys.exit("  ⇒ %s: %d rule(s) did not translate, expected %d.  "
                     "If that is intended, change `_SKIP_EXPECT`; if not, a "
                     "rule just went silently missing." % (desc, nskip, want))
    bymod, descs, L = {}, [], []
    for desc, datas, nskip, src in _CENSUS:
        bymod.setdefault(_SRCMOD[src], []).extend(datas)
        descs.append(desc)
    imp = ["open import %s using ( %s )" % (m, "; ".join(sorted(set(ds))))
           for m, ds in sorted(bymod.items())]
    # the description of each family comes from its Rows module
    _ROWMOD = {"JudgeD": "JudgeRows", "RedD": "RedRows"}
    for desc, _, _, _ in _CENSUS:
        m = _ROWMOD.get(desc, desc[:-1] + "Rows")
        imp.append("open import DirectedHoTT.Examples.Knot.%s using ( %s )" % (m, desc))
    for desc, datas, nskip, _ in _CENSUS:
        rhs = " + ".join("rules %s" % d for d in datas)
        nskip = _SKIP_EXPECT[desc]      # the CLAIM, not the observation
        lhs = "ilen %s" % desc if not nskip else "ilen %s + %d" % (desc, nskip)
        L.append("-- %s  (%d rule%s the generator could not translate)"
                 % (desc, nskip, "" if nskip == 1 else "s"))
        L.append("_ : %s ≡ %s" % (lhs, rhs))
        L.append("_ = refl")
        L.append("")
    open(os.path.join(out, "Census.agda"), "w").write(
        CENSUS_HDR % dict(imports="\n".join(imp)) + "\n".join(L) + "\n")
    return len(_CENSUS)


if __name__ == "__main__":
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = os.path.join(root, "Examples", "Knot")
    n_rho = sum(1 for _, _, fs in KNOT for f in fs if f[0] == 'rec')
    n_kap = sum(1 for _, _, fs in KNOT for f in fs if f[0] in ('nat', 'ford'))
    assert len(KNOT) == 53, f"expected 53 constructors, got {len(KNOT)}"
    assert len({n for n, _, _ in KNOT}) == 53, "duplicate constructor name"
    print("== coverage: the table vs `Spec/Syntax.agda`'s own datatypes ==")
    if verify(os.path.join(root, "Spec", "Syntax.agda")):
        sys.exit("  ⇒ TABLE AND SYNTAX DISAGREE — nothing written.")
    open(os.path.join(out, "Desc.agda"), "w").write(gen_desc())
    open(os.path.join(out, "Wf.agda"),   "w").write(gen_wf())
    open(os.path.join(out, "Tags.agda"), "w").write(gen_tags())
    open(os.path.join(out, "Ctors.agda"), "w").write(gen_ctors())
    open(os.path.join(out, "CtorsV.agda"), "w").write(gen_ctorsv())
    open(os.path.join(out, "Map.agda"),   "w").write(gen_map())
    open(os.path.join(out, "SzAgree.agda"), "w").write(gen_szagree())
    # ⚠⚠ NOT SPLIT, AND THE FIRST ATTEMPT TO SPLIT IT WAS A MISREADING.
    #   The 25-row module was OOM-killed at 234s (and 260s under `-c`), so
    #   it was split like `RedWfA`/`RedWfB`.  ★ THOSE TIMES WERE THE COLD
    #   CLOSURE, not the module: with its dependencies already built, the
    #   FULL 25-row module compiles in **12s at the default RTS**, and the
    #   13-row half in 9s.  ⇒ un-split.  `PERF.md` §6.10, fourth instance
    #   in one session — a per-module time is evidence only when the
    #   closure was already warm.
    open(os.path.join(out, "RenAgree.agda"), "w").write(gen_renagree("", 0, 25))
    open(os.path.join(out, "LookupGen.agda"), "w").write(gen_lookupgen())
    open(os.path.join(out, "RedRows.agda"), "w").write(gen_redrows())
    _CENSUS.append(("RedD", ["_⟶_"], len(_SKIP), "Typing"))
    _half = (len(_ROWS) + 1) // 2
    open(os.path.join(out, "RedWfA.agda"), "w").write(gen_redwf("A", 0, _half))
    open(os.path.join(out, "RedWfB.agda"), "w").write(gen_redwf("B", _half, len(_ROWS)))
    _CT = {d.split(":")[0].strip(): n[1:] + "K" for n, d, _ in KNOT}
    _CT.update(_SUBST_CT)
    for _J in (J_IND, J_IIND, J_NONATC, J_TYRED, J_CONV):
        for _m in write_judgement(_J, out, _CT):
            print("  wrote", _m)
    FOREIGN["ConvD"] = TJ("ConvD", "IConv", "ConvWf", TEL_TYR)
    FOREIGN["NoNatCD"] = TJ("NoNatCD", "INoNatC", "NoNatCWf", TEL_NNC)
    FOREIGN["InDD"]  = TJ("InDD",  "IInD",  "InDWf",  J_IND.tel)
    FOREIGN["InIDD"] = TJ("InIDD", "IInID", "InIDWf", J_IIND.tel)
    FOREIGN["LkD"] = TJ("LkD", "ILk", "LkWf",
                        [TNAT(), TCTX(), TKNOT("sVar"), TKNOT("sTy")])
    _njudge = len(write_mutual(out, _CT))
    _KNOTK.update(n[1:] + "K" for n, _, _ in KNOT)
    # ★★★ THE WRAPPER LEDGER, CHECKED BOTH WAYS.  A wrapper the emitter
    #   produces with no entry fails HERE, at generation; an entry no
    #   emitted row uses is a stale claim and fails too.
    _seen = scan_emitted_wrappers(out)
    for _n, _fs in scan_object_programs(out).items(): _seen.setdefault(_n, set()).update(_fs)
    _miss = sorted(set(_seen) - set(_WRAP_LEDGER))
    assert not _miss, (
        "the knot applies or defines %r with no _WRAP_LEDGER entry.  Every "
        "object-level program — emitted wrapper or hand-written eliminator — "
        "owes an adequacy (commutation) lemma or a written reason it does "
        "not." % _miss)
    _stale = sorted(set(_WRAP_LEDGER) - set(_seen))
    assert not _stale, ("_WRAP_LEDGER names %r, which the knot neither applies nor defines." % _stale)
    _awrap = sorted(_seen)
    print("  agreement ledger: %d object-level program(s), %d still OWED"
          % (len(_awrap), sum(1 for w in _awrap if _WRAP_LEDGER[w].startswith("⬜"))))
    _al, _aok, _askip, _ = gen_adequacy(_ADQ, _CT)
    open(os.path.join(out, "Adequacy.agda"), "w").write(
        ADQ_HDR % dict(ok=_aok, skip=len(_askip),
                       named="\n".join("--     %-12s %s" % t for t in _askip),
                       ledger="\n".join("--     %-10s %s" % (w, _WRAP_LEDGER[w])
                                        for w in _awrap))
        + "\n".join(_al) + "\n")
    print("  wrote Adequacy (%d checks, %d subjects skipped)" % (_aok, len(_askip)))
    print("  wrote Census (%d families)" % gen_census(out))
    print("  wrote JudgeRows (%d rows)" % _njudge)

    # ★★★ THE EMITTED COUNT IS A RATCHET.
    #
    # ⚠⚠ A SHRINKING ROW SET IS INVISIBLE TO EVERY OTHER CHECK.  Fewer
    #   rows still typecheck, `check.sh` still returns 0 and the sweep
    #   still says ALL GREEN — a description with rows missing is a
    #   perfectly well-formed description.  On 2026-08-31 that shipped a
    #   commit claiming `⊢app`/`⊢pair`/`⊢snd`/`⊢jsub` emitted when a
    #   table-indexing change had silently dropped all four; rc=0 and
    #   ALL GREEN both held.  ⇒ `verification-that-covers-less-than-it-
    #   claims`, and the COUNT is the only witness.
    #
    # ★ So it is asserted here, where it is computed.  Raising these
    #   numbers when rules land is the intended edit; seeing one FALL is
    #   the bug this exists to make loud.
    # ⚠ MEASUREMENT KNOB, and it DISARMS THE RATCHET.  `JUDGE_MAX_ROWS=n`
    #   truncates the judgement to `n` rows so its cost can be timed from
    #   BELOW, without ever running the full module at the memory cap —
    #   profiling the big one repeatedly is what OOMs a 7.7 GB box.
    #   ⇒ output under this knob is FOR TIMING ONLY, never to commit.
    if os.environ.get("JUDGE_MAX_ROWS"):
        print("  ⚠ JUDGE_MAX_ROWS=%s — TRUNCATED OUTPUT, ratchet disarmed."
              % os.environ["JUDGE_MAX_ROWS"])
        print("    DO NOT COMMIT.  Re-run without it to restore.")
        sys.exit(0)
    _FLOOR = {"Red": 71, "Judge": 51, "TyRed": 26, "Conv": 4}
    _got = {"Red": len(_ROWS), "Judge": _njudge,
            "TyRed": len(_JCACHE["TyRed"]), "Conv": len(_JCACHE["Conv"])}
    _lost = {k: (v, _got[k]) for k, v in _FLOOR.items() if _got[k] < v}
    if _lost:
        sys.exit("  ⇒ ROWS LOST — %s.  Files are written; do NOT commit."
                 % "; ".join("%s %d→%d" % (k, a, b) for k, (a, b) in _lost.items()))
    print(f"{len(KNOT)} constructors · {n_rho} recursive fields · "
          f"{n_kap} κ fields · {2 * (n_rho + n_kap) + 2 * len(KNOT)} "
          f"generated clauses")
