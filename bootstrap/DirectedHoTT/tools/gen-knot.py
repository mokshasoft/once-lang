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
import sys, os

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
    t = "var x" if V else f"num {NN}"
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
    if E[0] == "D":    return "var x"
    if E[0] == "sucD": return "nsuc (" * E[1] + "var x" + ")" * E[1]
    raise ValueError(E)

def _dvar(r):
    "the depth derivation `r` binders in, for a VARIABLE depth"
    return "⊢wk (" * r + "dx" + ")" * r

def depderiv(acts, en, V):
    """the DEPTH's derivation at a position reached by `acts`.
    ★ numeral: recognise it (`⊢numAt` + the chain).
    ★ variable: move it (`⊢wk`), and the substitutions cancel renamings
      on a variable, so only the surplus renamings survive."""
    if not V: return "⊢num n" if en == "refl" else f"⊢numAt n {en}"
    r = sum(1 for a in acts if a[0] == "ren") - sum(1 for a in acts if a[0] == "sub")
    return _dvar(max(r, 0))

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
        t = term_of(acts)
        if t not in eqs: eqs[t] = (f"e{len(eqs)}", acts)
        return eqs[t][0]
    def dd(acts):
        return depderiv(acts, en(acts) if not V else None, V)
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
        cs.append(component(fields[k], k, sX, "refl" if V else e, term_of(a, V=V)))
    prem = ["Δ ⊢ a{} ∷ Nat".format(j) if fields[j][0] == "nat"
            else f"Δ ⊢ a{j} ∷ K (pair {fields[j][1]} ({depth_expr(fields[j][2], V)}))"
            for j in nargs]
    imp = " ".join(f"a{j}" for j in nargs)
    sig = "⊢%sK%s" % (nm, "v" if V else "")
    if V:
        L.append(f"{sig} : {{Δ : Ctx}} {{x : Var ⌊ Δ ⌋}}"
                 + (f" {{{imp} : RTm ⌊ Δ ⌋}}" if nargs else "") + " →")
        L.append("        Δ ⊢ var x ∷ Nat →")
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
    lhs  = (["{x = x}"] + flds + ["dx"] + ds) if V else (["n"] + flds + ds)
    L.append(f"{sig} " + " ".join(lhs) + " =")
    L.append(f"  ⊢icon KnotWf mem{nm} (⊢ixP ⊢{sX} ({depderiv([], 'refl', V)}))")
    ind = "    "
    for k in range(m):
        L.append(f"{ind}(⊢pair ({Bs[k]})")
        L.append(f"{ind}       ({cs[k]})")
        ind += " "
    L.append(f"{ind}⊢unit" + ")" * m)
    if eqs and not V:
        L.append("  where")
        for t, (e, acts) in eqs.items():
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
        ; _\u22a2_\u2237_; _\u22a2ty_; \u22a2var; here; there; \u22a2conv
        ; \u22a2pair; \u22a2fst; \u22a2snd; \u22a2unit; \u22a2nzero; \u22a2nsuc; \u22a2\u231cNat\u231d; \u22a2\u231cId\u231d; \u22a2idrefl; \u22a2icon
        ; ty-El; ty-Unit; ty-Nat; ty-\u03a3; ty-IMu
        ; _\u27f6_; \u03b2fst; \u03b2snd; \u03be-pair\u02b3; \u03be-nsuc
        ; _\u2245\u1d40_; csym\u1d40; ctrn\u1d40; cred\u1d40; El-\u231cId\u231d; \u03be-El; \u03be-IMu; \u03be-\u231cId\u231d\u02e1 )
open import DirectedHoTT.Metatheory.SubjectReduction using ( \u22a2wk )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; \u22a2sTy; \u22a2sTm; \u22a2sDesc; \u22a2sDCon; \u22a2sIDesc; \u22a2sICon; \u22a2sVar
        ; toI; fromI; \u22a2ixP; num; \u22a2num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Tags
open import DirectedHoTT.Examples.Knot.Terms using ( ixConv; fordFst; tyFordFst )
open import DirectedHoTT.Examples.Knot.Ctors
  using ( """ + "; ".join(n[1:] + "K" for n, _, _ in KNOT if not n.startswith("cVar-")) + """ )

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
def TCTX():        return ('tctx',)
def TKNOT(sort):   return ('tknot', sort)

def _code(comp, d):
    "the object-level code for telescope component `comp` at depth `d`"
    if comp[0] == 'tnat':  return RAW("⌜Nat⌝")
    if comp[0] == 'tctx':  return AP("⌜IMu⌝", RAW("CtxD"), RAW("INat"), d)
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
WF_CTOR = {
    "Ctx-extK": ("⊢Ctx-extKv", ["N", "MU", "MU"], None),
    "Var-vzK":  ("⊢Var-vzKv",  ["N"],             None),
    "Var-vsK":  ("⊢Var-vsKv",  ["N", "MU"],       None),
    # ★ `wkK` lands at `sh (pair s m)` while the ford wants
    #   `pair s (nsuc m)` — the same two β-steps every time.
    "wkK":      ("⊢wkK",       ["IX", "MU"],      "WK"),
}

def _telty(comp):
    return ('nat',) if comp[0] == 'tnat' else ('mu', comp)

def _famwf(comp):
    return "CtxWf" if comp[0] == 'tctx' else "KnotWf"

def _ixderiv(comp, dnat):
    """the family's INDEX derivation, from one at native `Nat`.
    ⚠ `CtxD`'s index is `INat` — already `El ⌜Nat⌝` — and `KnotD`'s is
      `Σ' Nat Nat`.  The two want OPPOSITE coercions, and this is the
      only place that difference is written down."""
    if comp[0] == 'tctx': return "toI " + par(dnat)
    return "⊢ixP ⊢%s %s" % (comp[1], par(dnat))

def _codewf(comp, dnat):
    "…and that the CODE itself is in `U`"
    if comp[0] == 'tnat': return "⊢⌜Nat⌝"
    return "⊢⌜IMu⌝ %s %s" % (_famwf(comp), par(_ixderiv(comp, dnat)))

def _binder_comp(code):
    """(component, depth-expression) recovered from a binder's CODE.
    ★ So the description does not have to say twice what it already says
      once — and the two emitters cannot drift apart about it."""
    if code[0] == 'raw':                       # ⌜Nat⌝
        return TNAT(), None
    _, h, args = code
    assert h == "⌜IMu⌝", code
    fam = args[0][1]
    if fam == "CtxD": return TCTX(), args[2]
    return TKNOT(args[2][1][1]), args[2][2]    # PAIR(RAW(sort), depth)

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
            ds = []
            for a, r in zip(args, roles):
                ds.append(par(jd(a, k, ix, binders, tel)[0]) if r == 'IX'
                          else par(jdAt(a, k, ix, binders, tel,
                                        'nat' if r == 'N' else 'mu')))
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

def emit_jrowwf(row, tel, pre, ity, wfname, idesc=None):
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
        rho = nb
        names = ["%s%d" % (T, j) for j in range(rho + 1, len(fs) + 1)]
        L.append("-- ★ the telescope, back at `Ctx` level: `emit_jrow` had to")
        L.append("--   drop to a bare `Cx` at the premise to stay writable")
        L.append("--   before `%s` existed." % idesc)
        L.append("%s : Ctx" % " ".join(names))
        L.append("%s%d = %s%d ▹ IMu %s %s %s%d"
                 % (T, rho + 1, T, rho, idesc, ity, F, rho))
        for j in range(rho + 1, len(fs)):
            L.append("%s%d = %s%d ▹ El %s%d" % (T, j + 1, T, j, F, j))
        L.append("")
    for k in range(len(fs) - 1, -1, -1):
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
            comps = _tupcomps(e)
            body, m = None, len(tel)
            for j in range(m - 2, -1, -1):
                if j == 0:
                    depfn = lambda t: dbd(t)          # the Σ-BOUND depth
                else:
                    d0 = jdAt(comps[0], k, vis, bty, tel, 'nat')
                    depfn = (lambda d0: (lambda t: _wks(t, d0)))(d0)
                # ⚠ `t` STARTS AT 1 FOR A VALUE DEPTH, 0 FOR THE BOUND
                #   ONE.  `⊢pair`'s ⊢ty argument is already UNDER the
                #   pair's own binder, so a depth taken from the ambient
                #   context is one weakening away — while the Σ-bound
                #   depth IS that binder.  Off by one here still
                #   typechecks at a different component.
                ty = _tailty(j + 1, 0 if j == 0 else 1, tel, depfn)
                if body is None:
                    body = ("⊢pair %s %s %s"
                            % (par(ty),
                               par(jdAt(comps[j], k, vis, bty, tel,
                                        'nat' if j == 0 else 'mu')),
                               par(jdAt(comps[m - 1], k, vis, bty, tel, 'mu'))))
                else:
                    body = ("⊢pair %s %s\n      (%s)"
                            % (par(ty),
                               par(jdAt(comps[j], k, vis, bty, tel,
                                        'nat' if j == 0 else 'mu')),
                               body))
            rung = "iwf-ρ %s%d\n    (%s)" % (F, k, body)
            L.append("%s%d : IConWf %s %s %s%d %s"
                     % (W, k, idesc, ity, T, k, _conFrom(fs, F, k)))
            L.append("%s%d =\n  %s\n    %s" % (W, k, rung, inner))
            L.append("")
            continue
        if k < nb:
            comp = bty[row.binders[k][0]]
            if comp[0] == 'tnat':
                rung = "iwf-κ %s%d (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝" % (F, k)
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
                rung = ("iwf-κ %s%d (icw-ford _ _ _)\n"
                        "    (⊢⌜Id⌝ %s\n"
                        "           %s\n"
                        "           (⊢jsub %s\n"
                        "                  (toI %s)\n"
                        "                  (toI (⊢fst (%s)))\n"
                        "                  (⊢symN (⊢fst (%s)) %s\n"
                        "                         (fordAs (%s)))\n"
                        "                  %s))"
                        % (F, k,
                           par(_codewf(comp, "⊢fst (%s)" % damb)),
                           par(jdAt(_proj(c, n, AMB), k, vis, bty, tel, 'el')),
                           par(_codewf(comp, "fromI (⊢var here)")),
                           par(d0), damb, damb, par(d0),
                           dbd(k - 1 - depth_at),
                           par(jdAt(row.vals[c], k, vis, bty, tel, 'el'))))
        if para:
            L.append("%s%d : (D : IDesc) → IConWf D %s %s%d %s"
                     % (W, k, ity, T, k, _conFrom(fs, F, k)))
            L.append("%s%d D =\n  %s\n    (%s)" % (W, k, rung,
                     inner if inner == "iwf-ι" else inner + " D"))
        else:
            L.append("%s%d : IConWf %s %s %s%d %s"
                     % (W, k, idesc, ity, T, k, _conFrom(fs, F, k)))
            L.append("%s%d =\n  %s\n    %s" % (W, k, rung, inner))
        L.append("")
    if para:
        L.append("%s : (D : IDesc) → IConWf D %s %s0 %s" % (wfname, ity, T, row.name))
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
    "the ICon suffix from field `k` on"
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
  using ( Cx; ε; _∙; RTm; var; vz; vs; pair; fst; snd; nsuc; El; IMu
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub; ICon; IDesc; iι; iρ; iκ; εwkTy )
open import DirectedHoTT.Spec.Typing using ( Ctx; ◇; _▹_; ⌊_⌋ )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; sTy; sVar )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.CtxD using ( CtxD; INat; Ctx-extK )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK )
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
open import DirectedHoTT.Examples.Knot.CtxD using ( CtxWf; ⊢Ctx-extKv )
open import DirectedHoTT.Examples.Knot.Build using ( ⊢Var-vzKv; ⊢Var-vsKv )
open import DirectedHoTT.Examples.Knot.Wk using ( ⊢wkK )
open import DirectedHoTT.Examples.Knot.JudgeLib using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( ⊢symN )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Lookup
  using ( ILk; LkD; lkHere; lkThere )

"""

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
       AP("wkK", PAIR(RAW("sTy"), V("m")), V("A"))])
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
       AP("wkK", PAIR(RAW("sTy"), V("m")), V("A"))])
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
    open(os.path.join(out, "LookupGen.agda"), "w").write(gen_lookupgen())
    print(f"{len(KNOT)} constructors · {n_rho} recursive fields · "
          f"{n_kap} κ fields · {2 * (n_rho + n_kap) + 2 * len(KNOT)} "
          f"generated clauses")
