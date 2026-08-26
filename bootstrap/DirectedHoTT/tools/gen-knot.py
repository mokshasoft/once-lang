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
  TAG (0 RTy · 1 RTm · 2 Desc · 3 DCon · 4 IDesc · 5 ICon · 6 Var), `snd` is
  a CONTEXT DEPTH.  Every constructor FORDS ITS TAG ONLY — `Id Nat (fst ⟨i⟩)
  t` — and the depth RIDES, unconstrained (PLAN-INDEXED §14).  A recursive
  field names its own index outright: `lam`'s field is
  `pair 1 (suc (snd ⟨i⟩))` (same sort, depth pushed), `El`'s is
  `pair 1 (snd ⟨i⟩)` (other sort, depth held).

⚠ THE TWO EXCEPTIONS, and they are real.  `Var`'s `vz`/`vs` are the only
  constructors whose TARGET depth is constrained — they exist only at
  `suc m` — so they bind an `m : Nat` and Ford the SECOND component too.
  That is Fording used exactly as `Examples/Scoped`'s `Fin` uses it, and it
  is why "Ford the component, not the pair" is the right rule rather than
  "Ford the tag": BOTH components can need it, INDEPENDENTLY.

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
    L.append("-- ★ the description: 53 constructors, in table order.")
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
         "--   53 `IConWf`s in one module, measured cold on a 7.7 GB box,",
         "--   and RE-MEASURED 2026-08-26 after `Knot/Sz`'s marker turned out",
         "--   to be stale — this one is not:",
         "--     -A64m       OOM (143) at 76s;",
         "--     -A64m -c    104s, comfortably.",
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

def term_of(acts, NN="n"):
    t = f"num {NN}"
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

def depth_expr(E):
    if E[0] == "D":    return "num n"
    if E[0] == "sucD": return "num (" + "suc (" * E[1] + "n" + ")" * E[1] + ")"
    if E[0] == "lit":  return f"num {E[1]}"
    raise ValueError(E)

def entry_ty(f, sX, en, NN="n", en0=None):
    if f[0] == "nat":  return "ty-El ⊢⌜Nat⌝"
    if f[0] == "ford":
        if f[1] == "snd":            # the DEPTH ford — `Var` only
            return (f"ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢snd (⊢ixP ⊢{sX} (⊢numAt {NN} {en}))))"
                    f" (toI (⊢nsuc (⊢numAt n {en0}))))")
        return (f"ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP ⊢{sX} (⊢numAt {NN} {en})))) (toI ⊢{sX}))")
    s, E = f[1], f[2]
    if E[0] == "lit": return f"ty-IMu KnotWf (⊢ixP ⊢{s} (⊢num {E[1]}))"
    if E[0] == "fld": return f"ty-IMu KnotWf (⊢ixP ⊢{s} (⊢numAt n {en0}))"
    inner = f"⊢snd (⊢ixP ⊢{sX} (⊢numAt {NN} {en}))"
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

def emit_row(name, decl, fields):
    sX, m = SORT[name.split("-")[0]], len(fields)
    nm = name[1:]
    nargs = [j for j, f in enumerate(fields) if f[0] in ("rec", "nat")]
    L = [f"-- {decl}"]
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
    def needs_eq(f):
        return f[0] == "ford" or (f[0] == "rec" and f[2][0] in ("D", "sucD"))
    def B_of(k):
        if k == m - 1: return "ty-Unit"
        B = "ty-Unit"
        for j in reversed(range(k + 1, m)):
            e = en(actions(k, j)) if needs_eq(fields[j]) else "refl"
            B = f"ty-Σ ({entry_ty(fields[j], sX, e)}) ({B})"
        return B
    Bs, cs = [], []
    for k in range(m):
        Bs.append(B_of(k))
        a = actions(k, k)
        e = en(a) if (fields[k][0] == "rec" and fields[k][2][0] in ("D", "sucD")) else "refl"
        cs.append(component(fields[k], k, sX, e, term_of(a)))
    prem = ["Δ ⊢ a{} ∷ Nat".format(j) if fields[j][0] == "nat"
            else f"Δ ⊢ a{j} ∷ K (pair {fields[j][1]} ({depth_expr(fields[j][2])}))"
            for j in nargs]
    imp = " ".join(f"a{j}" for j in nargs)
    L.append(f"⊢{nm}K : {{Δ : Ctx}} (n : ℕ)" + (f" {{{imp} : RTm ⌊ Δ ⌋}}" if nargs else "") + " →")
    for p in prem: L.append(f"        {p} →")
    L.append(f"        Δ ⊢ {nm}K " + " ".join(f"a{j}" for j in nargs) + f" ∷ K (pair {sX} (num n))")
    L.append(f"⊢{nm}K n " + " ".join(f"{{a{j} = a{j}}}" for j in nargs) +
             (" " if nargs else "") + " ".join(f"d{j}" for j in nargs) + " =")
    L.append(f"  ⊢icon KnotWf mem{nm} (⊢ixP ⊢{sX} (⊢num n))")
    ind = "    "
    for k in range(m):
        L.append(f"{ind}(⊢pair ({Bs[k]})")
        L.append(f"{ind}       ({cs[k]})")
        ind += " "
    L.append(f"{ind}⊢unit" + ")" * m)
    if eqs:
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
        n_here = "n" if sX in CLOSED else f"(len {CARRIER[sX]})"
        if nm == "cVar-vz":
            L.append("⊢enVar {Γ = Γ ∙} vz = ⊢Var-vzK (len Γ)"); continue
        if nm == "cVar-vs":
            L.append("⊢enVar {Γ = Γ ∙} (vs x) = ⊢Var-vsK (len Γ) (⊢enVar x)"); continue
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
    open(os.path.join(out, "Map.agda"),   "w").write(gen_map())
    print(f"53 constructors · {n_rho} recursive fields · {n_kap} κ fields "
          f"· {2 * (n_rho + n_kap) + 106} generated clauses")
