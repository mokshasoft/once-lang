#!/usr/bin/env python3
"""
gen-knot.py — the kernel's own syntax (`RTy`/`RTm`) as ONE levitated family,
FIBRED BY SORT (D075) with the depth RIDING (D074).

★ THE ENCODING.  Index `KI = SortI ⌜Nat⌝ 2 = Σ (s : Fin 2) Nat`: a SORT
  (0 RTy · 1 RTm) and a CONTEXT DEPTH.  The fibre over `(s , d)` is sort
  `s`'s constructor list (`Lib/Sorted.Dₛ`): NO constructor carries a sort
  equation, and none carries a depth equation — a recursive field names
  its own index outright (`lam`'s body is at `(1 , suc d)`).
  `Var Γ` is the nested `Fin` family (`Lib/FinFam`), a σ-field at the
  ambient depth; `ℕ` arguments are σ-fields of code `⌜Nat⌝`.
  Descriptions are terms (D072), so there are no Desc/DCon/IDesc/ICon sorts.

★ THE ROWS ARE PARSED OUT OF `Spec/Syntax.agda`, not transcribed: every
  constructor of `RTy`/`RTm`, in declaration order, its argument types read
  as fields.  A kernel former added or removed changes the Knot on the next
  run, and `--check` fails if the committed output is stale.

Outputs (under Examples/Knot/):
  Desc.agda   the telescopes, the family `KD`, its well-formedness
  Ctors.agda  the term formers and their typing at EVERY depth
  Terms.agda  the QUOTATION: every `RTy Γ`/`RTm Γ` as a Knot term at depth
              `|Γ|`, typed — the encoding reaches the whole syntax

Usage:  python3 tools/gen-knot.py [--check]
"""
import os, re, sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
SYNTAX = os.path.join(ROOT, "Spec", "Syntax.agda")
OUTDIR = os.path.join(ROOT, "Examples", "Knot")

SORTS = {"RTy": 0, "RTm": 1}

# Agda-safe names for the source constructors
NAMES = {
    "⌜base⌝": "cbase", "⌜Π⌝": "cPi", "⌜Σ⌝": "cSg", "⌜Hom⌝": "cHom", "⌜Id⌝": "cId",
    "⌜Nat⌝": "cNat", "⌜IMu⌝": "cIMu", "⌜Fin⌝": "cFin", "⌜Unit⌝": "cUnit",
    "Π": "Pi", "Σ'": "Sg", "dι": "dI", "dσ": "dS", "dρ": "dR",
}

def kname(src):
    return "k" + NAMES.get(src, src)

# ------------------------------------------------------------ the parser
def parse():
    txt = open(SYNTAX, encoding="utf-8").read()
    rows = []
    for data in ("RTy", "RTm"):
        m = re.search(r"^data %s where\n(.*?)(?=^\S)" % data, txt, re.S | re.M)
        assert m, data
        for line in m.group(1).split("\n"):
            line = line.split("--")[0].rstrip()
            mm = re.match(r"^  (\S+)\s*:\s*∀ \{Γ\} → (.*)$", line)
            if not mm:
                assert not line.strip(), "unparsed constructor line: %r" % line
                continue
            name, ty = mm.group(1), mm.group(2)
            parts = [p.strip() for p in split_arrows(ty)]
            assert parts[-1] == data + " Γ", (name, parts)
            rows.append((data, name, [field(p, name) for p in parts[:-1]]))
    return rows

def split_arrows(ty):
    out, depth, cur = [], 0, ""
    i = 0
    while i < len(ty):
        c = ty[i]
        if c == "(": depth += 1
        if c == ")": depth -= 1
        if depth == 0 and ty.startswith("→", i):
            out.append(cur); cur = ""; i += 1; continue
        cur += c; i += 1
    out.append(cur)
    return out

def field(p, name):
    """('rec', sort, n) | ('var',) | ('nat',)"""
    if p == "ℕ": return ("nat",)
    if p == "Var Γ": return ("var",)
    m = re.match(r"^(RTy|RTm) (.*)$", p)
    assert m, (name, p)
    ctx = m.group(2)
    n = ctx.count("∙")
    assert ctx.replace("(", "").replace(")", "").replace("∙", "").strip() == "Γ", (name, p)
    return ("rec", SORTS[m.group(1)], n)

# ------------------------------------------------------------ emission
def vs(k, inner="vz"):
    for _ in range(k): inner = "vs (%s)" % inner if " " in inner else "vs %s" % inner
    return inner

def var(k):
    v = vs(k)
    return "var (%s)" % v if " " in v else "var %s" % v

def nsucs(n, t):
    for _ in range(n): t = "nsuc (%s)" % t
    return t

def there(k):
    t = "here"
    for _ in range(k): t = "there (%s)" % t
    return t

def isucs(n, d):
    for _ in range(n): d = "⊢isuc (%s)" % d
    return d

def lt(s):
    return "lt-z" if s == 0 else "(lt-s lt-z)"

def tel(fields):
    """the telescope, over the index variable (k = σ-binders so far)"""
    def go(fs, k):
        if not fs: return "tι"
        f, rest = fs[0], fs[1:]
        if f[0] == "rec":
            return "tρ (pair (tag %d) (%s)) (%s)" % (f[1], nsucs(f[2], "snd (%s)" % var(k)), go(rest, k))
        if f[0] == "nat":
            return "tσ ⌜Nat⌝ (%s)" % go(rest, k + 1)
        if f[0] == "var":
            return "tσ (⌜IMu⌝ ⌜Nat⌝ FinD (snd (%s))) (%s)" % (var(k), go(rest, k + 1))
    return go(fields, 0)

def telok(fields):
    def go(fs, k):
        if not fs: return "ok-ι"
        f, rest = fs[0], fs[1:]
        ix = "⊢var (%s)" % there(k)
        if f[0] == "rec":
            return "ok-ρ (⊢ixₛ ⊢J %s (%s)) (%s)" % (lt(f[1]), isucs(f[2], "⊢dep (%s)" % ix), go(rest, k))
        if f[0] == "nat":
            return "ok-σ ⊢⌜Nat⌝ (%s)" % go(rest, k + 1)
        if f[0] == "var":
            return "ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢dep (%s))) (%s)" % (ix, go(rest, k + 1))
    return go(fields, 0)

HDR = """------------------------------------------------------------------------
-- ⚠⚠ GENERATED by tools/gen-knot.py — DO NOT EDIT BY HAND. ⚠⚠
--
-- The kernel's syntax as ONE family fibred by sort (D075), index
-- `(sort, depth)`, rows parsed out of `Spec/Syntax.agda`.  The encoding is
-- documented in the generator's header.
------------------------------------------------------------------------
"""

def gen_desc(rows):
    ty = [r for r in rows if r[0] == "RTy"]
    tm = [r for r in rows if r[0] == "RTm"]
    L = [HDR, """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Desc where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( tag; lt-z; lt-s )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted
open import DirectedHoTT.Lib.TelAt
open import DirectedHoTT.Lib.FinFam using ( FinD; ⊢FinD; ⊢isuc )

------------------------------------------------------------------------
-- 0. THE INDEX: (sort, depth).
------------------------------------------------------------------------

KI : {Γ : Cx} → RTm Γ
KI = SortI ⌜Nat⌝ 2

⊢J : {Γ : Ctx} → (Γ ▹ El (⌜Fin⌝ 2)) ⊢ ⌜Nat⌝ ∷ U
⊢J = ⊢⌜Nat⌝

⊢KI : {Γ : Ctx} → Γ ⊢ KI ∷ U
⊢KI = ⊢SortI ⊢J

-- the depth of an index
⊢dep : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El KI → Γ ⊢ snd i ∷ El ⌜Nat⌝
⊢dep d = ⊢snd (unSortI d)

------------------------------------------------------------------------
-- 1. THE ROWS — one telescope per constructor, over the index `i`.
------------------------------------------------------------------------
"""]
    for data, name, fs in rows:
        L.append("-- %s  (%s)" % (name, ", ".join(fstr(f) for f in fs) or "no fields"))
        L.append("T-%s : {Γ : Cx} → Tel (Γ ∙)" % kname(name))
        L.append("T-%s = %s" % (kname(name), tel(fs)))
        L.append("")
    for data, rs in (("Ty", ty), ("Tm", tm)):
        L.append("%sTs : {Γ : Cx} → Tels (Γ ∙) %d" % (data, len(rs)))
        L.append("%sTs = %s ∷ᵗ []ᵗ" % (data, " ∷ᵗ ".join("T-" + kname(r[1]) for r in rs)))
        L.append("")
    L.append("""KTss : {Γ : Cx} → STels (Γ ∙) 2
KTss = TyTs ∷ˢᵗ TmTs ∷ˢᵗ []ˢᵗ

-- ★ THE FAMILY, and the syntax at a sort and depth
KD : {Γ : Cx} → RTm Γ
KD = Dₛₜ KTss

K : {Γ : Cx} → ℕ → RTm Γ → RTy Γ
K s d = IMu KI KD (pair (tag s) d)

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.
------------------------------------------------------------------------

module _ {Γ : Ctx} where
""")
    for data, name, fs in rows:
        L.append("  OK-%s : TelOK (Γ ▹ El KI) KI T-%s" % (kname(name), kname(name)))
        L.append("  OK-%s = %s" % (kname(name), telok(fs)))
        L.append("")
    L.append("KOK : {Γ : Ctx} → AllSOK Γ KI KTss")
    L.append("KOK = (%s ∷ᵒ []ᵒ)" % " ∷ᵒ ".join("OK-" + kname(r[1]) for r in ty))
    L.append("   ∷ˢᵒ (%s ∷ᵒ []ᵒ)" % " ∷ᵒ ".join("OK-" + kname(r[1]) for r in tm))
    L.append("   ∷ˢᵒ []ˢᵒ")
    L.append("""
⊢KD : {Γ : Ctx} → Γ ⊢ KD ∷ DescF KI
⊢KD = ⊢Dₛₜ ⊢J KOK
""")
    return "\n".join(L)

def fstr(f):
    if f[0] == "rec": return "%s@+%d" % (["Ty", "Tm"][f[1]], f[2])
    return f[0]

# ------------------------------------------------------------ constructors
def gen_ctors(rows):
    L = [HDR, """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Ctors where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-pairʳ; ⟶*-nsuc; red→≅ᵀ; ⟶ᵀ*-IMu )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ; lt-z; lt-s )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted
open import DirectedHoTT.Lib.TelAt
open import DirectedHoTT.Lib.FinFam using ( FinD; ⊢FinD; FinI; ⊢isuc )
open import DirectedHoTT.Examples.Knot.Desc

------------------------------------------------------------------------
-- The term formers, and their typing at EVERY depth `d`.  A recursive
-- field's index reads `snd (pair (tag s) d)` until `βsnd` fires, so each
-- field is converted once (`ixConv`).
------------------------------------------------------------------------

private
  ixConv : {Γ : Ctx} {t i i' : RTm ⌊ Γ ⌋} → i ⟶* i' → Γ ⊢ t ∷ IMu KI KD i' → Γ ⊢ t ∷ IMu KI KD i
  ixConv r d = ⊢conv d (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu r)))

  nsucs' : {Γ : Cx} → ℕ → RTm Γ → RTm Γ
  nsucs' zero    t = t
  nsucs' (suc n) t = nsuc (nsucs' n t)

  -- the depth of `(tag s , d)` is `d`
  dep-β : {Γ : Cx} (n s : ℕ) (d : RTm Γ) {s' : ℕ} →
          pair (tag s') (nsucs' n (snd (pair (tag s) d))) ⟶* pair (tag s') (nsucs' n d)
  dep-β zero    s d = ⟶*-pairʳ (step (βsnd _ _) done)
  dep-β (suc n) s d = ⟶*-pairʳ (⟶*-nsuc (dep-inner n s d))
    where
      dep-inner : {Γ : Cx} (n s : ℕ) (d : RTm Γ) → nsucs' n (snd (pair (tag s) d)) ⟶* nsucs' n d
      dep-inner zero    s d = step (βsnd _ _) done
      dep-inner (suc n) s d = ⟶*-nsuc (dep-inner n s d)

  ⊢unit' : {Γ : Ctx} → Γ ⊢ unit ∷ El (dpay KI KD dι)
  ⊢unit' = ⊢payι ⊢KI ⊢KD ⊢unit
"""]
    idx = {"RTy": 0, "RTm": 0}
    for data, name, fs in rows:
        s = SORTS[data]; k = idx[data]; idx[data] += 1
        kn = kname(name)
        args = ["a%d" % j for j in range(len(fs))]
        pay = "unit"
        for a in reversed(args): pay = "pair %s (%s)" % (a, pay)
        L.append("%s : {Γ : Cx} → %sRTm Γ" % (kn, "RTm Γ → " * len(fs)))
        L.append("%s %s = conₗ %s (%s)" % (kn, " ".join(args), nat(k), pay))
        L.append("")
        # typing
        prem = ["Γ ⊢ d ∷ El ⌜Nat⌝"]
        for f, a in zip(fs, args):
            if f[0] == "rec": prem.append("Γ ⊢ %s ∷ K %d (%s)" % (a, f[1], nsucs(f[2], "d")))
            elif f[0] == "nat": prem.append("Γ ⊢ %s ∷ El ⌜Nat⌝" % a)
            elif f[0] == "var": prem.append("Γ ⊢ %s ∷ FinI d" % a)
        imp = "{Γ : Ctx} {d%s : RTm ⌊ Γ ⌋}" % "".join(" " + a for a in args)
        L.append("⊢%s : %s →" % (kn, imp))
        L.append("      " + " → ".join(prem) + (" →" if prem else ""))
        L.append("      Γ ⊢ %s ∷ K %d d" % (" ".join([kn] + args), s))
        dargs = " ".join(["dd"] + ["d" + a for a in args])
        L.append("⊢%s %s =" % (kn, dargs))
        # ⚠ PIN the lists and the row: inferred, the unifier re-runs the
        #   lookups inside every meta (measured 16.5 s → 0.12 s for `DIh`)
        L.append("  ⊢conₛₜ {Tss = KTss} {Ts = %sTs} {T = T-%s} ⊢J KOK %s %s dd (%s)"
                 % (["Ty", "Tm"][s], kn, nths(s), ntht(k), payproof(fs, args, s)))
        L.append("  where dix = ⊢ixₛ ⊢J %s dd" % lt(s))
        L.append("")
    return "\n".join(L)

def nat(k):
    t = "zero"
    for _ in range(k): t = "(suc %s)" % t
    return t

def nths(s): return "nthˢᵗ-z" if s == 0 else "(nthˢᵗ-s nthˢᵗ-z)"

def ntht(k):
    t = "nthᵗ-z"
    for _ in range(k): t = "(nthᵗ-s %s)" % t
    return t

def payproof(fs, args, s):
    """the payload, field by field, at the instantiated telescope (index `dix`)"""
    if not fs: return "⊢unit'"
    f, a = fs[0], args[0]
    rest_ok = restok(fs[1:])
    if f[0] == "rec":
        return ("⊢payρ ⊢KI ⊢KD (ok-ρ (⊢ixₛ ⊢J %s (%s)) (%s)) (ixConv (dep-β %d %d _) d%s) (%s)"
                % (lt(f[1]), isucs(f[2], "⊢dep dix"), rest_ok, f[2], s, a, payproof(fs[1:], args[1:], s)))
    # σ fields only ever end a telescope in the kernel's syntax
    assert not fs[1:], "a σ-field followed by more fields needs a wk-single cast"
    if f[0] == "nat":
        return "⊢payσ ⊢KI ⊢KD (ok-σ ⊢⌜Nat⌝ ok-ι) d%s ⊢unit'" % a
    if f[0] == "var":
        return ("⊢payσ ⊢KI ⊢KD (ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢dep dix)) ok-ι) "
                "(⊢conv d%s (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜IMu⌝ⁱ (βsnd _ _)))) (credᵀ El-⌜IMu⌝)))) ⊢unit'" % a)

def restok(fs):
    if not fs: return "ok-ι"
    f = fs[0]
    if f[0] == "rec":
        return "ok-ρ (⊢ixₛ ⊢J %s (%s)) (%s)" % (lt(f[1]), isucs(f[2], "⊢dep dix"), restok(fs[1:]))
    raise AssertionError("σ-field not last")

# ------------------------------------------------------------ quotation
def gen_terms(rows):
    L = [HDR, """{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Terms where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.FinFam using ( FinI; ffz; ffs; ⊢ffz; ⊢ffs; toI; ⊢isuc )
open import DirectedHoTT.Examples.Knot.Desc
open import DirectedHoTT.Examples.Knot.Ctors

------------------------------------------------------------------------
-- The QUOTATION of the kernel's syntax into the Knot: a term of depth
-- `|Γ|` becomes a Knot term at `(sort, |Γ|)`, a variable a `Fin |Γ|`.
------------------------------------------------------------------------

-- the depth of a context, as an object numeral
dep : Cx → {Θ : Cx} → RTm Θ
dep ε       = nzero
dep (Γ ∙)   = nsuc (dep Γ)

⊢dep' : (Γ : Cx) {Θ : Ctx} → Θ ⊢ dep Γ ∷ El ⌜Nat⌝
⊢dep' ε       = toI ⊢nzero
⊢dep' (Γ ∙)   = ⊢isuc (⊢dep' Γ)

-- a meta-level natural, as an object numeral
quoteℕ : ℕ → {Θ : Cx} → RTm Θ
quoteℕ zero    = nzero
quoteℕ (suc n) = nsuc (quoteℕ n)

⊢quoteℕ : (n : ℕ) {Θ : Ctx} → Θ ⊢ quoteℕ n ∷ El ⌜Nat⌝
⊢quoteℕ zero    = toI ⊢nzero
⊢quoteℕ (suc n) = ⊢isuc (⊢quoteℕ n)

-- a variable is a `Fin` of the depth
quoteVar : {Γ : Cx} → Var Γ → {Θ : Cx} → RTm Θ
quoteVar {Γ ∙} vz     = ffz (dep Γ)
quoteVar {Γ ∙} (vs x) = ffs (dep Γ) (quoteVar x)

⊢quoteVar : {Γ : Cx} (x : Var Γ) {Θ : Ctx} → Θ ⊢ quoteVar x ∷ FinI (dep Γ)
⊢quoteVar {Γ ∙} vz     = ⊢ffz (⊢dep' Γ)
⊢quoteVar {Γ ∙} (vs x) = ⊢ffs (⊢dep' Γ) (⊢quoteVar x)

quoteTy : {Γ : Cx} → RTy Γ → {Θ : Cx} → RTm Θ
quoteTm : {Γ : Cx} → RTm Γ → {Θ : Cx} → RTm Θ
"""]
    Q = {"RTy": "quoteTy", "RTm": "quoteTm"}
    def qf(f, a):
        if f[0] == "rec": return "(%s %s)" % (["quoteTy", "quoteTm"][f[1]], a)
        if f[0] == "nat": return "(quoteℕ %s)" % a
        if f[0] == "var": return "(quoteVar %s)" % a
    def df(f, a):
        if f[0] == "rec": return "(⊢%s %s)" % (["quoteTy", "quoteTm"][f[1]], a)
        if f[0] == "nat": return "(⊢quoteℕ %s)" % a
        if f[0] == "var": return "(⊢quoteVar %s)" % a
    for data in ("RTy", "RTm"):
        for d, name, fs in rows:
            if d != data: continue
            args = ["a%d" % j for j in range(len(fs))]
            pat = "(%s)" % " ".join([name] + args) if args else name
            L.append("%s %s = %s" % (Q[data], pat, " ".join([kname(name)] + [qf(f, a) for f, a in zip(fs, args)])))
        L.append("")
    L.append("⊢quoteTy : {Γ : Cx} (A : RTy Γ) {Θ : Ctx} → Θ ⊢ quoteTy A ∷ K 0 (dep Γ)")
    L.append("⊢quoteTm : {Γ : Cx} (t : RTm Γ) {Θ : Ctx} → Θ ⊢ quoteTm t ∷ K 1 (dep Γ)")
    for data in ("RTy", "RTm"):
        for d, name, fs in rows:
            if d != data: continue
            args = ["a%d" % j for j in range(len(fs))]
            pat = "(%s)" % " ".join([name] + args) if args else name
            L.append("⊢%s {Γ} %s = %s" % (Q[data], pat, " ".join(["⊢" + kname(name), "(⊢dep' Γ)"] + [df(f, a) for f, a in zip(fs, args)])))
        L.append("")
    return "\n".join(L)

def main():
    rows = parse()
    outs = {"Desc.agda": gen_desc(rows), "Ctors.agda": gen_ctors(rows), "Terms.agda": gen_terms(rows)}
    check = "--check" in sys.argv
    os.makedirs(OUTDIR, exist_ok=True)
    stale = []
    for fn, txt in outs.items():
        p = os.path.join(OUTDIR, fn)
        if check:
            if not os.path.exists(p) or open(p, encoding="utf-8").read() != txt: stale.append(fn)
        else:
            open(p, "w", encoding="utf-8").write(txt)
    if check and stale:
        print("gen-knot: STALE:", " ".join(stale)); sys.exit(1)
    print("gen-knot: %d rows (%d Ty, %d Tm)%s" % (len(rows), sum(r[0] == "RTy" for r in rows),
                                                  sum(r[0] == "RTm" for r in rows), " — up to date" if check else ""))

if __name__ == "__main__":
    main()
