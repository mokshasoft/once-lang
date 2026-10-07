-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — the ENVIRONMENT EVALUATOR's VALUES (PLAN-EVAL),
--   and the TABLE of the signature's entry values (PLAN-REF, E4).
--
-- Split out of `Algorithm/NbE` so that the evaluator can be parameterised
-- by the table while the values (which the table holds) are not.
--
-- ★ THE TABLE.  A reference is a projection from the signature, and its
--   value is computed ONCE: the table is DATA, built once and passed down
--   as an argument — Agda shares an argument thunk, and recomputes a
--   function application (measured 2026-10-06, `tmp/Share*`: 200 uses of
--   an argument cost one evaluation, 200 of a function call 200).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.NbE.Value where
open import Agda.Builtin.Nat using ( zero; suc; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Variance using ( pwBody; pwShift )
open import DirectedHoTT.Spec.Base using ( single )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. Values, closures, environments.
------------------------------------------------------------------------

data Val : Set
data Clo : Set
data Clo₂ : Set
data Env : Cx → Set
data PwSpine : Val → Set

data Env where
  []  : Env ε
  _,_ : Env Γ → Val → Env (Γ ∙)

-- a body under ONE binder
data Clo where
  clo      : Env Γ → RTm (Γ ∙) → Clo
  -- the defunctionalised binders of the rules' right-hand sides
  cloK     : Val → Clo                   -- x ↦ v            (dpay-ρ: a weakened term)
  -- hrefl-pw: the code C with its pw-SPINE (forced, so its reading is
  --   pw-shaped: the rule's side condition `pw? C`)
  cloHrefl : (C : Val) → PwSpine C → Val → Clo      -- x ↦ hrefl (pwBody C)[x] (s x)
  cloDpay  : Val → Val → Val → Clo       -- x ↦ dpay I D (f x)                       (dpay-σ)
  -- tr-pw: the motive d, the body f, the point e.  ★ `vlam (cloTrPw d f e)`
  --   READS AS THE REDEX `tr d (lam f) e` itself; instantiation and readback
  --   re-check the guard (`trPwView`) at their OWN fuel, and take the rule's
  --   step only then — so nothing about the closure has to be remembered.
  cloTrPw  : Clo → Clo → Val → Clo
  cloHomTo : Val → Val → Clo             -- z ↦ ⌜Hom⌝ C A z                          (tr-pw's motive)

-- a body under TWO binders (natrec's step: pred, rec; psplit: x, y)
data Clo₂ where
  clo₂ : Env Γ → RTm ((Γ ∙) ∙) → Clo₂

-- one constructor per term former (binders become closures), plus levels
-- and references; a value whose head is an eliminator is STUCK.
data Val where
  vvar   : ℕ → Val
  vlam   : Clo → Val
  vapp   : Val → Val → Val
  vpair  : Val → Val → Val
  vabsurd : Val → Val → Val
  vordtr : Val → Val → Val → Val → Val → Val
  vfst vsnd : Val → Val
  v⌜base⌝ : Val
  v⌜Π⌝ v⌜Σ⌝ : Val → Clo → Val
  v⌜Hom⌝ : Val → Val → Val → Val
  vhrefl : Val → Val → Val
  vtr    : Clo → Val → Val → Val
  vap    : Val → Clo → Val → Val
  v⌜Id⌝  : Val → Val → Val → Val
  vidrefl : Val → Val → Val
  vjsub  : Clo → Val → Val → Val
  vunit vnzero : Val
  vnsuc  : Val → Val
  vnatrec : Val → Clo₂ → Val → Val
  vcon   : Val → Val
  vielim : Val → Val → Val → Val → Val
  vdι    : Val
  vdσ vdρ : Val → Val → Val
  vdpay  : Val → Val → Val → Val
  vdih   : Val → Val → Val → Val → Val
  vfzero : Val
  vfsuc  : Val → Val
  vfcase : Val → Val → Clo → Val
  vfcase0 : Val → Val
  vpsplit : Clo₂ → Val → Val
  v⌜Nat⌝ v⌜Unit⌝ : Val
  v⌜IMu⌝ : Val → Val → Val → Val
  v⌜Fin⌝ : Val → Val
  -- a reference: a NAME, forced through the table (PLAN-REF)
  vref   : ℕ → Val

-- tr-pw's inspection, when its guard holds: the pw-normal ambient (with
-- its spine) and the endpoint of the motive at its bound level
data TrPwV : Set where
  trpw : (c : Val) → PwSpine c → Val → TrPwV

-- ★ a pw-able code's SPINE, forced: ⌜Π⌝, or ⌜Hom⌝ over a spine
data PwSpine where
  spΠ   : (c : Val) (d : Clo) → PwSpine (v⌜Π⌝ c d)
  spHom : {C : Val} → PwSpine C → (a b : Val) → PwSpine (v⌜Hom⌝ C a b)

lookup : Env Γ → Var Γ → Val
lookup (ρ , v) vz     = v
lookup (ρ , v) (vs x) = lookup ρ x

------------------------------------------------------------------------
-- 2. VIEWS: what each rule inspects, as a small EXHAUSTIVE family.
--    Every eliminator below cases on a view, never on `Val` with a
--    catch-all — so a proof about it has one case per view constructor,
--    not one per value head (the redex-view lesson of `Metatheory`).
------------------------------------------------------------------------

data RefV : Val → Set where
  isRef  : (d : ℕ) → RefV (vref d)
  notRef : (v : Val) → RefV v

data LamV : Val → Set where
  isLam  : (c : Clo) → LamV (vlam c)
  notLam : (v : Val) → LamV v

data PairV : Val → Set where
  isPair  : (a b : Val) → PairV (vpair a b)
  notPair : (v : Val) → PairV v

data NatV : Val → Set where
  isZero : NatV vnzero
  isSuc  : (t : Val) → NatV (vnsuc t)
  notNat : (v : Val) → NatV v

data FinV : Val → Set where
  isFz   : FinV vfzero
  isFs   : (t : Val) → FinV (vfsuc t)
  notFin : (v : Val) → FinV v

data ConV : Val → Set where
  isCon  : (p : Val) → ConV (vcon p)
  notCon : (v : Val) → ConV v

data DescV : Val → Set where
  isDι    : DescV vdι
  isDσ    : (S f : Val) → DescV (vdσ S f)
  isDρ    : (j C : Val) → DescV (vdρ j C)
  notDesc : (v : Val) → DescV v

data HreflV : Val → Set where
  isHrefl  : (C s : Val) → HreflV (vhrefl C s)
  notHrefl : (v : Val) → HreflV v

data IdreflV : Val → Set where
  isIdrefl  : (c s : Val) → IdreflV (vidrefl c s)
  notIdrefl : (v : Val) → IdreflV v

data HomV : Val → Set where
  isHom  : (c a m : Val) → HomV (v⌜Hom⌝ c a m)
  notHom : (v : Val) → HomV v

data VarV : Val → Set where
  isVar  : (l : ℕ) → VarV (vvar l)
  notVar : (v : Val) → VarV v

-- the codes, as the guards and `El` see them
-- ★ every catch-all constructor CARRIES the value: a clause uses the field,
--   never the implicit index — an index inferred at the call site is a
--   separate copy of the scrutinee expression and would be re-evaluated
--   (measured: the traversal tests 10 s → OOM when stuck branches used it).
data CodeV : Val → Set where
  cbase : CodeV v⌜base⌝
  cΠ    : (c : Val) (d : Clo) → CodeV (v⌜Π⌝ c d)
  cΣ    : (c : Val) (d : Clo) → CodeV (v⌜Σ⌝ c d)
  cHom  : (c a b : Val) → CodeV (v⌜Hom⌝ c a b)
  cId   : (c a b : Val) → CodeV (v⌜Id⌝ c a b)
  cNat  : CodeV v⌜Nat⌝
  cUnit : CodeV v⌜Unit⌝
  cIMu  : (I D i : Val) → CodeV (v⌜IMu⌝ I D i)
  cFin  : (t : Val) → CodeV (v⌜Fin⌝ t)
  cOther : (v : Val) → CodeV v

refV : (v : Val) → RefV v
refV (vref d) = isRef d
refV v          = notRef v

lamV : (v : Val) → LamV v
lamV (vlam c) = isLam c
lamV v        = notLam v

pairV : (v : Val) → PairV v
pairV (vpair a b) = isPair a b
pairV v           = notPair v

natV : (v : Val) → NatV v
natV vnzero    = isZero
natV (vnsuc t) = isSuc t
natV v         = notNat v

finV : (v : Val) → FinV v
finV vfzero    = isFz
finV (vfsuc t) = isFs t
finV v         = notFin v

conV : (v : Val) → ConV v
conV (vcon p) = isCon p
conV v        = notCon v

descV : (v : Val) → DescV v
descV vdι       = isDι
descV (vdσ S f) = isDσ S f
descV (vdρ j C) = isDρ j C
descV v         = notDesc v

hreflV : (v : Val) → HreflV v
hreflV (vhrefl C s) = isHrefl C s
hreflV v            = notHrefl v

idreflV : (v : Val) → IdreflV v
idreflV (vidrefl c s) = isIdrefl c s
idreflV v             = notIdrefl v

homV : (v : Val) → HomV v
homV (v⌜Hom⌝ c a m) = isHom c a m
homV v              = notHom v

varV : (v : Val) → VarV v
varV (vvar l) = isVar l
varV v        = notVar v

codeV : (v : Val) → CodeV v
codeV v⌜base⌝         = cbase
codeV (v⌜Π⌝ c d)      = cΠ c d
codeV (v⌜Σ⌝ c d)      = cΣ c d
codeV (v⌜Hom⌝ c a b)  = cHom c a b
codeV (v⌜Id⌝ c a b)   = cId c a b
codeV v⌜Nat⌝          = cNat
codeV v⌜Unit⌝         = cUnit
codeV (v⌜IMu⌝ I D i)  = cIMu I D i
codeV (v⌜Fin⌝ t)      = cFin t
codeV v               = cOther v

-- is this closure tr-pw's? (its λ-value reads as a REDEX, not a `lam`, so
-- transport rules that need a syntactic λ path leave it stuck)
isTrPw : Clo → Bool
isTrPw (clo _ _)        = false
isTrPw (cloK _)         = false
isTrPw (cloHrefl _ _ _) = false
isTrPw (cloDpay _ _ _)  = false
isTrPw (cloHomTo _ _)   = false
isTrPw (cloTrPw _ _ _)  = true

-- is this value the level `n`?
isLvl : ℕ → {v : Val} → VarV v → Bool
isLvl n (isVar l) = l == n
isLvl n (notVar _) = false

-- ★ is this (forced) code pw-shaped all along its spine?  Structural: the
--   evaluator forces the spine first (`pwForce`), so a `ref` left unforced
--   means "not seen to be pw-able", never a wrong "yes".
pwSpine? : (v : Val) → Maybe (PwSpine v)
pwSpine? (v⌜Π⌝ c d)     = just (spΠ c d)
pwSpine? (v⌜Hom⌝ C a b) = homSp (pwSpine? C)
  where
  homSp : Maybe (PwSpine C) → Maybe (PwSpine (v⌜Hom⌝ C a b))
  homSp (just sp) = just (spHom sp a b)
  homSp nothing   = nothing
pwSpine? v              = nothing


------------------------------------------------------------------------
-- ★ The table: entry d's value, a telescope like the signature's.
------------------------------------------------------------------------

data TTele : Set where
  ∅ᵗ   : TTele
  _▸ᵗ_ : TTele → Val → TTele
infixl 5 _▸ᵗ_

record Tbl : Set where
  constructor mkT
  field
    tlen  : ℕ
    ttele : TTele
open Tbl public

pickV : Bool → Val → Val → Val
pickV true  x y = x
pickV false x y = y

lookupTT : ℕ → TTele → ℕ → Val
lookupTT (suc n) (T ▸ᵗ v) d = pickV (d == n) v (lookupTT n T d)
lookupTT zero    _        d = vref d
lookupTT (suc n) ∅ᵗ       d = vref d

-- entry d's value; a name beyond the table is its own value (stuck, as δ is)
lookupT : Tbl → ℕ → Val
lookupT t d = lookupTT (tlen t) (ttele t) d

∅T : Tbl
∅T = mkT 0 ∅ᵗ

_▸T_ : Tbl → Val → Tbl
mkT n T ▸T v = mkT (suc n) (T ▸ᵗ v)
infixl 5 _▸T_

------------------------------------------------------------------------
-- 6. ★ READING a value as a term (PLAN-EVAL E3).  Levels are read through
--    a map `L : ℕ → RTm Δ`; a closure as its body (a defunctionalised one
--    as its rule's right-hand-side body).  Not a normal form: what
--    readback falls back to when the fuel runs out, and what the soundness
--    proof relates every evaluation step to (`Algorithm/NbERead`).
------------------------------------------------------------------------

-- what the levels stand for
Lv : Cx → Set
Lv Δ = ℕ → RTm Δ

wkL : Lv Δ → Lv (Δ ∙)
wkL L l = renTm vs (L l)

wk : RTm Δ → RTm (Δ ∙)
wk = renTm vs

pickTm : Bool → RTm Δ → RTm Δ → RTm Δ
pickTm true  x y = x
pickTm false x y = y

-- under a binder that binds level m
bindL : ℕ → Lv Δ → Lv (Δ ∙)
bindL m L l = pickTm (l == m) (var vz) (wk (L l))

⌊_⌋  : Val → Lv Δ → RTm Δ
⌊_⌋ᶜ : Clo → Lv Δ → RTm (Δ ∙)
⌊_⌋² : Clo₂ → Lv Δ → RTm ((Δ ∙) ∙)
⌊_⌋ᵉ : Env Γ → Lv Δ → Sub Γ Δ
readLam : Clo → Lv Δ → RTm Δ

⌊ [] ⌋ᵉ     L ()
⌊ ρ , v ⌋ᵉ  L vz     = ⌊ v ⌋ L
⌊ ρ , v ⌋ᵉ  L (vs x) = ⌊ ρ ⌋ᵉ L x

⌊ clo ρ t ⌋ᶜ        L = subTm (extS (⌊ ρ ⌋ᵉ L)) t
⌊ cloK v ⌋ᶜ         L = wk (⌊ v ⌋ L)
⌊ cloHrefl C sp s ⌋ᶜ L = hrefl (pwBody (⌊ C ⌋ L)) (app (wk (⌊ s ⌋ L)) (var vz))
⌊ cloDpay I D f ⌋ᶜ  L = dpay (wk (⌊ I ⌋ L)) (wk (⌊ D ⌋ L)) (app (wk (⌊ f ⌋ L)) (var vz))
⌊ cloHomTo C A ⌋ᶜ   L = ⌜Hom⌝ (wk (⌊ C ⌋ L)) (wk (⌊ A ⌋ L)) (var vz)
-- tr-pw's closure under a binder: its redex applied (only `vlam` of it is
-- ever read, as the redex itself — `readLam`)
⌊ cloTrPw d f e ⌋ᶜ L = app (wk (tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L))) (var vz)

-- a λ-value: its closure's body under `lam` — except tr-pw's, the redex
readLam c@(clo _ _)        L = lam (⌊ c ⌋ᶜ L)
readLam c@(cloK _)         L = lam (⌊ c ⌋ᶜ L)
readLam c@(cloHrefl _ _ _) L = lam (⌊ c ⌋ᶜ L)
readLam c@(cloDpay _ _ _)  L = lam (⌊ c ⌋ᶜ L)
readLam c@(cloHomTo _ _)   L = lam (⌊ c ⌋ᶜ L)
readLam (cloTrPw d f e)    L = tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L)

⌊ clo₂ ρ t ⌋² L = subTm (extS (extS (⌊ ρ ⌋ᵉ L))) t

⌊ vvar l ⌋           L = L l
⌊ vlam c ⌋           L = readLam c L
⌊ vapp f a ⌋         L = app (⌊ f ⌋ L) (⌊ a ⌋ L)
⌊ vpair a b ⌋        L = pair (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ vabsurd c e ⌋      L = absurd (⌊ c ⌋ L) (⌊ e ⌋ L)
⌊ vordtr a t u p q ⌋ L = ordtr (⌊ a ⌋ L) (⌊ t ⌋ L) (⌊ u ⌋ L) (⌊ p ⌋ L) (⌊ q ⌋ L)
⌊ vfst p ⌋           L = fst (⌊ p ⌋ L)
⌊ vsnd p ⌋           L = snd (⌊ p ⌋ L)
⌊ v⌜base⌝ ⌋          L = ⌜base⌝
⌊ v⌜Π⌝ c d ⌋         L = ⌜Π⌝ (⌊ c ⌋ L) (⌊ d ⌋ᶜ L)
⌊ v⌜Σ⌝ c d ⌋         L = ⌜Σ⌝ (⌊ c ⌋ L) (⌊ d ⌋ᶜ L)
⌊ v⌜Hom⌝ c a b ⌋     L = ⌜Hom⌝ (⌊ c ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ vhrefl c t ⌋       L = hrefl (⌊ c ⌋ L) (⌊ t ⌋ L)
⌊ vtr d p e ⌋        L = tr (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L)
⌊ vap c b p ⌋        L = ap (⌊ c ⌋ L) (⌊ b ⌋ᶜ L) (⌊ p ⌋ L)
⌊ v⌜Id⌝ c a b ⌋      L = ⌜Id⌝ (⌊ c ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ vidrefl c t ⌋      L = idrefl (⌊ c ⌋ L) (⌊ t ⌋ L)
⌊ vjsub d p e ⌋      L = jsub (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L)
⌊ vunit ⌋            L = unit
⌊ vnzero ⌋           L = nzero
⌊ vnsuc t ⌋          L = nsuc (⌊ t ⌋ L)
⌊ vnatrec z s t ⌋    L = natrec (⌊ z ⌋ L) (⌊ s ⌋² L) (⌊ t ⌋ L)
⌊ vcon p ⌋           L = con (⌊ p ⌋ L)
⌊ vielim D i e t ⌋   L = ielim (⌊ D ⌋ L) (⌊ i ⌋ L) (⌊ e ⌋ L) (⌊ t ⌋ L)
⌊ vdι ⌋              L = dι
⌊ vdσ S f ⌋          L = dσ (⌊ S ⌋ L) (⌊ f ⌋ L)
⌊ vdρ j C ⌋          L = dρ (⌊ j ⌋ L) (⌊ C ⌋ L)
⌊ vdpay I D C ⌋      L = dpay (⌊ I ⌋ L) (⌊ D ⌋ L) (⌊ C ⌋ L)
⌊ vdih D e C p ⌋     L = dih (⌊ D ⌋ L) (⌊ e ⌋ L) (⌊ C ⌋ L) (⌊ p ⌋ L)
⌊ vfzero ⌋           L = fzero
⌊ vfsuc t ⌋          L = fsuc (⌊ t ⌋ L)
⌊ vfcase t a b ⌋     L = fcase (⌊ t ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ᶜ L)
⌊ vfcase0 t ⌋        L = fcase0 (⌊ t ⌋ L)
⌊ vpsplit b p ⌋      L = psplit (⌊ b ⌋² L) (⌊ p ⌋ L)
⌊ v⌜Nat⌝ ⌋           L = ⌜Nat⌝
⌊ v⌜Unit⌝ ⌋          L = ⌜Unit⌝
⌊ v⌜IMu⌝ I D i ⌋     L = ⌜IMu⌝ (⌊ I ⌋ L) (⌊ D ⌋ L) (⌊ i ⌋ L)
⌊ v⌜Fin⌝ t ⌋         L = ⌜Fin⌝ (⌊ t ⌋ L)
⌊ vref d ⌋           L = ref d


------------------------------------------------------------------------
-- 7. Readback, at a context.  `unfold` = true unfolds every reference
--    (the kernel's normal form); false keeps them as atoms.
------------------------------------------------------------------------

len : Cx → ℕ
len ε     = zero
len (Γ ∙) = suc (len Γ)

-- the variable at level `l`, if it is in scope
-- (out of scope cannot happen for a well-scoped input; the fallback
-- `absurd unit unit` makes such a bug visible in a test, never silent)
-- ★ the length is computed ONCE and passed down (`lvlAt`): recomputing
--   `len` at every level made each variable read quadratic in the depth
--   (profiled 2026-10-06: `len` was 31% of all unfoldings on Pw's rows).
--   `lvl (Γ ∙)` is still `bindL (len Γ) (lvl Γ)` DEFINITIONALLY.
lvlAt : (Γ : Cx) → ℕ → ℕ → RTm Γ
lvlAt ε       m       l = absurd unit unit
lvlAt (Γ ∙)   zero    l = absurd unit unit
lvlAt (Γ ∙)   (suc m) l = pickTm (l == m) (var vz) (wk (lvlAt Γ m l))

lvl : (Γ : Cx) → ℕ → RTm Γ
lvl Γ = lvlAt Γ (len Γ)

------------------------------------------------------------------------
-- 8. TYPES (`_⟶ᵀ_`, `Algorithm/Eval.headᵀ`).  Terms never contain types,
--    so this is a second layer over the term evaluator, not mutual with it.
------------------------------------------------------------------------

data TVal : Set
data TClo : Set
data TClo₂ : Set

data TClo where
  tclo    : Env Γ → RTy (Γ ∙) → TClo
  tcloK   : TVal → TClo                  -- x ↦ A               (Hom-U: El (wk d))
  tcloEl  : Clo → TClo                   -- x ↦ El (d x)        (El-⌜Π⌝, El-⌜Σ⌝)
  tcloHom : TClo → Val → Val → TClo      -- x ↦ Hom (B x) (f x) (g x)              (Hom-Π)
  tcloDIh : Val → TClo₂ → Val → Val → TClo   -- x ↦ DIh D M C (snd p)            (DIh-ρ)

data TClo₂ where
  tclo₂ : Env Γ → RTy ((Γ ∙) ∙) → TClo₂

data TVal where
  tbase tU tUnit tNat : TVal
  tΠ tΣ : TVal → TClo → TVal
  tEl   : Val → TVal
  tHom tId : TVal → Val → Val → TVal
  tIMu  : Val → Val → Val → TVal
  tDesc : Val → TVal
  tDIh  : Val → TClo₂ → Val → Val → TVal
  tFin  : Val → TVal
  -- a type closure applied, when the fuel ran out (sound: read as the
  --   substitution it stands for)
  tinst  : TClo → Val → TVal
  tinst₂ : TClo₂ → Val → Val → TVal

-- what `Hom` inspects of its ambient
data TyV : TVal → Set where
  tvNat   : TyV tNat
  tvU     : TyV tU
  tvΠ     : (A : TVal) (B : TClo) → TyV (tΠ A B)
  tvOther : (A : TVal) → TyV A

tyV : (A : TVal) → TyV A
tyV tNat     = tvNat
tyV tU       = tvU
tyV (tΠ A B) = tvΠ A B
tyV A        = tvOther A

-- reading a type value
⌊_⌋ᵀ  : TVal → Lv Δ → RTy Δ
⌊_⌋ᵀᶜ : TClo → Lv Δ → RTy (Δ ∙)
⌊_⌋ᵀ² : TClo₂ → Lv Δ → RTy ((Δ ∙) ∙)

⌊ tclo ρ B ⌋ᵀᶜ        L = subTy (extS (⌊ ρ ⌋ᵉ L)) B
⌊ tcloK A ⌋ᵀᶜ         L = renTy vs (⌊ A ⌋ᵀ L)
⌊ tcloEl d ⌋ᵀᶜ        L = El (⌊ d ⌋ᶜ L)
⌊ tcloHom B f g ⌋ᵀᶜ   L = Hom (⌊ B ⌋ᵀᶜ L) (app (wk (⌊ f ⌋ L)) (var vz)) (app (wk (⌊ g ⌋ L)) (var vz))
⌊ tcloDIh D M C p ⌋ᵀᶜ L = DIh (wk (⌊ D ⌋ L)) (renTy (extR (extR vs)) (⌊ M ⌋ᵀ² L)) (wk (⌊ C ⌋ L)) (snd (wk (⌊ p ⌋ L)))
⌊ tclo₂ ρ M ⌋ᵀ²       L = subTy (extS (extS (⌊ ρ ⌋ᵉ L))) M

⌊ tbase ⌋ᵀ          L = base
⌊ tU ⌋ᵀ             L = U
⌊ tUnit ⌋ᵀ          L = Unit
⌊ tNat ⌋ᵀ           L = Nat
⌊ tΠ A B ⌋ᵀ         L = Π (⌊ A ⌋ᵀ L) (⌊ B ⌋ᵀᶜ L)
⌊ tΣ A B ⌋ᵀ         L = Σ' (⌊ A ⌋ᵀ L) (⌊ B ⌋ᵀᶜ L)
⌊ tEl c ⌋ᵀ          L = El (⌊ c ⌋ L)
⌊ tHom A a b ⌋ᵀ     L = Hom (⌊ A ⌋ᵀ L) (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ tId A a b ⌋ᵀ      L = Id (⌊ A ⌋ᵀ L) (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ tIMu I D i ⌋ᵀ     L = IMu (⌊ I ⌋ L) (⌊ D ⌋ L) (⌊ i ⌋ L)
⌊ tDesc I ⌋ᵀ        L = Desc (⌊ I ⌋ L)
⌊ tDIh D M C p ⌋ᵀ   L = DIh (⌊ D ⌋ L) (⌊ M ⌋ᵀ² L) (⌊ C ⌋ L) (⌊ p ⌋ L)
⌊ tFin t ⌋ᵀ         L = Fin (⌊ t ⌋ L)
⌊ tinst c v ⌋ᵀ      L = subTy (single (⌊ v ⌋ L)) (⌊ c ⌋ᵀᶜ L)
⌊ tinst₂ c j t ⌋ᵀ   L = subTy (single (⌊ t ⌋ L)) (subTy (extS (single (⌊ j ⌋ L))) (⌊ c ⌋ᵀ² L))

