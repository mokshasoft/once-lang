-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE ENVIRONMENT EVALUATOR (PLAN-EVAL E0, D080).
--                      UNTRUSTED: nothing certified rests on it yet.
--
-- ★ WHAT IT IS.  Untyped normalisation by evaluation over erased kernel
--   terms (`RTm` holds no `RTy`, so terms evaluate on their own):
--   · a CLOSURE is a body with its environment; a variable is a LOOKUP.
--     No `subTm` is ever built — the cost PLAN-BIDI §3g measured (every
--     β leaving an unshared substitution tower) cannot arise.
--   · free variables are de Bruijn LEVELS, so a value means the same
--     thing under any extension of the context: no renaming action.
--   · δ is LAZY: `ref d b` is the atom `vref d b`, unfolded only where a
--     rule needs to see a constructor (`force`).
--   · the computation rules are EXACTLY `Algorithm/Eval.head` (the one
--     place the rules live as a function), clause for clause, as "smart"
--     eliminators on values.  Where a rule's right-hand side introduces a
--     binder of its own (`hrefl-pw`, `tr-pw`, `dpay-σ`, `dpay-ρ`), the
--     closure is DEFUNCTIONALISED: a `Clo` constructor per rule.
--
-- ★ IT IS THE CATEGORICAL ABSTRACT MACHINE, seen from the λ side: an
--   environment is a product, a closure the exponential transpose, a
--   variable a projection (ROADMAP §1).
--
-- ★ FUEL.  Untyped evaluation may diverge (Ω), so every non-structural
--   call (a closure instantiated, a reference unfolded, a value
--   re-examined) spends one unit; structural recursion on the term does
--   not.  Fuel exhausted ⇒ the value is left stuck — so a test that runs
--   out shows a non-normal readback, never a wrong "equal".
--
-- ★ DEPTH.  `n` is the number of levels in scope.  Only `tr` needs it:
--   its rules inspect the MOTIVE's body (`⌜Hom⌝ c a (var vz)`, `var vz`),
--   so the motive is instantiated at the fresh level `n`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.NbE where
open import Agda.Builtin.Nat using ( zero; suc; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Variance using ( pwBody; pwShift )
open import DirectedHoTT.Spec.Typing using ( single )

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
  vref   : ℕ → RTm ε → Val

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
  isRef  : (d : ℕ) (b : RTm ε) → RefV (vref d b)
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
refV (vref d b) = isRef d b
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
-- The evaluator's signatures (one mutual block).
------------------------------------------------------------------------

eval  : ℕ → ℕ → Env Γ → RTm Γ → Val
force : ℕ → Val → Val
forceR : ℕ → {v : Val} → RefV v → Val
inst  : ℕ → ℕ → Clo → Val → Val
inst₂ : ℕ → ℕ → Clo₂ → Val → Val → Val
trPwView : ℕ → ℕ → Clo → Maybe TrPwV
tpvH  : ℕ → ℕ → {h : Val} → HomV h → Maybe TrPwV
tpvL  : ℕ → Val → Val → Bool → Maybe TrPwV
tpvS  : Val → (c : Val) → Maybe (PwSpine c) → Maybe TrPwV
trPwN : ℕ → ℕ → Clo → Clo → Clo → Val → Val → Maybe TrPwV → Val
trPwI : ℕ → ℕ → Clo → Clo → Clo → Val → Val → {h : Val} → HomV h → Val
trPwK : ℕ → ℕ → Clo → Clo → Val → Val → Val → Val → Val
trPwS : ℕ → ℕ → Clo → Clo → Val → Val → Val → {c : Val} → Maybe (PwSpine c) → Val

vApp    : ℕ → ℕ → Val → Val → Val
appF    : ℕ → ℕ → {f : Val} → LamV f → Val → Val
vFst vSnd : ℕ → Val → Val
fstF sndF : {p : Val} → PairV p → Val
vPsplit : ℕ → ℕ → Clo₂ → Val → Val
psplitF : ℕ → ℕ → Clo₂ → {p : Val} → PairV p → Val
vNatrec : ℕ → ℕ → Val → Clo₂ → Val → Val
natrecF : ℕ → ℕ → Val → Clo₂ → {t : Val} → NatV t → Val
vFcase  : ℕ → ℕ → Val → Val → Clo → Val
fcaseF  : ℕ → ℕ → {t : Val} → FinV t → Val → Clo → Val
vOrdtr  : ℕ → ℕ → Val → Val → Val → Val → Val → Val
ordA    : ℕ → ℕ → {a : Val} → NatV a → Val → Val → Val → Val → Val
ordB    : ℕ → ℕ → Val → {t u : Val} → NatV t → NatV u → Val → Val → Val
vHrefl  : ℕ → ℕ → Val → Val → Val
hreflP  : ℕ → ℕ → Val → Val → Val
hreflS  : ℕ → ℕ → (C : Val) → Maybe (PwSpine C) → Val → Val
hreflC  : ℕ → ℕ → {C : Val} → CodeV C → Val → Val
hreflNat : ℕ → ℕ → Val → Val
hreflN  : ℕ → ℕ → {s : Val} → NatV s → Val
vTr     : ℕ → ℕ → Clo → Val → Val → Val
trG     : ℕ → ℕ → Clo → Val → Val → Val → Val
trF     : ℕ → ℕ → Clo → {h : Val} → HomV h → {p : Val} → HreflV p → LamV p → VarV h → Val → Val
trJB    : Bool → Clo → Val → Val → Val
trPwC   : ℕ → ℕ → Clo → Clo → Val → Maybe TrPwV → Val
trPwP   : ℕ → ℕ → Clo → Clo → Val → Bool → Val
trTautP : ℕ → ℕ → ℕ → Clo → Clo → Val → Bool → Val
trTautB : ℕ → ℕ → Bool → Clo → Clo → Val → Val
trJ     : ℕ → {C : Val} → CodeV C → Bool
vAp     : ℕ → ℕ → Val → Clo → Val → Val
apF     : ℕ → ℕ → Val → Clo → {p : Val} → HreflV p → Val
apB     : ℕ → ℕ → Bool → Val → Clo → Val → Val → Val
vJsub   : ℕ → Clo → Val → Val → Val
jsubF   : Clo → {p : Val} → IdreflV p → Val → Val
vIelim  : ℕ → ℕ → Val → Val → Val → Val → Val
ielimF  : ℕ → ℕ → Val → Val → Val → {t : Val} → ConV t → Val
vDpay   : ℕ → Val → Val → Val → Val
dpayF   : ℕ → Val → Val → {C : Val} → DescV C → Val
vDih    : ℕ → ℕ → Val → Val → Val → Val → Val
dihF    : ℕ → ℕ → Val → Val → {C : Val} → DescV C → Val → Val
pwAtS   : ℕ → ℕ → {C : Val} → PwSpine C → Val → Val
pwForce : ℕ → Val → Val
pwForceH : ℕ → {C : Val} → HomV C → Val
-- `stkA?`/`stkC?` agree except at ⌜Nat⌝ (and recurse through ⌜Hom⌝ into
-- `stkA?` both); `nat` says what ⌜Nat⌝ answers.
stkV    : Bool → ℕ → Val → Bool
stkF    : Bool → ℕ → {C : Val} → CodeV C → Bool

------------------------------------------------------------------------
-- 3. Evaluation: structural on the term, at the same fuel.
------------------------------------------------------------------------

eval k n ρ (var x)           = lookup ρ x
eval k n ρ (lam t)           = vlam (clo ρ t)
eval k n ρ (app f u)         = vApp k n (eval k n ρ f) (eval k n ρ u)
eval k n ρ (pair a b)        = vpair (eval k n ρ a) (eval k n ρ b)
eval k n ρ (absurd c e)      = vabsurd (eval k n ρ c) (eval k n ρ e)
eval k n ρ (ordtr a t u p q) = vOrdtr k n (eval k n ρ a) (eval k n ρ t) (eval k n ρ u) (eval k n ρ p) (eval k n ρ q)
eval k n ρ (fst p)           = vFst k (eval k n ρ p)
eval k n ρ (snd p)           = vSnd k (eval k n ρ p)
eval k n ρ ⌜base⌝            = v⌜base⌝
eval k n ρ (⌜Π⌝ c d)         = v⌜Π⌝ (eval k n ρ c) (clo ρ d)
eval k n ρ (⌜Σ⌝ c d)         = v⌜Σ⌝ (eval k n ρ c) (clo ρ d)
eval k n ρ (⌜Hom⌝ c a b)     = v⌜Hom⌝ (eval k n ρ c) (eval k n ρ a) (eval k n ρ b)
eval k n ρ (hrefl c t)       = vHrefl k n (eval k n ρ c) (eval k n ρ t)
eval k n ρ (tr d p e)        = vTr k n (clo ρ d) (eval k n ρ p) (eval k n ρ e)
eval k n ρ (ap c b p)        = vAp k n (eval k n ρ c) (clo ρ b) (eval k n ρ p)
eval k n ρ (⌜Id⌝ c a b)      = v⌜Id⌝ (eval k n ρ c) (eval k n ρ a) (eval k n ρ b)
eval k n ρ (idrefl c t)      = vidrefl (eval k n ρ c) (eval k n ρ t)
eval k n ρ (jsub d p e)      = vJsub k (clo ρ d) (eval k n ρ p) (eval k n ρ e)
eval k n ρ unit              = vunit
eval k n ρ nzero             = vnzero
eval k n ρ (nsuc t)          = vnsuc (eval k n ρ t)
eval k n ρ (natrec z s t)    = vNatrec k n (eval k n ρ z) (clo₂ ρ s) (eval k n ρ t)
eval k n ρ (con p)           = vcon (eval k n ρ p)
eval k n ρ (ielim D i e t)   = vIelim k n (eval k n ρ D) (eval k n ρ i) (eval k n ρ e) (eval k n ρ t)
eval k n ρ dι                = vdι
eval k n ρ (dσ S f)          = vdσ (eval k n ρ S) (eval k n ρ f)
eval k n ρ (dρ j C)          = vdρ (eval k n ρ j) (eval k n ρ C)
eval k n ρ (dpay I D C)      = vDpay k (eval k n ρ I) (eval k n ρ D) (eval k n ρ C)
eval k n ρ (dih D e C p)     = vDih k n (eval k n ρ D) (eval k n ρ e) (eval k n ρ C) (eval k n ρ p)
eval k n ρ fzero             = vfzero
eval k n ρ (fsuc t)          = vfsuc (eval k n ρ t)
eval k n ρ (fcase t a b)     = vFcase k n (eval k n ρ t) (eval k n ρ a) (clo ρ b)
eval k n ρ (fcase0 t)        = vfcase0 (eval k n ρ t)
eval k n ρ (psplit b p)      = vPsplit k n (clo₂ ρ b) (eval k n ρ p)
eval k n ρ ⌜Nat⌝             = v⌜Nat⌝
eval k n ρ (⌜IMu⌝ I D i)     = v⌜IMu⌝ (eval k n ρ I) (eval k n ρ D) (eval k n ρ i)
eval k n ρ (⌜Fin⌝ t)         = v⌜Fin⌝ (eval k n ρ t)
eval k n ρ ⌜Unit⌝            = v⌜Unit⌝
eval k n ρ (ref d b)         = vref d b

-- ★ lazy δ: unfold references at the head, and only there
force zero    v = v
force (suc k) v = forceR k (refV v)
forceR k (isRef d b)    = force k (eval k 0 [] b)
forceR k (notRef v)     = v

------------------------------------------------------------------------
-- 4. Closures.  Instantiation is where fuel is spent.
------------------------------------------------------------------------

inst zero    n c                  v = vapp (vlam c) v
inst (suc k) n (clo ρ t)          v = eval k n (ρ , v) t
inst (suc k) n (cloK w)           v = w
inst (suc k) n (cloHrefl C sp s)  v = vHrefl k n (pwAtS k n sp v) (vApp k n s v)
inst (suc k) n (cloDpay I D f)    v = vDpay k I D (vApp k n f v)
inst (suc k) n (cloHomTo C A)     v = v⌜Hom⌝ C A v
inst (suc k) n self@(cloTrPw d f e) y = trPwN k n self d f e y (trPwView k n d)

-- ★ tr-pw's inspection: the motive at the fresh level m, its head ⌜Hom⌝
--   with endpoint exactly that level, its ambient pw-normal after forcing
trPwView k m d = tpvH k m (homV (force k (inst k (suc m) d (vvar m))))
tpvH k m (isHom c a mm) = tpvL k c a (isLvl m (varV mm))
tpvH k m (notHom _)     = nothing
tpvL k c a true  = tpvS a (pwForce k c) (pwSpine? (pwForce k c))
tpvL k c a false = nothing
tpvS a c (just sp) = just (trpw c sp a)
tpvS a c nothing   = nothing


-- instantiated only if the guard holds at THIS fuel (else the β-redex)
trPwN k n self d f e y (just _) = trPwI k n self d f e y (homV (force k (inst k n d y)))
trPwN k n self d f e y nothing  = vapp (vlam self) y

-- `tr-pw`'s body at y: the motive re-inspected at y; pw-normal ⇒ the
--   right-hand side, else the β-redex itself (sound at any fuel)
trPwI k n self d f e y (isHom c a _) = trPwK k n self f e y a (pwForce k c)
trPwI k n self d f e y (notHom _)    = vapp (vlam self) y
trPwK k n self f e y a c = trPwS k n self f e y a (pwSpine? c)
trPwS k n self f e y a (just sp) = vTr k n (cloHomTo (pwAtS k n sp y) (vApp k n a y)) (inst k n f y) (vApp k n e y)
trPwS k n self f e y a nothing   = vapp (vlam self) y

inst₂ zero    n (clo₂ ρ t) x y = vpsplit (clo₂ ρ t) (vpair x y)
inst₂ (suc k) n (clo₂ ρ t) x y = eval k n ((ρ , x) , y) t

------------------------------------------------------------------------
-- 5. The rules, as smart eliminators (`Algorithm/Eval.head`'s order).
------------------------------------------------------------------------

vApp k n f u = appF k n (lamV (force k f)) u
appF zero    n (isLam c)      u = vapp (vlam c) u
appF zero    n (notLam f)     u = vapp f u
appF (suc k) n (isLam c)      u = inst k n c u                  -- β
appF (suc k) n (notLam f)     u = vapp f u

vFst k p = fstF (pairV (force k p))
vSnd k p = sndF (pairV (force k p))
fstF (isPair a b) = a                                           -- βfst
fstF (notPair p)  = vfst p
sndF (isPair a b) = b                                           -- βsnd
sndF (notPair p)  = vsnd p

vPsplit k n b p = psplitF k n b (pairV (force k p))
psplitF zero    n b (isPair x y)   = vpsplit b (vpair x y)
psplitF zero    n b (notPair p)    = vpsplit b p
psplitF (suc k) n b (isPair x y)   = inst₂ k n b x y            -- psplit-β
psplitF (suc k) n b (notPair p)    = vpsplit b p

vNatrec k n z s t = natrecF k n z s (natV (force k t))
natrecF k       n z s isZero    = z                             -- natrec-zero
natrecF zero    n z s (isSuc t) = vnatrec z s (vnsuc t)
natrecF (suc k) n z s (isSuc t) = inst₂ k n s t (vNatrec k n z s t)   -- natrec-suc
natrecF k       n z s (notNat t) = vnatrec z s t

vFcase k n t a b = fcaseF k n (finV (force k t)) a b
fcaseF k       n isFz       a b = a                             -- fcase-z
fcaseF zero    n (isFs t)   a b = vfcase (vfsuc t) a b
fcaseF (suc k) n (isFs t)   a b = inst k n b t                  -- fcase-s
fcaseF k       n (notFin t) a b = vfcase t a b

vOrdtr k n a t u p q = ordA k n (natV (force k a)) (force k t) (force k u) p q
ordA k n isZero      t u p q = vunit                            -- ordtr-z
ordA k n (isSuc a)   t u p q = ordB k n a (natV t) (natV u) p q
ordA k n (notNat a)  t u p q = vordtr a t u p q
ordB k       n a isZero    isZero    p q = p                    -- ordtr-szz
ordB k       n a (isSuc t) isZero    p q = q                    -- ordtr-ssz
ordB k       n a isZero    (isSuc u) p q = vabsurd (v⌜Hom⌝ v⌜Nat⌝ a u) p   -- ordtr-szs
ordB zero    n a (isSuc t) (isSuc u) p q = vordtr (vnsuc a) (vnsuc t) (vnsuc u) p q
ordB (suc k) n a (isSuc t) (isSuc u) p q = vOrdtr k n a t u p q -- ordtr-sss
ordB k       n a (notNat t) isZero     p q = vordtr (vnsuc a) t vnzero p q
ordB k       n a (notNat t) (isSuc u)  p q = vordtr (vnsuc a) t (vnsuc u) p q
ordB k       n a (notNat t) (notNat u) p q = vordtr (vnsuc a) t u p q
ordB k       n a isZero     (notNat u) p q = vordtr (vnsuc a) vnzero u p q
ordB k       n a (isSuc t)  (notNat u) p q = vordtr (vnsuc a) (vnsuc t) u p q

-- hrefl: pw-able code ⇒ pointwise (hrefl-pw); else the order's
-- reflexivity at ⌜Nat⌝ (hrefl-Nat-z/s); else stuck.
vHrefl k n C s = hreflP k n (pwForce k C) s
hreflP k n C s = hreflS k n C (pwSpine? C) s
hreflS k n C (just sp) s = vlam (cloHrefl C sp s)               -- hrefl-pw
hreflS k n C nothing   s = hreflC k n (codeV C) s
hreflC k n cNat           s = hreflNat k n s
hreflC k n cbase          s = vhrefl v⌜base⌝ s
hreflC k n (cΠ c d)       s = vhrefl (v⌜Π⌝ c d) s
hreflC k n (cΣ c d)       s = vhrefl (v⌜Σ⌝ c d) s
hreflC k n (cHom c a b)   s = vhrefl (v⌜Hom⌝ c a b) s
hreflC k n (cId c a b)    s = vhrefl (v⌜Id⌝ c a b) s
hreflC k n cUnit          s = vhrefl v⌜Unit⌝ s
hreflC k n (cIMu I D i)   s = vhrefl (v⌜IMu⌝ I D i) s
hreflC k n (cFin t)       s = vhrefl (v⌜Fin⌝ t) s
hreflC k n (cOther C)     s = vhrefl C s
hreflNat zero    n s = vhrefl v⌜Nat⌝ s
hreflNat (suc k) n s = hreflN k n (natV (force k s))
hreflN k n isZero      = vunit                                  -- hrefl-Nat-z
hreflN k n (isSuc m)   = hreflNat k n m                         -- hrefl-Nat-s
hreflN k n (notNat s)  = vhrefl v⌜Nat⌝ s

-- tr: the motive is inspected at the fresh level n
vTr zero    n d p e = vtr d p e
vTr (suc k) n d p e = trG k n d (force k (inst k (suc n) d (vvar n))) (force k p) e
-- (an argument, not a `where`: a `where` binding is re-evaluated per use)
trG k n d h p e = trF k n d (homV h) (hreflV p) (lamV p) (varV h) e
trF k n d (isHom c a m) (isHrefl C s) w        v e = trJB (trJ k (codeV (force k C))) d (vhrefl C s) e   -- tr-J-*
trF k n d (isHom c a m) (notHrefl _) (isLam f) v e = trPwP k n d f e (isTrPw f)   -- tr-pw
trF k n d (isHom c a m) (notHrefl _) (notLam p) v e = vtr d p e
trF k n d (notHom _) w (isLam f) (isVar l) e = trTautP k n l d f e (isTrPw f)   -- tr-taut (and β)
trF k n d (notHom _) w (isLam f) (notVar _) e = vtr d (vlam f) e
trF k n d (notHom _) w (notLam p) v e = vtr d p e

trJB true  d p e = e
trJB false d p e = vtr d p e
trPwP k n d f e true  = vtr d (vlam f) e
trPwP k n d f e false = trPwC k n d f e (trPwView k n d)
trTautP k n l d f e true  = vtr d (vlam f) e
trTautP k n l d f e false = trTautB k n (l == n) d f e
trPwC k n d f e (just _) = vlam (cloTrPw d f e)
trPwC k n d f e nothing  = vtr d (vlam f) e
trTautB k n true  d f e = inst k n f e
trTautB k n false d f e = vtr d (vlam f) e

-- which codes make `tr (⌜Hom⌝ ⋯) (hrefl C s) e ⟶ e`
trJ k cbase          = true
trJ k (cΣ _ _)       = true
trJ k cUnit          = true
trJ k (cId _ _ _)    = true
trJ k (cIMu _ _ _)   = true
trJ k (cFin _)       = true
trJ k (cHom c₁ _ _)  = stkV true k c₁                           -- tr-J-Hom (stkA?)
trJ k (cΠ _ _)       = false
trJ k cNat           = false
trJ k (cOther _)     = false

vAp k n cB b p = apF k n cB b (hreflV (force k p))
apF zero    n cB b (isHrefl c₁ s)     = vap cB b (vhrefl c₁ s)
apF zero    n cB b (notHrefl p)       = vap cB b p
apF (suc k) n cB b (isHrefl c₁ s)     = apB k n (stkV false k c₁) cB b c₁ s
apF (suc k) n cB b (notHrefl p)       = vap cB b p
apB k n true  cB b c₁ s = vHrefl k n cB (inst k n b s)          -- ap-J (stkC?)
apB k n false cB b c₁ s = vap cB b (vhrefl c₁ s)

vJsub k d p e = jsubF d (idreflV (force k p)) e
jsubF d (isIdrefl c s) e = e                                    -- jsub-refl
jsubF d (notIdrefl p)  e = vjsub d p e

vIelim k n D i e t = ielimF k n D i e (conV (force k t))
ielimF zero    n D i e (isCon p)  = vielim D i e (vcon p)
ielimF zero    n D i e (notCon t) = vielim D i e t
ielimF (suc k) n D i e (isCon p) =                              -- ι
  vApp k n (vApp k n (vApp k n e i) p) (vDih k n D e (vApp k n D i) p)
ielimF (suc k) n D i e (notCon t) = vielim D i e t

vDpay k I D C = dpayF k I D (descV (force k C))
dpayF k       I D isDι       = v⌜Unit⌝                          -- dpay-ι
dpayF k       I D (isDσ S f) = v⌜Σ⌝ S (cloDpay I D f)           -- dpay-σ
dpayF zero    I D (isDρ j C) = vdpay I D (vdρ j C)
dpayF (suc k) I D (isDρ j C) = v⌜Σ⌝ (v⌜IMu⌝ I D j) (cloK (vDpay k I D C))   -- dpay-ρ: a constant body
dpayF k       I D (notDesc C) = vdpay I D C

vDih k n D e C p = dihF k n D e (descV (force k C)) p
dihF k       n D e isDι       p = vunit                         -- dih-ι
dihF zero    n D e (isDσ S f) p = vdih D e (vdσ S f) p
dihF (suc k) n D e (isDσ S f) p = vDih k n D e (vApp k n f (vFst k p)) (vSnd k p)   -- dih-σ
dihF zero    n D e (isDρ j C) p = vdih D e (vdρ j C) p
dihF (suc k) n D e (isDρ j C) p =                               -- dih-ρ
  vpair (vIelim k n D j e (vFst k p)) (vDih k n D e C (vSnd k p))
dihF k n D e (notDesc C) p = vdih D e C p

-- pwBody, at a level, along a SPINE: structural, no forcing
pwAtS k n (spΠ c d)      x = inst k n d x
pwAtS k n (spHom sp a b) x = v⌜Hom⌝ (pwAtS k n sp x) (vApp k n a x) (vApp k n b x)

-- force a code's head, and along a ⌜Hom⌝ spine its ambient
pwForce zero    C = C
pwForce (suc k) C = pwForceH k (homV (force k C))
pwForceH k (isHom C a b) = v⌜Hom⌝ (pwForce k C) a b
pwForceH k (notHom v)    = v

stkV nat k C = stkF nat k (codeV (force k C))
stkF nat k       cbase          = true
stkF nat k       (cΣ _ _)       = true
stkF nat k       (cId _ _ _)    = true
stkF nat k       cUnit          = true
stkF nat k       (cFin _)       = true
stkF nat k       cNat           = nat
stkF nat k       (cIMu _ _ _)   = true
stkF nat zero    (cHom C _ _)   = false
stkF nat (suc k) (cHom C _ _)   = stkV true k C
stkF nat k       (cΠ _ _)       = false
stkF nat k       (cOther _)     = false

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
⌊ vref d b ⌋         L = ref d b


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

rbAt : Bool → ℕ → (Γ : Cx) → ℕ → Val → RTm Γ
rbᶜAt : Bool → ℕ → (Γ : Cx) → ℕ → Clo → RTm (Γ ∙)
rbLamAt : Bool → ℕ → (Γ : Cx) → ℕ → Clo → RTm Γ
rbTrPwAt : Bool → ℕ → (Γ : Cx) → ℕ → Clo → Clo → Clo → Val → Maybe TrPwV → RTm Γ
rb₂At : Bool → ℕ → (Γ : Cx) → ℕ → Clo₂ → RTm ((Γ ∙) ∙)

rbAt u k Γ n (vvar l)        = lvlAt Γ n l
rbAt u k Γ n (vlam c)        = rbLamAt u k Γ n c
rbAt u k Γ n (vapp f a)      = app (rbAt u k Γ n f) (rbAt u k Γ n a)
rbAt u k Γ n (vpair a b)     = pair (rbAt u k Γ n a) (rbAt u k Γ n b)
rbAt u k Γ n (vabsurd c e)   = absurd (rbAt u k Γ n c) (rbAt u k Γ n e)
rbAt u k Γ n (vordtr a t v p q) = ordtr (rbAt u k Γ n a) (rbAt u k Γ n t) (rbAt u k Γ n v) (rbAt u k Γ n p) (rbAt u k Γ n q)
rbAt u k Γ n (vfst p)        = fst (rbAt u k Γ n p)
rbAt u k Γ n (vsnd p)        = snd (rbAt u k Γ n p)
rbAt u k Γ n v⌜base⌝         = ⌜base⌝
rbAt u k Γ n (v⌜Π⌝ c d)      = ⌜Π⌝ (rbAt u k Γ n c) (rbᶜAt u k Γ n d)
rbAt u k Γ n (v⌜Σ⌝ c d)      = ⌜Σ⌝ (rbAt u k Γ n c) (rbᶜAt u k Γ n d)
rbAt u k Γ n (v⌜Hom⌝ c a b)  = ⌜Hom⌝ (rbAt u k Γ n c) (rbAt u k Γ n a) (rbAt u k Γ n b)
rbAt u k Γ n (vhrefl c t)    = hrefl (rbAt u k Γ n c) (rbAt u k Γ n t)
rbAt u k Γ n (vtr d p e)     = tr (rbᶜAt u k Γ n d) (rbAt u k Γ n p) (rbAt u k Γ n e)
rbAt u k Γ n (vap c b p)     = ap (rbAt u k Γ n c) (rbᶜAt u k Γ n b) (rbAt u k Γ n p)
rbAt u k Γ n (v⌜Id⌝ c a b)   = ⌜Id⌝ (rbAt u k Γ n c) (rbAt u k Γ n a) (rbAt u k Γ n b)
rbAt u k Γ n (vidrefl c t)   = idrefl (rbAt u k Γ n c) (rbAt u k Γ n t)
rbAt u k Γ n (vjsub d p e)   = jsub (rbᶜAt u k Γ n d) (rbAt u k Γ n p) (rbAt u k Γ n e)
rbAt u k Γ n vunit           = unit
rbAt u k Γ n vnzero          = nzero
rbAt u k Γ n (vnsuc t)       = nsuc (rbAt u k Γ n t)
rbAt u k Γ n (vnatrec z s t) = natrec (rbAt u k Γ n z) (rb₂At u k Γ n s) (rbAt u k Γ n t)
rbAt u k Γ n (vcon p)        = con (rbAt u k Γ n p)
rbAt u k Γ n (vielim D i e t) = ielim (rbAt u k Γ n D) (rbAt u k Γ n i) (rbAt u k Γ n e) (rbAt u k Γ n t)
rbAt u k Γ n vdι             = dι
rbAt u k Γ n (vdσ S f)       = dσ (rbAt u k Γ n S) (rbAt u k Γ n f)
rbAt u k Γ n (vdρ j C)       = dρ (rbAt u k Γ n j) (rbAt u k Γ n C)
rbAt u k Γ n (vdpay I D C)   = dpay (rbAt u k Γ n I) (rbAt u k Γ n D) (rbAt u k Γ n C)
rbAt u k Γ n (vdih D e C p)  = dih (rbAt u k Γ n D) (rbAt u k Γ n e) (rbAt u k Γ n C) (rbAt u k Γ n p)
rbAt u k Γ n vfzero          = fzero
rbAt u k Γ n (vfsuc t)       = fsuc (rbAt u k Γ n t)
rbAt u k Γ n (vfcase t a b)  = fcase (rbAt u k Γ n t) (rbAt u k Γ n a) (rbᶜAt u k Γ n b)
rbAt u k Γ n (vfcase0 t)     = fcase0 (rbAt u k Γ n t)
rbAt u k Γ n (vpsplit b p)   = psplit (rb₂At u k Γ n b) (rbAt u k Γ n p)
rbAt u k Γ n v⌜Nat⌝          = ⌜Nat⌝
rbAt u k Γ n v⌜Unit⌝         = ⌜Unit⌝
rbAt u k Γ n (v⌜IMu⌝ I D i)  = ⌜IMu⌝ (rbAt u k Γ n I) (rbAt u k Γ n D) (rbAt u k Γ n i)
rbAt u k Γ n (v⌜Fin⌝ t)      = ⌜Fin⌝ (rbAt u k Γ n t)
rbAt false k Γ n (vref d b)  = ref d b
rbAt true zero Γ n (vref d b) = ref d b
rbAt true (suc k) Γ n (vref d b) = rbAt true k Γ n (eval k 0 [] b)

-- a λ-value: λ of its body — except tr-pw's, whose guard is re-checked
--   (at this fuel): the λ of its body when it holds, else the redex
rbLamAt u k Γ n c@(clo _ _)        = lam (rbᶜAt u k Γ n c)
rbLamAt u k Γ n c@(cloK _)         = lam (rbᶜAt u k Γ n c)
rbLamAt u k Γ n c@(cloHrefl _ _ _) = lam (rbᶜAt u k Γ n c)
rbLamAt u k Γ n c@(cloDpay _ _ _)  = lam (rbᶜAt u k Γ n c)
rbLamAt u k Γ n c@(cloHomTo _ _)   = lam (rbᶜAt u k Γ n c)
rbLamAt u k Γ n c@(cloTrPw d f e)  = rbTrPwAt u k Γ n c d f e (trPwView k n d)
rbTrPwAt u k Γ n c d f e (just _) = lam (rbᶜAt u k Γ n c)
rbTrPwAt u k Γ n c d f e nothing  = tr (rbᶜAt u k Γ n d) (lam (rbᶜAt u k Γ n f)) (rbAt u k Γ n e)

rbᶜAt u zero    Γ n c = ⌊ c ⌋ᶜ (lvlAt Γ n)
rbᶜAt u (suc k) Γ n c = rbAt u k (Γ ∙) (suc n) (inst k (suc n) c (vvar n))

rb₂At u zero    Γ n c = ⌊ c ⌋² (lvlAt Γ n)
rb₂At u (suc k) Γ n c = rbAt u k ((Γ ∙) ∙) (suc (suc n))
  (inst₂ k (suc (suc n)) c (vvar n) (vvar (suc n)))


-- ★ the readback with the context length computed ONCE (passed down, as
--   `lvlAt`): `len` per variable and per binder was 15% of PwCore's
--   checking (profiled 2026-10-06).  `rb u k Γ` is `rbAt u k Γ (len Γ)`,
--   and `len (Γ ∙)` is `suc (len Γ)`, so every clause still holds
--   DEFINITIONALLY at the old names.
rb  : Bool → ℕ → (Γ : Cx) → Val → RTm Γ
rb u k Γ = rbAt u k Γ (len Γ)
rbᶜ : Bool → ℕ → (Γ : Cx) → Clo → RTm (Γ ∙)
rbᶜ u k Γ = rbᶜAt u k Γ (len Γ)
rbLam : Bool → ℕ → (Γ : Cx) → Clo → RTm Γ
rbLam u k Γ = rbLamAt u k Γ (len Γ)
rbTrPw : Bool → ℕ → (Γ : Cx) → Clo → Clo → Clo → Val → Maybe TrPwV → RTm Γ
rbTrPw u k Γ = rbTrPwAt u k Γ (len Γ)
rb₂ : Bool → ℕ → (Γ : Cx) → Clo₂ → RTm ((Γ ∙) ∙)
rb₂ u k Γ = rb₂At u k Γ (len Γ)

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

evalᵀ  : ℕ → ℕ → Env Γ → RTy Γ → TVal
instᵀ  : ℕ → ℕ → TClo → Val → TVal
instᵀ₂ : ℕ → ℕ → TClo₂ → Val → Val → TVal
tElS   : ℕ → ℕ → Val → TVal
tElF   : ℕ → ℕ → {c : Val} → CodeV c → TVal
tHomS  : ℕ → ℕ → TVal → Val → Val → TVal
tHomF  : ℕ → ℕ → {A : TVal} → TyV A → Val → Val → TVal
tHomNat : ℕ → Val → Val → TVal
tHomA  : ℕ → {a : Val} → NatV a → Val → TVal
tHomB  : ℕ → Val → {b : Val} → NatV b → TVal
tDIhS  : ℕ → ℕ → Val → TClo₂ → Val → Val → TVal
tDIhF  : ℕ → ℕ → Val → TClo₂ → {C : Val} → DescV C → Val → TVal

evalᵀ k n ρ base          = tbase
evalᵀ k n ρ U             = tU
evalᵀ k n ρ (Π A B)       = tΠ (evalᵀ k n ρ A) (tclo ρ B)
evalᵀ k n ρ (Σ' A B)      = tΣ (evalᵀ k n ρ A) (tclo ρ B)
evalᵀ k n ρ (El c)        = tElS k n (eval k n ρ c)
evalᵀ k n ρ (Hom A a b)   = tHomS k n (evalᵀ k n ρ A) (eval k n ρ a) (eval k n ρ b)
evalᵀ k n ρ Unit          = tUnit
evalᵀ k n ρ Nat           = tNat
evalᵀ k n ρ (Id A a b)    = tId (evalᵀ k n ρ A) (eval k n ρ a) (eval k n ρ b)
evalᵀ k n ρ (IMu I D i)   = tIMu (eval k n ρ I) (eval k n ρ D) (eval k n ρ i)
evalᵀ k n ρ (Desc I)      = tDesc (eval k n ρ I)
evalᵀ k n ρ (DIh D M C p) = tDIhS k n (eval k n ρ D) (tclo₂ ρ M) (eval k n ρ C) (eval k n ρ p)
evalᵀ k n ρ (Fin t)       = tFin (eval k n ρ t)

instᵀ zero    n c                 v = tinst c v
instᵀ (suc k) n (tclo ρ B)        v = evalᵀ k n (ρ , v) B
instᵀ (suc k) n (tcloK A)         v = A
instᵀ (suc k) n (tcloEl d)        v = tElS k n (inst k n d v)
instᵀ (suc k) n (tcloHom B f g)   v = tHomS k n (instᵀ k n B v) (vApp k n f v) (vApp k n g v)
instᵀ (suc k) n (tcloDIh D M C p) v = tDIhS k n D M C (vSnd k p)

instᵀ₂ zero    n c           j t = tinst₂ c j t
instᵀ₂ (suc k) n (tclo₂ ρ M) j t = evalᵀ k n ((ρ , j) , t) M

-- El of a code decodes it (El-⌜…⌝); a ⌜Hom⌝ code's decode may compute further
tElS k n c = tElF k n (codeV (force k c))
tElF k       n cbase        = tbase
tElF zero    n (cΠ c d)     = tEl (v⌜Π⌝ c d)
tElF (suc k) n (cΠ c d)     = tΠ (tElS k n c) (tcloEl d)
tElF zero    n (cΣ c d)     = tEl (v⌜Σ⌝ c d)
tElF (suc k) n (cΣ c d)     = tΣ (tElS k n c) (tcloEl d)
tElF zero    n (cHom c a b) = tEl (v⌜Hom⌝ c a b)
tElF (suc k) n (cHom c a b) = tHomS k n (tElS k n c) a b
tElF zero    n (cId c a b)  = tEl (v⌜Id⌝ c a b)
tElF (suc k) n (cId c a b)  = tId (tElS k n c) a b
tElF k       n cNat         = tNat
tElF k       n (cIMu I D i) = tIMu I D i
tElF k       n (cFin t)     = tFin t
tElF k       n cUnit        = tUnit
tElF k       n (cOther c)   = tEl c

-- Hom computes at Nat (the order), U (functions) and Π (pointwise)
tHomS k n A a b = tHomF k n (tyV A) a b
tHomF k       n tvNat     a b = tHomNat k a b
tHomF zero    n tvU       c d = tHom tU c d
tHomF (suc k) n tvU       c d = tΠ (tElS k n c) (tcloK (tElS k n d))         -- Hom-U
tHomF k       n (tvΠ A B) f g = tΠ A (tcloHom B f g)                         -- Hom-Π
tHomF k       n (tvOther A) a b = tHom A a b
tHomNat k a b = tHomA k (natV (force k a)) b
tHomA k isZero    b = tUnit                                                  -- Hom-Nat-z
tHomA k (isSuc m) b = tHomB k m (natV (force k b))
tHomA k (notNat a) b = tHom tNat a b
tHomB k       m isZero    = tbase                                            -- Hom-Nat-sz
tHomB zero    m (isSuc b) = tHom tNat (vnsuc m) (vnsuc b)
tHomB (suc k) m (isSuc b) = tHomNat k m b                                    -- Hom-Nat-ss
tHomB k       m (notNat b) = tHom tNat (vnsuc m) b

tDIhS k n D M C p = tDIhF k n D M (descV (force k C)) p
tDIhF k       n D M isDι       p = tUnit                                     -- DIh-ι
tDIhF zero    n D M (isDσ S f) p = tDIh D M (vdσ S f) p
tDIhF (suc k) n D M (isDσ S f) p = tDIhS k n D M (vApp k n f (vFst k p)) (vSnd k p)   -- DIh-σ
tDIhF zero    n D M (isDρ j C) p = tDIh D M (vdρ j C) p
tDIhF (suc k) n D M (isDρ j C) p =                                           -- DIh-ρ
  tΣ (instᵀ₂ k n M j (vFst k p)) (tcloDIh D M C p)
tDIhF k       n D M (notDesc C) p = tDIh D M C p

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

rbᵀAt : Bool → ℕ → (Γ : Cx) → ℕ → TVal → RTy Γ
rbᵀᶜAt : Bool → ℕ → (Γ : Cx) → ℕ → TClo → RTy (Γ ∙)
rbᵀ₂At : Bool → ℕ → (Γ : Cx) → ℕ → TClo₂ → RTy ((Γ ∙) ∙)

rbᵀAt u k Γ n tbase          = base
rbᵀAt u k Γ n tU             = U
rbᵀAt u k Γ n tUnit          = Unit
rbᵀAt u k Γ n tNat           = Nat
rbᵀAt u k Γ n (tΠ A B)       = Π (rbᵀAt u k Γ n A) (rbᵀᶜAt u k Γ n B)
rbᵀAt u k Γ n (tΣ A B)       = Σ' (rbᵀAt u k Γ n A) (rbᵀᶜAt u k Γ n B)
rbᵀAt u k Γ n (tEl c)        = El (rbAt u k Γ n c)
rbᵀAt u k Γ n (tHom A a b)   = Hom (rbᵀAt u k Γ n A) (rbAt u k Γ n a) (rbAt u k Γ n b)
rbᵀAt u k Γ n (tId A a b)    = Id (rbᵀAt u k Γ n A) (rbAt u k Γ n a) (rbAt u k Γ n b)
rbᵀAt u k Γ n (tIMu I D i)   = IMu (rbAt u k Γ n I) (rbAt u k Γ n D) (rbAt u k Γ n i)
rbᵀAt u k Γ n (tDesc I)      = Desc (rbAt u k Γ n I)
rbᵀAt u k Γ n (tDIh D M C p) = DIh (rbAt u k Γ n D) (rbᵀ₂At u k Γ n M) (rbAt u k Γ n C) (rbAt u k Γ n p)
rbᵀAt u k Γ n (tFin t)       = Fin (rbAt u k Γ n t)
rbᵀAt u zero    Γ n (tinst c v)    = ⌊ tinst c v ⌋ᵀ (lvlAt Γ n)
rbᵀAt u (suc k) Γ n (tinst c v)    = rbᵀAt u k Γ n (instᵀ k n c v)
rbᵀAt u zero    Γ n (tinst₂ c j t) = ⌊ tinst₂ c j t ⌋ᵀ (lvlAt Γ n)
rbᵀAt u (suc k) Γ n (tinst₂ c j t) = rbᵀAt u k Γ n (instᵀ₂ k n c j t)

rbᵀᶜAt u zero    Γ n c = ⌊ c ⌋ᵀᶜ (lvlAt Γ n)
rbᵀᶜAt u (suc k) Γ n c = rbᵀAt u k (Γ ∙) (suc n) (instᵀ k (suc n) c (vvar n))

rbᵀ₂At u zero    Γ n c = ⌊ c ⌋ᵀ² (lvlAt Γ n)
rbᵀ₂At u (suc k) Γ n c = rbᵀAt u k ((Γ ∙) ∙) (suc (suc n))
  (instᵀ₂ k (suc (suc n)) c (vvar n) (vvar (suc n)))


rbᵀ  : Bool → ℕ → (Γ : Cx) → TVal → RTy Γ
rbᵀ u k Γ = rbᵀAt u k Γ (len Γ)
rbᵀᶜ : Bool → ℕ → (Γ : Cx) → TClo → RTy (Γ ∙)
rbᵀᶜ u k Γ = rbᵀᶜAt u k Γ (len Γ)
rbᵀ₂ : Bool → ℕ → (Γ : Cx) → TClo₂ → RTy ((Γ ∙) ∙)
rbᵀ₂ u k Γ = rbᵀ₂At u k Γ (len Γ)

------------------------------------------------------------------------
-- 9. The entry points.
------------------------------------------------------------------------

-- the identity environment: variable i of Γ is its own level
-- (the length passed down, as `lvlAt`: `idEnv (Γ ∙)` is still
--  `idEnv Γ , vvar (len Γ)` definitionally)
idEnvAt : (Γ : Cx) → ℕ → Env Γ
idEnvAt ε     m       = []
idEnvAt (Γ ∙) zero    = idEnvAt Γ zero , vvar zero
idEnvAt (Γ ∙) (suc m) = idEnvAt Γ m , vvar m

idEnv : (Γ : Cx) → Env Γ
idEnv Γ = idEnvAt Γ (len Γ)

-- the value of an open term
⟦_⟧_ : RTm Γ → ℕ → Val
⟦_⟧_ {Γ} t k = eval k (len Γ) (idEnv Γ) t

-- the normal form, every reference unfolded (the kernel's)
nbe : ℕ → RTm Γ → RTm Γ
nbe {Γ} k t = rb true k Γ (⟦ t ⟧ k)

-- the normal form with references as atoms (lazy δ)
nbeᵃ : ℕ → RTm Γ → RTm Γ
nbeᵃ {Γ} k t = rb false k Γ (⟦ t ⟧ k)

-- the normal form of a type, every reference unfolded
nbeᵀ : ℕ → RTy Γ → RTy Γ
nbeᵀ {Γ} k A = rbᵀ true k Γ (evalᵀ k (len Γ) (idEnv Γ) A)
