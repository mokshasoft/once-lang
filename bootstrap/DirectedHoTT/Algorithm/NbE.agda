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
open import DirectedHoTT.Spec.Syntax

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 1. Values, closures, environments.
------------------------------------------------------------------------

data Val : Set
data Clo : Set
data Clo₂ : Set
data Env : Cx → Set

data Env where
  []  : Env ε
  _,_ : Env Γ → Val → Env (Γ ∙)

-- a body under ONE binder
data Clo where
  clo      : Env Γ → RTm (Γ ∙) → Clo
  -- the defunctionalised binders of the rules' right-hand sides
  cloK     : Val → Clo                   -- x ↦ v            (dpay-ρ: a weakened term)
  cloHrefl : Val → Val → Clo             -- x ↦ hrefl (pwBody C)[x] (s x)            (hrefl-pw)
  cloDpay  : Val → Val → Val → Clo       -- x ↦ dpay I D (f x)                       (dpay-σ)
  cloTrPw  : Clo → Clo → Val → Clo       -- y ↦ tr (z ↦ ⌜Hom⌝ ⋯) (f y) (e y)         (tr-pw)
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

lookup : Env Γ → Var Γ → Val
lookup (ρ , v) vz     = v
lookup (ρ , v) (vs x) = lookup ρ x

------------------------------------------------------------------------
-- 2. The guards (`Spec/Variance`'s `pw?`, `stkA?`, `stkC?`), on values.
--    They read only code HEADS; a reference in a head is unfolded.
------------------------------------------------------------------------

-- `stkA?`/`stkC?` agree except at ⌜Nat⌝ (and recurse through ⌜Hom⌝ into
-- `stkA?` both); `nat` says what ⌜Nat⌝ answers.
stkV : Bool → ℕ → Val → Bool

eval  : ℕ → ℕ → Env Γ → RTm Γ → Val
force : ℕ → Val → Val
inst  : ℕ → ℕ → Clo → Val → Val
inst₂ : ℕ → ℕ → Clo₂ → Val → Val → Val
pwV   : ℕ → Val → Bool
pwAt  : ℕ → ℕ → Val → Val → Val
vApp    : ℕ → ℕ → Val → Val → Val
vFst vSnd : ℕ → Val → Val
vPsplit : ℕ → ℕ → Clo₂ → Val → Val
vNatrec : ℕ → ℕ → Val → Clo₂ → Val → Val
vFcase  : ℕ → ℕ → Val → Val → Clo → Val
vOrdtr  : ℕ → ℕ → Val → Val → Val → Val → Val → Val
vHrefl  : ℕ → ℕ → Val → Val → Val
vTr     : ℕ → ℕ → Clo → Val → Val → Val
vAp     : ℕ → ℕ → Val → Clo → Val → Val
vJsub   : ℕ → Clo → Val → Val → Val
vIelim  : ℕ → ℕ → Val → Val → Val → Val → Val
vDpay   : ℕ → Val → Val → Val → Val
vDih    : ℕ → ℕ → Val → Val → Val → Val → Val

-- helpers on forced values (no fuel of their own: callers force first)
appF    : ℕ → ℕ → Val → Val → Val
fstF sndF : Val → Val
psplitF : ℕ → ℕ → Clo₂ → Val → Val
natrecF : ℕ → ℕ → Val → Clo₂ → Val → Val
fcaseF  : ℕ → ℕ → Val → Val → Clo → Val
ordtrF  : ℕ → ℕ → Val → Val → Val → Val → Val → Val
hreflF  : ℕ → ℕ → Bool → Val → Val → Val
hreflNat : ℕ → ℕ → Val → Val
trF     : ℕ → ℕ → Clo → Val → Val → Val → Val
trJ     : ℕ → Val → Bool
apF     : ℕ → ℕ → Val → Clo → Val → Val
jsubF   : Clo → Val → Val → Val
ielimF  : ℕ → ℕ → Val → Val → Val → Val → Val
dpayF   : ℕ → Val → Val → Val → Val
dihF    : ℕ → ℕ → Val → Val → Val → Val → Val
pwAtF   : ℕ → ℕ → Val → Val → Val
stkF    : Bool → ℕ → Val → Bool
pwF     : ℕ → Val → Bool

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
force (suc k) (vref d b) = force k (eval k 0 [] b)
force k       v          = v

------------------------------------------------------------------------
-- 4. Closures.  Instantiation is where fuel is spent.
------------------------------------------------------------------------

inst zero    n c                  v = vapp (vlam c) v
inst (suc k) n (clo ρ t)          v = eval k n (ρ , v) t
inst (suc k) n (cloK w)           v = w
inst (suc k) n (cloHrefl C s)     v = vHrefl k n (pwAt k n C v) (vApp k n s v)
inst (suc k) n (cloDpay I D f)    v = vDpay k I D (vApp k n f v)
inst (suc k) n (cloHomTo C A)     v = v⌜Hom⌝ C A v
inst (suc k) n (cloTrPw d f e)    y with force k (inst k n d y)
... | v⌜Hom⌝ c a _ = vTr k n (cloHomTo (pwAt k n c y) (vApp k n a y)) (inst k n f y) (vApp k n e y)
... | h            = vtr d (inst k n f y) (vApp k n e y)     -- unreachable: guarded at creation

inst₂ zero    n (clo₂ ρ t) x y = vpsplit (clo₂ ρ t) (vpair x y)
inst₂ (suc k) n (clo₂ ρ t) x y = eval k n ((ρ , x) , y) t

------------------------------------------------------------------------
-- 5. The rules, as smart eliminators (`Algorithm/Eval.head`'s order).
------------------------------------------------------------------------

vApp k n f u = appF k n (force k f) u
appF (suc k) n (vlam c) u = inst k n c u                       -- β
appF k       n f        u = vapp f u

vFst k p = fstF (force k p)
vSnd k p = sndF (force k p)
fstF (vpair a b) = a                                            -- βfst
fstF p           = vfst p
sndF (vpair a b) = b                                            -- βsnd
sndF p           = vsnd p

vPsplit k n b p = psplitF k n b (force k p)
psplitF (suc k) n b (vpair x y) = inst₂ k n b x y               -- psplit-β
psplitF k       n b p           = vpsplit b p

vNatrec k n z s t = natrecF k n z s (force k t)
natrecF k       n z s vnzero    = z                             -- natrec-zero
natrecF (suc k) n z s (vnsuc t) = inst₂ k n s t (vNatrec k n z s t)   -- natrec-suc
natrecF k       n z s t         = vnatrec z s t

vFcase k n t a b = fcaseF k n (force k t) a b
fcaseF k       n vfzero    a b = a                              -- fcase-z
fcaseF (suc k) n (vfsuc t) a b = inst k n b t                   -- fcase-s
fcaseF k       n t         a b = vfcase t a b

vOrdtr k n a t u p q = ordtrF k n (force k a) (force k t) (force k u) p q
ordtrF k       n vnzero    t         u         p q = vunit      -- ordtr-z
ordtrF k       n (vnsuc a) vnzero    vnzero    p q = p          -- ordtr-szz
ordtrF k       n (vnsuc a) (vnsuc t) vnzero    p q = q          -- ordtr-ssz
ordtrF k       n (vnsuc a) vnzero    (vnsuc u) p q = vabsurd (v⌜Hom⌝ v⌜Nat⌝ a u) p   -- ordtr-szs
ordtrF (suc k) n (vnsuc a) (vnsuc t) (vnsuc u) p q = vOrdtr k n a t u p q            -- ordtr-sss
ordtrF k       n a         t         u         p q = vordtr a t u p q

-- hrefl: pw-able code ⇒ pointwise (hrefl-pw); else the order's
-- reflexivity at ⌜Nat⌝ (hrefl-Nat-z/s); else stuck.
vHrefl k n C s = hreflF k n (pwV k C') C' s where C' = force k C
hreflF k n true  C s = vlam (cloHrefl C s)                      -- hrefl-pw
hreflF k n false v⌜Nat⌝ s = hreflNat k n s
hreflF k n false C s = vhrefl C s
hreflNat (suc k) n s with force k s
... | vnzero  = vunit                                           -- hrefl-Nat-z
... | vnsuc m = hreflNat k n m                                  -- hrefl-Nat-s
... | s'      = vhrefl v⌜Nat⌝ s'
hreflNat zero n s = vhrefl v⌜Nat⌝ s

-- tr: the motive is inspected at the fresh level n
vTr zero    n d p e = vtr d p e
vTr (suc k) n d p e = trF k n d (force k (inst k (suc n) d (vvar n))) (force k p) e
trF k n d (v⌜Hom⌝ c a m) (vhrefl C s) e with trJ k (force k C)
... | true  = e                                                 -- tr-J-*
... | false = vtr d (vhrefl C s) e
trF k n d (v⌜Hom⌝ c a (vvar m)) (vlam f) e with m == n | pwV k c
... | true | true = vlam (cloTrPw d f e)                        -- tr-pw
... | _    | _    = vtr d (vlam f) e
trF k n d (vvar m) (vlam f) e with m == n
... | true  = inst k n f e                                      -- tr-taut (and β)
... | false = vtr d (vlam f) e
trF k n d h p e = vtr d p e

-- which codes make `tr (⌜Hom⌝ ⋯) (hrefl C s) e ⟶ e`
trJ k v⌜base⌝          = true
trJ k (v⌜Σ⌝ _ _)       = true
trJ k v⌜Unit⌝          = true
trJ k (v⌜Id⌝ _ _ _)    = true
trJ k (v⌜IMu⌝ _ _ _)   = true
trJ k (v⌜Fin⌝ _)       = true
trJ k (v⌜Hom⌝ c₁ _ _)  = stkV true k c₁                        -- tr-J-Hom (stkA?)
trJ k _                = false

vAp k n cB b p = apF k n cB b (force k p)
apF (suc k) n cB b (vhrefl c₁ s) with stkV false k c₁
... | true  = vHrefl k n cB (inst k n b s)                      -- ap-J (stkC?)
... | false = vap cB b (vhrefl c₁ s)
apF k n cB b p = vap cB b p

vJsub k d p e = jsubF d (force k p) e
jsubF d (vidrefl c s) e = e                                     -- jsub-refl
jsubF d p             e = vjsub d p e

vIelim k n D i e t = ielimF k n D i e (force k t)
ielimF (suc k) n D i e (vcon p) =                               -- ι
  vApp k n (vApp k n (vApp k n e i) p) (vDih k n D e (vApp k n D i) p)
ielimF k n D i e t = vielim D i e t

vDpay k I D C = dpayF k I D (force k C)
dpayF k       I D vdι       = v⌜Unit⌝                           -- dpay-ι
dpayF k       I D (vdσ S f) = v⌜Σ⌝ S (cloDpay I D f)            -- dpay-σ
dpayF (suc k) I D (vdρ j C) = v⌜Σ⌝ (v⌜IMu⌝ I D j) (cloK (vDpay k I D C))   -- dpay-ρ: a constant body
dpayF k       I D C         = vdpay I D C

vDih k n D e C p = dihF k n D e (force k C) p
dihF k       n D e vdι       p = vunit                          -- dih-ι
dihF (suc k) n D e (vdσ S f) p = vDih k n D e (vApp k n f (vFst k p)) (vSnd k p)   -- dih-σ
dihF (suc k) n D e (vdρ j C) p =                                -- dih-ρ
  vpair (vIelim k n D j e (vFst k p)) (vDih k n D e C (vSnd k p))
dihF k n D e C p = vdih D e C p

-- pwBody, at a level: unfold a pw-able code at `x`
pwAt k n C x = pwAtF k n (force k C) x
pwAtF (suc k) n (v⌜Π⌝ γ δ)     x = inst k n δ x
pwAtF (suc k) n (v⌜Hom⌝ C a b) x = v⌜Hom⌝ (pwAt k n C x) (vApp k n a x) (vApp k n b x)
pwAtF k       n C              x = C

pwV k C = pwF k (force k C)
pwF k       (v⌜Π⌝ _ _)     = true
pwF (suc k) (v⌜Hom⌝ C _ _) = pwV k C
pwF k       _              = false

stkV nat k C = stkF nat k (force k C)
stkF nat k       v⌜base⌝         = true
stkF nat k       (v⌜Σ⌝ _ _)      = true
stkF nat k       (v⌜Id⌝ _ _ _)   = true
stkF nat k       v⌜Unit⌝         = true
stkF nat k       (v⌜Fin⌝ _)      = true
stkF nat k       v⌜Nat⌝          = nat
stkF nat k       (v⌜IMu⌝ _ _ _)  = true
stkF nat (suc k) (v⌜Hom⌝ C _ _)  = stkV true k C
stkF nat k       _               = false

------------------------------------------------------------------------
-- 6. Readback, at a context.  `unfold` = true unfolds every reference
--    (the kernel's normal form); false keeps them as atoms.
------------------------------------------------------------------------

len : Cx → ℕ
len ε     = zero
len (Γ ∙) = suc (len Γ)

-- the variable at level `l`, if it is in scope
-- (out of scope cannot happen for a well-scoped input; the fallback
-- `absurd unit unit` makes such a bug visible in a test, never silent)
lvl : (Γ : Cx) → ℕ → RTm Γ
lvl ε       l = absurd unit unit
lvl (Γ ∙) l with l == len Γ
... | true  = var vz
... | false = renTm vs (lvl Γ l)

rb  : Bool → ℕ → (Γ : Cx) → Val → RTm Γ
rbᶜ : Bool → ℕ → (Γ : Cx) → Clo → RTm (Γ ∙)
rb₂ : Bool → ℕ → (Γ : Cx) → Clo₂ → RTm ((Γ ∙) ∙)

rb u k Γ (vvar l)        = lvl Γ l
rb u k Γ (vlam c)        = lam (rbᶜ u k Γ c)
rb u k Γ (vapp f a)      = app (rb u k Γ f) (rb u k Γ a)
rb u k Γ (vpair a b)     = pair (rb u k Γ a) (rb u k Γ b)
rb u k Γ (vabsurd c e)   = absurd (rb u k Γ c) (rb u k Γ e)
rb u k Γ (vordtr a t v p q) = ordtr (rb u k Γ a) (rb u k Γ t) (rb u k Γ v) (rb u k Γ p) (rb u k Γ q)
rb u k Γ (vfst p)        = fst (rb u k Γ p)
rb u k Γ (vsnd p)        = snd (rb u k Γ p)
rb u k Γ v⌜base⌝         = ⌜base⌝
rb u k Γ (v⌜Π⌝ c d)      = ⌜Π⌝ (rb u k Γ c) (rbᶜ u k Γ d)
rb u k Γ (v⌜Σ⌝ c d)      = ⌜Σ⌝ (rb u k Γ c) (rbᶜ u k Γ d)
rb u k Γ (v⌜Hom⌝ c a b)  = ⌜Hom⌝ (rb u k Γ c) (rb u k Γ a) (rb u k Γ b)
rb u k Γ (vhrefl c t)    = hrefl (rb u k Γ c) (rb u k Γ t)
rb u k Γ (vtr d p e)     = tr (rbᶜ u k Γ d) (rb u k Γ p) (rb u k Γ e)
rb u k Γ (vap c b p)     = ap (rb u k Γ c) (rbᶜ u k Γ b) (rb u k Γ p)
rb u k Γ (v⌜Id⌝ c a b)   = ⌜Id⌝ (rb u k Γ c) (rb u k Γ a) (rb u k Γ b)
rb u k Γ (vidrefl c t)   = idrefl (rb u k Γ c) (rb u k Γ t)
rb u k Γ (vjsub d p e)   = jsub (rbᶜ u k Γ d) (rb u k Γ p) (rb u k Γ e)
rb u k Γ vunit           = unit
rb u k Γ vnzero          = nzero
rb u k Γ (vnsuc t)       = nsuc (rb u k Γ t)
rb u k Γ (vnatrec z s t) = natrec (rb u k Γ z) (rb₂ u k Γ s) (rb u k Γ t)
rb u k Γ (vcon p)        = con (rb u k Γ p)
rb u k Γ (vielim D i e t) = ielim (rb u k Γ D) (rb u k Γ i) (rb u k Γ e) (rb u k Γ t)
rb u k Γ vdι             = dι
rb u k Γ (vdσ S f)       = dσ (rb u k Γ S) (rb u k Γ f)
rb u k Γ (vdρ j C)       = dρ (rb u k Γ j) (rb u k Γ C)
rb u k Γ (vdpay I D C)   = dpay (rb u k Γ I) (rb u k Γ D) (rb u k Γ C)
rb u k Γ (vdih D e C p)  = dih (rb u k Γ D) (rb u k Γ e) (rb u k Γ C) (rb u k Γ p)
rb u k Γ vfzero          = fzero
rb u k Γ (vfsuc t)       = fsuc (rb u k Γ t)
rb u k Γ (vfcase t a b)  = fcase (rb u k Γ t) (rb u k Γ a) (rbᶜ u k Γ b)
rb u k Γ (vfcase0 t)     = fcase0 (rb u k Γ t)
rb u k Γ (vpsplit b p)   = psplit (rb₂ u k Γ b) (rb u k Γ p)
rb u k Γ v⌜Nat⌝          = ⌜Nat⌝
rb u k Γ v⌜Unit⌝         = ⌜Unit⌝
rb u k Γ (v⌜IMu⌝ I D i)  = ⌜IMu⌝ (rb u k Γ I) (rb u k Γ D) (rb u k Γ i)
rb u k Γ (v⌜Fin⌝ t)      = ⌜Fin⌝ (rb u k Γ t)
rb false k Γ (vref d b)  = ref d b
rb true zero Γ (vref d b) = ref d b
rb true (suc k) Γ (vref d b) = rb true k Γ (eval k 0 [] b)

rbᶜ u zero    Γ c = absurd unit unit
rbᶜ u (suc k) Γ c = rb u k (Γ ∙) (inst k (suc (len Γ)) c (vvar (len Γ)))

rb₂ u zero    Γ c = absurd unit unit
rb₂ u (suc k) Γ c = rb u k ((Γ ∙) ∙)
  (inst₂ k (suc (suc (len Γ))) c (vvar (len Γ)) (vvar (suc (len Γ))))

------------------------------------------------------------------------
-- 7. The entry points.
------------------------------------------------------------------------

-- the identity environment: variable i of Γ is its own level
idEnv : (Γ : Cx) → Env Γ
idEnv ε     = []
idEnv (Γ ∙) = idEnv Γ , vvar (len Γ)

-- the value of an open term
⟦_⟧_ : RTm Γ → ℕ → Val
⟦_⟧_ {Γ} t k = eval k (len Γ) (idEnv Γ) t

-- the normal form, every reference unfolded (the kernel's)
nbe : ℕ → RTm Γ → RTm Γ
nbe {Γ} k t = rb true k Γ (⟦ t ⟧ k)

-- the normal form with references as atoms (lazy δ)
nbeᵃ : ℕ → RTm Γ → RTm Γ
nbeᵃ {Γ} k t = rb false k Γ (⟦ t ⟧ k)
