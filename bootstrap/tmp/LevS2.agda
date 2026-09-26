{-# OPTIONS --safe #-}
-- SPIKE-LEVITATION S2 — SUBSTITUTION through descriptions.
--
-- Descriptions stop being closed: a telescope is a TERM (`dι j`, `dσ S f`
-- with `f` a FUNCTION, `dρ j C`), and the operators that read it — `pay`
-- (ipayTy) and `ih` (iihs) — are FORMERS with computation rules, as are
-- `ielim` (ι, guarded by a CANONICAL description, S1) and `lkp` (ilookupD).
--
-- SUCCESS: every reduction rule is stable under parallel substitution,
--   sub-step : t ⟶ t' → sub σ t ⟶ sub σ t'
-- with the only non-definitional cases discharged by the TWO standard
-- single-binder lemmas (β-commutation and `sub (exts σ) (wk t) ≡ wk (sub σ t)`)
-- — no tower, no plural binders.  The syntax is generic (one operator
-- table, one traversal), which is how the kernel's field table is used.
module tmp.LevS2 where

open import tmp.LevSyn

-- ═══ the operator table ═══════════════════════════════════════════════════
data Op : Set where
  `lam `app `sig `unit `tt `pair `fst `snd : Op
  `dnil `dcons `dι `dσ `dρ                 : Op   -- descriptions/telescopes
  `pay `ih `ielim `mnil `mcons             : Op
  `icon `lkp `sel                          : Nat → Op

ar : Op → List Nat          -- binder count of each argument
ar `lam      = 1 ∷ []
ar `app      = 0 ∷ 0 ∷ []
ar `sig      = 0 ∷ 1 ∷ []
ar `unit     = []
ar `tt       = []
ar `pair     = 0 ∷ 0 ∷ []
ar `fst      = 0 ∷ []
ar `snd      = 0 ∷ []
ar `dnil     = []
ar `dcons    = 0 ∷ 0 ∷ []
ar `dι       = 0 ∷ []            -- dι j
ar `dσ       = 0 ∷ 0 ∷ []        -- dσ S f      (f : S → telescope, a TERM)
ar `dρ       = 0 ∷ 0 ∷ []        -- dρ j C
ar `pay      = 0 ∷ 0 ∷ []        -- pay C X     (X the family)
ar `ih       = 0 ∷ 0 ∷ 0 ∷ 0 ∷ [] -- ih D C e p
ar `ielim    = 0 ∷ 0 ∷ 0 ∷ []    -- ielim D e t
ar `mnil     = []
ar `mcons    = 0 ∷ 0 ∷ []
ar (`icon k) = 0 ∷ []
ar (`lkp k)  = 0 ∷ []
ar (`sel k)  = 0 ∷ []

open Syntax Op ar

pattern lam b      = node `lam (b ∷ [])
pattern app t u    = node `app (t ∷ u ∷ [])
pattern sig S T    = node `sig (S ∷ T ∷ [])
pattern unit       = node `unit []
pattern tt         = node `tt []
pattern pair a b   = node `pair (a ∷ b ∷ [])
pattern fst p      = node `fst (p ∷ [])
pattern snd p      = node `snd (p ∷ [])
pattern dnil       = node `dnil []
pattern dcons c d  = node `dcons (c ∷ d ∷ [])
pattern dι j       = node `dι (j ∷ [])
pattern dσ S f     = node `dσ (S ∷ f ∷ [])
pattern dρ j C     = node `dρ (j ∷ C ∷ [])
pattern pay C X    = node `pay (C ∷ X ∷ [])
pattern ih D C e p = node `ih (D ∷ C ∷ e ∷ p ∷ [])
pattern ielim D e t = node `ielim (D ∷ e ∷ t ∷ [])
pattern mnil       = node `mnil []
pattern mcons a e  = node `mcons (a ∷ e ∷ [])
pattern icon k p   = node (`icon k) (p ∷ [])
pattern lkp D k    = node (`lkp k) (D ∷ [])
pattern sel k e    = node (`sel k) (e ∷ [])

-- ═══ reduction: the levitated rules ══════════════════════════════════════
data Canon {n : Nat} : Tm n → Set where
  c-nil  : Canon dnil
  c-cons : {c d : Tm n} → Canon (dcons c d)

variable
  a c d e f j p u t t' S X D C' : Tm n
  b : Tm (suc n)
  k : Nat

infix 4 _⟶_ _⟶ₐ_
data _⟶_  {n : Nat} : Tm n → Tm n → Set
data _⟶ₐ_ {n : Nat} : Args n ks → Args n ks → Set

data _⟶_ {n} where
  β      : app (lam b) u ⟶ b [ u ]
  π₁     : fst (pair a c) ⟶ a
  π₂     : snd (pair a c) ⟶ c
  -- ι (canonical D only — S1), lookup, method selection
  ι      : Canon D → ielim D e (icon k p) ⟶ app (app (sel k e) p) (ih D (lkp D k) e p)
  lkp-z  : lkp (dcons c d) zero ⟶ c
  lkp-s  : lkp (dcons c d) (suc k) ⟶ lkp d k
  sel-z  : sel zero (mcons a e) ⟶ a
  sel-s  : sel (suc k) (mcons a e) ⟶ sel k e
  -- the payload TYPE of a telescope: a Σ-telescope, the family at ρ's index
  pay-ι  : pay (dι j) X ⟶ unit
  pay-σ  : pay (dσ S f) X ⟶ sig S (pay (app (wk f) (var fz)) (wk X))
  pay-ρ  : pay (dρ j C') X ⟶ sig (app X j) (pay (wk C') (wk X))
  -- the recursive hypotheses of a payload
  ih-ι   : ih D (dι j) e p ⟶ tt
  ih-σ   : ih D (dσ S f) e p ⟶ ih D (app f (fst p)) e (snd p)
  ih-ρ   : ih D (dρ j C') e p ⟶ pair (ielim D e (fst p)) (ih D C' e (snd p))
  -- congruence, generically
  under  : {o : Op} {as as' : Args n (ar o)} → as ⟶ₐ as' → node o as ⟶ node o as'

data _⟶ₐ_ {n} where
  here  : {k : Nat} {t t' : Tm (k + n)} {as : Args n ks} → t ⟶ t' → (t ∷ as) ⟶ₐ (t' ∷ as)
  there : {k : Nat} {t : Tm (k + n)} {as as' : Args n ks} → as ⟶ₐ as' → (t ∷ as) ⟶ₐ (t ∷ as')

-- ═══ ★ S2: every rule is stable under substitution ═══════════════════════
canon-sub : (σ : Fin m → Tm n) → Canon D → Canon (sub σ D)
canon-sub σ c-nil  = c-nil
canon-sub σ c-cons = c-cons

≡-tgt : t ⟶ u → u ≡ t' → t ⟶ t'
≡-tgt s refl = s

sub-step  : (σ : Fin m → Tm n) {t t' : Tm m} → t ⟶ t' → sub σ t ⟶ sub σ t'
subA-step : (σ : Fin m → Tm n) {as as' : Args m ks} → as ⟶ₐ as' → subA σ as ⟶ₐ subA σ as'
sub-step σ (β {b = b} {u = u}) = ≡-tgt β (sym (sub-β σ b u))
sub-step σ π₁       = π₁
sub-step σ π₂       = π₂
sub-step σ (ι g)    = ι (canon-sub σ g)
sub-step σ lkp-z    = lkp-z
sub-step σ lkp-s    = lkp-s
sub-step σ sel-z    = sel-z
sub-step σ sel-s    = sel-s
sub-step σ pay-ι    = pay-ι
sub-step σ (pay-σ {S = S} {f = f} {X = X}) =
  ≡-tgt pay-σ (cong₂ (λ F Y → sig (sub σ S) (pay (app F (var fz)) Y))
                     (sym (sub-wk σ f)) (sym (sub-wk σ X)))
sub-step σ (pay-ρ {j = j} {C' = C'} {X = X}) =
  ≡-tgt pay-ρ (cong₂ (λ F Y → sig (app (sub σ X) (sub σ j)) (pay F Y))
                     (sym (sub-wk σ C')) (sym (sub-wk σ X)))
sub-step σ ih-ι     = ih-ι
sub-step σ ih-σ     = ih-σ
sub-step σ ih-ρ     = ih-ρ
sub-step σ (under s) = under (subA-step σ s)
subA-step σ (here {k = k} s) = here (sub-step (extsN k σ) s)
subA-step σ (there s)        = there (subA-step σ s)
