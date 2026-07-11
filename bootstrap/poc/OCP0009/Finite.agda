------------------------------------------------------------------------
-- OCP-0009 · POC-0b(i) — conversion on finite domains, by enumeration
--
-- POC-0 decides conversion `_≋_` only on CLOSED morphisms (`Unit` domain),
-- because `t ≋ u := ∀ x. eval t x ≡ eval u x` collapses to one point when
-- the domain has one inhabitant. This module lifts the domain to ANY FINITE
-- first-order type, still fully proven and postulate-free, by *enumerating*
-- all inhabitants and checking the equation at each.
--
--   conv-fin : FiniteFO A → FirstOrder C → Term A C → Term A C → Bool
--   conv-fin-decides : conv-fin decides `_≋_` on such morphisms.
--
-- This precisely maps the boundary of the evaluation-at-points method:
--
--   * Evaluation decides conversion  ⟺  the domain is FINITE.
--   * `FiniteFO` excludes exactly `μ` (infinite — e.g. `Nat`) and `⇒`
--     (function). Those are the two cases where the input set is not
--     enumerable, and are therefore *precisely* where residualizing NbE /
--     neutrals become necessary (POC-0b(ii)): evaluate at a single GENERIC
--     (neutral) input and compare symbolically, instead of at every input.
--
-- So: pure evaluation reaches all of the finite first-order fragment; μ/⇒
-- is the frontier that forces reification. Strictly generalizes POC-0
-- (`Unit` is `FiniteFO`), still zero postulates.
------------------------------------------------------------------------

module poc.OCP0009.Finite where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv
open import poc.OCP0009.Complete using (eq-val-refl; ∧-true)
open import poc.OCP0009.Sound using (_≋_; eq-val-sound; ∧-elimˡ; ∧-elimʳ)

------------------------------------------------------------------------
-- Finite first-order types: first-order AND enumerable.
-- (No `μ` — infinite; no `⇒` — function. These are the NbE frontier.)
------------------------------------------------------------------------

data FiniteFO : Ty → Set where
  ffo-void : FiniteFO Void
  ffo-unit : FiniteFO Unit
  ffo-*    : ∀ {A B} → FiniteFO A → FiniteFO B → FiniteFO (A * B)
  ffo-+    : ∀ {A B} → FiniteFO A → FiniteFO B → FiniteFO (A + B)

-- A finite first-order type is in particular first-order (its codomain use).
ffo→fo : ∀ {A} → FiniteFO A → FirstOrder A
ffo→fo ffo-void      = fo-void
ffo→fo ffo-unit      = fo-unit
ffo→fo (ffo-* fa fb) = fo-* (ffo→fo fa) (ffo→fo fb)
ffo→fo (ffo-+ fa fb) = fo-+ (ffo→fo fa) (ffo→fo fb)

------------------------------------------------------------------------
-- Check a Boolean predicate on ALL inhabitants of a finite domain.
-- (An enumerator fused with the check — no `List` needed.)
------------------------------------------------------------------------

AllEq : ∀ A → FiniteFO A → (⟦ A ⟧T → Bool) → Bool
AllEq Void    ffo-void      p = true
AllEq Unit    ffo-unit      p = p tt
AllEq (A * B) (ffo-* fa fb) p = AllEq A fa (λ a → AllEq B fb (λ b → p (a , b)))
AllEq (A + B) (ffo-+ fa fb) p = AllEq A fa (λ a → p (inj₁ a)) ∧ AllEq B fb (λ b → p (inj₂ b))

-- AllEq is sound and complete for "p holds at every inhabitant".
AllEq-sound : ∀ A (fa : FiniteFO A) (p : ⟦ A ⟧T → Bool)
            → AllEq A fa p ≡ true → (x : ⟦ A ⟧T) → p x ≡ true
AllEq-sound Void    ffo-void      p h ()
AllEq-sound Unit    ffo-unit      p h _        = h
AllEq-sound (A * B) (ffo-* fa fb) p h (a , b)  =
  AllEq-sound B fb _ (AllEq-sound A fa _ h a) b
AllEq-sound (A + B) (ffo-+ fa fb) p h (inj₁ a) =
  AllEq-sound A fa _ (∧-elimˡ _ _ h) a
AllEq-sound (A + B) (ffo-+ fa fb) p h (inj₂ b) =
  AllEq-sound B fb _ (∧-elimʳ _ _ h) b

AllEq-complete : ∀ A (fa : FiniteFO A) (p : ⟦ A ⟧T → Bool)
               → ((x : ⟦ A ⟧T) → p x ≡ true) → AllEq A fa p ≡ true
AllEq-complete Void    ffo-void      p h = refl
AllEq-complete Unit    ffo-unit      p h = h tt
AllEq-complete (A * B) (ffo-* fa fb) p h =
  AllEq-complete A fa _ (λ a → AllEq-complete B fb _ (λ b → h (a , b)))
AllEq-complete (A + B) (ffo-+ fa fb) p h =
  ∧-true (AllEq-complete A fa _ (λ a → h (inj₁ a)))
         (AllEq-complete B fb _ (λ b → h (inj₂ b)))

------------------------------------------------------------------------
-- Conversion on a finite first-order domain, decided by evaluation at
-- every input.
------------------------------------------------------------------------

conv-fin : ∀ {A C} → FiniteFO A → FirstOrder C → (t u : Term A C) → Bool
conv-fin {A} {C} fa fc t u = AllEq A fa (λ x → eq-val C fc (eval t x) (eval u x))

-- Sound and complete for `_≋_` (observational equality) on this fragment.
conv-fin-sound : ∀ {A C} (fa : FiniteFO A) (fc : FirstOrder C) (t u : Term A C)
               → conv-fin fa fc t u ≡ true → t ≋ u
conv-fin-sound {A} {C} fa fc t u h x =
  eq-val-sound C fc (eval t x) (eval u x)
               (AllEq-sound A fa (λ y → eq-val C fc (eval t y) (eval u y)) h x)

conv-fin-complete : ∀ {A C} (fa : FiniteFO A) (fc : FirstOrder C) (t u : Term A C)
                  → t ≋ u → conv-fin fa fc t u ≡ true
conv-fin-complete {A} {C} fa fc t u e =
  AllEq-complete A fa (λ x → eq-val C fc (eval t x) (eval u x))
    (λ x → subst (λ z → eq-val C fc (eval t x) z ≡ true)
                 (e x)
                 (eq-val-refl C fc (eval t x)))

-- `conv-fin` DECIDES `_≋_` on finite-domain, first-order-codomain morphisms.
conv-fin-decides : ∀ {A C} (fa : FiniteFO A) (fc : FirstOrder C) (t u : Term A C)
                 → (t ≋ u → conv-fin fa fc t u ≡ true) × (conv-fin fa fc t u ≡ true → t ≋ u)
conv-fin-decides fa fc t u = conv-fin-complete fa fc t u , conv-fin-sound fa fc t u

------------------------------------------------------------------------
-- Worked examples on a genuinely non-`Unit` (2-point) domain — beyond what
-- POC-0's `conv` could express. Each `refl` forces `conv-fin` to enumerate
-- BOTH inputs and compare, at type-check time.
------------------------------------------------------------------------

Bool₂ : Ty
Bool₂ = Unit + Unit

ffo-Bool₂ : FiniteFO Bool₂
ffo-Bool₂ = ffo-+ ffo-unit ffo-unit

fo-Bool₂ : FirstOrder Bool₂
fo-Bool₂ = fo-+ fo-unit fo-unit

notB : Term Bool₂ Bool₂
notB = [ inr , inl ]

-- Involutivity `not ∘ not ≋ id`, decided across both points of the domain.
_ : conv-fin ffo-Bool₂ fo-Bool₂ (notB ∘ notB) id ≡ true
_ = refl

-- `not` is not the identity (differs on both points).
_ : conv-fin ffo-Bool₂ fo-Bool₂ notB id ≡ false
_ = refl

-- A constant function is not `not`.
_ : conv-fin ffo-Bool₂ fo-Bool₂ (inl ∘ terminal) notB ≡ false
_ = refl
