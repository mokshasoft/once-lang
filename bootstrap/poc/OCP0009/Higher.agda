------------------------------------------------------------------------
-- OCP-0009 · POC-0b(ii) — higher-order codomains (finite-argument functions)
--
-- POC-0/0b(i) required a FIRST-ORDER codomain (no `⇒`), because you cannot
-- compare two Agda functions structurally. But if a function's ARGUMENT type
-- is finite (enumerable), you CAN: check the two functions agree at every
-- input. This lifts the codomain restriction to functions with finite
-- arguments — still fully proven, still zero new axioms beyond funext.
--
--   Checkable C  — C is Void/Unit/×/+/μ (first-order) OR `A ⇒ B` with A
--                  finite and B checkable.
--   conv-h : FiniteFO A → Checkable C → Term A C → Term A C → Bool
--   conv-h-{sound,complete} against `_≋_`.
--
-- Comparing functions uses **funext** (pointwise agreement ⇒ equal function)
-- — the same axiom already in Complete.agda; nothing new.
--
-- This completes the "how far does pure evaluation reach" story on the
-- CODOMAIN side: every *hereditarily finite* type (finite base, finite
-- function arguments) is decidable by evaluation+enumeration. The remaining
-- frontier is `μ` in a *negative/argument* position (an infinite input set:
-- e.g. domain `Nat`, or codomain `Nat ⇒ B`) — there enumeration fails and
-- residualizing NbE / neutrals are genuinely required.
------------------------------------------------------------------------

module poc.OCP0009.Higher where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv using (FirstOrder; eq-val)
open import poc.OCP0009.Complete using (funext; eq-val-refl)
open import poc.OCP0009.Sound using (_≋_; eq-val-sound)
open import poc.OCP0009.Finite using (FiniteFO; AllEq; AllEq-sound; AllEq-complete)

------------------------------------------------------------------------
-- Checkable codomains: first-order, or functions with finite arguments.
------------------------------------------------------------------------

data Checkable : Ty → Set where
  chk-fo : ∀ {C}   → FirstOrder C → Checkable C
  chk-⇒  : ∀ {A B} → FiniteFO A → Checkable B → Checkable (A ⇒ B)

check-eq : ∀ C → Checkable C → ⟦ C ⟧T → ⟦ C ⟧T → Bool
check-eq C       (chk-fo fo)   v w = eq-val C fo v w
check-eq (A ⇒ B) (chk-⇒ fa cb) f g = AllEq A fa (λ a → check-eq B cb (f a) (g a))

check-eq-refl : ∀ C (chk : Checkable C) (v : ⟦ C ⟧T) → check-eq C chk v v ≡ true
check-eq-refl C       (chk-fo fo)   v = eq-val-refl C fo v
check-eq-refl (A ⇒ B) (chk-⇒ fa cb) f =
  AllEq-complete A fa _ (λ a → check-eq-refl B cb (f a))

check-eq-sound : ∀ C (chk : Checkable C) (v w : ⟦ C ⟧T) → check-eq C chk v w ≡ true → v ≡ w
check-eq-sound C       (chk-fo fo)   v w p = eq-val-sound C fo v w p
check-eq-sound (A ⇒ B) (chk-⇒ fa cb) f g p =
  funext (λ a → check-eq-sound B cb (f a) (g a) (AllEq-sound A fa _ p a))

------------------------------------------------------------------------
-- Conversion with a checkable (possibly higher-order) codomain.
------------------------------------------------------------------------

conv-h : ∀ {A C} → FiniteFO A → Checkable C → (t u : Term A C) → Bool
conv-h {A} {C} fa cc t u = AllEq A fa (λ x → check-eq C cc (eval t x) (eval u x))

conv-h-sound : ∀ {A C} (fa : FiniteFO A) (cc : Checkable C) (t u : Term A C)
             → conv-h fa cc t u ≡ true → t ≋ u
conv-h-sound {A} {C} fa cc t u h x =
  check-eq-sound C cc (eval t x) (eval u x)
                 (AllEq-sound A fa (λ y → check-eq C cc (eval t y) (eval u y)) h x)

conv-h-complete : ∀ {A C} (fa : FiniteFO A) (cc : Checkable C) (t u : Term A C)
                → t ≋ u → conv-h fa cc t u ≡ true
conv-h-complete {A} {C} fa cc t u e =
  AllEq-complete A fa (λ x → check-eq C cc (eval t x) (eval u x))
    (λ x → subst (λ z → check-eq C cc (eval t x) z ≡ true)
                 (e x)
                 (check-eq-refl C cc (eval t x)))

------------------------------------------------------------------------
-- Worked examples: comparing FUNCTION-VALUED morphisms by enumerating the
-- (finite) argument — impossible for the first-order-codomain `conv`.
------------------------------------------------------------------------

Bool₂ : Ty
Bool₂ = Unit + Unit

ffo-Bool₂ : FiniteFO Bool₂
ffo-Bool₂ = FiniteFO.ffo-+ FiniteFO.ffo-unit FiniteFO.ffo-unit

fun-chk : Checkable (Bool₂ ⇒ Bool₂)
fun-chk = chk-⇒ ffo-Bool₂ (chk-fo (FirstOrder.fo-+ FirstOrder.fo-unit FirstOrder.fo-unit))

notB : Term (Unit * Bool₂) Bool₂
notB = [ inr , inl ] ∘ snd

-- `curry snd` is the identity function; `curry (not (not b))` is too.
idFun  : Term Unit (Bool₂ ⇒ Bool₂)
idFun  = curry snd

negneg : Term Unit (Bool₂ ⇒ Bool₂)
negneg = curry ([ inr , inl ] ∘ notB)   -- λ b. not (not b) = b

negFun : Term Unit (Bool₂ ⇒ Bool₂)
negFun = curry notB                       -- λ b. not b

-- Two function-valued terms that are extensionally equal (both identity),
-- decided by checking BOTH inputs of the finite argument type.
_ : conv-h FiniteFO.ffo-unit fun-chk idFun negneg ≡ true
_ = refl

-- Negation is not the identity function.
_ : conv-h FiniteFO.ffo-unit fun-chk idFun negFun ≡ false
_ = refl
