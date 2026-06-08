------------------------------------------------------------------------
-- normalizer.Theory.WeakNormalizationFails
--
-- A MACHINE-CHECKED counter-witness (zero postulates): the normalizer's
-- reduction relation `_⟶_` is NOT (even weakly) normalizing, so the
-- postulate
--
--   Axioms.EstablishedMath.strong-normalization
--     : ∀ {A B} (t : Term A B) → ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf)
--
-- is FALSE. (It is stated as weak normalization — "some reduction path
-- reaches a normal form" — and even that fails.)
--
-- ROOT CAUSE: `_⟶_` contains BOTH `assoc-l` and `assoc-r`
-- (Syntax/CCC.agda), so any composite associates back and forth forever:
--
--   (f ∘ g) ∘ h  ⟶assoc-r  f ∘ (g ∘ h)  ⟶assoc-l  (f ∘ g) ∘ h  ⟶ ...
--
-- A three-way composition of non-β-reducible atoms (here three `fst`s)
-- therefore has NO reachable normal form: every reduct is itself
-- reducible.
--
-- DUALITY WITH NonConfluenceWitness:
--   * formal StrongCCL.CCT1: ONE-WAY assoc → SN holds, CONFLUENCE fails
--     (Theory.Syntax.StrongCCL.CCT1.NonConfluenceWitness).
--   * this normalizer:       TWO-WAY assoc → confluence is salvageable,
--     but NORMALIZATION fails (this file).
--   Each concrete development sacrifices one of {confluence, termination}
--   and postulates it back. This is exactly the "no confluent AND
--   terminating directed rewrite system for full βη" dilemma, and the
--   reason the evaluator/NbE route (determinism + totality) is the way
--   out: it needs neither postulate.
--
-- IMPACT: `strong-normalization` is consumed by Theory.Uniqueness,
-- Theory.GeneralCorrectness.{Correctness,Terminates}, and the top-level
-- TCB0/Main — so the normalizer's uniqueness / general-correctness
-- claims currently rest on a false axiom. (The fixpoint EXISTENCE proof,
-- via the NoRedex per-constructor reductions, is independent of it.)
------------------------------------------------------------------------

module normalizer.Theory.WeakNormalizationFails where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC

------------------------------------------------------------------------
-- The looping term: three nested projections.
------------------------------------------------------------------------

o : Ty
o = Unit

a : Term (o * o) o
a = fst

b : Term ((o * o) * o) (o * o)
b = fst

c : Term (((o * o) * o) * o) ((o * o) * o)
c = fst

t-left : Term (((o * o) * o) * o) o
t-left = (a ∘ b) ∘ c

t-right : Term (((o * o) * o) * o) o
t-right = a ∘ (b ∘ c)

------------------------------------------------------------------------
-- Irreducibility of the atoms.
------------------------------------------------------------------------

fst-irred : ∀ {A B} {u : Term (A * B) A} → ¬ (fst ⟶ u)
fst-irred ()

-- `fst ∘ fst` (the shape of both `a ∘ b` and `b ∘ c`) is irreducible:
-- only the two ∘-congruence rules could fire, and both hit fst-irred.
fst∘fst-irred : ∀ {A B C} {u} →
                ¬ ((fst {A} {B} ∘ fst {A * B} {C}) ⟶ u)
fst∘fst-irred (⟶-∘-l s) = fst-irred s
fst∘fst-irred (⟶-∘-r s) = fst-irred s

------------------------------------------------------------------------
-- The ONLY single step from each form is the associativity flip to the
-- other form. All other rule constructors are excluded by unification
-- (composite/atomic head mismatch); the two ∘-congruence cases are
-- refuted by irreducibility of the immediate subterms.
------------------------------------------------------------------------

step-left : ∀ {w} → t-left ⟶ w → w ≡ t-right
step-left assoc-r      = refl
step-left (⟶-∘-l s)    = ⊥-elim (fst∘fst-irred s)
step-left (⟶-∘-r s)    = ⊥-elim (fst-irred s)

step-right : ∀ {w} → t-right ⟶ w → w ≡ t-left
step-right assoc-l     = refl
step-right (⟶-∘-l s)   = ⊥-elim (fst-irred s)
step-right (⟶-∘-r s)   = ⊥-elim (fst∘fst-irred s)

------------------------------------------------------------------------
-- The reachable set is exactly {t-left, t-right}, and both are reducible.
------------------------------------------------------------------------

Two : Term (((o * o) * o) * o) o → Set
Two u = (u ≡ t-left) ⊎ (u ≡ t-right)

two-reducible : ∀ {u} → Two u → ∃[ v ] (u ⟶ v)
two-reducible (inj₁ refl) = t-right , assoc-r
two-reducible (inj₂ refl) = t-left  , assoc-l

two-step : ∀ {u w} → Two u → u ⟶ w → Two w
two-step (inj₁ refl) s = inj₂ (step-left s)
two-step (inj₂ refl) s = inj₁ (step-right s)

two-closed : ∀ {u v} → Two u → u ⟶* v → Two v
two-closed tw done         = tw
two-closed tw (step s rest) = two-closed (two-step tw s) rest

------------------------------------------------------------------------
-- No normal form is reachable from t-left.
------------------------------------------------------------------------

no-nf-from-t-left : ∀ {v} → t-left ⟶* v → IsNormalForm v → ⊥
no-nf-from-t-left red isnf with two-reducible (two-closed (inj₁ refl) red)
... | (_ , s) = isnf s

------------------------------------------------------------------------
-- Therefore weak normalization (the `strong-normalization` postulate as
-- stated) is false.
------------------------------------------------------------------------

WeakNormalization : Set
WeakNormalization =
  ∀ {A B} (t : Term A B) → ∃[ nf ] ((t ⟶* nf) × IsNormalForm nf)

weak-normalization-fails : ¬ WeakNormalization
weak-normalization-fails wn with wn t-left
... | (_ , (red , isnf)) = no-nf-from-t-left red isnf
