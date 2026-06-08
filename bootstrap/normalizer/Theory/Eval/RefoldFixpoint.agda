------------------------------------------------------------------------
-- normalizer.Theory.Eval.RefoldFixpoint
--
-- A CONCRETE normalizer N = `cata TermF In` (the refold) that
-- provably has the Ranzow fixpoint property in the denotational model,
-- fed through the formal canonicity theorem.
--
-- The refold normalizer is denotationally the identity: `eval (cata F In)
-- = id` (the cata-reflection law). So `eval (N ∘ ⌜N⌝) ≡ eval ⌜N⌝`, the
-- denotational fixpoint, holds. This is a degenerate-but-concrete witness
-- that the whole pipeline (concrete N → HasEvalRanzowFixpoint → formal
-- eval-fixpoint-is-canonical) closes end-to-end with ZERO postulates and,
-- crucially, no confluence and no strong-normalization obligation.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/RefoldFixpoint.agda
------------------------------------------------------------------------

module normalizer.Theory.Eval.RefoldFixpoint where

open import normalizer.Syntax.Types
  using (Func; Id; K; _⊕_; _⊗_; μ_; Unit; ⊤; tt; inj₁; inj₂; _,_)
open import normalizer.Syntax.CCC using (Term; _∘_; cata; In)
open import normalizer.Encoding.Encoding using (TermF; TermCode'; encode)
open import normalizer.Testing.Evaluator
  using (⟦_⟧T; ⟦_⟧FS; Fix; fix; fmap-Set; cata-Set; coherence; coherence⁻¹;
         eval; normalizer)
open import normalizer.Theory.Eval.Instance
  using (HasEvalRanzowFixpoint; mkFixpoint; eval-fixpoint-is-canonical;
         DenValue; mkVal; _⇓ᵈ_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Product using (Σ; _×_)

------------------------------------------------------------------------
-- (1) coherence is a section of coherence⁻¹ (round-trip), by induction
-- on the functor code.
------------------------------------------------------------------------

coh-roundtrip : ∀ F A (z : ⟦ F ⟧FS ⟦ A ⟧T) →
                coherence F A (coherence⁻¹ F A z) ≡ z
coh-roundtrip Id      A z        = refl
coh-roundtrip (K _)   A z        = refl
coh-roundtrip (F ⊕ G) A (inj₁ x) = cong inj₁ (coh-roundtrip F A x)
coh-roundtrip (F ⊕ G) A (inj₂ y) = cong inj₂ (coh-roundtrip G A y)
coh-roundtrip (F ⊗ G) A (x , y)  = cong₂ _,_ (coh-roundtrip F A x)
                                             (coh-roundtrip G A y)

------------------------------------------------------------------------
-- (2) fmap-Set with a pointwise-identity function is the identity, by
-- induction on the functor code.
------------------------------------------------------------------------

fmap-pid : ∀ F {X} (g : X → X) → (∀ z → g z ≡ z) →
           (x : ⟦ F ⟧FS X) → fmap-Set F g x ≡ x
fmap-pid Id      g h x        = h x
fmap-pid (K _)   g h x        = refl
fmap-pid (F ⊕ G) g h (inj₁ x) = cong inj₁ (fmap-pid F g h x)
fmap-pid (F ⊕ G) g h (inj₂ y) = cong inj₂ (fmap-pid G g h y)
fmap-pid (F ⊗ G) g h (x , y)  = cong₂ _,_ (fmap-pid F g h x)
                                          (fmap-pid G g h y)

------------------------------------------------------------------------
-- (3) Reflection: folding with `In` is the identity. (Same TERMINATING
-- caveat as cata-Set: the recursive call appears under fmap-Set.)
------------------------------------------------------------------------

{-# TERMINATING #-}
cata-In-id : ∀ F (y : Fix F) → eval (cata F In) y ≡ y
cata-In-id F (fix x) =
  trans (cong (λ w → fix (coherence F (μ F) (coherence⁻¹ F (μ F) w)))
              (fmap-pid F (cata-Set F _) (cata-In-id F) x))
        (cong fix (coh-roundtrip F (μ F) x))

------------------------------------------------------------------------
-- (4) The denotational Ranzow fixpoint of the refold normalizer.
------------------------------------------------------------------------

-- pointwise at the unique closed-term input tt
fixpoint-at-tt :
  eval (normalizer ∘ encode normalizer) tt ≡ eval (encode normalizer) tt
fixpoint-at-tt = cata-In-id TermF (eval (encode normalizer) tt)

-- lift to function equality (⊤-eta makes a `⊤ → X` function definitionally
-- `λ _ → f tt`, so no funext is needed)
fixpoint-fn :
  eval (normalizer ∘ encode normalizer) ≡ eval (encode normalizer)
fixpoint-fn = cong (λ z → λ (_ : ⊤) → z) fixpoint-at-tt

normalizer-has-fixpoint : HasEvalRanzowFixpoint normalizer
normalizer-has-fixpoint = mkFixpoint {normalizer} fixpoint-fn

------------------------------------------------------------------------
-- (5) End-to-end: feed the concrete normalizer + its fixpoint through the
-- FORMAL canonicity theorem.
------------------------------------------------------------------------

-- Fully concrete application of the formal canonicity theorem: observing
-- that (N ∘ ⌜N⌝) evaluates to ⌜N⌝'s value, it returns the canonical value.
normalizer-canonical :
  Σ (DenValue Unit TermCode')
    (λ w → (encode normalizer ⇓ᵈ w)
         × (mkVal (eval (encode normalizer)) ≡ w))
normalizer-canonical =
  eval-fixpoint-is-canonical normalizer normalizer-has-fixpoint
    {mkVal (eval (encode normalizer))} fixpoint-fn
