------------------------------------------------------------------------
-- normalizer.Theory.Eval.Instance
--
-- Concrete instantiation of the FORMAL evaluator-form Ranzow correctness
-- (Theory.RanzowFixpoint.EvalCorrectness, in the `Once` library) at the
-- normalizer syntax, using the existing denotational evaluator
-- (Testing.Evaluator.eval).
--
-- This is decision (B) of plans/evaluator-instance.md: bootstrap depends
-- on Once, so the abstract theorem and the concrete model stay inline
-- (no duplication). The theorems are parameterised over the minimal
-- `SelfEncoding` interface, which the normalizer's first-order Func-based
-- syntax CAN supply (a full CCT3Structure, with higher-order μ, it could
-- not).
--
-- determinism + totality are discharged FOR FREE — `eval` is a total,
-- deterministic Agda function — so neither the confluence obligation
-- (cf. NonConfluenceWitness) nor the strong-normalization obligation
-- (cf. WeakNormalizationFails) appears. That is the whole point of the
-- evaluator route.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/Instance.agda
------------------------------------------------------------------------

module normalizer.Theory.Eval.Instance where

-- bootstrap side (own prelude / syntax / model)
open import normalizer.Syntax.Types using (Ty; Unit)
open import normalizer.Syntax.CCC using (Term; _∘_)
open import normalizer.Encoding.Encoding using (TermCode'; encode)
open import normalizer.Testing.Evaluator using (⟦_⟧T; eval)

-- Once side (abstract theorems)
open import Theory.Syntax.Evaluable using (Evaluable)
open import Theory.RanzowFixpoint.SelfEncoding using (SelfEncoding)
import Theory.RanzowFixpoint.EvalCorrectness as EC

-- stdlib (available via the Once dependency)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Product using (Σ; _,_; _×_)

------------------------------------------------------------------------
-- The denotational value domain + evaluation relation, as NAMED
-- definitions (not record-field lambdas) so their types match EC's
-- parameters rigidly.
------------------------------------------------------------------------

-- The value domain is wrapped in a record (not a bare function type) so
-- that value equality `v ≡ w` does not reduce to pointwise function
-- equality. Note also: in `t ⇓ᵈ v` the term `t` occurs only under the
-- non-injective `eval`, so the implicit `{t}` of `determinism` is not
-- recoverable from the goal — it is supplied explicitly at the use sites
-- below.
record DenValue (A B : Ty) : Set where
  constructor mkVal
  field unVal : ⟦ A ⟧T → ⟦ B ⟧T
open DenValue

_⇓ᵈ_ : ∀ {A B} → Term A B → DenValue A B → Set
t ⇓ᵈ v = eval t ≡ unVal v

infix 4 _⇓ᵈ_

------------------------------------------------------------------------
-- The self-encoding carrier and the Evaluable carrier.
------------------------------------------------------------------------

NormSE : SelfEncoding
NormSE = record
  { Obj = Ty ; Hom = Term ; _∘_ = _∘_
  ; Unit = Unit ; Code = TermCode' ; encode = encode }

NormEv : Evaluable Ty Term
NormEv = record { Value = DenValue ; _⇓_ = _⇓ᵈ_ }

------------------------------------------------------------------------
-- determinism + totality — free.
------------------------------------------------------------------------

determinism : ∀ {A B} {t : Term A B} {v w : DenValue A B} →
              t ⇓ᵈ v → t ⇓ᵈ w → v ≡ w
determinism p q = cong mkVal (trans (sym p) q)

totality : ∀ {A B} (t : Term A B) → Σ (DenValue A B) (λ v → t ⇓ᵈ v)
totality t = mkVal (eval t) , refl

------------------------------------------------------------------------
-- Concrete canonicity / uniqueness of the Ranzow fixpoint VALUE,
-- obtained by instantiating the abstract Once theorem with the model.
-- These are the first concrete (postulate-free, evaluator-backed)
-- consequences of the fixpoint property for the normalizer syntax.
------------------------------------------------------------------------

-- The Ranzow fixpoint property itself is reused verbatim from the formal
-- module (this is the cross-lib instantiation via SelfEncoding):
module Fix = EC.Fixpoint NormSE NormEv
open Fix public using (HasEvalRanzowFixpoint)

-- Its two consequences are EC.Fixpoint.Canonical.{eval-fixpoint-is-canonical,
-- eval-fixpoint-is-unique}. We re-prove them here directly from `determinism`
-- (the same one-liners) rather than instantiate EC.Canonical by module
-- application: with this function-based model, instantiating Canonical forces
-- `canonical-value`'s `with totality t`, where the `{t}` hidden under `eval`
-- cannot be solved. Proving the two theorems directly lets us pass `{t}`
-- explicitly; the proofs are otherwise identical to EC's.

-- Any observed value of (N ∘ ⌜N⌝) equals ⌜N⌝'s value.
eval-fixpoint-is-canonical :
  ∀ (T : Term TermCode' TermCode') →
  HasEvalRanzowFixpoint T →
  ∀ {u} → (T ∘ encode T) ⇓ᵈ u →
  Σ (DenValue Unit TermCode') (λ w → ((encode T) ⇓ᵈ w) × (u ≡ w))
eval-fixpoint-is-canonical T (v , fix-lhs , fix-rhs) p =
  v , fix-rhs , determinism {t = T ∘ encode T} p fix-lhs

-- The fixpoint value is unique (pure determinism).
eval-fixpoint-is-unique :
  ∀ (T : Term TermCode' TermCode') →
  ∀ {u w} → (T ∘ encode T) ⇓ᵈ u → (T ∘ encode T) ⇓ᵈ w → u ≡ w
eval-fixpoint-is-unique T p q = determinism {t = T ∘ encode T} p q

-- Convenience: a term whose self-application is denotationally the identity
-- (i.e. eval (T ∘ ⌜T⌝) ≡ eval ⌜T⌝) has the Ranzow fixpoint property.
mkFixpoint :
  ∀ {T : Term TermCode' TermCode'} →
  eval (T ∘ encode T) ≡ eval (encode T) →
  HasEvalRanzowFixpoint T
mkFixpoint {T} eq = mkVal (eval (encode T)) , eq , refl
