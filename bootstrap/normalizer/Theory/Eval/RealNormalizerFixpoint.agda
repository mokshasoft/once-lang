------------------------------------------------------------------------
-- normalizer.Theory.Eval.RealNormalizerFixpoint
--
-- The REAL dispatch normalizer `normalize = cata TermF normalize-step`
-- (NOT the refold) has the Ranzow fixpoint property in the denotational
-- model, fed through the formal canonicity theorem.
--
-- How: its SYNTACTIC fixpoint is constructive and axiom-free
-- (TCB0.Normalizer.fixpoint-from-noredex : normalize ∘ ⌜normalize⌝ ⟶*
-- ⌜normalize⌝). Since `eval` respects reduction (EvalSound.eval-sound*),
-- the syntactic fixpoint lifts to the denotational one. This is the
-- non-degenerate counterpart of RefoldFixpoint.
--
-- Trust: zero confluence, zero strong-normalization; the only axiom is
-- function extensionality (via EvalSound), plus the model's pre-existing
-- pragmas. No false postulates.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/RealNormalizerFixpoint.agda
------------------------------------------------------------------------

module normalizer.Theory.Eval.RealNormalizerFixpoint where

open import normalizer.Syntax.Types using (Unit; ⊤; tt)
open import normalizer.Syntax.CCC using (Term; _∘_)
open import normalizer.Encoding.Encoding using (TermCode'; encode)
open import normalizer.Testing.Evaluator using (eval)
open import normalizer.TCB0.Normalizer.Definition using (normalize)
open import normalizer.TCB0.Normalizer.NoRedexFixpoint using (fixpoint-from-noredex)
open import normalizer.Theory.Eval.Instance
  using (HasEvalRanzowFixpoint; mkFixpoint; eval-fixpoint-is-canonical;
         DenValue; mkVal; _⇓ᵈ_)
open import normalizer.Theory.Eval.EvalSound using (eval-sound*)

open import Relation.Binary.PropositionalEquality using (_≡_; cong)
open import Data.Product using (Σ; _×_)

------------------------------------------------------------------------
-- The denotational Ranzow fixpoint of the REAL normalizer, obtained by
-- lifting its constructive syntactic fixpoint through eval-soundness.
------------------------------------------------------------------------

real-fixpoint-at-tt :
  eval (normalize ∘ encode normalize) tt ≡ eval (encode normalize) tt
real-fixpoint-at-tt = eval-sound* fixpoint-from-noredex tt

real-fixpoint-fn :
  eval (normalize ∘ encode normalize) ≡ eval (encode normalize)
real-fixpoint-fn = cong (λ z → λ (_ : ⊤) → z) real-fixpoint-at-tt

normalize-has-fixpoint : HasEvalRanzowFixpoint normalize
normalize-has-fixpoint = mkFixpoint {normalize} real-fixpoint-fn

------------------------------------------------------------------------
-- End-to-end: feed the real normalizer + its fixpoint through the formal
-- canonicity theorem.
------------------------------------------------------------------------

normalize-canonical :
  Σ (DenValue Unit TermCode')
    (λ w → (encode normalize ⇓ᵈ w)
         × (mkVal (eval (encode normalize)) ≡ w))
normalize-canonical =
  eval-fixpoint-is-canonical normalize normalize-has-fixpoint
    {mkVal (eval (encode normalize))} real-fixpoint-fn
