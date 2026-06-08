------------------------------------------------------------------------
-- Theory.RanzowFixpoint.EvalFullCorrectness
--
-- The full "fixpoint ⟹ correctness on all inputs" theorem, evaluator
-- form — the dual of Theory.RanzowFixpoint.FullCorrectness.
--
-- WHAT THIS ADDS OVER THE REWRITING VERSION
--
-- The rewriting FullCorrectness discharges the entire deep content into
-- ONE monolithic Established postulate
-- (Theory.Established.Transparency.nf-fixpoint-implies-correctness),
-- which the doc itself flags as folklore "not stated in any single
-- published source". Here we instead DECOMPOSE that monolith into the
-- two halves of Appendix A of bootstrap/theory/fixpoint-correctness.md
-- and PROVE the assembly constructively:
--
--   encoding-completeness  (A.4 + A.5):  the fixpoint at ⌜N⌝ certifies a
--                                        branch-wise-correctness fact P.
--   transparency           (A.3):        P propagates to all inputs
--                                        (uniformity of NF behaviour).
--   fixpoint-implies-correctness:        transparency ∘ completeness,
--                                        threaded through the Ranzow
--                                        fixpoint. CONSTRUCTIVE.
--
-- So the trusted surface drops from one opaque axiom to two sharp,
-- separately-dischargeable hypotheses joined by a checked proof. ZERO
-- POSTULATES in this module — both halves are explicit hypotheses,
-- exactly like Correctness/EvalCorrectness keep their math facts
-- explicit.
--
-- WHERE THE REMAINING DEPTH GOES
--
--   * encoding-completeness is largely DEFINITIONAL: ⌜N⌝ exposes every
--     branch of N's step as a sub-encoding (the eval-form analogue of
--     EncodingInductive.encode-cata-decomposes), so reaching the
--     fixpoint forces each branch to be correct.
--   * transparency is the genuinely semantic part — but in the evaluator
--     setting it is exactly the standard NbE ADEQUACY lemma (the
--     logical-relation between syntax and the evaluation model), which
--     IS published (Altenkirch–Dybjer–Hofmann–Streicher 2001;
--     Balat–Di Cosmo–Fiore 2004). So the deep remainder is re-based from
--     "folklore" onto a known, provable result, to be discharged by the
--     concrete VM's adequacy proof rather than postulated.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.EvalFullCorrectness where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Syntax.Evaluable using (Evaluable)
open import Theory.RanzowFixpoint.SelfEncoding using (SelfEncoding)
import Theory.RanzowFixpoint.EvalCorrectness as EC
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- Parameterized over a self-encoding carrier and an Evaluable carrier —
-- as in EvalCorrectness.
------------------------------------------------------------------------

module _ (SE : SelfEncoding)
         (Ev : Evaluable (SelfEncoding.Obj SE) (SelfEncoding.Hom SE)) where
  open SelfEncoding SE
  open Evaluable Ev

  ----------------------------------------------------------------------
  -- Value-level encoding laws (definitional; the eval-form analogue of
  -- EncodingInductive.encode-is-nf):
  --   encVal g  : the canonical value of the encoding ⌜g⌝
  --   encode-⇓  : ⌜g⌝ indeed evaluates to encVal g
  -- plus determinism of evaluation (as in EvalCorrectness).
  ----------------------------------------------------------------------

  module _ (encVal      : ∀ {A B} → Hom A B → Value Unit Code)
           (encode-⇓    : ∀ {A B} (g : Hom A B) → encode g ⇓ encVal g)
           (determinism : ∀ {A B} {t : Hom A B} {v w} → t ⇓ v → t ⇓ w → v ≡ w)
    where

    ------------------------------------------------------------------
    -- Correctness of N against an intended spec, evaluator form:
    -- on every encoded input ⌜g⌝, N evaluates to the value of ⌜spec g⌝.
    -- For spec = nf this says "N correctly normalises every g".
    ------------------------------------------------------------------

    Correct : (∀ {A B} → Hom A B → Hom A B) → Hom Code Code → Set
    Correct spec N = ∀ {A B} (g : Hom A B) → (N ∘ encode g) ⇓ encVal (spec g)

    ------------------------------------------------------------------
    -- The decomposition.
    --
    --   spec               : the intended interpretation (spec g = nf g)
    --   N                  : the candidate transformation
    --   BranchwiseCorrect  : the abstract A.4/A.5 certificate — "every
    --                        case branch of N computes spec correctly".
    --                        Opaque here; defined concretely at
    --                        instantiation in terms of N's step algebra.
    --   encoding-completeness : (A.4 + A.5) the fixpoint at ⌜N⌝ certifies
    --                           branch-wise correctness, because ⌜N⌝
    --                           exposes every branch as a sub-encoding.
    --   transparency       : (A.3) branch-wise correctness propagates to
    --                        every input — the NbE adequacy lemma.
    ------------------------------------------------------------------

    module _ (spec : ∀ {A B} → Hom A B → Hom A B)
             (N    : Hom Code Code)
             (BranchwiseCorrect : Set)
             (encoding-completeness :
                (N ∘ encode N) ⇓ encVal (spec N) → BranchwiseCorrect)
             (transparency :
                BranchwiseCorrect → Correct spec N)
      where

      ----------------------------------------------------------------
      -- The Ranzow fixpoint at N (value form) together with the
      -- self-agreement spec N ≡ N supplies the premise that
      -- encoding-completeness needs: N ∘ ⌜N⌝ evaluates to ⌜spec N⌝.
      --
      -- Proof: from the fixpoint, N ∘ ⌜N⌝ and ⌜N⌝ share a value v;
      -- by encode-⇓ and determinism, v is encVal N; rewrite by spec N ≡ N.
      ----------------------------------------------------------------

      private
        fixpoint-at-spec :
          EC.HasEvalRanzowFixpoint SE Ev N →
          spec N ≡ N →
          (N ∘ encode N) ⇓ encVal (spec N)
        fixpoint-at-spec (v , lhs⇓v , rhs⇓v) spec≡ =
          subst (λ x → (N ∘ encode N) ⇓ encVal x) (sym spec≡)
            (subst (λ x → (N ∘ encode N) ⇓ x)
                   (determinism rhs⇓v (encode-⇓ N))
                   lhs⇓v)

      ----------------------------------------------------------------
      -- Main theorem: the evaluator-form of bootstrap doc Theorem 4.1.
      --
      -- If N satisfies the Ranzow fixpoint and agrees with spec on its
      -- own encoding, then N computes spec on EVERY encoded input.
      ----------------------------------------------------------------

      fixpoint-implies-correctness :
        EC.HasEvalRanzowFixpoint SE Ev N →
        spec N ≡ N →
        Correct spec N
      fixpoint-implies-correctness rf spec≡ =
        transparency (encoding-completeness (fixpoint-at-spec rf spec≡))
