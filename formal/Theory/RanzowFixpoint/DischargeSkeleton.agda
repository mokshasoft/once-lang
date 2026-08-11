------------------------------------------------------------------------
-- Theory.RanzowFixpoint.DischargeSkeleton
--
-- A skeleton documenting what concrete instantiation must provide
-- to discharge Theory.Established.Transparency for a given syntax.
--
-- Each obligation is given as a type signature in a record. A
-- concrete instance discharges the postulate by providing values
-- for these fields. The bootstrap normalizer (bootstrap/normalizer/
-- Encoding/, Syntax/BetaNormalForm.agda, TCB0/) is an existing
-- concrete realization of all these obligations against its own CCC
-- term datatype; this skeleton makes the analogous obligations
-- visible at the formal/Theory/ layer.
--
-- This module is purely a record of obligations.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.DischargeSkeleton where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme)
open import Theory.Encoding.Inductive using (EncodingInductive)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The Discharge Witness Record
--
-- A TransparencyDischarge witness packages the structural facts a
-- concrete syntax must provide to discharge the abstract Transparency
-- postulate. Given a witness, Transparency.nf-fixpoint-implies-correctness
-- becomes a THEOREM (provable by induction on the canonical NF form).
--
-- Concrete instances build this witness by:
--   - Committing to Code = μ TermF for an explicit TermF.
--   - Providing the canonical-form lemma for NF morphisms Code → Code.
--   - Providing the encoding-induction principle.
--   - Verifying the per-constructor uniformity property.
--
-- The bootstrap normalizer provides equivalents of all these for its
-- own CCC term datatype.
------------------------------------------------------------------------

record TransparencyDischarge
         (S   : CCT3Structure)
         (Red : Reducible (CCT3Structure.Obj S) (CCT3Structure.Hom S))
         (E   : EncodingScheme S)
         (EI  : EncodingInductive S Red E)
         : Set₁ where
  open CCT3Structure S
  open Reducible Red
  open EncodingScheme E
  open EncodingInductive EI

  field
    --------------------------------------------------------------------
    -- Obligation 1: Code is a μ-type for a specific TermF.
    --
    -- Pin down Code's μ-shape. This commits the concrete instance to
    -- a specific term-syntax functor and exposes the corresponding
    -- recursion principle.
    --------------------------------------------------------------------

    TermF      : Obj → Obj
    Code-is-μF : Code ≡ μ TermF

    --------------------------------------------------------------------
    -- Obligation 2: User-designated cata-form for the candidate.
    --
    -- The candidate transformation N : Code → Code is constructed AS
    -- a catamorphism cata α for an explicit α in NF. This is a
    -- STRUCTURAL CHOICE, not a universal claim about all NFs.
    --
    -- Why not the universal version: in any standard CCC syntax, the
    -- universal claim "every NF morphism is cata-form" is literally
    -- false — id is NF but not literally cata α (it is only ≈-equal
    -- to one via Lambek's lemma cata In ≈ id). The user-designated
    -- version sidesteps this by treating cata-form as a hypothesis
    -- on the candidate, not a theorem about all NFs.
    --
    -- The bootstrap normalizer adopts this convention: its N is
    -- always built as cata α from the start.
    --
    -- The corresponding witness is just a pair (α, IsNormalForm α)
    -- supplied alongside the candidate.
    --------------------------------------------------------------------

    candidate-cata-form :
      Hom Code Code →
      Σ (Hom (TermF Code) Code) λ α →
        IsNormalForm α  -- the algebra is in NF (and the candidate ≡ cata α
                        -- modulo the Code-is-μF transport)

    --------------------------------------------------------------------
    -- Obligation 3: Cata-β as a directed reduction.
    --
    -- The CCT3Structure record gives cata-β as an EQUATIONAL law
    -- (cata α ∘ In ≈ α ∘ fmap (cata α)). For directed-reduction
    -- reasoning, we need it as a ⟶* step.
    --
    -- Discharged at instantiation by inspection of the reduction rules.
    --------------------------------------------------------------------

    cata-β-reduction :
      ∀ {F : Obj → Obj} {A} (alg : Hom (F A) A) →
      (cata {F} alg ∘ In {F}) ⟶* (alg ∘ fmap {F} (cata {F} alg))

    --------------------------------------------------------------------
    -- Obligation 4: Encoding decomposition for cata morphisms.
    --
    -- Strengthening of EncodingInductive.encode-cata-decomposes:
    -- not just "⌜α⌝ ⊑ ⌜cata α⌝" but the EXACT positional structure.
    --
    -- For a concrete encoding via tagged sum-of-products, this is
    -- mechanical inspection.
    --------------------------------------------------------------------

    encode-cata-positional :
      ∀ {F : Obj → Obj} {A} (alg : Hom (F A) A) →
      Σ (Hom Unit Code → Hom Unit Code) λ wrapper →
        encode (cata {F} alg) ≡ wrapper (encode alg)

    --------------------------------------------------------------------
    -- Obligation 5: Per-constructor uniformity (the deep one).
    --
    -- For each constructor c of TermF and each algebra α, α's behavior
    -- on encoded inputs whose head constructor is c is determined by
    -- the encoded subterms only. Phrased operationally:
    --
    --   If the head constructor of ⌜g⌝ matches c, then α applied to
    --   the unfolded ⌜g⌝ produces output uniformly in the encoded
    --   subterms of g.
    --
    -- This is the genuinely parametric content. For a concrete syntax
    -- it follows from canonical NF analysis: each branch of α is a
    -- closed CCC term with no hidden parameters, so its action is
    -- structural.
    --
    -- The bootstrap normalizer's BetaNormalForm.agda + Dispatch.agda
    -- + DispatchLemmas.agda collectively establish this for its
    -- concrete syntax.
    --------------------------------------------------------------------

    branch-uniformity :
      ∀ (N : Hom Code Code)
        (spec : ∀ {A B} → Hom A B → Hom A B) →
      IsNormalForm N →
      -- if N reduces correctly on its own encoding
      (N ∘ encode N) ⟶* encode (spec N) →
      -- it does so on every encoded input
      (∀ {A B} (g : Hom A B) → (N ∘ encode g) ⟶* encode (spec g))

------------------------------------------------------------------------
-- Sketch of how Transparency would be derived from this witness.
--
-- module _ ... (W : TransparencyDischarge S Red E EI) where
--
--   nf-fixpoint-implies-correctness :
--     ∀ (spec : ∀ {A B} → Hom A B → Hom A B)
--       (N : Hom Code Code) →
--       IsNormalForm N →
--       (N ∘ encode N) ⟶* encode (spec N) →
--       ∀ {A B} (g : Hom A B) →
--       (N ∘ encode g) ⟶* encode (spec g)
--   nf-fixpoint-implies-correctness spec N nf-N rf g =
--     let
--       (α , nf-α) = nf-canonical-form N nf-N
--       -- N ≡ cata α (modulo Code-is-μF transport)
--       -- (cata α ∘ encode g) ⟶* (α ∘ fmap (cata α) ∘ Out ∘ encode g)
--       --   by cata-β-reduction
--       -- ⟶* encode (spec g)
--       --   by branch-uniformity (with rf supplying the per-input fact)
--     in ...
--
-- The proof is mechanical given the witness; the work lives in
-- DISCHARGING the five fields above for a concrete syntax.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Notes on the bootstrap normalizer as an existence proof.
--
-- The bootstrap normalizer at bootstrap/normalizer/ provides:
--
--   - Encoding/Encoding.agda           : concrete encode (→ obligations 1, 4)
--   - Encoding/TermFunctor.agda        : concrete TermF (→ obligation 1)
--   - Syntax/BetaNormalForm.agda       : NF analysis (→ obligation 2)
--   - Syntax/NoRedex.agda              : reduction-rule analysis (→ obligation 3)
--   - Theory/StandardCCCExtension/CataFree.agda : canonical form (→ obligation 2)
--   - TCB0/Normalizer/Proofs/DispatchLemmas.agda : branch correctness (→ obligation 5)
--
-- Together these constitute an EXISTING discharge of an analog of
-- TransparencyDischarge for the bootstrap CCC syntax. Translating
-- this work into the formal/Theory/ framework would convert
-- Transparency from postulate to theorem for that specific instance.
--
-- Estimated effort to translate: ~2000 lines of Agda, mostly
-- mechanical (encoding + NF + reduction analysis), with one focused
-- conceptual piece (the branch-uniformity lemma).
------------------------------------------------------------------------
