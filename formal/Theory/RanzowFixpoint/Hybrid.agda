------------------------------------------------------------------------
-- Theory.RanzowFixpoint.Hybrid
--
-- Joint μ-side / ν-side correctness at CCT4.
--
-- At CCT4 a structure has both μ-types (initial algebras) and ν-types
-- (final coalgebras), so it can simultaneously support:
--   - a μ-encoding Code = μ TermF for finite syntax,
--   - a ν-encoding CoCode = ν TermF' for productive coinductive
--     behavior.
--
-- A "hybrid OCP-4" candidate consists of:
--   - T_μ : Code → Code   satisfying HasRanzowFixpoint   (μ-side)
--   - T_ν : CoCode → CoCode satisfying HasCoFixpoint     (ν-side)
--
-- This module bundles the joint scenario and exposes the obvious
-- conjunction theorem: if both single-side correctness theorems
-- apply, the combined transformation is correct in both regimes.
--
-- Rests on the two Established postulates (Transparency + Cotransparency),
-- pulled in via the underlying correctness theorems.
--
-- TOWER LEVEL: CCT4 (ν is required).
------------------------------------------------------------------------

module Theory.RanzowFixpoint.Hybrid where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Systems.CCT4
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.Syntax.Coreducible using (Coreducible)

open import Theory.RanzowFixpoint
  using (EncodingScheme; HasRanzowFixpoint)
open import Theory.RanzowFixpoint.Coinductive
  using (CoEncodingScheme; HasCoFixpoint)
open import Theory.Encoding.Inductive   using (EncodingInductive)
open import Theory.Encoding.Coinductive using (CoEncodingInductive)

import Theory.RanzowFixpoint.FullCorrectness   as μFC
import Theory.RanzowFixpoint.CoFullCorrectness as νFC

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- Projection to CCT3 (μ-side operates at the CCT3 sub-structure).
------------------------------------------------------------------------

to-CCT3 : CCT4Structure → CCT3Structure
to-CCT3 S = CCT4Structure.bccμ S

------------------------------------------------------------------------
-- A Hybrid Bundle: everything needed for joint μ/ν self-verification.
------------------------------------------------------------------------

record HybridBundle (S : CCT4Structure) : Set₁ where
  open CCT4Structure S using (Obj; Hom)
  field
    -- Two reduction/equivalence carriers on the same Hom
    Red    : Reducible Obj Hom
    CoR    : Coreducible Obj Hom
    -- Two encoding schemes
    E-μ    : EncodingScheme (to-CCT3 S)
    E-ν    : CoEncodingScheme S
    -- Two structural-encoding records
    EI-μ   : EncodingInductive (to-CCT3 S) Red E-μ
    CoEI-ν : CoEncodingInductive S CoR E-ν

------------------------------------------------------------------------
-- The Joint Correctness Theorem.
--
-- Given a CCT4 structure with a HybridBundle, two specs (one for
-- each side), two candidate transformations (one for each side)
-- each satisfying the respective fixpoint and structural conditions,
-- conclude joint correctness on all encoded inputs of either kind.
--
-- The proof is just the conjunction of the two underlying theorems
-- — no novel content beyond the bundling. The value is a single
-- statement that the joint OCP-4 holds.
------------------------------------------------------------------------

module _ (S : CCT4Structure) (H : HybridBundle S) where
  open CCT4Structure S
  open HybridBundle H
  open Reducible Red
  open Coreducible CoR
  open EncodingScheme E-μ
    using () renaming (Code to Code-μ; encode to encode-μ)
  open CoEncodingScheme E-ν
    using () renaming (CoCode to Code-ν; co-encode to encode-ν)

  joint-correctness :
    ∀ (spec-μ  : ∀ {A B} → Hom A B → Hom A B)
      (spec-ν  : ∀ {A B} → Hom A B → Hom A B)
      (T-μ     : Hom Code-μ Code-μ)
      (T-ν     : Hom Code-ν Code-ν) →
      -- μ-side hypotheses
      IsNormalForm T-μ →
      spec-μ T-μ ≡ T-μ →
      HasRanzowFixpoint (to-CCT3 S) Red E-μ T-μ →
      -- ν-side hypotheses
      IsProductive T-ν →
      spec-ν T-ν ≡ T-ν →
      HasCoFixpoint S CoR E-ν T-ν →
      -- Joint conclusion: correctness on every input of either kind
      (∀ {A B} (g : Hom A B) → (T-μ ∘ encode-μ g) ⟶* encode-μ (spec-μ g))
      ∧
      (∀ {A B} (g : Hom A B) → (T-ν ∘ encode-ν g) ≈ω encode-ν (spec-ν g))
  joint-correctness spec-μ spec-ν T-μ T-ν
                    nf-Tμ specμTμ rfμ
                    pr-Tν specνTν cfν =
      μFC.fixpoint-implies-correctness (to-CCT3 S) Red E-μ EI-μ
        spec-μ T-μ nf-Tμ specμTμ rfμ
    , νFC.cofixpoint-implies-correctness S CoR E-ν CoEI-ν
        spec-ν T-ν pr-Tν specνTν cfν

------------------------------------------------------------------------
-- Open research direction: a natural map from μ to ν.
--
-- Categorically, every initial algebra μ F embeds into the final
-- coalgebra ν F via the unique morphism guaranteed by initiality
-- (when both exist over the same functor F):
--
--    embed-μν : μ F → ν F
--    embed-μν = ana (... unfold one layer using μ's recursion ...)
--
-- If a CCT4 structure provides such an embedding, AND the μ- and
-- ν-encodings are compatible (i.e., embed-μν ∘ encode-μ ≡ encode-ν
-- modulo bisim), then μ-side correctness should LIFT to ν-side
-- correctness automatically — a single μ-RF observation would
-- discharge ν-RF as well.
--
-- This bridge is not formalized here because:
--   (a) the natural map embed-μν is not part of the Systems.CCT4
--       record; concrete instances may or may not provide it,
--   (b) the compatibility condition is structural and depends on
--       the specific encoding choice,
--   (c) without a concrete syntax we cannot verify any of the
--       coherence diagrams the bridge would require.
--
-- This is the natural place to add such a bridge once the μ-side
-- gets its first concrete instantiation.
------------------------------------------------------------------------
