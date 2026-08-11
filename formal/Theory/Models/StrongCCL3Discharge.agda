------------------------------------------------------------------------
-- Theory.Models.StrongCCL3Discharge
--
-- Discharge of DischargeSkeleton obligations against the StrongCCL
-- CCT3 syntax (Theory.Syntax.StrongCCL.CCT3.canonical), which uses
-- full βη-reduction with congruence closure (the richer reduction
-- relation that supports adequacy proofs).
--
-- This module discharges the structural / inspection obligations
-- (1, 3, 4) for the StrongCCL syntax. Obligations 2 (canonical NF
-- form) and 5 (branch uniformity) are deferred — same fundamental
-- limitations as the canonical-CCT3 discharge.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

module Theory.Models.StrongCCL3Discharge where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme)
open import Theory.Encoding.Inductive using (EncodingInductive)

import Theory.Syntax.StrongCCL.CCT3 as Syn

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The concrete CCT3 structure and reducible carrier we are discharging
-- against. Both come from the StrongCCL CCT3 syntax.
------------------------------------------------------------------------

S : CCT3Structure
S = Syn.canonical

Red : Reducible Syn.Ty Syn.Term
Red = Syn.canonical-reducible

------------------------------------------------------------------------
-- OBLIGATION 3 (DischargeSkeleton.cata-β-reduction):
--   cata α ∘ In  ⟶*  α ∘ fmap (cata α)
--
-- DISCHARGED.
--
-- Chain of inclusions in the StrongCCL reduction structure:
--   cata-β       : _⟶β-CCT3_
--   from-CCT3-β  : _⟶β-CCT3_  → _⟶β_
--   β-rule       : _⟶β_       → _⟶βη-rules_
--   base         : _⟶βη-rules_ → _⟶βη_  (congruence-closure base case)
--   _∷ done      : _⟶βη_       → _⟶βη*_
------------------------------------------------------------------------

cata-β-reduction :
  ∀ {F : Syn.Ty → Syn.Ty} {A} (alg : Syn.Term (F A) A) →
  (Syn.cata {F} alg Syn.∘ Syn.In {F})
    Syn.⟶βη* (alg Syn.∘ Syn.fmap {F} (Syn.cata {F} alg))
cata-β-reduction alg =
  Syn.βη-Closure.base (Syn.β-rule (Syn.from-CCT3-β Syn.cata-β)) Syn.∷ Syn.done

------------------------------------------------------------------------
-- Companion: out-in and in-out as ⟶βη* steps.
--
-- These are not in the DischargeSkeleton record but are useful as
-- additional concrete-reduction lemmas for downstream proofs.
------------------------------------------------------------------------

out-in-reduction :
  ∀ {F : Syn.Ty → Syn.Ty} →
  (Syn.Out {F} Syn.∘ Syn.In {F}) Syn.⟶βη* Syn.id
out-in-reduction =
  Syn.βη-Closure.base (Syn.β-rule (Syn.from-CCT3-β Syn.out-in)) Syn.∷ Syn.done

in-out-reduction :
  ∀ {F : Syn.Ty → Syn.Ty} →
  (Syn.In {F} Syn.∘ Syn.Out {F}) Syn.⟶βη* Syn.id
in-out-reduction =
  Syn.βη-Closure.base (Syn.β-rule (Syn.from-CCT3-β Syn.in-out)) Syn.∷ Syn.done

------------------------------------------------------------------------
-- OBLIGATION 1 (DischargeSkeleton.TermF + Code-is-μF):
--   Pin down Code = μ TermF.
--
-- DISCHARGED for the trivial choice TermF = constant Unit.
--
-- (Same caveat as in CanonicalCCT3Discharge: a real injective
-- encoding requires a non-trivial TermF — porting the bootstrap
-- normalizer's TermFunctor.agda would discharge this with full
-- structural information.)
------------------------------------------------------------------------

TermF : Syn.Ty → Syn.Ty
TermF X = Syn.Unit

Code : Syn.Ty
Code = Syn.μ TermF

Code-is-μF : Code ≡ Syn.μ TermF
Code-is-μF = refl

------------------------------------------------------------------------
-- A trivial encoding scheme (constant encoding).
--
-- Same caveat as CanonicalCCT3Discharge: this discharges
-- EncodingScheme but NOT the faithfulness field of EncodingInductive
-- (faithfulness would require an injective encoding).
------------------------------------------------------------------------

trivial-encoding : EncodingScheme S
trivial-encoding = record
  { Code   = Code
  ; encode = λ _ → Syn.In Syn.∘ Syn.terminal
  }

------------------------------------------------------------------------
-- OBLIGATION 4 (DischargeSkeleton.encode-cata-positional):
--   ⌜cata α⌝ ≡ wrapper(⌜α⌝) for some wrapper.
--
-- DISCHARGED for the trivial encoding (identity wrapper, since both
-- sides equal In ∘ terminal under constant encoding).
------------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _,_)

private
  open module E = EncodingScheme trivial-encoding using (encode)

encode-cata-positional :
  ∀ {F : Syn.Ty → Syn.Ty} {A} (alg : Syn.Term (F A) A) →
  Σ-syntax (Syn.Term Syn.Unit Code → Syn.Term Syn.Unit Code) λ wrapper →
    encode (Syn.cata {F} alg) ≡ wrapper (encode alg)
encode-cata-positional alg = (λ x → x) , refl

------------------------------------------------------------------------
-- STATUS REPORT for StrongCCL CCT3 discharge.
--
-- DISCHARGED:
--   [✓] Obligation 1: TermF = constant Unit, Code = μ TermF.
--   [✓] Obligation 3: cata-β as a directed ⟶βη* reduction.
--                     Bonus: out-in and in-out reductions provided.
--   [✓] Obligation 4: encode-cata-positional with identity wrapper.
--
-- NOT DISCHARGED:
--   [ ] EncodingInductive.encode-faithful: constant encoding cannot
--       be injective on the StrongCCL.CCT3 ≈ relation.
--   [ ] Obligation 2: requires per-Term-constructor case analysis.
--   [ ] Obligation 5: requires the parametric uniformity argument.
--
-- The two concrete syntaxes in formal/Theory/Syntax/Bootstrap and
-- formal/Theory/Syntax/StrongCCL share the same fundamental
-- limitations:
--   - Both have rich type-indexed Term datatypes that require a
--     non-trivial encoding to satisfy faithfulness.
--   - Both have NF analyses that span ~14 constructors.
--   - Both face the same parametric-uniformity content for
--     branch-uniformity.
--
-- The StrongCCL syntax has the advantage that its reduction relation
-- is the FULL βη-closure with congruence, which is what's needed for
-- the eventual canonical-form analysis (whereas Bootstrap CCT3 uses
-- a simpler one-step β-reduction without explicit congruence rules).
-- So when the canonical-form proof of obligation 2 is undertaken,
-- StrongCCL is the better target.
------------------------------------------------------------------------
