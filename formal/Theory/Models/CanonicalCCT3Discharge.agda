------------------------------------------------------------------------
-- Theory.Models.CanonicalCCT3Discharge
--
-- A first concrete instance discharging Theory.RanzowFixpoint.
-- DischargeSkeleton obligations against the canonical CCT3 syntax
-- (Theory.Syntax.Bootstrap.CCT3.canonical).
--
-- This module discharges obligations 1, 3, and 4 of the discharge
-- skeleton — the structural / inspection obligations.
-- Obligations 2 (canonical NF form) and 5 (branch uniformity)
-- require larger proofs about the term datatype and are deferred
-- to follow-up modules.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

module Theory.Models.CanonicalCCT3Discharge where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3 using (CCT3Structure)
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme)
open import Theory.Encoding.Inductive using (EncodingInductive)

import Theory.Syntax.Bootstrap.CCT3 as Syn

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- The concrete CCT3 structure and reducible carrier we are discharging
-- against. Both come from the existing canonical CCT3 syntax.
------------------------------------------------------------------------

S : CCT3Structure
S = Syn.canonical

Red : Reducible Syn.Ty Syn.Term
Red = Syn.canonical-reducible

------------------------------------------------------------------------
-- OBLIGATION 3 (DischargeSkeleton.cata-β-reduction):
--   cata α ∘ In ⟶* α ∘ fmap (cata α)
--
-- DISCHARGED.
--
-- Direct: the canonical syntax has cata-β as a single-step _⟶_ rule,
-- so it embeds into _⟶*_ via the cons-onto-done construction.
------------------------------------------------------------------------

cata-β-reduction :
  ∀ {F : Syn.Ty → Syn.Ty} {A} (alg : Syn.Term (F A) A) →
  (Syn.cata {F} alg Syn.∘ Syn.In {F})
    Syn.⟶* (alg Syn.∘ Syn.fmap {F} (Syn.cata {F} alg))
cata-β-reduction alg = Syn.cata-β Syn.∷ Syn.done

------------------------------------------------------------------------
-- OBLIGATION 1 (DischargeSkeleton.TermF + Code-is-μF):
--   Pin down Code = μ TermF for an explicit TermF.
--
-- DISCHARGED for the trivial choice TermF = constant Unit.
--
-- Note: This is a degenerate but valid commitment. A non-trivial
-- TermF that distinguishes all term constructors is the natural
-- choice for a real instantiation (cf. bootstrap/normalizer/Encoding/
-- TermFunctor.agda). For the present module we only demonstrate the
-- discharge mechanism — the actual choice of TermF is a matter of
-- the encoding strategy.
------------------------------------------------------------------------

TermF : Syn.Ty → Syn.Ty
TermF X = Syn.Unit                   -- constant functor

Code : Syn.Ty
Code = Syn.μ TermF

Code-is-μF : Code ≡ Syn.μ TermF
Code-is-μF = refl

------------------------------------------------------------------------
-- A trivial encoding scheme.
--
-- encode g = In ∘ terminal — every morphism encodes to the same
-- canonical element of μ TermF.
--
-- This DOES discharge EncodingScheme. It does NOT discharge the
-- faithful field of EncodingInductive (a constant encoding cannot
-- be injective unless ≈ is total, which it is not for canonical
-- CCT3). So this concrete model does NOT yet give a full
-- EncodingInductive — see the note below.
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
-- DISCHARGED for the trivial encoding.
--
-- Under the constant encoding, every morphism (including cata α and
-- α individually) maps to the same syntactic value. The wrapper is
-- the identity function on Hom Unit Code.
--
-- This is the simplest possible witness for obligation 4 and works
-- precisely BECAUSE the encoding is degenerate. A real encoding
-- would have a non-trivial wrapper that places ⌜α⌝ at a specific
-- syntactic position inside ⌜cata α⌝.
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
-- WHAT REMAINS — Status report.
--
-- DISCHARGED HERE:
--   [✓] Obligation 1: TermF = constant Unit, Code = μ TermF.
--   [✓] Obligation 3: cata-β as a single-step ⟶ rule, embedded in ⟶*.
--   [✓] Obligation 4: encoding-cata-positional with identity wrapper
--                     (trivial under constant encoding).
--
-- NOT DISCHARGED HERE:
--   [ ] EncodingInductive.encode-faithful — fails under constant
--       encoding because canonical CCT3's ≈ is not the total relation.
--   [ ] Obligation 2 (canonical NF form) — requires case analysis on
--       all NF Term Code Code values, showing each has cata shape.
--       This is mechanical but lengthy (~14 Term constructors × NF
--       analysis).
--   [ ] Obligation 5 (branch uniformity / parametric content) —
--       requires the genuinely deep parametricity-style argument.
--
-- NEXT STEPS toward a fully discharged Transparency for canonical
-- CCT3:
--   (a) Replace the constant encoding with an injective one (port
--       bootstrap/normalizer/Encoding/Encoding.agda — ~266 lines).
--   (b) Discharge encode-faithful, encode-is-nf, encode-cata-decomposes
--       for the injective encoding (~few hundred lines).
--   (c) Prove canonical NF form for canonical CCT3 (~few hundred
--       lines — the bootstrap normalizer's
--       Theory/StandardCCCExtension/CataFree.agda is the analog).
--   (d) Prove branch uniformity (the deep step — bootstrap
--       normalizer's TCB0/Normalizer/Proofs/DispatchLemmas.agda is
--       the analog).
--
-- Total estimated effort: ~1000-2000 lines of concrete-instance Agda,
-- mechanical for (a)-(c), genuinely deep for (d).
------------------------------------------------------------------------
