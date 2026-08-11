------------------------------------------------------------------------
-- Theory.RanzowFixpoint.CotransparencySpecialCases
--
-- Provable special cases of Cotransparency.
--
-- Coinductive sibling of Theory.RanzowFixpoint.TransparencySpecialCases.
-- See that module's docstring for the rationale; this file provides
-- the dual results for the ν-side.
--
-- The Established postulate Theory.Established.Cotransparency states:
--
--   For productive T, single-point bisim-fixpoint at T implies
--   universal bisim-correctness:
--   (T ∘ ⌜T⌝ω) ≈ω ⌜cospec T⌝ω  ⟹  ∀g. (T ∘ ⌜g⌝ω) ≈ω ⌜cospec g⌝ω.
--
-- That postulate is the dual of Transparency and shares its deep
-- parametric content. Several SPECIAL CASES are provable from
-- abstract structure without invoking Cotransparency:
--
--   (1) T is the identity morphism with cospec ≡ identity.
--   (2) The co-encoding is constant (degenerate but consistent).
--
-- Each case takes its required bisimilarity laws as explicit
-- hypotheses.
--
-- Each case rests on the bisimilarity laws it takes as hypotheses, and on
-- nothing else — in particular it stands independently of
-- Theory.Established.Cotransparency.
--
-- TOWER LEVEL: CCT4.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.CotransparencySpecialCases where

open import Theory.CCTower using (TowerLevel; CCT4)
open import Theory.Systems.CCT4
open import Theory.Syntax.Coreducible using (Coreducible)
open import Theory.RanzowFixpoint.Coinductive using (CoEncodingScheme)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT4

------------------------------------------------------------------------
-- All cases parameterize over a fixed CCT4 + Coreducible + CoEncoding.
------------------------------------------------------------------------

module _ (S    : CCT4Structure)
         (CoR  : Coreducible (CCT4Structure.Obj S) (CCT4Structure.Hom S))
         (E    : CoEncodingScheme S)
         where
  open CCT4Structure S
  open Coreducible CoR
  open CoEncodingScheme E

  --------------------------------------------------------------------
  -- Special Case 1: T is the identity morphism.
  --
  -- When T = id and cospec ≡ identity, Cotransparency reduces to:
  -- id is bisim-correct on every co-encoded input under the
  -- identity-cospec interpretation.
  --
  -- HYPOTHESES:
  --   ≈ω-refl       : bisim is reflexive
  --   id-bisim-elim : id ∘ f ≈ω f for every f
  --
  -- HYPOTHESES ON cospec:
  --   cospec must agree with the identity on every input:
  --     cospec g ≡ g for all g
  --------------------------------------------------------------------

  module _ (≈ω-refl :
             ∀ {A B} (t : Hom A B) → t ≈ω t)
           (id-bisim-elim :
             ∀ {A B} (f : Hom A B) → (id ∘ f) ≈ω f)
           where

    cotransparency-id-case :
      ∀ (cospec : ∀ {A B} → Hom A B → Hom A B) →
        (∀ {A B} (g : Hom A B) → cospec g ≡ g) →
        -- cospec-is-identity
        (∀ {A B} (g : Hom A B) → (id ∘ co-encode g) ≈ω co-encode (cospec g))
    cotransparency-id-case cospec cospec-is-id g =
      subst (λ x → (id ∘ co-encode g) ≈ω co-encode x)
            (sym (cospec-is-id g))
            (id-bisim-elim (co-encode g))

  --------------------------------------------------------------------
  -- Special Case 2: co-encoding is constant.
  --
  -- When co-encode g ≡ co-encode g' for all g, g' (a degenerate but
  -- valid co-encoding scheme), the universal claim collapses to a
  -- single-point claim.
  --
  -- Specifically: under a constant co-encoding, the postulate's
  -- hypothesis IS its conclusion — Cotransparency is trivially
  -- provable.
  --
  -- This confirms the postulate is consistent: any model with a
  -- constant co-encoding satisfies it.
  --------------------------------------------------------------------

  module _ (co-encode-constant :
             ∀ {A B C D} (g : Hom A B) (h : Hom C D) →
             co-encode g ≡ co-encode h)
           where

    cotransparency-constant-encoding :
      ∀ (cospec : ∀ {A B} → Hom A B → Hom A B)
        (T : Hom CoCode CoCode)
        (T₀ : Hom CoCode CoCode) →
        -- Single-point bisim-fixpoint at T₀
        (T ∘ co-encode T₀) ≈ω co-encode (cospec T₀) →
        -- Conclusion: universal bisim-correctness
        (∀ {A B} (g : Hom A B) → (T ∘ co-encode g) ≈ω co-encode (cospec g))
    cotransparency-constant-encoding cospec T T₀ cf {A} {B} g =
      let
        eq-arg : co-encode T₀ ≡ co-encode g
        eq-arg = co-encode-constant T₀ g

        eq-cospec : co-encode (cospec T₀) ≡ co-encode (cospec g)
        eq-cospec = co-encode-constant (cospec T₀) (cospec g)

        step1 : (T ∘ co-encode g) ≈ω co-encode (cospec T₀)
        step1 = subst (λ x → (T ∘ x) ≈ω co-encode (cospec T₀)) eq-arg cf

        step2 : (T ∘ co-encode g) ≈ω co-encode (cospec g)
        step2 = subst (λ x → (T ∘ co-encode g) ≈ω x) eq-cospec step1
      in
        step2

  --------------------------------------------------------------------
  -- What remains in the deep postulate.
  --
  -- The cases above show Cotransparency is provable when:
  --   - T is the identity (Case 1), or
  --   - the co-encoding is constant (Case 2).
  --
  -- The genuinely deep content of Cotransparency is what's left:
  --
  --   Given a NON-IDENTITY productive T and a NON-CONSTANT
  --   co-encoding, single-point bisim-correctness DOES propagate to
  --   universal bisim-correctness.
  --
  -- This residual claim requires either:
  --   (a) Concrete coinductive structure that lets us co-induct over
  --       the co-encoded input's productive observations (i.e.,
  --       committing to CoCode = ν TermF for a specific TermF and
  --       providing the corresponding coinduction principle), OR
  --   (b) A coalgebraic uniformity theorem about CCT4 productive
  --       morphisms.
  --
  -- Both routes require structure beyond the abstract CCT4Structure
  -- + Coreducible + CoEncodingScheme stack. Hence Cotransparency
  -- remains postulated at the abstract level.
  --------------------------------------------------------------------
