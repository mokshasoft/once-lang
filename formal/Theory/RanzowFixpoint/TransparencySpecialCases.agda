------------------------------------------------------------------------
-- Theory.RanzowFixpoint.TransparencySpecialCases
--
-- Provable special cases of Transparency.
--
-- The Established postulate Theory.Established.Transparency states:
--
--   For NF N, single-point fixpoint at N implies universal correctness:
--   (N ∘ ⌜N⌝) ⟶* ⌜spec N⌝  ⟹  ∀g. (N ∘ ⌜g⌝) ⟶* ⌜spec g⌝.
--
-- That postulate is genuinely deep at the abstract level (requires
-- syntactic uniformity / parametricity, formalized by induction on
-- the canonical NF form which we have not pinned down abstractly).
-- However, several SPECIAL CASES are provable from the existing
-- abstract structure plus minimal extra hypotheses on the reduction
-- relation. This module collects them, demonstrating that
-- Transparency is non-vacuous and that downstream consumers working
-- in those cases do NOT need to invoke the postulate.
--
-- Each special case takes its required reduction laws as explicit
-- hypotheses, mirroring the Properties.agda style.
--
-- Each case rests on the reduction laws it takes as hypotheses, and on
-- nothing else — in particular it stands independently of
-- Theory.Established.Transparency.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.TransparencySpecialCases where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- All cases parameterize over a fixed CCT3 + Reducible + Encoding.
------------------------------------------------------------------------

module _ (S   : CCT3Structure)
         (Red : Reducible (CCT3Structure.Obj S) (CCT3Structure.Hom S))
         (E   : EncodingScheme S)
         where
  open CCT3Structure S
  open Reducible Red
  open EncodingScheme E

  --------------------------------------------------------------------
  -- Special Case 1: N is the identity morphism.
  --
  -- When N = id and spec respects identity-on-the-encoding-of-id
  -- (i.e., spec id = id), Transparency reduces to: id is correct on
  -- every encoded input under the identity-spec interpretation.
  --
  -- This is provable from a single hypothesis: that the reduction
  -- relation has identity-elimination as a step. No deep parametric
  -- content needed.
  --
  -- HYPOTHESES:
  --   ⟶-incl       : single-step ⟶ embeds into ⟶*
  --   id-left-elim : id ∘ f ⟶ f for every f
  --
  -- HYPOTHESES ON spec:
  --   spec must agree with the identity on every input:
  --     spec g ≡ g for all g
  --   This is the "identity-spec" — N = id is correct only relative
  --   to a spec that also computes the identity.
  --------------------------------------------------------------------

  module _ (⟶-incl :
             ∀ {A B} {t u : Hom A B} → t ⟶ u → t ⟶* u)
           (id-left-elim :
             ∀ {A B} (f : Hom A B) → (id ∘ f) ⟶ f)
           where

    transparency-id-case :
      ∀ (spec : ∀ {A B} → Hom A B → Hom A B) →
        (∀ {A B} (g : Hom A B) → spec g ≡ g) →
        -- spec-is-identity
        (∀ {A B} (g : Hom A B) → (id ∘ encode g) ⟶* encode (spec g))
    transparency-id-case spec spec-is-id g =
      subst (λ x → (id ∘ encode g) ⟶* encode x)
            (sym (spec-is-id g))
            (⟶-incl (id-left-elim (encode g)))

  --------------------------------------------------------------------
  -- Special Case 2: spec is constant on a single value.
  --
  -- When spec g = c for all g (some fixed c, e.g., a "constant
  -- normalizer" specification), Transparency reduces to: N
  -- universally produces ⌜c⌝.
  --
  -- This holds iff (N ∘ encode g) ⟶* encode c for all g, which is
  -- precisely the conclusion. So under a constant spec, the
  -- universal claim is equivalent to having the path uniformly for
  -- all g.
  --
  -- The interesting fact is that if N additionally has the structure
  -- "ignore input, produce constant output" (i.e., N = c-out ∘
  -- terminal for some c-out : Unit → Code, where terminal absorbs the
  -- input), then universal correctness follows from reduction laws.
  --
  -- We don't formalize the "ignore-input" structure here — it depends
  -- on which CCC laws are oriented in the reduction. The point is
  -- that constant-spec Transparency does NOT require the deep
  -- parametricity content; it's a structural fact about how N
  -- absorbs its argument.
  --------------------------------------------------------------------

  -- (Statement only — proof depends on the structure of N's
  -- input-absorption, which is concrete-syntax-specific. Provided
  -- here as a placeholder pointing to where the discharge happens.)

  --------------------------------------------------------------------
  -- Special Case 3: encoding is constant.
  --
  -- When encode g ≡ encode g' for all g, g' (a degenerate but valid
  -- encoding scheme — e.g., when Code = Unit), the universal claim
  -- collapses to a single-point claim.
  --
  -- Specifically: if encode is a constant function, then
  --   ∀g. (N ∘ encode g) ⟶* encode (spec g)
  -- is equivalent to
  --   (N ∘ encode T) ⟶* encode (spec T)
  -- (the RF-with-spec hypothesis itself).
  --
  -- So under a constant encoding, the postulate's hypothesis IS its
  -- conclusion — Transparency is trivially provable.
  --
  -- This is a degenerate case but useful: it confirms the postulate
  -- is consistent (any model with a constant encoding satisfies it).
  --------------------------------------------------------------------

  module _ (encode-constant :
             ∀ {A B C D} (g : Hom A B) (h : Hom C D) →
             encode g ≡ encode h)
           where

    transparency-constant-encoding :
      ∀ (spec : ∀ {A B} → Hom A B → Hom A B)
        (N : Hom Code Code)
        (T₀ : Hom Code Code) →
        -- Single-point fixpoint at T₀
        (N ∘ encode T₀) ⟶* encode (spec T₀) →
        -- Conclusion: universal correctness
        (∀ {A B} (g : Hom A B) → (N ∘ encode g) ⟶* encode (spec g))
    transparency-constant-encoding spec N T₀ rf {A} {B} g =
      let
        -- transport the path along constant-encoding equalities
        eq-arg : encode T₀ ≡ encode g
        eq-arg = encode-constant T₀ g

        eq-spec : encode (spec T₀) ≡ encode (spec g)
        eq-spec = encode-constant (spec T₀) (spec g)

        -- substitute the source
        step1 : (N ∘ encode g) ⟶* encode (spec T₀)
        step1 = subst (λ x → (N ∘ x) ⟶* encode (spec T₀)) eq-arg rf

        -- substitute the target
        step2 : (N ∘ encode g) ⟶* encode (spec g)
        step2 = subst (λ x → (N ∘ encode g) ⟶* x) eq-spec step1
      in
        step2

  --------------------------------------------------------------------
  -- What remains in the deep postulate.
  --
  -- The cases above show Transparency is provable when:
  --   - N is the identity (Case 1), or
  --   - the encoding is constant (Case 3).
  --
  -- The genuinely deep content of Transparency is what's left:
  --
  --   Given a NON-IDENTITY N and a NON-CONSTANT encoding, single-
  --   point correctness does propagate to universal correctness.
  --
  -- This residual claim requires either:
  --   (a) Concrete syntactic structure that lets us induct over the
  --       encoded input's shape (i.e., committing to Code = μ TermF
  --       for a specific TermF and providing the corresponding
  --       induction principle), OR
  --   (b) A parametricity-style theorem about CCC normal forms.
  --
  -- Both routes require structure beyond the abstract CCT3Structure
  -- + Reducible + EncodingScheme stack. Hence Transparency remains
  -- postulated at the abstract level; its discharge is a concrete-
  -- instantiation obligation.
  --------------------------------------------------------------------
