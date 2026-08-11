------------------------------------------------------------------------
-- Theory.RanzowFixpoint.Properties
--
-- Closure / structural lemmas about HasRanzowFixpoint at CCT3.
--
-- These lemmas describe how the RF property interacts with categorical
-- structure (composition, identity, reduction, equational equivalence).
-- Each lemma is parameterized by exactly the operations on _⟶_ / _⟶*_
-- it needs — Theory.Syntax.Reducible itself is intentionally minimal,
-- so this module pays the cost in hypothesis-threading rather than
-- expanding the carrier.
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

module Theory.RanzowFixpoint.Properties where

open import Theory.CCTower using (TowerLevel; CCT3)
open import Theory.Systems.CCT3
open import Theory.Syntax.Reducible using (Reducible)
open import Theory.RanzowFixpoint using (EncodingScheme; HasRanzowFixpoint)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)

------------------------------------------------------------------------
-- Tower level annotation
------------------------------------------------------------------------

applies-to : TowerLevel
applies-to = CCT3

------------------------------------------------------------------------
-- All lemmas parameterize over a fixed CCT3 structure, Reducible
-- carrier, and EncodingScheme.
------------------------------------------------------------------------

module _ (S   : CCT3Structure)
         (Red : Reducible (CCT3Structure.Obj S) (CCT3Structure.Hom S))
         (E   : EncodingScheme S)
         where
  open CCT3Structure S
  open Reducible Red
  open EncodingScheme E

  --------------------------------------------------------------------
  -- (1) Propositional substitutivity in the candidate.
  --
  -- HasRanzowFixpoint is a Set indexed by T : Hom Code Code, so
  -- propositional equality of the candidate transports the property.
  -- Trivial but useful as a building block in larger proofs.
  --------------------------------------------------------------------

  hasRF-cong-T :
    ∀ {T T' : Hom Code Code} →
      T ≡ T' →
      HasRanzowFixpoint S Red E T →
      HasRanzowFixpoint S Red E T'
  hasRF-cong-T refl rf = rf

  --------------------------------------------------------------------
  -- (2) Propositional substitutivity in the encoding.
  --
  -- If the encoding of T is propositionally equal to some other code
  -- e, the RF property transports along the equation.
  --------------------------------------------------------------------

  hasRF-encode-subst :
    ∀ {T : Hom Code Code} {e : Hom Unit Code} →
      encode T ≡ e →
      (T ∘ encode T) ⟶* encode T →
      (T ∘ e) ⟶* e
  hasRF-encode-subst {T} {e} eq rf =
    subst (λ x → (T ∘ x) ⟶* x) eq rf

  --------------------------------------------------------------------
  -- Lemmas requiring _⟶*_ to be reflexive-transitively closed.
  --
  -- The Reducible carrier abstractly leaves _⟶*_ as just a relation,
  -- so we take its closure operations as explicit hypotheses here.
  -- Any concrete instantiation of Reducible discharges these from
  -- the inductive definition of _⟶*_ as the reflexive-transitive
  -- closure of _⟶_.
  --------------------------------------------------------------------

  module _ (⟶*-refl :
             ∀ {A B} (t : Hom A B) → t ⟶* t)
           (⟶*-trans :
             ∀ {A B} {t u v : Hom A B} →
             t ⟶* u → u ⟶* v → t ⟶* v)
           (⟶-incl :
             ∀ {A B} {t u : Hom A B} →
             t ⟶ u → t ⟶* u)
           where

    ------------------------------------------------------------------
    -- (3) Reachability extension.
    --
    -- If T has RF and ⌜T⌝ further reduces to some x, then the full
    -- composition (T ∘ ⌜T⌝) reaches x. Useful for chaining the RF
    -- "self-test" with downstream reductions.
    ------------------------------------------------------------------

    hasRF-extend :
      ∀ {T : Hom Code Code} {x : Hom Unit Code} →
        HasRanzowFixpoint S Red E T →
        encode T ⟶* x →
        (T ∘ encode T) ⟶* x
    hasRF-extend rf p = ⟶*-trans rf p

    ------------------------------------------------------------------
    -- (4) HasRF is reflected by single-step fixpoints.
    --
    -- A single ⟶ step from (T ∘ ⌜T⌝) to ⌜T⌝ is enough to give RF.
    -- (Trivial via inclusion.)
    ------------------------------------------------------------------

    hasRF-from-step :
      ∀ {T : Hom Code Code} →
        (T ∘ encode T) ⟶ encode T →
        HasRanzowFixpoint S Red E T
    hasRF-from-step step = ⟶-incl step

    ------------------------------------------------------------------
    -- (5) HasRF is reflected by definitional fixpoints.
    --
    -- If (T ∘ ⌜T⌝) ≡ ⌜T⌝ propositionally (e.g., when ∘ is realized
    -- as definitional substitution), RF holds vacuously.
    ------------------------------------------------------------------

    hasRF-from-eq :
      ∀ {T : Hom Code Code} →
        (T ∘ encode T) ≡ encode T →
        HasRanzowFixpoint S Red E T
    hasRF-from-eq {T} eq =
      subst (λ x → x ⟶* encode T) (sym eq) (⟶*-refl (encode T))

  --------------------------------------------------------------------
  -- Lemmas requiring composition congruence on _⟶*_.
  --
  -- If a single-step _⟶_ on the left factor of a composition lifts
  -- to a _⟶*_ on the whole composition, we get nontrivial closure
  -- properties. This is a standard rewriting fact, taken as
  -- hypothesis here to keep the carrier minimal.
  --------------------------------------------------------------------

  module _ (⟶*-trans :
             ∀ {A B} {t u v : Hom A B} →
             t ⟶* u → u ⟶* v → t ⟶* v)
           (⟶-cong-∘L :
             ∀ {A B C} {f g : Hom B C} (h : Hom A B) →
             f ⟶ g → (f ∘ h) ⟶* (g ∘ h))
           where

    ------------------------------------------------------------------
    -- (6) Reduction-backwards closure under stable encoding.
    --
    -- If encoding is invariant under single-step reduction of the
    -- candidate (i.e., reductions of T do not change ⌜T⌝ — typical
    -- when encoding factors through normalization), then:
    --
    --   T' ⟶ T  ∧  HasRF T  ⟹  HasRF T'
    --
    -- That is, RF "pulls back" along reductions when encoding is
    -- reduction-stable. Useful for showing that a candidate close to
    -- (but not yet at) a fixpoint inherits the property as it reduces.
    --
    -- The encode-stable hypothesis is genuinely strong: in most
    -- concrete syntaxes, encoding does NOT respect reduction. It
    -- holds, however, for normalized encodings (encode g := encode
    -- (nf g) up to confluence), which is a common design choice for
    -- concrete RF instances.
    ------------------------------------------------------------------

    hasRF-pullback-along-step :
      (encode-stable :
        ∀ {T' T : Hom Code Code} → T' ⟶ T → encode T' ≡ encode T) →
      ∀ {T' T : Hom Code Code} →
        T' ⟶ T →
        HasRanzowFixpoint S Red E T →
        HasRanzowFixpoint S Red E T'
    hasRF-pullback-along-step encode-stable {T'} {T} step rf-T =
      let
        -- step lifted to a ⟶* of compositions, via cong on the left
        comp-step : (T' ∘ encode T') ⟶* (T ∘ encode T')
        comp-step = ⟶-cong-∘L (encode T') step

        -- transport T's RF along the encoding equality
        eq : encode T' ≡ encode T
        eq = encode-stable step

        rf-T-at-T' : (T ∘ encode T') ⟶* encode T'
        rf-T-at-T' =
          subst (λ x → (T ∘ x) ⟶* x) (sym eq) rf-T
      in
        ⟶*-trans comp-step rf-T-at-T'

  --------------------------------------------------------------------
  -- Lemma requiring an identity-elimination reduction.
  --
  -- The identity morphism trivially satisfies RF whenever the
  -- reduction relation has the standard left-identity rule. This
  -- gives a baseline inhabitant of HasRanzowFixpoint.
  --------------------------------------------------------------------

  module _ (id-left-elim :
             ∀ {A B} (f : Hom A B) → (id ∘ f) ⟶ f)
           (⟶-incl :
             ∀ {A B} {t u : Hom A B} →
             t ⟶ u → t ⟶* u)
           where

    ------------------------------------------------------------------
    -- (7) The identity morphism on Code has RF.
    --
    -- id ∘ ⌜id⌝ ⟶ ⌜id⌝ via id-left-elim, hence ⟶* by inclusion.
    --
    -- Note: this is a degenerate inhabitant — id is not a normalizer
    -- in any interesting sense. But it confirms that HasRF is
    -- non-trivially inhabited at every CCT3 instantiation with the
    -- standard reduction.
    ------------------------------------------------------------------

    id-hasRF : HasRanzowFixpoint S Red E id
    id-hasRF = ⟶-incl (id-left-elim (encode id))
