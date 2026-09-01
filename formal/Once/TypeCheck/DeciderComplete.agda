-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.DeciderComplete — the deciders DECIDE their properties.
--
-- PLAN 0.80 Phase A. The typing rules used to carry premises like
-- `wellFormedF? F ≡ just wfF` and `isGround schema ≡ inj₂ tt` — equations
-- about a DECISION PROCEDURE, sitting in the language definition. The rules
-- now carry the PROPERTIES (`WellFormedF F`, `¬ (Ground schema)`) instead, and
-- this module holds what makes the two interchangeable, proven once:
--
--   * the elaborator has the decider's answer and owes the rule a property
--     (`isGround-inj₂-¬Ground`);
--   * completeness has the rule's property and owes the elaborator's dispatch
--     an answer (`wellFormedF?-complete`, `isGround-complete`).
--
-- Both directions are the same fact — the decider is sound and complete for
-- its property — which is exactly why the language definition never needed to
-- name it.
--
-- Its own module rather than `Once.Functor.Decide` / `Once.Type`: those sit
-- below the judgment, so editing them re-checks the whole tree. Only the
-- elaborator and the completeness proof need these.
------------------------------------------------------------------------

module Once.TypeCheck.DeciderComplete where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; subst)

open import Once.Type using (PolyType; PolyFunctor; Ground; GroundF; isGround; isGroundF;
  both-ground;
  PUnit; PVoid; PInt; PFloat; PStr; PBuffer; PTVar; _P*_; _P+_; _P⇒[_]_; PEff;
  Pμ-type; Pν-type; PK; PId; _P⊕_; _P⊗_)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod;
  WellFormedF-irrelevant)
open import Once.Functor.Decide using (wellFormedF?; isBaseType?; isBaseType?-complete)

------------------------------------------------------------------------
-- `wellFormedF?` is complete for `WellFormedF` (the `isBaseType?-complete`
-- pattern, one level up).
------------------------------------------------------------------------

wellFormedF?-complete : ∀ {F} → WellFormedF F → ∃[ w ] wellFormedF? F ≡ just w
wellFormedF?-complete (wf-K bA) with isBaseType?-complete bA
... | (b , eq) rewrite eq = wf-K b , refl
wellFormedF?-complete wf-Id = wf-Id , refl
wellFormedF?-complete (wf-Sum wF wG)
  with wellFormedF?-complete wF | wellFormedF?-complete wG
... | (f , eqF) | (g , eqG) rewrite eqF | eqG = wf-Sum f g , refl
wellFormedF?-complete (wf-Prod wF wG)
  with wellFormedF?-complete wF | wellFormedF?-complete wG
... | (f , eqF) | (g , eqG) rewrite eqF | eqG = wf-Prod f g , refl

-- The form the proofs use: the decider's answer AT the derivation's own
-- witness. `WellFormedF-irrelevant` (already proven next to the definition) is
-- what lets the two be identified — which is the whole reason the rule never
-- needed to pin one of them.
wellFormedF?-complete-at : ∀ {F} (w : WellFormedF F) → wellFormedF? F ≡ just w
wellFormedF?-complete-at w with wellFormedF?-complete w
... | (w' , eq') rewrite WellFormedF-irrelevant w' w = eq'

------------------------------------------------------------------------
-- `isGround` is complete for `Ground`.
--
-- `both-ground` returns `inj₁` exactly when both arguments do, so each binary
-- case is the two IHs rewritten. Mutual with the functor half, mirroring
-- `Ground`/`GroundF` themselves.
------------------------------------------------------------------------

mutual
  isGroundF-complete : ∀ (F : PolyFunctor) → GroundF F → ∃[ g ] isGroundF F ≡ inj₁ g
  isGroundF-complete (PK A) gA = isGround-complete A gA
  isGroundF-complete PId _ = tt , refl
  isGroundF-complete (F P⊕ G) (gF , gG)
    with isGroundF-complete F gF | isGroundF-complete G gG
  ... | (f , eqF) | (g , eqG) rewrite eqF | eqG = (f , g) , refl
  isGroundF-complete (F P⊗ G) (gF , gG)
    with isGroundF-complete F gF | isGroundF-complete G gG
  ... | (f , eqF) | (g , eqG) rewrite eqF | eqG = (f , g) , refl

  isGround-complete : ∀ (A : PolyType) → Ground A → ∃[ g ] isGround A ≡ inj₁ g
  isGround-complete PUnit   _ = tt , refl
  isGround-complete PVoid   _ = tt , refl
  isGround-complete PInt    _ = tt , refl
  isGround-complete PFloat  _ = tt , refl
  isGround-complete PStr    _ = tt , refl
  isGround-complete PBuffer _ = tt , refl
  isGround-complete (A P* B) (gA , gB)
    with isGround-complete A gA | isGround-complete B gB
  ... | (a , eqA) | (b , eqB) rewrite eqA | eqB = (a , b) , refl
  isGround-complete (A P+ B) (gA , gB)
    with isGround-complete A gA | isGround-complete B gB
  ... | (a , eqA) | (b , eqB) rewrite eqA | eqB = (a , b) , refl
  isGround-complete (A P⇒[ q ] B) (gA , gB)
    with isGround-complete A gA | isGround-complete B gB
  ... | (a , eqA) | (b , eqB) rewrite eqA | eqB = (a , b) , refl
  isGround-complete (PEff A B) (gA , gB)
    with isGround-complete A gA | isGround-complete B gB
  ... | (a , eqA) | (b , eqB) rewrite eqA | eqB = (a , b) , refl
  isGround-complete (Pμ-type F) gF = isGroundF-complete F gF
  isGround-complete (Pν-type F) gF = isGroundF-complete F gF
  -- The ONE non-ground shape: `Ground (PTVar _) = ⊥`, so the witness refutes.
  isGround-complete (PTVar _) ()

------------------------------------------------------------------------
-- …and therefore its `inj₂` branch REFUTES the property. This is the
-- direction the elaborator needs: it has the decider's answer and owes the
-- typing rule a `¬ (Ground schema)`.
------------------------------------------------------------------------

isGround-inj₂-¬Ground : ∀ (A : PolyType) → isGround A ≡ inj₂ tt → ¬ (Ground A)
isGround-inj₂-¬Ground A eq g with isGround-complete A g
... | (g' , eq') rewrite eq' with eq
...   | ()

-- The converse, for completeness proofs that must show the elaborator's
-- dispatch takes the `inj₂` branch: `isGround A` is a sum, so refuting
-- `inj₁` leaves `inj₂ tt`.
¬Ground-isGround-inj₂ : ∀ (A : PolyType) → ¬ (Ground A) → isGround A ≡ inj₂ tt
¬Ground-isGround-inj₂ A ¬g with isGround A
... | inj₁ g   = ⊥-elim (¬g g)
... | inj₂ tt  = refl

------------------------------------------------------------------------
-- `Ground` is a PROPOSITION.
--
-- It is built from `⊤`, `_×_` and `⊥`, so any two witnesses agree. Needed
-- because the rule now carries a witness that is no longer pinned to the
-- decider's output: completeness recovers the decider's witness and must
-- identify it with the derivation's.
------------------------------------------------------------------------

mutual
  GroundF-irrelevant : ∀ (F : PolyFunctor) (g₁ g₂ : GroundF F) → g₁ ≡ g₂
  GroundF-irrelevant (PK A) g₁ g₂ = Ground-irrelevant A g₁ g₂
  GroundF-irrelevant PId _ _ = refl
  GroundF-irrelevant (F P⊕ G) (a₁ , b₁) (a₂ , b₂) =
    cong₂ _,_ (GroundF-irrelevant F a₁ a₂) (GroundF-irrelevant G b₁ b₂)
  GroundF-irrelevant (F P⊗ G) (a₁ , b₁) (a₂ , b₂) =
    cong₂ _,_ (GroundF-irrelevant F a₁ a₂) (GroundF-irrelevant G b₁ b₂)

  Ground-irrelevant : ∀ (A : PolyType) (g₁ g₂ : Ground A) → g₁ ≡ g₂
  Ground-irrelevant PUnit   _ _ = refl
  Ground-irrelevant PVoid   _ _ = refl
  Ground-irrelevant PInt    _ _ = refl
  Ground-irrelevant PFloat  _ _ = refl
  Ground-irrelevant PStr    _ _ = refl
  Ground-irrelevant PBuffer _ _ = refl
  Ground-irrelevant (A P* B) (a₁ , b₁) (a₂ , b₂) =
    cong₂ _,_ (Ground-irrelevant A a₁ a₂) (Ground-irrelevant B b₁ b₂)
  Ground-irrelevant (A P+ B) (a₁ , b₁) (a₂ , b₂) =
    cong₂ _,_ (Ground-irrelevant A a₁ a₂) (Ground-irrelevant B b₁ b₂)
  Ground-irrelevant (A P⇒[ q ] B) (a₁ , b₁) (a₂ , b₂) =
    cong₂ _,_ (Ground-irrelevant A a₁ a₂) (Ground-irrelevant B b₁ b₂)
  Ground-irrelevant (PEff A B) (a₁ , b₁) (a₂ , b₂) =
    cong₂ _,_ (Ground-irrelevant A a₁ a₂) (Ground-irrelevant B b₁ b₂)
  Ground-irrelevant (Pμ-type F) g₁ g₂ = GroundF-irrelevant F g₁ g₂
  Ground-irrelevant (Pν-type F) g₁ g₂ = GroundF-irrelevant F g₁ g₂
  Ground-irrelevant (PTVar _) () _

-- The form completeness actually uses: the decider's own witness, retyped as
-- the derivation's.
isGround-complete-at : ∀ (A : PolyType) (g : Ground A) → isGround A ≡ inj₁ g
isGround-complete-at A g with isGround-complete A g
... | (g' , eq') = subst (λ z → isGround A ≡ inj₁ z) (Ground-irrelevant A g' g) eq'
