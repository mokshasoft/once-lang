------------------------------------------------------------------------
-- Theory.Syntax.Convertibility
--
-- Generic construction of an equivalence relation from a (possibly
-- directed) reduction relation: the smallest reflexive-symmetric-
-- transitive closure.
--
-- This is what a concrete Syntax uses to define its `_≈_` field when
-- instantiating a Systems.CCT* record. Once `≈` contains `⟶`, every
-- CCT* rule (which is a single reduction step) immediately becomes
-- an equation, so the Systems laws are discharged straightforwardly.
--
-- Two sub-modules:
--   Plain    : for un-indexed carriers A (e.g., testing, scratch).
--   Indexed  : for doubly-indexed Hom I → I → Set (typed morphisms).
--              This is what Syntax/CCT* uses to build its _≈_ out of
--              its reduction relation.
--
-- NOTE: neither version makes `≈` a congruence by itself — congruence
-- of `≈` under composition / pairing / currying follows from the
-- congruence of the underlying `⟶` relation (i.e., `⟶` must already
-- include congruence rules, which is the case for every Syntax in
-- this project obtained as a congruence closure of base rules).
------------------------------------------------------------------------

module Theory.Syntax.Convertibility where

------------------------------------------------------------------------
-- Plain version: for un-indexed carriers.
------------------------------------------------------------------------

module Plain {A : Set} (_⟶_ : A → A → Set) where

  data _≈_ : A → A → Set where
    ≈-refl  : ∀ {x}     → x ≈ x
    ≈-step  : ∀ {x y z} → x ⟶ y → y ≈ z → x ≈ z
    ≈-back  : ∀ {x y z} → y ⟶ x → y ≈ z → x ≈ z

  ≈-snoc-step : ∀ {x y z} → x ≈ y → y ⟶ z → x ≈ z
  ≈-snoc-step ≈-refl        r = ≈-step r ≈-refl
  ≈-snoc-step (≈-step r' e) r = ≈-step r' (≈-snoc-step e r)
  ≈-snoc-step (≈-back r' e) r = ≈-back r' (≈-snoc-step e r)

  ≈-snoc-back : ∀ {x y z} → x ≈ y → z ⟶ y → x ≈ z
  ≈-snoc-back ≈-refl        r = ≈-back r ≈-refl
  ≈-snoc-back (≈-step r' e) r = ≈-step r' (≈-snoc-back e r)
  ≈-snoc-back (≈-back r' e) r = ≈-back r' (≈-snoc-back e r)

  ≈-sym : ∀ {x y} → x ≈ y → y ≈ x
  ≈-sym ≈-refl        = ≈-refl
  ≈-sym (≈-step r e)  = ≈-snoc-back (≈-sym e) r
  ≈-sym (≈-back r e)  = ≈-snoc-step (≈-sym e) r

  ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans ≈-refl       yz = yz
  ≈-trans (≈-step r e) yz = ≈-step r (≈-trans e yz)
  ≈-trans (≈-back r e) yz = ≈-back r (≈-trans e yz)

  step-to-≈ : ∀ {x y} → x ⟶ y → x ≈ y
  step-to-≈ r = ≈-step r ≈-refl

  back-to-≈ : ∀ {x y} → y ⟶ x → x ≈ y
  back-to-≈ r = ≈-back r ≈-refl

------------------------------------------------------------------------
-- Indexed version: for doubly-indexed carriers
-- (Hom : I → I → Set, morphism reduction).
------------------------------------------------------------------------

module Indexed
  {I : Set}
  (Hom : I → I → Set)
  (_⟶_ : ∀ {A B} → Hom A B → Hom A B → Set)
  where

  data _≈_ : ∀ {A B} → Hom A B → Hom A B → Set where
    ≈-refl  : ∀ {A B} {x : Hom A B}         → x ≈ x
    ≈-step  : ∀ {A B} {x y z : Hom A B}     → x ⟶ y → y ≈ z → x ≈ z
    ≈-back  : ∀ {A B} {x y z : Hom A B}     → y ⟶ x → y ≈ z → x ≈ z

  ≈-snoc-step : ∀ {A B} {x y z : Hom A B} → x ≈ y → y ⟶ z → x ≈ z
  ≈-snoc-step ≈-refl        r = ≈-step r ≈-refl
  ≈-snoc-step (≈-step r' e) r = ≈-step r' (≈-snoc-step e r)
  ≈-snoc-step (≈-back r' e) r = ≈-back r' (≈-snoc-step e r)

  ≈-snoc-back : ∀ {A B} {x y z : Hom A B} → x ≈ y → z ⟶ y → x ≈ z
  ≈-snoc-back ≈-refl        r = ≈-back r ≈-refl
  ≈-snoc-back (≈-step r' e) r = ≈-step r' (≈-snoc-back e r)
  ≈-snoc-back (≈-back r' e) r = ≈-back r' (≈-snoc-back e r)

  ≈-sym : ∀ {A B} {x y : Hom A B} → x ≈ y → y ≈ x
  ≈-sym ≈-refl        = ≈-refl
  ≈-sym (≈-step r e)  = ≈-snoc-back (≈-sym e) r
  ≈-sym (≈-back r e)  = ≈-snoc-step (≈-sym e) r

  ≈-trans : ∀ {A B} {x y z : Hom A B} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans ≈-refl       yz = yz
  ≈-trans (≈-step r e) yz = ≈-step r (≈-trans e yz)
  ≈-trans (≈-back r e) yz = ≈-back r (≈-trans e yz)

  step-to-≈ : ∀ {A B} {x y : Hom A B} → x ⟶ y → x ≈ y
  step-to-≈ r = ≈-step r ≈-refl

  back-to-≈ : ∀ {A B} {x y : Hom A B} → y ⟶ x → x ≈ y
  back-to-≈ r = ≈-back r ≈-refl
