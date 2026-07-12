------------------------------------------------------------------------
-- OCP-0009 · OTT step 4 — QUOTIENT types (the setoid/observational way)
--
-- Quotients are the piece that covers, for Once's needs, what univalence would
-- (plan §6 HOTT-vs-cubical note). In an OBSERVATIONAL setting they are clean and
-- need no HIT machinery: a quotient `A / R` is a carrier `A` whose equality has
-- been COARSENED to `R` — observational equality on the quotient IS the relation.
-- Because equality is already proof-irrelevant (`NbEPOTT` step 2), this is a
-- genuine quotient, not a mere setoid-with-baggage.
--
--   * `[_] : A → A / R`               — the class map;
--   * `eqQ R [a] [b] = a ≈ b`         — the quotient identifies `R`-related reps;
--   * `elim f` descends a `f : A → B` to the quotient, and RESPECTS `R` iff `f`
--     does (`elim-resp`) — the well-definedness obligation, made explicit.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPOTTQ where

open import normalizer.Syntax.Types

------------------------------------------------------------------------
-- Equivalence relations and the quotient they induce.
------------------------------------------------------------------------

record EqRel (A : Set) : Set₁ where
  field
    _≈_    : A → A → Set
    rfl    : ∀ x → x ≈ x
    sym≈   : ∀ {x y} → x ≈ y → y ≈ x
    trans≈ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

-- The quotient carrier: a class wrapping a representative.
record _/_ (A : Set) (R : EqRel A) : Set where
  constructor [_]
  field rep : A

-- Observational equality on the quotient — precisely the relation `R`.
eqQ : {A : Set} (R : EqRel A) → (A / R) → (A / R) → Set
eqQ R [ a ] [ b ] = EqRel._≈_ R a b

-- `eqQ` is an equivalence (inherited from `R`) — the quotient is well-behaved.
eqQ-refl : ∀ {A} (R : EqRel A) (x : A / R) → eqQ R x x
eqQ-refl R [ a ] = EqRel.rfl R a

eqQ-sym : ∀ {A} (R : EqRel A) {x y : A / R} → eqQ R x y → eqQ R y x
eqQ-sym R {[ a ]} {[ b ]} p = EqRel.sym≈ R p

eqQ-trans : ∀ {A} (R : EqRel A) {x y z : A / R} → eqQ R x y → eqQ R y z → eqQ R x z
eqQ-trans R {[ a ]} {[ b ]} {[ c ]} p q = EqRel.trans≈ R p q

------------------------------------------------------------------------
-- Elimination — a function descends to the quotient, and is WELL-DEFINED
-- exactly when it respects the relation.
------------------------------------------------------------------------

elim : ∀ {A} {R : EqRel A} {B : Set} → (A → B) → (A / R) → B
elim f [ a ] = f a

-- Well-definedness / the respect obligation: if `f` maps `R`-related inputs to
-- `RB`-related outputs, then `elim f` maps `eqQ`-related classes to `RB`-related
-- results. (For `RB = eq B` this is exactly "the eliminator respects the
-- quotient" — the coherence a quotient type demands of its eliminator.)
elim-resp : ∀ {A B} {R : EqRel A} (f : A → B) (RB : B → B → Set)
          → (∀ {a b} → EqRel._≈_ R a b → RB (f a) (f b))
          → ∀ {x y} → eqQ R x y → RB (elim {R = R} f x) (elim {R = R} f y)
elim-resp {R = R} f RB resp {[ a ]} {[ b ]} r = resp r

------------------------------------------------------------------------
-- Example — quotient `A × B` by its FIRST projection: the second component is
-- forgotten, so classes differing only there are identified.
------------------------------------------------------------------------

Two : Set
Two = ⊤ ⊎ ⊤

fstEq : EqRel (Two × Two)
fstEq = record
  { _≈_    = λ p q → proj₁ p ≡ proj₁ q
  ; rfl    = λ _ → refl
  ; sym≈   = sym
  ; trans≈ = trans
  }
  where
    proj₁ : Two × Two → Two
    proj₁ (a , _) = a

-- Classes `[(a,b)]` and `[(a,b')]` — same first component, different second —
-- are IDENTIFIED by the quotient (`eqQ` holds by `refl`).
_ : eqQ fstEq [ (inj₁ tt , inj₁ tt) ] [ (inj₁ tt , inj₂ tt) ]
_ = refl

-- A function that reads only the first component RESPECTS the quotient, so it
-- descends well-definedly (`elim-resp` above proves the general obligation).
-- Concretely: the descended `takeFst` agrees on the two identified classes.
takeFst : Two × Two → Two
takeFst (a , _) = a

_ : elim {R = fstEq} takeFst [ (inj₁ tt , inj₁ tt) ]
  ≡ elim {R = fstEq} takeFst [ (inj₁ tt , inj₂ tt) ]
_ = refl
