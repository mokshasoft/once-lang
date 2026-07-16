------------------------------------------------------------------------
-- OCP-0009 · LINEARIZATION step 1 — FOX'S THEOREM, machine-checked
--
-- The mathematical heart of the linearization bridge (PATHS.md, "Linearizing
-- the real core"). The real IR is a CARTESIAN closed category; its manual
-- memory management (`AllocMode` on every intro, `free-heap`) is the tax of
-- cartesianness — duplication is implicit, so lifetimes are not structural.
--
-- Fox's theorem is the factorization that removes the tax: a cartesian
-- category is exactly a symmetric monoidal category in which every object
-- carries a COMONOID (`dup : A → A⊗A`, `drop : A → I`) NATURALLY (every
-- morphism is a comonoid homomorphism — the "uniformity" / affine-relevant
-- condition). This module proves the load-bearing direction: given a linear
-- SMC + a natural comonoid, the CARTESIAN operations are DEFINABLE and their
-- universal laws are THEOREMS:
--
--   * `⟨_,_⟩ = (f ⊗ g) ∘ dup`     — pairing = duplicate then act
--   * `fstₗ  = ρ ∘ (id ⊗ drop)`   — projection = drop the other factor
--   * `sndₗ  = λ ∘ (drop ⊗ id)`
--   * `fox-fst`/`fox-snd`         — the β-laws `fstₗ ∘ ⟨f,g⟩ ≈ f`, `… ≈ g`
--   * `fox-terminal`              — `drop` is the unique map to `I`
--     (`I` is TERMINAL): the categorical content of "a value may be dropped".
--
-- So `⟨_,_⟩`/`fst`/`snd`/`terminal` are NOT primitive — they are a comonoid
-- layer above a linear core. The dividend (PATHS.md): in the linear core a
-- value is used exactly once, so `AllocMode` collapses to the single genuine
-- sharing point, `dup`. Everything here is a hypothesis-threaded theorem —
-- no postulate — so it holds for ANY such structure, in particular the one
-- the compiler's cartesian IR factors through.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPLinFox where

------------------------------------------------------------------------
-- A symmetric monoidal category with a natural comonoid (only the fields
-- Fox's projection/terminal laws consume — a focused, not maximal, signature).
------------------------------------------------------------------------

record SMCComonoid : Set₁ where
  infixr 9 _∘_
  infixr 7 _⊗ₘ_
  field
    Ob  : Set
    _⊸_ : Ob → Ob → Set

    -- Category.
    id    : ∀ {A} → A ⊸ A
    _∘_   : ∀ {A B C} → B ⊸ C → A ⊸ B → A ⊸ C
    _≈_   : ∀ {A B} → A ⊸ B → A ⊸ B → Set
    r≈    : ∀ {A B} {f : A ⊸ B} → f ≈ f
    s≈    : ∀ {A B} {f g : A ⊸ B} → f ≈ g → g ≈ f
    t≈    : ∀ {A B} {f g h : A ⊸ B} → f ≈ g → g ≈ h → f ≈ h
    ∘≈    : ∀ {A B C} {f f' : B ⊸ C} {g g' : A ⊸ B} →
            f ≈ f' → g ≈ g' → (f ∘ g) ≈ (f' ∘ g')
    assoc : ∀ {A B C D} {f : C ⊸ D} {g : B ⊸ C} {h : A ⊸ B} →
            ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))
    idl   : ∀ {A B} {f : A ⊸ B} → (id ∘ f) ≈ f
    idr   : ∀ {A B} {f : A ⊸ B} → (f ∘ id) ≈ f

    -- Monoidal (tensor on objects and morphisms; the bifunctor law).
    I     : Ob
    _⊗_   : Ob → Ob → Ob
    _⊗ₘ_  : ∀ {A B C D} → A ⊸ B → C ⊸ D → (A ⊗ C) ⊸ (B ⊗ D)
    ⊗≈    : ∀ {A B C D} {f f' : A ⊸ B} {g g' : C ⊸ D} →
            f ≈ f' → g ≈ g' → (f ⊗ₘ g) ≈ (f' ⊗ₘ g')
    ⊗∘    : ∀ {A B C D E F} {f' : B ⊸ C} {f : A ⊸ B} {g' : E ⊸ F} {g : D ⊸ E} →
            ((f' ⊗ₘ g') ∘ (f ⊗ₘ g)) ≈ ((f' ∘ f) ⊗ₘ (g' ∘ g))

    -- Unitors (the two we need to land the projections).
    ru    : ∀ {A} → (A ⊗ I) ⊸ A
    ru⁻   : ∀ {A} → A ⊸ (A ⊗ I)
    ru∘   : ∀ {A} → (ru {A} ∘ ru⁻ {A}) ≈ id
    ruNat : ∀ {A B} {f : A ⊸ B} → (ru ∘ (f ⊗ₘ id {I})) ≈ (f ∘ ru)
    lu    : ∀ {A} → (I ⊗ A) ⊸ A
    lu⁻   : ∀ {A} → A ⊸ (I ⊗ A)
    lu∘   : ∀ {A} → (lu {A} ∘ lu⁻ {A}) ≈ id
    luNat : ∀ {A B} {f : A ⊸ B} → (lu ∘ (id {I} ⊗ₘ f)) ≈ (f ∘ lu)

    -- Comonoid + Fox uniformity (every morphism is a comonoid homomorphism).
    dup     : ∀ {A} → A ⊸ (A ⊗ A)
    drop    : ∀ {A} → A ⊸ I
    counitR : ∀ {A} → ((id {A} ⊗ₘ drop {A}) ∘ dup {A}) ≈ ru⁻
    counitL : ∀ {A} → ((drop {A} ⊗ₘ id {A}) ∘ dup {A}) ≈ lu⁻
    dupNat  : ∀ {A B} {f : A ⊸ B} → (dup ∘ f) ≈ ((f ⊗ₘ f) ∘ dup)
    dropNat : ∀ {A B} {f : A ⊸ B} → (drop ∘ f) ≈ drop
    dropI   : (drop {I}) ≈ id

------------------------------------------------------------------------
-- Fox's theorem in that structure.
------------------------------------------------------------------------

module Fox (K : SMCComonoid) where
  open SMCComonoid K

  -- The recovered cartesian operations.
  ⟨_,_⟩ₗ : ∀ {C A B} → C ⊸ A → C ⊸ B → C ⊸ (A ⊗ B)
  ⟨ f , g ⟩ₗ = (f ⊗ₘ g) ∘ dup

  fstₗ : ∀ {A B} → (A ⊗ B) ⊸ A
  fstₗ = ru ∘ (id ⊗ₘ drop)

  sndₗ : ∀ {A B} → (A ⊗ B) ⊸ B
  sndₗ = lu ∘ (drop ⊗ₘ id)

  -- A chaining helper (transitivity, left-to-right).
  infixr 2 _≈⟨_⟩_
  _≈⟨_⟩_ : ∀ {A B} (f : A ⊸ B) {g h} → f ≈ g → g ≈ h → f ≈ h
  _ ≈⟨ p ⟩ q = t≈ p q

  infix 3 _∎
  _∎ : ∀ {A B} (f : A ⊸ B) → f ≈ f
  _ ∎ = r≈

  -- β for the first projection: `fstₗ ∘ ⟨f,g⟩ ≈ f`.
  fox-fst : ∀ {C A B} {f : C ⊸ A} {g : C ⊸ B} →
            (fstₗ ∘ ⟨ f , g ⟩ₗ) ≈ f
  fox-fst {f = f} {g} =
    (ru ∘ (id ⊗ₘ drop)) ∘ ((f ⊗ₘ g) ∘ dup)
      ≈⟨ assoc ⟩
    ru ∘ ((id ⊗ₘ drop) ∘ ((f ⊗ₘ g) ∘ dup))
      ≈⟨ ∘≈ r≈ (s≈ assoc) ⟩
    ru ∘ (((id ⊗ₘ drop) ∘ (f ⊗ₘ g)) ∘ dup)
      ≈⟨ ∘≈ r≈ (∘≈ (t≈ ⊗∘ (⊗≈ idl dropNat)) r≈) ⟩
    ru ∘ ((f ⊗ₘ drop) ∘ dup)
      ≈⟨ ∘≈ r≈ (∘≈ (s≈ (t≈ ⊗∘ (⊗≈ idr idl))) r≈) ⟩
    ru ∘ (((f ⊗ₘ id) ∘ (id ⊗ₘ drop)) ∘ dup)
      ≈⟨ ∘≈ r≈ assoc ⟩
    ru ∘ ((f ⊗ₘ id) ∘ ((id ⊗ₘ drop) ∘ dup))
      ≈⟨ ∘≈ r≈ (∘≈ r≈ counitR) ⟩
    ru ∘ ((f ⊗ₘ id) ∘ ru⁻)
      ≈⟨ s≈ assoc ⟩
    (ru ∘ (f ⊗ₘ id)) ∘ ru⁻
      ≈⟨ ∘≈ ruNat r≈ ⟩
    (f ∘ ru) ∘ ru⁻
      ≈⟨ assoc ⟩
    f ∘ (ru ∘ ru⁻)
      ≈⟨ ∘≈ r≈ ru∘ ⟩
    f ∘ id
      ≈⟨ idr ⟩
    f ∎

  -- β for the second projection: `sndₗ ∘ ⟨f,g⟩ ≈ g` (the `lu` mirror).
  fox-snd : ∀ {C A B} {f : C ⊸ A} {g : C ⊸ B} →
            (sndₗ ∘ ⟨ f , g ⟩ₗ) ≈ g
  fox-snd {f = f} {g} =
    (lu ∘ (drop ⊗ₘ id)) ∘ ((f ⊗ₘ g) ∘ dup)
      ≈⟨ assoc ⟩
    lu ∘ ((drop ⊗ₘ id) ∘ ((f ⊗ₘ g) ∘ dup))
      ≈⟨ ∘≈ r≈ (s≈ assoc) ⟩
    lu ∘ (((drop ⊗ₘ id) ∘ (f ⊗ₘ g)) ∘ dup)
      ≈⟨ ∘≈ r≈ (∘≈ (t≈ ⊗∘ (⊗≈ dropNat idl)) r≈) ⟩
    lu ∘ ((drop ⊗ₘ g) ∘ dup)
      ≈⟨ ∘≈ r≈ (∘≈ (s≈ (t≈ ⊗∘ (⊗≈ idl idr))) r≈) ⟩
    lu ∘ (((id ⊗ₘ g) ∘ (drop ⊗ₘ id)) ∘ dup)
      ≈⟨ ∘≈ r≈ assoc ⟩
    lu ∘ ((id ⊗ₘ g) ∘ ((drop ⊗ₘ id) ∘ dup))
      ≈⟨ ∘≈ r≈ (∘≈ r≈ counitL) ⟩
    lu ∘ ((id ⊗ₘ g) ∘ lu⁻)
      ≈⟨ s≈ assoc ⟩
    (lu ∘ (id ⊗ₘ g)) ∘ lu⁻
      ≈⟨ ∘≈ luNat r≈ ⟩
    (g ∘ lu) ∘ lu⁻
      ≈⟨ assoc ⟩
    g ∘ (lu ∘ lu⁻)
      ≈⟨ ∘≈ r≈ lu∘ ⟩
    g ∘ id
      ≈⟨ idr ⟩
    g ∎

  -- Pairing is natural: `⟨f,g⟩ ∘ h ≈ ⟨f∘h, g∘h⟩`. The load-bearing step is
  -- `dup ∘ h ≈ (h ⊗ h) ∘ dup` — this is precisely where `h`'s input is USED
  -- TWICE. Every duplication in the recovered cartesian structure is exactly
  -- one `dup`; nothing else in the linear core copies. This is the formal
  -- content of "memory annotations collapse onto `dup`".
  fox-pair-nat : ∀ {D C A B} {f : C ⊸ A} {g : C ⊸ B} {h : D ⊸ C} →
                 (⟨ f , g ⟩ₗ ∘ h) ≈ ⟨ f ∘ h , g ∘ h ⟩ₗ
  fox-pair-nat {f = f} {g} {h} =
    ((f ⊗ₘ g) ∘ dup) ∘ h
      ≈⟨ assoc ⟩
    (f ⊗ₘ g) ∘ (dup ∘ h)
      ≈⟨ ∘≈ r≈ dupNat ⟩
    (f ⊗ₘ g) ∘ ((h ⊗ₘ h) ∘ dup)
      ≈⟨ s≈ assoc ⟩
    ((f ⊗ₘ g) ∘ (h ⊗ₘ h)) ∘ dup
      ≈⟨ ∘≈ ⊗∘ r≈ ⟩
    ((f ∘ h) ⊗ₘ (g ∘ h)) ∘ dup ∎

  -- `I` is terminal: `drop` is the UNIQUE morphism into it. This is the
  -- categorical statement of "any value may be discarded" — the counit made
  -- a universal property, from `drop`'s naturality alone.
  fox-terminal : ∀ {A} (h : A ⊸ I) → h ≈ drop
  fox-terminal h =
    h            ≈⟨ s≈ idl ⟩
    id ∘ h       ≈⟨ ∘≈ (s≈ dropI) r≈ ⟩
    drop ∘ h     ≈⟨ dropNat ⟩
    drop ∎
