------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 2 — VARIANCE: the type formers as directed functors
--
-- `NbEPDirJ` gave the directed identity type (J, no-sym, transport, yo).
-- This module supplies the piece a directed CwF's substitution needs and
-- the one thing symmetric `Id` structurally cannot express: how the type
-- formers ACT on directed maps, WITH VARIANCE.
--
-- A program is a directed map of types: `Homₜ A B = Term A B`. The type
-- formers lift `Homₜ`:
--
--   * `_×→_`, `_+→_`  — COVARIANT bifunctors (both arguments forward);
--   * `_⇒→_`          — the exponential is CONTRAVARIANT in its domain:
--       `Homₜ A' A → Homₜ B B' → Homₜ (A ⇒ B) (A' ⇒ B')`
--     the first argument points A' → A (BACKWARD). A forward map on the
--     domain induces a BACKWARD map on the function type. This mixed
--     variance is the structural signature of directedness — and it is
--     exactly why `no-sym` (NbEPDirJ): you cannot transport symmetrically
--     across a `⇒`, because its domain reverses direction.
--
-- The covariant functor laws hold up to reduction (`⟶*`); the exponential's
-- involve βη and are stated up to convertibility `_≈_` (common reduct).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirV where

open import normalizer.Syntax.Types
  using ( Ty; _*_; _+_; _⇒_ )
open import normalizer.Syntax.CCC as C
  using ( Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_]; curry; apply
        ; _⟶_; _⟶*_; done; step
        ; id-left; id-right; fst-pair; snd-pair; eta-pair; eta-case
        ; ⟶*-trans; ⟶*-∘-l; ⟶*-∘-r; ⟶*-pair; ⟶*-case; ⟶*-curry )

------------------------------------------------------------------------
-- Types as objects, programs as directed maps.
------------------------------------------------------------------------

Homₜ : Ty → Ty → Set
Homₜ A B = Term A B

idₜ : ∀ {A} → Homₜ A A
idₜ = id

_∘ₜ_ : ∀ {A B C} → Homₜ B C → Homₜ A B → Homₜ A C
g ∘ₜ f = g ∘ f

------------------------------------------------------------------------
-- Product and coproduct: COVARIANT bifunctors.
------------------------------------------------------------------------

_×→_ : ∀ {A A' B B'} → Homₜ A A' → Homₜ B B' → Homₜ (A * B) (A' * B')
f ×→ g = ⟨ f ∘ fst , g ∘ snd ⟩

_+→_ : ∀ {A A' B B'} → Homₜ A A' → Homₜ B B' → Homₜ (A + B) (A' + B')
f +→ g = [ inl ∘ f , inr ∘ g ]

-- Functor identity laws, up to reduction.
×→-id : ∀ {A B} → (idₜ {A} ×→ idₜ {B}) ⟶* idₜ
×→-id = ⟶*-trans (⟶*-pair (step id-left done) (step id-left done))
                 (step eta-pair done)

+→-id : ∀ {A B} → (idₜ {A} +→ idₜ {B}) ⟶* idₜ
+→-id = ⟶*-trans (⟶*-case (step id-right done) (step id-right done))
                 (step eta-case done)

------------------------------------------------------------------------
-- The exponential: CONTRAVARIANT in the domain, covariant in the codomain.
--
-- Note the signature — the FIRST argument is `Homₜ A' A`, reversed. This is
-- the theorem: `⇒` only lifts directed maps if the domain map runs
-- BACKWARD. Try to give it type `Homₜ A A' → …` and it does not typecheck.
------------------------------------------------------------------------

_⇒→_ : ∀ {A A' B B'} → Homₜ A' A → Homₜ B B' → Homₜ (A ⇒ B) (A' ⇒ B')
h ⇒→ k = curry (k ∘ (apply ∘ ⟨ fst , h ∘ snd ⟩))

------------------------------------------------------------------------
-- The functoriality WALL — where directed reduction is not enough.
--
-- The exponential's identity law `id ⇒→ id ≡ id` is a βη fact. Directed
-- reduction takes us most of the way:
--
--   id ⇒→ id  =  curry (id ∘ (apply ∘ ⟨ fst , id ∘ snd ⟩))  ⟶*  curry apply
--
-- but there it STOPS: this system has no rule `curry apply ⟶ id`
-- (`curry-η` only fires on the η-EXPANDED shape `curry (apply ∘ ⟨f∘fst, snd⟩)`,
-- not on `curry apply`). So `curry apply` is a distinct `⟶*`-normal form,
-- and `id ⇒→ id` is a functor-identity ONLY up to the symmetric, η-complete
-- convertibility — path 1's `NF`, not path 2's `⟶*`.
--
-- This is the concrete payoff of the two-paths analysis (PATHS.md): the
-- COVARIANT type formers are directed functors by reduction alone (above);
-- the CONTRAVARIANT exponential needs the invertible/η-complete core to be
-- a functor at all. Directed structure sees the variance (the signature);
-- only the symmetric core closes the coherence.
------------------------------------------------------------------------

⇒→-id-reduces : ∀ {A B} → (idₜ {A} ⇒→ idₜ {B}) ⟶* curry apply
⇒→-id-reduces = ⟶*-curry
  (⟶*-trans (step id-left done)                                    -- outer id ∘ _  ⟶  _
  (⟶*-trans (⟶*-∘-r apply (⟶*-pair done (step id-left done)))    -- id ∘ snd  ⟶  snd
  (⟶*-trans (⟶*-∘-r apply (step eta-pair done))                  -- ⟨ fst , snd ⟩  ⟶  id
            (step id-right done))))                               -- apply ∘ id  ⟶  apply
