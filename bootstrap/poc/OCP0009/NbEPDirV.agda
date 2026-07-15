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
-- The covariant functor laws hold up to reduction (`⟶*`). The exponential's
-- identity law does NOT close by reduction here — but that is an
-- η-incompleteness of THIS rewrite presentation, not a real obstruction
-- (see the note at `⇒→-id-reduces` below), and it does not touch the cata
-- fragment (`NbEPDirC`), which is exponential-free and wall-free.
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
-- The exponential's identity law — an η-incompleteness, NOT a wall.
--
-- `id ⇒→ id ≡ id` is a βη fact. Directed reduction takes us most of the way:
--
--   id ⇒→ id  =  curry (id ∘ (apply ∘ ⟨ fst , id ∘ snd ⟩))  ⟶*  curry apply
--
-- and there it STOPS: no rule fires on `curry apply` (`curry-η` only matches
-- the η-EXPANDED `curry (apply ∘ ⟨f∘fst, snd⟩)`, and the first pair-component
-- stays `fst`, never `f∘fst`, so `curry-η` never gets a chance). So
-- `id ⇒→ id ⟶* id` is unreachable — a machine-checkable syntactic fact.
--
-- But its SIGNIFICANCE is small, and two things say so:
--   (1) SEMANTICALLY `curry apply = id` — both denote the identity function
--       (`eval (curry apply) g = λ a → g a = g`). The gap is a REDUCTION
--       artifact (this `⟶` is η-incomplete), not a semantic obstruction.
--   (2) This CCC's `⟶` is not cleanly confluent+terminating anyway (two-way
--       `assoc`; see `normalizer.Theory.WeakNormalizationFails` /
--       `RestrictedConfluence`), so `⟶*`-reachability is the wrong notion of
--       equality to read a "wall" off of.
--
-- The honest reading: `⟶*` does not EXHIBIT `⇒`-functoriality (η-short), but
-- the semantic model or an η-long NbE closes it trivially. What genuinely
-- survives for the directed programme is the CATA fragment (`NbEPDirC`),
-- which is exponential-free: there is no `⇒` in the polynomial functors, so
-- directed functoriality of `fmap`/`cata` holds by reduction with no η debt.
------------------------------------------------------------------------

⇒→-id-reduces : ∀ {A B} → (idₜ {A} ⇒→ idₜ {B}) ⟶* curry apply
⇒→-id-reduces = ⟶*-curry
  (⟶*-trans (step id-left done)                                    -- outer id ∘ _  ⟶  _
  (⟶*-trans (⟶*-∘-r apply (⟶*-pair done (step id-left done)))    -- id ∘ snd  ⟶  snd
  (⟶*-trans (⟶*-∘-r apply (step eta-pair done))                  -- ⟨ fst , snd ⟩  ⟶  id
            (step id-right done))))                               -- apply ∘ id  ⟶  apply
