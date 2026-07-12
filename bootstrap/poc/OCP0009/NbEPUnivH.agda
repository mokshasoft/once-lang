------------------------------------------------------------------------
-- OCP-0009 · Universe HIERARCHY — `U₀ ⊂ U₁`, predicative (no `Type : Type`)
--
-- A single universe cannot contain a code for ITSELF: `` `U : U `` with
-- `El `U = U` is `Type : Type` — Girard's paradox, inconsistent and
-- non-total. So to make the small universe `U₀` a first-class TYPE (something
-- you can quantify over — the point of a hierarchy), its code must live one
-- level UP, in `U₁`. This module builds the two-level STRATIFIED Tarski
-- hierarchy (each `El` references only the level below — non-mutual across
-- levels, so no impredicativity):
--
--   `U₀ : U₁`      — the small universe, as a large type;   `El₁ `U₀ = U₀`
--   `⇑  : U₀ → U₁` — cumulative lift;                        `El₁ (`⇑ a) = El₀ a`
--
-- HEADLINE: because `U₀` is now a type in `U₁`, we can QUANTIFY over it —
-- System-F-style polymorphism `(A : U₀) → El₀ A → El₀ A` becomes an honest code
-- `` `Π₁ `U₀ … ``, decoded and inhabited by the real polymorphic identity.
--
-- Predicativity: there is NO `` `U₀ : U₀ `` and NO `` `U₁ : U₁ `` — the tower is
-- consistent. (Extends to `Uₙ` by the same stratified pattern; two levels
-- suffice to exhibit the structure. Conversion inherits `NbEPUniv`'s
-- opaque-family caveat; the defunctionalized/decidable version mirrors
-- `NbEPUnivDec`.)
------------------------------------------------------------------------

module poc.OCP0009.NbEPUnivH where

open import normalizer.Syntax.Types using ( ⊤; tt )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x

------------------------------------------------------------------------
-- Level 0 — the small universe (inductive-recursive, as `NbEPUniv`).
------------------------------------------------------------------------

mutual
  data U₀ : Set where
    `nat₀ `unit₀ : U₀
    `Π₀ : (a : U₀) → (El₀ a → U₀) → U₀

  El₀ : U₀ → Set
  El₀ `nat₀     = ℕ
  El₀ `unit₀    = ⊤
  El₀ (`Π₀ a b) = (x : El₀ a) → El₀ (b x)

------------------------------------------------------------------------
-- Level 1 — the large universe: a code for `U₀`, a cumulative lift, and its
-- own dependent Π. `El₁` lands in `Set` (every large code decodes to a `Set`,
-- `U₀` included), so the tower stays predicative.
------------------------------------------------------------------------

mutual
  data U₁ : Set where
    `U₀   : U₁                       -- the small universe, as a large type
    `⇑    : U₀ → U₁                  -- cumulative lift of a small code
    `nat₁ `unit₁ : U₁
    `Π₁ : (a : U₁) → (El₁ a → U₁) → U₁

  El₁ : U₁ → Set
  El₁ `U₀       = U₀                 -- decode the small-universe code to `U₀`
  El₁ (`⇑ a)    = El₀ a             -- cumulativity: lifting preserves meaning
  El₁ `nat₁     = ℕ
  El₁ `unit₁    = ⊤
  El₁ (`Π₁ a b) = (x : El₁ a) → El₁ (b x)

------------------------------------------------------------------------
-- The small universe is a first-class large type.
------------------------------------------------------------------------

_ : El₁ `U₀ ≡₁ U₀
_ = refl₁

-- Cumulativity: a lifted small code means exactly what it did downstairs.
cumul : ∀ (a : U₀) → El₁ (`⇑ a) ≡₁ El₀ a
cumul a = refl₁

------------------------------------------------------------------------
-- HEADLINE — polymorphism over the small universe. `(A : U₀) → El₀ A → El₀ A`
-- is expressible ONLY because `U₀` is a type (in `U₁`) to quantify over.
------------------------------------------------------------------------

`poly-id : U₁
`poly-id = `Π₁ `U₀ (λ A → `⇑ (`Π₀ A (λ _ → A)))

_ : El₁ `poly-id ≡₁ ((A : U₀) → El₀ A → El₀ A)
_ = refl₁

-- …inhabited by the real polymorphic identity function.
polyId : (A : U₀) → El₀ A → El₀ A
polyId A x = x

_ : El₁ `poly-id
_ = polyId

------------------------------------------------------------------------
-- A polymorphic function APPLIED at a small type — polymorphism computes.
-- `polyId `nat₀ : ℕ → ℕ` (instantiate the type variable at `` `nat₀ ``).
------------------------------------------------------------------------

_ : El₀ (`Π₀ `nat₀ (λ _ → `nat₀))
_ = polyId `nat₀
