-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Principal — A DEFINITION'S TYPE IS ITS PRINCIPAL TYPE
-- (D314, refined by D321; plan 0.119 D6, plan 0.121 R6).
--
-- The Spec (`Spec.Surface.Program.Principal`): no type strictly below the
-- schema over its DOMAINS (`_<:ᶜ_`) types the body. Keeping the domains, a
-- type has finitely many types below it: each covariant position is itself or
-- something below it (`Void` for a whole type), each grade is itself or lower.
-- `below T` lists the ones strictly below, all of them (`below-complete`), and
-- the decision is the checker run on each: the body's type is principal when
-- the checker rejects the body at each (`PrincipalAt`). The checker is sound
-- and complete for the Spec's derivation (`SpecWitness`, `Completeness`), so
-- that is the Spec's principality (`SpecFront.Def`).
--
-- Not just the types one step down: checking is not closed upward along
-- `<:ᶜ` (`compose (\x -> x) (cata alg)` checks as a pure arrow and not as an
-- `act` one, `cata`'s grade being its algebra's), so a body may check two
-- steps down and at nothing in between.
------------------------------------------------------------------------

module Once.Principal where

open import Once.Spec.Type using (var; Ty)
open import Once.Spec.Sub using (subᶜ-*; subᶜ-+; subᶜ-var)
open import Data.List using (List; []; _∷_; _++_; map; cartesianProductWith)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Purity; pure; act; eff; Finite; mk-kind; fin)
import Once.Spec.Grade as G
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float)
open import Once.Spec.Type using (μ; ν)
open import Once.Spec.Sub using (_<:ᶜ_; subᶜ-void; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Data.Product using (proj₁)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.TypeCheck.Scope using (NamedCtx)
import Once.TypeCheck.Elaborate as TE

-- the grades strictly below a grade, on the chain `pure ≤ act ≤ eff`
gradesBelow : Purity → List Purity
gradesBelow pure = []
gradesBelow act  = pure ∷ []
gradesBelow eff  = pure ∷ act ∷ []

finBelow : Finite → List Finite
finBelow G.pureᶠ = []
finBelow G.actᶠ  = G.pureᶠ ∷ []

-- The types strictly below `T` over its domains: below one component, or the
-- first one at or below and the second strictly below.
below : ∀ {m} → Ty m → List (Ty m)
below Void        = []
below Unit        = Void ∷ []
below Int         = Void ∷ []
below Float       = Void ∷ []
below (var i) = Void ∷ []
below (μ F)  = Void ∷ []
below (ν F φ) = Void ∷ map (ν F) (finBelow φ)
below (A * B)     =
  Void ∷ (cartesianProductWith _*_ (below A) (B ∷ []) ++ cartesianProductWith _*_ (A ∷ below A) (below B))
below (A + B)     =
  Void ∷ (cartesianProductWith _+_ (below A) (B ∷ []) ++ cartesianProductWith _+_ (A ∷ below A) (below B))
below (A ⇒[ mk-kind q π ] B) =
  Void ∷ (cartesianProductWith (λ π′ B′ → A ⇒[ mk-kind q π′ ] B′) (gradesBelow π) (B ∷ [])
          ++ cartesianProductWith (λ π′ B′ → A ⇒[ mk-kind q π′ ] B′) (π ∷ gradesBelow π) (below B))

-- A check that fails.
data Fails {m n Γ A} : TE.CheckElabResult {m} {n} Γ A → Set where
  fails : ∀ {err} → Fails (TE.failure err)

-- The checker rejects the body at every type strictly below its type.
PrincipalAt : ∀ {m} → (ctx : NamedCtx m) → Expr → Ty m → Set
PrincipalAt ctx e T = ∀ {X} → X ∈ below T → Fails (TE.checkElab ctx e X)

------------------------------------------------------------------------
-- `below` lists everything strictly below

private
  grade-at-or-below : ∀ {π π′} → π ⊑π π′ → π ≡ π′ ⊎ π ∈ gradesBelow π′
  grade-at-or-below ⊑-pure = inj₁ refl
  grade-at-or-below ⊑-eff  = inj₁ refl
  grade-at-or-below ⊑-act  = inj₁ refl
  grade-at-or-below ⊑-pe   = inj₂ (here refl)
  grade-at-or-below ⊑-pa   = inj₂ (here refl)
  grade-at-or-below ⊑-ae   = inj₂ (there (here refl))

  fin-at-or-below : ∀ φ φ′ → fin φ ⊑π fin φ′ → φ ≡ φ′ ⊎ φ ∈ finBelow φ′
  fin-at-or-below G.pureᶠ G.pureᶠ _    = inj₁ refl
  fin-at-or-below G.actᶠ G.actᶠ  _    = inj₁ refl
  fin-at-or-below G.pureᶠ G.actᶠ  _    = inj₂ (here refl)
  fin-at-or-below G.actᶠ G.pureᶠ ()

  -- two components, at or below their own: the pair is the same, or below
  pair-below : ∀ {A B C : Set} (f : A → B → C) {a a′ b b′} {xs ys}
             → a ≡ a′ ⊎ a ∈ xs → b ≡ b′ ⊎ b ∈ ys
             → f a b ≡ f a′ b′ ⊎ f a b ∈ (cartesianProductWith f xs (b′ ∷ []) ++ cartesianProductWith f (a′ ∷ xs) ys)
  pair-below f (inj₁ refl) (inj₁ refl) = inj₁ refl
  pair-below f {xs = xs} (inj₂ a∈) (inj₁ refl) = inj₂ (∈-++⁺ˡ (∈-cartesianProductWith⁺ f a∈ (here refl)))
  pair-below f {a′ = a′} {b′ = b′} {xs = xs} {ys} (inj₁ refl) (inj₂ b∈) =
    inj₂ (∈-++⁺ʳ (cartesianProductWith f xs (b′ ∷ [])) (∈-cartesianProductWith⁺ f {a′ ∷ xs} {ys} (here refl) b∈))
  pair-below f {a′ = a′} {b′ = b′} {xs = xs} {ys} (inj₂ a∈) (inj₂ b∈) =
    inj₂ (∈-++⁺ʳ (cartesianProductWith f xs (b′ ∷ [])) (∈-cartesianProductWith⁺ f {a′ ∷ xs} {ys} (there a∈) b∈))

  void-below : ∀ {m} (T : Ty m) → Void ≡ T ⊎ Void ∈ below T
  void-below Void           = inj₁ refl
  void-below Unit           = inj₂ (here refl)
  void-below Int            = inj₂ (here refl)
  void-below Float          = inj₂ (here refl)
  void-below (var i)    = inj₂ (here refl)
  void-below (μ F)     = inj₂ (here refl)
  void-below (ν F φ)   = inj₂ (here refl)
  void-below (A * B)        = inj₂ (here refl)
  void-below (A + B)        = inj₂ (here refl)
  void-below (A ⇒[ _ ] B)   = inj₂ (here refl)

  tail : ∀ {m} {T : Ty m} {X} {xs : List (Ty m)} → X ≡ T ⊎ X ∈ xs → X ≡ T ⊎ X ∈ (Void ∷ xs)
  tail (inj₁ eq) = inj₁ eq
  tail (inj₂ m)  = inj₂ (there m)

at-or-below-<:ᶜ : ∀ {m} {T : Ty m} {X} → X <:ᶜ T → X ≡ T ⊎ X ∈ below T
at-or-below-<:ᶜ {T = T} subᶜ-void = void-below T
at-or-below-<:ᶜ subᶜ-unit  = inj₁ refl
at-or-below-<:ᶜ subᶜ-int   = inj₁ refl
at-or-below-<:ᶜ subᶜ-float = inj₁ refl
at-or-below-<:ᶜ subᶜ-μ     = inj₁ refl
at-or-below-<:ᶜ subᶜ-var = inj₁ refl
at-or-below-<:ᶜ (subᶜ-* a b) = tail (pair-below _*_ (at-or-below-<:ᶜ a) (at-or-below-<:ᶜ b))
at-or-below-<:ᶜ (subᶜ-+ a b)  = tail (pair-below _+_ (at-or-below-<:ᶜ a) (at-or-below-<:ᶜ b))
at-or-below-<:ᶜ (subᶜ-arr {A = A} {q = q} b g) =
  tail (pair-below (λ π′ B′ → A ⇒[ mk-kind q π′ ] B′) (grade-at-or-below g) (at-or-below-<:ᶜ b))
at-or-below-<:ᶜ (subᶜ-ν {F = F} {f = φ} {f′ = φ′} g) = ν-step (fin-at-or-below φ φ′ g)
  where
    ν-step : φ ≡ φ′ ⊎ φ ∈ finBelow φ′ → ν F φ ≡ ν F φ′ ⊎ ν F φ ∈ below (ν F φ′)
    ν-step (inj₁ refl) = inj₁ refl
    ν-step (inj₂ m)    = inj₂ (there (∈-map⁺ (ν F) m))

below-complete : ∀ {m} {T : Ty m} {X} → X <:ᶜ T → ¬ X ≡ T → X ∈ below T
below-complete s ne = strict (at-or-below-<:ᶜ s) ne
  where
    strict : ∀ {X T : Ty _} → X ≡ T ⊎ X ∈ below T → ¬ X ≡ T → X ∈ below T
    strict (inj₁ eq) ne = ⊥-elim (ne eq)
    strict (inj₂ m)  _  = m
