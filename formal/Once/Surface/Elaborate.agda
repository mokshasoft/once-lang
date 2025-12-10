------------------------------------------------------------------------
-- Once.Surface.Elaborate
--
-- Elaboration from surface syntax to IR.
-- Converts lambda/variable expressions to point-free combinators.
------------------------------------------------------------------------

module Once.Surface.Elaborate where

open import Once.Type
open import Once.IR
open import Once.Surface.Syntax

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

-- | Interpret context as a product type (environment type)
--
-- The context (A₀, A₁, ..., Aₙ₋₁) becomes the nested product
-- (...((Unit * A₀) * A₁) * ... * Aₙ₋₁)
--
-- We use left-nested products so newest binding is easiest to access.
--
⟦_⟧ᶜ : ∀ {n} → Ctx n → Type
⟦ ∅ ⟧ᶜ     = Unit
⟦ Γ , A ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

-- | Project variable from environment (de Bruijn index 0 = rightmost)
--
-- Given context (Γ, A), index 0 projects A (using snd),
-- index n+1 projects from Γ (using fst then recursing).
--
proj : ∀ {n} {Γ : Ctx n} (i : Fin n) → IR ⟦ Γ ⟧ᶜ (lookup Γ i)
proj {Γ = Γ , A} Fin.zero    = snd
proj {Γ = Γ , A} (Fin.suc i) = proj i ∘ fst

-- | Helper: swap product components
swap' : ∀ {X Y} → IR (X * Y) (Y * X)
swap' = ⟨ snd , fst ⟩

-- | Distribute environment over sum (distributivity isomorphism)
--
--   Γ * (A + B) → (Γ * A) + (Γ * B)
--
-- Uses curry/apply to thread environment through case:
-- 1. Swap to get (A + B) * Γ
-- 2. Case on sum, currying the injection to capture Γ
-- 3. Apply to reconstruct result
--
distribute : ∀ {Γ A B} → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute {Γ} {A} {B} = distrib' ∘ swap'
  where
    curryInlSwap : IR A (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInlSwap = curry (inl ∘ swap')

    curryInrSwap : IR B (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInrSwap = curry (inr ∘ swap')

    curryDistrib : IR (A + B) (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryDistrib = [ curryInlSwap , curryInrSwap ]

    distrib' : IR ((A + B) * Γ) ((Γ * A) + (Γ * B))
    distrib' = apply ∘ ⟨ curryDistrib ∘ fst , snd ⟩

-- | Elaborate surface expression to IR
--
-- elaborate e produces an IR morphism from the environment type to
-- the result type: IR ⟦Γ⟧ᶜ A
--
-- Key insight: lambdas extend the environment (product), variables
-- project from the environment, and applications compose appropriately.
--
elaborate : ∀ {n} {Γ : Ctx n} {A} → Expr Γ A → IR ⟦ Γ ⟧ᶜ A

-- Variable: project from environment
elaborate (var i) = proj i

-- Lambda: λx.e becomes curry of (elaborate e)
-- Context (Γ, A) has type ⟦Γ⟧ᶜ * A = ⟦Γ,A⟧ᶜ
elaborate (lam e) = curry (elaborate e)

-- Application: f x becomes apply ∘ ⟨f, x⟩
elaborate (app f x) = apply ∘ ⟨ elaborate f , elaborate x ⟩

-- Pair: (a, b) becomes ⟨a, b⟩
elaborate (pair a b) = ⟨ elaborate a , elaborate b ⟩

-- Projections: compose with projection
elaborate (fst' p) = fst ∘ elaborate p
elaborate (snd' p) = snd ∘ elaborate p

-- Sum introduction
elaborate (inl' a) = inl ∘ elaborate a
elaborate (inr' b) = inr ∘ elaborate b

-- Case: distribute environment over sum, then case on result
-- s : Expr Γ (A + B), l : Expr (Γ,A) C, r : Expr (Γ,B) C
-- Result: [ el , er ] ∘ distribute ∘ ⟨ id , es ⟩
elaborate (case' s l r) =
  [ elaborate l , elaborate r ] ∘ distribute ∘ ⟨ id , elaborate s ⟩

-- Unit
elaborate unit = terminal

-- Absurd (void elimination)
elaborate (absurd v) = initial ∘ elaborate v
