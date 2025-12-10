------------------------------------------------------------------------
-- Once.Semantics
--
-- Denotational semantics for Once.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
------------------------------------------------------------------------

module Once.Semantics where

open import Once.Type
open import Once.IR

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])

-- | Semantic interpretation of types
--
-- Maps Once types to Agda types (Sets).
-- This is the object mapping of a functor from Once's CCC to Set.
--
⟦_⟧ : Type → Set
⟦ Unit ⟧   = ⊤
⟦ Void ⟧   = ⊥
⟦ A * B ⟧  = ⟦ A ⟧ × ⟦ B ⟧
⟦ A + B ⟧  = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒ B ⟧  = ⟦ A ⟧ → ⟦ B ⟧

-- | Evaluation of IR morphisms
--
-- Maps IR morphisms to Agda functions.
-- This is the morphism mapping of a functor from Once's CCC to Set.
--
-- eval : IR A B → (⟦ A ⟧ → ⟦ B ⟧)
--
eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧

-- Category structure
eval id x              = x
eval (g ∘ f) x         = eval g (eval f x)

-- Products
eval fst (a , b)       = a
eval snd (a , b)       = b
eval ⟨ f , g ⟩ x       = (eval f x , eval g x)

-- Coproducts
eval inl a             = inj₁ a
eval inr b             = inj₂ b
eval [ f , g ] (inj₁ a) = eval f a
eval [ f , g ] (inj₂ b) = eval g b

-- Terminal
eval terminal _        = tt

-- Initial
eval initial ()

-- Exponential
eval (curry f) a       = λ b → eval f (a , b)
eval apply (f , a)     = f a
