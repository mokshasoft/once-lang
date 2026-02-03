------------------------------------------------------------------------
-- Once.SemanticsS
--
-- Sized-types version of denotational semantics for Once.
-- Interprets types as Agda Sets and sized IR morphisms as Agda functions.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.SemanticsS where

open import Size
open import Once.Type
open import Once.IRS
open import Once.Memory using (Word; AllocState; alloc-state; mem; heap-ptr)
  renaming (alloc-two-words to alloc-pair-mem)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Integer using (ℤ)
import Data.Integer as Int
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Data.Nat using (ℕ)

------------------------------------------------------------------------
-- Import shared definitions from Semantics
------------------------------------------------------------------------

-- Re-export type interpretation, closure, encoding from Semantics
open import Once.Semantics public
  using ( ⟦Fix⟧; wrap; unwrap; Closure; env-addr; code-ptr; semantics; ⟦_⟧
        ; encode-pair-addr; encode-inl-addr; encode-inr-addr
        ; encode-closure-addr; encode-int; encode-float
        ; encode-str; encode-buffer; encode
        ; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity
        )

------------------------------------------------------------------------
-- Evaluation of sized IR morphisms
------------------------------------------------------------------------

-- | Evaluation of IR morphisms
--
-- Maps IR morphisms to Agda functions.
-- This is the morphism mapping of a functor from Once's CCC to Set.
--
-- eval : IR i A B → (⟦ A ⟧ → ⟦ B ⟧)
--
-- The size parameter i is implicit and inferred from the IR structure.
--
eval : ∀ {i A B} → IR i A B → ⟦ A ⟧ → ⟦ B ⟧

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

-- Exponential (with explicit Closure)
-- curry f : IR A (B ⇒ C) creates a closure capturing the input
-- env-addr = encode a makes closure encoding computable!
eval (curry f) a       = record
  { env-addr  = encode a  -- Encoded environment (enables derivable encode-closure-construct)
  ; code-ptr  = 0         -- Placeholder; actual code pointer from compilation
  ; semantics = λ b → eval f (a , b)
  }
-- apply : IR ((A ⇒ B) * A) B extracts and applies the closure's semantics
eval apply (cl , a)    = semantics cl a

-- Recursive types (Fixed point isomorphism)
eval fold x            = wrap x
eval unfold x          = unwrap x

-- Effect lifting (D032)
-- arr : (A ⇒ B) → Eff A B
-- Takes a pure closure and returns it as an effectful closure
-- Both have the same Closure representation
eval arr cl            = cl

-- Primitives (explicit semantic function - no evalPrim postulate needed!)
eval (Prim _ sem _) x  = sem x
