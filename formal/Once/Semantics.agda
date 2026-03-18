------------------------------------------------------------------------
-- Once.Semantics
--
-- Denotational semantics for Once.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
------------------------------------------------------------------------

module Once.Semantics where

open import Once.Type
open import Once.CCC.IR
open import Once.Memory using (Word; AllocState; alloc-state; mem; heap-ptr)
  renaming (alloc-two-words to alloc-pair-mem)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer using (ℤ)
import Data.Integer as Int
open import Data.Float using () renaming (Float to AgdaFloat)
open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Import shared definitions from SemanticBase
------------------------------------------------------------------------

-- Re-export core type interpretation
-- NOTE: code-ptr removed from Closure - it's a compilation artifact, not semantic
open import Once.SemanticBase public
  using (⟦Fix⟧; wrap; unwrap; Closure; env-addr; semantics; ⟦_⟧)
  renaming ()

-- Re-export encoding postulates
open import Once.SemanticBase public
  using ( encode-pair-addr; encode-inl-addr; encode-inr-addr
        ; encode-closure-addr; encode-int; encode-float
        ; encode-str; encode-buffer; evalPrim; encode)

-- Re-export encoding properties
open import Once.SemanticBase public
  using (encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity)

------------------------------------------------------------------------
-- Word Type (imported from Once.Memory)
------------------------------------------------------------------------

-- Word is now imported from Once.Memory for consistency
-- This enables sharing memory model between semantics and backends

------------------------------------------------------------------------
-- KNOWN LIMITATION: Fixed Point Semantics
------------------------------------------------------------------------
--
-- The interpretation of Fix F uses a simple newtype wrapper:
--
--   ⟦ Fix F ⟧ = ⟦Fix⟧ ⟦ F ⟧
--
-- This models Fix F ≅ F, but the correct equation should be:
--
--   Fix F ≅ F[Fix F / X]   (F with recursive occurrences substituted)
--
-- For example, Nat = Fix (Unit + X) should satisfy:
--   ⟦ Nat ⟧ ≅ ⊤ ⊎ ⟦ Nat ⟧
--
-- But this model gives:
--   ⟦ Nat ⟧ = ⟦Fix⟧ (⊤ ⊎ ⟦ X ⟧)   where X is uninterpreted
--
-- The proofs eval-fold-unfold and eval-unfold-fold are trivially refl
-- because wrap/unwrap are inverses. This proves the wrapper isomorphism,
-- NOT the recursive fixed point property.
--
-- A proper treatment requires modeling F as a functor with an explicit
-- recursive position (e.g., a universe of strictly positive functors).
-- See docs/formal/what-is-proven.md for options to address this.
--
------------------------------------------------------------------------

-- | Propositional η-equality for Closure records
-- Records in mutual blocks lack definitional η-equality in Agda.
-- This postulate provides propositional η: reconstructing a Closure from
-- its fields produces the same Closure.
--
-- JUSTIFICATION: This is a standard mathematical truth for record types.
-- Any record equals a record constructed from its own fields. Agda doesn't
-- provide this definitionally for records in mutual blocks, but it's logically
-- sound and used in the standard library pattern for such cases.
postulate
  Closure-η : ∀ {A B} (cl : Closure A B) →
    record { env-addr = env-addr cl
           ; semantics = semantics cl } ≡ cl

------------------------------------------------------------------------
-- Evaluation of IR morphisms
------------------------------------------------------------------------

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

-- Products (AllocMode ignored in semantics)
eval fst (a , b)       = a
eval snd (a , b)       = b
eval (⟨ f , g ⟩ _) x   = (eval f x , eval g x)

-- Coproducts (AllocMode ignored in semantics)
eval (inl _) a         = inj₁ a
eval (inr _) b         = inj₂ b
eval (case f g) (inj₁ a) = eval f a
eval (case f g) (inj₂ b) = eval g b

-- Terminal
eval terminal _        = tt

-- Initial
eval initial ()

-- Exponential (with explicit Closure, AllocMode ignored in semantics)
-- curry f : IR A (B ⇒ C) creates a closure capturing the input
-- env-addr = encode a makes closure encoding computable!
-- NOTE: code-ptr is NOT in Closure - it's a compilation artifact, not semantic.
eval (curry f _) a     = record
  { env-addr  = encode a  -- Encoded environment (enables derivable encode-closure-construct)
  ; semantics = λ b → eval f (a , b)
  }
-- apply : IR ((A ⇒ B) * A) B extracts and applies the closure's semantics
eval apply (cl , a)    = semantics cl a

-- Recursive types (Fixed point isomorphism)
eval (fold _) x            = wrap x
eval unfold x          = unwrap x

-- Effect lifting (D032)
-- arr : (A ⇒ B) → Eff A B
-- Takes a pure closure and returns it as an effectful closure
-- Both have the same Closure representation
eval arr cl            = cl

-- Memory management (no-op in semantics)
eval (free-heap _) x   = x

-- Primitives (opaque operations)
eval (Prim name) x     = evalPrim name x
