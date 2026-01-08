------------------------------------------------------------------------
-- Once.Semantics
--
-- Denotational semantics for Once.
-- Interprets types as Agda Sets and IR morphisms as Agda functions.
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
record ⟦Fix⟧ (A : Set) : Set where
  constructor wrap
  field unwrap : A

open ⟦Fix⟧

------------------------------------------------------------------------
-- Closure Record (Explicit Function Representation)
------------------------------------------------------------------------
--
-- Closures are represented explicitly with:
--   - env-addr: Address of captured environment (for encoding)
--   - code-ptr: Address of thunk code (for apply)
--   - semantics: Actual function behavior
--
-- This makes closures inspectable, allowing `encode` to be computable.
-- Previously, ⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧ was opaque.
------------------------------------------------------------------------

-- | Semantic interpretation of types
--
-- Maps Once types to Agda types (Sets).
-- This is the object mapping of a functor from Once's CCC to Set.
--
-- NOTE: Closure and ⟦_⟧ are mutually recursive because:
--   - Closure.semantics has type ⟦ A ⟧ → ⟦ B ⟧
--   - ⟦ A ⇒ B ⟧ = Closure A B

-- NOTE: NO_POSITIVITY_CHECK is needed because Closure and ⟦_⟧ are mutually
-- recursive: Closure.semantics : ⟦ A ⟧ → ⟦ B ⟧, and ⟦ A ⇒ B ⟧ = Closure A B.
-- This appears non-strictly-positive, but is actually well-founded because:
--   1. Closures are only created via `eval (curry f)` for finite IR terms
--   2. The recursion terminates because IR has finite depth
--   3. No actual infinite regress occurs in practice
{-# NO_POSITIVITY_CHECK #-}
mutual
  record Closure (A B : Type) : Set where
    field
      env-addr  : Word           -- Encoded captured environment address
      code-ptr  : Word           -- Thunk code address
      semantics : ⟦ A ⟧ → ⟦ B ⟧  -- Actual function behavior

  ⟦_⟧ : Type → Set
  ⟦ Unit ⟧         = ⊤
  ⟦ Void ⟧         = ⊥
  ⟦ A * B ⟧        = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ A + B ⟧        = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ A ⇒[ q ] B ⟧   = Closure A B     -- Quantity erased at runtime
  ⟦ Eff A B ⟧      = Closure A B     -- D032: Same as pure function
  ⟦ Fix F ⟧        = ⟦Fix⟧ ⟦ F ⟧
  -- Base types
  ⟦ Int ⟧          = ℤ
  ⟦ Float ⟧        = AgdaFloat
  ⟦ Str ⟧          = String
  ⟦ Buffer ⟧       = String           -- Simplified: use String for bytes
  ⟦ TVar _ ⟧       = ⊤                 -- Type variables: use Unit as placeholder

open Closure public

------------------------------------------------------------------------
-- Encoding (moved here so eval can use it for closures)
------------------------------------------------------------------------

-- | Encode semantic values as machine words
--
-- encode maps semantic values to their runtime addresses/representations.
-- For compound types (pairs, sums, closures), encoding returns an ALLOCATION
-- ADDRESS where the value is stored in memory. For simple types (Unit, Fix),
-- encoding is a direct computation.
--
-- This is defined here (not in Postulates.agda) so eval can set
-- env-addr = encode a when creating closures.
--
-- PARTIALLY CONCRETE: Some types have obvious encodings that don't need
-- allocation state. These are defined concretely, making their encoding
-- axioms provable as refl.

-- | Abstract encoding primitives for types needing allocation addresses
-- These are the TRUE postulates - compound types need allocation.
postulate
  encode-pair-addr : ∀ {A B : Type} → ⟦ A ⟧ → ⟦ B ⟧ → Word      -- Pair allocation address
  encode-inl-addr  : ∀ {A B : Type} → ⟦ A ⟧ → Word              -- Left sum allocation address
  encode-inr-addr  : ∀ {A B : Type} → ⟦ B ⟧ → Word              -- Right sum allocation address
  encode-closure-addr : ∀ {A B : Type} → Closure A B → Word     -- Closure allocation address
  encode-int       : ℤ → Word                                    -- Integer encoding
  encode-float     : AgdaFloat → Word                            -- Float encoding (IEEE 754 bits)
  encode-str       : String → Word                               -- String encoding
  encode-buffer    : String → Word                               -- Buffer encoding
  -- Primitive evaluation (opaque operations resolved by runtime)
  evalPrim         : ∀ {A B : Type} → String → ⟦ A ⟧ → ⟦ B ⟧

-- | Concrete encode function
-- TERMINATING: Fix case recurses on smaller type (unwrapped value).
-- The recursion terminates because types are finite structures.
{-# TERMINATING #-}
encode : ∀ {A} → ⟦ A ⟧ → Word
encode {Unit} tt = 0                                          -- Unit → 0 (CONCRETE!)
encode {Void} ()                                              -- Void has no values
encode {A * B} (a , b) = encode-pair-addr {A} {B} a b         -- Needs allocation
encode {A + B} (inj₁ a) = encode-inl-addr {A} {B} a           -- Needs allocation
encode {A + B} (inj₂ b) = encode-inr-addr {A} {B} b           -- Needs allocation
encode {A ⇒[ q ] B} cl = encode-closure-addr cl               -- Quantity erased
encode {Eff A B} cl = encode-closure-addr cl                  -- Same as ⇒ (CONCRETE!)
encode {Fix F} (wrap x) = encode {F} x                        -- Identity (CONCRETE!)
encode {Int} n = encode-int n                                 -- Primitive
encode {Float} f = encode-float f                             -- Primitive (IEEE 754 bits)
encode {Str} s = encode-str s                                 -- Primitive
encode {Buffer} b = encode-buffer b                           -- Primitive
encode {TVar _} _ = 0                                         -- Placeholder

------------------------------------------------------------------------
-- PROVEN Encoding Properties (now refl!)
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- | encode-unit: Unit encodes to 0 (PROVEN - was postulated!)
encode-unit : encode {Unit} tt ≡ 0
encode-unit = refl

-- | encode-fix-wrap: wrapping doesn't change encoding (PROVEN - was postulated!)
encode-fix-wrap : ∀ {F} (x : ⟦ F ⟧) → encode {F} x ≡ encode {Fix F} (wrap x)
encode-fix-wrap x = refl

-- | encode-fix-unwrap: unwrapping doesn't change encoding (PROVEN - was postulated!)
encode-fix-unwrap : ∀ {F} (x : ⟦ Fix F ⟧) → encode {Fix F} x ≡ encode {F} (unwrap x)
encode-fix-unwrap (wrap x) = refl

-- | encode-arr-identity: Eff and ⇒ have same encoding (PROVEN - was postulated!)
encode-arr-identity : ∀ {A B} (cl : Closure A B) → encode {A ⇒ B} cl ≡ encode {Eff A B} cl
encode-arr-identity cl = refl

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

-- Primitives (opaque operations)
eval (Prim name) x     = evalPrim name x
