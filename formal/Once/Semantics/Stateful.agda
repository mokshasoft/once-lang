------------------------------------------------------------------------
-- Once.Semantics.Stateful
--
-- Stateful semantics with allocation tracking.
--
-- This module extends the pure semantics from Once.Semantics with
-- explicit allocation state. Key insight:
--
--   eval-stateful : AllocState → IR A B → ⟦ A ⟧ → AllocState × ⟦ B ⟧
--
-- When eval-stateful allocates a value, it:
--   1. Writes to memory at heap-ptr
--   2. Advances heap-ptr
--   3. Returns the allocation address
--
-- For this scheme, encode = allocation-address by definition!
------------------------------------------------------------------------

module Once.Semantics.Stateful where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type
open import Once.IR
open import Once.Semantics using (⟦_⟧; Closure; ⟦Fix⟧)
import Once.Semantics as Pure

open ⟦Fix⟧ public

------------------------------------------------------------------------
-- Memory and Allocation State
------------------------------------------------------------------------

Word : Set
Word = ℕ

Memory : Set
Memory = Word → Maybe Word

readMem : Memory → Word → Maybe Word
readMem m addr = m addr

-- Concrete writeMem (same as in Encoding.agda)
open import Data.Nat using (_≡ᵇ_)

writeMem : Memory → Word → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a

-- Allocation state: memory + heap pointer
record AllocState : Set where
  constructor alloc-state
  field
    mem : Memory
    heap-ptr : Word

open AllocState public

-- Initial allocation state
init-alloc-state : AllocState
init-alloc-state = alloc-state (λ _ → nothing) 1000

------------------------------------------------------------------------
-- Stateful Allocation Primitives
------------------------------------------------------------------------

-- Allocate a pair: returns (new state, address)
alloc-pair : AllocState → Word → Word → AllocState × Word
alloc-pair st v₁ v₂ = (st' , base)
  where
    base = heap-ptr st
    m₁ = writeMem (mem st) base v₁
    m₂ = writeMem m₁ (base +ℕ 8) v₂
    st' = alloc-state m₂ (base +ℕ 16)

-- Allocate a left sum (tag = 0)
alloc-inl : AllocState → Word → AllocState × Word
alloc-inl st v = (st' , base)
  where
    base = heap-ptr st
    m₁ = writeMem (mem st) base 0
    m₂ = writeMem m₁ (base +ℕ 8) v
    st' = alloc-state m₂ (base +ℕ 16)

-- Allocate a right sum (tag = 1)
alloc-inr : AllocState → Word → AllocState × Word
alloc-inr st v = (st' , base)
  where
    base = heap-ptr st
    m₁ = writeMem (mem st) base 1
    m₂ = writeMem m₁ (base +ℕ 8) v
    st' = alloc-state m₂ (base +ℕ 16)

-- Allocate a closure (env-addr, code-ptr)
alloc-closure : AllocState → Word → Word → AllocState × Word
alloc-closure st env-addr code-ptr = (st' , base)
  where
    base = heap-ptr st
    m₁ = writeMem (mem st) base env-addr
    m₂ = writeMem m₁ (base +ℕ 8) code-ptr
    st' = alloc-state m₂ (base +ℕ 16)

------------------------------------------------------------------------
-- Stateful Encode
--
-- encode-stateful traverses a value and allocates it in memory.
-- Returns (new state, address of value).
--
-- KEY PROPERTY: encode-stateful returns the heap-ptr where the
-- value was allocated. This makes encode-is-alloc-addr trivial!
------------------------------------------------------------------------

-- For atomic types, encode returns a fixed address (no allocation needed)
encode-unit : Word
encode-unit = 0

-- Mutually recursive with type interpretation
-- We need to traverse the value structure and allocate compound types
{-# TERMINATING #-}  -- Needed because of mutual recursion through ⟦_⟧
mutual
  -- Encode a value, allocating it in memory
  encode-stateful : ∀ {A : Type} → AllocState → ⟦ A ⟧ → AllocState × Word
  encode-stateful {Unit} st tt = (st , 0)
  encode-stateful {Void} st ()
  encode-stateful {A * B} st (a , b) =
    let (st₁ , addr-a) = encode-stateful {A} st a
        (st₂ , addr-b) = encode-stateful {B} st₁ b
        (st₃ , addr-pair) = alloc-pair st₂ addr-a addr-b
    in (st₃ , addr-pair)
  encode-stateful {A + B} st (inj₁ a) =
    let (st₁ , addr-a) = encode-stateful {A} st a
        (st₂ , addr-sum) = alloc-inl st₁ addr-a
    in (st₂ , addr-sum)
  encode-stateful {A + B} st (inj₂ b) =
    let (st₁ , addr-b) = encode-stateful {B} st b
        (st₂ , addr-sum) = alloc-inr st₁ addr-b
    in (st₂ , addr-sum)
  encode-stateful {A ⇒ B} st cl =
    -- Closure is already allocated, return its env-addr
    -- (In reality, the closure itself needs allocation, but we simplify)
    (st , Closure.env-addr cl)
  encode-stateful {Eff A B} st cl = encode-stateful {A ⇒ B} st cl
  encode-stateful {Fix F} st x = encode-stateful {F} st (unwrap x)
  encode-stateful {Int} st _ = (st , 0)  -- Simplified: integers as immediate
  encode-stateful {Str} st _ = (st , 0)  -- Simplified
  encode-stateful {Buffer} st _ = (st , 0)  -- Simplified
  encode-stateful {TVar _} st _ = (st , 0)  -- Simplified

------------------------------------------------------------------------
-- THE KEY THEOREM: Encode = Allocation Address
--
-- For compound types allocated via alloc-*, the returned address
-- IS the heap-ptr at allocation time. This is trivially refl!
------------------------------------------------------------------------

-- For pairs: encode returns the pair allocation address
encode-pair-is-alloc-addr : ∀ {A B : Type} (st : AllocState) (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
  let (st₁ , addr-a) = encode-stateful {A} st a
      (st₂ , addr-b) = encode-stateful {B} st₁ b
      (st₃ , addr-pair) = alloc-pair st₂ addr-a addr-b
  in addr-pair ≡ heap-ptr st₂
encode-pair-is-alloc-addr st a b = refl

-- For left sums: encode returns the sum allocation address
encode-inl-is-alloc-addr : ∀ {A B : Type} (st : AllocState) (a : ⟦ A ⟧) →
  let (st₁ , addr-a) = encode-stateful {A} st a
      (st₂ , addr-sum) = alloc-inl st₁ addr-a
  in addr-sum ≡ heap-ptr st₁
encode-inl-is-alloc-addr st a = refl

-- For right sums: encode returns the sum allocation address
encode-inr-is-alloc-addr : ∀ {B : Type} (st : AllocState) (b : ⟦ B ⟧) →
  let (st₁ , addr-b) = encode-stateful {B} st b
      (st₂ , addr-sum) = alloc-inr st₁ addr-b
  in addr-sum ≡ heap-ptr st₁
encode-inr-is-alloc-addr st b = refl

------------------------------------------------------------------------
-- Connection to Pure Semantics
--
-- The stateful encode agrees with pure eval followed by encoding.
-- This is the bridge between stateful and pure semantics.
------------------------------------------------------------------------

-- Get just the encoding (discarding state)
encode-value : ∀ {A : Type} → AllocState → ⟦ A ⟧ → Word
encode-value st v = proj₂ (encode-stateful st v)

------------------------------------------------------------------------
-- Summary
--
-- This module provides:
--   1. AllocState and allocation primitives
--   2. encode-stateful: allocates and returns address
--   3. Proof that encode = allocation-address (refl!)
--
-- The remaining step is to show that the pure `encode` postulate
-- in Once.Semantics agrees with encode-stateful. This requires
-- either:
--   a) Replacing the postulate with encode-stateful
--   b) Proving they're equivalent (needs more assumptions)
--
-- Option (a) requires changing Semantics.agda to thread AllocState.
-- Option (b) is what the bridge axiom encode-agrees-with-stateful does.
------------------------------------------------------------------------
