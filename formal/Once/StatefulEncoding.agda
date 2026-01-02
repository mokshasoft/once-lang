------------------------------------------------------------------------
-- Once.StatefulEncoding
--
-- Stateful encoding that allocates memory and returns addresses.
-- This makes encoding axioms PROVABLE as theorems.
--
-- Key insight: The old encode-pair-fst axiom claims:
--   readMem m (encode (a, b)) ≡ just (encode a)
-- for ANY memory m. But this is only true if (a, b) was properly
-- allocated. By making encode stateful, allocation creates memory
-- that satisfies the property by construction.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.StatefulEncoding where

open import Once.Type
open import Once.Memory
  using (Word; Memory; AllocState; alloc-state; mem; heap-ptr;
         readMem; writeMem; alloc-two-words;
         mem-read-write; mem-read-other; n≢n+8;
         alloc-two-words-fst; alloc-two-words-snd)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Import type interpretation from Semantics
-- We only need ⟦_⟧ and Closure, not eval
------------------------------------------------------------------------

open import Once.Semantics using (⟦_⟧; Closure; ⟦Fix⟧; wrap)
open ⟦Fix⟧

------------------------------------------------------------------------
-- Stateful Encoding
--
-- Unlike the abstract `encode` in Semantics.agda, this version:
-- 1. Takes an AllocState (memory + heap pointer)
-- 2. Allocates compound types in memory
-- 3. Returns the address AND updated AllocState
--
-- This makes encoding axioms provable because we KNOW what was written.
------------------------------------------------------------------------

-- | Stateful encoding: allocates and returns (address, new state)
{-# TERMINATING #-}
encode-s : ∀ {A} → ⟦ A ⟧ → AllocState → Word × AllocState

-- Simple types: no allocation needed
encode-s {Unit} tt st = (0 , st)
encode-s {Void} ()

-- Pair: allocate two words [encode a, encode b]
encode-s {A * B} (a , b) st =
  let (addr-a , st₁) = encode-s {A} a st
      (addr-b , st₂) = encode-s {B} b st₁
      (st₃ , base) = alloc-two-words st₂ addr-a addr-b
  in (base , st₃)

-- Left sum: allocate [0 (tag), encode a]
encode-s {A + B} (inj₁ a) st =
  let (addr-a , st₁) = encode-s {A} a st
      (st₂ , base) = alloc-two-words st₁ 0 addr-a
  in (base , st₂)

-- Right sum: allocate [1 (tag), encode b]
encode-s {A + B} (inj₂ b) st =
  let (addr-b , st₁) = encode-s {B} b st
      (st₂ , base) = alloc-two-words st₁ 1 addr-b
  in (base , st₂)

-- Closure: allocate [env-addr, code-ptr]
encode-s {A ⇒[ _ ] B} cl st =
  let (st' , base) = alloc-two-words st (Closure.env-addr cl) (Closure.code-ptr cl)
  in (base , st')

-- Eff is same as ⇒
encode-s {Eff A B} cl st =
  let (st' , base) = alloc-two-words st (Closure.env-addr cl) (Closure.code-ptr cl)
  in (base , st')

-- Fix: identity (no allocation)
encode-s {Fix F} (wrap x) st = encode-s {F} x st

-- Base types: placeholder (would need proper encoding)
encode-s {Int} _ st = (0 , st)
encode-s {Float} _ st = (0 , st)
encode-s {Str} _ st = (0 , st)
encode-s {Buffer} _ st = (0 , st)
encode-s {TVar _} _ st = (0 , st)

------------------------------------------------------------------------
-- PROVEN Encoding Theorems
--
-- These replace the postulated axioms in Postulates.agda.
-- They are PROVEN because we control what was written to memory.
------------------------------------------------------------------------

-- | Pair first component: reading base returns first value's encoding
encode-pair-fst-thm : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (st : AllocState) →
  let (addr-a , st₁) = encode-s {A} a st
      (addr-b , st₂) = encode-s {B} b st₁
      (addr-pair , st₃) = encode-s {A * B} (a , b) st
  in readMem (mem st₃) addr-pair ≡ just addr-a
encode-pair-fst-thm {A} {B} a b st =
  let (addr-a , st₁) = encode-s {A} a st
      (addr-b , st₂) = encode-s {B} b st₁
  in alloc-two-words-fst st₂ addr-a addr-b

-- | Pair second component: reading base+8 returns second value's encoding
encode-pair-snd-thm : ∀ {A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (st : AllocState) →
  let (addr-a , st₁) = encode-s {A} a st
      (addr-b , st₂) = encode-s {B} b st₁
      (addr-pair , st₃) = encode-s {A * B} (a , b) st
  in readMem (mem st₃) (addr-pair +ℕ 8) ≡ just addr-b
encode-pair-snd-thm {A} {B} a b st =
  let (addr-a , st₁) = encode-s {A} a st
      (addr-b , st₂) = encode-s {B} b st₁
  in alloc-two-words-snd st₂ addr-a addr-b

-- | Left sum tag: reading base returns 0
encode-inl-tag-thm : ∀ {A B} (a : ⟦ A ⟧) (st : AllocState) →
  let (addr-sum , st') = encode-s {A + B} (inj₁ a) st
  in readMem (mem st') addr-sum ≡ just 0
encode-inl-tag-thm {A} {B} a st =
  let (addr-a , st₁) = encode-s {A} a st
  in alloc-two-words-fst st₁ 0 addr-a

-- | Left sum value: reading base+8 returns value's encoding
encode-inl-val-thm : ∀ {A B} (a : ⟦ A ⟧) (st : AllocState) →
  let (addr-a , st₁) = encode-s {A} a st
      (addr-sum , st') = encode-s {A + B} (inj₁ a) st
  in readMem (mem st') (addr-sum +ℕ 8) ≡ just addr-a
encode-inl-val-thm {A} {B} a st =
  let (addr-a , st₁) = encode-s {A} a st
  in alloc-two-words-snd st₁ 0 addr-a

-- | Right sum tag: reading base returns 1
encode-inr-tag-thm : ∀ {A B} (b : ⟦ B ⟧) (st : AllocState) →
  let (addr-sum , st') = encode-s {A + B} (inj₂ b) st
  in readMem (mem st') addr-sum ≡ just 1
encode-inr-tag-thm {A} {B} b st =
  let (addr-b , st₁) = encode-s {B} b st
  in alloc-two-words-fst st₁ 1 addr-b

-- | Right sum value: reading base+8 returns value's encoding
encode-inr-val-thm : ∀ {A B} (b : ⟦ B ⟧) (st : AllocState) →
  let (addr-b , st₁) = encode-s {B} b st
      (addr-sum , st') = encode-s {A + B} (inj₂ b) st
  in readMem (mem st') (addr-sum +ℕ 8) ≡ just addr-b
encode-inr-val-thm {A} {B} b st =
  let (addr-b , st₁) = encode-s {B} b st
  in alloc-two-words-snd st₁ 1 addr-b

-- | Closure env: reading base returns env-addr
encode-closure-env-thm : ∀ {A B} (cl : Closure A B) (st : AllocState) →
  let (addr-cl , st') = encode-s {A ⇒ B} cl st
  in readMem (mem st') addr-cl ≡ just (Closure.env-addr cl)
encode-closure-env-thm cl st = alloc-two-words-fst st (Closure.env-addr cl) (Closure.code-ptr cl)

-- | Closure code: reading base+8 returns code-ptr
encode-closure-code-thm : ∀ {A B} (cl : Closure A B) (st : AllocState) →
  let (addr-cl , st') = encode-s {A ⇒ B} cl st
  in readMem (mem st') (addr-cl +ℕ 8) ≡ just (Closure.code-ptr cl)
encode-closure-code-thm cl st = alloc-two-words-snd st (Closure.env-addr cl) (Closure.code-ptr cl)

------------------------------------------------------------------------
-- Simple type theorems (trivial by definition)
------------------------------------------------------------------------

-- | Unit encodes to 0
encode-unit-thm : ∀ (st : AllocState) →
  proj₁ (encode-s {Unit} tt st) ≡ 0
encode-unit-thm st = refl

-- | Fix is identity encoding
encode-fix-thm : ∀ {F} (x : ⟦ F ⟧) (st : AllocState) →
  encode-s {Fix F} (wrap x) st ≡ encode-s {F} x st
encode-fix-thm x st = refl

------------------------------------------------------------------------
-- Summary: Postulates → Theorems
--
-- OLD (Postulates.agda):
--   postulate encode-pair-fst : ... → readMem m (encode (a,b)) ≡ just (encode a)
--
-- NEW (this module):
--   encode-pair-fst-thm : ... → readMem (mem st') addr-pair ≡ just addr-a
--   PROVEN: = alloc-two-words-fst st₂ addr-a addr-b
--
-- The key difference: stateful encoding CREATES the memory that
-- satisfies the property, rather than assuming any memory works.
------------------------------------------------------------------------

