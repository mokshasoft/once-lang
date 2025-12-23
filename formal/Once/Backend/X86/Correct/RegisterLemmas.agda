------------------------------------------------------------------------
-- Once.Backend.X86.Correct.RegisterLemmas
--
-- Lemmas for register file and memory operations.
-- These are independent (Level 0) - no dependencies on other Correct/* modules.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.RegisterLemmas where

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl)

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

------------------------------------------------------------------------
-- Register File Lemmas
------------------------------------------------------------------------

-- | Reading a register after writing to it returns the written value
-- This holds because both readReg and writeReg pattern-match on the same register.
readReg-writeReg-same : ∀ (rf : RegFile) (r : Reg) (v : Word) →
  readReg (writeReg rf r v) r ≡ v
readReg-writeReg-same rf rax v = refl
readReg-writeReg-same rf rbx v = refl
readReg-writeReg-same rf rcx v = refl
readReg-writeReg-same rf rdx v = refl
readReg-writeReg-same rf rsi v = refl
readReg-writeReg-same rf rdi v = refl
readReg-writeReg-same rf rbp v = refl
readReg-writeReg-same rf rsp v = refl
readReg-writeReg-same rf r8  v = refl
readReg-writeReg-same rf r9  v = refl
readReg-writeReg-same rf r10 v = refl
readReg-writeReg-same rf r11 v = refl
readReg-writeReg-same rf r12 v = refl
readReg-writeReg-same rf r13 v = refl
readReg-writeReg-same rf r14 v = refl
readReg-writeReg-same rf r15 v = refl

-- | Reading rdi after writing rsp returns the old value
-- This is what we need for run-inl-seq
readReg-writeReg-rsp-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) rdi ≡ readReg rf rdi
readReg-writeReg-rsp-rdi rf v = refl

-- | Reading rdi after writing r14 returns the old value
readReg-writeReg-r14-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) rdi ≡ readReg rf rdi
readReg-writeReg-r14-rdi rf v = refl

-- | Reading rsp after writing r14 returns the old value
readReg-writeReg-r14-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) rsp ≡ readReg rf rsp
readReg-writeReg-r14-rsp rf v = refl

-- | Reading r14 after writing rax returns the old value
readReg-writeReg-rax-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) r14 ≡ readReg rf r14
readReg-writeReg-rax-r14 rf v = refl

-- | Reading rsp after writing rax returns the old value
readReg-writeReg-rax-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) rsp ≡ readReg rf rsp
readReg-writeReg-rax-rsp rf v = refl

-- | Reading rsp after writing rdi returns the old value
readReg-writeReg-rdi-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) rsp ≡ readReg rf rsp
readReg-writeReg-rdi-rsp rf v = refl

-- | Reading rax after writing rsp returns the old value
readReg-writeReg-rsp-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) rax ≡ readReg rf rax
readReg-writeReg-rsp-rax rf v = refl

-- | Reading r15 after writing rsp returns the old value
readReg-writeReg-rsp-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) r15 ≡ readReg rf r15
readReg-writeReg-rsp-r15 rf v = refl

-- | Reading r14 after writing rsp returns the old value
readReg-writeReg-rsp-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) r14 ≡ readReg rf r14
readReg-writeReg-rsp-r14 rf v = refl

-- | Reading rax after writing r15 returns the old value
readReg-writeReg-r15-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rax ≡ readReg rf rax
readReg-writeReg-r15-rax rf v = refl

-- | Reading rdi after writing r15 returns the old value
readReg-writeReg-r15-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rdi ≡ readReg rf rdi
readReg-writeReg-r15-rdi rf v = refl

-- | Reading rsp after writing r15 returns the old value
readReg-writeReg-r15-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rsp ≡ readReg rf rsp
readReg-writeReg-r15-rsp rf v = refl

-- | Reading rax after writing r14 returns the old value
readReg-writeReg-r14-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) rax ≡ readReg rf rax
readReg-writeReg-r14-rax rf v = refl

-- | Reading r15 after writing r14 returns the old value
readReg-writeReg-r14-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) r15 ≡ readReg rf r15
readReg-writeReg-r14-r15 rf v = refl

-- | Reading r14 after writing rdi returns the old value
readReg-writeReg-rdi-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) r14 ≡ readReg rf r14
readReg-writeReg-rdi-r14 rf v = refl

-- | Reading r15 after writing rdi returns the old value
readReg-writeReg-rdi-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) r15 ≡ readReg rf r15
readReg-writeReg-rdi-r15 rf v = refl

-- | Reading rax after writing rdi returns the old value
readReg-writeReg-rdi-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) rax ≡ readReg rf rax
readReg-writeReg-rdi-rax rf v = refl

-- | Reading rbp after writing rdi returns the old value
readReg-writeReg-rdi-rbp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) rbp ≡ readReg rf rbp
readReg-writeReg-rdi-rbp rf v = refl

-- | Reading r15 after writing rax returns the old value
readReg-writeReg-rax-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) r15 ≡ readReg rf r15
readReg-writeReg-rax-r15 rf v = refl

-- | Reading rdi after writing rax returns the old value
readReg-writeReg-rax-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) rdi ≡ readReg rf rdi
readReg-writeReg-rax-rdi rf v = refl

-- | Reading rbp after writing rax returns the old value
readReg-writeReg-rax-rbp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rax v) rbp ≡ readReg rf rbp
readReg-writeReg-rax-rbp rf v = refl

-- | Reading rbp after writing rsp returns the old value
readReg-writeReg-rsp-rbp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) rbp ≡ readReg rf rbp
readReg-writeReg-rsp-rbp rf v = refl

-- | Reading rsp after writing rbp returns the old value
readReg-writeReg-rbp-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rbp v) rsp ≡ readReg rf rsp
readReg-writeReg-rbp-rsp rf v = refl

-- | Reading rdi after writing rbp returns the old value
readReg-writeReg-rbp-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rbp v) rdi ≡ readReg rf rdi
readReg-writeReg-rbp-rdi rf v = refl

-- | Reading r14 after writing rbp returns the old value
readReg-writeReg-rbp-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rbp v) r14 ≡ readReg rf r14
readReg-writeReg-rbp-r14 rf v = refl

-- | Reading r15 after writing rbp returns the old value
readReg-writeReg-rbp-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rbp v) r15 ≡ readReg rf r15
readReg-writeReg-rbp-r15 rf v = refl

-- | Reading rbp after writing r15 returns the old value
readReg-writeReg-r15-rbp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rbp ≡ readReg rf rbp
readReg-writeReg-r15-rbp rf v = refl

-- | Reading rbp after writing r14 returns the old value
readReg-writeReg-r14-rbp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r14 v) rbp ≡ readReg rf rbp
readReg-writeReg-r14-rbp rf v = refl

-- | Reading rax after writing rbp returns the old value
readReg-writeReg-rbp-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rbp v) rax ≡ readReg rf rax
readReg-writeReg-rbp-rax rf v = refl

-- | Reading r12 after writing rdi returns the old value
readReg-writeReg-rdi-r12 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) r12 ≡ readReg rf r12
readReg-writeReg-rdi-r12 rf v = refl

-- | Reading r12 after writing rsi returns the old value
readReg-writeReg-rsi-r12 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsi v) r12 ≡ readReg rf r12
readReg-writeReg-rsi-r12 rf v = refl

-- | Reading r14 after writing rsi returns the old value
readReg-writeReg-rsi-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsi v) r14 ≡ readReg rf r14
readReg-writeReg-rsi-r14 rf v = refl

-- | Reading r15 after writing rsi returns the old value
readReg-writeReg-rsi-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsi v) r15 ≡ readReg rf r15
readReg-writeReg-rsi-r15 rf v = refl

-- | Reading r14 after writing r12 returns the old value
readReg-writeReg-r12-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r12 v) r14 ≡ readReg rf r14
readReg-writeReg-r12-r14 rf v = refl

-- | Reading r15 after writing r12 returns the old value
readReg-writeReg-r12-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r12 v) r15 ≡ readReg rf r15
readReg-writeReg-r12-r15 rf v = refl

-- | Reading rsi after writing r12 returns the old value
readReg-writeReg-r12-rsi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r12 v) rsi ≡ readReg rf rsi
readReg-writeReg-r12-rsi rf v = refl

-- | Reading r14 after writing r15 returns the old value
readReg-writeReg-r15-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) r14 ≡ readReg rf r14
readReg-writeReg-r15-r14 rf v = refl

-- | Reading r12 after writing r15 returns the old value
readReg-writeReg-r15-r12 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) r12 ≡ readReg rf r12
readReg-writeReg-r15-r12 rf v = refl

-- | Reading rsi after writing r15 returns the old value
readReg-writeReg-r15-rsi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r15 v) rsi ≡ readReg rf rsi
readReg-writeReg-r15-rsi rf v = refl

-- | Reading r12 after writing rsp returns the old value
readReg-writeReg-rsp-r12 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rsp v) r12 ≡ readReg rf r12
readReg-writeReg-rsp-r12 rf v = refl

------------------------------------------------------------------------
-- r11 Lemmas (scratch register for case tag loading)
------------------------------------------------------------------------

-- | Reading rdi after writing r11 returns the old value
readReg-writeReg-r11-rdi : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r11 v) rdi ≡ readReg rf rdi
readReg-writeReg-r11-rdi rf v = refl

-- | Reading rsp after writing r11 returns the old value
readReg-writeReg-r11-rsp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r11 v) rsp ≡ readReg rf rsp
readReg-writeReg-r11-rsp rf v = refl

-- | Reading r14 after writing r11 returns the old value
readReg-writeReg-r11-r14 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r11 v) r14 ≡ readReg rf r14
readReg-writeReg-r11-r14 rf v = refl

-- | Reading r15 after writing r11 returns the old value
readReg-writeReg-r11-r15 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r11 v) r15 ≡ readReg rf r15
readReg-writeReg-r11-r15 rf v = refl

-- | Reading rbp after writing r11 returns the old value
readReg-writeReg-r11-rbp : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r11 v) rbp ≡ readReg rf rbp
readReg-writeReg-r11-rbp rf v = refl

-- | Reading rax after writing r11 returns the old value
readReg-writeReg-r11-rax : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r11 v) rax ≡ readReg rf rax
readReg-writeReg-r11-rax rf v = refl

-- | Reading r12 after writing r11 returns the old value
readReg-writeReg-r11-r12 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf r11 v) r12 ≡ readReg rf r12
readReg-writeReg-r11-r12 rf v = refl

-- | Reading r11 after writing rdi returns the old value
readReg-writeReg-rdi-r11 : ∀ (rf : RegFile) (v : Word) →
  readReg (writeReg rf rdi v) r11 ≡ readReg rf r11
readReg-writeReg-rdi-r11 rf v = refl

------------------------------------------------------------------------
-- Memory Lemmas
------------------------------------------------------------------------

-- | Reading from the address we just wrote returns the written value
readMem-writeMem-same : ∀ (m : Memory) (addr : Word) (v : Word) →
  readMem (writeMem m addr v) addr ≡ just v
readMem-writeMem-same m addr v with addr ≡ᵇ addr | ≡ᵇ-refl addr
... | true | _ = refl

-- | Reading from a different address after a write returns the old value
readMem-writeMem-diff : ∀ (m : Memory) (addr1 addr2 : Word) (v : Word) →
  addr1 ≢ addr2 →
  readMem (writeMem m addr1 v) addr2 ≡ readMem m addr2
readMem-writeMem-diff m addr1 addr2 v addr1≢addr2 with addr2 ≡ᵇ addr1 | ≡ᵇ⇒≡ addr2 addr1
... | false | _ = refl
... | true | eq = ⊥-elim (addr1≢addr2 (sym (eq tt)))
