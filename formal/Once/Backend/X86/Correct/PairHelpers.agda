------------------------------------------------------------------------
-- Once.Backend.X86.Correct.PairHelpers
--
-- Helper functions and lemmas for run-ir-at-offset-pair
--
-- This module contains non-recursive parts of the pair proof:
--   - Instruction definitions
--   - Basic arithmetic lemmas
--
-- Level 3a - depends on PreMutual but NOT on MutualIR
------------------------------------------------------------------------

module Once.Backend.X86.Correct.PairHelpers where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import encoding axioms
open import Once.Postulates public
  using ( encode
        ; encode-pair-construct
        )

-- Import from extracted modules
open import Once.Backend.X86.Correct.RegisterLemmas public
open import Once.Backend.X86.Correct.FetchStep public
open import Once.Backend.X86.Correct.CompileLength public hiding (length-++)
open import Once.Backend.X86.Correct.StackInvariant public
open import Once.Backend.X86.Correct.ExecLemmas public
open import Once.Backend.X86.Correct.PreMutual public

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≟_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-sum)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning; inspect) renaming ([_] to ⟦_⟧ᵢ)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

------------------------------------------------------------------------
-- Arithmetic Lemmas for Pair Proofs
------------------------------------------------------------------------

-- Helper: (a + 7) + (b + 2) = a + b + 9
add-7-2 : ∀ a b → (a +ℕ 7) +ℕ (b +ℕ 2) ≡ a +ℕ b +ℕ 9
add-7-2 a b = begin
  (a +ℕ 7) +ℕ (b +ℕ 2)
    ≡⟨ +-assoc a 7 (b +ℕ 2) ⟩
  a +ℕ (7 +ℕ (b +ℕ 2))
    ≡⟨ cong (a +ℕ_) (+-assoc 7 b 2) ⟩
  a +ℕ ((7 +ℕ b) +ℕ 2)
    ≡⟨ cong (λ z → a +ℕ (z +ℕ 2)) (+-comm 7 b) ⟩
  a +ℕ ((b +ℕ 7) +ℕ 2)
    ≡⟨ cong (a +ℕ_) (+-assoc b 7 2) ⟩
  a +ℕ (b +ℕ 9)
    ≡⟨ sym (+-assoc a b 9) ⟩
  a +ℕ b +ℕ 9
    ∎

-- Helper: a + b + 9 = a + 9 + b
commute-9 : ∀ a b → a +ℕ b +ℕ 9 ≡ a +ℕ 9 +ℕ b
commute-9 a b = begin
  a +ℕ b +ℕ 9
    ≡⟨ +-assoc a b 9 ⟩
  a +ℕ (b +ℕ 9)
    ≡⟨ cong (a +ℕ_) (+-comm b 9) ⟩
  a +ℕ (9 +ℕ b)
    ≡⟨ sym (+-assoc a 9 b) ⟩
  a +ℕ 9 +ℕ b
    ∎

------------------------------------------------------------------------
-- Pair Instruction Definitions
------------------------------------------------------------------------

-- Setup instructions (7 instructions with frame pointer)
pair-setup-push-r14 : Instr
pair-setup-push-r14 = push (reg r14)

pair-setup-push-r15 : Instr
pair-setup-push-r15 = push (reg r15)

pair-setup-push-rbp : Instr
pair-setup-push-rbp = push (reg rbp)

pair-setup-frame : Instr
pair-setup-frame = mov (reg rbp) (reg rsp)

pair-setup-sub : Instr
pair-setup-sub = sub (reg rsp) (imm 16)

pair-setup-base : Instr
pair-setup-base = mov (reg r15) (reg rsp)

pair-setup-save : Instr
pair-setup-save = mov (reg r14) (reg rdi)

-- Middle instructions (between f and g)
pair-store-f : Instr
pair-store-f = mov (mem (base r15)) (reg rax)

pair-restore-input : Instr
pair-restore-input = mov (reg rdi) (reg r14)

-- Final instructions (after g) - 6 instructions
pair-store-g : Instr
pair-store-g = mov (mem (base+disp r15 8)) (reg rax)

pair-return : Instr
pair-return = mov (reg rax) (reg r15)

pair-restore-rsp : Instr
pair-restore-rsp = mov (reg rsp) (reg rbp)

pair-pop-rbp : Instr
pair-pop-rbp = pop rbp

pair-pop-r15 : Instr
pair-pop-r15 = pop r15

pair-pop-r14 : Instr
pair-pop-r14 = pop r14

------------------------------------------------------------------------
-- Step Count Arithmetic
------------------------------------------------------------------------

-- Total step count: 7 + len-f + 2 + len-g + 6 = (15 + len-f) + len-g = compile-length ⟨ f , g ⟩
step-count-eq : ∀ len-f len-g →
  (((7 +ℕ len-f) +ℕ 2) +ℕ len-g) +ℕ 6 ≡ (15 +ℕ len-f) +ℕ len-g
step-count-eq len-f len-g = begin
  (((7 +ℕ len-f) +ℕ 2) +ℕ len-g) +ℕ 6
    ≡⟨ +-assoc ((7 +ℕ len-f) +ℕ 2) len-g 6 ⟩
  ((7 +ℕ len-f) +ℕ 2) +ℕ (len-g +ℕ 6)
    ≡⟨ cong (((7 +ℕ len-f) +ℕ 2) +ℕ_) (+-comm len-g 6) ⟩
  ((7 +ℕ len-f) +ℕ 2) +ℕ (6 +ℕ len-g)
    ≡⟨ sym (+-assoc ((7 +ℕ len-f) +ℕ 2) 6 len-g) ⟩
  (((7 +ℕ len-f) +ℕ 2) +ℕ 6) +ℕ len-g
    ≡⟨ cong (_+ℕ len-g) (+-assoc (7 +ℕ len-f) 2 6) ⟩
  ((7 +ℕ len-f) +ℕ 8) +ℕ len-g
    ≡⟨ cong (_+ℕ len-g) (+-assoc 7 len-f 8) ⟩
  (7 +ℕ (len-f +ℕ 8)) +ℕ len-g
    ≡⟨ cong (λ x → (7 +ℕ x) +ℕ len-g) (+-comm len-f 8) ⟩
  (7 +ℕ (8 +ℕ len-f)) +ℕ len-g
    ≡⟨ cong (_+ℕ len-g) (sym (+-assoc 7 8 len-f)) ⟩
  ((7 +ℕ 8) +ℕ len-f) +ℕ len-g
    ≡⟨ refl ⟩
  (15 +ℕ len-f) +ℕ len-g
    ∎
