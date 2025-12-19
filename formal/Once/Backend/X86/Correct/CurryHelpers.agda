------------------------------------------------------------------------
-- Once.Backend.X86.Correct.CurryHelpers
--
-- Helper functions and lemmas for run-ir-at-offset-curry and apply
--
-- This module contains non-recursive parts of the curry/apply proofs:
--   - Instruction definitions
--   - Register preservation lemmas
--   - Closure accessors
--
-- Level 3a - depends on PreMutual but NOT on MutualIR
------------------------------------------------------------------------

module Once.Backend.X86.Correct.CurryHelpers where

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
        ; encode-pair-fst
        ; encode-pair-snd
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
-- Closure Accessors (x86 specific)
------------------------------------------------------------------------

-- | Extract code-ptr from closure
closure-code-ptr-x86 : ∀ {A B : Type} → ⟦ A ⇒ B ⟧ → Word
closure-code-ptr-x86 cl = Closure.code-ptr cl

-- | Extract env from closure
closure-env-x86 : ∀ {A B : Type} → ⟦ A ⇒ B ⟧ → Word
closure-env-x86 cl = Closure.env-addr cl

------------------------------------------------------------------------
-- Curry Instruction Definitions
------------------------------------------------------------------------

-- Curry setup instructions (6 instructions before jmp)
curry-sub-rsp : Instr
curry-sub-rsp = sub (reg rsp) (imm 16)

curry-mov-env : Instr
curry-mov-env = mov (mem (base rsp)) (reg rdi)

curry-mov-rax-rsp : Instr
curry-mov-rax-rsp = mov (reg rax) (reg rsp)

-- curry-lea-r9 and curry-mov-code-ptr depend on len-f, so defined parametrically
curry-lea-r9 : Instr
curry-lea-r9 = lea r9 (rip+disp 4)

curry-mov-code-ptr : Instr
curry-mov-code-ptr = mov (mem (base+disp rsp 8)) (reg r9)

-- jmp instruction depends on len-f
curry-jmp : ℕ → Instr
curry-jmp len-f = jmp (6 +ℕ len-f)

-- label at end
curry-end-label : ℕ → Instr
curry-end-label len-f = label (12 +ℕ len-f)

------------------------------------------------------------------------
-- Apply Instruction Definitions
------------------------------------------------------------------------

-- Apply instructions (6 instructions)
apply-load-closure : Instr
apply-load-closure = mov (reg r15) (mem (base rdi))

apply-load-arg : Instr
apply-load-arg = mov (reg rsi) (mem (base+disp rdi 8))

apply-load-env : Instr
apply-load-env = mov (reg r12) (mem (base r15))

apply-load-code : Instr
apply-load-code = mov (reg r15) (mem (base+disp r15 8))

apply-mov-arg : Instr
apply-mov-arg = mov (reg rdi) (reg rsi)

apply-call : Instr
apply-call = call (reg r15)

------------------------------------------------------------------------
-- Thunk Instruction Definitions
------------------------------------------------------------------------

-- Thunk setup instructions (4 instructions before f)
thunk-sub-rsp : Instr
thunk-sub-rsp = sub (reg rsp) (imm 16)

thunk-mov-env : Instr
thunk-mov-env = mov (mem (base rsp)) (reg r12)

thunk-mov-arg : Instr
thunk-mov-arg = mov (mem (base+disp rsp 8)) (reg rdi)

thunk-mov-rdi-rsp : Instr
thunk-mov-rdi-rsp = mov (reg rdi) (reg rsp)

-- ret instruction
thunk-ret : Instr
thunk-ret = ret

------------------------------------------------------------------------
-- PC Arithmetic for Curry
------------------------------------------------------------------------

-- PC after 7 steps (including label): prefix + 13 + len-f = prefix + compile-length (curry f)
-- compile-length (curry f) = 13 + compile-length f
curry-pc-final : ∀ {A B C} (f : IR (A * B) C) (prefix : Program) →
  length prefix +ℕ 13 +ℕ compile-length f ≡ length prefix +ℕ compile-length (curry f)
curry-pc-final f prefix = begin
  length prefix +ℕ 13 +ℕ compile-length f
    ≡⟨ +-assoc (length prefix) 13 (compile-length f) ⟩
  length prefix +ℕ (13 +ℕ compile-length f)
    ≡⟨ refl ⟩
  length prefix +ℕ compile-length (curry f)
    ∎

------------------------------------------------------------------------
-- PC Arithmetic for Apply
------------------------------------------------------------------------

-- compile-length apply = 7 (6 instructions + potential suffix)
-- Actually compile-x86 apply is just the 6 instructions for setup
-- The thunk code is embedded in the curry

------------------------------------------------------------------------
-- Helper for Curry: PC after jmp
-- pc s5 = prefix + 5
-- jmp offset = 6 + len-f
-- pc s6 = (prefix + 5) + 1 + (6 + len-f) = prefix + 12 + len-f
------------------------------------------------------------------------

curry-pc-after-jmp : ∀ (prefix : Program) (len-f : ℕ) →
  (length prefix +ℕ 5) +ℕ 1 +ℕ (6 +ℕ len-f) ≡ length prefix +ℕ 12 +ℕ len-f
curry-pc-after-jmp prefix len-f = begin
  (length prefix +ℕ 5) +ℕ 1 +ℕ (6 +ℕ len-f)
    ≡⟨ cong (_+ℕ (6 +ℕ len-f)) (+-assoc (length prefix) 5 1) ⟩
  (length prefix +ℕ 6) +ℕ (6 +ℕ len-f)
    ≡⟨ +-assoc (length prefix) 6 (6 +ℕ len-f) ⟩
  length prefix +ℕ (6 +ℕ (6 +ℕ len-f))
    ≡⟨ cong (length prefix +ℕ_) (+-assoc 6 6 len-f) ⟩
  length prefix +ℕ (12 +ℕ len-f)
    ≡⟨ sym (+-assoc (length prefix) 12 len-f) ⟩
  length prefix +ℕ 12 +ℕ len-f
    ∎
