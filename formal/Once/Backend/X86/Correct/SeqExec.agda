{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.X86.Correct.SeqExec
--
-- Sequential execution helpers for pair setup, mov sequences, and
-- inl/inr instruction sequences.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.SeqExec where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)
open import Once.Memory using (mem-read-write; mem-read-other)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

-- Import common memory helper lemmas
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl; n≢n+suc)

open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.ExecLemmas

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; _>_; _≥_; s≤s; z≤n; _≟_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; ∸-+-assoc; <-irrefl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

-- Arithmetic lemmas for stack slot address proofs
-- These are needed because rsp > 24 ensures the subtractions don't underflow
-- Note: _+_ is defined by recursion on the first argument, so we use +-comm
-- We match on the proof to ensure complete coverage

-- (x ∸ 24) + 8 ≡ x ∸ 16 when x > 24
-- Matching on the proof ensures x = suc^25 n for some n
∸24+8≡∸16 : ∀ m → m > 24 → (m ∸ 24) +ℕ 8 ≡ m ∸ 16
∸24+8≡∸16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))))))))))) =
  trans (+-comm (suc n) 8) refl

-- (x ∸ 24) + 16 ≡ x ∸ 8 when x > 24
∸24+16≡∸8 : ∀ m → m > 24 → (m ∸ 24) +ℕ 16 ≡ m ∸ 8
∸24+16≡∸8 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))))))))))) =
  trans (+-comm (suc n) 16) refl

-- m ∸ 16 ≢ m ∸ 8 when m > 16
∸16≢∸8 : ∀ m → m > 16 → m ∸ 16 ≢ m ∸ 8
∸16≢∸8 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))) ()

-- m ∸ 24 ≢ m ∸ 8 when m > 24
∸24≢∸8 : ∀ m → m > 24 → m ∸ 24 ≢ m ∸ 8
∸24≢∸8 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))))))))))) ()

-- m ∸ 24 ≢ m ∸ 16 when m > 24
∸24≢∸16 : ∀ m → m > 24 → m ∸ 24 ≢ m ∸ 16
∸24≢∸16 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))))))))))) ()

-- | Execute pair setup with frame pointer at arbitrary offset in a program (non-halting)
-- 7 setup instructions: push r14; push r15; push rbp; mov rbp, rsp; sub rsp, 16; mov r15, rsp; mov r14, rdi
--
-- After execution:
--   rsp = orig_rsp - 40 (3 pushes of 8 bytes + sub 16)
--   rbp = orig_rsp - 24 (frame base, after 3 pushes)
--   r15 = rsp (pair base address)
--   r14 = orig_rdi (saved input)
--   rdi = orig_rdi (unchanged)
--   pc = orig_pc + 7
exec-pair-setup-at-7 : ∀ (prefix : Program) (rest : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rsp > 24 →   -- Need rsp > 24 to prove memory disjointness
  ∃[ s' ] (exec 7 (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 7
         × readReg (regs s') r14 ≡ readReg (regs s) rdi
         × readReg (regs s') rdi ≡ readReg (regs s) rdi
         × readReg (regs s') r15 ≡ readReg (regs s) rsp ∸ 40
         × readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ 40
         × readReg (regs s') rbp ≡ readReg (regs s) rsp ∸ 24
         -- Memory proofs: stack slots contain saved registers
         × readMem (memory s') (readReg (regs s') rbp) ≡ just (readReg (regs s) rbp)
         × readMem (memory s') (readReg (regs s') rbp +ℕ 8) ≡ just (readReg (regs s) r15)
         × readMem (memory s') (readReg (regs s') rbp +ℕ 16) ≡ just (readReg (regs s) r14)
         -- Memory preservation: addresses >= orig-rsp are unchanged (writes are below rsp)
         × (∀ addr → addr ≥ readReg (regs s) rsp → readMem (memory s') addr ≡ readMem (memory s) addr))
exec-pair-setup-at-7 prefix rest s h-false pc-eq rsp-gt-24 = s7 , exec-eq , h7 , pc7 , r14-eq , rdi-eq , r15-eq , rsp-eq , rbp-eq , mem-rbp-eq , mem-r15-eq , mem-r14-eq , mem-above-eq
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (+-assoc)

    prog : Program
    prog = prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest

    -- Original values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    orig-r14 : Word
    orig-r14 = readReg (regs s) r14

    orig-r15 : Word
    orig-r15 = readReg (regs s) r15

    orig-rbp : Word
    orig-rbp = readReg (regs s) rbp

    -- Step 1: push r14 - save r14 to stack, decrement rsp by 8
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp (orig-rsp ∸ 8)
                  ; memory = writeMem (memory s) (orig-rsp ∸ 8) orig-r14
                  ; pc = pc s +ℕ 1 }

    fetch1 : fetch prog (length prefix) ≡ just (push (reg r14))
    fetch1 = fetch-at-prefix-end prefix (push (reg r14)) _

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s (push (reg r14)) h-false
                             (subst (λ n → fetch prog n ≡ just (push (reg r14))) (sym pc-eq) fetch1))
                  (execPush-reg prog s r14)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ n → n +ℕ 1) pc-eq

    rsp-s1 : readReg (regs s1) rsp ≡ orig-rsp ∸ 8
    rsp-s1 = readReg-writeReg-same (regs s) rsp (orig-rsp ∸ 8)

    r15-s1 : readReg (regs s1) r15 ≡ orig-r15
    r15-s1 = readReg-writeReg-rsp-r15 (regs s) (orig-rsp ∸ 8)

    rbp-s1 : readReg (regs s1) rbp ≡ orig-rbp
    rbp-s1 = readReg-writeReg-rsp-rbp (regs s) (orig-rsp ∸ 8)

    -- Step 2: push r15 - save r15 to stack, decrement rsp by 8
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rsp (readReg (regs s1) rsp ∸ 8)
                   ; memory = writeMem (memory s1) (readReg (regs s1) rsp ∸ 8) (readReg (regs s1) r15)
                   ; pc = pc s1 +ℕ 1 }

    prog-eq1 : prog ≡ (prefix ++ push (reg r14) ∷ []) ++ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq1 = sym (++-assoc prefix _ _)

    len-prefix1 : length (prefix ++ push (reg r14) ∷ []) ≡ length prefix +ℕ 1
    len-prefix1 = List-length-++ prefix

    fetch2 : fetch prog (length prefix +ℕ 1) ≡ just (push (reg r15))
    fetch2 = subst₂ (λ p n → fetch p n ≡ just (push (reg r15))) (sym prog-eq1) len-prefix1
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ []) (push (reg r15)) _)

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (push (reg r15)) h1
                             (subst (λ n → fetch prog n ≡ just (push (reg r15))) (sym pc1) fetch2))
                  (execPush-reg prog s1 r15)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ n → n +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    rsp-s2-raw : readReg (regs s2) rsp ≡ readReg (regs s1) rsp ∸ 8
    rsp-s2-raw = readReg-writeReg-same (regs s1) rsp (readReg (regs s1) rsp ∸ 8)

    rsp-s2 : readReg (regs s2) rsp ≡ orig-rsp ∸ 16
    rsp-s2 = trans rsp-s2-raw (trans (cong (_∸ 8) rsp-s1) (∸-+-assoc orig-rsp 8 8))

    rbp-s2 : readReg (regs s2) rbp ≡ orig-rbp
    rbp-s2 = trans (readReg-writeReg-rsp-rbp (regs s1) (readReg (regs s1) rsp ∸ 8)) rbp-s1

    -- Step 3: push rbp - save rbp to stack, decrement rsp by 8
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rsp (readReg (regs s2) rsp ∸ 8)
                   ; memory = writeMem (memory s2) (readReg (regs s2) rsp ∸ 8) (readReg (regs s2) rbp)
                   ; pc = pc s2 +ℕ 1 }

    prog-eq2 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ []) ++ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq2 = sym (++-assoc prefix _ _)

    len-prefix2 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ []) ≡ length prefix +ℕ 2
    len-prefix2 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch3 : fetch prog (length prefix +ℕ 2) ≡ just (push (reg rbp))
    fetch3 = subst₂ (λ p n → fetch p n ≡ just (push (reg rbp))) (sym prog-eq2) len-prefix2
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ []) (push (reg rbp)) _)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (push (reg rbp)) h2
                             (subst (λ n → fetch prog n ≡ just (push (reg rbp))) (sym pc2) fetch3))
                  (execPush-reg prog s2 rbp)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ n → n +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    rsp-s3-raw : readReg (regs s3) rsp ≡ readReg (regs s2) rsp ∸ 8
    rsp-s3-raw = readReg-writeReg-same (regs s2) rsp (readReg (regs s2) rsp ∸ 8)

    rsp-s3 : readReg (regs s3) rsp ≡ orig-rsp ∸ 24
    rsp-s3 = trans rsp-s3-raw (trans (cong (_∸ 8) rsp-s2) (∸-+-assoc orig-rsp 16 8))

    -- Step 4: mov rbp, rsp - set rbp to current rsp (frame base)
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rbp (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    prog-eq3 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ []) ++ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq3 = sym (++-assoc prefix _ _)

    len-prefix3 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ []) ≡ length prefix +ℕ 3
    len-prefix3 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch4 : fetch prog (length prefix +ℕ 3) ≡ just (mov (reg rbp) (reg rsp))
    fetch4 = subst₂ (λ p n → fetch p n ≡ just (mov (reg rbp) (reg rsp))) (sym prog-eq3) len-prefix3
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ []) (mov (reg rbp) (reg rsp)) _)

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg rbp) (reg rsp)) h3
                             (subst (λ n → fetch prog n ≡ just (mov (reg rbp) (reg rsp))) (sym pc3) fetch4))
                  (execMov-reg-reg s3 rbp rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ n → n +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    rbp-s4 : readReg (regs s4) rbp ≡ orig-rsp ∸ 24
    rbp-s4 = trans (readReg-writeReg-same (regs s3) rbp (readReg (regs s3) rsp)) rsp-s3

    rsp-s4 : readReg (regs s4) rsp ≡ orig-rsp ∸ 24
    rsp-s4 = trans (readReg-writeReg-rbp-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    -- Step 5: sub rsp, 16 - allocate 16 bytes on stack
    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) rsp (readReg (regs s4) rsp ∸ 16)
                   ; pc = pc s4 +ℕ 1
                   ; flags = updateFlags (readReg (regs s4) rsp ∸ 16) (readReg (regs s4) rsp) }

    prog-eq4 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ []) ++ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq4 = sym (++-assoc prefix _ _)

    len-prefix4 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ []) ≡ length prefix +ℕ 4
    len-prefix4 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch5 : fetch prog (length prefix +ℕ 4) ≡ just (sub (reg rsp) (imm 16))
    fetch5 = subst₂ (λ p n → fetch p n ≡ just (sub (reg rsp) (imm 16))) (sym prog-eq4) len-prefix4
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ []) (sub (reg rsp) (imm 16)) _)

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (sub (reg rsp) (imm 16)) h4
                             (subst (λ n → fetch prog n ≡ just (sub (reg rsp) (imm 16))) (sym pc4) fetch5))
                  (execSub-reg-imm prog s4 rsp 16)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (λ n → n +ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    rsp-s5-raw : readReg (regs s5) rsp ≡ readReg (regs s4) rsp ∸ 16
    rsp-s5-raw = readReg-writeReg-same (regs s4) rsp (readReg (regs s4) rsp ∸ 16)

    rsp-s5 : readReg (regs s5) rsp ≡ orig-rsp ∸ 40
    rsp-s5 = trans rsp-s5-raw (trans (cong (_∸ 16) rsp-s4) (∸-+-assoc orig-rsp 24 16))

    rbp-s5 : readReg (regs s5) rbp ≡ orig-rsp ∸ 24
    rbp-s5 = trans (readReg-writeReg-rsp-rbp (regs s4) (readReg (regs s4) rsp ∸ 16)) rbp-s4

    -- Step 6: mov r15, rsp - set r15 to current rsp (pair base address)
    s6 : State
    s6 = record s5 { regs = writeReg (regs s5) r15 (readReg (regs s5) rsp)
                   ; pc = pc s5 +ℕ 1 }

    prog-eq5 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ []) ++ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq5 = sym (++-assoc prefix _ _)

    len-prefix5 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ []) ≡ length prefix +ℕ 5
    len-prefix5 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch6 : fetch prog (length prefix +ℕ 5) ≡ just (mov (reg r15) (reg rsp))
    fetch6 = subst₂ (λ p n → fetch p n ≡ just (mov (reg r15) (reg rsp))) (sym prog-eq5) len-prefix5
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ []) (mov (reg r15) (reg rsp)) _)

    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (mov (reg r15) (reg rsp)) h5
                             (subst (λ n → fetch prog n ≡ just (mov (reg r15) (reg rsp))) (sym pc5) fetch6))
                  (execMov-reg-reg s5 r15 rsp)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ length prefix +ℕ 6
    pc6 = trans (cong (λ n → n +ℕ 1) pc5) (+-assoc (length prefix) 5 1)

    r15-s6 : readReg (regs s6) r15 ≡ orig-rsp ∸ 40
    r15-s6 = trans (readReg-writeReg-same (regs s5) r15 (readReg (regs s5) rsp)) rsp-s5

    rsp-s6 : readReg (regs s6) rsp ≡ orig-rsp ∸ 40
    rsp-s6 = trans (readReg-writeReg-r15-rsp (regs s5) (readReg (regs s5) rsp)) rsp-s5

    rbp-s6 : readReg (regs s6) rbp ≡ orig-rsp ∸ 24
    rbp-s6 = trans (readReg-writeReg-r15-rbp (regs s5) (readReg (regs s5) rsp)) rbp-s5

    rdi-s6 : readReg (regs s6) rdi ≡ orig-rdi
    rdi-s6 = trans (readReg-writeReg-r15-rdi (regs s5) (readReg (regs s5) rsp))
                   (trans (readReg-writeReg-rsp-rdi (regs s4) (readReg (regs s4) rsp ∸ 16))
                          (trans (readReg-writeReg-rbp-rdi (regs s3) (readReg (regs s3) rsp))
                                 (trans (readReg-writeReg-rsp-rdi (regs s2) (readReg (regs s2) rsp ∸ 8))
                                        (trans (readReg-writeReg-rsp-rdi (regs s1) (readReg (regs s1) rsp ∸ 8))
                                               (readReg-writeReg-rsp-rdi (regs s) (orig-rsp ∸ 8))))))

    -- Step 7: mov r14, rdi - save input to r14
    s7 : State
    s7 = record s6 { regs = writeReg (regs s6) r14 (readReg (regs s6) rdi)
                   ; pc = pc s6 +ℕ 1 }

    prog-eq6 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ []) ++ mov (reg r14) (reg rdi) ∷ rest
    prog-eq6 = sym (++-assoc prefix _ _)

    len-prefix6 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ []) ≡ length prefix +ℕ 6
    len-prefix6 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch7 : fetch prog (length prefix +ℕ 6) ≡ just (mov (reg r14) (reg rdi))
    fetch7 = subst₂ (λ p n → fetch p n ≡ just (mov (reg r14) (reg rdi))) (sym prog-eq6) len-prefix6
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm 16) ∷ mov (reg r15) (reg rsp) ∷ []) (mov (reg r14) (reg rdi)) _)

    step7 : step prog s6 ≡ just s7
    step7 = trans (step-exec prog s6 (mov (reg r14) (reg rdi)) h6
                             (subst (λ n → fetch prog n ≡ just (mov (reg r14) (reg rdi))) (sym pc6) fetch7))
                  (execMov-reg-reg s6 r14 rdi)

    h7 : halted s7 ≡ false
    h7 = h-false

    pc7 : pc s7 ≡ length prefix +ℕ 7
    pc7 = trans (cong (λ n → n +ℕ 1) pc6) (+-assoc (length prefix) 6 1)

    exec-eq : exec 7 prog s ≡ just s7
    exec-eq = exec-seven-steps-nonhalt prog s s1 s2 s3 s4 s5 s6 s7 step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7 h7

    r14-eq : readReg (regs s7) r14 ≡ orig-rdi
    r14-eq = trans (readReg-writeReg-same (regs s6) r14 (readReg (regs s6) rdi)) rdi-s6

    rdi-eq : readReg (regs s7) rdi ≡ orig-rdi
    rdi-eq = trans (readReg-writeReg-r14-rdi (regs s6) (readReg (regs s6) rdi)) rdi-s6

    r15-eq : readReg (regs s7) r15 ≡ orig-rsp ∸ 40
    r15-eq = trans (readReg-writeReg-r14-r15 (regs s6) (readReg (regs s6) rdi)) r15-s6

    rsp-eq : readReg (regs s7) rsp ≡ orig-rsp ∸ 40
    rsp-eq = trans (readReg-writeReg-r14-rsp (regs s6) (readReg (regs s6) rdi)) rsp-s6

    rbp-eq : readReg (regs s7) rbp ≡ orig-rsp ∸ 24
    rbp-eq = trans (readReg-writeReg-r14-rbp (regs s6) (readReg (regs s6) rdi)) rbp-s6

    -- Memory proofs: stack slots contain saved registers
    -- The memory layout after setup is:
    --   [orig-rsp - 8]  = orig-r14  (pushed at step 1)
    --   [orig-rsp - 16] = orig-r15  (pushed at step 2)
    --   [orig-rsp - 24] = orig-rbp  (pushed at step 3)
    -- After step 4: rbp = orig-rsp - 24, so:
    --   [rbp]     = orig-rbp   (at orig-rsp - 24)
    --   [rbp + 8] = orig-r15   (at orig-rsp - 16)
    --   [rbp + 16] = orig-r14  (at orig-rsp - 8)

    -- Address where step 3 writes: (orig-rsp - 16) - 8 = orig-rsp - 24
    write-addr-s3 : readReg (regs s2) rsp ∸ 8 ≡ orig-rsp ∸ 24
    write-addr-s3 = trans (cong (_∸ 8) rsp-s2) (∸-+-assoc orig-rsp 16 8)

    -- Memory after step 3: push rbp wrote orig-rbp to [orig-rsp - 24]
    -- Steps 4-7 don't write to memory (only mov/sub instructions)
    mem-s3-at-rbp : readMem (memory s3) (orig-rsp ∸ 24) ≡ just orig-rbp
    mem-s3-at-rbp = begin
        readMem (memory s3) (orig-rsp ∸ 24)
      ≡⟨⟩
        readMem (writeMem (memory s2) (readReg (regs s2) rsp ∸ 8) (readReg (regs s2) rbp)) (orig-rsp ∸ 24)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rbp)) (orig-rsp ∸ 24)) write-addr-s3 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ 24) (readReg (regs s2) rbp)) (orig-rsp ∸ 24)
      ≡⟨ cong (λ v → readMem (writeMem (memory s2) (orig-rsp ∸ 24) v) (orig-rsp ∸ 24)) rbp-s2 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ 24) orig-rbp) (orig-rsp ∸ 24)
      ≡⟨ mem-read-write {memory s2} {orig-rsp ∸ 24} {orig-rbp} ⟩
        just orig-rbp
      ∎

    -- Address where step 2 writes: (orig-rsp - 8) - 8 = orig-rsp - 16
    write-addr-s2 : readReg (regs s1) rsp ∸ 8 ≡ orig-rsp ∸ 16
    write-addr-s2 = trans (cong (_∸ 8) rsp-s1) (∸-+-assoc orig-rsp 8 8)

    -- Memory after step 2: push r15 wrote orig-r15 to [orig-rsp - 16]
    mem-s2-at-r15slot : readMem (memory s2) (orig-rsp ∸ 16) ≡ just orig-r15
    mem-s2-at-r15slot = begin
        readMem (memory s2) (orig-rsp ∸ 16)
      ≡⟨⟩
        readMem (writeMem (memory s1) (readReg (regs s1) rsp ∸ 8) (readReg (regs s1) r15)) (orig-rsp ∸ 16)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s1) addr (readReg (regs s1) r15)) (orig-rsp ∸ 16)) write-addr-s2 ⟩
        readMem (writeMem (memory s1) (orig-rsp ∸ 16) (readReg (regs s1) r15)) (orig-rsp ∸ 16)
      ≡⟨ cong (λ v → readMem (writeMem (memory s1) (orig-rsp ∸ 16) v) (orig-rsp ∸ 16)) r15-s1 ⟩
        readMem (writeMem (memory s1) (orig-rsp ∸ 16) orig-r15) (orig-rsp ∸ 16)
      ≡⟨ mem-read-write {memory s1} {orig-rsp ∸ 16} {orig-r15} ⟩
        just orig-r15
      ∎

    -- Memory after step 1: push r14 wrote orig-r14 to [orig-rsp - 8]
    -- s1.memory = writeMem (memory s) (orig-rsp ∸ 8) orig-r14
    mem-s1-at-r14slot : readMem (memory s1) (orig-rsp ∸ 8) ≡ just orig-r14
    mem-s1-at-r14slot = begin
        readMem (memory s1) (orig-rsp ∸ 8)
      ≡⟨⟩  -- by definition of s1
        readMem (writeMem (memory s) (orig-rsp ∸ 8) orig-r14) (orig-rsp ∸ 8)
      ≡⟨ mem-read-write {memory s} {orig-rsp ∸ 8} {orig-r14} ⟩
        just orig-r14
      ∎

    -- Memory is unchanged from s3 to s7 (steps 4-7 only modify registers)
    -- s4 = mov rbp, rsp (register only), s5 = sub rsp, 16 (register only)
    -- s6 = mov r15, rsp (register only), s7 = mov r14, rdi (register only)
    mem-s7-eq-s3 : memory s7 ≡ memory s3
    mem-s7-eq-s3 = refl

    -- Chain: s3's [orig-rsp - 24] preserved through s4-s7
    -- Need to show push r15 and push rbp didn't overwrite [orig-rsp - 8]
    -- [orig-rsp - 16] ≢ [orig-rsp - 8] and [orig-rsp - 24] ≢ [orig-rsp - 8]

    -- Memory at [orig-rsp - 8] in s2 (after push r15 at step 2)
    -- push r15 wrote to [orig-rsp - 16], not [orig-rsp - 8]
    -- s2.memory = writeMem (memory s1) (orig-rsp ∸ 16) orig-r15 (by write-addr-s2 and r15-s1)
    -- Derive rsp > 16 from rsp-gt-24 for the ∸16≢∸8 lemma
    -- rsp > 24 means 25 ≤ rsp, we need rsp > 16 which is 17 ≤ rsp
    -- Use ≤-trans with 17 ≤ 25 and 25 ≤ rsp
    rsp-gt-16 : orig-rsp > 16
    rsp-gt-16 = ≤-trans 17≤25 rsp-gt-24
      where
        open import Data.Nat.Properties using (≤-trans)
        17≤25 : 17 ≤ 25
        17≤25 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

    mem-s2-at-r14slot : readMem (memory s2) (orig-rsp ∸ 8) ≡ just orig-r14
    mem-s2-at-r14slot = begin
        readMem (memory s2) (orig-rsp ∸ 8)
      ≡⟨⟩
        readMem (writeMem (memory s1) (readReg (regs s1) rsp ∸ 8) (readReg (regs s1) r15)) (orig-rsp ∸ 8)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s1) addr (readReg (regs s1) r15)) (orig-rsp ∸ 8)) write-addr-s2 ⟩
        readMem (writeMem (memory s1) (orig-rsp ∸ 16) (readReg (regs s1) r15)) (orig-rsp ∸ 8)
      ≡⟨ mem-read-other {memory s1} {orig-rsp ∸ 16} {orig-rsp ∸ 8} {readReg (regs s1) r15} (∸16≢∸8 orig-rsp rsp-gt-16) ⟩
        readMem (memory s1) (orig-rsp ∸ 8)
      ≡⟨ mem-s1-at-r14slot ⟩
        just orig-r14
      ∎

    -- Memory at [orig-rsp - 8] in s3 (after push rbp at step 3)
    -- push rbp wrote to [orig-rsp - 24], not [orig-rsp - 8]
    mem-s3-at-r14slot : readMem (memory s3) (orig-rsp ∸ 8) ≡ just orig-r14
    mem-s3-at-r14slot = begin
        readMem (memory s3) (orig-rsp ∸ 8)
      ≡⟨⟩
        readMem (writeMem (memory s2) (readReg (regs s2) rsp ∸ 8) (readReg (regs s2) rbp)) (orig-rsp ∸ 8)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rbp)) (orig-rsp ∸ 8)) write-addr-s3 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ 24) (readReg (regs s2) rbp)) (orig-rsp ∸ 8)
      ≡⟨ mem-read-other {memory s2} {orig-rsp ∸ 24} {orig-rsp ∸ 8} {readReg (regs s2) rbp} (∸24≢∸8 orig-rsp rsp-gt-24) ⟩
        readMem (memory s2) (orig-rsp ∸ 8)
      ≡⟨ mem-s2-at-r14slot ⟩
        just orig-r14
      ∎

    -- Memory at [orig-rsp - 16] in s3 (after push rbp at step 3)
    -- push rbp wrote to [orig-rsp - 24], not [orig-rsp - 16]
    mem-s3-at-r15slot : readMem (memory s3) (orig-rsp ∸ 16) ≡ just orig-r15
    mem-s3-at-r15slot = begin
        readMem (memory s3) (orig-rsp ∸ 16)
      ≡⟨⟩
        readMem (writeMem (memory s2) (readReg (regs s2) rsp ∸ 8) (readReg (regs s2) rbp)) (orig-rsp ∸ 16)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rbp)) (orig-rsp ∸ 16)) write-addr-s3 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ 24) (readReg (regs s2) rbp)) (orig-rsp ∸ 16)
      ≡⟨ mem-read-other {memory s2} {orig-rsp ∸ 24} {orig-rsp ∸ 16} {readReg (regs s2) rbp} (∸24≢∸16 orig-rsp rsp-gt-24) ⟩
        readMem (memory s2) (orig-rsp ∸ 16)
      ≡⟨ mem-s2-at-r15slot ⟩
        just orig-r15
      ∎

    -- Final memory proofs in s7 (memory unchanged from s3)
    -- [rbp] = [orig-rsp - 24] = orig-rbp
    mem-rbp-eq : readMem (memory s7) (readReg (regs s7) rbp) ≡ just orig-rbp
    mem-rbp-eq = subst (λ addr → readMem (memory s7) addr ≡ just orig-rbp) (sym rbp-eq) mem-s3-at-rbp

    -- [rbp + 8] = [orig-rsp - 16] = orig-r15
    -- We need to show: (orig-rsp ∸ 24) + 8 ≡ orig-rsp ∸ 16
    mem-r15-eq : readMem (memory s7) (readReg (regs s7) rbp +ℕ 8) ≡ just orig-r15
    mem-r15-eq = subst (λ addr → readMem (memory s7) (addr +ℕ 8) ≡ just orig-r15)
                       (sym rbp-eq)
                       (subst (λ a → readMem (memory s7) a ≡ just orig-r15)
                              (sym (∸24+8≡∸16 orig-rsp rsp-gt-24))
                              mem-s3-at-r15slot)

    -- [rbp + 16] = [orig-rsp - 8] = orig-r14
    -- We need to show: (orig-rsp ∸ 24) + 16 ≡ orig-rsp ∸ 8
    mem-r14-eq : readMem (memory s7) (readReg (regs s7) rbp +ℕ 16) ≡ just orig-r14
    mem-r14-eq = subst (λ addr → readMem (memory s7) (addr +ℕ 16) ≡ just orig-r14)
                       (sym rbp-eq)
                       (subst (λ a → readMem (memory s7) a ≡ just orig-r14)
                              (sym (∸24+16≡∸8 orig-rsp rsp-gt-24))
                              mem-s3-at-r14slot)

    -- Memory preservation: addresses >= orig-rsp are unchanged
    -- Writes happen at orig-rsp - 8, orig-rsp - 16, orig-rsp - 24 (all < orig-rsp)
    -- Steps 4-7 don't write memory
    mem-above-eq : ∀ addr → addr ≥ orig-rsp → readMem (memory s7) addr ≡ readMem (memory s) addr
    mem-above-eq addr addr≥rsp = trans mem-s7-s3 (trans mem-s3-s2 (trans mem-s2-s1 mem-s1-s))
      where
        open import Data.Nat.Properties using (≤-trans; <-≤-trans; ∸-monoʳ-<; <⇒≤)

        -- All write addresses are < orig-rsp, hence ≠ addr
        write1 = orig-rsp ∸ 8    -- step 1 write address
        write2 = orig-rsp ∸ 16   -- step 2 write address
        write3 = orig-rsp ∸ 24   -- step 3 write address

        -- orig-rsp > 8 (derived from rsp > 24)
        rsp-gt-8 : orig-rsp > 8
        rsp-gt-8 = ≤-trans 9≤25 rsp-gt-24
          where
            9≤25 : 9 ≤ 25
            9≤25 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

        -- 0 < 8 (needed for ∸-monoʳ-<)
        0<8 : 0 < 8
        0<8 = s≤s z≤n

        -- 0 < 16 (needed for ∸-monoʳ-<)
        0<16 : 0 < 16
        0<16 = s≤s z≤n

        -- 0 < 24 (needed for ∸-monoʳ-<)
        0<24 : 0 < 24
        0<24 = s≤s z≤n

        -- 8 ≤ orig-rsp
        8≤rsp : 8 ≤ orig-rsp
        8≤rsp = <⇒≤ rsp-gt-8

        -- 16 ≤ orig-rsp
        16≤rsp : 16 ≤ orig-rsp
        16≤rsp = <⇒≤ rsp-gt-16

        -- 24 ≤ orig-rsp
        24≤rsp : 24 ≤ orig-rsp
        24≤rsp = <⇒≤ rsp-gt-24

        -- write1 < orig-rsp (using ∸-monoʳ-<)
        write1<rsp : write1 < orig-rsp
        write1<rsp = ∸-monoʳ-< 0<8 8≤rsp

        -- write2 < orig-rsp
        write2<rsp : write2 < orig-rsp
        write2<rsp = ∸-monoʳ-< 0<16 16≤rsp

        -- write3 < orig-rsp
        write3<rsp : write3 < orig-rsp
        write3<rsp = ∸-monoʳ-< 0<24 24≤rsp

        -- addr ≠ write1 (because write1 < orig-rsp ≤ addr)
        addr≢write1 : addr ≢ write1
        addr≢write1 eq = <-irrefl refl (<-≤-trans (subst (_< orig-rsp) (sym eq) write1<rsp) addr≥rsp)

        -- addr ≠ write2
        addr≢write2 : addr ≢ write2
        addr≢write2 eq = <-irrefl refl (<-≤-trans (subst (_< orig-rsp) (sym eq) write2<rsp) addr≥rsp)

        -- addr ≠ write3
        addr≢write3 : addr ≢ write3
        addr≢write3 eq = <-irrefl refl (<-≤-trans (subst (_< orig-rsp) (sym eq) write3<rsp) addr≥rsp)

        -- Memory s7 = s3 (steps 4-7 are register-only)
        mem-s7-s3 : readMem (memory s7) addr ≡ readMem (memory s3) addr
        mem-s7-s3 = refl

        -- Memory s3: step 3 wrote at write3, which ≠ addr
        mem-s3-s2 : readMem (memory s3) addr ≡ readMem (memory s2) addr
        mem-s3-s2 = trans (cong (λ a → readMem (writeMem (memory s2) a (readReg (regs s2) rbp)) addr) write-addr-s3)
                          (mem-read-other {memory s2} {write3} {addr} {readReg (regs s2) rbp} (λ eq → addr≢write3 (sym eq)))

        -- Memory s2: step 2 wrote at write2, which ≠ addr
        mem-s2-s1 : readMem (memory s2) addr ≡ readMem (memory s1) addr
        mem-s2-s1 = trans (cong (λ a → readMem (writeMem (memory s1) a (readReg (regs s1) r15)) addr) write-addr-s2)
                          (mem-read-other {memory s1} {write2} {addr} {readReg (regs s1) r15} (λ eq → addr≢write2 (sym eq)))

        -- Memory s1: step 1 wrote at write1, which ≠ addr
        mem-s1-s : readMem (memory s1) addr ≡ readMem (memory s) addr
        mem-s1-s = mem-read-other {memory s} {write1} {addr} {orig-r14} (λ eq → addr≢write1 (sym eq))

-- | Execute pair middle instructions (mov [r15], rax; mov rdi, r14) at arbitrary offset
-- Used for phase 3 of pair construction - storing f's result and restoring input
-- Instructions:
--   mov [r15], rax   - store f's result at [r15] (stable pair base)
--   mov rdi, r14     - restore original input from r14 to rdi
exec-pair-middle-at : ∀ (prefix : Program) (rest : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] (exec 2 (prefix ++ mov (mem (base r15)) (reg rax) ∷ mov (reg rdi) (reg r14) ∷ rest) s ≡ just s'
         × halted s' ≡ false
         × pc s' ≡ length prefix +ℕ 2
         × readReg (regs s') rdi ≡ readReg (regs s) r14
         × readMem (memory s') (readReg (regs s') r15) ≡ just (readReg (regs s) rax)
         × readReg (regs s') r15 ≡ readReg (regs s) r15
         × readReg (regs s') rsp ≡ readReg (regs s) rsp
         -- Memory preservation: addresses ≠ r15 are unchanged (only r15 is written)
         × (∀ addr → addr ≢ readReg (regs s) r15 → readMem (memory s') addr ≡ readMem (memory s) addr))
exec-pair-middle-at prefix rest s h-false pc-eq = s-final , exec-eq , h-final , pc-final , rdi-eq , mem-eq , r15-eq , rsp-eq , mem-above-eq
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (+-assoc)

    prog : Program
    prog = prefix ++ mov (mem (base r15)) (reg rax) ∷ mov (reg rdi) (reg r14) ∷ rest

    -- State after step 1: mov [r15], rax (store rax to memory at r15)
    s1 : State
    s1 = record s { memory = writeMem (memory s) (readReg (regs s) r15) (readReg (regs s) rax)
                  ; pc = pc s +ℕ 1 }

    -- Fetch mov [r15], rax at length prefix
    fetch0 : fetch prog (length prefix) ≡ just (mov (mem (base r15)) (reg rax))
    fetch0 = fetch-at-prefix-end prefix (mov (mem (base r15)) (reg rax)) (mov (reg rdi) (reg r14) ∷ rest)

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s (mov (mem (base r15)) (reg rax)) h-false
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base r15)) (reg rax))) (sym pc-eq) fetch0))
                  (execMov-mem-base-reg prog s r15 rax)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    -- State after step 2: mov rdi, r14
    s-final : State
    s-final = record s1 { regs = writeReg (regs s1) rdi (readReg (regs s1) r14)
                        ; pc = pc s1 +ℕ 1 }

    -- For fetch at position length prefix + 1, rearrange program
    prog-eq1 : prog ≡ (prefix ++ mov (mem (base r15)) (reg rax) ∷ []) ++ mov (reg rdi) (reg r14) ∷ rest
    prog-eq1 = sym (++-assoc prefix (mov (mem (base r15)) (reg rax) ∷ []) (mov (reg rdi) (reg r14) ∷ rest))

    len-prefix-1 : length (prefix ++ mov (mem (base r15)) (reg rax) ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = List-length-++ prefix {mov (mem (base r15)) (reg rax) ∷ []}

    fetch1-helper : fetch ((prefix ++ mov (mem (base r15)) (reg rax) ∷ []) ++ mov (reg rdi) (reg r14) ∷ rest)
                         (length (prefix ++ mov (mem (base r15)) (reg rax) ∷ []))
                  ≡ just (mov (reg rdi) (reg r14))
    fetch1-helper = fetch-at-prefix-end (prefix ++ mov (mem (base r15)) (reg rax) ∷ []) (mov (reg rdi) (reg r14)) rest

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just (mov (reg rdi) (reg r14))
    fetch1 = subst₂ (λ p n → fetch p n ≡ just (mov (reg rdi) (reg r14))) (sym prog-eq1) len-prefix-1 fetch1-helper

    step2 : step prog s1 ≡ just s-final
    step2 = trans (step-exec prog s1 (mov (reg rdi) (reg r14)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (reg rdi) (reg r14))) (sym pc1) fetch1))
                  (execMov-reg-reg s1 rdi r14)

    h-final : halted s-final ≡ false
    h-final = h-false

    pc-final : pc s-final ≡ length prefix +ℕ 2
    pc-final = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    exec-eq : exec 2 prog s ≡ just s-final
    exec-eq = exec-two-steps-nonhalt prog s s1 s-final step1 h1 step2 h-final

    -- r14 in s1 is the same as in s (mov [r15], rax doesn't change registers)
    r14-s1-eq : readReg (regs s1) r14 ≡ readReg (regs s) r14
    r14-s1-eq = refl

    -- rdi gets r14's value from s1, which equals r14 from s
    rdi-eq : readReg (regs s-final) rdi ≡ readReg (regs s) r14
    rdi-eq = trans (readReg-writeReg-same (regs s1) rdi (readReg (regs s1) r14)) r14-s1-eq

    -- Memory at r15: s-final's memory came from s1, which came from writing rax to [r15]
    -- Need to show readMem (memory s-final) (readReg (regs s-final) r15) = just (rax from s)
    -- s-final's memory is s1's memory (mov rdi, r14 doesn't change memory)
    -- s1's memory has writeMem at (r15 of s) with value (rax of s)
    -- s-final's r15 is s1's r15 (mov rdi, r14 doesn't change r15)
    -- s1's r15 is s's r15 (mov [r15], rax doesn't change r15)

    r15-s1-eq : readReg (regs s1) r15 ≡ readReg (regs s) r15
    r15-s1-eq = refl

    r15-eq : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    r15-eq = trans (readReg-writeReg-rdi-r15 (regs s1) (readReg (regs s1) r14)) r15-s1-eq

    -- rsp is not touched by either instruction
    rsp-s1-eq : readReg (regs s1) rsp ≡ readReg (regs s) rsp
    rsp-s1-eq = refl

    rsp-eq : readReg (regs s-final) rsp ≡ readReg (regs s) rsp
    rsp-eq = trans (readReg-writeReg-rdi-rsp (regs s1) (readReg (regs s1) r14)) rsp-s1-eq

    mem-eq : readMem (memory s-final) (readReg (regs s-final) r15) ≡ just (readReg (regs s) rax)
    mem-eq = trans (cong (readMem (memory s-final)) r15-eq)
                   (readMem-writeMem-same (memory s) (readReg (regs s) r15) (readReg (regs s) rax))

    -- Memory preservation: only write is at r15, so other addresses are preserved
    -- s1.memory = writeMem (memory s) r15 rax
    -- s-final.memory = s1.memory (mov rdi, r14 is register-only)
    mem-above-eq : ∀ addr → addr ≢ readReg (regs s) r15 → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-above-eq addr addr≢r15 = mem-read-other {memory s} {readReg (regs s) r15} {addr} {readReg (regs s) rax} (λ eq → addr≢r15 (sym eq))

-- NOTE: exec-pair-final-at was removed - it was dead code with an outdated
-- instruction sequence (used add rsp, 16 instead of mov rsp, rbp).
-- The actual proof uses inline postulates in run-pair-at-offset.
-- See docs/formal/x86-full-proof-architecture.md for the correct approach.

-- | Execute id at arbitrary offset in a program (non-halting)
-- This is the general case of run-id-nonhalt where id code can be at any position
-- Program structure: prefix ++ [mov rax, rdi] ++ suffix
-- NOTE: run-*-at-offset functions and Common.Exec are imported from ExecLemmas

-- Helper: running a single-instruction program (mov reg, reg)
--
-- Proof outline:
-- 1. First step executes mov, producing s1 with pc=1, updated regs, halted=false
-- 2. Second step: fetch at pc=1 fails, sets halted=true
-- 3. exec-two-steps combines these
run-single-mov : ∀ (s : State) (dst src : Reg) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (mov (reg dst) (reg src) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ readReg (regs s) src
         × halted s' ≡ true)
run-single-mov s dst src h-false pc-0 = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (reg src) ∷ []

    -- State after first step: execute mov (use pc s +ℕ 1 to match execMov-reg-reg)
    s1 : State
    s1 = record s { regs = writeReg (regs s) dst (readReg (regs s) src)
                  ; pc = pc s +ℕ 1 }

    -- State after second step: halted
    s2 : State
    s2 = record s1 { halted = true }

    -- First step produces s1
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (reg src)) [] s h-false pc-0)
                  (execMov-reg-reg s dst src)

    -- s1 is not halted
    h1 : halted s1 ≡ false
    h1 = h-false  -- halted field unchanged in s1

    -- s1 has pc = pc s + 1 = 0 + 1 = 1
    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- fetch at pc s1 = 1 fails
    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    -- Second step produces s2 (halted)
    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    -- s2 is halted
    halt-eq : halted s2 ≡ true
    halt-eq = refl

    -- Register value is preserved: regs s2 = regs s1 = writeReg (regs s) dst (readReg (regs s) src)
    rax-eq : readReg (regs s2) dst ≡ readReg (regs s) src
    rax-eq = readReg-writeReg-same (regs s) dst (readReg (regs s) src)

    -- run = exec defaultFuel, defaultFuel = 10000 = suc (suc 9998)
    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: running a single-instruction program (mov reg, imm)
run-single-mov-imm : ∀ (s : State) (dst : Reg) (n : ℕ) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (mov (reg dst) (imm n) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ n
         × halted s' ≡ true)
run-single-mov-imm s dst n h-false pc-0 = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (imm n) ∷ []

    s1 : State
    s1 = record s { regs = writeReg (regs s) dst n ; pc = pc s +ℕ 1 }

    s2 : State
    s2 = record s1 { halted = true }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (imm n)) [] s h-false pc-0)
                  (execMov-reg-imm s dst n)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    halt-eq : halted s2 ≡ true
    halt-eq = refl

    rax-eq : readReg (regs s2) dst ≡ n
    rax-eq = readReg-writeReg-same (regs s) dst n

    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: running a single-instruction program (mov reg, [reg])
-- Loads from memory at address in src register
run-single-mov-mem-base : ∀ (s : State) (dst src : Reg) (v : ℕ) →
  halted s ≡ false →
  pc s ≡ 0 →
  readMem (memory s) (readReg (regs s) src) ≡ just v →
  ∃[ s' ] (run (mov (reg dst) (mem (base src)) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ v
         × halted s' ≡ true)
run-single-mov-mem-base s dst src v h-false pc-0 mem-ok = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (mem (base src)) ∷ []

    s1 : State
    s1 = record s { regs = writeReg (regs s) dst v ; pc = pc s +ℕ 1 }

    s2 : State
    s2 = record s1 { halted = true }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (mem (base src))) [] s h-false pc-0)
                  (execMov-reg-mem-base s dst src v mem-ok)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    halt-eq : halted s2 ≡ true
    halt-eq = refl

    rax-eq : readReg (regs s2) dst ≡ v
    rax-eq = readReg-writeReg-same (regs s) dst v

    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: running a single-instruction program (mov reg, [reg+disp])
-- Loads from memory at address (src register + displacement)
run-single-mov-mem-disp : ∀ (s : State) (dst src : Reg) (disp : ℕ) (v : ℕ) →
  halted s ≡ false →
  pc s ≡ 0 →
  readMem (memory s) (readReg (regs s) src +ℕ disp) ≡ just v →
  ∃[ s' ] (run (mov (reg dst) (mem (base+disp src disp)) ∷ []) s ≡ just s'
         × readReg (regs s') dst ≡ v
         × halted s' ≡ true)
run-single-mov-mem-disp s dst src disp v h-false pc-0 mem-ok = s2 , run-eq , rax-eq , halt-eq
  where
    prog : List Instr
    prog = mov (reg dst) (mem (base+disp src disp)) ∷ []

    s1 : State
    s1 = record s { regs = writeReg (regs s) dst v ; pc = pc s +ℕ 1 }

    s2 : State
    s2 = record s1 { halted = true }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (mov (reg dst) (mem (base+disp src disp))) [] s h-false pc-0)
                  (execMov-reg-mem-disp s dst src disp v mem-ok)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    fetch-fail : fetch prog (pc s1) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc1) refl

    step2 : step prog s1 ≡ just s2
    step2 = step-halt-on-fetch-fail prog s1 h1 fetch-fail

    halt-eq : halted s2 ≡ true
    halt-eq = refl

    rax-eq : readReg (regs s2) dst ≡ v
    rax-eq = readReg-writeReg-same (regs s) dst v

    run-eq : run prog s ≡ just s2
    run-eq = exec-two-steps 9998 prog s s1 s2 step1 h1 step2 halt-eq

-- Helper: inl instruction sequence
-- sub rsp, 16; mov [rsp], 0; mov [rsp+8], rdi; mov rax, rsp
-- Effect: allocates tagged union on stack with tag=0, value=input
--
-- Proof: trace through 5 steps (4 instructions + implicit halt when fetch fails at pc=4)
run-inl-seq : ∀ {A B} (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (compile-x86 (inl {_} {A} {B})) s ≡ just s'
         × halted s' ≡ true
         -- rax points to stack-allocated sum
         × readReg (regs s') rax ≡ readReg (regs s') rsp
         -- tag at [rax] = 0
         × readMem (memory s') (readReg (regs s') rax) ≡ just 0
         -- value at [rax+8] = original rdi
         × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))
run-inl-seq {A} {B} s h-false pc-0 = s5 , run-eq , halt-eq , rax-rsp-eq , tag-eq , val-eq
  where
    prog : List Instr
    prog = compile-x86 (inl {_} {A} {B})

    -- Original values we need to track
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    -- Use pc s +ℕ 1 to match execSub-reg-imm output
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (sub (reg rsp) (imm 16)) _ s h-false pc-0)
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov [rsp], 0
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 0
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (mem (base rsp)) (imm 0)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base rsp)) (imm 0))) (sym pc1) refl))
                  (execMov-mem-base-imm prog s1 rsp 0)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (mem (base+disp rsp 8)) (reg rdi)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base+disp rsp 8)) (reg rdi))) (sym pc2) refl))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg rax) (reg rsp)) h3
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rsp))) (sym pc3) refl))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 4
    pc4 = cong (λ x → x +ℕ 1) pc3

    -- State after step 5: fetch fails at pc=4, sets halted=true
    s5 : State
    s5 = record s4 { halted = true }

    fetch-fail : fetch prog (pc s4) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc4) refl

    step5 : step prog s4 ≡ just s5
    step5 = step-halt-on-fetch-fail prog s4 h4 fetch-fail

    halt-eq : halted s5 ≡ true
    halt-eq = refl

    -- Combined execution
    run-eq : run prog s ≡ just s5
    run-eq = exec-five-steps 9995 prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 halt-eq

    -- Now prove the properties about s5

    -- rax = rsp in s5 (both unchanged from s4)
    rax-rsp-eq : readReg (regs s5) rax ≡ readReg (regs s5) rsp
    rax-rsp-eq = readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)

    -- Helper: rsp is constant through s1,s2,s3 since only sub modifies it in s1
    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    -- Helper: rdi is constant through all states (never modified)
    -- In s1, only rsp was modified by sub instruction
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1  -- regs s2 = regs s1 (mov [rsp], 0 doesn't touch registers)

    -- Helper: rax in s5 = rsp in s3 = new-rsp
    rax-s5 : readReg (regs s5) rax ≡ new-rsp
    rax-s5 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    -- Key: new-rsp ≠ new-rsp + 8
    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- tag at [rax] = 0
    -- Memory path: s5.memory = s3.memory = writeMem s2.memory (new-rsp+8) rdi
    --              s2.memory = writeMem s1.memory new-rsp 0
    -- Reading at new-rsp: first write doesn't touch it (different addr), second does
    tag-eq : readMem (memory s5) (readReg (regs s5) rax) ≡ just 0
    tag-eq = trans (cong (readMem (memory s5)) rax-s5)
                   (trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi) (λ eq → addr-disjoint (sym eq)))
                          (readMem-writeMem-same (memory s1) new-rsp 0))

    -- value at [rax+8] = original rdi
    -- Memory path: same as above, but reading at new-rsp+8
    val-eq : readMem (memory s5) (readReg (regs s5) rax +ℕ 8) ≡ just (readReg (regs s) rdi)
    val-eq = trans (cong (λ a → readMem (memory s5) (a +ℕ 8)) rax-s5)
                   (trans (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi))
                          (cong just rdi-s2))

-- Helper: inr instruction sequence (similar to inl but tag=1)
-- Proof: identical structure to run-inl-seq, just writes tag=1 instead of tag=0
run-inr-seq : ∀ {A B} (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  ∃[ s' ] (run (compile-x86 (inr {_} {A} {B})) s ≡ just s'
         × halted s' ≡ true
         × readReg (regs s') rax ≡ readReg (regs s') rsp
         × readMem (memory s') (readReg (regs s') rax) ≡ just 1
         × readMem (memory s') (readReg (regs s') rax +ℕ 8) ≡ just (readReg (regs s) rdi))
run-inr-seq {A} {B} s h-false pc-0 = s5 , run-eq , halt-eq , rax-rsp-eq , tag-eq , val-eq
  where
    prog : List Instr
    prog = compile-x86 (inr {_} {A} {B})

    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    orig-rdi : Word
    orig-rdi = readReg (regs s) rdi

    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- State after step 1: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec-0 (sub (reg rsp) (imm 16)) _ s h-false pc-0)
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ 1
    pc1 = cong (λ x → x +ℕ 1) pc-0

    -- State after step 2: mov [rsp], 1 (tag = 1 for inr)
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) 1
                   ; pc = pc s1 +ℕ 1 }

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (mem (base rsp)) (imm 1)) h1
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base rsp)) (imm 1))) (sym pc1) refl))
                  (execMov-mem-base-imm prog s1 rsp 1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ 2
    pc2 = cong (λ x → x +ℕ 1) pc1

    -- State after step 3: mov [rsp+8], rdi
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (readReg (regs s2) rsp +ℕ 8) (readReg (regs s2) rdi)
                   ; pc = pc s2 +ℕ 1 }

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (mem (base+disp rsp 8)) (reg rdi)) h2
                             (subst (λ p → fetch prog p ≡ just (mov (mem (base+disp rsp 8)) (reg rdi))) (sym pc2) refl))
                  (execMov-mem-disp-reg prog s2 rsp rdi 8)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ 3
    pc3 = cong (λ x → x +ℕ 1) pc2

    -- State after step 4: mov rax, rsp
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rax (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (mov (reg rax) (reg rsp)) h3
                             (subst (λ p → fetch prog p ≡ just (mov (reg rax) (reg rsp))) (sym pc3) refl))
                  (execMov-reg-reg s3 rax rsp)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ 4
    pc4 = cong (λ x → x +ℕ 1) pc3

    -- State after step 5: fetch fails at pc=4, sets halted=true
    s5 : State
    s5 = record s4 { halted = true }

    fetch-fail : fetch prog (pc s4) ≡ nothing
    fetch-fail = subst (λ p → fetch prog p ≡ nothing) (sym pc4) refl

    step5 : step prog s4 ≡ just s5
    step5 = step-halt-on-fetch-fail prog s4 h4 fetch-fail

    halt-eq : halted s5 ≡ true
    halt-eq = refl

    run-eq : run prog s ≡ just s5
    run-eq = exec-five-steps 9995 prog s s1 s2 s3 s4 s5 step1 h1 step2 h2 step3 h3 step4 h4 step5 halt-eq

    -- Properties about s5
    rax-rsp-eq : readReg (regs s5) rax ≡ readReg (regs s5) rsp
    rax-rsp-eq = readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)

    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = readReg-writeReg-same (regs s) rsp new-rsp

    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = rsp-s2

    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1

    rax-s5 : readReg (regs s5) rax ≡ new-rsp
    rax-s5 = trans (readReg-writeReg-same (regs s3) rax (readReg (regs s3) rsp)) rsp-s3

    addr-disjoint : new-rsp ≢ new-rsp +ℕ 8
    addr-disjoint = n≢n+suc new-rsp 7

    -- tag at [rax] = 1
    tag-eq : readMem (memory s5) (readReg (regs s5) rax) ≡ just 1
    tag-eq = trans (cong (readMem (memory s5)) rax-s5)
                   (trans (readMem-writeMem-diff (memory s2) (new-rsp +ℕ 8) new-rsp (readReg (regs s2) rdi) (λ eq → addr-disjoint (sym eq)))
                          (readMem-writeMem-same (memory s1) new-rsp 1))

    -- value at [rax+8] = original rdi
    val-eq : readMem (memory s5) (readReg (regs s5) rax +ℕ 8) ≡ just (readReg (regs s) rdi)
    val-eq = trans (cong (λ a → readMem (memory s5) (a +ℕ 8)) rax-s5)
                   (trans (readMem-writeMem-same (memory s2) (new-rsp +ℕ 8) (readReg (regs s2) rdi))
                          (cong just rdi-s2))

------------------------------------------------------------------------
-- Case Setup Helpers (Generalized)
--
-- These helpers encapsulate the case dispatch setup:
--   inl: 4 instructions (load tag, cmp, jne not taken, load value)
--   inr: 3 instructions (load tag, cmp, jne taken -> jump to right branch)
------------------------------------------------------------------------

-- | Result record for case-inl setup (4 instructions, jne NOT taken)
-- Note: r15 is preserved because we use r11 (scratch) for tag loading
record CaseInlSetupResult (prog : Program) (s s' : State) (prefix : Program) (val : ℕ) : Set where
  field
    exec-eq   : exec 4 prog s ≡ just s'
    halted-eq : halted s' ≡ false
    pc-eq     : pc s' ≡ length prefix +ℕ 4
    rdi-eq    : readReg (regs s') rdi ≡ val
    r14-eq    : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq    : readReg (regs s') r15 ≡ readReg (regs s) r15  -- preserved (uses r11 for tag)
    rbp-eq    : readReg (regs s') rbp ≡ readReg (regs s) rbp
    rsp-eq    : readReg (regs s') rsp ≡ readReg (regs s) rsp
    mem-eq    : memory s' ≡ memory s

-- | Result record for case-inr setup (3 instructions, jne TAKEN)
-- Note: r15 is preserved because we use r11 (scratch) for tag loading
record CaseInrSetupResult (prog : Program) (s s' : State) (prefix : Program) (jne-offset : ℕ) : Set where
  field
    exec-eq   : exec 3 prog s ≡ just s'
    halted-eq : halted s' ≡ false
    pc-eq     : pc s' ≡ length prefix +ℕ 3 +ℕ jne-offset
    rdi-eq    : readReg (regs s') rdi ≡ readReg (regs s) rdi  -- unchanged
    r14-eq    : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-eq    : readReg (regs s') r15 ≡ readReg (regs s) r15  -- preserved (uses r11 for tag)
    rbp-eq    : readReg (regs s') rbp ≡ readReg (regs s) rbp
    rsp-eq    : readReg (regs s') rsp ≡ readReg (regs s) rsp
    mem-eq    : memory s' ≡ memory s

-- | Execute case-inl setup at arbitrary offset
-- 4 instructions: mov r15 [rdi]; cmp r15 0; jne (not taken); mov rdi [rdi+8]
--
-- Preconditions:
--   - memory at rdi = 0 (tag for inl)
--   - memory at rdi+8 = val (the value to load)
--
-- Postconditions:
--   - rdi = val
--   - r15 = 0
--   - r14, rbp, rsp, rax unchanged
--   - memory unchanged
-- Note: Uses r11 (scratch register) for tag to preserve r15 (callee-save)
exec-case-inl-setup : ∀ (prefix suffix : Program) (jne-offset : ℕ) (val : ℕ) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readMem (memory s) (readReg (regs s) rdi) ≡ just 0 →
  readMem (memory s) (readReg (regs s) rdi +ℕ 8) ≡ just val →
  let prog = prefix ++ mov (reg r11) (mem (base rdi)) ∷
                        cmp (reg r11) (imm 0) ∷
                        jne jne-offset ∷
                        mov (reg rdi) (mem (base+disp rdi 8)) ∷ suffix
  in ∃[ s' ] CaseInlSetupResult prog s s' prefix val
exec-case-inl-setup prefix suffix jne-offset val s h-false pc-eq mem-tag mem-val =
  s4 , record { exec-eq = exec-eq ; halted-eq = h4 ; pc-eq = pc4 ; rdi-eq = rdi-s4
              ; r14-eq = r14-s4 ; r15-eq = r15-s4 ; rbp-eq = rbp-s4 ; rsp-eq = rsp-s4
              ; mem-eq = mem-s4 }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)

    i0 = mov (reg r11) (mem (base rdi))
    i1 = cmp (reg r11) (imm 0)
    i2 = jne jne-offset
    i3 = mov (reg rdi) (mem (base+disp rdi 8))
    prog = prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ suffix

    orig-rdi = readReg (regs s) rdi

    -- State after step 1: mov r11, [rdi] (loads tag=0 into scratch register)
    s1 : State
    s1 = record s { regs = writeReg (regs s) r11 0 ; pc = pc s +ℕ 1 }

    -- State after step 2: cmp r11, 0 (sets ZF=true since r11=0)
    s2 : State
    s2 = record s1 { pc = pc s1 +ℕ 1 ; flags = mkflags true false false }

    -- State after step 3: jne (not taken since ZF=true)
    s3 : State
    s3 = record s2 { pc = pc s2 +ℕ 1 }

    -- State after step 4: mov rdi, [rdi+8] (loads value)
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rdi val ; pc = pc s3 +ℕ 1 }

    -- Fetch proofs
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ suffix)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = List-length-++ prefix {i0 ∷ []}

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1
             (fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ suffix))

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = List-length-++ prefix {i0 ∷ i1 ∷ []}

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2
             (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ suffix))

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = List-length-++ prefix {i0 ∷ i1 ∷ i2 ∷ []}

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3
             (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 suffix)

    -- Step proofs
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execMov-reg-mem-base s r11 rdi 0 mem-tag)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- r11 in s1 = 0 (scratch register for tag)
    r11-s1 : readReg (regs s1) r11 ≡ 0
    r11-s1 = readReg-writeReg-same (regs s) r11 0

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execCmp-zero prog s1 r11 r11-s1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- ZF in s2 = true (from cmp r11, 0 when r11=0)
    zf-s2 : zf (flags s2) ≡ true
    zf-s2 = refl

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execJne-not-taken prog s2 jne-offset zf-s2)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    -- rdi unchanged through s1, s2, s3 (we write to r11, not r15)
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-r11-rdi (regs s) 0

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = rdi-s1

    rdi-s3 : readReg (regs s3) rdi ≡ orig-rdi
    rdi-s3 = rdi-s2

    -- memory at rdi+8 in s3 (unchanged)
    mem-s3 : readMem (memory s3) (readReg (regs s3) rdi +ℕ 8) ≡ just val
    mem-s3 = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just val) (sym rdi-s3) mem-val

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-reg-mem-disp s3 rdi rdi 8 val mem-s3)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Final register values
    rdi-s4 : readReg (regs s4) rdi ≡ val
    rdi-s4 = readReg-writeReg-same (regs s3) rdi val

    r14-s4 : readReg (regs s4) r14 ≡ readReg (regs s) r14
    r14-s4 = trans (readReg-writeReg-rdi-r14 (regs s3) val)
             (readReg-writeReg-r11-r14 (regs s) 0)

    r15-s4 : readReg (regs s4) r15 ≡ readReg (regs s) r15
    r15-s4 = trans (readReg-writeReg-rdi-r15 (regs s3) val)
             (readReg-writeReg-r11-r15 (regs s) 0)

    rbp-s4 : readReg (regs s4) rbp ≡ readReg (regs s) rbp
    rbp-s4 = trans (readReg-writeReg-rdi-rbp (regs s3) val)
             (readReg-writeReg-r11-rbp (regs s) 0)

    rsp-s4 : readReg (regs s4) rsp ≡ readReg (regs s) rsp
    rsp-s4 = trans (readReg-writeReg-rdi-rsp (regs s3) val)
             (readReg-writeReg-r11-rsp (regs s) 0)

    mem-s4 : memory s4 ≡ memory s
    mem-s4 = refl

    -- Execution proof
    exec-eq : exec 4 prog s ≡ just s4
    exec-eq = exec-four-steps-nonhalt prog s s1 s2 s3 s4 step1 h1 step2 h2 step3 h3 step4 h4

------------------------------------------------------------------------
-- Case-inr Setup Helper (3 instructions, jne TAKEN)
------------------------------------------------------------------------
--
-- For case-inr, the tag is 1 (not 0), so jne is TAKEN.
-- 3 instructions: mov r11 [rdi]; cmp r11 0; jne (taken)
--
-- After execution:
--   pc = length prefix + 3 + jne-offset  (jumped to right branch)
--   r15 = unchanged (uses r11 scratch for tag)
--   rdi = unchanged
--   r14, rbp, rsp, memory unchanged
-- Note: Uses r11 (scratch register) for tag to preserve r15 (callee-save)
exec-case-inr-setup : ∀ (prefix suffix : Program) (jne-offset : ℕ) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readMem (memory s) (readReg (regs s) rdi) ≡ just 1 →  -- tag = 1 for inr
  let prog = prefix ++ mov (reg r11) (mem (base rdi)) ∷
                        cmp (reg r11) (imm 0) ∷
                        jne jne-offset ∷ suffix
  in ∃[ s' ] CaseInrSetupResult prog s s' prefix jne-offset
exec-case-inr-setup prefix suffix jne-offset s h-false pc-eq mem-tag =
  s3 , record { exec-eq = exec-eq ; halted-eq = h3 ; pc-eq = pc3 ; rdi-eq = rdi-s3
              ; r14-eq = r14-s3 ; r15-eq = r15-s3 ; rbp-eq = rbp-s3 ; rsp-eq = rsp-s3
              ; mem-eq = mem-s3 }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (+-assoc; +-comm; +-suc)

    i0 = mov (reg r11) (mem (base rdi))
    i1 = cmp (reg r11) (imm 0)
    i2 = jne jne-offset
    prog = prefix ++ i0 ∷ i1 ∷ i2 ∷ suffix

    orig-rdi = readReg (regs s) rdi

    -- State after step 1: mov r11, [rdi] (loads tag=1 into scratch)
    s1 : State
    s1 = record s { regs = writeReg (regs s) r11 1 ; pc = pc s +ℕ 1 }

    -- State after step 2: cmp r11, 0 (sets ZF=false since r11=1)
    s2 : State
    s2 = record s1 { pc = pc s1 +ℕ 1 ; flags = mkflags false false false }

    -- State after step 3: jne (taken since ZF=false)
    s3 : State
    s3 = record s2 { pc = pc s2 +ℕ 1 +ℕ jne-offset }

    -- Fetch proofs
    prog-eq : prefix ++ i0 ∷ i1 ∷ i2 ∷ suffix ≡ prog
    prog-eq = refl

    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ suffix)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = trans (List-length-++ prefix) refl

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1
             (fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ suffix))

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = trans (List-length-++ prefix) refl

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2
             (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 suffix)

    -- Step proofs
    h0 : halted s ≡ false
    h0 = h-false

    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s i0 h0 (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execMov-reg-mem-base s r11 rdi 1 mem-tag)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = trans (cong (_+ℕ 1) pc-eq) refl

    -- r11 in s1 is now 1 (scratch register for tag)
    r11-s1 : readReg (regs s1) r11 ≡ 1
    r11-s1 = readReg-writeReg-same (regs s) r11 1

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execCmp-one prog s1 r11 r11-s1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- ZF in s2 = false (from cmp r11, 0 when r11=1)
    zf-s2 : zf (flags s2) ≡ false
    zf-s2 = refl

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execJne-taken prog s2 jne-offset zf-s2)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3 +ℕ jne-offset
    pc3 = trans (cong (λ p → p +ℕ 1 +ℕ jne-offset) pc2)
                (cong (_+ℕ jne-offset) (+-assoc (length prefix) 2 1))

    -- Final register values (r11 is scratch, so callee-save regs preserved)
    rdi-s3 : readReg (regs s3) rdi ≡ readReg (regs s) rdi
    rdi-s3 = readReg-writeReg-r11-rdi (regs s) 1

    r14-s3 : readReg (regs s3) r14 ≡ readReg (regs s) r14
    r14-s3 = readReg-writeReg-r11-r14 (regs s) 1

    r15-s3 : readReg (regs s3) r15 ≡ readReg (regs s) r15
    r15-s3 = readReg-writeReg-r11-r15 (regs s) 1

    rbp-s3 : readReg (regs s3) rbp ≡ readReg (regs s) rbp
    rbp-s3 = readReg-writeReg-r11-rbp (regs s) 1

    rsp-s3 : readReg (regs s3) rsp ≡ readReg (regs s) rsp
    rsp-s3 = readReg-writeReg-r11-rsp (regs s) 1

    mem-s3 : memory s3 ≡ memory s
    mem-s3 = refl

    -- Execution proof
    exec-eq : exec 3 prog s ≡ just s3
    exec-eq = exec-three-steps-nonhalt prog s s1 s2 s3 step1 h1 step2 h2 step3 h3

