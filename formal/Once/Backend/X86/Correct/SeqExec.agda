------------------------------------------------------------------------
-- Once.Backend.X86.Correct.SeqExec
--
-- Sequential execution helpers for pair setup, mov sequences, and
-- inl/inr instruction sequences.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.SeqExec where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Memory using (mem-read-write; mem-read-other)
open import Once.Backend.Common.Memory using (n≢n+suc)
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.StackInstantiation
  using (∸two-slot≢∸one-slot; ∸three-slot≢∸one-slot; ∸three-slot≢∸two-slot;
         slot-size; slots; StackCapacity; rsp-in-stack; rsp-sufficient; capacity-maintained;
         slots-mono-≤; pair-setup-consumed-slots;
         -- Symbolic capacity lemmas (replacing numeric output-fits-apply-cap, apply-cap-fits-pair-setup, etc.)
         output-fits-apply-cap; apply-cap-fits-pair-setup;
         output-slots≤pair-setup; single-slot-fits-apply-cap)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.Star using (Star; refl*; step*; star-trans; star-step2; star-step3; star-step4; star-step6; star-step7)
open import Once.Backend.Common.MemoryRegions using (InStack; InHeap; InCode)

open import Data.Nat using (_>_; _≥_; _≟_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; +-comm; +-assoc; +-identityʳ; ∸-+-assoc; <-irrefl; <⇒≤; ≤-<-trans)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

-- Import semantic arithmetic lemmas from Arithmetic module
open import Once.Backend.X86.Correct.Arithmetic
  using (rbp-plus-word≡r15-save; rbp-plus-pair≡r14-save;
         word-size; pair-alloc; saved-regs-size; frame-size)
open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-positive; pair-positive; regs-positive)

------------------------------------------------------------------------
-- FrameSetupResult: Star-based result for pair frame setup
------------------------------------------------------------------------

-- | Result of executing 7 pair setup instructions with Star semantics
-- Encapsulates all frame setup state and proofs, replacing nested tuples.
--
-- Setup instructions: push r14; push r15; push rbp; mov rbp,rsp; sub rsp,16; mov r15,rsp; mov r14,rdi
--
-- After execution:
--   rsp = orig_rsp - 40 (3 pushes of 8 bytes + sub 16)
--   rbp = orig_rsp - 24 (frame base, after 3 pushes)
--   r15 = rsp (pair base address)
--   r14 = orig_rdi (saved input)
--   Stack: [rbp+0]=orig_rbp, [rbp+8]=orig_r15, [rbp+16]=orig_r14
record FrameSetupResult (prog : Program) (s : State) (pc-after : ℕ) : Set where
  field
    -- Output state
    s-setup : State

    -- Star execution proof (not fuel-based)
    star-setup : Star prog s s-setup

    -- Non-halting
    h-setup : halted s-setup ≡ false

    -- PC advancement
    pc-setup : pc s-setup ≡ pc-after

    -- Register values after setup
    r14-setup : readReg (regs s-setup) r14 ≡ readReg (regs s) rdi
    rdi-setup : readReg (regs s-setup) rdi ≡ readReg (regs s) rdi
    r15-setup : readReg (regs s-setup) r15 ≡ readReg (regs s) rsp ∸ slots 5
    rsp-setup : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slots 5
    rbp-setup : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ slots 3

    -- Stack slot memory (rbp-relative addressing)
    -- These express memory layout without requiring arithmetic at use sites
    mem-slot0 : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just (readReg (regs s) rbp)
    mem-slot8 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slot-size) ≡ just (readReg (regs s) r15)
    mem-slot16 : readMem (memory s-setup) (readReg (regs s-setup) rbp +ℕ slots 2) ≡ just (readReg (regs s) r14)

    -- Memory preservation
    mem-above : ∀ addr → addr ≥ readReg (regs s) rsp → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-at-0 : readMem (memory s-setup) 0 ≡ readMem (memory s) 0
    mem-code : ∀ addr → InCode addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-heap : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr

-- | Execute pair setup with frame pointer at arbitrary offset in a program (non-halting)
-- 7 setup instructions: push r14; push r15; push rbp; mov rbp, rsp; sub rsp, 16; mov r15, rsp; mov r14, rdi
--
-- Stack usage: 3 pushes (24 bytes) + sub 16 = 40 bytes = 5 slots
-- Returns FrameSetupResult with Star-based execution proof and all frame properties.
frame-setup-star : ∀ (prefix : Program) (rest : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackCapacity s pair-setup-consumed-slots →   -- 3 pushes + 2 slots for sub
  let prog = prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
  in FrameSetupResult prog s (length prefix +ℕ 7)
frame-setup-star prefix rest s h-false pc-eq cap = record
  { s-setup = s7
  ; star-setup = star-eq
  ; h-setup = h7
  ; pc-setup = pc7
  ; r14-setup = r14-eq
  ; rdi-setup = rdi-eq
  ; r15-setup = r15-eq
  ; rsp-setup = rsp-eq
  ; rbp-setup = rbp-eq
  ; mem-slot0 = mem-rbp-eq
  ; mem-slot8 = mem-r15-eq
  ; mem-slot16 = mem-r14-eq
  ; mem-above = mem-above-eq
  ; mem-at-0 = mem-at-0
  ; mem-code = mem-code
  ; mem-heap = mem-heap
  }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (+-assoc)

    prog : Program
    prog = prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest

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

    -- Extract rsp bound from capacity - we need 5 slots total
    rsp-bound : orig-rsp > slots 5
    rsp-bound = rsp-sufficient cap

    -- Derive smaller bounds using slot monotonicity: 3 ≤ 5 → slots 3 ≤ slots 5
    rsp-gt-slots3 : orig-rsp > slots 3
    rsp-gt-slots3 = ≤-<-trans (slots-mono-≤ apply-cap-fits-pair-setup) rsp-bound

    -- Step 1: push r14 - save r14 to stack, decrement rsp by 8
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp (orig-rsp ∸ slot-size)
                  ; memory = writeMem (memory s) (orig-rsp ∸ slot-size) orig-r14
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

    rsp-s1 : readReg (regs s1) rsp ≡ orig-rsp ∸ slot-size
    rsp-s1 = readReg-writeReg-same (regs s) rsp (orig-rsp ∸ slot-size)

    r15-s1 : readReg (regs s1) r15 ≡ orig-r15
    r15-s1 = readReg-writeReg-rsp-r15 (regs s) (orig-rsp ∸ slot-size)

    rbp-s1 : readReg (regs s1) rbp ≡ orig-rbp
    rbp-s1 = readReg-writeReg-rsp-rbp (regs s) (orig-rsp ∸ slot-size)

    -- Step 2: push r15 - save r15 to stack, decrement rsp by 8
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rsp (readReg (regs s1) rsp ∸ slot-size)
                   ; memory = writeMem (memory s1) (readReg (regs s1) rsp ∸ slot-size) (readReg (regs s1) r15)
                   ; pc = pc s1 +ℕ 1 }

    prog-eq1 : prog ≡ (prefix ++ push (reg r14) ∷ []) ++ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
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

    rsp-s2-raw : readReg (regs s2) rsp ≡ readReg (regs s1) rsp ∸ slot-size
    rsp-s2-raw = readReg-writeReg-same (regs s1) rsp (readReg (regs s1) rsp ∸ slot-size)

    rsp-s2 : readReg (regs s2) rsp ≡ orig-rsp ∸ slots 2
    rsp-s2 = trans rsp-s2-raw (trans (cong (_∸ slot-size) rsp-s1) (∸-+-assoc orig-rsp slot-size slot-size))

    rbp-s2 : readReg (regs s2) rbp ≡ orig-rbp
    rbp-s2 = trans (readReg-writeReg-rsp-rbp (regs s1) (readReg (regs s1) rsp ∸ slot-size)) rbp-s1

    -- Step 3: push rbp - save rbp to stack, decrement rsp by 8
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rsp (readReg (regs s2) rsp ∸ slot-size)
                   ; memory = writeMem (memory s2) (readReg (regs s2) rsp ∸ slot-size) (readReg (regs s2) rbp)
                   ; pc = pc s2 +ℕ 1 }

    prog-eq2 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ []) ++ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
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

    rsp-s3-raw : readReg (regs s3) rsp ≡ readReg (regs s2) rsp ∸ slot-size
    rsp-s3-raw = readReg-writeReg-same (regs s2) rsp (readReg (regs s2) rsp ∸ slot-size)

    rsp-s3 : readReg (regs s3) rsp ≡ orig-rsp ∸ slots 3
    rsp-s3 = trans rsp-s3-raw (trans (cong (_∸ slot-size) rsp-s2) (∸-+-assoc orig-rsp (slots 2) slot-size))

    -- Step 4: mov rbp, rsp - set rbp to current rsp (frame base)
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rbp (readReg (regs s3) rsp)
                   ; pc = pc s3 +ℕ 1 }

    prog-eq3 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ []) ++ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
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

    rbp-s4 : readReg (regs s4) rbp ≡ orig-rsp ∸ slots 3
    rbp-s4 = trans (readReg-writeReg-same (regs s3) rbp (readReg (regs s3) rsp)) rsp-s3

    rsp-s4 : readReg (regs s4) rsp ≡ orig-rsp ∸ slots 3
    rsp-s4 = trans (readReg-writeReg-rbp-rsp (regs s3) (readReg (regs s3) rsp)) rsp-s3

    -- Step 5: sub rsp, 16 - allocate 16 bytes on stack
    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) rsp (readReg (regs s4) rsp ∸ slots 2)
                   ; pc = pc s4 +ℕ 1
                   ; flags = updateFlags (readReg (regs s4) rsp ∸ slots 2) (readReg (regs s4) rsp) }

    prog-eq4 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ []) ++ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq4 = sym (++-assoc prefix _ _)

    len-prefix4 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ []) ≡ length prefix +ℕ 4
    len-prefix4 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch5 : fetch prog (length prefix +ℕ 4) ≡ just (sub (reg rsp) (imm (slots 2)))
    fetch5 = subst₂ (λ p n → fetch p n ≡ just (sub (reg rsp) (imm (slots 2)))) (sym prog-eq4) len-prefix4
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ []) (sub (reg rsp) (imm (slots 2))) _)

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (sub (reg rsp) (imm (slots 2))) h4
                             (subst (λ n → fetch prog n ≡ just (sub (reg rsp) (imm (slots 2)))) (sym pc4) fetch5))
                  (execSub-reg-imm prog s4 rsp (slots 2))

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (λ n → n +ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    rsp-s5-raw : readReg (regs s5) rsp ≡ readReg (regs s4) rsp ∸ slots 2
    rsp-s5-raw = readReg-writeReg-same (regs s4) rsp (readReg (regs s4) rsp ∸ slots 2)

    rsp-s5 : readReg (regs s5) rsp ≡ orig-rsp ∸ slots 5
    rsp-s5 = trans rsp-s5-raw (trans (cong (_∸ slots 2) rsp-s4) (∸-+-assoc orig-rsp (slots 3) (slots 2)))

    rbp-s5 : readReg (regs s5) rbp ≡ orig-rsp ∸ slots 3
    rbp-s5 = trans (readReg-writeReg-rsp-rbp (regs s4) (readReg (regs s4) rsp ∸ slots 2)) rbp-s4

    -- Step 6: mov r15, rsp - set r15 to current rsp (pair base address)
    s6 : State
    s6 = record s5 { regs = writeReg (regs s5) r15 (readReg (regs s5) rsp)
                   ; pc = pc s5 +ℕ 1 }

    prog-eq5 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ []) ++ mov (reg r15) (reg rsp) ∷ mov (reg r14) (reg rdi) ∷ rest
    prog-eq5 = sym (++-assoc prefix _ _)

    len-prefix5 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ []) ≡ length prefix +ℕ 5
    len-prefix5 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch6 : fetch prog (length prefix +ℕ 5) ≡ just (mov (reg r15) (reg rsp))
    fetch6 = subst₂ (λ p n → fetch p n ≡ just (mov (reg r15) (reg rsp))) (sym prog-eq5) len-prefix5
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ []) (mov (reg r15) (reg rsp)) _)

    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (mov (reg r15) (reg rsp)) h5
                             (subst (λ n → fetch prog n ≡ just (mov (reg r15) (reg rsp))) (sym pc5) fetch6))
                  (execMov-reg-reg s5 r15 rsp)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ length prefix +ℕ 6
    pc6 = trans (cong (λ n → n +ℕ 1) pc5) (+-assoc (length prefix) 5 1)

    r15-s6 : readReg (regs s6) r15 ≡ orig-rsp ∸ slots 5
    r15-s6 = trans (readReg-writeReg-same (regs s5) r15 (readReg (regs s5) rsp)) rsp-s5

    rsp-s6 : readReg (regs s6) rsp ≡ orig-rsp ∸ slots 5
    rsp-s6 = trans (readReg-writeReg-r15-rsp (regs s5) (readReg (regs s5) rsp)) rsp-s5

    rbp-s6 : readReg (regs s6) rbp ≡ orig-rsp ∸ slots 3
    rbp-s6 = trans (readReg-writeReg-r15-rbp (regs s5) (readReg (regs s5) rsp)) rbp-s5

    rdi-s6 : readReg (regs s6) rdi ≡ orig-rdi
    rdi-s6 = trans (readReg-writeReg-r15-rdi (regs s5) (readReg (regs s5) rsp))
                   (trans (readReg-writeReg-rsp-rdi (regs s4) (readReg (regs s4) rsp ∸ slots 2))
                          (trans (readReg-writeReg-rbp-rdi (regs s3) (readReg (regs s3) rsp))
                                 (trans (readReg-writeReg-rsp-rdi (regs s2) (readReg (regs s2) rsp ∸ slot-size))
                                        (trans (readReg-writeReg-rsp-rdi (regs s1) (readReg (regs s1) rsp ∸ slot-size))
                                               (readReg-writeReg-rsp-rdi (regs s) (orig-rsp ∸ slot-size))))))

    -- Step 7: mov r14, rdi - save input to r14
    s7 : State
    s7 = record s6 { regs = writeReg (regs s6) r14 (readReg (regs s6) rdi)
                   ; pc = pc s6 +ℕ 1 }

    prog-eq6 : prog ≡ (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ []) ++ mov (reg r14) (reg rdi) ∷ rest
    prog-eq6 = sym (++-assoc prefix _ _)

    len-prefix6 : length (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ []) ≡ length prefix +ℕ 6
    len-prefix6 = trans (List-length-++ prefix) (cong (length prefix +ℕ_) refl)

    fetch7 : fetch prog (length prefix +ℕ 6) ≡ just (mov (reg r14) (reg rdi))
    fetch7 = subst₂ (λ p n → fetch p n ≡ just (mov (reg r14) (reg rdi))) (sym prog-eq6) len-prefix6
                    (fetch-at-prefix-end (prefix ++ push (reg r14) ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷ sub (reg rsp) (imm (slots 2)) ∷ mov (reg r15) (reg rsp) ∷ []) (mov (reg r14) (reg rdi)) _)

    step7 : step prog s6 ≡ just s7
    step7 = trans (step-exec prog s6 (mov (reg r14) (reg rdi)) h6
                             (subst (λ n → fetch prog n ≡ just (mov (reg r14) (reg rdi))) (sym pc6) fetch7))
                  (execMov-reg-reg s6 r14 rdi)

    h7 : halted s7 ≡ false
    h7 = h-false

    pc7 : pc s7 ≡ length prefix +ℕ 7
    pc7 = trans (cong (λ n → n +ℕ 1) pc6) (+-assoc (length prefix) 6 1)

    star-eq : Star prog s s7
    star-eq = star-step7 h-false step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7

    r14-eq : readReg (regs s7) r14 ≡ orig-rdi
    r14-eq = trans (readReg-writeReg-same (regs s6) r14 (readReg (regs s6) rdi)) rdi-s6

    rdi-eq : readReg (regs s7) rdi ≡ orig-rdi
    rdi-eq = trans (readReg-writeReg-r14-rdi (regs s6) (readReg (regs s6) rdi)) rdi-s6

    r15-eq : readReg (regs s7) r15 ≡ orig-rsp ∸ slots 5
    r15-eq = trans (readReg-writeReg-r14-r15 (regs s6) (readReg (regs s6) rdi)) r15-s6

    rsp-eq : readReg (regs s7) rsp ≡ orig-rsp ∸ slots 5
    rsp-eq = trans (readReg-writeReg-r14-rsp (regs s6) (readReg (regs s6) rdi)) rsp-s6

    rbp-eq : readReg (regs s7) rbp ≡ orig-rsp ∸ slots 3
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
    write-addr-s3 : readReg (regs s2) rsp ∸ slot-size ≡ orig-rsp ∸ slots 3
    write-addr-s3 = trans (cong (_∸ slot-size) rsp-s2) (∸-+-assoc orig-rsp (slots 2) slot-size)

    -- Memory after step 3: push rbp wrote orig-rbp to [orig-rsp - 24]
    -- Steps 4-7 don't write to memory (only mov/sub instructions)
    mem-s3-at-rbp : readMem (memory s3) (orig-rsp ∸ slots 3) ≡ just orig-rbp
    mem-s3-at-rbp = begin
        readMem (memory s3) (orig-rsp ∸ slots 3)
      ≡⟨⟩
        readMem (writeMem (memory s2) (readReg (regs s2) rsp ∸ slot-size) (readReg (regs s2) rbp)) (orig-rsp ∸ slots 3)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rbp)) (orig-rsp ∸ slots 3)) write-addr-s3 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ slots 3) (readReg (regs s2) rbp)) (orig-rsp ∸ slots 3)
      ≡⟨ cong (λ v → readMem (writeMem (memory s2) (orig-rsp ∸ slots 3) v) (orig-rsp ∸ slots 3)) rbp-s2 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ slots 3) orig-rbp) (orig-rsp ∸ slots 3)
      ≡⟨ mem-read-write {memory s2} {orig-rsp ∸ slots 3} {orig-rbp} ⟩
        just orig-rbp
      ∎

    -- Address where step 2 writes: (orig-rsp - 8) - 8 = orig-rsp - 16
    write-addr-s2 : readReg (regs s1) rsp ∸ slot-size ≡ orig-rsp ∸ slots 2
    write-addr-s2 = trans (cong (_∸ slot-size) rsp-s1) (∸-+-assoc orig-rsp slot-size slot-size)

    -- Memory after step 2: push r15 wrote orig-r15 to [orig-rsp - 16]
    mem-s2-at-r15slot : readMem (memory s2) (orig-rsp ∸ slots 2) ≡ just orig-r15
    mem-s2-at-r15slot = begin
        readMem (memory s2) (orig-rsp ∸ slots 2)
      ≡⟨⟩
        readMem (writeMem (memory s1) (readReg (regs s1) rsp ∸ slot-size) (readReg (regs s1) r15)) (orig-rsp ∸ slots 2)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s1) addr (readReg (regs s1) r15)) (orig-rsp ∸ slots 2)) write-addr-s2 ⟩
        readMem (writeMem (memory s1) (orig-rsp ∸ slots 2) (readReg (regs s1) r15)) (orig-rsp ∸ slots 2)
      ≡⟨ cong (λ v → readMem (writeMem (memory s1) (orig-rsp ∸ slots 2) v) (orig-rsp ∸ slots 2)) r15-s1 ⟩
        readMem (writeMem (memory s1) (orig-rsp ∸ slots 2) orig-r15) (orig-rsp ∸ slots 2)
      ≡⟨ mem-read-write {memory s1} {orig-rsp ∸ slots 2} {orig-r15} ⟩
        just orig-r15
      ∎

    -- Memory after step 1: push r14 wrote orig-r14 to [orig-rsp - 8]
    -- s1.memory = writeMem (memory s) (orig-rsp ∸ slot-size) orig-r14
    mem-s1-at-r14slot : readMem (memory s1) (orig-rsp ∸ slot-size) ≡ just orig-r14
    mem-s1-at-r14slot = begin
        readMem (memory s1) (orig-rsp ∸ slot-size)
      ≡⟨⟩  -- by definition of s1
        readMem (writeMem (memory s) (orig-rsp ∸ slot-size) orig-r14) (orig-rsp ∸ slot-size)
      ≡⟨ mem-read-write {memory s} {orig-rsp ∸ slot-size} {orig-r14} ⟩
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
    -- s2.memory = writeMem (memory s1) (orig-rsp ∸ slots 2) orig-r15 (by write-addr-s2 and r15-s1)
    -- Derive rsp > slots 2 from rsp-gt-slots3 using slot monotonicity
    rsp-gt-slots2 : orig-rsp > slots 2
    rsp-gt-slots2 = ≤-<-trans (slots-mono-≤ output-fits-apply-cap) rsp-gt-slots3

    mem-s2-at-r14slot : readMem (memory s2) (orig-rsp ∸ slot-size) ≡ just orig-r14
    mem-s2-at-r14slot = begin
        readMem (memory s2) (orig-rsp ∸ slot-size)
      ≡⟨⟩
        readMem (writeMem (memory s1) (readReg (regs s1) rsp ∸ slot-size) (readReg (regs s1) r15)) (orig-rsp ∸ slot-size)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s1) addr (readReg (regs s1) r15)) (orig-rsp ∸ slot-size)) write-addr-s2 ⟩
        readMem (writeMem (memory s1) (orig-rsp ∸ slots 2) (readReg (regs s1) r15)) (orig-rsp ∸ slot-size)
      ≡⟨ mem-read-other {memory s1} {orig-rsp ∸ slots 2} {orig-rsp ∸ slot-size} {readReg (regs s1) r15} (∸two-slot≢∸one-slot orig-rsp rsp-gt-slots2) ⟩
        readMem (memory s1) (orig-rsp ∸ slot-size)
      ≡⟨ mem-s1-at-r14slot ⟩
        just orig-r14
      ∎

    -- Memory at [orig-rsp - 8] in s3 (after push rbp at step 3)
    -- push rbp wrote to [orig-rsp - 24], not [orig-rsp - 8]
    mem-s3-at-r14slot : readMem (memory s3) (orig-rsp ∸ slot-size) ≡ just orig-r14
    mem-s3-at-r14slot = begin
        readMem (memory s3) (orig-rsp ∸ slot-size)
      ≡⟨⟩
        readMem (writeMem (memory s2) (readReg (regs s2) rsp ∸ slot-size) (readReg (regs s2) rbp)) (orig-rsp ∸ slot-size)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rbp)) (orig-rsp ∸ slot-size)) write-addr-s3 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ slots 3) (readReg (regs s2) rbp)) (orig-rsp ∸ slot-size)
      ≡⟨ mem-read-other {memory s2} {orig-rsp ∸ slots 3} {orig-rsp ∸ slot-size} {readReg (regs s2) rbp} (∸three-slot≢∸one-slot orig-rsp rsp-gt-slots3) ⟩
        readMem (memory s2) (orig-rsp ∸ slot-size)
      ≡⟨ mem-s2-at-r14slot ⟩
        just orig-r14
      ∎

    -- Memory at [orig-rsp - 16] in s3 (after push rbp at step 3)
    -- push rbp wrote to [orig-rsp - 24], not [orig-rsp - 16]
    mem-s3-at-r15slot : readMem (memory s3) (orig-rsp ∸ slots 2) ≡ just orig-r15
    mem-s3-at-r15slot = begin
        readMem (memory s3) (orig-rsp ∸ slots 2)
      ≡⟨⟩
        readMem (writeMem (memory s2) (readReg (regs s2) rsp ∸ slot-size) (readReg (regs s2) rbp)) (orig-rsp ∸ slots 2)
      ≡⟨ cong (λ addr → readMem (writeMem (memory s2) addr (readReg (regs s2) rbp)) (orig-rsp ∸ slots 2)) write-addr-s3 ⟩
        readMem (writeMem (memory s2) (orig-rsp ∸ slots 3) (readReg (regs s2) rbp)) (orig-rsp ∸ slots 2)
      ≡⟨ mem-read-other {memory s2} {orig-rsp ∸ slots 3} {orig-rsp ∸ slots 2} {readReg (regs s2) rbp} (∸three-slot≢∸two-slot orig-rsp rsp-gt-slots3) ⟩
        readMem (memory s2) (orig-rsp ∸ slots 2)
      ≡⟨ mem-s2-at-r15slot ⟩
        just orig-r15
      ∎

    -- Final memory proofs in s7 (memory unchanged from s3)
    -- [rbp] = [orig-rsp - 24] = orig-rbp
    mem-rbp-eq : readMem (memory s7) (readReg (regs s7) rbp) ≡ just orig-rbp
    mem-rbp-eq = subst (λ addr → readMem (memory s7) addr ≡ just orig-rbp) (sym rbp-eq) mem-s3-at-rbp

    -- [rbp + 8] = [orig-rsp - 16] = orig-r15
    -- We need to show: (orig-rsp ∸ saved-regs-size) + word-size ≡ orig-rsp ∸ pair-alloc
    mem-r15-eq : readMem (memory s7) (readReg (regs s7) rbp +ℕ slot-size) ≡ just orig-r15
    mem-r15-eq = subst (λ addr → readMem (memory s7) (addr +ℕ slot-size) ≡ just orig-r15)
                       (sym rbp-eq)
                       (subst (λ a → readMem (memory s7) a ≡ just orig-r15)
                              (sym (rbp-plus-word≡r15-save orig-rsp (<⇒≤ rsp-gt-slots3)))
                              mem-s3-at-r15slot)

    -- [rbp + 16] = [orig-rsp - 8] = orig-r14
    -- We need to show: (orig-rsp ∸ saved-regs-size) + pair-alloc ≡ orig-rsp ∸ word-size
    mem-r14-eq : readMem (memory s7) (readReg (regs s7) rbp +ℕ slots 2) ≡ just orig-r14
    mem-r14-eq = subst (λ addr → readMem (memory s7) (addr +ℕ slots 2) ≡ just orig-r14)
                       (sym rbp-eq)
                       (subst (λ a → readMem (memory s7) a ≡ just orig-r14)
                              (sym (rbp-plus-pair≡r14-save orig-rsp (<⇒≤ rsp-gt-slots3)))
                              mem-s3-at-r14slot)

    -- Memory preservation: addresses >= orig-rsp are unchanged
    -- Writes happen at orig-rsp - 8, orig-rsp - 16, orig-rsp - 24 (all < orig-rsp)
    -- Steps 4-7 don't write memory
    mem-above-eq : ∀ addr → addr ≥ orig-rsp → readMem (memory s7) addr ≡ readMem (memory s) addr
    mem-above-eq addr addr≥rsp = trans mem-s7-s3 (trans mem-s3-s2 (trans mem-s2-s1 mem-s1-s))
      where
        open import Data.Nat.Properties using (≤-trans; <-≤-trans; ∸-monoʳ-<; <⇒≤)

        -- All write addresses are < orig-rsp, hence ≠ addr
        write1 = orig-rsp ∸ slot-size    -- step 1 write address
        write2 = orig-rsp ∸ slots 2   -- step 2 write address
        write3 = orig-rsp ∸ slots 3   -- step 3 write address

        -- Derive smaller bounds using slot monotonicity
        -- rsp > slots 1 (i.e., > 8)
        rsp-gt-slots1 : orig-rsp > slots 1
        rsp-gt-slots1 = ≤-<-trans (slots-mono-≤ single-slot-fits-apply-cap) rsp-gt-slots3

        -- 0 < slots k for positive k (needed for ∸-monoʳ-<)
        -- Use consolidated lemmas: word-positive = 0 < 8, pair-positive = 0 < 16, regs-positive = 0 < 24
        0<slot : 0 < slot-size
        0<slot = word-positive

        0<slots2 : 0 < slots 2
        0<slots2 = pair-positive

        0<slots3 : 0 < slots 3
        0<slots3 = regs-positive

        -- Bounds for memory write proofs
        slot1≤rsp : slot-size ≤ orig-rsp
        slot1≤rsp = <⇒≤ rsp-gt-slots1

        slots2≤rsp : slots 2 ≤ orig-rsp
        slots2≤rsp = <⇒≤ rsp-gt-slots2

        slots3≤rsp : slots 3 ≤ orig-rsp
        slots3≤rsp = <⇒≤ rsp-gt-slots3

        -- write1 < orig-rsp (using ∸-monoʳ-<)
        write1<rsp : write1 < orig-rsp
        write1<rsp = ∸-monoʳ-< 0<slot slot1≤rsp

        -- write2 < orig-rsp
        write2<rsp : write2 < orig-rsp
        write2<rsp = ∸-monoʳ-< 0<slots2 slots2≤rsp

        -- write3 < orig-rsp
        write3<rsp : write3 < orig-rsp
        write3<rsp = ∸-monoʳ-< 0<slots3 slots3≤rsp

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

    -- Memory at address 0 is preserved
    -- Uses abstract stackAddr-write-preserves-zero lemma (no inline arithmetic reasoning)
    mem-at-0 : readMem (memory s7) 0 ≡ readMem (memory s) 0
    mem-at-0 = trans mem0-s7-s3 (trans mem0-s3-s2 (trans mem0-s2-s1 mem0-s1-s))
      where
        open import Once.Backend.Common.MemoryRegions using (InStack; stackAddr-write-preserves-zero)

        -- Write addresses (from x86 semantics)
        write1 = orig-rsp ∸ slot-size
        write2 = orig-rsp ∸ slots 2
        write3 = orig-rsp ∸ slots 3

        -- Write addresses are in stack region (via capacity-maintained from cap parameter)
        write1-in-stack : InStack write1
        write1-in-stack = capacity-maintained cap 1 (s≤s z≤n)

        write2-in-stack : InStack write2
        write2-in-stack = capacity-maintained cap 2 output-slots≤pair-setup

        write3-in-stack : InStack write3
        write3-in-stack = capacity-maintained cap 3 apply-cap-fits-pair-setup

        -- Chain memory preservation at 0 using abstract lemma
        mem0-s7-s3 : readMem (memory s7) 0 ≡ readMem (memory s3) 0
        mem0-s7-s3 = refl

        mem0-s3-s2 : readMem (memory s3) 0 ≡ readMem (memory s2) 0
        mem0-s3-s2 = trans (cong (λ a → readMem (writeMem (memory s2) a (readReg (regs s2) rbp)) 0) write-addr-s3)
                          (stackAddr-write-preserves-zero (memory s2) write3 (readReg (regs s2) rbp) write3-in-stack)

        mem0-s2-s1 : readMem (memory s2) 0 ≡ readMem (memory s1) 0
        mem0-s2-s1 = trans (cong (λ a → readMem (writeMem (memory s1) a (readReg (regs s1) r15)) 0) write-addr-s2)
                          (stackAddr-write-preserves-zero (memory s1) write2 (readReg (regs s1) r15) write2-in-stack)

        mem0-s1-s : readMem (memory s1) 0 ≡ readMem (memory s) 0
        mem0-s1-s = stackAddr-write-preserves-zero (memory s) write1 orig-r14 write1-in-stack

    -- Memory at code-region addresses preserved (D041)
    mem-code : ∀ addr → InCode addr → readMem (memory s7) addr ≡ readMem (memory s) addr
    mem-code addr addr-in-code = trans memC-s7-s3 (trans memC-s3-s2 (trans memC-s2-s1 memC-s1-s))
      where
        open import Once.Backend.Common.MemoryRegions using (InStack; InCode; stackAddr-write-preserves-code)

        -- Write addresses (from x86 semantics)
        write1 = orig-rsp ∸ slot-size
        write2 = orig-rsp ∸ slots 2
        write3 = orig-rsp ∸ slots 3

        -- Write addresses are in stack region (via capacity-maintained from cap parameter)
        write1-in-stack : InStack write1
        write1-in-stack = capacity-maintained cap 1 (s≤s z≤n)

        write2-in-stack : InStack write2
        write2-in-stack = capacity-maintained cap 2 output-slots≤pair-setup

        write3-in-stack : InStack write3
        write3-in-stack = capacity-maintained cap 3 apply-cap-fits-pair-setup

        -- Chain memory preservation at code addresses using abstract lemma
        memC-s7-s3 : readMem (memory s7) addr ≡ readMem (memory s3) addr
        memC-s7-s3 = refl

        memC-s3-s2 : readMem (memory s3) addr ≡ readMem (memory s2) addr
        memC-s3-s2 = trans (cong (λ a → readMem (writeMem (memory s2) a (readReg (regs s2) rbp)) addr) write-addr-s3)
                          (stackAddr-write-preserves-code (memory s2) write3 (readReg (regs s2) rbp) addr write3-in-stack addr-in-code)

        memC-s2-s1 : readMem (memory s2) addr ≡ readMem (memory s1) addr
        memC-s2-s1 = trans (cong (λ a → readMem (writeMem (memory s1) a (readReg (regs s1) r15)) addr) write-addr-s2)
                          (stackAddr-write-preserves-code (memory s1) write2 (readReg (regs s1) r15) addr write2-in-stack addr-in-code)

        memC-s1-s : readMem (memory s1) addr ≡ readMem (memory s) addr
        memC-s1-s = stackAddr-write-preserves-code (memory s) write1 orig-r14 addr write1-in-stack addr-in-code

    -- Memory at heap-region addresses preserved (D041)
    mem-heap : ∀ addr → InHeap addr → readMem (memory s7) addr ≡ readMem (memory s) addr
    mem-heap addr addr-in-heap = trans memH-s7-s3 (trans memH-s3-s2 (trans memH-s2-s1 memH-s1-s))
      where
        open import Once.Backend.Common.MemoryRegions using (InStack; InHeap; stackAddr-write-preserves-heap)

        -- Write addresses (from x86 semantics)
        write1 = orig-rsp ∸ slot-size
        write2 = orig-rsp ∸ slots 2
        write3 = orig-rsp ∸ slots 3

        -- Write addresses are in stack region (via capacity-maintained from cap parameter)
        write1-in-stack : InStack write1
        write1-in-stack = capacity-maintained cap 1 (s≤s z≤n)

        write2-in-stack : InStack write2
        write2-in-stack = capacity-maintained cap 2 output-slots≤pair-setup

        write3-in-stack : InStack write3
        write3-in-stack = capacity-maintained cap 3 apply-cap-fits-pair-setup

        -- Chain memory preservation at heap addresses using abstract lemma
        memH-s7-s3 : readMem (memory s7) addr ≡ readMem (memory s3) addr
        memH-s7-s3 = refl

        memH-s3-s2 : readMem (memory s3) addr ≡ readMem (memory s2) addr
        memH-s3-s2 = trans (cong (λ a → readMem (writeMem (memory s2) a (readReg (regs s2) rbp)) addr) write-addr-s3)
                          (stackAddr-write-preserves-heap (memory s2) write3 (readReg (regs s2) rbp) addr write3-in-stack addr-in-heap)

        memH-s2-s1 : readMem (memory s2) addr ≡ readMem (memory s1) addr
        memH-s2-s1 = trans (cong (λ a → readMem (writeMem (memory s1) a (readReg (regs s1) r15)) addr) write-addr-s2)
                          (stackAddr-write-preserves-heap (memory s1) write2 (readReg (regs s1) r15) addr write2-in-stack addr-in-heap)

        memH-s1-s : readMem (memory s1) addr ≡ readMem (memory s) addr
        memH-s1-s = stackAddr-write-preserves-heap (memory s) write1 orig-r14 addr write1-in-stack addr-in-heap

------------------------------------------------------------------------
-- PairMiddleStarResult: Star-based result for pair middle phase
------------------------------------------------------------------------

-- | Result of executing 2 pair middle instructions with Star semantics
-- Instructions: mov [r15], rax; mov rdi, r14
-- Stores f's result at [r15] and restores original input to rdi.
record PairMiddleStarResult (prog : Program) (s : State) (pc-after : ℕ) : Set where
  field
    -- Output state
    s-mid : State

    -- Star execution proof (not fuel-based)
    star-mid : Star prog s s-mid

    -- Non-halting
    h-mid : halted s-mid ≡ false

    -- PC advancement
    pc-mid : pc s-mid ≡ pc-after

    -- rdi gets r14's value (input restored)
    rdi-mid : readReg (regs s-mid) rdi ≡ readReg (regs s) r14

    -- Memory at [r15] contains rax (f's result stored)
    mem-at-r15 : readMem (memory s-mid) (readReg (regs s-mid) r15) ≡ just (readReg (regs s) rax)

    -- r15 preserved
    r15-mid : readReg (regs s-mid) r15 ≡ readReg (regs s) r15

    -- rsp preserved
    rsp-mid : readReg (regs s-mid) rsp ≡ readReg (regs s) rsp

    -- Memory preservation: addresses ≠ r15 are unchanged
    mem-other : ∀ addr → addr ≢ readReg (regs s) r15 → readMem (memory s-mid) addr ≡ readMem (memory s) addr

-- | Execute pair middle instructions (mov [r15], rax; mov rdi, r14) at arbitrary offset
-- Returns PairMiddleStarResult with Star-based execution proof.
pair-middle-star-at : ∀ (prefix : Program) (rest : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  let prog = prefix ++ mov (mem (base r15)) (reg rax) ∷ mov (reg rdi) (reg r14) ∷ rest
  in PairMiddleStarResult prog s (length prefix +ℕ 2)
pair-middle-star-at prefix rest s h-false pc-eq = record
  { s-mid = s-final
  ; star-mid = star-eq
  ; h-mid = h-final
  ; pc-mid = pc-final
  ; rdi-mid = rdi-eq
  ; mem-at-r15 = mem-eq
  ; r15-mid = r15-eq
  ; rsp-mid = rsp-eq
  ; mem-other = mem-above-eq
  }
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

    star-eq : Star prog s s-final
    star-eq = star-step2 h-false step1 h1 step2

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

