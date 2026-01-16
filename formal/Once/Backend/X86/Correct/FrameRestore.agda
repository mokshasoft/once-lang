------------------------------------------------------------------------
-- Once.Backend.X86.Correct.FrameRestore
--
-- Reusable proofs for frame restoration sequences.
-- Used by Case, Pair, Curry, and other IR constructs that use stack frames.
--
-- Frame cleanup sequence: mov rsp, rbp ; pop rbp
-- This restores rsp to the value of rbp, then pops the saved rbp.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.FrameRestore where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.ExecLemmas
  using (fetch-at-prefix-end)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single)

open import Data.Nat using (_>_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (subst₂; cong₂)

------------------------------------------------------------------------
-- Frame Cleanup Instructions
--
-- These are the standard cleanup instructions for restoring a stack frame.
-- Defined here so all IR proofs use the same definitions.
------------------------------------------------------------------------

-- | Instruction: mov rsp, rbp (restore stack pointer from frame pointer)
restore-rsp-instr : Instr
restore-rsp-instr = mov (reg rsp) (reg rbp)

-- | Instruction: pop rbp (restore frame pointer from stack)
pop-rbp-instr : Instr
pop-rbp-instr = pop rbp

-- | Number of cleanup instructions
frame-cleanup-count : ℕ
frame-cleanup-count = 2

-- | The cleanup instruction sequence as a list
frame-cleanup-instrs : List Instr
frame-cleanup-instrs = restore-rsp-instr ∷ pop-rbp-instr ∷ []

------------------------------------------------------------------------
-- Frame Setup Instructions (for completeness)
------------------------------------------------------------------------

-- | Instruction: push rbp (save frame pointer)
push-rbp-instr : Instr
push-rbp-instr = push (reg rbp)

-- | Instruction: mov rbp, rsp (establish frame pointer)
establish-rbp-instr : Instr
establish-rbp-instr = mov (reg rbp) (reg rsp)

-- | Number of setup instructions
frame-setup-count : ℕ
frame-setup-count = 2

-- | The setup instruction sequence as a list
frame-setup-instrs : List Instr
frame-setup-instrs = push-rbp-instr ∷ establish-rbp-instr ∷ []

------------------------------------------------------------------------
-- Frame Restore Result Record
--
-- This captures the result of executing the cleanup sequence.
-- The key insight: after cleanup, rsp and rbp are restored to their
-- original values (from before the frame was established).
------------------------------------------------------------------------

record FrameRestoreResult (prog : Program)
                          (s-before : State)       -- State before cleanup
                          (saved-rbp : Word)       -- Value that was pushed for rbp
                          (original-rsp : Word)    -- RSP value before frame setup
                          : Set where
  field
    -- Final state after cleanup
    s-final : State

    -- Execution proof
    star : Star prog s-before s-final

    -- Halted status preserved
    h-final : halted s-final ≡ false

    -- PC advanced by cleanup count
    pc-final : pc s-final ≡ pc s-before +ℕ frame-cleanup-count

    -- RSP restored: after mov rsp,rbp and pop rbp, rsp = original + 8 (popped one slot)
    -- Actually: after mov rsp,rbp: rsp = rbp; after pop rbp: rsp = rbp + 8
    -- If rbp was set to (original-rsp - 8) after push, then final rsp = original-rsp
    rsp-final : readReg (regs s-final) rsp ≡ original-rsp

    -- RBP restored to saved value
    rbp-final : readReg (regs s-final) rbp ≡ saved-rbp

    -- Other registers preserved
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s-before) rax
    rdi-preserved : readReg (regs s-final) rdi ≡ readReg (regs s-before) rdi
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s-before) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s-before) r15

    -- Memory preserved
    mem-preserved : memory s-final ≡ memory s-before

------------------------------------------------------------------------
-- Frame Restore Execution Proof
--
-- Proves that executing the cleanup sequence achieves the expected result.
------------------------------------------------------------------------

-- | Execute frame cleanup: mov rsp, rbp ; pop rbp
--
-- Preconditions:
--   1. halted s = false
--   2. PC points to restore-rsp-instr in prog
--   3. Memory at (rbp s) contains saved-rbp value
--   4. rbp s = original-rsp - 8 (rbp was set after push)
--
-- Postconditions:
--   1. rsp restored to original-rsp
--   2. rbp restored to saved-rbp
--   3. PC advanced by 2
--   4. Other registers preserved
frame-restore-exec : ∀ (prog : Program)
                       (prefix : Program)
                       (suffix : Program)
                       (s : State)
                       (saved-rbp : Word)
                       (original-rsp : Word)
  → halted s ≡ false
  → prog ≡ prefix ++ restore-rsp-instr ∷ pop-rbp-instr ∷ suffix
  → pc s ≡ length prefix
  → readMem (memory s) (readReg (regs s) rbp) ≡ just saved-rbp
  → readReg (regs s) rbp +ℕ slot-size ≡ original-rsp
  → FrameRestoreResult prog s saved-rbp original-rsp
frame-restore-exec prog prefix suffix s saved-rbp original-rsp h-false prog-eq pc-eq mem-rbp rbp-eq = record
    { s-final = s2
    ; star = star-eq
    ; h-final = h2
    ; pc-final = pc2
    ; rsp-final = rsp2
    ; rbp-final = rbp2
    ; rax-preserved = rax2
    ; rdi-preserved = rdi2
    ; r14-preserved = r142
    ; r15-preserved = r152
    ; mem-preserved = mem2
    }
  where
    -- State after mov rsp, rbp
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp (readReg (regs s) rbp)
                  ; pc = pc s +ℕ 1 }

    -- State after pop rbp
    -- pop rbp: rbp := mem[rsp], rsp := rsp + 8
    -- At s1, rsp = rbp(s), so we read from rbp(s)
    s2 : State
    s2 = record s1 { regs = writeReg (writeReg (regs s1) rbp saved-rbp) rsp (readReg (regs s1) rsp +ℕ slot-size)
                   ; pc = pc s1 +ℕ 1 }

    -- Halted proofs
    h1 : halted s1 ≡ false
    h1 = h-false

    h2 : halted s2 ≡ false
    h2 = h1

    -- PC proofs
    pc1 : pc s1 ≡ pc s +ℕ 1
    pc1 = refl

    pc2 : pc s2 ≡ pc s +ℕ frame-cleanup-count
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (pc s) 1 1)

    -- Program structure for fetching
    prog-eq-1 : prog ≡ prefix ++ restore-rsp-instr ∷ pop-rbp-instr ∷ suffix
    prog-eq-1 = prog-eq

    -- Fetch proofs
    fetch1 : fetch prog (pc s) ≡ just restore-rsp-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just restore-rsp-instr)
                    (sym prog-eq-1)
                    (sym pc-eq)
                    (fetch-at-prefix-end prefix restore-rsp-instr (pop-rbp-instr ∷ suffix))

    prog-eq-2 : prog ≡ (prefix ++ restore-rsp-instr ∷ []) ++ pop-rbp-instr ∷ suffix
    prog-eq-2 = trans prog-eq-1 (sym (++-assoc prefix (restore-rsp-instr ∷ []) (pop-rbp-instr ∷ suffix)))

    -- pc s1 = pc s + 1 = length prefix + 1 = length (prefix ++ [restore-rsp-instr])
    pc-s1-eq : pc s1 ≡ length (prefix ++ restore-rsp-instr ∷ [])
    pc-s1-eq = trans (cong (_+ℕ 1) pc-eq) (sym (List-length-++ prefix))

    fetch2 : fetch prog (pc s1) ≡ just pop-rbp-instr
    fetch2 = subst₂ (λ p n → fetch p n ≡ just pop-rbp-instr)
                    (sym prog-eq-2)
                    (sym pc-s1-eq)
                    (fetch-at-prefix-end (prefix ++ restore-rsp-instr ∷ []) pop-rbp-instr suffix)

    -- Step proofs
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s restore-rsp-instr h-false fetch1)
                  (execMov-reg-reg s rsp rbp)

    -- For step2, need to show memory read succeeds
    -- At s1: rsp = rbp(s), memory unchanged
    mem-s1 : memory s1 ≡ memory s
    mem-s1 = refl

    rsp-s1 : readReg (regs s1) rsp ≡ readReg (regs s) rbp
    rsp-s1 = readReg-writeReg-same (regs s) rsp (readReg (regs s) rbp)

    mem-at-rsp-s1 : readMem (memory s1) (readReg (regs s1) rsp) ≡ just saved-rbp
    mem-at-rsp-s1 = trans (cong (λ addr → readMem (memory s1) addr) rsp-s1)
                          (trans (cong (λ m → readMem m (readReg (regs s) rbp)) mem-s1)
                                 mem-rbp)

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 pop-rbp-instr h1 fetch2)
                  (execPop prog s1 rbp saved-rbp mem-at-rsp-s1)

    -- Star proof
    star-eq : Star prog s s2
    star-eq = step* h-false step1 (step* h1 step2 refl*)

    -- Register proofs for final state s2
    -- s2.regs = writeReg (writeReg s1.regs rbp saved-rbp) rsp (rsp-s1 + 8)
    -- s1.regs = writeReg s.regs rsp (rbp s)

    -- RSP final = rbp(s) + 8 = original-rsp
    rsp2 : readReg (regs s2) rsp ≡ original-rsp
    rsp2 = trans (readReg-writeReg-same (writeReg (regs s1) rbp saved-rbp) rsp _)
                 (trans (cong (_+ℕ slot-size) rsp-s1) rbp-eq)

    -- Value written to rsp in s2 (for explicit arguments)
    rsp-val-s2 : Word
    rsp-val-s2 = readReg (regs s1) rsp +ℕ slot-size

    -- Value written to rsp in s1 (rbp value from s)
    rsp-val-s1 : Word
    rsp-val-s1 = readReg (regs s) rbp

    -- RBP final = saved-rbp
    -- s2.regs = writeReg (writeReg s1.regs rbp saved-rbp) rsp ...
    -- Reading rbp: first skip rsp write, then get from rbp write
    rbp2 : readReg (regs s2) rbp ≡ saved-rbp
    rbp2 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s1) rbp saved-rbp) rsp-val-s2)
                 (readReg-writeReg-same (regs s1) rbp saved-rbp)

    -- RAX preserved through both instructions
    -- s1.regs = writeReg s.regs rsp ..., s2.regs = writeReg (writeReg s1.regs rbp ...) rsp ...
    rax2 : readReg (regs s2) rax ≡ readReg (regs s) rax
    rax2 = trans (readReg-writeReg-rsp-rax (writeReg (regs s1) rbp saved-rbp) rsp-val-s2)
                 (trans (readReg-writeReg-rbp-rax (regs s1) saved-rbp)
                        (readReg-writeReg-rsp-rax (regs s) rsp-val-s1))

    -- RDI preserved
    rdi2 : readReg (regs s2) rdi ≡ readReg (regs s) rdi
    rdi2 = trans (readReg-writeReg-rsp-rdi (writeReg (regs s1) rbp saved-rbp) rsp-val-s2)
                 (trans (readReg-writeReg-rbp-rdi (regs s1) saved-rbp)
                        (readReg-writeReg-rsp-rdi (regs s) rsp-val-s1))

    -- R14 preserved
    r142 : readReg (regs s2) r14 ≡ readReg (regs s) r14
    r142 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s1) rbp saved-rbp) rsp-val-s2)
                 (trans (readReg-writeReg-rbp-r14 (regs s1) saved-rbp)
                        (readReg-writeReg-rsp-r14 (regs s) rsp-val-s1))

    -- R15 preserved
    r152 : readReg (regs s2) r15 ≡ readReg (regs s) r15
    r152 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s1) rbp saved-rbp) rsp-val-s2)
                 (trans (readReg-writeReg-rbp-r15 (regs s1) saved-rbp)
                        (readReg-writeReg-rsp-r15 (regs s) rsp-val-s1))

    -- Memory preserved (no stores in cleanup)
    mem2 : memory s2 ≡ memory s
    mem2 = refl

------------------------------------------------------------------------
-- Jump-to-Cleanup Result Record
--
-- For constructs that jump to cleanup (like Case after branch execution).
------------------------------------------------------------------------

record JumpToCleanupResult (prog : Program)
                           (s-before : State)      -- State before jmp
                           (saved-rbp : Word)
                           (original-rsp : Word)
                           : Set where
  field
    -- Final state after jmp + cleanup
    s-final : State

    -- Execution proof
    star : Star prog s-before s-final

    -- Halted status preserved
    h-final : halted s-final ≡ false

    -- PC at end of construct (cleanup-pos + 2)
    pc-final : ℕ
    pc-final-eq : pc s-final ≡ pc-final

    -- RSP and RBP restored
    rsp-final : readReg (regs s-final) rsp ≡ original-rsp
    rbp-final : readReg (regs s-final) rbp ≡ saved-rbp

    -- Other registers preserved
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s-before) rax
    rdi-preserved : readReg (regs s-final) rdi ≡ readReg (regs s-before) rdi
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s-before) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s-before) r15

    -- Memory preserved
    mem-preserved : memory s-final ≡ memory s-before

-- | Execute jump to cleanup: jmp offset ; (at target:) mov rsp, rbp ; pop rbp
--
-- This is the common pattern for Case after executing the left branch:
-- execute jmp, then execute cleanup.
jump-to-cleanup-exec : ∀ (prog : Program)
                         (prefix-jmp : Program)      -- Prefix up to jmp
                         (skipped : Program)         -- Code skipped by jmp (e.g., right branch)
                         (suffix : Program)          -- Code after cleanup
                         (s : State)
                         (jmp-offset : ℕ)
                         (saved-rbp : Word)
                         (original-rsp : Word)
  → halted s ≡ false
  → prog ≡ prefix-jmp ++ jmp jmp-offset ∷ skipped ++ restore-rsp-instr ∷ pop-rbp-instr ∷ suffix
  → pc s ≡ length prefix-jmp
  → jmp-offset ≡ length skipped   -- jmp at pos P, target at pos P+1+offset, so offset = length skipped
  → readMem (memory s) (readReg (regs s) rbp) ≡ just saved-rbp
  → readReg (regs s) rbp +ℕ slot-size ≡ original-rsp
  → JumpToCleanupResult prog s saved-rbp original-rsp
jump-to-cleanup-exec prog prefix-jmp skipped suffix s jmp-offset saved-rbp original-rsp
                     h-false prog-eq pc-eq offset-eq mem-rbp rbp-eq = record
    { s-final = FrameRestoreResult.s-final cleanup-result
    ; star = star-trans jmp-star (FrameRestoreResult.star cleanup-result)
    ; h-final = FrameRestoreResult.h-final cleanup-result
    ; pc-final = length prefix-jmp +ℕ 1 +ℕ jmp-offset +ℕ frame-cleanup-count
    ; pc-final-eq = pc-final-proof
    ; rsp-final = FrameRestoreResult.rsp-final cleanup-result
    ; rbp-final = FrameRestoreResult.rbp-final cleanup-result
    ; rax-preserved = trans (FrameRestoreResult.rax-preserved cleanup-result) refl
    ; rdi-preserved = trans (FrameRestoreResult.rdi-preserved cleanup-result) refl
    ; r14-preserved = trans (FrameRestoreResult.r14-preserved cleanup-result) refl
    ; r15-preserved = trans (FrameRestoreResult.r15-preserved cleanup-result) refl
    ; mem-preserved = trans (FrameRestoreResult.mem-preserved cleanup-result) refl
    }
  where
    -- State after jmp
    s-jmp : State
    s-jmp = record s { pc = pc s +ℕ 1 +ℕ jmp-offset }

    h-jmp : halted s-jmp ≡ false
    h-jmp = h-false

    -- Fetch jmp instruction
    fetch-jmp : fetch prog (pc s) ≡ just (jmp jmp-offset)
    fetch-jmp = subst₂ (λ p n → fetch p n ≡ just (jmp jmp-offset))
                       (sym prog-eq)
                       (sym pc-eq)
                       (fetch-at-prefix-end prefix-jmp (jmp jmp-offset) _)

    -- Step for jmp
    step-jmp : step prog s ≡ just s-jmp
    step-jmp = trans (step-exec prog s (jmp jmp-offset) h-false fetch-jmp)
                     (execJmp prog s jmp-offset)

    jmp-star : Star prog s s-jmp
    jmp-star = star-single h-false step-jmp

    -- PC after jmp points to cleanup
    pc-jmp : pc s-jmp ≡ length prefix-jmp +ℕ 1 +ℕ jmp-offset
    pc-jmp = cong (λ n → n +ℕ 1 +ℕ jmp-offset) pc-eq

    -- Cleanup prefix is prefix-jmp ++ jmp ∷ skipped
    cleanup-prefix : Program
    cleanup-prefix = prefix-jmp ++ jmp jmp-offset ∷ skipped

    -- length (prefix-jmp ++ jmp ∷ skipped) = length prefix-jmp + (1 + length skipped)
    --                                     = length prefix-jmp + 1 + length skipped
    len-cleanup-prefix : length cleanup-prefix ≡ length prefix-jmp +ℕ 1 +ℕ length skipped
    len-cleanup-prefix = trans (List-length-++ prefix-jmp)
                               (sym (+-assoc (length prefix-jmp) 1 (length skipped)))

    -- PC at cleanup start
    -- pc s-jmp = length prefix-jmp + 1 + jmp-offset
    --          = length prefix-jmp + 1 + length skipped  (by offset-eq)
    --          = length cleanup-prefix                    (by len-cleanup-prefix)
    pc-at-cleanup : pc s-jmp ≡ length cleanup-prefix
    pc-at-cleanup = trans pc-jmp
                          (trans (cong (λ n → length prefix-jmp +ℕ 1 +ℕ n) offset-eq)
                                 (sym len-cleanup-prefix))

    -- Program structure for cleanup
    prog-eq-cleanup : prog ≡ cleanup-prefix ++ restore-rsp-instr ∷ pop-rbp-instr ∷ suffix
    prog-eq-cleanup = trans prog-eq
                            (trans (cong (prefix-jmp ++_)
                                        (sym (++-assoc (jmp jmp-offset ∷ []) skipped _)))
                                   (sym (++-assoc prefix-jmp _ _)))

    -- Memory and rbp unchanged by jmp
    mem-jmp : memory s-jmp ≡ memory s
    mem-jmp = refl

    rbp-jmp : readReg (regs s-jmp) rbp ≡ readReg (regs s) rbp
    rbp-jmp = refl

    mem-rbp-jmp : readMem (memory s-jmp) (readReg (regs s-jmp) rbp) ≡ just saved-rbp
    mem-rbp-jmp = trans (cong₂ readMem mem-jmp rbp-jmp) mem-rbp

    rbp-eq-jmp : readReg (regs s-jmp) rbp +ℕ slot-size ≡ original-rsp
    rbp-eq-jmp = trans (cong (_+ℕ slot-size) rbp-jmp) rbp-eq

    -- Execute cleanup
    cleanup-result : FrameRestoreResult prog s-jmp saved-rbp original-rsp
    cleanup-result = frame-restore-exec prog cleanup-prefix suffix s-jmp saved-rbp original-rsp
                                        h-jmp prog-eq-cleanup pc-at-cleanup mem-rbp-jmp rbp-eq-jmp

    -- Final PC proof
    -- pc s-final = pc s-jmp + frame-cleanup-count
    --            = (length prefix-jmp + 1 + jmp-offset) + frame-cleanup-count
    pc-final-proof : pc (FrameRestoreResult.s-final cleanup-result) ≡
                     length prefix-jmp +ℕ 1 +ℕ jmp-offset +ℕ frame-cleanup-count
    pc-final-proof = trans (FrameRestoreResult.pc-final cleanup-result)
                           (cong (_+ℕ frame-cleanup-count) pc-jmp)
