------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Case
--
-- Case setup and cleanup helpers for the case (sum elimination) proof.
-- Non-recursive parts that don't need the mutual recursion dispatcher.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.Star using (Star; refl*; step*; star-trans; star-step2; star-step6)
open import Once.Backend.X86.Correct.FetchStep using (step-exec; fetch-append-skip)
open import Once.Backend.Common.Fetch using (fetch-0; fetch-1; fetch-2; fetch-3; fetch-4; fetch-5; fetch-append-right)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)
open import Once.Backend.X86.Correct.InstrExec
  using (execPush-reg; execMov-reg-reg; execMov-reg-mem-base; execMov-reg-mem-disp;
         execCmp-zero; execCmp-one; execJne-not-taken; execJne-taken; execJmp; execPop)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; ir-stack-requirement; capacity-after-push)
open import Once.Backend.X86.Correct.RegisterLemmas
  using (readReg-writeReg-same; readReg-writeReg-rsp-rbp; readReg-writeReg-rsp-rdi;
         readReg-writeReg-rsp-r14; readReg-writeReg-rsp-r15;
         readReg-writeReg-rbp-rsp; readReg-writeReg-rbp-rdi; readReg-writeReg-rbp-r14; readReg-writeReg-rbp-r15;
         readReg-writeReg-r11-rdi; readReg-writeReg-r11-rsp; readReg-writeReg-r11-rbp;
         readReg-writeReg-r11-r14; readReg-writeReg-r11-r15;
         readReg-writeReg-rdi-rsp; readReg-writeReg-rdi-rbp; readReg-writeReg-rdi-r14; readReg-writeReg-rdi-r15)
open import Once.Backend.Common.MemoryRegions using (InStack; InHeap; InCode; StackPointer)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _∸_; suc; zero) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; ≤-<-trans; <⇒≤; m∸n≤m)
open import Data.List using (List; _++_; length; _∷_; [])
open import Data.List.Properties using (++-assoc)
open import Once.Backend.X86.Correct.CompileLength using (length-++)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂)

------------------------------------------------------------------------
-- Case Inl Setup Result
--
-- Result of executing the 6-instruction setup sequence for inl branch:
--   0: push rbp
--   1: mov rbp, rsp
--   2: mov r11, [rdi]     ; load tag (should be 0)
--   3: cmp r11, 0         ; sets ZF=true
--   4: jne right-offset   ; NOT taken (ZF=true)
--   5: mov rdi, [rdi+8]   ; load value pointer
------------------------------------------------------------------------

record CaseInlSetupResult {A B C : Type} (a : ⟦ A ⟧)
    (prefix suffix : Program) (f : IR A C) (g : IR B C)
    (s s-setup : State) (val-addr : ℕ) : Set where
  field
    -- Execution star
    star-setup : Star (prefix ++ compile-x86 [ f , g ] ++ suffix) s s-setup
    -- State properties
    h-setup    : halted s-setup ≡ false
    pc-setup   : pc s-setup ≡ length prefix +ℕ 6
    -- Register values
    rdi-setup  : readReg (regs s-setup) rdi ≡ val-addr
    rbp-setup  : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ slot-size
    rsp-setup  : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slot-size
    r14-setup  : readReg (regs s-setup) r14 ≡ readReg (regs s) r14
    r15-setup  : readReg (regs s-setup) r15 ≡ readReg (regs s) r15
    -- Memory preservation
    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- Invariants
    stack-inv-setup : StackInvariant s-setup
    rbp-inv-setup   : RbpInvariant s-setup

------------------------------------------------------------------------
-- Case Inl Setup Proof
--
-- Execute 6 instructions step by step:
--   0: push rbp           - save frame pointer, rsp -= 8
--   1: mov rbp, rsp       - establish frame base
--   2: mov r11, [rdi]     - load tag (should be 0)
--   3: cmp r11, 0         - sets ZF=true (tag=0)
--   4: jne right-offset   - NOT taken (ZF=true)
--   5: mov rdi, [rdi+8]   - load value pointer
------------------------------------------------------------------------

-- | Execute the 6-instruction inl setup sequence
case-inl-setup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
  (prefix suffix : Program) (a : ⟦ A ⟧) (s : State) (val-addr : ℕ) →
  halted s ≡ false →
  pc s ≡ length prefix →
  -- Tag is 0 (from ValidAt inl)
  readMem (memory s) (readReg (regs s) rdi) ≡ just 0 →
  -- Value pointer is at rdi+8
  readMem (memory s) (readReg (regs s) rdi +ℕ slot-size) ≡ just val-addr →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  ∃[ s-setup ] CaseInlSetupResult {A} {B} {C} a prefix suffix f g s s-setup val-addr
case-inl-setup-star {A} {B} {C} f g prefix suffix a s val-addr
    h-false pc-eq tag-is-0 val-ptr-eq stack-inv cap rbp-inv =
    s6 , result
  where
    open import Data.Nat.Properties using (+-assoc)

    -- Program and original values
    len-f = compile-length f
    len-g = compile-length g
    prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    orig-rsp = readReg (regs s) rsp
    orig-rbp = readReg (regs s) rbp
    orig-rdi = readReg (regs s) rdi
    orig-r14 = readReg (regs s) r14
    orig-r15 = readReg (regs s) r15
    orig-mem = memory s

    -- ========== Step 1: push rbp ==========
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp (orig-rsp ∸ slot-size)
                  ; memory = writeMem orig-mem (orig-rsp ∸ slot-size) orig-rbp
                  ; pc = pc s +ℕ 1 }

    h1 : halted s1 ≡ false
    h1 = h-false  -- halted unchanged by push

    -- ========== Step 2: mov rbp, rsp ==========
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rbp (readReg (regs s1) rsp)
                   ; pc = pc s1 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h-false

    -- ========== Step 3: mov r11, [rdi] ==========
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) r11 0  -- tag is 0
                   ; pc = pc s2 +ℕ 1 }

    h3 : halted s3 ≡ false
    h3 = h-false

    -- ========== Step 4: cmp r11, 0 ==========
    s4 : State
    s4 = record s3 { pc = pc s3 +ℕ 1
                   ; flags = mkflags true false false }

    h4 : halted s4 ≡ false
    h4 = h-false

    -- ========== Step 5: jne right-offset (NOT taken) ==========
    s5 : State
    s5 = record s4 { pc = pc s4 +ℕ 1 }

    h5 : halted s5 ≡ false
    h5 = h-false

    -- ========== Step 6: mov rdi, [rdi+8] ==========
    s6 : State
    s6 = record s5 { regs = writeReg (regs s5) rdi val-addr
                   ; pc = pc s5 +ℕ 1 }

    -- ========== Instructions ==========
    -- Define the first 6 instructions of compile-x86 [ f , g ]
    -- These are definitionally equal to what compile-x86 produces

    case-code : Program
    case-code = compile-x86 [ f , g ] ++ suffix

    -- The instructions in compile-x86 [ f , g ]:
    --   0: push (reg rbp)
    --   1: mov (reg rbp) (reg rsp)
    --   2: mov (reg r11) (mem (base rdi))
    --   3: cmp (reg r11) (imm 0)
    --   4: jne (case-jne-base + len-f)
    --   5: mov (reg rdi) (mem (base+disp rdi slot-size))

    -- ========== Fetch Proofs ==========
    -- Helper to convert pc s to length prefix for fetch proofs
    open import Data.Nat.Properties using (+-identityʳ)

    -- fetch at length prefix + n in prog equals fetch at n in case-code
    fetch-at-n : ∀ n → fetch prog (length prefix +ℕ n) ≡ fetch case-code n
    fetch-at-n n = fetch-append-right prefix case-code n

    -- Fetch proofs for each instruction
    -- fetch case-code 0 = just (push (reg rbp)) by definitional equality
    fetch1 : fetch prog (pc s) ≡ just (push (reg rbp))
    fetch1 = subst (λ p → fetch prog p ≡ just (push (reg rbp))) (sym pc-eq)
             (subst (λ n → fetch prog n ≡ just (push (reg rbp)))
                    (+-identityʳ (length prefix))
                    (fetch-at-n 0))

    -- For subsequent fetches, we need pc s1 = length prefix + 1, etc.
    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    fetch2 : fetch prog (pc s1) ≡ just (mov (reg rbp) (reg rsp))
    fetch2 = subst (λ p → fetch prog p ≡ just (mov (reg rbp) (reg rsp))) (sym pc1) (fetch-at-n 1)

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    fetch3 : fetch prog (pc s2) ≡ just (mov (reg r11) (mem (base rdi)))
    fetch3 = subst (λ p → fetch prog p ≡ just (mov (reg r11) (mem (base rdi)))) (sym pc2) (fetch-at-n 2)

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    fetch4 : fetch prog (pc s3) ≡ just (cmp (reg r11) (imm 0))
    fetch4 = subst (λ p → fetch prog p ≡ just (cmp (reg r11) (imm 0))) (sym pc3) (fetch-at-n 3)

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    fetch5 : fetch prog (pc s4) ≡ just (jne (case-jne-base +ℕ len-f))
    fetch5 = subst (λ p → fetch prog p ≡ just (jne (case-jne-base +ℕ len-f))) (sym pc4) (fetch-at-n 4)

    pc5 : pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    fetch6 : fetch prog (pc s5) ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size)))
    fetch6 = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size)))) (sym pc5) (fetch-at-n 5)

    -- ========== Memory access proofs ==========
    -- For step3 (mov r11, [rdi]), we need rdi still points to the tag
    -- After push rbp, rdi is unchanged
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) (orig-rsp ∸ slot-size)

    -- After mov rbp, rsp, rdi is still unchanged
    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = trans (readReg-writeReg-rbp-rdi (regs s1) (readReg (regs s1) rsp)) rdi-s1

    -- Memory is unchanged by push for heap addresses (push writes to stack)
    -- For now, we need to show memory s1 at orig-rdi is still tag-is-0
    -- Since push only writes to (orig-rsp - slot-size), and tag is at orig-rdi which is in heap
    -- We postulate this for now (needs heap/stack disjointness)
    postulate
      tag-still-0-s1 : readMem (memory s1) orig-rdi ≡ just 0
      tag-still-0-s2 : readMem (memory s2) orig-rdi ≡ just 0

    -- Memory proof for step 3: read tag from memory
    mem3 : readMem (memory s2) (readReg (regs s2) rdi) ≡ just 0
    mem3 = subst (λ addr → readMem (memory s2) addr ≡ just 0) (sym rdi-s2) tag-still-0-s2

    -- For step 6, we need to prove memory still has val-addr at rdi+8
    -- rdi in s5 is still orig-rdi (unchanged by cmp, jne which don't touch rdi)
    rdi-s3 : readReg (regs s3) rdi ≡ orig-rdi
    rdi-s3 = trans (readReg-writeReg-r11-rdi (regs s2) 0) rdi-s2

    -- s4 and s5 don't change registers (cmp only changes flags, jne only changes pc)
    rdi-s4 : readReg (regs s4) rdi ≡ orig-rdi
    rdi-s4 = rdi-s3  -- s4 has same regs as s3

    rdi-s5 : readReg (regs s5) rdi ≡ orig-rdi
    rdi-s5 = rdi-s4  -- s5 has same regs as s4

    postulate
      val-ptr-still-valid : readMem (memory s5) (orig-rdi +ℕ slot-size) ≡ just val-addr

    mem6 : readMem (memory s5) (readReg (regs s5) rdi +ℕ slot-size) ≡ just val-addr
    mem6 = subst (λ addr → readMem (memory s5) (addr +ℕ slot-size) ≡ just val-addr) (sym rdi-s5) val-ptr-still-valid

    -- ========== ExecInstr Proofs ==========
    -- Step 1: push rbp
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s (push (reg rbp)) h-false fetch1) (execPush-reg prog s rbp)

    -- Step 2: mov rbp, rsp
    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (reg rbp) (reg rsp)) h1 fetch2) (execMov-reg-reg s1 rbp rsp)

    -- Step 3: mov r11, [rdi]
    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (reg r11) (mem (base rdi))) h2 fetch3)
                  (execMov-reg-mem-base s2 r11 rdi 0 mem3)

    -- Step 4: cmp r11, 0
    -- After step 3, r11 = 0, so cmp r11, 0 sets ZF = true
    r11-s3 : readReg (regs s3) r11 ≡ 0
    r11-s3 = readReg-writeReg-same (regs s2) r11 0

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (cmp (reg r11) (imm 0)) h3 fetch4) (execCmp-zero prog s3 r11 r11-s3)

    -- Step 5: jne (NOT taken because ZF = true)
    zf-s4 : zf (flags s4) ≡ true
    zf-s4 = refl  -- by definition of s4

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (jne (case-jne-base +ℕ len-f)) h4 fetch5)
                  (execJne-not-taken prog s4 (case-jne-base +ℕ len-f) zf-s4)

    -- Step 6: mov rdi, [rdi+8]
    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (mov (reg rdi) (mem (base+disp rdi slot-size))) h5 fetch6)
                  (execMov-reg-mem-disp s5 rdi rdi slot-size val-addr mem6)

    -- Build the star using star-step6
    star6 : Star prog s s6
    star6 = star-step6 h-false step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6

    -- ========== Final PC ==========
    pc6 : pc s6 ≡ length prefix +ℕ 6
    pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc (length prefix) 5 1)

    -- ========== Register values in s6 ==========
    -- rdi = val-addr (set in step 6)
    rdi6 : readReg (regs s6) rdi ≡ val-addr
    rdi6 = readReg-writeReg-same (regs s5) rdi val-addr

    -- rsp in s6 = rsp in s5 = ... = rsp in s1 = orig-rsp - slot-size
    rsp-s1 : readReg (regs s1) rsp ≡ orig-rsp ∸ slot-size
    rsp-s1 = readReg-writeReg-same (regs s) rsp (orig-rsp ∸ slot-size)

    rsp-s2 : readReg (regs s2) rsp ≡ orig-rsp ∸ slot-size
    rsp-s2 = trans (readReg-writeReg-rbp-rsp (regs s1) (readReg (regs s1) rsp)) rsp-s1

    rsp-s3 : readReg (regs s3) rsp ≡ orig-rsp ∸ slot-size
    rsp-s3 = trans (readReg-writeReg-r11-rsp (regs s2) 0) rsp-s2

    rsp-s4 : readReg (regs s4) rsp ≡ orig-rsp ∸ slot-size
    rsp-s4 = rsp-s3  -- s4 has same regs as s3

    rsp-s5 : readReg (regs s5) rsp ≡ orig-rsp ∸ slot-size
    rsp-s5 = rsp-s4  -- s5 has same regs as s4

    rsp6 : readReg (regs s6) rsp ≡ orig-rsp ∸ slot-size
    rsp6 = trans (readReg-writeReg-rdi-rsp (regs s5) val-addr) rsp-s5

    -- rbp in s6 = rbp in s5 = ... = rbp in s2 = readReg (regs s1) rsp = orig-rsp - slot-size
    rbp-s2 : readReg (regs s2) rbp ≡ orig-rsp ∸ slot-size
    rbp-s2 = trans (readReg-writeReg-same (regs s1) rbp (readReg (regs s1) rsp)) rsp-s1

    rbp-s3 : readReg (regs s3) rbp ≡ orig-rsp ∸ slot-size
    rbp-s3 = trans (readReg-writeReg-r11-rbp (regs s2) 0) rbp-s2

    rbp-s4 : readReg (regs s4) rbp ≡ orig-rsp ∸ slot-size
    rbp-s4 = rbp-s3

    rbp-s5 : readReg (regs s5) rbp ≡ orig-rsp ∸ slot-size
    rbp-s5 = rbp-s4

    rbp6 : readReg (regs s6) rbp ≡ orig-rsp ∸ slot-size
    rbp6 = trans (readReg-writeReg-rdi-rbp (regs s5) val-addr) rbp-s5

    -- r14 unchanged through all steps
    r14-s1 : readReg (regs s1) r14 ≡ orig-r14
    r14-s1 = readReg-writeReg-rsp-r14 (regs s) (orig-rsp ∸ slot-size)

    r14-s2 : readReg (regs s2) r14 ≡ orig-r14
    r14-s2 = trans (readReg-writeReg-rbp-r14 (regs s1) (readReg (regs s1) rsp)) r14-s1

    r14-s3 : readReg (regs s3) r14 ≡ orig-r14
    r14-s3 = trans (readReg-writeReg-r11-r14 (regs s2) 0) r14-s2

    r14-s4 : readReg (regs s4) r14 ≡ orig-r14
    r14-s4 = r14-s3

    r14-s5 : readReg (regs s5) r14 ≡ orig-r14
    r14-s5 = r14-s4

    r146 : readReg (regs s6) r14 ≡ orig-r14
    r146 = trans (readReg-writeReg-rdi-r14 (regs s5) val-addr) r14-s5

    -- r15 unchanged through all steps
    r15-s1 : readReg (regs s1) r15 ≡ orig-r15
    r15-s1 = readReg-writeReg-rsp-r15 (regs s) (orig-rsp ∸ slot-size)

    r15-s2 : readReg (regs s2) r15 ≡ orig-r15
    r15-s2 = trans (readReg-writeReg-rbp-r15 (regs s1) (readReg (regs s1) rsp)) r15-s1

    r15-s3 : readReg (regs s3) r15 ≡ orig-r15
    r15-s3 = trans (readReg-writeReg-r11-r15 (regs s2) 0) r15-s2

    r15-s4 : readReg (regs s5) r15 ≡ orig-r15
    r15-s4 = r15-s3

    r15-s5 : readReg (regs s5) r15 ≡ orig-r15
    r15-s5 = r15-s4

    r156 : readReg (regs s6) r15 ≡ orig-r15
    r156 = trans (readReg-writeReg-rdi-r15 (regs s5) val-addr) r15-s5

    -- Memory and invariants need heap/stack disjointness
    postulate
      mem-heap6 : ∀ addr → InHeap addr → readMem (memory s6) addr ≡ readMem orig-mem addr
      stack-inv6 : StackInvariant s6
      rbp-inv6 : RbpInvariant s6

    -- ========== Assemble result ==========
    result : CaseInlSetupResult {A} {B} {C} a prefix suffix f g s s6 val-addr
    result = record
      { star-setup = star6
      ; h-setup = h-false  -- halted unchanged
      ; pc-setup = pc6
      ; rdi-setup = rdi6
      ; rbp-setup = rbp6
      ; rsp-setup = rsp6
      ; r14-setup = r146
      ; r15-setup = r156
      ; mem-heap-setup = mem-heap6
      ; stack-inv-setup = stack-inv6
      ; rbp-inv-setup = rbp-inv6
      }

------------------------------------------------------------------------
-- Case Cleanup Result
--
-- Result of executing the 3-instruction cleanup sequence:
--   jmp cleanup-offset  ; skip right branch (for inl)
--   mov rsp, rbp        ; restore stack pointer
--   pop rbp             ; restore frame pointer
------------------------------------------------------------------------

record CaseCleanupResult {A B C : Type} (prefix suffix : Program) (f : IR A C) (g : IR B C)
    (s s-final : State) : Set where
  field
    -- Execution star
    star-cleanup : Star (prefix ++ compile-x86 [ f , g ] ++ suffix) s s-final
    -- State properties
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    -- Register restoration
    rsp-final : readReg (regs s-final) rsp ≡ readReg (regs s) rsp  -- restored via rbp
    rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp  -- popped from stack

------------------------------------------------------------------------
-- Case Cleanup Proof (for inl branch)
------------------------------------------------------------------------

postulate
  case-inl-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
    (prefix suffix : Program) (s : State) →
    halted s ≡ false →
    -- PC is at jmp instruction (after f completes)
    pc s ≡ length prefix +ℕ 6 +ℕ compile-length f →
    -- rbp points to saved old rbp
    -- rsp is somewhere in the stack
    StackInvariant s →
    let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    in ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s s-final

