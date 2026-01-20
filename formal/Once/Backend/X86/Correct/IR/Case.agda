------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Case
--
-- Case setup and cleanup helpers for the case (sum elimination) proof.
-- Non-recursive parts that don't need the mutual recursion dispatcher.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Case where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Once.Backend.X86.Correct.Star using (Star; refl*; step*; star-trans; star-step2; star-step3; star-step6; star-step7)
open import Once.Backend.X86.Correct.FetchStep using (step-exec; fetch-append-skip)
open import Once.Backend.Common.Fetch using (fetch-0; fetch-1; fetch-2; fetch-3; fetch-4; fetch-5; fetch-append-right)
open import Once.Backend.X86.Correct.ExecLemmas
  using (fetch-at-prefix-end; fetch-case-cleanup-mov; fetch-case-cleanup-pop)
open import Once.Backend.X86.Correct.InstrExec
  using (execPush-reg; execMov-reg-reg; execMov-reg-mem-base; execMov-reg-mem-disp;
         execCmp-zero; execCmp-one; execJne-not-taken; execJne-taken; execJmp; execPop; execLabel)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant; stack-inv-preserved-r15-unchanged)
open import Once.Backend.X86.MemoryRegionLemmas
  using (StackPointer) renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; ir-stack-requirement; capacity-after-push;
         capacity-from-larger; slot-1-addr-in-stack; rsp-in-stack;
         make-frame-at-slot; make-frame-at-slot-addr)
open import Once.Backend.X86.Correct.RegisterLemmas
  using (readReg-writeReg-same; readReg-writeReg-rsp-rbp; readReg-writeReg-rsp-rdi;
         readReg-writeReg-rsp-r14; readReg-writeReg-rsp-r15; readReg-writeReg-rsp-rax;
         readReg-writeReg-rbp-rsp; readReg-writeReg-rbp-rdi; readReg-writeReg-rbp-r14; readReg-writeReg-rbp-r15;
         readReg-writeReg-rbp-rax;
         readReg-writeReg-r11-rdi; readReg-writeReg-r11-rsp; readReg-writeReg-r11-rbp;
         readReg-writeReg-r11-r14; readReg-writeReg-r11-r15;
         readReg-writeReg-rdi-rsp; readReg-writeReg-rdi-rbp; readReg-writeReg-rdi-r14; readReg-writeReg-rdi-r15)
open import Once.Backend.X86.MemoryRegionLemmas
  using (InStack; InHeap; InCode; StackPointer; stack-heap-addr-disjoint;
         stack-code-addr-disjoint)
open import Once.Backend.X86.Correct.RegisterLemmas using (readMem-writeMem-diff)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _≥_; _∸_; suc; zero; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; ≤-<-trans; <⇒≤; <⇒≢; m∸n≤m; ≤-refl; m<m+n; m∸n+n≡m)
open import Data.List using (List; _++_; length; _∷_; [])
open import Data.List.Properties using (++-assoc)
open import Once.Backend.X86.Correct.CompileLength using (length-++; compile-length-correct)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; sym; subst; subst₂)

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
    -- Memory preservation (setup only writes to stack via push)
    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-code-setup : ∀ addr → InCode addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-r15-setup  : readMem (memory s-setup) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    -- Memory at rbp/rbp+8/above preserved (push writes below rbp per RbpInvariant)
    mem-rbp-setup  : readMem (memory s-setup) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8-setup : readMem (memory s-setup) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-above-setup : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- Stack frame: push wrote orig-rbp at (rsp - slot-size) = rbp
    mem-saved-rbp : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just (readReg (regs s) rbp)
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
  -- rdi and rdi+8 point to heap (for heap/stack disjointness)
  InHeap (readReg (regs s) rdi) →
  InHeap (readReg (regs s) rdi +ℕ slot-size) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  ∃[ s-setup ] CaseInlSetupResult {A} {B} {C} a prefix suffix f g s s-setup val-addr
case-inl-setup-star {A} {B} {C} f g prefix suffix a s val-addr
    h-false pc-eq tag-is-0 val-ptr-eq rdi-in-heap rdi+8-in-heap stack-inv cap rbp-inv =
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

    -- ========== Memory Preservation via Stack/Heap Disjointness ==========
    -- Push writes to (orig-rsp - slot-size) which is in stack region
    -- Tag address (orig-rdi) is in heap region (from rdi-in-heap)
    -- Stack and heap are disjoint, so memory at orig-rdi is preserved

    -- Get StackCapacity s 1 from cap (ir-stack-requirement [ f , g ] = 1 + ...)
    case-req≥1 : 1 ≤ ir-stack-requirement [ f , g ]
    case-req≥1 = s≤s z≤n  -- 1 ≤ 1 + (...)

    cap-1 : StackCapacity s 1
    cap-1 = capacity-from-larger s 1 (ir-stack-requirement [ f , g ]) cap case-req≥1

    -- Push address is in stack region
    push-addr : ℕ
    push-addr = orig-rsp ∸ slot-size

    push-addr-in-stack : InStack push-addr
    push-addr-in-stack = slot-1-addr-in-stack s cap-1

    -- Disjointness: push-addr ≢ orig-rdi
    push-addr≢orig-rdi : push-addr ≢ orig-rdi
    push-addr≢orig-rdi eq = stack-heap-addr-disjoint push-addr orig-rdi push-addr-in-stack rdi-in-heap eq

    -- Memory preserved at orig-rdi after push (s1 = push result)
    tag-still-0-s1 : readMem (memory s1) orig-rdi ≡ just 0
    tag-still-0-s1 = trans (readMem-writeMem-diff orig-mem push-addr orig-rdi orig-rbp push-addr≢orig-rdi) tag-is-0

    -- s2 = mov rbp, rsp (doesn't modify memory)
    tag-still-0-s2 : readMem (memory s2) orig-rdi ≡ just 0
    tag-still-0-s2 = tag-still-0-s1  -- memory s2 = memory s1

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

    -- Value pointer at rdi+8 is also preserved via stack/heap disjointness
    push-addr≢orig-rdi+8 : push-addr ≢ (orig-rdi +ℕ slot-size)
    push-addr≢orig-rdi+8 eq = stack-heap-addr-disjoint push-addr (orig-rdi +ℕ slot-size) push-addr-in-stack rdi+8-in-heap eq

    -- Memory s1 preserves value pointer
    val-ptr-still-valid-s1 : readMem (memory s1) (orig-rdi +ℕ slot-size) ≡ just val-addr
    val-ptr-still-valid-s1 = trans (readMem-writeMem-diff orig-mem push-addr (orig-rdi +ℕ slot-size) orig-rbp push-addr≢orig-rdi+8) val-ptr-eq

    -- Memory s2 through s5 don't modify memory (mov, cmp, jne only touch registers/flags)
    val-ptr-still-valid : readMem (memory s5) (orig-rdi +ℕ slot-size) ≡ just val-addr
    val-ptr-still-valid = val-ptr-still-valid-s1  -- memory s5 = memory s4 = ... = memory s1

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

    -- ========== Heap Memory Preservation ==========
    -- Any heap address is preserved because push only writes to stack
    mem-heap6 : ∀ addr → InHeap addr → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-heap6 addr addr-in-heap = mem-preserved
      where
        -- Disjointness: push address ≢ any heap address
        push-addr≢addr : push-addr ≢ addr
        push-addr≢addr eq = stack-heap-addr-disjoint push-addr addr push-addr-in-stack addr-in-heap eq

        -- Memory s1 preserves heap address
        mem-s1 : readMem (memory s1) addr ≡ readMem orig-mem addr
        mem-s1 = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr

        -- Memory s2 through s6 don't modify memory (mov/cmp/jne only touch regs/flags/pc)
        mem-preserved : readMem (memory s6) addr ≡ readMem orig-mem addr
        mem-preserved = mem-s1  -- memory s6 = ... = memory s1

    -- Code memory preserved (push writes to stack, not code region)
    mem-code6 : ∀ addr → InCode addr → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-code6 addr addr-in-code = mem-preserved
      where
        push-addr≢addr : push-addr ≢ addr
        push-addr≢addr eq = stack-code-addr-disjoint push-addr addr push-addr-in-stack addr-in-code eq

        mem-s1 : readMem (memory s1) addr ≡ readMem orig-mem addr
        mem-s1 = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr

        mem-preserved : readMem (memory s6) addr ≡ readMem orig-mem addr
        mem-preserved = mem-s1

    -- ========== StackInvariant preservation ==========
    -- r15 is unchanged through all 6 instructions
    -- rsp is decreased (push decreases rsp by slot-size)
    rsp-s6-≤-orig : readReg (regs s6) rsp ≤ orig-rsp
    rsp-s6-≤-orig = subst (_≤ orig-rsp) (sym rsp6) (m∸n≤m orig-rsp slot-size)

    stack-inv6 : StackInvariant s6
    stack-inv6 = stack-inv-preserved-r15-unchanged s s6 stack-inv r156 rsp-s6-≤-orig

    -- ========== RbpInvariant for new frame ==========
    -- After push rbp; mov rbp, rsp: rbp = rsp = orig-rsp - slot-size
    -- This establishes a new frame at slot 1
    new-frame : StackPointer
    new-frame = make-frame-at-slot s cap 1 case-req≥1

    -- The new frame address equals orig-rsp - slots 1 = orig-rsp - slot-size
    new-frame-addr : sp-addr new-frame ≡ orig-rsp ∸ slot-size
    new-frame-addr = make-frame-at-slot-addr 1 s cap case-req≥1

    -- rbp in s6 equals the new frame address
    rbp-is-new-frame : readReg (regs s6) rbp ≡ sp-addr new-frame
    rbp-is-new-frame = trans rbp6 (sym new-frame-addr)

    -- Frame bound: frame address ≥ rsp in s6
    -- Both are orig-rsp - slot-size, so this is ≤-refl
    frame-bound6 : sp-addr new-frame ≥ readReg (regs s6) rsp
    frame-bound6 = subst₂ _≥_ (sym new-frame-addr) (sym rsp6) ≤-refl

    rbp-inv6 : RbpInvariant s6
    rbp-inv6 = record
      { rbp-frame = new-frame
      ; rbp-is-base = rbp-is-new-frame
      ; frame-bound = frame-bound6
      }

    -- ========== Stack Frame Memory ==========
    -- Push wrote orig-rbp at (orig-rsp - slot-size) = rbp-val in s6
    -- Memory is unchanged from s1 to s6 (mov/cmp/jne/mov don't modify memory)
    mem-at-rbp6 : readMem (memory s6) (readReg (regs s6) rbp) ≡ just orig-rbp
    mem-at-rbp6 = subst (λ addr → readMem (memory s6) addr ≡ just orig-rbp) (sym rbp6) push-wrote-rbp
      where
        open import Once.Backend.X86.Correct.RegisterLemmas using (readMem-writeMem-same)
        -- After push, memory s1 at push-addr contains orig-rbp
        push-wrote-orig-rbp : readMem (memory s1) push-addr ≡ just orig-rbp
        push-wrote-orig-rbp = readMem-writeMem-same orig-mem push-addr orig-rbp
        -- Memory unchanged from s1 to s6
        push-wrote-rbp : readMem (memory s6) push-addr ≡ just orig-rbp
        push-wrote-rbp = push-wrote-orig-rbp  -- memory s6 = memory s1

    -- ========== Memory preservation at rbp addresses ==========
    -- Key: push writes to (orig-rsp - slot-size), and RbpInvariant says rbp ≥ rsp
    -- So push-addr = rsp - slot-size < rsp ≤ rbp, meaning push-addr < rbp

    -- From StackCapacity s 1: slot-size < orig-rsp
    slot-size<rsp : slot-size < orig-rsp
    slot-size<rsp = rsp-sufficient cap-1
      where
        open import Once.Backend.X86.Correct.StackInstantiation using (rsp-sufficient)

    -- Therefore push-addr < orig-rsp
    -- Proof: slot-size ≤ rsp, so (rsp - slot-size) + slot-size = rsp
    --        And slot-size > 0, so (rsp - slot-size) < (rsp - slot-size) + slot-size = rsp
    push-addr<rsp : push-addr < orig-rsp
    push-addr<rsp = subst (push-addr <_) sum-eq push-addr<sum
      where
        slot-size≤rsp : slot-size ≤ orig-rsp
        slot-size≤rsp = <⇒≤ slot-size<rsp

        -- (orig-rsp - slot-size) + slot-size = orig-rsp
        sum-eq : push-addr +ℕ slot-size ≡ orig-rsp
        sum-eq = m∸n+n≡m slot-size≤rsp

        -- slot-size > 0, so push-addr < push-addr + slot-size
        push-addr<sum : push-addr < push-addr +ℕ slot-size
        push-addr<sum = m<m+n push-addr {slot-size} (s≤s z≤n)

    -- From RbpInvariant: rsp ≤ rbp
    rsp≤rbp : orig-rsp ≤ orig-rbp
    rsp≤rbp = RbpInvariant.rsp≤rbp rbp-inv

    -- Chain: push-addr < rsp ≤ rbp, so push-addr < rbp
    push-addr<rbp : push-addr < orig-rbp
    push-addr<rbp = <-≤-trans push-addr<rsp rsp≤rbp
      where
        open import Data.Nat.Properties using (<-≤-trans)

    -- Therefore push-addr ≢ rbp
    push-addr≢rbp : push-addr ≢ orig-rbp
    push-addr≢rbp = <⇒≢ push-addr<rbp

    -- Memory at rbp preserved
    mem-rbp-6 : readMem (memory s6) orig-rbp ≡ readMem orig-mem orig-rbp
    mem-rbp-6 = readMem-writeMem-diff orig-mem push-addr orig-rbp orig-rbp push-addr≢rbp

    -- push-addr < rbp < rbp+8, so push-addr ≠ rbp+8
    push-addr<rbp+8 : push-addr < orig-rbp +ℕ 8
    push-addr<rbp+8 = <-trans push-addr<rbp rbp<rbp+8
      where
        rbp<rbp+8 : orig-rbp < orig-rbp +ℕ 8
        rbp<rbp+8 = m<m+n orig-rbp {8} (s≤s z≤n)

    push-addr≢rbp+8 : push-addr ≢ orig-rbp +ℕ 8
    push-addr≢rbp+8 = <⇒≢ push-addr<rbp+8

    mem-rbp+8-6 : readMem (memory s6) (orig-rbp +ℕ 8) ≡ readMem orig-mem (orig-rbp +ℕ 8)
    mem-rbp+8-6 = readMem-writeMem-diff orig-mem push-addr (orig-rbp +ℕ 8) orig-rbp push-addr≢rbp+8

    -- Memory above rbp preserved (any addr > rbp implies addr ≠ push-addr since push-addr < rbp)
    mem-above-6 : ∀ addr → addr > orig-rbp → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-above-6 addr addr>rbp = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr
      where
        push-addr<addr : push-addr < addr
        push-addr<addr = <-trans push-addr<rbp addr>rbp
          where open import Data.Nat.Properties using (<-trans)

        push-addr≢addr : push-addr ≢ addr
        push-addr≢addr = <⇒≢ push-addr<addr

    -- Memory at r15 preserved
    -- Uses stack-write-preserves-r15 which handles all R15Status cases
    mem-r15-6 : readMem (memory s6) (readReg (regs s) r15) ≡ readMem orig-mem (readReg (regs s) r15)
    mem-r15-6 = readMem-writeMem-diff orig-mem push-addr orig-r15 orig-rbp push-addr≢r15
      where
        open import Once.Backend.X86.Correct.StackInvariant
          using (stack-write-preserves-r15; FrameEvidenceFor;
                 R15Status; r15-in-heap; r15-in-code; r15-in-stack)
        open import Once.Backend.X86.MemoryRegionLemmas using (slot-addr; init-slot-at-base)
        open import Data.Unit using (tt)
        open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

        -- push-addr = slot-addr new-frame 0 (slot 0 of the new frame)
        push-addr-is-slot0 : push-addr ≡ slot-addr new-frame 0
        push-addr-is-slot0 = sym (trans (init-slot-at-base new-frame) new-frame-addr)

        -- Helper to compute frame evidence by case analysis
        -- Can't use 'with' on module parameter, so we use a helper function
        compute-frame-evidence : (inv : R15Status s) → FrameEvidenceFor new-frame inv
        compute-frame-evidence (r15-in-heap _) = tt
        compute-frame-evidence (r15-in-code _) = tt
        compute-frame-evidence (r15-in-stack r15-frame r15-slot r15-eq r15-frame-bound) = new-frame≢r15-frame
          where
            -- sp-addr new-frame = orig-rsp - slot-size
            -- sp-addr r15-frame ≥ orig-rsp (from r15-frame-bound)
            -- We need: orig-rsp - slot-size < orig-rsp ≤ sp-addr r15-frame
            -- Therefore: sp-addr new-frame < sp-addr r15-frame, so they're ≠

            new-frame<r15-frame : sp-addr new-frame < sp-addr r15-frame
            new-frame<r15-frame = <-≤-trans new-frame<rsp r15-frame-bound
              where
                -- new-frame < orig-rsp (from slot-size<rsp and m∸n<m logic)
                new-frame<rsp : sp-addr new-frame < orig-rsp
                new-frame<rsp = subst (_< orig-rsp) (sym new-frame-addr) push-addr<rsp

            new-frame≢r15-frame : sp-addr new-frame ≢ sp-addr r15-frame
            new-frame≢r15-frame = <⇒≢ new-frame<r15-frame

        frame-evidence : FrameEvidenceFor new-frame stack-inv
        frame-evidence = compute-frame-evidence stack-inv

        push-addr≢r15 : push-addr ≢ orig-r15
        push-addr≢r15 = stack-write-preserves-r15 s push-addr new-frame 0
                          push-addr-is-slot0 stack-inv frame-evidence

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
      ; mem-code-setup = mem-code6
      ; mem-r15-setup = mem-r15-6
      ; mem-rbp-setup = mem-rbp-6
      ; mem-rbp+8-setup = mem-rbp+8-6
      ; mem-above-setup = mem-above-6
      ; mem-saved-rbp = mem-at-rbp6
      ; stack-inv-setup = stack-inv6
      ; rbp-inv-setup = rbp-inv6
      }

------------------------------------------------------------------------
-- Case Inr Setup Result
--
-- Result of executing the setup sequence for inr branch:
--   0: push rbp
--   1: mov rbp, rsp
--   2: mov r11, [rdi]     ; load tag (should be 1 for inr)
--   3: cmp r11, 0         ; sets ZF=false (1 ≠ 0)
--   4: jne right-offset   ; TAKEN (ZF=false) - jumps to position (7 + len-f)
--   7+len-f: mov rdi, [rdi+8]   ; load value pointer
--
-- After these instructions, PC is at (8 + len-f).
------------------------------------------------------------------------

record CaseInrSetupResult {A B C : Type} (b : ⟦ B ⟧)
    (prefix suffix : Program) (f : IR A C) (g : IR B C)
    (s s-setup : State) (val-addr : ℕ) : Set where
  private
    len-f = compile-length f
  field
    -- Execution star
    star-setup : Star (prefix ++ compile-x86 [ f , g ] ++ suffix) s s-setup
    -- State properties
    h-setup    : halted s-setup ≡ false
    -- PC after 6 instructions: push, mov, mov, cmp, jne(taken to 8+len-f), mov
    pc-setup   : pc s-setup ≡ length prefix +ℕ 9 +ℕ len-f
    -- Register values
    rdi-setup  : readReg (regs s-setup) rdi ≡ val-addr
    rbp-setup  : readReg (regs s-setup) rbp ≡ readReg (regs s) rsp ∸ slot-size
    rsp-setup  : readReg (regs s-setup) rsp ≡ readReg (regs s) rsp ∸ slot-size
    r14-setup  : readReg (regs s-setup) r14 ≡ readReg (regs s) r14
    r15-setup  : readReg (regs s-setup) r15 ≡ readReg (regs s) r15
    -- Memory preservation (setup only writes to stack via push)
    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-code-setup : ∀ addr → InCode addr → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    mem-r15-setup  : readMem (memory s-setup) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    -- Memory at rbp/rbp+8/above preserved (push writes below rbp per RbpInvariant)
    mem-rbp-setup  : readMem (memory s-setup) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp+8-setup : readMem (memory s-setup) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-above-setup : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-setup) addr ≡ readMem (memory s) addr
    -- Stack frame: push wrote orig-rbp at (rsp - slot-size) = rbp
    mem-saved-rbp : readMem (memory s-setup) (readReg (regs s-setup) rbp) ≡ just (readReg (regs s) rbp)
    -- Invariants
    stack-inv-setup : StackInvariant s-setup
    rbp-inv-setup   : RbpInvariant s-setup

------------------------------------------------------------------------
-- Case Inr Setup Proof
--
-- The inr setup executes 6 instructions:
--   0: push rbp           - save frame pointer, rsp -= 8
--   1: mov rbp, rsp       - establish frame base
--   2: mov r11, [rdi]     - load tag (should be 1)
--   3: cmp r11, 0         - sets ZF=false (tag≠0)
--   4: jne right-offset   - TAKEN (ZF=false), jumps to 8+len-f
--   8+len-f: mov rdi, [rdi+8] - load value pointer
------------------------------------------------------------------------

-- | Execute the 6-instruction inr setup sequence
case-inr-setup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
  (prefix suffix : Program) (b : ⟦ B ⟧) (s : State) (val-addr : ℕ) →
  halted s ≡ false →
  pc s ≡ length prefix →
  -- Tag is 1 (from ValidAt inr)
  readMem (memory s) (readReg (regs s) rdi) ≡ just 1 →
  -- Value pointer is at rdi+8
  readMem (memory s) (readReg (regs s) rdi +ℕ slot-size) ≡ just val-addr →
  -- rdi and rdi+8 point to heap (for heap/stack disjointness)
  InHeap (readReg (regs s) rdi) →
  InHeap (readReg (regs s) rdi +ℕ slot-size) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  ∃[ s-setup ] CaseInrSetupResult {A} {B} {C} b prefix suffix f g s s-setup val-addr
case-inr-setup-star {A} {B} {C} f g prefix suffix b s val-addr
    h-false pc-eq tag-is-1 val-ptr-eq rdi-in-heap rdi+8-in-heap stack-inv cap rbp-inv =
    s7 , result
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
    h1 = h-false

    -- ========== Step 2: mov rbp, rsp ==========
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rbp (readReg (regs s1) rsp)
                   ; pc = pc s1 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h-false

    -- ========== Step 3: mov r11, [rdi] ==========
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) r11 1  -- tag is 1 for inr
                   ; pc = pc s2 +ℕ 1 }

    h3 : halted s3 ≡ false
    h3 = h-false

    -- ========== Step 4: cmp r11, 0 ==========
    -- Since r11 = 1 ≠ 0, ZF is set to false
    s4 : State
    s4 = record s3 { pc = pc s3 +ℕ 1
                   ; flags = mkflags false false false }

    h4 : halted s4 ≡ false
    h4 = h-false

    -- ========== Step 5: jne (TAKEN) ==========
    -- jne with offset (case-jne-base + len-f) = 2 + len-f
    -- From pc=4: new pc = 4 + 1 + (2 + len-f) = 7 + len-f (lands at label)
    s5 : State
    s5 = record s4 { pc = pc s4 +ℕ 1 +ℕ (case-jne-base +ℕ len-f) }

    h5 : halted s5 ≡ false
    h5 = h-false

    -- ========== Step 6: label (no-op) at position 7+len-f ==========
    s6 : State
    s6 = record s5 { pc = pc s5 +ℕ 1 }

    h6 : halted s6 ≡ false
    h6 = h-false

    -- ========== Step 7: mov rdi, [rdi+8] at position 8+len-f ==========
    s7 : State
    s7 = record s6 { regs = writeReg (regs s6) rdi val-addr
                   ; pc = pc s6 +ℕ 1 }

    h7 : halted s7 ≡ false
    h7 = h-false

    -- ========== Instructions ==========
    case-code : Program
    case-code = compile-x86 [ f , g ] ++ suffix

    -- ========== Fetch Proofs ==========
    open import Data.Nat.Properties using (+-identityʳ)

    fetch-at-n : ∀ n → fetch prog (length prefix +ℕ n) ≡ fetch case-code n
    fetch-at-n n = fetch-append-right prefix case-code n

    -- Fetch proofs for instructions 0-4 (same as inl)
    fetch1 : fetch prog (pc s) ≡ just (push (reg rbp))
    fetch1 = subst (λ p → fetch prog p ≡ just (push (reg rbp))) (sym pc-eq)
             (subst (λ n → fetch prog n ≡ just (push (reg rbp)))
                    (+-identityʳ (length prefix))
                    (fetch-at-n 0))

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

    -- After jne taken: pc = 4 + 1 + (2 + len-f) = 7 + len-f (lands at label)
    pc5 : pc s5 ≡ length prefix +ℕ 7 +ℕ len-f
    pc5 = trans step1 step2
      where
        step1 : pc s5 ≡ (length prefix +ℕ 4) +ℕ 1 +ℕ (case-jne-base +ℕ len-f)
        step1 = cong (λ x → x +ℕ 1 +ℕ (case-jne-base +ℕ len-f)) pc4

        -- ((length prefix + 4) + 1) + (2 + len-f) = (length prefix + 7) + len-f
        -- case-jne-base = 2
        step2 : (length prefix +ℕ 4) +ℕ 1 +ℕ (case-jne-base +ℕ len-f) ≡ length prefix +ℕ 7 +ℕ len-f
        step2 = trans (cong (_+ℕ (2 +ℕ len-f)) (+-assoc (length prefix) 4 1))
                (trans (sym (+-assoc (length prefix +ℕ 5) 2 len-f))
                       (cong (_+ℕ len-f) (+-assoc (length prefix) 5 2)))

    -- Fetch at position 7+len-f: this is the label instruction
    -- Requires explicit proof since fetch doesn't compute through the nested structure
    fetch6 : fetch prog (pc s5) ≡ just (label (case-right-label-base +ℕ len-f))
    fetch6 = subst (λ p → fetch prog p ≡ just (label (case-right-label-base +ℕ len-f))) (sym pc5) fetch6-at-7+len-f
      where
        open import Data.List using (_∷_; []; _++_) renaming (length to list-length)
        open import Data.Nat.Properties using (+-comm)

        -- The rest of the code after the 6 setup instructions
        rest-inner : Program
        rest-inner = jmp (case-jmp-base +ℕ len-g) ∷
                     label (case-right-label-base +ℕ len-f) ∷
                     mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
                     compile-x86 g ++
                     mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

        rest : Program
        rest = compile-x86 f ++ rest-inner

        after-setup : Program
        after-setup = rest ++ suffix

        -- Position 7+len-f = 6 + (1 + len-f)
        pos-eq : 7 +ℕ len-f ≡ 6 +ℕ (1 +ℕ len-f)
        pos-eq = refl

        -- After skipping 6 setup instructions (definitional)
        skip-setup : fetch case-code (6 +ℕ (1 +ℕ len-f)) ≡ fetch after-setup (1 +ℕ len-f)
        skip-setup = refl

        -- Rewrite after-setup using ++-assoc
        after-f-inner : Program
        after-f-inner = rest-inner ++ suffix

        after-setup-assoc : after-setup ≡ compile-x86 f ++ after-f-inner
        after-setup-assoc = ++-assoc (compile-x86 f) rest-inner suffix

        -- 1 + len-f = len-f + 1 for use with fetch-append-right
        idx-comm : 1 +ℕ len-f ≡ len-f +ℕ 1
        idx-comm = +-comm 1 len-f

        -- Skip compile-x86 f using fetch-append-right
        skip-f : fetch after-setup (1 +ℕ len-f) ≡ fetch after-f-inner 1
        skip-f = trans (cong (λ xs → fetch xs (1 +ℕ len-f)) after-setup-assoc)
                       (trans (cong (λ n → fetch (compile-x86 f ++ after-f-inner) n) idx-comm)
                              (trans (cong (λ n → fetch (compile-x86 f ++ after-f-inner) (n +ℕ 1))
                                           (sym (compile-length-correct f)))
                                     (fetch-append-right (compile-x86 f) after-f-inner 1)))

        -- Fetch at index 1 in rest-inner ++ suffix = label (definitional)
        fetch-label : fetch after-f-inner 1 ≡ just (label (case-right-label-base +ℕ len-f))
        fetch-label = refl

        -- Chain: fetch case-code (7+len-f) = just label
        fetch-case-code-label : fetch case-code (7 +ℕ len-f) ≡ just (label (case-right-label-base +ℕ len-f))
        fetch-case-code-label = trans (cong (λ n → fetch case-code n) pos-eq)
                                      (trans skip-setup (trans skip-f fetch-label))

        -- Use fetch-at-n to go from case-code to prog
        fetch6-at-7+len-f : fetch prog (length prefix +ℕ 7 +ℕ len-f) ≡ just (label (case-right-label-base +ℕ len-f))
        fetch6-at-7+len-f = subst (λ n → fetch prog n ≡ just (label (case-right-label-base +ℕ len-f)))
                                  (sym (+-assoc (length prefix) 7 len-f))
                                  (trans (fetch-at-n (7 +ℕ len-f)) fetch-case-code-label)

    -- After label: pc = 7 + len-f + 1 = 8 + len-f
    pc6 : pc s6 ≡ length prefix +ℕ 8 +ℕ len-f
    pc6 = trans (cong (_+ℕ 1) pc5) helper
      where
        helper : length prefix +ℕ 7 +ℕ len-f +ℕ 1 ≡ length prefix +ℕ 8 +ℕ len-f
        helper = trans (+-assoc (length prefix +ℕ 7) len-f 1)
                 (trans (cong ((length prefix +ℕ 7) +ℕ_) (+-comm len-f 1))
                 (trans (sym (+-assoc (length prefix +ℕ 7) 1 len-f))
                        (cong (_+ℕ len-f) (+-assoc (length prefix) 7 1))))

    -- Fetch at position 8+len-f: this is the inr mov rdi [rdi+8]
    -- Requires explicit proof since fetch doesn't compute through the nested structure
    fetch7 : fetch prog (pc s6) ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size)))
    fetch7 = subst (λ p → fetch prog p ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size)))) (sym pc6) fetch7-at-8+len-f
      where
        open import Data.List using (_∷_; []; _++_) renaming (length to list-length)
        open import Data.Nat.Properties using (+-comm)

        -- The rest of the code after the 6 setup instructions
        rest-inner : Program
        rest-inner = jmp (case-jmp-base +ℕ len-g) ∷
                     label (case-right-label-base +ℕ len-f) ∷
                     mov (reg rdi) (mem (base+disp rdi slot-size)) ∷
                     compile-x86 g ++
                     mov (reg rsp) (reg rbp) ∷ pop rbp ∷ []

        rest : Program
        rest = compile-x86 f ++ rest-inner

        after-setup : Program
        after-setup = rest ++ suffix

        -- Position 8+len-f = 6 + (2 + len-f)
        pos-eq : 8 +ℕ len-f ≡ 6 +ℕ (2 +ℕ len-f)
        pos-eq = refl

        -- After skipping 6 setup instructions (definitional)
        skip-setup : fetch case-code (6 +ℕ (2 +ℕ len-f)) ≡ fetch after-setup (2 +ℕ len-f)
        skip-setup = refl

        -- Rewrite after-setup using ++-assoc
        after-f-inner : Program
        after-f-inner = rest-inner ++ suffix

        after-setup-assoc : after-setup ≡ compile-x86 f ++ after-f-inner
        after-setup-assoc = ++-assoc (compile-x86 f) rest-inner suffix

        -- 2 + len-f = len-f + 2 for use with fetch-append-right
        idx-comm : 2 +ℕ len-f ≡ len-f +ℕ 2
        idx-comm = +-comm 2 len-f

        -- Skip compile-x86 f using fetch-append-right
        skip-f : fetch after-setup (2 +ℕ len-f) ≡ fetch after-f-inner 2
        skip-f = trans (cong (λ xs → fetch xs (2 +ℕ len-f)) after-setup-assoc)
                       (trans (cong (λ n → fetch (compile-x86 f ++ after-f-inner) n) idx-comm)
                              (trans (cong (λ n → fetch (compile-x86 f ++ after-f-inner) (n +ℕ 2))
                                           (sym (compile-length-correct f)))
                                     (fetch-append-right (compile-x86 f) after-f-inner 2)))

        -- Fetch at index 2 in rest-inner ++ suffix = mov rdi [rdi+8] (definitional)
        fetch-mov : fetch after-f-inner 2 ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size)))
        fetch-mov = refl

        -- Chain: fetch case-code (8+len-f) = just (mov rdi [rdi+8])
        fetch-case-code-mov : fetch case-code (8 +ℕ len-f) ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size)))
        fetch-case-code-mov = trans (cong (λ n → fetch case-code n) pos-eq)
                                    (trans skip-setup (trans skip-f fetch-mov))

        -- Use fetch-at-n to go from case-code to prog
        fetch7-at-8+len-f : fetch prog (length prefix +ℕ 8 +ℕ len-f) ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size)))
        fetch7-at-8+len-f = subst (λ n → fetch prog n ≡ just (mov (reg rdi) (mem (base+disp rdi slot-size))))
                                  (sym (+-assoc (length prefix) 8 len-f))
                                  (trans (fetch-at-n (8 +ℕ len-f)) fetch-case-code-mov)

    -- ========== Memory access proofs ==========
    -- rdi preserved through steps 1-6
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) (orig-rsp ∸ slot-size)

    rdi-s2 : readReg (regs s2) rdi ≡ orig-rdi
    rdi-s2 = trans (readReg-writeReg-rbp-rdi (regs s1) (readReg (regs s1) rsp)) rdi-s1

    rdi-s3 : readReg (regs s3) rdi ≡ orig-rdi
    rdi-s3 = trans (readReg-writeReg-r11-rdi (regs s2) 1) rdi-s2

    rdi-s4 : readReg (regs s4) rdi ≡ orig-rdi
    rdi-s4 = rdi-s3

    rdi-s5 : readReg (regs s5) rdi ≡ orig-rdi
    rdi-s5 = rdi-s4

    rdi-s6 : readReg (regs s6) rdi ≡ orig-rdi
    rdi-s6 = rdi-s5  -- label doesn't change registers

    -- Stack/heap disjointness for push
    case-req≥1 : 1 ≤ ir-stack-requirement [ f , g ]
    case-req≥1 = s≤s z≤n

    cap-1 : StackCapacity s 1
    cap-1 = capacity-from-larger s 1 (ir-stack-requirement [ f , g ]) cap case-req≥1

    push-addr : ℕ
    push-addr = orig-rsp ∸ slot-size

    push-addr-in-stack : InStack push-addr
    push-addr-in-stack = slot-1-addr-in-stack s cap-1

    push-addr≢orig-rdi : push-addr ≢ orig-rdi
    push-addr≢orig-rdi eq = stack-heap-addr-disjoint push-addr orig-rdi push-addr-in-stack rdi-in-heap eq

    -- Tag still reads as 1 after push
    tag-still-1-s1 : readMem (memory s1) orig-rdi ≡ just 1
    tag-still-1-s1 = trans (readMem-writeMem-diff orig-mem push-addr orig-rdi orig-rbp push-addr≢orig-rdi) tag-is-1

    mem3 : readMem (memory s2) (readReg (regs s2) rdi) ≡ just 1
    mem3 = subst (λ addr → readMem (memory s2) addr ≡ just 1) (sym rdi-s2) tag-still-1-s1

    -- Value pointer preserved for step 7
    push-addr≢orig-rdi+8 : push-addr ≢ (orig-rdi +ℕ slot-size)
    push-addr≢orig-rdi+8 eq = stack-heap-addr-disjoint push-addr (orig-rdi +ℕ slot-size) push-addr-in-stack rdi+8-in-heap eq

    val-ptr-still-valid-s1 : readMem (memory s1) (orig-rdi +ℕ slot-size) ≡ just val-addr
    val-ptr-still-valid-s1 = trans (readMem-writeMem-diff orig-mem push-addr (orig-rdi +ℕ slot-size) orig-rbp push-addr≢orig-rdi+8) val-ptr-eq

    -- Memory at s6 (after label, same as s5 since label doesn't modify memory)
    mem7 : readMem (memory s6) (readReg (regs s6) rdi +ℕ slot-size) ≡ just val-addr
    mem7 = subst (λ addr → readMem (memory s6) (addr +ℕ slot-size) ≡ just val-addr) (sym rdi-s6) val-ptr-still-valid-s1

    -- ========== ExecInstr Proofs ==========
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s (push (reg rbp)) h-false fetch1) (execPush-reg prog s rbp)

    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 (mov (reg rbp) (reg rsp)) h1 fetch2) (execMov-reg-reg s1 rbp rsp)

    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 (mov (reg r11) (mem (base rdi))) h2 fetch3)
                  (execMov-reg-mem-base s2 r11 rdi 1 mem3)

    -- r11 = 1 after step 3
    r11-s3 : readReg (regs s3) r11 ≡ 1
    r11-s3 = readReg-writeReg-same (regs s2) r11 1

    step4 : step prog s3 ≡ just s4
    step4 = trans (step-exec prog s3 (cmp (reg r11) (imm 0)) h3 fetch4) (execCmp-one prog s3 r11 r11-s3)

    -- ZF = false after cmp 1, 0
    zf-s4 : zf (flags s4) ≡ false
    zf-s4 = refl

    step5 : step prog s4 ≡ just s5
    step5 = trans (step-exec prog s4 (jne (case-jne-base +ℕ len-f)) h4 fetch5)
                  (execJne-taken prog s4 (case-jne-base +ℕ len-f) zf-s4)

    step6 : step prog s5 ≡ just s6
    step6 = trans (step-exec prog s5 (label (case-right-label-base +ℕ len-f)) h5 fetch6)
                  (execLabel prog s5 (case-right-label-base +ℕ len-f))

    step7 : step prog s6 ≡ just s7
    step7 = trans (step-exec prog s6 (mov (reg rdi) (mem (base+disp rdi slot-size))) h6 fetch7)
                  (execMov-reg-mem-disp s6 rdi rdi slot-size val-addr mem7)

    -- Build star
    star7 : Star prog s s7
    star7 = star-step7 h-false step1 h1 step2 h2 step3 h3 step4 h4 step5 h5 step6 h6 step7

    -- ========== Final PC ==========
    pc7 : pc s7 ≡ length prefix +ℕ 9 +ℕ len-f
    pc7 = trans (cong (_+ℕ 1) pc6) helper
      where
        -- (length prefix + 8 + len-f) + 1 = length prefix + 9 + len-f
        helper : length prefix +ℕ 8 +ℕ len-f +ℕ 1 ≡ length prefix +ℕ 9 +ℕ len-f
        helper = trans (+-assoc (length prefix +ℕ 8) len-f 1)
                 (trans (cong ((length prefix +ℕ 8) +ℕ_) (+-comm len-f 1))
                 (trans (sym (+-assoc (length prefix +ℕ 8) 1 len-f))
                        (cong (_+ℕ len-f) (+-assoc (length prefix) 8 1))))

    -- ========== Register values in s7 ==========
    rdi7 : readReg (regs s7) rdi ≡ val-addr
    rdi7 = readReg-writeReg-same (regs s6) rdi val-addr

    -- rsp chain
    rsp-s1 : readReg (regs s1) rsp ≡ orig-rsp ∸ slot-size
    rsp-s1 = readReg-writeReg-same (regs s) rsp (orig-rsp ∸ slot-size)

    rsp-s2 : readReg (regs s2) rsp ≡ orig-rsp ∸ slot-size
    rsp-s2 = trans (readReg-writeReg-rbp-rsp (regs s1) (readReg (regs s1) rsp)) rsp-s1

    rsp-s3 : readReg (regs s3) rsp ≡ orig-rsp ∸ slot-size
    rsp-s3 = trans (readReg-writeReg-r11-rsp (regs s2) 1) rsp-s2

    -- s4, s5, s6 don't modify rsp (only flags and pc change)
    rsp6 : readReg (regs s6) rsp ≡ orig-rsp ∸ slot-size
    rsp6 = rsp-s3

    rsp7 : readReg (regs s7) rsp ≡ orig-rsp ∸ slot-size
    rsp7 = trans (readReg-writeReg-rdi-rsp (regs s6) val-addr) rsp6

    -- rbp chain
    rbp-s2 : readReg (regs s2) rbp ≡ orig-rsp ∸ slot-size
    rbp-s2 = trans (readReg-writeReg-same (regs s1) rbp (readReg (regs s1) rsp)) rsp-s1

    rbp-s3 : readReg (regs s3) rbp ≡ orig-rsp ∸ slot-size
    rbp-s3 = trans (readReg-writeReg-r11-rbp (regs s2) 1) rbp-s2

    -- s4, s5, s6 don't modify rbp
    rbp6 : readReg (regs s6) rbp ≡ orig-rsp ∸ slot-size
    rbp6 = rbp-s3

    rbp7 : readReg (regs s7) rbp ≡ orig-rsp ∸ slot-size
    rbp7 = trans (readReg-writeReg-rdi-rbp (regs s6) val-addr) rbp6

    -- r14 chain
    r14-s1 : readReg (regs s1) r14 ≡ orig-r14
    r14-s1 = readReg-writeReg-rsp-r14 (regs s) (orig-rsp ∸ slot-size)

    r14-s2 : readReg (regs s2) r14 ≡ orig-r14
    r14-s2 = trans (readReg-writeReg-rbp-r14 (regs s1) (readReg (regs s1) rsp)) r14-s1

    r14-s3 : readReg (regs s3) r14 ≡ orig-r14
    r14-s3 = trans (readReg-writeReg-r11-r14 (regs s2) 1) r14-s2

    -- s4, s5, s6 don't modify r14
    r146 : readReg (regs s6) r14 ≡ orig-r14
    r146 = r14-s3

    r147 : readReg (regs s7) r14 ≡ orig-r14
    r147 = trans (readReg-writeReg-rdi-r14 (regs s6) val-addr) r146

    -- r15 chain
    r15-s1 : readReg (regs s1) r15 ≡ orig-r15
    r15-s1 = readReg-writeReg-rsp-r15 (regs s) (orig-rsp ∸ slot-size)

    r15-s2 : readReg (regs s2) r15 ≡ orig-r15
    r15-s2 = trans (readReg-writeReg-rbp-r15 (regs s1) (readReg (regs s1) rsp)) r15-s1

    r15-s3 : readReg (regs s3) r15 ≡ orig-r15
    r15-s3 = trans (readReg-writeReg-r11-r15 (regs s2) 1) r15-s2

    -- s4, s5, s6 don't modify r15
    r156 : readReg (regs s6) r15 ≡ orig-r15
    r156 = r15-s3

    r157 : readReg (regs s7) r15 ≡ orig-r15
    r157 = trans (readReg-writeReg-rdi-r15 (regs s6) val-addr) r156

    -- ========== Memory Preservation ==========
    mem-heap6 : ∀ addr → InHeap addr → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-heap6 addr addr-in-heap = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr
      where
        push-addr≢addr : push-addr ≢ addr
        push-addr≢addr eq = stack-heap-addr-disjoint push-addr addr push-addr-in-stack addr-in-heap eq

    mem-code6 : ∀ addr → InCode addr → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-code6 addr addr-in-code = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr
      where
        push-addr≢addr : push-addr ≢ addr
        push-addr≢addr eq = stack-code-addr-disjoint push-addr addr push-addr-in-stack addr-in-code eq

    -- ========== StackInvariant preservation ==========
    rsp-s7-≤-orig : readReg (regs s7) rsp ≤ orig-rsp
    rsp-s7-≤-orig = subst (_≤ orig-rsp) (sym rsp7) (m∸n≤m orig-rsp slot-size)

    stack-inv7 : StackInvariant s7
    stack-inv7 = stack-inv-preserved-r15-unchanged s s7 stack-inv r157 rsp-s7-≤-orig

    -- ========== RbpInvariant for new frame ==========
    new-frame : StackPointer
    new-frame = make-frame-at-slot s cap 1 case-req≥1

    new-frame-addr : sp-addr new-frame ≡ orig-rsp ∸ slot-size
    new-frame-addr = make-frame-at-slot-addr 1 s cap case-req≥1

    rbp-is-new-frame7 : readReg (regs s7) rbp ≡ sp-addr new-frame
    rbp-is-new-frame7 = trans rbp7 (sym new-frame-addr)

    frame-bound7 : sp-addr new-frame ≥ readReg (regs s7) rsp
    frame-bound7 = subst₂ _≥_ (sym new-frame-addr) (sym rsp7) ≤-refl

    rbp-inv7 : RbpInvariant s7
    rbp-inv7 = record
      { rbp-frame = new-frame
      ; rbp-is-base = rbp-is-new-frame7
      ; frame-bound = frame-bound7
      }

    -- ========== Stack Frame Memory ==========
    -- memory s7 = memory s6 (mov rdi doesn't write memory)
    mem-at-rbp7 : readMem (memory s7) (readReg (regs s7) rbp) ≡ just orig-rbp
    mem-at-rbp7 = subst (λ addr → readMem (memory s7) addr ≡ just orig-rbp) (sym rbp7) push-wrote-rbp
      where
        open import Once.Backend.X86.Correct.RegisterLemmas using (readMem-writeMem-same)
        push-wrote-orig-rbp : readMem (memory s1) push-addr ≡ just orig-rbp
        push-wrote-orig-rbp = readMem-writeMem-same orig-mem push-addr orig-rbp
        push-wrote-rbp : readMem (memory s7) push-addr ≡ just orig-rbp
        push-wrote-rbp = push-wrote-orig-rbp  -- memory unchanged through s1 → s7

    -- ========== Memory at rbp addresses ==========
    slot-size<rsp : slot-size < orig-rsp
    slot-size<rsp = rsp-sufficient cap-1
      where
        open import Once.Backend.X86.Correct.StackInstantiation using (rsp-sufficient)

    push-addr<rsp : push-addr < orig-rsp
    push-addr<rsp = subst (push-addr <_) sum-eq push-addr<sum
      where
        slot-size≤rsp : slot-size ≤ orig-rsp
        slot-size≤rsp = <⇒≤ slot-size<rsp
        sum-eq : push-addr +ℕ slot-size ≡ orig-rsp
        sum-eq = m∸n+n≡m slot-size≤rsp
        push-addr<sum : push-addr < push-addr +ℕ slot-size
        push-addr<sum = m<m+n push-addr {slot-size} (s≤s z≤n)

    rsp≤rbp : orig-rsp ≤ orig-rbp
    rsp≤rbp = RbpInvariant.rsp≤rbp rbp-inv

    push-addr<rbp : push-addr < orig-rbp
    push-addr<rbp = <-≤-trans push-addr<rsp rsp≤rbp
      where open import Data.Nat.Properties using (<-≤-trans)

    push-addr≢rbp : push-addr ≢ orig-rbp
    push-addr≢rbp = <⇒≢ push-addr<rbp

    mem-rbp-6 : readMem (memory s6) orig-rbp ≡ readMem orig-mem orig-rbp
    mem-rbp-6 = readMem-writeMem-diff orig-mem push-addr orig-rbp orig-rbp push-addr≢rbp

    push-addr<rbp+8 : push-addr < orig-rbp +ℕ 8
    push-addr<rbp+8 = <-trans push-addr<rbp rbp<rbp+8
      where
        rbp<rbp+8 : orig-rbp < orig-rbp +ℕ 8
        rbp<rbp+8 = m<m+n orig-rbp {8} (s≤s z≤n)

    push-addr≢rbp+8 : push-addr ≢ orig-rbp +ℕ 8
    push-addr≢rbp+8 = <⇒≢ push-addr<rbp+8

    mem-rbp+8-6 : readMem (memory s6) (orig-rbp +ℕ 8) ≡ readMem orig-mem (orig-rbp +ℕ 8)
    mem-rbp+8-6 = readMem-writeMem-diff orig-mem push-addr (orig-rbp +ℕ 8) orig-rbp push-addr≢rbp+8

    mem-above-6 : ∀ addr → addr > orig-rbp → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-above-6 addr addr>rbp = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr
      where
        push-addr<addr : push-addr < addr
        push-addr<addr = <-trans push-addr<rbp addr>rbp
        push-addr≢addr : push-addr ≢ addr
        push-addr≢addr = <⇒≢ push-addr<addr

    -- Memory at r15 preserved
    mem-r15-6 : readMem (memory s6) (readReg (regs s) r15) ≡ readMem orig-mem (readReg (regs s) r15)
    mem-r15-6 = readMem-writeMem-diff orig-mem push-addr orig-r15 orig-rbp push-addr≢r15
      where
        open import Once.Backend.X86.Correct.StackInvariant
          using (stack-write-preserves-r15; FrameEvidenceFor;
                 R15Status; r15-in-heap; r15-in-code; r15-in-stack)
        open import Once.Backend.X86.MemoryRegionLemmas using (slot-addr; init-slot-at-base)
        open import Data.Unit using (tt)
        open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

        push-addr-is-slot0 : push-addr ≡ slot-addr new-frame 0
        push-addr-is-slot0 = sym (trans (init-slot-at-base new-frame) new-frame-addr)

        compute-frame-evidence : (inv : R15Status s) → FrameEvidenceFor new-frame inv
        compute-frame-evidence (r15-in-heap _) = tt
        compute-frame-evidence (r15-in-code _) = tt
        compute-frame-evidence (r15-in-stack r15-frame r15-slot r15-eq r15-frame-bound) = new-frame≢r15-frame
          where
            new-frame<r15-frame : sp-addr new-frame < sp-addr r15-frame
            new-frame<r15-frame = <-≤-trans new-frame<rsp r15-frame-bound
              where
                new-frame<rsp : sp-addr new-frame < orig-rsp
                new-frame<rsp = subst (_< orig-rsp) (sym new-frame-addr) push-addr<rsp

            new-frame≢r15-frame : sp-addr new-frame ≢ sp-addr r15-frame
            new-frame≢r15-frame = <⇒≢ new-frame<r15-frame

        frame-evidence : FrameEvidenceFor new-frame stack-inv
        frame-evidence = compute-frame-evidence stack-inv

        push-addr≢r15 : push-addr ≢ orig-r15
        push-addr≢r15 = stack-write-preserves-r15 s push-addr new-frame 0
                          push-addr-is-slot0 stack-inv frame-evidence

    -- ========== Assemble result ==========
    -- Note: memory s7 = memory s6 definitionally (mov rdi doesn't write memory)
    -- so the mem-*-6 proofs work directly for s7
    result : CaseInrSetupResult {A} {B} {C} b prefix suffix f g s s7 val-addr
    result = record
      { star-setup = star7
      ; h-setup = h-false
      ; pc-setup = pc7
      ; rdi-setup = rdi7
      ; rbp-setup = rbp7
      ; rsp-setup = rsp7
      ; r14-setup = r147
      ; r15-setup = r157
      ; mem-heap-setup = mem-heap6  -- memory s7 = memory s6
      ; mem-code-setup = mem-code6
      ; mem-r15-setup = mem-r15-6
      ; mem-rbp-setup = mem-rbp-6
      ; mem-rbp+8-setup = mem-rbp+8-6
      ; mem-above-setup = mem-above-6
      ; mem-saved-rbp = mem-at-rbp7
      ; stack-inv-setup = stack-inv7
      ; rbp-inv-setup = rbp-inv7
      }

------------------------------------------------------------------------
-- Case Cleanup Result
--
-- Result of executing the 3-instruction cleanup sequence:
--   jmp cleanup-offset  ; skip right branch (for inl)
--   mov rsp, rbp        ; restore stack pointer
--   pop rbp             ; restore frame pointer
--
-- Takes original rsp/rbp as parameters since cleanup restores to original values.
------------------------------------------------------------------------

record CaseCleanupResult {A B C : Type} (prefix suffix : Program) (f : IR A C) (g : IR B C)
    (s s-final : State) (orig-rsp orig-rbp : ℕ) : Set where
  field
    -- Execution star
    star-cleanup : Star (prefix ++ compile-x86 [ f , g ] ++ suffix) s s-final
    -- State properties
    h-final : halted s-final ≡ false
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    -- Register restoration to original values
    rsp-final : readReg (regs s-final) rsp ≡ orig-rsp
    rbp-final : readReg (regs s-final) rbp ≡ orig-rbp
    -- Register preservation (r14/r15/rax unchanged through cleanup)
    r14-preserved : readReg (regs s-final) r14 ≡ readReg (regs s) r14
    r15-preserved : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    rax-preserved : readReg (regs s-final) rax ≡ readReg (regs s) rax
    -- Memory preservation (cleanup doesn't write to memory)
    memory-preserved : memory s-final ≡ memory s

------------------------------------------------------------------------
-- Case Cleanup Proof (for inl branch)
--
-- The cleanup sequence is:
--   6+len-f:      jmp (2+len-g)       ; skip to cleanup (target = 9+len-f+len-g)
--   9+len-f+len-g: mov rsp, rbp       ; restore stack pointer
--   10+len-f+len-g: pop rbp           ; restore frame pointer, pc becomes 11+len-f+len-g
------------------------------------------------------------------------

case-inl-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
  (prefix suffix : Program) (s : State) (orig-rsp orig-rbp : ℕ) →
  halted s ≡ false →
  -- PC is at jmp instruction (after f completes)
  pc s ≡ length prefix +ℕ 6 +ℕ compile-length f →
  -- rbp is the frame pointer from setup: orig-rsp - slot-size
  readReg (regs s) rbp ≡ orig-rsp ∸ slot-size →
  -- Memory at rbp contains the saved orig-rbp
  readMem (memory s) (readReg (regs s) rbp) ≡ just orig-rbp →
  -- Stack has capacity (orig-rsp ≥ slot-size for subtraction to be valid)
  slot-size ≤ orig-rsp →
  StackInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s s-final orig-rsp orig-rbp
case-inl-cleanup-star {A} {B} {C} f g prefix suffix s orig-rsp orig-rbp
    h-false pc-eq rbp-eq mem-rbp rsp-cap stack-inv =
    s3 , result
  where
    len-f = compile-length f
    len-g = compile-length g
    prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    case-code = compile-x86 [ f , g ] ++ suffix

    -- Current rbp value
    rbp-val = readReg (regs s) rbp

    -- ========== Step 1: jmp (case-jmp-base + len-g) ==========
    -- Jump from 6+len-f to 9+len-f+len-g
    s1 : State
    s1 = record s { pc = pc s +ℕ 3 +ℕ len-g }  -- jmp skips to cleanup (offset = 2 + len-g, but PC-relative adds 1 for instruction)

    h1 : halted s1 ≡ false
    h1 = h-false

    -- ========== Step 2: mov rsp, rbp ==========
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rsp rbp-val
                   ; pc = pc s1 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h-false

    -- ========== Step 3: pop rbp ==========
    -- pop reads from rsp, stores to rbp, increments rsp
    -- Define s3 using readReg so execPop directly produces it (no equality conversion needed)
    s3 : State
    s3 = record s2 { regs = writeReg (writeReg (regs s2) rbp orig-rbp) rsp (readReg (regs s2) rsp +ℕ slot-size)
                   ; pc = pc s2 +ℕ 1 }

    -- ========== Fetch and step proofs ==========
    open import Data.Nat.Properties using (+-identityʳ)

    -- fetch at length prefix + n in prog equals fetch at n in case-code
    fetch-at-n : ∀ n → fetch prog (length prefix +ℕ n) ≡ fetch case-code n
    fetch-at-n n = fetch-append-right prefix case-code n

    -- PC at start of cleanup: length prefix + 6 + len-f
    -- This is where the jmp instruction is

    -- Helper: fetch at index 6 in a list starting with 6 elements skips to the tail
    fetch-skip-6 : ∀ (i0 i1 i2 i3 i4 i5 : Instr) (xs : List Instr) (n : ℕ) →
      fetch (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ xs) (6 +ℕ n) ≡ fetch xs n
    fetch-skip-6 i0 i1 i2 i3 i4 i5 xs n = refl

    -- The compile-x86 [ f , g ] structure:
    -- i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ (compile-x86 f ++ jmp ∷ label ∷ mov ∷ compile-x86 g ++ cleanup)
    -- where cleanup = mov rsp rbp ∷ pop rbp ∷ []

    -- Setup instructions (indices 0-5)
    setup-0 = push (reg rbp)
    setup-1 = mov (reg rbp) (reg rsp)
    setup-2 = mov (reg r11) (mem (base rdi))
    setup-3 = cmp (reg r11) (imm 0)
    setup-4 = jne (case-jne-base +ℕ len-f)
    setup-5 = mov (reg rdi) (mem (base+disp rdi slot-size))

    -- Middle code after f (indices 6+len-f onwards in case code)
    jmp-instr = jmp (case-jmp-base +ℕ len-g)
    label-instr = label (case-right-label-base +ℕ len-f)
    mov-rdi-instr = mov (reg rdi) (mem (base+disp rdi slot-size))

    -- Cleanup instructions (indices 9+len-f+len-g and 10+len-f+len-g)
    cleanup-mov = mov (reg rsp) (reg rbp)
    cleanup-pop = pop rbp

    -- Middle code structure
    middle-code : List Instr
    middle-code = jmp-instr ∷ label-instr ∷ mov-rdi-instr ∷ compile-x86 g ++ cleanup-mov ∷ cleanup-pop ∷ []

    -- The tail after setup instructions
    after-setup : List Instr
    after-setup = compile-x86 f ++ middle-code

    -- compile-x86 [ f , g ] = setup ++ after-setup
    case-code-structure : compile-x86 [ f , g ] ≡
      setup-0 ∷ setup-1 ∷ setup-2 ∷ setup-3 ∷ setup-4 ∷ setup-5 ∷ after-setup
    case-code-structure = refl

    -- fetch at index 6+len-f in case-code gets jmp
    -- First skip 6 setup instrs, then skip len-f instrs of compile-x86 f, get jmp at head
    fetch-case-code-jmp : fetch case-code (6 +ℕ len-f) ≡ just jmp-instr
    fetch-case-code-jmp =
      let
        -- Step 1: case-code = compile-x86 [ f , g ] ++ suffix
        -- fetch case-code (6+len-f) = fetch (compile-x86 [ f , g ] ++ suffix) (6+len-f)
        -- Since 6+len-f < length (compile-x86 [ f , g ]), we can use fetch-append-left
        -- Actually, let's use a more direct approach

        -- Step 2: compile-x86 [ f , g ] = setup ++ after-setup
        -- fetch (compile-x86 [ f , g ] ++ suffix) (6+len-f)
        -- = fetch (setup ++ after-setup ++ suffix) (6+len-f)  where setup has length 6
        -- = fetch (after-setup ++ suffix) len-f  by fetch-append-right

        -- Step 3: after-setup = compile-x86 f ++ middle-code
        -- fetch (after-setup ++ suffix) len-f
        -- = fetch ((compile-x86 f ++ middle-code) ++ suffix) len-f
        -- = fetch (compile-x86 f ++ (middle-code ++ suffix)) len-f  by ++-assoc
        -- = fetch (middle-code ++ suffix) 0  by fetch-append-right

        -- Step 4: middle-code = jmp ∷ ...
        -- fetch (jmp ∷ ...) 0 = just jmp

        -- Putting it together:
        step1 : fetch case-code (6 +ℕ len-f) ≡ fetch (after-setup ++ suffix) len-f
        step1 = trans (cong (λ c → fetch (c ++ suffix) (6 +ℕ len-f)) case-code-structure)
                      (fetch-skip-6 setup-0 setup-1 setup-2 setup-3 setup-4 setup-5 (after-setup ++ suffix) len-f)

        step2 : fetch (after-setup ++ suffix) len-f ≡ fetch ((compile-x86 f ++ middle-code) ++ suffix) len-f
        step2 = refl

        step3 : fetch ((compile-x86 f ++ middle-code) ++ suffix) len-f ≡ fetch (compile-x86 f ++ (middle-code ++ suffix)) len-f
        step3 = cong (λ xs → fetch xs len-f) (++-assoc (compile-x86 f) middle-code suffix)

        -- len-f = compile-length f = length (compile-x86 f) by compile-length-correct
        len-f-eq : len-f ≡ length (compile-x86 f)
        len-f-eq = sym (compile-length-correct f)

        step4 : fetch (compile-x86 f ++ (middle-code ++ suffix)) len-f ≡ fetch (middle-code ++ suffix) 0
        step4 = trans (cong (λ n → fetch (compile-x86 f ++ (middle-code ++ suffix)) n)
                            (trans len-f-eq (sym (+-identityʳ (length (compile-x86 f))))))
                      (fetch-append-right (compile-x86 f) (middle-code ++ suffix) 0)

        step5 : fetch (middle-code ++ suffix) 0 ≡ just jmp-instr
        step5 = refl
      in trans step1 (trans step2 (trans step3 (trans step4 step5)))

    -- Now prove fetch-jmp using fetch-case-code-jmp
    fetch-jmp : fetch prog (pc s) ≡ just (jmp (case-jmp-base +ℕ len-g))
    fetch-jmp =
      let
        -- pc s = length prefix + 6 + len-f (using pc-eq which has compile-length f = len-f)
        -- Note: len-f = compile-length f by definition, so they're definitionally equal
        pc-eq' : pc s ≡ length prefix +ℕ (6 +ℕ len-f)
        pc-eq' = trans pc-eq (+-assoc (length prefix) 6 len-f)

        -- fetch prog (length prefix + (6 + len-f)) = fetch case-code (6 + len-f)
        step1 : fetch prog (length prefix +ℕ (6 +ℕ len-f)) ≡ fetch case-code (6 +ℕ len-f)
        step1 = fetch-at-n (6 +ℕ len-f)
      in trans (cong (fetch prog) pc-eq') (trans step1 fetch-case-code-jmp)

    -- step1: execute jmp instruction
    -- execInstr prog s (jmp target) = just (record s { pc = pc s + 1 + target })
    -- target = case-jmp-base + len-g = 2 + len-g
    -- So new pc = pc s + 1 + 2 + len-g = pc s + 3 + len-g
    -- s1 = record s { pc = pc s + 3 + len-g }
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s jmp-instr h-false fetch-jmp)
                  (trans (execJmp prog s (case-jmp-base +ℕ len-g))
                         (cong just (cong (λ p → record s { pc = p }) pc-arith)))
      where
        -- pc s + 1 + (case-jmp-base + len-g) = pc s + 1 + (2 + len-g) = pc s + 3 + len-g
        pc-arith : pc s +ℕ 1 +ℕ (case-jmp-base +ℕ len-g) ≡ pc s +ℕ 3 +ℕ len-g
        pc-arith = trans (cong (λ n → pc s +ℕ 1 +ℕ n) refl)  -- case-jmp-base = 2
                         (trans (sym (+-assoc (pc s +ℕ 1) 2 len-g))
                                (cong (_+ℕ len-g) (+-assoc (pc s) 1 2)))

    -- PC values for subsequent instructions
    -- pc s1 = pc s + 3 + len-g = (length prefix + 6 + len-f) + 3 + len-g = length prefix + 9 + len-f + len-g
    pc-s1 : pc s1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    pc-s1 =
      let
        -- pc s1 = pc s + 3 + len-g  (by definition of s1)
        -- pc s = length prefix + 6 + len-f  (by pc-eq)
        step1 : pc s1 ≡ (length prefix +ℕ 6 +ℕ len-f) +ℕ 3 +ℕ len-g
        step1 = cong (λ p → p +ℕ 3 +ℕ len-g) pc-eq

        -- (a + 6 + b) + 3 + c = a + 9 + b + c
        -- Inner: ((lp + 6) + len-f) + 3 ≡ (lp + 9) + len-f
        inner : ((length prefix +ℕ 6) +ℕ len-f) +ℕ 3 ≡ (length prefix +ℕ 9) +ℕ len-f
        inner = trans (+-assoc (length prefix +ℕ 6) len-f 3)
                      (trans (cong ((length prefix +ℕ 6) +ℕ_) (+-comm len-f 3))
                             (trans (sym (+-assoc (length prefix +ℕ 6) 3 len-f))
                                    (cong (_+ℕ len-f) (+-assoc (length prefix) 6 3))))

        step2 : (length prefix +ℕ 6 +ℕ len-f) +ℕ 3 +ℕ len-g ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
        step2 = cong (_+ℕ len-g) inner
      in trans step1 step2

    -- Helper: fetch at index 3 in a list starting with 3 elements skips to the tail
    fetch-skip-3 : ∀ (i0 i1 i2 : Instr) (xs : List Instr) (n : ℕ) →
      fetch (i0 ∷ i1 ∷ i2 ∷ xs) (3 +ℕ n) ≡ fetch xs n
    fetch-skip-3 i0 i1 i2 xs n = refl

    -- fetch at index 9+len-f+len-g in case-code gets cleanup-mov
    -- Uses symbolic position from CodeGen: case-cleanup-position f g

    -- Position equivalence: 9 + len-f + len-g = case-cleanup-position f g
    -- case-cleanup-position f g = ((6 + len-f) + 3) + len-g
    -- We need to show: (9 + len-f) + len-g = ((6 + len-f) + 3) + len-g
    pos-eq-cleanup : case-cleanup-position f g ≡ 9 +ℕ len-f +ℕ len-g
    pos-eq-cleanup = trans (cong (_+ℕ len-g) (+-assoc 6 len-f 3))
                           (trans (cong (λ x → (6 +ℕ x) +ℕ len-g) (+-comm len-f 3))
                                  (cong (_+ℕ len-g) (sym (+-assoc 6 3 len-f))))

    fetch-case-code-cleanup : fetch case-code (9 +ℕ len-f +ℕ len-g) ≡ just cleanup-mov
    fetch-case-code-cleanup = trans (cong (fetch case-code) (sym pos-eq-cleanup))
                                    (fetch-case-cleanup-mov f g suffix)

    -- Prove fetch-mov-cleanup using fetch-case-code-cleanup
    fetch-mov-cleanup : fetch prog (pc s1) ≡ just (mov (reg rsp) (reg rbp))
    fetch-mov-cleanup =
      let
        -- pc s1 = ((length prefix + 9) + len-f) + len-g (from pc-s1, left-assoc)
        -- We need: length prefix + (9 + len-f + len-g) = length prefix + ((9 + len-f) + len-g)
        pc-eq' : pc s1 ≡ length prefix +ℕ (9 +ℕ len-f +ℕ len-g)
        pc-eq' = trans pc-s1
                       (trans (+-assoc (length prefix +ℕ 9) len-f len-g)
                              (trans (+-assoc (length prefix) 9 (len-f +ℕ len-g))
                                     (cong (length prefix +ℕ_) (sym (+-assoc 9 len-f len-g)))))

        step1' : fetch prog (length prefix +ℕ (9 +ℕ len-f +ℕ len-g)) ≡ fetch case-code (9 +ℕ len-f +ℕ len-g)
        step1' = fetch-at-n (9 +ℕ len-f +ℕ len-g)
      in trans (cong (fetch prog) pc-eq') (trans step1' fetch-case-code-cleanup)

    -- step2: execute mov rsp rbp instruction
    -- execInstr prog s (mov dst src) = just (record s { regs = writeReg (regs s) dst val, pc = pc s + 1 })
    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 cleanup-mov h1 fetch-mov-cleanup) refl

    -- fetch-pop: fetch at pc s2
    -- pc s2 = pc s1 + 1 = length prefix + 9 + len-f + len-g + 1 = length prefix + 10 + len-f + len-g
    pc-s2 : pc s2 ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
    pc-s2 = trans step1' (trans step2' (trans step3' (trans step4' (trans step5' step6'))))
      where
        -- pc s2 = pc s1 + 1  (definitionally from s2 definition)
        -- First convert pc s1 + 1 to a workable form using pc-s1
        step1' : pc s2 ≡ ((length prefix +ℕ 9) +ℕ len-f) +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s1

        -- (((a + 9) + b) + c) + 1 = ((a + 10) + b) + c
        -- Regroup using associativity
        step2' : ((length prefix +ℕ 9) +ℕ len-f) +ℕ len-g +ℕ 1 ≡ ((length prefix +ℕ 9) +ℕ len-f) +ℕ (len-g +ℕ 1)
        step2' = +-assoc ((length prefix +ℕ 9) +ℕ len-f) len-g 1

        step3' : ((length prefix +ℕ 9) +ℕ len-f) +ℕ (len-g +ℕ 1) ≡ (length prefix +ℕ 9) +ℕ (len-f +ℕ (len-g +ℕ 1))
        step3' = +-assoc (length prefix +ℕ 9) len-f (len-g +ℕ 1)

        step4' : (length prefix +ℕ 9) +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ length prefix +ℕ (9 +ℕ (len-f +ℕ (len-g +ℕ 1)))
        step4' = +-assoc (length prefix) 9 (len-f +ℕ (len-g +ℕ 1))

        -- Now 9 + (len-f + (len-g + 1)) = 9 + ((len-f + len-g) + 1) = 9 + (1 + (len-f + len-g))
        --   = (9 + 1) + (len-f + len-g) = 10 + (len-f + len-g) = 10 + len-f + len-g
        inner1 : len-f +ℕ (len-g +ℕ 1) ≡ (len-f +ℕ len-g) +ℕ 1
        inner1 = sym (+-assoc len-f len-g 1)

        inner2 : (len-f +ℕ len-g) +ℕ 1 ≡ 1 +ℕ (len-f +ℕ len-g)
        inner2 = +-comm (len-f +ℕ len-g) 1

        inner3 : 9 +ℕ (1 +ℕ (len-f +ℕ len-g)) ≡ (9 +ℕ 1) +ℕ (len-f +ℕ len-g)
        inner3 = sym (+-assoc 9 1 (len-f +ℕ len-g))

        inner4 : (9 +ℕ 1) +ℕ (len-f +ℕ len-g) ≡ 10 +ℕ len-f +ℕ len-g
        inner4 = sym (+-assoc 10 len-f len-g)

        step5' : length prefix +ℕ (9 +ℕ (len-f +ℕ (len-g +ℕ 1))) ≡ length prefix +ℕ (10 +ℕ len-f +ℕ len-g)
        step5' = cong (length prefix +ℕ_)
                     (trans (cong (9 +ℕ_) inner1)
                            (trans (cong (9 +ℕ_) inner2)
                                   (trans inner3 inner4)))

        step6' : length prefix +ℕ (10 +ℕ len-f +ℕ len-g) ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
        step6' = trans (sym (+-assoc (length prefix) (10 +ℕ len-f) len-g))
                      (cong (_+ℕ len-g) (sym (+-assoc (length prefix) 10 len-f)))

    -- fetch at index 10+len-f+len-g in case-code gets cleanup-pop
    -- Position equivalence: case-cleanup-position f g + 1 = 10 + len-f + len-g
    pos-eq-pop : case-cleanup-position f g +ℕ 1 ≡ 10 +ℕ len-f +ℕ len-g
    pos-eq-pop = trans (cong (_+ℕ 1) pos-eq-cleanup)  -- ((9 + len-f) + len-g) + 1
                       (trans (+-assoc (9 +ℕ len-f) len-g 1)  -- (9 + len-f) + (len-g + 1)
                              (trans (+-assoc 9 len-f (len-g +ℕ 1))  -- 9 + (len-f + (len-g + 1))
                                     (trans (cong (9 +ℕ_) (sym (+-assoc len-f len-g 1)))  -- 9 + ((len-f + len-g) + 1)
                                            (trans (cong (9 +ℕ_) (+-comm (len-f +ℕ len-g) 1))  -- 9 + (1 + (len-f + len-g))
                                                   (trans (sym (+-assoc 9 1 (len-f +ℕ len-g)))  -- 10 + (len-f + len-g)
                                                          (sym (+-assoc 10 len-f len-g)))))))  -- (10 + len-f) + len-g

    fetch-case-code-pop : fetch case-code (10 +ℕ len-f +ℕ len-g) ≡ just cleanup-pop
    fetch-case-code-pop = trans (cong (fetch case-code) (sym pos-eq-pop))
                                (fetch-case-cleanup-pop f g suffix)

    fetch-pop : fetch prog (pc s2) ≡ just (pop rbp)
    fetch-pop =
      let
        -- pc s2 = ((length prefix + 10) + len-f) + len-g (from pc-s2, left-assoc)
        pc-eq' : pc s2 ≡ length prefix +ℕ (10 +ℕ len-f +ℕ len-g)
        pc-eq' = trans pc-s2
                       (trans (+-assoc (length prefix +ℕ 10) len-f len-g)
                              (trans (+-assoc (length prefix) 10 (len-f +ℕ len-g))
                                     (cong (length prefix +ℕ_) (sym (+-assoc 10 len-f len-g)))))

        step1' : fetch prog (length prefix +ℕ (10 +ℕ len-f +ℕ len-g)) ≡ fetch case-code (10 +ℕ len-f +ℕ len-g)
        step1' = fetch-at-n (10 +ℕ len-f +ℕ len-g)
      in trans (cong (fetch prog) pc-eq') (trans step1' fetch-case-code-pop)

    -- step3: execute pop rbp instruction
    -- Memory is unchanged through jmp (s1) and mov (s2): memory s2 = memory s
    -- After mov rsp, rbp: readReg (regs s2) rsp = rbp-val = readReg (regs s) rbp

    -- rsp in s2 = rbp-val (from mov rsp, rbp)
    rsp-s2 : readReg (regs s2) rsp ≡ rbp-val
    rsp-s2 = readReg-writeReg-same (regs s1) rsp rbp-val

    -- Memory at rsp in s2 = memory at rbp-val in s = orig-rbp
    mem-s2-at-rsp : readMem (memory s2) (readReg (regs s2) rsp) ≡ just orig-rbp
    mem-s2-at-rsp = trans (cong (readMem (memory s2)) rsp-s2) mem-rbp

    -- execPop directly produces s3 (no equality conversion needed)
    step3 : step prog s2 ≡ just s3
    step3 = trans (step-exec prog s2 cleanup-pop h2 fetch-pop)
                  (execPop prog s2 rbp orig-rbp mem-s2-at-rsp)

    star3 : Star prog s s3
    star3 = star-step3 h-false step1 h1 step2 h2 step3

    -- ========== Final PC ==========
    -- PC after cleanup = 11 + len-f + len-g = compile-length [ f , g ]
    -- Since compile-length [ f , g ] = case-overhead + len-f + len-g = 11 + len-f + len-g
    pc3 : pc s3 ≡ length prefix +ℕ compile-length [ f , g ]
    pc3 = trans step1' (trans step2' (trans step3' (trans step4' (trans step5' step6'))))
      where
        -- pc s3 = pc s2 + 1  (definitionally from s3 definition)
        step1' : pc s3 ≡ ((length prefix +ℕ 10) +ℕ len-f) +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s2

        -- Regroup: (((a + 10) + b) + c) + 1 = ((a + 10) + b) + (c + 1)
        step2' : ((length prefix +ℕ 10) +ℕ len-f) +ℕ len-g +ℕ 1 ≡ ((length prefix +ℕ 10) +ℕ len-f) +ℕ (len-g +ℕ 1)
        step2' = +-assoc ((length prefix +ℕ 10) +ℕ len-f) len-g 1

        -- ((a + 10) + b) + (c + 1) = (a + 10) + (b + (c + 1))
        step3' : ((length prefix +ℕ 10) +ℕ len-f) +ℕ (len-g +ℕ 1) ≡ (length prefix +ℕ 10) +ℕ (len-f +ℕ (len-g +ℕ 1))
        step3' = +-assoc (length prefix +ℕ 10) len-f (len-g +ℕ 1)

        -- (a + 10) + (b + (c + 1)) = a + (10 + (b + (c + 1)))
        step4' : (length prefix +ℕ 10) +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ length prefix +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1)))
        step4' = +-assoc (length prefix) 10 (len-f +ℕ (len-g +ℕ 1))

        -- 10 + (b + (c + 1)) = 11 + b + c = (11 + b) + c = compile-length [ f , g ]
        -- First: b + (c + 1) = (b + c) + 1
        inner1 : len-f +ℕ (len-g +ℕ 1) ≡ (len-f +ℕ len-g) +ℕ 1
        inner1 = sym (+-assoc len-f len-g 1)

        -- (b + c) + 1 = 1 + (b + c)
        inner2 : (len-f +ℕ len-g) +ℕ 1 ≡ 1 +ℕ (len-f +ℕ len-g)
        inner2 = +-comm (len-f +ℕ len-g) 1

        -- 10 + (1 + (b + c)) = (10 + 1) + (b + c) = 11 + (b + c)
        inner3 : 10 +ℕ (1 +ℕ (len-f +ℕ len-g)) ≡ (10 +ℕ 1) +ℕ (len-f +ℕ len-g)
        inner3 = sym (+-assoc 10 1 (len-f +ℕ len-g))

        -- 11 + (b + c) = (11 + b) + c
        inner4 : 11 +ℕ (len-f +ℕ len-g) ≡ (11 +ℕ len-f) +ℕ len-g
        inner4 = sym (+-assoc 11 len-f len-g)

        -- compile-length [ f , g ] = (case-overhead + len-f) + len-g = (11 + len-f) + len-g
        step5' : length prefix +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1))) ≡ length prefix +ℕ ((11 +ℕ len-f) +ℕ len-g)
        step5' = cong (length prefix +ℕ_)
                     (trans (cong (10 +ℕ_) inner1)
                            (trans (cong (10 +ℕ_) inner2)
                                   (trans inner3 inner4)))

        -- length prefix + ((11 + len-f) + len-g) = length prefix + compile-length [ f , g ]
        step6' : length prefix +ℕ ((11 +ℕ len-f) +ℕ len-g) ≡ length prefix +ℕ compile-length [ f , g ]
        step6' = refl  -- case-overhead = 11 definitionally

    -- ========== Final register values ==========
    -- rsp in s3 = readReg (regs s2) rsp + slot-size = rbp-val + slot-size = orig-rsp
    open import Data.Nat.Properties using (m∸n+n≡m)

    rsp3 : readReg (regs s3) rsp ≡ orig-rsp
    rsp3 = trans (readReg-writeReg-same (writeReg (regs s2) rbp orig-rbp) rsp (readReg (regs s2) rsp +ℕ slot-size))
                 (trans (cong (_+ℕ slot-size) rsp-s2)
                        (trans (cong (_+ℕ slot-size) rbp-eq) (m∸n+n≡m rsp-cap)))

    -- rbp in s3 = orig-rbp (the value loaded from memory)
    rbp3 : readReg (regs s3) rbp ≡ orig-rbp
    rbp3 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                 (readReg-writeReg-same (regs s2) rbp orig-rbp)

    -- r14 unchanged through cleanup
    r14-3 : readReg (regs s3) r14 ≡ readReg (regs s) r14
    r14-3 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r14 (regs s2) orig-rbp)
                         (readReg-writeReg-rsp-r14 (regs s1) rbp-val))

    r15-3 : readReg (regs s3) r15 ≡ readReg (regs s) r15
    r15-3 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r15 (regs s2) orig-rbp)
                         (readReg-writeReg-rsp-r15 (regs s1) rbp-val))

    -- rax unchanged through cleanup
    rax-3 : readReg (regs s3) rax ≡ readReg (regs s) rax
    rax-3 = trans (readReg-writeReg-rsp-rax (writeReg (regs s2) rbp orig-rbp) (readReg (regs s2) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-rax (regs s2) orig-rbp)
                         (readReg-writeReg-rsp-rax (regs s1) rbp-val))

    -- Memory unchanged through cleanup (jmp, mov, pop don't write memory)
    mem-3 : memory s3 ≡ memory s
    mem-3 = refl  -- s1, s2, s3 only update regs and pc, not memory

    -- ========== Assemble result ==========
    result : CaseCleanupResult {A} {B} {C} prefix suffix f g s s3 orig-rsp orig-rbp
    result = record
      { star-cleanup = star3
      ; h-final = h-false
      ; pc-final = pc3
      ; rsp-final = rsp3
      ; rbp-final = rbp3
      ; r14-preserved = r14-3
      ; r15-preserved = r15-3
      ; rax-preserved = rax-3
      ; memory-preserved = mem-3
      }

------------------------------------------------------------------------
-- Case Inr Cleanup
--
-- Result of executing the 2-instruction cleanup sequence (for inr):
--   mov rsp, rbp        ; restore stack pointer
--   pop rbp             ; restore frame pointer
--
-- Unlike inl cleanup, there's no jmp since we're already at cleanup.
------------------------------------------------------------------------

-- | Execute cleanup after g completes (inr branch)
-- PC starts at position 9 + len-f + len-g (after g)
case-inr-cleanup-star : ∀ {A B C} (f : IR A C) (g : IR B C)
  (prefix suffix : Program) (s : State) (orig-rsp orig-rbp : ℕ) →
  halted s ≡ false →
  -- PC is at cleanup position (after g completes)
  pc s ≡ length prefix +ℕ 9 +ℕ compile-length f +ℕ compile-length g →
  -- rbp is the frame pointer from setup: orig-rsp - slot-size
  readReg (regs s) rbp ≡ orig-rsp ∸ slot-size →
  -- Memory at rbp contains the saved orig-rbp
  readMem (memory s) (readReg (regs s) rbp) ≡ just orig-rbp →
  -- Stack has capacity (orig-rsp ≥ slot-size for subtraction to be valid)
  slot-size ≤ orig-rsp →
  StackInvariant s →
  let prog = prefix ++ compile-x86 [ f , g ] ++ suffix
  in ∃[ s-final ] CaseCleanupResult {A} {B} {C} prefix suffix f g s s-final orig-rsp orig-rbp
case-inr-cleanup-star {A} {B} {C} f g prefix suffix s orig-rsp orig-rbp
    h-false pc-eq rbp-eq mem-rbp rsp-cap stack-inv =
    s2 , result
  where
    len-f = compile-length f
    len-g = compile-length g
    prog = prefix ++ compile-x86 [ f , g ] ++ suffix
    case-code = compile-x86 [ f , g ] ++ suffix

    -- Current rbp value
    rbp-val = readReg (regs s) rbp

    -- ========== Step 1: mov rsp, rbp ==========
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp rbp-val
                  ; pc = pc s +ℕ 1 }

    h1 : halted s1 ≡ false
    h1 = h-false

    -- ========== Step 2: pop rbp ==========
    -- pop rbp: reads mem[rsp], stores in rbp, increments rsp
    s2 : State
    s2 = record s1 { regs = writeReg (writeReg (regs s1) rbp orig-rbp) rsp (readReg (regs s1) rsp +ℕ slot-size)
                   ; pc = pc s1 +ℕ 1 }

    h2 : halted s2 ≡ false
    h2 = h-false

    -- ========== Fetch proofs ==========
    open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
    open import Data.Nat.Properties using (m∸n+n≡m)

    fetch-at-n : ∀ n → fetch prog (length prefix +ℕ n) ≡ fetch case-code n
    fetch-at-n n = fetch-append-right prefix case-code n

    -- Position 9 + len-f + len-g is the cleanup mov instruction
    cleanup-mov : Instr
    cleanup-mov = mov (reg rsp) (reg rbp)

    cleanup-pop : Instr
    cleanup-pop = pop rbp

    -- PC at s: length prefix + 9 + len-f + len-g
    pc-s : pc s ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g
    pc-s = pc-eq

    -- Fetch at position 9 + len-f + len-g: mov rsp, rbp
    -- case-cleanup-position f g = ((6 + len-f) + 3) + len-g = (9 + len-f) + len-g (left-assoc)
    -- pc-s: pc s = ((length prefix + 9) + len-f) + len-g
    -- need: pc s = length prefix + case-cleanup-position f g
    fetch-mov : fetch prog (pc s) ≡ just cleanup-mov
    fetch-mov =
      let -- Step 1: regroup to (length prefix + (9 + len-f)) + len-g
          step1 : length prefix +ℕ 9 +ℕ len-f +ℕ len-g ≡ (length prefix +ℕ (9 +ℕ len-f)) +ℕ len-g
          step1 = cong (_+ℕ len-g) (+-assoc (length prefix) 9 len-f)

          -- Step 2: regroup to length prefix + ((9 + len-f) + len-g)
          step2 : (length prefix +ℕ (9 +ℕ len-f)) +ℕ len-g ≡ length prefix +ℕ ((9 +ℕ len-f) +ℕ len-g)
          step2 = +-assoc (length prefix) (9 +ℕ len-f) len-g

          -- (9 + len-f) + len-g = ((6 + len-f) + 3) + len-g = case-cleanup-position f g
          inner-eq' : 9 +ℕ len-f ≡ (6 +ℕ len-f) +ℕ 3
          inner-eq' = trans (sym (+-assoc 6 3 len-f))
                            (trans (cong (6 +ℕ_) (+-comm 3 len-f))
                                   (+-assoc 6 len-f 3))

          inner-eq : (9 +ℕ len-f) +ℕ len-g ≡ case-cleanup-position f g
          inner-eq = cong (_+ℕ len-g) inner-eq'

          step3 : length prefix +ℕ ((9 +ℕ len-f) +ℕ len-g) ≡ length prefix +ℕ case-cleanup-position f g
          step3 = cong (length prefix +ℕ_) inner-eq

          pc-eq' : pc s ≡ length prefix +ℕ case-cleanup-position f g
          pc-eq' = trans pc-s (trans step1 (trans step2 step3))
      in trans (cong (fetch prog) pc-eq')
               (trans (fetch-at-n (case-cleanup-position f g))
                      (fetch-case-cleanup-mov f g suffix))

    -- step1: execute mov rsp, rbp instruction
    step1 : step prog s ≡ just s1
    step1 = trans (step-exec prog s cleanup-mov h-false fetch-mov)
                  (execMov-reg-reg s rsp rbp)

    -- PC at s1: length prefix + 10 + len-f + len-g
    pc-s1 : pc s1 ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
    pc-s1 = trans step1' (trans step2' step3')
      where
        -- pc s1 = pc s + 1
        step1' : pc s1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s

        -- Regroup: (((a + 9) + b) + c) + 1 = ((a + 9) + b) + (c + 1)
        step2' : length prefix +ℕ 9 +ℕ len-f +ℕ len-g +ℕ 1 ≡ length prefix +ℕ 9 +ℕ len-f +ℕ (len-g +ℕ 1)
        step2' = +-assoc (length prefix +ℕ 9 +ℕ len-f) len-g 1

        -- 9 + len-f + (len-g + 1) = 10 + len-f + len-g
        -- LHS: (((lp + 9) + f) + (g + 1)), RHS: (((lp + 10) + f) + g)
        step3' : length prefix +ℕ 9 +ℕ len-f +ℕ (len-g +ℕ 1) ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g
        step3' =
          let lp = length prefix
              -- (((lp + 9) + f) + (g + 1)) = (((lp + 9) + f) + g) + 1
              s1 : lp +ℕ 9 +ℕ len-f +ℕ (len-g +ℕ 1) ≡ lp +ℕ 9 +ℕ len-f +ℕ len-g +ℕ 1
              s1 = sym (+-assoc (lp +ℕ 9 +ℕ len-f) len-g 1)
              -- ((lp + 9) + f) + g = (lp + 9) + (f + g)
              s2 : lp +ℕ 9 +ℕ len-f +ℕ len-g ≡ lp +ℕ 9 +ℕ (len-f +ℕ len-g)
              s2 = +-assoc (lp +ℕ 9) len-f len-g
              -- lp + 9 + x + 1 = (lp + 9 + 1) + x = (lp + 10) + x
              s3 : lp +ℕ 9 +ℕ (len-f +ℕ len-g) +ℕ 1 ≡ lp +ℕ 10 +ℕ (len-f +ℕ len-g)
              s3 = trans (+-assoc (lp +ℕ 9) (len-f +ℕ len-g) 1)
                         (trans (cong ((lp +ℕ 9) +ℕ_) (+-comm (len-f +ℕ len-g) 1))
                                (trans (sym (+-assoc (lp +ℕ 9) 1 (len-f +ℕ len-g)))
                                       (cong (_+ℕ (len-f +ℕ len-g)) (+-assoc lp 9 1))))
              -- (lp + 10) + (f + g) = ((lp + 10) + f) + g
              s4 : lp +ℕ 10 +ℕ (len-f +ℕ len-g) ≡ lp +ℕ 10 +ℕ len-f +ℕ len-g
              s4 = sym (+-assoc (lp +ℕ 10) len-f len-g)
          in trans s1 (trans (cong (_+ℕ 1) s2) (trans s3 s4))

    -- Fetch at position 10 + len-f + len-g: pop rbp
    fetch-pop : fetch prog (pc s1) ≡ just cleanup-pop
    fetch-pop =
      let -- pc-s1 : pc s1 ≡ (((lp + 10) + f) + g)
          -- goal: pc s1 ≡ lp + (case-cleanup-position f g + 1)
          -- case-cleanup-position f g + 1 = (((6 + f) + 3) + g) + 1 = (((9 + f) + g) + 1)
          lp = length prefix

          -- Show (((lp + 10) + f) + g) = lp + (((9 + f) + g) + 1)
          -- Step 1: flatten LHS to lp + 10 + f + g
          -- Step 2: show this equals lp + (9 + f + g + 1)

          -- First, show inner arithmetic: 10 + f + g = (9 + f + g) + 1
          inner-10 : 10 +ℕ len-f +ℕ len-g ≡ (9 +ℕ len-f +ℕ len-g) +ℕ 1
          inner-10 = trans (+-assoc (9 +ℕ 1) len-f len-g)
                           (trans (cong (λ x → x +ℕ len-f +ℕ len-g) (+-comm 9 1))
                                  (trans (sym (+-assoc 1 9 (len-f +ℕ len-g)))
                                         (trans (cong (1 +ℕ_) (sym (+-assoc 9 len-f len-g)))
                                                (+-comm 1 (9 +ℕ len-f +ℕ len-g)))))

          -- case-cleanup-position f g = 9 + f + g (with different associativity)
          cleanup-eq : 9 +ℕ len-f +ℕ len-g ≡ case-cleanup-position f g
          cleanup-eq = cong (_+ℕ len-g) (trans (sym (+-assoc 6 3 len-f))
                                               (trans (cong (6 +ℕ_) (+-comm 3 len-f))
                                                      (+-assoc 6 len-f 3)))

          inner-cleanup : 10 +ℕ len-f +ℕ len-g ≡ case-cleanup-position f g +ℕ 1
          inner-cleanup = trans inner-10 (cong (_+ℕ 1) cleanup-eq)

          -- pc-s1 gives us (((lp + 10) + f) + g)
          -- We need lp + (case-cleanup-position f g + 1)
          pc-eq' : pc s1 ≡ lp +ℕ (case-cleanup-position f g +ℕ 1)
          pc-eq' = trans pc-s1
                         (trans (+-assoc (lp +ℕ 10) len-f len-g)
                                (trans (+-assoc lp 10 (len-f +ℕ len-g))
                                       (trans (cong (lp +ℕ_) (sym (+-assoc 10 len-f len-g)))
                                              (cong (lp +ℕ_) inner-cleanup))))
      in trans (cong (fetch prog) pc-eq')
               (trans (fetch-at-n (case-cleanup-position f g +ℕ 1))
                      (fetch-case-cleanup-pop f g suffix))

    -- rsp in s1 = rbp-val (from mov rsp, rbp)
    rsp-s1 : readReg (regs s1) rsp ≡ rbp-val
    rsp-s1 = readReg-writeReg-same (regs s) rsp rbp-val

    -- Memory at rsp in s1 = memory at rbp-val in s = orig-rbp
    mem-s1-at-rsp : readMem (memory s1) (readReg (regs s1) rsp) ≡ just orig-rbp
    mem-s1-at-rsp = trans (cong (readMem (memory s1)) rsp-s1) mem-rbp

    -- step2: execute pop rbp instruction
    step2 : step prog s1 ≡ just s2
    step2 = trans (step-exec prog s1 cleanup-pop h1 fetch-pop)
                  (execPop prog s1 rbp orig-rbp mem-s1-at-rsp)

    star2 : Star prog s s2
    star2 = star-step2 h-false step1 h1 step2

    -- ========== Final PC ==========
    -- PC after cleanup = 11 + len-f + len-g = compile-length [ f , g ]
    pc2 : pc s2 ≡ length prefix +ℕ compile-length [ f , g ]
    pc2 = trans step1' (trans step2' step3')
      where
        -- pc s2 = pc s1 + 1  (definitionally from s2 definition)
        step1' : pc s2 ≡ length prefix +ℕ 10 +ℕ len-f +ℕ len-g +ℕ 1
        step1' = cong (_+ℕ 1) pc-s1

        -- Regroup: (((a + 10) + b) + c) + 1 = (a + (11 + b)) + c
        step2' : length prefix +ℕ 10 +ℕ len-f +ℕ len-g +ℕ 1 ≡ length prefix +ℕ (11 +ℕ len-f) +ℕ len-g
        step2' =
          let lp = length prefix
              -- Step 1: ((((lp + 10) + f) + g) + 1) = (((lp + 10) + f) + (g + 1))
              s1 : lp +ℕ 10 +ℕ len-f +ℕ len-g +ℕ 1 ≡ lp +ℕ 10 +ℕ len-f +ℕ (len-g +ℕ 1)
              s1 = +-assoc (lp +ℕ 10 +ℕ len-f) len-g 1
              -- Step 2: (((lp + 10) + f) + (g + 1)) = ((lp + 10) + (f + (g + 1)))
              s2 : lp +ℕ 10 +ℕ len-f +ℕ (len-g +ℕ 1) ≡ lp +ℕ 10 +ℕ (len-f +ℕ (len-g +ℕ 1))
              s2 = +-assoc (lp +ℕ 10) len-f (len-g +ℕ 1)
              -- Step 3: ((lp + 10) + x) = (lp + (10 + x))
              s3 : lp +ℕ 10 +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ lp +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1)))
              s3 = +-assoc lp 10 (len-f +ℕ (len-g +ℕ 1))
              -- Inner: 10 + (f + (g + 1)) = (11 + f) + g
              inner : 10 +ℕ (len-f +ℕ (len-g +ℕ 1)) ≡ (11 +ℕ len-f) +ℕ len-g
              inner = trans (sym (+-assoc 10 len-f (len-g +ℕ 1)))                  -- (10 + f) + (g + 1)
                      (trans (sym (+-assoc (10 +ℕ len-f) len-g 1))                 -- ((10 + f) + g) + 1
                      (trans (cong (_+ℕ 1) (+-assoc 10 len-f len-g))               -- (10 + (f + g)) + 1
                      (trans (+-assoc 10 (len-f +ℕ len-g) 1)                       -- 10 + ((f + g) + 1)
                      (trans (cong (10 +ℕ_) (+-comm (len-f +ℕ len-g) 1))           -- 10 + (1 + (f + g))
                      (trans (sym (+-assoc 10 1 (len-f +ℕ len-g)))                 -- (10 + 1) + (f + g)
                             (sym (+-assoc 11 len-f len-g)))))))                   -- (11 + f) + g
              -- Step 4: lp + (10 + (f + (g + 1))) = lp + ((11 + f) + g)
              s4 : lp +ℕ (10 +ℕ (len-f +ℕ (len-g +ℕ 1))) ≡ lp +ℕ ((11 +ℕ len-f) +ℕ len-g)
              s4 = cong (lp +ℕ_) inner
              -- Step 5: lp + ((11 + f) + g) = (lp + (11 + f)) + g
              s5 : lp +ℕ ((11 +ℕ len-f) +ℕ len-g) ≡ lp +ℕ (11 +ℕ len-f) +ℕ len-g
              s5 = sym (+-assoc lp (11 +ℕ len-f) len-g)
          in trans s1 (trans s2 (trans s3 (trans s4 s5)))

        -- length prefix + (11 + len-f) + len-g = length prefix + compile-length [ f , g ]
        step3' : length prefix +ℕ (11 +ℕ len-f) +ℕ len-g ≡ length prefix +ℕ compile-length [ f , g ]
        step3' = +-assoc (length prefix) (11 +ℕ len-f) len-g  -- compile-length [ f , g ] = (11 + len-f) + len-g

    -- ========== Final register values ==========
    rsp2 : readReg (regs s2) rsp ≡ orig-rsp
    rsp2 = trans (readReg-writeReg-same (writeReg (regs s1) rbp orig-rbp) rsp (readReg (regs s1) rsp +ℕ slot-size))
                 (trans (cong (_+ℕ slot-size) rsp-s1)
                        (trans (cong (_+ℕ slot-size) rbp-eq) (m∸n+n≡m rsp-cap)))

    rbp2 : readReg (regs s2) rbp ≡ orig-rbp
    rbp2 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                 (readReg-writeReg-same (regs s1) rbp orig-rbp)

    -- r14 unchanged through cleanup
    r14-2 : readReg (regs s2) r14 ≡ readReg (regs s) r14
    r14-2 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r14 (regs s1) orig-rbp)
                         (readReg-writeReg-rsp-r14 (regs s) rbp-val))

    r15-2 : readReg (regs s2) r15 ≡ readReg (regs s) r15
    r15-2 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-r15 (regs s1) orig-rbp)
                         (readReg-writeReg-rsp-r15 (regs s) rbp-val))

    -- rax unchanged through cleanup
    rax-2 : readReg (regs s2) rax ≡ readReg (regs s) rax
    rax-2 = trans (readReg-writeReg-rsp-rax (writeReg (regs s1) rbp orig-rbp) (readReg (regs s1) rsp +ℕ slot-size))
                  (trans (readReg-writeReg-rbp-rax (regs s1) orig-rbp)
                         (readReg-writeReg-rsp-rax (regs s) rbp-val))

    -- Memory unchanged through cleanup (mov, pop don't write memory)
    mem-2 : memory s2 ≡ memory s
    mem-2 = refl  -- s1, s2 only update regs and pc, not memory

    -- ========== Assemble result ==========
    result : CaseCleanupResult {A} {B} {C} prefix suffix f g s s2 orig-rsp orig-rbp
    result = record
      { star-cleanup = star2
      ; h-final = h-false
      ; pc-final = pc2
      ; rsp-final = rsp2
      ; rbp-final = rbp2
      ; r14-preserved = r14-2
      ; r15-preserved = r15-2
      ; rax-preserved = rax-2
      ; memory-preserved = mem-2
      }

