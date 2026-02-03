------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.CaseSetup
--
-- Setup instruction-tracing proofs for case (sum elimination):
--   case-inl-setup-star: 6-instruction inl setup sequence
--   case-inr-setup-star: 6-instruction inr setup sequence (with jne taken)
--
-- Extracted from IR/Case.agda to reduce type-checking time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.CaseSetup where

open import Once.Type

-- Import from Foundation to get X86ContractInterface-instantiated types
open import Once.Backend.X86.Correct.Foundation
  using (IR; [_,_]; inl; inr; ⟦_⟧; compile-x86; compile-length;
         case-overhead; case-right-label-base; case-jmp-base; case-jne-base;
         case-setup-count; case-prefix-count; case-cleanup-count;
         Instr; Program)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags

open import Once.Backend.X86.Correct.Star using (Star; refl*; step*; star-trans; star-step2; star-step3; star-step6; star-step7)
open import Once.Backend.X86.Correct.FetchStep using (step-exec; fetch-append-skip)
open import Once.Backend.Common.Fetch using (fetch-0; fetch-1; fetch-2; fetch-3; fetch-4; fetch-5; fetch-append-right)
open import Once.Backend.X86.Correct.ExecLemmas
  using (fetch-at-prefix-end; fetch-case-cleanup-mov; fetch-case-cleanup-pop)
open import Once.Backend.X86.Correct.InstrExec
  using (execPush-reg; execMov-reg-reg; execMov-reg-mem-base; execMov-reg-mem-disp;
         execCmp-zero; execCmp-one; execJne-not-taken; execJne-taken; execJmp; execPop; execLabel)
open import Once.Backend.X86.Correct.StarBase using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; Region; InRegion; Stack; Heap; HeapAlloc; StackAlloc; stack-offset; caller-disjoint-from-current)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant; stack-inv-preserved-r15-unchanged)
open import Once.Backend.X86.Layout
  using (StackPointer) renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slots; slot-size; StackCapacity; ir-stack-requirement; ir-output-capacity;
         capacity-after-push; capacity-from-larger; slot-1-addr-in-stack; rsp-in-stack;
         make-frame-at-slot; make-frame-at-slot-addr; rsp-sufficient)
open import Once.Backend.X86.Correct.RegisterLemmas
  using (readReg-writeReg-same; readReg-writeReg-rsp-rbp; readReg-writeReg-rsp-rdi;
         readReg-writeReg-rsp-r14; readReg-writeReg-rsp-r15; readReg-writeReg-rsp-rax;
         readReg-writeReg-rbp-rsp; readReg-writeReg-rbp-rdi; readReg-writeReg-rbp-r14; readReg-writeReg-rbp-r15;
         readReg-writeReg-rbp-rax;
         readReg-writeReg-r11-rdi; readReg-writeReg-r11-rsp; readReg-writeReg-r11-rbp;
         readReg-writeReg-r11-r14; readReg-writeReg-r11-r15;
         readReg-writeReg-rdi-rsp; readReg-writeReg-rdi-rbp; readReg-writeReg-rdi-r14; readReg-writeReg-rdi-r15)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; StackPointer; stack-heap-addr-disjoint;
         stack-code-addr-disjoint)
open import Once.Backend.X86.Correct.RegisterLemmas using (readMem-writeMem-diff)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_; _≤_; _<_; _≥_; _∸_; suc; zero; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; ≤-<-trans; <-≤-trans; <⇒≤; <⇒≢; m∸n≤m; ≤-refl; m<m+n; m∸n+n≡m)
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
    -- Memory preserved at addresses ≥ entry-rsp (push writes only at rsp - 8)
    mem-preserved-setup : ∀ addr → addr ≥ readReg (regs s) rsp → readMem (memory s-setup) addr ≡ readMem (memory s) addr
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
  -- Region proofs for rdi and rdi+8 (supports both Stack and Heap values)
  (rdi-r : Region) → InRegion rdi-r (readReg (regs s) rdi) →
  (rdi+8-r : Region) → InRegion rdi+8-r (readReg (regs s) rdi +ℕ slot-size) →
  -- Stack ownership bounds (for Stack case, from Ownership model)
  (rdi-r ≡ Stack → readReg (regs s) rdi ≥ readReg (regs s) rsp) →
  (rdi+8-r ≡ Stack → (readReg (regs s) rdi +ℕ slot-size) ≥ readReg (regs s) rsp) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  ∃[ s-setup ] CaseInlSetupResult {A} {B} {C} a prefix suffix f g s s-setup val-addr
case-inl-setup-star {A} {B} {C} f g prefix suffix a s val-addr
    h-false pc-eq tag-is-0 val-ptr-eq rdi-r rdi-in-region rdi+8-r rdi+8-in-region
    rdi-stack-bound rdi+8-stack-bound stack-inv cap rbp-inv =
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

    -- push-addr < orig-rsp (needed for Ownership-based disjointness)
    slot-size<rsp : slot-size < orig-rsp
    slot-size<rsp = rsp-sufficient cap-1

    push-addr<rsp : push-addr < orig-rsp
    push-addr<rsp = subst (push-addr <_) sum-eq push-addr<sum
      where
        slot-size≤rsp : slot-size ≤ orig-rsp
        slot-size≤rsp = <⇒≤ slot-size<rsp

        sum-eq : push-addr +ℕ slot-size ≡ orig-rsp
        sum-eq = m∸n+n≡m slot-size≤rsp

        push-addr<sum : push-addr < push-addr +ℕ slot-size
        push-addr<sum = m<m+n push-addr {slot-size} (s≤s z≤n)

    -- Disjointness: push-addr ≢ orig-rdi (region-based with Ownership for Stack)
    push-addr≢orig-rdi : push-addr ≢ orig-rdi
    push-addr≢orig-rdi = region-disjoint rdi-r rdi-in-region refl
      where
        region-disjoint : (r : Region) → InRegion r orig-rdi → rdi-r ≡ r → push-addr ≢ orig-rdi
        region-disjoint HeapAlloc ih _ = λ eq → stack-heap-addr-disjoint push-addr orig-rdi push-addr-in-stack ih eq
        region-disjoint StackAlloc _ r-eq = λ eq →
          caller-disjoint-from-current (rdi-stack-bound r-eq) push-addr<rsp (sym eq)

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

    -- Value pointer at rdi+8 is also preserved via stack/heap disjointness (region-based with Ownership for Stack)
    push-addr≢orig-rdi+8 : push-addr ≢ (orig-rdi +ℕ slot-size)
    push-addr≢orig-rdi+8 = region-disjoint rdi+8-r rdi+8-in-region refl
      where
        region-disjoint : (r : Region) → InRegion r (orig-rdi +ℕ slot-size) → rdi+8-r ≡ r → push-addr ≢ (orig-rdi +ℕ slot-size)
        region-disjoint HeapAlloc ih _ = λ eq → stack-heap-addr-disjoint push-addr (orig-rdi +ℕ slot-size) push-addr-in-stack ih eq
        region-disjoint StackAlloc _ r-eq = λ eq →
          caller-disjoint-from-current (rdi+8-stack-bound r-eq) push-addr<rsp (sym eq)

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

    -- Memory preserved at addresses ≥ entry-rsp (push writes at rsp - 8 < rsp)
    mem-preserved-6 : ∀ addr → addr ≥ orig-rsp → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-preserved-6 addr addr≥rsp = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr
      where
        -- push-addr = orig-rsp - 8 < orig-rsp ≤ addr
        push-addr<addr : push-addr < addr
        push-addr<addr = <-≤-trans push-addr<rsp addr≥rsp

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
        open import Once.Backend.X86.Layout using (slot-addr; init-slot-at-base)
        open import Data.Unit using (tt)
        open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

        -- push-addr = slot-addr new-frame 0 (slot 0 of the new frame)
        push-addr-is-slot0 : push-addr ≡ slot-addr new-frame 0
        push-addr-is-slot0 = sym (trans (init-slot-at-base new-frame) new-frame-addr)

        -- Helper to compute frame evidence by case analysis
        -- For r15-in-stack case, provides ORDERING evidence (not just ≢)
        compute-frame-evidence : (inv : R15Status s) → FrameEvidenceFor new-frame inv
        compute-frame-evidence (r15-in-heap _) = tt
        compute-frame-evidence (r15-in-code _) = tt
        compute-frame-evidence (r15-in-stack r15-frame r15-slot r15-eq r15-frame-bound) = new-frame<r15-frame
          where
            -- sp-addr new-frame = orig-rsp - slot-size
            -- sp-addr r15-frame ≥ orig-rsp (from r15-frame-bound)
            -- We prove: orig-rsp - slot-size < orig-rsp ≤ sp-addr r15-frame
            -- Therefore: sp-addr new-frame < sp-addr r15-frame (direct < evidence!)
            new-frame<r15-frame : sp-addr new-frame < sp-addr r15-frame
            new-frame<r15-frame = <-≤-trans new-frame<rsp r15-frame-bound
              where
                -- new-frame < orig-rsp (from slot-size<rsp and m∸n<m logic)
                new-frame<rsp : sp-addr new-frame < orig-rsp
                new-frame<rsp = subst (_< orig-rsp) (sym new-frame-addr) push-addr<rsp

        frame-evidence : FrameEvidenceFor new-frame stack-inv
        frame-evidence = compute-frame-evidence stack-inv

        push-addr≢r15 : push-addr ≢ orig-r15
        push-addr≢r15 = stack-write-preserves-r15 s push-addr new-frame
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
      ; mem-preserved-setup = mem-preserved-6
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
    -- Memory preserved at addresses ≥ entry-rsp (push writes only at rsp - 8)
    mem-preserved-setup : ∀ addr → addr ≥ readReg (regs s) rsp → readMem (memory s-setup) addr ≡ readMem (memory s) addr
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
  -- Region proofs for rdi and rdi+8 (supports both Stack and Heap values)
  (rdi-r : Region) → InRegion rdi-r (readReg (regs s) rdi) →
  (rdi+8-r : Region) → InRegion rdi+8-r (readReg (regs s) rdi +ℕ slot-size) →
  -- Stack ownership bounds (for Stack case, from Ownership model)
  (rdi-r ≡ Stack → readReg (regs s) rdi ≥ readReg (regs s) rsp) →
  (rdi+8-r ≡ Stack → (readReg (regs s) rdi +ℕ slot-size) ≥ readReg (regs s) rsp) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement [ f , g ]) →
  RbpInvariant s →
  ∃[ s-setup ] CaseInrSetupResult {A} {B} {C} b prefix suffix f g s s-setup val-addr
case-inr-setup-star {A} {B} {C} f g prefix suffix b s val-addr
    h-false pc-eq tag-is-1 val-ptr-eq rdi-r rdi-in-region rdi+8-r rdi+8-in-region
    rdi-stack-bound rdi+8-stack-bound stack-inv cap rbp-inv =
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

    -- push-addr < orig-rsp (needed for Ownership-based disjointness)
    slot-size<rsp : slot-size < orig-rsp
    slot-size<rsp = rsp-sufficient cap-1

    push-addr<rsp : push-addr < orig-rsp
    push-addr<rsp = subst (push-addr <_) sum-eq push-addr<sum
      where
        slot-size≤rsp : slot-size ≤ orig-rsp
        slot-size≤rsp = <⇒≤ slot-size<rsp

        sum-eq : push-addr +ℕ slot-size ≡ orig-rsp
        sum-eq = m∸n+n≡m slot-size≤rsp

        push-addr<sum : push-addr < push-addr +ℕ slot-size
        push-addr<sum = m<m+n push-addr {slot-size} (s≤s z≤n)

    push-addr≢orig-rdi : push-addr ≢ orig-rdi
    push-addr≢orig-rdi = region-disjoint rdi-r rdi-in-region refl
      where
        region-disjoint : (r : Region) → InRegion r orig-rdi → rdi-r ≡ r → push-addr ≢ orig-rdi
        region-disjoint HeapAlloc ih _ = λ eq → stack-heap-addr-disjoint push-addr orig-rdi push-addr-in-stack ih eq
        region-disjoint StackAlloc _ r-eq = λ eq →
          caller-disjoint-from-current (rdi-stack-bound r-eq) push-addr<rsp (sym eq)

    -- Tag still reads as 1 after push
    tag-still-1-s1 : readMem (memory s1) orig-rdi ≡ just 1
    tag-still-1-s1 = trans (readMem-writeMem-diff orig-mem push-addr orig-rdi orig-rbp push-addr≢orig-rdi) tag-is-1

    mem3 : readMem (memory s2) (readReg (regs s2) rdi) ≡ just 1
    mem3 = subst (λ addr → readMem (memory s2) addr ≡ just 1) (sym rdi-s2) tag-still-1-s1

    -- Value pointer preserved for step 7 (region-based with Ownership for Stack)
    push-addr≢orig-rdi+8 : push-addr ≢ (orig-rdi +ℕ slot-size)
    push-addr≢orig-rdi+8 = region-disjoint rdi+8-r rdi+8-in-region refl
      where
        region-disjoint : (r : Region) → InRegion r (orig-rdi +ℕ slot-size) → rdi+8-r ≡ r → push-addr ≢ (orig-rdi +ℕ slot-size)
        region-disjoint HeapAlloc ih _ = λ eq → stack-heap-addr-disjoint push-addr (orig-rdi +ℕ slot-size) push-addr-in-stack ih eq
        region-disjoint StackAlloc _ r-eq = λ eq →
          caller-disjoint-from-current (rdi+8-stack-bound r-eq) push-addr<rsp (sym eq)

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

    -- Memory preserved at addresses ≥ entry-rsp (push writes at rsp - 8 < rsp)
    mem-preserved-6 : ∀ addr → addr ≥ orig-rsp → readMem (memory s6) addr ≡ readMem orig-mem addr
    mem-preserved-6 addr addr≥rsp = readMem-writeMem-diff orig-mem push-addr addr orig-rbp push-addr≢addr
      where
        -- push-addr = orig-rsp - 8 < orig-rsp ≤ addr
        push-addr<addr : push-addr < addr
        push-addr<addr = <-≤-trans push-addr<rsp addr≥rsp

        push-addr≢addr : push-addr ≢ addr
        push-addr≢addr = <⇒≢ push-addr<addr

    -- Memory at r15 preserved
    mem-r15-6 : readMem (memory s6) (readReg (regs s) r15) ≡ readMem orig-mem (readReg (regs s) r15)
    mem-r15-6 = readMem-writeMem-diff orig-mem push-addr orig-r15 orig-rbp push-addr≢r15
      where
        open import Once.Backend.X86.Correct.StackInvariant
          using (stack-write-preserves-r15; FrameEvidenceFor;
                 R15Status; r15-in-heap; r15-in-code; r15-in-stack)
        open import Once.Backend.X86.Layout using (slot-addr; init-slot-at-base)
        open import Data.Unit using (tt)
        open import Data.Nat.Properties using (<⇒≢; <-≤-trans)

        push-addr-is-slot0 : push-addr ≡ slot-addr new-frame 0
        push-addr-is-slot0 = sym (trans (init-slot-at-base new-frame) new-frame-addr)

        compute-frame-evidence : (inv : R15Status s) → FrameEvidenceFor new-frame inv
        compute-frame-evidence (r15-in-heap _) = tt
        compute-frame-evidence (r15-in-code _) = tt
        compute-frame-evidence (r15-in-stack r15-frame r15-slot r15-eq r15-frame-bound) = new-frame<r15-frame
          where
            -- Direct < evidence (no conversion to ≢ needed!)
            new-frame<r15-frame : sp-addr new-frame < sp-addr r15-frame
            new-frame<r15-frame = <-≤-trans new-frame<rsp r15-frame-bound
              where
                new-frame<rsp : sp-addr new-frame < orig-rsp
                new-frame<rsp = subst (_< orig-rsp) (sym new-frame-addr) push-addr<rsp

        frame-evidence : FrameEvidenceFor new-frame stack-inv
        frame-evidence = compute-frame-evidence stack-inv

        push-addr≢r15 : push-addr ≢ orig-r15
        push-addr≢r15 = stack-write-preserves-r15 s push-addr new-frame
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
      ; mem-preserved-setup = mem-preserved-6
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

