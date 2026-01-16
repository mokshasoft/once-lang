------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Curry
--
-- Star-based curry proof.
-- Non-recursive, so can live outside the mutual block.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Curry where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
open import Once.Postulates using (encode-closure-construct)
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInstantiation
open import Once.Backend.X86.Correct.StackInstantiation
  using (rsp-bound-to-capacity; StackCapacity; capacity-after-alloc-2-slots; capacity-2-to-rsp-bound;
         alloc-2-slots-addrs-in-stack; slots-mono-≤;
         -- D041: Abstract helpers that encapsulate arithmetic
         curry-frame-disjoint-from-rbp; curry-rbp-inv-update; curry-stack-inv-frame-bound-update;
         curry-alloc-below-rbp; curry-alloc-nonzero)
open import Data.Nat.Properties using (≤-<-trans)
open import Once.Backend.Common.MemoryRegions
  using (region-of; code; heap; stack; stack-code-disjoint; stack-heap-disjoint;
         stackAddr-write-preserves-heap; slot-addr)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-at-0; ir-mem-code; ir-mem-heap; ir-closure-wf;
         IRStarResultV; ir-result-valid)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-closure-env; ClosureAtS; closure-at-s; valid-at-preserved-under-write; valid-in-heap)

open import Data.Nat using (_>_; _≥_; _<_; s≤s; z≤n)
-- D041: Arithmetic moved to abstract helpers in StackInvariant.agda
-- m≤m+n kept for simple numeric constant facts
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; m<m+n; 0<1+n; m≤m+n) renaming (<⇒≢ to Nat-<⇒≢)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- CurryMemoryResult: Memory layout produced by curry
------------------------------------------------------------------------

-- | Record capturing the memory layout produced by curry
-- This is what apply needs to look up the closure
record CurryMemoryResult {A B C : Type} (f : IR (A * B) C)
                         (prog : Program) (s-final : State)
                         (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
  field
    closure-addr : ℕ
    code-ptr : ℕ
    env-addr : ℕ
    -- rax holds the closure address
    rax-eq : readReg (regs s-final) rax ≡ closure-addr
    -- Memory layout of the closure
    mem-env : readMem (memory s-final) closure-addr ≡ just env-addr
    mem-cp : readMem (memory s-final) (closure-addr +ℕ slot-size) ≡ just code-ptr
    -- Env validity (replaces env-is-encoded : env-addr ≡ encode x)
    v-env : ValidAt x env-addr (memory s-final)
    code-ptr-is-thunk : code-ptr ≡ offset +ℕ 6

open CurryMemoryResult public

------------------------------------------------------------------------
-- CurryExecResult: Execution result without encode-based ir-rax
------------------------------------------------------------------------

-- | Curry execution result - all fields except ir-rax
-- This avoids computing encode equality, keeping curry validity-based.
-- ir-rax is not needed because run-curry-star-v computes validity directly.
record CurryExecResult {A B C : Type} (f : IR (A * B) C)
                       (prog : Program) (s s' : State)
                       (x : ⟦ A ⟧) (offset : ℕ) : Set₁ where
  field
    exec-star : Star prog s s'
    exec-halted : halted s' ≡ false
    exec-pc : pc s' ≡ offset +ℕ compile-length (curry f)
    exec-r14 : readReg (regs s') r14 ≡ readReg (regs s) r14
    exec-r15 : readReg (regs s') r15 ≡ readReg (regs s) r15
    exec-rbp : readReg (regs s') rbp ≡ readReg (regs s) rbp
    exec-mem : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    exec-mem-rbp : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    exec-mem-rbp+8 : readMem (memory s') (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
    exec-stack-inv : StackInvariant s'
    exec-capacity : StackCapacity s' 2
    exec-rbp-inv : RbpInvariant s'
    exec-mem-above : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    exec-mem-at-0 : readMem (memory s') 0 ≡ readMem (memory s) 0
    exec-mem-code : ∀ addr → region-of addr ≡ code → readMem (memory s') addr ≡ readMem (memory s) addr
    exec-mem-heap : ∀ addr → region-of addr ≡ heap → readMem (memory s') addr ≡ readMem (memory s) addr

open CurryExecResult public

------------------------------------------------------------------------
-- Main curry proof (validity-based, no encode)
------------------------------------------------------------------------

-- | Main curry proof (takes StackCapacity s 4 directly to eliminate postulate usage)
-- Curry allocates 2 slots, so we need 4 to guarantee output capacity of 2
run-curry-star : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s 4 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in ∃[ s' ] (CurryExecResult f prog s s' x (length prefix)
             × CurryMemoryResult f prog s' x (length prefix))
run-curry-star {A} {B} {C} f prefix suffix x s h-false pc-eq input-valid stack-inv cap rbp-inv =
  s-final , record
    { exec-star = star-all
    ; exec-halted = h-final
    ; exec-pc = pc-final
    ; exec-r14 = r14-final
    ; exec-r15 = r15-final
    ; exec-rbp = rbp-final
    ; exec-mem = mem-final
    ; exec-mem-rbp = mem-rbp-final
    ; exec-mem-rbp+8 = mem-rbp+8-final
    ; exec-stack-inv = stack-inv-final
    ; exec-capacity = output-capacity
    ; exec-rbp-inv = rbp-inv-final
    ; exec-mem-above = mem-above-final
    ; exec-mem-at-0 = mem-at-0-final
    ; exec-mem-code = mem-code-final
    ; exec-mem-heap = mem-heap-final
    } , record
    { closure-addr = new-rsp
    ; code-ptr = thunk-offset
    ; env-addr = orig-rdi
    ; rax-eq = rax-s7
    ; mem-env = mem-at-new-rsp-final
    ; mem-cp = mem-code-ptr-final
    ; v-env = v-env-final
    ; code-ptr-is-thunk = refl
    }
  where
    len-f = compile-length f
    prog = prefix ++ compile-x86 (curry f) ++ suffix

    -- Derive rsp bound from StackCapacity (no postulate needed!)
    2≤4 : 2 ≤ 4
    2≤4 = s≤s (s≤s z≤n)

    rsp-bound : readReg (regs s) rsp > slots 2
    rsp-bound = ≤-<-trans (slots-mono-≤ 2≤4) (StackCapacity.rsp-sufficient cap)

    rsp-region : region-of (readReg (regs s) rsp) ≡ stack
    rsp-region = StackCapacity.rsp-in-stack cap

    cap2 : StackCapacity s 2
    cap2 = rsp-bound-to-capacity 2 s rsp-region rsp-bound

    -- Track original rdi (env address from input)
    orig-rdi : ℕ
    orig-rdi = readReg (regs s) rdi

    -- Key offsets (matching CodeGen.agda layout)
    -- jmp at pos 5 needs to reach end-label at pos 18+len-f
    -- offset = target - (pc + 1) = (18+len-f) - 6 = 12+len-f
    jmp-offset : ℕ
    jmp-offset = 12 +ℕ len-f

    end-label-pos : ℕ
    end-label-pos = 18 +ℕ len-f

    -- Helper values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    new-rsp : Word
    new-rsp = orig-rsp ∸ slots 2

    -- The 7 instructions that actually execute
    i0 : Instr
    i0 = sub (reg rsp) (imm (slots 2))

    i1 : Instr
    i1 = mov (mem (base rsp)) (reg rdi)

    i2 : Instr
    i2 = lea r9 (rip+disp 4)

    i3 : Instr
    i3 = mov (mem (base+disp rsp 8)) (reg r9)

    i4 : Instr
    i4 = mov (reg rax) (reg rsp)

    i5 : Instr
    i5 = jmp jmp-offset

    i6-label : Instr
    i6-label = label end-label-pos

    -- State after step 0: sub rsp, 16
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; pc = pc s +ℕ 1
                  ; flags = updateFlags new-rsp orig-rsp }

    -- State after step 1: mov [rsp], rdi
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (readReg (regs s1) rsp) (readReg (regs s1) rdi)
                   ; pc = pc s1 +ℕ 1 }

    -- State after step 2: lea r9, [rip+4]
    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) r9 (effectiveAddr s2 (rip+disp 4))
                   ; pc = pc s2 +ℕ 1 }

    -- State after step 3: mov [rsp+8], r9
    s4 : State
    s4 = record s3 { memory = writeMem (memory s3) (readReg (regs s3) rsp +ℕ slot-size) (readReg (regs s3) r9)
                   ; pc = pc s3 +ℕ 1 }

    -- State after step 4: mov rax, rsp
    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) rax (readReg (regs s4) rsp)
                   ; pc = pc s4 +ℕ 1 }

    -- State after step 5: jmp jmp-offset
    s6 : State
    s6 = record s5 { pc = pc s5 +ℕ 1 +ℕ jmp-offset }

    -- State after step 6: label end-label-pos
    s7 : State
    s7 = record s6 { pc = pc s6 +ℕ 1 }

    -- Fetch lemmas
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 _

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) _)

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1
                    (fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 _)

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ _
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) _)

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 _)

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ _
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) _)

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = List-length-++ prefix

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 _)

    prog-eq4 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) ++ _
    prog-eq4 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) _)

    len-prefix-4 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) ≡ length prefix +ℕ 4
    len-prefix-4 = List-length-++ prefix

    fetch4 : fetch prog (length prefix +ℕ 4) ≡ just i4
    fetch4 = subst₂ (λ p n → fetch p n ≡ just i4) (sym prog-eq4) len-prefix-4
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) i4 _)

    prog-eq5 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) ++ _
    prog-eq5 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) _)

    len-prefix-5 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) ≡ length prefix +ℕ 5
    len-prefix-5 = List-length-++ prefix

    fetch5 : fetch prog (length prefix +ℕ 5) ≡ just i5
    fetch5 = subst₂ (λ p n → fetch p n ≡ just i5) (sym prog-eq5) len-prefix-5
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) i5 _)

    -- For the label, we need fetch at pc s6 = prefix + 18 + len-f
    -- New layout with frame pointer and r15 save/restore:
    -- 6 setup + 1 label + 1 push-r15 + 2 frame setup + 4 thunk setup + |f| + 4 cleanup = 18 + |f|
    curry-before-end-label : Program
    curry-before-end-label =
      i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷  -- 6 closure setup instructions
      label 6 ∷                        -- thunk entry
      push (reg r15) ∷                 -- save r15 (apply uses it as scratch)
      push (reg rbp) ∷                 -- save frame pointer
      mov (reg rbp) (reg rsp) ∷        -- set frame pointer
      sub (reg rsp) (imm (slots 2)) ∷         -- allocate pair
      mov (mem (base rsp)) (reg r12) ∷
      mov (mem (base+disp rsp 8)) (reg rdi) ∷
      mov (reg rdi) (reg rsp) ∷
      compile-x86 f ++                 -- inner function
      mov (reg rsp) (reg rbp) ∷        -- restore stack
      pop rbp ∷                        -- restore frame pointer
      pop r15 ∷                        -- restore r15
      ret ∷ []                         -- return

    len-curry-before : length curry-before-end-label ≡ end-label-pos
    len-curry-before = begin
      length curry-before-end-label
        ≡⟨ refl ⟩
      length (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷
              label 6 ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
              sub (reg rsp) (imm (slots 2)) ∷
              mov (mem (base rsp)) (reg r12) ∷
              mov (mem (base+disp rsp 8)) (reg rdi) ∷
              mov (reg rdi) (reg rsp) ∷
              compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ [])
        ≡⟨ refl ⟩
      14 +ℕ length (compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ [])
        ≡⟨ cong (14 +ℕ_) (List-length-++ (compile-x86 f)) ⟩
      14 +ℕ (length (compile-x86 f) +ℕ 4)
        ≡⟨ cong (λ z → 14 +ℕ (z +ℕ 4)) (compile-length-correct f) ⟩
      14 +ℕ (len-f +ℕ 4)
        ≡⟨ +-assoc 14 len-f 4 ⟩
      (14 +ℕ len-f) +ℕ 4
        ≡⟨ cong (_+ℕ 4) (+-comm 14 len-f) ⟩
      (len-f +ℕ 14) +ℕ 4
        ≡⟨ +-assoc len-f 14 4 ⟩
      len-f +ℕ 18
        ≡⟨ +-comm len-f 18 ⟩
      end-label-pos
        ∎

    curry-code-inner : Program
    curry-code-inner = compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ i6-label ∷ []

    curry-inner-split : curry-code-inner ≡ (compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ []) ++ i6-label ∷ []
    curry-inner-split = sym (++-assoc (compile-x86 f) (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ pop r15 ∷ ret ∷ []) (i6-label ∷ []))

    curry-split : compile-x86 (curry f) ≡ curry-before-end-label ++ i6-label ∷ []
    curry-split = cong (λ rest → i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷
                                 label 6 ∷ push (reg r15) ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
                                 sub (reg rsp) (imm (slots 2)) ∷
                                 mov (mem (base rsp)) (reg r12) ∷
                                 mov (mem (base+disp rsp 8)) (reg rdi) ∷
                                 mov (reg rdi) (reg rsp) ∷ rest) curry-inner-split

    prefix-to-end : Program
    prefix-to-end = prefix ++ curry-before-end-label

    len-prefix-to-end : length prefix-to-end ≡ length prefix +ℕ end-label-pos
    len-prefix-to-end = trans (List-length-++ prefix)
                              (cong (length prefix +ℕ_) len-curry-before)

    prog-eq-for-fetch6 : prog ≡ prefix-to-end ++ i6-label ∷ suffix
    prog-eq-for-fetch6 = begin
      prog
        ≡⟨ refl ⟩
      prefix ++ compile-x86 (curry f) ++ suffix
        ≡⟨ cong (λ z → prefix ++ z ++ suffix) curry-split ⟩
      prefix ++ (curry-before-end-label ++ i6-label ∷ []) ++ suffix
        ≡⟨ cong (prefix ++_) (++-assoc curry-before-end-label (i6-label ∷ []) suffix) ⟩
      prefix ++ curry-before-end-label ++ (i6-label ∷ [] ++ suffix)
        ≡⟨ sym (++-assoc prefix curry-before-end-label (i6-label ∷ suffix)) ⟩
      (prefix ++ curry-before-end-label) ++ i6-label ∷ suffix
        ≡⟨ refl ⟩
      prefix-to-end ++ i6-label ∷ suffix
        ∎

    fetch6 : fetch prog (length prefix +ℕ end-label-pos) ≡ just i6-label
    fetch6 = subst₂ (λ p n → fetch p n ≡ just i6-label) (sym prog-eq-for-fetch6) len-prefix-to-end
                    (fetch-at-prefix-end prefix-to-end i6-label suffix)

    -- Step proofs
    step0 : step prog s ≡ just s1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execSub-reg-imm prog s rsp 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    step1 : step prog s1 ≡ just s2
    step1 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execMov-mem-base-reg prog s1 rsp rdi)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    step2 : step prog s2 ≡ just s3
    step2 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execLea prog s2 r9 (rip+disp 4))

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step3 : step prog s3 ≡ just s4
    step3 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-mem-disp-reg prog s3 rsp r9 8)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    step4 : step prog s4 ≡ just s5
    step4 = trans (step-exec prog s4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (execMov-reg-reg s4 rax rsp)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (λ p → p +ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    step5 : step prog s5 ≡ just s6
    step5 = trans (step-exec prog s5 i5 h5 (subst (λ p → fetch prog p ≡ just i5) (sym pc5) fetch5))
                  (execJmp prog s5 jmp-offset)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6-correct : pc s6 ≡ length prefix +ℕ end-label-pos
    pc6-correct = begin
      pc s6
        ≡⟨ refl ⟩
      pc s5 +ℕ 1 +ℕ jmp-offset
        ≡⟨ cong (λ z → z +ℕ 1 +ℕ jmp-offset) pc5 ⟩
      (length prefix +ℕ 5) +ℕ 1 +ℕ jmp-offset
        ≡⟨ cong (_+ℕ jmp-offset) (+-assoc (length prefix) 5 1) ⟩
      (length prefix +ℕ 6) +ℕ jmp-offset
        ≡⟨ +-assoc (length prefix) 6 jmp-offset ⟩
      length prefix +ℕ (6 +ℕ jmp-offset)
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 6 12 len-f)) ⟩
      length prefix +ℕ ((6 +ℕ 12) +ℕ len-f)
        ≡⟨ cong (length prefix +ℕ_) refl ⟩
      length prefix +ℕ end-label-pos
        ∎

    step6 : step prog s6 ≡ just s7
    step6 = trans (step-exec prog s6 i6-label h6 (subst (λ p → fetch prog p ≡ just i6-label) (sym pc6-correct) fetch6))
                  (execLabel prog s6 end-label-pos)

    h7 : halted s7 ≡ false
    h7 = h-false

    pc7 : pc s7 ≡ length prefix +ℕ compile-length (curry f)
    pc7 = begin
      pc s7
        ≡⟨ refl ⟩
      pc s6 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc6-correct ⟩
      (length prefix +ℕ end-label-pos) +ℕ 1
        ≡⟨ +-assoc (length prefix) end-label-pos 1 ⟩
      length prefix +ℕ (end-label-pos +ℕ 1)
        ≡⟨ cong (length prefix +ℕ_) (+-comm end-label-pos 1) ⟩
      length prefix +ℕ (1 +ℕ end-label-pos)
        ≡⟨ cong (length prefix +ℕ_) refl ⟩
      length prefix +ℕ (19 +ℕ len-f)
        ≡⟨ refl ⟩
      length prefix +ℕ compile-length (curry f)
        ∎

    -- Build Star using combinators
    star-all : Star prog s s7
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               ⟨ h5 , step5 ⟩◅
               ⟨ h6 , step6 ⟩◅
               refl*

    -- Final state is s7
    s-final : State
    s-final = s7

    h-final : halted s-final ≡ false
    h-final = h7

    pc-final : pc s-final ≡ length prefix +ℕ compile-length (curry f)
    pc-final = pc7

    -- Register preservation through states
    r14-s1 : readReg (regs s1) r14 ≡ readReg (regs s) r14
    r14-s1 = readReg-writeReg-rsp-r14 (regs s) new-rsp

    r14-final : readReg (regs s-final) r14 ≡ readReg (regs s) r14
    r14-final = r14-s1

    r15-s1 : readReg (regs s1) r15 ≡ readReg (regs s) r15
    r15-s1 = readReg-writeReg-rsp-r15 (regs s) new-rsp

    r15-final : readReg (regs s-final) r15 ≡ readReg (regs s) r15
    r15-final = r15-s1

    rbp-s1 : readReg (regs s1) rbp ≡ readReg (regs s) rbp
    rbp-s1 = readReg-writeReg-rsp-rbp (regs s) new-rsp

    rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s) rbp
    rbp-final = rbp-s1

    -- rsp tracking through states
    rsp-s1 : readReg (regs s1) rsp ≡ new-rsp
    rsp-s1 = readReg-writeReg-same (regs s) rsp new-rsp

    -- s2 = mov [rsp], rdi - memory write doesn't change registers
    rsp-s2 : readReg (regs s2) rsp ≡ new-rsp
    rsp-s2 = rsp-s1

    -- s3 = lea r9, [rip+4] - only changes r9, not rsp
    rsp-s3 : readReg (regs s3) rsp ≡ new-rsp
    rsp-s3 = trans (readReg-writeReg-r9-rsp (regs s2) (effectiveAddr s2 (rip+disp 4))) rsp-s2

    rsp-s7 : readReg (regs s7) rsp ≡ new-rsp
    rsp-s7 = rsp-s1

    -- rax in s5 = rsp = new-rsp
    rax-s7 : readReg (regs s7) rax ≡ new-rsp
    rax-s7 = readReg-writeReg-same (regs s4) rax (readReg (regs s4) rsp)

    -- Show memory at new-rsp contains orig-rdi (the env address)
    -- s2 writes (readReg (regs s1) rdi) to (readReg (regs s1) rsp) = new-rsp
    -- s4 writes to rsp+8, not rsp, so new-rsp is unchanged
    rdi-s1 : readReg (regs s1) rdi ≡ orig-rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    mem-at-new-rsp-s2 : readMem (memory s2) new-rsp ≡ just orig-rdi
    mem-at-new-rsp-s2 = trans (readMem-writeMem-same (memory s1) (readReg (regs s1) rsp) (readReg (regs s1) rdi))
                              (cong just (trans (cong (λ addr → readReg (regs s1) rdi) (sym rsp-s1)) rdi-s1))

    -- s3 doesn't modify memory
    mem-at-new-rsp-s3 : readMem (memory s3) new-rsp ≡ just orig-rdi
    mem-at-new-rsp-s3 = mem-at-new-rsp-s2

    -- s4 writes to rsp+8, not new-rsp
    -- Need to show new-rsp ≢ new-rsp + 8
    -- Proof: new-rsp < new-rsp + 8 (since 8 > 0), therefore new-rsp ≢ new-rsp + 8
    new-rsp≢new-rsp+8 : new-rsp ≢ new-rsp +ℕ slot-size
    new-rsp≢new-rsp+8 = Nat-<⇒≢ (m<m+n new-rsp 0<1+n)

    mem-at-new-rsp-s4 : readMem (memory s4) new-rsp ≡ just orig-rdi
    mem-at-new-rsp-s4 = trans (readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) new-rsp
                                (readReg (regs s3) r9)
                                (subst (λ addr → addr +ℕ slot-size ≢ new-rsp) (sym rsp-s3) (λ eq → new-rsp≢new-rsp+8 (sym eq))))
                              mem-at-new-rsp-s3

    -- s5, s6, s7 don't modify memory
    mem-at-new-rsp-final : readMem (memory s-final) new-rsp ≡ just orig-rdi
    mem-at-new-rsp-final = mem-at-new-rsp-s4

    -- ============================================================
    -- Env validity tracking (no bridges in this section)
    -- ============================================================
    -- input-valid : ValidAt x orig-rdi (memory s)
    -- Curry writes to stack (new-rsp and new-rsp+8), not heap
    -- orig-rdi is in heap (from input validity), so validity is preserved

    -- orig-rdi is in heap (from input validity)
    orig-rdi-in-heap : region-of orig-rdi ≡ heap
    orig-rdi-in-heap = valid-in-heap input-valid

    -- s2 writes to new-rsp (stack), not orig-rdi (heap)
    new-rsp-in-stack : region-of new-rsp ≡ stack
    new-rsp-in-stack = proj₁ (alloc-2-slots-addrs-in-stack s cap2)

    orig-rdi≢new-rsp : orig-rdi ≢ new-rsp
    orig-rdi≢new-rsp eq = stack-heap-disjoint new-rsp orig-rdi new-rsp-in-stack orig-rdi-in-heap (sym eq)

    v-env-s2 : ValidAt x orig-rdi (memory s2)
    v-env-s2 = valid-at-preserved-under-write input-valid orig-rdi≢new-rsp

    -- s3 doesn't modify memory
    v-env-s3 : ValidAt x orig-rdi (memory s3)
    v-env-s3 = v-env-s2

    -- s4 writes to new-rsp+8 (stack), not orig-rdi (heap)
    new-rsp+8-in-stack : region-of (new-rsp +ℕ slot-size) ≡ stack
    new-rsp+8-in-stack = proj₂ (alloc-2-slots-addrs-in-stack s cap2)

    orig-rdi≢new-rsp+8 : orig-rdi ≢ new-rsp +ℕ slot-size
    orig-rdi≢new-rsp+8 eq = stack-heap-disjoint (new-rsp +ℕ slot-size) orig-rdi new-rsp+8-in-stack orig-rdi-in-heap (sym eq)

    v-env-s4 : ValidAt x orig-rdi (memory s4)
    v-env-s4 = valid-at-preserved-under-write v-env-s3 orig-rdi≢new-rsp+8

    -- s5, s6, s7 don't modify memory
    v-env-final : ValidAt x orig-rdi (memory s-final)
    v-env-final = v-env-s4

    -- Thunk offset: the code-ptr stored in the closure
    -- The thunk entry label is at index 6 within curry's compiled code
    thunk-offset : ℕ
    thunk-offset = length prefix +ℕ 6

    -- effectiveAddr s2 (rip+disp 4) = pc s2 + 4 = (length prefix + 2) + 4 = length prefix + 6
    r9-value : effectiveAddr s2 (rip+disp 4) ≡ thunk-offset
    r9-value = begin
      effectiveAddr s2 (rip+disp 4)
        ≡⟨ refl ⟩  -- by definition of effectiveAddr for rip+disp
      pc s2 +ℕ 4
        ≡⟨ cong (_+ℕ 4) pc2 ⟩
      (length prefix +ℕ 2) +ℕ 4
        ≡⟨ +-assoc (length prefix) 2 4 ⟩
      length prefix +ℕ 6
        ≡⟨ refl ⟩
      thunk-offset
        ∎

    -- r9 in s3 contains the thunk offset
    r9-s3 : readReg (regs s3) r9 ≡ thunk-offset
    r9-s3 = trans (readReg-writeReg-same (regs s2) r9 (effectiveAddr s2 (rip+disp 4))) r9-value

    -- s4 writes r9 to [rsp+8], so memory at new-rsp+8 = thunk-offset
    mem-code-ptr-s4 : readMem (memory s4) (new-rsp +ℕ slot-size) ≡ just thunk-offset
    mem-code-ptr-s4 =
      let rsp-eq : readReg (regs s3) rsp ≡ new-rsp
          rsp-eq = rsp-s3
          write-addr = readReg (regs s3) rsp +ℕ slot-size
          write-addr-eq : write-addr ≡ new-rsp +ℕ slot-size
          write-addr-eq = cong (_+ℕ slot-size) rsp-eq
      in trans (subst (λ addr → readMem (writeMem (memory s3) write-addr (readReg (regs s3) r9)) addr ≡
                                just (readReg (regs s3) r9))
                      write-addr-eq
                      (readMem-writeMem-same (memory s3) write-addr (readReg (regs s3) r9)))
               (cong just r9-s3)

    -- s5, s6, s7 don't modify memory, so code-ptr persists
    mem-code-ptr-final : readMem (memory s-final) (new-rsp +ℕ slot-size) ≡ just thunk-offset
    mem-code-ptr-final = mem-code-ptr-s4

    -- Memory preservation
    orig-r15 : Word
    orig-r15 = readReg (regs s) r15

    addr-diff : (new-rsp ≢ orig-r15) × ((new-rsp +ℕ slot-size) ≢ orig-r15)
    addr-diff = addr-diff-from-invariant s stack-inv rsp-region rsp-bound

    mem-s1-eq : readMem (memory s1) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s1-eq = refl

    mem-s2-eq : readMem (memory s2) orig-r15 ≡ readMem (memory s1) orig-r15
    mem-s2-eq = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) orig-r15
                  (readReg (regs s1) rdi) (subst (λ addr → addr ≢ orig-r15) (sym rsp-s1) (proj₁ addr-diff))

    mem-s3-eq : readMem (memory s3) orig-r15 ≡ readMem (memory s2) orig-r15
    mem-s3-eq = refl

    mem-s4-eq : readMem (memory s4) orig-r15 ≡ readMem (memory s3) orig-r15
    mem-s4-eq = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) orig-r15
                  (readReg (regs s3) r9)
                  (subst (λ addr → addr +ℕ slot-size ≢ orig-r15) (sym rsp-s3) (proj₂ addr-diff))

    mem-s5-eq : readMem (memory s5) orig-r15 ≡ readMem (memory s4) orig-r15
    mem-s5-eq = refl

    mem-s6-eq : readMem (memory s6) orig-r15 ≡ readMem (memory s5) orig-r15
    mem-s6-eq = refl

    mem-s7-eq : readMem (memory s7) orig-r15 ≡ readMem (memory s6) orig-r15
    mem-s7-eq = refl

    mem-final : readMem (memory s-final) (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-final = trans mem-s7-eq (trans mem-s6-eq (trans mem-s5-eq (trans mem-s4-eq
                  (trans mem-s3-eq (trans mem-s2-eq mem-s1-eq)))))

    -- Memory at rbp and rbp+8 preservation
    -- D041: Use abstract helper that encapsulates arithmetic
    orig-rbp : Word
    orig-rbp = readReg (regs s) rbp

    -- D041: All rbp/rbp+8 disjointness proofs via abstract helper
    rbp-diffs : (new-rsp ≢ orig-rbp) × ((new-rsp +ℕ slot-size) ≢ orig-rbp) ×
                (new-rsp ≢ orig-rbp +ℕ slot-size) × ((new-rsp +ℕ slot-size) ≢ orig-rbp +ℕ slot-size)
    rbp-diffs = curry-frame-disjoint-from-rbp s rbp-inv rsp-bound

    -- D041: Ordering facts for mem-above-final transitivity
    rbp-orders : (new-rsp < orig-rbp) × ((new-rsp +ℕ slot-size) < orig-rbp)
    rbp-orders = curry-alloc-below-rbp s rbp-inv rsp-bound

    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = proj₁ rbp-orders

    new-rsp+8<rbp : (new-rsp +ℕ slot-size) < orig-rbp
    new-rsp+8<rbp = proj₂ rbp-orders

    rbp-diff-1 : new-rsp ≢ orig-rbp
    rbp-diff-1 = proj₁ rbp-diffs

    rbp-diff-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp
    rbp-diff-2 = proj₁ (proj₂ rbp-diffs)

    -- Chain memory preservation through all states
    mem-rbp-s1 : readMem (memory s1) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-rbp-s1 = refl

    mem-rbp-s2 : readMem (memory s2) orig-rbp ≡ readMem (memory s1) orig-rbp
    mem-rbp-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) orig-rbp
                   (readReg (regs s1) rdi) (subst (λ addr → addr ≢ orig-rbp) (sym rsp-s1) rbp-diff-1)

    mem-rbp-s3 : readMem (memory s3) orig-rbp ≡ readMem (memory s2) orig-rbp
    mem-rbp-s3 = refl

    mem-rbp-s4 : readMem (memory s4) orig-rbp ≡ readMem (memory s3) orig-rbp
    mem-rbp-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) orig-rbp
                   (readReg (regs s3) r9)
                   (subst (λ addr → addr +ℕ slot-size ≢ orig-rbp) (sym rsp-s3) rbp-diff-2)

    mem-rbp-s5 : readMem (memory s5) orig-rbp ≡ readMem (memory s4) orig-rbp
    mem-rbp-s5 = refl

    mem-rbp-s6 : readMem (memory s6) orig-rbp ≡ readMem (memory s5) orig-rbp
    mem-rbp-s6 = refl

    mem-rbp-s7 : readMem (memory s7) orig-rbp ≡ readMem (memory s6) orig-rbp
    mem-rbp-s7 = refl

    mem-rbp-final : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp-final = trans mem-rbp-s7 (trans mem-rbp-s6 (trans mem-rbp-s5 (trans mem-rbp-s4
                      (trans mem-rbp-s3 (trans mem-rbp-s2 mem-rbp-s1)))))

    -- Similarly for rbp+8 (D041: extracted from abstract helper)
    orig-rbp+8 : Word
    orig-rbp+8 = readReg (regs s) rbp +ℕ slot-size

    rbp+8-diff-1 : new-rsp ≢ orig-rbp+8
    rbp+8-diff-1 = proj₁ (proj₂ (proj₂ rbp-diffs))

    rbp+8-diff-2 : (new-rsp +ℕ slot-size) ≢ orig-rbp+8
    rbp+8-diff-2 = proj₂ (proj₂ (proj₂ rbp-diffs))

    mem-rbp+8-s1 : readMem (memory s1) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-rbp+8-s1 = refl

    mem-rbp+8-s2 : readMem (memory s2) orig-rbp+8 ≡ readMem (memory s1) orig-rbp+8
    mem-rbp+8-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) orig-rbp+8
                     (readReg (regs s1) rdi) (subst (λ addr → addr ≢ orig-rbp+8) (sym rsp-s1) rbp+8-diff-1)

    mem-rbp+8-s3 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s2) orig-rbp+8
    mem-rbp+8-s3 = refl

    mem-rbp+8-s4 : readMem (memory s4) orig-rbp+8 ≡ readMem (memory s3) orig-rbp+8
    mem-rbp+8-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) orig-rbp+8
                     (readReg (regs s3) r9)
                     (subst (λ addr → addr +ℕ slot-size ≢ orig-rbp+8) (sym rsp-s3) rbp+8-diff-2)

    mem-rbp+8-s5 : readMem (memory s5) orig-rbp+8 ≡ readMem (memory s4) orig-rbp+8
    mem-rbp+8-s5 = refl

    mem-rbp+8-s6 : readMem (memory s6) orig-rbp+8 ≡ readMem (memory s5) orig-rbp+8
    mem-rbp+8-s6 = refl

    mem-rbp+8-s7 : readMem (memory s7) orig-rbp+8 ≡ readMem (memory s6) orig-rbp+8
    mem-rbp+8-s7 = refl

    mem-rbp+8-final : readMem (memory s-final) (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
    mem-rbp+8-final = trans mem-rbp+8-s7 (trans mem-rbp+8-s6 (trans mem-rbp+8-s5 (trans mem-rbp+8-s4
                        (trans mem-rbp+8-s3 (trans mem-rbp+8-s2 mem-rbp+8-s1)))))

    -- StackInvariant preservation (region-based)
    stack-inv-helper : StackInvariant s → StackInvariant s-final
    stack-inv-helper (r15-unused r15≡0) = r15-unused (trans r15-final r15≡0)
    stack-inv-helper (r15-in-heap r15-heap) =
      r15-in-heap (trans (cong region-of r15-final) r15-heap)
    stack-inv-helper (r15-in-code r15-code) =
      r15-in-code (trans (cong region-of r15-final) r15-code)
    stack-inv-helper (r15-in-stack frame slot r15-eq frame-bound) =
      r15-in-stack frame slot r15-eq' frame-bound'
      where
        -- r15-eq': s-final.r15 ≡ slot-addr frame slot
        -- from r15-final : s-final.r15 ≡ s.r15 and r15-eq : s.r15 ≡ slot-addr frame slot
        r15-eq' : readReg (regs s-final) r15 ≡ slot-addr frame slot
        r15-eq' = trans r15-final r15-eq
        -- frame-bound': D041 abstract helper encapsulates arithmetic
        frame-bound' : sp-addr frame ≥ readReg (regs s-final) rsp
        frame-bound' = curry-stack-inv-frame-bound-update s s-final rsp-s7 frame frame-bound

    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-helper stack-inv

    -- Clean capacity derivation via capacity-after-alloc-2-slots
    rsp-change : readReg (regs s-final) rsp ≡ readReg (regs s) rsp ∸ slots 2
    rsp-change = rsp-s7

    -- Use input cap directly (no postulate needed!)
    output-capacity : StackCapacity s-final 2
    output-capacity = capacity-after-alloc-2-slots s s-final 2 cap rsp-change

    rsp-sufficient-final : readReg (regs s-final) rsp > slots 2
    rsp-sufficient-final = capacity-2-to-rsp-bound s-final output-capacity

    -- RbpInvariant preservation: D041 abstract helper encapsulates arithmetic
    rbp-inv-final : RbpInvariant s-final
    rbp-inv-final = curry-rbp-inv-update s s-final rbp-inv rbp-final rsp-s7

    -- Memory above rbp preserved through all states
    -- Curry writes only at new-rsp (s2) and new-rsp+8 (s4), both < rbp
    mem-above-final : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-above-final addr addr>rbp =
      let -- new-rsp < rbp < addr, so new-rsp ≢ addr
          addr>new-rsp : addr > new-rsp
          addr>new-rsp = <-trans new-rsp<rbp addr>rbp
          diff-new-rsp : new-rsp ≢ addr
          diff-new-rsp = Nat-<⇒≢ addr>new-rsp
          -- new-rsp+8 < rbp < addr, so (new-rsp+8) ≢ addr
          addr>new-rsp+8 : addr > (new-rsp +ℕ slot-size)
          addr>new-rsp+8 = <-trans new-rsp+8<rbp addr>rbp
          diff-new-rsp+8 : (new-rsp +ℕ slot-size) ≢ addr
          diff-new-rsp+8 = Nat-<⇒≢ addr>new-rsp+8
          -- Chain through all states
          -- s1: no memory change
          mem-s1 : readMem (memory s1) addr ≡ readMem (memory s) addr
          mem-s1 = refl
          -- s2: writes at new-rsp (rsp s1 = new-rsp), but addr ≢ new-rsp
          mem-s2 : readMem (memory s2) addr ≡ readMem (memory s1) addr
          mem-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) addr
                     (readReg (regs s1) rdi) (subst (λ x → x ≢ addr) (sym rsp-s1) diff-new-rsp)
          -- s3: no memory change
          mem-s3 : readMem (memory s3) addr ≡ readMem (memory s2) addr
          mem-s3 = refl
          -- s4: writes at new-rsp+8 (rsp s3 = new-rsp), but addr ≢ new-rsp+8
          mem-s4 : readMem (memory s4) addr ≡ readMem (memory s3) addr
          mem-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) addr
                     (readReg (regs s3) r9) (subst (λ x → (x +ℕ slot-size) ≢ addr) (sym rsp-s3) diff-new-rsp+8)
          -- s5, s6, s7: no memory changes
          mem-s5 : readMem (memory s5) addr ≡ readMem (memory s4) addr
          mem-s5 = refl
          mem-s6 : readMem (memory s6) addr ≡ readMem (memory s5) addr
          mem-s6 = refl
          mem-s7 : readMem (memory s7) addr ≡ readMem (memory s6) addr
          mem-s7 = refl
      in trans mem-s7 (trans mem-s6 (trans mem-s5 (trans mem-s4 (trans mem-s3 (trans mem-s2 mem-s1)))))

    -- Memory at 0 preserved through all states
    -- D041: Use abstract helper for nonzero proofs
    mem-at-0-final : readMem (memory s-final) 0 ≡ readMem (memory s) 0
    mem-at-0-final =
      let -- D041: Abstract helper provides nonzero proofs
          alloc-nonzero = curry-alloc-nonzero s rsp-bound
          diff-new-rsp : new-rsp ≢ 0
          diff-new-rsp = proj₁ alloc-nonzero
          diff-new-rsp+8 : (new-rsp +ℕ slot-size) ≢ 0
          diff-new-rsp+8 = proj₂ alloc-nonzero
          -- Chain through all states
          mem-s2 : readMem (memory s2) 0 ≡ readMem (memory s) 0
          mem-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) 0
                     (readReg (regs s1) rdi) (subst (λ x → x ≢ 0) (sym rsp-s1) diff-new-rsp)
          mem-s4 : readMem (memory s4) 0 ≡ readMem (memory s2) 0
          mem-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) 0
                     (readReg (regs s3) r9) (subst (λ x → (x +ℕ slot-size) ≢ 0) (sym rsp-s3) diff-new-rsp+8)
      in trans mem-s4 mem-s2

    -- D041: Memory at code-region addresses preserved (PURE REGION APPROACH)
    -- 1. Get region membership for both write addresses (encapsulates arithmetic)
    -- 2. Use stack-code-disjoint to prove write ≠ code address
    -- 3. Chain readMem-writeMem-diff
    -- NO ARITHMETIC COMPARISONS at this level
    mem-code-final : ∀ addr → region-of addr ≡ code → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-code-final addr addr-in-code =
      let -- Step 1: Region membership (arithmetic encapsulated in infrastructure)
          writes-in-stack : (region-of new-rsp ≡ stack) × (region-of (new-rsp +ℕ slot-size) ≡ stack)
          writes-in-stack = alloc-2-slots-addrs-in-stack s cap2

          new-rsp-in-stack : region-of new-rsp ≡ stack
          new-rsp-in-stack = proj₁ writes-in-stack

          new-rsp+8-in-stack : region-of (new-rsp +ℕ slot-size) ≡ stack
          new-rsp+8-in-stack = proj₂ writes-in-stack

          -- Step 2: Disjointness from region membership
          addr≢new-rsp : addr ≢ new-rsp
          addr≢new-rsp eq = stack-code-disjoint new-rsp addr new-rsp-in-stack addr-in-code (sym eq)

          addr≢new-rsp+8 : addr ≢ (new-rsp +ℕ slot-size)
          addr≢new-rsp+8 eq = stack-code-disjoint (new-rsp +ℕ slot-size) addr new-rsp+8-in-stack addr-in-code (sym eq)

          -- Step 3: Chain through memory writes
          mem-s2 : readMem (memory s2) addr ≡ readMem (memory s) addr
          mem-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) addr
                     (readReg (regs s1) rdi) (subst (λ x → x ≢ addr) (sym rsp-s1) (λ eq → addr≢new-rsp (sym eq)))

          mem-s4 : readMem (memory s4) addr ≡ readMem (memory s2) addr
          mem-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) addr
                     (readReg (regs s3) r9) (subst (λ x → (x +ℕ slot-size) ≢ addr) (sym rsp-s3) (λ eq → addr≢new-rsp+8 (sym eq)))
      in trans mem-s4 mem-s2
      where
        open import Data.Product using (proj₁; proj₂)

    -- Memory at heap-region addresses preserved (D041)
    -- Stack and heap regions are disjoint, curry only writes to stack
    mem-heap-final : ∀ addr → region-of addr ≡ heap → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-heap-final addr addr-in-heap =
      let -- Step 1: Region membership (arithmetic encapsulated in infrastructure)
          writes-in-stack : (region-of new-rsp ≡ stack) × (region-of (new-rsp +ℕ slot-size) ≡ stack)
          writes-in-stack = alloc-2-slots-addrs-in-stack s cap2

          new-rsp-in-stack : region-of new-rsp ≡ stack
          new-rsp-in-stack = proj₁ writes-in-stack

          new-rsp+8-in-stack : region-of (new-rsp +ℕ slot-size) ≡ stack
          new-rsp+8-in-stack = proj₂ writes-in-stack

          -- Step 2: Disjointness from region membership
          addr≢new-rsp : addr ≢ new-rsp
          addr≢new-rsp eq = stack-heap-disjoint new-rsp addr new-rsp-in-stack addr-in-heap (sym eq)

          addr≢new-rsp+8 : addr ≢ (new-rsp +ℕ slot-size)
          addr≢new-rsp+8 eq = stack-heap-disjoint (new-rsp +ℕ slot-size) addr new-rsp+8-in-stack addr-in-heap (sym eq)

          -- Step 3: Chain through memory writes
          mem-s2 : readMem (memory s2) addr ≡ readMem (memory s) addr
          mem-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) addr
                     (readReg (regs s1) rdi) (subst (λ x → x ≢ addr) (sym rsp-s1) (λ eq → addr≢new-rsp (sym eq)))

          mem-s4 : readMem (memory s4) addr ≡ readMem (memory s2) addr
          mem-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ slot-size) addr
                     (readReg (regs s3) r9) (subst (λ x → (x +ℕ slot-size) ≢ addr) (sym rsp-s3) (λ eq → addr≢new-rsp+8 (sym eq)))
      in trans mem-s4 mem-s2
      where
        open import Data.Product using (proj₁; proj₂)

------------------------------------------------------------------------
-- Validity-Based Curry Proof
------------------------------------------------------------------------

-- | Validity-based curry execution
-- Like run-curry-star but produces ValidAt instead of encode equality
--
-- Key difference from encode-based:
-- - Instead of proving rax ≡ encode (eval (curry f) x)
-- - We prove ValidAt (eval (curry f) x) rax memory
--
-- The closure validity uses valid-closure-at because:
-- - Semantic closure has code-ptr = 0 (placeholder)
-- - Runtime memory has actual thunk address
-- - valid-closure-at only requires env-addr to match
-- Takes StackCapacity s 4 directly (eliminates blanket postulates)
-- Curry allocates 2 slots, so we need 4 to guarantee output capacity of 2
run-curry-star-v : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s 4 →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in ∃[ s' ] IRStarResultV (curry f) prog s s' x (length prefix)
run-curry-star-v {A} {B} {C} f prefix suffix x s h-false pc-eq input-valid stack-inv cap rbp-inv =
  s-final , record
    { ir-star = exec-star exec-result
    ; ir-halted = exec-halted exec-result
    ; ir-pc = exec-pc exec-result
    ; ir-result-valid = result-valid
    ; ir-r14 = exec-r14 exec-result
    ; ir-r15 = exec-r15 exec-result
    ; ir-rbp = exec-rbp exec-result
    ; ir-mem = exec-mem exec-result
    ; ir-mem-rbp = exec-mem-rbp exec-result
    ; ir-mem-rbp+8 = exec-mem-rbp+8 exec-result
    ; ir-stack-inv = exec-stack-inv exec-result
    ; ir-capacity = exec-capacity exec-result
    ; ir-rbp-inv = exec-rbp-inv exec-result
    ; ir-mem-above = exec-mem-above exec-result
    ; ir-mem-at-0 = exec-mem-at-0 exec-result
    ; ir-mem-code = exec-mem-code exec-result
    ; ir-mem-heap = exec-mem-heap exec-result
    ; ir-closure-wf = no-closure  -- TODO: curry should produce ClosureWellFormed
    }
  where
    -- Call curry with validity (no bridges!)
    curry-result : ∃[ s' ] (CurryExecResult f (prefix ++ compile-x86 (curry f) ++ suffix) s s' x (length prefix)
                           × CurryMemoryResult f (prefix ++ compile-x86 (curry f) ++ suffix) s' x (length prefix))
    curry-result = run-curry-star f prefix suffix x s h-false pc-eq input-valid stack-inv cap rbp-inv

    s-final = proj₁ curry-result
    exec-result = proj₁ (proj₂ curry-result)
    curry-mem = proj₂ (proj₂ curry-result)

    -- ============================================================
    -- VALIDITY-BASED PROOF (NO BRIDGES - uses valid-closure-env constructor)
    -- ============================================================

    -- Extract fields from CurryMemoryResult
    curry-env-addr = CurryMemoryResult.env-addr curry-mem
    curry-code-ptr = CurryMemoryResult.code-ptr curry-mem
    curry-closure-addr = CurryMemoryResult.closure-addr curry-mem
    curry-rax-eq = CurryMemoryResult.rax-eq curry-mem
    curry-mem-env = CurryMemoryResult.mem-env curry-mem
    curry-mem-cp = CurryMemoryResult.mem-cp curry-mem
    curry-v-env = CurryMemoryResult.v-env curry-mem

    -- Construct ClosureAtS from memory proofs
    closure-at : ClosureAtS curry-env-addr curry-code-ptr curry-closure-addr (memory s-final)
    closure-at = closure-at-s curry-mem-env curry-mem-cp

    -- The semantic closure from eval (curry f) x
    sem-closure : Closure B C
    sem-closure = eval (curry f) x

    -- Closure validity via valid-closure-env constructor
    -- The env-addr equality is refl because Closure.env-addr (eval (curry f) x) = encode x by definition
    closure-valid-at-addr : ValidAt {B ⇒ C} sem-closure curry-closure-addr (memory s-final)
    closure-valid-at-addr = valid-closure-env refl curry-v-env closure-at

    -- Transport to rax
    result-valid : ValidAt (eval (curry f) x) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst (λ addr → ValidAt {B ⇒ C} sem-closure addr (memory s-final))
                         (sym curry-rax-eq) closure-valid-at-addr
