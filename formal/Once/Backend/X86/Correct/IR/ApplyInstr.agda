------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.ApplyInstr
--
-- Instruction-tracing proofs for apply:
--   apply-setup-star: 6 setup instructions (push + 5 movs)
--   apply-call-star:  call r15 instruction
--   apply-pop-star:   pop r15 instruction
--
-- Extracted from IR/Apply.agda to reduce type-checking time.
-- Each function traces a specific instruction sequence and produces
-- postconditions for the next phase.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.ApplyInstr where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports for instruction tracing
open import Once.Backend.X86.Encoding using (mem-read-write)
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slot-size; slots; pair-alloc; StackInvariant; StackCapacity;
         r15-in-heap; r15-in-code; r15-in-stack;
         stack-inv-for-code-ptr;
         stack-inv-preserved-r15-unchanged;
         slots-mono-≤;
         capacity-after-push;
         ir-stack-requirement;
         apply-cap-after-push; apply-cap-after-call;
         abstract-to-rsp-slot-in-stack;
         apply-alloc-diff-from-above;
         apply-rsp-diff-from-alloc;
         rsp-sufficient; capacity-from-larger;
         rsp>slot-from-2slot)
open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-fits-thunk-bound)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; stack-heap-addr-disjoint;
         heap-offset; StackPointer;
         stackAddr-write-preserves-code;
         stackAddr-write-preserves-heap;
         slot-addr; slot-addr-≥-base)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)
open import Once.Backend.X86.Correct.MemoryValid
  using (Region; InRegion; Stack; Heap; HeapAlloc; StackAlloc; stack-offset; caller-disjoint-from-current)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_)

open import Data.Nat using (_>_; _≥_; _≤_; _∸_; s≤s; z≤n) renaming (_+_ to _+ℕ'_)
open import Data.Nat.Properties using (+-assoc; +-comm; m∸n≤m; ≤-trans; m∸n+n≡m; m≤m+n; <⇒≤; m<m+n)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂)

------------------------------------------------------------------------
-- apply-setup-star: Trace 6 setup instructions (push + 5 movs)
------------------------------------------------------------------------

-- The 6 setup instructions for apply:
--   0: push r15            ; save r15 (caller's value)
--   1: mov r15, [rdi]      ; load closure from pair.fst
--   2: mov rsi, [rdi+8]    ; load argument from pair.snd
--   3: mov r12, [r15]      ; load env from closure.fst
--   4: mov r15, [r15+8]    ; load code_ptr from closure.snd
--   5: mov rdi, rsi        ; move argument to rdi

-- Takes StackCapacity s (ir-stack-requirement apply) to produce StackCapacity s' 3 after push (for call phase)
apply-setup-star : ∀ {A B} (prefix suffix : Program)
                   (code-ptr env-addr closure-addr arg-addr : ℕ)
                   (s : State) →
  let prog = prefix ++ compile-instr (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (apply {A} {B})) →
  -- Region proofs for disjointness (supports both Stack and Heap values)
  (rdi-r : Region) → InRegion rdi-r (readReg (regs s) rdi) →
  (closure-r : Region) → InRegion closure-r closure-addr →
  -- Stack ownership bounds (for Stack case, from Ownership model)
  (rdi-r ≡ Stack → readReg (regs s) rdi ≥ readReg (regs s) rsp) →
  (closure-r ≡ Stack → closure-addr ≥ readReg (regs s) rsp) →
  -- Memory layout (derivable from validity, explicit for convenience)
  readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr →
  readMem (memory s) (readReg (regs s) rdi +ℕ slot-size) ≡ just arg-addr →
  readMem (memory s) closure-addr ≡ just env-addr →
  readMem (memory s) (closure-addr +ℕ slot-size) ≡ just code-ptr →
  -- NEW: code-ptr is a valid program address (needed for r15-in-code StackInvariant)
  code-ptr < length prog →
  -- Result after 6 instructions: r12=env, rdi=arg-addr, r15=code-ptr, pc=offset+6
  -- Plus: original r15 saved at rsp (before decrement)
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ 6
          × readReg (regs s') rdi ≡ arg-addr
          × readReg (regs s') r12 ≡ env-addr
          × readReg (regs s') r15 ≡ code-ptr
          × readReg (regs s') r14 ≡ readReg (regs s) r14
          × readReg (regs s') rbp ≡ readReg (regs s) rbp
          × StackInvariant s'
          × StackCapacity s' 3  -- Capacity after push (was rsp > pair-alloc)
          -- NEW: original r15 is saved on stack (at rsp after push = old rsp - 8)
          × readMem (memory s') (readReg (regs s') rsp) ≡ just (readReg (regs s) r15)
          -- RSP tracking: s'.rsp = s.rsp - 8 (push decrements by 8)
          × readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slot-size
          -- Memory preservation: addresses >= orig-rsp are not written by setup
          × (∀ addr → addr ≥ readReg (regs s) rsp →
             readMem (memory s') addr ≡ readMem (memory s) addr))
apply-setup-star {A} {B} prefix suffix code-ptr env-addr closure-addr arg-addr s
                 h-false pc-eq stack-inv cap rdi-r rdi-in-region closure-r closure-in-region
                 rdi-stack-bound closure-stack-bound mem-cl mem-arg mem-env mem-cp code-ptr<len =
  s6 , star-all , h6 , pc6 , rdi6 , r12-6 , r15-6 , r14-6 , rbp6 , stack-inv6 , rsp-sufficient-6 , mem-r15-saved , rsp6 , mem-above-setup
  where
    prog = prefix ++ compile-instr (apply {A} {B}) ++ suffix
    offset = length prefix
    old-r15 = readReg (regs s) r15
    old-rsp = readReg (regs s) rsp
    new-rsp = old-rsp ∸ slot-size

    -- Extract rsp-bound from cap for internal use (cap : StackCapacity s 4 gives > slots 4)
    -- Derive > pair-alloc for helpers that need weaker bound
    open import Data.Nat.Properties using (≤-<-trans; m≤m+n)
    rsp-bound : readReg (regs s) rsp > pair-alloc
    rsp-bound = ≤-<-trans (slots-mono-≤ (m≤m+n 2 2)) (StackCapacity.rsp-sufficient cap)

    -- D041: Stack region proof for new-rsp (uses cap directly, no postulate!)
    new-rsp-in-stack : InStack new-rsp
    new-rsp-in-stack = abstract-to-rsp-slot-in-stack s cap

    -- Proof that new-rsp < old-rsp (needed for caller-disjoint-from-current)
    slot-size<old-rsp : slot-size < old-rsp
    slot-size<old-rsp = rsp>slot-from-2slot rsp-bound

    new-rsp<old-rsp : new-rsp < old-rsp
    new-rsp<old-rsp = subst (new-rsp <_) sum-eq new-rsp<sum
      where
        slot-size≤old-rsp : slot-size ≤ old-rsp
        slot-size≤old-rsp = <⇒≤ slot-size<old-rsp
        sum-eq : new-rsp +ℕ slot-size ≡ old-rsp
        sum-eq = m∸n+n≡m slot-size≤old-rsp
        new-rsp<sum : new-rsp < new-rsp +ℕ slot-size
        new-rsp<sum = m<m+n new-rsp {slot-size} (s≤s z≤n)

    -- The 6 instructions (push + 5 movs)
    i0 = push (reg r15)
    i1 = mov (reg r15) (mem (base rdi))
    i2 = mov (reg rsi) (mem (base+disp rdi slot-size))
    i3 = mov (reg r12) (mem (base r15))
    i4 = mov (reg r15) (mem (base+disp r15 slot-size))
    i5 = mov (reg rdi) (reg rsi)

    -- Fetch lemmas
    fetch0 : fetch prog offset ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 _

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) _)

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1
               (fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 _)

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ _
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) _)

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ offset +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (offset +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2
               (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 _)

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ _
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) _)

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ offset +ℕ 3
    len-prefix-3 = List-length-++ prefix

    fetch3 : fetch prog (offset +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3
               (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 _)

    prog-eq4 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) ++ _
    prog-eq4 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) _)

    len-prefix-4 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) ≡ offset +ℕ 4
    len-prefix-4 = List-length-++ prefix

    fetch4 : fetch prog (offset +ℕ 4) ≡ just i4
    fetch4 = subst₂ (λ p n → fetch p n ≡ just i4) (sym prog-eq4) len-prefix-4
               (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) i4 _)

    prog-eq5 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) ++ _
    prog-eq5 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) _)

    len-prefix-5 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) ≡ offset +ℕ 5
    len-prefix-5 = List-length-++ prefix

    fetch5 : fetch prog (offset +ℕ 5) ≡ just i5
    fetch5 = subst₂ (λ p n → fetch p n ≡ just i5) (sym prog-eq5) len-prefix-5
               (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ []) i5 _)

    -- State after instruction 0: push r15
    -- Saves original r15 to stack, decrements rsp by 8
    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; memory = writeMem (memory s) new-rsp old-r15
                  ; pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just s1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  refl

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    rsp1 : readReg (regs s1) rsp ≡ new-rsp
    rsp1 = readReg-writeReg-same (regs s) rsp new-rsp

    -- State after instruction 1: mov r15, [rdi]
    -- r15 = closure-addr (read from [rdi])
    rdi-s1 : readReg (regs s1) rdi ≡ readReg (regs s) rdi
    rdi-s1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    -- Memory at rdi is preserved after push (region-based disjointness)
    -- For Heap: stack-heap disjointness (stack and heap are disjoint regions)
    -- For Stack: caller-disjoint-from-current (ownership model)
    stack-heap-disjoint-rdi : new-rsp ≢ readReg (regs s) rdi
    stack-heap-disjoint-rdi = region-disjoint-rdi rdi-r rdi-in-region refl
      where
        region-disjoint-rdi : (r : Region) → InRegion r (readReg (regs s) rdi) → rdi-r ≡ r → new-rsp ≢ readReg (regs s) rdi
        region-disjoint-rdi HeapAlloc ih _ = λ eq → stack-heap-addr-disjoint new-rsp (readReg (regs s) rdi) new-rsp-in-stack ih eq
        region-disjoint-rdi StackAlloc _ r-eq = λ eq →
          caller-disjoint-from-current (rdi-stack-bound r-eq) new-rsp<old-rsp (sym eq)

    mem-cl-s1 : readMem (memory s1) (readReg (regs s1) rdi) ≡ just closure-addr
    mem-cl-s1 = subst (λ addr → readMem (memory s1) addr ≡ just closure-addr)
                      (sym rdi-s1)
                      (trans (readMem-writeMem-diff (memory s) new-rsp (readReg (regs s) rdi)
                               old-r15 stack-heap-disjoint-rdi)
                             mem-cl)

    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) r15 closure-addr
                   ; pc = pc s1 +ℕ 1 }

    step1 : step prog s1 ≡ just s2
    step1 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execMov-reg-mem-base s1 r15 rdi closure-addr mem-cl-s1)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    -- State after instruction 2: mov rsi, [rdi+8]
    rdi-s2 : readReg (regs s2) rdi ≡ readReg (regs s) rdi
    rdi-s2 = trans (readReg-writeReg-r15-rdi (regs s1) closure-addr) rdi-s1

    -- Memory at rdi+8 is preserved after push (region-based disjointness)
    stack-heap-disjoint-rdi+8 : new-rsp ≢ readReg (regs s) rdi +ℕ slot-size
    stack-heap-disjoint-rdi+8 = region-disjoint-rdi+8 rdi-r rdi-in-region refl
      where
        region-disjoint-rdi+8 : (r : Region) → InRegion r (readReg (regs s) rdi) → rdi-r ≡ r → new-rsp ≢ readReg (regs s) rdi +ℕ slot-size
        region-disjoint-rdi+8 HeapAlloc ih _ = λ eq → let rdi+8-in-heap = heap-offset (readReg (regs s) rdi) ih
                                               in stack-heap-addr-disjoint new-rsp (readReg (regs s) rdi +ℕ slot-size) new-rsp-in-stack rdi+8-in-heap eq
        region-disjoint-rdi+8 StackAlloc _ r-eq = λ eq →
          let rdi-bound = rdi-stack-bound r-eq
              rdi+8-bound = ≤-trans rdi-bound (m≤m+n (readReg (regs s) rdi) slot-size)
          in caller-disjoint-from-current rdi+8-bound new-rsp<old-rsp (sym eq)

    -- Memory at closure-addr is preserved (region-based disjointness)
    stack-heap-disjoint-closure : new-rsp ≢ closure-addr
    stack-heap-disjoint-closure = region-disjoint-closure closure-r closure-in-region refl
      where
        region-disjoint-closure : (r : Region) → InRegion r closure-addr → closure-r ≡ r → new-rsp ≢ closure-addr
        region-disjoint-closure HeapAlloc ih _ = λ eq → stack-heap-addr-disjoint new-rsp closure-addr new-rsp-in-stack ih eq
        region-disjoint-closure StackAlloc _ r-eq = λ eq →
          caller-disjoint-from-current (closure-stack-bound r-eq) new-rsp<old-rsp (sym eq)

    stack-heap-disjoint-closure+8 : new-rsp ≢ closure-addr +ℕ slot-size
    stack-heap-disjoint-closure+8 = region-disjoint-closure+8 closure-r closure-in-region refl
      where
        region-disjoint-closure+8 : (r : Region) → InRegion r closure-addr → closure-r ≡ r → new-rsp ≢ closure-addr +ℕ slot-size
        region-disjoint-closure+8 HeapAlloc ih _ = λ eq → let closure+8-in-heap = heap-offset closure-addr ih
                                                   in stack-heap-addr-disjoint new-rsp (closure-addr +ℕ slot-size) new-rsp-in-stack closure+8-in-heap eq
        region-disjoint-closure+8 StackAlloc _ r-eq = λ eq →
          let closure-bound = closure-stack-bound r-eq
              closure+8-bound = ≤-trans closure-bound (m≤m+n closure-addr slot-size)
          in caller-disjoint-from-current closure+8-bound new-rsp<old-rsp (sym eq)

    -- memory s2 = memory s1 = writeMem (memory s) new-rsp old-r15
    mem-s2-eq-s1 : memory s2 ≡ memory s1
    mem-s2-eq-s1 = refl

    -- Chain: memory s → memory s1 → memory s2
    mem-arg-s2 : readMem (memory s2) (readReg (regs s2) rdi +ℕ slot-size) ≡ just arg-addr
    mem-arg-s2 = subst (λ addr → readMem (memory s2) (addr +ℕ slot-size) ≡ just arg-addr)
                       (sym rdi-s2)
                       (trans (readMem-writeMem-diff (memory s) new-rsp (readReg (regs s) rdi +ℕ slot-size)
                                old-r15 stack-heap-disjoint-rdi+8)
                              mem-arg)

    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rsi arg-addr
                   ; pc = pc s2 +ℕ 1 }

    step2 : step prog s2 ≡ just s3
    step2 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execMov-reg-mem-disp s2 rsi rdi slot-size arg-addr mem-arg-s2)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc offset 2 1)

    -- State after instruction 3: mov r12, [r15]
    r15-s2 : readReg (regs s2) r15 ≡ closure-addr
    r15-s2 = readReg-writeReg-same (regs s1) r15 closure-addr

    r15-s3 : readReg (regs s3) r15 ≡ closure-addr
    r15-s3 = trans (readReg-writeReg-rsi-r15 (regs s2) arg-addr) r15-s2

    mem-env-s3 : readMem (memory s3) (readReg (regs s3) r15) ≡ just env-addr
    mem-env-s3 = subst (λ addr → readMem (memory s3) addr ≡ just env-addr)
                       (sym r15-s3)
                       (trans (readMem-writeMem-diff (memory s) new-rsp closure-addr
                                old-r15 stack-heap-disjoint-closure)
                              mem-env)

    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) r12 env-addr
                   ; pc = pc s3 +ℕ 1 }

    step3 : step prog s3 ≡ just s4
    step3 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMov-reg-mem-base s3 r12 r15 env-addr mem-env-s3)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc offset 3 1)

    -- State after instruction 4: mov r15, [r15+8]
    r15-s4-old : readReg (regs s4) r15 ≡ closure-addr
    r15-s4-old = trans (readReg-writeReg-r12-r15 (regs s3) env-addr) r15-s3

    mem-cp-s4 : readMem (memory s4) (readReg (regs s4) r15 +ℕ slot-size) ≡ just code-ptr
    mem-cp-s4 = subst (λ addr → readMem (memory s4) (addr +ℕ slot-size) ≡ just code-ptr)
                      (sym r15-s4-old)
                      (trans (readMem-writeMem-diff (memory s) new-rsp (closure-addr +ℕ slot-size)
                               old-r15 stack-heap-disjoint-closure+8)
                             mem-cp)

    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) r15 code-ptr
                   ; pc = pc s4 +ℕ 1 }

    step4 : step prog s4 ≡ just s5
    step4 = trans (step-exec prog s4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (execMov-reg-mem-disp s4 r15 r15 slot-size code-ptr mem-cp-s4)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc offset 4 1)

    -- State after instruction 5: mov rdi, rsi
    rsi-s5 : readReg (regs s5) rsi ≡ arg-addr
    rsi-s5 = trans (readReg-writeReg-r15-rsi (regs s4) code-ptr)
                   (trans (readReg-writeReg-r12-rsi (regs s3) env-addr)
                          (readReg-writeReg-same (regs s2) rsi arg-addr))

    s6 : State
    s6 = record s5 { regs = writeReg (regs s5) rdi (readReg (regs s5) rsi)
                   ; pc = pc s5 +ℕ 1 }

    step5 : step prog s5 ≡ just s6
    step5 = trans (step-exec prog s5 i5 h5 (subst (λ p → fetch prog p ≡ just i5) (sym pc5) fetch5))
                  (execMov-reg-reg s5 rdi rsi)

    -- Build Star proof
    star-all : Star prog s s6
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               ⟨ h5 , step5 ⟩◅
               refl*

    -- Final state properties
    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ offset +ℕ 6
    pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc offset 5 1)

    rdi6 : readReg (regs s6) rdi ≡ arg-addr
    rdi6 = trans (readReg-writeReg-same (regs s5) rdi (readReg (regs s5) rsi)) rsi-s5

    r12-6 : readReg (regs s6) r12 ≡ env-addr
    r12-6 = trans (readReg-writeReg-rdi-r12 (regs s5) (readReg (regs s5) rsi))
                  (trans (readReg-writeReg-r15-r12 (regs s4) code-ptr)
                         (readReg-writeReg-same (regs s3) r12 env-addr))

    r15-6 : readReg (regs s6) r15 ≡ code-ptr
    r15-6 = trans (readReg-writeReg-rdi-r15 (regs s5) (readReg (regs s5) rsi))
                  (readReg-writeReg-same (regs s4) r15 code-ptr)

    r14-6 : readReg (regs s6) r14 ≡ readReg (regs s) r14
    r14-6 = trans (readReg-writeReg-rdi-r14 (regs s5) (readReg (regs s5) rsi))
                  (trans (readReg-writeReg-r15-r14 (regs s4) code-ptr)
                         (trans (readReg-writeReg-r12-r14 (regs s3) env-addr)
                                (trans (readReg-writeReg-rsi-r14 (regs s2) arg-addr)
                                       (trans (readReg-writeReg-r15-r14 (regs s1) closure-addr)
                                              (readReg-writeReg-rsp-r14 (regs s) new-rsp)))))

    rbp6 : readReg (regs s6) rbp ≡ readReg (regs s) rbp
    rbp6 = trans (readReg-writeReg-rdi-rbp (regs s5) (readReg (regs s5) rsi))
                 (trans (readReg-writeReg-r15-rbp (regs s4) code-ptr)
                        (trans (readReg-writeReg-r12-rbp (regs s3) env-addr)
                               (trans (readReg-writeReg-rsi-rbp (regs s2) arg-addr)
                                      (trans (readReg-writeReg-r15-rbp (regs s1) closure-addr)
                                             (readReg-writeReg-rsp-rbp (regs s) new-rsp)))))

    -- RSP after setup: same as after push (new-rsp = old-rsp - 8)
    rsp6 : readReg (regs s6) rsp ≡ new-rsp
    rsp6 = trans (readReg-writeReg-rdi-rsp (regs s5) (readReg (regs s5) rsi))
                 (trans (readReg-writeReg-r15-rsp (regs s4) code-ptr)
                        (trans (readReg-writeReg-r12-rsp (regs s3) env-addr)
                               (trans (readReg-writeReg-rsi-rsp (regs s2) arg-addr)
                                      (trans (readReg-writeReg-r15-rsp (regs s1) closure-addr)
                                             rsp1))))

    -- StackInvariant for apply setup
    stack-inv6 : StackInvariant s6
    stack-inv6 = stack-inv-for-code-ptr s6 (length prog) r15<len
      where
        r15<len : readReg (regs s6) r15 < length prog
        r15<len = subst (_< length prog) (sym r15-6) code-ptr<len

    -- Derive StackCapacity s6 3 from input cap : StackCapacity s (ir-stack-requirement apply) via push
    rsp-sufficient-6 : StackCapacity s6 3
    rsp-sufficient-6 = capacity-after-push s s6 3 cap rsp6'
      where
        rsp6' : readReg (regs s6) rsp ≡ readReg (regs s) rsp ∸ slot-size
        rsp6' = rsp6

    -- Memory preservation: original r15 is saved at new-rsp
    mem-r15-saved : readMem (memory s6) (readReg (regs s6) rsp) ≡ just old-r15
    mem-r15-saved = subst (λ addr → readMem (memory s6) addr ≡ just old-r15)
                          (sym rsp6)
                          (trans (mem-read-write {memory s} {new-rsp} {old-r15})
                                 refl)

    -- Memory preservation for addresses >= old-rsp
    mem-above-setup : ∀ addr → addr ≥ old-rsp → readMem (memory s6) addr ≡ readMem (memory s) addr
    mem-above-setup addr addr≥rsp =
      readMem-writeMem-diff (memory s) new-rsp addr old-r15
        (apply-alloc-diff-from-above s rsp-bound addr addr≥rsp)

------------------------------------------------------------------------
-- apply-call-star: Trace call r15 instruction
------------------------------------------------------------------------

-- Prove call instruction: pushes return address and jumps to code-ptr
-- Takes StackCapacity s apply-cap-after-push to produce StackCapacity s' apply-cap-after-call (for thunk)
apply-call-star : ∀ {A B} (prefix suffix : Program)
                  (code-ptr : ℕ) (s : State) →
  let prog = prefix ++ compile-instr (apply {A} {B}) ++ suffix
      offset = length prefix
      ret-addr = offset +ℕ 7
  in
  halted s ≡ false →
  pc s ≡ offset +ℕ 6 →
  readReg (regs s) r15 ≡ code-ptr →
  StackInvariant s →
  StackCapacity s apply-cap-after-push →
  -- Result after call: pc=code-ptr, ret-addr on stack
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ code-ptr
          × readMem (memory s') (readReg (regs s') rsp) ≡ just ret-addr
          × readReg (regs s') rdi ≡ readReg (regs s) rdi
          × readReg (regs s') r12 ≡ readReg (regs s) r12
          × readReg (regs s') r14 ≡ readReg (regs s) r14
          × readReg (regs s') rbp ≡ readReg (regs s) rbp
          × StackInvariant s'
          × StackCapacity s' apply-cap-after-call
          -- RSP tracking: call pushes return address (rsp -= 8)
          × readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slot-size
          -- Memory preservation at original rsp
          × readMem (memory s') (readReg (regs s) rsp) ≡ readMem (memory s) (readReg (regs s) rsp)
          -- General memory preservation for addresses >= s.rsp
          × (∀ addr → addr ≥ readReg (regs s) rsp →
             readMem (memory s') addr ≡ readMem (memory s) addr)
          -- Memory at code-region preserved
          × (∀ addr → InCode addr →
             readMem (memory s') addr ≡ readMem (memory s) addr)
          -- Memory at heap-region preserved
          × (∀ addr → InHeap addr →
             readMem (memory s') addr ≡ readMem (memory s) addr))
apply-call-star {A} {B} prefix suffix code-ptr s h-false pc-eq r15-eq stack-inv cap =
  s1 , star-all , h1 , pc1 , mem1 , rdi1 , r12-1 , r14-1 , rbp1 , stack-inv1 , rsp-sufficient-1 , rsp1-eq , mem-preserved-old-rsp , mem-above-call , mem-code-call , mem-heap-call
  where
    open import Data.Nat.Properties using (≤-<-trans; m≤m+n)

    prog = prefix ++ compile-instr (apply {A} {B}) ++ suffix
    offset = length prefix
    ret-addr = offset +ℕ 7

    -- Extract rsp-bound from cap
    rsp-bound : readReg (regs s) rsp > slots apply-cap-after-call
    rsp-bound = ≤-<-trans (slots-mono-≤ (m≤m+n 2 1)) (StackCapacity.rsp-sufficient cap)

    -- The call instruction (now i6)
    i6 = call (reg r15)

    -- Fetch lemma
    i0' = push (reg r15)
    i1' = mov (reg r15) (mem (base rdi))
    i2' = mov (reg rsi) (mem (base+disp rdi slot-size))
    i3' = mov (reg r12) (mem (base r15))
    i4' = mov (reg r15) (mem (base+disp r15 slot-size))
    i5' = mov (reg rdi) (reg rsi)

    prog-eq6 : prog ≡ (prefix ++ i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ []) ++ _
    prog-eq6 = sym (++-assoc prefix (i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ []) _)

    len-prefix6 : length (prefix ++ i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ []) ≡ offset +ℕ 6
    len-prefix6 = List-length-++ prefix

    fetch6 : fetch prog (offset +ℕ 6) ≡ just i6
    fetch6 = subst₂ (λ p n → fetch p n ≡ just i6) (sym prog-eq6) len-prefix6
               (fetch-at-prefix-end (prefix ++ i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ []) i6 _)

    -- State after call r15
    old-rsp = readReg (regs s) rsp
    new-rsp = old-rsp ∸ slot-size

    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp new-rsp
                  ; memory = writeMem (memory s) new-rsp (pc s +ℕ 1)
                  ; pc = code-ptr }

    step6 : step prog s ≡ just s1
    step6 = trans (step-exec prog s i6 h-false (subst (λ p → fetch prog p ≡ just i6) (sym pc-eq) fetch6))
                  (cong (λ cp → just (record s { regs = writeReg (regs s) rsp new-rsp
                                               ; memory = writeMem (memory s) new-rsp (pc s +ℕ 1)
                                               ; pc = cp })) r15-eq)

    star-all : Star prog s s1
    star-all = ⟨ h-false , step6 ⟩◅ refl*

    -- Final state properties
    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ code-ptr
    pc1 = refl

    -- Memory at new rsp contains return address
    ret-addr-eq : pc s +ℕ 1 ≡ ret-addr
    ret-addr-eq = trans (cong (_+ℕ 1) pc-eq) (+-assoc offset 6 1)

    rsp1 : readReg (regs s1) rsp ≡ new-rsp
    rsp1 = readReg-writeReg-same (regs s) rsp new-rsp

    mem1 : readMem (memory s1) (readReg (regs s1) rsp) ≡ just ret-addr
    mem1 = trans (cong (λ a → readMem (memory s1) a) rsp1)
                 (trans (mem-read-write {memory s} {new-rsp} {pc s +ℕ 1})
                        (cong just ret-addr-eq))

    -- Register preservation (call only writes rsp)
    rdi1 : readReg (regs s1) rdi ≡ readReg (regs s) rdi
    rdi1 = readReg-writeReg-rsp-rdi (regs s) new-rsp

    r12-1 : readReg (regs s1) r12 ≡ readReg (regs s) r12
    r12-1 = readReg-writeReg-rsp-r12 (regs s) new-rsp

    r14-1 : readReg (regs s1) r14 ≡ readReg (regs s) r14
    r14-1 = readReg-writeReg-rsp-r14 (regs s) new-rsp

    rbp1 : readReg (regs s1) rbp ≡ readReg (regs s) rbp
    rbp1 = readReg-writeReg-rsp-rbp (regs s) new-rsp

    -- r15 is preserved by call (call only writes rsp)
    r15-1 : readReg (regs s1) r15 ≡ readReg (regs s) r15
    r15-1 = readReg-writeReg-rsp-r15 (regs s) new-rsp

    -- StackInvariant after call
    stack-inv1 : StackInvariant s1
    stack-inv1 = stack-inv-preserved-r15-unchanged s s1 stack-inv r15-1 rsp1≤
      where
        open import Data.Nat.Properties using (m∸n≤m)
        rsp1≤ : readReg (regs s1) rsp ≤ readReg (regs s) rsp
        rsp1≤ = subst (_≤ old-rsp) (sym rsp1) (m∸n≤m old-rsp slot-size)

    -- RSP tracking
    rsp1-eq : readReg (regs s1) rsp ≡ readReg (regs s) rsp ∸ slot-size
    rsp1-eq = rsp1

    -- Derive StackCapacity s1 apply-cap-after-call from input cap via call (push ret addr)
    rsp-sufficient-1 : StackCapacity s1 apply-cap-after-call
    rsp-sufficient-1 = capacity-after-push s s1 apply-cap-after-call cap rsp1-eq

    -- Memory at original rsp preserved
    old-rsp≢new-rsp : old-rsp ≢ new-rsp
    old-rsp≢new-rsp = apply-rsp-diff-from-alloc s rsp-bound

    mem-preserved-old-rsp : readMem (memory s1) old-rsp ≡ readMem (memory s) old-rsp
    mem-preserved-old-rsp = readMem-writeMem-diff (memory s) new-rsp old-rsp (pc s +ℕ 1)
                              (λ eq → old-rsp≢new-rsp (sym eq))

    -- General memory preservation for addresses >= s.rsp
    mem-above-call : ∀ addr → addr ≥ old-rsp → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-above-call addr addr≥rsp =
      readMem-writeMem-diff (memory s) new-rsp addr (pc s +ℕ 1)
        (apply-alloc-diff-from-above s rsp-bound addr addr≥rsp)

    -- Shared: write address is in stack region
    write-addr-in-stack-call : InStack new-rsp
    write-addr-in-stack-call = abstract-to-rsp-slot-in-stack s cap

    -- Memory at code-region addresses preserved
    mem-code-call : ∀ addr → InCode addr → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-code-call addr addr-in-code = stackAddr-write-preserves-code (memory s) new-rsp (pc s +ℕ 1) addr write-addr-in-stack-call addr-in-code

    -- Memory at heap-region addresses preserved
    mem-heap-call : ∀ addr → InHeap addr → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-heap-call addr addr-in-heap = stackAddr-write-preserves-heap (memory s) new-rsp (pc s +ℕ 1) addr write-addr-in-stack-call addr-in-heap

------------------------------------------------------------------------
-- ApplyPopResult: Record type for pop r15 results
------------------------------------------------------------------------

record ApplyPopResult {A B : Type} (prefix suffix : Program)
                      (old-r15 orig-rsp : ℕ) (s s' : State) : Set where
  private
    prog = prefix ++ compile-instr (apply {A} {B}) ++ suffix
    offset = length prefix
  field
    star-pop     : Star prog s s'
    h-pop        : halted s' ≡ false
    pc-pop       : pc s' ≡ offset +ℕ 8
    r15-pop      : readReg (regs s') r15 ≡ old-r15
    rax-pop      : readReg (regs s') rax ≡ readReg (regs s) rax
    r14-pop      : readReg (regs s') r14 ≡ readReg (regs s) r14
    rbp-pop      : readReg (regs s') rbp ≡ readReg (regs s) rbp
    stack-inv-pop : StackInvariant s'
    rsp-sufficient-pop   : readReg (regs s') rsp > pair-alloc
    rsp-restored : readReg (regs s') rsp ≡ orig-rsp
    -- Pop doesn't write memory, so all memory is preserved
    mem-pop-preserved : memory s' ≡ memory s

open ApplyPopResult public

-- | R15OrigInfo: Information about r15 for pop reconstruction
data R15OrigInfo (old-r15 orig-rsp : ℕ) : Set where
  r15-was-in-heap  : InHeap old-r15 → R15OrigInfo old-r15 orig-rsp
  r15-was-in-code  : InCode old-r15 → R15OrigInfo old-r15 orig-rsp
  r15-was-in-stack : (frame : StackPointer) →
                     (slot : ℕ) →
                     old-r15 ≡ slot-addr frame slot →
                     sp-addr frame ≥ orig-rsp →
                     R15OrigInfo old-r15 orig-rsp

------------------------------------------------------------------------
-- apply-pop-star: Trace pop r15 instruction
------------------------------------------------------------------------

-- | Trace pop r15 instruction at the end of apply
-- This restores r15 to its original value (saved at start by push r15)
apply-pop-star : ∀ {A B} (prefix suffix : Program)
                 (old-r15 orig-rsp : ℕ) (s : State) →
  let prog = prefix ++ compile-instr (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset +ℕ 7 →
  readMem (memory s) (readReg (regs s) rsp) ≡ just old-r15 →
  readReg (regs s) rsp ≡ orig-rsp ∸ slot-size →
  R15OrigInfo old-r15 orig-rsp →
  readReg (regs s) rsp > pair-alloc →
  ∃[ s' ] ApplyPopResult {A} {B} prefix suffix old-r15 orig-rsp s s'
apply-pop-star {A} {B} prefix suffix old-r15 orig-rsp s h-false pc-eq mem-r15 rsp-eq orig-inv rsp-sufficient =
  s1 , record
    { star-pop = star-all
    ; h-pop = h1
    ; pc-pop = pc1
    ; r15-pop = r15-1
    ; rax-pop = rax1
    ; r14-pop = r14-1
    ; rbp-pop = rbp1
    ; stack-inv-pop = stack-inv1
    ; rsp-sufficient-pop = rsp-sufficient-1
    ; rsp-restored = rsp1-eq-orig
    ; mem-pop-preserved = refl
    }
  where
    prog = prefix ++ compile-instr (apply {A} {B}) ++ suffix
    offset = length prefix

    -- The pop instruction (i7)
    i7 = pop r15

    -- Fetch lemma for pop r15 at offset+7
    i0' = push (reg r15)
    i1' = mov (reg r15) (mem (base rdi))
    i2' = mov (reg rsi) (mem (base+disp rdi slot-size))
    i3' = mov (reg r12) (mem (base r15))
    i4' = mov (reg r15) (mem (base+disp r15 slot-size))
    i5' = mov (reg rdi) (reg rsi)
    i6' = call (reg r15)

    prog-eq7 : prog ≡ (prefix ++ i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ i6' ∷ []) ++ _
    prog-eq7 = sym (++-assoc prefix (i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ i6' ∷ []) _)

    len-prefix7 : length (prefix ++ i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ i6' ∷ []) ≡ offset +ℕ 7
    len-prefix7 = List-length-++ prefix

    fetch7 : fetch prog (offset +ℕ 7) ≡ just i7
    fetch7 = subst₂ (λ p n → fetch p n ≡ just i7) (sym prog-eq7) len-prefix7
               (fetch-at-prefix-end (prefix ++ i0' ∷ i1' ∷ i2' ∷ i3' ∷ i4' ∷ i5' ∷ i6' ∷ []) i7 _)

    -- State after pop r15
    old-rsp = readReg (regs s) rsp
    new-rsp = old-rsp +ℕ slot-size

    s1 : State
    s1 = record s { regs = writeReg (writeReg (regs s) r15 old-r15) rsp new-rsp
                  ; pc = pc s +ℕ 1 }

    step7 : step prog s ≡ just s1
    step7 = trans (step-exec prog s i7 h-false (subst (λ p → fetch prog p ≡ just i7) (sym pc-eq) fetch7))
                  (execPop prog s r15 old-r15 mem-r15)

    star-all : Star prog s s1
    star-all = ⟨ h-false , step7 ⟩◅ refl*

    -- Final state properties
    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ offset +ℕ 8
    pc1 = trans (cong (_+ℕ 1) pc-eq) (+-assoc offset 7 1)

    r15-1 : readReg (regs s1) r15 ≡ old-r15
    r15-1 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s) r15 old-r15) new-rsp)
                  (readReg-writeReg-same (regs s) r15 old-r15)

    rax1 : readReg (regs s1) rax ≡ readReg (regs s) rax
    rax1 = trans (readReg-writeReg-rsp-rax (writeReg (regs s) r15 old-r15) new-rsp)
                 (readReg-writeReg-r15-rax (regs s) old-r15)

    r14-1 : readReg (regs s1) r14 ≡ readReg (regs s) r14
    r14-1 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s) r15 old-r15) new-rsp)
                  (readReg-writeReg-r15-r14 (regs s) old-r15)

    rbp1 : readReg (regs s1) rbp ≡ readReg (regs s) rbp
    rbp1 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s) r15 old-r15) new-rsp)
                 (readReg-writeReg-r15-rbp (regs s) old-r15)

    -- s1.rsp = orig-rsp
    rsp1-eq-orig : readReg (regs s1) rsp ≡ orig-rsp
    rsp1-eq-orig = begin
      readReg (regs s1) rsp
        ≡⟨ readReg-writeReg-same (writeReg (regs s) r15 old-r15) rsp new-rsp ⟩
      new-rsp
        ≡⟨ refl ⟩
      old-rsp +ℕ slot-size
        ≡⟨ cong (_+ℕ slot-size) rsp-eq ⟩
      (orig-rsp ∸ slot-size) +ℕ slot-size
        ≡⟨ m∸n+n≡m 8≤orig-rsp ⟩
      orig-rsp ∎
      where
        open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
        open ≡-Reasoning
        open import Data.Nat using (s≤s; z≤n)
        open import Data.Nat.Properties using (<⇒≤; m∸n≤m)

        s-rsp≤orig : readReg (regs s) rsp ≤ orig-rsp
        s-rsp≤orig = subst (_≤ orig-rsp) (sym rsp-eq) (m∸n≤m orig-rsp slot-size)

        8≤orig-rsp : 8 ≤ orig-rsp
        8≤orig-rsp = ≤-trans word-fits-thunk-bound (≤-trans rsp-sufficient s-rsp≤orig)

    stack-inv1 : StackInvariant s1
    stack-inv1 = derive-stack-inv orig-inv
      where
        derive-stack-inv : R15OrigInfo old-r15 orig-rsp → StackInvariant s1
        derive-stack-inv (r15-was-in-heap r15-heap) =
          r15-in-heap (subst InHeap (sym r15-1) r15-heap)
        derive-stack-inv (r15-was-in-code r15-code) =
          r15-in-code (subst InCode (sym r15-1) r15-code)
        derive-stack-inv (r15-was-in-stack frame slot r15-eq frame-bound) =
          r15-in-stack frame slot (trans r15-1 r15-eq)
                       (subst (sp-addr frame ≥_) (sym rsp1-eq-orig) frame-bound)

    -- Derive rsp-sufficient-1 from preconditions
    rsp-sufficient-1 : readReg (regs s1) rsp > pair-alloc
    rsp-sufficient-1 = subst (_> pair-alloc) (sym rsp1-eq-orig) orig-rsp>slots2
      where
        open import Data.Nat.Properties using (≤-trans; m∸n≤m)
        orig-rsp≥s-rsp : orig-rsp ≥ readReg (regs s) rsp
        orig-rsp≥s-rsp = subst (orig-rsp ≥_) (sym rsp-eq) (m∸n≤m orig-rsp slot-size)

        orig-rsp>slots2 : orig-rsp > pair-alloc
        orig-rsp>slots2 = ≤-trans rsp-sufficient orig-rsp≥s-rsp
