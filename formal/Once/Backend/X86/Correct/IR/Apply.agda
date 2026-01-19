------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Apply
--
-- Star-based apply proof using ClosureWellFormed.
--
-- Apply compilation (8 instructions):
--   0: push r15            ; save r15 (caller's value)
--   1: mov r15, [rdi]      ; load closure from pair.fst
--   2: mov rsi, [rdi+8]    ; load argument from pair.snd
--   3: mov r12, [r15]      ; load env from closure.fst
--   4: mov r15, [r15+8]    ; load code_ptr from closure.snd
--   5: mov rdi, rsi        ; move argument to rdi
--   6: call r15            ; call thunk (pushes ret addr, jumps to code_ptr)
--   7: pop r15             ; restore r15 (satisfies ir-r15 preservation)
--
-- After call r15:
--   - PC = code_ptr (thunk entry)
--   - Return address (offset+7) is on stack
--   - r12 = env, rdi = arg
--
-- Thunk execution (via ClosureWellFormed.thunk-correct):
--   - Thunk runs with r12=env, rdi=arg
--   - Thunk ends with ret, popping return address
--   - PC returns to offset+7
--   - rax = encode (semantics arg)
--
-- After pop r15 (instruction 7):
--   - r15 restored to original value (from push at instruction 0)
--   - PC = offset+8 = compile-length apply
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Apply where

-- Import consolidated Foundation module
open import Once.Backend.X86.Correct.Foundation

-- Additional imports not in Foundation
-- NOTE: IR/Apply.agda is postulate-free! Uses validity-based proofs.
open import Once.Backend.X86.Encoding using (mem-read-write)
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.ExecLemmas using (fetch-at-prefix-end; just-injective)
open import Once.Backend.X86.Correct.InstrExec using (execPop)
open import Once.Backend.X86.Correct.StackInstantiation
  using (slot-size; slots; rsp-bound-to-capacity; R15Status; StackInvariant;
         r15-in-heap; r15-in-code; r15-in-stack;
         stack-write-preserves-code-r15;
         stack-write-preserves-r15; stack-inv-for-code-ptr;
         stack-inv-preserved-r15-unchanged; stack-inv-preserved-unchanged;
         StackCapacity; capacity-maintained; slots-mono-≤;
         capacity-after-push; capacity-after-pop; capacity-preserved-rsp-unchanged;
         capacity-when-rsp-restored; capacity-after-delta;
         ir-stack-requirement; ir-rsp-delta; ir-output-capacity;
         -- Apply intermediate capacities (symbolic names)
         apply-cap-after-push; apply-cap-after-call; apply-consumed-slots;
         output-slots; capacity-from-larger;
         -- D041: Abstract interface (no arithmetic in types)
         apply-frame-1; apply-frame-slot-0-in-stack; abstract-to-rsp-slot-in-stack;
         -- D041: Abstract helpers for 1-slot and 2-slot allocation
         apply-alloc-below-rsp; apply-alloc-diff-from-above;
         apply-rsp-diff-from-alloc; apply-double-alloc-below-rsp;
         apply-double-alloc-diff-from-above;
         -- D041: Heap-stack disjointness via regions (replaces postulate)
         heap-stack-disjoint-via-region;
         -- Region proofs from encode
         encode-in-heap-sem; encode-offset-in-heap)
open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-fits-thunk-bound)
open import Once.Backend.Common.MemoryRegions
  using (InStack; InHeap; InCode; stack-code-addr-disjoint; stack-heap-addr-disjoint;
         heap-offset; StackPointer; frameSlot;
         stackAddr-write-preserves-code;
         stackAddr-write-preserves-heap;
         pc-in-code; slot-addr; slot-addr-≥-base)
open import Once.Backend.Common.MemoryRegions using () renaming (addr to sp-addr)
-- Internal glue for abstraction boundary (implementation use only!)
open import Once.Backend.Common.MemoryRegions using (module FrameSlotInternal)
open FrameSlotInternal using (frameSlot-0-is-top)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; IRStarResultV; ClosureWFOutput; no-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-code; ir-mem-heap; ir-closure-wf;
         rbp-inv-preserved-unchanged)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-pair; valid-closure;
         PairAtS; fst-valid-s; snd-valid-s;
         ClosureAtS; env-valid-s; code-valid-s;
         valid-subst-addr-mem; valid-subst-heap-preserved;
         valid-pair-decompose; valid-in-heap)
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult;
         code-ptr-valid; thunk-correct;
         thunk-star; thunk-halted; thunk-result-valid;
         thunk-r14; thunk-r15; thunk-rbp;
         thunk-stack-inv; thunk-capacity;
         thunk-rsp-plus-8; thunk-preserves-frame;
         thunk-preserves-code; thunk-preserves-heap;
         thunk-preserves-above-entry-rsp)

open import Data.Nat using (_>_; _≥_; _≤_; _∸_) renaming (_+_ to _+ℕ'_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; m∸n≤m; ≤-trans; m+n∸n≡m; m∸n+n≡m; m≤m+n; ∸-+-assoc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- run-apply-with-wf: Apply using ClosureWellFormed
------------------------------------------------------------------------

-- | Execute apply with a well-formedness proof for the closure
--
-- KEY INSIGHT: Apply receives a pair (closure, arg) where:
-- - closure = address pointing to (env-addr, code-ptr)
-- - arg = encoded argument value
--
-- The ClosureWellFormed proof tells us that executing from code-ptr
-- with r12=env-addr and rdi=arg produces the correct result.
--
-- Proof structure:
-- 1. Trace 5 setup instructions (load closure, env, code-ptr, arg)
-- 2. Trace call instruction (pushes return address, jumps to code-ptr)
-- 3. Use thunk-correct from ClosureWellFormed
-- 4. Thunk returns to offset+6 with result in rax
-- 5. Compose via star-trans

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
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (apply {A} {B})) →
  -- Region proof: rdi is in heap (for heap-stack disjointness)
  -- Replaces rdi-eq - we only need the region, not the exact encode equality
  InHeap (readReg (regs s) rdi) →
  -- Region proof: closure-addr is in heap (for heap-stack disjointness)
  InHeap closure-addr →
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
          × StackCapacity s' 3  -- Capacity after push (was rsp > slots 2)
          -- NEW: original r15 is saved on stack (at rsp after push = old rsp - 8)
          × readMem (memory s') (readReg (regs s') rsp) ≡ just (readReg (regs s) r15)
          -- RSP tracking: s'.rsp = s.rsp - 8 (push decrements by 8)
          × readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slot-size
          -- Memory preservation: addresses >= orig-rsp are not written by setup
          × (∀ addr → addr ≥ readReg (regs s) rsp →
             readMem (memory s') addr ≡ readMem (memory s) addr))
apply-setup-star {A} {B} prefix suffix code-ptr env-addr closure-addr arg-addr s
                 h-false pc-eq stack-inv cap rdi-in-heap closure-in-heap mem-cl mem-arg mem-env mem-cp code-ptr<len =
  s6 , star-all , h6 , pc6 , rdi6 , r12-6 , r15-6 , r14-6 , rbp6 , stack-inv6 , rsp-sufficient-6 , mem-r15-saved , rsp6 , mem-above-setup
  where
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    offset = length prefix
    old-r15 = readReg (regs s) r15
    old-rsp = readReg (regs s) rsp
    new-rsp = old-rsp ∸ slot-size

    -- Extract rsp-bound from cap for internal use (cap : StackCapacity s 4 gives > slots 4)
    -- Derive > slots 2 for helpers that need weaker bound
    open import Data.Nat.Properties using (≤-<-trans; m≤m+n)
    rsp-bound : readReg (regs s) rsp > slots 2
    rsp-bound = ≤-<-trans (slots-mono-≤ (m≤m+n 2 2)) (StackCapacity.rsp-sufficient cap)

    -- D041: Stack region proof for new-rsp (uses cap directly, no postulate!)
    new-rsp-in-stack : InStack new-rsp
    new-rsp-in-stack = abstract-to-rsp-slot-in-stack s cap

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

    -- Memory at rdi is preserved after push (stack vs heap disjointness)
    -- Uses rdi-in-heap directly (no encode needed!)
    stack-heap-disjoint-rdi : new-rsp ≢ readReg (regs s) rdi
    stack-heap-disjoint-rdi eq =
      -- eq : new-rsp ≡ rdi
      -- new-rsp is in stack, rdi is in heap → contradiction
      stack-heap-addr-disjoint new-rsp (readReg (regs s) rdi) new-rsp-in-stack rdi-in-heap eq

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
    -- rsi = encode arg (read from [rdi+8])
    rdi-s2 : readReg (regs s2) rdi ≡ readReg (regs s) rdi
    rdi-s2 = trans (readReg-writeReg-r15-rdi (regs s1) closure-addr) rdi-s1

    -- Memory at rdi+8 is preserved after push (stack vs heap disjointness)
    -- Uses rdi-in-heap + heap-offset (no encode needed!)
    stack-heap-disjoint-rdi+8 : new-rsp ≢ readReg (regs s) rdi +ℕ slot-size
    stack-heap-disjoint-rdi+8 eq =
      -- eq : new-rsp ≡ rdi + 8
      -- new-rsp is in stack, rdi+8 is in heap (via heap-offset) → contradiction
      let rdi+8-in-heap = heap-offset (readReg (regs s) rdi) slot-size rdi-in-heap
      in stack-heap-addr-disjoint new-rsp (readReg (regs s) rdi +ℕ slot-size) new-rsp-in-stack rdi+8-in-heap eq

    -- Memory at closure-addr is preserved (stack vs heap disjointness)
    -- Uses closure-in-heap directly (no encode derivation needed!)
    stack-heap-disjoint-closure : new-rsp ≢ closure-addr
    stack-heap-disjoint-closure eq =
      -- new-rsp is in stack, closure-addr is in heap → contradiction
      stack-heap-addr-disjoint new-rsp closure-addr new-rsp-in-stack closure-in-heap eq

    stack-heap-disjoint-closure+8 : new-rsp ≢ closure-addr +ℕ slot-size
    stack-heap-disjoint-closure+8 eq =
      -- new-rsp is in stack, closure-addr+8 is in heap (via heap-offset) → contradiction
      let closure+8-in-heap = heap-offset closure-addr slot-size closure-in-heap
      in stack-heap-addr-disjoint new-rsp (closure-addr +ℕ slot-size) new-rsp-in-stack closure+8-in-heap eq

    -- memory s2 = memory s1 = writeMem (memory s) new-rsp old-r15
    -- Since s2 = s1 with only regs changed, memory s2 = memory s1
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
    -- r12 = env-addr (read from [r15] where r15=closure-addr)
    r15-s2 : readReg (regs s2) r15 ≡ closure-addr
    r15-s2 = readReg-writeReg-same (regs s1) r15 closure-addr

    r15-s3 : readReg (regs s3) r15 ≡ closure-addr
    r15-s3 = trans (readReg-writeReg-rsi-r15 (regs s2) arg-addr) r15-s2

    -- memory s3 = memory s2 = memory s1 = writeMem (memory s) new-rsp old-r15
    -- Since new-rsp ≢ closure-addr, readMem at closure-addr is preserved
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
    -- r15 = code-ptr (read from [r15+8] where old r15=closure-addr)
    r15-s4-old : readReg (regs s4) r15 ≡ closure-addr
    r15-s4-old = trans (readReg-writeReg-r12-r15 (regs s3) env-addr) r15-s3

    -- memory s4 = ... = writeMem (memory s) new-rsp old-r15
    -- Since new-rsp ≢ closure-addr+8, readMem at closure-addr+8 is preserved
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
    -- rdi = rsi = arg-addr
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
    -- After setup, r15 = code-ptr which is in the code region
    -- We use r15-in-code since code-ptr < length prog
    stack-inv6 : StackInvariant s6
    stack-inv6 = stack-inv-for-code-ptr s6 (length prog) r15<len
      where
        r15<len : readReg (regs s6) r15 < length prog
        r15<len = subst (_< length prog) (sym r15-6) code-ptr<len

    -- Derive StackCapacity s6 3 from input cap : StackCapacity s (ir-stack-requirement apply) via push
    rsp-sufficient-6 : StackCapacity s6 3
    rsp-sufficient-6 = capacity-after-push s s6 3 cap rsp6'
      where
        -- rsp6 proves s6.rsp = new-rsp, and new-rsp = old-rsp ∸ slot-size = s.rsp ∸ slot-size
        rsp6' : readReg (regs s6) rsp ≡ readReg (regs s) rsp ∸ slot-size
        rsp6' = rsp6  -- new-rsp = old-rsp ∸ slot-size by definition

    -- Memory preservation: original r15 is saved at new-rsp
    mem-r15-saved : readMem (memory s6) (readReg (regs s6) rsp) ≡ just old-r15
    mem-r15-saved = subst (λ addr → readMem (memory s6) addr ≡ just old-r15)
                          (sym rsp6)
                          (trans (mem-read-write {memory s} {new-rsp} {old-r15})
                                 refl)

    -- Memory preservation for addresses >= old-rsp
    -- D041: Use abstract helper for 1-slot allocation disjointness
    mem-above-setup : ∀ addr → addr ≥ old-rsp → readMem (memory s6) addr ≡ readMem (memory s) addr
    mem-above-setup addr addr≥rsp =
      readMem-writeMem-diff (memory s) new-rsp addr old-r15
        (apply-alloc-diff-from-above s rsp-bound addr addr≥rsp)

-- Prove call instruction: pushes return address and jumps to code-ptr
-- Takes StackCapacity s apply-cap-after-push to produce StackCapacity s' apply-cap-after-call (for thunk)
apply-call-star : ∀ {A B} (prefix suffix : Program)
                  (code-ptr : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
      ret-addr = offset +ℕ 7  -- Updated: call at 6, return at 7
  in
  halted s ≡ false →
  pc s ≡ offset +ℕ 6 →  -- Updated: setup ends at 6
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
          × StackCapacity s' apply-cap-after-call  -- Capacity after call (for thunk)
          -- RSP tracking: call pushes return address (rsp -= 8)
          × readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slot-size
          -- Memory preservation at original rsp (call writes at new-rsp, not old-rsp)
          × readMem (memory s') (readReg (regs s) rsp) ≡ readMem (memory s) (readReg (regs s) rsp)
          -- General memory preservation for addresses >= s.rsp
          × (∀ addr → addr ≥ readReg (regs s) rsp →
             readMem (memory s') addr ≡ readMem (memory s) addr)
          -- Memory at code-region preserved (D041: call writes to stack, disjoint from code)
          × (∀ addr → InCode addr →
             readMem (memory s') addr ≡ readMem (memory s) addr)
          -- Memory at heap-region preserved (D041: call writes to stack, disjoint from heap)
          × (∀ addr → InHeap addr →
             readMem (memory s') addr ≡ readMem (memory s) addr))
apply-call-star {A} {B} prefix suffix code-ptr s h-false pc-eq r15-eq stack-inv cap =
  s1 , star-all , h1 , pc1 , mem1 , rdi1 , r12-1 , r14-1 , rbp1 , stack-inv1 , rsp-sufficient-1 , rsp1-eq , mem-preserved-old-rsp , mem-above-call , mem-code-call , mem-heap-call
  where
    open import Data.Nat.Properties using (≤-<-trans; m≤m+n)

    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    offset = length prefix
    ret-addr = offset +ℕ 7  -- Updated

    -- Extract rsp-bound from cap for internal use (cap : StackCapacity s apply-cap-after-push gives > slots 3)
    -- Used where > slots 2 suffices (slots 3 > slots 2)
    rsp-bound : readReg (regs s) rsp > slots apply-cap-after-call
    rsp-bound = ≤-<-trans (slots-mono-≤ (m≤m+n 2 1)) (StackCapacity.rsp-sufficient cap)

    -- The call instruction (now i6)
    i6 = call (reg r15)

    -- compile-x86 apply = push r15 ∷ mov ... (5 movs) ∷ call r15 ∷ pop r15 ∷ []
    -- So instruction 6 is call at offset+6
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

    -- Memory at new rsp contains return address = pc s + 1 = (offset+6)+1 = offset+7
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

    -- StackInvariant after call: r15 unchanged, rsp decreased
    -- new-rsp = old-rsp ∸ slot-size ≤ old-rsp, and rsp1 proves s1.rsp = new-rsp
    stack-inv1 : StackInvariant s1
    stack-inv1 = stack-inv-preserved-r15-unchanged s s1 stack-inv r15-1 rsp1≤
      where
        open import Data.Nat.Properties using (m∸n≤m)
        rsp1≤ : readReg (regs s1) rsp ≤ readReg (regs s) rsp
        rsp1≤ = subst (_≤ old-rsp) (sym rsp1) (m∸n≤m old-rsp slot-size)

    -- RSP tracking: s1.rsp = new-rsp = old-rsp ∸ slot-size = s.rsp ∸ slot-size
    rsp1-eq : readReg (regs s1) rsp ≡ readReg (regs s) rsp ∸ slot-size
    rsp1-eq = rsp1  -- rsp1 proves s1.rsp = new-rsp, and new-rsp = old-rsp ∸ slot-size = s.rsp ∸ slot-size

    -- Derive StackCapacity s1 apply-cap-after-call from input cap via call (push ret addr)
    rsp-sufficient-1 : StackCapacity s1 apply-cap-after-call
    rsp-sufficient-1 = capacity-after-push s s1 apply-cap-after-call cap rsp1-eq

    -- Memory at original rsp preserved (call writes at new-rsp = old-rsp - 8, not old-rsp)
    -- Since old-rsp > slots 2, we have old-rsp > 8, so old-rsp - 8 ≠ old-rsp
    -- D041: Use abstract helper from StackInvariant
    old-rsp≢new-rsp : old-rsp ≢ new-rsp
    old-rsp≢new-rsp = apply-rsp-diff-from-alloc s rsp-bound

    mem-preserved-old-rsp : readMem (memory s1) old-rsp ≡ readMem (memory s) old-rsp
    mem-preserved-old-rsp = readMem-writeMem-diff (memory s) new-rsp old-rsp (pc s +ℕ 1)
                              (λ eq → old-rsp≢new-rsp (sym eq))

    -- General memory preservation for addresses >= s.rsp
    -- Call writes at new-rsp = old-rsp - 8. For addr >= old-rsp, addr > new-rsp.
    -- D041: Use abstract helper from StackInvariant
    mem-above-call : ∀ addr → addr ≥ old-rsp → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-above-call addr addr≥rsp =
      readMem-writeMem-diff (memory s) new-rsp addr (pc s +ℕ 1)
        (apply-alloc-diff-from-above s rsp-bound addr addr≥rsp)

    -- Shared: write address is in stack region (D041: uses cap directly, no postulate!)
    write-addr-in-stack-call : InStack new-rsp
    write-addr-in-stack-call = abstract-to-rsp-slot-in-stack s cap

    -- Memory at code-region addresses preserved (D041: use abstract interface)
    mem-code-call : ∀ addr → InCode addr → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-code-call addr addr-in-code = stackAddr-write-preserves-code (memory s) new-rsp (pc s +ℕ 1) addr write-addr-in-stack-call addr-in-code

    -- Memory at heap-region addresses preserved (D041: use abstract interface)
    mem-heap-call : ∀ addr → InHeap addr → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-heap-call addr addr-in-heap = stackAddr-write-preserves-heap (memory s) new-rsp (pc s +ℕ 1) addr write-addr-in-stack-call addr-in-heap

------------------------------------------------------------------------
-- ApplyPopResult: Record type for pop r15 results (avoids nested tuples)
------------------------------------------------------------------------

record ApplyPopResult {A B : Type} (prefix suffix : Program)
                      (old-r15 orig-rsp : ℕ) (s s' : State) : Set where
  private
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
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
    rsp-sufficient-pop   : readReg (regs s') rsp > slots 2
    rsp-restored : readReg (regs s') rsp ≡ orig-rsp  -- RSP restored to original
    -- Pop doesn't write memory, so all memory is preserved
    mem-pop-preserved : memory s' ≡ memory s

open ApplyPopResult public

-- | R15OrigInfo: Information about r15 for pop reconstruction
-- Three cases corresponding to StackInvariant constructors (slot-based)
data R15OrigInfo (old-r15 orig-rsp : ℕ) : Set where
  r15-was-in-heap  : InHeap old-r15 → R15OrigInfo old-r15 orig-rsp
  r15-was-in-code  : InCode old-r15 → R15OrigInfo old-r15 orig-rsp
  r15-was-in-stack : (frame : StackPointer) →
                     (slot : ℕ) →
                     old-r15 ≡ slot-addr frame slot →
                     sp-addr frame ≥ orig-rsp →
                     R15OrigInfo old-r15 orig-rsp

-- | Trace pop r15 instruction at the end of apply
-- This restores r15 to its original value (saved at start by push r15)
apply-pop-star : ∀ {A B} (prefix suffix : Program)
                 (old-r15 orig-rsp : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
  in
  halted s ≡ false →
  pc s ≡ offset +ℕ 7 →
  readMem (memory s) (readReg (regs s) rsp) ≡ just old-r15 →
  readReg (regs s) rsp ≡ orig-rsp ∸ slot-size →
  R15OrigInfo old-r15 orig-rsp →  -- Changed from disjunction to R15OrigInfo
  readReg (regs s) rsp > slots 2 →
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
    ; mem-pop-preserved = refl  -- s1 only modifies regs and pc, not memory
    }
  where
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
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

    -- StackInvariant for apply pop result
    -- Proven using original invariant information (orig-inv)
    --
    -- Key facts:
    -- - s1.r15 = old-r15 (proven by r15-1)
    -- - s1.rsp = new-rsp = old-rsp + 8 = (orig-rsp - 8) + 8 = orig-rsp
    --   (where old-rsp = s.rsp = orig-rsp - 8 by rsp-eq)
    --
    -- Case orig-inv:
    -- - r15-was-in-heap: use r15-in-heap
    -- - r15-was-in-code: use r15-in-code
    -- - r15-was-in-stack: s1.rsp = orig-rsp ≤ old-r15 = s1.r15

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
        -- Need 8 ≤ orig-rsp for m∸n+n≡m
        -- From rsp-sufficient : s.rsp > slots 2, and rsp-eq : s.rsp = orig-rsp - 8
        -- So orig-rsp - 8 > 16, hence orig-rsp > 24 ≥ 8
        open import Data.Nat using (s≤s; z≤n)
        open import Data.Nat.Properties using (<⇒≤; m∸n≤m)

        -- s.rsp ≤ orig-rsp because s.rsp = orig-rsp - 8 ≤ orig-rsp
        s-rsp≤orig : readReg (regs s) rsp ≤ orig-rsp
        s-rsp≤orig = subst (_≤ orig-rsp) (sym rsp-eq) (m∸n≤m orig-rsp slot-size)

        -- Note: rsp-sufficient : s.rsp > slots 2 = 17 ≤ s.rsp (m > n = suc n ≤ m)
        -- So we can use it directly without <⇒≤
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
          -- frame, slot: unchanged
          -- r15-eq': s1.r15 ≡ slot-addr frame slot
          --   from r15-1 : s1.r15 ≡ old-r15 and r15-eq : old-r15 ≡ slot-addr frame slot
          -- frame-bound': sp-addr frame ≥ s1.rsp
          --   from frame-bound : sp-addr frame ≥ orig-rsp and rsp1-eq-orig : s1.rsp ≡ orig-rsp
          r15-in-stack frame slot (trans r15-1 r15-eq)
                       (subst (sp-addr frame ≥_) (sym rsp1-eq-orig) frame-bound)

    -- Derive rsp-sufficient-1 from preconditions (no postulate!)
    -- s.rsp = orig-rsp - 8 and s.rsp > slots 2
    -- orig-rsp ≥ s.rsp (since m ∸ n ≤ m), and s.rsp ≥ 17 (from s.rsp > slots 2 = 16)
    -- By transitivity: orig-rsp ≥ 17 = suc (slots 2), i.e., orig-rsp > slots 2
    -- s1.rsp = orig-rsp (after pop restores)
    rsp-sufficient-1 : readReg (regs s1) rsp > slots 2
    rsp-sufficient-1 = subst (_> slots 2) (sym rsp1-eq-orig) orig-rsp>slots2
      where
        open import Data.Nat.Properties using (≤-trans; m∸n≤m)
        -- rsp-sufficient : s.rsp > slots 2 = slots 2 < s.rsp = suc (slots 2) ≤ s.rsp = 17 ≤ s.rsp
        -- orig-rsp ≥ s.rsp (since s.rsp = orig-rsp ∸ 8 ≤ orig-rsp by m∸n≤m)
        orig-rsp≥s-rsp : orig-rsp ≥ readReg (regs s) rsp
        orig-rsp≥s-rsp = subst (orig-rsp ≥_) (sym rsp-eq) (m∸n≤m orig-rsp slot-size)

        -- By transitivity: 17 ≤ s.rsp ≤ orig-rsp, so 17 ≤ orig-rsp
        -- 17 ≤ orig-rsp is suc (slots 2) ≤ orig-rsp = slots 2 < orig-rsp = orig-rsp > slots 2
        orig-rsp>slots2 : orig-rsp > slots 2
        orig-rsp>slots2 = ≤-trans rsp-sufficient orig-rsp≥s-rsp

------------------------------------------------------------------------
-- ApplyWfResult: Record type for run-apply-with-wf results
------------------------------------------------------------------------

record ApplyWfResult {A B : Type} (prefix suffix : Program)
                     (semantics : ⟦ A ⟧ → ⟦ B ⟧) (arg : ⟦ A ⟧)
                     (s s' : State) : Set where
  private
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    offset = length prefix
  field
    star         : Star prog s s'
    h-final      : halted s' ≡ false
    pc-final     : pc s' ≡ offset +ℕ compile-length (apply {A} {B})
    -- Validity-based result (no encode!)
    rax-valid    : ValidAt (semantics arg) (readReg (regs s') rax) (memory s')
    r14-final    : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-final    : readReg (regs s') r15 ≡ readReg (regs s) r15
    rbp-final    : readReg (regs s') rbp ≡ readReg (regs s) rbp
    stack-inv    : StackInvariant s'
    rsp-sufficient : readReg (regs s') rsp > slots 2
    rsp-restored : readReg (regs s') rsp ≡ readReg (regs s) rsp
    mem-above    : ∀ addr → addr ≥ readReg (regs s) rsp →
                   readMem (memory s') addr ≡ readMem (memory s) addr
    -- Memory at code-region addresses is preserved (for r15-in-code case)
    mem-code-region : ∀ addr → InCode addr →
                      readMem (memory s') addr ≡ readMem (memory s) addr
    -- Memory at heap-region addresses is preserved (for r15-in-heap case)
    mem-heap-region : ∀ addr → InHeap addr →
                      readMem (memory s') addr ≡ readMem (memory s) addr

open ApplyWfResult public

-- | run-apply-with-wf: Full apply execution with ClosureWellFormed
-- E is the env type, env is the captured environment value
-- Takes StackCapacity s (apply-consumed-slots + wf.thunk-capacity) for capacity threading
-- This is a dynamic capacity requirement that depends on the closure being applied
run-apply-with-wf : ∀ {E A B} (prefix suffix : Program)
                    (code-ptr : ℕ) (env : ⟦ E ⟧)
                    (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                    (arg : ⟦ A ⟧) (arg-addr : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
      cl = record { env-addr = encode env ; semantics = semantics }
  in
  (wf : ClosureWellFormed {E} {A} {B} prog code-ptr env semantics) →
  halted s ≡ false →
  pc s ≡ offset →
  StackInvariant s →
  StackCapacity s (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf) →
  -- Key: ValidAt for input pair (replaces rdi-eq for heap-stack separation)
  ValidAt {(A ⇒ B) * A} (cl , arg) (readReg (regs s) rdi) (memory s) →
  (∃[ closure-addr ] (
    readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr ×
    readMem (memory s) (readReg (regs s) rdi +ℕ slot-size) ≡ just arg-addr ×
    readMem (memory s) closure-addr ≡ just (encode env) ×
    readMem (memory s) (closure-addr +ℕ slot-size) ≡ just code-ptr)) →
  -- Validity-based argument (for thunk-correct)
  ValidAt arg arg-addr (memory s) →
  -- Validity-based environment (for thunk-correct)
  ValidAt env (encode env) (memory s) →
  ∃[ s' ] ApplyWfResult {A} {B} prefix suffix semantics arg s s'
run-apply-with-wf {E} {A} {B} prefix suffix code-ptr env semantics arg arg-addr s
                  wf h-eq pc-eq stack-inv cap input-valid (closure-addr , mem-cl , mem-arg , mem-env , mem-cp) v-arg v-env =
  s-final , record
    { star         = star-all
    ; h-final      = h-f
    ; pc-final     = pc-f
    ; rax-valid    = rax-valid-f
    ; r14-final    = r14-f
    ; r15-final    = r15-f
    ; rbp-final    = rbp-f
    ; stack-inv    = stack-inv-f
    ; rsp-sufficient = rsp-sufficient-f
    ; rsp-restored = rsp-restored-f
    ; mem-above    = mem-above-f
    ; mem-code-region = mem-code-region-f
    ; mem-heap-region = mem-heap-region-f
    }
  where
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    offset = length prefix
    ret-addr = offset +ℕ 7  -- Updated: thunk returns to pop r15 instruction
    old-r15 = readReg (regs s) r15
    -- Construct the closure from its components (env-addr = encode env)
    env-addr = encode env
    cl : Closure A B
    cl = record { env-addr = env-addr ; semantics = semantics }

    -- Step 1: Trace 6 setup instructions (push + 5 movs)
    -- Derive region proofs from input-valid for heap-stack disjointness
    pair : ⟦ (A ⇒ B) * A ⟧
    pair = (cl , arg)

    -- rdi-in-heap derived directly from input validity
    rdi-in-heap : InHeap (readReg (regs s) rdi)
    rdi-in-heap = valid-in-heap input-valid

    -- Decompose input validity to get closure validity
    -- valid-pair-decompose gives us component validities + PairAtS
    decomp = valid-pair-decompose input-valid
    closure-addr' = proj₁ decomp
    arg-addr' = proj₁ (proj₂ decomp)
    v-cl-decomp = proj₁ (proj₂ (proj₂ decomp))
    v-arg-decomp = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
    pair-at-decomp = proj₂ (proj₂ (proj₂ (proj₂ decomp)))

    -- closure-addr' from decomposition equals closure-addr from memory layout
    -- Both are the value at mem[rdi]
    closure-addr'-eq : closure-addr' ≡ closure-addr
    closure-addr'-eq = just-injective (trans (sym (fst-valid-s pair-at-decomp)) mem-cl)

    -- Transport validity along the address equality
    v-cl : ValidAt {A ⇒ B} cl closure-addr (memory s)
    v-cl = subst (λ a → ValidAt cl a (memory s)) closure-addr'-eq v-cl-decomp

    -- closure-in-heap derived from closure validity
    closure-in-heap : InHeap closure-addr
    closure-in-heap = valid-in-heap v-cl

    -- Extract rsp-bound from cap for internal use
    -- cap : StackCapacity s (apply-consumed-slots + wf.thunk-capacity) gives > slots (2 + thunk-cap)
    -- Derive > slots 2 for helpers that need weaker bound (since 2 ≤ 2 + thunk-cap)
    open import Data.Nat.Properties using (≤-<-trans; m≤m+n)
    rsp-bound : readReg (regs s) rsp > slots 2
    rsp-bound = ≤-<-trans (slots-mono-≤ (m≤m+n 2 (ClosureWellFormed.thunk-capacity wf))) (StackCapacity.rsp-sufficient cap)

    -- Derive StackCapacity s 4 for apply-setup-star
    -- cap : StackCapacity s (2 + wf.thunk-capacity) where wf.thunk-capacity ≥ 6 (from thunk-capacity-sufficient)
    -- So 2 + wf.thunk-capacity ≥ 2 + 6 = 8 ≥ 4
    open import Once.Backend.X86.Correct.StackInstantiation using (capacity-from-larger; thunk-setup-capacity)
    open import Data.Nat.Properties using (+-monoʳ-≤)
    -- 4 ≤ apply-consumed-slots + thunk-setup-capacity = 2 + 6 = 8
    four≤apply-consumed+thunk-setup : 4 ≤ apply-consumed-slots +ℕ thunk-setup-capacity
    four≤apply-consumed+thunk-setup = s≤s (s≤s (s≤s (s≤s z≤n)))
    -- 2 + 6 ≤ 2 + wf.thunk-capacity (since wf.thunk-capacity ≥ 6)
    apply-consumed+thunk-setup≤cap : apply-consumed-slots +ℕ thunk-setup-capacity ≤ apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf
    apply-consumed+thunk-setup≤cap = +-monoʳ-≤ apply-consumed-slots (ClosureWellFormed.thunk-capacity-sufficient wf)
    cap-for-setup : StackCapacity s (ir-stack-requirement (apply {A} {B}))
    cap-for-setup = capacity-from-larger s 4 (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf) cap
                      (≤-trans four≤apply-consumed+thunk-setup apply-consumed+thunk-setup≤cap)

    -- Step 1: Setup phase (now takes StackCapacity s (ir-stack-requirement apply), outputs StackCapacity s-setup 3)
    setup-result = apply-setup-star {A} {B} prefix suffix code-ptr env-addr closure-addr arg-addr s
                     h-eq pc-eq stack-inv cap-for-setup rdi-in-heap closure-in-heap mem-cl mem-arg mem-env mem-cp (code-ptr-valid wf)
    s-setup = proj₁ setup-result
    star-setup = proj₁ (proj₂ setup-result)
    h-setup = proj₁ (proj₂ (proj₂ setup-result))
    pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
    rdi-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
    r12-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
    r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
    r14-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
    rbp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))
    stack-inv-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))
    rsp-sufficient-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))
    mem-r15-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))))))
    -- RSP tracking: s-setup.rsp = s.rsp - 8
    rsp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))))
    -- Memory preservation for addresses >= orig-rsp
    mem-above-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))))))))

    -- Step 2: Trace call instruction
    -- rsp-sufficient-setup is StackCapacity s-setup apply-cap-after-push (from apply-setup-star)
    -- apply-call-star takes that and produces StackCapacity s-call apply-cap-after-call
    call-result = apply-call-star {A} {B} prefix suffix code-ptr s-setup
                    h-setup pc-setup r15-setup stack-inv-setup rsp-sufficient-setup
    s-call = proj₁ call-result
    star-call = proj₁ (proj₂ call-result)
    h-call = proj₁ (proj₂ (proj₂ call-result))
    pc-call = proj₁ (proj₂ (proj₂ (proj₂ call-result)))
    mem-ret = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))
    rdi-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))
    r12-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))
    r14-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))))
    rbp-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))))
    stack-inv-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))))))
    rsp-sufficient-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))))))
    -- RSP tracking: s-call.rsp = s-setup.rsp - 8
    rsp-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))))))))
    -- Memory at s-setup.rsp preserved through call (call writes at s-call.rsp, not s-setup.rsp)
    mem-call-preserved = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))))))))
    -- General memory preservation for addresses >= s-setup.rsp
    mem-above-call = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result)))))))))))))
    -- Memory at code-region addresses preserved through call (D041)
    mem-code-call-phase = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))))))))))
    -- Memory at heap-region addresses preserved through call (D041)
    mem-heap-call-phase = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ call-result))))))))))))))

    -- Step 3: Use thunk-correct from ClosureWellFormed
    -- The thunk executes and returns to ret-addr (offset+7) with result in rax

    -- Derive validity-based arg proof for thunk-correct
    -- We have v-arg : ValidAt arg arg-addr (memory s)
    -- We need: ValidAt arg (readReg (regs s-call) rdi) (memory s-call)
    -- Chain: s-call.rdi = s-setup.rdi = arg-addr, heap preserved from s to s-call

    -- Address chain: s-call.rdi ≡ arg-addr
    rdi-for-thunk : readReg (regs s-call) rdi ≡ arg-addr
    rdi-for-thunk = trans rdi-call rdi-setup

    -- Heap preservation through setup: setup only writes to stack (push)
    -- Using D041 region-based disjointness
    --
    -- Setup phase: memory s-setup = writeMem (memory s) (rsp-8) old-r15
    -- The write address (rsp-8) is in stack region, so heap is preserved
    setup-write-in-stack : InStack (readReg (regs s) rsp ∸ slot-size)
    setup-write-in-stack = abstract-to-rsp-slot-in-stack s cap

    heap-pres-setup : ∀ a → InHeap a →
                      readMem (memory s-setup) a ≡ readMem (memory s) a
    heap-pres-setup a a-in-heap =
      stackAddr-write-preserves-heap (memory s) (readReg (regs s) rsp ∸ slot-size) old-r15 a
        setup-write-in-stack a-in-heap

    -- Compose: heap preserved from s to s-call
    heap-pres-s-to-call : ∀ a → InHeap a →
                          readMem (memory s-call) a ≡ readMem (memory s) a
    heap-pres-s-to-call a a-in-heap = trans (mem-heap-call-phase a a-in-heap)
                                            (heap-pres-setup a a-in-heap)

    -- Validity at s-call: propagate using heap preservation
    arg-valid-at-call : ValidAt arg (readReg (regs s-call) rdi) (memory s-call)
    arg-valid-at-call = valid-subst-heap-preserved v-arg (sym rdi-for-thunk) heap-pres-s-to-call

    r12-for-thunk : readReg (regs s-call) r12 ≡ env-addr
    r12-for-thunk = trans r12-call r12-setup

    -- Validity for env at s-call: propagate using heap preservation
    env-valid-at-call : ValidAt env (readReg (regs s-call) r12) (memory s-call)
    env-valid-at-call = valid-subst-heap-preserved v-env (sym r12-for-thunk) heap-pres-s-to-call

    -- Construct apply-sp : StackPointer for apply's frame
    -- This is where old-r15 was pushed (at s-setup.rsp)
    -- Internal arithmetic, but abstract interface!
    apply-sp : StackPointer
    apply-sp = record
      { addr = readReg (regs s-setup) rsp
      ; in-stack = abstract-to-rsp-slot-in-stack s cap
      }

    -- D041: Prove caller-sp bound for thunk-correct
    -- apply-sp.addr = s-setup.rsp = s-call.rsp + 8
    -- Inline proof: s-call.rsp = s-setup.rsp - 8, so s-call.rsp + 8 = s-setup.rsp
    apply-sp-bound : StackPointer.addr apply-sp ≡ readReg (regs s-call) rsp +ℕ slot-size
    apply-sp-bound = sym (trans (cong (_+ℕ slot-size) rsp-call) (m∸n+n≡m 8≤setup))
      where
        open import Data.Nat.Properties using (<⇒≤; m∸n+n≡m; m≤m+n)
        -- rsp > slots 3 = 24, so 24 ≤ rsp. Since 8 ≤ 8+16 = 24, we get 8 ≤ rsp
        8≤setup : 8 ≤ readReg (regs s-setup) rsp
        8≤setup = ≤-trans (m≤m+n 8 16) (<⇒≤ (StackCapacity.rsp-sufficient rsp-sufficient-setup))

    -- Proof: r15 is in code region at s-call
    -- Chain: s-call.r15 = s-setup.r15 = code-ptr < length prog
    r15-call-in-code : InCode (readReg (regs s-call) r15)
    r15-call-in-code = pc-in-code (readReg (regs s-call) r15) (length prog) r15-call<len
      where
        -- Call preserves r15 (only modifies rsp, pc, and memory)
        -- apply-call-star constructs s1 with regs = writeReg (regs s) rsp new-rsp
        -- So readReg (regs s-call) r15 = readReg (regs s-setup) r15
        r15-call-eq-setup : readReg (regs s-call) r15 ≡ readReg (regs s-setup) r15
        r15-call-eq-setup = refl  -- s-call.regs differs from s-setup.regs only in rsp
        -- Chain: s-call.r15 = s-setup.r15 = code-ptr
        r15-call-eq-code-ptr : readReg (regs s-call) r15 ≡ code-ptr
        r15-call-eq-code-ptr = trans r15-call-eq-setup r15-setup
        -- code-ptr < length prog
        r15-call<len : readReg (regs s-call) r15 < length prog
        r15-call<len = Relation.Binary.PropositionalEquality.subst (_< length prog) (sym r15-call-eq-code-ptr) (code-ptr-valid wf)

    -- Derive StackCapacity s-call (wf.thunk-capacity) from input capacity using capacity-after-delta
    -- Input: cap : StackCapacity s (apply-consumed-slots + wf.thunk-capacity)
    -- After setup+call consumes apply-consumed-slots (2), we have wf.thunk-capacity remaining
    -- RSP delta: s-call.rsp = s.rsp - slots apply-consumed-slots
    rsp-delta-to-call : readReg (regs s-call) rsp ≡ readReg (regs s) rsp ∸ slots apply-consumed-slots
    rsp-delta-to-call = trans rsp-call (trans (cong (_∸ slot-size) rsp-setup) (∸-+-assoc (readReg (regs s) rsp) slot-size slot-size))

    cap-for-thunk : StackCapacity s-call (ClosureWellFormed.thunk-capacity wf)
    cap-for-thunk = capacity-after-delta s s-call apply-consumed-slots (ClosureWellFormed.thunk-capacity wf) cap rsp-delta-to-call

    thunk-result = thunk-correct wf arg s-call ret-addr apply-sp
                     h-call pc-call arg-valid-at-call env-valid-at-call mem-ret
                     stack-inv-call cap-for-thunk apply-sp-bound r15-call-in-code
    s-thunk = proj₁ thunk-result
    thunk-res = proj₁ (proj₂ thunk-result)
    pc-thunk = proj₂ (proj₂ thunk-result)
    star-thunk = thunk-star thunk-res

    -- Step 4: Trace pop r15 instruction
    -- Prove that original r15 is still on stack at s-thunk's rsp
    --
    -- Memory chain:
    -- 1. mem-r15-setup: readMem (memory s-setup) s-setup.rsp ≡ just old-r15
    -- 2. Call writes at s-call.rsp = s-setup.rsp - 8, not at s-setup.rsp
    -- 3. thunk-preserves-frame: memory at apply-sp's slots is preserved (abstract!)
    --    apply-sp.addr = s-setup.rsp, so slot 0 = s-setup.rsp is preserved
    -- 4. thunk-rsp-plus-8: s-thunk.rsp = s-call.rsp + 8 = s-setup.rsp
    --
    -- Therefore: readMem (memory s-thunk) s-thunk.rsp = just old-r15

    -- s-thunk.rsp = s-call.rsp + 8 (thunk's ret pops return address)
    rsp-thunk-eq : readReg (regs s-thunk) rsp ≡ readReg (regs s-call) rsp +ℕ slot-size
    rsp-thunk-eq = thunk-rsp-plus-8 thunk-res

    -- s-call.rsp = s-setup.rsp - 8 (call pushes return address)
    -- Therefore: s-call.rsp + 8 = s-setup.rsp (rsp > slots 3 = 24, so 8 ≤ 24 ≤ rsp)
    8≤setup-rsp : 8 ≤ readReg (regs s-setup) rsp
    8≤setup-rsp = ≤-trans (m≤m+n 8 16) (<⇒≤ (StackCapacity.rsp-sufficient rsp-sufficient-setup))
      where
        open import Data.Nat.Properties using (<⇒≤; m≤m+n)

    rsp-call-plus-8-eq : readReg (regs s-call) rsp +ℕ slot-size ≡ readReg (regs s-setup) rsp
    rsp-call-plus-8-eq = trans (cong (_+ℕ slot-size) rsp-call) (m∸n+n≡m 8≤setup-rsp)

    -- s-thunk.rsp = s-setup.rsp
    rsp-thunk-eq-setup : readReg (regs s-thunk) rsp ≡ readReg (regs s-setup) rsp
    rsp-thunk-eq-setup = trans rsp-thunk-eq rsp-call-plus-8-eq

    -- Memory at s-setup.rsp preserved from s-call to s-thunk
    -- Uses abstract thunk-preserves-frame instead of arithmetic thunk-mem-above!
    -- frameSlot mem apply-sp 0 = readMem mem (addr apply-sp) = readMem mem s-setup.rsp
    mem-preserved-thunk : readMem (memory s-thunk) (readReg (regs s-setup) rsp) ≡
                          readMem (memory s-call) (readReg (regs s-setup) rsp)
    mem-preserved-thunk = frame-preservation-as-mem
      where
        -- thunk-preserves-frame gives us frameSlot preservation
        frame-pres : frameSlot (memory s-thunk) apply-sp 0 ≡ frameSlot (memory s-call) apply-sp 0
        frame-pres = thunk-preserves-frame thunk-res 0

        -- Use frameSlot-0-is-top glue to connect abstract to concrete
        -- frameSlot-0-is-top : frameSlot mem sp 0 ≡ readMem mem (addr sp)
        -- addr apply-sp = readReg (regs s-setup) rsp by definition
        frame-preservation-as-mem : readMem (memory s-thunk) (readReg (regs s-setup) rsp) ≡
                                    readMem (memory s-call) (readReg (regs s-setup) rsp)
        frame-preservation-as-mem = begin
          readMem (memory s-thunk) (readReg (regs s-setup) rsp)
            ≡⟨ sym (frameSlot-0-is-top (memory s-thunk) apply-sp) ⟩
          frameSlot (memory s-thunk) apply-sp 0
            ≡⟨ frame-pres ⟩
          frameSlot (memory s-call) apply-sp 0
            ≡⟨ frameSlot-0-is-top (memory s-call) apply-sp ⟩
          readMem (memory s-call) (StackPointer.addr apply-sp)
            ≡⟨⟩  -- addr apply-sp = readReg (regs s-setup) rsp by definition
          readMem (memory s-call) (readReg (regs s-setup) rsp)
          ∎

    -- Call writes at s-call.rsp, not s-setup.rsp. They differ by 8.
    -- Memory at s-setup.rsp preserved from s-setup to s-call
    -- Proven via mem-call-preserved from apply-call-star
    mem-preserved-call : readMem (memory s-call) (readReg (regs s-setup) rsp) ≡
                         readMem (memory s-setup) (readReg (regs s-setup) rsp)
    mem-preserved-call = mem-call-preserved

    -- Chain the memory preservation proofs
    mem-r15-thunk : readMem (memory s-thunk) (readReg (regs s-thunk) rsp) ≡ just old-r15
    mem-r15-thunk = begin
      readMem (memory s-thunk) (readReg (regs s-thunk) rsp)
        ≡⟨ cong (readMem (memory s-thunk)) rsp-thunk-eq-setup ⟩
      readMem (memory s-thunk) (readReg (regs s-setup) rsp)
        ≡⟨ mem-preserved-thunk ⟩
      readMem (memory s-call) (readReg (regs s-setup) rsp)
        ≡⟨ mem-preserved-call ⟩
      readMem (memory s-setup) (readReg (regs s-setup) rsp)
        ≡⟨ mem-r15-setup ⟩
      just old-r15 ∎

    -- Original rsp for threading to apply-pop-star
    orig-rsp = readReg (regs s) rsp

    -- Prove s-thunk.rsp = orig-rsp - 8
    -- Chain: s-thunk.rsp = s-setup.rsp (rsp-thunk-eq-setup) = s.rsp - 8 (rsp-setup)
    rsp-thunk-eq-orig : readReg (regs s-thunk) rsp ≡ orig-rsp ∸ slot-size
    rsp-thunk-eq-orig = trans rsp-thunk-eq-setup rsp-setup

    -- Extract original StackInvariant info as R15OrigInfo
    -- NOW FULLY PROVEN - no postulates needed!
    -- Direct conversion from StackInvariant to R15OrigInfo
    -- old-r15 = s.r15 and orig-rsp = s.rsp, so types align directly
    orig-inv : R15OrigInfo old-r15 orig-rsp
    orig-inv = extract-stack-inv stack-inv
      where
        extract-stack-inv : StackInvariant s → R15OrigInfo old-r15 orig-rsp
        extract-stack-inv (r15-in-heap r15-heap) = r15-was-in-heap r15-heap
        extract-stack-inv (r15-in-code r15-code) = r15-was-in-code r15-code
        extract-stack-inv (r15-in-stack frame slot r15-eq frame-bound) =
          r15-was-in-stack frame slot r15-eq frame-bound

    pop-result = apply-pop-star {A} {B} prefix suffix old-r15 orig-rsp s-thunk
                   (thunk-halted thunk-res) pc-thunk mem-r15-thunk
                   rsp-thunk-eq-orig orig-inv (StackCapacity.rsp-sufficient (thunk-capacity thunk-res))
    s-pop = proj₁ pop-result
    module PopR = ApplyPopResult (proj₂ pop-result)

    -- Final state is after pop
    s-final = s-pop

    -- Compose all Star proofs
    star-all : Star prog s s-final
    star-all = star-trans star-setup (star-trans star-call (star-trans star-thunk PopR.star-pop))

    -- Extract final properties (using record field access)
    h-f = PopR.h-pop
    pc-f = PopR.pc-pop  -- pc = offset + 8 = compile-length apply
    -- Derive rax-valid from thunk-result-valid through pop
    -- thunk-result-valid gives ValidAt at s-thunk, pop preserves rax and memory
    rax-valid-f : ValidAt (semantics arg) (readReg (regs s-final) rax) (memory s-final)
    rax-valid-f = valid-subst-addr-mem (thunk-result-valid thunk-res)
                    (sym PopR.rax-pop)
                    (λ a → cong (λ m → readMem m a) PopR.mem-pop-preserved)
    r14-f = trans PopR.r14-pop (trans (thunk-r14 thunk-res) (trans r14-call r14-setup))
    r15-f = PopR.r15-pop  -- r15 restored to original value!
    rbp-f = trans PopR.rbp-pop (trans (thunk-rbp thunk-res) (trans rbp-call rbp-setup))
    stack-inv-f = PopR.stack-inv-pop
    rsp-sufficient-f = PopR.rsp-sufficient-pop
    rsp-restored-f = PopR.rsp-restored  -- RSP restored to original

    -- Memory preservation for addresses >= orig-rsp (chained through all phases)
    -- For addr >= orig-rsp:
    --   1. mem-above-setup: memory s-setup at addr = memory s at addr
    --   2. mem-above-call: memory s-call at addr = memory s-setup at addr
    --   3. thunk phase: memory s-thunk at addr = memory s-call at addr
    --      (TODO: thread caller-sp to make this fully abstract)
    --   4. PopR.mem-pop-preserved: memory s-pop = memory s-thunk
    -- D041: Use abstract helpers from StackInvariant for memory preservation
    mem-above-f : ∀ addr → addr ≥ orig-rsp → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-above-f addr addr≥rsp =
      trans mem-thunk-to-pop (trans mem-call-to-thunk (trans mem-setup-to-call mem-s-to-setup))
      where
        open import Data.Nat.Properties as NP using (<-≤-trans)

        -- Chain the proofs
        mem-s-to-setup : readMem (memory s-setup) addr ≡ readMem (memory s) addr
        mem-s-to-setup = mem-above-setup addr addr≥rsp

        -- D041: addr >= orig-rsp > orig-rsp - 8 = s-setup.rsp
        addr≥setup-rsp : addr ≥ readReg (regs s-setup) rsp
        addr≥setup-rsp = NP.<⇒≤ (<-≤-trans
          (subst (_< orig-rsp) (sym rsp-setup) (apply-alloc-below-rsp s rsp-bound))
          addr≥rsp)

        mem-setup-to-call : readMem (memory s-call) addr ≡ readMem (memory s-setup) addr
        mem-setup-to-call = mem-above-call addr addr≥setup-rsp

        -- D041: addr >= orig-rsp > (orig-rsp - 8) - 8 = s-call.rsp
        addr>call-rsp : addr > readReg (regs s-call) rsp
        addr>call-rsp = <-≤-trans call-rsp<orig addr≥rsp
          where
            -- s-call.rsp = (orig-rsp ∸ slot-size) ∸ slot-size
            call-rsp-eq : readReg (regs s-call) rsp ≡ (orig-rsp ∸ slot-size) ∸ slot-size
            call-rsp-eq = trans rsp-call (cong (_∸ slot-size) rsp-setup)
            -- s-call.rsp < orig-rsp via abstract helper
            call-rsp<orig : readReg (regs s-call) rsp < orig-rsp
            call-rsp<orig = subst (_< orig-rsp) (sym call-rsp-eq) (apply-double-alloc-below-rsp s rsp-bound)

        -- D041 PROVEN: Use thunk-preserves-above-entry-rsp
        mem-call-to-thunk : readMem (memory s-thunk) addr ≡ readMem (memory s-call) addr
        mem-call-to-thunk = thunk-preserves-above-entry-rsp thunk-res addr addr>call-rsp

        -- s-pop = s-final, and memory s-pop = memory s-thunk (pop doesn't write)
        mem-thunk-to-pop : readMem (memory s-final) addr ≡ readMem (memory s-thunk) addr
        mem-thunk-to-pop = cong (λ m → readMem m addr) PopR.mem-pop-preserved

    -- Shared: Setup write address (rsp - 8) is in stack region (D041: uses cap, no postulate!)
    setup-write-in-stack-f : InStack (readReg (regs s) rsp ∸ slot-size)
    setup-write-in-stack-f = abstract-to-rsp-slot-in-stack s cap

    -- Memory at code-region addresses preserved: chain through all phases
    mem-code-region-f : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-code-region-f addr addr-in-code = trans after-pop (trans after-thunk (trans after-call after-setup))
      where
        after-setup = stackAddr-write-preserves-code (memory s) (readReg (regs s) rsp ∸ slot-size) old-r15 addr setup-write-in-stack-f addr-in-code
        after-call  = mem-code-call-phase addr addr-in-code
        after-thunk = thunk-preserves-code thunk-res addr addr-in-code
        after-pop   = cong (λ m → readMem m addr) PopR.mem-pop-preserved

    -- Memory at heap-region addresses preserved: chain through all phases (D041)
    mem-heap-region-f : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-heap-region-f addr addr-in-heap = trans after-pop (trans after-thunk (trans after-call after-setup))
      where
        after-setup = stackAddr-write-preserves-heap (memory s) (readReg (regs s) rsp ∸ slot-size) old-r15 addr setup-write-in-stack-f addr-in-heap
        after-call  = mem-heap-call-phase addr addr-in-heap
        after-thunk = thunk-preserves-heap thunk-res addr addr-in-heap
        after-pop   = cong (λ m → readMem m addr) PopR.mem-pop-preserved

------------------------------------------------------------------------
-- Converting to IRStarResult format
------------------------------------------------------------------------

-- | Wrapper that produces IRStarResult from run-apply-with-wf
-- Takes StackCapacity s (apply-consumed-slots + wf.thunk-capacity) for capacity threading
run-apply-star-with-wf : ∀ {E A B} (prefix suffix : Program)
                         (code-ptr : ℕ) (env : ⟦ E ⟧)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                         (arg : ⟦ A ⟧) (arg-addr : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
      cl = record { env-addr = encode env ; semantics = semantics }
  in
  (wf : ClosureWellFormed {E} {A} {B} prog code-ptr env semantics) →
  halted s ≡ false →
  pc s ≡ offset →
  StackInvariant s →
  StackCapacity s (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf) →
  -- Key: ValidAt for input pair (replaces rdi-eq)
  ValidAt {(A ⇒ B) * A} (cl , arg) (readReg (regs s) rdi) (memory s) →
  (∃[ closure-addr ] (
    readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr ×
    readMem (memory s) (readReg (regs s) rdi +ℕ slot-size) ≡ just arg-addr ×
    readMem (memory s) closure-addr ≡ just (encode env) ×
    readMem (memory s) (closure-addr +ℕ slot-size) ≡ just code-ptr)) →
  -- Validity-based argument (for thunk-correct)
  ValidAt arg arg-addr (memory s) →
  -- Validity-based environment (for thunk-correct)
  ValidAt env (encode env) (memory s) →
  -- Note: The input type for apply is (closure , arg) but we abstract over semantics
  -- Validity-based return (no encode!)
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ offset +ℕ 8  -- compile-length apply = 8
          × ValidAt (semantics arg) (readReg (regs s') rax) (memory s')
          × StackInvariant s'
          × readReg (regs s') rsp > slots 2)
run-apply-star-with-wf {E} {A} {B} prefix suffix code-ptr env semantics arg arg-addr s
                       wf h-eq pc-eq stack-inv cap input-valid mem-layout v-arg v-env =
  let result = run-apply-with-wf prefix suffix code-ptr env semantics arg arg-addr s
                 wf h-eq pc-eq stack-inv cap input-valid mem-layout v-arg v-env
      s' = proj₁ result
      module R = ApplyWfResult (proj₂ result)
  in s' , R.star , R.h-final , R.pc-final , R.rax-valid , R.stack-inv , R.rsp-sufficient

------------------------------------------------------------------------
-- run-apply-to-ir-result: Produce IRStarResult from ClosureWellFormed
--
-- This function bridges ClosureWellFormed-based apply proof to IRStarResult,
-- enabling elimination of apply-produces-result postulate.
--
-- ALL PROPERTIES NOW FULLY PROVEN (zero local postulates!):
--   - star, halted, pc, rax (from thunk-correct)
--   - r14, r15, rbp (r15 preserved via push/pop!)
--   - stack-inv, rsp > slots 2 (from thunk-correct)
--   - Memory at rbp preserved (via mem-above + RbpInvariant.rsp≤rbp)
--   - Memory at rbp+8 preserved (via mem-above + rsp ≤ rbp ≤ rbp+8)
--   - Memory above rbp preserved (via mem-above + addr > rbp ≥ rsp)
--   - Memory at r15 (all cases via R15OrigInfo + region disjointness)
--   - Memory at code-region preserved (via D041: stack-code-disjoint)
--   - Memory at heap-region preserved (via D041: stack-heap-disjoint)
--   - RbpInvariant preserved (via RSP/RBP restoration)
--
-- Key techniques:
--   - D041 abstract memory regions (stack, heap, code)
--   - regions-disjoint postulate → stack-code-disjoint, stack-heap-disjoint
--   - R15OrigInfo type for clean three-way case split
--   - ThunkResult.thunk-preserves-code/heap for thunk phase
------------------------------------------------------------------------

open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure)
  renaming (ir-star to ir-star'; ir-halted to ir-halted'; ir-pc to ir-pc';
            ir-rax to ir-rax'; ir-r14 to ir-r14'; ir-r15 to ir-r15'; ir-rbp to ir-rbp';
            ir-mem to ir-mem'; ir-mem-rbp to ir-mem-rbp'; ir-mem-rbp+8 to ir-mem-rbp+8';
            ir-mem-above to ir-mem-above'; ir-stack-inv to ir-stack-inv';
            ir-rsp-bound to ir-rsp-bound'; ir-rbp-inv to ir-rbp-inv'; ir-closure-wf to ir-closure-wf')
open import Once.Backend.X86.Correct.StackInvariant using (RbpInvariant)

-- Takes StackCapacity s (apply-consumed-slots + wf.thunk-capacity) for capacity threading
run-apply-to-ir-result : ∀ {E A B} (prefix suffix : Program)
                         (code-ptr : ℕ) (env : ⟦ E ⟧)
                         (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                         (arg : ⟦ A ⟧) (arg-addr : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
      x = (record { env-addr = encode env ; semantics = semantics } , arg)
  in
  (wf : ClosureWellFormed {E} {A} {B} prog code-ptr env semantics) →
  halted s ≡ false →
  pc s ≡ offset →
  -- Key: ValidAt for input pair (replaces rdi-eq)
  ValidAt {(A ⇒ B) * A} x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf) →
  RbpInvariant s →
  (∃[ closure-addr ] (
    readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr ×
    readMem (memory s) (readReg (regs s) rdi +ℕ slot-size) ≡ just arg-addr ×
    readMem (memory s) closure-addr ≡ just (encode env) ×
    readMem (memory s) (closure-addr +ℕ slot-size) ≡ just code-ptr)) →
  -- Validity-based argument (for thunk-correct)
  ValidAt arg arg-addr (memory s) →
  -- Validity-based environment (for thunk-correct)
  ValidAt env (encode env) (memory s) →
  ∃[ s' ] IRStarResultV (apply {A} {B}) prog s s' x offset
run-apply-to-ir-result {E} {A} {B} prefix suffix code-ptr env semantics arg arg-addr s
                       wf h-eq pc-eq input-valid stack-inv cap rbp-inv mem-layout v-arg v-env =
  s' , record
    { ir-star = WfR.star
    ; ir-halted = WfR.h-final
    ; ir-pc = WfR.pc-final
    ; ir-result-valid = WfR.rax-valid  -- Direct validity (no bridge!)
    ; ir-r14 = WfR.r14-final
    ; ir-r15 = WfR.r15-final  -- NOW PROVEN! (via push/pop r15)
    ; ir-rbp = WfR.rbp-final
    ; ir-rsp = WfR.rsp-restored  -- apply: rsp restored (delta = 0)
    ; ir-mem = mem-r15-post  -- NOW PROVEN via R15OrigInfo + region disjointness
    ; ir-mem-rbp = mem-rbp-post  -- PROVEN via WfR.mem-above + RbpInvariant
    ; ir-mem-rbp+8 = mem-rbp+8-post  -- PROVEN via WfR.mem-above + RbpInvariant
    ; ir-mem-above = mem-above-post  -- PROVEN via WfR.mem-above + RbpInvariant
    ; ir-mem-code = WfR.mem-code-region  -- PROVEN via D041 region-based chain
    ; ir-mem-heap = WfR.mem-heap-region  -- PROVEN via D041 region-based chain
    ; ir-stack-inv = WfR.stack-inv
    -- Derive s' capacity from s capacity via rsp-restored (apply restores RSP, delta = 0)
    -- cap : StackCapacity s (apply-consumed-slots + wf.thunk-capacity)
    -- Need: StackCapacity s' (ir-output-capacity apply) = StackCapacity s' 4
    -- First derive StackCapacity s 4 from cap (since 4 ≤ 2 + thunk-capacity when thunk-capacity ≥ 6)
    -- Then transfer to s' via rsp-restored
    ; ir-capacity = capacity-when-rsp-restored s s' (ir-output-capacity (apply {A} {B}))
                      (capacity-from-larger s (ir-output-capacity (apply {A} {B}))
                        (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf) cap
                        output-cap-≤-input-cap)
                      WfR.rsp-restored
    ; ir-rbp-inv = rbp-inv-derived  -- PROVEN via RSP restoration
    ; ir-closure-wf = no-closure  -- apply consumes closure, doesn't produce one
    }
  where
    open import Once.Semantics using (Closure)
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    offset = length prefix
    env-addr = encode env
    x : ⟦ (A ⇒ B) * A ⟧
    x = (record { env-addr = env-addr ; semantics = semantics } , arg)

    -- Use proven run-apply-with-wf
    wf-result = run-apply-with-wf prefix suffix code-ptr env semantics arg arg-addr s
                  wf h-eq pc-eq stack-inv cap input-valid mem-layout v-arg v-env
    s' = proj₁ wf-result
    module WfR = ApplyWfResult (proj₂ wf-result)

    -- Capacity derivation for ir-capacity
    -- ir-output-capacity apply = 4, thunk-capacity ≥ 6, so 4 ≤ 2 + 6 ≤ 2 + thunk-capacity
    open import Once.Backend.X86.Correct.StackInstantiation using (thunk-setup-capacity)
    open import Data.Nat.Properties using (+-monoʳ-≤; ≤-trans)

    four≤apply-consumed+thunk-setup : 4 ≤ apply-consumed-slots +ℕ thunk-setup-capacity
    four≤apply-consumed+thunk-setup = s≤s (s≤s (s≤s (s≤s z≤n)))

    apply-consumed+thunk-setup≤cap : apply-consumed-slots +ℕ thunk-setup-capacity ≤ apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf
    apply-consumed+thunk-setup≤cap = +-monoʳ-≤ apply-consumed-slots (ClosureWellFormed.thunk-capacity-sufficient wf)

    output-cap-≤-input-cap : ir-output-capacity (apply {A} {B}) ≤ apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf
    output-cap-≤-input-cap = ≤-trans four≤apply-consumed+thunk-setup apply-consumed+thunk-setup≤cap

    -- PROVEN: RbpInvariant preserved via RSP restoration and RBP preservation
    -- From: WfR.rsp-restored : s'.rsp ≡ s.rsp
    --       WfR.rbp-final    : s'.rbp ≡ s.rbp
    -- Both rsp and rbp are restored/preserved, so use rbp-inv-preserved-unchanged
    rbp-inv-derived : RbpInvariant s'
    rbp-inv-derived = rbp-inv-preserved-unchanged s s' rbp-inv WfR.rsp-restored WfR.rbp-final

    -- Memory preservation proofs derived from WfR.mem-above
    --
    -- WfR.mem-above : ∀ addr → addr ≥ rsp → mem s' addr ≡ mem s addr
    -- RbpInvariant : rsp ≤ rbp
    --
    -- So for any addr ≥ rsp, memory is preserved. Since rbp ≥ rsp,
    -- memory at rbp, rbp+8, and above rbp are all preserved.

    open import Data.Nat.Properties as NP using (≤-trans; m≤m+n; <⇒≤)

    -- Memory at rbp preserved: rbp ≥ rsp (from RbpInvariant)
    mem-rbp-post : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp-post = WfR.mem-above (readReg (regs s) rbp) (RbpInvariant.rsp≤rbp rbp-inv)

    -- Memory at rbp+8 preserved: rbp+8 ≥ rbp ≥ rsp
    mem-rbp+8-post : readMem (memory s') (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
    mem-rbp+8-post = WfR.mem-above (readReg (regs s) rbp +ℕ slot-size)
                       (≤-trans (RbpInvariant.rsp≤rbp rbp-inv) (m≤m+n (readReg (regs s) rbp) slot-size))

    -- Memory above rbp preserved: addr > rbp ≥ rsp implies addr ≥ rsp
    mem-above-post : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    mem-above-post addr addr>rbp = WfR.mem-above addr (≤-trans (RbpInvariant.rsp≤rbp rbp-inv) (<⇒≤ addr>rbp))

    -- Memory at r15 preserved: depends on StackInvariant
    -- NOW FULLY PROVEN using WfR.mem-code-region and WfR.mem-heap-region
    -- StackInvariant gives: r15 in heap OR r15 in code OR r15 in stack (above rsp)
    -- - If r15 in heap, use WfR.mem-heap-region
    -- - If r15 in code, use WfR.mem-code-region
    -- - If r15 in stack, use WfR.mem-above
    mem-r15-post : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    mem-r15-post = derive-mem-r15 stack-inv
      where
        derive-mem-r15 : StackInvariant s → readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
        derive-mem-r15 (r15-in-heap r15-heap) =
          -- r15 is in heap region, stack operations don't affect heap
          -- NOW PROVEN via WfR.mem-heap-region (D041 region-based proof)
          WfR.mem-heap-region (readReg (regs s) r15) r15-heap
        derive-mem-r15 (r15-in-code r15-code) =
          -- r15 is in code region, use WfR.mem-code-region
          WfR.mem-code-region (readReg (regs s) r15) r15-code
        derive-mem-r15 (r15-in-stack frame slot r15-eq frame-bound) =
          -- r15 is in stack region but above rsp, use WfR.mem-above
          -- Derive r15 ≥ rsp from frame-bound and slot-addr-≥-base:
          --   slot-addr frame slot ≥ sp-addr frame  (from slot-addr-≥-base)
          --   sp-addr frame ≥ s.rsp  (from frame-bound)
          --   s.r15 = slot-addr frame slot  (from r15-eq)
          let slot≥frame : slot-addr frame slot ≥ sp-addr frame
              slot≥frame = slot-addr-≥-base frame slot
              slot≥rsp : slot-addr frame slot ≥ readReg (regs s) rsp
              slot≥rsp = ≤-trans frame-bound slot≥frame
              r15≥rsp : readReg (regs s) r15 ≥ readReg (regs s) rsp
              r15≥rsp = subst (_≥ readReg (regs s) rsp) (sym r15-eq) slot≥rsp
          in WfR.mem-above (readReg (regs s) r15) r15≥rsp

------------------------------------------------------------------------
-- Validity-Based Apply Wrapper (Phase 5c)
--
-- Takes ValidAt input, uses bridging postulates to call encode-based
-- implementation, converts result back to IRStarResultV.
--
-- Input type: (A ⇒ B) * A
-- ValidAt ((closure, arg)) input-addr m is valid-pair v-cl v-arg pair-at
--   where v-cl : ValidAt closure closure-addr m
--         v-arg : ValidAt arg arg-addr m
--         pair-at : PairAtS closure-addr arg-addr input-addr m
-- And v-cl is valid-closure closure-at where:
--   closure-at : ClosureAtS env-addr code-ptr closure-addr m
------------------------------------------------------------------------

-- Takes StackCapacity s (apply-consumed-slots + wf.thunk-capacity) for capacity threading
run-apply-to-ir-result-v : ∀ {E A B} (prefix suffix : Program)
                           (code-ptr : ℕ) (env : ⟦ E ⟧)
                           (semantics : ⟦ A ⟧ → ⟦ B ⟧)
                           (closure-addr arg-addr : ℕ)
                           (arg : ⟦ A ⟧) (s : State) →
  let prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
      offset = length prefix
      cl = record { env-addr = encode env ; semantics = semantics }
      x = (cl , arg)
  in
  (wf : ClosureWellFormed {E} {A} {B} prog code-ptr env semantics) →
  halted s ≡ false →
  pc s ≡ offset →
  StackInvariant s →
  StackCapacity s (apply-consumed-slots +ℕ ClosureWellFormed.thunk-capacity wf) →
  RbpInvariant s →
  -- Validity-based memory layout:
  (v-cl : ValidAt {A ⇒ B} cl closure-addr (memory s)) →
  (v-arg : ValidAt arg arg-addr (memory s)) →
  (v-env : ValidAt env (encode env) (memory s)) →
  (pair-at : PairAtS closure-addr arg-addr (readReg (regs s) rdi) (memory s)) →
  (closure-at : ClosureAtS (encode env) code-ptr closure-addr (memory s)) →
  ∃[ s' ] IRStarResultV (apply {A} {B}) prog s s' x offset
run-apply-to-ir-result-v {E} {A} {B} prefix suffix code-ptr env semantics closure-addr arg-addr arg s
                         wf h-eq pc-eq stack-inv cap rbp-inv v-cl v-arg v-env pair-at closure-at =
  let
    prog = prefix ++ compile-x86 (apply {A} {B}) ++ suffix
    offset = length prefix
    env-addr = encode env
    cl = record { env-addr = env-addr ; semantics = semantics }
    x : ⟦ (A ⇒ B) * A ⟧
    x = (cl , arg)

    -- Construct input validity from component validities (no bridge!)
    input-valid : ValidAt {(A ⇒ B) * A} x (readReg (regs s) rdi) (memory s)
    input-valid = valid-pair v-cl v-arg pair-at

    -- Construct mem-layout from validity predicates (no bridge - uses arg-addr directly!)
    mem-cl : readMem (memory s) (readReg (regs s) rdi) ≡ just closure-addr
    mem-cl = fst-valid-s pair-at

    mem-arg : readMem (memory s) (readReg (regs s) rdi +ℕ' slot-size) ≡ just arg-addr
    mem-arg = snd-valid-s pair-at

    mem-env : readMem (memory s) closure-addr ≡ just (encode env)
    mem-env = env-valid-s closure-at

    mem-code-ptr : readMem (memory s) (closure-addr +ℕ' slot-size) ≡ just code-ptr
    mem-code-ptr = code-valid-s closure-at

    mem-layout : ∃[ cl-addr ] (
        readMem (memory s) (readReg (regs s) rdi) ≡ just cl-addr ×
        readMem (memory s) (readReg (regs s) rdi +ℕ' slot-size) ≡ just arg-addr ×
        readMem (memory s) cl-addr ≡ just (encode env) ×
        readMem (memory s) (cl-addr +ℕ' slot-size) ≡ just code-ptr)
    mem-layout = closure-addr , mem-cl , mem-arg , mem-env , mem-code-ptr

    -- Call existing implementation - returns IRStarResultV directly (no bridge!)
    result = run-apply-to-ir-result prefix suffix code-ptr env semantics arg arg-addr s
               wf h-eq pc-eq input-valid stack-inv cap rbp-inv mem-layout v-arg v-env

  in result  -- Direct passthrough (no conversion needed!)
