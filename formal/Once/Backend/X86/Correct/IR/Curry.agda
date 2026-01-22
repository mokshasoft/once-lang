------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Curry
--
-- Star-based curry proof.
-- Contains both non-recursive parts (run-curry-star) and the thunk
-- implementation (curry-thunk-correct-v) which takes RecDispatcher.
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
         ir-stack-requirement; ir-rsp-delta; ir-output-capacity;
         curry-rsp-delta≤curry-req;
         -- D041: Abstract helpers that encapsulate arithmetic
         curry-frame-disjoint-from-rbp; curry-rbp-inv-update; curry-stack-inv-frame-bound-update;
         curry-alloc-below-rbp; curry-alloc-nonzero;
         -- For thunk implementation
         thunk-setup-consumed-slots; capacity-from-larger; thunk-setup-capacity;
         thunk-setup-cap≤thunk-consumed+ir-req; capacity-after-delta;
         output-slots; stack-inv-preserved-unchanged)
open import Data.Nat.Properties using (≤-<-trans)
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; stack-code-addr-disjoint; stack-heap-addr-disjoint;
         stackAddr-write-preserves-heap; slot-addr; StackPointer;
         slot-addr-above-thunk-rbp; slot-addr-≥-base; in-stack; frameSlot)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)
-- Internal glue for abstraction boundary (implementation use only!)
open import Once.Backend.X86.Layout using (module FrameSlotInternal)
open FrameSlotInternal using (frameSlot-is-readMem)
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.FetchStep using (step-exec)
open import Once.Backend.X86.Correct.InstrExec using (execMov-reg-reg; execPop)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.ArithmeticLemmas using (word-fits-pair-strict)
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_; star-trans)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult; ClosureWFOutput; no-closure; has-closure;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-mem-rbp; ir-mem-rbp+8; ir-stack-inv; ir-rsp-bound; ir-rbp-inv; ir-mem-above; ir-mem-code; ir-mem-heap; ir-closure-wf;
         IRStarResultV; ir-result-valid; ir-capacity; ir-rsp-bound-v)
  renaming (ir-rsp-v to ir-rsp)

-- Import thunk execution proofs
open import Once.Backend.X86.Correct.IR.ThunkExec
  using (thunk-setup-star; thunk-ret-star; ThunkSetupResult; ThunkRetResult)
import Once.Backend.X86.Correct.IR.ThunkExec as TE
open ThunkRetResult

-- Import thunk structure lemmas
open import Once.Backend.X86.Correct.IR.ThunkStructure
  using (cleanup-i0; cleanup-i1; cleanup-i2;
         fetch-cleanup-i0; fetch-cleanup-i1; fetch-cleanup-i2)

-- Import closure well-formedness infrastructure
open import Once.Backend.X86.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult;
         thunk-star; thunk-halted; thunk-result-valid;
         thunk-r14; thunk-r15; thunk-rbp; thunk-stack-inv; thunk-capacity)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; valid-closure-env; ClosureAtS; closure-at-s; valid-at-preserved-under-write;
         valid-subst-addr-mem)

-- Import IRSize for RecDispatcher type
open import Once.Backend.X86.Correct.IRSize
  using (ir-size; curry-smaller)

open import Data.Nat using (_>_; _≥_; _<_; _≤_; s≤s; z≤n)
-- D041: Arithmetic moved to abstract helpers in StackInvariant.agda
-- m≤m+n kept for simple numeric constant facts
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; <-trans; ≤-<-trans; <-≤-trans;
                                        m<m+n; 0<1+n; m≤m+n; <⇒≤; m+[n∸m]≡n; ∸-+-assoc) renaming (<⇒≢ to Nat-<⇒≢)
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
    -- Env validity
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
    -- RSP delta: curry allocates slots, rsp decreases by ir-rsp-delta
    exec-rsp : readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta (curry f))
    exec-mem : readMem (memory s') (readReg (regs s) r15) ≡ readMem (memory s) (readReg (regs s) r15)
    exec-mem-rbp : readMem (memory s') (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    exec-mem-rbp+8 : readMem (memory s') (readReg (regs s) rbp +ℕ slot-size) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ slot-size)
    exec-stack-inv : StackInvariant s'
    exec-capacity : StackCapacity s' (ir-output-capacity (curry f))
    exec-rbp-inv : RbpInvariant s'
    exec-mem-above : ∀ addr → addr > readReg (regs s) rbp → readMem (memory s') addr ≡ readMem (memory s) addr
    exec-mem-code : ∀ addr → InCode addr → readMem (memory s') addr ≡ readMem (memory s) addr
    exec-mem-heap : ∀ addr → InHeap addr → readMem (memory s') addr ≡ readMem (memory s) addr

open CurryExecResult public

------------------------------------------------------------------------
-- Main curry proof (validity-based, no encode)
------------------------------------------------------------------------

-- | Main curry proof (takes StackCapacity s (ir-stack-requirement (curry f)) directly)
-- Uses dynamic capacity based on the actual IR's requirements
run-curry-star : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (curry f)) →
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
    ; exec-rsp = rsp-change
    ; exec-mem = mem-final
    ; exec-mem-rbp = mem-rbp-final
    ; exec-mem-rbp+8 = mem-rbp+8-final
    ; exec-stack-inv = stack-inv-final
    ; exec-capacity = output-capacity
    ; exec-rbp-inv = rbp-inv-final
    ; exec-mem-above = mem-above-final
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

    -- Derive rsp bound from StackCapacity using dynamic requirement
    -- ir-rsp-delta (curry f) ≤ ir-stack-requirement (curry f) via named lemma
    rsp-bound : readReg (regs s) rsp > slots (ir-rsp-delta (curry f))
    rsp-bound = ≤-<-trans (slots-mono-≤ (curry-rsp-delta≤curry-req f)) (StackCapacity.rsp-sufficient cap)

    rsp-region : InStack (readReg (regs s) rsp)
    rsp-region = StackCapacity.rsp-in-stack cap

    -- StackCapacity for output allocation (derived from ir-rsp-delta)
    cap-output-alloc : StackCapacity s (ir-rsp-delta (curry f))
    cap-output-alloc = rsp-bound-to-capacity (ir-rsp-delta (curry f)) s rsp-region rsp-bound

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

    -- new-rsp uses ir-rsp-delta to avoid hardcoding
    new-rsp : Word
    new-rsp = orig-rsp ∸ slots (ir-rsp-delta (curry f))

    -- The 7 instructions that actually execute
    i0 : Instr
    i0 = sub (reg rsp) (imm (pair-alloc))

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
      sub (reg rsp) (imm (pair-alloc)) ∷         -- allocate pair
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
              sub (reg rsp) (imm (pair-alloc)) ∷
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
                                 sub (reg rsp) (imm (pair-alloc)) ∷
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

    -- s2 writes to new-rsp (stack), validity preserved since ValidAt addresses are in heap
    -- Derive InStack proofs from capacity
    write-addrs-in-stack : InStack new-rsp × InStack (new-rsp +ℕ slot-size)
    write-addrs-in-stack = alloc-2-slots-addrs-in-stack s cap-output-alloc

    v-env-s2 : ValidAt x orig-rdi (memory s2)
    v-env-s2 = valid-at-preserved-under-write input-valid (proj₁ write-addrs-in-stack)

    -- s3 doesn't modify memory
    v-env-s3 : ValidAt x orig-rdi (memory s3)
    v-env-s3 = v-env-s2

    -- s4 writes to new-rsp+8 (stack), validity preserved
    v-env-s4 : ValidAt x orig-rdi (memory s4)
    v-env-s4 = valid-at-preserved-under-write v-env-s3 (proj₂ write-addrs-in-stack)

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
    stack-inv-helper (r15-in-heap r15-heap) =
      r15-in-heap (subst InHeap (sym r15-final) r15-heap)
    stack-inv-helper (r15-in-code r15-code) =
      r15-in-code (subst InCode (sym r15-final) r15-code)
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
    -- rsp decreases by ir-rsp-delta (curry f) = 2 slots
    rsp-change : readReg (regs s-final) rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta (curry f))
    rsp-change = rsp-s7

    -- Output capacity = input requirement - delta
    -- capacity-after-alloc-2-slots expects StackCapacity s (suc (suc n)) and produces StackCapacity s' n
    -- Since ir-stack-requirement (curry f) = 2 + (4 + req f) and ir-output-capacity (curry f) = 4 + req f,
    -- we have ir-stack-requirement = suc (suc ir-output-capacity) definitionally
    output-capacity : StackCapacity s-final (ir-output-capacity (curry f))
    output-capacity = capacity-after-alloc-2-slots s s-final (ir-output-capacity (curry f)) cap rsp-change

    rsp-sufficient-final : readReg (regs s-final) rsp > slots (ir-output-capacity (curry f))
    rsp-sufficient-final = StackCapacity.rsp-sufficient output-capacity

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

    -- D041: Memory at code-region addresses preserved (PURE REGION APPROACH)
    -- 1. Get region membership for both write addresses (encapsulates arithmetic)
    -- 2. Use stack-code-disjoint to prove write ≠ code address
    -- 3. Chain readMem-writeMem-diff
    -- NO ARITHMETIC COMPARISONS at this level
    mem-code-final : ∀ addr → InCode addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-code-final addr addr-in-code =
      let -- Step 1: Region membership (arithmetic encapsulated in infrastructure)
          writes-in-stack : InStack new-rsp × InStack (new-rsp +ℕ slot-size)
          writes-in-stack = alloc-2-slots-addrs-in-stack s cap-output-alloc

          new-rsp-in-stk : InStack new-rsp
          new-rsp-in-stk = proj₁ writes-in-stack

          new-rsp+8-in-stk : InStack (new-rsp +ℕ slot-size)
          new-rsp+8-in-stk = proj₂ writes-in-stack

          -- Step 2: Disjointness from region membership
          addr≢new-rsp : addr ≢ new-rsp
          addr≢new-rsp eq = stack-code-addr-disjoint new-rsp addr new-rsp-in-stk addr-in-code (sym eq)

          addr≢new-rsp+8 : addr ≢ (new-rsp +ℕ slot-size)
          addr≢new-rsp+8 eq = stack-code-addr-disjoint (new-rsp +ℕ slot-size) addr new-rsp+8-in-stk addr-in-code (sym eq)

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
    mem-heap-final : ∀ addr → InHeap addr → readMem (memory s-final) addr ≡ readMem (memory s) addr
    mem-heap-final addr addr-in-heap =
      let -- Step 1: Region membership (arithmetic encapsulated in infrastructure)
          writes-in-stack : InStack new-rsp × InStack (new-rsp +ℕ slot-size)
          writes-in-stack = alloc-2-slots-addrs-in-stack s cap-output-alloc

          new-rsp-in-stk : InStack new-rsp
          new-rsp-in-stk = proj₁ writes-in-stack

          new-rsp+8-in-stk : InStack (new-rsp +ℕ slot-size)
          new-rsp+8-in-stk = proj₂ writes-in-stack

          -- Step 2: Disjointness from region membership
          addr≢new-rsp : addr ≢ new-rsp
          addr≢new-rsp eq = stack-heap-addr-disjoint new-rsp addr new-rsp-in-stk addr-in-heap (sym eq)

          addr≢new-rsp+8 : addr ≢ (new-rsp +ℕ slot-size)
          addr≢new-rsp+8 eq = stack-heap-addr-disjoint (new-rsp +ℕ slot-size) addr new-rsp+8-in-stk addr-in-heap (sym eq)

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
-- Takes StackCapacity s (ir-stack-requirement (curry f)) directly
-- Curry allocates ir-rsp-delta slots, output capacity = ir-output-capacity
run-curry-star-v : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (curry f)) →
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
    ; ir-rsp = exec-rsp exec-result  -- curry: rsp s' = rsp s ∸ slots (ir-rsp-delta)
    ; ir-mem = exec-mem exec-result
    ; ir-mem-rbp = exec-mem-rbp exec-result
    ; ir-mem-rbp+8 = exec-mem-rbp+8 exec-result
    ; ir-stack-inv = exec-stack-inv exec-result
    ; ir-capacity = exec-capacity exec-result
    ; ir-rbp-inv = exec-rbp-inv exec-result
    ; ir-mem-above = exec-mem-above exec-result
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
    -- Closure.env-addr (eval (curry f) x) = encode x (by definition of eval for curry)
    -- So the first arg to valid-closure-env is refl
    closure-valid-at-addr : ValidAt {B ⇒ C} sem-closure curry-closure-addr (memory s-final)
    closure-valid-at-addr = valid-closure-env refl curry-v-env closure-at

    -- Transport to rax
    result-valid : ValidAt (eval (curry f) x) (readReg (regs s-final) rax) (memory s-final)
    result-valid = subst (λ addr → ValidAt {B ⇒ C} sem-closure addr (memory s-final))
                         (sym curry-rax-eq) closure-valid-at-addr

------------------------------------------------------------------------
-- RecDispatcher: Type for recursive dispatcher function
--
-- This type represents the recursive dispatcher that IR implementations
-- receive as a function parameter. It allows calling back into the
-- dispatcher for sub-IRs (e.g., f in curry f).
--
-- Previously this was passed via Acc in MutualIR.agda's curry-thunk-correct-impl.
-- Now it's passed as an explicit function parameter, eliminating the need
-- for Acc-based termination tracking in this module.
------------------------------------------------------------------------

RecDispatcher : ℕ → Set₁
RecDispatcher bound =
  ∀ {A B} (ir : IR A B) → ir-size ir < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement ir) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 ir ++ suffix
  in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix)

------------------------------------------------------------------------
-- Private helpers for curry-thunk-correct-v
-- (Moved from MutualIR.agda to avoid function definitions in where clauses)
------------------------------------------------------------------------
private
  -- Helper: m ∸ n < m when both m > 0 and n > 0
  m∸n<m-when-positive : ∀ m n → m > 0 → n > 0 → m ∸ n < m
  m∸n<m-when-positive (suc m') (suc n') _ _ = s≤s (Data.Nat.Properties.m∸n≤m m' n')
    where open import Data.Nat.Properties using (m∸n≤m)

------------------------------------------------------------------------
-- curry-thunk-correct-v: Thunk execution proof with RecDispatcher
--
-- This function was previously curry-thunk-correct-impl in MutualIR.agda.
-- Now it takes RecDispatcher instead of Acc for recursive dispatch.
--
-- The proof structure is unchanged:
--   Phase 1: Setup (8 thunk setup instructions)
--   Phase 2: Execute f (recursive call via rec)
--   Phase 3: Cleanup (3 instructions: mov rsp rbp, pop rbp, pop r15)
--   Phase 4: Return (ret instruction)
------------------------------------------------------------------------

-- | curry-thunk-correct-v: Implementation using RecDispatcher
-- This composes: setup tracing → rec on f → ret tracing
-- caller-sp: StackPointer from the caller (D041)
-- caller-sp-bound: addr caller-sp = s.rsp + 8 (call convention)
-- r15-in-code: r15 is in code region (from Apply, allows postulate-free ret)
-- bound: Size bound for recursive dispatcher
-- rec: Recursive dispatcher function
-- f<bound: Proof that ir-size f < bound
-- cap: StackCapacity threaded from caller (replaces postulate-based capacity)
--      Capacity needed: thunk-setup-consumed-slots + ir-stack-requirement f
--      This is 4 + f-req, where thunk setup consumes 4 and f needs f-req
curry-thunk-correct-v : ∀ {A B C} (f : IR (A * B) C)
                        (bound : ℕ)
                        (rec : RecDispatcher bound)
                        (f<bound : ir-size f < bound)
                        (prefix suffix : Program) (caller-sp : StackPointer) (env : ⟦ A ⟧)
                        (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
      thunk-cap = thunk-setup-consumed-slots +ℕ ir-stack-requirement f
  in
  halted s ≡ false →
  pc s ≡ thunk-offset →
  ValidAt arg (readReg (regs s) rdi) (memory s) →  -- validity for arg!
  ValidAt env (readReg (regs s) r12) (memory s) →  -- validity for env!
  readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
  StackInvariant s →
  StackCapacity s thunk-cap →  -- Threaded capacity: 4 + ir-stack-requirement f
  sp-addr caller-sp ≡ readReg (regs s) rsp +ℕ slot-size →  -- D041: caller-sp bound
  InCode (readReg (regs s) r15) →  -- r15 in code region (from Apply)
  ∃[ s' ] (ThunkResult prog s s' caller-sp (λ b → eval f (env , b)) arg
          × pc s' ≡ ret-addr)
curry-thunk-correct-v {A} {B} {C} f bound rec f<bound prefix suffix caller-sp env arg s ret-addr
                      h-eq pc-eq v-arg v-env mem-ret stack-inv cap-thunk caller-sp-bound r15-in-code-entry =
    s-final , thunk-result , pc-final
    where
      -- Local imports (some may duplicate module-level imports)
      open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
      open import Data.Nat.Properties using (≤-trans; m≤m+n; ∸-monoˡ-≤; ∸-monoʳ-<) renaming (+-comm to Data-Nat-+-comm)

      -- Derive 8 ≤ rsp from capacity (for m+[n∸m]≡n)
      -- thunk-setup-consumed-slots = 4, so 4 + ir-req f ≥ 4 ≥ 1, meaning rsp > slots 1 ≥ 8
      8≤rsp : 8 ≤ readReg (regs s) rsp
      8≤rsp = ≤-trans (m≤m+n slot-size 0) (<⇒≤ (≤-<-trans (slots-mono-≤ 1≤thunk-cap) (StackCapacity.rsp-sufficient cap-thunk)))
        where
          -- 1 ≤ 4 + ir-req f (thunk-setup-consumed-slots = 4 ≥ 1)
          1≤thunk-cap : 1 ≤ thunk-setup-consumed-slots +ℕ ir-stack-requirement f
          1≤thunk-cap = ≤-trans (s≤s z≤n) (m≤m+n thunk-setup-consumed-slots (ir-stack-requirement f))

      prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
      f-offset = length prefix +ℕ 14      -- 6 closure + 8 thunk setup
      ret-offset = length prefix +ℕ 17 +ℕ compile-length f  -- f-offset + len-f + 3 cleanup

      -- Derive StackCapacity for thunk-setup-star from threaded capacity
      cap-thunk-setup : StackCapacity s thunk-setup-capacity
      cap-thunk-setup = capacity-from-larger s thunk-setup-capacity
                          (thunk-setup-consumed-slots +ℕ ir-stack-requirement f)
                          cap-thunk (thunk-setup-cap≤thunk-consumed+ir-req f)

      -- Step 1: Trace 8 setup instructions
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq v-arg v-env stack-inv cap-thunk-setup
      s-after-setup = proj₁ setup-result
      setup-rec = proj₂ setup-result
      open TE.ThunkSetupResult setup-rec

      -- Step 2: Call rec on f
      len-f = compile-length f
      end-label = 18 +ℕ len-f
      end-offset-curry = 12 +ℕ len-f

      curry-closure-setup : Program
      curry-closure-setup =
        sub (reg rsp) (imm (pair-alloc)) ∷
        mov (mem (base rsp)) (reg rdi) ∷
        lea r9 (rip+disp 4) ∷
        mov (mem (base+disp rsp slot-size)) (reg r9) ∷
        mov (reg rax) (reg rsp) ∷
        jmp end-offset-curry ∷ []

      curry-thunk-setup-prog : Program
      curry-thunk-setup-prog =
        label 6 ∷
        push (reg r15) ∷
        push (reg rbp) ∷
        mov (reg rbp) (reg rsp) ∷
        sub (reg rsp) (imm (pair-alloc)) ∷
        mov (mem (base rsp)) (reg r12) ∷
        mov (mem (base+disp rsp slot-size)) (reg rdi) ∷
        mov (reg rdi) (reg rsp) ∷ []

      prefix-f : Program
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup-prog

      curry-tail : Program
      curry-tail = mov (reg rsp) (reg rbp) ∷
                   pop rbp ∷
                   pop r15 ∷
                   ret ∷ label end-label ∷ []

      suffix-f : Program
      suffix-f = curry-tail ++ suffix

      len-prefix-f : length prefix-f ≡ length prefix +ℕ 14
      len-prefix-f = trans (List-length-++ prefix {curry-closure-setup ++ curry-thunk-setup-prog})
                           (cong (length prefix +ℕ_) (List-length-++ curry-closure-setup {curry-thunk-setup-prog}))

      curry-structure : compile-x86 (curry f) ≡
                        curry-closure-setup ++ curry-thunk-setup-prog ++ compile-x86 f ++ curry-tail
      curry-structure = refl

      prog-eq-f : prog ≡ prefix-f ++ compile-x86 f ++ suffix-f
      prog-eq-f = trans (cong (λ x → prefix ++ x ++ suffix) curry-structure) prog-reassoc
        where
          ccs = curry-closure-setup
          cts = curry-thunk-setup-prog
          code-f = compile-x86 f
          cta = curry-tail
          prog-reassoc : prefix ++ (ccs ++ cts ++ code-f ++ cta) ++ suffix ≡ prefix-f ++ code-f ++ suffix-f
          prog-reassoc =
            let inner-assoc1 : ccs ++ (cts ++ (code-f ++ cta)) ≡ (ccs ++ cts) ++ (code-f ++ cta)
                inner-assoc1 = sym (++-assoc ccs cts (code-f ++ cta))
                inner-assoc2 : ((ccs ++ cts) ++ (code-f ++ cta)) ++ suffix ≡ (ccs ++ cts) ++ ((code-f ++ cta) ++ suffix)
                inner-assoc2 = ++-assoc (ccs ++ cts) (code-f ++ cta) suffix
                inner-assoc3 : (code-f ++ cta) ++ suffix ≡ code-f ++ (cta ++ suffix)
                inner-assoc3 = ++-assoc code-f cta suffix
                inner-combined : (ccs ++ (cts ++ (code-f ++ cta))) ++ suffix ≡ (ccs ++ cts) ++ (code-f ++ (cta ++ suffix))
                inner-combined = trans (cong (_++ suffix) inner-assoc1)
                                 (trans inner-assoc2 (cong ((ccs ++ cts) ++_) inner-assoc3))
                outer-step : prefix ++ ((ccs ++ (cts ++ (code-f ++ cta))) ++ suffix) ≡ prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix)))
                outer-step = cong (prefix ++_) inner-combined
                final-assoc : prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix))) ≡ (prefix ++ (ccs ++ cts)) ++ (code-f ++ (cta ++ suffix))
                final-assoc = sym (++-assoc prefix (ccs ++ cts) (code-f ++ (cta ++ suffix)))
            in trans outer-step final-assoc

      pc-setup-f : pc s-after-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      input-valid-f : ValidAt (env , arg) (readReg (regs s-after-setup) rdi) (memory s-after-setup)
      input-valid-f = v-pair-setup

      cap-setup : StackCapacity s-after-setup (ir-stack-requirement f)
      cap-setup = capacity-after-delta s s-after-setup thunk-setup-consumed-slots (ir-stack-requirement f)
                    cap-thunk rsp-setup

      -- Recursive call via rec (replaces run-ir-star-at-offset-v ... (smaller-acc ...))
      step-f-v : ∃[ s-f ] IRStarResultV f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-f (env , arg) (length prefix-f)
      step-f-v = rec f f<bound prefix-f suffix-f caller-sp (env , arg) s-after-setup
                   h-setup pc-setup-f input-valid-f stack-inv-setup cap-setup rbp-inv-setup

      s-after-f-raw : State
      s-after-f-raw = proj₁ step-f-v

      r-f-v : IRStarResultV f (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw (env , arg) (length prefix-f)
      r-f-v = proj₂ step-f-v

      star-f-raw : Star (prefix-f ++ compile-x86 f ++ suffix-f) s-after-setup s-after-f-raw
      star-f-raw = IRStarResultV.ir-star r-f-v

      result-valid-f : ValidAt (eval f (env , arg)) (readReg (regs s-after-f-raw) rax) (memory s-after-f-raw)
      result-valid-f = IRStarResultV.ir-result-valid r-f-v

      star-f-converted : Star prog s-after-setup s-after-f-raw
      star-f-converted = subst (λ p → Star p s-after-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ compile-length f
      pc-f-raw = IRStarResultV.ir-pc r-f-v

      cleanup-offset = length prefix +ℕ 14 +ℕ compile-length f

      pc-f-at-cleanup : pc s-after-f-raw ≡ cleanup-offset
      pc-f-at-cleanup = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- Cleanup phase: mov rsp rbp, pop rbp, pop r15
      old-rsp-s = readReg (regs s) rsp
      rbp-val = readReg (regs s-after-f-raw) rbp

      rbp-after-f : readReg (regs s-after-f-raw) rbp ≡ readReg (regs s) rsp ∸ pair-alloc
      rbp-after-f = trans (IRStarResultV.ir-rbp r-f-v) rbp-setup

      -- State after mov rsp, rbp
      s-c1 : State
      s-c1 = record s-after-f-raw { regs = writeReg (regs s-after-f-raw) rsp rbp-val
                                  ; pc = pc s-after-f-raw +ℕ 1 }

      fetch-c0 : fetch prog cleanup-offset ≡ just cleanup-i0
      fetch-c0 = fetch-cleanup-i0 f prefix suffix

      step-c0 : step prog s-after-f-raw ≡ just s-c1
      step-c0 = trans (step-exec prog s-after-f-raw cleanup-i0 (IRStarResultV.ir-halted r-f-v)
                        (subst (λ n → fetch prog n ≡ just cleanup-i0) (sym pc-f-at-cleanup) fetch-c0))
                      (execMov-reg-reg s-after-f-raw rsp rbp)

      h-c1 : halted s-c1 ≡ false
      h-c1 = IRStarResultV.ir-halted r-f-v

      pc-c1 : pc s-c1 ≡ cleanup-offset +ℕ 1
      pc-c1 = cong (_+ℕ 1) pc-f-at-cleanup

      mem-c1-eq-f : ∀ addr → readMem (memory s-c1) addr ≡ readMem (memory s-after-f-raw) addr
      mem-c1-eq-f addr = refl

      rsp-c1-inline : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ pair-alloc
      rsp-c1-inline = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      -- Derive rsp > pair-alloc from cap-thunk
      rsp>slots2 : readReg (regs s) rsp > pair-alloc
      rsp>slots2 = ≤-<-trans (slots-mono-≤ (m≤m+n 2 (output-slots +ℕ ir-stack-requirement f))) (StackCapacity.rsp-sufficient cap-thunk)

      16≤rsp : pair-alloc ≤ readReg (regs s) rsp
      16≤rsp = <⇒≤ rsp>slots2

      -- Memory at rbp preserved through f
      mem-rbp-preserved-f : readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp) ≡
                            readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
      mem-rbp-preserved-f = IRStarResultV.ir-mem-rbp r-f-v

      rbp-setup-addr : readReg (regs s-after-setup) rbp ≡ old-rsp-s ∸ pair-alloc
      rbp-setup-addr = rbp-setup

      pop-rbp-mem : readMem (memory s-c1) (readReg (regs s-c1) rsp) ≡ just (readReg (regs s) rbp)
      pop-rbp-mem = begin
        readMem (memory s-c1) (readReg (regs s-c1) rsp)
          ≡⟨ cong (readMem (memory s-c1)) rsp-c1-inline ⟩
        readMem (memory s-c1) (old-rsp-s ∸ pair-alloc)
          ≡⟨ mem-c1-eq-f (old-rsp-s ∸ pair-alloc) ⟩
        readMem (memory s-after-f-raw) (old-rsp-s ∸ pair-alloc)
          ≡⟨ cong (readMem (memory s-after-f-raw)) (sym rbp-setup-addr) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-after-setup) rbp)
          ≡⟨ mem-rbp-preserved-f ⟩
        readMem (memory s-after-setup) (readReg (regs s-after-setup) rbp)
          ≡⟨ mem-at-rbp-setup ⟩
        just (readReg (regs s) rbp) ∎

      -- State after pop rbp
      s-c2 : State
      s-c2 = record s-c1 { regs = writeReg (writeReg (regs s-c1) rbp (readReg (regs s) rbp))
                                          rsp (readReg (regs s-c1) rsp +ℕ slot-size)
                         ; pc = pc s-c1 +ℕ 1 }

      cleanup-offset-plus-1 : cleanup-offset +ℕ 1 ≡ (length prefix +ℕ 15) +ℕ len-f
      cleanup-offset-plus-1 = trans (+-assoc (length prefix +ℕ 14) len-f 1)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (Data-Nat-+-comm len-f 1))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 1 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 1))))

      fetch-c1 : fetch prog (cleanup-offset +ℕ 1) ≡ just cleanup-i1
      fetch-c1 = subst (λ n → fetch prog n ≡ just cleanup-i1)
                       (sym cleanup-offset-plus-1)
                       (fetch-cleanup-i1 f prefix suffix)

      step-c1 : step prog s-c1 ≡ just s-c2
      step-c1 = trans (step-exec prog s-c1 cleanup-i1 h-c1
                        (subst (λ n → fetch prog n ≡ just cleanup-i1) (sym pc-c1) fetch-c1))
                      (execPop prog s-c1 rbp (readReg (regs s) rbp) pop-rbp-mem)

      h-c2 : halted s-c2 ≡ false
      h-c2 = h-c1

      pc-c2 : pc s-c2 ≡ cleanup-offset +ℕ 2
      pc-c2 = trans (cong (_+ℕ 1) pc-c1) (+-assoc cleanup-offset 1 1)

      rsp-c1 : readReg (regs s-c1) rsp ≡ old-rsp-s ∸ pair-alloc
      rsp-c1 = trans (readReg-writeReg-same (regs s-after-f-raw) rsp rbp-val) rbp-after-f

      8≤old-rsp-8 : slot-size ≤ old-rsp-s ∸ slot-size
      8≤old-rsp-8 = ∸-monoˡ-≤ slot-size 16≤rsp

      rsp-c2 : readReg (regs s-c2) rsp ≡ old-rsp-s ∸ slot-size
      rsp-c2 = begin
        readReg (regs s-c2) rsp
          ≡⟨ readReg-writeReg-same (writeReg (regs s-c1) rbp (readReg (regs s) rbp)) rsp
                                   (readReg (regs s-c1) rsp +ℕ slot-size) ⟩
        readReg (regs s-c1) rsp +ℕ slot-size
          ≡⟨ cong (_+ℕ slot-size) rsp-c1 ⟩
        (old-rsp-s ∸ pair-alloc) +ℕ slot-size
          ≡⟨ cong (_+ℕ slot-size) (sym (∸-+-assoc old-rsp-s slot-size slot-size)) ⟩
        ((old-rsp-s ∸ slot-size) ∸ slot-size) +ℕ slot-size
          ≡⟨ trans (Data-Nat-+-comm ((old-rsp-s ∸ slot-size) ∸ slot-size) slot-size) (m+[n∸m]≡n 8≤old-rsp-8) ⟩
        old-rsp-s ∸ slot-size
        ∎

      -- Register preservation through cleanup
      rsp-val-c2 = readReg (regs s-c1) rsp +ℕ slot-size
      orig-rbp = readReg (regs s) rbp

      rax-c2 : readReg (regs s-c2) rax ≡ readReg (regs s-after-f-raw) rax
      rax-c2 = trans (readReg-writeReg-rsp-rax (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-rax (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-rax (regs s-after-f-raw) rbp-val))

      r14-c2 : readReg (regs s-c2) r14 ≡ readReg (regs s-after-f-raw) r14
      r14-c2 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-r14 (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-r14 (regs s-after-f-raw) rbp-val))

      r15-c2 : readReg (regs s-c2) r15 ≡ readReg (regs s-after-f-raw) r15
      r15-c2 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (trans (readReg-writeReg-rbp-r15 (regs s-c1) orig-rbp)
                            (readReg-writeReg-rsp-r15 (regs s-after-f-raw) rbp-val))

      rbp-c2 : readReg (regs s-c2) rbp ≡ readReg (regs s) rbp
      rbp-c2 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s-c1) rbp orig-rbp) rsp-val-c2)
                     (readReg-writeReg-same (regs s-c1) rbp orig-rbp)

      -- Third cleanup step: pop r15
      cleanup-offset-plus-2 : cleanup-offset +ℕ 2 ≡ (length prefix +ℕ 16) +ℕ len-f
      cleanup-offset-plus-2 = trans (+-assoc (length prefix +ℕ 14) len-f 2)
                                    (trans (cong ((length prefix +ℕ 14) +ℕ_) (Data-Nat-+-comm len-f 2))
                                           (trans (sym (+-assoc (length prefix +ℕ 14) 2 len-f))
                                                  (cong (_+ℕ len-f) (+-assoc (length prefix) 14 2))))

      fetch-c2 : fetch prog (cleanup-offset +ℕ 2) ≡ just cleanup-i2
      fetch-c2 = subst (λ n → fetch prog n ≡ just cleanup-i2)
                       (sym cleanup-offset-plus-2)
                       (fetch-cleanup-i2 f prefix suffix)

      orig-r15 = readReg (regs s) r15
      rsp-val-c3 = readReg (regs s-c2) rsp +ℕ slot-size

      s-c3 : State
      s-c3 = record s-c2 { regs = writeReg (writeReg (regs s-c2) r15 orig-r15)
                                          rsp rsp-val-c3
                         ; pc = pc s-c2 +ℕ 1 }

      rsp-16<rsp-8 : readReg (regs s) rsp ∸ pair-alloc < readReg (regs s) rsp ∸ slot-size
      rsp-16<rsp-8 = ∸-monoʳ-< word-fits-pair-strict 16≤rsp

      old-rsp-8>rbp : old-rsp-s ∸ slot-size > readReg (regs s-after-setup) rbp
      old-rsp-8>rbp = subst (λ x → old-rsp-s ∸ slot-size > x) (sym rbp-setup-addr) rsp-16<rsp-8

      pop-r15-mem : readMem (memory s-c2) (readReg (regs s-c2) rsp) ≡ just orig-r15
      pop-r15-mem = begin
        readMem (memory s-c2) (readReg (regs s-c2) rsp)
          ≡⟨ cong (readMem (memory s-c2)) rsp-c2 ⟩
        readMem (memory s-c2) (old-rsp-s ∸ slot-size)
          ≡⟨⟩
        readMem (memory s-c1) (old-rsp-s ∸ slot-size)
          ≡⟨ mem-c1-eq-f (old-rsp-s ∸ slot-size) ⟩
        readMem (memory s-after-f-raw) (old-rsp-s ∸ slot-size)
          ≡⟨ IRStarResultV.ir-mem-above r-f-v (old-rsp-s ∸ slot-size) old-rsp-8>rbp ⟩
        readMem (memory s-after-setup) (old-rsp-s ∸ slot-size)
          ≡⟨ mem-r15-setup ⟩
        just orig-r15 ∎

      step-c2 : step prog s-c2 ≡ just s-c3
      step-c2 = trans (step-exec prog s-c2 cleanup-i2 h-c2
                        (subst (λ n → fetch prog n ≡ just cleanup-i2) (sym pc-c2) fetch-c2))
                      (execPop prog s-c2 r15 orig-r15 pop-r15-mem)

      h-c3 : halted s-c3 ≡ false
      h-c3 = h-c2

      prefix-14+3 : (length prefix +ℕ 14) +ℕ 3 ≡ length prefix +ℕ 17
      prefix-14+3 = +-assoc (length prefix) 14 3

      cleanup-plus-3≡ret : cleanup-offset +ℕ 3 ≡ ret-offset
      cleanup-plus-3≡ret = trans (+-assoc (length prefix +ℕ 14) len-f 3)
                                 (trans (cong ((length prefix +ℕ 14) +ℕ_) (Data-Nat-+-comm len-f 3))
                                        (trans (sym (+-assoc (length prefix +ℕ 14) 3 len-f))
                                               (cong (_+ℕ len-f) prefix-14+3)))

      pc-c3 : pc s-c3 ≡ ret-offset
      pc-c3 = begin
        pc s-c3
          ≡⟨⟩
        pc s-c2 +ℕ 1
          ≡⟨ cong (_+ℕ 1) pc-c2 ⟩
        (cleanup-offset +ℕ 2) +ℕ 1
          ≡⟨ +-assoc cleanup-offset 2 1 ⟩
        cleanup-offset +ℕ 3
          ≡⟨ cleanup-plus-3≡ret ⟩
        ret-offset
        ∎

      rsp-c3 : readReg (regs s-c3) rsp ≡ old-rsp-s
      rsp-c3 = begin
        readReg (regs s-c3) rsp
          ≡⟨ readReg-writeReg-same (writeReg (regs s-c2) r15 orig-r15) rsp rsp-val-c3 ⟩
        rsp-val-c3
          ≡⟨⟩
        readReg (regs s-c2) rsp +ℕ slot-size
          ≡⟨ cong (_+ℕ slot-size) rsp-c2 ⟩
        (old-rsp-s ∸ slot-size) +ℕ slot-size
          ≡⟨ trans (Data-Nat-+-comm (old-rsp-s ∸ slot-size) slot-size) (m+[n∸m]≡n 8≤rsp) ⟩
        old-rsp-s
        ∎

      rax-c3 : readReg (regs s-c3) rax ≡ readReg (regs s-after-f-raw) rax
      rax-c3 = trans (readReg-writeReg-rsp-rax (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rax (regs s-c2) orig-r15) rax-c2)

      r14-c3 : readReg (regs s-c3) r14 ≡ readReg (regs s-after-f-raw) r14
      r14-c3 = trans (readReg-writeReg-rsp-r14 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-r14 (regs s-c2) orig-r15) r14-c2)

      r15-c3 : readReg (regs s-c3) r15 ≡ orig-r15
      r15-c3 = trans (readReg-writeReg-rsp-r15 (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (readReg-writeReg-same (regs s-c2) r15 orig-r15)

      rbp-c3 : readReg (regs s-c3) rbp ≡ readReg (regs s) rbp
      rbp-c3 = trans (readReg-writeReg-rsp-rbp (writeReg (regs s-c2) r15 orig-r15) rsp-val-c3)
                     (trans (readReg-writeReg-r15-rbp (regs s-c2) orig-r15) rbp-c2)

      star-c : Star prog s-after-f-raw s-c3
      star-c = ⟨ IRStarResultV.ir-halted r-f-v , step-c0 ⟩◅ ⟨ h-c1 , step-c1 ⟩◅ ⟨ h-c2 , step-c2 ⟩◅ refl*

      rsp-sufficient-c3 : readReg (regs s-c3) rsp > pair-alloc
      rsp-sufficient-c3 = subst (_> pair-alloc) (sym rsp-c3) rsp>slots2

      r15-s-to-c3 : readReg (regs s-c3) r15 ≡ readReg (regs s) r15
      r15-s-to-c3 = r15-c3

      stack-inv-c3 : StackInvariant s-c3
      stack-inv-c3 = stack-inv-preserved-unchanged s s-c3 stack-inv r15-s-to-c3 rsp-c3

      mem-cleanup-preserves : ∀ addr → readMem (memory s-c3) addr ≡ readMem (memory s-after-f-raw) addr
      mem-cleanup-preserves addr = mem-c1-eq-f addr

      rax-cleanup : readReg (regs s-c3) rax ≡ readReg (regs s-after-f-raw) rax
      rax-cleanup = rax-c3

      mem-cleanup-preserved : ∀ addr → readMem (memory s-c3) addr ≡ readMem (memory s-after-f-raw) addr
      mem-cleanup-preserved = mem-cleanup-preserves

      -- Return address preserved
      mem-ret-through-setup : readMem (memory s-after-setup) old-rsp-s ≡ just ret-addr
      mem-ret-through-setup = trans mem-old-rsp-setup mem-ret

      rbp+16≡old-rsp : readReg (regs s-after-setup) rbp +ℕ pair-alloc ≡ old-rsp-s
      rbp+16≡old-rsp = trans (cong (_+ℕ pair-alloc) rbp-setup-addr)
                             (trans (Data-Nat-+-comm (old-rsp-s ∸ pair-alloc) (pair-alloc)) (m+[n∸m]≡n 16≤rsp))

      old-rsp>rbp : old-rsp-s > readReg (regs s-after-setup) rbp
      old-rsp>rbp = subst (_> readReg (regs s-after-setup) rbp)
                         rbp+16≡old-rsp
                         (m<m+n (readReg (regs s-after-setup) rbp) {pair-alloc} (s≤s z≤n))

      mem-ret-through-f : readMem (memory s-after-f-raw) old-rsp-s ≡ just ret-addr
      mem-ret-through-f = begin
        readMem (memory s-after-f-raw) old-rsp-s
          ≡⟨ IRStarResultV.ir-mem-above r-f-v old-rsp-s old-rsp>rbp ⟩
        readMem (memory s-after-setup) old-rsp-s
          ≡⟨ mem-ret-through-setup ⟩
        just ret-addr ∎

      mem-ret-preserved : readMem (memory s-c3) (readReg (regs s-c3) rsp) ≡ just ret-addr
      mem-ret-preserved = subst (λ addr → readMem (memory s-c3) addr ≡ just ret-addr)
                                (sym rsp-c3)
                                (trans (mem-c1-eq-f old-rsp-s) mem-ret-through-f)

      s-after-f : State
      s-after-f = s-c3

      star-f-to-cleanup : Star prog s-after-setup s-c3
      star-f-to-cleanup = star-trans star-f-converted star-c

      star-f : Star prog s-after-setup s-after-f
      star-f = star-f-to-cleanup

      h-f : halted s-after-f ≡ false
      h-f = h-c3

      pc-f : pc s-after-f ≡ ret-offset
      pc-f = pc-c3

      r14-f : readReg (regs s-after-f) r14 ≡ readReg (regs s-after-setup) r14
      r14-f = trans r14-c3 (IRStarResultV.ir-r14 r-f-v)

      r15-f : readReg (regs s-after-f) r15 ≡ readReg (regs s-after-setup) r15
      r15-f = trans r15-c3 (sym r15-setup)

      rbp-f : readReg (regs s-after-f) rbp ≡ readReg (regs s) rbp
      rbp-f = rbp-c3

      stack-inv-f : StackInvariant s-after-f
      stack-inv-f = stack-inv-c3

      rsp-sufficient-f : readReg (regs s-after-f) rsp > pair-alloc
      rsp-sufficient-f = rsp-sufficient-c3

      mem-ret-f : readMem (memory s-after-f) (readReg (regs s-after-f) rsp) ≡ just ret-addr
      mem-ret-f = mem-ret-preserved

      rsp-f-restored : readReg (regs s-after-f) rsp ≡ readReg (regs s) rsp
      rsp-f-restored = rsp-c3

      mem-f-preserved : ∀ addr → readMem (memory s-after-f) addr ≡ readMem (memory s-after-f-raw) addr
      mem-f-preserved = mem-cleanup-preserves

      -- Step 3: Trace ret instruction
      r15-in-code-f : InCode (readReg (regs s-after-f) r15)
      r15-in-code-f = subst InCode (sym r15-f-eq-s) r15-in-code-entry
        where
          r15-f-eq-setup : readReg (regs s-after-f) r15 ≡ readReg (regs s-after-setup) r15
          r15-f-eq-setup = r15-f
          r15-f-eq-s : readReg (regs s-after-f) r15 ≡ readReg (regs s) r15
          r15-f-eq-s = trans r15-f-eq-setup r15-setup

      ret-result-pair : ∃[ s-fin ] ThunkRetResult prog s-after-f s-fin ret-addr
      ret-result-pair = thunk-ret-star f prefix suffix ret-addr s-after-f
                          h-f pc-f mem-ret-f r15-in-code-f rsp-sufficient-f

      s-final : State
      s-final = proj₁ ret-result-pair

      ret-rec : ThunkRetResult prog s-after-f s-final ret-addr
      ret-rec = proj₂ ret-result-pair

      star-ret : Star prog s-after-f s-final
      star-ret = ret-star ret-rec

      h-final : halted s-final ≡ false
      h-final = ret-halted ret-rec

      pc-final : pc s-final ≡ ret-addr
      pc-final = ret-pc ret-rec

      rax-final : readReg (regs s-final) rax ≡ readReg (regs s-after-f) rax
      rax-final = ret-rax ret-rec

      r14-final : readReg (regs s-final) r14 ≡ readReg (regs s-after-f) r14
      r14-final = ret-r14 ret-rec

      r15-final : readReg (regs s-final) r15 ≡ readReg (regs s-after-f) r15
      r15-final = ret-r15 ret-rec

      rbp-final : readReg (regs s-final) rbp ≡ readReg (regs s-after-f) rbp
      rbp-final = ret-rbp ret-rec

      stack-inv-final : StackInvariant s-final
      stack-inv-final = ret-stack-inv ret-rec

      rsp-sufficient-final : readReg (regs s-final) rsp > pair-alloc
      rsp-sufficient-final = ret-rsp-bound ret-rec

      rsp-ret-plus-8 : readReg (regs s-final) rsp ≡ readReg (regs s-after-f) rsp +ℕ slot-size
      rsp-ret-plus-8 = ret-rsp-plus-8 ret-rec

      mem-ret-preserves : ∀ addr → readMem (memory s-final) addr ≡ readMem (memory s-after-f) addr
      mem-ret-preserves = ret-mem-preserved ret-rec

      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      thunk-rsp-plus-8-proof : readReg (regs s-final) rsp ≡ readReg (regs s) rsp +ℕ slot-size
      thunk-rsp-plus-8-proof = trans rsp-ret-plus-8 (cong (_+ℕ slot-size) rsp-f-restored)

      rsp-final-is-caller : readReg (regs s-final) rsp ≡ sp-addr caller-sp
      rsp-final-is-caller = trans thunk-rsp-plus-8-proof (sym caller-sp-bound)

      rsp-final-in-stack : InStack (readReg (regs s-final) rsp)
      rsp-final-in-stack = subst InStack (sym rsp-final-is-caller) (in-stack caller-sp)

      result-valid-after-cleanup : ValidAt (eval f (env , arg)) (readReg (regs s-after-f) rax) (memory s-after-f)
      result-valid-after-cleanup = valid-subst-addr-mem result-valid-f rax-cleanup mem-cleanup-preserved

      thunk-result-valid-proof : ValidAt (eval f (env , arg)) (readReg (regs s-final) rax) (memory s-final)
      thunk-result-valid-proof = valid-subst-addr-mem result-valid-after-cleanup rax-final mem-ret-preserves

      thunk-preserves-frame-proof : ∀ k → frameSlot (memory s-final) caller-sp k ≡
                                          frameSlot (memory s) caller-sp k
      thunk-preserves-frame-proof k = begin
        frameSlot (memory s-final) caller-sp k
          ≡⟨ frameSlot-is-readMem (memory s-final) caller-sp k ⟩
        readMem (memory s-final) the-slot-addr
          ≡⟨ mem-ret-preserves the-slot-addr ⟩
        readMem (memory s-after-f) the-slot-addr
          ≡⟨ mem-f-preserved the-slot-addr ⟩
        readMem (memory s-after-f-raw) the-slot-addr
          ≡⟨ IRStarResultV.ir-mem-above r-f-v the-slot-addr slot-addr>rbp ⟩
        readMem (memory s-after-setup) the-slot-addr
          ≡⟨ setup-preserves-caller-slot ⟩
        readMem (memory s) the-slot-addr
          ≡⟨ sym (frameSlot-is-readMem (memory s) caller-sp k) ⟩
        frameSlot (memory s) caller-sp k ∎
        where
          the-slot-addr = slot-addr caller-sp k
          slot-addr>rbp : the-slot-addr > readReg (regs s-after-setup) rbp
          slot-addr>rbp = slot-addr-above-thunk-rbp caller-sp k
                           (readReg (regs s) rsp) (readReg (regs s-after-setup) rbp)
                           caller-sp-bound rbp-setup rsp>slots2
          rsp+8≤slot : readReg (regs s) rsp +ℕ slot-size ≤ the-slot-addr
          rsp+8≤slot = subst (_≤ the-slot-addr) caller-sp-bound (slot-addr-≥-base caller-sp k)
          rsp<rsp+slot : readReg (regs s) rsp < readReg (regs s) rsp +ℕ slot-size
          rsp<rsp+slot = m<m+n (readReg (regs s) rsp) (s≤s z≤n)
          slot-addr>rsp : the-slot-addr > readReg (regs s) rsp
          slot-addr>rsp = <-≤-trans rsp<rsp+slot rsp+8≤slot
          setup-preserves-caller-slot : readMem (memory s-after-setup) the-slot-addr ≡
                                        readMem (memory s) the-slot-addr
          setup-preserves-caller-slot = mem-above-setup the-slot-addr slot-addr>rsp

      thunk-preserves-code-proof : ∀ addr → InCode addr →
                                   readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-preserves-code-proof addr addr-in-code = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ IRStarResultV.ir-mem-code r-f-v addr addr-in-code ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ mem-code-setup addr addr-in-code ⟩
        readMem (memory s) addr ∎

      thunk-preserves-heap-proof : ∀ addr → InHeap addr →
                                   readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-preserves-heap-proof addr addr-in-heap = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ IRStarResultV.ir-mem-heap r-f-v addr addr-in-heap ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ mem-heap-setup addr addr-in-heap ⟩
        readMem (memory s) addr ∎

      thunk-preserves-above-entry-rsp-proof : ∀ addr → addr > readReg (regs s) rsp →
                                               readMem (memory s-final) addr ≡ readMem (memory s) addr
      thunk-preserves-above-entry-rsp-proof addr addr>rsp = begin
        readMem (memory s-final) addr
          ≡⟨ mem-ret-preserves addr ⟩
        readMem (memory s-after-f) addr
          ≡⟨ mem-f-preserved addr ⟩
        readMem (memory s-after-f-raw) addr
          ≡⟨ IRStarResultV.ir-mem-above r-f-v addr addr>rbp ⟩
        readMem (memory s-after-setup) addr
          ≡⟨ mem-above-setup addr addr>rsp ⟩
        readMem (memory s) addr ∎
        where
          rsp>rsp-16 : readReg (regs s) rsp > readReg (regs s) rsp ∸ pair-alloc
          rsp>rsp-16 = m∸n<m-when-positive (readReg (regs s) rsp) (pair-alloc) (≤-trans (s≤s z≤n) rsp>slots2) (s≤s z≤n)
          addr>rbp : addr > readReg (regs s-after-setup) rbp
          addr>rbp = subst (addr >_) (sym rbp-setup) (<-trans rsp>rsp-16 addr>rsp)

      thunk-result : ThunkResult prog s s-final caller-sp (λ b → eval f (env , b)) arg
      thunk-result = record
        { thunk-star = star-all
        ; thunk-halted = h-final
        ; thunk-result-valid = thunk-result-valid-proof
        ; thunk-r14 = trans r14-final (trans r14-f r14-setup)
        ; thunk-r15 = trans r15-final (trans r15-f r15-setup)
        ; thunk-rbp = trans rbp-final rbp-f
        ; thunk-stack-inv = stack-inv-final
        ; thunk-capacity = rsp-bound-to-capacity 2 s-final rsp-final-in-stack rsp-sufficient-final
        ; thunk-rsp-plus-8 = thunk-rsp-plus-8-proof
        ; thunk-preserves-frame = thunk-preserves-frame-proof
        ; thunk-preserves-code = thunk-preserves-code-proof
        ; thunk-preserves-heap = thunk-preserves-heap-proof
        ; thunk-preserves-above-entry-rsp = thunk-preserves-above-entry-rsp-proof
        }
