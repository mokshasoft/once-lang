------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.ThunkExec
--
-- Thunk setup and ret execution proofs for curry.
-- Extracted from MutualIR.agda to reduce type-checking time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.ThunkExec where

open import Once.Backend.X86.Correct.Foundation hiding (n≢n+word-size; n+word-size≢n)
open import Once.Backend.X86.Correct.ArithmeticLemmas
  using (pair-fits-post-rbp-push; word-positive; pair-positive)
-- Note: Numeric lemmas (thunk-min-fits-actual, etc.) replaced with symbolic
-- versions from StackInstantiation: after-push1-fits-initial, thunk-frame-fits-initial,
-- post-rbp-push-fits-initial, three-slots-fits-four
-- Note: Capacity lemmas (formerly output-fits-thunk-setup etc.) now use symbolic
-- names from StackInstantiation: output-fits-thunk-cap, apply-cap-after-push-fits-thunk-cap,
-- apply-capacity-fits-thunk-cap
open import Once.Backend.X86.Correct.Arithmetic using (word-plus-one-fits-pair; >-implies-positive)
-- Postulates removed: rsp-bound-after-stack-op, rsp-in-stack-after-stack-op
-- encode, encode-pair-construct removed (unused - only in comments)
-- All stack capacity proofs now derived from input StackCapacity parameter
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInstantiation
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_)

open import Once.Backend.X86.Correct.IR.ThunkStructure
  using (fetch-thunk-i0; fetch-thunk-i1; fetch-thunk-i2; fetch-thunk-i3; fetch-thunk-i4;
         fetch-thunk-i5; fetch-thunk-i6; fetch-thunk-i7;
         thunk-entry-offset; thunk-body-offset; thunk-setup-len)
  renaming (fetch-ret to TS-fetch-ret)

open import Data.Nat using (_>_; _≤?_; _≤_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; m∸n≤m; ≤-trans; ≤-<-trans; ∸-monoˡ-≤; ∸-monoʳ-<;
                                       m∸n+n≡m; m≤n⇒m∸n≡0; +-monoˡ-<; +-monoʳ-<; m<m+n; <-trans;
                                       ∸-+-assoc; m≤m+n)
                                renaming (<⇒≢ to <⇒≢-neq; ≰⇒> to ≰⇒>-nat; <⇒≤ to <⇒≤-nat; ≤-pred to ≤-pred-nat)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

-- Import region lemmas for D041 approach
open import Once.Backend.X86.Layout
  using (InStack; InHeap; InCode; stack-code-addr-disjoint; stack-heap-addr-disjoint;
         StackPointer)
open import Once.Backend.X86.Layout using () renaming (addr to sp-addr)

-- Import validity types for validity-based interface
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt; PairAtS; pair-at-s; valid-pair; valid-subst-heap-preserved)
open import Once.Backend.X86.Correct.StackInstantiation
  using (StackCapacity; capacity-maintained; rsp-bound-to-capacity;
         r15-in-code; slot-size; slots; slots-mono-≤;
         -- Semantic frame sizes and lemmas
         saved-regs-size; saved-regs-fits-thunk-frame;
         thunk-frame-size; thunk-frame-fits-initial; two-push-offset; pair-alloc;
         -- Capacity constants (no hard-coded literals)
         thunk-setup-capacity; output-slots; thunk-local-size;
         thunk-cap-after-first-push; thunk-cap-after-pushes;
         output-fits-thunk-cap;
         -- D041: Parameterized abstract interface
         abstract-to-rsp-slot-in-stack; abstract-to-rsp-slots-in-stack;
         -- D041: Abstract helpers for thunk arithmetic (State-based)
         apply-alloc-below-rsp; thunk-2slot-below-1slot; thunk-2slot-below-orig;
         thunk-2slot-diff-from-orig; thunk-frame-below-orig; thunk-frame-diff-from-above;
         -- D041: Raw ℕ helpers for local variable patterns (semantic names)
         n∸slot<n-raw; n∸2slot<n∸slot-raw; n∸2slot<n-raw; n∸saved-regs<n; n∸saved-regs<n∸slot;
         n∸thunk-frame<n; n∸thunk-frame+slot<n; n∸thunk-frame+slot≡n∸saved-regs;
         -- D041: Generic arithmetic helpers
         ∸-gives-different; ∸-gives-smaller)

------------------------------------------------------------------------
-- ThunkSetupResult: Record type for thunk setup output
-- Replaces deeply nested tuple to improve typechecker performance
------------------------------------------------------------------------

record ThunkSetupResult {A B C : Type} (f : IR (A * B) C)
                        (prog : Program) (s s' : State)
                        (env : ⟦ A ⟧) (arg : ⟦ B ⟧)
                        (f-offset : ℕ) : Set₁ where
  field
    -- Star execution proof
    star-setup : Star prog s s'

    -- Non-halting
    h-setup : halted s' ≡ false

    -- PC advancement
    pc-setup : pc s' ≡ f-offset

    -- Validity output: pair (env, arg) at rdi
    v-pair-setup : ValidAt (env , arg) (readReg (regs s') rdi) (memory s')

    -- Callee-saved register preservation
    r14-setup : readReg (regs s') r14 ≡ readReg (regs s) r14
    r15-setup : readReg (regs s') r15 ≡ readReg (regs s) r15

    -- Frame pointer setup
    rbp-setup : readReg (regs s') rbp ≡ readReg (regs s) rsp ∸ two-push-offset

    -- Stack invariants
    stack-inv-setup : StackInvariant s'
    rsp-sufficient-setup : readReg (regs s') rsp > pair-alloc
    rbp-inv-setup : RbpInvariant s'

    -- RSP delta: thunk setup consumes thunk-setup-consumed-slots (4) slots
    -- Used for capacity threading: given capacity (4 + f-req), after delta we have f-req
    rsp-setup : readReg (regs s') rsp ≡ readReg (regs s) rsp ∸ slots thunk-setup-consumed-slots

    -- Memory at rbp contains original rbp
    mem-at-rbp-setup : readMem (memory s') (readReg (regs s') rbp) ≡ just (readReg (regs s) rbp)

    -- Memory at original rsp preserved (for return address)
    mem-old-rsp-setup : readMem (memory s') (readReg (regs s) rsp) ≡ readMem (memory s) (readReg (regs s) rsp)

    -- Memory for r15 restoration
    mem-r15-setup : readMem (memory s') (readReg (regs s) rsp ∸ slot-size) ≡ just (readReg (regs s) r15)

    -- Memory at code region preserved
    mem-code-setup : ∀ addr → InCode addr → readMem (memory s') addr ≡ readMem (memory s) addr

    -- Memory at heap region preserved
    mem-heap-setup : ∀ addr → InHeap addr → readMem (memory s') addr ≡ readMem (memory s) addr

    -- Memory above original rsp preserved
    mem-above-setup : ∀ caller-addr → caller-addr > readReg (regs s) rsp →
                      readMem (memory s') caller-addr ≡ readMem (memory s) caller-addr

open ThunkSetupResult public

-- Prove thunk setup: label, push r15, push rbp, mov rbp rsp, sub rsp 16, mov [rsp] r12, mov [rsp+8] rdi, mov rdi rsp
thunk-setup-star : ∀ {A B C} (f : IR (A * B) C)
                   (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ thunk-entry-offset
      f-offset = length prefix +ℕ thunk-body-offset  -- 6 closure-setup + 8 thunk-setup
  in
  halted s ≡ false →
  pc s ≡ thunk-offset →
  ValidAt arg (readReg (regs s) rdi) (memory s) →   -- validity-based!
  ValidAt env (readReg (regs s) r12) (memory s) →   -- validity-based!
  StackInvariant s →
  StackCapacity s thunk-setup-capacity →
  ∃[ s' ] ThunkSetupResult f prog s s' env arg f-offset
thunk-setup-star {A} {B} {C} f prefix suffix env arg s
                 h-false pc-eq v-arg v-env stack-inv cap =
  s8 , record
    { star-setup = star-all
    ; h-setup = h8
    ; pc-setup = pc8
    ; v-pair-setup = v-pair
    ; r14-setup = r14-8
    ; r15-setup = r15-8
    ; rbp-setup = rbp8
    ; stack-inv-setup = stack-inv8
    ; rsp-sufficient-setup = rsp-sufficient-8
    ; rbp-inv-setup = rbp-inv8
    ; rsp-setup = rsp-setup-8
    ; mem-at-rbp-setup = mem-at-rbp8
    ; mem-old-rsp-setup = mem-old-rsp-preserved
    ; mem-r15-setup = mem-r15-preserved
    ; mem-code-setup = mem-code-preserved
    ; mem-heap-setup = mem-heap-preserved
    ; mem-above-setup = mem-above-rsp-preserved
    }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (m∸n≤m; ≤-trans)
    open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+word-size)

    prog = prefix ++ compile-x86 (curry f) ++ suffix
    offset = length prefix
    thunk-offset = offset +ℕ thunk-entry-offset
    f-offset = offset +ℕ thunk-body-offset  -- 6 closure-setup + 8 thunk-setup

    -- The 8 thunk setup instructions (at positions 6-13 within curry)
    -- These match the compile-x86 curry definition exactly
    i0 = label thunk-entry-offset          -- label at thunk entry (code-ptr-label = 6)
    i1 = push (reg r15)                    -- save r15 (apply's scratch register)
    i2 = push (reg rbp)                    -- save frame pointer
    i3 = mov (reg rbp) (reg rsp)           -- set frame pointer
    i4 = sub (reg rsp) (imm thunk-local-size)            -- allocate pair
    i5 = mov (mem (base rsp)) (reg r12)    -- store env
    i6 = mov (mem (base+disp rsp slot-size)) (reg rdi)  -- store arg
    i7 = mov (reg rdi) (reg rsp)           -- rdi = pair address

    -- Program structure for fetch proofs:
    -- prog = prefix ++ compile-x86 (curry f) ++ suffix
    --      = prefix ++ (curry-closure-setup ++ curry-thunk-setup ++ compile-x86 f ++ curry-tail) ++ suffix
    -- where curry-closure-setup has 6 instructions and curry-thunk-setup starts with label 6
    --
    -- For fetch at thunk-offset = offset + 6:
    -- We need to show the program up to thunk-offset has length = offset + 6
    -- Then fetch-at-prefix-end gives us the instruction

    len-f = compile-length f
    end-offset-curry = 12 +ℕ len-f  -- jmp at pos 5 to reach end at 18+len-f

    -- curry-closure-setup: first 6 instructions of curry (positions 0-5)
    curry-closure-setup : Program
    curry-closure-setup =
      sub (reg rsp) (imm thunk-local-size) ∷
      mov (mem (base rsp)) (reg rdi) ∷
      lea r9 (rip+disp 4) ∷
      mov (mem (base+disp rsp slot-size)) (reg r9) ∷
      mov (reg rax) (reg rsp) ∷
      jmp end-offset-curry ∷ []

    -- Fetch lemmas (proven in ThunkStructure module)
    -- These use the program structure lemmas from ThunkStructure
    fetch0 : fetch prog thunk-offset ≡ just i0
    fetch0 = fetch-thunk-i0 f prefix suffix

    fetch1 : fetch prog (thunk-offset +ℕ 1) ≡ just i1
    fetch1 = fetch-thunk-i1 f prefix suffix

    fetch2 : fetch prog (thunk-offset +ℕ 2) ≡ just i2
    fetch2 = fetch-thunk-i2 f prefix suffix

    fetch3 : fetch prog (thunk-offset +ℕ 3) ≡ just i3
    fetch3 = fetch-thunk-i3 f prefix suffix

    fetch4 : fetch prog (thunk-offset +ℕ 4) ≡ just i4
    fetch4 = fetch-thunk-i4 f prefix suffix

    fetch5 : fetch prog (thunk-offset +ℕ 5) ≡ just i5
    fetch5 = fetch-thunk-i5 f prefix suffix

    fetch6 : fetch prog (thunk-offset +ℕ 6) ≡ just i6
    fetch6 = fetch-thunk-i6 f prefix suffix

    fetch7 : fetch prog (thunk-offset +ℕ 7) ≡ just i7
    fetch7 = fetch-thunk-i7 f prefix suffix

    old-rsp = readReg (regs s) rsp
    old-rbp = readReg (regs s) rbp
    old-r15 = readReg (regs s) r15
    rsp-after-push-r15 = old-rsp ∸ slot-size   -- after push r15
    rsp-after-push-rbp = rsp-after-push-r15 ∸ slot-size  -- after push rbp = old-rsp - 16
    new-rsp = rsp-after-push-rbp ∸ thunk-local-size  -- after sub rsp, 16 (thunk local allocation)

    -- Derive rsp-bound from cap for compatibility with existing proofs
    -- cap : StackCapacity s thunk-setup-capacity, so cap.rsp-sufficient : old-rsp > slots thunk-setup-capacity
    -- We need old-rsp > slots output-slots, which follows from output-fits-thunk-cap
    rsp-bound : old-rsp > slots output-slots
    rsp-bound = ≤-<-trans (slots-mono-≤ output-fits-thunk-cap) (StackCapacity.rsp-sufficient cap)
      where
        open import Data.Nat.Properties using (≤-<-trans)

    -- Raw register values (addresses where validity holds)
    orig-r12 = readReg (regs s) r12
    orig-rdi = readReg (regs s) rdi

    -- State after label (no-op, just pc++)
    s1 : State
    s1 = record s { pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just s1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execLabel [] s (offset +ℕ thunk-entry-offset))

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ thunk-offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after push r15 (save r15 for apply's scratch register)
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rsp rsp-after-push-r15
                   ; memory = writeMem (memory s1) rsp-after-push-r15 old-r15
                   ; pc = pc s1 +ℕ 1 }

    step1 : step prog s1 ≡ just s2
    step1 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execPush-reg [] s1 r15)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ thunk-offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc thunk-offset 1 1)

    -- State after push rbp (save frame pointer)
    rsp-s2 : readReg (regs s2) rsp ≡ rsp-after-push-r15
    rsp-s2 = readReg-writeReg-same (regs s1) rsp rsp-after-push-r15

    rbp-s2 : readReg (regs s2) rbp ≡ old-rbp
    rbp-s2 = trans (readReg-writeReg-rsp-rbp (regs s1) rsp-after-push-r15) refl

    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rsp rsp-after-push-rbp
                   ; memory = writeMem (memory s2) rsp-after-push-rbp old-rbp
                   ; pc = pc s2 +ℕ 1 }

    step2 : step prog s2 ≡ just s3
    step2 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execPush-reg [] s2 rbp)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ thunk-offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc thunk-offset 2 1)

    -- State after mov rbp, rsp (set frame pointer to current rsp)
    rsp-s3 : readReg (regs s3) rsp ≡ rsp-after-push-rbp
    rsp-s3 = readReg-writeReg-same (regs s2) rsp rsp-after-push-rbp

    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rbp rsp-after-push-rbp
                   ; pc = pc s3 +ℕ 1 }

    step3 : step prog s3 ≡ just s4
    step3 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (cong (λ sp → just (record s3 { regs = writeReg (regs s3) rbp sp
                                                ; pc = pc s3 +ℕ 1 }))
                        rsp-s3)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ thunk-offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc thunk-offset 3 1)

    -- State after sub rsp, 16
    rsp-s4 : readReg (regs s4) rsp ≡ rsp-after-push-rbp
    rsp-s4 = trans (readReg-writeReg-rbp-rsp (regs s3) rsp-after-push-rbp) rsp-s3

    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) rsp new-rsp
                   ; pc = pc s4 +ℕ 1
                   ; flags = updateFlags new-rsp rsp-after-push-rbp }

    step4 : step prog s4 ≡ just s5
    step4 = trans (step-exec prog s4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (execSub-reg-imm [] s4 rsp thunk-local-size)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ thunk-offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc thunk-offset 4 1)

    -- State after mov [rsp], r12 (store env)
    rsp-s5 : readReg (regs s5) rsp ≡ new-rsp
    rsp-s5 = readReg-writeReg-same (regs s4) rsp new-rsp

    -- r12 preserved through setup (no addr-from-valid needed!)
    r12-s5 : readReg (regs s5) r12 ≡ orig-r12
    r12-s5 = trans (readReg-writeReg-rsp-r12 (regs s4) new-rsp)
                   (trans (readReg-writeReg-rbp-r12 (regs s3) rsp-after-push-rbp)
                          (trans (readReg-writeReg-rsp-r12 (regs s2) rsp-after-push-rbp)
                                 (trans (readReg-writeReg-rsp-r12 (regs s1) rsp-after-push-r15)
                                        refl)))

    s6 : State
    s6 = record s5 { memory = writeMem (memory s5) new-rsp (readReg (regs s5) r12)
                   ; pc = pc s5 +ℕ 1 }

    step5 : step prog s5 ≡ just s6
    step5 = trans (step-exec prog s5 i5 h5 (subst (λ p → fetch prog p ≡ just i5) (sym pc5) fetch5))
                  (cong (λ addr → just (record s5 { memory = writeMem (memory s5) addr (readReg (regs s5) r12)
                                                  ; pc = pc s5 +ℕ 1 }))
                        rsp-s5)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ thunk-offset +ℕ 6
    pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc thunk-offset 5 1)

    -- State after mov [rsp+8], rdi (store arg)
    rsp-s6 : readReg (regs s6) rsp ≡ new-rsp
    rsp-s6 = rsp-s5

    -- rdi preserved through setup (no addr-from-valid needed!)
    rdi-s6 : readReg (regs s6) rdi ≡ orig-rdi
    rdi-s6 = trans (readReg-writeReg-rsp-rdi (regs s4) new-rsp)
                   (trans (readReg-writeReg-rbp-rdi (regs s3) rsp-after-push-rbp)
                          (trans (readReg-writeReg-rsp-rdi (regs s2) rsp-after-push-rbp)
                                 (trans (readReg-writeReg-rsp-rdi (regs s1) rsp-after-push-r15)
                                        refl)))

    s7 : State
    s7 = record s6 { memory = writeMem (memory s6) (new-rsp +ℕ slot-size) (readReg (regs s6) rdi)
                   ; pc = pc s6 +ℕ 1 }

    step6 : step prog s6 ≡ just s7
    step6 = trans (step-exec prog s6 i6 h6 (subst (λ p → fetch prog p ≡ just i6) (sym pc6) fetch6))
                  (cong (λ addr → just (record s6 { memory = writeMem (memory s6) (addr +ℕ slot-size) (readReg (regs s6) rdi)
                                                  ; pc = pc s6 +ℕ 1 }))
                        rsp-s6)

    h7 : halted s7 ≡ false
    h7 = h-false

    pc7 : pc s7 ≡ thunk-offset +ℕ 7
    pc7 = trans (cong (_+ℕ 1) pc6) (+-assoc thunk-offset 6 1)

    -- State after mov rdi, rsp (rdi = pair address)
    rsp-s7 : readReg (regs s7) rsp ≡ new-rsp
    rsp-s7 = rsp-s6

    s8 : State
    s8 = record s7 { regs = writeReg (regs s7) rdi new-rsp
                   ; pc = pc s7 +ℕ 1 }

    step7 : step prog s7 ≡ just s8
    step7 = trans (step-exec prog s7 i7 h7 (subst (λ p → fetch prog p ≡ just i7) (sym pc7) fetch7))
                  (cong (λ sp → just (record s7 { regs = writeReg (regs s7) rdi sp
                                                ; pc = pc s7 +ℕ 1 }))
                        rsp-s7)

    -- Compose Star proof
    star-all : Star prog s s8
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               ⟨ h5 , step5 ⟩◅
               ⟨ h6 , step6 ⟩◅
               ⟨ h7 , step7 ⟩◅
               refl*

    -- Final state properties
    h8 : halted s8 ≡ false
    h8 = h-false

    pc8 : pc s8 ≡ f-offset
    pc8 = begin
      pc s8
        ≡⟨ refl ⟩
      pc s7 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc7 ⟩
      (thunk-offset +ℕ 7) +ℕ 1
        ≡⟨ +-assoc thunk-offset 7 1 ⟩
      thunk-offset +ℕ 8
        ≡⟨ cong (_+ℕ thunk-setup-len) refl ⟩  -- thunk-offset = offset + 6, thunk-setup-len = 8
      (offset +ℕ thunk-entry-offset) +ℕ thunk-setup-len
        ≡⟨ +-assoc offset thunk-entry-offset thunk-setup-len ⟩
      offset +ℕ thunk-body-offset
        ≡⟨ refl ⟩
      f-offset ∎

    -- rdi = new-rsp after s8 (mov rdi, rsp), and memory[new-rsp] = encode env, memory[new-rsp+8] = encode arg
    -- By encode-pair-construct, new-rsp = encode (env, arg)
    rdi-s8-is-new-rsp : readReg (regs s8) rdi ≡ new-rsp
    rdi-s8-is-new-rsp = readReg-writeReg-same (regs s7) rdi new-rsp

    -- Memory at new-rsp has orig-r12 (no encode needed!)
    -- s8 doesn't write memory (only rdi register), so memory s8 = memory s7
    mem-env-raw : readMem (memory s8) new-rsp ≡ just orig-r12
    mem-env-raw = trans (mem-read-other {memory s6} {new-rsp +ℕ slot-size} {new-rsp} {readReg (regs s6) rdi}
                         (λ eq → n≢n+word-size new-rsp (sym eq)))
                        (trans (mem-read-write {memory s5} {new-rsp} {readReg (regs s5) r12})
                               (cong just r12-s5))

    -- Memory at new-rsp+8 has orig-rdi (no encode needed!)
    mem-arg-raw : readMem (memory s8) (new-rsp +ℕ slot-size) ≡ just orig-rdi
    mem-arg-raw = trans (mem-read-write {memory s6} {new-rsp +ℕ slot-size} {readReg (regs s6) rdi})
                        (cong just rdi-s6)

    -- NOTE: Removed encode-based proofs (pair-encoding, rdi8) - not needed with validity output!

    -- Register preservation (through all 8 instructions)
    -- Note: rbp is NOT preserved - it's set to frame pointer
    -- Trace: s8 writes rdi, s7 no regs, s6 no regs, s5 writes rsp, s4 writes rbp, s3 writes rsp, s2 writes rsp, s1 no regs
    r14-8 : readReg (regs s8) r14 ≡ readReg (regs s) r14
    r14-8 = trans (readReg-writeReg-rdi-r14 (regs s7) new-rsp)  -- s8: writes rdi
                  (trans (readReg-writeReg-rsp-r14 (regs s4) new-rsp)  -- s5: writes rsp
                         (trans (readReg-writeReg-rbp-r14 (regs s3) rsp-after-push-rbp)  -- s4: writes rbp
                                (trans (readReg-writeReg-rsp-r14 (regs s2) rsp-after-push-rbp)  -- s3: writes rsp
                                       (trans (readReg-writeReg-rsp-r14 (regs s1) rsp-after-push-r15)  -- s2: writes rsp
                                              refl))))

    r15-8 : readReg (regs s8) r15 ≡ readReg (regs s) r15
    r15-8 = trans (readReg-writeReg-rdi-r15 (regs s7) new-rsp)  -- s8: writes rdi
                  (trans (readReg-writeReg-rsp-r15 (regs s4) new-rsp)  -- s5: writes rsp
                         (trans (readReg-writeReg-rbp-r15 (regs s3) rsp-after-push-rbp)  -- s4: writes rbp
                                (trans (readReg-writeReg-rsp-r15 (regs s2) rsp-after-push-rbp)  -- s3: writes rsp
                                       (trans (readReg-writeReg-rsp-r15 (regs s1) rsp-after-push-r15)  -- s2: writes rsp
                                              refl))))

    -- rbp is now set to rsp-after-push-rbp (the frame pointer, = old-rsp - 16)
    rbp8' : readReg (regs s8) rbp ≡ rsp-after-push-rbp
    rbp8' = trans (readReg-writeReg-rdi-rbp (regs s7) new-rsp)  -- s8: writes rdi
                 (trans (readReg-writeReg-rsp-rbp (regs s4) new-rsp)  -- s5: writes rsp
                        (readReg-writeReg-same (regs s3) rbp rsp-after-push-rbp))  -- s4: writes rbp

    -- Prove that (old-rsp ∸ slot-size) ∸ 8 ≡ old-rsp ∸ two-push-offset
    -- Using ∸-+-assoc : ∀ m n o → (m ∸ n) ∸ o ≡ m ∸ (n + o)
    open import Data.Nat.Properties using (∸-+-assoc)
    rsp-after-push-rbp≡old-rsp∸16 : rsp-after-push-rbp ≡ old-rsp ∸ two-push-offset
    rsp-after-push-rbp≡old-rsp∸16 = ∸-+-assoc old-rsp slot-size slot-size

    -- Convert to expected type
    rbp8 : readReg (regs s8) rbp ≡ old-rsp ∸ two-push-offset
    rbp8 = trans rbp8' rsp-after-push-rbp≡old-rsp∸16

    -- StackInvariant proof: rsp decreased, r15 unchanged
    -- s8.rsp = new-rsp = old-rsp - 16 - 16 = old-rsp - 32 ≤ old-rsp = s.rsp
    rsp-s8 : readReg (regs s8) rsp ≡ new-rsp
    rsp-s8 = trans (readReg-writeReg-rdi-rsp (regs s7) new-rsp) rsp-s7

    -- new-rsp = ((old-rsp - 8) - 8) - 16 = old-rsp - 32 ≤ old-rsp
    rsp-decreased : new-rsp ≤ old-rsp
    rsp-decreased = ≤-trans (≤-trans (m∸n≤m rsp-after-push-rbp thunk-local-size) (m∸n≤m rsp-after-push-r15 slot-size)) (m∸n≤m old-rsp slot-size)

    rsp-s8≤s : readReg (regs s8) rsp ≤ readReg (regs s) rsp
    rsp-s8≤s = subst (_≤ old-rsp) (sym rsp-s8) rsp-decreased

    -- RSP delta for capacity threading: s8.rsp = old-rsp - slots thunk-setup-consumed-slots
    -- Derivation: new-rsp = (old-rsp - two-push-offset) - thunk-local-size = old-rsp - thunk-frame-size
    rsp-setup-8 : readReg (regs s8) rsp ≡ old-rsp ∸ slots thunk-setup-consumed-slots
    rsp-setup-8 = trans rsp-s8 new-rsp-eq-global
      where
        -- new-rsp = rsp-after-push-rbp - thunk-local-size
        -- rsp-after-push-rbp = old-rsp - two-push-offset
        -- So new-rsp = old-rsp - two-push-offset - thunk-local-size = old-rsp - thunk-frame-size
        new-rsp-eq-global : new-rsp ≡ old-rsp ∸ slots thunk-setup-consumed-slots
        new-rsp-eq-global = trans (cong (_∸ two-push-offset) rsp-after-push-rbp≡old-rsp∸16)
                                  (∸-+-assoc old-rsp two-push-offset thunk-local-size)

    stack-inv8 : StackInvariant s8
    stack-inv8 = stack-inv-preserved-r15-unchanged s s8 stack-inv r15-8 rsp-s8≤s

    -- Thread StackCapacity through state transitions to derive rsp-sufficient-8
    -- State flow: s → s1 (label) → s2 (push r15) → s3 (push rbp) → s4 (mov) → s5 (sub 16) → s6-s8 (movs)
    -- Capacity: thunk-setup-capacity → ... → output-slots

    -- s1 only changes pc, not regs
    rsp-s1-eq : readReg (regs s1) rsp ≡ readReg (regs s) rsp
    rsp-s1-eq = refl

    cap-at-label : StackCapacity s1 thunk-setup-capacity
    cap-at-label = capacity-preserved-rsp-unchanged s s1 thunk-setup-capacity cap rsp-s1-eq

    -- s2: push r15 (rsp -= 8)
    rsp-s2-from-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp ∸ slot-size
    rsp-s2-from-s1 = rsp-s2

    cap-after-push-r15 : StackCapacity s2 thunk-cap-after-first-push
    cap-after-push-r15 = capacity-after-push s1 s2 thunk-cap-after-first-push cap-at-label rsp-s2-from-s1

    -- s3: push rbp (rsp -= 8)
    rsp-s3-from-s2 : readReg (regs s3) rsp ≡ readReg (regs s2) rsp ∸ slot-size
    rsp-s3-from-s2 = trans rsp-s3 (cong (_∸ slot-size) (sym rsp-s2))

    cap-after-push-rbp : StackCapacity s3 thunk-cap-after-pushes
    cap-after-push-rbp = capacity-after-push s2 s3 thunk-cap-after-pushes cap-after-push-r15 rsp-s3-from-s2

    -- s4: mov rbp, rsp (no rsp change)
    rsp-s4-eq : readReg (regs s4) rsp ≡ readReg (regs s3) rsp
    rsp-s4-eq = trans rsp-s4 (sym rsp-s3)

    cap-after-mov-rbp : StackCapacity s4 thunk-cap-after-pushes
    cap-after-mov-rbp = capacity-preserved-rsp-unchanged s3 s4 thunk-cap-after-pushes cap-after-push-rbp rsp-s4-eq

    -- s5: sub rsp, 16 (thunk local allocation)
    rsp-s5-from-s4 : readReg (regs s5) rsp ≡ readReg (regs s4) rsp ∸ thunk-local-size
    rsp-s5-from-s4 = trans rsp-s5 (cong (_∸ thunk-local-size) (sym rsp-s4))

    cap-after-alloc : StackCapacity s5 output-slots
    cap-after-alloc = capacity-after-alloc-2-slots s4 s5 output-slots cap-after-mov-rbp rsp-s5-from-s4

    -- s6, s7, s8: memory/rdi writes, no rsp change
    rsp-s6-eq : readReg (regs s6) rsp ≡ readReg (regs s5) rsp
    rsp-s6-eq = trans rsp-s6 (sym rsp-s5)

    cap-after-mov-env : StackCapacity s6 output-slots
    cap-after-mov-env = capacity-preserved-rsp-unchanged s5 s6 output-slots cap-after-alloc rsp-s6-eq

    rsp-s7-eq : readReg (regs s7) rsp ≡ readReg (regs s6) rsp
    rsp-s7-eq = trans rsp-s7 (sym rsp-s6)

    cap-after-mov-arg : StackCapacity s7 output-slots
    cap-after-mov-arg = capacity-preserved-rsp-unchanged s6 s7 output-slots cap-after-mov-env rsp-s7-eq

    rsp-s8-eq : readReg (regs s8) rsp ≡ readReg (regs s7) rsp
    rsp-s8-eq = trans rsp-s8 (sym rsp-s7)

    cap-after-lea : StackCapacity s8 output-slots
    cap-after-lea = capacity-preserved-rsp-unchanged s7 s8 output-slots cap-after-mov-arg rsp-s8-eq

    rsp-sufficient-8 : readReg (regs s8) rsp > slots output-slots
    rsp-sufficient-8 = StackCapacity.rsp-sufficient cap-after-lea

    -- Memory at rbp contains original rbp (from push rbp in s3)
    -- s3 wrote old-rbp at rsp-after-push-rbp (= old-rsp - 16)
    -- s6 wrote at new-rsp (= old-rsp - 32), s7 wrote at new-rsp+8 (= old-rsp - 24)
    -- Neither overwrites rsp-after-push-rbp, so the value persists to s8
    -- rbp in s8 = rsp-after-push-rbp, so readMem s8 rbp = just old-rbp

    -- Need: new-rsp ≢ rsp-after-push-rbp
    -- new-rsp = rsp-after-push-rbp - 16 < rsp-after-push-rbp
    -- Approach: new-rsp < new-rsp + 16 = rsp-after-push-rbp (when 16 ≤ rsp-after-push-rbp)
    open import Data.Nat.Properties using (m∸n+n≡m; +-monoˡ-<; m<m+n; 0<1+n)

    -- Proof: new-rsp = rsp-after-push-rbp - 16 ≢ rsp-after-push-rbp
    -- Key insight: rsp-after-push-rbp = old-rsp - 16 ≥ 1 (since old-rsp > pair-alloc)
    -- Case 1: If rsp-after-push-rbp ≥ 16, then new-rsp = rsp-after-push-rbp - 16 < rsp-after-push-rbp
    -- Case 2: If rsp-after-push-rbp < 16, then new-rsp = 0, but rsp-after-push-rbp ≥ 1 > 0
    open import Data.Nat using (_≤?_; z<s)
    open import Relation.Nullary using (yes; no)

    -- First, show rsp-after-push-rbp ≥ 1 (stronger than just > 0)
    -- rsp-sufficient : old-rsp > pair-alloc, i.e., old-rsp ≥ 17
    -- rsp-after-push-rbp = old-rsp - 16 ≥ 17 - 16 = 1
    open import Data.Nat.Properties using (∸-monoˡ-≤)
    open import Data.Empty using (⊥-elim)

    -- old-rsp ≥ 17 (from rsp-bound)
    17≤old-rsp : 17 ≤ old-rsp
    17≤old-rsp = rsp-bound

    -- rsp-after-push-r15 = old-rsp ∸ slot-size ≥ 17 - 8 = 9
    9≤rsp-after-push-r15 : 9 ≤ rsp-after-push-r15
    9≤rsp-after-push-r15 = ∸-monoˡ-≤ {17} {old-rsp} slot-size 17≤old-rsp

    -- rsp-after-push-rbp = rsp-after-push-r15 ∸ slot-size ≥ 9 - 8 = 1
    1≤rsp-after-push-rbp : 1 ≤ rsp-after-push-rbp
    1≤rsp-after-push-rbp = ∸-monoˡ-≤ {9} {rsp-after-push-r15} slot-size 9≤rsp-after-push-r15

    rsp-after-push-rbp>0 : rsp-after-push-rbp > 0
    rsp-after-push-rbp>0 = 1≤rsp-after-push-rbp

    -- D041: Use centralized ∸-gives-different from StackInstantiation
    new-rsp≢rsp-after-push-rbp : new-rsp ≢ rsp-after-push-rbp
    new-rsp≢rsp-after-push-rbp = ∸-gives-different rsp-after-push-rbp thunk-local-size rsp-after-push-rbp>0 pair-positive

    -- For new-rsp + 8 ≢ rsp-after-push-rbp:
    -- new-rsp + 8 = (rsp-after-push-rbp - 16) + 8
    -- We use cap : StackCapacity s 6, so old-rsp > slots 6 = 48
    -- Therefore rsp-after-push-rbp = old-rsp - 16 ≥ 33, which is always ≥ 16
    -- So new-rsp + 8 = rsp-after-push-rbp - 8 < rsp-after-push-rbp

    -- Derive rsp bound from capacity: rsp > slots thunk-setup-capacity = rsp > 48, i.e. 49 ≤ rsp
    -- (Note: m > n = suc n ≤ m, so rsp > 48 is already 49 ≤ rsp)
    -- We derive 41 ≤ rsp via 41 ≤ 49 ≤ rsp
    rsp-above-r15-slot-bound : 41 ≤ old-rsp
    rsp-above-r15-slot-bound = ≤-trans after-push1-fits-initial (StackCapacity.rsp-sufficient cap)

    -- Semantic: rsp remains safe after first push (r15)
    -- old-rsp ≥ 41, so rsp-after-push-r15 = old-rsp - 8 ≥ 33
    rsp-safe-after-r15-push : 33 ≤ rsp-after-push-r15
    rsp-safe-after-r15-push = ∸-monoˡ-≤ slot-size rsp-above-r15-slot-bound

    -- Semantic: rsp remains safe after second push (rbp)
    -- rsp-after-push-r15 ≥ 33, so rsp-after-push-rbp = rsp-after-push-r15 - 8 ≥ 25
    rsp-safe-after-rbp-push : 25 ≤ rsp-after-push-rbp
    rsp-safe-after-rbp-push = ∸-monoˡ-≤ {33} {rsp-after-push-r15} slot-size rsp-safe-after-r15-push

    -- Semantic: local allocation (16 bytes) fits in available space after pushes
    local-alloc-safe-after-pushes : 16 ≤ rsp-after-push-rbp
    local-alloc-safe-after-pushes = ≤-trans pair-fits-post-rbp-push rsp-safe-after-rbp-push

    new-rsp+8≢rsp-after-push-rbp : new-rsp +ℕ slot-size ≢ rsp-after-push-rbp
    new-rsp+8≢rsp-after-push-rbp eq = <⇒≢-neq new-rsp+8<rsp-after-push-rbp eq
      where
        open import Data.Nat.Properties using (m∸n+n≡m)
        -- Semantic: slot-size < local allocation size
        -- new-rsp + slot-size = (rsp-after-push-rbp - local-alloc) + slot-size
        -- Since slot-size < local-alloc, new-rsp + slot-size < rsp-after-push-rbp
        slot-lt-local-alloc : slot-size < thunk-local-size
        slot-lt-local-alloc = word-plus-one-fits-pair
        new-rsp+slot<new-rsp+local : new-rsp +ℕ slot-size < new-rsp +ℕ thunk-local-size
        new-rsp+slot<new-rsp+local = +-monoʳ-< new-rsp slot-lt-local-alloc
        new-rsp+8<rsp-after-push-rbp : new-rsp +ℕ slot-size < rsp-after-push-rbp
        new-rsp+8<rsp-after-push-rbp = subst (new-rsp +ℕ slot-size <_) (m∸n+n≡m local-alloc-safe-after-pushes) new-rsp+slot<new-rsp+local

    -- s3 wrote old-rbp at rsp-after-push-rbp (after push r15 at s2 and push rbp at s3)
    mem-s3-at-rsp-after-push-rbp : readMem (memory s3) rsp-after-push-rbp ≡ just old-rbp
    mem-s3-at-rsp-after-push-rbp = mem-read-write {memory s2} {rsp-after-push-rbp} {old-rbp}

    -- s4, s5 don't write to memory (mov rbp rsp and sub rsp 16)
    mem-s5-at-rsp-after-push-rbp : readMem (memory s5) rsp-after-push-rbp ≡ just old-rbp
    mem-s5-at-rsp-after-push-rbp = mem-s3-at-rsp-after-push-rbp

    -- s6 wrote at new-rsp, which ≢ rsp-after-push-rbp
    mem-s6-at-rsp-after-push-rbp : readMem (memory s6) rsp-after-push-rbp ≡ just old-rbp
    mem-s6-at-rsp-after-push-rbp = trans
      (mem-read-other {memory s5} {new-rsp} {rsp-after-push-rbp} {readReg (regs s5) r12}
                      (λ eq → new-rsp≢rsp-after-push-rbp eq))
      mem-s5-at-rsp-after-push-rbp

    -- s7 wrote at new-rsp + 8, which ≢ rsp-after-push-rbp
    mem-s7-at-rsp-after-push-rbp : readMem (memory s7) rsp-after-push-rbp ≡ just old-rbp
    mem-s7-at-rsp-after-push-rbp = trans
      (mem-read-other {memory s6} {new-rsp +ℕ slot-size} {rsp-after-push-rbp} {readReg (regs s6) rdi}
                      (λ eq → new-rsp+8≢rsp-after-push-rbp eq))
      mem-s6-at-rsp-after-push-rbp

    -- s8 doesn't write to memory (mov rdi rsp only writes register)
    mem-s8-at-rsp-after-push-rbp : readMem (memory s8) rsp-after-push-rbp ≡ just old-rbp
    mem-s8-at-rsp-after-push-rbp = mem-s7-at-rsp-after-push-rbp

    -- Finally, using rbp8: rbp s8 = old-rsp ∸ two-push-offset
    -- First convert mem-s8-at-rsp-after-push-rbp to use old-rsp ∸ two-push-offset
    mem-s8-at-old-rsp∸16 : readMem (memory s8) (old-rsp ∸ two-push-offset) ≡ just old-rbp
    mem-s8-at-old-rsp∸16 = subst (λ addr → readMem (memory s8) addr ≡ just old-rbp)
                                  rsp-after-push-rbp≡old-rsp∸16 mem-s8-at-rsp-after-push-rbp
    mem-at-rbp8 : readMem (memory s8) (readReg (regs s8) rbp) ≡ just old-rbp
    mem-at-rbp8 = subst (λ addr → readMem (memory s8) addr ≡ just old-rbp)
                        (sym rbp8) mem-s8-at-old-rsp∸16

    -- Memory at old-rsp is preserved through setup
    -- s2 writes at rsp-after-push-r15 = old-rsp - 8 ≠ old-rsp
    -- s3 writes at rsp-after-push-rbp = old-rsp - 16 ≠ old-rsp
    -- s6 writes at new-rsp = old-rsp - 32 ≠ old-rsp
    -- s7 writes at new-rsp + 8 = old-rsp - 24 ≠ old-rsp
    rsp-after-push-r15≢old-rsp : rsp-after-push-r15 ≢ old-rsp
    rsp-after-push-r15≢old-rsp = ∸-gives-different old-rsp slot-size (>-implies-positive rsp-bound) word-positive

    -- rsp-after-push-rbp = old-rsp - 16 < old-rsp (D041: use abstract helper)
    rsp-after-push-rbp≢old-rsp : rsp-after-push-rbp ≢ old-rsp
    rsp-after-push-rbp≢old-rsp eq = <⇒≢-neq rsp-after-push-rbp<old-rsp eq
      where
        rsp-after-push-rbp<old-rsp : rsp-after-push-rbp < old-rsp
        rsp-after-push-rbp<old-rsp = subst (_< old-rsp) (sym rsp-after-push-rbp≡old-rsp∸16) (n∸2slot<n-raw old-rsp rsp-bound)

    -- new-rsp = old-rsp - 32 < old-rsp (D041: eliminate with, use abstract helper)
    new-rsp≢old-rsp : new-rsp ≢ old-rsp
    new-rsp≢old-rsp eq = <⇒≢-neq new-rsp<old-rsp eq
      where
        -- Derive new-rsp = old-rsp ∸ thunk-frame-size locally
        new-rsp-eq-local : new-rsp ≡ old-rsp ∸ thunk-frame-size
        new-rsp-eq-local = trans (cong (_∸ two-push-offset) rsp-after-push-rbp≡old-rsp∸16) (∸-+-assoc old-rsp two-push-offset thunk-local-size)
        -- Use abstract helper: (old-rsp ∸ thunk-frame-size) < old-rsp when old-rsp > pair-alloc
        new-rsp<old-rsp : new-rsp < old-rsp
        new-rsp<old-rsp = subst (_< old-rsp) (sym new-rsp-eq-local) (n∸thunk-frame<n old-rsp rsp-bound)

    -- new-rsp + 8 = (old-rsp - 32) + 8 < old-rsp (D041: eliminate with, use abstract helper)
    new-rsp+8≢old-rsp : new-rsp +ℕ slot-size ≢ old-rsp
    new-rsp+8≢old-rsp eq = <⇒≢-neq new-rsp+8<old-rsp eq
      where
        -- Derive new-rsp = old-rsp ∸ thunk-frame-size locally
        new-rsp-eq-local : new-rsp ≡ old-rsp ∸ thunk-frame-size
        new-rsp-eq-local = trans (cong (_∸ two-push-offset) rsp-after-push-rbp≡old-rsp∸16) (∸-+-assoc old-rsp two-push-offset thunk-local-size)
        -- new-rsp + 8 = (old-rsp ∸ thunk-frame-size) + 8
        new-rsp+8-eq : new-rsp +ℕ slot-size ≡ (old-rsp ∸ thunk-frame-size) +ℕ 8
        new-rsp+8-eq = cong (_+ℕ 8) new-rsp-eq-local
        -- Use abstract helper: (old-rsp ∸ thunk-frame-size) + 8 < old-rsp when old-rsp > pair-alloc
        new-rsp+8<old-rsp : new-rsp +ℕ slot-size < old-rsp
        new-rsp+8<old-rsp = subst (_< old-rsp) (sym new-rsp+8-eq) (n∸thunk-frame+slot<n old-rsp rsp-bound)

    -- s1 doesn't write memory (label instruction)
    mem-s1-old-rsp : readMem (memory s1) old-rsp ≡ readMem (memory s) old-rsp
    mem-s1-old-rsp = refl

    -- s2 writes at rsp-after-push-r15 ≠ old-rsp
    mem-s2-old-rsp : readMem (memory s2) old-rsp ≡ readMem (memory s) old-rsp
    mem-s2-old-rsp = mem-read-other {memory s1} {rsp-after-push-r15} {old-rsp} {old-r15}
                       (λ eq → rsp-after-push-r15≢old-rsp eq)

    -- s3 writes at rsp-after-push-rbp ≠ old-rsp
    mem-s3-old-rsp : readMem (memory s3) old-rsp ≡ readMem (memory s) old-rsp
    mem-s3-old-rsp = trans (mem-read-other {memory s2} {rsp-after-push-rbp} {old-rsp} {old-rbp}
                             (λ eq → rsp-after-push-rbp≢old-rsp eq))
                           mem-s2-old-rsp

    -- s4, s5 don't write memory
    mem-s5-old-rsp : readMem (memory s5) old-rsp ≡ readMem (memory s) old-rsp
    mem-s5-old-rsp = mem-s3-old-rsp

    -- s6 writes at new-rsp ≠ old-rsp
    mem-s6-old-rsp : readMem (memory s6) old-rsp ≡ readMem (memory s) old-rsp
    mem-s6-old-rsp = trans (mem-read-other {memory s5} {new-rsp} {old-rsp} {readReg (regs s5) r12}
                             (λ eq → new-rsp≢old-rsp eq))
                           mem-s5-old-rsp

    -- s7 writes at new-rsp + 8 ≠ old-rsp
    mem-s7-old-rsp : readMem (memory s7) old-rsp ≡ readMem (memory s) old-rsp
    mem-s7-old-rsp = trans (mem-read-other {memory s6} {new-rsp +ℕ slot-size} {old-rsp} {readReg (regs s6) rdi}
                             (λ eq → new-rsp+8≢old-rsp eq))
                           mem-s6-old-rsp

    -- s8 doesn't write memory (mov rdi rsp only writes register)
    mem-old-rsp-preserved : readMem (memory s8) old-rsp ≡ readMem (memory s) old-rsp
    mem-old-rsp-preserved = mem-s7-old-rsp

    -- Memory for r15 restoration: s2 wrote old-r15 at rsp-after-push-r15 = old-rsp - 8
    -- This value is preserved through all subsequent writes
    -- rsp-after-push-r15 = old-rsp - 8, rsp-after-push-rbp = rsp-after-push-r15 - 8
    -- D041: ∸-gives-different gives us: rsp-after-push-r15 ∸ slot-size ≢ rsp-after-push-r15
    -- We need to swap to get: rsp-after-push-r15 ≢ rsp-after-push-r15 ∸ slot-size = rsp-after-push-rbp
    rsp-after-push-r15≢rsp-after-push-rbp : rsp-after-push-r15 ≢ rsp-after-push-rbp
    rsp-after-push-r15≢rsp-after-push-rbp = ≢-sym (∸-gives-different rsp-after-push-r15 slot-size rsp-after-push-r15>0 word-positive)
      where
        open import Relation.Binary.PropositionalEquality using (≢-sym)
        rsp-after-push-r15>0 : rsp-after-push-r15 > 0
        rsp-after-push-r15>0 = ≤-trans (s≤s z≤n) 9≤rsp-after-push-r15

    new-rsp≢rsp-after-push-r15 : new-rsp ≢ rsp-after-push-r15
    new-rsp≢rsp-after-push-r15 eq = <⇒≢-neq new-rsp<rsp-after-push-r15 eq
      where
        -- new-rsp = old-rsp - 32, rsp-after-push-r15 = old-rsp - 8
        -- new-rsp < rsp-after-push-r15 (since 32 > 8)
        new-rsp≤rsp-after-push-rbp : new-rsp ≤ rsp-after-push-rbp
        new-rsp≤rsp-after-push-rbp = m∸n≤m rsp-after-push-rbp thunk-local-size
        rsp-after-push-rbp≤rsp-after-push-r15 : rsp-after-push-rbp ≤ rsp-after-push-r15
        rsp-after-push-rbp≤rsp-after-push-r15 = m∸n≤m rsp-after-push-r15 slot-size
        new-rsp≤rsp-after-push-r15 : new-rsp ≤ rsp-after-push-r15
        new-rsp≤rsp-after-push-r15 = ≤-trans new-rsp≤rsp-after-push-rbp rsp-after-push-rbp≤rsp-after-push-r15
        -- new-rsp = rsp-after-push-rbp - 16 ≤ rsp-after-push-rbp < rsp-after-push-r15
        -- Chain: new-rsp ≤ rsp-after-push-rbp < rsp-after-push-r15
        open import Data.Nat.Properties using (∸-monoʳ-<; n≤1+n)
        8≤rsp-after-push-r15''' : 8 ≤ rsp-after-push-r15
        8≤rsp-after-push-r15''' = ≤-trans (n≤1+n slot-size) 9≤rsp-after-push-r15
        rsp-after-push-rbp<rsp-after-push-r15''' : rsp-after-push-rbp < rsp-after-push-r15
        rsp-after-push-rbp<rsp-after-push-r15''' = ∸-monoʳ-< (s≤s z≤n) 8≤rsp-after-push-r15'''
        new-rsp<rsp-after-push-r15 : new-rsp < rsp-after-push-r15
        new-rsp<rsp-after-push-r15 = ≤-trans (s≤s new-rsp≤rsp-after-push-rbp) rsp-after-push-rbp<rsp-after-push-r15'''

    -- new-rsp + 8 = old-rsp - 24 < old-rsp - 8 = rsp-after-push-r15 (D041: eliminate with)
    new-rsp+8≢rsp-after-push-r15 : new-rsp +ℕ slot-size ≢ rsp-after-push-r15
    new-rsp+8≢rsp-after-push-r15 eq = <⇒≢-neq new-rsp+8<rsp-after-push-r15 eq
      where
        -- Semantic: rsp is at least 4 slots above the r15 slot bound
        -- (Note: rsp-sufficient cap : old-rsp > 48 = 49 ≤ old-rsp)
        rsp-above-4-slots : 32 ≤ old-rsp
        rsp-above-4-slots = ≤-trans thunk-frame-fits-initial (StackCapacity.rsp-sufficient cap)
        -- Semantic: rsp is above 3-slot offset (for new-rsp + slot calculation)
        rsp-above-3-slot-offset : old-rsp > 24
        rsp-above-3-slot-offset = ≤-trans post-rbp-push-fits-initial (StackCapacity.rsp-sufficient cap)
        -- new-rsp = old-rsp ∸ thunk-frame-size
        new-rsp-eq-local : new-rsp ≡ old-rsp ∸ thunk-frame-size
        new-rsp-eq-local = trans (cong (_∸ two-push-offset) rsp-after-push-rbp≡old-rsp∸16) (∸-+-assoc old-rsp two-push-offset thunk-local-size)
        -- new-rsp + slot-size = (old-rsp ∸ thunk-frame-size) + slot-size = old-rsp ∸ saved-regs-size
        new-rsp+slot≡old-rsp∸3slots : new-rsp +ℕ slot-size ≡ old-rsp ∸ saved-regs-size
        new-rsp+slot≡old-rsp∸3slots = trans (cong (_+ℕ 8) new-rsp-eq-local) (n∸thunk-frame+slot≡n∸saved-regs old-rsp rsp-above-4-slots)
        -- old-rsp ∸ saved-regs-size < old-rsp ∸ slot-size = rsp-after-push-r15
        offset-3slots-lt-1slot : old-rsp ∸ saved-regs-size < old-rsp ∸ slot-size
        offset-3slots-lt-1slot = n∸saved-regs<n∸slot old-rsp rsp-above-3-slot-offset
        -- Therefore new-rsp + slot-size < rsp-after-push-r15
        new-rsp+8<rsp-after-push-r15 : new-rsp +ℕ slot-size < rsp-after-push-r15
        new-rsp+8<rsp-after-push-r15 = subst (_< old-rsp ∸ slot-size) (sym new-rsp+slot≡old-rsp∸3slots) offset-3slots-lt-1slot

    -- Now prove r15 memory preservation
    -- s2 wrote old-r15 at rsp-after-push-r15
    mem-s2-at-rsp-after-push-r15 : readMem (memory s2) rsp-after-push-r15 ≡ just old-r15
    mem-s2-at-rsp-after-push-r15 = mem-read-write {memory s1} {rsp-after-push-r15} {old-r15}

    -- s3 wrote at rsp-after-push-rbp ≠ rsp-after-push-r15
    mem-s3-at-rsp-after-push-r15 : readMem (memory s3) rsp-after-push-r15 ≡ just old-r15
    mem-s3-at-rsp-after-push-r15 = trans
      (mem-read-other {memory s2} {rsp-after-push-rbp} {rsp-after-push-r15} {old-rbp}
                      (λ eq → rsp-after-push-r15≢rsp-after-push-rbp (sym eq)))
      mem-s2-at-rsp-after-push-r15

    -- s4, s5 don't write memory
    mem-s5-at-rsp-after-push-r15 : readMem (memory s5) rsp-after-push-r15 ≡ just old-r15
    mem-s5-at-rsp-after-push-r15 = mem-s3-at-rsp-after-push-r15

    -- s6 wrote at new-rsp ≠ rsp-after-push-r15
    mem-s6-at-rsp-after-push-r15 : readMem (memory s6) rsp-after-push-r15 ≡ just old-r15
    mem-s6-at-rsp-after-push-r15 = trans
      (mem-read-other {memory s5} {new-rsp} {rsp-after-push-r15} {readReg (regs s5) r12}
                      (λ eq → new-rsp≢rsp-after-push-r15 eq))
      mem-s5-at-rsp-after-push-r15

    -- s7 wrote at new-rsp + 8 ≠ rsp-after-push-r15
    mem-s7-at-rsp-after-push-r15 : readMem (memory s7) rsp-after-push-r15 ≡ just old-r15
    mem-s7-at-rsp-after-push-r15 = trans
      (mem-read-other {memory s6} {new-rsp +ℕ slot-size} {rsp-after-push-r15} {readReg (regs s6) rdi}
                      (λ eq → new-rsp+8≢rsp-after-push-r15 eq))
      mem-s6-at-rsp-after-push-r15

    -- s8 doesn't write memory
    mem-r15-preserved : readMem (memory s8) (old-rsp ∸ slot-size) ≡ just old-r15
    mem-r15-preserved = mem-s7-at-rsp-after-push-r15

    ------------------------------------------------------------------------
    -- D041: Memory at address 0 preserved (all writes are to stack region)
    ------------------------------------------------------------------------

    -- Use input cap : StackCapacity s 6 directly to prove write addresses are in stack region
    -- cap has capacity 6, which is sufficient for all operations that need up to 5 slots

    -- Write addresses are all in stack region
    -- Need to use ∸-+-assoc to relate nested subtractions to flat ones
    -- ∸-+-assoc m n o : (m ∸ n) ∸ o ≡ m ∸ (n + o)

    -- rsp-after-push-r15 = old-rsp ∸ slot-size matches old-rsp ∸ 1*8 directly (via abstract interface)
    addr-rsp-8-in-stack : InStack rsp-after-push-r15
    addr-rsp-8-in-stack = abstract-to-rsp-slot-in-stack s cap

    -- rsp-after-push-rbp = (old-rsp ∸ slot-size) ∸ 8 = old-rsp ∸ two-push-offset = old-rsp ∸ 2*8
    rsp-after-push-rbp-eq : rsp-after-push-rbp ≡ old-rsp ∸ two-push-offset
    rsp-after-push-rbp-eq = ∸-+-assoc old-rsp slot-size slot-size

    addr-rsp-16-in-stack : InStack rsp-after-push-rbp
    addr-rsp-16-in-stack = subst (λ x → InStack x) (sym rsp-after-push-rbp-eq)
                                 (abstract-to-rsp-slots-in-stack 2 s cap output-fits-thunk-cap)

    -- RbpInvariant: thunk creates a new frame at rsp-after-push-rbp = old-rsp - 16
    -- addr-rsp-16-in-stack has type InStack rsp-after-push-rbp
    -- We need InStack (old-rsp ∸ two-push-offset), so use rsp-after-push-rbp-eq to convert
    setup-thunk-frame : StackPointer
    setup-thunk-frame = record
      { addr = old-rsp ∸ two-push-offset
      ; in-stack = subst (λ x → InStack x) rsp-after-push-rbp-eq addr-rsp-16-in-stack
      }

    new-rsp≤frame : new-rsp ≤ old-rsp ∸ two-push-offset
    new-rsp≤frame = subst (new-rsp ≤_) rsp-after-push-rbp≡old-rsp∸16 (m∸n≤m rsp-after-push-rbp thunk-local-size)

    setup-thunk-frame-bound : sp-addr setup-thunk-frame ≥ readReg (regs s8) rsp
    setup-thunk-frame-bound = subst (old-rsp ∸ two-push-offset ≥_) (sym rsp-s8) new-rsp≤frame

    rbp-inv8 : RbpInvariant s8
    rbp-inv8 = record
      { rbp-frame = setup-thunk-frame
      ; rbp-is-base = rbp8  -- rbp s8 = old-rsp ∸ two-push-offset = sp-addr setup-thunk-frame
      ; frame-bound = setup-thunk-frame-bound
      }

    -- new-rsp = ((old-rsp ∸ slot-size) ∸ 8) ∸ 16 = (old-rsp ∸ two-push-offset) ∸ 16 = old-rsp ∸ thunk-frame-size = old-rsp ∸ 4*8
    new-rsp-eq : new-rsp ≡ old-rsp ∸ thunk-frame-size
    new-rsp-eq = trans (cong (_∸ two-push-offset) rsp-after-push-rbp-eq) (∸-+-assoc old-rsp two-push-offset thunk-local-size)

    addr-rsp-32-in-stack : InStack new-rsp
    addr-rsp-32-in-stack = subst (λ x → InStack x) (sym new-rsp-eq)
                                 (abstract-to-rsp-slots-in-stack 4 s cap apply-capacity-fits-thunk-cap)

    -- new-rsp + 8 = (old-rsp ∸ thunk-frame-size) + 8 = old-rsp ∸ saved-regs-size = old-rsp ∸ 3*8
    -- Proof using stdlib: m∸n+n≡m and +-∸-assoc
    -- Strategy: (old-rsp ∸ thunk-frame-size) + 8 = old-rsp ∸ saved-regs-size
    --   Let k = old-rsp ∸ thunk-frame-size. Then k + 32 = old-rsp (by m∸n+n≡m).
    --   old-rsp ∸ saved-regs-size = (k + 32) ∸ saved-regs-size = k + (32 ∸ saved-regs-size) = k + 8 (by +-∸-assoc)
    new-rsp+8-eq : new-rsp +ℕ slot-size ≡ old-rsp ∸ saved-regs-size
    new-rsp+8-eq = trans (cong (_+ℕ 8) new-rsp-eq) offset-plus-slot≡orig-minus-3slots
      where
        open import Data.Nat.Properties using (+-∸-assoc)

        -- Semantic: offset from original rsp to 4-slot position
        rsp-offset-4-slots = old-rsp ∸ thunk-frame-size

        -- Semantic: rsp is large enough for 4-slot addressing
        -- (Note: rsp-sufficient cap : old-rsp > 48 = 49 ≤ old-rsp)
        rsp-fits-4-slots : 32 ≤ old-rsp
        rsp-fits-4-slots = ≤-trans thunk-frame-fits-initial (StackCapacity.rsp-sufficient cap)

        -- Semantic: offset + 4-slots = original rsp
        offset-plus-4-slots≡orig : rsp-offset-4-slots +ℕ thunk-frame-size ≡ old-rsp
        offset-plus-4-slots≡orig = m∸n+n≡m rsp-fits-4-slots

        -- Semantic: saved-regs fits in 4 slots allocation (for associativity)
        three-slots-fit-in-four : saved-regs-size ≤ thunk-frame-size
        three-slots-fit-in-four = saved-regs-fits-thunk-frame

        -- Semantic: associativity for 4-slot minus 3-slot = offset + slot-size
        assoc-4-minus-3 : (rsp-offset-4-slots +ℕ thunk-frame-size) ∸ saved-regs-size ≡ rsp-offset-4-slots +ℕ 8
        assoc-4-minus-3 = +-∸-assoc rsp-offset-4-slots three-slots-fit-in-four

        -- Semantic: offset + slot-size = old-rsp - 3 slots
        offset-plus-slot≡orig-minus-3slots : rsp-offset-4-slots +ℕ 8 ≡ old-rsp ∸ saved-regs-size
        offset-plus-slot≡orig-minus-3slots = sym (trans (cong (_∸ saved-regs-size) (sym offset-plus-4-slots≡orig)) assoc-4-minus-3)

    addr-rsp-24-in-stack : InStack (new-rsp +ℕ slot-size)
    addr-rsp-24-in-stack = subst (λ x → InStack x) (sym new-rsp+8-eq)
                                 (abstract-to-rsp-slots-in-stack 3 s cap apply-cap-after-push-fits-thunk-cap)

    ------------------------------------------------------------------------
    -- D041: Memory at code-region addresses preserved
    ------------------------------------------------------------------------

    -- For any code address, it's not equal to any of the write addresses
    -- because stack region is disjoint from code region
    code-addr≢write-addr : ∀ addr → InCode addr →
      addr ≢ rsp-after-push-r15 × addr ≢ rsp-after-push-rbp ×
      addr ≢ new-rsp × addr ≢ (new-rsp +ℕ slot-size)
    code-addr≢write-addr addr addr-code =
      (λ eq → stack-code-addr-disjoint rsp-after-push-r15 addr addr-rsp-8-in-stack addr-code (sym eq)) ,
      (λ eq → stack-code-addr-disjoint rsp-after-push-rbp addr addr-rsp-16-in-stack addr-code (sym eq)) ,
      (λ eq → stack-code-addr-disjoint new-rsp addr addr-rsp-32-in-stack addr-code (sym eq)) ,
      (λ eq → stack-code-addr-disjoint (new-rsp +ℕ slot-size) addr addr-rsp-24-in-stack addr-code (sym eq))

    -- Chain memory preservation at code addresses through all states
    mem-code-preserved : ∀ addr → InCode addr → readMem (memory s8) addr ≡ readMem (memory s) addr
    mem-code-preserved addr addr-code = mem-s7-code
      where
        disj = code-addr≢write-addr addr addr-code
        addr≢rsp-8 = proj₁ disj
        addr≢rsp-16 = proj₁ (proj₂ disj)
        addr≢rsp-32 = proj₁ (proj₂ (proj₂ disj))
        addr≢rsp-24 = proj₂ (proj₂ (proj₂ disj))

        -- s1 doesn't write memory
        mem-s1-code : readMem (memory s1) addr ≡ readMem (memory s) addr
        mem-s1-code = refl

        -- s2 writes at rsp-8 ≠ addr
        mem-s2-code : readMem (memory s2) addr ≡ readMem (memory s) addr
        mem-s2-code = mem-read-other {memory s1} {rsp-after-push-r15} {addr} {old-r15} (λ eq → addr≢rsp-8 (sym eq))

        -- s3 writes at rsp-16 ≠ addr
        mem-s3-code : readMem (memory s3) addr ≡ readMem (memory s) addr
        mem-s3-code = trans (mem-read-other {memory s2} {rsp-after-push-rbp} {addr} {old-rbp} (λ eq → addr≢rsp-16 (sym eq)))
                            mem-s2-code

        -- s4, s5 don't write memory
        mem-s5-code : readMem (memory s5) addr ≡ readMem (memory s) addr
        mem-s5-code = mem-s3-code

        -- s6 writes at new-rsp ≠ addr
        mem-s6-code : readMem (memory s6) addr ≡ readMem (memory s) addr
        mem-s6-code = trans (mem-read-other {memory s5} {new-rsp} {addr} {readReg (regs s5) r12} (λ eq → addr≢rsp-32 (sym eq)))
                            mem-s5-code

        -- s7 writes at new-rsp + 8 ≠ addr
        mem-s7-code : readMem (memory s7) addr ≡ readMem (memory s) addr
        mem-s7-code = trans (mem-read-other {memory s6} {new-rsp +ℕ slot-size} {addr} {readReg (regs s6) rdi} (λ eq → addr≢rsp-24 (sym eq)))
                            mem-s6-code

    ------------------------------------------------------------------------
    -- D041: Memory at heap-region addresses preserved
    ------------------------------------------------------------------------

    -- For any heap address, it's not equal to any of the write addresses
    -- because stack region is disjoint from heap region
    heap-addr≢write-addr : ∀ addr → InHeap addr →
      addr ≢ rsp-after-push-r15 × addr ≢ rsp-after-push-rbp ×
      addr ≢ new-rsp × addr ≢ (new-rsp +ℕ slot-size)
    heap-addr≢write-addr addr addr-heap =
      (λ eq → stack-heap-addr-disjoint rsp-after-push-r15 addr addr-rsp-8-in-stack addr-heap (sym eq)) ,
      (λ eq → stack-heap-addr-disjoint rsp-after-push-rbp addr addr-rsp-16-in-stack addr-heap (sym eq)) ,
      (λ eq → stack-heap-addr-disjoint new-rsp addr addr-rsp-32-in-stack addr-heap (sym eq)) ,
      (λ eq → stack-heap-addr-disjoint (new-rsp +ℕ slot-size) addr addr-rsp-24-in-stack addr-heap (sym eq))

    -- Chain memory preservation at heap addresses through all states
    mem-heap-preserved : ∀ addr → InHeap addr → readMem (memory s8) addr ≡ readMem (memory s) addr
    mem-heap-preserved addr addr-heap = mem-s7-heap
      where
        disj = heap-addr≢write-addr addr addr-heap
        addr≢rsp-8 = proj₁ disj
        addr≢rsp-16 = proj₁ (proj₂ disj)
        addr≢rsp-32 = proj₁ (proj₂ (proj₂ disj))
        addr≢rsp-24 = proj₂ (proj₂ (proj₂ disj))

        -- s1 doesn't write memory
        mem-s1-heap : readMem (memory s1) addr ≡ readMem (memory s) addr
        mem-s1-heap = refl

        -- s2 writes at rsp-8 ≠ addr
        mem-s2-heap : readMem (memory s2) addr ≡ readMem (memory s) addr
        mem-s2-heap = mem-read-other {memory s1} {rsp-after-push-r15} {addr} {old-r15} (λ eq → addr≢rsp-8 (sym eq))

        -- s3 writes at rsp-16 ≠ addr
        mem-s3-heap : readMem (memory s3) addr ≡ readMem (memory s) addr
        mem-s3-heap = trans (mem-read-other {memory s2} {rsp-after-push-rbp} {addr} {old-rbp} (λ eq → addr≢rsp-16 (sym eq)))
                            mem-s2-heap

        -- s4, s5 don't write memory
        mem-s5-heap : readMem (memory s5) addr ≡ readMem (memory s) addr
        mem-s5-heap = mem-s3-heap

        -- s6 writes at new-rsp ≠ addr
        mem-s6-heap : readMem (memory s6) addr ≡ readMem (memory s) addr
        mem-s6-heap = trans (mem-read-other {memory s5} {new-rsp} {addr} {readReg (regs s5) r12} (λ eq → addr≢rsp-32 (sym eq)))
                            mem-s5-heap

        -- s7 writes at new-rsp + 8 ≠ addr
        mem-s7-heap : readMem (memory s7) addr ≡ readMem (memory s) addr
        mem-s7-heap = trans (mem-read-other {memory s6} {new-rsp +ℕ slot-size} {addr} {readReg (regs s6) rdi} (λ eq → addr≢rsp-24 (sym eq)))
                            mem-s6-heap

    -- Validity output: construct ValidAt (env, arg) from components
    -- NO addr-from-valid bridges needed!

    -- Step 1: Propagate v-env through heap preservation to memory s8
    -- Key: use refl for address (orig-r12 = orig-r12), no encode equality needed!
    v-env-at-s8 : ValidAt env orig-r12 (memory s8)
    v-env-at-s8 = valid-subst-heap-preserved v-env refl mem-heap-preserved

    -- Step 2: Propagate v-arg through heap preservation to memory s8
    v-arg-at-s8 : ValidAt arg orig-rdi (memory s8)
    v-arg-at-s8 = valid-subst-heap-preserved v-arg refl mem-heap-preserved

    -- Step 3: Construct PairAtS from memory layout (using raw addresses)
    pair-layout : PairAtS orig-r12 orig-rdi new-rsp (memory s8)
    pair-layout = pair-at-s mem-env-raw mem-arg-raw

    -- Step 4: Combine using valid-pair
    v-pair : ValidAt (env , arg) (readReg (regs s8) rdi) (memory s8)
    v-pair = subst (λ addr → ValidAt (env , arg) addr (memory s8))
                   (sym rdi-s8-is-new-rsp)
                   (valid-pair v-env-at-s8 v-arg-at-s8 pair-layout)

    -- D041: Memory above original rsp preserved (for caller frame)
    -- Setup writes to: rsp-8 (push r15), rsp-16 (push rbp), rsp-32 (mov [rsp]), rsp-24 (mov [rsp+8])
    -- All write addresses are < old-rsp, so addr > old-rsp implies addr ≠ all write addresses
    mem-above-rsp-preserved : ∀ caller-addr → caller-addr > old-rsp → readMem (memory s8) caller-addr ≡ readMem (memory s) caller-addr
    mem-above-rsp-preserved caller-addr caller-addr>old-rsp = mem-s7-above
      where
        open import Data.Nat.Properties using (<⇒≢; <-≤-trans; <-trans)

        -- D041: Use centralized ∸-gives-smaller from StackInstantiation

        -- Helper: if addr > old-rsp and write-addr < old-rsp, then addr ≠ write-addr
        -- Note: caller-addr > old-rsp means old-rsp < caller-addr (flip of _<_)
        addr≢write : ∀ write-addr → write-addr < old-rsp → caller-addr ≢ write-addr
        addr≢write write-addr write<rsp eq = <⇒≢ (<-trans write<rsp caller-addr>old-rsp) (sym eq)

        -- Semantic: all write addresses are below original rsp
        -- rsp after first push (r15) is below original
        r15-slot-lt-orig : rsp-after-push-r15 < old-rsp
        r15-slot-lt-orig = ∸-gives-smaller old-rsp 8 (≤-trans (s≤s z≤n) rsp-bound) (s≤s z≤n)
          where open import Data.Nat using (s≤s; z≤n)

        -- Semantic: rsp after both pushes is below rsp after first push
        rbp-slot-lt-r15-slot : rsp-after-push-rbp < rsp-after-push-r15
        rbp-slot-lt-r15-slot = ∸-gives-smaller rsp-after-push-r15 8 (≤-trans (s≤s z≤n) rsp-safe-after-r15-push) (s≤s z≤n)
          where open import Data.Nat using (s≤s; z≤n)

        rbp-slot-lt-orig : rsp-after-push-rbp < old-rsp
        rbp-slot-lt-orig = <-trans rbp-slot-lt-r15-slot r15-slot-lt-orig

        -- Semantic: new-rsp (after local alloc) is below rsp after pushes
        local-slot-lt-rbp-slot : new-rsp < rsp-after-push-rbp
        local-slot-lt-rbp-slot = ∸-gives-smaller rsp-after-push-rbp 16 (≤-trans (s≤s z≤n) rsp-safe-after-rbp-push) (s≤s z≤n)
          where open import Data.Nat using (s≤s; z≤n)

        local-slot-lt-orig : new-rsp < old-rsp
        local-slot-lt-orig = <-trans local-slot-lt-rbp-slot rbp-slot-lt-orig

        -- Semantic: new-rsp + slot-size (second local slot) is below original rsp
        second-local-slot-lt-orig : new-rsp +ℕ slot-size < old-rsp
        second-local-slot-lt-orig = <-≤-trans second-local-slot-lt-rbp-slot (Data.Nat.Properties.<⇒≤ rbp-slot-lt-orig)
          where
            open import Data.Nat.Properties using (+-monoʳ-<; m∸n+n≡m)
            -- slot-size < thunk-local-size (8 < 16)
            slot-lt-local-alloc' : slot-size < thunk-local-size
            slot-lt-local-alloc' = word-plus-one-fits-pair
            new-rsp+slot<new-rsp+local' : new-rsp +ℕ slot-size < new-rsp +ℕ thunk-local-size
            new-rsp+slot<new-rsp+local' = +-monoʳ-< new-rsp slot-lt-local-alloc'
            second-local-slot-lt-rbp-slot : new-rsp +ℕ slot-size < rsp-after-push-rbp
            second-local-slot-lt-rbp-slot = subst (new-rsp +ℕ slot-size <_) (m∸n+n≡m local-alloc-safe-after-pushes) new-rsp+slot<new-rsp+local'

        -- Semantic: all write addresses are disjoint from caller's memory
        addr-disjoint-r15-slot : caller-addr ≢ rsp-after-push-r15
        addr-disjoint-r15-slot = addr≢write rsp-after-push-r15 r15-slot-lt-orig

        addr-disjoint-rbp-slot : caller-addr ≢ rsp-after-push-rbp
        addr-disjoint-rbp-slot = addr≢write rsp-after-push-rbp rbp-slot-lt-orig

        addr-disjoint-first-local : caller-addr ≢ new-rsp
        addr-disjoint-first-local = addr≢write new-rsp local-slot-lt-orig

        addr-disjoint-second-local : caller-addr ≢ (new-rsp +ℕ slot-size)
        addr-disjoint-second-local = addr≢write (new-rsp +ℕ slot-size) second-local-slot-lt-orig

        -- Chain memory preservation through all states
        mem-s1-above : readMem (memory s1) caller-addr ≡ readMem (memory s) caller-addr
        mem-s1-above = refl

        mem-s2-above : readMem (memory s2) caller-addr ≡ readMem (memory s) caller-addr
        mem-s2-above = mem-read-other {memory s1} {rsp-after-push-r15} {caller-addr} {old-r15} (λ eq → addr-disjoint-r15-slot (sym eq))

        mem-s3-above : readMem (memory s3) caller-addr ≡ readMem (memory s) caller-addr
        mem-s3-above = trans (mem-read-other {memory s2} {rsp-after-push-rbp} {caller-addr} {old-rbp} (λ eq → addr-disjoint-rbp-slot (sym eq)))
                             mem-s2-above

        mem-s5-above : readMem (memory s5) caller-addr ≡ readMem (memory s) caller-addr
        mem-s5-above = mem-s3-above

        mem-s6-above : readMem (memory s6) caller-addr ≡ readMem (memory s) caller-addr
        mem-s6-above = trans (mem-read-other {memory s5} {new-rsp} {caller-addr} {readReg (regs s5) r12} (λ eq → addr-disjoint-first-local (sym eq)))
                             mem-s5-above

        mem-s7-above : readMem (memory s7) caller-addr ≡ readMem (memory s) caller-addr
        mem-s7-above = trans (mem-read-other {memory s6} {new-rsp +ℕ slot-size} {caller-addr} {readReg (regs s6) rdi} (λ eq → addr-disjoint-second-local (sym eq)))
                             mem-s6-above

------------------------------------------------------------------------
-- ThunkRetResult: Record for thunk-ret-star return value
-- Using a record avoids deep proj chains and helps termination checking
------------------------------------------------------------------------

record ThunkRetResult (prog : Program) (s s' : State) (ret-addr : ℕ) : Set where
  field
    ret-star : Star prog s s'
    ret-halted : halted s' ≡ false
    ret-pc : pc s' ≡ ret-addr
    ret-rax : readReg (regs s') rax ≡ readReg (regs s) rax
    ret-r14 : readReg (regs s') r14 ≡ readReg (regs s) r14
    ret-r15 : readReg (regs s') r15 ≡ readReg (regs s) r15
    ret-rbp : readReg (regs s') rbp ≡ readReg (regs s) rbp
    ret-stack-inv : StackInvariant s'
    ret-rsp-bound : readReg (regs s') rsp > pair-alloc
    ret-rsp-plus-8 : readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ 8
    ret-mem-preserved : ∀ addr → readMem (memory s') addr ≡ readMem (memory s) addr

-- Prove ret instruction tracing
-- Takes explicit r15-in-code evidence instead of generic StackInvariant.
-- At ret sites in thunks, r15 is ALWAYS in code region (from Apply setup).
-- Returns a record for clean field access (avoids proj chains)
thunk-ret-star : ∀ {A B C} (f : IR (A * B) C)
                 (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ret-offset = length prefix +ℕ 17 +ℕ compile-length f  -- 6 closure + 8 thunk + len-f + 3 cleanup
  in
  halted s ≡ false →
  pc s ≡ ret-offset →
  readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
  InCode (readReg (regs s) r15) →  -- r15 in code region (from Apply)
  readReg (regs s) rsp > pair-alloc →
  ∃[ s' ] ThunkRetResult prog s s' ret-addr
thunk-ret-star {A} {B} {C} f prefix suffix ret-addr s
               h-false pc-eq mem-ret r15-code rsp-sufficient =
  s1 , record
    { ret-star = star-all
    ; ret-halted = h1
    ; ret-pc = pc1
    ; ret-rax = rax1
    ; ret-r14 = r14-1
    ; ret-r15 = r15-1
    ; ret-rbp = rbp1
    ; ret-stack-inv = stack-inv1
    ; ret-rsp-bound = rsp-sufficient-1
    ; ret-rsp-plus-8 = rsp1
    ; ret-mem-preserved = mem-ret-preserves
    }
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)

    prog = prefix ++ compile-x86 (curry f) ++ suffix
    offset = length prefix
    ret-offset = offset +ℕ 17 +ℕ compile-length f  -- 6 closure + 8 thunk + len-f + 3 cleanup

    -- The ret instruction is at ret-offset in curry
    -- curry layout: [6 closure setup] [8 thunk setup] [compile-x86 f] [3 cleanup] [ret] [label end]
    -- ret is at position 17 + len(f) within curry

    -- Fetch the ret instruction (proven in ThunkStructure)
    -- TS-fetch-ret gives: fetch prog (length prefix +ℕ (17 +ℕ compile-length f)) ≡ just ret
    -- We need: fetch prog ((length prefix +ℕ 17) +ℕ compile-length f) ≡ just ret
    -- These differ by associativity
    fetch-ret : fetch prog ret-offset ≡ just ret
    fetch-ret = subst (λ n → fetch prog n ≡ just ret)
                      (sym (+-assoc offset 17 (compile-length f)))
                      (TS-fetch-ret f prefix suffix)

    -- State after ret: pc = ret-addr, rsp += 8
    old-rsp = readReg (regs s) rsp

    s1 : State
    s1 = record s { regs = writeReg (regs s) rsp (old-rsp +ℕ 8)
                  ; pc = ret-addr }

    step-ret : step prog s ≡ just s1
    step-ret = trans (step-exec prog s ret h-false (subst (λ p → fetch prog p ≡ just ret) (sym pc-eq) fetch-ret))
                     (execRet [] s ret-addr mem-ret)

    star-all : Star prog s s1
    star-all = ⟨ h-false , step-ret ⟩◅ refl*

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ ret-addr
    pc1 = refl

    -- Register preservation (ret only writes rsp)
    rax1 : readReg (regs s1) rax ≡ readReg (regs s) rax
    rax1 = readReg-writeReg-rsp-rax (regs s) (old-rsp +ℕ 8)

    r14-1 : readReg (regs s1) r14 ≡ readReg (regs s) r14
    r14-1 = readReg-writeReg-rsp-r14 (regs s) (old-rsp +ℕ 8)

    r15-1 : readReg (regs s1) r15 ≡ readReg (regs s) r15
    r15-1 = readReg-writeReg-rsp-r15 (regs s) (old-rsp +ℕ 8)

    rbp1 : readReg (regs s1) rbp ≡ readReg (regs s) rbp
    rbp1 = readReg-writeReg-rsp-rbp (regs s) (old-rsp +ℕ 8)

    -- StackInvariant: r15 is in code region (ret doesn't change r15)
    -- FULLY PROVEN: Direct construction using explicit r15-in-code evidence
    stack-inv1 : StackInvariant s1
    stack-inv1 = r15-in-code (subst InCode (sym r15-1) r15-code)

    -- D041: RSP after ret = original RSP + 8 (ret pops return address)
    rsp1 : readReg (regs s1) rsp ≡ readReg (regs s) rsp +ℕ 8
    rsp1 = readReg-writeReg-same (regs s) rsp (old-rsp +ℕ 8)

    -- Derive rsp-sufficient-1 from input rsp-sufficient (no postulate needed!)
    -- Input: rsp-sufficient : old-rsp > pair-alloc = 16
    -- After ret: rsp' = old-rsp + 8
    -- Proof: pair-alloc < old-rsp ≤ old-rsp + 8 = rsp'
    rsp-sufficient-1 : readReg (regs s1) rsp > pair-alloc
    rsp-sufficient-1 = subst (_> pair-alloc) (sym rsp1) (<-≤-trans rsp-sufficient (m≤m+n old-rsp 8))
      where
        open import Data.Nat.Properties using (<-≤-trans)

    -- D041: Memory preservation (ret doesn't write memory, record update preserves it)
    mem-ret-preserves : ∀ addr → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-ret-preserves addr = refl
