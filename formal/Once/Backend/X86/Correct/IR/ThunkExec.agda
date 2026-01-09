------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.ThunkExec
--
-- Thunk setup and ret execution proofs for curry.
-- Extracted from MutualIR.agda to reduce type-checking time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.ThunkExec where

open import Once.Backend.X86.Correct.Foundation hiding (n≢n+8; n+8≢n)
open import Once.Postulates using (encode; encode-pair-construct)
open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_)

open import Once.Backend.X86.Correct.IR.ThunkStructure
  using (fetch-thunk-i0; fetch-thunk-i1; fetch-thunk-i2; fetch-thunk-i3; fetch-thunk-i4;
         fetch-thunk-i5; fetch-thunk-i6; fetch-thunk-i7;
         thunk-entry-offset; thunk-body-offset; thunk-setup-len)
  renaming (fetch-ret to TS-fetch-ret)

open import Data.Nat using (_>_; _≤?_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; m∸n≤m; ≤-trans; ∸-monoˡ-≤; ∸-monoʳ-<;
                                       m∸n+n≡m; m≤n⇒m∸n≡0; +-monoˡ-<; +-monoʳ-<; m<m+n; <-trans;
                                       ∸-+-assoc)
                                renaming (<⇒≢ to <⇒≢-neq; ≰⇒> to ≰⇒>-nat; <⇒≤ to <⇒≤-nat; ≤-pred to ≤-pred-nat)
open import Relation.Binary.PropositionalEquality using (_≢_; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

-- Import region lemmas for D041 approach
open import Once.Backend.Common.MemoryRegions
  using (region-of; code; stack; stack-code-disjoint; zero-not-in-stack)
open import Once.Backend.X86.Correct.StackInvariant2
  using (StackCapacity; capacity-maintained; rsp-bound-to-capacity)

-- Prove thunk setup: label, push r15, push rbp, mov rbp rsp, sub rsp 16, mov [rsp] r12, mov [rsp+8] rdi, mov rdi rsp
thunk-setup-star : ∀ {A B C} (f : IR (A * B) C)
                   (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ thunk-entry-offset
      f-offset = length prefix +ℕ thunk-body-offset  -- 6 closure-setup + 8 thunk-setup
  in
  halted s ≡ false →
  pc s ≡ thunk-offset →
  readReg (regs s) rdi ≡ encode arg →
  readReg (regs s) r12 ≡ encode env →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ f-offset
          × readReg (regs s') rdi ≡ encode (env , arg)
          × readReg (regs s') r14 ≡ readReg (regs s) r14
          × readReg (regs s') r15 ≡ readReg (regs s) r15
          × readReg (regs s') rbp ≡ readReg (regs s) rsp ∸ 16  -- rbp is frame pointer (after push r15 and push rbp)
          × StackInvariant s'
          × readReg (regs s') rsp > 16
          × RbpInvariant s'
          -- Key property for pop-rbp-mem: memory at new rbp contains original rbp
          × readMem (memory s') (readReg (regs s') rbp) ≡ just (readReg (regs s) rbp)
          -- Memory at original rsp is preserved (for return address)
          × readMem (memory s') (readReg (regs s) rsp) ≡ readMem (memory s) (readReg (regs s) rsp)
          -- Memory for r15 restoration: saved at original_rsp - 8
          × readMem (memory s') (readReg (regs s) rsp ∸ 8) ≡ just (readReg (regs s) r15)
          -- D041: Memory at address 0 preserved (setup writes only to stack region)
          × readMem (memory s') 0 ≡ readMem (memory s) 0
          -- D041: Memory at code-region addresses preserved
          × (∀ addr → region-of addr ≡ code → readMem (memory s') addr ≡ readMem (memory s) addr))
thunk-setup-star {A} {B} {C} f prefix suffix env arg s
                 h-false pc-eq rdi-eq r12-eq stack-inv rsp>16 =
  s8 , star-all , h8 , pc8 , rdi8 , r14-8 , r15-8 , rbp8 , stack-inv8 , rsp>16-8 , rbp-inv8 , mem-at-rbp8 , mem-old-rsp-preserved , mem-r15-preserved , mem-at-0-preserved , mem-code-preserved
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (m∸n≤m; ≤-trans)
    open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+8)

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
    i4 = sub (reg rsp) (imm 16)            -- allocate pair
    i5 = mov (mem (base rsp)) (reg r12)    -- store env
    i6 = mov (mem (base+disp rsp 8)) (reg rdi)  -- store arg
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
      sub (reg rsp) (imm 16) ∷
      mov (mem (base rsp)) (reg rdi) ∷
      lea r9 (rip+disp 4) ∷
      mov (mem (base+disp rsp 8)) (reg r9) ∷
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
    rsp-after-push-r15 = old-rsp ∸ 8   -- after push r15
    rsp-after-push-rbp = rsp-after-push-r15 ∸ 8  -- after push rbp = old-rsp - 16
    new-rsp = rsp-after-push-rbp ∸ 16  -- after sub rsp, 16 = old-rsp - 32

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
                  (execSub-reg-imm [] s4 rsp 16)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ thunk-offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc thunk-offset 4 1)

    -- State after mov [rsp], r12 (store env)
    rsp-s5 : readReg (regs s5) rsp ≡ new-rsp
    rsp-s5 = readReg-writeReg-same (regs s4) rsp new-rsp

    r12-s5 : readReg (regs s5) r12 ≡ encode env
    r12-s5 = trans (readReg-writeReg-rsp-r12 (regs s4) new-rsp)
                   (trans (readReg-writeReg-rbp-r12 (regs s3) rsp-after-push-rbp)
                          (trans (readReg-writeReg-rsp-r12 (regs s2) rsp-after-push-rbp)
                                 (trans (readReg-writeReg-rsp-r12 (regs s1) rsp-after-push-r15)
                                        r12-eq)))

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

    rdi-s6 : readReg (regs s6) rdi ≡ encode arg
    rdi-s6 = trans (readReg-writeReg-rsp-rdi (regs s4) new-rsp)
                   (trans (readReg-writeReg-rbp-rdi (regs s3) rsp-after-push-rbp)
                          (trans (readReg-writeReg-rsp-rdi (regs s2) rsp-after-push-rbp)
                                 (trans (readReg-writeReg-rsp-rdi (regs s1) rsp-after-push-r15)
                                        rdi-eq)))

    s7 : State
    s7 = record s6 { memory = writeMem (memory s6) (new-rsp +ℕ 8) (readReg (regs s6) rdi)
                   ; pc = pc s6 +ℕ 1 }

    step6 : step prog s6 ≡ just s7
    step6 = trans (step-exec prog s6 i6 h6 (subst (λ p → fetch prog p ≡ just i6) (sym pc6) fetch6))
                  (cong (λ addr → just (record s6 { memory = writeMem (memory s6) (addr +ℕ 8) (readReg (regs s6) rdi)
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

    -- Memory at new-rsp has encode env
    -- s8 doesn't write memory (only rdi register), so memory s8 = memory s7
    mem-env : readMem (memory s8) new-rsp ≡ just (encode env)
    mem-env = trans (mem-read-other {memory s6} {new-rsp +ℕ 8} {new-rsp} {readReg (regs s6) rdi}
                      (λ eq → n≢n+8 new-rsp (sym eq)))
                    (trans (mem-read-write {memory s5} {new-rsp} {readReg (regs s5) r12})
                           (cong just r12-s5))

    -- Memory at new-rsp+8 has encode arg
    mem-arg : readMem (memory s8) (new-rsp +ℕ 8) ≡ just (encode arg)
    mem-arg = trans (mem-read-write {memory s6} {new-rsp +ℕ 8} {readReg (regs s6) rdi})
                    (cong just rdi-s6)

    -- Use encode-pair-construct to show new-rsp = encode (env, arg)
    pair-encoding : new-rsp ≡ encode (env , arg)
    pair-encoding = encode-pair-construct env arg new-rsp (memory s8) mem-env mem-arg

    rdi8 : readReg (regs s8) rdi ≡ encode (env , arg)
    rdi8 = trans rdi-s8-is-new-rsp pair-encoding

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

    -- Prove that (old-rsp ∸ 8) ∸ 8 ≡ old-rsp ∸ 16
    -- Using ∸-+-assoc : ∀ m n o → (m ∸ n) ∸ o ≡ m ∸ (n + o)
    open import Data.Nat.Properties using (∸-+-assoc)
    rsp-after-push-rbp≡old-rsp∸16 : rsp-after-push-rbp ≡ old-rsp ∸ 16
    rsp-after-push-rbp≡old-rsp∸16 = ∸-+-assoc old-rsp 8 8

    -- Convert to expected type
    rbp8 : readReg (regs s8) rbp ≡ old-rsp ∸ 16
    rbp8 = trans rbp8' rsp-after-push-rbp≡old-rsp∸16

    -- StackInvariant proof: rsp decreased, r15 unchanged
    -- s8.rsp = new-rsp = old-rsp - 16 - 16 = old-rsp - 32 ≤ old-rsp = s.rsp
    rsp-s8 : readReg (regs s8) rsp ≡ new-rsp
    rsp-s8 = trans (readReg-writeReg-rdi-rsp (regs s7) new-rsp) rsp-s7

    -- new-rsp = ((old-rsp - 8) - 8) - 16 = old-rsp - 32 ≤ old-rsp
    rsp-decreased : new-rsp ≤ old-rsp
    rsp-decreased = ≤-trans (≤-trans (m∸n≤m rsp-after-push-rbp 16) (m∸n≤m rsp-after-push-r15 8)) (m∸n≤m old-rsp 8)

    rsp-s8≤s : readReg (regs s8) rsp ≤ readReg (regs s) rsp
    rsp-s8≤s = subst (_≤ old-rsp) (sym rsp-s8) rsp-decreased

    stack-inv8 : StackInvariant s8
    stack-inv8 = stack-inv-preserved-rsp-decreased s s8 stack-inv r15-8 rsp-s8≤s

    rsp>16-8 : readReg (regs s8) rsp > 16
    rsp>16-8 = ≤-trans 17≤41 (rsp-bound-after-stack-op s8)
      where
        open import Data.Nat.Properties using (≤-trans)
        17≤41 : 17 ≤ 41
        17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

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
    -- Key insight: rsp-after-push-rbp = old-rsp - 16 ≥ 1 (since old-rsp > 16)
    -- Case 1: If rsp-after-push-rbp ≥ 16, then new-rsp = rsp-after-push-rbp - 16 < rsp-after-push-rbp
    -- Case 2: If rsp-after-push-rbp < 16, then new-rsp = 0, but rsp-after-push-rbp ≥ 1 > 0
    open import Data.Nat using (_≤?_; z<s)
    open import Relation.Nullary using (yes; no)

    -- First, show rsp-after-push-rbp ≥ 1 (stronger than just > 0)
    -- rsp>16 : old-rsp > 16, i.e., old-rsp ≥ 17
    -- rsp-after-push-rbp = old-rsp - 16 ≥ 17 - 16 = 1
    open import Data.Nat.Properties using (∸-monoˡ-≤)
    open import Data.Empty using (⊥-elim)

    -- old-rsp ≥ 17 (from rsp>16)
    17≤old-rsp : 17 ≤ old-rsp
    17≤old-rsp = rsp>16

    -- rsp-after-push-r15 = old-rsp ∸ 8 ≥ 17 - 8 = 9
    9≤rsp-after-push-r15 : 9 ≤ rsp-after-push-r15
    9≤rsp-after-push-r15 = ∸-monoˡ-≤ {17} {old-rsp} 8 17≤old-rsp

    -- rsp-after-push-rbp = rsp-after-push-r15 ∸ 8 ≥ 9 - 8 = 1
    1≤rsp-after-push-rbp : 1 ≤ rsp-after-push-rbp
    1≤rsp-after-push-rbp = ∸-monoˡ-≤ {9} {rsp-after-push-r15} 8 9≤rsp-after-push-r15

    rsp-after-push-rbp>0 : rsp-after-push-rbp > 0
    rsp-after-push-rbp>0 = 1≤rsp-after-push-rbp

    -- m ∸ n ≢ m when m > 0 and n > 0
    -- Case 1: n ≤ m → m ∸ n < m (subtracting positive makes smaller)
    -- Case 2: n > m → m ∸ n = 0 ≢ m (underflow)
    open import Data.Nat.Properties using (∸-monoʳ-<; m≤n⇒m∸n≡0; +-monoʳ-<; <-trans) renaming (<⇒≢ to <⇒≢-neq; ≰⇒> to ≰⇒>-nat; <⇒≤ to <⇒≤-nat)

    ∸-neq : ∀ m n → m > 0 → n > 0 → m ∸ n ≢ m
    ∸-neq zero _ () _
    ∸-neq (suc m) zero _ ()
    ∸-neq (suc m) (suc n) _ _ eq with suc n ≤? suc m
    ... | yes n≤m = <⇒≢-neq (∸-monoʳ-< z<s n≤m) eq
    ... | no ¬n≤m = 0≢suc m∸n≡0-then-eq
      where
        open import Data.Nat.Properties using (≤-pred)
        -- ¬(suc n ≤ suc m) → suc m < suc n = suc (suc m) ≤ suc n
        -- ≤-pred gives suc m ≤ n, which is m < n
        -- <⇒≤ gives m ≤ n
        suc-suc-m≤suc-n : suc (suc m) ≤ suc n
        suc-suc-m≤suc-n = ≰⇒>-nat ¬n≤m
        suc-m≤n : suc m ≤ n  -- same as m < n
        suc-m≤n = ≤-pred suc-suc-m≤suc-n
        m≤n : m ≤ n
        m≤n = <⇒≤-nat suc-m≤n
        m∸n≡0 : m ∸ n ≡ 0
        m∸n≡0 = m≤n⇒m∸n≡0 m≤n
        m∸n≡0-then-eq : 0 ≡ suc m
        m∸n≡0-then-eq = trans (sym m∸n≡0) eq
        0≢suc : ∀ {k} → 0 ≢ suc k
        0≢suc ()

    new-rsp≢rsp-after-push-rbp : new-rsp ≢ rsp-after-push-rbp
    new-rsp≢rsp-after-push-rbp = ∸-neq rsp-after-push-rbp 16 rsp-after-push-rbp>0 0<16
      where
        0<16 : 0 < 16
        0<16 = s≤s z≤n

    -- For new-rsp + 8 ≢ rsp-after-push-rbp:
    -- new-rsp + 8 = (rsp-after-push-rbp - 16) + 8
    -- We use rsp-bound-after-stack-op which gives old-rsp > 40, so old-rsp ≥ 41
    -- Therefore rsp-after-push-rbp = old-rsp - 16 ≥ 25, which is always ≥ 16
    -- So new-rsp + 8 = rsp-after-push-rbp - 8 < rsp-after-push-rbp

    -- First, derive the strong bound from rsp-bound-after-stack-op
    old-rsp>40 : old-rsp > 40
    old-rsp>40 = rsp-bound-after-stack-op s

    -- old-rsp ≥ 41, so rsp-after-push-r15 = old-rsp - 8 ≥ 33
    33≤rsp-after-push-r15 : 33 ≤ rsp-after-push-r15
    33≤rsp-after-push-r15 = ∸-monoˡ-≤ {41} {old-rsp} 8 old-rsp>40

    -- rsp-after-push-rbp = rsp-after-push-r15 - 8 ≥ 33 - 8 = 25
    25≤rsp-after-push-rbp : 25 ≤ rsp-after-push-rbp
    25≤rsp-after-push-rbp = ∸-monoˡ-≤ {33} {rsp-after-push-r15} 8 33≤rsp-after-push-r15

    16≤rsp-after-push-rbp : 16 ≤ rsp-after-push-rbp
    16≤rsp-after-push-rbp = ≤-trans 16≤25 25≤rsp-after-push-rbp
      where
        16≤25 : 16 ≤ 25
        16≤25 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))

    new-rsp+8≢rsp-after-push-rbp : new-rsp +ℕ 8 ≢ rsp-after-push-rbp
    new-rsp+8≢rsp-after-push-rbp eq = <⇒≢-neq new-rsp+8<rsp-after-push-rbp eq
      where
        open import Data.Nat.Properties using (m∸n+n≡m)
        -- new-rsp + 8 = (rsp-after-push-rbp - 16) + 8
        -- rsp-after-push-rbp - 16 + 16 = rsp-after-push-rbp (since 16 ≤ rsp-after-push-rbp)
        -- So (rsp-after-push-rbp - 16) + 8 < (rsp-after-push-rbp - 16) + 16 = rsp-after-push-rbp
        8<16 : 8 < 16
        8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        new-rsp+8<new-rsp+16 : new-rsp +ℕ 8 < new-rsp +ℕ 16
        new-rsp+8<new-rsp+16 = +-monoʳ-< new-rsp 8<16
        new-rsp+8<rsp-after-push-rbp : new-rsp +ℕ 8 < rsp-after-push-rbp
        new-rsp+8<rsp-after-push-rbp = subst (new-rsp +ℕ 8 <_) (m∸n+n≡m 16≤rsp-after-push-rbp) new-rsp+8<new-rsp+16

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
      (mem-read-other {memory s6} {new-rsp +ℕ 8} {rsp-after-push-rbp} {readReg (regs s6) rdi}
                      (λ eq → new-rsp+8≢rsp-after-push-rbp eq))
      mem-s6-at-rsp-after-push-rbp

    -- s8 doesn't write to memory (mov rdi rsp only writes register)
    mem-s8-at-rsp-after-push-rbp : readMem (memory s8) rsp-after-push-rbp ≡ just old-rbp
    mem-s8-at-rsp-after-push-rbp = mem-s7-at-rsp-after-push-rbp

    -- RbpInvariant: new-rsp ≤ rsp-after-push-rbp
    -- new-rsp = rsp-after-push-rbp - 16, so this follows from m∸n≤m
    rbp-inv8 : RbpInvariant s8
    rbp-inv8 = record { rsp≤rbp = new-rsp≤rsp-after-push-rbp }
      where
        new-rsp≤rsp-after-push-rbp-raw : new-rsp ≤ rsp-after-push-rbp
        new-rsp≤rsp-after-push-rbp-raw = m∸n≤m rsp-after-push-rbp 16
        -- Convert to use old-rsp ∸ 16
        new-rsp≤old-rsp∸16 : new-rsp ≤ old-rsp ∸ 16
        new-rsp≤old-rsp∸16 = subst (new-rsp ≤_) rsp-after-push-rbp≡old-rsp∸16 new-rsp≤rsp-after-push-rbp-raw
        new-rsp≤rsp-after-push-rbp : readReg (regs s8) rsp ≤ readReg (regs s8) rbp
        new-rsp≤rsp-after-push-rbp = subst₂ _≤_ (sym rsp-s8) (sym rbp8) new-rsp≤old-rsp∸16

    -- Finally, using rbp8: rbp s8 = old-rsp ∸ 16
    -- First convert mem-s8-at-rsp-after-push-rbp to use old-rsp ∸ 16
    mem-s8-at-old-rsp∸16 : readMem (memory s8) (old-rsp ∸ 16) ≡ just old-rbp
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
    rsp-after-push-r15≢old-rsp = ∸-neq old-rsp 8 (≤-trans 1≤17 rsp>16) 0<8
      where
        1≤17 : 1 ≤ 17
        1≤17 = s≤s z≤n
        0<8 : 0 < 8
        0<8 = s≤s z≤n

    -- rsp-after-push-rbp = (old-rsp - 8) - 8 < old-rsp - 8 < old-rsp
    rsp-after-push-rbp≢old-rsp : rsp-after-push-rbp ≢ old-rsp
    rsp-after-push-rbp≢old-rsp eq = <⇒≢-neq rsp-after-push-rbp<old-rsp eq
      where
        open import Data.Nat.Properties using (∸-monoʳ-<)
        -- rsp-after-push-rbp < rsp-after-push-r15 (since 8 > 0 and 8 ≤ rsp-after-push-r15)
        -- ∸-monoʳ-< : o < n → n ≤ m → m ∸ n < m ∸ o
        -- With o = 0, n = 8, m = rsp-after-push-r15
        -- Gives: rsp-after-push-r15 ∸ 8 < rsp-after-push-r15 ∸ 0 = rsp-after-push-r15
        8≤rsp-after-push-r15 : 8 ≤ rsp-after-push-r15
        8≤rsp-after-push-r15 = ≤-trans 8≤9 9≤rsp-after-push-r15
          where
            8≤9 : 8 ≤ 9
            8≤9 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
        rsp-after-push-rbp<rsp-after-push-r15 : rsp-after-push-rbp < rsp-after-push-r15
        rsp-after-push-rbp<rsp-after-push-r15 = ∸-monoʳ-< (s≤s z≤n) 8≤rsp-after-push-r15
        -- rsp-after-push-r15 < old-rsp (since 8 > 0 and 8 ≤ old-rsp)
        8≤old-rsp : 8 ≤ old-rsp
        8≤old-rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) rsp>16
        rsp-after-push-r15<old-rsp : rsp-after-push-r15 < old-rsp
        rsp-after-push-r15<old-rsp = ∸-monoʳ-< (s≤s z≤n) 8≤old-rsp
        rsp-after-push-rbp<old-rsp : rsp-after-push-rbp < old-rsp
        rsp-after-push-rbp<old-rsp = <-trans rsp-after-push-rbp<rsp-after-push-r15 rsp-after-push-r15<old-rsp

    -- new-rsp ≤ rsp-after-push-rbp < old-rsp (when old-rsp > 16)
    new-rsp≢old-rsp : new-rsp ≢ old-rsp
    new-rsp≢old-rsp eq with 16 ≤? rsp-after-push-rbp
    ... | yes 16≤ = <⇒≢-neq new-rsp<old-rsp eq
      where
        open import Data.Nat.Properties using (∸-monoʳ-<)
        -- new-rsp = rsp-after-push-rbp - 16 < rsp-after-push-rbp (since 16 > 0 and 16 ≤ rsp-after-push-rbp)
        new-rsp<rsp-after-push-rbp : new-rsp < rsp-after-push-rbp
        new-rsp<rsp-after-push-rbp = ∸-monoʳ-< z<s 16≤
        -- rsp-after-push-rbp = rsp-after-push-r15 - 8 < rsp-after-push-r15 < old-rsp
        8≤rsp-after-push-r15' : 8 ≤ rsp-after-push-r15
        8≤rsp-after-push-r15' = ≤-trans 8≤9' 9≤rsp-after-push-r15
          where
            8≤9' : 8 ≤ 9
            8≤9' = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
        rsp-after-push-rbp<rsp-after-push-r15' : rsp-after-push-rbp < rsp-after-push-r15
        rsp-after-push-rbp<rsp-after-push-r15' = ∸-monoʳ-< (s≤s z≤n) 8≤rsp-after-push-r15'
        8≤old-rsp' : 8 ≤ old-rsp
        8≤old-rsp' = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) rsp>16
        rsp-after-push-r15<old-rsp' : rsp-after-push-r15 < old-rsp
        rsp-after-push-r15<old-rsp' = ∸-monoʳ-< (s≤s z≤n) 8≤old-rsp'
        rsp-after-push-rbp<old-rsp : rsp-after-push-rbp < old-rsp
        rsp-after-push-rbp<old-rsp = <-trans rsp-after-push-rbp<rsp-after-push-r15' rsp-after-push-r15<old-rsp'
        new-rsp<old-rsp : new-rsp < old-rsp
        new-rsp<old-rsp = <-trans new-rsp<rsp-after-push-rbp rsp-after-push-rbp<old-rsp
    ... | no ¬16≤ = 0≢old-rsp (trans (sym new-rsp≡0) eq)
      where
        -- rsp-after-push-rbp < 16 → new-rsp = 0
        rsp<16 : rsp-after-push-rbp < 16
        rsp<16 = ≰⇒>-nat ¬16≤
        new-rsp≡0 : new-rsp ≡ 0
        new-rsp≡0 = m≤n⇒m∸n≡0 (<⇒≤-nat rsp<16)
        -- old-rsp > 16 > 0, so 0 ≠ old-rsp
        old-rsp>0 : old-rsp > 0
        old-rsp>0 = ≤-trans (s≤s z≤n) rsp>16
        0≢old-rsp : 0 ≢ old-rsp
        0≢old-rsp zeq = <⇒≢-neq old-rsp>0 zeq

    -- new-rsp + 8 = (rsp-after-push-rbp - 16) + 8 < old-rsp
    new-rsp+8≢old-rsp : new-rsp +ℕ 8 ≢ old-rsp
    new-rsp+8≢old-rsp eq with 16 ≤? rsp-after-push-rbp
    ... | yes 16≤ = <⇒≢-neq new-rsp+8<old-rsp eq
      where
        -- new-rsp + 8 = rsp-after-push-rbp - 16 + 8 = rsp-after-push-rbp - 8 < rsp-after-push-rbp < old-rsp
        open import Data.Nat.Properties using (m∸n+n≡m)
        8<16 : 8 < 16
        8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        new-rsp+8<rsp-after-push-rbp+16 : new-rsp +ℕ 8 < new-rsp +ℕ 16
        new-rsp+8<rsp-after-push-rbp+16 = +-monoʳ-< new-rsp 8<16
        new-rsp+8<rsp-after-push-rbp : new-rsp +ℕ 8 < rsp-after-push-rbp
        new-rsp+8<rsp-after-push-rbp = subst (new-rsp +ℕ 8 <_) (m∸n+n≡m 16≤) new-rsp+8<rsp-after-push-rbp+16
        -- rsp-after-push-rbp = rsp-after-push-r15 - 8 < rsp-after-push-r15 < old-rsp
        open import Data.Nat.Properties using (∸-monoʳ-<)
        8≤rsp-after-push-r15'' : 8 ≤ rsp-after-push-r15
        8≤rsp-after-push-r15'' = ≤-trans 8≤9'' 9≤rsp-after-push-r15
          where
            8≤9'' : 8 ≤ 9
            8≤9'' = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
        rsp-after-push-rbp<rsp-after-push-r15'' : rsp-after-push-rbp < rsp-after-push-r15
        rsp-after-push-rbp<rsp-after-push-r15'' = ∸-monoʳ-< (s≤s z≤n) 8≤rsp-after-push-r15''
        8≤old-rsp'' : 8 ≤ old-rsp
        8≤old-rsp'' = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) rsp>16
        rsp-after-push-r15<old-rsp'' : rsp-after-push-r15 < old-rsp
        rsp-after-push-r15<old-rsp'' = ∸-monoʳ-< (s≤s z≤n) 8≤old-rsp''
        rsp-after-push-rbp<old-rsp : rsp-after-push-rbp < old-rsp
        rsp-after-push-rbp<old-rsp = <-trans rsp-after-push-rbp<rsp-after-push-r15'' rsp-after-push-r15<old-rsp''
        new-rsp+8<old-rsp : new-rsp +ℕ 8 < old-rsp
        new-rsp+8<old-rsp = <-trans new-rsp+8<rsp-after-push-rbp rsp-after-push-rbp<old-rsp
    ... | no ¬16≤ = <⇒≢-neq new-rsp+8<old-rsp eq
      where
        -- new-rsp = 0, so new-rsp + 8 = 8 < old-rsp (since old-rsp > 16)
        rsp<16 : rsp-after-push-rbp < 16
        rsp<16 = ≰⇒>-nat ¬16≤
        new-rsp≡0 : new-rsp ≡ 0
        new-rsp≡0 = m≤n⇒m∸n≡0 (<⇒≤-nat rsp<16)
        8<17 : 8 < 17
        8<17 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        8<old-rsp : 8 < old-rsp
        8<old-rsp = ≤-trans 8<17 rsp>16
        new-rsp+8<old-rsp : new-rsp +ℕ 8 < old-rsp
        new-rsp+8<old-rsp = subst (λ n → n +ℕ 8 < old-rsp) (sym new-rsp≡0) 8<old-rsp

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
    mem-s7-old-rsp = trans (mem-read-other {memory s6} {new-rsp +ℕ 8} {old-rsp} {readReg (regs s6) rdi}
                             (λ eq → new-rsp+8≢old-rsp eq))
                           mem-s6-old-rsp

    -- s8 doesn't write memory (mov rdi rsp only writes register)
    mem-old-rsp-preserved : readMem (memory s8) old-rsp ≡ readMem (memory s) old-rsp
    mem-old-rsp-preserved = mem-s7-old-rsp

    -- Memory for r15 restoration: s2 wrote old-r15 at rsp-after-push-r15 = old-rsp - 8
    -- This value is preserved through all subsequent writes
    -- rsp-after-push-r15 = old-rsp - 8, rsp-after-push-rbp = rsp-after-push-r15 - 8
    -- ∸-neq gives us: rsp-after-push-r15 ∸ 8 ≢ rsp-after-push-r15
    -- We need to swap to get: rsp-after-push-r15 ≢ rsp-after-push-r15 ∸ 8 = rsp-after-push-rbp
    rsp-after-push-r15≢rsp-after-push-rbp : rsp-after-push-r15 ≢ rsp-after-push-rbp
    rsp-after-push-r15≢rsp-after-push-rbp = ≢-sym (∸-neq rsp-after-push-r15 8 rsp-after-push-r15>0 0<8)
      where
        open import Relation.Binary.PropositionalEquality using (≢-sym)
        rsp-after-push-r15>0 : rsp-after-push-r15 > 0
        rsp-after-push-r15>0 = ≤-trans (s≤s z≤n) 9≤rsp-after-push-r15
        0<8 : 0 < 8
        0<8 = s≤s z≤n

    new-rsp≢rsp-after-push-r15 : new-rsp ≢ rsp-after-push-r15
    new-rsp≢rsp-after-push-r15 eq = <⇒≢-neq new-rsp<rsp-after-push-r15 eq
      where
        -- new-rsp = old-rsp - 32, rsp-after-push-r15 = old-rsp - 8
        -- new-rsp < rsp-after-push-r15 (since 32 > 8)
        new-rsp≤rsp-after-push-rbp : new-rsp ≤ rsp-after-push-rbp
        new-rsp≤rsp-after-push-rbp = m∸n≤m rsp-after-push-rbp 16
        rsp-after-push-rbp≤rsp-after-push-r15 : rsp-after-push-rbp ≤ rsp-after-push-r15
        rsp-after-push-rbp≤rsp-after-push-r15 = m∸n≤m rsp-after-push-r15 8
        new-rsp≤rsp-after-push-r15 : new-rsp ≤ rsp-after-push-r15
        new-rsp≤rsp-after-push-r15 = ≤-trans new-rsp≤rsp-after-push-rbp rsp-after-push-rbp≤rsp-after-push-r15
        -- new-rsp = rsp-after-push-rbp - 16 ≤ rsp-after-push-rbp < rsp-after-push-r15
        -- Chain: new-rsp ≤ rsp-after-push-rbp < rsp-after-push-r15
        open import Data.Nat.Properties using (∸-monoʳ-<)
        8≤rsp-after-push-r15''' : 8 ≤ rsp-after-push-r15
        8≤rsp-after-push-r15''' = ≤-trans 8≤9''' 9≤rsp-after-push-r15
          where
            8≤9''' : 8 ≤ 9
            8≤9''' = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
        rsp-after-push-rbp<rsp-after-push-r15''' : rsp-after-push-rbp < rsp-after-push-r15
        rsp-after-push-rbp<rsp-after-push-r15''' = ∸-monoʳ-< (s≤s z≤n) 8≤rsp-after-push-r15'''
        new-rsp<rsp-after-push-r15 : new-rsp < rsp-after-push-r15
        new-rsp<rsp-after-push-r15 = ≤-trans (s≤s new-rsp≤rsp-after-push-rbp) rsp-after-push-rbp<rsp-after-push-r15'''

    new-rsp+8≢rsp-after-push-r15 : new-rsp +ℕ 8 ≢ rsp-after-push-r15
    new-rsp+8≢rsp-after-push-r15 eq = <⇒≢-neq new-rsp+8<rsp-after-push-r15 eq
      where
        -- new-rsp + 8 = old-rsp - 24, rsp-after-push-r15 = old-rsp - 8
        -- For new-rsp + 8 < rsp-after-push-r15: old-rsp - 24 < old-rsp - 8 when old-rsp ≥ 24
        new-rsp+8<rsp-after-push-r15 : new-rsp +ℕ 8 < rsp-after-push-r15
        new-rsp+8<rsp-after-push-r15 with 24 ≤? old-rsp
        ... | yes 24≤ = subst (new-rsp +ℕ 8 <_) (sym rsp-r15-eq) new-rsp+8<rsp-after-push-r15'
          where
            open import Data.Nat.Properties using (m∸n+n≡m)
            -- First show rsp-after-push-r15 = old-rsp - 8
            -- new-rsp + 8 = (rsp-after-push-rbp - 16) + 8
            -- We need: (old-rsp - 16 - 16) + 8 < old-rsp - 8
            -- Simplify: old-rsp - 32 + 8 < old-rsp - 8
            -- When old-rsp ≥ 32: old-rsp - 24 < old-rsp - 8, which is 16 > 0, true
            -- When old-rsp < 32 but ≥ 24: old-rsp - 24 ≥ 0, old-rsp - 8 ≥ 16, so 0..7 < 16+, true
            16≤rsp-after-push-r15 : 16 ≤ rsp-after-push-r15
            16≤rsp-after-push-r15 = ∸-monoˡ-≤ {24} {old-rsp} 8 24≤
            rsp-r15-eq : old-rsp ∸ 8 ≡ rsp-after-push-r15
            rsp-r15-eq = refl
            8<16' : 8 < 16
            8<16' = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
            -- Show new-rsp + 8 < new-rsp + 16 = rsp-after-push-rbp (when 16 ≤ rsp-after-push-rbp)
            -- Then show rsp-after-push-rbp < rsp-after-push-r15
            -- Use the outer scope's 16≤rsp-after-push-rbp which handles the chained subtraction
            16≤rsp-after-push-rbp''' : 16 ≤ rsp-after-push-rbp
            16≤rsp-after-push-rbp''' = 16≤rsp-after-push-rbp
            new-rsp+16≡rsp-after-push-rbp : new-rsp +ℕ 16 ≡ rsp-after-push-rbp
            new-rsp+16≡rsp-after-push-rbp = m∸n+n≡m 16≤rsp-after-push-rbp'''
            new-rsp+8<new-rsp+16 : new-rsp +ℕ 8 < new-rsp +ℕ 16
            new-rsp+8<new-rsp+16 = +-monoʳ-< new-rsp 8<16'
            new-rsp+8<rsp-after-push-rbp : new-rsp +ℕ 8 < rsp-after-push-rbp
            new-rsp+8<rsp-after-push-rbp = subst (new-rsp +ℕ 8 <_) new-rsp+16≡rsp-after-push-rbp new-rsp+8<new-rsp+16
            -- rsp-after-push-rbp = rsp-after-push-r15 ∸ 8, so need 8 ≤ rsp-after-push-r15
            8≤rsp-after-push-r15'''' : 8 ≤ rsp-after-push-r15
            8≤rsp-after-push-r15'''' = ≤-trans 8≤9'''' 9≤rsp-after-push-r15
              where
                8≤9'''' : 8 ≤ 9
                8≤9'''' = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
            rsp-after-push-rbp+8≡rsp-after-push-r15 : rsp-after-push-rbp +ℕ 8 ≡ rsp-after-push-r15
            rsp-after-push-rbp+8≡rsp-after-push-r15 = m∸n+n≡m 8≤rsp-after-push-r15''''
            0<8' : 0 < 8
            0<8' = s≤s z≤n
            rsp-after-push-rbp<rsp-after-push-r15 : rsp-after-push-rbp < rsp-after-push-r15
            rsp-after-push-rbp<rsp-after-push-r15 = subst (rsp-after-push-rbp <_) rsp-after-push-rbp+8≡rsp-after-push-r15 (m<m+n rsp-after-push-rbp 0<8')
            new-rsp+8<rsp-after-push-r15' : new-rsp +ℕ 8 < old-rsp ∸ 8
            new-rsp+8<rsp-after-push-r15' = <-trans new-rsp+8<rsp-after-push-rbp rsp-after-push-rbp<rsp-after-push-r15
        -- This case is unreachable since old-rsp > 40 implies 24 ≤ old-rsp
        ... | no ¬24≤ = ⊥-elim (¬24≤ 24≤old-rsp)
          where
            open import Data.Empty using (⊥-elim)
            24≤old-rsp : 24 ≤ old-rsp
            24≤old-rsp = ≤-trans 24≤41 old-rsp>40
              where
                24≤41 : 24 ≤ 41
                24≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))))))))

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
      (mem-read-other {memory s6} {new-rsp +ℕ 8} {rsp-after-push-r15} {readReg (regs s6) rdi}
                      (λ eq → new-rsp+8≢rsp-after-push-r15 eq))
      mem-s6-at-rsp-after-push-r15

    -- s8 doesn't write memory
    mem-r15-preserved : readMem (memory s8) (old-rsp ∸ 8) ≡ just old-r15
    mem-r15-preserved = mem-s7-at-rsp-after-push-r15

    ------------------------------------------------------------------------
    -- D041: Memory at address 0 preserved (all writes are to stack region)
    ------------------------------------------------------------------------

    -- Get StackCapacity to prove write addresses are in stack region
    -- We use old-rsp>40 from rsp-bound-after-stack-op which gives capacity 5
    -- Note: rsp-bound-to-capacity expects rsp > n*8, and 5*8 = 40
    cap-stronger : StackCapacity s 5
    cap-stronger = rsp-bound-to-capacity s 5 old-rsp>40

    -- Write addresses are all in stack region
    -- Need to use ∸-+-assoc to relate nested subtractions to flat ones
    -- ∸-+-assoc m n o : (m ∸ n) ∸ o ≡ m ∸ (n + o)

    -- rsp-after-push-r15 = old-rsp ∸ 8 matches old-rsp ∸ 1*8 directly
    addr-rsp-8-in-stack : region-of rsp-after-push-r15 ≡ stack
    addr-rsp-8-in-stack = capacity-maintained cap-stronger 1 (s≤s z≤n)

    -- rsp-after-push-rbp = (old-rsp ∸ 8) ∸ 8 = old-rsp ∸ 16 = old-rsp ∸ 2*8
    rsp-after-push-rbp-eq : rsp-after-push-rbp ≡ old-rsp ∸ 16
    rsp-after-push-rbp-eq = ∸-+-assoc old-rsp 8 8

    addr-rsp-16-in-stack : region-of rsp-after-push-rbp ≡ stack
    addr-rsp-16-in-stack = subst (λ x → region-of x ≡ stack) (sym rsp-after-push-rbp-eq)
                                 (capacity-maintained cap-stronger 2 (s≤s (s≤s z≤n)))

    -- new-rsp = ((old-rsp ∸ 8) ∸ 8) ∸ 16 = (old-rsp ∸ 16) ∸ 16 = old-rsp ∸ 32 = old-rsp ∸ 4*8
    new-rsp-eq : new-rsp ≡ old-rsp ∸ 32
    new-rsp-eq = trans (cong (_∸ 16) rsp-after-push-rbp-eq) (∸-+-assoc old-rsp 16 16)

    addr-rsp-32-in-stack : region-of new-rsp ≡ stack
    addr-rsp-32-in-stack = subst (λ x → region-of x ≡ stack) (sym new-rsp-eq)
                                 (capacity-maintained cap-stronger 4 (s≤s (s≤s (s≤s (s≤s z≤n)))))

    -- new-rsp + 8 = (old-rsp ∸ 32) + 8 = old-rsp ∸ 24 = old-rsp ∸ 3*8
    -- Proof using stdlib: m∸n+n≡m and +-∸-assoc
    -- Strategy: (old-rsp ∸ 32) + 8 = old-rsp ∸ 24
    --   Let k = old-rsp ∸ 32. Then k + 32 = old-rsp (by m∸n+n≡m).
    --   old-rsp ∸ 24 = (k + 32) ∸ 24 = k + (32 ∸ 24) = k + 8 (by +-∸-assoc)
    new-rsp+8-eq : new-rsp +ℕ 8 ≡ old-rsp ∸ 24
    new-rsp+8-eq = trans (cong (_+ℕ 8) new-rsp-eq) k+8≡old-rsp∸24
      where
        open import Data.Nat.Properties using (+-∸-assoc)

        k = old-rsp ∸ 32

        -- old-rsp > 40 implies 32 ≤ old-rsp
        32≤old-rsp : 32 ≤ old-rsp
        32≤old-rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
                     (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
                     (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
                     (s≤s (s≤s z≤n)))))))))))))))))))))))))))))))) old-rsp>40

        -- k + 32 = old-rsp
        k+32≡old-rsp : k +ℕ 32 ≡ old-rsp
        k+32≡old-rsp = m∸n+n≡m 32≤old-rsp

        24≤32 : 24 ≤ 32
        24≤32 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
                (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
                (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))))))))

        -- (k + 32) ∸ 24 = k + (32 ∸ 24) = k + 8
        assoc-step : (k +ℕ 32) ∸ 24 ≡ k +ℕ 8
        assoc-step = +-∸-assoc k 24≤32

        -- old-rsp ∸ 24 = (k + 32) ∸ 24 = k + 8
        k+8≡old-rsp∸24 : k +ℕ 8 ≡ old-rsp ∸ 24
        k+8≡old-rsp∸24 = sym (trans (cong (_∸ 24) (sym k+32≡old-rsp)) assoc-step)

    addr-rsp-24-in-stack : region-of (new-rsp +ℕ 8) ≡ stack
    addr-rsp-24-in-stack = subst (λ x → region-of x ≡ stack) (sym new-rsp+8-eq)
                                 (capacity-maintained cap-stronger 3 (s≤s (s≤s (s≤s z≤n))))

    -- Address 0 is not in stack region, so write addresses ≠ 0
    addr-rsp-8≢0 : rsp-after-push-r15 ≢ 0
    addr-rsp-8≢0 eq = zero-not-in-stack (trans (cong region-of (sym eq)) addr-rsp-8-in-stack)

    addr-rsp-16≢0 : rsp-after-push-rbp ≢ 0
    addr-rsp-16≢0 eq = zero-not-in-stack (trans (cong region-of (sym eq)) addr-rsp-16-in-stack)

    addr-rsp-32≢0 : new-rsp ≢ 0
    addr-rsp-32≢0 eq = zero-not-in-stack (trans (cong region-of (sym eq)) addr-rsp-32-in-stack)

    addr-rsp-24≢0 : new-rsp +ℕ 8 ≢ 0
    addr-rsp-24≢0 eq = zero-not-in-stack (trans (cong region-of (sym eq)) addr-rsp-24-in-stack)

    -- Chain memory preservation at 0 through all states
    -- s1 doesn't write memory
    mem-s1-at-0 : readMem (memory s1) 0 ≡ readMem (memory s) 0
    mem-s1-at-0 = refl

    -- s2 writes at rsp-after-push-r15 ≠ 0
    mem-s2-at-0 : readMem (memory s2) 0 ≡ readMem (memory s) 0
    mem-s2-at-0 = mem-read-other {memory s1} {rsp-after-push-r15} {0} {old-r15} addr-rsp-8≢0

    -- s3 writes at rsp-after-push-rbp ≠ 0
    mem-s3-at-0 : readMem (memory s3) 0 ≡ readMem (memory s) 0
    mem-s3-at-0 = trans (mem-read-other {memory s2} {rsp-after-push-rbp} {0} {old-rbp} addr-rsp-16≢0)
                        mem-s2-at-0

    -- s4, s5 don't write memory
    mem-s5-at-0 : readMem (memory s5) 0 ≡ readMem (memory s) 0
    mem-s5-at-0 = mem-s3-at-0

    -- s6 writes at new-rsp ≠ 0
    mem-s6-at-0 : readMem (memory s6) 0 ≡ readMem (memory s) 0
    mem-s6-at-0 = trans (mem-read-other {memory s5} {new-rsp} {0} {readReg (regs s5) r12} addr-rsp-32≢0)
                        mem-s5-at-0

    -- s7 writes at new-rsp + 8 ≠ 0
    mem-s7-at-0 : readMem (memory s7) 0 ≡ readMem (memory s) 0
    mem-s7-at-0 = trans (mem-read-other {memory s6} {new-rsp +ℕ 8} {0} {readReg (regs s6) rdi} addr-rsp-24≢0)
                        mem-s6-at-0

    -- s8 doesn't write memory
    mem-at-0-preserved : readMem (memory s8) 0 ≡ readMem (memory s) 0
    mem-at-0-preserved = mem-s7-at-0

    ------------------------------------------------------------------------
    -- D041: Memory at code-region addresses preserved
    ------------------------------------------------------------------------

    -- For any code address, it's not equal to any of the write addresses
    -- because stack region is disjoint from code region
    code-addr≢write-addr : ∀ addr → region-of addr ≡ code →
      addr ≢ rsp-after-push-r15 × addr ≢ rsp-after-push-rbp ×
      addr ≢ new-rsp × addr ≢ (new-rsp +ℕ 8)
    code-addr≢write-addr addr addr-code =
      (λ eq → stack-code-disjoint rsp-after-push-r15 addr addr-rsp-8-in-stack addr-code (sym eq)) ,
      (λ eq → stack-code-disjoint rsp-after-push-rbp addr addr-rsp-16-in-stack addr-code (sym eq)) ,
      (λ eq → stack-code-disjoint new-rsp addr addr-rsp-32-in-stack addr-code (sym eq)) ,
      (λ eq → stack-code-disjoint (new-rsp +ℕ 8) addr addr-rsp-24-in-stack addr-code (sym eq))

    -- Chain memory preservation at code addresses through all states
    mem-code-preserved : ∀ addr → region-of addr ≡ code → readMem (memory s8) addr ≡ readMem (memory s) addr
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
        mem-s7-code = trans (mem-read-other {memory s6} {new-rsp +ℕ 8} {addr} {readReg (regs s6) rdi} (λ eq → addr≢rsp-24 (sym eq)))
                            mem-s6-code

-- Prove ret instruction tracing
thunk-ret-star : ∀ {A B C} (f : IR (A * B) C)
                 (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ret-offset = length prefix +ℕ 17 +ℕ compile-length f  -- 6 closure + 8 thunk + len-f + 3 cleanup
  in
  halted s ≡ false →
  pc s ≡ ret-offset →
  readMem (memory s) (readReg (regs s) rsp) ≡ just ret-addr →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ ret-addr
          × readReg (regs s') rax ≡ readReg (regs s) rax
          × readReg (regs s') r14 ≡ readReg (regs s) r14
          × readReg (regs s') r15 ≡ readReg (regs s) r15
          × readReg (regs s') rbp ≡ readReg (regs s) rbp
          × StackInvariant s'
          × readReg (regs s') rsp > 16
          -- D041: Memory preservation (ret doesn't write memory)
          × readReg (regs s') rsp ≡ readReg (regs s) rsp +ℕ 8
          × (∀ addr → readMem (memory s') addr ≡ readMem (memory s) addr))
thunk-ret-star {A} {B} {C} f prefix suffix ret-addr s
               h-false pc-eq mem-ret stack-inv rsp>16 =
  s1 , star-all , h1 , pc1 , rax1 , r14-1 , r15-1 , rbp1 , stack-inv1 , rsp>16-1 , rsp1 , mem-ret-preserves
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

    -- StackInvariant preserved after ret (r15 unchanged)
    stack-inv1 : StackInvariant s1
    stack-inv1 = stack-inv-preserved-ret s s1 stack-inv r15-1

    rsp>16-1 : readReg (regs s1) rsp > 16
    rsp>16-1 = ≤-trans 17≤41 (rsp-bound-after-stack-op s1)
      where
        open import Data.Nat.Properties using (≤-trans)
        17≤41 : 17 ≤ 41
        17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

    -- D041: RSP after ret = original RSP + 8 (ret pops return address)
    rsp1 : readReg (regs s1) rsp ≡ readReg (regs s) rsp +ℕ 8
    rsp1 = readReg-writeReg-same (regs s) rsp (old-rsp +ℕ 8)

    -- D041: Memory preservation (ret doesn't write memory, record update preserves it)
    mem-ret-preserves : ∀ addr → readMem (memory s1) addr ≡ readMem (memory s) addr
    mem-ret-preserves addr = refl
