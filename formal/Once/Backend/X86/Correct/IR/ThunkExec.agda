------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.ThunkExec
--
-- Thunk setup and ret execution proofs for curry.
-- Extracted from MutualIR.agda to reduce type-checking time.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.ThunkExec where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Once.Postulates using (encode; encode-pair-construct)
open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_)

open import Once.Backend.X86.Correct.IR.ThunkStructure
  using (fetch-thunk-i0; fetch-thunk-i1; fetch-thunk-i2; fetch-thunk-i3; fetch-thunk-i4;
         fetch-thunk-i5; fetch-thunk-i6)
  renaming (fetch-ret to TS-fetch-ret)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; s≤s; z≤n; z<s; _≤?_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; m∸n≤m; ≤-trans; ∸-monoˡ-≤; ∸-monoʳ-<;
                                       m∸n+n≡m; m≤n⇒m∸n≡0; +-monoˡ-<; +-monoʳ-<; m<m+n; <-trans)
                                renaming (<⇒≢ to <⇒≢-neq; ≰⇒> to ≰⇒>-nat; <⇒≤ to <⇒≤-nat; ≤-pred to ≤-pred-nat)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

-- Prove thunk setup: label, push rbp, mov rbp rsp, sub rsp 16, mov [rsp] r12, mov [rsp+8] rdi, mov rdi rsp
thunk-setup-star : ∀ {A B C} (f : IR (A * B) C)
                   (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
      f-offset = length prefix +ℕ 13  -- 6 closure-setup + 7 thunk-setup
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
          × readReg (regs s') rbp ≡ readReg (regs s) rsp ∸ 8  -- rbp is now frame pointer
          × StackInvariant s'
          × readReg (regs s') rsp > 16
          × RbpInvariant s'
          -- Key property for pop-rbp-mem: memory at new rbp contains original rbp
          × readMem (memory s') (readReg (regs s') rbp) ≡ just (readReg (regs s) rbp)
          -- Memory at original rsp is preserved (for return address)
          × readMem (memory s') (readReg (regs s) rsp) ≡ readMem (memory s) (readReg (regs s) rsp))
thunk-setup-star {A} {B} {C} f prefix suffix env arg s
                 h-false pc-eq rdi-eq r12-eq stack-inv rsp>16 =
  s7 , star-all , h7 , pc7 , rdi7 , r14-7 , r15-7 , rbp7 , stack-inv7 , rsp>16-7 , rbp-inv7 , mem-at-rbp7 , mem-old-rsp-preserved
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
    open import Data.Nat.Properties using (m∸n≤m; ≤-trans)
    open import Once.Backend.X86.Encoding using (mem-read-write; mem-read-other; n≢n+8)

    prog = prefix ++ compile-x86 (curry f) ++ suffix
    offset = length prefix
    thunk-offset = offset +ℕ 6
    f-offset = offset +ℕ 13  -- 6 closure-setup + 7 thunk-setup

    -- The 7 thunk setup instructions (at positions 6-12 within curry)
    -- These match the compile-x86 curry definition exactly
    i0 = label 6                           -- label at thunk entry (code-ptr-label = 6)
    i1 = push (reg rbp)                    -- save frame pointer
    i2 = mov (reg rbp) (reg rsp)           -- set frame pointer
    i3 = sub (reg rsp) (imm 16)            -- allocate pair
    i4 = mov (mem (base rsp)) (reg r12)    -- store env
    i5 = mov (mem (base+disp rsp 8)) (reg rdi)  -- store arg
    i6 = mov (reg rdi) (reg rsp)           -- rdi = pair address

    -- Program structure for fetch proofs:
    -- prog = prefix ++ compile-x86 (curry f) ++ suffix
    --      = prefix ++ (curry-closure-setup ++ curry-thunk-setup ++ compile-x86 f ++ curry-tail) ++ suffix
    -- where curry-closure-setup has 6 instructions and curry-thunk-setup starts with label 6
    --
    -- For fetch at thunk-offset = offset + 6:
    -- We need to show the program up to thunk-offset has length = offset + 6
    -- Then fetch-at-prefix-end gives us the instruction

    len-f = compile-length f
    end-offset-curry = 10 +ℕ len-f  -- jmp at pos 5 to reach end at 16+len-f

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

    old-rsp = readReg (regs s) rsp
    old-rbp = readReg (regs s) rbp
    rsp-after-push = old-rsp ∸ 8   -- after push rbp
    new-rsp = rsp-after-push ∸ 16  -- after sub rsp, 16

    -- State after label (no-op, just pc++)
    s1 : State
    s1 = record s { pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just s1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execLabel [] s (offset +ℕ 6))

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ thunk-offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- State after push rbp
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) rsp rsp-after-push
                   ; memory = writeMem (memory s1) rsp-after-push old-rbp
                   ; pc = pc s1 +ℕ 1 }

    step1 : step prog s1 ≡ just s2
    step1 = trans (step-exec prog s1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execPush-reg [] s1 rbp)

    h2 : halted s2 ≡ false
    h2 = h-false

    pc2 : pc s2 ≡ thunk-offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc thunk-offset 1 1)

    -- State after mov rbp, rsp (set frame pointer to current rsp)
    rsp-s2 : readReg (regs s2) rsp ≡ rsp-after-push
    rsp-s2 = readReg-writeReg-same (regs s1) rsp rsp-after-push

    s3 : State
    s3 = record s2 { regs = writeReg (regs s2) rbp rsp-after-push
                   ; pc = pc s2 +ℕ 1 }

    step2 : step prog s2 ≡ just s3
    step2 = trans (step-exec prog s2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (cong (λ sp → just (record s2 { regs = writeReg (regs s2) rbp sp
                                                ; pc = pc s2 +ℕ 1 }))
                        rsp-s2)

    h3 : halted s3 ≡ false
    h3 = h-false

    pc3 : pc s3 ≡ thunk-offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc thunk-offset 2 1)

    -- State after sub rsp, 16
    rsp-s3 : readReg (regs s3) rsp ≡ rsp-after-push
    rsp-s3 = trans (readReg-writeReg-rbp-rsp (regs s2) rsp-after-push) rsp-s2

    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) rsp new-rsp
                   ; pc = pc s3 +ℕ 1
                   ; flags = updateFlags new-rsp rsp-after-push }

    step3 : step prog s3 ≡ just s4
    step3 = trans (step-exec prog s3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execSub-reg-imm [] s3 rsp 16)

    h4 : halted s4 ≡ false
    h4 = h-false

    pc4 : pc s4 ≡ thunk-offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc thunk-offset 3 1)

    -- State after mov [rsp], r12 (store env)
    rsp-s4 : readReg (regs s4) rsp ≡ new-rsp
    rsp-s4 = readReg-writeReg-same (regs s3) rsp new-rsp

    r12-s4 : readReg (regs s4) r12 ≡ encode env
    r12-s4 = trans (readReg-writeReg-rsp-r12 (regs s3) new-rsp)
                   (trans (readReg-writeReg-rbp-r12 (regs s2) rsp-after-push)
                          (trans (readReg-writeReg-rsp-r12 (regs s1) rsp-after-push)
                                 r12-eq))

    s5 : State
    s5 = record s4 { memory = writeMem (memory s4) new-rsp (readReg (regs s4) r12)
                   ; pc = pc s4 +ℕ 1 }

    step4 : step prog s4 ≡ just s5
    step4 = trans (step-exec prog s4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (cong (λ addr → just (record s4 { memory = writeMem (memory s4) addr (readReg (regs s4) r12)
                                                  ; pc = pc s4 +ℕ 1 }))
                        rsp-s4)

    h5 : halted s5 ≡ false
    h5 = h-false

    pc5 : pc s5 ≡ thunk-offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc thunk-offset 4 1)

    -- State after mov [rsp+8], rdi (store arg)
    rsp-s5 : readReg (regs s5) rsp ≡ new-rsp
    rsp-s5 = rsp-s4

    rdi-s5 : readReg (regs s5) rdi ≡ encode arg
    rdi-s5 = trans (readReg-writeReg-rsp-rdi (regs s3) new-rsp)
                   (trans (readReg-writeReg-rbp-rdi (regs s2) rsp-after-push)
                          (trans (readReg-writeReg-rsp-rdi (regs s1) rsp-after-push)
                                 rdi-eq))

    s6 : State
    s6 = record s5 { memory = writeMem (memory s5) (new-rsp +ℕ 8) (readReg (regs s5) rdi)
                   ; pc = pc s5 +ℕ 1 }

    step5 : step prog s5 ≡ just s6
    step5 = trans (step-exec prog s5 i5 h5 (subst (λ p → fetch prog p ≡ just i5) (sym pc5) fetch5))
                  (cong (λ addr → just (record s5 { memory = writeMem (memory s5) (addr +ℕ 8) (readReg (regs s5) rdi)
                                                  ; pc = pc s5 +ℕ 1 }))
                        rsp-s5)

    h6 : halted s6 ≡ false
    h6 = h-false

    pc6 : pc s6 ≡ thunk-offset +ℕ 6
    pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc thunk-offset 5 1)

    -- State after mov rdi, rsp (rdi = pair address)
    rsp-s6 : readReg (regs s6) rsp ≡ new-rsp
    rsp-s6 = rsp-s5

    s7 : State
    s7 = record s6 { regs = writeReg (regs s6) rdi new-rsp
                   ; pc = pc s6 +ℕ 1 }

    step6 : step prog s6 ≡ just s7
    step6 = trans (step-exec prog s6 i6 h6 (subst (λ p → fetch prog p ≡ just i6) (sym pc6) fetch6))
                  (cong (λ sp → just (record s6 { regs = writeReg (regs s6) rdi sp
                                                ; pc = pc s6 +ℕ 1 }))
                        rsp-s6)

    -- Compose Star proof
    star-all : Star prog s s7
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               ⟨ h5 , step5 ⟩◅
               ⟨ h6 , step6 ⟩◅
               refl*

    -- Final state properties
    h7 : halted s7 ≡ false
    h7 = h-false

    pc7 : pc s7 ≡ f-offset
    pc7 = begin
      pc s7
        ≡⟨ refl ⟩
      pc s6 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc6 ⟩
      (thunk-offset +ℕ 6) +ℕ 1
        ≡⟨ +-assoc thunk-offset 6 1 ⟩
      thunk-offset +ℕ 7
        ≡⟨ cong (_+ℕ 7) refl ⟩  -- thunk-offset = offset + 6
      (offset +ℕ 6) +ℕ 7
        ≡⟨ +-assoc offset 6 7 ⟩
      offset +ℕ 13
        ≡⟨ refl ⟩
      f-offset ∎

    -- rdi = new-rsp, and memory[new-rsp] = encode env, memory[new-rsp+8] = encode arg
    -- By encode-pair-construct, new-rsp = encode (env, arg)
    rdi-s7-is-new-rsp : readReg (regs s7) rdi ≡ new-rsp
    rdi-s7-is-new-rsp = readReg-writeReg-same (regs s6) rdi new-rsp

    -- Memory at new-rsp has encode env
    mem-env : readMem (memory s7) new-rsp ≡ just (encode env)
    mem-env = trans (mem-read-other {memory s5} {new-rsp +ℕ 8} {new-rsp} {readReg (regs s5) rdi}
                      (λ eq → n≢n+8 new-rsp (sym eq)))
                    (trans (mem-read-write {memory s4} {new-rsp} {readReg (regs s4) r12})
                           (cong just r12-s4))

    -- Memory at new-rsp+8 has encode arg
    mem-arg : readMem (memory s7) (new-rsp +ℕ 8) ≡ just (encode arg)
    mem-arg = trans (mem-read-write {memory s5} {new-rsp +ℕ 8} {readReg (regs s5) rdi})
                    (cong just rdi-s5)

    -- Use encode-pair-construct to show new-rsp = encode (env, arg)
    pair-encoding : new-rsp ≡ encode (env , arg)
    pair-encoding = encode-pair-construct env arg new-rsp (memory s7) mem-env mem-arg

    rdi7 : readReg (regs s7) rdi ≡ encode (env , arg)
    rdi7 = trans rdi-s7-is-new-rsp pair-encoding

    -- Register preservation (through all 7 instructions)
    -- Note: rbp is NOT preserved - it's set to frame pointer
    r14-7 : readReg (regs s7) r14 ≡ readReg (regs s) r14
    r14-7 = trans (readReg-writeReg-rdi-r14 (regs s6) new-rsp)
                  (trans (readReg-writeReg-rsp-r14 (regs s3) new-rsp)
                         (trans (readReg-writeReg-rbp-r14 (regs s2) rsp-after-push)
                                (trans (readReg-writeReg-rsp-r14 (regs s1) rsp-after-push)
                                       refl)))

    r15-7 : readReg (regs s7) r15 ≡ readReg (regs s) r15
    r15-7 = trans (readReg-writeReg-rdi-r15 (regs s6) new-rsp)
                  (trans (readReg-writeReg-rsp-r15 (regs s3) new-rsp)
                         (trans (readReg-writeReg-rbp-r15 (regs s2) rsp-after-push)
                                (trans (readReg-writeReg-rsp-r15 (regs s1) rsp-after-push)
                                       refl)))

    -- rbp is now set to rsp-after-push (the frame pointer)
    rbp7 : readReg (regs s7) rbp ≡ rsp-after-push
    rbp7 = trans (readReg-writeReg-rdi-rbp (regs s6) new-rsp)
                 (trans (readReg-writeReg-rsp-rbp (regs s3) new-rsp)
                        (readReg-writeReg-same (regs s2) rbp rsp-after-push))

    -- StackInvariant proof: rsp decreased, r15 unchanged
    -- s7.rsp = new-rsp = old-rsp - 8 - 16 ≤ old-rsp = s.rsp
    rsp-s7 : readReg (regs s7) rsp ≡ new-rsp
    rsp-s7 = trans (readReg-writeReg-rdi-rsp (regs s6) new-rsp) rsp-s6

    -- new-rsp = (old-rsp - 8) - 16 ≤ old-rsp
    rsp-decreased : new-rsp ≤ old-rsp
    rsp-decreased = ≤-trans (m∸n≤m rsp-after-push 16) (m∸n≤m old-rsp 8)

    rsp-s7≤s : readReg (regs s7) rsp ≤ readReg (regs s) rsp
    rsp-s7≤s = subst (_≤ old-rsp) (sym rsp-s7) rsp-decreased

    stack-inv7 : StackInvariant s7
    stack-inv7 = stack-inv-preserved-rsp-decreased s s7 stack-inv r15-7 rsp-s7≤s

    rsp>16-7 : readReg (regs s7) rsp > 16
    rsp>16-7 = ≤-trans 17≤41 (rsp-bound-after-stack-op s7)
      where
        open import Data.Nat.Properties using (≤-trans)
        17≤41 : 17 ≤ 41
        17≤41 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))))))

    -- Memory at rbp contains original rbp (from push rbp in s2)
    -- s2 wrote old-rbp at rsp-after-push (= old-rsp - 8)
    -- s5 wrote at new-rsp (= old-rsp - 24), s6 wrote at new-rsp+8 (= old-rsp - 16)
    -- Neither overwrites rsp-after-push, so the value persists to s7
    -- rbp in s7 = rsp-after-push, so readMem s7 rbp = just old-rbp

    -- Need: new-rsp ≢ rsp-after-push
    -- new-rsp = rsp-after-push - 16 < rsp-after-push
    -- Approach: new-rsp < new-rsp + 16 = rsp-after-push (when 16 ≤ rsp-after-push)
    open import Data.Nat.Properties using (m∸n+n≡m; +-monoˡ-<; m<m+n; 0<1+n)

    -- Proof: new-rsp = rsp-after-push - 16 ≢ rsp-after-push
    -- Key insight: rsp-after-push = old-rsp - 8 ≥ 9 (since old-rsp > 16)
    -- Case 1: If rsp-after-push ≥ 16, then new-rsp = rsp-after-push - 16 < rsp-after-push
    -- Case 2: If rsp-after-push < 16, then new-rsp = 0, but rsp-after-push ≥ 9 > 0
    open import Data.Nat using (_≤?_; z<s)
    open import Relation.Nullary using (yes; no)

    -- First, show rsp-after-push ≥ 9 (stronger than just > 0)
    -- rsp>16 : old-rsp > 16, i.e., old-rsp ≥ 17
    -- rsp-after-push = old-rsp - 8 ≥ 17 - 8 = 9
    open import Data.Nat.Properties using (∸-monoˡ-≤)
    open import Data.Empty using (⊥-elim)

    -- old-rsp ≥ 17 (from rsp>16)
    17≤old-rsp : 17 ≤ old-rsp
    17≤old-rsp = rsp>16

    9≤rsp-after-push : 9 ≤ rsp-after-push
    9≤rsp-after-push with 17 ≤? old-rsp
    -- ∸-monoˡ-≤ : m ≤ n → m ∸ o ≤ n ∸ o
    -- With m = 17, n = old-rsp, o = 8: 17 ≤ old-rsp → 17 ∸ 8 ≤ old-rsp ∸ 8
    -- 17 ∸ 8 = 9, old-rsp ∸ 8 = rsp-after-push
    ... | yes 17≤ = ∸-monoˡ-≤ {17} {old-rsp} 8 17≤
    ... | no ¬17≤ = ⊥-elim (¬17≤ 17≤old-rsp)

    rsp-after-push>0 : rsp-after-push > 0
    rsp-after-push>0 = ≤-trans 1≤9 9≤rsp-after-push
      where
        1≤9 : 1 ≤ 9
        1≤9 = s≤s z≤n

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

    new-rsp≢rsp-after-push : new-rsp ≢ rsp-after-push
    new-rsp≢rsp-after-push = ∸-neq rsp-after-push 16 rsp-after-push>0 0<16
      where
        0<16 : 0 < 16
        0<16 = s≤s z≤n

    -- For new-rsp + 8 ≢ rsp-after-push:
    -- new-rsp + 8 = (rsp-after-push - 16) + 8
    -- Case 1: If rsp-after-push ≥ 16, then new-rsp + 8 = rsp-after-push - 8 < rsp-after-push
    -- Case 2: If rsp-after-push < 16, then new-rsp = 0, so new-rsp + 8 = 8 < 9 ≤ rsp-after-push
    new-rsp+8≢rsp-after-push : new-rsp +ℕ 8 ≢ rsp-after-push
    new-rsp+8≢rsp-after-push eq with 16 ≤? rsp-after-push
    ... | yes 16≤ = <⇒≢-neq new-rsp+8<rsp-after-push eq
      where
        open import Data.Nat.Properties using (m∸n+n≡m)
        -- new-rsp + 8 = (rsp-after-push - 16) + 8
        -- rsp-after-push - 16 + 16 = rsp-after-push (since 16 ≤ rsp-after-push)
        -- So (rsp-after-push - 16) + 8 < (rsp-after-push - 16) + 16 = rsp-after-push
        new-rsp+8<rsp-after-push : new-rsp +ℕ 8 < rsp-after-push
        new-rsp+8<rsp-after-push = subst (new-rsp +ℕ 8 <_) (m∸n+n≡m 16≤) new-rsp+8<new-rsp+16
          where
            8<16 : 8 < 16
            8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
            new-rsp+8<new-rsp+16 : new-rsp +ℕ 8 < new-rsp +ℕ 16
            new-rsp+8<new-rsp+16 = +-monoʳ-< new-rsp 8<16
    ... | no ¬16≤ = <⇒≢-neq new-rsp+8<rsp eq
      where
        -- If rsp-after-push < 16, then rsp-after-push ≤ 16, so rsp-after-push ∸ 16 = 0
        -- new-rsp = rsp-after-push ∸ 16 = 0
        rsp<16 : rsp-after-push < 16
        rsp<16 = ≰⇒>-nat ¬16≤
        rsp≤16 : rsp-after-push ≤ 16
        rsp≤16 = <⇒≤-nat rsp<16
        new-rsp≡0 : new-rsp ≡ 0
        new-rsp≡0 = m≤n⇒m∸n≡0 rsp≤16
        -- 8 < 9 ≤ rsp-after-push
        8<9 : 8 < 9
        8<9 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        8<rsp : 8 < rsp-after-push
        8<rsp = ≤-trans 8<9 9≤rsp-after-push
        -- new-rsp + 8 = 0 + 8 = 8, so new-rsp + 8 < rsp-after-push
        new-rsp+8<rsp : new-rsp +ℕ 8 < rsp-after-push
        new-rsp+8<rsp = subst (λ n → n +ℕ 8 < rsp-after-push) (sym new-rsp≡0) 8<rsp

    -- s2 wrote old-rbp at rsp-after-push
    mem-s2-at-rsp-after-push : readMem (memory s2) rsp-after-push ≡ just old-rbp
    mem-s2-at-rsp-after-push = mem-read-write {memory s1} {rsp-after-push} {old-rbp}

    -- s3, s4 don't write to memory
    mem-s4-at-rsp-after-push : readMem (memory s4) rsp-after-push ≡ just old-rbp
    mem-s4-at-rsp-after-push = mem-s2-at-rsp-after-push

    -- s5 wrote at new-rsp, which ≢ rsp-after-push
    mem-s5-at-rsp-after-push : readMem (memory s5) rsp-after-push ≡ just old-rbp
    mem-s5-at-rsp-after-push = trans
      (mem-read-other {memory s4} {new-rsp} {rsp-after-push} {readReg (regs s4) r12}
                      (λ eq → new-rsp≢rsp-after-push eq))
      mem-s4-at-rsp-after-push

    -- s6 wrote at new-rsp + 8, which ≢ rsp-after-push
    mem-s6-at-rsp-after-push : readMem (memory s6) rsp-after-push ≡ just old-rbp
    mem-s6-at-rsp-after-push = trans
      (mem-read-other {memory s5} {new-rsp +ℕ 8} {rsp-after-push} {readReg (regs s5) rdi}
                      (λ eq → new-rsp+8≢rsp-after-push eq))
      mem-s5-at-rsp-after-push

    -- s7 doesn't write to memory
    mem-s7-at-rsp-after-push : readMem (memory s7) rsp-after-push ≡ just old-rbp
    mem-s7-at-rsp-after-push = mem-s6-at-rsp-after-push

    -- RbpInvariant: new-rsp ≤ rsp-after-push
    -- new-rsp = rsp-after-push - 16, so this follows from m∸n≤m
    rbp-inv7 : RbpInvariant s7
    rbp-inv7 = record { rsp≤rbp = new-rsp≤rsp-after-push }
      where
        new-rsp≤rsp-after-push-raw : new-rsp ≤ rsp-after-push
        new-rsp≤rsp-after-push-raw = m∸n≤m rsp-after-push 16
        new-rsp≤rsp-after-push : readReg (regs s7) rsp ≤ readReg (regs s7) rbp
        new-rsp≤rsp-after-push = subst₂ _≤_ (sym rsp-s7) (sym rbp7) new-rsp≤rsp-after-push-raw

    -- Finally, using rbp7: rbp s7 = rsp-after-push
    mem-at-rbp7 : readMem (memory s7) (readReg (regs s7) rbp) ≡ just old-rbp
    mem-at-rbp7 = subst (λ addr → readMem (memory s7) addr ≡ just old-rbp)
                        (sym rbp7) mem-s7-at-rsp-after-push

    -- Memory at old-rsp is preserved through setup
    -- s2 writes at rsp-after-push = old-rsp - 8 ≠ old-rsp
    -- s5 writes at new-rsp = old-rsp - 24 ≠ old-rsp
    -- s6 writes at new-rsp + 8 = old-rsp - 16 ≠ old-rsp
    rsp-after-push≢old-rsp : rsp-after-push ≢ old-rsp
    rsp-after-push≢old-rsp = ∸-neq old-rsp 8 (≤-trans 1≤17 rsp>16) 0<8
      where
        1≤17 : 1 ≤ 17
        1≤17 = s≤s z≤n
        0<8 : 0 < 8
        0<8 = s≤s z≤n

    -- new-rsp ≤ rsp-after-push < old-rsp (when old-rsp > 16)
    -- Case 1: rsp-after-push ≥ 16 → new-rsp = rsp-after-push - 16 < rsp-after-push < old-rsp
    -- Case 2: rsp-after-push < 16 → new-rsp = 0, but old-rsp > 16 > 0
    new-rsp≢old-rsp : new-rsp ≢ old-rsp
    new-rsp≢old-rsp eq with 16 ≤? rsp-after-push
    ... | yes 16≤ = <⇒≢-neq new-rsp<old-rsp eq
      where
        -- new-rsp = rsp-after-push - 16 < rsp-after-push (since 16 > 0 and 16 ≤ rsp-after-push)
        new-rsp<rsp-after-push : new-rsp < rsp-after-push
        new-rsp<rsp-after-push = ∸-monoʳ-< z<s 16≤
        -- rsp-after-push = old-rsp - 8 < old-rsp (since 8 > 0 and 8 ≤ old-rsp)
        8≤old-rsp : 8 ≤ old-rsp
        8≤old-rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) rsp>16
        rsp-after-push<old-rsp : rsp-after-push < old-rsp
        rsp-after-push<old-rsp = ∸-monoʳ-< z<s 8≤old-rsp
        new-rsp<old-rsp : new-rsp < old-rsp
        new-rsp<old-rsp = <-trans new-rsp<rsp-after-push rsp-after-push<old-rsp
    ... | no ¬16≤ = 0≢old-rsp (trans (sym new-rsp≡0) eq)
      where
        -- rsp-after-push < 16 → new-rsp = 0
        rsp<16 : rsp-after-push < 16
        rsp<16 = ≰⇒>-nat ¬16≤
        new-rsp≡0 : new-rsp ≡ 0
        new-rsp≡0 = m≤n⇒m∸n≡0 (<⇒≤-nat rsp<16)
        -- old-rsp > 16 > 0, so 0 ≠ old-rsp
        old-rsp>0 : old-rsp > 0
        old-rsp>0 = ≤-trans (s≤s z≤n) rsp>16
        0≢old-rsp : 0 ≢ old-rsp
        0≢old-rsp zeq = <⇒≢-neq old-rsp>0 zeq

    -- new-rsp + 8 = (rsp-after-push - 16) + 8 < old-rsp
    -- Since rsp-after-push = old-rsp - 8 < old-rsp (when old-rsp > 8)
    -- and new-rsp + 8 ≤ rsp-after-push (either equals rsp-after-push - 8 or 8)
    new-rsp+8≢old-rsp : new-rsp +ℕ 8 ≢ old-rsp
    new-rsp+8≢old-rsp eq with 16 ≤? rsp-after-push
    ... | yes 16≤ = <⇒≢-neq new-rsp+8<old-rsp eq
      where
        -- new-rsp + 8 = rsp-after-push - 16 + 8 = rsp-after-push - 8 < rsp-after-push < old-rsp
        open import Data.Nat.Properties using (m∸n+n≡m)
        8<16 : 8 < 16
        8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        new-rsp+8<rsp-after-push+16 : new-rsp +ℕ 8 < new-rsp +ℕ 16
        new-rsp+8<rsp-after-push+16 = +-monoʳ-< new-rsp 8<16
        new-rsp+8<rsp-after-push : new-rsp +ℕ 8 < rsp-after-push
        new-rsp+8<rsp-after-push = subst (new-rsp +ℕ 8 <_) (m∸n+n≡m 16≤) new-rsp+8<rsp-after-push+16
        8≤old-rsp : 8 ≤ old-rsp
        8≤old-rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) rsp>16
        rsp-after-push<old-rsp : rsp-after-push < old-rsp
        rsp-after-push<old-rsp = ∸-monoʳ-< z<s 8≤old-rsp
        new-rsp+8<old-rsp : new-rsp +ℕ 8 < old-rsp
        new-rsp+8<old-rsp = <-trans new-rsp+8<rsp-after-push rsp-after-push<old-rsp
    ... | no ¬16≤ = <⇒≢-neq new-rsp+8<old-rsp eq
      where
        -- new-rsp = 0, so new-rsp + 8 = 8 < 9 ≤ rsp-after-push < old-rsp
        rsp<16 : rsp-after-push < 16
        rsp<16 = ≰⇒>-nat ¬16≤
        new-rsp≡0 : new-rsp ≡ 0
        new-rsp≡0 = m≤n⇒m∸n≡0 (<⇒≤-nat rsp<16)
        8<9 : 8 < 9
        8<9 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        8<rsp-after-push : 8 < rsp-after-push
        8<rsp-after-push = ≤-trans 8<9 9≤rsp-after-push
        8≤old-rsp : 8 ≤ old-rsp
        8≤old-rsp = ≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) rsp>16
        rsp-after-push<old-rsp : rsp-after-push < old-rsp
        rsp-after-push<old-rsp = ∸-monoʳ-< z<s 8≤old-rsp
        new-rsp+8<rsp-after-push : new-rsp +ℕ 8 < rsp-after-push
        new-rsp+8<rsp-after-push = subst (λ n → n +ℕ 8 < rsp-after-push) (sym new-rsp≡0) 8<rsp-after-push
        new-rsp+8<old-rsp : new-rsp +ℕ 8 < old-rsp
        new-rsp+8<old-rsp = <-trans new-rsp+8<rsp-after-push rsp-after-push<old-rsp

    -- s1 doesn't write memory
    mem-s1-old-rsp : readMem (memory s1) old-rsp ≡ readMem (memory s) old-rsp
    mem-s1-old-rsp = refl

    -- s2 writes at rsp-after-push ≠ old-rsp
    mem-s2-old-rsp : readMem (memory s2) old-rsp ≡ readMem (memory s) old-rsp
    mem-s2-old-rsp = mem-read-other {memory s1} {rsp-after-push} {old-rsp} {old-rbp}
                       (λ eq → rsp-after-push≢old-rsp eq)

    -- s3, s4 don't write memory
    mem-s4-old-rsp : readMem (memory s4) old-rsp ≡ readMem (memory s) old-rsp
    mem-s4-old-rsp = mem-s2-old-rsp

    -- s5 writes at new-rsp ≠ old-rsp
    mem-s5-old-rsp : readMem (memory s5) old-rsp ≡ readMem (memory s) old-rsp
    mem-s5-old-rsp = trans (mem-read-other {memory s4} {new-rsp} {old-rsp} {readReg (regs s4) r12}
                             (λ eq → new-rsp≢old-rsp eq))
                           mem-s4-old-rsp

    -- s6 writes at new-rsp + 8 ≠ old-rsp
    mem-s6-old-rsp : readMem (memory s6) old-rsp ≡ readMem (memory s) old-rsp
    mem-s6-old-rsp = trans (mem-read-other {memory s5} {new-rsp +ℕ 8} {old-rsp} {readReg (regs s5) rdi}
                             (λ eq → new-rsp+8≢old-rsp eq))
                           mem-s5-old-rsp

    -- s7 doesn't write memory
    mem-old-rsp-preserved : readMem (memory s7) old-rsp ≡ readMem (memory s) old-rsp
    mem-old-rsp-preserved = mem-s6-old-rsp

-- Prove ret instruction tracing
thunk-ret-star : ∀ {A B C} (f : IR (A * B) C)
                 (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
      ret-offset = length prefix +ℕ 15 +ℕ compile-length f  -- 6 closure + 7 thunk + len-f + 2 cleanup
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
          × readReg (regs s') rsp > 16)
thunk-ret-star {A} {B} {C} f prefix suffix ret-addr s
               h-false pc-eq mem-ret stack-inv rsp>16 =
  s1 , star-all , h1 , pc1 , rax1 , r14-1 , r15-1 , rbp1 , stack-inv1 , rsp>16-1
  where
    open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)

    prog = prefix ++ compile-x86 (curry f) ++ suffix
    offset = length prefix
    ret-offset = offset +ℕ 15 +ℕ compile-length f  -- 6 closure + 7 thunk + len-f + 2 cleanup

    -- The ret instruction is at ret-offset in curry
    -- curry layout: [6 closure setup] [7 thunk setup] [compile-x86 f] [2 cleanup] [ret] [label end]
    -- ret is at position 15 + len(f) within curry

    -- Fetch the ret instruction (proven in ThunkStructure)
    fetch-ret : fetch prog ret-offset ≡ just ret
    fetch-ret = TS-fetch-ret f prefix suffix

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
