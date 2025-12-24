------------------------------------------------------------------------
-- Once.Backend.X86.Correct.IR.Curry
--
-- Star-based curry proof.
-- Non-recursive, so can live outside the mutual block.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.IR.Curry where

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open Once.Backend.X86.Semantics.Flags
open import Once.Backend.X86.CodeGen

open import Once.Postulates using (encode; encode-closure-construct)
open import Once.Backend.X86.Postulates using (rsp-bound-after-stack-op)
open import Once.Backend.X86.Correct.RegisterLemmas
open import Once.Backend.X86.Correct.FetchStep
open import Once.Backend.X86.Correct.CompileLength hiding (length-++)
open import Once.Backend.X86.Correct.InstrExec
open import Once.Backend.X86.Correct.StackInvariant
open import Once.Backend.X86.Correct.ExecLemmas
open import Once.Backend.X86.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_)
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResult;
         ir-star; ir-halted; ir-pc; ir-rax; ir-r14; ir-r15; ir-rbp;
         ir-mem; ir-stack-inv; ir-rsp-bound)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; suc; _∸_; _>_; _≤_; _<_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-trans; m∸n≤m; m<m+n; 0<1+n; ∸-monoʳ-<; <⇒≤; +-monoʳ-<; m∸n+n≡m; m≤m+n) renaming (<⇒≢ to Nat-<⇒≢)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- CurryMemoryResult: Memory layout produced by curry
------------------------------------------------------------------------

-- | Record capturing the memory layout produced by curry
-- This is what apply needs to look up the closure
record CurryMemoryResult {A B C : Type} (f : IR (A * B) C)
                         (prog : Program) (s-final : State)
                         (x : ⟦ A ⟧) (offset : ℕ) : Set where
  field
    closure-addr : ℕ
    code-ptr : ℕ
    env-addr : ℕ
    -- rax holds the closure address
    rax-eq : readReg (regs s-final) rax ≡ closure-addr
    -- Memory layout of the closure
    mem-env : readMem (memory s-final) closure-addr ≡ just env-addr
    mem-cp : readMem (memory s-final) (closure-addr +ℕ 8) ≡ just code-ptr
    -- Semantic values
    env-is-encoded : env-addr ≡ encode x
    code-ptr-is-thunk : code-ptr ≡ offset +ℕ 6

open CurryMemoryResult public

------------------------------------------------------------------------
-- Main curry proof
------------------------------------------------------------------------

run-curry-star : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) rdi ≡ encode x →
  StackInvariant s →
  readReg (regs s) rsp > 16 →
  let prog = prefix ++ compile-x86 (curry f) ++ suffix
  in ∃[ s' ] (IRStarResult (curry f) prog s s' x (length prefix)
             × CurryMemoryResult f prog s' x (length prefix))
run-curry-star {A} {B} {C} f prefix suffix x s h-false pc-eq rdi-eq stack-inv rsp>16 =
  s-final , record
    { ir-star = star-all
    ; ir-halted = h-final
    ; ir-pc = pc-final
    ; ir-rax = rax-final
    ; ir-r14 = r14-final
    ; ir-r15 = r15-final
    ; ir-rbp = rbp-final
    ; ir-mem = mem-final
    ; ir-mem-rbp = mem-rbp-final
    ; ir-mem-rbp+8 = mem-rbp+8-final
    ; ir-stack-inv = stack-inv-final
    ; ir-rsp-bound = rsp>16-final
    } , record
    { closure-addr = new-rsp
    ; code-ptr = thunk-offset
    ; env-addr = encode x
    ; rax-eq = rax-s7
    ; mem-env = mem-at-new-rsp-final
    ; mem-cp = mem-code-ptr-final
    ; env-is-encoded = refl
    ; code-ptr-is-thunk = refl
    }
  where
    len-f = compile-length f
    prog = prefix ++ compile-x86 (curry f) ++ suffix

    -- Key offsets (matching CodeGen.agda layout)
    -- jmp at pos 5 needs to reach end-label at pos 16+len-f
    -- offset = target - (pc + 1) = (16+len-f) - 6 = 10+len-f
    jmp-offset : ℕ
    jmp-offset = 10 +ℕ len-f

    end-label-pos : ℕ
    end-label-pos = 16 +ℕ len-f

    -- Helper values
    orig-rsp : Word
    orig-rsp = readReg (regs s) rsp

    new-rsp : Word
    new-rsp = orig-rsp ∸ 16

    -- The 7 instructions that actually execute
    i0 : Instr
    i0 = sub (reg rsp) (imm 16)

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
    s4 = record s3 { memory = writeMem (memory s3) (readReg (regs s3) rsp +ℕ 8) (readReg (regs s3) r9)
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

    -- For the label, we need fetch at pc s6 = prefix + 16 + len-f
    -- New layout with frame pointer:
    -- 6 setup + 1 label + 2 frame setup + 4 thunk setup + |f| + 3 cleanup = 16 + |f|
    curry-before-end-label : Program
    curry-before-end-label =
      i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷  -- 6 closure setup instructions
      label 6 ∷                        -- thunk entry
      push (reg rbp) ∷                 -- save frame pointer
      mov (reg rbp) (reg rsp) ∷        -- set frame pointer
      sub (reg rsp) (imm 16) ∷         -- allocate pair
      mov (mem (base rsp)) (reg r12) ∷
      mov (mem (base+disp rsp 8)) (reg rdi) ∷
      mov (reg rdi) (reg rsp) ∷
      compile-x86 f ++                 -- inner function
      mov (reg rsp) (reg rbp) ∷        -- restore stack
      pop rbp ∷                        -- restore frame pointer
      ret ∷ []                         -- return

    len-curry-before : length curry-before-end-label ≡ end-label-pos
    len-curry-before = begin
      length curry-before-end-label
        ≡⟨ refl ⟩
      length (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷
              label 6 ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
              sub (reg rsp) (imm 16) ∷
              mov (mem (base rsp)) (reg r12) ∷
              mov (mem (base+disp rsp 8)) (reg rdi) ∷
              mov (reg rdi) (reg rsp) ∷
              compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ ret ∷ [])
        ≡⟨ refl ⟩
      13 +ℕ length (compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ ret ∷ [])
        ≡⟨ cong (13 +ℕ_) (List-length-++ (compile-x86 f)) ⟩
      13 +ℕ (length (compile-x86 f) +ℕ 3)
        ≡⟨ cong (λ z → 13 +ℕ (z +ℕ 3)) (compile-length-correct f) ⟩
      13 +ℕ (len-f +ℕ 3)
        ≡⟨ +-assoc 13 len-f 3 ⟩
      (13 +ℕ len-f) +ℕ 3
        ≡⟨ cong (_+ℕ 3) (+-comm 13 len-f) ⟩
      (len-f +ℕ 13) +ℕ 3
        ≡⟨ +-assoc len-f 13 3 ⟩
      len-f +ℕ 16
        ≡⟨ +-comm len-f 16 ⟩
      end-label-pos
        ∎

    curry-code-inner : Program
    curry-code-inner = compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ ret ∷ i6-label ∷ []

    curry-inner-split : curry-code-inner ≡ (compile-x86 f ++ mov (reg rsp) (reg rbp) ∷ pop rbp ∷ ret ∷ []) ++ i6-label ∷ []
    curry-inner-split = sym (++-assoc (compile-x86 f) (mov (reg rsp) (reg rbp) ∷ pop rbp ∷ ret ∷ []) (i6-label ∷ []))

    curry-split : compile-x86 (curry f) ≡ curry-before-end-label ++ i6-label ∷ []
    curry-split = cong (λ rest → i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷
                                 label 6 ∷ push (reg rbp) ∷ mov (reg rbp) (reg rsp) ∷
                                 sub (reg rsp) (imm 16) ∷
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
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 6 10 len-f)) ⟩
      length prefix +ℕ ((6 +ℕ 10) +ℕ len-f)
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
      length prefix +ℕ (17 +ℕ len-f)
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

    -- Show memory at new-rsp contains encode x
    -- s2 writes (readReg (regs s1) rdi) to (readReg (regs s1) rsp) = new-rsp
    -- s4 writes to rsp+8, not rsp, so new-rsp is unchanged
    rdi-s1 : readReg (regs s1) rdi ≡ encode x
    rdi-s1 = trans (readReg-writeReg-rsp-rdi (regs s) new-rsp) rdi-eq

    mem-at-new-rsp-s2 : readMem (memory s2) new-rsp ≡ just (encode x)
    mem-at-new-rsp-s2 = trans (readMem-writeMem-same (memory s1) (readReg (regs s1) rsp) (readReg (regs s1) rdi))
                              (cong just (trans (cong (λ addr → readReg (regs s1) rdi) (sym rsp-s1)) rdi-s1))

    -- s3 doesn't modify memory
    mem-at-new-rsp-s3 : readMem (memory s3) new-rsp ≡ just (encode x)
    mem-at-new-rsp-s3 = mem-at-new-rsp-s2

    -- s4 writes to rsp+8, not new-rsp
    -- Need to show new-rsp ≢ new-rsp + 8
    -- Proof: new-rsp < new-rsp + 8 (since 8 > 0), therefore new-rsp ≢ new-rsp + 8
    new-rsp≢new-rsp+8 : new-rsp ≢ new-rsp +ℕ 8
    new-rsp≢new-rsp+8 = Nat-<⇒≢ (m<m+n new-rsp 0<1+n)

    mem-at-new-rsp-s4 : readMem (memory s4) new-rsp ≡ just (encode x)
    mem-at-new-rsp-s4 = trans (readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ 8) new-rsp
                                (readReg (regs s3) r9)
                                (subst (λ addr → addr +ℕ 8 ≢ new-rsp) (sym rsp-s3) (λ eq → new-rsp≢new-rsp+8 (sym eq))))
                              mem-at-new-rsp-s3

    -- s5, s6, s7 don't modify memory
    mem-at-new-rsp-final : readMem (memory s-final) new-rsp ≡ just (encode x)
    mem-at-new-rsp-final = mem-at-new-rsp-s4

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
    mem-code-ptr-s4 : readMem (memory s4) (new-rsp +ℕ 8) ≡ just thunk-offset
    mem-code-ptr-s4 =
      let rsp-eq : readReg (regs s3) rsp ≡ new-rsp
          rsp-eq = rsp-s3
          write-addr = readReg (regs s3) rsp +ℕ 8
          write-addr-eq : write-addr ≡ new-rsp +ℕ 8
          write-addr-eq = cong (_+ℕ 8) rsp-eq
      in trans (subst (λ addr → readMem (writeMem (memory s3) write-addr (readReg (regs s3) r9)) addr ≡
                                just (readReg (regs s3) r9))
                      write-addr-eq
                      (readMem-writeMem-same (memory s3) write-addr (readReg (regs s3) r9)))
               (cong just r9-s3)

    -- s5, s6, s7 don't modify memory, so code-ptr persists
    mem-code-ptr-final : readMem (memory s-final) (new-rsp +ℕ 8) ≡ just thunk-offset
    mem-code-ptr-final = mem-code-ptr-s4

    -- Use encode-closure-construct axiom
    encode-curry-result : new-rsp ≡ encode {B ⇒ C} (eval {A} {B ⇒ C} (curry f) x)
    encode-curry-result = encode-closure-construct f x new-rsp (memory s-final) mem-at-new-rsp-final

    rax-final : readReg (regs s-final) rax ≡ encode {B ⇒ C} (eval (curry f) x)
    rax-final = trans rax-s7 encode-curry-result

    -- Memory preservation
    orig-r15 : Word
    orig-r15 = readReg (regs s) r15

    addr-diff : (new-rsp ≢ orig-r15) × ((new-rsp +ℕ 8) ≢ orig-r15)
    addr-diff = addr-diff-from-invariant s stack-inv rsp>16

    mem-s1-eq : readMem (memory s1) orig-r15 ≡ readMem (memory s) orig-r15
    mem-s1-eq = refl

    mem-s2-eq : readMem (memory s2) orig-r15 ≡ readMem (memory s1) orig-r15
    mem-s2-eq = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) orig-r15
                  (readReg (regs s1) rdi) (subst (λ addr → addr ≢ orig-r15) (sym rsp-s1) (proj₁ addr-diff))

    mem-s3-eq : readMem (memory s3) orig-r15 ≡ readMem (memory s2) orig-r15
    mem-s3-eq = refl

    mem-s4-eq : readMem (memory s4) orig-r15 ≡ readMem (memory s3) orig-r15
    mem-s4-eq = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ 8) orig-r15
                  (readReg (regs s3) r9)
                  (subst (λ addr → addr +ℕ 8 ≢ orig-r15) (sym rsp-s3) (proj₂ addr-diff))

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
    -- Proved via RbpInvariant: rsp ≤ rbp, so new-rsp = rsp-16 < rsp ≤ rbp
    orig-rbp : Word
    orig-rbp = readReg (regs s) rbp

    -- RbpInvariant: s.rsp ≤ s.rbp (stack pointer at or below frame pointer)
    postulate rbp-inv : RbpInvariant s

    -- new-rsp < rbp: since new-rsp = rsp - 16 < rsp ≤ rbp
    -- ∸-monoʳ-< : o < n → n ≤ m → m ∸ n < m ∸ o
    -- With o = 0, n = 16, m = orig-rsp: 0 < 16 → 16 ≤ orig-rsp → orig-rsp ∸ 16 < orig-rsp
    16≤orig-rsp : 16 ≤ orig-rsp
    16≤orig-rsp = <⇒≤ rsp>16

    new-rsp<rbp : new-rsp < orig-rbp
    new-rsp<rbp = ≤-trans new-rsp<orig-rsp (RbpInvariant.rsp≤rbp rbp-inv)
      where
        new-rsp<orig-rsp : new-rsp < orig-rsp
        new-rsp<orig-rsp = ∸-monoʳ-< 0<16 16≤orig-rsp
          where
            0<16 : 0 < 16
            0<16 = m<m+n 0 0<1+n

    -- For new-rsp + 8 < rbp:
    -- new-rsp + 8 < orig-rsp (since 8 < 16 and 16 ≤ orig-rsp)
    -- orig-rsp ≤ rbp (from RbpInvariant)
    -- Therefore new-rsp + 8 < rbp
    new-rsp+8<rbp : (new-rsp +ℕ 8) < orig-rbp
    new-rsp+8<rbp = ≤-trans new-rsp+8<orig-rsp (RbpInvariant.rsp≤rbp rbp-inv)
      where
        -- (rsp - 16) + 8 < rsp when 8 < 16 and 16 ≤ rsp
        -- Using ∸-monoʳ-< with o=0, n=8: 0 < 8 → 8 ≤ m → m ∸ 8 < m
        -- But we have (rsp - 16) + 8, not rsp - 8
        -- Key: (rsp - 16) + 8 < (rsp - 16) + 16 = rsp (when rsp ≥ 16)
        8<16 : 8 < 16
        8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        new-rsp+8<new-rsp+16 : (new-rsp +ℕ 8) < (new-rsp +ℕ 16)
        new-rsp+8<new-rsp+16 = +-monoʳ-< new-rsp 8<16
        new-rsp+16≡orig-rsp : (new-rsp +ℕ 16) ≡ orig-rsp
        new-rsp+16≡orig-rsp = m∸n+n≡m 16≤orig-rsp
        new-rsp+8<orig-rsp : (new-rsp +ℕ 8) < orig-rsp
        new-rsp+8<orig-rsp = subst ((new-rsp +ℕ 8) <_) new-rsp+16≡orig-rsp new-rsp+8<new-rsp+16

    -- Disjointness: new-rsp ≢ rbp and new-rsp+8 ≢ rbp
    rbp-diff-1 : new-rsp ≢ orig-rbp
    rbp-diff-1 eq = Nat-<⇒≢ new-rsp<rbp eq

    rbp-diff-2 : (new-rsp +ℕ 8) ≢ orig-rbp
    rbp-diff-2 eq = Nat-<⇒≢ new-rsp+8<rbp eq

    -- Chain memory preservation through all states
    mem-rbp-s1 : readMem (memory s1) orig-rbp ≡ readMem (memory s) orig-rbp
    mem-rbp-s1 = refl

    mem-rbp-s2 : readMem (memory s2) orig-rbp ≡ readMem (memory s1) orig-rbp
    mem-rbp-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) orig-rbp
                   (readReg (regs s1) rdi) (subst (λ addr → addr ≢ orig-rbp) (sym rsp-s1) rbp-diff-1)

    mem-rbp-s3 : readMem (memory s3) orig-rbp ≡ readMem (memory s2) orig-rbp
    mem-rbp-s3 = refl

    mem-rbp-s4 : readMem (memory s4) orig-rbp ≡ readMem (memory s3) orig-rbp
    mem-rbp-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ 8) orig-rbp
                   (readReg (regs s3) r9)
                   (subst (λ addr → addr +ℕ 8 ≢ orig-rbp) (sym rsp-s3) rbp-diff-2)

    mem-rbp-s5 : readMem (memory s5) orig-rbp ≡ readMem (memory s4) orig-rbp
    mem-rbp-s5 = refl

    mem-rbp-s6 : readMem (memory s6) orig-rbp ≡ readMem (memory s5) orig-rbp
    mem-rbp-s6 = refl

    mem-rbp-s7 : readMem (memory s7) orig-rbp ≡ readMem (memory s6) orig-rbp
    mem-rbp-s7 = refl

    mem-rbp-final : readMem (memory s-final) (readReg (regs s) rbp) ≡ readMem (memory s) (readReg (regs s) rbp)
    mem-rbp-final = trans mem-rbp-s7 (trans mem-rbp-s6 (trans mem-rbp-s5 (trans mem-rbp-s4
                      (trans mem-rbp-s3 (trans mem-rbp-s2 mem-rbp-s1)))))

    -- Similarly for rbp+8
    orig-rbp+8 : Word
    orig-rbp+8 = readReg (regs s) rbp +ℕ 8

    -- new-rsp < rbp ≤ rbp+8, so new-rsp < rbp+8
    -- new-rsp<rbp : suc new-rsp ≤ rbp, and rbp ≤ rbp+8, gives suc new-rsp ≤ rbp+8
    new-rsp<rbp+8 : new-rsp < orig-rbp+8
    new-rsp<rbp+8 = ≤-trans new-rsp<rbp (m≤m+n orig-rbp 8)

    new-rsp+8<rbp+8 : (new-rsp +ℕ 8) < orig-rbp+8
    new-rsp+8<rbp+8 = ≤-trans new-rsp+8<rbp (m≤m+n orig-rbp 8)

    rbp+8-diff-1 : new-rsp ≢ orig-rbp+8
    rbp+8-diff-1 eq = Nat-<⇒≢ new-rsp<rbp+8 eq

    rbp+8-diff-2 : (new-rsp +ℕ 8) ≢ orig-rbp+8
    rbp+8-diff-2 eq = Nat-<⇒≢ new-rsp+8<rbp+8 eq

    mem-rbp+8-s1 : readMem (memory s1) orig-rbp+8 ≡ readMem (memory s) orig-rbp+8
    mem-rbp+8-s1 = refl

    mem-rbp+8-s2 : readMem (memory s2) orig-rbp+8 ≡ readMem (memory s1) orig-rbp+8
    mem-rbp+8-s2 = readMem-writeMem-diff (memory s1) (readReg (regs s1) rsp) orig-rbp+8
                     (readReg (regs s1) rdi) (subst (λ addr → addr ≢ orig-rbp+8) (sym rsp-s1) rbp+8-diff-1)

    mem-rbp+8-s3 : readMem (memory s3) orig-rbp+8 ≡ readMem (memory s2) orig-rbp+8
    mem-rbp+8-s3 = refl

    mem-rbp+8-s4 : readMem (memory s4) orig-rbp+8 ≡ readMem (memory s3) orig-rbp+8
    mem-rbp+8-s4 = readMem-writeMem-diff (memory s3) (readReg (regs s3) rsp +ℕ 8) orig-rbp+8
                     (readReg (regs s3) r9)
                     (subst (λ addr → addr +ℕ 8 ≢ orig-rbp+8) (sym rsp-s3) rbp+8-diff-2)

    mem-rbp+8-s5 : readMem (memory s5) orig-rbp+8 ≡ readMem (memory s4) orig-rbp+8
    mem-rbp+8-s5 = refl

    mem-rbp+8-s6 : readMem (memory s6) orig-rbp+8 ≡ readMem (memory s5) orig-rbp+8
    mem-rbp+8-s6 = refl

    mem-rbp+8-s7 : readMem (memory s7) orig-rbp+8 ≡ readMem (memory s6) orig-rbp+8
    mem-rbp+8-s7 = refl

    mem-rbp+8-final : readMem (memory s-final) (readReg (regs s) rbp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) rbp +ℕ 8)
    mem-rbp+8-final = trans mem-rbp+8-s7 (trans mem-rbp+8-s6 (trans mem-rbp+8-s5 (trans mem-rbp+8-s4
                        (trans mem-rbp+8-s3 (trans mem-rbp+8-s2 mem-rbp+8-s1)))))

    -- StackInvariant preservation
    stack-inv-helper : StackInvariant s → StackInvariant s-final
    stack-inv-helper (r15-unused r15≡0) = r15-unused (trans r15-final r15≡0)
    stack-inv-helper (stack-below-r15 rsp≤r15) = stack-below-r15 new-rsp≤r15
      where
        new-rsp≤orig-rsp : new-rsp ≤ orig-rsp
        new-rsp≤orig-rsp = m∸n≤m orig-rsp 16
        new-rsp≤r15-orig : new-rsp ≤ readReg (regs s) r15
        new-rsp≤r15-orig = ≤-trans new-rsp≤orig-rsp rsp≤r15
        new-rsp≤r15 : readReg (regs s-final) rsp ≤ readReg (regs s-final) r15
        new-rsp≤r15 = subst₂ _≤_ (sym rsp-s7) (sym r15-final) new-rsp≤r15-orig

    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-helper stack-inv

    rsp>16-final : readReg (regs s-final) rsp > 16
    rsp>16-final = rsp-bound-after-stack-op s-final
