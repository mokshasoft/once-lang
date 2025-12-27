------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Curry
--
-- Star-based curry proof for RISC-V 64-bit.
-- Non-recursive, so can live outside the mutual block.
--
-- RISC-V curry layout (8 executed steps):
--   0: addi sp sp -16      (allocate closure)
--   1: sd a0 0(sp)         (store env)
--   2: auipc t0 0          (t0 = PC = offset + 2)
--   3: addi t0 t0 5        (t0 = offset + 7 = thunk entry)
--   4: sd t0 8(sp)         (store code_ptr)
--   5: mv a0 sp            (return closure pointer)
--   6: j (12 + len-f)      (jump to end label)
--   [SKIPPED: positions 7 to 17+len-f = thunk code + cleanup + ret]
--   18+len-f: label end    (no-op)
--
-- After 8 steps: PC = offset + 19 + len-f = offset + compile-length (curry f)
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.IR.Curry where

open import Size

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr)

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates using (encode; encode-closure-construct)
open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.CompileLength using (compile-length-correct)
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_; star-step2; star-step3; star-step4)
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra;
         ir-sp-delta; ir-sp; ir-mem-sp; ir-mem-sp+8; ir-mem-sp+16; ir-mem-sp+24)

open import Once.Backend.Common.Memory
  using (readMem-writeMem-same; readMem-writeMem-diff; n≢n+suc)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; suc; _∸_; _≤_; z≤n; s≤s; _<_; z<s; s<s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; m∸n+n≡m; ≤-trans)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Main curry proof
------------------------------------------------------------------------

run-curry-star : ∀ {i A B C} (f : IR i (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  24 ≤ readReg (regs s) sp →
  let prog = prefix ++ compile-riscv (curry f) ++ suffix
  in ∃[ s' ] IRStarResult (curry f) prog s s' x (length prefix)
run-curry-star {_} {A} {B} {C} f prefix suffix x s h-false pc-eq a0-eq sp-bound =
  s-final , record
    { ir-star   = star-all
    ; ir-halted = h-final
    ; ir-pc     = pc-final
    ; ir-a0     = a0-final
    ; ir-s1     = s1-final
    ; ir-s2     = s2-final
    ; ir-ra     = ra-final
    ; ir-sp-delta = 16
    ; ir-sp     = sp-final
    ; ir-mem-sp = mem-sp-final
    ; ir-mem-sp+8 = mem-sp+8-final
    ; ir-mem-sp+16 = mem-sp+16-final
    ; ir-mem-sp+24 = mem-sp+24-final
    }
  where
    len-f = compile-length f
    prog = prefix ++ compile-riscv (curry f) ++ suffix

    -- Helper values
    orig-sp : Word
    orig-sp = readReg (regs s) sp

    orig-a0 : Word
    orig-a0 = readReg (regs s) a0

    new-sp : Word
    new-sp = orig-sp ∸ 16

    -- The 8 instructions that actually execute (7 setup + 1 end label)
    i0 : Instr
    i0 = addi sp sp neg16

    i1 : Instr
    i1 = sd a0 (+ 0) sp

    i2 : Instr
    i2 = auipc t0 (+ 0)

    i3 : Instr
    i3 = addi t0 t0 (+ 5)

    i4 : Instr
    i4 = sd t0 (+ 8) sp

    i5 : Instr
    i5 = mv a0 sp

    i6 : Instr
    i6 = j (+ (12 +ℕ len-f))

    i-end-label : Instr
    i-end-label = label (18 +ℕ len-f)

    -- State after step 0: addi sp sp -16
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp
                   ; pc = pc s +ℕ 1 }

    -- State after step 1: sd a0 0(sp)
    st2 : State
    st2 = record st1 { memory = writeMem (memory st1) (readReg (regs st1) sp +ℕ 0) (readReg (regs st1) a0)
                     ; pc = pc st1 +ℕ 1 }

    -- State after step 2: auipc t0 0 (t0 = pc = length prefix + 2)
    -- Note: RISC-V auipc sets t0 = PC, and PC is instruction index at execution time
    st3 : State
    st3 = record st2 { regs = writeReg (regs st2) t0 (pc st2)
                     ; pc = pc st2 +ℕ 1 }

    -- State after step 3: addi t0 t0 5 (t0 = PC + 5 = length prefix + 2 + 5 = length prefix + 7)
    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) t0 (readReg (regs st3) t0 +ℕ 5)
                     ; pc = pc st3 +ℕ 1 }

    -- State after step 4: sd t0 8(sp)
    st5 : State
    st5 = record st4 { memory = writeMem (memory st4) (readReg (regs st4) sp +ℕ 8) (readReg (regs st4) t0)
                     ; pc = pc st4 +ℕ 1 }

    -- State after step 5: mv a0 sp
    st6 : State
    st6 = record st5 { regs = writeReg (regs st5) a0 (readReg (regs st5) sp)
                     ; pc = pc st5 +ℕ 1 }

    -- State after step 6: j (12 + len-f)
    -- PC jumps from (prefix + 6) to (prefix + 6 + (12 + len-f)) = prefix + 18 + len-f
    st7 : State
    st7 = record st6 { pc = pc st6 +ℕ (12 +ℕ len-f) }

    -- State after step 7: label (18 + len-f) - just advances PC by 1
    st8 : State
    st8 = record st7 { pc = pc st7 +ℕ 1 }

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

    prog-eq6 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ []) ++ _
    prog-eq6 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ []) _)

    len-prefix-6 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ []) ≡ length prefix +ℕ 6
    len-prefix-6 = List-length-++ prefix

    fetch6 : fetch prog (length prefix +ℕ 6) ≡ just i6
    fetch6 = subst₂ (λ p n → fetch p n ≡ just i6) (sym prog-eq6) len-prefix-6
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ []) i6 _)

    -- For the end label, we need fetch at pc s7 = prefix + 18 + len-f
    -- The curry code before the end label is 18 + len-f instructions
    curry-before-end-label : Program
    curry-before-end-label =
      i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷  -- 7 closure setup instructions
      label 7 ∷                              -- thunk entry
      addi sp sp neg24 ∷                     -- thunk setup (allocate 24 bytes)
      sd s2 (+ 16) sp ∷                      -- save frame pointer
      mv s2 sp ∷                             -- set frame pointer
      sd s0 (+ 0) sp ∷                       -- store env
      sd a0 (+ 8) sp ∷                       -- store arg
      mv a0 sp ∷                             -- a0 = pair
      compile-riscv f ++                     -- inner function
      mv sp s2 ∷                             -- cleanup: restore sp
      ld s2 (+ 16) sp ∷                      -- cleanup: restore s2
      addi sp sp (+ 24) ∷                    -- cleanup: deallocate
      ret ∷ []                               -- return

    len-curry-before : length curry-before-end-label ≡ 18 +ℕ len-f
    len-curry-before = begin
      length curry-before-end-label
        ≡⟨ refl ⟩
      length (i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷
              label 7 ∷ addi sp sp neg24 ∷
              sd s2 (+ 16) sp ∷ mv s2 sp ∷
              sd s0 (+ 0) sp ∷ sd a0 (+ 8) sp ∷ mv a0 sp ∷
              compile-riscv f ++
              mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ [])
        ≡⟨ refl ⟩
      14 +ℕ length (compile-riscv f ++ mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ [])
        ≡⟨ cong (14 +ℕ_) (List-length-++ (compile-riscv f)) ⟩
      14 +ℕ (length (compile-riscv f) +ℕ 4)
        ≡⟨ cong (λ z → 14 +ℕ (z +ℕ 4)) (compile-length-correct f) ⟩
      14 +ℕ (len-f +ℕ 4)
        ≡⟨ +-assoc 14 len-f 4 ⟩
      (14 +ℕ len-f) +ℕ 4
        ≡⟨ cong (_+ℕ 4) (+-comm 14 len-f) ⟩
      (len-f +ℕ 14) +ℕ 4
        ≡⟨ +-assoc len-f 14 4 ⟩
      len-f +ℕ 18
        ≡⟨ +-comm len-f 18 ⟩
      18 +ℕ len-f
        ∎

    curry-split : compile-riscv (curry f) ≡ curry-before-end-label ++ i-end-label ∷ []
    curry-split = cong (λ rest → i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷
                                 label 7 ∷ addi sp sp neg24 ∷
                                 sd s2 (+ 16) sp ∷ mv s2 sp ∷
                                 sd s0 (+ 0) sp ∷ sd a0 (+ 8) sp ∷ mv a0 sp ∷ rest)
                       (sym (++-assoc (compile-riscv f)
                              (mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ [])
                              (i-end-label ∷ [])))

    prefix-to-end : Program
    prefix-to-end = prefix ++ curry-before-end-label

    len-prefix-to-end : length prefix-to-end ≡ length prefix +ℕ 18 +ℕ len-f
    len-prefix-to-end = trans (List-length-++ prefix)
                         (trans (cong (length prefix +ℕ_) len-curry-before)
                                (sym (+-assoc (length prefix) 18 len-f)))

    prog-eq-for-fetch7 : prog ≡ prefix-to-end ++ i-end-label ∷ suffix
    prog-eq-for-fetch7 = begin
      prog
        ≡⟨ refl ⟩
      prefix ++ compile-riscv (curry f) ++ suffix
        ≡⟨ cong (λ z → prefix ++ z ++ suffix) curry-split ⟩
      prefix ++ (curry-before-end-label ++ i-end-label ∷ []) ++ suffix
        ≡⟨ cong (prefix ++_) (++-assoc curry-before-end-label (i-end-label ∷ []) suffix) ⟩
      prefix ++ curry-before-end-label ++ (i-end-label ∷ [] ++ suffix)
        ≡⟨ sym (++-assoc prefix curry-before-end-label (i-end-label ∷ suffix)) ⟩
      (prefix ++ curry-before-end-label) ++ i-end-label ∷ suffix
        ≡⟨ refl ⟩
      prefix-to-end ++ i-end-label ∷ suffix
        ∎

    fetch7 : fetch prog (length prefix +ℕ 18 +ℕ len-f) ≡ just i-end-label
    fetch7 = subst₂ (λ p n → fetch p n ≡ just i-end-label) (sym prog-eq-for-fetch7) len-prefix-to-end
                    (fetch-at-prefix-end prefix-to-end i-end-label suffix)

    -- Step proofs
    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execAddiNeg prog s sp sp 15)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ length prefix +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execSd prog st1 a0 0 sp)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- auipc t0, 0 sets t0 = PC (instruction index)
    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execAuipc0 prog st2 t0)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execAddi prog st3 t0 t0 5)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    step4 : step prog st4 ≡ just st5
    step4 = trans (step-exec prog st4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (execSd prog st4 t0 8 sp)

    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (λ p → p +ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    step5 : step prog st5 ≡ just st6
    step5 = trans (step-exec prog st5 i5 h5 (subst (λ p → fetch prog p ≡ just i5) (sym pc5) fetch5))
                  (execMv prog st5 a0 sp)

    h6 : halted st6 ≡ false
    h6 = h-false

    pc6 : pc st6 ≡ length prefix +ℕ 6
    pc6 = trans (cong (λ p → p +ℕ 1) pc5) (+-assoc (length prefix) 5 1)

    step6 : step prog st6 ≡ just st7
    step6 = trans (step-exec prog st6 i6 h6 (subst (λ p → fetch prog p ≡ just i6) (sym pc6) fetch6))
                  (execJ prog st6 (12 +ℕ len-f))

    h7 : halted st7 ≡ false
    h7 = h-false

    pc7-correct : pc st7 ≡ length prefix +ℕ 18 +ℕ len-f
    pc7-correct = begin
      pc st7
        ≡⟨ refl ⟩
      pc st6 +ℕ (12 +ℕ len-f)
        ≡⟨ cong (λ z → z +ℕ (12 +ℕ len-f)) pc6 ⟩
      (length prefix +ℕ 6) +ℕ (12 +ℕ len-f)
        ≡⟨ +-assoc (length prefix) 6 (12 +ℕ len-f) ⟩
      length prefix +ℕ (6 +ℕ (12 +ℕ len-f))
        ≡⟨ cong (length prefix +ℕ_) (sym (+-assoc 6 12 len-f)) ⟩
      length prefix +ℕ ((6 +ℕ 12) +ℕ len-f)
        ≡⟨ cong (length prefix +ℕ_) refl ⟩
      length prefix +ℕ (18 +ℕ len-f)
        ≡⟨ sym (+-assoc (length prefix) 18 len-f) ⟩
      length prefix +ℕ 18 +ℕ len-f
        ∎

    step7 : step prog st7 ≡ just st8
    step7 = trans (step-exec prog st7 i-end-label h7 (subst (λ p → fetch prog p ≡ just i-end-label) (sym pc7-correct) fetch7))
                  (execLabel prog st7 (18 +ℕ len-f))

    h8 : halted st8 ≡ false
    h8 = h-false

    pc8 : pc st8 ≡ length prefix +ℕ compile-length (curry f)
    pc8 = begin
      pc st8
        ≡⟨ refl ⟩
      pc st7 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc7-correct ⟩
      (length prefix +ℕ 18 +ℕ len-f) +ℕ 1
        ≡⟨ +-assoc (length prefix +ℕ 18) len-f 1 ⟩
      (length prefix +ℕ 18) +ℕ (len-f +ℕ 1)
        ≡⟨ cong ((length prefix +ℕ 18) +ℕ_) (+-comm len-f 1) ⟩
      (length prefix +ℕ 18) +ℕ (1 +ℕ len-f)
        ≡⟨ sym (+-assoc (length prefix +ℕ 18) 1 len-f) ⟩
      ((length prefix +ℕ 18) +ℕ 1) +ℕ len-f
        ≡⟨ cong (_+ℕ len-f) (+-assoc (length prefix) 18 1) ⟩
      (length prefix +ℕ 19) +ℕ len-f
        ≡⟨ +-assoc (length prefix) 19 len-f ⟩
      length prefix +ℕ (19 +ℕ len-f)
        ≡⟨ refl ⟩
      length prefix +ℕ compile-length (curry f)
        ∎

    -- Build Star using combinators
    star-all : Star prog s st8
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               ⟨ h5 , step5 ⟩◅
               ⟨ h6 , step6 ⟩◅
               ⟨ h7 , step7 ⟩◅
               refl*

    -- Final state is st8
    s-final : State
    s-final = st8

    h-final : halted s-final ≡ false
    h-final = h8

    pc-final : pc s-final ≡ length prefix +ℕ compile-length (curry f)
    pc-final = pc8

    -- Register preservation through states (register s1 is callee-saved)
    -- curry touches: sp (addi), memory (sd), t0 (auipc, addi), a0 (mv), pc (j, label)
    -- Register s1 is NOT touched by any of these instructions

    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-st1 = readReg-writeReg-sp-s1 (regs s) new-sp

    s1-st2 : readReg (regs st2) s1 ≡ readReg (regs s) s1
    s1-st2 = s1-st1  -- memory write doesn't change regs

    s1-st3 : readReg (regs st3) s1 ≡ readReg (regs s) s1
    s1-st3 = trans (readReg-writeReg-t0-s1 (regs st2) (pc st2)) s1-st2

    s1-st4 : readReg (regs st4) s1 ≡ readReg (regs s) s1
    s1-st4 = trans (readReg-writeReg-t0-s1 (regs st3) (readReg (regs st3) t0 +ℕ 5)) s1-st3

    s1-st5 : readReg (regs st5) s1 ≡ readReg (regs s) s1
    s1-st5 = s1-st4  -- memory write doesn't change regs

    s1-st6 : readReg (regs st6) s1 ≡ readReg (regs s) s1
    s1-st6 = trans (readReg-writeReg-a0-s1 (regs st5) (readReg (regs st5) sp)) s1-st5

    s1-st7 : readReg (regs st7) s1 ≡ readReg (regs s) s1
    s1-st7 = s1-st6  -- j only changes pc

    s1-st8 : readReg (regs st8) s1 ≡ readReg (regs s) s1
    s1-st8 = s1-st7  -- label only changes pc

    s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
    s1-final = s1-st8

    -- Track s2 through states (none of the curry instructions modify s2)
    s2-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-st1 = readReg-writeReg-sp-s2 (regs s) new-sp

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs s) s2
    s2-st2 = s2-st1  -- memory write doesn't change regs

    s2-st3 : readReg (regs st3) s2 ≡ readReg (regs s) s2
    s2-st3 = trans (readReg-writeReg-t0-s2 (regs st2) (pc st2)) s2-st2

    s2-st4 : readReg (regs st4) s2 ≡ readReg (regs s) s2
    s2-st4 = trans (readReg-writeReg-t0-s2 (regs st3) (readReg (regs st3) t0 +ℕ 5)) s2-st3

    s2-st5 : readReg (regs st5) s2 ≡ readReg (regs s) s2
    s2-st5 = s2-st4  -- memory write doesn't change regs

    s2-st6 : readReg (regs st6) s2 ≡ readReg (regs s) s2
    s2-st6 = trans (readReg-writeReg-a0-s2 (regs st5) (readReg (regs st5) sp)) s2-st5

    s2-st7 : readReg (regs st7) s2 ≡ readReg (regs s) s2
    s2-st7 = s2-st6  -- j only changes pc

    s2-st8 : readReg (regs st8) s2 ≡ readReg (regs s) s2
    s2-st8 = s2-st7  -- label only changes pc

    s2-final : readReg (regs s-final) s2 ≡ readReg (regs s) s2
    s2-final = s2-st8

    -- Track ra through states (none of the curry instructions modify ra)
    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-sp-ra (regs s) new-sp

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = ra-st1  -- memory write doesn't change regs

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs s) ra
    ra-st3 = trans (readReg-writeReg-t0-ra (regs st2) (pc st2)) ra-st2

    ra-st4 : readReg (regs st4) ra ≡ readReg (regs s) ra
    ra-st4 = trans (readReg-writeReg-t0-ra (regs st3) (readReg (regs st3) t0 +ℕ 5)) ra-st3

    ra-st5 : readReg (regs st5) ra ≡ readReg (regs s) ra
    ra-st5 = ra-st4  -- memory write doesn't change regs

    ra-st6 : readReg (regs st6) ra ≡ readReg (regs s) ra
    ra-st6 = trans (readReg-writeReg-a0-ra (regs st5) (readReg (regs st5) sp)) ra-st5

    ra-st7 : readReg (regs st7) ra ≡ readReg (regs s) ra
    ra-st7 = ra-st6  -- j only changes pc

    ra-st8 : readReg (regs st8) ra ≡ readReg (regs s) ra
    ra-st8 = ra-st7  -- label only changes pc

    ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
    ra-final = ra-st8

    -- Track a0 through states
    -- Only st6 modifies a0 (mv a0 sp)

    a0-st1 : readReg (regs st1) a0 ≡ orig-a0
    a0-st1 = readReg-writeReg-sp-a0 (regs s) new-sp

    a0-st2 : readReg (regs st2) a0 ≡ orig-a0
    a0-st2 = a0-st1

    a0-st3 : readReg (regs st3) a0 ≡ orig-a0
    a0-st3 = trans (readReg-writeReg-t0-a0 (regs st2) (pc st2)) a0-st2

    a0-st4 : readReg (regs st4) a0 ≡ orig-a0
    a0-st4 = trans (readReg-writeReg-t0-a0 (regs st3) (readReg (regs st3) t0 +ℕ 5)) a0-st3

    a0-st5 : readReg (regs st5) a0 ≡ orig-a0
    a0-st5 = a0-st4

    -- Track sp through states (only st1 modifies sp)
    sp-st1 : readReg (regs st1) sp ≡ new-sp
    sp-st1 = readReg-writeReg-same (regs s) sp new-sp (λ ())

    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = sp-st1

    sp-st3 : readReg (regs st3) sp ≡ new-sp
    sp-st3 = trans (readReg-writeReg-t0-sp (regs st2) (pc st2)) sp-st2

    sp-st4 : readReg (regs st4) sp ≡ new-sp
    sp-st4 = trans (readReg-writeReg-t0-sp (regs st3) (readReg (regs st3) t0 +ℕ 5)) sp-st3

    sp-st5 : readReg (regs st5) sp ≡ new-sp
    sp-st5 = sp-st4

    sp-st6 : readReg (regs st6) sp ≡ new-sp
    sp-st6 = trans (readReg-writeReg-a0-sp (regs st5) (readReg (regs st5) sp)) sp-st5

    sp-st7 : readReg (regs st7) sp ≡ new-sp
    sp-st7 = sp-st6  -- j only changes pc

    sp-st8 : readReg (regs st8) sp ≡ new-sp
    sp-st8 = sp-st7  -- label only changes pc

    -- a0 in st6 = sp in st5 = new-sp
    a0-st6 : readReg (regs st6) a0 ≡ new-sp
    a0-st6 = trans (readReg-writeReg-same (regs st5) a0 (readReg (regs st5) sp) (λ ())) sp-st5

    a0-st7 : readReg (regs st7) a0 ≡ new-sp
    a0-st7 = a0-st6

    a0-st8 : readReg (regs st8) a0 ≡ new-sp
    a0-st8 = a0-st7

    -- Memory tracking for encode-closure-construct
    -- Step 1 (sd a0 0(sp)) stores encode x at new-sp
    -- Step 4 (sd t0 8(sp)) stores code-ptr at new-sp + 8

    -- In st1: a0 is unchanged (only sp modified)
    a0-st1-eq : readReg (regs st1) a0 ≡ encode x
    a0-st1-eq = trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq

    -- In st2: memory at new-sp = encode x
    -- st2 = record st1 { memory = writeMem (memory st1) (readReg (regs st1) sp +ℕ 0) (readReg (regs st1) a0) }
    -- sp in st1 = new-sp, a0 in st1 = encode x
    write-addr-st2 : readReg (regs st1) sp +ℕ 0 ≡ new-sp
    write-addr-st2 = trans (cong (_+ℕ 0) sp-st1) (+-identityʳ new-sp)

    -- After the write, reading from new-sp gives the value we wrote
    mem-at-new-sp-st2 : readMem (memory st2) new-sp ≡ just (encode x)
    mem-at-new-sp-st2 =
      let write-addr = readReg (regs st1) sp +ℕ 0
          write-val = readReg (regs st1) a0
          -- memory st2 = writeMem (memory st1) write-addr write-val
          -- readMem at write-addr gives write-val
          read-at-write : readMem (writeMem (memory st1) write-addr write-val) write-addr ≡ just write-val
          read-at-write = readMem-writeMem-same (memory st1) write-addr write-val
          -- write-addr = new-sp, so reading at new-sp gives write-val
          read-at-new-sp : readMem (writeMem (memory st1) write-addr write-val) new-sp ≡ just write-val
          read-at-new-sp = subst (λ a → readMem (writeMem (memory st1) write-addr write-val) a ≡ just write-val)
                                 write-addr-st2 read-at-write
          -- write-val = encode x
          val-eq : write-val ≡ encode x
          val-eq = a0-st1-eq
      in trans read-at-new-sp (cong just val-eq)

    -- st3, st4 don't modify memory (only regs)
    mem-at-new-sp-st3 : readMem (memory st3) new-sp ≡ just (encode x)
    mem-at-new-sp-st3 = mem-at-new-sp-st2

    mem-at-new-sp-st4 : readMem (memory st4) new-sp ≡ just (encode x)
    mem-at-new-sp-st4 = mem-at-new-sp-st3

    -- st5 writes at new-sp + 8, which is ≢ new-sp
    new-sp≢new-sp+8 : new-sp ≢ new-sp +ℕ 8
    new-sp≢new-sp+8 = n≢n+suc new-sp 7

    mem-at-new-sp-st5 : readMem (memory st5) new-sp ≡ just (encode x)
    mem-at-new-sp-st5 = trans (readMem-writeMem-diff (memory st4) (readReg (regs st4) sp +ℕ 8) new-sp
                                                     (readReg (regs st4) t0)
                                                     (λ eq → new-sp≢new-sp+8 (trans (sym eq) (cong (_+ℕ 8) sp-st4))))
                              mem-at-new-sp-st4

    -- st6, st7, st8 don't modify memory
    mem-at-new-sp-final : readMem (memory s-final) new-sp ≡ just (encode x)
    mem-at-new-sp-final = mem-at-new-sp-st5

    -- Use encode-closure-construct axiom
    encode-curry-result : new-sp ≡ encode {B ⇒ C} (eval {_} {A} {B ⇒ C} (curry f) x)
    encode-curry-result = encode-closure-construct f x new-sp (memory s-final) mem-at-new-sp-final

    -- Prove a0 = encode (eval (curry f) x)
    a0-final : readReg (regs s-final) a0 ≡ encode {B ⇒ C} (eval (curry f) x)
    a0-final = trans a0-st8 encode-curry-result

    -- SP tracking: curry allocates 16 bytes on stack (sp -= 16)
    -- With ir-sp-delta = 16, we need: new-sp + 16 ≡ orig-sp
    -- This is (orig-sp ∸ 16) + 16 ≡ orig-sp, which holds when 16 ≤ orig-sp

    -- Stack space: derived from sp-bound (24 ≤ orig-sp) since 16 ≤ 24
    16≤24 : 16 ≤ 24
    16≤24 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))

    stack-space : 16 ≤ orig-sp
    stack-space = ≤-trans 16≤24 sp-bound

    sp-final : readReg (regs s-final) sp +ℕ 16 ≡ readReg (regs s) sp
    sp-final = trans (cong (_+ℕ 16) sp-st8) (m∸n+n≡m stack-space)

    -- Memory preservation: curry writes to its own stack frame (sp-16..sp),
    -- but should preserve memory at caller's frame (original sp and above)
    --
    -- Memory changes:
    --   st2 writes at new-sp (= orig-sp ∸ 16)
    --   st5 writes at new-sp + 8
    -- Both are below orig-sp, so memory at orig-sp and above is preserved.

    -- Helper: 0 < 16 and 8 < 16 for the monus lemmas
    0<16 : 0 < 16
    0<16 = z<s

    8<16 : 8 < 16
    8<16 = s<s (s<s (s<s (s<s (s<s (s<s (s<s (s<s z<s)))))))

    -- Address disjointness: new-sp and new-sp+8 are both disjoint from orig-sp+k
    -- Since new-sp = orig-sp ∸ 16, and 16 > 0, new-sp < orig-sp ≤ orig-sp + k

    new-sp≢orig-sp : new-sp ≢ orig-sp
    new-sp≢orig-sp = monus-neq-self 16 orig-sp stack-space 0<16

    new-sp≢orig-sp+8 : new-sp ≢ (orig-sp +ℕ 8)
    new-sp≢orig-sp+8 = monus-neq-plus 16 orig-sp 8 stack-space 0<16

    new-sp≢orig-sp+16 : new-sp ≢ (orig-sp +ℕ 16)
    new-sp≢orig-sp+16 = monus-neq-plus 16 orig-sp 16 stack-space 0<16

    new-sp≢orig-sp+24 : new-sp ≢ (orig-sp +ℕ 24)
    new-sp≢orig-sp+24 = monus-neq-plus 16 orig-sp 24 stack-space 0<16

    -- new-sp + 8 disjointness (8 < 16, so we can use monus-plus-neq-plus)
    new-sp+8≢orig-sp : (new-sp +ℕ 8) ≢ orig-sp
    new-sp+8≢orig-sp eq = monus-plus-neq-plus 16 orig-sp 8 0 stack-space 8<16 (trans eq (sym (+-identityʳ orig-sp)))

    new-sp+8≢orig-sp+8 : (new-sp +ℕ 8) ≢ (orig-sp +ℕ 8)
    new-sp+8≢orig-sp+8 = monus-plus-neq-plus 16 orig-sp 8 8 stack-space 8<16

    new-sp+8≢orig-sp+16 : (new-sp +ℕ 8) ≢ (orig-sp +ℕ 16)
    new-sp+8≢orig-sp+16 = monus-plus-neq-plus 16 orig-sp 8 16 stack-space 8<16

    new-sp+8≢orig-sp+24 : (new-sp +ℕ 8) ≢ (orig-sp +ℕ 24)
    new-sp+8≢orig-sp+24 = monus-plus-neq-plus 16 orig-sp 8 24 stack-space 8<16

    -- Memory tracking through states
    -- st1: only changes regs, memory preserved
    mem-st1-eq : memory st1 ≡ memory s
    mem-st1-eq = refl

    -- st2 writes at new-sp, disjoint from orig-sp and above
    mem-st2-at-orig-sp : readMem (memory st2) orig-sp ≡ readMem (memory s) orig-sp
    mem-st2-at-orig-sp =
      trans (readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 0) orig-sp
              (readReg (regs st1) a0)
              (λ eq → new-sp≢orig-sp (trans (sym (trans (cong (_+ℕ 0) sp-st1) (+-identityʳ new-sp))) eq)))
            refl

    mem-st2-at-orig-sp+8 : readMem (memory st2) (orig-sp +ℕ 8) ≡ readMem (memory s) (orig-sp +ℕ 8)
    mem-st2-at-orig-sp+8 =
      trans (readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 0) (orig-sp +ℕ 8)
              (readReg (regs st1) a0)
              (λ eq → new-sp≢orig-sp+8 (trans (sym (trans (cong (_+ℕ 0) sp-st1) (+-identityʳ new-sp))) eq)))
            refl

    mem-st2-at-orig-sp+16 : readMem (memory st2) (orig-sp +ℕ 16) ≡ readMem (memory s) (orig-sp +ℕ 16)
    mem-st2-at-orig-sp+16 =
      trans (readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 0) (orig-sp +ℕ 16)
              (readReg (regs st1) a0)
              (λ eq → new-sp≢orig-sp+16 (trans (sym (trans (cong (_+ℕ 0) sp-st1) (+-identityʳ new-sp))) eq)))
            refl

    mem-st2-at-orig-sp+24 : readMem (memory st2) (orig-sp +ℕ 24) ≡ readMem (memory s) (orig-sp +ℕ 24)
    mem-st2-at-orig-sp+24 =
      trans (readMem-writeMem-diff (memory st1) (readReg (regs st1) sp +ℕ 0) (orig-sp +ℕ 24)
              (readReg (regs st1) a0)
              (λ eq → new-sp≢orig-sp+24 (trans (sym (trans (cong (_+ℕ 0) sp-st1) (+-identityʳ new-sp))) eq)))
            refl

    -- st3, st4: only change regs, memory preserved
    mem-st3-eq : memory st3 ≡ memory st2
    mem-st3-eq = refl

    mem-st4-eq : memory st4 ≡ memory st2
    mem-st4-eq = refl

    -- st5 writes at new-sp + 8, disjoint from orig-sp and above
    mem-st5-at-orig-sp : readMem (memory st5) orig-sp ≡ readMem (memory s) orig-sp
    mem-st5-at-orig-sp =
      trans (readMem-writeMem-diff (memory st4) (readReg (regs st4) sp +ℕ 8) orig-sp
              (readReg (regs st4) t0)
              (λ eq → new-sp+8≢orig-sp (trans (cong (_+ℕ 8) sp-st4) eq)))
            mem-st2-at-orig-sp

    mem-st5-at-orig-sp+8 : readMem (memory st5) (orig-sp +ℕ 8) ≡ readMem (memory s) (orig-sp +ℕ 8)
    mem-st5-at-orig-sp+8 =
      trans (readMem-writeMem-diff (memory st4) (readReg (regs st4) sp +ℕ 8) (orig-sp +ℕ 8)
              (readReg (regs st4) t0)
              (λ eq → new-sp+8≢orig-sp+8 (trans (cong (_+ℕ 8) sp-st4) eq)))
            mem-st2-at-orig-sp+8

    mem-st5-at-orig-sp+16 : readMem (memory st5) (orig-sp +ℕ 16) ≡ readMem (memory s) (orig-sp +ℕ 16)
    mem-st5-at-orig-sp+16 =
      trans (readMem-writeMem-diff (memory st4) (readReg (regs st4) sp +ℕ 8) (orig-sp +ℕ 16)
              (readReg (regs st4) t0)
              (λ eq → new-sp+8≢orig-sp+16 (trans (cong (_+ℕ 8) sp-st4) eq)))
            mem-st2-at-orig-sp+16

    mem-st5-at-orig-sp+24 : readMem (memory st5) (orig-sp +ℕ 24) ≡ readMem (memory s) (orig-sp +ℕ 24)
    mem-st5-at-orig-sp+24 =
      trans (readMem-writeMem-diff (memory st4) (readReg (regs st4) sp +ℕ 8) (orig-sp +ℕ 24)
              (readReg (regs st4) t0)
              (λ eq → new-sp+8≢orig-sp+24 (trans (cong (_+ℕ 8) sp-st4) eq)))
            mem-st2-at-orig-sp+24

    -- st6, st7, st8: only change regs or pc, memory preserved
    mem-final-eq : memory s-final ≡ memory st5
    mem-final-eq = refl

    -- Final memory preservation proofs
    mem-sp-final : readMem (memory s-final) (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
    mem-sp-final = mem-st5-at-orig-sp

    mem-sp+8-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
    mem-sp+8-final = mem-st5-at-orig-sp+8

    mem-sp+16-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)
    mem-sp+16-final = mem-st5-at-orig-sp+16

    mem-sp+24-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 24) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 24)
    mem-sp+24-final = mem-st5-at-orig-sp+24
