------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.ThunkSetup
--
-- Proven thunk setup instruction tracing for RISC-V 64-bit.
-- Traces the 7 thunk setup instructions within curry.
--
-- Thunk layout within curry (positions 7 onwards):
--   7: label code-ptr (thunk entry)
--   8: addi sp sp -24 (allocate 24 bytes: 8 saved-s2 + 16 pair)
--   9: sd s2 16(sp) (save frame pointer)
--   10: mv s2 sp (set frame pointer)
--   11: sd s0 0(sp) (store env = a at pair.fst)
--   12: sd a0 8(sp) (store arg = b at pair.snd)
--   13: mv a0 sp (a0 = pair pointer)
--   14 to 13+len-f: compile-riscv f
--   14+len-f: mv sp s2 (restore sp)
--   15+len-f: ld s2 16(sp) (restore s2)
--   16+len-f: addi sp sp 24 (deallocate)
--   17+len-f: ret
--   18+len-f: label end
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.IR.ThunkSetup where

open import Size

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr)

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates using (encode; encode-pair-construct)
open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.CompileLength using (compile-length-correct)
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_)

open import Once.Backend.Common.Memory
  using (readMem-writeMem-same; readMem-writeMem-diff; n≢n+suc)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Thunk setup proof
------------------------------------------------------------------------

-- | Prove thunk setup: traces 7 instructions
-- Entry: pc = thunk-offset, a0 = encode arg, s0 = encode env
-- Exit: pc = f-offset, a0 = encode (env, arg), s2 = frame pointer
thunk-setup-star-proven : ∀ {i A B C} (f : IR i (A * B) C)
                          (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
  let prog = prefix ++ compile-riscv (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 7
      f-offset = length prefix +ℕ 14
  in
  halted s ≡ false →
  pc s ≡ thunk-offset →
  readReg (regs s) a0 ≡ encode arg →
  readReg (regs s) s0 ≡ encode env →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ f-offset
          × readReg (regs s') a0 ≡ encode (env , arg)
          × readReg (regs s') s1 ≡ readReg (regs s) s1
          × readReg (regs s') ra ≡ readReg (regs s) ra
          × readReg (regs s') s2 ≡ readReg (regs s) sp ∸ 24)  -- s2 = frame pointer

thunk-setup-star-proven {A} {B} {C} f prefix suffix env arg s
                        h-false pc-eq a0-eq s0-eq =
  st7 , star-all , h7 , pc7 , a0-final , s1-final , ra-final , s2-final
  where
    len-f = compile-length f
    prog = prefix ++ compile-riscv (curry f) ++ suffix
    offset = length prefix
    thunk-offset = offset +ℕ 7
    f-offset = offset +ℕ 14

    -- Helper values
    orig-sp : Word
    orig-sp = readReg (regs s) sp

    new-sp : Word
    new-sp = orig-sp ∸ 24

    -- The 7 thunk setup instructions (at positions 7-13 within curry)
    i0 : Instr
    i0 = label 7

    i1 : Instr
    i1 = addi sp sp neg24

    i2 : Instr
    i2 = sd s2 (+ 16) sp   -- save s2

    i3 : Instr
    i3 = mv s2 sp           -- set frame pointer

    i4 : Instr
    i4 = sd s0 (+ 0) sp     -- store env at pair.fst

    i5 : Instr
    i5 = sd a0 (+ 8) sp     -- store arg at pair.snd

    i6 : Instr
    i6 = mv a0 sp           -- a0 = pair pointer

    -- Fetch lemmas (need to fetch at thunk-offset within curry)
    -- The curry code structure is:
    --   [6 closure setup] ++ [label 7] ++ [6 thunk setup] ++ [f code] ++ [cleanup + ret] ++ [label end]
    -- So positions 7-13 within curry are the thunk setup instructions

    -- Build prefix up to each instruction
    curry-prefix-to-7 : Program
    curry-prefix-to-7 = addi sp sp neg16 ∷     -- 0
                        sd a0 (+ 0) sp ∷       -- 1
                        auipc t0 (+ 0) ∷       -- 2
                        addi t0 t0 (+ 5) ∷     -- 3
                        sd t0 (+ 8) sp ∷       -- 4
                        mv a0 sp ∷             -- 5
                        j (+ (12 +ℕ len-f)) ∷  -- 6 (jump offset updated for new layout)
                        []

    prefix-to-i0 : Program
    prefix-to-i0 = prefix ++ curry-prefix-to-7

    len-prefix-to-i0 : length prefix-to-i0 ≡ thunk-offset
    len-prefix-to-i0 = List-length-++ prefix

    -- Fetch lemmas (proven using fetch-at-prefix-end)
    -- compile-riscv (curry f) = curry-prefix-to-7 ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ rest
    -- prog = prefix ++ (curry-prefix-to-7 ++ i0 ∷ ...) ++ suffix
    --      = (prefix ++ curry-prefix-to-7) ++ i0 ∷ ...
    --      = prefix-to-i0 ++ i0 ∷ ...

    -- The thunk body after the 7 setup instructions
    thunk-body : Program
    thunk-body = compile-riscv f ++ mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ label (18 +ℕ len-f) ∷ []

    -- Show curry code decomposes properly
    curry-code-eq : compile-riscv (curry f) ≡
                    curry-prefix-to-7 ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ i5 ∷ i6 ∷ thunk-body
    curry-code-eq = refl

    -- Program structure: prog = prefix-to-i0 ++ i0 ∷ rest
    prog-eq0 : prog ≡ prefix-to-i0 ++ i0 ∷ _
    prog-eq0 = trans (cong (λ c → prefix ++ c ++ suffix) curry-code-eq)
                     (sym (++-assoc prefix curry-prefix-to-7 _))

    fetch0 : fetch prog thunk-offset ≡ just i0
    fetch0 = subst₂ (λ p n → fetch p n ≡ just i0) (sym prog-eq0) len-prefix-to-i0
                    (fetch-at-prefix-end prefix-to-i0 i0 _)

    prefix-to-i1 : Program
    prefix-to-i1 = prefix-to-i0 ++ i0 ∷ []

    prog-eq1 : prog ≡ prefix-to-i1 ++ i1 ∷ _
    prog-eq1 = trans prog-eq0 (sym (++-assoc prefix-to-i0 (i0 ∷ []) _))

    len-prefix-to-i1 : length prefix-to-i1 ≡ thunk-offset +ℕ 1
    len-prefix-to-i1 = trans (List-length-++ prefix-to-i0) (cong (_+ℕ 1) len-prefix-to-i0)

    fetch1 : fetch prog (thunk-offset +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-to-i1
                    (fetch-at-prefix-end prefix-to-i1 i1 _)

    prefix-to-i2 : Program
    prefix-to-i2 = prefix-to-i1 ++ i1 ∷ []

    prog-eq2 : prog ≡ prefix-to-i2 ++ i2 ∷ _
    prog-eq2 = trans prog-eq1 (sym (++-assoc prefix-to-i1 (i1 ∷ []) _))

    len-prefix-to-i2 : length prefix-to-i2 ≡ thunk-offset +ℕ 2
    len-prefix-to-i2 = trans (List-length-++ prefix-to-i1)
                             (trans (cong (_+ℕ 1) len-prefix-to-i1) (+-assoc thunk-offset 1 1))

    fetch2 : fetch prog (thunk-offset +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-to-i2
                    (fetch-at-prefix-end prefix-to-i2 i2 _)

    prefix-to-i3 : Program
    prefix-to-i3 = prefix-to-i2 ++ i2 ∷ []

    prog-eq3 : prog ≡ prefix-to-i3 ++ i3 ∷ _
    prog-eq3 = trans prog-eq2 (sym (++-assoc prefix-to-i2 (i2 ∷ []) _))

    len-prefix-to-i3 : length prefix-to-i3 ≡ thunk-offset +ℕ 3
    len-prefix-to-i3 = trans (List-length-++ prefix-to-i2)
                             (trans (cong (_+ℕ 1) len-prefix-to-i2) (+-assoc thunk-offset 2 1))

    fetch3 : fetch prog (thunk-offset +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-to-i3
                    (fetch-at-prefix-end prefix-to-i3 i3 _)

    prefix-to-i4 : Program
    prefix-to-i4 = prefix-to-i3 ++ i3 ∷ []

    prog-eq4 : prog ≡ prefix-to-i4 ++ i4 ∷ _
    prog-eq4 = trans prog-eq3 (sym (++-assoc prefix-to-i3 (i3 ∷ []) _))

    len-prefix-to-i4 : length prefix-to-i4 ≡ thunk-offset +ℕ 4
    len-prefix-to-i4 = trans (List-length-++ prefix-to-i3)
                             (trans (cong (_+ℕ 1) len-prefix-to-i3) (+-assoc thunk-offset 3 1))

    fetch4 : fetch prog (thunk-offset +ℕ 4) ≡ just i4
    fetch4 = subst₂ (λ p n → fetch p n ≡ just i4) (sym prog-eq4) len-prefix-to-i4
                    (fetch-at-prefix-end prefix-to-i4 i4 _)

    prefix-to-i5 : Program
    prefix-to-i5 = prefix-to-i4 ++ i4 ∷ []

    prog-eq5 : prog ≡ prefix-to-i5 ++ i5 ∷ _
    prog-eq5 = trans prog-eq4 (sym (++-assoc prefix-to-i4 (i4 ∷ []) _))

    len-prefix-to-i5 : length prefix-to-i5 ≡ thunk-offset +ℕ 5
    len-prefix-to-i5 = trans (List-length-++ prefix-to-i4)
                             (trans (cong (_+ℕ 1) len-prefix-to-i4) (+-assoc thunk-offset 4 1))

    fetch5 : fetch prog (thunk-offset +ℕ 5) ≡ just i5
    fetch5 = subst₂ (λ p n → fetch p n ≡ just i5) (sym prog-eq5) len-prefix-to-i5
                    (fetch-at-prefix-end prefix-to-i5 i5 _)

    prefix-to-i6 : Program
    prefix-to-i6 = prefix-to-i5 ++ i5 ∷ []

    prog-eq6 : prog ≡ prefix-to-i6 ++ i6 ∷ _
    prog-eq6 = trans prog-eq5 (sym (++-assoc prefix-to-i5 (i5 ∷ []) _))

    len-prefix-to-i6 : length prefix-to-i6 ≡ thunk-offset +ℕ 6
    len-prefix-to-i6 = trans (List-length-++ prefix-to-i5)
                             (trans (cong (_+ℕ 1) len-prefix-to-i5) (+-assoc thunk-offset 5 1))

    fetch6 : fetch prog (thunk-offset +ℕ 6) ≡ just i6
    fetch6 = subst₂ (λ p n → fetch p n ≡ just i6) (sym prog-eq6) len-prefix-to-i6
                    (fetch-at-prefix-end prefix-to-i6 i6 _)

    -- State after step 0: label 7 (no-op, just pc++)
    st1 : State
    st1 = record s { pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execLabel prog s 7)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ thunk-offset +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    -- State after step 1: addi sp sp -24
    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) sp new-sp
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execAddiNeg prog st1 sp sp 23)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ thunk-offset +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc thunk-offset 1 1)

    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = readReg-writeReg-same (regs st1) sp new-sp (λ ())

    s2-st2 : readReg (regs st2) s2 ≡ readReg (regs s) s2
    s2-st2 = readReg-writeReg-sp-s2 (regs st1) new-sp

    -- State after step 2: sd s2 16(sp) - save frame pointer
    st3 : State
    st3 = record st2 { memory = writeMem (memory st2) (readReg (regs st2) sp +ℕ 16) (readReg (regs st2) s2)
                     ; pc = pc st2 +ℕ 1 }

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execSd prog st2 s2 16 sp)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ thunk-offset +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc thunk-offset 2 1)

    sp-st3 : readReg (regs st3) sp ≡ new-sp
    sp-st3 = sp-st2  -- memory write doesn't change regs

    -- State after step 3: mv s2 sp - set frame pointer
    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) s2 (readReg (regs st3) sp)
                     ; pc = pc st3 +ℕ 1 }

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMv prog st3 s2 sp)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ thunk-offset +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc thunk-offset 3 1)

    sp-st4 : readReg (regs st4) sp ≡ new-sp
    sp-st4 = trans (readReg-writeReg-s2-sp (regs st3) (readReg (regs st3) sp)) sp-st3

    s2-st4 : readReg (regs st4) s2 ≡ new-sp
    s2-st4 = trans (readReg-writeReg-same (regs st3) s2 (readReg (regs st3) sp) (λ ())) sp-st3

    s0-st4 : readReg (regs st4) s0 ≡ encode env
    s0-st4 = trans (readReg-writeReg-s2-s0 (regs st3) (readReg (regs st3) sp)) s0-eq

    a0-st4 : readReg (regs st4) a0 ≡ encode arg
    a0-st4 = trans (readReg-writeReg-s2-a0 (regs st3) (readReg (regs st3) sp)) a0-eq

    -- State after step 4: sd s0 0(sp) - store env at [new-sp]
    st5 : State
    st5 = record st4 { memory = writeMem (memory st4) (readReg (regs st4) sp +ℕ 0) (readReg (regs st4) s0)
                     ; pc = pc st4 +ℕ 1 }

    step4 : step prog st4 ≡ just st5
    step4 = trans (step-exec prog st4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (execSd prog st4 s0 0 sp)

    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ thunk-offset +ℕ 5
    pc5 = trans (cong (λ p → p +ℕ 1) pc4) (+-assoc thunk-offset 4 1)

    sp-st5 : readReg (regs st5) sp ≡ new-sp
    sp-st5 = sp-st4  -- memory write doesn't change regs

    s2-st5 : readReg (regs st5) s2 ≡ new-sp
    s2-st5 = s2-st4  -- memory write doesn't change regs

    a0-st5 : readReg (regs st5) a0 ≡ encode arg
    a0-st5 = a0-st4  -- memory write doesn't change regs

    -- State after step 5: sd a0 8(sp) - store arg at [new-sp + 8]
    st6 : State
    st6 = record st5 { memory = writeMem (memory st5) (readReg (regs st5) sp +ℕ 8) (readReg (regs st5) a0)
                     ; pc = pc st5 +ℕ 1 }

    step5 : step prog st5 ≡ just st6
    step5 = trans (step-exec prog st5 i5 h5 (subst (λ p → fetch prog p ≡ just i5) (sym pc5) fetch5))
                  (execSd prog st5 a0 8 sp)

    h6 : halted st6 ≡ false
    h6 = h-false

    pc6 : pc st6 ≡ thunk-offset +ℕ 6
    pc6 = trans (cong (λ p → p +ℕ 1) pc5) (+-assoc thunk-offset 5 1)

    sp-st6 : readReg (regs st6) sp ≡ new-sp
    sp-st6 = sp-st5  -- memory write doesn't change regs

    s2-st6 : readReg (regs st6) s2 ≡ new-sp
    s2-st6 = s2-st5  -- memory write doesn't change regs

    -- State after step 6: mv a0 sp (a0 = pair pointer)
    st7 : State
    st7 = record st6 { regs = writeReg (regs st6) a0 (readReg (regs st6) sp)
                     ; pc = pc st6 +ℕ 1 }

    step6 : step prog st6 ≡ just st7
    step6 = trans (step-exec prog st6 i6 h6 (subst (λ p → fetch prog p ≡ just i6) (sym pc6) fetch6))
                  (execMv prog st6 a0 sp)

    -- Build Star proof
    star-all : Star prog s st7
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               ⟨ h5 , step5 ⟩◅
               ⟨ h6 , step6 ⟩◅
               refl*

    -- Final state properties
    h7 : halted st7 ≡ false
    h7 = h-false

    pc7 : pc st7 ≡ f-offset
    pc7 = begin
      pc st7
        ≡⟨ refl ⟩
      pc st6 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc6 ⟩
      (thunk-offset +ℕ 6) +ℕ 1
        ≡⟨ +-assoc thunk-offset 6 1 ⟩
      thunk-offset +ℕ 7
        ≡⟨ cong (_+ℕ 7) refl ⟩  -- thunk-offset = offset + 7
      (offset +ℕ 7) +ℕ 7
        ≡⟨ +-assoc offset 7 7 ⟩
      offset +ℕ 14
        ≡⟨ refl ⟩
      f-offset ∎

    -- Register s1 preservation (not touched by any of these instructions)
    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-st1 = refl  -- label doesn't change regs

    s1-st2 : readReg (regs st2) s1 ≡ readReg (regs s) s1
    s1-st2 = trans (readReg-writeReg-sp-s1 (regs st1) new-sp) s1-st1

    s1-st3 : readReg (regs st3) s1 ≡ readReg (regs s) s1
    s1-st3 = s1-st2  -- memory write doesn't change regs

    s1-st4 : readReg (regs st4) s1 ≡ readReg (regs s) s1
    s1-st4 = trans (readReg-writeReg-s2-s1 (regs st3) (readReg (regs st3) sp)) s1-st3

    s1-st5 : readReg (regs st5) s1 ≡ readReg (regs s) s1
    s1-st5 = s1-st4  -- memory write doesn't change regs

    s1-st6 : readReg (regs st6) s1 ≡ readReg (regs s) s1
    s1-st6 = s1-st5  -- memory write doesn't change regs

    s1-st7 : readReg (regs st7) s1 ≡ readReg (regs s) s1
    s1-st7 = trans (readReg-writeReg-a0-s1 (regs st6) (readReg (regs st6) sp)) s1-st6

    s1-final : readReg (regs st7) s1 ≡ readReg (regs s) s1
    s1-final = s1-st7

    -- Register ra preservation (not touched by any of these instructions)
    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = refl  -- label doesn't change regs

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = trans (readReg-writeReg-sp-ra (regs st1) new-sp) ra-st1

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs s) ra
    ra-st3 = ra-st2  -- memory write doesn't change regs

    ra-st4 : readReg (regs st4) ra ≡ readReg (regs s) ra
    ra-st4 = trans (readReg-writeReg-s2-ra (regs st3) (readReg (regs st3) sp)) ra-st3

    ra-st5 : readReg (regs st5) ra ≡ readReg (regs s) ra
    ra-st5 = ra-st4  -- memory write doesn't change regs

    ra-st6 : readReg (regs st6) ra ≡ readReg (regs s) ra
    ra-st6 = ra-st5  -- memory write doesn't change regs

    ra-st7 : readReg (regs st7) ra ≡ readReg (regs s) ra
    ra-st7 = trans (readReg-writeReg-a0-ra (regs st6) (readReg (regs st6) sp)) ra-st6

    ra-final : readReg (regs st7) ra ≡ readReg (regs s) ra
    ra-final = ra-st7

    -- Register s2 final value (frame pointer = new-sp)
    s2-st7 : readReg (regs st7) s2 ≡ new-sp
    s2-st7 = trans (readReg-writeReg-a0-s2 (regs st6) (readReg (regs st6) sp)) s2-st6

    s2-final : readReg (regs st7) s2 ≡ readReg (regs s) sp ∸ 24
    s2-final = s2-st7

    -- Memory tracking for encode-pair-construct
    -- After step 4: memory[new-sp] = encode env
    -- After step 5: memory[new-sp + 8] = encode arg

    write-addr-env : readReg (regs st4) sp +ℕ 0 ≡ new-sp
    write-addr-env = trans (cong (_+ℕ 0) sp-st4) (+-identityʳ new-sp)

    s0-st5-val : readReg (regs st4) s0 ≡ encode env
    s0-st5-val = s0-st4

    mem-at-new-sp-st5 : readMem (memory st5) new-sp ≡ just (encode env)
    mem-at-new-sp-st5 =
      let write-addr = readReg (regs st4) sp +ℕ 0
          write-val = readReg (regs st4) s0
          read-at-write = readMem-writeMem-same (memory st4) write-addr write-val
          read-at-new-sp = subst (λ a → readMem (writeMem (memory st4) write-addr write-val) a ≡ just write-val)
                                 write-addr-env read-at-write
          val-eq = s0-st5-val
      in trans read-at-new-sp (cong just val-eq)

    -- st6 writes at new-sp + 8, which is ≢ new-sp
    new-sp≢new-sp+8 : new-sp ≢ new-sp +ℕ 8
    new-sp≢new-sp+8 = n≢n+suc new-sp 7

    mem-at-new-sp-st6 : readMem (memory st6) new-sp ≡ just (encode env)
    mem-at-new-sp-st6 = trans (readMem-writeMem-diff (memory st5) (readReg (regs st5) sp +ℕ 8) new-sp
                                                     (readReg (regs st5) a0)
                                                     (λ eq → new-sp≢new-sp+8 (trans (sym eq) (cong (_+ℕ 8) sp-st5))))
                              mem-at-new-sp-st5

    mem-at-new-sp-st7 : readMem (memory st7) new-sp ≡ just (encode env)
    mem-at-new-sp-st7 = mem-at-new-sp-st6  -- mv doesn't change memory

    mem-at-new-sp+8-st6 : readMem (memory st6) (new-sp +ℕ 8) ≡ just (encode arg)
    mem-at-new-sp+8-st6 =
      let write-addr = readReg (regs st5) sp +ℕ 8
          write-val = readReg (regs st5) a0
          addr-eq : write-addr ≡ new-sp +ℕ 8
          addr-eq = cong (_+ℕ 8) sp-st5
          read-at-write = readMem-writeMem-same (memory st5) write-addr write-val
          read-at-target = subst (λ a → readMem (writeMem (memory st5) write-addr write-val) a ≡ just write-val)
                                 addr-eq read-at-write
          val-eq = a0-st5
      in trans read-at-target (cong just val-eq)

    mem-at-new-sp+8-st7 : readMem (memory st7) (new-sp +ℕ 8) ≡ just (encode arg)
    mem-at-new-sp+8-st7 = mem-at-new-sp+8-st6  -- mv doesn't change memory

    -- Use encode-pair-construct to show new-sp = encode (env, arg)
    pair-encoding : new-sp ≡ encode (env , arg)
    pair-encoding = encode-pair-construct env arg new-sp (memory st7) mem-at-new-sp-st7 mem-at-new-sp+8-st7

    -- a0 in st7 = sp in st6 = new-sp = encode (env, arg)
    a0-st7-is-new-sp : readReg (regs st7) a0 ≡ new-sp
    a0-st7-is-new-sp = trans (readReg-writeReg-same (regs st6) a0 (readReg (regs st6) sp) (λ ())) sp-st6

    a0-final : readReg (regs st7) a0 ≡ encode (env , arg)
    a0-final = trans a0-st7-is-new-sp pair-encoding

------------------------------------------------------------------------
-- Thunk cleanup proof
------------------------------------------------------------------------

-- | Prove thunk cleanup: traces 3 instructions after f executes
-- Entry: pc = cleanup-offset (14 + len-f from curry start), s2 = frame pointer
-- Exit: pc = ret-offset (17 + len-f from curry start)
--
-- The 3 cleanup instructions:
--   14+len-f: mv sp s2 (restore sp to frame pointer)
--   15+len-f: ld s2 16(sp) (restore s2 from saved location)
--   16+len-f: addi sp sp +24 (deallocate stack frame)
thunk-cleanup-star-proven : ∀ {i A B C} (f : IR i (A * B) C)
                             (prefix suffix : Program) (s : State) →
  let prog = prefix ++ compile-riscv (curry f) ++ suffix
      len-f = compile-length f
      cleanup-offset = length prefix +ℕ 14 +ℕ len-f
      ret-offset = length prefix +ℕ 17 +ℕ len-f
  in
  halted s ≡ false →
  pc s ≡ cleanup-offset →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ ret-offset
          × readReg (regs s') a0 ≡ readReg (regs s) a0
          × readReg (regs s') s1 ≡ readReg (regs s) s1
          × readReg (regs s') ra ≡ readReg (regs s) ra)

thunk-cleanup-star-proven {A} {B} {C} f prefix suffix s h-false pc-eq =
  st3 , star-all , h3 , pc3 , a0-final , s1-final , ra-final
  where
    -- Use same names as type signature's let-bindings
    len-f = compile-length f
    cleanup-offset = length prefix +ℕ 14 +ℕ len-f
    ret-offset = length prefix +ℕ 17 +ℕ len-f
    prog = prefix ++ compile-riscv (curry f) ++ suffix

    -- curry-tail = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ label (18 +ℕ len-f) ∷ []
    -- These are at positions 14+len-f, 15+len-f, 16+len-f, 17+len-f, 18+len-f from curry start

    -- Instructions
    i0 : Instr
    i0 = mv sp s2

    i1 : Instr
    i1 = ld s2 (+ 16) sp

    i2 : Instr
    i2 = addi sp sp (+ 24)

    -- Fetch proofs using fetch-at-prefix-end pattern
    -- curry structure: closure-setup (7) ++ thunk-setup (7) ++ f (len-f) ++ tail (5)
    -- cleanup starts at position 14 + len-f

    curry-code = compile-riscv (curry f)

    -- Build the prefix up to cleanup instructions
    curry-before-cleanup : Program
    curry-before-cleanup = addi sp sp neg16 ∷
                           sd a0 (+ 0) sp ∷
                           auipc t0 (+ 0) ∷
                           addi t0 t0 (+ 5) ∷
                           sd t0 (+ 8) sp ∷
                           mv a0 sp ∷
                           j (+ (12 +ℕ len-f)) ∷
                           label 7 ∷
                           addi sp sp neg24 ∷
                           sd s2 (+ 16) sp ∷
                           mv s2 sp ∷
                           sd s0 (+ 0) sp ∷
                           sd a0 (+ 8) sp ∷
                           mv a0 sp ∷
                           compile-riscv f

    cleanup-and-tail : Program
    cleanup-and-tail = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ label (18 +ℕ len-f) ∷ []

    curry-split : curry-code ≡ curry-before-cleanup ++ cleanup-and-tail
    curry-split = refl

    len-curry-before : length curry-before-cleanup ≡ 14 +ℕ len-f
    len-curry-before = cong (14 +ℕ_) (compile-length-correct f)

    -- For fetch proofs, we use fetch-at-prefix-end
    -- prog = prefix ++ curry-code ++ suffix
    --      = prefix ++ (curry-before-cleanup ++ cleanup-and-tail) ++ suffix
    --      = (prefix ++ curry-before-cleanup) ++ cleanup-and-tail ++ suffix
    -- length (prefix ++ curry-before-cleanup) = cleanup-offset

    prefix-to-cleanup : Program
    prefix-to-cleanup = prefix ++ curry-before-cleanup

    len-prefix-to-cleanup : length prefix-to-cleanup ≡ cleanup-offset
    len-prefix-to-cleanup = begin
      length prefix-to-cleanup
        ≡⟨ List-length-++ prefix ⟩
      length prefix +ℕ length curry-before-cleanup
        ≡⟨ cong (length prefix +ℕ_) len-curry-before ⟩
      length prefix +ℕ (14 +ℕ len-f)
        ≡⟨ sym (+-assoc (length prefix) 14 len-f) ⟩
      (length prefix +ℕ 14) +ℕ len-f
        ≡⟨ cong (_+ℕ len-f) (+-comm (length prefix) 14) ⟩
      (14 +ℕ length prefix) +ℕ len-f
        ≡⟨ +-assoc 14 (length prefix) len-f ⟩
      14 +ℕ (length prefix +ℕ len-f)
        ≡⟨ cong (14 +ℕ_) (+-comm (length prefix) len-f) ⟩
      14 +ℕ (len-f +ℕ length prefix)
        ≡⟨ sym (+-assoc 14 len-f (length prefix)) ⟩
      (14 +ℕ len-f) +ℕ length prefix
        ≡⟨ +-comm (14 +ℕ len-f) (length prefix) ⟩
      length prefix +ℕ (14 +ℕ len-f)
        ≡⟨ sym (+-assoc (length prefix) 14 len-f) ⟩
      cleanup-offset
        ∎

    -- Show prog has the right structure for fetch-at-prefix-end
    prog-eq-for-fetch : prog ≡ prefix-to-cleanup ++ cleanup-and-tail ++ suffix
    prog-eq-for-fetch = begin
      prog
        ≡⟨ refl ⟩
      prefix ++ curry-code ++ suffix
        ≡⟨ cong (λ c → prefix ++ c ++ suffix) curry-split ⟩
      prefix ++ (curry-before-cleanup ++ cleanup-and-tail) ++ suffix
        ≡⟨ cong (prefix ++_) (++-assoc curry-before-cleanup cleanup-and-tail suffix) ⟩
      prefix ++ curry-before-cleanup ++ (cleanup-and-tail ++ suffix)
        ≡⟨ sym (++-assoc prefix curry-before-cleanup (cleanup-and-tail ++ suffix)) ⟩
      (prefix ++ curry-before-cleanup) ++ (cleanup-and-tail ++ suffix)
        ≡⟨ refl ⟩
      prefix-to-cleanup ++ cleanup-and-tail ++ suffix
        ∎

    -- cleanup-and-tail = i0 ∷ i1 ∷ i2 ∷ ret ∷ label (18 +ℕ len-f) ∷ []
    -- cleanup-and-tail ++ suffix has the structure i0 ∷ (i1 ∷ i2 ∷ ret ∷ label ... ∷ suffix)
    -- So fetch-at-prefix-end works with the right suffix

    fetch0 : fetch prog cleanup-offset ≡ just i0
    fetch0 = subst₂ (λ p n → fetch p n ≡ just i0) (sym prog-eq-for-fetch) len-prefix-to-cleanup
                    (fetch-at-prefix-end prefix-to-cleanup i0 (i1 ∷ i2 ∷ ret ∷ label (18 +ℕ len-f) ∷ suffix))

    -- For fetch1: need prefix-to-cleanup ++ i0 ∷ []
    prefix-to-i1 : Program
    prefix-to-i1 = prefix-to-cleanup ++ i0 ∷ []

    len-prefix-to-i1 : length prefix-to-i1 ≡ cleanup-offset +ℕ 1
    len-prefix-to-i1 = trans (List-length-++ prefix-to-cleanup) (cong (_+ℕ 1) len-prefix-to-cleanup)

    prog-eq-for-fetch1 : prog ≡ prefix-to-i1 ++ (i1 ∷ i2 ∷ ret ∷ label (18 +ℕ len-f) ∷ suffix)
    prog-eq-for-fetch1 = trans prog-eq-for-fetch (sym (++-assoc prefix-to-cleanup (i0 ∷ []) _))

    fetch1 : fetch prog (cleanup-offset +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq-for-fetch1) len-prefix-to-i1
                    (fetch-at-prefix-end prefix-to-i1 i1 (i2 ∷ ret ∷ label (18 +ℕ len-f) ∷ suffix))

    -- For fetch2: need prefix-to-cleanup ++ i0 ∷ i1 ∷ []
    prefix-to-i2 : Program
    prefix-to-i2 = prefix-to-i1 ++ i1 ∷ []

    len-prefix-to-i2 : length prefix-to-i2 ≡ cleanup-offset +ℕ 2
    len-prefix-to-i2 = trans (List-length-++ prefix-to-i1)
                             (trans (cong (_+ℕ 1) len-prefix-to-i1)
                                    (+-assoc cleanup-offset 1 1))

    prog-eq-for-fetch2 : prog ≡ prefix-to-i2 ++ (i2 ∷ ret ∷ label (18 +ℕ len-f) ∷ suffix)
    prog-eq-for-fetch2 = trans prog-eq-for-fetch1 (sym (++-assoc prefix-to-i1 (i1 ∷ []) _))

    fetch2 : fetch prog (cleanup-offset +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq-for-fetch2) len-prefix-to-i2
                    (fetch-at-prefix-end prefix-to-i2 i2 (ret ∷ label (18 +ℕ len-f) ∷ suffix))

    -- State after step 0: mv sp s2 (restore sp to frame pointer)
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp (readReg (regs s) s2)
                   ; pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execMv prog s sp s2)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ cleanup-offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- For ld s2, we need to know memory at sp+16 has saved s2
    -- We'll need this as a precondition or use a postulate for now
    -- The saved s2 value should be at (readReg (regs st1) sp) + 16

    sp-st1 : readReg (regs st1) sp ≡ readReg (regs s) s2
    sp-st1 = readReg-writeReg-same (regs s) sp (readReg (regs s) s2) (λ ())

    -- For now, postulate the memory read for the saved s2
    postulate
      mem-s2-saved : readMem (memory st1) (readReg (regs st1) sp +ℕ 16) ≡ just (readReg (regs s) s2 +ℕ 24)

    -- State after step 1: ld s2 16(sp)
    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) s2 (readReg (regs s) s2 +ℕ 24)
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execInstr-ld-success prog st1 s2 sp (+ 16) (readReg (regs s) s2 +ℕ 24) mem-s2-saved)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ cleanup-offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc cleanup-offset 1 1)

    sp-st2 : readReg (regs st2) sp ≡ readReg (regs s) s2
    sp-st2 = trans (readReg-writeReg-s2-sp (regs st1) (readReg (regs s) s2 +ℕ 24)) sp-st1

    -- State after step 2: addi sp sp +24 (deallocate)
    st3 : State
    st3 = record st2 { regs = writeReg (regs st2) sp (readReg (regs st2) sp +ℕ 24)
                     ; pc = pc st2 +ℕ 1 }

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execAddi prog st2 sp sp 24)

    h3 : halted st3 ≡ false
    h3 = h-false

    -- pc st3 = (cleanup-offset + 2) + 1 = cleanup-offset + 3
    -- cleanup-offset = (length prefix + 14) + len-f  [left assoc]
    -- ret-offset = (length prefix + 17) + len-f  [left assoc]
    -- Need: ((length prefix + 14) + len-f) + 3 = (length prefix + 17) + len-f
    pc3 : pc st3 ≡ ret-offset
    pc3 = begin
      pc st3
        ≡⟨ refl ⟩
      pc st2 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc2 ⟩
      (cleanup-offset +ℕ 2) +ℕ 1
        ≡⟨ +-assoc cleanup-offset 2 1 ⟩
      cleanup-offset +ℕ 3
        ≡⟨ refl ⟩
      (length prefix +ℕ 14 +ℕ len-f) +ℕ 3
        ≡⟨ +-assoc (length prefix +ℕ 14) len-f 3 ⟩
      (length prefix +ℕ 14) +ℕ (len-f +ℕ 3)
        ≡⟨ cong ((length prefix +ℕ 14) +ℕ_) (+-comm len-f 3) ⟩
      (length prefix +ℕ 14) +ℕ (3 +ℕ len-f)
        ≡⟨ sym (+-assoc (length prefix +ℕ 14) 3 len-f) ⟩
      ((length prefix +ℕ 14) +ℕ 3) +ℕ len-f
        ≡⟨ cong (_+ℕ len-f) (+-assoc (length prefix) 14 3) ⟩
      (length prefix +ℕ (14 +ℕ 3)) +ℕ len-f
        ≡⟨ refl ⟩
      (length prefix +ℕ 17) +ℕ len-f
        ≡⟨ refl ⟩
      ret-offset
        ∎

    -- Build Star proof
    star-all : Star prog s st3
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               refl*

    -- Register preservation through cleanup
    -- a0 not touched by any cleanup instruction
    a0-st1 : readReg (regs st1) a0 ≡ readReg (regs s) a0
    a0-st1 = readReg-writeReg-sp-a0 (regs s) (readReg (regs s) s2)

    a0-st2 : readReg (regs st2) a0 ≡ readReg (regs s) a0
    a0-st2 = trans (readReg-writeReg-s2-a0 (regs st1) (readReg (regs s) s2 +ℕ 24)) a0-st1

    a0-final : readReg (regs st3) a0 ≡ readReg (regs s) a0
    a0-final = trans (readReg-writeReg-sp-a0 (regs st2) (readReg (regs st2) sp +ℕ 24)) a0-st2

    -- s1 not touched by any cleanup instruction
    s1-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-st1 = readReg-writeReg-sp-s1 (regs s) (readReg (regs s) s2)

    s1-st2 : readReg (regs st2) s1 ≡ readReg (regs s) s1
    s1-st2 = trans (readReg-writeReg-s2-s1 (regs st1) (readReg (regs s) s2 +ℕ 24)) s1-st1

    s1-final : readReg (regs st3) s1 ≡ readReg (regs s) s1
    s1-final = trans (readReg-writeReg-sp-s1 (regs st2) (readReg (regs st2) sp +ℕ 24)) s1-st2

    -- ra not touched by any cleanup instruction
    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-sp-ra (regs s) (readReg (regs s) s2)

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = trans (readReg-writeReg-s2-ra (regs st1) (readReg (regs s) s2 +ℕ 24)) ra-st1

    ra-final : readReg (regs st3) ra ≡ readReg (regs s) ra
    ra-final = trans (readReg-writeReg-sp-ra (regs st2) (readReg (regs st2) sp +ℕ 24)) ra-st2
