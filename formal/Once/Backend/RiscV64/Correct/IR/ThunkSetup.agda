------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.ThunkSetup
--
-- Proven thunk setup instruction tracing for RISC-V 64-bit.
-- Traces the 5 thunk setup instructions within curry.
--
-- Thunk layout within curry (positions 7 onwards):
--   7: label code-ptr (thunk entry)
--   8: addi sp sp -16 (allocate pair)
--   9: sd s0 0(sp) (store env = a)
--   10: sd a0 8(sp) (store arg = b)
--   11: mv a0 sp (a0 = pair pointer)
--   12 to 11+len-f: compile-riscv f
--   12+len-f: ret
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.IR.ThunkSetup where

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

-- | Prove thunk setup: traces 5 instructions
-- Entry: pc = thunk-offset, a0 = encode arg, s0 = encode env
-- Exit: pc = f-offset, a0 = encode (env, arg)
thunk-setup-star-proven : ∀ {A B C} (f : IR (A * B) C)
                          (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
  let prog = prefix ++ compile-riscv (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 7
      f-offset = length prefix +ℕ 12
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
          × readReg (regs s') ra ≡ readReg (regs s) ra)

thunk-setup-star-proven {A} {B} {C} f prefix suffix env arg s
                        h-false pc-eq a0-eq s0-eq =
  st5 , star-all , h5 , pc5 , a0-final , s1-final , ra-final
  where
    len-f = compile-length f
    prog = prefix ++ compile-riscv (curry f) ++ suffix
    offset = length prefix
    thunk-offset = offset +ℕ 7
    f-offset = offset +ℕ 12

    -- Helper values
    orig-sp : Word
    orig-sp = readReg (regs s) sp

    new-sp : Word
    new-sp = orig-sp ∸ 16

    -- The 5 thunk setup instructions (at positions 7-11 within curry)
    i0 : Instr
    i0 = label 7

    i1 : Instr
    i1 = addi sp sp neg16

    i2 : Instr
    i2 = sd s0 (+ 0) sp

    i3 : Instr
    i3 = sd a0 (+ 8) sp

    i4 : Instr
    i4 = mv a0 sp

    -- Fetch lemmas (need to fetch at thunk-offset within curry)
    -- The curry code structure is:
    --   [6 closure setup] ++ [label 7] ++ [4 thunk setup] ++ [f code] ++ [ret] ++ [label end]
    -- So positions 7-11 within curry are the thunk setup instructions

    -- Build prefix up to each instruction
    curry-prefix-to-7 : Program
    curry-prefix-to-7 = addi sp sp neg16 ∷     -- 0
                        sd a0 (+ 0) sp ∷       -- 1
                        auipc t0 (+ 0) ∷       -- 2
                        addi t0 t0 (+ 5) ∷     -- 3
                        sd t0 (+ 8) sp ∷       -- 4
                        mv a0 sp ∷             -- 5
                        j (+ (7 +ℕ len-f)) ∷   -- 6
                        []

    prefix-to-i0 : Program
    prefix-to-i0 = prefix ++ curry-prefix-to-7

    len-prefix-to-i0 : length prefix-to-i0 ≡ thunk-offset
    len-prefix-to-i0 = List-length-++ prefix

    -- Fetch lemmas (proven using fetch-at-prefix-end)
    -- compile-riscv (curry f) = curry-prefix-to-7 ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ rest
    -- prog = prefix ++ (curry-prefix-to-7 ++ i0 ∷ ...) ++ suffix
    --      = (prefix ++ curry-prefix-to-7) ++ i0 ∷ ...
    --      = prefix-to-i0 ++ i0 ∷ ...

    -- The thunk body after the first 5 setup instructions
    thunk-body : Program
    thunk-body = compile-riscv f ++ ret ∷ label (13 +ℕ len-f) ∷ []

    -- Show curry code decomposes properly
    curry-code-eq : compile-riscv (curry f) ≡
                    curry-prefix-to-7 ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ thunk-body
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

    -- State after step 1: addi sp sp -16
    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) sp new-sp
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 i1 h1 (subst (λ p → fetch prog p ≡ just i1) (sym pc1) fetch1))
                  (execAddiNeg prog st1 sp sp 15)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ thunk-offset +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc thunk-offset 1 1)

    -- State after step 2: sd s0 0(sp) - store env at [new-sp]
    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = readReg-writeReg-same (regs st1) sp new-sp (λ ())

    s0-st2 : readReg (regs st2) s0 ≡ encode env
    s0-st2 = trans (readReg-writeReg-sp-s0 (regs st1) new-sp) s0-eq

    st3 : State
    st3 = record st2 { memory = writeMem (memory st2) (readReg (regs st2) sp +ℕ 0) (readReg (regs st2) s0)
                     ; pc = pc st2 +ℕ 1 }

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execSd prog st2 s0 0 sp)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ thunk-offset +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc thunk-offset 2 1)

    -- State after step 3: sd a0 8(sp) - store arg at [new-sp + 8]
    a0-st2 : readReg (regs st2) a0 ≡ encode arg
    a0-st2 = trans (readReg-writeReg-sp-a0 (regs st1) new-sp) a0-eq

    a0-st3 : readReg (regs st3) a0 ≡ encode arg
    a0-st3 = a0-st2  -- memory write doesn't change regs

    sp-st3 : readReg (regs st3) sp ≡ new-sp
    sp-st3 = sp-st2  -- memory write doesn't change regs

    st4 : State
    st4 = record st3 { memory = writeMem (memory st3) (readReg (regs st3) sp +ℕ 8) (readReg (regs st3) a0)
                     ; pc = pc st3 +ℕ 1 }

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execSd prog st3 a0 8 sp)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ thunk-offset +ℕ 4
    pc4 = trans (cong (λ p → p +ℕ 1) pc3) (+-assoc thunk-offset 3 1)

    -- State after step 4: mv a0 sp (a0 = pair pointer)
    sp-st4 : readReg (regs st4) sp ≡ new-sp
    sp-st4 = sp-st3  -- memory write doesn't change regs

    st5 : State
    st5 = record st4 { regs = writeReg (regs st4) a0 (readReg (regs st4) sp)
                     ; pc = pc st4 +ℕ 1 }

    step4 : step prog st4 ≡ just st5
    step4 = trans (step-exec prog st4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (execMv prog st4 a0 sp)

    -- Build Star proof
    star-all : Star prog s st5
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               ⟨ h4 , step4 ⟩◅
               refl*

    -- Final state properties
    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ f-offset
    pc5 = begin
      pc st5
        ≡⟨ refl ⟩
      pc st4 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc4 ⟩
      (thunk-offset +ℕ 4) +ℕ 1
        ≡⟨ +-assoc thunk-offset 4 1 ⟩
      thunk-offset +ℕ 5
        ≡⟨ cong (_+ℕ 5) refl ⟩  -- thunk-offset = offset + 7
      (offset +ℕ 7) +ℕ 5
        ≡⟨ +-assoc offset 7 5 ⟩
      offset +ℕ 12
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
    s1-st4 = s1-st3  -- memory write doesn't change regs

    s1-st5 : readReg (regs st5) s1 ≡ readReg (regs s) s1
    s1-st5 = trans (readReg-writeReg-a0-s1 (regs st4) (readReg (regs st4) sp)) s1-st4

    s1-final : readReg (regs st5) s1 ≡ readReg (regs s) s1
    s1-final = s1-st5

    -- Register ra preservation (not touched by any of these instructions)
    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = refl  -- label doesn't change regs

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = trans (readReg-writeReg-sp-ra (regs st1) new-sp) ra-st1

    ra-st3 : readReg (regs st3) ra ≡ readReg (regs s) ra
    ra-st3 = ra-st2  -- memory write doesn't change regs

    ra-st4 : readReg (regs st4) ra ≡ readReg (regs s) ra
    ra-st4 = ra-st3  -- memory write doesn't change regs

    ra-st5 : readReg (regs st5) ra ≡ readReg (regs s) ra
    ra-st5 = trans (readReg-writeReg-a0-ra (regs st4) (readReg (regs st4) sp)) ra-st4

    ra-final : readReg (regs st5) ra ≡ readReg (regs s) ra
    ra-final = ra-st5

    -- Memory tracking for encode-pair-construct
    -- After step 2: memory[new-sp] = encode env
    -- After step 3: memory[new-sp + 8] = encode arg

    write-addr-env : readReg (regs st2) sp +ℕ 0 ≡ new-sp
    write-addr-env = trans (cong (_+ℕ 0) sp-st2) (+-identityʳ new-sp)

    mem-at-new-sp-st3 : readMem (memory st3) new-sp ≡ just (encode env)
    mem-at-new-sp-st3 =
      let write-addr = readReg (regs st2) sp +ℕ 0
          write-val = readReg (regs st2) s0
          read-at-write = readMem-writeMem-same (memory st2) write-addr write-val
          read-at-new-sp = subst (λ a → readMem (writeMem (memory st2) write-addr write-val) a ≡ just write-val)
                                 write-addr-env read-at-write
          val-eq = s0-st2
      in trans read-at-new-sp (cong just val-eq)

    -- st4 writes at new-sp + 8, which is ≢ new-sp
    new-sp≢new-sp+8 : new-sp ≢ new-sp +ℕ 8
    new-sp≢new-sp+8 = n≢n+suc new-sp 7

    mem-at-new-sp-st4 : readMem (memory st4) new-sp ≡ just (encode env)
    mem-at-new-sp-st4 = trans (readMem-writeMem-diff (memory st3) (readReg (regs st3) sp +ℕ 8) new-sp
                                                     (readReg (regs st3) a0)
                                                     (λ eq → new-sp≢new-sp+8 (trans (sym eq) (cong (_+ℕ 8) sp-st3))))
                              mem-at-new-sp-st3

    mem-at-new-sp-st5 : readMem (memory st5) new-sp ≡ just (encode env)
    mem-at-new-sp-st5 = mem-at-new-sp-st4  -- mv doesn't change memory

    mem-at-new-sp+8-st4 : readMem (memory st4) (new-sp +ℕ 8) ≡ just (encode arg)
    mem-at-new-sp+8-st4 =
      let write-addr = readReg (regs st3) sp +ℕ 8
          write-val = readReg (regs st3) a0
          addr-eq : write-addr ≡ new-sp +ℕ 8
          addr-eq = cong (_+ℕ 8) sp-st3
          read-at-write = readMem-writeMem-same (memory st3) write-addr write-val
          read-at-target = subst (λ a → readMem (writeMem (memory st3) write-addr write-val) a ≡ just write-val)
                                 addr-eq read-at-write
          val-eq = a0-st3
      in trans read-at-target (cong just val-eq)

    mem-at-new-sp+8-st5 : readMem (memory st5) (new-sp +ℕ 8) ≡ just (encode arg)
    mem-at-new-sp+8-st5 = mem-at-new-sp+8-st4  -- mv doesn't change memory

    -- Use encode-pair-construct to show new-sp = encode (env, arg)
    pair-encoding : new-sp ≡ encode (env , arg)
    pair-encoding = encode-pair-construct env arg new-sp (memory st5) mem-at-new-sp-st5 mem-at-new-sp+8-st5

    -- a0 in st5 = sp in st4 = new-sp = encode (env, arg)
    a0-st5-is-new-sp : readReg (regs st5) a0 ≡ new-sp
    a0-st5-is-new-sp = trans (readReg-writeReg-same (regs st4) a0 (readReg (regs st4) sp) (λ ())) sp-st4

    a0-final : readReg (regs st5) a0 ≡ encode (env , arg)
    a0-final = trans a0-st5-is-new-sp pair-encoding
