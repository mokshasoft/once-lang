------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.ThunkSetup
--
-- Proven thunk setup instruction tracing for AArch64.
-- Traces the 4 thunk setup instructions within curry.
--
-- Thunk layout within curry (positions 6 onwards):
--   6: label code-ptr (thunk entry)
--   7: sub-sp 16 (allocate 16 bytes for pair)
--   8: stp x19 x0 (sp+imm 0) (store env and arg as pair)
--   9: mov-from-sp x0 (x0 = pointer to pair)
--   10 to 9+len-f: compile-aarch64 f
--   10+len-f: ret
--   11+len-f: label end
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.AArch64.Correct.IR.ThunkSetup where

open import Size

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (code-ptr)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Postulates using (encode; encode-pair-construct)
open import Once.Backend.AArch64.Correct.Foundation
  using (readReg-writeSP; readSP-writeSP; readSP-writeReg; readReg-writeReg-same;
         readReg-writeSP-x0; readReg-writeSP-x19; readReg-writeSP-x20;
         readReg-writeSP-x21; readReg-writeSP-x29; readReg-writeSP-x30;
         readReg-writeReg-x0-x19; readReg-writeReg-x0-x20; readReg-writeReg-x0-x21;
         readReg-writeReg-x0-x29; readReg-writeReg-x0-x30;
         execInstr-label; execInstr-sub-sp; execInstr-stp; execInstr-mov-from-sp;
         readMem-writeMem-same; readMem-writeMem-diff; n≢n+8; n+8≢n)
open import Once.Backend.AArch64.Correct.CompileLength using (compile-length-correct)
open import Once.Backend.AArch64.Correct.FetchStep using (step-exec-at-offset)
open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; ⟨_,_⟩◅_)

open import Once.Backend.Common.Memory
  using (n≢n+suc)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; suc; _∸_; _≡ᵇ_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Helper: fetch-at-prefix-end
------------------------------------------------------------------------

-- | Fetch the first instruction when program is split at prefix end
fetch-at-prefix-end : ∀ (prefix : Program) (i : Instr) (suffix : Program) →
  fetch (prefix ++ i ∷ suffix) (length prefix) ≡ just i
fetch-at-prefix-end [] i suffix = refl
fetch-at-prefix-end (x ∷ prefix) i suffix = fetch-at-prefix-end prefix i suffix

------------------------------------------------------------------------
-- Thunk setup proof
------------------------------------------------------------------------

-- | Prove thunk setup: traces 4 instructions
-- Entry: pc = thunk-offset, x0 = encode arg, x19 = encode env, x30 = return addr
-- Exit: pc = f-offset, x0 = encode (env, arg)
thunk-setup-star : ∀ {i A B C} (f : IR i (A * B) C)
                   (prefix suffix : Program) (env : ⟦ A ⟧) (arg : ⟦ B ⟧) (s : State) →
  let prog = prefix ++ compile-aarch64 (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 6
      f-offset = length prefix +ℕ 10
  in
  halted s ≡ false →
  pc s ≡ thunk-offset →
  readReg (regs s) x0 ≡ encode arg →
  readReg (regs s) x19 ≡ encode env →
  ∃[ s' ] (Star prog s s'
          × halted s' ≡ false
          × pc s' ≡ f-offset
          × readReg (regs s') x0 ≡ encode (env , arg)
          × readReg (regs s') x19 ≡ readReg (regs s) x19
          × readReg (regs s') x20 ≡ readReg (regs s) x20
          × readReg (regs s') x21 ≡ readReg (regs s) x21
          × readReg (regs s') x29 ≡ readReg (regs s) x29
          × readReg (regs s') x30 ≡ readReg (regs s) x30
          × readSP (regs s') ≡ readSP (regs s) ∸ 16)

thunk-setup-star {A} {B} {C} f prefix suffix env arg s
                 h-false pc-eq x0-eq x19-eq =
  st4 , star-all , h4 , pc4 , a0-final , x19-final , x20-final , x21-final , x29-final , x30-final , sp-final
  where
    len-f = compile-length f
    prog = prefix ++ compile-aarch64 (curry f) ++ suffix
    offset = length prefix
    thunk-offset = offset +ℕ 6
    f-offset = offset +ℕ 10

    -- Helper values
    orig-sp : Word
    orig-sp = readSP (regs s)

    new-sp : Word
    new-sp = orig-sp ∸ 16

    -- The 4 thunk setup instructions (at positions 6-9 within curry)
    i0 : Instr
    i0 = label 6

    i1 : Instr
    i1 = sub-sp 16

    i2 : Instr
    i2 = stp x19 x0 (sp+imm 0)

    i3 : Instr
    i3 = mov-from-sp x0

    -- The curry code structure
    curry-prefix-to-6 : Program
    curry-prefix-to-6 = sub-sp 16 ∷                      -- 0
                        str x0 (sp+imm 0) ∷              -- 1
                        adr x9 4 ∷                       -- 2
                        str x9 (sp+imm 8) ∷              -- 3
                        mov-from-sp x0 ∷                 -- 4
                        b (6 +ℕ len-f) ∷                 -- 5
                        []

    prefix-to-i0 : Program
    prefix-to-i0 = prefix ++ curry-prefix-to-6

    len-prefix-to-i0 : length prefix-to-i0 ≡ thunk-offset
    len-prefix-to-i0 = List-length-++ prefix

    -- The thunk body after the 4 setup instructions
    thunk-body : Program
    thunk-body = compile-aarch64 f ++ ret ∷ label (11 +ℕ len-f) ∷ []

    -- Show curry code decomposes properly
    curry-code-eq : compile-aarch64 (curry f) ≡
                    curry-prefix-to-6 ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ thunk-body
    curry-code-eq = refl

    -- The rest of the program after i0
    rest-after-i0 : Program
    rest-after-i0 = i1 ∷ i2 ∷ i3 ∷ thunk-body ++ suffix

    -- Program structure: prog = prefix-to-i0 ++ i0 ∷ rest
    prog-eq0 : prog ≡ prefix-to-i0 ++ i0 ∷ rest-after-i0
    prog-eq0 = trans (cong (λ c → prefix ++ c ++ suffix) curry-code-eq)
                     (sym (++-assoc prefix curry-prefix-to-6 (i0 ∷ i1 ∷ i2 ∷ i3 ∷ thunk-body ++ suffix)))

    fetch0 : fetch prog thunk-offset ≡ just i0
    fetch0 = subst₂ (λ p n → fetch p n ≡ just i0) (sym prog-eq0) len-prefix-to-i0
                    (fetch-at-prefix-end prefix-to-i0 i0 rest-after-i0)

    prefix-to-i1 : Program
    prefix-to-i1 = prefix-to-i0 ++ i0 ∷ []

    rest-after-i1 : Program
    rest-after-i1 = i2 ∷ i3 ∷ thunk-body ++ suffix

    prog-eq1 : prog ≡ prefix-to-i1 ++ i1 ∷ rest-after-i1
    prog-eq1 = trans prog-eq0 (sym (++-assoc prefix-to-i0 (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ thunk-body ++ suffix)))

    len-prefix-to-i1 : length prefix-to-i1 ≡ thunk-offset +ℕ 1
    len-prefix-to-i1 = trans (List-length-++ prefix-to-i0) (cong (_+ℕ 1) len-prefix-to-i0)

    fetch1 : fetch prog (thunk-offset +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-to-i1
                    (fetch-at-prefix-end prefix-to-i1 i1 rest-after-i1)

    prefix-to-i2 : Program
    prefix-to-i2 = prefix-to-i1 ++ i1 ∷ []

    rest-after-i2 : Program
    rest-after-i2 = i3 ∷ thunk-body ++ suffix

    prog-eq2 : prog ≡ prefix-to-i2 ++ i2 ∷ rest-after-i2
    prog-eq2 = trans prog-eq1 (sym (++-assoc prefix-to-i1 (i1 ∷ []) (i2 ∷ i3 ∷ thunk-body ++ suffix)))

    len-prefix-to-i2 : length prefix-to-i2 ≡ thunk-offset +ℕ 2
    len-prefix-to-i2 = trans (List-length-++ prefix-to-i1)
                             (trans (cong (_+ℕ 1) len-prefix-to-i1) (+-assoc thunk-offset 1 1))

    fetch2 : fetch prog (thunk-offset +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-to-i2
                    (fetch-at-prefix-end prefix-to-i2 i2 rest-after-i2)

    prefix-to-i3 : Program
    prefix-to-i3 = prefix-to-i2 ++ i2 ∷ []

    rest-after-i3 : Program
    rest-after-i3 = thunk-body ++ suffix

    prog-eq3 : prog ≡ prefix-to-i3 ++ i3 ∷ rest-after-i3
    prog-eq3 = trans prog-eq2 (sym (++-assoc prefix-to-i2 (i2 ∷ []) (i3 ∷ thunk-body ++ suffix)))

    len-prefix-to-i3 : length prefix-to-i3 ≡ thunk-offset +ℕ 3
    len-prefix-to-i3 = trans (List-length-++ prefix-to-i2)
                             (trans (cong (_+ℕ 1) len-prefix-to-i2) (+-assoc thunk-offset 2 1))

    fetch3 : fetch prog (thunk-offset +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-to-i3
                    (fetch-at-prefix-end prefix-to-i3 i3 rest-after-i3)

    -- State after step 0: label (no-op, just pc++)
    st1 : State
    st1 = record s { pc = pc s +ℕ 1 }

    step0 : step prog s ≡ just st1
    step0 = subst (λ p → step p s ≡ just st1) (sym prog-eq0)
                  (trans (step-exec-at-offset prefix-to-i0 i0 rest-after-i0 s h-false (subst (λ p → pc s ≡ p) (sym len-prefix-to-i0) pc-eq))
                         (execInstr-label (prefix-to-i0 ++ i0 ∷ rest-after-i0) s 6))

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ thunk-offset +ℕ 1
    pc1 = cong (λ p → p +ℕ 1) pc-eq

    -- State after step 1: sub-sp 16
    st2 : State
    st2 = record st1 { regs = writeSP (regs st1) new-sp
                     ; pc = pc st1 +ℕ 1 }

    step1 : step prog st1 ≡ just st2
    step1 = subst (λ p → step p st1 ≡ just st2) (sym prog-eq1)
                  (trans (step-exec-at-offset prefix-to-i1 i1 rest-after-i1 st1 h1 (subst (λ p → pc st1 ≡ p) (sym len-prefix-to-i1) pc1))
                         (execInstr-sub-sp (prefix-to-i1 ++ i1 ∷ rest-after-i1) st1 16))

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ thunk-offset +ℕ 2
    pc2 = trans (cong (λ p → p +ℕ 1) pc1) (+-assoc thunk-offset 1 1)

    sp-st2 : readSP (regs st2) ≡ new-sp
    sp-st2 = readSP-writeSP (regs st1) new-sp

    x19-st2 : readReg (regs st2) x19 ≡ encode env
    x19-st2 = trans (readReg-writeSP (regs st1) x19 new-sp) x19-eq

    x0-st2 : readReg (regs st2) x0 ≡ encode arg
    x0-st2 = trans (readReg-writeSP-x0 (regs st1) new-sp) x0-eq

    -- State after step 2: stp x19 x0 (sp+imm 0) - store env and arg as pair
    st3 : State
    st3 = record st2 { memory = writeMem (writeMem (memory st2) (readSP (regs st2)) (readReg (regs st2) x19))
                                                    (readSP (regs st2) +ℕ 8) (readReg (regs st2) x0)
                     ; pc = pc st2 +ℕ 1 }

    -- Helper: normalize addresses from effectiveAddr (sp+imm 0) form
    st3-from-exec : State
    st3-from-exec = record st2 { memory = writeMem (writeMem (memory st2) (readSP (regs st2) +ℕ 0) (readReg (regs st2) x19))
                                                             (readSP (regs st2) +ℕ 0 +ℕ 8) (readReg (regs st2) x0)
                                ; pc = pc st2 +ℕ 1 }

    -- Prove addresses normalize: readSP (regs st2) +ℕ 0 ≡ readSP (regs st2)
    addr1-eq : readSP (regs st2) +ℕ 0 ≡ readSP (regs st2)
    addr1-eq = +-identityʳ (readSP (regs st2))

    -- Prove: readSP (regs st2) +ℕ 0 +ℕ 8 ≡ readSP (regs st2) +ℕ 8
    addr2-eq : readSP (regs st2) +ℕ 0 +ℕ 8 ≡ readSP (regs st2) +ℕ 8
    addr2-eq = cong (_+ℕ 8) (+-identityʳ (readSP (regs st2)))

    st3-normalized : st3-from-exec ≡ st3
    st3-normalized = cong (λ m → record st2 { memory = m ; pc = pc st2 +ℕ 1 })
                          (trans (cong (λ a → writeMem (writeMem (memory st2) a (readReg (regs st2) x19))
                                                        (readSP (regs st2) +ℕ 0 +ℕ 8) (readReg (regs st2) x0))
                                       addr1-eq)
                                 (cong (λ a → writeMem (writeMem (memory st2) (readSP (regs st2)) (readReg (regs st2) x19))
                                                        a (readReg (regs st2) x0))
                                       addr2-eq))

    step2 : step prog st2 ≡ just st3
    step2 = subst (λ p → step p st2 ≡ just st3) (sym prog-eq2)
                  (trans (step-exec-at-offset prefix-to-i2 i2 rest-after-i2 st2 h2 (subst (λ p → pc st2 ≡ p) (sym len-prefix-to-i2) pc2))
                         (trans (execInstr-stp (prefix-to-i2 ++ i2 ∷ rest-after-i2) st2 x19 x0 (sp+imm 0))
                                (cong just st3-normalized)))

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ thunk-offset +ℕ 3
    pc3 = trans (cong (λ p → p +ℕ 1) pc2) (+-assoc thunk-offset 2 1)

    sp-st3 : readSP (regs st3) ≡ new-sp
    sp-st3 = sp-st2  -- memory write doesn't change regs

    x19-st3 : readReg (regs st3) x19 ≡ encode env
    x19-st3 = x19-st2  -- memory write doesn't change regs

    x0-st3 : readReg (regs st3) x0 ≡ encode arg
    x0-st3 = x0-st2  -- memory write doesn't change regs

    -- State after step 3: mov-from-sp x0 (x0 = pair pointer)
    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) x0 (readSP (regs st3))
                     ; pc = pc st3 +ℕ 1 }

    step3 : step prog st3 ≡ just st4
    step3 = subst (λ p → step p st3 ≡ just st4) (sym prog-eq3)
                  (trans (step-exec-at-offset prefix-to-i3 i3 rest-after-i3 st3 h3 (subst (λ p → pc st3 ≡ p) (sym len-prefix-to-i3) pc3))
                         (execInstr-mov-from-sp (prefix-to-i3 ++ i3 ∷ rest-after-i3) st3 x0))

    -- Build Star proof
    star-all : Star prog s st4
    star-all = ⟨ h-false , step0 ⟩◅
               ⟨ h1 , step1 ⟩◅
               ⟨ h2 , step2 ⟩◅
               ⟨ h3 , step3 ⟩◅
               refl*

    -- Final state properties
    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ f-offset
    pc4 = begin
      pc st4
        ≡⟨ refl ⟩
      pc st3 +ℕ 1
        ≡⟨ cong (_+ℕ 1) pc3 ⟩
      (thunk-offset +ℕ 3) +ℕ 1
        ≡⟨ +-assoc thunk-offset 3 1 ⟩
      thunk-offset +ℕ 4
        ≡⟨ refl ⟩
      (offset +ℕ 6) +ℕ 4
        ≡⟨ +-assoc offset 6 4 ⟩
      offset +ℕ 10
        ≡⟨ refl ⟩
      f-offset ∎

    -- Memory tracking for encode-pair-construct
    -- After step 2: memory[new-sp] = encode env, memory[new-sp + 8] = encode arg

    mem-at-new-sp-st3 : readMem (memory st3) new-sp ≡ just (encode env)
    mem-at-new-sp-st3 =
      let write-addr = readSP (regs st2)
          write-val1 = readReg (regs st2) x19
          mem1 = writeMem (memory st2) write-addr write-val1
          write-addr2 = readSP (regs st2) +ℕ 8
          write-val2 = readReg (regs st2) x0
          -- First write at new-sp
          read-at-write1 = readMem-writeMem-same (memory st2) write-addr write-val1
          -- Second write at new-sp + 8, doesn't affect new-sp
          new-sp≢write-addr2 : (new-sp ≡ᵇ write-addr2) ≡ false
          new-sp≢write-addr2 = subst (λ addr → (new-sp ≡ᵇ addr) ≡ false) (sym (cong (_+ℕ 8) sp-st2)) (n≢n+8 new-sp)
          read-at-new-sp = readMem-writeMem-diff mem1 write-addr2 new-sp write-val2 new-sp≢write-addr2
          val-eq = x19-st2
      in trans read-at-new-sp (trans (subst (λ a → readMem mem1 a ≡ just write-val1) sp-st2 read-at-write1)
                                     (cong just val-eq))

    mem-at-new-sp+8-st3 : readMem (memory st3) (new-sp +ℕ 8) ≡ just (encode arg)
    mem-at-new-sp+8-st3 =
      let write-addr = readSP (regs st2)
          write-val1 = readReg (regs st2) x19
          mem1 = writeMem (memory st2) write-addr write-val1
          write-addr2 = readSP (regs st2) +ℕ 8
          write-val2 = readReg (regs st2) x0
          addr-eq : write-addr2 ≡ new-sp +ℕ 8
          addr-eq = cong (_+ℕ 8) sp-st2
          read-at-write2 = readMem-writeMem-same mem1 write-addr2 write-val2
          read-at-target = subst (λ a → readMem (writeMem mem1 write-addr2 write-val2) a ≡ just write-val2)
                                 addr-eq read-at-write2
          val-eq = x0-st2
      in trans read-at-target (cong just val-eq)

    -- Memory in st4 is unchanged from st3
    mem-at-new-sp-st4 : readMem (memory st4) new-sp ≡ just (encode env)
    mem-at-new-sp-st4 = mem-at-new-sp-st3

    mem-at-new-sp+8-st4 : readMem (memory st4) (new-sp +ℕ 8) ≡ just (encode arg)
    mem-at-new-sp+8-st4 = mem-at-new-sp+8-st3

    -- Use encode-pair-construct to show new-sp = encode (env, arg)
    pair-encoding : new-sp ≡ encode (env , arg)
    pair-encoding = encode-pair-construct env arg new-sp (memory st4) mem-at-new-sp-st4 mem-at-new-sp+8-st4

    -- x0 in st4 = sp in st3 = new-sp = encode (env, arg)
    x0-st4-is-new-sp : readReg (regs st4) x0 ≡ new-sp
    x0-st4-is-new-sp = trans (readReg-writeReg-same (regs st3) x0 (readSP (regs st3))) sp-st3

    a0-final : readReg (regs st4) x0 ≡ encode (env , arg)
    a0-final = trans x0-st4-is-new-sp pair-encoding

    -- Register preservation
    x19-st3-preserved : readReg (regs st3) x19 ≡ readReg (regs s) x19
    x19-st3-preserved = trans x19-st3 (sym x19-eq)  -- x19-st3 : ... ≡ encode env, x19-eq : readReg (regs s) x19 ≡ encode env

    x19-final : readReg (regs st4) x19 ≡ readReg (regs s) x19
    x19-final = trans (readReg-writeReg-x0-x19 (regs st3) (readSP (regs st3))) x19-st3-preserved

    x20-st1 : readReg (regs st1) x20 ≡ readReg (regs s) x20
    x20-st1 = refl

    x20-st2 : readReg (regs st2) x20 ≡ readReg (regs s) x20
    x20-st2 = trans (readReg-writeSP-x20 (regs st1) new-sp) x20-st1

    x20-st3 : readReg (regs st3) x20 ≡ readReg (regs s) x20
    x20-st3 = x20-st2

    x20-final : readReg (regs st4) x20 ≡ readReg (regs s) x20
    x20-final = trans (readReg-writeReg-x0-x20 (regs st3) (readSP (regs st3))) x20-st3

    x21-st1 : readReg (regs st1) x21 ≡ readReg (regs s) x21
    x21-st1 = refl

    x21-st2 : readReg (regs st2) x21 ≡ readReg (regs s) x21
    x21-st2 = trans (readReg-writeSP-x21 (regs st1) new-sp) x21-st1

    x21-st3 : readReg (regs st3) x21 ≡ readReg (regs s) x21
    x21-st3 = x21-st2

    x21-final : readReg (regs st4) x21 ≡ readReg (regs s) x21
    x21-final = trans (readReg-writeReg-x0-x21 (regs st3) (readSP (regs st3))) x21-st3

    x29-st1 : readReg (regs st1) x29 ≡ readReg (regs s) x29
    x29-st1 = refl

    x29-st2 : readReg (regs st2) x29 ≡ readReg (regs s) x29
    x29-st2 = trans (readReg-writeSP-x29 (regs st1) new-sp) x29-st1

    x29-st3 : readReg (regs st3) x29 ≡ readReg (regs s) x29
    x29-st3 = x29-st2

    x29-final : readReg (regs st4) x29 ≡ readReg (regs s) x29
    x29-final = trans (readReg-writeReg-x0-x29 (regs st3) (readSP (regs st3))) x29-st3

    x30-st1 : readReg (regs st1) x30 ≡ readReg (regs s) x30
    x30-st1 = refl

    x30-st2 : readReg (regs st2) x30 ≡ readReg (regs s) x30
    x30-st2 = trans (readReg-writeSP-x30 (regs st1) new-sp) x30-st1

    x30-st3 : readReg (regs st3) x30 ≡ readReg (regs s) x30
    x30-st3 = x30-st2

    x30-final : readReg (regs st4) x30 ≡ readReg (regs s) x30
    x30-final = trans (readReg-writeReg-x0-x30 (regs st3) (readSP (regs st3))) x30-st3

    -- SP tracking
    sp-st4 : readSP (regs st4) ≡ new-sp
    sp-st4 = trans (readSP-writeReg (regs st3) x0 (readSP (regs st3))) sp-st3

    sp-final : readSP (regs st4) ≡ readSP (regs s) ∸ 16
    sp-final = sp-st4
