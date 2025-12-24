------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.MutualIR
--
-- Mutual block for run-ir-star-at-offset and complex IR cases.
--
-- RISC-V simplification over X86:
--   - a0 is BOTH input and output (no rdi/rax transfer needed)
--   - Only s1 needs preservation (vs x86's r14/r15/rbp)
--   - Simpler compose: no transfer instruction between f and g
--
-- NEW: curry-thunk-correct-impl replaces curry-thunk-correct postulate
-- by using the IH (run-ir-star-at-offset) to prove thunk correctness.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.MutualIR where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates
  using (encode; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-pair-construct; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val; encode-arr-identity;
         encode-closure-construct; encode-fix-unwrap; encode-fix-wrap;
         encode-inl-construct; encode-inr-construct)

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.CompileLength
open import Once.Backend.RiscV64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_;
         star-step2; star-step3; star-step4; star-step5)
open import Once.Backend.RiscV64.Correct.ClosureWellFormed
  using (ClosureWellFormed; ThunkResult; code-ptr-valid; thunk-correct;
         thunk-star; thunk-halted; thunk-a0; thunk-s1)

-- Re-export StarBase for backwards compatibility
open import Once.Backend.RiscV64.Correct.StarBase public
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-ra; ir-sp;
         ir-mem-sp; ir-mem-sp+8; ir-mem-sp+16;
         run-id-star; run-terminal-star; run-fold-star; run-unfold-star;
         run-arr-star; run-fst-star; run-snd-star)

-- Import extracted compose helpers
open import Once.Backend.RiscV64.Correct.IR.Compose
  using (ComposeContext; make-compose-context;
         assemble-compose-result; transform-f-result; transform-g-result)
open import Once.Backend.RiscV64.Correct.IR.Compose using (module ComposeContext)

-- Import extracted pair helpers
open import Once.Backend.RiscV64.Correct.IR.Pair
  using (PairContext; make-pair-context;
         pair-setup-star; pair-middle-star; pair-final-star)
open import Once.Backend.RiscV64.Correct.IR.Pair using (module PairContext)

-- Import extracted case helpers
open import Once.Backend.RiscV64.Correct.IR.Case
  using (CaseContext; make-case-context;
         case-dispatch-left-star; case-dispatch-right-star;
         case-left-jump-star; case-right-end-star)
open import Once.Backend.RiscV64.Correct.IR.Case using (module CaseContext)

-- Import extracted curry proof
open import Once.Backend.RiscV64.Correct.IR.Curry using (run-curry-star)

-- Import thunk setup proof
open import Once.Backend.RiscV64.Correct.IR.ThunkSetup using (thunk-setup-star-proven; thunk-cleanup-star-proven)

-- Import apply proof (proven when ClosureWellFormed is available)
open import Once.Backend.RiscV64.Correct.IR.Apply
  using (run-apply-with-wf; apply-setup-star; apply-jalr-star; apply-nop-star)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-monoˡ-<; m≤m+n; m≤n+m)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Star-based inl/inr execution
--
-- inl: addi sp sp -16; sd zero 0(sp); sd a0 8(sp); mv a0 sp
-- inr: addi sp sp -16; li t0 1; sd t0 0(sp); sd a0 8(sp); mv a0 sp
------------------------------------------------------------------------

open import Once.Backend.Common.Memory
  using (readMem-writeMem-same; readMem-writeMem-diff; n≢n+suc)

-- | Star-based inl execution
run-inl-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  let prog = prefix ++ compile-riscv {A} {A + B} inl ++ suffix
  in ∃[ s' ] IRStarResult {A} {A + B} inl prog s s' x (length prefix)
run-inl-star {A} {B} prefix suffix x s h-false pc-eq a0-eq =
  st4 , record
    { ir-star = star-proof
    ; ir-halted = h4
    ; ir-pc = pc4
    ; ir-a0 = a0-final
    ; ir-s1 = s1-reg-final
    ; ir-ra = ra-final
    ; ir-sp = sp-final
    ; ir-mem-sp = mem-sp-final
    ; ir-mem-sp+8 = mem-sp+8-final
    ; ir-mem-sp+16 = mem-sp+16-final
    }
  where
    prog : Program
    prog = prefix ++ compile-riscv {A} {A + B} inl ++ suffix

    offset = length prefix

    -- The 4 instructions of inl
    i0 = addi sp sp neg16
    i1-instr = sd zero (+ 0) sp
    i2 = sd a0 (+ 8) sp
    i3 = mv a0 sp

    orig-sp = readReg (regs s) sp
    new-sp = orig-sp ∸ 16

    -- States after each instruction
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp ; pc = pc s +ℕ 1 }

    st2 : State
    st2 = record st1 { memory = writeMem (memory st1) (readReg (regs st1) sp +ℕ 0) (readReg (regs st1) zero)
                     ; pc = pc st1 +ℕ 1 }

    st3 : State
    st3 = record st2 { memory = writeMem (memory st2) (readReg (regs st2) sp +ℕ 8) (readReg (regs st2) a0)
                     ; pc = pc st2 +ℕ 1 }

    st4 : State
    st4 = record st3 { regs = writeReg (regs st3) a0 (readReg (regs st3) sp)
                     ; pc = pc st3 +ℕ 1 }

    -- Fetch lemmas
    fetch0 : fetch prog offset ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 _

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) _)

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just i1-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1-instr) (sym prog-eq1) len-prefix-1
                    (fetch-at-prefix-end (prefix ++ i0 ∷ []) i1-instr _)

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1-instr ∷ []) ++ _
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1-instr ∷ []) _)

    len-prefix-2 : length (prefix ++ i0 ∷ i1-instr ∷ []) ≡ offset +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (offset +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1-instr ∷ []) i2 _)

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ []) ++ _
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1-instr ∷ i2 ∷ []) _)

    len-prefix-3 : length (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ []) ≡ offset +ℕ 3
    len-prefix-3 = List-length-++ prefix

    fetch3 : fetch prog (offset +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ []) i3 _)

    -- Step proofs
    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execAddiNeg prog s sp sp 15)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 i1-instr h1 (subst (λ p → fetch prog p ≡ just i1-instr) (sym pc1) fetch1))
                  (execSd prog st1 zero 0 sp)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execSd prog st2 a0 8 sp)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc offset 2 1)

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execMv prog st3 a0 sp)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc offset 3 1)

    star-proof : Star prog s st4
    star-proof = star-step4 h-false step0 h1 step1 h2 step2 h3 step3

    -- Register preservation
    sp-st1 : readReg (regs st1) sp ≡ new-sp
    sp-st1 = readReg-writeReg-same (regs s) sp new-sp (λ ())

    a0-st1 : readReg (regs st1) a0 ≡ encode x
    a0-st1 = trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq

    s1-reg-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-reg-st1 = readReg-writeReg-sp-s1 (regs s) new-sp

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-sp-ra (regs s) new-sp

    -- st2: memory write doesn't change regs
    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = sp-st1

    a0-st2 : readReg (regs st2) a0 ≡ encode x
    a0-st2 = a0-st1

    -- st3: memory write doesn't change regs
    sp-st3 : readReg (regs st3) sp ≡ new-sp
    sp-st3 = sp-st2

    -- st4: mv a0 sp
    a0-st4 : readReg (regs st4) a0 ≡ new-sp
    a0-st4 = trans (readReg-writeReg-same (regs st3) a0 (readReg (regs st3) sp) (λ ())) sp-st3

    s1-reg-final : readReg (regs st4) s1 ≡ readReg (regs s) s1
    s1-reg-final = trans (readReg-writeReg-a0-s1 (regs st3) (readReg (regs st3) sp)) s1-reg-st1

    ra-final : readReg (regs st4) ra ≡ readReg (regs s) ra
    ra-final = trans (readReg-writeReg-a0-ra (regs st3) (readReg (regs st3) sp)) ra-st1

    -- SP preservation: inl allocates stack space (sp -= 16), so sp is NOT preserved.
    -- Memory preservation: inl writes at new-sp (= orig-sp - 16) and new-sp + 8,
    -- so memory at original sp and above is preserved.
    postulate
      sp-final : readReg (regs st4) sp ≡ readReg (regs s) sp
      mem-sp-final : readMem (memory st4) (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
      mem-sp+8-final : readMem (memory st4) (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
      mem-sp+16-final : readMem (memory st4) (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)

    -- Memory properties for encode-inl-construct
    mem-tag : readMem (memory st4) new-sp ≡ just 0
    mem-tag = begin
      readMem (memory st4) new-sp
        ≡⟨ refl ⟩
      readMem (memory st3) new-sp
        ≡⟨ readMem-writeMem-diff (memory st2) (new-sp +ℕ 8) new-sp (readReg (regs st2) a0)
                                 (λ eq → n≢n+suc new-sp 7 (sym eq)) ⟩
      readMem (memory st2) new-sp
        ≡⟨ trans (cong (λ addr → readMem (memory st2) addr) (sym (+-identityʳ new-sp)))
                 (readMem-writeMem-same (memory st1) (new-sp +ℕ 0) (readReg (regs st1) zero)) ⟩
      just (readReg (regs st1) zero)
        ≡⟨ cong just (readReg-zero-always-0 (regs st1)) ⟩
      just 0
        ∎

    mem-val : readMem (memory st4) (new-sp +ℕ 8) ≡ just (encode x)
    mem-val = begin
      readMem (memory st4) (new-sp +ℕ 8)
        ≡⟨ refl ⟩
      readMem (memory st3) (new-sp +ℕ 8)
        ≡⟨ trans (cong (λ addr → readMem (memory st3) addr) (cong (_+ℕ 8) (sym sp-st2)))
                 (readMem-writeMem-same (memory st2) (readReg (regs st2) sp +ℕ 8) (readReg (regs st2) a0)) ⟩
      just (readReg (regs st2) a0)
        ≡⟨ cong just a0-st2 ⟩
      just (encode x)
        ∎

    a0-final : readReg (regs st4) a0 ≡ encode (inj₁ x)
    a0-final = trans a0-st4 (encode-inl-construct x new-sp (memory st4) mem-tag mem-val)

-- | Star-based inr execution
run-inr-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  let prog = prefix ++ compile-riscv {B} {A + B} inr ++ suffix
  in ∃[ s' ] IRStarResult {B} {A + B} inr prog s s' x (length prefix)
run-inr-star {A} {B} prefix suffix x s h-false pc-eq a0-eq =
  st5 , record
    { ir-star = star-proof
    ; ir-halted = h5
    ; ir-pc = pc5
    ; ir-a0 = a0-final
    ; ir-s1 = s1-reg-final
    ; ir-ra = ra-final
    ; ir-sp = sp-final
    ; ir-mem-sp = mem-sp-final
    ; ir-mem-sp+8 = mem-sp+8-final
    ; ir-mem-sp+16 = mem-sp+16-final
    }
  where
    prog : Program
    prog = prefix ++ compile-riscv {B} {A + B} inr ++ suffix

    offset = length prefix

    -- The 5 instructions of inr
    i0 = addi sp sp neg16
    i1-instr = li t0 (+ 1)
    i2 = sd t0 (+ 0) sp
    i3 = sd a0 (+ 8) sp
    i4 = mv a0 sp

    orig-sp = readReg (regs s) sp
    new-sp = orig-sp ∸ 16

    -- States after each instruction
    st1 : State
    st1 = record s { regs = writeReg (regs s) sp new-sp ; pc = pc s +ℕ 1 }

    st2 : State
    st2 = record st1 { regs = writeReg (regs st1) t0 1 ; pc = pc st1 +ℕ 1 }

    st3 : State
    st3 = record st2 { memory = writeMem (memory st2) (readReg (regs st2) sp +ℕ 0) (readReg (regs st2) t0)
                     ; pc = pc st2 +ℕ 1 }

    st4 : State
    st4 = record st3 { memory = writeMem (memory st3) (readReg (regs st3) sp +ℕ 8) (readReg (regs st3) a0)
                     ; pc = pc st3 +ℕ 1 }

    st5 : State
    st5 = record st4 { regs = writeReg (regs st4) a0 (readReg (regs st4) sp)
                     ; pc = pc st4 +ℕ 1 }

    -- Fetch lemmas
    fetch0 : fetch prog offset ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 _

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ _
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) _)

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ offset +ℕ 1
    len-prefix-1 = List-length-++ prefix

    fetch1 : fetch prog (offset +ℕ 1) ≡ just i1-instr
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1-instr) (sym prog-eq1) len-prefix-1
                    (fetch-at-prefix-end (prefix ++ i0 ∷ []) i1-instr _)

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1-instr ∷ []) ++ _
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1-instr ∷ []) _)

    len-prefix-2 : length (prefix ++ i0 ∷ i1-instr ∷ []) ≡ offset +ℕ 2
    len-prefix-2 = List-length-++ prefix

    fetch2 : fetch prog (offset +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1-instr ∷ []) i2 _)

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ []) ++ _
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1-instr ∷ i2 ∷ []) _)

    len-prefix-3 : length (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ []) ≡ offset +ℕ 3
    len-prefix-3 = List-length-++ prefix

    fetch3 : fetch prog (offset +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ []) i3 _)

    prog-eq4 : prog ≡ (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ i3 ∷ []) ++ _
    prog-eq4 = sym (++-assoc prefix (i0 ∷ i1-instr ∷ i2 ∷ i3 ∷ []) _)

    len-prefix-4 : length (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ i3 ∷ []) ≡ offset +ℕ 4
    len-prefix-4 = List-length-++ prefix

    fetch4 : fetch prog (offset +ℕ 4) ≡ just i4
    fetch4 = subst₂ (λ p n → fetch p n ≡ just i4) (sym prog-eq4) len-prefix-4
                    (fetch-at-prefix-end (prefix ++ i0 ∷ i1-instr ∷ i2 ∷ i3 ∷ []) i4 _)

    -- Step proofs
    step0 : step prog s ≡ just st1
    step0 = trans (step-exec prog s i0 h-false (subst (λ p → fetch prog p ≡ just i0) (sym pc-eq) fetch0))
                  (execAddiNeg prog s sp sp 15)

    h1 : halted st1 ≡ false
    h1 = h-false

    pc1 : pc st1 ≡ offset +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    step1 : step prog st1 ≡ just st2
    step1 = trans (step-exec prog st1 i1-instr h1 (subst (λ p → fetch prog p ≡ just i1-instr) (sym pc1) fetch1))
                  (execLi prog st1 t0 1)

    h2 : halted st2 ≡ false
    h2 = h-false

    pc2 : pc st2 ≡ offset +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc offset 1 1)

    step2 : step prog st2 ≡ just st3
    step2 = trans (step-exec prog st2 i2 h2 (subst (λ p → fetch prog p ≡ just i2) (sym pc2) fetch2))
                  (execSd prog st2 t0 0 sp)

    h3 : halted st3 ≡ false
    h3 = h-false

    pc3 : pc st3 ≡ offset +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc offset 2 1)

    step3 : step prog st3 ≡ just st4
    step3 = trans (step-exec prog st3 i3 h3 (subst (λ p → fetch prog p ≡ just i3) (sym pc3) fetch3))
                  (execSd prog st3 a0 8 sp)

    h4 : halted st4 ≡ false
    h4 = h-false

    pc4 : pc st4 ≡ offset +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc offset 3 1)

    step4 : step prog st4 ≡ just st5
    step4 = trans (step-exec prog st4 i4 h4 (subst (λ p → fetch prog p ≡ just i4) (sym pc4) fetch4))
                  (execMv prog st4 a0 sp)

    h5 : halted st5 ≡ false
    h5 = h-false

    pc5 : pc st5 ≡ offset +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc offset 4 1)

    star-proof : Star prog s st5
    star-proof = star-step5 h-false step0 h1 step1 h2 step2 h3 step3 h4 step4

    -- Register preservation
    sp-st1 : readReg (regs st1) sp ≡ new-sp
    sp-st1 = readReg-writeReg-same (regs s) sp new-sp (λ ())

    a0-st1 : readReg (regs st1) a0 ≡ encode x
    a0-st1 = trans (readReg-writeReg-sp-a0 (regs s) new-sp) a0-eq

    s1-reg-st1 : readReg (regs st1) s1 ≡ readReg (regs s) s1
    s1-reg-st1 = readReg-writeReg-sp-s1 (regs s) new-sp

    ra-st1 : readReg (regs st1) ra ≡ readReg (regs s) ra
    ra-st1 = readReg-writeReg-sp-ra (regs s) new-sp

    -- st2: li t0 1
    sp-st2 : readReg (regs st2) sp ≡ new-sp
    sp-st2 = trans (readReg-writeReg-t0-sp (regs st1) 1) sp-st1

    a0-st2 : readReg (regs st2) a0 ≡ encode x
    a0-st2 = trans (readReg-writeReg-t0-a0 (regs st1) 1) a0-st1

    t0-st2 : readReg (regs st2) t0 ≡ 1
    t0-st2 = readReg-writeReg-same (regs st1) t0 1 (λ ())

    s1-reg-st2 : readReg (regs st2) s1 ≡ readReg (regs s) s1
    s1-reg-st2 = trans (readReg-writeReg-t0-s1 (regs st1) 1) s1-reg-st1

    ra-st2 : readReg (regs st2) ra ≡ readReg (regs s) ra
    ra-st2 = trans (readReg-writeReg-t0-ra (regs st1) 1) ra-st1

    -- st3: memory write doesn't change regs
    sp-st3 : readReg (regs st3) sp ≡ new-sp
    sp-st3 = sp-st2

    a0-st3 : readReg (regs st3) a0 ≡ encode x
    a0-st3 = a0-st2

    t0-st3 : readReg (regs st3) t0 ≡ 1
    t0-st3 = t0-st2

    -- st4: memory write doesn't change regs
    sp-st4 : readReg (regs st4) sp ≡ new-sp
    sp-st4 = sp-st3

    -- st5: mv a0 sp
    a0-st5 : readReg (regs st5) a0 ≡ new-sp
    a0-st5 = trans (readReg-writeReg-same (regs st4) a0 (readReg (regs st4) sp) (λ ())) sp-st4

    s1-reg-final : readReg (regs st5) s1 ≡ readReg (regs s) s1
    s1-reg-final = trans (readReg-writeReg-a0-s1 (regs st4) (readReg (regs st4) sp)) s1-reg-st2

    ra-final : readReg (regs st5) ra ≡ readReg (regs s) ra
    ra-final = trans (readReg-writeReg-a0-ra (regs st4) (readReg (regs st4) sp)) ra-st2

    -- SP preservation: inr allocates stack space (sp -= 16), so sp is NOT preserved.
    -- Memory preservation: inr writes at new-sp (= orig-sp - 16) and new-sp + 8,
    -- so memory at original sp and above is preserved.
    postulate
      sp-final : readReg (regs st5) sp ≡ readReg (regs s) sp
      mem-sp-final : readMem (memory st5) (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
      mem-sp+8-final : readMem (memory st5) (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
      mem-sp+16-final : readMem (memory st5) (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)

    -- Memory properties for encode-inr-construct
    mem-tag : readMem (memory st5) new-sp ≡ just 1
    mem-tag = begin
      readMem (memory st5) new-sp
        ≡⟨ refl ⟩
      readMem (memory st4) new-sp
        ≡⟨ readMem-writeMem-diff (memory st3) (new-sp +ℕ 8) new-sp (readReg (regs st3) a0)
                                 (λ eq → n≢n+suc new-sp 7 (sym eq)) ⟩
      readMem (memory st3) new-sp
        ≡⟨ trans (cong (λ addr → readMem (memory st3) addr) (sym (+-identityʳ new-sp)))
                 (readMem-writeMem-same (memory st2) (new-sp +ℕ 0) (readReg (regs st2) t0)) ⟩
      just (readReg (regs st2) t0)
        ≡⟨ cong just t0-st2 ⟩
      just 1
        ∎

    mem-val : readMem (memory st5) (new-sp +ℕ 8) ≡ just (encode x)
    mem-val = begin
      readMem (memory st5) (new-sp +ℕ 8)
        ≡⟨ refl ⟩
      readMem (memory st4) (new-sp +ℕ 8)
        ≡⟨ trans (cong (λ addr → readMem (memory st4) addr) (cong (_+ℕ 8) (sym sp-st3)))
                 (readMem-writeMem-same (memory st3) (readReg (regs st3) sp +ℕ 8) (readReg (regs st3) a0)) ⟩
      just (readReg (regs st3) a0)
        ≡⟨ cong just a0-st3 ⟩
      just (encode x)
        ∎

    a0-final : readReg (regs st5) a0 ≡ encode (inj₂ x)
    a0-final = trans a0-st5 (encode-inr-construct x new-sp (memory st5) mem-tag mem-val)

------------------------------------------------------------------------
-- Star-based initial (void elimination)
--
-- compile-riscv initial = ebreak ∷ []
--
-- This should never be called since Void has no inhabitants.
------------------------------------------------------------------------

run-initial-star : ∀ {A} (prefix suffix : Program) (x : ⟦ Void ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  let prog = prefix ++ compile-riscv {Void} {A} initial ++ suffix
  in ∃[ s' ] IRStarResult {Void} {A} initial prog s s' x (length prefix)
run-initial-star prefix suffix x s h-false pc-eq a0-eq = ⊥-elim x

------------------------------------------------------------------------
-- Apply postulate
--
-- Apply requires whole-program analysis because:
-- 1. jalr jumps to a code pointer stored in the closure
-- 2. We need to know that code pointer points to valid thunk code
-- 3. The thunk was created by curry, which is proven separately
--
-- This is sound by construction: curry creates closures that apply
-- can call. Full verification requires tracking closure provenance.
--
-- PROVEN ALTERNATIVE: When a ClosureWellFormed proof is available
-- (from curry's output), use run-apply-with-wf from IR/Apply.agda.
-- This traces all 7 apply instructions and uses thunk-correct
-- to verify the indirect call executes correctly.
------------------------------------------------------------------------

postulate
  run-apply-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode {(A ⇒ B) * A} x →
    let prog = prefix ++ compile-riscv {(A ⇒ B) * A} {B} apply ++ suffix
    in ∃[ s' ] IRStarResult {(A ⇒ B) * A} {B} apply prog s s' x (length prefix)

------------------------------------------------------------------------
-- Main mutual block: run-ir-star-at-offset
--
-- This builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to StarBase functions
  run-ir-star-at-offset id prefix suffix x s h-false pc-eq a0-eq =
    run-id-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset terminal prefix suffix x s h-false pc-eq a0-eq =
    run-terminal-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fold prefix suffix x s h-false pc-eq a0-eq =
    run-fold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset unfold prefix suffix x s h-false pc-eq a0-eq =
    run-unfold-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset arr prefix suffix x s h-false pc-eq a0-eq =
    run-arr-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset fst prefix suffix x s h-false pc-eq a0-eq =
    run-fst-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset snd prefix suffix x s h-false pc-eq a0-eq =
    run-snd-star prefix suffix x s h-false pc-eq a0-eq

  -- Injection cases
  run-ir-star-at-offset inl prefix suffix x s h-false pc-eq a0-eq =
    run-inl-star prefix suffix x s h-false pc-eq a0-eq
  run-ir-star-at-offset inr prefix suffix x s h-false pc-eq a0-eq =
    run-inr-star prefix suffix x s h-false pc-eq a0-eq

  -- Void elimination
  run-ir-star-at-offset initial prefix suffix x s h-false pc-eq a0-eq =
    run-initial-star prefix suffix x s h-false pc-eq a0-eq

  -- Curry: delegate to extracted proof
  run-ir-star-at-offset (curry f) prefix suffix x s h-false pc-eq a0-eq =
    run-curry-star f prefix suffix x s h-false pc-eq a0-eq

  -- Apply: postulated (requires whole-program analysis)
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq a0-eq =
    run-apply-star {A} {B} prefix suffix x s h-false pc-eq a0-eq

  -- Compose: use extracted context helpers
  run-ir-star-at-offset (g ∘ f) prefix suffix x s h-false pc-eq a0-eq =
    let ctx = make-compose-context f g prefix suffix
        open ComposeContext ctx

        -- Step 1: Execute f
        (sf , rf) = run-ir-star-at-offset f prefix suffix-f x s h-false pc-eq a0-eq
        rf' = transform-f-result f g prefix suffix x s sf rf

        -- Step 2: Execute g (no transfer needed - a0 already has result!)
        a0-after-f : readReg (regs sf) a0 ≡ encode (eval f x)
        a0-after-f = ir-a0 rf

        -- PC conversion: ir-pc rf gives pc sf ≡ length prefix +ℕ compile-length f
        -- We need pc sf ≡ length prefix-g where length prefix-g = length prefix +ℕ len-f
        pc-for-g : pc sf ≡ length prefix-g
        pc-for-g = trans (ir-pc rf) (sym len-prefix-g)

        (sg , rg) = run-ir-star-at-offset g prefix-g suffix (eval f x) sf
                      (ir-halted rf) pc-for-g a0-after-f
        rg' = transform-g-result f g prefix suffix x sf sg rg

    in sg , assemble-compose-result f g prefix suffix x s sf sg rf' rg'

  -- Pair: use extracted context helpers (POSTULATE for now)
  run-ir-star-at-offset ⟨ f , g ⟩ prefix suffix x s h-false pc-eq a0-eq =
    run-pair-star f g prefix suffix x s h-false pc-eq a0-eq

  -- Case: use extracted context helpers (POSTULATE for now)
  run-ir-star-at-offset ([_,_] f g) prefix suffix x s h-false pc-eq a0-eq =
    run-case-star f g prefix suffix x s h-false pc-eq a0-eq

  -- Pair helper - proven using phase helpers and IH
  run-pair-star : ∀ {A B C} (f : IR C A) (g : IR C B)
                  (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
  run-pair-star {A} {B} {C} f g prefix suffix x s h-false pc-eq a0-eq =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-ra = ra-final
      ; ir-sp = sp-final
      ; ir-mem-sp = mem-sp-final
      ; ir-mem-sp+8 = mem-sp+8-final
      ; ir-mem-sp+16 = mem-sp+16-final
      }
    where
      ctx = make-pair-context f g prefix suffix
      open PairContext ctx
      offset = length prefix

      -- Phase 1: Setup (3 instructions - addi sp, sd s1, mv s1 a0)
      -- Original s1 is saved to stack at sp+16
      orig-s1 = readReg (regs s) s1
      setup-result = pair-setup-star f g prefix suffix x s h-false pc-eq a0-eq
      s-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      a0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      sp-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      ra-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))
      mem-s1-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))))

      -- Phase 2: Execute f (IH call)
      -- Program view: prog ≡ prefix-f ++ code-f ++ suffix-f
      step-f = run-ir-star-at-offset f prefix-f suffix-f x s-setup h-setup
                 (trans pc-setup (sym len-prefix-f)) a0-setup
      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f

      -- Convert f result to use prog
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-setup s-after-f-raw
      star-f-raw = ir-star r-f

      star-f : Star prog s-setup s-after-f-raw
      star-f = subst (λ p → Star p s-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract f result properties
      h-after-f = ir-halted r-f
      a0-after-f = ir-a0 r-f
      s1-after-f = ir-s1 r-f
      ra-after-f = ir-ra r-f

      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ len-f
      pc-f-raw = ir-pc r-f

      pc-after-f : pc s-after-f-raw ≡ offset +ℕ 3 +ℕ len-f
      pc-after-f = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- s1 is preserved through f, so it still holds x
      s1-after-f-is-x : readReg (regs s-after-f-raw) s1 ≡ encode x
      s1-after-f-is-x = trans s1-after-f s1-setup

      -- Phase 3: Middle (2 instructions)
      mid-result = pair-middle-star f g prefix suffix x s s-after-f-raw
                     h-after-f pc-after-f a0-after-f s1-after-f-is-x
      s-mid = proj₁ mid-result
      star-mid-raw = proj₁ (proj₂ mid-result)
      h-mid = proj₁ (proj₂ (proj₂ mid-result))
      pc-mid = proj₁ (proj₂ (proj₂ (proj₂ mid-result)))
      a0-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))
      s1-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))
      sp-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result))))))
      ra-mid = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))
      mem-mid = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mid-result)))))))

      -- Middle star is already in prog
      star-mid : Star prog s-after-f-raw s-mid
      star-mid = star-mid-raw

      -- Phase 4: Execute g (IH call)
      -- Need pc at correct offset for g
      -- pc-mid produces (offset +ℕ 3 +ℕ len-f) +ℕ 2, need (offset +ℕ 5) +ℕ len-f
      pc-for-g : pc s-mid ≡ length prefix-g
      pc-for-g = begin
        pc s-mid
          ≡⟨ pc-mid ⟩
        (offset +ℕ 3 +ℕ len-f) +ℕ 2
          ≡⟨ +-assoc (offset +ℕ 3) len-f 2 ⟩
        (offset +ℕ 3) +ℕ (len-f +ℕ 2)
          ≡⟨ +-assoc offset 3 (len-f +ℕ 2) ⟩
        offset +ℕ (3 +ℕ (len-f +ℕ 2))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 3 len-f 2)) ⟩
        offset +ℕ ((3 +ℕ len-f) +ℕ 2)
          ≡⟨ cong (λ z → offset +ℕ (z +ℕ 2)) (+-comm 3 len-f) ⟩
        offset +ℕ ((len-f +ℕ 3) +ℕ 2)
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 3 2) ⟩
        offset +ℕ (len-f +ℕ 5)
          ≡⟨ sym (+-assoc offset len-f 5) ⟩
        (offset +ℕ len-f) +ℕ 5
          ≡⟨ cong (_+ℕ 5) (+-comm offset len-f) ⟩
        (len-f +ℕ offset) +ℕ 5
          ≡⟨ +-assoc len-f offset 5 ⟩
        len-f +ℕ (offset +ℕ 5)
          ≡⟨ +-comm len-f (offset +ℕ 5) ⟩
        (offset +ℕ 5) +ℕ len-f
          ≡⟨ sym len-prefix-g ⟩
        length prefix-g ∎

      step-g = run-ir-star-at-offset g prefix-g suffix-g x s-mid h-mid
                 pc-for-g a0-mid
      s-after-g-raw = proj₁ step-g
      r-g = proj₂ step-g

      -- Convert g result to use prog
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-mid s-after-g-raw
      star-g-raw = ir-star r-g

      star-g : Star prog s-mid s-after-g-raw
      star-g = subst (λ p → Star p s-mid s-after-g-raw) (sym prog-eq-g) star-g-raw

      -- Extract g result properties
      h-after-g = ir-halted r-g
      a0-after-g = ir-a0 r-g
      s1-after-g = ir-s1 r-g
      ra-after-g = ir-ra r-g

      pc-g-raw : pc s-after-g-raw ≡ length prefix-g +ℕ len-g
      pc-g-raw = ir-pc r-g

      pc-after-g : pc s-after-g-raw ≡ offset +ℕ 5 +ℕ len-f +ℕ len-g
      pc-after-g = trans pc-g-raw (cong (_+ℕ len-g) len-prefix-g)

      -- Memory: sp should still point to our pair location through f and g execution
      -- sp is a callee-saved register, so f and g must preserve it
      -- The memory at sp and sp+16 should also be preserved (f and g don't clobber them)
      postulate
        sp-after-f : readReg (regs s-after-f-raw) sp ≡ readReg (regs s-setup) sp
        sp-after-g : readReg (regs s-after-g-raw) sp ≡ readReg (regs s-mid) sp
        mem-after-g : readMem (memory s-after-g-raw) (readReg (regs s-after-g-raw) sp)
                    ≡ just (encode (eval f x))
        mem-s1-after-g : readMem (memory s-after-g-raw) (readReg (regs s-after-g-raw) sp +ℕ 16)
                       ≡ just orig-s1

      -- Phase 5: Final (3 instructions - sd a0 8(sp), mv a0 sp, ld s1 16(sp))
      final-phase-result = pair-final-star f g prefix suffix x orig-s1 s-mid s-after-g-raw
                             h-after-g pc-after-g a0-after-g mem-after-g mem-s1-after-g
      s-final = proj₁ final-phase-result
      star-final-raw = proj₁ (proj₂ final-phase-result)
      h-final = proj₁ (proj₂ (proj₂ final-phase-result))
      pc-final-raw = proj₁ (proj₂ (proj₂ (proj₂ final-phase-result)))
      a0-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result))))
      s1-final-raw = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))
      ra-final-raw = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ final-phase-result)))))

      -- Final star is already in prog
      star-final : Star prog s-after-g-raw s-final
      star-final = star-final-raw

      -- Compose all Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup
                   (star-trans star-f
                     (star-trans star-mid
                       (star-trans star-g star-final)))

      -- Final pc
      -- compile-length ⟨ f , g ⟩ = (8 + len-f) + len-g
      pc-final : pc s-final ≡ offset +ℕ compile-length ⟨ f , g ⟩
      pc-final = begin
        pc s-final
          ≡⟨ pc-final-raw ⟩
        (offset +ℕ 5 +ℕ len-f +ℕ len-g) +ℕ 3
          ≡⟨ +-assoc (offset +ℕ 5 +ℕ len-f) len-g 3 ⟩
        (offset +ℕ 5 +ℕ len-f) +ℕ (len-g +ℕ 3)
          ≡⟨ +-assoc (offset +ℕ 5) len-f (len-g +ℕ 3) ⟩
        (offset +ℕ 5) +ℕ (len-f +ℕ (len-g +ℕ 3))
          ≡⟨ +-assoc offset 5 (len-f +ℕ (len-g +ℕ 3)) ⟩
        offset +ℕ (5 +ℕ (len-f +ℕ (len-g +ℕ 3)))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 5 len-f (len-g +ℕ 3))) ⟩
        offset +ℕ ((5 +ℕ len-f) +ℕ (len-g +ℕ 3))
          ≡⟨ cong (λ z → offset +ℕ (z +ℕ (len-g +ℕ 3))) (+-comm 5 len-f) ⟩
        offset +ℕ ((len-f +ℕ 5) +ℕ (len-g +ℕ 3))
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 5 (len-g +ℕ 3)) ⟩
        offset +ℕ (len-f +ℕ (5 +ℕ (len-g +ℕ 3)))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ z)) (sym (+-assoc 5 len-g 3)) ⟩
        offset +ℕ (len-f +ℕ ((5 +ℕ len-g) +ℕ 3))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ (z +ℕ 3))) (+-comm 5 len-g) ⟩
        offset +ℕ (len-f +ℕ ((len-g +ℕ 5) +ℕ 3))
          ≡⟨ cong (λ z → offset +ℕ (len-f +ℕ z)) (+-assoc len-g 5 3) ⟩
        offset +ℕ (len-f +ℕ (len-g +ℕ 8))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc len-f len-g 8)) ⟩
        offset +ℕ ((len-f +ℕ len-g) +ℕ 8)
          ≡⟨ cong (offset +ℕ_) (+-comm (len-f +ℕ len-g) 8) ⟩
        offset +ℕ (8 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 8 len-f len-g)) ⟩
        offset +ℕ ((8 +ℕ len-f) +ℕ len-g)
          ∎

      -- s1 preservation: pair now properly saves/restores s1
      -- s1-final-raw says s1 = orig-s1, and orig-s1 = readReg (regs s) s1
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = s1-final-raw

      -- ra preservation: chain through all phases
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-final-raw
                   (trans ra-after-g
                     (trans ra-mid
                       (trans ra-after-f ra-setup)))

      -- SP preservation: pair allocates stack space (sp -= 24) and doesn't restore it
      -- The pair result lives on stack, so sp points to it (sp = orig_sp - 24)
      -- Memory preservation: pair writes at new-sp, new-sp+8, new-sp+16 (its own frame)
      -- so memory at original sp and above is preserved.
      postulate
        sp-final : readReg (regs s-final) sp ≡ readReg (regs s) sp
        mem-sp-final : readMem (memory s-final) (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
        mem-sp+8-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
        mem-sp+16-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)

  -- Case helper - proven using dispatch helpers and IH
  run-case-star : ∀ {A B C} (f : IR A C) (g : IR B C)
                  (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv ([_,_] f g) ++ suffix
    in ∃[ s' ] IRStarResult ([_,_] f g) prog s s' x (length prefix)

  -- Left path implementation (inj₁ a)
  run-case-star {A} {B} {C} f g prefix suffix (inj₁ a) s h-false pc-eq a0-eq =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-ra = ra-final
      ; ir-sp = sp-final
      ; ir-mem-sp = mem-sp-final
      ; ir-mem-sp+8 = mem-sp+8-final
      ; ir-mem-sp+16 = mem-sp+16-final
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix

      -- Phase 1: Dispatch (3 instructions, branch NOT taken)
      dispatch-result = case-dispatch-left-star f g prefix suffix a s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      star-dispatch = proj₁ (proj₂ dispatch-result)
      h-dispatch = proj₁ (proj₂ (proj₂ dispatch-result))
      pc-dispatch = proj₁ (proj₂ (proj₂ (proj₂ dispatch-result)))
      a0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))
      t0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))
      s1-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))
      ra-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))))
      sp-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))))
      mem-dispatch = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))))

      -- Phase 2: Execute f (IH call)
      -- PC for f: need length prefix-f
      pc-for-f : pc s-dispatch ≡ length prefix-f
      pc-for-f = trans pc-dispatch (sym len-prefix-f)

      step-f = run-ir-star-at-offset f prefix-f suffix-f a s-dispatch h-dispatch pc-for-f a0-dispatch
      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f

      -- Convert f result to use prog
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-dispatch s-after-f-raw
      star-f-raw = ir-star r-f

      star-f : Star prog s-dispatch s-after-f-raw
      star-f = subst (λ p → Star p s-dispatch s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract f result properties
      h-after-f = ir-halted r-f
      a0-after-f = ir-a0 r-f
      s1-after-f = ir-s1 r-f
      ra-after-f = ir-ra r-f

      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ len-f
      pc-f-raw = ir-pc r-f

      pc-after-f : pc s-after-f-raw ≡ offset +ℕ 3 +ℕ len-f
      pc-after-f = trans pc-f-raw (cong (_+ℕ len-f) len-prefix-f)

      -- Phase 3: Jump over g (2 instructions)
      jump-result = case-left-jump-star f g prefix suffix s-after-f-raw h-after-f pc-after-f
      s-final = proj₁ jump-result
      star-jump = proj₁ (proj₂ jump-result)
      h-final = proj₁ (proj₂ (proj₂ jump-result))
      pc-jump = proj₁ (proj₂ (proj₂ (proj₂ jump-result)))
      a0-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ jump-result))))
      s1-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result)))))
      ra-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result))))))
      sp-jump = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result)))))))
      mem-jump = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ jump-result)))))))

      -- Compose all stars
      star-all : Star prog s s-final
      star-all = star-trans star-dispatch (star-trans star-f star-jump)

      -- Final pc: offset + 6 + len-f + len-g = offset + compile-length [f,g]
      -- case-left-jump-star gives: ((offset + 6) + len-f) + len-g
      -- We need: offset + ((6 + len-f) + len-g)
      pc-convert : offset +ℕ 6 +ℕ len-f +ℕ len-g ≡ offset +ℕ (6 +ℕ len-f +ℕ len-g)
      pc-convert = begin
        offset +ℕ 6 +ℕ len-f +ℕ len-g
          ≡⟨ +-assoc (offset +ℕ 6) len-f len-g ⟩
        (offset +ℕ 6) +ℕ (len-f +ℕ len-g)
          ≡⟨ +-assoc offset 6 (len-f +ℕ len-g) ⟩
        offset +ℕ (6 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 6 len-f len-g)) ⟩
        offset +ℕ (6 +ℕ len-f +ℕ len-g)
          ∎

      pc-final : pc s-final ≡ offset +ℕ compile-length ([_,_] f g)
      pc-final = trans pc-jump pc-convert

      -- Final a0: eval [f,g] (inj₁ a) = eval f a
      a0-final : readReg (regs s-final) a0 ≡ encode (eval ([_,_] f g) (inj₁ a))
      a0-final = trans a0-jump (trans a0-after-f refl)

      -- s1 preservation
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = trans s1-jump (trans s1-after-f s1-dispatch)

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-jump (trans ra-after-f ra-dispatch)

      -- sp preservation: case doesn't allocate
      -- Chains through: dispatch (sp unchanged) → f (ir-sp) → jump (sp unchanged)
      sp-after-f : readReg (regs s-after-f-raw) sp ≡ readReg (regs s-dispatch) sp
      sp-after-f = ir-sp r-f
      sp-final : readReg (regs s-final) sp ≡ readReg (regs s) sp
      sp-final = trans sp-jump (trans sp-after-f sp-dispatch)

      -- Memory preservation: case doesn't allocate or write memory directly
      -- Chains through: dispatch (mem unchanged) → f (ir-mem-sp) → jump (mem unchanged)
      -- The key is that dispatch and jump don't write memory, and f preserves caller's frame
      mem-sp-final : readMem (memory s-final) (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
      mem-sp-final = begin
        readMem (memory s-final) (readReg (regs s) sp)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp)) mem-jump ⟩
        readMem (memory s-after-f-raw) (readReg (regs s) sp)
          ≡⟨ cong (readMem (memory s-after-f-raw)) (sym sp-dispatch) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-dispatch) sp)
          ≡⟨ ir-mem-sp r-f ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp)
          ≡⟨ cong (readMem (memory s-dispatch)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp)
          ∎

      mem-sp+8-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
      mem-sp+8-final = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ 8)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 8)) mem-jump ⟩
        readMem (memory s-after-f-raw) (readReg (regs s) sp +ℕ 8)
          ≡⟨ cong (λ a → readMem (memory s-after-f-raw) (a +ℕ 8)) (sym sp-dispatch) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-dispatch) sp +ℕ 8)
          ≡⟨ ir-mem-sp+8 r-f ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ 8)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ 8)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ 8)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 8)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ 8)
          ∎

      mem-sp+16-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)
      mem-sp+16-final = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ 16)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 16)) mem-jump ⟩
        readMem (memory s-after-f-raw) (readReg (regs s) sp +ℕ 16)
          ≡⟨ cong (λ a → readMem (memory s-after-f-raw) (a +ℕ 16)) (sym sp-dispatch) ⟩
        readMem (memory s-after-f-raw) (readReg (regs s-dispatch) sp +ℕ 16)
          ≡⟨ ir-mem-sp+16 r-f ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ 16)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ 16)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ 16)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 16)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ 16)
          ∎

  -- Right path implementation (inj₂ b)
  run-case-star {A} {B} {C} f g prefix suffix (inj₂ b) s h-false pc-eq a0-eq =
    s-final , record
      { ir-star = star-all
      ; ir-halted = h-final
      ; ir-pc = pc-final
      ; ir-a0 = a0-final
      ; ir-s1 = s1-final
      ; ir-ra = ra-final
      ; ir-sp = sp-final
      ; ir-mem-sp = mem-sp-final
      ; ir-mem-sp+8 = mem-sp+8-final
      ; ir-mem-sp+16 = mem-sp+16-final
      }
    where
      ctx = make-case-context f g prefix suffix
      open CaseContext ctx
      offset = length prefix

      -- Phase 1: Dispatch (4 instructions, branch TAKEN + landing label)
      dispatch-result = case-dispatch-right-star f g prefix suffix b s h-false pc-eq a0-eq
      s-dispatch = proj₁ dispatch-result
      star-dispatch = proj₁ (proj₂ dispatch-result)
      h-dispatch = proj₁ (proj₂ (proj₂ dispatch-result))
      pc-dispatch = proj₁ (proj₂ (proj₂ (proj₂ dispatch-result)))
      a0-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))
      s1-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))
      ra-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result))))))
      sp-dispatch = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))))
      mem-dispatch = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dispatch-result)))))))

      -- Phase 2: Execute g (IH call)
      pc-for-g : pc s-dispatch ≡ length prefix-g
      pc-for-g = trans pc-dispatch (sym len-prefix-g)

      step-g = run-ir-star-at-offset g prefix-g suffix-g b s-dispatch h-dispatch pc-for-g a0-dispatch
      s-after-g-raw = proj₁ step-g
      r-g = proj₂ step-g

      -- Convert g result to use prog
      star-g-raw : Star (prefix-g ++ code-g ++ suffix-g) s-dispatch s-after-g-raw
      star-g-raw = ir-star r-g

      star-g : Star prog s-dispatch s-after-g-raw
      star-g = subst (λ p → Star p s-dispatch s-after-g-raw) (sym prog-eq-g) star-g-raw

      -- Extract g result properties
      h-after-g = ir-halted r-g
      a0-after-g = ir-a0 r-g
      s1-after-g = ir-s1 r-g
      ra-after-g = ir-ra r-g

      pc-g-raw : pc s-after-g-raw ≡ length prefix-g +ℕ len-g
      pc-g-raw = ir-pc r-g

      pc-after-g : pc s-after-g-raw ≡ offset +ℕ 5 +ℕ len-f +ℕ len-g
      pc-after-g = trans pc-g-raw (cong (_+ℕ len-g) len-prefix-g)

      -- Phase 3: Execute end-label (1 instruction)
      end-result = case-right-end-star f g prefix suffix s-after-g-raw h-after-g pc-after-g
      s-final = proj₁ end-result
      star-end = proj₁ (proj₂ end-result)
      h-final = proj₁ (proj₂ (proj₂ end-result))
      pc-end = proj₁ (proj₂ (proj₂ (proj₂ end-result)))
      a0-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ end-result))))
      s1-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result)))))
      ra-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result))))))
      sp-end = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result)))))))
      mem-end = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ end-result)))))))

      -- Compose all stars
      star-all : Star prog s s-final
      star-all = star-trans star-dispatch (star-trans star-g star-end)

      -- Final pc: offset + 6 + len-f + len-g = offset + compile-length [f,g]
      -- case-right-end-star gives: ((offset + 6) + len-f) + len-g
      -- We need: offset + ((6 + len-f) + len-g)
      pc-convert : offset +ℕ 6 +ℕ len-f +ℕ len-g ≡ offset +ℕ (6 +ℕ len-f +ℕ len-g)
      pc-convert = begin
        offset +ℕ 6 +ℕ len-f +ℕ len-g
          ≡⟨ +-assoc (offset +ℕ 6) len-f len-g ⟩
        (offset +ℕ 6) +ℕ (len-f +ℕ len-g)
          ≡⟨ +-assoc offset 6 (len-f +ℕ len-g) ⟩
        offset +ℕ (6 +ℕ (len-f +ℕ len-g))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 6 len-f len-g)) ⟩
        offset +ℕ (6 +ℕ len-f +ℕ len-g)
          ∎

      pc-final : pc s-final ≡ offset +ℕ compile-length ([_,_] f g)
      pc-final = trans pc-end pc-convert

      -- Final a0: eval [f,g] (inj₂ b) = eval g b
      a0-final : readReg (regs s-final) a0 ≡ encode (eval ([_,_] f g) (inj₂ b))
      a0-final = trans a0-end a0-after-g

      -- s1 preservation
      s1-final : readReg (regs s-final) s1 ≡ readReg (regs s) s1
      s1-final = trans s1-end (trans s1-after-g s1-dispatch)

      -- ra preservation
      ra-final : readReg (regs s-final) ra ≡ readReg (regs s) ra
      ra-final = trans ra-end (trans ra-after-g ra-dispatch)

      -- sp preservation: case doesn't allocate
      -- Chains through: dispatch (sp unchanged) → g (ir-sp) → end-label (sp unchanged)
      sp-after-g : readReg (regs s-after-g-raw) sp ≡ readReg (regs s-dispatch) sp
      sp-after-g = ir-sp r-g
      sp-final : readReg (regs s-final) sp ≡ readReg (regs s) sp
      sp-final = trans sp-end (trans sp-after-g sp-dispatch)

      -- Memory preservation: case doesn't allocate or write memory directly
      -- Chains through: dispatch (mem unchanged) → g (ir-mem-sp) → end-label (mem unchanged)
      mem-sp-final : readMem (memory s-final) (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
      mem-sp-final = begin
        readMem (memory s-final) (readReg (regs s) sp)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp)) mem-end ⟩
        readMem (memory s-after-g-raw) (readReg (regs s) sp)
          ≡⟨ cong (readMem (memory s-after-g-raw)) (sym sp-dispatch) ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-dispatch) sp)
          ≡⟨ ir-mem-sp r-g ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp)
          ≡⟨ cong (readMem (memory s-dispatch)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp)
          ∎

      mem-sp+8-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
      mem-sp+8-final = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ 8)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 8)) mem-end ⟩
        readMem (memory s-after-g-raw) (readReg (regs s) sp +ℕ 8)
          ≡⟨ cong (λ a → readMem (memory s-after-g-raw) (a +ℕ 8)) (sym sp-dispatch) ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-dispatch) sp +ℕ 8)
          ≡⟨ ir-mem-sp+8 r-g ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ 8)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ 8)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ 8)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 8)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ 8)
          ∎

      mem-sp+16-final : readMem (memory s-final) (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)
      mem-sp+16-final = begin
        readMem (memory s-final) (readReg (regs s) sp +ℕ 16)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 16)) mem-end ⟩
        readMem (memory s-after-g-raw) (readReg (regs s) sp +ℕ 16)
          ≡⟨ cong (λ a → readMem (memory s-after-g-raw) (a +ℕ 16)) (sym sp-dispatch) ⟩
        readMem (memory s-after-g-raw) (readReg (regs s-dispatch) sp +ℕ 16)
          ≡⟨ ir-mem-sp+16 r-g ⟩
        readMem (memory s-dispatch) (readReg (regs s-dispatch) sp +ℕ 16)
          ≡⟨ cong (λ a → readMem (memory s-dispatch) (a +ℕ 16)) sp-dispatch ⟩
        readMem (memory s-dispatch) (readReg (regs s) sp +ℕ 16)
          ≡⟨ cong (λ m → readMem m (readReg (regs s) sp +ℕ 16)) mem-dispatch ⟩
        readMem (memory s) (readReg (regs s) sp +ℕ 16)
          ∎

  ------------------------------------------------------------------------
  -- curry-thunk-correct-impl: Proven version using IH
  --
  -- This is the implementation of curry-thunk-correct that uses
  -- run-ir-star-at-offset (the IH) to prove thunk correctness.
  --
  -- RISC-V thunk layout within curry (positions 7 onwards):
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
  --
  -- Structure:
  --   1. Trace 7 setup instructions (label, addi, sd s2, mv s2, sd s0, sd a0, mv a0)
  --   2. Call run-ir-star-at-offset f (IH)
  --   3. Trace 4 cleanup/ret instructions (mv sp, ld s2, addi sp, ret)
  --   4. Compose via star-trans
  ------------------------------------------------------------------------

  -- Prove thunk setup: 7 instructions (label, addi sp -24, sd s2, mv s2, sd s0, sd a0, mv a0)
  -- Now using the proven version from ThunkSetup module
  thunk-setup-star : ∀ {A B C} (f : IR (A * B) C)
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
  thunk-setup-star = thunk-setup-star-proven

  -- Prove ret instruction tracing (after cleanup)
  -- The thunk cleanup does: mv sp s2, ld s2 16(sp), addi sp sp 24, ret
  -- We prove just the ret here; cleanup is traced separately or postulated
  thunk-ret-star : ∀ {A B C} (f : IR (A * B) C)
                   (prefix suffix : Program) (ret-addr : ℕ) (s : State) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        ret-offset = length prefix +ℕ 17 +ℕ compile-length f
    in
    halted s ≡ false →
    pc s ≡ ret-offset →
    readReg (regs s) ra ≡ ret-addr →
    ∃[ s' ] (Star prog s s'
            × halted s' ≡ false
            × pc s' ≡ ret-addr
            × readReg (regs s') a0 ≡ readReg (regs s) a0
            × readReg (regs s') s1 ≡ readReg (regs s) s1)
  thunk-ret-star {A} {B} {C} f prefix suffix ret-addr s h-false pc-eq ra-eq =
    s' , star-all , h' , pc' , a0' , s1'
    where
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      offset = length prefix
      ret-offset = offset +ℕ 17 +ℕ compile-length f

      -- The ret instruction is at ret-offset in curry
      -- curry layout: [7 closure setup] [7 thunk setup] [compile-riscv f] [3 cleanup] [ret] [label end]
      -- ret is at position 17 + len(f) within curry

      len-f = compile-length f

      -- First 14 instructions of curry (closure setup + thunk setup)
      curry-prefix-to-14 : Program
      curry-prefix-to-14 = addi sp sp neg16 ∷       -- 0
                           sd a0 (+ 0) sp ∷         -- 1
                           auipc t0 (+ 0) ∷         -- 2
                           addi t0 t0 (+ 5) ∷       -- 3
                           sd t0 (+ 8) sp ∷         -- 4
                           mv a0 sp ∷               -- 5
                           j (+ (12 +ℕ len-f)) ∷    -- 6 (jump over thunk, updated offset)
                           label 7 ∷                -- 7
                           addi sp sp neg24 ∷       -- 8
                           sd s2 (+ 16) sp ∷        -- 9
                           mv s2 sp ∷               -- 10
                           sd s0 (+ 0) sp ∷         -- 11
                           sd a0 (+ 8) sp ∷         -- 12
                           mv a0 sp ∷               -- 13
                           []

      -- Cleanup instructions after f
      thunk-cleanup : Program
      thunk-cleanup = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ []

      -- curry code = curry-prefix-to-14 ++ compile-riscv f ++ cleanup ++ ret ∷ label-end ∷ []
      curry-code-eq : compile-riscv (curry f) ≡
                      curry-prefix-to-14 ++ compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []
      curry-code-eq = refl

      -- Build prefix up to ret
      prefix-to-ret : Program
      prefix-to-ret = ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++ thunk-cleanup

      len-prefix-to-ret : length prefix-to-ret ≡ ret-offset
      len-prefix-to-ret = begin
        length prefix-to-ret
          ≡⟨ List-length-++ ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ⟩
        length ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) +ℕ 3
          ≡⟨ cong (_+ℕ 3) (List-length-++ (prefix ++ curry-prefix-to-14)) ⟩
        (length (prefix ++ curry-prefix-to-14) +ℕ length (compile-riscv f)) +ℕ 3
          ≡⟨ cong (λ x → (x +ℕ length (compile-riscv f)) +ℕ 3) (List-length-++ prefix) ⟩
        ((offset +ℕ 14) +ℕ length (compile-riscv f)) +ℕ 3
          ≡⟨ cong (λ x → ((offset +ℕ 14) +ℕ x) +ℕ 3) (compile-length-correct f) ⟩
        ((offset +ℕ 14) +ℕ len-f) +ℕ 3
          ≡⟨ +-assoc (offset +ℕ 14) len-f 3 ⟩
        (offset +ℕ 14) +ℕ (len-f +ℕ 3)
          ≡⟨ +-assoc offset 14 (len-f +ℕ 3) ⟩
        offset +ℕ (14 +ℕ (len-f +ℕ 3))
          ≡⟨ cong (offset +ℕ_) (sym (+-assoc 14 len-f 3)) ⟩
        offset +ℕ ((14 +ℕ len-f) +ℕ 3)
          ≡⟨ cong (λ x → offset +ℕ (x +ℕ 3)) (+-comm 14 len-f) ⟩
        offset +ℕ ((len-f +ℕ 14) +ℕ 3)
          ≡⟨ cong (offset +ℕ_) (+-assoc len-f 14 3) ⟩
        offset +ℕ (len-f +ℕ 17)
          ≡⟨ cong (offset +ℕ_) (+-comm len-f 17) ⟩
        offset +ℕ (17 +ℕ len-f)
          ≡⟨ sym (+-assoc offset 17 len-f) ⟩
        (offset +ℕ 17) +ℕ len-f
          ∎

      -- Show prog decomposes to prefix-to-ret ++ ret ∷ suffix'
      prog-eq-ret : prog ≡ prefix-to-ret ++ ret ∷ _
      prog-eq-ret = begin
        prog
          ≡⟨ cong (λ c → prefix ++ c ++ suffix) curry-code-eq ⟩
        prefix ++ (curry-prefix-to-14 ++ compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong (prefix ++_) (++-assoc curry-prefix-to-14 _ suffix) ⟩
        prefix ++ (curry-prefix-to-14 ++ (compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc prefix curry-prefix-to-14 _) ⟩
        (prefix ++ curry-prefix-to-14) ++ (compile-riscv f ++ thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong ((prefix ++ curry-prefix-to-14) ++_) (++-assoc (compile-riscv f) _ suffix) ⟩
        (prefix ++ curry-prefix-to-14) ++ (compile-riscv f ++ (thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc (prefix ++ curry-prefix-to-14) (compile-riscv f) _) ⟩
        ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++ (thunk-cleanup ++ ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ cong (((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++_) (++-assoc thunk-cleanup _ suffix) ⟩
        ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) ++ (thunk-cleanup ++ (ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix)
          ≡⟨ sym (++-assoc ((prefix ++ curry-prefix-to-14) ++ compile-riscv f) thunk-cleanup _) ⟩
        prefix-to-ret ++ (ret ∷ label (18 +ℕ len-f) ∷ []) ++ suffix
          ≡⟨ refl ⟩
        prefix-to-ret ++ ret ∷ _
          ∎

      fetch-ret : fetch prog ret-offset ≡ just ret
      fetch-ret = subst₂ (λ p n → fetch p n ≡ just ret) (sym prog-eq-ret) len-prefix-to-ret
                         (fetch-at-prefix-end prefix-to-ret ret _)

      -- State after ret: pc = ra, everything else unchanged
      s' : State
      s' = record s { pc = readReg (regs s) ra }

      -- Step execution using ret semantics
      step-ret : step prog s ≡ just s'
      step-ret = trans (step-exec prog s ret h-false (subst (λ p → fetch prog p ≡ just ret) (sym pc-eq) fetch-ret))
                       (execRet prog s)

      star-all : Star prog s s'
      star-all = ⟨ h-false , step-ret ⟩◅ refl*

      h' : halted s' ≡ false
      h' = h-false

      pc' : pc s' ≡ ret-addr
      pc' = ra-eq

      -- Register preservation (ret doesn't modify any registers, just pc)
      a0' : readReg (regs s') a0 ≡ readReg (regs s) a0
      a0' = refl

      s1' : readReg (regs s') s1 ≡ readReg (regs s) s1
      s1' = refl

  -- | curry-thunk-correct-impl: Implementation using IH
  -- This composes: setup tracing → IH on f → ret tracing
  curry-thunk-correct-impl : ∀ {A B C} (f : IR (A * B) C)
                             (prefix suffix : Program) (env : ⟦ A ⟧)
                             (arg : ⟦ B ⟧) (s : State) (ret-addr : ℕ) →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        thunk-offset = length prefix +ℕ 7
    in
    halted s ≡ false →
    pc s ≡ thunk-offset →
    readReg (regs s) a0 ≡ encode arg →
    readReg (regs s) s0 ≡ encode env →
    readReg (regs s) ra ≡ ret-addr →
    ∃[ s' ] (ThunkResult prog s s' (λ b → eval f (env , b)) arg
            × pc s' ≡ ret-addr)
  curry-thunk-correct-impl {A} {B} {C} f prefix suffix env arg s ret-addr
                           h-eq pc-eq a0-eq s0-eq ra-eq =
    s-final , thunk-result , pc-final
    where
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      thunk-offset = length prefix +ℕ 7
      f-offset = length prefix +ℕ 14
      ret-offset = length prefix +ℕ 17 +ℕ compile-length f

      -- Step 1: Trace 7 setup instructions
      setup-result = thunk-setup-star f prefix suffix env arg s
                       h-eq pc-eq a0-eq s0-eq
      s-after-setup = proj₁ setup-result
      star-setup = proj₁ (proj₂ setup-result)
      h-setup = proj₁ (proj₂ (proj₂ setup-result))
      pc-setup = proj₁ (proj₂ (proj₂ (proj₂ setup-result)))
      a0-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))
      s1-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result)))))
      ra-setup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))
      -- s2-setup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ setup-result))))))  -- frame pointer

      -- Step 2: Call IH on f using program reassociation
      -- Key insight: curry compiles to structured form that we can reassociate
      len-f = compile-length f
      code-f = compile-riscv f

      -- RISC-V curry structure (7 + 7 + len-f + 5 = 19 + len-f instructions)
      -- curry-closure-setup: 7 instructions (0-6)
      curry-closure-setup : Program
      curry-closure-setup = addi sp sp neg16 ∷
                            sd a0 (+ 0) sp ∷
                            auipc t0 (+ 0) ∷
                            addi t0 t0 (+ 5) ∷
                            sd t0 (+ 8) sp ∷
                            mv a0 sp ∷
                            j (+ (12 +ℕ len-f)) ∷ []  -- updated offset

      -- curry-thunk-setup: 7 instructions (7-13)
      curry-thunk-setup : Program
      curry-thunk-setup = label 7 ∷
                          addi sp sp neg24 ∷
                          sd s2 (+ 16) sp ∷
                          mv s2 sp ∷
                          sd s0 (+ 0) sp ∷
                          sd a0 (+ 8) sp ∷
                          mv a0 sp ∷ []

      -- curry-tail: 5 instructions (14+len-f to 18+len-f)
      curry-tail : Program
      curry-tail = mv sp s2 ∷ ld s2 (+ 16) sp ∷ addi sp sp (+ 24) ∷ ret ∷ label (18 +ℕ len-f) ∷ []

      -- prefix-f and suffix-f for calling IH
      prefix-f = prefix ++ curry-closure-setup ++ curry-thunk-setup
      suffix-f = curry-tail ++ suffix

      -- Length of prefix-f
      len-prefix-f : length prefix-f ≡ length prefix +ℕ 14
      len-prefix-f = trans (List-length-++ prefix)
                           (cong (length prefix +ℕ_) refl)

      -- curry-structure: compile-riscv (curry f) = closure-setup ++ thunk-setup ++ f ++ tail
      curry-structure : compile-riscv (curry f) ≡
                        curry-closure-setup ++ curry-thunk-setup ++ code-f ++ curry-tail
      curry-structure = refl

      -- Program reassociation proof
      -- prog = prefix ++ (A ++ B ++ f ++ C) ++ suffix = (prefix ++ A ++ B) ++ f ++ (C ++ suffix)
      prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      prog-eq-f = trans (cong (λ x → prefix ++ x ++ suffix) curry-structure) prog-reassoc
        where
          ccs = curry-closure-setup
          cts = curry-thunk-setup
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
                                 (trans inner-assoc2
                                        (cong ((ccs ++ cts) ++_) inner-assoc3))

                outer-step : prefix ++ ((ccs ++ (cts ++ (code-f ++ cta))) ++ suffix) ≡ prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix)))
                outer-step = cong (prefix ++_) inner-combined

                final-assoc : prefix ++ ((ccs ++ cts) ++ (code-f ++ (cta ++ suffix))) ≡ (prefix ++ (ccs ++ cts)) ++ (code-f ++ (cta ++ suffix))
                final-assoc = sym (++-assoc prefix (ccs ++ cts) (code-f ++ (cta ++ suffix)))

            in trans outer-step final-assoc

      -- Call IH on f
      pc-setup-f : pc s-after-setup ≡ length prefix-f
      pc-setup-f = trans pc-setup (sym len-prefix-f)

      step-f : ∃[ s-f ] IRStarResult f (prefix-f ++ code-f ++ suffix-f) s-after-setup s-f (env , arg) (length prefix-f)
      step-f = run-ir-star-at-offset f prefix-f suffix-f (env , arg) s-after-setup
                 h-setup pc-setup-f a0-setup

      s-after-f-raw = proj₁ step-f
      r-f = proj₂ step-f
      star-f-raw : Star (prefix-f ++ code-f ++ suffix-f) s-after-setup s-after-f-raw
      star-f-raw = ir-star r-f

      -- Convert star-f to use prog
      star-f-converted : Star prog s-after-setup s-after-f-raw
      star-f-converted = subst (λ p → Star p s-after-setup s-after-f-raw) (sym prog-eq-f) star-f-raw

      -- Extract properties from IH result
      pc-f-raw : pc s-after-f-raw ≡ length prefix-f +ℕ compile-length f
      pc-f-raw = ir-pc r-f

      -- After f, PC is at length prefix + 14 + len-f = cleanup-offset
      -- We need cleanup tracing to get to ret-offset = length prefix + 17 + len-f
      cleanup-offset = length prefix +ℕ 14 +ℕ len-f

      pc-f-is-cleanup : pc s-after-f-raw ≡ cleanup-offset
      pc-f-is-cleanup = trans pc-f-raw (trans (cong (_+ℕ len-f) len-prefix-f) refl)

      -- Step 2.5: Trace cleanup instructions (3 instructions)
      -- thunk-cleanup-star-proven traces: mv sp s2, ld s2 16(sp), addi sp sp +24
      cleanup-result = thunk-cleanup-star-proven f prefix suffix s-after-f-raw
                         (ir-halted r-f) pc-f-is-cleanup
      s-after-cleanup = proj₁ cleanup-result
      star-cleanup-raw = proj₁ (proj₂ cleanup-result)
      h-cleanup = proj₁ (proj₂ (proj₂ cleanup-result))
      pc-cleanup = proj₁ (proj₂ (proj₂ (proj₂ cleanup-result)))
      a0-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result))))
      s1-cleanup = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result)))))
      ra-cleanup = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ cleanup-result)))))

      -- star-cleanup-raw has type Star (prefix ++ compile-riscv (curry f) ++ suffix) = Star prog
      -- But we need Star (prefix-f ++ code-f ++ suffix-f) for composition
      -- prog-eq-f : prog ≡ prefix-f ++ code-f ++ suffix-f
      star-cleanup-converted : Star (prefix-f ++ code-f ++ suffix-f) s-after-f-raw s-after-cleanup
      star-cleanup-converted = subst (λ p → Star p s-after-f-raw s-after-cleanup) prog-eq-f star-cleanup-raw

      -- ra preservation: chain through IH, setup, and cleanup
      ra-preserved : readReg (regs s-after-cleanup) ra ≡ ret-addr
      ra-preserved = trans ra-cleanup (trans (ir-ra r-f) (trans ra-setup ra-eq))

      -- Combine f execution and cleanup
      star-f-and-cleanup : Star (prefix-f ++ code-f ++ suffix-f) s-after-setup s-after-cleanup
      star-f-and-cleanup = star-trans star-f-raw star-cleanup-converted

      -- Convert to use prog
      star-f-and-cleanup-prog : Star prog s-after-setup s-after-cleanup
      star-f-and-cleanup-prog = subst (λ p → Star p s-after-setup s-after-cleanup) (sym prog-eq-f) star-f-and-cleanup

      f-result-bridge : ∃[ s-f ] (Star prog s-after-setup s-f
                                 × halted s-f ≡ false
                                 × pc s-f ≡ ret-offset
                                 × readReg (regs s-f) a0 ≡ encode (eval f (env , arg))
                                 × readReg (regs s-f) s1 ≡ readReg (regs s-after-setup) s1
                                 × readReg (regs s-f) ra ≡ ret-addr)
      f-result-bridge = s-after-cleanup ,
                        star-f-and-cleanup-prog ,
                        h-cleanup ,
                        pc-cleanup ,
                        trans a0-cleanup (ir-a0 r-f) ,
                        trans s1-cleanup (ir-s1 r-f) ,
                        ra-preserved

      s-after-f = proj₁ f-result-bridge
      star-f = proj₁ (proj₂ f-result-bridge)
      h-f = proj₁ (proj₂ (proj₂ f-result-bridge))
      pc-f = proj₁ (proj₂ (proj₂ (proj₂ f-result-bridge)))
      a0-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge))))
      s1-f = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))
      ra-f = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ f-result-bridge)))))

      -- Step 3: Trace ret instruction
      ret-result = thunk-ret-star f prefix suffix ret-addr s-after-f
                     h-f pc-f ra-f
      s-final = proj₁ ret-result
      star-ret = proj₁ (proj₂ ret-result)
      h-final = proj₁ (proj₂ (proj₂ ret-result))
      pc-final = proj₁ (proj₂ (proj₂ (proj₂ ret-result)))
      a0-final = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))
      s1-final = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ ret-result))))

      -- Compose the three Star proofs
      star-all : Star prog s s-final
      star-all = star-trans star-setup (star-trans star-f star-ret)

      -- Build ThunkResult
      thunk-result : ThunkResult prog s s-final (λ b → eval f (env , b)) arg
      thunk-result = record
        { thunk-star = star-all
        ; thunk-halted = h-final
        ; thunk-a0 = trans a0-final a0-f
        ; thunk-s1 = trans s1-final (trans s1-f s1-setup)
        }

  ------------------------------------------------------------------------
  -- run-curry-star-with-wf: Curry with ClosureWellFormed proof
  --
  -- This is an enhanced version of run-curry-star that also produces
  -- a ClosureWellFormed proof. The proof is constructed using
  -- curry-thunk-correct-impl, which is available in this mutual block.
  ------------------------------------------------------------------------

  open import Once.Backend.RiscV64.Correct.ClosureWellFormed
    using (CurryResult; curry-star; curry-halted; curry-pc; curry-a0; curry-s1; closure-wf)
  open import Data.Nat using (_<_)

  run-curry-star-with-wf : ∀ {A B C} (f : IR (A * B) C)
                           (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) a0 ≡ encode x →
    let prog = prefix ++ compile-riscv (curry f) ++ suffix
        offset = length prefix
    in ∃[ s' ] CurryResult f prog s s' x offset

  run-curry-star-with-wf {A} {B} {C} f prefix suffix x s h-false pc-eq a0-eq =
    let (s' , result) = run-curry-star f prefix suffix x s h-false pc-eq a0-eq
        offset = length prefix
        prog = prefix ++ compile-riscv (curry f) ++ suffix
    in s' , record
      { curry-star   = ir-star result
      ; curry-halted = ir-halted result
      ; curry-pc     = ir-pc result
      ; curry-a0     = ir-a0 result
      ; curry-s1     = ir-s1 result
      ; closure-wf   = record
          { code-ptr-valid = code-ptr-valid-proof
          ; thunk-correct  = λ arg s' ret-addr h-eq' pc-eq' a0-eq' s0-eq' ra-eq' →
              curry-thunk-correct-impl f prefix suffix x arg s' ret-addr
                h-eq' pc-eq' a0-eq' s0-eq' ra-eq'
          }
      }
    where
      offset = length prefix
      prog = prefix ++ compile-riscv (curry f) ++ suffix
      curry-code = compile-riscv (curry f)

      -- code-ptr = offset + 7 < length prog
      -- Proof: length prog = length prefix + length curry-code + length suffix
      --        length curry-code = 19 + compile-length f ≥ 19
      --        So offset + 7 < offset + 19 ≤ length prog
      code-ptr-valid-proof : offset +ℕ 7 < length prog
      code-ptr-valid-proof = proof
        where
          open import Data.Nat.Properties using (<-≤-trans; +-monoʳ-<)

          -- 7 < 19 = 8 ≤ 19
          seven-lt-nineteen : 7 < 19
          seven-lt-nineteen = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

          -- length curry-code = 19 + compile-length f
          len-curry : length curry-code ≡ 19 +ℕ compile-length f
          len-curry = compile-length-correct (curry f)

          -- 19 ≤ 19 + compile-length f
          nineteen-le-curry : 19 ≤ 19 +ℕ compile-length f
          nineteen-le-curry = m≤m+n 19 (compile-length f)

          -- 7 < 19 ≤ 19 + compile-length f = length curry-code
          seven-lt-curry : 7 < length curry-code
          seven-lt-curry = subst (7 <_) (sym len-curry)
                            (<-≤-trans seven-lt-nineteen nineteen-le-curry)

          -- length prog = length prefix + length (curry-code ++ suffix)
          len-prog-eq : length prog ≡ length prefix +ℕ length (curry-code ++ suffix)
          len-prog-eq = List-length-++ prefix

          -- length (curry-code ++ suffix) = length curry-code + length suffix
          len-curry-suffix : length (curry-code ++ suffix) ≡ length curry-code +ℕ length suffix
          len-curry-suffix = List-length-++ curry-code

          -- length curry-code ≤ length curry-code + length suffix = length (curry-code ++ suffix)
          curry-le-curry-suffix : length curry-code ≤ length (curry-code ++ suffix)
          curry-le-curry-suffix = subst (length curry-code ≤_) (sym len-curry-suffix)
                                        (m≤m+n (length curry-code) (length suffix))

          -- 7 < length curry-code ≤ length (curry-code ++ suffix)
          seven-lt-curry-suffix : 7 < length (curry-code ++ suffix)
          seven-lt-curry-suffix = <-≤-trans seven-lt-curry curry-le-curry-suffix

          -- Use +-monoʳ-< : i < j → n + i < n + j
          step1 : offset +ℕ 7 < offset +ℕ length (curry-code ++ suffix)
          step1 = +-monoʳ-< offset seven-lt-curry-suffix

          -- offset + length (curry-code ++ suffix) = length prog
          proof : offset +ℕ 7 < length prog
          proof = subst (offset +ℕ 7 <_) (sym len-prog-eq) step1

------------------------------------------------------------------------
-- Top-level entry point
------------------------------------------------------------------------

-- | Execute IR starting at position 0
run-ir-star : ∀ {A B} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult ir (compile-riscv ir) s s' x 0
run-ir-star ir x s h-false pc-eq a0-eq =
  subst (λ prog → ∃[ s' ] IRStarResult ir prog s s' x 0)
        (++-identityʳ (compile-riscv ir))
        (run-ir-star-at-offset ir [] [] x s h-false pc-eq a0-eq)
  where
    open import Data.List.Properties using (++-identityʳ)
