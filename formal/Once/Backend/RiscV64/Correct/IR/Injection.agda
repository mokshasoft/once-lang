------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.IR.Injection
--
-- Star-based proofs for injection generators (inl, inr).
--
-- Extracted from MutualIR.agda to reduce module size.
--
-- inl: addi sp sp -16; sd zero 0(sp); sd a0 8(sp); mv a0 sp
-- inr: addi sp sp -16; li t0 1; sd t0 0(sp); sd a0 8(sp); mv a0 sp
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.IR.Injection where

open import Size

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Postulates
  using (encode; encode-inl-tag; encode-inl-val;
         encode-inr-tag; encode-inr-val;
         encode-inl-construct; encode-inr-construct)

open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.Star
  using (Star; star-step4; star-step5)
open import Once.Backend.RiscV64.Correct.StarBase
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-a0; ir-s1; ir-s2; ir-ra;
         ir-sp-delta; ir-sp-delta-leq; ir-sp; ir-mem-preserved; ir-output-wf)
open import Once.Backend.RiscV64.Correct.ClosureWellFormed
  using (ClosuresWF; trivialWF)

open import Once.Backend.Common.Memory
  using (readMem-writeMem-same; readMem-writeMem-diff; n≢n+suc)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; s≤s; z≤n; s<s; z<s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; m∸n+n≡m; ≤-trans; ≤-refl)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc) renaming (length-++ to List-length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

-- | Star-based inl execution
run-inl-star : ∀ {i A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  16 ≤ readReg (regs s) sp →  -- StackDepth inl = 16
  let prog = prefix ++ compile-riscv (inl {i} {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (inl {i} {A} {B}) prog s s' x (length prefix)
run-inl-star {i} {A} {B} prefix suffix x s h-false pc-eq a0-eq sp-bound =
  st4 , record
    { ir-star = star-proof
    ; ir-halted = h4
    ; ir-pc = pc4
    ; ir-a0 = a0-final
    ; ir-s1 = s1-reg-final
    ; ir-s2 = s2-reg-final
    ; ir-ra = ra-final
    ; ir-sp-delta = 16
    ; ir-sp-delta-leq = ≤-refl
    ; ir-sp = sp-final
    ; ir-mem-preserved = mem-preserved-final
    ; ir-output-wf = trivialWF (A + B) prog
    }
  where
    prog : Program
    prog = prefix ++ compile-riscv (inl {i} {A} {B}) ++ suffix

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

    s2-reg-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-reg-st1 = readReg-writeReg-sp-s2 (regs s) new-sp

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

    s2-reg-final : readReg (regs st4) s2 ≡ readReg (regs s) s2
    s2-reg-final = trans (readReg-writeReg-a0-s2 (regs st3) (readReg (regs st3) sp)) s2-reg-st1

    ra-final : readReg (regs st4) ra ≡ readReg (regs s) ra
    ra-final = trans (readReg-writeReg-a0-ra (regs st3) (readReg (regs st3) sp)) ra-st1

    -- SP tracking: inl allocates 16 bytes on stack (sp -= 16)
    -- With ir-sp-delta = 16, we need: new-sp + 16 ≡ orig-sp
    -- This is (orig-sp ∸ 16) + 16 ≡ orig-sp, which holds when 16 ≤ orig-sp

    -- Stack space: directly from sp-bound (16 ≤ orig-sp)
    stack-space : 16 ≤ orig-sp
    stack-space = sp-bound

    sp-final : readReg (regs st4) sp +ℕ 16 ≡ readReg (regs s) sp
    sp-final = trans (cong (_+ℕ 16) sp-st3) (m∸n+n≡m stack-space)

    -- Memory preservation: inl writes at new-sp and new-sp + 8 (16 and 8 bytes BELOW orig-sp).
    -- Memory at orig-sp and above is preserved because write addresses are disjoint.
    --
    -- Address disjointness: new-sp = orig-sp ∸ 16, so for orig-sp ≥ 16:
    --   new-sp ≢ orig-sp (since 16 ≢ 0)
    --   new-sp + 8 ≢ orig-sp (since 8 ≢ 0)
    --   new-sp ≢ orig-sp + 8, + 16, + 24 (always true when orig-sp ≥ 16)
    --   new-sp + 8 ≢ orig-sp + 8, + 16, + 24 (always true when orig-sp ≥ 16)
    --
    -- All 8 disjointness lemmas proven using monus-plus-neq-plus with n=16

    -- Helper: 0 < 16 and 8 < 16 for the monus lemmas
    0<16 : 0 < 16
    0<16 = z<s

    -- 8 < 16 = suc 8 ≤ 16 = 9 ≤ 16
    -- Need 8 applications of s<s then z<s
    8<16 : 8 < 16
    8<16 = s<s (s<s (s<s (s<s (s<s (s<s (s<s (s<s z<s)))))))

    -- Universal disjointness lemmas (replace 8 specific lemmas with 2 universal ones)
    -- new-sp = orig-sp - 16 < orig-sp ≤ orig-sp + n for all n
    new-sp≢orig-sp+n : ∀ n → new-sp ≢ (orig-sp +ℕ n)
    new-sp≢orig-sp+n 0 = λ eq → monus-neq-self 16 orig-sp stack-space 0<16
                                  (trans eq (+-identityʳ orig-sp))
    new-sp≢orig-sp+n (suc n) = monus-neq-plus 16 orig-sp (suc n) stack-space 0<16

    -- new-sp + 8 = orig-sp - 8 < orig-sp ≤ orig-sp + n for all n
    new-sp+8≢orig-sp+n : ∀ n → (new-sp +ℕ 8) ≢ (orig-sp +ℕ n)
    new-sp+8≢orig-sp+n n = monus-plus-neq-plus 16 orig-sp 8 n stack-space 8<16

    -- Actual write addresses (as used in state definitions)
    write-addr-st2 : ℕ
    write-addr-st2 = readReg (regs st1) sp +ℕ 0  -- = new-sp + 0

    write-addr-st3 : ℕ
    write-addr-st3 = readReg (regs st2) sp +ℕ 8  -- = new-sp + 8

    -- Prove write addresses equal new-sp and new-sp+8
    write-addr-st2-eq : write-addr-st2 ≡ new-sp
    write-addr-st2-eq = trans (cong (_+ℕ 0) sp-st1) (+-identityʳ new-sp)

    write-addr-st3-eq : write-addr-st3 ≡ new-sp +ℕ 8
    write-addr-st3-eq = cong (_+ℕ 8) sp-st2

    -- Universal memory preservation at orig-sp + n for all n
    -- st1 doesn't write memory, st2 writes at new-sp, st3 writes at new-sp+8, st4 doesn't write
    -- Both write addresses are below orig-sp, so memory at orig-sp + n is preserved
    mem-preserved-final : ∀ n → readMem (memory st4) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
    mem-preserved-final n =
      let mem-st1 : readMem (memory st1) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          mem-st1 = refl  -- st1 only changes regs
          mem-st2 : readMem (memory st2) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          mem-st2 = trans (readMem-writeMem-diff (memory st1) write-addr-st2 (orig-sp +ℕ n)
                            (readReg (regs st1) zero)
                            (λ eq → new-sp≢orig-sp+n n (trans (sym write-addr-st2-eq) eq)))
                          mem-st1
          mem-st3 : readMem (memory st3) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          mem-st3 = trans (readMem-writeMem-diff (memory st2) write-addr-st3 (orig-sp +ℕ n)
                            (readReg (regs st2) a0)
                            (λ eq → new-sp+8≢orig-sp+n n (trans (sym write-addr-st3-eq) eq)))
                          mem-st2
      in mem-st3  -- st4 only changes regs

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
run-inr-star : ∀ {i A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  16 ≤ readReg (regs s) sp →  -- StackDepth inr = 16
  let prog = prefix ++ compile-riscv (inr {i} {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResult (inr {i} {A} {B}) prog s s' x (length prefix)
run-inr-star {i} {A} {B} prefix suffix x s h-false pc-eq a0-eq sp-bound =
  st5 , record
    { ir-star = star-proof
    ; ir-halted = h5
    ; ir-pc = pc5
    ; ir-a0 = a0-final
    ; ir-s1 = s1-reg-final
    ; ir-s2 = s2-reg-final
    ; ir-ra = ra-final
    ; ir-sp-delta = 16
    ; ir-sp-delta-leq = ≤-refl
    ; ir-sp = sp-final
    ; ir-mem-preserved = mem-preserved-final
    ; ir-output-wf = trivialWF (A + B) prog
    }
  where
    prog : Program
    prog = prefix ++ compile-riscv (inr {i} {A} {B}) ++ suffix

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

    s2-reg-st1 : readReg (regs st1) s2 ≡ readReg (regs s) s2
    s2-reg-st1 = readReg-writeReg-sp-s2 (regs s) new-sp

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

    s2-reg-st2 : readReg (regs st2) s2 ≡ readReg (regs s) s2
    s2-reg-st2 = trans (readReg-writeReg-t0-s2 (regs st1) 1) s2-reg-st1

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

    s2-reg-final : readReg (regs st5) s2 ≡ readReg (regs s) s2
    s2-reg-final = trans (readReg-writeReg-a0-s2 (regs st4) (readReg (regs st4) sp)) s2-reg-st2

    ra-final : readReg (regs st5) ra ≡ readReg (regs s) ra
    ra-final = trans (readReg-writeReg-a0-ra (regs st4) (readReg (regs st4) sp)) ra-st2

    -- SP tracking: inr allocates 16 bytes on stack (sp -= 16)
    -- With ir-sp-delta = 16, we need: new-sp + 16 ≡ orig-sp
    -- This is (orig-sp ∸ 16) + 16 ≡ orig-sp, which holds when 16 ≤ orig-sp

    -- Stack space: directly from sp-bound (16 ≤ orig-sp)
    stack-space : 16 ≤ orig-sp
    stack-space = sp-bound

    sp-final : readReg (regs st5) sp +ℕ 16 ≡ readReg (regs s) sp
    sp-final = trans (cong (_+ℕ 16) sp-st4) (m∸n+n≡m stack-space)

    -- Memory preservation: inr writes at new-sp and new-sp + 8 (16 and 8 bytes BELOW orig-sp).
    -- Memory at orig-sp and above is preserved because write addresses are disjoint.
    --
    -- Address disjointness using monus lemmas from Foundation

    0<16 : 0 < 16
    0<16 = z<s

    8<16 : 8 < 16
    8<16 = s<s (s<s (s<s (s<s (s<s (s<s (s<s (s<s z<s)))))))

    -- Universal disjointness lemmas
    new-sp≢orig-sp+n : ∀ n → new-sp ≢ (orig-sp +ℕ n)
    new-sp≢orig-sp+n 0 = λ eq → monus-neq-self 16 orig-sp stack-space 0<16
                                  (trans eq (+-identityʳ orig-sp))
    new-sp≢orig-sp+n (suc n) = monus-neq-plus 16 orig-sp (suc n) stack-space 0<16

    new-sp+8≢orig-sp+n : ∀ n → (new-sp +ℕ 8) ≢ (orig-sp +ℕ n)
    new-sp+8≢orig-sp+n n = monus-plus-neq-plus 16 orig-sp 8 n stack-space 8<16

    -- Actual write addresses (as used in state definitions)
    -- st3: sd t0 0(sp) writes tag at sp + 0
    write-addr-st3 : ℕ
    write-addr-st3 = readReg (regs st2) sp +ℕ 0  -- = new-sp + 0

    -- st4: sd a0 8(sp) writes value at sp + 8
    write-addr-st4 : ℕ
    write-addr-st4 = readReg (regs st3) sp +ℕ 8  -- = new-sp + 8

    -- Prove write addresses equal new-sp and new-sp+8
    write-addr-st3-eq : write-addr-st3 ≡ new-sp
    write-addr-st3-eq = trans (cong (_+ℕ 0) sp-st2) (+-identityʳ new-sp)

    write-addr-st4-eq : write-addr-st4 ≡ new-sp +ℕ 8
    write-addr-st4-eq = cong (_+ℕ 8) sp-st3

    -- Universal memory preservation at orig-sp + n for all n
    -- st1, st2 don't write memory, st3 writes at new-sp, st4 writes at new-sp+8, st5 doesn't write
    mem-preserved-final : ∀ n → readMem (memory st5) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
    mem-preserved-final n =
      let mem-st1 : readMem (memory st1) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          mem-st1 = refl  -- st1 only changes regs (addi)
          mem-st2 : readMem (memory st2) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          mem-st2 = refl  -- st2 only changes regs (li)
          mem-st3 : readMem (memory st3) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          mem-st3 = trans (readMem-writeMem-diff (memory st2) write-addr-st3 (orig-sp +ℕ n)
                            (readReg (regs st2) t0)
                            (λ eq → new-sp≢orig-sp+n n (trans (sym write-addr-st3-eq) eq)))
                          mem-st2
          mem-st4 : readMem (memory st4) (orig-sp +ℕ n) ≡ readMem (memory s) (orig-sp +ℕ n)
          mem-st4 = trans (readMem-writeMem-diff (memory st3) write-addr-st4 (orig-sp +ℕ n)
                            (readReg (regs st3) a0)
                            (λ eq → new-sp+8≢orig-sp+n n (trans (sym write-addr-st4-eq) eq)))
                          mem-st3
      in mem-st4  -- st5 only changes regs (mv)

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
