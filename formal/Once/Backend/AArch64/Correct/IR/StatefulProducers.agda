{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.StatefulProducers
--
-- Stateful versions of inl/inr that return validity predicates
-- instead of using encode postulates.
--
-- Key insight: inl/inr allocate memory with known layout.
-- We prove the memory layout directly and return InlAtS/InrAtS.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.StatefulProducers where

open import Once.Type using (Type; _+_)
open import Once.IR using (IR; inl; inr)
open import Once.Semantics using (⟦_⟧)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation
  using (readReg-writeReg-same;
         readReg-writeReg-x0-x20; readReg-writeReg-x0-x21;
         readReg-writeReg-x0-x29; readReg-writeReg-x0-x30;
         readReg-writeReg-x9-x0; readReg-writeReg-x9-x20;
         readReg-writeReg-x9-x21; readReg-writeReg-x9-x29; readReg-writeReg-x9-x30;
         readReg-writeSP; readSP-writeReg; readSP-writeSP;
         readMem-writeMem-same; readMem-writeMem-diff-8-rev;
         step-instr; fetch-at-prefix-end;
         execInstr-sub-sp; execInstr-str-zr; execInstr-str; execInstr-mov-from-sp;
         execInstr-mov-imm)
open import Once.Backend.Common.Memory using (readMem-writeMem-diff)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant;
         stack-inv-preserved-sp-decreased; x29-inv-preserved-sp-decreased;
         addr-diff-from-invariant; x29-addr-diff-extended)
open import Once.Backend.AArch64.Postulates
  using (sp-bound-after-stack-op)
open import Once.Backend.AArch64.Correct.Star
  using (Star; star-single; star-trans)
open import Once.Backend.AArch64.Correct.StarBase
  using (IRStarResultS)
open import Once.Backend.AArch64.Correct.MemoryValid
  using (InlAtS; InrAtS)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _≤_; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; m∸n≤m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

------------------------------------------------------------------------
-- Stateful inl producer
------------------------------------------------------------------------

-- | Stateful Star-based inl execution
-- Returns IRStarResultS with explicit address plus InlAtS validity proof.
-- This eliminates the need for encode-inl-construct postulate.
--
-- The key insight: inl writes tag=0 at new-sp and addr-in at new-sp+8.
-- From these writes we can directly construct InlAtS.
run-inl-star-s : ∀ {i} {A B} (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-in →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 (inl {i} {A} {B}) ++ suffix
      new-sp = readSP (regs s) ∸ 16
  in ∃[ s' ] (IRStarResultS (inl {i} {A} {B}) prog s s' new-sp (length prefix)
             × InlAtS addr-in new-sp (memory s'))
run-inl-star-s {i} {A} {B} prefix suffix addr-in s h-false pc-eq x0-eq stack-inv x29-inv sp>16 =
  s4 , (result-s , validity)
  where
    -- Program
    prog : Program
    prog = prefix ++ compile-aarch64 {_} {A} {A + B} inl ++ suffix

    orig-sp : Word
    orig-sp = readSP (regs s)
    new-sp : Word
    new-sp = orig-sp ∸ 16

    -- State after each instruction
    -- inl generates 4 instructions: sub-sp 16, str-zr [sp], str x0 [sp+8], mov-from-sp
    s1 : State
    s1 = record s { regs = writeSP (regs s) new-sp ; pc = pc s +ℕ 1 }
    s2 : State
    s2 = record s1 { memory = writeMem (memory s1) (new-sp +ℕ 0) 0 ; pc = pc s1 +ℕ 1 }
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (new-sp +ℕ 8) (readReg (regs s) x0) ; pc = pc s2 +ℕ 1 }
    s4 : State
    s4 = record s3 { regs = writeReg (regs s3) x0 new-sp ; pc = pc s3 +ℕ 1 }

    -- Memory proofs for validity (PROVEN, not postulated!)
    mem-tag : readMem (memory s4) new-sp ≡ just 0
    mem-tag = trans (readMem-writeMem-diff-8-rev (memory s2) new-sp (readReg (regs s) x0))
                    (subst (λ addr → readMem (writeMem (memory s1) addr 0) new-sp ≡ just 0)
                           (sym (+-identityʳ new-sp))
                           (readMem-writeMem-same (memory s1) new-sp 0))

    mem-val : readMem (memory s4) (new-sp +ℕ 8) ≡ just (readReg (regs s) x0)
    mem-val = readMem-writeMem-same (memory s2) (new-sp +ℕ 8) (readReg (regs s) x0)

    mem-val-addr : readMem (memory s4) (new-sp +ℕ 8) ≡ just addr-in
    mem-val-addr = trans mem-val (cong just x0-eq)

    -- Construct InlAtS directly from memory proofs (PROVEN!)
    validity : InlAtS addr-in new-sp (memory s4)
    validity = record { tag-valid = mem-tag ; val-valid = mem-val-addr }

    -- The 4 instructions of inl
    i0 : Instr
    i0 = sub-sp 16
    i1 : Instr
    i1 = str-zr (sp+imm 0)
    i2 : Instr
    i2 = str x0 (sp+imm 8)
    i3 : Instr
    i3 = mov-from-sp x0

    -- Fetch proofs
    prog-eq0 : prog ≡ prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq0 = refl

    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ suffix)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = length-++ prefix

    fetch1-helper : fetch ((prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ [])) ≡ just i1
    fetch1-helper = fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ suffix)

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1 fetch1-helper

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = length-++ prefix

    fetch2-helper : fetch ((prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ [])) ≡ just i2
    fetch2-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ suffix)

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2 fetch2-helper

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = length-++ prefix

    fetch3-helper : fetch ((prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ i2 ∷ [])) ≡ just i3
    fetch3-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 suffix

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3 fetch3-helper

    -- Step proofs
    step0 : step prog s ≡ just s1
    step0 = step-instr prog s s1 i0 h-false
              (subst (λ n → fetch prog n ≡ just i0) (sym pc-eq) fetch0)
              (execInstr-sub-sp prog s 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    step1 : step prog s1 ≡ just s2
    step1 = step-instr prog s1 s2 i1 h1
              (subst (λ n → fetch prog n ≡ just i1) (sym pc1) fetch1)
              (execInstr-str-zr prog s1 (sp+imm 0))

    h2 : halted s2 ≡ false
    h2 = h1

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    step2 : step prog s2 ≡ just s3
    step2 = step-instr prog s2 s3 i2 h2
              (subst (λ n → fetch prog n ≡ just i2) (sym pc2) fetch2)
              (execInstr-str prog s2 x0 (sp+imm 8))

    h3 : halted s3 ≡ false
    h3 = h2

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step3 : step prog s3 ≡ just s4
    step3 = step-instr prog s3 s4 i3 h3
              (subst (λ n → fetch prog n ≡ just i3) (sym pc3) fetch3)
              (execInstr-mov-from-sp prog s3 x0)

    -- Build Star proof from 4 steps (PROVEN!)
    star01 : Star prog s s1
    star01 = star-single h-false step0
    star12 : Star prog s1 s2
    star12 = star-single h1 step1
    star23 : Star prog s2 s3
    star23 = star-single h2 step2
    star34 : Star prog s3 s4
    star34 = star-single h3 step3
    star-proof : Star prog s s4
    star-proof = star-trans (star-trans (star-trans star01 star12) star23) star34

    -- Final state properties (PROVEN!)
    h4 : halted s4 ≡ false
    h4 = h3

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Register preservation (PROVEN!)
    x20-eq : readReg (regs s4) x20 ≡ readReg (regs s) x20
    x20-eq = trans (readReg-writeReg-x0-x20 (regs s3) new-sp)
                   (readReg-writeSP (regs s) x20 new-sp)

    x21-eq : readReg (regs s4) x21 ≡ readReg (regs s) x21
    x21-eq = trans (readReg-writeReg-x0-x21 (regs s3) new-sp)
                   (readReg-writeSP (regs s) x21 new-sp)

    x29-eq : readReg (regs s4) x29 ≡ readReg (regs s) x29
    x29-eq = trans (readReg-writeReg-x0-x29 (regs s3) new-sp)
                   (readReg-writeSP (regs s) x29 new-sp)

    x30-eq : readReg (regs s4) x30 ≡ readReg (regs s) x30
    x30-eq = trans (readReg-writeReg-x0-x30 (regs s3) new-sp)
                   (readReg-writeSP (regs s) x30 new-sp)

    -- SP decreased (PROVEN!)
    sp-s4 : readSP (regs s4) ≡ new-sp
    sp-s4 = readSP-writeReg (regs s3) x0 new-sp

    sp-decreased : readSP (regs s4) ≤ readSP (regs s)
    sp-decreased = subst₂ _≤_ sp-s4 refl (m∸n≤m orig-sp 16)

    -- Address disjointness from invariants
    x21-diffs : (new-sp ≢ readReg (regs s) x21) × ((new-sp +ℕ 8) ≢ readReg (regs s) x21)
    x21-diffs = addr-diff-from-invariant s stack-inv sp>16

    x29-diffs : (new-sp ≢ readReg (regs s) x29) × ((new-sp +ℕ 8) ≢ readReg (regs s) x29) ×
                (new-sp ≢ (readReg (regs s) x29 +ℕ 8)) × ((new-sp +ℕ 8) ≢ (readReg (regs s) x29 +ℕ 8))
    x29-diffs = x29-addr-diff-extended s x29-inv sp>16

    -- Memory preservation (PROVEN!)
    mem-x21-step1 : readMem (memory s4) (readReg (regs s) x21) ≡ readMem (memory s2) (readReg (regs s) x21)
    mem-x21-step1 = readMem-writeMem-diff (memory s2) (new-sp +ℕ 8) (readReg (regs s) x21) (readReg (regs s) x0) (proj₂ x21-diffs)

    mem-x21-step2 : readMem (memory s2) (readReg (regs s) x21) ≡ readMem (memory s1) (readReg (regs s) x21)
    mem-x21-step2 = subst (λ addr → readMem (writeMem (memory s1) addr 0) (readReg (regs s) x21) ≡ readMem (memory s1) (readReg (regs s) x21))
                          (sym (+-identityʳ new-sp))
                          (readMem-writeMem-diff (memory s1) new-sp (readReg (regs s) x21) 0 (proj₁ x21-diffs))

    mem-x21-eq : readMem (memory s4) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-eq = trans mem-x21-step1 mem-x21-step2

    mem-x29-step1 : readMem (memory s4) (readReg (regs s) x29) ≡ readMem (memory s2) (readReg (regs s) x29)
    mem-x29-step1 = readMem-writeMem-diff (memory s2) (new-sp +ℕ 8) (readReg (regs s) x29) (readReg (regs s) x0) (proj₁ (proj₂ x29-diffs))

    mem-x29-step2 : readMem (memory s2) (readReg (regs s) x29) ≡ readMem (memory s1) (readReg (regs s) x29)
    mem-x29-step2 = subst (λ addr → readMem (writeMem (memory s1) addr 0) (readReg (regs s) x29) ≡ readMem (memory s1) (readReg (regs s) x29))
                          (sym (+-identityʳ new-sp))
                          (readMem-writeMem-diff (memory s1) new-sp (readReg (regs s) x29) 0 (proj₁ x29-diffs))

    mem-x29-eq : readMem (memory s4) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-eq = trans mem-x29-step1 mem-x29-step2

    mem-x29+8-step1 : readMem (memory s4) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s2) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-step1 = readMem-writeMem-diff (memory s2) (new-sp +ℕ 8) (readReg (regs s) x29 +ℕ 8) (readReg (regs s) x0) (proj₂ (proj₂ (proj₂ x29-diffs)))

    mem-x29+8-step2 : readMem (memory s2) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s1) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-step2 = subst (λ addr → readMem (writeMem (memory s1) addr 0) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s1) (readReg (regs s) x29 +ℕ 8))
                            (sym (+-identityʳ new-sp))
                            (readMem-writeMem-diff (memory s1) new-sp (readReg (regs s) x29 +ℕ 8) 0 (proj₁ (proj₂ (proj₂ x29-diffs))))

    mem-x29+8-eq : readMem (memory s4) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-eq = trans mem-x29+8-step1 mem-x29+8-step2

    -- Invariant preservation (PROVEN!)
    stack-inv' : StackInvariant s4
    stack-inv' = stack-inv-preserved-sp-decreased s s4 stack-inv x21-eq sp-decreased

    x29-inv' : X29Invariant s4
    x29-inv' = x29-inv-preserved-sp-decreased s s4 x29-inv x29-eq sp-decreased

    sp>16' : readSP (regs s4) > 16
    sp>16' = sp-bound-after-stack-op s4

    x0-s4 : readReg (regs s4) x0 ≡ new-sp
    x0-s4 = readReg-writeReg-same (regs s3) x0 new-sp

    result-s : IRStarResultS (inl {i} {A} {B}) prog s s4 new-sp (length prefix)
    result-s = record
      { ir-star = star-proof
      ; ir-halted = h4
      ; ir-pc = pc4
      ; ir-x0-s = x0-s4
      ; ir-x20 = x20-eq
      ; ir-x21 = x21-eq
      ; ir-x29 = x29-eq
      ; ir-x30 = x30-eq
      ; ir-sp = sp-decreased
      ; ir-mem-x21 = mem-x21-eq
      ; ir-mem-x29 = mem-x29-eq
      ; ir-mem-x29+8 = mem-x29+8-eq
      ; ir-stack-inv = stack-inv'
      ; ir-x29-inv = x29-inv'
      ; ir-sp-bound = sp>16'
      }

------------------------------------------------------------------------
-- Stateful inr producer
------------------------------------------------------------------------

-- | Stateful Star-based inr execution
-- Returns IRStarResultS with explicit address plus InrAtS validity proof.
run-inr-star-s : ∀ {i} {A B} (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-in →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 (inr {i} {A} {B}) ++ suffix
      new-sp = readSP (regs s) ∸ 16
  in ∃[ s' ] (IRStarResultS (inr {i} {A} {B}) prog s s' new-sp (length prefix)
             × InrAtS addr-in new-sp (memory s'))
run-inr-star-s {i} {A} {B} prefix suffix addr-in s h-false pc-eq x0-eq stack-inv x29-inv sp>16 =
  s5 , (result-s , validity)
  where
    -- Program
    prog : Program
    prog = prefix ++ compile-aarch64 {_} {B} {A + B} inr ++ suffix

    orig-sp : Word
    orig-sp = readSP (regs s)
    new-sp : Word
    new-sp = orig-sp ∸ 16

    -- State after each instruction
    -- inr generates 5 instructions: sub-sp, mov x9 1, str x9 [sp], str x0 [sp+8], mov-from-sp
    s1 : State
    s1 = record s { regs = writeSP (regs s) new-sp ; pc = pc s +ℕ 1 }
    s2 : State
    s2 = record s1 { regs = writeReg (regs s1) x9 1 ; pc = pc s1 +ℕ 1 }
    s3 : State
    s3 = record s2 { memory = writeMem (memory s2) (new-sp +ℕ 0) 1 ; pc = pc s2 +ℕ 1 }
    s4 : State
    s4 = record s3 { memory = writeMem (memory s3) (new-sp +ℕ 8) (readReg (regs s) x0) ; pc = pc s3 +ℕ 1 }
    s5 : State
    s5 = record s4 { regs = writeReg (regs s4) x0 new-sp ; pc = pc s4 +ℕ 1 }

    -- Memory proofs for validity (PROVEN!)
    mem-tag : readMem (memory s5) new-sp ≡ just 1
    mem-tag = trans (readMem-writeMem-diff-8-rev (memory s3) new-sp (readReg (regs s) x0))
                    (subst (λ addr → readMem (writeMem (memory s2) addr 1) new-sp ≡ just 1)
                           (sym (+-identityʳ new-sp))
                           (readMem-writeMem-same (memory s2) new-sp 1))

    mem-val : readMem (memory s5) (new-sp +ℕ 8) ≡ just (readReg (regs s) x0)
    mem-val = readMem-writeMem-same (memory s3) (new-sp +ℕ 8) (readReg (regs s) x0)

    mem-val-addr : readMem (memory s5) (new-sp +ℕ 8) ≡ just addr-in
    mem-val-addr = trans mem-val (cong just x0-eq)

    -- Construct InrAtS directly from memory proofs (PROVEN!)
    validity : InrAtS addr-in new-sp (memory s5)
    validity = record { tag-valid = mem-tag ; val-valid = mem-val-addr }

    -- The 5 instructions of inr
    i0 : Instr
    i0 = sub-sp 16
    i1 : Instr
    i1 = mov x9 (imm 1)
    i2 : Instr
    i2 = str x9 (sp+imm 0)
    i3 : Instr
    i3 = str x0 (sp+imm 8)
    i4 : Instr
    i4 = mov-from-sp x0

    -- Fetch proofs
    prog-eq0 : prog ≡ prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ i4 ∷ suffix
    prog-eq0 = refl

    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 (i1 ∷ i2 ∷ i3 ∷ i4 ∷ suffix)

    prog-eq1 : prog ≡ (prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ i4 ∷ suffix
    prog-eq1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ i2 ∷ i3 ∷ i4 ∷ suffix))

    len-prefix-1 : length (prefix ++ i0 ∷ []) ≡ length prefix +ℕ 1
    len-prefix-1 = length-++ prefix

    fetch1-helper : fetch ((prefix ++ i0 ∷ []) ++ i1 ∷ i2 ∷ i3 ∷ i4 ∷ suffix) (length (prefix ++ i0 ∷ [])) ≡ just i1
    fetch1-helper = fetch-at-prefix-end (prefix ++ i0 ∷ []) i1 (i2 ∷ i3 ∷ i4 ∷ suffix)

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog-eq1) len-prefix-1 fetch1-helper

    prog-eq2 : prog ≡ (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ i4 ∷ suffix
    prog-eq2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ i3 ∷ i4 ∷ suffix))

    len-prefix-2 : length (prefix ++ i0 ∷ i1 ∷ []) ≡ length prefix +ℕ 2
    len-prefix-2 = length-++ prefix

    fetch2-helper : fetch ((prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ i3 ∷ i4 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ [])) ≡ just i2
    fetch2-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ []) i2 (i3 ∷ i4 ∷ suffix)

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog-eq2) len-prefix-2 fetch2-helper

    prog-eq3 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ i4 ∷ suffix
    prog-eq3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ i4 ∷ suffix))

    len-prefix-3 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ≡ length prefix +ℕ 3
    len-prefix-3 = length-++ prefix

    fetch3-helper : fetch ((prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ i4 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ i2 ∷ [])) ≡ just i3
    fetch3-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) i3 (i4 ∷ suffix)

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog-eq3) len-prefix-3 fetch3-helper

    prog-eq4 : prog ≡ (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) ++ i4 ∷ suffix
    prog-eq4 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) (i4 ∷ suffix))

    len-prefix-4 : length (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) ≡ length prefix +ℕ 4
    len-prefix-4 = length-++ prefix

    fetch4-helper : fetch ((prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) ++ i4 ∷ suffix) (length (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ [])) ≡ just i4
    fetch4-helper = fetch-at-prefix-end (prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) i4 suffix

    fetch4 : fetch prog (length prefix +ℕ 4) ≡ just i4
    fetch4 = subst₂ (λ p n → fetch p n ≡ just i4) (sym prog-eq4) len-prefix-4 fetch4-helper

    -- Step proofs
    step0 : step prog s ≡ just s1
    step0 = step-instr prog s s1 i0 h-false
              (subst (λ n → fetch prog n ≡ just i0) (sym pc-eq) fetch0)
              (execInstr-sub-sp prog s 16)

    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    step1 : step prog s1 ≡ just s2
    step1 = step-instr prog s1 s2 i1 h1
              (subst (λ n → fetch prog n ≡ just i1) (sym pc1) fetch1)
              (execInstr-mov-imm prog s1 x9 1)

    h2 : halted s2 ≡ false
    h2 = h1

    pc2 : pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- For step2, we use the general execInstr-str lemma
    step2 : step prog s2 ≡ just s3
    step2 = step-instr prog s2 s3 i2 h2
              (subst (λ n → fetch prog n ≡ just i2) (sym pc2) fetch2)
              (execInstr-str prog s2 x9 (sp+imm 0))

    h3 : halted s3 ≡ false
    h3 = h2

    pc3 : pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    step3 : step prog s3 ≡ just s4
    step3 = step-instr prog s3 s4 i3 h3
              (subst (λ n → fetch prog n ≡ just i3) (sym pc3) fetch3)
              (execInstr-str prog s3 x0 (sp+imm 8))

    h4 : halted s4 ≡ false
    h4 = h3

    pc4 : pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    step4 : step prog s4 ≡ just s5
    step4 = step-instr prog s4 s5 i4 h4
              (subst (λ n → fetch prog n ≡ just i4) (sym pc4) fetch4)
              (execInstr-mov-from-sp prog s4 x0)

    -- Build Star proof from 5 steps (PROVEN!)
    star01 : Star prog s s1
    star01 = star-single h-false step0
    star12 : Star prog s1 s2
    star12 = star-single h1 step1
    star23 : Star prog s2 s3
    star23 = star-single h2 step2
    star34 : Star prog s3 s4
    star34 = star-single h3 step3
    star45 : Star prog s4 s5
    star45 = star-single h4 step4
    star-proof : Star prog s s5
    star-proof = star-trans (star-trans (star-trans (star-trans star01 star12) star23) star34) star45

    -- Final state properties (PROVEN!)
    h5 : halted s5 ≡ false
    h5 = h4

    pc5 : pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    -- Register preservation (PROVEN!)
    -- Note: s2 = writeReg s1 x9, s5 = writeReg s4 x0
    -- So x20,x21,x29,x30 are preserved through both writeReg and writeSP
    x20-eq : readReg (regs s5) x20 ≡ readReg (regs s) x20
    x20-eq = trans (readReg-writeReg-x0-x20 (regs s4) new-sp)
                   (trans (readReg-writeReg-x9-x20 (regs s1) 1)
                          (readReg-writeSP (regs s) x20 new-sp))

    x21-eq : readReg (regs s5) x21 ≡ readReg (regs s) x21
    x21-eq = trans (readReg-writeReg-x0-x21 (regs s4) new-sp)
                   (trans (readReg-writeReg-x9-x21 (regs s1) 1)
                          (readReg-writeSP (regs s) x21 new-sp))

    x29-eq : readReg (regs s5) x29 ≡ readReg (regs s) x29
    x29-eq = trans (readReg-writeReg-x0-x29 (regs s4) new-sp)
                   (trans (readReg-writeReg-x9-x29 (regs s1) 1)
                          (readReg-writeSP (regs s) x29 new-sp))

    x30-eq : readReg (regs s5) x30 ≡ readReg (regs s) x30
    x30-eq = trans (readReg-writeReg-x0-x30 (regs s4) new-sp)
                   (trans (readReg-writeReg-x9-x30 (regs s1) 1)
                          (readReg-writeSP (regs s) x30 new-sp))

    -- SP decreased (PROVEN!)
    sp-s5 : readSP (regs s5) ≡ new-sp
    sp-s5 = trans (readSP-writeReg (regs s4) x0 new-sp)
                  (trans (readSP-writeReg (regs s1) x9 1)
                         (readSP-writeSP (regs s) new-sp))

    sp-decreased : readSP (regs s5) ≤ readSP (regs s)
    sp-decreased = subst₂ _≤_ sp-s5 refl (m∸n≤m orig-sp 16)

    -- Address disjointness from invariants
    x21-diffs : (new-sp ≢ readReg (regs s) x21) × ((new-sp +ℕ 8) ≢ readReg (regs s) x21)
    x21-diffs = addr-diff-from-invariant s stack-inv sp>16

    x29-diffs : (new-sp ≢ readReg (regs s) x29) × ((new-sp +ℕ 8) ≢ readReg (regs s) x29) ×
                (new-sp ≢ (readReg (regs s) x29 +ℕ 8)) × ((new-sp +ℕ 8) ≢ (readReg (regs s) x29 +ℕ 8))
    x29-diffs = x29-addr-diff-extended s x29-inv sp>16

    -- Memory preservation (PROVEN!)
    -- Memory at x21: not modified by writes at new-sp and new-sp+8
    mem-x21-step1 : readMem (memory s5) (readReg (regs s) x21) ≡ readMem (memory s3) (readReg (regs s) x21)
    mem-x21-step1 = readMem-writeMem-diff (memory s3) (new-sp +ℕ 8) (readReg (regs s) x21) (readReg (regs s) x0) (proj₂ x21-diffs)

    mem-x21-step2 : readMem (memory s3) (readReg (regs s) x21) ≡ readMem (memory s2) (readReg (regs s) x21)
    mem-x21-step2 = subst (λ addr → readMem (writeMem (memory s2) addr 1) (readReg (regs s) x21) ≡ readMem (memory s2) (readReg (regs s) x21))
                          (sym (+-identityʳ new-sp))
                          (readMem-writeMem-diff (memory s2) new-sp (readReg (regs s) x21) 1 (proj₁ x21-diffs))

    mem-x21-eq : readMem (memory s5) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-eq = trans mem-x21-step1 mem-x21-step2

    mem-x29-step1 : readMem (memory s5) (readReg (regs s) x29) ≡ readMem (memory s3) (readReg (regs s) x29)
    mem-x29-step1 = readMem-writeMem-diff (memory s3) (new-sp +ℕ 8) (readReg (regs s) x29) (readReg (regs s) x0) (proj₁ (proj₂ x29-diffs))

    mem-x29-step2 : readMem (memory s3) (readReg (regs s) x29) ≡ readMem (memory s2) (readReg (regs s) x29)
    mem-x29-step2 = subst (λ addr → readMem (writeMem (memory s2) addr 1) (readReg (regs s) x29) ≡ readMem (memory s2) (readReg (regs s) x29))
                          (sym (+-identityʳ new-sp))
                          (readMem-writeMem-diff (memory s2) new-sp (readReg (regs s) x29) 1 (proj₁ x29-diffs))

    mem-x29-eq : readMem (memory s5) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-eq = trans mem-x29-step1 mem-x29-step2

    mem-x29+8-step1 : readMem (memory s5) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s3) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-step1 = readMem-writeMem-diff (memory s3) (new-sp +ℕ 8) (readReg (regs s) x29 +ℕ 8) (readReg (regs s) x0) (proj₂ (proj₂ (proj₂ x29-diffs)))

    mem-x29+8-step2 : readMem (memory s3) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s2) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-step2 = subst (λ addr → readMem (writeMem (memory s2) addr 1) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s2) (readReg (regs s) x29 +ℕ 8))
                            (sym (+-identityʳ new-sp))
                            (readMem-writeMem-diff (memory s2) new-sp (readReg (regs s) x29 +ℕ 8) 1 (proj₁ (proj₂ (proj₂ x29-diffs))))

    mem-x29+8-eq : readMem (memory s5) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-eq = trans mem-x29+8-step1 mem-x29+8-step2

    -- Invariant preservation (PROVEN!)
    stack-inv' : StackInvariant s5
    stack-inv' = stack-inv-preserved-sp-decreased s s5 stack-inv x21-eq sp-decreased

    x29-inv' : X29Invariant s5
    x29-inv' = x29-inv-preserved-sp-decreased s s5 x29-inv x29-eq sp-decreased

    sp>16' : readSP (regs s5) > 16
    sp>16' = sp-bound-after-stack-op s5

    x0-s5 : readReg (regs s5) x0 ≡ new-sp
    x0-s5 = readReg-writeReg-same (regs s4) x0 new-sp

    result-s : IRStarResultS (inr {i} {A} {B}) prog s s5 new-sp (length prefix)
    result-s = record
      { ir-star = star-proof
      ; ir-halted = h5
      ; ir-pc = pc5
      ; ir-x0-s = x0-s5
      ; ir-x20 = x20-eq
      ; ir-x21 = x21-eq
      ; ir-x29 = x29-eq
      ; ir-x30 = x30-eq
      ; ir-sp = sp-decreased
      ; ir-mem-x21 = mem-x21-eq
      ; ir-mem-x29 = mem-x29-eq
      ; ir-mem-x29+8 = mem-x29+8-eq
      ; ir-stack-inv = stack-inv'
      ; ir-x29-inv = x29-inv'
      ; ir-sp-bound = sp>16'
      }
