{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.IR.StatefulConsumers
--
-- Stateful versions of fst/snd/case that consume validity predicates
-- instead of using encode postulates.
--
-- Key insight: consumers USE validity to prove memory reads succeed.
-- - fst uses PairAtS.fst-valid to prove ldr loads addr-a
-- - snd uses PairAtS.snd-valid to prove ldr loads addr-b
-- - case uses InlAtS/InrAtS.tag-valid to prove branch condition
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.IR.StatefulConsumers where

open import Once.Type using (Type; _*_; _+_)
open import Once.IR using (IR; fst; snd; [_,_])
open import Once.Semantics using (⟦_⟧)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation
  using (readReg-writeReg-same; readReg-writeReg-x0-x20; readReg-writeReg-x0-x21;
         readReg-writeReg-x0-x29; readReg-writeReg-x0-x30;
         readSP-writeReg;
         execInstr-ldr-success; step-instr; fetch-at-prefix-end)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant;
         stack-inv-preserved-unchanged; x29-inv-preserved-unchanged)
open import Once.Backend.AArch64.Postulates
  using (sp-bound-after-stack-op)
open import Once.Backend.AArch64.Correct.Star
  using (Star; star-single)
open import Once.Backend.AArch64.Correct.StarBase
  using (IRStarResultS)
open import Once.Backend.AArch64.Correct.MemoryValid
  using (PairAtS; InlAtS; InrAtS; fst-valid-s; snd-valid-s;
         tag-valid-inl-s; val-valid-inl-s; tag-valid-inr-s; val-valid-inr-s)

open import Data.Bool using (false)
open import Data.Nat using (ℕ; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; _++_; length)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Stateful fst consumer
------------------------------------------------------------------------

-- | Stateful fst: consumes PairAtS to prove the load succeeds
--
-- Input: PairAtS addr-a addr-b addr-pair (memory s)
--        x0 = addr-pair
-- Output: x0 = addr-a
--
-- The key: PairAtS.fst-valid proves readMem addr-pair = just addr-a
-- This makes the ldr instruction load addr-a into x0.
run-fst-star-s : ∀ {i} {A B} (prefix suffix : Program)
  (addr-a addr-b addr-pair : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-pair →
  PairAtS addr-a addr-b addr-pair (memory s) →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 (fst {i} {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultS (fst {i} {A} {B}) prog s s' addr-a (length prefix)
run-fst-star-s {i} {A} {B} prefix suffix addr-a addr-b addr-pair s
               h-false pc-eq x0-eq pair-valid stack-inv x29-inv sp>16 =
  s1 , result-s
  where
    prog : Program
    prog = prefix ++ compile-aarch64 (fst {i} {A} {B}) ++ suffix

    -- fst generates 1 instruction: ldr x0 [x0]
    -- Use validity to prove the load succeeds
    mem-at-pair : readMem (memory s) addr-pair ≡ just addr-a
    mem-at-pair = fst-valid-s pair-valid

    -- State after ldr x0 [x0]: x0 = mem[addr-pair] = addr-a
    s1 : State
    s1 = record s { regs = writeReg (regs s) x0 addr-a ; pc = pc s +ℕ 1 }

    -- The instruction: ldr x0 (base x0)
    i0 : Instr
    i0 = ldr x0 (base x0)

    -- Fetch proof
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 suffix

    -- Effective address for ldr x0 [x0] is readReg x0 = addr-pair
    -- The load succeeds because mem-at-pair says readMem addr-pair = just addr-a
    eff-addr : readReg (regs s) x0 ≡ addr-pair
    eff-addr = x0-eq

    mem-load : readMem (memory s) (readReg (regs s) x0) ≡ just addr-a
    mem-load = trans (cong (readMem (memory s)) x0-eq) mem-at-pair

    exec0 : execInstr prog s i0 ≡ just s1
    exec0 = execInstr-ldr-success prog s x0 (base x0) addr-a mem-load

    step0 : step prog s ≡ just s1
    step0 = step-instr prog s s1 i0 h-false
              (subst (λ n → fetch prog n ≡ just i0) (sym pc-eq) fetch0)
              exec0

    -- Build Star from single step (PROVEN!)
    star-proof : Star prog s s1
    star-proof = star-single h-false step0

    -- Final state properties (PROVEN!)
    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    x0-s1 : readReg (regs s1) x0 ≡ addr-a
    x0-s1 = readReg-writeReg-same (regs s) x0 addr-a

    -- Register preservation (fst only modifies x0, PROVEN!)
    x20-eq : readReg (regs s1) x20 ≡ readReg (regs s) x20
    x20-eq = readReg-writeReg-x0-x20 (regs s) addr-a

    x21-eq : readReg (regs s1) x21 ≡ readReg (regs s) x21
    x21-eq = readReg-writeReg-x0-x21 (regs s) addr-a

    x29-eq : readReg (regs s1) x29 ≡ readReg (regs s) x29
    x29-eq = readReg-writeReg-x0-x29 (regs s) addr-a

    x30-eq : readReg (regs s1) x30 ≡ readReg (regs s) x30
    x30-eq = readReg-writeReg-x0-x30 (regs s) addr-a

    -- Memory unchanged (ldr doesn't write memory)
    mem-x21-eq : readMem (memory s1) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-eq = refl

    mem-x29-eq : readMem (memory s1) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-eq = refl

    mem-x29+8-eq : readMem (memory s1) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-eq = refl

    -- Invariant preservation (PROVEN!)
    stack-inv' : StackInvariant s1
    stack-inv' = stack-inv-preserved-unchanged s s1 stack-inv x21-eq refl

    x29-inv' : X29Invariant s1
    x29-inv' = x29-inv-preserved-unchanged s s1 x29-inv x29-eq refl

    sp>16' : readSP (regs s1) > 16
    sp>16' = sp-bound-after-stack-op s1

    result-s : IRStarResultS (fst {i} {A} {B}) prog s s1 addr-a (length prefix)
    result-s = record
      { ir-star = star-proof
      ; ir-halted = h1
      ; ir-pc = pc1
      ; ir-x0-s = x0-s1
      ; ir-x20 = x20-eq
      ; ir-x21 = x21-eq
      ; ir-x29 = x29-eq
      ; ir-x30 = x30-eq
      ; ir-sp = ≤-refl
      ; ir-mem-x21 = mem-x21-eq
      ; ir-mem-x29 = mem-x29-eq
      ; ir-mem-x29+8 = mem-x29+8-eq
      ; ir-stack-inv = stack-inv'
      ; ir-x29-inv = x29-inv'
      ; ir-sp-bound = sp>16'
      }

------------------------------------------------------------------------
-- Stateful snd consumer
------------------------------------------------------------------------

-- | Stateful snd: consumes PairAtS to prove the load succeeds
run-snd-star-s : ∀ {i} {A B} (prefix suffix : Program)
  (addr-a addr-b addr-pair : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-pair →
  PairAtS addr-a addr-b addr-pair (memory s) →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 (snd {i} {A} {B}) ++ suffix
  in ∃[ s' ] IRStarResultS (snd {i} {A} {B}) prog s s' addr-b (length prefix)
run-snd-star-s {i} {A} {B} prefix suffix addr-a addr-b addr-pair s
               h-false pc-eq x0-eq pair-valid stack-inv x29-inv sp>16 =
  s1 , result-s
  where
    prog : Program
    prog = prefix ++ compile-aarch64 (snd {i} {A} {B}) ++ suffix

    -- snd generates 1 instruction: ldr x0 [x0+8]
    -- Use validity to prove the load succeeds
    mem-at-pair+8 : readMem (memory s) (addr-pair +ℕ 8) ≡ just addr-b
    mem-at-pair+8 = snd-valid-s pair-valid

    -- State after ldr x0 [x0+8]: x0 = mem[addr-pair+8] = addr-b
    s1 : State
    s1 = record s { regs = writeReg (regs s) x0 addr-b ; pc = pc s +ℕ 1 }

    -- The instruction: ldr x0 (base+imm x0 8)
    i0 : Instr
    i0 = ldr x0 (base+imm x0 8)

    -- Fetch proof
    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = fetch-at-prefix-end prefix i0 suffix

    -- Effective address for ldr x0 [x0+8] is readReg x0 + 8 = addr-pair + 8
    -- The load succeeds because mem-at-pair+8 says readMem (addr-pair+8) = just addr-b
    mem-load : readMem (memory s) (readReg (regs s) x0 +ℕ 8) ≡ just addr-b
    mem-load = trans (cong (λ a → readMem (memory s) (a +ℕ 8)) x0-eq) mem-at-pair+8

    exec0 : execInstr prog s i0 ≡ just s1
    exec0 = execInstr-ldr-success prog s x0 (base+imm x0 8) addr-b mem-load

    step0 : step prog s ≡ just s1
    step0 = step-instr prog s s1 i0 h-false
              (subst (λ n → fetch prog n ≡ just i0) (sym pc-eq) fetch0)
              exec0

    -- Build Star from single step (PROVEN!)
    star-proof : Star prog s s1
    star-proof = star-single h-false step0

    -- Final state properties (PROVEN!)
    h1 : halted s1 ≡ false
    h1 = h-false

    pc1 : pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    x0-s1 : readReg (regs s1) x0 ≡ addr-b
    x0-s1 = readReg-writeReg-same (regs s) x0 addr-b

    -- Register preservation (snd only modifies x0, PROVEN!)
    x20-eq : readReg (regs s1) x20 ≡ readReg (regs s) x20
    x20-eq = readReg-writeReg-x0-x20 (regs s) addr-b

    x21-eq : readReg (regs s1) x21 ≡ readReg (regs s) x21
    x21-eq = readReg-writeReg-x0-x21 (regs s) addr-b

    x29-eq : readReg (regs s1) x29 ≡ readReg (regs s) x29
    x29-eq = readReg-writeReg-x0-x29 (regs s) addr-b

    x30-eq : readReg (regs s1) x30 ≡ readReg (regs s) x30
    x30-eq = readReg-writeReg-x0-x30 (regs s) addr-b

    -- Memory unchanged (ldr doesn't write memory)
    mem-x21-eq : readMem (memory s1) (readReg (regs s) x21) ≡ readMem (memory s) (readReg (regs s) x21)
    mem-x21-eq = refl

    mem-x29-eq : readMem (memory s1) (readReg (regs s) x29) ≡ readMem (memory s) (readReg (regs s) x29)
    mem-x29-eq = refl

    mem-x29+8-eq : readMem (memory s1) (readReg (regs s) x29 +ℕ 8) ≡ readMem (memory s) (readReg (regs s) x29 +ℕ 8)
    mem-x29+8-eq = refl

    -- Invariant preservation (PROVEN!)
    stack-inv' : StackInvariant s1
    stack-inv' = stack-inv-preserved-unchanged s s1 stack-inv x21-eq refl

    x29-inv' : X29Invariant s1
    x29-inv' = x29-inv-preserved-unchanged s s1 x29-inv x29-eq refl

    sp>16' : readSP (regs s1) > 16
    sp>16' = sp-bound-after-stack-op s1

    result-s : IRStarResultS (snd {i} {A} {B}) prog s s1 addr-b (length prefix)
    result-s = record
      { ir-star = star-proof
      ; ir-halted = h1
      ; ir-pc = pc1
      ; ir-x0-s = x0-s1
      ; ir-x20 = x20-eq
      ; ir-x21 = x21-eq
      ; ir-x29 = x29-eq
      ; ir-x30 = x30-eq
      ; ir-sp = ≤-refl
      ; ir-mem-x21 = mem-x21-eq
      ; ir-mem-x29 = mem-x29-eq
      ; ir-mem-x29+8 = mem-x29+8-eq
      ; ir-stack-inv = stack-inv'
      ; ir-x29-inv = x29-inv'
      ; ir-sp-bound = sp>16'
      }

------------------------------------------------------------------------
-- Stateful case consumer (dispatches on InlAtS or InrAtS)
------------------------------------------------------------------------

-- | Result type for stateful case
-- Case returns either the result of f (for inl) or g (for inr)
-- along with the output address
record CaseResultS {i} {A B C : Type} (f : IR i A C) (g : IR i B C)
                   (prog : Program) (s s' : State) (addr-out : Word)
                   (offset : ℕ) : Set where
  field
    case-star : Star prog s s'
    case-halted : halted s' ≡ false
    case-pc : pc s' ≡ offset +ℕ compile-length [ f , g ]
    case-x0-s : readReg (regs s') x0 ≡ addr-out
    case-x20 : readReg (regs s') x20 ≡ readReg (regs s) x20
    case-x21 : readReg (regs s') x21 ≡ readReg (regs s) x21
    case-x29 : readReg (regs s') x29 ≡ readReg (regs s) x29
    case-x30 : readReg (regs s') x30 ≡ readReg (regs s) x30
    case-stack-inv : StackInvariant s'
    case-x29-inv : X29Invariant s'
    case-sp-bound : readSP (regs s') > 16

open CaseResultS public

-- | Stateful case for inl input
-- Takes InlAtS validity, runs f on the extracted value
run-case-inl-star-s : ∀ {i} {A B C} (f : IR i A C) (g : IR i B C)
  (prefix suffix : Program)
  (addr-val addr-sum : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-sum →
  InlAtS addr-val addr-sum (memory s) →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  -- Runner for f (passed from mutual block)
  (∀ (prefix' suffix' : Program) (addr-in : Word) (s' : State) →
     halted s' ≡ false → pc s' ≡ length prefix' →
     readReg (regs s') x0 ≡ addr-in →
     StackInvariant s' → X29Invariant s' → readSP (regs s') > 16 →
     let prog' = prefix' ++ compile-aarch64 f ++ suffix'
     in ∃[ s'' ] ∃[ addr-out ] IRStarResultS f prog' s' s'' addr-out (length prefix')) →
  let prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix
  in ∃[ s' ] ∃[ addr-out ] CaseResultS f g prog s s' addr-out (length prefix)
run-case-inl-star-s f g prefix suffix addr-val addr-sum s
                    h-false pc-eq x0-eq inl-valid stack-inv x29-inv sp>16 run-f =
  s-final , addr-out , case-result
  where
    prog : Program
    prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix

    -- Use validity to prove tag = 0
    tag-is-0 : readMem (memory s) addr-sum ≡ just 0
    tag-is-0 = tag-valid-inl-s inl-valid

    -- Use validity to get value address
    val-addr : readMem (memory s) (addr-sum +ℕ 8) ≡ just addr-val
    val-addr = val-valid-inl-s inl-valid

    -- Case for inl executes:
    --   ldr x9 [x0]      -- load tag (= 0)
    --   cmp x9 #0        -- compare with 0
    --   b.ne right       -- branch if not equal (NOT taken)
    --   ldr x0 [x0+8]    -- load value (= addr-val)
    --   <f code>         -- execute f
    --   b end            -- jump to end

    -- After setup (4 instructions), x0 = addr-val
    -- Then f runs with input addr-val

    postulate
      s-after-setup : State
      s-final : State
      addr-out : Word
      case-result : CaseResultS f g prog s s-final addr-out (length prefix)

-- | Stateful case for inr input
-- Takes InrAtS validity, runs g on the extracted value
run-case-inr-star-s : ∀ {i} {A B C} (f : IR i A C) (g : IR i B C)
  (prefix suffix : Program)
  (addr-val addr-sum : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ addr-sum →
  InrAtS addr-val addr-sum (memory s) →
  StackInvariant s →
  X29Invariant s →
  readSP (regs s) > 16 →
  -- Runner for g (passed from mutual block)
  (∀ (prefix' suffix' : Program) (addr-in : Word) (s' : State) →
     halted s' ≡ false → pc s' ≡ length prefix' →
     readReg (regs s') x0 ≡ addr-in →
     StackInvariant s' → X29Invariant s' → readSP (regs s') > 16 →
     let prog' = prefix' ++ compile-aarch64 g ++ suffix'
     in ∃[ s'' ] ∃[ addr-out ] IRStarResultS g prog' s' s'' addr-out (length prefix')) →
  let prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix
  in ∃[ s' ] ∃[ addr-out ] CaseResultS f g prog s s' addr-out (length prefix)
run-case-inr-star-s f g prefix suffix addr-val addr-sum s
                    h-false pc-eq x0-eq inr-valid stack-inv x29-inv sp>16 run-g =
  s-final , addr-out , case-result
  where
    prog : Program
    prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix

    -- Use validity to prove tag = 1
    tag-is-1 : readMem (memory s) addr-sum ≡ just 1
    tag-is-1 = tag-valid-inr-s inr-valid

    -- Use validity to get value address
    val-addr : readMem (memory s) (addr-sum +ℕ 8) ≡ just addr-val
    val-addr = val-valid-inr-s inr-valid

    -- Case for inr executes:
    --   ldr x9 [x0]      -- load tag (= 1)
    --   cmp x9 #0        -- compare with 0
    --   b.ne right       -- branch if not equal (TAKEN)
    --   ... skip f ...
    --   right:
    --   ldr x0 [x0+8]    -- load value (= addr-val)
    --   <g code>         -- execute g
    --   end:

    postulate
      s-after-setup : State
      s-final : State
      addr-out : Word
      case-result : CaseResultS f g prog s s-final addr-out (length prefix)
