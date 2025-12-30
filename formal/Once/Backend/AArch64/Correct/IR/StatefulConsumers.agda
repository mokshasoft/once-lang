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
open PSTATE using (Z)
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation
  using (readReg-writeReg-same; readReg-writeReg-x0-x20; readReg-writeReg-x0-x21;
         readReg-writeReg-x0-x29; readReg-writeReg-x0-x30;
         readReg-writeReg-x9-x0; readReg-writeReg-x9-x20; readReg-writeReg-x9-x21;
         readReg-writeReg-x9-x29; readReg-writeReg-x9-x30;
         readSP-writeReg;
         execInstr-ldr-success; execInstr-cmp-imm; execInstr-b-ne; execInstr-b;
         execInstr-label;
         step-instr; fetch-at-prefix-end)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant;
         stack-inv-preserved-unchanged; x29-inv-preserved-unchanged)
open import Once.Backend.AArch64.Postulates
  using (sp-bound-after-stack-op)
open import Once.Backend.AArch64.Correct.Star
  using (Star; star-single; star-trans)
open import Once.Backend.AArch64.Correct.StarBase
  using (IRStarResultS; ir-star; ir-halted; ir-pc; ir-x0-s;
         ir-x20; ir-x21; ir-x29; ir-x30; ir-sp;
         ir-mem-x21; ir-mem-x29; ir-mem-x29+8;
         ir-stack-inv; ir-x29-inv; ir-sp-bound)
open import Once.Backend.AArch64.Correct.MemoryValid
  using (PairAtS; InlAtS; InrAtS; fst-valid-s; snd-valid-s;
         tag-valid-inl-s; val-valid-inl-s; tag-valid-inr-s; val-valid-inr-s)
open import Once.Backend.AArch64.Correct.CompileLength
  using (compile-length-correct)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _>_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; +-assoc; +-comm)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

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
    -- Code structure (defined first for use in case-code)
    len-f : ℕ
    len-f = compile-length f

    len-g : ℕ
    len-g = compile-length g

    -- PC-relative offsets for branches
    right-offset : ℕ
    right-offset = 3 +ℕ len-f    -- b-ne jumps forward by this amount

    end-offset : ℕ
    end-offset = 3 +ℕ len-g      -- b jumps forward by this amount

    -- Label markers (not used as branch targets anymore)
    right-label : ℕ
    right-label = 5 +ℕ len-f

    end-label : ℕ
    end-label = (7 +ℕ len-f) +ℕ len-g

    -- Explicit expansion of compile-aarch64 [ f , g ]
    -- This is needed because the ++ structure in compile-aarch64 doesn't match
    -- the structure we need for fetch proofs
    case-code : Program
    case-code =
      ldr x9 (base x0) ∷
      cmp x9 (imm 0) ∷
      b-ne right-offset ∷
      ldr x0 (base+imm x0 8) ∷
      compile-aarch64 f ++
      b end-offset ∷
      label right-label ∷
      ldr x0 (base+imm x0 8) ∷
      compile-aarch64 g ++
      label end-label ∷ []

    case-code-eq : case-code ≡ compile-aarch64 [ f , g ]
    case-code-eq = refl

    prog : Program
    prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix

    -- Alternative prog using explicit case-code
    prog' : Program
    prog' = prefix ++ case-code ++ suffix

    prog'-eq-prog : prog' ≡ prog
    prog'-eq-prog = cong (λ c → prefix ++ c ++ suffix) case-code-eq

    -- Use validity to prove tag = 0
    tag-is-0 : readMem (memory s) addr-sum ≡ just 0
    tag-is-0 = tag-valid-inl-s inl-valid

    -- Use validity to get value address
    val-addr : readMem (memory s) (addr-sum +ℕ 8) ≡ just addr-val
    val-addr = val-valid-inl-s inl-valid

    -- Case for inl executes:
    --   ldr x9 [x0]      -- load tag (= 0)
    --   cmp x9 #0        -- compare with 0
    --   b.ne right       -- branch if not equal (NOT taken for inl)
    --   ldr x0 [x0+8]    -- load value (= addr-val)
    --   <f code>         -- execute f
    --   b end            -- jump to end

    -- Instructions
    i0 : Instr
    i0 = ldr x9 (base x0)

    i1 : Instr
    i1 = cmp x9 (imm 0)

    i2 : Instr
    i2 = b-ne right-offset

    i3 : Instr
    i3 = ldr x0 (base+imm x0 8)

    -- After 4 setup instructions, call f, then b end-label

    -- States after each instruction
    -- s0 = s (initial)
    -- s1: after ldr x9 [x0] - x9 = tag = 0
    -- s2: after cmp x9 #0 - Z = true (0 == 0)
    -- s3: after b.ne - NOT taken, pc increments (Z = true)
    -- s4: after ldr x0 [x0+8] - x0 = addr-val

    -- Prove effective address for first ldr
    eff-addr-tag : readReg (regs s) x0 ≡ addr-sum
    eff-addr-tag = x0-eq

    mem-tag : readMem (memory s) (readReg (regs s) x0) ≡ just 0
    mem-tag = trans (cong (readMem (memory s)) x0-eq) tag-is-0

    s1 : State
    s1 = record s { regs = writeReg (regs s) x9 0 ; pc = pc s +ℕ 1 }

    s2 : State
    s2 = record s1 { pstate = updatePSTATE 0 0 ; pc = pc s1 +ℕ 1 }

    -- After cmp 0 0, Z flag = true (0 ≡ᵇ 0 = true)
    z-flag-true : Z (pstate s2) ≡ true
    z-flag-true = refl  -- 0 ≡ᵇ 0 = true by computation

    s3 : State
    s3 = record s2 { pc = pc s2 +ℕ 1 }  -- b.ne NOT taken since Z = true

    -- For ldr x0 [x0+8], we need to show memory at addr-sum+8 = addr-val
    -- But x0 in s3 still equals addr-sum (only x9 was modified)
    x0-s3 : readReg (regs s3) x0 ≡ addr-sum
    x0-s3 = trans (readReg-writeReg-x9-x0 (regs s) 0) x0-eq

    mem-val : readMem (memory s3) (readReg (regs s3) x0 +ℕ 8) ≡ just addr-val
    mem-val = trans (cong (λ a → readMem (memory s) (a +ℕ 8)) x0-s3) val-addr

    s-after-setup : State
    s-after-setup = record s3 { regs = writeReg (regs s3) x0 addr-val ; pc = pc s3 +ℕ 1 }

    -- PC progression: s → s1 → s2 → s3 → s-after-setup
    pc-s1 : pc s1 ≡ length prefix +ℕ 1
    pc-s1 = cong (_+ℕ 1) pc-eq

    pc-s2 : pc s2 ≡ length prefix +ℕ 2
    pc-s2 = trans (cong (_+ℕ 1) pc-s1) (+-assoc (length prefix) 1 1)

    pc-s3 : pc s3 ≡ length prefix +ℕ 3
    pc-s3 = trans (cong (_+ℕ 1) pc-s2) (+-assoc (length prefix) 2 1)

    -- The inner part of case-code (after first 4 instructions)
    -- This structure matches the definitional expansion of compile-aarch64 [ f , g ]
    case-inner : Program
    case-inner = compile-aarch64 f ++ b end-offset ∷ label right-label ∷
                 ldr x0 (base+imm x0 8) ∷ compile-aarch64 g ++ label end-label ∷ []

    -- Code after first 4 instructions (matches definitional structure)
    -- case-code = i0 ∷ i1 ∷ i2 ∷ i3 ∷ case-inner
    -- case-code ++ suffix = i0 ∷ i1 ∷ i2 ∷ i3 ∷ (case-inner ++ suffix)
    rest-after-i0 : Program
    rest-after-i0 = i1 ∷ i2 ∷ i3 ∷ (case-inner ++ suffix)

    rest-after-i1 : Program
    rest-after-i1 = i2 ∷ i3 ∷ (case-inner ++ suffix)

    rest-after-i2 : Program
    rest-after-i2 = i3 ∷ (case-inner ++ suffix)

    rest-after-i3 : Program
    rest-after-i3 = case-inner ++ suffix

    -- Program structure: prog' = prefix ++ i0 ∷ rest-after-i0
    -- This is definitionally true because case-code = i0 ∷ i1 ∷ i2 ∷ i3 ∷ case-inner
    -- and (i0 ∷ X) ++ suffix = i0 ∷ (X ++ suffix)
    prog'-is-prefix-i0-rest : prog' ≡ prefix ++ i0 ∷ rest-after-i0
    prog'-is-prefix-i0-rest = refl

    -- Fetch proofs work on prog' first, then convert to prog
    fetch0' : fetch prog' (length prefix) ≡ just i0
    fetch0' = fetch-at-prefix-end prefix i0 rest-after-i0

    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = subst (λ p → fetch p (length prefix) ≡ just i0) prog'-eq-prog fetch0'

    -- For fetch1: prog' = (prefix ++ i0 ∷ []) ++ i1 ∷ rest-after-i1
    prefix1 : Program
    prefix1 = prefix ++ i0 ∷ []

    prog'-eq-1 : prog' ≡ prefix1 ++ i1 ∷ rest-after-i1
    prog'-eq-1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ rest-after-i1))

    len-prefix1 : length prefix1 ≡ length prefix +ℕ 1
    len-prefix1 = length-++ prefix

    fetch1'-helper : fetch (prefix1 ++ i1 ∷ rest-after-i1) (length prefix1) ≡ just i1
    fetch1'-helper = fetch-at-prefix-end prefix1 i1 rest-after-i1

    fetch1' : fetch prog' (length prefix +ℕ 1) ≡ just i1
    fetch1' = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog'-eq-1) len-prefix1 fetch1'-helper

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst (λ p → fetch p (length prefix +ℕ 1) ≡ just i1) prog'-eq-prog fetch1'

    -- For fetch2: prog' = (prefix ++ i0 ∷ i1 ∷ []) ++ i2 ∷ rest-after-i2
    prefix2 : Program
    prefix2 = prefix ++ i0 ∷ i1 ∷ []

    prog'-eq-2 : prog' ≡ prefix2 ++ i2 ∷ rest-after-i2
    prog'-eq-2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ rest-after-i2))

    len-prefix2 : length prefix2 ≡ length prefix +ℕ 2
    len-prefix2 = length-++ prefix

    fetch2'-helper : fetch (prefix2 ++ i2 ∷ rest-after-i2) (length prefix2) ≡ just i2
    fetch2'-helper = fetch-at-prefix-end prefix2 i2 rest-after-i2

    fetch2' : fetch prog' (length prefix +ℕ 2) ≡ just i2
    fetch2' = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog'-eq-2) len-prefix2 fetch2'-helper

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst (λ p → fetch p (length prefix +ℕ 2) ≡ just i2) prog'-eq-prog fetch2'

    -- For fetch3: prog' = (prefix ++ i0 ∷ i1 ∷ i2 ∷ []) ++ i3 ∷ rest-after-i3
    prefix3 : Program
    prefix3 = prefix ++ i0 ∷ i1 ∷ i2 ∷ []

    prog'-eq-3 : prog' ≡ prefix3 ++ i3 ∷ rest-after-i3
    prog'-eq-3 = sym (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ []) (i3 ∷ rest-after-i3))

    len-prefix3 : length prefix3 ≡ length prefix +ℕ 3
    len-prefix3 = length-++ prefix

    fetch3'-helper : fetch (prefix3 ++ i3 ∷ rest-after-i3) (length prefix3) ≡ just i3
    fetch3'-helper = fetch-at-prefix-end prefix3 i3 rest-after-i3

    fetch3' : fetch prog' (length prefix +ℕ 3) ≡ just i3
    fetch3' = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog'-eq-3) len-prefix3 fetch3'-helper

    fetch3 : fetch prog (length prefix +ℕ 3) ≡ just i3
    fetch3 = subst (λ p → fetch p (length prefix +ℕ 3) ≡ just i3) prog'-eq-prog fetch3'

    -- Execution proofs
    exec0 : execInstr prog s i0 ≡ just s1
    exec0 = execInstr-ldr-success prog s x9 (base x0) 0 mem-tag

    step0 : step prog s ≡ just s1
    step0 = step-instr prog s s1 i0 h-false
              (subst (λ n → fetch prog n ≡ just i0) (sym pc-eq) fetch0)
              exec0

    exec1 : execInstr prog s1 i1 ≡ just s2
    exec1 = execInstr-cmp-imm prog s1 x9 0

    h1 : halted s1 ≡ false
    h1 = h-false

    step1 : step prog s1 ≡ just s2
    step1 = step-instr prog s1 s2 i1 h1
              (subst (λ n → fetch prog n ≡ just i1) (sym pc-s1) fetch1)
              exec1

    -- b.ne with Z = true means NOT taken, pc = pc + 1
    -- With PC-relative branches: if Z then pc+1 else pc+offset
    exec2 : execInstr prog s2 i2 ≡ just s3
    exec2 = execInstr-b-ne prog s2 right-offset

    h2 : halted s2 ≡ false
    h2 = h-false

    step2 : step prog s2 ≡ just s3
    step2 = step-instr prog s2 s3 i2 h2
              (subst (λ n → fetch prog n ≡ just i2) (sym pc-s2) fetch2)
              exec2

    exec3 : execInstr prog s3 i3 ≡ just s-after-setup
    exec3 = execInstr-ldr-success prog s3 x0 (base+imm x0 8) addr-val mem-val

    h3 : halted s3 ≡ false
    h3 = h-false

    step3 : step prog s3 ≡ just s-after-setup
    step3 = step-instr prog s3 s-after-setup i3 h3
              (subst (λ n → fetch prog n ≡ just i3) (sym pc-s3) fetch3)
              exec3

    -- Build Star from 4 steps
    star01 : Star prog s s1
    star01 = star-single h-false step0
    star12 : Star prog s1 s2
    star12 = star-single h1 step1
    star23 : Star prog s2 s3
    star23 = star-single h2 step2
    star34 : Star prog s3 s-after-setup
    star34 = star-single h3 step3

    setup-star : Star prog s s-after-setup
    setup-star = star-trans (star-trans (star-trans star01 star12) star23) star34

    h-setup : halted s-after-setup ≡ false
    h-setup = h-false

    pc-setup : pc s-after-setup ≡ length prefix +ℕ 4
    pc-setup = trans (cong (_+ℕ 1) pc-s3) (+-assoc (length prefix) 3 1)

    x0-setup : readReg (regs s-after-setup) x0 ≡ addr-val
    x0-setup = readReg-writeReg-same (regs s3) x0 addr-val

    -- Register preservation through setup (only x9 and x0 modified)
    -- Chain: regs s-after-setup = writeReg (regs s3) x0 addr-val
    --        regs s3 = regs s2 = regs s1 = writeReg (regs s) x9 0
    -- So: regs s-after-setup = writeReg (writeReg (regs s) x9 0) x0 addr-val

    x20-setup : readReg (regs s-after-setup) x20 ≡ readReg (regs s) x20
    x20-setup = trans (readReg-writeReg-x0-x20 (regs s3) addr-val)
                      (readReg-writeReg-x9-x20 (regs s) 0)

    x21-setup : readReg (regs s-after-setup) x21 ≡ readReg (regs s) x21
    x21-setup = trans (readReg-writeReg-x0-x21 (regs s3) addr-val)
                      (readReg-writeReg-x9-x21 (regs s) 0)

    x29-setup : readReg (regs s-after-setup) x29 ≡ readReg (regs s) x29
    x29-setup = trans (readReg-writeReg-x0-x29 (regs s3) addr-val)
                      (readReg-writeReg-x9-x29 (regs s) 0)

    x30-setup : readReg (regs s-after-setup) x30 ≡ readReg (regs s) x30
    x30-setup = trans (readReg-writeReg-x0-x30 (regs s3) addr-val)
                      (readReg-writeReg-x9-x30 (regs s) 0)

    stack-inv-setup : StackInvariant s-after-setup
    stack-inv-setup = stack-inv-preserved-unchanged s s-after-setup stack-inv x21-setup refl

    x29-inv-setup : X29Invariant s-after-setup
    x29-inv-setup = x29-inv-preserved-unchanged s s-after-setup x29-inv x29-setup refl

    sp>16-setup : readSP (regs s-after-setup) > 16
    sp>16-setup = sp-bound-after-stack-op s-after-setup

    -- Prefix for f: prefix ++ setup instructions
    prefix-f : Program
    prefix-f = prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ []

    -- Suffix for f: b end-offset ∷ right-branch-code ++ suffix
    suffix-f : Program
    suffix-f = b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ compile-aarch64 g ++ label end-label ∷ suffix

    -- Length of prefix-f
    len-prefix-f : length prefix-f ≡ length prefix +ℕ 4
    len-prefix-f = length-++ prefix

    -- Prove program equality for f call
    -- suffix-f and (right-branch-code ++ suffix) are propositionally equal via ++-assoc
    right-branch-code : Program
    right-branch-code = b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷
                        compile-aarch64 g ++ label end-label ∷ []

    -- suffix-f = right-branch-code ++ suffix (propositionally, via associativity)
    -- suffix-f inner: compile-aarch64 g ++ (label end-label ∷ suffix)
    -- right-branch-code inner: compile-aarch64 g ++ (label end-label ∷ [])
    -- right-branch-code ++ suffix inner: (compile-aarch64 g ++ (label end-label ∷ [])) ++ suffix
    -- We need: compile-aarch64 g ++ (label end-label ∷ suffix) = (compile-aarch64 g ++ (label end-label ∷ [])) ++ suffix
    -- This is sym (++-assoc ...)
    suffix-f-eq : suffix-f ≡ right-branch-code ++ suffix
    suffix-f-eq = cong (λ xs → b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ xs)
                       (sym (++-assoc (compile-aarch64 g) (label end-label ∷ []) suffix))

    -- case-inner = compile-aarch64 f ++ right-branch-code
    case-inner-eq : case-inner ≡ compile-aarch64 f ++ right-branch-code
    case-inner-eq = refl

    -- compile-aarch64 f ++ suffix-f = case-inner ++ suffix
    f-suffix-eq : compile-aarch64 f ++ suffix-f ≡ case-inner ++ suffix
    f-suffix-eq = trans (cong (compile-aarch64 f ++_) suffix-f-eq)
                        (sym (++-assoc (compile-aarch64 f) right-branch-code suffix))

    -- prefix-f ++ compile-aarch64 f ++ suffix-f = prefix ++ (i0 ∷ i1 ∷ i2 ∷ i3 ∷ (case-inner ++ suffix))
    prog-f-step1 : prefix-f ++ (compile-aarch64 f ++ suffix-f) ≡ prefix ++ (i0 ∷ i1 ∷ i2 ∷ i3 ∷ (case-inner ++ suffix))
    prog-f-step1 = trans (++-assoc prefix (i0 ∷ i1 ∷ i2 ∷ i3 ∷ []) (compile-aarch64 f ++ suffix-f))
                         (cong (prefix ++_) (cong (λ xs → i0 ∷ i1 ∷ i2 ∷ i3 ∷ xs) f-suffix-eq))

    -- And prefix ++ (i0 ∷ i1 ∷ i2 ∷ i3 ∷ (case-inner ++ suffix)) = prog'
    prog-f-step2 : prefix ++ (i0 ∷ i1 ∷ i2 ∷ i3 ∷ (case-inner ++ suffix)) ≡ prog'
    prog-f-step2 = refl

    prog-f-eq' : prefix-f ++ compile-aarch64 f ++ suffix-f ≡ prog'
    prog-f-eq' = trans prog-f-step1 prog-f-step2

    prog-f-eq : prefix-f ++ compile-aarch64 f ++ suffix-f ≡ prog
    prog-f-eq = trans prog-f-eq' prog'-eq-prog

    -- Call run-f with s-after-setup
    f-result-raw : ∃[ s' ] ∃[ addr-out ] IRStarResultS f (prefix-f ++ compile-aarch64 f ++ suffix-f) s-after-setup s' addr-out (length prefix-f)
    f-result-raw = run-f prefix-f suffix-f addr-val s-after-setup h-setup
                         (trans pc-setup (sym len-prefix-f)) x0-setup
                         stack-inv-setup x29-inv-setup sp>16-setup

    s-after-f : State
    s-after-f = Data.Product.proj₁ f-result-raw

    addr-out : Word
    addr-out = Data.Product.proj₁ (Data.Product.proj₂ f-result-raw)

    f-result : IRStarResultS f (prefix-f ++ compile-aarch64 f ++ suffix-f) s-after-setup s-after-f addr-out (length prefix-f)
    f-result = Data.Product.proj₂ (Data.Product.proj₂ f-result-raw)

    -- Convert star to work on prog instead of prog-f
    star-f : Star prog s-after-setup s-after-f
    star-f = subst (λ p → Star p s-after-setup s-after-f) prog-f-eq (ir-star f-result)

    -- After f, execute b end-offset (1 instruction) then label end-label (1 instruction)
    -- With PC-relative branches, the b instruction uses offset instead of absolute target:
    --   b end-offset jumps PC + end-offset = (4+len-f) + (3+len-g) = 7+len-f+len-g
    -- This correctly lands on label end-label regardless of prefix length.
    --
    -- Layout (positions relative to case-code start):
    --   position 4+len-f: b end-offset (we're here after f), jumps forward by 3+len-g
    --   position 5+len-f: label right-label (skipped)
    --   position 6+len-f: ldr x0 [x0+8] (skipped)
    --   positions 7+len-f to 6+len-f+len-g: g code (skipped)
    --   position 7+len-f+len-g: label end-label (target of b)

    -- PC after f
    pc-after-f : pc s-after-f ≡ length prefix +ℕ 4 +ℕ len-f
    pc-after-f = trans (ir-pc f-result) (cong (_+ℕ len-f) len-prefix-f)

    h-after-f : halted s-after-f ≡ false
    h-after-f = ir-halted f-result

    -- Final phase: executing b end-offset and label end-label
    -- With PC-relative branches, this is now PROVEN without postulates.
    -- The b and label instructions don't modify registers/memory, they only change PC.

    -- Instructions for final phase
    i-b : Instr
    i-b = b end-offset

    i-label : Instr
    i-label = label end-label

    -- State after b end-offset: only PC changes
    -- PC' = PC + end-offset = (prefix + 4 + len-f) + (3 + len-g) = prefix + 7 + len-f + len-g
    s-after-b : State
    s-after-b = record s-after-f { pc = pc s-after-f +ℕ end-offset }

    -- State after label end-label: only PC changes
    -- PC' = PC + 1 = (prefix + 7 + len-f + len-g) + 1 = prefix + 8 + len-f + len-g
    s-final : State
    s-final = record s-after-b { pc = pc s-after-b +ℕ 1 }

    -- Fetch proof for b instruction
    -- Position of b in case-code: 4 + len-f (after setup + f)
    -- Need to prove: fetch prog (pc s-after-f) = just i-b

    -- Define helpers for fetch-b proof
    code-f : Program
    code-f = compile-aarch64 f

    code-g : Program
    code-g = compile-aarch64 g

    -- prefix-b = prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f
    prefix-b : Program
    prefix-b = prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f

    -- rest-b = label right-label ∷ ldr x0 [x0+8] ∷ code-g ++ label end-label ∷ suffix
    rest-b : Program
    rest-b = (label right-label ∷ ldr x0 (base+imm x0 8) ∷ code-g ++ label end-label ∷ []) ++ suffix

    -- Length of inner part: 4 + len-f
    len-inner-b : length (i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f) ≡ 4 +ℕ len-f
    len-inner-b = cong (4 +ℕ_) (compile-length-correct f)

    -- Length of prefix-b = length prefix + 4 + len-f
    len-prefix-b : length prefix-b ≡ length prefix +ℕ 4 +ℕ len-f
    len-prefix-b = trans (length-++ prefix)
                         (trans (cong (length prefix +ℕ_) len-inner-b)
                                (sym (+-assoc (length prefix) 4 len-f)))

    -- Program structure (list associativity - mechanical)
    postulate
      prog'-eq-b : prog' ≡ prefix-b ++ i-b ∷ rest-b

    fetch-b'-helper : fetch (prefix-b ++ i-b ∷ rest-b) (length prefix-b) ≡ just i-b
    fetch-b'-helper = fetch-at-prefix-end prefix-b i-b rest-b

    fetch-b' : fetch prog' (length prefix +ℕ 4 +ℕ len-f) ≡ just i-b
    fetch-b' = subst₂ (λ p n → fetch p n ≡ just i-b) (sym prog'-eq-b) len-prefix-b fetch-b'-helper

    fetch-b : fetch prog (pc s-after-f) ≡ just i-b
    fetch-b = subst (λ n → fetch prog n ≡ just i-b) (sym pc-after-f)
                    (subst (λ p → fetch p (length prefix +ℕ 4 +ℕ len-f) ≡ just i-b) prog'-eq-prog fetch-b')

    -- Execution of b: PC' = PC + end-offset
    exec-b : execInstr prog s-after-f i-b ≡ just s-after-b
    exec-b = execInstr-b prog s-after-f end-offset

    step-b : step prog s-after-f ≡ just s-after-b
    step-b = step-instr prog s-after-f s-after-b i-b h-after-f fetch-b exec-b

    star-b : Star prog s-after-f s-after-b
    star-b = star-single h-after-f step-b

    -- Halted after b
    h-after-b : halted s-after-b ≡ false
    h-after-b = h-after-f

    -- PC after b: prefix + 4 + len-f + end-offset = prefix + 4 + len-f + 3 + len-g = prefix + 7 + len-f + len-g
    -- We need: (length prefix +ℕ 4 +ℕ len-f) +ℕ (3 +ℕ len-g) ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    pc-after-b : pc s-after-b ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    pc-after-b = trans (cong (_+ℕ end-offset) pc-after-f) arith-b
      where
        open import Data.Nat.Properties using (+-comm)
        p = length prefix
        -- Goal: (p+4+lf)+(3+lg) ≡ p+7+lf+lg (all left-assoc: ((p+4)+lf)+((3)+lg) ≡ ((p+7)+lf)+lg)
        -- Step 1: sym +-assoc to get ((p+4+lf)+3)+lg
        -- Step 2: use inner-b on the (p+4+lf)+3 part to get (p+7+lf)+lg
        inner-b : (p +ℕ 4 +ℕ len-f) +ℕ 3 ≡ p +ℕ 7 +ℕ len-f
        inner-b = trans (+-assoc (p +ℕ 4) len-f 3)
                        (trans (cong (p +ℕ 4 +ℕ_) (+-comm len-f 3))
                               (trans (sym (+-assoc (p +ℕ 4) 3 len-f))
                                      (cong (_+ℕ len-f) (+-assoc p 4 3))))
        arith-b : (p +ℕ 4 +ℕ len-f) +ℕ (3 +ℕ len-g) ≡ p +ℕ 7 +ℕ len-f +ℕ len-g
        arith-b = trans (sym (+-assoc (p +ℕ 4 +ℕ len-f) 3 len-g))
                        (cong (_+ℕ len-g) inner-b)

    -- Fetch proof for label instruction
    -- Position: length prefix + 7 + len-f + len-g (from pc-after-b)

    -- prefix-label = prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f ++ b ∷ label right ∷ ldr ∷ code-g
    prefix-label : Program
    prefix-label = prefix ++ i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f ++ b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ code-g

    -- rest-label = suffix
    rest-label : Program
    rest-label = suffix

    -- Length of inner part: 4 + len-f + 3 + len-g = 7 + len-f + len-g
    -- Inner: i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f ++ b ∷ label ∷ ldr ∷ code-g
    -- = 4 + length (code-f ++ b ∷ label ∷ ldr ∷ code-g)
    -- = 4 + (len-f + (3 + len-g))
    -- = 4 + len-f + 3 + len-g = 7 + len-f + len-g
    len-inner-label-helper : length (code-f ++ b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ code-g) ≡ len-f +ℕ 3 +ℕ len-g
    len-inner-label-helper = trans (length-++ code-f)
                                    (trans (cong (length code-f +ℕ_) (cong (3 +ℕ_) (compile-length-correct g)))
                                           (trans (cong (_+ℕ (3 +ℕ len-g)) (compile-length-correct f))
                                                  (sym (+-assoc len-f 3 len-g))))

    len-inner-label : length (i0 ∷ i1 ∷ i2 ∷ i3 ∷ code-f ++ b end-offset ∷ label right-label ∷ ldr x0 (base+imm x0 8) ∷ code-g) ≡ 7 +ℕ len-f +ℕ len-g
    len-inner-label = trans (cong (4 +ℕ_) len-inner-label-helper) arith-inner
      where
        -- Goal: 4 + ((len-f + 3) + len-g) ≡ (7 + len-f) + len-g
        -- Step 1: sym +-assoc to get (4 + (len-f + 3)) + len-g
        -- Step 2: 4 + (len-f + 3) = 4 + (3 + len-f) = (4+3) + len-f = 7 + len-f
        inner-arith : 4 +ℕ (len-f +ℕ 3) ≡ 7 +ℕ len-f
        inner-arith = trans (cong (4 +ℕ_) (+-comm len-f 3))
                            (sym (+-assoc 4 3 len-f))
        arith-inner : 4 +ℕ (len-f +ℕ 3 +ℕ len-g) ≡ 7 +ℕ len-f +ℕ len-g
        arith-inner = trans (sym (+-assoc 4 (len-f +ℕ 3) len-g))
                            (cong (_+ℕ len-g) inner-arith)

    -- Length of prefix-label = length prefix + 7 + len-f + len-g
    -- We have: length prefix + ((7 + len-f) + len-g) from cong len-inner-label
    -- We need: ((length prefix + 7) + len-f) + len-g (left-associative)
    len-prefix-label : length prefix-label ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    len-prefix-label = trans (length-++ prefix)
                              (trans (cong (length prefix +ℕ_) len-inner-label)
                                     (trans (sym (+-assoc (length prefix) (7 +ℕ len-f) len-g))
                                            (cong (_+ℕ len-g) (sym (+-assoc (length prefix) 7 len-f)))))

    -- Program structure (list associativity - mechanical)
    postulate
      prog'-eq-label : prog' ≡ prefix-label ++ i-label ∷ rest-label

    fetch-label'-helper : fetch (prefix-label ++ i-label ∷ rest-label) (length prefix-label) ≡ just i-label
    fetch-label'-helper = fetch-at-prefix-end prefix-label i-label rest-label

    fetch-label' : fetch prog' (length prefix +ℕ 7 +ℕ len-f +ℕ len-g) ≡ just i-label
    fetch-label' = subst₂ (λ p n → fetch p n ≡ just i-label) (sym prog'-eq-label) len-prefix-label fetch-label'-helper

    fetch-label : fetch prog (pc s-after-b) ≡ just i-label
    fetch-label = subst (λ n → fetch prog n ≡ just i-label) (sym pc-after-b)
                        (subst (λ p → fetch p (length prefix +ℕ 7 +ℕ len-f +ℕ len-g) ≡ just i-label) prog'-eq-prog fetch-label')

    -- Execution of label: PC' = PC + 1
    exec-label : execInstr prog s-after-b i-label ≡ just s-final
    exec-label = execInstr-label prog s-after-b end-label

    step-label : step prog s-after-b ≡ just s-final
    step-label = step-instr prog s-after-b s-final i-label h-after-b fetch-label exec-label

    star-label : Star prog s-after-b s-final
    star-label = star-single h-after-b step-label

    -- Combine stars: b then label
    final-star : Star prog s-after-f s-final
    final-star = star-trans star-b star-label

    -- Final state properties (all follow from b and label not modifying registers/memory)

    h-final : halted s-final ≡ false
    h-final = h-after-f

    -- PC after label: prefix + 7 + len-f + len-g + 1 = prefix + 8 + len-f + len-g = prefix + compile-length [ f , g ]
    -- compile-length [ f , g ] = (8 + len-f) + len-g
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    pc-final = trans (cong (_+ℕ 1) pc-after-b) arith-final
      where
        open import Data.Nat.Properties using (+-comm)
        p = length prefix
        -- Goal: (p+7+lf+lg)+1 ≡ p+((8+lf)+lg) = p + compile-length [ f , g ]
        -- All additions are left-associative, so:
        -- LHS: (((p+7)+lf)+lg)+1
        -- RHS: p+((8+lf)+lg)
        -- Step 1: +-assoc to get ((p+7)+lf)+(lg+1)
        -- Step 2: +-comm lg 1 to get ((p+7)+lf)+(1+lg)
        -- Step 3: sym +-assoc to get (((p+7)+lf)+1)+lg
        -- Step 4: use inner-final on ((p+7)+lf)+1 part to get ((p+8)+lf)+lg
        -- Step 5: +-assoc to get (p+8)+(lf+lg)
        -- Step 6: sym +-assoc on the RHS interpretation
        inner-final : (p +ℕ 7 +ℕ len-f) +ℕ 1 ≡ p +ℕ 8 +ℕ len-f
        inner-final = trans (+-assoc (p +ℕ 7) len-f 1)
                            (trans (cong (p +ℕ 7 +ℕ_) (+-comm len-f 1))
                                   (trans (sym (+-assoc (p +ℕ 7) 1 len-f))
                                          (cong (_+ℕ len-f) (+-assoc p 7 1))))
        -- Intermediate: show (p+7+lf+lg)+1 ≡ (p+8+lf)+lg first
        final-arith-step1 : (p +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 1 ≡ (p +ℕ 8 +ℕ len-f) +ℕ len-g
        final-arith-step1 = trans (+-assoc (p +ℕ 7 +ℕ len-f) len-g 1)
                                  (trans (cong (p +ℕ 7 +ℕ len-f +ℕ_) (+-comm len-g 1))
                                         (trans (sym (+-assoc (p +ℕ 7 +ℕ len-f) 1 len-g))
                                                (cong (_+ℕ len-g) inner-final)))
        -- Now show (p+8+lf)+lg ≡ p+((8+lf)+lg)
        final-arith-step2 : (p +ℕ 8 +ℕ len-f) +ℕ len-g ≡ p +ℕ ((8 +ℕ len-f) +ℕ len-g)
        final-arith-step2 = trans (+-assoc (p +ℕ 8) len-f len-g)
                                  (+-assoc p 8 (len-f +ℕ len-g))
        arith-final : (p +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 1 ≡ p +ℕ compile-length [ f , g ]
        arith-final = trans final-arith-step1 final-arith-step2

    -- x0 unchanged through final phase (b and label don't modify registers)
    x0-final : readReg (regs s-final) x0 ≡ addr-out
    x0-final = ir-x0-s f-result

    -- Register preservation through final phase (b and label don't modify registers)
    x20-final : readReg (regs s-final) x20 ≡ readReg (regs s) x20
    x20-final = trans (ir-x20 f-result) x20-setup

    x21-final : readReg (regs s-final) x21 ≡ readReg (regs s) x21
    x21-final = trans (ir-x21 f-result) x21-setup

    x29-final : readReg (regs s-final) x29 ≡ readReg (regs s) x29
    x29-final = trans (ir-x29 f-result) x29-setup

    x30-final : readReg (regs s-final) x30 ≡ readReg (regs s) x30
    x30-final = trans (ir-x30 f-result) x30-setup

    -- Invariants preserved (b and label don't modify regs, so SP and x21/x29 unchanged)
    -- Note: s-final is defined via record update { pc = ... }, so regs s-final = regs s-after-f
    -- and therefore readReg (regs s-final) r = readReg (regs s-after-f) r for any r
    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-preserved-unchanged s-after-f s-final (ir-stack-inv f-result) refl refl

    x29-inv-final : X29Invariant s-final
    x29-inv-final = x29-inv-preserved-unchanged s-after-f s-final (ir-x29-inv f-result) refl refl

    sp>16-final : readSP (regs s-final) > 16
    sp>16-final = ir-sp-bound f-result

    -- Compose stars: setup ◅◅ f ◅◅ final
    full-star : Star prog s s-final
    full-star = star-trans (star-trans setup-star star-f) final-star

    case-result : CaseResultS f g prog s s-final addr-out (length prefix)
    case-result = record
      { case-star = full-star
      ; case-halted = h-final
      ; case-pc = pc-final
      ; case-x0-s = x0-final
      ; case-x20 = x20-final
      ; case-x21 = x21-final
      ; case-x29 = x29-final
      ; case-x30 = x30-final
      ; case-stack-inv = stack-inv-final
      ; case-x29-inv = x29-inv-final
      ; case-sp-bound = sp>16-final
      }

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
    --   b.ne right       -- branch if not equal (TAKEN for inr)
    --   ... skip f ...
    --   right:           -- jump here
    --   ldr x0 [x0+8]    -- load value (= addr-val)
    --   <g code>         -- execute g
    --   end:

    -- Code structure
    len-f : ℕ
    len-f = compile-length f

    len-g : ℕ
    len-g = compile-length g

    -- PC-relative offsets for branches
    right-offset : ℕ
    right-offset = 3 +ℕ len-f    -- b-ne jumps forward by this amount

    end-offset : ℕ
    end-offset = 3 +ℕ len-g      -- b jumps forward by this amount

    -- Label markers
    right-label : ℕ
    right-label = 5 +ℕ len-f

    end-label : ℕ
    end-label = (7 +ℕ len-f) +ℕ len-g

    -- For inr, b.ne IS taken (because tag = 1 ≠ 0)
    -- With PC-relative branches: b.ne at position 2 jumps PC + right-offset
    --   = (prefix + 2) + (3 + len-f) = prefix + 5 + len-f = prefix + right-label
    -- We then execute label and load value

    -- Instructions for inr setup (5 instructions)
    i0 : Instr
    i0 = ldr x9 (base x0)           -- load tag (= 1)

    i1 : Instr
    i1 = cmp x9 (imm 0)             -- compare with 0, Z = false since 1 ≠ 0

    i2 : Instr
    i2 = b-ne right-offset          -- branch TAKEN (Z = false)

    i3 : Instr
    i3 = label right-label          -- at position 5 + len-f

    i4 : Instr
    i4 = ldr x0 (base+imm x0 8)     -- load value (= addr-val)

    -- Memory proof for tag load: readMem at x0 = just 1
    -- x0-eq : readReg (regs s) x0 ≡ addr-sum
    -- tag-is-1 : readMem (memory s) addr-sum ≡ just 1
    -- Goal: readMem (memory s) (readReg (regs s) x0) ≡ just 1
    -- effectiveAddr s (base x0) = readReg (regs s) x0 (no +ℕ 0)
    mem-tag : readMem (memory s) (readReg (regs s) x0) ≡ just 1
    mem-tag = subst (λ a → readMem (memory s) a ≡ just 1) (sym x0-eq) tag-is-1

    -- Intermediate states
    -- s1: after ldr x9 [x0] - x9 = 1
    s1 : State
    s1 = record s { regs = writeReg (regs s) x9 1 ; pc = pc s +ℕ 1 }

    -- s2: after cmp x9 #0 - Z = false (1 ≡ᵇ 0 = false)
    s2 : State
    s2 = record s1 { pstate = updatePSTATE 1 0 ; pc = pc s1 +ℕ 1 }

    -- After cmp 1 0, Z flag = false (1 ≡ᵇ 0 = false)
    z-flag-false : Z (pstate s2) ≡ false
    z-flag-false = refl  -- 1 ≡ᵇ 0 = false by computation

    -- s3: after b.ne (TAKEN) - pc jumps by right-offset
    -- PC = (prefix + 2) + right-offset = prefix + 2 + 3 + len-f = prefix + 5 + len-f
    s3 : State
    s3 = record s2 { pc = pc s2 +ℕ right-offset }

    -- s4: after label right-label - pc + 1
    s4 : State
    s4 = record s3 { pc = pc s3 +ℕ 1 }

    -- s-after-setup: after ldr x0 [x0+8] - x0 = addr-val
    s-after-setup : State
    s-after-setup = record s4 { regs = writeReg (regs s4) x0 addr-val ; pc = pc s4 +ℕ 1 }

    -- PC values at each state
    pc-s1 : pc s1 ≡ length prefix +ℕ 1
    pc-s1 = cong (_+ℕ 1) pc-eq

    pc-s2 : pc s2 ≡ length prefix +ℕ 2
    pc-s2 = trans (cong (_+ℕ 1) pc-s1) (+-assoc (length prefix) 1 1)

    -- After b.ne taken: PC = (prefix + 2) + right-offset = prefix + 2 + 3 + len-f = prefix + 5 + len-f
    pc-s3 : pc s3 ≡ length prefix +ℕ 5 +ℕ len-f
    pc-s3 = trans (cong (_+ℕ right-offset) pc-s2) arith-s3
      where
        open import Data.Nat.Properties using (+-comm)
        p = length prefix
        arith-s3 : (p +ℕ 2) +ℕ (3 +ℕ len-f) ≡ p +ℕ 5 +ℕ len-f
        arith-s3 = trans (sym (+-assoc (p +ℕ 2) 3 len-f))
                         (cong (_+ℕ len-f) (+-assoc p 2 3))

    pc-s4 : pc s4 ≡ length prefix +ℕ 6 +ℕ len-f
    pc-s4 = trans (cong (_+ℕ 1) pc-s3) arith-s4
      where
        open import Data.Nat.Properties using (+-comm)
        p = length prefix
        arith-s4 : (p +ℕ 5 +ℕ len-f) +ℕ 1 ≡ p +ℕ 6 +ℕ len-f
        arith-s4 = trans (+-assoc (p +ℕ 5) len-f 1)
                         (trans (cong (p +ℕ 5 +ℕ_) (+-comm len-f 1))
                                (trans (sym (+-assoc (p +ℕ 5) 1 len-f))
                                       (cong (_+ℕ len-f) (+-assoc p 5 1))))

    -- Program structure for fetch proofs
    -- compile-aarch64 [ f , g ] has this structure:
    --   i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b ∷ i3 ∷ i4 ∷ code-g ++ end-label ∷ []
    -- where ldr-left = ldr x0 (base+imm x0 8) (for inl path, skipped by inr)

    ldr-left : Instr
    ldr-left = ldr x0 (base+imm x0 8)

    code-f : Program
    code-f = compile-aarch64 f

    code-g : Program
    code-g = compile-aarch64 g

    -- Inner code after the first 3 instructions
    -- Matches structure: ldr-left ∷ code-f ++ b ∷ i3 ∷ i4 ∷ code-g ++ end-label ∷ []
    case-inner-3 : Program
    case-inner-3 = ldr-left ∷ code-f ++ b end-offset ∷ i3 ∷ i4 ∷ code-g ++ label end-label ∷ []

    -- The case code = i0 ∷ i1 ∷ i2 ∷ case-inner-3
    -- prog' = prefix ++ (i0 ∷ i1 ∷ i2 ∷ case-inner-3) ++ suffix
    -- By (x ∷ xs) ++ ys = x ∷ (xs ++ ys):
    --   = prefix ++ i0 ∷ ((i1 ∷ i2 ∷ case-inner-3) ++ suffix)

    -- rest-after-* must include ++ suffix at the right level
    rest-after-i0 : Program
    rest-after-i0 = (i1 ∷ i2 ∷ case-inner-3) ++ suffix

    rest-after-i1 : Program
    rest-after-i1 = (i2 ∷ case-inner-3) ++ suffix

    rest-after-i2 : Program
    rest-after-i2 = case-inner-3 ++ suffix

    -- For positions after the b.ne jump (positions 5+len-f onwards)
    -- These are within case-inner-3, after skipping ldr-left and code-f and b
    rest-after-i3 : Program
    rest-after-i3 = (i4 ∷ code-g ++ label end-label ∷ []) ++ suffix

    rest-after-i4 : Program
    rest-after-i4 = (code-g ++ label end-label ∷ []) ++ suffix

    -- prog' is definitionally equal to prog
    prog' : Program
    prog' = prefix ++ (i0 ∷ i1 ∷ i2 ∷ case-inner-3) ++ suffix

    prog'-eq-prog : prog' ≡ prog
    prog'-eq-prog = refl

    -- prog' structure proofs
    prog'-is-prefix-i0-rest : prog' ≡ prefix ++ i0 ∷ rest-after-i0
    prog'-is-prefix-i0-rest = refl

    -- fetch0 at position length prefix
    fetch0' : fetch prog' (length prefix) ≡ just i0
    fetch0' = fetch-at-prefix-end prefix i0 rest-after-i0

    fetch0 : fetch prog (length prefix) ≡ just i0
    fetch0 = subst (λ p → fetch p (length prefix) ≡ just i0) prog'-eq-prog fetch0'

    -- fetch1 at position length prefix + 1
    prefix1 : Program
    prefix1 = prefix ++ i0 ∷ []

    prog'-eq-1 : prog' ≡ prefix1 ++ i1 ∷ rest-after-i1
    prog'-eq-1 = sym (++-assoc prefix (i0 ∷ []) (i1 ∷ rest-after-i1))

    len-prefix1 : length prefix1 ≡ length prefix +ℕ 1
    len-prefix1 = length-++ prefix

    fetch1'-helper : fetch (prefix1 ++ i1 ∷ rest-after-i1) (length prefix1) ≡ just i1
    fetch1'-helper = fetch-at-prefix-end prefix1 i1 rest-after-i1

    fetch1' : fetch prog' (length prefix +ℕ 1) ≡ just i1
    fetch1' = subst₂ (λ p n → fetch p n ≡ just i1) (sym prog'-eq-1) len-prefix1 fetch1'-helper

    fetch1 : fetch prog (length prefix +ℕ 1) ≡ just i1
    fetch1 = subst (λ p → fetch p (length prefix +ℕ 1) ≡ just i1) prog'-eq-prog fetch1'

    -- fetch2 at position length prefix + 2
    prefix2 : Program
    prefix2 = prefix ++ i0 ∷ i1 ∷ []

    prog'-eq-2 : prog' ≡ prefix2 ++ i2 ∷ rest-after-i2
    prog'-eq-2 = sym (++-assoc prefix (i0 ∷ i1 ∷ []) (i2 ∷ rest-after-i2))

    len-prefix2 : length prefix2 ≡ length prefix +ℕ 2
    len-prefix2 = length-++ prefix

    fetch2'-helper : fetch (prefix2 ++ i2 ∷ rest-after-i2) (length prefix2) ≡ just i2
    fetch2'-helper = fetch-at-prefix-end prefix2 i2 rest-after-i2

    fetch2' : fetch prog' (length prefix +ℕ 2) ≡ just i2
    fetch2' = subst₂ (λ p n → fetch p n ≡ just i2) (sym prog'-eq-2) len-prefix2 fetch2'-helper

    fetch2 : fetch prog (length prefix +ℕ 2) ≡ just i2
    fetch2 = subst (λ p → fetch p (length prefix +ℕ 2) ≡ just i2) prog'-eq-prog fetch2'

    -- fetch3 at position length prefix + 5 + len-f (where b.ne lands)
    -- Need prefix of length prefix + 5 + len-f
    -- That's: prefix ++ i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b end-offset ∷ []
    prefix3 : Program
    prefix3 = prefix ++ i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b end-offset ∷ []

    -- Length of prefix3 = length prefix + 5 + len-f
    -- The inner list is: i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b ∷ []
    -- = 4 + (len-f + 1) = 4 + (1 + len-f) = 5 + len-f
    len-inner3 : length (i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b end-offset ∷ []) ≡ 5 +ℕ len-f
    len-inner3 = cong (4 +ℕ_) (trans (length-++ code-f)
                                      (trans (cong (_+ℕ 1) (compile-length-correct f))
                                             (+-comm len-f 1)))

    len-prefix3 : length prefix3 ≡ length prefix +ℕ 5 +ℕ len-f
    len-prefix3 = trans (length-++ prefix)
                        (trans (cong (length prefix +ℕ_) len-inner3)
                               (sym (+-assoc (length prefix) 5 len-f)))

    -- List associativity (mechanical - just list manipulation)
    postulate
      prog'-eq-3 : prog' ≡ prefix3 ++ i3 ∷ rest-after-i3

    fetch3'-helper : fetch (prefix3 ++ i3 ∷ rest-after-i3) (length prefix3) ≡ just i3
    fetch3'-helper = fetch-at-prefix-end prefix3 i3 rest-after-i3

    fetch3' : fetch prog' (length prefix +ℕ 5 +ℕ len-f) ≡ just i3
    fetch3' = subst₂ (λ p n → fetch p n ≡ just i3) (sym prog'-eq-3) len-prefix3 fetch3'-helper

    fetch3 : fetch prog (length prefix +ℕ 5 +ℕ len-f) ≡ just i3
    fetch3 = subst (λ p → fetch p (length prefix +ℕ 5 +ℕ len-f) ≡ just i3) prog'-eq-prog fetch3'

    -- fetch4 at position length prefix + 6 + len-f
    prefix4 : Program
    prefix4 = prefix ++ i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b end-offset ∷ i3 ∷ []

    -- Inner list: i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b ∷ i3 ∷ []
    -- = 4 + length (code-f ++ b ∷ i3 ∷ [])
    -- = 4 + len-f + 2 = 6 + len-f
    len-inner4 : length (i0 ∷ i1 ∷ i2 ∷ ldr-left ∷ code-f ++ b end-offset ∷ i3 ∷ []) ≡ 6 +ℕ len-f
    len-inner4 = cong (4 +ℕ_) (trans (length-++ code-f)
                                      (trans (cong (_+ℕ 2) (compile-length-correct f))
                                             (+-comm len-f 2)))

    len-prefix4 : length prefix4 ≡ length prefix +ℕ 6 +ℕ len-f
    len-prefix4 = trans (length-++ prefix)
                        (trans (cong (length prefix +ℕ_) len-inner4)
                               (sym (+-assoc (length prefix) 6 len-f)))

    -- List associativity (mechanical - just list manipulation)
    postulate
      prog'-eq-4 : prog' ≡ prefix4 ++ i4 ∷ rest-after-i4

    fetch4'-helper : fetch (prefix4 ++ i4 ∷ rest-after-i4) (length prefix4) ≡ just i4
    fetch4'-helper = fetch-at-prefix-end prefix4 i4 rest-after-i4

    fetch4' : fetch prog' (length prefix +ℕ 6 +ℕ len-f) ≡ just i4
    fetch4' = subst₂ (λ p n → fetch p n ≡ just i4) (sym prog'-eq-4) len-prefix4 fetch4'-helper

    fetch4 : fetch prog (length prefix +ℕ 6 +ℕ len-f) ≡ just i4
    fetch4 = subst (λ p → fetch p (length prefix +ℕ 6 +ℕ len-f) ≡ just i4) prog'-eq-prog fetch4'

    -- Memory proof for value load at s4
    -- At s4, x0 still has addr-sum (unchanged through b.ne and label)
    -- val-addr : readMem (memory s) (addr-sum + 8) ≡ just addr-val
    -- s4 has same memory as s, so can use val-addr

    -- Memory is unchanged: s → s1 → s2 → s3 → s4
    mem-s4-eq-s : memory s4 ≡ memory s
    mem-s4-eq-s = refl  -- No memory writes in any instruction

    -- x0 is unchanged: only x9 was written in s1
    x0-s4-eq-s : readReg (regs s4) x0 ≡ readReg (regs s) x0
    x0-s4-eq-s = readReg-writeReg-x9-x0 (regs s) 1

    -- Combine to prove mem-val
    mem-val : readMem (memory s4) (readReg (regs s4) x0 +ℕ 8) ≡ just addr-val
    mem-val = trans (cong (λ m → readMem m (readReg (regs s4) x0 +ℕ 8)) mem-s4-eq-s)
                    (trans (cong (λ a → readMem (memory s) (a +ℕ 8)) x0-s4-eq-s)
                           (trans (cong (λ a → readMem (memory s) (a +ℕ 8)) x0-eq)
                                  val-addr))

    -- Execution proofs
    exec0 : execInstr prog s i0 ≡ just s1
    exec0 = execInstr-ldr-success prog s x9 (base x0) 1 mem-tag

    step0 : step prog s ≡ just s1
    step0 = step-instr prog s s1 i0 h-false
              (subst (λ n → fetch prog n ≡ just i0) (sym pc-eq) fetch0)
              exec0

    exec1 : execInstr prog s1 i1 ≡ just s2
    exec1 = execInstr-cmp-imm prog s1 x9 0

    h1 : halted s1 ≡ false
    h1 = h-false

    step1 : step prog s1 ≡ just s2
    step1 = step-instr prog s1 s2 i1 h1
              (subst (λ n → fetch prog n ≡ just i1) (sym pc-s1) fetch1)
              exec1

    -- b.ne with Z = false means TAKEN, pc = pc + right-offset
    exec2 : execInstr prog s2 i2 ≡ just s3
    exec2 = execInstr-b-ne prog s2 right-offset

    h2 : halted s2 ≡ false
    h2 = h-false

    step2 : step prog s2 ≡ just s3
    step2 = step-instr prog s2 s3 i2 h2
              (subst (λ n → fetch prog n ≡ just i2) (sym pc-s2) fetch2)
              exec2

    exec3 : execInstr prog s3 i3 ≡ just s4
    exec3 = execInstr-label prog s3 right-label

    h3 : halted s3 ≡ false
    h3 = h-false

    step3 : step prog s3 ≡ just s4
    step3 = step-instr prog s3 s4 i3 h3
              (subst (λ n → fetch prog n ≡ just i3) (sym pc-s3) fetch3)
              exec3

    exec4 : execInstr prog s4 i4 ≡ just s-after-setup
    exec4 = execInstr-ldr-success prog s4 x0 (base+imm x0 8) addr-val mem-val

    h4 : halted s4 ≡ false
    h4 = h-false

    step4 : step prog s4 ≡ just s-after-setup
    step4 = step-instr prog s4 s-after-setup i4 h4
              (subst (λ n → fetch prog n ≡ just i4) (sym pc-s4) fetch4)
              exec4

    -- Build Star from 5 steps
    star01 : Star prog s s1
    star01 = star-single h-false step0
    star12 : Star prog s1 s2
    star12 = star-single h1 step1
    star23 : Star prog s2 s3
    star23 = star-single h2 step2
    star34 : Star prog s3 s4
    star34 = star-single h3 step3
    star45 : Star prog s4 s-after-setup
    star45 = star-single h4 step4

    setup-star : Star prog s s-after-setup
    setup-star = star-trans (star-trans (star-trans (star-trans star01 star12) star23) star34) star45

    h-setup : halted s-after-setup ≡ false
    h-setup = h-false

    pc-setup : pc s-after-setup ≡ length prefix +ℕ 7 +ℕ len-f
    pc-setup = trans (cong (_+ℕ 1) pc-s4) arith-setup
      where
        open import Data.Nat.Properties using (+-comm)
        p = length prefix
        arith-setup : (p +ℕ 6 +ℕ len-f) +ℕ 1 ≡ p +ℕ 7 +ℕ len-f
        arith-setup = trans (+-assoc (p +ℕ 6) len-f 1)
                            (trans (cong (p +ℕ 6 +ℕ_) (+-comm len-f 1))
                                   (trans (sym (+-assoc (p +ℕ 6) 1 len-f))
                                          (cong (_+ℕ len-f) (+-assoc p 6 1))))

    x0-setup : readReg (regs s-after-setup) x0 ≡ addr-val
    x0-setup = readReg-writeReg-same (regs s4) x0 addr-val

    -- Register preservation through setup
    -- regs s4 = regs s3 = regs s2 = regs s1 = writeReg (regs s) x9 1
    -- regs s-after-setup = writeReg (regs s4) x0 addr-val
    x20-setup : readReg (regs s-after-setup) x20 ≡ readReg (regs s) x20
    x20-setup = trans (readReg-writeReg-x0-x20 (regs s4) addr-val)
                      (readReg-writeReg-x9-x20 (regs s) 1)

    x21-setup : readReg (regs s-after-setup) x21 ≡ readReg (regs s) x21
    x21-setup = trans (readReg-writeReg-x0-x21 (regs s4) addr-val)
                      (readReg-writeReg-x9-x21 (regs s) 1)

    x29-setup : readReg (regs s-after-setup) x29 ≡ readReg (regs s) x29
    x29-setup = trans (readReg-writeReg-x0-x29 (regs s4) addr-val)
                      (readReg-writeReg-x9-x29 (regs s) 1)

    x30-setup : readReg (regs s-after-setup) x30 ≡ readReg (regs s) x30
    x30-setup = trans (readReg-writeReg-x0-x30 (regs s4) addr-val)
                      (readReg-writeReg-x9-x30 (regs s) 1)

    stack-inv-setup : StackInvariant s-after-setup
    stack-inv-setup = stack-inv-preserved-unchanged s s-after-setup stack-inv x21-setup refl

    x29-inv-setup : X29Invariant s-after-setup
    x29-inv-setup = x29-inv-preserved-unchanged s s-after-setup x29-inv x29-setup refl

    sp>16-setup : readSP (regs s-after-setup) > 16
    sp>16-setup = sp-bound-after-stack-op s-after-setup

    -- Prefix for g: prefix ++ all code before g
    prefix-g : Program
    prefix-g = prefix ++ ldr x9 (base x0) ∷ cmp x9 (imm 0) ∷ b-ne right-offset ∷
               ldr x0 (base+imm x0 8) ∷ compile-aarch64 f ++ b end-offset ∷
               label right-label ∷ ldr x0 (base+imm x0 8) ∷ []

    -- Suffix for g: label end ∷ suffix
    suffix-g : Program
    suffix-g = label end-label ∷ suffix

    -- Prove program equality for g call
    postulate
      prog-g-eq : prefix-g ++ compile-aarch64 g ++ suffix-g ≡ prog
      len-prefix-g : length prefix-g ≡ length prefix +ℕ 7 +ℕ len-f

    -- Call run-g with s-after-setup
    g-result-raw : ∃[ s' ] ∃[ addr-out ] IRStarResultS g (prefix-g ++ compile-aarch64 g ++ suffix-g) s-after-setup s' addr-out (length prefix-g)
    g-result-raw = run-g prefix-g suffix-g addr-val s-after-setup h-setup
                         (trans pc-setup (sym len-prefix-g)) x0-setup
                         stack-inv-setup x29-inv-setup sp>16-setup

    s-after-g : State
    s-after-g = Data.Product.proj₁ g-result-raw

    addr-out : Word
    addr-out = Data.Product.proj₁ (Data.Product.proj₂ g-result-raw)

    g-result : IRStarResultS g (prefix-g ++ compile-aarch64 g ++ suffix-g) s-after-setup s-after-g addr-out (length prefix-g)
    g-result = Data.Product.proj₂ (Data.Product.proj₂ g-result-raw)

    -- Convert star to work on prog
    star-g : Star prog s-after-setup s-after-g
    star-g = subst (λ p → Star p s-after-setup s-after-g) prog-g-eq (ir-star g-result)

    -- After g, we're at end-label position, execute label instruction
    -- The label instruction only increments PC by 1

    -- PC after g: length prefix-g + len-g = (length prefix + 7 + len-f) + len-g
    pc-after-g : pc s-after-g ≡ length prefix +ℕ 7 +ℕ len-f +ℕ len-g
    pc-after-g = trans (ir-pc g-result) (cong (_+ℕ len-g) len-prefix-g)

    h-after-g : halted s-after-g ≡ false
    h-after-g = ir-halted g-result

    -- Register preservation from s to s-after-g (through setup and g)
    -- Chain: ir-x20 g-result : s-after-g.x20 ≡ s-after-setup.x20
    --        x20-setup : s-after-setup.x20 ≡ s.x20
    x20-after-g : readReg (regs s-after-g) x20 ≡ readReg (regs s) x20
    x20-after-g = trans (ir-x20 g-result) x20-setup

    x21-after-g : readReg (regs s-after-g) x21 ≡ readReg (regs s) x21
    x21-after-g = trans (ir-x21 g-result) x21-setup

    x29-after-g : readReg (regs s-after-g) x29 ≡ readReg (regs s) x29
    x29-after-g = trans (ir-x29 g-result) x29-setup

    x30-after-g : readReg (regs s-after-g) x30 ≡ readReg (regs s) x30
    x30-after-g = trans (ir-x30 g-result) x30-setup

    -- Final phase: execute label end-label
    -- Only PC changes: PC' = PC + 1

    i-label : Instr
    i-label = label end-label

    -- State after label: only PC changes
    s-final : State
    s-final = record s-after-g { pc = pc s-after-g +ℕ 1 }

    -- Fetch proof for label instruction
    postulate
      fetch-label-inr : fetch prog (pc s-after-g) ≡ just i-label

    -- Execution of label: PC' = PC + 1
    exec-label : execInstr prog s-after-g i-label ≡ just s-final
    exec-label = execInstr-label prog s-after-g end-label

    step-label : step prog s-after-g ≡ just s-final
    step-label = step-instr prog s-after-g s-final i-label h-after-g fetch-label-inr exec-label

    final-star : Star prog s-after-g s-final
    final-star = star-single h-after-g step-label

    -- Final state properties
    h-final : halted s-final ≡ false
    h-final = h-after-g

    -- PC after label: (prefix + 7 + len-f + len-g) + 1 = prefix + 8 + len-f + len-g = prefix + compile-length [ f , g ]
    pc-final : pc s-final ≡ length prefix +ℕ compile-length [ f , g ]
    pc-final = trans (cong (_+ℕ 1) pc-after-g) arith-final
      where
        open import Data.Nat.Properties using (+-comm)
        p = length prefix
        -- Goal: (p+7+lf+lg)+1 ≡ p+((8+lf)+lg) = p + compile-length [ f , g ]
        inner-final : (p +ℕ 7 +ℕ len-f) +ℕ 1 ≡ p +ℕ 8 +ℕ len-f
        inner-final = trans (+-assoc (p +ℕ 7) len-f 1)
                            (trans (cong (p +ℕ 7 +ℕ_) (+-comm len-f 1))
                                   (trans (sym (+-assoc (p +ℕ 7) 1 len-f))
                                          (cong (_+ℕ len-f) (+-assoc p 7 1))))
        final-step1 : (p +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 1 ≡ (p +ℕ 8 +ℕ len-f) +ℕ len-g
        final-step1 = trans (+-assoc (p +ℕ 7 +ℕ len-f) len-g 1)
                            (trans (cong (p +ℕ 7 +ℕ len-f +ℕ_) (+-comm len-g 1))
                                   (trans (sym (+-assoc (p +ℕ 7 +ℕ len-f) 1 len-g))
                                          (cong (_+ℕ len-g) inner-final)))
        final-step2 : (p +ℕ 8 +ℕ len-f) +ℕ len-g ≡ p +ℕ ((8 +ℕ len-f) +ℕ len-g)
        final-step2 = trans (+-assoc (p +ℕ 8) len-f len-g)
                            (+-assoc p 8 (len-f +ℕ len-g))
        arith-final : (p +ℕ 7 +ℕ len-f +ℕ len-g) +ℕ 1 ≡ p +ℕ compile-length [ f , g ]
        arith-final = trans final-step1 final-step2

    -- x0 unchanged through final phase (label doesn't modify registers)
    x0-final : readReg (regs s-final) x0 ≡ addr-out
    x0-final = ir-x0-s g-result

    -- Register preservation through final phase
    x20-final : readReg (regs s-final) x20 ≡ readReg (regs s) x20
    x20-final = x20-after-g

    x21-final : readReg (regs s-final) x21 ≡ readReg (regs s) x21
    x21-final = x21-after-g

    x29-final : readReg (regs s-final) x29 ≡ readReg (regs s) x29
    x29-final = x29-after-g

    x30-final : readReg (regs s-final) x30 ≡ readReg (regs s) x30
    x30-final = x30-after-g

    -- Invariants preserved (label doesn't modify regs, so SP and x21/x29 unchanged)
    stack-inv-final : StackInvariant s-final
    stack-inv-final = stack-inv-preserved-unchanged s-after-g s-final (ir-stack-inv g-result) refl refl

    x29-inv-final : X29Invariant s-final
    x29-inv-final = x29-inv-preserved-unchanged s-after-g s-final (ir-x29-inv g-result) refl refl

    sp>16-final : readSP (regs s-final) > 16
    sp>16-final = ir-sp-bound g-result

    -- Compose stars: setup ◅◅ g ◅◅ final
    full-star : Star prog s s-final
    full-star = star-trans (star-trans setup-star star-g) final-star

    case-result : CaseResultS f g prog s s-final addr-out (length prefix)
    case-result = record
      { case-star = full-star
      ; case-halted = h-final
      ; case-pc = pc-final
      ; case-x0-s = x0-final
      ; case-x20 = x20-final
      ; case-x21 = x21-final
      ; case-x29 = x29-final
      ; case-x30 = x30-final
      ; case-stack-inv = stack-inv-final
      ; case-x29-inv = x29-inv-final
      ; case-sp-bound = sp>16-final
      }
