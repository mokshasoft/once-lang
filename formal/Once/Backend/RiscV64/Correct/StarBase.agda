------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.StarBase
--
-- Star-based proofs for non-recursive IR operations (base cases).
-- These are the simple cases that don't require mutual recursion:
-- id, terminal, fold, unfold, arr, fst, snd.
--
-- Key data types defined here:
--   - IRStarResult: Result of executing IR with Star semantics
--   - IRRunner: Type signature for the recursive IR executor (sized)
--
-- Adapted from x86-64 backend, simplified for RISC-V:
--   - a0 is both input AND output (no rdi/rax distinction)
--   - Only s1 needs to be preserved (simpler than x86's r14/r15/rbp)
--
-- Uses sized types to enable modular termination proofs.
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

module Once.Backend.RiscV64.Correct.StarBase where

open import Size
open import Once.Type
open import Once.IRS
open import Once.SemanticsS

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Backend.RiscV64.Correct.Star
open import Once.Backend.RiscV64.Correct.Foundation
open import Once.Backend.RiscV64.Correct.MemoryValid using (PairAt; fst-valid; snd-valid)
open import Once.Backend.RiscV64.Correct.ClosureWellFormed
  using (ClosuresWF; trivialWF; pairWF; fstWF; sndWF; applyInputWF; ApplyInputWF)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; ≤-refl)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- IRStarResult: Result of executing IR at an offset
--
-- This record captures all properties we need after executing IR code:
--   - Star execution proof (fuel-independent)
--   - Program counter advances correctly
--   - Output register (a0) contains encoded result
--   - Preserved register (s1) unchanged
--
-- RISC-V simplification: a0 is BOTH input and output!
------------------------------------------------------------------------

record IRStarResult {i : Size} {A B : Type} (ir : IR i A B) (prog : Program) (s s' : State)
                    (x : ⟦ A ⟧) (offset : ℕ) : Set where
  field
    ir-star    : Star prog s s'                           -- Execution reaches s'
    ir-halted  : halted s' ≡ false                        -- Not halted (can continue)
    ir-pc      : pc s' ≡ offset +ℕ compile-length ir      -- PC advanced correctly
    ir-a0      : readReg (regs s') a0 ≡ encode (eval ir x) -- Output in a0
    ir-s1      : readReg (regs s') s1 ≡ readReg (regs s) s1  -- s1 preserved
    ir-s2      : readReg (regs s') s2 ≡ readReg (regs s) s2  -- s2 preserved (for pair frame pointer)
    ir-ra      : readReg (regs s') ra ≡ readReg (regs s) ra  -- ra preserved
    -- SP tracking: Most ops preserve sp (delta=0), but inl/inr/pair allocate stack.
    -- ir-sp-delta tracks how many bytes were allocated (0, 16, or 24).
    -- ir-sp proves: sp' + delta = orig-sp (i.e., sp decreased by delta).
    -- ir-sp-delta-leq proves delta is bounded by static StackDelta computation.
    -- Note: For case, only one branch runs, so runtime delta ≤ max(delta_f, delta_g).
    ir-sp-delta : ℕ  -- Stack bytes allocated (0 for most, 16 for inl/inr, 24 for pair)
    ir-sp-delta-leq : ir-sp-delta ≤ StackDelta ir  -- Bounded by static computation
    ir-sp      : readReg (regs s') sp +ℕ ir-sp-delta ≡ readReg (regs s) sp
    -- Memory preservation at caller's frame (universally quantified)
    -- For ANY offset n from original sp, memory is preserved.
    -- This handles arbitrarily deep nesting (pair, case, etc.)
    ir-mem-preserved : ∀ n → readMem (memory s') (readReg (regs s) sp +ℕ n) ≡ readMem (memory s) (readReg (regs s) sp +ℕ n)
    -- WF for closures in the output value
    -- This is trivial for most IR nodes, but meaningful for curry.
    -- Threading this through compose allows apply to use proven WF.
    ir-output-wf : ClosuresWF B prog

open IRStarResult public

------------------------------------------------------------------------
-- IRRunner: Type signature for recursive IR executor (sized)
--
-- This type allows us to pass the recursive function as a parameter
-- to helper functions, enabling extraction from the mutual block.
--
-- The Size parameter enables termination checking across modules:
-- - IRRunner i can only be called on IR j A B where j < i
-- - This is enforced via Size< constraints in helper functions
------------------------------------------------------------------------

IRRunner : Size → Set
IRRunner i = ∀ {j : Size< i} {A B} (ir : IR j A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
             halted s ≡ false →
             pc s ≡ length prefix →
             readReg (regs s) a0 ≡ encode x →
             ∃[ s' ] IRStarResult ir (prefix ++ compile-riscv ir ++ suffix) s s' x (length prefix)

------------------------------------------------------------------------
-- Base case: id (nop)
--
-- compile-riscv id = nop ∷ []
-- compile-length id = 1
--
-- a0 unchanged, eval id x = x
------------------------------------------------------------------------

run-id-star : ∀ {i A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (id {i} {A}) (prefix ++ compile-riscv (id {i} {A}) ++ suffix) s s' x (length prefix)
run-id-star {i} {A} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = a0-eq  -- a0 unchanged, eval id x = x
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl  -- no memory write
  ; ir-output-wf = trivialWF A prog
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

------------------------------------------------------------------------
-- Base case: terminal (li a0, 0)
--
-- compile-riscv terminal = li a0 0 ∷ []
-- compile-length terminal = 1
--
-- a0 = 0 = encode tt (by encode-unit)
------------------------------------------------------------------------

run-terminal-star : ∀ {i A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (terminal {i} {A}) (prefix ++ compile-riscv (terminal {i} {A}) ++ suffix) s s' x (length prefix)
run-terminal-star {i} {A} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans (readReg-writeReg-same (regs s) a0 0 (λ ())) (sym encode-unit)
  ; ir-s1     = refl
  ; ir-s2     = readReg-writeReg-a0-s2 (regs s) 0
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = trans (+-identityʳ _) (readReg-writeReg-a0-sp (regs s) 0)
  ; ir-mem-preserved = λ n → refl  -- no memory write
  ; ir-output-wf = tt  -- Unit has no closures
  }
  where
    prog = prefix ++ li a0 (+ 0) ∷ suffix
    s' = record s { regs = writeReg (regs s) a0 0 ; pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix (li a0 (+ 0)) suffix s h-false pc-eq)
                    (execLi prog s a0 0)

------------------------------------------------------------------------
-- Base case: fold (nop - identity at runtime)
--
-- compile-riscv fold = nop ∷ []
-- compile-length fold = 1
--
-- a0 unchanged, encode x ≡ encode (wrap x) by encode-fix-wrap
------------------------------------------------------------------------

run-fold-star : ∀ {i F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (fold {i} {F}) (prefix ++ compile-riscv (fold {i} {F}) ++ suffix) s s' x (length prefix)
run-fold-star {i} {F} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans a0-eq (encode-fix-wrap x)
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl  -- no memory write
  ; ir-output-wf = tt  -- Fix F has no closures (by definition of ClosuresWF)
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

------------------------------------------------------------------------
-- Base case: unfold (nop - identity at runtime)
--
-- compile-riscv unfold = nop ∷ []
-- compile-length unfold = 1
--
-- a0 unchanged, encode x ≡ encode (unwrap x) by encode-fix-unwrap
------------------------------------------------------------------------

run-unfold-star : ∀ {i F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (unfold {i} {F}) (prefix ++ compile-riscv (unfold {i} {F}) ++ suffix) s s' x (length prefix)
run-unfold-star {i} {F} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans a0-eq (encode-fix-unwrap x)
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl  -- no memory write
  ; ir-output-wf = trivialWF F prog  -- F is the output type
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

------------------------------------------------------------------------
-- Base case: arr (nop - identity at runtime)
--
-- compile-riscv arr = nop ∷ []
-- compile-length arr = 1
--
-- a0 unchanged, encode {A ⇒ B} f ≡ encode {Eff A B} f by encode-arr-identity
------------------------------------------------------------------------

run-arr-star : ∀ {i A B} (prefix suffix : Program) (f : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode {A ⇒ B} f →
  ∃[ s' ] IRStarResult (arr {i} {A} {B}) (prefix ++ compile-riscv (arr {i} {A} {B}) ++ suffix) s s' f (length prefix)
run-arr-star {i} {A} {B} prefix suffix f s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans a0-eq (encode-arr-identity f)  -- encode {A ⇒ B} f ≡ encode {Eff A B} f
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl  -- no memory write
  ; ir-output-wf = tt  -- Eff A B has no closures (by definition of ClosuresWF)
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

------------------------------------------------------------------------
-- Validity-based versions: use PairAt instead of encoding postulates
--
-- These versions take a PairAt validity proof as a precondition,
-- eliminating the need for encode-pair-fst/snd postulates.
-- Use these when you have a validity proof from allocation.
------------------------------------------------------------------------

-- | Validity-based fst (uses PairAt instead of encode-pair-fst postulate)
run-fst-star-v : ∀ {i A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode (a , b) →
  PairAt a b (encode (a , b)) (memory s) →
  ∃[ s' ] IRStarResult (fst {i} {A} {B}) (prefix ++ compile-riscv (fst {i} {A} {B}) ++ suffix) s s' (a , b) (length prefix)
run-fst-star-v {i} {A} {B} prefix suffix a b s h-false pc-eq a0-eq pair-valid = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = readReg-writeReg-same (regs s) a0 (encode a) (λ ())
  ; ir-s1     = readReg-writeReg-a0-s1 (regs s) (encode a)
  ; ir-s2     = readReg-writeReg-a0-s2 (regs s) (encode a)
  ; ir-ra     = readReg-writeReg-a0-ra (regs s) (encode a)
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = trans (+-identityʳ _) (readReg-writeReg-a0-sp (regs s) (encode a))
  ; ir-mem-preserved = λ n → refl
  ; ir-output-wf = trivialWF A prog
  }
  where
    prog = prefix ++ ld a0 (+ 0) a0 ∷ suffix

    -- Memory precondition from validity proof (no postulate!)
    mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
    mem-eq = fst-valid pair-valid

    eff-addr : effectiveAddr (regs s) a0 (+ 0) ≡ encode (a , b)
    eff-addr = trans (cong (readReg (regs s) a0 +ℕ_) refl)
                     (trans (+-identityʳ (readReg (regs s) a0)) a0-eq)

    mem-read : readMem (memory s) (effectiveAddr (regs s) a0 (+ 0)) ≡ just (encode a)
    mem-read = trans (cong (λ addr → readMem (memory s) addr) eff-addr) mem-eq

    s' = record s { regs = writeReg (regs s) a0 (encode a) ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (ld a0 (+ 0) a0)
    fetch-eq = subst (λ p → fetch prog p ≡ just (ld a0 (+ 0) a0))
                     (sym pc-eq) (fetch-at-prefix-end prefix (ld a0 (+ 0) a0) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (ld a0 (+ 0) a0) h-false fetch-eq)
                    (execInstr-ld-success prog s a0 a0 (+ 0) (encode a) mem-read)

-- | Validity-based snd (uses PairAt instead of encode-pair-snd postulate)
run-snd-star-v : ∀ {i A B} (prefix suffix : Program) (a : ⟦ A ⟧) (b : ⟦ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode (a , b) →
  PairAt a b (encode (a , b)) (memory s) →
  ∃[ s' ] IRStarResult (snd {i} {A} {B}) (prefix ++ compile-riscv (snd {i} {A} {B}) ++ suffix) s s' (a , b) (length prefix)
run-snd-star-v {i} {A} {B} prefix suffix a b s h-false pc-eq a0-eq pair-valid = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = readReg-writeReg-same (regs s) a0 (encode b) (λ ())
  ; ir-s1     = readReg-writeReg-a0-s1 (regs s) (encode b)
  ; ir-s2     = readReg-writeReg-a0-s2 (regs s) (encode b)
  ; ir-ra     = readReg-writeReg-a0-ra (regs s) (encode b)
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = trans (+-identityʳ _) (readReg-writeReg-a0-sp (regs s) (encode b))
  ; ir-mem-preserved = λ n → refl
  ; ir-output-wf = trivialWF B prog
  }
  where
    prog = prefix ++ ld a0 (+ 8) a0 ∷ suffix

    -- Memory precondition from validity proof (no postulate!)
    mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
    mem-eq = snd-valid pair-valid

    eff-addr : effectiveAddr (regs s) a0 (+ 8) ≡ encode (a , b) +ℕ 8
    eff-addr = cong (_+ℕ 8) a0-eq

    mem-read : readMem (memory s) (effectiveAddr (regs s) a0 (+ 8)) ≡ just (encode b)
    mem-read = trans (cong (λ addr → readMem (memory s) addr) eff-addr) mem-eq

    s' = record s { regs = writeReg (regs s) a0 (encode b) ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (ld a0 (+ 8) a0)
    fetch-eq = subst (λ p → fetch prog p ≡ just (ld a0 (+ 8) a0))
                     (sym pc-eq) (fetch-at-prefix-end prefix (ld a0 (+ 8) a0) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (ld a0 (+ 8) a0) h-false fetch-eq)
                    (execInstr-ld-success prog s a0 a0 (+ 8) (encode b) mem-read)

------------------------------------------------------------------------
-- IRStarResultS: Stateful result type with explicit output address
--
-- This is the key to eliminating encoding postulates:
-- - Instead of ir-a0 : readReg a0 ≡ encode (eval ir x)
-- - We have ir-a0-s : readReg a0 ≡ addr-out
-- - The addr-out is the explicit memory address where the result is stored
--
-- This enables proofs using memory allocation lemmas instead of axioms.
------------------------------------------------------------------------

record IRStarResultS {i : Size} {A B : Type} (ir : IR i A B) (prog : Program)
                     (s s' : State) (addr-out : Word) (offset : ℕ) : Set where
  field
    ir-star       : Star prog s s'
    ir-halted     : halted s' ≡ false
    ir-pc         : pc s' ≡ offset +ℕ compile-length ir
    ir-a0-s       : readReg (regs s') a0 ≡ addr-out  -- Address, not encode!
    ir-s1         : readReg (regs s') s1 ≡ readReg (regs s) s1
    ir-s2         : readReg (regs s') s2 ≡ readReg (regs s) s2
    ir-ra         : readReg (regs s') ra ≡ readReg (regs s) ra
    ir-sp-delta   : ℕ
    ir-sp-delta-leq : ir-sp-delta ≤ StackDelta ir
    ir-sp         : readReg (regs s') sp +ℕ ir-sp-delta ≡ readReg (regs s) sp
    ir-mem-preserved : ∀ n → readMem (memory s') (readReg (regs s) sp +ℕ n) ≡
                             readMem (memory s) (readReg (regs s) sp +ℕ n)
    ir-output-wf  : ClosuresWF B prog

------------------------------------------------------------------------
-- Conversion bridge: IRStarResult → IRStarResultS
--
-- This allows gradual migration: we can convert existing proofs to
-- stateful form using encode (eval ir x) as the address.
------------------------------------------------------------------------

convert-to-stateful : ∀ {i} {A B} (ir : IR i A B) (prog : Program) (s s' : State)
                      (x : ⟦ A ⟧) (offset : ℕ) →
  IRStarResult ir prog s s' x offset →
  IRStarResultS ir prog s s' (encode (eval ir x)) offset
convert-to-stateful ir prog s s' x offset res = record
  { ir-star       = IRStarResult.ir-star res
  ; ir-halted     = IRStarResult.ir-halted res
  ; ir-pc         = IRStarResult.ir-pc res
  ; ir-a0-s       = IRStarResult.ir-a0 res  -- encode (eval ir x)
  ; ir-s1         = IRStarResult.ir-s1 res
  ; ir-s2         = IRStarResult.ir-s2 res
  ; ir-ra         = IRStarResult.ir-ra res
  ; ir-sp-delta   = IRStarResult.ir-sp-delta res
  ; ir-sp-delta-leq = IRStarResult.ir-sp-delta-leq res
  ; ir-sp         = IRStarResult.ir-sp res
  ; ir-mem-preserved = IRStarResult.ir-mem-preserved res
  ; ir-output-wf  = IRStarResult.ir-output-wf res
  }

------------------------------------------------------------------------
-- Stateful wrappers for base cases
--
-- These are direct stateful versions that don't go through IRStarResult.
-- The key insight: for simple cases, addr-in = addr-out.
------------------------------------------------------------------------

-- Base case: id (stateful)
-- Input address = output address (no transformation)
run-id-star-s : ∀ {i A} (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  ∃[ s' ] IRStarResultS (id {i} {A}) (prefix ++ compile-riscv (id {i} {A}) ++ suffix) s s' addr-in (length prefix)
run-id-star-s {i} {A} prefix suffix addr-in s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0-s   = a0-eq  -- a0 unchanged
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl
  ; ir-output-wf = trivialWF A prog
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

-- Base case: terminal (stateful)
-- Output address = 0 (unit encoding)
run-terminal-star-s : ∀ {i A} (prefix suffix : Program) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ∃[ s' ] IRStarResultS (terminal {i} {A}) (prefix ++ compile-riscv (terminal {i} {A}) ++ suffix) s s' 0 (length prefix)
run-terminal-star-s {i} {A} prefix suffix s h-false pc-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0-s   = readReg-writeReg-same (regs s) a0 0 (λ ())
  ; ir-s1     = refl
  ; ir-s2     = readReg-writeReg-a0-s2 (regs s) 0
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = trans (+-identityʳ _) (readReg-writeReg-a0-sp (regs s) 0)
  ; ir-mem-preserved = λ n → refl
  ; ir-output-wf = tt
  }
  where
    prog = prefix ++ li a0 (+ 0) ∷ suffix
    s' = record s { regs = writeReg (regs s) a0 0 ; pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix (li a0 (+ 0)) suffix s h-false pc-eq)
                    (execLi prog s a0 0)

-- Base case: fold (stateful)
-- Input address = output address (runtime nop)
run-fold-star-s : ∀ {i F} (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  ∃[ s' ] IRStarResultS (fold {i} {F}) (prefix ++ compile-riscv (fold {i} {F}) ++ suffix) s s' addr-in (length prefix)
run-fold-star-s {i} {F} prefix suffix addr-in s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0-s   = a0-eq  -- a0 unchanged
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl
  ; ir-output-wf = tt
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

-- Base case: unfold (stateful)
-- Input address = output address (runtime nop)
run-unfold-star-s : ∀ {i F} (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  ∃[ s' ] IRStarResultS (unfold {i} {F}) (prefix ++ compile-riscv (unfold {i} {F}) ++ suffix) s s' addr-in (length prefix)
run-unfold-star-s {i} {F} prefix suffix addr-in s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0-s   = a0-eq  -- a0 unchanged
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl
  ; ir-output-wf = trivialWF F prog
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

-- Base case: arr (stateful)
-- Input address = output address (runtime nop)
run-arr-star-s : ∀ {i A B} (prefix suffix : Program) (addr-in : Word) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ addr-in →
  ∃[ s' ] IRStarResultS (arr {i} {A} {B}) (prefix ++ compile-riscv (arr {i} {A} {B}) ++ suffix) s s' addr-in (length prefix)
run-arr-star-s {i} {A} {B} prefix suffix addr-in s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0-s   = a0-eq  -- a0 unchanged
  ; ir-s1     = refl
  ; ir-s2     = refl
  ; ir-ra     = refl
  ; ir-sp-delta = 0
  ; ir-sp-delta-leq = ≤-refl
  ; ir-sp     = +-identityʳ _
  ; ir-mem-preserved = λ n → refl
  ; ir-output-wf = tt
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

------------------------------------------------------------------------
-- Notes on Composing IRStarResults
--
-- Key benefit of Star: composition is trivial (just transitivity)!
-- No fuel arithmetic needed.
--
-- Composition is handled in MutualIR.agda where the recursive calls
-- happen. The pattern is:
--   1. Get result1 : IRStarResult ir1 for first IR
--   2. Get result2 : IRStarResult ir2 for second IR (starting from result1's state)
--   3. Combine using star-trans
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Export everything for use in MutualIR and other modules
------------------------------------------------------------------------

-- Re-export Star infrastructure (fuel-free: no exec-to-star, star-to-exec, etc.)
open import Once.Backend.RiscV64.Correct.Star public
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_; _◅◅_;
         star-step2; star-step3; star-step4; star-step5)
