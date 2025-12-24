------------------------------------------------------------------------
-- Once.Backend.RiscV64.Correct.StarBase
--
-- Star-based proofs for non-recursive IR operations (base cases).
-- These are the simple cases that don't require mutual recursion:
-- id, terminal, fold, unfold, arr, fst, snd.
--
-- Key data types defined here:
--   - IRStarResult: Result of executing IR with Star semantics
--   - IRRunner: Type signature for the recursive IR executor
--
-- Adapted from x86-64 backend, simplified for RISC-V:
--   - a0 is both input AND output (no rdi/rax distinction)
--   - Only s1 needs to be preserved (simpler than x86's r14/r15/rbp)
------------------------------------------------------------------------

module Once.Backend.RiscV64.Correct.StarBase where

open import Once.Type
open import Once.IR
open import Once.Semantics

open import Once.Backend.RiscV64.Syntax
open import Once.Backend.RiscV64.Semantics
open State
open import Once.Backend.RiscV64.CodeGen

open import Once.Backend.RiscV64.Correct.Star
open import Once.Backend.RiscV64.Correct.Foundation

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm)
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

record IRStarResult {A B : Type} (ir : IR A B) (prog : Program) (s s' : State)
                    (x : ⟦ A ⟧) (offset : ℕ) : Set where
  field
    ir-star    : Star prog s s'                           -- Execution reaches s'
    ir-halted  : halted s' ≡ false                        -- Not halted (can continue)
    ir-pc      : pc s' ≡ offset +ℕ compile-length ir      -- PC advanced correctly
    ir-a0      : readReg (regs s') a0 ≡ encode (eval ir x) -- Output in a0
    ir-s1      : readReg (regs s') s1 ≡ readReg (regs s) s1  -- s1 preserved
    ir-ra      : readReg (regs s') ra ≡ readReg (regs s) ra  -- ra preserved
    ir-sp      : readReg (regs s') sp ≡ readReg (regs s) sp  -- sp preserved (callee-saved)
    -- Memory preservation at caller's frame (for pair/case composition)
    -- These track that memory at the ORIGINAL sp locations is preserved
    ir-mem-sp    : readMem (memory s') (readReg (regs s) sp) ≡ readMem (memory s) (readReg (regs s) sp)
    ir-mem-sp+8  : readMem (memory s') (readReg (regs s) sp +ℕ 8) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 8)
    ir-mem-sp+16 : readMem (memory s') (readReg (regs s) sp +ℕ 16) ≡ readMem (memory s) (readReg (regs s) sp +ℕ 16)

open IRStarResult public

------------------------------------------------------------------------
-- IRRunner: Type signature for recursive IR executor
--
-- This type allows us to pass the recursive function as a parameter
-- to helper functions, enabling extraction from the mutual block.
------------------------------------------------------------------------

IRRunner : Set
IRRunner = ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
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

run-id-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (id {A}) (prefix ++ compile-riscv (id {A}) ++ suffix) s s' x (length prefix)
run-id-star {A} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = a0-eq  -- a0 unchanged, eval id x = x
  ; ir-s1     = refl
  ; ir-ra     = refl
  ; ir-sp     = refl
  ; ir-mem-sp    = refl  -- no memory write
  ; ir-mem-sp+8  = refl
  ; ir-mem-sp+16 = refl
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

run-terminal-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (terminal {A}) (prefix ++ compile-riscv (terminal {A}) ++ suffix) s s' x (length prefix)
run-terminal-star {A} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans (readReg-writeReg-same (regs s) a0 0 (λ ())) (sym encode-unit)
  ; ir-s1     = refl
  ; ir-ra     = refl
  ; ir-sp     = readReg-writeReg-a0-sp (regs s) 0
  ; ir-mem-sp    = refl  -- no memory write
  ; ir-mem-sp+8  = refl
  ; ir-mem-sp+16 = refl
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

run-fold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (fold {F}) (prefix ++ compile-riscv (fold {F}) ++ suffix) s s' x (length prefix)
run-fold-star {F} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans a0-eq (encode-fix-wrap x)
  ; ir-s1     = refl
  ; ir-ra     = refl
  ; ir-sp     = refl
  ; ir-mem-sp    = refl  -- no memory write
  ; ir-mem-sp+8  = refl
  ; ir-mem-sp+16 = refl
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

run-unfold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (unfold {F}) (prefix ++ compile-riscv (unfold {F}) ++ suffix) s s' x (length prefix)
run-unfold-star {F} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans a0-eq (encode-fix-unwrap x)
  ; ir-s1     = refl
  ; ir-ra     = refl
  ; ir-sp     = refl
  ; ir-mem-sp    = refl  -- no memory write
  ; ir-mem-sp+8  = refl
  ; ir-mem-sp+16 = refl
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

run-arr-star : ∀ {A B} (prefix suffix : Program) (f : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode {A ⇒ B} f →
  ∃[ s' ] IRStarResult (arr {A} {B}) (prefix ++ compile-riscv (arr {A} {B}) ++ suffix) s s' f (length prefix)
run-arr-star {A} {B} prefix suffix f s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = trans a0-eq (encode-arr-identity f)  -- encode {A ⇒ B} f ≡ encode {Eff A B} f
  ; ir-s1     = refl
  ; ir-ra     = refl
  ; ir-sp     = refl
  ; ir-mem-sp    = refl  -- no memory write
  ; ir-mem-sp+8  = refl
  ; ir-mem-sp+16 = refl
  }
  where
    prog = prefix ++ nop ∷ suffix
    s' = record s { pc = pc s +ℕ 1 }
    step-eq : step prog s ≡ just s'
    step-eq = trans (step-at-offset prefix nop suffix s h-false pc-eq) (execNop prog s)

------------------------------------------------------------------------
-- Base case: fst (1 instruction: ld a0, 0(a0))
--
-- compile-riscv fst = ld a0 (+ 0) a0 ∷ []
-- compile-length fst = 1
--
-- After ld: a0 = memory[a0] = encode (proj₁ x)
------------------------------------------------------------------------

run-fst-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (fst {A} {B}) (prefix ++ compile-riscv (fst {A} {B}) ++ suffix) s s' x (length prefix)
run-fst-star {A} {B} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = readReg-writeReg-same (regs s) a0 (encode (proj₁ x)) (λ ())
  ; ir-s1     = readReg-writeReg-a0-s1 (regs s) (encode (proj₁ x))
  ; ir-ra     = readReg-writeReg-a0-ra (regs s) (encode (proj₁ x))
  ; ir-sp     = readReg-writeReg-a0-sp (regs s) (encode (proj₁ x))
  ; ir-mem-sp    = refl  -- no memory write (only read)
  ; ir-mem-sp+8  = refl
  ; ir-mem-sp+16 = refl
  }
  where
    prog = prefix ++ ld a0 (+ 0) a0 ∷ suffix
    a = proj₁ x

    -- Memory precondition from encoding axiom
    mem-eq : readMem (memory s) (encode x) ≡ just (encode a)
    mem-eq = encode-pair-fst (proj₁ x) (proj₂ x) (memory s)

    -- Effective address = a0 + 0 = encode x
    eff-addr : effectiveAddr (regs s) a0 (+ 0) ≡ encode x
    eff-addr = trans (cong (readReg (regs s) a0 +ℕ_) refl)
                     (trans (+-identityʳ (readReg (regs s) a0)) a0-eq)

    -- Memory read succeeds
    mem-read : readMem (memory s) (effectiveAddr (regs s) a0 (+ 0)) ≡ just (encode a)
    mem-read = trans (cong (λ addr → readMem (memory s) addr) eff-addr) mem-eq

    s' = record s { regs = writeReg (regs s) a0 (encode a) ; pc = pc s +ℕ 1 }

    fetch-eq : fetch prog (pc s) ≡ just (ld a0 (+ 0) a0)
    fetch-eq = subst (λ p → fetch prog p ≡ just (ld a0 (+ 0) a0))
                     (sym pc-eq) (fetch-at-prefix-end prefix (ld a0 (+ 0) a0) suffix)

    step-eq : step prog s ≡ just s'
    step-eq = trans (step-exec prog s (ld a0 (+ 0) a0) h-false fetch-eq)
                    (execInstr-ld-success prog s a0 a0 (+ 0) (encode a) mem-read)

------------------------------------------------------------------------
-- Base case: snd (1 instruction: ld a0, 8(a0))
--
-- compile-riscv snd = ld a0 (+ 8) a0 ∷ []
-- compile-length snd = 1
--
-- After ld: a0 = memory[a0+8] = encode (proj₂ x)
------------------------------------------------------------------------

run-snd-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) a0 ≡ encode x →
  ∃[ s' ] IRStarResult (snd {A} {B}) (prefix ++ compile-riscv (snd {A} {B}) ++ suffix) s s' x (length prefix)
run-snd-star {A} {B} prefix suffix x s h-false pc-eq a0-eq = s' , record
  { ir-star   = star-single h-false step-eq
  ; ir-halted = h-false
  ; ir-pc     = cong (_+ℕ 1) pc-eq
  ; ir-a0     = readReg-writeReg-same (regs s) a0 (encode (proj₂ x)) (λ ())
  ; ir-s1     = readReg-writeReg-a0-s1 (regs s) (encode (proj₂ x))
  ; ir-ra     = readReg-writeReg-a0-ra (regs s) (encode (proj₂ x))
  ; ir-sp     = readReg-writeReg-a0-sp (regs s) (encode (proj₂ x))
  ; ir-mem-sp    = refl  -- no memory write (only read)
  ; ir-mem-sp+8  = refl
  ; ir-mem-sp+16 = refl
  }
  where
    prog = prefix ++ ld a0 (+ 8) a0 ∷ suffix
    b = proj₂ x

    -- Memory precondition from encoding axiom
    mem-eq : readMem (memory s) (encode x +ℕ 8) ≡ just (encode b)
    mem-eq = encode-pair-snd (proj₁ x) (proj₂ x) (memory s)

    -- Effective address = a0 + 8 = encode x + 8
    eff-addr : effectiveAddr (regs s) a0 (+ 8) ≡ encode x +ℕ 8
    eff-addr = cong (_+ℕ 8) a0-eq

    -- Memory read succeeds
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

-- Re-export Star infrastructure
open import Once.Backend.RiscV64.Correct.Star public
  using (Star; refl*; step*; star-trans; star-single; ⟨_,_⟩◅_; _◅◅_;
         star-step2; star-step3; star-step4; star-step5;
         exec-to-star; star-to-exec; star-to-exec-∃;
         star-to-exec-chain; exec-halted-extend; star-length)
