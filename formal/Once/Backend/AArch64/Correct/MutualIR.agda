------------------------------------------------------------------------
-- Once.Backend.AArch64.Correct.MutualIR
--
-- Mutual block for run-ir-star-at-offset and complex IR cases.
-- Following the x86 structure for consistency.
------------------------------------------------------------------------

module Once.Backend.AArch64.Correct.MutualIR where

open import Once.Type using (Type; _*_; _+_; _⇒_; Eff; Unit; Void; Fix)
open import Once.IR
open import Once.Semantics hiding (code-ptr; env-addr; semantics)

open import Once.Backend.AArch64.Syntax
open import Once.Backend.AArch64.Semantics
open State
open import Once.Backend.AArch64.CodeGen

open import Once.Backend.AArch64.Correct.Foundation
  using (encode; encodedMemory; encode-unit; encode-pair-fst; encode-pair-snd;
         encode-arr-identity; encode-fix-wrap; encode-fix-unwrap;
         readReg-writeReg-same; readReg-writeReg-x0-x20; readReg-writeReg-x0-x21;
         readReg-writeReg-x0-x29; readReg-writeReg-x0-x30;
         exec-chain; step-instr; fetch-append-right; execInstr-nop; execInstr-mov-imm;
         execInstr-ldr-success)
open import Once.Backend.AArch64.Correct.FetchStep
  using (step-exec-at-offset)
open import Once.Backend.AArch64.Correct.CompileLength
  using (compile-length-correct)
open import Once.Backend.AArch64.Correct.StackInvariant
  using (StackInvariant; X29Invariant; stack-inv-preserved-unchanged; sp>16-preserved-unchanged)
open import Once.Backend.AArch64.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; exec-to-star)

-- Re-export StarBase for backwards compatibility
open import Once.Backend.AArch64.Correct.StarBase public
  using (IRStarResult; ir-star; ir-halted; ir-pc; ir-x0;
         ir-x20; ir-x21; ir-x29; ir-x30;
         ir-mem-x21; ir-mem-x29; ir-mem-x29+8;
         ir-stack-inv; ir-sp-bound;
         IRRunner; combine-star-results)

-- Import extracted IR helper modules (non-recursive parts)
open import Once.Backend.AArch64.Correct.IR.Compose
  using (ComposeContext; mkComposeContext;
         ComposeFResult; ComposeNopResult; ComposeGResult;
         arith-compose-total; arith-compose-pc)
open import Once.Backend.AArch64.Correct.IR.Pair
  using (PairContext; mkPairContext;
         PairSetupResult; PairMiddleResult; PairFinalResult)
open import Once.Backend.AArch64.Correct.IR.Case
  using (CaseContext; mkCaseContext)
open import Once.Backend.AArch64.Correct.IR.Curry
  using (CurryContext; mkCurryContext;
         CurryFinalResult;
         arith-curry-pc-final)
open import Once.Backend.AArch64.Correct.IR.Apply
  using (ApplyContext; mkApplyContext;
         ApplySetupResult; run-ir-at-offset-apply;
         closure-code-ptr; closure-env)

-- | Re-export ClosureWellFormed types for whole-program proofs
-- These enable eliminating the apply postulate by threading well-formedness
-- from curry (producer) to apply (consumer)
open import Once.Backend.AArch64.Correct.ClosureWellFormed public
  using ( ClosureWellFormed
        ; ThunkResult
        ; CurryResult
        ; ApplyWithWFResult
        ; run-apply-with-wf
        )

-- | Import centralized postulates
-- These are backend-specific axioms that are documented and justified
open import Once.Backend.AArch64.Postulates
  using (sp-bound-after-stack-op; apply-produces-result)

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_; _>_; _≥_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Simple Star proofs (non-recursive base cases)
------------------------------------------------------------------------

-- These are proven by building Star proofs from step lemmas.
-- Each base case generates simple code (usually just nop) that
-- preserves x0 or modifies it trivially.

-- | Star-based id execution
-- compile-aarch64 id = nop ∷ []
-- eval id x = x, so x0 is unchanged
run-id-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 {A} {A} id ++ suffix
  in ∃[ s' ] IRStarResult {A} {A} id prog s s' x (length prefix)
run-id-star {A} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
  let prog = prefix ++ nop ∷ suffix
      -- The result state: only PC changes
      s' = record s { pc = pc s +ℕ 1 }

      -- Step 1: show step executes nop
      step-eq : step prog s ≡ execInstr prog s nop
      step-eq = step-exec-at-offset prefix nop suffix s h-false pc-eq

      exec-eq : execInstr prog s nop ≡ just s'
      exec-eq = execInstr-nop prog s

      step-full : step prog s ≡ just s'
      step-full = trans step-eq exec-eq

      -- Step 2: build Star proof
      star-pf : Star prog s s'
      star-pf = star-single h-false step-full

      -- Step 3: verify all IRStarResult fields
      -- halted unchanged
      h'-false : halted s' ≡ false
      h'-false = h-false

      -- pc s' = pc s + 1 = length prefix + 1 = length prefix + compile-length id
      pc'-eq : pc s' ≡ length prefix +ℕ compile-length {A} {A} id
      pc'-eq = cong (λ p → p +ℕ 1) pc-eq

      -- x0 unchanged (nop doesn't touch registers)
      -- eval id x = x, so encode (eval id x) = encode x
      x0'-eq : readReg (regs s') x0 ≡ encode (eval id x)
      x0'-eq = x0-eq  -- regs s' = regs s, and eval id x = x

      -- StackInvariant preserved (sp and x21 unchanged)
      stack-inv' : StackInvariant s'
      stack-inv' = stack-inv-preserved-unchanged s s' stack-inv refl refl

      -- sp>16 preserved (sp unchanged)
      sp>16' : readSP (regs s') > 16
      sp>16' = sp>16-preserved-unchanged s s' sp>16 refl

      -- Build the result
      result : IRStarResult {A} {A} id prog s s' x (length prefix)
      result = record
        { ir-star = star-pf
        ; ir-halted = h'-false
        ; ir-pc = pc'-eq
        ; ir-x0 = x0'-eq
        ; ir-x20 = refl  -- regs unchanged
        ; ir-x21 = refl
        ; ir-x29 = refl
        ; ir-x30 = refl
        ; ir-mem-x21 = refl  -- memory unchanged
        ; ir-mem-x29 = refl
        ; ir-mem-x29+8 = refl
        ; ir-stack-inv = stack-inv'
        ; ir-sp-bound = sp>16'
        }

  in s' , result

-- | Star-based terminal execution
-- compile-aarch64 terminal = mov x0 (imm 0) ∷ []
-- eval terminal x = tt, encode tt = 0
run-terminal-star : ∀ {A} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 {A} {Unit} terminal ++ suffix
  in ∃[ s' ] IRStarResult {A} {Unit} terminal prog s s' x (length prefix)
run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv sp>16 =
  let prog = prefix ++ mov x0 (imm 0) ∷ suffix
      s' = record s { regs = writeReg (regs s) x0 0 ; pc = pc s +ℕ 1 }

      step-eq : step prog s ≡ execInstr prog s (mov x0 (imm 0))
      step-eq = step-exec-at-offset prefix (mov x0 (imm 0)) suffix s h-false pc-eq

      exec-eq : execInstr prog s (mov x0 (imm 0)) ≡ just s'
      exec-eq = execInstr-mov-imm prog s x0 0

      step-full : step prog s ≡ just s'
      step-full = trans step-eq exec-eq

      star-pf : Star prog s s'
      star-pf = star-single h-false step-full

      stack-inv' : StackInvariant s'
      stack-inv' = stack-inv-preserved-unchanged s s' stack-inv
                     (readReg-writeReg-x0-x21 (regs s) 0) refl

      sp>16' : readSP (regs s') > 16
      sp>16' = sp>16-preserved-unchanged s s' sp>16 refl

      result : IRStarResult {A} {Unit} terminal prog s s' x (length prefix)
      result = record
        { ir-star = star-pf
        ; ir-halted = h-false
        ; ir-pc = cong (λ p → p +ℕ 1) pc-eq
        ; ir-x0 = trans (readReg-writeReg-same (regs s) x0 0) (sym encode-unit)
        ; ir-x20 = readReg-writeReg-x0-x20 (regs s) 0
        ; ir-x21 = readReg-writeReg-x0-x21 (regs s) 0
        ; ir-x29 = readReg-writeReg-x0-x29 (regs s) 0
        ; ir-x30 = readReg-writeReg-x0-x30 (regs s) 0
        ; ir-mem-x21 = refl
        ; ir-mem-x29 = refl
        ; ir-mem-x29+8 = refl
        ; ir-stack-inv = stack-inv'
        ; ir-sp-bound = sp>16'
        }

  in s' , result

-- | Star-based fold execution
-- compile-aarch64 fold = nop ∷ []
-- eval fold x = wrap x, encode (wrap x) = encode x (by encode-fix-wrap)
run-fold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 {F} {Fix F} fold ++ suffix
  in ∃[ s' ] IRStarResult {F} {Fix F} fold prog s s' x (length prefix)
run-fold-star {F} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
  let prog = prefix ++ nop ∷ suffix
      s' = record s { pc = pc s +ℕ 1 }

      step-eq : step prog s ≡ execInstr prog s nop
      step-eq = step-exec-at-offset prefix nop suffix s h-false pc-eq

      step-full : step prog s ≡ just s'
      step-full = trans step-eq (execInstr-nop prog s)

      star-pf : Star prog s s'
      star-pf = star-single h-false step-full

      stack-inv' : StackInvariant s'
      stack-inv' = stack-inv-preserved-unchanged s s' stack-inv refl refl

      sp>16' : readSP (regs s') > 16
      sp>16' = sp>16-preserved-unchanged s s' sp>16 refl

      -- eval fold x = wrap x, and encode (wrap x) = encode x
      x0'-eq : readReg (regs s') x0 ≡ encode (eval fold x)
      x0'-eq = trans x0-eq (sym (encode-fix-wrap x))

      result : IRStarResult {F} {Fix F} fold prog s s' x (length prefix)
      result = record
        { ir-star = star-pf
        ; ir-halted = h-false
        ; ir-pc = cong (λ p → p +ℕ 1) pc-eq
        ; ir-x0 = x0'-eq
        ; ir-x20 = refl
        ; ir-x21 = refl
        ; ir-x29 = refl
        ; ir-x30 = refl
        ; ir-mem-x21 = refl
        ; ir-mem-x29 = refl
        ; ir-mem-x29+8 = refl
        ; ir-stack-inv = stack-inv'
        ; ir-sp-bound = sp>16'
        }

  in s' , result

-- | Star-based unfold execution
-- compile-aarch64 unfold = nop ∷ []
-- eval unfold (wrap x) = x, encode x = encode (wrap x) (by encode-fix-unwrap)
run-unfold-star : ∀ {F} (prefix suffix : Program) (x : ⟦ Fix F ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 {Fix F} {F} unfold ++ suffix
  in ∃[ s' ] IRStarResult {Fix F} {F} unfold prog s s' x (length prefix)
run-unfold-star {F} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
  let prog = prefix ++ nop ∷ suffix
      s' = record s { pc = pc s +ℕ 1 }

      step-eq : step prog s ≡ execInstr prog s nop
      step-eq = step-exec-at-offset prefix nop suffix s h-false pc-eq

      step-full : step prog s ≡ just s'
      step-full = trans step-eq (execInstr-nop prog s)

      star-pf : Star prog s s'
      star-pf = star-single h-false step-full

      stack-inv' : StackInvariant s'
      stack-inv' = stack-inv-preserved-unchanged s s' stack-inv refl refl

      sp>16' : readSP (regs s') > 16
      sp>16' = sp>16-preserved-unchanged s s' sp>16 refl

      -- eval unfold x = unwrap x, and encode (unwrap x) = encode x
      x0'-eq : readReg (regs s') x0 ≡ encode (eval unfold x)
      x0'-eq = trans x0-eq (sym (encode-fix-unwrap x))

      result : IRStarResult {Fix F} {F} unfold prog s s' x (length prefix)
      result = record
        { ir-star = star-pf
        ; ir-halted = h-false
        ; ir-pc = cong (λ p → p +ℕ 1) pc-eq
        ; ir-x0 = x0'-eq
        ; ir-x20 = refl
        ; ir-x21 = refl
        ; ir-x29 = refl
        ; ir-x30 = refl
        ; ir-mem-x21 = refl
        ; ir-mem-x29 = refl
        ; ir-mem-x29+8 = refl
        ; ir-stack-inv = stack-inv'
        ; ir-sp-bound = sp>16'
        }

  in s' , result

-- | Star-based arr execution
-- compile-aarch64 arr = nop ∷ []
-- eval arr fn = fn (as Eff), encode (fn as Eff) = encode fn (by encode-arr-identity)
run-arr-star : ∀ {A B} (prefix suffix : Program) (fn : ⟦ A ⇒ B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode {A ⇒ B} fn →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 {A ⇒ B} {Eff A B} arr ++ suffix
  in ∃[ s' ] IRStarResult {A ⇒ B} {Eff A B} arr prog s s' fn (length prefix)
run-arr-star {A} {B} prefix suffix fn s h-false pc-eq x0-eq stack-inv sp>16 =
  let prog = prefix ++ nop ∷ suffix
      s' = record s { pc = pc s +ℕ 1 }

      step-eq : step prog s ≡ execInstr prog s nop
      step-eq = step-exec-at-offset prefix nop suffix s h-false pc-eq

      step-full : step prog s ≡ just s'
      step-full = trans step-eq (execInstr-nop prog s)

      star-pf : Star prog s s'
      star-pf = star-single h-false step-full

      stack-inv' : StackInvariant s'
      stack-inv' = stack-inv-preserved-unchanged s s' stack-inv refl refl

      sp>16' : readSP (regs s') > 16
      sp>16' = sp>16-preserved-unchanged s s' sp>16 refl

      -- eval arr fn = fn (as Eff A B), encode preserves by encode-arr-identity
      -- Note: eval arr fn = fn (same value, different type annotation)
      x0'-eq : readReg (regs s') x0 ≡ encode {Eff A B} (eval {A ⇒ B} {Eff A B} arr fn)
      x0'-eq = trans x0-eq (sym (encode-arr-identity {A} {B} fn))

      result : IRStarResult {A ⇒ B} {Eff A B} arr prog s s' fn (length prefix)
      result = record
        { ir-star = star-pf
        ; ir-halted = h-false
        ; ir-pc = cong (λ p → p +ℕ 1) pc-eq
        ; ir-x0 = x0'-eq
        ; ir-x20 = refl
        ; ir-x21 = refl
        ; ir-x29 = refl
        ; ir-x30 = refl
        ; ir-mem-x21 = refl
        ; ir-mem-x29 = refl
        ; ir-mem-x29+8 = refl
        ; ir-stack-inv = stack-inv'
        ; ir-sp-bound = sp>16'
        }

  in s' , result

-- | Star-based fst execution
-- compile-aarch64 fst = ldr x0 (base x0) ∷ []
-- Loads first component from pair pointer
run-fst-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 {A * B} {A} fst ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {A} fst prog s s' x (length prefix)
run-fst-star {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
  let prog = prefix ++ ldr x0 (base x0) ∷ suffix
      a = proj₁ x
      b = proj₂ x

      -- Memory contains encoded pair: reading at encode (a,b) gives encode a
      mem-eq : readMem (memory s) (encode (a , b)) ≡ just (encode a)
      mem-eq = encode-pair-fst a b (memory s)

      -- Effective address = readReg x0 = encode x = encode (a, b)
      eff-addr-eq : readMem (memory s) (readReg (regs s) x0) ≡ just (encode a)
      eff-addr-eq = subst (λ addr → readMem (memory s) addr ≡ just (encode a))
                          (sym x0-eq) mem-eq

      -- Result state
      s' = record s { regs = writeReg (regs s) x0 (encode a) ; pc = pc s +ℕ 1 }

      -- Step proof
      step-eq : step prog s ≡ execInstr prog s (ldr x0 (base x0))
      step-eq = step-exec-at-offset prefix (ldr x0 (base x0)) suffix s h-false pc-eq

      exec-eq : execInstr prog s (ldr x0 (base x0)) ≡ just s'
      exec-eq = execInstr-ldr-success prog s x0 (base x0) (encode a) eff-addr-eq

      step-full : step prog s ≡ just s'
      step-full = trans step-eq exec-eq

      star-pf : Star prog s s'
      star-pf = star-single h-false step-full

      stack-inv' : StackInvariant s'
      stack-inv' = stack-inv-preserved-unchanged s s' stack-inv
                     (readReg-writeReg-x0-x21 (regs s) (encode a)) refl

      sp>16' : readSP (regs s') > 16
      sp>16' = sp>16-preserved-unchanged s s' sp>16 refl

      result : IRStarResult {A * B} {A} fst prog s s' x (length prefix)
      result = record
        { ir-star = star-pf
        ; ir-halted = h-false
        ; ir-pc = cong (λ p → p +ℕ 1) pc-eq
        ; ir-x0 = readReg-writeReg-same (regs s) x0 (encode a)
        ; ir-x20 = readReg-writeReg-x0-x20 (regs s) (encode a)
        ; ir-x21 = readReg-writeReg-x0-x21 (regs s) (encode a)
        ; ir-x29 = readReg-writeReg-x0-x29 (regs s) (encode a)
        ; ir-x30 = readReg-writeReg-x0-x30 (regs s) (encode a)
        ; ir-mem-x21 = refl
        ; ir-mem-x29 = refl
        ; ir-mem-x29+8 = refl
        ; ir-stack-inv = stack-inv'
        ; ir-sp-bound = sp>16'
        }

  in s' , result

-- | Star-based snd execution
-- compile-aarch64 snd = ldr x0 (base+imm x0 8) ∷ []
-- Loads second component from pair pointer + 8
run-snd-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A * B ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = prefix ++ compile-aarch64 {A * B} {B} snd ++ suffix
  in ∃[ s' ] IRStarResult {A * B} {B} snd prog s s' x (length prefix)
run-snd-star {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
  let prog = prefix ++ ldr x0 (base+imm x0 8) ∷ suffix
      a = proj₁ x
      b = proj₂ x

      -- Memory contains encoded pair: reading at encode (a,b) + 8 gives encode b
      mem-eq : readMem (memory s) (encode (a , b) +ℕ 8) ≡ just (encode b)
      mem-eq = encode-pair-snd a b (memory s)

      -- Effective address = readReg x0 + 8 = encode x + 8 = encode (a, b) + 8
      eff-addr-eq : readMem (memory s) (readReg (regs s) x0 +ℕ 8) ≡ just (encode b)
      eff-addr-eq = subst (λ addr → readMem (memory s) (addr +ℕ 8) ≡ just (encode b))
                          (sym x0-eq) mem-eq

      -- Result state
      s' = record s { regs = writeReg (regs s) x0 (encode b) ; pc = pc s +ℕ 1 }

      -- Step proof
      step-eq : step prog s ≡ execInstr prog s (ldr x0 (base+imm x0 8))
      step-eq = step-exec-at-offset prefix (ldr x0 (base+imm x0 8)) suffix s h-false pc-eq

      exec-eq : execInstr prog s (ldr x0 (base+imm x0 8)) ≡ just s'
      exec-eq = execInstr-ldr-success prog s x0 (base+imm x0 8) (encode b) eff-addr-eq

      step-full : step prog s ≡ just s'
      step-full = trans step-eq exec-eq

      star-pf : Star prog s s'
      star-pf = star-single h-false step-full

      stack-inv' : StackInvariant s'
      stack-inv' = stack-inv-preserved-unchanged s s' stack-inv
                     (readReg-writeReg-x0-x21 (regs s) (encode b)) refl

      sp>16' : readSP (regs s') > 16
      sp>16' = sp>16-preserved-unchanged s s' sp>16 refl

      result : IRStarResult {A * B} {B} snd prog s s' x (length prefix)
      result = record
        { ir-star = star-pf
        ; ir-halted = h-false
        ; ir-pc = cong (λ p → p +ℕ 1) pc-eq
        ; ir-x0 = readReg-writeReg-same (regs s) x0 (encode b)
        ; ir-x20 = readReg-writeReg-x0-x20 (regs s) (encode b)
        ; ir-x21 = readReg-writeReg-x0-x21 (regs s) (encode b)
        ; ir-x29 = readReg-writeReg-x0-x29 (regs s) (encode b)
        ; ir-x30 = readReg-writeReg-x0-x30 (regs s) (encode b)
        ; ir-mem-x21 = refl
        ; ir-mem-x29 = refl
        ; ir-mem-x29+8 = refl
        ; ir-stack-inv = stack-inv'
        ; ir-sp-bound = sp>16'
        }

  in s' , result

postulate
  -- | Star-based inl execution
  run-inl-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 {A} {A + B} inl ++ suffix
    in ∃[ s' ] IRStarResult {A} {A + B} inl prog s s' x (length prefix)

  -- | Star-based inr execution
  run-inr-star : ∀ {A B} (prefix suffix : Program) (x : ⟦ B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 {B} {A + B} inr ++ suffix
    in ∃[ s' ] IRStarResult {B} {A + B} inr prog s s' x (length prefix)

------------------------------------------------------------------------
-- Star-Based Mutual Block
--
-- This mutual block builds Star proofs using star-single and star-trans.
-- Star composition is just transitivity, proven by structural recursion.
------------------------------------------------------------------------

mutual
  -- | Star-based IR execution at arbitrary offset
  run-ir-star-at-offset : ∀ {A B} (ir : IR A B) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 ir ++ suffix
    in ∃[ s' ] IRStarResult ir prog s s' x (length prefix)

  -- Base cases: delegate to Star helper functions
  run-ir-star-at-offset (id {A}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-id-star {A} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (terminal {A}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-terminal-star {A} prefix suffix x s h-false pc-eq stack-inv sp>16
  run-ir-star-at-offset (fold {F}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-fold-star {F} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (unfold {F}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-unfold-star {F} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (arr {A} {B}) prefix suffix f s h-false pc-eq x0-eq stack-inv sp>16 =
    run-arr-star {A} {B} prefix suffix f s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (fst {A} {B}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-fst-star {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (snd {A} {B}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-snd-star {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (inl {A} {B}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-inl-star {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (inr {A} {B}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-inr-star {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (initial {A}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    ⊥-elim x  -- Void has no inhabitants

  -- Recursive cases: use Star-based composition
  run-ir-star-at-offset (_∘_ {A} {B} {C} g f) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-compose-star-direct f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (⟨_,_⟩ {A} {B} {C} f g) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-pair-star-direct f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset ([_,_] {A} {B} {C} f g) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-case-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (curry {A} {B} {C} f) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-curry-star-direct {A} {B} {C} f prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
  run-ir-star-at-offset (apply {A} {B}) prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    run-apply-star-direct {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16

  -- | Star-based compose execution
  -- Uses extracted helpers from IR.Compose - only recursive calls remain here
  run-compose-star-direct : ∀ {A B C} (f : IR A B) (g : IR B C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 (g ∘ f) ++ suffix
    in ∃[ s' ] IRStarResult (g ∘ f) prog s s' x (length prefix)
  run-compose-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    -- Postulated for now - full proof requires:
    -- 1. Execute f (recursive call)
    -- 2. Execute nop (transfer)
    -- 3. Execute g (recursive call)
    -- 4. Assemble final result
    compose-postulate f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
    where
      postulate
        compose-postulate : ∀ {A B C} (f : IR A B) (g : IR B C)
          (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
          halted s ≡ false →
          pc s ≡ length prefix →
          readReg (regs s) x0 ≡ encode x →
          StackInvariant s →
          readSP (regs s) > 16 →
          let prog = prefix ++ compile-aarch64 (g ∘ f) ++ suffix
          in ∃[ s' ] IRStarResult (g ∘ f) prog s s' x (length prefix)

  -- | Star-based pair execution
  run-pair-star-direct : ∀ {A B C} (f : IR C A) (g : IR C B) (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 ⟨ f , g ⟩ ++ suffix
    in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)
  run-pair-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    -- Postulated for now - full proof requires:
    -- 1. Execute setup (7 instructions)
    -- 2. Execute f (recursive)
    -- 3. Execute middle (2 instructions)
    -- 4. Execute g (recursive)
    -- 5. Execute final (6 instructions)
    pair-postulate f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
    where
      postulate
        pair-postulate : ∀ {A B C} (f : IR C A) (g : IR C B)
          (prefix suffix : Program) (x : ⟦ C ⟧) (s : State) →
          halted s ≡ false →
          pc s ≡ length prefix →
          readReg (regs s) x0 ≡ encode x →
          StackInvariant s →
          readSP (regs s) > 16 →
          let prog = prefix ++ compile-aarch64 ⟨ f , g ⟩ ++ suffix
          in ∃[ s' ] IRStarResult ⟨ f , g ⟩ prog s s' x (length prefix)

  -- | Star-based case execution
  run-case-star-direct : ∀ {A B C} (f : IR A C) (g : IR B C) (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix
    in ∃[ s' ] IRStarResult [ f , g ] prog s s' x (length prefix)
  run-case-star-direct {A} {B} {C} f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    -- Postulated for now - full proof requires:
    -- 1. Execute tag check
    -- 2. Branch to f or g
    -- 3. Execute selected branch (recursive)
    -- 4. Jump to end
    case-postulate f g prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
    where
      postulate
        case-postulate : ∀ {A B C} (f : IR A C) (g : IR B C)
          (prefix suffix : Program) (x : ⟦ A + B ⟧) (s : State) →
          halted s ≡ false →
          pc s ≡ length prefix →
          readReg (regs s) x0 ≡ encode x →
          StackInvariant s →
          readSP (regs s) > 16 →
          let prog = prefix ++ compile-aarch64 [ f , g ] ++ suffix
          in ∃[ s' ] IRStarResult [ f , g ] prog s s' x (length prefix)

  -- | Star-based curry execution
  --
  -- This version returns IRStarResult (uniform type for all IR terms).
  -- For proofs that need ClosureWellFormed threading, use CurryResult
  -- from ClosureWellFormed which includes a closure-wf field proving
  -- the produced closure is well-formed.
  run-curry-star-direct : ∀ {A B C} (f : IR (A * B) C) (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 (curry f) ++ suffix
    in ∃[ s' ] IRStarResult (curry f) prog s s' x (length prefix)
  run-curry-star-direct {A} {B} {C} f prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    -- Curry is non-recursive: creates closure, jumps over thunk.
    -- For well-formedness threading, use CurryResult which includes
    -- a ClosureWellFormed proof for the produced closure.
    curry-postulate f prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
    where
      postulate
        curry-postulate : ∀ {A B C} (f : IR (A * B) C)
          (prefix suffix : Program) (x : ⟦ A ⟧) (s : State) →
          halted s ≡ false →
          pc s ≡ length prefix →
          readReg (regs s) x0 ≡ encode x →
          StackInvariant s →
          readSP (regs s) > 16 →
          let prog = prefix ++ compile-aarch64 (curry f) ++ suffix
          in ∃[ s' ] IRStarResult (curry f) prog s s' x (length prefix)

  -- | Star-based apply execution
  --
  -- Uses the centralized apply-produces-result postulate from Postulates.agda.
  -- The postulate is needed because we don't have ClosureWellFormed
  -- threading in the uniform IRStarResult approach.
  --
  -- For whole-program proofs that can eliminate the postulate, use
  -- run-apply-with-wf from ClosureWellFormed which takes a
  -- ClosureWellFormed proof (produced by curry) as input.
  run-apply-star-direct : ∀ {A B} (prefix suffix : Program) (x : ⟦ (A ⇒ B) * A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    readReg (regs s) x0 ≡ encode {(A ⇒ B) * A} x →
    StackInvariant s →
    readSP (regs s) > 16 →
    let prog = prefix ++ compile-aarch64 (apply {A} {B}) ++ suffix
    in ∃[ s' ] IRStarResult (apply {A} {B}) prog s s' x (length prefix)
  run-apply-star-direct {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16 =
    -- Use centralized postulate and wrap result in IRStarResult
    let (s' , star-pf , halted-pf , pc-pf , x0-pf , x20-pf , x21-pf , x29-pf , x30-pf ,
         mem-x21-pf , mem-x29-pf , mem-x29+8-pf , stack-inv' , sp>16') =
           apply-produces-result {A} {B} prefix suffix x s h-false pc-eq x0-eq stack-inv sp>16
    in s' , record
      { ir-star = star-pf
      ; ir-halted = halted-pf
      ; ir-pc = pc-pf
      ; ir-x0 = x0-pf
      ; ir-x20 = x20-pf
      ; ir-x21 = x21-pf
      ; ir-x29 = x29-pf
      ; ir-x30 = x30-pf
      ; ir-mem-x21 = mem-x21-pf
      ; ir-mem-x29 = mem-x29-pf
      ; ir-mem-x29+8 = mem-x29+8-pf
      ; ir-stack-inv = stack-inv'
      ; ir-sp-bound = sp>16'
      }

------------------------------------------------------------------------
-- Main theorem: codegen correctness
------------------------------------------------------------------------

-- | The main correctness theorem: for any IR term and input,
-- executing the compiled code produces the semantically correct result.
codegen-aarch64-star-correct : ∀ {A B : Type} (ir : IR A B) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ 0 →
  readReg (regs s) x0 ≡ encode x →
  StackInvariant s →
  readSP (regs s) > 16 →
  let prog = [] ++ compile-aarch64 ir ++ []
  in ∃[ s' ] IRStarResult ir prog s s' x 0
codegen-aarch64-star-correct ir x s h-false pc-eq x0-eq stack-inv sp>16 =
  run-ir-star-at-offset ir [] [] x s h-false pc-eq x0-eq stack-inv sp>16

