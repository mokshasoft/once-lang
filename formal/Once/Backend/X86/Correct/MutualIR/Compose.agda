------------------------------------------------------------------------
-- Once.Backend.X86.Correct.MutualIR.Compose
--
-- Compose implementation as a parameterized module.
-- Takes a size-bounded recursive dispatcher as a module parameter.
-- Enables well-founded recursion on IR size via Acc pattern.
------------------------------------------------------------------------

open import Once.Type
open import Once.IR
open import Once.Semantics hiding (env-addr; semantics)

open import Once.Backend.X86.Syntax
open import Once.Backend.X86.Semantics
open Once.Backend.X86.Semantics.State
open import Once.Backend.X86.CodeGen

-- Import types needed for module parameter signature
open import Once.Backend.X86.Correct.StarBase
  using (IRStarResultV)
open import Once.Backend.X86.Correct.MemoryValid
  using (ValidAt)
open import Once.Backend.X86.Correct.StackInvariant
  using (StackInvariant; RbpInvariant)
open import Once.Backend.X86.Correct.StackInstantiation using (slots; StackCapacity; ir-stack-requirement)
open import Once.Backend.Common.MemoryRegions
  using (StackPointer)
open import Once.Backend.X86.Correct.IRSize
  using (ir-size; ∘-f-smaller; ∘-g-smaller)
open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; _>_; _<_; _∸_) renaming (_+_ to _+ℕ_)
open import Data.List using (List; _++_; length)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

-- Parameterized module: takes size bound and size-bounded dispatcher
module Once.Backend.X86.Correct.MutualIR.Compose
  (bound : ℕ)
  (run-ir-star : ∀ {A B} (ir : IR A B) → ir-size ir < bound →
    (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
    halted s ≡ false →
    pc s ≡ length prefix →
    ValidAt x (readReg (regs s) rdi) (memory s) →
    StackInvariant s →
    StackCapacity s (ir-stack-requirement ir) →
    RbpInvariant s →
    let prog = prefix ++ compile-x86 ir ++ suffix
    in ∃[ s' ] IRStarResultV ir prog s s' x (length prefix))
  where

-- Additional imports needed inside the module (beyond what's in parameter signature)
open import Once.Backend.X86.Correct.StarBase
  using (rbp-inv-preserved-unchanged; IRStarResultV)
open import Once.Backend.X86.Correct.StackInstantiation
  using (capacity-preserved-rsp-unchanged; capacity-left-from-max; capacity-right-from-max;
         capacity-after-delta; ir-rsp-delta)
open import Once.Backend.X86.Correct.MemoryValid
  using (valid-subst-addr-mem)

-- Import Compose helpers (validity-based versions)
open import Once.Backend.X86.Correct.IR.Compose
  using (ComposeContext; make-compose-context; TransferResultV;
         compose-transfer-star-v; assemble-compose-result-v)
open import Once.Backend.X86.Correct.IR.Compose using (module ComposeContext)
open import Once.Backend.X86.Correct.IR.Compose using (module TransferResultV)

------------------------------------------------------------------------
-- Compose implementation using size-bounded dispatcher
-- Termination is proven via Acc pattern on ir-size in MutualIR.agda
------------------------------------------------------------------------
-- | Validity-based compose execution
-- Uses validity-based dispatcher and helpers - no encode bridging needed!
-- Takes size proofs for sub-terms to enable well-founded recursion.
run-compose-star-v : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-size f < bound →
  ir-size g < bound →
  (prefix suffix : Program) (caller-sp : StackPointer) (x : ⟦ A ⟧) (s : State) →
  halted s ≡ false →
  pc s ≡ length prefix →
  ValidAt x (readReg (regs s) rdi) (memory s) →
  StackInvariant s →
  StackCapacity s (ir-stack-requirement (g ∘ f)) →
  RbpInvariant s →
  let prog = prefix ++ compile-x86 (g ∘ f) ++ suffix
  in ∃[ s' ] IRStarResultV (g ∘ f) prog s s' x (length prefix)
run-compose-star-v {A} {B} {C} f g f<bound g<bound prefix suffix caller-sp x s h-false pc-eq input-valid stack-inv cap-in rbp-inv =
    s3 , result-v
    where
      -- Get context for computed values
      ctx = make-compose-context f g prefix suffix
      open ComposeContext ctx

      -- Derive sub-capacities from compose capacity
      -- ir-stack-requirement (g ∘ f) = ir-stack-requirement f ⊔ (ir-rsp-delta f +ℕ ir-stack-requirement g)
      cap-f : StackCapacity s (ir-stack-requirement f)
      cap-f = capacity-left-from-max s (ir-stack-requirement f) (ir-rsp-delta f +ℕ ir-stack-requirement g) cap-in

      -- Step 1: Execute f (RECURSIVE via size-bounded dispatcher)
      step-f : ∃[ s1 ] IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      step-f = run-ir-star f f<bound prefix suffix-f caller-sp x s h-false pc-eq input-valid stack-inv cap-f rbp-inv

      s1 : State
      s1 = proj₁ step-f

      r1-v : IRStarResultV f (prefix ++ code-f ++ suffix-f) s s1 x (length prefix)
      r1-v = proj₂ step-f

      -- Step 2: Execute transfer (validity-based helper - no encode bridging!)
      tr : TransferResultV f g prefix suffix x s s1
      tr = compose-transfer-star-v f g prefix suffix x s s1 r1-v

      s2 = TransferResultV.s2 tr

      -- RbpInvariant preserved through IR execution
      rsp-s2-eq-s1 : readReg (regs s2) rsp ≡ readReg (regs s1) rsp
      rsp-s2-eq-s1 = TransferResultV.rsp-s1-to-s2 tr

      rbp-s2-eq-s1 : readReg (regs s2) rbp ≡ readReg (regs s1) rbp
      rbp-s2-eq-s1 = TransferResultV.rbp-s1-to-s2 tr

      rbp-inv-2 : RbpInvariant s2
      rbp-inv-2 = rbp-inv-preserved-unchanged s1 s2 (IRStarResultV.ir-rbp-inv r1-v) rsp-s2-eq-s1 rbp-s2-eq-s1

      -- Construct validity for g's input via direct propagation
      -- The transfer moves rax→rdi and doesn't change memory
      -- So validity at rax in s1 becomes validity at rdi in s2
      input-valid-for-g : ValidAt (eval f x) (readReg (regs s2) rdi) (memory s2)
      input-valid-for-g = valid-subst-addr-mem
        (IRStarResultV.ir-result-valid r1-v)  -- ValidAt at rax in s1
        (TransferResultV.rdi2-raw tr)          -- rdi in s2 = rax in s1
        (TransferResultV.mem-s1-to-s2 tr)      -- memory unchanged

      -- Derive capacity for g from original compose capacity via rsp delta tracking
      -- f may change rsp by ir-rsp-delta f slots, so we use capacity-after-delta
      cap-delta-g-at-s : StackCapacity s (ir-rsp-delta f +ℕ ir-stack-requirement g)
      cap-delta-g-at-s = capacity-right-from-max s (ir-stack-requirement f) (ir-rsp-delta f +ℕ ir-stack-requirement g) cap-in

      -- f changes rsp: rsp s1 = rsp s ∸ slots (ir-rsp-delta f)
      rsp-s1-delta : readReg (regs s1) rsp ≡ readReg (regs s) rsp ∸ slots (ir-rsp-delta f)
      rsp-s1-delta = IRStarResultV.ir-rsp r1-v

      -- Use capacity-after-delta to derive capacity for g at s1
      cap-g-at-s1 : StackCapacity s1 (ir-stack-requirement g)
      cap-g-at-s1 = capacity-after-delta s s1 (ir-rsp-delta f) (ir-stack-requirement g) cap-delta-g-at-s rsp-s1-delta

      -- Transfer preserves rsp: rsp s2 = rsp s1
      cap-g : StackCapacity s2 (ir-stack-requirement g)
      cap-g = capacity-preserved-rsp-unchanged s1 s2 (ir-stack-requirement g) cap-g-at-s1 (sym rsp-s2-eq-s1)

      -- Step 3: Execute g (RECURSIVE via size-bounded dispatcher)
      step-g : ∃[ s3 ] IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      step-g = run-ir-star g g<bound prefix-g suffix caller-sp (eval f x) s2
                 (TransferResultV.h2 tr) (TransferResultV.pc2-g tr) input-valid-for-g
                 (TransferResultV.stack-inv-2 tr) cap-g rbp-inv-2

      s3 : State
      s3 = proj₁ step-g

      r3-v : IRStarResultV g (prefix-g ++ code-g ++ suffix) s2 s3 (eval f x) (length prefix-g)
      r3-v = proj₂ step-g

      -- Assemble final result (validity-based - no encode bridging!)
      result-v : IRStarResultV (g ∘ f) prog s s3 x (length prefix)
      result-v = assemble-compose-result-v f g prefix suffix x s s1 s2 s3 r1-v tr r3-v refl cap-in
