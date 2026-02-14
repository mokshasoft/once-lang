------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.Apply
--
-- Apply implementation for X86v3 dispatcher.
-- Takes RecDispatcher as parameter, enabling termination checking.
--
-- Key insight: When we extract body from a closure, we also extract
-- body-acc : Acc _<_ (ir-size body). We can construct a RecDispatcher
-- for (suc (ir-size body)) from this Acc, allowing us to call body.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.Apply where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; n<1+n)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Induction.WellFounded using (Acc; acc)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

module ApplyImpl {FS : FrameSemantics} where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open FrontierInvariant {FS}
  open StackAllocation {FS}
  open FrameSemantics FS

  -- Import result type and RecDispatcher from IRResult (avoids circular dependency)
  open import Once.Backend.X86v3.IRResult using (module DispatcherResult; module RecDispatcherDef)
  open DispatcherResult {FS}
  open RecDispatcherDef {FS}

  -- Import write operations
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Apply implementation
  -- Takes:
  --   - body : IR (EnvType * A) B (the closure's body)
  --   - env : ⟦ EnvType ⟧ (the captured environment)
  --   - arg : ⟦ A ⟧ (the argument)
  --   - rec : RecDispatcher bound where ir-size body < bound
  --   - body<bound : proof that ir-size body < bound
  --
  -- This allows Apply to dispatch to body without needing direct recursion.
  run-apply : ∀ {EnvType A B}
    (body : IR (EnvType * A) B)
    (env : ⟦ EnvType ⟧)
    (arg : ⟦ A ⟧)
    (bound : ℕ) (rec : RecDispatcher bound)
    (body<bound : ir-size body < bound)
    (pair-input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc (pair env arg) pair-input-loc s →
    BeforeFrontier alloc pair-input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ pair-input-loc →
    -- Result is the body's result, but semantically it equals apply's result
    IRResultA body (pair env arg) s alloc
  run-apply body env arg bound rec body<bound pair-input-loc s alloc
    pair-valid pair-before not-halted rdi-eq =
    rec body body<bound (pair env arg) pair-input-loc s alloc
      pair-valid pair-before not-halted rdi-eq
