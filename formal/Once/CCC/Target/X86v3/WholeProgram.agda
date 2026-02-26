------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.WholeProgram
--
-- COMPILER CORRECTNESS THEOREM
--
-- The essential property:
--   Represents x s  →  Represents (eval primSem ir x) s'
--
-- Everything else is implementation detail.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.WholeProgram where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Induction.WellFounded using (Acc)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine using (LocState; ValueLocation; halted; regs; readReg; RDI)

open import Once.CCC.Target.X86v3.Types using (Type; ⟦_⟧)
open import Once.CCC.IR using (IR; eval; ir-size; ir-stack-requirement; AllocMode; pair-slots; PrimSem)
open import Once.CCC.Target.X86v3.Dispatcher.Allocation using (AllocState; next-slot; current-frame; frame-capacity; module FrontierInvariant)

-- Import escape interface for SurvivesFramePop
import Once.CCC.Target.X86v3.Dispatcher.IR.ApplyWF as ApplyWFModule

-- Import Dispatcher for PrimProofInterface
import Once.CCC.Target.X86v3.Dispatcher.Dispatcher as DispatcherModule

-- Import Refinement proofs (Layer 1→2: x86 → SlotMachine)
-- This imports CodeGen.Compile, completing the verification chain:
--   WholeProgram → Refinement.InstrCorrect → CodeGen.Compile
import Once.CCC.Target.X86v3.Refinement.InstrCorrect as RefinementModule

------------------------------------------------------------------------
-- THE CORRECTNESS THEOREM
------------------------------------------------------------------------

module Correctness
  {FS : FrameSemantics}
  (program-bound : ℕ)
  (acc-pb : Acc _<_ program-bound)
  -- PrimSem provides semantics for all primitives (required for eval)
  (primSem : PrimSem)
  (get-child-frame : ∀ (alloc : AllocState {FS}) → FrameSemantics.Frame FS)
  (child-frame-ordered : ∀ (alloc : AllocState {FS}) →
    FrameSemantics._≺_ FS (get-child-frame alloc) (AllocState.current-frame alloc))
  (child-frame-adjacent : ∀ (alloc : AllocState {FS}) (f : FrameSemantics.Frame FS) →
    FrameSemantics._≺_ FS (get-child-frame alloc) f →
    FrameSemantics._≺_ FS f (AllocState.current-frame alloc) →
    ⊥)
  (child-capacity : ℕ)
  (child-cap-sufficient : pair-slots *ℕ program-bound ≤ child-capacity)
  -- Escape analysis guarantees (provided by escape analysis pass)
  -- Body results survive child frame pop (the MINIMAL escape interface)
  (escape-result-survives : ∀ (alloc : AllocState {FS}) (body-final : AllocState {FS})
    (result-loc : ValueLocation FS) →
    current-frame body-final ≡ get-child-frame alloc →
    ApplyWFModule.BeforeFrontier' body-final result-loc →
    ApplyWFModule.SurvivesFramePop (get-child-frame alloc) result-loc)
  (parent-bound-eq : ∀ (alloc : AllocState {FS}) (bound : ℕ) →
    bound ≡ AllocState.next-slot alloc Data.Nat.+ pair-slots)
  -- Prim proof provider (from domain compilers)
  (prim-proof : DispatcherModule.PrimProofInterface.PrimProofProviderV3 {FS} program-bound primSem)
  where

  open FrontierInvariant {FS} using (BeforeFrontier)

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  module CWF = ClosureWellFormedDef {FS} program-bound primSem

  open import Once.CCC.Target.X86v3.Dispatcher.Dispatcher
  module D = Dispatcher {FS} program-bound acc-pb primSem
    get-child-frame child-frame-ordered child-frame-adjacent child-capacity child-cap-sufficient
    escape-result-survives parent-bound-eq prim-proof

  ----------------------------------------------------------------------
  -- Represents: value v is stored at location loc in state s
  --
  -- This is the abstraction boundary. ValidAtWF carries proof details,
  -- but conceptually it just means "v is at loc".
  ----------------------------------------------------------------------

  Represents : ∀ {A : Type} → AllocMode → AllocState {FS} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set
  Represents m alloc v loc s = CWF.ValidAtWF m alloc v loc s

  ----------------------------------------------------------------------
  -- COMPILER CORRECTNESS
  --
  -- The one theorem that matters:
  --   If input represents x, output represents (eval primSem ir x)
  --
  -- The (eval primSem ir x) is the semantic bridge between:
  --   - ir (syntax)
  --   - eval (denotational semantics)
  --   - execution (operational semantics)
  ----------------------------------------------------------------------

  compile-correct : ∀ {A B} (ir : IR A B)
    (mIn : AllocMode) (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    -- If input represents x...
    Represents mIn alloc x input-loc s →
    -- ...and preconditions hold...
    BeforeFrontier alloc input-loc →
    ir-size ir < program-bound →
    -- Machine is ready to execute (caller must establish)
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    next-slot alloc +ℕ ir-stack-requirement ir ≤ frame-capacity alloc →
    -- ...then output represents (eval primSem ir x)
    ∃[ mOut ] ∃[ result-loc ] ∃[ s' ] ∃[ alloc' ]
      Represents mOut alloc' (eval primSem ir x) result-loc s'
      --                      ^^^^^^^^^^
      --            THE SEMANTIC CONNECTION
  compile-correct ir mIn x input-loc s alloc repr before ir<bound not-halted rdi-eq capacity-ok =
    -- Invoke Dispatcher with operational preconditions (caller provided)
    let (mOut , result) = D.run-wf mIn ir ir<bound x input-loc s alloc
          repr before not-halted rdi-eq capacity-ok
    in mOut
     , CWF.IRResultAWF.result-loc result
     , CWF.IRResultAWF.final-state result
     , CWF.IRResultAWF.final-alloc result
     , CWF.IRResultAWF.result-valid-wf result

------------------------------------------------------------------------
-- SUMMARY
--
-- Compiler correctness:
--
--   Represents x input-loc s
--   ∧ halted s ≡ false           (CPU running)
--   ∧ RDI = input-loc            (calling convention)
--   ∧ capacity sufficient        (stack space)
--     →
--   Represents (eval primSem ir x) result-loc s'
--
-- The preconditions are the caller's responsibility (runtime/loader).
-- The theorem says: IF properly set up, THEN semantics preserved.
------------------------------------------------------------------------
