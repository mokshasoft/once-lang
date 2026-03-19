------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.SimulationInterface
--
-- Target-agnostic interface for simulation proofs.
--
-- This module defines what ANY target backend must provide to get
-- a complete simulation proof from AbstractInstr to target code.
--
-- KEY INSIGHT: The proofs should be TRIVIAL if:
--   1. Target execution mirrors exec-abstract structure (same with-patterns)
--   2. Correspondence relation is simple (register + memory mapping)
--   3. compile-abstract is 1-to-1 mapping
--
-- If proofs are hard, something is WRONG with the abstraction.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.SimulationInterface where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore

------------------------------------------------------------------------
-- The Simulation Interface
--
-- Any target backend must instantiate this record to get simulation proofs.
------------------------------------------------------------------------

record TargetSimulation {FS : FrameSemantics} : Set₁ where
  open FrameSemantics FS
  open MemOps {FS}
  open AbstractExec {FS}

  field
    ------------------------------------------------------------------------
    -- Target-specific types
    ------------------------------------------------------------------------

    -- The target machine state (registers + memory + halted flag)
    TargetState : Set

    -- Target instruction type
    TargetInstr : Set

    -- Extract halted flag from target state
    target-halted : TargetState → Bool

    ------------------------------------------------------------------------
    -- Target execution
    --
    -- CRITICAL: Must mirror exec-abstract's structure!
    -- - Same with-pattern structure for memory reads
    -- - Same halted behavior
    ------------------------------------------------------------------------

    -- Execute single target instruction
    exec-target : TargetInstr → TargetState → TargetState

    -- Execute program (list of instructions)
    exec-target-prog : List TargetInstr → TargetState → TargetState

    ------------------------------------------------------------------------
    -- Compilation
    --
    -- Must be 1-to-1 (or 1-to-few) mapping from AbstractInstr
    ------------------------------------------------------------------------

    -- Compile single abstract instruction to target instructions
    compile-instr : AbstractInstr → List TargetInstr

    -- Compile trace (should just be concat of compile-instr)
    compile-trace : AbstractTrace → List TargetInstr

    ------------------------------------------------------------------------
    -- Correspondence relation
    --
    -- Simple mapping between abstract and target state:
    --   - Input register ↔ target input register
    --   - Output register ↔ target output register
    --   - Frame pointer ↔ target frame register
    --   - Memory at location ↔ Memory at address
    ------------------------------------------------------------------------

    Corresponds : LocState FS → TargetState → AllocState {FS} → Set

    ------------------------------------------------------------------------
    -- The core simulation theorem
    --
    -- This is what each target must prove.
    -- With proper structure, this should be TRIVIAL (parallel with-patterns).
    ------------------------------------------------------------------------

    instr-simulation : ∀ (i : AbstractInstr)
                         (ls : LocState FS)
                         (ts : TargetState)
                         (alloc : AllocState {FS}) →
      halted ls ≡ false →
      Corresponds ls ts alloc →
      Corresponds (proj₁ (exec-abstract i ls alloc))
                  (exec-target-prog (compile-instr i) ts)
                  (proj₂ (exec-abstract i ls alloc))

    ------------------------------------------------------------------------
    -- Trace simulation
    --
    -- This follows from instr-simulation by induction.
    -- Each target proves this using its concrete definitions.
    ------------------------------------------------------------------------

    trace-simulation : ∀ (trace : AbstractTrace)
                         (ls : LocState FS)
                         (ts : TargetState)
                         (alloc : AllocState {FS}) →
      Corresponds ls ts alloc →
      Corresponds (proj₁ (exec-trace trace ls alloc))
                  (exec-target-prog (compile-trace trace) ts)
                  (proj₂ (exec-trace trace ls alloc))

------------------------------------------------------------------------
-- Usage guide for new targets:
--
-- 1. Define your TargetState, TargetInstr, exec-target, etc.
--
-- 2. Define Corresponds with these fields:
--    - input-reg-corresponds : target-input-reg ≡ loc-to-addr (Input)
--    - output-reg-corresponds : target-output-reg ≡ loc-to-addr (Output)
--    - frame-reg-corresponds : target-frame-reg ≡ frame-base (current-frame)
--    - mem-corresponds : abstract-mem loc ≡ just v → target-mem (addr loc) ≡ just (addr v)
--    - halted-corresponds : target-halted ≡ abstract-halted
--
-- 3. Prove instr-simulation by case analysis on AbstractInstr.
--    For each case:
--    a. Match on halted (handle contradiction cases)
--    b. For memory operations, use PARALLEL with-patterns:
--       with readLoc ls loc | target-mem ts (addr loc)
--    c. Use mem-corresponds to eliminate impossible cases
--    d. Build new correspondence using register/memory update lemmas
--
-- 4. Get trace-simulation for FREE!
------------------------------------------------------------------------
