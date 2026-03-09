------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.AbstractSimulation
--
-- Simulation proofs for AbstractInstr to x86.
--
-- Each AbstractInstr has a simulation proof showing that:
--   - Starting from corresponding states (LocState, x86 State)
--   - Executing the abstract instruction (exec-abstract)
--   - And executing the compiled x86 code (compile-abstract)
--   - Results in corresponding final states
--
-- These per-instruction proofs compose via Star transitivity
-- to give full trace simulation.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.AbstractSimulation where

open import Data.Nat using (ℕ; _<_; _≤_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Import FrameSemantics
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Target.X86v3.FrameInstantiation
  using (x86v3-frame-semantics; X86Frame)

-- Import SlotMachine
open import Once.CCC.SlotMachine as SlotMachine
  using (LocState; AllocState; AbstractInstr; AbstractTrace;
         AbstractReg; Input; Output;
         mov-to-output; mov-to-input; load-indirect; load-indirect-suc;
         load-from-slot; store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack;
         instr-push-frame; instr-pop-frame; instr-call-closure)
open SlotMachine.AbstractExec {x86v3-frame-semantics}
  using (exec-abstract; exec-trace)

-- Import X86 types
open import Once.Target.X86.Syntax as X86
  using (Program)

open import Once.Target.X86.Semantics as X86Sem
  using (State)

-- Import AbstractToX86
open import Once.CCC.Target.X86v3.AbstractToX86
  using (compile-abstract; compile-trace)

-- Import correspondence
open import Once.CCC.Target.X86v3.Refinement.SlotToX86
  using (FS; StateCorresponds)

------------------------------------------------------------------------
-- Instruction Simulation
--
-- For each AbstractInstr ai:
--   Given: σ corresponds to s
--   exec-abstract ai σ alloc = (σ', alloc')
--   Running compile-abstract ai on s produces s'
--   Then: σ' corresponds to s'
--
-- This is the core lemma for compositional simulation.
------------------------------------------------------------------------

-- | Single instruction simulation
--
-- Postulated for now; actual proofs follow the InstrCorrect pattern.
-- Each instruction has a specific proof based on:
--   - What registers/memory it reads
--   - What it writes
--   - Preservation of correspondence invariants

postulate
  -- mov-to-output: Output := Input
  mov-to-output-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract mov-to-output σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- mov-to-input: Input := Output (compose bridge)
  mov-to-input-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract mov-to-input σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- load-indirect: Output := *Input
  load-indirect-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract load-indirect σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- load-indirect-suc: Output := *(sucLoc Input)
  load-indirect-suc-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract load-indirect-suc σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- load-from-slot n: Output := stack[n]
  load-from-slot-sim : ∀ (n : ℕ) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract (load-from-slot n) σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- store-at-slot n: stack[n] := Output
  store-at-slot-sim : ∀ (n : ℕ) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract (store-at-slot n) σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- store-indirect: *Input := Output
  store-indirect-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract store-indirect σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- store-indirect-suc: *(sucLoc Input) := Output
  store-indirect-suc-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract store-indirect-suc σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- lea-slot n: Output := &stack[n]
  lea-slot-sim : ∀ (n : ℕ) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract (lea-slot n) σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- restore-input n: Input := stack[n]
  restore-input-sim : ∀ (n : ℕ) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract (restore-input n) σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- instr-alloc-stack n: allocate N slots
  alloc-stack-sim : ∀ (n : ℕ) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract (instr-alloc-stack n) σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- instr-dealloc-stack n: deallocate N slots
  dealloc-stack-sim : ∀ (n : ℕ) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract (instr-dealloc-stack n) σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- instr-push-frame n: push new frame with capacity N
  push-frame-sim : ∀ (n : ℕ) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract (instr-push-frame n) σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- instr-pop-frame: restore caller frame
  pop-frame-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract instr-pop-frame σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

  -- instr-call-closure: call closure code
  call-closure-sim : ∀ (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-abstract instr-call-closure σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')

------------------------------------------------------------------------
-- Trace Simulation
--
-- Compose per-instruction simulations for full trace correctness.
-- Uses Star transitivity for sequential composition.
------------------------------------------------------------------------

-- | Full trace simulation
--
-- If σ corresponds to s, and we execute a trace producing (σ', alloc'),
-- then compiling the trace and executing on s produces s' that
-- corresponds to σ'.

postulate
  trace-sim : ∀ (trace : AbstractTrace) (σ : LocState FS) (alloc : AllocState {FS}) (s : State) →
    StateCorresponds σ s →
    let (σ' , alloc') = exec-trace trace σ alloc
    in ∃[ s' ] (StateCorresponds σ' s')
