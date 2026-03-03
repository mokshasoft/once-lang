------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.IRRunnerTypes
--
-- Shared types for IR execution at the x86 level.
--
-- Contains:
--   - IRStarResult: Result type for offset-parameterized IR simulation
--   - IRRunner: Type for IR runners that work at any offset
--   - state-frame: Extract current frame from StateCorresponds
--   - compose-parent-preserved: Chain frame preservation through composition
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.IRRunnerTypes where

open import Data.Bool using (false)
open import Data.List using (_++_; length; [])
open import Data.List.Properties using (length-++)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Nat using (ℕ; suc; _<_; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open FrameSemantics using (Frame; _≺_)

open import Once.CCC.Target.X86v3.Types using (Type)
open import Once.CCC.IR using (IR)

-- Import Star combinators
open import Once.CCC.Target.X86.Correct.Star using (Star)

-- Import SlotMachine
open import Once.CCC.SlotMachine as SM using (LocState)

-- Instantiate with concrete x86v3 frame semantics
open import Once.CCC.Target.X86v3.FrameInstantiation
  using (x86v3-frame-semantics; X86Frame)

private
  FS' : FrameSemantics
  FS' = x86v3-frame-semantics

-- Import x86 semantics
open import Once.Target.X86.Semantics as X86Sem
  renaming (readReg to x86-readReg)
open X86Sem using (State)

open import Once.Target.X86.Syntax using (rbp; rsp; Program)

-- Import SlotToX86 for StateCorresponds and HeapBaseMap
open import Once.CCC.Target.X86v3.Refinement.SlotToX86 using (StateCorresponds; HeapBaseMap)
open StateCorresponds

-- Import CodeGen for compile-ir and compile-length
open import Once.CCC.Target.X86v3.CodeGen.Compile using (compile-ir; compile-length)

------------------------------------------------------------------------
-- IRStarResult: Result type for offset-parameterized IR simulation
--
-- The full program is: prefix ++ compile-ir ir ++ suffix
-- PC starts at (length prefix), ends at (length prefix + compile-length ir)
--
-- Key invariant: frame-matches-input ensures that:
--   current-frame = current-frame (input StateCorresponds)
-- This allows compose to chain frame preservation through f → bridge → g.
------------------------------------------------------------------------

record IRStarResult {A B : Type} (ir : IR A B)
                    (prefix suffix : Program) (σ-initial : LocState FS') (s : State)
                    (sc-input : StateCorresponds σ-initial s)
                    (s' : State) (offset : ℕ) : Set where
  field
    star-proof     : Star (prefix ++ compile-ir ir ++ suffix) s s'
    halted-false   : X86Sem.State.halted s' ≡ false
    pc-advanced    : X86Sem.State.pc s' ≡ offset +ℕ compile-length ir
    σ-final        : LocState FS'
    corr-proof     : StateCorresponds σ-final s'
    -- Frame preservation: rbp and rsp are callee-saved
    rbp-preserved  : x86-readReg (X86Sem.State.regs s') rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
    rsp-preserved  : x86-readReg (X86Sem.State.regs s') rsp ≡ x86-readReg (X86Sem.State.regs s) rsp
    -- Current frame for this IR execution
    current-frame  : Frame FS'
    -- Frame invariant: current-frame equals input's current-frame
    frame-matches-input : current-frame ≡ StateCorresponds.current-frame sc-input
    -- Output frame preserved
    output-frame-preserved : StateCorresponds.current-frame corr-proof ≡ StateCorresponds.current-frame sc-input
    -- Parent frame preservation (stack discipline)
    parent-frames-preserved : ∀ (f : Frame FS') (slot : ℕ) →
      _≺_ FS' current-frame f →
      SM.LocState.stackMem σ-final f slot ≡ SM.LocState.stackMem σ-initial f slot
    -- Heap-base preservation: IR execution doesn't allocate, so heap-base mapping is constant
    -- This is NOT an allocator property, but an IR execution property.
    heap-base-preserved : StateCorresponds.heap-base corr-proof ≡ StateCorresponds.heap-base sc-input

open IRStarResult public

------------------------------------------------------------------------
-- IRRunner: Type for offset-parameterized IR simulation
------------------------------------------------------------------------

IRRunner : ∀ {A B} → IR A B → Set
IRRunner {A} {B} ir = ∀ (prefix suffix : Program) (σ : LocState FS') (s : State) →
  (sc : StateCorresponds σ s) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  ∃[ s' ] IRStarResult ir prefix suffix σ s sc s' (length prefix)

------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

-- | Get current frame from StateCorresponds
state-frame : ∀ (σ : LocState FS') (s : State) → StateCorresponds σ s → Frame FS'
state-frame σ s sc = StateCorresponds.current-frame sc

-- | Compose parent-frames-preserved
-- When composing f and g, if g's frame is current-frame, parent frame preservation
-- chains through f → bridge → g.
compose-parent-preserved : ∀ (σ-init σ-mid σ-final : LocState FS')
  (frame : Frame FS') (slot : ℕ) (cf-f cf-g : Frame FS') →
  cf-f ≡ cf-g →
  _≺_ FS' cf-g frame →
  (∀ (f : Frame FS') (s : ℕ) → _≺_ FS' cf-f f → SM.LocState.stackMem σ-mid f s ≡ SM.LocState.stackMem σ-init f s) →
  (∀ (f : Frame FS') (s : ℕ) → _≺_ FS' cf-g f → SM.LocState.stackMem σ-final f s ≡ SM.LocState.stackMem σ-mid f s) →
  SM.LocState.stackMem σ-final frame slot ≡ SM.LocState.stackMem σ-init frame slot
compose-parent-preserved σ-init σ-mid σ-final frame slot cf-f cf-g cf-f≡cf-g cf-g≺frame pf-f pf-g =
  let step1 = pf-g frame slot cf-g≺frame
      cf-f≺frame : _≺_ FS' cf-f frame
      cf-f≺frame = subst (λ x → _≺_ FS' x frame) (sym cf-f≡cf-g) cf-g≺frame
      step2 = pf-f frame slot cf-f≺frame
  in trans step1 step2
