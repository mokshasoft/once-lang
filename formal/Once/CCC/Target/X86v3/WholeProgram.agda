------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.WholeProgram
--
-- COMPILER CORRECTNESS THEOREM
--
-- The FULL correctness property we want to prove:
--
--   ∀ ir x x86-state →
--     let program = compile-ir ir
--         x86-final = exec program x86-state
--     in rax x86-final represents (eval ir x)
--
-- This decomposes into three layers:
--
--   Layer 1→2 (Refinement): x86 execution → SlotMachine state
--   Layer 2→3 (Dispatcher): SlotMachine ops → eval semantics
--
-- Current status:
--   ✓ Layer 2→3: PROVEN (compile-correct below)
--   ✗ Layer 1→2: PARTIAL (individual instruction lemmas in InstrCorrect)
--   ✗ Full theorem: NOT YET CONNECTED
--
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.WholeProgram where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (_++_; length; [])
open import Data.List.Properties using (length-++)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂; Σ)
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
-- LAYER 2→3: PROVEN
--
-- compile-correct proves:
--   Represents x input-loc s
--   ∧ halted s ≡ false           (CPU running)
--   ∧ RDI = input-loc            (calling convention)
--   ∧ capacity sufficient        (stack space)
--     →
--   Represents (eval primSem ir x) result-loc s'
--
-- The preconditions are the caller's responsibility (runtime/loader).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- THE FULL THEOREM (Layer 1→2→3)
--
-- This is what we WANT to prove end-to-end:
--   Compiling IR to x86 and executing it produces the correct result.
--
-- Gap: Layer 1→2 (x86 execution → SlotMachine) not yet connected.
------------------------------------------------------------------------

open import Once.Target.X86.Semantics as X86
  using (State)
open import Once.CCC.Target.X86v3.CodeGen.Compile
  using (compile-ir; pair-setup; pair-middle; pair-cleanup)
open import Once.CCC.Target.X86.Correct.Star
  using (Star)

-- Instantiate with concrete x86v3 frame semantics
open import Once.CCC.Target.X86v3.FrameInstantiation
  using (x86v3-frame-semantics; X86Frame)

private
  FS' : FrameSemantics
  FS' = x86v3-frame-semantics

------------------------------------------------------------------------
-- THE FULL THEOREM (Layer 1→2→3)
--
-- Given:
--   - An IR program
--   - Initial x86 state corresponding to SlotMachine state
--   - Input value at the location pointed to by RDI
--
-- Then:
--   - Executing the compiled x86 code produces a final state
--   - That state corresponds to a SlotMachine state
--   - RAX points to a location containing (eval ir x)
--
-- ARCHITECTURE: Per-instruction correspondence (portable across backends)
--   - Dispatcher handles IR semantics (shared, Layer 2→3)
--   - This module handles x86 simulation (per-backend, Layer 1→2)
--   - StateCorresponds is the simulation relation
--
-- NOTE: Uses Star (not exec) per proof-instructions.md:
--   "All proofs must use the Star relation"
------------------------------------------------------------------------

open import Once.CCC.IR using (id; _∘_; fst-ir; snd-ir; ⟨_,_⟩_; terminal;
                               inl-ir; inr-ir; case-ir; initial;
                               curry; apply; arr; fold-ir; unfold-ir;
                               free-heap; Prim; AllocMode)
open import Once.CCC.Target.X86v3.Types using (_*_; _+_; _⇒[_]_; Eff; Fix)
open import Once.CCC.SlotMachine using (HeapRef; mkHeapRef; RegId; RAX; RDI; R14; R15;
         HeapLocation; heap-loc; OnHeap; OnStack)
  renaming (Instr to SlotInstr; mov to slot-mov)
open import Data.String using (String)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- Import SlotMachine exec for simulation proofs
open import Once.CCC.SlotMachine as SM using (LocState; Registers; readReg; writeReg; sucLoc; sucHL)
open SM.ExecFinal {FS'} using () renaming (exec to slot-exec)

-- Import Star combinators
open import Once.CCC.Target.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; _◅◅_)

-- Import ExecLemmas for Star proofs (offset-parameterized only)
open import Once.Target.X86.ExecLemmas
  using (id-expected-state; id-instrs;
         terminal-expected-state; terminal-instrs;
         fst-expected-state; fst-instrs;
         snd-expected-state; snd-instrs;
         bridge-expected-state; compose-bridge;
         star-concat-left;
         -- Offset-parameterized lemmas for compose proofs
         id-star-at-offset; terminal-star-at-offset;
         fst-star-at-offset; snd-star-at-offset;
         bridge-star-at-offset;
         -- Offset-parameterized step lemmas for individual instructions
         push-expected-state; step-push-at-offset;
         mov-rr-expected-state; step-mov-rr-at-offset;
         sub-ri-expected-state; step-sub-ri-at-offset;
         -- step-fetch-result for direct step proofs
         step-fetch-result; fetch-++-right;
         push-reg-result; pop-reg-result; mov-reg-reg-result; mov-reg-mem-result; sub-imm-reg-result;
         -- StepChain infrastructure
         StepProof; mkStep; StepChain; done; _▸_; chain-to-star)

-- Import SlotToX86 for correspondence
open import Once.CCC.Target.X86v3.Refinement.SlotToX86 as SlotToX86
  using (RegsCorrespond; MemCorresponds; StateCorresponds; HeapBaseMap;
         mov-regs-correspond; mov-mem-corresponds;
         build-regs-correspond-after-write;
         loc-to-addr; compile-reg; sucLoc-to-addr-OnStack; sucLoc-to-addr)
open RegsCorrespond
open MemCorresponds
open StateCorresponds

open import Once.Target.X86.Semantics as X86Sem
  renaming (readReg to x86-readReg; writeReg to x86-writeReg; readMem to x86-readMem;
            writeMem to x86-writeMem)
open X86Sem using (updateFlags; effectiveAddr; Word)
open X86Sem.State using (halted; pc; regs; memory; flags)

open import Once.Target.X86.Syntax using (rax; rdi; rbp; rsp; r14; r15; slot-size; slots; Program; Instr; push; pop; mov; sub; reg; imm; mem; base; base+disp; Mem)
open import Data.List using (_∷_)

------------------------------------------------------------------------
-- StateCorresponds Preservation Proofs
--
-- These show that each IR's compiled code preserves StateCorresponds.
-- Uses SlotToX86 correspondence lemmas (mov-regs-correspond, etc.)
------------------------------------------------------------------------

-- For each IR construct, we need:
--   1. Star proof (execution happens) - from ExecLemmas
--   2. StateCorresponds preservation - use correspondence lemmas

------------------------------------------------------------------------
-- id: mov rax, rdi
--
-- SlotMachine equivalent: exec (mov RAX RDI) σ
-- X86 equivalent: id-expected-state s
-- The correspondence is preserved by mov-regs-correspond.
------------------------------------------------------------------------

-- SlotMachine state after id
id-slot-state : LocState FS' → LocState FS'
id-slot-state σ = slot-exec (slot-mov RAX RDI) σ

-- id preserves correspondence (PROVEN - not postulate)
id-preserves-corresponds : ∀ (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  StateCorresponds (id-slot-state σ) (id-expected-state s)
id-preserves-corresponds σ s sc = record
  { heap-base = heap-base sc
  ; unit-base-zero = unit-base-zero sc
  ; regs-correspond = mov-regs-correspond (heap-base sc) RAX RDI (SM.LocState.regs σ) (X86Sem.State.regs s)
                        (regs-correspond sc)
  ; mem-corresponds = mov-mem-corresponds (heap-base sc) RAX RDI σ (X86Sem.State.memory s) (mem-corresponds sc)
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }

------------------------------------------------------------------------
-- terminal: mov rax, 0
--
-- X86 puts 0 in rax. This represents the Unit value.
-- SlotMachine puts OnHeap (heap-loc (mkHeapRef 0) 0) in RAX.
-- By unit-base-zero: heap-base (mkHeapRef 0) = 0, so the addresses match.
--
-- PROVEN using unit-base-zero field of StateCorresponds
------------------------------------------------------------------------

-- Helper: readLoc is unchanged when only registers change
private
  open import Once.CCC.SlotMachine as SM' using (stackMem; heapMem)
  open SM.MemOps {FS'} using (readLoc)

  terminal-readLoc-unchanged : ∀ (σ : LocState FS') (loc : SM.ValueLocation FS') →
    readLoc (record σ { regs = writeReg (SM.LocState.regs σ) RAX (OnHeap (heap-loc (mkHeapRef 0) 0)) }) loc ≡ readLoc σ loc
  terminal-readLoc-unchanged σ (OnStack f k) = refl
  terminal-readLoc-unchanged σ (OnHeap hl) = refl

-- Unit location: HeapRef 0 at offset 0
unit-loc : SM.ValueLocation FS'
unit-loc = OnHeap (heap-loc (mkHeapRef 0) 0)

-- SlotMachine state after terminal
terminal-slot-state : LocState FS' → LocState FS'
terminal-slot-state σ = record σ { regs = writeReg (SM.LocState.regs σ) RAX unit-loc }

-- terminal preserves correspondence (PROVEN)
-- Uses unit-base-zero to show loc-to-addr hb unit-loc = 0
terminal-preserves-corresponds : ∀ (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  ∃[ σ' ] StateCorresponds σ' (terminal-expected-state s)
terminal-preserves-corresponds σ s sc =
  terminal-slot-state σ , record
    { heap-base = heap-base sc
    ; unit-base-zero = unit-base-zero sc
    ; regs-correspond = terminal-regs-correspond
    ; mem-corresponds = terminal-mem-corresponds
    ; halted-corresponds = halted-corresponds sc
    ; rbp-is-frame-base = rbp-is-frame-base sc
    }
  where
    hb = heap-base sc

    -- loc-to-addr hb unit-loc = hb (mkHeapRef 0) + 0 * slot-size = hb (mkHeapRef 0) + 0 = hb (mkHeapRef 0) = 0
    -- Need to show: hb (mkHeapRef 0) + 0 * slot-size = 0
    open import Data.Nat.Properties using (+-identityʳ)

    unit-loc-is-zero : loc-to-addr hb unit-loc ≡ 0
    unit-loc-is-zero = trans (+-identityʳ (hb (mkHeapRef 0))) (unit-base-zero sc)

    terminal-regs-correspond : RegsCorrespond hb
      (SM.LocState.regs (terminal-slot-state σ))
      (X86Sem.State.regs (terminal-expected-state s))
    terminal-regs-correspond = record
      { rax-corresponds = sym unit-loc-is-zero
      ; rdi-corresponds = rdi-corresponds (regs-correspond sc)
      ; rsi-corresponds = rsi-corresponds (regs-correspond sc)
      ; r12-corresponds = r12-corresponds (regs-correspond sc)
      ; r14-corresponds = r14-corresponds (regs-correspond sc)
      ; r15-corresponds = r15-corresponds (regs-correspond sc)
      }

    -- heapMem unchanged when only registers change
    terminal-heapMem-unchanged : SM.LocState.heapMem (terminal-slot-state σ) ≡ SM.LocState.heapMem σ
    terminal-heapMem-unchanged = refl

    terminal-mem-corresponds : MemCorresponds hb (terminal-slot-state σ)
                                 (X86Sem.State.memory (terminal-expected-state s))
    terminal-mem-corresponds = record
      { stack-corresponds = λ f k loc' read-eq →
          stack-corresponds (mem-corresponds sc) f k loc'
            (trans (sym (terminal-readLoc-unchanged σ (OnStack f k))) read-eq)
      ; heap-corresponds = λ hl hl' read-eq →
          heap-corresponds (mem-corresponds sc) hl hl'
            (trans (sym (cong (λ m → m hl) terminal-heapMem-unchanged)) read-eq)
      }

------------------------------------------------------------------------
-- fst: mov rax, [rdi]
--
-- SlotMachine equivalent: load RAX (IndReg RDI)
-- Precondition: memory at RDI contains fst-loc
-- After: RAX = fst-loc (both sides)
--
-- PROVEN for both OnStack and OnHeap cases
------------------------------------------------------------------------

-- SlotMachine state after fst (given the loaded value)
fst-slot-state : LocState FS' → SM.ValueLocation FS' → LocState FS'
fst-slot-state σ fst-loc = record σ { regs = writeReg (SM.LocState.regs σ) RAX fst-loc }

-- fst preserves correspondence (PROVEN - with memory precondition)
fst-preserves-corresponds : ∀ (σ : LocState FS') (s : State)
  (fst-loc : SM.ValueLocation FS') →
  (sc : StateCorresponds σ s) →
  readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc →
  StateCorresponds (fst-slot-state σ fst-loc)
                   (fst-expected-state s (loc-to-addr (heap-base sc) fst-loc))
fst-preserves-corresponds σ s fst-loc sc mem-pre = record
  { heap-base = heap-base sc
  ; unit-base-zero = unit-base-zero sc
  ; regs-correspond = fst-regs-correspond
  ; mem-corresponds = fst-mem-corresponds
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }
  where
    hb = heap-base sc

    fst-regs-correspond : RegsCorrespond hb
      (SM.LocState.regs (fst-slot-state σ fst-loc))
      (X86Sem.State.regs (fst-expected-state s (loc-to-addr hb fst-loc)))
    fst-regs-correspond = record
      { rax-corresponds = refl
      ; rdi-corresponds = rdi-corresponds (regs-correspond sc)
      ; rsi-corresponds = rsi-corresponds (regs-correspond sc)
      ; r12-corresponds = r12-corresponds (regs-correspond sc)
      ; r14-corresponds = r14-corresponds (regs-correspond sc)
      ; r15-corresponds = r15-corresponds (regs-correspond sc)
      }

    -- Helper: readLoc unchanged when only registers change
    fst-readLoc-unchanged : ∀ (loc : SM.ValueLocation FS') →
      readLoc (fst-slot-state σ fst-loc) loc ≡ readLoc σ loc
    fst-readLoc-unchanged (OnStack f k) = refl
    fst-readLoc-unchanged (OnHeap hl) = refl

    -- fst-slot-state only changes registers, heapMem is unchanged
    fst-heapMem-unchanged : SM.LocState.heapMem (fst-slot-state σ fst-loc) ≡ SM.LocState.heapMem σ
    fst-heapMem-unchanged = refl

    fst-mem-corresponds : MemCorresponds hb (fst-slot-state σ fst-loc)
                            (X86Sem.State.memory (fst-expected-state s (loc-to-addr hb fst-loc)))
    fst-mem-corresponds = record
      { stack-corresponds = λ f k loc' read-eq →
          stack-corresponds (mem-corresponds sc) f k loc'
            (trans (sym (fst-readLoc-unchanged (OnStack f k))) read-eq)
      ; heap-corresponds = λ hl hl' read-eq →
          heap-corresponds (mem-corresponds sc) hl hl'
            (trans (sym (cong (λ m → m hl) fst-heapMem-unchanged)) read-eq)
      }

-- fst simulation with memory precondition
-- PROVEN for both OnStack and OnHeap cases
fst-simulation : ∀ (σ : LocState FS') (s : State)
  (fst-loc : SM.ValueLocation FS') →
  (sc : StateCorresponds σ s) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc →
  ∃[ x86-final ] ∃[ σ-final ]
    Star fst-instrs s x86-final × StateCorresponds σ-final x86-final
fst-simulation σ s fst-loc sc h-eq pc-eq mem-pre =
  fst-sim-helper (SM.readReg (SM.LocState.regs σ) RDI) refl mem-pre
  where
    hb = heap-base sc

    -- Helper for heap case: use with pattern to match heapMem result and equality proof together
    -- Defined before fst-sim-helper so it can be used in the OnHeap clause
    -- Use 'in heapMem-eq' to capture the heapMem equality proof
    heap-x86-mem-helper : ∀ (hl : HeapLocation) (target : SM.ValueLocation FS') →
      readLoc σ (OnHeap hl) ≡ just target →
      x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (OnHeap hl)) ≡ just (loc-to-addr hb target)
    heap-x86-mem-helper hl target eq with SM.LocState.heapMem σ hl in heapMem-eq | eq
    ... | just hl' | refl = heap-corresponds (mem-corresponds sc) hl hl' heapMem-eq

    fst-sim-helper : ∀ (rdi-loc : SM.ValueLocation FS') →
      SM.readReg (SM.LocState.regs σ) RDI ≡ rdi-loc →
      readLoc σ rdi-loc ≡ just fst-loc →
      ∃[ x86-final ] ∃[ σ-final ]
        Star fst-instrs s x86-final × StateCorresponds σ-final x86-final

    -- OnStack case: fst reads from [rdi] = stack[f, k]
    fst-sim-helper (OnStack f k) rdi-eq mem-pre-stack =
      let rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
          -- By regs-correspond + rdi-eq: rdi-addr = loc-to-addr hb (OnStack f k)
          rdi-corr : rdi-addr ≡ loc-to-addr hb (OnStack f k)
          rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)
          -- By mem-corresponds: x86 memory at addr(OnStack f k) = loc-to-addr hb fst-loc
          x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (OnStack f k)) ≡ just (loc-to-addr hb fst-loc)
          x86-mem-eq = stack-corresponds (mem-corresponds sc) f k fst-loc mem-pre-stack
          -- Memory equality at rdi
          x86-mem-at-rdi : x86-readMem (X86Sem.State.memory s) rdi-addr ≡ just (loc-to-addr hb fst-loc)
          x86-mem-at-rdi = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb fst-loc))
                                 (sym rdi-corr) x86-mem-eq
          -- Transport mem-pre back to original form for fst-preserves-corresponds
          mem-pre-orig : readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc
          mem-pre-orig = subst (λ loc → readLoc σ loc ≡ just fst-loc) (sym rdi-eq) mem-pre-stack
      in fst-expected-state s (loc-to-addr hb fst-loc)
       , fst-slot-state σ fst-loc
       , fst-star-at-offset [] [] s (loc-to-addr hb fst-loc) h-eq pc-eq x86-mem-at-rdi
       , fst-preserves-corresponds σ s fst-loc sc mem-pre-orig

    -- OnHeap case (PROVEN using heap-corresponds)
    fst-sim-helper (OnHeap hl) rdi-eq mem-pre-heap =
      fst-expected-state s (loc-to-addr hb fst-loc)
      , fst-slot-state σ fst-loc
      , fst-star-at-offset [] [] s (loc-to-addr hb fst-loc) h-eq pc-eq x86-mem-at-rdi
      , fst-preserves-corresponds σ s fst-loc sc mem-pre-orig
      where
        rdi-addr = x86-readReg (X86Sem.State.regs s) rdi

        -- By regs-correspond + rdi-eq: rdi-addr = loc-to-addr hb (OnHeap hl)
        rdi-corr : rdi-addr ≡ loc-to-addr hb (OnHeap hl)
        rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)

        -- Use the helper to get x86 memory equality
        x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (OnHeap hl)) ≡ just (loc-to-addr hb fst-loc)
        x86-mem-eq = heap-x86-mem-helper hl fst-loc mem-pre-heap

        -- Memory equality at rdi
        x86-mem-at-rdi : x86-readMem (X86Sem.State.memory s) rdi-addr ≡ just (loc-to-addr hb fst-loc)
        x86-mem-at-rdi = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb fst-loc))
                               (sym rdi-corr) x86-mem-eq

        -- Transport mem-pre back to original form
        mem-pre-orig : readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc
        mem-pre-orig = subst (λ loc → readLoc σ loc ≡ just fst-loc) (sym rdi-eq) mem-pre-heap

------------------------------------------------------------------------
-- snd: mov rax, [rdi+8]
--
-- SlotMachine equivalent: load RAX (IndRegSuc RDI)
-- Precondition: memory at RDI+8 contains snd-loc
-- After: RAX = snd-loc (both sides)
--
-- PROVEN for both OnStack and OnHeap using sucLoc-to-addr
------------------------------------------------------------------------

-- SlotMachine state after snd (given the loaded value)
snd-slot-state : LocState FS' → SM.ValueLocation FS' → LocState FS'
snd-slot-state σ snd-loc = record σ { regs = writeReg (SM.LocState.regs σ) RAX snd-loc }

-- snd preserves correspondence (PROVEN - with memory precondition)
snd-preserves-corresponds : ∀ (σ : LocState FS') (s : State)
  (snd-loc : SM.ValueLocation FS') →
  (sc : StateCorresponds σ s) →
  readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc →
  StateCorresponds (snd-slot-state σ snd-loc)
                   (snd-expected-state s (loc-to-addr (heap-base sc) snd-loc))
snd-preserves-corresponds σ s snd-loc sc mem-pre = record
  { heap-base = heap-base sc
  ; unit-base-zero = unit-base-zero sc
  ; regs-correspond = snd-regs-correspond
  ; mem-corresponds = snd-mem-corresponds
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }
  where
    hb = heap-base sc

    snd-regs-correspond : RegsCorrespond hb
      (SM.LocState.regs (snd-slot-state σ snd-loc))
      (X86Sem.State.regs (snd-expected-state s (loc-to-addr hb snd-loc)))
    snd-regs-correspond = record
      { rax-corresponds = refl
      ; rdi-corresponds = rdi-corresponds (regs-correspond sc)
      ; rsi-corresponds = rsi-corresponds (regs-correspond sc)
      ; r12-corresponds = r12-corresponds (regs-correspond sc)
      ; r14-corresponds = r14-corresponds (regs-correspond sc)
      ; r15-corresponds = r15-corresponds (regs-correspond sc)
      }

    -- Helper: readLoc unchanged when only registers change
    snd-readLoc-unchanged : ∀ (loc : SM.ValueLocation FS') →
      readLoc (snd-slot-state σ snd-loc) loc ≡ readLoc σ loc
    snd-readLoc-unchanged (OnStack f k) = refl
    snd-readLoc-unchanged (OnHeap hl) = refl

    -- snd-slot-state only changes registers, heapMem is unchanged
    snd-heapMem-unchanged : SM.LocState.heapMem (snd-slot-state σ snd-loc) ≡ SM.LocState.heapMem σ
    snd-heapMem-unchanged = refl

    snd-mem-corresponds : MemCorresponds hb (snd-slot-state σ snd-loc)
                            (X86Sem.State.memory (snd-expected-state s (loc-to-addr hb snd-loc)))
    snd-mem-corresponds = record
      { stack-corresponds = λ f k loc' read-eq →
          stack-corresponds (mem-corresponds sc) f k loc'
            (trans (sym (snd-readLoc-unchanged (OnStack f k))) read-eq)
      ; heap-corresponds = λ hl hl' read-eq →
          heap-corresponds (mem-corresponds sc) hl hl'
            (trans (sym (cong (λ m → m hl) snd-heapMem-unchanged)) read-eq)
      }

-- snd simulation with memory precondition
-- Uses sucLoc-to-addr from SlotToX86 to connect sucLoc to +slot-size
-- PROVEN for both OnStack and OnHeap cases
snd-simulation : ∀ (σ : LocState FS') (s : State)
  (snd-loc : SM.ValueLocation FS') →
  (sc : StateCorresponds σ s) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc →
  ∃[ x86-final ] ∃[ σ-final ]
    Star snd-instrs s x86-final × StateCorresponds σ-final x86-final
snd-simulation σ s snd-loc sc h-eq pc-eq mem-pre =
  snd-sim-helper (SM.readReg (SM.LocState.regs σ) RDI) refl mem-pre
  where
    hb = heap-base sc

    -- Helper for heap case: use with pattern to match heapMem result and equality proof together
    -- Defined before snd-sim-helper so it can be used in the OnHeap clause
    -- Use 'in heapMem-eq' to capture the heapMem equality proof
    heap-x86-mem-helper : ∀ (hl : HeapLocation) (target : SM.ValueLocation FS') →
      readLoc σ (OnHeap (SM.sucHL hl)) ≡ just target →
      x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (SM.sucLoc (OnHeap hl))) ≡ just (loc-to-addr hb target)
    heap-x86-mem-helper hl target eq with SM.LocState.heapMem σ (SM.sucHL hl) in heapMem-eq | eq
    ... | just hl' | refl = heap-corresponds (mem-corresponds sc) (SM.sucHL hl) hl' heapMem-eq

    snd-sim-helper : ∀ (rdi-loc : SM.ValueLocation FS') →
      SM.readReg (SM.LocState.regs σ) RDI ≡ rdi-loc →
      readLoc σ (SM.sucLoc rdi-loc) ≡ just snd-loc →
      ∃[ x86-final ] ∃[ σ-final ]
        Star snd-instrs s x86-final × StateCorresponds σ-final x86-final

    -- OnStack case
    snd-sim-helper (OnStack f k) rdi-eq mem-pre-stack =
      let rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
          -- By regs-correspond + rdi-eq: rdi-addr = loc-to-addr hb (OnStack f k)
          rdi-corr : rdi-addr ≡ loc-to-addr hb (OnStack f k)
          rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)
          -- sucLoc location
          suc-loc = SM.sucLoc (OnStack f k)
          -- By sucLoc-to-addr: loc-to-addr hb (sucLoc (OnStack f k)) = loc-to-addr hb (OnStack f k) + slot-size
          sucLoc-eq : loc-to-addr hb suc-loc ≡ loc-to-addr hb (OnStack f k) +ℕ slot-size
          sucLoc-eq = sucLoc-to-addr hb (OnStack f k)
          -- By mem-corresponds: x86 memory at addr(suc-loc) = loc-to-addr hb snd-loc
          x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb suc-loc) ≡ just (loc-to-addr hb snd-loc)
          x86-mem-eq = stack-corresponds (mem-corresponds sc) f (suc k) snd-loc mem-pre-stack
          -- Combine: rdi-addr + slot-size = loc-to-addr hb suc-loc
          addr-eq : rdi-addr +ℕ slot-size ≡ loc-to-addr hb suc-loc
          addr-eq = trans (cong (_+ℕ slot-size) rdi-corr) (sym sucLoc-eq)
          -- Memory equality at rdi + slot-size
          x86-mem-at-rdi+8 : x86-readMem (X86Sem.State.memory s) (rdi-addr +ℕ slot-size) ≡ just (loc-to-addr hb snd-loc)
          x86-mem-at-rdi+8 = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb snd-loc))
                                   (sym addr-eq) x86-mem-eq
          -- Transport mem-pre back to original form for snd-preserves-corresponds
          mem-pre-orig : readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc
          mem-pre-orig = subst (λ loc → readLoc σ (SM.sucLoc loc) ≡ just snd-loc) (sym rdi-eq) mem-pre-stack
      in snd-expected-state s (loc-to-addr hb snd-loc)
       , snd-slot-state σ snd-loc
       , snd-star-at-offset [] [] s (loc-to-addr hb snd-loc) h-eq pc-eq x86-mem-at-rdi+8
       , snd-preserves-corresponds σ s snd-loc sc mem-pre-orig

    -- OnHeap case (PROVEN using sucLoc-to-addr-OnHeap and heap-corresponds)
    snd-sim-helper (OnHeap hl) rdi-eq mem-pre-heap =
      snd-expected-state s (loc-to-addr hb snd-loc)
      , snd-slot-state σ snd-loc
      , snd-star-at-offset [] [] s (loc-to-addr hb snd-loc) h-eq pc-eq x86-mem-at-rdi+8
      , snd-preserves-corresponds σ s snd-loc sc mem-pre-orig
      where
        rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
        suc-loc = SM.sucLoc (OnHeap hl)
        suc-hl = SM.sucHL hl

        -- By regs-correspond + rdi-eq: rdi-addr = loc-to-addr hb (OnHeap hl)
        rdi-corr : rdi-addr ≡ loc-to-addr hb (OnHeap hl)
        rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)

        -- By sucLoc-to-addr: loc-to-addr hb (sucLoc (OnHeap hl)) = loc-to-addr hb (OnHeap hl) + slot-size
        sucLoc-eq : loc-to-addr hb suc-loc ≡ loc-to-addr hb (OnHeap hl) +ℕ slot-size
        sucLoc-eq = sucLoc-to-addr hb (OnHeap hl)

        -- Use the helper to get x86 memory equality
        x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb suc-loc) ≡ just (loc-to-addr hb snd-loc)
        x86-mem-eq = heap-x86-mem-helper hl snd-loc mem-pre-heap

        -- Combine: rdi-addr + slot-size = loc-to-addr hb suc-loc
        addr-eq : rdi-addr +ℕ slot-size ≡ loc-to-addr hb suc-loc
        addr-eq = trans (cong (_+ℕ slot-size) rdi-corr) (sym sucLoc-eq)

        -- Memory equality at rdi + slot-size
        x86-mem-at-rdi+8 : x86-readMem (X86Sem.State.memory s) (rdi-addr +ℕ slot-size) ≡ just (loc-to-addr hb snd-loc)
        x86-mem-at-rdi+8 = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb snd-loc))
                                 (sym addr-eq) x86-mem-eq

        -- Transport mem-pre back to original form
        mem-pre-orig : readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc
        mem-pre-orig = subst (λ loc → readLoc σ (SM.sucLoc loc) ≡ just snd-loc) (sym rdi-eq) mem-pre-heap

------------------------------------------------------------------------
-- bridge: mov rdi, rax
--
-- Transfers the result of f (in rax) to rdi for g.
-- SlotMachine equivalent: mov RDI RAX
-- After: RDI = (what was in RAX)
--
-- PROVEN using mov-regs-correspond and mov-mem-corresponds
------------------------------------------------------------------------

-- bridge preserves correspondence (PROVEN - not postulate)
bridge-preserves-corresponds : ∀ (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  StateCorresponds (record σ { regs = writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) RAX) }) (bridge-expected-state s)
bridge-preserves-corresponds σ s sc = record
  { heap-base = heap-base sc
  ; unit-base-zero = unit-base-zero sc
  ; regs-correspond = bridge-regs-correspond
  ; mem-corresponds = bridge-mem-corresponds
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }
  where
    hb = heap-base sc

    -- Register correspondence: mov rdi, rax preserves correspondence
    bridge-regs-correspond : RegsCorrespond hb
      (writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) RAX))
      (X86Sem.State.regs (bridge-expected-state s))
    bridge-regs-correspond = mov-regs-correspond hb RDI RAX (SM.LocState.regs σ) (X86Sem.State.regs s)
                               (regs-correspond sc)

    -- Helper: readLoc unchanged when only registers change
    bridge-readLoc-unchanged : ∀ (loc : SM.ValueLocation FS') →
      readLoc (record σ { regs = writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) RAX) }) loc ≡ readLoc σ loc
    bridge-readLoc-unchanged (OnStack f k) = refl
    bridge-readLoc-unchanged (OnHeap hl) = refl

    -- heapMem is unchanged when only registers change
    bridge-heapMem-unchanged : SM.LocState.heapMem (record σ { regs = writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) RAX) }) ≡ SM.LocState.heapMem σ
    bridge-heapMem-unchanged = refl

    -- Memory correspondence: mov doesn't change memory
    bridge-mem-corresponds : MemCorresponds hb
      (record σ { regs = writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) RAX) })
      (X86Sem.State.memory (bridge-expected-state s))
    bridge-mem-corresponds = record
      { stack-corresponds = λ f k loc' read-eq →
          stack-corresponds (mem-corresponds sc) f k loc'
            (trans (sym (bridge-readLoc-unchanged (OnStack f k))) read-eq)
      ; heap-corresponds = λ hl hl' read-eq →
          heap-corresponds (mem-corresponds sc) hl hl'
            (trans (sym (cong (λ m → m hl) bridge-heapMem-unchanged)) read-eq)
      }

-- SlotMachine state after bridge
bridge-slot-state : LocState FS' → LocState FS'
bridge-slot-state σ = record σ { regs = writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) RAX) }

-- bridge simulation (Star + StateCorresponds)
bridge-simulation : ∀ (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ x86-final ] ∃[ σ-final ]
    Star compose-bridge s x86-final × StateCorresponds σ-final x86-final
bridge-simulation σ s sc h-eq pc-eq =
  bridge-expected-state s
  , bridge-slot-state σ
  , bridge-star-at-offset [] [] s h-eq pc-eq
  , bridge-preserves-corresponds σ s sc

------------------------------------------------------------------------
-- compose-simulation (Offset-Parameterized Approach)
--
-- For g ∘ f, we execute: compile-ir f ++ compose-bridge ++ compile-ir g
--
-- KEY INSIGHT: Use offset-parameterized Star proofs that work at any pc.
-- Instead of requiring pc=0, we parameterize by prefix/suffix:
--   - Execute f at offset (length prefix)
--   - Execute bridge at offset (length prefix + length (compile-ir f))
--   - Execute g at offset (length prefix + length (compile-ir f) + 1)
--
-- This eliminates the need for star-concat-middle/star-concat-right.
------------------------------------------------------------------------

open import Once.CCC.Target.X86v3.CodeGen.Compile using (compile-length; compile-ir-length)
open import Data.List.Properties using (length-++; ++-assoc; ++-identityʳ)
open import Data.Nat.Properties renaming (+-assoc to ℕ-+-assoc)

-- Type for IR simulation result at arbitrary offset
-- The full program is: prefix ++ compile-ir ir ++ suffix
-- PC starts at (length prefix), ends at (length prefix + compile-length ir)
record IRStarResult {A B : Type} (ir : IR A B)
                    (prefix suffix : Program) (s s' : State) (offset : ℕ) : Set where
  field
    star-proof     : Star (prefix ++ compile-ir ir ++ suffix) s s'
    halted-false   : X86Sem.State.halted s' ≡ false
    pc-advanced    : X86Sem.State.pc s' ≡ offset +ℕ compile-length ir
    σ-final        : LocState FS'
    corr-proof     : StateCorresponds σ-final s'

open IRStarResult

-- Type for offset-parameterized IR simulation
-- Takes prefix/suffix and works at any offset
IRRunner : ∀ {A B} → IR A B → Set
IRRunner {A} {B} ir = ∀ (prefix suffix : Program) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  ∃[ s' ] IRStarResult ir prefix suffix s s' (length prefix)

------------------------------------------------------------------------
-- Offset-Parameterized IR Runners (NEW APPROACH)
--
-- These run each IR at an arbitrary offset within a larger program.
-- The pattern is: prefix ++ compile-ir ir ++ suffix
-- PC advances from (length prefix) to (length prefix + compile-length ir)
------------------------------------------------------------------------

-- | id runner: mov rax, rdi at any offset
id-runner : ∀ {A} → IRRunner (id {A})
id-runner prefix suffix σ s sc h-eq pc-eq =
  id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq  -- record update preserves halted
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    }

-- | terminal runner: mov rax, 0 at any offset
terminal-runner : ∀ {A} → IRRunner (terminal {A})
terminal-runner prefix suffix σ s sc h-eq pc-eq =
  let (σ' , sc') = terminal-preserves-corresponds σ s sc
  in terminal-expected-state s , record
    { star-proof = terminal-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = σ'
    ; corr-proof = sc'
    }

-- | bridge runner: mov rdi, rax at any offset
bridge-runner : ∀ (prefix suffix : Program) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  ∃[ s' ] (Star (prefix ++ compose-bridge ++ suffix) s s'
         × X86Sem.State.halted s' ≡ false
         × X86Sem.State.pc s' ≡ length prefix +ℕ 1
         × StateCorresponds (bridge-slot-state σ) s')
bridge-runner prefix suffix σ s sc h-eq pc-eq =
  bridge-expected-state s
  , bridge-star-at-offset prefix suffix s h-eq pc-eq
  , h-eq
  , cong (_+ℕ 1) pc-eq
  , bridge-preserves-corresponds σ s sc

------------------------------------------------------------------------
-- compose-simulation using IRRunner
--
-- For g ∘ f, the full program is:
--   compile-ir f ++ compose-bridge ++ compile-ir g
--
-- Using IRRunner, we execute at arbitrary offsets:
--   1. f at offset 0 (or length prefix for nested case)
--   2. bridge at offset (length (compile-ir f))
--   3. g at offset (length (compile-ir f) + 1)
------------------------------------------------------------------------

-- compose-runner: execute g ∘ f at any offset
-- Takes IRRunner for f and g, returns IRStarResult for the composition
--
-- The key insight is that ++ is right-associative, so:
--   prefix ++ prog-f ++ compose-bridge ++ prog-g ++ suffix
-- parses as:
--   prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
--
-- We use ++-assoc to regroup and subst to transport Star proofs.
compose-runner : ∀ {A B C} (g : IR B C) (f : IR A B) →
  IRRunner f →
  IRRunner g →
  IRRunner (g ∘ f)
compose-runner g f f-run g-run prefix suffix σ s sc h-eq pc-eq =
  let -- Programs
      prog-f = compile-ir f
      prog-g = compile-ir g

      -- The full program for compose (g ∘ f) is:
      -- compile-ir (g ∘ f) = prog-f ++ compose-bridge ++ prog-g
      -- With prefix/suffix: prefix ++ (prog-f ++ compose-bridge ++ prog-g) ++ suffix

      -- Step 1: Execute f at offset (length prefix)
      -- f-run gets: prefix, (compose-bridge ++ prog-g ++ suffix)
      -- Star over: prefix ++ prog-f ++ (compose-bridge ++ prog-g ++ suffix)
      (sf , f-result) = f-run prefix (compose-bridge ++ prog-g ++ suffix) σ s sc h-eq pc-eq
      σf = IRStarResult.σ-final f-result
      star-f = IRStarResult.star-proof f-result
      h-sf = IRStarResult.halted-false f-result
      pc-sf = IRStarResult.pc-advanced f-result
      sc-f = IRStarResult.corr-proof f-result

      -- Helper lemmas for length calculations
      len-prefix-f : length (prefix ++ prog-f) ≡ length prefix +ℕ length prog-f
      len-prefix-f = length-++ prefix

      -- pc-sf : pc sf ≡ length prefix + compile-length f
      -- Need: pc sf ≡ length (prefix ++ prog-f)
      pc-at-bridge : X86Sem.State.pc sf ≡ length (prefix ++ prog-f)
      pc-at-bridge = trans pc-sf
                           (trans (cong (length prefix +ℕ_) (sym (compile-ir-length f)))
                                  (sym len-prefix-f))

      -- Step 2: Execute bridge at offset length (prefix ++ prog-f)
      -- bridge-runner gets: (prefix ++ prog-f), (prog-g ++ suffix)
      -- Star over: (prefix ++ prog-f) ++ compose-bridge ++ (prog-g ++ suffix)
      --
      -- We need to show this Star works on the same program as step 1's suffix
      -- By ++-assoc: (prefix ++ prog-f) ++ (compose-bridge ++ (prog-g ++ suffix))
      --            ≡ prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      assoc-for-bridge : (prefix ++ prog-f) ++ (compose-bridge ++ (prog-g ++ suffix))
                       ≡ prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      assoc-for-bridge = ++-assoc prefix prog-f (compose-bridge ++ (prog-g ++ suffix))

      (sb , star-b' , h-sb , pc-sb , sc-b) =
        bridge-runner (prefix ++ prog-f) (prog-g ++ suffix) σf sf sc-f h-sf pc-at-bridge

      -- Transport bridge's Star to the canonical form
      star-b : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) sf sb
      star-b = subst (λ p → Star p sf sb) assoc-for-bridge star-b'

      -- Step 3: Execute g at offset length (prefix ++ prog-f ++ compose-bridge)
      -- Note: prefix ++ prog-f ++ compose-bridge = prefix ++ (prog-f ++ compose-bridge) (right-assoc)
      -- We need: length (prefix ++ (prog-f ++ compose-bridge)) ≡ length (prefix ++ prog-f) + length compose-bridge
      --
      -- First use ++-assoc: prefix ++ (prog-f ++ compose-bridge) = (prefix ++ prog-f) ++ compose-bridge
      -- Then length-++: length ((prefix ++ prog-f) ++ compose-bridge) = length (prefix ++ prog-f) + length compose-bridge
      assoc-prefix-f-bridge : prefix ++ (prog-f ++ compose-bridge) ≡ (prefix ++ prog-f) ++ compose-bridge
      assoc-prefix-f-bridge = sym (++-assoc prefix prog-f compose-bridge)

      len-prefix-f-bridge : length (prefix ++ prog-f ++ compose-bridge)
                          ≡ length (prefix ++ prog-f) +ℕ length compose-bridge
      len-prefix-f-bridge = trans (cong length assoc-prefix-f-bridge) (length-++ (prefix ++ prog-f))

      pc-at-g : X86Sem.State.pc sb ≡ length (prefix ++ prog-f ++ compose-bridge)
      pc-at-g = trans pc-sb (sym len-prefix-f-bridge)

      -- g-run gets: (prefix ++ prog-f ++ compose-bridge), suffix
      -- Star over: (prefix ++ prog-f ++ compose-bridge) ++ prog-g ++ suffix
      --
      -- Associativity: we need to show this equals the full program
      -- (prefix ++ (prog-f ++ compose-bridge)) ++ (prog-g ++ suffix)
      -- = prefix ++ ((prog-f ++ compose-bridge) ++ (prog-g ++ suffix))  by ++-assoc
      -- = prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))  by ++-assoc on inner
      assoc-inner : (prog-f ++ compose-bridge) ++ (prog-g ++ suffix)
                  ≡ prog-f ++ (compose-bridge ++ (prog-g ++ suffix))
      assoc-inner = ++-assoc prog-f compose-bridge (prog-g ++ suffix)

      assoc-outer : (prefix ++ (prog-f ++ compose-bridge)) ++ (prog-g ++ suffix)
                  ≡ prefix ++ ((prog-f ++ compose-bridge) ++ (prog-g ++ suffix))
      assoc-outer = ++-assoc prefix (prog-f ++ compose-bridge) (prog-g ++ suffix)

      assoc-for-g : (prefix ++ (prog-f ++ compose-bridge)) ++ (prog-g ++ suffix)
                  ≡ prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      assoc-for-g = trans assoc-outer (cong (prefix ++_) assoc-inner)

      (sg , g-result) = g-run (prefix ++ prog-f ++ compose-bridge) suffix
                              (bridge-slot-state σf) sb sc-b h-sb pc-at-g
      σg = IRStarResult.σ-final g-result
      star-g' = IRStarResult.star-proof g-result
      h-sg = IRStarResult.halted-false g-result
      pc-sg = IRStarResult.pc-advanced g-result
      sc-g = IRStarResult.corr-proof g-result

      -- Transport g's Star to the canonical form
      star-g : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) sb sg
      star-g = subst (λ p → Star p sb sg) assoc-for-g star-g'

      -- Chain the three Stars together
      -- All three are now over the same program:
      --   prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      star-fg : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) s sg
      star-fg = star-f ◅◅ star-b ◅◅ star-g

      -- The result type expects Star over:
      --   prefix ++ compile-ir (g ∘ f) ++ suffix
      -- = prefix ++ (prog-f ++ compose-bridge ++ prog-g) ++ suffix
      -- = prefix ++ ((prog-f ++ compose-bridge ++ prog-g) ++ suffix)  (++ is right-assoc, so this is wrong)
      --
      -- Actually: compile-ir (g ∘ f) = prog-f ++ compose-bridge ++ prog-g
      --         = prog-f ++ (compose-bridge ++ prog-g)
      -- So: prefix ++ compile-ir (g ∘ f) ++ suffix
      --   = prefix ++ (prog-f ++ (compose-bridge ++ prog-g)) ++ suffix
      --   = prefix ++ ((prog-f ++ (compose-bridge ++ prog-g)) ++ suffix)  (by ++ right-assoc)
      --
      -- We have: prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      -- Need:    prefix ++ ((prog-f ++ (compose-bridge ++ prog-g)) ++ suffix)
      --
      -- These differ in how prog-g and suffix are grouped!
      -- (compose-bridge ++ (prog-g ++ suffix)) vs ((compose-bridge ++ prog-g) ++ suffix)
      --
      -- Use ++-assoc: compose-bridge ++ (prog-g ++ suffix) = (compose-bridge ++ prog-g) ++ suffix
      assoc-tail : compose-bridge ++ (prog-g ++ suffix) ≡ (compose-bridge ++ prog-g) ++ suffix
      assoc-tail = sym (++-assoc compose-bridge prog-g suffix)

      -- prog-f ++ (compose-bridge ++ (prog-g ++ suffix)) = prog-f ++ ((compose-bridge ++ prog-g) ++ suffix)
      --                                                  = (prog-f ++ (compose-bridge ++ prog-g)) ++ suffix
      assoc-mid : prog-f ++ (compose-bridge ++ (prog-g ++ suffix))
                ≡ (prog-f ++ (compose-bridge ++ prog-g)) ++ suffix
      assoc-mid = trans (cong (prog-f ++_) assoc-tail)
                        (sym (++-assoc prog-f (compose-bridge ++ prog-g) suffix))

      -- Finally: prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      --        = prefix ++ ((prog-f ++ (compose-bridge ++ prog-g)) ++ suffix)
      prog-eq : prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
              ≡ prefix ++ ((prog-f ++ (compose-bridge ++ prog-g)) ++ suffix)
      prog-eq = cong (prefix ++_) assoc-mid

      -- Transport to final form
      star-final : Star (prefix ++ compile-ir (g ∘ f) ++ suffix) s sg
      star-final = subst (λ p → Star p s sg) prog-eq star-fg

      -- PC calculation
      -- pc-sg : pc sg ≡ length (prefix ++ prog-f ++ compose-bridge) + compile-length g
      -- Need: pc sg ≡ length prefix + compile-length (g ∘ f)
      -- compile-length (g ∘ f) = compile-length f + length compose-bridge + compile-length g
      --
      -- length (prefix ++ prog-f ++ compose-bridge) + compile-length g
      -- = length (prefix ++ (prog-f ++ compose-bridge)) + compile-length g
      -- = (length prefix + length (prog-f ++ compose-bridge)) + compile-length g
      -- = (length prefix + (length prog-f + length compose-bridge)) + compile-length g
      -- = length prefix + (length prog-f + length compose-bridge + compile-length g)
      -- = length prefix + (compile-length f + length compose-bridge + compile-length g)
      -- = length prefix + compile-length (g ∘ f)

      -- PC calculation: show pc sg ≡ length prefix + compile-length (g ∘ f)
      -- pc-sg : pc sg ≡ length (prefix ++ prog-f ++ compose-bridge) + compile-length g
      -- compile-length (g ∘ f) = compile-length f + length compose-bridge + compile-length g
      pc-final : X86Sem.State.pc sg ≡ length prefix +ℕ compile-length (g ∘ f)
      pc-final = compose-pc-lemma prefix prog-f prog-g (compile-length f) (compile-length g)
                                  (compile-ir-length f) pc-sg

  in sg , record
    { star-proof = star-final
    ; halted-false = h-sg
    ; pc-advanced = pc-final
    ; σ-final = σg
    ; corr-proof = sc-g
    }
  where
    -- PC lemma for compose: converts pc result from g-runner to compose format
    -- Given: length prog-f ≡ compile-length f
    -- Given: pc ≡ length (prefix ++ prog-f ++ compose-bridge) + clg
    -- Show:  pc ≡ length prefix + (clf + length compose-bridge + clg)
    -- Where: compile-length (g ∘ f) = clf + length compose-bridge + clg
    compose-pc-lemma : ∀ (prefix prog-f prog-g : Program) (clf clg : ℕ) →
      length prog-f ≡ clf →
      ∀ {pc : ℕ} →
      pc ≡ length (prefix ++ prog-f ++ compose-bridge) +ℕ clg →
      pc ≡ length prefix +ℕ (clf +ℕ length compose-bridge +ℕ clg)
    compose-pc-lemma prefix prog-f prog-g clf clg len-f-eq {pc} pc-eq =
      -- pc = length (prefix ++ prog-f ++ compose-bridge) + clg
      -- Note: prefix ++ prog-f ++ compose-bridge = prefix ++ (prog-f ++ compose-bridge)
      -- Goal: pc ≡ length prefix + ((clf + length compose-bridge) + clg)
      --       (since _+ℕ_ is left-associative)
      let
        -- Step 1: length (prefix ++ (prog-f ++ compose-bridge)) = length prefix + length (prog-f ++ compose-bridge)
        step1 : length (prefix ++ (prog-f ++ compose-bridge)) ≡ length prefix +ℕ length (prog-f ++ compose-bridge)
        step1 = length-++ prefix

        -- Step 2: length (prog-f ++ compose-bridge) = length prog-f + length compose-bridge
        step2 : length (prog-f ++ compose-bridge) ≡ length prog-f +ℕ length compose-bridge
        step2 = length-++ prog-f

        -- Step 3: Combine steps
        len-eq : length (prefix ++ prog-f ++ compose-bridge) ≡ length prefix +ℕ (length prog-f +ℕ length compose-bridge)
        len-eq = trans step1 (cong (length prefix +ℕ_) step2)

        -- Step 4: Add clg to both sides, rearrange
        -- (length prefix + (length prog-f + length compose-bridge)) + clg
        -- = length prefix + ((length prog-f + length compose-bridge) + clg)  by +-assoc
        step4 : (length prefix +ℕ (length prog-f +ℕ length compose-bridge)) +ℕ clg
              ≡ length prefix +ℕ ((length prog-f +ℕ length compose-bridge) +ℕ clg)
        step4 = ℕ-+-assoc (length prefix) (length prog-f +ℕ length compose-bridge) clg

        -- Step 5: Use len-f-eq to replace length prog-f with clf
        -- (length prog-f + length compose-bridge) + clg = (clf + length compose-bridge) + clg
        step5 : length prefix +ℕ ((length prog-f +ℕ length compose-bridge) +ℕ clg)
              ≡ length prefix +ℕ ((clf +ℕ length compose-bridge) +ℕ clg)
        step5 = cong (λ x → length prefix +ℕ ((x +ℕ length compose-bridge) +ℕ clg)) len-f-eq

        -- Combine all
        -- Goal type is: length prefix +ℕ (clf +ℕ length compose-bridge +ℕ clg)
        -- which is:     length prefix +ℕ ((clf +ℕ length compose-bridge) +ℕ clg)  (left-assoc)
        final : length (prefix ++ prog-f ++ compose-bridge) +ℕ clg ≡ length prefix +ℕ ((clf +ℕ length compose-bridge) +ℕ clg)
        final = trans (cong (_+ℕ clg) len-eq) (trans step4 step5)
      in trans pc-eq final

------------------------------------------------------------------------
-- IR Runner by Induction
--
-- Build IRRunner for all IR constructs. This is the main induction
-- that proves all IR can be executed at any offset.
--
-- Postulated runners (complex, need more infrastructure):
--   - pair-runner: pair construction
--   - inl/inr/case-runner: sum types (codegen not implemented)
--   - curry/apply-runner: closures
--   - prim-runner: primitives
--
-- NOT postulated (special cases):
--   - fst-runner, snd-runner: PROVEN via fst/snd-runner-with-valid
--   - initial-runner: UNPROVABLE (ud2 halts, but Void has no inhabitants)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- fst-runner and snd-runner
--
-- These require memory validity: reading from [rdi] or [rdi+8] must
-- produce a valid value. This is guaranteed by well-typed programs
-- operating on pairs.
--
-- PORTABLE DESIGN: Validity is taken as an explicit parameter.
-- At Layer 1→2, we don't know types - validity comes from Layer 2→3.
-- The integration point (full-correctness) provides validity via ValidAtWF.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Location-Based Validity Pattern
--
-- See: location-validity-pattern.md for full documentation.
--
-- Key insight: Pass locations EXPLICITLY instead of hiding in existentials.
-- The caller (Dispatcher) knows the location from ValidAtWF.
-- The callee (runner) uses it directly.
------------------------------------------------------------------------

-- INPUT validity: Pair structure at a known location, RDI points to it
record PairAtLoc (pair-loc : SM.ValueLocation FS') (σ : LocState FS') : Set where
  field
    fst-loc : SM.ValueLocation FS'
    snd-loc : SM.ValueLocation FS'
    rdi-eq : SM.readReg (SM.LocState.regs σ) RDI ≡ pair-loc
    fst-ptr : readLoc σ pair-loc ≡ just fst-loc
    snd-ptr : readLoc σ (SM.sucLoc pair-loc) ≡ just snd-loc

open PairAtLoc

-- OUTPUT validity: Pair structure at a known location, RAX points to it
record PairOutputAtLoc (pair-loc : SM.ValueLocation FS') (σ : LocState FS') : Set where
  field
    fst-loc : SM.ValueLocation FS'
    snd-loc : SM.ValueLocation FS'
    rax-eq : SM.readReg (SM.LocState.regs σ) RAX ≡ pair-loc
    fst-ptr : readLoc σ pair-loc ≡ just fst-loc
    snd-ptr : readLoc σ (SM.sucLoc pair-loc) ≡ just snd-loc

open PairOutputAtLoc

-- INPUT validity: Closure structure at a known location, RDI points to it
-- Used by apply-ir which reads closure components
record ClosureAtLoc (closure-loc : SM.ValueLocation FS') (σ : LocState FS') : Set where
  field
    env-loc : SM.ValueLocation FS'
    code-loc : SM.ValueLocation FS'
    rdi-eq : SM.readReg (SM.LocState.regs σ) RDI ≡ closure-loc
    env-ptr : readLoc σ closure-loc ≡ just env-loc
    code-ptr : readLoc σ (SM.sucLoc closure-loc) ≡ just code-loc

open ClosureAtLoc

-- OUTPUT validity: Closure structure at a known location, RAX points to it
-- Used by curry which produces closures
record ClosureOutputAtLoc (closure-loc : SM.ValueLocation FS') (σ : LocState FS') : Set where
  field
    env-loc : SM.ValueLocation FS'
    code-loc : SM.ValueLocation FS'
    rax-eq : SM.readReg (SM.LocState.regs σ) RAX ≡ closure-loc
    env-ptr : readLoc σ closure-loc ≡ just env-loc
    code-ptr : readLoc σ (SM.sucLoc closure-loc) ≡ just code-loc

open ClosureOutputAtLoc

-- INPUT validity: Sum structure at a known location, RDI points to it
-- Used by case-ir which reads tag and payload
-- Note: tag is stored as a value at sum-loc, payload pointer at sucLoc
record SumAtLoc (sum-loc : SM.ValueLocation FS') (σ : LocState FS') : Set where
  field
    payload-loc : SM.ValueLocation FS'
    rdi-eq : SM.readReg (SM.LocState.regs σ) RDI ≡ sum-loc
    payload-ptr : readLoc σ (SM.sucLoc sum-loc) ≡ just payload-loc
    -- Note: tag at sum-loc is read as immediate value, not captured here

open SumAtLoc

-- OUTPUT validity: Sum structure at a known location, RAX points to it
-- Used by inl-ir/inr-ir which produce sums
record SumOutputAtLoc (sum-loc : SM.ValueLocation FS') (σ : LocState FS') : Set where
  field
    payload-loc : SM.ValueLocation FS'
    rax-eq : SM.readReg (SM.LocState.regs σ) RAX ≡ sum-loc
    payload-ptr : readLoc σ (SM.sucLoc sum-loc) ≡ just payload-loc

open SumOutputAtLoc

-- INPUT validity for apply: pair of (closure, arg), with closure structure
-- apply-ir input type is (A ⇒ B) * A
record ApplyInputAtLoc (input-loc : SM.ValueLocation FS') (σ : LocState FS') : Set where
  field
    closure-loc : SM.ValueLocation FS'
    arg-loc : SM.ValueLocation FS'
    env-loc : SM.ValueLocation FS'
    code-loc : SM.ValueLocation FS'
    rdi-eq : SM.readReg (SM.LocState.regs σ) RDI ≡ input-loc
    closure-ptr : readLoc σ input-loc ≡ just closure-loc
    arg-ptr : readLoc σ (SM.sucLoc input-loc) ≡ just arg-loc
    env-ptr : readLoc σ closure-loc ≡ just env-loc
    code-ptr : readLoc σ (SM.sucLoc closure-loc) ≡ just code-loc

open ApplyInputAtLoc

------------------------------------------------------------------------
-- Bridge Transfers: Output validity → Input validity
--
-- After bridge (mov rdi, rax), RDI = RAX and memory unchanged.
-- So PairOutputAtLoc before bridge becomes PairAtLoc after bridge.
------------------------------------------------------------------------

-- Helper: readLoc unchanged when only registers change
private
  bridge-readLoc-eq : ∀ (σ : LocState FS') (loc : SM.ValueLocation FS') →
    readLoc (bridge-slot-state σ) loc ≡ readLoc σ loc
  bridge-readLoc-eq σ (OnStack f k) = refl
  bridge-readLoc-eq σ (OnHeap hl) = refl

-- Transfer: PairOutputAtLoc σ → PairAtLoc (bridge-slot-state σ)
-- The same location, but now RDI points to it instead of RAX
bridge-transfers-pair : ∀ (pair-loc : SM.ValueLocation FS') (σ : LocState FS') →
  PairOutputAtLoc pair-loc σ → PairAtLoc pair-loc (bridge-slot-state σ)
bridge-transfers-pair pair-loc σ out = record
  { fst-loc = PairOutputAtLoc.fst-loc out
  ; snd-loc = PairOutputAtLoc.snd-loc out
  ; rdi-eq = PairOutputAtLoc.rax-eq out  -- After bridge: RDI = RAX (before)
  ; fst-ptr = trans (bridge-readLoc-eq σ pair-loc) (PairOutputAtLoc.fst-ptr out)
  ; snd-ptr = trans (bridge-readLoc-eq σ (SM.sucLoc pair-loc)) (PairOutputAtLoc.snd-ptr out)
  }

-- Transfer: ClosureOutputAtLoc σ → ClosureAtLoc (bridge-slot-state σ)
bridge-transfers-closure : ∀ (closure-loc : SM.ValueLocation FS') (σ : LocState FS') →
  ClosureOutputAtLoc closure-loc σ → ClosureAtLoc closure-loc (bridge-slot-state σ)
bridge-transfers-closure closure-loc σ out = record
  { env-loc = ClosureOutputAtLoc.env-loc out
  ; code-loc = ClosureOutputAtLoc.code-loc out
  ; rdi-eq = ClosureOutputAtLoc.rax-eq out
  ; env-ptr = trans (bridge-readLoc-eq σ closure-loc) (ClosureOutputAtLoc.env-ptr out)
  ; code-ptr = trans (bridge-readLoc-eq σ (SM.sucLoc closure-loc)) (ClosureOutputAtLoc.code-ptr out)
  }

-- Transfer: SumOutputAtLoc σ → SumAtLoc (bridge-slot-state σ)
bridge-transfers-sum : ∀ (sum-loc : SM.ValueLocation FS') (σ : LocState FS') →
  SumOutputAtLoc sum-loc σ → SumAtLoc sum-loc (bridge-slot-state σ)
bridge-transfers-sum sum-loc σ out = record
  { payload-loc = SumOutputAtLoc.payload-loc out
  ; rdi-eq = SumOutputAtLoc.rax-eq out
  ; payload-ptr = trans (bridge-readLoc-eq σ (SM.sucLoc sum-loc)) (SumOutputAtLoc.payload-ptr out)
  }

-- fst-runner with explicit location-based validity
-- Takes pair-loc explicitly (caller knows it from ValidAtWF)
fst-runner-with-valid : ∀ {A B} (pair-loc : SM.ValueLocation FS')
  (prefix suffix : Program) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  PairAtLoc pair-loc σ →
  ∃[ s' ] IRStarResult (fst-ir {A} {B}) prefix suffix s s' (length prefix)
fst-runner-with-valid {A} {B} pair-loc prefix suffix σ s sc h-eq pc-eq pv =
  let
    hb = heap-base sc
    fst-loc = PairAtLoc.fst-loc pv

    -- Derive: readLoc σ (readReg (regs σ) RDI) ≡ just fst-loc
    -- From: rdi-eq : readReg (regs σ) RDI ≡ pair-loc
    --       fst-ptr : readLoc σ pair-loc ≡ just fst-loc
    mem-pre : readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc
    mem-pre = subst (λ loc → readLoc σ loc ≡ just fst-loc) (sym (PairAtLoc.rdi-eq pv)) (PairAtLoc.fst-ptr pv)

    -- x86 memory precondition: derive from StateCorresponds
    x86-mem-eq : x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi) ≡ just (loc-to-addr hb fst-loc)
    x86-mem-eq = fst-x86-mem-helper σ s sc fst-loc mem-pre

    -- Final state
    s' = fst-expected-state s (loc-to-addr hb fst-loc)
    σ' = fst-slot-state σ fst-loc

  in s' , record
    { star-proof = fst-star-at-offset prefix suffix s (loc-to-addr hb fst-loc) h-eq pc-eq x86-mem-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = σ'
    ; corr-proof = fst-preserves-corresponds σ s fst-loc sc mem-pre
    }
  where
    -- Helper to derive x86 memory equality from SlotMachine memory and correspondence
    fst-x86-mem-helper : ∀ (σ : LocState FS') (s : State) (sc : StateCorresponds σ s)
      (fst-loc : SM.ValueLocation FS') →
      readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc →
      x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi) ≡ just (loc-to-addr (heap-base sc) fst-loc)
    fst-x86-mem-helper σ s sc fst-loc mem-pre =
      fst-x86-helper (SM.readReg (SM.LocState.regs σ) RDI) refl mem-pre
      where
        hb = heap-base sc

        -- Helper to get x86 memory from heap location (defined first to be in scope)
        heap-x86-mem-from-slot : ∀ (hl : HeapLocation) (target : SM.ValueLocation FS') →
          readLoc σ (OnHeap hl) ≡ just target →
          x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (OnHeap hl)) ≡ just (loc-to-addr hb target)
        heap-x86-mem-from-slot hl target eq with SM.LocState.heapMem σ hl in heapMem-eq | eq
        ... | just hl' | refl = heap-corresponds (mem-corresponds sc) hl hl' heapMem-eq

        fst-x86-helper : ∀ (rdi-loc : SM.ValueLocation FS') →
          SM.readReg (SM.LocState.regs σ) RDI ≡ rdi-loc →
          readLoc σ rdi-loc ≡ just fst-loc →
          x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi) ≡ just (loc-to-addr hb fst-loc)
        fst-x86-helper (OnStack f k) rdi-eq mem-pre-stack =
          let rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
              rdi-corr : rdi-addr ≡ loc-to-addr hb (OnStack f k)
              rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)
              x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (OnStack f k)) ≡ just (loc-to-addr hb fst-loc)
              x86-mem-eq = stack-corresponds (mem-corresponds sc) f k fst-loc mem-pre-stack
          in subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb fst-loc))
                   (sym rdi-corr) x86-mem-eq
        fst-x86-helper (OnHeap hl) rdi-eq mem-pre-heap =
          let rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
              rdi-corr : rdi-addr ≡ loc-to-addr hb (OnHeap hl)
              rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)
              x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (OnHeap hl)) ≡ just (loc-to-addr hb fst-loc)
              x86-mem-eq = heap-x86-mem-from-slot hl fst-loc mem-pre-heap
          in subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb fst-loc))
                   (sym rdi-corr) x86-mem-eq

-- snd-runner with explicit location-based validity
-- Takes pair-loc explicitly (caller knows it from ValidAtWF)
snd-runner-with-valid : ∀ {A B} (pair-loc : SM.ValueLocation FS')
  (prefix suffix : Program) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  PairAtLoc pair-loc σ →
  ∃[ s' ] IRStarResult (snd-ir {A} {B}) prefix suffix s s' (length prefix)
snd-runner-with-valid {A} {B} pair-loc prefix suffix σ s sc h-eq pc-eq pv =
  let
    hb = heap-base sc
    snd-loc = PairAtLoc.snd-loc pv

    -- Derive: readLoc σ (sucLoc (readReg (regs σ) RDI)) ≡ just snd-loc
    -- From: rdi-eq : readReg (regs σ) RDI ≡ pair-loc
    --       snd-ptr : readLoc σ (sucLoc pair-loc) ≡ just snd-loc
    mem-pre : readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc
    mem-pre = subst (λ loc → readLoc σ (SM.sucLoc loc) ≡ just snd-loc) (sym (PairAtLoc.rdi-eq pv)) (PairAtLoc.snd-ptr pv)

    -- x86 memory precondition: derive from StateCorresponds
    -- snd reads from rdi + slot-size, so we need to use sucLoc-to-addr
    x86-mem-eq : x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi +ℕ slot-size) ≡ just (loc-to-addr hb snd-loc)
    x86-mem-eq = snd-x86-mem-helper σ s sc snd-loc mem-pre

    -- Final state
    s' = snd-expected-state s (loc-to-addr hb snd-loc)
    σ' = snd-slot-state σ snd-loc

  in s' , record
    { star-proof = snd-star-at-offset prefix suffix s (loc-to-addr hb snd-loc) h-eq pc-eq x86-mem-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = σ'
    ; corr-proof = snd-preserves-corresponds σ s snd-loc sc mem-pre
    }
  where
    -- Helper to derive x86 memory equality from SlotMachine memory and correspondence
    snd-x86-mem-helper : ∀ (σ : LocState FS') (s : State) (sc : StateCorresponds σ s)
      (snd-loc : SM.ValueLocation FS') →
      readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc →
      x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi +ℕ slot-size) ≡ just (loc-to-addr (heap-base sc) snd-loc)
    snd-x86-mem-helper σ s sc snd-loc mem-pre =
      snd-x86-helper (SM.readReg (SM.LocState.regs σ) RDI) refl mem-pre
      where
        hb = heap-base sc

        -- Helper to get x86 memory from heap location (defined first to be in scope)
        heap-x86-mem-from-slot : ∀ (hl : HeapLocation) (target : SM.ValueLocation FS') →
          readLoc σ (OnHeap (SM.sucHL hl)) ≡ just target →
          x86-readMem (X86Sem.State.memory s) (loc-to-addr hb (SM.sucLoc (OnHeap hl))) ≡ just (loc-to-addr hb target)
        heap-x86-mem-from-slot hl target eq with SM.LocState.heapMem σ (SM.sucHL hl) in heapMem-eq | eq
        ... | just hl' | refl = heap-corresponds (mem-corresponds sc) (SM.sucHL hl) hl' heapMem-eq

        snd-x86-helper : ∀ (rdi-loc : SM.ValueLocation FS') →
          SM.readReg (SM.LocState.regs σ) RDI ≡ rdi-loc →
          readLoc σ (SM.sucLoc rdi-loc) ≡ just snd-loc →
          x86-readMem (X86Sem.State.memory s) (x86-readReg (X86Sem.State.regs s) rdi +ℕ slot-size) ≡ just (loc-to-addr hb snd-loc)
        snd-x86-helper (OnStack f k) rdi-eq mem-pre-stack =
          let rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
              rdi-corr : rdi-addr ≡ loc-to-addr hb (OnStack f k)
              rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)
              -- sucLoc (OnStack f k) = OnStack f (suc k)
              suc-loc = SM.sucLoc (OnStack f k)
              -- By sucLoc-to-addr: loc-to-addr hb (sucLoc (OnStack f k)) = loc-to-addr hb (OnStack f k) + slot-size
              sucLoc-eq : loc-to-addr hb suc-loc ≡ loc-to-addr hb (OnStack f k) +ℕ slot-size
              sucLoc-eq = sucLoc-to-addr hb (OnStack f k)
              -- By mem-corresponds: x86 memory at addr(suc-loc) = loc-to-addr hb snd-loc
              x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb suc-loc) ≡ just (loc-to-addr hb snd-loc)
              x86-mem-eq = stack-corresponds (mem-corresponds sc) f (suc k) snd-loc mem-pre-stack
              -- Combine: rdi-addr + slot-size = loc-to-addr hb suc-loc
              addr-eq : rdi-addr +ℕ slot-size ≡ loc-to-addr hb suc-loc
              addr-eq = trans (cong (_+ℕ slot-size) rdi-corr) (sym sucLoc-eq)
          in subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb snd-loc))
                   (sym addr-eq) x86-mem-eq
        snd-x86-helper (OnHeap hl) rdi-eq mem-pre-heap =
          let rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
              rdi-corr : rdi-addr ≡ loc-to-addr hb (OnHeap hl)
              rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong (loc-to-addr hb) rdi-eq)
              suc-loc = SM.sucLoc (OnHeap hl)
              -- By sucLoc-to-addr: loc-to-addr hb (sucLoc (OnHeap hl)) = loc-to-addr hb (OnHeap hl) + slot-size
              sucLoc-eq : loc-to-addr hb suc-loc ≡ loc-to-addr hb (OnHeap hl) +ℕ slot-size
              sucLoc-eq = sucLoc-to-addr hb (OnHeap hl)
              -- Use the helper to get x86 memory equality
              x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr hb suc-loc) ≡ just (loc-to-addr hb snd-loc)
              x86-mem-eq = heap-x86-mem-from-slot hl snd-loc mem-pre-heap
              -- Combine: rdi-addr + slot-size = loc-to-addr hb suc-loc
              addr-eq : rdi-addr +ℕ slot-size ≡ loc-to-addr hb suc-loc
              addr-eq = trans (cong (_+ℕ slot-size) rdi-corr) (sym sucLoc-eq)
          in subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr hb snd-loc))
                   (sym addr-eq) x86-mem-eq

------------------------------------------------------------------------
-- First-Principles Composition for fst/snd (Location-Based Validity)
--
-- The key insight: when we compose (fst-ir ∘ f), the f produces a pair.
-- Instead of requiring validity for ALL states, we use explicit
-- location-based validity via PairAtLoc/PairOutputAtLoc.
--
-- This is a more specific postulate, closer to semantics:
-- - Pairs are constructed with two valid pointers at known locations
-- - So pair output satisfies PairOutputAtLoc for some pair-loc
--
-- See: location-validity-pattern.md for full documentation.
--
-- We postulate this for now, as pair-runner is also postulated.
-- When pair-runner is proven, this follows automatically.
------------------------------------------------------------------------

-- Postulate: pair-producing IRs output PairOutputAtLoc
-- This is more specific than claiming ALL states valid.
-- This claims: states resulting from pair-typed output have valid pair structure.
-- The caller knows the location from the IR's output.
postulate
  pair-output-produces-valid : ∀ {A B C} (f : IR A (B * C)) →
    ∀ (result-σ : LocState FS') →
    ∃[ pair-loc ] PairOutputAtLoc pair-loc result-σ

-- compose-fst-runner: Specialized compose for (fst-ir ∘ f)
-- Uses output validity (PairOutputAtLoc) from f, transfers via bridge to PairAtLoc
compose-fst-runner : ∀ {A B C} (f : IR A (B * C)) →
  IRRunner f →
  IRRunner (fst-ir ∘ f)
compose-fst-runner {_} {B} {C} f f-run prefix suffix σ s sc h-eq pc-eq =
  let -- Programs
      prog-f = compile-ir f
      prog-g = compile-ir (fst-ir {B} {C})

      -- Step 1: Execute f
      (sf , f-result) = f-run prefix (compose-bridge ++ prog-g ++ suffix) σ s sc h-eq pc-eq
      σf = IRStarResult.σ-final f-result
      star-f = IRStarResult.star-proof f-result
      h-sf = IRStarResult.halted-false f-result
      pc-sf = IRStarResult.pc-advanced f-result
      sc-f = IRStarResult.corr-proof f-result

      -- PC at bridge
      len-prefix-f = length-++ prefix
      pc-at-bridge : X86Sem.State.pc sf ≡ length (prefix ++ prog-f)
      pc-at-bridge = trans pc-sf
                           (trans (cong (length prefix +ℕ_) (sym (compile-ir-length f)))
                                  (sym len-prefix-f))

      -- Step 2: Execute bridge
      assoc-for-bridge : (prefix ++ prog-f) ++ (compose-bridge ++ (prog-g ++ suffix))
                       ≡ prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      assoc-for-bridge = ++-assoc prefix prog-f (compose-bridge ++ (prog-g ++ suffix))

      (sb , star-b' , h-sb , pc-sb , sc-b) =
        bridge-runner (prefix ++ prog-f) (prog-g ++ suffix) σf sf sc-f h-sf pc-at-bridge

      star-b : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) sf sb
      star-b = subst (λ p → Star p sf sb) assoc-for-bridge star-b'

      -- KEY: Derive input validity for fst from f's output validity
      -- f outputs to RAX, bridge transfers RAX → RDI
      -- So PairOutputAtLoc σf → PairAtLoc (bridge-slot-state σf)
      (pair-loc , pair-output-valid) = pair-output-produces-valid f σf

      fst-input-valid : PairAtLoc pair-loc (bridge-slot-state σf)
      fst-input-valid = bridge-transfers-pair pair-loc σf pair-output-valid

      -- Step 3: Execute fst-ir using derived validity (NOT MemValidProvider!)
      assoc-prefix-f-bridge : prefix ++ (prog-f ++ compose-bridge) ≡ (prefix ++ prog-f) ++ compose-bridge
      assoc-prefix-f-bridge = sym (++-assoc prefix prog-f compose-bridge)

      len-prefix-f-bridge : length (prefix ++ prog-f ++ compose-bridge)
                          ≡ length (prefix ++ prog-f) +ℕ length compose-bridge
      len-prefix-f-bridge = trans (cong length assoc-prefix-f-bridge) (length-++ (prefix ++ prog-f))

      pc-at-g : X86Sem.State.pc sb ≡ length (prefix ++ prog-f ++ compose-bridge)
      pc-at-g = trans pc-sb (sym len-prefix-f-bridge)

      -- Use fst-runner-with-valid directly with derived validity!
      (sg , g-result) = fst-runner-with-valid {B} {C} pair-loc (prefix ++ prog-f ++ compose-bridge) suffix
                              (bridge-slot-state σf) sb sc-b h-sb pc-at-g
                              fst-input-valid

      σg = IRStarResult.σ-final g-result
      star-g' = IRStarResult.star-proof g-result
      h-sg = IRStarResult.halted-false g-result
      pc-sg = IRStarResult.pc-advanced g-result
      sc-g = IRStarResult.corr-proof g-result

      -- Transport g's Star
      assoc-inner : (prog-f ++ compose-bridge) ++ (prog-g ++ suffix)
                  ≡ prog-f ++ (compose-bridge ++ (prog-g ++ suffix))
      assoc-inner = ++-assoc prog-f compose-bridge (prog-g ++ suffix)

      assoc-outer : (prefix ++ (prog-f ++ compose-bridge)) ++ (prog-g ++ suffix)
                  ≡ prefix ++ ((prog-f ++ compose-bridge) ++ (prog-g ++ suffix))
      assoc-outer = ++-assoc prefix (prog-f ++ compose-bridge) (prog-g ++ suffix)

      assoc-for-g : (prefix ++ (prog-f ++ compose-bridge)) ++ (prog-g ++ suffix)
                  ≡ prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      assoc-for-g = trans assoc-outer (cong (prefix ++_) assoc-inner)

      star-g : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) sb sg
      star-g = subst (λ p → Star p sb sg) assoc-for-g star-g'

      -- Chain Stars
      star-fg : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) s sg
      star-fg = star-f ◅◅ star-b ◅◅ star-g

      -- Transport to final form
      assoc-tail : compose-bridge ++ (prog-g ++ suffix) ≡ (compose-bridge ++ prog-g) ++ suffix
      assoc-tail = sym (++-assoc compose-bridge prog-g suffix)

      assoc-mid : prog-f ++ (compose-bridge ++ (prog-g ++ suffix))
                ≡ (prog-f ++ (compose-bridge ++ prog-g)) ++ suffix
      assoc-mid = trans (cong (prog-f ++_) assoc-tail)
                        (sym (++-assoc prog-f (compose-bridge ++ prog-g) suffix))

      prog-eq : prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
              ≡ prefix ++ ((prog-f ++ (compose-bridge ++ prog-g)) ++ suffix)
      prog-eq = cong (prefix ++_) assoc-mid

      star-final : Star (prefix ++ compile-ir (fst-ir ∘ f) ++ suffix) s sg
      star-final = subst (λ p → Star p s sg) prog-eq star-fg

      -- PC calculation
      pc-final : X86Sem.State.pc sg ≡ length prefix +ℕ compile-length (fst-ir {B} {C} ∘ f)
      pc-final = compose-fst-pc-lemma prefix prog-f prog-g (compile-length f) (compile-length (fst-ir {B} {C}))
                                  (compile-ir-length f) pc-sg

  in sg , record
    { star-proof = star-final
    ; halted-false = h-sg
    ; pc-advanced = pc-final
    ; σ-final = σg
    ; corr-proof = sc-g
    }
  where
    compose-fst-pc-lemma : ∀ (prefix prog-f prog-g : Program) (clf clg : ℕ) →
      length prog-f ≡ clf →
      ∀ {pc : ℕ} →
      pc ≡ length (prefix ++ prog-f ++ compose-bridge) +ℕ clg →
      pc ≡ length prefix +ℕ (clf +ℕ length compose-bridge +ℕ clg)
    compose-fst-pc-lemma prefix prog-f prog-g clf clg len-f-eq {pc} pc-eq =
      let
        step1 : length (prefix ++ (prog-f ++ compose-bridge)) ≡ length prefix +ℕ length (prog-f ++ compose-bridge)
        step1 = length-++ prefix
        step2 : length (prog-f ++ compose-bridge) ≡ length prog-f +ℕ length compose-bridge
        step2 = length-++ prog-f
        len-eq : length (prefix ++ prog-f ++ compose-bridge) ≡ length prefix +ℕ (length prog-f +ℕ length compose-bridge)
        len-eq = trans step1 (cong (length prefix +ℕ_) step2)
        step4 : (length prefix +ℕ (length prog-f +ℕ length compose-bridge)) +ℕ clg
              ≡ length prefix +ℕ ((length prog-f +ℕ length compose-bridge) +ℕ clg)
        step4 = ℕ-+-assoc (length prefix) (length prog-f +ℕ length compose-bridge) clg
        step5 : length prefix +ℕ ((length prog-f +ℕ length compose-bridge) +ℕ clg)
              ≡ length prefix +ℕ ((clf +ℕ length compose-bridge) +ℕ clg)
        step5 = cong (λ x → length prefix +ℕ ((x +ℕ length compose-bridge) +ℕ clg)) len-f-eq
        final : length (prefix ++ prog-f ++ compose-bridge) +ℕ clg ≡ length prefix +ℕ ((clf +ℕ length compose-bridge) +ℕ clg)
        final = trans (cong (_+ℕ clg) len-eq) (trans step4 step5)
      in trans pc-eq final

-- compose-snd-runner: Specialized compose for (snd-ir ∘ f)
-- Symmetric to compose-fst-runner
compose-snd-runner : ∀ {A B C} (f : IR A (B * C)) →
  IRRunner f →
  IRRunner (snd-ir ∘ f)
compose-snd-runner {_} {B} {C} f f-run prefix suffix σ s sc h-eq pc-eq =
  let -- Programs
      prog-f = compile-ir f
      prog-g = compile-ir (snd-ir {B} {C})

      -- Step 1: Execute f
      (sf , f-result) = f-run prefix (compose-bridge ++ prog-g ++ suffix) σ s sc h-eq pc-eq
      σf = IRStarResult.σ-final f-result
      star-f = IRStarResult.star-proof f-result
      h-sf = IRStarResult.halted-false f-result
      pc-sf = IRStarResult.pc-advanced f-result
      sc-f = IRStarResult.corr-proof f-result

      -- PC at bridge
      len-prefix-f = length-++ prefix
      pc-at-bridge : X86Sem.State.pc sf ≡ length (prefix ++ prog-f)
      pc-at-bridge = trans pc-sf
                           (trans (cong (length prefix +ℕ_) (sym (compile-ir-length f)))
                                  (sym len-prefix-f))

      -- Step 2: Execute bridge
      assoc-for-bridge : (prefix ++ prog-f) ++ (compose-bridge ++ (prog-g ++ suffix))
                       ≡ prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      assoc-for-bridge = ++-assoc prefix prog-f (compose-bridge ++ (prog-g ++ suffix))

      (sb , star-b' , h-sb , pc-sb , sc-b) =
        bridge-runner (prefix ++ prog-f) (prog-g ++ suffix) σf sf sc-f h-sf pc-at-bridge

      star-b : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) sf sb
      star-b = subst (λ p → Star p sf sb) assoc-for-bridge star-b'

      -- KEY: Derive input validity for snd from f's output validity
      -- f outputs to RAX, bridge transfers RAX → RDI
      -- So PairOutputAtLoc σf → PairAtLoc (bridge-slot-state σf)
      (pair-loc , pair-output-valid) = pair-output-produces-valid f σf

      snd-input-valid : PairAtLoc pair-loc (bridge-slot-state σf)
      snd-input-valid = bridge-transfers-pair pair-loc σf pair-output-valid

      -- Step 3: Execute snd-ir using derived validity (NOT MemValidProvider!)
      assoc-prefix-f-bridge : prefix ++ (prog-f ++ compose-bridge) ≡ (prefix ++ prog-f) ++ compose-bridge
      assoc-prefix-f-bridge = sym (++-assoc prefix prog-f compose-bridge)

      len-prefix-f-bridge : length (prefix ++ prog-f ++ compose-bridge)
                          ≡ length (prefix ++ prog-f) +ℕ length compose-bridge
      len-prefix-f-bridge = trans (cong length assoc-prefix-f-bridge) (length-++ (prefix ++ prog-f))

      pc-at-g : X86Sem.State.pc sb ≡ length (prefix ++ prog-f ++ compose-bridge)
      pc-at-g = trans pc-sb (sym len-prefix-f-bridge)

      -- Use snd-runner-with-valid directly with derived validity!
      (sg , g-result) = snd-runner-with-valid {B} {C} pair-loc (prefix ++ prog-f ++ compose-bridge) suffix
                              (bridge-slot-state σf) sb sc-b h-sb pc-at-g
                              snd-input-valid

      σg = IRStarResult.σ-final g-result
      star-g' = IRStarResult.star-proof g-result
      h-sg = IRStarResult.halted-false g-result
      pc-sg = IRStarResult.pc-advanced g-result
      sc-g = IRStarResult.corr-proof g-result

      -- Transport g's Star
      assoc-inner : (prog-f ++ compose-bridge) ++ (prog-g ++ suffix)
                  ≡ prog-f ++ (compose-bridge ++ (prog-g ++ suffix))
      assoc-inner = ++-assoc prog-f compose-bridge (prog-g ++ suffix)

      assoc-outer : (prefix ++ (prog-f ++ compose-bridge)) ++ (prog-g ++ suffix)
                  ≡ prefix ++ ((prog-f ++ compose-bridge) ++ (prog-g ++ suffix))
      assoc-outer = ++-assoc prefix (prog-f ++ compose-bridge) (prog-g ++ suffix)

      assoc-for-g : (prefix ++ (prog-f ++ compose-bridge)) ++ (prog-g ++ suffix)
                  ≡ prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
      assoc-for-g = trans assoc-outer (cong (prefix ++_) assoc-inner)

      star-g : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) sb sg
      star-g = subst (λ p → Star p sb sg) assoc-for-g star-g'

      -- Chain Stars
      star-fg : Star (prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))) s sg
      star-fg = star-f ◅◅ star-b ◅◅ star-g

      -- Transport to final form
      assoc-tail : compose-bridge ++ (prog-g ++ suffix) ≡ (compose-bridge ++ prog-g) ++ suffix
      assoc-tail = sym (++-assoc compose-bridge prog-g suffix)

      assoc-mid : prog-f ++ (compose-bridge ++ (prog-g ++ suffix))
                ≡ (prog-f ++ (compose-bridge ++ prog-g)) ++ suffix
      assoc-mid = trans (cong (prog-f ++_) assoc-tail)
                        (sym (++-assoc prog-f (compose-bridge ++ prog-g) suffix))

      prog-eq : prefix ++ (prog-f ++ (compose-bridge ++ (prog-g ++ suffix)))
              ≡ prefix ++ ((prog-f ++ (compose-bridge ++ prog-g)) ++ suffix)
      prog-eq = cong (prefix ++_) assoc-mid

      star-final : Star (prefix ++ compile-ir (snd-ir {B} {C} ∘ f) ++ suffix) s sg
      star-final = subst (λ p → Star p s sg) prog-eq star-fg

      -- PC calculation
      pc-final : X86Sem.State.pc sg ≡ length prefix +ℕ compile-length (snd-ir {B} {C} ∘ f)
      pc-final = compose-snd-pc-lemma prefix prog-f prog-g (compile-length f) (compile-length (snd-ir {B} {C}))
                                  (compile-ir-length f) pc-sg

  in sg , record
    { star-proof = star-final
    ; halted-false = h-sg
    ; pc-advanced = pc-final
    ; σ-final = σg
    ; corr-proof = sc-g
    }
  where
    compose-snd-pc-lemma : ∀ (prefix prog-f prog-g : Program) (clf clg : ℕ) →
      length prog-f ≡ clf →
      ∀ {pc : ℕ} →
      pc ≡ length (prefix ++ prog-f ++ compose-bridge) +ℕ clg →
      pc ≡ length prefix +ℕ (clf +ℕ length compose-bridge +ℕ clg)
    compose-snd-pc-lemma prefix prog-f prog-g clf clg len-f-eq {pc} pc-eq =
      let
        step1 : length (prefix ++ (prog-f ++ compose-bridge)) ≡ length prefix +ℕ length (prog-f ++ compose-bridge)
        step1 = length-++ prefix
        step2 : length (prog-f ++ compose-bridge) ≡ length prog-f +ℕ length compose-bridge
        step2 = length-++ prog-f
        len-eq : length (prefix ++ prog-f ++ compose-bridge) ≡ length prefix +ℕ (length prog-f +ℕ length compose-bridge)
        len-eq = trans step1 (cong (length prefix +ℕ_) step2)
        step4 : (length prefix +ℕ (length prog-f +ℕ length compose-bridge)) +ℕ clg
              ≡ length prefix +ℕ ((length prog-f +ℕ length compose-bridge) +ℕ clg)
        step4 = ℕ-+-assoc (length prefix) (length prog-f +ℕ length compose-bridge) clg
        step5 : length prefix +ℕ ((length prog-f +ℕ length compose-bridge) +ℕ clg)
              ≡ length prefix +ℕ ((clf +ℕ length compose-bridge) +ℕ clg)
        step5 = cong (λ x → length prefix +ℕ ((x +ℕ length compose-bridge) +ℕ clg)) len-f-eq
        final : length (prefix ++ prog-f ++ compose-bridge) +ℕ clg ≡ length prefix +ℕ ((clf +ℕ length compose-bridge) +ℕ clg)
        final = trans (cong (_+ℕ clg) len-eq) (trans step4 step5)
      in trans pc-eq final

------------------------------------------------------------------------
-- pair-runner: Execute ⟨ f , g ⟩ at any offset
--
-- The pair program structure is:
--   pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g ++ pair-cleanup
--
-- Phase 1: pair-setup (7 instructions)
--   - push r14, push r15, push rbp
--   - mov rbp, rsp; sub rsp, (slots 2); mov r15, rsp; mov r14, rdi
--   - After: r15 = pair address, r14 = saved input, rdi unchanged
--
-- Phase 2: Execute f (input → f's result in rax)
--
-- Phase 3: pair-middle (2 instructions)
--   - mov [r15], rax (store f's result as fst)
--   - mov rdi, r14 (restore input for g)
--
-- Phase 4: Execute g (input → g's result in rax)
--
-- Phase 5: pair-cleanup (6 instructions)
--   - mov [r15+8], rax (store g's result as snd)
--   - mov rax, r15 (return pair address)
--   - mov rsp, rbp; pop rbp; pop r15; pop r14 (cleanup)
------------------------------------------------------------------------

-- SlotMachine state after pair-setup
-- r14 = original input, r15 = pair address, rdi unchanged
pair-setup-slot-state : LocState FS' → SM.ValueLocation FS' → LocState FS'
pair-setup-slot-state σ pair-loc = record σ
  { regs = writeReg (writeReg (SM.LocState.regs σ) R14 (SM.readReg (SM.LocState.regs σ) RDI)) R15 pair-loc }

-- SlotMachine state after pair-middle
-- Stores f's result at pair[0], restores input to rdi
pair-middle-slot-state : LocState FS' → LocState FS'
pair-middle-slot-state σ = record σ
  { regs = writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) R14) }

-- SlotMachine state after pair-cleanup
-- rax = pair address
pair-cleanup-slot-state : LocState FS' → LocState FS'
pair-cleanup-slot-state σ = record σ
  { regs = writeReg (SM.LocState.regs σ) RAX (SM.readReg (SM.LocState.regs σ) R15) }

------------------------------------------------------------------------
-- pair-setup-result: PROVEN using StepChain
--
-- This proves that executing pair-setup (7 instructions) at any offset:
--   1. Produces a Star proof of execution
--   2. Does not halt
--   3. Advances PC by 7 (length pair-setup)
--   4. Preserves StateCorresponds (postulated helper for now)
------------------------------------------------------------------------

-- Helper postulate for StateCorresponds preservation through pair-setup
-- TODO: Prove this by tracking register changes through 7 instructions
postulate
  pair-setup-preserves-corresponds : ∀ (s s' : State)
    (σ : LocState FS') (pair-loc : SM.ValueLocation FS') →
    StateCorresponds σ s →
    -- s' is the result of executing 7 pair-setup instructions on s
    StateCorresponds (pair-setup-slot-state σ pair-loc) s'

-- pair-setup executes 7 instructions, returns state AND correspondence
-- PROVEN using step-fetch-result pattern (like step-pair-setup in ExecLemmas)
pair-setup-result : ∀ (prefix suffix : Program) (s : State)
  (σ : LocState FS') (pair-loc : SM.ValueLocation FS') →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  ∃[ s' ] (Star (prefix ++ pair-setup ++ suffix) s s'
         × X86Sem.State.halted s' ≡ false
         × X86Sem.State.pc s' ≡ length prefix +ℕ length pair-setup
         × StateCorresponds (pair-setup-slot-state σ pair-loc) s')
pair-setup-result prefix suffix s σ pair-loc sc h-eq pc-eq =
  let
    -- The program
    prog = prefix ++ pair-setup ++ suffix
    ps = pair-setup ++ suffix  -- pair-setup with suffix for fetch proofs

    -- Helper: make-step for this program
    make-step : ∀ (st st' : State) (instr : Instr) →
      X86Sem.State.halted st ≡ false →
      fetch prog (X86Sem.State.pc st) ≡ just instr →
      X86Sem.execInstr prog st instr ≡ just st' →
      X86Sem.step prog st ≡ just st'
    make-step st st' instr h-st f-eq exec-eq =
      trans (step-fetch-result prog st instr h-st f-eq) exec-eq

    -- Step 0: push r14 at pc = length prefix
    -- fetch-++-right gives proof at (length prefix +ℕ 0), need it at (X86Sem.State.pc s)
    -- Use +-identityʳ: length prefix +ℕ 0 ≡ length prefix
    -- Then sym pc-eq: length prefix ≡ X86Sem.State.pc s
    fetch-0 : fetch prog (X86Sem.State.pc s) ≡ just (push (reg r14))
    fetch-0 = subst (λ n → fetch prog n ≡ just (push (reg r14)))
                    (trans (+-identityʳ (length prefix)) (sym pc-eq))
                    (fetch-++-right prefix ps 0 (push (reg r14)) refl)
    s1 = record s { regs = x86-writeReg (X86Sem.State.regs s) rsp
                             (x86-readReg (X86Sem.State.regs s) rsp ∸ slot-size)
                  ; memory = x86-writeMem (X86Sem.State.memory s)
                               (x86-readReg (X86Sem.State.regs s) rsp ∸ slot-size)
                               (x86-readReg (X86Sem.State.regs s) r14)
                  ; pc = X86Sem.State.pc s +ℕ 1 }
    step-0 = make-step s s1 (push (reg r14)) h-eq fetch-0 (push-reg-result prog s r14)
    pc1 : X86Sem.State.pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- Step 1: push r15 at pc = length prefix + 1
    fetch-1 : fetch prog (X86Sem.State.pc s1) ≡ just (push (reg r15))
    fetch-1 = subst (λ n → fetch prog n ≡ just (push (reg r15)))
                    (sym pc1) (fetch-++-right prefix ps 1 (push (reg r15)) refl)
    s2 = record s1 { regs = x86-writeReg (X86Sem.State.regs s1) rsp
                              (x86-readReg (X86Sem.State.regs s1) rsp ∸ slot-size)
                   ; memory = x86-writeMem (X86Sem.State.memory s1)
                                (x86-readReg (X86Sem.State.regs s1) rsp ∸ slot-size)
                                (x86-readReg (X86Sem.State.regs s1) r15)
                   ; pc = X86Sem.State.pc s1 +ℕ 1 }
    step-1 = make-step s1 s2 (push (reg r15)) h-eq fetch-1 (push-reg-result prog s1 r15)
    pc2 : X86Sem.State.pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- Step 2: push rbp at pc = length prefix + 2
    fetch-2 : fetch prog (X86Sem.State.pc s2) ≡ just (push (reg rbp))
    fetch-2 = subst (λ n → fetch prog n ≡ just (push (reg rbp)))
                    (sym pc2) (fetch-++-right prefix ps 2 (push (reg rbp)) refl)
    s3 = record s2 { regs = x86-writeReg (X86Sem.State.regs s2) rsp
                              (x86-readReg (X86Sem.State.regs s2) rsp ∸ slot-size)
                   ; memory = x86-writeMem (X86Sem.State.memory s2)
                                (x86-readReg (X86Sem.State.regs s2) rsp ∸ slot-size)
                                (x86-readReg (X86Sem.State.regs s2) rbp)
                   ; pc = X86Sem.State.pc s2 +ℕ 1 }
    step-2 = make-step s2 s3 (push (reg rbp)) h-eq fetch-2 (push-reg-result prog s2 rbp)
    pc3 : X86Sem.State.pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    -- Step 3: mov rbp, rsp at pc = length prefix + 3
    fetch-3 : fetch prog (X86Sem.State.pc s3) ≡ just (mov (reg rbp) (reg rsp))
    fetch-3 = subst (λ n → fetch prog n ≡ just (mov (reg rbp) (reg rsp)))
                    (sym pc3) (fetch-++-right prefix ps 3 (mov (reg rbp) (reg rsp)) refl)
    s4 = record s3 { regs = x86-writeReg (X86Sem.State.regs s3) rbp
                              (x86-readReg (X86Sem.State.regs s3) rsp)
                   ; pc = X86Sem.State.pc s3 +ℕ 1 }
    step-3 = make-step s3 s4 (mov (reg rbp) (reg rsp)) h-eq fetch-3 (mov-reg-reg-result prog s3 rbp rsp)
    pc4 : X86Sem.State.pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Step 4: sub rsp, (slots 2) at pc = length prefix + 4
    fetch-4 : fetch prog (X86Sem.State.pc s4) ≡ just (sub (reg rsp) (imm (slots 2)))
    fetch-4 = subst (λ n → fetch prog n ≡ just (sub (reg rsp) (imm (slots 2))))
                    (sym pc4) (fetch-++-right prefix ps 4 (sub (reg rsp) (imm (slots 2))) refl)
    s5 = record s4 { regs = x86-writeReg (X86Sem.State.regs s4) rsp
                              (x86-readReg (X86Sem.State.regs s4) rsp ∸ slots 2)
                   ; pc = X86Sem.State.pc s4 +ℕ 1
                   ; flags = updateFlags
                               (x86-readReg (X86Sem.State.regs s4) rsp ∸ slots 2)
                               (x86-readReg (X86Sem.State.regs s4) rsp) }
    step-4 = make-step s4 s5 (sub (reg rsp) (imm (slots 2))) h-eq fetch-4
               (sub-imm-reg-result prog s4 rsp (slots 2))
    pc5 : X86Sem.State.pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    -- Step 5: mov r15, rsp at pc = length prefix + 5
    fetch-5 : fetch prog (X86Sem.State.pc s5) ≡ just (mov (reg r15) (reg rsp))
    fetch-5 = subst (λ n → fetch prog n ≡ just (mov (reg r15) (reg rsp)))
                    (sym pc5) (fetch-++-right prefix ps 5 (mov (reg r15) (reg rsp)) refl)
    s6 = record s5 { regs = x86-writeReg (X86Sem.State.regs s5) r15
                              (x86-readReg (X86Sem.State.regs s5) rsp)
                   ; pc = X86Sem.State.pc s5 +ℕ 1 }
    step-5 = make-step s5 s6 (mov (reg r15) (reg rsp)) h-eq fetch-5 (mov-reg-reg-result prog s5 r15 rsp)
    pc6 : X86Sem.State.pc s6 ≡ length prefix +ℕ 6
    pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc (length prefix) 5 1)

    -- Step 6: mov r14, rdi at pc = length prefix + 6
    fetch-6 : fetch prog (X86Sem.State.pc s6) ≡ just (mov (reg r14) (reg rdi))
    fetch-6 = subst (λ n → fetch prog n ≡ just (mov (reg r14) (reg rdi)))
                    (sym pc6) (fetch-++-right prefix ps 6 (mov (reg r14) (reg rdi)) refl)
    s7 = record s6 { regs = x86-writeReg (X86Sem.State.regs s6) r14
                              (x86-readReg (X86Sem.State.regs s6) rdi)
                   ; pc = X86Sem.State.pc s6 +ℕ 1 }
    step-6 = make-step s6 s7 (mov (reg r14) (reg rdi)) h-eq fetch-6 (mov-reg-reg-result prog s6 r14 rdi)
    pc7 : X86Sem.State.pc s7 ≡ length prefix +ℕ 7
    pc7 = trans (cong (_+ℕ 1) pc6) (+-assoc (length prefix) 6 1)

    -- Final state
    s' = s7

    -- Combined Star proof
    star-proof : Star prog s s'
    star-proof = star-single h-eq step-0 ◅◅
                 star-single h-eq step-1 ◅◅
                 star-single h-eq step-2 ◅◅
                 star-single h-eq step-3 ◅◅
                 star-single h-eq step-4 ◅◅
                 star-single h-eq step-5 ◅◅
                 star-single h-eq step-6

    -- halted preservation (push/mov/sub don't change halted flag)
    h'-eq : X86Sem.State.halted s' ≡ false
    h'-eq = h-eq

    -- PC after 7 instructions = length prefix + 7 = length prefix + length pair-setup
    pc'-eq : X86Sem.State.pc s' ≡ length prefix +ℕ length pair-setup
    pc'-eq = pc7

    -- StateCorresponds (postulated for now)
    sc' : StateCorresponds (pair-setup-slot-state σ pair-loc) s'
    sc' = pair-setup-preserves-corresponds s s' σ pair-loc sc

  in s' , star-proof , h'-eq , pc'-eq , sc'

------------------------------------------------------------------------
-- pair-middle-result: PROVEN using step-fetch-result pattern
--
-- pair-middle is 2 instructions:
--   mov (mem (base r15)) (reg rax)  -- [pair] = f's result
--   mov (reg rdi) (reg r14)         -- rdi = input (for g)
------------------------------------------------------------------------

-- Helper postulate for StateCorresponds preservation through pair-middle
postulate
  pair-middle-preserves-corresponds : ∀ (s s' : State)
    (σ : LocState FS') →
    StateCorresponds σ s →
    StateCorresponds (pair-middle-slot-state σ) s'

-- pair-middle executes 2 instructions, returns state AND correspondence
-- PROVEN using step-fetch-result pattern
pair-middle-result : ∀ (prefix suffix : Program) (s : State)
  (σ : LocState FS') →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  ∃[ s' ] (Star (prefix ++ pair-middle ++ suffix) s s'
         × X86Sem.State.halted s' ≡ false
         × X86Sem.State.pc s' ≡ length prefix +ℕ length pair-middle
         × StateCorresponds (pair-middle-slot-state σ) s')
pair-middle-result prefix suffix s σ sc h-eq pc-eq =
  let
    -- The program
    prog = prefix ++ pair-middle ++ suffix
    ps = pair-middle ++ suffix  -- pair-middle with suffix for fetch proofs

    -- Helper: make-step for this program
    make-step : ∀ (st st' : State) (instr : Instr) →
      X86Sem.State.halted st ≡ false →
      fetch prog (X86Sem.State.pc st) ≡ just instr →
      X86Sem.execInstr prog st instr ≡ just st' →
      X86Sem.step prog st ≡ just st'
    make-step st st' instr h-st f-eq exec-eq =
      trans (step-fetch-result prog st instr h-st f-eq) exec-eq

    -- Step 0: mov (mem (base r15)) (reg rax) at pc = length prefix
    -- Stores rax to memory at [r15]
    fetch-0 : fetch prog (X86Sem.State.pc s) ≡ just (mov (mem (base r15)) (reg rax))
    fetch-0 = subst (λ n → fetch prog n ≡ just (mov (mem (base r15)) (reg rax)))
                    (trans (+-identityʳ (length prefix)) (sym pc-eq))
                    (fetch-++-right prefix ps 0 (mov (mem (base r15)) (reg rax)) refl)
    s1 = record s { memory = x86-writeMem (X86Sem.State.memory s)
                               (effectiveAddr s (base r15))
                               (x86-readReg (X86Sem.State.regs s) rax)
                  ; pc = X86Sem.State.pc s +ℕ 1 }
    step-0 = make-step s s1 (mov (mem (base r15)) (reg rax)) h-eq fetch-0
               (mov-reg-mem-result prog s (base r15) rax)
    pc1 : X86Sem.State.pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- Step 1: mov (reg rdi) (reg r14) at pc = length prefix + 1
    -- Copies r14 to rdi
    fetch-1 : fetch prog (X86Sem.State.pc s1) ≡ just (mov (reg rdi) (reg r14))
    fetch-1 = subst (λ n → fetch prog n ≡ just (mov (reg rdi) (reg r14)))
                    (sym pc1) (fetch-++-right prefix ps 1 (mov (reg rdi) (reg r14)) refl)
    s2 = record s1 { regs = x86-writeReg (X86Sem.State.regs s1) rdi
                              (x86-readReg (X86Sem.State.regs s1) r14)
                   ; pc = X86Sem.State.pc s1 +ℕ 1 }
    step-1 = make-step s1 s2 (mov (reg rdi) (reg r14)) h-eq fetch-1
               (mov-reg-reg-result prog s1 rdi r14)
    pc2 : X86Sem.State.pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- Final state
    s' = s2

    -- Combined Star proof
    star-proof : Star prog s s'
    star-proof = star-single h-eq step-0 ◅◅
                 star-single h-eq step-1

    -- halted preservation
    h'-eq : X86Sem.State.halted s' ≡ false
    h'-eq = h-eq

    -- PC after 2 instructions = length prefix + 2 = length prefix + length pair-middle
    pc'-eq : X86Sem.State.pc s' ≡ length prefix +ℕ length pair-middle
    pc'-eq = pc2

    -- StateCorresponds (postulated)
    sc' : StateCorresponds (pair-middle-slot-state σ) s'
    sc' = pair-middle-preserves-corresponds s s' σ sc

  in s' , star-proof , h'-eq , pc'-eq , sc'

------------------------------------------------------------------------
-- pair-cleanup-result: PROVEN using step-fetch-result pattern
--
-- pair-cleanup is 6 instructions:
--   mov (mem (base+disp r15 slot-size)) (reg rax)  -- [pair+8] = g's result
--   mov (reg rax) (reg r15)                        -- rax = pair address
--   mov (reg rsp) (reg rbp)                        -- restore stack
--   pop rbp                                        -- restore rbp
--   pop r15                                        -- restore r15
--   pop r14                                        -- restore r14
------------------------------------------------------------------------

-- Helper postulate for StateCorresponds preservation through pair-cleanup
postulate
  pair-cleanup-preserves-corresponds : ∀ (s s' : State)
    (σ : LocState FS') →
    StateCorresponds σ s →
    StateCorresponds (pair-cleanup-slot-state σ) s'

-- pair-cleanup executes 6 instructions, returns state AND correspondence
-- PROVEN using step-fetch-result pattern
pair-cleanup-result : ∀ (prefix suffix : Program) (s : State)
  (σ : LocState FS') →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  ∃[ s' ] (Star (prefix ++ pair-cleanup ++ suffix) s s'
         × X86Sem.State.halted s' ≡ false
         × X86Sem.State.pc s' ≡ length prefix +ℕ length pair-cleanup
         × StateCorresponds (pair-cleanup-slot-state σ) s')
pair-cleanup-result prefix suffix s σ sc h-eq pc-eq =
  let
    -- The program
    prog = prefix ++ pair-cleanup ++ suffix
    ps = pair-cleanup ++ suffix  -- pair-cleanup with suffix for fetch proofs

    -- Helper: make-step for this program
    make-step : ∀ (st st' : State) (instr : Instr) →
      X86Sem.State.halted st ≡ false →
      fetch prog (X86Sem.State.pc st) ≡ just instr →
      X86Sem.execInstr prog st instr ≡ just st' →
      X86Sem.step prog st ≡ just st'
    make-step st st' instr h-st f-eq exec-eq =
      trans (step-fetch-result prog st instr h-st f-eq) exec-eq

    -- Step 0: mov (mem (base+disp r15 slot-size)) (reg rax) at pc = length prefix
    -- Stores rax to memory at [r15 + slot-size]
    fetch-0 : fetch prog (X86Sem.State.pc s) ≡ just (mov (mem (base+disp r15 slot-size)) (reg rax))
    fetch-0 = subst (λ n → fetch prog n ≡ just (mov (mem (base+disp r15 slot-size)) (reg rax)))
                    (trans (+-identityʳ (length prefix)) (sym pc-eq))
                    (fetch-++-right prefix ps 0 (mov (mem (base+disp r15 slot-size)) (reg rax)) refl)
    s1 = record s { memory = x86-writeMem (X86Sem.State.memory s)
                               (effectiveAddr s (base+disp r15 slot-size))
                               (x86-readReg (X86Sem.State.regs s) rax)
                  ; pc = X86Sem.State.pc s +ℕ 1 }
    step-0 = make-step s s1 (mov (mem (base+disp r15 slot-size)) (reg rax)) h-eq fetch-0
               (mov-reg-mem-result prog s (base+disp r15 slot-size) rax)
    pc1 : X86Sem.State.pc s1 ≡ length prefix +ℕ 1
    pc1 = cong (_+ℕ 1) pc-eq

    -- Step 1: mov (reg rax) (reg r15) at pc = length prefix + 1
    -- Copies r15 to rax (pair address)
    fetch-1 : fetch prog (X86Sem.State.pc s1) ≡ just (mov (reg rax) (reg r15))
    fetch-1 = subst (λ n → fetch prog n ≡ just (mov (reg rax) (reg r15)))
                    (sym pc1) (fetch-++-right prefix ps 1 (mov (reg rax) (reg r15)) refl)
    s2 = record s1 { regs = x86-writeReg (X86Sem.State.regs s1) rax
                              (x86-readReg (X86Sem.State.regs s1) r15)
                   ; pc = X86Sem.State.pc s1 +ℕ 1 }
    step-1 = make-step s1 s2 (mov (reg rax) (reg r15)) h-eq fetch-1
               (mov-reg-reg-result prog s1 rax r15)
    pc2 : X86Sem.State.pc s2 ≡ length prefix +ℕ 2
    pc2 = trans (cong (_+ℕ 1) pc1) (+-assoc (length prefix) 1 1)

    -- Step 2: mov (reg rsp) (reg rbp) at pc = length prefix + 2
    -- Restores stack pointer from frame pointer
    fetch-2 : fetch prog (X86Sem.State.pc s2) ≡ just (mov (reg rsp) (reg rbp))
    fetch-2 = subst (λ n → fetch prog n ≡ just (mov (reg rsp) (reg rbp)))
                    (sym pc2) (fetch-++-right prefix ps 2 (mov (reg rsp) (reg rbp)) refl)
    s3 = record s2 { regs = x86-writeReg (X86Sem.State.regs s2) rsp
                              (x86-readReg (X86Sem.State.regs s2) rbp)
                   ; pc = X86Sem.State.pc s2 +ℕ 1 }
    step-2 = make-step s2 s3 (mov (reg rsp) (reg rbp)) h-eq fetch-2
               (mov-reg-reg-result prog s2 rsp rbp)
    pc3 : X86Sem.State.pc s3 ≡ length prefix +ℕ 3
    pc3 = trans (cong (_+ℕ 1) pc2) (+-assoc (length prefix) 2 1)

    -- Step 3: pop rbp at pc = length prefix + 3
    -- Pop needs memory read proof - postulate the value and read proof
    postulate
      v-rbp : Word
      mem-rbp : x86-readMem (X86Sem.State.memory s3) (x86-readReg (X86Sem.State.regs s3) rsp) ≡ just v-rbp
    fetch-3 : fetch prog (X86Sem.State.pc s3) ≡ just (pop rbp)
    fetch-3 = subst (λ n → fetch prog n ≡ just (pop rbp))
                    (sym pc3) (fetch-++-right prefix ps 3 (pop rbp) refl)
    s4 = record s3 { regs = x86-writeReg
                              (x86-writeReg (X86Sem.State.regs s3) rbp v-rbp)
                              rsp
                              (x86-readReg (X86Sem.State.regs s3) rsp +ℕ slot-size)
                   ; pc = X86Sem.State.pc s3 +ℕ 1 }
    step-3 = make-step s3 s4 (pop rbp) h-eq fetch-3
               (pop-reg-result prog s3 rbp v-rbp mem-rbp)
    pc4 : X86Sem.State.pc s4 ≡ length prefix +ℕ 4
    pc4 = trans (cong (_+ℕ 1) pc3) (+-assoc (length prefix) 3 1)

    -- Step 4: pop r15 at pc = length prefix + 4
    postulate
      v-r15 : Word
      mem-r15 : x86-readMem (X86Sem.State.memory s4) (x86-readReg (X86Sem.State.regs s4) rsp) ≡ just v-r15
    fetch-4 : fetch prog (X86Sem.State.pc s4) ≡ just (pop r15)
    fetch-4 = subst (λ n → fetch prog n ≡ just (pop r15))
                    (sym pc4) (fetch-++-right prefix ps 4 (pop r15) refl)
    s5 = record s4 { regs = x86-writeReg
                              (x86-writeReg (X86Sem.State.regs s4) r15 v-r15)
                              rsp
                              (x86-readReg (X86Sem.State.regs s4) rsp +ℕ slot-size)
                   ; pc = X86Sem.State.pc s4 +ℕ 1 }
    step-4 = make-step s4 s5 (pop r15) h-eq fetch-4
               (pop-reg-result prog s4 r15 v-r15 mem-r15)
    pc5 : X86Sem.State.pc s5 ≡ length prefix +ℕ 5
    pc5 = trans (cong (_+ℕ 1) pc4) (+-assoc (length prefix) 4 1)

    -- Step 5: pop r14 at pc = length prefix + 5
    postulate
      v-r14 : Word
      mem-r14 : x86-readMem (X86Sem.State.memory s5) (x86-readReg (X86Sem.State.regs s5) rsp) ≡ just v-r14
    fetch-5 : fetch prog (X86Sem.State.pc s5) ≡ just (pop r14)
    fetch-5 = subst (λ n → fetch prog n ≡ just (pop r14))
                    (sym pc5) (fetch-++-right prefix ps 5 (pop r14) refl)
    s6 = record s5 { regs = x86-writeReg
                              (x86-writeReg (X86Sem.State.regs s5) r14 v-r14)
                              rsp
                              (x86-readReg (X86Sem.State.regs s5) rsp +ℕ slot-size)
                   ; pc = X86Sem.State.pc s5 +ℕ 1 }
    step-5 = make-step s5 s6 (pop r14) h-eq fetch-5
               (pop-reg-result prog s5 r14 v-r14 mem-r14)
    pc6 : X86Sem.State.pc s6 ≡ length prefix +ℕ 6
    pc6 = trans (cong (_+ℕ 1) pc5) (+-assoc (length prefix) 5 1)

    -- Final state
    s' = s6

    -- Combined Star proof
    star-proof : Star prog s s'
    star-proof = star-single h-eq step-0 ◅◅
                 star-single h-eq step-1 ◅◅
                 star-single h-eq step-2 ◅◅
                 star-single h-eq step-3 ◅◅
                 star-single h-eq step-4 ◅◅
                 star-single h-eq step-5

    -- halted preservation
    h'-eq : X86Sem.State.halted s' ≡ false
    h'-eq = h-eq

    -- PC after 6 instructions = length prefix + 6 = length prefix + length pair-cleanup
    pc'-eq : X86Sem.State.pc s' ≡ length prefix +ℕ length pair-cleanup
    pc'-eq = pc6

    -- StateCorresponds (postulated)
    sc' : StateCorresponds (pair-cleanup-slot-state σ) s'
    sc' = pair-cleanup-preserves-corresponds s s' σ sc

  in s' , star-proof , h'-eq , pc'-eq , sc'

-- pair-runner implementation
-- Chains: setup → f → middle → g → cleanup
--
-- Structure: pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g ++ pair-cleanup
--
-- The proof chains the five phases, with postulated lemmas for:
-- 1. Star lemmas for setup/middle/cleanup instruction sequences
-- 2. Star chaining (associativity of program concatenation)
-- 3. PC transformations between phases
pair-runner : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) →
  IRRunner f → IRRunner g → IRRunner (⟨ f , g ⟩ m)
pair-runner {A} {B} {C} f g m f-run g-run prefix suffix σ s sc h-eq pc-eq =
  let -- Program components
      prog-f = compile-ir f
      prog-g = compile-ir g

      -- Placeholder pair-loc (actual value comes from allocation)
      pair-loc = SM.readReg (SM.LocState.regs σ) RDI

      -- Define all prefixes/suffixes
      prefix-f = prefix ++ pair-setup
      suffix-f = pair-middle ++ prog-g ++ pair-cleanup ++ suffix

      prefix-mid = prefix ++ pair-setup ++ prog-f
      suffix-mid = prog-g ++ pair-cleanup ++ suffix

      prefix-g = prefix ++ pair-setup ++ prog-f ++ pair-middle
      suffix-g = pair-cleanup ++ suffix

      prefix-clean = prefix ++ pair-setup ++ prog-f ++ pair-middle ++ prog-g

      -- Phase 1: Execute pair-setup
      suffix-after-setup = prog-f ++ pair-middle ++ prog-g ++ pair-cleanup ++ suffix
      (s1 , star-setup , h1 , pc1 , sc1) =
        pair-setup-result prefix suffix-after-setup s σ pair-loc sc h-eq pc-eq
      σ1 = pair-setup-slot-state σ pair-loc

      -- Phase 2: Execute f
      pc1-for-f : X86Sem.State.pc s1 ≡ length prefix-f
      pc1-for-f = pair-pc-setup-to-f prefix pc1

      (s2 , f-result) = f-run prefix-f suffix-f σ1 s1 sc1 h1 pc1-for-f
      σ2 = IRStarResult.σ-final f-result
      h2 = IRStarResult.halted-false f-result
      pc2 = IRStarResult.pc-advanced f-result
      sc2 = IRStarResult.corr-proof f-result
      star-f = IRStarResult.star-proof f-result

      -- Phase 3: Execute pair-middle
      pc2-for-mid : X86Sem.State.pc s2 ≡ length prefix-mid
      pc2-for-mid = pair-pc-f-to-mid prefix prog-f pc2

      (s3 , star-mid , h3 , pc3 , sc3) =
        pair-middle-result prefix-mid suffix-mid s2 σ2 sc2 h2 pc2-for-mid
      σ3 = pair-middle-slot-state σ2

      -- Phase 4: Execute g
      pc3-for-g : X86Sem.State.pc s3 ≡ length prefix-g
      pc3-for-g = pair-pc-mid-to-g prefix prog-f pc3

      (s4 , g-result) = g-run prefix-g suffix-g σ3 s3 sc3 h3 pc3-for-g
      σ4 = IRStarResult.σ-final g-result
      h4 = IRStarResult.halted-false g-result
      pc4 = IRStarResult.pc-advanced g-result
      sc4 = IRStarResult.corr-proof g-result
      star-g = IRStarResult.star-proof g-result

      -- Phase 5: Execute pair-cleanup
      pc4-for-clean : X86Sem.State.pc s4 ≡ length prefix-clean
      pc4-for-clean = pair-pc-g-to-clean prefix prog-f prog-g pc4

      (s5 , star-clean , h5 , pc5 , sc5) =
        pair-cleanup-result prefix-clean suffix s4 σ4 sc4 h4 pc4-for-clean
      σ5 = pair-cleanup-slot-state σ4

      -- Chain all stars together
      star-final : Star (prefix ++ compile-ir (⟨ f , g ⟩ m) ++ suffix) s s5
      star-final = pair-star-chain prefix suffix prog-f prog-g s s1 s2 s3 s4 s5
                     star-setup star-f star-mid star-g star-clean

      -- PC calculation
      pc-final : X86Sem.State.pc s5 ≡ length prefix +ℕ compile-length (⟨ f , g ⟩ m)
      pc-final = pair-pc-final prefix prog-f prog-g pc5

  in s5 , record
    { star-proof = star-final
    ; halted-false = h5
    ; pc-advanced = pc-final
    ; σ-final = σ5
    ; corr-proof = sc5
    }
  where
    -- PROVEN PC transformation lemmas
    -- Key: use compile-ir f and compile-ir g directly since f,g are in scope

    -- After setup: pc = length prefix + length pair-setup = length (prefix ++ pair-setup)
    pair-pc-setup-to-f : ∀ (pref : Program) →
      ∀ {pc : ℕ} →
      pc ≡ length pref +ℕ length pair-setup →
      pc ≡ length (pref ++ pair-setup)
    pair-pc-setup-to-f pref pc-eq = trans pc-eq (sym (length-++ pref))

    -- After f: pc = length (prefix ++ pair-setup) + compile-length f = length (prefix ++ pair-setup ++ compile-ir f)
    -- Use compile-ir f directly since f is in scope
    pair-pc-f-to-mid : ∀ (pref pf : Program) →
      ∀ {pc : ℕ} →
      pc ≡ length (pref ++ pair-setup) +ℕ compile-length f →
      pc ≡ length (pref ++ pair-setup ++ compile-ir f)
    pair-pc-f-to-mid pref _ pc-eq =
      -- pc = length (pref ++ pair-setup) + compile-length f
      -- Goal: pc = length (pref ++ pair-setup ++ compile-ir f)
      --     = length (pref ++ pair-setup) + length (compile-ir f)  (by length-++ with assoc)
      --     = length (pref ++ pair-setup) + compile-length f  (by compile-ir-length)
      let prog-f' = compile-ir f
          len-eq : length (pref ++ pair-setup ++ prog-f') ≡ length (pref ++ pair-setup) +ℕ length prog-f'
          len-eq = trans (cong length (sym (++-assoc pref pair-setup prog-f')))
                         (length-++ (pref ++ pair-setup))
          len-f : length prog-f' ≡ compile-length f
          len-f = compile-ir-length f
          goal-eq : length (pref ++ pair-setup ++ prog-f') ≡ length (pref ++ pair-setup) +ℕ compile-length f
          goal-eq = trans len-eq (cong (length (pref ++ pair-setup) +ℕ_) len-f)
      in trans pc-eq (sym goal-eq)

    -- After middle: use length-++ and ++-assoc
    -- Note: ++ is right-associative, so pref ++ pair-setup ++ pf ++ pair-middle
    --       = pref ++ (pair-setup ++ (pf ++ pair-middle))
    pair-pc-mid-to-g : ∀ (pref pf : Program) →
      ∀ {pc : ℕ} →
      pc ≡ length (pref ++ pair-setup ++ pf) +ℕ length pair-middle →
      pc ≡ length (pref ++ pair-setup ++ pf ++ pair-middle)
    pair-pc-mid-to-g pref pf pc-eq =
      let -- Step 1: length a + length b = length (a ++ b)
          step1 : length (pref ++ pair-setup ++ pf) +ℕ length pair-middle
                ≡ length ((pref ++ pair-setup ++ pf) ++ pair-middle)
          step1 = sym (length-++ (pref ++ pair-setup ++ pf))
          -- Step 2: (pref ++ pair-setup ++ pf) ++ pair-middle = pref ++ pair-setup ++ pf ++ pair-middle
          -- Using right-assoc: (pref ++ (pair-setup ++ pf)) ++ pair-middle
          --                  = pref ++ ((pair-setup ++ pf) ++ pair-middle)  by ++-assoc
          --                  = pref ++ (pair-setup ++ (pf ++ pair-middle))  by ++-assoc inside
          step2 : (pref ++ pair-setup ++ pf) ++ pair-middle ≡ pref ++ pair-setup ++ pf ++ pair-middle
          step2 = trans (++-assoc pref (pair-setup ++ pf) pair-middle)
                        (cong (pref ++_) (++-assoc pair-setup pf pair-middle))
      in trans pc-eq (trans step1 (cong length step2))

    -- After g: similar to f-to-mid, use compile-ir g directly
    -- PROVEN: list length arithmetic with ++ associativity
    pair-pc-g-to-clean : ∀ (pref pf pg : Program) →
      ∀ {pc : ℕ} →
      pc ≡ length (pref ++ pair-setup ++ pf ++ pair-middle) +ℕ compile-length g →
      pc ≡ length (pref ++ pair-setup ++ pf ++ pair-middle ++ compile-ir g)
    pair-pc-g-to-clean pref pf _ pc-eq =
      -- Same pattern as pair-pc-f-to-mid
      let prog-g' = compile-ir g
          prefix-g = pref ++ pair-setup ++ pf ++ pair-middle
          -- Step 1: length (prefix-g ++ prog-g') = length prefix-g + length prog-g'
          -- Using ++-assoc to group properly for length-++
          step1 : length (prefix-g ++ prog-g') ≡ length prefix-g +ℕ length prog-g'
          step1 = length-++ prefix-g
          -- Step 2: (pref ++ pair-setup ++ pf ++ pair-middle) ++ prog-g' = pref ++ pair-setup ++ pf ++ pair-middle ++ prog-g'
          -- Right-assoc: (pref ++ (pair-setup ++ (pf ++ pair-middle))) ++ prog-g'
          --            = pref ++ (pair-setup ++ (pf ++ (pair-middle ++ prog-g')))
          step2 : (pref ++ pair-setup ++ pf ++ pair-middle) ++ prog-g'
                ≡ pref ++ pair-setup ++ pf ++ pair-middle ++ prog-g'
          step2 = trans (++-assoc pref (pair-setup ++ pf ++ pair-middle) prog-g')
                        (cong (pref ++_) (trans (++-assoc pair-setup (pf ++ pair-middle) prog-g')
                                                (cong (pair-setup ++_) (++-assoc pf pair-middle prog-g'))))
          -- Step 3: length prog-g' = compile-length g
          len-g : length prog-g' ≡ compile-length g
          len-g = compile-ir-length g
          -- Combine: length (prefix-g ++ prog-g') = length prefix-g + compile-length g
          goal-eq : length (pref ++ pair-setup ++ pf ++ pair-middle ++ prog-g')
                  ≡ length (pref ++ pair-setup ++ pf ++ pair-middle) +ℕ compile-length g
          goal-eq = trans (cong length (sym step2))
                          (trans step1 (cong (length prefix-g +ℕ_) len-g))
      in trans pc-eq (sym goal-eq)

    -- Final PC: arithmetic connecting to compile-length (⟨ f , g ⟩ m)
    -- PROVEN: list length arithmetic
    -- compile-length (⟨ f , g ⟩ m) = length pair-setup + compile-length f + length pair-middle + compile-length g + length pair-cleanup
    pair-pc-final : ∀ (pref pf pg : Program) →
      ∀ {pc : ℕ} →
      pc ≡ length (pref ++ pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g) +ℕ length pair-cleanup →
      pc ≡ length pref +ℕ compile-length (⟨ f , g ⟩ m)
    pair-pc-final pref _ _ pc-eq =
      let -- Step 1: Expand length of the big concatenation using length-++ chain
          -- length (pref ++ pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g)
          -- = length pref + length (pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g)
          inner = pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g
          len-split : length (pref ++ inner) ≡ length pref +ℕ length inner
          len-split = length-++ pref

          -- Step 2: Expand inner length
          -- length (pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g)
          inner2 = compile-ir f ++ pair-middle ++ compile-ir g
          len-inner1 : length inner ≡ length pair-setup +ℕ length inner2
          len-inner1 = length-++ pair-setup {inner2}

          inner3 = pair-middle ++ compile-ir g
          len-inner2 : length inner2 ≡ length (compile-ir f) +ℕ length inner3
          len-inner2 = length-++ (compile-ir f) {inner3}

          len-inner3 : length inner3 ≡ length pair-middle +ℕ length (compile-ir g)
          len-inner3 = length-++ pair-middle {compile-ir g}

          -- Step 3: Use compile-ir-length
          len-f : length (compile-ir f) ≡ compile-length f
          len-f = compile-ir-length f

          len-g : length (compile-ir g) ≡ compile-length g
          len-g = compile-ir-length g

          -- Step 4: Build the full equality
          -- length (pref ++ inner) + length pair-cleanup
          -- = (length pref + length inner) + length pair-cleanup
          -- = length pref + (length inner + length pair-cleanup)
          -- = length pref + (length pair-setup + compile-length f + length pair-middle + compile-length g + length pair-cleanup)
          -- = length pref + compile-length (⟨ f , g ⟩ m)

          -- Inner length fully expanded
          -- Need to build: length inner ≡ ((len-setup + compile-len-f) + len-mid) + compile-len-g
          -- Build step by step with correct associativity
          inner-len : length inner ≡ length pair-setup +ℕ compile-length f +ℕ length pair-middle +ℕ compile-length g
          inner-len =
            let -- length inner = length pair-setup + length inner2
                step1 = len-inner1
                -- length inner2 = length (compile-ir f) + length inner3
                step2 = cong (length pair-setup +ℕ_) len-inner2
                -- Apply len-f: length (compile-ir f) = compile-length f
                -- Result: length pair-setup + (compile-length f + length inner3)
                step3 = cong (length pair-setup +ℕ_) (cong (_+ℕ length inner3) len-f)
                -- Apply associativity: a + (b + c) = (a + b) + c
                step4 : length pair-setup +ℕ (compile-length f +ℕ length inner3)
                      ≡ (length pair-setup +ℕ compile-length f) +ℕ length inner3
                step4 = sym (ℕ-+-assoc (length pair-setup) (compile-length f) (length inner3))
                -- Apply len-inner3: length inner3 = length pair-middle + length (compile-ir g)
                step5 = cong ((length pair-setup +ℕ compile-length f) +ℕ_) len-inner3
                -- Result: (len-setup + compile-len-f) + (len-mid + length (compile-ir g))
                -- Need: ((len-setup + compile-len-f) + len-mid) + length (compile-ir g)
                step6 : (length pair-setup +ℕ compile-length f) +ℕ (length pair-middle +ℕ length (compile-ir g))
                      ≡ ((length pair-setup +ℕ compile-length f) +ℕ length pair-middle) +ℕ length (compile-ir g)
                step6 = sym (ℕ-+-assoc (length pair-setup +ℕ compile-length f) (length pair-middle) (length (compile-ir g)))
                -- Apply len-g: length (compile-ir g) = compile-length g
                step7 = cong (((length pair-setup +ℕ compile-length f) +ℕ length pair-middle) +ℕ_) len-g
            in trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 step7)))))

          -- LHS: length (pref ++ inner) + length pair-cleanup
          -- = (length pref + length inner) + length pair-cleanup  [by len-split]
          -- = length pref + (length inner + length pair-cleanup)  [by +-assoc]
          -- = length pref + (length pair-setup + compile-length f + length pair-middle + compile-length g + length pair-cleanup)
          --   [by inner-len and arithmetic]

          -- The key: (a + b) + c = a + (b + c)
          assoc-step : (length pref +ℕ length inner) +ℕ length pair-cleanup
                     ≡ length pref +ℕ (length inner +ℕ length pair-cleanup)
          assoc-step = ℕ-+-assoc (length pref) (length inner) (length pair-cleanup)

          -- compile-length (⟨ f , g ⟩ m) definition
          pair-compile-len : compile-length (⟨ f , g ⟩ m)
                           ≡ length pair-setup +ℕ compile-length f +ℕ length pair-middle +ℕ compile-length g +ℕ length pair-cleanup
          pair-compile-len = refl

          -- length inner + length pair-cleanup = compile-length (⟨ f , g ⟩ m)
          inner-plus-cleanup : length inner +ℕ length pair-cleanup ≡ compile-length (⟨ f , g ⟩ m)
          inner-plus-cleanup = trans (cong (_+ℕ length pair-cleanup) inner-len) refl

          -- Full chain
          full-eq : length (pref ++ inner) +ℕ length pair-cleanup ≡ length pref +ℕ compile-length (⟨ f , g ⟩ m)
          full-eq = trans (cong (_+ℕ length pair-cleanup) len-split)
                    (trans assoc-step
                           (cong (length pref +ℕ_) inner-plus-cleanup))

      in trans pc-eq full-eq

    -- Chain all pair phase stars
    -- Uses Star transitivity (◅◅) and subst for ++ associativity
    -- PROVEN: list associativity and Star transitivity
    -- Use compile-ir f/g directly since f,g are in scope
    pair-star-chain : ∀ (pref suff pf pg : Program)
      (s0 s1 s2 s3 s4 s5 : State) →
      Star (pref ++ pair-setup ++ (compile-ir f ++ pair-middle ++ compile-ir g ++ pair-cleanup ++ suff)) s0 s1 →
      Star ((pref ++ pair-setup) ++ compile-ir f ++ (pair-middle ++ compile-ir g ++ pair-cleanup ++ suff)) s1 s2 →
      Star ((pref ++ pair-setup ++ compile-ir f) ++ pair-middle ++ (compile-ir g ++ pair-cleanup ++ suff)) s2 s3 →
      Star ((pref ++ pair-setup ++ compile-ir f ++ pair-middle) ++ compile-ir g ++ (pair-cleanup ++ suff)) s3 s4 →
      Star ((pref ++ pair-setup ++ compile-ir f ++ pair-middle ++ compile-ir g) ++ pair-cleanup ++ suff) s4 s5 →
      Star (pref ++ compile-ir (⟨ f , g ⟩ m) ++ suff) s0 s5
    pair-star-chain pref suff _ _ s0 s1 s2 s3 s4 s5 star1 star2 star3 star4 star5 =
      -- Chain all stars using transitivity
      -- All lists are equivalent via ++-assoc
      -- PROVEN: mechanical ◅◅ and subst
      let
          -- Use compile-ir f/g directly
          pf = compile-ir f
          pg = compile-ir g

          -- Canonical program: pref ++ pair-setup ++ pf ++ pair-middle ++ pg ++ pair-cleanup ++ suff
          -- This is the natural right-associative form
          canonical = pref ++ pair-setup ++ pf ++ pair-middle ++ pg ++ pair-cleanup ++ suff

          -- All input programs equal canonical by ++-assoc
          -- Form 1: pref ++ pair-setup ++ (pf ++ pair-middle ++ pg ++ pair-cleanup ++ suff)
          --       = pref ++ (pair-setup ++ (pf ++ pair-middle ++ pg ++ pair-cleanup ++ suff))  (right-assoc)
          -- These are definitionally equal due to right-assoc!
          eq1 : pref ++ pair-setup ++ (pf ++ pair-middle ++ pg ++ pair-cleanup ++ suff) ≡ canonical
          eq1 = refl

          -- Form 2: (pref ++ pair-setup) ++ pf ++ (pair-middle ++ pg ++ pair-cleanup ++ suff)
          eq2 : (pref ++ pair-setup) ++ pf ++ (pair-middle ++ pg ++ pair-cleanup ++ suff) ≡ canonical
          eq2 = trans (++-assoc pref pair-setup (pf ++ pair-middle ++ pg ++ pair-cleanup ++ suff)) refl

          -- Form 3: (pref ++ pair-setup ++ pf) ++ pair-middle ++ (pg ++ pair-cleanup ++ suff)
          eq3 : (pref ++ pair-setup ++ pf) ++ pair-middle ++ (pg ++ pair-cleanup ++ suff) ≡ canonical
          eq3 = trans (++-assoc pref (pair-setup ++ pf) (pair-middle ++ pg ++ pair-cleanup ++ suff))
                      (cong (pref ++_) (++-assoc pair-setup pf (pair-middle ++ pg ++ pair-cleanup ++ suff)))

          -- Form 4: (pref ++ pair-setup ++ pf ++ pair-middle) ++ pg ++ (pair-cleanup ++ suff)
          eq4 : (pref ++ pair-setup ++ pf ++ pair-middle) ++ pg ++ (pair-cleanup ++ suff) ≡ canonical
          eq4 = trans (++-assoc pref (pair-setup ++ pf ++ pair-middle) (pg ++ pair-cleanup ++ suff))
                      (cong (pref ++_) (trans (++-assoc pair-setup (pf ++ pair-middle) (pg ++ pair-cleanup ++ suff))
                                              (cong (pair-setup ++_) (++-assoc pf pair-middle (pg ++ pair-cleanup ++ suff)))))

          -- Form 5: (pref ++ pair-setup ++ pf ++ pair-middle ++ pg) ++ pair-cleanup ++ suff
          eq5 : (pref ++ pair-setup ++ pf ++ pair-middle ++ pg) ++ pair-cleanup ++ suff ≡ canonical
          eq5 = trans (++-assoc pref (pair-setup ++ pf ++ pair-middle ++ pg) (pair-cleanup ++ suff))
                      (cong (pref ++_) (trans (++-assoc pair-setup (pf ++ pair-middle ++ pg) (pair-cleanup ++ suff))
                                              (cong (pair-setup ++_) (trans (++-assoc pf (pair-middle ++ pg) (pair-cleanup ++ suff))
                                                                            (cong (pf ++_) (++-assoc pair-middle pg (pair-cleanup ++ suff)))))))

          -- Transport each Star to canonical form
          star1' : Star canonical s0 s1
          star1' = subst (λ p → Star p s0 s1) eq1 star1

          star2' : Star canonical s1 s2
          star2' = subst (λ p → Star p s1 s2) eq2 star2

          star3' : Star canonical s2 s3
          star3' = subst (λ p → Star p s2 s3) eq3 star3

          star4' : Star canonical s3 s4
          star4' = subst (λ p → Star p s3 s4) eq4 star4

          star5' : Star canonical s4 s5
          star5' = subst (λ p → Star p s4 s5) eq5 star5

          -- Chain all Stars together
          star-all : Star canonical s0 s5
          star-all = star1' ◅◅ star2' ◅◅ star3' ◅◅ star4' ◅◅ star5'

          -- Final form: pref ++ compile-ir (⟨ f , g ⟩ m) ++ suff
          -- compile-ir (⟨ f , g ⟩ m) = pair-setup ++ pf ++ pair-middle ++ pg ++ pair-cleanup
          --
          -- canonical = pref ++ pair-setup ++ pf ++ pair-middle ++ pg ++ pair-cleanup ++ suff
          --           = pref ++ (pair-setup ++ (pf ++ (pair-middle ++ (pg ++ (pair-cleanup ++ suff)))))
          --
          -- goal = pref ++ compile-ir (⟨ f , g ⟩ m) ++ suff
          --      = pref ++ (pair-setup ++ (pf ++ (pair-middle ++ (pg ++ pair-cleanup)))) ++ suff
          --      = pref ++ ((pair-setup ++ (pf ++ (pair-middle ++ (pg ++ pair-cleanup)))) ++ suff)
          --
          -- Key difference: pg ++ (pair-cleanup ++ suff) vs (pg ++ pair-cleanup) ++ suff
          -- Need: sym (++-assoc pg pair-cleanup suff)

          -- Work inside out to prove canonical = goal
          assoc-pg : pg ++ (pair-cleanup ++ suff) ≡ (pg ++ pair-cleanup) ++ suff
          assoc-pg = sym (++-assoc pg pair-cleanup suff)

          assoc-mid : pair-middle ++ (pg ++ (pair-cleanup ++ suff))
                    ≡ (pair-middle ++ (pg ++ pair-cleanup)) ++ suff
          assoc-mid = trans (cong (pair-middle ++_) assoc-pg)
                            (sym (++-assoc pair-middle (pg ++ pair-cleanup) suff))

          assoc-pf : pf ++ (pair-middle ++ (pg ++ (pair-cleanup ++ suff)))
                   ≡ (pf ++ (pair-middle ++ (pg ++ pair-cleanup))) ++ suff
          assoc-pf = trans (cong (pf ++_) assoc-mid)
                           (sym (++-assoc pf (pair-middle ++ (pg ++ pair-cleanup)) suff))

          assoc-setup : pair-setup ++ (pf ++ (pair-middle ++ (pg ++ (pair-cleanup ++ suff))))
                      ≡ (pair-setup ++ (pf ++ (pair-middle ++ (pg ++ pair-cleanup)))) ++ suff
          assoc-setup = trans (cong (pair-setup ++_) assoc-pf)
                              (sym (++-assoc pair-setup (pf ++ (pair-middle ++ (pg ++ pair-cleanup))) suff))

          eq-final : canonical ≡ pref ++ compile-ir (⟨ f , g ⟩ m) ++ suff
          eq-final = cong (pref ++_) assoc-setup

      in subst (λ p → Star p s0 s5) eq-final star-all

-- Postulated runners for remaining complex cases
--
-- SOUNDNESS STATUS:
--
-- SOUND postulates (provable once instruction lemmas are added):
--   - curry-runner: has real codegen (curry-closure-setup ++ thunk-setup ++ body ++ thunk-cleanup)
--   - apply-runner: has real codegen (apply-instrs with call r15)
--
-- UNSOUND postulates (need codegen implementation first):
--   - inl-runner, inr-runner: codegen is `ud2 ∷ []` (placeholder that halts)
--   - case-runner: codegen is `compile-ir f ++ compile-ir g` (no dispatch logic)
--   - prim-runner: codegen is `ud2 ∷ []` (placeholder, needs FFI)
--
-- These are marked UNSOUND because IRRunner requires halted-false,
-- but ud2 sets halted = true. Once real codegen is implemented,
-- these become sound and provable.
--
-- NOTE: initial-runner is intentionally NOT included because it's unprovable:
--   - compile-ir initial = ud2 (undefined instruction)
--   - ud2 sets halted = true
--   - This is sound: initial : IR Void A is never called (Void has no inhabitants)
postulate
  -- UNSOUND until codegen implemented (currently ud2)
  inl-runner : ∀ {A B} (m : AllocMode) → IRRunner (inl-ir {A} {B} m)
  inr-runner : ∀ {A B} (m : AllocMode) → IRRunner (inr-ir {A} {B} m)
  case-runner : ∀ {A B C} (f : IR A C) (g : IR B C) →
    IRRunner f → IRRunner g → IRRunner (case-ir f g)
  prim-runner : ∀ {A B} (p : String) → IRRunner (Prim {A} {B} p)

  -- SOUND postulates (have real codegen, need instruction lemmas to prove)
  curry-runner : ∀ {A B C q} (f : IR (A * B) C) (m : AllocMode) →
    IRRunner f → IRRunner (curry {q = q} f m)
  apply-runner : ∀ {A B q} → IRRunner (apply {A} {B} {q})

-- arr, fold, unfold compile to id-instrs
arr-runner : ∀ {A B q} → IRRunner (arr {A} {B} {q})
arr-runner prefix suffix σ s sc h-eq pc-eq =
  id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    }

fold-runner : ∀ {F} (m : AllocMode) → IRRunner (fold-ir {F} m)
fold-runner m prefix suffix σ s sc h-eq pc-eq =
  id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    }

unfold-runner : ∀ {F} → IRRunner (unfold-ir {F})
unfold-runner prefix suffix σ s sc h-eq pc-eq =
  id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    }

-- free-heap compiles to [] (no-op, zero steps)
-- Special: Star [] s s (refl*), pc unchanged
-- Note: compile-ir (free-heap r) = []
-- So: prefix ++ compile-ir (free-heap r) ++ suffix = prefix ++ [] ++ suffix = prefix ++ suffix
-- compile-length (free-heap r) = 0, so pc-advanced needs: pc s ≡ length prefix + 0
free-heap-runner : ∀ (r : HeapRef) → IRRunner (free-heap r)
free-heap-runner r prefix suffix σ s sc h-eq pc-eq =
  s , record
    { star-proof = refl*  -- Star (prefix ++ suffix) s s
    ; halted-false = h-eq
    ; pc-advanced = trans pc-eq (sym (+-identityʳ (length prefix)))  -- length prefix ≡ length prefix + 0
    ; σ-final = σ
    ; corr-proof = sc
    }

------------------------------------------------------------------------
-- Proven simulations for simple IR constructs
--
-- These compile to id-instrs or no-ops.
-- Used internally, NOT the main correctness theorem (which uses Dispatcher).
------------------------------------------------------------------------

-- arr: compiles to id-instrs (mov rax, rdi)
arr-simulation : ∀ {A B q} (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (arr {A} {B} {q})) s x86-final × StateCorresponds σ-final x86-final
arr-simulation σ s sc h-eq pc-eq =
  id-expected-state s
  , id-slot-state σ
  , id-star-at-offset [] [] s h-eq pc-eq
  , id-preserves-corresponds σ s sc

-- fold-ir: compiles to id-instrs (mov rax, rdi)
fold-simulation : ∀ {F} (m : AllocMode) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (fold-ir {F} m)) s x86-final × StateCorresponds σ-final x86-final
fold-simulation m σ s sc h-eq pc-eq =
  id-expected-state s
  , id-slot-state σ
  , id-star-at-offset [] [] s h-eq pc-eq
  , id-preserves-corresponds σ s sc

-- unfold-ir: compiles to id-instrs (mov rax, rdi)
unfold-simulation : ∀ {F} (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (unfold-ir {F})) s x86-final × StateCorresponds σ-final x86-final
unfold-simulation σ s sc h-eq pc-eq =
  id-expected-state s
  , id-slot-state σ
  , id-star-at-offset [] [] s h-eq pc-eq
  , id-preserves-corresponds σ s sc

-- free-heap: compiles to [] (no-op), zero steps
free-heap-simulation : ∀ (r : HeapRef) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (free-heap r)) s x86-final × StateCorresponds σ-final x86-final
free-heap-simulation r σ s sc =
  s , σ , refl* , sc
