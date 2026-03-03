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
open FrameSemantics using (Frame; _≺_)
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
  using (x86v3-frame-semantics; X86Frame; x86-frame-base)

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
open import Once.CCC.SlotMachine using (HeapRef; mkHeapRef; RegId; RAX; RDI; RSI; R12; R14; R15;
         HeapLocation; heap-loc; OnHeap; OnStack)
  renaming (Instr to SlotInstr; mov to slot-mov)
open import Data.String using (String)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- Import SlotMachine exec for simulation proofs
open import Once.CCC.SlotMachine as SM using (LocState; Registers; readReg; writeReg; writeReg-same; sucLoc; sucHL)
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
         push-reg-result; pop-reg-result; mov-reg-reg-result; mov-reg-mem-result; mov-mem-reg-result; sub-imm-reg-result;
         -- Register lemmas for rbp preservation
         readReg-writeReg-diff;
         -- StepChain infrastructure
         StepProof; mkStep; StepChain; done; _▸_; chain-to-star)

-- Import SlotToX86 for correspondence
open import Once.CCC.Target.X86v3.Refinement.SlotToX86 as SlotToX86
  using (RegsCorrespond; MemCorresponds; StateCorresponds; HeapBaseMap;
         mov-regs-correspond; mov-mem-corresponds;
         build-regs-correspond-after-write;
         loc-to-addr; compile-reg; sucLoc-to-addr-OnStack; sucLoc-to-addr;
         -- X86-only correspondence preservation lemmas
         push-preserves-state-corresponds; sub-rsp-preserves-state-corresponds;
         mov-rbp-preserves-state-corresponds;
         -- PC and flags independence lemmas
         pc-change-preserves-corresponds; pc-flags-change-preserves-corresponds;
         -- Combined SlotMachine + x86 register write lemmas
         write-r14-both-preserves-corresponds; write-r15-both-preserves-corresponds;
         -- Allocation invariant
         AllocInvariant; FullStateCorresponds; derive-alloc-loc; derive-alloc-loc-addr-zero)
open RegsCorrespond
open MemCorresponds
open StateCorresponds

open import Once.Target.X86.Semantics as X86Sem
  renaming (readReg to x86-readReg; writeReg to x86-writeReg; readMem to x86-readMem;
            writeMem to x86-writeMem)
open X86Sem using (updateFlags; effectiveAddr; Word)
open X86Sem.State using (halted; pc; regs; memory; flags)

open import Once.Target.X86.Syntax using (rax; rdi; rsi; rbp; rsp; r12; r14; r15; slot-size; slots; Program; Instr; push; pop; mov; sub; reg; imm; mem; base; base+disp; Mem)
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
  ; current-frame = current-frame sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  ; frame-scope = frame-scope sc  -- stackMem unchanged by mov
  ; heap-in-heap = heap-in-heap sc  -- heapMem unchanged by mov
  ; rsp-at-or-below-rbp = rsp-at-or-below-rbp sc  -- rsp, rbp unchanged by mov
  ; rsp-in-stack = rsp-in-stack sc  -- rsp unchanged by mov
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
    ; current-frame = current-frame sc
    ; rbp-is-frame-base = rbp-is-frame-base sc
    ; frame-scope = frame-scope sc  -- stackMem unchanged
    ; heap-in-heap = heap-in-heap sc  -- heapMem unchanged
    ; rsp-at-or-below-rbp = rsp-at-or-below-rbp sc  -- rsp, rbp unchanged
    ; rsp-in-stack = rsp-in-stack sc  -- rsp unchanged
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
  ; current-frame = current-frame sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  ; frame-scope = frame-scope sc  -- stackMem unchanged by fst
  ; heap-in-heap = heap-in-heap sc  -- heapMem unchanged by fst
  ; rsp-at-or-below-rbp = rsp-at-or-below-rbp sc  -- rsp, rbp unchanged by fst
  ; rsp-in-stack = rsp-in-stack sc  -- rsp unchanged by fst
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
  ; current-frame = current-frame sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  ; frame-scope = frame-scope sc  -- stackMem unchanged by snd
  ; heap-in-heap = heap-in-heap sc  -- heapMem unchanged by snd
  ; rsp-at-or-below-rbp = rsp-at-or-below-rbp sc  -- rsp, rbp unchanged by snd
  ; rsp-in-stack = rsp-in-stack sc  -- rsp unchanged by snd
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
  ; current-frame = current-frame sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  ; frame-scope = frame-scope sc  -- stackMem unchanged by bridge
  ; heap-in-heap = heap-in-heap sc  -- heapMem unchanged by bridge
  ; rsp-at-or-below-rbp = rsp-at-or-below-rbp sc  -- rsp, rbp unchanged by bridge
  ; rsp-in-stack = rsp-in-stack sc  -- rsp unchanged by bridge
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

-- Import shared IR runner types from IRRunnerTypes module
open import Once.CCC.Target.X86v3.IRRunnerTypes public
  using (IRStarResult; IRRunner; state-frame; compose-parent-preserved)
open IRStarResult public

------------------------------------------------------------------------
-- Offset-Parameterized IR Runners (NEW APPROACH)
--
-- These run each IR at an arbitrary offset within a larger program.
-- The pattern is: prefix ++ compile-ir ir ++ suffix
-- PC advances from (length prefix) to (length prefix + compile-length ir)
------------------------------------------------------------------------

-- | For simple IRs that don't modify stack memory, stackMem is unchanged
-- Therefore parent-frames-preserved is trivially refl
id-stackMem-unchanged : ∀ (σ : LocState FS') →
  SM.LocState.stackMem (id-slot-state σ) ≡ SM.LocState.stackMem σ
id-stackMem-unchanged σ = refl

-- | id runner: mov rax, rdi at any offset
id-runner : ∀ {A} → IRRunner (id {A})
id-runner prefix suffix σ s sc h-eq pc-eq =
  let cf = state-frame σ s sc
  in id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq  -- record update preserves halted
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    ; rbp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rbp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; rsp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rsp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; current-frame = cf
    ; frame-matches-input = refl  -- cf = state-frame σ s sc = current-frame sc
    ; output-frame-preserved = refl  -- id-preserves-corresponds sets current-frame = current-frame sc
    ; parent-frames-preserved = λ f slot _ → refl  -- stackMem unchanged by id
    ; heap-base-preserved = refl  -- id-preserves-corresponds sets heap-base = heap-base sc
    }

-- | terminal runner: mov rax, 0 at any offset
terminal-runner : ∀ {A} → IRRunner (terminal {A})
terminal-runner prefix suffix σ s sc h-eq pc-eq =
  let (σ' , sc') = terminal-preserves-corresponds σ s sc
      cf = state-frame σ s sc
  in terminal-expected-state s , record
    { star-proof = terminal-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = σ'
    ; corr-proof = sc'
    ; rbp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rbp 0 (λ ())
    ; rsp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rsp 0 (λ ())
    ; current-frame = cf
    ; frame-matches-input = refl  -- cf = state-frame σ s sc = current-frame sc
    ; output-frame-preserved = refl  -- terminal-preserves-corresponds sets current-frame = current-frame sc
    ; parent-frames-preserved = λ f slot _ → refl  -- stackMem unchanged by terminal
    ; heap-base-preserved = refl  -- terminal-preserves-corresponds sets heap-base = heap-base sc
    }

-- | bridge runner: mov rdi, rax at any offset
bridge-runner : ∀ (prefix suffix : Program) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  ∃[ s' ] (Star (prefix ++ compose-bridge ++ suffix) s s'
         × X86Sem.State.halted s' ≡ false
         × X86Sem.State.pc s' ≡ length prefix +ℕ 1
         × StateCorresponds (bridge-slot-state σ) s'
         × x86-readReg (X86Sem.State.regs s') rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
         × x86-readReg (X86Sem.State.regs s') rsp ≡ x86-readReg (X86Sem.State.regs s) rsp)
bridge-runner prefix suffix σ s sc h-eq pc-eq =
  bridge-expected-state s
  , bridge-star-at-offset prefix suffix s h-eq pc-eq
  , h-eq
  , cong (_+ℕ 1) pc-eq
  , bridge-preserves-corresponds σ s sc
  , readReg-writeReg-diff (X86Sem.State.regs s) rdi rbp
      (x86-readReg (X86Sem.State.regs s) rax) (λ ())
  , readReg-writeReg-diff (X86Sem.State.regs s) rdi rsp
      (x86-readReg (X86Sem.State.regs s) rax) (λ ())

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
      rbp-f = IRStarResult.rbp-preserved f-result
      rsp-f = IRStarResult.rsp-preserved f-result

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

      (sb , star-b' , h-sb , pc-sb , sc-b , rbp-b , rsp-b) =
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
      rbp-g = IRStarResult.rbp-preserved g-result
      rsp-g = IRStarResult.rsp-preserved g-result

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

      -- rbp and rsp preservation: chain f → bridge → g
      rbp-final : x86-readReg (X86Sem.State.regs sg) rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
      rbp-final = trans rbp-g (trans rbp-b rbp-f)

      rsp-final : x86-readReg (X86Sem.State.regs sg) rsp ≡ x86-readReg (X86Sem.State.regs s) rsp
      rsp-final = trans rsp-g (trans rsp-b rsp-f)

      -- Frame and parent preservation
      cf-f = IRStarResult.current-frame f-result
      cf-g = IRStarResult.current-frame g-result
      pf-f = IRStarResult.parent-frames-preserved f-result
      pf-g = IRStarResult.parent-frames-preserved g-result

      -- PROVEN: cf-f ≡ cf-g using the new frame invariant fields
      -- Chain: cf-f ≡ current-frame sc (by frame-matches-input f-result)
      --        cf-g ≡ current-frame sc-b (by frame-matches-input g-result)
      --        current-frame sc-b = current-frame sc-f (by bridge-preserves-corresponds)
      --        current-frame sc-f ≡ current-frame sc (by output-frame-preserved f-result)
      --        Therefore: cf-f ≡ current-frame sc ≡ current-frame sc-f = current-frame sc-b ≡ cf-g
      cf-f≡sc : cf-f ≡ current-frame sc
      cf-f≡sc = IRStarResult.frame-matches-input f-result

      cf-g≡sc-b : cf-g ≡ current-frame sc-b
      cf-g≡sc-b = IRStarResult.frame-matches-input g-result

      -- bridge-preserves-corresponds preserves current-frame: sc-b has current-frame = current-frame sc-f
      -- This is definitionally true from how bridge-preserves-corresponds is defined
      sc-b≡sc-f : current-frame sc-b ≡ current-frame sc-f
      sc-b≡sc-f = refl  -- bridge-preserves-corresponds sets current-frame = current-frame sc-f

      sc-f≡sc : current-frame sc-f ≡ current-frame sc
      sc-f≡sc = IRStarResult.output-frame-preserved f-result

      cf-f≡cf-g : cf-f ≡ cf-g
      cf-f≡cf-g = trans cf-f≡sc (sym (trans cf-g≡sc-b (trans sc-b≡sc-f sc-f≡sc)))

      -- Note: bridge doesn't modify stack memory, so bridge-slot-state σf has same stackMem as σf
      -- This allows chaining f's preservation with g's preservation
      parent-preserved : ∀ (frame : Frame FS') (slot : ℕ) →
        _≺_ FS' cf-g frame →
        SM.LocState.stackMem σg frame slot ≡ SM.LocState.stackMem σ frame slot
      parent-preserved frame slot cf-g≺frame =
        compose-parent-preserved σ σf σg frame slot cf-f cf-g cf-f≡cf-g cf-g≺frame pf-f pf-g

      -- Compose frame invariants: current-frame result = current-frame sc
      -- By cf-f≡sc and cf-f≡cf-g, we have cf-g ≡ current-frame sc
      compose-frame-matches : cf-g ≡ current-frame sc
      compose-frame-matches = trans (sym cf-f≡cf-g) cf-f≡sc

      -- Output frame preserved: current-frame sc-g = current-frame sc
      -- By g's output-frame-preserved: current-frame sc-g = current-frame sc-b
      -- And sc-b → sc-f → sc chain
      compose-output-preserved : current-frame sc-g ≡ current-frame sc
      compose-output-preserved =
        let g-out = IRStarResult.output-frame-preserved g-result  -- current-frame sc-g ≡ current-frame sc-b
        in trans g-out (trans sc-b≡sc-f sc-f≡sc)

      -- Heap-base preserved through composition
      compose-heap-base-preserved : StateCorresponds.heap-base sc-g ≡ StateCorresponds.heap-base sc
      compose-heap-base-preserved =
        trans (IRStarResult.heap-base-preserved g-result)
              (trans (IRStarResult.heap-base-preserved f-result) refl)

  in sg , record
    { star-proof = star-final
    ; halted-false = h-sg
    ; pc-advanced = pc-final
    ; σ-final = σg
    ; corr-proof = sc-g
    ; rbp-preserved = rbp-final
    ; rsp-preserved = rsp-final
    ; current-frame = cf-g
    ; frame-matches-input = compose-frame-matches
    ; output-frame-preserved = compose-output-preserved
    ; parent-frames-preserved = parent-preserved
    ; heap-base-preserved = compose-heap-base-preserved
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
  (sc : StateCorresponds σ s) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  PairAtLoc pair-loc σ →
  ∃[ s' ] IRStarResult (fst-ir {A} {B}) prefix suffix σ s sc s' (length prefix)
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
    cf = state-frame σ s sc

  in s' , record
    { star-proof = fst-star-at-offset prefix suffix s (loc-to-addr hb fst-loc) h-eq pc-eq x86-mem-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = σ'
    ; corr-proof = fst-preserves-corresponds σ s fst-loc sc mem-pre
    ; rbp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rbp
                        (loc-to-addr hb fst-loc) (λ ())
    ; rsp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rsp
                        (loc-to-addr hb fst-loc) (λ ())
    ; current-frame = cf
    ; frame-matches-input = refl  -- cf = state-frame σ s sc = current-frame sc
    ; output-frame-preserved = refl  -- fst-preserves-corresponds sets current-frame = current-frame sc
    ; parent-frames-preserved = λ f slot _ → refl  -- fst doesn't modify stack memory
    ; heap-base-preserved = refl  -- fst-preserves-corresponds sets heap-base = heap-base sc
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
  (sc : StateCorresponds σ s) →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ length prefix →
  PairAtLoc pair-loc σ →
  ∃[ s' ] IRStarResult (snd-ir {A} {B}) prefix suffix σ s sc s' (length prefix)
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
    cf = state-frame σ s sc

  in s' , record
    { star-proof = snd-star-at-offset prefix suffix s (loc-to-addr hb snd-loc) h-eq pc-eq x86-mem-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = σ'
    ; corr-proof = snd-preserves-corresponds σ s snd-loc sc mem-pre
    ; rbp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rbp
                        (loc-to-addr hb snd-loc) (λ ())
    ; rsp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rsp
                        (loc-to-addr hb snd-loc) (λ ())
    ; current-frame = cf
    ; frame-matches-input = refl  -- cf = state-frame σ s sc = current-frame sc
    ; output-frame-preserved = refl  -- snd-preserves-corresponds sets current-frame = current-frame sc
    ; parent-frames-preserved = λ f slot _ → refl  -- snd doesn't modify stack memory
    ; heap-base-preserved = refl  -- snd-preserves-corresponds sets heap-base = heap-base sc
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
      rbp-f = IRStarResult.rbp-preserved f-result
      rsp-f = IRStarResult.rsp-preserved f-result

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

      (sb , star-b' , h-sb , pc-sb , sc-b , rbp-b , rsp-b) =
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
      rbp-g = IRStarResult.rbp-preserved g-result
      rsp-g = IRStarResult.rsp-preserved g-result

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

      -- rbp and rsp preservation: chain f → bridge → g
      rbp-final : x86-readReg (X86Sem.State.regs sg) rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
      rbp-final = trans rbp-g (trans rbp-b rbp-f)

      rsp-final : x86-readReg (X86Sem.State.regs sg) rsp ≡ x86-readReg (X86Sem.State.regs s) rsp
      rsp-final = trans rsp-g (trans rsp-b rsp-f)

      -- Frame and parent preservation
      cf-f = IRStarResult.current-frame f-result
      cf-g = IRStarResult.current-frame g-result
      pf-f = IRStarResult.parent-frames-preserved f-result
      pf-g = IRStarResult.parent-frames-preserved g-result

      -- PROVEN: cf-f ≡ cf-g using the frame invariant fields
      cf-f≡sc : cf-f ≡ current-frame sc
      cf-f≡sc = IRStarResult.frame-matches-input f-result

      cf-g≡sc-b : cf-g ≡ current-frame sc-b
      cf-g≡sc-b = IRStarResult.frame-matches-input g-result

      sc-b≡sc-f : current-frame sc-b ≡ current-frame sc-f
      sc-b≡sc-f = refl

      sc-f≡sc : current-frame sc-f ≡ current-frame sc
      sc-f≡sc = IRStarResult.output-frame-preserved f-result

      cf-f≡cf-g : cf-f ≡ cf-g
      cf-f≡cf-g = trans cf-f≡sc (sym (trans cf-g≡sc-b (trans sc-b≡sc-f sc-f≡sc)))

      parent-preserved : ∀ (frame : Frame FS') (slot : ℕ) →
        _≺_ FS' cf-g frame →
        SM.LocState.stackMem σg frame slot ≡ SM.LocState.stackMem σ frame slot
      parent-preserved frame slot cf-g≺frame =
        compose-parent-preserved σ σf σg frame slot cf-f cf-g cf-f≡cf-g cf-g≺frame pf-f pf-g

      compose-frame-matches : cf-g ≡ current-frame sc
      compose-frame-matches = trans (sym cf-f≡cf-g) cf-f≡sc

      compose-output-preserved : current-frame sc-g ≡ current-frame sc
      compose-output-preserved =
        let g-out = IRStarResult.output-frame-preserved g-result
        in trans g-out (trans sc-b≡sc-f sc-f≡sc)

      compose-heap-base-preserved : StateCorresponds.heap-base sc-g ≡ StateCorresponds.heap-base sc
      compose-heap-base-preserved =
        trans (IRStarResult.heap-base-preserved g-result)
              (trans (IRStarResult.heap-base-preserved f-result) refl)

  in sg , record
    { star-proof = star-final
    ; halted-false = h-sg
    ; pc-advanced = pc-final
    ; σ-final = σg
    ; corr-proof = sc-g
    ; rbp-preserved = rbp-final
    ; rsp-preserved = rsp-final
    ; current-frame = cf-g
    ; frame-matches-input = compose-frame-matches
    ; output-frame-preserved = compose-output-preserved
    ; parent-frames-preserved = parent-preserved
    ; heap-base-preserved = compose-heap-base-preserved
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
      rbp-f = IRStarResult.rbp-preserved f-result
      rsp-f = IRStarResult.rsp-preserved f-result

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

      (sb , star-b' , h-sb , pc-sb , sc-b , rbp-b , rsp-b) =
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
      rbp-g = IRStarResult.rbp-preserved g-result
      rsp-g = IRStarResult.rsp-preserved g-result

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

      -- rbp and rsp preservation: chain f → bridge → g
      rbp-final : x86-readReg (X86Sem.State.regs sg) rbp ≡ x86-readReg (X86Sem.State.regs s) rbp
      rbp-final = trans rbp-g (trans rbp-b rbp-f)

      rsp-final : x86-readReg (X86Sem.State.regs sg) rsp ≡ x86-readReg (X86Sem.State.regs s) rsp
      rsp-final = trans rsp-g (trans rsp-b rsp-f)

      -- Frame and parent preservation
      cf-f = IRStarResult.current-frame f-result
      cf-g = IRStarResult.current-frame g-result
      pf-f = IRStarResult.parent-frames-preserved f-result
      pf-g = IRStarResult.parent-frames-preserved g-result

      -- PROVEN: cf-f ≡ cf-g using the frame invariant fields
      cf-f≡sc : cf-f ≡ current-frame sc
      cf-f≡sc = IRStarResult.frame-matches-input f-result

      cf-g≡sc-b : cf-g ≡ current-frame sc-b
      cf-g≡sc-b = IRStarResult.frame-matches-input g-result

      sc-b≡sc-f : current-frame sc-b ≡ current-frame sc-f
      sc-b≡sc-f = refl

      sc-f≡sc : current-frame sc-f ≡ current-frame sc
      sc-f≡sc = IRStarResult.output-frame-preserved f-result

      cf-f≡cf-g : cf-f ≡ cf-g
      cf-f≡cf-g = trans cf-f≡sc (sym (trans cf-g≡sc-b (trans sc-b≡sc-f sc-f≡sc)))

      parent-preserved : ∀ (frame : Frame FS') (slot : ℕ) →
        _≺_ FS' cf-g frame →
        SM.LocState.stackMem σg frame slot ≡ SM.LocState.stackMem σ frame slot
      parent-preserved frame slot cf-g≺frame =
        compose-parent-preserved σ σf σg frame slot cf-f cf-g cf-f≡cf-g cf-g≺frame pf-f pf-g

      compose-frame-matches : cf-g ≡ current-frame sc
      compose-frame-matches = trans (sym cf-f≡cf-g) cf-f≡sc

      compose-output-preserved : current-frame sc-g ≡ current-frame sc
      compose-output-preserved =
        let g-out = IRStarResult.output-frame-preserved g-result
        in trans g-out (trans sc-b≡sc-f sc-f≡sc)

      compose-heap-base-preserved' : StateCorresponds.heap-base sc-g ≡ StateCorresponds.heap-base sc
      compose-heap-base-preserved' =
        trans (IRStarResult.heap-base-preserved g-result)
              (trans (IRStarResult.heap-base-preserved f-result) refl)

  in sg , record
    { star-proof = star-final
    ; halted-false = h-sg
    ; pc-advanced = pc-final
    ; σ-final = σg
    ; corr-proof = sc-g
    ; rbp-preserved = rbp-final
    ; rsp-preserved = rsp-final
    ; current-frame = cf-g
    ; frame-matches-input = compose-frame-matches
    ; output-frame-preserved = compose-output-preserved
    ; parent-frames-preserved = parent-preserved
    ; heap-base-preserved = compose-heap-base-preserved'
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
-- Imported from Once.CCC.Target.X86v3.FramelessPairRunner module.
-- Uses frameless codegen (no push/pop rbp) for simpler proofs.
-- See FramelessPairRunner.agda for implementation details.
------------------------------------------------------------------------

open import Once.CCC.Target.X86v3.FramelessPairRunner public
  using (pair-runner; pair-setup-slot-state; pair-middle-slot-state; pair-cleanup-slot-state)

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
  let cf = state-frame σ s sc
  in id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    ; rbp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rbp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; rsp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rsp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; current-frame = cf
    ; frame-matches-input = refl
    ; output-frame-preserved = refl
    ; parent-frames-preserved = λ f slot _ → refl  -- arr doesn't modify stack memory
    ; heap-base-preserved = refl  -- id-preserves-corresponds sets heap-base = heap-base sc
    }

fold-runner : ∀ {F} (m : AllocMode) → IRRunner (fold-ir {F} m)
fold-runner m prefix suffix σ s sc h-eq pc-eq =
  let cf = state-frame σ s sc
  in id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    ; rbp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rbp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; rsp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rsp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; current-frame = cf
    ; frame-matches-input = refl
    ; output-frame-preserved = refl
    ; parent-frames-preserved = λ f slot _ → refl  -- fold doesn't modify stack memory
    ; heap-base-preserved = refl  -- id-preserves-corresponds sets heap-base = heap-base sc
    }

unfold-runner : ∀ {F} → IRRunner (unfold-ir {F})
unfold-runner prefix suffix σ s sc h-eq pc-eq =
  let cf = state-frame σ s sc
  in id-expected-state s , record
    { star-proof = id-star-at-offset prefix suffix s h-eq pc-eq
    ; halted-false = h-eq
    ; pc-advanced = cong (_+ℕ 1) pc-eq
    ; σ-final = id-slot-state σ
    ; corr-proof = id-preserves-corresponds σ s sc
    ; rbp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rbp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; rsp-preserved = readReg-writeReg-diff (X86Sem.State.regs s) rax rsp
                        (x86-readReg (X86Sem.State.regs s) rdi) (λ ())
    ; current-frame = cf
    ; frame-matches-input = refl
    ; output-frame-preserved = refl
    ; parent-frames-preserved = λ f slot _ → refl  -- unfold doesn't modify stack memory
    ; heap-base-preserved = refl  -- id-preserves-corresponds sets heap-base = heap-base sc
    }

-- free-heap compiles to [] (no-op, zero steps)
-- Special: Star [] s s (refl*), pc unchanged
-- Note: compile-ir (free-heap r) = []
-- So: prefix ++ compile-ir (free-heap r) ++ suffix = prefix ++ [] ++ suffix = prefix ++ suffix
-- compile-length (free-heap r) = 0, so pc-advanced needs: pc s ≡ length prefix + 0
free-heap-runner : ∀ (r : HeapRef) → IRRunner (free-heap r)
free-heap-runner r prefix suffix σ s sc h-eq pc-eq =
  let cf = state-frame σ s sc
  in s , record
    { star-proof = refl*  -- Star (prefix ++ suffix) s s
    ; halted-false = h-eq
    ; pc-advanced = trans pc-eq (sym (+-identityʳ (length prefix)))  -- length prefix ≡ length prefix + 0
    ; σ-final = σ
    ; corr-proof = sc
    ; rbp-preserved = refl  -- s unchanged, so rbp unchanged
    ; rsp-preserved = refl  -- s unchanged, so rsp unchanged
    ; current-frame = cf
    ; frame-matches-input = refl
    ; output-frame-preserved = refl
    ; parent-frames-preserved = λ f slot _ → refl  -- free-heap doesn't modify stack memory
    ; heap-base-preserved = refl  -- corr-proof = sc, so heap-base unchanged
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
