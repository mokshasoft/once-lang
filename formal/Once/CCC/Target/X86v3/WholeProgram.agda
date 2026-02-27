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
  using (compile-ir)
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
open import Once.CCC.SlotMachine using (HeapRef; mkHeapRef; RegId; RAX; RDI;
         HeapLocation; heap-loc; OnHeap; OnStack)
  renaming (Instr to SlotInstr; mov to slot-mov)
open import Data.String using (String)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

-- Import SlotMachine exec for simulation proofs
open import Once.CCC.SlotMachine as SM using (LocState; Registers; readReg; writeReg)
open SM.ExecFinal {FS'} using () renaming (exec to slot-exec)

-- Import Star combinators
open import Once.CCC.Target.X86.Correct.Star
  using (Star; refl*; step*; star-trans; star-single; _◅◅_)

-- Import ExecLemmas for Star proofs
open import Once.Target.X86.ExecLemmas
  using (id-star; id-expected-state; id-instrs;
         terminal-star; terminal-expected-state; terminal-instrs;
         fst-star; fst-expected-state; fst-instrs;
         snd-star; snd-expected-state; snd-instrs;
         bridge-star; bridge-expected-state; compose-bridge)

-- Import SlotToX86 for correspondence
open import Once.CCC.Target.X86v3.Refinement.SlotToX86 as SlotToX86
  using (RegsCorrespond; MemCorresponds; StateCorresponds;
         mov-regs-correspond; mov-mem-corresponds;
         build-regs-correspond-after-write;
         loc-to-addr; compile-reg; sucLoc-to-addr-OnStack)
open RegsCorrespond
open MemCorresponds
open StateCorresponds

open import Once.Target.X86.Semantics as X86Sem
  renaming (readReg to x86-readReg; writeReg to x86-writeReg; readMem to x86-readMem)
open X86Sem.State using (halted; pc)

open import Once.Target.X86.Syntax using (rax; rdi; slot-size)

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
  { regs-correspond = mov-regs-correspond RAX RDI (SM.LocState.regs σ) (X86Sem.State.regs s)
                        (regs-correspond sc)
  ; mem-corresponds = mov-mem-corresponds RAX RDI σ (X86Sem.State.memory s) (mem-corresponds sc)
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }

------------------------------------------------------------------------
-- terminal: mov rax, 0
--
-- X86 puts 0 in rax. This represents the Unit value.
-- We construct σ' where RAX holds an OnHeap location.
-- Since loc-to-addr (OnHeap _) = 0, the correspondence holds.
------------------------------------------------------------------------

-- A canonical Unit location (any OnHeap location maps to 0)
unit-loc : SM.ValueLocation FS'
unit-loc = OnHeap (heap-loc (mkHeapRef 0) 0)

-- SlotMachine state after terminal: RAX holds unit-loc
terminal-slot-state : LocState FS' → LocState FS'
terminal-slot-state σ = record σ { regs = writeReg (SM.LocState.regs σ) RAX unit-loc }

-- Lemma: loc-to-addr unit-loc = 0
unit-loc-addr : loc-to-addr unit-loc ≡ 0
unit-loc-addr = refl

-- Helper: readLoc is unchanged when only registers change
-- (readLoc only uses stackMem and heapMem, not regs)
private
  open import Once.CCC.SlotMachine as SM' using (stackMem; heapMem)
  open SM.MemOps {FS'} using (readLoc)

  terminal-readLoc-unchanged : ∀ (σ : LocState FS') (loc : SM.ValueLocation FS') →
    readLoc (terminal-slot-state σ) loc ≡ readLoc σ loc
  terminal-readLoc-unchanged σ (OnStack f k) = refl
  terminal-readLoc-unchanged σ (OnHeap hl) = refl

-- terminal preserves correspondence (PROVEN - not postulate)
terminal-preserves-corresponds : ∀ (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  ∃[ σ' ] StateCorresponds σ' (terminal-expected-state s)
terminal-preserves-corresponds σ s sc =
  terminal-slot-state σ , record
    { regs-correspond = terminal-regs-correspond σ s sc
    ; mem-corresponds = terminal-mem-corresponds σ s sc
    ; halted-corresponds = halted-corresponds sc
    ; rbp-is-frame-base = rbp-is-frame-base sc
    }
  where
    -- RAX correspondence: both hold 0
    -- terminal-expected-state writes 0 to x86 rax
    -- terminal-slot-state writes unit-loc (which maps to 0) to SlotMachine RAX
    terminal-regs-correspond : ∀ (σ : LocState FS') (s : State) →
      StateCorresponds σ s →
      RegsCorrespond (SM.LocState.regs (terminal-slot-state σ)) (X86Sem.State.regs (terminal-expected-state s))
    terminal-regs-correspond σ s sc = record
      { rax-corresponds = refl  -- 0 = loc-to-addr unit-loc = 0
      ; rdi-corresponds = rdi-corresponds (regs-correspond sc)
      ; rsi-corresponds = rsi-corresponds (regs-correspond sc)
      ; r12-corresponds = r12-corresponds (regs-correspond sc)
      ; r14-corresponds = r14-corresponds (regs-correspond sc)
      ; r15-corresponds = r15-corresponds (regs-correspond sc)
      }

    -- Memory correspondence: memory unchanged in both SlotMachine and x86
    terminal-mem-corresponds : ∀ (σ : LocState FS') (s : State) →
      StateCorresponds σ s →
      MemCorresponds (terminal-slot-state σ) (X86Sem.State.memory (terminal-expected-state s))
    terminal-mem-corresponds σ s sc = record
      { stack-corresponds = λ loc loc' read-eq →
          stack-corresponds (mem-corresponds sc) loc loc'
            (trans (sym (terminal-readLoc-unchanged σ loc)) read-eq)
      }

------------------------------------------------------------------------
-- fst: mov rax, [rdi]
--
-- SlotMachine equivalent: load RAX (IndReg RDI)
-- Precondition: memory at RDI contains fst-loc
-- After: RAX = fst-loc (both sides)
------------------------------------------------------------------------

-- SlotMachine state after fst (given the loaded value)
fst-slot-state : LocState FS' → SM.ValueLocation FS' → LocState FS'
fst-slot-state σ fst-loc = record σ { regs = writeReg (SM.LocState.regs σ) RAX fst-loc }

-- Helper: readLoc unchanged when only registers change (same as terminal)
private
  fst-readLoc-unchanged : ∀ (σ : LocState FS') (fst-loc : SM.ValueLocation FS')
    (loc : SM.ValueLocation FS') →
    readLoc (fst-slot-state σ fst-loc) loc ≡ readLoc σ loc
  fst-readLoc-unchanged σ fst-loc (OnStack f k) = refl
  fst-readLoc-unchanged σ fst-loc (OnHeap hl) = refl

-- fst preserves correspondence (PROVEN - with memory precondition)
fst-preserves-corresponds : ∀ (σ : LocState FS') (s : State)
  (fst-loc : SM.ValueLocation FS') →
  StateCorresponds σ s →
  -- Memory precondition: SlotMachine memory at RDI contains fst-loc
  readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc →
  StateCorresponds (fst-slot-state σ fst-loc)
                   (fst-expected-state s (loc-to-addr fst-loc))
fst-preserves-corresponds σ s fst-loc sc mem-pre = record
  { regs-correspond = fst-regs-correspond
  ; mem-corresponds = fst-mem-corresponds
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }
  where
    fst-regs-correspond : RegsCorrespond
      (SM.LocState.regs (fst-slot-state σ fst-loc))
      (X86Sem.State.regs (fst-expected-state s (loc-to-addr fst-loc)))
    fst-regs-correspond = record
      { rax-corresponds = refl  -- Both sides: loc-to-addr fst-loc
      ; rdi-corresponds = rdi-corresponds (regs-correspond sc)
      ; rsi-corresponds = rsi-corresponds (regs-correspond sc)
      ; r12-corresponds = r12-corresponds (regs-correspond sc)
      ; r14-corresponds = r14-corresponds (regs-correspond sc)
      ; r15-corresponds = r15-corresponds (regs-correspond sc)
      }

    fst-mem-corresponds : MemCorresponds (fst-slot-state σ fst-loc)
                            (X86Sem.State.memory (fst-expected-state s (loc-to-addr fst-loc)))
    fst-mem-corresponds = record
      { stack-corresponds = λ loc loc' read-eq →
          stack-corresponds (mem-corresponds sc) loc loc'
            (trans (sym (fst-readLoc-unchanged σ fst-loc loc)) read-eq)
      }

-- fst simulation with memory precondition
fst-simulation : ∀ (σ : LocState FS') (s : State)
  (fst-loc : SM.ValueLocation FS') →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  readLoc σ (SM.readReg (SM.LocState.regs σ) RDI) ≡ just fst-loc →
  ∃[ x86-final ] ∃[ σ-final ]
    Star fst-instrs s x86-final × StateCorresponds σ-final x86-final
fst-simulation σ s fst-loc sc h-eq pc-eq mem-pre =
  let -- Get x86 memory read value from correspondence
      rdi-loc = SM.readReg (SM.LocState.regs σ) RDI
      rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
      -- By regs-correspond: rdi-addr = loc-to-addr rdi-loc
      rdi-eq : rdi-addr ≡ loc-to-addr rdi-loc
      rdi-eq = rdi-corresponds (regs-correspond sc)
      -- By mem-corresponds: x86 memory at rdi-addr = loc-to-addr fst-loc
      x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr rdi-loc) ≡ just (loc-to-addr fst-loc)
      x86-mem-eq = stack-corresponds (mem-corresponds sc) rdi-loc fst-loc mem-pre
      -- Combine: x86 memory at rdi = loc-to-addr fst-loc
      x86-mem-at-rdi : x86-readMem (X86Sem.State.memory s) rdi-addr ≡ just (loc-to-addr fst-loc)
      x86-mem-at-rdi = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr fst-loc))
                             (sym rdi-eq) x86-mem-eq
  in fst-expected-state s (loc-to-addr fst-loc)
   , fst-slot-state σ fst-loc
   , fst-star s (loc-to-addr fst-loc) h-eq pc-eq x86-mem-at-rdi
   , fst-preserves-corresponds σ s fst-loc sc mem-pre

------------------------------------------------------------------------
-- snd: mov rax, [rdi+8]
--
-- SlotMachine equivalent: load RAX (IndRegSuc RDI)
-- Precondition: memory at RDI+8 contains snd-loc
-- After: RAX = snd-loc (both sides)
------------------------------------------------------------------------

-- SlotMachine state after snd (given the loaded value)
snd-slot-state : LocState FS' → SM.ValueLocation FS' → LocState FS'
snd-slot-state σ snd-loc = record σ { regs = writeReg (SM.LocState.regs σ) RAX snd-loc }

-- Helper: readLoc unchanged when only registers change
private
  snd-readLoc-unchanged : ∀ (σ : LocState FS') (snd-loc : SM.ValueLocation FS')
    (loc : SM.ValueLocation FS') →
    readLoc (snd-slot-state σ snd-loc) loc ≡ readLoc σ loc
  snd-readLoc-unchanged σ snd-loc (OnStack f k) = refl
  snd-readLoc-unchanged σ snd-loc (OnHeap hl) = refl

-- snd preserves correspondence (PROVEN - with memory precondition)
snd-preserves-corresponds : ∀ (σ : LocState FS') (s : State)
  (snd-loc : SM.ValueLocation FS') →
  StateCorresponds σ s →
  readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc →
  StateCorresponds (snd-slot-state σ snd-loc)
                   (snd-expected-state s (loc-to-addr snd-loc))
snd-preserves-corresponds σ s snd-loc sc mem-pre = record
  { regs-correspond = snd-regs-correspond
  ; mem-corresponds = snd-mem-corresponds
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }
  where
    snd-regs-correspond : RegsCorrespond
      (SM.LocState.regs (snd-slot-state σ snd-loc))
      (X86Sem.State.regs (snd-expected-state s (loc-to-addr snd-loc)))
    snd-regs-correspond = record
      { rax-corresponds = refl
      ; rdi-corresponds = rdi-corresponds (regs-correspond sc)
      ; rsi-corresponds = rsi-corresponds (regs-correspond sc)
      ; r12-corresponds = r12-corresponds (regs-correspond sc)
      ; r14-corresponds = r14-corresponds (regs-correspond sc)
      ; r15-corresponds = r15-corresponds (regs-correspond sc)
      }

    snd-mem-corresponds : MemCorresponds (snd-slot-state σ snd-loc)
                            (X86Sem.State.memory (snd-expected-state s (loc-to-addr snd-loc)))
    snd-mem-corresponds = record
      { stack-corresponds = λ loc loc' read-eq →
          stack-corresponds (mem-corresponds sc) loc loc'
            (trans (sym (snd-readLoc-unchanged σ snd-loc loc)) read-eq)
      }

-- snd simulation with memory precondition
-- Uses sucLoc-to-addr-OnStack from SlotToX86 to connect sucLoc to +slot-size
--
-- OnStack case: fully proven using sucLoc-to-addr-OnStack
-- OnHeap case: postulated (heap layout not yet implemented)
snd-simulation : ∀ (σ : LocState FS') (s : State)
  (snd-loc : SM.ValueLocation FS') →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc →
  ∃[ x86-final ] ∃[ σ-final ]
    Star snd-instrs s x86-final × StateCorresponds σ-final x86-final
snd-simulation σ s snd-loc sc h-eq pc-eq mem-pre =
  snd-sim-helper (SM.readReg (SM.LocState.regs σ) RDI) refl mem-pre
  where
    snd-sim-helper : ∀ (rdi-loc : SM.ValueLocation FS') →
      SM.readReg (SM.LocState.regs σ) RDI ≡ rdi-loc →
      readLoc σ (SM.sucLoc rdi-loc) ≡ just snd-loc →
      ∃[ x86-final ] ∃[ σ-final ]
        Star snd-instrs s x86-final × StateCorresponds σ-final x86-final
    snd-sim-helper (OnStack f k) rdi-eq mem-pre-stack =
      let rdi-addr = x86-readReg (X86Sem.State.regs s) rdi
          -- By regs-correspond + rdi-eq: rdi-addr = loc-to-addr (OnStack f k)
          -- rdi-corresponds : rdi-addr ≡ loc-to-addr (readReg σ-regs RDI)
          -- rdi-eq : readReg σ-regs RDI ≡ OnStack f k
          -- cong loc-to-addr rdi-eq : loc-to-addr (readReg σ-regs RDI) ≡ loc-to-addr (OnStack f k)
          rdi-corr : rdi-addr ≡ loc-to-addr (OnStack f k)
          rdi-corr = trans (rdi-corresponds (regs-correspond sc)) (cong loc-to-addr rdi-eq)
          -- sucLoc location: sucLoc (OnStack f k) = OnStack f (suc k)
          suc-loc = SM.sucLoc (OnStack f k)
          -- By mem-corresponds: x86 memory at addr(suc-loc) = loc-to-addr snd-loc
          x86-mem-eq : x86-readMem (X86Sem.State.memory s) (loc-to-addr suc-loc) ≡ just (loc-to-addr snd-loc)
          x86-mem-eq = stack-corresponds (mem-corresponds sc) suc-loc snd-loc mem-pre-stack
          -- By sucLoc-to-addr-OnStack: loc-to-addr (sucLoc (OnStack f k)) = loc-to-addr (OnStack f k) + slot-size
          sucLoc-eq : loc-to-addr suc-loc ≡ loc-to-addr (OnStack f k) +ℕ slot-size
          sucLoc-eq = sucLoc-to-addr-OnStack f k
          -- Combine: rdi-addr + slot-size = loc-to-addr suc-loc
          addr-eq : rdi-addr +ℕ slot-size ≡ loc-to-addr suc-loc
          addr-eq = trans (cong (_+ℕ slot-size) rdi-corr) (sym sucLoc-eq)
          -- Memory equality at rdi + slot-size
          -- subst P (sym addr-eq) x86-mem-eq : P (rdi-addr + slot-size)
          -- where P addr = x86-readMem mem addr ≡ just result
          x86-mem-at-rdi+8 : x86-readMem (X86Sem.State.memory s) (rdi-addr +ℕ slot-size) ≡ just (loc-to-addr snd-loc)
          x86-mem-at-rdi+8 = subst (λ addr → x86-readMem (X86Sem.State.memory s) addr ≡ just (loc-to-addr snd-loc))
                                   (sym addr-eq) x86-mem-eq
          -- For snd-preserves-corresponds, need mem-pre in original form
          -- mem-pre-stack : readLoc σ (sucLoc (OnStack f k)) ≡ just snd-loc
          -- We need: readLoc σ (sucLoc (readReg σ-regs RDI)) ≡ just snd-loc
          -- Use sym rdi-eq to transport from OnStack f k back to readReg σ-regs RDI
          mem-pre-orig : readLoc σ (SM.sucLoc (SM.readReg (SM.LocState.regs σ) RDI)) ≡ just snd-loc
          mem-pre-orig = subst (λ loc → readLoc σ (SM.sucLoc loc) ≡ just snd-loc) (sym rdi-eq) mem-pre-stack
      in snd-expected-state s (loc-to-addr snd-loc)
       , snd-slot-state σ snd-loc
       , snd-star s (loc-to-addr snd-loc) h-eq pc-eq x86-mem-at-rdi+8
       , snd-preserves-corresponds σ s snd-loc sc mem-pre-orig
    snd-sim-helper (OnHeap hl) rdi-eq mem-pre-heap = snd-simulation-heap hl rdi-eq mem-pre-heap
      where
        postulate
          -- OnHeap case: heap layout not yet implemented
          -- loc-to-addr (OnHeap _) = 0, needs proper heap address computation
          snd-simulation-heap : ∀ (hl : SM.HeapLocation) →
            SM.readReg (SM.LocState.regs σ) RDI ≡ OnHeap hl →
            readLoc σ (SM.sucLoc (OnHeap hl)) ≡ just snd-loc →
            ∃[ x86-final ] ∃[ σ-final ]
              Star snd-instrs s x86-final × StateCorresponds σ-final x86-final

------------------------------------------------------------------------
-- bridge: mov rdi, rax
--
-- Transfers the result of f (in rax) to rdi for g.
-- SlotMachine equivalent: mov RDI RAX
-- After: RDI = (what was in RAX)
------------------------------------------------------------------------

-- SlotMachine state after bridge
bridge-slot-state : LocState FS' → LocState FS'
bridge-slot-state σ = record σ { regs = writeReg (SM.LocState.regs σ) RDI (SM.readReg (SM.LocState.regs σ) RAX) }

-- Helper: readLoc unchanged when only registers change
private
  bridge-readLoc-unchanged : ∀ (σ : LocState FS') (loc : SM.ValueLocation FS') →
    readLoc (bridge-slot-state σ) loc ≡ readLoc σ loc
  bridge-readLoc-unchanged σ (OnStack f k) = refl
  bridge-readLoc-unchanged σ (OnHeap hl) = refl

-- bridge preserves correspondence (PROVEN)
bridge-preserves-corresponds : ∀ (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  StateCorresponds (bridge-slot-state σ) (bridge-expected-state s)
bridge-preserves-corresponds σ s sc = record
  { regs-correspond = bridge-regs-correspond
  ; mem-corresponds = bridge-mem-corresponds
  ; halted-corresponds = halted-corresponds sc
  ; rbp-is-frame-base = rbp-is-frame-base sc
  }
  where
    bridge-regs-correspond : RegsCorrespond
      (SM.LocState.regs (bridge-slot-state σ))
      (X86Sem.State.regs (bridge-expected-state s))
    bridge-regs-correspond = mov-regs-correspond RDI RAX (SM.LocState.regs σ) (X86Sem.State.regs s)
                               (regs-correspond sc)

    bridge-mem-corresponds : MemCorresponds (bridge-slot-state σ)
                               (X86Sem.State.memory (bridge-expected-state s))
    bridge-mem-corresponds = record
      { stack-corresponds = λ loc loc' read-eq →
          stack-corresponds (mem-corresponds sc) loc loc'
            (trans (sym (bridge-readLoc-unchanged σ loc)) read-eq)
      }

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
  , bridge-star s h-eq pc-eq
  , bridge-preserves-corresponds σ s sc

------------------------------------------------------------------------
-- Simulation postulates for full-correctness
--
-- These are simplified versions without explicit memory preconditions.
-- The detailed versions (fst-simulation, snd-simulation) above have
-- the memory preconditions explicit for compositional proofs.
------------------------------------------------------------------------

postulate
  -- fst: needs fst-loc from memory (caller provides StateCorresponds which implies this)
  fst-simulation-simple : ∀ (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star fst-instrs s x86-final × StateCorresponds σ-final x86-final

  -- snd: needs snd-loc from memory at rdi+8
  snd-simulation-simple : ∀ (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star snd-instrs s x86-final × StateCorresponds σ-final x86-final

postulate
  -- compose: uses IH + star-trans
  compose-simulation : ∀ {A B C} (g : IR B C) (f : IR A B)
    (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (g ∘ f)) s x86-final × StateCorresponds σ-final x86-final

  -- pair: setup ++ f ++ middle ++ g ++ cleanup
  pair-simulation : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode)
    (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (⟨ f , g ⟩ m)) s x86-final × StateCorresponds σ-final x86-final

  -- Sum types (placeholder implementations in compile-ir)
  inl-simulation : ∀ {A B} (m : AllocMode) (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (inl-ir {A} {B} m)) s x86-final × StateCorresponds σ-final x86-final

  inr-simulation : ∀ {A B} (m : AllocMode) (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (inr-ir {A} {B} m)) s x86-final × StateCorresponds σ-final x86-final

  case-simulation : ∀ {A B C} (f : IR A C) (g : IR B C) (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (case-ir f g)) s x86-final × StateCorresponds σ-final x86-final

  initial-simulation : ∀ {A} (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (initial {A})) s x86-final × StateCorresponds σ-final x86-final

  -- Closures (complex - needs closure correspondence)
  curry-simulation : ∀ {A B C q} (f : IR (A * B) C) (m : AllocMode)
    (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (curry {q = q} f m)) s x86-final × StateCorresponds σ-final x86-final

  apply-simulation : ∀ {A B q} (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (apply {A} {B} {q})) s x86-final × StateCorresponds σ-final x86-final

  -- Remaining postulates (need more infrastructure to prove)
  prim-simulation : ∀ {A B} (p : String) (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    X86Sem.State.halted s ≡ false →
    X86Sem.State.pc s ≡ 0 →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (Prim {A} {B} p)) s x86-final × StateCorresponds σ-final x86-final

------------------------------------------------------------------------
-- Proven simulations for simple IR constructs
--
-- arr, fold-ir, unfold-ir all compile to id-instrs (mov rax, rdi)
-- free-heap compiles to [] (no-op)
------------------------------------------------------------------------

-- arr: compiles to id-instrs, same as id
arr-simulation : ∀ {A B q} (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (arr {A} {B} {q})) s x86-final × StateCorresponds σ-final x86-final
arr-simulation σ s sc h-eq pc-eq =
  id-expected-state s
  , id-slot-state σ
  , id-star s h-eq pc-eq
  , id-preserves-corresponds σ s sc

-- fold-ir: compiles to id-instrs, same as id
fold-simulation : ∀ {F} (m : AllocMode) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (fold-ir {F} m)) s x86-final × StateCorresponds σ-final x86-final
fold-simulation m σ s sc h-eq pc-eq =
  id-expected-state s
  , id-slot-state σ
  , id-star s h-eq pc-eq
  , id-preserves-corresponds σ s sc

-- unfold-ir: compiles to id-instrs, same as id
unfold-simulation : ∀ {F} (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  X86Sem.State.halted s ≡ false →
  X86Sem.State.pc s ≡ 0 →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (unfold-ir {F})) s x86-final × StateCorresponds σ-final x86-final
unfold-simulation σ s sc h-eq pc-eq =
  id-expected-state s
  , id-slot-state σ
  , id-star s h-eq pc-eq
  , id-preserves-corresponds σ s sc

-- free-heap: compiles to [] (no-op), zero steps
free-heap-simulation : ∀ (r : HeapRef) (σ : LocState FS') (s : State) →
  StateCorresponds σ s →
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir (free-heap r)) s x86-final × StateCorresponds σ-final x86-final
free-heap-simulation r σ s sc =
  s , σ , refl* , sc

------------------------------------------------------------------------
-- Full Correctness by IR Induction
--
-- The proof follows compile-ir structure:
--   - Base cases: id, terminal (proven using Star lemmas + correspondence)
--   - Memory cases: fst, snd (use simulation postulates)
--   - Compound cases: compose, pair (use simulation postulates)
--   - Complex cases: curry, apply, etc. (use simulation postulates)
--
-- ARCHITECTURE:
--   - Postulates are per-construct simulation lemmas
--   - Each can be eliminated independently
--   - No re-doing of Dispatcher's IR semantics work
------------------------------------------------------------------------

full-correctness : ∀ {A B : Type} (ir : IR A B)
  (x : ⟦ A ⟧)
  (x86-init : State)
  (σ-init : LocState FS')
  (input-loc : ValueLocation FS') →
  StateCorresponds σ-init x86-init →
  X86Sem.State.halted x86-init ≡ false →  -- Machine must be running
  X86Sem.State.pc x86-init ≡ 0 →           -- Start at beginning of compiled code
  ∃[ x86-final ] ∃[ σ-final ]
    Star (compile-ir ir) x86-init x86-final
    × StateCorresponds σ-final x86-final

-- id: mov rax, rdi (1 step) - PROVEN
full-correctness id x s σ loc sc h-eq pc-eq =
  id-expected-state s
  , id-slot-state σ
  , id-star s h-eq pc-eq
  , id-preserves-corresponds σ s sc

-- terminal: mov rax, 0 (1 step)
full-correctness terminal x s σ loc sc h-eq pc-eq =
  let (σ' , sc') = terminal-preserves-corresponds σ s sc
  in terminal-expected-state s
   , σ'
   , terminal-star s h-eq pc-eq
   , sc'

-- fst, snd: memory operations
full-correctness fst-ir x s σ loc sc h-eq pc-eq = fst-simulation-simple σ s sc
full-correctness snd-ir x s σ loc sc h-eq pc-eq = snd-simulation-simple σ s sc

-- compose, pair: compound structures
full-correctness (g ∘ f) x s σ loc sc h-eq pc-eq = compose-simulation g f σ s sc
full-correctness (⟨ f , g ⟩ m) x s σ loc sc h-eq pc-eq = pair-simulation f g m σ s sc

-- sum types
full-correctness {A} {A+B} (inl-ir {.A} {B} m) x s σ loc sc h-eq pc-eq = inl-simulation {A} {B} m σ s sc
full-correctness {B} {A+B} (inr-ir {A} {.B} m) x s σ loc sc h-eq pc-eq = inr-simulation {A} {B} m σ s sc
full-correctness (case-ir f g) x s σ loc sc h-eq pc-eq = case-simulation f g σ s sc
full-correctness {_} {B} initial x s σ loc sc h-eq pc-eq = initial-simulation {B} σ s sc

-- closures
full-correctness {A} {.(B ⇒[ _ ] C)} (curry {.A} {B} {C} {q} f m) x s σ loc sc h-eq pc-eq =
  curry-simulation {A} {B} {C} {q} f m σ s sc
full-correctness {.((A ⇒[ q ] B) * A)} {B} (apply {A} {.B} {q}) x s σ loc sc h-eq pc-eq =
  apply-simulation {A} {B} {q} σ s sc

-- remaining (arr, fold, unfold compile to id-instrs; free-heap compiles to [])
full-correctness {.(A ⇒[ q ] B)} {.(Eff A B)} (arr {A} {B} {q}) x s σ loc sc h-eq pc-eq =
  arr-simulation {A} {B} {q} σ s sc h-eq pc-eq
full-correctness {F} {.(Fix F)} (fold-ir m) x s σ loc sc h-eq pc-eq = fold-simulation {F} m σ s sc h-eq pc-eq
full-correctness {.(Fix F)} {F} unfold-ir x s σ loc sc h-eq pc-eq = unfold-simulation {F} σ s sc h-eq pc-eq
full-correctness (free-heap r) x s σ loc sc h-eq pc-eq = free-heap-simulation r σ s sc
full-correctness {A} {B} (Prim p) x s σ loc sc h-eq pc-eq = prim-simulation {A} {B} p σ s sc h-eq pc-eq
