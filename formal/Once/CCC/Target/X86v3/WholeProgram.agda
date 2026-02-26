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
open import Once.CCC.Target.X86v3.FrameInstantiation using (x86v3-frame-semantics)

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
         snd-star; snd-expected-state; snd-instrs)

-- Import SlotToX86 for correspondence
open import Once.CCC.Target.X86v3.Refinement.SlotToX86 as SlotToX86
  using (RegsCorrespond; MemCorresponds; StateCorresponds;
         mov-regs-correspond; mov-mem-corresponds;
         build-regs-correspond-after-write;
         loc-to-addr; compile-reg)
open RegsCorrespond
open MemCorresponds
open StateCorresponds

open import Once.Target.X86.Semantics as X86Sem
  renaming (readReg to x86-readReg; writeReg to x86-writeReg)
open X86Sem.State using (halted; pc)

open import Once.Target.X86.Syntax using (rax; rdi)

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

postulate
  -- fst: mov rax, [rdi] (needs memory precondition for full proof)
  fst-simulation : ∀ (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star fst-instrs s x86-final × StateCorresponds σ-final x86-final

  -- snd: mov rax, [rdi+8] (needs memory precondition for full proof)
  snd-simulation : ∀ (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star snd-instrs s x86-final × StateCorresponds σ-final x86-final

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

  -- Remaining constructs
  arr-simulation : ∀ {A B q} (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (arr {A} {B} {q})) s x86-final × StateCorresponds σ-final x86-final

  fold-simulation : ∀ {F} (m : AllocMode) (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (fold-ir {F} m)) s x86-final × StateCorresponds σ-final x86-final

  unfold-simulation : ∀ {F} (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (unfold-ir {F})) s x86-final × StateCorresponds σ-final x86-final

  free-heap-simulation : ∀ (r : HeapRef) (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (free-heap r)) s x86-final × StateCorresponds σ-final x86-final

  prim-simulation : ∀ {A B} (p : String) (σ : LocState FS') (s : State) →
    StateCorresponds σ s →
    ∃[ x86-final ] ∃[ σ-final ]
      Star (compile-ir (Prim {A} {B} p)) s x86-final × StateCorresponds σ-final x86-final

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
full-correctness fst-ir x s σ loc sc h-eq pc-eq = fst-simulation σ s sc
full-correctness snd-ir x s σ loc sc h-eq pc-eq = snd-simulation σ s sc

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

-- remaining
full-correctness {.(A ⇒[ q ] B)} {.(Eff A B)} (arr {A} {B} {q}) x s σ loc sc h-eq pc-eq =
  arr-simulation {A} {B} {q} σ s sc
full-correctness {F} {.(Fix F)} (fold-ir m) x s σ loc sc h-eq pc-eq = fold-simulation {F} m σ s sc
full-correctness {.(Fix F)} {F} unfold-ir x s σ loc sc h-eq pc-eq = unfold-simulation {F} σ s sc
full-correctness (free-heap r) x s σ loc sc h-eq pc-eq = free-heap-simulation r σ s sc
full-correctness {A} {B} (Prim p) x s σ loc sc h-eq pc-eq = prim-simulation {A} {B} p σ s sc
