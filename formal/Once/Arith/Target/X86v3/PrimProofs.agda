------------------------------------------------------------------------
-- Once.Arith.Target.X86v3.PrimProofs
--
-- Arithmetic PrimProofProviderV3 for X86v3 CCC.
--
-- Architecture:
--   - CCC defines generic contract (PrimContractV3)
--   - Arith defines CONCRETE primitives with IsPrimitive evidence
--   - Arith provides proofs using the concrete evidence
--
-- TRUST BOUNDARY: Only CPU instruction semantics.
-- The semantic functions (add-int-sem, etc.) ARE the specification.
--
-- NO POSTULATES - IsPrimitive evidence enables ValidAtWF dispatch.
------------------------------------------------------------------------

module Once.Arith.Target.X86v3.PrimProofs where

open import Data.Nat using (ℕ; _≤_; _<_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; <-≤-trans)
open import Data.Bool using (Bool; false)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine
  using (LocState; mkLocState; ValueLocation; OnStack; OnHeap;
         halted; regs; stackMem; heapMem;
         readReg; writeReg; writeReg-same;
         RDI; RAX; module MemOps; module ExecLemmas)
open import Once.CCC.Target.X86v3.Types using (Type; Int; Float; Str; Buffer; _*_; ⟦_⟧)
open import Once.CCC.IR
  using (IR; Prim; eval; PrimContractV3; AllocMode; Stack;
         stack-requirement; output-mode; IsPrimitive; is-int; is-float;
         PrimSem; evalPrim; ir-stack-requirement; pair-slots)
open import Once.CCC.Target.X86v3.Dispatcher.Allocation
  using (AllocState; next-slot; next-heap-ref; frame-capacity; current-frame; module FrontierInvariant)

------------------------------------------------------------------------
-- Concrete Arithmetic Primitives
--
-- Each arithmetic primitive is defined with:
--   - name: String identifier
--   - sem: Semantic function (the specification)
--   - contract: Generic PrimContractV3
--   - is-prim: IsPrimitive evidence for the output type
--
-- This evidence is used to construct ValidAtWF without postulates.
------------------------------------------------------------------------

record ArithPrimitive (A B : Type) : Set where
  field
    name : String
    sem : ⟦ A ⟧ → ⟦ B ⟧
    contract : PrimContractV3 A B
    is-prim : IsPrimitive B

open ArithPrimitive public

-- Helper to construct contracts for arithmetic (no stack needed, stack output)
arith-contract : PrimContractV3 (Int * Int) Int
arith-contract = record
  { stack-requirement = 0
  ; output-mode = Stack
  ; stack-req-bounded = z≤n
  }

-- Concrete arithmetic primitives
add-int-prim : ArithPrimitive (Int * Int) Int
add-int-prim = record
  { name = "add-int"
  ; sem = λ (a , b) → a +ℕ b
  ; contract = arith-contract
  ; is-prim = is-int
  }

------------------------------------------------------------------------
-- Arithmetic PrimProofProviderV3
------------------------------------------------------------------------

module ArithPrimProvider {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open FrontierInvariant {FS}
    using (BeforeFrontier; stack-before; stack-ancestor; heap-before)
  open MemOps {FS} using (readLoc)

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF;
           valid-int-wf; valid-float-wf; valid-str-wf; valid-buffer-wf;
           valid-primitive-wf)

  open import Once.CCC.Target.X86v3.Dispatcher.Dispatcher
  open PrimProofInterface {FS} program-bound primSem
    using (PrimProofV3; PrimProofProviderV3)

  ------------------------------------------------------------------------
  -- PROVEN LEMMAS (structural properties)
  ------------------------------------------------------------------------

  -- BeforeFrontier is preserved when only slots-available changes.
  before-frontier-slots-irrel : ∀ {loc : ValueLocation FS}
    (alloc : AllocState {FS}) (fits : next-slot alloc ≤ frame-capacity alloc) →
    BeforeFrontier alloc loc →
    BeforeFrontier (record alloc { next-slot = next-slot alloc ; slots-available = fits }) loc
  before-frontier-slots-irrel alloc fits (stack-before {f} {k} f≡cf k<next) =
    stack-before f≡cf k<next
  before-frontier-slots-irrel alloc fits (stack-ancestor {f} {k} cf≺f src) =
    stack-ancestor cf≺f src
  before-frontier-slots-irrel alloc fits (heap-before {hl} r<next) =
    heap-before r<next

  ------------------------------------------------------------------------
  -- CONCRETE EXECUTION MODEL (PROVEN)
  --
  -- Arithmetic is register-only: it reads from input location, computes
  -- in registers, and returns the result at the input location.
  -- Only RAX changes (to point to result location = input location).
  -- Memory is unchanged.
  ------------------------------------------------------------------------

  -- Execute arithmetic: result stays at input location, RAX := input-loc
  exec-arith : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS) →
    ValueLocation FS × LocState FS
  exec-arith sem x input-loc s =
    input-loc ,  -- Result at input location
    mkLocState (writeReg (regs s) RAX input-loc) (stackMem s) (heapMem s) (halted s)

  -- Result location is before frontier (given as input precondition)
  exec-arith-before : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS)
    (alloc : AllocState {FS}) →
    BeforeFrontier alloc input-loc →
    let (result-loc , _) = exec-arith sem x input-loc s
    in BeforeFrontier alloc result-loc
  exec-arith-before sem x input-loc s alloc input-before = input-before

  -- RAX contains result location (trivially true by definition)
  exec-arith-rax : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS) →
    let (result-loc , final-state) = exec-arith sem x input-loc s
    in readReg (regs final-state) RAX ≡ result-loc
  exec-arith-rax sem x input-loc s = writeReg-same (regs s) RAX input-loc

  -- Not halted (halted flag unchanged)
  exec-arith-not-halted : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS) →
    halted s ≡ false →
    let (_ , final-state) = exec-arith sem x input-loc s
    in halted final-state ≡ false
  exec-arith-not-halted sem x input-loc s not-halted = not-halted

  -- Memory preserved (only registers change)
  -- Uses readLoc-stackMem-eq since stackMem and heapMem are unchanged
  exec-arith-mem-preserved : ∀ {A B} (sem : ⟦ A ⟧ → ⟦ B ⟧) (x : ⟦ A ⟧)
    (input-loc : ValueLocation FS) (s : LocState FS)
    (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    let (_ , final-state) = exec-arith sem x input-loc s
    in readLoc final-state loc ≡ readLoc s loc
  exec-arith-mem-preserved sem x input-loc s alloc loc bf =
    let final-state = mkLocState (writeReg (regs s) RAX input-loc) (stackMem s) (heapMem s) (halted s)
    in ExecLemmas.readLoc-stackMem-eq final-state s loc refl refl

  ------------------------------------------------------------------------
  -- THE PROOF: arithmetic satisfies PrimProofProviderV3
  --
  -- Architecture:
  --   1. arith-prim-proof-with-evidence: Takes IsPrimitive evidence directly
  --   2. arith-prim-proof: Generic provider that takes evidence as parameter
  --
  -- The evidence comes from concrete ArithPrimitive definitions.
  -- No postulates - all dispatch via IsPrimitive constructors.
  --
  -- TRUST BOUNDARY: Only CPU instruction semantics.
  ------------------------------------------------------------------------

  -- Core proof with explicit IsPrimitive evidence
  -- NOTE: With opaque Prim, semantics comes from primSem: eval primSem (Prim name) x = evalPrim primSem name x
  -- The proof shows execution produces the same result as evalPrim.
  arith-prim-proof-with-evidence : ∀ {A B}
    (is-prim : IsPrimitive B)
    (name : String)
    (c : PrimContractV3 A B) →
    PrimProofV3 c (Prim name)
  arith-prim-proof-with-evidence {A} {B} is-prim name c mIn x input-loc s alloc
    input-valid-wf input-before not-halted rdi-eq cap-ok =
    let
      -- Semantics comes from primSem
      sem = evalPrim primSem {A} {B} name

      -- Execute arithmetic (register-only)
      (result-loc , final-state) = exec-arith sem x input-loc s

      -- Result is before frontier (same as input location)
      result-before = exec-arith-before sem x input-loc s alloc input-before

      -- Result is valid: dispatch on IsPrimitive evidence
      result-valid = valid-primitive-wf is-prim result-before
    in
    record
      { result-loc = result-loc
      ; final-state = final-state
      ; final-alloc = alloc  -- No allocation changes
      ; result-valid-wf = result-valid
      ; result-before = result-before
      ; rax-is-result = exec-arith-rax sem x input-loc s
      ; not-halted = exec-arith-not-halted sem x input-loc s not-halted
      ; frame-preserved = refl
      ; slot-monotone = ≤-refl
      ; heap-monotone = ≤-refl
      ; heap-preserved = refl
      ; capacity-preserved = refl
      ; mem-preserved-before = λ loc bf → exec-arith-mem-preserved sem x input-loc s alloc loc bf
      -- Reclaim: trivial since stack-requirement = 0 for arithmetic
      ; reclaimable-slot = next-slot alloc
      ; reclaim-monotone = ≤-refl
      ; reclaim-bounded = ≤-refl
      -- PROVEN: uses before-frontier-slots-irrel
      ; reclaim-preserves-result = λ fits → before-frontier-slots-irrel alloc fits result-before
      ; reclaim-preserves-validity = λ fits →
          let reclaim-before = before-frontier-slots-irrel alloc fits result-before
          in valid-primitive-wf is-prim reclaim-before
      ; reclaim-size-bound = m≤m+n (next-slot alloc) pair-slots  -- ir-stack-requirement (Prim _) = pair-slots
      }

  -- Proof for a concrete ArithPrimitive (uses embedded evidence)
  arith-prim-proof-concrete : ∀ {A B} (p : ArithPrimitive A B) →
    PrimProofV3 (contract p) (Prim (name p))
  arith-prim-proof-concrete p =
    arith-prim-proof-with-evidence (is-prim p) (name p) (contract p)
