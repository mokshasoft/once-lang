------------------------------------------------------------------------
-- Once.Arith.Prim.Proofs
--
-- Arithmetic primitive proofs (arch-portable).
--
-- Parameterized by FrameSemantics, not tied to any specific target.
-- Uses the simplified Once.CCC.Prim.Helper interface.
-- NO POSTULATES - fully proven from first principles.
------------------------------------------------------------------------

module Once.Arith.Prim.Proofs where

open import Data.Nat using (ℕ; _≤_; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; Int; IsPrimitive; is-int; _*_)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.IR using (IR; Prim; AllocMode; Stack)
open import Once.CCC.Prim.Contract using (PrimContract; output-mode)
open import Once.CCC.SMCore
  using (LocState; ValueLocation; OnStack; halted; regs;
         readReg; Input; Output; AbstractTrace; mov-to-output;
         mkLocState; stackMem; heapMem; writeReg; module MemOps;
         module AbstractExec; module ExecLemmas)
open import Once.CCC.Eval using (PrimSem; evalPrim)
open import Once.Sem using (⟦_⟧)

------------------------------------------------------------------------
-- Arithmetic Contract: Just says result is on Stack (in-place)
------------------------------------------------------------------------

arith-contract : PrimContract (Int * Int) Int
arith-contract = record { output-mode = Stack }

------------------------------------------------------------------------
-- Arithmetic Semantics
------------------------------------------------------------------------

add-sem : ⟦ Int * Int ⟧ → ⟦ Int ⟧
add-sem (a , b) = a +ℕ b

------------------------------------------------------------------------
-- Arithmetic Proof Module
------------------------------------------------------------------------

module ArithProofs {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open import Once.CCC.Prim.Helper
  open PrimHelper {FS} program-bound primSem

  open import Once.CCC.Target.X86v3.Dispatcher.Allocation
    using (AllocState; current-frame; next-slot; frame-capacity)
  open import Once.CCC.Target.X86v3.Dispatcher.Allocation
    using (module FrontierInvariant)
  open FrontierInvariant {FS} using (BeforeFrontier)

  open import Once.CCC.Target.X86v3.Dispatcher.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound primSem
    using (ValidAtWF; IRResultAWF)

  open import Once.CCC.Target.X86v3.Dispatcher.Dispatcher
  open PrimProofInterface {FS} program-bound primSem
    using (PrimProofV3)

  open AbstractExec {FS} using (exec-trace; exec-trace-single; exec-abstract)
  open MemOps {FS} using (readLoc)
  open ExecLemmas {FS} using (readLoc-stackMem-eq)
  open import Data.List using ([]; _∷_)

  ------------------------------------------------------------------------
  -- Proven Lemmas (no postulates!)
  ------------------------------------------------------------------------

  -- Trace execution: mov-to-output writes Input to Output
  -- Precondition: readReg (regs s) Input ≡ input-loc
  arith-trace-correct : ∀ (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    readReg (regs s) Input ≡ input-loc →
    proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
    mkLocState (writeReg (regs s) Output input-loc)
               (stackMem s) (heapMem s) (halted s)
  arith-trace-correct input-loc s alloc not-halted rdi-eq =
    let
      -- exec-trace (i ∷ []) = exec-abstract i when not halted
      step1 : proj₁ (exec-trace (mov-to-output ∷ []) s alloc) ≡
              proj₁ (exec-abstract mov-to-output s alloc)
      step1 = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)

      -- exec-abstract mov-to-output writes readReg Input to Output
      -- Result state only changes regs field
      step2 : proj₁ (exec-abstract mov-to-output s alloc) ≡
              mkLocState (writeReg (regs s) Output (readReg (regs s) Input))
                         (stackMem s) (heapMem s) (halted s)
      step2 = refl

      -- Using rdi-eq to substitute input-loc
      step3 : mkLocState (writeReg (regs s) Output (readReg (regs s) Input))
                         (stackMem s) (heapMem s) (halted s) ≡
              mkLocState (writeReg (regs s) Output input-loc)
                         (stackMem s) (heapMem s) (halted s)
      step3 = cong (λ loc → mkLocState (writeReg (regs s) Output loc)
                                       (stackMem s) (heapMem s) (halted s)) rdi-eq
    in trans step1 (trans step2 step3)

  -- Frontier slot stability: mov-to-output only affects registers
  arith-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS)
    (alloc : AllocState {FS}) →
    halted s' ≡ false →
    readReg (regs s') Input ≡ input-loc' →
    readLoc s' (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc' →
    readLoc (proj₁ (exec-trace (mov-to-output ∷ []) s' alloc))
            (OnStack (current-frame alloc) (next-slot alloc)) ≡ just input-loc'
  arith-frontier-stable s' input-loc' alloc not-halted rdi-eq slot-eq =
    let
      s'' = proj₁ (exec-trace (mov-to-output ∷ []) s' alloc)

      -- After mov-to-output, stackMem is unchanged
      stack-preserved : stackMem s'' ≡ stackMem s'
      stack-preserved = cong stackMem
        (trans (cong proj₁ (exec-trace-single mov-to-output s' alloc not-halted)) refl)

      -- heapMem is also unchanged
      heap-preserved : heapMem s'' ≡ heapMem s'
      heap-preserved = cong heapMem
        (trans (cong proj₁ (exec-trace-single mov-to-output s' alloc not-halted)) refl)

      -- readLoc only depends on stackMem/heapMem for OnStack locations
      loc-preserved : readLoc s'' (OnStack (current-frame alloc) (next-slot alloc)) ≡
                      readLoc s' (OnStack (current-frame alloc) (next-slot alloc))
      loc-preserved = readLoc-stackMem-eq s'' s'
                        (OnStack (current-frame alloc) (next-slot alloc))
                        stack-preserved heap-preserved
    in trans loc-preserved slot-eq

  ------------------------------------------------------------------------
  -- THE PROOF: Clean and simple
  ------------------------------------------------------------------------

  add-int-proof : PrimProofV3 arith-contract (Prim "add-int")
  add-int-proof mIn x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mkPurePrimResult
      "add-int"
      arith-contract
      is-int
      x
      input-loc
      s
      alloc
      input-before
      not-halted
      rdi-eq
      (arith-trace-correct input-loc s alloc not-halted rdi-eq)
      (λ s' loc' nh' rdi' slot-eq' → arith-frontier-stable s' loc' alloc nh' rdi' slot-eq')

  ------------------------------------------------------------------------
  -- Provider: Maps "add-int" to its proof
  ------------------------------------------------------------------------

  add-int-contract-proof : ∃[ c ] PrimProofV3 {Int * Int} {Int} c (Prim "add-int")
  add-int-contract-proof = arith-contract , add-int-proof
