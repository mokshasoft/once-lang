------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.Compose
--
-- Compose implementation for X86v3 dispatcher.
-- Takes RecDispatcher as parameter, enabling termination checking.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.Compose where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-assoc)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

module ComposeImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open MemOps {FS}
  open FrontierInvariant {FS}
  open FrameSemantics FS
  open import Data.Nat.Properties using (≤-reflexive; +-monoˡ-≤)

  -- Import result type and RecDispatcher from IRResult (avoids circular dependency)
  open import Once.Backend.X86v3.IRResult using (module DispatcherResult; module RecDispatcherDef)
  open DispatcherResult {FS} program-bound
  open RecDispatcherDef {FS} program-bound

  -- Arithmetic helper for slot-bounded
  private
    compose-slot-bounded-lemma : ∀ (slot slot₁ slot₂ req-f req-g : ℕ) →
      slot₂ ≤ slot₁ + req-g →
      slot₁ ≤ slot + req-f →
      slot₂ ≤ slot + (req-f + req-g)
    compose-slot-bounded-lemma slot slot₁ slot₂ req-f req-g bound-g bound-f =
      ≤-trans (≤-trans bound-g (+-monoˡ-≤ req-g bound-f))
              (≤-reflexive (+-assoc slot req-f req-g))

  -- Compose implementation
  -- RecDispatcher handles Acc internally - no Acc parameters needed here
  run-compose : ∀ {A B C} (f : IR A B) (g : IR B C)
    (bound : ℕ) (rec : RecDispatcher bound)
    (f<bound : ir-size f < bound) (g<bound : ir-size g < bound)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultA (g ∘ f) x s alloc
  run-compose f g bound rec f<bound g<bound x input-loc s alloc input-valid input-before not-halted rdi-eq =
    let -- Run f via dispatcher
        result-f = rec f f<bound x input-loc s alloc input-valid input-before not-halted rdi-eq
        s' = IRResultA.final-state result-f
        alloc' = IRResultA.final-alloc result-f
        inter-loc = IRResultA.result-loc result-f
        -- Set up RDI for g
        s'-rdi = record s' { regs = writeReg (regs s') RDI inter-loc }
        inter-valid' = validity-mem-only (eval f x) inter-loc s' s'-rdi refl refl
                         (IRResultA.result-valid result-f)
        -- Run g via dispatcher
        result-g = rec g g<bound (eval f x) inter-loc s'-rdi alloc'
                     inter-valid'
                     (IRResultA.result-before result-f)
                     (IRResultA.not-halted result-f)
                     (writeReg-same (regs s') RDI inter-loc)
        -- Slot bounded for compose
        slot-bounded-compose = compose-slot-bounded-lemma
          (next-slot alloc) (next-slot alloc') (next-slot (IRResultA.final-alloc result-g))
          (ir-stack-requirement f) (ir-stack-requirement g)
          (IRResultA.slot-bounded result-g) (IRResultA.slot-bounded result-f)
    in record
      { result-loc = IRResultA.result-loc result-g
      ; final-state = IRResultA.final-state result-g
      ; final-alloc = IRResultA.final-alloc result-g
      ; result-valid = IRResultA.result-valid result-g
      ; result-before = IRResultA.result-before result-g
      ; rax-is-result = IRResultA.rax-is-result result-g
      ; not-halted = IRResultA.not-halted result-g
      ; frame-preserved = trans (IRResultA.frame-preserved result-g) (IRResultA.frame-preserved result-f)
      ; slot-monotone = ≤-trans (IRResultA.slot-monotone result-f) (IRResultA.slot-monotone result-g)
      ; heap-monotone = ≤-trans (IRResultA.heap-monotone result-f) (IRResultA.heap-monotone result-g)
      ; slot-bounded = slot-bounded-compose
      ; capacity-preserved = trans (IRResultA.capacity-preserved result-g) (IRResultA.capacity-preserved result-f)
      }
