------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.Pair
--
-- Pair implementation for X86v3 dispatcher.
-- Takes RecDispatcher as parameter, enabling termination checking.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.Pair where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-assoc; +-monoˡ-≤; ≤-reflexive; m<m+n)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

module PairImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open MemOps {FS}
  open WriteOps {FS}
  open FrontierInvariant {FS}
  open StackAllocation {FS}
  open FrameSemantics FS

  -- Import result type and RecDispatcher from IRResult (avoids circular dependency)
  open import Once.Backend.X86v3.IRResult using (module DispatcherResult; module RecDispatcherDef)
  open DispatcherResult {FS} program-bound
  open RecDispatcherDef {FS} program-bound

  -- Import write operations
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Arithmetic helper for slot-bounded
  private
    pair-slot-bounded-lemma : ∀ (slot slot₁ slot₂ req-f req-g ps : ℕ) →
      slot₂ ≤ slot₁ + req-g →
      slot₁ ≤ slot + req-f →
      slot₂ + ps ≤ slot + ((req-f + req-g) + ps)
    pair-slot-bounded-lemma slot slot₁ slot₂ req-f req-g ps bound-g bound-f =
      ≤-trans (+-monoˡ-≤ ps alloc₂-bound) (≤-reflexive step2)
      where
        alloc₂-bound : slot₂ ≤ (slot + req-f) + req-g
        alloc₂-bound = ≤-trans bound-g (+-monoˡ-≤ req-g bound-f)
        step2 : ((slot + req-f) + req-g) + ps ≡ slot + ((req-f + req-g) + ps)
        step2 = trans (cong (_+ ps) (+-assoc slot req-f req-g))
                      (+-assoc slot (req-f + req-g) ps)

    -- suc n < n + 2
    suc<+2 : ∀ n → suc n < n + pair-slots
    suc<+2 n = subst (suc (suc n) ≤_) (sym eq) (s≤s (s≤s ≤-refl))
      where
        open import Data.Nat.Properties using (+-suc; +-identityʳ)
        eq : n + pair-slots ≡ suc (suc n)
        eq = trans (+-suc n 1) (cong suc (trans (+-suc n 0) (cong suc (+-identityʳ n))))

  -- Pair implementation
  -- RecDispatcher handles Acc internally - no Acc parameters needed here
  run-pair : ∀ {A B C} (f : IR A B) (g : IR A C)
    (bound : ℕ) (rec : RecDispatcher bound)
    (f<bound : ir-size f < bound) (g<bound : ir-size g < bound)
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAt alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    IRResultA ⟨ f , g ⟩ x s alloc
  run-pair f g bound rec f<bound g<bound x input-loc s alloc input-valid input-before not-halted rdi-eq = record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc₃
      ; result-valid = pair-valid
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = IRResultA.not-halted result-g
      ; frame-preserved = trans (trans refl (IRResultA.frame-preserved result-g)) (IRResultA.frame-preserved result-f)
      ; slot-monotone = ≤-trans (≤-trans (IRResultA.slot-monotone result-f) (IRResultA.slot-monotone result-g)) (m≤m+n (next-slot alloc₂) pair-slots)
      ; heap-monotone = ≤-trans (IRResultA.heap-monotone result-f) (IRResultA.heap-monotone result-g)
      ; slot-bounded = pair-slot-bounded-lemma (next-slot alloc) (next-slot alloc₁) (next-slot alloc₂) (ir-stack-requirement f) (ir-stack-requirement g) pair-slots (IRResultA.slot-bounded result-g) (IRResultA.slot-bounded result-f)
      ; capacity-preserved = trans (IRResultA.capacity-preserved result-g) (IRResultA.capacity-preserved result-f)
      }
    where
      -- Run f via dispatcher
      result-f = rec f f<bound x input-loc s alloc input-valid input-before not-halted rdi-eq
      s₁ = IRResultA.final-state result-f
      alloc₁ = IRResultA.final-alloc result-f
      s₁-rdi = record s₁ { regs = writeReg (regs s₁) RDI input-loc }
      input-before₁ = frontier-monotone alloc alloc₁
                        (sym (IRResultA.frame-preserved result-f))
                        (IRResultA.slot-monotone result-f)
                        (IRResultA.heap-monotone result-f)
                        input-loc input-before

      postulate
        input-valid₁ : ValidAt alloc₁ x input-loc s₁-rdi

      -- Run g via dispatcher
      result-g = rec g g<bound x input-loc s₁-rdi alloc₁
                   input-valid₁
                   input-before₁
                   (IRResultA.not-halted result-f)
                   (writeReg-same (regs s₁) RDI input-loc)

      fst-loc = IRResultA.result-loc result-f
      fst-before = IRResultA.result-before result-f
      s₂ = IRResultA.final-state result-g
      alloc₂ = IRResultA.final-alloc result-g
      snd-loc = IRResultA.result-loc result-g
      snd-before = IRResultA.result-before result-g
      pair-loc = OnStack (current-frame alloc₂) (next-slot alloc₂)

      postulate
        pair-fits : next-slot alloc₂ + pair-slots ≤ frame-capacity alloc₂

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc₂
        { next-slot = next-slot alloc₂ + pair-slots
        ; slots-available = pair-fits
        }

      s₃ = write-loc s₂ pair-loc fst-loc
      s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
      s-final = record s₄ { regs = writeReg (regs s₄) RAX pair-loc }

      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl (m<m+n (next-slot alloc₂) (s≤s z≤n))

      sucLoc-pair-before : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before = stack-before refl (suc<+2 (next-slot alloc₂))

      pair-ptr : readLoc s-final pair-loc ≡ just fst-loc
      pair-ptr = trans refl (trans
                   (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc pair-loc (sucLoc-neq pair-loc))
                   (write-read-same s₂ pair-loc fst-loc))

      snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
      snd-ptr = write-read-same s₃ (sucLoc pair-loc) snd-loc

      fst-before-alloc₂ : BeforeFrontier alloc₂ fst-loc
      fst-before-alloc₂ = frontier-monotone alloc₁ alloc₂
                            (sym (IRResultA.frame-preserved result-g))
                            (IRResultA.slot-monotone result-g)
                            (IRResultA.heap-monotone result-g)
                            fst-loc fst-before

      fst-before₃ : BeforeFrontier alloc₃ fst-loc
      fst-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits fst-loc fst-before-alloc₂

      snd-before₃ : BeforeFrontier alloc₃ snd-loc
      snd-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits snd-loc snd-before

      postulate
        fst-valid-final : ValidAt alloc₃ (eval f x) fst-loc s-final
        snd-valid-final : ValidAt alloc₃ (eval g x) snd-loc s-final

      pair-valid : ValidAt alloc₃ (eval ⟨ f , g ⟩ x) pair-loc s-final
      pair-valid = valid-pair pair-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before fst-valid-final snd-valid-final

      rax-eq : readReg (regs s-final) RAX ≡ pair-loc
      rax-eq = writeReg-same (regs s₄) RAX pair-loc
