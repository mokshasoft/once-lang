------------------------------------------------------------------------
-- Once.Backend.X86v3.ValidityChainLemma
--
-- Validity preservation through chains of writes to frontier locations.
-- Extracted from Dispatcher.agda for faster compilation.
--
-- Key insight: When we write to locations at or beyond the current
-- frontier, existing valid data (which is BeforeFrontier) is preserved.
------------------------------------------------------------------------

module Once.Backend.X86v3.ValidityChainLemma where

open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine

------------------------------------------------------------------------
-- Validity Chain Lemmas Module
------------------------------------------------------------------------

module ValidityChainLemmas {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open import Once.Backend.X86v3.Allocation
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open FrameSemantics FS

  -- Import write operations from separate module
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import single write lemmas
  open import Once.Backend.X86v3.ValidityWriteLemma using (module ValidityWriteLemmas)
  open ValidityWriteLemmas {FS} program-bound

  ------------------------------------------------------------------------
  -- Two-write chain: validity preserved through writes to slot n and n+1
  --
  -- Pattern: We have valid data at loc (BeforeFrontier alloc), then:
  --   s₁ = write-loc s (OnStack cf n) val₁
  --   s₂ = write-loc s₁ (OnStack cf (suc n)) val₂
  -- where n = next-slot alloc. The valid data at loc is preserved in s₂.
  --
  -- Used in: fst-valid-final, snd-valid-final, input-valid-final
  ------------------------------------------------------------------------

  validity-two-writes : ∀ {alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val₁ val₂ : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAt alloc v loc s →
    let cf = current-frame alloc
        n = next-slot alloc
        s₁ = write-loc s (OnStack cf n) val₁
        s₂ = write-loc s₁ (OnStack cf (suc n)) val₂
    in ValidAt alloc v loc s₂
  validity-two-writes {alloc} v loc s val₁ val₂ loc-before valid-s =
    let cf = current-frame alloc
        n = next-slot alloc
        s₁ = write-loc s (OnStack cf n) val₁
        valid-s₁ = validity-write-at-frontier v loc s val₁ loc-before valid-s
    in validity-write-at-suc-frontier v loc s₁ val₂ loc-before valid-s₁

  ------------------------------------------------------------------------
  -- Validity with register write: validity preserved after reg update
  --
  -- Pattern: ValidAt ... s → ValidAt ... (record s { regs = ... })
  --
  -- Used in: fst-valid-final, etc. after RAX update
  ------------------------------------------------------------------------

  validity-reg-update : ∀ {alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (r : RegId) (val : ValueLocation FS) →
    ValidAt alloc v loc s →
    ValidAt alloc v loc (record s { regs = writeReg (regs s) r val })
  validity-reg-update v loc s r val valid-s =
    validity-mem-only v loc s (record s { regs = writeReg (regs s) r val }) refl refl valid-s

  ------------------------------------------------------------------------
  -- Full sequence: two writes + register update
  --
  -- Pattern for pair/closure: after allocating 2 slots and writing to them,
  -- plus updating RAX, existing valid data is preserved.
  --
  -- Used in: final validity proofs for fst-loc, snd-loc, env-loc, etc.
  ------------------------------------------------------------------------

  validity-pair-sequence : ∀ {alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val₁ val₂ result-loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAt alloc v loc s →
    let cf = current-frame alloc
        n = next-slot alloc
        s₁ = write-loc s (OnStack cf n) val₁
        s₂ = write-loc s₁ (OnStack cf (suc n)) val₂
        s-final = record s₂ { regs = writeReg (regs s₂) RAX result-loc }
    in ValidAt alloc v loc s-final
  validity-pair-sequence {alloc} v loc s val₁ val₂ result-loc loc-before valid-s =
    let cf = current-frame alloc
        n = next-slot alloc
        s₁ = write-loc s (OnStack cf n) val₁
        s₂ = write-loc s₁ (OnStack cf (suc n)) val₂
        valid-s₂ = validity-two-writes v loc s val₁ val₂ loc-before valid-s
    in validity-reg-update v loc s₂ RAX result-loc valid-s₂

