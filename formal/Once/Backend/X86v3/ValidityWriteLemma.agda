------------------------------------------------------------------------
-- Once.Backend.X86v3.ValidityWriteLemma
--
-- Validity preservation lemmas for writes to frontier locations.
-- Extracted from Dispatcher.agda for faster compilation.
------------------------------------------------------------------------

module Once.Backend.X86v3.ValidityWriteLemma where

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Validity Write Lemmas Module
------------------------------------------------------------------------

module ValidityWriteLemmas {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open FrameSemantics FS

  -- Import write operations from separate module
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  ------------------------------------------------------------------------
  -- Frontier inequality lemmas
  ------------------------------------------------------------------------

  -- Helper: slot at next-slot is different from any slot before frontier
  at-frontier-neq-before : ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    OnStack (current-frame alloc) (next-slot alloc) ≢ loc
  at-frontier-neq-before alloc loc bf eq = fresh-stack-after alloc loc bf (sym eq)

  -- Helper: slot at suc next-slot is different from any slot before frontier
  suc-frontier-neq-before : ∀ (alloc : AllocState {FS}) (loc : ValueLocation FS) →
    BeforeFrontier alloc loc →
    OnStack (current-frame alloc) (suc (next-slot alloc)) ≢ loc
  suc-frontier-neq-before alloc (OnStack .(current-frame alloc) .(suc (next-slot alloc)))
    (stack-before refl k<next) refl =
    -- k<next : suc (suc (next-slot alloc)) ≤ next-slot alloc, which is absurd
    ⊥-elim (1+n≰n (<⇒≤ k<next))
    where
      open import Data.Nat.Properties using (1+n≰n; <⇒≤)
  suc-frontier-neq-before alloc (OnStack f k) (stack-ancestor cf≺f _) eq
    with eq
  ... | refl = ≺⇒≢ cf≺f refl
  suc-frontier-neq-before alloc (OnHeap r o) _ ()

  ------------------------------------------------------------------------
  -- Validity preservation under writes to at-frontier locations
  --
  -- Key insight: if we write to OnStack cf (next-slot alloc), and all
  -- existing valid locations are BeforeFrontier, then the write doesn't
  -- affect any existing valid data.
  ------------------------------------------------------------------------

  -- Validity is preserved when writing to at-frontier location
  validity-write-at-frontier : ∀ {alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAt alloc v loc s →
    ValidAt alloc v loc (write-loc s (OnStack (current-frame alloc) (next-slot alloc)) val)

  validity-write-at-frontier {alloc} {Unit} tt loc s val loc-before valid-unit = valid-unit

  validity-write-at-frontier {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair fp' sp' fb sb slb fv' sv'
    where
      fresh = OnStack (current-frame alloc) (next-slot alloc)

      fp' : readLoc (write-loc s fresh val) loc ≡ just fl
      fp' = trans (write-preserves-disjoint s fresh val loc
                    (at-frontier-neq-before alloc loc loc-before)) fp

      sp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just sl
      sp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (at-frontier-neq-before alloc (sucLoc loc) slb)) sp

      fv' = validity-write-at-frontier a fl s val fb fv
      sv' = validity-write-at-frontier b sl s val sb sv

  validity-write-at-frontier {alloc} {A ⇒ B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure {_} {.A} {.B} {body} {env} ba {.loc} {el} {cl} {.s} ep cp eb cb slb ev) =
    valid-closure {body = body} {env = env} ba ep' cp' eb cb slb ev'
    where
      fresh = OnStack (current-frame alloc) (next-slot alloc)

      ep' : readLoc (write-loc s fresh val) loc ≡ just el
      ep' = trans (write-preserves-disjoint s fresh val loc
                    (at-frontier-neq-before alloc loc loc-before)) ep

      cp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just cl
      cp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (at-frontier-neq-before alloc (sucLoc loc) slb)) cp

      ev' = validity-write-at-frontier env el s val eb ev

  -- Same for suc next-slot (slot index next-slot + 1)
  validity-write-at-suc-frontier : ∀ {alloc A} (v : ⟦ A ⟧) (loc : ValueLocation FS)
    (s : LocState FS) (val : ValueLocation FS) →
    BeforeFrontier alloc loc →
    ValidAt alloc v loc s →
    ValidAt alloc v loc (write-loc s (OnStack (current-frame alloc) (suc (next-slot alloc))) val)

  validity-write-at-suc-frontier {alloc} {Unit} tt loc s val loc-before valid-unit = valid-unit

  validity-write-at-suc-frontier {alloc} {A * B} (a , b) loc s val loc-before
    (valid-pair {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair fp' sp' fb sb slb fv' sv'
    where
      fresh = OnStack (current-frame alloc) (suc (next-slot alloc))

      fp' : readLoc (write-loc s fresh val) loc ≡ just fl
      fp' = trans (write-preserves-disjoint s fresh val loc
                    (suc-frontier-neq-before alloc loc loc-before)) fp

      sp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just sl
      sp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (suc-frontier-neq-before alloc (sucLoc loc) slb)) sp

      fv' = validity-write-at-suc-frontier a fl s val fb fv
      sv' = validity-write-at-suc-frontier b sl s val sb sv

  validity-write-at-suc-frontier {alloc} {A ⇒ B} .(λ arg → eval body (pair env arg)) loc s val loc-before
    (valid-closure {_} {.A} {.B} {body} {env} ba {.loc} {el} {cl} {.s} ep cp eb cb slb ev) =
    valid-closure {body = body} {env = env} ba ep' cp' eb cb slb ev'
    where
      fresh = OnStack (current-frame alloc) (suc (next-slot alloc))

      ep' : readLoc (write-loc s fresh val) loc ≡ just el
      ep' = trans (write-preserves-disjoint s fresh val loc
                    (suc-frontier-neq-before alloc loc loc-before)) ep

      cp' : readLoc (write-loc s fresh val) (sucLoc loc) ≡ just cl
      cp' = trans (write-preserves-disjoint s fresh val (sucLoc loc)
                    (suc-frontier-neq-before alloc (sucLoc loc) slb)) cp

      ev' = validity-write-at-suc-frontier env el s val eb ev
