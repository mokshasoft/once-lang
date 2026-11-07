-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell.Build
--
-- The FACTS about the two-cell build's end state (`TwoCellRun`): what it
-- reads back, its frontier and what it leaves alone.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.TwoCell.Build (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtDynamic; AtStack; ValueLocation)
open import Once.CCC.Machine.SMCore using (AllocState; AbstractTrace; LocState; StoredValue; sucLoc; readReg; Output; SV-Code; SV-Ptr; module LocState; module AllocState)
open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)
open LocState using (halted; regs)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; module HeapRef; module HeapLocation)
import Once.CCC.Machine.FlatAlloc as FlatAlloc

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.Denotation.ValueDomain as ValueDomain

open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Run o tbl

module TwoCellBuildC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open TwoCellRunC {FS}
  open SMCore.MemOps {FS} using (writeLoc-preserves-other)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)

  module TwoCellBuild
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (two-cell-trace n l))
    where
    open TwoCellRun n l prog base s alloc cl rs n≤ nh span

    -- ── The frontier: the allocation hands out a fresh ref and moves past it.
    heapref-≤ : next-heap-ref alloc ≤ next-heap-ref (falloc fs10)
    heapref-≤ = n≤1+n _

    nextslot-≤ : next-slot alloc ≤ next-slot (falloc fs10)
    nextslot-≤ = ≤-refl

    cf-fs10 : current-frame (falloc fs10) ≡ current-frame alloc
    cf-fs10 = refl

    sf-fs10 : saved-frames (falloc fs10) ≡ saved-frames alloc
    sf-fs10 = refl

    before : BeforeFrontier (falloc fs10) obj-loc
    before = FlatAlloc.alloc-live {FS} 2 alloc 0

    before-suc : BeforeFrontier (falloc fs10) (sucLoc obj-loc)
    before-suc = FlatAlloc.alloc-live {FS} 2 alloc 1

    blocks-kept : BlocksKept alloc (falloc fs10)
    blocks-kept = FlatAlloc.alloc-bk {FS} 2 alloc

    -- ── The two cells, and the result.
    cell0-fs10 : SMCore.MemOps.readLoc (floc fs10) obj-loc ≡ just cell0v
    cell0-fs10 =
      trans (writeLoc-preserves-other t₈ (sucLoc obj-loc) obj-loc code (λ e → 0≢1 (cong off-of e)))
            (readLoc-writeLoc-same t₆ obj-loc cell0v)
      where
        off-of : ValueLocation FS → ℕ
        off-of (AtDynamic (heap-loc _ o′)) = o′
        off-of (AtStack _ _) = 0
        0≢1 : 1 ≡ 0 → ⊥
        0≢1 ()

    code-fs10 : SMCore.MemOps.readLoc (floc fs10) (sucLoc obj-loc) ≡ just (SV-Code code-lbl)
    code-fs10 = readLoc-writeLoc-same t₈ (sucLoc obj-loc) code

    out-eq : readReg (regs (floc fs10)) Output ≡ SV-Ptr obj-loc
    out-eq = refl

    bf-advance : ∀ {lc : ValueLocation FS} → BeforeFrontier alloc lc
               → BeforeFrontier (falloc fs10) lc
    bf-advance (BeforeFrontier.stack-before f≡cf k<ns) =
      BeforeFrontier.stack-before f≡cf k<ns
    bf-advance (BeforeFrontier.stack-ancestor cf≺f src) =
      BeforeFrontier.stack-ancestor cf≺f src
    bf-advance (BeforeFrontier.heap-before r<h) =
      BeforeFrontier.heap-before (<-≤-trans r<h heapref-≤)

    -- D204: what the build LEAVES ALONE — two slots at and above `n`, and the
    -- fresh block.
    mem-pres : ∀ (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = n }) loc
             → SMCore.MemOps.readLoc (floc fs10) loc ≡ SMCore.MemOps.readLoc s loc
    mem-pres (AtDynamic hl) (BeforeFrontier.heap-before p) =
      trans (writeLoc-preserves-other t₈ (sucLoc obj-loc) (AtDynamic hl) code (ne _))
            (writeLoc-preserves-other t₆ obj-loc (AtDynamic hl) cell0v (ne _))
      where
        ref-of : ValueLocation FS → ℕ
        ref-of (AtDynamic h) = HeapRef.ref-id (HeapLocation.heap-ref h)
        ref-of (AtStack _ _) = 0
        ne : ∀ o′ → AtDynamic (heap-loc rd o′) ≢ AtDynamic hl
        ne o′ e = <-irrefl (sym (cong ref-of e)) p
    mem-pres (AtStack fr j) bf =
      trans (writeLoc-preserves-other t₈ (sucLoc obj-loc) (AtStack fr j) code (λ ()))
     (trans (writeLoc-preserves-other t₆ obj-loc (AtStack fr j) cell0v (λ ()))
     (trans (store-slot-preserves-before (suc n) t₃ (record alloc { next-slot = n }) A₁ (AtStack fr j) refl (n≤1+n n) bf)
            (store-slot-preserves-before n t₁ (record alloc { next-slot = n }) alloc (AtStack fr j) refl ≤-refl bf)))

    -- The input's validity, carried from the entry state to `fs10`.
    -- `{A}` is PINNED at every application: `⟦_⟧ᴰᴵ` is not constructor-headed
    -- (D180), so nothing here determines it from the value's type.
    valid-transport : ∀ {mIn A} (x : ValueDomain.⟦ A ⟧ᴰᴵ) (loc : ValueLocation FS)
                    → BeforeFrontier alloc loc
                    → ValidAtWF {prog = prog} mIn alloc {A} x loc s
                    → ValidAtWF {prog = prog} mIn (falloc fs10) {A} x loc (floc fs10)
    valid-transport {A = A} x loc bf valid =
      validityWF-frontier-advance {A = A} x loc (floc fs10)
        cf-fs10 nextslot-≤ heapref-≤ blocks-kept
        (validityWF-mem-preserved {A = A} x loc s (floc fs10) bf
           (λ loc' bf' → mem-pres loc'
                           (frontier-monotone alloc (record alloc { next-slot = n })
                              refl n≤ ≤-refl loc' bf'))
           valid)
