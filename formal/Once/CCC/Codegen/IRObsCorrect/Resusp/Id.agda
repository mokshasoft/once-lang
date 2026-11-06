-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Id
--
-- plan 0.135 S3: THE RECURSIVE POSITION of the re-suspension
-- (`resuspend-layer … wf-Id`, nineteen straight rows). Output holds the
-- seed `a′`; the rows build the pair `(e , a′)` — its first cell copied
-- from the forced suspension's own seed pair (slot 0), its second the seed —
-- and then the two-cell suspension `[pair , code]` of this block, the same
-- nine-row heap build `TwoCell` runs (`NineStepPres`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Id (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.IdRows o tbl using (module ResuspIdRowsC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Code; SV-Ptr; sucLoc
        ; store-at-slot; restore-input; load-from-slot; load-indirect; store-indirect
        ; store-indirect-suc; mov-to-input; instr-alloc-heap; instr-load-code-addr; sv-as-loc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ; LabelId)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-Id)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot; nhw-restore-input)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL)
open import Data.Nat using (z≤n; s≤s)
open import Data.Sum using (inj₁; inj₂)

module ResuspIdC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  module RId {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
             (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
             (prog : AbstractTrace) (lbl-n : ℕ)
             (R : VTy (ν-type F))
             (mk-child : ∀ {alloc ν-loc s} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                       → LocMatchesMode Heap ν-loc
                       → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                       → Live alloc (sucLoc ν-loc)
                       → CellAt {prog = prog} alloc (E IRTy′.* A) (e , a′) ν-loc s
                       → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
             where

    open RBase wf coalg e prog lbl-n R mk-child

    module Run (n l : ℕ) (σ : FlatState) (y : ValueDomain.⟦ A ⟧ᴰᴵ) (pl : ValueLocation FS)
               (span : SpanAt prog (fpc σ) (rtrace wf-Id n l))
               (nh0 : halted (floc σ) ≡ false) (lk : flink σ ≡ nothing)
               (ns0 : next-slot (falloc σ) ≡ 0) (n≥1 : 1 ≤ n)
               (sl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl))
               (b : AllocState {FS}) (hb : next-heap-ref b ≤ next-heap-ref (falloc σ))
               (lpl : Live b pl)
               (cE : CellAt {prog = prog} b E e pl (floc σ))
               (oA : OutAt′ {A} b y (floc σ))
               where
      open ResuspIdRowsC.RId {FS} {F} wf {E} {A} coalg e prog lbl-n R mk-child
      open Run n l σ y pl span nh0 lk ns0 n≥1 sl0 b hb lpl cE oA
      open NSP using (u2; u3; u4; u5; u6; u7; u8; u9; u10)

      -- The 19-row run in three nested pieces, each with its type (rows
      -- 1-based as above; `span i` is row i+1): `srC` is rows 15–19 (u5 → u10,
      -- 5 steps), `srB` is rows 8–14 followed by `srC` (t7 → u10, 12 steps),
      -- and `sr` is rows 1–7 followed by `srB` (σ → u10, all 19). Unifying the
      -- whole chain as one term cost ~5 GB (each step's implicit state and
      -- instruction).
      srC : SRun prog 5 u5 u10
      srC =
        s-at {prog} {u5} {4} {u10} u6 (nhu5 , span 14 _ refl) refl refl tt (
        s-at {prog} {u6} {3} {u10} u7 (nhu6 , span 15 _ refl) refl refl tt (
        s-at {prog} {u7} {2} {u10} u8 (nhu7 , span 16 _ refl) refl refl tt (
        s-at {prog} {u8} {1} {u10} u9 (nhu8 , span 17 _ refl) refl refl tt (
        s-at {prog} {u9} {0} {u10} u10 (nhu9 , span 18 _ refl) refl refl tt (
        s-nil)))))

      srB : SRun prog 12 t7 u10
      srB =
        s-at {prog} {t7} {11} {u10} t8 (nh7 , span 7 _ refl) refl refl tt (
        s-at {prog} {t8} {10} {u10} t9 (nh8 , span 8 _ refl) refl refl tt (
        s-at {prog} {t9} {9} {u10} t10 (nh9 , span 9 _ refl) refl refl tt (
        s-at {prog} {t10} {8} {u10} u2 (nh10 , span 10 _ refl) refl refl tt (
        s-at {prog} {u2} {7} {u10} u3 (nhu2 , span 11 _ refl) refl refl tt (
        s-at {prog} {u3} {6} {u10} u4 (nhu3 , span 12 _ refl) refl refl tt (
        s-at {prog} {u4} {5} {u10} u5 (nhu4 , span 13 _ refl) refl refl tt srC))))))

      sr : SRun prog 19 σ u10
      sr =
        s-at {prog} {σ} {18} {u10} t1 (nh0 , span 0 _ refl) refl refl tt (
        s-at {prog} {t1} {17} {u10} t2 (nh1 , span 1 _ refl) refl refl tt (
        s-at {prog} {t2} {16} {u10} t3 (nh2 , span 2 _ refl) refl refl tt (
        s-at {prog} {t3} {15} {u10} t4 (nh3 , span 3 _ refl) refl refl tt (
        s-at {prog} {t4} {14} {u10} t5 (nh4 , span 4 _ refl) refl refl tt (
        s-at {prog} {t5} {13} {u10} t6 (nh5 , span 5 _ refl) refl refl tt (
        s-at {prog} {t6} {12} {u10} t7 (nh6 , span 6 _ refl) refl refl tt srB))))))

      run : FlatSteps prog 19 σ u10
      run = proj₁ sr

      result : RRuns′ wf-Id n l σ y b
      result = record
        { steps    = 19
        ; settle   = u10
        ; run      = run
        ; nh       = nhu10
        ; pc       = refl
        ; ret      = refl
        ; lnk      = lk
        ; ev       = proj₁ (proj₂ sr)
        ; log      = proj₂ (proj₂ sr)
        ; left     = chain-left run nhu10
        ; out-mode = Heap
        ; rout     = ro-loc (AtDynamic shl) (proj₁ p-s) outu10 child
        ; seg      = seg
        }

    resusp-Id : Resusp′ wf-Id
    resusp-Id n l σ y pl b hb span _ nh lk ns n≥1 sl0 lpl cE oA =
      Run.result n l σ y pl span nh lk ns n≥1 sl0 b hb lpl cE oA
