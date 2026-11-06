-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Call   (plan 0.135 S3, cata M1)
--
-- THE FOURTEEN ROWS BEFORE THE CALL (`cata-call cl k ev pr`, all but its
-- last row `instr-call-closure`), run from where the setup (or a fold round)
-- leaves the machine: `Input1` holds the layer, slot `cl` the closure
-- record, slot `ev` the environment.
--
--     mov-to-output · store k                             k := layer
--       (D366: the first row is `Head`'s — `load-indirect` at a boxed μ)
--     alloc · store pr · mov-to-input · load ev ·
--       store-indirect · load k · store-indirect-suc      pr := FRESH [env , layer]
--     load cl · mov-to-input · save-closure-reg           fclosure := cl
--     load pr · mov-to-input                              Input1 := pr
--
-- The pair is allocated by EVERY call (plan 0.135 D1a): an algebra may keep
-- its argument (`curry` stores it as a closure's environment), so a pair
-- reused across calls would change what earlier results see. So at the call
-- the closure register names the record whose code cell is the algebra's
-- body, and `Input1` points at a block fresh at the call's start holding
-- `[env , layer]` — the algebra's argument. Stated over ANY start state (a
-- parameter, not the setup's last state), so nothing here re-reads the
-- setup's steps.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Call (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.CallRows o tbl using (module CataCallRowsC)
open import Once.CCC.Codegen.IRToTrace o using (cata-call; cata-call-from)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (Head; head-instr)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output; Input1; SV-Code; SV-Ptr; sv-as-loc; store-at-slot; load-from-slot; store-indirect; store-indirect-suc; mov-to-input; mov-to-output; instr-alloc-heap; instr-save-closure-reg; AbstractInstr)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
import Data.Nat as ℕ
open import Data.Nat.Properties using (+-cancelˡ-≡)

module CataCallC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  -- the closure-register move touches neither memory nor allocator
  seg-save : ∀ {a₀ : AllocState {FS}} {n : ℕ} (t : FlatState) → SegA a₀ n t (do-save-closure t)
  seg-save t = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }


  -- WHAT THE CALL ROWS HAND ON, as an opaque bundle (`Setup.SetupOut`'s reason).
  -- `hp` is the FRESH argument pair: its ref is the heap frontier at the
  -- call rows' start, and the rows leave the frontier one past it.
  record CallOut (n : ℕ) (prog : AbstractTrace) (σ : FlatState) (a₀ : AllocState {FS})
                 (hc : HeapLocation) (lbl : LabelId) (env-sv μ-sv : StoredValue FS) : Set where
    field
      w      : FlatState
      runK   : SRun prog 14 σ w
      seg    : SegA a₀ n σ w
      nh     : halted (floc w) ≡ false
      pc     : fpc w ≡ 14 + fpc σ
      ret    : fret w ≡ fret σ
      clo    : fclosure w ≡ SV-Ptr (AtDynamic hc)
      hp     : HeapLocation
      ref-hp : ref-id (heap-ref hp) ≡ next-heap-ref (falloc σ)
      hr     : next-heap-ref (falloc w) ≡ suc (next-heap-ref (falloc σ))
      cf     : current-frame (falloc w) ≡ current-frame (falloc σ)
      inp    : readReg (regs (floc w)) Input1 ≡ SV-Ptr (AtDynamic hp)
      hp0    : readLoc (floc w) (AtDynamic hp) ≡ just env-sv
      shp    : readLoc (floc w) (AtDynamic (sucHL hp)) ≡ just μ-sv
      code   : readLoc (floc w) (AtDynamic (sucHL hc)) ≡ just (SV-Code lbl)
      cl     : readLoc (floc w) (AtStack (current-frame (falloc σ)) n) ≡ just (SV-Ptr (AtDynamic hc))
      ev     : readLoc (floc w) (AtStack (current-frame (falloc σ)) (n ℕ.+ 2)) ≡ just env-sv
      pr     : readLoc (floc w) (AtStack (current-frame (falloc σ)) (n ℕ.+ 3)) ≡ just (SV-Ptr (AtDynamic hp))

  -- D366: the first row is a parameter (`Head`): `mov-to-output` at every
  -- strategy but `strat-box`, whose layer is read out of the box.
  module Call (n : ℕ) (prog : AbstractTrace) (σ : FlatState) (a₀ : AllocState {FS}) (h : Head)
              (span : SpanAt prog (fpc σ) (cata-call-from (head-instr h) n (n ℕ.+ 1) (n ℕ.+ 2) (n ℕ.+ 3)))
              (nh0 : halted (floc σ) ≡ false)
              (hc : HeapLocation) (lbl : LabelId) (env-sv μ-sv : StoredValue FS)
              (hd : HeadOK prog σ h μ-sv)
              (cl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) n) ≡ just (SV-Ptr (AtDynamic hc)))
              (ev0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) (n ℕ.+ 2)) ≡ just env-sv)
              (code0 : readLoc (floc σ) (AtDynamic (sucHL hc)) ≡ just (SV-Code lbl))
              (hc-lt : suc (ref-id (heap-ref hc)) ≤ next-heap-ref (falloc σ))
              (cf0 : current-frame (falloc σ) ≡ current-frame a₀)
              (fresh : next-heap-ref a₀ ≤ next-heap-ref (falloc σ))
              where
    open CataCallRowsC.Rows {FS} n prog σ a₀ h span nh0 hc lbl env-sv μ-sv hd cl0 ev0 code0 hc-lt cf0 fresh

    ------------------------------------------------------------------
    -- THE RUN, silent, and what it leaves alone. Every link names its
    -- states (`{prog} {from} {k} {to}`): left as metas, they are solved
    -- through `SRun`'s log fact, which reduces the machine state — one link
    -- after `do-save-closure` took 35 s that way, 40 ms pinned (plan 0.144).
    ------------------------------------------------------------------
    runA : SRun prog 6 σ w6
    runA =
      s-at {prog} {σ} {5} {w6} w1 (nh0 , span 0 _ refl) (HeadOK.step hd) (HeadOK.ev hd) (HeadOK.lf hd) (
      s-at {prog} {w1} {4} {w6} w2 (nh1 , span 1 _ refl) refl refl tt (
      s-at {prog} {w2} {3} {w6} w3 (nh2 , span 2 _ refl) refl refl tt (
      s-at {prog} {w3} {2} {w6} w4 (nh3 , span 3 _ refl) refl refl tt (
      s-at {prog} {w4} {1} {w6} w5 (nh4 , span 4 _ refl) refl refl tt (
      s-at {prog} {w5} {0} {w6} w6 (nh5 , span 5 _ refl) refl refl tt s-nil)))))

    runB : SRun prog 8 w6 w14
    runB =
      s-at {prog} {w6} {7} {w14} w7 (nh6 , span 6 _ refl) refl refl tt (
      s-at {prog} {w7} {6} {w14} w8 (nh7 , span 7 _ refl) refl refl tt (
      s-at {prog} {w8} {5} {w14} w9 (nh8 , span 8 _ refl) refl refl tt (
      s-at {prog} {w9} {4} {w14} w10 (nh9 , span 9 _ refl) refl refl tt (
      s-at {prog} {w10} {3} {w14} w11 (nh10 , span 10 _ refl) refl refl tt (
      s-at {prog} {w11} {2} {w14} w12 (nh11 , span 11 _ refl) refl refl tt (
      s-at {prog} {w12} {1} {w14} w13 (nh11 , span 12 _ refl) refl refl tt (
      s-at {prog} {w13} {0} {w14} w14 (nh13 , span 13 _ refl) refl refl tt s-nil)))))))

    runK : SRun prog 14 σ w14
    runK = s-++ {prog} {6} {8} {σ} {w6} {w14} runA runB

    abstract
      seg : SegA a₀ n σ w14
      seg =
        segA-∘ (seg-q (head-instr h) σ (HeadOK.nhw hd) (HeadOK.nws hd) (HeadOK.ff hd) (HeadOK.eh hd))
        (segA-∘ (seg-store ks w1 (trans cf1 cf0) (m≤m+n n 1))
        (segA-∘ (seg-alloc w2)
        (segA-∘ (seg-store pr w3 (trans cf3 cf0) (m≤m+n n 3))
        (segA-∘ (seg-q mov-to-input w4 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-q (load-from-slot ev) w5 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-sind w6 hp rdi7 frhp)
        (segA-∘ (seg-q (load-from-slot ks) w7 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-sind-suc w8 hp rdi9 frhp)
        (segA-∘ (seg-q (load-from-slot n) w9 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-q mov-to-input w10 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-save w11)
        (segA-∘ (seg-q (load-from-slot pr) w12 nhw-load-from-slot refl tt tt)
                (seg-q mov-to-input w13 nhw-mov-to-input refl tt tt)))))))))))))

    abstract
      out : CallOut n prog σ a₀ hc lbl env-sv μ-sv
      out = record
        { w = w14 ; runK = runK ; seg = seg ; nh = nh14 ; pc = refl ; ret = refl ; clo = clo14
        ; hp = hp ; ref-hp = hr2 ; hr = hr14 ; cf = cf14
        ; inp = in14 ; hp0 = hp14 ; shp = shp14 ; code = code14
        ; cl = cl14 ; ev = ev14 ; pr = pr14 }
