-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Call   (plan 0.125 S3, cata M1)
--
-- THE ELEVEN ROWS BEFORE THE CALL (`cata-call cl k pr`, all but its last
-- row `instr-call-closure`), run from where the setup leaves the machine:
-- `Input1` holds the μ cell, slot `cl` the closure record, slot `pr` the
-- argument pair.
--
--     mov-to-output · store k · load pr · mov-to-input · load k ·
--       store-indirect-suc                                pr[1] := μ
--     load cl · mov-to-input · save-closure-reg           fclosure := cl
--     load pr · mov-to-input                              Input1 := pr
--
-- So at the call the closure register names the record whose code cell is
-- the algebra's body, and `Input1` points at the pair `[env , μ]` — the
-- algebra's argument. Stated over ANY start state (a parameter, not the
-- setup's last state), so nothing here re-reads the setup's eighteen steps.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Call (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRToTrace o using (cata-call)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output; Input1; SV-Code; SV-Ptr; sv-as-loc; store-at-slot; load-from-slot; store-indirect-suc; mov-to-input; mov-to-output; instr-save-closure-reg)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; module HeapLocation; module HeapRef)
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
  record CallOut (n : ℕ) (prog : AbstractTrace) (σ : FlatState) (a₀ : AllocState {FS})
                 (hp hc : HeapLocation) (lbl : LabelId) (env-sv μ-sv : StoredValue FS) : Set where
    field
      w    : FlatState
      runK : SRun prog 11 σ w
      seg  : SegA a₀ n σ w
      nh   : halted (floc w) ≡ false
      pc   : fpc w ≡ 11 + fpc σ
      ret  : fret w ≡ fret σ
      clo  : fclosure w ≡ SV-Ptr (AtDynamic hc)
      inp  : readReg (regs (floc w)) Input1 ≡ SV-Ptr (AtDynamic hp)
      hp0  : readLoc (floc w) (AtDynamic hp) ≡ just env-sv
      shp  : readLoc (floc w) (AtDynamic (sucHL hp)) ≡ just μ-sv
      code : readLoc (floc w) (AtDynamic (sucHL hc)) ≡ just (SV-Code lbl)

  module Call (n : ℕ) (prog : AbstractTrace) (σ : FlatState) (a₀ : AllocState {FS})
              (span : SpanAt prog (fpc σ) (cata-call n (n ℕ.+ 1) (n ℕ.+ 3)))
              (nh0 : halted (floc σ) ≡ false)
              (hp hc : HeapLocation) (lbl : LabelId) (env-sv μ-sv : StoredValue FS)
              (in0 : readReg (regs (floc σ)) Input1 ≡ μ-sv)
              (cl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) n) ≡ just (SV-Ptr (AtDynamic hc)))
              (pr0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) (n ℕ.+ 3)) ≡ just (SV-Ptr (AtDynamic hp)))
              (hp0 : readLoc (floc σ) (AtDynamic hp) ≡ just env-sv)
              (code0 : readLoc (floc σ) (AtDynamic (sucHL hc)) ≡ just (SV-Code lbl))
              (shp≢shc : AtDynamic {FS} (sucHL hp) ≢ AtDynamic (sucHL hc))
              (cf0 : current-frame (falloc σ) ≡ current-frame a₀)
              (fresh : next-heap-ref a₀ ≤ ref-id (heap-ref hp))
              where

    f₀ = current-frame (falloc σ)

    ks pr : ℕ
    ks = n ℕ.+ 1
    pr = n ℕ.+ 3

    n≢ks : n ≢ ks
    n≢ks e with +-cancelˡ-≡ n 0 1 (trans (+-identityʳ n) e)
    ... | ()
    pr≢ks : pr ≢ ks
    pr≢ks e with +-cancelˡ-≡ n 3 1 e
    ... | ()

    w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : FlatState
    w1  = St mov-to-output σ
    w2  = St (store-at-slot ks) w1
    w3  = St (load-from-slot pr) w2
    w4  = St mov-to-input w3
    w5  = St (load-from-slot ks) w4
    w6  = St store-indirect-suc w5
    w7  = St (load-from-slot n) w6
    w8  = St mov-to-input w7
    w9  = do-save-closure w8
    w10 = St (load-from-slot pr) w9
    w11 = St mov-to-input w10

    Inp Oup : FlatState → StoredValue FS
    Inp t = readReg (regs (floc t)) Input1
    Oup t = readReg (regs (floc t)) Output

    sl : FlatState → ℕ → Maybe (StoredValue FS)
    sl t j = readLoc (floc t) (AtStack f₀ j)

    hpr : FlatState → HeapLocation → Maybe (StoredValue FS)
    hpr t h = readLoc (floc t) (AtDynamic h)

    ------------------------------------------------------------------
    -- rows 1-6: the pair's second cell := the μ cell
    ------------------------------------------------------------------
    nh1 : halted (floc w1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc σ) (falloc σ) nh0 tt
    out1 : Oup w1 ≡ μ-sv
    out1 = trans (out-movout (floc σ) (falloc σ)) in0
    cl1 : sl w1 n ≡ just (SV-Ptr (AtDynamic hc))
    cl1 = trans (sl-keep mov-to-output (floc σ) (falloc σ) f₀ n nhw-mov-to-output refl) cl0
    pr1 : sl w1 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr1 = trans (sl-keep mov-to-output (floc σ) (falloc σ) f₀ pr nhw-mov-to-output refl) pr0
    hp1 : hpr w1 hp ≡ just env-sv
    hp1 = trans (hp-keep mov-to-output (floc σ) (falloc σ) hp nhw-mov-to-output) hp0
    code1 : hpr w1 (sucHL hc) ≡ just (SV-Code lbl)
    code1 = trans (hp-keep mov-to-output (floc σ) (falloc σ) (sucHL hc) nhw-mov-to-output) code0

    nh2 : halted (floc w2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (store-at-slot ks) (floc w1) (falloc w1) nh1 tt
    ks2 : sl w2 ks ≡ just μ-sv
    ks2 = trans (sl-same ks (floc w1) (falloc w1) f₀ refl) (cong just out1)
    cl2 : sl w2 n ≡ just (SV-Ptr (AtDynamic hc))
    cl2 = trans (sl-other ks n (floc w1) (falloc w1) f₀ n≢ks) cl1
    pr2 : sl w2 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr2 = trans (sl-other ks pr (floc w1) (falloc w1) f₀ pr≢ks) pr1
    hp2 : hpr w2 hp ≡ just env-sv
    hp2 = trans (hp-keep (store-at-slot ks) (floc w1) (falloc w1) hp nhw-store-at-slot) hp1
    code2 : hpr w2 (sucHL hc) ≡ just (SV-Code lbl)
    code2 = trans (hp-keep (store-at-slot ks) (floc w1) (falloc w1) (sucHL hc) nhw-store-at-slot) code1

    wf3 : InstrWF (floc w2) (falloc w2) (load-from-slot pr)
    wf3 = SV-Ptr (AtDynamic hp) , pr2
    nh3 : halted (floc w3) ≡ false
    nh3 = exec-abstract-preserves-halted-WF (load-from-slot pr) (floc w2) (falloc w2) nh2 wf3
    out3 : Oup w3 ≡ SV-Ptr (AtDynamic hp)
    out3 = out-lslot pr (floc w2) (falloc w2) _ pr2
    ks3 : sl w3 ks ≡ just μ-sv
    ks3 = trans (sl-keep (load-from-slot pr) (floc w2) (falloc w2) f₀ ks nhw-load-from-slot refl) ks2
    cl3 : sl w3 n ≡ just (SV-Ptr (AtDynamic hc))
    cl3 = trans (sl-keep (load-from-slot pr) (floc w2) (falloc w2) f₀ n nhw-load-from-slot refl) cl2
    pr3 : sl w3 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr3 = trans (sl-keep (load-from-slot pr) (floc w2) (falloc w2) f₀ pr nhw-load-from-slot refl) pr2
    hp3 : hpr w3 hp ≡ just env-sv
    hp3 = trans (hp-keep (load-from-slot pr) (floc w2) (falloc w2) hp nhw-load-from-slot) hp2
    code3 : hpr w3 (sucHL hc) ≡ just (SV-Code lbl)
    code3 = trans (hp-keep (load-from-slot pr) (floc w2) (falloc w2) (sucHL hc) nhw-load-from-slot) code2
    cf3 : current-frame (falloc w3) ≡ f₀
    cf3 = exec-abstract-preserves-frame (load-from-slot pr) (floc w2) (falloc w2)

    nh4 : halted (floc w4) ≡ false
    nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc w3) (falloc w3) nh3 tt
    in4 : Inp w4 ≡ SV-Ptr (AtDynamic hp)
    in4 = trans (in-movin (floc w3) (falloc w3)) out3
    ks4 : sl w4 ks ≡ just μ-sv
    ks4 = trans (sl-keep mov-to-input (floc w3) (falloc w3) f₀ ks nhw-mov-to-input refl) ks3
    cl4 : sl w4 n ≡ just (SV-Ptr (AtDynamic hc))
    cl4 = trans (sl-keep mov-to-input (floc w3) (falloc w3) f₀ n nhw-mov-to-input refl) cl3
    pr4 : sl w4 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr4 = trans (sl-keep mov-to-input (floc w3) (falloc w3) f₀ pr nhw-mov-to-input refl) pr3
    hp4 : hpr w4 hp ≡ just env-sv
    hp4 = trans (hp-keep mov-to-input (floc w3) (falloc w3) hp nhw-mov-to-input) hp3
    code4 : hpr w4 (sucHL hc) ≡ just (SV-Code lbl)
    code4 = trans (hp-keep mov-to-input (floc w3) (falloc w3) (sucHL hc) nhw-mov-to-input) code3

    wf5 : InstrWF (floc w4) (falloc w4) (load-from-slot ks)
    wf5 = μ-sv , at-cf (floc w4) (falloc w4) cf3 ks4
    nh5 : halted (floc w5) ≡ false
    nh5 = exec-abstract-preserves-halted-WF (load-from-slot ks) (floc w4) (falloc w4) nh4 wf5
    out5 : Oup w5 ≡ μ-sv
    out5 = out-lslot ks (floc w4) (falloc w4) μ-sv (proj₂ wf5)
    in5 : Inp w5 ≡ SV-Ptr (AtDynamic hp)
    in5 = trans (in-lslot ks (floc w4) (falloc w4) μ-sv (proj₂ wf5)) in4
    cl5 : sl w5 n ≡ just (SV-Ptr (AtDynamic hc))
    cl5 = trans (sl-keep (load-from-slot ks) (floc w4) (falloc w4) f₀ n nhw-load-from-slot refl) cl4
    pr5 : sl w5 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr5 = trans (sl-keep (load-from-slot ks) (floc w4) (falloc w4) f₀ pr nhw-load-from-slot refl) pr4
    hp5 : hpr w5 hp ≡ just env-sv
    hp5 = trans (hp-keep (load-from-slot ks) (floc w4) (falloc w4) hp nhw-load-from-slot) hp4
    code5 : hpr w5 (sucHL hc) ≡ just (SV-Code lbl)
    code5 = trans (hp-keep (load-from-slot ks) (floc w4) (falloc w4) (sucHL hc) nhw-load-from-slot) code4
    cf5 : current-frame (falloc w5) ≡ f₀
    cf5 = trans (exec-abstract-preserves-frame (load-from-slot ks) (floc w4) (falloc w4)) cf3

    rdi6 : sv-as-loc (Inp w5) ≡ just (AtDynamic hp)
    rdi6 = cong sv-as-loc in5
    nh6 : halted (floc w6) ≡ false
    nh6 = exec-abstract-preserves-halted-WF store-indirect-suc (floc w5) (falloc w5) nh5 (AtDynamic hp , rdi6)
    shp6 : hpr w6 (sucHL hp) ≡ just μ-sv
    shp6 = trans (store-ind-suc-result (floc w5) (falloc w5) hp rdi6) (cong just out5)
    hp6 : hpr w6 hp ≡ just env-sv
    hp6 = trans (store-ind-suc-preserves-heap (floc w5) (falloc w5) hp hp rdi6 (sucHL-≢ hp)) hp5
    code6 : hpr w6 (sucHL hc) ≡ just (SV-Code lbl)
    code6 = trans (store-ind-suc-preserves-heap (floc w5) (falloc w5) hp (sucHL hc) rdi6 shp≢shc) code5
    cl6 : sl w6 n ≡ just (SV-Ptr (AtDynamic hc))
    cl6 = trans (sl-sind-suc (floc w5) (falloc w5) hp f₀ n rdi6) cl5
    pr6 : sl w6 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr6 = trans (sl-sind-suc (floc w5) (falloc w5) hp f₀ pr rdi6) pr5

    ------------------------------------------------------------------
    -- rows 7-9: the closure register := the record
    ------------------------------------------------------------------
    wf7 : InstrWF (floc w6) (falloc w6) (load-from-slot n)
    wf7 = SV-Ptr (AtDynamic hc) , at-cf (floc w6) (falloc w6) cf5 cl6
    nh7 : halted (floc w7) ≡ false
    nh7 = exec-abstract-preserves-halted-WF (load-from-slot n) (floc w6) (falloc w6) nh6 wf7
    out7 : Oup w7 ≡ SV-Ptr (AtDynamic hc)
    out7 = out-lslot n (floc w6) (falloc w6) _ (proj₂ wf7)
    pr7 : sl w7 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr7 = trans (sl-keep (load-from-slot n) (floc w6) (falloc w6) f₀ pr nhw-load-from-slot refl) pr6
    hp7 : hpr w7 hp ≡ just env-sv
    hp7 = trans (hp-keep (load-from-slot n) (floc w6) (falloc w6) hp nhw-load-from-slot) hp6
    shp7 : hpr w7 (sucHL hp) ≡ just μ-sv
    shp7 = trans (hp-keep (load-from-slot n) (floc w6) (falloc w6) (sucHL hp) nhw-load-from-slot) shp6
    code7 : hpr w7 (sucHL hc) ≡ just (SV-Code lbl)
    code7 = trans (hp-keep (load-from-slot n) (floc w6) (falloc w6) (sucHL hc) nhw-load-from-slot) code6
    cf7 : current-frame (falloc w7) ≡ f₀
    cf7 = trans (exec-abstract-preserves-frame (load-from-slot n) (floc w6) (falloc w6)) cf5

    nh8 : halted (floc w8) ≡ false
    nh8 = exec-abstract-preserves-halted-WF mov-to-input (floc w7) (falloc w7) nh7 tt
    in8 : Inp w8 ≡ SV-Ptr (AtDynamic hc)
    in8 = trans (in-movin (floc w7) (falloc w7)) out7
    pr8 : sl w8 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr8 = trans (sl-keep mov-to-input (floc w7) (falloc w7) f₀ pr nhw-mov-to-input refl) pr7
    hp8 : hpr w8 hp ≡ just env-sv
    hp8 = trans (hp-keep mov-to-input (floc w7) (falloc w7) hp nhw-mov-to-input) hp7
    shp8 : hpr w8 (sucHL hp) ≡ just μ-sv
    shp8 = trans (hp-keep mov-to-input (floc w7) (falloc w7) (sucHL hp) nhw-mov-to-input) shp7
    code8 : hpr w8 (sucHL hc) ≡ just (SV-Code lbl)
    code8 = trans (hp-keep mov-to-input (floc w7) (falloc w7) (sucHL hc) nhw-mov-to-input) code7

    ------------------------------------------------------------------
    -- rows 10-11: Input1 := the pair
    ------------------------------------------------------------------
    wf10 : InstrWF (floc w9) (falloc w9) (load-from-slot pr)
    wf10 = SV-Ptr (AtDynamic hp) , at-cf (floc w9) (falloc w9) cf7 pr8
    nh10 : halted (floc w10) ≡ false
    nh10 = exec-abstract-preserves-halted-WF (load-from-slot pr) (floc w9) (falloc w9) nh8 wf10
    out10 : Oup w10 ≡ SV-Ptr (AtDynamic hp)
    out10 = out-lslot pr (floc w9) (falloc w9) _ (proj₂ wf10)
    hp10 : hpr w10 hp ≡ just env-sv
    hp10 = trans (hp-keep (load-from-slot pr) (floc w9) (falloc w9) hp nhw-load-from-slot) hp8
    shp10 : hpr w10 (sucHL hp) ≡ just μ-sv
    shp10 = trans (hp-keep (load-from-slot pr) (floc w9) (falloc w9) (sucHL hp) nhw-load-from-slot) shp8
    code10 : hpr w10 (sucHL hc) ≡ just (SV-Code lbl)
    code10 = trans (hp-keep (load-from-slot pr) (floc w9) (falloc w9) (sucHL hc) nhw-load-from-slot) code8

    nh11 : halted (floc w11) ≡ false
    nh11 = exec-abstract-preserves-halted-WF mov-to-input (floc w10) (falloc w10) nh10 tt
    in11 : Inp w11 ≡ SV-Ptr (AtDynamic hp)
    in11 = trans (in-movin (floc w10) (falloc w10)) out10
    hp11 : hpr w11 hp ≡ just env-sv
    hp11 = trans (hp-keep mov-to-input (floc w10) (falloc w10) hp nhw-mov-to-input) hp10
    shp11 : hpr w11 (sucHL hp) ≡ just μ-sv
    shp11 = trans (hp-keep mov-to-input (floc w10) (falloc w10) (sucHL hp) nhw-mov-to-input) shp10
    code11 : hpr w11 (sucHL hc) ≡ just (SV-Code lbl)
    code11 = trans (hp-keep mov-to-input (floc w10) (falloc w10) (sucHL hc) nhw-mov-to-input) code10
    clo11 : fclosure w11 ≡ SV-Ptr (AtDynamic hc)
    clo11 = in8

    ------------------------------------------------------------------
    -- THE RUN, silent, and what it leaves alone.
    ------------------------------------------------------------------
    runA : SRun prog 6 σ w6
    runA =
      s-at w1 (nh0 , span 0 _ refl) refl refl tt (
      s-at w2 (nh1 , span 1 _ refl) refl refl tt (
      s-at w3 (nh2 , span 2 _ refl) refl refl tt (
      s-at w4 (nh3 , span 3 _ refl) refl refl tt (
      s-at w5 (nh4 , span 4 _ refl) refl refl tt (
      s-at w6 (nh5 , span 5 _ refl) refl refl tt s-nil)))))

    runB : SRun prog 5 w6 w11
    runB =
      s-at w7 (nh6 , span 6 _ refl) refl refl tt (
      s-at w8 (nh7 , span 7 _ refl) refl refl tt (
      s-at w9 (nh8 , span 8 _ refl) refl refl tt (
      s-at w10 (nh8 , span 9 _ refl) refl refl tt (
      s-at w11 (nh10 , span 10 _ refl) refl refl tt s-nil))))

    runK : SRun prog 11 σ w11
    runK = s-++ {prog} {6} {5} {σ} {w6} {w11} runA runB

    abstract
      seg : SegA a₀ n σ w11
      seg =
        segA-∘ (seg-q mov-to-output σ nhw-mov-to-output refl tt tt)
        (segA-∘ (seg-store ks w1 cf0 (m≤m+n n 1))
        (segA-∘ (seg-q (load-from-slot pr) w2 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-q mov-to-input w3 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-q (load-from-slot ks) w4 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-sind-suc w5 hp rdi6 fresh)
        (segA-∘ (seg-q (load-from-slot n) w6 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-q mov-to-input w7 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-save w8)
        (segA-∘ (seg-q (load-from-slot pr) w9 nhw-load-from-slot refl tt tt)
                (seg-q mov-to-input w10 nhw-mov-to-input refl tt tt))))))))))

    abstract
      out : CallOut n prog σ a₀ hp hc lbl env-sv μ-sv
      out = record
        { w = w11 ; runK = runK ; seg = seg ; nh = nh11 ; pc = refl ; ret = refl ; clo = clo11
        ; inp = in11 ; hp0 = hp11 ; shp = shp11 ; code = code11 }
