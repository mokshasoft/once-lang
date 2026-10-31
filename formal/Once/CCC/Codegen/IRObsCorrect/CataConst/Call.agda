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
--       (D364: the first row is `Head`'s — `load-indirect` at a boxed μ)
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

  -- one straight step keeps the frame, and (when it allocates nothing) the heap frontier
  cfS : ∀ (i : AbstractInstr) (t : FlatState) → current-frame (falloc (St i t)) ≡ current-frame (falloc t)
  cfS i t = exec-abstract-preserves-frame i (floc t) (falloc t)

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

  -- D364: the first row is a parameter (`Head`): `mov-to-output` at every
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

    f₀ = current-frame (falloc σ)
    r₀ = next-heap-ref (falloc σ)

    ks ev pr : ℕ
    ks = n ℕ.+ 1
    ev = n ℕ.+ 2
    pr = n ℕ.+ 3

    off-≢ : ∀ {a b : ℕ} → a ≢ b → n ℕ.+ a ≢ n ℕ.+ b
    off-≢ ne e = ne (+-cancelˡ-≡ n _ _ e)

    n≢ks : n ≢ ks
    n≢ks e with +-cancelˡ-≡ n 0 1 (trans (+-identityʳ n) e)
    ... | ()
    n≢pr : n ≢ pr
    n≢pr e with +-cancelˡ-≡ n 0 3 (trans (+-identityʳ n) e)
    ... | ()
    ev≢ks : ev ≢ ks
    ev≢ks = off-≢ (λ ())
    ks≢pr : ks ≢ pr
    ks≢pr = off-≢ (λ ())
    ev≢pr : ev ≢ pr
    ev≢pr = off-≢ (λ ())

    w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : FlatState
    w1  = St (head-instr h) σ
    w2  = St (store-at-slot ks) w1
    w3  = St (instr-alloc-heap 2) w2
    w4  = St (store-at-slot pr) w3
    w5  = St mov-to-input w4
    w6  = St (load-from-slot ev) w5
    w7  = St store-indirect w6
    w8  = St (load-from-slot ks) w7
    w9  = St store-indirect-suc w8
    w10 = St (load-from-slot n) w9
    w11 = St mov-to-input w10
    w12 = do-save-closure w11
    w13 = St (load-from-slot pr) w12
    w14 = St mov-to-input w13

    Inp Oup : FlatState → StoredValue FS
    Inp t = readReg (regs (floc t)) Input1
    Oup t = readReg (regs (floc t)) Output

    sl : FlatState → ℕ → Maybe (StoredValue FS)
    sl t j = readLoc (floc t) (AtStack f₀ j)

    hpr : FlatState → HeapLocation → Maybe (StoredValue FS)
    hpr t h = readLoc (floc t) (AtDynamic h)

    ------------------------------------------------------------------
    -- rows 1-2: stash the layer
    ------------------------------------------------------------------
    nh1 : halted (floc w1) ≡ false
    nh1 = HeadOK.nh1 hd nh0
    out1 : Oup w1 ≡ μ-sv
    out1 = HeadOK.out1 hd
    cl1 : sl w1 n ≡ just (SV-Ptr (AtDynamic hc))
    cl1 = trans (sl-keep (head-instr h) (floc σ) (falloc σ) f₀ n (HeadOK.nhw hd) (HeadOK.nws hd)) cl0
    ev1 : sl w1 ev ≡ just env-sv
    ev1 = trans (sl-keep (head-instr h) (floc σ) (falloc σ) f₀ ev (HeadOK.nhw hd) (HeadOK.nws hd)) ev0
    code1 : hpr w1 (sucHL hc) ≡ just (SV-Code lbl)
    code1 = trans (hp-keep (head-instr h) (floc σ) (falloc σ) (sucHL hc) (HeadOK.nhw hd)) code0
    cf1 : current-frame (falloc w1) ≡ f₀
    cf1 = cfS (head-instr h) σ

    nh2 : halted (floc w2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (store-at-slot ks) (floc w1) (falloc w1) nh1 tt
    ks2 : sl w2 ks ≡ just μ-sv
    ks2 = trans (sl-same ks (floc w1) (falloc w1) f₀ cf1) (cong just out1)
    cl2 : sl w2 n ≡ just (SV-Ptr (AtDynamic hc))
    cl2 = trans (sl-other ks n (floc w1) (falloc w1) f₀ n≢ks) cl1
    ev2 : sl w2 ev ≡ just env-sv
    ev2 = trans (sl-other ks ev (floc w1) (falloc w1) f₀ ev≢ks) ev1
    code2 : hpr w2 (sucHL hc) ≡ just (SV-Code lbl)
    code2 = trans (hp-keep (store-at-slot ks) (floc w1) (falloc w1) (sucHL hc) nhw-store-at-slot) code1
    cf2 : current-frame (falloc w2) ≡ f₀
    cf2 = trans (cfS (store-at-slot ks) w1) cf1
    hr2 : next-heap-ref (falloc w2) ≡ r₀
    hr2 = trans (exec-abstract-preserves-heap-ref (store-at-slot ks) (floc w1) (falloc w1) tt)
                (exec-abstract-preserves-heap-ref (head-instr h) (floc σ) (falloc σ) (HeadOK.eh hd))

    ------------------------------------------------------------------
    -- rows 3-9: the FRESH pair := [env , layer]
    ------------------------------------------------------------------
    hp : HeapLocation
    hp = heap-loc (mkHeapRef (next-heap-ref (falloc w2))) 0

    -- the record is older than the pair, so their cells are apart
    hc-ne : ref-id (heap-ref (sucHL hc)) ≢ next-heap-ref (falloc w2)
    hc-ne e = <-irrefl (trans (sym (sucHL-ref hc)) (trans e hr2)) hc-lt
    ne7 : AtDynamic {FS} hp ≢ AtDynamic (sucHL hc)
    ne7 e = hc-ne (sym (cong loc-ref e))
    ne9 : AtDynamic {FS} (sucHL hp) ≢ AtDynamic (sucHL hc)
    ne9 e = hc-ne (sym (trans (sym (sucHL-ref hp)) (cong loc-ref e)))

    frhp : next-heap-ref a₀ ≤ ref-id (heap-ref hp)
    frhp = ≤-trans fresh (≤-reflexive (sym hr2))

    nh3 : halted (floc w3) ≡ false
    nh3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc w2) (falloc w2) nh2 tt
    out3 : Oup w3 ≡ SV-Ptr (AtDynamic hp)
    out3 = out-alloc 2 (floc w2) (falloc w2)
    ks3 : sl w3 ks ≡ just μ-sv
    ks3 = trans (sl-keep (instr-alloc-heap 2) (floc w2) (falloc w2) f₀ ks nhw-instr-alloc-heap refl) ks2
    cl3 : sl w3 n ≡ just (SV-Ptr (AtDynamic hc))
    cl3 = trans (sl-keep (instr-alloc-heap 2) (floc w2) (falloc w2) f₀ n nhw-instr-alloc-heap refl) cl2
    ev3 : sl w3 ev ≡ just env-sv
    ev3 = trans (sl-keep (instr-alloc-heap 2) (floc w2) (falloc w2) f₀ ev nhw-instr-alloc-heap refl) ev2
    code3 : hpr w3 (sucHL hc) ≡ just (SV-Code lbl)
    code3 = trans (hp-keep (instr-alloc-heap 2) (floc w2) (falloc w2) (sucHL hc) nhw-instr-alloc-heap) code2
    cf3 : current-frame (falloc w3) ≡ f₀
    cf3 = trans (cfS (instr-alloc-heap 2) w2) cf2
    hr3 : next-heap-ref (falloc w3) ≡ suc r₀
    hr3 = cong suc hr2

    nh4 : halted (floc w4) ≡ false
    nh4 = exec-abstract-preserves-halted-WF (store-at-slot pr) (floc w3) (falloc w3) nh3 tt
    pr4 : sl w4 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr4 = trans (sl-same pr (floc w3) (falloc w3) f₀ cf3) (cong just out3)
    ks4 : sl w4 ks ≡ just μ-sv
    ks4 = trans (sl-other pr ks (floc w3) (falloc w3) f₀ ks≢pr) ks3
    cl4 : sl w4 n ≡ just (SV-Ptr (AtDynamic hc))
    cl4 = trans (sl-other pr n (floc w3) (falloc w3) f₀ n≢pr) cl3
    ev4 : sl w4 ev ≡ just env-sv
    ev4 = trans (sl-other pr ev (floc w3) (falloc w3) f₀ ev≢pr) ev3
    code4 : hpr w4 (sucHL hc) ≡ just (SV-Code lbl)
    code4 = trans (hp-keep (store-at-slot pr) (floc w3) (falloc w3) (sucHL hc) nhw-store-at-slot) code3
    cf4 : current-frame (falloc w4) ≡ f₀
    cf4 = trans (cfS (store-at-slot pr) w3) cf3

    nh5 : halted (floc w5) ≡ false
    nh5 = exec-abstract-preserves-halted-WF mov-to-input (floc w4) (falloc w4) nh4 tt
    in5 : Inp w5 ≡ SV-Ptr (AtDynamic hp)
    in5 = trans (in-movin (floc w4) (falloc w4)) (trans (reg-store pr (floc w3) (falloc w3) Output) out3)
    pr5 : sl w5 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr5 = trans (sl-keep mov-to-input (floc w4) (falloc w4) f₀ pr nhw-mov-to-input refl) pr4
    ks5 : sl w5 ks ≡ just μ-sv
    ks5 = trans (sl-keep mov-to-input (floc w4) (falloc w4) f₀ ks nhw-mov-to-input refl) ks4
    cl5 : sl w5 n ≡ just (SV-Ptr (AtDynamic hc))
    cl5 = trans (sl-keep mov-to-input (floc w4) (falloc w4) f₀ n nhw-mov-to-input refl) cl4
    ev5 : sl w5 ev ≡ just env-sv
    ev5 = trans (sl-keep mov-to-input (floc w4) (falloc w4) f₀ ev nhw-mov-to-input refl) ev4
    code5 : hpr w5 (sucHL hc) ≡ just (SV-Code lbl)
    code5 = trans (hp-keep mov-to-input (floc w4) (falloc w4) (sucHL hc) nhw-mov-to-input) code4
    cf5 : current-frame (falloc w5) ≡ f₀
    cf5 = trans (cfS mov-to-input w4) cf4

    wf6 : InstrWF (floc w5) (falloc w5) (load-from-slot ev)
    wf6 = env-sv , at-cf (floc w5) (falloc w5) cf5 ev5
    nh6 : halted (floc w6) ≡ false
    nh6 = exec-abstract-preserves-halted-WF (load-from-slot ev) (floc w5) (falloc w5) nh5 wf6
    out6 : Oup w6 ≡ env-sv
    out6 = out-lslot ev (floc w5) (falloc w5) env-sv (proj₂ wf6)
    in6 : Inp w6 ≡ SV-Ptr (AtDynamic hp)
    in6 = trans (in-lslot ev (floc w5) (falloc w5) env-sv (proj₂ wf6)) in5
    pr6 : sl w6 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr6 = trans (sl-keep (load-from-slot ev) (floc w5) (falloc w5) f₀ pr nhw-load-from-slot refl) pr5
    ks6 : sl w6 ks ≡ just μ-sv
    ks6 = trans (sl-keep (load-from-slot ev) (floc w5) (falloc w5) f₀ ks nhw-load-from-slot refl) ks5
    cl6 : sl w6 n ≡ just (SV-Ptr (AtDynamic hc))
    cl6 = trans (sl-keep (load-from-slot ev) (floc w5) (falloc w5) f₀ n nhw-load-from-slot refl) cl5
    ev6 : sl w6 ev ≡ just env-sv
    ev6 = trans (sl-keep (load-from-slot ev) (floc w5) (falloc w5) f₀ ev nhw-load-from-slot refl) ev5
    code6 : hpr w6 (sucHL hc) ≡ just (SV-Code lbl)
    code6 = trans (hp-keep (load-from-slot ev) (floc w5) (falloc w5) (sucHL hc) nhw-load-from-slot) code5
    cf6 : current-frame (falloc w6) ≡ f₀
    cf6 = trans (cfS (load-from-slot ev) w5) cf5

    rdi7 : sv-as-loc (Inp w6) ≡ just (AtDynamic hp)
    rdi7 = cong sv-as-loc in6
    nh7 : halted (floc w7) ≡ false
    nh7 = exec-abstract-preserves-halted-WF store-indirect (floc w6) (falloc w6) nh6 (AtDynamic hp , rdi7)
    hp7 : hpr w7 hp ≡ just env-sv
    hp7 = trans (store-ind-result (floc w6) (falloc w6) hp rdi7) (cong just out6)
    in7 : Inp w7 ≡ SV-Ptr (AtDynamic hp)
    in7 = trans (in-sind (floc w6) (falloc w6) (AtDynamic hp) rdi7) in6
    pr7 : sl w7 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr7 = trans (sl-sind (floc w6) (falloc w6) hp f₀ pr rdi7) pr6
    ks7 : sl w7 ks ≡ just μ-sv
    ks7 = trans (sl-sind (floc w6) (falloc w6) hp f₀ ks rdi7) ks6
    cl7 : sl w7 n ≡ just (SV-Ptr (AtDynamic hc))
    cl7 = trans (sl-sind (floc w6) (falloc w6) hp f₀ n rdi7) cl6
    ev7 : sl w7 ev ≡ just env-sv
    ev7 = trans (sl-sind (floc w6) (falloc w6) hp f₀ ev rdi7) ev6
    code7 : hpr w7 (sucHL hc) ≡ just (SV-Code lbl)
    code7 = trans (hp-sind-other (floc w6) (falloc w6) hp (sucHL hc) rdi7 ne7) code6
    cf7 : current-frame (falloc w7) ≡ f₀
    cf7 = trans (cfS store-indirect w6) cf6

    wf8 : InstrWF (floc w7) (falloc w7) (load-from-slot ks)
    wf8 = μ-sv , at-cf (floc w7) (falloc w7) cf7 ks7
    nh8 : halted (floc w8) ≡ false
    nh8 = exec-abstract-preserves-halted-WF (load-from-slot ks) (floc w7) (falloc w7) nh7 wf8
    out8 : Oup w8 ≡ μ-sv
    out8 = out-lslot ks (floc w7) (falloc w7) μ-sv (proj₂ wf8)
    in8 : Inp w8 ≡ SV-Ptr (AtDynamic hp)
    in8 = trans (in-lslot ks (floc w7) (falloc w7) μ-sv (proj₂ wf8)) in7
    pr8 : sl w8 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr8 = trans (sl-keep (load-from-slot ks) (floc w7) (falloc w7) f₀ pr nhw-load-from-slot refl) pr7
    cl8 : sl w8 n ≡ just (SV-Ptr (AtDynamic hc))
    cl8 = trans (sl-keep (load-from-slot ks) (floc w7) (falloc w7) f₀ n nhw-load-from-slot refl) cl7
    ev8 : sl w8 ev ≡ just env-sv
    ev8 = trans (sl-keep (load-from-slot ks) (floc w7) (falloc w7) f₀ ev nhw-load-from-slot refl) ev7
    hp8 : hpr w8 hp ≡ just env-sv
    hp8 = trans (hp-keep (load-from-slot ks) (floc w7) (falloc w7) hp nhw-load-from-slot) hp7
    code8 : hpr w8 (sucHL hc) ≡ just (SV-Code lbl)
    code8 = trans (hp-keep (load-from-slot ks) (floc w7) (falloc w7) (sucHL hc) nhw-load-from-slot) code7
    cf8 : current-frame (falloc w8) ≡ f₀
    cf8 = trans (cfS (load-from-slot ks) w7) cf7

    rdi9 : sv-as-loc (Inp w8) ≡ just (AtDynamic hp)
    rdi9 = cong sv-as-loc in8
    nh9 : halted (floc w9) ≡ false
    nh9 = exec-abstract-preserves-halted-WF store-indirect-suc (floc w8) (falloc w8) nh8 (AtDynamic hp , rdi9)
    shp9 : hpr w9 (sucHL hp) ≡ just μ-sv
    shp9 = trans (store-ind-suc-result (floc w8) (falloc w8) hp rdi9) (cong just out8)
    hp9 : hpr w9 hp ≡ just env-sv
    hp9 = trans (store-ind-suc-preserves-heap (floc w8) (falloc w8) hp hp rdi9 (sucHL-≢ hp)) hp8
    code9 : hpr w9 (sucHL hc) ≡ just (SV-Code lbl)
    code9 = trans (store-ind-suc-preserves-heap (floc w8) (falloc w8) hp (sucHL hc) rdi9 ne9) code8
    pr9 : sl w9 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr9 = trans (sl-sind-suc (floc w8) (falloc w8) hp f₀ pr rdi9) pr8
    cl9 : sl w9 n ≡ just (SV-Ptr (AtDynamic hc))
    cl9 = trans (sl-sind-suc (floc w8) (falloc w8) hp f₀ n rdi9) cl8
    ev9 : sl w9 ev ≡ just env-sv
    ev9 = trans (sl-sind-suc (floc w8) (falloc w8) hp f₀ ev rdi9) ev8
    cf9 : current-frame (falloc w9) ≡ f₀
    cf9 = trans (cfS store-indirect-suc w8) cf8

    ------------------------------------------------------------------
    -- rows 10-12: the closure register := the record
    ------------------------------------------------------------------
    wf10 : InstrWF (floc w9) (falloc w9) (load-from-slot n)
    wf10 = SV-Ptr (AtDynamic hc) , at-cf (floc w9) (falloc w9) cf9 cl9
    nh10 : halted (floc w10) ≡ false
    nh10 = exec-abstract-preserves-halted-WF (load-from-slot n) (floc w9) (falloc w9) nh9 wf10
    out10 : Oup w10 ≡ SV-Ptr (AtDynamic hc)
    out10 = out-lslot n (floc w9) (falloc w9) _ (proj₂ wf10)
    pr10 : sl w10 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr10 = trans (sl-keep (load-from-slot n) (floc w9) (falloc w9) f₀ pr nhw-load-from-slot refl) pr9
    cl10 : sl w10 n ≡ just (SV-Ptr (AtDynamic hc))
    cl10 = trans (sl-keep (load-from-slot n) (floc w9) (falloc w9) f₀ n nhw-load-from-slot refl) cl9
    ev10 : sl w10 ev ≡ just env-sv
    ev10 = trans (sl-keep (load-from-slot n) (floc w9) (falloc w9) f₀ ev nhw-load-from-slot refl) ev9
    hp10 : hpr w10 hp ≡ just env-sv
    hp10 = trans (hp-keep (load-from-slot n) (floc w9) (falloc w9) hp nhw-load-from-slot) hp9
    shp10 : hpr w10 (sucHL hp) ≡ just μ-sv
    shp10 = trans (hp-keep (load-from-slot n) (floc w9) (falloc w9) (sucHL hp) nhw-load-from-slot) shp9
    code10 : hpr w10 (sucHL hc) ≡ just (SV-Code lbl)
    code10 = trans (hp-keep (load-from-slot n) (floc w9) (falloc w9) (sucHL hc) nhw-load-from-slot) code9
    cf10 : current-frame (falloc w10) ≡ f₀
    cf10 = trans (cfS (load-from-slot n) w9) cf9

    nh11 : halted (floc w11) ≡ false
    nh11 = exec-abstract-preserves-halted-WF mov-to-input (floc w10) (falloc w10) nh10 tt
    in11 : Inp w11 ≡ SV-Ptr (AtDynamic hc)
    in11 = trans (in-movin (floc w10) (falloc w10)) out10
    pr11 : sl w11 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr11 = trans (sl-keep mov-to-input (floc w10) (falloc w10) f₀ pr nhw-mov-to-input refl) pr10
    cl11 : sl w11 n ≡ just (SV-Ptr (AtDynamic hc))
    cl11 = trans (sl-keep mov-to-input (floc w10) (falloc w10) f₀ n nhw-mov-to-input refl) cl10
    ev11 : sl w11 ev ≡ just env-sv
    ev11 = trans (sl-keep mov-to-input (floc w10) (falloc w10) f₀ ev nhw-mov-to-input refl) ev10
    hp11 : hpr w11 hp ≡ just env-sv
    hp11 = trans (hp-keep mov-to-input (floc w10) (falloc w10) hp nhw-mov-to-input) hp10
    shp11 : hpr w11 (sucHL hp) ≡ just μ-sv
    shp11 = trans (hp-keep mov-to-input (floc w10) (falloc w10) (sucHL hp) nhw-mov-to-input) shp10
    code11 : hpr w11 (sucHL hc) ≡ just (SV-Code lbl)
    code11 = trans (hp-keep mov-to-input (floc w10) (falloc w10) (sucHL hc) nhw-mov-to-input) code10
    cf11 : current-frame (falloc w11) ≡ f₀
    cf11 = trans (cfS mov-to-input w10) cf10

    -- row 12 (`do-save-closure`) changes neither `floc` nor `falloc`

    ------------------------------------------------------------------
    -- rows 13-14: Input1 := the pair
    ------------------------------------------------------------------
    wf13 : InstrWF (floc w12) (falloc w12) (load-from-slot pr)
    wf13 = SV-Ptr (AtDynamic hp) , at-cf (floc w12) (falloc w12) cf11 pr11
    nh13 : halted (floc w13) ≡ false
    nh13 = exec-abstract-preserves-halted-WF (load-from-slot pr) (floc w12) (falloc w12) nh11 wf13
    out13 : Oup w13 ≡ SV-Ptr (AtDynamic hp)
    out13 = out-lslot pr (floc w12) (falloc w12) _ (proj₂ wf13)
    pr13 : sl w13 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr13 = trans (sl-keep (load-from-slot pr) (floc w12) (falloc w12) f₀ pr nhw-load-from-slot refl) pr11
    cl13 : sl w13 n ≡ just (SV-Ptr (AtDynamic hc))
    cl13 = trans (sl-keep (load-from-slot pr) (floc w12) (falloc w12) f₀ n nhw-load-from-slot refl) cl11
    ev13 : sl w13 ev ≡ just env-sv
    ev13 = trans (sl-keep (load-from-slot pr) (floc w12) (falloc w12) f₀ ev nhw-load-from-slot refl) ev11
    hp13 : hpr w13 hp ≡ just env-sv
    hp13 = trans (hp-keep (load-from-slot pr) (floc w12) (falloc w12) hp nhw-load-from-slot) hp11
    shp13 : hpr w13 (sucHL hp) ≡ just μ-sv
    shp13 = trans (hp-keep (load-from-slot pr) (floc w12) (falloc w12) (sucHL hp) nhw-load-from-slot) shp11
    code13 : hpr w13 (sucHL hc) ≡ just (SV-Code lbl)
    code13 = trans (hp-keep (load-from-slot pr) (floc w12) (falloc w12) (sucHL hc) nhw-load-from-slot) code11
    cf13 : current-frame (falloc w13) ≡ f₀
    cf13 = trans (cfS (load-from-slot pr) w12) cf11

    nh14 : halted (floc w14) ≡ false
    nh14 = exec-abstract-preserves-halted-WF mov-to-input (floc w13) (falloc w13) nh13 tt
    in14 : Inp w14 ≡ SV-Ptr (AtDynamic hp)
    in14 = trans (in-movin (floc w13) (falloc w13)) out13
    pr14 : sl w14 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr14 = trans (sl-keep mov-to-input (floc w13) (falloc w13) f₀ pr nhw-mov-to-input refl) pr13
    cl14 : sl w14 n ≡ just (SV-Ptr (AtDynamic hc))
    cl14 = trans (sl-keep mov-to-input (floc w13) (falloc w13) f₀ n nhw-mov-to-input refl) cl13
    ev14 : sl w14 ev ≡ just env-sv
    ev14 = trans (sl-keep mov-to-input (floc w13) (falloc w13) f₀ ev nhw-mov-to-input refl) ev13
    hp14 : hpr w14 hp ≡ just env-sv
    hp14 = trans (hp-keep mov-to-input (floc w13) (falloc w13) hp nhw-mov-to-input) hp13
    shp14 : hpr w14 (sucHL hp) ≡ just μ-sv
    shp14 = trans (hp-keep mov-to-input (floc w13) (falloc w13) (sucHL hp) nhw-mov-to-input) shp13
    code14 : hpr w14 (sucHL hc) ≡ just (SV-Code lbl)
    code14 = trans (hp-keep mov-to-input (floc w13) (falloc w13) (sucHL hc) nhw-mov-to-input) code13
    cf14 : current-frame (falloc w14) ≡ f₀
    cf14 = trans (cfS mov-to-input w13) cf13
    clo14 : fclosure w14 ≡ SV-Ptr (AtDynamic hc)
    clo14 = in11

    -- the heap frontier: one block, at row 3
    hr14 : next-heap-ref (falloc w14) ≡ suc r₀
    hr14 =
      trans (exec-abstract-preserves-heap-ref mov-to-input (floc w13) (falloc w13) tt)
      (trans (exec-abstract-preserves-heap-ref (load-from-slot pr) (floc w12) (falloc w12) tt)
      (trans (exec-abstract-preserves-heap-ref mov-to-input (floc w10) (falloc w10) tt)
      (trans (exec-abstract-preserves-heap-ref (load-from-slot n) (floc w9) (falloc w9) tt)
      (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc w8) (falloc w8) tt)
      (trans (exec-abstract-preserves-heap-ref (load-from-slot ks) (floc w7) (falloc w7) tt)
      (trans (exec-abstract-preserves-heap-ref store-indirect (floc w6) (falloc w6) tt)
      (trans (exec-abstract-preserves-heap-ref (load-from-slot ev) (floc w5) (falloc w5) tt)
      (trans (exec-abstract-preserves-heap-ref mov-to-input (floc w4) (falloc w4) tt)
      (trans (exec-abstract-preserves-heap-ref (store-at-slot pr) (floc w3) (falloc w3) tt)
             hr3)))))))))

    ------------------------------------------------------------------
    -- THE RUN, silent, and what it leaves alone.
    ------------------------------------------------------------------
    runA : SRun prog 6 σ w6
    runA =
      s-at w1 (nh0 , span 0 _ refl) (HeadOK.step hd) (HeadOK.ev hd) (HeadOK.lf hd) (
      s-at w2 (nh1 , span 1 _ refl) refl refl tt (
      s-at w3 (nh2 , span 2 _ refl) refl refl tt (
      s-at w4 (nh3 , span 3 _ refl) refl refl tt (
      s-at w5 (nh4 , span 4 _ refl) refl refl tt (
      s-at w6 (nh5 , span 5 _ refl) refl refl tt s-nil)))))

    runB : SRun prog 8 w6 w14
    runB =
      s-at w7 (nh6 , span 6 _ refl) refl refl tt (
      s-at w8 (nh7 , span 7 _ refl) refl refl tt (
      s-at w9 (nh8 , span 8 _ refl) refl refl tt (
      s-at w10 (nh9 , span 9 _ refl) refl refl tt (
      s-at w11 (nh10 , span 10 _ refl) refl refl tt (
      s-at w12 (nh11 , span 11 _ refl) refl refl tt (
      s-at w13 (nh11 , span 12 _ refl) refl refl tt (
      s-at w14 (nh13 , span 13 _ refl) refl refl tt s-nil)))))))

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
