-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Setup   (plan 0.125 S3, cata M1)
--
-- THE CATA'S EIGHTEEN SETUP ROWS (`cata-call-setup cl k ev pr body`), run
-- from any state whose `Input1` points at the input pair `(env , μ)`:
--
--     load-indirect · store ev · load-indirect-suc · store k     split the pair
--     alloc · store pr · mov-to-input · load ev · store-indirect  pr := [env , _]
--     alloc · store cl · mov-to-input · tag 0 · store-indirect ·
--       code-addr body · store-indirect-suc                       cl := [0 , body]
--     load k · mov-to-input                                       Input1 := μ
--
-- What the call rows need afterwards: the closure record's code cell, the
-- argument pair's environment cell, the two stashed pointers (`cl`, `pr`),
-- and `Input1` holding the μ cell again. Everything the caller has live is
-- untouched (`seg`): the four slots are at or above the frontier and the
-- two heap writes land in blocks this run allocated.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Setup (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRToTrace o using (cata-call-setup)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output; Input1; SV-Code; SV-Ptr; sv-as-loc; store-at-slot; load-from-slot; load-indirect; load-indirect-suc; store-indirect; store-indirect-suc; mov-to-input; instr-alloc-heap; instr-load-code-addr; instr-load-tag-lit)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
import Data.Nat as ℕ
open import Data.Nat.Properties using (+-cancelˡ-≡)

module CataSetupC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  -- distinct offsets above one frontier are distinct slots
  off-≢ : ∀ (n : ℕ) {a b : ℕ} → a ≢ b → n ℕ.+ a ≢ n ℕ.+ b
  off-≢ n ne e = ne (+-cancelˡ-≡ n _ _ e)

  off0-≢ : ∀ (n : ℕ) {b : ℕ} → 0 ≢ b → n ≢ n ℕ.+ b
  off0-≢ n ne e = ne (+-cancelˡ-≡ n _ _ (trans (+-identityʳ n) e))

  -- WHAT THE SETUP HANDS ON, as an opaque bundle: a consumer sees the last
  -- state only through these facts, so no conversion outside this module can
  -- unfold the eighteen steps behind it.
  record SetupOut (n l1 : ℕ) (prog : AbstractTrace) (σ : FlatState) (env-sv μ-sv : StoredValue FS) : Set where
    field
      u      : FlatState
      runS   : SRun prog 18 σ u
      seg    : SegA (falloc σ) n σ u
      nh     : halted (floc u) ≡ false
      pc     : fpc u ≡ 18 + fpc σ
      ret    : fret u ≡ fret σ
      clo    : fclosure u ≡ fclosure σ
      lnk    : flink u ≡ flink σ
      hc     : HeapLocation
      ref-hc : ref-id (heap-ref hc) ≡ suc (next-heap-ref (falloc σ))
      inμ    : readReg (regs (floc u)) Input1 ≡ μ-sv
      cl     : readLoc (floc u) (AtStack (current-frame (falloc u)) n) ≡ just (SV-Ptr (AtDynamic hc))
      pr     : readLoc (floc u) (AtStack (current-frame (falloc u)) (n ℕ.+ 3))
               ≡ just (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (next-heap-ref (falloc σ))) 0)))
      hp0    : readLoc (floc u) (AtDynamic (heap-loc (mkHeapRef (next-heap-ref (falloc σ))) 0)) ≡ just env-sv
      code   : readLoc (floc u) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o l1))
      cf     : current-frame (falloc u) ≡ current-frame (falloc σ)
      hr     : next-heap-ref (falloc u) ≡ suc (suc (next-heap-ref (falloc σ)))

  module Setup (n l1 : ℕ) (prog : AbstractTrace) (σ : FlatState)
               (span : SpanAt prog (fpc σ) (cata-call-setup n (n ℕ.+ 1) (n ℕ.+ 2) (n ℕ.+ 3) l1))
               (nh0 : halted (floc σ) ≡ false)
               (phl : HeapLocation) (env-sv μ-sv : StoredValue FS)
               (rdi : readReg (regs (floc σ)) Input1 ≡ SV-Ptr (AtDynamic phl))
               (c0 : readLoc (floc σ) (AtDynamic phl) ≡ just env-sv)
               (c1 : readLoc (floc σ) (AtDynamic (sucHL phl)) ≡ just μ-sv)
               where

    s₀ : LocState FS
    s₀ = floc σ
    a₀ : AllocState {FS}
    a₀ = falloc σ
    f₀ = current-frame a₀
    r₀ : ℕ
    r₀ = next-heap-ref a₀

    ks ev pr : ℕ
    ks = n ℕ.+ 1
    ev = n ℕ.+ 2
    pr = n ℕ.+ 3

    pl : ValueLocation FS
    pl = AtDynamic phl

    ev≢ks : ev ≢ ks
    ev≢ks = off-≢ n (λ ())
    ev≢pr : ev ≢ pr
    ev≢pr = off-≢ n (λ ())
    ks≢pr : ks ≢ pr
    ks≢pr = off-≢ n (λ ())
    ks≢n : ks ≢ n
    ks≢n e = off0-≢ n (λ ()) (sym e)
    pr≢n : pr ≢ n
    pr≢n e = off0-≢ n (λ ()) (sym e)

    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 : FlatState
    u1  = St load-indirect σ
    u2  = St (store-at-slot ev) u1
    u3  = St load-indirect-suc u2
    u4  = St (store-at-slot ks) u3
    u5  = St (instr-alloc-heap 2) u4
    u6  = St (store-at-slot pr) u5
    u7  = St mov-to-input u6
    u8  = St (load-from-slot ev) u7
    u9  = St store-indirect u8
    u10 = St (instr-alloc-heap 2) u9
    u11 = St (store-at-slot n) u10
    u12 = St mov-to-input u11
    u13 = St (instr-load-tag-lit 0) u12
    u14 = St store-indirect u13
    u15 = St (instr-load-code-addr (ℓ o l1)) u14
    u16 = St store-indirect-suc u15
    u17 = St (load-from-slot ks) u16
    u18 = St mov-to-input u17

    -- the two blocks, as the allocator hands them out
    hp hc : HeapLocation
    hp = heap-loc (mkHeapRef r₀) 0
    hc = heap-loc (mkHeapRef (next-heap-ref (falloc u9))) 0

    Inp Oup : FlatState → StoredValue FS
    Inp t = readReg (regs (floc t)) Input1
    Oup t = readReg (regs (floc t)) Output

    sl : FlatState → ℕ → Maybe (StoredValue FS)
    sl t j = readLoc (floc t) (AtStack f₀ j)

    hpr : FlatState → HeapLocation → Maybe (StoredValue FS)
    hpr t h = readLoc (floc t) (AtDynamic h)

    ------------------------------------------------------------------
    -- rows 1-4: split the pair, stash both halves
    ------------------------------------------------------------------
    wf1 : InstrWF s₀ a₀ load-indirect
    wf1 = pl , cong sv-as-loc rdi , env-sv , c0
    nh1 : halted (floc u1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF load-indirect s₀ a₀ nh0 wf1
    out1 : Oup u1 ≡ env-sv
    out1 = out-lind s₀ a₀ pl env-sv rdi c0
    in1 : Inp u1 ≡ SV-Ptr pl
    in1 = trans (load-ind-preserves-input s₀ a₀ pl env-sv (cong sv-as-loc rdi) c0) rdi
    c1-1 : hpr u1 (sucHL phl) ≡ just μ-sv
    c1-1 = trans (hp-keep load-indirect s₀ a₀ (sucHL phl) nhw-load-indirect) c1

    nh2 : halted (floc u2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (store-at-slot ev) (floc u1) (falloc u1) nh1 tt
    in2 : Inp u2 ≡ SV-Ptr pl
    in2 = trans (reg-store ev (floc u1) (falloc u1) Input1) in1
    c1-2 : hpr u2 (sucHL phl) ≡ just μ-sv
    c1-2 = trans (hp-keep (store-at-slot ev) (floc u1) (falloc u1) (sucHL phl) nhw-store-at-slot) c1-1
    ev2 : sl u2 ev ≡ just env-sv
    ev2 = trans (sl-same ev (floc u1) (falloc u1) f₀ refl) (cong just out1)

    wf3 : InstrWF (floc u2) (falloc u2) load-indirect-suc
    wf3 = pl , cong sv-as-loc in2 , μ-sv , c1-2
    nh3 : halted (floc u3) ≡ false
    nh3 = exec-abstract-preserves-halted-WF load-indirect-suc (floc u2) (falloc u2) nh2 wf3
    out3 : Oup u3 ≡ μ-sv
    out3 = out-lind-suc (floc u2) (falloc u2) pl μ-sv in2 c1-2
    ev3 : sl u3 ev ≡ just env-sv
    ev3 = trans (sl-keep load-indirect-suc (floc u2) (falloc u2) f₀ ev nhw-load-indirect-suc refl) ev2

    nh4 : halted (floc u4) ≡ false
    nh4 = exec-abstract-preserves-halted-WF (store-at-slot ks) (floc u3) (falloc u3) nh3 tt
    ks4 : sl u4 ks ≡ just μ-sv
    ks4 = trans (sl-same ks (floc u3) (falloc u3) f₀ refl) (cong just out3)
    ev4 : sl u4 ev ≡ just env-sv
    ev4 = trans (sl-other ks ev (floc u3) (falloc u3) f₀ ev≢ks) ev3

    ------------------------------------------------------------------
    -- rows 5-9: the argument pair, its first cell the environment
    ------------------------------------------------------------------
    nh5 : halted (floc u5) ≡ false
    nh5 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc u4) (falloc u4) nh4 tt
    out5 : Oup u5 ≡ SV-Ptr (AtDynamic hp)
    out5 = out-alloc 2 (floc u4) (falloc u4)
    ks5 : sl u5 ks ≡ just μ-sv
    ks5 = trans (sl-keep (instr-alloc-heap 2) (floc u4) (falloc u4) f₀ ks nhw-instr-alloc-heap refl) ks4
    ev5 : sl u5 ev ≡ just env-sv
    ev5 = trans (sl-keep (instr-alloc-heap 2) (floc u4) (falloc u4) f₀ ev nhw-instr-alloc-heap refl) ev4

    nh6 : halted (floc u6) ≡ false
    nh6 = exec-abstract-preserves-halted-WF (store-at-slot pr) (floc u5) (falloc u5) nh5 tt
    pr6 : sl u6 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr6 = trans (sl-same pr (floc u5) (falloc u5) f₀ refl) (cong just out5)
    ks6 : sl u6 ks ≡ just μ-sv
    ks6 = trans (sl-other pr ks (floc u5) (falloc u5) f₀ ks≢pr) ks5
    ev6 : sl u6 ev ≡ just env-sv
    ev6 = trans (sl-other pr ev (floc u5) (falloc u5) f₀ ev≢pr) ev5

    nh7 : halted (floc u7) ≡ false
    nh7 = exec-abstract-preserves-halted-WF mov-to-input (floc u6) (falloc u6) nh6 tt
    in7 : Inp u7 ≡ SV-Ptr (AtDynamic hp)
    in7 = trans (in-movin (floc u6) (falloc u6)) (trans (reg-store pr (floc u5) (falloc u5) Output) out5)
    pr7 : sl u7 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr7 = trans (sl-keep mov-to-input (floc u6) (falloc u6) f₀ pr nhw-mov-to-input refl) pr6
    ks7 : sl u7 ks ≡ just μ-sv
    ks7 = trans (sl-keep mov-to-input (floc u6) (falloc u6) f₀ ks nhw-mov-to-input refl) ks6
    ev7 : sl u7 ev ≡ just env-sv
    ev7 = trans (sl-keep mov-to-input (floc u6) (falloc u6) f₀ ev nhw-mov-to-input refl) ev6

    wf8 : InstrWF (floc u7) (falloc u7) (load-from-slot ev)
    wf8 = env-sv , ev7
    nh8 : halted (floc u8) ≡ false
    nh8 = exec-abstract-preserves-halted-WF (load-from-slot ev) (floc u7) (falloc u7) nh7 wf8
    out8 : Oup u8 ≡ env-sv
    out8 = out-lslot ev (floc u7) (falloc u7) env-sv ev7
    in8 : Inp u8 ≡ SV-Ptr (AtDynamic hp)
    in8 = trans (in-lslot ev (floc u7) (falloc u7) env-sv ev7) in7
    pr8 : sl u8 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr8 = trans (sl-keep (load-from-slot ev) (floc u7) (falloc u7) f₀ pr nhw-load-from-slot refl) pr7
    ks8 : sl u8 ks ≡ just μ-sv
    ks8 = trans (sl-keep (load-from-slot ev) (floc u7) (falloc u7) f₀ ks nhw-load-from-slot refl) ks7
    cf8 : current-frame (falloc u8) ≡ f₀
    cf8 = exec-abstract-preserves-frame (load-from-slot ev) (floc u7) (falloc u7)
    hr8 : next-heap-ref (falloc u8) ≡ suc r₀
    hr8 = exec-abstract-preserves-heap-ref (load-from-slot ev) (floc u7) (falloc u7) tt

    rdi9 : sv-as-loc (Inp u8) ≡ just (AtDynamic hp)
    rdi9 = cong sv-as-loc in8
    nh9 : halted (floc u9) ≡ false
    nh9 = exec-abstract-preserves-halted-WF store-indirect (floc u8) (falloc u8) nh8 (AtDynamic hp , rdi9)
    hp9 : hpr u9 hp ≡ just env-sv
    hp9 = trans (store-ind-result (floc u8) (falloc u8) hp rdi9) (cong just out8)
    pr9 : sl u9 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr9 = trans (sl-sind (floc u8) (falloc u8) hp f₀ pr rdi9) pr8
    ks9 : sl u9 ks ≡ just μ-sv
    ks9 = trans (sl-sind (floc u8) (falloc u8) hp f₀ ks rdi9) ks8

    ------------------------------------------------------------------
    -- rows 10-16: the closure record, [tag 0 , code of the body]
    ------------------------------------------------------------------
    ref-hc : ref-id (heap-ref hc) ≡ suc r₀
    ref-hc = hr8

    hc≢hp : AtDynamic {FS} hc ≢ AtDynamic hp
    hc≢hp e = <-irrefl (sym (trans (sym ref-hc) (cong loc-ref e))) (n<1+n r₀)

    shc≢hp : AtDynamic {FS} (sucHL hc) ≢ AtDynamic hp
    shc≢hp e = <-irrefl (sym (trans (sym ref-hc) (cong loc-ref e))) (n<1+n r₀)

    nh10 : halted (floc u10) ≡ false
    nh10 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc u9) (falloc u9) nh9 tt
    out10 : Oup u10 ≡ SV-Ptr (AtDynamic hc)
    out10 = out-alloc 2 (floc u9) (falloc u9)
    hp10 : hpr u10 hp ≡ just env-sv
    hp10 = trans (hp-keep (instr-alloc-heap 2) (floc u9) (falloc u9) hp nhw-instr-alloc-heap) hp9
    pr10 : sl u10 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr10 = trans (sl-keep (instr-alloc-heap 2) (floc u9) (falloc u9) f₀ pr nhw-instr-alloc-heap refl) pr9
    ks10 : sl u10 ks ≡ just μ-sv
    ks10 = trans (sl-keep (instr-alloc-heap 2) (floc u9) (falloc u9) f₀ ks nhw-instr-alloc-heap refl) ks9
    cf10 : current-frame (falloc u10) ≡ f₀
    cf10 = cf8

    nh11 : halted (floc u11) ≡ false
    nh11 = exec-abstract-preserves-halted-WF (store-at-slot n) (floc u10) (falloc u10) nh10 tt
    cl11 : sl u11 n ≡ just (SV-Ptr (AtDynamic hc))
    cl11 = trans (sl-same n (floc u10) (falloc u10) f₀ cf10) (cong just out10)
    pr11 : sl u11 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr11 = trans (sl-other n pr (floc u10) (falloc u10) f₀ pr≢n) pr10
    ks11 : sl u11 ks ≡ just μ-sv
    ks11 = trans (sl-other n ks (floc u10) (falloc u10) f₀ ks≢n) ks10
    hp11 : hpr u11 hp ≡ just env-sv
    hp11 = trans (hp-keep (store-at-slot n) (floc u10) (falloc u10) hp nhw-store-at-slot) hp10

    nh12 : halted (floc u12) ≡ false
    nh12 = exec-abstract-preserves-halted-WF mov-to-input (floc u11) (falloc u11) nh11 tt
    in12 : Inp u12 ≡ SV-Ptr (AtDynamic hc)
    in12 = trans (in-movin (floc u11) (falloc u11)) (trans (reg-store n (floc u10) (falloc u10) Output) out10)
    cl12 : sl u12 n ≡ just (SV-Ptr (AtDynamic hc))
    cl12 = trans (sl-keep mov-to-input (floc u11) (falloc u11) f₀ n nhw-mov-to-input refl) cl11
    pr12 : sl u12 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr12 = trans (sl-keep mov-to-input (floc u11) (falloc u11) f₀ pr nhw-mov-to-input refl) pr11
    ks12 : sl u12 ks ≡ just μ-sv
    ks12 = trans (sl-keep mov-to-input (floc u11) (falloc u11) f₀ ks nhw-mov-to-input refl) ks11
    hp12 : hpr u12 hp ≡ just env-sv
    hp12 = trans (hp-keep mov-to-input (floc u11) (falloc u11) hp nhw-mov-to-input) hp11

    nh13 : halted (floc u13) ≡ false
    nh13 = exec-abstract-preserves-halted-WF (instr-load-tag-lit 0) (floc u12) (falloc u12) nh12 tt
    in13 : Inp u13 ≡ SV-Ptr (AtDynamic hc)
    in13 = trans (in-tag 0 (floc u12) (falloc u12)) in12
    cl13 : sl u13 n ≡ just (SV-Ptr (AtDynamic hc))
    cl13 = trans (sl-keep (instr-load-tag-lit 0) (floc u12) (falloc u12) f₀ n nhw-instr-load-tag-lit refl) cl12
    pr13 : sl u13 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr13 = trans (sl-keep (instr-load-tag-lit 0) (floc u12) (falloc u12) f₀ pr nhw-instr-load-tag-lit refl) pr12
    ks13 : sl u13 ks ≡ just μ-sv
    ks13 = trans (sl-keep (instr-load-tag-lit 0) (floc u12) (falloc u12) f₀ ks nhw-instr-load-tag-lit refl) ks12
    hp13 : hpr u13 hp ≡ just env-sv
    hp13 = trans (hp-keep (instr-load-tag-lit 0) (floc u12) (falloc u12) hp nhw-instr-load-tag-lit) hp12

    rdi14 : sv-as-loc (Inp u13) ≡ just (AtDynamic hc)
    rdi14 = cong sv-as-loc in13
    nh14 : halted (floc u14) ≡ false
    nh14 = exec-abstract-preserves-halted-WF store-indirect (floc u13) (falloc u13) nh13 (AtDynamic hc , rdi14)
    in14 : Inp u14 ≡ SV-Ptr (AtDynamic hc)
    in14 = trans (in-sind (floc u13) (falloc u13) (AtDynamic hc) rdi14) in13
    cl14 : sl u14 n ≡ just (SV-Ptr (AtDynamic hc))
    cl14 = trans (sl-sind (floc u13) (falloc u13) hc f₀ n rdi14) cl13
    pr14 : sl u14 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr14 = trans (sl-sind (floc u13) (falloc u13) hc f₀ pr rdi14) pr13
    ks14 : sl u14 ks ≡ just μ-sv
    ks14 = trans (sl-sind (floc u13) (falloc u13) hc f₀ ks rdi14) ks13
    hp14 : hpr u14 hp ≡ just env-sv
    hp14 = trans (hp-sind-other (floc u13) (falloc u13) hc hp rdi14 hc≢hp) hp13

    nh15 : halted (floc u15) ≡ false
    nh15 = exec-abstract-preserves-halted-WF (instr-load-code-addr (ℓ o l1)) (floc u14) (falloc u14) nh14 tt
    in15 : Inp u15 ≡ SV-Ptr (AtDynamic hc)
    in15 = trans (in-code (ℓ o l1) (floc u14) (falloc u14)) in14
    out15 : Oup u15 ≡ SV-Code (ℓ o l1)
    out15 = out-code (ℓ o l1) (floc u14) (falloc u14)
    cl15 : sl u15 n ≡ just (SV-Ptr (AtDynamic hc))
    cl15 = trans (sl-keep (instr-load-code-addr (ℓ o l1)) (floc u14) (falloc u14) f₀ n nhw-instr-load-code-addr refl) cl14
    pr15 : sl u15 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr15 = trans (sl-keep (instr-load-code-addr (ℓ o l1)) (floc u14) (falloc u14) f₀ pr nhw-instr-load-code-addr refl) pr14
    ks15 : sl u15 ks ≡ just μ-sv
    ks15 = trans (sl-keep (instr-load-code-addr (ℓ o l1)) (floc u14) (falloc u14) f₀ ks nhw-instr-load-code-addr refl) ks14
    hp15 : hpr u15 hp ≡ just env-sv
    hp15 = trans (hp-keep (instr-load-code-addr (ℓ o l1)) (floc u14) (falloc u14) hp nhw-instr-load-code-addr) hp14

    rdi16 : sv-as-loc (Inp u15) ≡ just (AtDynamic hc)
    rdi16 = cong sv-as-loc in15
    nh16 : halted (floc u16) ≡ false
    nh16 = exec-abstract-preserves-halted-WF store-indirect-suc (floc u15) (falloc u15) nh15 (AtDynamic hc , rdi16)
    code16 : hpr u16 (sucHL hc) ≡ just (SV-Code (ℓ o l1))
    code16 = trans (store-ind-suc-result (floc u15) (falloc u15) hc rdi16) (cong just out15)
    cl16 : sl u16 n ≡ just (SV-Ptr (AtDynamic hc))
    cl16 = trans (sl-sind-suc (floc u15) (falloc u15) hc f₀ n rdi16) cl15
    pr16 : sl u16 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr16 = trans (sl-sind-suc (floc u15) (falloc u15) hc f₀ pr rdi16) pr15
    ks16 : sl u16 ks ≡ just μ-sv
    ks16 = trans (sl-sind-suc (floc u15) (falloc u15) hc f₀ ks rdi16) ks15
    hp16 : hpr u16 hp ≡ just env-sv
    hp16 = trans (store-ind-suc-preserves-heap (floc u15) (falloc u15) hc hp rdi16 shc≢hp) hp15

    ------------------------------------------------------------------
    -- rows 17-18: Input1 := the μ cell again
    ------------------------------------------------------------------
    wf17 : InstrWF (floc u16) (falloc u16) (load-from-slot ks)
    wf17 = μ-sv , at-cf (floc u16) (falloc u16) cf10 ks16
    nh17 : halted (floc u17) ≡ false
    nh17 = exec-abstract-preserves-halted-WF (load-from-slot ks) (floc u16) (falloc u16) nh16 wf17
    out17 : Oup u17 ≡ μ-sv
    out17 = out-lslot ks (floc u16) (falloc u16) μ-sv (proj₂ wf17)
    cl17 : sl u17 n ≡ just (SV-Ptr (AtDynamic hc))
    cl17 = trans (sl-keep (load-from-slot ks) (floc u16) (falloc u16) f₀ n nhw-load-from-slot refl) cl16
    pr17 : sl u17 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr17 = trans (sl-keep (load-from-slot ks) (floc u16) (falloc u16) f₀ pr nhw-load-from-slot refl) pr16
    hp17 : hpr u17 hp ≡ just env-sv
    hp17 = trans (hp-keep (load-from-slot ks) (floc u16) (falloc u16) hp nhw-load-from-slot) hp16
    code17 : hpr u17 (sucHL hc) ≡ just (SV-Code (ℓ o l1))
    code17 = trans (hp-keep (load-from-slot ks) (floc u16) (falloc u16) (sucHL hc) nhw-load-from-slot) code16
    hr17 : next-heap-ref (falloc u17) ≡ suc (suc r₀)
    hr17 = trans (exec-abstract-preserves-heap-ref (load-from-slot ks) (floc u16) (falloc u16) tt) (cong suc hr8)

    nh18 : halted (floc u18) ≡ false
    nh18 = exec-abstract-preserves-halted-WF mov-to-input (floc u17) (falloc u17) nh17 tt
    in18 : Inp u18 ≡ μ-sv
    in18 = trans (in-movin (floc u17) (falloc u17)) out17
    cl18 : sl u18 n ≡ just (SV-Ptr (AtDynamic hc))
    cl18 = trans (sl-keep mov-to-input (floc u17) (falloc u17) f₀ n nhw-mov-to-input refl) cl17
    pr18 : sl u18 pr ≡ just (SV-Ptr (AtDynamic hp))
    pr18 = trans (sl-keep mov-to-input (floc u17) (falloc u17) f₀ pr nhw-mov-to-input refl) pr17
    hp18 : hpr u18 hp ≡ just env-sv
    hp18 = trans (hp-keep mov-to-input (floc u17) (falloc u17) hp nhw-mov-to-input) hp17
    code18 : hpr u18 (sucHL hc) ≡ just (SV-Code (ℓ o l1))
    code18 = trans (hp-keep mov-to-input (floc u17) (falloc u17) (sucHL hc) nhw-mov-to-input) code17
    cf18 : current-frame (falloc u18) ≡ f₀
    cf18 = trans (exec-abstract-preserves-frame (load-from-slot ks) (floc u16) (falloc u16)) cf10
    hr18 : next-heap-ref (falloc u18) ≡ suc (suc r₀)
    hr18 = hr17

    ------------------------------------------------------------------
    -- THE RUN, silent, in three typed pieces.
    ------------------------------------------------------------------
    runA : SRun prog 6 σ u6
    runA =
      s-at u1 (nh0 , span 0 _ refl) refl refl tt (
      s-at u2 (nh1 , span 1 _ refl) refl refl tt (
      s-at u3 (nh2 , span 2 _ refl) refl refl tt (
      s-at u4 (nh3 , span 3 _ refl) refl refl tt (
      s-at u5 (nh4 , span 4 _ refl) refl refl tt (
      s-at u6 (nh5 , span 5 _ refl) refl refl tt s-nil)))))

    runB : SRun prog 6 u6 u12
    runB =
      s-at u7 (nh6 , span 6 _ refl) refl refl tt (
      s-at u8 (nh7 , span 7 _ refl) refl refl tt (
      s-at u9 (nh8 , span 8 _ refl) refl refl tt (
      s-at u10 (nh9 , span 9 _ refl) refl refl tt (
      s-at u11 (nh10 , span 10 _ refl) refl refl tt (
      s-at u12 (nh11 , span 11 _ refl) refl refl tt s-nil)))))

    runC : SRun prog 6 u12 u18
    runC =
      s-at u13 (nh12 , span 12 _ refl) refl refl tt (
      s-at u14 (nh13 , span 13 _ refl) refl refl tt (
      s-at u15 (nh14 , span 14 _ refl) refl refl tt (
      s-at u16 (nh15 , span 15 _ refl) refl refl tt (
      s-at u17 (nh16 , span 16 _ refl) refl refl tt (
      s-at u18 (nh17 , span 17 _ refl) refl refl tt s-nil)))))

    -- composed here, where the states have their own names
    runS : SRun prog 18 σ u18
    runS = s-++ {prog} {6} {12} {σ} {u6} {u18} runA (s-++ {prog} {6} {6} {u6} {u12} {u18} runB runC)

    ------------------------------------------------------------------
    -- WHAT IT LEAVES ALONE, at frontier `n` against the entry allocator.
    ------------------------------------------------------------------
    abstract
      segA : SegA a₀ n σ u6
      segA =
        segA-∘ (seg-q load-indirect σ nhw-load-indirect refl tt tt)
        (segA-∘ (seg-store ev u1 refl (m≤m+n n 2))
        (segA-∘ (seg-q load-indirect-suc u2 nhw-load-indirect-suc refl tt tt)
        (segA-∘ (seg-store ks u3 refl (m≤m+n n 1))
        (segA-∘ (seg-alloc u4)
                (seg-store pr u5 refl (m≤m+n n 3))))))

      segB : SegA a₀ n u6 u12
      segB =
        segA-∘ (seg-q mov-to-input u6 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-q (load-from-slot ev) u7 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-sind u8 hp rdi9 ≤-refl)
        (segA-∘ (seg-alloc u9)
        (segA-∘ (seg-store n u10 cf10 ≤-refl)
                (seg-q mov-to-input u11 nhw-mov-to-input refl tt tt)))))

      segC : SegA a₀ n u12 u18
      segC =
        segA-∘ (seg-q (instr-load-tag-lit 0) u12 nhw-instr-load-tag-lit refl tt tt)
        (segA-∘ (seg-sind u13 hc rdi14 (≤-trans (n≤1+n r₀) (≤-reflexive (sym ref-hc))))
        (segA-∘ (seg-q (instr-load-code-addr (ℓ o l1)) u14 nhw-instr-load-code-addr refl tt tt)
        (segA-∘ (seg-sind-suc u15 hc rdi16 (≤-trans (n≤1+n r₀) (≤-reflexive (sym ref-hc))))
        (segA-∘ (seg-q (load-from-slot ks) u16 nhw-load-from-slot refl tt tt)
                (seg-q mov-to-input u17 nhw-mov-to-input refl tt tt)))))

      seg : SegA a₀ n σ u18
      seg = segA-∘ segA (segA-∘ segB segC)

    abstract
      out : SetupOut n l1 prog σ env-sv μ-sv
      out = record
        { u = u18 ; runS = runS ; seg = seg ; nh = nh18 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; hc = hc ; ref-hc = ref-hc
        ; inμ = in18 ; cl = at-cf (floc u18) (falloc u18) cf18 cl18 ; pr = at-cf (floc u18) (falloc u18) cf18 pr18
        ; hp0 = hp18 ; code = code18 ; cf = cf18 ; hr = hr18 }
