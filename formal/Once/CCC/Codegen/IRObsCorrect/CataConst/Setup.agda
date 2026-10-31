-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Setup   (plan 0.135 S3, cata M1)
--
-- THE CATA'S THIRTEEN SETUP ROWS (`cata-call-setup cl k ev body`), run
-- from any state whose `Input1` points at the input pair `(env , μ)`:
--
--     load-indirect · store ev · load-indirect-suc · store k     split the pair
--     alloc · store cl · mov-to-input · tag 0 · store-indirect ·
--       code-addr body · store-indirect-suc                       cl := [0 , body]
--     load k · mov-to-input                                       Input1 := μ
--
-- What the call rows need afterwards: the closure record's code cell, the
-- environment in slot `ev` (every call copies it into its FRESH argument
-- pair — plan 0.135 D1a), the record pointer in `cl`, and `Input1` holding
-- the μ cell again. Everything the caller has live is untouched (`seg`): the
-- three slots are at or above the frontier and the two heap writes land in
-- the block this run allocated.
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
  -- unfold the thirteen steps behind it.
  record SetupOut (n l1 : ℕ) (prog : AbstractTrace) (σ : FlatState) (env-sv μ-sv : StoredValue FS) : Set where
    field
      u      : FlatState
      runS   : SRun prog 13 σ u
      seg    : SegA (falloc σ) n σ u
      nh     : halted (floc u) ≡ false
      pc     : fpc u ≡ 13 + fpc σ
      ret    : fret u ≡ fret σ
      clo    : fclosure u ≡ fclosure σ
      lnk    : flink u ≡ flink σ
      hc     : HeapLocation
      ref-hc : ref-id (heap-ref hc) ≡ next-heap-ref (falloc σ)
      inμ    : readReg (regs (floc u)) Input1 ≡ μ-sv
      cl     : readLoc (floc u) (AtStack (current-frame (falloc u)) n) ≡ just (SV-Ptr (AtDynamic hc))
      ev     : readLoc (floc u) (AtStack (current-frame (falloc u)) (n ℕ.+ 2)) ≡ just env-sv
      code   : readLoc (floc u) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o l1))
      cf     : current-frame (falloc u) ≡ current-frame (falloc σ)
      hr     : next-heap-ref (falloc u) ≡ suc (next-heap-ref (falloc σ))

  module Setup (n l1 : ℕ) (prog : AbstractTrace) (σ : FlatState)
               (span : SpanAt prog (fpc σ) (cata-call-setup n (n ℕ.+ 1) (n ℕ.+ 2) l1))
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

    ks ev : ℕ
    ks = n ℕ.+ 1
    ev = n ℕ.+ 2

    pl : ValueLocation FS
    pl = AtDynamic phl

    ev≢ks : ev ≢ ks
    ev≢ks = off-≢ n (λ ())
    ks≢n : ks ≢ n
    ks≢n e = off0-≢ n (λ ()) (sym e)
    ev≢n : ev ≢ n
    ev≢n e = off0-≢ n (λ ()) (sym e)

    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 : FlatState
    u1  = St load-indirect σ
    u2  = St (store-at-slot ev) u1
    u3  = St load-indirect-suc u2
    u4  = St (store-at-slot ks) u3
    u5  = St (instr-alloc-heap 2) u4
    u6  = St (store-at-slot n) u5
    u7  = St mov-to-input u6
    u8  = St (instr-load-tag-lit 0) u7
    u9  = St store-indirect u8
    u10 = St (instr-load-code-addr (ℓ o l1)) u9
    u11 = St store-indirect-suc u10
    u12 = St (load-from-slot ks) u11
    u13 = St mov-to-input u12

    -- the closure record, as the allocator hands it out
    hc : HeapLocation
    hc = heap-loc (mkHeapRef (next-heap-ref (falloc u4))) 0

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
    cf4 : current-frame (falloc u4) ≡ f₀
    cf4 = trans (exec-abstract-preserves-frame (store-at-slot ks) (floc u3) (falloc u3))
          (trans (exec-abstract-preserves-frame load-indirect-suc (floc u2) (falloc u2))
          (trans (exec-abstract-preserves-frame (store-at-slot ev) (floc u1) (falloc u1))
                 (exec-abstract-preserves-frame load-indirect s₀ a₀)))
    hr4 : next-heap-ref (falloc u4) ≡ r₀
    hr4 = trans (exec-abstract-preserves-heap-ref (store-at-slot ks) (floc u3) (falloc u3) tt)
          (trans (exec-abstract-preserves-heap-ref load-indirect-suc (floc u2) (falloc u2) tt)
          (trans (exec-abstract-preserves-heap-ref (store-at-slot ev) (floc u1) (falloc u1) tt)
                 (exec-abstract-preserves-heap-ref load-indirect s₀ a₀ tt)))

    ------------------------------------------------------------------
    -- rows 5-11: the closure record, [tag 0 , code of the body]
    ------------------------------------------------------------------
    ref-hc : ref-id (heap-ref hc) ≡ r₀
    ref-hc = hr4

    nh5 : halted (floc u5) ≡ false
    nh5 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc u4) (falloc u4) nh4 tt
    out5 : Oup u5 ≡ SV-Ptr (AtDynamic hc)
    out5 = out-alloc 2 (floc u4) (falloc u4)
    ks5 : sl u5 ks ≡ just μ-sv
    ks5 = trans (sl-keep (instr-alloc-heap 2) (floc u4) (falloc u4) f₀ ks nhw-instr-alloc-heap refl) ks4
    ev5 : sl u5 ev ≡ just env-sv
    ev5 = trans (sl-keep (instr-alloc-heap 2) (floc u4) (falloc u4) f₀ ev nhw-instr-alloc-heap refl) ev4
    cf5 : current-frame (falloc u5) ≡ f₀
    cf5 = cf4

    nh6 : halted (floc u6) ≡ false
    nh6 = exec-abstract-preserves-halted-WF (store-at-slot n) (floc u5) (falloc u5) nh5 tt
    cl6 : sl u6 n ≡ just (SV-Ptr (AtDynamic hc))
    cl6 = trans (sl-same n (floc u5) (falloc u5) f₀ cf5) (cong just out5)
    ks6 : sl u6 ks ≡ just μ-sv
    ks6 = trans (sl-other n ks (floc u5) (falloc u5) f₀ ks≢n) ks5
    ev6 : sl u6 ev ≡ just env-sv
    ev6 = trans (sl-other n ev (floc u5) (falloc u5) f₀ ev≢n) ev5

    nh7 : halted (floc u7) ≡ false
    nh7 = exec-abstract-preserves-halted-WF mov-to-input (floc u6) (falloc u6) nh6 tt
    in7 : Inp u7 ≡ SV-Ptr (AtDynamic hc)
    in7 = trans (in-movin (floc u6) (falloc u6)) (trans (reg-store n (floc u5) (falloc u5) Output) out5)
    cl7 : sl u7 n ≡ just (SV-Ptr (AtDynamic hc))
    cl7 = trans (sl-keep mov-to-input (floc u6) (falloc u6) f₀ n nhw-mov-to-input refl) cl6
    ks7 : sl u7 ks ≡ just μ-sv
    ks7 = trans (sl-keep mov-to-input (floc u6) (falloc u6) f₀ ks nhw-mov-to-input refl) ks6
    ev7 : sl u7 ev ≡ just env-sv
    ev7 = trans (sl-keep mov-to-input (floc u6) (falloc u6) f₀ ev nhw-mov-to-input refl) ev6

    nh8 : halted (floc u8) ≡ false
    nh8 = exec-abstract-preserves-halted-WF (instr-load-tag-lit 0) (floc u7) (falloc u7) nh7 tt
    in8 : Inp u8 ≡ SV-Ptr (AtDynamic hc)
    in8 = trans (in-tag 0 (floc u7) (falloc u7)) in7
    cl8 : sl u8 n ≡ just (SV-Ptr (AtDynamic hc))
    cl8 = trans (sl-keep (instr-load-tag-lit 0) (floc u7) (falloc u7) f₀ n nhw-instr-load-tag-lit refl) cl7
    ks8 : sl u8 ks ≡ just μ-sv
    ks8 = trans (sl-keep (instr-load-tag-lit 0) (floc u7) (falloc u7) f₀ ks nhw-instr-load-tag-lit refl) ks7
    ev8 : sl u8 ev ≡ just env-sv
    ev8 = trans (sl-keep (instr-load-tag-lit 0) (floc u7) (falloc u7) f₀ ev nhw-instr-load-tag-lit refl) ev7

    rdi9 : sv-as-loc (Inp u8) ≡ just (AtDynamic hc)
    rdi9 = cong sv-as-loc in8
    nh9 : halted (floc u9) ≡ false
    nh9 = exec-abstract-preserves-halted-WF store-indirect (floc u8) (falloc u8) nh8 (AtDynamic hc , rdi9)
    in9 : Inp u9 ≡ SV-Ptr (AtDynamic hc)
    in9 = trans (in-sind (floc u8) (falloc u8) (AtDynamic hc) rdi9) in8
    cl9 : sl u9 n ≡ just (SV-Ptr (AtDynamic hc))
    cl9 = trans (sl-sind (floc u8) (falloc u8) hc f₀ n rdi9) cl8
    ks9 : sl u9 ks ≡ just μ-sv
    ks9 = trans (sl-sind (floc u8) (falloc u8) hc f₀ ks rdi9) ks8
    ev9 : sl u9 ev ≡ just env-sv
    ev9 = trans (sl-sind (floc u8) (falloc u8) hc f₀ ev rdi9) ev8

    nh10 : halted (floc u10) ≡ false
    nh10 = exec-abstract-preserves-halted-WF (instr-load-code-addr (ℓ o l1)) (floc u9) (falloc u9) nh9 tt
    in10 : Inp u10 ≡ SV-Ptr (AtDynamic hc)
    in10 = trans (in-code (ℓ o l1) (floc u9) (falloc u9)) in9
    out10 : Oup u10 ≡ SV-Code (ℓ o l1)
    out10 = out-code (ℓ o l1) (floc u9) (falloc u9)
    cl10 : sl u10 n ≡ just (SV-Ptr (AtDynamic hc))
    cl10 = trans (sl-keep (instr-load-code-addr (ℓ o l1)) (floc u9) (falloc u9) f₀ n nhw-instr-load-code-addr refl) cl9
    ks10 : sl u10 ks ≡ just μ-sv
    ks10 = trans (sl-keep (instr-load-code-addr (ℓ o l1)) (floc u9) (falloc u9) f₀ ks nhw-instr-load-code-addr refl) ks9
    ev10 : sl u10 ev ≡ just env-sv
    ev10 = trans (sl-keep (instr-load-code-addr (ℓ o l1)) (floc u9) (falloc u9) f₀ ev nhw-instr-load-code-addr refl) ev9

    rdi11 : sv-as-loc (Inp u10) ≡ just (AtDynamic hc)
    rdi11 = cong sv-as-loc in10
    nh11 : halted (floc u11) ≡ false
    nh11 = exec-abstract-preserves-halted-WF store-indirect-suc (floc u10) (falloc u10) nh10 (AtDynamic hc , rdi11)
    code11 : hpr u11 (sucHL hc) ≡ just (SV-Code (ℓ o l1))
    code11 = trans (store-ind-suc-result (floc u10) (falloc u10) hc rdi11) (cong just out10)
    cl11 : sl u11 n ≡ just (SV-Ptr (AtDynamic hc))
    cl11 = trans (sl-sind-suc (floc u10) (falloc u10) hc f₀ n rdi11) cl10
    ks11 : sl u11 ks ≡ just μ-sv
    ks11 = trans (sl-sind-suc (floc u10) (falloc u10) hc f₀ ks rdi11) ks10
    ev11 : sl u11 ev ≡ just env-sv
    ev11 = trans (sl-sind-suc (floc u10) (falloc u10) hc f₀ ev rdi11) ev10

    ------------------------------------------------------------------
    -- rows 12-13: Input1 := the μ cell again
    ------------------------------------------------------------------
    wf12 : InstrWF (floc u11) (falloc u11) (load-from-slot ks)
    wf12 = μ-sv , at-cf (floc u11) (falloc u11) cf5 ks11
    nh12 : halted (floc u12) ≡ false
    nh12 = exec-abstract-preserves-halted-WF (load-from-slot ks) (floc u11) (falloc u11) nh11 wf12
    out12 : Oup u12 ≡ μ-sv
    out12 = out-lslot ks (floc u11) (falloc u11) μ-sv (proj₂ wf12)
    cl12 : sl u12 n ≡ just (SV-Ptr (AtDynamic hc))
    cl12 = trans (sl-keep (load-from-slot ks) (floc u11) (falloc u11) f₀ n nhw-load-from-slot refl) cl11
    ev12 : sl u12 ev ≡ just env-sv
    ev12 = trans (sl-keep (load-from-slot ks) (floc u11) (falloc u11) f₀ ev nhw-load-from-slot refl) ev11
    code12 : hpr u12 (sucHL hc) ≡ just (SV-Code (ℓ o l1))
    code12 = trans (hp-keep (load-from-slot ks) (floc u11) (falloc u11) (sucHL hc) nhw-load-from-slot) code11
    hr12 : next-heap-ref (falloc u12) ≡ suc r₀
    hr12 = trans (exec-abstract-preserves-heap-ref (load-from-slot ks) (floc u11) (falloc u11) tt) (cong suc hr4)

    nh13 : halted (floc u13) ≡ false
    nh13 = exec-abstract-preserves-halted-WF mov-to-input (floc u12) (falloc u12) nh12 tt
    in13 : Inp u13 ≡ μ-sv
    in13 = trans (in-movin (floc u12) (falloc u12)) out12
    cl13 : sl u13 n ≡ just (SV-Ptr (AtDynamic hc))
    cl13 = trans (sl-keep mov-to-input (floc u12) (falloc u12) f₀ n nhw-mov-to-input refl) cl12
    ev13 : sl u13 ev ≡ just env-sv
    ev13 = trans (sl-keep mov-to-input (floc u12) (falloc u12) f₀ ev nhw-mov-to-input refl) ev12
    code13 : hpr u13 (sucHL hc) ≡ just (SV-Code (ℓ o l1))
    code13 = trans (hp-keep mov-to-input (floc u12) (falloc u12) (sucHL hc) nhw-mov-to-input) code12
    cf13 : current-frame (falloc u13) ≡ f₀
    cf13 = trans (exec-abstract-preserves-frame (load-from-slot ks) (floc u11) (falloc u11)) cf5
    hr13 : next-heap-ref (falloc u13) ≡ suc r₀
    hr13 = hr12

    ------------------------------------------------------------------
    -- THE RUN, silent, in two typed pieces.
    ------------------------------------------------------------------
    runA : SRun prog 6 σ u6
    runA =
      s-at u1 (nh0 , span 0 _ refl) refl refl tt (
      s-at u2 (nh1 , span 1 _ refl) refl refl tt (
      s-at u3 (nh2 , span 2 _ refl) refl refl tt (
      s-at u4 (nh3 , span 3 _ refl) refl refl tt (
      s-at u5 (nh4 , span 4 _ refl) refl refl tt (
      s-at u6 (nh5 , span 5 _ refl) refl refl tt s-nil)))))

    runB : SRun prog 7 u6 u13
    runB =
      s-at u7 (nh6 , span 6 _ refl) refl refl tt (
      s-at u8 (nh7 , span 7 _ refl) refl refl tt (
      s-at u9 (nh8 , span 8 _ refl) refl refl tt (
      s-at u10 (nh9 , span 9 _ refl) refl refl tt (
      s-at u11 (nh10 , span 10 _ refl) refl refl tt (
      s-at u12 (nh11 , span 11 _ refl) refl refl tt (
      s-at u13 (nh12 , span 12 _ refl) refl refl tt s-nil))))))

    -- composed here, where the states have their own names
    runS : SRun prog 13 σ u13
    runS = s-++ {prog} {6} {7} {σ} {u6} {u13} runA runB

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
                (seg-store n u5 cf5 ≤-refl)))))

      segB : SegA a₀ n u6 u13
      segB =
        segA-∘ (seg-q mov-to-input u6 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-q (instr-load-tag-lit 0) u7 nhw-instr-load-tag-lit refl tt tt)
        (segA-∘ (seg-sind u8 hc rdi9 (≤-reflexive (sym ref-hc)))
        (segA-∘ (seg-q (instr-load-code-addr (ℓ o l1)) u9 nhw-instr-load-code-addr refl tt tt)
        (segA-∘ (seg-sind-suc u10 hc rdi11 (≤-reflexive (sym ref-hc)))
        (segA-∘ (seg-q (load-from-slot ks) u11 nhw-load-from-slot refl tt tt)
                (seg-q mov-to-input u12 nhw-mov-to-input refl tt tt))))))

      seg : SegA a₀ n σ u13
      seg = segA-∘ segA segB

    abstract
      out : SetupOut n l1 prog σ env-sv μ-sv
      out = record
        { u = u13 ; runS = runS ; seg = seg ; nh = nh13 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; hc = hc ; ref-hc = ref-hc
        ; inμ = in13 ; cl = at-cf (floc u13) (falloc u13) cf13 cl13 ; ev = at-cf (floc u13) (falloc u13) cf13 ev13
        ; code = code13 ; cf = cf13 ; hr = hr13 }
