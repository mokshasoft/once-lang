-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Init   (plan 0.135 S3, cata M4 stage C)
--
-- THE INIT ROWS of `cata-br-I₁` (`Text.init-rows`, fourteen) and the push of
-- the root, from a state whose `Input1` holds the root node's word:
--
--     mov-to-output · store tmp                          tmp := root
--     alloc · store n+6 · mov-to-input ·
--       tag 0 · store-indirect                           sn := [SV-Tag 0 , _]
--     load n+6 · store eval · load n+6 · store val ·
--       load n+6 · store todo                            three empty stacks
--     load tmp                                           Output := root
--     push2 todo                                         todo = [ root ]
--
-- It ends (`Init.out`, a `Walk`) with the three stacks on the one fresh
-- sentinel `sn` (`InitQ`): todo `[ root ]`, eval `[]`, val `[]`. Every slot
-- from `c ≥ n+7` on is kept (the call slots the setup filled), and the rest
-- is the walk's `Seg` at frontier `n`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Init (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (init-rows; module SlotArith; module OffArith)
open import Once.CCC.Codegen.IRToTrace o using (push2)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Tag; sv-as-loc; store-at-slot; load-from-slot; store-indirect; mov-to-input; mov-to-output
        ; instr-alloc-heap; instr-load-tag-lit)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.IRTy using (IRTy; IRFunctor; μ-type)
open import Data.Unit using (⊤)

module CataInitC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  -- what the init leaves: three stacks on one sentinel
  record InitQ (prog : AbstractTrace) (F : IRFunctor) (C : IRTy) (n : ℕ) (sn : HeapLocation)
               (root : ⟦ μ-type F ⟧) (τ : FlatState) : Set where
    field
      todo : StackAt (NodeE prog F) (falloc τ) (floc τ) n sn (root ∷ [])
      eval : StackAt (NodeE prog F) (falloc τ) (floc τ) (suc n) sn []
      val  : StackAt (ValE prog C) (falloc τ) (floc τ) (n + 2) sn []

  -- the slots it keeps: the call slots and above
  KI : ℕ → ℕ → Set
  KI c j = c ≤ j

  module Init (prog : AbstractTrace) (F : IRFunctor) (C : IRTy) (n c : ℕ) (n7≤c : n + 7 ≤ c) (σ : FlatState)
              (span : SpanAt prog (fpc σ) (init-rows n ++ push2 n (n + 4) (n + 5)))
              (nh0 : halted (floc σ) ≡ false)
              (root : ⟦ μ-type F ⟧)
              (wd : NodeE prog F (falloc σ) (floc σ) root (readReg (regs (floc σ)) Input1)) where

    open SlotArith n c n7≤c
    open OffArith n

    s₀ = floc σ
    a₀ = falloc σ
    f₀ = current-frame a₀
    r₀ = next-heap-ref a₀
    w  = readReg (regs s₀) Input1

    tmp ss ev vl : ℕ
    tmp = n + 3
    ss = n + 6
    ev = suc n
    vl = n + 2

    -- the sentinel, as the allocator hands it out
    sn : HeapLocation
    sn = heap-loc (mkHeapRef r₀) 0

    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 : FlatState
    u1  = St mov-to-output σ
    u2  = St (store-at-slot tmp) u1
    u3  = St (instr-alloc-heap 2) u2
    u4  = St (store-at-slot ss) u3
    u5  = St mov-to-input u4
    u6  = St (instr-load-tag-lit 0) u5
    u7  = St store-indirect u6
    u8  = St (load-from-slot ss) u7
    u9  = St (store-at-slot ev) u8
    u10 = St (load-from-slot ss) u9
    u11 = St (store-at-slot vl) u10
    u12 = St (load-from-slot ss) u11
    u13 = St (store-at-slot n) u12
    u14 = St (load-from-slot tmp) u13

    Inp Oup : FlatState → StoredValue FS
    Inp t = readReg (regs (floc t)) Input1
    Oup t = readReg (regs (floc t)) Output

    sl : FlatState → ℕ → Maybe (StoredValue FS)
    sl t j = readLoc (floc t) (AtStack f₀ j)

    hpr : FlatState → HeapLocation → Maybe (StoredValue FS)
    hpr t h = readLoc (floc t) (AtDynamic h)

    psn : StoredValue FS
    psn = SV-Ptr (AtDynamic sn)

    -- frames
    cf1 : current-frame (falloc u1) ≡ f₀
    cf1 = exec-abstract-preserves-frame mov-to-output s₀ a₀
    cf2 : current-frame (falloc u2) ≡ f₀
    cf2 = trans (exec-abstract-preserves-frame (store-at-slot tmp) (floc u1) (falloc u1)) cf1
    cf3 : current-frame (falloc u3) ≡ f₀
    cf3 = trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc u2) (falloc u2)) cf2
    cf4 : current-frame (falloc u4) ≡ f₀
    cf4 = trans (exec-abstract-preserves-frame (store-at-slot ss) (floc u3) (falloc u3)) cf3
    cf5 : current-frame (falloc u5) ≡ f₀
    cf5 = trans (exec-abstract-preserves-frame mov-to-input (floc u4) (falloc u4)) cf4
    cf6 : current-frame (falloc u6) ≡ f₀
    cf6 = trans (exec-abstract-preserves-frame (instr-load-tag-lit 0) (floc u5) (falloc u5)) cf5
    cf7 : current-frame (falloc u7) ≡ f₀
    cf7 = trans (exec-abstract-preserves-frame store-indirect (floc u6) (falloc u6)) cf6
    cf8 : current-frame (falloc u8) ≡ f₀
    cf8 = trans (exec-abstract-preserves-frame (load-from-slot ss) (floc u7) (falloc u7)) cf7
    cf9 : current-frame (falloc u9) ≡ f₀
    cf9 = trans (exec-abstract-preserves-frame (store-at-slot ev) (floc u8) (falloc u8)) cf8
    cf10 : current-frame (falloc u10) ≡ f₀
    cf10 = trans (exec-abstract-preserves-frame (load-from-slot ss) (floc u9) (falloc u9)) cf9
    cf11 : current-frame (falloc u11) ≡ f₀
    cf11 = trans (exec-abstract-preserves-frame (store-at-slot vl) (floc u10) (falloc u10)) cf10
    cf12 : current-frame (falloc u12) ≡ f₀
    cf12 = trans (exec-abstract-preserves-frame (load-from-slot ss) (floc u11) (falloc u11)) cf11
    cf13 : current-frame (falloc u13) ≡ f₀
    cf13 = trans (exec-abstract-preserves-frame (store-at-slot n) (floc u12) (falloc u12)) cf12
    cf14 : current-frame (falloc u14) ≡ f₀
    cf14 = trans (exec-abstract-preserves-frame (load-from-slot tmp) (floc u13) (falloc u13)) cf13

    -- heap frontier
    hr2 : next-heap-ref (falloc u2) ≡ r₀
    hr2 = trans (exec-abstract-preserves-heap-ref (store-at-slot tmp) (floc u1) (falloc u1) tt)
                (exec-abstract-preserves-heap-ref mov-to-output s₀ a₀ tt)

    ------------------------------------------------------------------
    -- rows 1-2: tmp := root
    ------------------------------------------------------------------
    nh1 : halted (floc u1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF mov-to-output s₀ a₀ nh0 tt
    out1 : Oup u1 ≡ w
    out1 = out-movout s₀ a₀
    nh2 : halted (floc u2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (store-at-slot tmp) (floc u1) (falloc u1) nh1 tt
    tmp2 : sl u2 tmp ≡ just w
    tmp2 = trans (sl-same tmp (floc u1) (falloc u1) f₀ cf1) (cong just out1)

    ------------------------------------------------------------------
    -- rows 3-7: the sentinel
    ------------------------------------------------------------------
    nh3 : halted (floc u3) ≡ false
    nh3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc u2) (falloc u2) nh2 tt
    out3 : Oup u3 ≡ psn
    out3 = trans (out-alloc 2 (floc u2) (falloc u2)) (cong (λ r → SV-Ptr (AtDynamic (heap-loc (mkHeapRef r) 0))) hr2)
    tmp3 : sl u3 tmp ≡ just w
    tmp3 = trans (sl-keep (instr-alloc-heap 2) (floc u2) (falloc u2) f₀ tmp nhw-instr-alloc-heap refl) tmp2
    hr3 : next-heap-ref (falloc u3) ≡ suc r₀
    hr3 = cong suc hr2

    nh4 : halted (floc u4) ≡ false
    nh4 = exec-abstract-preserves-halted-WF (store-at-slot ss) (floc u3) (falloc u3) nh3 tt
    ss4 : sl u4 ss ≡ just psn
    ss4 = trans (sl-same ss (floc u3) (falloc u3) f₀ cf3) (cong just out3)
    tmp4 : sl u4 tmp ≡ just w
    tmp4 = trans (sl-other ss tmp (floc u3) (falloc u3) f₀ (off-≢ (λ ()))) tmp3

    nh5 : halted (floc u5) ≡ false
    nh5 = exec-abstract-preserves-halted-WF mov-to-input (floc u4) (falloc u4) nh4 tt
    in5 : Inp u5 ≡ psn
    in5 = trans (in-movin (floc u4) (falloc u4)) (trans (reg-store ss (floc u3) (falloc u3) Output) out3)
    ss5 : sl u5 ss ≡ just psn
    ss5 = trans (sl-keep mov-to-input (floc u4) (falloc u4) f₀ ss nhw-mov-to-input refl) ss4
    tmp5 : sl u5 tmp ≡ just w
    tmp5 = trans (sl-keep mov-to-input (floc u4) (falloc u4) f₀ tmp nhw-mov-to-input refl) tmp4

    nh6 : halted (floc u6) ≡ false
    nh6 = exec-abstract-preserves-halted-WF (instr-load-tag-lit 0) (floc u5) (falloc u5) nh5 tt
    in6 : Inp u6 ≡ psn
    in6 = trans (in-tag 0 (floc u5) (falloc u5)) in5
    out6 : Oup u6 ≡ SV-Tag 0
    out6 = out-tag 0 (floc u5) (falloc u5)
    ss6 : sl u6 ss ≡ just psn
    ss6 = trans (sl-keep (instr-load-tag-lit 0) (floc u5) (falloc u5) f₀ ss nhw-instr-load-tag-lit refl) ss5
    tmp6 : sl u6 tmp ≡ just w
    tmp6 = trans (sl-keep (instr-load-tag-lit 0) (floc u5) (falloc u5) f₀ tmp nhw-instr-load-tag-lit refl) tmp5

    rdi7 : sv-as-loc (Inp u6) ≡ just (AtDynamic sn)
    rdi7 = cong sv-as-loc in6
    nh7 : halted (floc u7) ≡ false
    nh7 = exec-abstract-preserves-halted-WF store-indirect (floc u6) (falloc u6) nh6 (AtDynamic sn , rdi7)
    sent7 : hpr u7 sn ≡ just (SV-Tag 0)
    sent7 = trans (store-ind-result (floc u6) (falloc u6) sn rdi7) (cong just out6)
    ss7 : sl u7 ss ≡ just psn
    ss7 = trans (sl-sind (floc u6) (falloc u6) sn f₀ ss rdi7) ss6
    tmp7 : sl u7 tmp ≡ just w
    tmp7 = trans (sl-sind (floc u6) (falloc u6) sn f₀ tmp rdi7) tmp6

    ------------------------------------------------------------------
    -- rows 8-13: eval, val, todo := sn
    ------------------------------------------------------------------
    wf8 : InstrWF (floc u7) (falloc u7) (load-from-slot ss)
    wf8 = psn , at-cf (floc u7) (falloc u7) cf7 ss7
    nh8 : halted (floc u8) ≡ false
    nh8 = exec-abstract-preserves-halted-WF (load-from-slot ss) (floc u7) (falloc u7) nh7 wf8
    out8 : Oup u8 ≡ psn
    out8 = out-lslot ss (floc u7) (falloc u7) psn (proj₂ wf8)
    ss8 : sl u8 ss ≡ just psn
    ss8 = trans (sl-keep (load-from-slot ss) (floc u7) (falloc u7) f₀ ss nhw-load-from-slot refl) ss7
    tmp8 : sl u8 tmp ≡ just w
    tmp8 = trans (sl-keep (load-from-slot ss) (floc u7) (falloc u7) f₀ tmp nhw-load-from-slot refl) tmp7
    sent8 : hpr u8 sn ≡ just (SV-Tag 0)
    sent8 = trans (hp-keep (load-from-slot ss) (floc u7) (falloc u7) sn nhw-load-from-slot) sent7

    nh9 : halted (floc u9) ≡ false
    nh9 = exec-abstract-preserves-halted-WF (store-at-slot ev) (floc u8) (falloc u8) nh8 tt
    ev9 : sl u9 ev ≡ just psn
    ev9 = trans (sl-same ev (floc u8) (falloc u8) f₀ cf8) (cong just out8)
    ss9 : sl u9 ss ≡ just psn
    ss9 = trans (sl-other ev ss (floc u8) (falloc u8) f₀ (λ e → off-≢ {6} {1} (λ ()) (trans e suc-is))) ss8
    tmp9 : sl u9 tmp ≡ just w
    tmp9 = trans (sl-other ev tmp (floc u8) (falloc u8) f₀ (λ e → off-≢ {3} {1} (λ ()) (trans e suc-is))) tmp8
    sent9 : hpr u9 sn ≡ just (SV-Tag 0)
    sent9 = trans (hp-keep (store-at-slot ev) (floc u8) (falloc u8) sn nhw-store-at-slot) sent8

    wf10 : InstrWF (floc u9) (falloc u9) (load-from-slot ss)
    wf10 = psn , at-cf (floc u9) (falloc u9) cf9 ss9
    nh10 : halted (floc u10) ≡ false
    nh10 = exec-abstract-preserves-halted-WF (load-from-slot ss) (floc u9) (falloc u9) nh9 wf10
    out10 : Oup u10 ≡ psn
    out10 = out-lslot ss (floc u9) (falloc u9) psn (proj₂ wf10)
    ss10 : sl u10 ss ≡ just psn
    ss10 = trans (sl-keep (load-from-slot ss) (floc u9) (falloc u9) f₀ ss nhw-load-from-slot refl) ss9
    tmp10 : sl u10 tmp ≡ just w
    tmp10 = trans (sl-keep (load-from-slot ss) (floc u9) (falloc u9) f₀ tmp nhw-load-from-slot refl) tmp9
    ev10 : sl u10 ev ≡ just psn
    ev10 = trans (sl-keep (load-from-slot ss) (floc u9) (falloc u9) f₀ ev nhw-load-from-slot refl) ev9
    sent10 : hpr u10 sn ≡ just (SV-Tag 0)
    sent10 = trans (hp-keep (load-from-slot ss) (floc u9) (falloc u9) sn nhw-load-from-slot) sent9

    nh11 : halted (floc u11) ≡ false
    nh11 = exec-abstract-preserves-halted-WF (store-at-slot vl) (floc u10) (falloc u10) nh10 tt
    vl11 : sl u11 vl ≡ just psn
    vl11 = trans (sl-same vl (floc u10) (falloc u10) f₀ cf10) (cong just out10)
    ss11 : sl u11 ss ≡ just psn
    ss11 = trans (sl-other vl ss (floc u10) (falloc u10) f₀ (off-≢ (λ ()))) ss10
    tmp11 : sl u11 tmp ≡ just w
    tmp11 = trans (sl-other vl tmp (floc u10) (falloc u10) f₀ (off-≢ (λ ()))) tmp10
    ev11 : sl u11 ev ≡ just psn
    ev11 = trans (sl-other vl ev (floc u10) (falloc u10) f₀ (λ e → off-≢ {1} {2} (λ ()) (trans (sym suc-is) e))) ev10
    sent11 : hpr u11 sn ≡ just (SV-Tag 0)
    sent11 = trans (hp-keep (store-at-slot vl) (floc u10) (falloc u10) sn nhw-store-at-slot) sent10

    wf12 : InstrWF (floc u11) (falloc u11) (load-from-slot ss)
    wf12 = psn , at-cf (floc u11) (falloc u11) cf11 ss11
    nh12 : halted (floc u12) ≡ false
    nh12 = exec-abstract-preserves-halted-WF (load-from-slot ss) (floc u11) (falloc u11) nh11 wf12
    out12 : Oup u12 ≡ psn
    out12 = out-lslot ss (floc u11) (falloc u11) psn (proj₂ wf12)
    tmp12 : sl u12 tmp ≡ just w
    tmp12 = trans (sl-keep (load-from-slot ss) (floc u11) (falloc u11) f₀ tmp nhw-load-from-slot refl) tmp11
    ev12 : sl u12 ev ≡ just psn
    ev12 = trans (sl-keep (load-from-slot ss) (floc u11) (falloc u11) f₀ ev nhw-load-from-slot refl) ev11
    vl12 : sl u12 vl ≡ just psn
    vl12 = trans (sl-keep (load-from-slot ss) (floc u11) (falloc u11) f₀ vl nhw-load-from-slot refl) vl11
    sent12 : hpr u12 sn ≡ just (SV-Tag 0)
    sent12 = trans (hp-keep (load-from-slot ss) (floc u11) (falloc u11) sn nhw-load-from-slot) sent11

    nh13 : halted (floc u13) ≡ false
    nh13 = exec-abstract-preserves-halted-WF (store-at-slot n) (floc u12) (falloc u12) nh12 tt
    td13 : sl u13 n ≡ just psn
    td13 = trans (sl-same n (floc u12) (falloc u12) f₀ cf12) (cong just out12)
    tmp13 : sl u13 tmp ≡ just w
    tmp13 = trans (sl-other n tmp (floc u12) (falloc u12) f₀ (λ e → off0-≢ {3} (λ ()) (sym e))) tmp12
    ev13 : sl u13 ev ≡ just psn
    ev13 = trans (sl-other n ev (floc u12) (falloc u12) f₀ s≢n) ev12
    vl13 : sl u13 vl ≡ just psn
    vl13 = trans (sl-other n vl (floc u12) (falloc u12) f₀ (λ e → off0-≢ {2} (λ ()) (sym e))) vl12
    sent13 : hpr u13 sn ≡ just (SV-Tag 0)
    sent13 = trans (hp-keep (store-at-slot n) (floc u12) (falloc u12) sn nhw-store-at-slot) sent12

    ------------------------------------------------------------------
    -- row 14: Output := root
    ------------------------------------------------------------------
    wf14 : InstrWF (floc u13) (falloc u13) (load-from-slot tmp)
    wf14 = w , at-cf (floc u13) (falloc u13) cf13 tmp13
    nh14 : halted (floc u14) ≡ false
    nh14 = exec-abstract-preserves-halted-WF (load-from-slot tmp) (floc u13) (falloc u13) nh13 wf14
    out14 : Oup u14 ≡ w
    out14 = out-lslot tmp (floc u13) (falloc u13) w (proj₂ wf14)
    td14 : sl u14 n ≡ just psn
    td14 = trans (sl-keep (load-from-slot tmp) (floc u13) (falloc u13) f₀ n nhw-load-from-slot refl) td13
    ev14 : sl u14 ev ≡ just psn
    ev14 = trans (sl-keep (load-from-slot tmp) (floc u13) (falloc u13) f₀ ev nhw-load-from-slot refl) ev13
    vl14 : sl u14 vl ≡ just psn
    vl14 = trans (sl-keep (load-from-slot tmp) (floc u13) (falloc u13) f₀ vl nhw-load-from-slot refl) vl13
    sent14 : hpr u14 sn ≡ just (SV-Tag 0)
    sent14 = trans (hp-keep (load-from-slot tmp) (floc u13) (falloc u13) sn nhw-load-from-slot) sent13

    hr14 : next-heap-ref (falloc u14) ≡ suc r₀
    hr14 =
      trans (exec-abstract-preserves-heap-ref (load-from-slot tmp) (floc u13) (falloc u13) tt)
      (trans (exec-abstract-preserves-heap-ref (store-at-slot n) (floc u12) (falloc u12) tt)
      (trans (exec-abstract-preserves-heap-ref (load-from-slot ss) (floc u11) (falloc u11) tt)
      (trans (exec-abstract-preserves-heap-ref (store-at-slot vl) (floc u10) (falloc u10) tt)
      (trans (exec-abstract-preserves-heap-ref (load-from-slot ss) (floc u9) (falloc u9) tt)
      (trans (exec-abstract-preserves-heap-ref (store-at-slot ev) (floc u8) (falloc u8) tt)
      (trans (exec-abstract-preserves-heap-ref (load-from-slot ss) (floc u7) (falloc u7) tt)
      (trans (exec-abstract-preserves-heap-ref store-indirect (floc u6) (falloc u6) tt)
      (trans (exec-abstract-preserves-heap-ref (instr-load-tag-lit 0) (floc u5) (falloc u5) tt)
      (trans (exec-abstract-preserves-heap-ref mov-to-input (floc u4) (falloc u4) tt)
      (trans (exec-abstract-preserves-heap-ref (store-at-slot ss) (floc u3) (falloc u3) tt) hr3))))))))))

    sn-live : Live (falloc u14) (AtDynamic sn)
    sn-live = BeforeFrontier.heap-before (≤-reflexive (sym hr14))

    -- every slot from `c` on
    slots14 : ∀ j → c ≤ j → sl u14 j ≡ sl σ j
    slots14 j c≤j =
      trans (sl-keep (load-from-slot tmp) (floc u13) (falloc u13) f₀ j nhw-load-from-slot refl)
      (trans (sl-other n j (floc u12) (falloc u12) f₀ (far lt0 c≤j))
      (trans (sl-keep (load-from-slot ss) (floc u11) (falloc u11) f₀ j nhw-load-from-slot refl)
      (trans (sl-other vl j (floc u10) (falloc u10) f₀ (far lt2 c≤j))
      (trans (sl-keep (load-from-slot ss) (floc u9) (falloc u9) f₀ j nhw-load-from-slot refl)
      (trans (sl-other ev j (floc u8) (falloc u8) f₀ (far lt1 c≤j))
      (trans (sl-keep (load-from-slot ss) (floc u7) (falloc u7) f₀ j nhw-load-from-slot refl)
      (trans (sl-sind (floc u6) (falloc u6) sn f₀ j rdi7)
      (trans (sl-keep (instr-load-tag-lit 0) (floc u5) (falloc u5) f₀ j nhw-instr-load-tag-lit refl)
      (trans (sl-keep mov-to-input (floc u4) (falloc u4) f₀ j nhw-mov-to-input refl)
      (trans (sl-other ss j (floc u3) (falloc u3) f₀ (far lt6 c≤j))
      (trans (sl-keep (instr-alloc-heap 2) (floc u2) (falloc u2) f₀ j nhw-instr-alloc-heap refl)
      (trans (sl-other tmp j (floc u1) (falloc u1) f₀ (far lt3 c≤j))
             (sl-keep mov-to-output s₀ a₀ f₀ j nhw-mov-to-output refl)))))))))))))

    ------------------------------------------------------------------
    -- THE FOURTEEN ROWS, silent.
    ------------------------------------------------------------------
    runA : SRun prog 7 σ u7
    runA =
      s-at u1 (nh0 , span 0 _ refl) refl refl tt (
      s-at u2 (nh1 , span 1 _ refl) refl refl tt (
      s-at u3 (nh2 , span 2 _ refl) refl refl tt (
      s-at u4 (nh3 , span 3 _ refl) refl refl tt (
      s-at u5 (nh4 , span 4 _ refl) refl refl tt (
      s-at u6 (nh5 , span 5 _ refl) refl refl tt (
      s-at u7 (nh6 , span 6 _ refl) refl refl tt s-nil))))))

    runB : SRun prog 7 u7 u14
    runB =
      s-at u8 (nh7 , span 7 _ refl) refl refl tt (
      s-at u9 (nh8 , span 8 _ refl) refl refl tt (
      s-at u10 (nh9 , span 9 _ refl) refl refl tt (
      s-at u11 (nh10 , span 10 _ refl) refl refl tt (
      s-at u12 (nh11 , span 11 _ refl) refl refl tt (
      s-at u13 (nh12 , span 12 _ refl) refl refl tt (
      s-at u14 (nh13 , span 13 _ refl) refl refl tt s-nil))))))

    abstract
      segA : SegA a₀ n σ u7
      segA =
        segA-∘ (seg-q mov-to-output σ nhw-mov-to-output refl tt tt)
        (segA-∘ (seg-store tmp u1 cf1 (m≤m+n n 3))
        (segA-∘ (seg-alloc u2)
        (segA-∘ (seg-store ss u3 cf3 (m≤m+n n 6))
        (segA-∘ (seg-q mov-to-input u4 nhw-mov-to-input refl tt tt)
        (segA-∘ (seg-q (instr-load-tag-lit 0) u5 nhw-instr-load-tag-lit refl tt tt)
                (seg-sind u6 sn rdi7 ≤-refl))))))

      segB : SegA a₀ n u7 u14
      segB =
        segA-∘ (seg-q (load-from-slot ss) u7 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-store ev u8 cf8 (n≤1+n n))
        (segA-∘ (seg-q (load-from-slot ss) u9 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-store vl u10 cf10 (m≤m+n n 2))
        (segA-∘ (seg-q (load-from-slot ss) u11 nhw-load-from-slot refl tt tt)
        (segA-∘ (seg-store n u12 cf12 ≤-refl)
                (seg-q (load-from-slot tmp) u13 nhw-load-from-slot refl tt tt))))))

      seg14 : SegA a₀ n σ u14
      seg14 = segA-∘ segA segB

    kp14 : Kp a₀ s₀ (falloc u14) (floc u14)
    kp14 = seg-kp seg14

    w14 : Walk prog n (KI c) σ (14 + fpc σ) (λ _ → ⊤)
    w14 = record
      { τ = u14 ; steps = 14 ; run = s-++ {prog} {7} {7} {σ} {u7} {u14} runA runB ; seg = seg14 ; nh = nh14 ; pc = refl
      ; ret = refl ; clo = refl ; lnk = refl ; cf = cf14 ; slots = slots14 ; post = tt }

    ------------------------------------------------------------------
    -- …and the push of the root.
    ------------------------------------------------------------------
    NE = NodeE prog F
    VE = ValE prog C

    empty : ∀ {V : Set} {E : ElemP V} {k : ℕ} → sl u14 k ≡ just psn → StackAt E (falloc u14) (floc u14) k sn []
    empty r = stack-at sn (at-cf (floc u14) (falloc u14) cf14 r) ch-nil sent14 sn-live

    ex14 : NE (falloc u14) (floc u14) root (Oup u14)
    ex14 = subst (λ z → WordAt prog (falloc u14) (μ-type F) root z (floc u14)) (sym out14) (word-tr kp14 wd)

    pu : Push2Out NE prog n n (n + 4) (n + 5) sn u14 root []
    pu = push2-run NE node-tr prog n n (n + 4) (n + 5) sn u14 root []
           (span-drop prog (init-rows n) {push2 n (n + 4) (n + 5)} (fpc σ) span) nh14
           ≤-refl (m≤m+n n 4) (m≤m+n n 5) n≢4 n≢5 4≢5 ex14 (empty {k = n} td14)

    τ = Push2Out.τ pu
    kpp : Kp (falloc u14) (floc u14) (falloc τ) (floc τ)
    kpp = seg-kp (Push2Out.seg pu)

    keep-k : ∀ {V : Set} {E : ElemP V} → ETr E → ∀ {k} → k ≢ n → k ≢ n + 4 → k ≢ n + 5
           → StackAt E (falloc u14) (floc u14) k sn [] → StackAt E (falloc τ) (floc τ) k sn []
    keep-k et a b c′ st = stack-keep et kpp (Push2Out.cf pu) (Push2Out.slots pu _ a b c′) st

    iq : InitQ prog F C n sn root τ
    iq = record
      { todo = Push2Out.stack pu
      ; eval = keep-k node-tr s≢n s≢4 s≢5 (empty {k = ev} ev14)
      ; val  = keep-k val-tr (λ e → off0-≢ {2} (λ ()) (sym e)) (off-≢ (λ ())) (off-≢ (λ ())) (empty {k = vl} vl14) }

    abstract
      out : Walk prog n (KI c) σ (24 + fpc σ) (InitQ prog F C n sn root)
      out = walk-∘ {prog} {n} {KI c} {σ} w14
              (walk-post (push-walk (λ j c≤j → far lt0 c≤j , far lt4 c≤j , far lt5 c≤j) pu) iq)
