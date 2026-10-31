-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.SumTail
--
-- plan 0.135 S3: the nine rows that end each arm of a sum layer's
-- re-suspension — a FRESH two-cell node `[tag , payload]`, the payload the
-- arm's re-suspended result (stashed at slot `n + 2`), its pointer back in
-- Output (via slot `n + 1`):
--
--   store-at-slot tmp ∷ instr-alloc-heap 2 ∷ store-at-slot dst ∷ mov-to-input ∷
--   load-from-slot tmp ∷ store-indirect-suc ∷ instr-load-tag-lit tag ∷
--   store-indirect ∷ load-from-slot dst ∷ []
--
-- It writes only the node it allocates, so everything live at its start —
-- and everything below any base no later than that — reads the same after.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.SumTail (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Ptr; SV-Tag
        ; store-at-slot; load-from-slot; store-indirect; store-indirect-suc; mov-to-input
        ; instr-alloc-heap; instr-load-tag-lit; sv-as-loc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL)

module ResuspSumTailC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  private
    cfx : ∀ i (t : FlatState) → current-frame (falloc (St i t)) ≡ current-frame (falloc t)
    cfx i t = exec-abstract-preserves-frame i (floc t) (falloc t)

    sfx : ∀ i (t : FlatState) → saved-frames (falloc (St i t)) ≡ saved-frames (falloc t)
    sfx i t = exec-abstract-preserves-saved i (floc t) (falloc t)

  tail9 : ℕ → ℕ → AbstractTrace
  tail9 n tag = store-at-slot (suc (suc n)) ∷ instr-alloc-heap 2 ∷ store-at-slot (suc n) ∷ mov-to-input ∷
                load-from-slot (suc (suc n)) ∷ store-indirect-suc ∷ instr-load-tag-lit tag ∷ store-indirect ∷
                load-from-slot (suc n) ∷ []

  module Tail (n tag : ℕ) (prog : AbstractTrace) (fs : FlatState) (f₀ : _)
              (cf : current-frame (falloc fs) ≡ f₀) (nh : halted (floc fs) ≡ false)
              {rest : AbstractTrace} (sp : SpanAt prog (fpc fs) (tail9 n tag ++ rest)) where

    dst tmp : ℕ
    dst = suc n
    tmp = suc dst

    r : StoredValue FS
    r = readReg (regs (floc fs)) Output

    ohl : HeapLocation
    ohl = heap-loc (mkHeapRef (next-heap-ref (falloc fs))) 0

    w1 w2 w3 w4 w5 w6 w7 w8 w9 : FlatState
    w1 = St (store-at-slot tmp) fs
    w2 = St (instr-alloc-heap 2) w1
    w3 = St (store-at-slot dst) w2
    w4 = St mov-to-input w3
    w5 = St (load-from-slot tmp) w4
    w6 = St store-indirect-suc w5
    w7 = St (instr-load-tag-lit tag) w6
    w8 = St store-indirect w7
    w9 = St (load-from-slot dst) w8

    cfw1 : current-frame (falloc w1) ≡ f₀
    cfw1 = trans (cfx (store-at-slot tmp) fs) cf
    cfw2 : current-frame (falloc w2) ≡ f₀
    cfw2 = trans (cfx (instr-alloc-heap 2) w1) cfw1
    cfw3 : current-frame (falloc w3) ≡ f₀
    cfw3 = trans (cfx (store-at-slot dst) w2) cfw2
    cfw4 : current-frame (falloc w4) ≡ f₀
    cfw4 = trans (cfx mov-to-input w3) cfw3
    cfw5 : current-frame (falloc w5) ≡ f₀
    cfw5 = trans (cfx (load-from-slot tmp) w4) cfw4
    cfw6 : current-frame (falloc w6) ≡ f₀
    cfw6 = trans (cfx store-indirect-suc w5) cfw5
    cfw7 : current-frame (falloc w7) ≡ f₀
    cfw7 = trans (cfx (instr-load-tag-lit tag) w6) cfw6
    cfw8 : current-frame (falloc w8) ≡ f₀
    cfw8 = trans (cfx store-indirect w7) cfw7
    cfw9 : current-frame (falloc w9) ≡ f₀
    cfw9 = trans (cfx (load-from-slot dst) w8) cfw8

    ne-tmp-dst : tmp ≢ dst
    ne-tmp-dst eq = <-irrefl (sym eq) (n<1+n dst)

    stw1 : readLoc (floc w1) (AtStack f₀ tmp) ≡ just r
    stw1 = sl-same tmp (floc fs) (falloc fs) f₀ cf
    stw2 : readLoc (floc w2) (AtStack f₀ tmp) ≡ just r
    stw2 = trans (sl-keep (instr-alloc-heap 2) (floc w1) (falloc w1) f₀ tmp nhw-instr-alloc-heap refl) stw1
    stw3 : readLoc (floc w3) (AtStack f₀ tmp) ≡ just r
    stw3 = trans (sl-other dst tmp (floc w2) (falloc w2) f₀ ne-tmp-dst) stw2
    stw4 : readLoc (floc w4) (AtStack f₀ tmp) ≡ just r
    stw4 = trans (sl-keep mov-to-input (floc w3) (falloc w3) f₀ tmp nhw-mov-to-input refl) stw3

    outw2 : readReg (regs (floc w2)) Output ≡ SV-Ptr (AtDynamic ohl)
    outw2 = out-alloc 2 (floc w1) (falloc w1)

    sdw3 : readLoc (floc w3) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
    sdw3 = trans (sl-same dst (floc w2) (falloc w2) f₀ cfw2) (cong just outw2)
    sdw4 : readLoc (floc w4) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
    sdw4 = trans (sl-keep mov-to-input (floc w3) (falloc w3) f₀ dst nhw-mov-to-input refl) sdw3
    sdw5 : readLoc (floc w5) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
    sdw5 = trans (sl-keep (load-from-slot tmp) (floc w4) (falloc w4) f₀ dst nhw-load-from-slot refl) sdw4

    inw4 : readReg (regs (floc w4)) Input1 ≡ SV-Ptr (AtDynamic ohl)
    inw4 = trans (in-movin (floc w3) (falloc w3)) (trans (reg-store dst (floc w2) (falloc w2) Output) outw2)

    outw5 : readReg (regs (floc w5)) Output ≡ r
    outw5 = out-lslot tmp (floc w4) (falloc w4) r (at-cf (floc w4) (falloc w4) cfw4 stw4)

    inw5 : readReg (regs (floc w5)) Input1 ≡ SV-Ptr (AtDynamic ohl)
    inw5 = trans (in-lslot tmp (floc w4) (falloc w4) r (at-cf (floc w4) (falloc w4) cfw4 stw4)) inw4

    rdiw5 : sv-as-loc (readReg (regs (floc w5)) Input1) ≡ just (AtDynamic ohl)
    rdiw5 = cong sv-as-loc inw5

    hsw6 : readLoc (floc w6) (AtDynamic (sucHL ohl)) ≡ just r
    hsw6 = trans (store-ind-suc-result (floc w5) (falloc w5) ohl rdiw5) (cong just outw5)

    inw7 : readReg (regs (floc w7)) Input1 ≡ SV-Ptr (AtDynamic ohl)
    inw7 = trans (in-tag tag (floc w6) (falloc w6)) (trans (in-sind-suc (floc w5) (falloc w5) _ rdiw5) inw5)

    rdiw7 : sv-as-loc (readReg (regs (floc w7)) Input1) ≡ just (AtDynamic ohl)
    rdiw7 = cong sv-as-loc inw7

    how8 : readLoc (floc w8) (AtDynamic ohl) ≡ just (SV-Tag tag)
    how8 = trans (store-ind-result (floc w7) (falloc w7) ohl rdiw7) (cong just (out-tag tag (floc w6) (falloc w6)))

    hsw7 : readLoc (floc w7) (AtDynamic (sucHL ohl)) ≡ just r
    hsw7 = trans (hp-keep (instr-load-tag-lit tag) (floc w6) (falloc w6) (sucHL ohl) nhw-instr-load-tag-lit) hsw6
    hsw8 : readLoc (floc w8) (AtDynamic (sucHL ohl)) ≡ just r
    hsw8 = trans (hp-sind-other (floc w7) (falloc w7) ohl (sucHL ohl) rdiw7 (λ eq → sucHL-≢ ohl (sym eq))) hsw7

    hsw9 : readLoc (floc w9) (AtDynamic (sucHL ohl)) ≡ just r
    hsw9 = trans (hp-keep (load-from-slot dst) (floc w8) (falloc w8) (sucHL ohl) nhw-load-from-slot) hsw8
    how9 : readLoc (floc w9) (AtDynamic ohl) ≡ just (SV-Tag tag)
    how9 = trans (hp-keep (load-from-slot dst) (floc w8) (falloc w8) ohl nhw-load-from-slot) how8

    sdw6 : readLoc (floc w6) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
    sdw6 = trans (sl-sind-suc (floc w5) (falloc w5) ohl f₀ dst rdiw5) sdw5
    sdw7 : readLoc (floc w7) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
    sdw7 = trans (sl-keep (instr-load-tag-lit tag) (floc w6) (falloc w6) f₀ dst nhw-instr-load-tag-lit refl) sdw6
    sdw8 : readLoc (floc w8) (AtStack f₀ dst) ≡ just (SV-Ptr (AtDynamic ohl))
    sdw8 = trans (sl-sind (floc w7) (falloc w7) ohl f₀ dst rdiw7) sdw7

    outw9 : readReg (regs (floc w9)) Output ≡ SV-Ptr (AtDynamic ohl)
    outw9 = out-lslot dst (floc w8) (falloc w8) _ (at-cf (floc w8) (falloc w8) cfw8 sdw8)

    hrw9 : next-heap-ref (falloc w9) ≡ suc (next-heap-ref (falloc fs))
    hrw9 =
      trans (exec-abstract-preserves-heap-ref (load-from-slot dst) (floc w8) (falloc w8) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect (floc w7) (falloc w7) tt)
     (trans (exec-abstract-preserves-heap-ref (instr-load-tag-lit tag) (floc w6) (falloc w6) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc w5) (falloc w5) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot tmp) (floc w4) (falloc w4) tt)
     (trans (exec-abstract-preserves-heap-ref mov-to-input (floc w3) (falloc w3) tt)
            (exec-abstract-preserves-heap-ref (store-at-slot dst) (floc w2) (falloc w2) tt))))))

    -- the node is below the frontier the tail leaves
    o< : next-heap-ref (falloc fs) < next-heap-ref (falloc w9)
    o< = subst (next-heap-ref (falloc fs) <_) (sym hrw9) (n<1+n _)

    n≤tmp : n ≤ tmp
    n≤tmp = ≤-trans (n≤1+n n) (n≤1+n dst)

    -- what the tail leaves alone, measured against any base the node is
    -- fresh for
    module TMem (c : AllocState {FS}) (cfc : current-frame c ≡ f₀)
                (hrc : next-heap-ref c ≤ next-heap-ref (falloc fs)) where
      c-n : AllocState {FS}
      c-n = record c { next-slot = n }

      tm1 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w1) loc ≡ readLoc (floc fs) loc
      tm1 loc bf = store-slot-preserves-before tmp (floc fs) c-n (falloc fs) loc (trans cf (sym cfc)) n≤tmp bf
      tm2 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w2) loc ≡ readLoc (floc fs) loc
      tm2 loc bf = trans (mem-untouched (instr-alloc-heap 2) (floc w1) (falloc w1) loc nhw-instr-alloc-heap refl) (tm1 loc bf)
      tm3 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w3) loc ≡ readLoc (floc fs) loc
      tm3 loc bf = trans (store-slot-preserves-before dst (floc w2) c-n (falloc w2) loc (trans cfw2 (sym cfc)) (n≤1+n n) bf) (tm2 loc bf)
      tm4 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w4) loc ≡ readLoc (floc fs) loc
      tm4 loc bf = trans (mem-untouched mov-to-input (floc w3) (falloc w3) loc nhw-mov-to-input refl) (tm3 loc bf)
      tm5 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w5) loc ≡ readLoc (floc fs) loc
      tm5 loc bf = trans (mem-untouched (load-from-slot tmp) (floc w4) (falloc w4) loc nhw-load-from-slot refl) (tm4 loc bf)
      tm6 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w6) loc ≡ readLoc (floc fs) loc
      tm6 loc bf = trans (store-ind-suc-preserves-before (floc w5) c-n (falloc w5) ohl loc rdiw5 hrc bf) (tm5 loc bf)
      tm7 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w7) loc ≡ readLoc (floc fs) loc
      tm7 loc bf = trans (mem-untouched (instr-load-tag-lit tag) (floc w6) (falloc w6) loc nhw-instr-load-tag-lit refl) (tm6 loc bf)
      tm8 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w8) loc ≡ readLoc (floc fs) loc
      tm8 loc bf = trans (store-ind-preserves-before (floc w7) c-n (falloc w7) ohl loc rdiw7 hrc bf) (tm7 loc bf)
      tm9 : ∀ loc → BeforeFrontier c-n loc → readLoc (floc w9) loc ≡ readLoc (floc fs) loc
      tm9 loc bf = trans (mem-untouched (load-from-slot dst) (floc w8) (falloc w8) loc nhw-load-from-slot refl) (tm8 loc bf)

      seg : SegA c n fs w9
      seg = record
        { mem  = tm9
        ; cf   = trans cfw9 (sym cf)
        ; sf   = trans (sfx (load-from-slot dst) w8) (trans (sfx store-indirect w7)
                 (trans (sfx (instr-load-tag-lit tag) w6) (trans (sfx store-indirect-suc w5)
                 (trans (sfx (load-from-slot tmp) w4) (trans (sfx mov-to-input w3)
                 (trans (sfx (store-at-slot dst) w2) (trans (sfx (instr-alloc-heap 2) w1)
                        (sfx (store-at-slot tmp) fs))))))))
        ; ns   = trans (exec-abstract-preserves-next-slot (load-from-slot dst) (floc w8) (falloc w8) tt)
                 (trans (exec-abstract-preserves-next-slot store-indirect (floc w7) (falloc w7) tt)
                 (trans (exec-abstract-preserves-next-slot (instr-load-tag-lit tag) (floc w6) (falloc w6) tt)
                 (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc w5) (falloc w5) tt)
                 (trans (exec-abstract-preserves-next-slot (load-from-slot tmp) (floc w4) (falloc w4) tt)
                 (trans (exec-abstract-preserves-next-slot mov-to-input (floc w3) (falloc w3) tt)
                 (trans (exec-abstract-preserves-next-slot (store-at-slot dst) (floc w2) (falloc w2) tt)
                 (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc w1) (falloc w1) tt)
                        (exec-abstract-preserves-next-slot (store-at-slot tmp) (floc fs) (falloc fs) tt))))))))
        ; href = ≤-trans (n≤1+n _) o<
        }

    nhw1 : halted (floc w1) ≡ false
    nhw1 = exec-abstract-preserves-halted-WF (store-at-slot tmp) (floc fs) (falloc fs) nh tt
    nhw2 : halted (floc w2) ≡ false
    nhw2 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc w1) (falloc w1) nhw1 tt
    nhw3 : halted (floc w3) ≡ false
    nhw3 = exec-abstract-preserves-halted-WF (store-at-slot dst) (floc w2) (falloc w2) nhw2 tt
    nhw4 : halted (floc w4) ≡ false
    nhw4 = exec-abstract-preserves-halted-WF mov-to-input (floc w3) (falloc w3) nhw3 tt
    nhw5 : halted (floc w5) ≡ false
    nhw5 = exec-abstract-preserves-halted-WF (load-from-slot tmp) (floc w4) (falloc w4) nhw4 (_ , at-cf (floc w4) (falloc w4) cfw4 stw4)
    nhw6 : halted (floc w6) ≡ false
    nhw6 = exec-abstract-preserves-halted-WF store-indirect-suc (floc w5) (falloc w5) nhw5 (_ , rdiw5)
    nhw7 : halted (floc w7) ≡ false
    nhw7 = exec-abstract-preserves-halted-WF (instr-load-tag-lit tag) (floc w6) (falloc w6) nhw6 tt
    nhw8 : halted (floc w8) ≡ false
    nhw8 = exec-abstract-preserves-halted-WF store-indirect (floc w7) (falloc w7) nhw7 (_ , rdiw7)
    nhw9 : halted (floc w9) ≡ false
    nhw9 = exec-abstract-preserves-halted-WF (load-from-slot dst) (floc w8) (falloc w8) nhw8 (_ , at-cf (floc w8) (falloc w8) cfw8 sdw8)

    sr : SRun prog 9 fs w9
    sr =
      s-at w1 (nh , sp 0 _ refl) refl refl tt (
      s-at w2 (nhw1 , sp 1 _ refl) refl refl tt (
      s-at w3 (nhw2 , sp 2 _ refl) refl refl tt (
      s-at w4 (nhw3 , sp 3 _ refl) refl refl tt (
      s-at w5 (nhw4 , sp 4 _ refl) refl refl tt (
      s-at w6 (nhw5 , sp 5 _ refl) refl refl tt (
      s-at w7 (nhw6 , sp 6 _ refl) refl refl tt (
      s-at w8 (nhw7 , sp 7 _ refl) refl refl tt (
      s-at w9 (nhw8 , sp 8 _ refl) refl refl tt (
      s-nil)))))))))

    run : FlatSteps prog 9 fs w9
    run = proj₁ sr

    ev : chain-events run ≡ []
    ev = proj₁ (proj₂ sr)

    log : LocState.ev-log (floc w9) ≡ LocState.ev-log (floc fs)
    log = proj₂ (proj₂ sr)
