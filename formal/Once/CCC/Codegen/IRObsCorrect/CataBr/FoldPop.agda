-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldPop   (plan 0.135 S3, cata M4 stage D1b)
--
-- THE FOLD LOOP'S HEAD (`FoldText.fold-hd`, eight rows), from the fold head
-- `ℓ (l1+2)` with eval `ns` and val `vs`:
--
--     ℓ (l1+2) · load eval · mov-to-input · branch-tag-zero ℓ (l1+3)
--     load-indirect-suc · store eval · load-indirect · mov-to-input
--
--   * `Exit.out` (eval empty): the branch finds the sentinel's tag and jumps
--     to the exit label; val unchanged.
--   * `Pop.out` (eval `t ∷ ns`): the branch falls through, eval := `ns`,
--     `Input1` := the node's word.
--
-- Both are silent `Walk`s keeping every slot but eval's (`suc n`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldPop (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText o tbl using (fold-hd)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; sv-as-loc; store-at-slot; load-from-slot; load-indirect; load-indirect-suc; mov-to-input
        ; instr-ctrl; c-branch-tag-zero; c-label; writeReg-preserves)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.IRTy using (IRTy; IRFunctor; μ-type)
open import Data.Unit using (⊤)

module CataFoldPopC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open FlatStepsAPI {FS} using (flat-tag-branch-yes; flat-tag-branch-not)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  -- the slots the head keeps: all but eval's
  KH : ℕ → ℕ → Set
  KH n j = j ≢ suc n

  module FoldHead (prog : AbstractTrace) (F : IRFunctor) (C : IRTy) (n l1 : ℕ) (sn : HeapLocation) (XE : ℕ)
                  (ex : find-label prog (ℓ o (l1 + 3)) ≡ just XE) where

    NE : ElemP ⟦ μ-type F ⟧
    NE = NodeE prog F
    VE : ElemP ⟦ C ⟧
    VE = ValE prog C

    hd8 : AbstractTrace
    hd8 = fold-hd n l1

    s≢2 : suc n ≢ n + 2
    s≢2 e = <-irrefl (trans e (+-comm n 2)) (n<1+n (suc n))

    module Head (σ : FlatState) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧) (span : SpanAt prog (fpc σ) hd8)
                (nh : halted (floc σ) ≡ false)
                (se : StackAt NE (falloc σ) (floc σ) (suc n) sn ns) (sv : StackAt VE (falloc σ) (floc σ) (n + 2) sn vs) where

      s₀ = floc σ
      a₀ = falloc σ
      f₀ = current-frame a₀
      tp = StackAt.top se

      h1 h2 h3 : FlatState
      h1 = record σ { fpc = suc (fpc σ) }
      h2 = St (load-from-slot (suc n)) h1
      h3 = St mov-to-input h2

      wf2 : InstrWF (floc h1) (falloc h1) (load-from-slot (suc n))
      wf2 = SV-Ptr (AtDynamic tp) , StackAt.slot se
      nh2 : halted (floc h2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (load-from-slot (suc n)) s₀ a₀ nh wf2
      nh3 : halted (floc h3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF mov-to-input (floc h2) (falloc h2) nh2 tt
      in3 : readReg (regs (floc h3)) Input1 ≡ SV-Ptr (AtDynamic tp)
      in3 = trans (in-movin (floc h2) (falloc h2)) (out-lslot (suc n) s₀ a₀ _ (StackAt.slot se))

      kp3 : Kp a₀ s₀ (falloc h3) (floc h3)
      kp3 = kp-∘ (kp-q (load-from-slot (suc n)) h1 nhw-load-from-slot refl tt tt) (kp-q mov-to-input h2 nhw-mov-to-input refl tt tt)
      cf3 : current-frame (falloc h3) ≡ f₀
      cf3 = trans (exec-abstract-preserves-frame mov-to-input (floc h2) (falloc h2))
                  (exec-abstract-preserves-frame (load-from-slot (suc n)) s₀ a₀)
      sl3 : ∀ j → readLoc (floc h3) (AtStack f₀ j) ≡ readLoc s₀ (AtStack f₀ j)
      sl3 j = trans (sl-keep mov-to-input (floc h2) (falloc h2) f₀ j nhw-mov-to-input refl)
                    (sl-keep (load-from-slot (suc n)) s₀ a₀ f₀ j nhw-load-from-slot refl)
      hk3 : ∀ hl → readLoc (floc h3) (AtDynamic hl) ≡ readLoc s₀ (AtDynamic hl)
      hk3 hl = trans (hp-keep mov-to-input (floc h2) (falloc h2) hl nhw-mov-to-input)
                     (hp-keep (load-from-slot (suc n)) s₀ a₀ hl nhw-load-from-slot)

      se3 : StackAt NE (falloc h3) (floc h3) (suc n) sn ns
      se3 = stack-keep node-tr kp3 cf3 (sl3 (suc n)) se
      sv3 : StackAt VE (falloc h3) (floc h3) (n + 2) sn vs
      sv3 = stack-keep val-tr kp3 cf3 (sl3 (n + 2)) sv

      cond : tag-zf (flat-read-tag (floc h3)) ≡ DL.null ns
      cond = stack-tag node-nz se3 in3

      walk : Walk prog n (KH n) σ (3 + fpc σ) (λ _ → ⊤)
      walk =
        walk-∘ {prog} {n} {KH n} {σ} (walk-ctrl {Q = λ _ → ⊤} σ (instr-ctrl (c-label (ℓ o (l1 + 2)))) (suc (fpc σ)) nh (span 0 _ refl) refl refl tt tt)
        (walk-∘ {prog} {n} {KH n} {h1} (walk-q {Q = λ _ → ⊤} h1 (load-from-slot (suc n)) refl nh (span 1 _ refl) wf2 nhw-load-from-slot refl tt tt refl tt tt)
                (walk-q {Q = λ _ → ⊤} h2 mov-to-input refl nh2 (span 2 _ refl) tt nhw-mov-to-input refl tt tt refl tt tt))

    --------------------------------------------------------------------
    -- THE EXIT: eval is empty, the branch jumps to `ℓ (l1+3)`.
    --------------------------------------------------------------------
    module Exit (σ : FlatState) (vs : List ⟦ C ⟧) (span : SpanAt prog (fpc σ) hd8) (nh : halted (floc σ) ≡ false)
                (se : StackAt NE (falloc σ) (floc σ) (suc n) sn []) (sv : StackAt VE (falloc σ) (floc σ) (n + 2) sn vs) where

      open Head σ [] vs span nh se sv

      wb : Walk prog n (KH n) h3 XE (λ τ → StackAt VE (falloc τ) (floc τ) (n + 2) sn vs)
      wb = walk-ctrl h3 (instr-ctrl (c-branch-tag-zero (ℓ o (l1 + 3)))) XE nh3 (span 3 _ refl)
             (trans (flat-tag-branch-yes prog h3 (ℓ o (l1 + 3)) cond) (cong (λ mj → do-jump mj h3) ex)) refl tt sv3

      abstract
        out : Walk prog n (KH n) σ XE (λ τ → StackAt VE (falloc τ) (floc τ) (n + 2) sn vs)
        out = walk-∘ {prog} {n} {KH n} {σ} walk wb

    --------------------------------------------------------------------
    -- THE POP: eval is `t ∷ ns`.
    --------------------------------------------------------------------
    record PopQ (t : ⟦ μ-type F ⟧) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧) (τ : FlatState) : Set where
      field
        eval : StackAt NE (falloc τ) (floc τ) (suc n) sn ns
        val  : StackAt VE (falloc τ) (floc τ) (n + 2) sn vs
        node : NE (falloc τ) (floc τ) t (readReg (regs (floc τ)) Input1)

    module Pop (σ : FlatState) (t : ⟦ μ-type F ⟧) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧)
               (span : SpanAt prog (fpc σ) hd8) (nh : halted (floc σ) ≡ false)
               (se : StackAt NE (falloc σ) (floc σ) (suc n) sn (t ∷ ns)) (sv : StackAt VE (falloc σ) (floc σ) (n + 2) sn vs) where

      open Head σ (t ∷ ns) vs span nh se sv

      data Top : Set where
        top-is : (w : StoredValue FS) (nb : HeapLocation)
               → readLoc s₀ (AtDynamic tp) ≡ just w → NE a₀ s₀ t w
               → readLoc s₀ (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb))
               → Chain NE a₀ s₀ sn nb ns → Top

      uncons : ∀ {b} → Chain NE a₀ s₀ sn b (t ∷ ns) → b ≡ tp → Top
      uncons (ch-cons w lv r0 e r1 ch) refl = top-is w _ r0 e r1 ch

      tp-cell : Top
      tp-cell = uncons (StackAt.chain se) refl

      module T (w : StoredValue FS) (nb : HeapLocation)
               (c0 : readLoc s₀ (AtDynamic tp) ≡ just w) (ew : NE a₀ s₀ t w)
               (c1 : readLoc s₀ (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb)))
               (rest : Chain NE a₀ s₀ sn nb ns) where

        h4 p1 p2 p3 p4 : FlatState
        h4 = record h3 { fpc = suc (fpc h3) }
        p1 = St load-indirect-suc h4
        p2 = St (store-at-slot (suc n)) p1
        p3 = St load-indirect p2
        p4 = St mov-to-input p3

        Inp Oup : FlatState → StoredValue FS
        Inp q = readReg (regs (floc q)) Input1
        Oup q = readReg (regs (floc q)) Output

        sl : FlatState → ℕ → Maybe (StoredValue FS)
        sl q j = readLoc (floc q) (AtStack f₀ j)

        c0-3 : readLoc (floc h3) (AtDynamic tp) ≡ just w
        c0-3 = trans (hk3 tp) c0
        c1-3 : readLoc (floc h3) (AtDynamic (sucHL tp)) ≡ just (SV-Ptr (AtDynamic nb))
        c1-3 = trans (hk3 (sucHL tp)) c1

        wf-p1 : InstrWF (floc h4) (falloc h4) load-indirect-suc
        wf-p1 = AtDynamic tp , cong sv-as-loc in3 , SV-Ptr (AtDynamic nb) , c1-3
        nh-p1 : halted (floc p1) ≡ false
        nh-p1 = exec-abstract-preserves-halted-WF load-indirect-suc (floc h4) (falloc h4) nh3 wf-p1
        out-p1 : Oup p1 ≡ SV-Ptr (AtDynamic nb)
        out-p1 = out-lind-suc (floc h4) (falloc h4) (AtDynamic tp) _ in3 c1-3
        in-p1 : Inp p1 ≡ SV-Ptr (AtDynamic tp)
        in-p1 = trans (load-ind-suc-preserves-input (floc h4) (falloc h4) (AtDynamic tp) _ (cong sv-as-loc in3) c1-3) in3
        cf-p1 : current-frame (falloc p1) ≡ f₀
        cf-p1 = trans (exec-abstract-preserves-frame load-indirect-suc (floc h4) (falloc h4)) cf3

        nh-p2 : halted (floc p2) ≡ false
        nh-p2 = exec-abstract-preserves-halted-WF (store-at-slot (suc n)) (floc p1) (falloc p1) nh-p1 tt
        ev-p2 : sl p2 (suc n) ≡ just (SV-Ptr (AtDynamic nb))
        ev-p2 = trans (sl-same (suc n) (floc p1) (falloc p1) f₀ cf-p1) (cong just out-p1)
        in-p2 : Inp p2 ≡ SV-Ptr (AtDynamic tp)
        in-p2 = trans (reg-store (suc n) (floc p1) (falloc p1) Input1) in-p1
        cf-p2 : current-frame (falloc p2) ≡ f₀
        cf-p2 = trans (exec-abstract-preserves-frame (store-at-slot (suc n)) (floc p1) (falloc p1)) cf-p1

        c0-p2 : readLoc (floc p2) (AtDynamic tp) ≡ just w
        c0-p2 = trans (hp-keep (store-at-slot (suc n)) (floc p1) (falloc p1) tp nhw-store-at-slot)
                      (trans (hp-keep load-indirect-suc (floc h4) (falloc h4) tp nhw-load-indirect-suc) c0-3)

        wf-p3 : InstrWF (floc p2) (falloc p2) load-indirect
        wf-p3 = AtDynamic tp , cong sv-as-loc in-p2 , w , c0-p2
        nh-p3 : halted (floc p3) ≡ false
        nh-p3 = exec-abstract-preserves-halted-WF load-indirect (floc p2) (falloc p2) nh-p2 wf-p3
        out-p3 : Oup p3 ≡ w
        out-p3 = out-lind (floc p2) (falloc p2) (AtDynamic tp) w in-p2 c0-p2
        ev-p3 : sl p3 (suc n) ≡ just (SV-Ptr (AtDynamic nb))
        ev-p3 = trans (sl-keep load-indirect (floc p2) (falloc p2) f₀ (suc n) nhw-load-indirect refl) ev-p2
        cf-p3 : current-frame (falloc p3) ≡ f₀
        cf-p3 = trans (exec-abstract-preserves-frame load-indirect (floc p2) (falloc p2)) cf-p2

        nh-p4 : halted (floc p4) ≡ false
        nh-p4 = exec-abstract-preserves-halted-WF mov-to-input (floc p3) (falloc p3) nh-p3 tt
        in-p4 : Inp p4 ≡ w
        in-p4 = trans (in-movin (floc p3) (falloc p3)) out-p3
        ev-p4 : sl p4 (suc n) ≡ just (SV-Ptr (AtDynamic nb))
        ev-p4 = trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ (suc n) nhw-mov-to-input refl) ev-p3
        cf-p4 : current-frame (falloc p4) ≡ f₀
        cf-p4 = trans (exec-abstract-preserves-frame mov-to-input (floc p3) (falloc p3)) cf-p3

        -- every slot but eval
        slots4 : ∀ j → j ≢ suc n → sl p4 j ≡ sl σ j
        slots4 j j≢s =
          trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ j nhw-mov-to-input refl)
          (trans (sl-keep load-indirect (floc p2) (falloc p2) f₀ j nhw-load-indirect refl)
          (trans (sl-other (suc n) j (floc p1) (falloc p1) f₀ j≢s)
          (trans (sl-keep load-indirect-suc (floc h4) (falloc h4) f₀ j nhw-load-indirect-suc refl) (sl3 j))))

        runA : SRun prog 8 σ p4
        runA =
          s-at h1 (nh , span 0 _ refl) refl refl tt (
          s-at h2 (nh , span 1 _ refl) refl refl tt (
          s-at h3 (nh2 , span 2 _ refl) refl refl tt (
          s-at h4 (nh3 , span 3 _ refl) (flat-tag-branch-not prog h3 (ℓ o (l1 + 3)) cond) refl tt (
          s-at p1 (nh3 , span 4 _ refl) refl refl tt (
          s-at p2 (nh-p1 , span 5 _ refl) refl refl tt (
          s-at p3 (nh-p2 , span 6 _ refl) refl refl tt (
          s-at p4 (nh-p3 , span 7 _ refl) refl refl tt s-nil)))))))

        abstract
          segA : SegA a₀ n σ p4
          segA =
            segA-∘ (seg-ctrl′ σ (suc (fpc σ)))
            (segA-∘ (seg-q (load-from-slot (suc n)) h1 nhw-load-from-slot refl tt tt)
            (segA-∘ (seg-q mov-to-input h2 nhw-mov-to-input refl tt tt)
            (segA-∘ (seg-ctrl′ h3 (suc (fpc h3)))
            (segA-∘ (seg-q load-indirect-suc h4 nhw-load-indirect-suc refl tt tt)
            (segA-∘ (seg-store (suc n) p1 cf-p1 (n≤1+n n))
            (segA-∘ (seg-q load-indirect p2 nhw-load-indirect refl tt tt)
                    (seg-q mov-to-input p3 nhw-mov-to-input refl tt tt)))))))
            where
              seg-ctrl′ : ∀ (t : FlatState) (k : ℕ) → SegA a₀ n t (record t { fpc = k })
              seg-ctrl′ t k = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }

        kp4 : Kp a₀ s₀ (falloc p4) (floc p4)
        kp4 = seg-kp segA

        post : PopQ t ns vs p4
        post = record
          { eval = stack-at nb (at-cf (floc p4) (falloc p4) cf-p4 ev-p4) (chain-tr node-tr kp4 rest)
                     (trans (proj₂ kp4 _ (StackAt.sent-live se)) (StackAt.sent se)) (proj₁ kp4 _ (StackAt.sent-live se))
          ; val = stack-keep val-tr kp4 cf-p4 (slots4 (n + 2) (λ e → s≢2 (sym e))) sv
          ; node = subst (λ z → WordAt prog (falloc p4) (μ-type F) t z (floc p4)) (sym in-p4) (word-tr kp4 ew) }

        result : Walk prog n (KH n) σ (8 + fpc σ) (PopQ t ns vs)
        result = record
          { τ = p4 ; steps = 8 ; run = runA ; seg = segA ; nh = nh-p4 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl
          ; cf = cf-p4 ; slots = slots4 ; post = post }

      abstract
        out : Walk prog n (KH n) σ (8 + fpc σ) (PopQ t ns vs)
        out with tp-cell
        ... | top-is w nb c0 ew c1 rest = T.result w nb c0 ew c1 rest
