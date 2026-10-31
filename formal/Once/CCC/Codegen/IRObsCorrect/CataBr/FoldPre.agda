-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldPre   (plan 0.125 S3, cata M4 stage D1b)
--
-- ONE FOLD ROUND UP TO ITS CALL, from the fold head (`FoldInv.HeadAt`
-- with eval `t ∷ ns`, val `vs`) to the `instr-call-closure` row, as one
-- abstract bundle (`PreOut`):
--
--   1. the head pops `t` (`FoldPop.Pop`);
--   2. the rebuild walk builds the layer `L` from the node's top layer and
--      the value stack (`Rebuild.rebuild`, premise
--      `fillI wf (μ-type F) C (μ-layer-val wf t) vs ≡ just (L , rest)`);
--   3. `mov-to-input` hands the layer word to the call;
--   4. the call's fourteen rows (M1's `CataConst.Call`, at the branching
--      call slot `c`): a FRESH pair `[env , layer]` in `Input1`, the closure
--      register the record `hc`.
--
-- Everything below the frontier `n` reads the same (`seg`); the stacks,
-- the call slots and the record's code cell are carried across.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldPre (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Call o tbl using (module CataCallC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning o using (μ-layer-val)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o using (fillI)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Rebuild o tbl using (module CataRebuildC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Round o tbl using (module CataRoundC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC; module SlotArith; module OffArith)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText o tbl using (module CataFoldTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldPop o tbl using (module CataFoldPopC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv o tbl using (module CataFoldInvC)
open import Once.CCC.Codegen.IRToTrace o using (fsize)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Code; mov-to-input)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (s≤s; z≤n; _*_)
open import Data.Nat.Properties using (+-monoʳ-<)
open import Data.Unit using (⊤)

module CataFoldPreC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} hiding (X)
  open CataStepsC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataCallC {FS} using (module Call; CallOut)
  open CataRebuildC {FS} using (module Rebuild)
  open CataRoundC {FS} using (μ-word)
  open CataBrTextC {FS} using (module Text)
  open CataFoldTextC {FS} using (module FoldAt)
  open CataFoldPopC {FS} using (module FoldHead; KH)
  open CataFoldInvC {FS} using (module Inv)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  -- WHAT THE ROUND HAS AT ITS CALL, as an opaque bundle.
  record PreOut (prog : AbstractTrace) (F : IRFunctor) (E C : IRTy) (n c bodyL Y : ℕ) (sn hc : HeapLocation)
                (e : ⟦ E ⟧) (env-sv : StoredValue FS) (σ : FlatState)
                (ns : List ⟦ μ-type F ⟧) (rest : List ⟦ C ⟧) (L : ⟦ ⟦ F ⟧TI C ⟧) : Set where
    field
      cs    : FlatState
      steps : ℕ
      run   : SRun prog steps σ cs
      seg   : SegA (falloc σ) n σ cs
      nh    : halted (floc cs) ≡ false
      pc    : fpc cs ≡ 14 + Y
      ret   : fret cs ≡ fret σ
      clo   : fclosure cs ≡ SV-Ptr (AtDynamic hc)
      code  : readLoc (floc cs) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o bodyL))
      hc-lt : suc (ref-id (heap-ref hc)) ≤ next-heap-ref (falloc cs)
      ns0   : next-slot (falloc cs) ≡ 0
      hp    : HeapLocation
      hp-lt : suc (ref-id (heap-ref hp)) ≤ next-heap-ref (falloc cs)
      inp   : readReg (regs (floc cs)) Input1 ≡ SV-Ptr (AtDynamic hp)
      hp0   : readLoc (floc cs) (AtDynamic hp) ≡ just env-sv
      lw    : StoredValue FS
      shp   : readLoc (floc cs) (AtDynamic (sucHL hp)) ≡ just lw
      layer : WordAt prog (falloc cs) (⟦ F ⟧TI C) L lw (floc cs)
      env   : WordAt prog (falloc cs) E e env-sv (floc cs)
      eval  : StackAt (NodeE prog F) (falloc cs) (floc cs) (suc n) sn ns
      val   : StackAt (ValE prog C) (falloc cs) (floc cs) (n + 2) sn rest
      cl    : readLoc (floc cs) (AtStack (current-frame (falloc cs)) c) ≡ just (SV-Ptr (AtDynamic hc))
      ev    : readLoc (floc cs) (AtStack (current-frame (falloc cs)) (c + 2)) ≡ just env-sv

  module Pre (prog : AbstractTrace) {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
             (n l base : ℕ)
             (span : SpanAt prog base (Text.text′ wf alg n l))
             (la : LabelsAt prog base (Text.text′ wf alg n l))
             (sn hc : HeapLocation) (e : ⟦ E ⟧) (env-sv : StoredValue FS) where

    module FA = FoldAt wf alg n l prog base span la
    open FA using (X; Y; RL; lr; rbTxt; span-hd; span-rb; rb-labels; fetch-mti; span-call; exit-label)

    c bodyL l1 : ℕ
    c = FA.T.Pc.cslot
    bodyL = FA.T.Pc.bodyL
    l1 = FA.T.l1

    cb : n + 7 + 4 * fsize ⌈ F ⌉F ≤ c
    cb = m≤m+n (n + 7 + 4 * fsize ⌈ F ⌉F) 4

    n7≤c : n + 7 ≤ c
    n7≤c = ≤-trans (m≤m+n (n + 7) (4 * fsize ⌈ F ⌉F)) cb

    n≤c : n ≤ c
    n≤c = ≤-trans (m≤m+n n 7) n7≤c

    open SlotArith n c n7≤c
    open OffArith n

    open Inv prog F E C n c bodyL X sn hc e env-sv

    module FH = FoldHead prog F C n l1 sn (26 + Y) exit-label
    module RB = Rebuild prog F C n (n + 2) (n + 4) (n + 5) sn c (m≤m+n n 2)

    NE : ElemP ⟦ μ-type F ⟧
    NE = NodeE prog F
    VE : ElemP ⟦ C ⟧
    VE = ValE prog C

    -- the slots the round carries across its walks: the closure record's and the environment's
    K₀ : ℕ → Set
    K₀ j = (j ≡ c) ⊎ (j ≡ c + 2)

    k-c : ∀ j → K₀ j → c ≤ j
    k-c _ (inj₁ refl) = ≤-refl
    k-c _ (inj₂ refl) = m≤m+n c 2

    k-h : ∀ j → K₀ j → KH n j
    k-h j kj = far lt1 (k-c j kj)

    k-r : ∀ j → K₀ j → RB.KR (n + 7) j
    k-r j kj = inj₂ (k-c j kj) , far lt2 (k-c j kj)

    s≢2 : suc n ≢ n + 2
    s≢2 e = <-irrefl (trans e (+-comm n 2)) (n<1+n (suc n))

    module Go (σ : FlatState) (t : ⟦ μ-type F ⟧) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧)
              (L : ⟦ ⟦ F ⟧TI C ⟧) (rest : List ⟦ C ⟧)
              (fq : fillI wf (μ-type F) C (μ-layer-val wf t) vs ≡ just (L , rest))
              (h : HeadAt σ (t ∷ ns) vs) where

      module H = HeadAt h

      ------------------------------------------------------------------
      -- 1. the pop
      ------------------------------------------------------------------
      span-hd′ : SpanAt prog (fpc σ) FH.hd8
      span-hd′ = subst (λ b → SpanAt prog b FH.hd8) (sym H.pc) span-hd

      wP : Walk prog n (KH n) σ (8 + fpc σ) (FH.PopQ t ns vs)
      wP = FH.Pop.out σ t ns vs span-hd′ H.nh H.eval H.val

      τP : FlatState
      τP = Walk.τ wP
      module PQ = FH.PopQ (Walk.post wP)

      pcP : fpc τP ≡ 8 + X
      pcP = trans (Walk.pc wP) (cong (8 +_) H.pc)

      ------------------------------------------------------------------
      -- 2. the rebuild
      ------------------------------------------------------------------
      wR : Walk prog n (RB.KR (n + 7)) τP (RL + fpc τP) (RB.RQ (⟦ F ⟧TI C) L rest)
      wR = RB.rebuild wf (n + 7) lr τP (μ-layer-val wf t) vs L rest fq (m≤m+n n 7)
             (+-monoʳ-< n (s≤s (s≤s (s≤s z≤n)))) cb
             (subst (λ b → SpanAt prog b rbTxt) (sym pcP) span-rb)
             (subst (λ b → LabelsAt prog b rbTxt) (sym pcP) rb-labels)
             (Walk.nh wP) (μ-word wf PQ.node) PQ.val

      τR : FlatState
      τR = Walk.τ wR
      module RQ = RB.RQs (Walk.post wR)

      pcR : fpc τR ≡ RL + (8 + X)
      pcR = trans (Walk.pc wR) (cong (RL +_) pcP)

      evalR : StackAt NE (falloc τR) (floc τR) (suc n) sn ns
      evalR = stack-keep node-tr (walk-kp wR) (Walk.cf wR)
                (Walk.slots wR (suc n) (inj₁ (subst (_< n + 7) (sym suc-is) (+-monoʳ-< n (s≤s (s≤s z≤n)))) , s≢2)) PQ.eval

      ------------------------------------------------------------------
      -- 3. `mov-to-input`
      ------------------------------------------------------------------
      τM : FlatState
      τM = St mov-to-input τR

      wM : Walk prog n K₀ τR (suc (fpc τR)) (λ _ → ⊤)
      wM = walk-q τR mov-to-input refl (Walk.nh wR) (subst (λ z → fetch prog z ≡ just mov-to-input) (sym pcR) fetch-mti)
             tt nhw-mov-to-input refl tt tt refl tt tt

      kpM : Kp (falloc τR) (floc τR) (falloc τM) (floc τM)
      kpM = kp-q mov-to-input τR nhw-mov-to-input refl tt tt
      cfM : current-frame (falloc τM) ≡ current-frame (falloc τR)
      cfM = exec-abstract-preserves-frame mov-to-input (floc τR) (falloc τR)
      slM : ∀ j → readLoc (floc τM) (AtStack (current-frame (falloc τR)) j) ≡ readLoc (floc τR) (AtStack (current-frame (falloc τR)) j)
      slM j = sl-keep mov-to-input (floc τR) (falloc τR) _ j nhw-mov-to-input refl

      inM : readReg (regs (floc τM)) Input1 ≡ readReg (regs (floc τR)) Output
      inM = in-movin (floc τR) (falloc τR)

      ------------------------------------------------------------------
      -- the three walks, as one
      ------------------------------------------------------------------
      wA : Walk prog n K₀ σ (suc (fpc τR)) (λ _ → ⊤)
      wA = walk-∘ {prog} {n} {K₀} {σ} (walk-K k-h wP) (walk-∘ {prog} {n} {K₀} {τP} (walk-K k-r wR) wM)

      pcM : fpc τM ≡ Y
      pcM = cong suc pcR

      cfA : current-frame (falloc τM) ≡ current-frame (falloc σ)
      cfA = Walk.cf wA

      slotA : ∀ j → K₀ j → readLoc (floc τM) (AtStack (current-frame (falloc τM)) j) ≡ readLoc (floc σ) (AtStack (current-frame (falloc σ)) j)
      slotA j kj = trans (cong (λ f → readLoc (floc τM) (AtStack f j)) cfA) (Walk.slots wA j kj)

      kpA : Kp (falloc σ) (floc σ) (falloc τM) (floc τM)
      kpA = walk-kp wA

      live-shc : Live (falloc σ) (AtDynamic (sucHL hc))
      live-shc = live-suc (BeforeFrontier.heap-before H.hc-lt)

      hcM : suc (ref-id (heap-ref hc)) ≤ next-heap-ref (falloc τM)
      hcM = ≤-trans H.hc-lt (SegA.href (Walk.seg wA))

      ------------------------------------------------------------------
      -- 4. the call rows
      ------------------------------------------------------------------
      co : CallOut c prog τM (falloc τM) hc (ℓ o bodyL) env-sv (readReg (regs (floc τR)) Output)
      co = Call.out c prog τM (falloc τM) (subst (λ b → SpanAt prog b FA.callTxt) (sym pcM) span-call)
             (Walk.nh wA) hc (ℓ o bodyL) env-sv (readReg (regs (floc τR)) Output) inM
             (trans (slotA c (inj₁ refl)) H.cl) (trans (slotA (c + 2) (inj₂ refl)) H.ev)
             (trans (proj₂ kpA _ live-shc) H.code) hcM refl ≤-refl
      module CO = CallOut co

      w : FlatState
      w = CO.w

      kpC : Kp (falloc τM) (floc τM) (falloc w) (floc w)
      kpC = seg-kp CO.seg

      keep< : ∀ j → j < c → readLoc (floc w) (AtStack (current-frame (falloc τM)) j) ≡ readLoc (floc τM) (AtStack (current-frame (falloc τM)) j)
      keep< j p = SegA.mem CO.seg _ (BeforeFrontier.stack-before refl p)

      segAll : SegA (falloc σ) n σ w
      segAll = segA-∘ {falloc σ} {n} {σ} {τM} {w} (Walk.seg wA)
                 (seg-rebase {falloc σ} {falloc τM} {n} {c} {τM} {w} CO.seg cfA n≤c (SegA.href (Walk.seg wA)))

      abstract
        out : PreOut prog F E C n c bodyL Y sn hc e env-sv σ ns rest L
        out = record
          { cs = w ; steps = Walk.steps wA + 14
          ; run = s-++ {prog} {Walk.steps wA} {14} {σ} {τM} {w} (Walk.run wA) CO.runK
          ; seg = segAll ; nh = CO.nh ; pc = trans CO.pc (cong (14 +_) pcM)
          ; ret = trans CO.ret (Walk.ret wA) ; clo = CO.clo ; code = CO.code
          ; hc-lt = ≤-trans hcM (SegA.href CO.seg)
          ; ns0 = trans (SegA.ns segAll) H.ns0
          ; hp = CO.hp ; hp-lt = ≤-reflexive (trans (cong suc CO.ref-hp) (sym CO.hr))
          ; inp = CO.inp ; hp0 = CO.hp0 ; lw = readReg (regs (floc τR)) Output ; shp = CO.shp
          ; layer = word-tr (kp-∘ kpM kpC) RQ.out
          ; env = word-tr (seg-kp segAll) H.env
          ; eval = stack-keep node-tr (kp-∘ kpM kpC) (trans CO.cf cfM) (trans (cong (λ f → readLoc (floc w) (AtStack f (suc n))) (sym cfM))
                      (trans (keep< (suc n) lt1) (trans (cong (λ f → readLoc (floc τM) (AtStack f (suc n))) cfM) (slM (suc n))))) evalR
          ; val = stack-keep val-tr (kp-∘ kpM kpC) (trans CO.cf cfM) (trans (cong (λ f → readLoc (floc w) (AtStack f (n + 2))) (sym cfM))
                      (trans (keep< (n + 2) lt2) (trans (cong (λ f → readLoc (floc τM) (AtStack f (n + 2))) cfM) (slM (n + 2))))) RQ.stack
          ; cl = trans (cong (λ f → readLoc (floc w) (AtStack f c)) CO.cf) CO.cl
          ; ev = trans (cong (λ f → readLoc (floc w) (AtStack f (c + 2))) CO.cf) CO.ev }
