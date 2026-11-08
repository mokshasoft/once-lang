-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldExit   (plan 0.135 S3, cata M4 stage D1b)
--
-- THE FOLD LOOP'S EXIT, from the fold head with eval empty and val
-- `v ∷ vs` (`FoldInv.Inv.HeadAt σ [] (v ∷ vs)`), to the END of the cata's
-- text:
--
--     head (3 rows) · branch → ℓ (l1+3) · the label ·
--     load val · mov-to-input · load-at 0              Output := v's word
--     c-jmp ℓ (bodyL+1) · the end label                 over the body
--
-- a silent `Walk` ending at `length text′ + base` with `Output` holding a
-- valid word of `C` for `v` — which is the cata's `ResultPlace`
-- (`word→place`, at the word's own mode).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldExit (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText o tbl using (module CataFoldTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldPop o tbl using (module CataFoldPopC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv o tbl using (module CataFoldInvC)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; sv-as-loc; load-from-slot; load-at; mov-to-input; instr-ctrl; c-jmp; c-label; writeReg-same; offsetLoc)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Visit o tbl using (module CataVisitC)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
import Once.CCC.Machine.FlatPut as FlatPut
open import Data.List.Properties using (++-identityʳ)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; μ-type)
import Once.IRTy as IRTy′
open import Data.Product using (Σ)
open import Data.Unit using (⊤)

module CataFoldExitC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} hiding (X)
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataBrTextC {FS} using (module Text)
  open CataFoldTextC {FS} using (module FoldAt)
  open CataFoldPopC {FS} using (module FoldHead; KH)
  open CataFoldInvC {FS} using (module Inv)
  open CataVisitC {FS} using (bk-id; load-bk; kp-set)
  open GetC {FS} using (setOut; out-mem; offset-zero; load-at-step)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  -- a valid word in `Output` is a result place, at the word's own mode
  word→place′ : ∀ {prog a B v s w} → FlatPut.Src {FS} {prog} a s B v w → readReg (regs s) Output ≡ w
              → Σ AllocMode (λ m → ResultPlace {prog = prog} B m a a v s)
  word→place′ (FlatPut.src-node {cl = cl} {m = m} nd lv val) e = m , at-loc cl val lv e val lv
  word→place′ (FlatPut.src-flat {m = m} {sl = sl} fl lv val) e = m , at-loc sl val lv e val lv
  word→place′ (FlatPut.src-scalar fit) e                       = Heap , at-reg fit e
  word→place′ FlatPut.src-unit e                               = Heap , unit-result

  word→place : ∀ {prog a B v s} → WordAt prog a B v (readReg (regs s) Output) s
             → Σ AllocMode (λ m → ResultPlace {prog = prog} B m a a v s)
  word→place w = word→place′ w refl

  module Exit (prog : AbstractTrace) {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
              (n l base : ℕ)
              (span : SpanAt prog base (Text.text′ wf alg n l))
              (la : LabelsAt prog base (Text.text′ wf alg n l))
              (sn hc : HeapLocation) (e : ⟦ E ⟧) (env-sv : StoredValue FS) where

    module FA = FoldAt wf alg n l prog base span la
    open FA using (X; Y; Z; span-hd; exit-label; exitL; endL; fetch-exit; fetch-ld; fetch-mti2; fetch-li; fetch-jmp-end; end-label; fetch-end)

    c bodyL l1 : ℕ
    c = FA.T.Pc.cslot
    bodyL = FA.T.Pc.bodyL
    l1 = FA.T.l1

    at : AbstractTrace
    at = FA.T.at

    open Inv prog F E C n c bodyL X sn hc e env-sv

    module FH = FoldHead prog F C n l1 sn (11 + Z) exit-label

    -- the end of the cata's text
    END : ℕ
    END = (19 + length at) + Z

    OutQ : ⟦ C ⟧ → FlatState → Set
    OutQ v τ = WordAt prog (falloc τ) C v (readReg (regs (floc τ)) Output) (floc τ)

    -- from the exit label on, over an abstract state
    module Tail (v : ⟦ C ⟧) (vs : List ⟦ C ⟧) (x0 : FlatState) (pc0 : fpc x0 ≡ 11 + Z) (nh0 : halted (floc x0) ≡ false)
                (sv0 : StackAt (ValE prog C) (falloc x0) (floc x0) (n + 2) sn (v ∷ vs)) where

      x1 : FlatState
      x1 = record x0 { fpc = 12 + Z }

      w1 : Walk prog n (λ _ → ⊥) x0 (12 + Z) (λ _ → ⊤)
      w1 = walk-ctrl x0 (instr-ctrl (c-label exitL)) (12 + Z) nh0
             (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-label exitL))) (sym pc0) fetch-exit)
             (cong (λ z → record x0 { fpc = suc z }) pc0) refl tt tt

      tp : HeapLocation
      tp = StackAt.top sv0

      data Top : Set where
        top-is : (w : StoredValue FS) → readLoc (floc x0) (AtDynamic tp) ≡ just w → ValE prog C (falloc x0) (floc x0) v w → Top

      uncons : ∀ {b} → Chain (ValE prog C) (falloc x0) (floc x0) sn b (v ∷ vs) → b ≡ tp → Top
      uncons (ch-cons w lv r0 ew r1 ch) refl = top-is w r0 ew

      module T (w : StoredValue FS) (r0 : readLoc (floc x0) (AtDynamic tp) ≡ just w) (ew : ValE prog C (falloc x0) (floc x0) v w) where

        x2 x3 x4 : FlatState
        x2 = St (load-from-slot (n + 2)) x1
        x3 = St mov-to-input x2
        x4 = setOut x3 w

        wf2 : InstrWF (floc x1) (falloc x1) (load-from-slot (n + 2))
        wf2 = SV-Ptr (AtDynamic tp) , StackAt.slot sv0
        nh2 : halted (floc x2) ≡ false
        nh2 = exec-abstract-preserves-halted-WF (load-from-slot (n + 2)) (floc x1) (falloc x1) nh0 wf2
        nh3 : halted (floc x3) ≡ false
        nh3 = exec-abstract-preserves-halted-WF mov-to-input (floc x2) (falloc x2) nh2 tt
        in3 : readReg (regs (floc x3)) Input1 ≡ SV-Ptr (AtDynamic tp)
        in3 = trans (in-movin (floc x2) (falloc x2)) (out-lslot (n + 2) (floc x1) (falloc x1) _ (StackAt.slot sv0))

        r0-3 : readLoc (floc x3) (AtDynamic tp) ≡ just w
        r0-3 = trans (hp-keep mov-to-input (floc x2) (falloc x2) tp nhw-mov-to-input)
                     (trans (hp-keep (load-from-slot (n + 2)) (floc x1) (falloc x1) tp nhw-load-from-slot) r0)

        -- the value's word, `load-at 0` (D381)
        r0′ : readLoc (floc x3) (offsetLoc (AtDynamic tp) 0) ≡ just w
        r0′ = trans (cong (readLoc (floc x3)) (offset-zero (AtDynamic tp))) r0-3
        nh4 : halted (floc x4) ≡ false
        nh4 = nh3
        out4 : readReg (regs (floc x4)) Output ≡ w
        out4 = writeReg-same (regs (floc x3)) Output w

        bk2 = load-bk (n + 2) (floc x1) (falloc x1) (StackAt.slot sv0)
        kp4 : Kp (falloc x1) (floc x1) (falloc x4) (floc x4)
        kp4 = kp-∘ (kp-q (load-from-slot (n + 2)) x1 nhw-load-from-slot refl tt tt bk2)
                   (kp-∘ (kp-q mov-to-input x2 nhw-mov-to-input refl tt tt bk-id) (kp-set x3 w))

        q4 : OutQ v x4
        q4 = subst (λ z → WordAt prog (falloc x4) C v z (floc x4)) (sym out4) (word-tr kp4 ew)

        -- the read, as a one-step walk: only `Output` moves
        eq4 : flat-exec-instr (load-at 0) prog x3 ≡ x4
        eq4 = load-at-step prog x3 0 (AtDynamic tp) w in3 r0′
        st4 : FlatSteps prog 1 x3 x4
        st4 = step-at x4 (nh3 , fetch-li) eq4 []
        sil4 : chain-events st4 ≡ []
        sil4 = chain-events-subst-start (sym eq4) []
        w-la : Walk prog n (λ _ → ⊥) x3 (suc (fpc x3)) (OutQ v)
        w-la = record
          { τ = x4 ; steps = 1 ; run = st4 , sil4 , trans (log-of st4 sil4) (++-identityʳ _)
          ; seg = record { mem = λ loc _ → out-mem x3 w loc ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }
          ; bk = λ _ _ ib → ib ; nh = nh3 ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = refl
          ; slots = λ j _ → out-mem x3 w (AtStack (current-frame (falloc x3)) j) ; post = q4 }

        w2 : Walk prog n (λ _ → ⊥) x1 (15 + Z) (OutQ v)
        w2 = walk-∘ {prog} {n} {λ _ → ⊥} {x1}
               (walk-q {Q = λ _ → ⊤} x1 (load-from-slot (n + 2)) refl nh0 fetch-ld wf2 nhw-load-from-slot refl tt tt refl tt bk2 tt)
               (walk-∘ {prog} {n} {λ _ → ⊥} {x2}
                 (walk-q {Q = λ _ → ⊤} x2 mov-to-input refl nh2 fetch-mti2 tt nhw-mov-to-input refl tt tt refl tt bk-id tt)
                 w-la)

        x5 : FlatState
        x5 = record x4 { fpc = (18 + length at) + Z }

        w3 : Walk prog n (λ _ → ⊥) x4 ((18 + length at) + Z) (OutQ v)
        w3 = walk-ctrl x4 (instr-ctrl (c-jmp endL)) ((18 + length at) + Z) nh4 fetch-jmp-end
               (cong (λ mj → do-jump mj x4) end-label) refl tt q4

        w4 : Walk prog n (λ _ → ⊥) x5 END (OutQ v)
        w4 = walk-ctrl x5 (instr-ctrl (c-label endL)) END nh4 fetch-end refl refl tt q4

        result : Walk prog n (λ _ → ⊥) x0 END (OutQ v)
        result = walk-∘ {prog} {n} {λ _ → ⊥} {x0} w1
                   (walk-∘ {prog} {n} {λ _ → ⊥} {x1} w2
                   (walk-∘ {prog} {n} {λ _ → ⊥} {x4} w3 w4))

      abstract
        out : Walk prog n (λ _ → ⊥) x0 END (OutQ v)
        out with uncons (StackAt.chain sv0) refl
        ... | top-is w r0 ew = T.result w r0 ew

    module Go (σ : FlatState) (v : ⟦ C ⟧) (vs : List ⟦ C ⟧) (h : HeadAt σ [] (v ∷ vs)) where

      module H = HeadAt h

      wE : Walk prog n (KH n) σ (11 + Z) (λ τ → StackAt (ValE prog C) (falloc τ) (floc τ) (n + 2) sn (v ∷ vs))
      wE = FH.Exit.out σ (v ∷ vs) (subst (λ b → SpanAt prog b FH.hd8) (sym H.pc) span-hd) H.nh H.eval H.val

      abstract
        out : Walk prog n (λ _ → ⊥) σ END (OutQ v)
        out = walk-∘ {prog} {n} {λ _ → ⊥} {σ} (walk-K (λ _ ()) wE)
                (Tail.out v vs (Walk.τ wE) (Walk.pc wE) (Walk.nh wE) (Walk.post wE))

    -- THE EXIT: from the fold head with nothing left to fold, to the cata's end
    exit : ∀ (σ : FlatState) (v : ⟦ C ⟧) (vs : List ⟦ C ⟧) → HeadAt σ [] (v ∷ vs) → Walk prog n (λ _ → ⊥) σ END (OutQ v)
    exit σ v vs h = Go.out σ v vs h
