-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldBack   (plan 0.135 S3, cata M4 stage D1b)
--
-- THE END OF A FOLD ROUND, after the algebra returned (at the row after the
-- call, `15 + Y`, its result's word in `Output`): `push2` onto the value
-- stack, then `c-jmp ℓ (l1+2)` back to the fold head — where `HeadAt`
-- holds one node on, with the result pushed. A silent `Walk`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldBack (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC; module SlotArith; module OffArith)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText o tbl using (module CataFoldTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv o tbl using (module CataFoldInvC)
open import Once.CCC.Codegen.IRToTrace o using (fsize)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output
        ; SV-Ptr; SV-Code; instr-ctrl; c-jmp)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
open import Data.Nat using (_*_)

module CataFoldBackC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} hiding (X)
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataBrTextC {FS} using (module Text)
  open CataFoldTextC {FS} using (module FoldAt)
  open CataFoldInvC {FS} using (module Inv)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  module Back (prog : AbstractTrace) {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
              (n l base : ℕ)
              (span : SpanAt prog base (Text.text′ wf alg n l))
              (la : LabelsAt prog base (Text.text′ wf alg n l))
              (sn hc : HeapLocation) (e : ⟦ E ⟧) (env-sv : StoredValue FS) where

    module FA = FoldAt wf alg n l prog base span la
    open FA using (X; Y; span-push; fetch-jmp-head; head-label; headL)

    c bodyL : ℕ
    c = FA.T.Pc.cslot
    bodyL = FA.T.Pc.bodyL

    n7≤c : n + 7 ≤ c
    n7≤c = ≤-trans (m≤m+n (n + 7) (4 * fsize ⌈ F ⌉F)) (m≤m+n (n + 7 + 4 * fsize ⌈ F ⌉F) 4)

    open SlotArith n c n7≤c
    open OffArith n

    open Inv prog F E C n c bodyL X sn hc e env-sv

    -- what the machine has when the algebra returned `v`
    record BackIn (τ : FlatState) (ns : List ⟦ μ-type F ⟧) (v : ⟦ C ⟧) (rest : List ⟦ C ⟧) : Set where
      field
        nh    : halted (floc τ) ≡ false
        pc    : fpc τ ≡ 15 + Y
        ns0   : next-slot (falloc τ) ≡ 0
        eval  : StackAt (NodeE prog F) (falloc τ) (floc τ) (suc n) sn ns
        val   : StackAt (ValE prog C) (falloc τ) (floc τ) (n + 2) sn rest
        out   : WordAt prog (falloc τ) C v (readReg (regs (floc τ)) Output) (floc τ)
        cl    : readLoc (floc τ) (AtStack (current-frame (falloc τ)) c) ≡ just (SV-Ptr (AtDynamic hc))
        ev    : readLoc (floc τ) (AtStack (current-frame (falloc τ)) (c + 2)) ≡ just env-sv
        code  : readLoc (floc τ) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o bodyL))
        hc-lt : suc (ref-id (heap-ref hc)) ≤ next-heap-ref (falloc τ)
        env   : WordAt prog (falloc τ) E e env-sv (floc τ)

    s≢2 : suc n ≢ n + 2
    s≢2 e = <-irrefl (trans e (+-comm n 2)) (n<1+n (suc n))

    module Go (τ : FlatState) (ns : List ⟦ μ-type F ⟧) (v : ⟦ C ⟧) (rest : List ⟦ C ⟧) (b : BackIn τ ns v rest) where

      module B = BackIn b

      pu : Push2Out (ValE prog C) prog n (n + 2) (n + 4) (n + 5) sn τ v rest
      pu = push2-run (ValE prog C) val-tr prog n (n + 2) (n + 4) (n + 5) sn τ v rest
             (subst (λ z → SpanAt prog z FA.pushV) (sym B.pc) span-push) B.nh
             (m≤m+n n 2) (m≤m+n n 4) (m≤m+n n 5) (off-≢ (λ ())) (off-≢ (λ ())) 4≢5 B.out B.val
      module PU = Push2Out pu

      τ7 : FlatState
      τ7 = PU.τ

      kp7 : Kp (falloc τ) (floc τ) (falloc τ7) (floc τ7)
      kp7 = seg-kp PU.seg

      sl7 : ∀ j → j ≢ n + 2 → j ≢ n + 4 → j ≢ n + 5
          → readLoc (floc τ7) (AtStack (current-frame (falloc τ7)) j) ≡ readLoc (floc τ) (AtStack (current-frame (falloc τ)) j)
      sl7 j a b′ c′ = trans (cong (λ f → readLoc (floc τ7) (AtStack f j)) PU.cf) (PU.slots j a b′ c′)

      far-c : ∀ {j} → c ≤ j → (j ≢ n + 2) × (j ≢ n + 4) × (j ≢ n + 5)
      far-c c≤j = far lt2 c≤j , far lt4 c≤j , far lt5 c≤j

      pc7 : fpc τ7 ≡ 25 + Y
      pc7 = trans PU.pc (cong (10 +_) B.pc)

      live-shc : Live (falloc τ) (AtDynamic (sucHL hc))
      live-shc = live-suc (BeforeFrontier.heap-before B.hc-lt)

      τX : FlatState
      τX = record τ7 { fpc = X }

      hd : HeadAt τX ns (v ∷ rest)
      hd = record
        { nh = PU.nh ; pc = refl ; ns0 = trans (SegA.ns PU.seg) B.ns0
        ; eval = stack-keep node-tr kp7 PU.cf (PU.slots (suc n) s≢2 s≢4 s≢5) B.eval
        ; val = PU.stack
        ; cl = trans (sl7 c (proj₁ (far-c ≤-refl)) (proj₁ (proj₂ (far-c ≤-refl))) (proj₂ (proj₂ (far-c ≤-refl)))) B.cl
        ; ev = trans (sl7 (c + 2) (proj₁ (far-c (m≤m+n c 2))) (proj₁ (proj₂ (far-c (m≤m+n c 2)))) (proj₂ (proj₂ (far-c (m≤m+n c 2))))) B.ev
        ; code = trans (proj₂ kp7 _ live-shc) B.code
        ; hc-lt = ≤-trans B.hc-lt (SegA.href PU.seg)
        ; env = word-tr kp7 B.env }

      abstract
        out : Walk prog n (λ _ → ⊥) τ X (λ τ′ → HeadAt τ′ ns (v ∷ rest))
        out = walk-∘ {prog} {n} {λ _ → ⊥} {τ} (walk-K (λ _ ()) (push-walk {K = λ _ → ⊥} (λ _ ()) pu))
                (walk-ctrl τ7 (instr-ctrl (c-jmp headL)) X PU.nh
                   (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp headL))) (sym pc7) fetch-jmp-head)
                   (cong (λ mj → do-jump mj τ7) head-label) refl tt hd)
