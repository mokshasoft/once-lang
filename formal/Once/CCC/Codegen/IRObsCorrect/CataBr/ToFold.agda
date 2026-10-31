-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.ToFold   (plan 0.135 S3, cata M4 stage C)
--
-- A `strat-branching` CATA FROM ITS ENTRY TO THE FOLD LOOP'S HEAD, as one
-- abstract bundle (`ToFoldOut`), for the input pair at `phl` whose μ cell
-- points at `μhl` (exactly what M1's `CataConst.Glue` receives):
--
--   1. the thirteen setup rows — M1's own `CataConst.Setup` at the
--      branching slots (`cl = c`, `k`, `ev = c+2`, `c = n+7+4·fsize F+4`,
--      body label `l1+4+2·lsize F`): the environment in `ev` and the
--      closure record `[0 , body]` (`Setup.out`; the argument pair is no
--      longer the setup's — every call allocates its own, plan 0.135 D1a);
--   2. the fourteen init rows and the root's push (`CataBr.Init`);
--   3. the flatten loop to its exit (`CataBr.Flatten`), from todo `[ root ]`.
--
-- It ends at the fold head `ℓ (l1+2)` with todo `[]`, eval
-- `PO.FI … [ root ] []` (= `po root ++ []`, `flatten-start`), val `[]`, the
-- facts M1's `Call` consumes (the record in slot `cl`, the environment in
-- slot `ev`, the record's code cell), the run
-- silent and everything below the frontier `n` untouched (`seg`, against
-- the entry allocator). The init and the loop keep the call slots
-- (`Init.KI`, `Round.KL`), which is what carries the setup's facts across.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.ToFold (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Setup o tbl using (module CataSetupC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Run o tbl using (module CataRunC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Init o tbl using (module CataInitC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Round o tbl using (module CataRoundC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Flatten o tbl using (module CataFlattenC)
open import Once.CCC.Codegen.IRToTrace o using (cata-strategy; strat-branching; fsize)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Input1; SV-Ptr; SV-Code)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using (⟦_⟧F)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.Spec.Type using (Fun)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Nat using (_*_)

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

private
  fold-pc : ∀ (v h : ℕ) → suc ((23 + v) + h) ≡ (22 + (v + 2)) + h
  fold-pc = solve 2 (λ v h → con 1 :+ ((con 23 :+ v) :+ h) := (con 22 :+ (v :+ con 2)) :+ h) refl

module CataToFoldC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (SRun; SegA; Seg; seg-rebase; Kp)
  open CataSetupC {FS} using (module Setup; SetupOut)
  open CataRunC {FS} using (cell-sv; cell-read)
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataBrTextC {FS} using (module Text)
  open CataInitC {FS} using (module Init; InitQ; KI)
  open CataRoundC {FS} using (KL)
  open CataFlattenC {FS} using (module Flatten; module Keep)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  ------------------------------------------------------------------------
  -- WHAT THE FOLD LOOP STARTS FROM, as an opaque bundle.
  ------------------------------------------------------------------------
  record ToFoldOut (prog : AbstractTrace) (n c bodyL X : ℕ) (σ : FlatState)
                   {F : IRFunctor} (wf : WellFormedFI F) {C₀ : Set} (alg₀ : ⟦ ⌈ F ⌉F ⟧F C₀ → T∞ C₀)
                   (C : IRTy) (root : ⟦ μ-type F ⟧) (env-sv : StoredValue FS) : Set where
    field
      τ      : FlatState
      steps  : ℕ
      run    : SRun prog steps σ τ
      seg    : Seg n σ τ
      nh     : halted (floc τ) ≡ false
      pc     : fpc τ ≡ X
      ret    : fret τ ≡ fret σ
      clo    : fclosure τ ≡ fclosure σ
      lnk    : flink τ ≡ flink σ
      cf     : current-frame (falloc τ) ≡ current-frame (falloc σ)
      -- the three stacks, on one sentinel
      sn     : HeapLocation
      todo   : StackAt (NodeE prog F) (falloc τ) (floc τ) n sn []
      eval   : StackAt (NodeE prog F) (falloc τ) (floc τ) (suc n) sn (PO.FI (wf-⌈⌉ wf) alg₀ (root ∷ []) [])
      val    : StackAt (ValE prog C) (falloc τ) (floc τ) (n + 2) sn []
      -- the closure record and the environment (what M1's `Call` consumes)
      hc     : HeapLocation
      ref-hc : ref-id (heap-ref hc) ≡ next-heap-ref (falloc σ)
      cl     : readLoc (floc τ) (AtStack (current-frame (falloc τ)) c) ≡ just (SV-Ptr (AtDynamic hc))
      ev     : readLoc (floc τ) (AtStack (current-frame (falloc τ)) (c + 2)) ≡ just env-sv
      code   : readLoc (floc τ) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o bodyL))
      hr     : suc (next-heap-ref (falloc σ)) ≤ next-heap-ref (falloc τ)

  ------------------------------------------------------------------------
  -- THE BUNDLE, for one input.
  ------------------------------------------------------------------------
  module Build {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
               {G′ : Fun 0} (st : cata-strategy ⌈ F ⌉F ≡ strat-branching G′)
               (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
               (span : SpanAt prog base (emitted n l (Cata wf alg)))
               (la : LabelsAt prog base (emitted n l (Cata wf alg)))
               {C₀ : Set} (alg₀ : ⟦ ⌈ F ⌉F ⟧F C₀ → T∞ C₀)
               (x : ⟦ E IRTy′.* μ-type F ⟧) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
               (rs : List ℕ) (nh : halted s ≡ false)
               (phl : HeapLocation) (rdi : readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic phl))
               (c₁ : CellAt {prog = prog} alloc E (proj₁ x) (AtDynamic phl) s)
               (μhl : HeapLocation) (mC : AllocMode)
               (rdμ : readLoc s (AtDynamic (sucHL phl)) ≡ just (SV-Ptr (AtDynamic μhl)))
               (lμ : Live alloc (AtDynamic μhl))
               (vμ : ValidAtWF {prog = prog} mC alloc {μ-type F} (proj₂ x) (AtDynamic μhl) s)
               where

    module T = Text wf alg n l

    span′ : SpanAt prog base T.text′
    span′ = subst (SpanAt prog base) (T.emitted-eq st) span
    la′ : LabelsAt prog base T.text′
    la′ = subst (LabelsAt prog base) (T.emitted-eq st) la

    module TA = T.At prog base span′ la′

    c : ℕ
    c = T.Pc.cslot

    cb : n + 7 + 4 * fsize ⌈ F ⌉F ≤ c
    cb = m≤m+n (n + 7 + 4 * fsize ⌈ F ⌉F) 4

    n7≤c : n + 7 ≤ c
    n7≤c = ≤-trans (m≤m+n (n + 7) (4 * fsize ⌈ F ⌉F)) cb

    n≤c : n ≤ c
    n≤c = ≤-trans (m≤m+n n 7) n7≤c

    σ : FlatState
    σ = entry-flat base s alloc cl rs

    env-sv μ-sv : StoredValue FS
    env-sv = cell-sv c₁
    μ-sv   = SV-Ptr (AtDynamic μhl)

    root : ⟦ μ-type F ⟧
    root = proj₂ x

    -- the fold head: one past the flatten loop
    X : ℕ
    X = length T.Pc.flatTxt + TA.H

    ------------------------------------------------------------------
    -- 1. the setup (M1's), as a walk keeping no slot
    ------------------------------------------------------------------
    so : SetupOut c T.Pc.bodyL prog σ env-sv μ-sv
    so = Setup.out c T.Pc.bodyL prog σ TA.span-setup nh phl env-sv μ-sv rdi (cell-read c₁) rdμ
    module SO = SetupOut so

    u : FlatState
    u = SO.u

    wS : Walk prog n (λ _ → ⊥) σ (13 + base) (λ _ → ⊤)
    wS = record
      { τ = u ; steps = 13 ; run = SO.runS
      ; seg = seg-rebase {falloc σ} {falloc σ} {n} {c} {σ} {u} SO.seg refl n≤c ≤-refl
      ; nh = SO.nh ; pc = SO.pc ; ret = SO.ret ; clo = SO.clo ; lnk = SO.lnk ; cf = SO.cf ; slots = λ _ () ; post = tt }

    ------------------------------------------------------------------
    -- 2. the init and the root's push
    ------------------------------------------------------------------
    span-i : SpanAt prog (fpc u) (T.Pc.initTxt ++ T.Pc.rootTxt)
    span-i = subst (λ b → SpanAt prog b (T.Pc.initTxt ++ T.Pc.rootTxt)) (sym SO.pc) TA.span-init

    kpS : Kp alloc s (falloc u) (floc u)
    kpS = seg-kp SO.seg

    wd : NodeE prog F (falloc u) (floc u) root (readReg (regs (floc u)) Input1)
    wd = subst (λ z → WordAt prog (falloc u) (μ-type F) root z (floc u)) (sym SO.inμ)
               (word-tr kpS (w-ptr {prog} {alloc} {μ-type F} {root} {μ-sv} {s} {mC} (AtDynamic μhl) refl lμ vμ))

    module I = Init prog F C n c n7≤c u span-i SO.nh root wd

    wI : Walk prog n (KI c) u (24 + fpc u) (InitQ prog F C n I.sn root)
    wI = I.out

    τI : FlatState
    τI = Walk.τ wI

    pcI : fpc τI ≡ TA.H
    pcI = trans (Walk.pc wI) (cong (24 +_) SO.pc)

    ------------------------------------------------------------------
    -- 3. the flatten loop
    ------------------------------------------------------------------
    module FL = Flatten prog wf alg₀ n c T.l1 I.sn cb TA.H TA.span-flat TA.head-label TA.exit-label TA.visit-labels

    wF : Walk prog n (KL n c) τI (suc FL.L.XL) (FL.FQ (root ∷ []) [])
    wF = FL.flatten-root τI root pcI (Walk.nh wI) (InitQ.todo (Walk.post wI)) (InitQ.eval (Walk.post wI))

    τ : FlatState
    τ = Walk.τ wF

    ------------------------------------------------------------------
    -- …and what crosses them: the call slots and the record's code cell
    ------------------------------------------------------------------
    module KI′ = Keep wI
    module KF = Keep wF

    live-shc : Live (falloc u) (AtDynamic (sucHL SO.hc))
    live-shc = live-suc (BeforeFrontier.heap-before (subst (λ z → suc z ≤ next-heap-ref (falloc u)) (sym SO.ref-hc)
                                                            (≤-reflexive (sym SO.hr))))

    cross-slot : ∀ {k v} → c ≤ k
               → readLoc (floc u) (AtStack (current-frame (falloc u)) k) ≡ just v
               → readLoc (floc τ) (AtStack (current-frame (falloc τ)) k) ≡ just v
    cross-slot c≤k r = KF.keep-slot (inj₂ c≤k) (KI′.keep-slot c≤k r)

    cross-heap : ∀ {l v} → Live (falloc u) l → readLoc (floc u) l ≡ just v → readLoc (floc τ) l ≡ just v
    cross-heap lv r = KF.keep-heap (proj₁ (walk-kp wI) _ lv) (KI′.keep-heap lv r)

    ------------------------------------------------------------------
    -- THE BUNDLE.
    ------------------------------------------------------------------
    wAll : Walk prog n (λ _ → ⊥) σ (suc FL.L.XL) (FL.FQ (root ∷ []) [])
    wAll = walk-∘ {prog} {n} {λ _ → ⊥} {σ} wS
             (walk-∘ {prog} {n} {λ _ → ⊥} {u} (walk-K (λ _ ()) wI) (walk-K (λ _ ()) wF))

    pc-X : suc FL.L.XL ≡ X
    pc-X = trans (fold-pc FL.L.VL TA.H)
                 (cong (λ z → (22 + z) + TA.H) (sym (length-++ T.Pc.visitTxt {T.Pc.exitTxt})))

    abstract
      out : ToFoldOut prog n c T.Pc.bodyL X σ wf alg₀ C root env-sv
      out = record
        { τ = τ ; steps = Walk.steps wAll ; run = Walk.run wAll ; seg = Walk.seg wAll ; nh = Walk.nh wF
        ; pc = trans (Walk.pc wF) pc-X
        ; ret = Walk.ret wAll ; clo = Walk.clo wAll ; lnk = Walk.lnk wAll ; cf = Walk.cf wAll
        ; sn = I.sn
        ; todo = proj₁ (Walk.post wF)
        ; eval = proj₂ (Walk.post wF)
        ; val = KF.keep-stack val-tr (inj₁ refl) (InitQ.val (Walk.post wI))
        ; hc = SO.hc ; ref-hc = SO.ref-hc
        ; cl = cross-slot ≤-refl SO.cl
        ; ev = cross-slot (m≤m+n c 2) SO.ev
        ; code = cross-heap live-shc SO.code
        ; hr = ≤-trans (≤-reflexive (sym SO.hr)) (≤-trans (SegA.href (Walk.seg wI)) (SegA.href (Walk.seg wF))) }
