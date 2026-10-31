-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldRound   (plan 0.135 S3, cata M4 stage D1b)
--
-- ONE ROUND OF THE FOLD LOOP, PROVED. From the fold head with eval
-- `t ∷ ns` and val `vs` (`FoldInv.Inv.HeadAt`), where the node's layer
-- rebuilds from `vs` to `L` with `rest` left over, at observation depth `k`:
--
--   * the rows up to the call (`FoldPre`: pop, rebuild, the call rows with
--     a FRESH pair `[env , L]`) are silent;
--   * `instr-call-closure` lands on the algebra's marker (`thunk-found`),
--     and the body runs as the block-call lemma says (`BlockCall.block-call`
--     on the algebra's IH) — the round's events, log, budget and stop are
--     the algebra's, `evalᴰ alg (e , L)` at depth `k`;
--   * when it RETURNED `v`, the push and the back edge (`FoldBack`) bring
--     the machine back to the fold head with eval `ns`, val `v ∷ rest`.
--
-- So the round is a `RoundRun … (evalᴰ alg (e , L)) k (λ v τ → HeadAt τ ns (v ∷ rest))`
-- (`round`); `round-po` restates it at stage A's model (`PO.fill`, the
-- per-layer algebra `cata-alg`), which is what the fold's induction (D2)
-- runs over with `PO.runPO-step-run`.
--
-- Across the call, the caller's cells and slots are the callee's
-- `mem-pres` (every cell the round wrote before it is fresh or a slot of
-- the cata's own frame); the stack frontier is the program's invariant
-- (`exec-flat-keeps-next-slot`), so the next round's call has its
-- `next-slot ≡ 0` again.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldRound (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.BlockCall o tbl using (module BlockCallC)
open import Once.CCC.Codegen.IRObsCorrect.Apply o tbl using (module ApplyC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning o using (μ-layer-val)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO; cata-alg)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o using (fillI; enc; fill-enc)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText o tbl using (module CataFoldTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv o tbl using (module CataFoldInvC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldPre o tbl using (module CataFoldPreC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldBack o tbl using (module CataFoldBackC)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; instr-call-closure)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using (⟦_⟧F; sem-Out)
open import Once.Res using (Res; returns; stopped; is-stopped)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)
open import Data.List.Properties using (++-identityʳ)
import Once.CCC.FrameSemantics
import Once.IR.Semantics.Trace as TM

module CataFoldRoundC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (SRun; SegA; Kp; bf-step; seg-bf)
  open ApplyC {FS} using (call-at)
  module BC = BlockCallC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataBrTextC {FS} using (module Text)
  open CataFoldTextC {FS} using (module FoldAt)
  open CataFoldInvC {FS} using (module Inv; RoundRun; Same)
  open CataFoldPreC {FS} using (module Pre; PreOut)
  open CataFoldBackC {FS} using (module Back)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  -- where a callee's result is, as a word in `Output`
  place→word : ∀ {prog B m a ca v s} → ResultPlace {prog = prog} B m a ca v s → WordAt prog a B v (readReg (regs s) Output) s
  place→word unit-result                    = w-inl (rep-unit refl _) refl
  place→word (at-loc loc val lv out _ _)    = w-ptr loc out lv val
  place→word (at-reg fit rax)               = w-inl (rep-prim fit) rax

  -- a heap cell below one frontier, read at a stack bound
  bf-live : ∀ {a a′ : AllocState {FS}} {m : ℕ} (l : ValueLocation FS) → Live a l
          → BeforeFrontier (record a′ { next-slot = m }) l → Live a′ l
  bf-live (AtDynamic _) _ (BeforeFrontier.heap-before r) = BeforeFrontier.heap-before r

  live-lt : ∀ {a : AllocState {FS}} {h : HeapLocation} → Live a (AtDynamic h) → suc (ref-id (heap-ref h)) ≤ next-heap-ref a
  live-lt (BeforeFrontier.heap-before r) = r

  done-inj : ∀ {V : Set} {v v′ : V} {r r′ : ℕ} → _≡_ {A = Res (Ap V)} (returns (done v r)) (returns (done v′ r′)) → v ≡ v′
  done-inj refl = refl

  module Round (prog : AbstractTrace) {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
               (ih : IRObsCorrectF alg) (n l base : ℕ) (ss : AllSlotStable prog) (cr : BlockRuns prog)
               (span : SpanAt prog base (Text.text′ wf alg n l))
               (la : LabelsAt prog base (Text.text′ wf alg n l))
               (bl : BlocksAt prog (blocks n l (Cata wf alg)))
               (sn hc : HeapLocation) (e : ⟦ E ⟧) (env-sv : StoredValue FS) where

    module FA = FoldAt wf alg n l prog base span la
    open FA using (X; Y)

    c bodyL bb : ℕ
    c = FA.T.Pc.cslot
    bodyL = FA.T.Pc.bodyL
    bb = FA.T.bb

    open Inv prog F E C n c bodyL X sn hc e env-sv
    module PR = Pre prog wf alg n l base span la sn hc e env-sv
    module BK = Back prog wf alg n l base span la sn hc e env-sv

    j : ℕ
    j = 31 + Y

    feq : find-thunk prog (ℓ o bodyL) ≡ just j
    feq = thunk-found {prog} (BlockRuns.thunks-unique cr) j (ℓ o bodyL) bb FA.fetch-thunk

    module Go (σ : FlatState) (t : ⟦ μ-type F ⟧) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧)
              (L : ⟦ ⟦ F ⟧TI C ⟧) (rest : List ⟦ C ⟧)
              (fq : fillI wf (μ-type F) C (μ-layer-val wf t) vs ≡ just (L , rest))
              (h : HeadAt σ (t ∷ ns) vs) (k : ℕ) where

      po : PreOut prog F E C n c bodyL Y sn hc e env-sv σ ns rest L
      po = PR.Go.out σ t ns vs L rest fq h
      module P = PreOut po

      cs : FlatState
      cs = P.cs

      ------------------------------------------------------------------
      -- the call, landing on the algebra's marker
      ------------------------------------------------------------------
      fs₁ : FlatState
      fs₁ = record cs { falloc = enter-call (falloc cs) ; fret = suc (fpc cs) ∷ fret cs
                      ; flink = just (suc (fpc cs)) ; fpc = j }

      call-eq : flat-exec-instr instr-call-closure prog cs ≡ fs₁
      call-eq = call-at prog cs hc (ℓ o bodyL) j P.clo P.code feq

      callS : FlatSteps prog 1 cs fs₁
      callS = step-at fs₁ (P.nh , subst (λ z → fetch prog z ≡ just instr-call-closure) (sym P.pc) FA.fetch-cc) call-eq []

      runC : FlatSteps prog (P.steps + 1) σ fs₁
      runC = FlatSteps-++ (proj₁ P.run) callS

      evC : chain-events runC ≡ []
      evC = trans (chain-events-++ (proj₁ P.run) callS)
                  (cong₂ _++_ (proj₁ (proj₂ P.run)) (chain-events-subst-start (sym call-eq) []))

      h-eq : LocState.ev-log (floc fs₁) ≡ LocState.ev-log (floc σ)
      h-eq = proj₂ (proj₂ P.run)

      ------------------------------------------------------------------
      -- what the callee sees: the fresh pair `[env , L]`
      ------------------------------------------------------------------
      a′ : AllocState {FS}
      a′ = BC.callee-alloc bb fs₁
      s′ : LocState FS
      s′ = BC.callee-loc bb fs₁

      kpc : Kp (falloc cs) (floc cs) a′ s′
      kpc = BC.live-callee bb fs₁ (falloc cs) refl , (λ q lq → BC.callee-heap bb fs₁ q lq)

      hp-live : Live (falloc cs) (AtDynamic P.hp)
      hp-live = BeforeFrontier.heap-before P.hp-lt

      x′ : ⟦ E IRTy′.* ⟦ F ⟧TI C ⟧
      x′ = e , L

      cE : CellAt {prog = prog} a′ E e (AtDynamic P.hp) s′
      cE = word→cell (trans (proj₂ kpc _ hp-live) P.hp0) (word-tr kpc P.env)

      cL : CellAt {prog = prog} a′ (⟦ F ⟧TI C) L (AtDynamic (sucHL P.hp)) s′
      cL = word→cell (trans (proj₂ kpc _ (live-suc hp-live)) P.shp) (word-tr kpc P.layer)

      inp : InputAt {prog} {E IRTy′.* ⟦ F ⟧TI C} Heap a′ x′ s′
      inp = in-loc (AtDynamic P.hp) (valid-pair-wf tt (proj₁ kpc _ (live-suc hp-live)) cE cL) (proj₁ kpc _ hp-live) P.inp

      comp : T∞ ⟦ C ⟧
      comp = evalᴰ alg x′

      crun : CalleeRunP {prog = prog} {C} (ResultPlaceP {C} (VAt {prog = prog} C)) fs₁ (suc (fpc cs)) (fret cs) comp k
      crun = BC.block-call alg ih l prog (ℓ o bodyL) bb j ss cr FA.body-span bl FA.body-labels
               fs₁ (falloc cs) Heap x′ (suc (fpc cs)) k (fret cs) refl P.nh refl refl P.ns0 inp

      module CR = CalleeRunP crun

      RE : runAt (floc fs₁) (⟪ comp ⟫ k) ≡ runAt (floc σ) (⟪ comp ⟫ k)
      RE = runAt-≡ {st = floc fs₁} {st′ = floc σ} {m = ⟪ comp ⟫ k} {m′ = ⟪ comp ⟫ k} h-eq refl

      ρ₀ : Res (Ap ⟦ C ⟧)
      ρ₀ = resultAt (floc σ) (⟪ comp ⟫ k)

      res-eq : resultAt (floc fs₁) (⟪ comp ⟫ k) ≡ ρ₀
      res-eq = cong proj₂ RE

      st-eq : stopsAt (floc fs₁) (⟪ comp ⟫ k) ≡ stopsAt (floc σ) (⟪ comp ⟫ k)
      st-eq = cong (λ q → is-stopped (proj₂ q)) RE

      nc′ : NotCut ρ₀ → NotCut (resultAt (floc fs₁) (⟪ comp ⟫ k))
      nc′ = subst NotCut (sym res-eq)

      ------------------------------------------------------------------
      -- the fields every outcome shares
      ------------------------------------------------------------------
      Post : ⟦ C ⟧ → FlatState → Set
      Post v τ = HeadAt τ ns (v ∷ rest)

      live-f : stopsAt (floc σ) (⟪ comp ⟫ k) ≡ false → halted (floc CR.settle) ≡ false
      live-f p = CR.live (trans st-eq p)

      stops-f : stopsAt (floc σ) (⟪ comp ⟫ k) ≡ true
              → halted (floc CR.settle) ≡ true × LocState.left (floc CR.settle) ≡ LocState.left (floc σ)
      stops-f p = proj₁ (CR.stops (trans st-eq p))
                , trans (proj₂ (CR.stops (trans st-eq p))) (chain-left (proj₁ P.run) P.nh)

      log-f : LocState.ev-log (floc CR.settle) ≡ LocState.ev-log (floc σ) ++ eventsAt (floc σ) (⟪ comp ⟫ k)
      log-f = trans CR.log (cong₂ _++_ h-eq (cong proj₁ RE))

      bf-cs : ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record (falloc σ) { next-slot = m }) loc
            → BeforeFrontier (record (falloc cs) { next-slot = m }) loc
      bf-cs m = bf-step {falloc σ} {falloc cs} m m (SegA.cf P.seg) ≤-refl (SegA.href P.seg)

      mem-f : NotCut ρ₀ → ∀ (loc : ValueLocation FS)
            → BeforeFrontier (record (falloc σ) { next-slot = n }) loc → readLoc (floc CR.settle) loc ≡ readLoc (floc σ) loc
      mem-f nc loc bf = trans (CR.mem-pres (nc′ nc) (falloc cs) n refl loc (bf-cs n loc bf)) (SegA.mem P.seg loc bf)

      bf-f : NotCut ρ₀ → ∀ (m : ℕ) (loc : ValueLocation FS)
           → BeforeFrontier (record (falloc σ) { next-slot = m }) loc
           → BeforeFrontier (record (falloc CR.settle) { next-slot = m }) loc
      bf-f nc m loc bf = CR.bf-mono (nc′ nc) (falloc cs) m refl loc (bf-cs m loc bf)

      prog-c : k ≤ budgetLeft k ρ₀ + chain-ctrls CR.run
      prog-c = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls CR.run) res-eq CR.progress

      ------------------------------------------------------------------
      -- STOPPED or CUT: the round ends inside the callee.
      ------------------------------------------------------------------
      stuck : ∀ {ρ} → ρ₀ ≡ ρ → (∀ {v r} → ρ ≡ returns (done v r) → ⊥) → RoundRun prog n σ comp k Post
      stuck eq nr = record
        { τ = CR.settle ; steps = (P.steps + 1) + CR.steps ; run = FlatSteps-++ runC CR.run
        ; events = trans (chain-events-++ runC CR.run)
                         (trans (cong (_++ chain-events CR.run) evC) (trans CR.events (cong proj₁ RE)))
        ; log = log-f
        ; progress = progress-≤ prog-c (ctrls-≤ʳ runC CR.run)
        ; live = live-f ; stops = stops-f
        ; no-link = λ nc → CR.no-link (nc′ nc)
        ; mem = mem-f ; bf = bf-f
        ; same = λ p → ⊥-elim (nr (trans (sym eq) p))
        ; post = λ p → ⊥-elim (nr (trans (sym eq) p)) }

      ------------------------------------------------------------------
      -- RETURNED: push the result, back to the head.
      ------------------------------------------------------------------
      module Ret (v : ⟦ C ⟧) (r : ℕ) (eq : ρ₀ ≡ returns (done v r)) where

        retd : resultAt (floc fs₁) (⟪ comp ⟫ k) ≡ returns (done v r)
        retd = trans res-eq eq

        nc : NotCut (resultAt (floc fs₁) (⟪ comp ⟫ k))
        nc = subst NotCut (sym retd) tt

        settle : FlatState
        settle = CR.settle

        nhS : halted (floc settle) ≡ false
        nhS = CR.live (cong is-stopped retd)

        pcS : fpc settle ≡ 15 + Y
        pcS = trans (CR.returned retd) (cong suc P.pc)

        kpS : Kp (falloc cs) (floc cs) (falloc settle) (floc settle)
        kpS = (λ q lq → bf-live q lq (CR.bf-mono nc (falloc cs) 0 refl q (live-ns 0 lq)))
            , (λ q lq → CR.mem-pres nc (falloc cs) 0 refl q (live-ns 0 lq))

        cfS : current-frame (falloc settle) ≡ current-frame (falloc cs)
        cfS = CR.frame-pres retd (falloc cs) refl

        slS : ∀ (i : ℕ) → readLoc (floc settle) (AtStack (current-frame (falloc cs)) i)
                          ≡ readLoc (floc cs) (AtStack (current-frame (falloc cs)) i)
        slS i = CR.mem-pres nc (falloc cs) (suc i) refl _ (BeforeFrontier.stack-before refl (n<1+n i))

        slS′ : ∀ (i : ℕ) → readLoc (floc settle) (AtStack (current-frame (falloc settle)) i)
                           ≡ readLoc (floc cs) (AtStack (current-frame (falloc cs)) i)
        slS′ i = trans (cong (λ f → readLoc (floc settle) (AtStack f i)) cfS) (slS i)

        runS : FlatSteps prog (1 + CR.steps) cs settle
        runS = FlatSteps-++ callS CR.run

        ns0S : next-slot (falloc settle) ≡ 0
        ns0S = trans (cong (λ z → next-slot (falloc z)) (sym (exec-flat-steps runS 0)))
                     (trans (exec-flat-keeps-next-slot prog ss ((1 + CR.steps) + 0) cs) P.ns0)

        live-shc : Live (falloc cs) (AtDynamic (sucHL hc))
        live-shc = live-suc (BeforeFrontier.heap-before P.hc-lt)

        bin : BK.BackIn settle ns v rest
        bin = record
          { nh = nhS ; pc = pcS ; ns0 = ns0S
          ; eval = stack-keep node-tr kpS cfS (slS (suc n)) P.eval
          ; val = stack-keep val-tr kpS cfS (slS (n + 2)) P.val
          ; out = place→word (rp→place (CR.place retd))
          ; cl = trans (slS′ c) P.cl
          ; ev = trans (slS′ (c + 2)) P.ev
          ; code = trans (proj₂ kpS _ live-shc) P.code
          ; hc-lt = live-lt (proj₁ kpS (AtDynamic hc) (BeforeFrontier.heap-before P.hc-lt))
          ; env = word-tr kpS P.env }

        wB : Walk prog n (λ _ → ⊥) settle X (λ τ′ → HeadAt τ′ ns (v ∷ rest))
        wB = BK.Go.out settle ns v rest bin

        tailR : FlatSteps prog (Walk.steps wB) settle (Walk.τ wB)
        tailR = proj₁ (Walk.run wB)

        runR : FlatSteps prog ((P.steps + 1) + (CR.steps + Walk.steps wB)) σ (Walk.τ wB)
        runR = FlatSteps-++ runC (FlatSteps-++ CR.run tailR)

        out : RoundRun prog n σ comp k Post
        out = record
          { τ = Walk.τ wB ; steps = (P.steps + 1) + (CR.steps + Walk.steps wB) ; run = runR
          ; events = trans (chain-events-++ runC (FlatSteps-++ CR.run tailR))
                       (trans (cong (_++ chain-events (FlatSteps-++ CR.run tailR)) evC)
                       (trans (chain-events-++ CR.run tailR)
                       (trans (cong₂ _++_ CR.events (proj₁ (proj₂ (Walk.run wB))))
                       (trans (++-identityʳ _) (cong proj₁ RE)))))
          ; log = trans (proj₂ (proj₂ (Walk.run wB))) log-f
          ; progress = progress-≤ prog-c (≤-trans (ctrls-≤ˡ CR.run tailR) (ctrls-≤ʳ runC (FlatSteps-++ CR.run tailR)))
          ; live = λ _ → Walk.nh wB
          ; stops = λ p → ⊥-elim (f≢t (trans (sym (cong is-stopped eq)) p))
          ; no-link = λ _ → trans (Walk.lnk wB) (CR.no-link nc)
          ; mem = λ nc₀ loc b → trans (SegA.mem (Walk.seg wB) loc (bf-f nc₀ n loc b)) (mem-f nc₀ loc b)
          ; bf = λ nc₀ m loc b → seg-bf (Walk.seg wB) m loc (bf-f nc₀ m loc b)
          ; same = λ _ → record
              { ret = trans (Walk.ret wB) (trans (CR.no-ret retd) P.ret)
              ; cf = trans (Walk.cf wB) (trans cfS (SegA.cf P.seg))
              ; sf = trans (SegA.sf (Walk.seg wB)) (trans (CR.frames-pres retd (falloc cs) refl) (SegA.sf P.seg)) }
          ; post = λ eq′ → subst (λ z → HeadAt (Walk.τ wB) ns (z ∷ rest)) (done-inj (trans (sym eq) eq′)) (Walk.post wB) }
          where
            f≢t : false ≡ true → ⊥
            f≢t ()

      go : (ρ : Res (Ap ⟦ C ⟧)) → ρ₀ ≡ ρ → RoundRun prog n σ comp k Post
      go (returns (done v r)) eq = Ret.out v r eq
      go stopped             eq = stuck eq (λ ())
      go (returns cut)       eq = stuck eq (λ ())

      abstract
        result : RoundRun prog n σ comp k Post
        result = go ρ₀ refl

    ------------------------------------------------------------------
    -- THE ROUND.
    ------------------------------------------------------------------
    round : ∀ (σ : FlatState) (t : ⟦ μ-type F ⟧) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧)
              (L : ⟦ ⟦ F ⟧TI C ⟧) (rest : List ⟦ C ⟧)
          → fillI wf (μ-type F) C (μ-layer-val wf t) vs ≡ just (L , rest)
          → HeadAt σ (t ∷ ns) vs → (k : ℕ)
          → RoundRun prog n σ (evalᴰ alg (e , L)) k (λ v τ → HeadAt τ ns (v ∷ rest))
    round σ t ns vs L rest fq h k = Go.result σ t ns vs L rest fq h k

    -- …at stage A's model: the per-layer algebra, the layer `PO.fill` rebuilds
    alg₀ : ⟦ ⌈ F ⌉F ⟧F ⟦ C ⟧ → T∞ ⟦ C ⟧
    alg₀ = cata-alg (Once.CCC.FrameSemantics.fs-numerics FS)
             (tableEnv (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl) wf alg e

    round-po : ∀ (σ : FlatState) (t : ⟦ μ-type F ⟧) (ns : List ⟦ μ-type F ⟧) (vs : List ⟦ C ⟧)
                 (l′ : ⟦ ⌈ F ⌉F ⟧F ⟦ C ⟧) (rest : List ⟦ C ⟧)
             → PO.fill (wf-⌈⌉ wf) alg₀ ⌈ F ⌉F (sem-Out (wf-⌈⌉ wf) t) vs ≡ just (l′ , rest)
             → HeadAt σ (t ∷ ns) vs → (k : ℕ)
             → RoundRun prog n σ (alg₀ l′) k (λ v τ → HeadAt τ ns (v ∷ rest))
    round-po σ t ns vs l′ rest eq h k =
      round σ t ns vs (enc wf C l′) rest (fill-enc wf alg₀ wf (sem-Out (wf-⌈⌉ wf) t) vs eq) h k
