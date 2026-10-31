-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Branching   (plan 0.125 S3, cata M4 stage D2)
--
-- `cata-correct` AT `strat-branching`, PROVED: the generic post-order walk
-- (`cata-trace-branching`) refines the IR's cata, for every functor with a
-- recursive position.
--
-- For the input pair at `phl` (its μ cell pointing at `μhl`, exactly M1's
-- `CataConst.Glue` input):
--
--   1. entry → fold head (`ToFold.Build.out`): the setup, the init, the
--      flatten loop, silent; eval = `PO.FI [ root ] []`, val = `[]`; the
--      fold-head invariant `FoldInv.Inv.HeadAt` follows (the environment's
--      word carried across by the run's segment);
--   2. the fold loop (`FoldLoop.Loop.loop-run`): the machine runs as stage
--      A's `PO.runPO (PO.FI [ root ] []) []` — every fill on that run
--      succeeds (`FillOk.root-ok`);
--   3. that model runs as the cata, its result the value stack's only
--      entry (`Meaning.cata-br-meaning`, from `po-run`);
--   4. when it RETURNED, the exit (`FoldExit.Exit.exit`) puts the top of
--      val in `Output` and jumps over the body to the cata's end
--      (`word→place`). When it stopped or was cut, the run ends inside the
--      loop, where the algebra's call stopped or ran out of budget.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Branching (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Run o tbl using (module CataRunC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO; cata-alg; cata-br-meaning)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FillOk using (module FillOk)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Text o tbl using (module CataBrTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldText o tbl using (module CataFoldTextC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv o tbl using (module CataFoldInvC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.ToFold o tbl using (module CataToFoldC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldLoop o tbl using (module CataFoldLoopC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldExit o tbl using (module CataFoldExitC)
open import Once.CCC.Codegen.IRToTrace o using (cata-strategy; strat-branching)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Input1; Output; SV-Ptr)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Internal.Type using (Functor)
open import Once.Spec.Word using (Carrier)
open import Once.Internal.Value Carrier Carrier using (⟦_⟧F)
open import Once.Internal.Res using (Res; returns; stopped; is-stopped; mapRes)
open import Once.Internal.Iterative using (T∞)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (Σ)
import Once.CCC.FrameSemantics
open import Once.Spec.Numerics using (TargetNum)
import Once.Internal.Trace as TM

module CataBranchC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (SegA; seg-bf)
  open CataRunC {FS} using (cell-sv; cell-read)
  open CataStackC {FS} using (cell→word; word-tr; seg-kp)
  open CataWalkC {FS} using (Walk)
  open CataBrTextC {FS} using (module Text)
  open CataFoldTextC {FS} using (module FoldAt)
  open CataFoldInvC {FS} using (module Inv; RoundRun; Same)
  open CataToFoldC {FS} using (ToFoldOut; module Build)
  open CataFoldLoopC {FS} using (module Loop)
  open CataFoldExitC {FS} using (module Exit; word→place)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  private
    done-inj : ∀ {V : Set} {v v′ : V} {r r′ : ℕ} → _≡_ {A = Res (Ap V)} (returns (done v r)) (returns (done v′ r′)) → v ≡ v′
    done-inj refl = refl

    f≢t : false ≡ true → ⊥
    f≢t ()

  ------------------------------------------------------------------------
  -- THE CATA, for one input (the pair at `phl`, its μ cell pointing at `μhl`).
  ------------------------------------------------------------------------
  module Glue {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
              (ih : IRObsCorrectF alg) {G′ : Functor} (st : cata-strategy ⌈ F ⌉F ≡ strat-branching G′)
              (n l : ℕ) (prog : AbstractTrace) (base : ℕ) (ss : AllSlotStable prog) (cr : BlockRuns prog)
              (span : SpanAt prog base (emitted n l (Cata wf alg)))
              (bl : BlocksAt prog (blocks n l (Cata wf alg)))
              (la : LabelsAt prog base (emitted n l (Cata wf alg)))
              (x : ⟦ E IRTy′.* μ-type F ⟧) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
              (ns0 : next-slot alloc ≡ 0) (nh : halted s ≡ false) (k : ℕ) (rs : List ℕ)
              (phl : HeapLocation) (rdi : readReg (regs s) Input1 ≡ SV-Ptr (AtDynamic phl))
              (c₁ : CellAt {prog = prog} alloc E (proj₁ x) (AtDynamic phl) s)
              (μhl : HeapLocation) (mC : AllocMode)
              (rdμ : readLoc s (AtDynamic (sucHL phl)) ≡ just (SV-Ptr (AtDynamic μhl)))
              (lμ : Live alloc (AtDynamic μhl))
              (vμ : ValidAtWF {prog = prog} mC alloc {μ-type F} (proj₂ x) (AtDynamic μhl) s)
              where

    span′ : SpanAt prog base (Text.text′ wf alg n l)
    span′ = subst (SpanAt prog base) (Text.emitted-eq wf alg n l st) span
    la′ : LabelsAt prog base (Text.text′ wf alg n l)
    la′ = subst (LabelsAt prog base) (Text.emitted-eq wf alg n l st) la

    c bodyL X : ℕ
    c = Text.Pc.cslot wf alg n l
    bodyL = Text.Pc.bodyL wf alg n l
    X = FoldAt.X wf alg n l prog base span′ la′

    e : ⟦ E ⟧
    e = proj₁ x
    root : ⟦ μ-type F ⟧
    root = proj₂ x

    env-sv : StoredValue FS
    env-sv = cell-sv c₁

    σ : FlatState
    σ = entry-flat base s alloc cl rs

    fmt : TargetNum
    fmt = Once.CCC.FrameSemantics.fs-numerics FS

    -- the per-layer algebra (stage A's model)
    alg₀ : ⟦ ⌈ F ⌉F ⟧F ⟦ C ⟧ → T∞ ⟦ C ⟧
    alg₀ = cata-alg fmt (tableEnv fmt (TM.pureHalf ιᶠ) tbl) wf alg e

    ------------------------------------------------------------------
    -- 1. entry → the fold head
    ------------------------------------------------------------------
    tf : ToFoldOut prog n c bodyL X σ wf alg₀ C root env-sv
    tf = Build.out wf alg st n l prog base span la alg₀ x s alloc cl rs nh phl rdi c₁ μhl mC rdμ lμ vμ
    module TF = ToFoldOut tf

    open Inv prog F E C n c bodyL X TF.sn TF.hc e env-sv

    ev₀ : List ⟦ μ-type F ⟧
    ev₀ = PO.FI (wf-⌈⌉ wf) alg₀ (root ∷ []) []

    h₀ : HeadAt TF.τ ev₀ []
    h₀ = record
      { nh = TF.nh ; pc = TF.pc ; ns0 = trans (SegA.ns TF.seg) ns0
      ; eval = TF.eval ; val = TF.val ; cl = TF.cl ; ev = TF.ev ; code = TF.code
      ; hc-lt = subst (λ z → suc z ≤ next-heap-ref (falloc TF.τ)) (sym TF.ref-hc) TF.hr
      ; env = word-tr (seg-kp TF.seg) (cell→word c₁ (cell-read c₁)) }

    run₀ : FlatSteps prog TF.steps σ TF.τ
    run₀ = proj₁ TF.run

    log₀ : LocState.ev-log (floc TF.τ) ≡ LocState.ev-log s
    log₀ = proj₂ (proj₂ TF.run)

    ------------------------------------------------------------------
    -- 2. the fold loop
    ------------------------------------------------------------------
    M₀ : T∞ (List ⟦ C ⟧)
    M₀ = PO.runPO (wf-⌈⌉ wf) alg₀ ev₀ []

    RR : RoundRun prog n TF.τ M₀ k (λ ws τ → HeadAt τ [] ws)
    RR = Loop.loop-run prog wf alg ih n l base ss cr span′ la′ bl TF.sn TF.hc e env-sv ev₀ [] TF.τ
           (FillOk.root-ok (wf-⌈⌉ wf) alg₀ root) h₀ TF.lnk k
    module RR = RoundRun RR

    ------------------------------------------------------------------
    -- 3. what it means
    ------------------------------------------------------------------
    E′ : T∞ ⟦ C ⟧
    E′ = evalᴰ (Cata wf alg) x

    single : Ap ⟦ C ⟧ → Ap (List ⟦ C ⟧)
    single = PO.single (wf-⌈⌉ wf) alg₀

    ME : runAt (floc TF.τ) (⟪ M₀ ⟫ k) ≡ PO.singleRun (wf-⌈⌉ wf) alg₀ (runAt s (⟪ E′ ⟫ k))
    ME = trans (cong (λ h → TM.run ιᶠ h (⟪ M₀ ⟫ k)) log₀)
               (cata-br-meaning fmt (tableEnv fmt (TM.pureHalf ιᶠ) tbl) wf alg e root ιᶠ (LocState.ev-log s) k)

    ρ : Res (Ap ⟦ C ⟧)
    ρ = resultAt s (⟪ E′ ⟫ k)

    evs : eventsAt (floc TF.τ) (⟪ M₀ ⟫ k) ≡ eventsAt s (⟪ E′ ⟫ k)
    evs = cong proj₁ ME

    res : resultAt (floc TF.τ) (⟪ M₀ ⟫ k) ≡ mapRes single ρ
    res = cong proj₂ ME

    stop-s : ∀ (ρ′ : Res (Ap ⟦ C ⟧)) → is-stopped (mapRes single ρ′) ≡ is-stopped ρ′
    stop-s stopped     = refl
    stop-s (returns _) = refl

    bl-s : ∀ (ρ′ : Res (Ap ⟦ C ⟧)) → budgetLeft k (mapRes single ρ′) ≡ budgetLeft k ρ′
    bl-s stopped              = refl
    bl-s (returns (done _ _)) = refl
    bl-s (returns cut)        = refl

    nc-s : ∀ (ρ′ : Res (Ap ⟦ C ⟧)) → NotCut ρ′ → NotCut (mapRes single ρ′)
    nc-s stopped              _ = tt
    nc-s (returns (done _ _)) _ = tt
    nc-s (returns cut)        ()

    ------------------------------------------------------------------
    -- the fields every outcome shares
    ------------------------------------------------------------------
    stop-eq : stopsAt (floc TF.τ) (⟪ M₀ ⟫ k) ≡ stopsAt s (⟪ E′ ⟫ k)
    stop-eq = trans (cong is-stopped res) (stop-s ρ)

    ncR : NotCut ρ → NotCut (resultAt (floc TF.τ) (⟪ M₀ ⟫ k))
    ncR nc = subst NotCut (sym res) (nc-s ρ nc)

    prog-R : k ≤ budgetLeft k ρ + chain-ctrls RR.run
    prog-R = subst (λ b → k ≤ b + chain-ctrls RR.run) (trans (cong (budgetLeft k) res) (bl-s ρ)) RR.progress

    left₀ : LocState.left (floc TF.τ) ≡ LocState.left s
    left₀ = chain-left run₀ TF.nh

    log-R : LocState.ev-log (floc RR.τ) ≡ LocState.ev-log s ++ eventsAt s (⟪ E′ ⟫ k)
    log-R = trans RR.log (cong₂ _++_ log₀ evs)

    mem-R : NotCut ρ → ∀ (loc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = n }) loc
          → readLoc (floc RR.τ) loc ≡ readLoc s loc
    mem-R nc loc b = trans (RR.mem (ncR nc) loc (seg-bf TF.seg n loc b)) (SegA.mem TF.seg loc b)

    bf-R : NotCut ρ → ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = m }) loc
         → BeforeFrontier (record (falloc RR.τ) { next-slot = m }) loc
    bf-R nc m loc b = RR.bf (ncR nc) m loc (seg-bf TF.seg m loc b)

    ------------------------------------------------------------------
    -- STOPPED or CUT: the run ends inside the loop.
    ------------------------------------------------------------------
    stuck : ∀ {ρ′} → ρ ≡ ρ′ → (∀ {v r} → ρ′ ≡ returns (done v r) → ⊥)
          → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    stuck eq nr = record
      { value-realized =
          realized (TF.steps + RR.steps) RR.τ Heap (falloc RR.τ) (FlatSteps-++ run₀ RR.run)
                   (λ p → RR.live (trans stop-eq p))
                   (λ p → ⊥-elim (nr (trans (sym eq) p)))
                   (λ p → proj₁ (RR.stops (trans stop-eq p)) , trans (proj₂ (RR.stops (trans stop-eq p))) left₀)
                   (λ p → ⊥-elim (nr (trans (sym eq) p)))
                   (λ nc → RR.no-link (ncR nc)) log-R
                   (λ p → ⊥-elim (nr (trans (sym eq) p)))
                   (progress-≤ prog-R (ctrls-≤ʳ run₀ RR.run))
                   (λ nc fr j bf → mem-R nc (AtStack fr j) bf) (λ nc hl bf → mem-R nc (AtDynamic hl) bf)
                   (λ p → ⊥-elim (nr (trans (sym eq) p))) bf-R (λ p → ⊥-elim (nr (trans (sym eq) p)))
      ; traces-agree = trans (chain-events-++ run₀ RR.run)
                             (trans (cong₂ _++_ (proj₁ (proj₂ TF.run)) RR.events) evs)
      }

    ------------------------------------------------------------------
    -- RETURNED: the exit, to the cata's end.
    ------------------------------------------------------------------
    module Ret (v : ⟦ C ⟧) (r : ℕ) (eq : ρ ≡ returns (done v r)) where

      resR : resultAt (floc TF.τ) (⟪ M₀ ⟫ k) ≡ returns (done (v ∷ []) r)
      resR = trans res (cong (mapRes single) eq)

      sm : Same TF.τ RR.τ
      sm = RR.same resR

      wX : Walk prog n (λ _ → ⊥) RR.τ (Exit.END prog wf alg n l base span′ la′ TF.sn TF.hc e env-sv)
                (Exit.OutQ prog wf alg n l base span′ la′ TF.sn TF.hc e env-sv v)
      wX = Exit.exit prog wf alg n l base span′ la′ TF.sn TF.hc e env-sv RR.τ v [] (RR.post resR)

      τX : FlatState
      τX = Walk.τ wX

      runX : FlatSteps prog (Walk.steps wX) RR.τ τX
      runX = proj₁ (Walk.run wX)

      full : FlatSteps prog (TF.steps + (RR.steps + Walk.steps wX)) σ τX
      full = FlatSteps-++ run₀ (FlatSteps-++ RR.run runX)

      pl : Σ AllocMode (λ m → ResultPlace {prog = prog} C m (falloc τX) (falloc τX) v (floc τX))
      pl = word→place (Walk.post wX)

      at-end : fpc τX ≡ length (emitted n l (Cata wf alg)) + base
      at-end = trans (Walk.pc wX)
                 (sym (trans (cong (λ t → length t + base) {x = emitted n l (Cata wf alg)} {y = Text.text′ wf alg n l}
                                   (Text.emitted-eq wf alg n l st))
                             (FoldAt.len-end wf alg n l prog base span′ la′)))

      memX : NotCut ρ → ∀ (loc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = n }) loc
           → readLoc (floc τX) loc ≡ readLoc s loc
      memX nc loc b = trans (SegA.mem (Walk.seg wX) loc (bf-R nc n loc b)) (mem-R nc loc b)

      ctrlsX : chain-ctrls RR.run ≤ chain-ctrls full
      ctrlsX = ≤-trans (ctrls-≤ˡ RR.run runX) (ctrls-≤ʳ run₀ (FlatSteps-++ RR.run runX))

      evX : chain-events full ≡ eventsAt s (⟪ E′ ⟫ k)
      evX = trans (chain-events-++ run₀ (FlatSteps-++ RR.run runX))
              (trans (cong₂ _++_ (proj₁ (proj₂ TF.run))
                       (trans (chain-events-++ RR.run runX)
                       (trans (cong₂ _++_ RR.events (proj₁ (proj₂ (Walk.run wX)))) (++-identityʳ _))))
                     evs)

      mro : MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
      mro = record
        { value-realized =
            realized (TF.steps + (RR.steps + Walk.steps wX)) τX (proj₁ pl) (falloc τX) full
                     (λ _ → Walk.nh wX)
                     (λ _ → at-end)
                     (λ p → ⊥-elim (f≢t (trans (sym (cong is-stopped eq)) p)))
                     (λ _ → trans (Walk.ret wX) (trans (Same.ret sm) TF.ret))
                     (λ _ → trans (Walk.lnk wX) (RR.no-link (subst NotCut (sym resR) tt)))
                     (trans (proj₂ (proj₂ (Walk.run wX))) log-R)
                     (λ p → subst (λ z → ResultPlace {prog = prog} C (proj₁ pl) (falloc τX) (falloc τX) z (floc τX))
                                  (done-inj (trans (sym eq) p)) (proj₂ pl))
                     (progress-≤ prog-R ctrlsX)
                     (λ nc fr j bf → memX nc (AtStack fr j) bf) (λ nc hl bf → memX nc (AtDynamic hl) bf)
                     (λ _ → trans (Walk.cf wX) (trans (Same.cf sm) TF.cf))
                     (λ nc m loc b → seg-bf (Walk.seg wX) m loc (bf-R nc m loc b))
                     (λ _ → trans (SegA.sf (Walk.seg wX)) (trans (Same.sf sm) (SegA.sf TF.seg)))
        ; traces-agree = evX
        }

    go : (ρ′ : Res (Ap ⟦ C ⟧)) → ρ ≡ ρ′ → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    go (returns (done v r)) eq = Ret.mro v r eq
    go stopped             eq = stuck eq (λ ())
    go (returns cut)       eq = stuck eq (λ ())

    result : MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    result = go ρ refl

  ------------------------------------------------------------------------
  -- THE CLAUSE.
  ------------------------------------------------------------------------
  cata-correct-branching : ∀ {F} (wf : WellFormedFI F) {E C} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
                         → IRObsCorrectF alg → ∀ {G : Functor} → cata-strategy ⌈ F ⌉F ≡ strat-branching G
                         → IRObsCorrectF (Cata wf alg)
  -- the input is a PAIR: no register holds it, and it is not `Unit`
  cata-correct-branching wf alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-reg () _) k rs
  cata-correct-branching wf alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-unit ()) k rs
  cata-correct-branching wf alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh (in-loc (AtStack _ _) _ () _) k rs
  cata-correct-branching {F} wf {E} {C} alg ih st n l prog base ss cr span bl la mIn x s alloc cl ns0 nh
    (in-loc (AtDynamic phl) valid lv rdi) k rs =
    go-μ (PairValidWF.snd-cell d)
    where
      d = decomposePairWF valid

      -- a μ is never inline, and its cell points at the heap
      go-μ : CellAt {prog = prog} alloc (μ-type F) (proj₂ x) (AtDynamic (sucHL phl)) s
           → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
      go-μ (cell-inline (rep-prim ()) _)
      go-μ (cell-inline (rep-unit () _) _)
      go-μ (cell-ptr {comp-loc = AtStack _ _} _ () _)
      go-μ (cell-ptr {comp-loc = AtDynamic μhl} {mC = mC} rdμ lμ vμ) =
        Glue.result wf alg ih st n l prog base ss cr span bl la x s alloc cl ns0 nh k rs
                    phl rdi (PairValidWF.fst-cell d) μhl mC rdμ lμ vμ
