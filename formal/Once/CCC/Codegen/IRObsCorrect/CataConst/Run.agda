-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Run   (plan 0.135 S3, cata M1)
--
-- THE CATA FROM ITS CALL ON, over an ABSTRACT call state: whatever the
-- twenty-seven rows before the call established is a parameter here (the closure
-- register and its code cell, the argument pair and its two cells, what was
-- left alone), so no conversion in this module can unfold the machine run
-- that produced it. `CataConst` instantiates it at the setup's and the call
-- rows' last state.
--
-- From the call: the marker found by `thunk-found`, the body's run by the
-- block-call lemma on the algebra's IH, its meaning by `cata-const-meaning′`,
-- and — when the call returned — the jump over the body and its end label.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Run (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.BlockCall o tbl using (module BlockCallC)
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl using (module NuForceC)
open import Once.CCC.Codegen.IRObsCorrect.Apply o tbl using (module ApplyC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning o
  using (IdFree; idfree-of; tyeq; μ-layer-val; cata-const-meaning′)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Layout o tbl using (module CataLayoutC; const-rc; end-pc)
open import Once.CCC.Codegen.IRToTrace o using (cata-strategy; strat-const)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Input1; SV-Ptr; SV-Code; instr-call-closure; instr-ctrl; c-jmp; c-label)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.Res using (Res; returns; stopped; is-stopped)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)
open import Data.List.Properties using (++-identityʳ)
import Once.CCC.FrameSemantics
import Once.IR.Semantics.Trace as TM

module CataRunC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (SRun; SegA; segA-∘; bf-step; live-from; loc-ref; at-cf)
  open CataLayoutC {FS} using (module Text)
  open NuForceC {FS} using (crun-retarget)
  open ApplyC {FS} using (call-at)
  module BC = BlockCallC {FS}
  open CataStepsC {FS} using (s-++)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)


  -- a cell, by what it holds
  cell-sv : ∀ {prog a C c q st} → CellAt {prog = prog} a C c q st → StoredValue FS
  cell-sv (cell-ptr {comp-loc = cl′} _ _ _) = SV-Ptr cl′
  cell-sv (cell-inline {c = c} rep _)       = inline-sv rep c

  cell-read : ∀ {prog a C c q st} (ce : CellAt {prog = prog} a C c q st) → readLoc st q ≡ just (cell-sv ce)
  cell-read (cell-ptr r _ _)    = r
  cell-read (cell-inline rep r) = r

  -- a validity moved along a type equation
  valid-subst : ∀ {prog m a} {A B : IRTy} (eq : A ≡ B) {v : ⟦ A ⟧} {loc st}
              → ValidAtWF {prog = prog} m a {A} v loc st → ValidAtWF {prog = prog} m a {B} (subst ⟦_⟧ eq v) loc st
  valid-subst refl w = w

  module Run {F : IRFunctor} (wf : WellFormedFI F) {E C : IRTy} (alg : IR (E IRTy′.* ⟦ F ⟧TI C) C)
             (ih : IRObsCorrectF alg) (st : cata-strategy ⌈ F ⌉F ≡ strat-const)
             (n l : ℕ) (prog : AbstractTrace) (base : ℕ) (ss : AllSlotStable prog) (cr : BlockRuns prog)
             (span : SpanAt prog base (emitted n l (Cata wf alg)))
             (bl : BlocksAt prog (blocks n l (Cata wf alg)))
             (la : LabelsAt prog base (emitted n l (Cata wf alg)))
             (x : ⟦ E IRTy′.* μ-type F ⟧) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
             (ns0 : next-slot alloc ≡ 0) (k : ℕ) (rs : List ℕ)
             -- the state at the call, and what the twenty-seven rows before it established
             (cs : FlatState)
             (u : FlatState)
             (runS : SRun prog 13 (entry-flat base s alloc cl rs) u) (segS : SegA alloc n (entry-flat base s alloc cl rs) u)
             (runK : SRun prog 14 u cs) (segK : SegA alloc n u cs)
             (nh-cs : halted (floc cs) ≡ false) (pc-cs : fpc cs ≡ 27 + base) (ret-cs : fret cs ≡ rs)
             (hc hp μhl : HeapLocation) (mC : AllocMode) (pl : ValueLocation FS)
             (clo : fclosure cs ≡ SV-Ptr (AtDynamic hc))
             (code : readLoc (floc cs) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o (proj₁ (proj₂ (ir-to-trace' 0 l alg))))))
             (in-cs : readReg (regs (floc cs)) Input1 ≡ SV-Ptr (AtDynamic hp))
             (c₁ : CellAt {prog = prog} alloc E (proj₁ x) pl s)
             (hp-cs : readLoc (floc cs) (AtDynamic hp) ≡ readLoc s pl)
             (shp-cs : readLoc (floc cs) (AtDynamic (sucHL hp)) ≡ just (SV-Ptr (AtDynamic μhl)))
             -- the argument pair is below the frontier at the call (the call rows allocated it)
             (hp-lt : suc (loc-ref (AtDynamic hp)) ≤ next-heap-ref (falloc cs))
             (lμ : Live alloc (AtDynamic μhl))
             (vμ : ValidAtWF {prog = prog} mC alloc {μ-type F} (proj₂ x) (AtDynamic μhl) s)
             where

    i : IdFree wf
    i = idfree-of wf (const-rc ⌈ F ⌉F st)

    module T = Text wf alg n l

    span′ : SpanAt prog base T.text
    span′ = subst (SpanAt prog base) (T.emitted-eq st) span
    la′ : LabelsAt prog base T.text
    la′ = subst (LabelsAt prog base) (T.emitted-eq st) la
    module TA = T.At prog base span′ la′

    σ : FlatState
    σ = entry-flat base s alloc cl rs

    E′ : T∞ ⟦ C ⟧
    E′ = evalᴰ (Cata wf alg) x

    -- the twenty-seven rows, composed over the abstract states
    run27 : SRun prog 27 σ cs
    run27 = s-++ {prog} {13} {14} {σ} {u} {cs} runS runK

    seg : SegA alloc n σ cs
    seg = segA-∘ {alloc} {n} {σ} {u} {cs} segS segK

    hp-live : Live (falloc cs) (AtDynamic hp)
    hp-live = BeforeFrontier.heap-before hp-lt

    shp-live : Live (falloc cs) (AtDynamic (sucHL hp))
    shp-live = BeforeFrontier.heap-before (subst (λ z → suc z ≤ next-heap-ref (falloc cs)) (sym (sucHL-ref hp)) hp-lt)

    ------------------------------------------------------------------
    -- the call, landing on the body's marker
    ------------------------------------------------------------------
    j : ℕ
    j = 29 + base

    feq : find-thunk prog (ℓ o T.l1) ≡ just j
    feq = thunk-found {prog} (BlockRuns.thunks-unique cr) j (ℓ o T.l1) T.bb TA.fetch-thunk

    fs₁ : FlatState
    fs₁ = record cs { falloc = enter-call (falloc cs) ; fret = suc (fpc cs) ∷ fret cs
                    ; flink = just (suc (fpc cs)) ; fpc = j }

    call-eq : flat-exec-instr instr-call-closure prog cs ≡ fs₁
    call-eq = call-at prog cs hc (ℓ o T.l1) j clo code feq

    callS : FlatSteps prog 1 cs fs₁
    callS = step-at fs₁ (nh-cs , subst (λ z → fetch prog z ≡ just instr-call-closure) (sym pc-cs) (TA.span-call 14 _ refl)) call-eq []

    call-ev : chain-events callS ≡ []
    call-ev = chain-events-subst-start (sym call-eq) []

    run28 : FlatSteps prog 28 σ fs₁
    run28 = FlatSteps-++ (proj₁ run27) callS

    ev28 : chain-events run28 ≡ []
    ev28 = trans (chain-events-++ (proj₁ run27) callS) (cong₂ _++_ (proj₁ (proj₂ run27)) call-ev)

    h-eq : LocState.ev-log (floc fs₁) ≡ LocState.ev-log s
    h-eq = proj₂ (proj₂ run27)

    ------------------------------------------------------------------
    -- what the callee sees: everything live at entry, unchanged
    ------------------------------------------------------------------
    href-cs : next-heap-ref alloc ≤ next-heap-ref (falloc cs)
    href-cs = SegA.href seg

    a′ : AllocState {FS}
    a′ = BC.callee-alloc T.bb fs₁
    s′ : LocState FS
    s′ = BC.callee-loc T.bb fs₁

    to-callee : ∀ q → Live (falloc cs) q → Live a′ q
    to-callee = BC.live-callee T.bb fs₁ (falloc cs) refl

    live-cs : ∀ q → Live alloc q → Live (falloc cs) q
    live-cs = live-from alloc (falloc cs) href-cs

    bft : ∀ q → Live alloc q → Live a′ q
    bft q b = to-callee q (live-cs q b)

    rd′ : ∀ q → Live alloc q → readLoc s′ q ≡ readLoc s q
    rd′ q b = trans (BC.callee-heap T.bb fs₁ q (live-cs q b)) (SegA.mem seg q (live-ns n b))

    v-tr : ∀ {m A} {c : ⟦ A ⟧} {loc} → Live alloc loc
         → ValidAtWF {prog = prog} m alloc {A} c loc s → ValidAtWF {prog = prog} m a′ {A} c loc s′
    v-tr {m} {A} {c} {loc} q w = validityWF-heap-transport {prog = prog} {m} {A} (Live alloc) (λ _ b → b) rd′ bft c loc q w

    cell-copy : ∀ {A} {c : ⟦ A ⟧} {q₀ q} → readLoc s′ q ≡ readLoc s q₀
              → CellAt {prog = prog} alloc A c q₀ s → CellAt {prog = prog} a′ A c q s′
    cell-copy eq (cell-ptr r b w) = cell-ptr (trans eq r) (bft _ b) (v-tr b w)
    cell-copy eq (cell-inline rep r) = cell-inline rep (trans eq r)

    -- the algebra's argument: the environment and the μ's own layer
    L″ : ⟦ ⟦ F ⟧TI C ⟧
    L″ = subst ⟦_⟧ (tyeq i (μ-type F) C) (μ-layer-val wf (proj₂ x))

    x′ : ⟦ E IRTy′.* ⟦ F ⟧TI C ⟧
    x′ = proj₁ x , L″

    vL : ValidAtWF {prog = prog} mC a′ {⟦ F ⟧TI C} L″ (AtDynamic μhl) s′
    vL = valid-subst {prog = prog} (tyeq i (μ-type F) C) (v-tr lμ (μ-layer {prog = prog} {wf = wf} vμ))

    cE : CellAt {prog = prog} a′ E (proj₁ x) (AtDynamic hp) s′
    cE = cell-copy (trans (BC.callee-heap T.bb fs₁ {falloc cs} (AtDynamic hp) hp-live) hp-cs) c₁

    cL : CellAt {prog = prog} a′ (⟦ F ⟧TI C) L″ (AtDynamic (sucHL hp)) s′
    cL = cell-ptr (trans (BC.callee-heap T.bb fs₁ {falloc cs} (AtDynamic (sucHL hp)) shp-live) shp-cs)
                  (bft _ lμ) vL

    pv : ValidAtWF {prog = prog} Heap a′ {E IRTy′.* ⟦ F ⟧TI C} x′ (AtDynamic hp) s′
    pv = valid-pair-wf tt (to-callee (AtDynamic (sucHL hp)) shp-live) cE cL

    inp : InputAt {prog} {E IRTy′.* ⟦ F ⟧TI C} Heap a′ x′ s′
    inp = in-loc (AtDynamic hp) pv (to-callee (AtDynamic hp) hp-live) in-cs

    ------------------------------------------------------------------
    -- the body's run, and what it means
    ------------------------------------------------------------------
    crun₀ : CalleeRunP {prog = prog} {C} (ResultPlaceP {C} (VAt {prog = prog} C)) fs₁ (suc (fpc cs)) rs (evalᴰ alg x′) k
    crun₀ = BC.block-call alg ih l prog (ℓ o T.l1) T.bb j ss cr TA.body-span bl TA.body-labels
              fs₁ (falloc cs) Heap x′ (suc (fpc cs)) k rs refl nh-cs (cong (suc (fpc cs) ∷_) ret-cs) refl (trans (SegA.ns seg) ns0) inp

    meq : ⟪ E′ ⟫ k ≡ ⟪ evalᴰ alg x′ ⟫ k
    meq = cata-const-meaning′ (Once.CCC.FrameSemantics.fs-numerics FS)
            (tableEnv (Once.CCC.FrameSemantics.fs-numerics FS) (TM.pureHalf ιᶠ) tbl) wf i alg (proj₁ x) (proj₂ x) k

    crun : CalleeRunP {prog = prog} {C} (ResultPlaceP {C} (VAt {prog = prog} C)) fs₁ (suc (fpc cs)) rs E′ k
    crun = crun-retarget {prog = prog} {fs = fs₁} {c = evalᴰ alg x′} {c′ = E′} {k = k} (cong (runAt (floc fs₁)) meq) crun₀

    module CR = CalleeRunP crun

    RE : runAt (floc fs₁) (⟪ E′ ⟫ k) ≡ runAt s (⟪ E′ ⟫ k)
    RE = runAt-≡ {st = floc fs₁} {st′ = s} {m = ⟪ E′ ⟫ k} {m′ = ⟪ E′ ⟫ k} h-eq refl

    res-eq : resultAt (floc fs₁) (⟪ E′ ⟫ k) ≡ resultAt s (⟪ E′ ⟫ k)
    res-eq = cong proj₂ RE

    st-eq : stopsAt (floc fs₁) (⟪ E′ ⟫ k) ≡ stopsAt s (⟪ E′ ⟫ k)
    st-eq = cong (λ q → is-stopped (proj₂ q)) RE

    nc′ : NotCut (resultAt s (⟪ E′ ⟫ k)) → NotCut (resultAt (floc fs₁) (⟪ E′ ⟫ k))
    nc′ = subst NotCut (sym res-eq)

    ------------------------------------------------------------------
    -- the fields every outcome shares
    ------------------------------------------------------------------
    live-f : stopsAt s (⟪ E′ ⟫ k) ≡ false → halted (floc CR.settle) ≡ false
    live-f p = CR.live (trans st-eq p)

    stops-f : stopsAt s (⟪ E′ ⟫ k) ≡ true
            → halted (floc CR.settle) ≡ true × LocState.left (floc CR.settle) ≡ LocState.left s
    stops-f p = proj₁ (CR.stops (trans st-eq p))
              , trans (proj₂ (CR.stops (trans st-eq p))) (chain-left (proj₁ run27) nh-cs)

    log-f : LocState.ev-log (floc CR.settle) ≡ LocState.ev-log s ++ eventsAt s (⟪ E′ ⟫ k)
    log-f = trans CR.log (cong₂ _++_ h-eq (cong proj₁ RE))

    bf-cs : ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = m }) loc
          → BeforeFrontier (record (falloc cs) { next-slot = m }) loc
    bf-cs m = bf-step {alloc} {falloc cs} m m (SegA.cf seg) ≤-refl href-cs

    mem-f : NotCut (resultAt s (⟪ E′ ⟫ k)) → ∀ (loc : ValueLocation FS)
          → BeforeFrontier (record alloc { next-slot = n }) loc → readLoc (floc CR.settle) loc ≡ readLoc s loc
    mem-f nc loc bf = trans (CR.mem-pres (nc′ nc) (falloc cs) n refl loc (bf-cs n loc bf)) (SegA.mem seg loc bf)

    bfm-f : NotCut (resultAt s (⟪ E′ ⟫ k)) → ∀ (m : ℕ) (loc : ValueLocation FS)
          → BeforeFrontier (record alloc { next-slot = m }) loc
          → BeforeFrontier (record (falloc CR.settle) { next-slot = m }) loc
    bfm-f nc m loc bf = CR.bf-mono (nc′ nc) (falloc cs) m refl loc (bf-cs m loc bf)

    prog-c : k ≤ budgetLeft k (resultAt s (⟪ E′ ⟫ k)) + chain-ctrls CR.run
    prog-c = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls CR.run) res-eq CR.progress

    ------------------------------------------------------------------
    -- STOPPED or CUT: the run ends inside the callee.
    ------------------------------------------------------------------
    stuck : ∀ {ρ} → resultAt s (⟪ E′ ⟫ k) ≡ ρ → (∀ {v r} → ρ ≡ returns (done v r) → ⊥)
          → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    stuck eq nr = record
      { value-realized =
          realized (28 + CR.steps) CR.settle CR.out-mode CR.cont-alloc (FlatSteps-++ run28 CR.run)
                   live-f (λ p → ⊥-elim (nr (trans (sym eq) p))) stops-f (λ p → ⊥-elim (nr (trans (sym eq) p)))
                   (λ nc → CR.no-link (nc′ nc)) log-f (λ p → ⊥-elim (nr (trans (sym eq) p)))
                   (progress-≤ prog-c (ctrls-≤ʳ run28 CR.run))
                   (λ nc fr j′ bf → mem-f nc (AtStack fr j′) bf) (λ nc hl bf → mem-f nc (AtDynamic hl) bf)
                   (λ p → ⊥-elim (nr (trans (sym eq) p))) bfm-f (λ p → ⊥-elim (nr (trans (sym eq) p)))
      ; traces-agree = trc
      }
      where
        trc : chain-events (FlatSteps-++ run28 CR.run) ≡ eventsAt s (⟪ E′ ⟫ k)
        trc = trans (chain-events-++ run28 CR.run)
                    (trans (cong (_++ chain-events CR.run) ev28) (trans CR.events (cong proj₁ RE)))

    ------------------------------------------------------------------
    -- RETURNED: the jump over the body, and its end label.
    ------------------------------------------------------------------
    module Ret (v : ⟦ C ⟧) (r : ℕ) (eq : resultAt s (⟪ E′ ⟫ k) ≡ returns (done v r)) where

      retd : resultAt (floc fs₁) (⟪ E′ ⟫ k) ≡ returns (done v r)
      retd = trans res-eq eq

      nhS : halted (floc CR.settle) ≡ false
      nhS = CR.live (cong is-stopped retd)

      pcS : fpc CR.settle ≡ 28 + base
      pcS = trans (CR.returned retd) (cong suc pc-cs)

      t1 t2 : FlatState
      t1 = record CR.settle { fpc = (31 + length T.at) + base }
      t2 = record CR.settle { fpc = suc ((31 + length T.at) + base) }

      jmp-eq : flat-exec-instr (instr-ctrl (c-jmp T.endL)) prog CR.settle ≡ t1
      jmp-eq = cong (λ z → do-jump z CR.settle) TA.end-label

      rest2 : FlatSteps prog 1 t1 t2
      rest2 = step-at t2 (nhS , TA.fetch-end) refl []

      tail : FlatSteps prog 2 CR.settle t2
      tail = step-at t1 (nhS , subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp T.endL))) (sym pcS) TA.fetch-jmp)
                     jmp-eq rest2

      tail-ev : chain-events tail ≡ []
      tail-ev = chain-events-subst-start (sym jmp-eq) rest2

      run-r : FlatSteps prog (28 + (CR.steps + 2)) σ t2
      run-r = FlatSteps-++ run28 (FlatSteps-++ CR.run tail)

      trc-r : chain-events run-r ≡ eventsAt s (⟪ E′ ⟫ k)
      trc-r = trans (chain-events-++ run28 (FlatSteps-++ CR.run tail))
                (trans (cong (_++ chain-events (FlatSteps-++ CR.run tail)) ev28)
                (trans (chain-events-++ CR.run tail)
                (trans (cong₂ _++_ CR.events tail-ev)
                (trans (++-identityʳ _) (cong proj₁ RE)))))

      ctrls-r : chain-ctrls CR.run ≤ chain-ctrls run-r
      ctrls-r = ≤-trans (ctrls-≤ˡ CR.run tail) (ctrls-≤ʳ run28 (FlatSteps-++ CR.run tail))

      at-end-r : fpc t2 ≡ length (emitted n l (Cata wf alg)) + base
      at-end-r = trans (end-pc (length T.at) base)
                       (cong (_+ base) (sym (trans (cong length (T.emitted-eq st)) T.len-text)))

      mro : MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
      mro = record
        { value-realized =
            realized (28 + (CR.steps + 2)) t2 CR.out-mode CR.cont-alloc run-r
                     live-f (λ _ → at-end-r) stops-f (λ _ → CR.no-ret retd)
                     (λ nc → CR.no-link (nc′ nc)) log-f (λ p → rp→place (CR.place (trans res-eq p)))
                     (progress-≤ prog-c ctrls-r)
                     (λ nc fr j′ bf → mem-f nc (AtStack fr j′) bf) (λ nc hl bf → mem-f nc (AtDynamic hl) bf)
                     (λ _ → trans (CR.frame-pres retd (falloc cs) refl) (SegA.cf seg)) bfm-f
                     (λ _ → trans (CR.frames-pres retd (falloc cs) refl) (SegA.sf seg))
        ; traces-agree = trc-r
        }

    go : (ρ : Res (Ap ⟦ C ⟧)) → resultAt s (⟪ E′ ⟫ k) ≡ ρ
       → MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    go (returns (done v r)) eq = Ret.mro v r eq
    go stopped             eq = stuck eq (λ ())
    go (returns cut)       eq = stuck eq (λ ())

    result : MachineRefinesObsF prog base n l (Cata wf alg) x s alloc cl rs k
    result = go (resultAt s (⟪ E′ ⟫ k)) refl

