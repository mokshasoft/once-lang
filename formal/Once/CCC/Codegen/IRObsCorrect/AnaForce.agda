-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.AnaForce
--
-- plan 0.135 S3: `Ana`'s FORCE. An `Ana` suspension is two heap cells — the
-- seed pair `(e , a)`, and the code address of the Ana block — and forcing it
-- calls that block on the seed. The block is the coalgebra followed by the
-- re-suspension of every recursive position (D199), so one force yields a
-- layer whose recursive positions are again `Ana` suspensions.
--
-- The proof is about an INDUCTIVE predicate (`AnaP`: "this cell is an `Ana`
-- suspension of a valid seed"), and shows one force lands in a layer of
-- `AnaP`s (`ana-step`). `NuCoind` turns that into `NuV`; nothing here is
-- corecursive.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.AnaForce (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.BlockCall o tbl
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl
open import Once.CCC.Codegen.IRToTrace o using (resuspend-layer)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; StoredValue; readReg; Input1; Output; writeReg-same; writeReg-preserves; SV-Code; SV-Ptr; sucLoc
        ; mov-to-output; store-at-slot; block-layout; e-thunk)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; _⊕_; _⊗_; wf-K; wf-Id; wf-Sum; wf-Prod)
import Once.IRTy as IRTy′
open import Once.IR.Semantics.Iterative using (T∞; fmap∞)
open import Data.Unit using (⊤)
import Data.Maybe as DM
open import Once.CCC.Codegen.LabelScope o using (labels-in; resuspend-labels-in)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Codegen.IRObsCorrect.Resusp o tbl
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_; con)
import Once.IR.Semantics.Trace as TM
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (1+n≰n)
open import Data.List.Properties using (++-identityʳ)
open import Once.Res using (Res; stopped; returns; mapRes; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
import Once.Denotation.ValueDomain as ValueDomain
import Once.CCC.Machine.ValueRel as CWF

module AnaForceC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open Resolve {FS} using (found-in-window; noLabel-outside)
  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix)
  open LocState using (regs; halted)
  open AllocState using (next-slot; current-frame; saved-frames; next-heap-ref)
  open NuForceC {FS}
  open CWF.ClosureWellFormedBase {FS} using (CellAtP; fo-base; pair-wf; inl-wf; inr-wf; inl-reg-wf; inr-reg-wf)

  module AnaBlock {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
                  (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (ihc : IRObsCorrectF coalg)
                  (l : ℕ) (prog : AbstractTrace) (ss : AllSlotStable prog) (cr : BlockRuns prog) where

    -- The block `Ana` mints (IRToTrace, `ir-to-trace' n l (Ana wf coalg)`).
    ctrace : AbstractTrace
    ctrace = emitted 1 (suc l) coalg

    rsp : ℕ × ℕ × AbstractTrace
    rsp = resuspend-layer (proj₁ (ir-to-trace' 1 (suc l) coalg)) (proj₁ (proj₂ (ir-to-trace' 1 (suc l) coalg))) (ℓ o l) 0 wf

    bb : ℕ
    bb = proj₁ rsp

    body : AbstractTrace
    body = mov-to-output ∷ store-at-slot 0 ∷ ctrace DL.++ proj₂ (proj₂ rsp)

    -- AN `Ana` SUSPENSION: the code cell names this block, and cell 0 holds a
    -- valid seed (its own residence, as a closure's environment cell).
    data AnaP : AllocMode → AllocState {FS} → ValueDomain.⟦ ν-type F ⟧ᴰᴵ → ValueLocation FS → LocState FS → Set where
      ana-p : ∀ {alloc ν-loc s} (x : ValueDomain.⟦ E IRTy′.* A ⟧ᴰᴵ)
            → LocMatchesMode Heap ν-loc
            → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o l))
            → Live alloc (sucLoc ν-loc)
            → CellAt {prog = prog} alloc (E IRTy′.* A) x ν-loc s
            → AnaP Heap alloc (retVal (evalᴰ (Ana wf coalg) x)) ν-loc s

    AP : VTy (ν-type F)
    AP m a v lc st = AnaP m a v lc st

    -- the seed cell's content
    cell-sv : ∀ {a C c cl st} → CellAt {prog = prog} a C c cl st → StoredValue FS
    cell-sv (cell-ptr {comp-loc = cl′} _ _ _) = SV-Ptr cl′
    cell-sv (cell-inline {c = c} rep _)       = inline-sv rep c

    cell-mode : ∀ {a C c cl st} → CellAt {prog = prog} a C c cl st → AllocMode
    cell-mode (cell-ptr {mC = m} _ _ _) = m
    cell-mode (cell-inline _ _)         = Heap

    cell-read : ∀ {a C c cl st} (ce : CellAt {prog = prog} a C c cl st) → readLoc st cl ≡ just (cell-sv ce)
    cell-read (cell-ptr r _ _)    = r
    cell-read (cell-inline rep r) = r

    -- AnaP, and a layer of them, survive a heap-frontier move.
    ap-tr : ∀ {a a′ : AllocState {FS}} → (∀ l′ → Live a l′ → Live a′ l′)
          → ∀ {m v lc st} → AnaP m a v lc st → AnaP m a′ v lc st
    ap-tr bft (ana-p x lmm cp slb c0) =
      ana-p x lmm cp (bft _ slb) (cellWF-heap-transport (λ _ → ⊤) (λ _ _ → tt) (λ _ _ → refl) bft x _ tt c0)

    live-pred : ∀ {a : AllocState {FS}} {lc : ValueLocation FS} → LocMatchesMode Heap lc → Live a (sucLoc lc) → Live a lc
    live-pred {lc = AtDynamic _} _ (BeforeFrontier.heap-before r<h) = BeforeFrontier.heap-before r<h

    ap-tr′ : ∀ {a a′ : AllocState {FS}} {st st′ : LocState FS}
           → (∀ l′ → Live a l′ → Live a′ l′) → (∀ l′ → Live a l′ → readLoc st′ l′ ≡ readLoc st l′)
           → ∀ {m v lc} → AnaP m a v lc st → AnaP m a′ v lc st′
    ap-tr′ {a} bft rdq (ana-p x lmm cp slb c0) =
      ana-p x lmm (trans (rdq _ slb) cp) (bft _ slb)
            (cellWF-heap-transport (Live a) (λ _ b → b) rdq bft x _ (live-pred lmm slb) c0)

    arith-span : ∀ k′ c b → suc (suc (c + k′)) + b ≡ k′ + (c + suc (suc b))
    arith-span k′ c b = solve 3 (λ k′ c b → con 2 :+ (c :+ k′) :+ b := k′ :+ (c :+ (con 2 :+ b))) refl k′ c b

    arith-lab : ∀ jj c b → (jj + suc (suc c)) + b ≡ jj + (c + suc (suc b))
    arith-lab jj c b = solve 3 (λ jj c b → (jj :+ (con 2 :+ c)) :+ b := jj :+ (c :+ (con 2 :+ b))) refl jj c b

    arith-end′ : ∀ c r b → r + (c + suc (suc b)) ≡ suc (suc (c + r)) + b
    arith-end′ c r b = solve 3 (λ c r b → r :+ (c :+ (con 2 :+ b)) := (con 2 :+ (c :+ r)) :+ b) refl c r b

    mutual
      lay-tr : ∀ {G : IRFunctor} → WellFormedFI G → ∀ {a a′ : AllocState {FS}} → (∀ l′ → Live a l′ → Live a′ l′)
             → ∀ {m v lc st} → LayerV G {ν-type F} AP m a v lc st → LayerV G {ν-type F} AP m a′ v lc st
      lay-tr (wf-K ib) bft lv =
        valid→fo (fo-base ib) (validityWF-heap-transport {prog = prog} (λ _ → ⊤) (λ _ _ → tt) (λ _ _ → refl) bft _ _ tt (fo→valid lv))
      lay-tr wf-Id bft lv = ap-tr bft lv
      lay-tr (wf-Sum f g) bft (inl-wf lmm tg pp pb slb pv) = inl-wf lmm tg pp (bft _ pb) (bft _ slb) (lay-tr f bft pv)
      lay-tr (wf-Sum f g) bft (inr-wf lmm tg pp pb slb pv) = inr-wf lmm tg pp (bft _ pb) (bft _ slb) (lay-tr g bft pv)
      lay-tr (wf-Sum f g) bft (inl-reg-wf lmm tg rep pp slb) = inl-reg-wf lmm tg rep pp (bft _ slb)
      lay-tr (wf-Sum f g) bft (inr-reg-wf lmm tg rep pp slb) = inr-reg-wf lmm tg rep pp (bft _ slb)
      lay-tr (wf-Prod f g) bft (pair-wf lmm slb c₁ c₂) = pair-wf lmm (bft _ slb) (cell-tr f bft c₁) (cell-tr g bft c₂)

      cell-tr : ∀ {G : IRFunctor} → WellFormedFI G → ∀ {a a′ : AllocState {FS}} → (∀ l′ → Live a l′ → Live a′ l′)
              → ∀ {c cl st} → CellAtP {⟦ G ⟧TI (ν-type F)} (LayerV G {ν-type F} AP) a c cl st
              → CellAtP {⟦ G ⟧TI (ν-type F)} (LayerV G {ν-type F} AP) a′ c cl st
      cell-tr w bft (cell-ptr r bf v)   = cell-ptr r (bft _ bf) (lay-tr w bft v)
      cell-tr w bft (cell-inline rep r) = cell-inline rep r

    across : ∀ {m a ca v st} {a′ : AllocState {FS}} → (∀ l′ → Live a l′ → Live a′ l′)
           → ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} AP) m a ca v st
           → ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} AP) m a′ a′ v st
    across bft (rp-unit e) = rp-unit e
    across bft (rp-loc loc v bf rax _ _) = rp-loc loc (lay-tr wf bft v) (bft loc bf) rax (lay-tr wf bft v) (bft loc bf)
    across bft (rp-reg fit rax) = rp-reg fit rax

    module Block (j : ℕ) (feq : find-thunk prog (ℓ o l) ≡ just j)
                 (sp : SpanAt prog j (block-layout (ℓ o l , bb , body)))
                 (lab : LabelsAt prog (suc j) body)
                 (bl′ : BlocksAt prog (blocks 1 (suc l) coalg)) where

      -- ── THE BODY'S RUN. Two rows keep the seed pair's pointer in slot 0; the
      -- coalgebra runs from frontier 1 (its own correctness, `ihc`), which
      -- leaves slot 0 alone; the re-suspension (`Resusp`) rebuilds its layer.
      module Body (x : ValueDomain.⟦ E IRTy′.* A ⟧ᴰᴵ) (fs : FlatState) (pre : AllocState {FS})
                  (mIn : AllocMode) (ret-pc k : ℕ) (rs : List ℕ)
                  (nh : halted (floc fs) ≡ false) (fa : falloc fs ≡ enter-call pre) (ns : next-slot pre ≡ 0)
                  (pl : ValueLocation FS)
                  (pv : ValidAtWF {prog = prog} mIn (BC.callee-alloc bb fs) {E IRTy′.* A} x pl (BC.callee-loc bb fs))
                  (bfp : Live (BC.callee-alloc bb fs) pl)
                  (rd : readReg (regs (BC.callee-loc bb fs)) Input1 ≡ SV-Ptr pl) where

        s     = BC.callee-loc bb fs
        alloc = BC.callee-alloc bb fs
        cl    = fclosure fs
        rs′   = ret-pc ∷ rs
        base  = suc j
        e     = proj₁ x
        M     = evalᴰ coalg x
        cb    = proj₁ (ir-to-trace' 1 (suc l) coalg)
        l2    = proj₁ (proj₂ (ir-to-trace' 1 (suc l) coalg))
        rt    = proj₂ (proj₂ rsp)
        rsdF  = AnaDen.rsd wf coalg e wf
        comp  = fmap∞ rsdF M

        mk-child : ∀ {a′c ν-loc st} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                 → LocMatchesMode Heap ν-loc → readLoc st (sucLoc ν-loc) ≡ just (SV-Code (ℓ o l))
                 → Live a′c (sucLoc ν-loc) → CellAt {prog = prog} a′c (E IRTy′.* A) (e , a′) ν-loc st
                 → AnaP Heap a′c (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc st
        mk-child a′ lmm cp slb c0 = ana-p (e , a′) lmm cp slb c0

        module RS = ResuspC.Resusp {FS} wf coalg e prog l AP mk-child ap-tr′

        arith-end : DL.length rt + (DL.length ctrace + suc (suc base)) ≡ DL.length body + base
        arith-end = trans (arith-end′ (DL.length ctrace) (DL.length rt) base)
                          (cong (λ z → suc (suc z) + base) (sym (length-++ ctrace)))

        span-b : SpanAt prog base body
        span-b = BC.Layout.body-span prog (e-thunk (ℓ o l)) bb j body sp

        ns0 : next-slot alloc ≡ 0
        ns0 = trans (cong next-slot fa) ns

        fs0 fs1 fs2 : FlatState
        fs0 = entry-flat base s alloc cl rs′
        fs1 = flat-exec-instr mov-to-output prog fs0
        fs2 = flat-exec-instr (store-at-slot 0) prog fs1

        nh1 : halted (floc fs1) ≡ false
        nh1 = exec-abstract-preserves-halted-WF mov-to-output s alloc nh tt
        nh2 : halted (floc fs2) ≡ false
        nh2 = exec-abstract-preserves-halted-WF (store-at-slot 0) (floc fs1) (falloc fs1) nh1 tt

        pre-chain : FlatSteps prog 2 fs0 fs2
        pre-chain = (nh , span-b 0 _ refl) ∷ (nh1 , span-b 1 _ refl) ∷ []

        mem01 : ∀ (lc : ValueLocation FS) → readLoc (floc fs1) lc ≡ readLoc s lc
        mem01 lc = mem-untouched mov-to-output s alloc lc nhw-mov-to-output refl

        memS : ∀ (lc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = 0 }) lc
             → readLoc (floc fs2) lc ≡ readLoc (floc fs1) lc
        memS lc bf = store-slot-preserves-before 0 (floc fs1) (record alloc { next-slot = 0 }) (falloc fs1) lc refl z≤n bf

        mem02 : ∀ (lc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = 0 }) lc
              → readLoc (floc fs2) lc ≡ readLoc s lc
        mem02 lc bf = trans (memS lc bf) (mem01 lc)

        heap02 : ∀ (lc : ValueLocation FS) → Live alloc lc → readLoc (floc fs2) lc ≡ readLoc s lc
        heap02 lc b = mem02 lc (live-ns 0 b)

        out1 : readReg (regs (floc fs1)) Output ≡ SV-Ptr pl
        out1 = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) rd

        in2 : readReg (regs (floc fs2)) Input1 ≡ SV-Ptr pl
        in2 = trans (cong (λ r → readReg r Input1)
                          (SMCore.MemOps.writeLoc-regs (floc fs1) (AtStack (current-frame alloc) 0) (readReg (regs (floc fs1)) Output)))
                    (trans (writeReg-preserves (regs s) Output Input1 (readReg (regs s) Input1) (λ ())) rd)

        slot0 : readLoc (floc fs2) (AtStack (current-frame alloc) 0) ≡ just (SV-Ptr pl)
        slot0 = trans (SMCore.MemOps.writeLoc-read-same-stack (floc fs1) (current-frame alloc) 0 (readReg (regs (floc fs1)) Output))
                      (cong just out1)

        log2 : LocState.ev-log (floc fs2) ≡ LocState.ev-log s
        log2 = trans (log-abstract (store-at-slot 0) tt (floc fs1) (falloc fs1)) (log-abstract mov-to-output tt s alloc)

        inp2 : InputAt {prog = prog} {E IRTy′.* A} mIn alloc x (floc fs2)
        inp2 = in-loc pl (validityWF-heap-transport (Live alloc) (λ _ b → b) heap02 (λ _ b → b) x pl bfp pv) bfp in2

        -- the coalgebra's text and labels, inside the body
        span-c : SpanAt prog (suc (suc base)) ctrace
        span-c k′ i eq = subst (λ z → fetch prog z ≡ just i) (sym (trans (+-suc k′ (suc base)) (cong suc (+-suc k′ base))))
                               (span-b (suc (suc k′)) i (fetch-++-left ctrace rt k′ i eq))

        labs-c : LabelsIn (suc l) l2 ctrace
        labs-c = labels-in coalg 1 (suc l)

        labs-r : LabelsIn l2 (proj₁ (proj₂ rsp)) rt
        labs-r = resuspend-labels-in l2 (proj₁ (proj₂ rsp)) cb l2 (ℓ o l) 0 wf ≤-refl ≤-refl

        lab-c : LabelsAt prog (suc (suc base)) ctrace
        lab-c m jj eq =
          subst (λ z → find-label prog m ≡ just z) (+-assoc jj 2 base)
            (lab m (jj + 2) (trans (fl-go-prefix ctrace rt m 2 (jj + 2)
                                      (trans (fl-go-shift ctrace m 2 0) (cong (DM.map (_+ 2)) eq))) refl))

        mrc : MachineRefinesObsF prog (suc (suc base)) 1 (suc l) coalg x (floc fs2) (falloc fs2) cl rs′ k
        mrc = ihc 1 (suc l) prog (suc (suc base)) ss cr span-c bl′ lab-c mIn x (floc fs2) (falloc fs2) cl ns0 nh2 inp2 k rs′

        vr = MachineRefinesObsF.value-realized mrc
        module VR = ValueRealized vr
        S0 = VR.settle

        BR : Set
        BR = BC.BodyRuns prog base (DL.length body) {⟦ F ⟧TI (ν-type F)}
               (ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} AP)) comp s alloc cl rs′ k

        -- the composite's run is the coalgebra's, its result re-suspended
        RC-eq : runAt s (⟪ comp ⟫ k) ≡ mapRun rsdF (runAt (floc fs2) (⟪ M ⟫ k))
        RC-eq = trans (run-fmap ιᶠ (LocState.ev-log s) k M rsdF)
                      (cong (mapRun rsdF) (cong (λ h → TM.run ιᶠ h (⟪ M ⟫ k)) (sym log2)))

        ρM = resultAt (floc fs2) (⟪ M ⟫ k)

        res-c : resultAt s (⟪ comp ⟫ k) ≡ mapRes (mapAp rsdF) ρM
        res-c = cong proj₂ RC-eq

        ev-c : eventsAt s (⟪ comp ⟫ k) ≡ eventsAt (floc fs2) (⟪ M ⟫ k)
        ev-c = cong proj₁ RC-eq

        stop-map : ∀ (ρ : Res (Ap ValueDomain.⟦ ⟦ F ⟧TI A ⟧ᴰᴵ)) → is-stopped (mapRes (mapAp rsdF) ρ) ≡ is-stopped ρ
        stop-map stopped     = refl
        stop-map (returns _) = refl

        budget-map : ∀ (ρ : Res (Ap ValueDomain.⟦ ⟦ F ⟧TI A ⟧ᴰᴵ)) → budgetLeft k (mapRes (mapAp rsdF) ρ) ≡ budgetLeft k ρ
        budget-map stopped              = refl
        budget-map (returns cut)        = refl
        budget-map (returns (done _ _)) = refl

        nc-map : ∀ (ρ : Res (Ap ValueDomain.⟦ ⟦ F ⟧TI A ⟧ᴰᴵ)) → NotCut (mapRes (mapAp rsdF) ρ) → NotCut ρ
        nc-map stopped              p = p
        nc-map (returns (done _ _)) p = p

        stops-c : stopsAt s (⟪ comp ⟫ k) ≡ stopsAt (floc fs2) (⟪ M ⟫ k)
        stops-c = trans (cong is-stopped res-c) (stop-map ρM)

        nc-c : NotCut (resultAt s (⟪ comp ⟫ k)) → NotCut ρM
        nc-c nc = nc-map ρM (subst NotCut res-c nc)

        budget-c : budgetLeft k (resultAt s (⟪ comp ⟫ k)) ≡ budgetLeft k ρM
        budget-c = trans (cong (budgetLeft k) res-c) (budget-map ρM)

        bf-up : ∀ (m′ : ℕ) (lc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = 0 }) lc
              → BeforeFrontier (record alloc { next-slot = m′ }) lc
        bf-up m′ = frontier-monotone (record alloc { next-slot = 0 }) (record alloc { next-slot = m′ }) refl z≤n ≤-refl

        -- NOT RETURNED: the coalgebra's run is the whole run.
        stuck : (∀ {v r} → ρM ≡ returns (done v r) → ⊥) → BR
        stuck nr =
          BC.body-runs (2 + VR.steps) S0 VR.out-mode VR.cont-alloc (FlatSteps-++ pre-chain VR.run)
            (λ p → VR.live (trans (sym stops-c) p))
            (λ p → ⊥-elim (nr′ p))
            (λ p → proj₁ (VR.stops (trans (sym stops-c) p))
                 , trans (proj₂ (VR.stops (trans (sym stops-c) p))) (chain-left pre-chain nh2))
            (λ p → ⊥-elim (nr′ p))
            (λ nc → VR.no-link (nc-c nc))
            (trans VR.log (cong₂ DL._++_ log2 (sym ev-c)))
            (λ p → ⊥-elim (nr′ p))
            (progress-≤ (subst (λ b → k ≤ b + chain-ctrls VR.run) (sym budget-c) VR.progress) (ctrls-≤ʳ pre-chain VR.run))
            (trans (chain-events-++ pre-chain VR.run) (trans (MachineRefinesObsF.traces-agree mrc) (sym ev-c)))
            (λ nc lc bf → trans (vr-mem-pres vr (nc-c nc) lc (bf-up 1 lc bf)) (mem02 lc bf))
            (λ p → ⊥-elim (nr′ p))
            (λ nc m′ lc bf → VR.bf-mono (nc-c nc) m′ lc bf)
            (λ p → ⊥-elim (nr′ p))
          where
            nr′ : ∀ {v r} → resultAt s (⟪ comp ⟫ k) ≡ returns (done v r) → ⊥
            nr′ p = unmap ρM refl (trans (sym res-c) p)
              where
                unmap : ∀ (ρ : Res (Ap ValueDomain.⟦ ⟦ F ⟧TI A ⟧ᴰᴵ)) {v r} → ρM ≡ ρ → mapRes (mapAp rsdF) ρ ≡ returns (done v r) → ⊥
                unmap (returns (done y r′)) e _ = nr e
                unmap stopped               e ()
                unmap (returns cut)         e ()

        -- RETURNED: the re-suspension runs from where the coalgebra stopped.
        module Ret (y : ValueDomain.⟦ ⟦ F ⟧TI A ⟧ᴰᴵ) (r′ : ℕ) (eq : ρM ≡ returns (done y r′)) where
          nc0 : NotCut ρM
          nc0 = subst NotCut (sym eq) tt

          nh0 : halted (floc S0) ≡ false
          nh0 = VR.live (cong is-stopped eq)

          cf0 : current-frame (falloc S0) ≡ current-frame alloc
          cf0 = VR.frame-pres eq

          ns-S0 : next-slot (falloc S0) ≡ 0
          ns-S0 = trans (trans (cong (λ st → next-slot (falloc st)) (sym run≡))
                               (flat-run-keeps-next-slot VR.steps prog ss (suc (suc base)) (floc fs2) (falloc fs2) cl rs′))
                        ns0
            where
              run≡ : exec-flat VR.steps prog (entry-flat (suc (suc base)) (floc fs2) (falloc fs2) cl rs′) ≡ S0
              run≡ = trans (cong (λ m′ → exec-flat m′ prog (entry-flat (suc (suc base)) (floc fs2) (falloc fs2) cl rs′))
                                 (sym (+-identityʳ VR.steps)))
                           (exec-flat-steps VR.run 0)

          slot0-S0 : readLoc (floc S0) (AtStack (current-frame (falloc S0)) 0) ≡ just (SV-Ptr pl)
          slot0-S0 = subst (λ f → readLoc (floc S0) (AtStack f 0) ≡ just (SV-Ptr pl)) (sym cf0)
                       (trans (VR.stack-pres nc0 (current-frame alloc) 0 (BeforeFrontier.stack-before refl (s≤s z≤n))) slot0)

          liveS0 : ∀ (lc : ValueLocation FS) → Live alloc lc → Live (falloc S0) lc
          liveS0 (AtDynamic hl) b with VR.bf-mono nc0 0 (AtDynamic hl) (live-ns 0 b)
          ... | BeforeFrontier.heap-before r<h = BeforeFrontier.heap-before r<h

          memS0 : ∀ (lc : ValueLocation FS) → Live alloc lc → readLoc (floc S0) lc ≡ readLoc s lc
          memS0 lc b = trans (vr-mem-pres vr nc0 lc (live-ns 1 b)) (heap02 lc b)

          env-c : CellAt {prog = prog} (falloc S0) E e pl (floc S0)
          env-c = cellWF-heap-transport (Live alloc) (λ _ b → b) memS0 liveS0 e pl bfp
                    (PairValidWF.fst-cell (decomposePairWF pv))

          place→out : ∀ {B m a ca v st} → ResultPlace {prog = prog} B m a ca v st → RS.OutAt {B} a v st
          place→out (at-loc loc v lv rax _ _) = RS.out-loc loc v lv rax
          place→out (at-reg fit rax)          = RS.out-reg fit rax
          place→out unit-result               = RS.out-unit refl

          span-r : SpanAt prog (fpc S0) rt
          span-r k′ i eq′ =
            subst (λ z → fetch prog z ≡ just i)
                  (trans (arith-span k′ (DL.length ctrace) base) (cong (k′ +_) (sym (VR.at-end eq))))
                  (span-b (suc (suc (DL.length ctrace + k′))) i (trans (fetch-++-right ctrace rt k′) eq′))

          lab-r : LabelsAt prog (fpc S0) rt
          lab-r m jj eq′ =
            subst (λ z → find-label prog m ≡ just z)
                  (trans (arith-lab jj (DL.length ctrace) base) (cong (jj +_) (sym (VR.at-end eq))))
                  (lab m (jj + suc (suc (DL.length ctrace))) scan)
            where
              inW = proj₁ (found-in-window rt m jj eq′ labs-r)
              noC = noLabel-outside m ctrace labs-c (λ w → 1+n≰n (≤-trans (proj₂ w) inW))
              scan : find-label body m ≡ just (jj + suc (suc (DL.length ctrace)))
              scan = trans (fl-go-skip ctrace rt m 2 noC)
                           (trans (fl-go-shift rt m (suc (suc (DL.length ctrace))) 0)
                                  (cong (DM.map (_+ suc (suc (DL.length ctrace)))) eq′))

          rr = RS.resusp wf cb l2 S0 y pl span-r lab-r nh0 (VR.no-link nc0) ns-S0 (frontier-mono coalg 1 (suc l))
                 slot0-S0 (liveS0 pl bfp) env-c (place→out (VR.place eq))
          module RR = RS.RRuns rr

          done-inj : ∀ {X : Set} {a b : X} {r₁ r₂} → returns (done a r₁) ≡ returns (done b r₂) → a ≡ b
          done-inj refl = refl

          runs : BR
          runs =
            BC.body-runs (2 + (VR.steps + RR.steps)) RR.settle RR.out-mode (falloc RR.settle)
              (FlatSteps-++ pre-chain (FlatSteps-++ VR.run RR.run))
              (λ _ → RR.nh)
              (λ _ → trans RR.pc (trans (cong (DL.length rt +_) (VR.at-end eq)) arith-end))
              (λ p → ⊥-elim (BC.true≢false (trans (sym p) (trans stops-c (cong is-stopped eq)))))
              (λ _ → trans RR.ret (VR.no-ret eq))
              (λ _ → RR.lnk)
              (trans RR.log (trans VR.log (cong₂ DL._++_ log2 (sym ev-c))))
              (λ p → subst (λ w → ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} AP) RR.out-mode
                                     (falloc RR.settle) (falloc RR.settle) w (floc RR.settle))
                           (done-inj (trans (sym (trans res-c (cong (mapRes (mapAp rsdF)) eq))) p)) RR.out)
              (progress-≤ (subst (λ b → k ≤ b + chain-ctrls VR.run) (sym budget-c) VR.progress)
                          (≤-trans (ctrls-≤ˡ VR.run RR.run) (ctrls-≤ʳ pre-chain (FlatSteps-++ VR.run RR.run))))
              (trans (chain-events-++ pre-chain (FlatSteps-++ VR.run RR.run))
                (trans (chain-events-++ VR.run RR.run)
                  (trans (cong₂ DL._++_ (MachineRefinesObsF.traces-agree mrc) RR.ev)
                         (trans (++-identityʳ _) (sym ev-c)))))
              (λ nc lc bf → trans (RR.mem lc (VR.bf-mono nc0 cb lc (bf-up cb lc bf)))
                                  (trans (vr-mem-pres vr nc0 lc (bf-up 1 lc bf)) (mem02 lc bf)))
              (λ _ → trans RR.cf cf0)
              (λ nc m′ lc bf → RR.bf-mono m′ lc (VR.bf-mono nc0 m′ lc bf))
              (λ _ → trans RR.sf (VR.frames-pres eq))

        go : ∀ (ρ : Res (Ap ValueDomain.⟦ ⟦ F ⟧TI A ⟧ᴰᴵ)) → ρM ≡ ρ → BR
        go (returns (done y r′)) eq = Ret.runs y r′ eq
        go stopped               eq = stuck (λ p → noS (trans (sym eq) p))
          where noS : ∀ {v r} → stopped ≡ returns (done v r) → ⊥
                noS ()
        go (returns cut)         eq = stuck (λ p → noC (trans (sym eq) p))
          where noC : ∀ {v r} → returns cut ≡ returns (done v r) → ⊥
                noC ()

        body-run : BR
        body-run = go ρM refl

      ana-body : ∀ (x : ValueDomain.⟦ E IRTy′.* A ⟧ᴰᴵ) (fs : FlatState) (pre : AllocState {FS})
                   (mIn : AllocMode) (ret-pc k : ℕ) (rs : List ℕ)
        → halted (floc fs) ≡ false → falloc fs ≡ enter-call pre → next-slot pre ≡ 0
        → InputAt {prog = prog} {E IRTy′.* A} mIn (BC.callee-alloc bb fs) x (BC.callee-loc bb fs)
        → BC.BodyRuns prog (suc j) (DL.length body) {⟦ F ⟧TI (ν-type F)}
            (ResultPlaceP {⟦ F ⟧TI (ν-type F)} (LayerV F {ν-type F} AP))
            (fmap∞ (AnaDen.rsd wf coalg (proj₁ x) wf) (evalᴰ coalg x))
            (BC.callee-loc bb fs) (BC.callee-alloc bb fs) (fclosure fs) (ret-pc ∷ rs) k
      ana-body x fs pre mIn ret-pc k rs nh fa ns (in-loc pl pv bfp rd) =
        Body.body-run x fs pre mIn ret-pc k rs nh fa ns pl pv bfp rd
      ana-body x fs pre mIn ret-pc k rs nh fa ns (in-reg () _)
      ana-body x fs pre mIn ret-pc k rs nh fa ns (in-unit ())

      -- ONE FORCE: the block call, its body's run, and what that run means.
      ana-force : ∀ {alloc ν-loc st} (x : ValueDomain.⟦ E IRTy′.* A ⟧ᴰᴵ)
                  (c0 : CellAt {prog = prog} alloc (E IRTy′.* A) x ν-loc st)
                → ForceRuns {prog = prog} {F} AP alloc st (cell-sv c0) j (retVal (evalᴰ (Ana wf coalg) x))
      ana-force {alloc} {ν-loc} {st} x c0 wf′ fs pre ret-pc k rs pc nh fr fa ns incl agree i1 =
        crun-retarget (AnaDen.out-ana wf coalg (proj₁ x) wf′ (proj₂ x) k (floc fs))
          (BC.block-call-gen {⟦ F ⟧TI (ν-type F)} across body (fmap∞ (AnaDen.rsd wf coalg (proj₁ x) wf) (evalᴰ coalg x))
             prog (ℓ o l) bb j sp fs pre ret-pc k rs pc nh fr fa
             (ana-body x fs pre (cell-mode c0) ret-pc k rs nh fa ns (callee-input c0 i1)))
        where
          live-pre : ∀ l′ → Live alloc l′ → Live (BC.callee-alloc bb fs) l′
          live-pre l′ b = BC.live-callee bb fs pre fa l′ (incl l′ b)

          callee-input : (ce : CellAt {prog = prog} alloc (E IRTy′.* A) x ν-loc st)
                       → readReg (regs (floc fs)) Input1 ≡ cell-sv ce
                       → InputAt {prog = prog} {E IRTy′.* A} (cell-mode ce) (BC.callee-alloc bb fs) x (BC.callee-loc bb fs)
          callee-input (cell-ptr {comp-loc = pl} r bf v) i =
            in-loc pl
              (validityWF-heap-transport (Live alloc) (λ _ b → b)
                 (λ l′ b → trans (BC.callee-heap bb fs l′ (incl l′ b)) (agree l′ b))
                 live-pre x pl bf v)
              (live-pre pl bf) i
          callee-input (cell-inline (rep-prim fit) r) i = in-reg fit i
          callee-input (cell-inline (rep-unit e _) r) i = in-unit e

      ana-step : ∀ {m a v lc st} → AnaP m a v lc st → NuStep {prog = prog} {F} AP m a v lc st
      ana-step (ana-p x lmm cp slb c0) = record
        { st-mode  = refl
        ; st-heap  = lmm
        ; st-seed  = cell-sv c0
        ; st-lbl   = ℓ o l
        ; st-j     = j
        ; st-cell0 = cell-read c0
        ; st-cell1 = cp
        ; st-live1 = slb
        ; st-code  = feq
        ; st-force = ana-force x c0
        }

      -- THE ν: every `Ana` suspension of a valid seed is a `NuV`.
      ana-nu : ∀ {m a v lc st} → AnaP m a v lc st → NuV {prog = prog} {F} m a v lc st
      ana-nu = NuCoind.coind {prog = prog} AP ana-step
