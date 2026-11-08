-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterRoundsCont
--
-- plan 0.119 D5, the continue path of one round (split from IterRounds,
-- plan 0.144): the round returned `inr a′` with budget `suc r″`; the back
-- edge runs (`IterCont`), then the rounds from the next entry at `r″` — the
-- induction hypothesis `rec`. The back edge is a control step, so `progress`
-- holds.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterRoundsCont (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.CCC.Machine.SMCore
  using (AllocState; AbstractTrace; LocState; StoredValue; module LocState; module AllocState)
open AllocState using (next-slot; current-frame; saved-frames; next-heap-ref)
open LocState using (halted; regs)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (+-monoˡ-≤; +-monoʳ-≤; ≤-pred)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)
open import Once.IRTy using (IRTy)
import Once.IRTy as IRT
open import Once.Res using (Res; stopped; returns; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft; thenIter; run-approx-iter; done-≤; done-value)
import Once.IR.Semantics.Trace as TM
import Data.List.Properties as DLP

open import Once.CCC.Codegen.IRObsCorrect.IterShape o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterRun o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterInv o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterExit o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterCont o tbl
open import Once.CCC.Codegen.IRObsCorrect.IterBody o tbl

module IterRoundsContC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open IterShapeC {FS}
  open IterRunC {FS}
  open IterInvC {FS}
  open IterExitC {FS}
  open IterContC {FS}
  open IterBodyC {FS}

  -- the composite's progress: the round left `suc r″`, the rounds from the
  -- next entry ran at `r″`, and the back edge is at least one control step.
  prog-arith : ∀ (x r r″ cB cC cR : ℕ) → r ≤ suc r″ + cB → r″ ≤ x + cR → 1 ≤ cC → r ≤ x + (cB + (cC + cR))
  prog-arith x r r″ cB cC cR p1 p2 p3 =
    ≤-trans p1 (≤-trans (+-monoˡ-≤ cB (s≤s p2))
      (≤-trans (≤-reflexive (eq x cB cR)) (+-monoʳ-≤ x (+-monoʳ-≤ cB (+-monoˡ-≤ cR p3)))))
    where
      eq : ∀ (x cB cR : ℕ) → suc (x + cR) + cB ≡ x + (cB + (1 + cR))
      eq = solve 3 (λ x cB cR → (con 1 :+ (x :+ cR)) :+ cB := x :+ (cB :+ (con 1 :+ cR))) refl

  prog-cont : ∀ {X : Set} (r r″ cB cC cR : ℕ) (ρ : Res (Ap X)) → r ≤ suc r″ + cB → r″ ≤ budgetLeft r″ ρ + cR → 1 ≤ cC
            → r ≤ budgetLeft r ρ + (cB + (cC + cR))
  prog-cont r r″ cB cC cR stopped              _  _  _  = m≤m+n r _
  prog-cont r r″ cB cC cR (returns (done v x)) p1 p2 p3 = prog-arith x r r″ cB cC cR p1 p2 p3
  prog-cont r r″ cB cC cR (returns cut)        p1 p2 p3 = prog-arith 0 r r″ cB cC cR p1 p2 p3

  -- The continue path's log, over plain lists (plan 0.144: the same chain written
  -- inline on the machine states cost cont-run 13 s and 1.4 GB of unification).
  log-glue : ∀ {X : Set} {x y E L : DL.List X} (h es₁ : DL.List X)
           → x ≡ y DL.++ L → y ≡ h DL.++ es₁ → E ≡ es₁ DL.++ L → x ≡ h DL.++ E
  log-glue {L = L} h es₁ p q r = trans p (trans (cong (DL._++ L) q) (trans (++-assoc h es₁ L) (cong (h DL.++_) (sym r))))

  module ContRun {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A))
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (Iter body)))
    (ihb : IRObsCorrectF body)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (bl : BlocksAt prog (blocks n l (Iter body)))
    (la : LabelsAt prog base (emitted n l (Iter body)))
    (Z : Loop.Anchor body n l base prog)
    where

    open IterShape body n l
    open IterRun body n l prog base span
    open Loop body n l base
    open Anchor Z
    module VR = ValueRealized

    module At (σ : FlatState) (a : ⟦ A ⟧) (inv : RoundInv Z σ a) (r : ℕ)
      (rec : ∀ (r″ : ℕ) → suc r″ ≤ r → ∀ (σ′ : FlatState) (a′ : ⟦ A ⟧) → RoundInv Z σ′ a′ → RoundsRun Z prog σ′ a′ r″)
      where
      open Body body n l prog base span ihb ss cr bl la Z σ a inv r
      h = SMCore.LocState.ev-log (floc σ)
      es₁ = eventsAt (floc σ) (⟪ round e a ⟫ r)

      RE : runAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ thenIter ιᶠ h es₁ ρ₁ (round e)
      RE = run-approx-iter ιᶠ h r (round e a) (round e)

      cont-run : ∀ (a′ : ⟦ A ⟧) (r″ : ℕ) (q : ρ₁ ≡ returns (done (inj₂ a′) (suc r″)))
               → ResultPlace {prog = prog} (B IRT.+ A) (VR.out-mode vb) (falloc S0) (VR.cont-alloc vb) (inj₂ a′) (floc S0)
               → RoundsRun Z prog σ a r
      cont-run a′ r″ q (at-loc loc vS bef rax _ _) = record
        { steps = VR.steps vb + (_ + RoundsRun.steps rr) ; settle = RoundsRun.settle rr
        ; out-mode = RoundsRun.out-mode rr ; cont-alloc = RoundsRun.cont-alloc rr
        ; run = FlatSteps-++ chainB (FlatSteps-++ C.chain (RoundsRun.run rr))
        ; live = λ p → RoundsRun.live rr (trans (cong is-stopped (sym res)) p)
        ; at-end = λ p → RoundsRun.at-end rr (trans (sym res) p)
        ; stops = λ p → RoundsRun.stops rr (trans (cong is-stopped (sym res)) p)
        ; no-ret = λ p → RoundsRun.no-ret rr (trans (sym res) p)
        ; no-link = λ nc′ → RoundsRun.no-link rr (subst NotCut res nc′)
        ; place = λ p → RoundsRun.place rr (trans (sym res) p)
        ; events = trans (chain-events-++ chainB (FlatSteps-++ C.chain (RoundsRun.run rr)))
                     (trans (cong₂ DL._++_ ev-chainB
                               (trans (chain-events-++ C.chain (RoundsRun.run rr))
                                      (cong₂ DL._++_ C.ev-chain (RoundsRun.events rr))))
                            (sym evs))
        ; log = log-glue h es₁ (RoundsRun.log rr) logσ′ evs
        ; progress = subst (λ m → r ≤ budgetLeft r (resultAt (floc σ) (⟪ loopFrom e a ⟫ r)) + m)
                       (sym (trans (chain-ctrls-++ chainB (FlatSteps-++ C.chain (RoundsRun.run rr)))
                                   (cong (chain-ctrls chainB +_) (chain-ctrls-++ C.chain (RoundsRun.run rr)))))
                       (subst (λ ρ → r ≤ budgetLeft r ρ + (chain-ctrls chainB + (chain-ctrls C.chain + chain-ctrls (RoundsRun.run rr))))
                              (sym res)
                         (prog-cont r r″ (chain-ctrls chainB) (chain-ctrls C.chain) (chain-ctrls (RoundsRun.run rr))
                            (resultAt (floc C.σ′) (⟪ loopFrom e a′ ⟫ r″))
                            (subst (λ m → r ≤ suc r″ + m) (sym ctrls-chainB)
                               (subst (λ ρ → r ≤ budgetLeft r ρ + chain-ctrls (VR.run vb)) q (VR.progress vb)))
                            (RoundsRun.progress rr) C.ctrls-chain))
        ; mem0 = λ nc′ → RoundsRun.mem0 rr (subst NotCut res nc′)
        ; frame = λ p → RoundsRun.frame rr (trans (sym res) p)
        ; frames = λ p → RoundsRun.frames rr (trans (sym res) p)
        ; bf0 = λ nc′ → RoundsRun.bf0 rr (subst NotCut res nc′)
        ; bk0 = λ nc′ → RoundsRun.bk0 rr (subst NotCut res nc′)
        }
        where
          nc : NotCut ρ₁
          nc = subst NotCut (sym q) tt
          ns : stopsAt (floc σ) (⟪ round e a ⟫ r) ≡ false
          ns = cong is-stopped q
          module C = Cont body n l prog base span la Z S0 a′ (Live.nh0 ns) (pc0-of q)
                       (cf0-of q) (sf0-of q) ns0 (NC.hr0 nc) (NC.memF0 nc) (NC.env0 nc) (ret0-of q) (NC.lnk0 nc)
                       (NC.mem00 nc) (NC.bf00 nc) (Live.left0 ns) (NC.bkF0 nc) (NC.bk00 nc) loc vS bef rax
          lt : suc r″ ≤ r
          lt = done-≤ ιᶠ h r (round e a) q
          rr : RoundsRun Z prog C.σ′ a′ r″
          rr = rec r″ lt C.σ′ a′ C.next-inv
          logσ′ : SMCore.LocState.ev-log (floc C.σ′) ≡ h DL.++ es₁
          logσ′ = trans C.log-chain (VR.log vb)
          RE′ : runAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ TM.appE es₁ (runAt (floc C.σ′) (⟪ loopFrom e a′ ⟫ r″))
          RE′ = trans RE (trans (cong (λ ρ → thenIter ιᶠ h es₁ ρ (round e)) q)
                                (cong (λ hh → TM.appE es₁ (TM.run ιᶠ hh (⟪ loopFrom e a′ ⟫ r″))) (sym logσ′)))
          res : resultAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ resultAt (floc C.σ′) (⟪ loopFrom e a′ ⟫ r″)
          res = cong proj₂ RE′
          evs : eventsAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ es₁ DL.++ eventsAt (floc C.σ′) (⟪ loopFrom e a′ ⟫ r″)
          evs = cong proj₁ RE′
