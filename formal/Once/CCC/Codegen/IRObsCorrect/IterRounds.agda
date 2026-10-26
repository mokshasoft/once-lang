-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.IterRounds
--
-- plan 0.119 D5: THE ROUNDS, by induction on the round budget. From a round
-- entry the body's witness runs the round; its budgeted result decides the
-- rest (`Approx.run-approx-iter`):
--
--   * stopped or cut: the loop stopped or was cut inside the round;
--   * `inl b`: the exit path, the loop returns `b`;
--   * `inr a′` with no budget left: the loop is cut at its silent step;
--   * `inr a′` with budget `suc r″`: the continue path, then the rounds from
--     the next entry at `r″` — the induction hypothesis. The back edge is a
--     control step, so `progress` holds: each silent step the meaning takes
--     costs the machine at least one control step.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.IterRounds (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.CCC.Machine.SMCore
  using (AllocState; AbstractTrace; LocState; StoredValue; module LocState; module AllocState)
open AllocState using (next-slot; current-frame; next-heap-ref)
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

module IterRoundsC {FS : FrameSemantics} where

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

  module Rounds {E A B : IRTy} (body : IR (E IRT.* A) (B IRT.+ A))
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (Iter body)))
    (ihb : IRObsCorrectF body)
    (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (bl : BlocksAt prog (blocks n l (Iter body)))
    (la : LabelsAt prog base (emitted n l (Iter body)))
    (Z : Loop.Anchor body n l base)
    where

    open IterShape body n l
    open IterRun body n l prog base span
    open Loop body n l base
    open Anchor Z
    module VR = ValueRealized

    -- One round from an entry, given the rounds from every later entry at a
    -- smaller budget.
    step : ∀ (r : ℕ) (σ : FlatState) (a : ⟦ A ⟧) (inv : RoundInv Z σ a)
         → (∀ (r″ : ℕ) → suc r″ ≤ r → ∀ (σ′ : FlatState) (a′ : ⟦ A ⟧) → RoundInv Z σ′ a′ → RoundsRun Z prog σ′ a′ r″)
         → RoundsRun Z prog σ a r
    step r σ a inv rec = go (Body.ρ₁ body n l prog base span ihb ss cr bl la Z σ a inv r) refl
      where
        open Body body n l prog base span ihb ss cr bl la Z σ a inv r
        h = SMCore.LocState.ev-log (floc σ)
        es₁ = eventsAt (floc σ) (⟪ round e a ⟫ r)

        RE : runAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ thenIter ιᶠ h es₁ ρ₁ (round e)
        RE = run-approx-iter ιᶠ h r (round e a) (round e)

        cut-run : ∀ {ρ} → ρ₁ ≡ ρ → runAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ (es₁ , returns cut)
                → budgetLeft r ρ ≡ 0 → is-stopped ρ ≡ false → RoundsRun Z prog σ a r
        exit-run : ∀ (b : ⟦ B ⟧) (r′ : ℕ) (q : ρ₁ ≡ returns (done (inj₁ b) r′))
                 → ResultPlace (B IRT.+ A) (VR.out-mode vb) (falloc S0) (VR.cont-alloc vb) (inj₁ b) (floc S0)
                 → RoundsRun Z prog σ a r
        go : (ρ : Res (Ap ⟦ B IRT.+ A ⟧)) → ρ₁ ≡ ρ → RoundsRun Z prog σ a r
        -- the round stopped: so did the loop
        go stopped q = record
          { steps = VR.steps vb ; settle = S0 ; out-mode = VR.out-mode vb ; cont-alloc = VR.cont-alloc vb
          ; run = chainB
          ; live = λ p → case trans (sym (cong is-stopped res)) p of λ ()
          ; at-end = λ p → case trans (sym res) p of λ ()
          ; stops = λ _ → proj₁ (VR.stops vb (cong is-stopped q)) , trans (proj₂ (VR.stops vb (cong is-stopped q))) (RoundInv.left inv)
          ; no-ret = λ _ → NC.ret0 nc ; no-link = λ _ → NC.lnk0 nc
          ; place = λ p → case trans (sym res) p of λ ()
          ; events = trans ev-chainB (sym evs)
          ; log = trans (VR.log vb) (cong (h DL.++_) (sym evs))
          ; progress = subst (λ ρ → r ≤ budgetLeft r ρ + chain-ctrls chainB) (sym res) (m≤m+n r _)
          ; mem0 = λ _ → NC.mem00 nc ; frame = λ _ → NC.cf0 nc ; bf0 = λ _ → NC.bf00 nc
          }
          where
            RE′ : runAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ (es₁ , stopped)
            RE′ = trans RE (cong (λ ρ → thenIter ιᶠ h es₁ ρ (round e)) q)
            res = cong proj₂ RE′
            evs = cong proj₁ RE′
            nc : NotCut ρ₁
            nc = subst NotCut (sym q) tt
        -- the round was cut: so was the loop
        go (returns cut) q = cut-run q (trans RE (cong (λ ρ → thenIter ιᶠ h es₁ ρ (round e)) q)) refl refl
        -- the round continues, but no budget is left for the silent step
        go (returns (done (inj₂ a′) zero)) q = cut-run q (trans RE (cong (λ ρ → thenIter ιᶠ h es₁ ρ (round e)) q)) refl refl
        go (returns (done (inj₁ b) r′)) q = exit-run b r′ q (VR.place vb q)
        go (returns (done (inj₂ a′) (suc r″))) q = cont-run a′ r″ q (VR.place vb q)
          where
            cont-run : ∀ (a′ : ⟦ A ⟧) (r″ : ℕ) (q : ρ₁ ≡ returns (done (inj₂ a′) (suc r″)))
                     → ResultPlace (B IRT.+ A) (VR.out-mode vb) (falloc S0) (VR.cont-alloc vb) (inj₂ a′) (floc S0)
                     → RoundsRun Z prog σ a r
            cont-run a′ r″ q (at-loc loc vS bef rax _ _) = record
              { steps = VR.steps vb + (15 + RoundsRun.steps rr) ; settle = RoundsRun.settle rr
              ; out-mode = RoundsRun.out-mode rr ; cont-alloc = RoundsRun.cont-alloc rr
              ; run = FlatSteps-++ chainB (FlatSteps-++ C.chain (RoundsRun.run rr))
              ; live = λ p → RoundsRun.live rr (trans (cong is-stopped (sym res)) p)
              ; at-end = λ p → RoundsRun.at-end rr (trans (sym res) p)
              ; stops = λ p → RoundsRun.stops rr (trans (cong is-stopped (sym res)) p)
              ; no-ret = λ nc′ → RoundsRun.no-ret rr (subst NotCut res nc′)
              ; no-link = λ nc′ → RoundsRun.no-link rr (subst NotCut res nc′)
              ; place = λ p → RoundsRun.place rr (trans (sym res) p)
              ; events = trans (chain-events-++ chainB (FlatSteps-++ C.chain (RoundsRun.run rr)))
                           (trans (cong₂ DL._++_ ev-chainB
                                     (trans (chain-events-++ C.chain (RoundsRun.run rr))
                                            (cong₂ DL._++_ C.ev-chain (RoundsRun.events rr))))
                                  (sym evs))
              ; log = trans (RoundsRun.log rr)
                        (trans (cong (DL._++ eventsAt (floc C.σ′) (⟪ loopFrom e a′ ⟫ r″)) logσ′)
                          (trans (++-assoc h es₁ _) (cong (h DL.++_) (sym evs))))
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
              ; frame = λ nc′ → RoundsRun.frame rr (subst NotCut res nc′)
              ; bf0 = λ nc′ → RoundsRun.bf0 rr (subst NotCut res nc′)
              }
              where
                nc : NotCut ρ₁
                nc = subst NotCut (sym q) tt
                ns : stopsAt (floc σ) (⟪ round e a ⟫ r) ≡ false
                ns = cong is-stopped q
                module C = Cont body n l prog base span la Z S0 a′ (Live.nh0 ns) (pc0-of q)
                             (NC.cf0 nc) ns0 (NC.hr0 nc) (NC.memF0 nc) (NC.env0 nc) (NC.ret0 nc) (NC.lnk0 nc)
                             (NC.mem00 nc) (NC.bf00 nc) (Live.left0 ns) loc vS bef rax
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

        cut-run {ρ} q RE′ bl0 nst = record
          { steps = VR.steps vb ; settle = S0 ; out-mode = VR.out-mode vb ; cont-alloc = VR.cont-alloc vb
          ; run = chainB
          ; live = λ _ → Live.nh0 (trans (cong is-stopped q) nst)
          ; at-end = λ p → case trans (sym res) p of λ ()
          ; stops = λ p → case trans (sym (cong is-stopped res)) p of λ ()
          ; no-ret = cut-absurd res ; no-link = cut-absurd res
          ; place = λ p → case trans (sym res) p of λ ()
          ; events = trans ev-chainB (sym evs)
          ; log = trans (VR.log vb) (cong (h DL.++_) (sym evs))
          ; progress = subst (λ ρ′ → r ≤ budgetLeft r ρ′ + chain-ctrls chainB) (sym res)
                         (subst (λ m → r ≤ 0 + m) (sym ctrls-chainB)
                           (subst (λ x → r ≤ x + chain-ctrls (VR.run vb)) bl0
                             (subst (λ ρ′ → r ≤ budgetLeft r ρ′ + chain-ctrls (VR.run vb)) q (VR.progress vb))))
          ; mem0 = cut-absurd res ; frame = cut-absurd res ; bf0 = cut-absurd res
          }
          where
            res = cong proj₂ RE′
            evs = cong proj₁ RE′

        exit-run b r′ q (at-loc loc vS bef rax _ _) = record
          { steps = VR.steps vb + 4 ; settle = XE.s4 ; out-mode = proj₁ X.placeB ; cont-alloc = falloc XE.s4
          ; run = FlatSteps-++ chainB X.chain
          ; live = λ _ → X.nh4
          ; at-end = λ _ → X.pc-end
          ; stops = λ p → case trans (sym (cong is-stopped res)) p of λ ()
          ; no-ret = λ _ → NC.ret0 nc ; no-link = λ _ → NC.lnk0 nc
          ; place = λ p → subst (λ w → ResultPlace B (proj₁ X.placeB) (falloc XE.s4) (falloc XE.s4) w (floc XE.s4))
                                (done-value (trans (sym res) p)) (proj₂ X.placeB)
          ; events = trans (chain-events-++ chainB X.chain)
                       (trans (cong₂ DL._++_ ev-chainB X.ev-chain) (trans (DLP.++-identityʳ es₁) (sym evs)))
          ; log = trans X.log4 (trans (VR.log vb) (cong (h DL.++_) (sym evs)))
          ; progress = subst (λ ρ′ → r ≤ budgetLeft r ρ′ + chain-ctrls (FlatSteps-++ chainB X.chain)) (sym res)
                         (progress-≤ (subst (λ m → r ≤ r′ + m) (sym ctrls-chainB)
                                       (subst (λ ρ′ → r ≤ budgetLeft r ρ′ + chain-ctrls (VR.run vb)) q (VR.progress vb)))
                                     (ctrls-≤ˡ chainB X.chain))
          ; mem0 = λ _ lc bf → trans (X.mem4 lc) (NC.mem00 nc lc bf)
          ; frame = λ _ → NC.cf0 nc
          ; bf0 = λ _ → NC.bf00 nc
          }
          where
            nc : NotCut ρ₁
            nc = subst NotCut (sym q) tt
            ns : stopsAt (floc σ) (⟪ round e a ⟫ r) ≡ false
            ns = cong is-stopped q
            module XE = Exit body n l prog base span la S0 b {VR.out-mode vb} (Live.nh0 ns) (pc0-of q)
            module X = XE.P loc vS bef rax
            RE′ : runAt (floc σ) (⟪ loopFrom e a ⟫ r) ≡ (es₁ , returns (done b r′))
            RE′ = trans RE (cong (λ ρ → thenIter ιᶠ h es₁ ρ (round e)) q)
            res = cong proj₂ RE′
            evs = cong proj₁ RE′

    -- THE INDUCTION, on a fuel bounding the budget: a round that continues
    -- leaves strictly less (`Approx.done-≤`), so the next entry's rounds are
    -- at a smaller budget.
    rounds : ∀ (F r : ℕ) → r ≤ F → ∀ (σ : FlatState) (a : ⟦ A ⟧) → RoundInv Z σ a → RoundsRun Z prog σ a r
    rounds zero    r r≤F σ a inv = step r σ a inv (λ r″ lt → case ≤-trans lt r≤F of λ ())
    rounds (suc F) r r≤F σ a inv = step r σ a inv (λ r″ lt → rounds F r″ (≤-pred (≤-trans lt r≤F)))
