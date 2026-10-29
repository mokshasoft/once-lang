-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.BlockCall   (plan 0.125 S2)
--
-- THE BLOCK-CALL LEMMA: a block whose body satisfies `IRObsCorrectF`, entered
-- by a call (`enter-call pre`, the return pc pushed), runs as a `CalleeRunP`.
--
-- The run is the block's own three parts (`block-layout`): the `c-thunk`
-- marker grows and clears the callee frame, which puts the machine exactly
-- at the body's entry state; the body's run is its `MachineRefinesObsF`
-- (D337: stated over every return stack, so the pending return is no
-- obstacle); and when the body returned, its `c-ret` pops the return pc and
-- `leave-frame` restores the caller's frame (D338's `frames-pres`).
--
-- What crosses the two frame moves is settled by two facts. The caller's
-- live slots are ANCESTORS of the callee frame (`shift-≺`, `shift-below`), so
-- the clear misses them and the body's `stack-pres` covers them. And a VALUE
-- lives on the heap (`Live`), whose frontier no frame move touches, so the
-- body's result is still valid after the return.
--
-- The body's INPUT is the caller's business: `curry` builds it from the
-- closure's environment and the argument, so it arrives here as an
-- `InputAt` at the entry state.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.BlockCall (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; instr-ctrl; c-ret; c-thunk; c-entry; EntryId; e-thunk; block-layout; StackMem; module MemOps)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Label using (LabelId)
open import Data.Nat using (s≤s; z≤n)
open import Data.List.Properties using (++-identityʳ)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
import Once.Denotation.ValueDomain as ValueDomain
open import Data.Unit using (⊤)
open import Once.IRTy using (IRTy)
open import Once.Internal.Iterative using (T∞)
open import Once.CCC.Machine.SMCore using (StoredValue)
open import Once.Denotation.Approx using (budgetLeft)
import Once.CCC.Machine.Allocation as Alloc
open import Relation.Nullary using (yes; no)
open import Once.Internal.Res using (Res; returns; stopped; is-stopped)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut)

module BlockCallC {FS : FrameSemantics} where

  open Core {FS}
  open FrameSemantics FS using (Frame; shift-frame; _≺_; ≺-trans; ≺-irrefl; shift-≺; shift-below; _≟F_)
  open AllocState using (current-frame; saved-frames; next-slot; next-heap-ref; frame-slots)
  open LocState using (halted; stackMem; heapMem)
  open Alloc.FrontierInvariant {FS} using (src-origin)
  open MemOps {FS} using (clear-frame)
  open FlatStepsAPI {FS} using (flat-step1)

  ----------------------------------------------------------------------
  -- The callee frame and the state the marker leaves.
  ----------------------------------------------------------------------
  callee-alloc : ℕ → FlatState → AllocState {FS}
  callee-alloc bb fs = grow-frame bb (falloc fs)

  callee-loc : ℕ → FlatState → LocState FS
  callee-loc bb fs = floc (do-thunk bb fs)

  -- the marker leaves the body's entry state
  thunk-entry : ∀ (bb j : ℕ) (rs : List ℕ) (fs : FlatState) → fpc fs ≡ j → fret fs ≡ rs
              → do-thunk bb fs ≡ entry-flat (suc j) (callee-loc bb fs) (callee-alloc bb fs) (fclosure fs) rs
  thunk-entry bb j rs fs refl refl = refl

  -- the callee frame is below the caller's
  callee-≺ : ∀ (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
           → current-frame (callee-alloc bb fs) ≺ current-frame pre
  callee-≺ bb fs pre refl = shift-below bb (shift-≺ (current-frame pre) 1 (s≤s z≤n))

  -- …so a caller-live location is live in the callee (at any slot bound),
  callee-bf : ∀ (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
            → ∀ (m m′ : ℕ) (loc : ValueLocation FS)
            → BeforeFrontier (record pre { next-slot = m }) loc
            → BeforeFrontier (record (callee-alloc bb fs) { next-slot = m′ }) loc
  callee-bf bb fs pre fa m m′ (AtStack f k) (BeforeFrontier.stack-before refl k<m) =
    BeforeFrontier.stack-ancestor (callee-≺ bb fs pre fa) (src-origin m k<m)
  callee-bf bb fs pre fa m m′ (AtStack f k) (BeforeFrontier.stack-ancestor cf≺f src) =
    BeforeFrontier.stack-ancestor (≺-trans (callee-≺ bb fs pre fa) cf≺f) src
  callee-bf bb fs pre refl m m′ (AtDynamic hl) (BeforeFrontier.heap-before r<h) =
    BeforeFrontier.heap-before r<h

  -- …and the marker's clear does not touch it.
  clear-miss : ∀ (mem : StackMem FS) (f₀ : Frame) (b : ℕ) (f : Frame) (k : ℕ) → f₀ ≢ f
             → clear-frame mem f₀ b f k ≡ mem f k
  clear-miss mem f₀ b f k ne with f₀ ≟F f
  ... | yes e = ⊥-elim (ne e)
  ... | no  _ = refl

  thunk-keeps : ∀ (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
              → ∀ (m : ℕ) (loc : ValueLocation FS)
              → BeforeFrontier (record pre { next-slot = m }) loc
              → readLoc (callee-loc bb fs) loc ≡ readLoc (floc fs) loc
  thunk-keeps bb fs pre fa m (AtStack f k) bf =
    clear-miss (stackMem (floc fs)) _ bb f k (λ e → ≺-irrefl (subst (_≺ f) e (below bf)))
    where
      below : BeforeFrontier (record pre { next-slot = m }) (AtStack f k)
            → current-frame (callee-alloc bb fs) ≺ f
      below (BeforeFrontier.stack-before refl _)   = callee-≺ bb fs pre fa
      below (BeforeFrontier.stack-ancestor cf≺f _) = ≺-trans (callee-≺ bb fs pre fa) cf≺f
  thunk-keeps bb fs pre fa m (AtDynamic hl) bf = refl

  -- the heap is the caller's, and so is its frontier
  callee-heap : ∀ (bb : ℕ) (fs : FlatState) {a : AllocState {FS}} (l : ValueLocation FS) → Live a l
              → readLoc (callee-loc bb fs) l ≡ readLoc (floc fs) l
  callee-heap bb fs (AtDynamic hl) _ = refl

  live-callee : ∀ (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
              → ∀ (l : ValueLocation FS) → Live pre l → Live (callee-alloc bb fs) l
  live-callee bb fs pre refl (AtDynamic hl) (BeforeFrontier.heap-before r<h) = BeforeFrontier.heap-before r<h

  -- the frame comes back on return
  lf-cf : ∀ (a : AllocState {FS}) (f : Frame) (b : ℕ) (frs : List (Frame × ℕ))
        → saved-frames a ≡ (f , b) ∷ frs → current-frame (leave-frame a) ≡ f
  lf-cf a f b frs e rewrite e = refl

  -- a value's cells are heap cells, and a frame move keeps the heap frontier
  live-leave : ∀ (a : AllocState {FS}) (l : ValueLocation FS) → Live a l → Live (leave-frame a) l
  live-leave a (AtDynamic hl) (BeforeFrontier.heap-before r<h) =
    BeforeFrontier.heap-before (subst (_ <_) (sym (leave-frame-heap-ref a)) r<h)

  true≢false : true ≡ false → ⊥
  true≢false ()

  ----------------------------------------------------------------------
  -- The block's own text, fetched.
  ----------------------------------------------------------------------
  -- plan 0.125 S3: a called ENTRY of either kind — a block (`e-thunk`, which
  -- is `block-layout`) or one of the program's functions (`e-fn`, whose marker
  -- is followed by its linked unit). The marker executes the same either way.
  entry-layout : EntryId → ℕ → AbstractTrace → AbstractTrace
  entry-layout eid bb t = instr-ctrl (c-entry eid bb) ∷ t ++ instr-ctrl (c-ret bb) ∷ []

  module Layout (prog : AbstractTrace) (eid : EntryId) (bb j : ℕ) (t : AbstractTrace)
                (sp : SpanAt prog j (entry-layout eid bb t)) where

    fetch-thunk : fetch prog j ≡ just (instr-ctrl (c-entry eid bb))
    fetch-thunk = sp 0 _ refl

    body-span : SpanAt prog (suc j) t
    body-span k i eq =
      subst (λ z → fetch prog z ≡ just i) (sym (+-suc k j))
            (sp (suc k) i (fetch-++-left t (instr-ctrl (c-ret bb) ∷ []) k i eq))

    fetch-ret : fetch prog (length t + suc j) ≡ just (instr-ctrl (c-ret bb))
    fetch-ret =
      subst (λ z → fetch prog z ≡ just (instr-ctrl (c-ret bb))) (sym (+-suc (length t) j))
            (sp (suc (length t)) _
                (subst (λ z → fetch (t ++ instr-ctrl (c-ret bb) ∷ []) z ≡ just (instr-ctrl (c-ret bb)))
                       (+-identityʳ (length t)) (fetch-++-right t (instr-ctrl (c-ret bb) ∷ []) 0)))

  ----------------------------------------------------------------------
  -- THE LEMMA.
  ----------------------------------------------------------------------
  place-across : ∀ {prog : AbstractTrace} {B m a ca v s} {a′ : AllocState {FS}}
               → (∀ l → Live a l → Live a′ l)
               → ResultPlace {prog = prog} B m a ca v s
               → ResultPlaceP {B} (VAt {prog = prog} B) m a′ a′ v s
  place-across bft unit-result = rp-unit refl
  place-across {prog = prog} bft (at-loc loc va lv rax _ _) =
    rp-loc loc va′ (bft loc lv) rax va′ (bft loc lv)
    where va′ = validityWF-heap-transport {prog = prog} (λ _ → ⊤) (λ _ _ → tt) (λ _ _ → refl) bft _ loc tt va
  place-across bft (at-reg fit rax) = rp-reg fit rax

  -- plan 0.125 S3 (`FnRuns`): the same move, landing at `ResultPlace` — a
  -- function's run is stated where the body's obligation states its own.
  place-across′ : ∀ {prog : AbstractTrace} {B m a ca v s} {a′ : AllocState {FS}}
                → (∀ l → Live a l → Live a′ l)
                → ResultPlace {prog = prog} B m a ca v s
                → ResultPlace {prog = prog} B m a′ a′ v s
  place-across′ bft unit-result = unit-result
  place-across′ {prog = prog} bft (at-loc loc va lv rax _ _) =
    at-loc loc va′ (bft loc lv) rax va′ (bft loc lv)
    where va′ = validityWF-heap-transport {prog = prog} (λ _ → ⊤) (λ _ _ → tt) (λ _ _ → refl) bft _ loc tt va
  place-across′ bft (at-reg fit rax) = at-reg fit rax

  -- …and a caller's input is the callee's: its cells are heap cells, which
  -- the marker neither moves nor clears, and the registers are untouched.
  input-callee : ∀ {prog : AbstractTrace} {A} {mIn : AllocMode} {x : ValueDomain.⟦ A ⟧ᴰᴵ}
                   (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) → falloc fs ≡ enter-call pre
               → InputAt {prog = prog} mIn pre x (floc fs)
               → InputAt {prog = prog} mIn (callee-alloc bb fs) x (callee-loc bb fs)
  input-callee {prog = prog} {A} {mIn} {x} bb fs pre fa (in-loc loc va lv rd) =
    in-loc loc (validityWF-heap-transport {prog = prog} {mIn} {A} (Live pre) (λ _ l → l)
                  (λ l q → callee-heap bb fs {pre} l q) (live-callee bb fs pre fa) x loc lv va)
           (live-callee bb fs pre fa loc lv) rd
  input-callee bb fs pre fa (in-reg fit rd) = in-reg fit rd
  input-callee bb fs pre fa (in-unit eq) = in-unit eq

  ----------------------------------------------------------------------
  -- WHAT A BLOCK BODY OWES, for any body text `t`, computation `comp` and
  -- result relation `R`: a `ValueRealized` (at frontier 0, `length t`) with
  -- its `traces-agree`. A compiled IR's body supplies it from its own
  -- `MachineRefinesObsF` (`block-call`); a body that is not one IR (the `Ana`
  -- block: coalgebra, then re-suspension) composes it.
  ----------------------------------------------------------------------
  record BodyRuns (prog : AbstractTrace) (base len : ℕ) {B : IRTy}
                  (R : AllocMode → AllocState {FS} → AllocState {FS} → ValueDomain.⟦ B ⟧ᴰᴵ → LocState FS → Set)
                  (comp : T∞ ValueDomain.⟦ B ⟧ᴰᴵ) (s : LocState FS) (alloc : AllocState {FS})
                  (cl : StoredValue FS) (rs : List ℕ) (k : ℕ) : Set where
    constructor body-runs
    field
      steps      : ℕ
      settle     : FlatState
      out-mode   : AllocMode
      cont-alloc : AllocState {FS}
      run        : FlatSteps prog steps (entry-flat base s alloc cl rs) settle
      live       : stopsAt s (⟪ comp ⟫ k) ≡ false → halted (floc settle) ≡ false
      at-end     : ∀ {v r} → resultAt s (⟪ comp ⟫ k) ≡ returns (done v r) → fpc settle ≡ len + base
      stops      : stopsAt s (⟪ comp ⟫ k) ≡ true → halted (floc settle) ≡ true × LocState.left (floc settle) ≡ LocState.left s
      no-ret     : ∀ {v r} → resultAt s (⟪ comp ⟫ k) ≡ returns (done v r) → fret settle ≡ rs
      no-link    : NotCut (resultAt s (⟪ comp ⟫ k)) → flink settle ≡ nothing
      log        : LocState.ev-log (floc settle) ≡ LocState.ev-log s ++ eventsAt s (⟪ comp ⟫ k)
      place      : ∀ {v r} → resultAt s (⟪ comp ⟫ k) ≡ returns (done v r) → R out-mode (falloc settle) cont-alloc v (floc settle)
      progress   : k ≤ budgetLeft k (resultAt s (⟪ comp ⟫ k)) + chain-ctrls run
      events     : chain-events run ≡ eventsAt s (⟪ comp ⟫ k)
      mem-pres   : NotCut (resultAt s (⟪ comp ⟫ k)) → ∀ (loc : ValueLocation FS)
                 → BeforeFrontier (record alloc { next-slot = 0 }) loc → readLoc (floc settle) loc ≡ readLoc s loc
      frame-pres : ∀ {v r} → resultAt s (⟪ comp ⟫ k) ≡ returns (done v r) → current-frame (falloc settle) ≡ current-frame alloc
      bf-mono    : NotCut (resultAt s (⟪ comp ⟫ k)) → ∀ (m : ℕ) (loc : ValueLocation FS)
                 → BeforeFrontier (record alloc { next-slot = m }) loc → BeforeFrontier (record (falloc settle) { next-slot = m }) loc
      frames-pres : ∀ {v r} → resultAt s (⟪ comp ⟫ k) ≡ returns (done v r) → saved-frames (falloc settle) ≡ saved-frames alloc

  mro→body : ∀ {prog base A B l} {ir : IR A B} {x s alloc cl rs k}
           → MachineRefinesObsF prog base 0 l ir x s alloc cl rs k
           → BodyRuns prog base (length (emitted 0 l ir)) {B} (ResultPlace {prog = prog} B) (evalᴰ ir x) s alloc cl rs k
  mro→body {B = B} mro =
    body-runs VR.steps VR.settle VR.out-mode VR.cont-alloc VR.run VR.live VR.at-end VR.stops VR.no-ret VR.no-link
              VR.log VR.place VR.progress (MachineRefinesObsF.traces-agree mro) (vr-mem-pres vr)
              VR.frame-pres VR.bf-mono VR.frames-pres
    where
      vr = MachineRefinesObsF.value-realized mro
      module VR = ValueRealized {B = B} vr

  entry-call-gen : ∀ {B : IRTy}
      {R  : AllocMode → AllocState {FS} → AllocState {FS} → ValueDomain.⟦ B ⟧ᴰᴵ → LocState FS → Set}
      {R′ : AllocMode → AllocState {FS} → AllocState {FS} → ValueDomain.⟦ B ⟧ᴰᴵ → LocState FS → Set}
    → (∀ {m a ca v s} {a′ : AllocState {FS}} → (∀ l → Live a l → Live a′ l) → R m a ca v s → R′ m a′ a′ v s)
    → ∀ (t : AbstractTrace) (comp : T∞ ValueDomain.⟦ B ⟧ᴰᴵ)
        (prog : AbstractTrace) (eid : EntryId) (bb j : ℕ)
    → SpanAt prog j (entry-layout eid bb t)
    → ∀ (fs : FlatState) (pre : AllocState {FS}) (ret-pc k : ℕ) (rs : List ℕ)
    → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ rs
    → falloc fs ≡ enter-call pre
    → BodyRuns prog (suc j) (length t) {B} R comp (callee-loc bb fs) (callee-alloc bb fs) (fclosure fs) (ret-pc ∷ rs) k
    → CalleeRunP {prog = prog} {B} R′ fs ret-pc rs comp k
  entry-call-gen {B} {R} {R′} across t comp prog eid bb j sp fs pre ret-pc k rs pc nh fr fa br =
    go (resultAt s′ (⟪ comp ⟫ k)) refl
    where
      open Layout prog eid bb j t sp

      s′ = callee-loc bb fs
      a′ = callee-alloc bb fs
      cl = fclosure fs

      module VR = BodyRuns {B = B} {R = R} br

      -- the marker step, landing on the body's entry
      te = thunk-entry bb j (ret-pc ∷ rs) fs pc fr

      thunk-step : ∀ {n fs″} → FlatSteps prog n (entry-flat (suc j) s′ a′ cl (ret-pc ∷ rs)) fs″
                 → FlatSteps prog (suc n) fs fs″
      thunk-step rest =
        step-at (entry-flat (suc j) s′ a′ cl (ret-pc ∷ rs))
                (nh , subst (λ z → fetch prog z ≡ just _) (sym pc) fetch-thunk)
                te rest

      -- caller memory is the body's
      mem-body : NotCut (resultAt s′ (⟪ comp ⟫ k)) → ∀ (pre′ : AllocState {FS}) (m : ℕ) → falloc fs ≡ enter-call pre′
               → ∀ (loc : ValueLocation FS) → BeforeFrontier (record pre′ { next-slot = m }) loc
               → readLoc (floc VR.settle) loc ≡ readLoc (floc fs) loc
      mem-body nc pre′ m fa′ loc bf =
        trans (VR.mem-pres nc loc (callee-bf bb fs pre′ fa′ m 0 loc bf)) (thunk-keeps bb fs pre′ fa′ m loc bf)

      stuck : ∀ {ρ} → resultAt s′ (⟪ comp ⟫ k) ≡ ρ
            → (∀ {v r} → ρ ≡ returns (done v r) → ⊥)
            → CalleeRunP {prog = prog} {B} R′ fs ret-pc rs comp k
      stuck eq nr = record
        { steps      = suc VR.steps
        ; settle     = VR.settle
        ; out-mode   = VR.out-mode
        ; cont-alloc = VR.cont-alloc
        ; run        = thunk-step VR.run
        ; live       = λ p → VR.live p
        ; returned   = λ p → ⊥-elim (nr (trans (sym eq) p))
        ; stops      = λ p → VR.stops p
        ; no-ret     = λ p → ⊥-elim (nr (trans (sym eq) p))
        ; no-link    = λ nc → VR.no-link nc
        ; place      = λ p → ⊥-elim (nr (trans (sym eq) p))
        ; events     = trans (chain-events-subst-start (sym te) VR.run) VR.events
        ; log        = VR.log
        ; progress   = progress-≤ VR.progress (≤-trans (≤-reflexive (sym (chain-ctrls-subst-start (sym te) VR.run))) (n≤1+n _))
        ; mem-pres   = mem-body
        ; frame-pres = λ p → ⊥-elim (nr (trans (sym eq) p))
        ; bf-mono    = λ nc pre′ m fa′ loc bf → VR.bf-mono nc m loc (callee-bf bb fs pre′ fa′ m m loc bf)
        ; frames-pres = λ p → ⊥-elim (nr (trans (sym eq) p))
        }

      go : (ρ : Res (Ap ValueDomain.⟦ B ⟧ᴰᴵ)) → resultAt s′ (⟪ comp ⟫ k) ≡ ρ
         → CalleeRunP {prog = prog} {B} R′ fs ret-pc rs comp k
      -- RETURNED: one more step, the `c-ret`.
      go (returns (done v r)) eq = record
        { steps      = suc (VR.steps + 1)
        ; settle     = settle-r
        ; out-mode   = VR.out-mode
        ; cont-alloc = falloc settle-r
        ; run        = run-r
        ; live       = λ p → VR.live p
        ; returned   = λ _ → refl
        ; stops      = λ p → ⊥-elim (true≢false (trans (sym p) (cong is-stopped eq)))
        ; no-ret     = λ _ → refl
        ; no-link    = λ nc → VR.no-link nc
        ; place      = λ p → across (live-leave (falloc VR.settle)) (VR.place p)
        ; events     = trans (chain-events-subst-start (sym te) (FlatSteps-++ VR.run ret-run)) ev-r
        ; log        = VR.log
        ; progress   = progress-≤ VR.progress (ctrls-r)
        ; mem-pres   = mem-body
        ; frame-pres = λ _ pre′ fa′ → lf-cf (falloc VR.settle) _ _ _ (frames-back pre′ fa′)
        ; bf-mono    = λ nc pre′ m fa′ loc bf → bf-back nc pre′ m fa′ loc bf
        ; frames-pres = λ _ pre′ fa′ → leave-frame-saved-∷ (falloc VR.settle) _ _ _ (frames-back pre′ fa′)
        }
        where
          retd : resultAt s′ (⟪ comp ⟫ k) ≡ returns (done v r)
          retd = eq

          settle-r : FlatState
          settle-r = record VR.settle { falloc = leave-frame (falloc VR.settle) ; fpc = ret-pc ; fret = rs }

          ret-eq : flat-exec-instr (instr-ctrl (c-ret bb)) prog VR.settle ≡ settle-r
          ret-eq rewrite VR.no-ret retd = refl

          ret-run : FlatSteps prog 1 VR.settle settle-r
          ret-run = step-at settle-r
                      (VR.live (cong is-stopped retd)
                      , subst (λ z → fetch prog z ≡ just (instr-ctrl (c-ret bb))) (sym (VR.at-end retd)) fetch-ret)
                      ret-eq []

          ret-silent : chain-events ret-run ≡ []
          ret-silent = chain-events-subst-start (sym ret-eq) []

          run-r : FlatSteps prog (suc (VR.steps + 1)) fs settle-r
          run-r = thunk-step (FlatSteps-++ VR.run ret-run)

          ev-r : chain-events (FlatSteps-++ VR.run ret-run) ≡ eventsAt (floc fs) (⟪ comp ⟫ k)
          ev-r = trans (chain-events-++ VR.run ret-run)
                       (trans (cong (_++ chain-events ret-run) VR.events)
                              (trans (cong (eventsAt s′ (⟪ comp ⟫ k) ++_) ret-silent) (++-identityʳ _)))

          ctrls-r : chain-ctrls VR.run ≤ chain-ctrls run-r
          ctrls-r = ≤-trans (subst (chain-ctrls VR.run ≤_) (sym (chain-ctrls-subst-start (sym te) (FlatSteps-++ VR.run ret-run)))
                               (ctrls-≤ˡ VR.run ret-run))
                            (n≤1+n _)

          frames-back : ∀ (pre′ : AllocState {FS}) → falloc fs ≡ enter-call pre′
                      → saved-frames (falloc VR.settle) ≡ (current-frame pre′ , frame-slots pre′) ∷ saved-frames pre′
          frames-back pre′ fa′ = trans (VR.frames-pres retd) (cong saved-frames fa′)

          bf-back : NotCut (resultAt s′ (⟪ comp ⟫ k)) → ∀ (pre′ : AllocState {FS}) (m : ℕ) → falloc fs ≡ enter-call pre′
                  → ∀ (loc : ValueLocation FS) → BeforeFrontier (record pre′ { next-slot = m }) loc
                  → BeforeFrontier (record (falloc settle-r) { next-slot = m }) loc
          bf-back nc pre′ m fa′ (AtStack f k′) (BeforeFrontier.stack-before refl k<m) =
            BeforeFrontier.stack-before (sym (lf-cf (falloc VR.settle) _ _ _ (frames-back pre′ fa′))) k<m
          bf-back nc pre′ m fa′ (AtStack f k′) (BeforeFrontier.stack-ancestor cf≺f src) =
            BeforeFrontier.stack-ancestor (subst (_≺ f) (sym (lf-cf (falloc VR.settle) _ _ _ (frames-back pre′ fa′))) cf≺f) src
          bf-back nc pre′ m fa′ (AtDynamic hl) bf with VR.bf-mono nc m (AtDynamic hl) (callee-bf bb fs pre′ fa′ m m (AtDynamic hl) bf)
          ... | BeforeFrontier.heap-before r<h =
            BeforeFrontier.heap-before (subst (_ <_) (sym (leave-frame-heap-ref (falloc VR.settle))) r<h)

      -- STOPPED or CUT: the body's run is the whole run.
      go stopped eq = stuck eq (λ ())
      go (returns cut) eq = stuck eq (λ ())

  block-call-gen : ∀ {B : IRTy}
      {R  : AllocMode → AllocState {FS} → AllocState {FS} → ValueDomain.⟦ B ⟧ᴰᴵ → LocState FS → Set}
      {R′ : AllocMode → AllocState {FS} → AllocState {FS} → ValueDomain.⟦ B ⟧ᴰᴵ → LocState FS → Set}
    → (∀ {m a ca v s} {a′ : AllocState {FS}} → (∀ l → Live a l → Live a′ l) → R m a ca v s → R′ m a′ a′ v s)
    → ∀ (t : AbstractTrace) (comp : T∞ ValueDomain.⟦ B ⟧ᴰᴵ)
        (prog : AbstractTrace) (lbl : LabelId) (bb j : ℕ)
    → SpanAt prog j (block-layout (lbl , bb , t))
    → ∀ (fs : FlatState) (pre : AllocState {FS}) (ret-pc k : ℕ) (rs : List ℕ)
    → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ rs
    → falloc fs ≡ enter-call pre
    → BodyRuns prog (suc j) (length t) {B} R comp (callee-loc bb fs) (callee-alloc bb fs) (fclosure fs) (ret-pc ∷ rs) k
    → CalleeRunP {prog = prog} {B} R′ fs ret-pc rs comp k
  block-call-gen across t comp prog lbl = entry-call-gen across t comp prog (e-thunk lbl)

  -- …and a compiled IR's entry, of either kind.
  entry-call : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
    → ∀ (l : ℕ) (prog : AbstractTrace) (eid : EntryId) (bb j : ℕ)
    → AllSlotStable prog → BlockRuns prog
    → SpanAt prog j (entry-layout eid bb (emitted 0 l ir))
    → BlocksAt prog (blocks 0 l ir)
    → LabelsAt prog (suc j) (emitted 0 l ir)
    → ∀ (fs : FlatState) (pre : AllocState {FS}) (mIn : AllocMode) (x : ValueDomain.⟦ A ⟧ᴰᴵ)
        (ret-pc k : ℕ) (rs : List ℕ)
    → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ rs
    → falloc fs ≡ enter-call pre → next-slot pre ≡ 0
    → InputAt {prog = prog} mIn (callee-alloc bb fs) x (callee-loc bb fs)
    → CalleeRunP {prog = prog} {B} (ResultPlaceP {B} (VAt {prog = prog} B)) fs ret-pc rs (evalᴰ ir x) k
  entry-call {A} {B} ir ioc l prog eid bb j ss cr sp bl la fs pre mIn x ret-pc k rs pc nh fr fa ns inp =
    entry-call-gen {B} {ResultPlace {prog = prog} B} {ResultPlaceP {B} (VAt {prog = prog} B)} place-across (emitted 0 l ir) (evalᴰ ir x) prog eid bb j sp fs pre ret-pc k rs pc nh fr fa
      (mro→body {prog} {suc j} {A} {B} {l} {ir} (ioc 0 l prog (suc j) ss cr (Layout.body-span prog eid bb j (emitted 0 l ir) sp) bl la mIn x
                   (callee-loc bb fs) (callee-alloc bb fs) (fclosure fs) (trans (cong next-slot fa) ns) nh inp k (ret-pc ∷ rs)))

  block-call : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
    → ∀ (l : ℕ) (prog : AbstractTrace) (lbl : LabelId) (bb j : ℕ)
    → AllSlotStable prog → BlockRuns prog
    → SpanAt prog j (block-layout (lbl , bb , emitted 0 l ir))
    → BlocksAt prog (blocks 0 l ir)
    → LabelsAt prog (suc j) (emitted 0 l ir)
    → ∀ (fs : FlatState) (pre : AllocState {FS}) (mIn : AllocMode) (x : ValueDomain.⟦ A ⟧ᴰᴵ)
        (ret-pc k : ℕ) (rs : List ℕ)
    → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ rs
    → falloc fs ≡ enter-call pre → next-slot pre ≡ 0
    → InputAt {prog = prog} mIn (callee-alloc bb fs) x (callee-loc bb fs)
    → CalleeRunP {prog = prog} {B} (ResultPlaceP {B} (VAt {prog = prog} B)) fs ret-pc rs (evalᴰ ir x) k
  block-call ir ioc l prog lbl = entry-call ir ioc l prog (e-thunk lbl)

  -- plan 0.125 S3: A FUNCTION's entry, as `FnRuns` asks for it — the input
  -- where the caller left it, the result at `ResultPlace`.
  fn-call : ∀ {A B} (ir : IR A B) → IRObsCorrectF ir
    → ∀ (l : ℕ) (prog : AbstractTrace) (eid : EntryId) (bb j : ℕ)
    → AllSlotStable prog → BlockRuns prog
    → SpanAt prog j (entry-layout eid bb (emitted 0 l ir))
    → BlocksAt prog (blocks 0 l ir)
    → LabelsAt prog (suc j) (emitted 0 l ir)
    → ∀ (fs : FlatState) (pre : AllocState {FS}) (x : ValueDomain.⟦ A ⟧ᴰᴵ)
        (ret-pc k : ℕ) (rs : List ℕ) (mIn : AllocMode)
    → fpc fs ≡ j → halted (floc fs) ≡ false → fret fs ≡ ret-pc ∷ rs
    → falloc fs ≡ enter-call pre → next-slot pre ≡ 0
    → InputAt {prog = prog} mIn pre x (floc fs)
    → CalleeRunP {prog = prog} {B} (ResultPlace {prog = prog} B) fs ret-pc rs (evalᴰ ir x) k
  fn-call {A} {B} ir ioc l prog eid bb j ss cr sp bl la fs pre x ret-pc k rs mIn pc nh fr fa ns inp =
    entry-call-gen {B} {ResultPlace {prog = prog} B} {ResultPlace {prog = prog} B} place-across′ (emitted 0 l ir) (evalᴰ ir x) prog eid bb j sp fs pre ret-pc k rs pc nh fr fa
      (mro→body {prog} {suc j} {A} {B} {l} {ir} (ioc 0 l prog (suc j) ss cr (Layout.body-span prog eid bb j (emitted 0 l ir) sp) bl la mIn x
                   (callee-loc bb fs) (callee-alloc bb fs) (fclosure fs) (trans (cong next-slot fa) ns) nh
                   (input-callee {prog = prog} {A} {mIn} {x} bb fs pre fa inp) k (ret-pc ∷ rs)))
