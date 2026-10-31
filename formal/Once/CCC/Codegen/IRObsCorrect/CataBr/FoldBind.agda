-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FoldBind   (plan 0.135 S3, cata M4 stage D2)
--
-- RUNS OF THE FOLD LOOP COMPOSE (`FoldInv.RoundRun`):
--
--   * `bind-rr`: RoundRuns compose along `_>>=∞_` (the second at the
--     first's end state, at the budget the first left), at the run level
--     (`Approx.run-approx-bind`); stopped and cut runs end in the first;
--   * `pure-rr`: `return∞` is the empty run.
--
-- Machine-generic (no fold text); `FoldLoop` chains the rounds with them.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun; tableEnv)
module Once.CCC.Codegen.IRObsCorrect.CataBr.FoldBind (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.CataBr.FoldInv o tbl using (module CataFoldInvC)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.Res using (Res; returns; stopped; is-stopped)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_)
open import Once.Denotation.Approx using (Ap; done; cut; NotCut; budgetLeft; thenAp; run-approx-bind)
open import Data.List.Properties using (++-identityʳ)
import Once.IR.Semantics.Trace as TM
open import Once.IR.Semantics.Event using (SigOpEvent)

module CataFoldBindC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open CataFoldInvC {FS} using (module Inv; RoundRun; Same)
  open LocState using (halted)
  open AllocState using (next-slot)

  private
    done-inj : ∀ {V : Set} {v v′ : V} {r r′ : ℕ} → _≡_ {A = Res (Ap V)} (returns (done v r)) (returns (done v′ r′)) → v ≡ v′
    done-inj refl = refl

    st≢ret : ∀ {V : Set} {v : V} {r : ℕ} → _≡_ {A = Res (Ap V)} stopped (returns (done v r)) → ⊥
    st≢ret ()

    cut≢ret : ∀ {V : Set} {v : V} {r : ℕ} → _≡_ {A = Res (Ap V)} (returns cut) (returns (done v r)) → ⊥
    cut≢ret ()

    t≢f : true ≡ false → ⊥
    t≢f ()

  ------------------------------------------------------------------------
  -- RUNS COMPOSE ALONG A BIND.
  ------------------------------------------------------------------------
  module Bind {prog : AbstractTrace} {n : ℕ} {σ : FlatState} {X Y : Set} {m : T∞ X} {f : X → T∞ Y} {k : ℕ}
              {P : X → FlatState → Set} {Q : Y → FlatState → Set}
              (R : RoundRun prog n σ m k P)
              (K : ∀ {v r} → resultAt (floc σ) (⟪ m ⟫ k) ≡ returns (done v r) → RoundRun prog n (RoundRun.τ R) (f v) r Q)
              where

    module R = RoundRun R

    H : List SigOpEvent
    H = LocState.ev-log (floc σ)

    es₁ : List SigOpEvent
    es₁ = eventsAt (floc σ) (⟪ m ⟫ k)

    ρ₁ : Res (Ap X)
    ρ₁ = resultAt (floc σ) (⟪ m ⟫ k)

    BE : runAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ thenAp ιᶠ H es₁ ρ₁ f
    BE = run-approx-bind ιᶠ H k m f

    -- the first part RETURNED: the second runs from its end, at the budget left
    module Ret (v : X) (r : ℕ) (eq : ρ₁ ≡ returns (done v r)) where

      R2 : RoundRun prog n R.τ (f v) r Q
      R2 = K eq
      module R2 = RoundRun R2

      nc₁ : NotCut ρ₁
      nc₁ = subst NotCut (sym eq) tt

      RL : runAt (floc R.τ) (⟪ f v ⟫ r) ≡ TM.run ιᶠ (H ++ es₁) (⟪ f v ⟫ r)
      RL = cong (λ h → TM.run ιᶠ h (⟪ f v ⟫ r)) R.log

      BEq : runAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ TM.appE es₁ (runAt (floc R.τ) (⟪ f v ⟫ r))
      BEq = trans BE (trans (cong (λ ρ → thenAp ιᶠ H es₁ ρ f) eq) (cong (TM.appE es₁) (sym RL)))

      es₂ : List SigOpEvent
      es₂ = eventsAt (floc R.τ) (⟪ f v ⟫ r)

      ev-eq : eventsAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ es₁ ++ es₂
      ev-eq = cong proj₁ BEq

      res-eq : resultAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ resultAt (floc R.τ) (⟪ f v ⟫ r)
      res-eq = cong proj₂ BEq

      nc₂ : NotCut (resultAt (floc σ) (⟪ m >>=∞ f ⟫ k)) → NotCut (resultAt (floc R.τ) (⟪ f v ⟫ r))
      nc₂ = subst NotCut res-eq

      left₁ : LocState.left (floc R.τ) ≡ LocState.left (floc σ)
      left₁ = chain-left R.run (R.live (cong is-stopped eq))

      prog₁ : k ≤ r + chain-ctrls R.run
      prog₁ = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls R.run) eq R.progress

      out : RoundRun prog n σ (m >>=∞ f) k Q
      out = record
        { τ = R2.τ ; steps = R.steps + R2.steps ; run = FlatSteps-++ R.run R2.run
        ; events = trans (chain-events-++ R.run R2.run) (trans (cong₂ _++_ R.events R2.events) (sym ev-eq))
        ; log = trans R2.log (trans (cong (_++ es₂) R.log) (trans (++-assoc H es₁ es₂) (cong (H ++_) (sym ev-eq))))
        ; progress = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (FlatSteps-++ R.run R2.run)) (sym res-eq)
                       (progress-bind (resultAt (floc R.τ) (⟪ f v ⟫ r)) prog₁ R2.progress
                          (≤-reflexive (sym (chain-ctrls-++ R.run R2.run))))
        ; live = λ p → R2.live (trans (sym (cong is-stopped res-eq)) p)
        ; stops = λ p → proj₁ (R2.stops (trans (sym (cong is-stopped res-eq)) p))
                      , trans (proj₂ (R2.stops (trans (sym (cong is-stopped res-eq)) p))) left₁
        ; no-link = λ nc → R2.no-link (nc₂ nc)
        ; mem = λ nc loc b → trans (R2.mem (nc₂ nc) loc (R.bf nc₁ n loc b)) (R.mem nc₁ loc b)
        ; bf = λ nc mm loc b → R2.bf (nc₂ nc) mm loc (R.bf nc₁ mm loc b)
        ; same = λ p → record
            { ret = trans (Same.ret (R2.same (trans (sym res-eq) p))) (Same.ret (R.same eq))
            ; cf = trans (Same.cf (R2.same (trans (sym res-eq) p))) (Same.cf (R.same eq))
            ; sf = trans (Same.sf (R2.same (trans (sym res-eq) p))) (Same.sf (R.same eq)) }
        ; post = λ p → R2.post (trans (sym res-eq) p) }

    -- the first part STOPPED: so did the bind
    module Stop (eq : ρ₁ ≡ stopped) where

      BEq : runAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ (es₁ , stopped)
      BEq = trans BE (cong (λ ρ → thenAp ιᶠ H es₁ ρ f) eq)

      nc₁ : NotCut ρ₁
      nc₁ = subst NotCut (sym eq) tt

      res-eq : resultAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ stopped
      res-eq = cong proj₂ BEq

      out : RoundRun prog n σ (m >>=∞ f) k Q
      out = record
        { τ = R.τ ; steps = R.steps ; run = R.run
        ; events = trans R.events (sym (cong proj₁ BEq))
        ; log = trans R.log (cong (H ++_) (sym (cong proj₁ BEq)))
        ; progress = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls R.run) (sym res-eq) (m≤m+n k (chain-ctrls R.run))
        ; live = λ p → ⊥-elim (t≢f (trans (sym (cong is-stopped res-eq)) p))
        ; stops = λ _ → R.stops (cong is-stopped eq)
        ; no-link = λ _ → R.no-link nc₁
        ; mem = λ _ → R.mem nc₁
        ; bf = λ _ → R.bf nc₁
        ; same = λ p → ⊥-elim (st≢ret (trans (sym res-eq) p))
        ; post = λ p → ⊥-elim (st≢ret (trans (sym res-eq) p)) }

    -- the first part was CUT: so was the bind
    module Cut (eq : ρ₁ ≡ returns cut) where

      BEq : runAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ (es₁ , returns cut)
      BEq = trans BE (cong (λ ρ → thenAp ιᶠ H es₁ ρ f) eq)

      res-eq : resultAt (floc σ) (⟪ m >>=∞ f ⟫ k) ≡ returns cut
      res-eq = cong proj₂ BEq

      no-nc : NotCut (resultAt (floc σ) (⟪ m >>=∞ f ⟫ k)) → ⊥
      no-nc nc = subst NotCut res-eq nc

      out : RoundRun prog n σ (m >>=∞ f) k Q
      out = record
        { τ = R.τ ; steps = R.steps ; run = R.run
        ; events = trans R.events (sym (cong proj₁ BEq))
        ; log = trans R.log (cong (H ++_) (sym (cong proj₁ BEq)))
        ; progress = subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls R.run) (sym res-eq)
                       (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls R.run) eq R.progress)
        ; live = λ _ → R.live (cong is-stopped eq)
        ; stops = λ p → ⊥-elim (t≢f (trans (sym p) (cong is-stopped res-eq)))
        ; no-link = λ nc → ⊥-elim (no-nc nc)
        ; mem = λ nc → ⊥-elim (no-nc nc)
        ; bf = λ nc → ⊥-elim (no-nc nc)
        ; same = λ p → ⊥-elim (cut≢ret (trans (sym res-eq) p))
        ; post = λ p → ⊥-elim (cut≢ret (trans (sym res-eq) p)) }

    go : (ρ : Res (Ap X)) → ρ₁ ≡ ρ → RoundRun prog n σ (m >>=∞ f) k Q
    go (returns (done v r)) eq = Ret.out v r eq
    go stopped             eq = Stop.out eq
    go (returns cut)       eq = Cut.out eq

    out : RoundRun prog n σ (m >>=∞ f) k Q
    out = go ρ₁ refl

  bind-rr : ∀ {prog : AbstractTrace} {n : ℕ} {σ : FlatState} {X Y : Set} {m : T∞ X} {f : X → T∞ Y} {k : ℕ}
              {P : X → FlatState → Set} {Q : Y → FlatState → Set}
          → (R : RoundRun prog n σ m k P)
          → (∀ {v r} → resultAt (floc σ) (⟪ m ⟫ k) ≡ returns (done v r) → RoundRun prog n (RoundRun.τ R) (f v) r Q)
          → RoundRun prog n σ (m >>=∞ f) k Q
  bind-rr {prog} {n} {σ} {X} {Y} {m} {f} {k} {P} {Q} R K = Bind.out {prog} {n} {σ} {X} {Y} {m} {f} {k} {P} {Q} R K

  ------------------------------------------------------------------------
  -- A RETURN IS THE EMPTY RUN.
  ------------------------------------------------------------------------
  pure-rr : ∀ {prog : AbstractTrace} {n : ℕ} (σ : FlatState) {Y : Set} (y : Y) (k : ℕ) {Q : Y → FlatState → Set}
          → halted (floc σ) ≡ false → flink σ ≡ nothing → Q y σ
          → RoundRun prog n σ (return∞ y) k Q
  pure-rr {prog} σ y k {Q} nh lk q = record
    { τ = σ ; steps = 0 ; run = []
    ; events = chain-events-nil {prog} {σ}
    ; log = sym (++-identityʳ _)
    ; progress = m≤m+n k _
    ; live = λ _ → nh
    ; stops = λ p → ⊥-elim (f≢t p)
    ; no-link = λ _ → lk
    ; mem = λ _ _ _ → refl
    ; bf = λ _ _ _ b → b
    ; same = λ _ → record { ret = refl ; cf = refl ; sf = refl }
    ; post = λ p → subst (λ z → Q z σ) (done-inj p) q }
    where
      f≢t : false ≡ true → ⊥
      f≢t ()
