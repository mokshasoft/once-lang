-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSimD — plan 0.146 B1.4b, `LowerSim` layer (4),
-- continued: the BRANCHES. A `case` tests the tag on the stack; `inl` jumps
-- to its label (given: the whole-run relation resolves it), `inr` falls
-- through; each shifts its payload up to the result's place.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n; _⊔_)
import Data.Nat.Properties
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-trans; ≤-reflexive; m≤n+m; m≤m+n; +-monoˡ-<; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using ( StoredValue; SV-Ptr; SV-Tag; readReg; writeReg; Input1; Output; lea-slot; mov-to-input; instr-ctrl
        ; c-branch-tag-zero; c-label; module AllocState; module LocState; module MemOps )
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Label using (LabelId)

module Once.LinCore.LowerSimD
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; minl; minr)
open import Once.LinCore.Machine fmt ans bw using (Stk; _∷ˢ_; Slots; _∥_)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.MoveCode using (mvSSd)

module SimD {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open import Once.LinCore.Moves {FS} using (Seg; slot; mvSSd-run; MovedD; d-moved; d-rest; d-heap; d-pc; lea-step; mov-in-step)
    renaming (ln to nsteps; d-halt to dm-halt)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fetch; find-label)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps; step-at; FlatSteps-++; flat-tag-branch-yes; flat-tag-branch-not; flat-label)
    renaming ([] to done)

  -- the words a descending move leaves at its destination
  slots-movedD : ∀ {fs fs′ a b n} (w : List W) → MovedD fs fs′ a b n → SlotsAt (slot fs) a w → length w ≡ n
               → SlotsAt (slot fs′) b w
  slots-movedD {fs} {fs′} {a} {b} {n} w M s refl =
    subst (λ z → SlotsAt (slot fs′) z w) (Data.Nat.Properties.+-identityʳ b)
      (go w 0 (subst (λ z → SlotsAt (slot fs) z w) (sym (Data.Nat.Properties.+-identityʳ a)) s) (λ k k< → d-moved M k k<))
    where
      go : ∀ (v : List W) j → SlotsAt (slot fs) (a + j) v
         → (∀ k → k < j + length v → slot fs′ (b + k) ≡ slot fs (a + k)) → SlotsAt (slot fs′) (b + j) v
      go []      j s h = tt
      go (x ∷ v) j (e , s) h =
        trans (h j (subst (j <_) (sym (+-suc j (length v))) (s≤s (m≤m+n j (length v))))) e ,
        subst (λ z → SlotsAt (slot fs′) z v) (+-suc b j)
          (go v (suc j) (subst (λ z → SlotsAt (slot fs) z v) (sym (+-suc a j)) s)
             (λ k k< → h k (subst (k <_) (sym (+-suc j (length v))) k<)))

  -- the arithmetic of a sum on the stack
  private
    new-top : ∀ B a s → (B ∸ s) ∸ a ≡ B ∸ (a + s)
    new-top B a s = trans (Data.Nat.Properties.∸-+-assoc B s a) (cong (B ∸_) (+-comm s a))

    suc-∸ : ∀ m n → n < m → suc (m ∸ suc n) ≡ m ∸ n
    suc-∸ (suc m) zero    _        = refl
    suc-∸ (suc m) (suc n) (s≤s lt) = suc-∸ m n lt

  -- ★ a sum's payload shifted up from just past its tag to its own place
  -- (the result of a `case`): the rest of the stack and the environment kept
  shift-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es P S} {es : Slots Es} {os : Stk S} {p : MV P} (src : ℕ) (wP : List W)
            → Seg prog (fpc fs) (mvSSd src ((budget φ ∸ ws S) ∸ wsz P) (wsz P))
            → fhalted (floc fs) ≡ false
            → EnvW (heapMem (floc fs)) (slot fs) es → StkW (heapMem (floc fs)) (slot fs) φ os
            → VW (heapMem (floc fs)) p wP → SlotsAt (slot fs) src wP
            → src ≤ (budget φ ∸ ws S) ∸ wsz P → EP φ ≤ src → ws Es ≤ EP φ → ws (P ∷ S) ≤ OP φ
            → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz P)) fs fs′
                × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ p ∷ˢ os) × fpc fs′ ≡ nsteps (wsz P) + fpc fs
  shift-sim prog fs φ {Es} {P} {S} {es} {os} {p} src wP s h ev st pp sp up ep efit fit =
    fin (mvSSd-run prog fs src dst (wsz P) s h
           (λ k k< → def k k<)
           (λ k k′ lt _ e → Data.Nat.Properties.<-irrefl (sym e)
                              (Data.Nat.Properties.<-≤-trans (Data.Nat.Properties.+-monoʳ-< src lt) (Data.Nat.Properties.+-monoˡ-≤ k up))))
    where
      dst = (budget φ ∸ ws S) ∸ wsz P
      def : ∀ k → k < wsz P → Σ W λ v → slot fs (src + k) ≡ just v
      def k k< with slots-def {slot fs} {src} wP sp k (subst (k <_) (sym (vw-len pp)) k<)
      ... | (v , e) = v , trans (cong (slot fs) (+-comm src k)) e
      fitB : wsz P + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) (wsz P)) fitB
      -- the destination: [dst, bot)
      in-dst : ∀ k → k < wsz P → dst + k < budget φ ∸ ws S
      in-dst k k< = Data.Nat.Properties.<-≤-trans (Data.Nat.Properties.+-monoʳ-< dst k<) (≤-reflexive (Data.Nat.Properties.m∸n+n≡m (≤∸ (wsz P) (ws S) (budget φ) fitB)))
      fin : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz P)) fs fs′ × MovedD fs fs′ src dst (wsz P))
          → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz P)) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ p ∷ˢ os) × fpc fs′ ≡ nsteps (wsz P) + fpc fs
      fin (fs′ , st′ , M) =
        fs′ , st′ ,
        record { c-env  = subst (λ r → EnvW r (slot fs′) es) (sym (d-heap M))
                            (envW-frame es (λ x x< → d-rest M x (λ k k< e → Data.Nat.Properties.<-irrefl e
                                              (Data.Nat.Properties.<-≤-trans x< (≤-trans efit (≤-trans ep (≤-trans up (m≤m+n dst k))))))) ev)
               ; c-stk  = ( wP , subst (λ r → VW r p wP) (sym (d-heap M)) pp
                          , subst (λ z → SlotsAt (slot fs′) z wP) (new-top (budget φ) (wsz P) (ws S)) (slots-movedD wP M sp (vw-len pp)) )
                        , subst (λ r → StkW r (slot fs′) φ os) (sym (d-heap M))
                            (stkW-frame os fitS (λ x lo _ → d-rest M x (λ k k< e → Data.Nat.Properties.<-irrefl (sym e)
                                                   (Data.Nat.Properties.<-≤-trans (in-dst k k<) lo))) st)
               ; c-efit = efit ; c-sfit = fit } ,
        d-pc M
