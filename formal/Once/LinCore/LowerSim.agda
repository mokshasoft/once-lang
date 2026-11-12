-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSim — plan 0.146 B1.4b, `LowerSim` layer (4): each
-- image step against its lowered code.
--
-- Here first: the steps whose lowering is EMPTY (D416: a pair on the stack
-- is its components in place; a tag is no word; a unit and a lifted view
-- are no words): the flat machine does not move, and the same slots hold
-- the image's next configuration.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (+-assoc; +-comm; m∸n+n≡m; ∸-+-assoc; +-∸-assoc; ≤-trans; m≤m+n; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (StoredValue)
open import Once.Memory.HeapAddress using (HeapLocation)

module Once.LinCore.LowerSim
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw

module Sim {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf

  ----------------------------------------------------------------------
  -- 1. WORDS AT SLOTS: split and joined.
  ----------------------------------------------------------------------

  slots-++ : ∀ {sm o} (xs ys : List W) → SlotsAt sm o (xs ++ ys) → SlotsAt sm o xs × SlotsAt sm (length xs + o) ys
  slots-++ []       ys s       = tt , s
  slots-++ {sm} {o} (x ∷ xs) ys (e , s) with slots-++ {sm} {suc o} xs ys s
  ... | (a , b) = (e , a) , subst (λ z → SlotsAt sm z ys) (+-suc′ (length xs) o) b
    where
      +-suc′ : ∀ m n → m + suc n ≡ suc m + n
      +-suc′ m n = Data.Nat.Properties.+-suc m n
        where import Data.Nat.Properties

  slots-join : ∀ {sm o} (xs ys : List W) → SlotsAt sm o xs → SlotsAt sm (length xs + o) ys → SlotsAt sm o (xs ++ ys)
  slots-join []       ys tt      b = b
  slots-join {sm} {o} (x ∷ xs) ys (e , a) b =
    e , slots-join {sm} {suc o} xs ys a (subst (λ z → SlotsAt sm z ys) (sym (Data.Nat.Properties.+-suc (length xs) o)) b)
    where import Data.Nat.Properties

  ----------------------------------------------------------------------
  -- 2. ★ THE EMPTY STEPS: the same slots, the image's next configuration.
  ----------------------------------------------------------------------

  -- the offset arithmetic of a stack whose top two are one pair's
  private
    pair-at : ∀ B (a b s : ℕ) → a + (b + s) ≤ B → a + (B ∸ (a + (b + s))) ≡ B ∸ (b + s)
    pair-at B a b s le =
      sym (trans (cong (_∸ (b + s)) (sym (m∸n+n≡m le)))
          (trans (cong (_∸ (b + s)) (sym (+-assoc X a (b + s))))
          (trans (Data.Nat.Properties.m+n∸n≡m (X + a) (b + s)) (+-comm X a))))
      where import Data.Nat.Properties
            X = B ∸ (a + (b + s))

  -- ★ `unpair`: a pair's words are its components', in place
  unpair-W : ∀ {rd sm φ A B S} {a : MV A} {b : MV B} {os : Stk S}
           → ws (A ∷ B ∷ S) ≤ budget φ → StkW rd sm φ (mpair a b ∷ˢ os) → StkW rd sm φ (a ∷ˢ b ∷ˢ os)
  unpair-W {rd} {sm} {φ} {A} {B} {S} le ((_ , vpair {wa = wa} {wb} pa pb , sl) , rest) with slots-++ {sm} wa wb sl′
    where sl′ = subst (λ z → SlotsAt sm (budget φ ∸ z) (wa ++ wb)) (+-assoc (wsz A) (wsz B) (ws S)) sl
  ... | (sa , sb) =
    (wa , pa , sa) ,
    (wb , pb , subst (λ z → SlotsAt sm z wb)
                 (trans (cong (_+ (budget φ ∸ ws (A ∷ B ∷ S))) (vw-len pa)) (pair-at (budget φ) (wsz A) (wsz B) (ws S) le)) sb) ,
    rest

  -- ★ `pair`: two components in place are their pair's words
  pair-W : ∀ {rd sm φ A B S} {a : MV A} {b : MV B} {os : Stk S}
         → ws (A ∷ B ∷ S) ≤ budget φ → StkW rd sm φ (a ∷ˢ b ∷ˢ os) → StkW rd sm φ (mpair a b ∷ˢ os)
  pair-W {rd} {sm} {φ} {A} {B} {S} le ((wa , pa , sa) , (wb , pb , sb) , rest) =
    (wa ++ wb , vpair pa pb ,
      subst (λ z → SlotsAt sm (budget φ ∸ z) (wa ++ wb)) (sym (+-assoc (wsz A) (wsz B) (ws S)))
        (slots-join {sm} wa wb sa
          (subst (λ z → SlotsAt sm z wb)
             (sym (trans (cong (_+ (budget φ ∸ ws (A ∷ B ∷ S))) (vw-len pa)) (pair-at (budget φ) (wsz A) (wsz B) (ws S) le))) sb))) ,
    rest

  -- ★ `untag`, `untag₁`, `tag₁`: a tagged closure is its environment's words
  untag-W : ∀ {rd sm φ l X A S} {x : MV X} {a : MV A} {os : Stk S}
          → StkW rd sm φ (mpair (mct {l = l} x) a ∷ˢ os) → StkW rd sm φ (mpair x a ∷ˢ os)
  untag-W ((w , vpair (vct px) pa , sl) , rest) = (w , vpair px pa , sl) , rest

  untag₁-W : ∀ {rd sm φ l X S} {x : MV X} {os : Stk S}
           → StkW rd sm φ (mct {l = l} x ∷ˢ os) → StkW rd sm φ (x ∷ˢ os)
  untag₁-W ((w , vct px , sl) , rest) = (w , px , sl) , rest

  tag₁-W : ∀ {rd sm φ l X S} {x : MV X} {os : Stk S}
         → StkW rd sm φ (x ∷ˢ os) → StkW rd sm φ (mct {l = l} x ∷ˢ os)
  tag₁-W ((w , px , sl) , rest) = (w , vct px , sl) , rest

  -- ★ `unit`: no words
  unit-W : ∀ {rd sm φ S} {os : Stk S} → StkW rd sm φ os → StkW rd sm φ (mone ∷ˢ os)
  unit-W st = ([] , vone , tt) , st

  -- ★ `elift`, `epop`: a lifted view is no words; a popped view's buffer is left
  elift-W : ∀ {rd sm Es} {es : Slots Es} → EnvW rd sm es → EnvW rd sm (vw mone es)
  elift-W ev = ([] , vone , tt) , ev

  epop-W : ∀ {rd sm E Es} {e : MV E} {es : Slots Es} → EnvW rd sm (vw e es) → EnvW rd sm es
  epop-W (_ , ev) = ev

  ----------------------------------------------------------------------
  -- 3. ★ FRAME STABILITY: a region's words stand while its slots do.
  ----------------------------------------------------------------------

  open import Data.Nat using (_<_; s≤s; z≤n)
  open import Data.Nat.Properties using (≤-refl; +-monoʳ-≤; +-monoˡ-<; <-≤-trans; ≤-<-trans; m∸n≤m; +-suc)

  slots-frame : ∀ {sm sm′ : ℕ → Maybe W} {o} (w : List W)
              → (∀ k → k < length w → sm′ (k + o) ≡ sm (k + o)) → SlotsAt sm o w → SlotsAt sm′ o w
  slots-frame []       h tt      = tt
  slots-frame {sm} {sm′} {o} (x ∷ w) h (e , s) =
    trans (h 0 (s≤s z≤n)) e ,
    slots-frame {sm} {sm′} {suc o} w (λ k k< → trans (cong sm′ (+-suc k o)) (trans (h (suc k) (s≤s k<)) (cong sm (sym (+-suc k o))))) s

  -- the environment's buffers lie below its words
  envW-frame : ∀ {rd} {sm sm′ : ℕ → Maybe W} {Es} (es : Slots Es)
             → (∀ x → x < ws Es → sm′ x ≡ sm x) → EnvW rd sm es → EnvW rd sm′ es
  envW-frame []ᵉ h tt = tt
  envW-frame {rd} {sm} {sm′} (vw {E = E} {Es = Es} e es) h ((w , p , s) , ev) =
    (w , p , slots-frame {sm} {sm′} w (λ k k< → h (k + ws Es) (+-monoˡ-< (ws Es) (subst (k <_) (vw-len p) k<))) s) ,
    envW-frame es (λ x x< → h x (<-≤-trans x< (m≤n+m (ws Es) (wsz E)))) ev
  envW-frame {rd} {sm} {sm′} (ln {E = E} {X = X} {Es = Es} e x es) h ((w , p , s) , ev) =
    (w , p , slots-frame {sm} {sm′} w (λ k k< → h (k + ws (E ∷ Es)) (+-monoˡ-< (ws (E ∷ Es)) (subst (k <_) (vw-len p) k<))) s) ,
    envW-frame es (λ y y< → h y (<-≤-trans y< (m≤n+m (ws (E ∷ Es)) (wsz (E ⊗t X))))) ev

  -- the operand stack's words lie in [budget ∸ its words, budget)
  open import Data.Nat.Properties using (∸-monoʳ-≤)

  stkW-frame : ∀ {rd} {sm sm′ : ℕ → Maybe W} {φ S} (os : Stk S) → ws S ≤ budget φ
             → (∀ x → budget φ ∸ ws S ≤ x → x < budget φ → sm′ x ≡ sm x) → StkW rd sm φ os → StkW rd sm′ φ os
  stkW-frame []ˢ fit h tt = tt
  stkW-frame {rd} {sm} {sm′} {φ} (_∷ˢ_ {A} {S} v os) fit h ((w , p , s) , st) =
    (w , p , slots-frame {sm} {sm′} w (λ k k< → h (k + o) (m≤n+m o k) (in-range k (subst (k <_) (vw-len p) k<))) s) ,
    stkW-frame os fitS (λ x lo hi → h x (≤-trans (∸-monoʳ-≤ (budget φ) (m≤n+m (ws S) (wsz A))) lo) hi) st
    where
      o = budget φ ∸ ws (A ∷ S)
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) (wsz A)) fit
      in-range : ∀ k → k < wsz A → k + o < budget φ
      in-range k k< = <-≤-trans (+-monoˡ-< o k<)
                        (≤-trans (Data.Nat.Properties.≤-reflexive (pair-at (budget φ) (wsz A) 0 (ws S) fit))
                                 (m∸n≤m (budget φ) (ws S)))
        where import Data.Nat.Properties
