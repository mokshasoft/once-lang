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
open import Relation.Nullary using (¬_)
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

  ----------------------------------------------------------------------
  -- 4. HELPERS for the moving steps.
  ----------------------------------------------------------------------

  -- the top environment slot's buffer: the words of what it sees
  topW : ∀ {rd sm E Es} (es : Slots (E ∷ Es)) → EnvW rd sm es → Σ (List W) λ w → VW rd (see es) w × SlotsAt sm (ws Es) w
  topW (vw e es)   (b , _) = b
  topW (ln e x es) (b , _) = b

  -- a pair's words are its components'
  vpair-inv : ∀ {rd A B} {a : MV A} {b : MV B} {w} → VW rd (mpair a b) w
            → Σ (List W) λ wa → Σ (List W) λ wb → w ≡ wa ++ wb × VW rd a wa × VW rd b wb
  vpair-inv (vpair {wa = wa} {wb} p q) = wa , wb , refl , p , q

  -- defined words at slots
  slots-def : ∀ {sm o} (w : List W) → SlotsAt sm o w → ∀ k → k < length w → Σ W λ v → sm (k + o) ≡ just v
  slots-def (x ∷ w) (e , s) zero    _        = x , e
  slots-def {sm} {o} (x ∷ w) (e , s) (suc k) (s≤s k<) with slots-def {sm} {suc o} w s k k<
  ... | (v , ev) = v , trans (cong sm (sym (+-suc k o))) ev

  -- the words a move leaves at its destination
  open import Once.LinCore.Moves {FS} using (Seg; slot; mvSS-run; MovedS; m-moved; m-rest; m-heap; m-halt; m-pc) renaming (ln to nsteps)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open import Once.CCC.Machine.SMCore using (module LocState; module AllocState)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Data.Bool using (false)

  slots-moved : ∀ {fs fs′ a b n} (w : List W) → MovedS fs fs′ a b n → SlotsAt (slot fs) a w → length w ≡ n
              → SlotsAt (slot fs′) b w
  slots-moved {fs} {fs′} {a} {b} {n} w M s refl = go w 0 s (λ k k< → m-moved M k k<)
    where
      go : ∀ (v : List W) j → SlotsAt (slot fs) (j + a) v
         → (∀ k → k < j + length v → slot fs′ (k + b) ≡ slot fs (k + a)) → SlotsAt (slot fs′) (j + b) v
      go []      j s h = tt
      go (x ∷ v) j (e , s) h =
        trans (h j (subst (j <_) (sym (+-suc j (length v))) (s≤s (m≤m+n j (length v))))) e ,
        go v (suc j) s (λ k k< → h k (subst (k <_) (sym (+-suc j (length v))) k<))

  -- a store above a read never clobbers it
  no-clash : ∀ {a b k k′ n} → a + n ≤ b → k′ < n → ¬ k + b ≡ k′ + a
  no-clash {a} {b} {k} {k′} {n} le lt eq =
    Data.Nat.Properties.<-irrefl (sym eq)
      (Data.Nat.Properties.<-≤-trans (+-monoˡ-< a lt)
        (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm n a)) (≤-trans le (m≤n+m b k))))
    where import Data.Nat.Properties

  -- the environment region lies below the operand region
  env-below : ∀ φ s → s ≤ OP φ → EP φ ≤ budget φ ∸ s
  env-below φ s le = ≤-trans (m≤m+n (EP φ) (OP φ ∸ s)) (Data.Nat.Properties.≤-reflexive (sym (Data.Nat.Properties.+-∸-assoc (EP φ) le)))
    where import Data.Nat.Properties

  open CfgW

  ----------------------------------------------------------------------
  -- 5. ★ THE VIEW STEPS.
  ----------------------------------------------------------------------

  open import Once.LinCore.MoveCode using (mvSS)

  -- ★ `efst`: the pair's first component's words, into a new buffer above
  efst-sim : ∀ prog (fs : FlatState) (φ : Frame) {E₁ E₂ Es S} {es : Slots ((E₁ ⊗t E₂) ∷ Es)} {os : Stk S}
               {e₁ : MV E₁} {e₂ : MV E₂}
           → see es ≡ mpair e₁ e₂
           → Seg prog (fpc fs) (mvSS (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁))
           → fhalted (floc fs) ≡ false
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
           → ws (E₁ ∷ (E₁ ⊗t E₂) ∷ Es) ≤ EP φ
           → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz E₁)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₁ es ∥ os) × MovedS fs fs′ (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁)
  efst-sim prog fs φ {E₁} {E₂} {Es} {S} {es} {os} {e₁} {e₂} eq s h C fit with topW es (c-env C)
  ... | (w , pw , sw) with vpair-inv (subst (λ z → VW (heapMem (floc fs)) z w) eq pw)
  ...   | (wa , wb , refl , pa , pb) with slots-++ {slot fs} wa wb sw
  ...     | (sa , _) with mvSS-run prog fs (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁) s h def nc
    where
      def : ∀ k → k < wsz E₁ → Σ W λ v → slot fs (k + ws Es) ≡ just v
      def k k< = slots-def wa sa k (subst (k <_) (sym (vw-len pa)) k<)
      nc : ∀ k k′ → k < k′ → k′ < wsz E₁ → ¬ k + (ws Es + wsz (E₁ ⊗t E₂)) ≡ k′ + ws Es
      nc k k′ _ lt = no-clash {k = k} (Data.Nat.Properties.+-monoʳ-≤ (ws Es) (m≤m+n (wsz E₁) (wsz E₂))) lt
        where import Data.Nat.Properties
  ...       | (fs′ , st , M) =
    fs′ , st ,
    record { c-env  = (wa , heap pa , subst (λ z → SlotsAt (slot fs′) z wa) (+-comm (ws Es) (wsz (E₁ ⊗t E₂)))
                                             (slots-moved wa M sa (vw-len pa)))
                    , envW-frame {heapMem (floc fs′)} es (λ x x< → m-rest M x (λ k _ e → above x x< k e)) (envH (c-env C))
           ; c-stk  = stkW-frame os (fitS) (λ x lo hi → m-rest M x (λ k k< e → under x lo k k< e)) (stkH (c-stk C))
           ; c-efit = fit ; c-sfit = c-sfit C }
    , M
    where
      w12 = wsz (E₁ ⊗t E₂)
      heap : ∀ {A} {v : MV A} {ws′} → VW (heapMem (floc fs)) v ws′ → VW (heapMem (floc fs′)) v ws′
      heap p = subst (λ r → VW r _ _) (sym (m-heap M)) p
      envH : EnvW (heapMem (floc fs)) (slot fs) es → EnvW (heapMem (floc fs′)) (slot fs) es
      envH e = subst (λ r → EnvW r (slot fs) es) (sym (m-heap M)) e
      stkH : StkW (heapMem (floc fs)) (slot fs) φ os → StkW (heapMem (floc fs′)) (slot fs) φ os
      stkH e = subst (λ r → StkW r (slot fs) φ os) (sym (m-heap M)) e
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))
      -- the new buffer is above the old ones
      above : ∀ x → x < ws ((E₁ ⊗t E₂) ∷ Es) → ∀ k → ¬ x ≡ k + (ws Es + w12)
      above x x< k e = Data.Nat.Properties.<-irrefl e
                         (<-≤-trans x< (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm w12 (ws Es))) (m≤n+m (ws Es + w12) k)))
        where import Data.Nat.Properties
      -- …and below the operand stack
      under : ∀ x → budget φ ∸ ws S ≤ x → ∀ k → k < wsz E₁ → ¬ x ≡ k + (ws Es + w12)
      under x lo k k< e = Data.Nat.Properties.<-irrefl (sym e)
                            (<-≤-trans (+-monoˡ-< (ws Es + w12) k<)
                              (≤-trans (Data.Nat.Properties.≤-reflexive (top-words))
                                (≤-trans fit (≤-trans (env-below φ (ws S) (c-sfit C)) lo))))
        where import Data.Nat.Properties
              top-words : wsz E₁ + (ws Es + w12) ≡ ws (E₁ ∷ (E₁ ⊗t E₂) ∷ Es)
              top-words = cong (wsz E₁ +_) (+-comm (ws Es) w12)
