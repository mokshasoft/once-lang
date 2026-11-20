-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowerSim — plan 0.146 B1.4b, `LowerSim` layer (4): each
-- image step against its lowered code.
--
-- Here first: the steps whose lowering is EMPTY (D433: a pair on the stack
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
import Data.Empty
open import Function using (case_of_)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (StoredValue)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Machine.Locations using (AtStack)

module Once.LinCore.LowerSim
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b)
open Sg using (env)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.Keys fmt bw
open import Once.LinCore.Layout fmt bw
open Frame using (EP; OP)
open import Once.LinCore.Words fmt ans bw

module Sim {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf

  ----------------------------------------------------------------------
  -- 1. WORDS AT SLOTS: split and joined.
  ----------------------------------------------------------------------

  slots-++ : ∀ {sm o} (xs ys : List W) → SlotsAt sm o (xs ++ ys) → SlotsAt sm o xs × SlotsAt sm (length xs + o) ys
  slots-++ []       ys s       = tt , s
  slots-++ {sm} {o} (x ∷ xs) ys (e , s) = case slots-++ {sm} {suc o} xs ys s of λ where
      (a , b) → (e , a) , subst (λ z → SlotsAt sm z ys) (Data.Nat.Properties.+-suc (length xs) o) b
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
  unpair-W {rd} {sm} {φ} {A} {B} {S} le ((_ , vpair {wa = wa} {wb} pa pb , sl) , rest) = case slots-++ {sm} wa wb sl′ of λ where
      (sa , sb) →
        (wa , pa , sa) ,
        (wb , pb , subst (λ z → SlotsAt sm z wb)
                     (trans (cong (_+ (budget φ ∸ ws (A ∷ B ∷ S))) (vw-len pa)) (pair-at (budget φ) (wsz A) (wsz B) (ws S) le)) sb) ,
        rest
    where sl′ = subst (λ z → SlotsAt sm (budget φ ∸ z) (wa ++ wb)) (+-assoc (wsz A) (wsz B) (ws S)) sl

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
  slots-def {sm} {o} (x ∷ w) (e , s) (suc k) (s≤s k<) = case slots-def {sm} {suc o} w s k k< of λ where
    (v , ev) → v , trans (cong sm (sym (+-suc k o))) ev

  -- the words a move leaves at its destination
  open import Once.LinCore.Moves {FS} using (Seg; slot; Fr; InFr; module InFr; InFrD; infr; infrD; top-in; sub-in; sub-le; mvSS-run; MovedS; Keep; keep-refl; keep-trans; keepS; keepP; keepF; keepW; keep-regs; keep-store; keep-pc; keep-heap; Ran; ran-trans; ranS; ranP; ranF; ranW; ran-regs; ran-store; ran-pc; ran-heap; fresh-block; ran-hi; pred<; inb-write; module MovedS) renaming (ln to nsteps)
  open MovedS using (m-pc; m-heap; m-halt; m-moved; m-rest; m-alloc)
  open InFr using (in-fr)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fpc)
  open import Once.CCC.Machine.SMCore using (module LocState; module AllocState)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Data.Bool using (false; true)

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

  -- the environment region is the bottom of the frame
  env-in : ∀ φ {x} → x ≤ EP φ → x ≤ budget φ
  env-in φ le = ≤-trans le (m≤m+n (EP φ) (OP φ))

  open CfgW

  ----------------------------------------------------------------------
  -- 5. ★ THE VIEW STEPS.
  ----------------------------------------------------------------------

  open import Once.LinCore.MoveCode using (mvSS)

  -- ★ A NEW VIEW: words inside the top buffer (what a part of the viewed value
  -- is), copied into a new buffer above it; the buffers below and the
  -- operand stack stand, the heap is untouched
  view-sim : ∀ prog (fs : FlatState) (φ : Frame) {E E′ Es S} {es : Slots (E ∷ Es)} {os : Stk S} {v′ : MV E′}
               (src : ℕ) (w′ : List W)
           → VW (heapMem (floc fs)) v′ w′ → SlotsAt (slot fs) src w′ → src + wsz E′ ≤ ws (E ∷ Es)
           → Seg prog (fpc fs) (mvSS src (ws Es + wsz E) (wsz E′))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
           → ws (E′ ∷ E ∷ Es) ≤ EP φ
           → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz E′)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw v′ es ∥ os) × MovedS fs fs′ src (ws Es + wsz E) (wsz E′)
  view-sim prog fs φ {E} {E′} {Es} {S} {es} {os} {v′} src w′ pv sv inside s h B C fit =
    fin (mvSS-run prog fs src (ws Es + wsz E) (wsz E′) s h
           (infr B (env-in φ (≤-trans inside (≤-trans (m≤n+m (ws (E ∷ Es)) (wsz E′)) fit))))
           (infr B (env-in φ (≤-trans (Data.Nat.Properties.≤-reflexive top-view) fit))) def nc)
    where
      import Data.Nat.Properties
      top-view : ws Es + wsz E + wsz E′ ≡ ws (E′ ∷ E ∷ Es)
      top-view = trans (+-comm (ws Es + wsz E) (wsz E′)) (cong (wsz E′ +_) (+-comm (ws Es) (wsz E)))
      def : ∀ k → k < wsz E′ → Σ W λ v → slot fs (k + src) ≡ just v
      def k k< = slots-def w′ sv k (subst (k <_) (sym (vw-len pv)) k<)
      nc : ∀ k k′ → k < k′ → k′ < wsz E′ → ¬ k + (ws Es + wsz E) ≡ k′ + src
      nc k k′ _ lt = no-clash {k = k} (≤-trans inside (Data.Nat.Properties.≤-reflexive (+-comm (wsz E) (ws Es)))) lt
        where import Data.Nat.Properties
      fin : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz E′)) fs fs′ × MovedS fs fs′ src (ws Es + wsz E) (wsz E′))
          → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz E′)) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw v′ es ∥ os) × MovedS fs fs′ src (ws Es + wsz E) (wsz E′)
      fin (fs′ , st , M) =
        fs′ , st ,
        record { c-env  = (w′ , heap pv , subst (λ z → SlotsAt (slot fs′) z w′) (+-comm (ws Es) (wsz E))
                                                (slots-moved w′ M sv (vw-len pv)))
                        , envW-frame {heapMem (floc fs′)} es (λ x x< → m-rest M x (λ k _ e → above x x< k e)) (envH (c-env C))
               ; c-stk  = stkW-frame os fitS (λ x lo hi → m-rest M x (λ k k< e → under x lo k k< e)) (stkH (c-stk C))
               ; c-efit = fit ; c-sfit = c-sfit C }
        , M
        where
          heap : ∀ {A} {v : MV A} {ws′} → VW (heapMem (floc fs)) v ws′ → VW (heapMem (floc fs′)) v ws′
          heap p = subst (λ r → VW r _ _) (sym (m-heap M)) p
          envH : EnvW (heapMem (floc fs)) (slot fs) es → EnvW (heapMem (floc fs′)) (slot fs) es
          envH e = subst (λ r → EnvW r (slot fs) es) (sym (m-heap M)) e
          stkH : StkW (heapMem (floc fs)) (slot fs) φ os → StkW (heapMem (floc fs′)) (slot fs) φ os
          stkH e = subst (λ r → StkW r (slot fs) φ os) (sym (m-heap M)) e
          fitS : ws S ≤ budget φ
          fitS = ≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))
          above : ∀ x → x < ws (E ∷ Es) → ∀ k → ¬ x ≡ k + (ws Es + wsz E)
          above x x< k e = Data.Nat.Properties.<-irrefl e
                             (<-≤-trans x< (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (wsz E) (ws Es))) (m≤n+m (ws Es + wsz E) k)))
          under : ∀ x → budget φ ∸ ws S ≤ x → ∀ k → k < wsz E′ → ¬ x ≡ k + (ws Es + wsz E)
          under x lo k k< e = Data.Nat.Properties.<-irrefl (sym e)
                                (<-≤-trans (+-monoˡ-< (ws Es + wsz E) k<)
                                  (≤-trans (Data.Nat.Properties.≤-reflexive top-words)
                                    (≤-trans fit (≤-trans (env-below φ (ws S) (c-sfit C)) lo))))
            where top-words : wsz E′ + (ws Es + wsz E) ≡ ws (E′ ∷ E ∷ Es)
                  top-words = cong (wsz E′ +_) (+-comm (ws Es) (wsz E))

  -- the top buffer, and the words of a pair it sees
  private
    top-pair : ∀ {rd sm E₁ E₂ Es} (es : Slots ((E₁ ⊗t E₂) ∷ Es)) {e₁ : MV E₁} {e₂ : MV E₂} → see es ≡ mpair e₁ e₂
             → EnvW rd sm es
             → Σ (List W) λ wa → Σ (List W) λ wb → VW rd e₁ wa × VW rd e₂ wb
               × SlotsAt sm (ws Es) wa × SlotsAt sm (length wa + ws Es) wb
    top-pair {rd} {sm} {Es = Es} es eq ev = case topW es ev of λ where
      (w , pw , sw) → case vpair-inv (subst (λ z → VW rd z w) eq pw) of λ where
        (wa , wb , refl , pa , pb) → case slots-++ {sm} wa wb sw of λ where
          (sa , sb) → wa , wb , pa , pb , sa , sb

  -- ★ `efst`
  efst-sim : ∀ prog (fs : FlatState) (φ : Frame) {E₁ E₂ Es S} {es : Slots ((E₁ ⊗t E₂) ∷ Es)} {os : Stk S}
               {e₁ : MV E₁} {e₂ : MV E₂}
           → see es ≡ mpair e₁ e₂
           → Seg prog (fpc fs) (mvSS (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
           → ws (E₁ ∷ (E₁ ⊗t E₂) ∷ Es) ≤ EP φ
           → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz E₁)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₁ es ∥ os) × MovedS fs fs′ (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁)
  efst-sim prog fs φ {E₁} {E₂} {Es} {es = es} eq s h Bf C fit = case top-pair es eq (c-env C) of λ where
      (wa , wb , pa , pb , sa , sb) →
        view-sim prog fs φ (ws Es) wa pa sa
          (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (ws Es) (wsz E₁)))
            (Data.Nat.Properties.+-monoˡ-≤ (ws Es) (m≤m+n (wsz E₁) (wsz E₂))))
          s h Bf C fit
    where import Data.Nat.Properties

  -- ★ `esnd`
  esnd-sim : ∀ prog (fs : FlatState) (φ : Frame) {E₁ E₂ Es S} {es : Slots ((E₁ ⊗t E₂) ∷ Es)} {os : Stk S}
               {e₁ : MV E₁} {e₂ : MV E₂}
           → see es ≡ mpair e₁ e₂
           → Seg prog (fpc fs) (mvSS (ws Es + wsz E₁) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₂))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
           → ws (E₂ ∷ (E₁ ⊗t E₂) ∷ Es) ≤ EP φ
           → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz E₂)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw e₂ es ∥ os)
               × MovedS fs fs′ (ws Es + wsz E₁) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₂)
  esnd-sim prog fs φ {E₁} {E₂} {Es} {es = es} eq s h Bf C fit = case top-pair es eq (c-env C) of λ where
      (wa , wb , pa , pb , sa , sb) →
        view-sim prog fs φ (ws Es + wsz E₁) wb pb
          (subst (λ z → SlotsAt (slot fs) z wb) (trans (cong (_+ ws Es) (vw-len pa)) (+-comm (wsz E₁) (ws Es))) sb)
          (≤-trans (Data.Nat.Properties.≤-reflexive (+-assoc (ws Es) (wsz E₁) (wsz E₂)))
            (Data.Nat.Properties.≤-reflexive (+-comm (ws Es) (wsz E₁ + wsz E₂))))
          s h Bf C fit
    where import Data.Nat.Properties

  -- ★ `eapp`: a tagged closure's view is its environment's words
  eapp-sim : ∀ prog (fs : FlatState) (φ : Frame) {l X Es S} {es : Slots (Ct l X ∷ Es)} {os : Stk S} {x : MV X}
           → see es ≡ mct x
           → Seg prog (fpc fs) (mvSS (ws Es) (ws Es + wsz X) (wsz X))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
           → ws (X ∷ Ct l X ∷ Es) ≤ EP φ
           → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz X)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw x es ∥ os) × MovedS fs fs′ (ws Es) (ws Es + wsz X) (wsz X)
  eapp-sim prog fs φ {l} {X} {Es} {es = es} {x = x} eq s h Bf C fit = case topW es (c-env C) of λ where
      (w , pw , sw) → case subst (λ z → VW (heapMem (floc fs)) z w) eq pw of λ where
        (vct px) → view-sim prog fs φ (ws Es) w px sw (Data.Nat.Properties.≤-reflexive (+-comm (ws Es) (wsz X))) s h Bf C fit
    where import Data.Nat.Properties


  ----------------------------------------------------------------------
  -- 6. ★ FROM A VIEW TO THE STACK.
  ----------------------------------------------------------------------

  private
    -- the stack's new top, just below it
    new-top : ∀ B a s → (B ∸ s) ∸ a ≡ B ∸ (a + s)
    new-top B a s = trans (Data.Nat.Properties.∸-+-assoc B s a) (cong (B ∸_) (+-comm s a))
      where import Data.Nat.Properties

    -- a move of one word clobbers nothing it reads later
    single : ∀ {k k′} → k < k′ → k′ < 1 → Data.Empty.⊥
    single {k′ = zero}  () _
    single {k′ = suc _} _  (s≤s ())

  -- ★ `eword`: the viewed word onto the stack (in place of a unit)
  eword-sim : ∀ prog (fs : FlatState) (φ : Frame) {b Es S} {es : Slots (Bt b ∷ Es)} {os : Stk S} {x : ⟦ b ⟧b}
            → see es ≡ mbase x
            → Seg prog (fpc fs) (mvSS (ws Es) ((budget φ ∸ ws S) ∸ 1) 1)
            → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mone ∷ˢ os)
            → ws (Bt b ∷ S) ≤ OP φ
            → Σ FlatState λ fs′ → FlatSteps prog (nsteps 1) fs fs′
                × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mbase x ∷ˢ os) × MovedS fs fs′ (ws Es) ((budget φ ∸ ws S) ∸ 1) 1
  eword-sim prog fs φ {b} {Es} {S} {es} {os} {x} eq s h B C fit = case topW es (c-env C) of λ where
      (w , pw , sw) → case subst (λ z → VW (heapMem (floc fs)) z w) eq pw of λ where
        vbase → fin sw (mvSS-run prog fs (ws Es) ((budget φ ∸ ws S) ∸ 1) 1 s h
                         (infr B (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (ws Es) 1)) (env-in φ (c-efit C))))
                         (infr B (top-in (budget φ) (ws S) 1 (≤-trans fit (m≤n+m (OP φ) (EP φ)))))
                         (λ k k< → slots-def {slot fs} {ws Es} w sw k k<)
                         (λ k k′ lt lt′ → Data.Empty.⊥-elim (single lt lt′)))
    where
      import Data.Nat.Properties
      dst = (budget φ ∸ ws S) ∸ 1
      fitB : 1 + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) 1) fitB
      dst< : dst < budget φ ∸ ws S
      dst< = subst (_< budget φ ∸ ws S) (sym (new-top (budget φ) 1 (ws S)))
               (Data.Nat.Properties.∸-monoʳ-< (Data.Nat.Properties.n<1+n (ws S)) fitB)
        where import Data.Nat.Properties
      -- the word lands below the stack…
      stk-ok : ∀ y → budget φ ∸ ws S ≤ y → ∀ k → k < 1 → ¬ y ≡ k + dst
      stk-ok y lo zero _ e = Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans dst< lo)
        where import Data.Nat.Properties
      stk-ok y lo (suc k) (s≤s ())
      -- …and above the environment
      env-ok : ∀ y → y < ws (Bt b ∷ Es) → ∀ k → k < 1 → ¬ y ≡ k + dst
      env-ok y y< zero _ e =
        Data.Nat.Properties.<-irrefl e
          (<-≤-trans y< (≤-trans (c-efit C)
            (subst (EP φ ≤_) (sym (new-top (budget φ) 1 (ws S))) (env-below φ (1 + ws S) fit))))
        where import Data.Nat.Properties
      env-ok y y< (suc k) (s≤s ())
      fin : SlotsAt (slot fs) (ws Es) (wordOf x ∷ [])
          → Σ FlatState (λ fs′ → FlatSteps prog (nsteps 1) fs fs′ × MovedS fs fs′ (ws Es) ((budget φ ∸ ws S) ∸ 1) 1)
          → Σ FlatState λ fs′ → FlatSteps prog (nsteps 1) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mbase x ∷ˢ os) × MovedS fs fs′ (ws Es) ((budget φ ∸ ws S) ∸ 1) 1
      fin sw (fs′ , st , M) =
        fs′ , st ,
        record { c-env  = envW-frame {heapMem (floc fs′)} es (λ y y< → m-rest M y (λ k k< e → env-ok y y< k k< e)) (envH (c-env C))
               ; c-stk  = ( wordOf x ∷ [] , vbase
                          , subst (λ z → SlotsAt (slot fs′) z (wordOf x ∷ [])) (new-top (budget φ) 1 (ws S))
                              (slots-moved (wordOf x ∷ []) M sw refl) )
                        , stkW-frame os fitS (λ y lo hi → m-rest M y (λ k k< e → stk-ok y lo k k< e)) (stkH (proj₂ (c-stk C)))
               ; c-efit = c-efit C ; c-sfit = fit }
        , M
        where
          envH : EnvW (heapMem (floc fs)) (slot fs) es → EnvW (heapMem (floc fs′)) (slot fs) es
          envH e = subst (λ r → EnvW r (slot fs) es) (sym (m-heap M)) e
          stkH : StkW (heapMem (floc fs)) (slot fs) φ os → StkW (heapMem (floc fs′)) (slot fs) φ os
          stkH e = subst (λ r → StkW r (slot fs) φ os) (sym (m-heap M)) e

  ----------------------------------------------------------------------
  -- 7. ★ LENDS: a value moved between the stack and a lend's buffer.
  ----------------------------------------------------------------------

  open FlatStepsAPI {FS} using (FlatSteps-++)
  open import Once.LinCore.Moves {FS} using (Seg-++ˡ; Seg-++ʳ)

  -- a move's trace has its steps' length
  len-mvSS : ∀ a b n → length (mvSS a b n) ≡ nsteps n
  len-mvSS a b zero    = refl
  len-mvSS a b (suc n) = cong (λ z → suc (suc z)) (len-mvSS (suc a) (suc b) n)

  -- a store below a read never clobbers it
  no-clash₂ : ∀ {a b k k′ n} → b + n ≤ a → k < n → ¬ k + b ≡ k′ + a
  no-clash₂ {a} {b} {k} {k′} {n} le lt eq =
    Data.Nat.Properties.<-irrefl eq
      (Data.Nat.Properties.<-≤-trans (+-monoˡ-< b lt)
        (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm n b)) (≤-trans le (m≤n+m a k′))))
    where import Data.Nat.Properties

  -- the stack's top pair, split into its components' words
  private
    stk-pair : ∀ {rd sm φ X A S} {x : MV X} {a : MV A} {os : Stk S} → ws ((X ⊗t A) ∷ S) ≤ budget φ
             → StkW rd sm φ (mpair x a ∷ˢ os)
             → Σ (List W) λ wx → Σ (List W) λ wa → VW rd x wx × VW rd a wa
               × SlotsAt sm (budget φ ∸ ws ((X ⊗t A) ∷ S)) wx × StkW rd sm φ (a ∷ˢ os)
    stk-pair {rd} {sm} {φ} {X} {A} {S} fit st =
      case unpair-W {rd} {sm} {φ} {X} {A} {S}
             (Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (sym (+-assoc (wsz X) (wsz A) (ws S)))) fit) st of λ where
        ((wx , px , sx) , (wa , pa , sa) , rest) →
          wx , wa , px , pa , subst (λ z → SlotsAt sm (budget φ ∸ z) wx) (sym (+-assoc (wsz X) (wsz A) (ws S))) sx , (wa , pa , sa) , rest
      where import Data.Nat.Properties

  -- a lend's buffer: the view's words, then the lent value's, above the environment
  private
    lend-words : ∀ e E X → (e + E) + (E + X) ≡ (E + X) + (E + e)
    lend-words = solve-∀
    lend-end : ∀ e E X → ((e + E) + E) + X ≡ (E + X) + (E + e)
    lend-end = solve-∀
    lend-buf : ∀ e E → E + (E + e) ≡ (e + E) + E
    lend-buf = solve-∀

  -- a write in the environment region misses the operand stack
  apart : ∀ φ {s p x} → s ≤ OP φ → p < EP φ → budget φ ∸ s ≤ x → ¬ x ≡ p
  apart φ {s} le p< lo e = Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans p< (≤-trans (env-below φ s le) lo))
    where import Data.Nat.Properties

  -- ★ `elend`: the view's words, then the lent value's (from the stack's top),
  -- into the lend's buffer above the environment
  elend-sim : ∀ prog (fs : FlatState) (φ : Frame) {E Es X A S} {es : Slots (E ∷ Es)} {os : Stk S} {x : MV X} {a : MV A}
            → Seg prog (fpc fs) (mvSS (ws Es) (ws Es + wsz E) (wsz E)
                                 ++ mvSS (budget φ ∸ ws ((X ⊗t A) ∷ S)) (ws Es + wsz E + wsz E) (wsz X))
            → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mpair x a ∷ˢ os)
            → ws ((E ⊗t X) ∷ E ∷ Es) ≤ EP φ
            → Σ FlatState λ fs₂ → FlatSteps prog (nsteps (wsz E) + nsteps (wsz X)) fs fs₂
                × CfgW (heapMem (floc fs₂)) (slot fs₂) φ (ln (see es) x es ∥ a ∷ˢ os) × Ran (nsteps (wsz E) + nsteps (wsz X)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₂
  elend-sim prog fs φ {E} {Es} {X} {A} {S} {es} {os} {x} {a} s h B C fit =
    case topW es (c-env C) of λ where
      (we , pe , se) → case stk-pair {heapMem (floc fs)} {slot fs} {φ} fitXA (c-stk C) of λ where
        (wx , wa , px , pa , sx , stA) →
          run₁ we pe se wx px sx stA
            (mvSS-run prog fs (ws Es) (ws Es + wsz E) (wsz E) (Seg-++ˡ prog (fpc fs) (mvSS (ws Es) (ws Es + wsz E) (wsz E)) _ s) h
               (infr B (≤-trans (m≤m+n (ws Es + wsz E) (wsz E + wsz X))
                           (≤-trans (Data.Nat.Properties.≤-reflexive (lend-words (ws Es) (wsz E) (wsz X))) (env-in φ fit))))
               (infr B (≤-trans (Data.Nat.Properties.+-monoʳ-≤ (ws Es + wsz E) (m≤m+n (wsz E) (wsz X)))
                           (≤-trans (Data.Nat.Properties.≤-reflexive (lend-words (ws Es) (wsz E) (wsz X))) (env-in φ fit))))
               (λ k k< → slots-def {slot fs} {ws Es} we se k (subst (k <_) (sym (vw-len pe)) k<))
               (λ k k′ _ lt → no-clash {k = k} ≤-refl lt))
    where
      import Data.Nat.Properties
      fitXA = ≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))
      t = budget φ ∸ ws ((X ⊗t A) ∷ S)
      Goal : Set
      Goal = Σ FlatState λ fs₂ → FlatSteps prog (nsteps (wsz E) + nsteps (wsz X)) fs fs₂
               × CfgW (heapMem (floc fs₂)) (slot fs₂) φ (ln (see es) x es ∥ a ∷ˢ os) × Ran (nsteps (wsz E) + nsteps (wsz X)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₂
      to-B : ws ((E ⊗t X) ∷ E ∷ Es) ≤ budget φ
      to-B = ≤-trans fit (m≤m+n (EP φ) (OP φ))
      b₁ : (ws Es + wsz E) + wsz E ≤ budget φ
      b₁ = ≤-trans (Data.Nat.Properties.+-monoʳ-≤ (ws Es + wsz E) (m≤m+n (wsz E) (wsz X)))
             (≤-trans (Data.Nat.Properties.≤-reflexive (lend-words (ws Es) (wsz E) (wsz X))) to-B)
      b₂ : (ws Es + wsz E + wsz E) + wsz X ≤ budget φ
      b₂ = ≤-trans (Data.Nat.Properties.≤-reflexive (+-assoc (ws Es + wsz E) (wsz E) (wsz X)))
             (≤-trans (Data.Nat.Properties.≤-reflexive (lend-words (ws Es) (wsz E) (wsz X))) to-B)
      fitAS : ws (A ∷ S) ≤ budget φ
      fitAS = ≤-trans (Data.Nat.Properties.+-monoˡ-≤ (ws S) (m≤n+m (wsz A) (wsz X)))
                (≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ)))
      lo′ : ∀ y → budget φ ∸ ws (A ∷ S) ≤ y → t ≤ y
      lo′ y lo = ≤-trans (∸-monoʳ-≤ (budget φ) (Data.Nat.Properties.+-monoˡ-≤ (ws S) (m≤n+m (wsz A) (wsz X)))) lo
      -- the second move's destination: inside the environment region
      in-env₂ : ∀ k → k < wsz X → k + (ws Es + wsz E + wsz E) < EP φ
      in-env₂ k k< = <-≤-trans (+-monoˡ-< (ws Es + wsz E + wsz E) k<)
                       (≤-trans (Data.Nat.Properties.≤-reflexive (trans (+-comm (wsz X) (ws Es + wsz E + wsz E))
                                                                        (lend-end (ws Es) (wsz E) (wsz X)))) fit)
      -- both moves write above the old environment
      above₁ : ∀ y → y < ws (E ∷ Es) → ∀ k → ¬ y ≡ k + (ws Es + wsz E)
      above₁ y y< k e = Data.Nat.Properties.<-irrefl e
                          (<-≤-trans y< (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (wsz E) (ws Es))) (m≤n+m (ws Es + wsz E) k)))
      above₂ : ∀ y → y < ws (E ∷ Es) → ∀ k → ¬ y ≡ k + (ws Es + wsz E + wsz E)
      above₂ y y< k e = Data.Nat.Properties.<-irrefl e
                          (<-≤-trans y< (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (wsz E) (ws Es)))
                                          (≤-trans (m≤m+n (ws Es + wsz E) (wsz E)) (m≤n+m (ws Es + wsz E + wsz E) k))))
      -- the first move: the view's words into the lend's buffer
      run₁ : ∀ we (pe : VW (heapMem (floc fs)) (see es) we) (se : SlotsAt (slot fs) (ws Es) we)
               wx (px : VW (heapMem (floc fs)) x wx) (sx : SlotsAt (slot fs) t wx)
               (stA : StkW (heapMem (floc fs)) (slot fs) φ (a ∷ˢ os))
           → Σ FlatState (λ fs₁ → FlatSteps prog (nsteps (wsz E)) fs fs₁ × MovedS fs fs₁ (ws Es) (ws Es + wsz E) (wsz E))
           → Goal
      run₁ we pe se wx px sx stA (fs₁ , st₁ , M₁) =
        run₂ (mvSS-run prog fs₁ t (ws Es + wsz E + wsz E) (wsz X) seg₂ (trans (m-halt M₁) h) ra₂ rb₂ def₂ nc₂)
        where
          B₁ : budget φ ≤ Fr fs₁
          B₁ = subst (budget φ ≤_) (sym (cong AllocState.frame-slots (MovedS.m-alloc M₁))) B
          ra₂ : InFr fs₁ t (wsz X)
          ra₂ = infr B₁ (≤-trans (Data.Nat.Properties.+-monoʳ-≤ t (m≤m+n (wsz X) (wsz A)))
                           (sub-in (budget φ) (wsz (X ⊗t A)) (ws S) (≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ)))))
          rb₂ : InFr fs₁ (ws Es + wsz E + wsz E) (wsz X)
          rb₂ = infr B₁ (≤-trans (Data.Nat.Properties.≤-reflexive (+-assoc (ws Es + wsz E) (wsz E) (wsz X)))
                           (≤-trans (Data.Nat.Properties.≤-reflexive (lend-words (ws Es) (wsz E) (wsz X))) (env-in φ fit)))
          seg₂ : Seg prog (fpc fs₁) (mvSS t (ws Es + wsz E + wsz E) (wsz X))
          seg₂ = subst (λ z → Seg prog z (mvSS t (ws Es + wsz E + wsz E) (wsz X)))
                   (trans (cong (fpc fs +_) (len-mvSS (ws Es) (ws Es + wsz E) (wsz E)))
                          (trans (+-comm (fpc fs) (nsteps (wsz E))) (sym (m-pc M₁))))
                   (Seg-++ʳ prog (fpc fs) (mvSS (ws Es) (ws Es + wsz E) (wsz E)) _ s)
          -- the stack's words stand through the first move
          kept₁ : ∀ y → t ≤ y → slot fs₁ y ≡ slot fs y
          kept₁ y lo = m-rest M₁ y (λ k k< e → apart φ (c-sfit C) (in-env₁ k k<) lo e)
            where
              in-env₁ : ∀ k → k < wsz E → k + (ws Es + wsz E) < EP φ
              in-env₁ k k< = <-≤-trans (+-monoˡ-< (ws Es + wsz E) k<)
                               (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (wsz E) (ws Es + wsz E)))
                                 (≤-trans (Data.Nat.Properties.+-monoʳ-≤ (ws Es + wsz E) (m≤m+n (wsz E) (wsz X)))
                                   (≤-trans (Data.Nat.Properties.≤-reflexive (lend-words (ws Es) (wsz E) (wsz X))) fit)))
          def₂ : ∀ k → k < wsz X → Σ W λ v → slot fs₁ (k + t) ≡ just v
          def₂ k k< = case slots-def {slot fs} {t} wx sx k (subst (k <_) (sym (vw-len px)) k<) of λ where
            (v , ev) → v , trans (kept₁ (k + t) (m≤n+m t k)) ev
          nc₂ : ∀ k k′ → k < k′ → k′ < wsz X → ¬ k + (ws Es + wsz E + wsz E) ≡ k′ + t
          nc₂ k k′ lt lt′ = no-clash₂ {k = k} {k′ = k′}
                              (≤-trans (Data.Nat.Properties.≤-reflexive (lend-end (ws Es) (wsz E) (wsz X)))
                                (≤-trans fit (env-below φ (ws ((X ⊗t A) ∷ S)) (c-sfit C))))
                              (Data.Nat.Properties.<-trans lt lt′)
          -- the second move: the lent value's words after them
          run₂ : Σ FlatState (λ fs₂ → FlatSteps prog (nsteps (wsz X)) fs₁ fs₂ × MovedS fs₁ fs₂ t (ws Es + wsz E + wsz E) (wsz X))
               → Goal
          run₂ (fs₂ , st₂ , M₂) =
            fs₂ , FlatSteps-++ st₁ st₂ ,
            record { c-env  = ( we ++ wx , vpair (heap₂ pe) (heap₂ px) , slots-join {slot fs₂} we wx sa sb )
                            , envH (envW-frame es (λ y y< → m-rest M₂ y (λ k _ e → above₂ y y< k e))
                                     (envW-frame es (λ y y< → m-rest M₁ y (λ k _ e → above₁ y y< k e)) (c-env C)))
                   ; c-stk  = stkH (stkW-frame (a ∷ˢ os) fitAS
                                     (λ y lo _ → trans (m-rest M₂ y (λ k k< e → apart φ (c-sfit C) (in-env₂ k k<) (lo′ y lo) e))
                                                       (kept₁ y (lo′ y lo))) stA)
                   ; c-efit = fit
                   ; c-sfit = ≤-trans (Data.Nat.Properties.+-monoˡ-≤ (ws S) (m≤n+m (wsz A) (wsz X))) (c-sfit C) }
            , ran-trans (ranS M₁ b₁) (ranS M₂ b₂)
            where
              heap₂ : ∀ {B} {v : MV B} {w′} → VW (heapMem (floc fs)) v w′ → VW (heapMem (floc fs₂)) v w′
              heap₂ p = subst (λ r → VW r _ _) (sym (trans (m-heap M₂) (m-heap M₁))) p
              envH : EnvW (heapMem (floc fs)) (slot fs₂) es → EnvW (heapMem (floc fs₂)) (slot fs₂) es
              envH e = subst (λ r → EnvW r (slot fs₂) es) (sym (trans (m-heap M₂) (m-heap M₁))) e
              stkH : StkW (heapMem (floc fs)) (slot fs₂) φ (a ∷ˢ os) → StkW (heapMem (floc fs₂)) (slot fs₂) φ (a ∷ˢ os)
              stkH e = subst (λ r → StkW r (slot fs₂) φ (a ∷ˢ os)) (sym (trans (m-heap M₂) (m-heap M₁))) e
              -- the view's words, moved, and kept by the second move
              sa : SlotsAt (slot fs₂) (ws (E ∷ Es)) we
              sa = subst (λ z → SlotsAt (slot fs₂) z we) (+-comm (ws Es) (wsz E))
                     (slots-frame {slot fs₁} {slot fs₂} we
                       (λ k k< → m-rest M₂ (k + (ws Es + wsz E)) (λ k′ _ e → kept-a k k< k′ e))
                       (slots-moved we M₁ se (vw-len pe)))
                where
                  kept-a : ∀ k → k < length we → ∀ k′ → ¬ k + (ws Es + wsz E) ≡ k′ + (ws Es + wsz E + wsz E)
                  kept-a k k< k′ e = Data.Nat.Properties.<-irrefl e
                                       (<-≤-trans (+-monoˡ-< (ws Es + wsz E) (subst (k <_) (vw-len pe) k<))
                                         (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (wsz E) (ws Es + wsz E)))
                                           (m≤n+m (ws Es + wsz E + wsz E) k′)))
              -- the lent value's words, moved
              sb : SlotsAt (slot fs₂) (length we + ws (E ∷ Es)) wx
              sb = subst (λ z → SlotsAt (slot fs₂) z wx) (sym (trans (cong (_+ ws (E ∷ Es)) (vw-len pe)) (lend-buf (ws Es) (wsz E))))
                     (slots-moved wx M₂ (slots-frame {slot fs} {slot fs₁} wx (λ k _ → kept₁ (k + t) (m≤n+m t k)) sx) (vw-len px))

  -- ★ `eunlend`: the lent value's words, from the lend's buffer back onto the
  -- stack below the body's result: the pair again
  eunlend-sim : ∀ prog (fs : FlatState) (φ : Frame) {E Es X B S} {e : MV E} {x : MV X} {es : Slots (E ∷ Es)}
                  {w : MV B} {os : Stk S}
              → Seg prog (fpc fs) (mvSS (ws Es + wsz E + wsz E) ((budget φ ∸ ws (B ∷ S)) ∸ wsz X) (wsz X))
              → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
              → CfgW (heapMem (floc fs)) (slot fs) φ (ln e x es ∥ w ∷ˢ os)
              → ws ((X ⊗t B) ∷ S) ≤ OP φ
              → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz X)) fs fs′
                  × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mpair x w ∷ˢ os) × Ran (nsteps (wsz X)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  eunlend-sim prog fs φ {E} {Es} {X} {B} {S} {e} {x} {es} {w} {os} s h Bf C fitN =
    case c-env C of λ where
      ((wp , pp , sp) , ev) → case c-stk C of λ where
        ((wb , pb , sb) , rest) → case vpair-inv pp of λ where
          (we , wx , refl , pe , px) → case slots-++ {slot fs} we wx sp of λ where
            (_ , sx) → unlend-move we wx pe px sx wb pb sb ev rest
    where
      import Data.Nat.Properties
      src = ws Es + wsz E + wsz E
      dst = (budget φ ∸ ws (B ∷ S)) ∸ wsz X
      dst≡ : dst ≡ budget φ ∸ ws ((X ⊗t B) ∷ S)
      dst≡ = trans (new-top (budget φ) (wsz X) (ws (B ∷ S))) (cong (budget φ ∸_) (sym (+-assoc (wsz X) (wsz B) (ws S))))
      fitXB : wsz X + ws (B ∷ S) ≤ budget φ
      fitXB = ≤-trans (Data.Nat.Properties.≤-reflexive (sym (+-assoc (wsz X) (wsz B) (ws S)))) (≤-trans fitN (m≤n+m (OP φ) (EP φ)))
      ra : InFr fs src (wsz X)
      ra = infr Bf (≤-trans (Data.Nat.Properties.≤-reflexive (lend-end (ws Es) (wsz E) (wsz X)))
                       (≤-trans (c-efit C)
                         (≤-trans (subst (EP φ ≤_) (sym dst≡) (env-below φ (ws ((X ⊗t B) ∷ S)) fitN))
                           (≤-trans (Data.Nat.Properties.m∸n≤m _ (wsz X)) (Data.Nat.Properties.m∸n≤m (budget φ) (ws (B ∷ S)))))))
      rb : InFr fs dst (wsz X)
      rb = infr Bf (top-in (budget φ) (ws (B ∷ S)) (wsz X) fitXB)
      nc : ∀ k k′ → k < k′ → k′ < wsz X → ¬ k + dst ≡ k′ + src
      nc k k′ _ lt = no-clash {k = k}
                       (≤-trans (Data.Nat.Properties.≤-reflexive (lend-end (ws Es) (wsz E) (wsz X)))
                         (≤-trans (c-efit C)
                           (subst (EP φ ≤_) (sym dst≡) (env-below φ (ws ((X ⊗t B) ∷ S)) fitN))))
                       lt
      wX≤ : wsz X ≤ budget φ ∸ ws (B ∷ S)
      wX≤ = Data.Nat.Properties.m+n≤o⇒m≤o∸n (wsz X)
              (≤-trans (Data.Nat.Properties.≤-reflexive (sym (+-assoc (wsz X) (wsz B) (ws S)))) (≤-trans fitN (m≤n+m (OP φ) (EP φ))))
      bnd : dst + wsz X ≤ budget φ
      bnd = ≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.m∸n+n≡m wX≤)) (Data.Nat.Properties.m∸n≤m (budget φ) (ws (B ∷ S)))
      fitB : ws ((X ⊗t B) ∷ S) ≤ budget φ
      fitB = ≤-trans fitN (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) (wsz (X ⊗t B))) fitB
      -- the moved words lie in the stack region, from `dst`
      lo-d : ∀ k → budget φ ∸ ws ((X ⊗t B) ∷ S) ≤ k + dst
      lo-d k = ≤-trans (Data.Nat.Properties.≤-reflexive (sym dst≡)) (m≤n+m dst k)
      y<EP : ∀ y → y < ws (E ∷ Es) → y < EP φ
      y<EP y y< = <-≤-trans y< (≤-trans (m≤n+m (ws (E ∷ Es)) (wsz (E ⊗t X))) (c-efit C))
      Goal : Set
      Goal = Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz X)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mpair x w ∷ˢ os) × Ran (nsteps (wsz X)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
      -- the lent value's words, from the buffer onto the stack
      unlend-move : ∀ we wx (pe : VW (heapMem (floc fs)) e we) (px : VW (heapMem (floc fs)) x wx)
               (sx : SlotsAt (slot fs) (length we + ws (E ∷ Es)) wx)
               wb (pb : VW (heapMem (floc fs)) w wb) (sb : SlotsAt (slot fs) (budget φ ∸ ws (B ∷ S)) wb)
               (ev : EnvW (heapMem (floc fs)) (slot fs) es) (rest : StkW (heapMem (floc fs)) (slot fs) φ os)
           → Goal
      unlend-move we wx pe px sx wb pb sb ev rest = fin (mvSS-run prog fs src dst (wsz X) s h ra rb def nc)
        where
          sx′ : SlotsAt (slot fs) src wx
          sx′ = subst (λ z → SlotsAt (slot fs) z wx) (trans (cong (_+ ws (E ∷ Es)) (vw-len pe)) (lend-buf (ws Es) (wsz E))) sx
          def : ∀ k → k < wsz X → Σ W λ v → slot fs (k + src) ≡ just v
          def k k< = slots-def {slot fs} {src} wx sx′ k (subst (k <_) (sym (vw-len px)) k<)
          -- the result's words start right after the moved ones
          bot≡ : length wx + dst ≡ budget φ ∸ ws (B ∷ S)
          bot≡ = trans (cong (_+ dst) (vw-len px))
                   (trans (cong (wsz X +_) (trans dst≡ (cong (budget φ ∸_) (+-assoc (wsz X) (wsz B) (ws S)))))
                     (pair-at (budget φ) (wsz X) (wsz B) (ws S) (≤-trans (Data.Nat.Properties.≤-reflexive (sym (+-assoc (wsz X) (wsz B) (ws S)))) fitB)))
          -- …below the result's words and the rest of the stack
          d<b : ∀ k → k < wsz X → k + dst < budget φ ∸ ws (B ∷ S)
          d<b k k< = <-≤-trans (+-monoˡ-< dst k<) (Data.Nat.Properties.≤-reflexive (trans (cong (_+ dst) refl) (subst (λ z → z + dst ≡ _) refl (trans (cong (_+ dst) (sym (vw-len px))) bot≡))))
          below-b : ∀ k k′ → k′ < wsz X → ¬ k + (budget φ ∸ ws (B ∷ S)) ≡ k′ + dst
          below-b k k′ k′< e′ = Data.Nat.Properties.<-irrefl (sym e′) (<-≤-trans (d<b k′ k′<) (m≤n+m _ k))
          below-os : ∀ y → budget φ ∸ ws S ≤ y → ∀ k → k < wsz X → ¬ y ≡ k + dst
          below-os y lo k k< e′ = Data.Nat.Properties.<-irrefl (sym e′)
                                    (<-≤-trans (d<b k k<) (≤-trans (∸-monoʳ-≤ (budget φ) (m≤n+m (ws S) (wsz B))) lo))
          fin : Σ FlatState (λ fs′ → FlatSteps prog (nsteps (wsz X)) fs fs′ × MovedS fs fs′ src dst (wsz X)) → Goal
          fin (fs′ , st , M) =
            fs′ , st ,
            record { c-env  = envH (envW-frame es (λ y y< → m-rest M y (λ k k< e′ → apart φ fitN (y<EP y y<) (lo-d k) (sym e′))) ev)
                   ; c-stk  = ( wx ++ wb , vpair (heap px) (heap pb)
                              , subst (λ z → SlotsAt (slot fs′) z (wx ++ wb)) dst≡
                                  (slots-join {slot fs′} wx wb (slots-moved wx M sx′ (vw-len px))
                                     (subst (λ z → SlotsAt (slot fs′) z wb) (sym bot≡)
                                       (slots-frame {slot fs} {slot fs′} wb (λ k k< → m-rest M (k + (budget φ ∸ ws (B ∷ S))) (λ k′ k′< e′ → below-b k k′ k′< e′)) sb))) )
                            , stkH (stkW-frame os fitS (λ y lo _ → m-rest M y (λ k k< e′ → below-os y lo k k< e′)) rest)
                   ; c-efit = ≤-trans (m≤n+m (ws (E ∷ Es)) (wsz (E ⊗t X))) (c-efit C)
                   ; c-sfit = fitN }
            , ranS M bnd
            where
              heap : ∀ {A′} {v : MV A′} {w′} → VW (heapMem (floc fs)) v w′ → VW (heapMem (floc fs′)) v w′
              heap p = subst (λ r → VW r _ _) (sym (m-heap M)) p
              envH : EnvW (heapMem (floc fs)) (slot fs′) es → EnvW (heapMem (floc fs′)) (slot fs′) es
              envH e′ = subst (λ r → EnvW r (slot fs′) es) (sym (m-heap M)) e′
              stkH : StkW (heapMem (floc fs)) (slot fs′) φ os → StkW (heapMem (floc fs′)) (slot fs′) φ os
              stkH e′ = subst (λ r → StkW r (slot fs′) φ os) (sym (m-heap M)) e′

  ----------------------------------------------------------------------
  -- 8. ★ A SUM BUILT: the payload moved down, the tag, the padding.
  ----------------------------------------------------------------------

  open import Once.LinCore.Moves {FS} using (tag-step; store-step; stores-run; Filled; module Filled)
  open Filled using (f-pc; f-heap; f-halt; f-regs; f-set; f-rest)
  open import Once.LinCore.MoveCode using (stores)
  open import Data.List using (replicate)
  open import Data.List.Properties using (length-replicate)
  open import Data.Nat using (_⊔_)
  open import Once.CCC.Machine.SMCore using (SV-Tag; store-at-slot; instr-load-tag-lit; readReg; writeReg; Output; module MemOps)
  open FlatStepsAPI {FS} using (step-at; _∷_; [])

  -- a move down never clobbers a word it reads later
  no-clash-down : ∀ {a b k k′} → b ≤ a → k < k′ → ¬ k + b ≡ k′ + a
  no-clash-down {a} {b} {k} {k′} le lt eq =
    Data.Nat.Properties.<-irrefl eq (Data.Nat.Properties.<-≤-trans (+-monoˡ-< b lt) (Data.Nat.Properties.+-monoʳ-≤ k′ le))
    where import Data.Nat.Properties

  private
    suc-∸ : ∀ m n → n < m → suc (m ∸ suc n) ≡ m ∸ n
    suc-∸ (suc m) zero    _        = refl
    suc-∸ (suc m) (suc n) (s≤s lt) = suc-∸ m n lt

    pad-at : ∀ p M bot → p ≤ M → M ≤ bot → p + (bot ∸ M) ≡ bot ∸ (M ∸ p)
    pad-at p M bot pM Mb =
      sym (trans (cong (_∸ (M ∸ p)) (sym eq))
             (trans (Data.Nat.Properties.m+n∸n≡m ((bot ∸ M) + p) (M ∸ p)) (+-comm (bot ∸ M) p)))
      where
        import Data.Nat.Properties
        -- bot = (bot ∸ M) + p + (M ∸ p)
        eq : ((bot ∸ M) + p) + (M ∸ p) ≡ bot
        eq = trans (+-assoc (bot ∸ M) p (M ∸ p))
               (trans (cong ((bot ∸ M) +_) (Data.Nat.Properties.m+[n∸m]≡n pM)) (m∸n+n≡m Mb))

  -- a run of one word
  slots-replicate : ∀ {sm : ℕ → Maybe W} {b} n (v : W) → (∀ k → k < n → sm (k + b) ≡ just v) → SlotsAt sm b (replicate n v)
  slots-replicate zero    v h = tt
  slots-replicate {sm} {b} (suc n) v h =
    h 0 (s≤s z≤n) , slots-replicate {sm} {suc b} n v (λ k k< → trans (cong sm (+-suc k b)) (h (suc k) (s≤s k<)))

  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Once.LinCore.Moves {FS} using (store-same; store-other)
  open FlatMachine {FS} using (fetch)

  -- ★ a sum's words built on the stack: the payload moved down to just past
  -- the tag's slot, the tag, the padding; nothing outside [tag, bot) moves
  inj-core : ∀ prog (fs : FlatState) (bot M wP t : ℕ) (w : List W)
           → wP ≤ M → M < bot → length w ≡ wP → SlotsAt (slot fs) (bot ∸ wP) w
           → Seg prog (fpc fs) (mvSS (bot ∸ wP) (bot ∸ M) wP
                                ++ instr-load-tag-lit t ∷ store-at-slot (bot ∸ suc M) ∷ stores (bot ∸ (M ∸ wP)) (M ∸ wP))
           → fhalted (floc fs) ≡ false → bot ≤ Fr fs
           → Σ FlatState λ fs₄ → FlatSteps prog (nsteps wP + suc (suc (M ∸ wP))) fs fs₄
               × SlotsAt (slot fs₄) (bot ∸ suc M) (SV-Tag t ∷ w ++ replicate (M ∸ wP) (SV-Tag t))
               × (∀ x → (x < bot ∸ suc M) ⊎ (bot ≤ x) → slot fs₄ x ≡ slot fs x)
               × heapMem (floc fs₄) ≡ heapMem (floc fs) × Ran (nsteps wP + suc (suc (M ∸ wP))) 0 (AllocState.next-heap-ref (falloc fs)) bot fs fs₄
  inj-core prog fs bot M wP t w pM Mb lw sw s h Bb =
    run₁ (mvSS-run prog fs (bot ∸ wP) (bot ∸ M) wP (Seg-++ˡ prog (fpc fs) (mvSS (bot ∸ wP) (bot ∸ M) wP) _ s) h
           (infr Bb (Data.Nat.Properties.≤-reflexive (m∸n+n≡m (≤-trans pM (Data.Nat.Properties.<⇒≤ Mb)))))
           (infr Bb (≤-trans (Data.Nat.Properties.+-monoʳ-≤ (bot ∸ M) pM)
                       (Data.Nat.Properties.≤-reflexive (m∸n+n≡m (Data.Nat.Properties.<⇒≤ Mb)))))
           (λ k k< → slots-def {slot fs} {bot ∸ wP} w sw k (subst (k <_) (sym lw) k<))
           (λ k k′ lt _ → no-clash-down (∸-monoʳ-≤ bot pM) lt))
    where
      import Data.Nat.Properties
      tp = bot ∸ suc M
      M≤ : M ≤ bot
      M≤ = Data.Nat.Properties.<⇒≤ Mb
      bS : (bot ∸ M) + wP ≤ bot
      bS = ≤-trans (Data.Nat.Properties.+-monoʳ-≤ (bot ∸ M) pM) (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.m∸n+n≡m M≤))
      tp< : tp < bot
      tp< = Data.Nat.Properties.≤-<-trans (Data.Nat.Properties.∸-monoʳ-≤ bot (s≤s z≤n)) (pred< (≤-trans (s≤s z≤n) Mb))
      bF : (bot ∸ (M ∸ wP)) + (M ∸ wP) ≤ bot
      bF = Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.m∸n+n≡m (≤-trans (Data.Nat.Properties.m∸n≤m M wP) M≤))
      dst = bot ∸ M
      pp = bot ∸ (M ∸ wP)
      rest = Seg-++ʳ prog (fpc fs) (mvSS (bot ∸ wP) (bot ∸ M) wP) _ s
      pad = replicate (M ∸ wP) (SV-Tag t)
      -- where things are
      tp<dst : tp < dst
      tp<dst = Data.Nat.Properties.≤-reflexive (suc-∸ bot M Mb)
      pp≡ : wP + dst ≡ pp
      pp≡ = pad-at wP M bot pM (Data.Nat.Properties.<⇒≤ Mb)
      ppEnd : (M ∸ wP) + pp ≡ bot
      ppEnd = trans (cong ((M ∸ wP) +_) (sym pp≡))
                (trans (sym (+-assoc (M ∸ wP) wP dst))
                  (trans (cong (_+ dst) (trans (+-comm (M ∸ wP) wP) (Data.Nat.Properties.m+[n∸m]≡n pM)))
                    (trans (+-comm M dst) (m∸n+n≡m (Data.Nat.Properties.<⇒≤ Mb)))))
      in-pay : ∀ k → k < wP → k + dst < pp
      in-pay k k< = <-≤-trans (+-monoˡ-< dst k<) (Data.Nat.Properties.≤-reflexive pp≡)
      in-pad : ∀ k → k < M ∸ wP → k + pp < bot
      in-pad k k< = <-≤-trans (+-monoˡ-< pp k<) (Data.Nat.Properties.≤-reflexive ppEnd)
      tp<pp : tp < pp
      tp<pp = <-≤-trans tp<dst (≤-trans (m≤n+m dst wP) (Data.Nat.Properties.≤-reflexive pp≡))
      pp≤bot : pp ≤ bot
      pp≤bot = ≤-trans (m≤n+m pp (M ∸ wP)) (Data.Nat.Properties.≤-reflexive ppEnd)
      Goal : Set
      Goal = Σ FlatState λ fs₄ → FlatSteps prog (nsteps wP + suc (suc (M ∸ wP))) fs fs₄
               × SlotsAt (slot fs₄) (bot ∸ suc M) (SV-Tag t ∷ w ++ replicate (M ∸ wP) (SV-Tag t))
               × (∀ x → (x < bot ∸ suc M) ⊎ (bot ≤ x) → slot fs₄ x ≡ slot fs x)
               × heapMem (floc fs₄) ≡ heapMem (floc fs) × Ran (nsteps wP + suc (suc (M ∸ wP))) 0 (AllocState.next-heap-ref (falloc fs)) bot fs fs₄
      -- the payload moved down
      run₁ : Σ FlatState (λ fs₁ → FlatSteps prog (nsteps wP) fs fs₁ × MovedS fs fs₁ (bot ∸ wP) (bot ∸ M) wP) → Goal
      run₁ (fs₁ , st₁ , M₁) =
        run₂ (stores-run prog fs₃ pp (M ∸ wP) seg₄ h₁ (infr Bb₁ (Data.Nat.Properties.≤-reflexive
                                                       (m∸n+n≡m (≤-trans (Data.Nat.Properties.m∸n≤m M wP) M≤)))))
        where
          cf = AllocState.current-frame (falloc fs₁)
          fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Output (SV-Tag t) } ; fpc = suc (fpc fs₁) }
          fs₃ = record fs₂ { floc = MemOps.writeLoc {FS} (floc fs₂) (AtStack (AllocState.current-frame (falloc fs₂)) tp)
                                      (readReg (LocState.regs (floc fs₂)) Output) ; fpc = suc (fpc fs₂) }
          h₁ : fhalted (floc fs₁) ≡ false
          h₁ = trans (m-halt M₁) h
          Bb₁ : bot ≤ Fr fs₁
          Bb₁ = subst (bot ≤_) (sym (cong AllocState.frame-slots (MovedS.m-alloc M₁))) Bb
          pcEq : fpc fs + length (mvSS (bot ∸ wP) (bot ∸ M) wP) ≡ fpc fs₁
          pcEq = trans (cong (fpc fs +_) (len-mvSS (bot ∸ wP) (bot ∸ M) wP)) (trans (+-comm (fpc fs) (nsteps wP)) (sym (m-pc M₁)))
          seg₄ : Seg prog (fpc fs₃) (stores pp (M ∸ wP))
          seg₄ = subst (λ z → Seg prog (suc (suc z)) (stores pp (M ∸ wP))) pcEq (proj₂ (proj₂ rest))
          ftag : fetch prog (fpc fs₁) ≡ just (instr-load-tag-lit t)
          ftag = subst (λ z → fetch prog z ≡ just (instr-load-tag-lit t)) pcEq (proj₁ rest)
          fstore : fetch prog (fpc fs₂) ≡ just (store-at-slot tp)
          fstore = subst (λ z → fetch prog (suc z) ≡ just (store-at-slot tp)) pcEq (proj₁ (proj₂ rest))
          -- the tag, then the padding
          run₂ : Σ FlatState (λ fs₄ → FlatSteps prog (M ∸ wP) fs₃ fs₄ × Filled fs₃ fs₄ pp (M ∸ wP)) → Goal
          run₂ (fs₄ , st₄ , F) =
            fs₄ ,
            FlatSteps-++ st₁ (step-at fs₂ (h₁ , ftag) (tag-step fs₁ t) (step-at fs₃ (h₁ , fstore) (store-step fs₂ tp (<-≤-trans tp< Bb₁)) st₄)) ,
            (tagEq , subst (λ z → SlotsAt (slot fs₄) z (w ++ pad)) (sym (suc-∸ bot M Mb))
                       (slots-join {slot fs₄} w pad payload padS)) ,
            outside ,
            trans (f-heap F) (m-heap M₁) ,
            ran-trans (ranS M₁ bS) (ran-trans (ran-regs _) (ran-trans (ran-store fs₂ tp (readReg (LocState.regs (floc fs₂)) Output) tp<) (ranF F bF)))
            where
              -- the tag
              tagEq : slot fs₄ tp ≡ just (SV-Tag t)
              tagEq = trans (f-rest F tp (λ k _ e → Data.Nat.Properties.<-irrefl e (<-≤-trans tp<pp (m≤n+m pp k))))
                            (store-same (floc fs₂) cf tp (SV-Tag t))
              -- the payload, moved, kept by the tag's store and the padding
              payload : SlotsAt (slot fs₄) dst w
              payload =
                slots-frame {slot fs₃} {slot fs₄} w
                  (λ k k< → f-rest F (k + dst) (λ k′ _ e → Data.Nat.Properties.<-irrefl e
                                                             (<-≤-trans (in-pay k (subst (k <_) lw k<)) (m≤n+m pp k′))))
                  (slots-frame {slot fs₁} {slot fs₃} w
                     (λ k k< → store-other (floc fs₂) cf tp (SV-Tag t) (k + dst)
                                 (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans tp<dst (m≤n+m dst k))))
                     (slots-moved w M₁ sw lw))
              -- the padding
              padS : SlotsAt (slot fs₄) (length w + dst) pad
              padS = subst (λ z → SlotsAt (slot fs₄) z pad) (sym (trans (cong (_+ dst) lw) pp≡))
                       (slots-replicate {slot fs₄} {pp} (M ∸ wP) (SV-Tag t) (λ k k< → f-set F k k<))
              -- nothing outside [tag, bot) moves
              outside : ∀ x → (x < tp) ⊎ (bot ≤ x) → slot fs₄ x ≡ slot fs x
              outside x (inj₁ x<tp) =
                trans (f-rest F x (λ k k< e → Data.Nat.Properties.<-irrefl e
                                                (Data.Nat.Properties.<-trans x<tp (<-≤-trans tp<pp (m≤n+m pp k)))))
                  (trans (store-other (floc fs₂) cf tp (SV-Tag t) x (λ e → Data.Nat.Properties.<-irrefl (sym e) x<tp))
                    (m-rest M₁ x (λ k k< e → Data.Nat.Properties.<-irrefl e
                                                (Data.Nat.Properties.<-trans x<tp (<-≤-trans tp<dst (m≤n+m dst k))))))
              outside x (inj₂ bx) =
                trans (f-rest F x (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (in-pad k k<) bx)))
                  (trans (store-other (floc fs₂) cf tp (SV-Tag t) x
                            (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans (<-≤-trans tp<pp pp≤bot) bx)))
                    (m-rest M₁ x (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (in-pay k k<) (≤-trans pp≤bot bx)))))

  -- ★ `linl`, `linr`: the sum's words on the stack, the rest as it was
  private
    inj-W : ∀ {rd A B S} (φ : Frame) {os : Stk S} (fs fs₄ : FlatState) t (P : LTy) (w : List W)
          → let bot = budget φ ∸ ws S ; M = wsz A ⊔ wsz B in
            P ≡ A ⊎ P ≡ B → wsz P ≤ M → suc M + ws S ≤ budget φ
          → SlotsAt (slot fs₄) (bot ∸ suc M) (SV-Tag t ∷ w ++ replicate (M ∸ wsz P) (SV-Tag t))
          → (∀ x → (x < bot ∸ suc M) ⊎ (bot ≤ x) → slot fs₄ x ≡ slot fs x)
          → StkW rd (slot fs) φ os → ws S ≤ budget φ
          → SlotsAt (slot fs₄) (budget φ ∸ ws ((A ⊕t B) ∷ S)) (SV-Tag t ∷ w ++ replicate (M ∸ wsz P) (SV-Tag t))
            × StkW rd (slot fs₄) φ os
    inj-W {rd} {A} {B} {S} φ {os} fs fs₄ t P w _ pM fit sl out st fitS =
      subst (λ z → SlotsAt (slot fs₄) z (SV-Tag t ∷ w ++ replicate ((wsz A ⊔ wsz B) ∸ wsz P) (SV-Tag t))) (new-top (budget φ) (suc (wsz A ⊔ wsz B)) (ws S)) sl ,
      stkW-frame os fitS (λ x lo _ → out x (inj₂ lo)) st

  pad-len : ∀ (w : List W) P M t → length w ≡ wsz P → wsz P ≤ M → length (w ++ replicate (M ∸ wsz P) (SV-Tag t)) ≡ M
  pad-len w P M t lw pM =
    trans (length-++ w) (trans (cong₂ _+_ lw (length-replicate (M ∸ wsz P))) (Data.Nat.Properties.m+[n∸m]≡n pM))
    where import Data.Nat.Properties
          open import Data.List.Properties using (length-++)
          open Relation.Binary.PropositionalEquality using (cong₂)

  ≤∸ : ∀ m n o → m + n ≤ o → m ≤ o ∸ n
  ≤∸ m n o le = ≤-trans (Data.Nat.Properties.≤-reflexive (sym (Data.Nat.Properties.m+n∸n≡m m n))) (Data.Nat.Properties.∸-monoˡ-≤ n le)
    where import Data.Nat.Properties

  linl-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {a : MV A}
           → Seg prog (fpc fs) (mvSS ((budget φ ∸ ws S) ∸ wsz A) ((budget φ ∸ ws S) ∸ (wsz A ⊔ wsz B)) (wsz A)
                                ++ instr-load-tag-lit 0 ∷ store-at-slot ((budget φ ∸ ws S) ∸ suc (wsz A ⊔ wsz B))
                                ∷ stores ((budget φ ∸ ws S) ∸ ((wsz A ⊔ wsz B) ∸ wsz A)) ((wsz A ⊔ wsz B) ∸ wsz A))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ a ∷ˢ os)
           → ws ((A ⊕t B) ∷ S) ≤ OP φ
           → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz A) + suc (suc ((wsz A ⊔ wsz B) ∸ wsz A))) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ minl {B = B} a ∷ˢ os)
               × Ran (nsteps (wsz A) + suc (suc ((wsz A ⊔ wsz B) ∸ wsz A))) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  linl-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} s h Bf C fit = case c-stk C of λ where
      ((wa , pa , sa) , rest) →
        case inj-core prog fs (budget φ ∸ ws S) (wsz A ⊔ wsz B) (wsz A) 0 wa (Data.Nat.Properties.m≤m⊔n (wsz A) (wsz B)) M<bot (vw-len pa)
               (subst (λ z → SlotsAt (slot fs) z wa) (sym (new-top (budget φ) (wsz A) (ws S))) sa) s h
               (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)) Bf) of λ where
          (fs₄ , st , sl , out , hp , K) →
            let W₄ = inj-W {heapMem (floc fs)} {A} {B} {S} φ {os} fs fs₄ 0 A wa (inj₁ refl) (Data.Nat.Properties.m≤m⊔n (wsz A) (wsz B)) fitB
                       sl out rest (≤-trans (m≤n+m (ws S) (suc (wsz A ⊔ wsz B))) fitB) in
            fs₄ , st ,
            record { c-env  = subst (λ r → EnvW r (slot fs₄) es) (sym hp)
                                (envW-frame es (λ x x< → out x (inj₁ (env< x x<))) (c-env C))
                   ; c-stk  = ( SV-Tag 0 ∷ wa ++ replicate ((wsz A ⊔ wsz B) ∸ wsz A) (SV-Tag 0)
                              , subst (λ r → VW r _ _) (sym hp)
                                  (vinl pa (pad-len wa A (wsz A ⊔ wsz B) 0 (vw-len pa) (Data.Nat.Properties.m≤m⊔n (wsz A) (wsz B))))
                              , proj₁ W₄ )
                            , subst (λ r → StkW r (slot fs₄) φ os) (sym hp) (proj₂ W₄)
                   ; c-efit = c-efit C ; c-sfit = fit } , ran-hi (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)) K
    where
      import Data.Nat.Properties
      fitB : suc (wsz A ⊔ wsz B) + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      M<bot : wsz A ⊔ wsz B < budget φ ∸ ws S
      M<bot = ≤∸ (suc (wsz A ⊔ wsz B)) (ws S) (budget φ) fitB
      env< : ∀ x → x < ws Es → x < (budget φ ∸ ws S) ∸ suc (wsz A ⊔ wsz B)
      env< x x< = <-≤-trans x< (≤-trans (c-efit C)
                    (subst (EP φ ≤_) (sym (new-top (budget φ) (suc (wsz A ⊔ wsz B)) (ws S))) (env-below φ (ws ((A ⊕t B) ∷ S)) fit)))

  linr-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {b : MV B}
           → Seg prog (fpc fs) (mvSS ((budget φ ∸ ws S) ∸ wsz B) ((budget φ ∸ ws S) ∸ (wsz A ⊔ wsz B)) (wsz B)
                                ++ instr-load-tag-lit 1 ∷ store-at-slot ((budget φ ∸ ws S) ∸ suc (wsz A ⊔ wsz B))
                                ∷ stores ((budget φ ∸ ws S) ∸ ((wsz A ⊔ wsz B) ∸ wsz B)) ((wsz A ⊔ wsz B) ∸ wsz B))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ b ∷ˢ os)
           → ws ((A ⊕t B) ∷ S) ≤ OP φ
           → Σ FlatState λ fs′ → FlatSteps prog (nsteps (wsz B) + suc (suc ((wsz A ⊔ wsz B) ∸ wsz B))) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ minr {A = A} b ∷ˢ os)
               × Ran (nsteps (wsz B) + suc (suc ((wsz A ⊔ wsz B) ∸ wsz B))) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  linr-sim prog fs φ {Es} {A} {B} {S} {es} {os} {b} s h Bf C fit = case c-stk C of λ where
      ((wb , pb , sb) , rest) →
        case inj-core prog fs (budget φ ∸ ws S) (wsz A ⊔ wsz B) (wsz B) 1 wb (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) M<bot (vw-len pb)
               (subst (λ z → SlotsAt (slot fs) z wb) (sym (new-top (budget φ) (wsz B) (ws S))) sb) s h
               (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)) Bf) of λ where
          (fs₄ , st , sl , out , hp , K) →
            let W₄ = inj-W {heapMem (floc fs)} {A} {B} {S} φ {os} fs fs₄ 1 B wb (inj₂ refl) (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) fitB
                       sl out rest (≤-trans (m≤n+m (ws S) (suc (wsz A ⊔ wsz B))) fitB) in
            fs₄ , st ,
            record { c-env  = subst (λ r → EnvW r (slot fs₄) es) (sym hp)
                                (envW-frame es (λ x x< → out x (inj₁ (env< x x<))) (c-env C))
                   ; c-stk  = ( SV-Tag 1 ∷ wb ++ replicate ((wsz A ⊔ wsz B) ∸ wsz B) (SV-Tag 1)
                              , subst (λ r → VW r _ _) (sym hp)
                                  (vinr pb (pad-len wb B (wsz A ⊔ wsz B) 1 (vw-len pb) (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B))))
                              , proj₁ W₄ )
                            , subst (λ r → StkW r (slot fs₄) φ os) (sym hp) (proj₂ W₄)
                   ; c-efit = c-efit C ; c-sfit = fit } , ran-hi (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)) K
    where
      import Data.Nat.Properties
      fitB : suc (wsz A ⊔ wsz B) + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      M<bot : wsz A ⊔ wsz B < budget φ ∸ ws S
      M<bot = ≤∸ (suc (wsz A ⊔ wsz B)) (ws S) (budget φ) fitB
      env< : ∀ x → x < ws Es → x < (budget φ ∸ ws S) ∸ suc (wsz A ⊔ wsz B)
      env< x x< = <-≤-trans x< (≤-trans (c-efit C)
                    (subst (EP φ ≤_) (sym (new-top (budget φ) (suc (wsz A ⊔ wsz B)) (ws S))) (env-below φ (ws ((A ⊕t B) ∷ S)) fit)))

  ----------------------------------------------------------------------
  -- 9. ★ THE HEAP STEPS.
  ----------------------------------------------------------------------

  open import Once.LinCore.Moves {FS} using (mvPS-run; MovedP; restore-step; module MovedP) renaming (free-step to ffree-step)
  open MovedP using (p-pc; p-heap; p-in; p-moved; p-rest) renaming (p-halt to pm-halt)
  open import Once.LinCore.MoveCode using (mvPS)
  import Once.LinCore.MoveCode
  open import Once.CCC.Machine.Locations using (AtDynamic)
  open import Once.CCC.Machine.SMCore using (offsetLoc; restore-input; instr-free-heap; SV-Ptr; Input1; module ExecFinal)
  open import Once.Memory.HeapAddress using (heap-loc; mkHeapRef)

  -- a cell's words, moved by a pointer move from its first word
  cell-slots : ∀ {fs fs′ : FlatState} {i b n} (w : List W)
             → MovedP fs fs′ (AtDynamic (cellLoc i 0)) 0 b n
             → At (heapMem (floc fs)) i 0 w → length w ≡ n → SlotsAt (slot fs′) b w
  cell-slots {fs} {fs′} {i} {b} {n} w P a refl = go w 0 a (λ k k< → p-moved P k k<)
    where
      at′ : ∀ k → MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + 0)) ≡ heapMem (floc fs) (cellLoc i k)
      at′ k = cong (λ z → heapMem (floc fs) (heap-loc (mkHeapRef (serial i)) z))
                  (trans (Data.Nat.Properties.+-identityʳ (k + 0)) (Data.Nat.Properties.+-identityʳ k))
        where import Data.Nat.Properties
      go : ∀ (v : List W) j → At (heapMem (floc fs)) i j v
         → (∀ k → k < j + length v → slot fs′ (k + b) ≡ MemOps.readLoc {FS} (floc fs) (offsetLoc (AtDynamic (cellLoc i 0)) (k + 0)))
         → SlotsAt (slot fs′) (j + b) v
      go []      j a h = tt
      go (x ∷ v) j (e , a) h =
        trans (h j (subst (j <_) (sym (+-suc j (length v))) (s≤s (m≤m+n j (length v))))) (trans (at′ j) e) ,
        go v (suc j) a (λ k k< → h k (subst (k <_) (sym (+-suc j (length v))) k<))

  len-mvPS : ∀ o b n → length (mvPS o b n) ≡ nsteps n
  len-mvPS o b zero    = refl
  len-mvPS o b (suc n) = cong (λ z → suc (suc z)) (len-mvPS (suc o) (suc b) n)

  len-mvSP : ∀ a o n → length (Once.LinCore.MoveCode.mvSP a o n) ≡ nsteps n
  len-mvSP a o zero    = refl
  len-mvSP a o (suc n) = cong (λ z → suc (suc z)) (len-mvSP (suc a) (suc o) n)

  -- a cell's words are defined
  at-def : ∀ {rd i o} (w : List W) → At rd i o w → ∀ k → k < length w → Σ W λ x → rd (cellLoc i (k + o)) ≡ just x
  at-def (x ∷ w) (e , a) zero    _        = x , e
  at-def {rd} {i} {o} (x ∷ w) (e , a) (suc k) (s≤s k<) = case at-def {rd} {i} {suc o} w a k k< of λ where
    (y , ey) → y , trans (cong (λ z → rd (cellLoc i z)) (sym (+-suc k o))) ey

  -- ★ `lOutμ`: the node's layer, out of its cell onto the stack; the cell freed
  lOutμ-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es F S} {es : Slots Es} {os : Stk S} {i} {v : MV (LF∙ F (μt F))}
            → Seg prog (fpc fs) (restore-input ((budget φ ∸ ws S) ∸ 1)
                                 ∷ mvPS 0 ((budget φ ∸ ws S) ∸ wsz (LF∙ F (μt F))) (wsz (LF∙ F (μt F)))
                                 ++ instr-free-heap (1 ⊔ wsz (LF∙ F (μt F))) ∷ [])
            → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
            → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ mmu i v ∷ˢ os)
            → ws (LF∙ F (μt F) ∷ S) ≤ OP φ
            → Σ FlatState λ fs′ → FlatSteps prog (suc (nsteps (wsz (LF∙ F (μt F))) + 1)) fs fs′
                × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ v ∷ˢ os) × Ran (suc (nsteps (wsz (LF∙ F (μt F))) + 1)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  lOutμ-sim prog fs φ {Es} {F} {S} {es} {os} {i} {v} (f₀ , s) h Bf C fit = case c-stk C of λ where
      ((_ , vmu {wv = wv} pv ca , (ep , _)) , rest) → out-move wv pv ca ep rest
    where
      import Data.Nat.Properties
      wL = wsz (LF∙ F (μt F))
      bot = budget φ ∸ ws S
      dst = bot ∸ wL
      bP : dst + wL ≤ budget φ
      bP = ≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.m∸n+n≡m (Data.Nat.Properties.m+n≤o⇒m≤o∸n wL (≤-trans fit (m≤n+m (OP φ) (EP φ))))))
             (Data.Nat.Properties.m∸n≤m (budget φ) (ws S))
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 (cellPtr i) } ; fpc = suc (fpc fs) }
      fitB : wL + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) wL) fitB
      env< : ∀ x → x < ws Es → x < dst
      env< x x< = <-≤-trans x< (≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) wL (ws S))) (env-below φ (ws (LF∙ F (μt F) ∷ S)) fit)))
      in-stk : ∀ k → k < wL → k + dst < bot
      in-stk k k< = <-≤-trans (+-monoˡ-< dst k<)
                      (Data.Nat.Properties.≤-reflexive (trans (cong (wL +_) (new-top (budget φ) wL (ws S))) (pair-at (budget φ) wL 0 (ws S) fitB)))
      Goal : Set
      Goal = Σ FlatState λ fs′ → FlatSteps prog (suc (nsteps wL + 1)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ v ∷ˢ os) × Ran (suc (nsteps wL + 1)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
      -- the node's layer, moved out of its cell
      out-move : ∀ wv (pv : VW (heapMem (floc fs)) v wv) (ca : At (heapMem (floc fs)) i 0 wv)
                   (ep : slot fs (budget φ ∸ (1 + ws S)) ≡ just (cellPtr i))
                   (rest : StkW (heapMem (floc fs)) (slot fs) φ os)
               → Goal
      out-move wv pv ca ep rest =
        fin (mvPS-run prog fs₁ (AtDynamic (cellLoc i 0)) 0 dst wL (Seg-++ˡ prog (suc (fpc fs)) (mvPS 0 dst wL) _ s) h refl def (λ k _ → refl)
               (λ k k′ _ _ ()) (infr Bf (top-in (budget φ) (ws S) wL (≤-trans fit (m≤n+m (OP φ) (EP φ))))))
        where
          def : ∀ k → k < wL → Σ W λ x → MemOps.readLoc {FS} (floc fs₁) (offsetLoc (AtDynamic (cellLoc i 0)) (k + 0)) ≡ just x
          def k k< = case at-def wv ca k (subst (k <_) (sym (vw-len pv)) k<) of λ where
            (x , ex) → x , trans (cong (λ z → heapMem (floc fs) (heap-loc (mkHeapRef (serial i)) z))
                                   (trans (Data.Nat.Properties.+-identityʳ (k + 0)) refl)) ex
          ptrEq : slot fs (bot ∸ 1) ≡ just (cellPtr i)
          ptrEq = trans (cong (slot fs) (new-top (budget φ) 1 (ws S))) ep
          fin : Σ FlatState (λ fs₂ → FlatSteps prog (nsteps wL) fs₁ fs₂ × MovedP fs₁ fs₂ (AtDynamic (cellLoc i 0)) 0 dst wL) → Goal
          fin (fs₂ , st₂ , P) =
            fs₃ ,
            step-at fs₁ (h , f₀) (restore-step fs (bot ∸ 1) (in-fr (infr {fs = fs} Bf (top-in (budget φ) (ws S) 1 (≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))))) 0 (s≤s z≤n)) ptrEq) (FlatSteps-++ st₂ (step-at fs₃ (h₂ , ffree) (ffree-step fs₂ (1 ⊔ wL)) [])) ,
            record { c-env  = subst (λ r → EnvW r (slot fs₃) es) (sym (p-heap P))
                                (envW-frame es (λ x x< → p-rest P x (λ k _ e → Data.Nat.Properties.<-irrefl e (<-≤-trans (env< x x<) (m≤n+m dst k)))) (c-env C))
                   ; c-stk  = ( wv , subst (λ r → VW r v wv) (sym (p-heap P)) pv
                              , subst (λ z → SlotsAt (slot fs₃) z wv) (new-top (budget φ) wL (ws S)) (cell-slots wv P ca (vw-len pv)) )
                            , subst (λ r → StkW r (slot fs₃) φ os) (sym (p-heap P))
                                (stkW-frame os fitS (λ x lo _ → p-rest P x (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (in-stk k k<) lo))) rest)
                   ; c-efit = c-efit C ; c-sfit = fit }
            , ran-trans (ran-regs _) (ran-trans (ranP P bP) ran-pc)
            where
              fs₃ = record fs₂ { fpc = suc (fpc fs₂) }
              h₂ : fhalted (floc fs₂) ≡ false
              h₂ = trans (pm-halt P) h
              ffree : fetch prog (fpc fs₂) ≡ just (instr-free-heap (1 ⊔ wL))
              ffree = subst (λ z → fetch prog z ≡ just (instr-free-heap (1 ⊔ wL)))
                        (trans (cong (suc (fpc fs) +_) (len-mvPS 0 dst wL)) (trans (+-comm (suc (fpc fs)) (nsteps wL)) (sym (p-pc P))))
                        (proj₁ (Seg-++ʳ prog (suc (fpc fs)) (mvPS 0 dst wL) _ s))

  ----------------------------------------------------------------------
  -- 10. A CONFIGURATION'S CELLS, and its words while the heap changes
  -- elsewhere (a fresh cell's block is no held cell's).
  ----------------------------------------------------------------------

  cntE : ∀ {Es} → Slots Es → Id → ℕ
  cntE []ᵉ         i = 0
  cntE (vw e es)   i = cnt e i + cntE es i
  cntE (ln e x es) i = (cnt e i + cnt x i) + cntE es i

  cntS : ∀ {S} → Stk S → Id → ℕ
  cntS []ˢ       i = 0
  cntS (v ∷ˢ os) i = cnt v i + cntS os i

  private
    lft′ : ∀ {a b} → 1 ≤ a → 1 ≤ a + b
    lft′ {a} {b} p = ≤-trans p (m≤m+n a b)
    rgt′ : ∀ {a b} → 1 ≤ b → 1 ≤ a + b
    rgt′ {a} {b} p = ≤-trans p (m≤n+m b a)

  envW-heap : ∀ {rd rd′ sm Es} (es : Slots Es)
            → (∀ i k → 1 ≤ cntE es i → rd′ (cellLoc i k) ≡ rd (cellLoc i k)) → EnvW rd sm es → EnvW rd′ sm es
  envW-heap []ᵉ h tt = tt
  envW-heap (vw e es) h ((w , p , s) , ev) =
    (w , vw-frame p (λ i k c → h i k (lft′ c)) , s) , envW-heap es (λ i k c → h i k (rgt′ c)) ev
  envW-heap (ln e x es) h ((w , p , s) , ev) =
    (w , vw-frame p (λ i k c → h i k (lft′ c)) , s) , envW-heap es (λ i k c → h i k (rgt′ c)) ev

  stkW-heap : ∀ {rd rd′ sm φ S} (os : Stk S)
            → (∀ i k → 1 ≤ cntS os i → rd′ (cellLoc i k) ≡ rd (cellLoc i k)) → StkW rd sm φ os → StkW rd′ sm φ os
  stkW-heap []ˢ h tt = tt
  stkW-heap (v ∷ˢ os) h ((w , p , s) , st) =
    (w , vw-frame p (λ i k c → h i k (lft′ c)) , s) , stkW-heap os (λ i k c → h i k (rgt′ c)) st

  ----------------------------------------------------------------------
  -- 11. ★ A FRESH CELL: the block the counter names, of its words.
  ----------------------------------------------------------------------

  open import Once.CCC.Machine.SMCore using (size-with; size-with-aux)
  open import Data.Nat using (_<ᵇ_; _≟_)
  open import Relation.Nullary using (yes; no)

  -- the fresh block has its size
  size-with-same : ∀ n r (szs : ℕ → ℕ) → size-with n r szs r ≡ n
  size-with-same n r szs = same (r ≟ r)
    where
      same : (d : Relation.Nullary.Dec (r ≡ r)) → size-with-aux n {r} {r} szs d ≡ n
      same (yes _) = refl
      same (no ne) = Data.Empty.⊥-elim (ne refl)

  <ᵇ-true : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
  <ᵇ-true {zero}  {suc n} _        = refl
  <ᵇ-true {suc m} {suc n} (s≤s lt) = <ᵇ-true lt

  -- a block's words are no other block's
  other-block : ∀ {r s o o′} → ¬ r ≡ s → ¬ AtDynamic {FS} (heap-loc (mkHeapRef s) o′) ≡ AtDynamic (heap-loc (mkHeapRef r) o)
  other-block ne refl = ne refl

  -- a cell's words, from the slots it was filled from
  slots-at : ∀ {rd : HeapLocation → Maybe W} {sm : ℕ → Maybe W} {i} (w : List W) o src
           → (∀ k → k < length w → rd (cellLoc i (k + o)) ≡ sm (k + src)) → SlotsAt sm src w → At rd i o w
  slots-at []      o src h tt      = tt
  slots-at {rd} {sm} {i} (x ∷ w) o src h (e , s) =
    trans (h 0 (s≤s z≤n)) e ,
    slots-at {rd} {sm} {i} w (suc o) (suc src)
      (λ k k< → trans (cong (λ z → rd (cellLoc i z)) (+-suc k o)) (trans (h (suc k) (s≤s k<)) (cong sm (sym (+-suc k src))))) s

  open import Once.LinCore.Moves {FS} using (alloc-step; mov-in-step; mov-out-step; mvSP-run; MovedW; module MovedW)
  open MovedW using (w-pc; w-alloc; w-in; w-moved; w-rest)
    renaming (w-halt to wm-halt)
  open import Once.LinCore.MoveCode using (mvSP)
  open import Once.CCC.Machine.SMCore using (instr-alloc-heap; mov-to-input; mov-to-output)

  -- ★ `lIn`: a fresh cell, the counter's block, holding the layer's words;
  -- its pointer on the stack; the counter moves on
  lIn-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es F S} {es : Slots Es} {os : Stk S} {v : MV (LF∙ F (μt F))} {n}
          → AllocState.next-heap-ref (falloc fs) ≡ n
          → (∀ j → n ≤ serial j → cntE es j ≡ 0 × cntS (v ∷ˢ os) j ≡ 0)
          → Seg prog (fpc fs) (instr-alloc-heap (1 ⊔ wsz (LF∙ F (μt F))) ∷ mov-to-input
                                ∷ mvSP ((budget φ ∸ ws S) ∸ wsz (LF∙ F (μt F))) 0 (wsz (LF∙ F (μt F)))
                                ++ mov-to-output ∷ store-at-slot ((budget φ ∸ ws S) ∸ 1) ∷ [])
          → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
          → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ v ∷ˢ os)
          → ws (μt F ∷ S) ≤ OP φ
          → Σ FlatState λ fs′ → FlatSteps prog (suc (suc (nsteps (wsz (LF∙ F (μt F))) + 2))) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mmu (szμ F , n) v ∷ˢ os)
              × AllocState.next-heap-ref (falloc fs′) ≡ suc n × Ran (suc (suc (nsteps (wsz (LF∙ F (μt F))) + 2))) 1 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  lIn-sim prog fs φ {Es} {F} {S} {es} {os} {v} refl fresh (f₀ , f₁ , s) h Bf C fit = case c-stk C of λ where
      ((wv , pv , sv) , rest) → lin-move wv pv sv rest
    where
      import Data.Nat.Properties
      wL = wsz (LF∙ F (μt F))
      bot = budget φ ∸ ws S
      src = bot ∸ wL
      r = AllocState.next-heap-ref (falloc fs)
      loc = AtDynamic {FS} (heap-loc (mkHeapRef r) 0)
      fs₁ = record fs { floc   = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (SV-Ptr loc) }
                      ; falloc = record (falloc fs) { next-heap-ref = suc r ; block-size = size-with (1 ⊔ wL) r (AllocState.block-size (falloc fs)) }
                      ; fpc    = suc (fpc fs) }
      fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 (SV-Ptr loc) } ; fpc = suc (fpc fs₁) }
      ib : ∀ k → k < wL → ExecFinal.in-block? {FS} (AllocState.block-size (falloc fs₂)) (offsetLoc loc (k + 0)) ≡ true
      ib k k< = trans (cong ((k + 0) + 0 <ᵇ_) (size-with-same (1 ⊔ wL) r (AllocState.block-size (falloc fs))))
                      (<ᵇ-true (<-≤-trans (subst (_< wL) (sym (trans (Data.Nat.Properties.+-identityʳ (k + 0)) (Data.Nat.Properties.+-identityʳ k))) k<)
                                          (Data.Nat.Properties.m≤n⊔m 1 wL)))
      rest′ = Seg-++ʳ prog (suc (suc (fpc fs))) (mvSP src 0 wL) _ s
      -- the fresh block below the counter, its words inside it (D441)
      lt₂ : r < AllocState.next-heap-ref (falloc fs₂)
      lt₂ = Data.Nat.Properties.n<1+n r
      bnd₂ : ∀ k → k < wL → (k + 0) < AllocState.block-size (falloc fs₂) r
      bnd₂ k k< = subst (k + 0 <_) (sym (size-with-same (1 ⊔ wL) r (AllocState.block-size (falloc fs))))
                    (<-≤-trans (subst (_< wL) (sym (Data.Nat.Properties.+-identityʳ k)) k<) (Data.Nat.Properties.m≤n⊔m 1 wL))
      ne-of : ∀ j → 1 ≤ cntE es j + cntS (v ∷ˢ os) j → ¬ serial j ≡ r
      ne-of j c e = case fresh j (Data.Nat.Properties.≤-reflexive (sym e)) of λ where
          (z₁ , z₂) → Data.Nat.Properties.<-irrefl refl (subst (λ q → 0 < q) (cong₂′ z₁ z₂) c)
        where cong₂′ : cntE es j ≡ 0 → cntS (v ∷ˢ os) j ≡ 0 → cntE es j + cntS (v ∷ˢ os) j ≡ 0
              cong₂′ a b = trans (cong (_+ cntS (v ∷ˢ os) j) a) b
      ne-env : ∀ j → 1 ≤ cntE es j → ¬ serial j ≡ r
      ne-env j c = ne-of j (≤-trans c (m≤m+n (cntE es j) (cntS (v ∷ˢ os) j)))
      ne-v : ∀ j → 1 ≤ cnt v j → ¬ serial j ≡ r
      ne-v j c = ne-of j (≤-trans c (≤-trans (m≤m+n (cnt v j) (cntS os j)) (m≤n+m (cntS (v ∷ˢ os) j) (cntE es j))))
      ne-os : ∀ j → 1 ≤ cntS os j → ¬ serial j ≡ r
      ne-os j c = ne-of j (≤-trans c (≤-trans (m≤n+m (cntS os j) (cnt v j)) (m≤n+m (cntS (v ∷ˢ os) j) (cntE es j))))
      fitB : 1 + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) 1) fitB
      env≤ : ws Es ≤ bot ∸ 1
      env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) 1 (ws S))) (env-below φ (ws (μt F ∷ S)) fit))
      b1<b : bot ∸ 1 < bot
      b1<b = Data.Nat.Properties.∸-monoʳ-< {o = 0} (s≤s z≤n) (≤∸ 1 (ws S) (budget φ) fitB)
      Goal : Set
      Goal = Σ FlatState λ fs′ → FlatSteps prog (suc (suc (nsteps wL + 2))) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ mmu (szμ F , r) v ∷ˢ os)
               × AllocState.next-heap-ref (falloc fs′) ≡ suc r × Ran (suc (suc (nsteps wL + 2))) 1 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
      -- the layer's words, moved into the fresh cell
      lin-move : ∀ wv (pv : VW (heapMem (floc fs)) v wv) (sv : SlotsAt (slot fs) (budget φ ∸ ws (LF∙ F (μt F) ∷ S)) wv)
                   (rest : StkW (heapMem (floc fs)) (slot fs) φ os)
               → Goal
      lin-move wv pv sv rest =
        fin (mvSP-run prog fs₂ loc src 0 wL (Seg-++ˡ prog (suc (suc (fpc fs))) (mvSP src 0 wL) _ s) h refl def (λ k _ → refl) ib (λ k k′ _ _ ())
               (infr Bf (top-in (budget φ) (ws S) wL (≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))))))
        where
          def : ∀ k → k < wL → Σ W λ x → slot fs₂ (k + src) ≡ just x
          def k k< = slots-def {slot fs} {src} wv (subst (λ z → SlotsAt (slot fs) z wv) (sym (new-top (budget φ) wL (ws S))) sv) k
                       (subst (k <_) (sym (vw-len pv)) k<)
          fin : Σ FlatState (λ fs₃ → FlatSteps prog (nsteps wL) fs₂ fs₃ × MovedW fs₂ fs₃ loc src 0 wL) → Goal
          fin (fs₃ , st₃ , Wd) =
            fs₅ ,
            step-at fs₁ (h , f₀) (alloc-step fs (1 ⊔ wL)) (step-at fs₂ (h , f₁) (mov-in-step fs₁)
              (FlatSteps-++ st₃ (step-at fs₄ (h₃ , f₄) (mov-out-step fs₃) (step-at fs₅ (h₃ , f₅) (store-step fs₄ (bot ∸ 1)
                                                                                      (in-fr (infr {fs = fs₄} (subst (budget φ ≤_) (sym (cong AllocState.frame-slots (w-alloc Wd))) Bf)
                                                                                         (top-in (budget φ) (ws S) 1 (≤-trans fit (m≤n+m (OP φ) (EP φ))))) 0 (s≤s z≤n))) [])))) ,
            record { c-env  = envW-heap es (λ j k c → hp (serial j) k (ne-env j c))
                                (envW-frame es (λ x x< → stk-kept x (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans x< env≤))) (c-env C))
                   ; c-stk  = ( cellPtr (szμ F , r) ∷ []
                              , vmu (vw-frame pv (λ j k c → hp (serial j) k (ne-v j c))) cell
                              , (trans (cong (slot fs₅) (sym (new-top (budget φ) 1 (ws S)))) top₅ , tt) )
                            , stkW-heap os (λ j k c → hp (serial j) k (ne-os j c))
                                (stkW-frame os fitS (λ x lo _ → stk-kept x (λ e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans b1<b lo))) rest)
                   ; c-efit = c-efit C ; c-sfit = fit } ,
            cong AllocState.next-heap-ref (w-alloc Wd) ,
            ran-trans (ran-heap fs (1 ⊔ wL)) (ran-trans (ran-regs _)
              (ran-trans (ranW Wd (λ f x ne k k< ()) (λ x k k< ()) (λ hl lt k k< → fresh-block (AllocState.next-heap-ref (falloc fs)) hl (k + 0) lt) (inb-write r Wd lt₂ bnd₂)) (ran-trans (ran-regs _) (ran-store fs₄ (bot ∸ 1) _ (<-≤-trans b1<b (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)))))))
            where
              fs₄ = record fs₃ { floc = record (floc fs₃) { regs = writeReg (LocState.regs (floc fs₃)) Output (readReg (LocState.regs (floc fs₃)) Input1) }
                               ; fpc = suc (fpc fs₃) }
              cf₄ = AllocState.current-frame (falloc fs₄)
              fs₅ = record fs₄ { floc = MemOps.writeLoc {FS} (floc fs₄) (AtStack cf₄ (bot ∸ 1)) (readReg (LocState.regs (floc fs₄)) Output)
                               ; fpc = suc (fpc fs₄) }
              h₃ : fhalted (floc fs₃) ≡ false
              h₃ = trans (wm-halt Wd) h
              pcEq : suc (suc (fpc fs)) + length (mvSP src 0 wL) ≡ fpc fs₃
              pcEq = trans (cong (suc (suc (fpc fs)) +_) (len-mvSP src 0 wL)) (trans (+-comm (suc (suc (fpc fs))) (nsteps wL)) (sym (w-pc Wd)))
              f₄ : fetch prog (fpc fs₃) ≡ just mov-to-output
              f₄ = subst (λ z → fetch prog z ≡ just mov-to-output) pcEq (proj₁ rest′)
              f₅ : fetch prog (fpc fs₄) ≡ just (store-at-slot (bot ∸ 1))
              f₅ = subst (λ z → fetch prog (suc z) ≡ just (store-at-slot (bot ∸ 1))) pcEq (proj₁ (proj₂ rest′))
              -- the heap: only the fresh block is written
              hp : ∀ s k → ¬ s ≡ r → heapMem (floc fs₅) (heap-loc (mkHeapRef s) k) ≡ heapMem (floc fs) (heap-loc (mkHeapRef s) k)
              hp s k ne = w-rest Wd (AtDynamic (heap-loc (mkHeapRef s) k)) (λ k′ _ e → other-block (λ e′ → ne (sym e′)) e)
              -- the stack: only the pointer's slot is written
              cfEq : AllocState.current-frame (falloc fs₃) ≡ AllocState.current-frame (falloc fs)
              cfEq = cong AllocState.current-frame (w-alloc Wd)
              stk-kept : ∀ x → ¬ x ≡ bot ∸ 1 → slot fs₅ x ≡ slot fs x
              stk-kept x ne =
                trans (store-other (floc fs₄) cf₄ (bot ∸ 1) _ x (λ e → ne (sym e)))
                  (trans (w-rest Wd (AtStack cf₄ x) (λ k′ _ ()))
                         (cong (λ f → LocState.stackMem (floc fs) f x) cfEq))
              -- the cell holds the layer's words
              cell : At (heapMem (floc fs₅)) (szμ F , r) 0 wv
              cell = slots-at wv 0 src
                       (λ k k< → trans (cong (λ z → heapMem (floc fs₃) (heap-loc (mkHeapRef r) z)) (sym (Data.Nat.Properties.+-identityʳ (k + 0))))
                                   (w-moved Wd k (subst (k <_) (vw-len pv) k<)))
                       (subst (λ z → SlotsAt (slot fs) z wv) (sym (new-top (budget φ) wL (ws S))) sv)
              -- the pointer on the stack
              top₅ : slot fs₅ (bot ∸ 1) ≡ just (cellPtr (szμ F , r))
              top₅ = trans (store-same (floc fs₄) cf₄ (bot ∸ 1) _) (cong just (w-in Wd))

  -- ★ `eout`, `eoutq`: the viewed node's layer, read out of its cell into a
  -- new buffer above
  eout-sim : ∀ prog (fs : FlatState) (φ : Frame) {F Es S} {es : Slots (μt F ∷ Es)} {os : Stk S} {i} {v : MV (LF∙ F (μt F))}
           → see es ≡ mmu i v
           → Seg prog (fpc fs) (restore-input (ws Es) ∷ mvPS 0 (suc (ws Es)) (wsz (LF∙ F (μt F))))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ os)
           → ws (LF∙ F (μt F) ∷ μt F ∷ Es) ≤ EP φ
           → Σ FlatState λ fs′ → FlatSteps prog (suc (nsteps (wsz (LF∙ F (μt F))))) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw v es ∥ os) × Ran (suc (nsteps (wsz (LF∙ F (μt F))))) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
  eout-sim prog fs φ {F} {Es} {S} {es} {os} {i} {v} eq (f₀ , s) h Bf C fit = case topW es (c-env C) of λ where
      (w , pw , sw) → case subst (λ z → VW (heapMem (floc fs)) z w) eq pw of λ where
        (vmu {wv = wv} pv ca) → case sw of λ where
          (ep , _) → out-move wv pv ca ep
    where
      import Data.Nat.Properties
      wL = wsz (LF∙ F (μt F))
      bP : suc (ws Es) + wL ≤ budget φ
      bP = ≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (suc (ws Es)) wL)) (≤-trans fit (m≤m+n (EP φ) (OP φ)))
      fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Input1 (cellPtr i) } ; fpc = suc (fpc fs) }
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))
      in-env : ∀ k → k < wL → k + suc (ws Es) < EP φ
      in-env k k< = <-≤-trans (+-monoˡ-< (suc (ws Es)) k<) fit
      Goal : Set
      Goal = Σ FlatState λ fs′ → FlatSteps prog (suc (nsteps wL)) fs fs′
               × CfgW (heapMem (floc fs′)) (slot fs′) φ (vw v es ∥ os) × Ran (suc (nsteps wL)) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′
      -- the node's layer, read out of its cell above the environment
      out-move : ∀ wv (pv : VW (heapMem (floc fs)) v wv) (ca : At (heapMem (floc fs)) i 0 wv)
                   (ep : slot fs (ws Es) ≡ just (cellPtr i))
               → Goal
      out-move wv pv ca ep =
        fin (mvPS-run prog fs₁ (AtDynamic (cellLoc i 0)) 0 (suc (ws Es)) wL s h refl def (λ k _ → refl) (λ k k′ _ _ ())
               (infr Bf (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (suc (ws Es)) wL)) (env-in φ fit))))
        where
          def : ∀ k → k < wL → Σ W λ x → MemOps.readLoc {FS} (floc fs₁) (offsetLoc (AtDynamic (cellLoc i 0)) (k + 0)) ≡ just x
          def k k< = case at-def wv ca k (subst (k <_) (sym (vw-len pv)) k<) of λ where
            (x , ex) → x , trans (cong (λ z → heapMem (floc fs) (heap-loc (mkHeapRef (serial i)) z))
                                   (Data.Nat.Properties.+-identityʳ (k + 0))) ex
          fin : Σ FlatState (λ fs₂ → FlatSteps prog (nsteps wL) fs₁ fs₂ × MovedP fs₁ fs₂ (AtDynamic (cellLoc i 0)) 0 (suc (ws Es)) wL) → Goal
          fin (fs₂ , st₂ , P) =
            fs₂ ,
            step-at fs₁ (h , f₀) (restore-step fs (ws Es) (in-fr (infr {fs = fs} Bf (≤-trans (Data.Nat.Properties.≤-reflexive (+-comm (ws Es) 1)) (env-in φ (c-efit C)))) 0 (s≤s z≤n)) ep) st₂ ,
            record { c-env  = ( wv , subst (λ r → VW r v wv) (sym (p-heap P)) pv , cell-slots wv P ca (vw-len pv) )
                            , subst (λ r → EnvW r (slot fs₂) es) (sym (p-heap P))
                                (envW-frame es (λ x x< → p-rest P x (λ k _ e → Data.Nat.Properties.<-irrefl e (<-≤-trans x< (m≤n+m (suc (ws Es)) k))))
                                  (c-env C))
                   ; c-stk  = subst (λ r → StkW r (slot fs₂) φ os) (sym (p-heap P))
                                (stkW-frame os fitS (λ x lo _ → p-rest P x (λ k k< e → apart φ (c-sfit C) (in-env k k<) lo e)) (c-stk C))
                   ; c-efit = fit ; c-sfit = c-sfit C }
            , ran-trans (ran-regs _) (ranP P bP)

  ----------------------------------------------------------------------
  -- 12. ★ A SWAP: the top element to the words below the stack, the next
  -- one up, the first back above it.
  ----------------------------------------------------------------------

  private
    swap-words : ∀ a b s → a + (b + s) ≡ b + (a + s)
    swap-words = solve-∀

  -- a slot outside a move's range is kept
  outside-move : ∀ {fs fs′ a b n} x → MovedS fs fs′ a b n → (x < b) ⊎ (n + b ≤ x) → slot fs′ x ≡ slot fs x
  outside-move x M (inj₁ x<b) = m-rest M x (λ k _ e → Data.Nat.Properties.<-irrefl e (<-≤-trans x<b (m≤n+m _ k)))
    where import Data.Nat.Properties
  outside-move {b = b} x M (inj₂ ge) = m-rest M x (λ k k< e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans (+-monoˡ-< b k<) ge))
    where import Data.Nat.Properties

  -- words disjoint from a move's range are kept
  kept-words : ∀ {fs fs′ a b n o} (w : List W) → MovedS fs fs′ a b n
             → (length w + o ≤ b) ⊎ (n + b ≤ o) → SlotsAt (slot fs) o w → SlotsAt (slot fs′) o w
  kept-words {fs} {fs′} {a} {b} {n} {o} w M d s = slots-frame {slot fs} {slot fs′} w (λ k k< → outside-move (k + o) M (side k k< d)) s
    where
      import Data.Nat.Properties
      side : ∀ k → k < length w → (length w + o ≤ b) ⊎ (n + b ≤ o) → (k + o < b) ⊎ (n + b ≤ k + o)
      side k k< (inj₁ le) = inj₁ (<-≤-trans (+-monoˡ-< o k<) le)
      side k k< (inj₂ ge) = inj₂ (≤-trans ge (m≤n+m o k))

  swap-sim : ∀ prog (fs : FlatState) (φ : Frame) {Es A B S} {es : Slots Es} {os : Stk S} {a : MV A} {b : MV B}
           → let t = budget φ ∸ ws (A ∷ B ∷ S) in
             Seg prog (fpc fs) (mvSS t (t ∸ wsz A) (wsz A) ++ mvSS (t + wsz A) t (wsz B) ++ mvSS (t ∸ wsz A) (t + wsz B) (wsz A))
           → fhalted (floc fs) ≡ false → budget φ ≤ Fr fs
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ a ∷ˢ b ∷ˢ os)
           → wsz A + ws (A ∷ B ∷ S) ≤ OP φ
           → Σ FlatState λ fs₃ → FlatSteps prog (nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))) fs fs₃
               × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ b ∷ˢ a ∷ˢ os)
               × Ran (nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
  swap-sim prog fs φ {Es} {A} {B} {S} {es} {os} {a} {b} s h Bf C fitT = case c-stk C of λ where
      ((wa , pa , sa) , (wb , pb , sb) , rest) → swap-move wa pa sa wb pb sb rest
    where
      import Data.Nat.Properties
      ≤-reflexive′ = Data.Nat.Properties.≤-reflexive
      t = budget φ ∸ ws (A ∷ B ∷ S)
      scr = t ∸ wsz A
      X₁ = mvSS t scr (wsz A)
      X₂ = mvSS (t + wsz A) t (wsz B)
      X₃ = mvSS scr (t + wsz B) (wsz A)
      fitT0 : wsz A + (wsz B + ws S) ≤ budget φ
      fitT0 = ≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))
      AB≤W : wsz A + wsz B ≤ ws (A ∷ B ∷ S)
      AB≤W = Data.Nat.Properties.+-monoʳ-≤ (wsz A) (m≤m+n (wsz B) (ws S))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) (wsz A + wsz B)) (≤-trans (≤-reflexive′ (+-assoc (wsz A) (wsz B) (ws S))) fitT0)
      wA≤t : wsz A ≤ t
      wA≤t = ≤∸ (wsz A) (ws (A ∷ B ∷ S)) (budget φ) (≤-trans fitT (m≤n+m (OP φ) (EP φ)))
      scrEnd : wsz A + scr ≡ t
      scrEnd = Data.Nat.Properties.m+[n∸m]≡n wA≤t
      t-top : t + ws (A ∷ B ∷ S) ≡ budget φ
      t-top = Data.Nat.Properties.m∸n+n≡m fitT0
      b₁ : scr + wsz A ≤ budget φ
      b₁ = ≤-trans (≤-reflexive′ (trans (+-comm scr (wsz A)) scrEnd)) (Data.Nat.Properties.m∸n≤m (budget φ) (ws (A ∷ B ∷ S)))
      b₂ : t + wsz B ≤ budget φ
      b₂ = ≤-trans (Data.Nat.Properties.+-monoʳ-≤ t (≤-trans (m≤m+n (wsz B) (ws S)) (m≤n+m (wsz B + ws S) (wsz A)))) (≤-reflexive′ t-top)
      b₃ : (t + wsz B) + wsz A ≤ budget φ
      b₃ = ≤-trans (≤-reflexive′ (+-assoc t (wsz B) (wsz A)))
             (≤-trans (Data.Nat.Properties.+-monoʳ-≤ t (≤-trans (≤-reflexive′ (+-comm (wsz B) (wsz A)))
                                                         (Data.Nat.Properties.+-monoʳ-≤ (wsz A) (m≤m+n (wsz B) (ws S)))))
               (≤-reflexive′ t-top))
      -- where the moves end: the rest of the stack
      bPos : wsz A + t ≡ budget φ ∸ (wsz B + ws S)
      bPos = pair-at (budget φ) (wsz A) (wsz B) (ws S) fitT0
      endW : wsz A + (t + wsz B) ≡ budget φ ∸ ws S
      endW = trans (r (wsz A) t (wsz B))
              (trans (cong (wsz B +_) bPos)
                (pair-at (budget φ) (wsz B) 0 (ws S) (≤-trans (m≤n+m (wsz B + ws S) (wsz A)) fitT0)))
        where r : ∀ a t b → a + (t + b) ≡ b + (a + t)
              r = solve-∀
      aPos : t + wsz B ≡ budget φ ∸ ws (A ∷ S)
      aPos = trans (+-comm t (wsz B))
               (trans (cong (λ z → wsz B + (budget φ ∸ z)) (swap-words (wsz A) (wsz B) (ws S)))
                 (pair-at (budget φ) (wsz B) (wsz A) (ws S) (≤-trans (≤-reflexive′ (sym (swap-words (wsz A) (wsz B) (ws S)))) fitT0)))
      -- the environment lies below the words used
      x<scr : ∀ x → x < ws Es → x < scr
      x<scr x x< = <-≤-trans x< (≤-trans (c-efit C)
                     (subst (EP φ ≤_) (sym (new-top (budget φ) (wsz A) (ws (A ∷ B ∷ S)))) (env-below φ (wsz A + ws (A ∷ B ∷ S)) fitT)))
      Goal : Set
      Goal = Σ FlatState λ fs₃ → FlatSteps prog (nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))) fs fs₃
               × CfgW (heapMem (floc fs₃)) (slot fs₃) φ (es ∥ b ∷ˢ a ∷ˢ os)
               × Ran (nsteps (wsz A) + (nsteps (wsz B) + nsteps (wsz A))) 0 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃
      -- the three moves: the top element down, the next one up, the first back above it
      swap-move : ∀ wa (pa : VW (heapMem (floc fs)) a wa) (sa : SlotsAt (slot fs) t wa)
                    wb (pb : VW (heapMem (floc fs)) b wb) (sb : SlotsAt (slot fs) (budget φ ∸ (wsz B + ws S)) wb)
                    (rest : StkW (heapMem (floc fs)) (slot fs) φ os)
                → Goal
      swap-move wa pa sa wb pb sb rest =
        run₁ (mvSS-run prog fs t scr (wsz A) (Seg-++ˡ prog (fpc fs) X₁ _ s) h
               (infr Bf (sub-le (budget φ) (ws (A ∷ B ∷ S)) (wsz A) (m≤m+n (wsz A) (wsz B + ws S)) fitT0))
               (infr Bf (≤-trans (≤-reflexive′ (m∸n+n≡m wA≤t)) (Data.Nat.Properties.m∸n≤m (budget φ) (ws (A ∷ B ∷ S)))))
               (λ k k< → slots-def {slot fs} {t} wa sa k (subst (k <_) (sym (vw-len pa)) k<))
               (λ k k′ lt _ → no-clash-down (Data.Nat.Properties.m∸n≤m t (wsz A)) lt))
        where
          sb′ : SlotsAt (slot fs) (t + wsz A) wb
          sb′ = subst (λ z → SlotsAt (slot fs) z wb) (trans (sym bPos) (+-comm (wsz A) t)) sb
          run₁ : Σ FlatState (λ fs₁ → FlatSteps prog (nsteps (wsz A)) fs fs₁ × MovedS fs fs₁ t scr (wsz A)) → Goal
          run₁ (fs₁ , st₁ , M₁) =
            run₂ (mvSS-run prog fs₁ (t + wsz A) t (wsz B) s₂ (trans (m-halt M₁) h)
                   (infr B₁ (≤-trans (≤-reflexive′ (+-assoc t (wsz A) (wsz B)))
                               (sub-le (budget φ) (ws (A ∷ B ∷ S)) (wsz A + wsz B) AB≤W fitT0)))
                   (infr B₁ (sub-le (budget φ) (ws (A ∷ B ∷ S)) (wsz B) (≤-trans (m≤m+n (wsz B) (ws S)) (m≤n+m (wsz B + ws S) (wsz A))) fitT0))
                   def₂ (λ k k′ lt _ → no-clash-down (m≤m+n t (wsz A)) lt))
            where
              B₁ : budget φ ≤ Fr fs₁
              B₁ = subst (budget φ ≤_) (sym (cong AllocState.frame-slots (MovedS.m-alloc M₁))) Bf
              s₂ : Seg prog (fpc fs₁) X₂
              s₂ = subst (λ z → Seg prog z X₂)
                     (trans (cong (fpc fs +_) (len-mvSS t scr (wsz A))) (trans (+-comm (fpc fs) (nsteps (wsz A))) (sym (m-pc M₁))))
                     (Seg-++ˡ prog (fpc fs + length X₁) X₂ X₃ (Seg-++ʳ prog (fpc fs) X₁ _ s))
              def₂ : ∀ k → k < wsz B → Σ W λ x → slot fs₁ (k + (t + wsz A)) ≡ just x
              def₂ k k< = case slots-def {slot fs} {t + wsz A} wb sb′ k (subst (k <_) (sym (vw-len pb)) k<) of λ where
                (x , ex) → x , trans (outside-move (k + (t + wsz A)) M₁
                                        (inj₂ (≤-trans (≤-reflexive′ scrEnd) (≤-trans (m≤m+n t (wsz A)) (m≤n+m (t + wsz A) k)))))
                                     ex
              run₂ : Σ FlatState (λ fs₂ → FlatSteps prog (nsteps (wsz B)) fs₁ fs₂ × MovedS fs₁ fs₂ (t + wsz A) t (wsz B)) → Goal
              run₂ (fs₂ , st₂ , M₂) =
                run₃ (mvSS-run prog fs₂ scr (t + wsz B) (wsz A) s₃ (trans (m-halt M₂) (trans (m-halt M₁) h))
                       (infr B₂ (≤-trans (≤-reflexive′ (m∸n+n≡m wA≤t)) (Data.Nat.Properties.m∸n≤m (budget φ) (ws (A ∷ B ∷ S)))))
                       (infr B₂ (≤-trans (≤-reflexive′ (trans (+-assoc t (wsz B) (wsz A)) (cong (t +_) (+-comm (wsz B) (wsz A)))))
                                   (sub-le (budget φ) (ws (A ∷ B ∷ S)) (wsz A + wsz B) AB≤W fitT0)))
                       def₃
                       (λ k k′ _ lt′ → no-clash {k = k} (≤-trans (≤-reflexive′ (trans (+-comm scr (wsz A)) scrEnd)) (m≤m+n t (wsz B))) lt′))
                where
                  B₂ : budget φ ≤ Fr fs₂
                  B₂ = subst (budget φ ≤_) (sym (cong AllocState.frame-slots (trans (MovedS.m-alloc M₂) (MovedS.m-alloc M₁)))) Bf
                  s₃ : Seg prog (fpc fs₂) X₃
                  s₃ = subst (λ z → Seg prog z X₃)
                         (trans (cong (_+ length X₂) (cong (fpc fs +_) (len-mvSS t scr (wsz A))))
                           (trans (cong ((fpc fs + nsteps (wsz A)) +_) (len-mvSS (t + wsz A) t (wsz B)))
                             (trans (+-comm (fpc fs + nsteps (wsz A)) (nsteps (wsz B)))
                               (trans (cong (nsteps (wsz B) +_) (+-comm (fpc fs) (nsteps (wsz A))))
                                 (trans (cong (nsteps (wsz B) +_) (sym (m-pc M₁))) (sym (m-pc M₂)))))))
                         (Seg-++ʳ prog (fpc fs + length X₁) X₂ X₃ (Seg-++ʳ prog (fpc fs) X₁ _ s))
                  -- the first element's words, in the words below the stack, kept by the second move
                  sa₂ : SlotsAt (slot fs₂) scr wa
                  sa₂ = kept-words wa M₂ (inj₁ (≤-reflexive′ (trans (cong (_+ scr) (vw-len pa)) scrEnd))) (slots-moved wa M₁ sa (vw-len pa))
                  def₃ : ∀ k → k < wsz A → Σ W λ x → slot fs₂ (k + scr) ≡ just x
                  def₃ k k< = slots-def {slot fs₂} {scr} wa sa₂ k (subst (k <_) (sym (vw-len pa)) k<)
                  run₃ : Σ FlatState (λ fs₃ → FlatSteps prog (nsteps (wsz A)) fs₂ fs₃ × MovedS fs₂ fs₃ scr (t + wsz B) (wsz A)) → Goal
                  run₃ (fs₃ , st₃ , M₃) =
                    fs₃ , FlatSteps-++ st₁ (FlatSteps-++ st₂ st₃) ,
                    record { c-env  = subst (λ r → EnvW r (slot fs₃) es) (sym hp)
                                        (envW-frame es (λ x x< → kept₃ x (inj₁ (x<scr x x<))) (c-env C))
                           ; c-stk  = ( wb , subst (λ r → VW r b wb) (sym hp) pb
                                      , subst (λ z → SlotsAt (slot fs₃) z wb) (cong (budget φ ∸_) (swap-words (wsz A) (wsz B) (ws S))) sbF )
                                    , ( wa , subst (λ r → VW r a wa) (sym hp) pa
                                      , subst (λ z → SlotsAt (slot fs₃) z wa) aPos (slots-moved wa M₃ sa₂ (vw-len pa)) )
                                    , subst (λ r → StkW r (slot fs₃) φ os) (sym hp)
                                        (stkW-frame os fitS (λ x lo _ → kept₃ x (inj₂ lo)) rest)
                           ; c-efit = c-efit C
                           ; c-sfit = subst (_≤ OP φ) (swap-words (wsz A) (wsz B) (ws S)) (c-sfit C) }
                    , ran-trans (ranS M₁ b₁) (ran-trans (ranS M₂ b₂) (ranS M₃ b₃))
                    where
                      hp : heapMem (floc fs₃) ≡ heapMem (floc fs)
                      hp = trans (m-heap M₃) (trans (m-heap M₂) (m-heap M₁))
                      -- a slot below all three moves, or above them all, is kept
                      kept₃ : ∀ x → (x < scr) ⊎ (budget φ ∸ ws S ≤ x) → slot fs₃ x ≡ slot fs x
                      kept₃ x (inj₁ x<) =
                        trans (outside-move x M₃ (inj₁ (<-≤-trans x< (≤-trans (Data.Nat.Properties.m∸n≤m t (wsz A)) (m≤m+n t (wsz B))))))
                          (trans (outside-move x M₂ (inj₁ (<-≤-trans x< (Data.Nat.Properties.m∸n≤m t (wsz A)))))
                                 (outside-move x M₁ (inj₁ x<)))
                      kept₃ x (inj₂ ge) =
                        trans (outside-move x M₃ (inj₂ (≤-trans (≤-reflexive′ endW) ge)))
                          (trans (outside-move x M₂ (inj₂ (≤-trans (≤-trans (≤-reflexive′ (+-comm (wsz B) t)) (m≤n+m (t + wsz B) (wsz A))) (≤-trans (≤-reflexive′ endW) ge))))
                                 (outside-move x M₁ (inj₂ (≤-trans (≤-reflexive′ scrEnd) (≤-trans (≤-trans (m≤m+n t (wsz B)) (m≤n+m (t + wsz B) (wsz A))) (≤-trans (≤-reflexive′ endW) ge))))))
                      -- the words: the second element's moved up, kept by the third move
                      sbF : SlotsAt (slot fs₃) t wb
                      sbF = kept-words wb M₃ (inj₁ (≤-reflexive′ (trans (cong (_+ t) (vw-len pb)) (+-comm (wsz B) t))))
                              (slots-moved wb M₂ (kept-words wb M₁ (inj₂ (≤-trans (≤-reflexive′ scrEnd) (m≤m+n t (wsz A)))) sb′) (vw-len pb))
