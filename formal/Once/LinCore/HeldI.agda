-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.HeldI — plan 0.146 B1.4a: D410 amended, on the image.
--
-- A16's `Held.held-always` for the finite-code image: at every configuration
-- a closed program's image reaches, whatever its code, every event so far
-- was legal and the live cells are exactly the cells of the values it holds.
-- The configurations are A16's; the return stack holds code only, so the
-- invariant (`Held.Inv`) is the same, and each new step is one of three
-- kinds: a call, a return or a loop moves nothing; a copy's dispatch opens a
-- view owned below (as `eapply`); a free's dispatch frees the cell and holds
-- what it held (`freed`, as `apply`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-antisym; m≤m+n; m≤n+m; 0∸n≡0; +-comm; +-identityʳ; suc-injective)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.HeldI
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_; op-NoT)
open import Once.LinCore.Held fmt ans bw using (own; held; Owned; Within; Sees; see-own; Inv; module Inv; start-inv)
open Inv
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_; start)

private
  cancelˡ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
  cancelˡ zero    e = e
  cancelˡ (suc c) e = cancelˡ c (suc-injective e)

  cancelʳ : ∀ c {a b} → a + c ≡ b + c → a ≡ b
  cancelʳ c {a} {b} e = cancelˡ c (trans (+-comm c a) (trans e (+-comm b c)))

  -- the same cells, held otherwise
  same : ∀ {sh sh′} {m : Cfg sh} {m′ : Cfg sh′} {n h} → Inv m n h
       → (∀ i → Owned m i ≡ Owned m′ i) → Sees (Cfg.envs m′) → Inv m′ n h
  same inv e s = record { i-le1 = i-le1 inv ; i-above = i-above inv
                        ; i-exact = λ i → trans (i-exact inv i) (e i) ; i-sees = s }

  -- ★ a cell `j` freed, all else held: the invariant at what is held after
  freed : ∀ {sh sh′} {m : Cfg sh} {m′ : Cfg sh′} {n h} j → Inv m n h
        → (∀ i → Owned m i ≡ δ j i + Owned m′ i) → Sees (Cfg.envs m′)
        → OK (free j ∷ []) h × Inv m′ n (play (free j ∷ []) h)
  freed {m′ = m′} {h = h} j inv e s =
    ( (fst fr , tt)
    , record { i-le1   = fst (snd fr)
             ; i-above = λ i le → trans (cong (_∸ δ j i) (i-above inv i le)) (0∸n≡0 (δ j i))
             ; i-exact = λ i → cancelʳ (δ j i) (trans (snd (snd (snd fr)) i)
                                                      (trans (i-exact inv i) (trans (e i) (+-comm (δ j i) (Owned m′ i)))))
             ; i-sees  = s } )
    where
      fr = free-step j (Owned m′) h (λ _ → 0) (i-le1 inv)
             (λ i → ≤-reflexive (sym (trans (i-exact inv i) (trans (e i) (sym (+-identityʳ (δ j i + Owned m′ i)))))))

  topᵒ : ∀ {Es A S} (es : Slots Es) (v : MV A) (os : Stk S) i
      → own es i + (cnt v i + held os i) ≡ cnt v i + (own es i + held os i)
  topᵒ es v os i = r (own es i) (cnt v i) (held os i)
    where r : ∀ O V H → O + (V + H) ≡ V + (O + H)
          r = solve-∀

  xch : ∀ P V O H W → P + V ≡ (O + (V + H)) + W → P ≡ O + (W + H)
  xch P V O H W e = cancelʳ V (trans e (r O V H W))
    where r : ∀ O V H W → (O + (V + H)) + W ≡ (O + (W + H)) + V
          r = solve-∀

  -- a view of what the top view's cell holds: owned below
  inside : ∀ {E Es X} (es : Slots (E ∷ Es)) {x : MV X} (v : MV E) → see es ≡ v
         → (∀ i → 1 ≤ cnt x i → 1 ≤ cnt v i) → Sees es → Within (cnt x) (own es)
  inside es v eq sub s i p = see-own es s i (subst (λ z → 1 ≤ cnt z i) (sym eq) (sub i p))

------------------------------------------------------------------------
-- ★ THE INVARIANT, step by step (A16's, and the image's own steps).
------------------------------------------------------------------------

inv-stepI : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t h}
          → StepI c r m n t c′ r′ m′ n′ → Inv m n h → OK t h × Inv m′ n′ (play t h)
inv-stepI (i-unpair {es = es} {a = a} {b = b} {os = os}) inv =
  (tt , same inv (λ i → cong (own es i +_) (r (cnt a i) (cnt b i) (held os i))) (i-sees inv))
  where r : ∀ A B H → (A + B) + H ≡ A + (B + H)
        r = solve-∀
inv-stepI (i-pair {es = es} {a = a} {b = b} {os = os}) inv =
  (tt , same inv (λ i → cong (own es i +_) (r (cnt a i) (cnt b i) (held os i))) (i-sees inv))
  where r : ∀ A B H → A + (B + H) ≡ (A + B) + H
        r = solve-∀
inv-stepI (i-swap {es = es} {a = a} {b = b} {os = os}) inv =
  (tt , same inv (λ i → cong (own es i +_) (r (cnt a i) (cnt b i) (held os i))) (i-sees inv))
  where r : ∀ A B H → A + (B + H) ≡ B + (A + H)
        r = solve-∀
inv-stepI i-unit inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI {n = n} {h = h} (i-prim {es = es} {v = v} {w = w} {os = os} run) inv =
  ( fst x
  , record { i-le1 = Pre.le1 pr′ ; i-above = Pre.above pr′
           ; i-exact = λ i → xch _ (cnt v i) (own es i) (held os i) (cnt w i)
                               (trans (snd x i) (cong (_+ cnt w i) (i-exact inv i)))
           ; i-sees = i-sees inv } )
  where
    pr : Pre h n v (λ i → own es i + held os i)
    pr = record { le1 = i-le1 inv ; above = i-above inv
                 ; sub = λ i → ≤-reflexive (sym (trans (i-exact inv i) (topᵒ es v os i))) }
    x = exchange run pr lent₀
    pr′ = post run pr (fst x) (snd x)
inv-stepI {h = h} (i-opend {s = s} {es = es} {x = x} {os = os} p) inv =
  ( op-OK p h
  , subst (Inv _ _) (sym (op-play p h))
      (same inv (λ i → cong (λ z → own es i + (z + held os i)) (cnt-flat (sdom s) x i)) (i-sees inv)) )
inv-stepI i-untag inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-untag₁ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-tag₁ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-case₁ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-case₂ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI (i-elend {es = es} {x = x} {a = a} {os = os}) inv =
  (tt , same inv (λ i → r (own es i) (cnt x i) (cnt a i) (held os i)) (see-own es (i-sees inv) , i-sees inv))
  where r : ∀ O X A H → O + ((X + A) + H) ≡ (X + O) + (A + H)
        r = solve-∀
inv-stepI (i-eunlend {es = es} {x = x} {w = w} {os = os}) inv =
  (tt , same inv (λ i → r (own es i) (cnt x i) (cnt w i) (held os i)) (snd (i-sees inv)))
  where r : ∀ O X W H → (X + O) + (W + H) ≡ O + ((X + W) + H)
        r = solve-∀
inv-stepI i-elift inv = (tt , same inv (λ i → refl) ((λ i ()) , i-sees inv))
inv-stepI (i-efst {e₁ = e₁} {e₂} {es} {os} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = e₁} _ eq (λ i p → ≤-trans p (m≤m+n (cnt e₁ i) (cnt e₂ i))) (i-sees inv) , i-sees inv))
inv-stepI (i-esnd {e₁ = e₁} {e₂} {es} {os} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = e₂} _ eq (λ i p → ≤-trans p (m≤n+m (cnt e₂ i) (cnt e₁ i))) (i-sees inv) , i-sees inv))
inv-stepI {h = h} (i-eout {i = j} {v} {es} {os} eq) inv =
  ( (≤-antisym (i-le1 inv j) alive , tt)
  , same inv (λ i → refl) (inside es {x = v} _ eq (λ i p → ≤-trans p (m≤n+m (cnt v i) (δ j i))) (i-sees inv) , i-sees inv) )
  where
    seen : 1 ≤ cnt (see es) j
    seen = subst (λ z → 1 ≤ cnt z j) (sym eq) (subst (λ d → 1 ≤ d + cnt v j) (sym (δ-same j)) (s≤s z≤n))
    alive : 1 ≤ h j
    alive = subst (1 ≤_) (sym (i-exact inv j)) (≤-trans (see-own es (i-sees inv) j seen) (m≤m+n (own es j) (held os j)))
inv-stepI (i-eoutq {i = j} {v} {es} {os} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = v} _ eq (λ i p → ≤-trans p (m≤n+m (cnt v i) (δ j i))) (i-sees inv) , i-sees inv))
inv-stepI (i-ecase₁ {e = e} {es} {os} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = e} _ eq (λ i p → p) (i-sees inv) , i-sees inv))
inv-stepI (i-ecase₂ {e = e} {es} {os} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = e} _ eq (λ i p → p) (i-sees inv) , i-sees inv))
inv-stepI (i-eapp {x = x} {es} {os} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = x} _ eq (λ i p → p) (i-sees inv) , i-sees inv))
inv-stepI i-epop inv = (tt , same inv (λ i → refl) (snd (i-sees inv)))
inv-stepI (i-eword _) inv = (tt , same inv (λ i → refl) (i-sees inv))
-- a call, a return, a loop's turn: no value moves (a frame is a temporary)
inv-stepI i-call inv = ((tt , tt) , inv)
inv-stepI i-ret  inv = ((tt , tt) , inv)
inv-stepI i-reti inv = (tt , inv)
inv-stepI i-loop inv = (tt , inv)
-- ★ through a cell's code word
inv-stepI (i-icall {es = es} {i = j} {x} {a} {os}) inv =
  freed j inv (λ i → r (own es i) (δ j i) (cnt x i) (cnt a i) (held os i)) (i-sees inv)
  where r : ∀ O D X A H → O + (((D + X) + A) + H) ≡ D + (O + ((X + A) + H))
        r = solve-∀
inv-stepI {h = h} (i-icallω {i = j} {x} {es} {os} eq) inv =
  ( (≤-antisym (i-le1 inv j) alive , tt)
  , same inv (λ i → refl) (inside es {x = x} _ eq (λ i p → ≤-trans p (m≤n+m (cnt x i) (δ j i))) (i-sees inv) , i-sees inv) )
  where
    seen : 1 ≤ cnt (see es) j
    seen = subst (λ z → 1 ≤ cnt z j) (sym eq) (subst (λ d → 1 ≤ d + cnt x j) (sym (δ-same j)) (s≤s z≤n))
    alive : 1 ≤ h j
    alive = subst (1 ≤_) (sym (i-exact inv j)) (≤-trans (see-own es (i-sees inv) j seen) (m≤m+n (own es j) (held os j)))
inv-stepI (i-iobs {es = es} {i = j} {p} {os}) inv =
  freed j inv (λ i → r (own es i) (δ j i) (cnt p i) (held os i)) (i-sees inv)
  where r : ∀ O D P H → O + ((D + P) + H) ≡ D + (O + (P + H))
        r = solve-∀
inv-stepI (i-ccopy1 {i = j} {x} {es} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = x} _ eq (λ i p → ≤-trans p (m≤n+m (cnt x i) (δ j i))) (i-sees inv) , i-sees inv))
inv-stepI (i-ccopyω {i = j} {x} {es} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = x} _ eq (λ i p → ≤-trans p (m≤n+m (cnt x i) (δ j i))) (i-sees inv) , i-sees inv))
inv-stepI (i-ncopy {i = j} {p} {es} eq) inv =
  (tt , same inv (λ i → refl) (inside es {x = p} _ eq (λ i q → ≤-trans q (m≤n+m (cnt p i) (δ j i))) (i-sees inv) , i-sees inv))
inv-stepI (i-cfree {es = es} {i = j} {x = x} {os}) inv =
  freed j inv (λ i → r (own es i) (δ j i) (cnt x i) (held os i)) (i-sees inv)
  where r : ∀ O D X H → O + ((D + X) + H) ≡ D + (O + (X + H))
        r = solve-∀
inv-stepI (i-nfree {es = es} {i = j} {p} {os}) inv =
  freed j inv (λ i → r (own es i) (δ j i) (cnt p i) (held os i)) (i-sees inv)
  where r : ∀ O D P H → O + ((D + P) + H) ≡ D + (O + (P + H))
        r = solve-∀

-- along a stretch of steps
inv-stepsI : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t h}
           → StepsI c r m n t c′ r′ m′ n′ → Inv m n h → OK t h × Inv m′ n′ (play t h)
inv-stepsI done inv = (tt , inv)
inv-stepsI {m′ = m′} {n′ = n′} {h = h} (_⟫_ {t₁ = t₁} {t₂} x st) inv with inv-stepI x inv
... | (ok₁ , inv₁) with inv-stepsI st inv₁
...   | (ok₂ , inv₂) = (OK-++ t₁ t₂ h ok₁ ok₂ , subst (Inv m′ n′) (sym (play-++ t₁ t₂ h)) inv₂)

-- ★ D410 amended, on the image: at every configuration a closed program's
-- image reaches, whatever its code, every event so far was legal and the
-- live cells are exactly the cells of the values it holds
held-alwaysI : ∀ {T sh U U₀} {c : Codeᴵ (One ∷ [] ∣ One ∷ []) U₀} {r : Ret U₀ T} {c′ : Codeᴵ sh U} {r′ : Ret U T} {m′ n′ mt}
             → StepsI c r start 0 mt c′ r′ m′ n′
             → OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ Owned m′ i)
held-alwaysI st with inv-stepsI st start-inv
... | (ok , inv) = (ok , i-exact inv)
