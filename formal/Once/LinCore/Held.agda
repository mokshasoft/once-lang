-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Held — plan 0.146 A16 (D410 amended): NO LEAK AS A SAFETY CLAIM.
--
-- What a configuration of the machine HOLDS: its operands, and the value each
-- lend's slot keeps until it hands it back (`ln`). The other slots are views,
-- and own nothing.
--
-- ★ `held-always`: from a closed program's start, at EVERY configuration the
-- machine reaches, every event so far was legal (no double free, no free or
-- read of a dead cell) and the live cells are EXACTLY the cells of the values
-- it holds. No garbage at any step, so a server's state is live data, not a
-- leak, and a finished run, holding nothing, has freed everything.
--
-- It holds of ANY code, not only compiled code: the instruction set is linear.
-- Only a `dup` or an `ecopy` makes a second value, by allocating; only a
-- `drop` or a fold's node ends one, by freeing; a view is opened and closed
-- with no event, and `eunlend` hands the lent value back to the operands.
--
-- Frames (temporaries) are outside the claim's cells: the simulation shows
-- each is freed by the `leave` its `enter` is matched with (`Machine.framed`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-antisym; m≤m+n; m≤n+m; m∸n≤m; 0∸n≡0; +-comm; suc-injective)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base; FTy)

module Once.LinCore.Held
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw

------------------------------------------------------------------------
-- 1. WHAT A CONFIGURATION HOLDS.
------------------------------------------------------------------------

-- the slots own the values lent beside a view
own : ∀ {Es} → Slots Es → Heap
own []ᵉ         i = 0
own (vw e es)   i = own es i
own (ln e x es) i = cnt x i + own es i

held : ∀ {S} → Stk S → Heap
held []ˢ       i = 0
held (v ∷ˢ os) i = cnt v i + held os i

Owned : ∀ {sh} → Cfg sh → Heap
Owned (es ∥ os) i = own es i + held os i

-- every cell of `V` is one of `W`'s
Within : Heap → Heap → Set
Within V W = ∀ i → 1 ≤ V i → 1 ≤ W i

-- a slot sees only cells owned below it
Sees : ∀ {Es} → Slots Es → Set
Sees []ᵉ         = ⊤
Sees (vw e es)   = Within (cnt e) (own es) × Sees es
Sees (ln e x es) = Within (cnt e) (own es) × Sees es

private
  split : ∀ a {b c} → (1 ≤ a → 1 ≤ c) → 1 ≤ a + b → 1 ≤ b + c
  split zero    {b} {c} f l = ≤-trans l (m≤m+n b c)
  split (suc a) {b} {c} f l = ≤-trans (f (s≤s z≤n)) (m≤n+m c b)

  cancelˡ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
  cancelˡ zero    e = e
  cancelˡ (suc c) e = cancelˡ c (suc-injective e)

  cancelʳ : ∀ c {a b} → a + c ≡ b + c → a ≡ b
  cancelʳ c {a} {b} e = cancelˡ c (trans (+-comm c a) (trans e (+-comm b c)))

-- the top slot's view is owned below or by it
see-own : ∀ {E Es} (es : Slots (E ∷ Es)) → Sees es → Within (cnt (see es)) (own es)
see-own (vw e es)   (w , _) = w
see-own (ln e x es) (w , _) i p = split (cnt e i) (w i) p

------------------------------------------------------------------------
-- 2. THE INVARIANT, step by step.
------------------------------------------------------------------------

record Inv {sh} (m : Cfg sh) (n : ℕ) (h : Heap) : Set where
  field
    i-le1   : ∀ i → h i ≤ 1
    i-above : ∀ i → n ≤ serial i → h i ≡ 0
    i-exact : ∀ i → h i ≡ Owned m i
    i-sees  : Sees (Cfg.envs m)
open Inv

private
  -- the same cells, held otherwise
  same : ∀ {sh sh′} {m : Cfg sh} {m′ : Cfg sh′} {n h} → Inv m n h
       → (∀ i → Owned m i ≡ Owned m′ i) → Sees (Cfg.envs m′) → Inv m′ n h
  same inv e s = record { i-le1 = i-le1 inv ; i-above = i-above inv
                        ; i-exact = λ i → trans (i-exact inv i) (e i) ; i-sees = s }

  -- the top operand beside everything else held
  top : ∀ {Es A S} (es : Slots Es) (v : MV A) (os : Stk S) i
      → own es i + (cnt v i + held os i) ≡ cnt v i + (own es i + held os i)
  top es v os i = r (own es i) (cnt v i) (held os i)
    where r : ∀ O V H → O + (V + H) ≡ V + (O + H)
          r = solve-∀

  -- an exchange of the top operand `V` for `W`
  xch : ∀ P V O H W → P + V ≡ (O + (V + H)) + W → P ≡ O + (W + H)
  xch P V O H W e = cancelʳ V (trans e (r O V H W))
    where r : ∀ O V H W → (O + (V + H)) + W ≡ (O + (W + H)) + V
          r = solve-∀

inv-step : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t h}
         → Step c m n t c′ m′ n′ → Inv m n h → OK t h × Inv m′ n′ (play t h)
inv-step {m = es ∥ mpair a b ∷ˢ os} s-unpair inv =
  (tt , same inv (λ i → cong (own es i +_) (r (cnt a i) (cnt b i) (held os i))) (i-sees inv))
  where r : ∀ A B H → (A + B) + H ≡ A + (B + H)
        r = solve-∀
inv-step {m = es ∥ a ∷ˢ b ∷ˢ os} s-pair inv =
  (tt , same inv (λ i → cong (own es i +_) (r (cnt a i) (cnt b i) (held os i))) (i-sees inv))
  where r : ∀ A B H → A + (B + H) ≡ (A + B) + H
        r = solve-∀
inv-step {m = es ∥ a ∷ˢ b ∷ˢ os} s-swap inv =
  (tt , same inv (λ i → cong (own es i +_) (r (cnt a i) (cnt b i) (held os i))) (i-sees inv))
  where r : ∀ A B H → A + (B + H) ≡ B + (A + H)
        r = solve-∀
inv-step {m = es ∥ v ∷ˢ os} {n = n} {h = h} (s-prim {w = w} run) inv =
  ( fst x
  , record { i-le1 = Pre.le1 pr′ ; i-above = Pre.above pr′
           ; i-exact = λ i → xch _ (cnt v i) (own es i) (held os i) (cnt w i)
                               (trans (snd x i) (cong (_+ cnt w i) (i-exact inv i)))
           ; i-sees = i-sees inv } )
  where
    pr : Pre h n v (λ i → own es i + held os i)
    pr = record { le1 = i-le1 inv ; above = i-above inv
                 ; sub = λ i → ≤-reflexive (sym (trans (i-exact inv i) (top es v os i))) }
    x = exchange run pr lent₀
    pr′ = post run pr (fst x) (snd x)
inv-step s-untag inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-step s-enter inv = ((tt , tt) , inv)
inv-step s-leave inv = ((tt , tt) , inv)
inv-step s-case₁ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-step s-case₂ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-step {m = es ∥ mpair x a ∷ˢ os} s-elend inv =
  (tt , same inv (λ i → r (own es i) (cnt x i) (cnt a i) (held os i)) (see-own es (i-sees inv) , i-sees inv))
  where r : ∀ O X A H → O + ((X + A) + H) ≡ (X + O) + (A + H)
        r = solve-∀
inv-step {m = ln e x es ∥ w ∷ˢ os} s-eunlend inv =
  (tt , same inv (λ i → r (own es i) (cnt x i) (cnt w i) (held os i)) (snd (i-sees inv)))
  where r : ∀ O X W H → (X + O) + (W + H) ≡ O + ((X + W) + H)
        r = solve-∀
inv-step s-elift inv = (tt , same inv (λ i → refl) ((λ i ()) , i-sees inv))
inv-step {m = es ∥ os} (s-efst {e₁ = e₁} {e₂} eq) inv =
  (tt , same inv (λ i → refl)
          ((λ i p → see-own es (i-sees inv) i (subst (λ z → 1 ≤ cnt z i) (sym eq) (≤-trans p (m≤m+n (cnt e₁ i) (cnt e₂ i)))))
          , i-sees inv))
inv-step {m = es ∥ os} (s-esnd {e₁ = e₁} {e₂} eq) inv =
  (tt , same inv (λ i → refl)
          ((λ i p → see-own es (i-sees inv) i (subst (λ z → 1 ≤ cnt z i) (sym eq) (≤-trans p (m≤n+m (cnt e₂ i) (cnt e₁ i)))))
          , i-sees inv))
inv-step {m = es ∥ os} {h = h} (s-eout {i = j} {v} eq) inv =
  ( (≤-antisym (i-le1 inv j) alive , tt)
  , same inv (λ i → refl)
      ((λ i p → see-own es (i-sees inv) i (subst (λ z → 1 ≤ cnt z i) (sym eq) (≤-trans p (m≤n+m (cnt v i) (δ j i)))))
      , i-sees inv) )
  where
    seen : 1 ≤ cnt (see es) j
    seen = subst (λ z → 1 ≤ cnt z j) (sym eq) (subst (λ d → 1 ≤ d + cnt v j) (sym (δ-same j)) (s≤s z≤n))
    alive : 1 ≤ h j
    alive = subst (1 ≤_) (sym (i-exact inv j)) (≤-trans (see-own es (i-sees inv) j seen) (m≤m+n (own es j) (held os j)))
inv-step {m = es ∥ os} (s-ecase₁ eq) inv =
  (tt , same inv (λ i → refl) ((λ i p → see-own es (i-sees inv) i (subst (λ z → 1 ≤ cnt z i) (sym eq) p)) , i-sees inv))
inv-step {m = es ∥ os} (s-ecase₂ eq) inv =
  (tt , same inv (λ i → refl) ((λ i p → see-own es (i-sees inv) i (subst (λ z → 1 ≤ cnt z i) (sym eq) p)) , i-sees inv))
inv-step {m = es ∥ os} (s-eapp eq) inv =
  (tt , same inv (λ i → refl) ((λ i p → see-own es (i-sees inv) i (subst (λ z → 1 ≤ cnt z i) (sym eq) p)) , i-sees inv))
inv-step s-epop inv = (tt , same inv (λ i → refl) (snd (i-sees inv)))
inv-step {m = es ∥ mone ∷ˢ os} {n = n} {h = h} s-ecopy inv =
  ( ok
  , record { i-le1   = OK-le1 _ h ok (i-le1 inv)
           ; i-above = λ i le → trans (eq i) (cong₂′ (i-above inv i (≤-trans (copy-mono (see es) n) le))
                                                     (copy-below (see es) n i le))
           ; i-exact = λ i → trans (eq i) (trans (cong (_+ cnt (fst (copy (see es) n)) i) (i-exact inv i))
                                                 (r (own es i) (held os i) (cnt (fst (copy (see es) n)) i)))
           ; i-sees  = i-sees inv } )
  where
    ok = fst (copy-ok (see es) n h (i-above inv))
    eq = snd (copy-ok (see es) n h (i-above inv))
    r : ∀ O H C → (O + (0 + H)) + C ≡ O + (C + H)
    r = solve-∀
    cong₂′ : ∀ {a b} → a ≡ 0 → b ≡ 0 → a + b ≡ 0
    cong₂′ refl refl = refl
inv-step {m = es ∥ x ∷ˢ os} {h = h} (s-opend {s = s} p) inv =
  ( op-OK p h
  , subst (Inv _ _) (sym (op-play p h))
      (same inv (λ i → cong (λ z → own es i + (z + held os i)) (cnt-flat (sdom s) x i)) (i-sees inv)) )
inv-step {m = es ∥ mmu j v ∷ˢ os} {h = h} s-fold inv =
  ( (fst fr , tt)
  , record { i-le1   = fst (snd fr)
           ; i-above = λ i le → trans (cong (_∸ δ j i) (i-above inv i le)) (0∸n≡0 (δ j i))
           ; i-exact = λ i → cancelʳ (δ j i) (trans (snd (snd (snd fr)) i)
                                                    (trans (i-exact inv i) (r₂ (own es i) (δ j i) (cnt v i) (held os i))))
           ; i-sees  = i-sees inv } )
  where
    r₁ : ∀ O D V H → O + ((D + V) + H) ≡ (D + V) + (O + H)
    r₁ = solve-∀
    r₂ : ∀ O D V H → O + ((D + V) + H) ≡ (O + (V + H)) + D
    r₂ = solve-∀
    fr = free-step j (cnt v) h (λ i → own es i + held os i) (i-le1 inv)
           (λ i → ≤-reflexive (sym (trans (i-exact inv i) (r₁ (own es i) (δ j i) (cnt v i) (held os i)))))
inv-step s-loop inv = (tt , inv)
-- ★ D409 part 3: the indirect call frees the closure's cell; its environment
-- and the argument stay held, as the body's input
inv-step {m = es ∥ mpair (mfn j _ x) a ∷ˢ os} {h = h} s-apply inv =
  ( (fst fr , tt)
  , record { i-le1   = fst (snd fr)
           ; i-above = λ i le → trans (cong (_∸ δ j i) (i-above inv i le)) (0∸n≡0 (δ j i))
           ; i-exact = λ i → cancelʳ (δ j i) (trans (snd (snd (snd fr)) i)
                                                    (trans (i-exact inv i) (r₂ (own es i) (δ j i) (cnt x i) (cnt a i) (held os i))))
           ; i-sees  = i-sees inv } )
  where
    r₁ : ∀ O D X A H → O + (((D + X) + A) + H) ≡ (D + (X + A)) + (O + H)
    r₁ = solve-∀
    r₂ : ∀ O D X A H → O + (((D + X) + A) + H) ≡ (O + ((X + A) + H)) + D
    r₂ = solve-∀
    fr = free-step j (λ i → cnt x i + cnt a i) h (λ i → own es i + held os i) (i-le1 inv)
           (λ i → ≤-reflexive (sym (trans (i-exact inv i) (r₁ (own es i) (δ j i) (cnt x i) (cnt a i) (held os i)))))
-- ★ observing a ν frees its cell; its coalgebra and seed stay held
inv-step {m = es ∥ mnu j p ∷ˢ os} {h = h} s-nopen inv =
  ( (fst fr , tt)
  , record { i-le1   = fst (snd fr)
           ; i-above = λ i le → trans (cong (_∸ δ j i) (i-above inv i le)) (0∸n≡0 (δ j i))
           ; i-exact = λ i → cancelʳ (δ j i) (trans (snd (snd (snd fr)) i)
                                                    (trans (i-exact inv i) (r₂ (own es i) (δ j i) (cnt p i) (held os i))))
           ; i-sees  = i-sees inv } )
  where
    r₁ : ∀ O D V H → O + ((D + V) + H) ≡ (D + V) + (O + H)
    r₁ = solve-∀
    r₂ : ∀ O D V H → O + ((D + V) + H) ≡ (O + (V + H)) + D
    r₂ = solve-∀
    fr = free-step j (cnt p) h (λ i → own es i + held os i) (i-le1 inv)
           (λ i → ≤-reflexive (sym (trans (i-exact inv i) (r₁ (own es i) (δ j i) (cnt p i) (held os i)))))
-- a lent closure's cell is read; its environment is viewed, owned below
inv-step {m = es ∥ os} {h = h} (s-eapply {i = j} {x} eq) inv =
  ( (≤-antisym (i-le1 inv j) alive , tt)
  , same inv (λ i → refl)
      ((λ i p → see-own es (i-sees inv) i (subst (λ z → 1 ≤ cnt z i) (sym eq) (≤-trans p (m≤n+m (cnt x i) (δ j i)))))
      , i-sees inv) )
  where
    seen : 1 ≤ cnt (see es) j
    seen = subst (λ z → 1 ≤ cnt z j) (sym eq) (subst (λ d → 1 ≤ d + cnt x j) (sym (δ-same j)) (s≤s z≤n))
    alive : 1 ≤ h j
    alive = subst (1 ≤_) (sym (i-exact inv j)) (≤-trans (see-own es (i-sees inv) j seen) (m≤m+n (own es j) (held os j)))

-- along a stretch of steps
inv-steps : ∀ {T sh sh′} {c : Code sh T} {c′ : Code sh′ T} {m m′ n n′ t h}
          → Steps c m n t c′ m′ n′ → Inv m n h → OK t h × Inv m′ n′ (play t h)
inv-steps done inv = (tt , inv)
inv-steps {m′ = m′} {n′ = n′} {h = h} (_⟫_ {t₁ = t₁} {t₂} x st) inv with inv-step x inv
... | (ok₁ , inv₁) with inv-steps st inv₁
...   | (ok₂ , inv₂) = (OK-++ t₁ t₂ h ok₁ ok₂ , subst (Inv m′ n′) (sym (play-++ t₁ t₂ h)) inv₂)

------------------------------------------------------------------------
-- 3. ★ THE CLAIM.
------------------------------------------------------------------------

start-inv : Inv start 0 (λ _ → 0)
start-inv = record { i-le1 = λ _ → z≤n ; i-above = λ _ _ → refl ; i-exact = λ _ → refl
                   ; i-sees = ((λ i ()) , tt) }

-- ★ D410 amended: at every configuration a closed program's machine reaches,
-- whatever its code, every event so far was legal and the live cells are
-- exactly the cells of the values it holds
held-always : ∀ {T sh} {c : Code (One ∷ [] ∣ One ∷ []) T} {c′ : Code sh T} {m′ n′ mt}
            → Steps c start 0 mt c′ m′ n′
            → OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ Owned m′ i)
held-always st with inv-steps st start-inv
... | (ok , inv) = (ok , i-exact inv)
