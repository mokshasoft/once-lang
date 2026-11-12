-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.HeldI — plan 0.146 B1.4a: D410 amended, on the image.
--
-- A16's `Held.held-always` for the finite-code image: at every configuration
-- a closed program's image reaches, whatever its code, every event so far
-- was legal and the live cells are exactly the cells of the values it holds:
-- the current frame's and every saved frame's (D415: a call opens a frame of
-- its own, the caller's configuration saved on the return stack).
--
-- A16's invariant (`Held.Inv`), spanning the frames (`InvI`): a view sees
-- cells owned by the slots below it, in its frame or in its callers' (a
-- callee's top view is its caller's). Each new step is one of four kinds: a
-- call saves the caller's configuration below its top view and argument, a
-- return puts the result back on it, a loop's turn moves nothing; a copy's
-- dispatch opens a view owned below (as `eapply`); a free's dispatch frees
-- the cell and holds what it held (`freed`, as `apply`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-antisym; m≤m+n; m≤n+m; 0∸n≡0; +-comm; +-identityʳ; suc-injective; +-mono-≤)
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
open import Once.LinCore.Held fmt ans bw using (own; held; Owned; Within)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_; start)

------------------------------------------------------------------------
-- 1. THE FRAMES: what the saved frames hold, what their slots own.
------------------------------------------------------------------------

-- the cells the saved frames hold
OwnR : ∀ {U T} → Ret U T → Heap
OwnR []ʳ              i = 0
OwnR (frm k es os r)  i = (own es i + held os i) + OwnR r i
OwnR (k ∷ⁱ r)         i = OwnR r i

-- the cells the saved frames' slots own: what a callee's views may see
EnvR : ∀ {U T} → Ret U T → Heap
EnvR []ʳ              i = 0
EnvR (frm k es os r)  i = own es i + EnvR r i
EnvR (k ∷ⁱ r)         i = EnvR r i

-- a slot sees only cells owned below it, in its frame or by the frames
-- below (`O`)
Sees′ : ∀ {Es} → Heap → Slots Es → Set
Sees′ O []ᵉ         = ⊤
Sees′ O (vw e es)   = Within (cnt e) (λ i → own es i + O i) × Sees′ O es
Sees′ O (ln e x es) = Within (cnt e) (λ i → own es i + O i) × Sees′ O es

-- every saved frame's slots, likewise
SeesR : ∀ {U T} → Ret U T → Set
SeesR []ʳ             = ⊤
SeesR (frm k es os r) = Sees′ (EnvR r) es × SeesR r
SeesR (k ∷ⁱ r)        = SeesR r

private
  split : ∀ a {b c} → (1 ≤ a → 1 ≤ c) → 1 ≤ a + b → 1 ≤ b + c
  split zero    {b} {c} f l = ≤-trans l (m≤m+n b c)
  split (suc a) {b} {c} f l = ≤-trans (f (s≤s z≤n)) (m≤n+m c b)

  assoc : ∀ X O P → X + (O + P) ≡ (X + O) + P
  assoc = solve-∀

see-own′ : ∀ {E Es O} (es : Slots (E ∷ Es)) → Sees′ O es → Within (cnt (see es)) (λ i → own es i + O i)
see-own′ (vw e es)   (w , _) = w
see-own′ {O = O} (ln e x es) (w , _) i p =
  subst (1 ≤_) (assoc (cnt x i) (own es i) (O i)) (split (cnt e i) (w i) p)

-- the slots' cells are among the frames' cells
envR≤ : ∀ {U T} (r : Ret U T) i → EnvR r i ≤ OwnR r i
envR≤ []ʳ             i = z≤n
envR≤ (frm k es os r) i = +-mono-≤ (m≤m+n (own es i) (held os i)) (envR≤ r i)
envR≤ (k ∷ⁱ r)        i = envR≤ r i

-- a called block's frame: the caller's top view owns nothing
own-topv : ∀ t {Es} (es : Slots (t ⊳ Es)) i → own (topv t es) i ≡ 0
own-topv nothing  es i = refl
own-topv (just E) es i = refl

own-top0 : ∀ t (e : Slots (t ⊳ [])) i → own e i ≡ 0
own-top0 nothing  []ᵉ          i = refl
own-top0 (just E) (vw e []ᵉ)   i = refl

-- …and sees what the caller's top view saw
topv-sees : ∀ t {Es O} (es : Slots (t ⊳ Es)) → Sees′ O es → Sees′ (λ i → own es i + O i) (topv t es)
topv-sees nothing  es s = tt
topv-sees (just E) es s = see-own′ es s , tt

------------------------------------------------------------------------
-- 2. ★ THE INVARIANT, across the frames.
------------------------------------------------------------------------

record InvI {sh U T} (m : Cfg sh) (r : Ret U T) (n : ℕ) (h : Heap) : Set where
  field
    i-le1   : ∀ i → h i ≤ 1
    i-above : ∀ i → n ≤ serial i → h i ≡ 0
    i-exact : ∀ i → h i ≡ Owned m i + OwnR r i
    i-sees  : Sees′ (EnvR r) (Cfg.envs m)
    i-seesR : SeesR r
open InvI

private
  cancelˡ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
  cancelˡ zero    e = e
  cancelˡ (suc c) e = cancelˡ c (suc-injective e)

  cancelʳ : ∀ c {a b} → a + c ≡ b + c → a ≡ b
  cancelʳ c {a} {b} e = cancelˡ c (trans (+-comm c a) (trans e (+-comm b c)))

  -- the same cells, held otherwise in the current frame
  same : ∀ {sh sh′ U T} {m : Cfg sh} {m′ : Cfg sh′} {r : Ret U T} {n h} → InvI m r n h
       → (∀ i → Owned m i ≡ Owned m′ i) → Sees′ (EnvR r) (Cfg.envs m′) → InvI m′ r n h
  same {r = r} inv e s = record { i-le1 = i-le1 inv ; i-above = i-above inv
                                ; i-exact = λ i → trans (i-exact inv i) (cong (_+ OwnR r i) (e i))
                                ; i-sees = s ; i-seesR = i-seesR inv }

  -- ★ a cell `j` freed, all else held: the invariant at what is held after
  freed : ∀ {sh sh′ U T} {m : Cfg sh} {m′ : Cfg sh′} {r : Ret U T} {n h} j → InvI m r n h
        → (∀ i → Owned m i ≡ δ j i + Owned m′ i) → Sees′ (EnvR r) (Cfg.envs m′)
        → OK (free j ∷ []) h × InvI m′ r n (play (free j ∷ []) h)
  freed {m = m} {m′ = m′} {r = r} {h = h} j inv e s =
    ( (fst fr , tt)
    , record { i-le1   = fst (snd fr)
             ; i-above = λ i le → trans (cong (_∸ δ j i) (i-above inv i le)) (0∸n≡0 (δ j i))
             ; i-exact = λ i → cancelʳ (δ j i) (trans (snd (snd (snd fr)) i) (trans (hx i) (rr (δ j i) (Owned m′ i) (OwnR r i))))
             ; i-sees  = s ; i-seesR = i-seesR inv } )
    where
      hx : ∀ i → h i ≡ (δ j i + Owned m′ i) + OwnR r i
      hx i = trans (i-exact inv i) (cong (_+ OwnR r i) (e i))
      rr : ∀ D O R → (D + O) + R ≡ (O + R) + D
      rr = solve-∀
      fr = free-step j (Owned m′) h (OwnR r) (i-le1 inv) (λ i → ≤-reflexive (sym (hx i)))

  topᵒ : ∀ {Es A S} (es : Slots Es) (v : MV A) (os : Stk S) R i
      → (own es i + (cnt v i + held os i)) + R ≡ cnt v i + ((own es i + held os i) + R)
  topᵒ es v os R i = r (own es i) (cnt v i) (held os i) R
    where r : ∀ O V H R → (O + (V + H)) + R ≡ V + ((O + H) + R)
          r = solve-∀

  xch : ∀ P V O H R W → P + V ≡ ((O + (V + H)) + R) + W → P ≡ (O + (W + H)) + R
  xch P V O H R W e = cancelʳ V (trans e (r O V H R W))
    where r : ∀ O V H R W → ((O + (V + H)) + R) + W ≡ ((O + (W + H)) + R) + V
          r = solve-∀

  -- a view of what the top view's cell holds: owned below
  inside : ∀ {E Es X O} (es : Slots (E ∷ Es)) {x : MV X} (v : MV E) → see es ≡ v
         → (∀ i → 1 ≤ cnt x i → 1 ≤ cnt v i) → Sees′ O es → Within (cnt x) (λ i → own es i + O i)
  inside es v eq sub s i p = see-own′ es s i (subst (λ z → 1 ≤ cnt z i) (sym eq) (sub i p))

  -- what the top view sees is live
  alive : ∀ {E Es S U T} (es : Slots (E ∷ Es)) (os : Stk S) (r : Ret U T) {n h} → InvI (es ∥ os) r n h
        → ∀ j → 1 ≤ cnt (see es) j → 1 ≤ h j
  alive es os r inv j seen =
    subst (1 ≤_) (sym (i-exact inv j))
      (≤-trans (see-own′ es (i-sees inv) j seen) (+-mono-≤ (m≤m+n (own es j) (held os j)) (envR≤ r j)))

------------------------------------------------------------------------
-- 3. ★ THE INVARIANT, step by step (A16's, and the image's own steps).
------------------------------------------------------------------------

inv-stepI : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t h}
          → StepI c r m n t c′ r′ m′ n′ → InvI m r n h → OK t h × InvI m′ r′ n′ (play t h)
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
inv-stepI {r = r} {n = n} {h = h} (i-prim {es = es} {v = v} {w = w} {os = os} run) inv =
  ( fst x
  , record { i-le1 = Pre.le1 pr′ ; i-above = Pre.above pr′
           ; i-exact = λ i → xch _ (cnt v i) (own es i) (held os i) (OwnR r i) (cnt w i)
                               (trans (snd x i) (cong (_+ cnt w i) (i-exact inv i)))
           ; i-sees = i-sees inv ; i-seesR = i-seesR inv } )
  where
    pr : Pre h n v (λ i → (own es i + held os i) + OwnR r i)
    pr = record { le1 = i-le1 inv ; above = i-above inv
                 ; sub = λ i → ≤-reflexive (sym (trans (i-exact inv i) (topᵒ es v os (OwnR r i) i))) }
    x = exchange run pr lent₀
    pr′ = post run pr (fst x) (snd x)
inv-stepI {r = r} {h = h} (i-opend {s = s} {es = es} {x = x} {os = os} p) inv =
  ( op-OK p h
  , subst (InvI _ r _) (sym (op-play p h))
      (same inv (λ i → cong (λ z → own es i + (z + held os i)) (cnt-flat (sdom s) x i)) (i-sees inv)) )
inv-stepI i-untag inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-untag₁ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-tag₁ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-case₁ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI i-case₂ inv = (tt , same inv (λ i → refl) (i-sees inv))
inv-stepI (i-elend {es = es} {x = x} {a = a} {os = os}) inv =
  (tt , same inv (λ i → r (own es i) (cnt x i) (cnt a i) (held os i)) (see-own′ es (i-sees inv) , i-sees inv))
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
inv-stepI {r = r} (i-eout {i = j} {v} {es} {os} eq) inv =
  ( (≤-antisym (i-le1 inv j) (alive es os r inv j seen) , tt)
  , same inv (λ i → refl) (inside es {x = v} _ eq (λ i p → ≤-trans p (m≤n+m (cnt v i) (δ j i))) (i-sees inv) , i-sees inv) )
  where
    seen : 1 ≤ cnt (see es) j
    seen = subst (λ z → 1 ≤ cnt z j) (sym eq) (subst (λ d → 1 ≤ d + cnt v j) (sym (δ-same j)) (s≤s z≤n))
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
-- ★ a call: the caller's configuration saved below its top view and the argument
inv-stepI {r = r} (i-call {σ = σ} {es = es} {a = a} {os = os}) inv =
  ( (tt , tt)
  , record { i-le1 = i-le1 inv ; i-above = i-above inv
           ; i-exact = λ i → trans (i-exact inv i) (e i)
           ; i-sees = topv-sees (top σ) es (i-sees inv) ; i-seesR = i-sees inv , i-seesR inv } )
  where
    rr : ∀ T O A H R → T ≡ 0 → (O + (A + H)) + R ≡ (T + (A + 0)) + ((O + H) + R)
    rr T O A H R refl = q O A H R
      where q : ∀ O A H R → (O + (A + H)) + R ≡ (0 + (A + 0)) + ((O + H) + R)
            q = solve-∀
    e = λ i → rr (own (topv (top σ) es) i) (own es i) (cnt a i) (held os i) (OwnR r i) (own-topv (top σ) es i)
-- ★ a return: the result put back on the caller's configuration
inv-stepI (i-ret {t = t} {r = r} {es = es} {os = os} {e′ = e′} {b = b}) inv =
  ( (tt , tt)
  , record { i-le1 = i-le1 inv ; i-above = i-above inv
           ; i-exact = λ i → trans (i-exact inv i) (rr (own e′ i) (own es i) (cnt b i) (held os i) (OwnR r i) (own-top0 t e′ i))
           ; i-sees = fst (i-seesR inv) ; i-seesR = snd (i-seesR inv) } )
  where
    rr : ∀ T O B H R → T ≡ 0 → (T + (B + 0)) + ((O + H) + R) ≡ (O + (B + H)) + R
    rr T O B H R refl = q O B H R
      where q : ∀ O B H R → (0 + (B + 0)) + ((O + H) + R) ≡ (O + (B + H)) + R
            q = solve-∀
-- a loop's turn: nothing moves
inv-stepI i-reti inv =
  (tt , record { i-le1 = i-le1 inv ; i-above = i-above inv ; i-exact = i-exact inv ; i-sees = i-sees inv ; i-seesR = i-seesR inv })
inv-stepI i-loop inv =
  (tt , record { i-le1 = i-le1 inv ; i-above = i-above inv ; i-exact = i-exact inv ; i-sees = i-sees inv ; i-seesR = i-seesR inv })
-- ★ through a cell's code word
inv-stepI (i-icall {es = es} {i = j} {x} {a} {os}) inv =
  freed j inv (λ i → r (own es i) (δ j i) (cnt x i) (cnt a i) (held os i)) (i-sees inv)
  where r : ∀ O D X A H → O + (((D + X) + A) + H) ≡ D + (O + ((X + A) + H))
        r = solve-∀
inv-stepI {r = r} (i-icallω {i = j} {x} {es} {os} eq) inv =
  ( (≤-antisym (i-le1 inv j) (alive es os r inv j seen) , tt)
  , same inv (λ i → refl) (inside es {x = x} _ eq (λ i p → ≤-trans p (m≤n+m (cnt x i) (δ j i))) (i-sees inv) , i-sees inv) )
  where
    seen : 1 ≤ cnt (see es) j
    seen = subst (λ z → 1 ≤ cnt z j) (sym eq) (subst (λ d → 1 ≤ d + cnt x j) (sym (δ-same j)) (s≤s z≤n))
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
           → StepsI c r m n t c′ r′ m′ n′ → InvI m r n h → OK t h × InvI m′ r′ n′ (play t h)
inv-stepsI done inv = (tt , inv)
inv-stepsI {r′ = r′} {m′ = m′} {n′ = n′} {h = h} (_⟫_ {t₁ = t₁} {t₂} x st) inv with inv-stepI x inv
... | (ok₁ , inv₁) with inv-stepsI st inv₁
...   | (ok₂ , inv₂) = (OK-++ t₁ t₂ h ok₁ ok₂ , subst (InvI m′ r′ n′) (sym (play-++ t₁ t₂ h)) inv₂)

start-invI : ∀ {T} → InvI start ([]ʳ {T = T}) 0 (λ _ → 0)
start-invI = record { i-le1 = λ _ → z≤n ; i-above = λ _ _ → refl ; i-exact = λ _ → refl
                    ; i-sees = ((λ i ()) , tt) ; i-seesR = tt }

-- ★ D410 amended, on the image: at every configuration a closed program's
-- image reaches, whatever its code, every event so far was legal and the
-- live cells are exactly the cells of the values it holds, in every frame
held-alwaysI : ∀ {T sh U} {c : Codeᴵ (One ∷ [] ∣ One ∷ []) T} {c′ : Codeᴵ sh U} {r′ : Ret U T} {m′ n′ mt}
             → StepsI c []ʳ start 0 mt c′ r′ m′ n′
             → OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ Owned m′ i + OwnR r′ i)
held-alwaysI st with inv-stepsI st start-invI
... | (ok , inv) = (ok , i-exact inv)
