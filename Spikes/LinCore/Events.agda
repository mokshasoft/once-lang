-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Events — plan 0.146 A3: what the linear core does to MEMORY.
--
-- `NbEPLinCore.Lᶜ` is a denotation with a cost count: values are Agda values
-- (a closure is an Agda function, a ν is an Agda coinductive record), and
-- nothing is ever freed because nothing is ever allocated. Here a value is
-- laid out the way D402's two heaps lay it out, and a run emits the cell
-- events it causes:
--
--   * FLAT (no cell; a frame slot or registers): `One`, `⊗t`, `⊕t`, base words.
--   * CELLS (the cell heap, one id each): a μ node, a ν suspension (its seed
--     and its coalgebra) or an observed ν layer, a closure (its environment).
--
-- `dup` copies every cell of its value (fresh ids); `drop` frees every cell of
-- its value; `lIn`/`lAna`/`lInν`/`lcurry` allocate one cell; `lOutμ`/`leval`
-- free one. Nothing else touches the heap: moving data is not copying it.
--
-- The run is a RELATION (`Run`), not a function: a closure stores its body as
-- syntax, and running it is not structurally smaller. The relation is checked
-- against `Lᶜ` (`sound`: a run computes the denotation), and the memory
-- theorem (`exchange`, the next stage) is about every run that exists.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m∸n≤m; m∸n+n≡m; n≤0⇒n≡0; ≤-antisym; m≤m+n; m≤n+m; <⇒≢)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (subst; _≢_)

module LinCore.Events (Base : Set) (⟦_⟧b : Base → Set) where

open import LinCore.NbEPLinCore Base ⟦_⟧b

------------------------------------------------------------------------
-- 1. MACHINE VALUES: a value as it sits in memory.
------------------------------------------------------------------------

Id : Set
Id = ℕ

data MV : LTy → Set where
  mone  : MV One
  mpair : ∀ {A B} → MV A → MV B → MV (A ⊗t B)
  minl  : ∀ {A B} → MV A → MV (A ⊕t B)
  minr  : ∀ {A B} → MV B → MV (A ⊕t B)
  mbase : ∀ {b} → ⟦ b ⟧b → MV (Bt b)
  -- a μ node: one cell holding its layer
  mmu   : ∀ {F} → Id → MV (LF∙ F (μt F)) → MV (μt F)
  -- a closure: one cell holding its environment (the body is code)
  mclo  : ∀ {E A B} → Id → MV E → LTm (E ⊗t A) B → MV (A ⇒t B)
  -- a ν not yet observed: one cell holding its seed (the coalgebra is code)
  mnu   : ∀ {S F} → Id → MV S → LTm S (LF∙ F S) → MV (νt F)
  -- a ν built from a layer (`lInν`): one cell holding the layer
  mnuv  : ∀ {F} → Id → MV (LF∙ F (νt F)) → MV (νt F)

-- what a machine value means
er : ∀ {A} → MV A → ⟦ A ⟧
er mone              = tt
er (mpair a b)       = (er a , er b)
er (minl a)          = inj₁ (er a)
er (minr b)          = inj₂ (er b)
er (mbase x)         = x
er (mmu {F} i v)     = inμ (coh F (μt F) (er v))
er (mclo i env f)    = λ a → Lᶜ f (er env , a)
er (mnu {F = F} i s c) = unfoldNu F c (er s)
er (mnuv {F} i v)    = inν (coh F (νt F) (er v))

------------------------------------------------------------------------
-- 2. EVENTS.
------------------------------------------------------------------------

data Ev : Set where
  alloc : Id → Ev
  free  : Id → Ev

Trace : Set
Trace = List Ev

-- `dup`: copy every cell, fresh ids from the counter
copy : ∀ {A} → MV A → ℕ → MV A × ℕ × Trace
copy mone          n = (mone , n , [])
copy (mpair a b)   n with copy a n
... | (a' , n₁ , t₁) with copy b n₁
...   | (b' , n₂ , t₂) = (mpair a' b' , n₂ , t₁ ++ t₂)
copy (minl a)      n with copy a n
... | (a' , n₁ , t₁) = (minl a' , n₁ , t₁)
copy (minr b)      n with copy b n
... | (b' , n₁ , t₁) = (minr b' , n₁ , t₁)
copy (mbase x)     n = (mbase x , n , [])
copy (mmu i v)     n with copy v (suc n)
... | (v' , n₁ , t₁) = (mmu n v' , n₁ , alloc n ∷ t₁)
copy (mclo i e f)  n with copy e (suc n)
... | (e' , n₁ , t₁) = (mclo n e' f , n₁ , alloc n ∷ t₁)
copy (mnu i s c)   n with copy s (suc n)
... | (s' , n₁ , t₁) = (mnu n s' c , n₁ , alloc n ∷ t₁)
copy (mnuv i v)    n with copy v (suc n)
... | (v' , n₁ , t₁) = (mnuv n v' , n₁ , alloc n ∷ t₁)

-- `drop`: free every cell
freeAll : ∀ {A} → MV A → Trace
freeAll mone         = []
freeAll (mpair a b)  = freeAll a ++ freeAll b
freeAll (minl a)     = freeAll a
freeAll (minr b)     = freeAll b
freeAll (mbase x)    = []
freeAll (mmu i v)    = free i ∷ freeAll v
freeAll (mclo i e f) = free i ∷ freeAll e
freeAll (mnu i s c)  = free i ∷ freeAll s
freeAll (mnuv i v)   = free i ∷ freeAll v

------------------------------------------------------------------------
-- 3. THE RUN (stage 1: everything but `lcata` and ν observation).
--
-- `Run f v n w n′ t`: `f` takes `v` to `w`; the ids `n … n′-1` are the fresh
-- ones it allocated; `t` is the events, in order.
------------------------------------------------------------------------

data Run : ∀ {A B} → LTm A B → MV A → ℕ → MV B → ℕ → Trace → Set where
  r-id    : ∀ {A} {v : MV A} {n} → Run lid v n v n []
  r-∘     : ∀ {A B C} {f : LTm B C} {g : LTm A B} {v u w n n₁ n₂ t₁ t₂}
          → Run g v n u n₁ t₁ → Run f u n₁ w n₂ t₂ → Run (f ∘l g) v n w n₂ (t₁ ++ t₂)
  r-⊗     : ∀ {A B C D} {f : LTm A B} {g : LTm C D} {a a′ b b′ n n₁ n₂ t₁ t₂}
          → Run f a n a′ n₁ t₁ → Run g b n₁ b′ n₂ t₂
          → Run (f ⊗l g) (mpair a b) n (mpair a′ b′) n₂ (t₁ ++ t₂)
  r-ρ     : ∀ {A} {a : MV A} {n} → Run ρl (mpair a mone) n a n []
  r-ρ⁻    : ∀ {A} {a : MV A} {n} → Run ρl⁻ a n (mpair a mone) n []
  r-λ     : ∀ {A} {a : MV A} {n} → Run lul (mpair mone a) n a n []
  r-λ⁻    : ∀ {A} {a : MV A} {n} → Run lul⁻ a n (mpair mone a) n []
  r-α     : ∀ {A B C} {a : MV A} {b : MV B} {c : MV C} {n}
          → Run lassoc (mpair (mpair a b) c) n (mpair a (mpair b c)) n []
  r-α⁻    : ∀ {A B C} {a : MV A} {b : MV B} {c : MV C} {n}
          → Run lassoc⁻ (mpair a (mpair b c)) n (mpair (mpair a b) c) n []
  r-swap  : ∀ {A B} {a : MV A} {b : MV B} {n} → Run lswap (mpair a b) n (mpair b a) n []
  r-dup   : ∀ {A} {v : MV A} {n} → Run dup v n (mpair v (fst (copy v n))) (fst (snd (copy v n))) (snd (snd (copy v n)))
  r-drop  : ∀ {A} {v : MV A} {n} → Run drop v n mone n (freeAll v)
  r-inl   : ∀ {A B} {a : MV A} {n} → Run (linl {A} {B}) a n (minl a) n []
  r-inr   : ∀ {A B} {b : MV B} {n} → Run (linr {A} {B}) b n (minr b) n []
  r-case₁ : ∀ {A B C} {f : LTm A C} {g : LTm B C} {a w n n′ t}
          → Run f a n w n′ t → Run (lcase f g) (minl a) n w n′ t
  r-case₂ : ∀ {A B C} {f : LTm A C} {g : LTm B C} {b w n n′ t}
          → Run g b n w n′ t → Run (lcase f g) (minr b) n w n′ t
  r-In    : ∀ {F} {v : MV (LF∙ F (μt F))} {n} → Run (lIn {F}) v n (mmu n v) (suc n) (alloc n ∷ [])
  r-Outμ  : ∀ {F} {v : MV (LF∙ F (μt F))} {i n} → Run (lOutμ {F}) (mmu i v) n v n (free i ∷ [])
  r-curry : ∀ {A B C} {f : LTm (A ⊗t B) C} {a : MV A} {n}
          → Run (lcurry f) a n (mclo n a f) (suc n) (alloc n ∷ [])
  r-eval  : ∀ {E A B} {f : LTm (E ⊗t A) B} {env : MV E} {a : MV A} {i w n n′ t}
          → Run f (mpair env a) n w n′ t → Run leval (mpair (mclo i env f) a) n w n′ (free i ∷ t)
  r-Ana   : ∀ {S F} {c : LTm S (LF∙ F S)} {s : MV S} {n}
          → Run (lAna F c) s n (mnu n s c) (suc n) (alloc n ∷ [])
  r-Inν   : ∀ {F} {v : MV (LF∙ F (νt F))} {n} → Run (lInν {F}) v n (mnuv n v) (suc n) (alloc n ∷ [])

------------------------------------------------------------------------
-- 4. SOUNDNESS: a run computes the denotation (`Lᶜ`'s value; its cost is
--    a different count and is not compared here).
------------------------------------------------------------------------

copy-er : ∀ {A} (v : MV A) n → er (fst (copy v n)) ≡ er v
copy-er mone         n = refl
copy-er (mpair a b)  n with copy a n | copy-er a n
... | (a' , n₁ , t₁) | ea with copy b n₁ | copy-er b n₁
...   | (b' , n₂ , t₂) | eb = cong₂ _,_ ea eb
copy-er (minl a)     n with copy a n | copy-er a n
... | (a' , n₁ , t₁) | ea = cong inj₁ ea
copy-er (minr b)     n with copy b n | copy-er b n
... | (b' , n₁ , t₁) | eb = cong inj₂ eb
copy-er (mbase x)    n = refl
copy-er (mmu {F} i v) n with copy v (suc n) | copy-er v (suc n)
... | (v' , n₁ , t₁) | ev = cong (λ x → inμ (coh F (μt F) x)) ev
copy-er (mclo i e f) n with copy e (suc n) | copy-er e (suc n)
... | (e' , n₁ , t₁) | ee = cong (λ x → λ a → Lᶜ f (x , a)) ee
copy-er (mnu {F = F} i s c) n with copy s (suc n) | copy-er s (suc n)
... | (s' , n₁ , t₁) | es = cong (unfoldNu F c) es
copy-er (mnuv {F} i v) n with copy v (suc n) | copy-er v (suc n)
... | (v' , n₁ , t₁) | ev = cong (λ x → inν (coh F (νt F) x)) ev

-- `lOutμ ∘ lIn` round trip at the denotation: `coh⁻¹ ∘ coh` is the identity
coh⁻¹∘coh : ∀ F X (x : ⟦ LF∙ F X ⟧) → coh⁻¹ F X (coh F X x) ≡ x
coh⁻¹∘coh Idf      X x        = refl
coh⁻¹∘coh Kone     X x        = refl
coh⁻¹∘coh (Kb b)   X x        = refl
coh⁻¹∘coh (Kμ G)   X x        = refl
coh⁻¹∘coh (Kν G)   X x        = refl
coh⁻¹∘coh (F ⊕f G) X (inj₁ x) = cong inj₁ (coh⁻¹∘coh F X x)
coh⁻¹∘coh (F ⊕f G) X (inj₂ y) = cong inj₂ (coh⁻¹∘coh G X y)
coh⁻¹∘coh (F ⊗f G) X (x , y)  = cong₂ _,_ (coh⁻¹∘coh F X x) (coh⁻¹∘coh G X y)

sound : ∀ {A B} {f : LTm A B} {v w n n′ t} → Run f v n w n′ t → er w ≡ fst (Lᶜ f (er v))
sound r-id = refl
sound (r-∘ {f = f} {v = v} rg rf) = trans (sound rf) (cong (λ x → fst (Lᶜ f x)) (sound rg))
sound (r-⊗ {f = f} {g = g} {a = a} {b = b} rf rg) = cong₂ _,_ (sound rf) (sound rg)
sound r-ρ    = refl
sound r-ρ⁻   = refl
sound r-λ    = refl
sound r-λ⁻   = refl
sound r-α    = refl
sound r-α⁻   = refl
sound r-swap = refl
sound (r-dup {v = v} {n}) = cong (er v ,_) (copy-er v n)
sound r-drop = refl
sound r-inl  = refl
sound r-inr  = refl
sound (r-case₁ r) = sound r
sound (r-case₂ r) = sound r
sound r-In   = refl
sound (r-Outμ {F} {v}) = sym (coh⁻¹∘coh F (μt F) (er v))
sound r-curry = refl
sound (r-eval r) = sound r
sound r-Ana  = refl
sound r-Inν  = refl

------------------------------------------------------------------------
-- 5. ★ THE MEMORY THEOREM (stage 2).
--
-- A heap counts, per id, the live cells with that id (a sound heap: 0 or 1).
-- `play t h` is the heap after the events `t`; `OK t h` says every event was
-- legal when it happened: an `alloc` of a dead id, a `free` of a live one (no
-- double free, no free of a stranger).
--
-- `exchange`: if the heap holds the input's cells (beside a frame `r`: the
-- cells of whatever else is live, which the run must not touch), every run's
-- events are legal, and afterwards the heap holds the OUTPUT's cells instead
-- of the input's, and nothing else changed. The frame is the separation-logic
-- frame rule; it is what makes `⊗l` compose.
--
-- `noleak`: a run of a whole program (`One → One`) from the empty heap ends
-- with the empty heap: every cell it allocated, it freed, exactly once.
------------------------------------------------------------------------

-- the arithmetic, local and small
private
  cancelˡ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
  cancelˡ zero    e = e
  cancelˡ (suc c) e = cancelˡ c (cong (λ { zero → zero ; (suc x) → x }) e)

  cancelʳ : ∀ c {a b} → a + c ≡ b + c → a ≡ b
  cancelʳ c {a} {b} e = cancelˡ c (trans (comm c a) (trans e (comm b c)))
    where comm : ∀ x y → x + y ≡ y + x
          comm = solve-∀

  ≤-cancelˡ : ∀ c {a b} → c + a ≤ c + b → a ≤ b
  ≤-cancelˡ zero    le       = le
  ≤-cancelˡ (suc c) (s≤s le) = ≤-cancelˡ c le

  ≤-cancelʳ : ∀ c {a b} → a + c ≤ b + c → a ≤ b
  ≤-cancelʳ c {a} {b} le = ≤-cancelˡ c (subst (_≤ c + b) (comm a c) (subst (a + c ≤_) (comm b c) le))
    where comm : ∀ x y → x + y ≡ y + x
          comm = solve-∀

  ≤-+ʳ : ∀ {a b} c → a ≤ b → a + c ≤ b + c
  ≤-+ʳ {a} {b} c le = subst₂′ (comm c a) (comm c b) (≤-+ˡ c le)
    where comm : ∀ x y → x + y ≡ y + x
          comm = solve-∀
          ≤-+ˡ : ∀ {a b} c → a ≤ b → c + a ≤ c + b
          ≤-+ˡ zero    le = le
          ≤-+ˡ (suc c) le = s≤s (≤-+ˡ c le)
          subst₂′ : ∀ {x x′ y y′} → x ≡ x′ → y ≡ y′ → x ≤ y → x′ ≤ y′
          subst₂′ refl refl le = le

  -- `m + k ≤ n` gives `k ≤ n ∸ m`
  sub-le : ∀ m {k n} → m + k ≤ n → k ≤ n ∸ m
  sub-le zero    le = le
  sub-le (suc m) {n = suc n} (s≤s le) = sub-le m le

  +≡0ˡ : ∀ m n → m + n ≡ 0 → m ≡ 0
  +≡0ˡ zero n e = refl
  +≡0ʳ : ∀ m n → m + n ≡ 0 → n ≡ 0
  +≡0ʳ zero n e = e

  ≤0 : ∀ {m} → m ≤ 0 → m ≡ 0
  ≤0 z≤n = refl

δ : Id → Id → ℕ
δ i j with i ≟ j
... | yes _ = 1
... | no  _ = 0

δ-same : ∀ i → δ i i ≡ 1
δ-same i with i ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

δ-≢ : ∀ {i j} → i ≢ j → δ i j ≡ 0
δ-≢ {i} {j} ne with i ≟ j
... | yes p = ⊥-elim (ne p)
... | no _  = refl

δ≤1 : ∀ i j → δ i j ≤ 1
δ≤1 i j with i ≟ j
... | yes _ = s≤s z≤n
... | no  _ = z≤n

-- a cell allocated at `n` is not at any id from `suc n` on
δ-fresh : ∀ {n i} → suc n ≤ i → δ n i ≡ 0
δ-fresh {n} {i} lt = δ-≢ (<⇒≢ lt)

cnt : ∀ {A} → MV A → Id → ℕ
cnt mone         i = 0
cnt (mpair a b)  i = cnt a i + cnt b i
cnt (minl a)     i = cnt a i
cnt (minr b)     i = cnt b i
cnt (mbase x)    i = 0
cnt (mmu j v)    i = δ j i + cnt v i
cnt (mclo j e f) i = δ j i + cnt e i
cnt (mnu j s c)  i = δ j i + cnt s i
cnt (mnuv j v)   i = δ j i + cnt v i

Heap : Set
Heap = Id → ℕ

step : Ev → Heap → Heap
step (alloc i) h j = h j + δ i j
step (free i)  h j = h j ∸ δ i j

play : Trace → Heap → Heap
play []      h = h
play (e ∷ t) h = play t (step e h)

OK : Trace → Heap → Set
OK []            h = ⊤
OK (alloc i ∷ t) h = h i ≡ 0 × OK t (step (alloc i) h)
OK (free i ∷ t)  h = h i ≡ 1 × OK t (step (free i) h)

play-++ : ∀ t₁ t₂ h → play (t₁ ++ t₂) h ≡ play t₂ (play t₁ h)
play-++ []       t₂ h = refl
play-++ (e ∷ t₁) t₂ h = play-++ t₁ t₂ (step e h)

OK-++ : ∀ t₁ t₂ h → OK t₁ h → OK t₂ (play t₁ h) → OK (t₁ ++ t₂) h
OK-++ []             t₂ h ok₁         ok₂ = ok₂
OK-++ (alloc i ∷ t₁) t₂ h (p , ok₁) ok₂ = (p , OK-++ t₁ t₂ _ ok₁ ok₂)
OK-++ (free i ∷ t₁)  t₂ h (p , ok₁) ok₂ = (p , OK-++ t₁ t₂ _ ok₁ ok₂)

-- legal events keep a heap sound
OK-le1 : ∀ t h → OK t h → (∀ i → h i ≤ 1) → ∀ i → play t h i ≤ 1
OK-le1 []            h ok        le = le
OK-le1 (alloc i ∷ t) h (p , ok) le = OK-le1 t _ ok le′
  where
    le′ : ∀ j → h j + δ i j ≤ 1
    le′ j with i ≟ j
    ... | yes refl = subst (λ x → x + 1 ≤ 1) (sym p) (s≤s z≤n)
    ... | no  _    = subst (_≤ 1) (sym (+0 (h j))) (le j)
      where +0 : ∀ x → x + 0 ≡ x
            +0 = solve-∀
OK-le1 (free i ∷ t)  h (p , ok) le = OK-le1 t _ ok (λ j → ≤-trans (m∸n≤m (h j) (δ i j)) (le j))

record Pre (h : Heap) (n : ℕ) {A} (v : MV A) (r : Heap) : Set where
  field
    le1   : ∀ i → h i ≤ 1
    above : ∀ i → n ≤ i → h i ≡ 0
    sub   : ∀ i → cnt v i + r i ≤ h i
open Pre

private
  +0 : ∀ x → x + 0 ≡ x
  +0 = solve-∀
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc = solve-∀
  comm : ∀ a b → a + b ≡ b + a
  comm = solve-∀

  -- two exchanges in a row are one
  chain : ∀ P U H₁ W V H → P + U ≡ H₁ + W → H₁ + V ≡ H + U → P + V ≡ H + W
  chain P U H₁ W V H e₁ e₂ = cancelʳ U (begin′)
    where
      r1 : ∀ P V U → (P + V) + U ≡ (P + U) + V
      r1 = solve-∀
      r2 : ∀ H₁ W V → (H₁ + W) + V ≡ (H₁ + V) + W
      r2 = solve-∀
      r3 : ∀ H U W → (H + U) + W ≡ (H + W) + U
      r3 = solve-∀
      begin′ : (P + V) + U ≡ (H + W) + U
      begin′ = trans (r1 P V U) (trans (cong (_+ V) e₁) (trans (r2 H₁ W V) (trans (cong (_+ W) e₂) (r3 H U W))))

  -- the halves of a pair, exchanged one after the other
  chain⊗ : ∀ P B H₁ B′ A H A′ → P + B ≡ H₁ + B′ → H₁ + A ≡ H + A′ → P + (A + B) ≡ H + (A′ + B′)
  chain⊗ P B H₁ B′ A H A′ e₁ e₂ =
    trans (r1 P A B) (trans (cong (_+ A) e₁) (trans (r2 H₁ B′ A) (trans (cong (_+ B′) e₂) (r3 H A′ B′))))
    where
      r1 : ∀ P A B → P + (A + B) ≡ (P + B) + A
      r1 = solve-∀
      r2 : ∀ H₁ B′ A → (H₁ + B′) + A ≡ (H₁ + A) + B′
      r2 = solve-∀
      r3 : ∀ H A′ B′ → (H + A′) + B′ ≡ H + (A′ + B′)
      r3 = solve-∀

  -- what an exchange leaves of the frame
  post-sub : ∀ P V H W R → P + V ≡ H + W → V + R ≤ H → W + R ≤ P
  post-sub P V H W R e le =
    ≤-cancelʳ V (subst ((W + R) + V ≤_) (trans (comm W H) (sym e)) (subst (_≤ W + H) (r W R V) (≤-+ˡ′ W le)))
    where
      r : ∀ W R V → W + (V + R) ≡ (W + R) + V
      r = solve-∀
      ≤-+ˡ′ : ∀ {a b} c → a ≤ b → c + a ≤ c + b
      ≤-+ˡ′ zero    le = le
      ≤-+ˡ′ (suc c) le = s≤s (≤-+ˡ′ c le)

-- every fresh id comes from the counter
copy-mono : ∀ {A} (v : MV A) n → n ≤ fst (snd (copy v n))
copy-mono mone n = ≤-refl
copy-mono (mpair a b) n with copy a n | copy-mono a n
... | (a' , n₁ , t₁) | m₁ with copy b n₁ | copy-mono b n₁
...   | (b' , n₂ , t₂) | m₂ = ≤-trans m₁ m₂
copy-mono (minl a) n with copy a n | copy-mono a n
... | (a' , n₁ , t₁) | m₁ = m₁
copy-mono (minr b) n with copy b n | copy-mono b n
... | (b' , n₁ , t₁) | m₁ = m₁
copy-mono (mbase x) n = ≤-refl
copy-mono (mmu i v) n with copy v (suc n) | copy-mono v (suc n)
... | (v' , n₁ , t₁) | m₁ = ≤-trans (n≤1+n n) m₁
copy-mono (mclo i e f) n with copy e (suc n) | copy-mono e (suc n)
... | (e' , n₁ , t₁) | m₁ = ≤-trans (n≤1+n n) m₁
copy-mono (mnu i s c) n with copy s (suc n) | copy-mono s (suc n)
... | (s' , n₁ , t₁) | m₁ = ≤-trans (n≤1+n n) m₁
copy-mono (mnuv i v) n with copy v (suc n) | copy-mono v (suc n)
... | (v' , n₁ , t₁) | m₁ = ≤-trans (n≤1+n n) m₁

copy-below : ∀ {A} (v : MV A) n i → fst (snd (copy v n)) ≤ i → cnt (fst (copy v n)) i ≡ 0
copy-below mone n i le = refl
copy-below (mpair a b) n i le with copy a n | copy-below a n | copy-mono a n
... | (a' , n₁ , t₁) | ba | m₁ with copy b n₁ | copy-below b n₁ | copy-mono b n₁
...   | (b' , n₂ , t₂) | bb | m₂ = cong₂ _+_ (ba i (≤-trans m₂ le)) (bb i le)
copy-below (minl a) n i le with copy a n | copy-below a n
... | (a' , n₁ , t₁) | ba = ba i le
copy-below (minr b) n i le with copy b n | copy-below b n
... | (b' , n₁ , t₁) | bb = bb i le
copy-below (mbase x) n i le = refl
copy-below (mmu j v) n i le with copy v (suc n) | copy-below v (suc n) | copy-mono v (suc n)
... | (v' , n₁ , t₁) | bv | m₁ = cong₂ _+_ (δ-fresh (≤-trans m₁ le)) (bv i le)
copy-below (mclo j e f) n i le with copy e (suc n) | copy-below e (suc n) | copy-mono e (suc n)
... | (e' , n₁ , t₁) | bv | m₁ = cong₂ _+_ (δ-fresh (≤-trans m₁ le)) (bv i le)
copy-below (mnu j s c) n i le with copy s (suc n) | copy-below s (suc n) | copy-mono s (suc n)
... | (s' , n₁ , t₁) | bv | m₁ = cong₂ _+_ (δ-fresh (≤-trans m₁ le)) (bv i le)
copy-below (mnuv j v) n i le with copy v (suc n) | copy-below v (suc n) | copy-mono v (suc n)
... | (v' , n₁ , t₁) | bv | m₁ = cong₂ _+_ (δ-fresh (≤-trans m₁ le)) (bv i le)

-- one allocated cell, at the counter, onto a heap empty from the counter on
private
  alloc-above : ∀ n (h : Heap) → (∀ i → n ≤ i → h i ≡ 0) → ∀ i → suc n ≤ i → step (alloc n) h i ≡ 0
  alloc-above n h ab i le = trans (cong (h i +_) (δ-fresh le)) (trans (+0 (h i)) (ab i (≤-trans (n≤1+n n) le)))

  alloc-eq : ∀ n (h : Heap) (V : Heap) (P : Heap) → (∀ i → P i ≡ step (alloc n) h i + V i)
           → ∀ i → P i ≡ h i + (δ n i + V i)
  alloc-eq n h V P e i = trans (e i) (assoc (h i) (δ n i) (V i))

-- `dup`'s copy: legal, and it adds exactly the copy's cells
copy-ok : ∀ {A} (v : MV A) n (h : Heap) → (∀ i → n ≤ i → h i ≡ 0)
        → OK (snd (snd (copy v n))) h × (∀ i → play (snd (snd (copy v n))) h i ≡ h i + cnt (fst (copy v n)) i)
copy-ok mone n h ab = (tt , λ i → sym (+0 (h i)))
copy-ok (mpair a b) n h ab with copy a n | copy-ok a n h ab | copy-below a n | copy-mono a n
... | (a' , n₁ , t₁) | (oka , eqa) | ba | m₁ with copy b n₁ | copy-ok b n₁ (play t₁ h) ab₁ | copy-mono b n₁
  where ab₁ : ∀ i → n₁ ≤ i → play t₁ h i ≡ 0
        ab₁ i le = trans (eqa i) (cong₂ _+_ (ab i (≤-trans m₁ le)) (ba i le))
...   | (b' , n₂ , t₂) | (okb , eqb) | m₂ =
  ( OK-++ t₁ t₂ h oka okb
  , λ i → trans (cong (λ x → x i) (play-++ t₁ t₂ h)) (trans (eqb i) (trans (cong (_+ cnt b' i) (eqa i)) (assoc (h i) (cnt a' i) (cnt b' i)))))
copy-ok (minl a) n h ab with copy a n | copy-ok a n h ab
... | (a' , n₁ , t₁) | r = r
copy-ok (minr b) n h ab with copy b n | copy-ok b n h ab
... | (b' , n₁ , t₁) | r = r
copy-ok (mbase x) n h ab = (tt , λ i → sym (+0 (h i)))
copy-ok (mmu j v) n h ab with copy v (suc n) | copy-ok v (suc n) (step (alloc n) h) (alloc-above n h ab)
... | (v' , n₁ , t₁) | (ok , eq) = ((ab n ≤-refl , ok) , alloc-eq n h (cnt v') (play t₁ (step (alloc n) h)) eq)
copy-ok (mclo j e f) n h ab with copy e (suc n) | copy-ok e (suc n) (step (alloc n) h) (alloc-above n h ab)
... | (e' , n₁ , t₁) | (ok , eq) = ((ab n ≤-refl , ok) , alloc-eq n h (cnt e') (play t₁ (step (alloc n) h)) eq)
copy-ok (mnu j s c) n h ab with copy s (suc n) | copy-ok s (suc n) (step (alloc n) h) (alloc-above n h ab)
... | (s' , n₁ , t₁) | (ok , eq) = ((ab n ≤-refl , ok) , alloc-eq n h (cnt s') (play t₁ (step (alloc n) h)) eq)
copy-ok (mnuv j v) n h ab with copy v (suc n) | copy-ok v (suc n) (step (alloc n) h) (alloc-above n h ab)
... | (v' , n₁ , t₁) | (ok , eq) = ((ab n ≤-refl , ok) , alloc-eq n h (cnt v') (play t₁ (step (alloc n) h)) eq)

-- freeing one live cell `j` whose contents count `V`
free-step : ∀ j (V : Heap) (h r : Heap) → (∀ i → h i ≤ 1) → (∀ i → (δ j i + V i) + r i ≤ h i)
          → h j ≡ 1 × (∀ i → step (free j) h i ≤ 1) × (∀ i → V i + r i ≤ step (free j) h i)
            × (∀ i → step (free j) h i + δ j i ≡ h i)
free-step j V h r le sb =
  ( ≤-antisym (le j) (≤-trans one≤ (sb j))
  , (λ i → ≤-trans (m∸n≤m (h i) (δ j i)) (le i))
  , (λ i → sub-le (δ j i) (subst (_≤ h i) (assoc (δ j i) (V i) (r i)) (sb i)))
  , (λ i → m∸n+n≡m (≤-trans (m≤m+n (δ j i) (V i + r i)) (subst (_≤ h i) (assoc (δ j i) (V i) (r i)) (sb i)))) )
  where
    one≤ : 1 ≤ (δ j j + V j) + r j
    one≤ = subst (λ x → 1 ≤ (x + V j) + r j) (sym (δ-same j)) (s≤s z≤n)

-- freeing a cell after freeing what it holds
free-cell : ∀ j (V : Heap) (t : Trace) (h r : Heap) → (∀ i → h i ≤ 1) → (∀ i → (δ j i + V i) + r i ≤ h i)
          → (∀ h′ → (∀ i → h′ i ≤ 1) → (∀ i → V i + r i ≤ h′ i) → OK t h′ × (∀ i → play t h′ i + V i ≡ h′ i))
          → OK (free j ∷ t) h × (∀ i → play (free j ∷ t) h i + (δ j i + V i) ≡ h i)
free-cell j V t h r le sb ih with free-step j V h r le sb
... | (hj , le′ , sb′ , back) with ih (step (free j) h) le′ sb′
...   | (ok , eq) = ((hj , ok) , λ i → trans (r1 (play t (step (free j) h) i) (V i) (δ j i)) (trans (cong (_+ δ j i) (eq i)) (back i)))
  where r1 : ∀ P V D → P + (D + V) ≡ (P + V) + D
        r1 = solve-∀

-- `drop`'s frees: legal, and they remove exactly the value's cells
free-ok : ∀ {A} (v : MV A) (h r : Heap) → (∀ i → h i ≤ 1) → (∀ i → cnt v i + r i ≤ h i)
        → OK (freeAll v) h × (∀ i → play (freeAll v) h i + cnt v i ≡ h i)
free-ok mone h r le sb = (tt , λ i → +0 (h i))
free-ok (mpair a b) h r le sb
  with free-ok a h (λ i → cnt b i + r i) le (λ i → subst (_≤ h i) (assoc (cnt a i) (cnt b i) (r i)) (sb i))
... | (oka , eqa)
  with free-ok b (play (freeAll a) h) r (OK-le1 (freeAll a) h oka le)
         (λ i → ≤-cancelʳ (cnt a i)
                  (subst (λ x → (cnt b i + r i) + cnt a i ≤ x) (sym (eqa i))
                     (subst (_≤ h i) (r2 (cnt a i) (cnt b i) (r i)) (sb i))))
  where r2 : ∀ A B R → (A + B) + R ≡ (B + R) + A
        r2 = solve-∀
...   | (okb , eqb) =
  ( OK-++ (freeAll a) (freeAll b) h oka okb
  , λ i → trans (cong (λ x → x i + (cnt a i + cnt b i)) (play-++ (freeAll a) (freeAll b) h))
            (trans (r3 (play (freeAll b) (play (freeAll a) h) i) (cnt a i) (cnt b i))
              (trans (cong (_+ cnt a i) (eqb i)) (eqa i))) )
  where r3 : ∀ P A B → P + (A + B) ≡ (P + B) + A
        r3 = solve-∀
free-ok (minl a) h r le sb = free-ok a h r le sb
free-ok (minr b) h r le sb = free-ok b h r le sb
free-ok (mbase x) h r le sb = (tt , λ i → +0 (h i))
free-ok (mmu j v) h r le sb = free-cell j (cnt v) (freeAll v) h r le sb (λ h′ le′ sb′ → free-ok v h′ r le′ sb′)
free-ok (mclo j e f) h r le sb = free-cell j (cnt e) (freeAll e) h r le sb (λ h′ le′ sb′ → free-ok e h′ r le′ sb′)
free-ok (mnu j s c) h r le sb = free-cell j (cnt s) (freeAll s) h r le sb (λ h′ le′ sb′ → free-ok s h′ r le′ sb′)
free-ok (mnuv j v) h r le sb = free-cell j (cnt v) (freeAll v) h r le sb (λ h′ le′ sb′ → free-ok v h′ r le′ sb′)

mono : ∀ {A B} {f : LTm A B} {v w n n′ t} → Run f v n w n′ t → n ≤ n′
mono r-id          = ≤-refl
mono (r-∘ rg rf)   = ≤-trans (mono rg) (mono rf)
mono (r-⊗ rf rg)   = ≤-trans (mono rf) (mono rg)
mono r-ρ           = ≤-refl
mono r-ρ⁻          = ≤-refl
mono r-λ           = ≤-refl
mono r-λ⁻          = ≤-refl
mono r-α           = ≤-refl
mono r-α⁻          = ≤-refl
mono r-swap        = ≤-refl
mono (r-dup {v = v} {n}) = copy-mono v n
mono r-drop        = ≤-refl
mono r-inl         = ≤-refl
mono r-inr         = ≤-refl
mono (r-case₁ r)   = mono r
mono (r-case₂ r)   = mono r
mono r-In          = n≤1+n _
mono r-Outμ        = ≤-refl
mono r-curry       = n≤1+n _
mono (r-eval r)    = mono r
mono r-Ana         = n≤1+n _
mono r-Inν         = n≤1+n _

Below : ∀ {A} → MV A → ℕ → Set
Below v n = ∀ i → n ≤ i → cnt v i ≡ 0

below : ∀ {A B} {f : LTm A B} {v w n n′ t} → Run f v n w n′ t → Below v n → Below w n′
below r-id b = b
below (r-∘ rg rf) b = below rf (below rg b)
below (r-⊗ {a = a} {b = bb} rf rg) b i le =
  cong₂ _+_ (below rf (λ j l → +≡0ˡ (cnt a j) (cnt bb j) (b j l)) i (≤-trans (mono rg) le))
            (below rg (λ j l → +≡0ʳ (cnt a j) (cnt bb j) (b j (≤-trans (mono rf) l))) i le)
below (r-ρ {a = a}) b i le = +≡0ˡ (cnt a i) 0 (b i le)
below r-ρ⁻ b i le = trans (+0 _) (b i le)
below r-λ b = b
below r-λ⁻ b = b
below (r-α {a = a} {b = bb} {c = c}) b i le = trans (sym (assoc (cnt a i) (cnt bb i) (cnt c i))) (b i le)
below (r-α⁻ {a = a} {b = bb} {c = c}) b i le = trans (assoc (cnt a i) (cnt bb i) (cnt c i)) (b i le)
below (r-swap {a = a} {b = bb}) b i le = trans (comm (cnt bb i) (cnt a i)) (b i le)
below (r-dup {v = v} {n}) b i le = cong₂ _+_ (b i (≤-trans (copy-mono v n) le)) (copy-below v n i le)
below r-drop b i le = refl
below r-inl b = b
below r-inr b = b
below (r-case₁ r) b = below r b
below (r-case₂ r) b = below r b
below (r-In {n = n}) b i le = cong₂ _+_ (δ-fresh le) (b i (≤-trans (n≤1+n n) le))
below (r-Outμ {v = v} {i = j}) b i le = +≡0ʳ (δ j i) (cnt v i) (b i le)
below (r-curry {n = n}) b i le = cong₂ _+_ (δ-fresh le) (b i (≤-trans (n≤1+n n) le))
below (r-eval {env = env} {a = a} {i = j} r) b = below r (λ i le →
  cong₂ _+_ (+≡0ʳ (δ j i) (cnt env i) (+≡0ˡ (δ j i + cnt env i) (cnt a i) (b i le)))
            (+≡0ʳ (δ j i + cnt env i) (cnt a i) (b i le)))
below (r-Ana {n = n}) b i le = cong₂ _+_ (δ-fresh le) (b i (≤-trans (n≤1+n n) le))
below (r-Inν {n = n}) b i le = cong₂ _+_ (δ-fresh le) (b i (≤-trans (n≤1+n n) le))

pre-below : ∀ {h n A} {v : MV A} {r} → Pre h n v r → Below v n
pre-below {h} {v = v} {r} pre i le = +≡0ˡ (cnt v i) (r i) (≤0 (subst (cnt v i + r i ≤_) (above pre i le) (sub pre i)))

-- after a run, the same precondition holds of the output, at the new counter
post : ∀ {A B} {f : LTm A B} {v w n n′ t h r} → Run f v n w n′ t → Pre h n v r → OK t h
     → (∀ i → play t h i + cnt v i ≡ h i + cnt w i) → Pre (play t h) n′ w r
post {v = v} {w} {n} {n′} {t} {h} {r} run pre ok eq = record
  { le1   = OK-le1 t h ok (le1 pre)
  ; above = λ i le →
      let n≤i = ≤-trans (mono run) le
          e   = eq i
          e′  = trans (sym (+0 (play t h i)))
                  (trans (cong (play t h i +_) (sym (pre-below pre i n≤i)))
                    (trans e (cong₂ _+_ (above pre i n≤i) (below run (pre-below pre) i le))))
      in e′
  ; sub   = λ i → post-sub (play t h i) (cnt v i) (h i) (cnt w i) (r i) (eq i) (sub pre i) }

------------------------------------------------------------------------
-- ★ The theorem.
------------------------------------------------------------------------

private
  -- one cell allocated at the counter, holding `V`
  alloc1 : ∀ {h n A} {v : MV A} {r} (V : Heap) → Pre h n v r
         → OK (alloc n ∷ []) h × (∀ i → play (alloc n ∷ []) h i + V i ≡ h i + (δ n i + V i))
  alloc1 {h} {n} V pre = ((above pre n ≤-refl , tt) , λ i → assoc (h i) (δ n i) (V i))

exchange : ∀ {A B} {f : LTm A B} {v w n n′ t} → Run f v n w n′ t → ∀ {h r} → Pre h n v r
         → OK t h × (∀ i → play t h i + cnt v i ≡ h i + cnt w i)
exchange r-id pre = (tt , λ i → refl)
exchange (r-∘ {v = v} {u} {w} {t₁ = t₁} {t₂} rg rf) {h} pre with exchange rg pre
... | (okg , eqg) with exchange rf (post rg pre okg eqg)
...   | (okf , eqf) =
  ( OK-++ t₁ t₂ h okg okf
  , λ i → trans (cong (λ x → x i + cnt v i) (play-++ t₁ t₂ h))
            (chain (play t₂ (play t₁ h) i) (cnt u i) (play t₁ h i) (cnt w i) (cnt v i) (h i) (eqf i) (eqg i)) )
exchange (r-⊗ {a = a} {a′} {b} {b′} {t₁ = t₁} {t₂} rf rg) {h} {r} pre
  with exchange rf {h} {λ i → cnt b i + r i}
         record { le1 = le1 pre ; above = above pre
                ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt b i) (r i)) (sub pre i) }
... | (oka , eqa)
  with exchange rg {play t₁ h} {λ i → cnt a′ i + r i}
         (let p₁ = post rf (record { le1 = le1 pre ; above = above pre
                                   ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt b i) (r i)) (sub pre i) })
                        oka eqa
          in record { le1 = le1 p₁ ; above = λ i le → above p₁ i (≤-trans (≤-refl) le)
                    ; sub = λ i → subst (_≤ play t₁ h i) (sw (cnt a′ i) (cnt b i) (r i)) (sub p₁ i) })
  where sw : ∀ A′ B R → A′ + (B + R) ≡ B + (A′ + R)
        sw = solve-∀
...   | (okb , eqb) =
  ( OK-++ t₁ t₂ h oka okb
  , λ i → trans (cong (λ x → x i + (cnt a i + cnt b i)) (play-++ t₁ t₂ h))
            (chain⊗ (play t₂ (play t₁ h) i) (cnt b i) (play t₁ h i) (cnt b′ i) (cnt a i) (h i) (cnt a′ i) (eqb i) (eqa i)) )
exchange (r-ρ {a = a}) {h} pre = (tt , λ i → cong (h i +_) (+0 (cnt a i)))
exchange (r-ρ⁻ {a = a}) {h} pre = (tt , λ i → cong (h i +_) (sym (+0 (cnt a i))))
exchange r-λ pre = (tt , λ i → refl)
exchange r-λ⁻ pre = (tt , λ i → refl)
exchange (r-α {a = a} {b} {c}) {h} pre = (tt , λ i → cong (h i +_) (assoc (cnt a i) (cnt b i) (cnt c i)))
exchange (r-α⁻ {a = a} {b} {c}) {h} pre = (tt , λ i → cong (h i +_) (sym (assoc (cnt a i) (cnt b i) (cnt c i))))
exchange (r-swap {a = a} {b}) {h} pre = (tt , λ i → cong (h i +_) (comm (cnt a i) (cnt b i)))
exchange (r-dup {v = v} {n}) {h} pre with copy-ok v n h (above pre)
... | (ok , eq) = (ok , λ i → trans (cong (_+ cnt v i) (eq i)) (r4 (h i) (cnt (fst (copy v n)) i) (cnt v i)))
  where r4 : ∀ H C V → (H + C) + V ≡ H + (V + C)
        r4 = solve-∀
exchange (r-drop {v = v}) {h} {r} pre with free-ok v h r (le1 pre) (sub pre)
... | (ok , eq) = (ok , λ i → trans (eq i) (sym (+0 (h i))))
exchange r-inl pre = (tt , λ i → refl)
exchange r-inr pre = (tt , λ i → refl)
exchange (r-case₁ r) pre = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre }
exchange (r-case₂ r) pre = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre }
exchange (r-In {v = v}) pre = alloc1 (cnt v) pre
exchange (r-Outμ {v = v} {i = j}) {h} {r} pre with free-step j (cnt v) h r (le1 pre) (sub pre)
... | (hj , _ , _ , back) = ((hj , tt) , λ i → trans (r5 (step (free j) h i) (δ j i) (cnt v i)) (cong (_+ cnt v i) (back i)))
  where r5 : ∀ P D V → P + (D + V) ≡ (P + D) + V
        r5 = solve-∀
exchange (r-curry {a = a}) pre = alloc1 (cnt a) pre
exchange (r-eval {env = env} {a = a} {i = j} {t = t} r) {h} {rf} pre
  with free-step j (λ i → cnt env i + cnt a i) h rf (le1 pre)
         (λ i → subst (_≤ h i) (cong (_+ rf i) (assoc (δ j i) (cnt env i) (cnt a i))) (sub pre i))
... | (hj , le′ , sb′ , back)
  with exchange r {step (free j) h} {rf}
         record { le1 = le′
                ; above = λ i le → ≤0 (subst (step (free j) h i ≤_) (above pre i le) (m∸n≤m (h i) (δ j i)))
                ; sub = sb′ }
...   | (ok , eq) =
  ( (hj , ok)
  , λ i → trans (r6 (play t (step (free j) h) i) (δ j i) (cnt env i) (cnt a i))
            (trans (cong (_+ δ j i) (eq i)) (trans (r7 (step (free j) h i) _ (δ j i)) (cong (_+ _) (back i)))) )
  where r6 : ∀ P D E A → P + ((D + E) + A) ≡ (P + (E + A)) + D
        r6 = solve-∀
        r7 : ∀ H W D → (H + W) + D ≡ (H + D) + W
        r7 = solve-∀
exchange (r-Ana {s = s}) pre = alloc1 (cnt s) pre
exchange (r-Inν {v = v}) pre = alloc1 (cnt v) pre

-- ★ NoLeak, for a run that returns: a whole program, from the empty heap,
-- frees every cell it allocated, exactly once, and frees nothing else.
noleak : ∀ {f : LTm One One} {n′ t} → Run f mone 0 mone n′ t
       → OK t (λ _ → 0) × (∀ i → play t (λ _ → 0) i ≡ 0)
noleak run with exchange run {λ _ → 0} {λ _ → 0}
                  record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }
... | (ok , eq) = (ok , λ i → trans (sym (+0 _)) (eq i))
