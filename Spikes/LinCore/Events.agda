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
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_)

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
