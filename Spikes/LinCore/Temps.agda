-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Temps — plan 0.146 A13 (D407): TEMPORARIES.
--
-- The lowering may allocate heap blocks the run does not have (a fold's work
-- stack), if the same generator frees them before it finishes and nothing in
-- the result points into them (the user, 2026-11-10). In `Events` they are a
-- decoration of a run (`r-tmp`): events `tmp (tnew k)`/`tmp (tdel k)` of a
-- size `k`, woven into the events of the term whose lowering uses them, and
-- balanced there if it gives a value. They have no ids and are not values,
-- so nothing can point into them; they are not cells of the run, so every
-- theorem of `Events` holds as it was. Here:
--
--   * `plain`: a run ERASES to a run of the same term, with the same values
--     and the same cell events, with no temporaries;
--   * `tsound`: every run's temporaries are BALANCED if it gives a value —
--     each one freed, by size — and legal if it stopped (the exit exception).
--
-- The run's ids are the machine's names for cells: temporaries take none.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m; +-assoc; +-∸-comm; +-∸-assoc; +-monoˡ-≤; ∸-monoˡ-≤)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-monoid)
open import Algebra using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_→-setoid_)
open import Level using (0ℓ; _⊔_)
import Function.Endo.Setoid
open import Relation.Nullary using (yes; no)
open import LinCore.Flat using (FTy)

module LinCore.Temps
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  (bw : Base → ℕ)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Events Base ⟦_⟧b Sig sdom scod bw

------------------------------------------------------------------------
-- 1. ERASURE: a run without its temporaries is a run.
------------------------------------------------------------------------

erase : Trace → Trace
erase []             = []
erase (alloc i ∷ t)  = alloc i ∷ erase t
erase (free i ∷ t)   = free i ∷ erase t
erase (peek i ∷ t)   = peek i ∷ erase t
erase (io s x y ∷ t) = io s x y ∷ erase t
erase (stp s x ∷ t)  = stp s x ∷ erase t
erase (tmp _ ∷ t)    = erase t

-- a trace with no temporaries
NoT : Trace → Set
NoT []             = ⊤
NoT (alloc _ ∷ t)  = NoT t
NoT (free _ ∷ t)   = NoT t
NoT (peek _ ∷ t)   = NoT t
NoT (io _ _ _ ∷ t) = NoT t
NoT (stp _ _ ∷ t)  = NoT t
NoT (tmp _ ∷ t)    = ⊥

erase-++ : ∀ t₁ t₂ → erase (t₁ ++ t₂) ≡ erase t₁ ++ erase t₂
erase-++ []             t₂ = refl
erase-++ (alloc i ∷ t₁) t₂ = cong (alloc i ∷_) (erase-++ t₁ t₂)
erase-++ (free i ∷ t₁)  t₂ = cong (free i ∷_) (erase-++ t₁ t₂)
erase-++ (peek i ∷ t₁)  t₂ = cong (peek i ∷_) (erase-++ t₁ t₂)
erase-++ (io s x y ∷ t₁) t₂ = cong (io s x y ∷_) (erase-++ t₁ t₂)
erase-++ (stp s x ∷ t₁) t₂ = cong (stp s x ∷_) (erase-++ t₁ t₂)
erase-++ (tmp _ ∷ t₁)   t₂ = erase-++ t₁ t₂

erase-NoT : ∀ t → NoT t → erase t ≡ t
erase-NoT []             _ = refl
erase-NoT (alloc i ∷ t)  n = cong (alloc i ∷_) (erase-NoT t n)
erase-NoT (free i ∷ t)   n = cong (free i ∷_) (erase-NoT t n)
erase-NoT (peek i ∷ t)   n = cong (peek i ∷_) (erase-NoT t n)
erase-NoT (io s x y ∷ t) n = cong (io s x y ∷_) (erase-NoT t n)
erase-NoT (stp s x ∷ t)  n = cong (stp s x ∷_) (erase-NoT t n)
erase-NoT (tmp _ ∷ t)    ()

-- what erasure leaves has no temporaries
erase-clean : ∀ t → NoT (erase t)
erase-clean []             = tt
erase-clean (alloc _ ∷ t)  = erase-clean t
erase-clean (free _ ∷ t)   = erase-clean t
erase-clean (peek _ ∷ t)   = erase-clean t
erase-clean (io _ _ _ ∷ t) = erase-clean t
erase-clean (stp _ _ ∷ t)  = erase-clean t
erase-clean (tmp _ ∷ t)    = erase-clean t

erase-weave : ∀ {t ts t′} → Weave t ts t′ → erase t′ ≡ erase t
erase-weave w-[]                       = refl
erase-weave (w-run {x = alloc i} w)    = cong (alloc i ∷_) (erase-weave w)
erase-weave (w-run {x = free i} w)     = cong (free i ∷_) (erase-weave w)
erase-weave (w-run {x = peek i} w)     = cong (peek i ∷_) (erase-weave w)
erase-weave (w-run {x = io s x y} w)   = cong (io s x y ∷_) (erase-weave w)
erase-weave (w-run {x = stp s x} w)    = cong (stp s x ∷_) (erase-weave w)
erase-weave (w-run {x = tmp _} w)      = erase-weave w
erase-weave (w-tmp w)                  = erase-weave w

erase-≼ : ∀ {t′ t} → t′ ≼ t → erase t′ ≼ erase t
erase-≼ []≼                    = []≼
erase-≼ (∷≼ {x = alloc _} q)   = ∷≼ (erase-≼ q)
erase-≼ (∷≼ {x = free _} q)    = ∷≼ (erase-≼ q)
erase-≼ (∷≼ {x = peek _} q)    = ∷≼ (erase-≼ q)
erase-≼ (∷≼ {x = io _ _ _} q)  = ∷≼ (erase-≼ q)
erase-≼ (∷≼ {x = stp _ _} q)   = ∷≼ (erase-≼ q)
erase-≼ (∷≼ {x = tmp _} q)     = erase-≼ q

NoT-++ : ∀ t₁ t₂ → NoT t₁ → NoT t₂ → NoT (t₁ ++ t₂)
NoT-++ []             t₂ _  n₂ = n₂
NoT-++ (alloc _ ∷ t₁) t₂ n₁ n₂ = NoT-++ t₁ t₂ n₁ n₂
NoT-++ (free _ ∷ t₁)  t₂ n₁ n₂ = NoT-++ t₁ t₂ n₁ n₂
NoT-++ (peek _ ∷ t₁)  t₂ n₁ n₂ = NoT-++ t₁ t₂ n₁ n₂
NoT-++ (io _ _ _ ∷ t₁) t₂ n₁ n₂ = NoT-++ t₁ t₂ n₁ n₂
NoT-++ (stp _ _ ∷ t₁) t₂ n₁ n₂ = NoT-++ t₁ t₂ n₁ n₂
NoT-++ (tmp _ ∷ t₁)   t₂ ()  n₂

-- `dup`'s and `drop`'s own events are cell events
NoT-copy : ∀ {A} (v : MV A) n → NoT (snd (snd (copy v n)))
NoT-copy mone n = tt
NoT-copy (mpair a b) n with copy a n | NoT-copy a n
... | (a' , n₁ , t₁) | na with copy b n₁ | NoT-copy b n₁
...   | (b' , n₂ , t₂) | nb = NoT-++ t₁ t₂ na nb
NoT-copy (minl a) n with copy a n | NoT-copy a n
... | (a' , n₁ , t₁) | na = na
NoT-copy (minr b) n with copy b n | NoT-copy b n
... | (b' , n₁ , t₁) | nb = nb
NoT-copy (mbase x) n = tt
NoT-copy (mmu i v) n with copy v (suc n) | NoT-copy v (suc n)
... | (v' , n₁ , t₁) | nv = nv
NoT-copy (mct x) n with copy x n | NoT-copy x n
... | (x' , n₁ , t₁) | nx = nx

NoT-freeAll : ∀ {A} (v : MV A) → NoT (freeAll v)
NoT-freeAll mone        = tt
NoT-freeAll (mpair a b) = NoT-++ (freeAll a) (freeAll b) (NoT-freeAll a) (NoT-freeAll b)
NoT-freeAll (minl a)    = NoT-freeAll a
NoT-freeAll (minr b)    = NoT-freeAll b
NoT-freeAll (mbase x)   = tt
NoT-freeAll (mmu i v)   = NoT-freeAll v
NoT-freeAll (mct x)     = NoT-freeAll x

private
  retrace : ∀ {E A B} {f : Tm Γ E A B} {e v n o t t′} → t ≡ t′ → Run ds f e v n o t → Run ds f e v n o t′
  retrace refl r = r

  retraceM : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e G x n o t t′} → t ≡ t′
           → RunMap ds F alg e G x n o t → RunMap ds F alg e G x n o t′
  retraceM refl r = r

plain-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
          → RunMap ds F alg e G x n o t → RunMap ds F alg e G x n o (erase t)

-- ★ a run without its temporaries: the same term, values and cell events
plain : ∀ {E A B} {f : Tm Γ E A B} {e v n o t} → Run ds f e v n o t → Run ds f e v n o (erase t)
plain r-id = r-id
plain (r-∘ {t₁ = t₁} {t₂} rg rf) = retrace (sym (erase-++ t₁ t₂)) (r-∘ (plain rg) (plain rf))
plain (r-∘! r) = r-∘! (plain r)
plain (r-⊗ {t₁ = t₁} {t₂} rf rg) = retrace (sym (erase-++ t₁ t₂)) (r-⊗ (plain rf) (plain rg))
plain (r-⊗!₁ r) = r-⊗!₁ (plain r)
plain (r-⊗!₂ {t₁ = t₁} {t₂} rf rg) = retrace (sym (erase-++ t₁ t₂)) (r-⊗!₂ (plain rf) (plain rg))
plain r-ρ = r-ρ
plain r-ρ⁻ = r-ρ⁻
plain r-λ = r-λ
plain r-λ⁻ = r-λ⁻
plain r-α = r-α
plain r-α⁻ = r-α⁻
plain r-swap = r-swap
plain (r-dup {v = v} {n}) = retrace (sym (erase-NoT _ (NoT-copy v n))) r-dup
plain (r-drop {v = v}) = retrace (sym (erase-NoT _ (NoT-freeAll v))) r-drop
plain r-inl = r-inl
plain r-inr = r-inr
plain (r-case₁ r) = r-case₁ (plain r)
plain (r-case₂ r) = r-case₂ (plain r)
plain r-In = r-In
plain r-Outμ = r-Outμ
plain r-clo = r-clo
plain (r-app q r) = r-app q (plain r)
plain (r-cata {i = i} {t₁ = t₁} {t₂} rm ra) =
  retrace (cong (free i ∷_) (sym (erase-++ t₁ t₂))) (r-cata (plain-map rm) (plain ra))
plain (r-cata! rm) = r-cata! (plain-map rm)
plain (r-cata-reuse {t₁ = t₁} {t₂} rm rg) = retrace (sym (erase-++ t₁ t₂)) (r-cata-reuse (plain-map rm) (plain rg))
plain (r-cata-reuse!₁ rm) = r-cata-reuse!₁ (plain-map rm)
plain (r-cata-reuse!₂ {t₁ = t₁} {t₂} rm rg) = retrace (sym (erase-++ t₁ t₂)) (r-cata-reuse!₂ (plain-map rm) (plain rg))
plain (r-lend r) = r-lend (plain r)
plain (r-lend! r) = r-lend! (plain r)
plain (r-lift r) = r-lift (plain r)
plain (r-fst r) = r-fst (plain r)
plain (r-snd r) = r-snd (plain r)
plain (r-caseE₁ r) = r-caseE₁ (plain r)
plain (r-caseE₂ r) = r-caseE₂ (plain r)
plain (r-out r) = r-out (plain r)
plain (r-copy {e = e} {n}) = retrace (sym (erase-NoT _ (NoT-copy e n))) r-copy
plain (r-bapp q r) = r-bapp q (plain r)
plain r-op = r-op
plain r-halt = r-halt
plain (r-iter-done r) = r-iter-done (plain r)
plain (r-iter-next {t₁ = t₁} {t₂} r rn) = retrace (sym (erase-++ t₁ t₂)) (r-iter-next (plain r) (plain rn))
plain (r-iter! r) = r-iter! (plain r)
plain r-exh = r-exh
plain (r-cut r q) = r-cut (plain r) (erase-≼ q)
plain (r-tmp r w p) = retrace (sym (erase-weave w)) (plain r)

plain-map (m-id r) = m-id (plain r)
plain-map m-one = m-one
plain-map m-b = m-b
plain-map m-μ = m-μ
plain-map (m-inl r) = m-inl (plain-map r)
plain-map (m-inl! r) = m-inl! (plain-map r)
plain-map (m-inr r) = m-inr (plain-map r)
plain-map (m-inr! r) = m-inr! (plain-map r)
plain-map (m-pair {t₁ = t₁} {t₂} r r′) = retraceM (sym (erase-++ t₁ t₂)) (m-pair (plain-map r) (plain-map r′))
plain-map (m-pair!₁ r) = m-pair!₁ (plain-map r)
plain-map (m-pair!₂ {t₁ = t₁} {t₂} r r′) = retraceM (sym (erase-++ t₁ t₂)) (m-pair!₂ (plain-map r) (plain-map r′))

------------------------------------------------------------------------
-- 2. THE LEDGER of live temporaries, by size.
------------------------------------------------------------------------

tplay-++ : ∀ t₁ t₂ L → tplay (t₁ ++ t₂) L ≡ tplay t₂ (tplay t₁ L)
tplay-++ []       t₂ L = refl
tplay-++ (x ∷ t₁) t₂ L = tplay-++ t₁ t₂ (tstep x L)

-- the same ledger, written differently
tstep-ext : ∀ x {L L′ : TL} → (∀ k → L k ≡ L′ k) → ∀ k → tstep x L k ≡ tstep x L′ k
tstep-ext (alloc _)      e k = e k
tstep-ext (free _)       e k = e k
tstep-ext (peek _)       e k = e k
tstep-ext (io _ _ _)     e k = e k
tstep-ext (stp _ _)      e k = e k
tstep-ext (tmp (tnew j)) e k = cong (_+ δn j k) (e k)
tstep-ext (tmp (tdel j)) e k = cong (_∸ δn j k) (e k)

tplay-ext : ∀ t {L L′ : TL} → (∀ k → L k ≡ L′ k) → ∀ k → tplay t L k ≡ tplay t L′ k
tplay-ext []      e = e
tplay-ext (x ∷ t) e = tplay-ext t (tstep-ext x e)

TOK-ext : ∀ t {L L′ : TL} → (∀ k → L k ≡ L′ k) → TOK t L → TOK t L′
TOK-ext []                 e ok       = tt
TOK-ext (alloc _ ∷ t)      e ok       = TOK-ext t e ok
TOK-ext (free _ ∷ t)       e ok       = TOK-ext t e ok
TOK-ext (peek _ ∷ t)       e ok       = TOK-ext t e ok
TOK-ext (io _ _ _ ∷ t)     e ok       = TOK-ext t e ok
TOK-ext (stp _ _ ∷ t)      e ok       = TOK-ext t e ok
TOK-ext (tmp (tnew j) ∷ t) e ok       = TOK-ext t (tstep-ext (tmp (tnew j)) e) ok
TOK-ext (tmp (tdel j) ∷ t) e (p , ok) = (subst (1 ≤_) (e j) p , TOK-ext t (tstep-ext (tmp (tdel j)) e) ok)

TOK-++ : ∀ t₁ t₂ L → TOK t₁ L → TOK t₂ (tplay t₁ L) → TOK (t₁ ++ t₂) L
TOK-++ []                  t₂ L ok₁       ok₂ = ok₂
TOK-++ (alloc _ ∷ t₁)      t₂ L ok₁       ok₂ = TOK-++ t₁ t₂ L ok₁ ok₂
TOK-++ (free _ ∷ t₁)       t₂ L ok₁       ok₂ = TOK-++ t₁ t₂ L ok₁ ok₂
TOK-++ (peek _ ∷ t₁)       t₂ L ok₁       ok₂ = TOK-++ t₁ t₂ L ok₁ ok₂
TOK-++ (io _ _ _ ∷ t₁)     t₂ L ok₁       ok₂ = TOK-++ t₁ t₂ L ok₁ ok₂
TOK-++ (stp _ _ ∷ t₁)      t₂ L ok₁       ok₂ = TOK-++ t₁ t₂ L ok₁ ok₂
TOK-++ (tmp (tnew j) ∷ t₁) t₂ L ok₁       ok₂ = TOK-++ t₁ t₂ _ ok₁ ok₂
TOK-++ (tmp (tdel j) ∷ t₁) t₂ L (p , ok₁) ok₂ = (p , TOK-++ t₁ t₂ _ ok₁ ok₂)

TOK-≼ : ∀ {t′ t L} → t′ ≼ t → TOK t L → TOK t′ L
TOK-≼ []≼                          ok       = tt
TOK-≼ (∷≼ {x = alloc _} q)         ok       = TOK-≼ q ok
TOK-≼ (∷≼ {x = free _} q)          ok       = TOK-≼ q ok
TOK-≼ (∷≼ {x = peek _} q)          ok       = TOK-≼ q ok
TOK-≼ (∷≼ {x = io _ _ _} q)        ok       = TOK-≼ q ok
TOK-≼ (∷≼ {x = stp _ _} q)         ok       = TOK-≼ q ok
TOK-≼ (∷≼ {x = tmp (tnew _)} q)    ok       = TOK-≼ q ok
TOK-≼ (∷≼ {x = tmp (tdel _)} q)    (p , ok) = (p , TOK-≼ q ok)

-- a trace with no temporaries leaves the ledger as it was
NoT-TOK : ∀ t {L} → NoT t → TOK t L
NoT-TOK []             _ = tt
NoT-TOK (alloc _ ∷ t)  n = NoT-TOK t n
NoT-TOK (free _ ∷ t)   n = NoT-TOK t n
NoT-TOK (peek _ ∷ t)   n = NoT-TOK t n
NoT-TOK (io _ _ _ ∷ t) n = NoT-TOK t n
NoT-TOK (stp _ _ ∷ t)  n = NoT-TOK t n
NoT-TOK (tmp _ ∷ t)    ()

NoT-tplay : ∀ t {L} → NoT t → tplay t L ≡ L
NoT-tplay []             _ = refl
NoT-tplay (alloc _ ∷ t)  n = NoT-tplay t n
NoT-tplay (free _ ∷ t)   n = NoT-tplay t n
NoT-tplay (peek _ ∷ t)   n = NoT-tplay t n
NoT-tplay (io _ _ _ ∷ t) n = NoT-tplay t n
NoT-tplay (stp _ _ ∷ t)  n = NoT-tplay t n
NoT-tplay (tmp _ ∷ t)    ()

NoT-Bal : ∀ t → NoT t → TBal t
NoT-Bal t n = (NoT-TOK t n , λ k → cong (λ L → L k) (NoT-tplay t n))

-- more live temporaries never make a free illegal
TOK-mono : ∀ t {L L′ : TL} → (∀ k → L k ≤ L′ k) → TOK t L → TOK t L′
TOK-mono []                 le ok       = tt
TOK-mono (alloc _ ∷ t)      le ok       = TOK-mono t le ok
TOK-mono (free _ ∷ t)       le ok       = TOK-mono t le ok
TOK-mono (peek _ ∷ t)       le ok       = TOK-mono t le ok
TOK-mono (io _ _ _ ∷ t)     le ok       = TOK-mono t le ok
TOK-mono (stp _ _ ∷ t)      le ok       = TOK-mono t le ok
TOK-mono (tmp (tnew j) ∷ t) le ok       = TOK-mono t (λ k → +-monoˡ-≤ (δn j k) (le k)) ok
TOK-mono (tmp (tdel j) ∷ t) le (p , ok) = (≤-trans p (le j) , TOK-mono t (λ k → ∸-monoˡ-≤ (δn j k) (le k)) ok)

------------------------------------------------------------------------
-- 2½. ★ THE STRUCTURE. Traces are the free monoid on events (`++`, `[]`);
-- a trace ACTS on ledgers, as a monoid homomorphism into the endomaps of
-- the ledgers (pointwise equal); the balanced traces and the legal ones are
-- SUBMONOIDS. The run's claims below are their laws, nothing invented.
------------------------------------------------------------------------

-- a predicate that holds of the unit, of products, and up to equality
record IsSubmonoid {c ℓ p} (M : Monoid c ℓ) (P : Monoid.Carrier M → Set p) : Set (c ⊔ ℓ ⊔ p) where
  open Monoid M using (_≈_; _∙_)
  field
    ∈-resp : ∀ {x y} → x ≈ y → P x → P y
    ε-∈    : P (Monoid.ε M)
    ∙-∈    : ∀ {x y} → P x → P y → P (x ∙ y)

trace-monoid : Monoid 0ℓ 0ℓ
trace-monoid = ++-monoid Ev

ledgers : Setoid 0ℓ 0ℓ
ledgers = ℕ →-setoid ℕ

module Endo = Function.Endo.Setoid ledgers

-- a trace acts on ledgers
act : Trace → Endo.Endo
act t = record { to = tplay t ; cong = tplay-ext t }

open MonoidMorphisms (Monoid.rawMonoid trace-monoid) (Monoid.rawMonoid Endo.∘-id-monoid)
  using (IsMonoidHomomorphism)

-- ★ the action is a monoid homomorphism: `[]` acts as the identity, and
-- `t₁ ++ t₂` as `t₁`, then `t₂` (stdlib's composition is diagrammatic)
act-isMonoidHomomorphism : IsMonoidHomomorphism act
act-isMonoidHomomorphism = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = λ { refl L k → refl } }
    ; homo = λ t₁ t₂ L k → cong (λ M → M k) (tplay-++ t₁ t₂ L) }
  ; ε-homo = λ L k → refl }

-- ★ the legal traces are a submonoid: what follows a legal trace starts with
-- at least as many temporaries live (`TOK-mono`)
legal : IsSubmonoid trace-monoid TLeg
legal = record
  { ∈-resp = λ { refl l → l }
  ; ε-∈    = tt
  ; ∙-∈    = λ {t₁} {t₂} l₁ l₂ → TOK-++ t₁ t₂ none l₁ (TOK-mono t₂ (λ k → z≤n) l₂) }

-- ★ the balanced traces are a submonoid: legal, and the action fixes the
-- empty ledger — the stabiliser of `none`, by the homomorphism's law
balanced : IsSubmonoid trace-monoid TBal
balanced = record
  { ∈-resp = λ { refl b → b }
  ; ε-∈    = (tt , λ k → refl)
  ; ∙-∈    = λ {t₁} {t₂} (l₁ , z₁) (l₂ , z₂) →
      ( IsSubmonoid.∙-∈ legal {t₁} {t₂} l₁ l₂
      , λ k → trans (IsMonoidHomomorphism.homo act-isMonoidHomomorphism t₁ t₂ none k)
                    (trans (tplay-ext t₂ z₁ k) (z₂ k)) ) }

-- what a run claims of its temporaries, after a balanced prefix: a product
-- in the submonoid it claims
Bal-++ : ∀ {B} (o : Outcome B) t₁ t₂ → TBal t₁ → TPost o t₂ → TPost o (t₁ ++ t₂)
Bal-++ (gives _ _) t₁ t₂ b₁ b₂ = IsSubmonoid.∙-∈ balanced {t₁} {t₂} b₁ b₂
Bal-++ (stop _)    t₁ t₂ b₁ l₂ = IsSubmonoid.∙-∈ legal {t₁} {t₂} (fst b₁) l₂

Post-Leg : ∀ {B} (o : Outcome B) t → TPost o t → TLeg t
Post-Leg (gives _ _) t p = fst p
Post-Leg (stop _)    t p = p

-- a cell event first changes nothing of the claim
TPost-free : ∀ {B} (o : Outcome B) i t → TPost o t → TPost o (free i ∷ t)
TPost-free (gives _ _) i t p = p
TPost-free (stop _)    i t p = p

TPost-peek : ∀ {B} (o : Outcome B) i t → TPost o t → TPost o (peek i ∷ t)
TPost-peek (gives _ _) i t p = p
TPost-peek (stop _)    i t p = p

------------------------------------------------------------------------
-- 3. WEAVING: the live temporaries are those of both.
------------------------------------------------------------------------

private
  δn-≤ : ∀ {L : TL} k → 1 ≤ L k → ∀ j → δn k j ≤ L j
  δn-≤ k p j with k ≟ j
  ... | yes refl = p
  ... | no _     = z≤n

  swap+ : ∀ a b d → (a + b) + d ≡ (a + d) + b
  swap+ = solve-∀

weave-ok : ∀ {t ts t′} → Weave t ts t′ → ∀ (L₁ L₂ L : TL) → (∀ k → L k ≡ L₁ k + L₂ k)
         → TOK t L₁ → TOK (tmps ts) L₂
         → TOK t′ L × (∀ k → tplay t′ L k ≡ tplay t L₁ k + tplay (tmps ts) L₂ k)
weave-ok w-[] L₁ L₂ L e ok₁ ok₂ = (tt , e)
weave-ok (w-run {x = alloc _} w)  L₁ L₂ L e ok₁ ok₂ = weave-ok w L₁ L₂ L e ok₁ ok₂
weave-ok (w-run {x = free _} w)   L₁ L₂ L e ok₁ ok₂ = weave-ok w L₁ L₂ L e ok₁ ok₂
weave-ok (w-run {x = peek _} w)   L₁ L₂ L e ok₁ ok₂ = weave-ok w L₁ L₂ L e ok₁ ok₂
weave-ok (w-run {x = io _ _ _} w) L₁ L₂ L e ok₁ ok₂ = weave-ok w L₁ L₂ L e ok₁ ok₂
weave-ok (w-run {x = stp _ _} w)  L₁ L₂ L e ok₁ ok₂ = weave-ok w L₁ L₂ L e ok₁ ok₂
weave-ok (w-run {x = tmp (tnew k)} w) L₁ L₂ L e ok₁ ok₂ =
  weave-ok w _ L₂ _ (λ j → trans (cong (_+ δn k j) (e j)) (swap+ (L₁ j) (L₂ j) (δn k j))) ok₁ ok₂
weave-ok (w-run {x = tmp (tdel k)} w) L₁ L₂ L e (p , ok₁) ok₂
  with weave-ok w _ L₂ _ (λ j → trans (cong (_∸ δn k j) (e j)) (+-∸-comm (L₂ j) (δn-≤ k p j))) ok₁ ok₂
... | (ok , eq) = ((subst (1 ≤_) (sym (e k)) (≤-trans p (m≤m+n (L₁ k) (L₂ k))) , ok) , eq)
weave-ok (w-tmp {y = tnew k} w) L₁ L₂ L e ok₁ ok₂ =
  weave-ok w L₁ _ _ (λ j → trans (cong (_+ δn k j) (e j)) (+-assoc (L₁ j) (L₂ j) (δn k j))) ok₁ ok₂
weave-ok (w-tmp {y = tdel k} w) L₁ L₂ L e ok₁ (p , ok₂)
  with weave-ok w L₁ _ _ (λ j → trans (cong (_∸ δn k j) (e j)) (+-∸-assoc (L₁ j) (δn-≤ k p j))) ok₁ ok₂
... | (ok , eq) = ((subst (1 ≤_) (sym (e k)) (≤-trans p (m≤n+m (L₂ k) (L₁ k))) , ok) , eq)

weave-post : ∀ {B} (o : Outcome B) {t ts t′} → Weave t ts t′ → TPost o t → TPost o (tmps ts) → TPost o t′
weave-post (gives _ _) w (ok₁ , z₁) (ok₂ , z₂) with weave-ok w none none none (λ _ → refl) ok₁ ok₂
... | (ok , eq) = (ok , λ k → trans (eq k) (cong₂ _+_ (z₁ k) (z₂ k)))
weave-post (stop _) w ok₁ ok₂ = fst (weave-ok w none none none (λ _ → refl) ok₁ ok₂)

------------------------------------------------------------------------
-- 4. ★ THE THEOREM: every run frees its temporaries, if it gives a value.
------------------------------------------------------------------------

private
  bal[] : TBal []
  bal[] = IsSubmonoid.ε-∈ balanced

tsound-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
           → RunMap ds F alg e G x n o t → TPost o t

tsound : ∀ {E A B} {f : Tm Γ E A B} {e v n o t} → Run ds f e v n o t → TPost o t
tsound r-id = bal[]
tsound (r-∘ {o = o} {t₁ = t₁} {t₂} rg rf) = Bal-++ o t₁ t₂ (tsound rg) (tsound rf)
tsound (r-∘! r) = tsound r
tsound (r-⊗ {t₁ = t₁} {t₂} rf rg) = IsSubmonoid.∙-∈ balanced {t₁} {t₂} (tsound rf) (tsound rg)
tsound (r-⊗!₁ r) = tsound r
tsound (r-⊗!₂ {y = y} {t₁ = t₁} {t₂} rf rg) = IsSubmonoid.∙-∈ legal {t₁} {t₂} (fst (tsound rf)) (tsound rg)
tsound r-ρ = bal[]
tsound r-ρ⁻ = bal[]
tsound r-λ = bal[]
tsound r-λ⁻ = bal[]
tsound r-α = bal[]
tsound r-α⁻ = bal[]
tsound r-swap = bal[]
tsound (r-dup {v = v} {n}) = NoT-Bal (snd (snd (copy v n))) (NoT-copy v n)
tsound (r-drop {v = v}) = NoT-Bal (freeAll v) (NoT-freeAll v)
tsound r-inl = bal[]
tsound r-inr = bal[]
tsound (r-case₁ r) = tsound r
tsound (r-case₂ r) = tsound r
tsound r-In = bal[]
tsound r-Outμ = bal[]
tsound r-clo = bal[]
tsound (r-app q r) = tsound r
tsound (r-cata {i = i} {o = o} {t₁ = t₁} {t₂} rm ra) = TPost-free o i (t₁ ++ t₂) (Bal-++ o t₁ t₂ (tsound-map rm) (tsound ra))
tsound (r-cata! rm) = tsound-map rm
tsound (r-cata-reuse {t₁ = t₁} {t₂} rm rg) = IsSubmonoid.∙-∈ balanced {t₁} {t₂} (tsound-map rm) (tsound rg)
tsound (r-cata-reuse!₁ rm) = tsound-map rm
tsound (r-cata-reuse!₂ {y = y} {t₁ = t₁} {t₂} rm rg) = IsSubmonoid.∙-∈ legal {t₁} {t₂} (fst (tsound-map rm)) (tsound rg)
tsound (r-lend r) = tsound r
tsound (r-lend! r) = tsound r
tsound (r-lift r) = tsound r
tsound (r-fst r) = tsound r
tsound (r-snd r) = tsound r
tsound (r-caseE₁ r) = tsound r
tsound (r-caseE₂ r) = tsound r
tsound (r-out {i = i} {o = o} {t = t} r) = TPost-peek o i t (tsound r)
tsound (r-copy {e = e} {n}) = NoT-Bal (snd (snd (copy e n))) (NoT-copy e n)
tsound (r-bapp q r) = tsound r
tsound r-op = bal[]
tsound r-halt = tt
tsound (r-iter-done r) = tsound r
tsound (r-iter-next {o = o} {t₁ = t₁} {t₂} r rn) = Bal-++ o t₁ t₂ (tsound r) (tsound rn)
tsound (r-iter! r) = tsound r
tsound r-exh = tt
tsound (r-cut {o = o} {t = t} r q) = TOK-≼ q (Post-Leg o t (tsound r))
tsound (r-tmp {o = o} r w p) = weave-post o w (tsound r) p

tsound-map (m-id r) = tsound r
tsound-map m-one = bal[]
tsound-map m-b = bal[]
tsound-map m-μ = bal[]
tsound-map (m-inl r) = tsound-map r
tsound-map (m-inl! r) = tsound-map r
tsound-map (m-inr r) = tsound-map r
tsound-map (m-inr! r) = tsound-map r
tsound-map (m-pair {t₁ = t₁} {t₂} r r′) = IsSubmonoid.∙-∈ balanced {t₁} {t₂} (tsound-map r) (tsound-map r′)
tsound-map (m-pair!₁ r) = tsound-map r
tsound-map (m-pair!₂ {w = w} {t₁ = t₁} {t₂} r r′) = IsSubmonoid.∙-∈ legal {t₁} {t₂} (fst (tsound-map r)) (tsound-map r′)
