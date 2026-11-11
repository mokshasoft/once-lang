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
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Properties using (++-monoid; foldl-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import LinCore.Free
  using (_≼_; []≼; ∷≼; Weave; w-[]; w-run; w-tmp; Along; Along-++; Along-≼; Along-pres; Along-all;
         cmap-++; cmap-≼; cmap-weave; cmap-id; cmap-All; foldl-pres; foldl-all)
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

-- an event that is not a temporary
data Kept : Ev → Set where
  k-alloc : ∀ {i} → Kept (alloc i)
  k-free  : ∀ {i} → Kept (free i)
  k-peek  : ∀ {i} → Kept (peek i)
  k-io    : ∀ {s x y} → Kept (io s x y)
  k-stp   : ∀ {s x} → Kept (stp s x)

-- what an event leaves when the temporaries are erased
keep : Ev → Trace
keep (alloc i)  = alloc i ∷ []
keep (free i)   = free i ∷ []
keep (peek i)   = peek i ∷ []
keep (io s x y) = io s x y ∷ []
keep (stp s x)  = stp s x ∷ []
keep (tmp _)    = []

-- what is left of each event is kept, and a kept event is left as it was
keep-kept : ∀ x → All Kept (keep x)
keep-kept (alloc _)  = k-alloc ∷ []
keep-kept (free _)   = k-free ∷ []
keep-kept (peek _)   = k-peek ∷ []
keep-kept (io _ _ _) = k-io ∷ []
keep-kept (stp _ _)  = k-stp ∷ []
keep-kept (tmp _)    = []

kept-keep : ∀ {x} → Kept x → keep x ≡ x ∷ []
kept-keep k-alloc = refl
kept-keep k-free  = refl
kept-keep k-peek  = refl
kept-keep k-io    = refl
kept-keep k-stp   = refl

mem-kept : ∀ {x} → Mem x → Kept x
mem-kept m-alloc = k-alloc
mem-kept m-free  = k-free

-- the trace without its temporaries: a homomorphism of free monoids
erase : Trace → Trace
erase = concatMap keep

-- a trace with no temporaries
NoT : Trace → Set
NoT = All Kept

-- the laws, from the free monoid's (`Free`)
erase-++ : ∀ t₁ t₂ → erase (t₁ ++ t₂) ≡ erase t₁ ++ erase t₂
erase-++ = cmap-++ keep

erase-≼ : ∀ {t′ t} → t′ ≼ t → erase t′ ≼ erase t
erase-≼ = cmap-≼ keep

erase-weave : ∀ {t ts t′} → Weave tmp t ts t′ → erase t′ ≡ erase t
erase-weave = cmap-weave keep (λ _ → refl)

erase-NoT : ∀ t → NoT t → erase t ≡ t
erase-NoT t n = cmap-id keep (All.map kept-keep n)

erase-clean : ∀ t → NoT (erase t)
erase-clean = cmap-All keep keep-kept

-- `dup`'s and `drop`'s own events are cell events (`Events.copy-mem`)
NoT-copy : ∀ {A} (v : MV A) n → NoT (snd (snd (copy v n)))
NoT-copy v n = All.map mem-kept (copy-mem v n)

NoT-freeAll : ∀ {A} (v : MV A) → NoT (freeAll v)
NoT-freeAll v = All.map mem-kept (freeAll-mem v)

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
plain (r-∘ {t₁ = t₁} {t₂} rg (go-on rf)) = retrace (sym (erase-++ t₁ t₂)) (r-∘ (plain rg) (go-on (plain rf)))
plain (r-∘ {t₁ = t₁} rg stopped) = retrace (sym (erase-++ t₁ [])) (r-∘ (plain rg) stopped)
plain (r-⊗ {t₁ = t₁} {t₂} rf (go-on (fm-gives rg))) = retrace (sym (erase-++ t₁ t₂)) (r-⊗ (plain rf) (go-on (fm-gives (plain rg))))
plain (r-⊗ {t₁ = t₁} {t₂} rf (go-on (fm-stop rg))) = retrace (sym (erase-++ t₁ t₂)) (r-⊗ (plain rf) (go-on (fm-stop (plain rg))))
plain (r-⊗ {t₁ = t₁} rf stopped) = retrace (sym (erase-++ t₁ [])) (r-⊗ (plain rf) stopped)
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
plain (r-cata {i = i} {t₁ = t₁} {t₂} rm (go-on ra)) =
  retrace (cong (free i ∷_) (sym (erase-++ t₁ t₂))) (r-cata (plain-map rm) (go-on (plain ra)))
plain (r-cata {i = i} {t₁ = t₁} rm stopped) =
  retrace (cong (free i ∷_) (sym (erase-++ t₁ []))) (r-cata (plain-map rm) stopped)
plain (r-cata-reuse {t₁ = t₁} {t₂} rm (go-on (fm-gives rg))) =
  retrace (sym (erase-++ t₁ t₂)) (r-cata-reuse (plain-map rm) (go-on (fm-gives (plain rg))))
plain (r-cata-reuse {t₁ = t₁} {t₂} rm (go-on (fm-stop rg))) =
  retrace (sym (erase-++ t₁ t₂)) (r-cata-reuse (plain-map rm) (go-on (fm-stop (plain rg))))
plain (r-cata-reuse {t₁ = t₁} rm stopped) = retrace (sym (erase-++ t₁ [])) (r-cata-reuse (plain-map rm) stopped)
plain (r-lend (fm-gives r)) = r-lend (fm-gives (plain r))
plain (r-lend (fm-stop r))  = r-lend (fm-stop (plain r))
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
plain (r-iter {t₁ = t₁} r (go-on done)) = retrace (sym (erase-++ t₁ [])) (r-iter (plain r) (go-on done))
plain (r-iter {t₁ = t₁} {t₂} r (go-on (again rn))) = retrace (sym (erase-++ t₁ t₂)) (r-iter (plain r) (go-on (again (plain rn))))
plain (r-iter {t₁ = t₁} r stopped) = retrace (sym (erase-++ t₁ [])) (r-iter (plain r) stopped)
plain r-exh = r-exh
plain (r-cut r q) = r-cut (plain r) (erase-≼ q)
plain (r-tmp r w p) = retrace (sym (erase-weave w)) (plain r)

plain-map (m-id r) = m-id (plain r)
plain-map m-one = m-one
plain-map m-b = m-b
plain-map m-μ = m-μ
plain-map (m-inl (fm-gives r)) = m-inl (fm-gives (plain-map r))
plain-map (m-inl (fm-stop r))  = m-inl (fm-stop (plain-map r))
plain-map (m-inr (fm-gives r)) = m-inr (fm-gives (plain-map r))
plain-map (m-inr (fm-stop r))  = m-inr (fm-stop (plain-map r))
plain-map (m-pair {t₁ = t₁} {t₂} r (go-on (fm-gives r′))) =
  retraceM (sym (erase-++ t₁ t₂)) (m-pair (plain-map r) (go-on (fm-gives (plain-map r′))))
plain-map (m-pair {t₁ = t₁} {t₂} r (go-on (fm-stop r′))) =
  retraceM (sym (erase-++ t₁ t₂)) (m-pair (plain-map r) (go-on (fm-stop (plain-map r′))))
plain-map (m-pair {t₁ = t₁} r stopped) = retraceM (sym (erase-++ t₁ [])) (m-pair (plain-map r) stopped)

------------------------------------------------------------------------
-- 2. THE LEDGER of live temporaries, by size: what one event does, then
-- lifted (`Free`).
------------------------------------------------------------------------

-- ledgers equal, or one below another, pointwise
_≗_ _≤̇_ : TL → TL → Set
L ≗ L′ = ∀ k → L k ≡ L′ k
L ≤̇ L′ = ∀ k → L k ≤ L′ k

-- one event respects both
tstep-≗ : ∀ x {L L′} → L ≗ L′ → tstep x L ≗ tstep x L′
tstep-≗ (alloc _)      e k = e k
tstep-≗ (free _)       e k = e k
tstep-≗ (peek _)       e k = e k
tstep-≗ (io _ _ _)     e k = e k
tstep-≗ (stp _ _)      e k = e k
tstep-≗ (tmp (tnew j)) e k = cong (_+ δn j k) (e k)
tstep-≗ (tmp (tdel j)) e k = cong (_∸ δn j k) (e k)

tstep-≤ : ∀ x {L L′} → L ≤̇ L′ → tstep x L ≤̇ tstep x L′
tstep-≤ (alloc _)      le k = le k
tstep-≤ (free _)       le k = le k
tstep-≤ (peek _)       le k = le k
tstep-≤ (io _ _ _)     le k = le k
tstep-≤ (stp _ _)      le k = le k
tstep-≤ (tmp (tnew j)) le k = +-monoˡ-≤ (δn j k) (le k)
tstep-≤ (tmp (tdel j)) le k = ∸-monoˡ-≤ (δn j k) (le k)

tpre-≗ : ∀ x {L L′} → L ≗ L′ → tpre x L → tpre x L′
tpre-≗ (alloc _)      e p = p
tpre-≗ (free _)       e p = p
tpre-≗ (peek _)       e p = p
tpre-≗ (io _ _ _)     e p = p
tpre-≗ (stp _ _)      e p = p
tpre-≗ (tmp (tnew j)) e p = p
tpre-≗ (tmp (tdel j)) e p = subst (1 ≤_) (e j) p

tpre-≤ : ∀ x {L L′} → L ≤̇ L′ → tpre x L → tpre x L′
tpre-≤ (alloc _)      le p = p
tpre-≤ (free _)       le p = p
tpre-≤ (peek _)       le p = p
tpre-≤ (io _ _ _)     le p = p
tpre-≤ (stp _ _)      le p = p
tpre-≤ (tmp (tnew j)) le p = p
tpre-≤ (tmp (tdel j)) le p = ≤-trans p (le j)

-- a kept event leaves the ledger as it is and asks nothing of it
kept-tstep : ∀ {x} → Kept x → ∀ L → tstep x L ≡ L
kept-tstep k-alloc L = refl
kept-tstep k-free  L = refl
kept-tstep k-peek  L = refl
kept-tstep k-io    L = refl
kept-tstep k-stp   L = refl

kept-tpre : ∀ {x} → Kept x → ∀ L → tpre x L
kept-tpre k-alloc L = tt
kept-tpre k-free  L = tt
kept-tpre k-peek  L = tt
kept-tpre k-io    L = tt
kept-tpre k-stp   L = tt

-- lifted: the laws of the action and of where it is defined
tplay-++ : ∀ t₁ t₂ L → tplay (t₁ ++ t₂) L ≡ tplay t₂ (tplay t₁ L)
tplay-++ t₁ t₂ L = foldl-++ (λ M x → tstep x M) L t₁ t₂

tplay-ext : ∀ t {L L′ : TL} → L ≗ L′ → tplay t L ≗ tplay t L′
tplay-ext = foldl-pres _≗_ (λ M x → tstep x M) tstep-≗

TOK-ext : ∀ t {L L′ : TL} → L ≗ L′ → TOK t L → TOK t L′
TOK-ext = Along-pres _≗_ tpre-≗ tstep-≗

-- more live temporaries never make a free illegal
TOK-mono : ∀ t {L L′ : TL} → L ≤̇ L′ → TOK t L → TOK t L′
TOK-mono = Along-pres _≤̇_ tpre-≤ tstep-≤

TOK-++ : ∀ t₁ t₂ L → TOK t₁ L → TOK t₂ (tplay t₁ L) → TOK (t₁ ++ t₂) L
TOK-++ = Along-++

TOK-≼ : ∀ {t′ t L} → t′ ≼ t → TOK t L → TOK t′ L
TOK-≼ = Along-≼

-- a trace with no temporaries leaves the ledger as it was
NoT-Bal : ∀ t → NoT t → TBal t
NoT-Bal t n = ( Along-all kept-tpre kept-tstep n none
              , λ k → cong (λ L → L k) (foldl-all (λ M x → tstep x M) kept-tstep n none) )


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
TPost-free (gives _ _) i t (ok , z) = ((tt , ok) , z)
TPost-free (stop _)    i t ok      = (tt , ok)

TPost-peek : ∀ {B} (o : Outcome B) i t → TPost o t → TPost o (peek i ∷ t)
TPost-peek (gives _ _) i t (ok , z) = ((tt , ok) , z)
TPost-peek (stop _)    i t ok      = (tt , ok)

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

  -- an event that asks nothing, first: as the rest
  skip : ∀ {P Q : Set} → P × Q → (⊤ × P) × Q
  skip (p , q) = ((tt , p) , q)

-- ★ two legal traces woven: legal, and the live temporaries are those of both
weave-ok : ∀ {t ts t′} → Weave tmp t ts t′ → ∀ (L₁ L₂ L : TL) → (∀ k → L k ≡ L₁ k + L₂ k)
         → TOK t L₁ → TOK (tmps ts) L₂
         → TOK t′ L × (∀ k → tplay t′ L k ≡ tplay t L₁ k + tplay (tmps ts) L₂ k)
weave-ok w-[] L₁ L₂ L e ok₁ ok₂ = (tt , e)
weave-ok (w-run {x = alloc _} w)  L₁ L₂ L e (_ , ok₁) ok₂ = skip (weave-ok w L₁ L₂ L e ok₁ ok₂)
weave-ok (w-run {x = free _} w)   L₁ L₂ L e (_ , ok₁) ok₂ = skip (weave-ok w L₁ L₂ L e ok₁ ok₂)
weave-ok (w-run {x = peek _} w)   L₁ L₂ L e (_ , ok₁) ok₂ = skip (weave-ok w L₁ L₂ L e ok₁ ok₂)
weave-ok (w-run {x = io _ _ _} w) L₁ L₂ L e (_ , ok₁) ok₂ = skip (weave-ok w L₁ L₂ L e ok₁ ok₂)
weave-ok (w-run {x = stp _ _} w)  L₁ L₂ L e (_ , ok₁) ok₂ = skip (weave-ok w L₁ L₂ L e ok₁ ok₂)
weave-ok (w-run {x = tmp (tnew k)} w) L₁ L₂ L e (_ , ok₁) ok₂ =
  skip (weave-ok w _ L₂ _ (λ j → trans (cong (_+ δn k j) (e j)) (swap+ (L₁ j) (L₂ j) (δn k j))) ok₁ ok₂)
weave-ok (w-run {x = tmp (tdel k)} w) L₁ L₂ L e (p , ok₁) ok₂
  with weave-ok w _ L₂ _ (λ j → trans (cong (_∸ δn k j) (e j)) (+-∸-comm (L₂ j) (δn-≤ k p j))) ok₁ ok₂
... | (ok , eq) = ((subst (1 ≤_) (sym (e k)) (≤-trans p (m≤m+n (L₁ k) (L₂ k))) , ok) , eq)
weave-ok (w-tmp {y = tnew k} w) L₁ L₂ L e ok₁ (_ , ok₂) =
  skip (weave-ok w L₁ _ _ (λ j → trans (cong (_+ δn k j) (e j)) (+-assoc (L₁ j) (L₂ j) (δn k j))) ok₁ ok₂)
weave-ok (w-tmp {y = tdel k} w) L₁ L₂ L e ok₁ (p , ok₂)
  with weave-ok w L₁ _ _ (λ j → trans (cong (_∸ δn k j) (e j)) (+-∸-assoc (L₁ j) (δn-≤ k p j))) ok₁ ok₂
... | (ok , eq) = ((subst (1 ≤_) (sym (e k)) (≤-trans p (m≤n+m (L₂ k) (L₁ k))) , ok) , eq)

weave-post : ∀ {B} (o : Outcome B) {t ts t′} → Weave tmp t ts t′ → TPost o t → TPost o (tmps ts) → TPost o t′
weave-post (gives _ _) w (ok₁ , z₁) (ok₂ , z₂) with weave-ok w none none none (λ _ → refl) ok₁ ok₂
... | (ok , eq) = (ok , λ k → trans (eq k) (cong₂ _+_ (z₁ k) (z₂ k)))
weave-post (stop _) w ok₁ ok₂ = fst (weave-ok w none none none (λ _ → refl) ok₁ ok₂)

------------------------------------------------------------------------
-- 4. ★ THE THEOREM: every run frees its temporaries, if it gives a value.
------------------------------------------------------------------------

private
  bal[] : TBal []
  bal[] = IsSubmonoid.ε-∈ balanced

  -- a stop adds no events: what it ran is the claim
  leg-[] : ∀ t → TLeg t → TLeg (t ++ [])
  leg-[] t l = IsSubmonoid.∙-∈ legal {t} {[]} l tt
tsound-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
           → RunMap ds F alg e G x n o t → TPost o t

tsound : ∀ {E A B} {f : Tm Γ E A B} {e v n o t} → Run ds f e v n o t → TPost o t
tsound r-id = bal[]
tsound (r-∘ {t₁ = t₁} {t₂} rg (go-on {o = o} rf)) = Bal-++ o t₁ t₂ (tsound rg) (tsound rf)
tsound (r-∘ {t₁ = t₁} rg stopped) = leg-[] t₁ (tsound rg)
tsound (r-⊗ {t₁ = t₁} {t₂} rf (go-on (fm-gives rg))) = IsSubmonoid.∙-∈ balanced {t₁} {t₂} (tsound rf) (tsound rg)
tsound (r-⊗ {t₁ = t₁} {t₂} rf (go-on (fm-stop rg))) = IsSubmonoid.∙-∈ legal {t₁} {t₂} (fst (tsound rf)) (tsound rg)
tsound (r-⊗ {t₁ = t₁} rf stopped) = leg-[] t₁ (tsound rf)
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
tsound r-In = ((tt , tt) , λ k → refl)
tsound r-Outμ = ((tt , tt) , λ k → refl)
tsound r-clo = bal[]
tsound (r-app q r) = tsound r
tsound (r-cata {i = i} {t₁ = t₁} {t₂} rm (go-on {o = o} ra)) = TPost-free o i (t₁ ++ t₂) (Bal-++ o t₁ t₂ (tsound-map rm) (tsound ra))
tsound (r-cata {A = A} {i = i} {t₁ = t₁} rm (stopped {y = y})) = TPost-free (stop {A} y) i (t₁ ++ []) (leg-[] t₁ (tsound-map rm))
tsound (r-cata-reuse {t₁ = t₁} {t₂} rm (go-on (fm-gives rg))) = IsSubmonoid.∙-∈ balanced {t₁} {t₂} (tsound-map rm) (tsound rg)
tsound (r-cata-reuse {t₁ = t₁} {t₂} rm (go-on (fm-stop rg))) = IsSubmonoid.∙-∈ legal {t₁} {t₂} (fst (tsound-map rm)) (tsound rg)
tsound (r-cata-reuse {t₁ = t₁} rm stopped) = leg-[] t₁ (tsound-map rm)
tsound (r-lend (fm-gives r)) = tsound r
tsound (r-lend (fm-stop r))  = tsound r
tsound (r-lift r) = tsound r
tsound (r-fst r) = tsound r
tsound (r-snd r) = tsound r
tsound (r-caseE₁ r) = tsound r
tsound (r-caseE₂ r) = tsound r
tsound (r-out {i = i} {o = o} {t = t} r) = TPost-peek o i t (tsound r)
tsound (r-copy {e = e} {n}) = NoT-Bal (snd (snd (copy e n))) (NoT-copy e n)
tsound (r-bapp q r) = tsound r
tsound r-op = ((tt , tt) , λ k → refl)
tsound r-halt = (tt , tt)
tsound (r-iter {t₁ = t₁} r (go-on done)) = IsSubmonoid.∙-∈ balanced {t₁} {[]} (tsound r) bal[]
tsound (r-iter {t₁ = t₁} {t₂} r (go-on (again {o = o} rn))) = Bal-++ o t₁ t₂ (tsound r) (tsound rn)
tsound (r-iter {t₁ = t₁} r stopped) = leg-[] t₁ (tsound r)
tsound r-exh = tt
tsound (r-cut {o = o} {t = t} r q) = TOK-≼ q (Post-Leg o t (tsound r))
tsound (r-tmp {o = o} r w p) = weave-post o w (tsound r) p

tsound-map (m-id r) = tsound r
tsound-map m-one = bal[]
tsound-map m-b = bal[]
tsound-map m-μ = bal[]
tsound-map (m-inl (fm-gives r)) = tsound-map r
tsound-map (m-inl (fm-stop r))  = tsound-map r
tsound-map (m-inr (fm-gives r)) = tsound-map r
tsound-map (m-inr (fm-stop r))  = tsound-map r
tsound-map (m-pair {t₁ = t₁} {t₂} r (go-on (fm-gives r′))) = IsSubmonoid.∙-∈ balanced {t₁} {t₂} (tsound-map r) (tsound-map r′)
tsound-map (m-pair {t₁ = t₁} {t₂} r (go-on (fm-stop r′))) = IsSubmonoid.∙-∈ legal {t₁} {t₂} (fst (tsound-map r)) (tsound-map r′)
tsound-map (m-pair {t₁ = t₁} r stopped) = leg-[] t₁ (tsound-map r)
