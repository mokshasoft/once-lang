{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FuelTrace — two step machines whose fuelled runs agree at
-- every BUDGET have weakly bisimilar traces (plan 0.119 D5).
--
-- A machine's run with fuel `n` (`runN`) is what it does in `n` steps: its
-- calls, and how it ended if it did. The budget agreement says: for every
-- `k`, some run of each machine shows the same calls and end, and where
-- neither has ended both have taken at least `k` steps. That is all the
-- backend can say about a program that need not stop — and it is enough:
-- a prefix of either trace arrives after finitely many steps, and a budget
-- above that count reads it off the other machine's run (`Depth`, then
-- `fromDepth`). Everything here is finite: `Depth` is arrival-based.
------------------------------------------------------------------------

module Once.Adequacy.FuelTrace where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-total)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Signature using (Event)
open import Once.Spec.Delay using (Delay; module Delay; now; _⇓_; now⇓; later⇓)
open import Once.Spec.Trace using (End; returned; halted; exhausted; Tr; module Tr; returned≈; halted≈; exhausted≈; _≈ᵗ⟨_⟩_)
open import Once.Metatheory.Trace
  using (bindD; bind⇓; bind⇓⁻; nowInv; ⇓-det; pre; preStep; Depth; ObsR; MaybeEnd; cut≈; end≈; fromDepth)
open import Once.Adequacy.MachineTrace using (Step; silent; emit; stop; stuck; listTr; never; module Machine)

open Delay using (step)
open Tr using (next)

------------------------------------------------------------------------
-- Observations, their prefix order, and reading the first `n` calls
------------------------------------------------------------------------

Obs : Set
Obs = List Event × Maybe (End ⊤)

_⊕_ : List Event → Obs → Obs
vs ⊕ o = (vs ++ proj₁ o) , proj₂ o

-- `o` is a prefix of `o′`: a run cut short, extended; or the same ended run.
data _≼_ : Obs → Obs → Set where
  ≼-cut : ∀ es fs (e : Maybe (End ⊤)) → (es , nothing) ≼ (es ++ fs , e)
  ≼-end : ∀ es (e : End ⊤) → (es , just e) ≼ (es , just e)

-- The first `n` calls of an observation, and whether it determines them (it
-- has `n` calls, or it ended first).
cutAt : ℕ → Obs → Obs
cutAt zero    o              = [] , nothing
cutAt (suc n) ([] , e)       = [] , e
cutAt (suc n) (v ∷ es , e)   = v ∷ proj₁ (cutAt n (es , e)) , proj₂ (cutAt n (es , e))

IsJust : Maybe (End ⊤) → Set
IsJust (just _) = ⊤
IsJust nothing  = ⊥

Det : ℕ → Obs → Set
Det zero    o            = ⊤
Det (suc n) ([] , e)     = IsJust e
Det (suc n) (v ∷ es , e) = Det n (es , e)

Det-ended : ∀ n vs (e : End ⊤) → Det n (vs , just e)
Det-ended zero    vs       e = tt
Det-ended (suc n) []       e = tt
Det-ended (suc n) (v ∷ vs) e = Det-ended n vs e

-- An extension determines what its prefix determined, the same way.
≼-det : ∀ n {o o′} → o ≼ o′ → Det n o → Det n o′ × cutAt n o ≡ cutAt n o′
≼-det zero    _                     _ = tt , refl
≼-det (suc n) (≼-cut [] fs e)       ()
≼-det (suc n) (≼-cut (v ∷ es) fs e) d with ≼-det n (≼-cut es fs e) d
... | d′ , q = d′ , cong (λ c → v ∷ proj₁ c , proj₂ c) q
≼-det (suc n) (≼-end es e)          d = d , refl

-- An ended observation has no proper extension.
≼-ended : ∀ {es e o′} → (es , just e) ≼ o′ → o′ ≡ (es , just e)
≼-ended (≼-end es e) = refl

ended-≼ : ∀ (o : Obs) {o′} {e} → proj₂ o ≡ just e → o ≼ o′ → o′ ≡ o
ended-≼ (es , just e)  refl (≼-end .es .e) = refl
ended-≼ (es , nothing) ()   _

private
  ⊕-≼ : ∀ vs {o o′} → o ≼ o′ → (vs ⊕ o) ≼ (vs ⊕ o′)
  ⊕-≼ vs (≼-cut es fs e) = subst (λ l → (vs ++ es , nothing) ≼ (l , e)) (assoc vs es fs) (≼-cut (vs ++ es) fs e)
    where
      assoc : ∀ (a b c : List Event) → (a ++ b) ++ c ≡ a ++ (b ++ c)
      assoc []      b c = refl
      assoc (x ∷ a) b c = cong (x ∷_) (assoc a b c)
  ⊕-≼ vs (≼-end es e) = ≼-end (vs ++ es) e

  bot-≼ : ∀ o → ([] , nothing) ≼ o
  bot-≼ (es , e) = ≼-cut [] es e

  -- Two delays that take the same first step arrive at the same values.
  ⇓-step : ∀ {A : Set} {d d′ : Delay A} {a} → step d ≡ step d′ → d ⇓ a → d′ ⇓ a
  ⇓-step q (now⇓ e)     = now⇓ (trans (sym q) e)
  ⇓-step q (later⇓ e x) = later⇓ (trans (sym q) e) x

------------------------------------------------------------------------
-- One machine: its fuelled run, and the prefixes of its trace
------------------------------------------------------------------------

module Fuel {S : Set} (δ : S → Step S) where
  open Machine δ using (tr; go; trace)

  runN : ℕ → S → Obs
  runS : ℕ → Step S → Obs
  runN zero    s = [] , nothing
  runN (suc n) s = runS n (δ s)
  runS n (silent s′)  = runN n s′
  runS n (emit vs s′) = vs ⊕ runN n s′
  runS n (stop vs e)  = vs , just e
  runS n stuck        = [] , nothing

  -- More fuel, a longer run.
  runN-mono : ∀ {N N′} s → N ≤ N′ → runN N s ≼ runN N′ s
  runS-mono : ∀ {N N′} (st : Step S) → N ≤ N′ → runS N st ≼ runS N′ st
  runN-mono {zero}  {N′}     s _         = bot-≼ (runN N′ s)
  runN-mono {suc N} {suc N′} s (s≤s le) = runS-mono (δ s) le
  runS-mono (silent s′)  le = runN-mono s′ le
  runS-mono (emit vs s′) le = ⊕-≼ vs (runN-mono s′ le)
  runS-mono (stop vs e)  le = ≼-end vs e
  runS-mono stuck        le = ≼-cut [] [] nothing

  -- A finite list's prefixes.
  pre-listTr : ∀ n vs (e : End ⊤) → pre n (listTr vs e) ⇓ cutAt n (vs , just e)
  pre-listTr zero    vs       e = now⇓ refl
  pre-listTr (suc n) []       e = bind⇓ (now⇓ refl) (now⇓ refl)
  pre-listTr (suc n) (v ∷ vs) e = bind⇓ (now⇓ refl) (bind⇓ (pre-listTr n vs e) (now⇓ refl))

  -- A run that determines the first `n` calls: the trace's prefix arrives at them.
  pre-run : ∀ n pend N s → Det n (pend ⊕ runN N s) → pre n (tr pend s) ⇓ cutAt n (pend ⊕ runN N s)
  pre-go  : ∀ n N (st : Step S) → Det (suc n) (runS N st)
          → bindD (go st) (preStep n) ⇓ cutAt (suc n) (runS N st)
  pre-run zero    pend       N       s d = now⇓ refl
  pre-run (suc n) (v ∷ vs)   N       s d = bind⇓ (now⇓ refl) (bind⇓ (pre-run n vs N s d) (now⇓ refl))
  pre-run (suc n) []         zero    s ()
  pre-run (suc n) []         (suc N) s d = pre-go n N (δ s) d
  pre-go n N (silent s′)       d = later⇓ refl (pre-run (suc n) [] N s′ d)
  pre-go n N (emit [] s′)      d = later⇓ refl (pre-run (suc n) [] N s′ d)
  pre-go n N (emit (v ∷ vs) s′) d = bind⇓ (now⇓ refl) (bind⇓ (pre-run n vs N s′ d) (now⇓ refl))
  pre-go n N (stop [] e)       d = bind⇓ (now⇓ refl) (now⇓ refl)
  pre-go n N (stop (v ∷ vs) e) d = bind⇓ (now⇓ refl) (bind⇓ (pre-listTr n vs e) (now⇓ refl))
  pre-go n N stuck             ()

  -- …and back: a prefix that arrives was read off some fuelled run.
  private
    inj₂-inj : ∀ {A B : Set} {x y : B} → _≡_ {A = A ⊎ B} (inj₂ x) (inj₂ y) → x ≡ y
    inj₂-inj refl = refl

    clash : ∀ {A B C : Set} {x : A} {y : B} → _≡_ {A = A ⊎ B} (inj₂ y) (inj₁ x) → C
    clash ()

    never-⇓ : ∀ {A B : Set} {f : A → Delay B} {d : Delay B} {b} → step d ≡ step (bindD never f) → d ⇓ b → ⊥
    never-⇓ q (now⇓ e)     with trans (sym q) e
    ... | ()
    never-⇓ {f = f} q (later⇓ e x) = never-⇓ {f = f} (cong step (inj₂-inj (trans (sym e) q))) x

  run-pre : ∀ n pend s {o} → pre n (tr pend s) ⇓ o
          → ∃[ N ] (Det n (pend ⊕ runN N s) × cutAt n (pend ⊕ runN N s) ≡ o)
  run-go  : ∀ n (st : Step S) {d o} → step d ≡ step (bindD (go st) (preStep n)) → d ⇓ o
          → ∃[ N ] (Det (suc n) (runS N st) × cutAt (suc n) (runS N st) ≡ o)
  run-pre zero    pend     s a = 0 , tt , nowInv a
  run-pre (suc n) (v ∷ vs) s a with bind⇓⁻ (next (tr (v ∷ vs) s)) (preStep n) a
  ... | x , ax , px with ⇓-det ax (now⇓ refl)
  ...   | refl with bind⇓⁻ (pre n (tr vs s)) (λ o → now (v ∷ proj₁ o , proj₂ o)) px
  ...     | o₁ , a₁ , n₁ with run-pre n vs s a₁
  ...       | N , d , q = N , d , trans (cong (λ c → v ∷ proj₁ c , proj₂ c) q) (nowInv n₁)
  run-pre (suc n) []       s a with run-go n (δ s) refl a
  ... | N , d , q = suc N , d , q
  run-go n (silent s′) q (now⇓ e) = ⊥-elim (clash (trans (sym q) e))
  run-go n (silent s′) q (later⇓ e x) with run-go n (δ s′) (cong step (inj₂-inj (trans (sym e) q))) x
  ... | N , d , r = suc N , d , r
  run-go n (emit [] s′) q (now⇓ e) = ⊥-elim (clash (trans (sym q) e))
  run-go n (emit [] s′) q (later⇓ e x) with run-go n (δ s′) (cong step (inj₂-inj (trans (sym e) q))) x
  ... | N , d , r = suc N , d , r
  run-go n (emit (v ∷ vs) s′) {d} q a with run-pre (suc n) (v ∷ vs) s′ (⇓-step q′ a)
    where
      q′ : step d ≡ step (pre (suc n) (tr (v ∷ vs) s′))
      q′ = q
  ... | N , d′ , r = N , d′ , r
  run-go n (stop vs e) {d} q a =
    0 , Det-ended (suc n) vs e , ⇓-det (pre-go n 0 (stop vs e) (Det-ended (suc n) vs e)) (⇓-step q a)
  run-go n stuck {d} q a = ⊥-elim (never-⇓ {f = preStep n} q a)

  -- A prefix, read off any long enough run — or any run that ended.
  align : ∀ n s {N n₁ o} → Det n (runN N s) → cutAt n (runN N s) ≡ o
        → (proj₂ (runN n₁ s) ≡ nothing → N ≤ n₁)
        → Det n (runN n₁ s) × cutAt n (runN n₁ s) ≡ o
  align n s {N} {n₁} d q long = pick (proj₂ (runN n₁ s)) refl
    where
      viaMono : N ≤ n₁ → Det n (runN n₁ s) × cutAt n (runN n₁ s) ≡ _
      viaMono le with ≼-det n (runN-mono s le) d
      ... | d′ , q′ = d′ , trans (sym q′) q
      pick : (e : Maybe (End ⊤)) → proj₂ (runN n₁ s) ≡ e → Det n (runN n₁ s) × cutAt n (runN n₁ s) ≡ _
      pick nothing  eq = viaMono (long eq)
      pick (just e) eq with ≤-total N n₁
      ... | inj₁ le = viaMono le
      ... | inj₂ le =
        subst (λ r → Det n r × cutAt n r ≡ _) (ended-≼ (runN n₁ s) eq (runN-mono s le)) (d , q)

------------------------------------------------------------------------
-- Two machines that agree at every budget have weakly bisimilar traces
------------------------------------------------------------------------

module Agree {S₁ S₂ : Set} (δ₁ : S₁ → Step S₁) (δ₂ : S₂ → Step S₂) where
  module F₁ = Fuel δ₁
  module F₂ = Fuel δ₂
  open Machine δ₁ using () renaming (trace to trace₁)
  open Machine δ₂ using () renaming (trace to trace₂)

  -- At budget `k`: runs of the two that show the same, and that have each
  -- taken at least `k` steps if they have not ended.
  BudgetAgree : S₁ → S₂ → Set
  BudgetAgree s₁ s₂ =
    ∀ k → Σ[ n₁ ∈ ℕ ] Σ[ n₂ ∈ ℕ ] (F₁.runN n₁ s₁ ≡ F₂.runN n₂ s₂)
                                × (proj₂ (F₁.runN n₁ s₁) ≡ nothing → k ≤ n₁ × k ≤ n₂)

  private
    endRefl : ∀ (e : Maybe (End ⊤)) → MaybeEnd _≡_ e e
    endRefl nothing             = cut≈
    endRefl (just (returned x)) = end≈ (returned≈ refl)
    endRefl (just halted)       = end≈ halted≈
    endRefl (just exhausted)    = end≈ exhausted≈

    obsRefl : ∀ (o : Obs) → ObsR _≡_ o o
    obsRefl o = refl , endRefl (proj₂ o)

  agree-depth : ∀ {s₁ s₂} → BudgetAgree s₁ s₂ → Depth _≡_ (trace₁ s₁) (trace₂ s₂)
  agree-depth {s₁} {s₂} ag n = fw , bw
    where
      fw : ∀ o → pre n (trace₁ s₁) ⇓ o → ∃[ o′ ] (pre n (trace₂ s₂) ⇓ o′ × ObsR _≡_ o o′)
      fw o a with F₁.run-pre n [] s₁ a
      ... | N , d , q with ag N
      ...   | n₁ , n₂ , eq , long with F₁.align n s₁ {N} {n₁} d q (λ c → proj₁ (long c))
      ...     | d₁ , q₁ =
        o , subst (λ c → pre n (trace₂ s₂) ⇓ c) q₂ (F₂.pre-run n [] n₂ s₂ (subst (Det n) eq d₁)) , obsRefl o
        where
          q₂ : cutAt n (F₂.runN n₂ s₂) ≡ o
          q₂ = trans (cong (cutAt n) (sym eq)) q₁
      bw : ∀ o′ → pre n (trace₂ s₂) ⇓ o′ → ∃[ o ] (pre n (trace₁ s₁) ⇓ o × ObsR _≡_ o o′)
      bw o′ a with F₂.run-pre n [] s₂ a
      ... | N , d , q with ag N
      ...   | n₁ , n₂ , eq , long with F₂.align n s₂ {N} {n₂} d q (λ c → proj₂ (long (trans (cong proj₂ eq) c)))
      ...     | d₂ , q₂ =
        o′ , subst (λ c → pre n (trace₁ s₁) ⇓ c) q₁ (F₁.pre-run n [] n₁ s₁ (subst (Det n) (sym eq) d₂)) , obsRefl o′
        where
          q₁ : cutAt n (F₁.runN n₁ s₁) ≡ o′
          q₁ = trans (cong (cutAt n) eq) q₂

  agree-≈ : ∀ {s₁ s₂} → BudgetAgree s₁ s₂ → trace₁ s₁ ≈ᵗ⟨ _≡_ ⟩ trace₂ s₂
  agree-≈ ag = fromDepth (agree-depth ag)
