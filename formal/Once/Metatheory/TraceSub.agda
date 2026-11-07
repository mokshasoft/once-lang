{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.TraceSub — agreement at every depth UP TO RUNNING OUT is
-- `⊑ᵗ` (D347; plan 0.123 A.4).
--
-- `Depth` (`Once.Metatheory.Trace`) says the first `n` visible steps of two
-- traces agree, for every `n`, and `fromDepth` makes that weak bisimilarity.
-- Its twin here lets the first trace stop early by running out: at every
-- depth, what `t` shows is what `t′` shows, or `t` ended `exhausted` after
-- calls that `t′` makes first. `fromSub` makes that `t ⊑ᵗ t′`, by the same
-- route: the first visible step is matched first-order, and the corecursive
-- call sits directly under the pair.
------------------------------------------------------------------------

module Once.Metatheory.TraceSub where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Signature using (Event)
open import Once.Spec.Delay using (_⇓_)
open import Once.Spec.Trace
  using (End; exhausted; Tr; module Tr; EndRel; StepRel; _⊑ᵗ⟨_⟩_; module _⊑ᵗ⟨_⟩_)
open import Once.Metatheory.Trace
  using (Obs; pre; ObsR; MaybeEnd; end≈; FirstIs; firstOf; seeFirst; deeper; shallower)

open Tr using (next)
open _⊑ᵗ⟨_⟩_ using (sound; complete)

private
  S : Set → Set
  S X = End X ⊎ (Event × Tr X)

  ∷-inj : ∀ {v v′ : Event} {l l′} → _≡_ {A = List Event} (v ∷ l) (v′ ∷ l′) → v ≡ v′ × l ≡ l′
  ∷-inj refl = refl , refl

  []≢∷ : ∀ {v : Event} {l} {C : Set} → _≡_ {A = List Event} [] (v ∷ l) → C
  []≢∷ ()

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  nothing≢just : ∀ {A : Set} {a : A} {C : Set} → nothing ≡ just a → C
  nothing≢just ()

module _ {X : Set} {R : X → X → Set} where

  -- What `t` shows against what `t′` shows: the same, or `t` ran out after a
  -- prefix of `t′`'s calls.
  ObsEx : Obs X → Obs X → Set
  ObsEx o o′ = ObsR R o o′ ⊎ (proj₂ o ≡ just exhausted × ∃[ rest ] (proj₁ o ++ rest ≡ proj₁ o′))

  -- `t` ran out after the calls `es`, and `t′` makes them first.
  RanOut : Obs X → Tr X → Set
  RanOut o t′ = proj₂ o ≡ just exhausted × pre (length (proj₁ o)) t′ ⇓ (proj₁ o , nothing)

  DepthSub : Tr X → Tr X → Set
  DepthSub t t′ = ∀ n →
      (∀ o → pre n t ⇓ o → RanOut o t′ ⊎ ∃[ o′ ] (pre n t′ ⇓ o′ × ObsR R o o′))
    × (∀ o′ → pre n t′ ⇓ o′ → ∃[ o ] (pre n t ⇓ o × ObsEx o o′))

  -- After the same call on both sides, the rests agree up to running out.
  restSub : ∀ {t t′ : Tr X} {v t₁ t₁′} → DepthSub t t′ → next t ⇓ inj₂ (v , t₁) → next t′ ⇓ inj₂ (v , t₁′)
          → DepthSub t₁ t₁′
  restSub {t} {t′} {v} {t₁} {t₁′} p a a′ n = fw , bw
    where
      fw : ∀ o → pre n t₁ ⇓ o → RanOut o t₁′ ⊎ ∃[ o′ ] (pre n t₁′ ⇓ o′ × ObsR R o o′)
      fw o o⇓ = pick (proj₁ (p (suc n)) _ (deeper {t = t} a o⇓))
        where
          ran : pre (length (v ∷ proj₁ o)) t′ ⇓ (v ∷ proj₁ o , nothing) → pre (length (proj₁ o)) t₁′ ⇓ (proj₁ o , nothing)
          ran r = fin (shallower {t = t′} a′ r)
            where fin : ∃[ o₁ ] (pre (length (proj₁ o)) t₁′ ⇓ o₁ × (v ∷ proj₁ o , nothing) ≡ (v ∷ proj₁ o₁ , proj₂ o₁))
                      → pre (length (proj₁ o)) t₁′ ⇓ (proj₁ o , nothing)
                  fin (o₁ , o₁⇓ , refl) = o₁⇓
          same₁ : ∀ {o″} → ObsR R (v ∷ proj₁ o , proj₂ o) o″
                → ∃[ o₁ ] (pre n t₁′ ⇓ o₁ × o″ ≡ (v ∷ proj₁ o₁ , proj₂ o₁))
                → ∃[ o′ ] (pre n t₁′ ⇓ o′ × ObsR R o o′)
          same₁ (eq , me) (o₁ , o₁⇓ , refl) = o₁ , o₁⇓ , proj₂ (∷-inj eq) , me
          pick : RanOut (v ∷ proj₁ o , proj₂ o) t′ ⊎ ∃[ o″ ] (pre (suc n) t′ ⇓ o″ × ObsR R (v ∷ proj₁ o , proj₂ o) o″)
               → RanOut o t₁′ ⊎ ∃[ o′ ] (pre n t₁′ ⇓ o′ × ObsR R o o′)
          pick (inj₁ (q , r))         = inj₁ (q , ran r)
          pick (inj₂ (o″ , o″⇓ , r)) = inj₂ (same₁ r (shallower {t = t′} a′ o″⇓))
      bw : ∀ o′ → pre n t₁′ ⇓ o′ → ∃[ o ] (pre n t₁ ⇓ o × ObsEx o o′)
      bw o′ o′⇓ = step₁ (proj₂ (p (suc n)) _ (deeper {t = t′} a′ o′⇓))
        where
          fin : ∀ {o″} → ObsEx o″ (v ∷ proj₁ o′ , proj₂ o′)
              → ∃[ o₁ ] (pre n t₁ ⇓ o₁ × o″ ≡ (v ∷ proj₁ o₁ , proj₂ o₁))
              → ∃[ o ] (pre n t₁ ⇓ o × ObsEx o o′)
          fin (inj₁ (eq , me))            (o₁ , o₁⇓ , refl) = o₁ , o₁⇓ , inj₁ (proj₂ (∷-inj eq) , me)
          fin (inj₂ (q , rest , req))     (o₁ , o₁⇓ , refl) = o₁ , o₁⇓ , inj₂ (q , rest , proj₂ (∷-inj req))
          step₁ : ∃[ o″ ] (pre (suc n) t ⇓ o″ × ObsEx o″ (v ∷ proj₁ o′ , proj₂ o′)) → ∃[ o ] (pre n t₁ ⇓ o × ObsEx o o′)
          step₁ (o″ , o″⇓ , r) = fin r (shallower {t = t} a o″⇓)

  -- THE FIRST STEP OF `t`: it ran out, or `t′` takes a related step.
  FwdOut : Tr X → Tr X → S X → Set
  FwdOut t t′ a = a ≡ inj₁ exhausted
             ⊎ ((∃[ e ] ∃[ e′ ] (a ≡ inj₁ e × next t′ ⇓ inj₁ e′ × EndRel R e e′))
               ⊎ ∃[ v ] ∃[ t₁ ] ∃[ t₁′ ] (a ≡ inj₂ (v , t₁) × next t′ ⇓ inj₂ (v , t₁′) × DepthSub t₁ t₁′))

  fwdFirst : ∀ {t t′ : Tr X} → DepthSub t t′ → ∀ a → next t ⇓ a → FwdOut t t′ a
  fwdFirst {t} {t′} p (inj₁ e) a = one (seeFirst {t = t} (inj₁ e) a)
    where
      decide : ∀ {o′} (s′ : S X) → next t′ ⇓ s′ → FirstIs s′ o′ → ObsR R ([] , just e) o′
             → ∃[ e₁ ] ∃[ e′ ] (inj₁ e ≡ inj₁ e₁ × next t′ ⇓ inj₁ e′ × EndRel R e₁ e′)
      decide (inj₁ e′)      a′ refl (_ , end≈ r) = e , e′ , refl , a′ , r
      decide (inj₂ (v , _)) a′ refl (eq , _)     = []≢∷ eq
      two : RanOut ([] , just e) t′ ⊎ ∃[ o′ ] (pre 1 t′ ⇓ o′ × ObsR R ([] , just e) o′) → FwdOut t t′ (inj₁ e)
      two (inj₁ (q , _))         = inj₁ (cong inj₁ (just-inj q))
      two (inj₂ (o′ , o′⇓ , r)) = three (firstOf t′ o′⇓)
        where three : ∃[ s′ ] (next t′ ⇓ s′ × FirstIs s′ o′) → FwdOut t t′ (inj₁ e)
              three (s′ , a′ , fi) = inj₂ (inj₁ (decide s′ a′ fi r))
      one : ∃[ o ] (pre 1 t ⇓ o × FirstIs (inj₁ e) o) → FwdOut t t′ (inj₁ e)
      one (o , o⇓ , refl) = two (proj₁ (p 1) _ o⇓)
  fwdFirst {t} {t′} p (inj₂ (v , t₁)) a = one (seeFirst {t = t} (inj₂ (v , t₁)) a)
    where
      decide : ∀ {o′} (s′ : S X) → next t′ ⇓ s′ → FirstIs s′ o′ → ObsR R (v ∷ [] , nothing) o′
             → ∃[ v₁ ] ∃[ t₂ ] ∃[ t₁′ ] (inj₂ (v , t₁) ≡ inj₂ (v₁ , t₂) × next t′ ⇓ inj₂ (v₁ , t₁′) × DepthSub t₂ t₁′)
      decide (inj₁ e′)         a′ refl (eq , _) = []≢∷ (sym eq)
      decide (inj₂ (v′ , t₁′)) a′ refl (eq , _) = fin (proj₁ (∷-inj eq)) a′
        where fin : v ≡ v′ → next t′ ⇓ inj₂ (v′ , t₁′)
                  → ∃[ v₁ ] ∃[ t₂ ] ∃[ t₁″ ] (inj₂ (v , t₁) ≡ inj₂ (v₁ , t₂) × next t′ ⇓ inj₂ (v₁ , t₁″) × DepthSub t₂ t₁″)
              fin refl a″ = v , t₁ , t₁′ , refl , a″ , restSub {t = t} {t′} p a a″
      two : RanOut (v ∷ [] , nothing) t′ ⊎ ∃[ o′ ] (pre 1 t′ ⇓ o′ × ObsR R (v ∷ [] , nothing) o′) → FwdOut t t′ (inj₂ (v , t₁))
      two (inj₁ (q , _))         = nothing≢just q
      two (inj₂ (o′ , o′⇓ , r)) = three (firstOf t′ o′⇓)
        where three : ∃[ s′ ] (next t′ ⇓ s′ × FirstIs s′ o′) → FwdOut t t′ (inj₂ (v , t₁))
              three (s′ , a′ , fi) = inj₂ (inj₂ (decide s′ a′ fi r))
      one : ∃[ o ] (pre 1 t ⇓ o × FirstIs (inj₂ (v , t₁)) o) → FwdOut t t′ (inj₂ (v , t₁))
      one (o , o⇓ , refl) = two (proj₁ (p 1) _ o⇓)

  -- THE FIRST STEP OF `t′`: `t` ran out at once, or takes a related step.
  BwdOut : Tr X → Tr X → S X → Set
  BwdOut t t′ b = next t ⇓ inj₁ exhausted
             ⊎ ((∃[ e ] ∃[ e′ ] (b ≡ inj₁ e′ × next t ⇓ inj₁ e × EndRel R e e′))
               ⊎ ∃[ v ] ∃[ t₁ ] ∃[ t₁′ ] (b ≡ inj₂ (v , t₁′) × next t ⇓ inj₂ (v , t₁) × DepthSub t₁ t₁′))

  bwdFirst : ∀ {t t′ : Tr X} → DepthSub t t′ → ∀ b → next t′ ⇓ b → BwdOut t t′ b
  bwdFirst {t} {t′} p (inj₁ e′) b⇓ = one (seeFirst {t = t′} (inj₁ e′) b⇓)
    where
      decide : ∀ {o} (s : S X) → next t ⇓ s → FirstIs s o → ObsEx o ([] , just e′) → BwdOut t t′ (inj₁ e′)
      decide (inj₁ e)       a refl (inj₁ (_ , end≈ r)) = inj₂ (inj₁ (e , e′ , refl , a , r))
      decide (inj₁ e)       a refl (inj₂ (q , _))      = inj₁ (subst (λ x → next t ⇓ inj₁ x) (just-inj q) a)
      decide (inj₂ (v , _)) a refl (inj₁ (eq , _))     = []≢∷ (sym eq)
      decide (inj₂ (v , _)) a refl (inj₂ (q , _))      = nothing≢just q
      one : ∃[ o′ ] (pre 1 t′ ⇓ o′ × FirstIs (inj₁ e′) o′) → BwdOut t t′ (inj₁ e′)
      one (o′ , o′⇓ , refl) = two (proj₂ (p 1) _ o′⇓)
        where two : ∃[ o ] (pre 1 t ⇓ o × ObsEx o ([] , just e′)) → BwdOut t t′ (inj₁ e′)
              two (o , o⇓ , r) = three (firstOf t o⇓)
                where three : ∃[ s ] (next t ⇓ s × FirstIs s o) → BwdOut t t′ (inj₁ e′)
                      three (s , a , fi) = decide s a fi r
  bwdFirst {t} {t′} p (inj₂ (v , t₁′)) b⇓ = one (seeFirst {t = t′} (inj₂ (v , t₁′)) b⇓)
    where
      decide : ∀ {o} (s : S X) → next t ⇓ s → FirstIs s o → ObsEx o (v ∷ [] , nothing) → BwdOut t t′ (inj₂ (v , t₁′))
      decide (inj₁ e)         a refl (inj₁ (eq , _)) = []≢∷ eq
      decide (inj₁ e)         a refl (inj₂ (q , _))  = inj₁ (subst (λ x → next t ⇓ inj₁ x) (just-inj q) a)
      decide (inj₂ (v₁ , t₁)) a refl (inj₁ (eq , _)) = fin (proj₁ (∷-inj eq)) a
        where fin : v₁ ≡ v → next t ⇓ inj₂ (v₁ , t₁) → BwdOut t t′ (inj₂ (v , t₁′))
              fin refl a″ = inj₂ (inj₂ (v , t₁ , t₁′ , refl , a″ , restSub {t = t} {t′} p a″ b⇓))
      decide (inj₂ (v₁ , _))  a refl (inj₂ (q , _))  = nothing≢just q
      one : ∃[ o′ ] (pre 1 t′ ⇓ o′ × FirstIs (inj₂ (v , t₁′)) o′) → BwdOut t t′ (inj₂ (v , t₁′))
      one (o′ , o′⇓ , refl) = two (proj₂ (p 1) _ o′⇓)
        where two : ∃[ o ] (pre 1 t ⇓ o × ObsEx o (v ∷ [] , nothing)) → BwdOut t t′ (inj₂ (v , t₁′))
              two (o , o⇓ , r) = three (firstOf t o⇓)
                where three : ∃[ s ] (next t ⇓ s × FirstIs s o) → BwdOut t t′ (inj₂ (v , t₁′))
                      three (s , a , fi) = decide s a fi r

-- THE CONVERSION: agreement at every depth up to running out is `⊑ᵗ`.
fromSub : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → DepthSub {X} {R} t t′ → t ⊑ᵗ⟨ R ⟩ t′
fwdS : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → DepthSub {X} {R} t t′ → ∀ a → next t ⇓ a
     → a ≡ inj₁ exhausted ⊎ ∃[ b ] (next t′ ⇓ b × StepRel R (λ u u′ → u ⊑ᵗ⟨ R ⟩ u′) a b)
bwdS : ∀ {X} {R : X → X → Set} {t t′ : Tr X} → DepthSub {X} {R} t t′ → ∀ b → next t′ ⇓ b
     → next t ⇓ inj₁ exhausted ⊎ ∃[ a ] (next t ⇓ a × StepRel R (λ u u′ → u ⊑ᵗ⟨ R ⟩ u′) a b)
sound    (fromSub p) a a⇓ = fwdS p a a⇓
complete (fromSub p) b b⇓ = bwdS p b b⇓
fwdS p a a⇓ with fwdFirst p a a⇓
... | inj₁ ex = inj₁ ex
... | inj₂ (inj₁ (e , e′ , refl , a′ , r))             = inj₂ (inj₁ e′ , a′ , r)
... | inj₂ (inj₂ (v , t₁ , t₁′ , refl , a′ , rest))    = inj₂ (inj₂ (v , t₁′) , a′ , refl , fromSub rest)
bwdS p b b⇓ with bwdFirst p b b⇓
... | inj₁ ex = inj₁ ex
... | inj₂ (inj₁ (e , e′ , refl , a , r))              = inj₂ (inj₁ e , a , r)
... | inj₂ (inj₂ (v , t₁ , t₁′ , refl , a , rest))     = inj₂ (inj₂ (v , t₁) , a , refl , fromSub rest)
