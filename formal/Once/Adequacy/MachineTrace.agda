{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MachineTrace — the trace of a machine (D320, plan 0.119 §7 D4).
--
-- A machine is a function from a state to what its next step SHOWS: a silent
-- step, some calls and a next state, an end (after some calls), or no next
-- state at all (stuck). Its trace (`Spec.Trace.Tr ⊤`) is read off by
-- corecursion: a silent step is a step of the `Delay`, a call a visible step,
-- an end the trace's end. A stuck machine shows nothing more, ever: it never
-- arrives at an end, so a broken binary is never "returned".
--
-- No fuel is involved: a run that never makes another call is a `Delay` that
-- never arrives, which is what the Spec says it is.
--
-- `reaches-≈`: a run that REACHES its end — finitely many steps, the calls
-- `es`, then the end `e` — has the finite trace `listTr es e`, up to weak
-- bisimilarity. That is what a terminating simulation proves.
------------------------------------------------------------------------

module Once.Adequacy.MachineTrace where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Spec.Signature using (Event)
open import Once.Spec.Delay using (Delay; module Delay; now; _⇓_; now⇓; later⇓)
open import Once.Spec.Trace using (End; returned; halted; exhausted; Tr; module Tr; EndRel; returned≈; halted≈; exhausted≈; StepRel; _≈ᵗ⟨_⟩_; module _≈ᵗ⟨_⟩_)
open import Once.Metatheory.Trace using (⇓-det)

open Delay using (step)
open Tr using (next)
open _≈ᵗ⟨_⟩_ using (same)

-- What one step of a machine shows.
data Step (S : Set) : Set where
  silent : S → Step S                    -- no call
  emit   : List Event → S → Step S       -- these calls, then the next state
  stop   : List Event → End ⊤ → Step S   -- these calls, then the run ends
  stuck  : Step S                        -- no next state

-- The finite trace: the calls, then the end.
listTr : List Event → End ⊤ → Tr ⊤
step (next (listTr []       e)) = inj₁ (inj₁ e)
step (next (listTr (v ∷ vs) e)) = inj₁ (inj₂ (v , listTr vs e))

-- The `Delay` that never arrives.
never : ∀ {A : Set} → Delay A
step never = inj₂ never

-- The trace that never shows anything: no call, no end.
silentTr : Tr ⊤
next silentTr = never

private
  S′ : Set
  S′ = End ⊤ ⊎ (Event × Tr ⊤)

  endRefl : ∀ (e : End ⊤) → EndRel _≡_ e e
  endRefl (returned x) = returned≈ refl
  endRefl halted       = halted≈
  endRefl exhausted    = exhausted≈

module Machine {S : Set} (δ : S → Step S) where

  -- The trace from a state, with some calls still to show first.
  tr  : List Event → S → Tr ⊤
  go  : Step S → Delay S′
  step (next (tr (v ∷ vs) s)) = inj₁ (inj₂ (v , tr vs s))
  next (tr []       s) = go (δ s)
  step (go (silent s′))       = inj₂ (go (δ s′))
  step (go (emit [] s′))      = inj₂ (go (δ s′))
  step (go (emit (v ∷ vs) s′)) = inj₁ (inj₂ (v , tr vs s′))
  step (go (stop [] e))       = inj₁ (inj₁ e)
  step (go (stop (v ∷ vs) e)) = inj₁ (inj₂ (v , listTr vs e))
  step (go stuck)             = inj₂ never

  trace : S → Tr ⊤
  trace = tr []

  -- A run that reaches its end: the calls it makes on the way, and the end.
  data Reaches : S → List Event → End ⊤ → Set where
    r-silent : ∀ {s s′ es e}    → δ s ≡ silent s′ → Reaches s′ es e → Reaches s es e
    r-emit   : ∀ {s s′ vs es e} → δ s ≡ emit vs s′ → Reaches s′ es e → Reaches s (vs ++ es) e
    r-stop   : ∀ {s vs e}       → δ s ≡ stop vs e → Reaches s vs e

  -- The traces a reaching run passes through.
  data Good : Tr ⊤ → List Event → End ⊤ → Set where
    g-run : ∀ {pend s es e out} → Reaches s es e → out ≡ pend ++ es → Good (tr pend s) out e
    g-fin : ∀ {es e} → Good (listTr es e) es e

  -- What a delay shows first, for the calls `es` and then the end `e`.
  Arrive : Delay S′ → List Event → End ⊤ → Set
  Arrive d []       e = d ⇓ inj₁ e
  Arrive d (v ∷ es) e = ∃[ t ] (d ⇓ inj₂ (v , t) × Good t es e)

  private
    laterA : ∀ {d d′ es e} → step d ≡ inj₂ d′ → Arrive d′ es e → Arrive d es e
    laterA {es = []}     q a             = later⇓ q a
    laterA {es = v ∷ es} q (t , a , g)   = t , later⇓ q a , g

  arriveR : ∀ {s es e} → Reaches s es e → Arrive (go (δ s)) es e
  arriveR {s} (r-silent {s′ = s′} {es} {e} q r) =
    subst (λ x → Arrive (go x) es e) (sym q) (laterA {d = go (silent s′)} refl (arriveR r))
  arriveR {s} (r-emit {s′ = s′} {[]} {es} {e} q r) =
    subst (λ x → Arrive (go x) es e) (sym q) (laterA {d = go (emit [] s′)} refl (arriveR r))
  arriveR {s} (r-emit {s′ = s′} {v ∷ vs} {es} {e} q r) =
    subst (λ x → Arrive (go x) (v ∷ vs ++ es) e) (sym q) (tr vs s′ , now⇓ refl , g-run r refl)
  arriveR {s} (r-stop {vs = []} {e} q) =
    subst (λ x → Arrive (go x) [] e) (sym q) (now⇓ refl)
  arriveR {s} (r-stop {vs = v ∷ vs} {e} q) =
    subst (λ x → Arrive (go x) (v ∷ vs) e) (sym q) (listTr vs e , now⇓ refl , g-fin)

  arriveG : ∀ {t es e} → Good t es e → Arrive (next t) es e
  arriveG (g-run {[]}     r refl) = arriveR r
  arriveG (g-run {v ∷ vs} {s} r refl) = tr vs s , now⇓ refl , g-run r refl
  arriveG (g-fin {[]})     = now⇓ refl
  arriveG (g-fin {v ∷ vs} {e}) = listTr vs e , now⇓ refl , g-fin

  private
    endAt : ∀ {e : End ⊤} {o : S′} → inj₁ e ≡ o → StepRel _≡_ (λ u u′ → u ≈ᵗ⟨ _≡_ ⟩ u′) o (inj₁ e)
    endAt {e} refl = endRefl e
    endAt′ : ∀ {e : End ⊤} {o : S′} → inj₁ e ≡ o → StepRel _≡_ (λ u u′ → u ≈ᵗ⟨ _≡_ ⟩ u′) (inj₁ e) o
    endAt′ {e} refl = endRefl e
    evAt : ∀ {v t t′} {o : S′} → inj₂ (v , t) ≡ o → t ≈ᵗ⟨ _≡_ ⟩ t′
         → StepRel _≡_ (λ u u′ → u ≈ᵗ⟨ _≡_ ⟩ u′) o (inj₂ (v , t′))
    evAt refl w = refl , w
    evAt′ : ∀ {v t t′} {o : S′} → inj₂ (v , t′) ≡ o → t ≈ᵗ⟨ _≡_ ⟩ t′
          → StepRel _≡_ (λ u u′ → u ≈ᵗ⟨ _≡_ ⟩ u′) (inj₂ (v , t)) o
    evAt′ refl w = refl , w

  -- THE CONVERSION: a trace a reaching run passes through is its finite trace.
  good-≈ : ∀ {t es e} → Good t es e → t ≈ᵗ⟨ _≡_ ⟩ listTr es e
  fwdG : ∀ {t es e} → Good t es e → ∀ o → next t ⇓ o
       → ∃[ o′ ] (next (listTr es e) ⇓ o′ × StepRel _≡_ (λ u u′ → u ≈ᵗ⟨ _≡_ ⟩ u′) o o′)
  bwdG : ∀ {t es e} → Good t es e → ∀ o′ → next (listTr es e) ⇓ o′
       → ∃[ o ] (next t ⇓ o × StepRel _≡_ (λ u u′ → u ≈ᵗ⟨ _≡_ ⟩ u′) o o′)
  same (good-≈ g) = (λ o a → fwdG g o a) , (λ o′ a′ → bwdG g o′ a′)
  fwdG {es = []}     {e} g o a = inj₁ e , now⇓ refl , endAt (⇓-det (arriveG g) a)
  fwdG {es = v ∷ es} {e} g o a =
    inj₂ (v , listTr es e) , now⇓ refl
    , evAt (⇓-det (proj₁ (proj₂ (arriveG g))) a) (good-≈ (proj₂ (proj₂ (arriveG g))))
  bwdG {es = []}     {e} g o′ a′ = inj₁ e , arriveG g , endAt′ (⇓-det (now⇓ refl) a′)
  bwdG {es = v ∷ es} {e} g o′ a′ =
    inj₂ (v , proj₁ (arriveG g)) , proj₁ (proj₂ (arriveG g))
    , evAt′ (⇓-det (now⇓ refl) a′) (good-≈ (proj₂ (proj₂ (arriveG g))))

  reaches-≈ : ∀ {s es e} → Reaches s es e → trace s ≈ᵗ⟨ _≡_ ⟩ listTr es e
  reaches-≈ r = good-≈ (g-run {pend = []} r refl)
