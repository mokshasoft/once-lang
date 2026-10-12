-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Effects — the meaning's effect structure
-- (`Spec.Metatheory.Effects`, plan 0.112 E and C4).
--
-- `M π` is one monad per grade (the identity monad at `pure`, the interaction
-- tree `T` at `eff`), not a graded monad: a derivation has one grade and moves
-- up by subeffecting. So the structure is a family of monads and the monad
-- morphisms between them — `subM` (subeffecting) and `toT` (what compilation
-- erases a grade to) — and the observation `run`, which respects `T`'s return
-- and bind.
------------------------------------------------------------------------

module Once.Metatheory.Effects where

open import Data.List using (List; [])
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Type.Grade using (Purity; pure; eff)
open import Once.Spec.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe)
open import Once.Spec.Metatheory using (Effects)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; Interp; run; then)
open import Once.Denotation.TraceMonadLaws using (>>=T-identityʳ; >>=T-assoc; run-bind)
open import Once.Denotation.GradedDomain using (M; returnM; bindM; subM; toT; _>>=ᵖ_)
open import Once.Metatheory.Coherence.Relation using (toT-bindᵍ)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β; >>=ᵖ-assoc; >>=ᵖ-idʳ; bindM-idˡ)

M-identityʳ : ∀ π {X : Set} (m : M π X) → bindM π m (returnM π) ≡ m
M-identityʳ pure m = >>=ᵖ-idʳ m
M-identityʳ eff  m = >>=T-identityʳ m

M-assoc : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
        → bindM π (bindM π m f) g ≡ bindM π m (λ x → bindM π (f x) g)
M-assoc pure m f g = >>=ᵖ-assoc m f g
M-assoc eff  m f g = >>=T-assoc m f g

subM-return : ∀ {π π′} (g : π ⊑π π′) {X : Set} (x : X) → subM g (returnM π x) ≡ returnM π′ x
subM-return ⊑-pure x = refl
subM-return ⊑-eff  x = refl
subM-return ⊑-pe   x = refl

subM-bind : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
          → subM g (bindM π m k) ≡ bindM π′ (subM g m) (λ x → subM g (k x))
subM-bind ⊑-pure m k = refl
subM-bind ⊑-eff  m k = refl
subM-bind ⊑-pe   m k = cong returnT (>>=ᵖ-β m k)

toT-return : ∀ π {X : Set} (x : X) → toT π (returnM π x) ≡ returnT x
toT-return pure x = refl
toT-return eff  x = refl

toT-bind : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
         → toT π (bindM π m k) ≡ (toT π m >>=T λ x → toT π (k x))
toT-bind pure m k = cong returnT (>>=ᵖ-β m k)
toT-bind eff  m k = cong (m >>=T_) refl

run-return : ∀ (ι : Interp) (h : List SigOpEvent) {X Y : Set} (x : X) (f : X → T Y)
           → then ι h (run ι h (returnT x)) f ≡ run ι h (f x)
run-return ι h x f = cong (λ hh → run ι hh (f x)) (++-identityʳ h)

effects : Effects
effects = record
  { M-identityˡ = bindM-idˡ
  ; M-identityʳ = M-identityʳ
  ; M-assoc     = M-assoc
  ; subM-return = subM-return
  ; subM-bind   = subM-bind
  ; toT-return  = toT-return
  ; toT-bind    = toT-bind
  ; toT-bindᵍ   = toT-bindᵍ
  ; run-return  = run-return
  ; run-bind    = λ ι h m f → run-bind ι h m f
  }
