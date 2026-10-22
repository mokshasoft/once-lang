-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.TargetView — the target shapes of the builtin check rules.
--
-- Each builtin check rule (`cata`, `ana`, `In`, `curry`, `pair`, `case`,
-- `compose`, `inl`/`inr`) accepts ONE shape of expected type and rejects every
-- other. The rule dispatches on a two-constructor view of the target instead of
-- matching the shape against a catch-all. The elaborator means the same thing
-- and reduces the same way at a concrete target, but a proof about a rule can
-- now case the VIEW (two cases) instead of letting the coverage checker split
-- the target type and refute every rejected shape against the proof's goal.
-- That refutation was most of the check time of the proofs over these rules
-- (`agree-check-RApp`: 36 s → the few cases it states).
------------------------------------------------------------------------

module Once.TypeCheck.TargetView where

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type.Poly
open import Once.Type
open import Once.Spec.Grade using (_⊑π_; ⊑-pa; ⊑-act)

-- `cata alg` : μ F ⇒ A
data CataTarget : Type → Set where
  cata-at    : ∀ F π A → CataTarget (μ-type F ⇒[ mk-kind Many π ] A)
  cata-other : ∀ {T} → CataTarget T

cataTarget : (T : Type) → CataTarget T
cataTarget (μ-type F ⇒[ mk-kind Many π ] A) = cata-at F π A
{-# CATCHALL #-}
cataTarget _ = cata-other

-- `ana coalg` : A ⇒ ν F at a terminating grade (a stream), or `ana round` :
-- A ⇒[eff] B (THE LOOP, D317/D319) — the Spec's `c-ana` bounds the stream's
-- arrow by `act`, so the two never overlap. The `eff` clause comes FIRST: it
-- reads the grade alone, so it reduces at any codomain.
data AnaTarget : Type → Set where
  loop-at   : ∀ A B → AnaTarget (A ⇒[ mk-kind Many eff ] B)
  ana-at    : ∀ A π₀ F π → π₀ ⊑π act → AnaTarget (A ⇒[ mk-kind Many π₀ ] ν-type F π)
  ana-other : ∀ {T} → AnaTarget T

anaTarget : (T : Type) → AnaTarget T
anaTarget (A ⇒[ mk-kind Many eff ] B)           = loop-at A B
anaTarget (A ⇒[ mk-kind Many pure ] ν-type F π) = ana-at A pure F π ⊑-pa
anaTarget (A ⇒[ mk-kind Many act ] ν-type F π)  = ana-at A act F π ⊑-act
{-# CATCHALL #-}
anaTarget _ = ana-other

-- `In arg` : μ F
data InTarget : Type → Set where
  in-at    : ∀ F → InTarget (μ-type F)
  in-other : ∀ {T} → InTarget T

inTarget : (T : Type) → InTarget T
inTarget (μ-type F) = in-at F
{-# CATCHALL #-}
inTarget _ = in-other

-- `curry f` : A ⇒ (B ⇒ C)
data CurryTarget : Type → Set where
  curry-at    : ∀ A π₀ B π C → CurryTarget (A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C))
  curry-other : ∀ {T} → CurryTarget T

curryTarget : (T : Type) → CurryTarget T
curryTarget (A ⇒[ mk-kind Many π₀ ] (B ⇒[ mk-kind Many π ] C)) = curry-at A π₀ B π C
{-# CATCHALL #-}
curryTarget _ = curry-other

-- `pair f g` : A ⇒ (B * C)
data PairTarget : Type → Set where
  pair-at    : ∀ A π B C → PairTarget (A ⇒[ mk-kind Many π ] (B * C))
  pair-other : ∀ {T} → PairTarget T

pairTarget : (T : Type) → PairTarget T
pairTarget (A ⇒[ mk-kind Many π ] (B * C)) = pair-at A π B C
{-# CATCHALL #-}
pairTarget _ = pair-other

-- `case f g` : (A + B) ⇒ C
data CaseTarget : Type → Set where
  case-at    : ∀ A B π C → CaseTarget ((A + B) ⇒[ mk-kind Many π ] C)
  case-other : ∀ {T} → CaseTarget T

caseTarget : (T : Type) → CaseTarget T
caseTarget ((A + B) ⇒[ mk-kind Many π ] C) = case-at A B π C
{-# CATCHALL #-}
caseTarget _ = case-other

-- `compose f g` : A ⇒ C
data ArrowTarget : Type → Set where
  arrow-at    : ∀ A π C → ArrowTarget (A ⇒[ mk-kind Many π ] C)
  arrow-other : ∀ {T} → ArrowTarget T

arrowTarget : (T : Type) → ArrowTarget T
arrowTarget (A ⇒[ mk-kind Many π ] C) = arrow-at A π C
{-# CATCHALL #-}
arrowTarget _ = arrow-other

-- `inl a` / `inr b` : A + B
data SumTarget : Type → Set where
  sum-at    : ∀ A B → SumTarget (A + B)
  sum-other : ∀ {T} → SumTarget T

------------------------------------------------------------------------
-- Argument views of the infer-mode builtins whose argument's type decides
-- the rule: `Out` (a stream) and `apply` (a closure paired with its argument).
-- D251: no view has a `Void` case; ex falso is `initial`.
------------------------------------------------------------------------

data NuView : Type → Set where
  nu-at    : ∀ F π → NuView (ν-type F π)
  nu-other : ∀ {T} → NuView T

nuView : (T : Type) → NuView T
nuView (ν-type F π) = nu-at F π
{-# CATCHALL #-}
nuView _            = nu-other

data ApplyView : Type → Set where
  apply-at    : ∀ A π B A' → ApplyView ((A ⇒[ mk-kind Many π ] B) * A')
  apply-other : ∀ {T} → ApplyView T

applyView : (T : Type) → ApplyView T
applyView ((A ⇒[ mk-kind Many π ] B) * A') = apply-at A π B A'
{-# CATCHALL #-}
applyView _ = apply-other

-- `fst` / `snd` : a pair.
data ProdView : Type → Set where
  prod-at    : ∀ A B → ProdView (A * B)
  prod-other : ∀ {T} → ProdView T

prodView : (T : Type) → ProdView T
prodView (A * B) = prod-at A B
{-# CATCHALL #-}
prodView _       = prod-other
