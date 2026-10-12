-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Totality — Once is total and productive
-- (`Spec.Metatheory.Totality`, D311, plan 0.117 A).
--
-- `T` is an inductive type, so every tree is finite by induction on it; a
-- stream's layer is a value (pure) or such a tree (effectful).
------------------------------------------------------------------------

module Once.Metatheory.Totality where

open import Once.Spec.Type.Grade using (pure; eff)
open import Once.Spec.Totality using (FiniteT; fin-ret; fin-call; fin-halt)
open import Once.Spec.Metatheory using (Totality)
open import Once.Denotation.TraceMonad using (T; ret; call; halt)
open import Once.Denotation.GradedOps using (out-semᵛ)
open import Once.Metatheory.Witness.NoSelfRef using (no-self-reference; no-forward-reference)
open import Once.Metatheory.Witness.Server using (stream-typed; stream-emits)

finite : ∀ {X : Set} (m : T X) → FiniteT m
finite (ret x)      = fin-ret
finite (call o a k) = fin-call (λ b → finite (k b))
finite (halt o a)   = fin-halt

totality : Totality
totality = record
  { finite     = finite
  ; productive = λ { pure wf v → _ ; eff wf v → finite (out-semᵛ eff wf v) }
  ; no-self-reference    = no-self-reference
  ; no-forward-reference = no-forward-reference
  ; stream-typed = stream-typed
  ; stream-emits = stream-emits
  }
