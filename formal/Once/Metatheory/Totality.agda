-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Totality — Once is total and productive
-- (`Spec.Metatheory.Totality`, D311, plan 0.117 A).
--
-- Every node of a `T∞` tree is an event or the end (D312), so every tree is
-- productive by the shape of its nodes; a stream's layer is a value (pure) or
-- such a tree (effectful).
------------------------------------------------------------------------

module Once.Metatheory.Totality where

open import Once.Spec.Type.Grade using (pure; eff⁺; eff)
open import Once.Spec.Guarded using (forget⁺)
open import Once.Spec.Totality using (ProductiveT∞; ProductiveNode; prod-ret; prod-call; prod-halt)
open Once.Spec.Totality.ProductiveT∞ using (node)
open import Once.Spec.Iterative using (T∞; T∞F; ret∞; call∞; halt∞)
open Once.Spec.Iterative.T∞ using (force)
open import Once.Spec.Metatheory using (Totality)
open import Once.Spec.GradedOps using (out-semᵛ)
open import Once.Denotation.TraceMonadInfLaws using (events∞-pf)
open import Once.Metatheory.Witness.NoSelfRef using (no-self-reference; no-forward-reference)
open import Once.Metatheory.Witness.Server using (stream-typed; stream-emits)
import Once.Metatheory.Witness.Echo as Echo

-- Every tree of `T∞` is productive: by the shape of its nodes.
productive∞ : ∀ {X : Set} (m : T∞ X) → ProductiveT∞ m
productiveN : ∀ {X : Set} (l : T∞F X (T∞ X)) → ProductiveNode ProductiveT∞ l
node (productive∞ m) = productiveN (force m)
productiveN (ret∞ x)      = prod-ret
productiveN (call∞ o a k) = prod-call (λ b → productive∞ (k b))
productiveN (halt∞ o a)   = prod-halt

totality : Totality
totality = record
  { productive = λ { pure wf v → _ ; eff wf v → productive∞ (out-semᵛ eff wf v) ; eff⁺ wf v → productive∞ (forget⁺ (out-semᵛ eff⁺ wf v)) }
  ; productive∞ = productive∞
  ; observable∞ = events∞-pf
  ; no-self-reference    = no-self-reference
  ; no-forward-reference = no-forward-reference
  ; stream-typed = stream-typed
  ; stream-emits = stream-emits
  ; server-typed = Echo.server-typed
  ; server-runs  = Echo.server-runs
  }
