-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IRTy.WF
--
-- Transport the ungraded well-formedness witnesses (`IsBaseTypeI` /
-- `WellFormedFI`, over `IRTy`/`IRFunctor`) to the surface ones
-- (`Base ∅ₖ` / `WFFun ∅ₖ`, over `Type`/`Functor`) along the
-- canonical section `⌈_⌉`. Plan 0.52 M2: the IR recursion schemes carry
-- `WellFormedFI` proofs, but the surface `sem-cata`/`sem-Out`/… helpers
-- want `WFFun ∅ₖ ⌈F⌉F`. Refl/cong by induction.
------------------------------------------------------------------------

module Once.IRTy.WF where

open import Once.IRTy
import Once.Internal.Type.WellFormed as Tr
import Once.Spec.Type as Tr

-- Base-type witness transports along `⌈_⌉`.
base-⌈⌉ : ∀ {A} → IsBaseTypeI A → (Tr.Base Tr.∅ₖ) ⌈ A ⌉
base-⌈⌉ base-Unit       = Tr.b-Unit
base-⌈⌉ base-Void       = Tr.b-Void
base-⌈⌉ base-Int        = Tr.b-Int
base-⌈⌉ base-Float      = Tr.b-Float
base-⌈⌉ (base-Prod a b) = Tr.b-* (base-⌈⌉ a) (base-⌈⌉ b)
base-⌈⌉ (base-Sum a b)  = Tr.b-+  (base-⌈⌉ a) (base-⌈⌉ b)

-- Well-formed-functor witness transports along `⌈_⌉F`.
wf-⌈⌉ : ∀ {F} → WellFormedFI F → (Tr.WFFun Tr.∅ₖ) ⌈ F ⌉F
wf-⌈⌉ (wf-K b)      = Tr.wf-K (base-⌈⌉ b)
wf-⌈⌉ wf-Id         = Tr.wf-Id
wf-⌈⌉ (wf-Sum f g)  = Tr.wf-⊕  (wf-⌈⌉ f) (wf-⌈⌉ g)
wf-⌈⌉ (wf-Prod f g) = Tr.wf-⊗ (wf-⌈⌉ f) (wf-⌈⌉ g)

-- The REVERSE transports (surface → ungraded, along `⌊_⌋`), for the
-- elaborator, which carries surface `WFFun ∅ₖ` but builds IR whose
-- recursion schemes demand `WellFormedFI (eraseF F)`.
-- At any kinding context: a base type variable erases to `Void`.
base-⌊⌋ : ∀ {m} {Δ : Tr.KCtx m} {A} → Tr.Base Δ A → IsBaseTypeI ⌊ A ⌋
base-⌊⌋ (Tr.b-var _)       = base-Void
base-⌊⌋ Tr.b-Unit       = base-Unit
base-⌊⌋ Tr.b-Void       = base-Void
base-⌊⌋ Tr.b-Int        = base-Int
base-⌊⌋ Tr.b-Float      = base-Float
base-⌊⌋ (Tr.b-* a b) = base-Prod (base-⌊⌋ a) (base-⌊⌋ b)
base-⌊⌋ (Tr.b-+ a b)  = base-Sum  (base-⌊⌋ a) (base-⌊⌋ b)

wf-⌊⌋ : ∀ {m} {Δ : Tr.KCtx m} {F} → Tr.WFFun Δ F → WellFormedFI (eraseF F)
wf-⌊⌋ (Tr.wf-K b)      = wf-K (base-⌊⌋ b)
wf-⌊⌋ Tr.wf-Id         = wf-Id
wf-⌊⌋ (Tr.wf-⊕ f g)  = wf-Sum  (wf-⌊⌋ f) (wf-⌊⌋ g)
wf-⌊⌋ (Tr.wf-⊗ f g) = wf-Prod (wf-⌊⌋ f) (wf-⌊⌋ g)
