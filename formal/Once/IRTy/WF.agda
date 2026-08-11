-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IRTy.WF
--
-- Transport the ungraded well-formedness witnesses (`IsBaseTypeI` /
-- `WellFormedFI`, over `IRTy`/`IRFunctor`) to the surface ones
-- (`IsBaseType` / `WellFormedF`, over `Type`/`Functor`) along the
-- canonical section `⌈_⌉`. Plan 0.52 M2: the IR recursion schemes carry
-- `WellFormedFI` proofs, but the surface `sem-cata`/`sem-Out`/… helpers
-- want `WellFormedF ⌈F⌉F`. Refl/cong by induction.
------------------------------------------------------------------------

module Once.IRTy.WF where

open import Once.IRTy
import Once.Functor.Translate as Tr

-- Base-type witness transports along `⌈_⌉`.
base-⌈⌉ : ∀ {A} → IsBaseTypeI A → Tr.IsBaseType ⌈ A ⌉
base-⌈⌉ base-Unit       = Tr.base-Unit
base-⌈⌉ base-Void       = Tr.base-Void
base-⌈⌉ base-Int        = Tr.base-Int
base-⌈⌉ base-Float      = Tr.base-Float
base-⌈⌉ base-Str        = Tr.base-Str
base-⌈⌉ base-Buffer     = Tr.base-Buffer
base-⌈⌉ (base-Prod a b) = Tr.base-Prod (base-⌈⌉ a) (base-⌈⌉ b)
base-⌈⌉ (base-Sum a b)  = Tr.base-Sum  (base-⌈⌉ a) (base-⌈⌉ b)

-- Well-formed-functor witness transports along `⌈_⌉F`.
wf-⌈⌉ : ∀ {F} → WellFormedFI F → Tr.WellFormedF ⌈ F ⌉F
wf-⌈⌉ (wf-K b)      = Tr.wf-K (base-⌈⌉ b)
wf-⌈⌉ wf-Id         = Tr.wf-Id
wf-⌈⌉ (wf-Sum f g)  = Tr.wf-Sum  (wf-⌈⌉ f) (wf-⌈⌉ g)
wf-⌈⌉ (wf-Prod f g) = Tr.wf-Prod (wf-⌈⌉ f) (wf-⌈⌉ g)

-- The REVERSE transports (surface → ungraded, along `⌊_⌋`), for the
-- elaborator, which carries surface `WellFormedF` but builds IR whose
-- recursion schemes demand `WellFormedFI (eraseF F)`.
base-⌊⌋ : ∀ {A} → Tr.IsBaseType A → IsBaseTypeI ⌊ A ⌋
base-⌊⌋ Tr.base-Unit       = base-Unit
base-⌊⌋ Tr.base-Void       = base-Void
base-⌊⌋ Tr.base-Int        = base-Int
base-⌊⌋ Tr.base-Float      = base-Float
base-⌊⌋ Tr.base-Str        = base-Str
base-⌊⌋ Tr.base-Buffer     = base-Buffer
base-⌊⌋ (Tr.base-Prod a b) = base-Prod (base-⌊⌋ a) (base-⌊⌋ b)
base-⌊⌋ (Tr.base-Sum a b)  = base-Sum  (base-⌊⌋ a) (base-⌊⌋ b)

wf-⌊⌋ : ∀ {F} → Tr.WellFormedF F → WellFormedFI (eraseF F)
wf-⌊⌋ (Tr.wf-K b)      = wf-K (base-⌊⌋ b)
wf-⌊⌋ Tr.wf-Id         = wf-Id
wf-⌊⌋ (Tr.wf-Sum f g)  = wf-Sum  (wf-⌊⌋ f) (wf-⌊⌋ g)
wf-⌊⌋ (Tr.wf-Prod f g) = wf-Prod (wf-⌊⌋ f) (wf-⌊⌋ g)
