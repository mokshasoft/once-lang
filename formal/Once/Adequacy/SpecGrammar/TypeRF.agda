-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.TypeRF — a type the compiler's type grammar
-- parses is a surface type: no rigid parameter (plan 0.121 `complete`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.TypeRF where

open import Once.Lang.Type.WellFormed using (RigidFree; RigidFreeF; rf-Unit; rf-Void; rf-Int; rf-Float; rf-*; rf-+; rf-⇒; rf-μ; rf-ν;
  rf-K; rf-Id; rf-⊕; rf-⊗)
open import Once.Parser.TypeRelation

atom-rf   : ∀ {ts T r} → ParsesAtom ts T r → RigidFree T
prodT-rf  : ∀ {l ts T r} → ParsesProdTail l ts T r → RigidFree l → RigidFree T
prod-rf   : ∀ {ts T r} → ParsesProd ts T r → RigidFree T
sumT-rf   : ∀ {l ts T r} → ParsesSumTail l ts T r → RigidFree l → RigidFree T
sum-rf    : ∀ {ts T r} → ParsesSum ts T r → RigidFree T
type-rf   : ∀ {ts T r} → ParsesType ts T r → RigidFree T
arrowT-rf : ∀ {l ts T r} → ParsesArrowTail l ts T r → RigidFree l → RigidFree T
fatom-rf  : ∀ {ts F r} → ParsesFunctorAtom ts F r → RigidFreeF F
fprod-rf  : ∀ {ts F r} → ParsesFunctorProd ts F r → RigidFreeF F
fprodT-rf : ∀ {l ts F r} → ParsesFunctorProdTail l ts F r → RigidFreeF l → RigidFreeF F
fsum-rf   : ∀ {ts F r} → ParsesFunctorSum ts F r → RigidFreeF F
fsumT-rf  : ∀ {l ts F r} → ParsesFunctorSumTail l ts F r → RigidFreeF l → RigidFreeF F

atom-rf (pa-unit _)     = rf-Unit
atom-rf (pa-void _)     = rf-Void
atom-rf (pa-int _)      = rf-Int
atom-rf (pa-float _)    = rf-Float
atom-rf (pa-eff p q)    = rf-⇒ (atom-rf p) (atom-rf q)
atom-rf (pa-act p q)    = rf-⇒ (atom-rf p) (atom-rf q)
atom-rf (pa-paren p _)  = type-rf p
atom-rf (pa-mu p)       = rf-μ (fsum-rf p)
atom-rf (pa-nu p)       = rf-ν (fsum-rf p)
atom-rf (pa-nu-act p)   = rf-ν (fsum-rf p)

prodT-rf (ppt-done _)   l = l
prodT-rf (ppt-star p q) l = prodT-rf q (rf-* l (atom-rf p))
prod-rf (pp-mk p q) = prodT-rf q (atom-rf p)

sumT-rf (pst-done _)   l = l
sumT-rf (pst-plus p q) l = sumT-rf q (rf-+ l (prod-rf p))
sum-rf (ps-mk p q) = sumT-rf q (prod-rf p)

type-rf (pt-mk p q) = arrowT-rf q (sum-rf p)
arrowT-rf (pat-done _)    l = l
arrowT-rf (pat-arrow-g p) l = rf-⇒ l (type-rf p)
arrowT-rf (pat-arrow p)   l = rf-⇒ l (type-rf p)

fatom-rf (pfa-id _)      = rf-Id
fatom-rf (pfa-k p)       = rf-K (atom-rf p)
fatom-rf (pfa-paren p _) = fsum-rf p
fprod-rf (pfp-mk p q) = fprodT-rf q (fatom-rf p)
fprodT-rf (pfpt-done _)   l = l
fprodT-rf (pfpt-star p q) l = fprodT-rf q (rf-⊗ l (fatom-rf p))
fsum-rf (pfs-mk p q) = fsumT-rf q (fprod-rf p)
fsumT-rf (pfst-done _)   l = l
fsumT-rf (pfst-plus p q) l = fsumT-rf q (rf-⊕ l (fprod-rf p))
