-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Numbers — every row of the table has its theory's laws
-- (`Spec.Metatheory.Numbers`, plan 0.150, D409), at every target: `Int`'s on
-- the words of its width (`Numbers.Int`), `Float`'s on the values of its
-- format (`Numbers.Rounded`, `Numbers.FloatOrder`).
------------------------------------------------------------------------

module Once.Metatheory.Numbers where

open import Data.Unit using (tt)

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Theory
  using ( Has; int-neg; int-ring; int-division; int-order; int-equality
        ; float-neg; float-rounded; float-order; float-equality; module Models; module Laws)
open import Once.Spec.Metatheory using (Numbers)
import Once.Metatheory.Numbers.Int as I
import Once.Metatheory.Numbers.Rounded as R
import Once.Metatheory.Numbers.FloatOrder as O

numbers : ∀ (fmt : TargetNum) → Numbers fmt
numbers fmt = record { lawful = lawful }
  where
    open TargetNum fmt using (int-bits; float-format)
    open Models fmt using (Valid; structure)

    lawful : ∀ {A U} (h : Has A U) → Laws.Laws (Valid A) U (structure h)
    lawful int-neg        = I.negLaws int-bits
    lawful int-ring       = I.ringLaws int-bits
    lawful int-division   = tt
    lawful int-order      = I.orderLaws int-bits
    lawful int-equality   = I.equalityLaws int-bits
    lawful float-neg      = R.negLaws float-format
    lawful float-rounded  = R.roundedLaws float-format
    lawful float-order    = O.orderLaws float-format
    lawful float-equality = O.equalityLaws float-format
