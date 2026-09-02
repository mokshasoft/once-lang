-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Type — the type/functor-type GRAMMAR (OCP-0006, spec).
--
-- SPEC (trust boundary): the alphabet of types a Once program ranges over,
-- including the functor-type constructors (`μ-type`/`ν-type`). Re-exports
-- `Once.Type` verbatim. `Once.Functor.*` (deciders/operations over functors)
-- are IMPLEMENTATION, checked against this grammar, and are NOT re-exported.
------------------------------------------------------------------------

module Once.Spec.Type where

-- EXPLICIT re-export: the TYPE LANGUAGE. What stays out is as much the point
-- as what comes in — every decider (`_≟q_`, `isUnit?`, `isGround`,
-- `fits-in-reg?`), every `show`, the unification oracle's substitution
-- machinery (`Subst`, `instantiate`, `applySubst`), the generic `Maybe`
-- helpers (`maybe-bind`, `if-true-maybe`) and the `NatF`/`ListF`/`TreeF`
-- examples were all inside the trust boundary while this was a blanket
-- re-export. None of them is part of what a Once type IS.
open import Once.Type public
  using ( -- usage algebra (the rules compute with it)
          Quantity ; Zero ; One ; Many ; _+q_ ; _*q_ ; _⊔q_ ; _≤q_
        ; Purity ; pure ; eff ; _⊔p_
        ; ArrowKind ; mk-kind ; quantity ; purity ; pureK ; effK
          -- the type / functor grammar
        ; Type ; Unit ; Void ; Int ; Float ; Str ; Buffer
        ; _*_ ; _+_ ; _⇒[_]_ ; μ-type ; ν-type
        ; _⊸_ ; _⇒_ ; _⇒₀_
        ; Functor ; K ; Id ; _⊕_ ; _⊗_ ; ⟦_⟧T
          -- schemas, and groundness as a PROPERTY (D134)
        ; PolyType ; PUnit ; PVoid ; PInt ; PFloat ; PStr ; PBuffer
        ; _P*_ ; _P+_ ; _P⇒[_]_ ; PEff ; Pμ-type ; Pν-type ; PTVar
        ; PolyFunctor ; PK ; PId ; _P⊕_ ; _P⊗_
        ; Ground ; GroundF ; extractGround ; extractGroundF
          -- target expressibility (D115)
        ; FitsInReg ; fits-int ; fits-float
        )
