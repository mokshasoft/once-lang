{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Type — the types a programmer writes.
--
-- A type in a signature may mention named type variables (`PTVar`); its
-- functors are written with `PK`, `PId`, `_P⊕_` and `_P⊗_`. The expression
-- syntax (`Spec.Surface.Syntax`) and the meaning of a written type
-- (`Spec.Surface.Program`) both build on this module; what only needs types
-- imports this alone.
------------------------------------------------------------------------

module Once.Spec.Surface.Type where

open import Data.String using (String)
open import Once.Spec.Grade using (Quantity; Finite)

mutual
  data PolyFunctor : Set where
    PK   : PolyType → PolyFunctor
    PId  : PolyFunctor
    _P⊕_ : PolyFunctor → PolyFunctor → PolyFunctor
    _P⊗_ : PolyFunctor → PolyFunctor → PolyFunctor

  data PolyType : Set where
    PUnit PVoid PInt PFloat : PolyType
    _P*_ _P+_ : PolyType → PolyType → PolyType
    _P⇒[_]_   : PolyType → Quantity → PolyType → PolyType   -- a pure arrow
    PAct PEff : PolyType → PolyType → PolyType               -- `Act A B`, `Eff A B`
    Pμ        : PolyFunctor → PolyType                       -- `Mu F`
    Pν        : PolyFunctor → Finite → PolyType              -- `Nu F`, `Nu (Act F)`
    PTVar     : String → PolyType                            -- a type variable

infixr 40 _P⊕_
infixr 50 _P⊗_
infixr 30 _P⇒[_]_
infixr 40 _P+_
infixr 50 _P*_
