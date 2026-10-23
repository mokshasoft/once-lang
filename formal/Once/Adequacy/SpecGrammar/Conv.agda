-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Conv — the compiler's grades and types read
-- as the Spec's.
--
-- `toTy` and `toPolyG` send a type the annotation and alias parsers
-- produce to the Spec's; a `rigid` parameter is never parsed, and goes
-- anywhere.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Conv where

import Once.Spec.Grade as LG
import Once.Spec.Grade as SG
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Type as LT
import Once.Internal.Type.Poly as LP
import Once.Spec.Type as ST
import Once.Spec.Surface.Syntax as SS

-- Plan 0.122: the compiler's grades ARE the Spec's; the readings are the
-- identity (kept as names the bridges are written with).
qS : LG.Quantity → SG.Quantity
qS q = q

πS : LG.Purity → SG.Purity
πS π = π

-- A ν's grade is finite on both sides (D318 item 13).
φS : LG.Finite → SG.Finite
φS φ = φ

kS : LG.ArrowKind → SG.ArrowKind
kS k = k

-- Schemas.
toPoly  : LP.PolyType → SS.PolyType
toPolyF : LP.PolyFunctor → SS.PolyFunctor
toPoly LP.PUnit           = SS.PUnit
toPoly LP.PVoid           = SS.PVoid
toPoly (A LP.P* B)        = toPoly A SS.P* toPoly B
toPoly (A LP.P+ B)        = toPoly A SS.P+ toPoly B
toPoly (A LP.P⇒[ q ] B)   = toPoly A SS.P⇒[ qS q ] toPoly B
toPoly (LP.PEff A B)      = SS.PEff (toPoly A) (toPoly B)
toPoly (LP.PAct A B)      = SS.PAct (toPoly A) (toPoly B)
toPoly (LP.Pμ-type F)     = SS.Pμ (toPolyF F)
toPoly (LP.Pν-type F φ)   = SS.Pν (toPolyF F) (φS φ)
toPoly LP.PInt            = SS.PInt
toPoly LP.PFloat          = SS.PFloat
toPoly (LP.PTVar x)       = SS.PTVar x
toPolyF (LP.PK A)         = SS.PK (toPoly A)
toPolyF LP.PId            = SS.PId
toPolyF (F LP.P⊕ G)       = toPolyF F SS.P⊕ toPolyF G
toPolyF (F LP.P⊗ G)       = toPolyF F SS.P⊗ toPolyF G

-- Ground types, as the Spec's types: the same (plan 0.122).
toTy  : LT.Type → ST.Type
toTy A = A

toFun : LT.Fun 0 → ST.Fun 0
toFun F = F

-- Ground types, as the schemas a type alias is written with.
toPolyG  : LT.Type → SS.PolyType
toPolyGF : LT.Fun 0 → SS.PolyFunctor
arrowG   : LG.Purity → LG.Quantity → SS.PolyType → SS.PolyType → SS.PolyType
arrowG LG.pure q A B = A SS.P⇒[ qS q ] B
arrowG LG.act  q A B = SS.PAct A B
arrowG LG.eff  q A B = SS.PEff A B
toPolyG LT.Unit                        = SS.PUnit
toPolyG LT.Void                        = SS.PVoid
toPolyG (A LT.* B)                     = toPolyG A SS.P* toPolyG B
toPolyG (A LT.+ B)                     = toPolyG A SS.P+ toPolyG B
toPolyG (A LT.⇒[ LG.mk-kind q π ] B)   = arrowG π q (toPolyG A) (toPolyG B)
toPolyG (LT.μ F)                  = SS.Pμ (toPolyGF F)
toPolyG (LT.ν F φ)                = SS.Pν (toPolyGF F) (φS φ)
toPolyG LT.Int                         = SS.PInt
toPolyG LT.Float                       = SS.PFloat
toPolyG (ST.var ())
toPolyGF (LT.K A)                      = SS.PK (toPolyG A)
toPolyGF LT.Id                         = SS.PId
toPolyGF (F LT.⊕ G)                    = toPolyGF F SS.P⊕ toPolyGF G
toPolyGF (F LT.⊗ G)                    = toPolyGF F SS.P⊗ toPolyGF G
