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

import Once.Lang.Type.Grade as LG
import Once.Spec.Grade as SG
import Once.Lang.Type as LT
import Once.Lang.Type.Poly as LP
import Once.Spec.Type as ST
import Once.Spec.Surface.Syntax as SS

qS : LG.Quantity → SG.Quantity
qS LG.Zero = SG.Zero
qS LG.One  = SG.One
qS LG.Many = SG.Many

πS : LG.Purity → SG.Purity
πS LG.pure = SG.pure
πS LG.act  = SG.act
πS LG.eff⁺ = SG.eff⁺
πS LG.eff  = SG.eff

kS : LG.ArrowKind → SG.ArrowKind
kS (LG.mk-kind q π) = SG.mk-kind (qS q) (πS π)

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
toPoly (LP.Pν-type F π)   = SS.Pν (toPolyF F) (πS π)
toPoly LP.PInt            = SS.PInt
toPoly LP.PFloat          = SS.PFloat
toPoly (LP.PTVar x)       = SS.PTVar x
toPolyF (LP.PK A)         = SS.PK (toPoly A)
toPolyF LP.PId            = SS.PId
toPolyF (F LP.P⊕ G)       = toPolyF F SS.P⊕ toPolyF G
toPolyF (F LP.P⊗ G)       = toPolyF F SS.P⊗ toPolyF G

-- Ground types, as the Spec's types.
toTy  : LT.Type → ST.Type
toFun : LT.Functor → ST.Fun 0
toTy LT.Unit             = ST.Unit
toTy LT.Void             = ST.Void
toTy (A LT.* B)          = toTy A ST.* toTy B
toTy (A LT.+ B)          = toTy A ST.+ toTy B
toTy (A LT.⇒[ k ] B)     = toTy A ST.⇒[ kS k ] toTy B
toTy (LT.μ-type F)       = ST.μ (toFun F)
toTy (LT.ν-type F π)     = ST.ν (toFun F) (πS π)
toTy LT.Int              = ST.Int
toTy LT.Float            = ST.Float
toTy (LT.rigid _ _)      = ST.Unit
toFun (LT.K A)           = ST.K (toTy A)
toFun LT.Id              = ST.Id
toFun (F LT.⊕ G)         = toFun F ST.⊕ toFun G
toFun (F LT.⊗ G)         = toFun F ST.⊗ toFun G

-- Ground types, as the schemas a type alias is written with.
toPolyG  : LT.Type → SS.PolyType
toPolyGF : LT.Functor → SS.PolyFunctor
arrowG   : LG.Purity → LG.Quantity → SS.PolyType → SS.PolyType → SS.PolyType
arrowG LG.pure q A B = A SS.P⇒[ qS q ] B
arrowG LG.act  q A B = SS.PAct A B
arrowG LG.eff⁺ q A B = SS.PEff A B
arrowG LG.eff  q A B = SS.PEff A B
toPolyG LT.Unit                        = SS.PUnit
toPolyG LT.Void                        = SS.PVoid
toPolyG (A LT.* B)                     = toPolyG A SS.P* toPolyG B
toPolyG (A LT.+ B)                     = toPolyG A SS.P+ toPolyG B
toPolyG (A LT.⇒[ LG.mk-kind q π ] B)   = arrowG π q (toPolyG A) (toPolyG B)
toPolyG (LT.μ-type F)                  = SS.Pμ (toPolyGF F)
toPolyG (LT.ν-type F π)                = SS.Pν (toPolyGF F) (πS π)
toPolyG LT.Int                         = SS.PInt
toPolyG LT.Float                       = SS.PFloat
toPolyG (LT.rigid _ _)                 = SS.PUnit
toPolyGF (LT.K A)                      = SS.PK (toPolyG A)
toPolyGF LT.Id                         = SS.PId
toPolyGF (F LT.⊕ G)                    = toPolyGF F SS.P⊕ toPolyGF G
toPolyGF (F LT.⊗ G)                    = toPolyGF F SS.P⊗ toPolyGF G
