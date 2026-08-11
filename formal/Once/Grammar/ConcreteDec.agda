-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Grammar.ConcreteDec — decision procedures for the `Concrete`
-- (GType) and `ConcreteExpr` (GExpr) round-trip-domain predicates.
--
-- These produce the witnesses that `gexprToRaw` / `gtypeToType`
-- consume. They are what lets a *raw* `GExpr` / `GType` (e.g. coming
-- out of `GModule`) be converted: try to build the witness, and the
-- conversion succeeds iff the value is in the concrete domain (no
-- `TVar`, no reserved-word vars, single-binding lets only).
--
-- Used to discharge `gmoduleToModule` (Once.Adequacy.Compile).
------------------------------------------------------------------------

module Once.Grammar.ConcreteDec where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Grammar as G
  using ( GExpr; GType
        ; EUnit; EInt; EString; EVar; EQualified; ELam; EApp; EPair
        ; EAnnot; EBinOp; EUnaryOp; ECompose; ELet; EDestruct
        ; TUnit; TVoid; TInt; TFloat; TBuffer; TString; TEff; TVar; GMu
        ; _⊗_; _⊕_; _⇒[_]_ )
open import Once.Grammar.Printer using
  ( Concrete; c-unit; c-void; c-int; c-float; c-buffer; c-string
  ; c-prod; c-sum; c-fun; c-eff )
open import Once.Grammar.ExprPrinter using
  ( ConcreteExpr; c-e-unit; c-e-int; c-e-string; c-e-var; c-e-qual
  ; c-e-lam; c-e-app; c-e-pair; c-e-annot; c-e-binop; c-e-unary
  ; c-e-comp; c-e-let1; c-e-destr )
open import Once.Parser.Expr using (isReserved)

------------------------------------------------------------------------
-- Type concreteness (no `TVar`).
------------------------------------------------------------------------

concreteType? : (t : GType) → Maybe (Concrete t)
concreteType? TUnit   = just c-unit
concreteType? TVoid   = just c-void
concreteType? TInt    = just c-int
concreteType? TFloat  = just c-float
concreteType? TBuffer = just c-buffer
concreteType? TString = just c-string
concreteType? (a ⊗ b) with concreteType? a | concreteType? b
... | just ca | just cb = just (c-prod ca cb)
... | _       | _       = nothing
concreteType? (a ⊕ b) with concreteType? a | concreteType? b
... | just ca | just cb = just (c-sum ca cb)
... | _       | _       = nothing
concreteType? (a ⇒[ q ] b) with concreteType? a | concreteType? b
... | just ca | just cb = just (c-fun ca cb)
... | _       | _       = nothing
concreteType? (TEff a b) with concreteType? a | concreteType? b
... | just ca | just cb = just (c-eff ca cb)
... | _       | _       = nothing
concreteType? (TVar _) = nothing
-- `GMu` is outside the round-trip `Concrete` domain (no c-mu constructor):
-- recursion-scheme types are handled by the parser/elaborator directly,
-- not via the printed-GType round-trip.
concreteType? (GMu _) = nothing

------------------------------------------------------------------------
-- Expression concreteness (no `TVar` in annotations, no reserved-word
-- variables, single-binding lets only).
------------------------------------------------------------------------

concrete? : (g : GExpr) → Maybe (ConcreteExpr g)
concrete? EUnit       = just c-e-unit
concrete? (EInt _)    = just c-e-int
concrete? (EString _) = just c-e-string
concrete? (EVar name) with isReserved name in eq
... | false = just (c-e-var eq)
... | true  = nothing
concrete? (EQualified name alias) with isReserved name in eq
... | false = just (c-e-qual eq)
... | true  = nothing
concrete? (ELam x body) with concrete? body
... | just cb = just (c-e-lam cb)
... | nothing = nothing
concrete? (EApp f x) with concrete? f | concrete? x
... | just cf | just cx = just (c-e-app cf cx)
... | _       | _       = nothing
concrete? (EPair a b) with concrete? a | concrete? b
... | just ca | just cb = just (c-e-pair ca cb)
... | _       | _       = nothing
concrete? (EAnnot e t) with concrete? e | concreteType? t
... | just ce | just ct = just (c-e-annot ce ct)
... | _       | _       = nothing
concrete? (EBinOp op a b) with concrete? a | concrete? b
... | just ca | just cb = just (c-e-binop ca cb)
... | _       | _       = nothing
concrete? (EUnaryOp op e) with concrete? e
... | just ce = just (c-e-unary ce)
... | nothing = nothing
concrete? (ECompose f g) with concrete? f | concrete? g
... | just cf | just cg = just (c-e-comp cf cg)
... | _       | _       = nothing
concrete? (ELet [] body)                = nothing
concrete? (ELet ((x , v) ∷ []) body) with concrete? v | concrete? body
... | just cv | just cb = just (c-e-let1 cv cb)
... | _       | _       = nothing
concrete? (ELet (_ ∷ _ ∷ _) body)       = nothing
concrete? (EDestruct scrut x l y r) with concrete? scrut | concrete? l | concrete? r
... | just cs | just cl | just cr = just (c-e-destr cs cl cr)
... | _       | _       | _       = nothing
