-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Written — what a Spec parse writes: no resolved
-- name (plan 0.121 `complete`, resolution back).
--
-- `RResolved` is resolution's output; no rule of the grammar
-- (`Once.Spec.Surface.Grammar`) produces it, so a parsed definition's body
-- has none (`decls-written`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Written where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Grammar as G

-- An expression as written: no resolved name.
Written : Expr → Set
Written (RVar _)              = ⊤
Written (RQualified _ _)      = ⊤
Written (RResolved _)         = ⊥
Written (RApp f a)            = Written f × Written a
Written (RLam _ b)            = Written b
Written (RLet _ e b)          = Written e × Written b
Written (RPair a b)           = Written a × Written b
Written (RDestruct s _ l _ r) = Written s × Written l × Written r
Written RUnit                 = ⊤
Written (RInt _)              = ⊤
Written (RFloat _ _ _)        = ⊤
Written (RAnnot e _)          = Written e
Written (RBinOp _ a b)        = Written a × Written b
Written (RNeg e)              = Written e

expr-w   : ∀ {ts e r} → ParsesExpr ts e r → Written e
compT-w  : ∀ {l ts e r} → ParsesCompTail l ts e r → Written l → Written e
cmp-w    : ∀ {ts e r} → ParsesCmp ts e r → Written e
add-w    : ∀ {ts e r} → ParsesAdd ts e r → Written e
addT-w   : ∀ {l ts e r} → ParsesAddTail l ts e r → Written l → Written e
mul-w    : ∀ {ts e r} → ParsesMul ts e r → Written e
mulT-w   : ∀ {l ts e r} → ParsesMulTail l ts e r → Written l → Written e
unary-w  : ∀ {ts e r} → ParsesUnary ts e r → Written e
app-w    : ∀ {ts e r} → ParsesApp ts e r → Written e
appT-w   : ∀ {l ts e r} → ParsesAppTail l ts e r → Written l → Written e
atom-w   : ∀ {ts e r} → ParsesAtomExpr ts e r → Written e
lam-w    : ∀ {ts e r} → ParsesLamParams ts e r → Written e
parenC-w : ∀ {l ts e r} → ParsesParenCont l ts e r → Written l → Written e

expr-w (expr p q) = compT-w q (cmp-w p)
compT-w (comp-done _)  wl = wl
compT-w (comp-dot p q) wl = compT-w q ((tt , wl) , cmp-w p)

cmp-w (cmp-none p _) = add-w p
cmp-w (cmp _ p q)    = add-w p , add-w q

add-w (add p q) = addT-w q (mul-w p)
addT-w (add-done _)   wl = wl
addT-w (add-op _ p q) wl = addT-w q (wl , mul-w p)

mul-w (mul p q) = mulT-w q (unary-w p)
mulT-w (mul-done _)   wl = wl
mulT-w (mul-op _ p q) wl = mulT-w q (wl , unary-w p)

unary-w (neg p)   = unary-w p
unary-w (unary p) = app-w p

app-w (app p q) = appT-w q (atom-w p)
appT-w (app-done _)    wl = wl
appT-w (app-arg _ p q) wl = appT-w q (wl , atom-w p)

atom-w atom-unit             = tt
atom-w atom-int              = tt
atom-w atom-float            = tt
atom-w (atom-var _ _)        = tt
atom-w (atom-qual _)         = tt
atom-w (atom-paren p q)      = parenC-w q (expr-w p)
atom-w (atom-op _)           = tt
atom-w (atom-lambda p)       = lam-w p
atom-w (atom-let p q)        = expr-w p , expr-w q
atom-w (atom-destruct p q r) = expr-w p , expr-w q , expr-w r

lam-w (lam-body p) = expr-w p
lam-w (lam-arg p)  = lam-w p

parenC-w paren-close     wl = wl
parenC-w (paren-pair p)  wl = wl , expr-w p
parenC-w (paren-annot _) wl = wl

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

-- A declaration as written: a definition's body has no resolved name.
DeclWritten : Decl → Set
DeclWritten (DFunDef _ e) = Written e
DeclWritten (DTypeSig _ _)        = ⊤
DeclWritten (DSignature _ _)      = ⊤
DeclWritten (DTypeAlias _ _ _)    = ⊤
DeclWritten (DImport _)           = ⊤

private
  lams-w : ∀ xs {e} → Written e → Written (G.wrapLams xs e)
  lams-w []       w = w
  lams-w (_ ∷ xs) w = lams-w xs w

  fundef-w : ∀ {x ts d r} → ParsesFunDef x ts d r → DeclWritten d
  fundef-w (fundef {ps = ps} _ q) = lams-w ps (expr-w q)

  alias-w : ∀ {x ps ts d r} → ParsesTypeAlias x ps ts d r → DeclWritten d
  alias-w (alias-eq _)    = tt
  alias-w (alias-param p) = alias-w p

  import-w : ∀ {ts d r} → ParsesImport ts d r → DeclWritten d
  import-w (import-as _)      = tt
  import-w (import-plain _ _) = tt

  decl-w : ∀ {ts d r} → ParsesDecl ts d r → DeclWritten d
  decl-w (decl-import p)            = import-w p
  decl-w (decl-alias p)             = alias-w p
  decl-w (decl-signature _)         = tt
  decl-w (decl-typesig _ _ _)       = tt
  decl-w (decl-fundef _ _ p)        = fundef-w p
  decl-w (decl-op _ (op-sig _))     = tt
  decl-w (decl-op _ (op-def _ p))   = fundef-w p

  decls-w : ∀ {ts ds r} → ParsesDecls ts ds r → All DeclWritten ds
  decls-w (decls-stop _ _)    = []
  decls-w (decls-cons _ d ds) = decl-w d ∷ decls-w ds

-- A module the Spec parses is as written.
decls-written : ∀ {txt m} → Parses txt m → All DeclWritten (Module.decls m)
decls-written (_ , _ , _ , pd , _) = decls-w pd
