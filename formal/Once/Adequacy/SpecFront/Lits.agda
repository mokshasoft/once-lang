-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Lits — a program's integer literals, read by the
-- compiler and by the Spec (plan 0.121 §3.6, F7: `Admissible`).
--
-- The compiler checks its target's range on the RESOLVED module's literals
-- (`AdmissibleM`), the Spec on the written module's (`Admissible`).
-- Resolution renames references only, an import adds signatures only, and a
-- written expression's Spec image has the same literals (a minus on a
-- numeral is one literal on both sides): the two lists are equal
-- (`lits-eq`), so the checks agree (`admissible-of`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Lits where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Integer using (ℤ)
import Data.Product
import Data.List.Relation.Unary.All
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Surface.Syntax using (BinOp; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Internal.Syntax
import Once.Spec.Surface.Syntax as S
import Once.Spec.Source as SP
open import Once.Denotation.Admissible using (rawIntLits; negLits; declIntLits; moduleIntLits; AdmissibleM)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; mkModule)
open import Once.Parser.Module.Resolve using (signaturesWithOwner)
import Once.Internal.Resolution as LR
open import Once.Adequacy.SpecGrammar.Expr
  using (Emb; e-var; e-qual; e-res; e-app; e-lam; e-let; e-pair; e-destruct; e-unit; e-int; e-float; e-annot; e-binop; e-neg)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import)
open import Once.Target.Arch using (Arch; arch-numerics)

------------------------------------------------------------------------
-- Resolution keeps the literals
------------------------------------------------------------------------

private
  var-lits : ∀ {bound um x e} → LR.ResolvesVar bound um x e → rawIntLits e ≡ [] × negLits e ≡ []
  var-lits (LR.rv-binder _)          = refl , refl
  var-lits (LR.rv-gen _ _)           = refl , refl
  var-lits (LR.rv-import _ _ _ _)    = refl , refl
  var-lits (LR.rv-own _ _ _)         = refl , refl

mutual
  res-lits : ∀ {um am bound e e′} → LR.ResolvesExpr um am bound e e′ → rawIntLits e′ ≡ rawIntLits e
  res-lits (LR.re-var rv) = Data.Product.proj₁ (var-lits rv)
  res-lits LR.re-this = refl
  res-lits (LR.re-qual _ _ _) = refl
  res-lits (LR.re-qual-path _ _) = refl
  res-lits LR.re-res = refl
  res-lits (LR.re-app f a) = cong₂ _++_ (res-lits f) (res-lits a)
  res-lits (LR.re-lam b) = res-lits b
  res-lits (LR.re-let e b) = cong₂ _++_ (res-lits e) (res-lits b)
  res-lits (LR.re-pair a b) = cong₂ _++_ (res-lits a) (res-lits b)
  res-lits (LR.re-destruct s l r) = cong₂ _++_ (res-lits s) (cong₂ _++_ (res-lits l) (res-lits r))
  res-lits (LR.re-annot e) = res-lits e
  res-lits (LR.re-binop a b) = cong₂ _++_ (res-lits a) (res-lits b)
  res-lits (LR.re-unop e) = res-neg e
  res-lits LR.re-unit = refl
  res-lits LR.re-int = refl
  res-lits LR.re-float = refl

  res-neg : ∀ {um am bound e e′} → LR.ResolvesExpr um am bound e e′ → negLits e′ ≡ negLits e
  res-neg (LR.re-var rv) = Data.Product.proj₂ (var-lits rv)
  res-neg LR.re-this = refl
  res-neg (LR.re-qual _ _ _) = refl
  res-neg (LR.re-qual-path _ _) = refl
  res-neg LR.re-res = refl
  res-neg (LR.re-app f a) = cong₂ _++_ (res-lits f) (res-lits a)
  res-neg (LR.re-lam b) = res-lits b
  res-neg (LR.re-let e b) = cong₂ _++_ (res-lits e) (res-lits b)
  res-neg (LR.re-pair a b) = cong₂ _++_ (res-lits a) (res-lits b)
  res-neg (LR.re-destruct s l r) = cong₂ _++_ (res-lits s) (cong₂ _++_ (res-lits l) (res-lits r))
  res-neg (LR.re-annot e) = res-lits e
  res-neg (LR.re-binop a b) = cong₂ _++_ (res-lits a) (res-lits b)
  res-neg (LR.re-unop e) = res-neg e
  res-neg LR.re-unit = refl
  res-neg LR.re-int = refl
  res-neg LR.re-float = refl

private
  go : List Decl → List ℤ
  go []       = []
  go (d ∷ ds) = declIntLits d ++ go ds

  go-owned : ∀ o ds rest → go (signaturesWithOwner o ds ++ rest) ≡ go rest
  go-owned o [] rest = refl
  go-owned o (DSignature _ _ _ ∷ ds) rest = go-owned o ds rest
  go-owned o (DTypeSig _ _ ∷ ds) rest = go-owned o ds rest
  go-owned o (DFunDef _ _ ∷ ds) rest = go-owned o ds rest
  go-owned o (DTypeAlias _ _ _ ∷ ds) rest = go-owned o ds rest
  go-owned o (DImport _ ∷ ds) rest = go-owned o ds rest

-- (`moduleIntLits`' walk, on the resolved declarations)
decls-res : ∀ {mm um am dsU dsR} → LR.ResolvesDecls mm um am dsU dsR → go dsR ≡ go dsU
decls-res LR.rds-nil = refl
decls-res (LR.rds-cons LR.nim-fundef (LR.rd-fundef rb _) rds) = cong₂ _++_ (res-lits rb) (decls-res rds)
decls-res (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) = decls-res rds
decls-res (LR.rds-cons LR.nim-sig LR.rd-signature rds) = decls-res rds
decls-res (LR.rds-cons LR.nim-alias LR.rd-typealias rds) = decls-res rds
decls-res (LR.rds-import {impDs = impDs} {ds' = dsR′} _ rds) = trans (go-owned _ impDs dsR′) (decls-res rds)

------------------------------------------------------------------------
-- The Spec image keeps the literals
------------------------------------------------------------------------

mutual
  emb-lits : ∀ {e e′} → Emb e e′ → SP.intLits e′ ≡ rawIntLits e
  emb-lits e-var = refl
  emb-lits e-qual = refl
  emb-lits e-res = refl
  emb-lits (e-app f a) = cong₂ _++_ (emb-lits f) (emb-lits a)
  emb-lits (e-lam b) = emb-lits b
  emb-lits (e-let e b) = cong₂ _++_ (emb-lits e) (emb-lits b)
  emb-lits (e-pair a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-lits (e-destruct s l r) = cong₂ _++_ (emb-lits s) (cong₂ _++_ (emb-lits l) (emb-lits r))
  emb-lits e-unit = refl
  emb-lits e-int = refl
  emb-lits e-float = refl
  emb-lits (e-annot _ e) = emb-lits e
  emb-lits (e-binop a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-lits (e-neg e) = emb-neg e

  emb-neg : ∀ {e e′} → Emb e e′ → SP.negLits e′ ≡ negLits e
  emb-neg e-var = refl
  emb-neg e-qual = refl
  emb-neg e-res = refl
  emb-neg (e-app f a) = cong₂ _++_ (emb-lits f) (emb-lits a)
  emb-neg (e-lam b) = emb-lits b
  emb-neg (e-let e b) = cong₂ _++_ (emb-lits e) (emb-lits b)
  emb-neg (e-pair a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-neg (e-destruct s l r) = cong₂ _++_ (emb-lits s) (cong₂ _++_ (emb-lits l) (emb-lits r))
  emb-neg e-unit = refl
  emb-neg e-int = refl
  emb-neg e-float = refl
  emb-neg (e-annot _ e) = emb-lits e
  emb-neg (e-binop a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-neg (e-neg e) = emb-neg e

decls-emb : ∀ {ds ds′} → Pointwise DEmb ds ds′ → SP.declLits ds′ ≡ go ds
decls-emb [] = refl
decls-emb (d-typesig ∷ pw) = decls-emb pw
decls-emb (d-fundef em ∷ pw) = cong₂ _++_ (emb-lits em) (decls-emb pw)
decls-emb (d-signature ∷ pw) = decls-emb pw
decls-emb (d-alias ∷ pw) = decls-emb pw
decls-emb (d-import ∷ pw) = decls-emb pw

------------------------------------------------------------------------
-- The checks agree
------------------------------------------------------------------------

lits-eq : ∀ {mm um am dsU dsR ds′} → LR.ResolvesDecls mm um am dsU dsR → Pointwise DEmb dsU ds′
        → moduleIntLits (mkModule dsR) ≡ SP.declLits ds′
lits-eq {dsR = dsR} rds pw = trans (mil dsR) (trans (decls-res rds) (sym (decls-emb pw)))
  where
    mil : ∀ ds → moduleIntLits (mkModule ds) ≡ go ds
    mil [] = refl
    mil (d ∷ ds) = cong (declIntLits d ++_) (mil ds)

admissible-of : ∀ {mm um am dsU dsR ds′} (arch : Arch) → LR.ResolvesDecls mm um am dsU dsR → Pointwise DEmb dsU ds′
              → AdmissibleM arch (mkModule dsR) → Data.List.Relation.Unary.All.All _ (SP.declLits ds′)
admissible-of arch rds pw a = subst (Data.List.Relation.Unary.All.All _) (lits-eq rds pw) a

-- …and conversely (plan 0.121 `complete`).
admissible← : ∀ {mm um am dsU dsR ds′} (arch : Arch) → LR.ResolvesDecls mm um am dsU dsR → Pointwise DEmb dsU ds′
            → Data.List.Relation.Unary.All.All _ (SP.declLits ds′) → AdmissibleM arch (mkModule dsR)
admissible← arch rds pw a = subst (Data.List.Relation.Unary.All.All _) (sym (lits-eq rds pw)) a
