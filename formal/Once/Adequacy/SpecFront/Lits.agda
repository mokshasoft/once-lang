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
open import Data.Integer using (ℤ)
import Data.Product
import Data.List.Relation.Unary.All
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Surface.Syntax using (BinOp; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.TypeCheck.Raw using (isComparisonOp; isArithmeticOp; isFloatArithmeticOp)
import Once.Spec.Surface.Syntax as S
import Once.Spec.Source as SP
open import Once.Denotation.Admissible using (rawIntLits; negLits; declIntLits; moduleIntLits; AdmissibleM)
open import Once.Spec.Surface.Syntax using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; mkModule)
import Once.Parser.Relation.Resolution as LR
import Once.Spec.Surface.Program
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

-- (`moduleIntLits`' walk, on the resolved declarations)
decls-res : ∀ {mm um am dsU dsR} → LR.ResolvesDecls mm um am dsU dsR → go dsR ≡ go dsU
decls-res LR.rds-nil = refl
decls-res (LR.rds-cons Once.Spec.Surface.Program.ni-def (LR.rd-fundef rb _) rds) = cong₂ _++_ (res-lits rb) (decls-res rds)
decls-res (LR.rds-cons Once.Spec.Surface.Program.ni-tsig LR.rd-typesig rds) = decls-res rds
decls-res (LR.rds-cons Once.Spec.Surface.Program.ni-sig LR.rd-signature rds) = decls-res rds
decls-res (LR.rds-cons Once.Spec.Surface.Program.ni-alias LR.rd-typealias rds) = decls-res rds
decls-res (LR.rds-import _ rds) = decls-res rds

------------------------------------------------------------------------
-- The Spec image keeps the literals
------------------------------------------------------------------------

mutual
  emb-lits : ∀ e → SP.intLits e ≡ rawIntLits e
  emb-lits (RVar _) = refl
  emb-lits (RQualified _ _) = refl
  emb-lits (RResolved _) = refl
  emb-lits (RApp f a) = cong₂ _++_ (emb-lits f) (emb-lits a)
  emb-lits (RLam _ b) = emb-lits b
  emb-lits (RLet _ e b) = cong₂ _++_ (emb-lits e) (emb-lits b)
  emb-lits (RPair a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-lits (RDestruct s _ l _ r) = cong₂ _++_ (emb-lits s) (cong₂ _++_ (emb-lits l) (emb-lits r))
  emb-lits RUnit = refl
  emb-lits (RInt _) = refl
  emb-lits (RFloat _ _ _) = refl
  emb-lits (RAnnot e _) = emb-lits e
  emb-lits (RBinOp _ a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-lits (RNeg e) = emb-neg e

  emb-neg : ∀ e → SP.negLits e ≡ negLits e
  emb-neg (RVar _) = refl
  emb-neg (RQualified _ _) = refl
  emb-neg (RResolved _) = refl
  emb-neg (RApp f a) = cong₂ _++_ (emb-lits f) (emb-lits a)
  emb-neg (RLam _ b) = emb-lits b
  emb-neg (RLet _ e b) = cong₂ _++_ (emb-lits e) (emb-lits b)
  emb-neg (RPair a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-neg (RDestruct s _ l _ r) = cong₂ _++_ (emb-lits s) (cong₂ _++_ (emb-lits l) (emb-lits r))
  emb-neg RUnit = refl
  emb-neg (RInt _) = refl
  emb-neg (RFloat _ _ _) = refl
  emb-neg (RAnnot e _) = emb-lits e
  emb-neg (RBinOp _ a b) = cong₂ _++_ (emb-lits a) (emb-lits b)
  emb-neg (RNeg e) = emb-neg e

decls-emb : ∀ ds → SP.declLits ds ≡ go ds
decls-emb [] = refl
decls-emb (DTypeSig _ _ ∷ ds) = decls-emb ds
decls-emb (DFunDef _ e ∷ ds) = cong₂ _++_ (emb-lits e) (decls-emb ds)
decls-emb (DSignature _ _ ∷ ds) = decls-emb ds
decls-emb (DTypeAlias _ _ _ ∷ ds) = decls-emb ds
decls-emb (DImport _ ∷ ds) = decls-emb ds

------------------------------------------------------------------------
-- The checks agree
------------------------------------------------------------------------

lits-eq : ∀ {mm um am dsU dsR} → LR.ResolvesDecls mm um am dsU dsR
        → moduleIntLits (mkModule dsR) ≡ SP.declLits dsU
lits-eq {dsU = dsU} {dsR = dsR} rds = trans (mil dsR) (trans (decls-res rds) (sym (decls-emb dsU)))
  where
    mil : ∀ ds → moduleIntLits (mkModule ds) ≡ go ds
    mil [] = refl
    mil (d ∷ ds) = cong (declIntLits d ++_) (mil ds)

admissible-of : ∀ {mm um am dsU dsR} (arch : Arch) → LR.ResolvesDecls mm um am dsU dsR
              → AdmissibleM arch (mkModule dsR) → Data.List.Relation.Unary.All.All _ (SP.declLits dsU)
admissible-of arch rds a = subst (Data.List.Relation.Unary.All.All _) (lits-eq rds) a

-- …and conversely (plan 0.121 `complete`).
admissible← : ∀ {mm um am dsU dsR} (arch : Arch) → LR.ResolvesDecls mm um am dsU dsR
            → Data.List.Relation.Unary.All.All _ (SP.declLits dsU) → AdmissibleM arch (mkModule dsR)
admissible← arch rds a = subst (Data.List.Relation.Unary.All.All _) (sym (lits-eq rds)) a
