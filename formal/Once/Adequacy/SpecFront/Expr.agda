-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Expr — a resolved expression of the compiler's as
-- the Spec's (plan 0.121 §3.6, F2).
--
-- The two resolvers agree on what each name denotes but write one case
-- differently: the compiler keeps a reference to the module's own
-- polymorphic definition as the bare name (`rv-own-poly`), where the Spec
-- writes every own definition as its canonical name (`rn-own`). So a bare
-- name is the Spec's variable when a binder encloses it and the own
-- polymorphic definition otherwise (`RX`, over the module's polymorphic
-- definitions `ps` and the names bound around it); a resolved own name is
-- never a polymorphic one, nor the entry `main` (D324: no definition refers
-- to it), and an annotation is a surface type (no rigid constant). The
-- other formers are the grammar bridge's (`SpecGrammar.Expr.Emb`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Expr where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)
open import Relation.Nullary using (¬_)

open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Lang.Syntax
  using (RawExpr; RVar; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RUnaryOp; OpNeg)
import Once.Spec.Surface.Syntax as S
open import Once.Lang.Type.WellFormed using (RigidFree)
open import Once.Adequacy.SpecGrammar.Conv using (toTy)
open import Once.Adequacy.SpecGrammar.Expr using (opS)

-- A resolved name that is not an own polymorphic definition's.
NotOwnPoly : List String → CanonicalName → Set
NotOwnPoly ps c = ∀ {x} → c ≡ canonical (x ∷ []) → ¬ (x ∈ ps)

data RX (ps bound : List String) : RawExpr → S.Expr → Set where
  x-local    : ∀ {x} → x ∈ bound → RX ps bound (RVar x) (S.RVar x)
  x-own      : ∀ {x} → ¬ (x ∈ bound) → x ∈ ps → RX ps bound (RVar x) (S.RResolved (canonical (x ∷ [])))
  x-res      : ∀ {c} → NotOwnPoly ps c → c ≢ canonical ("main" ∷ []) → RX ps bound (RResolved c) (S.RResolved c)
  x-app      : ∀ {f a f′ a′} → RX ps bound f f′ → RX ps bound a a′ → RX ps bound (RApp f a) (S.RApp f′ a′)
  x-lam      : ∀ {x b b′} → RX ps (x ∷ bound) b b′ → RX ps bound (RLam x b) (S.RLam x b′)
  x-let      : ∀ {x e b e′ b′} → RX ps bound e e′ → RX ps (x ∷ bound) b b′ → RX ps bound (RLet x e b) (S.RLet x e′ b′)
  x-pair     : ∀ {a b a′ b′} → RX ps bound a a′ → RX ps bound b b′ → RX ps bound (RPair a b) (S.RPair a′ b′)
  x-destruct : ∀ {e xl l xr r e′ l′ r′} → RX ps bound e e′ → RX ps (xl ∷ bound) l l′ → RX ps (xr ∷ bound) r r′
             → RX ps bound (RDestruct e xl l xr r) (S.RDestruct e′ xl l′ xr r′)
  x-unit     : RX ps bound RUnit S.RUnit
  x-int      : ∀ {n} → RX ps bound (RInt n) (S.RInt n)
  x-float    : ∀ {i f l p} → RX ps bound (RFloat i f l p) (S.RFloat i f l)
  x-annot    : ∀ {e e′ T} → RigidFree T → RX ps bound e e′ → RX ps bound (RAnnot e T) (S.RAnnot e′ (toTy T))
  x-binop    : ∀ {op a b a′ b′} → RX ps bound a a′ → RX ps bound b b′ → RX ps bound (RBinOp op a b) (S.RBinOp (opS op) a′ b′)
  x-neg      : ∀ {e e′} → RX ps bound e e′ → RX ps bound (RUnaryOp OpNeg e) (S.RNeg e′)
