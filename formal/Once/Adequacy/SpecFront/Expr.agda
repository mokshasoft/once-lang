-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Expr — a resolved expression of the compiler's as
-- the Spec's (plan 0.121 §3.6, F2).
--
-- The two resolvers write every name alike (R11, D330): a bare name is a
-- variable a binder encloses (`RX`, over the names bound around it), and a
-- resolved one is never the entry `main` (D324: no definition refers to it).
-- The other formers are the same on both sides (plan 0.122: one syntax).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Expr where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)

open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Surface.Syntax using (RVar; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg)
open import Once.Spec.Surface.Syntax using (Expr)
import Once.Spec.Surface.Syntax as S
open import Once.Adequacy.SpecGrammar.Conv using (toTy)

data RX (bound : List String) : Expr → S.Expr → Set where
  x-local    : ∀ {x} → x ∈ bound → RX bound (RVar x) (S.RVar x)
  x-res      : ∀ {c} → c ≢ canonical ("main" ∷ []) → RX bound (RResolved c) (S.RResolved c)
  x-app      : ∀ {f a f′ a′} → RX bound f f′ → RX bound a a′ → RX bound (RApp f a) (S.RApp f′ a′)
  x-lam      : ∀ {x b b′} → RX (x ∷ bound) b b′ → RX bound (RLam x b) (S.RLam x b′)
  x-let      : ∀ {x e b e′ b′} → RX bound e e′ → RX (x ∷ bound) b b′ → RX bound (RLet x e b) (S.RLet x e′ b′)
  x-pair     : ∀ {a b a′ b′} → RX bound a a′ → RX bound b b′ → RX bound (RPair a b) (S.RPair a′ b′)
  x-destruct : ∀ {e xl l xr r e′ l′ r′} → RX bound e e′ → RX (xl ∷ bound) l l′ → RX (xr ∷ bound) r r′
             → RX bound (RDestruct e xl l xr r) (S.RDestruct e′ xl l′ xr r′)
  x-unit     : RX bound RUnit S.RUnit
  x-int      : ∀ {n} → RX bound (RInt n) (S.RInt n)
  x-float    : ∀ {i f l} → RX bound (RFloat i f l) (S.RFloat i f l)
  x-annot    : ∀ {e e′ T} → RX bound e e′ → RX bound (RAnnot e T) (S.RAnnot e′ (toTy T))
  x-binop    : ∀ {op a b a′ b′} → RX bound a a′ → RX bound b b′ → RX bound (RBinOp op a b) (S.RBinOp op a′ b′)
  x-neg      : ∀ {e e′} → RX bound e e′ → RX bound (RNeg e) (S.RNeg e′)

-- The relation is the identity: the compiler's expressions are the Spec's
-- (plan 0.122 2b-2).
rx-≡ : ∀ {bound e e′} → RX bound e e′ → e ≡ e′
rx-≡ (x-local _)          = refl
rx-≡ (x-res _)            = refl
rx-≡ (x-app f a)          = cong₂ RApp (rx-≡ f) (rx-≡ a)
rx-≡ (x-lam b)            = cong (RLam _) (rx-≡ b)
rx-≡ (x-let e b)          = cong₂ (RLet _) (rx-≡ e) (rx-≡ b)
rx-≡ (x-pair a b)         = cong₂ RPair (rx-≡ a) (rx-≡ b)
rx-≡ (x-destruct e l r)   = cong₃ (rx-≡ e) (rx-≡ l) (rx-≡ r)
  where
    cong₃ : ∀ {e e′ l l′ r r′ xl xr} → e ≡ e′ → l ≡ l′ → r ≡ r′ → RDestruct e xl l xr r ≡ RDestruct e′ xl l′ xr r′
    cong₃ refl refl refl = refl
rx-≡ x-unit               = refl
rx-≡ x-int                = refl
rx-≡ x-float              = refl
rx-≡ (x-annot e)          = cong (λ e″ → RAnnot e″ _) (rx-≡ e)
rx-≡ (x-binop a b)        = cong₂ (RBinOp _) (rx-≡ a) (rx-≡ b)
rx-≡ (x-neg e)            = cong RNeg (rx-≡ e)
