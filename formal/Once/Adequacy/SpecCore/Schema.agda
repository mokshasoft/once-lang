-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Schema — the compiler's definitions signature as
-- the Spec's (plan 0.121, the core bridge).
--
-- A schema `∀ Δ. A` is the same on both sides: its variables are de Bruijn
-- indices in both grammars. The compiler's schema grammar also has the
-- constants `rigid k i` (an enclosing definition's parameter), which no
-- definition's schema contains (`Clean`); `ptyS` sends them anywhere. On a
-- clean schema, instantiating commutes with the translation (`TyR-inst`), and
-- an instance that respects the kinds does on both sides (`respects-S`).
------------------------------------------------------------------------

module Once.Adequacy.SpecCore.Schema where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Internal.Core.PolyTy as LP
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SS
open import Once.Adequacy.SpecGrammar.Conv using (kS; φS)
open import Once.Adequacy.SpecCore.Type
  using (TyR; FunR; r-unit; r-void; r-int; r-float; r-*; r-+; r-⇒; r-μ; r-ν; r-rigid; r-K; r-Id; r-⊕; r-⊗;
         kindS; base-S)

------------------------------------------------------------------------
-- Schemas
------------------------------------------------------------------------

mutual
  ptyS : ∀ {a} → LP.Ty a → ST.Ty a
  ptyS (LP.var i)       = ST.var i
  ptyS LP.Unit          = ST.Unit
  ptyS LP.Void          = ST.Void
  ptyS LP.Int           = ST.Int
  ptyS LP.Float         = ST.Float
  ptyS (A LP.* B)       = ptyS A ST.* ptyS B
  ptyS (A LP.+ B)       = ptyS A ST.+ ptyS B
  ptyS (A LP.⇒[ k ] B)  = ptyS A ST.⇒[ kS k ] ptyS B
  ptyS (LP.μ-type F)    = ST.μ (pfunS F)
  ptyS (LP.ν-type F φ)  = ST.ν (pfunS F) (φS φ)
  ptyS (LP.rigid _ _)   = ST.Unit

  pfunS : ∀ {a} → LP.Fun a → ST.Fun a
  pfunS (LP.K A)    = ST.K (ptyS A)
  pfunS LP.Id       = ST.Id
  pfunS (F LP.⊕ G)  = pfunS F ST.⊕ pfunS G
  pfunS (F LP.⊗ G)  = pfunS F ST.⊗ pfunS G

-- No enclosing parameter in it.
mutual
  data Clean {a} : LP.Ty a → Set where
    c-var   : ∀ {i} → Clean (LP.var i)
    c-Unit  : Clean LP.Unit
    c-Void  : Clean LP.Void
    c-Int   : Clean LP.Int
    c-Float : Clean LP.Float
    c-*     : ∀ {A B} → Clean A → Clean B → Clean (A LP.* B)
    c-+     : ∀ {A B} → Clean A → Clean B → Clean (A LP.+ B)
    c-⇒     : ∀ {A B k} → Clean A → Clean B → Clean (A LP.⇒[ k ] B)
    c-μ     : ∀ {F} → CleanF F → Clean (LP.μ-type F)
    c-ν     : ∀ {F φ} → CleanF F → Clean (LP.ν-type F φ)

  data CleanF {a} : LP.Fun a → Set where
    c-K  : ∀ {A} → Clean A → CleanF (LP.K A)
    c-Id : CleanF LP.Id
    c-⊕  : ∀ {F G} → CleanF F → CleanF G → CleanF (F LP.⊕ G)
    c-⊗  : ∀ {F G} → CleanF F → CleanF G → CleanF (F LP.⊗ G)

kindsS : ∀ {a} → LP.KCtx a → ST.KCtx a
kindsS κ i = kindS (κ i)

schS : LP.Schema → SS.Schema
schS sc = SS.schema (LP.Schema.arity sc) (kindsS (LP.Schema.kinds sc)) (ptyS (LP.Schema.type sc))

defsS : ∀ {Fs s} → LP.Sig Fs s → SS.Defs s
defsS LP.[]       = SS.[]
defsS (S LP.▷ sc) = defsS S SS.▷ schS sc

-- (looking a definition up commutes with the translation)
!!-defsS : ∀ {Fs s} (S : LP.Sig Fs s) (d : Fin s) → defsS S SS.!! d ≡ schS (S LP.!! d)
!!-defsS (S LP.▷ sc) zero    = refl
!!-defsS (S LP.▷ sc) (suc d) = !!-defsS S d

-- An instance of the `d`-th schema, read at the Spec's schema (the same arity).
castSub : ∀ {Fs s′ m} (S₀ : LP.Sig Fs s′) (d : Fin s′)
        → ST.TySub (LP.Schema.arity (S₀ LP.!! d)) m → ST.TySub (SS.Schema.arity (defsS S₀ SS.!! d)) m
castSub (S₀ LP.▷ sc) zero    τ′ = τ′
castSub (S₀ LP.▷ sc) (suc d) τ′ = castSub S₀ d τ′

-- Every definition's schema is clean.
CleanSig : ∀ {Fs s} → LP.Sig Fs s → Set
CleanSig S = ∀ d → Clean (LP.Schema.type (S LP.!! d))

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

module _ {m} {Δ : ST.KCtx m} where

  -- `τ′` is `τ` in the Spec's grammar
  InstR : ∀ {a} → LP.GSub a → ST.TySub a m → Set
  InstR τ τ′ = ∀ i → TyR Δ (τ i) (τ′ i)

  mutual
    TyR-inst : ∀ {a} {A : LP.Ty a} {τ τ′} → Clean A → InstR τ τ′ → TyR Δ (A LP.⟪ τ ⟫) (ptyS A ST.⟨ τ′ ⟩)
    TyR-inst {A = LP.var i} c-var r = r i
    TyR-inst c-Unit  r = r-unit
    TyR-inst c-Void  r = r-void
    TyR-inst c-Int   r = r-int
    TyR-inst c-Float r = r-float
    TyR-inst (c-* a b) r = r-* (TyR-inst a r) (TyR-inst b r)
    TyR-inst (c-+ a b) r = r-+ (TyR-inst a r) (TyR-inst b r)
    TyR-inst (c-⇒ a b) r = r-⇒ refl (TyR-inst a r) (TyR-inst b r)
    TyR-inst (c-μ f)   r = r-μ (FunR-inst f r)
    TyR-inst (c-ν f)   r = r-ν refl (FunR-inst f r)

    FunR-inst : ∀ {a} {F : LP.Fun a} {τ τ′} → CleanF F → InstR τ τ′ → FunR Δ (F LP.⟪ τ ⟫F) (pfunS F ST.⟨ τ′ ⟩F)
    FunR-inst (c-K a)   r = r-K (TyR-inst a r)
    FunR-inst c-Id      r = r-Id
    FunR-inst (c-⊕ f g) r = r-⊕ (FunR-inst f r) (FunR-inst g r)
    FunR-inst (c-⊗ f g) r = r-⊗ (FunR-inst f r) (FunR-inst g r)

  -- An instance respecting the kinds does on both sides.
  respects-S : ∀ {a} {κ : LP.KCtx a} {τ τ′} → LP.Respects κ τ → InstR τ τ′ → ST.Respects (kindsS κ) Δ τ′
  respects-S {κ = κ} rs r i e = base-S (rs i (kind-base (κ i) e)) (r i)
    where
      kind-base : ∀ k → kindS k ≡ ST.base → k ≡ LT.k-base
      kind-base LT.k-base _ = refl
      kind-base LT.k-any  ()
