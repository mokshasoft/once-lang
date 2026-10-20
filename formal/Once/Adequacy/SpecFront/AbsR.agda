-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.AbsR — a type is related to its abstraction
-- (plan 0.121 §3.6, F6).
--
-- A compiler type whose rigid constants its kinds all bind (its abstraction
-- has no constant left) is related, at the Spec's kinds, to the Spec type its
-- abstraction translates to (`cf-R`): a schema's rigid instance to the
-- schema's type, a ground type to itself.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.AbsR where

open import Data.Nat using (_<_; _<?_)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Once.Lang.Type as LT
import Once.Lang.Core.PolyTy as LP
open import Once.Lang.Type.DecEq using (_≟tk_)
open import Once.Lang.Core.AbsTy using (absTy; absF; ar-bound; ar-kind; ConstFree; ConstFreeF; cf-var; cf-Unit; cf-Void; cf-Int; cf-Float; cf-*; cf-+; cf-⇒; cf-μ; cf-ν; cf-K; cf-Id; cf-⊕; cf-⊗)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Schema using (ptyS; pfunS; kindsS)

------------------------------------------------------------------------
-- A type all of whose rigid constants its kinds bind: related to its
-- abstraction
------------------------------------------------------------------------

private
  cf-rig-kind : ∀ {m} (κ : LP.KCtx m) k i (j : Fin m) → toℕ j ≡ i → (d : Dec (κ j ≡ k))
              → ConstFree (ar-kind κ k i j d) → TyR (kindsS κ) (LT.rigid k i) (ptyS (ar-kind κ k i j d))
  cf-rig-kind κ k i j e (yes refl) _ = r-rigid j e refl
  cf-rig-kind κ k i j e (no _) ()

  cf-rig : ∀ {m} (κ : LP.KCtx m) k i → (d : Dec (i < m))
         → ConstFree (ar-bound κ k i d) → TyR (kindsS κ) (LT.rigid k i) (ptyS (ar-bound κ k i d))
  cf-rig κ k i (yes p) c = cf-rig-kind κ k i (fromℕ< p) (toℕ-fromℕ< p) (κ (fromℕ< p) ≟tk k) c
  cf-rig κ k i (no _) ()

mutual
  cf-R : ∀ {m} (κ : LP.KCtx m) (A : LT.Type) → ConstFree (absTy κ A) → TyR (kindsS κ) A (ptyS (absTy κ A))
  cf-R κ LT.Unit          _          = r-unit
  cf-R κ LT.Void          _          = r-void
  cf-R κ LT.Int           _          = r-int
  cf-R κ LT.Float         _          = r-float
  cf-R κ (A LT.* B)       (cf-* a b) = r-* (cf-R κ A a) (cf-R κ B b)
  cf-R κ (A LT.+ B)       (cf-+ a b) = r-+ (cf-R κ A a) (cf-R κ B b)
  cf-R κ (A LT.⇒[ k ] B)  (cf-⇒ a b) = r-⇒ refl (cf-R κ A a) (cf-R κ B b)
  cf-R κ (LT.μ-type F)    (cf-μ f)   = r-μ (cfF-R κ F f)
  cf-R κ (LT.ν-type F φ)  (cf-ν f)   = r-ν refl (cfF-R κ F f)
  cf-R {m} κ (LT.rigid k i) c         = cf-rig κ k i (i <? m) c

  cfF-R : ∀ {m} (κ : LP.KCtx m) (F : LT.Functor) → ConstFreeF (absF κ F) → FunR (kindsS κ) F (pfunS (absF κ F))
  cfF-R κ (LT.K A)   (cf-K a)   = r-K (cf-R κ A a)
  cfF-R κ LT.Id      cf-Id      = r-Id
  cfF-R κ (F LT.⊕ G) (cf-⊕ f g) = r-⊕ (cfF-R κ F f) (cfF-R κ G g)
  cfF-R κ (F LT.⊗ G) (cf-⊗ f g) = r-⊗ (cfF-R κ F f) (cfF-R κ G g)

