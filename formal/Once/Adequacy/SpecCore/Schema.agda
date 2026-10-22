-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Schema — the compiler's definitions signature as
-- the Spec's (plan 0.121, the core bridge).
--
-- Plan 0.122: the compiler's schemas and definitions table ARE the Spec's;
-- the translations are identities (kept as the front-end bridge reads them).
-- Instantiating relates (`TyR-inst`), and an instance that respects the kinds
-- does on both sides (`respects-S`).
------------------------------------------------------------------------

module Once.Adequacy.SpecCore.Schema where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SS
open import Once.Adequacy.SpecCore.Type
  using (TyR; FunR; r-unit; r-void; r-int; r-float; r-*; r-+; r-⇒; r-μ; r-ν; r-var; r-K; r-Id; r-⊕; r-⊗; tyR; funR; base-S)

------------------------------------------------------------------------
-- Schemas: one grammar (plan 0.122)
------------------------------------------------------------------------

ptyS : ∀ {a} → ST.Ty a → ST.Ty a
ptyS A = A

pfunS : ∀ {a} → ST.Fun a → ST.Fun a
pfunS F = F

-- (every type is clean: there are no enclosing parameters any more)
mutual
  data Clean {a} : ST.Ty a → Set where
    c-var   : ∀ {i} → Clean (ST.var i)
    c-Unit  : Clean ST.Unit
    c-Void  : Clean ST.Void
    c-Int   : Clean ST.Int
    c-Float : Clean ST.Float
    c-*     : ∀ {A B} → Clean A → Clean B → Clean (A ST.* B)
    c-+     : ∀ {A B} → Clean A → Clean B → Clean (A ST.+ B)
    c-⇒     : ∀ {A B k} → Clean A → Clean B → Clean (A ST.⇒[ k ] B)
    c-μ     : ∀ {F} → CleanF F → Clean (ST.μ F)
    c-ν     : ∀ {F φ} → CleanF F → Clean (ST.ν F φ)

  data CleanF {a} : ST.Fun a → Set where
    c-K  : ∀ {A} → Clean A → CleanF (ST.K A)
    c-Id : CleanF ST.Id
    c-⊕  : ∀ {F G} → CleanF F → CleanF G → CleanF (F ST.⊕ G)
    c-⊗  : ∀ {F G} → CleanF F → CleanF G → CleanF (F ST.⊗ G)

mutual
  clean : ∀ {a} (A : ST.Ty a) → Clean A
  clean (ST.var i) = c-var
  clean ST.Unit    = c-Unit
  clean ST.Void    = c-Void
  clean ST.Int     = c-Int
  clean ST.Float   = c-Float
  clean (A ST.* B) = c-* (clean A) (clean B)
  clean (A ST.+ B) = c-+ (clean A) (clean B)
  clean (A ST.⇒[ k ] B) = c-⇒ (clean A) (clean B)
  clean (ST.μ F)   = c-μ (cleanF F)
  clean (ST.ν F φ) = c-ν (cleanF F)

  cleanF : ∀ {a} (F : ST.Fun a) → CleanF F
  cleanF (ST.K A)   = c-K (clean A)
  cleanF ST.Id      = c-Id
  cleanF (F ST.⊕ G) = c-⊕ (cleanF F) (cleanF G)
  cleanF (F ST.⊗ G) = c-⊗ (cleanF F) (cleanF G)

kindsS : ∀ {a} → ST.KCtx a → ST.KCtx a
kindsS κ = κ

schS : SS.Schema → SS.Schema
schS sc = sc

defsS : ∀ {s} → SS.Defs s → SS.Defs s
defsS S = S

!!-defsS : ∀ {s} (S : SS.Defs s) (d : Fin s) → defsS S SS.!! d ≡ schS (S SS.!! d)
!!-defsS S d = refl

castSub : ∀ {s′ m} (S₀ : SS.Defs s′) (d : Fin s′)
        → ST.TySub (SS.Schema.arity (S₀ SS.!! d)) m → ST.TySub (SS.Schema.arity (defsS S₀ SS.!! d)) m
castSub S₀ d τ′ = τ′

CleanSig : ∀ {s} → SS.Defs s → Set
CleanSig S = ∀ d → Clean (SS.Schema.type (S SS.!! d))

cleanSig : ∀ {s} (S : SS.Defs s) → CleanSig S
cleanSig S d = clean _

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

module _ {m} {Δ : ST.KCtx m} where

  -- `τ′` is `τ` (the identity's graph, pointwise)
  InstR : ∀ {a} → ST.TySub a m → ST.TySub a m → Set
  InstR τ τ′ = ∀ i → TyR Δ (τ i) (τ′ i)

  mutual
    TyR-inst : ∀ {a} {A : ST.Ty a} {τ τ′} → Clean A → InstR τ τ′ → TyR Δ (A ST.⟨ τ ⟩) (ptyS A ST.⟨ τ′ ⟩)
    TyR-inst {A = ST.var i} c-var r = r i
    TyR-inst c-Unit  r = r-unit
    TyR-inst c-Void  r = r-void
    TyR-inst c-Int   r = r-int
    TyR-inst c-Float r = r-float
    TyR-inst (c-* a b) r = r-* (TyR-inst a r) (TyR-inst b r)
    TyR-inst (c-+ a b) r = r-+ (TyR-inst a r) (TyR-inst b r)
    TyR-inst {A = A ST.⇒[ k ] B} (c-⇒ a b) r = r-⇒ (kS-id k) (TyR-inst a r) (TyR-inst b r)
      where
        open import Once.Adequacy.SpecGrammar.Conv using (kS)
        import Once.Spec.Grade as LG
        kS-id : ∀ k → kS k ≡ k
        kS-id (LG.mk-kind LG.Zero LG.pure) = refl
        kS-id (LG.mk-kind LG.Zero LG.act)  = refl
        kS-id (LG.mk-kind LG.Zero LG.eff)  = refl
        kS-id (LG.mk-kind LG.One  LG.pure) = refl
        kS-id (LG.mk-kind LG.One  LG.act)  = refl
        kS-id (LG.mk-kind LG.One  LG.eff)  = refl
        kS-id (LG.mk-kind LG.Many LG.pure) = refl
        kS-id (LG.mk-kind LG.Many LG.act)  = refl
        kS-id (LG.mk-kind LG.Many LG.eff)  = refl
    TyR-inst (c-μ f)   r = r-μ (FunR-inst f r)
    TyR-inst {A = ST.ν F φ} (c-ν f) r = r-ν (φS-id φ) (FunR-inst f r)
      where
        open import Once.Adequacy.SpecGrammar.Conv using (φS)
        import Once.Spec.Grade as LG
        φS-id : ∀ φ → φS φ ≡ φ
        φS-id LG.pureᶠ = refl
        φS-id LG.actᶠ  = refl

    FunR-inst : ∀ {a} {F : ST.Fun a} {τ τ′} → CleanF F → InstR τ τ′ → FunR Δ (F ST.⟨ τ ⟩F) (pfunS F ST.⟨ τ′ ⟩F)
    FunR-inst (c-K a)   r = r-K (TyR-inst a r)
    FunR-inst c-Id      r = r-Id
    FunR-inst (c-⊕ f g) r = r-⊕ (FunR-inst f r) (FunR-inst g r)
    FunR-inst (c-⊗ f g) r = r-⊗ (FunR-inst f r) (FunR-inst g r)

  -- An instance respecting the kinds does on both sides.
  respects-S : ∀ {a} {κ : ST.KCtx a} {τ τ′} → ST.Respects κ Δ τ → InstR τ τ′ → ST.Respects (kindsS κ) Δ τ′
  respects-S rs r i e = base-S (rs i e) (r i)
