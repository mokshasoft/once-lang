-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Schema — the compiler's definitions signature as
-- the Spec's (plan 0.121, the core bridge).
--
-- Plan 0.122: the compiler's schemas and definitions table ARE the Spec's;
-- the translations are identities (kept as the front-end bridge reads them).
------------------------------------------------------------------------

module Once.Adequacy.SpecCore.Schema where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SS

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
