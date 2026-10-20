-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.ModRel — the compiler's module map and the Spec's,
-- related (plan 0.121 §3.6, F2): the same paths, each module's declarations
-- as written in both grammars (`ModRel`); a module the compiler finds, the
-- Spec finds at the same path (`find`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.ModRel where

open import Data.List using (List)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Spec.Surface.Syntax as S
import Once.Spec.Surface.Resolution as SR
import Once.Lang.Resolution as LR
open import Once.Parser.Module.Core using (Module; mkModule)
open import Once.Parser.Module.Resolve using (ModuleMap)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb)

ModRel : ModuleMap → SR.ModuleMap → Set
ModRel = Pointwise (λ q q′ → (proj₁ q ≡ proj₁ q′) × Pointwise DEmb (Module.decls (proj₂ q)) (S.Module.decls (proj₂ q′)))

find : ∀ {mm mm′ p ds} → ModRel mm mm′ → LR.FirstAt p (mkModule ds) mm
     → Σ[ ds′ ∈ List S.Decl ] SR.FirstAt p (S.mkModule ds′) mm′ × Pointwise DEmb ds ds′
find ((refl , pw) ∷ _) LR.fa-here = _ , SR.fa-here , pw
find ((refl , _) ∷ mr) (LR.fa-there ne fa) = let (ds′ , fa′ , pw) = find mr fa in ds′ , SR.fa-there ne fa′ , pw
