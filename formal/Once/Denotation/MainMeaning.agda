-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.MainMeaning — the DIRECT reference meaning of `main`
-- (Plan 0.58, OCP-0006). Mirrors `ModuleComplete.mainRealized` but returns the
-- IR-free direct closure `⟦ deriv ⟧ᶜ` (Once.Denotation.Meaning) instead of
-- `realize deriv`, and runs it to a `Behavior`. This is what discharges the
-- apex `⟦_⟧ᵈ` postulate (in `Once.Adequacy.Compile`).
------------------------------------------------------------------------

module Once.Denotation.MainMeaning where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.List using (List; take)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type; Unit)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.TypeCheck.Elaborate using (ctxWithImportsAndSelfAndPolys; PolyCtx; _≟T_)
open import Once.TypeCheck.Classify using (SigEffectCtx; NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.Behavior using (Behavior)
open import Once.Surface.Context using (∅) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ)
import Once.Compile as C
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.ModuleComplete using (EffUU)
open import Once.Parser using (FunInfo)
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open FunInfo

-- The direct main closure: the denotation of `main`'s (∅-context) EffUU body.
MClo : Set
MClo = ⟦ ⟦ ∅ ⟧ᶜᵗ ⟧ᴰ → T ⟦ EffUU ⟧ᴰ

------------------------------------------------------------------------
-- The first-`isMain` selector, mirroring `mainRealized-go`/`mrg-dispatch`
-- but reading `⟦ deriv ⟧ᶜ` (the direct meaning) off the derivation.
------------------------------------------------------------------------

-- Plan 0.73 (D113): the format, explicit — this chain is recursive and its
-- reduction is what `MainExtract`/`MeaningBridge` rewrite through.
mainMeaningᵈ-go : ∀ {polys sigEffs funs ctx} (fmt : TargetNum)
                  (aft : AS.AllFunsTyped polys sigEffs funs ctx)
                → MC.MainExists aft → Σ-syntax (Usage 0) (λ _ → MClo)
mmd-dispatch : ∀ {polys sigEffs nm bdy rest ctx ty Ψ} (fmt : TargetNum)
  (deriv : (ctxWithImportsAndSelfAndPolys ctx polys sigEffs nm ty) ⊢ᶜ bdy ∶ ty ⨾ Ψ)
  (rest-typed : AS.AllFunsTyped polys sigEffs rest (C.extendFunCtx ctx nm ty))
  (w : MC.MainExists rest-typed)
  → Dec (nm ≡ "main") → Dec (ty ≡ EffUU) → Bool
  → Σ-syntax (Usage 0) (λ _ → MClo)

mainMeaningᵈ-go fmt (AS.tcons {Ψ = Ψ} rf deriv rest) (inj₁ (_ , _ , refl)) = Ψ , (⟦ deriv ⟧ᶜ fmt)
mainMeaningᵈ-go fmt (AS.tcons {fi = fi} {ty = ty} rf deriv rt) (inj₂ w) =
  mmd-dispatch fmt deriv rt w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)

mmd-dispatch {Ψ = Ψ} fmt deriv rest-typed w (yes _) (yes refl) false = Ψ , (⟦ deriv ⟧ᶜ fmt)
mmd-dispatch fmt deriv rest-typed w (no _)  _          _     = mainMeaningᵈ-go fmt rest-typed w
mmd-dispatch fmt deriv rest-typed w (yes _) (no _)     _     = mainMeaningᵈ-go fmt rest-typed w
mmd-dispatch fmt deriv rest-typed w (yes _) (yes _)    true  = mainMeaningᵈ-go fmt rest-typed w

mainMeaningᵈ-ef : ∀ (fmt : TargetNum) (m : C.Module) (ef : String ⊎ (List FunInfo × List C.PolyFunInfo))
  (mt : AS.ModuleTyped-ef m ef)
  → MC.ModuleMainEffUU-ef m ef mt → MC.ModuleMainExists-ef m ef mt
  → Σ-syntax (Usage 0) (λ _ → MClo)
mainMeaningᵈ-ef fmt m (inj₂ (funs , polys)) mt amu me = mainMeaningᵈ-go fmt mt me

mainMeaningᵈ : ∀ (fmt : TargetNum) (m : C.Module) (mt : AS.ModuleTyped m) → MC.HasValidMain-decl m mt
             → Σ-syntax (Usage 0) (λ _ → MClo)
mainMeaningᵈ fmt m mt (amu , me) =
  mainMeaningᵈ-ef fmt m (C.extractFunctions (C.extractAliases m) m) mt amu me

------------------------------------------------------------------------
-- Run the direct closure to a Behavior (mirrors `MainExtract.runMainˢ`).
------------------------------------------------------------------------

runMainᵈ : MClo → Behavior
runMainᵈ dclo n = take n (projTrace (dclo tt >>=T (λ clo → clo tt)) n)

-- THE direct reference meaning (discharges the apex `⟦_⟧ᵈ`).
meaningᵈ : ∀ (fmt : TargetNum) (m : C.Module) (mt : AS.ModuleTyped m) → MC.HasValidMain-decl m mt → Behavior
meaningᵈ fmt m mt hvm = runMainᵈ (proj₂ (mainMeaningᵈ fmt m mt hvm))
