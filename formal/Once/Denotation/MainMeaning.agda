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
open import Data.List using (List; take; []; _∷_)
open import Once.Denotation.Trace using (SigOpEvent)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type; Unit)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.TypeCheck.Elaborate using (ctxWithImportsAndPolys; PolyCtx)
open import Once.Type.DecEq using (_≟T_)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace; PrefixFamily; bnd; sat; coh)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.Behavior using (Behavior; mkBehavior)
open import Once.Surface.Context using (∅) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.Phase using (env0)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; DefMeanings)
import Once.Compile as C
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Spec.Module using (EffUU; AllFunsTyped; tnil; tcons; ModuleTyped; ModuleTyped-ef; MainExists; AllMainEffUU; HasValidMain-decl; ModuleMainEffUU-ef; ModuleMainExists-ef; PolysTyped; PolysTyped-ef; EntriesTyped)
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
-- Plan 0.103 phase 1c: THE MEANING OF THE TELESCOPE. Each ground entry means
-- its declaration-time derivation's meaning in its tail's environment — a
-- plain recursion, because `PolysTyped` is stated structurally.
defMeanings : (fmt : TargetNum) (at : ℕ → C.FunCtx) (pfis : List C.PolyFunInfo)
  → EntriesTyped at pfis → DefMeanings (C.buildPolyCtx pfis)
defMeanings fmt at []           _        = tt
defMeanings fmt at (pfi ∷ pfis) (t , ts) =
  (λ g → ⟦ t g ⟧ᶜ fmt (defMeanings fmt at pfis ts) tt) , defMeanings fmt at pfis ts

mainMeaningᵈ-go : ∀ {polys funs ctx} (fmt : TargetNum) (ρ : DefMeanings polys)
                  (aft : AllFunsTyped polys funs ctx)
                → MainExists aft → Σ-syntax (Usage 0) (λ _ → MClo)
mmd-dispatch : ∀ {polys nm bdy rest ctx ty Ψ} (fmt : TargetNum) (ρ : DefMeanings polys)
  (deriv : (ctxWithImportsAndPolys ctx polys) ⊢ᶜ bdy ∶ ty ⨾ Ψ)
  (rest-typed : AllFunsTyped polys rest (C.extendFunCtx ctx nm ty))
  (w : MainExists rest-typed)
  → Dec (nm ≡ "main") → Dec (ty ≡ EffUU) → Bool
  → Σ-syntax (Usage 0) (λ _ → MClo)

-- D143: `⟦_⟧ᶜ` runs on the RUNTIME environment `∅ ↾ Ψ`; `MClo` takes the
-- full (empty) one, so `env0` bridges — it is the identity.
mainMeaningᵈ-go fmt ρ (tcons {Ψ = Ψ} rf deriv rest) (inj₁ (_ , _ , refl)) =
  Ψ , (λ _ → ⟦ deriv ⟧ᶜ fmt ρ (env0 {Ψ} tt))
mainMeaningᵈ-go fmt ρ (tcons {fi = fi} {ty = ty} rf deriv rt) (inj₂ w) =
  mmd-dispatch fmt ρ deriv rt w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi)

mmd-dispatch {Ψ = Ψ} fmt ρ deriv rest-typed w (yes _) (yes refl) false =
  Ψ , (λ _ → ⟦ deriv ⟧ᶜ fmt ρ (env0 {Ψ} tt))
mmd-dispatch fmt ρ deriv rest-typed w (no _)  _          _     = mainMeaningᵈ-go fmt ρ rest-typed w
mmd-dispatch fmt ρ deriv rest-typed w (yes _) (no _)     _     = mainMeaningᵈ-go fmt ρ rest-typed w
mmd-dispatch fmt ρ deriv rest-typed w (yes _) (yes _)    true  = mainMeaningᵈ-go fmt ρ rest-typed w

mainMeaningᵈ-ef : ∀ (fmt : TargetNum) (m : C.Module) (ef : String ⊎ (List FunInfo × List C.PolyFunInfo))
  (mt : ModuleTyped-ef m ef)
  → ModuleMainEffUU-ef m ef mt → ModuleMainExists-ef m ef mt → PolysTyped-ef ef
  → Σ-syntax (Usage 0) (λ _ → MClo)
mainMeaningᵈ-ef fmt m (inj₂ (funs , polys)) mt amu me pts =
  mainMeaningᵈ-go fmt (defMeanings fmt (C.funCtxAt funs C.emptyFunCtx (C.buildPolyCtx polys)) polys pts) mt me

mainMeaningᵈ : ∀ (fmt : TargetNum) (m : C.Module) (mt : ModuleTyped m) → HasValidMain-decl m mt
             → PolysTyped m → Σ-syntax (Usage 0) (λ _ → MClo)
mainMeaningᵈ fmt m mt (amu , me) pts =
  mainMeaningᵈ-ef fmt m (C.extractFunctions (C.extractAliases m) m) mt amu me pts

------------------------------------------------------------------------
-- Run the direct closure to a Behavior (mirrors `MainExtract.runMainˢ`).
------------------------------------------------------------------------

-- D179: the depth-indexed trace FAMILY, not yet a `Behavior`. `Behavior` now
-- carries its three laws, and only the apex reference meaning below needs
-- them; every bridge lemma compares this family POINTWISE, so making the
-- intermediate a record would oblige each of them to rebuild the laws for a
-- closure it only passes through. (`take n` is gone with the cap: `bounded`
-- says the prefix is already that short.)
runMainᵈ : MClo → ℕ → List SigOpEvent
runMainᵈ dclo n = projTrace (dclo tt >>=T (λ clo → clo tt)) n

-- D179 (deferred proof, NOT an axiom): the direct meaning is a prefix family.
--
-- This is the `⟦_⟧ᶜ` analogue of `evalᴰ-good` (DenotPrefix), which proves
-- exactly this for the IR semantics by induction with `>>=T-pf` at each bind.
-- The same induction over TYPED DERIVATIONS discharges it — `⟦_⟧ᶜ`/`⟦_⟧ᵢ` are
-- built from the same `returnT`/`>>=T`/`emit` combinators — and until that
-- induction is written the statement is assumed HERE, about this chain, rather
-- than as a property of an arbitrary `MClo` (which would be FALSE: a bare
-- function may be any family at all).
postulate
  mainMeaningᵈ-pf :
    ∀ (fmt : TargetNum) (m : C.Module) (mt : ModuleTyped m) (hvm : HasValidMain-decl m mt) (pts : PolysTyped m)
    → PrefixFamily (proj₂ (mainMeaningᵈ fmt m mt hvm pts) tt >>=T (λ clo → clo tt))

-- THE direct reference meaning (discharges the apex `⟦_⟧ᵈ`).
meaningᵈ : ∀ (fmt : TargetNum) (m : C.Module) (mt : ModuleTyped m) → HasValidMain-decl m mt → PolysTyped m → Behavior
meaningᵈ fmt m mt hvm pts =
  mkBehavior (runMainᵈ (proj₂ (mainMeaningᵈ fmt m mt hvm pts)))
             -- plan 0.97: `Saturating` is on the trace alone now — nothing
             -- to project out of a pair.
             (coh pf) (bnd pf) (sat pf)
  where
    pf = mainMeaningᵈ-pf fmt m mt hvm pts
