-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MainMeaningBridge — the SELECTION LEMMA that discharges the
-- apex `bridgeᵈ` (Plan 0.58, OCP-0006).
--
-- `mainRealized` (surface, `realize`) and `mainMeaningᵈ` (direct, `⟦_⟧ᶜ`) walk
-- the SAME first-`main` dispatch (`mainRealized-go`/`mmd-dispatch` vs
-- `mainMeaningᵈ-go`/`mmd-dispatch`), differing ONLY at the leaf: `realize deriv`
-- vs `⟦ deriv ⟧ᶜ`. A parallel induction over that dispatch reduces the whole
-- `runMainˢ ≡ runMainᵈ` claim to `bridge-c deriv` applied at `main : EffUU`,
-- env `∅` (`RelEnv ∅ = ⊤`), and the top-level thunk `tt` — funext-free.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.MainMeaningBridge (fmt : TargetNum) where


open import Once.Spec.Module using (EffUU; AllFunsTyped; HasValidMain-decl; MainExists; ModuleMainEffUU-ef; ModuleMainExists-ef; ModuleTyped; ModuleTyped-ef; tcons)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.List using (List; take; _++_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)

open import Once.Type using (Type; Unit)
open import Once.Surface.Syntax using (Expr; Usage)
open import Once.Surface.Context using (∅) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.TypeCheck.Elaborate using (ctxWithImportsAndSelfAndPolys; _≟T_)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace; valueT)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.Behavior using (Behavior)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ)
open import Once.Denotation.Realize using (realize)
import Once.Compile as C
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.MainExtract fmt as ME
import Once.Denotation.MainMeaning as MM
open import Once.Adequacy.MeaningBridge fmt using (bridge-c; RelEnv; RelEnv↾; mk↾; rel-env0)
open import Once.Denotation.Phase using (env0)
open import Once.Parser using (FunInfo)
open FunInfo

------------------------------------------------------------------------
-- The leaf: at `main : EffUU` (empty context, so the env / related-env are
-- both `tt`), the surface run and the direct run agree — `bridge-c deriv`
-- applied to the top-level thunk `tt`.
------------------------------------------------------------------------

main-bridge-leaf : ∀ {polys sigEffs nm bdy ctx Ψ}
  (deriv : (ctxWithImportsAndSelfAndPolys ctx polys sigEffs nm EffUU) ⊢ᶜ bdy ∶ EffUU ⨾ Ψ)
  (n : ℕ)
  → ME.runMainˢ (realize deriv) n
    ≡ MM.runMainᵈ (λ _ → ⟦ deriv ⟧ᶜ fmt (env0 {Ψ} tt)) n
main-bridge-leaf {Ψ = Ψ} deriv n =
  let bd = bridge-c deriv {env0 {Ψ} tt} {env0 {Ψ} tt} rel-env0 n
  in sym (cong (take n)
       (cong₂ _++_ (proj₁ bd) (proj₁ (proj₂ bd {tt} {tt} tt n))))

------------------------------------------------------------------------
-- The parallel dispatch — identical branching to `mrg-dispatch`/`mmd-dispatch`.
------------------------------------------------------------------------

main-bridge-go : ∀ {polys sigEffs funs ctx}
  (aft : AllFunsTyped polys sigEffs funs ctx) (me : MainExists aft) (n : ℕ)
  → ME.runMainˢ (proj₂ (MC.mainRealized-go aft me)) n
    ≡ MM.runMainᵈ (proj₂ (MM.mainMeaningᵈ-go fmt aft me)) n
main-bridge-dispatch : ∀ {polys sigEffs nm bdy rest ctx ty Ψ}
  (deriv : (ctxWithImportsAndSelfAndPolys ctx polys sigEffs nm ty) ⊢ᶜ bdy ∶ ty ⨾ Ψ)
  (rt : AllFunsTyped polys sigEffs rest (C.extendFunCtx ctx nm ty))
  (w : MainExists rt)
  (dn : Dec (nm ≡ "main")) (dt : Dec (ty ≡ EffUU)) (b : Bool) (n : ℕ)
  → ME.runMainˢ (proj₂ (MC.mrg-dispatch deriv rt w dn dt b)) n
    ≡ MM.runMainᵈ (proj₂ (MM.mmd-dispatch fmt deriv rt w dn dt b)) n

main-bridge-go (tcons rf deriv rest) (inj₁ (_ , _ , refl)) n = main-bridge-leaf deriv n
main-bridge-go (tcons {fi = fi} {ty = ty} rf deriv rt) (inj₂ w) n =
  main-bridge-dispatch deriv rt w (funName fi ≟str "main") (ty ≟T EffUU) (funIsPrimitive fi) n

main-bridge-dispatch deriv rt w (yes _) (yes refl) false n = main-bridge-leaf deriv n
main-bridge-dispatch deriv rt w (no _)  _          _     n = main-bridge-go rt w n
main-bridge-dispatch deriv rt w (yes _) (no _)     _     n = main-bridge-go rt w n
main-bridge-dispatch deriv rt w (yes _) (yes refl) true  n = main-bridge-go rt w n

------------------------------------------------------------------------
-- Lift through the `-ef` layer (mirrors `mainRealized-ef`/`mainMeaningᵈ-ef`;
-- the `inj₁` case is impossible — `ModuleTyped-ef m (inj₁ _) = ⊥`).
------------------------------------------------------------------------

main-bridge-ef : ∀ (m : C.Module) (ef : String ⊎ (List FunInfo × List C.PolyFunInfo))
  (mt : ModuleTyped-ef m ef)
  (amu : ModuleMainEffUU-ef m ef mt) (me : ModuleMainExists-ef m ef mt) (n : ℕ)
  → ME.runMainˢ (proj₂ (MC.mainRealized-ef m ef mt amu me)) n
    ≡ MM.runMainᵈ (proj₂ (MM.mainMeaningᵈ-ef fmt m ef mt amu me)) n
main-bridge-ef m (inj₂ (funs , polys)) mt amu me n = main-bridge-go mt me n

-- THE selection lemma: `⟦ tp ⟧ˢ n ≡ ⟦ tp ⟧ᵈ n` (discharges the apex `bridgeᵈ`).
main-bridge : ∀ (m : C.Module) (mt : ModuleTyped m) (hvm : HasValidMain-decl m mt) (n : ℕ)
            → ME.runMainˢ (proj₂ (MC.mainRealized m mt hvm)) n
              ≡ MM.runMainᵈ (proj₂ (MM.mainMeaningᵈ fmt m mt hvm)) n
main-bridge m mt (amu , me) n =
  main-bridge-ef m (C.extractFunctions (C.extractAliases m) m) mt amu me n
