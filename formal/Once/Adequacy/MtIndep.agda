-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
-- SCRATCH: mt-independence lemma for main-extract wiring (Plan 0.55 step 4).

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.SourceDenote using (DefsSem)

-- plan 0.103 1c: in any definitions environment.
module Once.Adequacy.MtIndep (fmt : TargetNum) (σ : DefsSem) where


open import Once.Spec.Module using (EffUU; ModTele; []; ffi; mono; poly; MainIn; ctxOf; addImp)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
import Data.Empty
open import Data.Maybe.Properties using (just-injective)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function using (case_of_)

open import Once.Type using (Type)
import Once.Compile as C
import Once.Denotation.SourceDenote as SD
open import Once.Surface.Syntax as Srf using (Expr; ∅; Usage; ⟦_⟧ᶜ; []; _∷_; _↾_)
open import Once.Denotation.Phase using (env0)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate using (ctxWithImportsAndPolys; PolyCtx)
open import Once.Type.DecEq using (_≟T_)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.Realize using (realize)
open import Once.Parser using (FunInfo)
open FunInfo
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.RealizeInvariant fmt using (realize-invariant)

-- `Usage 0` is a singleton.
usage0-unique : (Ψ : Usage 0) → Ψ ≡ []
usage0-unique [] = refl


-- realize-invariant specialised to the (size-0) main context, absorbing the
-- `Usage 0` mismatch of the two derivations.
RI0 : ∀ (c : C.FunCtx) (p : PolyCtx) (nm : String) (e : RawExpr)
  {Ψ₁ Ψ₂ : Usage 0}
  (d₁ : (ctxWithImportsAndPolys c p) ⊢ᶜ e ∶ EffUU ⨾ Ψ₁)
  (d₂ : (ctxWithImportsAndPolys c p) ⊢ᶜ e ∶ EffUU ⨾ Ψ₂)
  (dγ : ⟦ ⟦ ∅ ⟧ᶜ ⟧ᴰ) →
  SD.⟦ realize d₁ ⟧ˢ fmt σ (env0 {Ψ₁} dγ) ≡ SD.⟦ realize d₂ ⟧ˢ fmt σ (env0 {Ψ₂} dγ)
RI0 c p nm e {[]} {[]} d₁ d₂ dγ = realize-invariant d₁ d₂ σ dγ

-- When the head IS main, `mainRealized-go` returns `realize deriv` for ANY
-- witness (it does not trust `me`'s `inj₁`; it re-checks `isMain(head)`).
true≢false : true ≡ false → Data.Empty.⊥
true≢false ()

-- D241 (plan 0.103 6c′): two typings of ONE telescope realize `main` alike.
mt-den-indep : ∀ {sc es} (mt bt : ModTele sc es) (me : MainIn mt) (bme : MainIn bt)
  (dγ : ⟦ ⟦ ∅ ⟧ᶜ ⟧ᴰ) →
  SD.⟦ proj₂ (MC.mainRealized-go mt me) ⟧ˢ fmt σ (env0 {proj₁ (MC.mainRealized-go mt me)} dγ)
  ≡ SD.⟦ proj₂ (MC.mainRealized-go bt bme) ⟧ˢ fmt σ (env0 {proj₁ (MC.mainRealized-go bt bme)} dγ)
mt-den-indep [] [] () bme dγ
mt-den-indep (ffi _ et₁ _ _ _ rt₁) (ffi _ et₂ _ _ _ rt₂) me bme dγ
  with just-injective (trans (sym et₁) et₂)
... | refl = mt-den-indep rt₁ rt₂ me bme dγ
mt-den-indep (ffi ep₁ _ _ _ _ _) (mono ep₂ _ _ _ _) _ _ _ = ⊥-elim (true≢false (trans (sym ep₁) ep₂))
mt-den-indep (mono ep₁ _ _ _ _) (ffi ep₂ _ _ _ _ _) _ _ _ = ⊥-elim (true≢false (trans (sym ep₂) ep₁))
mt-den-indep (poly _ rt₁) (poly _ rt₂) me bme dγ = mt-den-indep rt₁ rt₂ me bme dγ
mt-den-indep {sc} (mono {fi = fi} {ty = ty₁} {es = es} ep₁ rf₁ g₁ d₁ rt₁) (mono {ty = ty₂} ep₂ rf₂ g₂ d₂ rt₂) me bme dγ
  with inj₂-injective (trans (sym rf₁) rf₂)
... | refl = dispatch me bme
  where
    ctx = ctxOf sc
    RI : ∀ {Ψ₁ Ψ₂ : Usage 0} (e₁ : ctx ⊢ᶜ funBody fi ∶ EffUU ⨾ Ψ₁) (e₂ : ctx ⊢ᶜ funBody fi ∶ EffUU ⨾ Ψ₂)
       → SD.⟦ realize e₁ ⟧ˢ fmt σ (env0 {Ψ₁} dγ) ≡ SD.⟦ realize e₂ ⟧ˢ fmt σ (env0 {Ψ₂} dγ)
    RI {[]} {[]} e₁ e₂ = realize-invariant e₁ e₂ σ dγ
    dispatch2 : (w₁ : MainIn rt₁) (w₂ : MainIn rt₂) (dm : Dec (funName fi ≡ "main")) (de : Dec (ty₁ ≡ EffUU)) →
      SD.⟦ proj₂ (MC.mrg-dispatch {sc = sc} {fi = fi} {es = es} d₁ {rt₁} w₁ dm de) ⟧ˢ fmt σ (env0 {proj₁ (MC.mrg-dispatch {sc = sc} {fi = fi} {es = es} d₁ {rt₁} w₁ dm de)} dγ)
      ≡ SD.⟦ proj₂ (MC.mrg-dispatch {sc = sc} {fi = fi} {es = es} d₂ {rt₂} w₂ dm de) ⟧ˢ fmt σ (env0 {proj₁ (MC.mrg-dispatch {sc = sc} {fi = fi} {es = es} d₂ {rt₂} w₂ dm de)} dγ)
    dispatch2 w₁ w₂ (yes _) (yes refl) = RI d₁ d₂
    dispatch2 w₁ w₂ (no _) _ = mt-den-indep rt₁ rt₂ w₁ w₂ dγ
    dispatch2 w₁ w₂ (yes _) (no _) = mt-den-indep rt₁ rt₂ w₁ w₂ dγ
    -- A `main : IO Unit` at the head is what the other side's dispatch picks.
    head : ∀ {Ψ} (d : ctx ⊢ᶜ funBody fi ∶ EffUU ⨾ Ψ) {rt : ModTele (addImp sc (funName fi) EffUU) es} (w : MainIn rt)
         → funName fi ≡ "main"
         → MC.mrg-dispatch {sc = sc} {fi = fi} {es = es} d {rt} w (funName fi ≟str "main") (EffUU ≟T EffUU) ≡ (Ψ , realize d)
    head d w hp with funName fi ≟str "main" | EffUU ≟T EffUU
    ... | yes _ | yes refl = refl
    ... | no ¬p | _ = ⊥-elim (¬p hp)
    ... | yes _ | no ¬e = ⊥-elim (¬e refl)
    dispatch : (me : MainIn (mono {sc = sc} {fi = fi} ep₁ rf₁ g₁ d₁ rt₁)) (bme : MainIn (mono {sc = sc} {fi = fi} ep₂ rf₂ g₂ d₂ rt₂)) →
      SD.⟦ proj₂ (MC.mainRealized-go (mono {sc = sc} {fi = fi} ep₁ rf₁ g₁ d₁ rt₁) me) ⟧ˢ fmt σ (env0 {proj₁ (MC.mainRealized-go (mono {sc = sc} {fi = fi} ep₁ rf₁ g₁ d₁ rt₁) me)} dγ)
      ≡ SD.⟦ proj₂ (MC.mainRealized-go (mono {sc = sc} {fi = fi} ep₂ rf₂ g₂ d₂ rt₂) bme) ⟧ˢ fmt σ (env0 {proj₁ (MC.mainRealized-go (mono {sc = sc} {fi = fi} ep₂ rf₂ g₂ d₂ rt₂) bme)} dγ)
    dispatch (inj₁ (_ , refl)) (inj₁ (_ , refl)) = RI d₁ d₂
    dispatch (inj₁ (p₁ , refl)) (inj₂ w₂) =
      trans (RI d₁ d₂) (sym (cong (λ x → SD.⟦ proj₂ x ⟧ˢ fmt σ (env0 {proj₁ x} dγ)) (head d₂ w₂ p₁)))
    dispatch (inj₂ w₁) (inj₁ (p₂ , refl)) =
      trans (cong (λ x → SD.⟦ proj₂ x ⟧ˢ fmt σ (env0 {proj₁ x} dγ)) (head d₁ w₁ p₂)) (RI d₁ d₂)
    dispatch (inj₂ w₁) (inj₂ w₂) = dispatch2 w₁ w₂ (funName fi ≟str "main") (ty₁ ≟T EffUU)
