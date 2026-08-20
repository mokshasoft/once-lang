-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
-- SCRATCH: mt-independence lemma for main-extract wiring (Plan 0.55 step 4).

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.MtIndep (fmt : FloatFormat) where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function using (case_of_)

open import Once.Type using (Type)
import Once.Compile as C
import Once.Denotation.SourceDenote as SD
open import Once.Surface.Syntax as Srf using (Expr; ∅; Usage; ⟦_⟧ᶜ; []; _∷_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)
open import Once.TypeCheck.Classify using (NamedCtx; SigEffectCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate using (ctxWithImportsAndSelfAndPolys; PolyCtx; _≟T_)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Denotation.Realize using (realize)
open import Once.Parser using (FunInfo)
open FunInfo
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.ModuleComplete using (EffUU)
open import Once.Adequacy.RealizeInvariant fmt using (realize-invariant)

-- `Usage 0` is a singleton.
usage0-unique : (Ψ : Usage 0) → Ψ ≡ []
usage0-unique [] = refl

-- realize-invariant specialised to the (size-0) main context, absorbing the
-- `Usage 0` mismatch of the two derivations.
RI0 : ∀ (c : C.FunCtx) (p : PolyCtx) (s : SigEffectCtx) (nm : String) (e : RawExpr)
  {Ψ₁ Ψ₂ : Usage 0}
  (d₁ : (ctxWithImportsAndSelfAndPolys c p s nm EffUU) ⊢ᶜ e ∶ EffUU ⨾ Ψ₁)
  (d₂ : (ctxWithImportsAndSelfAndPolys c p s nm EffUU) ⊢ᶜ e ∶ EffUU ⨾ Ψ₂)
  (dγ : ⟦ ⟦ ∅ ⟧ᶜ ⟧ᴰ) (n : ℕ) →
  SD.⟦ realize d₁ ⟧ˢ fmt dγ n ≡ SD.⟦ realize d₂ ⟧ˢ fmt dγ n
RI0 c p s nm e {Ψ₁} {Ψ₂} d₁ d₂ dγ n
  rewrite usage0-unique Ψ₁ | usage0-unique Ψ₂ = realize-invariant d₁ d₂ dγ n

-- When the head IS main, `mainRealized-go` returns `realize deriv` for ANY
-- witness (it does not trust `me`'s `inj₁`; it re-checks `isMain(head)`).
head-main-realize : ∀ {polys sigEffs rest ctx} (fi : FunInfo)
  {Ψ : Usage (NamedCtx.size (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) EffUU))}
  (rf : C.resolveFunType ctx polys (funType fi) (funBody fi) ≡ inj₂ EffUU)
  (d : (ctxWithImportsAndSelfAndPolys ctx polys sigEffs (funName fi) EffUU) ⊢ᶜ funBody fi ∶ EffUU ⨾ Ψ)
  (rt : AS.AllFunsTyped polys sigEffs rest (C.extendFunCtx ctx (funName fi) EffUU))
  (w : MC.MainExists (AS.tcons {fi = fi} rf d rt)) →
  funName fi ≡ "main" → funIsPrimitive fi ≡ false →
  MC.mainRealized-go (AS.tcons {fi = fi} rf d rt) w ≡ (Ψ , realize d)
head-main-realize fi rf d rt (inj₁ (_ , _ , refl)) hp hpr = refl
head-main-realize fi rf d rt (inj₂ w') hp hpr
  with funName fi ≟str "main" | EffUU ≟T EffUU | funIsPrimitive fi
... | yes _  | yes refl | false = refl
... | no ¬p  | _        | _     = ⊥-elim (¬p hp)
... | yes _  | no ¬e    | _     = ⊥-elim (¬e refl)
... | yes _  | yes _    | true  = ⊥-elim (case hpr of λ ())

-- THE mt-independence lemma: any two typing derivations of the SAME module
-- (`funs`) realize the SAME `main` denotationally.
mt-den-indep : ∀ {polys sigEffs funs ctx}
  (mt bt : AS.AllFunsTyped polys sigEffs funs ctx)
  (me : MC.MainExists mt) (bme : MC.MainExists bt)
  (dγ : ⟦ ⟦ ∅ ⟧ᶜ ⟧ᴰ) (n : ℕ) →
  SD.⟦ proj₂ (MC.mainRealized-go mt me) ⟧ˢ fmt dγ n
  ≡ SD.⟦ proj₂ (MC.mainRealized-go bt bme) ⟧ˢ fmt dγ n
mt-den-indep AS.tnil AS.tnil me bme dγ n = ⊥-elim me
mt-den-indep {polys = polys} {sigEffs = sigEffs} {ctx = ctx}
             (AS.tcons {fi = fi} {ty = ty₁} rf₁ d₁ rt₁) (AS.tcons {ty = ty₂} rf₂ d₂ rt₂) me bme dγ n
  with inj₂-injective (trans (sym rf₁) rf₂)
mt-den-indep {polys = polys} {sigEffs = sigEffs} {ctx = ctx}
             (AS.tcons {fi = fi} {ty = ty₁} rf₁ d₁ rt₁) (AS.tcons rf₂ d₂ rt₂) me bme dγ n
  | refl = dispatch me bme
  where
    -- mrg-dispatch spelled out so `with` can abstract the shared scrutinees.
    dispatch2 : (w₁ : MC.MainExists rt₁) (w₂ : MC.MainExists rt₂) →
      SD.⟦ proj₂ (MC.mrg-dispatch d₁ rt₁ w₁ (funName fi ≟str "main") (ty₁ ≟T EffUU) (funIsPrimitive fi)) ⟧ˢ fmt dγ n
      ≡ SD.⟦ proj₂ (MC.mrg-dispatch d₂ rt₂ w₂ (funName fi ≟str "main") (ty₁ ≟T EffUU) (funIsPrimitive fi)) ⟧ˢ fmt dγ n
    dispatch2 w₁ w₂ with funName fi ≟str "main" | ty₁ ≟T EffUU | funIsPrimitive fi
    ... | yes _ | yes refl | false = RI0 ctx polys sigEffs (funName fi) (funBody fi) d₁ d₂ dγ n
    ... | no _  | _        | _     = mt-den-indep rt₁ rt₂ w₁ w₂ dγ n
    ... | yes _ | no _     | _     = mt-den-indep rt₁ rt₂ w₁ w₂ dγ n
    ... | yes _ | yes refl | true  = mt-den-indep rt₁ rt₂ w₁ w₂ dγ n

    dispatch : (me : MC.MainExists (AS.tcons {fi = fi} rf₁ d₁ rt₁)) (bme : MC.MainExists (AS.tcons {fi = fi} rf₂ d₂ rt₂)) →
      SD.⟦ proj₂ (MC.mainRealized-go (AS.tcons {fi = fi} rf₁ d₁ rt₁) me) ⟧ˢ fmt dγ n
      ≡ SD.⟦ proj₂ (MC.mainRealized-go (AS.tcons {fi = fi} rf₂ d₂ rt₂) bme) ⟧ˢ fmt dγ n
    dispatch (inj₁ (p₁ , q₁ , refl)) (inj₁ (p₂ , q₂ , refl)) =
      RI0 ctx polys sigEffs (funName fi) (funBody fi) d₁ d₂ dγ n
    dispatch (inj₁ (p₁ , q₁ , refl)) (inj₂ w₂) =
      trans (RI0 ctx polys sigEffs (funName fi) (funBody fi) d₁ d₂ dγ n)
            (sym (cong (λ x → SD.⟦ proj₂ x ⟧ˢ fmt dγ n)
                       (head-main-realize fi rf₂ d₂ rt₂ (inj₂ w₂) p₁ q₁)))
    dispatch (inj₂ w₁) (inj₁ (p₂ , q₂ , refl)) =
      trans (cong (λ x → SD.⟦ proj₂ x ⟧ˢ fmt dγ n)
                  (head-main-realize fi rf₁ d₁ rt₁ (inj₂ w₁) p₂ q₂))
            (RI0 ctx polys sigEffs (funName fi) (funBody fi) d₁ d₂ dγ n)
    dispatch (inj₂ w₁) (inj₂ w₂) = dispatch2 w₁ w₂
