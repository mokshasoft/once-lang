-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonReflectPolyTransport — Plan 0.51 reverse poly-context
-- transport. The mirror of `CanonPolyTransport.polys-transport-{ᵢ,ᵐ,ᶜ}`: a `⊢ᶜ`
-- derivation at the canonExpr'd poly context `canonPolysCtx b p` REFLECTS back to
-- one at `p` (the expression is UNCHANGED — only the context's poly bodies move).
-- The foundational commutes (`lookupPoly-canon`, `removePoly-canon`,
-- `composeArgB-polys-canon`, …) are EQUALITIES reused from the forward module.
------------------------------------------------------------------------

module Once.Adequacy.CanonReflectPolyTransport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; PolyType)
open import Once.Surface.Syntax as Surface using (zeroUsage)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr)
open import Once.TypeCheck.Classify
  using (PolyCtx; NamedCtx; mkCtx; lookupPoly; removePoly; ctxWithImportsAndPolys; composeMid)
open import Once.TypeCheck.Judgment
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPolyTransport
  using (canonPolysCtx; canon-entry; cpc; PInB; lookupPoly-canon; removePoly-canon;
         removePoly-PInB; composeArgB-polys-canon; domainOfHead-polys-canon)
open import Once.Adequacy.CanonReflectMutual using (canon-reflects-ᶜ)

------------------------------------------------------------------------
-- composeMid reflects through the poly-context canonExpr (reuse the forward
-- component equalities + sym, applied to the REFLECTED arms).
------------------------------------------------------------------------

composeMid-polys-decanon : ∀ (b : List String) (ctx : NamedCtx) {fa g A′ π′ B″ A″ π B′} {A B}
  → ctx ⊢ᵐ fa ∶ A″ ⇨[ π′ ] B″
  → ctx ⊢ᵐ g ∶ A′ ⇨[ π ] B′
  → composeMid (cpc b ctx) fa g A ≡ just B
  → composeMid ctx fa g A ≡ just B
composeMid-polys-decanon b ctx {A = A} df dg cm
  rewrite sym (composeArgB-polys-canon b ctx A dg)
        | sym (domainOfHead-polys-canon b ctx df) = cm

-- just-injection for the poly lookup recovery.
just-inj : ∀ {A : Set} {x y : A} → (just x ≡ just y) → x ≡ y
just-inj refl = refl

n≢j : ∀ {A : Set} {y : A} → nothing ≡ just y → ⊥
n≢j ()

------------------------------------------------------------------------
-- The reverse mutual transport. `⊢ᵍ` is poly-independent.
------------------------------------------------------------------------

polys-reflect-ᵍ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) {e A}
  → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵍ e ∶ A
  → mkCtx n Γ Δ f i p s ⊢ᵍ e ∶ A
polys-reflect-ᵍ b p (g-int n)          = g-int n
polys-reflect-ᵍ b p (g-terminal lL lI) = g-terminal lL lI
polys-reflect-ᵍ b p (g-pair d₁ d₂)     = g-pair (polys-reflect-ᵍ b p d₁) (polys-reflect-ᵍ b p d₂)
polys-reflect-ᵍ b p (g-inl d)          = g-inl (polys-reflect-ᵍ b p d)
polys-reflect-ᵍ b p (g-inr d)          = g-inr (polys-reflect-ᵍ b p d)
polys-reflect-ᵍ b p (g-In wf d)        = g-In wf (polys-reflect-ᵍ b p d)

{-# TERMINATING #-}
mutual
  polys-reflect-ᵢ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵢ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i p s ⊢ᵢ e ∶ A ⨾ Ψ
  polys-reflect-ᵢ b p pib (t-int n)  = t-int n
  polys-reflect-ᵢ b p pib (t-str s)  = t-str s
  polys-reflect-ᵢ b p pib t-unit     = t-unit
  polys-reflect-ᵢ b p pib t-unit-var = t-unit-var
  polys-reflect-ᵢ b p pib (t-var-local ¬u lk) = t-var-local ¬u lk
  polys-reflect-ᵢ b p pib (t-var-qualified imp) = t-var-qualified imp
  polys-reflect-ᵢ b p pib (t-var-resolved imp) = t-var-resolved imp
  polys-reflect-ᵢ b p pib (t-var-import ¬u lkn imp) = t-var-import ¬u lkn imp
  polys-reflect-ᵢ b p pib (t-annot d) = t-annot (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᵢ b p pib (t-pair d₁ d₂) = t-pair (polys-reflect-ᵢ b p pib d₁) (polys-reflect-ᵢ b p pib d₂)
  polys-reflect-ᵢ b p pib (t-neg d) = t-neg (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᵢ b p pib (t-let d₁ d₂) = t-let (polys-reflect-ᵢ b p pib d₁) (polys-reflect-ᵢ b p pib d₂)
  polys-reflect-ᵢ b p pib (t-case ds dL dR) =
    t-case (polys-reflect-ᵢ b p pib ds) (polys-reflect-ᵢ b p pib dL) (polys-reflect-ᵢ b p pib dR)
  polys-reflect-ᵢ b p pib (t-binop-arith pr d₁ d₂) = t-binop-arith pr (polys-reflect-ᵢ b p pib d₁) (polys-reflect-ᵢ b p pib d₂)
  polys-reflect-ᵢ b p pib (t-binop-cmp pr d₁ d₂) = t-binop-cmp pr (polys-reflect-ᵢ b p pib d₁) (polys-reflect-ᵢ b p pib d₂)
  polys-reflect-ᵢ b p pib (t-id-app d) = t-id-app (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᵢ b p pib (t-fst-app d) = t-fst-app (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᵢ b p pib (t-snd-app d) = t-snd-app (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᵢ b p pib (t-terminal-app d) = t-terminal-app (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᵢ b p pib (t-arr-app-infer d) = t-arr-app-infer (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᵢ b p pib (t-apply-app-infer d) = t-apply-app-infer (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᵢ b p pib (t-app cls df dx) = t-app cls (polys-reflect-ᵢ b p pib df) (polys-reflect-ᶜ b p pib dx)
  polys-reflect-ᵢ b p pib (t-effApp cls df dx) = t-effApp cls (polys-reflect-ᵢ b p pib df) (polys-reflect-ᶜ b p pib dx)

  polys-reflect-ᵐ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → ∀ {e A π B}
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵐ e ∶ A ⇨[ π ] B
    → mkCtx n Γ Δ f i p s ⊢ᵐ e ∶ A ⇨[ π ] B
  polys-reflect-ᵐ b p pib (m-id ll li) = m-id ll li
  polys-reflect-ᵐ b p pib (m-fst ll li) = m-fst ll li
  polys-reflect-ᵐ b p pib (m-snd ll li) = m-snd ll li
  polys-reflect-ᵐ b p pib (m-terminal ll li) = m-terminal ll li
  polys-reflect-ᵐ b p pib (m-initial ll li) = m-initial ll li
  polys-reflect-ᵐ b p pib (m-inl ll li) = m-inl ll li
  polys-reflect-ᵐ b p pib (m-inr ll li) = m-inr ll li
  polys-reflect-ᵐ b {n = n} {Γ = Γ} {Δ = Δ} {f = fr} {i = i} {s = s} p pib (m-compose cm df dg) =
    m-compose (composeMid-polys-decanon b (mkCtx n Γ Δ fr i p s)
                (polys-reflect-ᵐ b p pib df) (polys-reflect-ᵐ b p pib dg) cm)
              (polys-reflect-ᵐ b p pib df) (polys-reflect-ᵐ b p pib dg)
  polys-reflect-ᵐ b p pib (m-case df dg) = m-case (polys-reflect-ᵐ b p pib df) (polys-reflect-ᵐ b p pib dg)
  polys-reflect-ᵐ b p pib (m-pair df dg) = m-pair (polys-reflect-ᵐ b p pib df) (polys-reflect-ᵐ b p pib dg)
  polys-reflect-ᵐ b p pib (m-curry df) = m-curry (polys-reflect-ᵐ b p pib df)
  polys-reflect-ᵐ b p pib (m-cata wf d) = m-cata wf (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᵐ b p pib (m-arr df) = m-arr (polys-reflect-ᵐ b p pib df)
  polys-reflect-ᵐ b p pib (m-const d) = m-const (polys-reflect-ᵍ b p d)
  polys-reflect-ᵐ b p pib (m-named ¬u lln imp) = m-named ¬u lln imp
  polys-reflect-ᵐ b p pib (m-named-resolved imp) = m-named-resolved imp

  polys-reflect-ᶜ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᶜ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i p s ⊢ᶜ e ∶ A ⨾ Ψ
  polys-reflect-ᶜ b p pib (t-morph-lift d) = t-morph-lift (polys-reflect-ᵐ b p pib d)
  polys-reflect-ᶜ b p pib (t-embed d) = t-embed (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᶜ b p pib (t-lam le d) = t-lam le (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᶜ b p pib (t-value-lift d) = t-value-lift (polys-reflect-ᵍ b p d)
  polys-reflect-ᶜ b p pib (t-pair-lit-check d₁ d₂) = t-pair-lit-check (polys-reflect-ᶜ b p pib d₁) (polys-reflect-ᶜ b p pib d₂)
  polys-reflect-ᶜ b p pib (t-In-app-check wf d) = t-In-app-check wf (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᶜ b p pib (t-apply-check d) = t-apply-check (polys-reflect-ᵢ b p pib d)
  polys-reflect-ᶜ b p pib (t-inl-app-check d) = t-inl-app-check (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᶜ b p pib (t-inr-app-check d) = t-inr-app-check (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᶜ b p pib (t-initial-app-check d) = t-initial-app-check (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᶜ b p pib (t-arr-app-check d) = t-arr-app-check (polys-reflect-ᶜ b p pib d)
  polys-reflect-ᶜ b p pib (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check cls (polys-reflect-ᵢ b p pib darg) (polys-reflect-ᶜ b p pib df)
  polys-reflect-ᶜ b {i = i} p pib (t-var-poly-instantiate {x = x} {T = T} {schema = schema} {body = bodyC} cb ¬u lln lin lpC dC)
    with lookupPoly p x in eqLP | lookupPoly-canon b p x
  ... | nothing | lc = ⊥-elim (n≢j (trans (sym lc) lpC))
  ... | just (schema′ , bodyP) | lc =
        t-var-poly-instantiate cb ¬u lln lin lp-rec d-rec
    where
      -- mapMaybe (canon-entry b) (just (schema′ , bodyP)) ≡ just (schema , bodyC)
      eqJ : (schema′ , canonExpr b [] [] bodyP) ≡ (schema , bodyC)
      eqJ = just-inj (trans (sym lc) lpC)
      lp-rec : lookupPoly p x ≡ just (schema , bodyP)
      lp-rec = subst (λ sc → lookupPoly p x ≡ just (sc , bodyP)) (cong proj₁ eqJ) eqLP
      -- transport dC : ctx[removePoly x (canonPolysCtx b p)] ⊢ᶜ bodyC  to  bodyP at ctx[removePoly x p]
      dC1 : ctxWithImportsAndPolys i (canonPolysCtx b (removePoly x p)) ⊢ᶜ bodyC ∶ T ⨾ zeroUsage
      dC1 = subst (λ q → ctxWithImportsAndPolys i q ⊢ᶜ bodyC ∶ T ⨾ zeroUsage)
                  (sym (removePoly-canon b x p)) dC
      dC2 : ctxWithImportsAndPolys i (canonPolysCtx b (removePoly x p)) ⊢ᶜ canonExpr b [] [] bodyP ∶ T ⨾ zeroUsage
      dC2 = subst (λ e → ctxWithImportsAndPolys i (canonPolysCtx b (removePoly x p)) ⊢ᶜ e ∶ T ⨾ zeroUsage)
                  (sym (cong proj₂ eqJ)) dC1
      d-rec : ctxWithImportsAndPolys i (removePoly x p) ⊢ᶜ bodyP ∶ T ⨾ zeroUsage
      d-rec = canon-reflects-ᶜ b bodyP (⊆ᵇ-nil {b})
                (polys-reflect-ᶜ b (removePoly x p) (removePoly-PInB {p} {b} x pib) dC2)
