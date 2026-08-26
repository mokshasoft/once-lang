-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_<_)
open import Induction.WellFounded using (Acc; acc)
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
  using (PolyCtx; NamedCtx; mkCtx; lookupPoly; removePoly; removePoly-decreases;
         lookupPolyPrefix; lookupPolyPrefix-decreases; ctxWithImportsAndPolys; composeMid)
open import Once.TypeCheck.Judgment
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPolyTransport
  using (canonPolysCtx; canon-entry; cpc; PInB; lookupPoly-canon; removePoly-canon;
         removePoly-PInB; composeArgB-polys-canon; domainOfHead-polys-canon;
         canon-prefix-entry; lookupPolyPrefix-canon; lookupPolyPrefix-PInB)
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
-- PLAN 0.73 F3 / D120's other half.
polys-reflect-ᵍ b p (g-neg-int n)      = g-neg-int n
polys-reflect-ᵍ b p (g-neg-float i f l q) = g-neg-float i f l q
polys-reflect-ᵍ b p (g-float i f l pos) = g-float i f l pos
polys-reflect-ᵍ b p (g-terminal lL lI) = g-terminal lL lI
polys-reflect-ᵍ b p (g-pair d₁ d₂)     = g-pair (polys-reflect-ᵍ b p d₁) (polys-reflect-ᵍ b p d₂)
polys-reflect-ᵍ b p (g-inl d)          = g-inl (polys-reflect-ᵍ b p d)
polys-reflect-ᵍ b p (g-inr d)          = g-inr (polys-reflect-ᵍ b p d)
polys-reflect-ᵍ b p (g-In wf d)        = g-In wf (polys-reflect-ᵍ b p d)

-- Formerly `{-# TERMINATING #-}`; now PROVEN by well-founded recursion on
-- `Acc _<_ (length p)` (the poly-context descent `removePoly-decreases` supplies),
-- the dual of `polys-transport-*`. Lexicographic (Acc, derivation): structural calls
-- keep `ac`, the one poly-shrink call passes `rec (removePoly-decreases …)`.
mutual
  polys-reflect-ᵢ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → Acc _<_ (length p) → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵢ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i p s ⊢ᵢ e ∶ A ⨾ Ψ
  polys-reflect-ᵢ b p pib ac (t-int n)  = t-int n
  polys-reflect-ᵢ b p pib ac (t-float i f l pos) = t-float i f l pos
  polys-reflect-ᵢ b p pib ac (t-str s)  = t-str s
  polys-reflect-ᵢ b p pib ac t-unit     = t-unit
  polys-reflect-ᵢ b p pib ac t-unit-var = t-unit-var
  polys-reflect-ᵢ b p pib ac (t-var-local ¬u lk) = t-var-local ¬u lk
  polys-reflect-ᵢ b p pib ac (t-var-qualified imp conc) = t-var-qualified imp conc
  polys-reflect-ᵢ b p pib ac (t-var-resolved imp conc) = t-var-resolved imp conc
  polys-reflect-ᵢ b p pib ac (t-var-import ¬u lkn imp conc) = t-var-import ¬u lkn imp conc
  -- Plan 0.58 / D071: infer-mode ground telescope reference — same reflect
  -- descent as the check-mode `t-var-poly-instantiate` case below (schema is
  -- canon-invariant, so the `isGround`/type-pin premises carry over).
  polys-reflect-ᵢ b {i = i} p pib (acc rec) (t-var-poly-instantiate-infer {x = x} {T = T} {schema = schema} {body = bodyC} {prefix = prefixC} cb ¬u lln lin lpC ig Teq dC)
    with lookupPolyPrefix p x in eqLP | lookupPolyPrefix-canon b p x
  ... | nothing | lc = ⊥-elim (n≢j (trans (sym lc) lpC))
  ... | just (schema′ , bodyP , prefixP) | lc =
        t-var-poly-instantiate-infer cb ¬u lln lin lp-rec ig Teq d-rec
    where
      eqJ : (schema′ , canonExpr b [] [] bodyP , canonPolysCtx b prefixP) ≡ (schema , bodyC , prefixC)
      eqJ = just-inj (trans (sym lc) lpC)
      lp-rec : lookupPolyPrefix p x ≡ just (schema , bodyP , prefixP)
      lp-rec = subst (λ sc → lookupPolyPrefix p x ≡ just (sc , bodyP , prefixP)) (cong proj₁ eqJ) eqLP
      dC1 : ctxWithImportsAndPolys i (canonPolysCtx b prefixP) ⊢ᶜ bodyC ∶ T ⨾ zeroUsage
      dC1 = subst (λ q → ctxWithImportsAndPolys i q ⊢ᶜ bodyC ∶ T ⨾ zeroUsage)
                  (sym (cong (λ r → proj₂ (proj₂ r)) eqJ)) dC
      dC2 : ctxWithImportsAndPolys i (canonPolysCtx b prefixP) ⊢ᶜ canonExpr b [] [] bodyP ∶ T ⨾ zeroUsage
      dC2 = subst (λ e → ctxWithImportsAndPolys i (canonPolysCtx b prefixP) ⊢ᶜ e ∶ T ⨾ zeroUsage)
                  (sym (cong (λ r → proj₁ (proj₂ r)) eqJ)) dC1
      d-rec : ctxWithImportsAndPolys i prefixP ⊢ᶜ bodyP ∶ T ⨾ zeroUsage
      d-rec = canon-reflects-ᶜ b bodyP (⊆ᵇ-nil {b})
                (polys-reflect-ᶜ b prefixP (lookupPolyPrefix-PInB {p} {b} x lp-rec pib)
                  (rec (lookupPolyPrefix-decreases x p lp-rec)) dC2)
  polys-reflect-ᵢ b p pib ac (t-annot d) = t-annot (polys-reflect-ᶜ b p pib ac d)
  polys-reflect-ᵢ b p pib ac (t-pair d₁ d₂) = t-pair (polys-reflect-ᵢ b p pib ac d₁) (polys-reflect-ᵢ b p pib ac d₂)
  polys-reflect-ᵢ b p pib ac (t-neg d) = t-neg (polys-reflect-ᵢ b p pib ac d)
  -- PLAN 0.73 F3: a leaf, like `t-float` — no premise to reflect.
  polys-reflect-ᵢ b p pib ac (t-neg-float i f l q) = t-neg-float i f l q
  polys-reflect-ᵢ b p pib ac (t-let d₁ d₂) = t-let (polys-reflect-ᵢ b p pib ac d₁) (polys-reflect-ᵢ b p pib ac d₂)
  polys-reflect-ᵢ b p pib ac (t-case ds dL dR) =
    t-case (polys-reflect-ᵢ b p pib ac ds) (polys-reflect-ᵢ b p pib ac dL) (polys-reflect-ᵢ b p pib ac dR)
  polys-reflect-ᵢ b p pib ac (t-binop-arith pr d₁ d₂) = t-binop-arith pr (polys-reflect-ᵢ b p pib ac d₁) (polys-reflect-ᵢ b p pib ac d₂)
  polys-reflect-ᵢ b p pib ac (t-binop-cmp pr d₁ d₂) = t-binop-cmp pr (polys-reflect-ᵢ b p pib ac d₁) (polys-reflect-ᵢ b p pib ac d₂)
  polys-reflect-ᵢ b p pib ac (t-id-app d) = t-id-app (polys-reflect-ᵢ b p pib ac d)
  polys-reflect-ᵢ b p pib ac (t-fst-app d) = t-fst-app (polys-reflect-ᵢ b p pib ac d)
  polys-reflect-ᵢ b p pib ac (t-snd-app d) = t-snd-app (polys-reflect-ᵢ b p pib ac d)
  polys-reflect-ᵢ b p pib ac (t-terminal-app d) = t-terminal-app (polys-reflect-ᵢ b p pib ac d)
  polys-reflect-ᵢ b p pib ac (t-apply-app-infer d) = t-apply-app-infer (polys-reflect-ᵢ b p pib ac d)
  polys-reflect-ᵢ b p pib ac (t-app cls df dx) = t-app cls (polys-reflect-ᵢ b p pib ac df) (polys-reflect-ᶜ b p pib ac dx)
  polys-reflect-ᵢ b p pib ac (t-effApp cls df dx) = t-effApp cls (polys-reflect-ᵢ b p pib ac df) (polys-reflect-ᶜ b p pib ac dx)

  polys-reflect-ᵐ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → Acc _<_ (length p) → ∀ {e A π B}
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵐ e ∶ A ⇨[ π ] B
    → mkCtx n Γ Δ f i p s ⊢ᵐ e ∶ A ⇨[ π ] B
  polys-reflect-ᵐ b p pib ac (m-id ll li) = m-id ll li
  polys-reflect-ᵐ b p pib ac (m-fst ll li) = m-fst ll li
  polys-reflect-ᵐ b p pib ac (m-snd ll li) = m-snd ll li
  polys-reflect-ᵐ b p pib ac (m-terminal ll li) = m-terminal ll li
  polys-reflect-ᵐ b p pib ac (m-initial ll li) = m-initial ll li
  polys-reflect-ᵐ b p pib ac (m-inl ll li) = m-inl ll li
  polys-reflect-ᵐ b p pib ac (m-inr ll li) = m-inr ll li
  polys-reflect-ᵐ b {n = n} {Γ = Γ} {Δ = Δ} {f = fr} {i = i} {s = s} p pib ac (m-compose cm df dg) =
    m-compose (composeMid-polys-decanon b (mkCtx n Γ Δ fr i p s)
                (polys-reflect-ᵐ b p pib ac df) (polys-reflect-ᵐ b p pib ac dg) cm)
              (polys-reflect-ᵐ b p pib ac df) (polys-reflect-ᵐ b p pib ac dg)
  polys-reflect-ᵐ b p pib ac (m-case df dg) = m-case (polys-reflect-ᵐ b p pib ac df) (polys-reflect-ᵐ b p pib ac dg)
  polys-reflect-ᵐ b p pib ac (m-pair df dg) = m-pair (polys-reflect-ᵐ b p pib ac df) (polys-reflect-ᵐ b p pib ac dg)
  polys-reflect-ᵐ b p pib ac (m-curry df) = m-curry (polys-reflect-ᵐ b p pib ac df)
  polys-reflect-ᵐ b p pib ac (m-cata wf d) = m-cata wf (polys-reflect-ᵐ b p pib ac d)
  polys-reflect-ᵐ b p pib ac (m-const d) = m-const (polys-reflect-ᵍ b p d)
  polys-reflect-ᵐ b p pib ac (m-named ¬u lln imp bA cB) = m-named ¬u lln imp bA cB
  polys-reflect-ᵐ b p pib ac (m-named-resolved imp bA cB) = m-named-resolved imp bA cB

  polys-reflect-ᶜ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → Acc _<_ (length p) → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᶜ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i p s ⊢ᶜ e ∶ A ⨾ Ψ
  polys-reflect-ᶜ b p pib ac (t-morph-lift d) = t-morph-lift (polys-reflect-ᵐ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-embed d) = t-embed (polys-reflect-ᵢ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-subsume d) = t-subsume (polys-reflect-ᶜ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-lam le d) = t-lam le (polys-reflect-ᶜ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-value-lift d) = t-value-lift (polys-reflect-ᵍ b p d)
  polys-reflect-ᶜ b p pib ac (t-pair-lit-check d₁ d₂) = t-pair-lit-check (polys-reflect-ᶜ b p pib ac d₁) (polys-reflect-ᶜ b p pib ac d₂)
  polys-reflect-ᶜ b p pib ac (t-In-app-check wf d) = t-In-app-check wf (polys-reflect-ᶜ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-apply-check d) = t-apply-check (polys-reflect-ᵢ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-inl-app-check d) = t-inl-app-check (polys-reflect-ᶜ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-inr-app-check d) = t-inr-app-check (polys-reflect-ᶜ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-initial-app-check d) = t-initial-app-check (polys-reflect-ᶜ b p pib ac d)
  polys-reflect-ᶜ b p pib ac (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check cls (polys-reflect-ᵢ b p pib ac darg) (polys-reflect-ᶜ b p pib ac df)
  polys-reflect-ᶜ b {i = i} p pib (acc rec) (t-var-poly-instantiate {x = x} {T = T} {schema = schema} {body = bodyC} {prefix = prefixC} cb ¬u lln lin lpC ig dC)
    with lookupPolyPrefix p x in eqLP | lookupPolyPrefix-canon b p x
  ... | nothing | lc = ⊥-elim (n≢j (trans (sym lc) lpC))
  ... | just (schema′ , bodyP , prefixP) | lc =
        t-var-poly-instantiate cb ¬u lln lin lp-rec ig d-rec
    where
      -- mapMaybe (canon-prefix-entry b) (just (schema′,bodyP,prefixP))
      --   ≡ just (schema , bodyC , prefixC)
      eqJ : (schema′ , canonExpr b [] [] bodyP , canonPolysCtx b prefixP) ≡ (schema , bodyC , prefixC)
      eqJ = just-inj (trans (sym lc) lpC)
      lp-rec : lookupPolyPrefix p x ≡ just (schema , bodyP , prefixP)
      lp-rec = subst (λ sc → lookupPolyPrefix p x ≡ just (sc , bodyP , prefixP)) (cong proj₁ eqJ) eqLP
      -- reflect dC : ctx[prefixC] ⊢ᶜ bodyC  to  bodyP at ctx[prefixP].
      -- prefixC ≡ canon prefixP and bodyC ≡ canon bodyP (both from eqJ).
      dC1 : ctxWithImportsAndPolys i (canonPolysCtx b prefixP) ⊢ᶜ bodyC ∶ T ⨾ zeroUsage
      dC1 = subst (λ q → ctxWithImportsAndPolys i q ⊢ᶜ bodyC ∶ T ⨾ zeroUsage)
                  (sym (cong (λ r → proj₂ (proj₂ r)) eqJ)) dC
      dC2 : ctxWithImportsAndPolys i (canonPolysCtx b prefixP) ⊢ᶜ canonExpr b [] [] bodyP ∶ T ⨾ zeroUsage
      dC2 = subst (λ e → ctxWithImportsAndPolys i (canonPolysCtx b prefixP) ⊢ᶜ e ∶ T ⨾ zeroUsage)
                  (sym (cong (λ r → proj₁ (proj₂ r)) eqJ)) dC1
      d-rec : ctxWithImportsAndPolys i prefixP ⊢ᶜ bodyP ∶ T ⨾ zeroUsage
      d-rec = canon-reflects-ᶜ b bodyP (⊆ᵇ-nil {b})
                (polys-reflect-ᶜ b prefixP (lookupPolyPrefix-PInB {p} {b} x lp-rec pib)
                  (rec (lookupPolyPrefix-decreases x p lp-rec)) dC2)
