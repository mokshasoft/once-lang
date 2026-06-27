-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonPolyTransport — the POLY-CONTEXT transport (Plan 0.51).
--
-- `canonModule` canonicalizes poly-DEF bodies too, so `ModuleTyped mR` lives at
-- the canonExpr'd poly context `canonPolysCtx b p`, not `p`. This module:
--   * foundational commutes (`lookupPoly-canon`, `removePoly-canon`),
--   * `polys-transport-{ᵢ,ᵐ,ᶜ}`: a `⊢ᶜ` derivation at a poly context `p` lifts to
--     the canonExpr'd context `canonPolysCtx b p` (the expression is UNCHANGED;
--     only the t-var-poly-instantiate body and the m-cata sub-context read polys,
--     and they re-derive via `canon-pres-ᶜ` + recursion).
------------------------------------------------------------------------

module Once.Adequacy.CanonPolyTransport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties as StrProp using ()
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type; PolyType)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr; elemStr)
open import Once.TypeCheck.Classify using (PolyCtx; lookupPoly; removePoly)

------------------------------------------------------------------------
-- canonExpr a poly context's bodies.
------------------------------------------------------------------------

canonPolysCtx : List String → PolyCtx → PolyCtx
canonPolysCtx b [] = []
canonPolysCtx b ((n , s , body) ∷ rest) = (n , s , canonExpr b [] [] body) ∷ canonPolysCtx b rest

canon-entry : List String → (PolyType × RawExpr) → (PolyType × RawExpr)
canon-entry b (s , body) = (s , canonExpr b [] [] body)

------------------------------------------------------------------------
-- lookupPoly / removePoly commute with canonPolysCtx.
------------------------------------------------------------------------

lookupPoly-canon : ∀ (b : List String) (p : PolyCtx) (x : String)
  → lookupPoly (canonPolysCtx b p) x ≡ mapMaybe (canon-entry b) (lookupPoly p x)
lookupPoly-canon b [] x = refl
lookupPoly-canon b ((n , s , body) ∷ rest) x with StrProp._≟_ n x
... | yes _ = refl
... | no  _ = lookupPoly-canon b rest x

removePoly-canon : ∀ (b : List String) (x : String) (p : PolyCtx)
  → canonPolysCtx b (removePoly x p) ≡ removePoly x (canonPolysCtx b p)
removePoly-canon b x [] = refl
removePoly-canon b x ((n , s , body) ∷ rest) with StrProp._≟_ n x
... | yes _ = refl
... | no  _ = cong ((n , s , canonExpr b [] [] body) ∷_) (removePoly-canon b x rest)

------------------------------------------------------------------------
-- A poly name found in `p` is found in `canonPolysCtx b p` (names preserved).
------------------------------------------------------------------------

lookupPoly-canon-just : ∀ (b : List String) (p : PolyCtx) (x : String) {s body}
  → lookupPoly p x ≡ just (s , body)
  → lookupPoly (canonPolysCtx b p) x ≡ just (s , canonExpr b [] [] body)
lookupPoly-canon-just b p x {s} {body} lp
  rewrite lookupPoly-canon b p x rewrite lp = refl

------------------------------------------------------------------------
-- PInB + removePoly preserves it.
------------------------------------------------------------------------

open import Data.Product using (Σ-syntax)

PInB : PolyCtx → List String → Set
PInB p b = ∀ {x s body} → lookupPoly p x ≡ just (s , body) → elemStr x b ≡ true

lookupPoly-removePoly-mono : ∀ (x y : String) (p : PolyCtx) {r}
  → lookupPoly (removePoly x p) y ≡ just r → Σ-syntax _ (λ r' → lookupPoly p y ≡ just r')
lookupPoly-removePoly-mono x y [] ()
lookupPoly-removePoly-mono x y ((n , s , b) ∷ rest) lp with StrProp._≟_ n x
... | yes _ with StrProp._≟_ n y
...   | yes _ = _ , refl
...   | no  _ = _ , lp
lookupPoly-removePoly-mono x y ((n , s , b) ∷ rest) lp | no _ with StrProp._≟_ n y
...   | yes _ = _ , refl
...   | no  _ = lookupPoly-removePoly-mono x y rest lp

removePoly-PInB : ∀ {p b} (x : String) → PInB p b → PInB (removePoly x p) b
removePoly-PInB {p} x pib {y} lp with lookupPoly-removePoly-mono x y p lp
... | _ , lp' = pib lp'

------------------------------------------------------------------------
-- The transport itself.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst)
open import Once.Surface.Syntax using (zeroUsage)
open import Once.TypeCheck.Classify using (NamedCtx; mkCtx; ctxWithImportsAndPolys; composeMid)
open import Once.TypeCheck.Judgment
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPreserveMutual using (canon-pres-ᶜ; mkPIB)

postulate
  -- m-compose's premise: `composeMid` reads `lookupPoly`'s SCHEMA (not body), which
  -- `canonPolysCtx` preserves, so composeMid is invariant. (To discharge: case the
  -- ⊢ᵐ arms like CanonComposeMid.)
  composeMid-polys-canon :
    ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) {fa g A B}
    → composeMid (mkCtx n Γ Δ f i p s) fa g A ≡ just B
    → composeMid (mkCtx n Γ Δ f i (canonPolysCtx b p) s) fa g A ≡ just B

-- ⊢ᵍ is polys-INDEPENDENT (g-rules read only lookupLocal/lookupImport), so its
-- derivations transport by re-applying each rule (premises transfer verbatim).
polys-transport-ᵍ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) {e A}
  → mkCtx n Γ Δ f i p s ⊢ᵍ e ∶ A
  → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵍ e ∶ A
polys-transport-ᵍ b p (g-int n)          = g-int n
polys-transport-ᵍ b p (g-terminal lL lI) = g-terminal lL lI
polys-transport-ᵍ b p (g-pair d₁ d₂)     = g-pair (polys-transport-ᵍ b p d₁) (polys-transport-ᵍ b p d₂)
polys-transport-ᵍ b p (g-inl d)          = g-inl (polys-transport-ᵍ b p d)
polys-transport-ᵍ b p (g-inr d)          = g-inr (polys-transport-ᵍ b p d)
polys-transport-ᵍ b p (g-In wf d)        = g-In wf (polys-transport-ᵍ b p d)

-- The `t-var-poly-instantiate` case recurses on `canon-pres-ᶜ d` (the inlined poly
-- body) at `removePoly x p` — genuinely WELL-FOUNDED (the poly context strictly
-- shrinks each level, mirroring the elaborator's own cycle-guarded poly recursion)
-- but not structural, so termination is asserted.
{-# TERMINATING #-}
mutual
  polys-transport-ᵢ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i p s ⊢ᵢ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵢ e ∶ A ⨾ Ψ
  polys-transport-ᵢ b p pib (t-int n)  = t-int n
  polys-transport-ᵢ b p pib (t-str s)  = t-str s
  polys-transport-ᵢ b p pib t-unit     = t-unit
  polys-transport-ᵢ b p pib t-unit-var = t-unit-var
  polys-transport-ᵢ b p pib (t-var-local ¬u lk) = t-var-local ¬u lk
  polys-transport-ᵢ b p pib (t-var-qualified imp) = t-var-qualified imp
  polys-transport-ᵢ b p pib (t-var-resolved imp) = t-var-resolved imp
  polys-transport-ᵢ b p pib (t-var-import ¬u lkn imp) = t-var-import ¬u lkn imp
  polys-transport-ᵢ b p pib (t-annot d) = t-annot (polys-transport-ᶜ b p pib d)
  polys-transport-ᵢ b p pib (t-pair d₁ d₂) = t-pair (polys-transport-ᵢ b p pib d₁) (polys-transport-ᵢ b p pib d₂)
  polys-transport-ᵢ b p pib (t-neg d) = t-neg (polys-transport-ᵢ b p pib d)
  polys-transport-ᵢ b p pib (t-let d₁ d₂) = t-let (polys-transport-ᵢ b p pib d₁) (polys-transport-ᵢ b p pib d₂)
  polys-transport-ᵢ b p pib (t-case ds dL dR) =
    t-case (polys-transport-ᵢ b p pib ds) (polys-transport-ᵢ b p pib dL) (polys-transport-ᵢ b p pib dR)
  polys-transport-ᵢ b p pib (t-binop-arith pr d₁ d₂) = t-binop-arith pr (polys-transport-ᵢ b p pib d₁) (polys-transport-ᵢ b p pib d₂)
  polys-transport-ᵢ b p pib (t-binop-cmp pr d₁ d₂) = t-binop-cmp pr (polys-transport-ᵢ b p pib d₁) (polys-transport-ᵢ b p pib d₂)
  polys-transport-ᵢ b p pib (t-id-app d) = t-id-app (polys-transport-ᵢ b p pib d)
  polys-transport-ᵢ b p pib (t-fst-app d) = t-fst-app (polys-transport-ᵢ b p pib d)
  polys-transport-ᵢ b p pib (t-snd-app d) = t-snd-app (polys-transport-ᵢ b p pib d)
  polys-transport-ᵢ b p pib (t-terminal-app d) = t-terminal-app (polys-transport-ᵢ b p pib d)
  polys-transport-ᵢ b p pib (t-arr-app-infer d) = t-arr-app-infer (polys-transport-ᵢ b p pib d)
  polys-transport-ᵢ b p pib (t-apply-app-infer d) = t-apply-app-infer (polys-transport-ᵢ b p pib d)
  polys-transport-ᵢ b p pib (t-app cls df dx) = t-app cls (polys-transport-ᵢ b p pib df) (polys-transport-ᶜ b p pib dx)
  polys-transport-ᵢ b p pib (t-effApp cls df dx) = t-effApp cls (polys-transport-ᵢ b p pib df) (polys-transport-ᶜ b p pib dx)

  polys-transport-ᵐ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → ∀ {e A π B}
    → mkCtx n Γ Δ f i p s ⊢ᵐ e ∶ A ⇨[ π ] B
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵐ e ∶ A ⇨[ π ] B
  polys-transport-ᵐ b p pib (m-id ll li) = m-id ll li
  polys-transport-ᵐ b p pib (m-fst ll li) = m-fst ll li
  polys-transport-ᵐ b p pib (m-snd ll li) = m-snd ll li
  polys-transport-ᵐ b p pib (m-terminal ll li) = m-terminal ll li
  polys-transport-ᵐ b p pib (m-initial ll li) = m-initial ll li
  polys-transport-ᵐ b p pib (m-inl ll li) = m-inl ll li
  polys-transport-ᵐ b p pib (m-inr ll li) = m-inr ll li
  polys-transport-ᵐ b {n = n} {Γ = Γ} {Δ = Δ} {f = fr} {i = i} {s = s} p pib
    (m-compose {f = f} {g = g} {A = A} {B = B} cm df dg) =
    m-compose (composeMid-polys-canon b {n} {Γ} {Δ} {fr} {i} {s} p {f} {g} {A} {B} cm)
              (polys-transport-ᵐ b p pib df) (polys-transport-ᵐ b p pib dg)
  polys-transport-ᵐ b p pib (m-case df dg) = m-case (polys-transport-ᵐ b p pib df) (polys-transport-ᵐ b p pib dg)
  polys-transport-ᵐ b p pib (m-pair df dg) = m-pair (polys-transport-ᵐ b p pib df) (polys-transport-ᵐ b p pib dg)
  polys-transport-ᵐ b p pib (m-curry df) = m-curry (polys-transport-ᵐ b p pib df)
  polys-transport-ᵐ b p pib (m-cata wf d) = m-cata wf (polys-transport-ᶜ b p pib d)
  polys-transport-ᵐ b p pib (m-arr df) = m-arr (polys-transport-ᵐ b p pib df)
  polys-transport-ᵐ b p pib (m-const d) = m-const (polys-transport-ᵍ b p d)
  polys-transport-ᵐ b p pib (m-named ¬u lln imp) = m-named ¬u lln imp
  polys-transport-ᵐ b p pib (m-named-resolved imp) = m-named-resolved imp

  polys-transport-ᶜ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i p s ⊢ᶜ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᶜ e ∶ A ⨾ Ψ
  polys-transport-ᶜ b p pib (t-morph-lift d) = t-morph-lift (polys-transport-ᵐ b p pib d)
  polys-transport-ᶜ b p pib (t-embed d) = t-embed (polys-transport-ᵢ b p pib d)
  polys-transport-ᶜ b p pib (t-lam le d) = t-lam le (polys-transport-ᶜ b p pib d)
  polys-transport-ᶜ b p pib (t-value-lift d) = t-value-lift (polys-transport-ᵍ b p d)
  polys-transport-ᶜ b p pib (t-pair-lit-check d₁ d₂) = t-pair-lit-check (polys-transport-ᶜ b p pib d₁) (polys-transport-ᶜ b p pib d₂)
  polys-transport-ᶜ b p pib (t-In-app-check wf d) = t-In-app-check wf (polys-transport-ᶜ b p pib d)
  polys-transport-ᶜ b p pib (t-apply-check d) = t-apply-check (polys-transport-ᵢ b p pib d)
  polys-transport-ᶜ b p pib (t-inl-app-check d) = t-inl-app-check (polys-transport-ᶜ b p pib d)
  polys-transport-ᶜ b p pib (t-inr-app-check d) = t-inr-app-check (polys-transport-ᶜ b p pib d)
  polys-transport-ᶜ b p pib (t-initial-app-check d) = t-initial-app-check (polys-transport-ᶜ b p pib d)
  polys-transport-ᶜ b p pib (t-arr-app-check d) = t-arr-app-check (polys-transport-ᶜ b p pib d)
  polys-transport-ᶜ b p pib (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check cls (polys-transport-ᵢ b p pib darg) (polys-transport-ᶜ b p pib df)
  polys-transport-ᶜ b {i = i} p pib (t-var-poly-instantiate {x = x} {T = T} {body = body} cb ¬u lln lin lp d) =
    t-var-poly-instantiate cb ¬u lln lin (lookupPoly-canon-just b p x lp)
      (subst (λ q → ctxWithImportsAndPolys i q ⊢ᶜ canonExpr b [] [] body ∶ T ⨾ zeroUsage)
             (removePoly-canon b x p)
             (polys-transport-ᶜ b (removePoly x p) (removePoly-PInB {p} {b} x pib)
                (canon-pres-ᶜ {ctx = ctxWithImportsAndPolys i (removePoly x p)} b
                  (⊆ᵇ-nil {b}) (mkPIB (removePoly-PInB {p} {b} x pib)) d)))
