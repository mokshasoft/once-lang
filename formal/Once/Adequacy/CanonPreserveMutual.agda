-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonPreserveMutual — Plan 0.51 Step 2 (mutual preservation).
-- The resolver's own-module canonicalization `canonExpr bound [] []` (RVar x →
-- RResolved (canonical [x]) for a FREE, non-builtin, non-bound, non-poly x)
-- PRESERVES the three mutual declarative judgments `⊢ᵢ` / `⊢ᵐ` / `⊢ᶜ`, given:
--   * `Names⊆ ctx bound` — the context's locals are all in `bound`, AND
--   * `PolyInB ctx bound` — every own-module poly-def name is in `bound`
--     (true by construction: `canonDecl` seeds `bound := polyDefNames ds`, the
--     SAME source the `polys` context is built from — see Resolve.polyDefNames).
-- `⊢ᵍ` preservation (`pres-ᵍ`) is in `Once.Adequacy.CanonPreserve` (independent).
--
-- Single deferred hole: `composeMid-canon`, the `m-compose` middle-type premise
-- transfer — TRUE but provable only by casing the `⊢ᵐ` sub-derivations (the
-- `domainOfHead`/`composeArgB` literal patterns are stuck for an abstract head).
------------------------------------------------------------------------

module Once.Adequacy.CanonPreserveMutual where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr; isBuiltinName; elemStr; cls-canon)
open import Once.TypeCheck.Classify
  using (NamedCtx; composeMid; lookupPoly; lookupPolyPrefix⇒lookupPoly; extendNamedCtx; ctxWithImportsAndPolys)
open import Once.TypeCheck.Context using (names)
open import Once.TypeCheck.Judgment
open import Once.Adequacy.CanonPreserve

------------------------------------------------------------------------
-- Hypotheses + the small lemmas the binder/poly cases need.
------------------------------------------------------------------------

Names⊆ : NamedCtx → List String → Set
Names⊆ ctx bound = names (NamedCtx.named ctx) ⊆ᵇ bound

-- A RECORD (not a defined function-type) so the type former stays rigid: the
-- binder cases must infer `poly-ext`'s ctx/bound by unifying `PolyInB …` types,
-- which only works if `PolyInB` is injective (a function-type would unfold and
-- get stuck on the non-invertible `NamedCtx.polys` projection).
record PolyInB (ctx : NamedCtx) (bound : List String) : Set where
  constructor mkPIB
  field app : ∀ {x s b} → lookupPoly (NamedCtx.polys ctx) x ≡ just (s , b) → elemStr x bound ≡ true
open PolyInB

or-l : ∀ {a b : Bool} → a ≡ true → (a ∨ b) ≡ true
or-l refl = refl

⊆ᵇ-weaken : ∀ {bound} (x : String) → bound ⊆ᵇ (x ∷ bound)
⊆ᵇ-weaken x y h with y ≟s x
... | yes _ = refl
... | no  _ = h

-- Extend the two hypotheses across a binder `x` (locals/polys both grow under
-- `x ∷ bound`; `polys` is unchanged by `extendNamedCtx`, so `PolyInB` only weakens).
poly-ext : ∀ {ctx bound} (x : String) (A : Type)
         → PolyInB ctx bound → PolyInB (extendNamedCtx ctx x A) (x ∷ bound)
poly-ext x A pib = mkPIB (λ {x'} h → ⊆ᵇ-weaken x x' (app pib {x'} h))

------------------------------------------------------------------------
-- `composeMid` is invariant under canonExpr on the compose ARMS — DISCHARGED in
-- `Once.Adequacy.CanonComposeMid` by casing the `⊢ᵐ` derivations (one residual
-- there: `composeArgB-RVar-resolved`, an Agda literal-pattern limitation).
------------------------------------------------------------------------

open import Once.Adequacy.CanonComposeMid using (composeMid-canon)

------------------------------------------------------------------------
-- Mutual preservation.
------------------------------------------------------------------------

mutual

  canon-pres-ᵢ : ∀ {ctx e A Ψ} (bound : List String)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ canonExpr bound [] [] e ∶ A ⨾ Ψ
  canon-pres-ᵢ bound sub pib (t-int n) = t-int n
  canon-pres-ᵢ bound sub pib (t-float i f l p) = t-float i f l p
  canon-pres-ᵢ bound sub pib (t-str s) = t-str s
  canon-pres-ᵢ bound sub pib t-unit = t-unit
  canon-pres-ᵢ bound sub pib t-unit-var
    rewrite canon-builtin bound "unit" refl = t-unit-var
  canon-pres-ᵢ {ctx} bound sub pib (t-var-local {x = x} ¬u lk)
    rewrite canon-RVar-keep bound x (or-l (sub x (lookup-just→elem ctx x lk))) =
      t-var-local ¬u lk
  canon-pres-ᵢ bound sub pib (t-var-qualified imp conc) = t-var-qualified imp conc
  canon-pres-ᵢ bound sub pib (t-var-resolved imp conc) = t-var-resolved imp conc
  canon-pres-ᵢ bound sub pib (t-var-import {x = x} ¬u lkn imp conc)
    with elemStr x bound ∨ isBuiltinName x in eb
  ... | true  rewrite canon-RVar-keep    bound x eb = t-var-import ¬u lkn imp conc
  ... | false rewrite canon-RVar-resolve bound x eb = t-var-resolved imp conc
  -- Plan 0.58 / D071: infer-mode ground telescope reference — same keep-bare
  -- rewrite as the check-mode `t-var-poly-instantiate` case (a telescope name
  -- is in `bound`, so canonExpr keeps the bare RVar; premises are ctx-side).
  canon-pres-ᵢ {ctx = ctx} bound sub pib (t-var-poly-instantiate-infer {x = x} cb ¬u lln lin lp ig Teq d)
    rewrite canon-RVar-keep bound x (or-l (app pib (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x lp))) =
      t-var-poly-instantiate-infer cb ¬u lln lin lp ig Teq d
  canon-pres-ᵢ bound sub pib (t-annot d) = t-annot (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-pair d₁ d₂) =
    t-pair (canon-pres-ᵢ bound sub pib d₁) (canon-pres-ᵢ bound sub pib d₂)
  canon-pres-ᵢ bound sub pib (t-neg d) = t-neg (canon-pres-ᵢ bound sub pib d)
  -- PLAN 0.73 F3. A LEAF here, like `t-float`: the resolver rewrites NAMES,
  -- and `- 3.14` contains none, so `canonExpr` is the identity on it and the
  -- derivation transports unchanged.
  canon-pres-ᵢ bound sub pib (t-neg-float i f l p) = t-neg-float i f l p
  canon-pres-ᵢ bound sub pib (t-let {x = x} {A = A} d₁ d₂) =
    t-let (canon-pres-ᵢ bound sub pib d₁)
          (canon-pres-ᵢ (x ∷ bound) (⊆ᵇ-cons x sub) (poly-ext x A pib) d₂)
  canon-pres-ᵢ bound sub pib (t-case {xL = xL} {xR = xR} {A = A} {B = B} ds dL dR) =
    t-case (canon-pres-ᵢ bound sub pib ds)
           (canon-pres-ᵢ (xL ∷ bound) (⊆ᵇ-cons xL sub) (poly-ext xL A pib) dL)
           (canon-pres-ᵢ (xR ∷ bound) (⊆ᵇ-cons xR sub) (poly-ext xR B pib) dR)
  canon-pres-ᵢ bound sub pib (t-binop-arith p d₁ d₂) =
    t-binop-arith p (canon-pres-ᵢ bound sub pib d₁) (canon-pres-ᵢ bound sub pib d₂)
  -- PLAN 0.75 F4: structural, exactly as its integer twin above.
  canon-pres-ᵢ bound sub pib (t-binop-arith-float p d₁ d₂) =
    t-binop-arith-float p (canon-pres-ᵢ bound sub pib d₁) (canon-pres-ᵢ bound sub pib d₂)
  -- D125: the mixed forms, structurally identical again.
  canon-pres-ᵢ bound sub pib (t-binop-arith-float-il p d₁ d₂) =
    t-binop-arith-float-il p (canon-pres-ᵢ bound sub pib d₁) (canon-pres-ᵢ bound sub pib d₂)
  canon-pres-ᵢ bound sub pib (t-binop-arith-float-ir p d₁ d₂) =
    t-binop-arith-float-ir p (canon-pres-ᵢ bound sub pib d₁) (canon-pres-ᵢ bound sub pib d₂)
  canon-pres-ᵢ bound sub pib (t-binop-cmp p d₁ d₂) =
    t-binop-cmp p (canon-pres-ᵢ bound sub pib d₁) (canon-pres-ᵢ bound sub pib d₂)
  canon-pres-ᵢ bound sub pib (t-id-app d)
    rewrite canon-builtin bound "id" refl = t-id-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-fst-app d)
    rewrite canon-builtin bound "fst" refl = t-fst-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-snd-app d)
    rewrite canon-builtin bound "snd" refl = t-snd-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-terminal-app d)
    rewrite canon-builtin bound "terminal" refl = t-terminal-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-apply-app-infer d)
    rewrite canon-builtin bound "apply" refl = t-apply-app-infer (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-app {f = f} cls df dx) =
    t-app (classify-canon bound f cls)
          (canon-pres-ᵢ bound sub pib df) (canon-pres-ᶜ bound sub pib dx)
  canon-pres-ᵢ bound sub pib (t-effApp {f = f} cls df dx) =
    t-effApp (classify-canon bound f cls)
             (canon-pres-ᵢ bound sub pib df) (canon-pres-ᶜ bound sub pib dx)

  canon-pres-ᵐ : ∀ {ctx e A π B} (bound : List String)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᵐ e ∶ A ⇨[ π ] B → ctx ⊢ᵐ canonExpr bound [] [] e ∶ A ⇨[ π ] B
  canon-pres-ᵐ bound sub pib (m-id ll li)
    rewrite canon-builtin bound "id" refl = m-id ll li
  canon-pres-ᵐ bound sub pib (m-fst ll li)
    rewrite canon-builtin bound "fst" refl = m-fst ll li
  canon-pres-ᵐ bound sub pib (m-snd ll li)
    rewrite canon-builtin bound "snd" refl = m-snd ll li
  canon-pres-ᵐ bound sub pib (m-terminal ll li)
    rewrite canon-builtin bound "terminal" refl = m-terminal ll li
  canon-pres-ᵐ bound sub pib (m-initial ll li)
    rewrite canon-builtin bound "initial" refl = m-initial ll li
  canon-pres-ᵐ bound sub pib (m-inl ll li)
    rewrite canon-builtin bound "inl" refl = m-inl ll li
  canon-pres-ᵐ bound sub pib (m-inr ll li)
    rewrite canon-builtin bound "inr" refl = m-inr ll li
  canon-pres-ᵐ bound sub pib (m-compose {f = f} {g = g} cm df dg)
    rewrite canon-builtin bound "compose" refl =
      m-compose (composeMid-canon bound df dg cm)
                (canon-pres-ᵐ bound sub pib df) (canon-pres-ᵐ bound sub pib dg)
  canon-pres-ᵐ bound sub pib (m-case df dg)
    rewrite canon-builtin bound "case" refl =
      m-case (canon-pres-ᵐ bound sub pib df) (canon-pres-ᵐ bound sub pib dg)
  canon-pres-ᵐ bound sub pib (m-pair df dg)
    rewrite canon-builtin bound "pair" refl =
      m-pair (canon-pres-ᵐ bound sub pib df) (canon-pres-ᵐ bound sub pib dg)
  canon-pres-ᵐ bound sub pib (m-curry df)
    rewrite canon-builtin bound "curry" refl = m-curry (canon-pres-ᵐ bound sub pib df)
  canon-pres-ᵐ bound sub pib (m-cata wf d)
    rewrite canon-builtin bound "cata" refl =
      m-cata wf (canon-pres-ᵐ bound (⊆ᵇ-nil {bound}) (mkPIB (λ {x'} h → app pib {x'} h)) d)
  canon-pres-ᵐ bound sub pib (m-const d) = m-const (pres-ᵍ bound d)
  canon-pres-ᵐ bound sub pib (m-named {x = x} ¬u lln imp bA cB)
    with elemStr x bound ∨ isBuiltinName x in eb
  ... | true  rewrite canon-RVar-keep    bound x eb = m-named ¬u lln imp bA cB
  ... | false rewrite canon-RVar-resolve bound x eb = m-named-resolved imp bA cB
  canon-pres-ᵐ bound sub pib (m-named-resolved imp bA cB) = m-named-resolved imp bA cB

  canon-pres-ᶜ : ∀ {ctx e A Ψ} (bound : List String)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ canonExpr bound [] [] e ∶ A ⨾ Ψ
  canon-pres-ᶜ bound sub pib (t-morph-lift d) = t-morph-lift (canon-pres-ᵐ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-embed d) = t-embed (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-subsume d) = t-subsume (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-lam {x = x} {A = A} le d) =
    t-lam le (canon-pres-ᶜ (x ∷ bound) (⊆ᵇ-cons x sub) (poly-ext x A pib) d)
  canon-pres-ᶜ bound sub pib (t-value-lift d) = t-value-lift (pres-ᵍ bound d)
  -- D126: structural, on the INFER sub-derivation rather than a `⊢ᵍ` one.
  canon-pres-ᶜ bound sub pib (t-closed-lift cls d) =
    t-closed-lift (cls-canon bound [] [] cls) (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-pair-lit-check d₁ d₂) =
    t-pair-lit-check (canon-pres-ᶜ bound sub pib d₁) (canon-pres-ᶜ bound sub pib d₂)
  canon-pres-ᶜ bound sub pib (t-In-app-check wf d)
    rewrite canon-builtin bound "In" refl = t-In-app-check wf (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-apply-check d)
    rewrite canon-builtin bound "apply" refl = t-apply-check (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-inl-app-check d)
    rewrite canon-builtin bound "inl" refl = t-inl-app-check (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-inr-app-check d)
    rewrite canon-builtin bound "inr" refl = t-inr-app-check (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-initial-app-check d)
    rewrite canon-builtin bound "initial" refl = t-initial-app-check (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-arg-driven-app-check {f = f} cls darg df) =
    t-arg-driven-app-check (classify-canon bound f cls)
                           (canon-pres-ᵢ bound sub pib darg) (canon-pres-ᶜ bound sub pib df)
  canon-pres-ᶜ {ctx = ctx} bound sub pib (t-var-poly-instantiate {x = x} cb ¬u lln lin lp ig d)
    rewrite canon-RVar-keep bound x (or-l (app pib (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x lp))) =
      t-var-poly-instantiate cb ¬u lln lin lp ig d
