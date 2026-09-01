-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonPreserveMutual — Plan 0.51 Step 2 (mutual preservation).
-- The resolver's own-module canonicalization `canonExpr bound [] []` (RVar x →
-- RResolved (canonical [x]) for a FREE, non-builtin, non-bound, non-poly x)
-- PRESERVES the two mutual declarative judgments `⊢ᵢ` / `⊢ᶜ`, given:
--   * `Names⊆ ctx bound` — the context's locals are all in `bound`, AND
--   * `PolyInB ctx bound` — every own-module poly-def name is in `bound`
--     (true by construction: `canonDecl` seeds `bound := polyDefNames ds`, the
--     SAME source the `polys` context is built from — see Resolve.polyDefNames).
-- D127: the `⊢ᵐ` and `⊢ᵍ` realms are gone, and with them `canon-pres-ᵐ` and
-- `pres-ᵍ`. The combinator rules they carried are now ordinary `⊢ᶜ` rules and
-- live in `canon-pres-ᶜ` below.
--
-- `composeMid-canon` (the `t-compose-check` middle-type premise transfer) is
-- discharged in `Once.Adequacy.CanonComposeMid`, now WITHOUT any typing
-- premise: it is a fact about raw syntax.
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
open import Once.Parser.Module.Resolve using (canonExpr; isBuiltinName; elemStr)
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
-- `Once.Adequacy.CanonComposeMid` by structural induction on the RAW ARMS (no
-- typing premise; see that module's header).
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

  canon-pres-ᶜ : ∀ {ctx e A Ψ} (bound : List String)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ canonExpr bound [] [] e ∶ A ⨾ Ψ
  -- D127: the categorical combinators are ORDINARY `⊢ᶜ` rules now, so what was
  -- the separate `canon-pres-ᵐ` induction is these clauses. The point-free
  -- leaves are builtin heads (kept by `canon-builtin`); the combinators recurse
  -- into `canon-pres-ᶜ` on arms that are ordinary terms in the ambient context.
  canon-pres-ᶜ bound sub pib (t-id-check)
    rewrite canon-builtin bound "id" refl = t-id-check
  canon-pres-ᶜ bound sub pib (t-fst-check)
    rewrite canon-builtin bound "fst" refl = t-fst-check
  canon-pres-ᶜ bound sub pib (t-snd-check)
    rewrite canon-builtin bound "snd" refl = t-snd-check
  canon-pres-ᶜ bound sub pib (t-terminal-morph-check)
    rewrite canon-builtin bound "terminal" refl = t-terminal-morph-check
  canon-pres-ᶜ bound sub pib (t-initial-morph-check)
    rewrite canon-builtin bound "initial" refl = t-initial-morph-check
  canon-pres-ᶜ bound sub pib (t-inl-morph-check)
    rewrite canon-builtin bound "inl" refl = t-inl-morph-check
  canon-pres-ᶜ bound sub pib (t-inr-morph-check)
    rewrite canon-builtin bound "inr" refl = t-inr-morph-check
  canon-pres-ᶜ bound sub pib (t-compose-check {f = f} {g = g} cm df dg)
    rewrite canon-builtin bound "compose" refl =
      t-compose-check (composeMid-canon bound f g cm)
                      (canon-pres-ᶜ bound sub pib df) (canon-pres-ᶜ bound sub pib dg)
  canon-pres-ᶜ bound sub pib (t-case-copair-check df dg)
    rewrite canon-builtin bound "case" refl =
      t-case-copair-check (canon-pres-ᶜ bound sub pib df) (canon-pres-ᶜ bound sub pib dg)
  canon-pres-ᶜ bound sub pib (t-pair-morph-check df dg)
    rewrite canon-builtin bound "pair" refl =
      t-pair-morph-check (canon-pres-ᶜ bound sub pib df) (canon-pres-ᶜ bound sub pib dg)
  canon-pres-ᶜ bound sub pib (t-curry-check df)
    rewrite canon-builtin bound "curry" refl =
      t-curry-check (canon-pres-ᶜ bound sub pib df)
  -- The algebra is checked in the CLEARED context (`ctxWithImportsAndPolys`),
  -- whose `named` is empty — so `Names⊆` is the vacuous `⊆ᵇ-nil` — while its
  -- `polys` are the ambient ones, so `PolyInB` transports unchanged.
  canon-pres-ᶜ bound sub pib (t-cata-check eqW dalg)
    rewrite canon-builtin bound "cata" refl =
      t-cata-check eqW
        (canon-pres-ᶜ bound (⊆ᵇ-nil {bound}) (mkPIB (λ {x'} h → app pib {x'} h)) dalg)
  canon-pres-ᶜ bound sub pib (t-embed d) = t-embed (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-subsume d) = t-subsume (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-lam {x = x} {A = A} le d) =
    t-lam le (canon-pres-ᶜ (x ∷ bound) (⊆ᵇ-cons x sub) (poly-ext x A pib) d)
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
