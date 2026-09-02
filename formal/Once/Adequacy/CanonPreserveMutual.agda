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
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CanonicalName using (bare-NotGenerator; CanonicalName)
open import Once.Type using (Type)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr; isBuiltinName; elemStr; ¬GenWord-isBuiltinName; isBuiltinName-false)
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

open import Once.Adequacy.CanonComposeMid using (composeMid-canon; CabOK; DohOK)

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
  canon-pres-ᵢ bound sub pib t-unit-var = t-unit-var
  canon-pres-ᵢ {ctx} bound sub pib (t-var-local {x = x} lk)
    rewrite canon-RVar-keep bound x (sub x (lookup-just→elem ctx x lk)) =
      t-var-local lk
  canon-pres-ᵢ bound sub pib (t-var-qualified imp conc) = t-var-qualified imp conc
  canon-pres-ᵢ bound sub pib (t-var-resolved ng imp conc) = t-var-resolved ng imp conc
  -- D136: the rule's own `¬ GenWord x` premise is what rules out the middle
  -- branch — a reserved word never reaches the import table as a bare name, so
  -- the resolver's generator arm is unreachable here.
  canon-pres-ᵢ {ctx = ctx} {A = T} {Ψ = Ψ} bound sub pib (t-var-import {x = x} ¬gw lkn imp conc) =
    go (nameOK-of bound x ¬gw)
    where
      go : NameOK bound x → ctx ⊢ᵢ canonExpr bound [] [] (RawExpr.RVar x) ∶ T ⨾ Ψ
      go (inj₁ eb) rewrite canon-RVar-keep bound x eb = t-var-import ¬gw lkn imp conc
      go (inj₂ (eb , eg)) rewrite canon-RVar-resolve bound x eb eg =
        t-var-resolved (bare-NotGenerator x) imp conc
  -- Plan 0.58 / D071: infer-mode ground telescope reference — same keep-bare
  -- rewrite as the check-mode `t-var-poly-instantiate` case (a telescope name
  -- is in `bound`, so canonExpr keeps the bare RVar; premises are ctx-side).
  canon-pres-ᵢ {ctx = ctx} bound sub pib (t-var-poly-instantiate-infer {x = x} cb lln lin lp ig Teq d)
    rewrite canon-RVar-keep bound x (app pib (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x lp)) =
      t-var-poly-instantiate-infer cb lln lin lp ig Teq d
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
  canon-pres-ᵢ bound sub pib (t-id-app d) = t-id-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-fst-app d) = t-fst-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-snd-app d) = t-snd-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-terminal-app d) = t-terminal-app (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-apply-app-infer d) = t-apply-app-infer (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᵢ bound sub pib (t-app {f = f} cls df dx) =
    t-app (classify-canon bound f (head-unclaimed bound f sub pib df) cls)
          (canon-pres-ᵢ bound sub pib df) (canon-pres-ᶜ bound sub pib dx)
  canon-pres-ᵢ bound sub pib (t-effApp {f = f} cls df dx) =
    t-effApp (classify-canon bound f (head-unclaimed bound f sub pib df) cls)
             (canon-pres-ᵢ bound sub pib df) (canon-pres-ᶜ bound sub pib dx)

  -- D136: `classify-canon` needs to know the resolver does not CLAIM the
  -- application's head, and the head's own derivation is what says so —
  -- `t-var-local` puts it in `bound`, `t-var-import` carries `¬ GenWord x`
  -- outright, and a poly reference is in `bound` by `PolyInB`.
  head-unclaimed-name : ∀ {ctx A Ψ} (bound : List String) (x : String)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᵢ RawExpr.RVar x ∶ A ⨾ Ψ → NameOK bound x
  head-unclaimed-name {ctx} bound x sub pib (t-var-local lk) =
    inj₁ (sub x (lookup-just→elem ctx x lk))
  head-unclaimed-name bound x sub pib (t-var-import ¬gw _ _ _) = nameOK-of bound x ¬gw
  head-unclaimed-name {ctx} bound x sub pib (t-var-poly-instantiate-infer _ _ _ lp _ _ _) =
    inj₁ (app pib (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x lp))

  head-unclaimed : ∀ {ctx A Ψ} (bound : List String) (f : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᵢ f ∶ A ⨾ Ψ → HeadUnclaimed bound f
  head-unclaimed bound (RawExpr.RVar x) sub pib d = head-unclaimed-name bound x sub pib d
  head-unclaimed bound (RawExpr.RApp (RawExpr.RVar x) g) sub pib (t-app _ df _) =
    head-unclaimed-name bound x sub pib df
  head-unclaimed bound (RawExpr.RApp (RawExpr.RVar x) g) sub pib (t-effApp _ df _) =
    head-unclaimed-name bound x sub pib df
  head-unclaimed bound (RawExpr.RApp (RawExpr.RApp _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RQualified _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RResolved _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RLam _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RLet _ _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RPair _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RDestruct _ _ _ _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp RawExpr.RUnit _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RInt _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RFloat _ _ _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RStringLit _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RAnnot _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RBinOp _ _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RUnaryOp _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RApp (RawExpr.RAna _ _) _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RQualified _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RResolved _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RLam _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RLet _ _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RPair _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RDestruct _ _ _ _ _) sub pib _ = tt
  head-unclaimed bound RawExpr.RUnit sub pib _ = tt
  head-unclaimed bound (RawExpr.RInt _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RFloat _ _ _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RStringLit _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RAnnot _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RBinOp _ _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RUnaryOp _ _) sub pib _ = tt
  head-unclaimed bound (RawExpr.RAna _ _) sub pib _ = tt

  -- D136: the same extraction, for the compose ARMS. `domainOfHead` looks only
  -- at the arm's head; `composeArgB` also recurses into a canonical nested
  -- compose, so `CabOK` does too — and so does this, along the derivation that
  -- justifies each arm.
  nameOK-ᶜ : ∀ {ctx A Ψ} (bound : List String) (x : String)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ RawExpr.RVar x ∶ A ⨾ Ψ → NameOK bound x
  nameOK-ᶜ bound x sub pib (t-embed d) = head-unclaimed-name bound x sub pib d
  nameOK-ᶜ bound x sub pib (t-subsume d) = nameOK-ᶜ bound x sub pib d
  nameOK-ᶜ {ctx} bound x sub pib (t-var-poly-instantiate _ _ _ lp _ _) =
    inj₁ (app pib (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x lp))

  cabOK-of : ∀ {ctx A Ψ} (bound : List String) (g : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ g ∶ A ⨾ Ψ → CabOK bound g
  cabOK-of bound (RawExpr.RVar x) sub pib d = nameOK-ᶜ bound x sub pib d
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RVar z) f') g') sub pib d =
    cabOK-app2-var bound z f' g' sub pib d
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RResolved cn) f') g') sub pib d =
    cabOK-app2-res bound cn f' g' sub pib d
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RApp _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RQualified _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RLam _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RLet _ _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RPair _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RDestruct _ _ _ _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp RawExpr.RUnit _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RInt _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RFloat _ _ _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RStringLit _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RAnnot _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RBinOp _ _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RUnaryOp _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RApp (RawExpr.RAna _ _) _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RVar _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RQualified _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RResolved _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RLam _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RLet _ _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RPair _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RDestruct _ _ _ _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp RawExpr.RUnit _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RInt _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RFloat _ _ _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RStringLit _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RAnnot _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RBinOp _ _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RUnaryOp _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RApp (RawExpr.RAna _ _) _) sub pib _ = tt
  cabOK-of bound (RawExpr.RQualified _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RResolved _) sub pib _ = tt
  cabOK-of bound (RawExpr.RLam _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RLet _ _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RPair _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RDestruct _ _ _ _ _) sub pib _ = tt
  cabOK-of bound RawExpr.RUnit sub pib _ = tt
  cabOK-of bound (RawExpr.RInt _) sub pib _ = tt
  cabOK-of bound (RawExpr.RFloat _ _ _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RStringLit _) sub pib _ = tt
  cabOK-of bound (RawExpr.RAnnot _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RBinOp _ _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RUnaryOp _ _) sub pib _ = tt
  cabOK-of bound (RawExpr.RAna _ _) sub pib _ = tt

  -- A BARE two-argument head: `CabOK` asks only that the resolver not claim it.
  cabOK-app2-var : ∀ {ctx A Ψ} (bound : List String) (z : String) (f' g' : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ RawExpr.RApp (RawExpr.RApp (RawExpr.RVar z) f') g' ∶ A ⨾ Ψ
    → NameOK bound z
  cabOK-app2-var bound z f' g' sub pib (t-embed (t-app _ df _)) =
    cabOK-app1-var bound z f' sub pib df
  cabOK-app2-var bound z f' g' sub pib (t-embed (t-effApp _ df _)) =
    cabOK-app1-var bound z f' sub pib df
  cabOK-app2-var bound z f' g' sub pib (t-subsume d) = cabOK-app2-var bound z f' g' sub pib d
  cabOK-app2-var bound z f' g' sub pib (t-arg-driven-app-check _ _ df) =
    cabOK-app1-var-ᶜ bound z f' sub pib df

  cabOK-app1-var : ∀ {ctx A Ψ} (bound : List String) (z : String) (f' : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᵢ RawExpr.RApp (RawExpr.RVar z) f' ∶ A ⨾ Ψ → NameOK bound z
  cabOK-app1-var bound z f' sub pib (t-app _ df _) = head-unclaimed-name bound z sub pib df
  cabOK-app1-var bound z f' sub pib (t-effApp _ df _) = head-unclaimed-name bound z sub pib df

  cabOK-app1-var-ᶜ : ∀ {ctx A Ψ} (bound : List String) (z : String) (f' : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ RawExpr.RApp (RawExpr.RVar z) f' ∶ A ⨾ Ψ → NameOK bound z
  cabOK-app1-var-ᶜ bound z f' sub pib (t-embed d) = cabOK-app1-var bound z f' sub pib d
  cabOK-app1-var-ᶜ bound z f' sub pib (t-subsume d) = cabOK-app1-var-ᶜ bound z f' sub pib d
  cabOK-app1-var-ᶜ bound z f' sub pib (t-arg-driven-app-check _ _ df) =
    nameOK-ᶜ bound z sub pib df

  -- A CANONICAL two-argument head: `composeArgB` may recurse, so both arms do.
  cabOK-app2-res : ∀ {ctx A Ψ} (bound : List String) (cn : CanonicalName) (f' g' : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ RawExpr.RApp (RawExpr.RApp (RawExpr.RResolved cn) f') g' ∶ A ⨾ Ψ
    → CabOK bound f' × CabOK bound g'
  cabOK-app2-res bound cn f' g' sub pib (t-compose-check _ df dg) =
    cabOK-of bound f' sub pib df , cabOK-of bound g' sub pib dg
  cabOK-app2-res bound cn f' g' sub pib (t-case-copair-check df dg) =
    cabOK-of bound f' sub pib df , cabOK-of bound g' sub pib dg
  cabOK-app2-res bound cn f' g' sub pib (t-pair-morph-check df dg) =
    cabOK-of bound f' sub pib df , cabOK-of bound g' sub pib dg
  cabOK-app2-res bound cn f' g' sub pib (t-subsume d) =
    cabOK-app2-res bound cn f' g' sub pib d
  cabOK-app2-res bound cn f' g' sub pib (t-arg-driven-app-check _ dg df) =
    cabOK-app1-res-ᶜ bound cn f' sub pib df , cabOK-ᵢ bound g' sub pib dg
  cabOK-app2-res bound cn f' g' sub pib (t-embed (t-app _ df dg)) =
    cabOK-app1-res bound cn f' sub pib df , cabOK-of bound g' sub pib dg
  cabOK-app2-res bound cn f' g' sub pib (t-embed (t-effApp _ df dg)) =
    cabOK-app1-res bound cn f' sub pib df , cabOK-of bound g' sub pib dg

  cabOK-app1-res : ∀ {ctx A Ψ} (bound : List String) (cn : CanonicalName) (f' : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᵢ RawExpr.RApp (RawExpr.RResolved cn) f' ∶ A ⨾ Ψ → CabOK bound f'
  cabOK-app1-res bound cn f' sub pib (t-id-app d) = cabOK-ᵢ bound f' sub pib d
  cabOK-app1-res bound cn f' sub pib (t-fst-app d) = cabOK-ᵢ bound f' sub pib d
  cabOK-app1-res bound cn f' sub pib (t-snd-app d) = cabOK-ᵢ bound f' sub pib d
  cabOK-app1-res bound cn f' sub pib (t-terminal-app d) = cabOK-ᵢ bound f' sub pib d
  cabOK-app1-res bound cn f' sub pib (t-apply-app-infer d) = cabOK-ᵢ bound f' sub pib d
  cabOK-app1-res bound cn f' sub pib (t-app _ _ dx) = cabOK-of bound f' sub pib dx
  cabOK-app1-res bound cn f' sub pib (t-effApp _ _ dx) = cabOK-of bound f' sub pib dx

  cabOK-app1-res-ᶜ : ∀ {ctx A Ψ} (bound : List String) (cn : CanonicalName) (f' : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ RawExpr.RApp (RawExpr.RResolved cn) f' ∶ A ⨾ Ψ → CabOK bound f'
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-embed d) = cabOK-app1-res bound cn f' sub pib d
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-subsume d) = cabOK-app1-res-ᶜ bound cn f' sub pib d
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-curry-check df) = cabOK-of bound f' sub pib df
  -- The cata algebra is typed in the CLEARED context (no locals, ambient
  -- polys), exactly as in `canon-pres-ᶜ`'s own cata clause.
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-cata-check _ df) =
    cabOK-of bound f' (⊆ᵇ-nil {bound}) (mkPIB (λ {x'} h → app pib {x'} h)) df
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-In-app-check _ df) = cabOK-of bound f' sub pib df
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-apply-check d) = cabOK-ᵢ bound f' sub pib d
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-inl-app-check df) = cabOK-of bound f' sub pib df
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-inr-app-check df) = cabOK-of bound f' sub pib df
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-initial-app-check df) = cabOK-of bound f' sub pib df
  cabOK-app1-res-ᶜ bound cn f' sub pib (t-arg-driven-app-check _ dg _) =
    cabOK-ᵢ bound f' sub pib dg

  cabOK-ᵢ : ∀ {ctx A Ψ} (bound : List String) (g : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᵢ g ∶ A ⨾ Ψ → CabOK bound g
  cabOK-ᵢ bound g sub pib d = cabOK-of bound g sub pib (t-embed d)

  head-unclaimed-ᶜ : ∀ {ctx A Ψ} (bound : List String) (f : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ f ∶ A ⨾ Ψ → HeadUnclaimed bound f
  head-unclaimed-ᶜ bound (RawExpr.RVar x) sub pib d = nameOK-ᶜ bound x sub pib d
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RVar x) g) sub pib d =
    cabOK-app1-var-ᶜ bound x g sub pib d
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RApp _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RQualified _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RResolved _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RLam _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RLet _ _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RPair _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RDestruct _ _ _ _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp RawExpr.RUnit _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RInt _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RFloat _ _ _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RStringLit _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RAnnot _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RBinOp _ _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RUnaryOp _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RApp (RawExpr.RAna _ _) _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RQualified _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RResolved _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RLam _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RLet _ _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RPair _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RDestruct _ _ _ _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound RawExpr.RUnit sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RInt _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RFloat _ _ _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RStringLit _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RAnnot _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RBinOp _ _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RUnaryOp _ _) sub pib _ = tt
  head-unclaimed-ᶜ bound (RawExpr.RAna _ _) sub pib _ = tt

  dohOK-of : ∀ {ctx A Ψ} (bound : List String) (f : RawExpr)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ f ∶ A ⨾ Ψ → DohOK bound f
  dohOK-of bound (RawExpr.RVar x) sub pib d = nameOK-ᶜ bound x sub pib d
  dohOK-of bound (RawExpr.RApp _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RQualified _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RResolved _) sub pib _ = tt
  dohOK-of bound (RawExpr.RLam _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RLet _ _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RPair _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RDestruct _ _ _ _ _) sub pib _ = tt
  dohOK-of bound RawExpr.RUnit sub pib _ = tt
  dohOK-of bound (RawExpr.RInt _) sub pib _ = tt
  dohOK-of bound (RawExpr.RFloat _ _ _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RStringLit _) sub pib _ = tt
  dohOK-of bound (RawExpr.RAnnot _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RBinOp _ _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RUnaryOp _ _) sub pib _ = tt
  dohOK-of bound (RawExpr.RAna _ _) sub pib _ = tt

  canon-pres-ᶜ : ∀ {ctx e A Ψ} (bound : List String)
    → Names⊆ ctx bound → PolyInB ctx bound
    → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ canonExpr bound [] [] e ∶ A ⨾ Ψ
  -- D127: the categorical combinators are ORDINARY `⊢ᶜ` rules now, so what was
  -- the separate `canon-pres-ᵐ` induction is these clauses. The point-free
  -- leaves conclude at a canonical head (canonExpr is the identity there); the
  -- into `canon-pres-ᶜ` on arms that are ordinary terms in the ambient context.
  canon-pres-ᶜ bound sub pib (t-id-check) = t-id-check
  canon-pres-ᶜ bound sub pib (t-fst-check) = t-fst-check
  canon-pres-ᶜ bound sub pib (t-snd-check) = t-snd-check
  canon-pres-ᶜ bound sub pib (t-terminal-morph-check) = t-terminal-morph-check
  canon-pres-ᶜ bound sub pib (t-initial-morph-check) = t-initial-morph-check
  canon-pres-ᶜ bound sub pib (t-inl-morph-check) = t-inl-morph-check
  canon-pres-ᶜ bound sub pib (t-inr-morph-check) = t-inr-morph-check
  canon-pres-ᶜ bound sub pib (t-compose-check {f = f} {g = g} cm df dg) =
      t-compose-check (composeMid-canon bound f g (dohOK-of bound f sub pib df)
                                                  (cabOK-of bound g sub pib dg) cm)
                      (canon-pres-ᶜ bound sub pib df) (canon-pres-ᶜ bound sub pib dg)
  canon-pres-ᶜ bound sub pib (t-case-copair-check df dg) =
      t-case-copair-check (canon-pres-ᶜ bound sub pib df) (canon-pres-ᶜ bound sub pib dg)
  canon-pres-ᶜ bound sub pib (t-pair-morph-check df dg) =
      t-pair-morph-check (canon-pres-ᶜ bound sub pib df) (canon-pres-ᶜ bound sub pib dg)
  canon-pres-ᶜ bound sub pib (t-curry-check df) =
      t-curry-check (canon-pres-ᶜ bound sub pib df)
  -- The algebra is checked in the CLEARED context (`ctxWithImportsAndPolys`),
  -- whose `named` is empty — so `Names⊆` is the vacuous `⊆ᵇ-nil` — while its
  -- `polys` are the ambient ones, so `PolyInB` transports unchanged.
  canon-pres-ᶜ bound sub pib (t-cata-check eqW dalg) =
      t-cata-check eqW
        (canon-pres-ᶜ bound (⊆ᵇ-nil {bound}) (mkPIB (λ {x'} h → app pib {x'} h)) dalg)
  canon-pres-ᶜ bound sub pib (t-embed d) = t-embed (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-subsume d) = t-subsume (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-lam {x = x} {A = A} le d) =
    t-lam le (canon-pres-ᶜ (x ∷ bound) (⊆ᵇ-cons x sub) (poly-ext x A pib) d)
  canon-pres-ᶜ bound sub pib (t-pair-lit-check d₁ d₂) =
    t-pair-lit-check (canon-pres-ᶜ bound sub pib d₁) (canon-pres-ᶜ bound sub pib d₂)
  canon-pres-ᶜ bound sub pib (t-In-app-check wf d) = t-In-app-check wf (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-apply-check d) = t-apply-check (canon-pres-ᵢ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-inl-app-check d) = t-inl-app-check (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-inr-app-check d) = t-inr-app-check (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-initial-app-check d) = t-initial-app-check (canon-pres-ᶜ bound sub pib d)
  canon-pres-ᶜ bound sub pib (t-arg-driven-app-check {f = f} cls darg df) =
    t-arg-driven-app-check (classify-canon bound f (head-unclaimed-ᶜ bound f sub pib df) cls)
                           (canon-pres-ᵢ bound sub pib darg) (canon-pres-ᶜ bound sub pib df)
  canon-pres-ᶜ {ctx = ctx} bound sub pib (t-var-poly-instantiate {x = x} cb lln lin lp ig d)
    rewrite canon-RVar-keep bound x (app pib (lookupPolyPrefix⇒lookupPoly (NamedCtx.polys ctx) x lp)) =
      t-var-poly-instantiate cb lln lin lp ig d
