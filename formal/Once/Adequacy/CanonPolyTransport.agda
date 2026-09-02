-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonPolyTransport — the POLY-CONTEXT transport (Plan 0.51).
--
-- `canonModule` canonicalizes poly-DEF bodies too, so `ModuleTyped mR` lives at
-- the canonExpr'd poly context `canonPolysCtx b p`, not `p`. This module:
--   * foundational commutes (`lookupPoly-canon`, `removePoly-canon`),
--   * `polys-transport-{ᵢ,ᶜ}`: a `⊢ᶜ` derivation at a poly context `p` lifts to
--     the canonExpr'd context `canonPolysCtx b p` (the expression is UNCHANGED;
--     only the t-var-poly-instantiate body and the cata sub-context read polys,
--     and they re-derive via `canon-pres-ᶜ` + recursion).
------------------------------------------------------------------------

module Once.Adequacy.CanonPolyTransport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (_<_)
open import Induction.WellFounded using (Acc; acc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.String.Properties as StrProp using ()
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type; PolyType; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; Int; Float; Str; Buffer)
open import Once.CanonicalName using (showCanonical; CanonicalName; canonical; gen; generatorNS; _≟ᶜ_)
open import Once.TypeCheck.Raw using (RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna)
open import Once.Parser.Module.Resolve using (canonExpr; elemStr)
open import Once.TypeCheck.Classify using (PolyCtx; lookupPoly; removePoly; removePoly-decreases;
  lookupPolyPrefix; lookupPolyPrefix-decreases)

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
-- Plan 0.58 (telescope): the corresponding commutes for `lookupPolyPrefix`.
-- The prefix IS the canonicalized tail, so ONE commute subsumes both
-- `lookupPoly-canon` and `removePoly-canon`.
------------------------------------------------------------------------

canon-prefix-entry : List String → (PolyType × RawExpr × PolyCtx) → (PolyType × RawExpr × PolyCtx)
canon-prefix-entry b (s , body , prefix) = (s , canonExpr b [] [] body , canonPolysCtx b prefix)

lookupPolyPrefix-canon : ∀ (b : List String) (p : PolyCtx) (x : String)
  → lookupPolyPrefix (canonPolysCtx b p) x ≡ mapMaybe (canon-prefix-entry b) (lookupPolyPrefix p x)
lookupPolyPrefix-canon b [] x = refl
lookupPolyPrefix-canon b ((n , s , body) ∷ rest) x with StrProp._≟_ n x
... | yes _ = refl
... | no  _ = lookupPolyPrefix-canon b rest x

lookupPolyPrefix-canon-just : ∀ (b : List String) (p : PolyCtx) (x : String) {s body prefix}
  → lookupPolyPrefix p x ≡ just (s , body , prefix)
  → lookupPolyPrefix (canonPolysCtx b p) x ≡ just (s , canonExpr b [] [] body , canonPolysCtx b prefix)
lookupPolyPrefix-canon-just b p x {s} {body} {prefix} lp
  rewrite lookupPolyPrefix-canon b p x rewrite lp = refl

-- A name found in the prefix (a tail of `p`) is found in `p` — so PInB descends.
lookupPolyPrefix-mono : ∀ (x y : String) (p : PolyCtx) {s body prefix r}
  → lookupPolyPrefix p x ≡ just (s , body , prefix)
  → lookupPoly prefix y ≡ just r → Σ-syntax _ (λ r' → lookupPoly p y ≡ just r')
lookupPolyPrefix-mono x y [] () lpre
lookupPolyPrefix-mono x y ((n , s , b) ∷ rest) lp lpre with StrProp._≟_ n x
... | yes _ = aux lp lpre
  where
    aux : ∀ {s' b' prefix r} → just (s , b , rest) ≡ just (s' , b' , prefix)
        → lookupPoly prefix y ≡ just r → Σ-syntax _ (λ r' → lookupPoly ((n , s , b) ∷ rest) y ≡ just r')
    aux refl lpre' with StrProp._≟_ n y
    ... | yes _ = _ , refl
    ... | no  _ = _ , lpre'
... | no  _ with lookupPolyPrefix-mono x y rest lp lpre
...   | _ , lp' with StrProp._≟_ n y
...     | yes _ = _ , refl
...     | no  _ = _ , lp'

lookupPolyPrefix-PInB : ∀ {p b} (x : String) {s body prefix}
  → lookupPolyPrefix p x ≡ just (s , body , prefix) → PInB p b → PInB prefix b
lookupPolyPrefix-PInB {p} x lp pib {y} lpre with lookupPolyPrefix-mono x y p lp lpre
... | _ , lp' = pib lp'

------------------------------------------------------------------------
-- The transport itself.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst)
open import Once.Surface.Syntax using (zeroUsage)
open import Once.TypeCheck.Classify
  using (NamedCtx; mkCtx; ctxWithImportsAndPolys; composeMid
        ; composeArgB; composeArgB-res; composeArgB-lookup; composeArgB-fst; composeArgB-snd; domainOfHead)
open import Once.TypeCheck.Judgment
open import Once.Adequacy.CanonPreserve using (⊆ᵇ-nil)
open import Once.Adequacy.CanonPreserveMutual using (canon-pres-ᶜ; mkPIB)

-- canonicalize a ctx's poly context (record-update keeps imports/locals).
cpc : List String → NamedCtx → NamedCtx
cpc b ctx = record ctx { polys = canonPolysCtx b (NamedCtx.polys ctx) }

-- `composeMid` reads `lookupPoly`'s SCHEMA (preserved by canonPolysCtx) +
-- `domainOfHead` (imports only, unchanged), so it is INVARIANT. Stated over a
-- single explicit `ctx` (no buried implicits); composeArgB's only polys-dependence
-- is `composeArgB-lookup` (the schema path).
composeArgB-lookup-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (name : String) (A : Type)
  → composeArgB-lookup (cpc b ctx) name A ≡ composeArgB-lookup ctx name A
composeArgB-lookup-polys-canon b ctx name A
  rewrite lookupPoly-canon b (NamedCtx.polys ctx) name with lookupPoly (NamedCtx.polys ctx) name
... | just (schema , _) = refl
... | nothing = refl

composeArgB-fst-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (A : Type)
  → composeArgB-fst (cpc b ctx) A ≡ composeArgB-fst ctx A
composeArgB-fst-polys-canon b ctx (X * Y)      = refl
composeArgB-fst-polys-canon b ctx Unit         = composeArgB-lookup-polys-canon b ctx "fst" Unit
composeArgB-fst-polys-canon b ctx Void         = composeArgB-lookup-polys-canon b ctx "fst" Void
composeArgB-fst-polys-canon b ctx (X + Y)      = composeArgB-lookup-polys-canon b ctx "fst" (X + Y)
composeArgB-fst-polys-canon b ctx (X ⇒[ k ] Y) = composeArgB-lookup-polys-canon b ctx "fst" (X ⇒[ k ] Y)
composeArgB-fst-polys-canon b ctx (μ-type F)   = composeArgB-lookup-polys-canon b ctx "fst" (μ-type F)
composeArgB-fst-polys-canon b ctx (ν-type F)   = composeArgB-lookup-polys-canon b ctx "fst" (ν-type F)
composeArgB-fst-polys-canon b ctx Int          = composeArgB-lookup-polys-canon b ctx "fst" Int
composeArgB-fst-polys-canon b ctx Float        = composeArgB-lookup-polys-canon b ctx "fst" Float
composeArgB-fst-polys-canon b ctx Str          = composeArgB-lookup-polys-canon b ctx "fst" Str
composeArgB-fst-polys-canon b ctx Buffer       = composeArgB-lookup-polys-canon b ctx "fst" Buffer

composeArgB-snd-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (A : Type)
  → composeArgB-snd (cpc b ctx) A ≡ composeArgB-snd ctx A
composeArgB-snd-polys-canon b ctx (X * Y)      = refl
composeArgB-snd-polys-canon b ctx Unit         = composeArgB-lookup-polys-canon b ctx "snd" Unit
composeArgB-snd-polys-canon b ctx Void         = composeArgB-lookup-polys-canon b ctx "snd" Void
composeArgB-snd-polys-canon b ctx (X + Y)      = composeArgB-lookup-polys-canon b ctx "snd" (X + Y)
composeArgB-snd-polys-canon b ctx (X ⇒[ k ] Y) = composeArgB-lookup-polys-canon b ctx "snd" (X ⇒[ k ] Y)
composeArgB-snd-polys-canon b ctx (μ-type F)   = composeArgB-lookup-polys-canon b ctx "snd" (μ-type F)
composeArgB-snd-polys-canon b ctx (ν-type F)   = composeArgB-lookup-polys-canon b ctx "snd" (ν-type F)
composeArgB-snd-polys-canon b ctx Int          = composeArgB-lookup-polys-canon b ctx "snd" Int
composeArgB-snd-polys-canon b ctx Float        = composeArgB-lookup-polys-canon b ctx "snd" Float
composeArgB-snd-polys-canon b ctx Str          = composeArgB-lookup-polys-canon b ctx "snd" Str
composeArgB-snd-polys-canon b ctx Buffer       = composeArgB-lookup-polys-canon b ctx "snd" Buffer

-- D136: the four generator arms read off the CANONICAL head now, so this is
-- the `composeArgB-res` twin; a bare name is a plain lookup (below).
composeArgB-res-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (cn : CanonicalName) (A : Type)
  → composeArgB-res (cpc b ctx) cn A ≡ composeArgB-res ctx cn A
composeArgB-res-polys-canon b ctx (canonical (ns ∷ g ∷ [])) A with StrProp._≟_ ns generatorNS
... | no  _ = composeArgB-lookup-polys-canon b ctx (showCanonical (canonical (ns ∷ g ∷ []))) A
... | yes refl with StrProp._≟_ g "fst"
...   | yes _ = composeArgB-fst-polys-canon b ctx A
...   | no  _ with StrProp._≟_ g "snd"
...     | yes _ = composeArgB-snd-polys-canon b ctx A
...     | no  _ with StrProp._≟_ g "id"
...       | yes _ = refl
...       | no  _ with StrProp._≟_ g "terminal"
...         | yes _ = refl
...         | no  _ = composeArgB-lookup-polys-canon b ctx (showCanonical (canonical (generatorNS ∷ g ∷ []))) A
composeArgB-res-polys-canon b ctx (canonical []) A =
  composeArgB-lookup-polys-canon b ctx (showCanonical (canonical [])) A
composeArgB-res-polys-canon b ctx (canonical (n ∷ [])) A =
  composeArgB-lookup-polys-canon b ctx (showCanonical (canonical (n ∷ []))) A
composeArgB-res-polys-canon b ctx (canonical (p ∷ q ∷ r ∷ rest)) A =
  composeArgB-lookup-polys-canon b ctx (showCanonical (canonical (p ∷ q ∷ r ∷ rest))) A

-- D127: like `CanonComposeMid`, these two are PREMISE-FREE structural
-- inductions on the raw arm. `cpc` touches only the `polys` field, and the only
-- polys-dependence in `composeArgB` is `composeArgB-lookup`; `domainOfHead`
-- reads `imports` alone, so every one of its clauses is `refl` — but the split
-- is still needed, since `cpc b ctx` and `ctx` differ syntactically and neither
-- side reduces while the arm is abstract.
composeArgB-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (A : Type) (g : RawExpr)
  → composeArgB (cpc b ctx) g A ≡ composeArgB ctx g A
composeArgB-polys-canon b ctx A (RVar name)     = composeArgB-lookup-polys-canon b ctx name A
composeArgB-polys-canon b ctx A (RResolved cn)  = composeArgB-res-polys-canon b ctx cn A
composeArgB-polys-canon b ctx A (RQualified n al) = refl
-- The nested-compose head: recurse into `g'` then `f'`. A head that is NOT
-- `compose` is `nothing` on both sides — and reduces there because the `with`
-- abstracts exactly the `≟` that `Classify.composeArgB` dispatches on.
-- D136: a BARE two-argument head is no longer a nested compose (that clause was
-- deleted — post-resolution it could only fire on a shadowing binder), so both
-- sides are `nothing`. The CANONICAL head is where the recursion lives.
composeArgB-polys-canon b ctx A (RApp (RApp (RVar x) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RResolved cn) f') g') with cn ≟ᶜ gen "compose"
... | no  _ = refl
... | yes _ rewrite composeArgB-polys-canon b ctx A g' with composeArgB ctx g' A
...   | nothing = refl
...   | just B′ rewrite composeArgB-polys-canon b ctx B′ f' = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RApp a c) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RQualified n al) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RLam y c) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RLet y e₁ e₂) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RPair a c) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RDestruct sc xl el xr er) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp RUnit f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RInt n) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RFloat i fp l q) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RStringLit str) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RAnnot e t) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RBinOp op a c) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RUnaryOp op e) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RApp (RAna F c) f') g') = refl
composeArgB-polys-canon b ctx A (RApp (RVar x) g') = refl
composeArgB-polys-canon b ctx A (RApp (RQualified n al) g') = refl
composeArgB-polys-canon b ctx A (RApp (RResolved cn) g') = refl
composeArgB-polys-canon b ctx A (RApp (RLam y c) g') = refl
composeArgB-polys-canon b ctx A (RApp (RLet y e₁ e₂) g') = refl
composeArgB-polys-canon b ctx A (RApp (RPair a c) g') = refl
composeArgB-polys-canon b ctx A (RApp (RDestruct sc xl el xr er) g') = refl
composeArgB-polys-canon b ctx A (RApp RUnit g') = refl
composeArgB-polys-canon b ctx A (RApp (RInt n) g') = refl
composeArgB-polys-canon b ctx A (RApp (RFloat i fp l q) g') = refl
composeArgB-polys-canon b ctx A (RApp (RStringLit str) g') = refl
composeArgB-polys-canon b ctx A (RApp (RAnnot e t) g') = refl
composeArgB-polys-canon b ctx A (RApp (RBinOp op a c) g') = refl
composeArgB-polys-canon b ctx A (RApp (RUnaryOp op e) g') = refl
composeArgB-polys-canon b ctx A (RApp (RAna F c) g') = refl
-- D135: the body must be exposed (see `CanonComposeMid`). `cpc` does not
-- touch the expression at all, so every case is `refl`.
composeArgB-polys-canon b ctx A (RLam y (RQualified n al)) = refl
composeArgB-polys-canon b ctx A (RLam y (RResolved cn)) = refl
composeArgB-polys-canon b ctx A (RLam y (RApp a c)) = refl
composeArgB-polys-canon b ctx A (RLam y (RLam z c)) = refl
composeArgB-polys-canon b ctx A (RLam y (RLet z e₁ e₂)) = refl
composeArgB-polys-canon b ctx A (RLam y (RPair a c)) = refl
composeArgB-polys-canon b ctx A (RLam y (RDestruct sc xl el xr er)) = refl
composeArgB-polys-canon b ctx A (RLam y RUnit) = refl
composeArgB-polys-canon b ctx A (RLam y (RInt n)) = refl
composeArgB-polys-canon b ctx A (RLam y (RFloat i fp l q)) = refl
composeArgB-polys-canon b ctx A (RLam y (RStringLit str)) = refl
composeArgB-polys-canon b ctx A (RLam y (RAnnot e t)) = refl
composeArgB-polys-canon b ctx A (RLam y (RBinOp op a c)) = refl
composeArgB-polys-canon b ctx A (RLam y (RUnaryOp op e)) = refl
composeArgB-polys-canon b ctx A (RLam y (RAna F c)) = refl
composeArgB-polys-canon b ctx A (RLam y (RVar x)) = refl
composeArgB-polys-canon b ctx A (RLet y e₁ e₂) = refl
composeArgB-polys-canon b ctx A (RPair a c) = refl
composeArgB-polys-canon b ctx A (RDestruct sc xl el xr er) = refl
composeArgB-polys-canon b ctx A RUnit = refl
composeArgB-polys-canon b ctx A (RInt n) = refl
composeArgB-polys-canon b ctx A (RFloat i fp l q) = refl
composeArgB-polys-canon b ctx A (RStringLit str) = refl
composeArgB-polys-canon b ctx A (RAnnot e t) = refl
composeArgB-polys-canon b ctx A (RBinOp op a c) = refl
composeArgB-polys-canon b ctx A (RUnaryOp op e) = refl
composeArgB-polys-canon b ctx A (RAna F c) = refl

domainOfHead-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (fa : RawExpr)
  → domainOfHead (cpc b ctx) fa ≡ domainOfHead ctx fa
domainOfHead-polys-canon b ctx (RVar name)      = refl
domainOfHead-polys-canon b ctx (RQualified n al) = refl
domainOfHead-polys-canon b ctx (RResolved cn)   = refl
domainOfHead-polys-canon b ctx (RApp f x)       = refl
domainOfHead-polys-canon b ctx (RLam y c)       = refl
domainOfHead-polys-canon b ctx (RLet y e₁ e₂)   = refl
domainOfHead-polys-canon b ctx (RPair a c)      = refl
domainOfHead-polys-canon b ctx (RDestruct sc xl el xr er) = refl
domainOfHead-polys-canon b ctx RUnit            = refl
domainOfHead-polys-canon b ctx (RInt n)         = refl
domainOfHead-polys-canon b ctx (RFloat i fp l q) = refl
domainOfHead-polys-canon b ctx (RStringLit str) = refl
domainOfHead-polys-canon b ctx (RAnnot e t)     = refl
domainOfHead-polys-canon b ctx (RBinOp op a c)  = refl
domainOfHead-polys-canon b ctx (RUnaryOp op e)  = refl
domainOfHead-polys-canon b ctx (RAna F c)       = refl

composeMid-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (fa g : RawExpr) {A B}
  → composeMid ctx fa g A ≡ just B
  → composeMid (cpc b ctx) fa g A ≡ just B
composeMid-polys-canon b ctx fa g {A = A} cm
  rewrite composeArgB-polys-canon b ctx A g | domainOfHead-polys-canon b ctx fa = cm

-- The `t-var-poly-instantiate` case recurses on `canon-pres-ᶜ d` (the inlined poly
-- body) at `removePoly x p` — genuinely WELL-FOUNDED (the poly context strictly
-- shrinks each level). Formerly asserted via `{-# TERMINATING #-}`; now PROVEN by
-- well-founded recursion on `Acc _<_ (length p)` (the descent that
-- `removePoly-decreases` supplies), mirroring `resolveExprWF` (Elaborate). Foetus
-- takes the lexicographic (Acc, derivation) order: structural sub-derivation calls
-- keep `ac`; the one poly-shrink call passes `rec (removePoly-decreases …)`.
mutual
  polys-transport-ᵢ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → Acc _<_ (length p) → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i p s ⊢ᵢ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵢ e ∶ A ⨾ Ψ
  polys-transport-ᵢ b p pib ac (t-int n)  = t-int n
  polys-transport-ᵢ b p pib ac (t-float i f l pos) = t-float i f l pos
  polys-transport-ᵢ b p pib ac (t-str s)  = t-str s
  polys-transport-ᵢ b p pib ac t-unit     = t-unit
  polys-transport-ᵢ b p pib ac t-unit-var = t-unit-var
  polys-transport-ᵢ b p pib ac (t-var-local lk) = t-var-local lk
  polys-transport-ᵢ b p pib ac (t-var-qualified imp conc) = t-var-qualified imp conc
  polys-transport-ᵢ b p pib ac (t-var-resolved ng imp conc) = t-var-resolved ng imp conc
  polys-transport-ᵢ b p pib ac (t-var-import ¬gw lkn imp conc) = t-var-import ¬gw lkn imp conc
  -- Plan 0.58 / D071: infer-mode ground telescope reference — same telescope
  -- descent as the check-mode `t-var-poly-instantiate` case below (the schema
  -- is canon-invariant, so the `isGround` and type-pin premises carry over).
  polys-transport-ᵢ b {i = i} p pib (acc rec) (t-var-poly-instantiate-infer {x = x} {body = body} {prefix = prefix} cb lln lin lp ig Teq d) =
    t-var-poly-instantiate-infer cb lln lin (lookupPolyPrefix-canon-just b p x lp) ig Teq
      (polys-transport-ᶜ b prefix (lookupPolyPrefix-PInB {p} {b} x lp pib)
         (rec (lookupPolyPrefix-decreases x p lp))
         (canon-pres-ᶜ {ctx = ctxWithImportsAndPolys i prefix} b
           (⊆ᵇ-nil {b}) (mkPIB (lookupPolyPrefix-PInB {p} {b} x lp pib)) d))
  polys-transport-ᵢ b p pib ac (t-annot d) = t-annot (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-pair d₁ d₂) = t-pair (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-neg d) = t-neg (polys-transport-ᵢ b p pib ac d)
  -- PLAN 0.73 F3: a leaf, like `t-float` — no premise to transport.
  polys-transport-ᵢ b p pib ac (t-neg-float i f l q) = t-neg-float i f l q
  polys-transport-ᵢ b p pib ac (t-let d₁ d₂) = t-let (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-case ds dL dR) =
    t-case (polys-transport-ᵢ b p pib ac ds) (polys-transport-ᵢ b p pib ac dL) (polys-transport-ᵢ b p pib ac dR)
  polys-transport-ᵢ b p pib ac (t-binop-arith pr d₁ d₂) = t-binop-arith pr (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  -- PLAN 0.75 F4: structural, exactly as its integer twin above.
  polys-transport-ᵢ b p pib ac (t-binop-arith-float pr d₁ d₂) = t-binop-arith-float pr (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  -- D125: the mixed forms, structurally identical again.
  polys-transport-ᵢ b p pib ac (t-binop-arith-float-il pr d₁ d₂) = t-binop-arith-float-il pr (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-binop-arith-float-ir pr d₁ d₂) = t-binop-arith-float-ir pr (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-binop-cmp pr d₁ d₂) = t-binop-cmp pr (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-id-app d) = t-id-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-fst-app d) = t-fst-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-snd-app d) = t-snd-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-terminal-app d) = t-terminal-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-apply-app-infer d) = t-apply-app-infer (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-app cls df dx) = t-app cls (polys-transport-ᵢ b p pib ac df) (polys-transport-ᶜ b p pib ac dx)
  polys-transport-ᵢ b p pib ac (t-effApp cls df dx) = t-effApp cls (polys-transport-ᵢ b p pib ac df) (polys-transport-ᶜ b p pib ac dx)

  polys-transport-ᶜ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → Acc _<_ (length p) → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i p s ⊢ᶜ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᶜ e ∶ A ⨾ Ψ
  -- D127: what was `polys-transport-ᵐ` is these clauses. The seven leaves have
  -- no premise that reads `polys`; the combinators recurse.
  polys-transport-ᶜ b p pib ac (t-id-check) = t-id-check
  polys-transport-ᶜ b p pib ac (t-fst-check) = t-fst-check
  polys-transport-ᶜ b p pib ac (t-snd-check) = t-snd-check
  polys-transport-ᶜ b p pib ac (t-terminal-morph-check) = t-terminal-morph-check
  polys-transport-ᶜ b p pib ac (t-initial-morph-check) = t-initial-morph-check
  polys-transport-ᶜ b p pib ac (t-inl-morph-check) = t-inl-morph-check
  polys-transport-ᶜ b p pib ac (t-inr-morph-check) = t-inr-morph-check
  polys-transport-ᶜ b {n = n} {Γ = Γ} {Δ = Δ} {f = fr} {i = i} {s = s} p pib ac
    (t-compose-check {f = fa} {g = g} cm df dg) =
    t-compose-check (composeMid-polys-canon b (mkCtx n Γ Δ fr i p s) fa g cm)
                    (polys-transport-ᶜ b p pib ac df) (polys-transport-ᶜ b p pib ac dg)
  polys-transport-ᶜ b p pib ac (t-case-copair-check df dg) =
    t-case-copair-check (polys-transport-ᶜ b p pib ac df) (polys-transport-ᶜ b p pib ac dg)
  polys-transport-ᶜ b p pib ac (t-pair-morph-check df dg) =
    t-pair-morph-check (polys-transport-ᶜ b p pib ac df) (polys-transport-ᶜ b p pib ac dg)
  polys-transport-ᶜ b p pib ac (t-curry-check df) = t-curry-check (polys-transport-ᶜ b p pib ac df)
  -- The algebra sits at `ctxWithImportsAndPolys i p`, which IS a `mkCtx` with
  -- the same poly context, so the recursion applies to it unchanged.
  polys-transport-ᶜ b p pib ac (t-cata-check eqW dalg) =
    t-cata-check eqW (polys-transport-ᶜ b p pib ac dalg)
  polys-transport-ᶜ b p pib ac (t-embed d) = t-embed (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-subsume d) = t-subsume (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-lam le d) = t-lam le (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-pair-lit-check d₁ d₂) = t-pair-lit-check (polys-transport-ᶜ b p pib ac d₁) (polys-transport-ᶜ b p pib ac d₂)
  polys-transport-ᶜ b p pib ac (t-In-app-check wf d) = t-In-app-check wf (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-apply-check d) = t-apply-check (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-inl-app-check d) = t-inl-app-check (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-inr-app-check d) = t-inr-app-check (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-initial-app-check d) = t-initial-app-check (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check cls (polys-transport-ᵢ b p pib ac darg) (polys-transport-ᶜ b p pib ac df)
  -- The one NON-structural recursion: the poly context shrinks to the PREFIX
  -- (Plan 0.58 telescope), so pass the strictly-smaller accessibility
  -- `rec (lookupPolyPrefix-decreases x p lp)`. The commute is baked into
  -- `lookupPolyPrefix-canon-just` (prefix = canonicalized tail), so — unlike the
  -- old `removePoly` version — NO `subst` is needed.
  polys-transport-ᶜ b {i = i} p pib (acc rec) (t-var-poly-instantiate {x = x} {T = T} {body = body} {prefix = prefix} cb lln lin lp ig d) =
    t-var-poly-instantiate cb lln lin (lookupPolyPrefix-canon-just b p x lp) ig
      (polys-transport-ᶜ b prefix (lookupPolyPrefix-PInB {p} {b} x lp pib)
         (rec (lookupPolyPrefix-decreases x p lp))
         (canon-pres-ᶜ {ctx = ctxWithImportsAndPolys i prefix} b
           (⊆ᵇ-nil {b}) (mkPIB (lookupPolyPrefix-PInB {p} {b} x lp pib)) d))
