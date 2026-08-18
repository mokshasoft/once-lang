-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Once.CanonicalName using (showCanonical)
open import Once.TypeCheck.Raw using (RawExpr)
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
        ; composeArgB; composeArgB-rvar; composeArgB-lookup; composeArgB-fst; composeArgB-snd; domainOfHead)
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

composeArgB-rvar-polys-canon : ∀ (b : List String) (ctx : NamedCtx) (name : String) (A : Type)
  → composeArgB-rvar (cpc b ctx) name A ≡ composeArgB-rvar ctx name A
composeArgB-rvar-polys-canon b ctx name A with StrProp._≟_ name "fst"
... | yes _ = composeArgB-fst-polys-canon b ctx A
... | no  _ with StrProp._≟_ name "snd"
...   | yes _ = composeArgB-snd-polys-canon b ctx A
...   | no  _ with StrProp._≟_ name "id"
...     | yes _ = refl
...     | no  _ with StrProp._≟_ name "terminal"
...       | yes _ = refl
...       | no  _ = composeArgB-lookup-polys-canon b ctx name A

composeArgB-polys-canon : ∀ (b : List String) (ctx : NamedCtx) {g A′ π B′} (A : Type)
  → ctx ⊢ᵐ g ∶ A′ ⇨[ π ] B′
  → composeArgB (cpc b ctx) g A ≡ composeArgB ctx g A
composeArgB-polys-canon b ctx A (m-id _ _)       = composeArgB-rvar-polys-canon b ctx "id" A
composeArgB-polys-canon b ctx A (m-fst _ _)      = composeArgB-rvar-polys-canon b ctx "fst" A
composeArgB-polys-canon b ctx A (m-snd _ _)      = composeArgB-rvar-polys-canon b ctx "snd" A
composeArgB-polys-canon b ctx A (m-terminal _ _) = composeArgB-rvar-polys-canon b ctx "terminal" A
composeArgB-polys-canon b ctx A (m-initial _ _)  = composeArgB-rvar-polys-canon b ctx "initial" A
composeArgB-polys-canon b ctx A (m-inl _ _)      = composeArgB-rvar-polys-canon b ctx "inl" A
composeArgB-polys-canon b ctx A (m-inr _ _)      = composeArgB-rvar-polys-canon b ctx "inr" A
composeArgB-polys-canon b ctx A (m-compose {f = f} {g = g} cm df dg)
  rewrite composeArgB-polys-canon b ctx A dg with composeArgB ctx g A
... | nothing  = refl
... | just B′ rewrite composeArgB-polys-canon b ctx B′ df = refl
composeArgB-polys-canon b ctx A (m-case _ _)  = refl
composeArgB-polys-canon b ctx A (m-pair _ _)  = refl
composeArgB-polys-canon b ctx A (m-curry _)   = refl
composeArgB-polys-canon b ctx A (m-cata _ _)  = refl
composeArgB-polys-canon b ctx A (m-const (g-int n))       = refl
composeArgB-polys-canon b ctx A (m-const (g-float i f l d ok)) = refl
composeArgB-polys-canon b ctx A (m-const (g-terminal _ _)) = composeArgB-rvar-polys-canon b ctx "terminal" A
composeArgB-polys-canon b ctx A (m-const (g-pair _ _))    = refl
composeArgB-polys-canon b ctx A (m-const (g-inl _))       = refl
composeArgB-polys-canon b ctx A (m-const (g-inr _))       = refl
composeArgB-polys-canon b ctx A (m-const (g-In _ _))      = refl
composeArgB-polys-canon b ctx A (m-named {x = x} _ _ _ _ _)   = composeArgB-rvar-polys-canon b ctx x A
composeArgB-polys-canon b ctx A (m-named-resolved {cn = cn} _ _ _) = composeArgB-lookup-polys-canon b ctx (showCanonical cn) A

domainOfHead-polys-canon : ∀ (b : List String) (ctx : NamedCtx) {fa A′ π B′}
  → ctx ⊢ᵐ fa ∶ A′ ⇨[ π ] B′
  → domainOfHead (cpc b ctx) fa ≡ domainOfHead ctx fa
domainOfHead-polys-canon b ctx (m-id _ _)        = refl
domainOfHead-polys-canon b ctx (m-fst _ _)       = refl
domainOfHead-polys-canon b ctx (m-snd _ _)       = refl
domainOfHead-polys-canon b ctx (m-terminal _ _)  = refl
domainOfHead-polys-canon b ctx (m-initial _ _)   = refl
domainOfHead-polys-canon b ctx (m-inl _ _)       = refl
domainOfHead-polys-canon b ctx (m-inr _ _)       = refl
domainOfHead-polys-canon b ctx (m-compose _ _ _) = refl
domainOfHead-polys-canon b ctx (m-case _ _)      = refl
domainOfHead-polys-canon b ctx (m-pair _ _)      = refl
domainOfHead-polys-canon b ctx (m-curry _)       = refl
domainOfHead-polys-canon b ctx (m-cata _ _)      = refl
domainOfHead-polys-canon b ctx (m-const (g-int n))        = refl
domainOfHead-polys-canon b ctx (m-const (g-float i f l d ok)) = refl
domainOfHead-polys-canon b ctx (m-const (g-terminal _ _)) = refl
domainOfHead-polys-canon b ctx (m-const (g-pair _ _))     = refl
domainOfHead-polys-canon b ctx (m-const (g-inl _))        = refl
domainOfHead-polys-canon b ctx (m-const (g-inr _))        = refl
domainOfHead-polys-canon b ctx (m-const (g-In _ _))       = refl
domainOfHead-polys-canon b ctx (m-named _ _ _ _ _)            = refl
domainOfHead-polys-canon b ctx (m-named-resolved _ _ _)       = refl

composeMid-polys-canon : ∀ (b : List String) (ctx : NamedCtx) {fa g A′ π B′ A″ π′ B″} {A B}
  → ctx ⊢ᵐ fa ∶ A″ ⇨[ π′ ] B″
  → ctx ⊢ᵐ g ∶ A′ ⇨[ π ] B′
  → composeMid ctx fa g A ≡ just B
  → composeMid (cpc b ctx) fa g A ≡ just B
composeMid-polys-canon b ctx {A = A} df dg cm
  rewrite composeArgB-polys-canon b ctx A dg | domainOfHead-polys-canon b ctx df = cm

-- ⊢ᵍ is polys-INDEPENDENT (g-rules read only lookupLocal/lookupImport), so its
-- derivations transport by re-applying each rule (premises transfer verbatim).
polys-transport-ᵍ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) {e A}
  → mkCtx n Γ Δ f i p s ⊢ᵍ e ∶ A
  → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵍ e ∶ A
polys-transport-ᵍ b p (g-int n)          = g-int n
polys-transport-ᵍ b p (g-float i f l d ok) = g-float i f l d ok
polys-transport-ᵍ b p (g-terminal lL lI) = g-terminal lL lI
polys-transport-ᵍ b p (g-pair d₁ d₂)     = g-pair (polys-transport-ᵍ b p d₁) (polys-transport-ᵍ b p d₂)
polys-transport-ᵍ b p (g-inl d)          = g-inl (polys-transport-ᵍ b p d)
polys-transport-ᵍ b p (g-inr d)          = g-inr (polys-transport-ᵍ b p d)
polys-transport-ᵍ b p (g-In wf d)        = g-In wf (polys-transport-ᵍ b p d)

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
  polys-transport-ᵢ b p pib ac (t-float i f l d ok) = t-float i f l d ok
  polys-transport-ᵢ b p pib ac (t-str s)  = t-str s
  polys-transport-ᵢ b p pib ac t-unit     = t-unit
  polys-transport-ᵢ b p pib ac t-unit-var = t-unit-var
  polys-transport-ᵢ b p pib ac (t-var-local ¬u lk) = t-var-local ¬u lk
  polys-transport-ᵢ b p pib ac (t-var-qualified imp conc) = t-var-qualified imp conc
  polys-transport-ᵢ b p pib ac (t-var-resolved imp conc) = t-var-resolved imp conc
  polys-transport-ᵢ b p pib ac (t-var-import ¬u lkn imp conc) = t-var-import ¬u lkn imp conc
  -- Plan 0.58 / D071: infer-mode ground telescope reference — same telescope
  -- descent as the check-mode `t-var-poly-instantiate` case below (the schema
  -- is canon-invariant, so the `isGround` and type-pin premises carry over).
  polys-transport-ᵢ b {i = i} p pib (acc rec) (t-var-poly-instantiate-infer {x = x} {body = body} {prefix = prefix} cb ¬u lln lin lp ig Teq d) =
    t-var-poly-instantiate-infer cb ¬u lln lin (lookupPolyPrefix-canon-just b p x lp) ig Teq
      (polys-transport-ᶜ b prefix (lookupPolyPrefix-PInB {p} {b} x lp pib)
         (rec (lookupPolyPrefix-decreases x p lp))
         (canon-pres-ᶜ {ctx = ctxWithImportsAndPolys i prefix} b
           (⊆ᵇ-nil {b}) (mkPIB (lookupPolyPrefix-PInB {p} {b} x lp pib)) d))
  polys-transport-ᵢ b p pib ac (t-annot d) = t-annot (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-pair d₁ d₂) = t-pair (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-neg d) = t-neg (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-let d₁ d₂) = t-let (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-case ds dL dR) =
    t-case (polys-transport-ᵢ b p pib ac ds) (polys-transport-ᵢ b p pib ac dL) (polys-transport-ᵢ b p pib ac dR)
  polys-transport-ᵢ b p pib ac (t-binop-arith pr d₁ d₂) = t-binop-arith pr (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-binop-cmp pr d₁ d₂) = t-binop-cmp pr (polys-transport-ᵢ b p pib ac d₁) (polys-transport-ᵢ b p pib ac d₂)
  polys-transport-ᵢ b p pib ac (t-id-app d) = t-id-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-fst-app d) = t-fst-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-snd-app d) = t-snd-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-terminal-app d) = t-terminal-app (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-apply-app-infer d) = t-apply-app-infer (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᵢ b p pib ac (t-app cls df dx) = t-app cls (polys-transport-ᵢ b p pib ac df) (polys-transport-ᶜ b p pib ac dx)
  polys-transport-ᵢ b p pib ac (t-effApp cls df dx) = t-effApp cls (polys-transport-ᵢ b p pib ac df) (polys-transport-ᶜ b p pib ac dx)

  polys-transport-ᵐ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → Acc _<_ (length p) → ∀ {e A π B}
    → mkCtx n Γ Δ f i p s ⊢ᵐ e ∶ A ⇨[ π ] B
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᵐ e ∶ A ⇨[ π ] B
  polys-transport-ᵐ b p pib ac (m-id ll li) = m-id ll li
  polys-transport-ᵐ b p pib ac (m-fst ll li) = m-fst ll li
  polys-transport-ᵐ b p pib ac (m-snd ll li) = m-snd ll li
  polys-transport-ᵐ b p pib ac (m-terminal ll li) = m-terminal ll li
  polys-transport-ᵐ b p pib ac (m-initial ll li) = m-initial ll li
  polys-transport-ᵐ b p pib ac (m-inl ll li) = m-inl ll li
  polys-transport-ᵐ b p pib ac (m-inr ll li) = m-inr ll li
  polys-transport-ᵐ b {n = n} {Γ = Γ} {Δ = Δ} {f = fr} {i = i} {s = s} p pib ac
    (m-compose cm df dg) =
    m-compose (composeMid-polys-canon b (mkCtx n Γ Δ fr i p s) df dg cm)
              (polys-transport-ᵐ b p pib ac df) (polys-transport-ᵐ b p pib ac dg)
  polys-transport-ᵐ b p pib ac (m-case df dg) = m-case (polys-transport-ᵐ b p pib ac df) (polys-transport-ᵐ b p pib ac dg)
  polys-transport-ᵐ b p pib ac (m-pair df dg) = m-pair (polys-transport-ᵐ b p pib ac df) (polys-transport-ᵐ b p pib ac dg)
  polys-transport-ᵐ b p pib ac (m-curry df) = m-curry (polys-transport-ᵐ b p pib ac df)
  polys-transport-ᵐ b p pib ac (m-cata wf d) = m-cata wf (polys-transport-ᵐ b p pib ac d)
  polys-transport-ᵐ b p pib ac (m-const d) = m-const (polys-transport-ᵍ b p d)
  polys-transport-ᵐ b p pib ac (m-named ¬u lln imp bA cB) = m-named ¬u lln imp bA cB
  polys-transport-ᵐ b p pib ac (m-named-resolved imp bA cB) = m-named-resolved imp bA cB

  polys-transport-ᶜ : ∀ (b : List String) {n Γ Δ f i s} (p : PolyCtx) → PInB p b → Acc _<_ (length p) → ∀ {e A Ψ}
    → mkCtx n Γ Δ f i p s ⊢ᶜ e ∶ A ⨾ Ψ
    → mkCtx n Γ Δ f i (canonPolysCtx b p) s ⊢ᶜ e ∶ A ⨾ Ψ
  polys-transport-ᶜ b p pib ac (t-morph-lift d) = t-morph-lift (polys-transport-ᵐ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-embed d) = t-embed (polys-transport-ᵢ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-subsume d) = t-subsume (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-lam le d) = t-lam le (polys-transport-ᶜ b p pib ac d)
  polys-transport-ᶜ b p pib ac (t-value-lift d) = t-value-lift (polys-transport-ᵍ b p d)
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
  polys-transport-ᶜ b {i = i} p pib (acc rec) (t-var-poly-instantiate {x = x} {T = T} {body = body} {prefix = prefix} cb ¬u lln lin lp ig d) =
    t-var-poly-instantiate cb ¬u lln lin (lookupPolyPrefix-canon-just b p x lp) ig
      (polys-transport-ᶜ b prefix (lookupPolyPrefix-PInB {p} {b} x lp pib)
         (rec (lookupPolyPrefix-decreases x p lp))
         (canon-pres-ᶜ {ctx = ctxWithImportsAndPolys i prefix} b
           (⊆ᵇ-nil {b}) (mkPIB (lookupPolyPrefix-PInB {p} {b} x lp pib)) d))
