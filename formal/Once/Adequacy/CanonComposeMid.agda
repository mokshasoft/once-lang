-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonComposeMid — discharge of `composeMid-canon` (the lone
-- deferred hole of `CanonPreserveMutual`'s Step-2 `t-compose-check` case).
--
-- `composeMid ctx f g A = composeMid-pick (composeArgB ctx g A) (domainOfHead ctx f)`
-- is INVARIANT under `canonExpr` on the compose arms.
--
-- D127: the arms are now ORDINARY `⊢ᶜ` terms, so the old proof — case on the
-- `⊢ᵐ` derivation, which enumerated the seven-or-so head forms a morphism could
-- have — no longer has a closed set of cases to enumerate. It does not need
-- one: `domainOfHead` and `composeArgB` are functions of the RAW SYNTAX alone,
-- and so is `canonExpr`. Both lemmas are therefore PREMISE-FREE structural
-- inductions on `RawExpr`, in the same shape as `CanonPreserve.classify-canon`
-- (which had already made this move for `classifyAppHead`).
--
-- Dropping the typing premise is a strengthening, not a workaround: the old
-- statement was restricted to well-typed morphism arms purely because casing a
-- derivation was the only way to make the literal patterns in `composeArgB`
-- reduce, and the restriction is exactly what would have made the lemma
-- unusable now ([[feedback_restricted_lemma_hides_defect]]).
--
-- The one thing the syntax must be shown to respect is SHAPE: `canonExpr`
-- rewrites names, so it can neither create nor destroy the nested-`compose`
-- head pattern `RApp (RApp (RVar "compose") f') g'` — an `RVar` only ever
-- canonicalizes to an `RVar` or an `RResolved`, and `"compose"` is a builtin,
-- hence kept. That is what the RApp case-split below is enumerating.
------------------------------------------------------------------------

module Once.Adequacy.CanonComposeMid where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.Type using (Type)
open import Once.CanonicalName using (canonical; showCanonical; gen; _≟ᶜ_)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr; isBuiltinName; elemStr)
open import Once.TypeCheck.Classify
  using (NamedCtx; composeArgB; domainOfHead; composeMid; composeMid-pick)
open import Once.Adequacy.CanonPreserve
  using (canon-RVar-keep; canon-RVar-gen; canon-RVar-resolve)

------------------------------------------------------------------------
-- domainOfHead is canonExpr-invariant on ANY head.
--
-- `domainOfHead` only looks at `RVar`/`RResolved`; every other shape is
-- `nothing`, and `canonExpr` maps each of those shapes to itself. The named
-- case is the `showCanonical (canonical [x]) = x` coincidence, which holds
-- DEFINITIONALLY, so both branches of the keep/resolve dispatch are `refl`.
------------------------------------------------------------------------

-- D136: a name the resolver CLAIMS changes the lookup key ("fst" becomes
-- "Generators.fst"), so head-domain invariance holds exactly for the names it
-- does not claim. `NameOK` is that condition, split so each alternative names
-- the decision `canonVar` makes (a `with` here would abstract `elemStr x
-- bound` in the goal but not in the bridge lemma, and the rewrite would not
-- fire).
NameOK : List String → String → Set
NameOK bound x =
  (elemStr x bound ≡ true) ⊎ (elemStr x bound ≡ false × isBuiltinName x ≡ false)

DohOK : List String → RawExpr → Set
DohOK bound (Raw.RVar x) = NameOK bound x
DohOK bound _ = ⊤

domainOfHead-canon : ∀ (ctx : NamedCtx) (bound : List String) (f : RawExpr)
  → DohOK bound f
  → domainOfHead ctx (canonExpr bound [] [] f) ≡ domainOfHead ctx f
domainOfHead-canon ctx bound (Raw.RVar x) (inj₁ eb)
  rewrite canon-RVar-keep bound x eb = refl
domainOfHead-canon ctx bound (Raw.RVar x) (inj₂ (eb , eg))
  rewrite canon-RVar-resolve bound x eb eg = refl
domainOfHead-canon ctx bound (Raw.RQualified n al) _ = refl
domainOfHead-canon ctx bound (Raw.RResolved cn) _ = refl
domainOfHead-canon ctx bound (Raw.RApp f x) _ = refl
domainOfHead-canon ctx bound (Raw.RLam y b) _ = refl
domainOfHead-canon ctx bound (Raw.RLet y e₁ e₂) _ = refl
domainOfHead-canon ctx bound (Raw.RPair a b) _ = refl
domainOfHead-canon ctx bound (Raw.RDestruct s xl el xr er) _ = refl
domainOfHead-canon ctx bound Raw.RUnit _ = refl
domainOfHead-canon ctx bound (Raw.RInt n) _ = refl
domainOfHead-canon ctx bound (Raw.RFloat i f l p) _ = refl
domainOfHead-canon ctx bound (Raw.RStringLit s) _ = refl
domainOfHead-canon ctx bound (Raw.RAnnot e t) _ = refl
domainOfHead-canon ctx bound (Raw.RBinOp op a b) _ = refl
domainOfHead-canon ctx bound (Raw.RUnaryOp op e) _ = refl
domainOfHead-canon ctx bound (Raw.RAna F c) _ = refl

------------------------------------------------------------------------
-- composeArgB is canonExpr-invariant on ANY arm.
------------------------------------------------------------------------

-- For a NON-builtin name, the resolver's `RVar x → RResolved (canonical [x])`
-- leaves `composeArgB` unchanged: both reduce to `composeArgB-lookup ctx x A` —
-- the RResolved clause directly (`showCanonical (canonical [x]) = x`), the RVar one
-- after the `≟`-dispatch skips fst/snd/id/terminal (ruled out by `isBuiltinName`).
t≢f : true ≡ false → ⊥
t≢f ()

composeArgB-RVar-resolved :
  ∀ (ctx : NamedCtx) (y : String) (A : Type) → isBuiltinName y ≡ false
  → composeArgB ctx (Raw.RResolved (canonical (y ∷ []))) A ≡ composeArgB ctx (Raw.RVar y) A
composeArgB-RVar-resolved ctx y A nb with y ≟s "fst"
... | yes refl = ⊥-elim (t≢f nb)
... | no _ with y ≟s "snd"
...   | yes refl = ⊥-elim (t≢f nb)
...   | no _ with y ≟s "id"
...     | yes refl = ⊥-elim (t≢f nb)
...     | no _ with y ≟s "terminal"
...       | yes refl = ⊥-elim (t≢f nb)
...       | no _ = refl

∨-false-r : ∀ {x : String} {a : Bool} → (a ∨ isBuiltinName x) ≡ false → isBuiltinName x ≡ false
∨-false-r {a = false} e = e
∨-false-r {a = true}  ()

-- `composeArgB` on an application whose head name is NOT `compose`.
cab-RVar-nc : ∀ (ctx : NamedCtx) (A : Type) (x : String) (f' g' : RawExpr)
  → ¬ (x ≡ "compose")
  → composeArgB ctx (Raw.RApp (Raw.RApp (Raw.RVar x) f') g') A ≡ nothing
cab-RVar-nc ctx A x f' g' ¬p with x ≟s "compose"
... | yes p = ⊥-elim (¬p p)
... | no  _ = refl

-- D136: resolution CHANGES `composeArgB` on a bare reserved word — that is the
-- point of the plan — so invariance holds exactly for the arms the resolver
-- does not claim. `CabOK` names that condition at the positions `composeArgB`
-- actually inspects: the arm's own head, and (recursively) the arms of a
-- nested compose, which is now recognised only at a CANONICAL head.
CabOK : List String → RawExpr → Set
CabOK bound (Raw.RVar x) = NameOK bound x
CabOK bound (Raw.RApp (Raw.RApp (Raw.RVar z) f') g') = NameOK bound z
CabOK bound (Raw.RApp (Raw.RApp (Raw.RResolved cn) f') g') =
  CabOK bound f' × CabOK bound g'
CabOK bound _ = ⊤

-- An own-module head `canonical [x]` is not the canonical `compose` — they
-- differ in LENGTH — so the resolved side is `nothing` too. The `≟ᶜ` has to be
-- forced explicitly; it does not reduce on an abstract `x`.
cab-own-nc : ∀ (ctx : NamedCtx) (A : Type) (x : String) (f' g' : RawExpr)
  → composeArgB ctx (Raw.RApp (Raw.RApp (Raw.RResolved (canonical (x ∷ []))) f') g') A ≡ nothing
cab-own-nc ctx A x f' g' with canonical (x ∷ []) ≟ᶜ gen "compose"
... | yes ()
... | no _ = refl

-- The RApp arm. Only a canonical `compose` head is meaningful to
-- `composeArgB`; every other head is `nothing` on both sides. Splitting the
-- inner head down to its constructor is what makes the literal pattern reduce.
composeArgB-canon : ∀ (ctx : NamedCtx) (bound : List String) (A : Type) (g : RawExpr)
  → CabOK bound g
  → composeArgB ctx (canonExpr bound [] [] g) A ≡ composeArgB ctx g A
composeArgB-canon ctx bound A (Raw.RVar x) (inj₁ eb)
  rewrite canon-RVar-keep bound x eb = refl
composeArgB-canon ctx bound A (Raw.RVar x) (inj₂ (eb , eg))
  rewrite canon-RVar-resolve bound x eb eg = refl
composeArgB-canon ctx bound A (Raw.RQualified n al) _ = refl
composeArgB-canon ctx bound A (Raw.RResolved cn) _ = refl
-- D136: a BARE head is `nothing` on the right (the clause that recognised it
-- is gone), and the premise keeps the resolver from turning it into the
-- canonical `compose` on the left.
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RVar x) f') g') (inj₁ eb)
  rewrite canon-RVar-keep bound x eb = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RVar x) f') g') (inj₂ (eb , eg))
  rewrite canon-RVar-resolve bound x eb eg =
    cab-own-nc ctx A x (canonExpr bound [] [] f') (canonExpr bound [] [] g')
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RApp a b) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RQualified n al) f') g') _ = refl
-- The canonical `compose` head: unchanged by `canonExpr`, so both sides take
-- the same clause and the recursion is the two arms'.
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RResolved cn) f') g') (cf , cg)
  with cn ≟ᶜ gen "compose"
... | no _ = refl
... | yes _ rewrite composeArgB-canon ctx bound A g' cg with composeArgB ctx g' A
...   | nothing = refl
...   | just B' rewrite composeArgB-canon ctx bound B' f' cf = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RLam y b) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RLet y e₁ e₂) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RPair a b) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RDestruct s xl el xr er) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp Raw.RUnit f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RInt n) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RFloat i f l p) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RStringLit s) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RAnnot e t) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RBinOp op a b) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RUnaryOp op e) f') g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RAna F c) f') g') _ = refl
-- A one-argument application of a bare name: `nothing` on both sides, but the
-- left one is stuck on `canonVar`'s Bool until the keep/resolve split.
composeArgB-canon ctx bound A (Raw.RApp (Raw.RVar x) g') _
  with elemStr x bound in eb
... | true  rewrite canon-RVar-keep bound x eb = refl
... | false with isBuiltinName x in eg
...   | true  rewrite canon-RVar-gen     bound x eb eg = refl
...   | false rewrite canon-RVar-resolve bound x eb eg = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RQualified n al) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RResolved cn) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RLam y b) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RLet y e₁ e₂) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RPair a b) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RDestruct s xl el xr er) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp Raw.RUnit g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RInt n) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RFloat i f l p) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RStringLit s) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RAnnot e t) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RBinOp op a b) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RUnaryOp op e) g') _ = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RAna F c) g') _ = refl
-- D135: `composeArgB` now looks INSIDE a `RLam` (a written constant function's
-- codomain is its body's type), so the body has to be exposed for either side
-- to reduce. `canonExpr` preserves the body's head constructor, so every case
-- is `refl` — except a bare `RVar` body, which stays stuck until the
-- keep/resolve dispatch, and is `nothing` either way (neither an `RVar` nor an
-- `RResolved` body is a literal).
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RVar x)) _
  with elemStr x (y ∷ bound) in eb
... | true  rewrite canon-RVar-keep (y ∷ bound) x eb = refl
... | false with isBuiltinName x in eg
...   | true  rewrite canon-RVar-gen     (y ∷ bound) x eb eg = refl
...   | false rewrite canon-RVar-resolve (y ∷ bound) x eb eg = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RQualified n al)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RResolved cn)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RApp a c)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RLam z c)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RLet z e₁ e₂)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RPair a c)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RDestruct sc xl el xr er)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y Raw.RUnit) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RInt n)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RFloat i fp l q)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RStringLit str)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RAnnot e t)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RBinOp op a c)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RUnaryOp op e)) _ = refl
composeArgB-canon ctx bound A (Raw.RLam y (Raw.RAna F c)) _ = refl
composeArgB-canon ctx bound A (Raw.RLet y e₁ e₂) _ = refl
composeArgB-canon ctx bound A (Raw.RPair a b) _ = refl
composeArgB-canon ctx bound A (Raw.RDestruct s xl el xr er) _ = refl
composeArgB-canon ctx bound A Raw.RUnit _ = refl
composeArgB-canon ctx bound A (Raw.RInt n) _ = refl
composeArgB-canon ctx bound A (Raw.RFloat i f l p) _ = refl
composeArgB-canon ctx bound A (Raw.RStringLit s) _ = refl
composeArgB-canon ctx bound A (Raw.RAnnot e t) _ = refl
composeArgB-canon ctx bound A (Raw.RBinOp op a b) _ = refl
composeArgB-canon ctx bound A (Raw.RUnaryOp op e) _ = refl
composeArgB-canon ctx bound A (Raw.RAna F c) _ = refl

------------------------------------------------------------------------
-- composeMid-canon: both components are canonExpr-invariant.
------------------------------------------------------------------------

composeMid-canon :
  ∀ {ctx : NamedCtx} {A B : Type} (bound : List String) (f g : RawExpr)
  → DohOK bound f → CabOK bound g
  → composeMid ctx f g A ≡ just B
  → composeMid ctx (canonExpr bound [] [] f) (canonExpr bound [] [] g) A ≡ just B
composeMid-canon {ctx} {A} bound f g cf cg eq
  rewrite composeArgB-canon ctx bound A g cg
  rewrite domainOfHead-canon ctx bound f cf = eq
