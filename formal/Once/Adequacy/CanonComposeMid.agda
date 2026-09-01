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
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.Type using (Type)
open import Once.CanonicalName using (canonical; showCanonical)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr; isBuiltinName; elemStr)
open import Once.TypeCheck.Classify
  using (NamedCtx; composeArgB; domainOfHead; composeMid; composeMid-pick)
open import Once.Adequacy.CanonPreserve
  using (canon-builtin; canon-RVar-keep; canon-RVar-resolve)

------------------------------------------------------------------------
-- domainOfHead is canonExpr-invariant on ANY head.
--
-- `domainOfHead` only looks at `RVar`/`RResolved`; every other shape is
-- `nothing`, and `canonExpr` maps each of those shapes to itself. The named
-- case is the `showCanonical (canonical [x]) = x` coincidence, which holds
-- DEFINITIONALLY, so both branches of the keep/resolve dispatch are `refl`.
------------------------------------------------------------------------

domainOfHead-canon : ∀ (ctx : NamedCtx) (bound : List String) (f : RawExpr)
  → domainOfHead ctx (canonExpr bound [] [] f) ≡ domainOfHead ctx f
domainOfHead-canon ctx bound (Raw.RVar x)
  with elemStr x bound ∨ isBuiltinName x in eb
... | true  rewrite canon-RVar-keep    bound x eb = refl
... | false rewrite canon-RVar-resolve bound x eb = refl
domainOfHead-canon ctx bound (Raw.RQualified n al) = refl
domainOfHead-canon ctx bound (Raw.RResolved cn) = refl
domainOfHead-canon ctx bound (Raw.RApp f x) = refl
domainOfHead-canon ctx bound (Raw.RLam y b) = refl
domainOfHead-canon ctx bound (Raw.RLet y e₁ e₂) = refl
domainOfHead-canon ctx bound (Raw.RPair a b) = refl
domainOfHead-canon ctx bound (Raw.RDestruct s xl el xr er) = refl
domainOfHead-canon ctx bound Raw.RUnit = refl
domainOfHead-canon ctx bound (Raw.RInt n) = refl
domainOfHead-canon ctx bound (Raw.RFloat i f l p) = refl
domainOfHead-canon ctx bound (Raw.RStringLit s) = refl
domainOfHead-canon ctx bound (Raw.RAnnot e t) = refl
domainOfHead-canon ctx bound (Raw.RBinOp op a b) = refl
domainOfHead-canon ctx bound (Raw.RUnaryOp op e) = refl
domainOfHead-canon ctx bound (Raw.RAna F c) = refl

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

-- The RApp arm. Only `RApp (RApp (RVar "compose") f') g'` is meaningful to
-- `composeArgB`; every other head is `nothing` on both sides. Splitting the
-- inner head down to its constructor is what makes the literal pattern reduce.
composeArgB-canon : ∀ (ctx : NamedCtx) (bound : List String) (A : Type) (g : RawExpr)
  → composeArgB ctx (canonExpr bound [] [] g) A ≡ composeArgB ctx g A
composeArgB-canon ctx bound A (Raw.RVar x)
  with elemStr x bound ∨ isBuiltinName x in eb
... | true  rewrite canon-RVar-keep    bound x eb = refl
... | false rewrite canon-RVar-resolve bound x eb =
      composeArgB-RVar-resolved ctx x A (∨-false-r {x} eb)
composeArgB-canon ctx bound A (Raw.RQualified n al) = refl
composeArgB-canon ctx bound A (Raw.RResolved cn) = refl
-- The nested-compose head: `"compose"` is a builtin, so `canonExpr` keeps it
-- and the same clause fires on both sides; recurse into `g'` then `f'`.
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RVar x) f') g')
  with x ≟s "compose"
... | yes refl
      rewrite canon-builtin bound "compose" refl
      rewrite composeArgB-canon ctx bound A g'
      with composeArgB ctx g' A
...     | nothing = refl
...     | just B' rewrite composeArgB-canon ctx bound B' f' = refl
-- A non-`compose` head: both sides are `nothing`, whether the resolver kept
-- the name or resolved it (an `RResolved` head is not a nested compose at
-- all, so it falls straight to the catch-all).
--
-- The RIGHT side is already `nothing` in the goal: the `with` abstracted
-- `x ≟ "compose"`, which is the very term `Classify.composeArgB` is stuck on,
-- so the `no` pattern reduced it. The LEFT side is not — it only became an
-- `RVar`-headed application after `canon-RVar-keep`, i.e. after the
-- abstraction — so it takes `cab-RVar-nc` explicitly. Under the OLD literal
-- pattern neither side could be reduced at all.
-- (the LHS is repeated: the `yes` branch above opened a second `with`, so a
-- bare `...` here would be read at the wrong depth.)
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RVar x) f') g')
    | no ¬p with elemStr x bound ∨ isBuiltinName x in eb
...   | true  rewrite canon-RVar-keep    bound x eb =
          cab-RVar-nc ctx A x (canonExpr bound [] [] f') (canonExpr bound [] [] g') ¬p
...   | false rewrite canon-RVar-resolve bound x eb = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RApp a b) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RQualified n al) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RResolved cn) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RLam y b) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RLet y e₁ e₂) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RPair a b) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RDestruct s xl el xr er) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp Raw.RUnit f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RInt n) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RFloat i f l p) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RStringLit s) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RAnnot e t) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RBinOp op a b) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RUnaryOp op e) f') g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RApp (Raw.RAna F c) f') g') = refl
-- A one-argument application of a bare name: `nothing` on both sides, but the
-- left one is stuck on `canonVar`'s Bool until the keep/resolve split.
composeArgB-canon ctx bound A (Raw.RApp (Raw.RVar x) g')
  with elemStr x bound ∨ isBuiltinName x in eb
... | true  rewrite canon-RVar-keep    bound x eb = refl
... | false rewrite canon-RVar-resolve bound x eb = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RQualified n al) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RResolved cn) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RLam y b) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RLet y e₁ e₂) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RPair a b) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RDestruct s xl el xr er) g') = refl
composeArgB-canon ctx bound A (Raw.RApp Raw.RUnit g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RInt n) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RFloat i f l p) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RStringLit s) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RAnnot e t) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RBinOp op a b) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RUnaryOp op e) g') = refl
composeArgB-canon ctx bound A (Raw.RApp (Raw.RAna F c) g') = refl
composeArgB-canon ctx bound A (Raw.RLam y b) = refl
composeArgB-canon ctx bound A (Raw.RLet y e₁ e₂) = refl
composeArgB-canon ctx bound A (Raw.RPair a b) = refl
composeArgB-canon ctx bound A (Raw.RDestruct s xl el xr er) = refl
composeArgB-canon ctx bound A Raw.RUnit = refl
composeArgB-canon ctx bound A (Raw.RInt n) = refl
composeArgB-canon ctx bound A (Raw.RFloat i f l p) = refl
composeArgB-canon ctx bound A (Raw.RStringLit s) = refl
composeArgB-canon ctx bound A (Raw.RAnnot e t) = refl
composeArgB-canon ctx bound A (Raw.RBinOp op a b) = refl
composeArgB-canon ctx bound A (Raw.RUnaryOp op e) = refl
composeArgB-canon ctx bound A (Raw.RAna F c) = refl

------------------------------------------------------------------------
-- composeMid-canon: both components are canonExpr-invariant.
------------------------------------------------------------------------

composeMid-canon :
  ∀ {ctx : NamedCtx} {A B : Type} (bound : List String) (f g : RawExpr)
  → composeMid ctx f g A ≡ just B
  → composeMid ctx (canonExpr bound [] [] f) (canonExpr bound [] [] g) A ≡ just B
composeMid-canon {ctx} {A} bound f g eq
  rewrite composeArgB-canon ctx bound A g
  rewrite domainOfHead-canon ctx bound f = eq
