-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonPreserve — Plan 0.51 discharge (import-free fragment).
-- `canonExpr [] []` (the resolver's own-module canonicalization, RVar x →
-- RResolved (canonical [x]) for free non-builtin x) PRESERVES the declarative
-- typing judgment `⊢ᶜ`. Foundational layer: the bound/local agreement invariant
-- `BLA`, the canonExpr-RVar dispatch facts, and `classify-canon`.
------------------------------------------------------------------------

module Once.Adequacy.CanonPreserve where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type)
open import Once.CanonicalName using (CanonicalName; canonical; showCanonical)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.Parser.Module.Resolve
  using (canonExpr; canonVar; isBuiltinName; elemStr; lookupUnaliased)
open import Once.TypeCheck.Classify
  using (NamedCtx; lookupLocal; lookupLocal-go; extendNamedCtx; classifyAppHead)
open import Once.TypeCheck.Judgment
  using (_⊢ᵍ_∶_; g-int; g-terminal; g-pair; g-inl; g-inr; g-In)
open import Once.TypeCheck.Context using (Ctx; names; name)
open import Once.Surface.Syntax
  using () renaming (Ctx to SCtx; ∅ to S∅; _,_^_ to _S,_^_)

------------------------------------------------------------------------
-- canonExpr-RVar dispatch (import-free: um = am = []).
------------------------------------------------------------------------

-- canonExpr bound [] [] (RVar x) = canonVar (elemStr x bound ∨ isBuiltinName x)
--   (lookupUnaliased [] x = nothing) x  — so it dispatches on the head Bool.
canon-RVar-keep : ∀ (bound : List String) (x : String) →
  (elemStr x bound ∨ isBuiltinName x) ≡ true →
  canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RVar x
canon-RVar-keep bound x eq rewrite eq = refl

canon-RVar-resolve : ∀ (bound : List String) (x : String) →
  (elemStr x bound ∨ isBuiltinName x) ≡ false →
  canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RResolved (canonical (x ∷ []))
canon-RVar-resolve bound x eq rewrite eq = refl

------------------------------------------------------------------------
-- `bound` is taken to be `names (named ctx)` everywhere (so binder cases are
-- DEFINITIONAL: names (extend ctx x A) = x ∷ names (named ctx)). The only fact
-- the var case needs is: a name found locally is in `names` — proven by direct
-- induction on the `Ctx` (where the `with x ≟ name b` DOES drive both
-- `lookupLocal-go` and `elemStr`, since the binder is applied directly).
------------------------------------------------------------------------

-- lookupLocal-go found ⇒ the name is in the context's `names`.
llg-just→elem : ∀ {m} (x : String) (Γ : Ctx) (Δ : SCtx m) {r} →
  lookupLocal-go x Γ Δ ≡ just r → elemStr x (names Γ) ≡ true
llg-just→elem x [] S∅ ()
llg-just→elem x [] (_ S, _ ^ _) ()
llg-just→elem x (_ ∷ _) S∅ ()
llg-just→elem x (b ∷ Γ') (Δ' S, B ^ q) h with x ≟s name b
... | yes _ = refl
... | no _ with lookupLocal-go x Γ' Δ' in eq2
...   | just r' = llg-just→elem x Γ' Δ' eq2

lookup-just→elem : ∀ (ctx : NamedCtx) (x : String) {r} →
  lookupLocal ctx x ≡ just r → elemStr x (names (NamedCtx.named ctx)) ≡ true
lookup-just→elem ctx x h = llg-just→elem x (NamedCtx.named ctx) (NamedCtx.debruijn ctx) h

------------------------------------------------------------------------
-- canonExpr keeps every builtin head, so classifyAppHead is preserved.
------------------------------------------------------------------------

∨-true : ∀ (b : Bool) → b ∨ true ≡ true
∨-true true  = refl
∨-true false = refl

canon-builtin : ∀ (bound : List String) (s : String) → isBuiltinName s ≡ true →
  canonExpr bound [] [] (Raw.RVar s) ≡ Raw.RVar s
canon-builtin bound s eq = canon-RVar-keep bound s lem
  where lem : (elemStr s bound ∨ isBuiltinName s) ≡ true
        lem rewrite eq = ∨-true (elemStr s bound)

-- Plan 0.52 (OCP-0008 classifier flatten): `classifyAppHead` is now
-- `viewToPba ∘ classifyAppHeadView`, so for an `RApp (RVar x) _` head its stuck
-- neutral form mentions the argument (the view's applied constructors carry it),
-- even though the result ignores it. This lemma restores argument-irrelevance,
-- which `classify-canon`'s keep-branch relies on (arg g vs canonExpr g).
caHead-RApp-arg-irr : ∀ (x : String) (g g' : RawExpr)
  → classifyAppHead (Raw.RApp (Raw.RVar x) g) ≡ classifyAppHead (Raw.RApp (Raw.RVar x) g')
caHead-RApp-arg-irr x g g' with x ≟s "pair"
... | yes refl = refl
... | no _ with x ≟s "compose"
...   | yes refl = refl
...   | no _ with x ≟s "case"
...     | yes refl = refl
...     | no _ = refl

classify-canon : ∀ (bound : List String) (f : RawExpr) →
  classifyAppHead f ≡ nothing → classifyAppHead (canonExpr bound [] [] f) ≡ nothing
classify-canon bound (Raw.RVar x) h with elemStr x bound ∨ isBuiltinName x in eb
... | true  rewrite canon-RVar-keep bound x eb = h
... | false rewrite canon-RVar-resolve bound x eb = refl
classify-canon bound (Raw.RApp (Raw.RVar x) g) h with elemStr x bound ∨ isBuiltinName x in eb
... | true  rewrite canon-RVar-keep bound x eb = trans (caHead-RApp-arg-irr x (canonExpr bound [] [] g) g) h
... | false rewrite canon-RVar-resolve bound x eb = refl
classify-canon bound (Raw.RApp (Raw.RApp a b) g) h = refl
classify-canon bound (Raw.RApp (Raw.RQualified n al) g) h = refl
classify-canon bound (Raw.RApp (Raw.RResolved cn) g) h = refl
classify-canon bound (Raw.RApp (Raw.RLam y b) g) h = refl
classify-canon bound (Raw.RApp (Raw.RLet y e₁ e₂) g) h = refl
classify-canon bound (Raw.RApp (Raw.RPair a b) g) h = refl
classify-canon bound (Raw.RApp (Raw.RDestruct s xl el xr er) g) h = refl
classify-canon bound (Raw.RApp Raw.RUnit g) h = refl
classify-canon bound (Raw.RApp (Raw.RInt n) g) h = refl
classify-canon bound (Raw.RApp (Raw.RFloat i f l) g) h = refl
classify-canon bound (Raw.RApp (Raw.RStringLit s) g) h = refl
classify-canon bound (Raw.RApp (Raw.RAnnot e t) g) h = refl
classify-canon bound (Raw.RApp (Raw.RBinOp op a b) g) h = refl
classify-canon bound (Raw.RApp (Raw.RUnaryOp op e) g) h = refl
classify-canon bound (Raw.RApp (Raw.RAna F c) g) h = refl
classify-canon bound (Raw.RQualified n al) h = refl
classify-canon bound (Raw.RResolved cn) h = refl
classify-canon bound (Raw.RLam y b) h = refl
classify-canon bound (Raw.RLet y e₁ e₂) h = refl
classify-canon bound (Raw.RPair a b) h = refl
classify-canon bound (Raw.RDestruct s xl el xr er) h = refl
classify-canon bound Raw.RUnit h = refl
classify-canon bound (Raw.RInt n) h = refl
classify-canon bound (Raw.RFloat i f l) h = refl
classify-canon bound (Raw.RStringLit s) h = refl
classify-canon bound (Raw.RAnnot e t) h = refl
classify-canon bound (Raw.RBinOp op a b) h = refl
classify-canon bound (Raw.RUnaryOp op e) h = refl
classify-canon bound (Raw.RAna F c) h = refl

------------------------------------------------------------------------
-- Bound subset (a binder list grown by the resolver covers the context's
-- locals). `names(named ctx) ⊆ bound` is the only hypothesis the preservation
-- induction needs (so the cata-algebra context-reset is the vacuous `[] ⊆`).
------------------------------------------------------------------------

_⊆ᵇ_ : List String → List String → Set
b₁ ⊆ᵇ b₂ = ∀ y → elemStr y b₁ ≡ true → elemStr y b₂ ≡ true

elemStr-head : ∀ (x : String) (bound : List String) → elemStr x (x ∷ bound) ≡ true
elemStr-head x bound with x ≟s x
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

elemStr-tail : ∀ {y x : String} (bound : List String) → ¬ (y ≡ x) →
  elemStr y (x ∷ bound) ≡ elemStr y bound
elemStr-tail {y} {x} bound ¬p with y ≟s x
... | yes p = ⊥-elim (¬p p)
... | no _  = refl

⊆ᵇ-refl : ∀ {b} → b ⊆ᵇ b
⊆ᵇ-refl y h = h

⊆ᵇ-nil : ∀ {b} → [] ⊆ᵇ b
⊆ᵇ-nil y ()

⊆ᵇ-cons : ∀ {b₁ b₂} (x : String) → b₁ ⊆ᵇ b₂ → (x ∷ b₁) ⊆ᵇ (x ∷ b₂)
⊆ᵇ-cons {b₁} {b₂} x sub y h with y ≟s x
... | yes refl = refl
... | no ¬p    = sub y h

------------------------------------------------------------------------
-- Value-judgment preservation. `⊢ᵍ` is INDEPENDENT of the other judgments
-- (it recurses only into itself), and has no var-local / binder, so no bound
-- hypothesis is needed — every head is a builtin (kept) or structural.
------------------------------------------------------------------------

pres-ᵍ : ∀ {ctx e T} (bound : List String) →
  ctx ⊢ᵍ e ∶ T → ctx ⊢ᵍ canonExpr bound [] [] e ∶ T
pres-ᵍ bound (g-int n) = g-int n
pres-ᵍ bound (g-terminal lL lI) rewrite canon-builtin bound "terminal" refl = g-terminal lL lI
pres-ᵍ bound (g-pair d₁ d₂) = g-pair (pres-ᵍ bound d₁) (pres-ᵍ bound d₂)
pres-ᵍ bound (g-inl d) rewrite canon-builtin bound "inl" refl = g-inl (pres-ᵍ bound d)
pres-ᵍ bound (g-inr d) rewrite canon-builtin bound "inr" refl = g-inr (pres-ᵍ bound d)
pres-ᵍ bound (g-In wf d) rewrite canon-builtin bound "In" refl = g-In wf (pres-ᵍ bound d)
