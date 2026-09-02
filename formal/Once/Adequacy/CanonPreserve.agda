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
open import Data.Product using (_,_; _×_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type)
open import Once.CanonicalName using (CanonicalName; canonical; showCanonical; generatorNS; gen; GenWord)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.Parser.Module.Resolve
  using (canonExpr; canonVar; isBuiltinName; elemStr; lookupUnaliased;
         isBuiltinName-sound; isBuiltinName-false; ¬GenWord-isBuiltinName)
open import Once.TypeCheck.Classify
  using (NamedCtx; lookupLocal; lookupLocal-go; extendNamedCtx; classifyAppHead)
open import Once.TypeCheck.Context using (Ctx; names; name)
open import Once.Surface.Syntax
  using () renaming (Ctx to SCtx; ∅ to S∅; _,_^_ to _S,_^_)

------------------------------------------------------------------------
-- canonExpr-RVar dispatch (import-free: um = am = []).
------------------------------------------------------------------------

-- D136: `canonExpr bound [] [] (RVar x) = canonVar (elemStr x bound)
-- (isBuiltinName x) nothing x` — a THREE-way decision on two booleans, so
-- three bridge lemmas rather than two. Only a LEXICAL BINDER keeps the bare
-- name now; a reserved word resolves into the generator namespace.
canon-RVar-keep : ∀ (bound : List String) (x : String) →
  elemStr x bound ≡ true →
  canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RVar x
canon-RVar-keep bound x eq rewrite eq = refl

canon-RVar-gen : ∀ (bound : List String) (x : String) →
  elemStr x bound ≡ false → isBuiltinName x ≡ true →
  canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RResolved (gen x)
canon-RVar-gen bound x eb eg rewrite eb rewrite eg = refl

canon-RVar-resolve : ∀ (bound : List String) (x : String) →
  elemStr x bound ≡ false → isBuiltinName x ≡ false →
  canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RResolved (canonical (x ∷ []))
canon-RVar-resolve bound x eb eg rewrite eb rewrite eg = refl

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

-- D136: `canon-builtin` is GONE. It said a builtin head SURVIVES `canonExpr`
-- as a bare name; the resolver now sends it to `RResolved (gen s)`, and the
-- rules that used it already conclude at that canonical head, so every use of
-- it was a no-op rewrite that simply deletes.

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

-- D136: the same argument-irrelevance, for a CANONICAL head. `canonExpr` is
-- the identity on `RResolved`, so only the argument moves — and the view's
-- applied-generator dispatch never reads it.
caHead-RApp-resolved-arg-irr : ∀ (cn : CanonicalName) (g g' : RawExpr)
  → classifyAppHead (Raw.RApp (Raw.RResolved cn) g)
    ≡ classifyAppHead (Raw.RApp (Raw.RResolved cn) g')
caHead-RApp-resolved-arg-irr (canonical [])                g g' = refl
caHead-RApp-resolved-arg-irr (canonical (_ ∷ []))          g g' = refl
caHead-RApp-resolved-arg-irr (canonical (_ ∷ _ ∷ _ ∷ _))   g g' = refl
caHead-RApp-resolved-arg-irr (canonical (ns ∷ n ∷ [])) g g' with ns ≟s generatorNS
... | no _ = refl
... | yes refl with n ≟s "pair"
...   | yes refl = refl
...   | no _ with n ≟s "compose"
...     | yes refl = refl
...     | no _ with n ≟s "case"
...       | yes refl = refl
...       | no _ = refl

-- D136: `classifyAppHead` survives resolution only for a head the resolver
-- does not CLAIM. A bare reserved word IS claimed — it becomes
-- `RResolved (gen x)`, which classifies — so preservation needs to know the
-- head is either a lexical binder or not a reserved word. That is exactly what
-- a derivation of the head supplies (`t-var-local` ⇒ bound, `t-var-import` ⇒
-- `¬ GenWord x` by its own premise), and `head-unclaimed` extracts it.
-- D136: "the resolver does not CLAIM this name" — either a lexical binder
-- keeps it bare, or it is not a reserved word. Shared by every lemma that has
-- to know which of `canonVar`'s three arms fires.
NameOK : List String → String → Set
NameOK bound x =
  (elemStr x bound ≡ true) ⊎ (elemStr x bound ≡ false × isBuiltinName x ≡ false)

-- The rule premise `¬ GenWord x` gives it, whatever `bound` says. Written with
-- an explicit boolean parameter rather than a `with`: a `with` would abstract
-- `elemStr x bound` in the RESULT type too, and `inj₁ eb` would then be asked
-- for `true ≡ true`.
nameOK-of : ∀ (bound : List String) (x : String) → ¬ GenWord x → NameOK bound x
nameOK-of bound x ¬gw = go (elemStr x bound) refl
  where
    go : ∀ (b : Bool) → elemStr x bound ≡ b → NameOK bound x
    go true  eb = inj₁ eb
    go false eb = inj₂ (eb , ¬GenWord-isBuiltinName x ¬gw)

-- The two alternatives are MUTUALLY EXCLUSIVE on purpose: each one names the
-- decision `canonVar` makes, so the bridge lemmas rewrite without a `with`
-- (a `with` here abstracts `elemStr x bound` in the goal but not in the
-- lemma's statement, and the rewrite then fails to fire).
HeadUnclaimed : List String → RawExpr → Set
HeadUnclaimed bound (Raw.RVar x) = NameOK bound x
HeadUnclaimed bound (Raw.RApp (Raw.RVar x) _) = NameOK bound x
HeadUnclaimed bound _ = ⊤

classify-canon : ∀ (bound : List String) (f : RawExpr) → HeadUnclaimed bound f →
  classifyAppHead f ≡ nothing → classifyAppHead (canonExpr bound [] [] f) ≡ nothing
classify-canon bound (Raw.RVar x) (inj₁ eb) h
  rewrite canon-RVar-keep bound x eb = h
classify-canon bound (Raw.RVar x) (inj₂ (eb , eg)) h
  rewrite canon-RVar-resolve bound x eb eg = refl
classify-canon bound (Raw.RApp (Raw.RVar x) g) (inj₁ eb) h
  rewrite canon-RVar-keep bound x eb = trans (caHead-RApp-arg-irr x (canonExpr bound [] [] g) g) h
classify-canon bound (Raw.RApp (Raw.RVar x) g) (inj₂ (eb , eg)) h
  rewrite canon-RVar-resolve bound x eb eg = refl
classify-canon bound (Raw.RApp (Raw.RApp a b) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RQualified n al) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RResolved cn) g) _ h =
  trans (caHead-RApp-resolved-arg-irr cn (canonExpr bound [] [] g) g) h
classify-canon bound (Raw.RApp (Raw.RLam y b) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RLet y e₁ e₂) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RPair a b) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RDestruct s xl el xr er) g) _ h = refl
classify-canon bound (Raw.RApp Raw.RUnit g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RInt n) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RFloat i f l _) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RStringLit s) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RAnnot e t) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RBinOp op a b) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RUnaryOp op e) g) _ h = refl
classify-canon bound (Raw.RApp (Raw.RAna F c) g) _ h = refl
classify-canon bound (Raw.RQualified n al) _ h = refl
classify-canon bound (Raw.RResolved cn) _ h = h
classify-canon bound (Raw.RLam y b) _ h = refl
classify-canon bound (Raw.RLet y e₁ e₂) _ h = refl
classify-canon bound (Raw.RPair a b) _ h = refl
classify-canon bound (Raw.RDestruct s xl el xr er) _ h = refl
classify-canon bound Raw.RUnit _ h = refl
classify-canon bound (Raw.RInt n) _ h = refl
classify-canon bound (Raw.RFloat i f l _) _ h = refl
classify-canon bound (Raw.RStringLit s) _ h = refl
classify-canon bound (Raw.RAnnot e t) _ h = refl
classify-canon bound (Raw.RBinOp op a b) _ h = refl
classify-canon bound (Raw.RUnaryOp op e) _ h = refl
classify-canon bound (Raw.RAna F c) _ h = refl

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

-- D127: `pres-ᵍ` (value-judgment preservation) is GONE with the `⊢ᵍ` realm.
-- Its only two consumers were `CanonPreserveMutual`'s `m-const` and
-- `t-value-lift` clauses, and both rules were deleted in phase A.
