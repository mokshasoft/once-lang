-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.PolysCheck — plan 0.103 phase 1: the declaration-time check
-- of ground telescope entries (`Compile.polysWalkCheck`) is SOUND and
-- COMPLETE for `Spec.Module.PolysWalkTyped`.
------------------------------------------------------------------------

module Once.Adequacy.PolysCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Nat
import Data.String

open import Once.Type using (Type; PolyType; Ground; isGround; extractGround)
import Once.Compile as C
open C.PolyFunInfo using (pfunName; pfunType; pfunBody; pfunAfter)
open C.FunInfo using (funName; funType; funBody)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (lookupPolyPrefix; ctxWithImportsAndPolys; PolyCtx)
open import Once.TypeCheck.Elaborate using (checkElabV; success; failure)
open import Once.TypeCheck.Completeness using (check-completeV)
open import Once.TypeCheck.DeciderComplete using (isGround-complete-at)
open import Once.Surface.Context using (Usage; []; zeroUsage)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Spec.Module
  using (PolyDeclTyped; PolysTypedAt; PolysWalkTyped; PolysWalkStep)

------------------------------------------------------------------------
-- One entry
------------------------------------------------------------------------

private
  seq-inj₂ˡ : ∀ {a b} → C.seqCheck a b ≡ inj₂ tt → a ≡ inj₂ tt
  seq-inj₂ˡ {inj₂ tt} _ = refl
  seq-inj₂ˡ {inj₁ _} ()

  seq-inj₂ʳ : ∀ {a b} → C.seqCheck a b ≡ inj₂ tt → b ≡ inj₂ tt
  seq-inj₂ʳ {inj₂ tt} e = e
  seq-inj₂ʳ {inj₁ _} ()

  seq-both : ∀ {a b} → a ≡ inj₂ tt → b ≡ inj₂ tt → C.seqCheck a b ≡ inj₂ tt
  seq-both refl e = e

-- The check of one body in a CLEARED context (no locals): success is exactly
-- a derivation, at the only usage there is (`[]` = `zeroUsage`).
check-ok-sound : ∀ {imps prefix e T}
  (r : Once.TypeCheck.Elaborate.VerifiedCheckResult (ctxWithImportsAndPolys imps prefix) e T)
  → C.checkOK r ≡ inj₂ tt
  → ctxWithImportsAndPolys imps prefix ⊢ᶜ e ∶ T ⨾ zeroUsage
check-ok-sound (success [] _ _ _ , w) _ = w
check-ok-sound (failure _ , _) ()

decl-sound : ∀ ctx pctx pfi (g : Ground (pfunType pfi))
  → C.polyDeclCheck-g ctx pctx pfi (inj₁ g) ≡ inj₂ tt
  → Σ-syntax (PolyType × RawExpr × PolyCtx) (λ e →
      (lookupPolyPrefix pctx (pfunName pfi) ≡ just e)
      × (ctxWithImportsAndPolys ctx (proj₂ (proj₂ e)) ⊢ᶜ pfunBody pfi
           ∶ extractGround (pfunType pfi) g ⨾ zeroUsage))
decl-sound ctx pctx pfi g h with lookupPolyPrefix pctx (pfunName pfi) in eqL
... | just e = e , refl , check-ok-sound _ h
... | nothing with () ← h

pos-sound : ∀ ctx pctx r pfi (d : Dec (pfunAfter pfi ≡ r))
  → C.polyPosCheck ctx pctx r pfi d ≡ inj₂ tt
  → pfunAfter pfi ≡ r → PolyDeclTyped ctx pctx pfi
pos-sound ctx pctx r pfi (no ¬p) _ p = Data.Empty.⊥-elim (¬p p)
  where import Data.Empty
pos-sound ctx pctx r pfi (yes _) h _ g
  rewrite isGround-complete-at (pfunType pfi) g = decl-sound ctx pctx pfi g h

at-sound : ∀ ctx pctx r pfis → C.polysAtCheck ctx pctx r pfis ≡ inj₂ tt → PolysTypedAt ctx pctx r pfis
at-sound ctx pctx r []           _ = tt
at-sound ctx pctx r (pfi ∷ pfis) h =
  pos-sound ctx pctx r pfi d (seq-inj₂ˡ {C.polyPosCheck ctx pctx r pfi d} h)
  , at-sound ctx pctx r pfis (seq-inj₂ʳ {C.polyPosCheck ctx pctx r pfi d} h)
  where d = pfunAfter pfi Data.Nat.≟ r

walk-sound : ∀ funs ctx pctx pfis → C.polysWalkCheck funs ctx pctx pfis ≡ inj₂ tt → PolysWalkTyped funs ctx pctx pfis
step-sound : ∀ rest fi ctx pctx pfis (r : Data.String.String ⊎ Type)
  → C.polysWalkStep rest fi ctx pctx pfis r ≡ inj₂ tt → PolysWalkStep rest fi ctx pctx pfis r
walk-sound []          ctx pctx pfis h = at-sound ctx pctx zero pfis h
walk-sound (fi ∷ rest) ctx pctx pfis h =
  at-sound ctx pctx (suc (length rest)) pfis (seq-inj₂ˡ {a} h) ,
  step-sound rest fi ctx pctx pfis rf (seq-inj₂ʳ {a} h)
  where a  = C.polysAtCheck ctx pctx (suc (length rest)) pfis
        rf = C.resolveFunType ctx pctx (funType fi) (funBody fi)
step-sound rest fi ctx pctx pfis (inj₁ _)  _ = tt
step-sound rest fi ctx pctx pfis (inj₂ ty) h = walk-sound rest (C.extendFunCtx ctx (funName fi) ty) pctx pfis h

------------------------------------------------------------------------
-- Completeness
------------------------------------------------------------------------

decl-complete : ∀ ctx pctx pfi (g : Ground (pfunType pfi))
  → PolyDeclTyped ctx pctx pfi → C.polyDeclCheck-g ctx pctx pfi (inj₁ g) ≡ inj₂ tt
decl-complete ctx pctx pfi g t with t g
... | (e , eqL , w) rewrite eqL with check-completeV w
...   | (_ , _ , _ , _ , eqV) rewrite eqV = refl

pos-complete : ∀ ctx pctx r pfi (d : Dec (pfunAfter pfi ≡ r))
  → (pfunAfter pfi ≡ r → PolyDeclTyped ctx pctx pfi) → C.polyPosCheck ctx pctx r pfi d ≡ inj₂ tt
pos-complete ctx pctx r pfi (no _)  _ = refl
pos-complete ctx pctx r pfi (yes p) t with isGround (pfunType pfi)
... | inj₂ _ = refl
... | inj₁ g = decl-complete ctx pctx pfi g (t p)

at-complete : ∀ ctx pctx r pfis → PolysTypedAt ctx pctx r pfis → C.polysAtCheck ctx pctx r pfis ≡ inj₂ tt
at-complete ctx pctx r []           _        = refl
at-complete ctx pctx r (pfi ∷ pfis) (t , ts) =
  seq-both (pos-complete ctx pctx r pfi (pfunAfter pfi Data.Nat.≟ r) t) (at-complete ctx pctx r pfis ts)

walk-complete : ∀ funs ctx pctx pfis → PolysWalkTyped funs ctx pctx pfis → C.polysWalkCheck funs ctx pctx pfis ≡ inj₂ tt
step-complete : ∀ rest fi ctx pctx pfis (r : Data.String.String ⊎ Type)
  → PolysWalkStep rest fi ctx pctx pfis r → C.polysWalkStep rest fi ctx pctx pfis r ≡ inj₂ tt
walk-complete []          ctx pctx pfis t = at-complete ctx pctx zero pfis t
walk-complete (fi ∷ rest) ctx pctx pfis (t , s) =
  seq-both (at-complete ctx pctx (suc (length rest)) pfis t)
           (step-complete rest fi ctx pctx pfis (C.resolveFunType ctx pctx (funType fi) (funBody fi)) s)
step-complete rest fi ctx pctx pfis (inj₁ _)  _ = refl
step-complete rest fi ctx pctx pfis (inj₂ ty) s = walk-complete rest (C.extendFunCtx ctx (funName fi) ty) pctx pfis s
