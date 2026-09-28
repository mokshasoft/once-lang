-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.PolysCheck — plan 0.103 phase 1: the declaration-time check
-- of ground telescope entries (`Compile.polysCheck`) is SOUND and
-- COMPLETE for `Spec.Module.EntriesTyped`.
------------------------------------------------------------------------

module Once.Adequacy.PolysCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
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
open import Once.Spec.Module using (PolyEntryTyped; EntriesTyped)

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

entry-sound : ∀ imps pfi tail (g : Ground (pfunType pfi))
  → C.polyEntryCheck imps (C.buildPolyCtx tail) pfi (inj₁ g) ≡ inj₂ tt
  → ctxWithImportsAndPolys imps (C.buildPolyCtx tail) ⊢ᶜ pfunBody pfi
      ∶ extractGround (pfunType pfi) g ⨾ zeroUsage
entry-sound imps pfi tail g h = check-ok-sound _ h

entry-sound-g : ∀ imps pfi tail (ig : Ground (pfunType pfi) ⊎ ⊤) → isGround (pfunType pfi) ≡ ig
  → C.polyEntryCheck imps (C.buildPolyCtx tail) pfi ig ≡ inj₂ tt
  → PolyEntryTyped imps pfi tail
entry-sound-g imps pfi tail ig eqG h g with trans (sym eqG) (isGround-complete-at (pfunType pfi) g)
... | refl = entry-sound imps pfi tail g h

polys-sound : ∀ at pfis → C.polysCheck at pfis ≡ inj₂ tt → EntriesTyped at pfis
polys-sound at []           _ = tt
polys-sound at (pfi ∷ pfis) h =
  entry-sound-g (at (pfunAfter pfi)) pfi pfis _ refl (seq-inj₂ˡ {a} h)
  , polys-sound at pfis (seq-inj₂ʳ {a} h)
  where a = C.polyEntryCheck (at (pfunAfter pfi)) (C.buildPolyCtx pfis) pfi (isGround (pfunType pfi))

------------------------------------------------------------------------
-- Completeness
------------------------------------------------------------------------

entry-complete : ∀ imps pfi tail → PolyEntryTyped imps pfi tail
  → C.polyEntryCheck imps (C.buildPolyCtx tail) pfi (isGround (pfunType pfi)) ≡ inj₂ tt
entry-complete imps pfi tail t with isGround (pfunType pfi)
... | inj₂ _ = refl
... | inj₁ g with check-completeV (t g)
...   | (_ , _ , _ , _ , eqV) rewrite eqV = refl

polys-complete : ∀ at pfis → EntriesTyped at pfis → C.polysCheck at pfis ≡ inj₂ tt
polys-complete at []           _        = refl
polys-complete at (pfi ∷ pfis) (t , ts) =
  seq-both (entry-complete (at (pfunAfter pfi)) pfi pfis t) (polys-complete at pfis ts)
