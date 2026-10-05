-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A SIGNATURE FROM SURFACE ENTRIES, checked.
--                      (PLAN-BIDI S7 — the Knot's machinery)
--
-- ★ IN: `size` surface entries, each a type and a body (holes allowed).
--   OUT: the signature `S` they denote, and — when everything checks —
--   `WfSig S` (`Metatheory/Signature`): every entry checked over its
--   prefix by the CERTIFYING checker.  On concrete entries it computes,
--   so a well-formedness proof is `fromJust (wfSig) _`: nobody writes or
--   generates a derivation.
--
-- ★ THE SIGNATURE IS A TELESCOPE (2026-10-05, `Spec/Signature`).  Entry
--   n is ELABORATED (untrusted) over the telescope of the entries before
--   it, then CHECKED (trusted, `CheckA`) over that same telescope; its
--   stored body is BY DEFINITION the erasure of its elaborated body there,
--   so the erasure equation of `EntryWf` is `refl` (the old builder decided
--   it with `_≟Tm_` against a different table).  The reference bound is a
--   decided Boolean.
--
-- ★ EXTENSION (`SigExtend`).  A module extends a signature built and
--   checked in another: `WfSig (S ▸ˢ e)` is `WfSig S × EntryWf S e`
--   definitionally, so the base's proof is REUSED, not recomputed — the
--   Knot is checked in segments.  `SigBuild` is extension of the empty
--   signature.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_; _×_; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( ε; RTm; nzero )
open import DirectedHoTT.Spec.Typing using ( c-◇ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature using ( Sig; Entry; ⟨_∣_⟩; len; _▸ˢ_; ∅ˢ )
open import DirectedHoTT.Metatheory.Signature using ( EntryWf; WfSig; wf→ok )
open import DirectedHoTT.Metatheory.SigBelow using ( below; belowᵀ )
open import DirectedHoTT.Algorithm.Surface using ( STy; STm )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟ℕ_ )
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Algorithm.Elab as E
open import DirectedHoTT.Algorithm.Result using ( R; ok; err; why )
open import Agda.Builtin.String using ( String; primStringAppend; primShowNat )
import DirectedHoTT.Algorithm.CheckA as CA
import DirectedHoTT.Metatheory.Erasure as Er

-- `size` new entries over a checked `base`: new entry i (i < size; its
-- absolute index — what a `ref` names — is `len base + i`) is declared
-- `tys i` with body `tms i`
module DirectedHoTT.Algorithm.SigBuild where

module SigExtend (base : Sig) (abase : ℕ → ATm ε) (wbase : WfSig base)
                 (size : ℕ) (tys : ℕ → STy ε) (tms : ℕ → STm ε) (fuel : ℕ) where

  private
    fromR : {A : Set} → A → R A → A
    fromR a (err _) = a
    fromR a (ok x)  = x

    -- extend a table below `n` by entry `n`
    ext : {A : Set} → ℕ → A → (ℕ → A) → ℕ → A
    ext n a f d with d ≟ℕ n
    ... | yes _ = a
    ... | no _  = f d

  -- the absolute index of new entry i
  ix : ℕ → ℕ
  ix i = len base + i

  ----------------------------------------------------------------------
  -- 1. The telescope, entry by entry: elaborated over the entries before.
  ----------------------------------------------------------------------

  sigAt   : ℕ → Sig
  abodyAt : ℕ → ℕ → ATm ε
  elabTyR : ℕ → R (ATy ε)
  elabTmR : ℕ → R (ATm ε)
  elabTy  : ℕ → ATy ε
  elabTm  : ℕ → ATm ε
  entryAt : ℕ → Entry

  elabTyR i = E.elT (sigAt i) (abodyAt i) fuel (λ ()) (tys i)
  elabTmR i = E.chk (sigAt i) (abodyAt i) fuel (λ ()) (tms i) (elabTy i)
  elabTy i = fromR Unit (elabTyR i)
  elabTm i = fromR nzero (elabTmR i)

  -- ★ the stored body IS the erasure of the elaborated one, over the
  --   telescope before it
  entryAt i = ⟨ elabTy i ∣ Era.⌈_⌉ (Sig.body (sigAt i)) (elabTm i) ⟩

  sigAt zero    = base
  sigAt (suc i) = sigAt i ▸ˢ entryAt i
  abodyAt zero    = abase
  abodyAt (suc i) = ext (ix i) (elabTm i) (abodyAt i)

  ----------------------------------------------------------------------
  -- 2. ★ The signature, and its well-formedness — CHECKED.
  ----------------------------------------------------------------------

  S : Sig
  S = sigAt size

  -- the annotated bodies (base entries from `abase`)
  abody : ℕ → ATm ε
  abody = abodyAt size

  -- why new entry i failed to ELABORATE ("ok" if it did) — read it off a
  -- type error: `why-entry 3 ≡ "ok"` by `refl`
  why-entry : ℕ → String
  why-entry i with elabTyR i
  ... | err w = primStringAppend "type › " w
  ... | ok _  = primStringAppend "body › " (why (elabTmR i))

  -- ★ NO `with` on the checker's verdicts: each is an ARGUMENT of a helper
  --   (memory: with-over-knot-contexts-ooms).
  private
    isTrue : {X : Set} (b : Bool) → String → (b ≡ true → R X) → R X
    isTrue true  m k = k refl
    isTrue false m k = err m

    module Chk (i : ℕ) (w : WfSig (sigAt i)) where
      Sᵢ = sigAt i
      wΓ = wf→ok Sᵢ w

      byBelow : TA._⊢ᴬ_∷_ Sᵢ TA.◇ᴬ (elabTm i) (elabTy i) → R (EntryWf Sᵢ (entryAt i))
      byBelow d =
        isTrue (below (len Sᵢ) (elabTm i)) "a reference in the body is not below the entry" λ bb →
        isTrue (belowᵀ (len Sᵢ) (elabTy i)) "a reference in the type is not below the entry" λ bt →
        ok (elabTm i , (d , (refl , (bb , bt))))

      byBody : Dec (TA._⊢ᴬ_∷_ Sᵢ TA.◇ᴬ (elabTm i) (elabTy i)) → R (EntryWf Sᵢ (entryAt i))
      byBody (yes d) = byBelow d
      byBody (no _)  = err (primStringAppend "the checker rejects the body › " (why-entry i))

      byType : Dec (TA._⊢tyᴬ_ Sᵢ TA.◇ᴬ (elabTy i)) → R (EntryWf Sᵢ (entryAt i))
      byType (yes dA) = byBody (CA.checkᴬ Sᵢ wΓ TA.◇ᴬ c-◇ (elabTm i) (elabTy i) (Er.erase-ty Sᵢ wΓ dA))
      byType (no _)   = err (primStringAppend "the checker rejects the type › " (why-entry i))

      entry : R (EntryWf Sᵢ (entryAt i))
      entry = byType (CA.checkTyᴬ Sᵢ wΓ TA.◇ᴬ c-◇ (elabTy i))

    next : (i : ℕ) → WfSig (sigAt i) → R (EntryWf (sigAt i) (entryAt i)) → R (WfSig (sigAt (suc i)))
    next i w (err w') = err (primStringAppend "entry " (primStringAppend (primShowNat (ix i)) (primStringAppend " › " w')))
    next i w (ok e)   = ok (w , e)

    step : (i : ℕ) → R (WfSig (sigAt i)) → R (WfSig (sigAt (suc i)))
    step i (err w) = err w
    step i (ok w)  = next i w (Chk.entry i w)

  wfAt : (i : ℕ) → R (WfSig (sigAt i))
  wfAt zero    = ok wbase
  wfAt (suc i) = step i (wfAt i)

  -- ★ the signature's well-formedness, when it holds — else the reason
  wfSig : R (WfSig S)
  wfSig = wfAt size

  -- for a concrete signature: `wf = fromJust wfSig _`
  IsJust : {A : Set} → R A → Set
  IsJust (ok _)  = ⊤
  IsJust (err _) = ⊥

  fromJust : {A : Set} (m : R A) → IsJust m → A
  fromJust (ok a) _ = a
  fromJust (err _)  ()

-- a signature from scratch: extension of the empty one
module SigBuild (size : ℕ) (tys : ℕ → STy ε) (tms : ℕ → STm ε) (fuel : ℕ) =
  SigExtend ∅ˢ (λ _ → nzero) tt size tys tms fuel
