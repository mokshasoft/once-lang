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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong; subst; Σ; _,_; _×_; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax using ( ε; RTm; nzero )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature using ( Sig; Entry; ⟨_∣_⟩; eBody; len; _▸ˢ_; ∅ˢ; kernel )
open import DirectedHoTT.Metatheory.Signature using ( EntryWf; WfSig; wf→K )
open import DirectedHoTT.Algorithm.NbE.Value using ( Tbl )
import DirectedHoTT.Algorithm.NbE.TblOK as TO
import DirectedHoTT.Algorithm.NbETable as NT
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

  -- ★ the stored body IS the erasure of the elaborated one
  entryAt i = ⟨ elabTy i ∣ ⌈ elabTm i ⌉ ⟩

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
    -- ★ PLAN-REF: the value table of the telescope so far, THREADED, so
    --   every entry is evaluated once per check.  It IS `mkTbl` of the
    --   prefix's kernel signature — definitionally, so the equation is
    --   `refl` at every step, and soundness is `mkTbl-ok`'s.
    module Chk (i : ℕ) (w : WfSig (sigAt i)) (t : Tbl) (teq : t ≡ NT.mkTbl (kernel (sigAt i))) where
      Sᵢ = sigAt i
      wK = wf→K Sᵢ w
      tok : TO.TblOK (kernel Sᵢ) t
      tok = subst (TO.TblOK (kernel Sᵢ)) (sym teq) (NT.mkTbl-ok (kernel Sᵢ))
      open import DirectedHoTT.Spec.Typing (kernel Sᵢ) (Sig.size Sᵢ) using ( c-◇ )

      byBody : TA._⊢tyᴬ_ Sᵢ TA.◇ᴬ (elabTy i) → Dec (TA._⊢ᴬ_∷_ Sᵢ TA.◇ᴬ (elabTm i) (elabTy i)) → R (EntryWf Sᵢ (entryAt i))
      byBody dA (yes d) = ok (elabTm i , (dA , (d , refl)))
      byBody dA (no _)  = err (primStringAppend "the checker rejects the body › " (why-entry i))

      byType : Dec (TA._⊢tyᴬ_ Sᵢ TA.◇ᴬ (elabTy i)) → R (EntryWf Sᵢ (entryAt i))
      byType (yes dA) = byBody dA (CA.checkᴬ Sᵢ wK t tok TA.◇ᴬ c-◇ (elabTm i) (elabTy i) (Er.erase-ty Sᵢ dA))
      byType (no _)   = err (primStringAppend "the checker rejects the type › " (why-entry i))

      entry : R (EntryWf Sᵢ (entryAt i))
      entry = byType (CA.checkTyᴬ Sᵢ wK t tok TA.◇ᴬ c-◇ (elabTy i))

    -- a stage of the telescope: its well-formedness and its table
    record Stage (i : ℕ) : Set where
      constructor stage
      field
        swf  : WfSig (sigAt i)
        stbl : Tbl
        steq : stbl ≡ NT.mkTbl (kernel (sigAt i))

    next : (i : ℕ) (w : WfSig (sigAt i)) (t : Tbl) → t ≡ NT.mkTbl (kernel (sigAt i)) →
           R (EntryWf (sigAt i) (entryAt i)) → R (Stage (suc i))
    next i w t teq (err w') = err (primStringAppend "entry " (primStringAppend (primShowNat (ix i)) (primStringAppend " › " w')))
    next i w t teq (ok e)   =
      ok (stage (w , e) (NT.extendAt (len (sigAt i)) t (eBody (entryAt i)))
                (cong (λ x → NT.extendAt (len (sigAt i)) x (eBody (entryAt i))) teq))

    step : (i : ℕ) → R (Stage i) → R (Stage (suc i))
    step i (err w)              = err w
    step i (ok (stage w t teq)) = next i w t teq (Chk.entry i w t teq)

    stageAt : (i : ℕ) → R (Stage i)
    stageAt zero    = ok (stage wbase (NT.mkTbl (kernel base)) refl)
    stageAt (suc i) = step i (stageAt i)

  wfAt : (i : ℕ) → R (WfSig (sigAt i))
  wfAt i = forget (stageAt i)
    where
    forget : R (Stage i) → R (WfSig (sigAt i))
    forget (err w) = err w
    forget (ok st) = ok (Stage.swf st)

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
