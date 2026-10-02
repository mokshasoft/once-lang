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
-- ★ TWO PASSES, and why.
--   1. ELABORATE (untrusted): entry `n` is elaborated over `sigAt n`, the
--      signature of the entries before it, built by structural recursion
--      on `n` together with the elaborated types and bodies.
--   2. CHECK (trusted): the elaborated body is re-checked by `CheckA` over
--      `prefix S n` of the FINAL signature, the one `WfSig` speaks about,
--      and its erasure is compared (`_≟Tm_`) with the final `body n`.
--   The elaboration pass never needs to agree with the final signature:
--   it only proposes terms.  So no lemma relates the two.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import normalizer.Syntax.Types using ( _≡_; refl; Σ; _,_; _×_; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax using ( ε; RTm; nzero )
open import DirectedHoTT.Spec.Typing using ( c-◇ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature using ( Sig; prefix )
open import DirectedHoTT.Metatheory.Signature using ( EntryWf; WfUpTo; WfSig; okUpTo )
open import DirectedHoTT.Algorithm.Surface using ( STy; STm )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no; _≟ℕ_; _≟Tm_ )
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Algorithm.Elab as E
open import DirectedHoTT.Algorithm.Result using ( R; ok; err; why )
open import Agda.Builtin.String using ( String; primStringAppend; primShowNat )
import DirectedHoTT.Algorithm.CheckA as CA
import DirectedHoTT.Metatheory.Erasure as Er

-- entry `d` is declared `tys d` with body `tms d`
module DirectedHoTT.Algorithm.SigBuild
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

------------------------------------------------------------------------
-- 1. ELABORATION: entry n over the signature of the entries before it.
------------------------------------------------------------------------

typeAt  : ℕ → ℕ → ATy ε
abodyAt : ℕ → ℕ → ATm ε
bodyAt  : ℕ → ℕ → RTm ε
elabTy  : ℕ → ATy ε
elabTm  : ℕ → ATm ε

sigAt : ℕ → Sig
sigAt n = record { size = n ; type = typeAt n ; body = bodyAt n }

elabTyR : ℕ → R (ATy ε)
elabTyR n = E.elT (sigAt n) (abodyAt n) fuel (λ ()) (tys n)

elabTmR : ℕ → R (ATm ε)
elabTmR n = E.chk (sigAt n) (abodyAt n) fuel (λ ()) (tms n) (elabTy n)

elabTy n = fromR Unit (elabTyR n)
elabTm n = fromR nzero (elabTmR n)

typeAt zero    = λ _ → Unit
typeAt (suc n) = ext n (elabTy n) (typeAt n)
abodyAt zero    = λ _ → nzero
abodyAt (suc n) = ext n (elabTm n) (abodyAt n)
bodyAt zero    = λ _ → nzero
bodyAt (suc n) = ext n (Era.⌈_⌉ (bodyAt n) (elabTm n)) (bodyAt n)

------------------------------------------------------------------------
-- 2. ★ The signature, and its well-formedness — CHECKED.
------------------------------------------------------------------------

S : Sig
S = sigAt size

-- the annotated body of entry n (the elaborated one)
abody : ℕ → ATm ε
abody = abodyAt size

-- why entry n failed to ELABORATE ("ok" if it did) — read it off a type
-- error: `why-entry 3 ≡ "ok"` by `refl`
why-entry : ℕ → String
why-entry n with elabTyR n
... | err w = primStringAppend "type › " w
... | ok _  = primStringAppend "body › " (why (elabTmR n))

private
  entry : (n : ℕ) → WfUpTo S n → R (EntryWf S n)
  entry n w with CA.checkTyᴬ (prefix S n) (okUpTo S n w) TA.◇ᴬ c-◇ (Sig.type S n)
  ... | no _ = err (primStringAppend "the checker rejects the type › " (why-entry n))
  ... | yes dA
      with CA.checkᴬ (prefix S n) (okUpTo S n w) TA.◇ᴬ c-◇ (abody n) (Sig.type S n)
             (Er.erase-ty (prefix S n) (okUpTo S n w) dA)
  ...   | no _ = err (primStringAppend "the checker rejects the body › " (why-entry n))
  ...   | yes d with Era.⌈_⌉ (Sig.body S) (abody n) ≟Tm Sig.body S n
  ...     | yes eq = ok (abody n , (d , eq))
  ...     | no _   = err "the erased body differs from the stored one"

wfUpTo : (n : ℕ) → R (WfUpTo S n)
wfUpTo zero = ok tt
wfUpTo (suc n) with wfUpTo n
... | err w = err w
... | ok w with entry n w
...   | err w' = err (primStringAppend "entry " (primStringAppend (primShowNat n) (primStringAppend " › " w')))
...   | ok e   = ok (w , e)

-- ★ the signature's well-formedness, when it holds — else the reason
wfSig : R (WfSig S)
wfSig = wfUpTo size

-- for a concrete signature: `wf = fromJust wfSig _`
IsJust : {A : Set} → R A → Set
IsJust (ok _)  = ⊤
IsJust (err _) = ⊥

fromJust : {A : Set} (m : R A) → IsJust m → A
fromJust (ok a) _ = a
fromJust (err _)  ()
