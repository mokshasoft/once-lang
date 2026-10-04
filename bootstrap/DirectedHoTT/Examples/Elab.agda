-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE ELABORATOR, exercised.  (PLAN-BIDI S6)
--
-- Surface terms with HOLES, over `Examples/Signature`'s Σ₃, elaborated and
-- then CHECKED by `CheckA` — each `ok` below holds by evaluation: the
-- elaborator proposed an annotated term and the certifying checker
-- returned its derivation.  The terms are written without the
-- annotations the core needs (`lam`'s domain, `pair`'s types, a constant
-- motive, `fsuc`'s bound).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Elab where
open import normalizer.Syntax.Types using ( ⊤; ⊥ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax using ( vz; vs )
open import DirectedHoTT.Spec.Typing using ( c-◇; ty-Nat; ty-Π; ty-Σ; ty-Unit; ty-Fin; ⊢nsuc; ⊢nzero )
open import DirectedHoTT.Spec.Annotated using ( ATy; Π; Σ'; Nat; Unit; Fin )
import DirectedHoTT.Spec.Annotated as AN
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Metatheory.Signature using ( wf→ok )
open import DirectedHoTT.Examples.Signature using ( Σ₃; wf )
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Algorithm.Elab as E
open import DirectedHoTT.Algorithm.Result using ( R; ok; err )
-- a pattern synonym resolves its constructor where it is DEFINED, so the
-- Lib/Sugar `v₀` (an `RTm`) cannot be reused for `STm`
pattern v₀ = var vz

private
  -- the annotated bodies of Σ₃, as δ hints for weak-head evaluation
  open import DirectedHoTT.Spec.Annotated as A using ( ATm )
  open import DirectedHoTT.Spec.Syntax using ( ε )
  open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
  hints : ℕ → ATm ε
  hints 0 = A.lam A.Nat (A.nsuc (A.var vz))
  hints 1 = A.⌜Nat⌝
  hints 2 = A.app (A.ref 0) A.nzero
  hints _ = A.nzero

open E Σ₃ hints 100
open Checked (wf→ok Σ₃ wf)

private
  isJust : {X : Set} → R X → Set
  isJust (ok _)  = ⊤
  isJust (err _) = ⊥

-- `lam`'s domain from the expected `Π`
ok-lam : isJust (elaborate TA.◇ᴬ c-◇ (lam □ᵀ (nsuc v₀)) (Π Nat Nat) (ty-Π ty-Nat ty-Nat))
ok-lam = _

-- doubling: an unannotated `lam`, and `natrec` at the CONSTANT motive
ok-double : isJust (elaborate TA.◇ᴬ c-◇
              (lam □ᵀ (natrec □ᵀ nzero (nsuc (nsuc v₀)) v₀)) (Π Nat Nat) (ty-Π ty-Nat ty-Nat))
ok-double = _

-- `pair`'s two types from the expected `Σ'`
ok-pair : isJust (elaborate TA.◇ᴬ c-◇ (pair □ᵀ □ᵀ nzero unit) (Σ' Nat Unit) (ty-Σ ty-Nat ty-Unit))
ok-pair = _

-- `fsuc`'s bound from the expected `Fin`
ok-fin : isJust (elaborate TA.◇ᴬ c-◇ (fsuc □ (fzero □)) (Fin (AN.nsuc (AN.nsuc AN.nzero))) (ty-Fin (⊢nsuc (⊢nsuc ⊢nzero))))
ok-fin = _

-- a signature reference whose type needs δ (`El (ref 1)` is `Nat`)
ok-ref : isJust (elaborate TA.◇ᴬ c-◇ (app (ref 0) (ref 2)) Nat ty-Nat)
ok-ref = _

-- …and a wrong one is REJECTED (CheckA's certified "no")
private
  isNothing : {X : Set} → R X → Set
  isNothing (ok _)  = ⊥
  isNothing (err _) = ⊤

no-ill : isNothing (elaborate TA.◇ᴬ c-◇ (app (ref 0) unit) Nat ty-Nat)
no-ill = _
