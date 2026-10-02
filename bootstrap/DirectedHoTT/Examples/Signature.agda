-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A SIGNATURE, exercised.  (PLAN-BIDI S5)
--
--     0  suc′ : Π Nat Nat    := lam Nat (nsuc v₀)
--     1  N    : U            := ⌜Nat⌝
--     2  one  : El (ref 1)   := app (ref 0) nzero
--
-- ★ What it shows:
--   · each entry is typed over its PREFIX (`wf`), so the signature is
--     well-formed and every kernel theorem holds over it (`consistent`);
--   · a reference is typed by its DECLARATION alone (`⊢ᴬref`);
--   · δ works INSIDE TYPES: `El (ref 1)` and `Nat` are convertible because
--     conversion is on erasures and erasure unfolds `ref 1` (`one∷Nat`,
--     `zero∷N`);
--   · the checker decides it, `ref` included (`checks`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Signature where
open import normalizer.Syntax.Types using ( _≡_; refl; _,_; ⊤; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; vz; RTm; lam; app; nsuc; nzero; var; ⌜Nat⌝; Nat; El )
open import DirectedHoTT.Spec.Typing using ( _≅ᵀ_; credᵀ; csymᵀ; El-⌜Nat⌝; c-◇; ty-Nat )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature
open import DirectedHoTT.Metatheory.Signature
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no )
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Algorithm.CheckA as CA
open import DirectedHoTT.Lib.Sugar using ( v₀ )

------------------------------------------------------------------------
-- The signature.
------------------------------------------------------------------------

ty : ℕ → ATy ε
ty 0 = Π Nat Nat
ty 1 = U
ty 2 = El (ref 1)
ty _ = Unit

-- the bodies, ERASED (`wf` checks each against its annotated source)
bd : ℕ → RTm ε
bd 0 = lam (nsuc v₀)
bd 1 = ⌜Nat⌝
bd 2 = app (lam (nsuc v₀)) nzero
bd _ = nzero

Σ₃ : Sig
Σ₃ = record { size = 3 ; type = ty ; body = bd }

------------------------------------------------------------------------
-- ★ Well-formed: each entry over its prefix.
------------------------------------------------------------------------

private
  -- the annotated bodies
  suc′ one : ATm ε
  suc′ = lam Nat (nsuc (var vz))
  one  = app (ref 0) nzero

  Nat≅N : {Γ : Cx} → _≅ᵀ_ {Γ} Nat (El ⌜Nat⌝)
  Nat≅N = csymᵀ (credᵀ El-⌜Nat⌝)

wf : WfSig Σ₃
wf = ((((_ ,
  (suc′ , (TA.⊢ᴬlam TA.tyᴬ-Nat (TA.⊢ᴬnsuc (TA.⊢ᴬvar TA.hereᴬ)) , refl))) ,
  (⌜Nat⌝ , (TA.⊢ᴬ⌜Nat⌝ , refl))) ,
  -- `one`'s type is `Nat`; its declaration says `El (ref 1)` — δ
  (one , (TA.⊢ᴬconv (TA.⊢ᴬapp (TA.⊢ᴬref (<-there <-here)) TA.⊢ᴬnzero) Nat≅N , refl))))

consistent : {t : ATm ε} → TA._⊢ᴬ_∷_ Σ₃ TA.◇ᴬ t base → ⊥
consistent = consistencyˢ Σ₃ wf

------------------------------------------------------------------------
-- ★ Using it: δ in both directions.
------------------------------------------------------------------------

-- a reference used at the type its BODY has, not its declaration
one∷Nat : TA._⊢ᴬ_∷_ Σ₃ TA.◇ᴬ (ref 2) Nat
one∷Nat = TA.⊢ᴬconv (TA.⊢ᴬref <-here) (credᵀ El-⌜Nat⌝)

-- a definition unfolding inside a TYPE
zero∷N : TA._⊢ᴬ_∷_ Σ₃ TA.◇ᴬ nzero (El (ref 1))
zero∷N = TA.⊢ᴬconv TA.⊢ᴬnzero Nat≅N

------------------------------------------------------------------------
-- ★ The checker decides it.
------------------------------------------------------------------------

private
  isYes : {P : Set} → Dec P → Set
  isYes (yes _) = ⊤
  isYes (no _)  = ⊥

checks : isYes (CA.checkᴬ Σ₃ (wf→ok Σ₃ wf) TA.◇ᴬ c-◇ (app (ref 0) (ref 2)) Nat ty-Nat)
checks = _

-- …and REJECTS a reference to no entry, with a certified "no"
private
  isNo : {P : Set} → Dec P → Set
  isNo (yes _) = ⊥
  isNo (no _)  = ⊤

rejects : isNo (CA.inferᴬ Σ₃ (wf→ok Σ₃ wf) TA.◇ᴬ c-◇ (ref 3))
rejects = _
