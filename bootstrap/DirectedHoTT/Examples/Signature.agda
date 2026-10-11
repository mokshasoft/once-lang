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
--   · δ works INSIDE TYPES: `El (ref 1)` and `Nat` are convertible — the
--     kernel's `ref 1` (a name) δ-steps to entry 1's body (`δref`, at its
--     bound) (`one∷Nat`, `zero∷N`);
--   · the checker decides it, `ref` included (`checks`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Signature where
open import normalizer.Syntax.Types using ( _≡_; refl; _,_; ⊤; tt; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; vz; RTm; lam; app; nsuc; nzero; var; ⌜Nat⌝; Nat; El; ref; <-here; <-there )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature
open import DirectedHoTT.Metatheory.Signature
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no )
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Algorithm.CheckA as CA
import DirectedHoTT.Spec.Reduction
open import DirectedHoTT.Spec.Syntax using ( ∅ᴷ )
open import DirectedHoTT.Examples.Sig0 using ( ok₀ )
open import DirectedHoTT.Lib.Sugar ∅ᴷ 0 ok₀ using ( v₀ )
open import DirectedHoTT.Algorithm.NbETable using ( mkTbl; mkTbl-ok )

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
bd 2 = app (ref 0) nzero
bd _ = nzero

-- a TELESCOPE: each entry over the ones before it
Σ₃ : Sig
Σ₃ = mkSig 3 (∅ ▸ ⟨ ty 0 ∣ bd 0 ⟩ ▸ ⟨ ty 1 ∣ bd 1 ⟩ ▸ ⟨ ty 2 ∣ bd 2 ⟩)

-- its prefix: entry 2 is checked over it
Σ₂ : Sig
Σ₂ = mkSig 2 (∅ ▸ ⟨ ty 0 ∣ bd 0 ⟩ ▸ ⟨ ty 1 ∣ bd 1 ⟩)

module R₂ = DirectedHoTT.Spec.Reduction (kernel Σ₂)
module R₃ = DirectedHoTT.Spec.Reduction (kernel Σ₃)

------------------------------------------------------------------------
-- ★ Well-formed: each entry over its prefix.
------------------------------------------------------------------------

private
  -- the annotated bodies
  suc′ one : ATm ε
  suc′ = lam Nat (nsuc (var vz))
  one  = app (ref 0) nzero

  -- `El (ref 1)`: one δ step (entry 1 is in range), then decode — over
  --   the prefix (where entry 2 is checked) and over the whole signature
  Nat≅N₂ : {Γ : Cx} → R₂._≅ᵀ_ {Γ} Nat (El (ref 1))
  Nat≅N₂ = R₂.csymᵀ (R₂.ctrnᵀ (R₂.credᵀ (R₂.ξ-El (R₂.δref 1 <-here))) (R₂.credᵀ R₂.El-⌜Nat⌝))

  N≅Nat : {Γ : Cx} → R₃._≅ᵀ_ {Γ} (El (ref 1)) Nat
  N≅Nat = R₃.ctrnᵀ (R₃.credᵀ (R₃.ξ-El (R₃.δref 1 (<-there <-here)))) (R₃.credᵀ R₃.El-⌜Nat⌝)

  Nat≅N : {Γ : Cx} → R₃._≅ᵀ_ {Γ} Nat (El (ref 1))
  Nat≅N = R₃.csymᵀ N≅Nat

-- context formation: entry by entry, each over the telescope before it
-- (its type formed, its body's derivation, its erasure)
wf : WfSig Σ₃
wf = (((tt ,
  (suc′ , (TA.tyᴬ-Π TA.tyᴬ-Nat TA.tyᴬ-Nat , (TA.⊢ᴬlam TA.tyᴬ-Nat (TA.⊢ᴬnsuc (TA.⊢ᴬvar TA.hereᴬ)) , refl)))) ,
  (⌜Nat⌝ , (TA.tyᴬ-U , (TA.⊢ᴬ⌜Nat⌝ , refl)))) ,
  -- `one`'s type is `Nat`; its declaration says `El (ref 1)` — δ
  (one , (TA.tyᴬ-El (TA.⊢ᴬref <-here) ,
          (TA.⊢ᴬconv (TA.⊢ᴬapp (TA.⊢ᴬref (<-there <-here)) TA.⊢ᴬnzero) Nat≅N₂ , refl))))

consistent : {t : ATm ε} → TA._⊢ᴬ_∷_ Σ₃ TA.◇ᴬ t base → ⊥
consistent = consistencyˢ Σ₃ wf

------------------------------------------------------------------------
-- ★ Using it: δ in both directions.
------------------------------------------------------------------------

-- a reference used at the type its BODY has, not its declaration
one∷Nat : TA._⊢ᴬ_∷_ Σ₃ TA.◇ᴬ (ref 2) Nat
one∷Nat = TA.⊢ᴬconv (TA.⊢ᴬref <-here) N≅Nat

-- a definition unfolding inside a TYPE
zero∷N : TA._⊢ᴬ_∷_ Σ₃ TA.◇ᴬ nzero (El (ref 1))
zero∷N = TA.⊢ᴬconv TA.⊢ᴬnzero Nat≅N

------------------------------------------------------------------------
-- ★ The checker decides it.
------------------------------------------------------------------------

-- the checker at Σ₃: its kernel's well-formedness, its value table
module CA₃ = CA Σ₃ (wf→K Σ₃ wf) (mkTbl (kernel Σ₃)) (mkTbl-ok (kernel Σ₃))
open import DirectedHoTT.Spec.Typing (kernel Σ₃) (Sig.size Σ₃) using ( c-◇; ty-Nat )

private
  isYes : {P : Set} → Dec P → Set
  isYes (yes _) = ⊤
  isYes (no _)  = ⊥

checks : isYes (CA₃.checkᴬ TA.◇ᴬ c-◇ (app (ref 0) (ref 2)) Nat ty-Nat)
checks = _

-- …and REJECTS a reference to no entry, with a certified "no"
private
  isNo : {P : Set} → Dec P → Set
  isNo (yes _) = ⊥
  isNo (no _)  = ⊤

rejects : isNo (CA₃.inferᴬ TA.◇ᴬ c-◇ (ref 3))
rejects = _
