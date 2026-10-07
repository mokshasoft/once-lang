-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- ⚠ GENERATED (PLAN-REF; scratch `gen_sigext.py`): one clause per rule.
--
-- OCP-0009 · dHoTT — ★ ALONG A SIGNATURE EXTENSION (PLAN-REF §1.4).
--
-- A signature 𝒮' EXTENDS 𝒮 below its size when it has every name of 𝒮
-- with the same body.  Then every reduction and conversion under 𝒮 is one
-- under 𝒮' (δ's side condition makes reduction monotone: a name beyond 𝒮
-- is stuck under 𝒮), and every derivation at bound n — whose references
-- also agree on their declared types — is one at bound n under 𝒮'.
--
-- This is how a signature built in segments (D081) moves its results
-- across a boundary: an entry is checked over its prefix, and used over
-- the whole.  SN, the logical relation and canonicity are NOT moved: they
-- are theorems about one well-formed signature.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import normalizer.Syntax.Types using ( _≡_; subst; sym )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; ref; εwkTm; εwkTy )
module DirectedHoTT.Metatheory.SigExt (𝒮 𝒮' : KSig)
  (inc   : ∀ {d} → d <ˢ KSig.size 𝒮 → d <ˢ KSig.size 𝒮')
  (body≡ : ∀ {d} → d <ˢ KSig.size 𝒮 → KSig.body 𝒮 d ≡ KSig.body 𝒮' d) where
import DirectedHoTT.Spec.Reduction 𝒮 as A
import DirectedHoTT.Spec.Reduction 𝒮' as B

mutual
  ext⟶  : ∀ {Γ t u} → A._⟶_ {Γ} t u → B._⟶_ t u
  ext⟶ᵀ : ∀ {Γ S T} → A._⟶ᵀ_ {Γ} S T → B._⟶ᵀ_ S T
  ext⟶ (A.β x0 x1) = B.β x0 x1
  ext⟶ (A.βfst x0 x1) = B.βfst x0 x1
  ext⟶ (A.βsnd x0 x1) = B.βsnd x0 x1
  ext⟶ (A.ξ-lam x0) = B.ξ-lam (ext⟶ x0)
  ext⟶ (A.ξ-appˡ x0) = B.ξ-appˡ (ext⟶ x0)
  ext⟶ (A.ξ-appʳ x0) = B.ξ-appʳ (ext⟶ x0)
  ext⟶ (A.ξ-pairˡ x0) = B.ξ-pairˡ (ext⟶ x0)
  ext⟶ (A.ξ-pairʳ x0) = B.ξ-pairʳ (ext⟶ x0)
  ext⟶ (A.ordtr-z x0 x1 x2 x3) = B.ordtr-z x0 x1 x2 x3
  ext⟶ (A.ordtr-szz x0 x1 x2) = B.ordtr-szz x0 x1 x2
  ext⟶ (A.ordtr-ssz x0 x1 x2 x3) = B.ordtr-ssz x0 x1 x2 x3
  ext⟶ (A.ordtr-szs x0 x1 x2 x3) = B.ordtr-szs x0 x1 x2 x3
  ext⟶ (A.ordtr-sss x0 x1 x2 x3 x4) = B.ordtr-sss x0 x1 x2 x3 x4
  ext⟶ (A.ξ-ordtrᵃ x0) = B.ξ-ordtrᵃ (ext⟶ x0)
  ext⟶ (A.ξ-ordtrᵗ x0) = B.ξ-ordtrᵗ (ext⟶ x0)
  ext⟶ (A.ξ-ordtrᵘ x0) = B.ξ-ordtrᵘ (ext⟶ x0)
  ext⟶ (A.ξ-ordtrᵖ x0) = B.ξ-ordtrᵖ (ext⟶ x0)
  ext⟶ (A.ξ-ordtrq x0) = B.ξ-ordtrq (ext⟶ x0)
  ext⟶ (A.ξ-absurdᶜ x0) = B.ξ-absurdᶜ (ext⟶ x0)
  ext⟶ (A.ξ-absurdᵉ x0) = B.ξ-absurdᵉ (ext⟶ x0)
  ext⟶ (A.ξ-fst x0) = B.ξ-fst (ext⟶ x0)
  ext⟶ (A.ξ-snd x0) = B.ξ-snd (ext⟶ x0)
  ext⟶ (A.ξ-⌜Π⌝ˡ x0) = B.ξ-⌜Π⌝ˡ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Π⌝ʳ x0) = B.ξ-⌜Π⌝ʳ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Σ⌝ˡ x0) = B.ξ-⌜Σ⌝ˡ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Σ⌝ʳ x0) = B.ξ-⌜Σ⌝ʳ (ext⟶ x0)
  ext⟶ (A.tr-J-base x0 x1 x2 x3 x4) = B.tr-J-base x0 x1 x2 x3 x4
  ext⟶ (A.tr-J-Σ x0 x1 x2 x3 x4 x5 x6) = B.tr-J-Σ x0 x1 x2 x3 x4 x5 x6
  ext⟶ (A.tr-J-Unit x0 x1 x2 x3 x4) = B.tr-J-Unit x0 x1 x2 x3 x4
  ext⟶ (A.tr-J-Id x0 x1 x2 x3 x4 x5 x6 x7) = B.tr-J-Id x0 x1 x2 x3 x4 x5 x6 x7
  ext⟶ (A.tr-J-IMu x0 x1 x2 x3 x4) = B.tr-J-IMu x0 x1 x2 x3 x4
  ext⟶ (A.tr-J-Fin x0 x1 x2 x3 x4) = B.tr-J-Fin x0 x1 x2 x3 x4
  ext⟶ (A.tr-taut x0 x1) = B.tr-taut x0 x1
  ext⟶ (A.hrefl-pw x0 x1 x2) = B.hrefl-pw x0 x1 x2
  ext⟶ A.hrefl-Nat-z = B.hrefl-Nat-z
  ext⟶ (A.hrefl-Nat-s x0) = B.hrefl-Nat-s x0
  ext⟶ (A.tr-J-Hom x0 x1 x2 x3 x4 x5 x6 x7 x8) = B.tr-J-Hom x0 x1 x2 x3 x4 x5 x6 x7 x8
  ext⟶ (A.tr-pw x0 x1 x2 x3 x4) = B.tr-pw x0 x1 x2 x3 x4
  ext⟶ (A.ξ-⌜Hom⌝ᶜ x0) = B.ξ-⌜Hom⌝ᶜ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Hom⌝ˡ x0) = B.ξ-⌜Hom⌝ˡ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Hom⌝ʳ x0) = B.ξ-⌜Hom⌝ʳ (ext⟶ x0)
  ext⟶ (A.ξ-hreflᶜ x0) = B.ξ-hreflᶜ (ext⟶ x0)
  ext⟶ (A.ξ-hreflᵃ x0) = B.ξ-hreflᵃ (ext⟶ x0)
  ext⟶ (A.ξ-trᵈ x0) = B.ξ-trᵈ (ext⟶ x0)
  ext⟶ (A.ξ-trᵖ x0) = B.ξ-trᵖ (ext⟶ x0)
  ext⟶ (A.ξ-trᵉ x0) = B.ξ-trᵉ (ext⟶ x0)
  ext⟶ (A.ap-J x0 x1 x2 x3 x4) = B.ap-J x0 x1 x2 x3 x4
  ext⟶ (A.ξ-apᶜ x0) = B.ξ-apᶜ (ext⟶ x0)
  ext⟶ (A.ξ-apᵇ x0) = B.ξ-apᵇ (ext⟶ x0)
  ext⟶ (A.ξ-apᵖ x0) = B.ξ-apᵖ (ext⟶ x0)
  ext⟶ (A.jsub-refl x0 x1 x2 x3) = B.jsub-refl x0 x1 x2 x3
  ext⟶ (A.ξ-⌜Id⌝ᶜ x0) = B.ξ-⌜Id⌝ᶜ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Id⌝ˡ x0) = B.ξ-⌜Id⌝ˡ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Id⌝ʳ x0) = B.ξ-⌜Id⌝ʳ (ext⟶ x0)
  ext⟶ (A.ξ-⌜Fin⌝ x0) = B.ξ-⌜Fin⌝ (ext⟶ x0)
  ext⟶ (A.ξ-idreflᶜ x0) = B.ξ-idreflᶜ (ext⟶ x0)
  ext⟶ (A.ξ-idreflᵃ x0) = B.ξ-idreflᵃ (ext⟶ x0)
  ext⟶ (A.ξ-jsubᵈ x0) = B.ξ-jsubᵈ (ext⟶ x0)
  ext⟶ (A.ξ-jsubᵖ x0) = B.ξ-jsubᵖ (ext⟶ x0)
  ext⟶ (A.ξ-jsubᵉ x0) = B.ξ-jsubᵉ (ext⟶ x0)
  ext⟶ (A.natrec-zero x0 x1) = B.natrec-zero x0 x1
  ext⟶ (A.natrec-suc x0 x1 x2) = B.natrec-suc x0 x1 x2
  ext⟶ (A.ξ-nsuc x0) = B.ξ-nsuc (ext⟶ x0)
  ext⟶ (A.ξ-natrecᶻ x0) = B.ξ-natrecᶻ (ext⟶ x0)
  ext⟶ (A.ξ-natrecˢ x0) = B.ξ-natrecˢ (ext⟶ x0)
  ext⟶ (A.ξ-natrecⁿ x0) = B.ξ-natrecⁿ (ext⟶ x0)
  ext⟶ (A.ι x0 x1 x2 x3) = B.ι x0 x1 x2 x3
  ext⟶ (A.dpay-ι x0 x1) = B.dpay-ι x0 x1
  ext⟶ (A.dpay-σ x0 x1 x2 x3) = B.dpay-σ x0 x1 x2 x3
  ext⟶ (A.dpay-ρ x0 x1 x2 x3) = B.dpay-ρ x0 x1 x2 x3
  ext⟶ (A.dih-ι x0 x1 x2) = B.dih-ι x0 x1 x2
  ext⟶ (A.dih-σ x0 x1 x2 x3 x4) = B.dih-σ x0 x1 x2 x3 x4
  ext⟶ (A.dih-ρ x0 x1 x2 x3 x4) = B.dih-ρ x0 x1 x2 x3 x4
  ext⟶ (A.fcase-z x0 x1) = B.fcase-z x0 x1
  ext⟶ (A.fcase-s x0 x1 x2) = B.fcase-s x0 x1 x2
  ext⟶ (A.psplit-β x0 x1 x2) = B.psplit-β x0 x1 x2
  ext⟶ (A.δref d p) = subst (λ z → B._⟶_ (ref d) (εwkTm z)) (sym (body≡ p)) (B.δref d (inc p))
  ext⟶ (A.ξ-⌜IMu⌝ᴵ x0) = B.ξ-⌜IMu⌝ᴵ (ext⟶ x0)
  ext⟶ (A.ξ-⌜IMu⌝ᴰ x0) = B.ξ-⌜IMu⌝ᴰ (ext⟶ x0)
  ext⟶ (A.ξ-⌜IMu⌝ⁱ x0) = B.ξ-⌜IMu⌝ⁱ (ext⟶ x0)
  ext⟶ (A.ξ-con x0) = B.ξ-con (ext⟶ x0)
  ext⟶ (A.ξ-ielimᴰ x0) = B.ξ-ielimᴰ (ext⟶ x0)
  ext⟶ (A.ξ-ielimⁱ x0) = B.ξ-ielimⁱ (ext⟶ x0)
  ext⟶ (A.ξ-ielimᵉ x0) = B.ξ-ielimᵉ (ext⟶ x0)
  ext⟶ (A.ξ-ielimᵗ x0) = B.ξ-ielimᵗ (ext⟶ x0)
  ext⟶ (A.ξ-dσˢ x0) = B.ξ-dσˢ (ext⟶ x0)
  ext⟶ (A.ξ-dσᶠ x0) = B.ξ-dσᶠ (ext⟶ x0)
  ext⟶ (A.ξ-dρʲ x0) = B.ξ-dρʲ (ext⟶ x0)
  ext⟶ (A.ξ-dρᶜ x0) = B.ξ-dρᶜ (ext⟶ x0)
  ext⟶ (A.ξ-dpayᴵ x0) = B.ξ-dpayᴵ (ext⟶ x0)
  ext⟶ (A.ξ-dpayᴰ x0) = B.ξ-dpayᴰ (ext⟶ x0)
  ext⟶ (A.ξ-dpayᶜ x0) = B.ξ-dpayᶜ (ext⟶ x0)
  ext⟶ (A.ξ-dihᴰ x0) = B.ξ-dihᴰ (ext⟶ x0)
  ext⟶ (A.ξ-dihᵉ x0) = B.ξ-dihᵉ (ext⟶ x0)
  ext⟶ (A.ξ-dihᶜ x0) = B.ξ-dihᶜ (ext⟶ x0)
  ext⟶ (A.ξ-dihᵖ x0) = B.ξ-dihᵖ (ext⟶ x0)
  ext⟶ (A.ξ-fsuc x0) = B.ξ-fsuc (ext⟶ x0)
  ext⟶ (A.ξ-fcaseᵗ x0) = B.ξ-fcaseᵗ (ext⟶ x0)
  ext⟶ (A.ξ-fcaseᵃ x0) = B.ξ-fcaseᵃ (ext⟶ x0)
  ext⟶ (A.ξ-fcaseᵇ x0) = B.ξ-fcaseᵇ (ext⟶ x0)
  ext⟶ (A.ξ-fcase0 x0) = B.ξ-fcase0 (ext⟶ x0)
  ext⟶ (A.ξ-psplitᵇ x0) = B.ξ-psplitᵇ (ext⟶ x0)
  ext⟶ (A.ξ-psplitᵍ x0) = B.ξ-psplitᵍ (ext⟶ x0)
  ext⟶ᵀ A.El-⌜base⌝ = B.El-⌜base⌝
  ext⟶ᵀ (A.El-⌜Π⌝ x0 x1) = B.El-⌜Π⌝ x0 x1
  ext⟶ᵀ (A.El-⌜Σ⌝ x0 x1) = B.El-⌜Σ⌝ x0 x1
  ext⟶ᵀ (A.El-⌜Hom⌝ x0 x1 x2) = B.El-⌜Hom⌝ x0 x1 x2
  ext⟶ᵀ (A.El-⌜Id⌝ x0 x1 x2) = B.El-⌜Id⌝ x0 x1 x2
  ext⟶ᵀ A.El-⌜Nat⌝ = B.El-⌜Nat⌝
  ext⟶ᵀ A.El-⌜IMu⌝ = B.El-⌜IMu⌝
  ext⟶ᵀ A.El-⌜Fin⌝ = B.El-⌜Fin⌝
  ext⟶ᵀ (A.DIh-ι x0 x1 x2) = B.DIh-ι x0 x1 x2
  ext⟶ᵀ (A.DIh-σ x0 x1 x2 x3 x4) = B.DIh-σ x0 x1 x2 x3 x4
  ext⟶ᵀ (A.DIh-ρ x0 x1 x2 x3 x4) = B.DIh-ρ x0 x1 x2 x3 x4
  ext⟶ᵀ A.El-⌜Unit⌝ = B.El-⌜Unit⌝
  ext⟶ᵀ (A.ξ-El x0) = B.ξ-El (ext⟶ x0)
  ext⟶ᵀ (A.ξ-Πˡ x0) = B.ξ-Πˡ (ext⟶ᵀ x0)
  ext⟶ᵀ (A.ξ-Πʳ x0) = B.ξ-Πʳ (ext⟶ᵀ x0)
  ext⟶ᵀ (A.ξ-Σˡ x0) = B.ξ-Σˡ (ext⟶ᵀ x0)
  ext⟶ᵀ (A.ξ-Σʳ x0) = B.ξ-Σʳ (ext⟶ᵀ x0)
  ext⟶ᵀ (A.Hom-Nat-z x0) = B.Hom-Nat-z x0
  ext⟶ᵀ (A.Hom-Nat-sz x0) = B.Hom-Nat-sz x0
  ext⟶ᵀ (A.Hom-Nat-ss x0 x1) = B.Hom-Nat-ss x0 x1
  ext⟶ᵀ (A.Hom-U x0 x1) = B.Hom-U x0 x1
  ext⟶ᵀ (A.Hom-Π x0 x1 x2 x3) = B.Hom-Π x0 x1 x2 x3
  ext⟶ᵀ (A.ξ-Homᵀ x0) = B.ξ-Homᵀ (ext⟶ᵀ x0)
  ext⟶ᵀ (A.ξ-Homˡ x0) = B.ξ-Homˡ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-Homʳ x0) = B.ξ-Homʳ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-Idᵀ x0) = B.ξ-Idᵀ (ext⟶ᵀ x0)
  ext⟶ᵀ (A.ξ-Idˡ x0) = B.ξ-Idˡ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-Idʳ x0) = B.ξ-Idʳ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-IMuᴵ x0) = B.ξ-IMuᴵ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-IMuᴰ x0) = B.ξ-IMuᴰ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-IMuⁱ x0) = B.ξ-IMuⁱ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-Desc x0) = B.ξ-Desc (ext⟶ x0)
  ext⟶ᵀ (A.ξ-Fin x0) = B.ξ-Fin (ext⟶ x0)
  ext⟶ᵀ (A.ξ-DIhᴰ x0) = B.ξ-DIhᴰ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-DIhᴹ x0) = B.ξ-DIhᴹ (ext⟶ᵀ x0)
  ext⟶ᵀ (A.ξ-DIhᶜ x0) = B.ξ-DIhᶜ (ext⟶ x0)
  ext⟶ᵀ (A.ξ-DIhᵖ x0) = B.ξ-DIhᵖ (ext⟶ x0)

ext≅ : ∀ {Γ t u} → A._≅_ {Γ} t u → B._≅_ t u
ext≅ (A.cred x0) = B.cred (ext⟶ x0)
ext≅ A.crfl = B.crfl
ext≅ (A.csym x0) = B.csym (ext≅ x0)
ext≅ (A.ctrn x0 x1) = B.ctrn (ext≅ x0) (ext≅ x1)

ext≅ᵀ : ∀ {Γ S T} → A._≅ᵀ_ {Γ} S T → B._≅ᵀ_ S T
ext≅ᵀ (A.credᵀ x0) = B.credᵀ (ext⟶ᵀ x0)
ext≅ᵀ A.crflᵀ = B.crflᵀ
ext≅ᵀ (A.csymᵀ x0) = B.csymᵀ (ext≅ᵀ x0)
ext≅ᵀ (A.ctrnᵀ x0 x1) = B.ctrnᵀ (ext≅ᵀ x0) (ext≅ᵀ x1)

-- ★ derivations at bound n, whose references also agree on their types
module Typed (n : ℕ)
  (type≡ : ∀ {d} → d <ˢ n → KSig.type 𝒮 d ≡ KSig.type 𝒮' d) where
  import DirectedHoTT.Spec.Typing 𝒮 n as TA
  import DirectedHoTT.Spec.Typing 𝒮' n as TB

  mutual
    ext⊢    : ∀ {Γ t T} → TA._⊢_∷_ Γ t T → TB._⊢_∷_ Γ t T
    ext⊢ty  : ∀ {Γ T} → TA._⊢ty_ Γ T → TB._⊢ty_ Γ T
    ext⊢ctx : ∀ {Γ} → TA.⊢ctx_ Γ → TB.⊢ctx_ Γ
    ext⊢ (TA.⊢var x0) = TB.⊢var x0
    ext⊢ (TA.⊢lam x0 x1) = TB.⊢lam (ext⊢ty x0) (ext⊢ x1)
    ext⊢ (TA.⊢app x0 x1) = TB.⊢app (ext⊢ x0) (ext⊢ x1)
    ext⊢ (TA.⊢pair x0 x1 x2) = TB.⊢pair (ext⊢ty x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ (TA.⊢absurd x0 x1) = TB.⊢absurd (ext⊢ x0) (ext⊢ x1)
    ext⊢ (TA.⊢ordtr x0 x1 x2 x3 x4) = TB.⊢ordtr (ext⊢ x0) (ext⊢ x1) (ext⊢ x2) (ext⊢ x3) (ext⊢ x4)
    ext⊢ (TA.⊢fst x0) = TB.⊢fst (ext⊢ x0)
    ext⊢ (TA.⊢snd x0) = TB.⊢snd (ext⊢ x0)
    ext⊢ TA.⊢⌜base⌝ = TB.⊢⌜base⌝
    ext⊢ (TA.⊢⌜Π⌝ x0 x1) = TB.⊢⌜Π⌝ (ext⊢ x0) (ext⊢ x1)
    ext⊢ (TA.⊢⌜Σ⌝ x0 x1) = TB.⊢⌜Σ⌝ (ext⊢ x0) (ext⊢ x1)
    ext⊢ (TA.⊢⌜Hom⌝ x0 x1 x2) = TB.⊢⌜Hom⌝ (ext⊢ x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ (TA.⊢hrefl x0 x1) = TB.⊢hrefl (ext⊢ x0) (ext⊢ x1)
    ext⊢ (TA.⊢trU x0 x1 x2 x3) = TB.⊢trU (ext⊢ x0) (ext⊢ x1) (ext⊢ x2) (ext⊢ x3)
    ext⊢ (TA.⊢tr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) = TB.⊢tr (ext⊢ x0) (ext⊢ x1) (ext⊢ x2) x3 x4 x5 (ext⊢ x6) (ext⊢ x7) (ext⊢ x8) (ext⊢ x9)
    ext⊢ (TA.⊢ap x0 x1 x2 x3 x4 x5 x6) = TB.⊢ap (ext⊢ x0) x1 (ext⊢ x2) (ext⊢ x3) (ext⊢ x4) (ext⊢ x5) (ext⊢ x6)
    ext⊢ (TA.⊢⌜Id⌝ x0 x1 x2) = TB.⊢⌜Id⌝ (ext⊢ x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ TA.⊢⌜Nat⌝ = TB.⊢⌜Nat⌝
    ext⊢ (TA.⊢⌜IMu⌝ x0 x1 x2) = TB.⊢⌜IMu⌝ (ext⊢ x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ (TA.⊢⌜Fin⌝ x0) = TB.⊢⌜Fin⌝ (ext⊢ x0)
    ext⊢ TA.⊢⌜Unit⌝ = TB.⊢⌜Unit⌝
    ext⊢ (TA.⊢idrefl x0 x1) = TB.⊢idrefl (ext⊢ x0) (ext⊢ x1)
    ext⊢ (TA.⊢jsub x0 x1 x2 x3 x4) = TB.⊢jsub (ext⊢ x0) (ext⊢ x1) (ext⊢ x2) (ext⊢ x3) (ext⊢ x4)
    ext⊢ TA.⊢unit = TB.⊢unit
    ext⊢ TA.⊢nzero = TB.⊢nzero
    ext⊢ (TA.⊢nsuc x0) = TB.⊢nsuc (ext⊢ x0)
    ext⊢ (TA.⊢natrec x0 x1 x2 x3) = TB.⊢natrec (ext⊢ty x0) (ext⊢ x1) (ext⊢ x2) (ext⊢ x3)
    ext⊢ (TA.⊢dι x0) = TB.⊢dι (ext⊢ x0)
    ext⊢ (TA.⊢dσ x0 x1 x2) = TB.⊢dσ (ext⊢ x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ (TA.⊢dρ x0 x1 x2) = TB.⊢dρ (ext⊢ x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ (TA.⊢dpay x0 x1 x2) = TB.⊢dpay (ext⊢ x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ (TA.⊢con x0 x1 x2 x3) = TB.⊢con (ext⊢ x0) (ext⊢ x1) (ext⊢ x2) (ext⊢ x3)
    ext⊢ (TA.⊢dih x0 x1 x2 x3 x4 x5) = TB.⊢dih (ext⊢ x0) (ext⊢ x1) (ext⊢ty x2) (ext⊢ x3) (ext⊢ x4) (ext⊢ x5)
    ext⊢ (TA.⊢ielim x0 x1 x2 x3 x4 x5) = TB.⊢ielim (ext⊢ x0) (ext⊢ x1) (ext⊢ty x2) (ext⊢ x3) (ext⊢ x4) (ext⊢ x5)
    ext⊢ (TA.⊢fzero x0) = TB.⊢fzero (ext⊢ x0)
    ext⊢ (TA.⊢fsuc x0) = TB.⊢fsuc (ext⊢ x0)
    ext⊢ (TA.⊢fcase x0 x1 x2 x3) = TB.⊢fcase (ext⊢ty x0) (ext⊢ x1) (ext⊢ x2) (ext⊢ x3)
    ext⊢ (TA.⊢fcase0 x0 x1) = TB.⊢fcase0 (ext⊢ty x0) (ext⊢ x1)
    ext⊢ (TA.⊢psplit x0 x1 x2 x3 x4) = TB.⊢psplit (ext⊢ty x0) (ext⊢ty x1) (ext⊢ty x2) (ext⊢ x3) (ext⊢ x4)
    ext⊢ (TA.⊢ref {d = d} p) = subst (λ z → TB._⊢_∷_ _ (ref d) (εwkTy z)) (sym (type≡ p)) (TB.⊢ref p)
    ext⊢ (TA.⊢conv x0 x1) = TB.⊢conv (ext⊢ x0) (ext≅ᵀ x1)
    ext⊢ty TA.ty-base = TB.ty-base
    ext⊢ty TA.ty-U = TB.ty-U
    ext⊢ty (TA.ty-Π x0 x1) = TB.ty-Π (ext⊢ty x0) (ext⊢ty x1)
    ext⊢ty (TA.ty-Σ x0 x1) = TB.ty-Σ (ext⊢ty x0) (ext⊢ty x1)
    ext⊢ty (TA.ty-El x0) = TB.ty-El (ext⊢ x0)
    ext⊢ty (TA.ty-Id x0 x1 x2) = TB.ty-Id (ext⊢ty x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ty TA.ty-Unit = TB.ty-Unit
    ext⊢ty TA.ty-Nat = TB.ty-Nat
    ext⊢ty (TA.ty-IMu x0 x1 x2) = TB.ty-IMu (ext⊢ x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ty (TA.ty-Desc x0) = TB.ty-Desc (ext⊢ x0)
    ext⊢ty (TA.ty-DIh x0 x1 x2 x3 x4) = TB.ty-DIh (ext⊢ x0) (ext⊢ x1) (ext⊢ty x2) (ext⊢ x3) (ext⊢ x4)
    ext⊢ty (TA.ty-Fin x0) = TB.ty-Fin (ext⊢ x0)
    ext⊢ty (TA.ty-Hom x0 x1 x2) = TB.ty-Hom (ext⊢ty x0) (ext⊢ x1) (ext⊢ x2)
    ext⊢ctx TA.c-◇ = TB.c-◇
    ext⊢ctx (TA.c-▹ x0 x1) = TB.c-▹ (ext⊢ctx x0) (ext⊢ty x1)
