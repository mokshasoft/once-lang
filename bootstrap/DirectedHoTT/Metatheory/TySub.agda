-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- DirectedHoTT · METATHEORY — ★★★ THE **STRUCTURAL** TYPING LEMMAS, SPLIT
-- OUT OF `SubjectReduction`: WHAT CALLERS ACTUALLY USE.
--
-- ⚠⚠ THE SPLIT IS BY CONSUMPTION, NOT BY SUBJECT.  Of the ~100 modules
--   that import `SubjectReduction`, roughly NINETY use exactly ONE name
--   from it: `⊢wk`.  A handful more want `⊢-cast`, `ren-ty`, `Sub⊢`.
--   Only EIGHT want `sr`, `sr*`, or the indexed-ι lemmas — the things
--   the module is NAMED for.
--
-- ★★★ AND THE PRICE OF THAT MISMATCH IS MEASURED.  `SubjectReduction`
--   depends on `Confluence` (8.9 MB) and `Injectivity` (5.4 MB), so every
--   knot module was deserializing the whole confluence proof IN ORDER TO
--   WEAKEN A DERIVATION.  `--profile=all` puts ~70% of a knot module's
--   time in deserialization against ~0ms of TYPING (`Knot/Census`:
--   3,948ms of 5,811ms) — so what a module must READ is the cost, and
--   this is the only lever that touches it.
--
-- ★ WHY THE CUT IS EXACTLY HERE.  `SubjectReduction` lines 1–1644 are
--   closed under themselves except for ONE section — 565–913, the reduct
--   analyses for `sr`'s J and taut cases, which are the only place
--   `Π-reduct`/`ΠRed`/`church-rosserᵀ` are used.  That section defines 19
--   names and NOT ONE of them is used anywhere else in the head; it stays
--   behind.  What is left needs `RedCong` and nothing more.
--
-- ⚠ `SubjectReduction` re-exports this `public`, so nothing that already
--   imported it breaks; a module that wants only weakening imports THIS.
--
-- WHAT IS HERE: `∋-cast`, `⊢-cast`, the type-level commute/cancel lemmas,
-- conversion-survives-renaming, the eliminator naturality layer (plain
-- and indexed), monotonicity, `Ren⊢`/`ren-ty`/`ren-lemma`/`⊢wk`,
-- `Sub⊢`/`sub-ty`/`sub-lemma`/`⊢single`/`⊢[]`, `wk-cancel-tm`.
-- WHAT IS NOT: the reduct analyses, generation, the pw decode joins,
-- `sr`, `sr*`, and the ι/indexed-ι lemmas — all downstream of `sr`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 28 — (B2, part 2) SUBJECT REDUCTION, completed
--
-- The mechanical closing of subject reduction, on the Π-injectivity of
-- `NbEPDirDBInj` (dHoTT-26). Everything here is confluence-free and reuses the
-- strict substitution laws of `NbEPDirDBPi`/`NbEPDirDBSR`/`NbEPDirDBConf`.
--
--   * Type-level commute/cancel lemmas (`wk-cancel`, `subTy-comm`,
--     `ren-wk-comm`, `ren-comm-ty`, `exts-wk-ty`) — all via the type fusion
--     lemmas + refl/`sub-comm` bridges.
--   * `⟶ᵀ-ren`/`≅ᵀ-ren` — conversion survives renaming; `subTy-monoˢ` — types
--     are monotone in the substitution.
--   * `ren-lemma` / `sub-lemma` — TYPED renaming and substitution preserve
--     typing (the `⊢ˢ`/`Ren⊢` judgments + the ext-lemmas), and `⊢[]` — single
--     substitution preserves typing (what β needs).
--   * `gen-lam` / `gen-app` — generation (inversion through `⊢conv`).
--   * **`sr`** — SUBJECT REDUCTION: `Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A`. The β case
--     converts the argument to the λ's domain and the result type (via
--     `Π-inj`), sidestepping context conversion entirely.
--
-- With this, dHoTT-24's scoped ceiling is fully lifted: the kernel enjoys
-- subject reduction. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs; _<ˢ_; _<ˢ?_ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
module DirectedHoTT.Metatheory.TySub (𝒮 : Defs) (n : ℕ) where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ ; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; Thin; keep; thinR; vz; vs; RTy; base; U; Π; Σ'; El
        ; Hom; RTm; var; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝
        ; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub; Id-cong₃
        ; ⌜Id⌝-cong₃; jsub-cong₃; Unit; Nat; unit; nzero; nsuc; natrec; ⌜Nat⌝
        ; ⌜Unit⌝; Ren; extR; renTm; renTy; Sub; extS; subTm; subTy; idₛ; _∘ᵣ_
        ; _ₛ∘ᵣ_; _ᵣ∘ₛ_; _∘ₛ_; subTy-renTy; renTy-subTy; subTy-subTy
        ; renTy-renTy; subTy-cong; renTy-cong; subTy-id; subTm-renTm; subTm-id
        ; subTm-cong; renTm-renTm; renTm-subTm; ⌜Hom⌝-cong₃; Hom-cong₃
        ; ordtr-cong₅; Desc; con; dι; dρ; IMu; ielim; ⌜IMu⌝; εwkTy; εwk-ren
        ; εwk-sub; εwkTm; εwkTm-ren; εwkTm-sub; subTm-subTm; DIh; Fin; ⌜Fin⌝
        ; dσ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit; cong₃; cong₄
        ; renTm-cong
        ; ref )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; _∨_; occTm; ∨-false; ∨-false₁; ∨-false₂; occ-ren-eq
        ; occ-sub; eqv; Avoids; occ-ren-tm; avoids-wk; PosC; posc-var
        ; posc-Hom; posc-ren; posc-sub; pw?; stkC?; pwDom; pwBody; pwShift
        ; pw?-sub; stkC?-sub; pwBody-sub; pwDom-sub; pwBody-occ; ren-as-sub
        ; avoids-pwShift; subTm-occ; stkC?-ren; wk-ren-tm; wk-sub-tm; flat?
        ; flat→stk; flat?-ren; flat?-sub; NoNatC; nnc-base; nnc-Unit; nnc-Π
        ; nnc-Σ; nnc-Hom; nnc-Id; nonatc-ren; nonatc-sub; nonatc-pwBody; stkA?
        ; stkA?-ren; stkA?-sub; stkC?→stkA?; NoNatHd; nnh-base; nnh-Unit
        ; nnh-Σ; nnh-Id; nnh-Π; nnh-Hom; nnh-IMu; nonatc→hd; stkC?→hd
        ; occ-εwkTm )
open import DirectedHoTT.Spec.Typing 𝒮 n
  using ( single; nrs; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ
        ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; _⟶_; β; βfst
        ; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ
        ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss; ξ-ordtrᵃ
        ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ
        ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; tr-J-base; tr-J-Σ; tr-J-Id; tr-J-Unit; tr-J-IMu
        ; tr-taut; hrefl-pw; hrefl-Nat-z; hrefl-Nat-s; tr-J-Hom; tr-pw; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜IMu⌝
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ
        ; ξ-trᵉ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ
        ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; El-⌜Id⌝
        ; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ
        ; ξ-natrecˢ; ξ-natrecⁿ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss; _⟶*_; done
        ; step; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_
        ; here; there; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢absurd
        ; ⊢ordtr; ⊢trU; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢ap; ⊢conv
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec; ⊢⌜Nat⌝
        ; ⊢⌜Unit⌝; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom; ty-Id
        ; ty-Unit; ty-Nat; ⊢ctx_; c-◇; c-▹; ξ-con; ξ-ielimⁱ; ξ-ielimᵗ; ⊢con
        ; wk-single; iinst; ty-IMu; ⊢ielim; ⊢⌜IMu⌝; _≅_; csym; ctrn; cred
        ; crfl; El-⌜Fin⌝; DIh-ι; DIh-σ; DIh-ρ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-Fin; ξ-⌜Fin⌝
        ; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι
        ; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β; tr-J-Fin; single2; methS
        ; wk2M; MethTy; fsucS; pairS; motCtx; ty-Desc; ty-DIh; ty-Fin; ⊢⌜Fin⌝
        ; ⊢dι; ⊢dσ; ⊢dρ; ⊢dpay; ⊢dih; ⊢fzero; ⊢fsuc; ⊢fcase; ⊢fcase0; ⊢psplit
        ; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dσˢ; ξ-dσᶠ
        ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ
        ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ
        ; ξ-psplitᵍ; DescF
        ; δref; ⊢ref )
import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 as ᴵSubjectReductionBase
open ᴵSubjectReductionBase using ( ≅ᵀ-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.RedCong 𝒮
  using ( ⟶-ren; ⟶*-ren; ⟶*-appʳ; ren-comm; subTm-monoˢ; extS-mono
        ; single-mono; stkC?-red; stkA?-red; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans
        ; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ
        ; red→≅ᵀ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-IMu; ⟶ᵀ*-IMuᴵ; ⟶ᵀ*-IMuᴰ
        ; ⟶ᵀ*-Desc; ⟶ᵀ*-Fin; ⟶*-⌜Fin⌝; ⟶ᵀ*-DIhᴰ; ⟶ᵀ*-DIhᴹ; ⟶ᵀ*-DIhᶜ; ⟶ᵀ*-DIhᵖ; ⟶*-trans; ⟶*-dpayᴰ
        ; ⟶*-dpayᶜ; ⟶*-appˡ )
open ᴵSubjectReductionBase using ( sub-comm; ⟶ᵀ-sub; subTy-comm; sub-comm-ty-ext; iinst-sub; wk-sub ; wk2-subTy )
open import DirectedHoTT.Metatheory.TySub.Red 𝒮 public


⊢-cast : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {A A' : RTy ⌊ Γ ⌋} →
         A ≡ A' → Γ ⊢ t ∷ A → Γ ⊢ t ∷ A'
⊢-cast refl d = d

------------------------------------------------------------------------
-- Typed renaming preserves typing.
------------------------------------------------------------------------

Ren⊢ : (Γ Δ : Ctx) → Ren ⌊ Γ ⌋ ⌊ Δ ⌋ → Set
Ren⊢ Γ Δ ρ = ∀ {x A} → Γ ∋ x ∷ A → Δ ∋ ρ x ∷ renTy ρ A

Ren⊢-ext : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {C : RTy ⌊ Γ ⌋} →
           Ren⊢ Γ Δ ρ → Ren⊢ (Γ ▹ C) (Δ ▹ renTy ρ C) (extR ρ)
Ren⊢-ext {ρ = ρ} {C = C} h here =
  ∋-cast (sym (ren-wk-comm ρ C)) here
Ren⊢-ext {ρ = ρ} h (there {A = A₀} v) =
  ∋-cast (sym (ren-wk-comm ρ A₀)) (there (h v))

-- Typed renaming, now MUTUAL with renaming for TYPE FORMATION: `⊢lam`/`⊢pair`
-- carry `⊢ty` premises (2026-07-30, option A), so the two must move together.
ren-lemma : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
            Γ ⊢ t ∷ A → Ren⊢ Γ Δ ρ → Δ ⊢ renTm ρ t ∷ renTy ρ A

ren-ty : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
         Γ ⊢ty A → Ren⊢ Γ Δ ρ → Δ ⊢ty renTy ρ A

ren-ty ty-base       h = ty-base
ren-ty ty-Unit       h = ty-Unit
ren-ty ty-Nat        h = ty-Nat
ren-ty {ρ = ρ} (ty-IMu {I = I} dI dD di) h = ty-IMu (ren-lemma dI h) (⊢-cast (DescF-ren ρ I) (ren-lemma dD h)) (ren-lemma di h)
ren-ty (ty-Desc dI) h = ty-Desc (ren-lemma dI h)
ren-ty {Δ = Δ} {ρ = ρ} (ty-DIh {I = I} {D = D} {M = M} dI dD dM dC dp) h =
  ty-DIh (ren-lemma dI h) (⊢-cast (DescF-ren ρ I) (ren-lemma dD h))
    (subst (λ A → ((Δ ▹ El (renTm ρ I)) ▹ A) ⊢ty renTy (extR (extR ρ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-ren ρ I) (wk-ren ρ D))
             (ren-ty dM (Ren⊢-ext (Ren⊢-ext h))))
    (ren-lemma dC h) (ren-lemma dp h)
ren-ty (ty-Fin dn) h = ty-Fin (ren-lemma dn h)
ren-ty ty-U          h = ty-U
ren-ty (ty-Π dA dB)  h = ty-Π (ren-ty dA h) (ren-ty dB (Ren⊢-ext h))
ren-ty (ty-Σ dA dB)  h = ty-Σ (ren-ty dA h) (ren-ty dB (Ren⊢-ext h))
ren-ty (ty-El dc)    h = ty-El (ren-lemma dc h)
ren-ty (ty-Hom dA dt du) h =
  ty-Hom (ren-ty dA h) (ren-lemma dt h) (ren-lemma du h)
ren-ty (ty-Id dA dt du) h =
  ty-Id (ren-ty dA h) (ren-lemma dt h) (ren-lemma du h)

ren-lemma ⊢unit  h = ⊢unit
ren-lemma ⊢nzero h = ⊢nzero
ren-lemma (⊢nsuc dn) h = ⊢nsuc (ren-lemma dn h)
-- under renaming; the motive's is not, and rides `methsTyFrom-ren`.
ren-lemma {ρ = ρ} (⊢natrec {M = M} {n = n} dM dz ds dn) h =
  ⊢-cast (sym (ren-comm-ty ρ M n))
    (⊢natrec (ren-ty dM (Ren⊢-ext h))
             (⊢-cast (ren-comm-ty ρ M nzero) (ren-lemma dz h))
             (⊢-cast (nrs-ren ρ M) (ren-lemma ds (Ren⊢-ext (Ren⊢-ext h))))
             (ren-lemma dn h))
-- ★★ LEVITATION
ren-lemma {ρ = ρ} (⊢⌜IMu⌝ {I = I} dI dD di) h = ⊢⌜IMu⌝ (ren-lemma dI h) (⊢-cast (DescF-ren ρ I) (ren-lemma dD h)) (ren-lemma di h)
ren-lemma (⊢⌜Fin⌝ dn) h = ⊢⌜Fin⌝ (ren-lemma dn h)
ren-lemma (⊢dι dI) h = ⊢dι (ren-lemma dI h)
ren-lemma {ρ = ρ} (⊢dσ {I = I} {S = S} dI dS df) h =
  ⊢dσ (ren-lemma dI h) (ren-lemma dS h)
      (⊢-cast (cong (λ X → Π (El (renTm ρ S)) (Desc X)) (wk-ren ρ I)) (ren-lemma df h))
ren-lemma (⊢dρ dI dj dC) h = ⊢dρ (ren-lemma dI h) (ren-lemma dj h) (ren-lemma dC h)
ren-lemma {ρ = ρ} (⊢dpay {I = I} dI dD dC) h = ⊢dpay (ren-lemma dI h) (⊢-cast (DescF-ren ρ I) (ren-lemma dD h)) (ren-lemma dC h)
ren-lemma {ρ = ρ} (⊢con {I = I} dI dD di dp) h = ⊢con (ren-lemma dI h) (⊢-cast (DescF-ren ρ I) (ren-lemma dD h)) (ren-lemma di h) (ren-lemma dp h)
ren-lemma {Δ = Δ} {ρ = ρ} (⊢dih {I = I} {D = D} {M = M} dI dD dM de dC dp) h =
  ⊢dih (ren-lemma dI h) (⊢-cast (DescF-ren ρ I) (ren-lemma dD h))
    (subst (λ A → ((Δ ▹ El (renTm ρ I)) ▹ A) ⊢ty renTy (extR (extR ρ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-ren ρ I) (wk-ren ρ D))
             (ren-ty dM (Ren⊢-ext (Ren⊢-ext h))))
    (⊢-cast (MethTy-ren ρ I D M) (ren-lemma de h))
    (ren-lemma dC h) (ren-lemma dp h)
ren-lemma {Δ = Δ} {ρ = ρ} (⊢ielim {I = I} {D = D} {M = M} {i = i} {t = t} dI dD dM de di dt) h =
  ⊢-cast (sym (iinst-ren ρ M i t))
    (⊢ielim (ren-lemma dI h) (⊢-cast (DescF-ren ρ I) (ren-lemma dD h))
      (subst (λ A → ((Δ ▹ El (renTm ρ I)) ▹ A) ⊢ty renTy (extR (extR ρ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-ren ρ I) (wk-ren ρ D))
             (ren-ty dM (Ren⊢-ext (Ren⊢-ext h))))
      (⊢-cast (MethTy-ren ρ I D M) (ren-lemma de h))
      (ren-lemma di h) (ren-lemma dt h))
ren-lemma (⊢fzero dn) h = ⊢fzero (ren-lemma dn h)
ren-lemma (⊢fsuc dt) h = ⊢fsuc (ren-lemma dt h)
ren-lemma {ρ = ρ} (⊢fcase {P = P} {t = t} dP dt da db) h =
  ⊢-cast (sym (ren-comm-ty ρ P t))
    (⊢fcase (ren-ty dP (Ren⊢-ext h)) (ren-lemma dt h)
            (⊢-cast (ren-comm-ty ρ P fzero) (ren-lemma da h))
            (⊢-cast (fsucS-ren ρ P) (ren-lemma db (Ren⊢-ext h))))
ren-lemma {ρ = ρ} (⊢fcase0 {P = P} {t = t} dP dt) h =
  ⊢-cast (sym (ren-comm-ty ρ P t)) (⊢fcase0 (ren-ty dP (Ren⊢-ext h)) (ren-lemma dt h))
ren-lemma {ρ = ρ} (⊢psplit {P = P} {q = q} dA dB dP dq db) h =
  ⊢-cast (sym (ren-comm-ty ρ P q))
    (⊢psplit (ren-ty dA h) (ren-ty dB (Ren⊢-ext h)) (ren-ty dP (Ren⊢-ext h)) (ren-lemma dq h)
             (⊢-cast (pairS-ren ρ P) (ren-lemma db (Ren⊢-ext (Ren⊢-ext h)))))
ren-lemma (⊢var v) h = ⊢var (h v)
ren-lemma (⊢lam dA d) h = ⊢lam (ren-ty dA h) (ren-lemma d (Ren⊢-ext h))
ren-lemma {ρ = ρ} (⊢app {B = D} {u = u} d₁ d₂) h =
  ⊢-cast (sym (ren-comm-ty ρ D u)) (⊢app (ren-lemma d₁ h) (ren-lemma d₂ h))
ren-lemma {ρ = ρ} (⊢pair {B = B} {a = a} dB d₁ d₂) h =
  ⊢pair (ren-ty dB (Ren⊢-ext h))
        (ren-lemma d₁ h) (⊢-cast (ren-comm-ty ρ B a) (ren-lemma d₂ h))
ren-lemma (⊢absurd dc de) h = ⊢absurd (ren-lemma dc h) (ren-lemma de h)
ren-lemma (⊢ordtr da dt du dp dq) h =
  ⊢ordtr (ren-lemma da h) (ren-lemma dt h) (ren-lemma du h)
         (ren-lemma dp h) (ren-lemma dq h)
ren-lemma (⊢fst d) h = ⊢fst (ren-lemma d h)
ren-lemma {ρ = ρ} (⊢snd {B = B} {p = p} d) h =
  ⊢-cast (sym (ren-comm-ty ρ B (fst p))) (⊢snd (ren-lemma d h))
ren-lemma ⊢⌜base⌝ h = ⊢⌜base⌝
ren-lemma ⊢⌜Nat⌝ h = ⊢⌜Nat⌝
ren-lemma ⊢⌜Unit⌝ h = ⊢⌜Unit⌝
--   `⊢elim`'s is `Γ ▹ Mu D` and `⊢natrec`'s is `Γ ▹ Nat`; both survive
--   `renTy ρ` on the nose.  `⊢ielim`'s is `Γ ▹ εwkTy I`, which does NOT —
--   it is only propositionally fixed, by `εwk-ren`.  Hence a `subst` on
--   the CONTEXT slot, which no other clause here needs.  It is harmless
--   because `⌊ Γ ▹ A ⌋ = ⌊ Γ ⌋ ∙` ignores `A`, so no `RTy` index moves.
ren-lemma (⊢⌜Π⌝ dc dd) h = ⊢⌜Π⌝ (ren-lemma dc h) (ren-lemma dd (Ren⊢-ext h))
ren-lemma (⊢⌜Σ⌝ dc dd) h = ⊢⌜Σ⌝ (ren-lemma dc h) (ren-lemma dd (Ren⊢-ext h))
ren-lemma (⊢⌜Hom⌝ dc da db) h =
  ⊢⌜Hom⌝ (ren-lemma dc h) (ren-lemma da h) (ren-lemma db h)
ren-lemma (⊢hrefl dc dt) h = ⊢hrefl (ren-lemma dc h) (ren-lemma dt h)
ren-lemma (⊢⌜Id⌝ dc da db) h =
  ⊢⌜Id⌝ (ren-lemma dc h) (ren-lemma da h) (ren-lemma db h)
ren-lemma (⊢idrefl dc dt) h = ⊢idrefl (ren-lemma dc h) (ren-lemma dt h)
ren-lemma {ρ = ρ} (⊢jsub {d = d} {t = t} {u = u} dd dt du dp de) h =
  ⊢-cast (cong El (sym (ren-comm ρ d u)))
    (⊢jsub (ren-lemma dd (Ren⊢-ext h))
           (ren-lemma dt h) (ren-lemma du h) (ren-lemma dp h)
           (⊢-cast (cong El (ren-comm ρ d t)) (ren-lemma de h)))
ren-lemma {ρ = ρ} (⊢tr {c = cM} {a = aM} {t = t} {u = u} dc da dv nc hc ha dt du dp de) h
  with posc-ren {ρ = ρ} (posc-Hom {c = cM} {a = aM} hc ha)
... | posc-Hom hc' ha' =
      ⊢-cast (cong El (sym (ren-comm ρ (⌜Hom⌝ cM aM (var vz)) u)))
        (⊢tr {c = renTm (extR ρ) cM} {a = renTm (extR ρ) aM}
             {t = renTm ρ t} {u = renTm ρ u}
             (ren-lemma dc (Ren⊢-ext h)) (ren-lemma da (Ren⊢-ext h))
             (ren-lemma dv (Ren⊢-ext h)) (nonatc-ren (extR ρ) nc) hc' ha'
             (ren-lemma dt h) (ren-lemma du h) (ren-lemma dp h)
             (⊢-cast (cong El (ren-comm ρ (⌜Hom⌝ cM aM (var vz)) t))
                     (ren-lemma de h)))
-- `⊢trU` — everything is DEFINITIONAL under renaming (the pinned `U`
-- ambient and `var vz` motive are renaming-invariant).
ren-lemma {ρ = ρ} (⊢ap {cA = cA} {cB = cB} {b = b} {t = t} {u = u}
                       dcA key dcB db dt du dp) h =
  ⊢-cast (Hom-cong₃ refl (sym (ren-comm ρ b t)) (sym (ren-comm ρ b u)))
    (⊢ap (ren-lemma dcA h) (trans (flat?-ren ρ cA) key)
         (ren-lemma dcB h)
         (⊢-cast (cong El (wk-ren-tm ρ cB)) (ren-lemma db (Ren⊢-ext h)))
         (ren-lemma dt h) (ren-lemma du h) (ren-lemma dp h))
ren-lemma (⊢trU dt du dp de) h =
  ⊢trU (ren-lemma dt h) (ren-lemma du h) (ren-lemma dp h) (ren-lemma de h)
ren-lemma {ρ = ρ} (⊢ref {d = d} p) h = ⊢-cast (sym (εwk-ren ρ (Defs.type 𝒮 d))) (⊢ref p)
ren-lemma {ρ = ρ} (⊢conv d c) h = ⊢conv (ren-lemma d h) (≅ᵀ-ren ρ c)

⊢wk : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
      Γ ⊢ t ∷ A → (Γ ▹ B) ⊢ renTm vs t ∷ renTy vs A
⊢wk d = ren-lemma d there

------------------------------------------------------------------------
-- Typed substitution preserves typing, and single substitution.
------------------------------------------------------------------------

Sub⊢ : (Γ Δ : Ctx) → Sub ⌊ Γ ⌋ ⌊ Δ ⌋ → Set
Sub⊢ Γ Δ σ = ∀ {x A} → Γ ∋ x ∷ A → Δ ⊢ subTm σ (var x) ∷ subTy σ A

Sub⊢-ext : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {C : RTy ⌊ Γ ⌋} →
           Sub⊢ Γ Δ σ → Sub⊢ (Γ ▹ C) (Δ ▹ subTy σ C) (extS σ)
Sub⊢-ext {σ = σ} {C = C} h here =
  ⊢-cast (sym (exts-wk-ty σ C)) (⊢var here)
Sub⊢-ext {σ = σ} h (there {A = A₀} v) =
  ⊢-cast (sym (exts-wk-ty σ A₀)) (⊢wk (h v))

-- the same, landing at a CONVERTIBLE extension type.
Sub⊢-ext-conv : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {C : RTy ⌊ Γ ⌋} {B : RTy ⌊ Δ ⌋} →
                Sub⊢ Γ Δ σ → subTy σ C ≅ᵀ B → Sub⊢ (Γ ▹ C) (Δ ▹ B) (extS σ)
Sub⊢-ext-conv {σ = σ} {C = C} h c here =
  ⊢-cast (sym (exts-wk-ty σ C)) (⊢conv (⊢var here) (≅ᵀ-ren vs (csymᵀ c)))
Sub⊢-ext-conv {σ = σ} h c (there {A = A₀} v) =
  ⊢-cast (sym (exts-wk-ty σ A₀)) (⊢wk (h v))

sub-lemma : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
            Γ ⊢ t ∷ A → Sub⊢ Γ Δ σ → Δ ⊢ subTm σ t ∷ subTy σ A
sub-ty : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
         Γ ⊢ty A → Sub⊢ Γ Δ σ → Δ ⊢ty subTy σ A

sub-ty ty-base      h = ty-base
sub-ty ty-Unit      h = ty-Unit
sub-ty ty-Nat       h = ty-Nat
sub-ty {σ = σ} (ty-IMu {I = I} dI dD di) h = ty-IMu (sub-lemma dI h) (⊢-cast (DescF-sub σ I) (sub-lemma dD h)) (sub-lemma di h)
sub-ty (ty-Desc dI) h = ty-Desc (sub-lemma dI h)
sub-ty {Δ = Δ} {σ = σ} (ty-DIh {I = I} {D = D} {M = M} dI dD dM dC dp) h =
  ty-DIh (sub-lemma dI h) (⊢-cast (DescF-sub σ I) (sub-lemma dD h))
    (subst (λ A → ((Δ ▹ El (subTm σ I)) ▹ A) ⊢ty subTy (extS (extS σ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-sub σ I) (wk-sub σ D))
             (sub-ty dM (Sub⊢-ext (Sub⊢-ext h))))
    (sub-lemma dC h) (sub-lemma dp h)
sub-ty (ty-Fin dn) h = ty-Fin (sub-lemma dn h)
sub-ty ty-U         h = ty-U
sub-ty (ty-Π dA dB) h = ty-Π (sub-ty dA h) (sub-ty dB (Sub⊢-ext h))
sub-ty (ty-Σ dA dB) h = ty-Σ (sub-ty dA h) (sub-ty dB (Sub⊢-ext h))
sub-ty (ty-El dc)   h = ty-El (sub-lemma dc h)
sub-ty (ty-Id dA dt du) h =
  ty-Id (sub-ty dA h) (sub-lemma dt h) (sub-lemma du h)
sub-ty (ty-Hom dA dt du) h =
  ty-Hom (sub-ty dA h) (sub-lemma dt h) (sub-lemma du h)

sub-lemma ⊢unit  h = ⊢unit
sub-lemma ⊢nzero h = ⊢nzero
sub-lemma (⊢nsuc dn) h = ⊢nsuc (sub-lemma dn h)
sub-lemma {σ = σ} (⊢natrec {M = M} {n = n} dM dz ds dn) h =
  ⊢-cast (sym (subTy-comm σ M n))
    (⊢natrec (sub-ty dM (Sub⊢-ext h))
             (⊢-cast (subTy-comm σ M nzero) (sub-lemma dz h))
             (⊢-cast (nrs-sub σ M) (sub-lemma ds (Sub⊢-ext (Sub⊢-ext h))))
             (sub-lemma dn h))
-- ★★ LEVITATION
sub-lemma {σ = σ} (⊢⌜IMu⌝ {I = I} dI dD di) h = ⊢⌜IMu⌝ (sub-lemma dI h) (⊢-cast (DescF-sub σ I) (sub-lemma dD h)) (sub-lemma di h)
sub-lemma (⊢⌜Fin⌝ dn) h = ⊢⌜Fin⌝ (sub-lemma dn h)
sub-lemma (⊢dι dI) h = ⊢dι (sub-lemma dI h)
sub-lemma {σ = σ} (⊢dσ {I = I} {S = S} dI dS df) h =
  ⊢dσ (sub-lemma dI h) (sub-lemma dS h)
      (⊢-cast (cong (λ X → Π (El (subTm σ S)) (Desc X)) (wk-sub σ I)) (sub-lemma df h))
sub-lemma (⊢dρ dI dj dC) h = ⊢dρ (sub-lemma dI h) (sub-lemma dj h) (sub-lemma dC h)
sub-lemma {σ = σ} (⊢dpay {I = I} dI dD dC) h = ⊢dpay (sub-lemma dI h) (⊢-cast (DescF-sub σ I) (sub-lemma dD h)) (sub-lemma dC h)
sub-lemma {σ = σ} (⊢con {I = I} dI dD di dp) h = ⊢con (sub-lemma dI h) (⊢-cast (DescF-sub σ I) (sub-lemma dD h)) (sub-lemma di h) (sub-lemma dp h)
sub-lemma {Δ = Δ} {σ = σ} (⊢dih {I = I} {D = D} {M = M} dI dD dM de dC dp) h =
  ⊢dih (sub-lemma dI h) (⊢-cast (DescF-sub σ I) (sub-lemma dD h))
    (subst (λ A → ((Δ ▹ El (subTm σ I)) ▹ A) ⊢ty subTy (extS (extS σ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-sub σ I) (wk-sub σ D))
             (sub-ty dM (Sub⊢-ext (Sub⊢-ext h))))
    (⊢-cast (MethTy-sub σ I D M) (sub-lemma de h))
    (sub-lemma dC h) (sub-lemma dp h)
sub-lemma {Δ = Δ} {σ = σ} (⊢ielim {I = I} {D = D} {M = M} {i = i} {t = t} dI dD dM de di dt) h =
  ⊢-cast (sym (iinst-sub σ M i t))
    (⊢ielim (sub-lemma dI h) (⊢-cast (DescF-sub σ I) (sub-lemma dD h))
      (subst (λ A → ((Δ ▹ El (subTm σ I)) ▹ A) ⊢ty subTy (extS (extS σ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-sub σ I) (wk-sub σ D))
             (sub-ty dM (Sub⊢-ext (Sub⊢-ext h))))
      (⊢-cast (MethTy-sub σ I D M) (sub-lemma de h))
      (sub-lemma di h) (sub-lemma dt h))
sub-lemma (⊢fzero dn) h = ⊢fzero (sub-lemma dn h)
sub-lemma (⊢fsuc dt) h = ⊢fsuc (sub-lemma dt h)
sub-lemma {σ = σ} (⊢fcase {P = P} {t = t} dP dt da db) h =
  ⊢-cast (sym (subTy-comm σ P t))
    (⊢fcase (sub-ty dP (Sub⊢-ext h)) (sub-lemma dt h)
            (⊢-cast (subTy-comm σ P fzero) (sub-lemma da h))
            (⊢-cast (fsucS-sub σ P) (sub-lemma db (Sub⊢-ext h))))
sub-lemma {σ = σ} (⊢fcase0 {P = P} {t = t} dP dt) h =
  ⊢-cast (sym (subTy-comm σ P t)) (⊢fcase0 (sub-ty dP (Sub⊢-ext h)) (sub-lemma dt h))
sub-lemma {σ = σ} (⊢psplit {P = P} {q = q} dA dB dP dq db) h =
  ⊢-cast (sym (subTy-comm σ P q))
    (⊢psplit (sub-ty dA h) (sub-ty dB (Sub⊢-ext h)) (sub-ty dP (Sub⊢-ext h)) (sub-lemma dq h)
             (⊢-cast (pairS-sub σ P) (sub-lemma db (Sub⊢-ext (Sub⊢-ext h)))))
sub-lemma (⊢var v) h = h v
sub-lemma (⊢lam dA d) h = ⊢lam (sub-ty dA h) (sub-lemma d (Sub⊢-ext h))
sub-lemma {σ = σ} (⊢app {B = D} {u = u} d₁ d₂) h =
  ⊢-cast (sym (subTy-comm σ D u)) (⊢app (sub-lemma d₁ h) (sub-lemma d₂ h))
sub-lemma {σ = σ} (⊢pair {B = B} {a = a} dB d₁ d₂) h =
  ⊢pair (sub-ty dB (Sub⊢-ext h))
        (sub-lemma d₁ h) (⊢-cast (subTy-comm σ B a) (sub-lemma d₂ h))
sub-lemma (⊢absurd dc de) h = ⊢absurd (sub-lemma dc h) (sub-lemma de h)
sub-lemma (⊢ordtr da dt du dp dq) h =
  ⊢ordtr (sub-lemma da h) (sub-lemma dt h) (sub-lemma du h)
         (sub-lemma dp h) (sub-lemma dq h)
sub-lemma (⊢fst d) h = ⊢fst (sub-lemma d h)
sub-lemma {σ = σ} (⊢snd {B = B} {p = p} d) h =
  ⊢-cast (sym (subTy-comm σ B (fst p))) (⊢snd (sub-lemma d h))
sub-lemma ⊢⌜base⌝ h = ⊢⌜base⌝
sub-lemma ⊢⌜Nat⌝ h = ⊢⌜Nat⌝
sub-lemma ⊢⌜Unit⌝ h = ⊢⌜Unit⌝
sub-lemma (⊢⌜Π⌝ dc dd) h = ⊢⌜Π⌝ (sub-lemma dc h) (sub-lemma dd (Sub⊢-ext h))
sub-lemma (⊢⌜Σ⌝ dc dd) h = ⊢⌜Σ⌝ (sub-lemma dc h) (sub-lemma dd (Sub⊢-ext h))
sub-lemma (⊢⌜Hom⌝ dc da db) h =
  ⊢⌜Hom⌝ (sub-lemma dc h) (sub-lemma da h) (sub-lemma db h)
sub-lemma (⊢hrefl dc dt) h = ⊢hrefl (sub-lemma dc h) (sub-lemma dt h)
sub-lemma (⊢⌜Id⌝ dc da db) h =
  ⊢⌜Id⌝ (sub-lemma dc h) (sub-lemma da h) (sub-lemma db h)
sub-lemma (⊢idrefl dc dt) h = ⊢idrefl (sub-lemma dc h) (sub-lemma dt h)
sub-lemma {σ = σ} (⊢jsub {d = d} {t = t} {u = u} dd dt du dp de) h =
  ⊢-cast (cong El (sym (sub-comm σ d u)))
    (⊢jsub (sub-lemma dd (Sub⊢-ext h))
           (sub-lemma dt h) (sub-lemma du h) (sub-lemma dp h)
           (⊢-cast (cong El (sub-comm σ d t)) (sub-lemma de h)))
sub-lemma {σ = σ} (⊢tr {c = cM} {a = aM} {t = t} {u = u} dc da dv nc hc ha dt du dp de) h
  with posc-sub {σ = σ} (posc-Hom {c = cM} {a = aM} hc ha)
... | posc-Hom hc' ha' =
      ⊢-cast (cong El (sym (sub-comm σ (⌜Hom⌝ cM aM (var vz)) u)))
        (⊢tr {c = subTm (extS σ) cM} {a = subTm (extS σ) aM}
             {t = subTm σ t} {u = subTm σ u}
             (sub-lemma dc (Sub⊢-ext h)) (sub-lemma da (Sub⊢-ext h))
             (sub-lemma dv (Sub⊢-ext h)) (nonatc-sub (extS σ) nc) hc' ha'
             (sub-lemma dt h) (sub-lemma du h) (sub-lemma dp h)
             (⊢-cast (cong El (sub-comm σ (⌜Hom⌝ cM aM (var vz)) t))
                     (sub-lemma de h)))
sub-lemma {σ = σ} (⊢ap {cA = cA} {cB = cB} {b = b} {t = t} {u = u}
                       dcA key dcB db dt du dp) h =
  ⊢-cast (Hom-cong₃ refl (sym (sub-comm σ b t)) (sym (sub-comm σ b u)))
    (⊢ap (sub-lemma dcA h) (flat?-sub σ cA key)
         (sub-lemma dcB h)
         (⊢-cast (cong El (wk-sub-tm σ cB)) (sub-lemma db (Sub⊢-ext h)))
         (sub-lemma dt h) (sub-lemma du h) (sub-lemma dp h))
sub-lemma (⊢trU dt du dp de) h =
  ⊢trU (sub-lemma dt h) (sub-lemma du h) (sub-lemma dp h) (sub-lemma de h)
sub-lemma {σ = σ} (⊢ref {d = d} p) h = ⊢-cast (sym (εwk-sub σ (Defs.type 𝒮 d))) (⊢ref p)
sub-lemma {σ = σ} (⊢conv d c) h = ⊢conv (sub-lemma d h) (≅ᵀ-sub σ c)

-- the single substitution AS a typed substitution — `⊢[]` is its
-- instantiation, and `sr`'s `natrec-suc` case needs it standalone (to
-- substitute the recursor's OUTER binder, under the IH binder).
⊢single : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {a : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ A → Sub⊢ (Γ ▹ A) Γ (single a)
⊢single {A = A} {a = a} da here = ⊢-cast (sym (wk-cancel a A)) da
⊢single {a = a} da (there {A = A₀} v) = ⊢-cast (sym (wk-cancel a A₀)) (⊢var v)

⊢[] : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {t : RTm (⌊ Γ ⌋ ∙)} {B : RTy (⌊ Γ ⌋ ∙)}
      {a : RTm ⌊ Γ ⌋} →
      (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ a ∷ A → Γ ⊢ subTm (single a) t ∷ subTy (single a) B
⊢[] dt da = sub-lemma dt (⊢single da)

-- Context conversion: converting the LAST context entry along `≅ᵀ`. Derived
-- from the substitution lemma (identity substitution, with `⊢conv` at `vz`),
-- sidestepping the induction-on-derivation obstruction.
conv-ctx : {Γ : Ctx} {A A' : RTy ⌊ Γ ⌋} → A ≅ᵀ A' →
           {t : RTm (⌊ Γ ⌋ ∙)} {B : RTy (⌊ Γ ⌋ ∙)} →
           (Γ ▹ A) ⊢ t ∷ B → (Γ ▹ A') ⊢ t ∷ B
conv-ctx {Γ} {A} {A'} c {t} {B} d =
  ⊢-cast (subTy-id B)
    (subst (λ z → (Γ ▹ A') ⊢ z ∷ subTy idₛ B) (subTm-id t) (sub-lemma d idₛ⊢))
  where
  idₛ⊢ : Sub⊢ (Γ ▹ A) (Γ ▹ A') idₛ
  idₛ⊢ here =
    ⊢-cast (sym (subTy-id (renTy vs A))) (⊢conv (⊢var here) (csymᵀ (≅ᵀ-ren vs c)))
  idₛ⊢ (there {A = A₀} v) =
    ⊢-cast (sym (subTy-id (renTy vs A₀))) (⊢var (there v))

-- the same, for a TYPE under the converted entry (a motive whose
--   context mentions a description that stepped).
conv-ctxᵀ : {Γ : Ctx} {A A' : RTy ⌊ Γ ⌋} → A ≅ᵀ A' →
            {B : RTy (⌊ Γ ⌋ ∙)} → (Γ ▹ A) ⊢ty B → (Γ ▹ A') ⊢ty B
conv-ctxᵀ {Γ} {A} {A'} c {B} d =
  subst (λ z → (Γ ▹ A') ⊢ty z) (subTy-id B) (sub-ty d idₛ⊢)
  where
  idₛ⊢ : Sub⊢ (Γ ▹ A) (Γ ▹ A') idₛ
  idₛ⊢ here =
    ⊢-cast (sym (subTy-id (renTy vs A))) (⊢conv (⊢var here) (csymᵀ (≅ᵀ-ren vs c)))
  idₛ⊢ (there {A = A₀} v) =
    ⊢-cast (sym (subTy-id (renTy vs A₀))) (⊢var (there v))

------------------------------------------------------------------------
-- ★ LEVITATION: instantiating the TWO-SLOT motive at a well-typed index
--   and scrutinee yields a well-formed type.  Two `⊢single`s; the
--   scrutinee's slot mentions the weakened index code and description,
--   which the outer `single` cancels.
------------------------------------------------------------------------

iinst-wf : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} (M : RTy ((⌊ Γ ⌋ ∙) ∙)) (j t : RTm ⌊ Γ ⌋) →
           Γ ⊢ j ∷ El I → Γ ⊢ t ∷ IMu I D j → motCtx Γ I D ⊢ty M →
           Γ ⊢ty iinst j t M
iinst-wf {Γ} {I} {D} M j t dj dt dM =
  sub-ty (sub-ty dM (Sub⊢-ext (⊢single dj)))
         (⊢single (⊢-cast (cong₂ (λ a b → IMu a b j) (sym (wk-cancel-tm j I)) (sym (wk-cancel-tm j D))) dt))

