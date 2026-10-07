-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
import DirectedHoTT.Spec.Typing as Ty
module DirectedHoTT.Metatheory.SubjectReduction (𝒮 : KSig) (n : ℕ) (ok : Ty.EntriesOK 𝒮 n) where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ ; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; Thin; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var
        ; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝
        ; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub; Id-cong₃; ⌜Id⌝-cong₃
        ; jsub-cong₃; Unit; Nat; unit; nzero; nsuc; natrec; ⌜Nat⌝; ⌜Unit⌝; Ren
        ; extR; renTm; renTy; Sub; extS; subTm; subTy; idₛ; _∘ᵣ_; _ₛ∘ᵣ_; _ᵣ∘ₛ_
        ; _∘ₛ_; subTy-renTy; renTy-subTy; subTy-subTy; renTy-renTy; subTy-cong
        ; renTy-cong; subTy-id; subTm-renTm; subTm-id; subTm-cong; renTm-renTm
        ; renTm-subTm; ⌜Hom⌝-cong₃; Hom-cong₃; ordtr-cong₅; Desc; con; dι; dρ
        ; IMu; ielim; ⌜IMu⌝; εwkTy; εwk-ren; εwk-sub; εwkTm; εwkTm-ren
        ; εwkTm-sub; subTm-subTm
        ; DIh; Fin; ⌜Fin⌝; dσ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit; cong₄; cong₃
        ; ref )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; _∨_; occTm; ∨-false; ∨-false₁; ∨-false₂; occ-ren-eq
        ; occ-sub; eqv; Avoids; occ-ren-tm; avoids-wk; PosC; posc-var
        ; posc-Hom; posc-ren; posc-sub; pw?; stkC?; pwDom; pwBody; pwShift
        ; pw?-sub; stkC?-sub; pwBody-sub; pwDom-sub; pwBody-occ; ren-as-sub
        ; avoids-pwShift; subTm-occ; stkC?-ren; wk-ren-tm; wk-sub-tm; flat?
        ; flat→stk; flat?-ren; flat?-sub; NoNatC; nnc-base; nnc-Unit; nnc-Fin; nnc-Π
        ; nnc-Σ; nnc-Hom; nnc-Id; nonatc-ren; nonatc-sub; nonatc-pwBody; stkA?
        ; stkA?-ren; stkA?-sub; stkC?→stkA?; NoNatHd; nnh-base; nnh-Unit
        ; nnh-Σ; nnh-Id; nnh-Π; nnh-Hom; nnh-IMu; nonatc→hd; stkC?→hd
        ; occ-εwkTm
        ; nnh-Fin )
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
        ; crfl
        ; El-⌜Fin⌝; DIh-ι; DIh-σ; DIh-ρ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-Fin; ξ-⌜Fin⌝; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dσˢ; ξ-dσᶠ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ; ξ-psplitᵍ; tr-J-Fin; ⊢⌜Fin⌝; ⊢dι; ⊢dσ; ⊢dρ; ⊢dpay; ⊢dih; ⊢fzero; ⊢fsuc; ⊢fcase; ⊢fcase0; ⊢psplit; ty-Desc; ty-DIh; ty-Fin; MethTy; motCtx; methS; wk2M; single2; pairS; fsucS; DescF
        ; δref; ⊢ref; okBody )
import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 as ᴵSubjectReductionBase
open ᴵSubjectReductionBase using ( ≅ᵀ-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.Confluence 𝒮
  using ( ⟶-ren; ⟶*-ren; ⟶*-appʳ; ren-comm; subTm-monoˢ; extS-mono; single-mono
        ; stkC?-red; stkA?-red; church-rosser
        ; ⟶*-trans; ⟶*-dpayᴵ; ⟶*-dpayᴰ; ⟶*-dpayᶜ; ⟶*-appˡ )
open ᴵSubjectReductionBase using ( sub-comm; ⟶ᵀ-sub )
open import DirectedHoTT.Metatheory.Injectivity 𝒮
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El
        ; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ
        ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; red→≅ᵀ; Π-inj; Σ-inj
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; Id-reduct
        ; church-rosserᵀ; Π-reduct; ΠRed; mkΠRed
        ; ⟶ᵀ*-IMu; IMu-inj; IMu-reduct; IMuRed; mkIMuRed
        ; Desc-inj; Fin-inj; nsuc-inj≅; Fin-cong≅; ⟶ᵀ*-Desc )

private
  variable
    Γ Δ : Cx


------------------------------------------------------------------------
-- ★★★ THE STRUCTURAL TYPING LEMMAS MOVED TO `Metatheory/TySub` and are
--   re-exported here, so every existing importer is unaffected.
--
-- ⚠⚠ THE REASON IS A CONSUMPTION MISMATCH, MEASURED.  ~100 modules import
--   this one; roughly NINETY use exactly ONE name from it — `⊢wk` — and
--   only EIGHT want `sr`/`sr*`/the indexed-ι lemmas it is named for.  This
--   module depends on `Confluence` (8.9 MB) and `Injectivity` (5.4 MB), so
--   the ninety were deserializing the whole confluence proof to weaken a
--   derivation.  `--profile=all`: ~70% deserialization, ~0ms typing.
--
-- ★ WHAT STAYS: the reduct analyses below (the only users of `Π-reduct`
--   and `church-rosserᵀ`), `ipayTy-conv` (the only user of
--   `church-rosser`), generation, the pw decode joins, `sr`, `sr*` and
--   the ι/indexed-ι lemmas.  Everything else is in `TySub`.
------------------------------------------------------------------------

open import DirectedHoTT.Metatheory.TySub 𝒮 n
open import DirectedHoTT.Metatheory.SubjectReduction.Red 𝒮 public
open import DirectedHoTT.Metatheory.RedCong 𝒮


-- application with the argument typed at a propositionally equal domain;
--   leaves the codomain for Agda to read off the function's type.
⊢app-cast : {Γ : Ctx} {A A' : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} {t u : RTm ⌊ Γ ⌋} →
            A ≡ A' → Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A' → Γ ⊢ app t u ∷ subTy (single u) B
⊢app-cast refl dt du = ⊢app dt du

-- the two-slot single substitution as a typed substitution
⊢single2 : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} {x y : RTm ⌊ Γ ⌋} →
           Γ ⊢ x ∷ A → Γ ⊢ y ∷ subTy (single x) B → Sub⊢ ((Γ ▹ A) ▹ B) Γ (single2 x y)
⊢single2 {B = B} {x = x} {y = y} dx dy here = ⊢-cast (sym (s2-wk x y B)) dy
⊢single2 {A = A} {x = x} {y = y} dx dy (there here) = ⊢-cast (sym (s2-cancel x y A)) dx
⊢single2 {x = x} {y = y} dx dy (there (there {A = A₀} v)) =
  ⊢-cast (sym (s2-cancel x y A₀)) (⊢var v)

------------------------------------------------------------------------
-- Generation (inversion through `⊢conv`).
------------------------------------------------------------------------

gen-lam : {Γ : Ctx} {s : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} → Γ ⊢ lam s ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (C ≅ᵀ Π A B) × ((Γ ⊢ty A) × ((Γ ▹ A) ⊢ s ∷ B))))
-- ⚠ now also returns the DOMAIN's well-formedness: `sr`'s `ξ-lam` case
-- reconstructs a `⊢lam`, which needs it (2026-07-30, option A).
gen-lam (⊢lam dA d) = _ , (_ , (crflᵀ , (dA , d)))
gen-lam (⊢conv d c) with gen-lam d
... | A , (B , (c' , (dA , ds))) = A , (B , (ctrnᵀ (csymᵀ c) c' , (dA , ds)))

gen-app : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ app t u ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ t ∷ Π A B) × ((Γ ⊢ u ∷ A) × (C ≅ᵀ subTy (single u) B))))
gen-app (⊢app d₁ d₂) = _ , (_ , (d₁ , (d₂ , crflᵀ)))
gen-app (⊢conv d c) with gen-app d
... | A , (B , (d₁ , (d₂ , c'))) = A , (B , (d₁ , (d₂ , ctrnᵀ (csymᵀ c) c')))

gen-pair : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ pair a b ∷ C →
           Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
             (C ≅ᵀ Σ' A B) ×
             (((Γ ▹ A) ⊢ty B) × ((Γ ⊢ a ∷ A) × (Γ ⊢ b ∷ subTy (single a) B)))))
-- ⚠ likewise returns the CODOMAIN's well-formedness, for `sr`'s `ξ-pair*`.
gen-pair (⊢pair dB da db) = _ , (_ , (crflᵀ , (dB , (da , db))))
gen-pair (⊢conv d c) with gen-pair d
... | A , (B , (c' , (dB , (da , db)))) =
      A , (B , (ctrnᵀ (csymᵀ c) c' , (dB , (da , db))))

gen-fst : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fst p ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ p ∷ Σ' A B) × (C ≅ᵀ A)))
gen-fst (⊢fst d) = _ , (_ , (d , crflᵀ))
gen-fst (⊢conv d c) with gen-fst d
... | A , (B , (dp , c')) = A , (B , (dp , ctrnᵀ (csymᵀ c) c'))

gen-snd : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ snd p ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ p ∷ Σ' A B) × (C ≅ᵀ subTy (single (fst p)) B)))
gen-snd (⊢snd d) = _ , (_ , (d , crflᵀ))
gen-snd (⊢conv d c) with gen-snd d
... | A , (B , (dp , c')) = A , (B , (dp , ctrnᵀ (csymᵀ c) c'))

gen-⌜Π⌝ : {Γ : Ctx} {c : RTm ⌊ Γ ⌋} {d : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
          Γ ⊢ ⌜Π⌝ c d ∷ C →
          (Γ ⊢ c ∷ U) × (((Γ ▹ El c) ⊢ d ∷ U) × (C ≅ᵀ U))
gen-⌜Π⌝ (⊢⌜Π⌝ dc dd) = dc , (dd , crflᵀ)
gen-⌜Π⌝ (⊢conv d c) with gen-⌜Π⌝ d
... | (dc , (dd , c')) = dc , (dd , ctrnᵀ (csymᵀ c) c')

gen-⌜Σ⌝ : {Γ : Ctx} {c : RTm ⌊ Γ ⌋} {d : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
          Γ ⊢ ⌜Σ⌝ c d ∷ C →
          (Γ ⊢ c ∷ U) × (((Γ ▹ El c) ⊢ d ∷ U) × (C ≅ᵀ U))
gen-⌜Σ⌝ (⊢⌜Σ⌝ dc dd) = dc , (dd , crflᵀ)
gen-⌜Σ⌝ (⊢conv d c) with gen-⌜Σ⌝ d
... | (dc , (dd , c')) = dc , (dd , ctrnᵀ (csymᵀ c) c')

gen-var : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ var x ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → (Γ ∋ x ∷ A) × (C ≅ᵀ A))
gen-var (⊢var v) = _ , (v , crflᵀ)
gen-var (⊢conv d c) with gen-var d
... | A , (v , c') = A , (v , ctrnᵀ (csymᵀ c) c')

gen-⌜Hom⌝ : {Γ : Ctx} {c a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ ⌜Hom⌝ c a b ∷ C →
            (Γ ⊢ c ∷ U) × ((Γ ⊢ a ∷ El c) × ((Γ ⊢ b ∷ El c) × (C ≅ᵀ U)))
gen-⌜Hom⌝ (⊢⌜Hom⌝ dc da db) = dc , (da , (db , crflᵀ))
gen-⌜Hom⌝ (⊢conv d c) with gen-⌜Hom⌝ d
... | (dc , (da , (db , c'))) = dc , (da , (db , ctrnᵀ (csymᵀ c) c'))

-- ★ stage D: ex falso inverts like `hrefl` — the code determines the
-- type, so the conversion is the only thing `⊢conv` can have added.
gen-absurd : {Γ : Ctx} {c e₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ absurd c e₀ ∷ C →
             (Γ ⊢ c ∷ U) × ((Γ ⊢ e₀ ∷ base) × (C ≅ᵀ El c))
gen-absurd (⊢absurd dc de) = dc , (de , crflᵀ)
gen-absurd (⊢conv d c) with gen-absurd d
... | (dc , (de , c')) = dc , (de , ctrnᵀ (csymᵀ c) c')

-- ★ the order's inversion.  `⊢ordtr`'s result type `Hom Nat a u` is
-- FIXED by the rule (no motive to guess), so unlike `gen-natrec` there
-- is nothing existential to recover — five premises and a conversion.
gen-ordtr : {Γ : Ctx} {a t u p q : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ ordtr a t u p q ∷ C →
            (Γ ⊢ a ∷ Nat) × ((Γ ⊢ t ∷ Nat) × ((Γ ⊢ u ∷ Nat) ×
            ((Γ ⊢ p ∷ Hom Nat a t) × ((Γ ⊢ q ∷ Hom Nat t u) ×
             (C ≅ᵀ Hom Nat a u)))))
gen-ordtr (⊢ordtr da dt du dp dq) =
  da , (dt , (du , (dp , (dq , crflᵀ))))
gen-ordtr (⊢conv d c) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , c')))) =
      da , (dt , (du , (dp , (dq , ctrnᵀ (csymᵀ c) c'))))

gen-hrefl : {Γ : Ctx} {c t₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ hrefl c t₀ ∷ C →
            (Γ ⊢ c ∷ U) × ((Γ ⊢ t₀ ∷ El c) × (C ≅ᵀ Hom (El c) t₀ t₀))
gen-hrefl (⊢hrefl dc dt) = dc , (dt , crflᵀ)
gen-hrefl (⊢conv d c) with gen-hrefl d
... | (dc , (dt , c')) = dc , (dt , ctrnᵀ (csymᵀ c) c')

gen-⌜Id⌝ : {Γ : Ctx} {c a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ ⌜Id⌝ c a b ∷ C →
           (Γ ⊢ c ∷ U) × ((Γ ⊢ a ∷ El c) × ((Γ ⊢ b ∷ El c) × (C ≅ᵀ U)))
gen-⌜Id⌝ (⊢⌜Id⌝ dc da db) = dc , (da , (db , crflᵀ))
gen-⌜Id⌝ (⊢conv d c) with gen-⌜Id⌝ d
... | (dc , (da , (db , c'))) = dc , (da , (db , ctrnᵀ (csymᵀ c) c'))

-- ★ WF stage A generation lemmas.
gen-nsuc : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ nsuc n ∷ C → (Γ ⊢ n ∷ Nat) × (C ≅ᵀ Nat)
gen-nsuc (⊢nsuc dn)  = dn , crflᵀ
gen-nsuc (⊢conv d c) with gen-nsuc d
... | (dn , c') = dn , ctrnᵀ (csymᵀ c) c'

gen-natrec : {Γ : Ctx} {z : RTm ⌊ Γ ⌋} {s₀ : RTm ((⌊ Γ ⌋ ∙) ∙)}
             {n : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ natrec z s₀ n ∷ C →
             Σ (RTy (⌊ Γ ⌋ ∙)) (λ M →
               ((Γ ▹ Nat) ⊢ty M) ×
               ((Γ ⊢ z ∷ subTy (single nzero) M) ×
               ((((Γ ▹ Nat) ▹ M) ⊢ s₀ ∷ subTy nrs M) ×
               ((Γ ⊢ n ∷ Nat) × (C ≅ᵀ subTy (single n) M)))))
gen-natrec (⊢natrec dM dz ds dn) = _ , (dM , (dz , (ds , (dn , crflᵀ))))
gen-natrec (⊢conv d c) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , c')))) =
      M , (dM , (dz , (ds , (dn , ctrnᵀ (csymᵀ c) c'))))

gen-idrefl : {Γ : Ctx} {c t₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ idrefl c t₀ ∷ C →
             (Γ ⊢ c ∷ U) × ((Γ ⊢ t₀ ∷ El c) × (C ≅ᵀ Id (El c) t₀ t₀))
gen-idrefl (⊢idrefl dc dt) = dc , (dt , crflᵀ)
gen-idrefl (⊢conv d c) with gen-idrefl d
... | (dc , (dt , c')) = dc , (dt , ctrnᵀ (csymᵀ c) c')

gen-jsub : {Γ : Ctx} {d₀ : RTm (⌊ Γ ⌋ ∙)} {p e : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ jsub d₀ p e ∷ C →
           Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTm ⌊ Γ ⌋) (λ t → Σ (RTm ⌊ Γ ⌋) (λ u →
             (((Γ ▹ A) ⊢ d₀ ∷ U) ×
             ((Γ ⊢ t ∷ A) × ((Γ ⊢ u ∷ A) ×
             ((Γ ⊢ p ∷ Id A t u) ×
             ((Γ ⊢ e ∷ El (subTm (single t) d₀)) ×
              (C ≅ᵀ El (subTm (single u) d₀))))))))))
gen-jsub (⊢jsub dd dt du dp de) =
  _ , (_ , (_ , (dd , (dt , (du , (dp , (de , crflᵀ)))))))
gen-jsub (⊢conv d c) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , c'))))))) =
      A , (t , (u , (dd , (dt , (du , (dp , (de , ctrnᵀ (csymᵀ c) c')))))))

gen-ap : {Γ : Ctx} {cB : RTm ⌊ Γ ⌋} {b : RTm (⌊ Γ ⌋ ∙)} {p : RTm ⌊ Γ ⌋}
         {C : RTy ⌊ Γ ⌋} → Γ ⊢ ap cB b p ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ cA → Σ (RTm ⌊ Γ ⌋) (λ t → Σ (RTm ⌊ Γ ⌋) (λ u →
           (Γ ⊢ cA ∷ U) × ((flat? cA ≡ true) × ((Γ ⊢ cB ∷ U) ×
           (((Γ ▹ El cA) ⊢ b ∷ El (renTm vs cB)) ×
           ((Γ ⊢ t ∷ El cA) × ((Γ ⊢ u ∷ El cA) ×
           ((Γ ⊢ p ∷ Hom (El cA) t u) ×
           (C ≅ᵀ Hom (El cB) (subTm (single t) b) (subTm (single u) b)))))))))))
gen-ap (⊢ap dcA key dcB db dt du dp) =
  _ , (_ , (_ , (dcA , (key , (dcB , (db , (dt , (du , (dp , crflᵀ)))))))))
gen-ap (⊢conv d c) with gen-ap d
... | cA , (t , (u , (dcA , (key , (dcB , (db , (dt , (du , (dp , c'))))))))) =
      cA , (t , (u , (dcA , (key , (dcB , (db ,
        (dt , (du , (dp , ctrnᵀ (csymᵀ c) c')))))))))

-- CONTEXT CONVERSION at the top entry — payable through `sub-lemma`
-- with the identity substitution (the derivation's var-here uses the
-- conversion; everything else is untouched).
ctx-conv : {Γ : Ctx} {A A' : RTy ⌊ Γ ⌋} {t : RTm (⌊ Γ ⌋ ∙)}
           {D : RTy (⌊ Γ ⌋ ∙)} →
           (Γ ▹ A) ⊢ t ∷ D → A' ≅ᵀ A → (Γ ▹ A') ⊢ t ∷ D
ctx-conv {Γ = Γ} {A = A} {A' = A'} {t = t} {D = D} d cA =
  subst₂-⊢ (subTm-id t) (subTy-id D) (sub-lemma d idσ⊢)
  where
  subst₂-⊢ : {Δ : Ctx} {t₁ t₂ : RTm ⌊ Δ ⌋} {D₁ D₂ : RTy ⌊ Δ ⌋} →
             t₁ ≡ t₂ → D₁ ≡ D₂ → Δ ⊢ t₁ ∷ D₁ → Δ ⊢ t₂ ∷ D₂
  subst₂-⊢ refl refl d₀ = d₀
  idσ⊢ : Sub⊢ (Γ ▹ A) (Γ ▹ A') idₛ
  idσ⊢ here = ⊢-cast (sym (subTy-id _))
                     (⊢conv (⊢var here) (≅ᵀ-ren vs cA))
  idσ⊢ (there v) = ⊢-cast (sym (subTy-id _)) (⊢var (there v))

-- ★ the WORKHORSE: a member of a pw-able decoded type, weakened and
-- applied at the fresh domain variable, lands in the pointwise body.
pw-app : {Γ : Ctx} {C : RTm ⌊ Γ ⌋} {w : RTm ⌊ Γ ⌋} →
         Γ ⊢ w ∷ El C → (key : pw? C ≡ true) →
         (Γ ▹ El (pwDom C)) ⊢ app (renTm vs w) (var vz) ∷ El (pwBody C)
pw-app {Γ = Γ} {C = C} {w = w} dw key with pw-El-decode C key
... | Body , (ch₁ , ch₂) =
  ⊢conv
    (⊢-cast (wk-inst-ty Body)
      (⊢app (⊢conv (⊢wk dw) (red→≅ᵀ (⟶ᵀ*-ren vs ch₁))) (⊢var here)))
    (csymᵀ (red→≅ᵀ ch₂))

-- typing of the pointwise dom/body codes, by spine induction.
pw-gen : {Γ : Ctx} {C : RTm ⌊ Γ ⌋} →
         Γ ⊢ C ∷ U → (key : pw? C ≡ true) →
         (Γ ⊢ pwDom C ∷ U) × ((Γ ▹ El (pwDom C)) ⊢ pwBody C ∷ U)
pw-gen {C = var v} d ()
pw-gen {C = lam t} d ()
pw-gen {C = app t u} d ()
pw-gen {C = pair a b} d ()
pw-gen {C = fst t} d ()
pw-gen {C = snd t} d ()
pw-gen {C = ⌜base⌝} d ()
pw-gen {C = ⌜Π⌝ γ δ} d key with gen-⌜Π⌝ d
... | (dγ , (dδ , _)) = dγ , dδ
pw-gen {C = ⌜Σ⌝ c d₁} d ()
pw-gen {C = ⌜Hom⌝ C a b} d key with gen-⌜Hom⌝ d
... | (dC , (da , (db , _))) with pw-gen dC key
...   | (dDom , dBody) =
      dDom , ⊢⌜Hom⌝ dBody (pw-app da key) (pw-app db key)
pw-gen {C = hrefl c t} d ()
pw-gen {C = tr d₁ p e} d ()

-- Inversion for `⊢tr` (stage 2: the composition motive, pinned in the
-- rule).  `deq` records that ANY typeable `tr`-motive has that shape.
record TrInv (Γ : Ctx) (d₀ : RTm (⌊ Γ ⌋ ∙)) (p e : RTm ⌊ Γ ⌋)
             (C : RTy ⌊ Γ ⌋) : Set where
  constructor mkTrInv
  field
    cM aM : RTm (⌊ Γ ⌋ ∙)
    deq  : d₀ ≡ ⌜Hom⌝ cM aM (var vz)
    A    : RTy ⌊ Γ ⌋
    t u  : RTm ⌊ Γ ⌋
    dcM  : (Γ ▹ A) ⊢ cM ∷ U
    daM  : (Γ ▹ A) ⊢ aM ∷ El cM
    dvM  : (Γ ▹ A) ⊢ var vz ∷ El cM
    ncM  : NoNatC cM
    hcM  : occTm vz cM ≡ false
    haM  : occTm vz aM ≡ false
    dt   : Γ ⊢ t ∷ A
    du   : Γ ⊢ u ∷ A
    dp   : Γ ⊢ p ∷ Hom A t u
    de   : Γ ⊢ e ∷ El (subTm (single t) (⌜Hom⌝ cM aM (var vz)))
    cC   : C ≅ᵀ El (subTm (single u) (⌜Hom⌝ cM aM (var vz)))

-- ...and the TAUT rule's inversion (`⊢trU`, motive pinned `var vz`).
record TrInvU (Γ : Ctx) (d₀ : RTm (⌊ Γ ⌋ ∙)) (p e : RTm ⌊ Γ ⌋)
              (C : RTy ⌊ Γ ⌋) : Set where
  constructor mkTrInvU
  field
    deq : d₀ ≡ var vz
    t u : RTm ⌊ Γ ⌋
    dt  : Γ ⊢ t ∷ U
    du  : Γ ⊢ u ∷ U
    dp  : Γ ⊢ p ∷ Hom U t u
    de  : Γ ⊢ e ∷ El t
    cC  : C ≅ᵀ El u

data TrGen (Γ : Ctx) (d₀ : RTm (⌊ Γ ⌋ ∙)) (p e : RTm ⌊ Γ ⌋)
           (C : RTy ⌊ Γ ⌋) : Set where
  tgC : TrInv  Γ d₀ p e C → TrGen Γ d₀ p e C
  tgU : TrInvU Γ d₀ p e C → TrGen Γ d₀ p e C

gen-tr : {Γ : Ctx} {d₀ : RTm (⌊ Γ ⌋ ∙)} {p e : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
         Γ ⊢ tr d₀ p e ∷ C → TrGen Γ d₀ p e C
gen-tr (⊢tr dc da dv nc hc ha dt du dp de) =
  tgC (mkTrInv _ _ refl _ _ _ dc da dv nc hc ha dt du dp de crflᵀ)
gen-tr (⊢trU dt du dp de) = tgU (mkTrInvU refl _ _ dt du dp de crflᵀ)
gen-tr (⊢conv d c) with gen-tr d
... | tgC (mkTrInv cM aM deq A t u dc da dv nc hc ha dt du dp de cC) =
      tgC (mkTrInv cM aM deq A t u dc da dv nc hc ha dt du dp de
                   (ctrnᵀ (csymᵀ c) cC))
... | tgU (mkTrInvU deq t u dt du dp de cC) =
      tgU (mkTrInvU deq t u dt du dp de (ctrnᵀ (csymᵀ c) cC))

------------------------------------------------------------------------
-- ★ SUBJECT REDUCTION.
------------------------------------------------------------------------

sr : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A
-- ★★ LEVITATION: generation lemmas for the levitated formers — the rule,
--   then `⊢conv` composing the conversion (the file's two-clause shape).
gen-con : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ con p ∷ C →
          Σ (RTm ⌊ Γ ⌋) (λ I → Σ (RTm ⌊ Γ ⌋) (λ D → Σ (RTm ⌊ Γ ⌋) (λ i →
            (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ DescF I) × ((Γ ⊢ i ∷ El I) ×
            ((Γ ⊢ p ∷ El (dpay I D (app D i))) × (C ≅ᵀ IMu I D i)))))))
gen-con (⊢con dI dD di dp) = _ , (_ , (_ , (dI , (dD , (di , (dp , crflᵀ))))))
gen-con (⊢conv d c) with gen-con d
... | I , (D , (i , (dI , (dD , (di , (dp , c')))))) =
      I , (D , (i , (dI , (dD , (di , (dp , ctrnᵀ (csymᵀ c) c'))))))

gen-ielim : {Γ : Ctx} {D i e t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ielim D i e t ∷ C →
            Σ (RTm ⌊ Γ ⌋) (λ I → Σ (RTy ((⌊ Γ ⌋ ∙) ∙)) (λ M →
              (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ DescF I) × ((motCtx Γ I D ⊢ty M) ×
              ((Γ ⊢ e ∷ MethTy I D M) × ((Γ ⊢ i ∷ El I) ×
              ((Γ ⊢ t ∷ IMu I D i) × (C ≅ᵀ iinst i t M))))))))
gen-ielim (⊢ielim dI dD dM de di dt) = _ , (_ , (dI , (dD , (dM , (de , (di , (dt , crflᵀ)))))))
gen-ielim (⊢conv d c) with gen-ielim d
... | I , (M , (dI , (dD , (dM , (de , (di , (dt , c'))))))) =
      I , (M , (dI , (dD , (dM , (de , (di , (dt , ctrnᵀ (csymᵀ c) c')))))))

gen-⌜IMu⌝ : {Γ : Ctx} {I D i : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜IMu⌝ I D i ∷ C →
            (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ DescF I) × ((Γ ⊢ i ∷ El I) × (C ≅ᵀ U)))
gen-⌜IMu⌝ (⊢⌜IMu⌝ dI dD di) = dI , (dD , (di , crflᵀ))
gen-⌜IMu⌝ (⊢conv d c) with gen-⌜IMu⌝ d
... | dI , (dD , (di , c')) = dI , (dD , (di , ctrnᵀ (csymᵀ c) c'))

gen-⌜Fin⌝ : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜Fin⌝ n ∷ C → (Γ ⊢ n ∷ Nat) × (C ≅ᵀ U)
gen-⌜Fin⌝ (⊢⌜Fin⌝ dn) = dn , crflᵀ
gen-⌜Fin⌝ (⊢conv d c) with gen-⌜Fin⌝ d
... | dn , c' = dn , ctrnᵀ (csymᵀ c) c'

gen-dι : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dι ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ I → (Γ ⊢ I ∷ U) × (C ≅ᵀ Desc I))
gen-dι (⊢dι dI) = _ , (dI , crflᵀ)
gen-dι (⊢conv d c) with gen-dι d
... | I , (dI , c') = I , (dI , ctrnᵀ (csymᵀ c) c')

gen-dσ : {Γ : Ctx} {S f : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dσ S f ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ I → (Γ ⊢ I ∷ U) × ((Γ ⊢ S ∷ U) ×
           ((Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I))) × (C ≅ᵀ Desc I))))
gen-dσ (⊢dσ dI dS df) = _ , (dI , (dS , (df , crflᵀ)))
gen-dσ (⊢conv d c) with gen-dσ d
... | I , (dI , (dS , (df , c'))) = I , (dI , (dS , (df , ctrnᵀ (csymᵀ c) c')))

gen-dρ : {Γ : Ctx} {j C₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dρ j C₀ ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ I → (Γ ⊢ I ∷ U) × ((Γ ⊢ j ∷ El I) × ((Γ ⊢ C₀ ∷ Desc I) × (C ≅ᵀ Desc I))))
gen-dρ (⊢dρ dI dj dC) = _ , (dI , (dj , (dC , crflᵀ)))
gen-dρ (⊢conv d c) with gen-dρ d
... | I , (dI , (dj , (dC , c'))) = I , (dI , (dj , (dC , ctrnᵀ (csymᵀ c) c')))

gen-dpay : {Γ : Ctx} {I D C₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dpay I D C₀ ∷ C →
           (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ DescF I) × ((Γ ⊢ C₀ ∷ Desc I) × (C ≅ᵀ U)))
gen-dpay (⊢dpay dI dD dC) = dI , (dD , (dC , crflᵀ))
gen-dpay (⊢conv d c) with gen-dpay d
... | dI , (dD , (dC , c')) = dI , (dD , (dC , ctrnᵀ (csymᵀ c) c'))

gen-dih : {Γ : Ctx} {D e C₀ p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dih D e C₀ p ∷ C →
          Σ (RTm ⌊ Γ ⌋) (λ I → Σ (RTy ((⌊ Γ ⌋ ∙) ∙)) (λ M →
            (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ DescF I) × ((motCtx Γ I D ⊢ty M) × ((Γ ⊢ e ∷ MethTy I D M) ×
            ((Γ ⊢ C₀ ∷ Desc I) ×
            ((Γ ⊢ p ∷ El (dpay I D C₀)) × (C ≅ᵀ DIh D M C₀ p))))))))
gen-dih (⊢dih dI dD dM de dC dp) = _ , (_ , (dI , (dD , (dM , (de , (dC , (dp , crflᵀ)))))))
gen-dih (⊢conv d c) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , c'))))))) =
      I , (M , (dI , (dD , (dM , (de , (dC , (dp , ctrnᵀ (csymᵀ c) c')))))))

gen-fsuc : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fsuc t ∷ C →
           Σ (RTm ⌊ Γ ⌋) (λ n → (Γ ⊢ t ∷ Fin n) × (C ≅ᵀ Fin (nsuc n)))
gen-fsuc (⊢fsuc dt) = _ , (dt , crflᵀ)
gen-fsuc (⊢conv d c) with gen-fsuc d
... | n , (dt , c') = n , (dt , ctrnᵀ (csymᵀ c) c')

gen-fcase : {Γ : Ctx} {t a : RTm ⌊ Γ ⌋} {b : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ fcase t a b ∷ C →
            Σ (RTm ⌊ Γ ⌋) (λ n → Σ (RTy (⌊ Γ ⌋ ∙)) (λ P →
              ((Γ ▹ Fin (nsuc n)) ⊢ty P) × ((Γ ⊢ t ∷ Fin (nsuc n)) ×
              ((Γ ⊢ a ∷ subTy (single fzero) P) × (((Γ ▹ Fin n) ⊢ b ∷ subTy fsucS P) ×
              (C ≅ᵀ subTy (single t) P))))))
gen-fcase (⊢fcase dP dt da db) = _ , (_ , (dP , (dt , (da , (db , crflᵀ)))))
gen-fcase (⊢conv d c) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , c'))))) = n , (P , (dP , (dt , (da , (db , ctrnᵀ (csymᵀ c) c')))))

gen-fcase0 : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fcase0 t ∷ C →
             Σ (RTy (⌊ Γ ⌋ ∙)) (λ P → ((Γ ▹ Fin nzero) ⊢ty P) × ((Γ ⊢ t ∷ Fin nzero) ×
               (C ≅ᵀ subTy (single t) P)))
gen-fcase0 (⊢fcase0 dP dt) = _ , (dP , (dt , crflᵀ))
gen-fcase0 (⊢conv d c) with gen-fcase0 d
... | P , (dP , (dt , c')) = P , (dP , (dt , ctrnᵀ (csymᵀ c) c'))

gen-psplit : {Γ : Ctx} {b : RTm ((⌊ Γ ⌋ ∙) ∙)} {q : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ psplit b q ∷ C →
             Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B → Σ (RTy (⌊ Γ ⌋ ∙)) (λ P →
               (Γ ⊢ty A) × (((Γ ▹ A) ⊢ty B) × (((Γ ▹ Σ' A B) ⊢ty P) × ((Γ ⊢ q ∷ Σ' A B) ×
               ((((Γ ▹ A) ▹ B) ⊢ b ∷ subTy pairS P) × (C ≅ᵀ subTy (single q) P))))))))
gen-psplit (⊢psplit dA dB dP dq db) = _ , (_ , (_ , (dA , (dB , (dP , (dq , (db , crflᵀ)))))))
gen-psplit (⊢conv d c) with gen-psplit d
... | A , (B , (P , (dA , (dB , (dP , (dq , (db , c'))))))) = A , (B , (P , (dA , (dB , (dP , (dq , (db , ctrnᵀ (csymᵀ c) c')))))))

-- ★ a reference: its name is in scope, and the use's type converts to
--   the declared one
gen-ref : {Γ : Ctx} {d : ℕ} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ref d ∷ C →
          (d <ˢ n) × (C ≅ᵀ εwkTy (KSig.type 𝒮 d))
gen-ref (⊢ref p) = p , crflᵀ
gen-ref (⊢conv d c) with gen-ref d
... | p , c' = p , ctrnᵀ (csymᵀ c) c'

-- ★★ THE PAYLOAD'S σ AND ρ STEPS: a payload of a `dσ`/`dρ` telescope is a
--   pair; its halves are typed at the chosen branch / the recursive field
--   and the rest.  Used by `sr` at `dih-σ`/`dih-ρ` and by `srᵀ` at
--   `DIh-σ`/`DIh-ρ` (Validity).
dσ-step : {Γ : Ctx} {I D S f p : RTm ⌊ Γ ⌋} →
          Γ ⊢ dσ S f ∷ Desc I → Γ ⊢ p ∷ El (dpay I D (dσ S f)) →
          (Γ ⊢ app f (fst p) ∷ Desc I) × (Γ ⊢ snd p ∷ El (dpay I D (app f (fst p))))
dσ-step {I = I} {D = D} {S = S} {f = f} {p = p} dC dp with gen-dσ dC
... | I₀ , (dI₀ , (dS , (df , c))) =
      ⊢conv (⊢-cast (cong Desc (wk-cancel-tm (fst p) I₀)) (⊢app df (⊢fst dp'))) (csymᵀ c)
    , ⊢-cast (cong₃ (λ a b g → El (dpay a b (app g (fst p))))
                    (wk-cancel-tm (fst p) I) (wk-cancel-tm (fst p) D)
                    (wk-cancel-tm (fst p) f))
             (⊢snd dp')
  where
  dp' = ⊢conv dp (ctrnᵀ (credᵀ (ξ-El (dpay-σ I D S f))) (credᵀ (El-⌜Σ⌝ _ _)))

dρ-step : {Γ : Ctx} {I D j C p : RTm ⌊ Γ ⌋} →
          Γ ⊢ dρ j C ∷ Desc I → Γ ⊢ p ∷ El (dpay I D (dρ j C)) →
          (Γ ⊢ j ∷ El I) × ((Γ ⊢ C ∷ Desc I) ×
          ((Γ ⊢ fst p ∷ IMu I D j) × (Γ ⊢ snd p ∷ El (dpay I D C))))
dρ-step {I = I} {D = D} {j = j} {C = C} {p = p} dC dp with gen-dρ dC
... | I₀ , (_ , (dj , (dC₀ , c))) =
      ⊢conv dj (El-≅ (csym (Desc-inj c)))
    , (⊢conv dC₀ (csymᵀ c)
    , (⊢conv (⊢fst dp') (credᵀ El-⌜IMu⌝)
    , ⊢-cast (cong₃ (λ a b g → El (dpay a b g))
                    (wk-cancel-tm (fst p) I) (wk-cancel-tm (fst p) D)
                    (wk-cancel-tm (fst p) C))
             (⊢snd dp')))
  where
  dp' = ⊢conv dp (ctrnᵀ (credᵀ (ξ-El (dpay-ρ I D j C))) (credᵀ (El-⌜Σ⌝ _ _)))

------------------------------------------------------------------------
-- ★★★ LEVITATED INDUCTIVE FAMILIES: the reduction rules.
------------------------------------------------------------------------

-- the payload CODE computes; each reduct is a code again.
sr d (dpay-ι I D) with gen-dpay d
... | dI , (dD , (dC , cU)) = ⊢conv ⊢⌜Unit⌝ (csymᵀ cU)
sr d (dpay-σ I D S f) with gen-dpay d
... | dI , (dD , (dC , cU)) with gen-dσ dC
...   | I₀ , (dI₀ , (dS , (df , c))) =
        ⊢conv (⊢⌜Σ⌝ dS
                (⊢dpay (⊢wk dI) (⊢-cast (DescF-ren vs I) (⊢wk dD))
                       (⊢conv (⊢-cast (cong Desc (wk-app-vzᵗ I₀)) (⊢app (⊢wk df) (⊢var here)))
                              (≅ᵀ-ren vs (csymᵀ c)))))
              (csymᵀ cU)
sr d (dpay-ρ I D j C) with gen-dpay d
... | dI , (dD , (dC , cU)) with gen-dρ dC
...   | I₀ , (_ , (dj , (dC₀ , c))) =
        ⊢conv (⊢⌜Σ⌝ (⊢⌜IMu⌝ dI dD (⊢conv dj (El-≅ (csym (Desc-inj c)))))
                    (⊢dpay (⊢wk dI) (⊢-cast (DescF-ren vs I) (⊢wk dD)) (⊢wk (⊢conv dC₀ (csymᵀ c)))))
              (csymᵀ cU)
-- the hypotheses: none at `dι`, the chosen branch's at `dσ`, one
--   recursive call AT ITS OWN INDEX plus the rest at `dρ`.
sr d (dih-ι D e p) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC))))))) =
      ⊢conv ⊢unit (csymᵀ (ctrnᵀ cC (credᵀ (DIh-ι D M p))))
sr d (dih-σ D e S f p) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC))))))) with dσ-step dC dp
...   | dC' , dsnd =
        ⊢conv (⊢dih dI dD dM de dC' dsnd) (csymᵀ (ctrnᵀ cC (credᵀ (DIh-σ D M S f p))))
sr d (dih-ρ D e j C p) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC))))))) with dρ-step dC dp
...   | dj , (dC' , (dfst , dsnd)) =
        ⊢conv (⊢pair (ren-ty (ty-DIh dI dD dM dC' dsnd) there)
                     (⊢ielim dI dD dM de dj dfst)
                     (⊢-cast (sym (wk-cancel _ _)) (⊢dih dI dD dM de dC' dsnd)))
              (csymᵀ (ctrnᵀ cC (credᵀ (DIh-ρ D M j C p))))
-- ★★★ ι.  `IMu-inj` reconciles the constructor's family with the
--   eliminator's (three CONVERSIONS — every slot is a term), the payload
--   is transported once, and the method is applied to index, payload and
--   hypotheses.  The result type is the motive at `con p` by σ-calculus
--   alone (`meth-inst`) — no η.
sr d (ι D i e p) with gen-ielim d
... | I , (M , (dI , (dD , (dM , (de , (di , (dt , cC))))))) with gen-con dt
...   | I' , (D' , (i' , (dI' , (dD' , (di' , (dp , cIMu)))))) with IMu-inj cIMu
...     | cI , (cD , ci) =
          ⊢conv (⊢-cast (meth-inst (dih D e (app D i) p) p i M)
                  (⊢app-cast (cong₄ DIh (ww-cancel p i D) (wk2M-cancel p i M)
                                        (cong₂ app (ww-cancel p i D) (wk-cancel-tm p i)) refl)
                    (⊢app-cast (cong₂ (λ a b → El (dpay a b (app b i)))
                                      (wk-cancel-tm i I) (wk-cancel-tm i D))
                      (⊢app de di) dp₁)
                    (⊢dih dI dD dM de dDi dp₁)))
                (csymᵀ cC)
  where
  dp₁ = ⊢conv dp (dpay-≅ (csym cI) (csym cD) (csym ci))
  -- the fibre over `i`
  dDi = ⊢-cast (cong Desc (wk-cancel-tm i I)) (⊢app dD di)
-- tags and pairs
sr d (fcase-z a b) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) = ⊢conv da (csymᵀ cC)
sr d (fcase-s t a b) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) with gen-fsuc dt
...   | n' , (dt' , c') =
        ⊢conv (⊢-cast (fsucS-inst t P) (⊢[] db (⊢conv dt' (Fin-cong≅ (csym (nsuc-inj≅ (Fin-inj c'))))))) (csymᵀ cC)
-- ★ δ: the body, weakened from the empty context
sr d (δref _ _) with gen-ref d
... | p , c = ⊢conv (sub-lemma (okBody (ok p)) (λ ())) (csymᵀ c)
sr d (psplit-β b x y) with gen-psplit d
... | A , (B , (P , (dA , (dB , (dP , (dq , (db , cC))))))) with gen-pair dq
...   | A' , (B' , (cΣ , (dB' , (dx , dy)))) with Σ-inj (csymᵀ cΣ)
...     | cA , cB =
          ⊢conv (⊢-cast (pairS-inst x y P)
                  (sub-lemma db (⊢single2 (⊢conv dx cA) (⊢conv dy (≅ᵀ-sub (single x) cB)))))
                (csymᵀ cC)
-- ★★ the CONGRUENCES.  A stepped description/index/code that occurs in a
--   premise's TYPE is carried there by conversion.
sr d (ξ-⌜IMu⌝ᴵ r) with gen-⌜IMu⌝ d
... | dI , (dD , (di , cU)) =
      ⊢conv (⊢⌜IMu⌝ (sr dI r) (⊢conv dD (DescF-step r)) (⊢conv di (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-⌜Fin⌝ r) with gen-⌜Fin⌝ d
... | dn , cU = ⊢conv (⊢⌜Fin⌝ (sr dn r)) (csymᵀ cU)
sr d (ξ-⌜IMu⌝ᴰ r) with gen-⌜IMu⌝ d
... | dI , (dD , (di , cU)) = ⊢conv (⊢⌜IMu⌝ dI (sr dD r) di) (csymᵀ cU)
sr d (ξ-⌜IMu⌝ⁱ r) with gen-⌜IMu⌝ d
... | dI , (dD , (di , cU)) = ⊢conv (⊢⌜IMu⌝ dI dD (sr di r)) (csymᵀ cU)
sr d (ξ-con r) with gen-con d
... | I , (D , (i , (dI , (dD , (di , (dp , c)))))) = ⊢conv (⊢con dI dD di (sr dp r)) (csymᵀ c)
sr d (ξ-ielimᴰ r) with gen-ielim d
... | I , (M , (dI , (dD , (dM , (de , (di , (dt , cC))))))) =
      ⊢conv (⊢ielim dI (sr dD r) (conv-ctxᵀ (credᵀ (ξ-IMuᴰ (⟶-ren vs r))) dM)
                    (⊢conv de (red→≅ᵀ (MethTy-monoᴰ I M (step r done))))
                    di (⊢conv dt (credᵀ (ξ-IMuᴰ r))))
            (csymᵀ cC)
sr d (ξ-ielimⁱ r) with gen-ielim d
... | I , (M , (dI , (dD , (dM , (de , (di , (dt , cC))))))) =
      ⊢conv (⊢ielim dI dD dM de (sr di r) (⊢conv dt (credᵀ (ξ-IMuⁱ r))))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (iinst-mono M _ (step r done)))))
sr d (ξ-ielimᵉ r) with gen-ielim d
... | I , (M , (dI , (dD , (dM , (de , (di , (dt , cC))))))) =
      ⊢conv (⊢ielim dI dD dM (sr de r) di dt) (csymᵀ cC)
sr d (ξ-ielimᵗ {i = i} r) with gen-ielim d
... | I , (M , (dI , (dD , (dM , (de , (di , (dt , cC))))))) =
      ⊢conv (⊢ielim dI dD dM de di (sr dt r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (iinst-monoˢ M i (step r done)))))
sr d (ξ-dσˢ r) with gen-dσ d
... | I , (dI , (dS , (df , c))) =
      ⊢conv (⊢dσ dI (sr dS r) (⊢conv df (credᵀ (ξ-Πˡ (ξ-El r))))) (csymᵀ c)
sr d (ξ-dσᶠ r) with gen-dσ d
... | I , (dI , (dS , (df , c))) = ⊢conv (⊢dσ dI dS (sr df r)) (csymᵀ c)
sr d (ξ-dρʲ r) with gen-dρ d
... | I , (dI , (dj , (dC , c))) = ⊢conv (⊢dρ dI (sr dj r) dC) (csymᵀ c)
sr d (ξ-dρᶜ r) with gen-dρ d
... | I , (dI , (dj , (dC , c))) = ⊢conv (⊢dρ dI dj (sr dC r)) (csymᵀ c)
sr d (ξ-dpayᴵ r) with gen-dpay d
... | dI , (dD , (dC , cU)) =
      ⊢conv (⊢dpay (sr dI r) (⊢conv dD (DescF-step r)) (⊢conv dC (credᵀ (ξ-Desc r))))
            (csymᵀ cU)
sr d (ξ-dpayᴰ r) with gen-dpay d
... | dI , (dD , (dC , cU)) = ⊢conv (⊢dpay dI (sr dD r) dC) (csymᵀ cU)
sr d (ξ-dpayᶜ r) with gen-dpay d
... | dI , (dD , (dC , cU)) = ⊢conv (⊢dpay dI dD (sr dC r)) (csymᵀ cU)
sr d (ξ-dihᴰ r) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC))))))) =
      ⊢conv (⊢dih dI (sr dD r) (conv-ctxᵀ (credᵀ (ξ-IMuᴰ (⟶-ren vs r))) dM)
                  (⊢conv de (red→≅ᵀ (MethTy-monoᴰ I M (step r done))))
                  dC (⊢conv dp (credᵀ (ξ-El (ξ-dpayᴰ r)))))
            (csymᵀ (ctrnᵀ cC (credᵀ (ξ-DIhᴰ r))))
sr d (ξ-dihᵉ r) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC))))))) =
      ⊢conv (⊢dih dI dD dM (sr de r) dC dp) (csymᵀ cC)
sr d (ξ-dihᶜ r) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC))))))) =
      ⊢conv (⊢dih dI dD dM de (sr dC r) (⊢conv dp (credᵀ (ξ-El (ξ-dpayᶜ r)))))
            (csymᵀ (ctrnᵀ cC (credᵀ (ξ-DIhᶜ r))))
sr d (ξ-dihᵖ r) with gen-dih d
... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC))))))) =
      ⊢conv (⊢dih dI dD dM de dC (sr dp r)) (csymᵀ (ctrnᵀ cC (credᵀ (ξ-DIhᵖ r))))
sr d (ξ-fsuc r) with gen-fsuc d
... | n , (dt , c) = ⊢conv (⊢fsuc (sr dt r)) (csymᵀ c)
sr d (ξ-fcaseᵗ r) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) =
      ⊢conv (⊢fcase dP (sr dt r) da db)
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) P))))
sr d (ξ-fcaseᵃ r) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) = ⊢conv (⊢fcase dP dt (sr da r) db) (csymᵀ cC)
sr d (ξ-fcaseᵇ r) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) = ⊢conv (⊢fcase dP dt da (sr db r)) (csymᵀ cC)
sr d (ξ-fcase0 r) with gen-fcase0 d
... | P , (dP , (dt , cC)) =
      ⊢conv (⊢fcase0 dP (sr dt r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) P))))
sr d (ξ-psplitᵇ r) with gen-psplit d
... | A , (B , (P , (dA , (dB , (dP , (dq , (db , cC))))))) = ⊢conv (⊢psplit dA dB dP dq (sr db r)) (csymᵀ cC)
sr d (ξ-psplitᵍ r) with gen-psplit d
... | A , (B , (P , (dA , (dB , (dP , (dq , (db , cC))))))) =
      ⊢conv (⊢psplit dA dB dP (sr dq r) db)
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) P))))

sr d (ξ-nsuc r) with gen-nsuc d
... | (dn , cC) = ⊢conv (⊢nsuc (sr dn r)) (csymᵀ cC)
sr d (natrec-zero z s₀) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) = ⊢conv dz (csymᵀ cC)
sr d (natrec-suc z s₀ n) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) with gen-nsuc dn
...   | (dn' , _) =
      ⊢conv (⊢-cast (natrec-step-ty M (natrec z s₀ n) n)
              (⊢[] (sub-lemma ds (Sub⊢-ext (⊢single dn')))
                   (⊢natrec dM dz ds dn')))
            (csymᵀ cC)
sr d (ξ-natrecᶻ r) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) =
      ⊢conv (⊢natrec dM (sr dz r) ds dn) (csymᵀ cC)
sr d (ξ-natrecˢ r) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) =
      ⊢conv (⊢natrec dM dz (sr ds r) dn) (csymᵀ cC)
sr d (ξ-natrecⁿ r) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) =
      ⊢conv (⊢natrec dM dz ds (sr dn r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) M))))
-- ★★ stage D: ex falso preserves typing under both congruences.  The
-- code determines the result type, so the scrutinee case is a plain
-- rebuild and the code case rides `ξ-El`.
sr d (ξ-absurdᶜ r) with gen-absurd d
... | dc , (de , cv) =
      ⊢conv (⊢absurd (sr dc r) de)
            (ctrnᵀ (csymᵀ (credᵀ (ξ-El r))) (csymᵀ cv))
sr d (ξ-absurdᵉ r) with gen-absurd d
... | dc , (de , cv) = ⊢conv (⊢absurd dc (sr de r)) (csymᵀ cv)
-- ★ SUBJECT REDUCTION FOR THE ORDER.  Four of the five rules change
-- the result type, and each is repaired by the SAME computing order
-- that fired the rule — this is the payoff of `Hom Nat` computing.
--
--   ordtr-z   ↦ `Hom Nat nzero u` IS `Unit`, so `unit` fits.
--   ordtr-szz ↦ `p` already has the goal type verbatim.
--   ordtr-ssz ↦ ⚠ `q : Hom Nat (nsuc t) nzero` but the goal is
--               `Hom Nat (nsuc a) nzero` — DIFFERENT terms.  The rule
--               is sound only because BOTH collapse to `base` under
--               `Hom-Nat-sz`; that is the whole justification.
--   ordtr-szs ↦ ex falso, at the code whose `El` is the goal.
--   ordtr-sss ↦ peel `nsuc` off all three bounds via `Hom-Nat-ss`.
sr d (ordtr-z t u p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv ⊢unit (csymᵀ (ctrnᵀ cv (credᵀ (Hom-Nat-z u))))
sr d (ordtr-szz a p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) = ⊢conv dp (csymᵀ cv)
sr d (ordtr-ssz a t p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv dq (ctrnᵀ (credᵀ (Hom-Nat-sz t))
                      (ctrnᵀ (csymᵀ (credᵀ (Hom-Nat-sz a))) (csymᵀ cv)))
sr d (ordtr-szs a u p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) with gen-nsuc da | gen-nsuc du
...   | da' , _ | du' , _ =
        ⊢conv (⊢absurd (⊢⌜Hom⌝ ⊢⌜Nat⌝
                          (⊢conv da' (csymᵀ (credᵀ El-⌜Nat⌝)))
                          (⊢conv du' (csymᵀ (credᵀ El-⌜Nat⌝))))
                       (⊢conv dp (credᵀ (Hom-Nat-sz a))))
              (ctrnᵀ (credᵀ (El-⌜Hom⌝ _ _ _))
                (ctrnᵀ (credᵀ (ξ-Homᵀ El-⌜Nat⌝))
                  (ctrnᵀ (csymᵀ (credᵀ (Hom-Nat-ss a u))) (csymᵀ cv))))
sr d (ordtr-sss a t u p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) with gen-nsuc da | gen-nsuc dt | gen-nsuc du
...   | da' , _ | dt' , _ | du' , _ =
        ⊢conv (⊢ordtr da' dt' du'
                 (⊢conv dp (credᵀ (Hom-Nat-ss a t)))
                 (⊢conv dq (credᵀ (Hom-Nat-ss t u))))
              (ctrnᵀ (csymᵀ (credᵀ (Hom-Nat-ss a u))) (csymᵀ cv))
-- the congruences.  Only ᵃ and ᵘ move the result type (they are its
-- endpoints); ᵗ, ᵖ and q leave it alone.
sr d (ξ-ordtrᵃ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr (sr da r) dt du (⊢conv dp (credᵀ (ξ-Homˡ r))) dq)
            (csymᵀ (ctrnᵀ cv (credᵀ (ξ-Homˡ r))))
sr d (ξ-ordtrᵗ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da (sr dt r) du
               (⊢conv dp (credᵀ (ξ-Homʳ r))) (⊢conv dq (credᵀ (ξ-Homˡ r))))
            (csymᵀ cv)
sr d (ξ-ordtrᵘ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da dt (sr du r) dp (⊢conv dq (credᵀ (ξ-Homʳ r))))
            (csymᵀ (ctrnᵀ cv (credᵀ (ξ-Homʳ r))))
sr d (ξ-ordtrᵖ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da dt du (sr dp r) dq) (csymᵀ cv)
sr d (ξ-ordtrq r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da dt du dp (sr dq r)) (csymᵀ cv)
sr d (β s a) with gen-app d
... | A₀ , (B₀ , (d-lam , (d-a , cC))) with gen-lam d-lam
...   | A₁ , (B₁ , (cΠ , (tyA₁ , d-s))) with Π-inj cΠ
...     | (cA , cB) =
          ⊢conv (⊢[] d-s (⊢conv d-a cA))
                (ctrnᵀ (≅ᵀ-sub (single a) (csymᵀ cB)) (csymᵀ cC))
sr d (ξ-lam r) with gen-lam d
... | A₀ , (B₀ , (cΠ , (tyA₀ , d-s))) =
      ⊢conv (⊢lam tyA₀ (sr d-s r)) (csymᵀ cΠ)
sr d (ξ-appˡ r) with gen-app d
... | A₀ , (B₀ , (d-t , (d-u , cC))) = ⊢conv (⊢app (sr d-t r) d-u) (csymᵀ cC)
sr d (ξ-appʳ {u = u} {u' = u'} r) with gen-app d
... | A₀ , (B₀ , (d-t , (d-u , cC))) =
      ⊢conv (⊢app d-t (sr d-u r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) B₀))))
sr d (βfst a b) with gen-fst d
... | A₀ , (B₀ , (d-pair , cC)) with gen-pair d-pair
...   | A₁ , (B₁ , (cΣ , (tyB₁ , (d-a , d-b)))) with Σ-inj cΣ
...     | (cA , cB) = ⊢conv d-a (csymᵀ (ctrnᵀ cC cA))
sr d (βsnd a b) with gen-snd d
... | A₀ , (B₀ , (d-pair , cC)) with gen-pair d-pair
...   | A₁ , (B₁ , (cΣ , (tyB₁ , (d-a , d-b)))) with Σ-inj cΣ
...     | (cA , cB) =
          ⊢conv d-b
            (csymᵀ (ctrnᵀ cC
              (ctrnᵀ (red→≅ᵀ (subTy-monoˢ (single-mono (step (βfst a b) done)) B₀))
                     (≅ᵀ-sub (single a) cB))))
sr d (ξ-pairˡ r) with gen-pair d
... | A₀ , (B₀ , (cΣ , (tyB₀ , (d-a , d-b)))) =
      ⊢conv (⊢pair tyB₀ (sr d-a r)
              (⊢conv d-b (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) B₀))))
            (csymᵀ cΣ)
sr d (ξ-pairʳ r) with gen-pair d
... | A₀ , (B₀ , (cΣ , (tyB₀ , (d-a , d-b)))) =
      ⊢conv (⊢pair tyB₀ d-a (sr d-b r)) (csymᵀ cΣ)
sr d (ξ-fst r) with gen-fst d
... | A₀ , (B₀ , (d-p , cC)) = ⊢conv (⊢fst (sr d-p r)) (csymᵀ cC)
sr d (ξ-snd r) with gen-snd d
... | A₀ , (B₀ , (d-p , cC)) =
      ⊢conv (⊢snd (sr d-p r))
        (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step (ξ-fst r) done)) B₀))))
sr d (ξ-⌜Π⌝ˡ r) with gen-⌜Π⌝ d
... | (dc , (dd , cU)) =
      ⊢conv (⊢⌜Π⌝ (sr dc r) (conv-ctx (credᵀ (ξ-El r)) dd)) (csymᵀ cU)
sr d (ξ-⌜Π⌝ʳ r) with gen-⌜Π⌝ d
... | (dc , (dd , cU)) = ⊢conv (⊢⌜Π⌝ dc (sr dd r)) (csymᵀ cU)
sr d (ξ-⌜Σ⌝ˡ r) with gen-⌜Σ⌝ d
... | (dc , (dd , cU)) =
      ⊢conv (⊢⌜Σ⌝ (sr dc r) (conv-ctx (credᵀ (ξ-El r)) dd)) (csymᵀ cU)
sr d (ξ-⌜Σ⌝ʳ r) with gen-⌜Σ⌝ d
... | (dc , (dd , cU)) = ⊢conv (⊢⌜Σ⌝ dc (sr dd r)) (csymᵀ cU)
-- `tr`-rule reductions (stage 2).  The J cases extract the endpoint
-- conversion a canonical identity path witnesses via confluence
-- (stuck-ambient `Hom`s never unfold, so reducts decompose
-- componentwise); the taut case is VACUOUS in the base judgment — the
-- rule pins the motive to a `⌜Hom⌝`, never `var vz`.
sr d (tr-J-base cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with homred-inv baseamb-red (λ ()) (λ ()) (λ ()) ba-el rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-base))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
sr d (tr-J-Σ cm am mm c₁ c₂ s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with homred-inv σamb-red (λ ()) (λ ()) (λ ()) sa-el rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Σ))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★ the TAUT redex — REAL in the base judgment now (`⊢trU`).  The
-- pinned `U` ambient makes the `via-Π` arm a one-line `U-reduct` clash
-- (the staged proof needed a `gen-var` renaming dance here).
-- ★ W2b: `hrefl` at a pw-able code unfolds pointwise — the LHS/RHS
-- types convert through the `pw-Hom-decode` join.
sr d (hrefl-pw C s key) with gen-hrefl d
... | (dc , (ds , cH)) with pw-gen dc key | pw-Hom-decode C key s s
...   | (dDom , dBody) | Body , (ch₁ , ch₂) =
      ⊢conv (⊢lam (ty-El dDom) (⊢hrefl dBody (pw-app ds key)))
            (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Πʳ ch₂))
                   (csymᵀ (ctrnᵀ cH (red→≅ᵀ ch₁))))
-- ★ F6: the order's reflexivity, in lockstep with its type
sr d hrefl-Nat-z with gen-hrefl d
... | (_ , (_ , cH)) =
      ⊢conv ⊢unit (csymᵀ (ctrnᵀ cH (ctrnᵀ (credᵀ (ξ-Homᵀ El-⌜Nat⌝)) (credᵀ (Hom-Nat-z nzero)))))
sr d (hrefl-Nat-s m) with gen-hrefl d
... | (_ , (ds , cH)) with gen-nsuc ds
...   | (dm , _) =
      ⊢conv (⊢hrefl ⊢⌜Nat⌝ (⊢conv dm (csymᵀ (credᵀ El-⌜Nat⌝))))
            (ctrnᵀ (credᵀ (ξ-Homᵀ El-⌜Nat⌝))
            (ctrnᵀ (csymᵀ (credᵀ (Hom-Nat-ss m m)))
            (ctrnᵀ (csymᵀ (credᵀ (ξ-Homᵀ El-⌜Nat⌝))) (csymᵀ cH))))
-- ★ W2b: J at stable ⌜Hom⌝ codes — the endpoint conversion extracted
-- via confluence against the `StkAmb` analysis (stable-code decodings
-- never unfold to Π/U, so reducts decompose componentwise).
sr d (tr-J-Id cm am mm c₁ a₁ b₁ s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Id⌝ c₁ a₁ b₁} refl , nn-El nnh-Id) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Id))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★ WF stage C: J at ⌜Unit⌝ — the `tr-J-Id` case verbatim, at the other
-- stable datatype code.  (There is NO `tr-J-Nat` peer: `⌜Nat⌝` is not
-- `stkC?`, and `Hom Nat` computes, so J there is unsound — see
-- `stkC?` in NbEPDirDBVar.)
sr d (tr-J-Unit cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Unit⌝} refl , nn-El nnh-Unit) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Unit))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★ §10.4's subject-reduction obligation.  `tr-J-Unit`'s proof VERBATIM:
--   the only input that differs is the stuck-ambient witness, which is
--   `st-el {c = ⌜IMu⌝ …} refl` (that is `stkC? (⌜IMu⌝ …) = true`) paired
--   with `nn-El nnh-IMu`.
sr d (tr-J-IMu {I = Iⁱ} {D = Dⁱ} {iˣ = iˣ} cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜IMu⌝ Iⁱ Dⁱ iˣ} refl , nn-El nnh-IMu) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-IMu))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★ tags: `Hom (Fin n)` computes nothing either — the same proof.
sr d (tr-J-Fin {n = n} cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Fin⌝ n} refl , nn-El nnh-Fin) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Fin))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
sr d (tr-J-Hom cm am mm c₁ a₁ b₁ s e₀ key) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Hom⌝ c₁ a₁ b₁} key , nn-El nnh-Hom) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR)
                            (nn-El nnh-Hom))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★★ W2b: POINTWISE TRANSPORT preserves typing.  The rebuilt term is a
-- lambda whose body is ANOTHER composition-motive `⊢tr` instance at the
-- pointwise body code — assembled from `pw-app`/`pw-gen`, the decode
-- joins, and raw↔typed bridges (the rule's `pwShift`-renamed motive
-- equals the weakened pointwise body of the SUBSTITUTED code, because
-- the motive's components are vz-free).
sr {Γ = Γ} d (tr-pw c a f e₀ key) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-var dvM
...   | _ , (here , cv) =
      ⊢conv
        (⊢-cast
          (cong (Π (El (pwDom C₀)))
                (cong El (⌜Hom⌝-cong₃ (inst-c u') (inst-a u') refl)))
          (⊢lam (ty-El dDom) inner))
        (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Πʳ (stepᵀ (El-⌜Hom⌝ (pwBody C₀) W u') chU₂)))
               (csymᵀ (ctrnᵀ cC'
                         (ctrnᵀ (credᵀ (El-⌜Hom⌝ C₀ A₀ u))
                                (red→≅ᵀ chU₁)))))
  where
  C₀ A₀ : RTm ⌊ Γ ⌋
  C₀ = subTm (single t) c
  A₀ = subTm (single t) a
  keyT : pw? C₀ ≡ true
  keyT = pw?-sub (single t) c key

  cA : A ≅ᵀ El C₀
  cA = csymᵀ (subst (λ z → El C₀ ≅ᵀ z) (wk-cancel t A)
                    (≅ᵀ-sub (single t) cv))

  dC₀ : Γ ⊢ C₀ ∷ U
  dC₀ = ⊢[] dcM dt
  dA₀ : Γ ⊢ A₀ ∷ El C₀
  dA₀ = ⊢[] daM dt

  D : RTy ⌊ Γ ⌋
  D = El (pwDom C₀)
  ΓD : Ctx
  ΓD = Γ ▹ D
  A″ : RTy (⌊ Γ ⌋ ∙)
  A″ = El (pwBody C₀)
  ΓDA : Ctx
  ΓDA = ΓD ▹ A″

  genC = pw-gen dC₀ keyT
  dDom : Γ ⊢ pwDom C₀ ∷ U
  dDom = Σ.fst genC
  dBody : ΓD ⊢ pwBody C₀ ∷ U
  dBody = Σ.snd genC

  -- raw-rule ↔ typed-form bridges
  eq-c-in : renTm pwShift (pwBody c) ≡ renTm vs (pwBody C₀)
  eq-c-in =
    trans (ren-as-sub pwShift (pwBody c))
      (trans (subTm-occ (pwBody c) agree)
        (trans (sym (renTm-subTm (pwBody c)))
               (cong (renTm vs) (sym (pwBody-sub (single t) c key)))))
    where
    dead : occTm (vs vz) (pwBody c) ≡ false
    dead = pwBody-occ c key hcM
    agree : ∀ y → occTm y (pwBody c) ≡ true →
            var (pwShift y) ≡ (vs ᵣ∘ₛ extS (single t)) y
    agree vz o = refl
    agree (vs vz) o with trans (sym o) dead
    ... | ()
    agree (vs (vs i)) o = refl

  a-comp : renTm vs a ≡ renTm vs (renTm vs A₀)
  a-comp = trans (ren-as-sub vs a)
             (trans (subTm-occ a agree)
               (sym (trans (renTm-renTm A₀) (renTm-subTm a))))
    where
    agree : ∀ y → occTm y a ≡ true →
            var (vs y) ≡ ((vs ∘ᵣ vs) ᵣ∘ₛ single t) y
    agree vz o with trans (sym o) haM
    ... | ()
    agree (vs i) o = refl

  eq-a-in : app (renTm vs a) (var (vs vz))
            ≡ renTm vs (app (renTm vs A₀) (var vz))
  eq-a-in = cong (λ z → app z (var (vs vz))) a-comp

  -- endpoint agreement (the motive's components are endpoint-blind)
  eq-cu : subTm (single u) c ≡ C₀
  eq-cu = subTm-occ c agree
    where
    agree : ∀ y → occTm y c ≡ true → single u y ≡ single t y
    agree vz o with trans (sym o) hcM
    ... | ()
    agree (vs i) o = refl
  eq-au : subTm (single u) a ≡ A₀
  eq-au = subTm-occ a agree
    where
    agree : ∀ y → occTm y a ≡ true → single u y ≡ single t y
    agree vz o with trans (sym o) haM
    ... | ()
    agree (vs i) o = refl

  W t' u' : RTm (⌊ Γ ⌋ ∙)
  W  = app (renTm vs A₀) (var vz)
  t' = app (renTm vs t) (var vz)
  u' = app (renTm vs u) (var vz)

  cdU = pw-Hom-decode C₀ keyT A₀ u
  BodyU : RTy (⌊ Γ ⌋ ∙)
  BodyU = Σ.fst cdU
  chU₁ : Hom (El C₀) A₀ u ⟶ᵀ* Π (El (pwDom C₀)) BodyU
  chU₁ = Σ.fst (Σ.snd cdU)
  chU₂ : Hom (El (pwBody C₀)) W u' ⟶ᵀ* BodyU
  chU₂ = Σ.snd (Σ.snd cdU)

  cdP = pw-Hom-decode C₀ keyT t u
  BodyP : RTy (⌊ Γ ⌋ ∙)
  BodyP = Σ.fst cdP
  chP₁ : Hom (El C₀) t u ⟶ᵀ* Π (El (pwDom C₀)) BodyP
  chP₁ = Σ.fst (Σ.snd cdP)
  chP₂ : Hom (El (pwBody C₀)) t' u' ⟶ᵀ* BodyP
  chP₂ = Σ.snd (Σ.snd cdP)

  inst-c : (w : RTm (⌊ Γ ⌋ ∙)) →
           subTm (single w) (renTm pwShift (pwBody c)) ≡ pwBody C₀
  inst-c w = trans (cong (subTm (single w)) eq-c-in)
                   (wk-cancel-tm w (pwBody C₀))
  inst-a : (w : RTm (⌊ Γ ⌋ ∙)) →
           subTm (single w) (app (renTm vs a) (var (vs vz))) ≡ W
  inst-a w =
    cong (λ z → app z (var vz))
         (trans (cong (subTm (single w)) a-comp)
                (wk-cancel-tm w (renTm vs A₀)))

  dc-in : ΓDA ⊢ renTm pwShift (pwBody c) ∷ U
  dc-in = subst (λ z → ΓDA ⊢ z ∷ U) (sym eq-c-in)
                (⊢wk {Γ = ΓD} {B = A″} dBody)

  da-in : ΓDA ⊢ app (renTm vs a) (var (vs vz))
              ∷ El (renTm pwShift (pwBody c))
  da-in = ⊢-cast (cong El (sym eq-c-in))
            (subst (λ z → ΓDA ⊢ z ∷ El (renTm vs (pwBody C₀)))
                   (sym eq-a-in)
                   (⊢wk {Γ = ΓD} {B = A″} (pw-app dA₀ keyT)))

  dv-in : ΓDA ⊢ var vz ∷ El (renTm pwShift (pwBody c))
  dv-in = ⊢-cast (cong El (sym eq-c-in)) (⊢var here)

  hc-in : occTm vz (renTm pwShift (pwBody c)) ≡ false
  hc-in = occ-ren-tm avoids-pwShift (pwBody c)

  ha-in : occTm vz (app (renTm vs a) (var (vs vz))) ≡ false
  ha-in = ∨-false (occ-ren-tm avoids-wk a) refl

  dt-in : ΓD ⊢ t' ∷ A″
  dt-in = pw-app (⊢conv dt cA) keyT
  du-in : ΓD ⊢ u' ∷ A″
  du-in = pw-app (⊢conv du cA) keyT

  glam = gen-lam dp
  A₁ : RTy ⌊ Γ ⌋
  A₁ = Σ.fst glam
  B₁ : RTy (⌊ Γ ⌋ ∙)
  B₁ = Σ.fst (Σ.snd glam)
  cΠ : Hom A t u ≅ᵀ Π A₁ B₁
  cΠ = Σ.fst (Σ.snd (Σ.snd glam))
  tyA₁ : Γ ⊢ty A₁
  tyA₁ = Σ.fst (Σ.snd (Σ.snd (Σ.snd glam)))
  d-f : (Γ ▹ A₁) ⊢ f ∷ B₁
  d-f = Σ.snd (Σ.snd (Σ.snd (Σ.snd glam)))

  cΠ' : Π A₁ B₁ ≅ᵀ Π (El (pwDom C₀)) BodyP
  cΠ' = ctrnᵀ (csymᵀ cΠ) (ctrnᵀ (≅ᵀ-Homᵀ cA) (red→≅ᵀ chP₁))

  dp-in : ΓD ⊢ f ∷ Hom A″ t' u'
  dp-in = ⊢conv (ctx-conv d-f (csymᵀ (Σ.fst (Π-inj cΠ'))))
                (ctrnᵀ (Σ.snd (Π-inj cΠ')) (csymᵀ (red→≅ᵀ chP₂)))

  de-in : ΓD ⊢ app (renTm vs e₀) (var vz)
             ∷ El (subTm (single t')
                     (⌜Hom⌝ (renTm pwShift (pwBody c))
                            (app (renTm vs a) (var (vs vz)))
                            (var vz)))
  de-in = ⊢-cast
            (cong El (sym (⌜Hom⌝-cong₃ (inst-c t') (inst-a t') refl)))
            (pw-app de keyT)

  inner : ΓD ⊢ tr (⌜Hom⌝ (renTm pwShift (pwBody c))
                         (app (renTm vs a) (var (vs vz)))
                         (var vz))
                  f (app (renTm vs e₀) (var vz))
             ∷ El (subTm (single u')
                     (⌜Hom⌝ (renTm pwShift (pwBody c))
                            (app (renTm vs a) (var (vs vz)))
                            (var vz)))
  -- ★ the hereditary premise earns its keep here: `tr-pw` rewrites the
  -- motive code to `pwBody c`, and `nonatc-pwBody` is exactly what says
  -- that stays Nat-free.
  inner = ⊢tr dc-in da-in dv-in
              (nonatc-ren pwShift (nonatc-pwBody c ncM key))
              hc-in ha-in dt-in du-in dp-in de-in

  eq→≅ᵀ : {X Y : RTy ⌊ Γ ⌋} → X ≡ Y → X ≅ᵀ Y
  eq→≅ᵀ refl = crflᵀ

  cC' = ctrnᵀ cC (eq→≅ᵀ (cong El (⌜Hom⌝-cong₃ eq-cu eq-au refl)))
sr d (tr-taut f e₀) with gen-tr d
... | tgC (mkTrInv cM aM () A t u dcM daM dvM ncM hcM haM dt du dp de cC)
... | tgU (mkTrInvU refl t u dt du dp de cC) with gen-lam dp
...   | A₁ , (B₁ , (cΠ , (tyA₁ , d-f))) with church-rosserᵀ cΠ
...     | W , (rL , rR) with Π-reduct rR
...       | mkΠRed P₂ Q₂ eqW rP rQ
            with hom-to-Π nn-U (subst (Hom U t u ⟶ᵀ*_) eqW rL)
...         | via-Π rA with U-reduct rA
...           | ()
sr d (tr-taut f e₀) | tgU (mkTrInvU refl t u dt du dp de cC)
    | A₁ , (B₁ , (cΠ , (tyA₁ , d-f))) | W , (rL , rR)
    | mkΠRed P₂ Q₂ eqW rP rQ | via-U rA rt ru rEt rEu =
      ⊢conv
        (⊢-cast (cong El (wk-cancel-tm e₀ u))
          (⊢conv
            (⊢app (⊢lam tyA₁ d-f)
              (⊢conv de
                (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El rt) rEt))
                       (csymᵀ (red→≅ᵀ rP)))))
            (≅ᵀ-sub (single e₀)
              (ctrnᵀ (red→≅ᵀ rQ)
                     (csymᵀ (red→≅ᵀ
                       (⟶ᵀ*-trans (⟶ᵀ*-El (⟶*-ren vs ru)) rEu)))))))
        (csymᵀ cC)
-- congruence cases for the three new formers.
sr d (ξ-⌜Hom⌝ᶜ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) =
      ⊢conv (⊢⌜Hom⌝ (sr dc r) (⊢conv da (credᵀ (ξ-El r)))
                    (⊢conv db (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-⌜Hom⌝ˡ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Hom⌝ dc (sr da r) db) (csymᵀ cU)
sr d (ξ-⌜Hom⌝ʳ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Hom⌝ dc da (sr db r)) (csymᵀ cU)
sr d (ξ-hreflᶜ r) with gen-hrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢hrefl (sr dc r) (⊢conv dt (credᵀ (ξ-El r))))
            (csymᵀ (ctrnᵀ cH (credᵀ (ξ-Homᵀ (ξ-El r)))))
sr d (ξ-hreflᵃ r) with gen-hrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢hrefl dc (sr dt r))
            (csymᵀ (ctrnᵀ cH (ctrnᵀ (credᵀ (ξ-Homˡ r)) (credᵀ (ξ-Homʳ r)))))
sr d (ξ-trᵈ r) with gen-tr d
... | tgU (mkTrInvU refl t u dt du dp de cC) with r
...   | ()
sr d (ξ-trᵈ r) | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
  with hom-step r
...   | hsᶜ rc =
        ⊢conv (⊢tr (sr dcM rc) (⊢conv daM (credᵀ (ξ-El rc)))
                   (⊢conv dvM (credᵀ (ξ-El rc)))
                   (nonatc-red ncM rc) (occ-red rc hcM) haM dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
              (csymᵀ (ctrnᵀ cC (credᵀ (ξ-El (⟶-sub (single u) r)))))
...   | hsˡ ra =
        ⊢conv (⊢tr dcM (sr daM ra) dvM ncM hcM (occ-red ra haM) dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
              (csymᵀ (ctrnᵀ cC (credᵀ (ξ-El (⟶-sub (single u) r)))))
...   | hsʳ ()
sr d (ξ-trᵖ r) with gen-tr d
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC) =
      ⊢conv (⊢tr dcM daM dvM ncM hcM haM dt du (sr dp r) de) (csymᵀ cC)
... | tgU (mkTrInvU refl t u dt du dp de cC) =
      ⊢conv (⊢trU dt du (sr dp r) de) (csymᵀ cC)
sr d (ξ-trᵉ r) with gen-tr d
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC) =
      ⊢conv (⊢tr dcM daM dvM ncM hcM haM dt du dp (sr de r)) (csymᵀ cC)
... | tgU (mkTrInvU refl t u dt du dp de cC) =
      ⊢conv (⊢trU dt du dp (sr de r)) (csymᵀ cC)
-- ★ directed `ap` (SpikeAp).  The J case extracts the endpoint
-- conversions via confluence against the STABLE source ambient (the
-- typing key): both sides decompose componentwise, and the body's
-- substitution instances ride the endpoint chains.
sr d (ap-J cB b c₁ s key) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC)))))))))
      with gen-hrefl dp
...   | (dc₁ , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = cA} (stkC?→stkA? cA (flat→stk cA keyA))
                          , nn-El (stkC?→hd cA (flat→stk cA keyA))) rL
...       | A₂ , (t₁ , (u₁ , (eqW , (rt , ru))))
            with Hom-to-Hom
                   (homAmb→ (subst (Hom (El cA) t u ⟶ᵀ*_) eqW rL)
                            (nn-El (stkC?→hd cA (flat→stk cA keyA))))
                   (subst (Hom (El cA) t u ⟶ᵀ*_) eqW rL)
              |  Hom-to-Hom
                   (homAmb→ (subst (Hom (El cA) t u ⟶ᵀ*_) eqW rL)
                            (nn-El (stkC?→hd cA (flat→stk cA keyA))))
                   (subst (Hom (El _) s s ⟶ᵀ*_) eqW rR)
...         | mkHomRed rAL rt' ru' | mkHomRed rAR rs₁ rs₂ =
              ⊢conv
                (⊢hrefl dcB
                  (⊢-cast (cong El (wk-cancel-tm s cB))
                    (⊢[] db
                      (⊢conv ds (ctrnᵀ (red→≅ᵀ rAR)
                                       (csymᵀ (red→≅ᵀ rAL)))))))
                (ctrnᵀ
                  (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Homˡ (subTm-monoˢ (single-mono rs₁) b)))
                    (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Homʳ (subTm-monoˢ (single-mono rs₂) b)))
                      (ctrnᵀ (csymᵀ (red→≅ᵀ (⟶ᵀ*-Homʳ (subTm-monoˢ (single-mono ru) b))))
                             (csymᵀ (red→≅ᵀ (⟶ᵀ*-Homˡ (subTm-monoˢ (single-mono rt) b)))))))
                  (csymᵀ cC))
sr d (ξ-apᶜ r) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC))))))))) =
      ⊢conv (⊢ap dcA keyA (sr dcB r)
                 (⊢conv db (credᵀ (ξ-El (⟶-ren vs r))))
                 dt du dp)
            (ctrnᵀ (csymᵀ (credᵀ (ξ-Homᵀ (ξ-El r)))) (csymᵀ cC))
sr d (ξ-apᵇ {b = b} {b' = b'} r) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC))))))))) =
      ⊢conv (⊢ap dcA keyA dcB (sr db r) dt du dp)
            (ctrnᵀ
              (csymᵀ (red→≅ᵀ
                (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (step (⟶-sub (single t) r) done))
                           (⟶ᵀ*-Homʳ (step (⟶-sub (single u) r) done)))))
              (csymᵀ cC))
sr d (ξ-apᵖ r) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC))))))))) =
      ⊢conv (⊢ap dcA keyA dcB db dt du (sr dp r)) (csymᵀ cC)
-- ★ the two-former kernel.  `jsub-refl`'s endpoint conversion is the
-- `tr-J-base` pattern with the EASIER decomposition (`Id-reduct`:
-- Id is inert, both church-rosser arms split componentwise).
sr d (jsub-refl dM c₁ s e₀) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) with gen-idrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with Id-reduct rL | Id-reduct rR
...       | A₁ , (t₁ , (u₁ , (eqW , (rA , (rt , ru)))))
          | A₂ , (s₁ , (s₂ , (eqW' , (rA' , (rs₁ , rs₂)))))
            with trans (sym eqW) eqW'
...         | refl =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] dM rt)
                         (ctrnᵀ (csymᵀ (mono-El[] dM rs₁))
                           (ctrnᵀ (mono-El[] dM rs₂)
                             (csymᵀ (mono-El[] dM ru)))))
                       (csymᵀ cC))
sr d (ξ-jsubᵈ r) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) =
      ⊢conv (⊢jsub (sr dd r) dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
            (ctrnᵀ (csymᵀ (credᵀ (ξ-El (⟶-sub (single u) r)))) (csymᵀ cC))
sr d (ξ-jsubᵖ r) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) =
      ⊢conv (⊢jsub dd dt du (sr dp r) de) (csymᵀ cC)
sr d (ξ-jsubᵉ r) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) =
      ⊢conv (⊢jsub dd dt du dp (sr de r)) (csymᵀ cC)
sr d (ξ-⌜Id⌝ᶜ r) with gen-⌜Id⌝ d
... | (dc , (da , (db , cU))) =
      ⊢conv (⊢⌜Id⌝ (sr dc r) (⊢conv da (credᵀ (ξ-El r)))
                   (⊢conv db (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-⌜Id⌝ˡ r) with gen-⌜Id⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Id⌝ dc (sr da r) db) (csymᵀ cU)
sr d (ξ-⌜Id⌝ʳ r) with gen-⌜Id⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Id⌝ dc da (sr db r)) (csymᵀ cU)
sr d (ξ-idreflᶜ r) with gen-idrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢idrefl (sr dc r) (⊢conv dt (credᵀ (ξ-El r))))
            (csymᵀ (ctrnᵀ cH (credᵀ (ξ-Idᵀ (ξ-El r)))))
sr d (ξ-idreflᵃ r) with gen-idrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢idrefl dc (sr dt r))
            (csymᵀ (ctrnᵀ cH (ctrnᵀ (credᵀ (ξ-Idˡ r)) (credᵀ (ξ-Idʳ r)))))

------------------------------------------------------------------------
-- Type preservation for MULTI-step reduction — the immediate corollary.
------------------------------------------------------------------------

sr* : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → t ⟶* u → Γ ⊢ u ∷ A
sr* d done       = d
sr* d (step r p) = sr* (sr d r) p

