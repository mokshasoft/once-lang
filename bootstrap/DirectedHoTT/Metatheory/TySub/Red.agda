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
module DirectedHoTT.Metatheory.TySub.Red (𝒮 : Defs) where
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
open import DirectedHoTT.Spec.Reduction 𝒮
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


private
  variable
    Γ Δ : Cx

-- Transport a judgment along a type equality (fixed motive — avoids the
-- higher-order motive inference of a bare `subst`).
∋-cast : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {A A' : RTy ⌊ Γ ⌋} →
         A ≡ A' → Γ ∋ x ∷ A → Γ ∋ x ∷ A'
∋-cast refl v = v

------------------------------------------------------------------------
-- Type-level commute / cancel lemmas.
------------------------------------------------------------------------

wk-cancel : (a : RTm Γ) (A : RTy Γ) → subTy (single a) (renTy vs A) ≡ A
wk-cancel a A =
  trans (subTy-renTy A) (trans (subTy-cong (λ _ → refl) A) (subTy-id A))

ren-wk-comm : (ρ : Ren Γ Δ) (C : RTy Γ) →
              renTy (extR ρ) (renTy vs C) ≡ renTy vs (renTy ρ C)
ren-wk-comm ρ C =
  trans (renTy-renTy C) (trans (renTy-cong (λ _ → refl) C) (sym (renTy-renTy C)))

ren-comm-ty : (ρ : Ren Γ Δ) (D : RTy (Γ ∙)) (u : RTm Γ) →
              renTy ρ (subTy (single u) D) ≡
              subTy (single (renTm ρ u)) (renTy (extR ρ) D)
ren-comm-ty {Γ} ρ D u =
  trans (renTy-subTy D) (trans (subTy-cong bridge D) (sym (subTy-renTy D)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           (ρ ᵣ∘ₛ single u) x ≡ (single (renTm ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

exts-wk-ty : (σ : Sub Γ Δ) (C : RTy Γ) →
             subTy (extS σ) (renTy vs C) ≡ renTy vs (subTy σ C)
exts-wk-ty σ C =
  trans (subTy-renTy C) (trans (subTy-cong (λ _ → refl) C) (sym (renTy-subTy C)))

------------------------------------------------------------------------
-- Conversion survives renaming; types are monotone in the substitution.
------------------------------------------------------------------------

-- Weakening commutes with a renaming, at TERMS — both composites are
-- definitionally `x ↦ vs (ρ x)`.  The `Hom-U`/`Hom-Π` cases need it.
wk-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
         renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
wk-ren ρ t = trans (renTm-renTm t) (sym (renTm-renTm t))

-- ★ D074: the type of a fibred description is stable (its codomain is
--   one binder in)
DescF-ren : (ρ : Ren Γ Δ) (I : RTm Γ) → renTy ρ (DescF I) ≡ DescF (renTm ρ I)
DescF-ren ρ I = cong (λ X → Π (El (renTm ρ I)) (Desc X)) (wk-ren ρ I)

DescF-sub : (σ : Sub Γ Δ) (I : RTm Γ) → subTy σ (DescF I) ≡ DescF (subTm σ I)
DescF-sub σ I = cong (λ X → Π (El (subTm σ I)) (Desc X)) (wk-sub σ I)

-- ★ `ren-comm-ty` ONE BINDER UP — what the motive's INDEX layer needs.
--   Only the index variable moves; the payload and ambient slots are refl.
ren-comm-ty-ext : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) (j : RTm Γ) →
                  renTy (extR ρ) (subTy (extS (single j)) M)
                    ≡ subTy (extS (single (renTm ρ j))) (renTy (extR (extR ρ)) M)
ren-comm-ty-ext {Γ} ρ M j =
  trans (renTy-subTy M) (trans (subTy-cong bridge M) (sym (subTy-renTy M)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           (extR ρ ᵣ∘ₛ extS (single j)) x
             ≡ (extS (single (renTm ρ j)) ₛ∘ᵣ extR (extR ρ)) x
  bridge vz          = refl
  bridge (vs vz)     = wk-ren ρ j
  bridge (vs (vs x)) = refl

-- ★★ the two-slot instantiation is natural.  Built by peeling the two
--    `single`s in order: the SCRUTINEE slot with `ren-comm-ty`, then the
--    INDEX slot with its `-ext` twin.
iinst-ren : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) (j t : RTm Γ) →
            renTy ρ (iinst j t M)
              ≡ iinst (renTm ρ j) (renTm ρ t) (renTy (extR (extR ρ)) M)
iinst-ren ρ M j t =
  trans (ren-comm-ty ρ (subTy (extS (single j)) M) t)
        (cong (subTy (single (renTm ρ t))) (ren-comm-ty-ext ρ M j))

-- ★ LEVITATION: the motive, weakened past one more binder (its own two
--   kept), commutes with renaming — `DIh-ρ`'s renaming case.
wk2-renTy : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) →
            renTy (extR (extR (extR ρ))) (renTy (extR (extR vs)) M)
              ≡ renTy (extR (extR vs)) (renTy (extR (extR ρ)) M)
wk2-renTy ρ M =
  trans (renTy-renTy M)
        (trans (renTy-cong (λ { vz → refl ; (vs vz) → refl ; (vs (vs x)) → refl }) M)
               (sym (renTy-renTy M)))

⟶ᵀ-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ⟶ᵀ B → renTy ρ A ⟶ᵀ renTy ρ B
⟶ᵀ-ren ρ El-⌜base⌝    = El-⌜base⌝
⟶ᵀ-ren ρ (El-⌜Π⌝ c d) = El-⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)
⟶ᵀ-ren ρ (El-⌜Σ⌝ c d) = El-⌜Σ⌝ (renTm ρ c) (renTm (extR ρ) d)
⟶ᵀ-ren ρ (El-⌜Hom⌝ c a b) = El-⌜Hom⌝ (renTm ρ c) (renTm ρ a) (renTm ρ b)
-- ★ WF stage C: the datatype decodes.  Both targets are closed formers,
-- so renaming is the identity on them.
⟶ᵀ-ren ρ El-⌜Nat⌝  = El-⌜Nat⌝
⟶ᵀ-ren ρ El-⌜Unit⌝ = El-⌜Unit⌝
⟶ᵀ-ren ρ El-⌜IMu⌝ = El-⌜IMu⌝
⟶ᵀ-ren ρ El-⌜Fin⌝ = El-⌜Fin⌝
⟶ᵀ-ren ρ (DIh-ι D M p) = DIh-ι _ _ _
⟶ᵀ-ren ρ (DIh-σ D M S f p) = DIh-σ _ _ _ _ _
⟶ᵀ-ren ρ (DIh-ρ D M j C p) =
  subst (λ Z → DIh (renTm ρ D) (renTy (extR (extR ρ)) M) (dρ (renTm ρ j) (renTm ρ C)) (renTm ρ p) ⟶ᵀ Z)
        (sym (cong₂ Σ' (iinst-ren ρ M j (fst p))
                        (cong₄ (λ a b c d → DIh a b c (snd d))
                               (wk-ren ρ D) (wk2-renTy ρ M) (wk-ren ρ C) (wk-ren ρ p))))
        (DIh-ρ _ _ _ _ _)
⟶ᵀ-ren ρ (ξ-IMuᴵ r) = ξ-IMuᴵ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-IMuᴰ r) = ξ-IMuᴰ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-IMuⁱ r) = ξ-IMuⁱ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-Desc r) = ξ-Desc (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-Fin r) = ξ-Fin (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-DIhᴰ r) = ξ-DIhᴰ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-DIhᴹ r) = ξ-DIhᴹ (⟶ᵀ-ren (extR (extR ρ)) r)
⟶ᵀ-ren ρ (ξ-DIhᶜ r) = ξ-DIhᶜ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-DIhᵖ r) = ξ-DIhᵖ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-El r) = ξ-El (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-Πˡ r) = ξ-Πˡ (⟶ᵀ-ren ρ r)
⟶ᵀ-ren ρ (ξ-Πʳ r) = ξ-Πʳ (⟶ᵀ-ren (extR ρ) r)
⟶ᵀ-ren ρ (ξ-Σˡ r) = ξ-Σˡ (⟶ᵀ-ren ρ r)
⟶ᵀ-ren ρ (ξ-Σʳ r) = ξ-Σʳ (⟶ᵀ-ren (extR ρ) r)
⟶ᵀ-ren ρ (Hom-Nat-z n)    = Hom-Nat-z (renTm ρ n)
⟶ᵀ-ren ρ (Hom-Nat-sz m)   = Hom-Nat-sz (renTm ρ m)
⟶ᵀ-ren ρ (Hom-Nat-ss m n) = Hom-Nat-ss (renTm ρ m) (renTm ρ n)
⟶ᵀ-ren ρ (Hom-U c d) =
  subst (λ z → Hom U (renTm ρ c) (renTm ρ d) ⟶ᵀ Π (El (renTm ρ c)) (El z))
        (sym (wk-ren ρ d))
        (Hom-U (renTm ρ c) (renTm ρ d))
⟶ᵀ-ren ρ (Hom-Π A B f g) =
  subst (λ Z → Hom (Π (renTy ρ A) (renTy (extR ρ) B)) (renTm ρ f) (renTm ρ g) ⟶ᵀ Z)
        (cong₂ (λ x y → Π (renTy ρ A)
                          (Hom (renTy (extR ρ) B) (app x (var vz)) (app y (var vz))))
               (sym (wk-ren ρ f)) (sym (wk-ren ρ g)))
        (Hom-Π (renTy ρ A) (renTy (extR ρ) B) (renTm ρ f) (renTm ρ g))
⟶ᵀ-ren ρ (ξ-Homᵀ r) = ξ-Homᵀ (⟶ᵀ-ren ρ r)
⟶ᵀ-ren ρ (ξ-Homˡ r) = ξ-Homˡ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-Homʳ r) = ξ-Homʳ (⟶-ren ρ r)
⟶ᵀ-ren ρ (El-⌜Id⌝ c a b) = El-⌜Id⌝ (renTm ρ c) (renTm ρ a) (renTm ρ b)
⟶ᵀ-ren ρ (ξ-Idᵀ r) = ξ-Idᵀ (⟶ᵀ-ren ρ r)
⟶ᵀ-ren ρ (ξ-Idˡ r) = ξ-Idˡ (⟶-ren ρ r)
⟶ᵀ-ren ρ (ξ-Idʳ r) = ξ-Idʳ (⟶-ren ρ r)

≅ᵀ-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ≅ᵀ B → renTy ρ A ≅ᵀ renTy ρ B
≅ᵀ-ren ρ (credᵀ r)   = credᵀ (⟶ᵀ-ren ρ r)
≅ᵀ-ren ρ crflᵀ       = crflᵀ
≅ᵀ-ren ρ (csymᵀ c)   = csymᵀ (≅ᵀ-ren ρ c)
≅ᵀ-ren ρ (ctrnᵀ c d) = ctrnᵀ (≅ᵀ-ren ρ c) (≅ᵀ-ren ρ d)

subTy-monoˢ : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟶* σ' x) →
              (A : RTy Γ) → subTy σ A ⟶ᵀ* subTy σ' A
subTy-monoˢ h base     = doneᵀ
subTy-monoˢ h Unit     = doneᵀ
subTy-monoˢ h Nat      = doneᵀ
subTy-monoˢ h (IMu I D i) =
  ⟶ᵀ*-trans (⟶ᵀ*-IMuᴵ (subTm-monoˢ h I))
    (⟶ᵀ*-trans (⟶ᵀ*-IMuᴰ (subTm-monoˢ h D)) (⟶ᵀ*-IMu (subTm-monoˢ h i)))
subTy-monoˢ h (Desc I) = ⟶ᵀ*-Desc (subTm-monoˢ h I)
subTy-monoˢ h (DIh D M C p) =
  ⟶ᵀ*-trans (⟶ᵀ*-DIhᴰ (subTm-monoˢ h D))
    (⟶ᵀ*-trans (⟶ᵀ*-DIhᴹ (subTy-monoˢ (extS-mono (extS-mono h)) M))
      (⟶ᵀ*-trans (⟶ᵀ*-DIhᶜ (subTm-monoˢ h C)) (⟶ᵀ*-DIhᵖ (subTm-monoˢ h p))))
subTy-monoˢ h (Fin n) = ⟶ᵀ*-Fin (subTm-monoˢ h n)
subTy-monoˢ h U        = doneᵀ
subTy-monoˢ h (El t)   = ⟶ᵀ*-El (subTm-monoˢ h t)
subTy-monoˢ h (Π A B)  =
  ⟶ᵀ*-trans (⟶ᵀ*-Πˡ (subTy-monoˢ h A)) (⟶ᵀ*-Πʳ (subTy-monoˢ (extS-mono h) B))
subTy-monoˢ h (Σ' A B) =
  ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (subTy-monoˢ h A)) (⟶ᵀ*-Σʳ (subTy-monoˢ (extS-mono h) B))
subTy-monoˢ h (Hom A t u) =
  ⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (subTy-monoˢ h A))
    (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (subTm-monoˢ h t)) (⟶ᵀ*-Homʳ (subTm-monoˢ h u)))
subTy-monoˢ h (Id A t u) =
  ⟶ᵀ*-trans (⟶ᵀ*-Idᵀ (subTy-monoˢ h A))
    (⟶ᵀ*-trans (⟶ᵀ*-Idˡ (subTm-monoˢ h t)) (⟶ᵀ*-Idʳ (subTm-monoˢ h u)))

------------------------------------------------------------------------
-- W2 eliminator support: term-level cancels, type reduction under
-- renaming (star), occurrence preservation under reduction (`PosC`
-- survives `ξ-trᵈ`), and the reduct analyses `sr`'s new root cases need.
------------------------------------------------------------------------

-- ★ WF stage A: the recursor's step-motive substitution `nrs` commutes
-- with renaming and substitution (all bridges definitional but for the
-- weakening of the substituted term), and — the payload lemma — the
-- TWO-LEVEL instantiation of the step motive collapses to `single (nsuc n)`.
nrs-ren : (ρ : Ren Γ Δ) (M : RTy (Γ ∙)) →
          renTy (extR (extR ρ)) (subTy nrs M) ≡ subTy nrs (renTy (extR ρ) M)
nrs-ren {Γ} ρ M =
  trans (renTy-subTy M) (trans (subTy-cong bridge M) (sym (subTy-renTy M)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           renTm (extR (extR ρ)) (nrs x) ≡ nrs (extR ρ x)
  bridge vz     = refl
  bridge (vs x) = refl

wk-cancel-tm : (a t : RTm Γ) → subTm (single a) (renTm vs t) ≡ t
wk-cancel-tm a t =
  trans (subTm-renTm t) (trans (subTm-cong (λ _ → refl) t) (subTm-id t))

nrs-sub : (σ : Sub Γ Δ) (M : RTy (Γ ∙)) →
          subTy (extS (extS σ)) (subTy nrs M) ≡ subTy nrs (subTy (extS σ) M)
nrs-sub {Γ} σ M =
  trans (subTy-subTy M) (trans (subTy-cong bridge M) (sym (subTy-subTy M)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           subTm (extS (extS σ)) (nrs x) ≡ subTm nrs (extS σ x)
  bridge vz     = refl
  bridge (vs y) =
    trans (renTm-renTm (σ y))
      (trans (ren-as-sub (vs ∘ᵣ vs) (σ y))
             (trans (subTm-cong (λ _ → refl) (σ y))
                    (sym (subTm-renTm (σ y)))))

-- the payload: instantiating the step motive at the number then at the
-- IH is exactly the motive at the SUCCESSOR — which is what makes
-- `natrec-suc` type-preserving.
natrec-step-ty : (M : RTy (Γ ∙)) (r n : RTm Γ) →
                 subTy (single r) (subTy (extS (single n)) (subTy nrs M)) ≡
                 subTy (single (nsuc n)) M
natrec-step-ty {Γ} M r n =
  trans (subTy-subTy (subTy nrs M))
        (trans (subTy-subTy M) (subTy-cong bridge M))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           subTm (single r ∘ₛ extS (single n)) (nrs x) ≡ single (nsuc n) x
  bridge vz     = cong nsuc (wk-cancel-tm r n)
  bridge (vs y) = refl

wk-inst : (d : RTm (Γ ∙)) → subTm (single (var vz)) (renTm (extR vs) d) ≡ d
wk-inst d =
  trans (subTm-renTm d) (trans (subTm-cong ptw d) (subTm-id d))
  where
  ptw : ∀ x → (single (var vz) ₛ∘ᵣ extR vs) x ≡ idₛ x
  ptw vz     = refl
  ptw (vs y) = refl

⟶ᵀ*-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ⟶ᵀ* B → renTy ρ A ⟶ᵀ* renTy ρ B
⟶ᵀ*-ren ρ doneᵀ       = doneᵀ
⟶ᵀ*-ren ρ (stepᵀ r p) = stepᵀ (⟶ᵀ-ren ρ r) (⟶ᵀ*-ren ρ p)

-- Reduction never INTRODUCES a free variable — so `PosC` (whose content
-- is vz-freeness of the motive's frozen components) survives `ξ-trᵈ`.
occ-red : {x : Var Γ} {t t' : RTm Γ} →
          t ⟶ t' → occTm x t ≡ false → occTm x t' ≡ false
occ-red {x = x} (β t u) e = occ-sub h t (∨-false₁ (occTm (vs x) t) e)
  where
  h : ∀ y → eqv (vs x) y ≡ false → occTm x (single u y) ≡ false
  h vz     _ = ∨-false₂ (occTm (vs x) t) e
  h (vs z) q = q
occ-red {x = x} (βfst a b) e = ∨-false₁ (occTm x a) e
occ-red {x = x} (βsnd a b) e = ∨-false₂ (occTm x a) e
occ-red (ξ-nsuc r) e = occ-red r e
occ-red (ξ-⌜Fin⌝ r) e = occ-red r e
-- ★ LEVITATION: the levitated rules introduce no variable.
occ-red {x = x} (ξ-⌜IMu⌝ᴵ {I = I} {D = D} {i = i} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x I) e)) (∨-false (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))
occ-red {x = x} (ξ-⌜IMu⌝ᴰ {I = I} {D = D} {i = i} r) e =
  ∨-false (∨-false₁ (occTm x I) e) (∨-false (occ-red r (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e))) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))
occ-red {x = x} (ξ-⌜IMu⌝ⁱ {I = I} {D = D} {i = i} r) e =
  ∨-false (∨-false₁ (occTm x I) e) (∨-false (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)) (occ-red r (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))))
occ-red (ξ-con r) e = occ-red r e
occ-red {x = x} (ξ-ielimᴰ {D = D} {i = i} {e = m} {t = t} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x D) e)) (∨-false (∨-false₁ (occTm x i) (∨-false₂ (occTm x D) e)) (∨-false (∨-false₁ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))) (∨-false₂ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e)))))
occ-red {x = x} (ξ-ielimⁱ {D = D} {i = i} {e = m} {t = t} r) e =
  ∨-false (∨-false₁ (occTm x D) e) (∨-false (occ-red r (∨-false₁ (occTm x i) (∨-false₂ (occTm x D) e))) (∨-false (∨-false₁ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))) (∨-false₂ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e)))))
occ-red {x = x} (ξ-ielimᵉ {D = D} {i = i} {e = m} {t = t} r) e =
  ∨-false (∨-false₁ (occTm x D) e) (∨-false (∨-false₁ (occTm x i) (∨-false₂ (occTm x D) e)) (∨-false (occ-red r (∨-false₁ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e)))) (∨-false₂ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e)))))
occ-red {x = x} (ξ-ielimᵗ {D = D} {i = i} {e = m} {t = t} r) e =
  ∨-false (∨-false₁ (occTm x D) e) (∨-false (∨-false₁ (occTm x i) (∨-false₂ (occTm x D) e)) (∨-false (∨-false₁ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))) (occ-red r (∨-false₂ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))))))
occ-red {x = x} (ξ-dσˢ {S = S} {f = f} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x S) e)) (∨-false₂ (occTm x S) e)
occ-red {x = x} (ξ-dσᶠ {S = S} {f = f} r) e =
  ∨-false (∨-false₁ (occTm x S) e) (occ-red r (∨-false₂ (occTm x S) e))
occ-red {x = x} (ξ-dρʲ {j = j} {C = C} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x j) e)) (∨-false₂ (occTm x j) e)
occ-red {x = x} (ξ-dρᶜ {j = j} {C = C} r) e =
  ∨-false (∨-false₁ (occTm x j) e) (occ-red r (∨-false₂ (occTm x j) e))
occ-red {x = x} (ξ-dpayᴵ {I = I} {D = D} {C = C} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x I) e)) (∨-false (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))
occ-red {x = x} (ξ-dpayᴰ {I = I} {D = D} {C = C} r) e =
  ∨-false (∨-false₁ (occTm x I) e) (∨-false (occ-red r (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e))) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))
occ-red {x = x} (ξ-dpayᶜ {I = I} {D = D} {C = C} r) e =
  ∨-false (∨-false₁ (occTm x I) e) (∨-false (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)) (occ-red r (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))))
occ-red {x = x} (ξ-dihᴰ {D = D} {e = m} {C = C} {p = p} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x D) e)) (∨-false (∨-false₁ (occTm x m) (∨-false₂ (occTm x D) e)) (∨-false (∨-false₁ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))) (∨-false₂ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e)))))
occ-red {x = x} (ξ-dihᵉ {D = D} {e = m} {C = C} {p = p} r) e =
  ∨-false (∨-false₁ (occTm x D) e) (∨-false (occ-red r (∨-false₁ (occTm x m) (∨-false₂ (occTm x D) e))) (∨-false (∨-false₁ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))) (∨-false₂ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e)))))
occ-red {x = x} (ξ-dihᶜ {D = D} {e = m} {C = C} {p = p} r) e =
  ∨-false (∨-false₁ (occTm x D) e) (∨-false (∨-false₁ (occTm x m) (∨-false₂ (occTm x D) e)) (∨-false (occ-red r (∨-false₁ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e)))) (∨-false₂ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e)))))
occ-red {x = x} (ξ-dihᵖ {D = D} {e = m} {C = C} {p = p} r) e =
  ∨-false (∨-false₁ (occTm x D) e) (∨-false (∨-false₁ (occTm x m) (∨-false₂ (occTm x D) e)) (∨-false (∨-false₁ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))) (occ-red r (∨-false₂ (occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))))))
occ-red (ξ-fsuc r) e = occ-red r e
occ-red {x = x} (ξ-fcaseᵗ {t = t} {a = a} {b = b} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x t) e)) (∨-false (∨-false₁ (occTm x a) (∨-false₂ (occTm x t) e)) (∨-false₂ (occTm x a) (∨-false₂ (occTm x t) e)))
occ-red {x = x} (ξ-fcaseᵃ {t = t} {a = a} {b = b} r) e =
  ∨-false (∨-false₁ (occTm x t) e) (∨-false (occ-red r (∨-false₁ (occTm x a) (∨-false₂ (occTm x t) e))) (∨-false₂ (occTm x a) (∨-false₂ (occTm x t) e)))
occ-red {x = x} (ξ-fcaseᵇ {t = t} {a = a} {b = b} r) e =
  ∨-false (∨-false₁ (occTm x t) e) (∨-false (∨-false₁ (occTm x a) (∨-false₂ (occTm x t) e)) (occ-red r (∨-false₂ (occTm x a) (∨-false₂ (occTm x t) e))))
occ-red (ξ-fcase0 r) e = occ-red r e
occ-red {x = x} (ξ-psplitᵇ {b = b} {q = q} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm (vs (vs x)) b) e)) (∨-false₂ (occTm (vs (vs x)) b) e)
occ-red {x = x} (ξ-psplitᵍ {b = b} {q = q} r) e =
  ∨-false (∨-false₁ (occTm (vs (vs x)) b) e) (occ-red r (∨-false₂ (occTm (vs (vs x)) b) e))
occ-red {x = x} (ι D i m p) e =
  ∨-false (∨-false (∨-false eM ei) eP) (∨-false eD (∨-false eM (∨-false (∨-false eD ei) eP)))
  where
  eD = ∨-false₁ (occTm x D) e
  ei = ∨-false₁ (occTm x i) (∨-false₂ (occTm x D) e)
  eM = ∨-false₁ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))
  eP = ∨-false₂ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))
occ-red (dpay-ι I D) e = refl
occ-red {x = x} (dpay-σ I D S f) e =
  ∨-false (∨-false₁ (occTm x S) eC)
    (∨-false (wk I eI) (∨-false (wk D eD) (∨-false (wk f (∨-false₂ (occTm x S) eC)) refl)))
  where
  wk : (t : RTm _) → occTm x t ≡ false → occTm (vs x) (renTm vs t) ≡ false
  wk t o = trans (occ-ren-eq (λ _ → refl) t) o
  eI = ∨-false₁ (occTm x I) e
  eD = ∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)
  eC = ∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)
occ-red {x = x} (dpay-ρ I D j C) e =
  ∨-false (∨-false eI (∨-false eD (∨-false₁ (occTm x j) eC)))
    (∨-false (wk I eI) (∨-false (wk D eD) (wk C (∨-false₂ (occTm x j) eC))))
  where
  wk : (t : RTm _) → occTm x t ≡ false → occTm (vs x) (renTm vs t) ≡ false
  wk t o = trans (occ-ren-eq (λ _ → refl) t) o
  eI = ∨-false₁ (occTm x I) e
  eD = ∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)
  eC = ∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)
occ-red (dih-ι D m p) e = refl
occ-red {x = x} (dih-σ D m S f p) e =
  ∨-false eD (∨-false eM (∨-false (∨-false (∨-false₂ (occTm x S) eC) eP) eP))
  where
  eD = ∨-false₁ (occTm x D) e
  eM = ∨-false₁ (occTm x m) (∨-false₂ (occTm x D) e)
  eC = ∨-false₁ (occTm x S ∨ occTm x f) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))
  eP = ∨-false₂ (occTm x S ∨ occTm x f) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))
occ-red {x = x} (dih-ρ D m j C p) e =
  ∨-false (∨-false eD (∨-false (∨-false₁ (occTm x j) eC) (∨-false eM eP)))
          (∨-false eD (∨-false eM (∨-false (∨-false₂ (occTm x j) eC) eP)))
  where
  eD = ∨-false₁ (occTm x D) e
  eM = ∨-false₁ (occTm x m) (∨-false₂ (occTm x D) e)
  eC = ∨-false₁ (occTm x j ∨ occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))
  eP = ∨-false₂ (occTm x j ∨ occTm x C) (∨-false₂ (occTm x m) (∨-false₂ (occTm x D) e))
occ-red {x = x} (fcase-z a b) e = ∨-false₁ (occTm x a) e
occ-red {x = x} (fcase-s t a b) e = occ-sub h b (∨-false₂ (occTm x a) (∨-false₂ (occTm x t) e))
  where
  h : ∀ y → eqv (vs x) y ≡ false → occTm x (single t y) ≡ false
  h vz     _ = ∨-false₁ (occTm x t) e
  h (vs z) q = q
occ-red (δref d p) e = occ-εwkTm (Defs.body 𝒮 d)
occ-red {x = x} (psplit-β b u v) e = occ-sub h b (∨-false₁ (occTm (vs (vs x)) b) e)
  where
  eu = ∨-false₁ (occTm x u) (∨-false₂ (occTm (vs (vs x)) b) e)
  ev = ∨-false₂ (occTm x u) (∨-false₂ (occTm (vs (vs x)) b) e)
  h : ∀ y → eqv (vs (vs x)) y ≡ false → occTm x (single2 u v y) ≡ false
  h vz          _ = ev
  h (vs vz)     _ = eu
  h (vs (vs z)) q = q
occ-red {x = x} (tr-J-IMu {I = Iⁱ} {D = Dⁱ} {iˣ = iˣ} c a m s e₀) e =
  ∨-false₂ (occTm x (hrefl (⌜IMu⌝ Iⁱ Dⁱ iˣ) s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red {x = x} (tr-J-Fin {n = n} c a m s e₀) e =
  ∨-false₂ (occTm x (hrefl (⌜Fin⌝ n) s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red {x = x} (ξ-natrecᶻ {z = z} {s = s₀} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x z) e)) (∨-false₂ (occTm x z) e)
occ-red {x = x} (ξ-natrecˢ {z = z} {s = s₀} r) e =
  ∨-false (∨-false₁ (occTm x z) e)
    (∨-false (occ-red r (∨-false₁ (occTm (vs (vs x)) s₀) (∨-false₂ (occTm x z) e)))
             (∨-false₂ (occTm (vs (vs x)) s₀) (∨-false₂ (occTm x z) e)))
occ-red {x = x} (ξ-natrecⁿ {z = z} {s = s₀} r) e =
  ∨-false (∨-false₁ (occTm x z) e)
    (∨-false (∨-false₁ (occTm (vs (vs x)) s₀) (∨-false₂ (occTm x z) e))
             (occ-red r (∨-false₂ (occTm (vs (vs x)) s₀) (∨-false₂ (occTm x z) e))))
occ-red {x = x} (natrec-zero z s₀) e = ∨-false₁ (occTm x z) e
occ-red {x = x} (natrec-suc z s₀ n) e =
  occ-sub h₁ (subTm (extS (single n)) s₀) (occ-sub h₂ s₀ eS)
  where
  eZ = ∨-false₁ (occTm x z) e
  eS = ∨-false₁ (occTm (vs (vs x)) s₀) (∨-false₂ (occTm x z) e)
  eN = ∨-false₂ (occTm (vs (vs x)) s₀) (∨-false₂ (occTm x z) e)
  h₂ : ∀ y → eqv (vs (vs x)) y ≡ false → occTm (vs x) (extS (single n) y) ≡ false
  h₂ vz          _ = refl
  h₂ (vs vz)     _ = trans (occ-ren-eq (λ _ → refl) n) eN
  h₂ (vs (vs y)) q = q
  h₁ : ∀ y → eqv (vs x) y ≡ false → occTm x (single (natrec z s₀ n) y) ≡ false
  h₁ vz     _ = ∨-false eZ (∨-false eS eN)
  h₁ (vs y) q = q
occ-red (ξ-lam r) e = occ-red r e
occ-red {x = x} (ξ-appˡ {t = t} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x t) e)) (∨-false₂ (occTm x t) e)
occ-red {x = x} (ξ-appʳ {t = t} r) e =
  ∨-false (∨-false₁ (occTm x t) e) (occ-red r (∨-false₂ (occTm x t) e))
occ-red {x = x} (ξ-pairˡ {a = a} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x a) e)) (∨-false₂ (occTm x a) e)
occ-red {x = x} (ξ-pairʳ {a = a} r) e =
  ∨-false (∨-false₁ (occTm x a) e) (occ-red r (∨-false₂ (occTm x a) e))
occ-red {x = x} (ξ-absurdᶜ {e = e₉} r) e =
  ∨-false (occ-red r (∨-false₁ _ e)) (∨-false₂ _ e)
occ-red {x = x} (ξ-absurdᵉ {c = c₉} r) e =
  ∨-false (∨-false₁ _ e) (occ-red r (∨-false₂ (occTm x c₉) e))
-- the order's rules.  `occTm` of `ordtr` is a right-nested five-way ∨,
-- and `occTm x (nsuc n) = occTm x n`, so `ordtr-sss` — which peels a
-- `nsuc` off all three bounds — returns the occurrence proof VERBATIM.
--
-- ⚠ every `∨-false₁`/`∨-false₂` summand is written OUT.  Passing `_`
-- leaves the 𝔹 unsolved and the metas escape the clause — the same
-- trap as the arithmetic summands in the bound lemmas.
occ-red (ordtr-z t u p q) e = refl
occ-red {x = x} (ordtr-szz a p q) e =
  ∨-false₁ (occTm x p)
    (∨-false₂ false (∨-false₂ false (∨-false₂ (occTm x a) e)))
occ-red {x = x} (ordtr-ssz a t p q) e =
  ∨-false₂ (occTm x p)
    (∨-false₂ false (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e)))
occ-red {x = x} (ordtr-szs a u p q) e =
  ∨-false (∨-false (∨-false₁ (occTm x a) e)
                   (∨-false₁ (occTm x u)
                     (∨-false₂ false (∨-false₂ (occTm x a) e))))
          (∨-false₁ (occTm x p)
            (∨-false₂ (occTm x u)
              (∨-false₂ false (∨-false₂ (occTm x a) e))))
occ-red (ordtr-sss a t u p q) e = e
occ-red {x = x} (ξ-ordtrᵃ {a = a} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x a) e)) (∨-false₂ (occTm x a) e)
occ-red {x = x} (ξ-ordtrᵗ {a = a} {t = t} r) e =
  ∨-false (∨-false₁ (occTm x a) e)
    (∨-false (occ-red r (∨-false₁ (occTm x t) (∨-false₂ (occTm x a) e)))
             (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e)))
occ-red {x = x} (ξ-ordtrᵘ {a = a} {t = t} {u = u} r) e =
  ∨-false (∨-false₁ (occTm x a) e)
    (∨-false (∨-false₁ (occTm x t) (∨-false₂ (occTm x a) e))
      (∨-false (occ-red r (∨-false₁ (occTm x u)
                            (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e))))
               (∨-false₂ (occTm x u)
                 (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e)))))
occ-red {x = x} (ξ-ordtrᵖ {a = a} {t = t} {u = u} {p = p} r) e =
  ∨-false (∨-false₁ (occTm x a) e)
    (∨-false (∨-false₁ (occTm x t) (∨-false₂ (occTm x a) e))
      (∨-false (∨-false₁ (occTm x u)
                 (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e)))
        (∨-false (occ-red r (∨-false₁ (occTm x p)
                              (∨-false₂ (occTm x u)
                                (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e)))))
                 (∨-false₂ (occTm x p)
                   (∨-false₂ (occTm x u)
                     (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e)))))))
occ-red {x = x} (ξ-ordtrq {a = a} {t = t} {u = u} {p = p} r) e =
  ∨-false (∨-false₁ (occTm x a) e)
    (∨-false (∨-false₁ (occTm x t) (∨-false₂ (occTm x a) e))
      (∨-false (∨-false₁ (occTm x u)
                 (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e)))
        (∨-false (∨-false₁ (occTm x p)
                   (∨-false₂ (occTm x u)
                     (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e))))
                 (occ-red r (∨-false₂ (occTm x p)
                              (∨-false₂ (occTm x u)
                                (∨-false₂ (occTm x t) (∨-false₂ (occTm x a) e))))))))
occ-red (ξ-fst r) e = occ-red r e
occ-red (ξ-snd r) e = occ-red r e
occ-red {x = x} (ξ-⌜Π⌝ˡ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-⌜Π⌝ʳ {c = c} r) e =
  ∨-false (∨-false₁ (occTm x c) e) (occ-red r (∨-false₂ (occTm x c) e))
occ-red {x = x} (ξ-⌜Σ⌝ˡ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-⌜Σ⌝ʳ {c = c} r) e =
  ∨-false (∨-false₁ (occTm x c) e) (occ-red r (∨-false₂ (occTm x c) e))
occ-red {x = x} (tr-J-base c a m s e₀) e =
  ∨-false₂ (occTm x (hrefl ⌜base⌝ s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red {x = x} (tr-J-Σ c a m c₁ c₂ s e₀) e =
  ∨-false₂ (occTm x (hrefl (⌜Σ⌝ c₁ c₂) s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red {x = x} (tr-J-Id c a m c₁ a₁ b₁ s e₀) e =
  ∨-false₂ (occTm x (hrefl (⌜Id⌝ c₁ a₁ b₁) s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red {x = x} (tr-J-Unit c a m s e₀) e =
  ∨-false₂ (occTm x (hrefl ⌜Unit⌝ s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red (tr-taut f e₀) e = e
occ-red {x = x} (hrefl-pw C s key) e =
  ∨-false (pwBody-occ C key (∨-false₁ (occTm x C) e))
          (∨-false (trans (occ-ren-eq (λ y → refl) s)
                          (∨-false₂ (occTm x C) e))
                   refl)
occ-red hrefl-Nat-z e = refl
occ-red (hrefl-Nat-s m) e = e
occ-red {x = x} (tr-J-Hom c a m c₁ a₁ b₁ s e₀ key) e =
  ∨-false₂ (occTm x (hrefl (⌜Hom⌝ c₁ a₁ b₁) s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red {x = x} (tr-pw c a f e₀ key) e =
  ∨-false
    (∨-false part-code (∨-false (∨-false part-a refl) refl))
    (∨-false h-f (∨-false part-e refl))
  where
  h-mot  = ∨-false₁ (occTm (vs x) (⌜Hom⌝ c a (var vz))) e
  h-rest = ∨-false₂ (occTm (vs x) (⌜Hom⌝ c a (var vz))) e
  h-f    = ∨-false₁ (occTm (vs x) f) h-rest
  h-e0   = ∨-false₂ (occTm (vs x) f) h-rest
  h-c    = ∨-false₁ (occTm (vs x) c) h-mot
  h-a    = ∨-false₁ (occTm (vs x) a) (∨-false₂ (occTm (vs x) c) h-mot)
  pwsh-eq : ∀ y → eqv (vs (vs x)) (pwShift y) ≡ eqv (vs (vs x)) y
  pwsh-eq vz     = refl
  pwsh-eq (vs y) = refl
  part-code = trans (occ-ren-eq pwsh-eq (pwBody c)) (pwBody-occ c key h-c)
  part-a    = trans (occ-ren-eq (λ y → refl) a) h-a
  part-e    = trans (occ-ren-eq (λ y → refl) e₀) h-e0
occ-red {x = x} (ξ-⌜Hom⌝ᶜ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-⌜Hom⌝ˡ {c = c} {a = a} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (occ-red r (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e)))
                   (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e)))
occ-red {x = x} (ξ-⌜Hom⌝ʳ {c = c} {a = a} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e))
                   (occ-red r (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e))))
occ-red {x = x} (ξ-hreflᶜ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-hreflᵃ {c = c} r) e =
  ∨-false (∨-false₁ (occTm x c) e) (occ-red r (∨-false₂ (occTm x c) e))
occ-red {x = x} (ξ-trᵈ {d = d} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm (vs x) d) e)) (∨-false₂ (occTm (vs x) d) e)
occ-red {x = x} (ξ-trᵖ {d = d} {p = p} r) e =
  ∨-false (∨-false₁ (occTm (vs x) d) e)
          (∨-false (occ-red r (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
                   (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
occ-red {x = x} (ξ-trᵉ {d = d} {p = p} r) e =
  ∨-false (∨-false₁ (occTm (vs x) d) e)
          (∨-false (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e))
                   (occ-red r (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e))))
occ-red {x = x} (ap-J cB b c₁ s key) e =
  ∨-false (∨-false₁ (occTm x cB) e)
          (occ-sub h b (∨-false₁ (occTm (vs x) b) (∨-false₂ (occTm x cB) e)))
  where
  h : ∀ y → eqv (vs x) y ≡ false → occTm x (single s y) ≡ false
  h vz     _ = ∨-false₂ (occTm x c₁)
                 (∨-false₂ (occTm (vs x) b) (∨-false₂ (occTm x cB) e))
  h (vs z) q = q
occ-red {x = x} (ξ-apᶜ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-apᵇ {c = c} {b = b} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (occ-red r (∨-false₁ (occTm (vs x) b) (∨-false₂ (occTm x c) e)))
                   (∨-false₂ (occTm (vs x) b) (∨-false₂ (occTm x c) e)))
occ-red {x = x} (ξ-apᵖ {c = c} {b = b} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (∨-false₁ (occTm (vs x) b) (∨-false₂ (occTm x c) e))
                   (occ-red r (∨-false₂ (occTm (vs x) b) (∨-false₂ (occTm x c) e))))
occ-red {x = x} (jsub-refl d c s e₀) e =
  ∨-false₂ (occTm x c ∨ occTm x s) (∨-false₂ (occTm (vs x) d) e)
occ-red {x = x} (ξ-⌜Id⌝ᶜ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-⌜Id⌝ˡ {c = c} {a = a} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (occ-red r (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e)))
                   (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e)))
occ-red {x = x} (ξ-⌜Id⌝ʳ {c = c} {a = a} r) e =
  ∨-false (∨-false₁ (occTm x c) e)
          (∨-false (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e))
                   (occ-red r (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e))))
occ-red {x = x} (ξ-idreflᶜ {c = c} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x c) e)) (∨-false₂ (occTm x c) e)
occ-red {x = x} (ξ-idreflᵃ {c = c} r) e =
  ∨-false (∨-false₁ (occTm x c) e) (occ-red r (∨-false₂ (occTm x c) e))
occ-red {x = x} (ξ-jsubᵈ {d = d} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm (vs x) d) e)) (∨-false₂ (occTm (vs x) d) e)
occ-red {x = x} (ξ-jsubᵖ {d = d} {p = p} r) e =
  ∨-false (∨-false₁ (occTm (vs x) d) e)
          (∨-false (occ-red r (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
                   (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
occ-red {x = x} (ξ-jsubᵉ {d = d} {p = p} r) e =
  ∨-false (∨-false₁ (occTm (vs x) d) e)
          (∨-false (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e))
                   (occ-red r (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e))))

posc-red : {d d' : RTm (Γ ∙)} → PosC vz d → d ⟶ d' → PosC vz d'
posc-red posc-var ()
posc-red (posc-Hom hc ha) (ξ-⌜Hom⌝ᶜ r) = posc-Hom (occ-red r hc) ha
posc-red (posc-Hom hc ha) (ξ-⌜Hom⌝ˡ r) = posc-Hom hc (occ-red r ha)
posc-red (posc-Hom hc ha) (ξ-⌜Hom⌝ʳ ())
------------------------------------------------------------------------
-- ★★★ THE INDEXED NATURALITY LAYER.
--
-- Same shapes as the block above, with ONE systematic difference: every
-- computed type here mentions the AMBIENT INDEX, so the action is
-- TRANSPORTED onto it instead of vanishing.  `ipayTy-ren`/`-sub` (Syntax)
-- set the pattern; these lift it to the TWO-SLOT motive, where the index
-- lives one binder further out than the scrutinee.
------------------------------------------------------------------------

-- weakening commutes with a substitution, at TERMS.
exts-wk-tm : (σ : Sub Γ Δ) (t : RTm Γ) →
             subTm (extS σ) (renTm vs t) ≡ renTm vs (subTm σ t)
exts-wk-tm σ t = trans (subTm-renTm t) (sym (renTm-subTm t))


⟶ᵀ*-sub' : (σ : Sub Γ Δ) {A A' : RTy Γ} → A ⟶ᵀ* A' → subTy σ A ⟶ᵀ* subTy σ A'
⟶ᵀ*-sub' σ doneᵀ       = doneᵀ
⟶ᵀ*-sub' σ (stepᵀ r p) = stepᵀ (⟶ᵀ-sub σ r) (⟶ᵀ*-sub' σ p)

-- ⚠ TWO slots move, for two different rules: `ξ-ielimⁱ` steps the INDEX,
--   `ξ-ielimᵗ` steps the SCRUTINEE.  The scrutinee one is exactly the
--   non-indexed `ξ-elimᵗ` shape; the index one has no non-indexed twin.
iinst-monoˢ : (M : RTy ((Γ ∙) ∙)) (j : RTm Γ) {t t' : RTm Γ} →
              t ⟶* t' → iinst j t M ⟶ᵀ* iinst j t' M
iinst-monoˢ M j r = subTy-monoˢ (single-mono r) (subTy (extS (single j)) M)

iinst-mono : (M : RTy ((Γ ∙) ∙)) (t : RTm Γ) {j j' : RTm Γ} →
             j ⟶* j' → iinst j t M ⟶ᵀ* iinst j' t M
iinst-mono M t r =
  ⟶ᵀ*-sub' (single t)
    (subTy-monoˢ (λ { vz → done ; (vs vz) → ⟶*-ren vs r ; (vs (vs x)) → done }) M)

-- ★ the method type is reduction-monotone in the DESCRIPTION: it names
--   `D` twice in the payload and twice in the hypotheses.
MethTy-monoᴰ : (I : RTm Γ) (M : RTy ((Γ ∙) ∙)) {D D' : RTm Γ} →
               D ⟶* D' → MethTy I D M ⟶ᵀ* MethTy I D' M
MethTy-monoᴰ I M r =
  ⟶ᵀ*-Πʳ (⟶ᵀ*-trans
    (⟶ᵀ*-Πˡ (⟶ᵀ*-El (⟶*-trans (⟶*-dpayᴰ (⟶*-ren vs r)) (⟶*-dpayᶜ (⟶*-appˡ (⟶*-ren vs r))))))
    (⟶ᵀ*-Πʳ (⟶ᵀ*-Πˡ (⟶ᵀ*-trans (⟶ᵀ*-DIhᴰ (⟶*-ren vs (⟶*-ren vs r)))
                                (⟶ᵀ*-DIhᶜ (⟶*-appˡ (⟶*-ren vs (⟶*-ren vs r))))))))

------------------------------------------------------------------------
-- ★★ LEVITATION: naturality of the ONE method type, and the two motive
--   re-basings (`fcase`'s successor, `psplit`'s pair).
------------------------------------------------------------------------

wk2-ren-tm : (ρ : Ren Γ Δ) (t : RTm Γ) →
             renTm (extR (extR ρ)) (renTm vs (renTm vs t)) ≡ renTm vs (renTm vs (renTm ρ t))
wk2-ren-tm ρ t =
  trans (trans (cong (renTm (extR (extR ρ))) (renTm-renTm t)) (renTm-renTm t))
        (trans (renTm-cong (λ _ → refl) t)
               (sym (trans (renTm-renTm (renTm ρ t)) (renTm-renTm t))))

wk2-sub-tm : (σ : Sub Γ Δ) (t : RTm Γ) →
             subTm (extS (extS σ)) (renTm vs (renTm vs t)) ≡ renTm vs (renTm vs (subTm σ t))
wk2-sub-tm σ t = trans (wk-sub (extS σ) (renTm vs t)) (cong (renTm vs) (wk-sub σ t))

wk2M-ren : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) →
           renTy (extR (extR (extR (extR ρ)))) (wk2M M) ≡ wk2M (renTy (extR (extR ρ)) M)
wk2M-ren ρ M =
  trans (renTy-renTy M)
        (trans (renTy-cong (λ { vz → refl ; (vs vz) → refl ; (vs (vs x)) → refl }) M)
               (sym (renTy-renTy M)))

wk2M-sub : (σ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) →
           subTy (extS (extS (extS (extS σ)))) (wk2M M) ≡ wk2M (subTy (extS (extS σ)) M)
wk2M-sub σ M = trans (subTy-renTy M) (trans (subTy-cong ptw M) (sym (renTy-subTy M)))
  where
  f4 : ∀ {Θ} (t : RTm Θ) →
       renTm vs (renTm vs (renTm vs (renTm vs t))) ≡ renTm (λ y → vs (vs (vs (vs y)))) t
  f4 t = trans (cong (renTm vs) (cong (renTm vs) (renTm-renTm t)))
               (trans (cong (renTm vs) (renTm-renTm t)) (renTm-renTm t))
  fE : ∀ {Θ} (t : RTm Θ) →
       renTm (extR (extR (λ y → vs (vs y)))) (renTm vs (renTm vs t)) ≡ renTm (λ y → vs (vs (vs (vs y)))) t
  fE t = trans (cong (renTm (extR (extR (λ y → vs (vs y))))) (renTm-renTm t)) (renTm-renTm t)
  ptw : ∀ x → (extS (extS (extS (extS σ))) ₛ∘ᵣ extR (extR (λ y → vs (vs y)))) x
                ≡ (extR (extR (λ y → vs (vs y))) ᵣ∘ₛ extS (extS σ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs x)) = trans (f4 (σ x)) (sym (fE (σ x)))

methS-ren : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) →
            renTy (extR (extR (extR ρ))) (subTy methS M) ≡ subTy methS (renTy (extR (extR ρ)) M)
methS-ren ρ M =
  trans (renTy-subTy M)
        (trans (subTy-cong (λ { vz → refl ; (vs vz) → refl ; (vs (vs x)) → refl }) M)
               (sym (subTy-renTy M)))

methS-sub : (σ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) →
            subTy (extS (extS (extS σ))) (subTy methS M) ≡ subTy methS (subTy (extS (extS σ)) M)
methS-sub σ M = trans (subTy-subTy M) (trans (subTy-cong ptw M) (sym (subTy-subTy M)))
  where
  ptw : ∀ x → (extS (extS (extS σ)) ∘ₛ methS) x ≡ (methS ∘ₛ extS (extS σ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs x)) =
    trans (trans (cong (renTm vs) (renTm-renTm (σ x))) (renTm-renTm (σ x)))
          (trans (ren-as-sub (λ y → vs (vs (vs y))) (σ x))
                 (sym (trans (subTm-renTm (renTm vs (σ x))) (subTm-renTm (σ x)))))

MethTy-ren : (ρ : Ren Γ Δ) (I D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
             renTy ρ (MethTy I D M) ≡ MethTy (renTm ρ I) (renTm ρ D) (renTy (extR (extR ρ)) M)
MethTy-ren ρ I D M =
  cong₂ (λ P Q → Π (El (renTm ρ I)) (Π P Q))
    (cong₂ (λ a b → El (dpay a b (app b (var vz)))) (wk-ren ρ I) (wk-ren ρ D))
    (cong₃ (λ c m t → Π (DIh c m (app c (var (vs vz))) (var vz)) t) (wk2-ren-tm ρ D) (wk2M-ren ρ M) (methS-ren ρ M))

MethTy-sub : (σ : Sub Γ Δ) (I D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
             subTy σ (MethTy I D M) ≡ MethTy (subTm σ I) (subTm σ D) (subTy (extS (extS σ)) M)
MethTy-sub σ I D M =
  cong₂ (λ P Q → Π (El (subTm σ I)) (Π P Q))
    (cong₂ (λ a b → El (dpay a b (app b (var vz)))) (wk-sub σ I) (wk-sub σ D))
    (cong₃ (λ c m t → Π (DIh c m (app c (var (vs vz))) (var vz)) t) (wk2-sub-tm σ D) (wk2M-sub σ M) (methS-sub σ M))

fsucS-ren : (ρ : Ren Γ Δ) (P : RTy (Γ ∙)) →
            renTy (extR ρ) (subTy fsucS P) ≡ subTy fsucS (renTy (extR ρ) P)
fsucS-ren ρ P =
  trans (renTy-subTy P)
        (trans (subTy-cong (λ { vz → refl ; (vs x) → refl }) P) (sym (subTy-renTy P)))

fsucS-sub : (σ : Sub Γ Δ) (P : RTy (Γ ∙)) →
            subTy (extS σ) (subTy fsucS P) ≡ subTy fsucS (subTy (extS σ) P)
fsucS-sub {Γ} σ P = trans (subTy-subTy P) (trans (subTy-cong bridge P) (sym (subTy-subTy P)))
  where
  bridge : ∀ (x : Var (Γ ∙)) → subTm (extS σ) (fsucS x) ≡ subTm fsucS (extS σ x)
  bridge vz     = refl
  bridge (vs y) =
    trans (ren-as-sub vs (σ y)) (trans (subTm-cong (λ _ → refl) (σ y)) (sym (subTm-renTm (σ y))))

pairS-ren : (ρ : Ren Γ Δ) (P : RTy (Γ ∙)) →
            renTy (extR (extR ρ)) (subTy pairS P) ≡ subTy pairS (renTy (extR ρ) P)
pairS-ren ρ P =
  trans (renTy-subTy P)
        (trans (subTy-cong (λ { vz → refl ; (vs x) → refl }) P) (sym (subTy-renTy P)))

pairS-sub : (σ : Sub Γ Δ) (P : RTy (Γ ∙)) →
            subTy (extS (extS σ)) (subTy pairS P) ≡ subTy pairS (subTy (extS σ) P)
pairS-sub {Γ} σ P = trans (subTy-subTy P) (trans (subTy-cong bridge P) (sym (subTy-subTy P)))
  where
  bridge : ∀ (x : Var (Γ ∙)) → subTm (extS (extS σ)) (pairS x) ≡ subTm pairS (extS σ x)
  bridge vz     = refl
  bridge (vs y) =
    trans (renTm-renTm (σ y))
      (trans (ren-as-sub (vs ∘ᵣ vs) (σ y))
             (trans (subTm-cong (λ _ → refl) (σ y))
                    (sym (subTm-renTm (σ y)))))

------------------------------------------------------------------------
-- ★ arithmetic, kept for downstream users.
+-suc : (j k : ℕ) → (j + suc k) ≡ suc (j + k)
+-suc zero    k = refl
+-suc (suc j) k = cong suc (+-suc j k)
