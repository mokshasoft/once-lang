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
module DirectedHoTT.Metatheory.TySub where
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
        ; renTm-cong )
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
open import DirectedHoTT.Spec.Typing
  using ( single; nrs; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ
        ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; _⟶_; β; βfst
        ; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ
        ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss; ξ-ordtrᵃ
        ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ
        ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; tr-J-base; tr-J-Σ; tr-J-Id; tr-J-Unit; tr-J-IMu
        ; tr-taut; hrefl-pw; tr-J-Hom; tr-pw; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜IMu⌝
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
        ; crfl; El-⌜Fin⌝; DIh-ι; DIh-σ; DIh-ρ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc
        ; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι
        ; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β; tr-J-Fin; single2; methS
        ; wk2M; MethTy; fsucS; pairS; motCtx; ty-Desc; ty-DIh; ty-Fin; ⊢⌜Fin⌝
        ; ⊢dι; ⊢dσ; ⊢dρ; ⊢dpay; ⊢dih; ⊢fzero; ⊢fsuc; ⊢fcase; ⊢fcase0; ⊢psplit
        ; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dι; ξ-dσˢ; ξ-dσᶠ
        ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dpayⁱ; ξ-dihᴰ; ξ-dihᵉ
        ; ξ-dihᶜ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0
        ; ξ-psplitᵇ; ξ-psplitᵍ )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( ≅ᵀ-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶-ren; ⟶*-ren; ⟶*-appʳ; ren-comm; subTm-monoˢ; extS-mono
        ; single-mono; stkC?-red; stkA?-red; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans
        ; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ
        ; red→≅ᵀ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-IMu; ⟶ᵀ*-IMuᴵ; ⟶ᵀ*-IMuᴰ
        ; ⟶ᵀ*-Desc; ⟶ᵀ*-DIhᴰ; ⟶ᵀ*-DIhᴹ; ⟶ᵀ*-DIhᶜ; ⟶ᵀ*-DIhᵖ )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( sub-comm; ⟶ᵀ-sub; subTy-comm; sub-comm-ty-ext; iinst-sub; wk-sub
        ; wk2-subTy )

private
  variable
    Γ Δ : Cx

-- Transport a judgment along a type equality (fixed motive — avoids the
-- higher-order motive inference of a bare `subst`).
∋-cast : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {A A' : RTy ⌊ Γ ⌋} →
         A ≡ A' → Γ ∋ x ∷ A → Γ ∋ x ∷ A'
∋-cast refl v = v

⊢-cast : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {A A' : RTy ⌊ Γ ⌋} →
         A ≡ A' → Γ ⊢ t ∷ A → Γ ⊢ t ∷ A'
⊢-cast refl d = d

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
⟶ᵀ-ren ρ (DIh-ι D M j p) = DIh-ι _ _ _ _
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
subTy-monoˢ h (Fin n) = doneᵀ
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
occ-red (ξ-dι r) e = occ-red r e
occ-red {x = x} (ξ-dσˢ {S = S} {f = f} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x S) e)) (∨-false₂ (occTm x S) e)
occ-red {x = x} (ξ-dσᶠ {S = S} {f = f} r) e =
  ∨-false (∨-false₁ (occTm x S) e) (occ-red r (∨-false₂ (occTm x S) e))
occ-red {x = x} (ξ-dρʲ {j = j} {C = C} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x j) e)) (∨-false₂ (occTm x j) e)
occ-red {x = x} (ξ-dρᶜ {j = j} {C = C} r) e =
  ∨-false (∨-false₁ (occTm x j) e) (occ-red r (∨-false₂ (occTm x j) e))
occ-red {x = x} (ξ-dpayᴵ {I = I} {D = D} {C = C} {i = i} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x I) e)) (∨-false (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)) (∨-false (∨-false₁ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))) (∨-false₂ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))))
occ-red {x = x} (ξ-dpayᴰ {I = I} {D = D} {C = C} {i = i} r) e =
  ∨-false (∨-false₁ (occTm x I) e) (∨-false (occ-red r (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e))) (∨-false (∨-false₁ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))) (∨-false₂ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))))
occ-red {x = x} (ξ-dpayᶜ {I = I} {D = D} {C = C} {i = i} r) e =
  ∨-false (∨-false₁ (occTm x I) e) (∨-false (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)) (∨-false (occ-red r (∨-false₁ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))) (∨-false₂ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)))))
occ-red {x = x} (ξ-dpayⁱ {I = I} {D = D} {C = C} {i = i} r) e =
  ∨-false (∨-false₁ (occTm x I) e) (∨-false (∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)) (∨-false (∨-false₁ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))) (occ-red r (∨-false₂ (occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))))))
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
  ∨-false (∨-false (∨-false eM ei) eP) (∨-false eD (∨-false eM (∨-false eD eP)))
  where
  eD = ∨-false₁ (occTm x D) e
  ei = ∨-false₁ (occTm x i) (∨-false₂ (occTm x D) e)
  eM = ∨-false₁ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))
  eP = ∨-false₂ (occTm x m) (∨-false₂ (occTm x i) (∨-false₂ (occTm x D) e))
occ-red {x = x} (dpay-ι I D j i) e =
  ∨-false eI (∨-false (∨-false₁ (occTm x j) eR) (∨-false₂ (occTm x j) eR))
  where
  eI = ∨-false₁ (occTm x I) e
  eR = ∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e)
occ-red {x = x} (dpay-σ I D S f i) e =
  ∨-false (∨-false₁ (occTm x S) eC)
    (∨-false (wk I eI) (∨-false (wk D eD) (∨-false (∨-false (wk f (∨-false₂ (occTm x S) eC)) refl) (wk i ei))))
  where
  wk : (t : RTm _) → occTm x t ≡ false → occTm (vs x) (renTm vs t) ≡ false
  wk t o = trans (occ-ren-eq (λ _ → refl) t) o
  eI = ∨-false₁ (occTm x I) e
  eD = ∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)
  eC = ∨-false₁ (occTm x S ∨ occTm x f) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))
  ei = ∨-false₂ (occTm x S ∨ occTm x f) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))
occ-red {x = x} (dpay-ρ I D j C i) e =
  ∨-false (∨-false eI (∨-false eD (∨-false₁ (occTm x j) eC)))
    (∨-false (wk I eI) (∨-false (wk D eD) (∨-false (wk C (∨-false₂ (occTm x j) eC)) (wk i ei))))
  where
  wk : (t : RTm _) → occTm x t ≡ false → occTm (vs x) (renTm vs t) ≡ false
  wk t o = trans (occ-ren-eq (λ _ → refl) t) o
  eI = ∨-false₁ (occTm x I) e
  eD = ∨-false₁ (occTm x D) (∨-false₂ (occTm x I) e)
  eC = ∨-false₁ (occTm x j ∨ occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))
  ei = ∨-false₂ (occTm x j ∨ occTm x C) (∨-false₂ (occTm x D) (∨-false₂ (occTm x I) e))
occ-red (dih-ι D m j p) e = refl
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
    (cong₂ (λ a b → El (dpay a b b (var vz))) (wk-ren ρ I) (wk-ren ρ D))
    (cong₃ (λ c m t → Π (DIh c m c (var vz)) t) (wk2-ren-tm ρ D) (wk2M-ren ρ M) (methS-ren ρ M))

MethTy-sub : (σ : Sub Γ Δ) (I D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
             subTy σ (MethTy I D M) ≡ MethTy (subTm σ I) (subTm σ D) (subTy (extS (extS σ)) M)
MethTy-sub σ I D M =
  cong₂ (λ P Q → Π (El (subTm σ I)) (Π P Q))
    (cong₂ (λ a b → El (dpay a b b (var vz))) (wk-sub σ I) (wk-sub σ D))
    (cong₃ (λ c m t → Π (DIh c m c (var vz)) t) (wk2-sub-tm σ D) (wk2M-sub σ M) (methS-sub σ M))

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

ren-ty : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
         Γ ⊢ty A → Ren⊢ Γ Δ ρ → Δ ⊢ty renTy ρ A

ren-ty ty-base       h = ty-base
ren-ty ty-Unit       h = ty-Unit
ren-ty ty-Nat        h = ty-Nat
ren-ty (ty-IMu dD di) h = ty-IMu (ren-lemma dD h) (ren-lemma di h)
ren-ty (ty-Desc dI) h = ty-Desc (ren-lemma dI h)
ren-ty {Δ = Δ} {ρ = ρ} (ty-DIh {I = I} {D = D} {M = M} dD dM dC di dp) h =
  ty-DIh (ren-lemma dD h)
    (subst (λ A → ((Δ ▹ El (renTm ρ I)) ▹ A) ⊢ty renTy (extR (extR ρ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-ren ρ I) (wk-ren ρ D))
             (ren-ty dM (Ren⊢-ext (Ren⊢-ext h))))
    (ren-lemma dC h) (ren-lemma di h) (ren-lemma dp h)
ren-ty ty-Fin h = ty-Fin
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
ren-lemma (⊢⌜IMu⌝ dD di) h = ⊢⌜IMu⌝ (ren-lemma dD h) (ren-lemma di h)
ren-lemma ⊢⌜Fin⌝ h = ⊢⌜Fin⌝
ren-lemma (⊢dι dj) h = ⊢dι (ren-lemma dj h)
ren-lemma {ρ = ρ} (⊢dσ {I = I} {S = S} dI dS df) h =
  ⊢dσ (ren-lemma dI h) (ren-lemma dS h)
      (⊢-cast (cong (λ X → Π (El (renTm ρ S)) (Desc X)) (wk-ren ρ I)) (ren-lemma df h))
ren-lemma (⊢dρ dj dC) h = ⊢dρ (ren-lemma dj h) (ren-lemma dC h)
ren-lemma (⊢dpay dD dC di) h = ⊢dpay (ren-lemma dD h) (ren-lemma dC h) (ren-lemma di h)
ren-lemma (⊢con dD di dp) h = ⊢con (ren-lemma dD h) (ren-lemma di h) (ren-lemma dp h)
ren-lemma {Δ = Δ} {ρ = ρ} (⊢dih {I = I} {D = D} {M = M} dD dM de dC di dp) h =
  ⊢dih (ren-lemma dD h)
    (subst (λ A → ((Δ ▹ El (renTm ρ I)) ▹ A) ⊢ty renTy (extR (extR ρ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-ren ρ I) (wk-ren ρ D))
             (ren-ty dM (Ren⊢-ext (Ren⊢-ext h))))
    (⊢-cast (MethTy-ren ρ I D M) (ren-lemma de h))
    (ren-lemma dC h) (ren-lemma di h) (ren-lemma dp h)
ren-lemma {Δ = Δ} {ρ = ρ} (⊢ielim {I = I} {D = D} {M = M} {i = i} {t = t} dD dM de di dt) h =
  ⊢-cast (sym (iinst-ren ρ M i t))
    (⊢ielim (ren-lemma dD h)
      (subst (λ A → ((Δ ▹ El (renTm ρ I)) ▹ A) ⊢ty renTy (extR (extR ρ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-ren ρ I) (wk-ren ρ D))
             (ren-ty dM (Ren⊢-ext (Ren⊢-ext h))))
      (⊢-cast (MethTy-ren ρ I D M) (ren-lemma de h))
      (ren-lemma di h) (ren-lemma dt h))
ren-lemma ⊢fzero h = ⊢fzero
ren-lemma (⊢fsuc dt) h = ⊢fsuc (ren-lemma dt h)
ren-lemma {ρ = ρ} (⊢fcase {P = P} {t = t} dP dt da db) h =
  ⊢-cast (sym (ren-comm-ty ρ P t))
    (⊢fcase (ren-ty dP (Ren⊢-ext h)) (ren-lemma dt h)
            (⊢-cast (ren-comm-ty ρ P fzero) (ren-lemma da h))
            (⊢-cast (fsucS-ren ρ P) (ren-lemma db (Ren⊢-ext h))))
ren-lemma {ρ = ρ} (⊢fcase0 {P = P} {t = t} dP dt) h =
  ⊢-cast (sym (ren-comm-ty ρ P t)) (⊢fcase0 (ren-ty dP (Ren⊢-ext h)) (ren-lemma dt h))
ren-lemma {ρ = ρ} (⊢psplit {P = P} {q = q} dP dq db) h =
  ⊢-cast (sym (ren-comm-ty ρ P q))
    (⊢psplit (ren-ty dP (Ren⊢-ext h)) (ren-lemma dq h)
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
sub-ty (ty-IMu dD di) h = ty-IMu (sub-lemma dD h) (sub-lemma di h)
sub-ty (ty-Desc dI) h = ty-Desc (sub-lemma dI h)
sub-ty {Δ = Δ} {σ = σ} (ty-DIh {I = I} {D = D} {M = M} dD dM dC di dp) h =
  ty-DIh (sub-lemma dD h)
    (subst (λ A → ((Δ ▹ El (subTm σ I)) ▹ A) ⊢ty subTy (extS (extS σ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-sub σ I) (wk-sub σ D))
             (sub-ty dM (Sub⊢-ext (Sub⊢-ext h))))
    (sub-lemma dC h) (sub-lemma di h) (sub-lemma dp h)
sub-ty ty-Fin h = ty-Fin
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
sub-lemma (⊢⌜IMu⌝ dD di) h = ⊢⌜IMu⌝ (sub-lemma dD h) (sub-lemma di h)
sub-lemma ⊢⌜Fin⌝ h = ⊢⌜Fin⌝
sub-lemma (⊢dι dj) h = ⊢dι (sub-lemma dj h)
sub-lemma {σ = σ} (⊢dσ {I = I} {S = S} dI dS df) h =
  ⊢dσ (sub-lemma dI h) (sub-lemma dS h)
      (⊢-cast (cong (λ X → Π (El (subTm σ S)) (Desc X)) (wk-sub σ I)) (sub-lemma df h))
sub-lemma (⊢dρ dj dC) h = ⊢dρ (sub-lemma dj h) (sub-lemma dC h)
sub-lemma (⊢dpay dD dC di) h = ⊢dpay (sub-lemma dD h) (sub-lemma dC h) (sub-lemma di h)
sub-lemma (⊢con dD di dp) h = ⊢con (sub-lemma dD h) (sub-lemma di h) (sub-lemma dp h)
sub-lemma {Δ = Δ} {σ = σ} (⊢dih {I = I} {D = D} {M = M} dD dM de dC di dp) h =
  ⊢dih (sub-lemma dD h)
    (subst (λ A → ((Δ ▹ El (subTm σ I)) ▹ A) ⊢ty subTy (extS (extS σ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-sub σ I) (wk-sub σ D))
             (sub-ty dM (Sub⊢-ext (Sub⊢-ext h))))
    (⊢-cast (MethTy-sub σ I D M) (sub-lemma de h))
    (sub-lemma dC h) (sub-lemma di h) (sub-lemma dp h)
sub-lemma {Δ = Δ} {σ = σ} (⊢ielim {I = I} {D = D} {M = M} {i = i} {t = t} dD dM de di dt) h =
  ⊢-cast (sym (iinst-sub σ M i t))
    (⊢ielim (sub-lemma dD h)
      (subst (λ A → ((Δ ▹ El (subTm σ I)) ▹ A) ⊢ty subTy (extS (extS σ)) M)
             (cong₂ (λ a b → IMu a b (var vz)) (wk-sub σ I) (wk-sub σ D))
             (sub-ty dM (Sub⊢-ext (Sub⊢-ext h))))
      (⊢-cast (MethTy-sub σ I D M) (sub-lemma de h))
      (sub-lemma di h) (sub-lemma dt h))
sub-lemma ⊢fzero h = ⊢fzero
sub-lemma (⊢fsuc dt) h = ⊢fsuc (sub-lemma dt h)
sub-lemma {σ = σ} (⊢fcase {P = P} {t = t} dP dt da db) h =
  ⊢-cast (sym (subTy-comm σ P t))
    (⊢fcase (sub-ty dP (Sub⊢-ext h)) (sub-lemma dt h)
            (⊢-cast (subTy-comm σ P fzero) (sub-lemma da h))
            (⊢-cast (fsucS-sub σ P) (sub-lemma db (Sub⊢-ext h))))
sub-lemma {σ = σ} (⊢fcase0 {P = P} {t = t} dP dt) h =
  ⊢-cast (sym (subTy-comm σ P t)) (⊢fcase0 (sub-ty dP (Sub⊢-ext h)) (sub-lemma dt h))
sub-lemma {σ = σ} (⊢psplit {P = P} {q = q} dP dq db) h =
  ⊢-cast (sym (subTy-comm σ P q))
    (⊢psplit (sub-ty dP (Sub⊢-ext h)) (sub-lemma dq h)
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

------------------------------------------------------------------------
-- ★ arithmetic, kept for downstream users.
+-suc : (j k : ℕ) → (j + suc k) ≡ suc (j + k)
+-suc zero    k = refl
+-suc (suc j) k = cong suc (+-suc j k)

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
