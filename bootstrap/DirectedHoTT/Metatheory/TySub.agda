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
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var
        ; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝
        ; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub; Id-cong₃; ⌜Id⌝-cong₃
        ; jsub-cong₃; Unit; Nat; unit; nzero; nsuc; natrec; ⌜Nat⌝; ⌜Unit⌝
        ; ⌜Mu⌝; Ren; extR; renTm; renTy; Sub; extS; subTm; subTy; idₛ; _∘ᵣ_
        ; _ₛ∘ᵣ_; _ᵣ∘ₛ_; _∘ₛ_; subTy-renTy; renTy-subTy; subTy-subTy
        ; renTy-renTy; subTy-cong; renTy-cong; subTy-id; subTm-renTm
        ; subTm-id; subTm-cong; renTm-renTm; renTm-subTm; ⌜Hom⌝-cong₃
        ; Hom-cong₃; ordtr-cong₅; Desc; Mu; con; elim; lookupD; sel; fields
        ; DCon; dι; dρ; dκ; dnil; _◃_; payTy; payTy-ren; payTy-sub; _∈D_
        ; hereD; thereD; ihs; IMu; icon; ielim; ⌜IMu⌝; ICon; IDesc; iι; iρ
        ; iκ; inil; _◂_; ipayTy; ilookupD; _∈ID_; hereID; thereID; iihs
        ; ifields; εwkTy; εwk-ren; εwk-sub; εwkTm; εwkTm-ren; εwkTm-sub
        ; ipayTy-ren; ipayTy-sub; iext; isingle; ipayTy-cong; subTm-subTm
        ; iext-ren; iext-sub; ipayTy-renⁱ; ipayTy-subⁱ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; _∨_; occTm; ∨-false; ∨-false₁; ∨-false₂
        ; occ-ren-eq; occ-sub; eqv; Avoids; occ-ren-tm; avoids-wk
        ; PosC; posc-var; posc-Hom; posc-ren; posc-sub
        ; pw?; stkC?; pwDom; pwBody; pwShift
        ; pw?-sub; stkC?-sub; pwBody-sub; pwDom-sub
        ; pwBody-occ; ren-as-sub; avoids-pwShift; subTm-occ
        ; stkC?-ren; wk-ren-tm; wk-sub-tm; flat?; flat→stk; flat?-ren; flat?-sub
        ; NoNatC; nnc-base; nnc-Unit; nnc-Π; nnc-Σ; nnc-Hom; nnc-Id
        ; nonatc-ren; nonatc-sub; nonatc-pwBody
        ; stkA?; stkA?-ren; stkA?-sub; stkC?→stkA?
        ; NoNatHd; nnh-base; nnh-Unit; nnh-Σ; nnh-Id; nnh-Π; nnh-Hom; nnh-Mu; nnh-IMu
        ; nonatc→hd; stkC?→hd
        ; occ-sel; occ-fields; occ-ifields; occ-iihs; occ-εwkTm )
open import DirectedHoTT.Spec.Typing
  using ( single; nrs; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝
        ; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss
        ; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; tr-J-base; tr-J-Σ; tr-J-Id; tr-J-Unit; tr-J-Mu; tr-J-IMu; tr-taut; hrefl-pw; tr-J-Hom; tr-pw
        ; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜Mu⌝
        ; El-⌜IMu⌝; ξ-IMu
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ
        ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; El-⌜Id⌝; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ
        ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _⟶*_; done; step
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢absurd; ⊢ordtr; ⊢trU
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢ap; ⊢conv
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec; ⊢⌜Nat⌝; ⊢⌜Unit⌝; ⊢⌜Mu⌝
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom; ty-Id; ty-Unit; ty-Nat
        ; ⊢ctx_; c-◇; c-▹
        ; ι-elim; ξ-con; ξ-elimᵐ; ξ-elimᵗ
        ; ι-ielim; ξ-icon; ξ-ielimⁱ; ξ-ielimᵐ; ξ-ielimᵗ; ξ-⌜IMu⌝
        ; ihTy; atCon; conS; methTy; methsTy; methsTyFrom; atCon-inst; ty-Mu; ⊢con; ⊢elim
        ; DescWf
        ; wk-single; iinst; iihTy; iconS; iatCon; iatCon-inst
        ; imethTy; imethsTy; imethsTyFrom; IDescWf
        ; ty-IMu; ⊢icon; ⊢ielim; ⊢⌜IMu⌝; IConWf; iwf-ρ; iwf-κ; IDescWfFrom; idwf-cons; idwf-nil; _≅_; csym; ctrn; cred; crfl )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ≅ᵀ-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶-ren; ⟶*-ren; ⟶*-appʳ; ren-comm; subTm-monoˢ; extS-mono; single-mono
        ; stkC?-red; stkA?-red
        -- ★ and the type-level relation, also from `RedCong` now:
        ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El
        ; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ
        ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; red→≅ᵀ
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-IMu )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( sub-comm; ⟶ᵀ-sub )

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

subTy-comm : (σ : Sub Γ Δ) (B : RTy (Γ ∙)) (u : RTm Γ) →
             subTy σ (subTy (single u) B) ≡
             subTy (single (subTm σ u)) (subTy (extS σ) B)
subTy-comm {Γ} σ B u =
  trans (subTy-subTy B) (trans (subTy-cong bridge B) (sym (subTy-subTy B)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           (σ ∘ₛ single u) x ≡ (single (subTm σ u) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (subTm-renTm (σ x)) (subTm-id (σ x)))

------------------------------------------------------------------------
-- Conversion survives renaming; types are monotone in the substitution.
------------------------------------------------------------------------

-- Weakening commutes with a renaming, at TERMS — both composites are
-- definitionally `x ↦ vs (ρ x)`.  The `Hom-U`/`Hom-Π` cases need it.
wk-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
         renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
wk-ren ρ t = trans (renTm-renTm t) (sym (renTm-renTm t))

⟶ᵀ-ren : (ρ : Ren Γ Δ) {A B : RTy Γ} → A ⟶ᵀ B → renTy ρ A ⟶ᵀ renTy ρ B
⟶ᵀ-ren ρ El-⌜base⌝    = El-⌜base⌝
⟶ᵀ-ren ρ (El-⌜Π⌝ c d) = El-⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)
⟶ᵀ-ren ρ (El-⌜Σ⌝ c d) = El-⌜Σ⌝ (renTm ρ c) (renTm (extR ρ) d)
⟶ᵀ-ren ρ (El-⌜Hom⌝ c a b) = El-⌜Hom⌝ (renTm ρ c) (renTm ρ a) (renTm ρ b)
-- ★ WF stage C: the datatype decodes.  Both targets are closed formers,
-- so renaming is the identity on them.
⟶ᵀ-ren ρ El-⌜Nat⌝  = El-⌜Nat⌝
⟶ᵀ-ren ρ El-⌜Unit⌝ = El-⌜Unit⌝
⟶ᵀ-ren ρ El-⌜Mu⌝   = El-⌜Mu⌝
⟶ᵀ-ren ρ El-⌜IMu⌝  = El-⌜IMu⌝
⟶ᵀ-ren ρ (ξ-IMu r) = ξ-IMu (⟶-ren ρ r)
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
subTy-monoˢ h (Mu D)   = doneᵀ
-- ⚠ NOT `doneᵀ` like `Mu`: the INDEX is a term, so it moves.
subTy-monoˢ h (IMu D I i) = ⟶ᵀ*-IMu (subTm-monoˢ h i)
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
-- ★ INDUCTIVE TYPES: ι introduces no variable — `occ-fields`/`occ-sel`.
occ-red (ξ-con r) e = occ-red r e
occ-red {x = x} (ξ-elimᵐ {ms = ms} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x ms) e)) (∨-false₂ (occTm x ms) e)
occ-red {x = x} (ξ-elimᵗ {ms = ms} r) e =
  ∨-false (∨-false₁ (occTm x ms) e) (occ-red r (∨-false₂ (occTm x ms) e))
occ-red (ξ-icon r) e = occ-red r e
occ-red (ξ-⌜IMu⌝ r) e = occ-red r e
occ-red {x = x} (ξ-ielimⁱ {i = i} r) e =
  ∨-false (occ-red r (∨-false₁ (occTm x i) e)) (∨-false₂ (occTm x i) e)
occ-red {x = x} (ξ-ielimᵐ {i = i} {ms = ms} r) e =
  ∨-false (∨-false₁ (occTm x i) e)
          (∨-false (occ-red r (∨-false₁ (occTm x ms) (∨-false₂ (occTm x i) e)))
                   (∨-false₂ (occTm x ms) (∨-false₂ (occTm x i) e)))
occ-red {x = x} (ξ-ielimᵗ {i = i} {ms = ms} r) e =
  ∨-false (∨-false₁ (occTm x i) e)
          (∨-false (∨-false₁ (occTm x ms) (∨-false₂ (occTm x i) e))
                   (occ-red r (∨-false₂ (occTm x ms) (∨-false₂ (occTm x i) e))))
occ-red {x = x} (ι-ielim D i ms k p) e =
  occ-ifields D i ms (isingle i) (ilookupD D k) (sel k ms) p
    -- the environment is `isingle i`, so its only slot is `i` itself
    (λ { vz → ∨-false₁ (occTm x i) e })
    (∨-false₁ (occTm x i) e)
    (∨-false₁ (occTm x ms) (∨-false₂ (occTm x i) e))
    (occ-sel k ms (∨-false₁ (occTm x ms) (∨-false₂ (occTm x i) e)))
    (∨-false₂ (occTm x ms) (∨-false₂ (occTm x i) e))
occ-red {x = x} (ι-elim D ms k p) e =
  occ-fields D ms (lookupD D k) (sel k ms) p
    (∨-false₁ (occTm x ms) e)
    (occ-sel k ms (∨-false₁ (occTm x ms) e))
    (∨-false₂ (occTm x ms) e)
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
occ-red {x = x} (tr-J-Mu {D = Dᵐ} c a m s e₀) e =
  ∨-false₂ (occTm x (hrefl (⌜Mu⌝ Dᵐ) s))
           (∨-false₂ (occTm (vs x) (⌜Hom⌝ c a m)) e)
occ-red {x = x} (tr-J-IMu {D = Dⁱ} {I = Iⁱ} {iˣ = iˣ} c a m s e₀) e =
  ∨-false₂ (occTm x (hrefl (⌜IMu⌝ Dⁱ Iⁱ iˣ) s))
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
-- ★★ NATURALITY OF THE ELIMINATOR'S COMPUTED TYPES.
--
-- `ren-lemma`/`sub-lemma` must move a `⊢con`/`⊢elim` derivation across a
-- renaming or substitution, so every computed type needs its commuting
-- law.  ⚠ `payTy` needs none beyond inertness (it is CLOSED — see
-- `payTy-ren`/`payTy-sub` in Pi); the motive-carrying ones do.
------------------------------------------------------------------------

wk-ren-ty : (ρ : Ren Γ Δ) (A : RTy Γ) →
            renTy (extR ρ) (renTy vs A) ≡ renTy vs (renTy ρ A)
wk-ren-ty ρ A = trans (renTy-renTy A) (sym (renTy-renTy A))

atCon-ren : (ρ : Ren Γ Δ) (k : ℕ) (M : RTy (Γ ∙)) →
            renTy (extR ρ) (atCon k M) ≡ atCon k (renTy (extR ρ) M)
atCon-ren ρ k M =
  trans (renTy-subTy M)
        (trans (subTy-cong (λ { vz → refl ; (vs x) → refl }) M)
               (sym (subTy-renTy M)))

-- ★ `conS k` is the IDENTITY on a WEAKENED term: it only rewrites `vz`,
--   and a weakening has no `vz`.  ⚠ true but NOT definitional — this is
--   what `atCon-sub`'s `vs` case needs.
conS-wk : (k : ℕ) (t : RTm Γ) → subTm (conS k) (renTm vs t) ≡ renTm vs t
conS-wk k t =
  trans (subTm-renTm t)
        (trans (subTm-cong (λ y → refl) t) (sym (ren-as-sub vs t)))

atCon-sub : (σ : Sub Γ Δ) (k : ℕ) (M : RTy (Γ ∙)) →
            subTy (extS σ) (atCon k M) ≡ atCon k (subTy (extS σ) M)
atCon-sub σ k M =
  trans (subTy-subTy M)
        (trans (subTy-cong (λ { vz → refl ; (vs x) → sym (conS-wk k (σ x)) }) M)
               (sym (subTy-subTy M)))

ihTy-ren : (ρ : Ren Γ Δ) (D : Desc) (C : DCon) (q : RTm Γ) (M : RTy (Γ ∙)) →
           renTy ρ (ihTy D C q M) ≡ ihTy D C (renTm ρ q) (renTy (extR ρ) M)
ihTy-ren ρ D dι       q M = refl
ihTy-ren ρ D (dρ C)   q M =
  cong₂ Σ' (ren-comm-ty ρ M (fst q))
           (trans (wk-ren-ty ρ (ihTy D C (snd q) M))
                  (cong (renTy vs) (ihTy-ren ρ D C (snd q) M)))
ihTy-ren ρ D (dκ A C) q M = ihTy-ren ρ D C (snd q) M

ihTy-sub : (σ : Sub Γ Δ) (D : Desc) (C : DCon) (q : RTm Γ) (M : RTy (Γ ∙)) →
           subTy σ (ihTy D C q M) ≡ ihTy D C (subTm σ q) (subTy (extS σ) M)
ihTy-sub σ D dι       q M = refl
ihTy-sub σ D (dρ C)   q M =
  cong₂ Σ' (subTy-comm σ M (fst q))
           (trans (wk-sub-ty σ (ihTy D C (snd q) M))
                  (cong (renTy vs) (ihTy-sub σ D C (snd q) M)))
  where
    wk-sub-ty : (σ : Sub Γ Δ) (A : RTy Γ) →
                subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A)
    wk-sub-ty σ A = trans (subTy-renTy A) (sym (renTy-subTy A))
ihTy-sub σ D (dκ A C) q M = ihTy-sub σ D C (snd q) M

methTy-ren : (ρ : Ren Γ Δ) (D : Desc) (k : ℕ) (C : DCon) (M : RTy (Γ ∙)) →
             renTy ρ (methTy D k C M) ≡ methTy D k C (renTy (extR ρ) M)
methTy-ren ρ D k C M =
  cong₂ Π (payTy-ren ρ D C)
          (cong₂ Π (trans (ihTy-ren (extR ρ) D C (var vz) (renTy (extR vs) M))
                          (cong (ihTy D C (var vz)) (extR-swap ρ M)))
                   (trans (wk-ren-ty (extR ρ) (atCon k M))
                          (cong (renTy vs) (atCon-ren ρ k M))))
  where
    -- ★ the two weakenings COMMUTE: pushing `extR ρ` past `extR vs`.
    extR-swap : (ρ : Ren Γ Δ) (M : RTy (Γ ∙)) →
                renTy (extR (extR ρ)) (renTy (extR vs) M)
                  ≡ renTy (extR vs) (renTy (extR ρ) M)
    extR-swap ρ M =
      trans (renTy-renTy M)
            (trans (renTy-cong (λ { vz → refl ; (vs x) → refl }) M)
                   (sym (renTy-renTy M)))

methTy-sub : (σ : Sub Γ Δ) (D : Desc) (k : ℕ) (C : DCon) (M : RTy (Γ ∙)) →
             subTy σ (methTy D k C M) ≡ methTy D k C (subTy (extS σ) M)
methTy-sub σ D k C M =
  cong₂ Π (payTy-sub σ D C)
          (cong₂ Π (trans (ihTy-sub (extS σ) D C (var vz) (renTy (extR vs) M))
                          (cong (ihTy D C (var vz)) (extS-swap σ M)))
                   (trans (wk-sub-ty' (extS σ) (atCon k M))
                          (cong (renTy vs) (atCon-sub σ k M))))
  where
    wk-sub-ty' : (σ : Sub Γ Δ) (A : RTy Γ) →
                 subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A)
    wk-sub-ty' σ A = trans (subTy-renTy A) (sym (renTy-subTy A))

    -- ★ the substitution and the weakening COMMUTE, one binder down.
    extS-swap : (σ : Sub Γ Δ) (M : RTy (Γ ∙)) →
                subTy (extS (extS σ)) (renTy (extR vs) M)
                  ≡ renTy (extR vs) (subTy (extS σ) M)
    extS-swap σ M =
      trans (subTy-renTy M)
            (trans (subTy-cong
                      (λ { vz → refl
                         ; (vs x) → trans (renTm-renTm (σ x))
                                          (sym (renTm-renTm (σ x))) }) M)
                   (sym (renTy-subTy M)))

methsTyFrom-ren : (ρ : Ren Γ Δ) (D : Desc) (M : RTy (Γ ∙)) (j : ℕ) (E : Desc) →
                  renTy ρ (methsTyFrom D M j E)
                    ≡ methsTyFrom D (renTy (extR ρ) M) j E
methsTyFrom-ren ρ D M j dnil    = refl
methsTyFrom-ren ρ D M j (C ◃ E) =
  cong₂ Σ' (methTy-ren ρ D j C M)
           (trans (wk-ren-ty ρ (methsTyFrom D M (suc j) E))
                  (cong (renTy vs) (methsTyFrom-ren ρ D M (suc j) E)))

methsTyFrom-sub : (σ : Sub Γ Δ) (D : Desc) (M : RTy (Γ ∙)) (j : ℕ) (E : Desc) →
                  subTy σ (methsTyFrom D M j E)
                    ≡ methsTyFrom D (subTy (extS σ) M) j E
methsTyFrom-sub σ D M j dnil    = refl
methsTyFrom-sub σ D M j (C ◃ E) =
  cong₂ Σ' (methTy-sub σ D j C M)
           (trans (wk-sub-ty'' σ (methsTyFrom D M (suc j) E))
                  (cong (renTy vs) (methsTyFrom-sub σ D M (suc j) E)))
  where
    wk-sub-ty'' : (σ : Sub Γ Δ) (A : RTy Γ) →
                  subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A)
    wk-sub-ty'' σ A = trans (subTy-renTy A) (sym (renTy-subTy A))

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

sub-comm-ty-ext : (σ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) (j : RTm Γ) →
                  subTy (extS σ) (subTy (extS (single j)) M)
                    ≡ subTy (extS (single (subTm σ j))) (subTy (extS (extS σ)) M)
sub-comm-ty-ext {Γ} σ M j =
  trans (subTy-subTy M) (trans (subTy-cong bridge M) (sym (subTy-subTy M)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           (extS σ ∘ₛ extS (single j)) x
             ≡ (extS (single (subTm σ j)) ∘ₛ extS (extS σ)) x
  bridge vz          = refl
  bridge (vs vz)     = exts-wk-tm σ j
  bridge (vs (vs x)) =
    sym (trans (exts-wk-tm (single (subTm σ j)) (renTm vs (σ x)))
               (cong (renTm vs) (wk-single (σ x))))

-- ★★ the two-slot instantiation is natural.  Built by peeling the two
--    `single`s in order: the SCRUTINEE slot with `ren-comm-ty`, then the
--    INDEX slot with its `-ext` twin.
iinst-ren : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) (j t : RTm Γ) →
            renTy ρ (iinst j t M)
              ≡ iinst (renTm ρ j) (renTm ρ t) (renTy (extR (extR ρ)) M)
iinst-ren ρ M j t =
  trans (ren-comm-ty ρ (subTy (extS (single j)) M) t)
        (cong (subTy (single (renTm ρ t))) (ren-comm-ty-ext ρ M j))

iinst-sub : (σ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) (j t : RTm Γ) →
            subTy σ (iinst j t M)
              ≡ iinst (subTm σ j) (subTm σ t) (subTy (extS (extS σ)) M)
iinst-sub σ M j t =
  trans (subTy-comm σ (subTy (extS (single j)) M) t)
        (cong (subTy (single (subTm σ t))) (sub-comm-ty-ext σ M j))

-- ★ the IH TUPLE's type is natural.  ⚠ the ENVIRONMENT absorbs the action
--   — same shape as `ipayTy-ren` in Syntax, and the reason this layer got
--   SMALLER when the telescope replaced the closed shift.
iihTy-cong : (D : IDesc) (I : RTy ε) {Θ : Cx} {σ σ' : Sub Θ Γ}
             (C : ICon Θ) (q : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
             (∀ x → σ x ≡ σ' x) →
             iihTy D I σ C q M ≡ iihTy D I σ' C q M
iihTy-cong D I iι       q M h = refl
iihTy-cong D I (iρ j C) q M h =
  cong₂ Σ' (cong (λ z → iinst z (fst q) M) (subTm-cong h j))
           (cong (renTy vs) (iihTy-cong D I C (snd q) M
                              (λ { vz → refl ; (vs x) → h x })))
iihTy-cong D I (iκ κ C) q M h =
  iihTy-cong D I C (snd q) M (λ { vz → refl ; (vs x) → h x })

iihTy-ren : (ρ : Ren Γ Δ) (D : IDesc) (I : RTy ε) {Θ : Cx}
            (σ : Sub Θ Γ) (C : ICon Θ) (q : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
            renTy ρ (iihTy D I σ C q M)
              ≡ iihTy D I (λ x → renTm ρ (σ x)) C (renTm ρ q)
                       (renTy (extR (extR ρ)) M)
iihTy-ren ρ D I σ iι       q M = refl
iihTy-ren ρ D I σ (iρ j C) q M =
  cong₂ Σ' (trans (iinst-ren ρ M (subTm σ j) (fst q))
                  (cong (λ z → iinst z (fst (renTm ρ q))
                                     (renTy (extR (extR ρ)) M))
                        (renTm-subTm j)))
           (trans (wk-ren-ty ρ (iihTy D I (iext σ (fst q)) C (snd q) M))
                  (cong (renTy vs)
                        (trans (iihTy-ren ρ D I (iext σ (fst q)) C (snd q) M)
                               (iihTy-cong D I C (snd (renTm ρ q))
                                           (renTy (extR (extR ρ)) M)
                                           (iext-ren ρ σ (fst q))))))
iihTy-ren ρ D I σ (iκ κ C) q M =
  trans (iihTy-ren ρ D I (iext σ (fst q)) C (snd q) M)
        (iihTy-cong D I C (snd (renTm ρ q)) (renTy (extR (extR ρ)) M)
                    (iext-ren ρ σ (fst q)))

iihTy-sub : (τ : Sub Γ Δ) (D : IDesc) (I : RTy ε) {Θ : Cx}
            (σ : Sub Θ Γ) (C : ICon Θ) (q : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
            subTy τ (iihTy D I σ C q M)
              ≡ iihTy D I (λ x → subTm τ (σ x)) C (subTm τ q)
                       (subTy (extS (extS τ)) M)
iihTy-sub τ D I σ iι       q M = refl
iihTy-sub τ D I σ (iρ j C) q M =
  cong₂ Σ' (trans (iinst-sub τ M (subTm σ j) (fst q))
                  (cong (λ z → iinst z (fst (subTm τ q))
                                     (subTy (extS (extS τ)) M))
                        (subTm-subTm j)))
           (trans (wk-sub-ty4 τ (iihTy D I (iext σ (fst q)) C (snd q) M))
                  (cong (renTy vs)
                        (trans (iihTy-sub τ D I (iext σ (fst q)) C (snd q) M)
                               (iihTy-cong D I C (snd (subTm τ q))
                                           (subTy (extS (extS τ)) M)
                                           (iext-sub τ σ (fst q))))))
  where
    wk-sub-ty4 : (τ : Sub Γ Δ) (A : RTy Γ) →
                 subTy (extS τ) (renTy vs A) ≡ renTy vs (subTy τ A)
    wk-sub-ty4 τ A = trans (subTy-renTy A) (sym (renTy-subTy A))
iihTy-sub τ D I σ (iκ κ C) q M =
  trans (iihTy-sub τ D I (iext σ (fst q)) C (snd q) M)
        (iihTy-cong D I C (snd (subTm τ q)) (subTy (extS (extS τ)) M)
                    (iext-sub τ σ (fst q)))

-- ★ the re-based motive is natural.  Only the INDEX slot has content.
iatCon-ren : (ρ : Ren Γ Δ) (k : ℕ) (i : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
             renTy (extR ρ) (iatCon k i M)
               ≡ iatCon k (renTm ρ i) (renTy (extR (extR ρ)) M)
iatCon-ren {Γ} ρ k i M =
  trans (renTy-subTy M) (trans (subTy-cong bridge M) (sym (subTy-renTy M)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           (extR ρ ᵣ∘ₛ iconS k i) x ≡ (iconS k (renTm ρ i) ₛ∘ᵣ extR (extR ρ)) x
  bridge vz          = refl
  bridge (vs vz)     = wk-ren ρ i
  bridge (vs (vs x)) = refl

iatCon-sub : (σ : Sub Γ Δ) (k : ℕ) (i : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
             subTy (extS σ) (iatCon k i M)
               ≡ iatCon k (subTm σ i) (subTy (extS (extS σ)) M)
iatCon-sub {Γ} σ k i M =
  trans (subTy-subTy M) (trans (subTy-cong bridge M) (sym (subTy-subTy M)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           (extS σ ∘ₛ iconS k i) x ≡ (iconS k (subTm σ i) ∘ₛ extS (extS σ)) x
  bridge vz          = refl
  bridge (vs vz)     = exts-wk-tm σ i
  -- ⚠ NOT the `single`-shaped bridge: `iconS` and `extS (single _)` differ
  --   at `vz`, so this row peels two weakenings by hand.
  bridge (vs (vs x)) =
    sym (trans (subTm-renTm (renTm vs (σ x)))
               (trans (subTm-renTm (σ x)) (sym (ren-as-sub vs (σ x)))))

-- ★ one METHOD's type is natural.  ⚠ NO INDEX PARAMETER any more (§9.1) —
--   a method quantifies over the index, so its type mentions none.
imethTy-ren : (ρ : Ren Γ Δ) (D : IDesc) (I : RTy ε) (k : ℕ)
              (C : ICon (ε ∙)) (M : RTy ((Γ ∙) ∙)) →
              renTy ρ (imethTy D I k C M)
                ≡ imethTy D I k C (renTy (extR (extR ρ)) M)
imethTy-ren ρ D I k C M =
  cong₂ Π (εwk-ren ρ I)
          (cong₂ Π (trans (ipayTy-ren (extR ρ) D I (isingle (var vz)) C)
                          (ipayTy-cong D I C (λ { vz → refl })))
                   (cong₂ Π (trans (iihTy-ren (extR (extR ρ)) D I
                                              (isingle (var (vs vz))) C (var vz) _)
                                   (trans (iihTy-cong D I C (var vz) _
                                             (λ { vz → refl }))
                                          (cong (iihTy D I (isingle (var (vs vz)))
                                                       C (var vz))
                                                -- ⚠ the motive is weakened TWICE here
                                                --   (past the index binder AND the
                                                --   payload binder), so the swap has
                                                --   to be composed with itself.
                                                (trans (swap3 (extR ρ)
                                                          (renTy (extR (extR vs)) M))
                                                       (cong (renTy (extR (extR vs)))
                                                             (swap3 ρ M))))))
                            (trans (wk-ren-ty (extR (extR ρ)) (iatCon k (var vz) _))
                                   (cong (renTy vs)
                                         (trans (iatCon-ren (extR ρ) k (var vz) _)
                                                (cong (iatCon k (var vz))
                                                      (swap3 ρ M)))))))
  where
    -- pushing `extR³ ρ` past `extR² vs` — the motive's two slots must end
    -- up under the SAME binders on both sides.
    swap3 : (ρ : Ren Γ Δ) (M : RTy ((Γ ∙) ∙)) →
            renTy (extR (extR (extR ρ))) (renTy (extR (extR vs)) M)
              ≡ renTy (extR (extR vs)) (renTy (extR (extR ρ)) M)
    swap3 ρ M =
      trans (renTy-renTy M)
            (trans (renTy-cong (λ { vz → refl ; (vs vz) → refl
                                  ; (vs (vs x)) → refl }) M)
                   (sym (renTy-renTy M)))

imethTy-sub : (τ : Sub Γ Δ) (D : IDesc) (I : RTy ε) (k : ℕ)
              (C : ICon (ε ∙)) (M : RTy ((Γ ∙) ∙)) →
              subTy τ (imethTy D I k C M)
                ≡ imethTy D I k C (subTy (extS (extS τ)) M)
imethTy-sub τ D I k C M =
  cong₂ Π (εwk-sub τ I)
          (cong₂ Π (trans (ipayTy-sub (extS τ) D I (isingle (var vz)) C)
                          (ipayTy-cong D I C (λ { vz → refl })))
                   (cong₂ Π (trans (iihTy-sub (extS (extS τ)) D I
                                              (isingle (var (vs vz))) C (var vz) _)
                                   (trans (iihTy-cong D I C (var vz) _
                                             (λ { vz → refl }))
                                          (cong (iihTy D I (isingle (var (vs vz)))
                                                       C (var vz))
                                                (trans (swap3s (extS τ)
                                                          (renTy (extR (extR vs)) M))
                                                       (cong (renTy (extR (extR vs)))
                                                             (swap3s τ M))))))
                            (trans (wk-sub-ty5 (extS (extS τ)) (iatCon k (var vz) _))
                                   (cong (renTy vs)
                                         (trans (iatCon-sub (extS τ) k (var vz) _)
                                                (cong (iatCon k (var vz))
                                                      (swap3s τ M)))))))
  where
    wk-sub-ty5 : (τ : Sub Γ Δ) (A : RTy Γ) →
                 subTy (extS τ) (renTy vs A) ≡ renTy vs (subTy τ A)
    wk-sub-ty5 τ A = trans (subTy-renTy A) (sym (renTy-subTy A))
    swap3s : (τ : Sub Γ Δ) (M : RTy ((Γ ∙) ∙)) →
             subTy (extS (extS (extS τ))) (renTy (extR (extR vs)) M)
               ≡ renTy (extR (extR vs)) (subTy (extS (extS τ)) M)
    swap3s τ M =
      trans (subTy-renTy M)
            (trans (subTy-cong
                      (λ { vz → refl ; (vs vz) → refl
                         ; (vs (vs x)) →
                             trans (cong (renTm vs) (renTm-renTm (τ x)))
                                   (trans (renTm-renTm (τ x))
                                          (sym (trans (cong (renTm (extR (extR vs)))
                                                            (renTm-renTm (τ x)))
                                                      (renTm-renTm (τ x))))) }) M)
                   (sym (renTy-subTy M)))

imethsTyFrom-ren : (ρ : Ren Γ Δ) (D : IDesc) (I : RTy ε) (M : RTy ((Γ ∙) ∙))
                   (j : ℕ) (E : IDesc) →
                   renTy ρ (imethsTyFrom D I M j E)
                     ≡ imethsTyFrom D I (renTy (extR (extR ρ)) M) j E
imethsTyFrom-ren ρ D I M j inil    = refl
imethsTyFrom-ren ρ D I M j (C ◂ E) =
  cong₂ Σ' (imethTy-ren ρ D I j C M)
           (trans (wk-ren-ty ρ (imethsTyFrom D I M (suc j) E))
                  (cong (renTy vs) (imethsTyFrom-ren ρ D I M (suc j) E)))

imethsTyFrom-sub : (τ : Sub Γ Δ) (D : IDesc) (I : RTy ε) (M : RTy ((Γ ∙) ∙))
                   (j : ℕ) (E : IDesc) →
                   subTy τ (imethsTyFrom D I M j E)
                     ≡ imethsTyFrom D I (subTy (extS (extS τ)) M) j E
imethsTyFrom-sub τ D I M j inil    = refl
imethsTyFrom-sub τ D I M j (C ◂ E) =
  cong₂ Σ' (imethTy-sub τ D I j C M)
           (trans (wk-sub-ty6 τ (imethsTyFrom D I M (suc j) E))
                  (cong (renTy vs) (imethsTyFrom-sub τ D I M (suc j) E)))
  where
    wk-sub-ty6 : (τ : Sub Γ Δ) (A : RTy Γ) →
                 subTy (extS τ) (renTy vs A) ≡ renTy vs (subTy τ A)
    wk-sub-ty6 τ A = trans (subTy-renTy A) (sym (renTy-subTy A))

------------------------------------------------------------------------
-- ★★ MONOTONICITY — WHAT SURVIVED §9.1.
--
-- This block used to carry `ipayTy-mono` … `imethsTyFrom-mono`, and its
-- header called that layer "the clearest place where indexing costs
-- something rather than mirroring something".  THAT WAS THE WRONG
-- READING.  A metatheory layer with no counterpart in the non-indexed
-- development is a tell that a DEFINITION is wrong, not a cost to pay:
-- methods were typed at ONE index, so `imethsTy` mentioned a term
-- `ξ-ielimⁱ` could move, so it needed monotonicity.  With methods
-- index-quantified there is nothing to move, and six lemmas were DELETED
-- rather than fixed.
--
-- ⚠ `iinst-mono` is the one genuine cost of indexing here: under
--   `ξ-ielimⁱ` the RESULT type `iinst i t M` really does move.
------------------------------------------------------------------------

⟶ᵀ*-sub' : (σ : Sub Γ Δ) {A A' : RTy Γ} → A ⟶ᵀ* A' → subTy σ A ⟶ᵀ* subTy σ A'
⟶ᵀ*-sub' σ doneᵀ       = doneᵀ
⟶ᵀ*-sub' σ (stepᵀ r p) = stepᵀ (⟶ᵀ-sub σ r) (⟶ᵀ*-sub' σ p)

-- ⚠ TWO slots move, for two different rules: `ξ-ielimⁱ` steps the INDEX,
--   `ξ-ielimᵗ` steps the SCRUTINEE.  The scrutinee one is exactly the
--   non-indexed `ξ-elimᵗ` shape; the index one has no non-indexed twin.
-- ★★ `ipayTy-mono` IS BACK — and this corrects the claim in the §9.1
--   commit that all six monotonicity lemmas were deleted outright.
--   ⚠ It returns for a DIFFERENT reason than it left.  It left because
--   `imethsTy` mentioned the index, which was the formulation bug.  It
--   returns because `IMu-inj` yields a CONVERSION `i ≅ i''` where
--   `Mu-inj` yields a syntactic `D ≡ D'` — so ι's payload derivation must
--   be TRANSPORTED along that conversion, which the non-indexed ι never
--   has to do.  Same `Mu`-is-inert / `IMu`-is-inert-SHAPED asymmetry that
--   made `IMu-reduct` a record where `Mu-reduct` was `stepᵀ ()`.
ipayTy-mono : (D : IDesc) (I : RTy ε) {Θ : Cx} {σ σ' : Sub Θ Γ} (C : ICon Θ) →
              (∀ x → σ x ⟶* σ' x) →
              ipayTy D I σ C ⟶ᵀ* ipayTy D I σ' C
ipayTy-mono D I iι       h = doneᵀ
ipayTy-mono D I (iρ j C) h =
  ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (⟶ᵀ*-IMu (subTm-monoˢ h j)))
            (⟶ᵀ*-Σʳ (ipayTy-mono D I C (extS-mono h)))
ipayTy-mono D I (iκ κ C) h =
  ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (⟶ᵀ*-El (subTm-monoˢ h κ)))
            (⟶ᵀ*-Σʳ (ipayTy-mono D I C (extS-mono h)))

-- ★ `ipayTy-conv` STAYED IN `SubjectReduction`: it is the one definition
--   in this range that calls `church-rosser`, and its only caller is
--   the indexed-ι block, which stays behind too.

iinst-monoˢ : (M : RTy ((Γ ∙) ∙)) (j : RTm Γ) {t t' : RTm Γ} →
              t ⟶* t' → iinst j t M ⟶ᵀ* iinst j t' M
iinst-monoˢ M j r = subTy-monoˢ (single-mono r) (subTy (extS (single j)) M)

iinst-mono : (M : RTy ((Γ ∙) ∙)) (t : RTm Γ) {j j' : RTm Γ} →
             j ⟶* j' → iinst j t M ⟶ᵀ* iinst j' t M
iinst-mono M t r =
  ⟶ᵀ*-sub' (single t)
    (subTy-monoˢ (λ { vz → done ; (vs vz) → ⟶*-ren vs r ; (vs (vs x)) → done }) M)

ren-ty : {Γ Δ : Ctx} {ρ : Ren ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
         Γ ⊢ty A → Ren⊢ Γ Δ ρ → Δ ⊢ty renTy ρ A

ren-ty ty-base       h = ty-base
ren-ty ty-Unit       h = ty-Unit
ren-ty ty-Nat        h = ty-Nat
ren-ty (ty-Mu w)     h = ty-Mu w
ren-ty {ρ = ρ} (ty-IMu {I = I} w di) h =
  ty-IMu w (⊢-cast (εwk-ren ρ I) (ren-lemma di h))
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
-- ★ INDUCTIVE TYPES.  `payTy` is CLOSED, so the payload's type is inert
-- under renaming; the motive's is not, and rides `methsTyFrom-ren`.
ren-lemma {ρ = ρ} (⊢con {D = D} {k = k} w i dp) h =
  ⊢con w i (⊢-cast (payTy-ren ρ D (lookupD D k)) (ren-lemma dp h))
ren-lemma {ρ = ρ} (⊢elim {D = D} {M = M} {t = t} w dM dms dt) h =
  ⊢-cast (sym (ren-comm-ty ρ M t))
    (⊢elim w (ren-ty dM (Ren⊢-ext h))
           (⊢-cast (methsTyFrom-ren ρ D M zero D) (ren-lemma dms h))
           (ren-lemma dt h))
ren-lemma {ρ = ρ} (⊢natrec {M = M} {n = n} dM dz ds dn) h =
  ⊢-cast (sym (ren-comm-ty ρ M n))
    (⊢natrec (ren-ty dM (Ren⊢-ext h))
             (⊢-cast (ren-comm-ty ρ M nzero) (ren-lemma dz h))
             (⊢-cast (nrs-ren ρ M) (ren-lemma ds (Ren⊢-ext (Ren⊢-ext h))))
             (ren-lemma dn h))
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
ren-lemma (⊢⌜Mu⌝ w) h = ⊢⌜Mu⌝ w
ren-lemma {ρ = ρ} (⊢⌜IMu⌝ {I = I} w di) h =
  ⊢⌜IMu⌝ w (⊢-cast (εwk-ren ρ I) (ren-lemma di h))
ren-lemma {ρ = ρ} (⊢icon {D = D} {I = I} {i = i} {k = k} w kin di dp) h =
  ⊢icon w kin (⊢-cast (εwk-ren ρ I) (ren-lemma di h))
        (⊢-cast (ipayTy-renⁱ ρ D I i (ilookupD D k)) (ren-lemma dp h))
-- ★★ ⚠ THE FIRST RULE WHOSE MOTIVE CONTEXT IS NOT DEFINITIONALLY STABLE.
--   `⊢elim`'s is `Γ ▹ Mu D` and `⊢natrec`'s is `Γ ▹ Nat`; both survive
--   `renTy ρ` on the nose.  `⊢ielim`'s is `Γ ▹ εwkTy I`, which does NOT —
--   it is only propositionally fixed, by `εwk-ren`.  Hence a `subst` on
--   the CONTEXT slot, which no other clause here needs.  It is harmless
--   because `⌊ Γ ▹ A ⌋ = ⌊ Γ ⌋ ∙` ignores `A`, so no `RTy` index moves.
ren-lemma {Δ = Δ} {ρ = ρ} (⊢ielim {D = D} {I = I} {M = M} {i = i} {t = t}
                                  w dM di dms dt) h =
  ⊢-cast (sym (iinst-ren ρ M i t))
    (⊢ielim w
      (subst (λ A → ((Δ ▹ A) ▹ IMu D I (var vz)) ⊢ty renTy (extR (extR ρ)) M)
             (εwk-ren ρ I)
             (ren-ty dM (Ren⊢-ext (Ren⊢-ext h))))
      (⊢-cast (εwk-ren ρ I) (ren-lemma di h))
      (⊢-cast (imethsTyFrom-ren ρ D I M zero D) (ren-lemma dms h))
      (ren-lemma dt h))
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

sub-lemma : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
            Γ ⊢ t ∷ A → Sub⊢ Γ Δ σ → Δ ⊢ subTm σ t ∷ subTy σ A
sub-ty : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {A : RTy ⌊ Γ ⌋} →
         Γ ⊢ty A → Sub⊢ Γ Δ σ → Δ ⊢ty subTy σ A

sub-ty ty-base      h = ty-base
sub-ty ty-Unit      h = ty-Unit
sub-ty ty-Nat       h = ty-Nat
sub-ty (ty-Mu w)    h = ty-Mu w
sub-ty {σ = σ} (ty-IMu {I = I} w di) h =
  ty-IMu w (⊢-cast (εwk-sub σ I) (sub-lemma di h))
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
sub-lemma {σ = σ} (⊢con {D = D} {k = k} w i dp) h =
  ⊢con w i (⊢-cast (payTy-sub σ D (lookupD D k)) (sub-lemma dp h))
sub-lemma {σ = σ} (⊢elim {D = D} {M = M} {t = t} w dM dms dt) h =
  ⊢-cast (sym (subTy-comm σ M t))
    (⊢elim w (sub-ty dM (Sub⊢-ext h))
           (⊢-cast (methsTyFrom-sub σ D M zero D) (sub-lemma dms h))
           (sub-lemma dt h))
sub-lemma {σ = σ} (⊢natrec {M = M} {n = n} dM dz ds dn) h =
  ⊢-cast (sym (subTy-comm σ M n))
    (⊢natrec (sub-ty dM (Sub⊢-ext h))
             (⊢-cast (subTy-comm σ M nzero) (sub-lemma dz h))
             (⊢-cast (nrs-sub σ M) (sub-lemma ds (Sub⊢-ext (Sub⊢-ext h))))
             (sub-lemma dn h))
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
sub-lemma (⊢⌜Mu⌝ w) h = ⊢⌜Mu⌝ w
sub-lemma {σ = σ} (⊢⌜IMu⌝ {I = I} w di) h =
  ⊢⌜IMu⌝ w (⊢-cast (εwk-sub σ I) (sub-lemma di h))
sub-lemma {σ = σ} (⊢icon {D = D} {I = I} {i = i} {k = k} w kin di dp) h =
  ⊢icon w kin (⊢-cast (εwk-sub σ I) (sub-lemma di h))
        (⊢-cast (ipayTy-subⁱ σ D I i (ilookupD D k)) (sub-lemma dp h))
sub-lemma {Δ = Δ} {σ = σ} (⊢ielim {D = D} {I = I} {M = M} {i = i} {t = t}
                                  w dM di dms dt) h =
  ⊢-cast (sym (iinst-sub σ M i t))
    (⊢ielim w
      (subst (λ A → ((Δ ▹ A) ▹ IMu D I (var vz)) ⊢ty subTy (extS (extS σ)) M)
             (εwk-sub σ I)
             (sub-ty dM (Sub⊢-ext (Sub⊢-ext h))))
      (⊢-cast (εwk-sub σ I) (sub-lemma di h))
      (⊢-cast (imethsTyFrom-sub σ D I M zero D) (sub-lemma dms h))
      (sub-lemma dt h))
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

----------------------------------------------------------------- ★ arithmetic the indexed-ι block needs, brought along with it.
+-suc : (j k : ℕ) → (j + suc k) ≡ suc (j + k)
+-suc zero    k = refl
+-suc (suc j) k = cong suc (+-suc j k)

---------
-- ★★★ AND THE **INDEXED-ι** LEMMAS COME WITH THEM — `iinst-wf`,
--   `ipayTy-sub-single`, `iext-Sub⊢`, `iihTy-wf`, `isingle-Sub⊢`.
--
-- ⚠⚠ THIS IS THE LAST MILE, AND IT WAS THE WHOLE WIN.  Repointing 172
--   modules at `TySub` bought the knot NOTHING while these five sat
--   here, because `Lib/IWk`, `Lib/ISub`, `Lib/IFold` and `Lib/IPay` want
--   them — and EVERY knot module goes through those four.  Measured
--   before this move: 112 of 112 knot modules still reached
--   `Confluence`, 13.0 MB of metatheory each.
--
-- ★ AND THEY DO NOT BELONG DOWNSTREAM.  Their dependency cone inside
--   `SubjectReduction` is FIVE definitions and touches neither `sr` nor
--   any `gen-*`; they sat after `sr` for narrative reasons only.  The
--   section header called them "the two lemmas the indexed ι needs",
--   which is why they were filed with ι — but ι needing them is not the
--   same as them needing ι.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ THE TWO LEMMAS THE INDEXED ι NEEDS.
------------------------------------------------------------------------

-- instantiating the TWO-SLOT motive at a well-typed index and scrutinee
-- yields a well-formed type.  Two `⊢single`s, outermost last.
iinst-wf : {Γ : Ctx} (D : IDesc) (I : RTy ε) (M : RTy ((⌊ Γ ⌋ ∙) ∙))
           (j t : RTm ⌊ Γ ⌋) →
           Γ ⊢ j ∷ εwkTy I → Γ ⊢ t ∷ IMu D I j →
           ((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M →
           Γ ⊢ty iinst j t M
iinst-wf {Γ} D I M j t dj dt dM =
  sub-ty (sub-ty dM (Sub⊢-ext (⊢single dj))) (⊢single dt')
  where
    dt' : Γ ⊢ t ∷ subTy (single j) (IMu D I (var vz))
    dt' = dt

-- the tail of a payload lives under the Σ-binder; instantiating it at the
-- head field IS the payload type at the extended ENVIRONMENT.  ⚠ this is
-- the type-level/term-level bridge: `ipayTy` extends with `extS`, `iihs`
-- with `iext`, and `single` is what connects them.
ipayTy-sub-single : {Γ Θ : Cx} (D : IDesc) (I : RTy ε) (σ : Sub Θ Γ)
                    (v : RTm Γ) (C : ICon (Θ ∙)) →
                    subTy (single v) (ipayTy D I (extS σ) C)
                      ≡ ipayTy D I (iext σ v) C
ipayTy-sub-single D I σ v C =
  trans (ipayTy-sub (single v) D I (extS σ) C)
        (ipayTy-cong D I C (λ { vz → refl ; (vs x) → wk-single (σ x) }))

-- extending a well-typed environment by a well-typed value.
iext-Sub⊢ : {Γ Θ : Ctx} {σ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋} {A : RTy ⌊ Θ ⌋} {v : RTm ⌊ Γ ⌋} →
            Sub⊢ Θ Γ σ → Γ ⊢ v ∷ subTy σ A → Sub⊢ (Θ ▹ A) Γ (iext σ v)
iext-Sub⊢ {σ = σ} {A = A} h dv here =
  ⊢-cast (sym (trans (subTy-renTy A)
                     (subTy-cong (λ x → refl) A))) dv
iext-Sub⊢ {σ = σ} h dv (there {A = A₀} x) =
  ⊢-cast (sym (trans (subTy-renTy A₀)
                     (subTy-cong (λ x → refl) A₀))) (h x)

-- the IH TUPLE'S TYPE is well-formed.  Mirrors `ihTy-wf`; the `iρ` row's
-- first component is the motive instantiated at the recursive field.
iihTy-wf : {Γ Θ : Ctx} (D : IDesc) (I : RTy ε) (M : RTy ((⌊ Γ ⌋ ∙) ∙))
           (σ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋) (C : ICon ⌊ Θ ⌋) (p : RTm ⌊ Γ ⌋) →
           IConWf D I Θ C → Sub⊢ Θ Γ σ →
           ((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M →
           Γ ⊢ p ∷ ipayTy D I σ C →
           Γ ⊢ty iihTy D I σ C p M
iihTy-wf D I M σ iι p wC hσ dM hp = ty-Unit
iihTy-wf {Γ} {Θ} D I M σ (iρ j C) p (iwf-ρ .j dj wC) hσ dM hp =
  ty-Σ (iinst-wf D I M (subTm σ j) (fst p)
                 (⊢-cast (εwk-sub σ I) (sub-lemma dj hσ)) (⊢fst hp) dM)
       (ren-ty (iihTy-wf D I M (iext σ (fst p)) C (snd p) wC
                         (iext-Sub⊢ hσ (⊢fst hp)) dM
                         (⊢-cast (ipayTy-sub-single D I σ (fst p) C) (⊢snd hp)))
               there)
iihTy-wf D I M σ (iκ κ C) p (iwf-κ .κ _ dcode wC) hσ dM hp =
  iihTy-wf D I M (iext σ (fst p)) C (snd p) wC
           (iext-Sub⊢ hσ (⊢fst hp)) dM
           (⊢-cast (ipayTy-sub-single D I σ (fst p) C) (⊢snd hp))

-- `sel k` extracts method `k` at its own tag.  ⚠ NO INDEX PARAMETER —
--   after §9.1 a method's type mentions no particular index, which is
--   precisely what makes `iihs-ty` below possible at all.
isel-ty : {Γ : Ctx} (D : IDesc) (I : RTy ε) (M : RTy ((⌊ Γ ⌋ ∙) ∙))
          (E : IDesc) (j k : ℕ) (ms : RTm ⌊ Γ ⌋) → k ∈ID E →
          Γ ⊢ ms ∷ imethsTyFrom D I M j E →
          Γ ⊢ sel k ms ∷ imethTy D I (j + k) (ilookupD E k) M
isel-ty {Γ} D I M (C ◂ E) j zero ms hereID hms =
  ⊢-cast (cong (λ n → imethTy D I n C M) (sym (+zero j))) (⊢fst hms)
  where
    +zero : (n : ℕ) → (n + zero) ≡ n
    +zero zero    = refl
    +zero (suc n) = cong suc (+zero n)
isel-ty {Γ} D I M (C ◂ E) j (suc k) ms (thereID i) hms =
  ⊢-cast (cong (λ n → imethTy D I n (ilookupD E k) M) (sym (+-suc j k)))
         (isel-ty D I M E (suc j) k (snd ms) i
                  (⊢-cast (wk-sub-single (imethsTyFrom D I M (suc j) E) (fst ms))
                          (⊢snd hms)))
  where
    wk-sub-single : (A : RTy ⌊ Γ ⌋) (u : RTm ⌊ Γ ⌋) →
                    subTy (single u) (renTy vs A) ≡ A
    wk-sub-single A u =
      trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))

-- the k-th constructor of a well-formed description is well-formed, in
-- the STARTING telescope `◇ ▹ εwkTy I` (just the ambient index bound).
ilookupD-wf : {I : RTy ε} {D E : IDesc} (k : ℕ) →
              IDescWfFrom D I E → k ∈ID E →
              IConWf D I (◇ ▹ εwkTy I) (ilookupD E k)
ilookupD-wf zero    (idwf-cons wC wE) hereID      = wC
ilookupD-wf (suc k) (idwf-cons wC wE) (thereID m) = ilookupD-wf k wE m

-- ★ a well-typed index IS a well-typed environment for the starting
--   telescope — the base case that gets `iihs-ty` off the ground.
isingle-Sub⊢ : {Γ : Ctx} {I : RTy ε} {i : RTm ⌊ Γ ⌋} →
               Γ ⊢ i ∷ εwkTy I → Sub⊢ (◇ ▹ εwkTy I) Γ (isingle i)
isingle-Sub⊢ {I = I} di here =
  ⊢-cast (sym (trans (subTy-renTy (εwkTy I)) (εwk-sub _ I))) di
isingle-Sub⊢ di (there ())
