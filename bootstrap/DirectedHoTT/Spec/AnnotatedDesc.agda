------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE DESCRIPTION FUNCTIONS, ANNOTATED.
--                      (PLAN-BIDI §3d — what `⊢ᴬ` needs for the inductive
--                       formers)
--
-- ★ Each function is `Spec/Typing`'s / `Spec/Syntax`'s, over annotated
--   syntax, and each has ONE lemma: its erasure IS the original applied to
--   erasures.  That lemma is all `Metatheory/Erasure` needs for the
--   inductive rules.
--
-- ★ The only place annotation is CREATED rather than copied: `conSᴬ` and
--   `iconSᴬ` build `con`/`icon` terms, which in `ATm` carry their
--   description (and index type and index).  The index of the constructed
--   `icon` is the weakened ambient index — exactly what `iatCon` means.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.AnnotatedDesc where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing
  using ( single; nrs; ihTy; conS; atCon; methTy; methsTyFrom; methsTy
        ; iinst; iihTy; iconS; iatCon; imethTy; imethsTyFrom; imethsTy )
open import DirectedHoTT.Spec.Annotated

private
  variable
    Γ Δ : Cx

  cong3 : {A B C D : Set} (f : A → B → C → D) {a a' : A} {b b' : B} {c c' : C} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong3 f refl refl refl = refl

------------------------------------------------------------------------
-- 0. Substitutions.
------------------------------------------------------------------------

singleᴬ : ATm Γ → Subᴬ (Γ ∙) Γ
singleᴬ u vz     = u
singleᴬ u (vs x) = var x

era-single : (u : ATm Γ) → ∀ x → ⌈ singleᴬ u x ⌉ ≡ single ⌈ u ⌉ x
era-single u vz     = refl
era-single u (vs x) = refl

εsubᴬ : Subᴬ ε Γ
εsubᴬ ()

εwkTyᴬ : ATy ε → ATy Γ
εwkTyᴬ = subTyᴬ εsubᴬ

εwkTmᴬ : ATm ε → ATm Γ
εwkTmᴬ = subTmᴬ εsubᴬ

era-εwkTy : (A : ATy ε) → ⌈ εwkTyᴬ {Γ} A ⌉ᵀ ≡ εwkTy ⌈ A ⌉ᵀ
era-εwkTy A = era-subTy εsubᴬ εsub (λ ()) A

era-εwkTm : (t : ATm ε) → ⌈ εwkTmᴬ {Γ} t ⌉ ≡ εwkTm ⌈ t ⌉
era-εwkTm t = era-subTm εsubᴬ εsub (λ ()) t

isingleᴬ : ATm Γ → Subᴬ (ε ∙) Γ
isingleᴬ i vz      = i
isingleᴬ i (vs ())

era-isingle : (i : ATm Γ) → ∀ x → ⌈ isingleᴬ i x ⌉ ≡ isingle ⌈ i ⌉ x
era-isingle i vz      = refl
era-isingle i (vs ())

iextᴬ : Subᴬ Δ Γ → ATm Γ → Subᴬ (Δ ∙) Γ
iextᴬ σ v vz     = v
iextᴬ σ v (vs x) = σ x

era-iext : {σ : Subᴬ Δ Γ} {τ : Sub Δ Γ} → (∀ x → ⌈ σ x ⌉ ≡ τ x) →
           (v : ATm Γ) → ∀ x → ⌈ iextᴬ σ v x ⌉ ≡ iext τ ⌈ v ⌉ x
era-iext h v vz     = refl
era-iext h v (vs x) = h x

------------------------------------------------------------------------
-- 1. Non-indexed descriptions.
------------------------------------------------------------------------

lookupDᴬ : ADesc → ℕ → ADCon
lookupDᴬ dnil    _       = dι
lookupDᴬ (C ◃ D) zero    = C
lookupDᴬ (C ◃ D) (suc k) = lookupDᴬ D k

era-lookupD : (D : ADesc) (k : ℕ) → ⌈ lookupDᴬ D k ⌉ᴰᶜ ≡ lookupD ⌈ D ⌉ᴰ k
era-lookupD dnil    k       = refl
era-lookupD (C ◃ D) zero    = refl
era-lookupD (C ◃ D) (suc k) = era-lookupD D k

payTyᴬ : ADesc → ADCon → ATy Γ
payTyᴬ D dι       = Unit
payTyᴬ D (dρ C)   = Σ' (Mu D) (payTyᴬ D C)
payTyᴬ D (dκ A C) = Σ' (εwkTyᴬ A) (payTyᴬ D C)

era-payTy : (D : ADesc) (C : ADCon) → ⌈ payTyᴬ {Γ} D C ⌉ᵀ ≡ payTy ⌈ D ⌉ᴰ ⌈ C ⌉ᴰᶜ
era-payTy D dι       = refl
era-payTy D (dρ C)   = cong (Σ' (Mu ⌈ D ⌉ᴰ)) (era-payTy D C)
era-payTy D (dκ A C) = cong₂ Σ' (era-εwkTy A) (era-payTy D C)

ihTyᴬ : ADesc → ADCon → ATm Γ → ATy (Γ ∙) → ATy Γ
ihTyᴬ D dι       q M = Unit
ihTyᴬ D (dρ C)   q M = Σ' (subTyᴬ (singleᴬ (fst q)) M) (renTyᴬ vs (ihTyᴬ D C (snd q) M))
ihTyᴬ D (dκ A C) q M = ihTyᴬ D C (snd q) M

era-ihTy : (D : ADesc) (C : ADCon) (q : ATm Γ) (M : ATy (Γ ∙)) →
           ⌈ ihTyᴬ D C q M ⌉ᵀ ≡ ihTy ⌈ D ⌉ᴰ ⌈ C ⌉ᴰᶜ ⌈ q ⌉ ⌈ M ⌉ᵀ
era-ihTy D dι       q M = refl
era-ihTy D (dρ C)   q M =
  cong₂ Σ' (era-subTy (singleᴬ (fst q)) (single (fst ⌈ q ⌉)) (era-single (fst q)) M)
           (trans (era-renTy vs (ihTyᴬ D C (snd q) M)) (cong (renTy vs) (era-ihTy D C (snd q) M)))
era-ihTy D (dκ A C) q M = era-ihTy D C (snd q) M

-- ★ annotation CREATED: the constructed `con` carries its description
conSᴬ : ADesc → ℕ → Subᴬ (Γ ∙) (Γ ∙)
conSᴬ D k vz     = con D k (var vz)
conSᴬ D k (vs x) = var (vs x)

era-conS : (D : ADesc) (k : ℕ) → ∀ (x : Var (Γ ∙)) → ⌈ conSᴬ D k x ⌉ ≡ conS k x
era-conS D k vz     = refl
era-conS D k (vs x) = refl

atConᴬ : ADesc → ℕ → ATy (Γ ∙) → ATy (Γ ∙)
atConᴬ D k M = subTyᴬ (conSᴬ D k) M

era-atCon : (D : ADesc) (k : ℕ) (M : ATy (Γ ∙)) → ⌈ atConᴬ D k M ⌉ᵀ ≡ atCon k ⌈ M ⌉ᵀ
era-atCon D k M = era-subTy (conSᴬ D k) (conS k) (era-conS D k) M

methTyᴬ : ADesc → ℕ → ADCon → ATy (Γ ∙) → ATy Γ
methTyᴬ D k C M =
  Π (payTyᴬ D C)
    (Π (ihTyᴬ D C (var vz) (renTyᴬ (extR vs) M))
       (renTyᴬ vs (atConᴬ D k M)))

era-methTy : (D : ADesc) (k : ℕ) (C : ADCon) (M : ATy (Γ ∙)) →
             ⌈ methTyᴬ D k C M ⌉ᵀ ≡ methTy ⌈ D ⌉ᴰ k ⌈ C ⌉ᴰᶜ ⌈ M ⌉ᵀ
era-methTy D k C M =
  cong₂ Π (era-payTy D C)
    (cong₂ Π (trans (era-ihTy D C (var vz) (renTyᴬ (extR vs) M))
                    (cong (ihTy ⌈ D ⌉ᴰ ⌈ C ⌉ᴰᶜ (var vz)) (era-renTy (extR vs) M)))
             (trans (era-renTy vs (atConᴬ D k M)) (cong (renTy vs) (era-atCon D k M))))

methsTyFromᴬ : ADesc → ATy (Γ ∙) → ℕ → ADesc → ATy Γ
methsTyFromᴬ D M j dnil    = Unit
methsTyFromᴬ D M j (C ◃ E) = Σ' (methTyᴬ D j C M) (renTyᴬ vs (methsTyFromᴬ D M (suc j) E))

era-methsTyFrom : (D : ADesc) (M : ATy (Γ ∙)) (j : ℕ) (E : ADesc) →
                  ⌈ methsTyFromᴬ D M j E ⌉ᵀ ≡ methsTyFrom ⌈ D ⌉ᴰ ⌈ M ⌉ᵀ j ⌈ E ⌉ᴰ
era-methsTyFrom D M j dnil    = refl
era-methsTyFrom D M j (C ◃ E) =
  cong₂ Σ' (era-methTy D j C M)
           (trans (era-renTy vs (methsTyFromᴬ D M (suc j) E))
                  (cong (renTy vs) (era-methsTyFrom D M (suc j) E)))

methsTyᴬ : ADesc → ATy (Γ ∙) → ADesc → ATy Γ
methsTyᴬ D M E = methsTyFromᴬ D M zero E

------------------------------------------------------------------------
-- 2. Indexed descriptions.
------------------------------------------------------------------------

ilookupDᴬ : AIDesc → ℕ → AICon (ε ∙)
ilookupDᴬ inil    _       = iι
ilookupDᴬ (C ◂ D) zero    = C
ilookupDᴬ (C ◂ D) (suc k) = ilookupDᴬ D k

era-ilookupD : (D : AIDesc) (k : ℕ) → ⌈ ilookupDᴬ D k ⌉ᴵᶜ ≡ ilookupD ⌈ D ⌉ᴵᴰ k
era-ilookupD inil    k       = refl
era-ilookupD (C ◂ D) zero    = refl
era-ilookupD (C ◂ D) (suc k) = era-ilookupD D k

ipayTyᴬ : AIDesc → ATy ε → Subᴬ Δ Γ → AICon Δ → ATy Γ
ipayTyᴬ D I σ iι       = Unit
ipayTyᴬ D I σ (iρ j C) = Σ' (IMu D I (subTmᴬ σ j)) (ipayTyᴬ D I (extSᴬ σ) C)
ipayTyᴬ D I σ (iκ κ C) = Σ' (El (subTmᴬ σ κ))      (ipayTyᴬ D I (extSᴬ σ) C)

era-ipayTy : (D : AIDesc) (I : ATy ε) (σ : Subᴬ Δ Γ) (τ : Sub Δ Γ) → (∀ x → ⌈ σ x ⌉ ≡ τ x) →
             (C : AICon Δ) → ⌈ ipayTyᴬ D I σ C ⌉ᵀ ≡ ipayTy ⌈ D ⌉ᴵᴰ ⌈ I ⌉ᵀ τ ⌈ C ⌉ᴵᶜ
era-ipayTy D I σ τ h iι       = refl
era-ipayTy D I σ τ h (iρ j C) =
  cong₂ Σ' (cong (IMu ⌈ D ⌉ᴵᴰ ⌈ I ⌉ᵀ) (era-subTm σ τ h j))
           (era-ipayTy D I (extSᴬ σ) (extS τ) (era-ext h) C)
era-ipayTy D I σ τ h (iκ κ C) =
  cong₂ Σ' (cong El (era-subTm σ τ h κ))
           (era-ipayTy D I (extSᴬ σ) (extS τ) (era-ext h) C)

iinstᴬ : ATm Γ → ATm Γ → ATy ((Γ ∙) ∙) → ATy Γ
iinstᴬ j t M = subTyᴬ (singleᴬ t) (subTyᴬ (extSᴬ (singleᴬ j)) M)

era-iinst : (j t : ATm Γ) (M : ATy ((Γ ∙) ∙)) →
            ⌈ iinstᴬ j t M ⌉ᵀ ≡ iinst ⌈ j ⌉ ⌈ t ⌉ ⌈ M ⌉ᵀ
era-iinst j t M =
  trans (era-subTy (singleᴬ t) (single ⌈ t ⌉) (era-single t) (subTyᴬ (extSᴬ (singleᴬ j)) M))
        (cong (subTy (single ⌈ t ⌉))
              (era-subTy (extSᴬ (singleᴬ j)) (extS (single ⌈ j ⌉)) (era-ext (era-single j)) M))

iihTyᴬ : AIDesc → ATy ε → Subᴬ Δ Γ → AICon Δ → ATm Γ → ATy ((Γ ∙) ∙) → ATy Γ
iihTyᴬ D I σ iι       q M = Unit
iihTyᴬ D I σ (iρ j C) q M =
  Σ' (iinstᴬ (subTmᴬ σ j) (fst q) M) (renTyᴬ vs (iihTyᴬ D I (iextᴬ σ (fst q)) C (snd q) M))
iihTyᴬ D I σ (iκ κ C) q M = iihTyᴬ D I (iextᴬ σ (fst q)) C (snd q) M

era-iihTy : (D : AIDesc) (I : ATy ε) (σ : Subᴬ Δ Γ) (τ : Sub Δ Γ) → (∀ x → ⌈ σ x ⌉ ≡ τ x) →
            (C : AICon Δ) (q : ATm Γ) (M : ATy ((Γ ∙) ∙)) →
            ⌈ iihTyᴬ D I σ C q M ⌉ᵀ ≡ iihTy ⌈ D ⌉ᴵᴰ ⌈ I ⌉ᵀ τ ⌈ C ⌉ᴵᶜ ⌈ q ⌉ ⌈ M ⌉ᵀ
era-iihTy D I σ τ h iι       q M = refl
era-iihTy D I σ τ h (iρ j C) q M =
  cong₂ Σ' (trans (era-iinst (subTmᴬ σ j) (fst q) M)
                  (cong (λ z → iinst z (fst ⌈ q ⌉) ⌈ M ⌉ᵀ) (era-subTm σ τ h j)))
           (trans (era-renTy vs (iihTyᴬ D I (iextᴬ σ (fst q)) C (snd q) M))
                  (cong (renTy vs) (era-iihTy D I (iextᴬ σ (fst q)) (iext τ (fst ⌈ q ⌉))
                                               (era-iext h (fst q)) C (snd q) M)))
era-iihTy D I σ τ h (iκ κ C) q M =
  era-iihTy D I (iextᴬ σ (fst q)) (iext τ (fst ⌈ q ⌉)) (era-iext h (fst q)) C (snd q) M

-- ★ annotation CREATED: the constructed `icon` carries description, index
--   type, and its index — the WEAKENED ambient index.
iconSᴬ : AIDesc → ATy ε → ℕ → ATm Γ → Subᴬ ((Γ ∙) ∙) (Γ ∙)
iconSᴬ D I k i vz          = icon D I (renTmᴬ vs i) k (var vz)
iconSᴬ D I k i (vs vz)     = renTmᴬ vs i
iconSᴬ D I k i (vs (vs x)) = var (vs x)

era-iconS : (D : AIDesc) (I : ATy ε) (k : ℕ) (i : ATm Γ) →
            ∀ x → ⌈ iconSᴬ D I k i x ⌉ ≡ iconS k ⌈ i ⌉ x
era-iconS D I k i vz          = refl
era-iconS D I k i (vs vz)     = era-renTm vs i
era-iconS D I k i (vs (vs x)) = refl

iatConᴬ : AIDesc → ATy ε → ℕ → ATm Γ → ATy ((Γ ∙) ∙) → ATy (Γ ∙)
iatConᴬ D I k i M = subTyᴬ (iconSᴬ D I k i) M

era-iatCon : (D : AIDesc) (I : ATy ε) (k : ℕ) (i : ATm Γ) (M : ATy ((Γ ∙) ∙)) →
             ⌈ iatConᴬ D I k i M ⌉ᵀ ≡ iatCon k ⌈ i ⌉ ⌈ M ⌉ᵀ
era-iatCon D I k i M = era-subTy (iconSᴬ D I k i) (iconS k ⌈ i ⌉) (era-iconS D I k i) M

imethTyᴬ : AIDesc → ATy ε → ℕ → AICon (ε ∙) → ATy ((Γ ∙) ∙) → ATy Γ
imethTyᴬ D I k C M =
  Π (εwkTyᴬ I)
    (Π (ipayTyᴬ D I (isingleᴬ (var vz)) C)
       (Π (iihTyᴬ D I (isingleᴬ (var (vs vz))) C (var vz)
                  (renTyᴬ (extR (extR vs)) (renTyᴬ (extR (extR vs)) M)))
          (renTyᴬ vs (iatConᴬ D I k (var vz) (renTyᴬ (extR (extR vs)) M)))))

era-imethTy : (D : AIDesc) (I : ATy ε) (k : ℕ) (C : AICon (ε ∙)) (M : ATy ((Γ ∙) ∙)) →
              ⌈ imethTyᴬ D I k C M ⌉ᵀ ≡ imethTy ⌈ D ⌉ᴵᴰ ⌈ I ⌉ᵀ k ⌈ C ⌉ᴵᶜ ⌈ M ⌉ᵀ
era-imethTy D I k C M =
  cong₂ Π (era-εwkTy I)
    (cong₂ Π (era-ipayTy D I (isingleᴬ (var vz)) (isingle (var vz)) (era-isingle (var vz)) C)
      (cong₂ Π
        (trans (era-iihTy D I (isingleᴬ (var (vs vz))) (isingle (var (vs vz)))
                          (era-isingle (var (vs vz))) C (var vz)
                          (renTyᴬ (extR (extR vs)) (renTyᴬ (extR (extR vs)) M)))
               (cong (iihTy ⌈ D ⌉ᴵᴰ ⌈ I ⌉ᵀ (isingle (var (vs vz))) ⌈ C ⌉ᴵᶜ (var vz))
                     (trans (era-renTy (extR (extR vs)) (renTyᴬ (extR (extR vs)) M))
                            (cong (renTy (extR (extR vs))) (era-renTy (extR (extR vs)) M)))))
        (trans (era-renTy vs (iatConᴬ D I k (var vz) (renTyᴬ (extR (extR vs)) M)))
               (cong (renTy vs)
                     (trans (era-iatCon D I k (var vz) (renTyᴬ (extR (extR vs)) M))
                            (cong (iatCon k (var vz)) (era-renTy (extR (extR vs)) M)))))))

imethsTyFromᴬ : AIDesc → ATy ε → ATy ((Γ ∙) ∙) → ℕ → AIDesc → ATy Γ
imethsTyFromᴬ D I M j inil    = Unit
imethsTyFromᴬ D I M j (C ◂ E) =
  Σ' (imethTyᴬ D I j C M) (renTyᴬ vs (imethsTyFromᴬ D I M (suc j) E))

era-imethsTyFrom : (D : AIDesc) (I : ATy ε) (M : ATy ((Γ ∙) ∙)) (j : ℕ) (E : AIDesc) →
                   ⌈ imethsTyFromᴬ D I M j E ⌉ᵀ ≡ imethsTyFrom ⌈ D ⌉ᴵᴰ ⌈ I ⌉ᵀ ⌈ M ⌉ᵀ j ⌈ E ⌉ᴵᴰ
era-imethsTyFrom D I M j inil    = refl
era-imethsTyFrom D I M j (C ◂ E) =
  cong₂ Σ' (era-imethTy D I j C M)
           (trans (era-renTy vs (imethsTyFromᴬ D I M (suc j) E))
                  (cong (renTy vs) (era-imethsTyFrom D I M (suc j) E)))

imethsTyᴬ : AIDesc → ATy ε → ATy ((Γ ∙) ∙) → AIDesc → ATy Γ
imethsTyᴬ D I M E = imethsTyFromᴬ D I M zero E
