------------------------------------------------------------------------
-- OCP-0009 · dHoTT — the PREMISE TYPES of the levitated rules are
--                     well-formed, and `pairS`/`fsucS` are typed.
--
-- The rules STATE their premise types (`⊢ielim`/`⊢dih`'s `e ∷ MethTy I D M`,
-- `⊢psplit`'s branch at `subTy pairS P`, `⊢fcase`'s at `subTy fsucS P`) and
-- the kernel never needed them well-formed: its metatheory takes a
-- derivation AGAINST them as given.  A CHECKER, or an ELABORATOR, must
-- show them well-formed before checking against them — `Algorithm/CheckA`
-- and `Lib/Sugar` are the two customers.
--
-- ⚠ `subTy-var` is imported from `Fundamental/Syntactic` (where it was
--   born); it is pure σ-calculus and belongs in `Spec` — consolidation item.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Premises where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub
  using ( Sub⊢; sub-lemma; sub-ty; Ren⊢; Ren⊢-ext; ren-ty; ∋-cast; ⊢-cast; ⊢wk; wk-ren
        ; wk2-sub-tm; wk2M-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var; subTy-var )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Metatheory.RedCong
  using ( _⟶ᵀ*_; ⟶ᵀ*-trans; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-El; ⟶ᵀ*-DIhᶜ; ⟶*-dpayᶜ; ⟶*-ren )
open import DirectedHoTT.Spec.Variance using ( ren-as-sub )

private
  w3 : {Δ : Cx} → Ren Δ (((Δ ∙) ∙) ∙)
  w3 x = vs (vs (vs x))

  w2⊢ : {Δ : Ctx} {B : RTy ⌊ Δ ⌋} {B' : RTy (⌊ Δ ⌋ ∙)} → Ren⊢ Δ ((Δ ▹ B) ▹ B') (λ x → vs (vs x))
  w2⊢ {A = A} v = ∋-cast (renTy-renTy A) (there (there v))

-- the motive, renamed under its own two binders
mot-ren : {Δ Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {I D : RTm ⌊ Δ ⌋} {M : RTy ((⌊ Δ ⌋ ∙) ∙)} →
          Ren⊢ Δ Θ ρ → motCtx Δ I D ⊢ty M →
          motCtx Θ (renTm ρ I) (renTm ρ D) ⊢ty renTy (extR (extR ρ)) M
mot-ren {Θ = Θ} {ρ = ρ} {I} {D} {M} h dM =
  subst (λ A → ((Θ ▹ El (renTm ρ I)) ▹ A) ⊢ty renTy (extR (extR ρ)) M)
        (cong₂ (λ a b → IMu a b (var vz)) (wk-ren ρ I) (wk-ren ρ D))
        (ren-ty dM (Ren⊢-ext (Ren⊢-ext h)))

------------------------------------------------------------------------
-- ★ THE METHOD TYPE, general form.  `MethTy I D M` (the kernel's), the
--   per-constructor and the tag-generic method types of `Lib/Sugar` are
--   ONE shape: a telescope `C` for the payload and a scrutinee `s` (in
--   the context of index, payload and hypotheses) for the conclusion.
------------------------------------------------------------------------

methSg : {Δ : Cx} → RTm (((Δ ∙) ∙) ∙) → Sub ((Δ ∙) ∙) (((Δ ∙) ∙) ∙)
methSg s vz          = s
methSg s (vs vz)     = var (vs (vs vz))
methSg s (vs (vs x)) = var (vs (vs (vs x)))

MethG : {Δ : Cx} → RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTm Δ → RTm (((Δ ∙) ∙) ∙) → RTy Δ
MethG I D M C s =
  Π (El I)
    (Π (El (dpay (renTm vs I) (renTm vs D) (renTm vs C) (var vz)))
       (Π (DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs (renTm vs C)) (var vz))
          (subTy (methSg s) M)))

-- the kernel's method type is the instance at `C = D`, `s = con p`
MethTy-MethG : {Δ : Cx} (I D : RTm Δ) (M : RTy ((Δ ∙) ∙)) →
               MethTy I D M ≡ MethG I D M D (con (var (vs vz)))
MethTy-MethG I D M =
  cong (λ X → Π (El I) (Π (El (dpay (renTm vs I) (renTm vs D) (renTm vs D) (var vz)))
                         (Π (DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs (renTm vs D)) (var vz)) X)))
       (subTy-cong pt M)
  where
    pt : ∀ x → methS x ≡ methSg (con (var (vs vz))) x
    pt vz          = refl
    pt (vs vz)     = refl
    pt (vs (vs x)) = refl

private
  -- `methSg s` on a twice-weakened term: the third weakening.
  methSg-wk : {Δ : Cx} (s : RTm (((Δ ∙) ∙) ∙)) (t : RTm Δ) →
              subTm (methSg s) (renTm vs (renTm vs t)) ≡ renTm vs (renTm vs (renTm vs t))
  methSg-wk s t = trans (subTm-renTm (renTm vs t))
                    (trans (subTm-renTm t)
                      (trans (subTm-var w3 t)
                             (sym (trans (renTm-renTm (renTm vs t)) (renTm-renTm t)))))

  methSg-wkᵀ : {Δ : Cx} (s : RTm (((Δ ∙) ∙) ∙)) (A : RTy Δ) →
               subTy (methSg s) (renTy vs (renTy vs A)) ≡ renTy vs (renTy vs (renTy vs A))
  methSg-wkᵀ s A = trans (subTy-renTy (renTy vs A))
                     (trans (subTy-renTy A)
                       (trans (subTy-var w3 A)
                              (sym (trans (renTy-renTy (renTy vs A)) (renTy-renTy A)))))

-- substitution commutes with the general method type
methSg-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (s : RTm (((Δ ∙) ∙) ∙)) (M : RTy ((Δ ∙) ∙)) →
             subTy (extS (extS (extS σ))) (subTy (methSg s) M)
             ≡ subTy (methSg (subTm (extS (extS (extS σ))) s)) (subTy (extS (extS σ)) M)
methSg-sub σ s M = trans (subTy-subTy M) (trans (subTy-cong ptw M) (sym (subTy-subTy M)))
  where
  ptw : ∀ x → (extS (extS (extS σ)) ∘ₛ methSg s) x
            ≡ (methSg (subTm (extS (extS (extS σ))) s) ∘ₛ extS (extS σ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs x)) =
    trans (trans (cong (renTm vs) (renTm-renTm (σ x))) (renTm-renTm (σ x)))
          (trans (ren-as-sub (λ y → vs (vs (vs y))) (σ x))
                 (sym (trans (subTm-renTm (renTm vs (σ x))) (subTm-renTm (σ x)))))

MethG-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (I D : RTm Δ) (M : RTy ((Δ ∙) ∙)) (C : RTm Δ)
            (s : RTm (((Δ ∙) ∙) ∙)) →
            subTy σ (MethG I D M C s)
            ≡ MethG (subTm σ I) (subTm σ D) (subTy (extS (extS σ)) M) (subTm σ C)
                    (subTm (extS (extS (extS σ))) s)
MethG-sub σ I D M C s =
  cong₂ (λ P Q → Π (El (subTm σ I)) (Π P Q))
    (cong₃ (λ a b c → El (dpay a b c (var vz))) (wk-sub σ I) (wk-sub σ D) (wk-sub σ C))
    (cong₄ (λ d m c t → Π (DIh d m c (var vz)) t)
           (wk2-sub-tm σ D) (wk2M-sub σ M) (wk2-sub-tm σ C) (methSg-sub σ s M))

-- ★ a method type computes with its payload telescope
MethG-monoᶜ : {Δ : Cx} {I D C C' : RTm Δ} {M : RTy ((Δ ∙) ∙)} {s : RTm (((Δ ∙) ∙) ∙)} →
              C ⟶* C' → MethG I D M C s ⟶ᵀ* MethG I D M C' s
MethG-monoᶜ r =
  ⟶ᵀ*-trans (⟶ᵀ*-Πʳ (⟶ᵀ*-Πˡ (⟶ᵀ*-El (⟶*-dpayᶜ (⟶*-ren vs r)))))
            (⟶ᵀ*-Πʳ (⟶ᵀ*-Πʳ (⟶ᵀ*-Πˡ (⟶ᵀ*-DIhᶜ (⟶*-ren vs (⟶*-ren vs r))))))

-- the context a method's CONCLUSION lives in: index, payload of `C`,
--   hypotheses
MethCtx : (Δ : Ctx) → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTy ((⌊ Δ ⌋ ∙) ∙) → RTm ⌊ Δ ⌋ → Ctx
MethCtx Δ I D M C =
  ((Δ ▹ El I) ▹ El (dpay (renTm vs I) (renTm vs D) (renTm vs C) (var vz)))
    ▹ DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs (renTm vs C)) (var vz)

-- ★ a method type is well-formed when its scrutinee lives in the family
--   at the method's index.
MethG-wf : {Δ : Ctx} {I D C : RTm ⌊ Δ ⌋} {M : RTy ((⌊ Δ ⌋ ∙) ∙)} {s : RTm (((⌊ Δ ⌋ ∙) ∙) ∙)} →
           Δ ⊢ I ∷ U → Δ ⊢ D ∷ Desc I → Δ ⊢ C ∷ Desc I → motCtx Δ I D ⊢ty M →
           MethCtx Δ I D M C ⊢ s ∷ IMu (renTm vs (renTm vs (renTm vs I)))
                                        (renTm vs (renTm vs (renTm vs D))) (var (vs (vs vz))) →
           Δ ⊢ty MethG I D M C s
MethG-wf {Δ} {I} {D} {C} {M} {s} dI dD dC dM ds =
  ty-Π (ty-El dI)
    (ty-Π (ty-El (⊢dpay dI₁ dD₁ dC₁ (⊢var here)))
      (ty-Π (ty-DIh dI₂ dD₂ dM₂ dC₂ (⊢var (there here)) (⊢var here))
            (sub-ty dM hm)))
  where
    dI₁ = ⊢wk {B = El I} dI
    dD₁ = ⊢wk {B = El I} dD
    dC₁ = ⊢wk {B = El I} dC
    P₁ = El (dpay (renTm vs I) (renTm vs D) (renTm vs C) (var vz))
    dI₂ = ⊢wk {B = P₁} dI₁
    dD₂ = ⊢wk {B = P₁} dD₁
    dC₂ = ⊢wk {B = P₁} dC₁
    Δ₂ = (Δ ▹ El I) ▹ P₁
    dM₂ : motCtx Δ₂ (renTm vs (renTm vs I)) (renTm vs (renTm vs D)) ⊢ty wk2M M
    dM₂ = subst (λ a → motCtx Δ₂ a (renTm vs (renTm vs D)) ⊢ty wk2M M) (sym (renTm-renTm I))
            (subst (λ b → motCtx Δ₂ (renTm (λ x → vs (vs x)) I) b ⊢ty wk2M M) (sym (renTm-renTm D))
              (mot-ren (w2⊢ {B = El I} {B' = P₁}) dM))
    hm : Sub⊢ (motCtx Δ I D) (MethCtx Δ I D M C) (methSg s)
    hm here =
      ⊢-cast (cong₂ (λ a b → IMu a b (var (vs (vs vz)))) (sym (methSg-wk s I)) (sym (methSg-wk s D))) ds
    hm (there here) = ⊢-cast (cong El (sym (methSg-wk s I))) (⊢var (there (there here)))
    hm (there (there {A = A₀} v)) = ⊢-cast (sym (methSg-wkᵀ s A₀)) (⊢var (there (there (there v))))

-- ★ the METHOD TYPE is well-formed — the premise type of `⊢ielim`/`⊢dih`.
MethTy-wf : {Δ : Ctx} {I D : RTm ⌊ Δ ⌋} {M : RTy ((⌊ Δ ⌋ ∙) ∙)} →
            Δ ⊢ I ∷ U → Δ ⊢ D ∷ Desc I → motCtx Δ I D ⊢ty M → Δ ⊢ty MethTy I D M
MethTy-wf {Δ} {I} {D} {M} dI dD dM =
  subst (λ X → Δ ⊢ty X) (sym (MethTy-MethG I D M))
    (MethG-wf dI dD dD dM
      (⊢con (⊢wk (⊢wk (⊢wk dI))) (⊢wk (⊢wk (⊢wk dD))) (⊢var (there (there here))) (⊢var (there here))))

-- `pairS` and `fsucS` are well-typed substitutions (the kernel never needed
--   these: `⊢psplit`/`⊢fcase` take their branch types as given).
pairS⊢ : {Δ : Ctx} {A : RTy ⌊ Δ ⌋} {B : RTy (⌊ Δ ⌋ ∙)} →
         (Δ ▹ A) ⊢ty B → Sub⊢ (Δ ▹ Σ' A B) ((Δ ▹ A) ▹ B) pairS
pairS⊢ {Δ} {A} {B} dB here =
  ⊢pair dB' (⊢-cast eqA (⊢var (there here))) (⊢-cast eqb (⊢var here))
  where
    w2 : Ren ⌊ Δ ⌋ ((⌊ Δ ⌋ ∙) ∙)
    w2 x = vs (vs x)
    X = subTy pairS (renTy vs A)
    eqX : X ≡ renTy w2 A
    eqX = trans (subTy-renTy A) (subTy-var w2 A)
    -- the fibre, re-based under the split's two binders
    hR : Ren⊢ (Δ ▹ A) (((Δ ▹ A) ▹ B) ▹ X) (extR w2)
    hR here = ∋-cast (trans (cong (renTy vs) eqX) (trans (renTy-renTy A) (sym (renTy-renTy A)))) here
    hR (there {A = A₀} v) =
      ∋-cast (trans (renTy-renTy (renTy vs A₀))
               (trans (renTy-renTy A₀) (sym (trans (renTy-renTy A₀) refl))))
             (there (there (there v)))
    eqB : subTy (extS pairS) (renTy (extR vs) B) ≡ renTy (extR w2) B
    eqB = trans (subTy-renTy B) (trans (subTy-cong pt B) (subTy-var (extR w2) B))
      where
        pt : ∀ x → (extS pairS ₛ∘ᵣ extR vs) x ≡ ⟨ extR w2 ⟩ᵣ x
        pt vz     = refl
        pt (vs x) = refl
    dB' = subst (λ T → (((Δ ▹ A) ▹ B) ▹ X) ⊢ty T) (sym eqB) (ren-ty dB hR)
    eqA : renTy vs (renTy vs A) ≡ X
    eqA = trans (renTy-renTy A) (sym eqX)
    eqb : renTy vs B ≡ subTy (single (var (vs vz))) (subTy (extS pairS) (renTy (extR vs) B))
    eqb = sym (trans (cong (subTy (single (var (vs vz)))) eqB)
                     (trans (subTy-renTy B) (trans (subTy-cong pt B) (subTy-var vs B))))
      where
        pt : ∀ x → (single (var (vs vz)) ₛ∘ᵣ extR w2) x ≡ ⟨ vs ⟩ᵣ x
        pt vz     = refl
        pt (vs x) = refl
pairS⊢ {A = A} dB (there {A = A₀} v) =
  ⊢-cast (trans (renTy-renTy A₀) (sym (trans (subTy-renTy A₀) (subTy-var (λ x → vs (vs x)) A₀))))
         (⊢var (there (there v)))

fsucS⊢ : {Δ : Ctx} {n : ℕ} → Sub⊢ (Δ ▹ Fin (suc n)) (Δ ▹ Fin n) fsucS
fsucS⊢ here = ⊢fsuc (⊢var here)
fsucS⊢ (there {A = A₀} v) =
  ⊢-cast (sym (trans (subTy-renTy A₀) (subTy-var vs A₀))) (⊢var (there v))

