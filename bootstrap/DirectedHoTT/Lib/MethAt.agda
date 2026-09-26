------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ THE METHOD AT AN INDEX TERM.
--
-- The kernel's method type binds the index: `MethTy I D M = Π (El I) R`.
-- Its body `R` is a method AT the index variable.  This module states
-- that body at an ARBITRARY index TERM `i`:
--
--   MethAt I D M i F s = Π (p : El (dpay I D F)).
--                        Π (h : DIh D M F p).  M[i, s]
--
-- (`F` the payload telescope, `s` the scrutinee over `p`/`h`), and builds
-- the one method at `i` from one method per constructor AT `i`
-- (`⊢methAt`).  The kernel's `MethTy` is the instance at `i = var vz`
-- (`MethTy-At`).
--
-- ★ WHY.  A family presented by fibres over a STRUCTURED index (a sorted
--   family, `Lib/Sorted`) has a fibre that computes only once the index
--   is split: its methods are typed at `pair (tag s) j`, not at a
--   variable — "pattern matching on the index".  A method at an index
--   variable is the special case, not the general one.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.MethAt where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-dpayᶜ; ⟶ᵀ*-El; red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ
        ; ⟶ᵀ*-trans; ⟶ᵀ*-DIhᶜ; ⟶*-ren; ⟶*-appˡ; ⟶*-appʳ )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; wk-cancel-tm; ren-ty; sub-ty; Ren⊢-ext; wk-ren; wk2-sub-tm
        ; ren-lemma; Ren⊢; ∋-cast; conv-ctxᵀ; sub-lemma; Sub⊢ )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren; ⊢wkD )
open import DirectedHoTT.Metatheory.Validity using ( wk-app-vz )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Nth; nth-z; nth-s; tag; tag-ren; sel; selM; selF-β; conₗ; ⊢con-fib; ⊢pay-σ
        ; ⊢tag; nth-lt; Lt; AllQ; []q; _∷q_; castQ; ⊢selG; fsucsS; fsucsS-zero; fsucsS-suc; fsucsS-head
        ; wk-single-tag; ≅ᵀ-ren; ⊢wkF; wkC; subC; selF-sub )

private
  variable
    Γ Δ : Cx
    c k : ℕ

------------------------------------------------------------------------
-- 1. THE TYPE.
------------------------------------------------------------------------

-- the motive under the method's two binders (payload, hypotheses), at
--   index `i` and scrutinee `s`
atS : RTm Γ → RTm ((Γ ∙) ∙) → Sub ((Γ ∙) ∙) ((Γ ∙) ∙)
atS i s vz          = s
atS i s (vs vz)     = renTm vs (renTm vs i)
atS i s (vs (vs x)) = var (vs (vs x))

-- the motive past one binder (its own two kept)
wk1M : RTy ((Γ ∙) ∙) → RTy (((Γ ∙) ∙) ∙)
wk1M M = renTy (extR (extR vs)) M

MethAt : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTm Γ → RTm Γ → RTm ((Γ ∙) ∙) → RTy Γ
MethAt I D M i F s =
  Π (El (dpay I D F))
    (Π (DIh (renTm vs D) (wk1M M) (renTm vs F) (var vz))
       (subTy (atS i s) M))

-- the context a method's conclusion lives in
AtCtx : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTm ⌊ Γ ⌋ → RTy ((⌊ Γ ⌋ ∙) ∙) → RTm ⌊ Γ ⌋ → Ctx
AtCtx Γ I D M F = (Γ ▹ El (dpay I D F)) ▹ DIh (renTm vs D) (wk1M M) (renTm vs F) (var vz)

------------------------------------------------------------------------
-- 2. THE ALGEBRA.
------------------------------------------------------------------------

private
  w2 : Ren Γ ((Γ ∙) ∙)
  w2 x = vs (vs x)

  -- `atS` fixes everything twice weakened
  atS-wk2 : (i : RTm Γ) (s : RTm ((Γ ∙) ∙)) (t : RTm Γ) →
            subTm (atS i s) (renTm vs (renTm vs t)) ≡ renTm vs (renTm vs t)
  atS-wk2 i s t = trans (subTm-renTm (renTm vs t))
                    (trans (subTm-renTm t)
                      (trans (subTm-var w2 t) (sym (renTm-renTm t))))

  atS-wk2ᵀ : (i : RTm Γ) (s : RTm ((Γ ∙) ∙)) (A : RTy Γ) →
             subTy (atS i s) (renTy vs (renTy vs A)) ≡ renTy vs (renTy vs A)
  atS-wk2ᵀ i s A = trans (subTy-renTy (renTy vs A))
                     (trans (subTy-renTy A)
                       (trans (subTy-var w2 A) (sym (renTy-renTy A))))

wk1M-sub : {Θ : Cx} (σ : Sub Γ Θ) (M : RTy ((Γ ∙) ∙)) →
           subTy (extS (extS (extS σ))) (wk1M M) ≡ wk1M (subTy (extS (extS σ)) M)
wk1M-sub σ M = trans (subTy-renTy M) (trans (subTy-cong pt M) (sym (renTy-subTy M)))
  where
    pt : ∀ x → (extS (extS (extS σ)) ₛ∘ᵣ extR (extR vs)) x ≡ (extR (extR vs) ᵣ∘ₛ extS (extS σ)) x
    pt vz          = refl
    pt (vs vz)     = refl
    pt (vs (vs x)) = trans (trans (cong (renTm vs) (renTm-renTm (σ x))) (renTm-renTm (σ x)))
                           (sym (trans (renTm-renTm (renTm vs (σ x))) (renTm-renTm (σ x))))

atS-sub : {Θ : Cx} (σ : Sub Γ Θ) (i : RTm Γ) (s : RTm ((Γ ∙) ∙)) (M : RTy ((Γ ∙) ∙)) →
          subTy (extS (extS σ)) (subTy (atS i s) M)
          ≡ subTy (atS (subTm σ i) (subTm (extS (extS σ)) s)) (subTy (extS (extS σ)) M)
atS-sub σ i s M = trans (subTy-subTy M) (trans (subTy-cong pt M) (sym (subTy-subTy M)))
  where
    pt : ∀ x → (extS (extS σ) ∘ₛ atS i s) x ≡ (atS (subTm σ i) (subTm (extS (extS σ)) s) ∘ₛ extS (extS σ)) x
    pt vz          = refl
    pt (vs vz)     = wk2-sub-tm σ i
    pt (vs (vs x)) = sym (atS-wk2 (subTm σ i) (subTm (extS (extS σ)) s) (σ x))

-- ★ substitution commutes with the method type
MethAt-sub : {Θ : Cx} (σ : Sub Γ Θ) (I D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (i F : RTm Γ) (s : RTm ((Γ ∙) ∙)) →
             subTy σ (MethAt I D M i F s)
             ≡ MethAt (subTm σ I) (subTm σ D) (subTy (extS (extS σ)) M) (subTm σ i) (subTm σ F)
                      (subTm (extS (extS σ)) s)
MethAt-sub σ I D M i F s =
  cong (λ Q → Π (El (dpay (subTm σ I) (subTm σ D) (subTm σ F))) Q)
    (cong₂ (λ P R → Π P R)
      (cong₃ (λ d m c → DIh d m c (var vz)) (wk-sub σ D) (wk1M-sub σ M) (wk-sub σ F))
      (atS-sub σ i s M))

-- ★ a method type computes with its payload telescope
MethAt-monoᶜ : {I D i F F' : RTm Γ} {M : RTy ((Γ ∙) ∙)} {s : RTm ((Γ ∙) ∙)} →
               F ⟶* F' → MethAt I D M i F s ⟶ᵀ* MethAt I D M i F' s
MethAt-monoᶜ r =
  ⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟶ᵀ*-El (⟶*-dpayᶜ r)))
            (⟶ᵀ*-Πʳ (⟶ᵀ*-Πˡ (⟶ᵀ*-DIhᶜ (⟶*-ren vs r))))

-- ★ the kernel's method type IS the method at the index VARIABLE, bound
MethTy-At : (I D : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
            MethTy I D M ≡ Π (El I) (MethAt (renTm vs I) (renTm vs D) (wk1M M) (var vz)
                                           (app (renTm vs D) (var vz)) (con (var (vs vz))))
MethTy-At I D M =
  cong (Π (El I))
    (cong (Π (El (dpay (renTm vs I) (renTm vs D) (app (renTm vs D) (var vz)))))
      (cong₂ (λ m X → Π (DIh (renTm vs (renTm vs D)) m (app (renTm vs (renTm vs D)) (var (vs vz))) (var vz)) X)
             (sym (trans (renTy-renTy M) (renTy-cong (λ { vz → refl ; (vs vz) → refl ; (vs (vs x)) → refl }) M)))
             (sym (trans (subTy-renTy M) (subTy-cong (λ { vz → refl ; (vs vz) → refl ; (vs (vs x)) → refl }) M)))))

------------------------------------------------------------------------
-- 3. WELL-FORMEDNESS: when its scrutinee lives in the family at `i`.
------------------------------------------------------------------------

MethAt-wf : {Γ : Ctx} {I D i F : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} →
            Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ F ∷ Desc I → motCtx Γ I D ⊢ty M → Γ ⊢ i ∷ El I →
            AtCtx Γ I D M F ⊢ s ∷ IMu (renTm vs (renTm vs I)) (renTm vs (renTm vs D)) (renTm vs (renTm vs i)) →
            Γ ⊢ty MethAt I D M i F s
MethAt-wf {Γ} {I} {D} {i} {F} {M} {s} dI dD dF dM di ds =
  ty-Π (ty-El (⊢dpay dI dD dF))
    (ty-Π (ty-DIh (⊢wk dI) (⊢wkD dD) (mot-ren there dM) (⊢wk dF) (⊢var here))
          (sub-ty dM hm))
  where
    hm : Sub⊢ (motCtx Γ I D) (AtCtx Γ I D M F) (atS i s)
    hm here =
      ⊢-cast (cong₂ (λ a b → IMu a b (renTm vs (renTm vs i))) (sym (atS-wk2 i s I)) (sym (atS-wk2 i s D))) ds
    hm (there here) = ⊢-cast (cong El (sym (atS-wk2 i s I))) (⊢wk (⊢wk di))
    hm (there (there {A = A₀} v)) = ⊢-cast (sym (atS-wk2ᵀ i s A₀)) (⊢var (there (there v)))

------------------------------------------------------------------------
-- 4. ★ PER-CONSTRUCTOR METHODS AT `i`, and the TAG-GENERIC one.
--
-- At `i` the fibre is `dσ (⌜Fin⌝ c) f` for a selector `f` (a function of
-- the tag); constructor `k`'s method sees `f (tag k)`'s payload and
-- concludes at `con (tag k , p)`.
------------------------------------------------------------------------

MethKAt : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTm Γ → RTm Γ → ℕ → RTy Γ
MethKAt I D M i C k = MethAt I D M i C (conₗ k (var (vs vz)))

-- over the tag: the selector at the tag, the scrutinee `con (tag , p)`
MethTAt : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTm Γ → RTm Γ → RTy (Γ ∙)
MethTAt I D M i f =
  MethAt (renTm vs I) (renTm vs D) (wk1M M) (renTm vs i) (app (renTm vs f) (var vz))
         (con (pair (var (vs (vs vz))) (var (vs vz))))

private
  cong₆ : {A B C D E F G : Set} (g : A → B → C → D → E → F → G)
          {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {f f' : F} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f' → g a b c d e f ≡ g a' b' c' d' e' f'
  cong₆ g refl refl refl refl refl refl = refl

  -- the motive under the tag's binder, weakened then instantiated: itself
  M-cancel : (a : RTm Γ) (M : RTy ((Γ ∙) ∙)) → subTy (extS (extS (single a))) (wk1M M) ≡ M
  M-cancel a M = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-id M))
    where
      pt : ∀ x → (extS (extS (single a)) ₛ∘ᵣ extR (extR vs)) x ≡ idₛ x
      pt vz          = refl
      pt (vs vz)     = refl
      pt (vs (vs x)) = refl

-- ★ the tag-generic method type at `tag k` IS constructor `k`'s
MethTAt-inst : (I D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (i f : RTm Γ) (k : ℕ) →
               subTy (single (tag k)) (MethTAt I D M i f) ≡ MethKAt I D M i (app f (tag k)) k
MethTAt-inst I D M i f k =
  trans (MethAt-sub (single (tag k)) (renTm vs I) (renTm vs D) (wk1M M) (renTm vs i)
                    (app (renTm vs f) (var vz)) (con (pair (var (vs (vs vz))) (var (vs vz)))))
        (cong₆ MethAt (wk-cancel-tm (tag k) I) (wk-cancel-tm (tag k) D) (M-cancel (tag k) M)
                      (wk-cancel-tm (tag k) i)
                      (cong₂ app (wk-cancel-tm (tag k) f) refl)
                      (cong (λ z → con (pair z (var (vs vz))))
                            (trans (cong (renTm vs) (tag-ren vs k)) (tag-ren vs k))))

MethKAt≅TAt : {I D i f C : RTm Γ} {M : RTy ((Γ ∙) ∙)} (k : ℕ) → app f (tag k) ⟶* C →
              MethKAt I D M i C k ≅ᵀ subTy (single (tag k)) (MethTAt I D M i f)
MethKAt≅TAt {I = I} {D} {i} {f} {C} {M} k r =
  subst (λ X → MethKAt I D M i C k ≅ᵀ X) (sym (MethTAt-inst I D M i f k))
        (csymᵀ (red→≅ᵀ (MethAt-monoᶜ r)))

private
  w3 : Ren Γ (((Γ ∙) ∙) ∙)
  w3 x = vs (vs (vs x))

  ren3 : (t : RTm Γ) → renTm vs (renTm vs (renTm vs t)) ≡ renTm w3 t
  ren3 t = trans (cong (renTm vs) (renTm-renTm t)) (renTm-renTm t)

  ren3ᵀ : (A : RTy Γ) → renTy vs (renTy vs (renTy vs A)) ≡ renTy w3 A
  ren3ᵀ A = trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A)

  -- a substitution after a renaming that lands on variables is a renaming
  sr-flat : {Θ Ξ Ω : Cx} (σ : Sub Θ Ξ) (ρ : Ren Ω Θ) (ρ' : Ren Ω Ξ) →
            (∀ x → σ (ρ x) ≡ var (ρ' x)) → (t : RTm Ω) → subTm σ (renTm ρ t) ≡ renTm ρ' t
  sr-flat σ ρ ρ' h t = trans (subTm-renTm t) (trans (subTm-cong h t) (subTm-var ρ' t))

-- the tag-generic method type is well-formed over the tag, when the
--   family's fibre at `i` is the selector's
MethTAt-wf : {Γ : Ctx} {I D i f : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} →
             Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → Γ ⊢ i ∷ El I →
             Γ ⊢ f ∷ Π (El (⌜Fin⌝ c)) (Desc (renTm vs I)) → app D i ⟶* dσ (⌜Fin⌝ c) f →
             (Γ ▹ Fin c) ⊢ty MethTAt I D M i f
MethTAt-wf {c = c} {Γ = Γ} {I} {D} {i} {f} {M} dI dD dM di df fib =
  MethAt-wf (⊢wk dI) (⊢wkD dD) dF (mot-ren there dM) (⊢wk di) dscr
  where
    dF : (Γ ▹ Fin c) ⊢ app (renTm vs f) (var vz) ∷ Desc (renTm vs I)
    dF = ⊢-cast (cong Desc (wk-cancel-tm (var vz) (renTm vs I)))
                (⊢app (⊢wkF df) (⊢conv (⊢var here) (csymᵀ (credᵀ El-⌜Fin⌝))))
    I₃ = renTm vs (renTm vs (renTm vs I))
    D₃ = renTm vs (renTm vs (renTm vs D))
    f₃ = renTm vs (renTm vs (renTm vs f))
    dI₃ = ⊢wk (⊢wk (⊢wk dI))
    dD₃ = ⊢wkD (⊢wkD (⊢wkD dD))
    red : app D₃ (renTm vs (renTm vs (renTm vs i))) ⟶* dσ (⌜Fin⌝ c) f₃
    red = ⟶*-ren vs (⟶*-ren vs (⟶*-ren vs fib))
    dscr = ⊢con-fib dI₃ dD₃ (⊢wk (⊢wk (⊢wk di))) red
             (⊢pay-σ dI₃ dD₃ (⊢wkF (⊢wkF (⊢wkF df)))
                     (⊢conv (⊢var (there (there here))) (csymᵀ (credᵀ El-⌜Fin⌝)))
                     (⊢var (there here)))

-- ★ one method PER CONSTRUCTOR at `i`, with the selection's lookup
infixr 5 _∷ₐ_
data PerKAt (Γ : Ctx) (I D : RTm ⌊ Γ ⌋) (M : RTy ((⌊ Γ ⌋ ∙) ∙)) (i f : RTm ⌊ Γ ⌋) :
            ℕ → {n : ℕ} → Cons ⌊ Γ ⌋ n → Set where
  []ₐ  : {k : ℕ} → PerKAt Γ I D M i f k []
  _∷ₐ_ : {k n : ℕ} {C m : RTm ⌊ Γ ⌋} {ms : Cons ⌊ Γ ⌋ n} →
         (app f (tag k) ⟶* C) × (Γ ⊢ m ∷ MethKAt I D M i C k) →
         PerKAt Γ I D M i f (suc k) ms → PerKAt Γ I D M i f k (m ∷ ms)

mkAllQAt : {Γ : Ctx} {I D i f : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {B : RTy ⌊ Γ ⌋} {k n : ℕ}
           {ms : Cons ⌊ Γ ⌋ n} → PerKAt Γ I D M i f k ms →
           AllQ (Γ ▹ B) (subTy (fsucsS k) (renTy (extR vs) (MethTAt I D M i f))) (wkC ms)
mkAllQAt []ₐ = []q
mkAllQAt {I = I} {D} {i} {f} {M} {k = k} ((r , dm) ∷ₐ ps) =
  ⊢-cast (sym (trans (fsucsS-head k (renTy (extR vs) (MethTAt I D M i f)))
                     (wk-single-tag k (MethTAt I D M i f))))
         (⊢conv (⊢wk dm) (≅ᵀ-ren vs (MethKAt≅TAt k r)))
  ∷q castQ (sym (fsucsS-suc k (renTy (extR vs) (MethTAt I D M i f)))) (mkAllQAt ps)

-- ★ the method SELECTOR at `i`
⊢selMAt : {Γ : Ctx} {I D i f : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {ms : Cons ⌊ Γ ⌋ c} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → Γ ⊢ i ∷ El I →
          Γ ⊢ f ∷ Π (El (⌜Fin⌝ c)) (Desc (renTm vs I)) → app D i ⟶* dσ (⌜Fin⌝ c) f →
          PerKAt Γ I D M i f zero ms →
          Γ ⊢ selM ms ∷ Π (El (⌜Fin⌝ c)) (MethTAt I D M i f)
⊢selMAt {I = I} {D} {i} {f} {M} dI dD dM di df fib ps =
  ⊢lam (ty-El ⊢⌜Fin⌝)
       (⊢-cast (wk-app-vz MT)
               (⊢selG (ren-ty (MethTAt-wf dI dD dM di df fib) (Ren⊢-ext there))
                      (castQ (fsucsS-zero (renTy (extR vs) MT)) (mkAllQAt ps))
                      (⊢conv (⊢var here) (credᵀ El-⌜Fin⌝))))
  where
    MT = MethTAt I D M i f

------------------------------------------------------------------------
-- 5. ★★ THE ONE METHOD AT `i`, from one method per constructor at `i`.
--
--      methAt ms = λ q. psplit (λ t p'. selM ms t p') q
--
-- `psplit` is required: the kernel has no Σ-η (D071), so the payload must
-- be split before the selection can see its tag.
------------------------------------------------------------------------

methAt : Cons Γ c → RTm Γ
methAt ms = lam (psplit (app (app (renTm (λ x → vs (vs (vs x))) (selM ms)) (var (vs vz))) (var vz)) (var vz))

private
  Π-cod : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} → Γ ⊢ty Π A B → (Γ ▹ A) ⊢ty B
  Π-cod (ty-Π _ d) = d

  w4 : Ren Γ ((((Γ ∙) ∙) ∙) ∙)
  w4 x = vs (vs (vs (vs x)))

⊢methAt : {Γ : Ctx} {I D i f : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {ms : Cons ⌊ Γ ⌋ c} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → Γ ⊢ i ∷ El I →
          Γ ⊢ f ∷ Π (El (⌜Fin⌝ c)) (Desc (renTm vs I)) → app D i ⟶* dσ (⌜Fin⌝ c) f →
          PerKAt Γ I D M i f zero ms →
          Γ ⊢ methAt ms ∷ MethAt I D M i (dσ (⌜Fin⌝ c) f) (con (var (vs vz)))
⊢methAt {c = c} {Γ = Γ} {I = I} {D} {i} {f} {M} {ms} dI dD dM di df fib ps =
  ⊢lam dP₁ (⊢-cast eqP (⊢psplit dA dB dP dq db))
  where
    F = dσ (⌜Fin⌝ c) f
    dF : Γ ⊢ F ∷ Desc I
    dF = ⊢dσ dI ⊢⌜Fin⌝ df
    P₁ = El (dpay I D F)
    dP₁ = ty-El (⊢dpay dI dD dF)
    Γ₁ = Γ ▹ P₁
    s₀ : RTm ((⌊ Γ ⌋ ∙) ∙)
    s₀ = con (var (vs vz))
    T : RTy ⌊ Γ₁ ⌋
    T = Π (DIh (renTm vs D) (wk1M M) (renTm vs F) (var vz)) (subTy (atS i s₀) M)
    dscr = ⊢con-fib (⊢wk (⊢wk dI)) (⊢wkD (⊢wkD dD)) (⊢wk (⊢wk di)) (⟶*-ren vs (⟶*-ren vs fib))
                    (⊢var (there here))
    dT : Γ₁ ⊢ty T
    dT = Π-cod (MethAt-wf dI dD dF dM di dscr)
    I₁ = renTm vs I
    D₁ = renTm vs D
    f₁ = renTm vs f
    A = El (⌜Fin⌝ {⌊ Γ₁ ⌋} c)
    B = El (dpay (renTm vs I₁) (renTm vs D₁) (app (renTm vs f₁) (var vz)))
    cvq : renTy vs P₁ ≅ᵀ Σ' A B
    cvq = ctrnᵀ (credᵀ (ξ-El (dpay-σ I₁ D₁ (⌜Fin⌝ c) f₁))) (credᵀ (El-⌜Σ⌝ _ _))
    dq = ⊢conv (⊢var here) cvq
    dA = ty-El (⊢⌜Fin⌝ {n = c})
    dB : (Γ₁ ▹ A) ⊢ty B
    dB = ty-El (⊢dpay (⊢wk (⊢wk dI)) (⊢wkD (⊢wkD dD))
                      (⊢-cast (cong Desc (wk-cancel-tm (var vz) (renTm vs I₁)))
                              (⊢app (⊢wkF (⊢wkF df)) (⊢var here))))
    -- the motive: the method type's inner Π, the payload read as the Σ
    ρP : Ren ⌊ Γ₁ ⌋ (⌊ Γ₁ ⌋ ∙)
    ρP vz     = vz
    ρP (vs y) = vs (vs y)
    hρP : Ren⊢ Γ₁ (Γ₁ ▹ renTy vs P₁) ρP
    hρP here = ∋-cast (trans (renTy-renTy P₁) (sym (renTy-renTy P₁))) here
    hρP (there {A = A₀} v) = ∋-cast (trans (renTy-renTy A₀) (sym (renTy-renTy A₀))) (there (there v))
    dP : (Γ₁ ▹ Σ' A B) ⊢ty renTy ρP T
    dP = conv-ctxᵀ cvq (ren-ty dT hρP)
    eqP : subTy (single (var vz)) (renTy ρP T) ≡ T
    eqP = trans (subTy-renTy T) (trans (subTy-cong pt T) (subTy-id T))
      where
        pt : ∀ x → (single (var vz) ₛ∘ᵣ ρP) x ≡ idₛ x
        pt vz     = refl
        pt (vs y) = refl
    -- ── the branch: the selector at the tag, then the payload ──
    Γ₃ = (Γ₁ ▹ A) ▹ B
    t p' : RTm ⌊ Γ₃ ⌋
    t  = var (vs vz)
    p' = var vz
    MT = MethTAt I D M i f
    h3 : Ren⊢ Γ Γ₃ w3
    h3 {A = A₀} v = ∋-cast (ren3ᵀ A₀) (there (there (there v)))
    dSel : Γ₃ ⊢ renTm w3 (selM ms) ∷ Π (El (⌜Fin⌝ c)) (renTy (extR w3) MT)
    dSel = ren-lemma (⊢selMAt dI dD dM di df fib ps) h3
    I₃ = renTm w3 I
    D₃ = renTm w3 D
    i₃ = renTm w3 i
    f₃ = renTm w3 f
    M₃ = renTy (extR (extR w3)) M
    s₃ : RTm ((⌊ Γ₃ ⌋ ∙) ∙)
    s₃ = con (pair (var (vs (vs (vs vz)))) (var (vs vz)))
    τ = single t ₛ∘ᵣ extR w3
    wk-τ : (x : RTm ⌊ Γ ⌋) → subTm τ (renTm vs x) ≡ renTm w3 x
    wk-τ x = trans (subTm-renTm x) (subTm-var w3 x)
    E1 : subTy (single t) (renTy (extR w3) MT) ≡ MethAt I₃ D₃ M₃ i₃ (app f₃ t) s₃
    E1 = trans (subTy-renTy MT)
           (trans (MethAt-sub τ (renTm vs I) (renTm vs D) (wk1M M) (renTm vs i)
                              (app (renTm vs f) (var vz)) (con (pair (var (vs (vs vz))) (var (vs vz)))))
                  (cong₆ MethAt (wk-τ I) (wk-τ D) eM (wk-τ i) (cong₂ app (wk-τ f) refl) refl))
      where
        eM : subTy (extS (extS τ)) (wk1M M) ≡ M₃
        eM = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-var (extR (extR w3)) M))
          where
            pt : ∀ x → (extS (extS τ) ₛ∘ᵣ extR (extR vs)) x ≡ ⟨ extR (extR w3) ⟩ᵣ x
            pt vz          = refl
            pt (vs vz)     = refl
            pt (vs (vs x)) = refl
    d1 = ⊢-cast E1 (⊢app dSel (⊢var (there here)))
    dp' : Γ₃ ⊢ p' ∷ El (dpay I₃ D₃ (app f₃ t))
    dp' = ⊢-cast (cong₃ (λ a b g → El (dpay a b (app g t))) (ren3 I) (ren3 D) (ren3 f)) (⊢var here)
    d2 = ⊢app d1 dp'
    -- ── the two domains, and the one codomain ──
    Gc = subTy (extS pairS) (renTy (extR ρP) (subTy (atS i s₀) M))
    domL : subTy (single p') (DIh (renTm vs D₃) (wk1M M₃) (renTm vs (app f₃ t)) (var vz))
           ≡ DIh D₃ M₃ (app f₃ t) p'
    domL = cong₃ (λ d m x → DIh d m x p') (wk-cancel-tm p' D₃) (M-cancel p' M₃) (wk-cancel-tm p' (app f₃ t))
    fl : (x : RTm ⌊ Γ ⌋) → subTm pairS (renTm ρP (renTm vs x)) ≡ renTm w3 x
    fl x = trans (cong (subTm pairS) (renTm-renTm x)) (sr-flat pairS _ w3 (λ y → refl) x)
    domR : subTy pairS (renTy ρP (DIh (renTm vs D) (wk1M M) (renTm vs F) (var vz)))
           ≡ DIh D₃ M₃ (renTm w3 F) (pair t p')
    domR = cong₃ (λ d m x → DIh d m x (pair t p')) (fl D) eM (fl F)
      where
        eM : subTy (extS (extS pairS)) (renTy (extR (extR ρP)) (wk1M M)) ≡ M₃
        eM = trans (cong (subTy (extS (extS pairS))) (renTy-renTy M))
               (trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-var (extR (extR w3)) M)))
          where
            pt : ∀ x → (extS (extS pairS) ₛ∘ᵣ (extR (extR ρP) ∘ᵣ extR (extR vs))) x ≡ ⟨ extR (extR w3) ⟩ᵣ x
            pt vz          = refl
            pt (vs vz)     = refl
            pt (vs (vs x)) = refl
    cod : subTy (extS (single p')) (subTy (atS i₃ s₃) M₃) ≡ Gc
    cod = trans (cong (subTy (extS (single p'))) (subTy-renTy M))
            (trans (subTy-subTy M)
              (trans (subTy-cong pt M)
                (sym (trans (cong (subTy (extS pairS)) (renTy-subTy M)) (subTy-subTy M)))))
      where
        idxL : subTm (extS (single p')) (renTm vs (renTm vs i₃)) ≡ renTm w4 i
        idxL = trans (cong (subTm (extS (single p')))
                           (trans (cong (renTm vs) (renTm-renTm i)) (renTm-renTm i)))
                     (sr-flat (extS (single p')) _ w4 (λ y → refl) i)
        idxR : subTm (extS pairS) (renTm (extR ρP) (renTm vs (renTm vs i))) ≡ renTm w4 i
        idxR = trans (cong (λ z → subTm (extS pairS) (renTm (extR ρP) z)) (renTm-renTm i))
                 (trans (cong (subTm (extS pairS)) (renTm-renTm i))
                        (sr-flat (extS pairS) _ w4 (λ y → refl) i))
        pt : ∀ x → (extS (single p') ∘ₛ (atS i₃ s₃ ₛ∘ᵣ extR (extR w3))) x
                   ≡ (extS pairS ∘ₛ (extR ρP ᵣ∘ₛ atS i s₀)) x
        pt vz          = refl
        pt (vs vz)     = trans idxL (sym idxR)
        pt (vs (vs x)) = refl
    -- the hypotheses at the whole fibre compute to those at the selection
    red : DIh D₃ M₃ (renTm w3 F) (pair t p') ⟶ᵀ* DIh D₃ M₃ (app f₃ t) p'
    red = stepᵀ (DIh-σ D₃ M₃ (⌜Fin⌝ c) f₃ (pair t p'))
            (stepᵀ (ξ-DIhᶜ (ξ-appʳ (βfst t p'))) (stepᵀ (ξ-DIhᵖ (βsnd t p')) doneᵀ))
    Y = Π (DIh (renTm vs D₃) (wk1M M₃) (renTm vs (app f₃ t)) (var vz)) (subTy (atS i₃ s₃) M₃)
    cvfinal : subTy (single p') Y ≅ᵀ subTy pairS (renTy ρP T)
    cvfinal = subst (λ X → X ≅ᵀ subTy pairS (renTy ρP T)) (sym (cong₂ Π domL cod))
                (subst (λ X → Π (DIh D₃ M₃ (app f₃ t) p') Gc ≅ᵀ X) (sym (cong (λ X → Π X Gc) domR))
                  (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ red))))
    db : Γ₃ ⊢ app (app (renTm w3 (selM ms)) t) p' ∷ subTy pairS (renTy ρP T)
    db = ⊢conv d2 cvfinal

-- ★ …AND IT COMPUTES: at constructor `k`'s payload, the one method IS
--   constructor `k`'s — one β, the split, the tag selection.
methAt-β : {k : ℕ} {m p h : RTm Γ} {ms : Cons Γ c} → Nth ms k m →
           app (app (methAt ms) (pair (tag k) p)) h ⟶* app (app m p) h
methAt-β {Γ = Γ} {k = k} {m} {p} {h} {ms} nt =
  step (ξ-appˡ (β (psplit b (var vz)) q))
   (step (ξ-appˡ (psplit-β b₁ (tag k) p))
    (subst (λ z → app z h ⟶* app (app m p) h) (sym E)
           (⟶*-appˡ (⟶*-appˡ (selF-β nt)))))
  where
    q = pair (tag k) p
    b : RTm ((((Γ ∙) ∙) ∙))
    b = app (app (renTm w3 (selM ms)) (var (vs vz))) (var vz)
    b₁ = subTm (extS (extS (single q))) b
    L3 : (X : RTm Γ) → subTm (single2 (tag k) p) (subTm (extS (extS (single q))) (renTm w3 X)) ≡ X
    L3 X = trans (cong (subTm (single2 (tag k) p)) (subTm-renTm X))
             (trans (subTm-subTm X) (trans (subTm-cong pt X) (subTm-id X)))
      where
        pt : ∀ x → (single2 (tag k) p ∘ₛ (extS (extS (single q)) ₛ∘ᵣ w3)) x ≡ idₛ x
        pt x = refl
    E : subTm (single2 (tag k) p) b₁ ≡ app (app (selM ms) (tag k)) p
    E = cong₂ app (cong₂ app (L3 (selM ms)) refl) refl

-- the one method commutes with substitution
methAt-sub : {Θ : Cx} (σ : Sub Γ Θ) (ms : Cons Γ c) → subTm σ (methAt ms) ≡ methAt (subC σ ms)
methAt-sub σ ms =
  cong (λ X → lam (psplit (app (app X (var (vs vz))) (var vz)) (var vz)))
       (trans (trans (subTm-renTm (selM ms))
                     (trans (subTm-cong pt (selM ms)) (sym (renTm-subTm (selM ms)))))
              (cong (renTm w3) (selF-sub σ ms)))
  where
    pt : ∀ x → (extS (extS (extS σ)) ₛ∘ᵣ w3) x ≡ (w3 ᵣ∘ₛ σ) x
    pt x = ren3 (σ x)
