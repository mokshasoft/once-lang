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
-- ★ The only places annotation is CREATED rather than copied: `methSᴬ`
--   builds the scrutinee `con p` (which in `ATm` carries its index code,
--   description and index), `pairSᴬ` a `pair` (its second component's
--   family), `fsucSᴬ` a successor tag (its bound).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.AnnotatedDesc where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing
  using ( single; single2; pairS; fsucS; iinst; methS; wk2M; MethTy; DescF )
open import DirectedHoTT.Spec.Annotated

private
  variable
    Γ Δ : Cx
    I D : ATm Γ

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

iinstᴬ : ATm Γ → ATm Γ → ATy ((Γ ∙) ∙) → ATy Γ
iinstᴬ j t M = subTyᴬ (singleᴬ t) (subTyᴬ (extSᴬ (singleᴬ j)) M)

era-iinst : (j t : ATm Γ) (M : ATy ((Γ ∙) ∙)) →
            ⌈ iinstᴬ j t M ⌉ᵀ ≡ iinst ⌈ j ⌉ ⌈ t ⌉ ⌈ M ⌉ᵀ
era-iinst j t M =
  trans (era-subTy (singleᴬ t) (single ⌈ t ⌉) (era-single t) (subTyᴬ (extSᴬ (singleᴬ j)) M))
        (cong (subTy (single ⌈ t ⌉))
              (era-subTy (extSᴬ (singleᴬ j)) (extS (single ⌈ j ⌉)) (era-ext (era-single j)) M))

-- ★ `psplit`'s instantiation and motive re-basing, `fcase`'s successor
single2ᴬ : ATm Γ → ATm Γ → Subᴬ ((Γ ∙) ∙) Γ
single2ᴬ x y vz           = y
single2ᴬ x y (vs vz)      = x
single2ᴬ x y (vs (vs x')) = var x'

era-single2 : (x y : ATm Γ) → ∀ z → ⌈ single2ᴬ x y z ⌉ ≡ single2 ⌈ x ⌉ ⌈ y ⌉ z
era-single2 x y vz          = refl
era-single2 x y (vs vz)     = refl
era-single2 x y (vs (vs z)) = refl

-- the rebuilt pair carries the second component's family, weakened past
--   the two halves
pairSᴬ : ATy (Γ ∙) → Subᴬ (Γ ∙) ((Γ ∙) ∙)
pairSᴬ B vz     = pair (renTyᴬ (extR (λ x → vs (vs x))) B) (var (vs vz)) (var vz)
pairSᴬ B (vs x) = var (vs (vs x))

era-pairS : (B : ATy (Γ ∙)) → ∀ z → ⌈ pairSᴬ B z ⌉ ≡ pairS z
era-pairS B vz     = refl
era-pairS B (vs z) = refl

fsucSᴬ : ℕ → Subᴬ (Γ ∙) (Γ ∙)
fsucSᴬ n vz     = fsuc n (var vz)
fsucSᴬ n (vs x) = var (vs x)

era-fsucS : (n : ℕ) → ∀ z → ⌈ fsucSᴬ {Γ} n z ⌉ ≡ fsucS z
era-fsucS n vz     = refl
era-fsucS n (vs z) = refl

------------------------------------------------------------------------
-- ★ THE ONE METHOD'S TYPE (Spec/Typing's `MethTy`), annotated.
------------------------------------------------------------------------

wk3ᴬ : ATm Γ → ATm (((Γ ∙) ∙) ∙)
wk3ᴬ = renTmᴬ (λ x → vs (vs (vs x)))

-- the scrutinee `con p` at index `i` after the method's three binders
methSᴬ : ATm Γ → ATm Γ → Subᴬ ((Γ ∙) ∙) (((Γ ∙) ∙) ∙)
methSᴬ I D vz          = con (wk3ᴬ I) (wk3ᴬ D) (var (vs (vs vz))) (var (vs vz))
methSᴬ I D (vs vz)     = var (vs (vs vz))
methSᴬ I D (vs (vs x)) = var (vs (vs (vs x)))

era-methS : (I D : ATm Γ) → ∀ z → ⌈ methSᴬ I D z ⌉ ≡ methS z
era-methS I D vz          = refl
era-methS I D (vs vz)     = refl
era-methS I D (vs (vs z)) = refl

wk2Mᴬ : ATy ((Γ ∙) ∙) → ATy ((((Γ ∙) ∙) ∙) ∙)
wk2Mᴬ M = renTyᴬ (extR (extR (λ x → vs (vs x)))) M

-- D074: the type of a (fibred) description
DescFᴬ : ATm Γ → ATy Γ
DescFᴬ I = Π (El I) (Desc (renTmᴬ vs I))

era-DescF : (I : ATm Γ) → ⌈ DescFᴬ I ⌉ᵀ ≡ DescF ⌈ I ⌉
era-DescF I = cong (λ a → Π (El ⌈ I ⌉) (Desc a)) (era-renTm vs I)

MethTyᴬ : ATm Γ → ATm Γ → ATy ((Γ ∙) ∙) → ATy Γ
MethTyᴬ I D M =
  Π (El I)
    (Π (El (dpay (renTmᴬ vs I) (renTmᴬ vs D) (app (renTmᴬ vs D) (var vz))))
       (Π (DIh (renTmᴬ vs (renTmᴬ vs I)) (renTmᴬ vs (renTmᴬ vs D)) (wk2Mᴬ M)
               (app (renTmᴬ vs (renTmᴬ vs D)) (var (vs vz))) (var vz))
          (subTyᴬ (methSᴬ I D) M)))

era-MethTy : (I D : ATm Γ) (M : ATy ((Γ ∙) ∙)) → ⌈ MethTyᴬ I D M ⌉ᵀ ≡ MethTy ⌈ I ⌉ ⌈ D ⌉ ⌈ M ⌉ᵀ
era-MethTy I D M =
  cong₂ (λ X Y → Π (El ⌈ I ⌉) (Π X Y))
    (cong₂ (λ a b → El (dpay a b (app b (var vz)))) (era-renTm vs I) (era-renTm vs D))
    (cong₃ (λ a b c → Π (DIh a b (app a (var (vs vz))) (var vz)) c)
       (trans (era-renTm vs (renTmᴬ vs D)) (cong (renTm vs) (era-renTm vs D)))
       (era-renTy (extR (extR (λ x → vs (vs x)))) M)
       (era-subTy (methSᴬ I D) methS (era-methS I D) M))
