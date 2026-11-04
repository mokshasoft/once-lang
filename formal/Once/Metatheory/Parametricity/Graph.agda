{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Parametricity.Graph — the graph lemma: a type's
-- relational reading, with variable 0 related by the graph of a function
-- and every other variable by sameness, relates a value to its image under
-- the type's map (`Laws.MapSem.mapS`), and relates only such pairs, for a
-- type in which variable 0 is strictly positive.
--
-- The relational reading compares values of `T ⟨ σA ⟩`, `σA` the instance
-- with `A` for variable 0; the map is stated on `T ⟨ at₀ A ⟩ ⟨ σ ⟩`. The two
-- agree up to `⟨⟩-∘`, a `cong` of the parts' equalities at each former, so
-- the lemma goes by recursion on the type with the transports of
-- `Parametricity.Transport`. A tree's or a stream's constants are related
-- in the map's own value sets (`qG`), and carried across by `Fits`. An
-- arrow's domain, where the variable does not occur, is a shifted type: its
-- reading is sameness (`Subst`, `Identity`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Metatheory.Parametricity.Graph (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Finite; fin; Purity; mk-kind; Zero; One; Many)
open import Once.Spec.Type
  using (Ty; Type; Fun; KCtx; TySub; _⟨_⟩; _⟨_⟩F; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_;
         at₀; shiftᵗ; Occurs; OccursF; o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ˡ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ)
open import Once.Spec.Type.Substitution using (⟨⟩-∘; ⟨⟩F-∘)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Effect Σ using (M; T∞; toT∞; fmap; _>>=∞_; return∞; SRel; rK; rId; _r⊕_; _r⊗_; LayerRel; νM; ana)
open νM using (outν)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code)
open import Once.Spec.Equivalence Σ
open import Once.Spec.Metatheory
  using (StrictlyPositive; StrictlyPositiveF; sp-var; sp-Unit; sp-Void; sp-Int; sp-Float; sp-*; sp-+; sp-⇒; sp-μ; sp-ν;
         sp-K; sp-Id; sp-⊕; sp-⊗)
open import Once.Metatheory.Bisim Σ using (idʳ; idˡ; assoc; ≈-bind; ≈-refl; ≈-sym; ≈-trans)
open import Once.Metatheory.Erase Σ using (toT∞-fmap)
open import Once.Metatheory.Unfold Σ using (module Unfold)
open import Once.Metatheory.Coherence.Relation Σ using (Related; fromObserved; toObserved; bindRel; returnRel; ≈-Relatedˡ; ≈-Relatedʳ)
open import Once.Metatheory.Laws.MapSem Σ
  using (module MapAt; Occ; OccF; p-var; p-*ˡ; p-*ʳ; p-+ˡ; p-+ʳ; p-⇒ʳ; p-μ; p-ν; p-K; p-⊕ˡ; p-⊕ʳ; p-⊗ˡ; p-⊗ʳ)
open import Once.Metatheory.Parametricity.Identity Σ using (rel-same; same-rel; Observed-mono)
open import Once.Metatheory.Parametricity.Transport Σ
open import Once.Metatheory.Parametricity.Comp Σ using (outRelR)
open import Once.Metatheory.Parametricity.Subst Σ using (rel-sub→; rel-sub←; E)

------------------------------------------------------------------------
-- A type without variable 0 is a shifted type
------------------------------------------------------------------------

str  : ∀ {m} (T : Ty (suc m)) → ¬ Occurs zero T → Σ[ T′ ∈ Ty m ] (T ≡ T′ ⟨ shiftᵗ ⟩)
strF : ∀ {m} (F : Fun (suc m)) → ¬ OccursF zero F → Σ[ F′ ∈ Fun m ] (F ≡ F′ ⟨ shiftᵗ ⟩F)
str (var zero)    n = ⊥-elim (n o-var)
str (var (suc i)) n = var i , refl
str Unit  n = Unit , refl
str Void  n = Void , refl
str Int   n = Int , refl
str Float n = Float , refl
str (A * B) n with str A (λ o → n (o-*ˡ o)) | str B (λ o → n (o-*ʳ o))
... | A′ , refl | B′ , refl = A′ * B′ , refl
str (A + B) n with str A (λ o → n (o-+ˡ o)) | str B (λ o → n (o-+ʳ o))
... | A′ , refl | B′ , refl = A′ + B′ , refl
str (A ⇒[ k ] B) n with str A (λ o → n (o-⇒ˡ o)) | str B (λ o → n (o-⇒ʳ o))
... | A′ , refl | B′ , refl = A′ ⇒[ k ] B′ , refl
str (μ F) n with strF F (λ o → n (o-μ o))
... | F′ , refl = μ F′ , refl
str (ν F f) n with strF F (λ o → n (o-ν o))
... | F′ , refl = ν F′ f , refl
strF (K A) n with str A (λ o → n (o-K o))
... | A′ , refl = K A′ , refl
strF Id n = Id , refl
strF (F ⊕ G) n with strF F (λ o → n (o-⊕ˡ o)) | strF G (λ o → n (o-⊕ʳ o))
... | F′ , refl | G′ , refl = F′ ⊕ G′ , refl
strF (F ⊗ G) n with strF F (λ o → n (o-⊗ˡ o)) | strF G (λ o → n (o-⊗ʳ o))
... | F′ , refl | G′ , refl = F′ ⊗ G′ , refl

------------------------------------------------------------------------
-- Transports between closed types
------------------------------------------------------------------------

coe : ∀ {X Y : Type} → X ≡ Y → ⟦ X ⟧ᵛ → ⟦ Y ⟧ᵛ
coe = subst ⟦_⟧ᵛ

coe-trans : ∀ {X Y Z : Type} (p : X ≡ Y) (q : Y ≡ Z) (x : ⟦ X ⟧ᵛ) → coe q (coe p x) ≡ coe (trans p q) x
coe-trans refl refl x = refl

-- Any two transports between the same types agree.
coe-irr : ∀ {X Y : Type} (p q : X ≡ Y) (x : ⟦ X ⟧ᵛ) → coe p x ≡ coe q x
coe-irr p q x = cong (λ e → coe e x) (uip p q)

-- Three transports are one.
coe₃ : ∀ {W X Y Z : Type} (a : W ≡ X) (b : X ≡ Y) (c : Y ≡ Z) (p : W ≡ Z) (x : ⟦ W ⟧ᵛ) → coe c (coe b (coe a x)) ≡ coe p x
coe₃ a b c p x = trans (cong (coe c) (coe-trans a b x)) (trans (coe-trans (trans a b) c x) (coe-irr _ p x))

Same-coe : ∀ {X Y : Type} (p : X ≡ Y) {u v} → Same X u v → Same Y (coe p u) (coe p v)
Same-coe refl s = s

-- The relational reading, along an equality of open types.
Rel-≡ : ∀ {k} {T T′ : Ty k} (eq : T ≡ T′) {σ₁ σ₂ : TySub k 0} (ρ : RelSub σ₁ σ₂) {x y}
      → Rel T ρ x y → Rel T′ ρ (coe (cong (_⟨ σ₁ ⟩) eq) x) (coe (cong (_⟨ σ₂ ⟩) eq) y)
Rel-≡ refl ρ r = r

-- Observed computations, transported back; mapped on one side.
obs-subst⁻ : ∀ π {C D C′ D′ : Type} (e : C ≡ D) (e′ : C′ ≡ D′) {R : ⟦ D ⟧ᵛ → ⟦ D′ ⟧ᵛ → Set} {m m′}
           → Observed R (toT∞ π (subst (MT π) e m)) (toT∞ π (subst (MT π) e′ m′))
           → Observed (λ u v → R (subst T⟦_⟧ e u) (subst T⟦_⟧ e′ v)) (toT∞ π m) (toT∞ π m′)
obs-subst⁻ π refl refl o = o

module _ (π : Purity) {X X′ Y : Set} where
  obs-fmapʳ : ∀ {R : X → Y → Set} {h : X′ → Y} {m : M π X} {m′ : M π X′}
            → Observed (λ u v → R u (h v)) (toT∞ π m) (toT∞ π m′) → Observed R (toT∞ π m) (toT∞ π (fmap π h m′))
  obs-fmapʳ {h = h} {m} {m′} o = toObserved
    (≈-Relatedˡ (≈-sym (idʳ (toT∞ π m))) (≈-Relatedʳ (toT∞-fmap π h m′) (bindRel (fromObserved o) λ r → returnRel r)))

  obs-fmapˡ : ∀ {R : Y → X → Set} {h : X′ → Y} {m : M π X′} {m′ : M π X}
            → Observed (λ u v → R (h u) v) (toT∞ π m) (toT∞ π m′) → Observed R (toT∞ π (fmap π h m)) (toT∞ π m′)
  obs-fmapˡ {h = h} {m} {m′} o = toObserved
    (≈-Relatedˡ (toT∞-fmap π h m) (≈-Relatedʳ (≈-sym (idʳ (toT∞ π m′))) (bindRel (fromObserved o) λ r → returnRel r)))

------------------------------------------------------------------------
-- The graph lemma
------------------------------------------------------------------------

module Graph {m : ℕ} (Δ : KCtx m) (σ : TySub m 0) (A B : Ty m) (R₀ : ⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ B ⟨ σ ⟩ ⟧ᵛ → Set) where
  open MapAt Δ σ A B

  -- The instances with `A`, `B` for variable 0.
  σA σB : TySub (suc m) 0
  σA i = at₀ A i ⟨ σ ⟩
  σB i = at₀ B i ⟨ σ ⟩

  -- Variable 0 by `R₀`, every other variable by sameness.
  ρ₀ : RelSub σA σB
  ρ₀ = relSub λ { zero → R₀ ; (suc i) → Same (σ i) }

  pA : ∀ T → T ⟨ at₀ A ⟩ ⟨ σ ⟩ ≡ T ⟨ σA ⟩
  pA T = ⟨⟩-∘ T (at₀ A) σ
  pB : ∀ T → T ⟨ at₀ B ⟩ ⟨ σ ⟩ ≡ T ⟨ σB ⟩
  pB T = ⟨⟩-∘ T (at₀ B) σ
  pAF : ∀ H → H ⟨ at₀ A ⟩F ⟨ σ ⟩F ≡ H ⟨ σA ⟩F
  pAF H = ⟨⟩F-∘ H (at₀ A) σ
  pBF : ∀ H → H ⟨ at₀ B ⟩F ⟨ σ ⟩F ≡ H ⟨ σB ⟩F
  pBF H = ⟨⟩F-∘ H (at₀ B) σ

  -- The relational reading, on the map's own value sets.
  RelT : ∀ T → VA T → VB T → Set
  RelT T x y = Rel T ρ₀ (coe (pA T) x) (coe (pB T) y)

  -- A functor's constants, so related.
  qG : ∀ H → SRel (CA H) (CB H)
  qG (K C)   = rK (RelT C)
  qG Id      = rId
  qG (F ⊕ G) = qG F r⊕ qG G
  qG (F ⊗ G) = qG F r⊗ qG G

  fitsQ : ∀ H → Fits (pAF H) (pBF H) (qG H) (RelF H ρ₀)
  fitsQ (K C)   = fits-K (pA C) (pB C) (λ r → r)
  fitsQ Id      = tt
  fitsQ (F ⊕ G) = fits-⊕ (pAF F) (pAF G) (pBF F) (pBF G) (fitsQ F) (fitsQ G)
  fitsQ (F ⊗ G) = fits-⊗ (pAF F) (pAF G) (pBF F) (pBF G) (fitsQ F) (fitsQ G)

  fitsQˢ : ∀ H → Fits (sym (pAF H)) (sym (pBF H)) (RelF H ρ₀) (qG H)
  fitsQˢ (K C)   = fits-Kˢ (pA C) (pB C) (λ {a} {b} r → subst₂ (Rel C ρ₀) (sym (coe-sym (pA C) a)) (sym (coe-sym (pB C) b)) r)
  fitsQˢ Id      = tt
  fitsQˢ (F ⊕ G) = fits-⊕ˢ (pAF F) (pAF G) (pBF F) (pBF G) (fitsQˢ F) (fitsQˢ G)
  fitsQˢ (F ⊗ G) = fits-⊗ˢ (pAF F) (pAF G) (pBF F) (pBF G) (fitsQˢ F) (fitsQˢ G)

  ----------------------------------------------------------------------
  -- Where variable 0 does not occur: the reading is sameness
  ----------------------------------------------------------------------

  private
    coeσ : ∀ {X Y : Ty m} → X ≡ Y → ⟦ X ⟨ σ ⟩ ⟧ᵛ → ⟦ Y ⟨ σ ⟩ ⟧ᵛ
    coeσ e = subst (λ Z → ⟦ Z ⟨ σ ⟩ ⟧ᵛ) e

    coeσ-is : ∀ {X Y : Ty m} (e : X ≡ Y) x → coeσ e x ≡ coe (cong (_⟨ σ ⟩) e) x
    coeσ-is refl x = refl

    Same-coeσ : ∀ {X Y : Ty m} (e : X ≡ Y) {u v} → Same (X ⟨ σ ⟩) u v → Same (Y ⟨ σ ⟩) (coeσ e u) (coeσ e v)
    Same-coeσ refl s = s

    coeσ-sym : ∀ {X Y : Ty m} (e : X ≡ Y) x → coeσ e (coeσ (sym e) x) ≡ x
    coeσ-sym refl x = refl

    sym-coeσ : ∀ {X Y : Ty m} (e : X ≡ Y) x → coeσ (sym e) (coeσ e x) ≡ x
    sym-coeσ refl x = refl

    -- the shifted type's variable `j` is variable `suc j`, read at `σ j`
    e₀A : ∀ j → σ j ≡ shiftᵗ j ⟨ σA ⟩
    e₀A j = refl
    e₀B : ∀ j → σ j ≡ shiftᵗ j ⟨ σB ⟩
    e₀B j = refl

  -- No occurrence: related exactly when the same, across the instances' equality.
  module NoOcc (T : Ty (suc m)) (n : ¬ Occurs zero T) (e : T ⟨ at₀ A ⟩ ≡ T ⟨ at₀ B ⟩) where
    private
      T′  = proj₁ (str T n)
      eq₀ = proj₂ (str T n)
      -- each side, carried to the shifted type's instance
      qA : T ⟨ at₀ A ⟩ ⟨ σ ⟩ ≡ T′ ⟨ σ ⟩
      qA = trans (pA T) (trans (cong (_⟨ σA ⟩) eq₀) (sym (E e₀A T′)))
      qB : T ⟨ at₀ B ⟩ ⟨ σ ⟩ ≡ T′ ⟨ σ ⟩
      qB = trans (pB T) (trans (cong (_⟨ σB ⟩) eq₀) (sym (E e₀B T′)))

      toSame : ∀ {x y} → RelT T x y → Same (T′ ⟨ σ ⟩) (coe qA x) (coe qB y)
      toSame {x} {y} r =
        subst₂ (Same (T′ ⟨ σ ⟩)) (coe₃ (pA T) (cong (_⟨ σA ⟩) eq₀) (sym (E e₀A T′)) qA x)
                                 (coe₃ (pB T) (cong (_⟨ σB ⟩) eq₀) (sym (E e₀B T′)) qB y)
          (rel-same T′ σ (rel-sub← shiftᵗ ρ₀ e₀A e₀B T′ (Rel-≡ eq₀ ρ₀ r)))

      fromSame : ∀ {x y} → Same (T′ ⟨ σ ⟩) (coe qA x) (coe qB y) → RelT T x y
      fromSame {x} {y} s =
        subst₂ (Rel T ρ₀) (coe₃ qA (E e₀A T′) (cong (_⟨ σA ⟩) (sym eq₀)) (pA T) x)
                          (coe₃ qB (E e₀B T′) (cong (_⟨ σB ⟩) (sym eq₀)) (pB T) y)
          (Rel-≡ (sym eq₀) ρ₀ (rel-sub→ shiftᵗ ρ₀ e₀A e₀B T′ (same-rel T′ σ s)))

      -- `coeσ e` then `qB` is `qA`
      viaB : ∀ x → coe qB (coeσ e x) ≡ coe qA x
      viaB x = trans (cong (coe qB) (coeσ-is e x)) (trans (coe-trans _ qB x) (coe-irr _ qA x))

    no← : ∀ {x y} → RelT T x y → Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩) (coeσ e x) y
    no← {x} {y} r =
      subst₂ (Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩))
        (trans (cong (coe (sym qB)) (sym (viaB x))) (trans (coe-trans qB (sym qB) (coeσ e x)) (coe-irr (trans qB (sym qB)) refl (coeσ e x))))
        (trans (coe-trans qB (sym qB) y) (coe-irr (trans qB (sym qB)) refl y))
        (Same-coe (sym qB) (toSame r))

    no→ : ∀ {x y} → Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩) (coeσ e x) y → RelT T x y
    no→ {x} {y} s = fromSame (subst (λ z → Same (T′ ⟨ σ ⟩) z (coe qB y)) (viaB x) (Same-coe qB s))
