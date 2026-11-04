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
open import Data.Nat using (ℕ; zero; suc)
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
open import Once.Spec.Effect Σ using (M; T∞; toT∞; fmap; _>>=∞_; return∞; _≈_; SRel; rK; rId; _r⊕_; _r⊗_; LayerRel; νM; ana)
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

  ----------------------------------------------------------------------
  -- The lemma, both ways
  ----------------------------------------------------------------------

  -- The map's function is the graph's, where the variable occurs.
  H→ : ∀ T → Fn T → Set
  H→ T φ = ∀ (o : Occ T) {a a′} → Same (A ⟨ σ ⟩) a a′ → R₀ a (φ o a′)
  H← : ∀ T → Fn T → Set
  H← T φ = ∀ (o : Occ T) {a b} → R₀ a b → Same (B ⟨ σ ⟩) (φ o a) b
  HF→ : ∀ H → FnF H → Set
  HF→ H φ = ∀ (o : OccF H) {a a′} → Same (A ⟨ σ ⟩) a a′ → R₀ a (φ o a′)
  HF← : ∀ H → FnF H → Set
  HF← H φ = ∀ (o : OccF H) {a b} → R₀ a b → Same (B ⟨ σ ⟩) (φ o a) b

  -- A stream's map: each forced layer mapped.
  cν : ∀ (f : Finite) G → CovF G → FnF G → νM f (CA G) → M (fin f) (⟦ CB G ⟧SF (νM f (CA G)))
  cν f G c φ y = fmap (fin f) (nuLayer G c φ {νM f (CA G)}) (outν y)

  private
    module UB (G : Fun (suc m)) = Unfold (CB G)
    module UA (G : Fun (suc m)) = Unfold (CA G)

    -- forcing a mapped stream: its layer computation, mapped twice
    outAna : ∀ (f : Finite) G (c : CovF G) (φ : FnF G) (x : νM f (CA G))
           → toT∞ (fin f) (outν (ana f (CB G) (cν f G c φ) x))
             ≈ (toT∞ (fin f) (outν x) >>=∞ λ l → return∞ (sfmap (CB G) (ana f (CB G) (cν f G c φ)) (nuLayer G c φ l)))
    outAna f G c φ x =
      ≈-trans (UB.unfold-out≈ G f (cν f G c φ) x)
        (≈-trans (toT∞-fmap (fin f) (sfmap (CB G) (ana f (CB G) (cν f G c φ))) (cν f G c φ x))
          (≈-trans (≈-bind (toT∞-fmap (fin f) (nuLayer G c φ) (outν x)) (λ _ → ≈-refl _))
            (≈-trans (assoc (toT∞ (fin f) (outν x)) _ _) (≈-bind (≈-refl _) (λ l → idˡ (nuLayer G c φ l) _)))))

  -- An arrow's domain: related arguments are the same, once the map's
  -- argument is read back across the instances' equality.
  dom : ∀ T (n : ¬ Occurs zero T) (e : T ⟨ at₀ A ⟩ ≡ T ⟨ at₀ B ⟩) {a a′}
      → Rel T ρ₀ a a′ → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) (coe (sym (pA T)) a) (coeσ (sym e) (coe (sym (pB T)) a′))
  dom T n e {a} {a′} r =
    subst (λ z → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) z (coeσ (sym e) (coe (sym (pB T)) a′))) (sym-coeσ e (coe (sym (pA T)) a))
      (Same-coeσ (sym e) (NoOcc.no← T n e (subst₂ (Rel T ρ₀) (sym (coe-sym (pA T) a)) (sym (coe-sym (pB T) a′)) r)))

  gl→   : ∀ T → StrictlyPositive T → (c : Cov T) (φ : Fn T) → H→ T φ
        → ∀ {x x′} → Same (T ⟨ at₀ A ⟩ ⟨ σ ⟩) x x′ → RelT T x (mapS T c φ x′)
  muGL→ : ∀ G → StrictlyPositiveF G → (c : CovF G) (φ : FnF G) → HF→ G φ
        → ∀ {x x′} → RelMu (SameF (G ⟨ at₀ A ⟩F ⟨ σ ⟩F)) x x′ → RelMu (qG G) x (muMap G c φ x′)
  lyGL→ : ∀ G H → StrictlyPositiveF G → (cG : CovF G) (φG : FnF G) → HF→ G φG
        → StrictlyPositiveF H → (cH : CovF H) (φH : FnF H) → HF→ H φH
        → ∀ {l l′} → LayerRel (SameF (H ⟨ at₀ A ⟩F ⟨ σ ⟩F)) (RelMu (SameF (G ⟨ at₀ A ⟩F ⟨ σ ⟩F))) l l′
        → LayerRel (qG H) (RelMu (qG G)) l (muLayer G H cG φG cH φH l′)
  nuGL→ : ∀ (f : Finite) G → StrictlyPositiveF G → (c : CovF G) (φ : FnF G) → HF→ G φ
        → ∀ n {x x′} → RelStream f (SameF (G ⟨ at₀ A ⟩F ⟨ σ ⟩F)) x x′ → RelNu f (qG G) n x (ana f (CB G) (cν f G c φ) x′)
  lyNu→ : ∀ (f : Finite) G H → StrictlyPositiveF G → (cG : CovF G) (φG : FnF G) → HF→ G φG
        → StrictlyPositiveF H → (cH : CovF H) (φH : FnF H) → HF→ H φH → ∀ n
        → ∀ {l l′} → LayerRel (SameF (H ⟨ at₀ A ⟩F ⟨ σ ⟩F)) (RelStream f (SameF (G ⟨ at₀ A ⟩F ⟨ σ ⟩F))) l l′
        → LayerRel (qG H) (RelNu f (qG G) n) l (sfmap (CB H) (ana f (CB G) (cν f G cG φG)) (nuLayer H cH φH l′))

  gl→ (var zero)    sp-var c φ h s = h p-var s
  gl→ (var (suc i)) sp-var c φ h s = s
  gl→ Unit  sp-Unit  c φ h s = tt
  gl→ Void  sp-Void  c φ h {()}
  gl→ Int   sp-Int   c φ h s = s
  gl→ Float sp-Float c φ h s = s
  gl→ (T₁ * T₂) (sp-* s₁ s₂) (c₁ , c₂) φ h {x₁ , x₂} {x₁′ , x₂′} (r₁ , r₂) =
    subst₂ (Rel (T₁ * T₂) ρ₀) (sym (fwd-* (pA T₁) (pA T₂) x₁ x₂)) (sym (fwd-* (pB T₁) (pB T₂) _ _))
      (gl→ T₁ s₁ c₁ (λ o → φ (p-*ˡ o)) (λ o → h (p-*ˡ o)) r₁ , gl→ T₂ s₂ c₂ (λ o → φ (p-*ʳ o)) (λ o → h (p-*ʳ o)) r₂)
  gl→ (T₁ + T₂) (sp-+ s₁ s₂) (c₁ , c₂) φ h {inj₁ x} {inj₁ x′} r =
    subst₂ (Rel (T₁ + T₂) ρ₀) (sym (fwd-+₁ (pA T₁) (pA T₂) x)) (sym (fwd-+₁ (pB T₁) (pB T₂) _))
      (gl→ T₁ s₁ c₁ (λ o → φ (p-+ˡ o)) (λ o → h (p-+ˡ o)) r)
  gl→ (T₁ + T₂) (sp-+ s₁ s₂) (c₁ , c₂) φ h {inj₂ x} {inj₂ x′} r =
    subst₂ (Rel (T₁ + T₂) ρ₀) (sym (fwd-+₂ (pA T₁) (pA T₂) x)) (sym (fwd-+₂ (pB T₁) (pB T₂) _))
      (gl→ T₂ s₂ c₂ (λ o → φ (p-+ʳ o)) (λ o → h (p-+ʳ o)) r)
  gl→ (T₁ + T₂) (sp-+ s₁ s₂) c φ h {inj₁ x} {inj₂ x′} ()
  gl→ (T₁ + T₂) (sp-+ s₁ s₂) c φ h {inj₂ x} {inj₁ x′} ()
  gl→ (T₁ ⇒[ mk-kind Zero π ] T₂) (sp-⇒ n s₂) (e , c₂) φ h {g} {g′} s =
    subst₂ (λ u u′ → Observed (Rel T₂ ρ₀) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd₀ π (pA T₁) (pA T₂) g _))
      (sym (app-fwd₀ π (pB T₁) (pB T₂) (mapS (T₁ ⇒[ mk-kind Zero π ] T₂) (e , c₂) φ g′) _))
      (obs-subst π (pA T₂) (pB T₂) (obs-fmapʳ π (Observed-mono (gl→ T₂ s₂ c₂ (λ o → φ (p-⇒ʳ o)) (λ o → h (p-⇒ʳ o))) s)))
  gl→ (T₁ ⇒[ mk-kind One π ] T₂) (sp-⇒ n s₂) (e , c₂) φ h {g} {g′} s a a′ ra =
    subst₂ (λ u u′ → Observed (Rel T₂ ρ₀) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd₁ π (pA T₁) (pA T₂) g a))
      (sym (app-fwd₁ π (pB T₁) (pB T₂) (mapS (T₁ ⇒[ mk-kind One π ] T₂) (e , c₂) φ g′) a′))
      (obs-subst π (pA T₂) (pB T₂) (obs-fmapʳ π (Observed-mono (gl→ T₂ s₂ c₂ (λ o → φ (p-⇒ʳ o)) (λ o → h (p-⇒ʳ o)))
        (s _ _ (dom T₁ n e ra)))))
  gl→ (T₁ ⇒[ mk-kind Many π ] T₂) (sp-⇒ n s₂) (e , c₂) φ h {g} {g′} s a a′ ra =
    subst₂ (λ u u′ → Observed (Rel T₂ ρ₀) (toT∞ π u) (toT∞ π u′))
      (sym (app-fwd π (pA T₁) (pA T₂) g a))
      (sym (app-fwd π (pB T₁) (pB T₂) (mapS (T₁ ⇒[ mk-kind Many π ] T₂) (e , c₂) φ g′) a′))
      (obs-subst π (pA T₂) (pB T₂) (obs-fmapʳ π (Observed-mono (gl→ T₂ s₂ c₂ (λ o → φ (p-⇒ʳ o)) (λ o → h (p-⇒ʳ o)))
        (s _ _ (dom T₁ n e ra)))))
  gl→ (μ G) (sp-μ spG) c φ h s = castμ (pAF G) (pBF G) (fitsQ G) (muGL→ G spG c (λ o → φ (p-μ o)) (λ o → h (p-μ o)) s)
  gl→ (ν G f) (sp-ν spG) c φ h s = castν f (pAF G) (pBF G) (fitsQ G) (λ n → nuGL→ f G spG c (λ o → φ (p-ν o)) (λ o → h (p-ν o)) n s)

  muGL→ G sp c φ h {inS l} {inS l′} (inR p) = inR (lyGL→ G G sp c φ h sp c φ h p)

  lyGL→ G (K C) spG cG φG hG (sp-K sC) (cC , _ , _) φH hH p = gl→ C sC cC (λ o → φH (p-K o)) (λ o → hH (p-K o)) p
  lyGL→ G Id spG cG φG hG sp-Id cH φH hH p = muGL→ G spG cG φG hG p
  lyGL→ G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₁ x} {inj₁ y} p =
    lyGL→ G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊕ˡ o)) (λ o → hH (p-⊕ˡ o)) p
  lyGL→ G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₂ x} {inj₂ y} p =
    lyGL→ G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊕ʳ o)) (λ o → hH (p-⊕ʳ o)) p
  lyGL→ G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₁ x} {inj₂ y} ()
  lyGL→ G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₂ x} {inj₁ y} ()
  lyGL→ G (H₁ ⊗ H₂) spG cG φG hG (sp-⊗ s₁ s₂) (c₁ , c₂) φH hH {x , x′} {y , y′} (p , p′) =
    lyGL→ G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊗ˡ o)) (λ o → hH (p-⊗ˡ o)) p ,
    lyGL→ G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊗ʳ o)) (λ o → hH (p-⊗ʳ o)) p′

  nuGL→ f G sp c φ h zero    s = tt
  nuGL→ f G sp c φ h (suc n) {x} {x′} s =
    toObserved (≈-Relatedˡ (≈-sym (idʳ (toT∞ (fin f) (outν x)))) (≈-Relatedʳ (outAna f G c φ x′)
      (bindRel (outRelR f (SameF (G ⟨ at₀ A ⟩F ⟨ σ ⟩F)) s) λ r → returnRel (lyNu→ f G G sp c φ h sp c φ h n r))))

  lyNu→ f G (K C) spG cG φG hG (sp-K sC) (cC , _ , _) φH hH n p = gl→ C sC cC (λ o → φH (p-K o)) (λ o → hH (p-K o)) p
  lyNu→ f G Id spG cG φG hG sp-Id cH φH hH n p = nuGL→ f G spG cG φG hG n p
  lyNu→ f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₁ x} {inj₁ y} p =
    lyNu→ f G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊕ˡ o)) (λ o → hH (p-⊕ˡ o)) n p
  lyNu→ f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₂ x} {inj₂ y} p =
    lyNu→ f G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊕ʳ o)) (λ o → hH (p-⊕ʳ o)) n p
  lyNu→ f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₁ x} {inj₂ y} ()
  lyNu→ f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₂ x} {inj₁ y} ()
  lyNu→ f G (H₁ ⊗ H₂) spG cG φG hG (sp-⊗ s₁ s₂) (c₁ , c₂) φH hH n {x , x′} {y , y′} (p , p′) =
    lyNu→ f G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊗ˡ o)) (λ o → hH (p-⊗ˡ o)) n p ,
    lyNu→ f G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊗ʳ o)) (λ o → hH (p-⊗ʳ o)) n p′

  private
    -- forcing a mapped stream, read the other way round
    outAnaˡ : ∀ (f : Finite) G (c : CovF G) (φ : FnF G) (x : νM f (CA G))
            → toT∞ (fin f) (outν (ana f (CB G) (cν f G c φ) x))
              ≈ (toT∞ (fin f) (outν x) >>=∞ λ l → return∞ (sfmap (CB G) (ana f (CB G) (cν f G c φ)) (nuLayer G c φ l)))
    outAnaˡ = outAna

  -- An arrow's domain, the other way: the same arguments are related, once
  -- the map's argument is read across the instances' equality.
  domʳ : ∀ T (n : ¬ Occurs zero T) (e : T ⟨ at₀ A ⟩ ≡ T ⟨ at₀ B ⟩) {b b′}
       → Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩) b b′ → Rel T ρ₀ (coe (pA T) (coeσ (sym e) b)) (coe (pB T) b′)
  domʳ T n e {b} {b′} s = NoOcc.no→ T n e (subst (λ z → Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩) z b′) (sym (coeσ-sym e b)) s)

  gl←   : ∀ T → StrictlyPositive T → (c : Cov T) (φ : Fn T) → H← T φ
        → ∀ {u v} → RelT T u v → Same (T ⟨ at₀ B ⟩ ⟨ σ ⟩) (mapS T c φ u) v
  muGL← : ∀ G → StrictlyPositiveF G → (c : CovF G) (φ : FnF G) → HF← G φ
        → ∀ {u v} → RelMu (qG G) u v → RelMu (SameF (G ⟨ at₀ B ⟩F ⟨ σ ⟩F)) (muMap G c φ u) v
  lyGL← : ∀ G H → StrictlyPositiveF G → (cG : CovF G) (φG : FnF G) → HF← G φG
        → StrictlyPositiveF H → (cH : CovF H) (φH : FnF H) → HF← H φH
        → ∀ {l l′} → LayerRel (qG H) (RelMu (qG G)) l l′
        → LayerRel (SameF (H ⟨ at₀ B ⟩F ⟨ σ ⟩F)) (RelMu (SameF (G ⟨ at₀ B ⟩F ⟨ σ ⟩F))) (muLayer G H cG φG cH φH l) l′
  nuGL← : ∀ (f : Finite) G → StrictlyPositiveF G → (c : CovF G) (φ : FnF G) → HF← G φ
        → ∀ n {u v} → RelStream f (qG G) u v → RelNu f (SameF (G ⟨ at₀ B ⟩F ⟨ σ ⟩F)) n (ana f (CB G) (cν f G c φ) u) v
  lyNu← : ∀ (f : Finite) G H → StrictlyPositiveF G → (cG : CovF G) (φG : FnF G) → HF← G φG
        → StrictlyPositiveF H → (cH : CovF H) (φH : FnF H) → HF← H φH → ∀ n
        → ∀ {l l′} → LayerRel (qG H) (λ x y → ∀ k → RelNu f (qG G) k x y) l l′
        → LayerRel (SameF (H ⟨ at₀ B ⟩F ⟨ σ ⟩F)) (RelNu f (SameF (G ⟨ at₀ B ⟩F ⟨ σ ⟩F)) n)
                   (sfmap (CB H) (ana f (CB G) (cν f G cG φG)) (nuLayer H cH φH l)) l′

  gl← (var zero)    sp-var c φ h r = h p-var r
  gl← (var (suc i)) sp-var c φ h r = r
  gl← Unit  sp-Unit  c φ h r = tt
  gl← Void  sp-Void  c φ h {()}
  gl← Int   sp-Int   c φ h r = r
  gl← Float sp-Float c φ h r = r
  gl← (T₁ * T₂) (sp-* s₁ s₂) (c₁ , c₂) φ h {u₁ , u₂} {v₁ , v₂} r
    with subst₂ (Rel (T₁ * T₂) ρ₀) (fwd-* (pA T₁) (pA T₂) u₁ u₂) (fwd-* (pB T₁) (pB T₂) v₁ v₂) r
  ... | r₁ , r₂ = gl← T₁ s₁ c₁ (λ o → φ (p-*ˡ o)) (λ o → h (p-*ˡ o)) r₁ , gl← T₂ s₂ c₂ (λ o → φ (p-*ʳ o)) (λ o → h (p-*ʳ o)) r₂
  gl← (T₁ + T₂) (sp-+ s₁ s₂) (c₁ , c₂) φ h {inj₁ u} {inj₁ v} r =
    gl← T₁ s₁ c₁ (λ o → φ (p-+ˡ o)) (λ o → h (p-+ˡ o)) (subst₂ (Rel (T₁ + T₂) ρ₀) (fwd-+₁ (pA T₁) (pA T₂) u) (fwd-+₁ (pB T₁) (pB T₂) v) r)
  gl← (T₁ + T₂) (sp-+ s₁ s₂) (c₁ , c₂) φ h {inj₂ u} {inj₂ v} r =
    gl← T₂ s₂ c₂ (λ o → φ (p-+ʳ o)) (λ o → h (p-+ʳ o)) (subst₂ (Rel (T₁ + T₂) ρ₀) (fwd-+₂ (pA T₁) (pA T₂) u) (fwd-+₂ (pB T₁) (pB T₂) v) r)
  gl← (T₁ + T₂) (sp-+ s₁ s₂) c φ h {inj₁ u} {inj₂ v} r =
    ⊥-elim (subst₂ (Rel (T₁ + T₂) ρ₀) (fwd-+₁ (pA T₁) (pA T₂) u) (fwd-+₂ (pB T₁) (pB T₂) v) r)
  gl← (T₁ + T₂) (sp-+ s₁ s₂) c φ h {inj₂ u} {inj₁ v} r =
    ⊥-elim (subst₂ (Rel (T₁ + T₂) ρ₀) (fwd-+₂ (pA T₁) (pA T₂) u) (fwd-+₁ (pB T₁) (pB T₂) v) r)
  gl← (T₁ ⇒[ mk-kind Zero π ] T₂) (sp-⇒ n s₂) (e , c₂) φ h {g} {k} r =
    obs-fmapˡ π (Observed-mono (gl← T₂ s₂ c₂ (λ o → φ (p-⇒ʳ o)) (λ o → h (p-⇒ʳ o)))
      (obs-subst⁻ π (pA T₂) (pB T₂)
        (subst₂ (λ u u′ → Observed (Rel T₂ ρ₀) (toT∞ π u) (toT∞ π u′))
          (app-fwd₀ π (pA T₁) (pA T₂) g _) (app-fwd₀ π (pB T₁) (pB T₂) k _) r)))
  gl← (T₁ ⇒[ mk-kind One π ] T₂) (sp-⇒ n s₂) (e , c₂) φ h {g} {k} r b b′ sb =
    obs-fmapˡ π (Observed-mono (gl← T₂ s₂ c₂ (λ o → φ (p-⇒ʳ o)) (λ o → h (p-⇒ʳ o)))
      (obs-subst⁻ π (pA T₂) (pB T₂)
        (subst₂ (λ u u′ → Observed (Rel T₂ ρ₀) (toT∞ π u) (toT∞ π u′))
          (trans (app-fwd₁ π (pA T₁) (pA T₂) g _) (cong (λ z → subst (MT π) (pA T₂) (g z)) (sym-coe (pA T₁) _)))
          (trans (app-fwd₁ π (pB T₁) (pB T₂) k _) (cong (λ z → subst (MT π) (pB T₂) (k z)) (sym-coe (pB T₁) b′)))
          (r _ _ (domʳ T₁ n e sb)))))
  gl← (T₁ ⇒[ mk-kind Many π ] T₂) (sp-⇒ n s₂) (e , c₂) φ h {g} {k} r b b′ sb =
    obs-fmapˡ π (Observed-mono (gl← T₂ s₂ c₂ (λ o → φ (p-⇒ʳ o)) (λ o → h (p-⇒ʳ o)))
      (obs-subst⁻ π (pA T₂) (pB T₂)
        (subst₂ (λ u u′ → Observed (Rel T₂ ρ₀) (toT∞ π u) (toT∞ π u′))
          (trans (app-fwd π (pA T₁) (pA T₂) g _) (cong (λ z → subst (MT π) (pA T₂) (g z)) (sym-coe (pA T₁) _)))
          (trans (app-fwd π (pB T₁) (pB T₂) k _) (cong (λ z → subst (MT π) (pB T₂) (k z)) (sym-coe (pB T₁) b′)))
          (r _ _ (domʳ T₁ n e sb)))))
  gl← (μ G) (sp-μ spG) c φ h {u} {v} r =
    muGL← G spG c (λ o → φ (p-μ o)) (λ o → h (p-μ o))
      (subst₂ (RelMu (qG G)) (sym-coe (cong μ (pAF G)) u) (sym-coe (cong μ (pBF G)) v) (castμˢ (pAF G) (pBF G) (fitsQˢ G) r))
  gl← (ν G f) (sp-ν spG) c φ h {u} {v} r n =
    nuGL← f G spG c (λ o → φ (p-ν o)) (λ o → h (p-ν o)) n
      (subst₂ (RelStream f (qG G)) (sym-coe (cong (λ X → ν X f) (pAF G)) u) (sym-coe (cong (λ X → ν X f) (pBF G)) v)
        (castνˢ f (pAF G) (pBF G) (fitsQˢ G) r))

  muGL← G sp c φ h {inS l} {inS l′} (inR p) = inR (lyGL← G G sp c φ h sp c φ h p)

  lyGL← G (K C) spG cG φG hG (sp-K sC) (cC , _ , _) φH hH p = gl← C sC cC (λ o → φH (p-K o)) (λ o → hH (p-K o)) p
  lyGL← G Id spG cG φG hG sp-Id cH φH hH p = muGL← G spG cG φG hG p
  lyGL← G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₁ x} {inj₁ y} p =
    lyGL← G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊕ˡ o)) (λ o → hH (p-⊕ˡ o)) p
  lyGL← G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₂ x} {inj₂ y} p =
    lyGL← G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊕ʳ o)) (λ o → hH (p-⊕ʳ o)) p
  lyGL← G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₁ x} {inj₂ y} ()
  lyGL← G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH {inj₂ x} {inj₁ y} ()
  lyGL← G (H₁ ⊗ H₂) spG cG φG hG (sp-⊗ s₁ s₂) (c₁ , c₂) φH hH {x , x′} {y , y′} (p , p′) =
    lyGL← G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊗ˡ o)) (λ o → hH (p-⊗ˡ o)) p ,
    lyGL← G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊗ʳ o)) (λ o → hH (p-⊗ʳ o)) p′

  nuGL← f G sp c φ h zero    r = tt
  nuGL← f G sp c φ h (suc n) {u} {v} r =
    toObserved (≈-Relatedˡ (outAnaˡ f G c φ u) (≈-Relatedʳ (≈-sym (idʳ (toT∞ (fin f) (outν v))))
      (bindRel (outRelR f (qG G) r) λ q → returnRel (lyNu← f G G sp c φ h sp c φ h n q))))

  lyNu← f G (K C) spG cG φG hG (sp-K sC) (cC , _ , _) φH hH n p = gl← C sC cC (λ o → φH (p-K o)) (λ o → hH (p-K o)) p
  lyNu← f G Id spG cG φG hG sp-Id cH φH hH n p = nuGL← f G spG cG φG hG n p
  lyNu← f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₁ x} {inj₁ y} p =
    lyNu← f G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊕ˡ o)) (λ o → hH (p-⊕ˡ o)) n p
  lyNu← f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₂ x} {inj₂ y} p =
    lyNu← f G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊕ʳ o)) (λ o → hH (p-⊕ʳ o)) n p
  lyNu← f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₁ x} {inj₂ y} ()
  lyNu← f G (H₁ ⊕ H₂) spG cG φG hG (sp-⊕ s₁ s₂) (c₁ , c₂) φH hH n {inj₂ x} {inj₁ y} ()
  lyNu← f G (H₁ ⊗ H₂) spG cG φG hG (sp-⊗ s₁ s₂) (c₁ , c₂) φH hH n {x , x′} {y , y′} (p , p′) =
    lyNu← f G H₁ spG cG φG hG s₁ c₁ (λ o → φH (p-⊗ˡ o)) (λ o → hH (p-⊗ˡ o)) n p ,
    lyNu← f G H₂ spG cG φG hG s₂ c₂ (λ o → φH (p-⊗ʳ o)) (λ o → hH (p-⊗ʳ o)) n p′
