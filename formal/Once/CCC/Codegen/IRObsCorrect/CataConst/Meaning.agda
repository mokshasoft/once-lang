-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning   (plan 0.125 S3, cata M1)
--
-- WHAT A `strat-const` CATA MEANS: the algebra, run once on the input's
-- own layer.
--
-- A functor with no `Id` (`rec-count ⌈F⌉F ≡ 0`, the classifier's
-- `strat-const`) has no recursive positions, so a layer holds no
-- children: sequencing it (`seqF∞`) returns at once, and `sem-cata`'s one
-- unfolding (`sem-cata-compute`) leaves exactly the algebra on the layer.
-- The equation is between APPROXIMATIONS (`approx k`), which is all an
-- observation reads; the two trees agree on the nose after one `force`.
--
-- The layer the MACHINE has is the μ value's own layer (`ValidFO`'s
-- `fo-μwf`, read through `out-μ`), typed at `⟦ F ⟧TI (μ-type F)`. The
-- algebra takes it at `⟦ F ⟧TI C`. For an `Id`-free `F` the two types are
-- EQUAL (`tyeq`), and the coercions on either side agree along that
-- equation (`coh`) — so the algebra's argument is the machine's layer,
-- moved along a type equation and nothing else.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.CataConst.Meaning (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.IR using (IR; Cata)
open import Once.IRTy using (IRTy; IRFunctor; K; Id; _⊕_; _⊗_; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseTypeI; ⟦_⟧TI; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; μ-type)
import Once.IRTy as I
import Once.Internal.Type as T
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; coerce-functor⁻¹-D)
open import Once.Internal.Iterative using (T∞; module T∞; seqF∞; bindBlock)
open T∞ using (force)
open import Once.Internal.Trace using (T; ret)
open import Once.Spec.Word using (Carrier)
open import Once.Internal.Value Carrier Carrier using (⟦_⟧F; ⟦μ⟧; sem-cata; sem-fmap; sem-Out; sem-In)
open import Once.Semantics.Value Carrier Carrier using (sem-In-Out; sem-cata-compute)
open import Once.Denotation.Approx using (Ap; approx; approxBlock)
open import Once.Spec.Numerics using (TargetNum)
import Once.Denotation.DenotTrace as DT
open import Once.CCC.Codegen.IRToTrace o using (rec-count)

------------------------------------------------------------------------
-- AN `Id`-FREE FUNCTOR, as evidence over its well-formedness witness (so
-- every induction below takes the functor and its witness apart at once).
------------------------------------------------------------------------
data IdFree : ∀ {F : IRFunctor} → WellFormedFI F → Set where
  idf-K    : ∀ {A} {b : IsBaseTypeI A} → IdFree (wf-K b)
  idf-Sum  : ∀ {F G} {f : WellFormedFI F} {g : WellFormedFI G} → IdFree f → IdFree g → IdFree (wf-Sum f g)
  idf-Prod : ∀ {F G} {f : WellFormedFI F} {g : WellFormedFI G} → IdFree f → IdFree g → IdFree (wf-Prod f g)

private
  ⊔-0 : ∀ m n → m ⊔ n ≡ 0 → (m ≡ 0) × (n ≡ 0)
  ⊔-0 zero    zero    _ = refl , refl
  ⊔-0 zero    (suc n) ()
  ⊔-0 (suc m) zero    ()
  ⊔-0 (suc m) (suc n) ()

  +-0 : ∀ m n → m + n ≡ 0 → (m ≡ 0) × (n ≡ 0)
  +-0 zero    n e = refl , e
  +-0 (suc m) n ()

-- The classifier's `strat-const` (`rec-count ≡ 0`) is exactly that.
idfree-of : ∀ {F} (wf : WellFormedFI F) → rec-count ⌈ F ⌉F ≡ 0 → IdFree wf
idfree-of (wf-K b)      _  = idf-K
idfree-of wf-Id         ()
idfree-of (wf-Sum f g)  e  = idf-Sum  (idfree-of f (proj₁ (⊔-0 _ _ e))) (idfree-of g (proj₂ (⊔-0 _ _ e)))
idfree-of (wf-Prod f g) e  = idf-Prod (idfree-of f (proj₁ (+-0 _ _ e))) (idfree-of g (proj₂ (+-0 _ _ e)))

------------------------------------------------------------------------
-- A LAYER HAS NO CHILDREN: it re-types at any carrier, and sequencing it
-- returns at once.
------------------------------------------------------------------------
rty : ∀ {F} {wf : WellFormedFI F} → IdFree wf → ∀ {X Y : Set} → ⟦ ⌈ F ⌉F ⟧F X → ⟦ ⌈ F ⌉F ⟧F Y
rty idf-K          x        = x
rty (idf-Sum f g)  (inj₁ x) = inj₁ (rty f x)
rty (idf-Sum f g)  (inj₂ y) = inj₂ (rty g y)
rty (idf-Prod f g) (x , y)  = rty f x , rty g y

seq-pure : ∀ {F} {wf : WellFormedFI F} (i : IdFree wf) {X Y : Set} (h : Y → T∞ X) (y : ⟦ ⌈ F ⌉F ⟧F Y)
         → force (seqF∞ ⌈ F ⌉F (sem-fmap ⌈ F ⌉F h y)) ≡ ret (inj₁ (rty i y))
seq-pure idf-K          h y        = refl
seq-pure (idf-Sum f g)  h (inj₁ y) rewrite seq-pure f h y = refl
seq-pure (idf-Sum f g)  h (inj₂ y) rewrite seq-pure g h y = refl
seq-pure (idf-Prod f g) h (x , y)  rewrite seq-pure f h x | seq-pure g h y = refl

------------------------------------------------------------------------
-- THE MEANING: one unfolding of the fold, and the layer's (empty)
-- sequencing, leave the algebra on the input's layer.
------------------------------------------------------------------------
-- the algebra's argument, at the algebra's own carrier `C`
layer-at : ∀ {F} {wf : WellFormedFI F} → IdFree wf → (C : IRTy) → ⟦ μ-type F ⟧ᴰᴵ → ⟦ ⟦ F ⟧TI C ⟧ᴰᴵ
layer-at {F} {wf} i C x =
  subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F C)) (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ C ⌉ (rty i (sem-Out (wf-⌈⌉ wf) x)))

cata-const-meaning : ∀ (fmt : TargetNum) (ρ : DT.CallEnv) {F} (wf : WellFormedFI F) (i : IdFree wf)
                       {E C : IRTy} (alg : IR (E I.* ⟦ F ⟧TI C) C) (e : ⟦ E ⟧ᴰᴵ) (x : ⟦ μ-type F ⟧ᴰᴵ) (k : ℕ)
                   → approx k (DT.evalᴰ fmt ρ (Cata wf alg) (e , x)) ≡ approx k (DT.evalᴰ fmt ρ alg (e , layer-at i C x))
cata-const-meaning fmt ρ {F} wf i {E} {C} alg e x k =
  trans (cong (approx k) unfold)
        (cong (λ t → approxBlock k (bindBlock t kont)) (seq-pure i (sem-cata w algD) (sem-Out w x)))
  where
    w     = wf-⌈⌉ wf
    algD  = DT.cata-ev-algᴰ fmt ρ {F} {E} {C} wf alg e
    kont  = λ layer → DT.evalᴰ fmt ρ alg (e , subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F C)) (coerce-functor⁻¹-D w ⌈ C ⌉ layer))

    unfold : sem-cata w algD x ≡ algD (sem-fmap ⌈ F ⌉F (sem-cata w algD) (sem-Out w x))
    unfold = trans (cong (sem-cata w algD) (sym (sem-In-Out w x))) (sem-cata-compute w algD (sem-Out w x))

------------------------------------------------------------------------
-- THE TYPES AGREE, and so do the coercions along them.
------------------------------------------------------------------------
tyeq : ∀ {F} {wf : WellFormedFI F} → IdFree wf → ∀ (X Y : IRTy) → ⟦ F ⟧TI X ≡ ⟦ F ⟧TI Y
tyeq idf-K          X Y = refl
tyeq (idf-Sum f g)  X Y = cong₂ I._+_ (tyeq f X Y) (tyeq g X Y)
tyeq (idf-Prod f g) X Y = cong₂ I._*_ (tyeq f X Y) (tyeq g X Y)

private
  sD-inl : ∀ {A A′ B B′ : T.Type} (a : A′ ≡ A) (b : B′ ≡ B) (w : ⟦ A ⟧ᴰ)
         → subst ⟦_⟧ᴰ (sym (cong₂ T._+_ a b)) (inj₁ w) ≡ inj₁ (subst ⟦_⟧ᴰ (sym a) w)
  sD-inl refl refl w = refl

  sD-inr : ∀ {A A′ B B′ : T.Type} (a : A′ ≡ A) (b : B′ ≡ B) (w : ⟦ B ⟧ᴰ)
         → subst ⟦_⟧ᴰ (sym (cong₂ T._+_ a b)) (inj₂ w) ≡ inj₂ (subst ⟦_⟧ᴰ (sym b) w)
  sD-inr refl refl w = refl

  sD-pair : ∀ {A A′ B B′ : T.Type} (a : A′ ≡ A) (b : B′ ≡ B) (u : ⟦ A ⟧ᴰ) (v : ⟦ B ⟧ᴰ)
          → subst ⟦_⟧ᴰ (sym (cong₂ T._*_ a b)) (u , v) ≡ (subst ⟦_⟧ᴰ (sym a) u , subst ⟦_⟧ᴰ (sym b) v)
  sD-pair refl refl u v = refl

  sI-inl : ∀ {A A′ B B′ : IRTy} (p : A ≡ A′) (q : B ≡ B′) (w : ⟦ A ⟧ᴰᴵ)
         → subst ⟦_⟧ᴰᴵ (cong₂ I._+_ p q) (inj₁ w) ≡ inj₁ (subst ⟦_⟧ᴰᴵ p w)
  sI-inl refl refl w = refl

  sI-inr : ∀ {A A′ B B′ : IRTy} (p : A ≡ A′) (q : B ≡ B′) (w : ⟦ B ⟧ᴰᴵ)
         → subst ⟦_⟧ᴰᴵ (cong₂ I._+_ p q) (inj₂ w) ≡ inj₂ (subst ⟦_⟧ᴰᴵ q w)
  sI-inr refl refl w = refl

  sI-pair : ∀ {A A′ B B′ : IRTy} (p : A ≡ A′) (q : B ≡ B′) (u : ⟦ A ⟧ᴰᴵ) (v : ⟦ B ⟧ᴰᴵ)
          → subst ⟦_⟧ᴰᴵ (cong₂ I._*_ p q) (u , v) ≡ (subst ⟦_⟧ᴰᴵ p u , subst ⟦_⟧ᴰᴵ q v)
  sI-pair refl refl u v = refl

coh : ∀ {F} {wf : WellFormedFI F} (i : IdFree wf) (X Y : IRTy) (z : ⟦ ⌈ F ⌉F ⟧F ⟦ ⌈ X ⌉ ⟧ᴰ)
    → subst ⟦_⟧ᴰᴵ (tyeq i X Y) (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F X)) (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ X ⌉ z))
      ≡ subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F Y)) (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ Y ⌉ (rty i z))
coh idf-K X Y z = refl
coh {F₁ ⊕ F₂} (idf-Sum f g) X Y (inj₁ z) =
  trans (cong (subst ⟦_⟧ᴰᴵ (tyeq (idf-Sum f g) X Y)) (sD-inl (⌈⟧TI-commute F₁ X) (⌈⟧TI-commute F₂ X) _))
  (trans (sI-inl (tyeq f X Y) (tyeq g X Y) _)
  (trans (cong inj₁ (coh f X Y z))
         (sym (sD-inl (⌈⟧TI-commute F₁ Y) (⌈⟧TI-commute F₂ Y) _))))
coh {F₁ ⊕ F₂} (idf-Sum f g) X Y (inj₂ z) =
  trans (cong (subst ⟦_⟧ᴰᴵ (tyeq (idf-Sum f g) X Y)) (sD-inr (⌈⟧TI-commute F₁ X) (⌈⟧TI-commute F₂ X) _))
  (trans (sI-inr (tyeq f X Y) (tyeq g X Y) _)
  (trans (cong inj₂ (coh g X Y z))
         (sym (sD-inr (⌈⟧TI-commute F₁ Y) (⌈⟧TI-commute F₂ Y) _))))
coh {F₁ ⊗ F₂} (idf-Prod f g) X Y (u , v) =
  trans (cong (subst ⟦_⟧ᴰᴵ (tyeq (idf-Prod f g) X Y)) (sD-pair (⌈⟧TI-commute F₁ X) (⌈⟧TI-commute F₂ X) _ _))
  (trans (sI-pair (tyeq f X Y) (tyeq g X Y) _ _)
  (trans (cong₂ _,_ (coh f X Y u) (coh g X Y v))
         (sym (sD-pair (⌈⟧TI-commute F₁ Y) (⌈⟧TI-commute F₂ Y) _ _))))

------------------------------------------------------------------------
-- THE MACHINE'S LAYER, i.e. `out-μ`'s value on the input (what `μ-layer`
-- hands out), moved along `tyeq`, is the algebra's argument.
------------------------------------------------------------------------
μ-layer-val : ∀ {F} (wf : WellFormedFI F) → ⟦ μ-type F ⟧ᴰᴵ → ⟦ ⟦ F ⟧TI (μ-type F) ⟧ᴰᴵ
μ-layer-val {F} wf x =
  subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F (μ-type F))) (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ μ-type F ⌉ (sem-Out (wf-⌈⌉ wf) x))

layer-retype : ∀ {F} {wf : WellFormedFI F} (i : IdFree wf) (C : IRTy) (x : ⟦ μ-type F ⟧ᴰᴵ)
             → subst ⟦_⟧ᴰᴵ (tyeq i (μ-type F) C) (μ-layer-val wf x) ≡ layer-at i C x
layer-retype {F} {wf} i C x = coh i (μ-type F) C (sem-Out (wf-⌈⌉ wf) x)

-- …so the cata means the algebra on the machine's layer.
cata-const-meaning′ : ∀ (fmt : TargetNum) (ρ : DT.CallEnv) {F} (wf : WellFormedFI F) (i : IdFree wf)
                        {E C : IRTy} (alg : IR (E I.* ⟦ F ⟧TI C) C) (e : ⟦ E ⟧ᴰᴵ) (x : ⟦ μ-type F ⟧ᴰᴵ) (k : ℕ)
                    → approx k (DT.evalᴰ fmt ρ (Cata wf alg) (e , x))
                      ≡ approx k (DT.evalᴰ fmt ρ alg (e , subst ⟦_⟧ᴰᴵ (tyeq i (μ-type F) C) (μ-layer-val wf x)))
cata-const-meaning′ fmt ρ wf i {C = C} alg e x k =
  trans (cata-const-meaning fmt ρ wf i alg e x k)
        (cong (λ z → approx k (DT.evalᴰ fmt ρ alg (e , z))) (sym (layer-retype i C x)))
