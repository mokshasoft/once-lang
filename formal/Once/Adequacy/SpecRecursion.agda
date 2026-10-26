{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecRecursion — the recursion formers: the Spec's fold and
-- unfold against the implementation's (plan 0.122 §5.5 M3).
--
-- A layer crosses between the two domains by the Spec's `toL`/`fromL` and the
-- implementation's first-order coercions (`coerce-functor-D` and the
-- polynomial's): a functor's constants are the same base values. The Spec's
-- fold runs the layer's recursive positions left to right, then the algebra
-- (`foldM`); the implementation folds the children into runs, sequences them
-- left to right (`seqF∞`), then runs the algebra (`cata-ev-algᴰ-D`) — so the
-- two are related by induction on the data, a layer at a time. The unfolds are
-- related coinductively, a forced layer at a time.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Type using (b-*; b-+; b-Float; b-Int; b-Unit; b-Void; wf-⊕; wf-⊗)
open import Once.Spec.Type using (TySub)

module Once.Adequacy.SpecRecursion (Σ : Signature) (σ : TySub 0 0) where

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
import Once.Spec.Signature
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Word using (Carrier)
open import Once.Spec.Grade using (Purity; pure; Finite; fin; pureᶠ; actᶠ; mk-kind; Many; _⊑π_)
open import Once.Spec.Type
  using (Type; Fun; KCtx; WFFun; Base; _⟨_⟩; _⟨_⟩F; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_;
         wf-K; wf-Id; b-var)
import Once.Spec.Type as SpT
open import Once.Internal.FunctorMeaning using (translateF; ⟦_,_⟧-base)
import Once.Internal.Polynomial as LPoly
open import Once.Semantics.Machine using (coerce-μ-in; coerce-μ-out; coerce-full-to-base; coerce-base-to-full)
import Once.Semantics.Machine as Val
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; seqF∞)
import Once.Internal.Iterative as LI
open import Once.Internal.StreamInf using (νᴵ; anaᴵ; anaRun; anaBlock; mapAnaᴵ; anaFᴵ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; forgetᵇ; injectᵇ; coerce-functor-D; coerce-functor⁻¹-D)
open import Once.Denotation.MeaningD using (cata-sem; cata-ev-algᴰ-D)
import Once.Spec.Effect Σ as SE
import Once.Spec.Domain Σ as SD
import Once.Spec.Polynomial as SPoly
open import Once.Denotation.SpecDomain Σ σ using (⟦_⟧ᵛ; M; cata-semᵛ; ana-semᵛ)
open import Once.Adequacy.GradedRelation Σ σ
  using (RelGV; RelGM; RelM; RelM-return; RelM-bind; RelM-fmap; BR; LayerR; μR; inR;
         _∼ᵖᵈ_; _∼ᵈ_)
open _∼ᵖᵈ_ using (force-∼ᵖᵈ)
open _∼ᵈ_ using (force-∼)
open import Once.Adequacy.SpecRun Σ using (fmapʳ-R; RunR; BlockR; ret; call; halt; SumR; left; right)
open RunR using (forceR)

------------------------------------------------------------------------
-- Base values: the same value on both sides
------------------------------------------------------------------------

-- A machine base value and the Spec's.
BV : (A : Type) → SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → Val.⟦ A ⟧ → Set
BV Unit    _ _ = ⊤
BV Void    () _
BV Int     x y = x ≡ y
BV Float   x y = x ≡ y
BV (A * B) (x , x′) (y , y′) = BV A x y × BV B x′ y′
BV (A + B) (inj₁ x) (inj₁ y) = BV A x y
BV (A + B) (inj₂ x) (inj₂ y) = BV B x y
BV (A + B) (inj₁ _) (inj₂ _) = ⊥
BV (A + B) (inj₂ _) (inj₁ _) = ⊥
BV (_ ⇒[ _ ] _) _ _ = ⊤
BV (μ _)   _ _ = ⊤
BV (ν _ _) _ _ = ⊤

module _ {Δ : KCtx 0} where

  -- into a layer: the implementation forgets to the machine value, then to
  -- the polynomial's constant
  base-in : ∀ {A : Type} (ib : Base Δ A) {a b} → RelGV A a b → BR A a (coerce-full-to-base A (forgetᵇ ib b))
  base-in b-Unit r = tt
  base-in b-Void {()}
  base-in b-Int r = r
  base-in b-Float r = r
  base-in (b-* ia ib) {_ , _} {_ , _} (r , s) = base-in ia r , base-in ib s
  base-in (b-+ ia ib) {inj₁ _} {inj₁ _} r = base-in ia r
  base-in (b-+ ia ib) {inj₂ _} {inj₂ _} r = base-in ib r
  base-in (b-var {i = ()} _)

  -- out of a layer, into the machine value
  base-mid : ∀ {A : Type} (ib : Base Δ A) {a y} → BR A a y → BV A a (coerce-base-to-full ib y)
  base-mid b-Unit r = tt
  base-mid b-Void {()}
  base-mid b-Int r = r
  base-mid b-Float r = r
  base-mid (b-* ia ib) {_ , _} {_ , _} (r , s) = base-mid ia r , base-mid ib s
  base-mid (b-+ ia ib) {inj₁ _} {inj₁ _} r = base-mid ia r
  base-mid (b-+ ia ib) {inj₂ _} {inj₂ _} r = base-mid ib r
  base-mid (b-var {i = ()} _)

  -- …and back into the Kleisli domain
  base-out : ∀ {A : Type} (ib : Base Δ A) {a y} → BV A a y → RelGV A a (injectᵇ ib y)
  base-out b-Unit r = tt
  base-out b-Void {()}
  base-out b-Int r = r
  base-out b-Float r = r
  base-out (b-* ia ib) {_ , _} {_ , _} (r , s) = base-out ia r , base-out ib s
  base-out (b-+ ia ib) {inj₁ _} {inj₁ _} r = base-out ia r
  base-out (b-+ ia ib) {inj₂ _} {inj₂ _} r = base-out ib r
  base-out (b-var {i = ()} _)

------------------------------------------------------------------------
-- Layers
------------------------------------------------------------------------

-- A Spec layer against a machine layer (the polynomial's coercion out).
VLayerR : ∀ (H : Fun 0) {X Y : Set} → (X → Y → Set) → SPoly.⟦ SD.code (H ⟨ σ ⟩F) ⟧SF X → Val.⟦ H ⟧F Y → Set
VLayerR (K A)   R x y = BV A x y
VLayerR Id      R x y = R x y
VLayerR (F ⊕ G) R (inj₁ x) (inj₁ y) = VLayerR F R x y
VLayerR (F ⊕ G) R (inj₂ x) (inj₂ y) = VLayerR G R x y
VLayerR (F ⊕ G) R (inj₁ _) (inj₂ _) = ⊥
VLayerR (F ⊕ G) R (inj₂ _) (inj₁ _) = ⊥
VLayerR (F ⊗ G) R (x , x′) (y , y′) = VLayerR F R x y × VLayerR G R x′ y′

module _ {Δ : KCtx 0} where

  -- A value of `⟦ H ⟧F A`, into a layer on both sides.
  toL-rel : ∀ {H : Fun 0} (wf : WFFun Δ H) (A : Type) {l r}
          → RelGV (SpT.⟦ H ⟧F A) l r
          → LayerR H (RelGV A) (SD.toL σ H A l) (coerce-μ-in H ⟦ A ⟧ᴰ (coerce-functor-D wf A r))
  toL-rel (wf-K ib)        A r = base-in ib r
  toL-rel wf-Id            A r = r
  toL-rel (wf-⊕ wf₁ wf₂) A {inj₁ _} {inj₁ _} r = toL-rel wf₁ A r
  toL-rel (wf-⊕ wf₁ wf₂) A {inj₂ _} {inj₂ _} r = toL-rel wf₂ A r
  toL-rel (wf-⊗ wf₁ wf₂) A {_ , _} {_ , _} (r , s) = toL-rel wf₁ A r , toL-rel wf₂ A s

  -- A polynomial layer, out of the layer on both sides.
  outL-rel : ∀ {H : Fun 0} (wf : WFFun Δ H) {X Y : Set} {R : X → Y → Set} {l l′}
           → LayerR H R l l′ → VLayerR H R l (coerce-μ-out wf Y l′)
  outL-rel (wf-K ib)        r = base-mid ib r
  outL-rel wf-Id            r = r
  outL-rel (wf-⊕ wf₁ wf₂) {l = inj₁ _} {inj₁ _} r = outL-rel wf₁ r
  outL-rel (wf-⊕ wf₁ wf₂) {l = inj₂ _} {inj₂ _} r = outL-rel wf₂ r
  outL-rel (wf-⊗ wf₁ wf₂) {l = _ , _} {_ , _} (r , s) = outL-rel wf₁ r , outL-rel wf₂ s

  -- A machine layer, back into a value of `⟦ H ⟧F A` on both sides.
  fromL-rel : ∀ {H : Fun 0} (wf : WFFun Δ H) (A : Type) {l l′}
            → VLayerR H (RelGV A) l l′ → RelGV (SpT.⟦ H ⟧F A) (SD.fromL σ H A l) (coerce-functor⁻¹-D wf A l′)
  fromL-rel (wf-K ib)        A r = base-out ib r
  fromL-rel wf-Id            A r = r
  fromL-rel (wf-⊕ wf₁ wf₂) A {inj₁ _} {inj₁ _} r = fromL-rel wf₁ A r
  fromL-rel (wf-⊕ wf₁ wf₂) A {inj₂ _} {inj₂ _} r = fromL-rel wf₂ A r
  fromL-rel (wf-⊗ wf₁ wf₂) A {_ , _} {_ , _} (r , s) = fromL-rel wf₁ A r , fromL-rel wf₂ A s

------------------------------------------------------------------------
-- THE FOLD BRIDGE: related algebras fold related data to related results.
------------------------------------------------------------------------

module _ {π : Purity} {Δ : KCtx 0} {F : Fun 0} {A : Type} (wfF : WFFun Δ F)
         (alg₁ : ⟦ SpT.⟦ F ⟧F A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg₂ : ⟦ SpT.⟦ F ⟧F A ⟧ᴰ → T∞ ⟦ A ⟧ᴰ)
         (algR : ∀ {x y} → RelGV (SpT.⟦ F ⟧F A) x y → RelGM π A (alg₁ x) (alg₂ y)) where

  private
    G : SPoly.SFunctor
    G = SD.code (F ⟨ σ ⟩F)

    alg : SPoly.⟦ G ⟧SF ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ
    alg l = alg₁ (SD.fromL σ F A l)

    alg′ : SPoly.⟦ translateF Carrier Carrier F ⟧SF (T∞ ⟦ A ⟧ᴰ) → T∞ ⟦ A ⟧ᴰ
    alg′ x = cata-ev-algᴰ-D {F = F} {A = A} wfF alg₂ (coerce-μ-out wfF (T∞ ⟦ A ⟧ᴰ) x)

  fold-R  : ∀ {a b} → μR F a b → RelGM π A (SD.foldM π G alg a) (LPoly.cataS alg′ b)
  layer-R : ∀ {H : Fun 0} (wfH : WFFun Δ H) {x y}
          → LayerR H (μR F) x y
          → RelM π (VLayerR H (RelGV A)) (SD.layerM π G (SD.code (H ⟨ σ ⟩F)) alg x)
                   (seqF∞ H (coerce-μ-out wfH (T∞ ⟦ A ⟧ᴰ) (LPoly.sfmapCata (translateF Carrier Carrier H) alg′ y)))
  fold-R (inR lr) = RelM-bind π (layer-R wfF lr) (λ r → algR (fromL-rel wfF A r))
  layer-R (wf-K ib) lr = RelM-return π (base-mid ib lr)
  layer-R wf-Id     lr = fold-R lr
  layer-R (wf-⊕ wf₁ wf₂) {inj₁ _} {inj₁ _} lr = RelM-fmap π (layer-R wf₁ lr) (λ r → r)
  layer-R (wf-⊕ wf₁ wf₂) {inj₂ _} {inj₂ _} lr = RelM-fmap π (layer-R wf₂ lr) (λ r → r)
  layer-R (wf-⊗ wf₁ wf₂) {_ , _} {_ , _} (lr₁ , lr₂) =
    RelM-bind π (layer-R wf₁ lr₁) λ r₁ → RelM-bind π (layer-R wf₂ lr₂) λ r₂ → RelM-return π (r₁ , r₂)

cata-bridgeᵍ : ∀ {π : Purity} (u : pure ⊑π π) {Δ : KCtx 0} {F : Fun 0} {A : Type} {wfF : WFFun Δ F}
                 (alg₁ : ⟦ SpT.⟦ F ⟧F A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg₂ : ⟦ SpT.⟦ F ⟧F A ⟧ᴰ → T∞ ⟦ A ⟧ᴰ)
             → (∀ {x y} → RelGV (SpT.⟦ F ⟧F A) x y → RelGM π A (alg₁ x) (alg₂ y))
             → ∀ {a b} → RelGV (μ F) a b
             → RelGM π A (cata-semᵛ u wfF alg₁ a) (cata-sem wfF alg₂ b)
cata-bridgeᵍ {π} u {wfF = wfF} alg₁ alg₂ algR r = fold-R {π = π} wfF alg₁ alg₂ algR r

------------------------------------------------------------------------
-- Runs, mapped on one side
------------------------------------------------------------------------

module _ {X X′ Y : Set} {S : X′ → Y → Set} {f : X → X′} where

  -- the Spec's value, mapped
  returnˡ-R : ∀ {x n} → RunR (λ x y → S (f x) y) (SE.return∞ x) n → RunR S (SE.return∞ (f x)) n
  forceR (returnˡ-R r) = go (forceR r)
    where
      go : ∀ {x b} → BlockR (SumR (λ x y → S (f x) y) (RunR (λ x y → S (f x) y))) (SE.roll (SE.done (inj₁ x))) b
         → BlockR (SumR S (RunR S)) (SE.roll (SE.done (inj₁ (f x)))) b
      go (ret (left r)) = ret (left r)

  -- the Spec's block, mapped, embedded
  embedˡ-R  : ∀ t {n} → RunR (λ x y → S (f x) y) (SE.embed t) n → RunR S (SE.embed (SE.mapT f t)) n
  embedBˡ-R : ∀ t {b} → BlockR (SumR (λ x y → S (f x) y) (RunR (λ x y → S (f x) y))) (SE.mapT inj₁ t) b
            → BlockR (SumR S (RunR S)) (SE.mapT inj₁ (SE.mapT f t)) b
  forceR (embedˡ-R t r) = embedBˡ-R t (forceR r)
  embedBˡ-R (SE.roll (SE.done x)) (ret (left r)) = ret (left r)
  embedBˡ-R (SE.roll (SE.node (Once.Spec.Signature.call o a k))) (call c ar kr) = call c ar (λ e → embedBˡ-R (k _) (kr e))
  embedBˡ-R (SE.roll (SE.node (Once.Spec.Signature.call o a k))) (halt x ar)    = halt x ar

------------------------------------------------------------------------
-- THE UNFOLD BRIDGE: related coalgebras unfold related seeds to related
-- streams.
------------------------------------------------------------------------

module _ (F : Fun 0) {X Y : Set} {R : X → Y → Set} where

  private
    G : SPoly.SFunctor
    G = SD.code (F ⟨ σ ⟩F)
    H : SPoly.SFunctor
    H = translateF Carrier Carrier F

  -- A pure Spec unfold: its layer is there at once.
  module _ {c : X → SPoly.⟦ G ⟧SF X} {c₂ : Y → T∞ (SPoly.⟦ H ⟧SF Y)}
           (cr : ∀ {x y} → R x y → RunR (LayerR F R) (SE.return∞ (c x)) (c₂ y)) where
    anaP-∼    : ∀ {a b} → R a b → SE.anaP G c a ∼ᵖᵈ anaᴵ H c₂ b
    anaRunP   : ∀ {l m} → RunR (LayerR F R) (SE.return∞ l) m
              → RunR (LayerR F (_∼ᵖᵈ_ {F})) (SE.return∞ (SE.mapP G G c l)) (anaRun H c₂ m)
    anaBlockP : ∀ {l b} → BlockR (SumR (LayerR F R) (RunR (LayerR F R))) (SE.roll (SE.done (inj₁ l))) b
              → BlockR (SumR (LayerR F (_∼ᵖᵈ_ {F})) (RunR (LayerR F (_∼ᵖᵈ_ {F}))))
                       (SE.roll (SE.done (inj₁ (SE.mapP G G c l)))) (anaBlock H c₂ b)
    mapP-∼    : ∀ (F′ : Fun 0) {x y} → LayerR F′ R x y
              → LayerR F′ (_∼ᵖᵈ_ {F}) (SE.mapP G (SD.code (F′ ⟨ σ ⟩F)) c x) (mapAnaᴵ H (translateF Carrier Carrier F′) c₂ y)
    force-∼ᵖᵈ (anaP-∼ r) = anaRunP (cr r)
    forceR (anaRunP h) = anaBlockP (forceR h)
    anaBlockP (ret (left lr)) = ret (left (mapP-∼ F lr))
    mapP-∼ (K A)     r = r
    mapP-∼ Id        r = anaP-∼ r
    mapP-∼ (F₁ ⊕ F₂) {inj₁ _} {inj₁ _} r = mapP-∼ F₁ r
    mapP-∼ (F₁ ⊕ F₂) {inj₂ _} {inj₂ _} r = mapP-∼ F₂ r
    mapP-∼ (F₁ ⊗ F₂) {_ , _} {_ , _} (r₁ , r₂) = mapP-∼ F₁ r₁ , mapP-∼ F₂ r₂

  -- An `act` Spec unfold: its layer is a finite block, embedded.
  module _ {c : X → SE.T (SPoly.⟦ G ⟧SF X)} {c₂ : Y → T∞ (SPoly.⟦ H ⟧SF Y)}
           (cr : ∀ {x y} → R x y → RunR (LayerR F R) (SE.embed (c x)) (c₂ y)) where
    anaA-∼    : ∀ {a b} → R a b → SE.anaA G c a ∼ᵈ anaᴵ H c₂ b
    anaRunA   : ∀ t {m} → RunR (LayerR F R) (SE.embed t) m
              → RunR (LayerR F (_∼ᵈ_ {F})) (SE.embed (SE.treeA G c t)) (anaRun H c₂ m)
    anaBlockA : ∀ t {b} → BlockR (SumR (LayerR F R) (RunR (LayerR F R))) (SE.mapT inj₁ t) b
              → BlockR (SumR (LayerR F (_∼ᵈ_ {F})) (RunR (LayerR F (_∼ᵈ_ {F}))))
                       (SE.mapT inj₁ (SE.treeA G c t)) (anaBlock H c₂ b)
    mapA-∼    : ∀ (F′ : Fun 0) {x y} → LayerR F′ R x y
              → LayerR F′ (_∼ᵈ_ {F}) (SE.mapA G (SD.code (F′ ⟨ σ ⟩F)) c x) (mapAnaᴵ H (translateF Carrier Carrier F′) c₂ y)
    force-∼ (anaA-∼ {a} r) = anaRunA (c a) (cr r)
    forceR (anaRunA t h) = anaBlockA t (forceR h)
    anaBlockA (SE.roll (SE.done l)) (ret (left lr)) = ret (left (mapA-∼ F lr))
    anaBlockA (SE.roll (SE.node (Once.Spec.Signature.call o a k))) (call cc ar kr) = call cc ar (λ e → anaBlockA (k _) (kr e))
    anaBlockA (SE.roll (SE.node (Once.Spec.Signature.call o a k))) (halt h ar)    = halt h ar
    mapA-∼ (K A)     r = r
    mapA-∼ Id        r = anaA-∼ r
    mapA-∼ (F₁ ⊕ F₂) {inj₁ _} {inj₁ _} r = mapA-∼ F₁ r
    mapA-∼ (F₁ ⊕ F₂) {inj₂ _} {inj₂ _} r = mapA-∼ F₂ r
    mapA-∼ (F₁ ⊗ F₂) {_ , _} {_ , _} (r₁ , r₂) = mapA-∼ F₁ r₁ , mapA-∼ F₂ r₂

-- A layer value run on both sides, crossed into the layer.
private
  Cross : ∀ (F : Fun 0) (A : Type) → ⟦ SpT.⟦ F ⟧F A ⟧ᵛ → Val.⟦ F ⟧F ⟦ A ⟧ᴰ → Set
  Cross F A z w = LayerR F (RelGV A) (SD.toL σ F A z) (coerce-μ-in F ⟦ A ⟧ᴰ w)

ana-bridgeᵍ : ∀ (φ : Finite) {Δ : KCtx 0} {A : Type} {F : Fun 0} (wfF : WFFun Δ F)
                (c₁ : ⟦ A ⇒[ mk-kind Many (fin φ) ] SpT.⟦ F ⟧F A ⟧ᵛ) (c₂ : ⟦ A ⇒[ mk-kind Many (fin φ) ] SpT.⟦ F ⟧F A ⟧ᴰ)
            → RelGV (A ⇒[ mk-kind Many (fin φ) ] SpT.⟦ F ⟧F A) c₁ c₂
            → ∀ {a b} → RelGV A a b
            → RelGV (ν F φ) (ana-semᵛ φ wfF c₁ a) (anaFᴵ F (λ a′ → fmap∞ (coerce-functor-D wfF A) (c₂ a′)) b)
ana-bridgeᵍ pureᶠ {A = A} {F = F} wfF c₁ c₂ (rc , _) rab = anaP-∼ F cr rab
  where
    cr : ∀ {x y} → RelGV A x y → RunR (LayerR F (RelGV A)) (SE.return∞ (SD.toL σ F A (c₁ x)))
                                       (fmap∞ (coerce-μ-in F ⟦ A ⟧ᴰ) (fmap∞ (coerce-functor-D wfF A) (c₂ y)))
    cr r = returnˡ-R {S = LayerR F (RelGV A)} {f = SD.toL σ F A}
             (fmapʳ-R {R = Cross F A} {S = λ z w′ → LayerR F (RelGV A) (SD.toL σ F A z) w′} (λ s → s)
               (fmapʳ-R {R = RelGV (SpT.⟦ F ⟧F A)} {S = Cross F A} (λ rv → toL-rel wfF A rv) (rc r)))
ana-bridgeᵍ actᶠ {A = A} {F = F} wfF c₁ c₂ (rc , _) rab = anaA-∼ F cr rab
  where
    cr : ∀ {x y} → RelGV A x y → RunR (LayerR F (RelGV A)) (SE.embed (SE.mapT (SD.toL σ F A) (c₁ x)))
                                       (fmap∞ (coerce-μ-in F ⟦ A ⟧ᴰ) (fmap∞ (coerce-functor-D wfF A) (c₂ y)))
    cr {x} r = embedˡ-R {S = LayerR F (RelGV A)} {f = SD.toL σ F A} (c₁ x)
             (fmapʳ-R {R = Cross F A} {S = λ z w′ → LayerR F (RelGV A) (SD.toL σ F A z) w′} (λ s → s)
               (fmapʳ-R {R = RelGV (SpT.⟦ F ⟧F A)} {S = Cross F A} (λ rv → toL-rel wfF A rv) (rc r)))
