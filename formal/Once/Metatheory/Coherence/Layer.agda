{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Layer — each semantic operation of the core
-- meaning (`Spec.Core.Meaning`) maps related inputs to related outputs.
--
-- `Rel π π′ A m m′`: two computations, at two grades, whose runs are related
-- with returned values the same at `A`. The fundamental lemma is a
-- composition of these congruences, one per former; the loop's is in
-- `Coherence.Loop`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.Layer (Σ : Signature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Grade using (Purity; pure; act; eff; mk-kind; Zero; One; Many; _·p_; _⊑π_)
open import Once.Spec.Type
  using (Ty; Type; Fun; KCtx; ∅ₖ; TySub; Respects; Base; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; base-⟨⟩;
         WFFun; wf-K; wf-Id; wf-⊕; wf-⊗; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_;
         ⟦_⟧F; _⟨_⟩; _⟨_⟩F)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; code; toL; fromL; foldM; layerM; anaM)
open import Once.Spec.Observation Σ using (Interp)
open import Once.Spec.Equivalence Σ
open import Once.Metatheory.Bisim Σ using (≈-refl)
open import Once.Metatheory.Erase Σ
open import Once.Metatheory.Unfold Σ using (module Unfold)
open import Once.Metatheory.Coherence.Relation Σ

open T∞ using (force)
open νM using (outν)

------------------------------------------------------------------------
-- Related computations
------------------------------------------------------------------------

record Rel π π′ (A : Type) (m : M π ⟦ A ⟧ᵛ) (m′ : M π′ ⟦ A ⟧ᵛ) : Set where
  constructor rel
  field runs : Related (Same A) (toT∞ π m) (toT∞ π′ m′)
open Rel public

relPure : ∀ {A : Type} {x x′} → Same A x x′ → Rel pure pure A x x′
relPure s = rel (returnRel s)

-- A pure computation's value is observed by running it somewhere.
relPure⁻ : ∀ {A : Type} {x x′} → Interp → Rel pure pure A x x′ → Same A x x′
relPure⁻ ι p = returnRel⁻ ι (runs p)

relSubˡ : ∀ {π₀ π π′} (g : π ⊑π π₀) {A : Type} {m m′} → Rel π π′ A m m′ → Rel π₀ π′ A (sub g m) m′
relSubˡ g {m = m} p = rel (≈-Relatedˡ (toT∞-sub g m) (runs p))

relSubʳ : ∀ {π π₀ π′} (g : π′ ⊑π π₀) {A : Type} {m m′} → Rel π π′ A m m′ → Rel π π₀ A m (sub g m′)
relSubʳ g {m′ = m′} p = rel (≈-Relatedʳ (toT∞-sub g m′) (runs p))

relBindᵍ : ∀ {π₁ π₂ π₁′ π₂′} {A B : Type} {m m′} {k : ⟦ A ⟧ᵛ → M π₂ ⟦ B ⟧ᵛ} {k′ : ⟦ A ⟧ᵛ → M π₂′ ⟦ B ⟧ᵛ}
         → Rel π₁ π₁′ A m m′ → (∀ {x x′} → Same A x x′ → Rel π₂ π₂′ B (k x) (k′ x′))
         → Rel (π₁ ·p π₂) (π₁′ ·p π₂′) B (bindᵍ π₁ π₂ m k) (bindᵍ π₁′ π₂′ m′ k′)
relBindᵍ {π₁} {π₂} {π₁′} {π₂′} {m = m} {m′} {k} {k′} p h =
  rel (≈-Relatedˡ (toT∞-bindᵍ π₁ π₂ m k) (≈-Relatedʳ (toT∞-bindᵍ π₁′ π₂′ m′ k′) (bindRel (runs p) λ s → runs (h s))))

relBind : ∀ {π π′} {A B : Type} {m m′} {k : ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ} {k′ : ⟦ A ⟧ᵛ → M π′ ⟦ B ⟧ᵛ}
        → Rel π π′ A m m′ → (∀ {x x′} → Same A x x′ → Rel π π′ B (k x) (k′ x′))
        → Rel π π′ B (bind π m k) (bind π′ m′ k′)
relBind {π} {π′} {m = m} {m′} {k} {k′} p h =
  rel (≈-Relatedˡ (toT∞-bind π m k) (≈-Relatedʳ (toT∞-bind π′ m′ k′) (bindRel (runs p) λ s → runs (h s))))

relFmap : ∀ {π π′} {A B : Type} {m m′} {f f′ : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ}
        → Rel π π′ A m m′ → (∀ {x x′} → Same A x x′ → Same B (f x) (f′ x′))
        → Rel π π′ B (fmap π f m) (fmap π′ f′ m′)
relFmap {π} {π′} {m = m} {m′} {f} {f′} p h =
  rel (≈-Relatedˡ (toT∞-fmap π f m) (≈-Relatedʳ (toT∞-fmap π′ f′ m′) (bindRel (runs p) λ s → returnRel (h s))))

-- Related computations mapped by functions that relate values to a new relation.
relatedFmap : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {t t′ : T∞ X} {f f′ : X → Y}
            → Related R t t′ → (∀ {x x′} → R x x′ → R′ (f x) (f′ x′))
            → Related R′ (t >>=∞ λ x → return∞ (f x)) (t′ >>=∞ λ x → return∞ (f′ x))
relatedFmap p h = bindRel p λ r → returnRel (h r)

------------------------------------------------------------------------
-- Functions
------------------------------------------------------------------------

-- Applying the same functions to the same arguments.
appZero : ∀ {π} {A B : Type} {f f′ : ⟦ A ⇒[ mk-kind Zero π ] B ⟧ᵛ} → Same (A ⇒[ mk-kind Zero π ] B) f f′
        → Rel π π B (f tt) (f′ tt)
appZero s = rel (fromUpTo s)

appOne : ∀ {π} {A B : Type} {f f′ : ⟦ A ⇒[ mk-kind One π ] B ⟧ᵛ} → Same (A ⇒[ mk-kind One π ] B) f f′
       → ∀ {a a′} → Same A a a′ → Rel π π B (f a) (f′ a′)
appOne s sa = rel (fromUpTo (s _ _ sa))

appMany : ∀ {π} {A B : Type} {f f′ : ⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ} → Same (A ⇒[ mk-kind Many π ] B) f f′
        → ∀ {a a′} → Same A a a′ → Rel π π B (f a) (f′ a′)
appMany s sa = rel (fromUpTo (s _ _ sa))

-- A function whose results are related on related arguments.
lamZero : ∀ {π} {A B : Type} {f f′ : ⟦ A ⇒[ mk-kind Zero π ] B ⟧ᵛ} → Rel π π B (f tt) (f′ tt)
        → Same (A ⇒[ mk-kind Zero π ] B) f f′
lamZero p = toUpTo (runs p)

lamOne : ∀ {π} {A B : Type} {f f′ : ⟦ A ⇒[ mk-kind One π ] B ⟧ᵛ}
       → (∀ {a a′} → Same A a a′ → Rel π π B (f a) (f′ a′)) → Same (A ⇒[ mk-kind One π ] B) f f′
lamOne h a a′ sa = toUpTo (runs (h sa))

lamMany : ∀ {π} {A B : Type} {f f′ : ⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ}
        → (∀ {a a′} → Same A a a′ → Rel π π B (f a) (f′ a′)) → Same (A ⇒[ mk-kind Many π ] B) f f′
lamMany h a a′ sa = toUpTo (runs (h sa))

------------------------------------------------------------------------
-- Data
------------------------------------------------------------------------

samePair : ∀ {A B : Type} {a a′ b b′} → Same A a a′ → Same B b b′ → Same (A * B) (a , b) (a′ , b′)
samePair sa sb = sa , sb

sameFst : ∀ {A B : Type} {p p′} → Same (A * B) p p′ → Same A (proj₁ p) (proj₁ p′)
sameFst s = proj₁ s

sameSnd : ∀ {A B : Type} {p p′} → Same (A * B) p p′ → Same B (proj₂ p) (proj₂ p′)
sameSnd s = proj₂ s

sameInl : ∀ {A B : Type} {a a′} → Same A a a′ → Same (A + B) (inj₁ a) (inj₁ a′)
sameInl s = s

sameInr : ∀ {A B : Type} {b b′} → Same B b b′ → Same (A + B) (inj₂ b) (inj₂ b′)
sameInr s = s

-- The two values of a sum agree in their summand.
sameSum : ∀ {A B : Type} {C : Set} (u u′ : ⟦ A + B ⟧ᵛ) → Same (A + B) u u′
        → (∀ a a′ → Same A a a′ → u ≡ inj₁ a → u′ ≡ inj₁ a′ → C)
        → (∀ b b′ → Same B b b′ → u ≡ inj₂ b → u′ ≡ inj₂ b′ → C) → C
sameSum (inj₁ a) (inj₁ a′) s l r = l a a′ s refl refl
sameSum (inj₂ b) (inj₂ b′) s l r = r b b′ s refl refl
sameSum (inj₁ a) (inj₂ b′) () l r
sameSum (inj₂ b) (inj₁ a′) () l r

-- Base values are the same exactly when they are equal.
sameBase : ∀ {A : Type} → Base ∅ₖ A → ∀ {x y} → Same A x y → x ≡ y
sameBase (b-var {()} _)
sameBase b-Unit s = refl
sameBase b-Void {()}
sameBase b-Int   s = s
sameBase b-Float s = s
sameBase (b-* a b) {x₁ , x₂} {y₁ , y₂} (s , t) = cong₂ _,_ (sameBase a s) (sameBase b t)
sameBase (b-+ a b) {inj₁ x} {inj₁ y} s = cong inj₁ (sameBase a s)
sameBase (b-+ a b) {inj₂ x} {inj₂ y} s = cong inj₂ (sameBase b s)
sameBase (b-+ a b) {inj₁ x} {inj₂ y} ()
sameBase (b-+ a b) {inj₂ x} {inj₁ y} ()

reflBase : ∀ {A : Type} → Base ∅ₖ A → ∀ x → Same A x x
reflBase (b-var {()} _)
reflBase b-Unit  x = tt
reflBase b-Void  ()
reflBase b-Int   x = refl
reflBase b-Float x = refl
reflBase (b-* a b) (x , y) = reflBase a x , reflBase b y
reflBase (b-+ a b) (inj₁ x) = reflBase a x
reflBase (b-+ a b) (inj₂ y) = reflBase b y

-- A μ value is the same only as itself.
sameμ : ∀ {F} {x y : ⟦ μ F ⟧ᵛ} → Same (μ F) x y → x ≡ y
sameμ s = s

------------------------------------------------------------------------
-- Layers
------------------------------------------------------------------------

LayerEq-map : ∀ (G : SFunctor) {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {f f′ : X → Y}
            → (∀ {x y} → R x y → R′ (f x) (f′ y)) → ∀ {l l′} → LayerEq G R l l′ → LayerEq G R′ (sfmap G f l) (sfmap G f′ l′)
LayerEq-map (SK B)   h p = p
LayerEq-map SId      h p = h p
LayerEq-map (G S⊕ H) h {inj₁ x} {inj₁ y} p = LayerEq-map G h p
LayerEq-map (G S⊕ H) h {inj₂ x} {inj₂ y} p = LayerEq-map H h p
LayerEq-map (G S⊕ H) h {inj₁ x} {inj₂ y} ()
LayerEq-map (G S⊕ H) h {inj₂ x} {inj₁ y} ()
LayerEq-map (G S⊗ H) h (p , q) = LayerEq-map G h p , LayerEq-map H h q

LayerEq-∀ : ∀ (G : SFunctor) {X} {R : ℕ → X → X → Set} {l l′}
          → (∀ n → LayerEq G (R n) l l′) → LayerEq G (λ x y → ∀ n → R n x y) l l′
LayerEq-∀ (SK B)   h = h 0
LayerEq-∀ SId      h = h
LayerEq-∀ (G S⊕ H) {l = inj₁ x} {inj₁ y} h = LayerEq-∀ G h
LayerEq-∀ (G S⊕ H) {l = inj₂ x} {inj₂ y} h = LayerEq-∀ H h
LayerEq-∀ (G S⊕ H) {l = inj₁ x} {inj₂ y} h = ⊥-elim (h 0)
LayerEq-∀ (G S⊕ H) {l = inj₂ x} {inj₁ y} h = ⊥-elim (h 0)
LayerEq-∀ (G S⊗ H) h = LayerEq-∀ G (λ n → proj₁ (h n)) , LayerEq-∀ H (λ n → proj₂ (h n))

LayerEq-≡ : ∀ (G : SFunctor) {X} {l l′ : ⟦ G ⟧SF X} → LayerEq G _≡_ l l′ → l ≡ l′
LayerEq-≡ (SK B)   p = p
LayerEq-≡ SId      p = p
LayerEq-≡ (G S⊕ H) {l = inj₁ x} {inj₁ y} p = cong inj₁ (LayerEq-≡ G p)
LayerEq-≡ (G S⊕ H) {l = inj₂ x} {inj₂ y} p = cong inj₂ (LayerEq-≡ H p)
LayerEq-≡ (G S⊕ H) {l = inj₁ x} {inj₂ y} ()
LayerEq-≡ (G S⊕ H) {l = inj₂ x} {inj₁ y} ()
LayerEq-≡ (G S⊗ H) (p , q) = cong₂ _,_ (LayerEq-≡ G p) (LayerEq-≡ H q)

module Functor {m} {Δ : KCtx m} (σ : TySub m 0) (r : Respects Δ ∅ₖ σ) where

  toL-same : ∀ {F} (wf : WFFun Δ F) (X : Ty m) {l l′}
           → Same ((⟦ F ⟧F X) ⟨ σ ⟩) l l′ → LayerEq (code (F ⟨ σ ⟩F)) (Same (X ⟨ σ ⟩)) (toL σ F X l) (toL σ F X l′)
  toL-same (wf-K b) X s = sameBase (base-⟨⟩ r b) s
  toL-same wf-Id    X s = s
  toL-same (wf-⊕ f g) X {inj₁ x} {inj₁ y} s = toL-same f X s
  toL-same (wf-⊕ f g) X {inj₂ x} {inj₂ y} s = toL-same g X s
  toL-same (wf-⊕ f g) X {inj₁ x} {inj₂ y} ()
  toL-same (wf-⊕ f g) X {inj₂ x} {inj₁ y} ()
  toL-same (wf-⊗ f g) X (s , t) = toL-same f X s , toL-same g X t

  fromL-same : ∀ {F} (wf : WFFun Δ F) (X : Ty m) {l l′}
             → LayerEq (code (F ⟨ σ ⟩F)) (Same (X ⟨ σ ⟩)) l l′ → Same ((⟦ F ⟧F X) ⟨ σ ⟩) (fromL σ F X l) (fromL σ F X l′)
  fromL-same (wf-K b) X {l} refl = reflBase (base-⟨⟩ r b) l
  fromL-same wf-Id    X p = p
  fromL-same (wf-⊕ f g) X {inj₁ x} {inj₁ y} p = fromL-same f X p
  fromL-same (wf-⊕ f g) X {inj₂ x} {inj₂ y} p = fromL-same g X p
  fromL-same (wf-⊕ f g) X {inj₁ x} {inj₂ y} ()
  fromL-same (wf-⊕ f g) X {inj₂ x} {inj₁ y} ()
  fromL-same (wf-⊗ f g) X (p , q) = fromL-same f X p , fromL-same g X q

  -- Rolling the same layers gives the same tree.
  roll-same : ∀ {F} (wf : WFFun Δ F) {l l′}
            → Same ((⟦ F ⟧F (μ F)) ⟨ σ ⟩) l l′ → inS (toL σ F (μ F) l) ≡ inS (toL σ F (μ F) l′)
  roll-same {F} wf s = cong (inS {F = code (F ⟨ σ ⟩F)}) (LayerEq-≡ (code (F ⟨ σ ⟩F)) (LayerEq-mono (code (F ⟨ σ ⟩F)) sameμ (toL-same wf (μ F) s)))

------------------------------------------------------------------------
-- The fold
------------------------------------------------------------------------

module Fold (π : Purity) (G : SFunctor) (A : Type)
            (alg alg′ : ⟦ G ⟧SF ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ)
            (h : ∀ {l l′} → LayerEq G (Same A) l l′ → Rel π π A (alg l) (alg′ l′)) where
  foldRel  : ∀ v → Rel π π A (foldM π G alg v) (foldM π G alg′ v)
  layerRel : ∀ H (x : ⟦ H ⟧SF (μS G))
           → Related (LayerEq H (Same A)) (toT∞ π (layerM π G H alg x)) (toT∞ π (layerM π G H alg′ x))
  foldRel (inS x) =
    rel (≈-Relatedˡ (toT∞-bind π (layerM π G G alg x) alg)
          (≈-Relatedʳ (toT∞-bind π (layerM π G G alg′ x) alg′) (bindRel (layerRel G x) λ le → runs (h le))))
  layerRel (SK B) x =
    ≈-Relatedˡ (toT∞-return π x) (≈-Relatedʳ (toT∞-return π x) (returnRel refl))
  layerRel SId x = runs (foldRel x)
  layerRel (H₁ S⊕ H₂) (inj₁ x) =
    ≈-Relatedˡ (toT∞-fmap π inj₁ (layerM π G H₁ alg x))
      (≈-Relatedʳ (toT∞-fmap π inj₁ (layerM π G H₁ alg′ x)) (relatedFmap (layerRel H₁ x) λ p → p))
  layerRel (H₁ S⊕ H₂) (inj₂ y) =
    ≈-Relatedˡ (toT∞-fmap π inj₂ (layerM π G H₂ alg y))
      (≈-Relatedʳ (toT∞-fmap π inj₂ (layerM π G H₂ alg′ y)) (relatedFmap (layerRel H₂ y) λ p → p))
  layerRel (H₁ S⊗ H₂) (x , y) =
    ≈-Relatedˡ (toT∞-bind π (layerM π G H₁ alg x) _)
      (≈-Relatedʳ (toT∞-bind π (layerM π G H₁ alg′ x) _)
        (bindRel (layerRel H₁ x) λ {u} {u′} p →
          ≈-Relatedˡ (toT∞-bind π (layerM π G H₂ alg y) _)
            (≈-Relatedʳ (toT∞-bind π (layerM π G H₂ alg′ y) _)
              (bindRel (layerRel H₂ y) λ {v} {v′} q →
                ≈-Relatedˡ (toT∞-return π (u , v)) (≈-Relatedʳ (toT∞-return π (u′ , v′)) (returnRel (p , q)))))))

------------------------------------------------------------------------
-- The unfold, and forcing it
------------------------------------------------------------------------

module Ana (π : Purity) (g : π ⊑π act) (G : SFunctor) (A : Type) (c c′ : ⟦ A ⟧ᵛ → M π (⟦ G ⟧SF ⟦ A ⟧ᵛ))
           (h : ∀ {a a′} → Same A a a′ → Related (LayerEq G (Same A)) (toT∞ π (c a)) (toT∞ π (c′ a′))) where
  open Unfold G using (unfold-out≈)

  anaRel : ∀ n {a a′} → Same A a a′ → νUpTo π G n (anaM g G c a) (anaM g G c′ a′)
  anaRel zero    s = tt
  anaRel (suc n) {a} {a′} s =
    toUpTo (≈-Relatedˡ (unfold-out≈ g c a) (≈-Relatedʳ (unfold-out≈ g c′ a′)
             (≈-Relatedˡ (toT∞-fmap π (sfmap G (anaM g G c)) (c a))
               (≈-Relatedʳ (toT∞-fmap π (sfmap G (anaM g G c′)) (c′ a′))
                 (relatedFmap (h s) (LayerEq-map G (anaRel n)))))))

-- Forcing the same codata gives the same layer computations.
outRel : ∀ π (G : SFunctor) {v v′ : νM π G} → (∀ n → νUpTo π G n v v′)
       → Related (λ l l′ → ∀ n → LayerEq G (νUpTo π G n) l l′) (toT∞ π (outν v)) (toT∞ π (outν v′))
outRel π G s = Related-∀ λ n → fromUpTo (s (suc n))
