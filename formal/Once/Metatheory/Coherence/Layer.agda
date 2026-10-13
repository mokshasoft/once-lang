-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Layer — the semantic operations respect the
-- relation (plan 0.116 D1c): functor layers, `μ` (roll, fold), `ν` (unfold,
-- out) and the subtyping coercions.
--
-- A layer is related position-wise (`LiftF` on `⟦ F ⟧F`, the Spec's `LayerEq`
-- on `⟦ H ⟧SF`): constants equal, recursive positions related. The
-- conversions between the two (`cfᵛ`, `coerce-ν-in`, …) and the graded
-- sequencing (`seqM`) carry related layers to related layers; the fold is
-- related by induction on the `μ` value, the unfold to every depth by
-- induction on the depth.
------------------------------------------------------------------------

module Once.Metatheory.Coherence.Layer where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst₂)

open import Once.Spec.Type.Grade using (Purity; pure; eff⁺; eff; prod; mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid;
  Functor; K; Id; _⊕_; _⊗_; ⟦_⟧T)
open import Once.Spec.Type.WellFormed using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid;
  WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Spec.Type.Sub using (_<:_; sub-void; sub-unit; sub-int; sub-float; sub-arr; sub-prod; sub-sum; sub-μ; sub-ν; sub-rigid;
  _⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-prod; ⊑-pp; ⊑-ep; ⊑-g; ⊑-ge; ⊑-gp)
open import Once.Spec.Equivalence using (TreeEq; ret≈; call≈; halt≈; LayerEq; νᵖ-upto; νᵈ-upto; ν∞-upto; ν⁺-upto; Same; TreeEqN)
open import Once.Spec.Guarded using (T⁺; forget⁺; fmap⁺; ν⁺; ana⁺; anaRoot⁺; anaTree⁺; mapAna⁺; call⁺; halt⁺; iter∞; iterRoot∞; iterTree∞)
import Data.Sum
open Once.Spec.Guarded.ν⁺ using (force⁺)
open import Once.Denotation.GuardedLaws using (forget-bind⁺; forget-anaRoot)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; ⟨_⟩; sfmapCata)
open import Once.Spec.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
import Once.Semantics.Machine as Val
open import Once.Denotation.TraceMonad using (T; ret; call; halt; _>>=T_; fmapT)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; toT∞; bindM; returnM; subM; νᵖ; module νᵖ)
open import Once.Denotation.ValueDomain using (νᵈ; module νᵈ; anaᵈ; anaTree; mapAnaᵈ; seqF)
open import Once.Denotation.GradedOps using (fmapM; injB; prjB; cfᵛ; cf⁻¹ᵛ; seqM; cata-semᵛ; anaᵖ; mapAnaᵖ;
  embν; mapEmbν; ana-semᵛ; out-semᵛ; ⟦_⟧<:ᵛ; embν∞ᵈ; embLay∞; mapEmbν∞ᵈ; embν∞ᵖ; mapEmbν∞ᵖ;
  embν⁺ᵈ; embRoot⁺; embTree⁺; mapEmbν⁺ᵈ)
open import Once.Spec.Iterative
  using (T∞; T∞F; ret∞; call∞; halt∞; return∞; _>>=∞_; fmap∞; seqF∞; embed; TreeEq∞; NodeEq; ret≈∞; call≈∞; halt≈∞;
         ν∞; ana∞; anaTree∞; anaLayer∞; mapAna∞)
open Once.Spec.Iterative.T∞ using (force)
open Once.Spec.Iterative.TreeEq∞ using (force≈)
open Once.Spec.Iterative.ν∞ using (force∞)
open import Once.Denotation.TraceMonadInfLaws using (≈∞-bind; ≈∞-rewrite; ≈∞-map; embed-≈; embed-bind)
open import Once.Metatheory.Coherence.Relation using (S; SM; TreeEq-map; TreeEq-bind; ∀-TreeEq;
  ≈refl; retT≈; toT∞-bindM; toT∞-returnM; toT∞-subM; LayerEq-map; TreeEqN-mono; module Depth; ν∞-mono)
open νᵖ using (forceᵖ)
open νᵈ using (forceᵈ)

------------------------------------------------------------------------
-- Base values: the relation is equality
------------------------------------------------------------------------

S-base-≡ : ∀ {A} → IsBaseType A → ∀ {x y} → S A x y → x ≡ y
S-base-≡ base-Unit  s = refl
S-base-≡ base-Void  {()} s
S-base-≡ base-Int   s = s
S-base-≡ base-Float s = s
S-base-≡ (base-Prod a b) {x , y} {x′ , y′} (sa , sb) = cong₂ _,_ (S-base-≡ a sa) (S-base-≡ b sb)
S-base-≡ (base-Sum a b) {inj₁ x} {inj₁ x′} s = cong inj₁ (S-base-≡ a s)
S-base-≡ (base-Sum a b) {inj₂ y} {inj₂ y′} s = cong inj₂ (S-base-≡ b s)
S-base-≡ (base-Sum a b) {inj₁ _} {inj₂ _} ()
S-base-≡ (base-Sum a b) {inj₂ _} {inj₁ _} ()
S-base-≡ base-rigid {()} s

S-refl-base : ∀ {A} → IsBaseType A → ∀ x → S A x x
S-refl-base base-Unit  x = tt
S-refl-base base-Void  ()
S-refl-base base-Int   x = refl
S-refl-base base-Float x = refl
S-refl-base (base-Prod a b) (x , y) = S-refl-base a x , S-refl-base b y
S-refl-base (base-Sum a b) (inj₁ x) = S-refl-base a x
S-refl-base (base-Sum a b) (inj₂ y) = S-refl-base b y
S-refl-base base-rigid ()

S-base : ∀ {A} → IsBaseType A → ∀ {x y} → x ≡ y → S A x y
S-base ib {x} refl = S-refl-base ib x

-- A tree whose leaves are each related to themselves.
TreeEq-refl : ∀ {X} {R : X → X → Set} → (∀ x → R x x) → ∀ m → TreeEq R m m
TreeEq-refl r (ret x)      = ret≈ (r x)
TreeEq-refl r (call o a k) = call≈ (λ b → TreeEq-refl r (k b))
TreeEq-refl r (halt o a)   = halt≈

------------------------------------------------------------------------
-- Layers
------------------------------------------------------------------------

-- `⟦ F ⟧F` layers, position-wise.
LiftF : ∀ (F : Functor) {X : Set} → (X → X → Set) → Val.⟦ F ⟧F X → Val.⟦ F ⟧F X → Set
LiftF (K B)   R x y = x ≡ y
LiftF Id      R x y = R x y
LiftF (F ⊕ G) R (inj₁ x) (inj₁ y) = LiftF F R x y
LiftF (F ⊕ G) R (inj₂ x) (inj₂ y) = LiftF G R x y
LiftF (F ⊕ G) R (inj₁ _) (inj₂ _) = ⊥
LiftF (F ⊕ G) R (inj₂ _) (inj₁ _) = ⊥
LiftF (F ⊗ G) R (x , x′) (y , y′) = LiftF F R x y × LiftF G R x′ y′

LiftF-map : ∀ (F : Functor) {X} {R R′ : X → X → Set} → (∀ {a b} → R a b → R′ a b)
          → ∀ {x y} → LiftF F R x y → LiftF F R′ x y
LiftF-map (K B)   f e = e
LiftF-map Id      f r = f r
LiftF-map (F ⊕ G) f {inj₁ x} {inj₁ y} r = LiftF-map F f r
LiftF-map (F ⊕ G) f {inj₂ x} {inj₂ y} r = LiftF-map G f r
LiftF-map (F ⊕ G) f {inj₁ _} {inj₂ _} ()
LiftF-map (F ⊕ G) f {inj₂ _} {inj₁ _} ()
LiftF-map (F ⊗ G) f (r , r′) = LiftF-map F f r , LiftF-map G f r′

-- Every depth, outside, is every depth, inside: a layer is finite.
∀-LayerEq : ∀ (G : SFunctor) {X} {R : ℕ → X → X → Set} {x y}
          → (∀ n → LayerEq G (R n) x y) → LayerEq G (λ a b → ∀ n → R n a b) x y
∀-LayerEq (SK B)   h = h zero
∀-LayerEq SId      h = h
∀-LayerEq (G S⊕ H) {x = inj₁ x} {inj₁ y} h = ∀-LayerEq G h
∀-LayerEq (G S⊕ H) {x = inj₂ x} {inj₂ y} h = ∀-LayerEq H h
∀-LayerEq (G S⊕ H) {x = inj₁ _} {inj₂ _} h = h zero
∀-LayerEq (G S⊕ H) {x = inj₂ _} {inj₁ _} h = h zero
∀-LayerEq (G S⊗ H) h = ∀-LayerEq G (λ n → proj₁ (h n)) , ∀-LayerEq H (λ n → proj₂ (h n))

-- The conversions between a type-level layer and a set-level one.
cf-rel : ∀ {F} (C : Type) (wf : WellFormedF F) {x y}
       → S (⟦ F ⟧T C) x y → LiftF F (S C) (cfᵛ C wf x) (cfᵛ C wf y)
cf-rel C (wf-K ib) s = cong (prjB ib) (S-base-≡ ib s)
cf-rel C wf-Id     s = s
cf-rel C (wf-Sum f g) {inj₁ x} {inj₁ y} s = cf-rel C f s
cf-rel C (wf-Sum f g) {inj₂ x} {inj₂ y} s = cf-rel C g s
cf-rel C (wf-Sum f g) {inj₁ _} {inj₂ _} ()
cf-rel C (wf-Sum f g) {inj₂ _} {inj₁ _} ()
cf-rel C (wf-Prod f g) {x , x′} {y , y′} (s , s′) = cf-rel C f s , cf-rel C g s′

cf⁻¹-rel : ∀ {F} (C : Type) (wf : WellFormedF F) {x y}
         → LiftF F (S C) x y → S (⟦ F ⟧T C) (cf⁻¹ᵛ C wf x) (cf⁻¹ᵛ C wf y)
cf⁻¹-rel C (wf-K ib) e = S-base ib (cong (injB ib) e)
cf⁻¹-rel C wf-Id     s = s
cf⁻¹-rel C (wf-Sum f g) {inj₁ x} {inj₁ y} s = cf⁻¹-rel C f s
cf⁻¹-rel C (wf-Sum f g) {inj₂ x} {inj₂ y} s = cf⁻¹-rel C g s
cf⁻¹-rel C (wf-Sum f g) {inj₁ _} {inj₂ _} ()
cf⁻¹-rel C (wf-Sum f g) {inj₂ _} {inj₁ _} ()
cf⁻¹-rel C (wf-Prod f g) {x , x′} {y , y′} (s , s′) = cf⁻¹-rel C f s , cf⁻¹-rel C g s′

coerce-in-rel : ∀ (F : Functor) {X} {R : X → X → Set} {x y}
              → LiftF F R x y → LayerEq (translateF Carrier Carrier F) R (Val.coerce-μ-in F X x) (Val.coerce-μ-in F X y)
coerce-in-rel (K B) {X} e = cong (Val.coerce-μ-in (K B) X) e
coerce-in-rel Id    r = r
coerce-in-rel (F ⊕ G) {x = inj₁ x} {inj₁ y} r = coerce-in-rel F r
coerce-in-rel (F ⊕ G) {x = inj₂ x} {inj₂ y} r = coerce-in-rel G r
coerce-in-rel (F ⊕ G) {x = inj₁ _} {inj₂ _} ()
coerce-in-rel (F ⊕ G) {x = inj₂ _} {inj₁ _} ()
coerce-in-rel (F ⊗ G) {x = x , x′} {y , y′} (r , r′) = coerce-in-rel F r , coerce-in-rel G r′

coerce-out-rel : ∀ {F} (wf : WellFormedF F) {X} {R : X → X → Set} {x y}
               → LayerEq (translateF Carrier Carrier F) R x y → LiftF F R (Val.coerce-μ-out wf X x) (Val.coerce-μ-out wf X y)
coerce-out-rel (wf-K ib) {X} e = cong (Val.coerce-μ-out (wf-K ib) X) e
coerce-out-rel wf-Id     r = r
coerce-out-rel (wf-Sum f g) {x = inj₁ x} {inj₁ y} r = coerce-out-rel f r
coerce-out-rel (wf-Sum f g) {x = inj₂ x} {inj₂ y} r = coerce-out-rel g r
coerce-out-rel (wf-Sum f g) {x = inj₁ _} {inj₂ _} ()
coerce-out-rel (wf-Sum f g) {x = inj₂ _} {inj₁ _} ()
coerce-out-rel (wf-Prod f g) {x = x , x′} {y , y′} (r , r′) = coerce-out-rel f r , coerce-out-rel g r′

-- Sequencing a layer of related computations gives related layers.
private
  un-ret : ∀ {X} {R : X → X → Set} {x y} → TreeEq R (ret x) (ret y) → R x y
  un-ret (ret≈ r) = r

seqF-rel : ∀ (F : Functor) {X} {R : X → X → Set} {x y}
         → LiftF F (TreeEq R) x y → TreeEq (LiftF F R) (seqF F x) (seqF F y)
seqF-rel (K B)   e = ret≈ e
seqF-rel Id      t = t
seqF-rel (F ⊕ G) {x = inj₁ x} {inj₁ y} r = TreeEq-bind (seqF-rel F r) (λ l → ret≈ l)
seqF-rel (F ⊕ G) {x = inj₂ x} {inj₂ y} r = TreeEq-bind (seqF-rel G r) (λ l → ret≈ l)
seqF-rel (F ⊕ G) {x = inj₁ _} {inj₂ _} ()
seqF-rel (F ⊕ G) {x = inj₂ _} {inj₁ _} ()
seqF-rel (F ⊗ G) {x = x , x′} {y , y′} (r , r′) =
  TreeEq-bind (seqF-rel F r) (λ l → TreeEq-bind (seqF-rel G r′) (λ l′ → ret≈ (l , l′)))

-- …and of trees that may be infinite.
seqF∞-rel : ∀ (F : Functor) {X} {R : X → X → Set} {x y}
          → LiftF F (TreeEq∞ R) x y → TreeEq∞ (LiftF F R) (seqF∞ F x) (seqF∞ F y)
seqF∞-rel (K B)   e = retT≈ e
seqF∞-rel Id      t = t
seqF∞-rel (F ⊕ G) {x = inj₁ x} {inj₁ y} r = ≈∞-bind (seqF∞-rel F r) (λ l → retT≈ l)
seqF∞-rel (F ⊕ G) {x = inj₂ x} {inj₂ y} r = ≈∞-bind (seqF∞-rel G r) (λ l → retT≈ l)
seqF∞-rel (F ⊕ G) {x = inj₁ _} {inj₂ _} ()
seqF∞-rel (F ⊕ G) {x = inj₂ _} {inj₁ _} ()
seqF∞-rel (F ⊗ G) {x = x , x′} {y , y′} (r , r′) =
  ≈∞-bind (seqF∞-rel F r) (λ l → ≈∞-bind (seqF∞-rel G r′) (λ l′ → retT≈ (l , l′)))

-- A leaf, read back; a finite tree, read back from its embedding.
un-ret∞ : ∀ {X} {R : X → X → Set} {x y} → TreeEq∞ R (return∞ x) (return∞ y) → R x y
un-ret∞ h = leaf (force≈ h)
  where leaf : ∀ {X} {R : X → X → Set} {Q : T∞ X → T∞ X → Set} {x y} → NodeEq R Q (ret∞ x) (ret∞ y) → R x y
        leaf (ret≈∞ r) = r

embed⁻¹ : ∀ {X} {R : X → X → Set} (m m′ : T X) → TreeEq∞ R (embed m) (embed m′) → TreeEq R m m′
embed⁻¹F : ∀ {X} {R : X → X → Set} (m m′ : T X)
         → NodeEq R (TreeEq∞ R) (force (embed m)) (force (embed m′)) → TreeEq R m m′
embed⁻¹ m m′ h = embed⁻¹F m m′ (force≈ h)
embed⁻¹F (ret x)      (ret y)        (ret≈∞ r)  = ret≈ r
embed⁻¹F (call o a k) (call .o .a k′) (call≈∞ f) = call≈ (λ b → embed⁻¹ (k b) (k′ b) (f b))
embed⁻¹F (halt o a)   (halt .o .a)    halt≈∞     = halt≈

seqM-rel : ∀ {π} (u : pure ⊑π π) (F : Functor) {X} {R : X → X → Set} {x y}
         → LiftF F (λ m m′ → TreeEq∞ R (toT∞ π m) (toT∞ π m′)) x y
         → TreeEq∞ (LiftF F R) (toT∞ π (seqM u F x)) (toT∞ π (seqM u F y))
seqM-rel ⊑-pure F r = retT≈ (LiftF-map F un-ret∞ r)
seqM-rel ⊑-pe   F {x = x} {y} r = embed-≈ (seqF-rel F (LiftF-mapᵈ F r))
  where LiftF-mapᵈ : ∀ (G : Functor) {u v} → LiftF G (λ m m′ → TreeEq∞ _ (embed m) (embed m′)) u v → LiftF G (TreeEq _) u v
        LiftF-mapᵈ G = LiftF-map G (λ {m} {m′} h → embed⁻¹ m m′ h)
seqM-rel ⊑-pp   F r = seqF∞-rel F r

private
  ret-≈ : ∀ {X} (x : X) → TreeEq∞ _≡_ (embed (ret x)) (return∞ x)
  force≈ (ret-≈ x) = ret≈∞ refl

  fmap-pure : ∀ {X Y} (h : X → Y) (m : X) → TreeEq∞ _≡_ (return∞ (h m)) (fmap∞ h (return∞ m))
  force≈ (fmap-pure h m) = ret≈∞ refl

-- `fmapM` is `fmap∞` on the tree.
toT∞-fmapM : ∀ π {X Y} (h : X → Y) (m : M π X) → TreeEq∞ _≡_ (toT∞ π (fmapM π h m)) (fmap∞ h (toT∞ π m))
toT∞-fmapM pure h m = fmap-pure h m
toT∞-fmapM eff  h m =
  ≈∞-rewrite (embed-bind m (λ x → ret (h x))) (≈refl _)
             (≈∞-bind {R = _≡_} (≈refl (embed m)) λ { refl → ret-≈ _ })
toT∞-fmapM prod h m = ≈refl (fmap∞ h m)
toT∞-fmapM eff⁺ h m =
  ≈∞-rewrite (≡→≈ (cong embed (forget-bind⁺ m (λ x → ret (h x))))) (≈refl _) (toT∞-fmapM eff h (forget⁺ m))
  where ≡→≈ : ∀ {X} {a b : T∞ X} → a ≡ b → TreeEq∞ _≡_ a b
        ≡→≈ {a = a} refl = ≈refl a

-- Two bisimilarities of trees, composed.
≈trans : ∀ {X} {a b c : T∞ X} → TreeEq∞ _≡_ a b → TreeEq∞ _≡_ b c → TreeEq∞ _≡_ a c
≈trans {c = c} e₁ e₂ = ≈∞-rewrite e₁ (≈refl c) e₂

------------------------------------------------------------------------
-- μ: the fold, by induction on the value
------------------------------------------------------------------------

module Fold {π : Purity} (u : pure ⊑π π) {F : Functor} {A : Type} (wf : WellFormedF F)
            (alg alg′ : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ)
            (salg : ∀ a a′ → S (⟦ F ⟧T A) a a′ → TreeEq∞ (S A) (toT∞ π (alg a)) (toT∞ π (alg′ a′))) where

  private
    H = translateF Carrier Carrier F
    φ φ′ : ⟦ H ⟧SF (M π ⟦ A ⟧ᵛ) → M π ⟦ A ⟧ᵛ
    φ  x = bindM π (seqM u F (Val.coerce-μ-out wf (M π ⟦ A ⟧ᵛ) x)) λ layer → alg  (cf⁻¹ᵛ A wf layer)
    φ′ x = bindM π (seqM u F (Val.coerce-μ-out wf (M π ⟦ A ⟧ᵛ) x)) λ layer → alg′ (cf⁻¹ᵛ A wf layer)

  mutual
    cata-S : ∀ (v : μS H) → SM π A (cata-semᵛ u wf alg v) (cata-semᵛ u wf alg′ v)
    cata-S ⟨ x ⟩ =
      ≈∞-rewrite (toT∞-bindM π _ _) (toT∞-bindM π _ _)
        (≈∞-bind (seqM-rel u F (coerce-out-rel wf (layer-S H x)))
                 (λ l → salg _ _ (cf⁻¹-rel A wf l)))

    layer-S : ∀ (G : SFunctor) (x : ⟦ G ⟧SF (μS H))
            → LayerEq G (SM π A) (sfmapCata G φ x) (sfmapCata G φ′ x)
    layer-S (SK B)   x        = refl
    layer-S SId      v        = cata-S v
    layer-S (G S⊕ G₂) (inj₁ x) = layer-S G x
    layer-S (G S⊕ G₂) (inj₂ y) = layer-S G₂ y
    layer-S (G S⊗ G₂) (x , y)  = layer-S G x , layer-S G₂ y

------------------------------------------------------------------------
-- ν: unfold, to every depth
------------------------------------------------------------------------

module UnfoldPure {F : Functor} {A : Type} (wf : WellFormedF F)
                  (clo clo′ : ⟦ A ⟧ᵛ → ⟦ ⟦ F ⟧T A ⟧ᵛ)
                  (sc : ∀ {a a′} → S A a a′ → S (⟦ F ⟧T A) (clo a) (clo′ a′)) where

  private
    H = translateF Carrier Carrier F
    c c′ : ⟦ A ⟧ᵛ → ⟦ H ⟧SF ⟦ A ⟧ᵛ
    c  a = Val.coerce-ν-in F _ (cfᵛ A wf (clo a))
    c′ a = Val.coerce-ν-in F _ (cfᵛ A wf (clo′ a))

  mutual
    ana-upto : ∀ n {a a′} → S A a a′ → νᵖ-upto H n (anaᵖ H c a) (anaᵖ H c′ a′)
    ana-upto zero    s = tt
    ana-upto (suc n) s = map-upto H n (coerce-in-rel F (cf-rel A wf (sc s)))

    map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (S A) x y
             → LayerEq G (νᵖ-upto H n) (mapAnaᵖ H G c x) (mapAnaᵖ H G c′ y)
    map-upto (SK B)   n e = e
    map-upto SId      n s = ana-upto n s
    map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
    map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
    map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
    map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
    map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

  ana-Same : ∀ {a a′} → S A a a′ → Same (ν-type F pure) (anaᵖ H c a) (anaᵖ H c′ a′)
  ana-Same s n = ana-upto n s

module UnfoldEff {F : Functor} {A : Type} (wf : WellFormedF F)
                 (clo clo′ : ⟦ A ⟧ᵛ → T ⟦ ⟦ F ⟧T A ⟧ᵛ)
                 (sc : ∀ {a a′} → S A a a′ → TreeEq (S (⟦ F ⟧T A)) (clo a) (clo′ a′)) where

  private
    H = translateF Carrier Carrier F
    c c′ : ⟦ A ⟧ᵛ → T (⟦ H ⟧SF ⟦ A ⟧ᵛ)
    c  a = fmapT (λ l → Val.coerce-ν-in F _ (cfᵛ A wf l)) (clo a)
    c′ a = fmapT (λ l → Val.coerce-ν-in F _ (cfᵛ A wf l)) (clo′ a)

    step : ∀ {a a′} → S A a a′ → TreeEq (LayerEq H (S A)) (c a) (c′ a′)
    step s = TreeEq-bind (sc s) (λ r → ret≈ (coerce-in-rel F (cf-rel A wf r)))

  mutual
    ana-upto : ∀ n {a a′} → S A a a′ → νᵈ-upto H n (anaᵈ H c a) (anaᵈ H c′ a′)
    ana-upto zero    s = tt
    ana-upto (suc n) s = tree-upto n (step s)

    tree-upto : ∀ n {t t′} → TreeEq (LayerEq H (S A)) t t′
              → TreeEq (LayerEq H (νᵈ-upto H n)) (anaTree H c t) (anaTree H c′ t′)
    tree-upto n (ret≈ l)  = ret≈ (map-upto H n l)
    tree-upto n (call≈ k) = call≈ (λ b → tree-upto n (k b))
    tree-upto n halt≈     = halt≈

    map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (S A) x y
             → LayerEq G (νᵈ-upto H n) (mapAnaᵈ H G c x) (mapAnaᵈ H G c′ y)
    map-upto (SK B)   n e = e
    map-upto SId      n s = ana-upto n s
    map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
    map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
    map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
    map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
    map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

  ana-Same : ∀ {a a′} → S A a a′ → Same (ν-type F eff) (anaᵈ H c a) (anaᵈ H c′ a′)
  ana-Same s n = ana-upto n s

module UnfoldProd {F : Functor} {A : Type} (wf : WellFormedF F)
                  (clo clo′ : ⟦ A ⟧ᵛ → T∞ ⟦ ⟦ F ⟧T A ⟧ᵛ)
                  (sc : ∀ {a a′} → S A a a′ → TreeEq∞ (S (⟦ F ⟧T A)) (clo a) (clo′ a′)) where

  private
    H = translateF Carrier Carrier F
    c c′ : ⟦ A ⟧ᵛ → T∞ (⟦ H ⟧SF ⟦ A ⟧ᵛ)
    c  a = fmap∞ (λ l → Val.coerce-ν-in F _ (cfᵛ A wf l)) (clo a)
    c′ a = fmap∞ (λ l → Val.coerce-ν-in F _ (cfᵛ A wf l)) (clo′ a)

    step : ∀ {a a′} → S A a a′ → TreeEq∞ (LayerEq H (S A)) (c a) (c′ a′)
    step s = ≈∞-bind (sc s) (λ r → retT≈ (coerce-in-rel F (cf-rel A wf r)))

  ana-upto  : ∀ n {a a′} → S A a a′ → ν∞-upto H n (ana∞ H c a) (ana∞ H c′ a′)
  tree-upto : ∀ n k {t t′} → TreeEq∞ (LayerEq H (S A)) t t′
            → TreeEqN k (LayerEq H (ν∞-upto H n)) (anaTree∞ H c t) (anaTree∞ H c′ t′)
  layer-upto : ∀ n k {l l′} → NodeEq (LayerEq H (S A)) (TreeEq∞ (LayerEq H (S A))) l l′
             → NodeEq (LayerEq H (ν∞-upto H n)) (TreeEqN k (LayerEq H (ν∞-upto H n))) (anaLayer∞ H c l) (anaLayer∞ H c′ l′)
  map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (S A) x y
           → LayerEq G (ν∞-upto H n) (mapAna∞ H G c x) (mapAna∞ H G c′ y)
  ana-upto zero    s = tt
  ana-upto (suc n) s = tree-upto n (suc n) (step s)
  tree-upto n zero    h = tt
  tree-upto n (suc k) h = layer-upto n k (force≈ h)
  layer-upto n k (ret≈∞ l)  = ret≈∞ (map-upto H n l)
  layer-upto n k (call≈∞ g) = call≈∞ (λ b → tree-upto n k (g b))
  layer-upto n k halt≈∞     = halt≈∞
  map-upto (SK B)   n e = e
  map-upto SId      n s = ana-upto n s
  map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
  map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
  map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
  map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
  map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

  ana-Same : ∀ {a a′} → S A a a′ → Same (ν-type F prod) (ana∞ H c a) (ana∞ H c′ a′)
  ana-Same s n = ana-upto n s

module UnfoldGuarded {F : Functor} {A : Type} (wf : WellFormedF F)
                     (clo clo′ : ⟦ A ⟧ᵛ → T⁺ ⟦ ⟦ F ⟧T A ⟧ᵛ)
                     (sc : ∀ {a a′} → S A a a′ → TreeEq (S (⟦ F ⟧T A)) (forget⁺ (clo a)) (forget⁺ (clo′ a′))) where

  private
    H = translateF Carrier Carrier F
    g : ⟦ ⟦ F ⟧T A ⟧ᵛ → ⟦ H ⟧SF ⟦ A ⟧ᵛ
    g l = Val.coerce-ν-in F _ (cfᵛ A wf l)
    c c′ : ⟦ A ⟧ᵛ → T⁺ (⟦ H ⟧SF ⟦ A ⟧ᵛ)
    c  a = fmap⁺ g (clo a)
    c′ a = fmap⁺ g (clo′ a)

    step : ∀ {a a′} → S A a a′ → TreeEq (LayerEq H (S A)) (forget⁺ (c a)) (forget⁺ (c′ a′))
    step {a} {a′} s =
      subst₂ (TreeEq (LayerEq H (S A))) (sym (forget-bind⁺ (clo a) (λ l → ret (g l)))) (sym (forget-bind⁺ (clo′ a′) (λ l → ret (g l))))
        (TreeEq-bind (sc s) (λ r → ret≈ (coerce-in-rel F (cf-rel A wf r))))

  mutual
    ana-upto : ∀ n {a a′} → S A a a′ → ν⁺-upto H n (ana⁺ H c a) (ana⁺ H c′ a′)
    ana-upto zero    s = tt
    ana-upto (suc n) {a} {a′} s =
      subst₂ (TreeEq (LayerEq H (ν⁺-upto H n))) (sym (forget-anaRoot H c (c a))) (sym (forget-anaRoot H c′ (c′ a′)))
        (tree-upto n (step s))

    tree-upto : ∀ n {t t′} → TreeEq (LayerEq H (S A)) t t′
              → TreeEq (LayerEq H (ν⁺-upto H n)) (anaTree⁺ H c t) (anaTree⁺ H c′ t′)
    tree-upto n (ret≈ l)  = ret≈ (map-upto H n l)
    tree-upto n (call≈ k) = call≈ (λ b → tree-upto n (k b))
    tree-upto n halt≈     = halt≈

    map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (S A) x y
             → LayerEq G (ν⁺-upto H n) (mapAna⁺ H G c x) (mapAna⁺ H G c′ y)
    map-upto (SK B)   n e = e
    map-upto SId      n s = ana-upto n s
    map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
    map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
    map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
    map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
    map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

  ana-Same : ∀ {a a′} → S A a a′ → Same (ν-type F eff⁺) (ana⁺ H c a) (ana⁺ H c′ a′)
  ana-Same s n = ana-upto n s

-- The unfold's meaning, at every grade of the stream: the coalgebra functions
-- related as arrows, the seeds related. The stream is a VALUE (building it
-- runs nothing); the rule embeds it at the grade it is built at.
ana-S : ∀ (π : Purity) {F A} (wf : WellFormedF F) (clo clo′ : ⟦ A ⟧ᵛ → M π ⟦ ⟦ F ⟧T A ⟧ᵛ)
      → (∀ a a′ → S A a a′ → TreeEq∞ (S (⟦ F ⟧T A)) (toT∞ π (clo a)) (toT∞ π (clo′ a′)))
      → ∀ {a a′} → S A a a′
      → S (ν-type F π) (ana-semᵛ π wf clo a) (ana-semᵛ π wf clo′ a′)
ana-S pure {F} {A} wf clo clo′ sc s = UnfoldPure.ana-Same wf clo clo′ (λ s′ → un-ret∞ (sc _ _ s′)) s
ana-S eff⁺ {F} {A} wf clo clo′ sc s =
  UnfoldGuarded.ana-Same wf clo clo′ (λ {a} {a′} s′ → embed⁻¹ (forget⁺ (clo a)) (forget⁺ (clo′ a′)) (sc _ _ s′)) s
ana-S eff  {F} {A} wf clo clo′ sc s =
  UnfoldEff.ana-Same wf clo clo′ (λ {a} {a′} s′ → embed⁻¹ (clo a) (clo′ a′) (sc _ _ s′)) s
ana-S prod {F} {A} wf clo clo′ sc s = UnfoldProd.ana-Same wf clo clo′ (λ s′ → sc _ _ s′) s

------------------------------------------------------------------------
-- ν: out
------------------------------------------------------------------------

out-S : ∀ π {F} (wf : WellFormedF F) {v w}
      → Same (ν-type F π) v w → SM π (⟦ F ⟧T (ν-type F π)) (out-semᵛ π wf v) (out-semᵛ π wf w)
out-S pure {F} wf h =
  retT≈ (cf⁻¹-rel (ν-type F pure) wf
          (coerce-out-rel wf (∀-LayerEq (translateF Carrier Carrier F) (λ n → h (suc n)))))
out-S eff {F} wf {v} {w} h =
  embed-≈
    (TreeEq-bind
      (TreeEq-map (∀-LayerEq (translateF Carrier Carrier F))
        (∀-TreeEq (forceᵈ v) (forceᵈ w) (λ n → h (suc n))))
      (λ l → ret≈ (cf⁻¹-rel (ν-type F eff) wf (coerce-out-rel wf l))))
out-S eff⁺ {F} wf {v} {w} h =
  ≈∞-rewrite (e v) (e w)
    (embed-≈
      (TreeEq-bind
        (TreeEq-map (∀-LayerEq H) (∀-TreeEq (forget⁺ (force⁺ v)) (forget⁺ (force⁺ w)) (λ n → h (suc n))))
        (λ l → ret≈ (cf⁻¹-rel (ν-type F eff⁺) wf (coerce-out-rel wf l)))))
  where
    H = translateF Carrier Carrier F
    k : _ → T _
    k layer = ret (cf⁻¹ᵛ (ν-type F eff⁺) wf (Val.coerce-ν-out wf _ layer))
    e : ∀ x → TreeEq∞ _≡_ (embed (forget⁺ (Once.Spec.Guarded._>>=⁺_ (force⁺ x) k))) (embed (forget⁺ (force⁺ x) >>=T k))
    e x = ≡→≈ (cong embed (forget-bind⁺ (force⁺ x) k))
      where ≡→≈ : ∀ {X} {a b : T∞ X} → a ≡ b → TreeEq∞ _≡_ a b
            ≡→≈ {a = a} refl = ≈refl a
out-S prod {F} wf {v} {w} h =
  ≈∞-bind
    (≈∞-map (∀-LayerEq H)
      (Depth.N→≈∞ (λ n → LayerEq H (ν∞-upto H n)) (λ {n} → LayerEq-map H (ν∞-mono H n))
        (λ n → TreeEqN-mono (λ x → x) n {force∞ v} {force∞ w} (h (suc n)))))
    (λ l → retT≈ (cf⁻¹-rel (ν-type F prod) wf (coerce-out-rel wf l)))
  where H = translateF Carrier Carrier F

------------------------------------------------------------------------
-- The subtyping coercions
------------------------------------------------------------------------

module Emb (H : SFunctor) where
  mutual
    emb-upto : ∀ n {v w} → νᵖ-upto H n v w → νᵈ-upto H n (embν v) (embν w)
    emb-upto zero    h = tt
    emb-upto (suc n) h = ret≈ (map-upto H n h)

    map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (νᵖ-upto H n) x y
             → LayerEq G (νᵈ-upto H n) (mapEmbν H G x) (mapEmbν H G y)
    map-upto (SK B)   n e = e
    map-upto SId      n h = emb-upto n h
    map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
    map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
    map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
    map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
    map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

module Emb∞ᵈ (H : SFunctor) where
  emb-upto : ∀ n {v w} → νᵈ-upto H n v w → ν∞-upto H n (embν∞ᵈ v) (embν∞ᵈ w)
  lay      : ∀ n k {t t′} → TreeEq (LayerEq H (νᵈ-upto H n)) t t′
           → TreeEqN k (LayerEq H (ν∞-upto H n)) (embLay∞ H t) (embLay∞ H t′)
  map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (νᵈ-upto H n) x y
           → LayerEq G (ν∞-upto H n) (mapEmbν∞ᵈ H G x) (mapEmbν∞ᵈ H G y)
  emb-upto zero    h = tt
  emb-upto (suc n) h = lay n (suc n) h
  lay n zero    h = tt
  lay n (suc k) (ret≈ l)  = ret≈∞ (map-upto H n l)
  lay n (suc k) (call≈ f) = call≈∞ (λ b → lay n k (f b))
  lay n (suc k) halt≈     = halt≈∞
  map-upto (SK B)   n e = e
  map-upto SId      n h = emb-upto n h
  map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
  map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
  map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
  map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
  map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

module Emb⁺ᵈ (H : SFunctor) where
  private
    root : ∀ (m : T⁺ (⟦ H ⟧SF (ν⁺ H))) → embRoot⁺ H m ≡ embTree⁺ H (forget⁺ m)
    root (call⁺ o a k) = refl
    root (halt⁺ o a)   = refl
  emb-upto : ∀ n {v w} → ν⁺-upto H n v w → νᵈ-upto H n (embν⁺ᵈ v) (embν⁺ᵈ w)
  lay      : ∀ n {t t′} → TreeEq (LayerEq H (ν⁺-upto H n)) t t′
           → TreeEq (LayerEq H (νᵈ-upto H n)) (embTree⁺ H t) (embTree⁺ H t′)
  map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (ν⁺-upto H n) x y
           → LayerEq G (νᵈ-upto H n) (mapEmbν⁺ᵈ H G x) (mapEmbν⁺ᵈ H G y)
  emb-upto zero    h = tt
  emb-upto (suc n) {v} {w} h = subst₂ (TreeEq (LayerEq H (νᵈ-upto H n))) (sym (root (force⁺ v))) (sym (root (force⁺ w))) (lay n h)
  lay n (ret≈ l)  = ret≈ (map-upto H n l)
  lay n (call≈ f) = call≈ (λ b → lay n (f b))
  lay n halt≈     = halt≈
  map-upto (SK B)   n e = e
  map-upto SId      n h = emb-upto n h
  map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
  map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
  map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
  map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
  map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

module Emb∞ᵖ (H : SFunctor) where
  emb-upto : ∀ n {v w} → νᵖ-upto H n v w → ν∞-upto H n (embν∞ᵖ v) (embν∞ᵖ w)
  map-upto : ∀ (G : SFunctor) n {x y} → LayerEq G (νᵖ-upto H n) x y
           → LayerEq G (ν∞-upto H n) (mapEmbν∞ᵖ H G x) (mapEmbν∞ᵖ H G y)
  emb-upto zero    h = tt
  emb-upto (suc n) h = ret≈∞ (map-upto H n h)
  map-upto (SK B)   n e = e
  map-upto SId      n h = emb-upto n h
  map-upto (G S⊕ G₂) n {inj₁ x} {inj₁ y} r = map-upto G n r
  map-upto (G S⊕ G₂) n {inj₂ x} {inj₂ y} r = map-upto G₂ n r
  map-upto (G S⊕ G₂) n {inj₁ _} {inj₂ _} ()
  map-upto (G S⊕ G₂) n {inj₂ _} {inj₁ _} ()
  map-upto (G S⊗ G₂) n (r , r′) = map-upto G n r , map-upto G₂ n r′

coerce-S : ∀ {A B} (p : A <: B) {x y} → S A x y → S B (⟦ p ⟧<:ᵛ x) (⟦ p ⟧<:ᵛ y)
coerce-S sub-void  {()} s
coerce-S sub-unit  s = s
coerce-S sub-int   s = s
coerce-S sub-float s = s
coerce-S (sub-arr {q = Zero} {π = π} {π′ = π′} a b g) {f} {f′} s =
  ≈∞-rewrite (≈trans (toT∞-subM g _) (toT∞-fmapM π _ _)) (≈trans (toT∞-subM g _) (toT∞-fmapM π _ _))
    (≈∞-bind s (λ r → retT≈ (coerce-S b r)))
coerce-S (sub-arr {q = One} {π = π} a b g) {f} {f′} s x x′ sx =
  ≈∞-rewrite (≈trans (toT∞-subM g _) (toT∞-fmapM π _ _)) (≈trans (toT∞-subM g _) (toT∞-fmapM π _ _))
    (≈∞-bind (s _ _ (coerce-S a sx)) (λ r → retT≈ (coerce-S b r)))
coerce-S (sub-arr {q = Many} {π = π} a b g) {f} {f′} s x x′ sx =
  ≈∞-rewrite (≈trans (toT∞-subM g _) (toT∞-fmapM π _ _)) (≈trans (toT∞-subM g _) (toT∞-fmapM π _ _))
    (≈∞-bind (s _ _ (coerce-S a sx)) (λ r → retT≈ (coerce-S b r)))
coerce-S (sub-prod a b) {x , y} {x′ , y′} (sa , sb) = coerce-S a sa , coerce-S b sb
coerce-S (sub-sum a b) {inj₁ x} {inj₁ y} s = coerce-S a s
coerce-S (sub-sum a b) {inj₂ x} {inj₂ y} s = coerce-S b s
coerce-S (sub-sum a b) {inj₁ _} {inj₂ _} ()
coerce-S (sub-sum a b) {inj₂ _} {inj₁ _} ()
coerce-S sub-μ s = s
coerce-S (sub-ν ⊑-pure) s = s
coerce-S (sub-ν ⊑-eff)  s = s
coerce-S (sub-ν {F = F} ⊑-pe) s n = Emb.emb-upto (translateF Carrier Carrier F) n (s n)
coerce-S (sub-ν ⊑-prod) s = s
coerce-S (sub-ν {F = F} ⊑-pp) s n = Emb∞ᵖ.emb-upto (translateF Carrier Carrier F) n (s n)
coerce-S (sub-ν {F = F} ⊑-ep) s n = Emb∞ᵈ.emb-upto (translateF Carrier Carrier F) n (s n)
coerce-S (sub-ν ⊑-g) s = s
coerce-S (sub-ν {F = F} ⊑-ge) s n = Emb⁺ᵈ.emb-upto (translateF Carrier Carrier F) n (s n)
coerce-S (sub-ν {F = F} ⊑-gp) s n =
  Emb∞ᵈ.emb-upto (translateF Carrier Carrier F) n (Emb⁺ᵈ.emb-upto (translateF Carrier Carrier F) n (s n))
coerce-S sub-rigid s = s

------------------------------------------------------------------------
-- D311: GUARDED ITERATION. Related steps, iterated from related seeds, give
-- bisimilar trees: each round's tree is related node by node, and a looping
-- answer starts the next round from related seeds — under the event the
-- step performed first, so the bisimulation is guarded.
------------------------------------------------------------------------

module Iter {A B : Type} (step step′ : ⟦ A ⟧ᵛ → T⁺ (⟦ B ⟧ᵛ Data.Sum.⊎ ⟦ A ⟧ᵛ))
            (sf : ∀ a a′ → S A a a′ → TreeEq∞ (S (B + A)) (embed (forget⁺ (step a))) (embed (forget⁺ (step′ a′))))
            where
  iter-S : ∀ a a′ → S A a a′ → TreeEq∞ (S B) (iter∞ step a) (iter∞ step′ a′)
  root-S : ∀ (m m′ : T⁺ (⟦ B ⟧ᵛ Data.Sum.⊎ ⟦ A ⟧ᵛ))
         → NodeEq (S (B + A)) (TreeEq∞ (S (B + A))) (force (embed (forget⁺ m))) (force (embed (forget⁺ m′)))
         → NodeEq (S B) (TreeEq∞ (S B)) (iterRoot∞ step m) (iterRoot∞ step′ m′)
  tree-S : ∀ (t t′ : T (⟦ B ⟧ᵛ Data.Sum.⊎ ⟦ A ⟧ᵛ))
         → TreeEq∞ (S (B + A)) (embed t) (embed t′) → TreeEq∞ (S B) (iterTree∞ step t) (iterTree∞ step′ t′)
  tree-N : ∀ (t t′ : T (⟦ B ⟧ᵛ Data.Sum.⊎ ⟦ A ⟧ᵛ))
         → NodeEq (S (B + A)) (TreeEq∞ (S (B + A))) (force (embed t)) (force (embed t′))
         → NodeEq (S B) (TreeEq∞ (S B)) (force (iterTree∞ step t)) (force (iterTree∞ step′ t′))

  force≈ (iter-S a a′ s) = root-S (step a) (step′ a′) (force≈ (sf a a′ s))

  root-S (call⁺ o x k) (call⁺ .o .x k′) (call≈∞ hk) = call≈∞ (λ b → tree-S (k b) (k′ b) (hk b))
  root-S (halt⁺ o x)   (halt⁺ .o .x)    halt≈∞      = halt≈∞
  root-S (call⁺ _ _ _) (halt⁺ _ _)      ()
  root-S (halt⁺ _ _)   (call⁺ _ _ _)    ()

  force≈ (tree-S t t′ h) = tree-N t t′ (force≈ h)

  tree-N (ret (inj₁ b)) (ret (inj₁ b′)) (ret≈∞ r) = ret≈∞ r
  tree-N (ret (inj₂ a)) (ret (inj₂ a′)) (ret≈∞ r) = root-S (step a) (step′ a′) (force≈ (sf a a′ r))
  tree-N (ret (inj₁ _)) (ret (inj₂ _)) (ret≈∞ ())
  tree-N (ret (inj₂ _)) (ret (inj₁ _)) (ret≈∞ ())
  tree-N (call o x k) (call .o .x k′) (call≈∞ hk) = call≈∞ (λ b → tree-S (k b) (k′ b) (hk b))
  tree-N (halt o x) (halt .o .x) halt≈∞ = halt≈∞
  tree-N (ret _)      (call _ _ _) ()
  tree-N (ret _)      (halt _ _)   ()
  tree-N (call _ _ _) (ret _)      ()
  tree-N (call _ _ _) (halt _ _)   ()
  tree-N (halt _ _)   (ret _)      ()
  tree-N (halt _ _)   (call _ _ _) ()
