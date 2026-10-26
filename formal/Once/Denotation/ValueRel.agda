-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ValueRel — when two values of the IR's domain behave alike
-- (plan 0.119 D5).
--
-- The IR means `T∞` arrows, and two runs are compared step for step
-- (`RelS`), never by `≡`: a coinductive record has no η, so two meanings built
-- differently are not equal even when every observation agrees. A value
-- relation follows the type: first-order data must be EQUAL; an arrow takes
-- related arguments to related runs; a stream's forced layers are related runs
-- of related layers (coinductively). It is the relation an IR-to-IR
-- transformation (the arith lowering) is proved against.
------------------------------------------------------------------------

module Once.Denotation.ValueRel where

import Once.Spec.Type as SpT
open import Once.Spec.Type using (Base; WFFun; b-*; b-+; b-Float; b-Int; b-Unit; b-Void; wf-⊕; wf-⊗; ∅ₖ)
open import Once.Spec.Type using (Base)
open import Once.Spec.Type using (var; b-var; Ty; Fun; KCtx; WFFun)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Type; K; Id; _⊕_; _⊗_; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float)
open import Once.Spec.Type using (μ; ν)
open import Once.Spec.Polynomial using (SFunctor; SId; SK; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.IR.Semantics.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using (⟦_⟧F)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.IR.Semantics.StreamInf using (νᴵ; module νᴵ)
open νᴵ using (forceᴵ)
open import Once.Denotation.TraceMonadInfLaws using (RelS)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)

------------------------------------------------------------------------
-- Streams: forced layers are related runs; a layer's constants are equal and
-- its recursive positions related streams.
------------------------------------------------------------------------

record StreamRel (H : SFunctor) (x y : νᴵ H) : Set
LayerRel : ∀ (H G : SFunctor) → ⟦ G ⟧SF (νᴵ H) → ⟦ G ⟧SF (νᴵ H) → Set

record StreamRel H x y where
  coinductive
  field forceR : RelS (LayerRel H H) (forceᴵ x) (forceᴵ y)

LayerRel H (SK B)     x        y        = x ≡ y
LayerRel H SId        x        y        = StreamRel H x y
LayerRel H (G₁ S⊕ G₂) (inj₁ x) (inj₁ y) = LayerRel H G₁ x y
LayerRel H (G₁ S⊕ G₂) (inj₂ x) (inj₂ y) = LayerRel H G₂ x y
LayerRel H (G₁ S⊕ G₂) (inj₁ _) (inj₂ _) = ⊥
LayerRel H (G₁ S⊕ G₂) (inj₂ _) (inj₁ _) = ⊥
LayerRel H (G₁ S⊗ G₂) (x , y)  (x′ , y′) = LayerRel H G₁ x x′ × LayerRel H G₂ y y′

------------------------------------------------------------------------
-- The relation, by type.
------------------------------------------------------------------------

RelD : ∀ {m} (A : Ty m) → ⟦ A ⟧ᴰ → ⟦ A ⟧ᴰ → Set
RelD Unit        _ _ = ⊤
RelD Void        () _
RelD (A * B) (a , b) (a′ , b′) = RelD A a a′ × RelD B b b′
RelD (A + B) (inj₁ a) (inj₁ a′) = RelD A a a′
RelD (A + B) (inj₂ b) (inj₂ b′) = RelD B b b′
RelD (A + B) (inj₁ _) (inj₂ _)  = ⊥
RelD (A + B) (inj₂ _) (inj₁ _)  = ⊥
RelD (A ⇒[ mk-kind Zero π ] B) f g = RelS (RelD B) (f tt) (g tt)
RelD (A ⇒[ mk-kind One  π ] B) f g = ∀ {a a′} → RelD A a a′ → RelS (RelD B) (f a) (g a′)
RelD (A ⇒[ mk-kind Many π ] B) f g = ∀ {a a′} → RelD A a a′ → RelS (RelD B) (f a) (g a′)
RelD (μ F)  x y = x ≡ y
RelD (ν F _) x y = StreamRel (translateF Carrier Carrier F) x y
RelD Int         x y = x ≡ y
RelD Float       x y = x ≡ y
RelD (var _) () _

-- Transport along an equation of types.
RelD-subst : ∀ {m} {A B : Ty m} (e : A ≡ B) {x y : ⟦ A ⟧ᴰ}
           → RelD A x y → RelD B (subst ⟦_⟧ᴰ e x) (subst ⟦_⟧ᴰ e y)
RelD-subst refl r = r

------------------------------------------------------------------------
-- A relation lifted through a functor's layer: constants equal, recursive
-- positions related.
------------------------------------------------------------------------

data FRel {m} {X Y : Set} (R : X → Y → Set) : (F : Fun m) → ⟦ F ⟧F X → ⟦ F ⟧F Y → Set where
  fr-K    : ∀ {A x} → FRel R (K A) x x
  fr-Id   : ∀ {x y} → R x y → FRel R Id x y
  fr-inl  : ∀ {F G x y} → FRel R F x y → FRel R (F ⊕ G) (inj₁ x) (inj₁ y)
  fr-inr  : ∀ {F G x y} → FRel R G x y → FRel R (F ⊕ G) (inj₂ x) (inj₂ y)
  fr-pair : ∀ {F G x y x′ y′} → FRel R F x x′ → FRel R G y y′ → FRel R (F ⊗ G) (x , y) (x′ , y′)

SRel : ∀ {X Y : Set} (R : X → Y → Set) (G : SFunctor) → ⟦ G ⟧SF X → ⟦ G ⟧SF Y → Set
SRel R (SK B)    x        y        = x ≡ y
SRel R SId       x        y        = R x y
SRel R (F S⊕ G) (inj₁ x) (inj₁ y) = SRel R F x y
SRel R (F S⊕ G) (inj₂ x) (inj₂ y) = SRel R G x y
SRel R (F S⊕ G) (inj₁ _) (inj₂ _) = ⊥
SRel R (F S⊕ G) (inj₂ _) (inj₁ _) = ⊥
SRel R (F S⊗ G) (x , y)  (x′ , y′) = SRel R F x x′ × SRel R G y y′

------------------------------------------------------------------------
-- Base types: related is equal, and equal is related.
------------------------------------------------------------------------

open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Denotation.ValueDomain using (forgetᵇ; injectᵇ; coerce-functor-D; coerce-functor⁻¹-D)

base-eq : ∀ {m} {Δₖ : KCtx m} {A : Ty m} → Base Δₖ A → ∀ {x y : ⟦ A ⟧ᴰ} → RelD A x y → x ≡ y
base-eq b-Unit       _ = refl
base-eq b-Void {()}
base-eq b-Int        r = r
base-eq b-Float      r = r
base-eq (b-* a b) {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) with base-eq a r₁ | base-eq b r₂
... | refl | refl = refl
base-eq (b-+ a b) {inj₁ x} {inj₁ y} r = cong inj₁ (base-eq a r)
base-eq (b-+ a b) {inj₂ x} {inj₂ y} r = cong inj₂ (base-eq b r)
base-eq (b-+ a b) {inj₁ _} {inj₂ _} ()
base-eq (b-+ a b) {inj₂ _} {inj₁ _} ()
base-eq (b-var _) {()}

base-refl : ∀ {m} {Δₖ : KCtx m} {A : Ty m} → Base Δₖ A → ∀ (x : ⟦ A ⟧ᴰ) → RelD A x x
base-refl b-Unit       x = tt
base-refl b-Void       ()
base-refl b-Int        x = refl
base-refl b-Float      x = refl
base-refl (b-* a b) (x , y) = base-refl a x , base-refl b y
base-refl (b-+ a b)  (inj₁ x) = base-refl a x
base-refl (b-+ a b)  (inj₂ y) = base-refl b y
base-refl (b-var _)      ()

------------------------------------------------------------------------
-- Runs: the monad's operations preserve relatedness.
------------------------------------------------------------------------

open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; fmap∞; seqF∞; bindBlock)
open T∞ using (force)
open import Once.IR.Semantics.Trace using (ret; call; halt)
open import Once.Denotation.TraceMonadInfLaws using (RelS-bind; relS-ret; RelSB; module RelS; s-ret; s-next; s-call; s-halt)
open RelS using (forceS)

-- A larger relation relates more runs.
RelS-mono  : ∀ {X Y} {R R′ : X → Y → Set} → (∀ {a b} → R a b → R′ a b) → ∀ {m m′} → RelS R m m′ → RelS R′ m m′
RelSB-mono : ∀ {X Y} {R R′ : X → Y → Set} → (∀ {a b} → R a b → R′ a b) → ∀ {l l′} → RelSB R l l′ → RelSB R′ l l′
forceS (RelS-mono h r) = RelSB-mono h (forceS r)
RelSB-mono h (s-ret r)  = s-ret (h r)
RelSB-mono h (s-next r) = s-next (RelS-mono h r)
RelSB-mono h (s-call f) = s-call (λ b → RelSB-mono h (f b))
RelSB-mono h s-halt     = s-halt

RelS-fmap : ∀ {X Y X′ Y′} {R : X → X′ → Set} {R′ : Y → Y′ → Set} {m : T∞ X} {m′ : T∞ X′} {f : X → Y} {g : X′ → Y′}
          → RelS R m m′ → (∀ {a b} → R a b → R′ (f a) (g b)) → RelS R′ (fmap∞ f m) (fmap∞ g m′)
RelS-fmap h c = RelS-bind h (λ r → relS-ret (c r))

-- Mapping one side.
RelS-fmapˡ  : ∀ {X X′ Y} {R : X → Y → Set} {R′ : X′ → Y → Set} {f : X → X′} {m : T∞ X} {m′ : T∞ Y}
            → RelS R m m′ → (∀ {a b} → R a b → R′ (f a) b) → RelS R′ (fmap∞ f m) m′
RelSB-fmapˡ : ∀ {X X′ Y} {R : X → Y → Set} {R′ : X′ → Y → Set} {f : X → X′} {l l′}
            → RelSB R l l′ → (∀ {a b} → R a b → R′ (f a) b) → RelSB R′ (bindBlock l (λ x → return∞ (f x))) l′
forceS (RelS-fmapˡ r h) = RelSB-fmapˡ (forceS r) h
RelSB-fmapˡ (s-ret r)  h = s-ret (h r)
RelSB-fmapˡ (s-next r) h = s-next (RelS-fmapˡ r h)
RelSB-fmapˡ (s-call g) h = s-call (λ b → RelSB-fmapˡ (g b) h)
RelSB-fmapˡ s-halt     h = s-halt

-- Mapping the other side.
RelS-fmapʳ  : ∀ {X Y Y′} {R : X → Y → Set} {R′ : X → Y′ → Set} {g : Y → Y′} {m : T∞ X} {m′ : T∞ Y}
            → RelS R m m′ → (∀ {a b} → R a b → R′ a (g b)) → RelS R′ m (fmap∞ g m′)
RelSB-fmapʳ : ∀ {X Y Y′} {R : X → Y → Set} {R′ : X → Y′ → Set} {g : Y → Y′} {l l′}
            → RelSB R l l′ → (∀ {a b} → R a b → R′ a (g b)) → RelSB R′ l (bindBlock l′ (λ y → return∞ (g y)))
forceS (RelS-fmapʳ r h) = RelSB-fmapʳ (forceS r) h
RelSB-fmapʳ (s-ret r)  h = s-ret (h r)
RelSB-fmapʳ (s-next r) h = s-next (RelS-fmapʳ r h)
RelSB-fmapʳ (s-call g) h = s-call (λ b → RelSB-fmapʳ (g b) h)
RelSB-fmapʳ s-halt     h = s-halt

-- A bind of a bind, related to a bind: associativity, step for step. The
-- inner run's steps are the outer run's; once it returns, its continuation and
-- the next one run in sequence.
RelS-assocˡ  : ∀ {X Y Z W V} {R₀ : X → W → Set} {R : Z → V → Set} {m : T∞ X} {n : T∞ W}
                 {f : X → T∞ Y} {g : Y → T∞ Z} {k : W → T∞ V}
             → RelS R₀ m n → (∀ {a b} → R₀ a b → RelS R (f a >>=∞ g) (k b))
             → RelS R ((m >>=∞ f) >>=∞ g) (n >>=∞ k)
RelSB-assocˡ : ∀ {X Y Z W V} {R₀ : X → W → Set} {R : Z → V → Set} {l l′}
                 {f : X → T∞ Y} {g : Y → T∞ Z} {k : W → T∞ V}
             → RelSB R₀ l l′ → (∀ {a b} → R₀ a b → RelS R (f a >>=∞ g) (k b))
             → RelSB R (bindBlock (bindBlock l f) g) (bindBlock l′ k)
forceS (RelS-assocˡ h c) = RelSB-assocˡ (forceS h) c
RelSB-assocˡ (s-ret r)  c = forceS (c r)
RelSB-assocˡ (s-next h) c = s-next (RelS-assocˡ h c)
RelSB-assocˡ (s-call f) c = s-call (λ b → RelSB-assocˡ (f b) c)
RelSB-assocˡ s-halt     c = s-halt

-- The mirror image: a bind related to a bind of a bind.
RelS-assocʳ  : ∀ {X Y Z W V} {R₀ : W → X → Set} {R : V → Z → Set} {m : T∞ W} {n : T∞ X}
                 {f : X → T∞ Y} {g : Y → T∞ Z} {k : W → T∞ V}
             → RelS R₀ m n → (∀ {a b} → R₀ a b → RelS R (k a) (f b >>=∞ g))
             → RelS R (m >>=∞ k) ((n >>=∞ f) >>=∞ g)
RelSB-assocʳ : ∀ {X Y Z W V} {R₀ : W → X → Set} {R : V → Z → Set} {l l′}
                 {f : X → T∞ Y} {g : Y → T∞ Z} {k : W → T∞ V}
             → RelSB R₀ l l′ → (∀ {a b} → R₀ a b → RelS R (k a) (f b >>=∞ g))
             → RelSB R (bindBlock l k) (bindBlock (bindBlock l′ f) g)
forceS (RelS-assocʳ h c) = RelSB-assocʳ (forceS h) c
RelSB-assocʳ (s-ret r)  c = forceS (c r)
RelSB-assocʳ (s-next h) c = s-next (RelS-assocʳ h c)
RelSB-assocʳ (s-call f) c = s-call (λ b → RelSB-assocʳ (f b) c)
RelSB-assocʳ s-halt     c = s-halt

-- Both sides binds of binds.
RelS-assoc₂  : ∀ {X X′ Y Y′ Z Z′} {R₀ : X → X′ → Set} {R : Z → Z′ → Set} {m : T∞ X} {n : T∞ X′}
                 {f : X → T∞ Y} {g : Y → T∞ Z} {f′ : X′ → T∞ Y′} {g′ : Y′ → T∞ Z′}
             → RelS R₀ m n → (∀ {a b} → R₀ a b → RelS R (f a >>=∞ g) (f′ b >>=∞ g′))
             → RelS R ((m >>=∞ f) >>=∞ g) ((n >>=∞ f′) >>=∞ g′)
RelSB-assoc₂ : ∀ {X X′ Y Y′ Z Z′} {R₀ : X → X′ → Set} {R : Z → Z′ → Set} {l l′}
                 {f : X → T∞ Y} {g : Y → T∞ Z} {f′ : X′ → T∞ Y′} {g′ : Y′ → T∞ Z′}
             → RelSB R₀ l l′ → (∀ {a b} → R₀ a b → RelS R (f a >>=∞ g) (f′ b >>=∞ g′))
             → RelSB R (bindBlock (bindBlock l f) g) (bindBlock (bindBlock l′ f′) g′)
forceS (RelS-assoc₂ h c) = RelSB-assoc₂ (forceS h) c
RelSB-assoc₂ (s-ret r)  c = forceS (c r)
RelSB-assoc₂ (s-next h) c = s-next (RelS-assoc₂ h c)
RelSB-assoc₂ (s-call f) c = s-call (λ b → RelSB-assoc₂ (f b) c)
RelSB-assoc₂ s-halt     c = s-halt

-- A map on the right, read back into the relation.
RelS-unfmapʳ  : ∀ {X Y Y′} {R : X → Y′ → Set} {g : Y → Y′} {m : T∞ X} {n : T∞ Y}
              → RelS R m (fmap∞ g n) → RelS (λ a b → R a (g b)) m n
RelSB-unfmapʳ : ∀ {X Y Y′} {R : X → Y′ → Set} {g : Y → Y′} {l l′}
              → RelSB R l (bindBlock l′ (λ y → return∞ (g y))) → RelSB (λ a b → R a (g b)) l l′
forceS (RelS-unfmapʳ {n = n} h) = RelSB-unfmapʳ {l′ = force n} (forceS h)
RelSB-unfmapʳ {l′ = ret (inj₁ y)} (s-ret r)  = s-ret r
RelSB-unfmapʳ {l′ = ret (inj₂ n)} (s-next h) = s-next (RelS-unfmapʳ h)
RelSB-unfmapʳ {l′ = call o a k}   (s-call f) = s-call (λ b → RelSB-unfmapʳ {l′ = k b} (f b))
RelSB-unfmapʳ {l′ = halt o a}     s-halt     = s-halt

-- Two runs that force to the same block are interchangeable (a bind of a
-- returned value forces to its continuation, so this is how left identity is
-- used: by `refl`).
retargetˡ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y} → force m ≡ force m′ → RelS R m′ n → RelS R m n
forceS (retargetˡ e h) = subst (λ l → RelSB _ l _) (sym e) (forceS h)

retargetʳ : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {n n′ : T∞ Y} → force n ≡ force n′ → RelS R m n′ → RelS R m n
forceS (retargetʳ e h) = subst (RelSB _ _) (sym e) (forceS h)

-- A run transported along an equation of carriers.
RelS-substˡ : ∀ {X X′ Y} {R : X′ → Y → Set} (E : X ≡ X′) {m : T∞ X} {n : T∞ Y}
            → RelS (λ a b → R (subst (λ Z → Z) E a) b) m n → RelS R (subst T∞ E m) n
RelS-substˡ refl h = h

seqF∞-rel : ∀ {m} {X Y} {R : X → Y → Set} (G : Fun m) {l : ⟦ G ⟧F (T∞ X)} {l′ : ⟦ G ⟧F (T∞ Y)}
          → FRel (RelS R) G l l′ → RelS (FRel R G) (seqF∞ G l) (seqF∞ G l′)
seqF∞-rel (K A)   fr-K        = relS-ret fr-K
seqF∞-rel Id      (fr-Id r)   = RelS-mono fr-Id r
seqF∞-rel (G ⊕ H) (fr-inl r)  = RelS-fmap (seqF∞-rel G r) fr-inl
seqF∞-rel (G ⊕ H) (fr-inr r)  = RelS-fmap (seqF∞-rel H r) fr-inr
seqF∞-rel (G ⊗ H) (fr-pair r s) =
  RelS-bind (seqF∞-rel G r) (λ u → RelS-bind (seqF∞-rel H s) (λ v → relS-ret (fr-pair u v)))

------------------------------------------------------------------------
-- The functor coercions preserve relatedness (constants equal: base types).
------------------------------------------------------------------------

private
  fr-K≡ : ∀ {m} {X Y} {R : X → Y → Set} {A : Ty m} {x y} → x ≡ y → FRel R (K A) x y
  fr-K≡ refl = fr-K

cfD-rel : ∀ {m} {Δₖ : KCtx m} {F : Fun m} (wf : WFFun Δₖ F) (C : Ty m) {x y : ⟦ SpT.⟦ F ⟧F C ⟧ᴰ}
        → RelD (SpT.⟦ F ⟧F C) x y → FRel (RelD C) F (coerce-functor-D wf C x) (coerce-functor-D wf C y)
cfD-rel (wf-K b) C r = fr-K≡ (cong (forgetᵇ b) (base-eq b r))
cfD-rel wf-Id C r = fr-Id r
cfD-rel (wf-⊕ wf wg) C {inj₁ x} {inj₁ y} r = fr-inl (cfD-rel wf C r)
cfD-rel (wf-⊕ wf wg) C {inj₂ x} {inj₂ y} r = fr-inr (cfD-rel wg C r)
cfD-rel (wf-⊕ wf wg) C {inj₁ _} {inj₂ _} ()
cfD-rel (wf-⊕ wf wg) C {inj₂ _} {inj₁ _} ()
cfD-rel (wf-⊗ wf wg) C {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) = fr-pair (cfD-rel wf C r₁) (cfD-rel wg C r₂)

cfD⁻¹-rel : ∀ {m} {Δₖ : KCtx m} {F : Fun m} (wf : WFFun Δₖ F) (C : Ty m) {x y : ⟦ F ⟧F ⟦ C ⟧ᴰ}
          → FRel (RelD C) F x y → RelD (SpT.⟦ F ⟧F C) (coerce-functor⁻¹-D wf C x) (coerce-functor⁻¹-D wf C y)
cfD⁻¹-rel (wf-K b) C {x} fr-K = base-refl b (injectᵇ b x)
cfD⁻¹-rel wf-Id C (fr-Id r) = r
cfD⁻¹-rel (wf-⊕ wf wg) C (fr-inl r) = cfD⁻¹-rel wf C r
cfD⁻¹-rel (wf-⊕ wf wg) C (fr-inr r) = cfD⁻¹-rel wg C r
cfD⁻¹-rel (wf-⊗ wf wg) C (fr-pair r s) = cfD⁻¹-rel wf C r , cfD⁻¹-rel wg C s

------------------------------------------------------------------------
-- The source-functor ↔ semantic-functor coercions preserve relatedness.
------------------------------------------------------------------------

open import Once.IR.Semantics.Value Carrier Carrier using (coerce-μ-in; coerce-μ-out; coerce-full-to-base; coerce-base-to-full)

cμin-rel : ∀ {m} (F : Fun m) {X : Set} {R : X → X → Set} {x y : ⟦ F ⟧F X}
         → FRel R F x y → SRel R (translateF Carrier Carrier F) (coerce-μ-in F X x) (coerce-μ-in F X y)
cμin-rel (K A)   fr-K          = refl
cμin-rel Id      (fr-Id r)     = r
cμin-rel (F ⊕ G) (fr-inl r)    = cμin-rel F r
cμin-rel (F ⊕ G) (fr-inr r)    = cμin-rel G r
cμin-rel (F ⊗ G) (fr-pair r s) = cμin-rel F r , cμin-rel G s

cμout-rel : ∀ {m} {Δₖ : KCtx m} {F : Fun m} (wf : WFFun Δₖ F) {X : Set} {R : X → X → Set} {x y : ⟦ translateF Carrier Carrier F ⟧SF X}
          → SRel R (translateF Carrier Carrier F) x y → FRel R F (coerce-μ-out wf X x) (coerce-μ-out wf X y)
cμout-rel (wf-K pA) e = fr-K≡ (cong (coerce-base-to-full pA) e)
cμout-rel wf-Id r = fr-Id r
cμout-rel (wf-⊕ wf wg) {x = inj₁ x} {inj₁ y} r = fr-inl (cμout-rel wf r)
cμout-rel (wf-⊕ wf wg) {x = inj₂ x} {inj₂ y} r = fr-inr (cμout-rel wg r)
cμout-rel (wf-⊕ wf wg) {x = inj₁ _} {inj₂ _} ()
cμout-rel (wf-⊕ wf wg) {x = inj₂ _} {inj₁ _} ()
cμout-rel (wf-⊗ wf wg) {x = x₁ , x₂} {y₁ , y₂} (r , s) = fr-pair (cμout-rel wf r) (cμout-rel wg s)

------------------------------------------------------------------------
-- The fold: related algebras fold the same value to related results.
------------------------------------------------------------------------

open import Once.IR.Semantics.Polynomial using (cataS; sfmapCata)
open import Once.Spec.Polynomial using (μS; inS)

module _ {G : SFunctor} {A B : Set} {R : A → B → Set} {alg₁ : ⟦ G ⟧SF A → A} {alg₂ : ⟦ G ⟧SF B → B}
         (h : ∀ {l₁ l₂} → SRel R G l₁ l₂ → R (alg₁ l₁) (alg₂ l₂)) where
  cataS-rel      : ∀ (x : μS G) → R (cataS alg₁ x) (cataS alg₂ x)
  sfmapCata-rel  : ∀ (F : SFunctor) (x : ⟦ F ⟧SF (μS G)) → SRel R F (sfmapCata F alg₁ x) (sfmapCata F alg₂ x)
  cataS-rel (inS x) = h (sfmapCata-rel G x)
  sfmapCata-rel (SK B′)    x        = refl
  sfmapCata-rel SId        x        = cataS-rel x
  sfmapCata-rel (F S⊕ F′) (inj₁ x) = sfmapCata-rel F x
  sfmapCata-rel (F S⊕ F′) (inj₂ y) = sfmapCata-rel F′ y
  sfmapCata-rel (F S⊗ F′) (x , y)  = sfmapCata-rel F x , sfmapCata-rel F′ y

------------------------------------------------------------------------
-- The unfold: related coalgebras unfold related seeds to related streams.
------------------------------------------------------------------------

open import Once.IR.Semantics.StreamInf using (anaᴵ; anaRun; anaBlock; mapAnaᴵ)
open import Once.IR.Semantics.Trace using (T)
open StreamRel

module _ {H : SFunctor} {A B : Set} {RA : A → B → Set} {c₁ : A → T∞ (⟦ H ⟧SF A)} {c₂ : B → T∞ (⟦ H ⟧SF B)}
         (hc : ∀ {a b} → RA a b → RelS (SRel RA H) (c₁ a) (c₂ b)) where
  anaᴵ-rel     : ∀ {a b} → RA a b → StreamRel H (anaᴵ H c₁ a) (anaᴵ H c₂ b)
  anaRun-rel   : ∀ {m₁ m₂} → RelS (SRel RA H) m₁ m₂ → RelS (LayerRel H H) (anaRun H c₁ m₁) (anaRun H c₂ m₂)
  anaBlock-rel : ∀ {b₁ b₂} → RelSB (SRel RA H) b₁ b₂ → RelSB (LayerRel H H) (anaBlock H c₁ b₁) (anaBlock H c₂ b₂)
  mapAna-rel   : ∀ (G : SFunctor) {l₁ l₂} → SRel RA G l₁ l₂ → LayerRel H G (mapAnaᴵ H G c₁ l₁) (mapAnaᴵ H G c₂ l₂)
  forceR (anaᴵ-rel r) = anaRun-rel (hc r)
  forceS (anaRun-rel r) = anaBlock-rel (forceS r)
  anaBlock-rel (s-ret r)  = s-ret (mapAna-rel H r)
  anaBlock-rel (s-next r) = s-next (anaRun-rel r)
  anaBlock-rel (s-call f) = s-call (λ v → anaBlock-rel (f v))
  anaBlock-rel s-halt     = s-halt
  mapAna-rel (SK B′)    e = e
  mapAna-rel SId        r = anaᴵ-rel r
  mapAna-rel (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} r = mapAna-rel G₁ r
  mapAna-rel (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} r = mapAna-rel G₂ r
  mapAna-rel (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
  mapAna-rel (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
  mapAna-rel (G₁ S⊗ G₂) {_ , _} {_ , _} (r , s) = mapAna-rel G₁ r , mapAna-rel G₂ s

------------------------------------------------------------------------
-- The fold of a source functor (`sem-cata`), and the stream constructor.
------------------------------------------------------------------------

open import Once.IR.Semantics.Value Carrier Carrier using (sem-cata)
open import Once.IR.Semantics.StreamInf using (in-νᴵ)

sem-cata-rel : ∀ {m} {Δₖ : KCtx m} {F : Fun m} (wf : WFFun Δₖ F) {A : Set} {R : A → A → Set} {alg₁ alg₂ : ⟦ F ⟧F A → A}
             → (∀ {l₁ l₂} → FRel R F l₁ l₂ → R (alg₁ l₁) (alg₂ l₂))
             → ∀ x → R (sem-cata wf alg₁ x) (sem-cata wf alg₂ x)
sem-cata-rel wf h x = cataS-rel (λ sr → h (cμout-rel wf sr)) x

-- A stream layer's relation IS the lifted stream relation.
layer→srel : ∀ {H} (G : SFunctor) {l l′} → LayerRel H G l l′ → SRel (StreamRel H) G l l′
layer→srel (SK B)     e = e
layer→srel SId        r = r
layer→srel (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} r = layer→srel G₁ r
layer→srel (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} r = layer→srel G₂ r
layer→srel (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
layer→srel (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
layer→srel (G₁ S⊗ G₂) {_ , _} {_ , _} (r , s) = layer→srel G₁ r , layer→srel G₂ s

srel→layer : ∀ {H} (G : SFunctor) {l l′} → SRel (StreamRel H) G l l′ → LayerRel H G l l′
srel→layer (SK B)     e = e
srel→layer SId        r = r
srel→layer (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} r = srel→layer G₁ r
srel→layer (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} r = srel→layer G₂ r
srel→layer (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
srel→layer (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
srel→layer (G₁ S⊗ G₂) {_ , _} {_ , _} (r , s) = srel→layer G₁ r , srel→layer G₂ s

in-rel : ∀ {H} {l l′ : ⟦ H ⟧SF (νᴵ H)} → SRel (StreamRel H) H l l′ → StreamRel H (in-νᴵ l) (in-νᴵ l′)
forceS (forceR (in-rel {H} r)) = s-ret (srel→layer H r)
