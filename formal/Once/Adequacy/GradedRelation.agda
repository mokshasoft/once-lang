{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.GradedRelation — the logical relation between the Spec's
-- meaning (`Spec.Domain Σ`, graded by `Spec.Effect Σ`) and the purity-blind
-- Kleisli implementation meaning (`⟦_⟧ᴰ`, SD and the IR's `evalᴰ`). Plan
-- 0.104 A.6; plan 0.122 §5.5 M1: against the Spec's own domain.
--
-- HETEROGENEOUS: the two sides are different sets at a pure arrow (a total
-- function against a Kleisli one), at `μ` (the Spec's polynomial data against
-- the machine's, layer by layer) and at `ν` (the Spec's streams against
-- suspensions of runs). A Spec computation at grade `π` is compared with the
-- implementation's run after its lift into `T∞` (`toT∞`), step for step, a
-- call of Σ's declaration against the implementation's call of its name
-- (`SpecRun`). The implementation's closure is also related to itself
-- (`RelD`) — the PER condition (plan 0.119 D5).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

open import Once.Spec.Type using (TySub)

module Once.Adequacy.GradedRelation (Σ : Signature) (σ : TySub 0 0) where

open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Once.Denotation.PureBind using (_>>=ᵖ_; >>=ᵖ-β)

open import Once.Spec.Grade using (Purity; pure; act; eff; mk-kind; Zero; One; Many; pureᶠ; actᶠ)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-pe; ⊑-pa)
open import Once.Spec.Type using (_⟨_⟩; _⟨_⟩F; Type; Fun; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_)
open import Once.Spec.Word using (Carrier)
import Once.Internal.Polynomial as LPoly
import Once.Spec.Polynomial as SPoly
open import Once.Internal.FunctorMeaning using (translateF; ⟦_,_⟧-base)
import Once.Internal.Trace as LTr
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞)
import Once.Internal.Iterative as LI
open import Once.Internal.StreamInf using (νᴵ; module νᴵ)
open νᴵ using (forceᴵ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt)
open RelS using (forceS)
open import Once.Denotation.ValueRel using (RelD; StreamRel; LayerRel)
open import Once.Denotation.ValueRelPER using (RelD-leftself)
open StreamRel using () renaming (forceR to forceSR)
import Once.Spec.Effect Σ as SE
open SE.νM using (outν)
import Once.Spec.Domain Σ as SD
open import Once.Type.Core using (wk₀)
open import Once.Weaken using (wk₀-id; ⟦wk₀⟧ᴰ)
open import Once.Denotation.SpecDomain Σ σ using (⟦wk₀⟧ᵛ)
open import Once.Adequacy.SpecRun Σ
  using (RunR; BlockR; ret; call; halt; SumR; left; right; return∞-R; bind∞-R; embed-R; embed-bind-R; bindT-R; mapT-R; BlockR-mono; RunR-mono; CallR; cr)
open RunR using (forceR)
import Once.Adequacy.SpecInterp as SI

------------------------------------------------------------------------
-- Layers and data: a functor's constant (a base value) the same on both
-- sides, its recursive positions related.
------------------------------------------------------------------------

BR : (A : Type) → SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ Carrier , Carrier ⟧-base A → Set
BR Unit    _ _ = ⊤
BR Void    () _
BR Int     x y = x ≡ y
BR Float   x y = x ≡ y
BR (A * B) (x , x′) (y , y′) = BR A x y × BR B x′ y′
BR (A + B) (inj₁ x) (inj₁ y) = BR A x y
BR (A + B) (inj₂ x) (inj₂ y) = BR B x y
BR (A + B) (inj₁ _) (inj₂ _) = ⊥
BR (A + B) (inj₂ _) (inj₁ _) = ⊥
BR (_ ⇒[ _ ] _) _ _ = ⊤
BR (μ _)   _ _ = ⊤
BR (ν _ _) _ _ = ⊤

LayerR : ∀ (F : Fun 0) {X Y : Set} → (X → Y → Set)
       → SPoly.⟦ SD.code (F ⟨ σ ⟩F) ⟧SF X → SPoly.⟦ translateF Carrier Carrier F ⟧SF Y → Set
LayerR (K A)   R x y = BR A x y
LayerR Id      R x y = R x y
LayerR (F ⊕ G) R (inj₁ x) (inj₁ y) = LayerR F R x y
LayerR (F ⊕ G) R (inj₂ x) (inj₂ y) = LayerR G R x y
LayerR (F ⊕ G) R (inj₁ _) (inj₂ _) = ⊥
LayerR (F ⊕ G) R (inj₂ _) (inj₁ _) = ⊥
LayerR (F ⊗ G) R (x , x′) (y , y′) = LayerR F R x y × LayerR G R x′ y′

data μR (F : Fun 0) : SPoly.μS (SD.code (F ⟨ σ ⟩F)) → SPoly.μS (translateF Carrier Carrier F) → Set where
  inR : ∀ {x y} → LayerR F (μR F) x y → μR F (SPoly.inS x) (SPoly.inS y)

------------------------------------------------------------------------
-- Codata: the Spec's streams against the IR's (whose layers are `T∞` runs).
------------------------------------------------------------------------

-- A pure stream's layer is there at once: the IR's force returns a related
-- layer, silently.
record _∼ᵖᵈ_ {F : Fun 0} (x : SE.νM pureᶠ (SD.code (F ⟨ σ ⟩F))) (y : νᴵ (translateF Carrier Carrier F)) : Set where
  coinductive
  field
    force-∼ᵖᵈ : RunR (LayerR F (_∼ᵖᵈ_ {F})) (SE.return∞ (outν x)) (forceᴵ y)

open _∼ᵖᵈ_

-- An `act` stream's layer is a finite block: the IR's force makes the same
-- calls, step for step, ending in a related layer.
record _∼ᵈ_ {F : Fun 0} (x : SE.νM actᶠ (SD.code (F ⟨ σ ⟩F))) (y : νᴵ (translateF Carrier Carrier F)) : Set where
  coinductive
  field
    force-∼ : RunR (LayerR F (_∼ᵈ_ {F})) (SE.embed (outν x)) (forceᴵ y)

open _∼ᵈ_

------------------------------------------------------------------------
-- The relation, by recursion on the type.
------------------------------------------------------------------------

RelGV : (A : Type) → SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → ⟦ A ⟧ᴰ → Set

-- A grade-`π` Spec meaning against the IR's run: its lift into `T∞`, step for
-- step.
RelGM : (π : Purity) (A : Type) → SE.M π SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → T∞ ⟦ A ⟧ᴰ → Set
RelGM π A m t = RunR (RelGV A) (SE.toT∞ π m) t

-- A finite block against the IR's run.
RelGT : (A : Type) → SE.T SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → T∞ ⟦ A ⟧ᴰ → Set
RelGT A t₁ t₂ = RelGM act A t₁ t₂

RelGV Unit        _ _ = ⊤
RelGV Void        () _
RelGV Int         x y = x ≡ y
RelGV Float       x y = x ≡ y
RelGV (μ F)       x y = μR F x y
RelGV (ν F pureᶠ) x y = x ∼ᵖᵈ y
RelGV (ν F actᶠ)  x y = x ∼ᵈ y
RelGV (A * B) (a₁ , b₁) (a₂ , b₂) = RelGV A a₁ a₂ × RelGV B b₁ b₂
RelGV (A + B) (inj₁ a₁) (inj₁ a₂) = RelGV A a₁ a₂
RelGV (A + B) (inj₂ b₁) (inj₂ b₂) = RelGV B b₁ b₂
RelGV (A + B) (inj₁ _)  (inj₂ _)  = ⊥
RelGV (A + B) (inj₂ _)  (inj₁ _)  = ⊥
-- The arrow: related arguments to related results AT THE ARROW'S GRADE. A pure
-- arrow's Kleisli twin must answer silently with a related value. The
-- implementation's closure is also related to itself (`RelD`): an
-- implementation related to it (the IR, which `faithful` relates to the
-- source) then inherits the relation (`GV-D`).
RelGV (A ⇒[ mk-kind Zero π ] B) f g = RelGM π B (f tt) (g tt) × RelD (A ⇒[ mk-kind Zero π ] B) g g
RelGV (A ⇒[ mk-kind One  π ] B) f g = (∀ {a b} → RelGV A a b → RelGM π B (f a) (g b)) × RelD (A ⇒[ mk-kind One π ] B) g g
RelGV (A ⇒[ mk-kind Many π ] B) f g = (∀ {a b} → RelGV A a b → RelGM π B (f a) (g b)) × RelD (A ⇒[ mk-kind Many π ] B) g g

------------------------------------------------------------------------
-- The monad lemmas, at any relation of the results (`RelM`), and at the
-- relation of a type (`RelGM`).
------------------------------------------------------------------------

RelM : ∀ (π : Purity) {X Y : Set} → (X → Y → Set) → SE.M π X → T∞ Y → Set
RelM π R m t = RunR R (SE.toT∞ π m) t

RelM-return : ∀ π {X Y : Set} {R : X → Y → Set} {x y} → R x y → RelM π R (SE.return π x) (return∞ y)
RelM-return pure r = return∞-R r
forceR (RelM-return act r) = ret (left r)
RelM-return eff r = return∞-R r

module _ {X X′ Y Y′ : Set} {R : X → Y → Set} {S : X′ → Y′ → Set} where

  -- The pure bind (application) against the IR's: the IR's run returns a
  -- related value at once, which the continuation receives.
  RelMᵖ-app : ∀ {m t} {k : X → X′} {g : Y → T∞ Y′}
            → RelM pure R m t → (∀ {x y} → R x y → RelM pure S (k x) (g y)) → RelM pure S (k m) (t >>=∞ g)
  forceR (RelMᵖ-app {k = k} rt rk) = forceR (bind∞-R {k = λ a → SE.return∞ (k a)} rk rt)

  RelM-bind : ∀ π {m t} {k : X → SE.M π X′} {g : Y → T∞ Y′}
            → RelM π R m t → (∀ {x y} → R x y → RelM π S (k x) (g y)) → RelM π S (SE.bind π m k) (t >>=∞ g)
  RelM-bind pure rm rk = RelMᵖ-app rm rk
  RelM-bind act {m = m} rm rk = embed-bind-R rk m rm
  RelM-bind eff rm rk = bind∞-R rk rm

  RelM-fmap : ∀ π {m t} {f : X → X′} {g : Y → Y′}
            → RelM π R m t → (∀ {x y} → R x y → S (f x) (g y)) → RelM π S (SE.fmap π f m) (fmap∞ g t)
  RelM-fmap pure {f = f} rm h = RelMᵖ-app {k = f} rm (λ r → return∞-R (h r))
  RelM-fmap act  rm h = RelM-bind act rm (λ r → RelM-return act (h r))
  RelM-fmap eff  rm h = bind∞-R (λ r → return∞-R (h r)) rm

RelGT-return : ∀ {A : Type} {x y} → RelGV A x y → RelGT A (SE.returnT x) (return∞ y)
RelGT-return {A} = RelM-return act {R = RelGV A}

RelGT-bind : ∀ {A B : Type} {t₁ : SE.T SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {f : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → SE.T SD.⟦ B ⟨ σ ⟩ ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
           → RelGT A t₁ t₂
           → (∀ {a b} → RelGV A a b → RelGT B (f a) (g b))
           → RelGT B (t₁ SE.>>=T f) (t₂ >>=∞ g)
RelGT-bind {A} {B} = RelM-bind {R = RelGV A} {S = RelGV B} act

-- The PURE bind (`_>>=ᵖ_`, application kept opaque) against the IR's.
RelGᵖ-bind : ∀ {A B : Type} {m : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {k : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → SD.⟦ B ⟨ σ ⟩ ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
           → RelGM pure A m t₂
           → (∀ {a b} → RelGV A a b → RelGM pure B (k a) (g b))
           → RelGM pure B (m >>=ᵖ k) (t₂ >>=∞ g)
RelGᵖ-bind {A} {B} {m} {t₂} {k} {g} rt rk =
  subst (λ z → RelGM pure B z (t₂ >>=∞ g)) (sym (>>=ᵖ-β m k)) (RelMᵖ-app {R = RelGV A} {S = RelGV B} {k = k} rt rk)

-- A pure meaning fed to a continuation directly, against the IR's bind.
RelGᵖ-app : ∀ {A B : Type} {m : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {k : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → SD.⟦ B ⟨ σ ⟩ ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
          → RelGM pure A m t₂
          → (∀ {a b} → RelGV A a b → RelGM pure B (k a) (g b))
          → RelGM pure B (k m) (t₂ >>=∞ g)
RelGᵖ-app {A} {B} {k = k} = RelMᵖ-app {R = RelGV A} {S = RelGV B} {k = k}

-- A pure bind feeding any continuation: the IR's run returns a related value
-- at once, which the continuation receives.
RelGᵖᵉ-bind : ∀ {A B : Type} {X : Set} {P : X → T∞ ⟦ B ⟧ᴰ → Set} {m : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {k : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → X} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
            → RelGM pure A m t₂
            → (∀ {a b} → RelGV A a b → P (k a) (g b))
            → (∀ {x t t′} → LI.T∞.force t ≡ LI.T∞.force t′ → P x t′ → P x t)
            → P (m >>=ᵖ k) (t₂ >>=∞ g)
RelGᵖᵉ-bind {A = A} {P = P} {m} {t₂} {k} {g} rt rk tr =
  subst (λ z → P z (t₂ >>=∞ g)) (sym (>>=ᵖ-β m k)) (go (LI.T∞.force t₂) refl (forceR rt))
  where
    go : ∀ b → LI.T∞.force t₂ ≡ b → BlockR (SumR (RelGV A) (RunR (RelGV A))) (SE.roll (SE.done (inj₁ m))) b → P (k m) (t₂ >>=∞ g)
    go .(LTr.ret (inj₁ _)) e (ret (left {y = y} r)) = tr (cong (λ bl → LI.bindBlock bl g) e) (rk r)

-- The two, at any grade.
RelGM-bind : ∀ π {A B : Type} {m : SE.M π SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {k : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → SE.M π SD.⟦ B ⟨ σ ⟩ ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
           → RelGM π A m t₂
           → (∀ {a b} → RelGV A a b → RelGM π B (k a) (g b))
           → RelGM π B (SE.bind π m k) (t₂ >>=∞ g)
RelGM-bind π {A} {B} = RelM-bind {R = RelGV A} {S = RelGV B} π

-- The graded map: both sides map their result along related functions.
RelGM-fmap : ∀ π {A B : Type} {m : SE.M π SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ} {f : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ → SD.⟦ B ⟨ σ ⟩ ⟧ᵛ} {g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ}
           → RelGM π A m t
           → (∀ {a b} → RelGV A a b → RelGV B (f a) (g b))
           → RelGM π B (SE.fmap π f m) (fmap∞ g t)
RelGM-fmap π {A} {B} = RelM-fmap {R = RelGV A} {S = RelGV B} π

-- A pure value, embedded at a grade with a unit.
RelGM-return : ∀ {π} (u : pure ⊑π π) {A : Type} {x y} → RelGV A x y → RelGM π A (SE.sub u x) (return∞ y)
RelGM-return ⊑-pure rv = return∞-R rv
RelGM-return ⊑-pa {A} rv = RelGT-return {A = A} rv
RelGM-return ⊑-pe   rv = return∞-R rv

-- A pure meaning, embedded at any grade (what a lambda's body is, D250).
RelGM-ret : ∀ {π} (u : pure ⊑π π) {B : Type} {v : SD.⟦ B ⟨ σ ⟩ ⟧ᵛ} {t : T∞ ⟦ B ⟧ᴰ} → RelGM pure B v t → RelGM π B (SE.sub u v) t
RelGM-ret ⊑-pure r = r
forceR (RelGM-ret ⊑-pa r) = forceR r
RelGM-ret ⊑-pe   r = r

------------------------------------------------------------------------
-- `pure ⊑ act` at ν: the Spec's subeffect of a pure stream keeps it related.
------------------------------------------------------------------------

private
  emb : (G : SPoly.SFunctor) → SE.νM pureᶠ G → SE.T (SPoly.⟦ G ⟧SF (SE.νM pureᶠ G))
  emb G u = SE.returnT (outν u)

mutual
  embνᵃ-∼ : ∀ {F : Fun 0} {x : SE.νM pureᶠ (SD.code (F ⟨ σ ⟩F))} {y : νᴵ (translateF Carrier Carrier F)}
          → x ∼ᵖᵈ y → SD.subν ⊑-pa (SD.code (F ⟨ σ ⟩F)) x ∼ᵈ y
  force-∼ (embνᵃ-∼ {F} r) = embLayerᵃ F (force-∼ᵖᵈ r)

  embLayerᵃ : ∀ (F : Fun 0) {l : SPoly.⟦ SD.code (F ⟨ σ ⟩F) ⟧SF (SE.νM pureᶠ (SD.code (F ⟨ σ ⟩F)))} {n}
            → RunR (LayerR F (_∼ᵖᵈ_ {F})) (SE.return∞ l) n
            → RunR (LayerR F (_∼ᵈ_ {F})) (SE.embed (SE.returnT (SE.mapA (SD.code (F ⟨ σ ⟩F)) (SD.code (F ⟨ σ ⟩F)) (emb (SD.code (F ⟨ σ ⟩F))) l))) n
  forceR (embLayerᵃ F r) = embLayerBᵃ F (forceR r)

  embLayerBᵃ : ∀ (F : Fun 0) {l : SPoly.⟦ SD.code (F ⟨ σ ⟩F) ⟧SF (SE.νM pureᶠ (SD.code (F ⟨ σ ⟩F)))} {b}
             → BlockR (SumR (LayerR F (_∼ᵖᵈ_ {F})) (RunR (LayerR F (_∼ᵖᵈ_ {F})))) (SE.roll (SE.done (inj₁ l))) b
             → BlockR (SumR (LayerR F (_∼ᵈ_ {F})) (RunR (LayerR F (_∼ᵈ_ {F}))))
                      (SE.roll (SE.done (inj₁ (SE.mapA (SD.code (F ⟨ σ ⟩F)) (SD.code (F ⟨ σ ⟩F)) (emb (SD.code (F ⟨ σ ⟩F))) l)))) b
  embLayerBᵃ F (ret (left rr)) = ret (left (mapEmbνᵃ-∼ F F rr))

  mapEmbνᵃ-∼ : ∀ (F G : Fun 0) {l : SPoly.⟦ SD.code (G ⟨ σ ⟩F) ⟧SF (SE.νM pureᶠ (SD.code (F ⟨ σ ⟩F)))} {l′}
             → LayerR G (_∼ᵖᵈ_ {F}) l l′ → LayerR G (_∼ᵈ_ {F}) (SE.mapA (SD.code (F ⟨ σ ⟩F)) (SD.code (G ⟨ σ ⟩F)) (emb (SD.code (F ⟨ σ ⟩F))) l) l′
  mapEmbνᵃ-∼ F (K A)     r = r
  mapEmbνᵃ-∼ F Id        r = embνᵃ-∼ r
  mapEmbνᵃ-∼ F (G₁ ⊕ G₂) {inj₁ _} {inj₁ _} r = mapEmbνᵃ-∼ F G₁ r
  mapEmbνᵃ-∼ F (G₁ ⊕ G₂) {inj₂ _} {inj₂ _} r = mapEmbνᵃ-∼ F G₂ r
  mapEmbνᵃ-∼ F (G₁ ⊗ G₂) {_ , _} {_ , _} (r₁ , r₂) = mapEmbνᵃ-∼ F G₁ r₁ , mapEmbνᵃ-∼ F G₂ r₂

------------------------------------------------------------------------
-- The implementation side is self-related, and the relation transfers along
-- `RelD` on the implementation side (plan 0.119 D5).
------------------------------------------------------------------------

-- Two relations meet at the implementation side: a Spec run related to `s`,
-- and an implementation run `RelS`-related to `s`.
module _ {X Y : Set} {R : X → Y → Set} {D : Y → Y → Set} where

  Meet : X → Y → Set
  Meet x i = Σ-syntax Y (λ s → R x s × D i s)

  run-meet  : ∀ {m s i} → RunR R m s → RelS D i s → RunR Meet m i
  runB-meet : ∀ {b s i} → BlockR (SumR R (RunR R)) b s → RelSB D i s → BlockR (SumR Meet (RunR Meet)) b i
  forceR (run-meet r d) = runB-meet (forceR r) (forceS d)
  runB-meet (ret (left r))  (s-ret d)  = ret (left (_ , r , d))
  runB-meet (ret (right r)) (s-next d) = ret (right (run-meet r d))
  runB-meet (call c a k)    (s-call f) = call c a (λ {b} {b′} e → runB-meet (k e) (f b′))
  runB-meet (halt x a)      s-halt     = halt x a

-- Streams. A Spec stream's IR twin is self-related; and an IR stream related
-- to the twin is a twin too.
module _ {F : Fun 0} where
  private
    H : SPoly.SFunctor
    H = translateF Carrier Carrier F
    Lp = LayerR F (_∼ᵖᵈ_ {F})
    La = LayerR F (_∼ᵈ_ {F})

  pd-self   : ∀ {x y} → x ∼ᵖᵈ y → StreamRel H y y
  pd-run    : ∀ {m n} → RunR Lp m n → RelS (LayerRel H H) n n
  pd-block  : ∀ {b b′} → BlockR (SumR Lp (RunR Lp)) b b′ → RelSB (LayerRel H H) b′ b′
  pd-layer  : ∀ (G : Fun 0) {l l′} → LayerR G (_∼ᵖᵈ_ {F}) l l′ → LayerRel H (translateF Carrier Carrier G) l′ l′
  forceSR (pd-self r) = pd-run (force-∼ᵖᵈ r)
  forceS (pd-run r) = pd-block (forceR r)
  pd-block (ret (left r))  = s-ret (pd-layer F r)
  pd-block (ret (right r)) = s-next (pd-run r)
  pd-block (call (cr {b = b} m ne) a k) = s-call (λ x → pd-block (k (sym (SI.fromB-toB b x))))
  pd-block (halt x a)      = s-halt
  pd-layer (K A)     e = refl
  pd-layer Id        r = pd-self r
  pd-layer (G₁ ⊕ G₂) {inj₁ _} {inj₁ _} r = pd-layer G₁ r
  pd-layer (G₁ ⊕ G₂) {inj₂ _} {inj₂ _} r = pd-layer G₂ r
  pd-layer (G₁ ⊗ G₂) {_ , _} {_ , _} (r , s) = pd-layer G₁ r , pd-layer G₂ s

  ad-self   : ∀ {x y} → x ∼ᵈ y → StreamRel H y y
  ad-run    : ∀ {m n} → RunR La m n → RelS (LayerRel H H) n n
  ad-block  : ∀ {b b′} → BlockR (SumR La (RunR La)) b b′ → RelSB (LayerRel H H) b′ b′
  ad-layer  : ∀ (G : Fun 0) {l l′} → LayerR G (_∼ᵈ_ {F}) l l′ → LayerRel H (translateF Carrier Carrier G) l′ l′
  forceSR (ad-self r) = ad-run (force-∼ r)
  forceS (ad-run r) = ad-block (forceR r)
  ad-block (ret (left r))  = s-ret (ad-layer F r)
  ad-block (ret (right r)) = s-next (ad-run r)
  ad-block (call (cr {b = b} m ne) a k) = s-call (λ x → ad-block (k (sym (SI.fromB-toB b x))))
  ad-block (halt x a)      = s-halt
  ad-layer (K A)     e = refl
  ad-layer Id        r = ad-self r
  ad-layer (G₁ ⊕ G₂) {inj₁ _} {inj₁ _} r = ad-layer G₁ r
  ad-layer (G₁ ⊕ G₂) {inj₂ _} {inj₂ _} r = ad-layer G₂ r
  ad-layer (G₁ ⊗ G₂) {_ , _} {_ , _} (r , s) = ad-layer G₁ r , ad-layer G₂ s

  pd-D       : ∀ {x s i} → x ∼ᵖᵈ s → StreamRel H i s → x ∼ᵖᵈ i
  pd-D-run   : ∀ {m n n′} → RunR Lp m n → RelS (LayerRel H H) n′ n → RunR Lp m n′
  pd-D-block : ∀ {b l′ l″} → BlockR (SumR Lp (RunR Lp)) b l′ → RelSB (LayerRel H H) l″ l′ → BlockR (SumR Lp (RunR Lp)) b l″
  pd-D-layer : ∀ (G : Fun 0) {l l′ l″} → LayerR G (_∼ᵖᵈ_ {F}) l l′ → LayerRel H (translateF Carrier Carrier G) l″ l′
             → LayerR G (_∼ᵖᵈ_ {F}) l l″
  force-∼ᵖᵈ (pd-D r d) = pd-D-run (force-∼ᵖᵈ r) (forceSR d)
  forceR (pd-D-run r d) = pd-D-block (forceR r) (forceS d)
  pd-D-block (ret (left r))  (s-ret d)  = ret (left (pd-D-layer F r d))
  pd-D-block (ret (right r)) (s-next d) = ret (right (pd-D-run r d))
  pd-D-block (call c a k)    (s-call g) = call c a (λ {b} {b′} e → pd-D-block (k e) (g b′))
  pd-D-block (halt x a)      s-halt     = halt x a
  pd-D-layer (K A) {l} e e′ = subst (BR A l) (sym e′) e
  pd-D-layer Id        r d  = pd-D r d
  pd-D-layer (G₁ ⊕ G₂) {inj₁ _} {inj₁ _} {inj₁ _} r d = pd-D-layer G₁ r d
  pd-D-layer (G₁ ⊕ G₂) {inj₂ _} {inj₂ _} {inj₂ _} r d = pd-D-layer G₂ r d
  pd-D-layer (G₁ ⊕ G₂) {_} {inj₁ _} {inj₂ _} _ ()
  pd-D-layer (G₁ ⊕ G₂) {_} {inj₂ _} {inj₁ _} _ ()
  pd-D-layer (G₁ ⊗ G₂) {_ , _} {_ , _} {_ , _} (r , s) (d , d′) = pd-D-layer G₁ r d , pd-D-layer G₂ s d′

  ad-D       : ∀ {x s i} → x ∼ᵈ s → StreamRel H i s → x ∼ᵈ i
  ad-D-run   : ∀ {m n n′} → RunR La m n → RelS (LayerRel H H) n′ n → RunR La m n′
  ad-D-block : ∀ {b l′ l″} → BlockR (SumR La (RunR La)) b l′ → RelSB (LayerRel H H) l″ l′ → BlockR (SumR La (RunR La)) b l″
  ad-D-layer : ∀ (G : Fun 0) {l l′ l″} → LayerR G (_∼ᵈ_ {F}) l l′ → LayerRel H (translateF Carrier Carrier G) l″ l′
             → LayerR G (_∼ᵈ_ {F}) l l″
  force-∼ (ad-D r d) = ad-D-run (force-∼ r) (forceSR d)
  forceR (ad-D-run r d) = ad-D-block (forceR r) (forceS d)
  ad-D-block (ret (left r))  (s-ret d)  = ret (left (ad-D-layer F r d))
  ad-D-block (ret (right r)) (s-next d) = ret (right (ad-D-run r d))
  ad-D-block (call c a k)    (s-call g) = call c a (λ {b} {b′} e → ad-D-block (k e) (g b′))
  ad-D-block (halt x a)      s-halt     = halt x a
  ad-D-layer (K A) {l} e e′ = subst (BR A l) (sym e′) e
  ad-D-layer Id        r d  = ad-D r d
  ad-D-layer (G₁ ⊕ G₂) {inj₁ _} {inj₁ _} {inj₁ _} r d = ad-D-layer G₁ r d
  ad-D-layer (G₁ ⊕ G₂) {inj₂ _} {inj₂ _} {inj₂ _} r d = ad-D-layer G₂ r d
  ad-D-layer (G₁ ⊕ G₂) {_} {inj₁ _} {inj₂ _} _ ()
  ad-D-layer (G₁ ⊕ G₂) {_} {inj₂ _} {inj₁ _} _ ()
  ad-D-layer (G₁ ⊗ G₂) {_ , _} {_ , _} {_ , _} (r , s) (d , d′) = ad-D-layer G₁ r d , ad-D-layer G₂ s d′

-- The implementation side of a related pair is related to itself.
right-self : ∀ (A : Type) {x : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {y : ⟦ A ⟧ᴰ} → RelGV A x y → RelD A y y
right-self Unit r = tt
right-self Void {()}
right-self Int r = refl
right-self Float r = refl
right-self (μ F) r = refl
right-self (ν F pureᶠ) r = pd-self r
right-self (ν F actᶠ) r = ad-self r
right-self (A * B) {_ , _} {_ , _} (r , s) = right-self A r , right-self B s
right-self (A + B) {inj₁ _} {inj₁ _} r = right-self A r
right-self (A + B) {inj₂ _} {inj₂ _} r = right-self B r
right-self (A ⇒[ mk-kind Zero π ] B) (_ , d) = d
right-self (A ⇒[ mk-kind One π ] B) (_ , d) = d
right-self (A ⇒[ mk-kind Many π ] B) (_ , d) = d

-- An implementation related (`RelD`) to a Spec meaning's twin is a twin too.
mutual
  GV-D : ∀ (A : Type) {c : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {s i : ⟦ A ⟧ᴰ} → RelGV A c s → RelD A i s → RelGV A c i
  GV-D Unit r d = tt
  GV-D Void {()}
  GV-D Int r d = trans r (sym d)
  GV-D Float r d = trans r (sym d)
  GV-D (μ F) {c} r d = subst (μR F c) (sym d) r
  GV-D (ν F pureᶠ) r d = pd-D r d
  GV-D (ν F actᶠ) r d = ad-D r d
  GV-D (A * B) {_ , _} {_ , _} {_ , _} (r , s) (d , d′) = GV-D A r d , GV-D B s d′
  GV-D (A + B) {inj₁ _} {inj₁ _} {inj₁ _} r d = GV-D A r d
  GV-D (A + B) {inj₂ _} {inj₂ _} {inj₂ _} r d = GV-D B r d
  GV-D (A + B) {inj₁ _} {inj₁ _} {inj₂ _} _ ()
  GV-D (A + B) {inj₂ _} {inj₂ _} {inj₁ _} _ ()
  GV-D (A ⇒[ mk-kind Zero π ] B) (h , _) d = GM-D π B h d , RelD-leftself (A ⇒[ mk-kind Zero π ] B) d
  GV-D (A ⇒[ mk-kind One π ] B) (h , _) d =
    (λ rab → GM-D π B (h rab) (d (right-self A rab))) , RelD-leftself (A ⇒[ mk-kind One π ] B) d
  GV-D (A ⇒[ mk-kind Many π ] B) (h , _) d =
    (λ rab → GM-D π B (h rab) (d (right-self A rab))) , RelD-leftself (A ⇒[ mk-kind Many π ] B) d

  GM-D : ∀ (π : Purity) (A : Type) {m : SE.M π SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {s i : T∞ ⟦ A ⟧ᴰ} → RelGM π A m s → RelS (RelD A) i s → RelGM π A m i
  GM-D π A r d = RunR-mono (λ { (_ , gv , dv) → GV-D A gv dv }) (run-meet r d)

------------------------------------------------------------------------
-- At the ground index the weakening is the identity: whatever is related at
-- `A` is related at `wk₀ A`, transported.
------------------------------------------------------------------------

RelGM-wk₀ : ∀ {π} {A : Type} {v : SE.M π SD.⟦ A ⟨ σ ⟩ ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ} → RelGM π A v t
          → RelGM π (wk₀ {0} A) (subst (SE.M π) (sym (⟦wk₀⟧ᵛ A)) v) (subst T∞ (sym (⟦wk₀⟧ᴰ A)) t)
RelGM-wk₀ {π} {A} {v} {t} r = go (wk₀ A) (wk₀-id A) (sym (⟦wk₀⟧ᵛ A)) (sym (⟦wk₀⟧ᴰ A))
  where
    go : (U : Type) → U ≡ A → (p : SD.⟦ A ⟨ σ ⟩ ⟧ᵛ ≡ SD.⟦ U ⟨ σ ⟩ ⟧ᵛ) (q : ⟦ A ⟧ᴰ ≡ ⟦ U ⟧ᴰ)
       → RelGM π U (subst (SE.M π) p v) (subst T∞ q t)
    go .A refl refl refl = r
