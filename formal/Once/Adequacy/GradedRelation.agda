-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.GradedRelation — the logical relation between the GRADED Spec
-- meaning (`⟦_⟧ᵛ`, D250) and the purity-blind Kleisli implementation meaning
-- (`⟦_⟧ᴰ`, SD and the IR's `evalᴰ`). Plan 0.104 A.6.
--
-- `MeaningRelation` relates two Kleisli meanings and stays for the SD/IR
-- modules. This one is HETEROGENEOUS: the two sides are different sets at a
-- pure arrow (a total function against a Kleisli one) and at a pure ν (plain
-- codata against a suspension of computations). A pure value is related to a
-- Kleisli computation when the computation emits nothing and returns a related
-- value — `RelGM pure B v m = RelS (RelGV B) (return∞ v) m`. Plan 0.119 D5: the
-- implementation side is a `T∞` run (the IR is ungraded), so every grade's
-- meaning is compared, after its lift into `T∞` (`toT∞`), step for step
-- (`RelS`); the streams likewise, coinductively.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.GradedRelation (fmt : TargetNum) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

open import Once.Lang.Type.Grade using (Purity; pure; act; eff; mk-kind; Zero; One; Many)
open import Once.Lang.Type.Sub using (_⊑π_; ⊑-pure; ⊑-pe; ⊑-pa)
open import Once.Lang.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid)
open import Once.Lang.Type.WellFormed using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
import Once.Semantics.Machine as Val
open import Once.Lang.GradedOps using (fmapM; prjB; injB; embνᵃ; mapEmbνᵃ)
open import Once.Lang.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Lang.Trace using (T; ret; returnT; _>>=T_; fmapT; RelT′; rel-ret)
open import Once.Lang.Stream using (νᵈ; module νᵈ)
open import Once.Lang.StreamInf using (νᴵ; module νᴵ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; forgetᵇ; injectᵇ)
open νᵈ using (forceᵈ)
open νᴵ using (forceᴵ)
open import Once.Lang.Graded using (M; ⟦_⟧ᵛ; νᵖ; bindM; returnM; _>>=ᵖ_; toT∞)
open import Once.Lang.Iterative using (T∞; return∞; _>>=∞_; fmap∞; embed; TreeEq∞; force≈; BlockEq; ret≈; StepEq; done≈)
open Once.Lang.Iterative.T∞ using (force)
open import Once.Denotation.TraceMonadInfLaws
  using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt; relS-ret; RelS-bind; RelS-≈ˡ; embed-bind)
open RelS using (forceS)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β)
open Once.Lang.Graded.νᵖ using (forceᵖ)

------------------------------------------------------------------------
-- Codata: the Spec's streams against the IR's (whose layers are `T∞` runs).
------------------------------------------------------------------------

-- A pure stream's layer is there at once: the IR's force returns a related
-- layer, silently.
record _∼ᵖᵈ_ {F : SFunctor} (x : νᵖ F) (y : νᴵ F) : Set where
  coinductive
  field
    force-∼ᵖᵈ : RelS (⟦ F ⟧SF-rel (_∼ᵖᵈ_ {F})) (return∞ (forceᵖ x)) (forceᴵ y)

open _∼ᵖᵈ_

-- An `act` stream's layer is a finite block: the IR's force makes the same
-- calls, step for step, ending in a related layer.
record _∼ᵈ_ {F : SFunctor} (x : νᵈ F) (y : νᴵ F) : Set where
  coinductive
  field
    force-∼ : RelS (⟦ F ⟧SF-rel (_∼ᵈ_ {F})) (embed (forceᵈ x)) (forceᴵ y)

open _∼ᵈ_

------------------------------------------------------------------------
-- The relation, by recursion on the type.
------------------------------------------------------------------------

RelGV : ∀ (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᴰ → Set

-- A grade-`π` Spec meaning against the IR's run: its lift into `T∞`, step for
-- step.
RelGM : ∀ (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → T∞ ⟦ A ⟧ᴰ → Set
RelGM π A m t = RelS (RelGV A) (toT∞ π m) t

-- A finite block against the IR's run.
RelGT : ∀ (A : Type) → T ⟦ A ⟧ᵛ → T∞ ⟦ A ⟧ᴰ → Set
RelGT A t₁ t₂ = RelGM act A t₁ t₂

RelGV Unit        _ _ = ⊤
RelGV Void        () _
RelGV Int         x y = x ≡ y
RelGV Float       x y = x ≡ y
RelGV (μ-type F)  x y = x ≡ y
RelGV (ν-type F pure) x y = x ∼ᵖᵈ y
RelGV (ν-type F act)  x y = x ∼ᵈ y
RelGV (rigid _ _) () _
RelGV (A * B) (a₁ , b₁) (a₂ , b₂) = RelGV A a₁ a₂ × RelGV B b₁ b₂
RelGV (A + B) (inj₁ a₁) (inj₁ a₂) = RelGV A a₁ a₂
RelGV (A + B) (inj₂ b₁) (inj₂ b₂) = RelGV B b₁ b₂
RelGV (A + B) (inj₁ _)  (inj₂ _)  = ⊥
RelGV (A + B) (inj₂ _)  (inj₁ _)  = ⊥
-- The arrow: related arguments to related results AT THE ARROW'S GRADE. A pure
-- arrow's Kleisli twin must answer silently with a related value.
RelGV (A ⇒[ mk-kind Zero π ] B) f g = RelGM π B (f tt) (g tt)
RelGV (A ⇒[ mk-kind One  π ] B) f g = ∀ {a b} → RelGV A a b → RelGM π B (f a) (g b)
RelGV (A ⇒[ mk-kind Many π ] B) f g = ∀ {a b} → RelGV A a b → RelGM π B (f a) (g b)

------------------------------------------------------------------------
-- The monad lemmas.
------------------------------------------------------------------------

private
  -- Runs with the same first block relate to the same runs.
  sameˡ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y} → force m ≡ force m′ → RelS R m′ n → RelS R m n
  forceS (sameˡ e r) = subst (λ b → RelSB _ b _) (sym e) (forceS r)

  ret≈ˡ : ∀ {X} {x y : X} → x ≡ y → TreeEq∞ _≡_ (return∞ x) (return∞ y)
  force≈ (ret≈ˡ e) = ret≈ (done≈ e)

RelGT-return : ∀ {A} {x y} → RelGV A x y → RelGT A (returnT x) (return∞ y)
forceS (RelGT-return rv) = s-ret rv

RelGT-bind : ∀ {A B} {t₁ : T ⟦ A ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {f : ⟦ A ⟧ᵛ → T ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
           → RelGT A t₁ t₂
           → (∀ {a b} → RelGV A a b → RelGT B (f a) (g b))
           → RelGT B (t₁ >>=T f) (t₂ >>=∞ g)
RelGT-bind {A} {B} {t₁} {t₂} {f} {g} rt rk = RelS-≈ˡ (embed-bind t₁ f) (RelS-bind rt rk)

-- The PURE bind against the IR's: the pure side's value is its continuation's
-- (`>>=ᵖ-β`).
RelGᵖ-bind : ∀ {A B} {m : ⟦ A ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {k : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
           → RelGM pure A m t₂
           → (∀ {a b} → RelGV A a b → RelGM pure B (k a) (g b))
           → RelGM pure B (m >>=ᵖ k) (t₂ >>=∞ g)
RelGᵖ-bind {A} {B} {m} {t₂} {k} {g} rt rk =
  RelS-≈ˡ (ret≈ˡ (>>=ᵖ-β m k)) (sameˡ refl (RelS-bind rt rk))

-- A pure bind feeding any continuation: the IR's run returns a related value at
-- once, which the continuation receives.
RelGᵖᵉ-bind : ∀ {A B} {X : Set} {P : X → T∞ ⟦ B ⟧ᴰ → Set} {m : ⟦ A ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {k : ⟦ A ⟧ᵛ → X} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
            → RelGM pure A m t₂
            → (∀ {a b} → RelGV A a b → P (k a) (g b))
            → (∀ {x t t′} → force t ≡ force t′ → P x t′ → P x t)
            → P (m >>=ᵖ k) (t₂ >>=∞ g)
RelGᵖᵉ-bind {A} {B} {P = P} {m} {t₂} {k} {g} rt rk tr = go (force t₂) refl (forceS rt)
  where
    go : ∀ (b : _) → force t₂ ≡ b → RelSB (RelGV A) (Once.Lang.Trace.ret (inj₁ m)) b → P (m >>=ᵖ k) (t₂ >>=∞ g)
    go .(Once.Lang.Trace.ret (inj₁ _)) e (s-ret {y = y} r) =
      tr (cong (λ bl → Once.Lang.Iterative.bindBlock bl g) e)
         (subst (λ x → P x (g y)) (sym (>>=ᵖ-β m k)) (rk r))

-- The two, at any grade.
RelGM-bind : ∀ π {A B} {m : M π ⟦ A ⟧ᵛ} {t₂ : T∞ ⟦ A ⟧ᴰ} {k : ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
           → RelGM π A m t₂
           → (∀ {a b} → RelGV A a b → RelGM π B (k a) (g b))
           → RelGM π B (bindM π m k) (t₂ >>=∞ g)
RelGM-bind pure {A} {B} {m} {t₂} {k} {g} = RelGᵖ-bind {A} {B} {m} {t₂} {k} {g}
RelGM-bind act  {A} {B} {m} {t₂} {k} {g} = RelGT-bind {A} {B} {m} {t₂} {k} {g}
RelGM-bind eff  rm rk = RelS-bind rm rk

-- The graded map: both sides map their result along related functions.
RelGM-fmap : ∀ π {A B} {m : M π ⟦ A ⟧ᵛ} {t : T∞ ⟦ A ⟧ᴰ} {f : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ}
           → RelGM π A m t
           → (∀ {a b} → RelGV A a b → RelGV B (f a) (g b))
           → RelGM π B (fmapM π f m) (fmap∞ g t)
RelGM-fmap pure {A} {B} {m} rm h = sameˡ refl (RelS-bind rm (λ r → relS-ret (h r)))
RelGM-fmap act  {A} {B} {m} {f = f} rm h =
  RelS-≈ˡ (embed-bind m (λ x → ret (f x))) (RelS-bind rm (λ r → embed-ret (h r)))
  where
    embed-ret : ∀ {x y} → RelGV B (f x) y → RelS (RelGV B) (embed (ret (f x))) (return∞ y)
    forceS (embed-ret r) = s-ret r
RelGM-fmap eff  rm h = RelS-bind rm (λ r → relS-ret (h r))

RelGM-return : ∀ {π} (u : pure ⊑π π) {A} {x y} → RelGV A x y → RelGM π A (returnM u x) (return∞ y)
RelGM-return ⊑-pure rv = relS-ret rv
RelGM-return ⊑-pa {A} rv = RelGT-return {A} rv
RelGM-return ⊑-pe   rv = relS-ret rv

------------------------------------------------------------------------
-- The FFI boundary. Contracts are first-order (plan 0.105), so at a base type
-- both domains are the machine value: related values project to the same one,
-- and a machine value read into either domain is related to itself.
------------------------------------------------------------------------

prjB-rel : ∀ {A} (ib : IsBaseType A) {a : ⟦ A ⟧ᵛ} {b : ⟦ A ⟧ᴰ} → RelGV A a b → prjB ib a ≡ forgetᵇ ib b
prjB-rel base-Unit   _ = refl
prjB-rel base-Void   {()}
prjB-rel base-Int    r = r
prjB-rel base-Float  r = r
prjB-rel (base-Prod ia ib) {_ , _} {_ , _} (ra , rb) = cong₂ _,_ (prjB-rel ia ra) (prjB-rel ib rb)
prjB-rel (base-Sum ia ib) {inj₁ _} {inj₁ _} r = cong inj₁ (prjB-rel ia r)
prjB-rel (base-Sum ia ib) {inj₂ _} {inj₂ _} r = cong inj₂ (prjB-rel ib r)
prjB-rel (base-Sum ia ib) {inj₁ _} {inj₂ _} ()
prjB-rel (base-Sum ia ib) {inj₂ _} {inj₁ _} ()
prjB-rel base-rigid  {()}

injB-rel : ∀ {A} (ib : IsBaseType A) (x : Val.⟦ A ⟧) → RelGV A (injB ib x) (injectᵇ ib x)
injB-rel base-Unit   x = tt
injB-rel base-Void   ()
injB-rel base-Int    x = refl
injB-rel base-Float  x = refl
injB-rel (base-Prod ia ib) (x , y) = injB-rel ia x , injB-rel ib y
injB-rel (base-Sum ia ib) (inj₁ x) = injB-rel ia x
injB-rel (base-Sum ia ib) (inj₂ y) = injB-rel ib y
injB-rel base-rigid  ()

-- `pure ⊑ act` at ν: embedding a pure stream keeps it related.
mutual
  embνᵃ-∼ : ∀ {H : SFunctor} {x : νᵖ H} {y : νᴵ H} → x ∼ᵖᵈ y → embνᵃ x ∼ᵈ y
  force-∼ (embνᵃ-∼ {H} r) = embLayerᵃ H (force-∼ᵖᵈ r)

  embLayerᵃ : ∀ (H : SFunctor) {l : ⟦ H ⟧SF (νᵖ H)} {m : T∞ (⟦ H ⟧SF (νᴵ H))}
           → RelS (⟦ H ⟧SF-rel (_∼ᵖᵈ_ {H})) (return∞ l) m
           → RelS (⟦ H ⟧SF-rel (_∼ᵈ_ {H})) (embed (ret (mapEmbνᵃ H H l))) m
  forceS (embLayerᵃ H r) = embLayerBᵃ H (forceS r)

  embLayerBᵃ : ∀ (H : SFunctor) {l : ⟦ H ⟧SF (νᵖ H)} {b}
            → RelSB (⟦ H ⟧SF-rel (_∼ᵖᵈ_ {H})) (ret (inj₁ l)) b
            → RelSB (⟦ H ⟧SF-rel (_∼ᵈ_ {H})) (ret (inj₁ (mapEmbνᵃ H H l))) b
  embLayerBᵃ H (s-ret rr) = s-ret (mapEmbνᵃ-∼ H H rr)

  mapEmbνᵃ-∼ : ∀ (H G : SFunctor) {l : ⟦ G ⟧SF (νᵖ H)} {l′ : ⟦ G ⟧SF (νᴵ H)}
            → ⟦ G ⟧SF-rel (_∼ᵖᵈ_ {H}) l l′ → ⟦ G ⟧SF-rel (_∼ᵈ_ {H}) (mapEmbνᵃ H G l) l′
  mapEmbνᵃ-∼ H (SK B)     r = r
  mapEmbνᵃ-∼ H SId        r = embνᵃ-∼ r
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} r = mapEmbνᵃ-∼ H G₁ r
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} r = mapEmbνᵃ-∼ H G₂ r
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
  mapEmbνᵃ-∼ H (G₁ S⊗ G₂) {_ , _} {_ , _} (r₁ , r₂) = mapEmbνᵃ-∼ H G₁ r₁ , mapEmbνᵃ-∼ H G₂ r₂

-- A pure meaning, embedded at any grade (what a lambda's body is, D250).
RelGM-ret : ∀ {π} (u : pure ⊑π π) {B} {v : ⟦ B ⟧ᵛ} {t : T∞ ⟦ B ⟧ᴰ} → RelGM pure B v t → RelGM π B (returnM u v) t
RelGM-ret ⊑-pure r = r
RelGM-ret ⊑-pa   r = sameˡ refl r
RelGM-ret ⊑-pe   r = r
