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
-- value — `RelGM pure B v m = RelGT B (returnT v) m`.
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
open import Once.Denotation.TraceMonadLaws using (RelT′-bind; RelT′-fmap)
open import Once.Lang.Stream using (νᵈ; module νᵈ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; forgetᵇ; injectᵇ)
open νᵈ using (forceᵈ)
open import Once.Denotation.ValueDomainLaws using (_∼ᵈ_)
open Once.Denotation.ValueDomainLaws._∼ᵈ_ using (force-∼)
open import Once.Lang.Graded using (M; ⟦_⟧ᵛ; νᵖ; bindM; returnM; _>>=ᵖ_)
open import Once.Lang.Iterative using (T∞; return∞)
open Once.Lang.Iterative.T∞ using (force)
open import Once.Denotation.TraceMonadInfLaws using (RelT∞′; rel∞-ret; RelT∞′-bind; RelT∞′-≈)
open import Once.Lang.Trace using (call; halt; rel-call; rel-halt)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β)
open Once.Lang.Graded.νᵖ using (forceᵖ)

------------------------------------------------------------------------
-- Pure codata against effectful codata: the heterogeneous bisimulation.
-- The pure side's layer is always there and emits nothing, so the Kleisli
-- side's force must emit nothing and return a related layer.
------------------------------------------------------------------------

-- Plan 0.105: the Kleisli force is a TREE related to the pure layer's `ret` —
-- so it makes no call and returns a related layer.
record _∼ᵖᵈ_ {F : SFunctor} (x : νᵖ F) (y : νᵈ F) : Set where
  coinductive
  field
    force-∼ᵖᵈ : RelT′ (⟦ F ⟧SF-rel (_∼ᵖᵈ_ {F})) (ret (forceᵖ x)) (forceᵈ y)

open _∼ᵖᵈ_


------------------------------------------------------------------------
-- The relation, by recursion on the type.
------------------------------------------------------------------------

RelGV : ∀ (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᴰ → Set
RelGT : ∀ (A : Type) → T ⟦ A ⟧ᵛ → T ⟦ A ⟧ᴰ → Set

-- A grade-`π` Spec meaning against a Kleisli computation. An effectful one is
-- a tree of `T∞` (D312) against the IR's finite one.
RelGM : ∀ (π : Purity) (A : Type) → M π ⟦ A ⟧ᵛ → T ⟦ A ⟧ᴰ → Set
RelGM pure A m t = RelGT A (returnT m) t
RelGM act  A m t = RelGT A m t
RelGM eff  A m t = RelT∞′ (RelGV A) m t

-- Plan 0.105: related computations are related TREES (`RelT′`).
RelGT A t₁ t₂ = RelT′ (RelGV A) t₁ t₂

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

RelGT-return : ∀ {A} {x y} → RelGV A x y → RelGT A (returnT x) (returnT y)
RelGT-return rv = rel-ret rv

RelGT-bind : ∀ {A B} {t₁ : T ⟦ A ⟧ᵛ} {t₂ : T ⟦ A ⟧ᴰ} {f : ⟦ A ⟧ᵛ → T ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
           → RelGT A t₁ t₂
           → (∀ {a b} → RelGV A a b → RelGT B (f a) (g b))
           → RelGT B (t₁ >>=T f) (t₂ >>=T g)
RelGT-bind {A} {B} {t₁} {t₂} {f} {g} rt rk =
  RelT′-bind (RelGV A) (RelGV B) rt (λ a b r → rk r)

-- The PURE bind against a Kleisli one: the pure side's value is its
-- continuation's (`>>=ᵖ-β`), and `returnT v >>=T k` is `k v` definitionally.
RelGᵖ-bind : ∀ {A B} {m : ⟦ A ⟧ᵛ} {t₂ : T ⟦ A ⟧ᴰ} {k : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
           → RelGT A (returnT m) t₂
           → (∀ {a b} → RelGV A a b → RelGT B (returnT (k a)) (g b))
           → RelGT B (returnT (m >>=ᵖ k)) (t₂ >>=T g)
RelGᵖ-bind {A} {B} {m} {t₂} {k} {g} rt rk =
  subst (λ v → RelGT B (returnT v) (t₂ >>=T g)) (sym (>>=ᵖ-β m k))
        (RelGT-bind {A} {B} {returnT m} {t₂} {λ a → returnT (k a)} {g} rt rk)

-- A pure bind feeding an EFFECTFUL continuation (a suspension's body: its
-- pieces are values, its last step runs): a tree of `T∞` (D312) against the
-- Kleisli one.
RelGᵖᵉ-bind : ∀ {A B} {X : Set} {P : X → T ⟦ B ⟧ᴰ → Set} {m : ⟦ A ⟧ᵛ} {t₂ : T ⟦ A ⟧ᴰ} {k : ⟦ A ⟧ᵛ → X} {g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
            → RelGT A (returnT m) t₂
            → (∀ {a b} → RelGV A a b → P (k a) (g b))
            → P (m >>=ᵖ k) (t₂ >>=T g)
RelGᵖᵉ-bind {A} {B} {P = P} {m} {ret y} {k} {g} (rel-ret r) rk =
  subst (λ t → P t (g y)) (sym (>>=ᵖ-β m k)) (rk r)

-- The two, at any grade.
RelGM-bind : ∀ π {A B} {m : M π ⟦ A ⟧ᵛ} {t₂ : T ⟦ A ⟧ᴰ} {k : ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
           → RelGM π A m t₂
           → (∀ {a b} → RelGV A a b → RelGM π B (k a) (g b))
           → RelGM π B (bindM π m k) (t₂ >>=T g)
RelGM-bind pure {A} {B} {m} {t₂} {k} {g} = RelGᵖ-bind {A} {B} {m} {t₂} {k} {g}
RelGM-bind act  {A} {B} {m} {t₂} {k} {g} = RelGT-bind {A} {B} {m} {t₂} {k} {g}
RelGM-bind eff  {A} {B} {m} {t₂} {k} {g} = RelT∞′-bind

-- The graded map: both sides map their result along related functions.
RelGM-fmap : ∀ π {A B} {m : M π ⟦ A ⟧ᵛ} {t : T ⟦ A ⟧ᴰ} {f : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ} {g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ}
           → RelGM π A m t
           → (∀ {a b} → RelGV A a b → RelGV B (f a) (g b))
           → RelGM π B (fmapM π f m) (fmapT g t)
RelGM-fmap pure {A} {B} rm h = RelT′-fmap (RelGV A) (RelGV B) (λ _ _ r → h r) rm
RelGM-fmap act  {A} {B} rm h = RelT′-fmap (RelGV A) (RelGV B) (λ _ _ r → h r) rm
RelGM-fmap eff  rm h = RelT∞′-bind rm (λ r → rel∞-ret (h r))

RelGM-return : ∀ {π} (u : pure ⊑π π) {A} {x y} → RelGV A x y → RelGM π A (returnM u x) (returnT y)
RelGM-return ⊑-pure {A} rv = RelGT-return {A} rv
RelGM-return ⊑-pa   {A} rv = RelGT-return {A} rv
RelGM-return ⊑-pe   {A} rv = rel∞-ret rv

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
  embνᵃ-∼ : ∀ {H : SFunctor} {x : νᵖ H} {y : νᵈ H} → x ∼ᵖᵈ y → embνᵃ x ∼ᵈ y
  force-∼ (embνᵃ-∼ {H} r) = embLayerᵃ H (force-∼ᵖᵈ r)

  embLayerᵃ : ∀ (H : SFunctor) {l : ⟦ H ⟧SF (νᵖ H)} {m : T (⟦ H ⟧SF (νᵈ H))}
           → RelT′ (⟦ H ⟧SF-rel (_∼ᵖᵈ_ {H})) (ret l) m
           → RelT′ (⟦ H ⟧SF-rel (_∼ᵈ_ {H})) (ret (mapEmbνᵃ H H l)) m
  embLayerᵃ H (rel-ret rr) = rel-ret (mapEmbνᵃ-∼ H H rr)

  mapEmbνᵃ-∼ : ∀ (H G : SFunctor) {l : ⟦ G ⟧SF (νᵖ H)} {l′ : ⟦ G ⟧SF (νᵈ H)}
            → ⟦ G ⟧SF-rel (_∼ᵖᵈ_ {H}) l l′ → ⟦ G ⟧SF-rel (_∼ᵈ_ {H}) (mapEmbνᵃ H G l) l′
  mapEmbνᵃ-∼ H (SK B)     r = r
  mapEmbνᵃ-∼ H SId        r = embνᵃ-∼ r
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₁ _} {inj₁ _} r = mapEmbνᵃ-∼ H G₁ r
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₂ _} {inj₂ _} r = mapEmbνᵃ-∼ H G₂ r
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₁ _} {inj₂ _} ()
  mapEmbνᵃ-∼ H (G₁ S⊕ G₂) {inj₂ _} {inj₁ _} ()
  mapEmbνᵃ-∼ H (G₁ S⊗ G₂) {_ , _} {_ , _} (r₁ , r₂) = mapEmbνᵃ-∼ H G₁ r₁ , mapEmbνᵃ-∼ H G₂ r₂

-- A pure meaning, embedded at any grade (what a lambda's body is, D250).
RelGM-ret : ∀ {π} (u : pure ⊑π π) {B} {v : ⟦ B ⟧ᵛ} {t : T ⟦ B ⟧ᴰ} → RelGM pure B v t → RelGM π B (returnM u v) t
RelGM-ret ⊑-pure r = r
RelGM-ret ⊑-pa   r = r
RelGM-ret ⊑-pe   (rel-ret r) = rel∞-ret r
