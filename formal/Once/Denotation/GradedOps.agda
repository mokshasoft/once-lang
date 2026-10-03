-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.GradedOps — the semantic operations of the GRADED Spec
-- meaning (D250, plan 0.104 A.3).
--
-- The Kleisli twins (`Denotation.Meaning`'s `cata-sem`, `ana-sem`, `out-sem`,
-- `in-value`, `sigOpRefᴰ`, and `Denotation.Sub`'s coercion) run every grade in
-- `T`. These run grade `π` in `M π`: at `pure` a fold is a plain fold, a pure
-- stream is plain codata, a subtyping coercion between pure arrows is a function
-- between total functions, and a pure FFI reference is its contract's graded
-- value (`semP`). `μ`/`ν` payloads are first-order, so the base-type
-- conversions `injB`/`prjB` are all the functor layers need.
------------------------------------------------------------------------

module Once.Denotation.GradedOps where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type
open import Once.Type.Sub
open import Once.Functor.Translate
  using ( WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod
        ; IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum
        ; IsConcrete; con-base; con-fun; translateF )
import Once.Semantics.Machine as Val
open import Once.Semantics.Machine using (⟦_⟧F; sem-cata; sem-In; coerce-ν-in; coerce-ν-out)
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Res using (Res; stopped; returns; mapRes)
open import Once.Target.Arch using (TargetNum)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Contract using (ISig; Impl; key; valueOf; value-∈; base-contract)
open import Once.Denotation.TraceMonad using (T; ret; returnT; _>>=T_; fmapT)
open import Once.Denotation.ValueDomain using (νᵈ; forceᵈ; anaᵈ; seqF)
open import Once.Denotation.DenotTrace using (sigOpT)
open import Once.Denotation.GradedDomain
open import Once.SigOp.Info using (FFIAnswers)
open import Once.Arith.SigOp.Builders using (arrow-info)

------------------------------------------------------------------------
-- The grade's functor action.
------------------------------------------------------------------------

fmapM : ∀ π {X Y} → (X → Y) → M π X → M π Y
fmapM pure f m = f m
fmapM eff  f m = fmapT f m

------------------------------------------------------------------------
-- Base types: the graded value IS the machine value, up to the products and
-- sums `⟦_⟧ᵛ` and `Val.⟦_⟧` each build.
------------------------------------------------------------------------

injB : ∀ {A} → IsBaseType A → Val.⟦ A ⟧ → ⟦ A ⟧ᵛ
injB base-Unit   x = x
injB base-Void   x = x
injB base-Int    x = x
injB base-Float  x = x
injB base-Str    x = x
injB base-Buffer x = x
injB (base-Prod a b) (x , y) = injB a x , injB b y
injB (base-Sum a b) (inj₁ x) = inj₁ (injB a x)
injB (base-Sum a b) (inj₂ y) = inj₂ (injB b y)

prjB : ∀ {A} → IsBaseType A → ⟦ A ⟧ᵛ → Val.⟦ A ⟧
prjB base-Unit   x = x
prjB base-Void   x = x
prjB base-Int    x = x
prjB base-Float  x = x
prjB base-Str    x = x
prjB base-Buffer x = x
prjB (base-Prod a b) (x , y) = prjB a x , prjB b y
prjB (base-Sum a b) (inj₁ x) = inj₁ (prjB a x)
prjB (base-Sum a b) (inj₂ y) = inj₂ (prjB b y)

injBᵍ : ∀ {A} → IsBaseType A → Val.⟦ A ⟧ᵍ → ⟦ A ⟧ᵛ
injBᵍ base-Unit   x = x
injBᵍ base-Void   x = x
injBᵍ base-Int    x = x
injBᵍ base-Float  x = x
injBᵍ base-Str    x = x
injBᵍ base-Buffer x = x
injBᵍ (base-Prod a b) (x , y) = injBᵍ a x , injBᵍ b y
injBᵍ (base-Sum a b) (inj₁ x) = inj₁ (injBᵍ a x)
injBᵍ (base-Sum a b) (inj₂ y) = inj₂ (injBᵍ b y)

------------------------------------------------------------------------
-- Functor layers (first-order payloads only, per `WellFormedF`).
------------------------------------------------------------------------

cfᵛ : ∀ {F} (C : Type) → WellFormedF F → ⟦ ⟦ F ⟧T C ⟧ᵛ → ⟦ F ⟧F ⟦ C ⟧ᵛ
cfᵛ C (wf-K ib)     x        = prjB ib x
cfᵛ C wf-Id         x        = x
cfᵛ C (wf-Sum f g)  (inj₁ x) = inj₁ (cfᵛ C f x)
cfᵛ C (wf-Sum f g)  (inj₂ y) = inj₂ (cfᵛ C g y)
cfᵛ C (wf-Prod f g) (x , y)  = cfᵛ C f x , cfᵛ C g y

cf⁻¹ᵛ : ∀ {F} (C : Type) → WellFormedF F → ⟦ F ⟧F ⟦ C ⟧ᵛ → ⟦ ⟦ F ⟧T C ⟧ᵛ
cf⁻¹ᵛ C (wf-K ib)     x        = injB ib x
cf⁻¹ᵛ C wf-Id         x        = x
cf⁻¹ᵛ C (wf-Sum f g)  (inj₁ x) = inj₁ (cf⁻¹ᵛ C f x)
cf⁻¹ᵛ C (wf-Sum f g)  (inj₂ y) = inj₂ (cf⁻¹ᵛ C g y)
cf⁻¹ᵛ C (wf-Prod f g) (x , y)  = cf⁻¹ᵛ C f x , cf⁻¹ᵛ C g y

-- Sequence a layer of grade-`π` computations (at `pure`, there is nothing to run).
seqM : ∀ π (G : Functor) {X : Set} → ⟦ G ⟧F (M π X) → M π (⟦ G ⟧F X)
seqM pure G x = x
seqM eff  G x = seqF G x

------------------------------------------------------------------------
-- μ: introduction and the fold.
------------------------------------------------------------------------

in-valueᵛ : ∀ {F} → WellFormedF F → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᵛ → ⟦ μ-type F ⟧ᵛ
in-valueᵛ {F} wf x = sem-In F (cfᵛ (μ-type F) wf x)

cata-semᵛ : ∀ π {F A} → WellFormedF F
          → (⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) → ⟦ μ-type F ⟧ᵛ → M π ⟦ A ⟧ᵛ
cata-semᵛ π {F} {A} wf alg =
  sem-cata wf (λ fc → bindM π (seqM π F fc) λ layer → alg (cf⁻¹ᵛ A wf layer))

------------------------------------------------------------------------
-- ν: pure codata, its embedding into the effectful one, unfold and out.
------------------------------------------------------------------------

-- The layer maps are NAMED and applied directly (D062): a corecursive call
-- handed to a higher-order function is opaque to the guardedness checker.
mutual
  anaᵖ : ∀ (H : SFunctor) {X : Set} → (X → ⟦ H ⟧SF X) → X → νᵖ H
  forceᵖ (anaᵖ H c x) = mapAnaᵖ H H c (c x)

  mapAnaᵖ : ∀ (H G : SFunctor) {X : Set} → (X → ⟦ H ⟧SF X) → ⟦ G ⟧SF X → ⟦ G ⟧SF (νᵖ H)
  mapAnaᵖ H (SK B)     c x        = x
  mapAnaᵖ H SId        c x        = anaᵖ H c x
  mapAnaᵖ H (G₁ S⊕ G₂) c (inj₁ x) = inj₁ (mapAnaᵖ H G₁ c x)
  mapAnaᵖ H (G₁ S⊕ G₂) c (inj₂ y) = inj₂ (mapAnaᵖ H G₂ c y)
  mapAnaᵖ H (G₁ S⊗ G₂) c (x , y)  = mapAnaᵖ H G₁ c x , mapAnaᵖ H G₂ c y

-- `pure ⊑ eff` at ν: a pure stream is an effectful one whose layers emit
-- nothing and always arrive.
mutual
  embν : ∀ {H} → νᵖ H → νᵈ H
  forceᵈ (embν {H} v) = ret (mapEmbν H H (forceᵖ v))

  mapEmbν : ∀ (H G : SFunctor) → ⟦ G ⟧SF (νᵖ H) → ⟦ G ⟧SF (νᵈ H)
  mapEmbν H (SK B)     x        = x
  mapEmbν H SId        x        = embν x
  mapEmbν H (G₁ S⊕ G₂) (inj₁ x) = inj₁ (mapEmbν H G₁ x)
  mapEmbν H (G₁ S⊕ G₂) (inj₂ y) = inj₂ (mapEmbν H G₂ y)
  mapEmbν H (G₁ S⊗ G₂) (x , y)  = mapEmbν H G₁ x , mapEmbν H G₂ y

-- `unfold c s` at coalgebra grade `π`, built at grade `π′`. A pure ν needs a
-- pure coalgebra FUNCTION, so the term computing it runs once, when the stream
-- is built. An effectful ν stores that computation and runs it in each forced
-- layer (D247), as the Kleisli `ana-sem` does.
ana-semᵛ : ∀ {F A} (π π′ : Purity) → WellFormedF F
         → M π′ (⟦ A ⟧ᵛ → M π ⟦ ⟦ F ⟧T A ⟧ᵛ) → ⟦ A ⟧ᵛ → M π′ ⟦ ν-type F π ⟧ᵛ
ana-semᵛ {F} {A} pure π′ wf cM a =
  bindM π′ cM λ clo →
    returnM π′ (anaᵖ (translateF Carrier Carrier F) (λ a′ → coerce-ν-in F _ (cfᵛ A wf (clo a′))) a)
ana-semᵛ {F} {A} eff π′ wf cM a =
  returnM π′ (anaᵈ (translateF Carrier Carrier F)
                   (λ a′ → fmapT (λ l → coerce-ν-in F _ (cfᵛ A wf l)) (toT π′ cM >>=T λ clo → clo a′)) a)

out-semᵛ : ∀ π {F} → WellFormedF F → ⟦ ν-type F π ⟧ᵛ → M π ⟦ ⟦ F ⟧T (ν-type F π) ⟧ᵛ
out-semᵛ pure {F} wf v = cf⁻¹ᵛ (ν-type F pure) wf (coerce-ν-out wf _ (forceᵖ v))
out-semᵛ eff  {F} wf v = fmapT (λ layer → cf⁻¹ᵛ (ν-type F eff) wf (coerce-ν-out wf _ layer)) (forceᵈ v)

------------------------------------------------------------------------
-- Subtyping coercions (D226), graded.
------------------------------------------------------------------------

⟦_⟧<:ᵛ : ∀ {A B} → A <: B → ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ
⟦ sub-void   ⟧<:ᵛ ()
⟦ sub-unit   ⟧<:ᵛ x = x
⟦ sub-int    ⟧<:ᵛ x = x
⟦ sub-float  ⟧<:ᵛ x = x
⟦ sub-str    ⟧<:ᵛ x = x
⟦ sub-buffer ⟧<:ᵛ x = x
⟦ sub-arr {q = Zero} {π = π} a b g ⟧<:ᵛ f = λ u → subM g (fmapM π ⟦ b ⟧<:ᵛ (f u))
⟦ sub-arr {q = One}  {π = π} a b g ⟧<:ᵛ f = λ x → subM g (fmapM π ⟦ b ⟧<:ᵛ (f (⟦ a ⟧<:ᵛ x)))
⟦ sub-arr {q = Many} {π = π} a b g ⟧<:ᵛ f = λ x → subM g (fmapM π ⟦ b ⟧<:ᵛ (f (⟦ a ⟧<:ᵛ x)))
⟦ sub-prod a b ⟧<:ᵛ (x , y) = ⟦ a ⟧<:ᵛ x , ⟦ b ⟧<:ᵛ y
⟦ sub-sum a b ⟧<:ᵛ (inj₁ x) = inj₁ (⟦ a ⟧<:ᵛ x)
⟦ sub-sum a b ⟧<:ᵛ (inj₂ y) = inj₂ (⟦ b ⟧<:ᵛ y)
⟦ sub-μ ⟧<:ᵛ x = x
⟦ sub-ν ⊑-pure ⟧<:ᵛ x = x
⟦ sub-ν ⊑-eff  ⟧<:ᵛ x = x
⟦ sub-ν ⊑-pe   ⟧<:ᵛ x = embν x
⟦ sub-rigid ⟧<:ᵛ x = x

------------------------------------------------------------------------
-- An FFI reference (`⊢sigop`), plan 0.105. A PURE contract is the
-- interpretation's pure half at its argument — a value, so a pure reference is
-- referentially transparent by its type. An effectful arrow's application is
-- the contract's computation (`sigOpT`, the IR's own dispatch): a call the
-- interpretation answers, an emitted event, or a halt. Contracts are
-- first-order (`IsConcrete`), so both sides cross by the base conversions.
------------------------------------------------------------------------

-- An effectful arrow's contract is a call, an emitted event or a halt: it never
-- consults a pure contract, so its dispatch is given none.
noPure : FFIAnswers
noPure _ _ _ _ = stopped

-- Plan 0.105 (D257 amendment 2): a reference to a SigOp the program is compiled
-- against (`m`: its declaration in `Σ`). A VALUE contract reads the
-- implementation (`valueOf`, the reading every layer shares); an effectful
-- arrow's application is its call, answered when the program runs.
sigOpRefᵛ : ∀ {A} → TargetNum → (Σ : ISig) → Impl Σ → (cn : CanonicalName) → IsConcrete A
          → (showCanonical cn , A) ∈ Σ → ⟦ A ⟧ᵛ
sigOpRefᵛ {A} fmt Σ I cn (con-base ib) m =
  injB ib (valueOf I (key (showCanonical cn) Unit A) (value-∈ m (base-contract (showCanonical cn) ib)) tt)
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero pure} bDom bCod) m =
  λ _ → injB bCod (valueOf I (key (showCanonical cn) Unit Cod) (value-∈ m refl) tt)
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero eff} bDom bCod) m =
  λ _ → returnT (injB bCod (valueOf I (key (showCanonical cn) Unit Cod) (value-∈ m refl) tt))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One pure} bDom bCod) m =
  λ a → injB bCod (valueOf I (key (showCanonical cn) Dom Cod) (value-∈ m refl) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many pure} bDom bCod) m =
  λ a → injB bCod (valueOf I (key (showCanonical cn) Dom Cod) (value-∈ m refl) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One eff} bDom bCod) m =
  λ a → fmapT (injB bCod) (sigOpT fmt noPure (arrow-info {Dom} {Cod} (mk-kind One eff) cn bDom bCod) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many eff} bDom bCod) m =
  λ a → fmapT (injB bCod) (sigOpT fmt noPure (arrow-info {Dom} {Cod} (mk-kind Many eff) cn bDom bCod) (prjB bDom a))
