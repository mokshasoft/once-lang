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

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Spec.Type.Grade
open import Once.Spec.Type
open import Once.Spec.Type.Poly
open import Once.Type
open import Once.Spec.Type.Sub
open import Once.Type.Sub
open import Once.Spec.Type.WellFormed using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; IsConcrete; con-base; con-fun)
open import Once.Functor.Translate using (translateF)
import Once.Semantics.Machine as Val
open import Once.Semantics.Machine using (⟦_⟧F; sem-fmap; sem-cata; sem-In; coerce-ν-in; coerce-ν-out)
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Target.Arch using (TargetNum)
open import Once.Spec.Name using (CanonicalName; showCanonical)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Contract using (ISig; Impl; key; valueOf)
open import Once.Spec.ContractLaws using (value-∈; base-contract)
open import Once.Denotation.TraceMonad using (ret; returnT; _>>=T_; fmapT; pureHalf; interp)
open import Once.Denotation.ValueDomain using (νᵈ; anaᵈ; seqF; module νᵈ)
open import Once.Spec.Iterative
  using (T∞; T∞F; ret∞; call∞; halt∞; return∞; fmap∞; seqF∞; embed; ν∞; ana∞)
open Once.Spec.Iterative.T∞ using (force)
open Once.Spec.Iterative.ν∞ using (force∞)
open import Once.Denotation.TraceMonad using (T; call; halt; callOp; haltOp)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open νᵈ using (forceᵈ)
open import Once.Denotation.DenotTrace using (sigOpT)
open import Once.Denotation.GradedDomain
open import Once.Spec.Guarded using (T⁺; call⁺; halt⁺; fmap⁺; ν⁺; ana⁺)
open Once.Spec.Guarded.ν⁺ using (force⁺)
open Once.Denotation.GradedDomain.νᵖ using (forceᵖ)
open import Once.Arith.SigOp.Builders using (arrow-info)

------------------------------------------------------------------------
-- The grade's functor action.
------------------------------------------------------------------------

fmapM : ∀ π {X Y} → (X → Y) → M π X → M π Y
fmapM pure f m = f m
fmapM eff⁺ f m = fmap⁺ f m
fmapM eff  f m = fmapT f m
fmapM prod f m = fmap∞ f m

------------------------------------------------------------------------
-- Base types: the graded value IS the machine value, up to the products and
-- sums `⟦_⟧ᵛ` and `Val.⟦_⟧` each build.
------------------------------------------------------------------------

injB : ∀ {A} → IsBaseType A → Val.⟦ A ⟧ → ⟦ A ⟧ᵛ
injB base-Unit   x = x
injB base-Void   x = x
injB base-Int    x = x
injB base-Float  x = x
injB (base-Prod a b) (x , y) = injB a x , injB b y
injB (base-Sum a b) (inj₁ x) = inj₁ (injB a x)
injB (base-Sum a b) (inj₂ y) = inj₂ (injB b y)

prjB : ∀ {A} → IsBaseType A → ⟦ A ⟧ᵛ → Val.⟦ A ⟧
prjB base-Unit   x = x
prjB base-Void   x = x
prjB base-Int    x = x
prjB base-Float  x = x
prjB (base-Prod a b) (x , y) = prjB a x , prjB b y
prjB (base-Sum a b) (inj₁ x) = inj₁ (prjB a x)
prjB (base-Sum a b) (inj₂ y) = inj₂ (prjB b y)

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

-- Sequence a layer of grade-`π` computations (at `pure`, there is nothing to
-- run). It needs the grade's UNIT — a layer with no recursive position runs
-- nothing — so it is defined at the grades that have one (`pure ⊑π π`; not
-- at the guard `eff⁺`, D311).
seqM : ∀ {π} → pure ⊑π π → (G : Functor) {X : Set} → ⟦ G ⟧F (M π X) → M π (⟦ G ⟧F X)
seqM ⊑-pure G x = x
seqM ⊑-pe   G x = seqF G x
seqM ⊑-pp   G x = seqF∞ G x

------------------------------------------------------------------------
-- μ: introduction and the fold.
------------------------------------------------------------------------

in-valueᵛ : ∀ {F} → WellFormedF F → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᵛ → ⟦ μ-type F ⟧ᵛ
in-valueᵛ {F} wf x = sem-In F (cfᵛ (μ-type F) wf x)

-- The fold at a grade with a unit (a fold traverses its layer).
cata-semᵛ : ∀ {π} → pure ⊑π π → ∀ {F A} → WellFormedF F
          → (⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) → ⟦ μ-type F ⟧ᵛ → M π ⟦ A ⟧ᵛ
cata-semᵛ {π} u {F} {A} wf alg =
  sem-cata wf (λ fc → bindM π (seqM u F fc) λ layer → alg (cf⁻¹ᵛ A wf layer))

-- The functor's action on one layer at grade `π`: run `h` at every recursive
-- position and sequence the results (a plain map at `pure`, Kleisli at `eff`).
-- What a fold does to one layer before its algebra; the fold's laws
-- (`Spec.Metatheory.Recursion`) are stated with it.
mapLayerᵛ : ∀ {π} → pure ⊑π π → ∀ {F A B} → WellFormedF F
          → (⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ) → ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ ⟦ F ⟧T B ⟧ᵛ
mapLayerᵛ {π} u {F} {A} {B} wf h x = fmapM π (cf⁻¹ᵛ B wf) (seqM u F (sem-fmap F h (cfᵛ A wf x)))

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

-- `unfold c s` at coalgebra grade `π` — the stream, a VALUE (building it runs
-- nothing; the rule embeds it at the grade it is built at) — given the
-- coalgebra's FUNCTION `clo` (its term was evaluated once, when the stream was
-- built — D273, as the IR's `Ana` and `cata`'s algebra, D131) and the seed. A
-- pure ν needs a pure coalgebra function; an effectful one runs the function in
-- each forced layer — a server is such a stream (D233), its coalgebra reads the
-- next request.
ana-semᵛ : ∀ {F A} (π : Purity) → WellFormedF F
         → (⟦ A ⟧ᵛ → M π ⟦ ⟦ F ⟧T A ⟧ᵛ) → ⟦ A ⟧ᵛ → ⟦ ν-type F π ⟧ᵛ
ana-semᵛ {F} {A} pure wf clo a =
  anaᵖ (translateF Carrier Carrier F) (λ a′ → coerce-ν-in F _ (cfᵛ A wf (clo a′))) a
ana-semᵛ {F} {A} eff⁺ wf clo a =
  ana⁺ (translateF Carrier Carrier F) (λ a′ → fmap⁺ (λ l → coerce-ν-in F _ (cfᵛ A wf l)) (clo a′)) a
ana-semᵛ {F} {A} eff wf clo a =
  anaᵈ (translateF Carrier Carrier F) (λ a′ → fmapT (λ l → coerce-ν-in F _ (cfᵛ A wf l)) (clo a′)) a
ana-semᵛ {F} {A} prod wf clo a =
  ana∞ (translateF Carrier Carrier F) (λ a′ → fmap∞ (λ l → coerce-ν-in F _ (cfᵛ A wf l)) (clo a′)) a

out-semᵛ : ∀ π {F} → WellFormedF F → ⟦ ν-type F π ⟧ᵛ → M π ⟦ ⟦ F ⟧T (ν-type F π) ⟧ᵛ
out-semᵛ pure {F} wf v = cf⁻¹ᵛ (ν-type F pure) wf (coerce-ν-out wf _ (forceᵖ v))
out-semᵛ eff⁺ {F} wf v = fmap⁺ (λ layer → cf⁻¹ᵛ (ν-type F eff⁺) wf (coerce-ν-out wf _ layer)) (force⁺ v)
out-semᵛ eff  {F} wf v = fmapT (λ layer → cf⁻¹ᵛ (ν-type F eff) wf (coerce-ν-out wf _ layer)) (forceᵈ v)
out-semᵛ prod {F} wf v = fmap∞ (λ layer → cf⁻¹ᵛ (ν-type F prod) wf (coerce-ν-out wf _ layer)) (force∞ v)

-- `eff⁺ ⊑ eff` at ν: a stream whose layers begin with an event is one whose
-- layers are trees (D311).
embν⁺ᵈ   : ∀ {H} → ν⁺ H → νᵈ H
embRoot⁺ : ∀ (H : SFunctor) → T⁺ (⟦ H ⟧SF (ν⁺ H)) → T (⟦ H ⟧SF (νᵈ H))
embTree⁺ : ∀ (H : SFunctor) → T (⟦ H ⟧SF (ν⁺ H)) → T (⟦ H ⟧SF (νᵈ H))
mapEmbν⁺ᵈ : ∀ (H G : SFunctor) → ⟦ G ⟧SF (ν⁺ H) → ⟦ G ⟧SF (νᵈ H)
forceᵈ (embν⁺ᵈ {H} v) = embRoot⁺ H (force⁺ v)
embRoot⁺ H (call⁺ o a k) = call o a (λ b → embTree⁺ H (k b))
embRoot⁺ H (halt⁺ o a)   = halt o a
embTree⁺ H (ret l)      = ret (mapEmbν⁺ᵈ H H l)
embTree⁺ H (call o a k) = call o a (λ b → embTree⁺ H (k b))
embTree⁺ H (halt o a)   = halt o a
mapEmbν⁺ᵈ H (SK B)     x        = x
mapEmbν⁺ᵈ H SId        x        = embν⁺ᵈ x
mapEmbν⁺ᵈ H (G₁ S⊕ G₂) (inj₁ x) = inj₁ (mapEmbν⁺ᵈ H G₁ x)
mapEmbν⁺ᵈ H (G₁ S⊕ G₂) (inj₂ y) = inj₂ (mapEmbν⁺ᵈ H G₂ y)
mapEmbν⁺ᵈ H (G₁ S⊗ G₂) (x , y)  = mapEmbν⁺ᵈ H G₁ x , mapEmbν⁺ᵈ H G₂ y

-- `eff ⊑ prod` and `pure ⊑ prod` at ν: a stream whose layers are finite
-- trees, or always there, is one whose layers are trees of `T∞` (D311). The
-- maps are named and written by hand (D062).
embν∞ᵈ  : ∀ {H} → νᵈ H → ν∞ H
embLay∞ : ∀ (H : SFunctor) → T (⟦ H ⟧SF (νᵈ H)) → T∞ (⟦ H ⟧SF (ν∞ H))
mapEmbν∞ᵈ : ∀ (H G : SFunctor) → ⟦ G ⟧SF (νᵈ H) → ⟦ G ⟧SF (ν∞ H)
force∞ (embν∞ᵈ {H} v) = embLay∞ H (forceᵈ v)
force (embLay∞ H (ret l))      = ret∞ (mapEmbν∞ᵈ H H l)
force (embLay∞ H (call o a k)) = call∞ o a (λ b → embLay∞ H (k b))
force (embLay∞ H (halt o a))   = halt∞ o a
mapEmbν∞ᵈ H (SK B)     x        = x
mapEmbν∞ᵈ H SId        x        = embν∞ᵈ x
mapEmbν∞ᵈ H (G₁ S⊕ G₂) (inj₁ x) = inj₁ (mapEmbν∞ᵈ H G₁ x)
mapEmbν∞ᵈ H (G₁ S⊕ G₂) (inj₂ y) = inj₂ (mapEmbν∞ᵈ H G₂ y)
mapEmbν∞ᵈ H (G₁ S⊗ G₂) (x , y)  = mapEmbν∞ᵈ H G₁ x , mapEmbν∞ᵈ H G₂ y

embν∞ᵖ    : ∀ {H} → νᵖ H → ν∞ H
mapEmbν∞ᵖ : ∀ (H G : SFunctor) → ⟦ G ⟧SF (νᵖ H) → ⟦ G ⟧SF (ν∞ H)
force (force∞ (embν∞ᵖ {H} v)) = ret∞ (mapEmbν∞ᵖ H H (forceᵖ v))
mapEmbν∞ᵖ H (SK B)     x        = x
mapEmbν∞ᵖ H SId        x        = embν∞ᵖ x
mapEmbν∞ᵖ H (G₁ S⊕ G₂) (inj₁ x) = inj₁ (mapEmbν∞ᵖ H G₁ x)
mapEmbν∞ᵖ H (G₁ S⊕ G₂) (inj₂ y) = inj₂ (mapEmbν∞ᵖ H G₂ y)
mapEmbν∞ᵖ H (G₁ S⊗ G₂) (x , y)  = mapEmbν∞ᵖ H G₁ x , mapEmbν∞ᵖ H G₂ y

------------------------------------------------------------------------
-- Subtyping coercions (D226), graded.
------------------------------------------------------------------------

⟦_⟧<:ᵛ : ∀ {A B} → A <: B → ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ
⟦ sub-void   ⟧<:ᵛ ()
⟦ sub-unit   ⟧<:ᵛ x = x
⟦ sub-int    ⟧<:ᵛ x = x
⟦ sub-float  ⟧<:ᵛ x = x
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
⟦ sub-ν ⊑-prod ⟧<:ᵛ x = x
⟦ sub-ν ⊑-pp   ⟧<:ᵛ x = embν∞ᵖ x
⟦ sub-ν ⊑-ep   ⟧<:ᵛ x = embν∞ᵈ x
⟦ sub-ν ⊑-g    ⟧<:ᵛ x = x
⟦ sub-ν ⊑-ge   ⟧<:ᵛ x = embν⁺ᵈ x
⟦ sub-ν ⊑-gp   ⟧<:ᵛ x = embν∞ᵈ (embν⁺ᵈ x)
⟦ sub-rigid ⟧<:ᵛ x = x

------------------------------------------------------------------------
-- An FFI reference (`⊢sigop`), plan 0.105. A PURE contract is the
-- interpretation's pure half at its argument — a value, so a pure reference is
-- referentially transparent by its type. An effectful arrow's application is
-- the contract's computation (`sigOpT`, the IR's own dispatch): a call the
-- interpretation answers, an emitted event, or a halt. Contracts are
-- first-order (`IsConcrete`), so both sides cross by the base conversions.
------------------------------------------------------------------------

-- A foreign operation's call, GUARDED (D311): the generic effect — its root is
-- the call (or the halt). The form `arrow-sem-eff` decides, read as `T⁺`.
opCall⁺ : ∀ {A B} → CanonicalName → IsBaseType A → Dec (B ≡ Void) → Dec (B ≡ Unit) → Val.⟦ A ⟧ → T⁺ Val.⟦ B ⟧
opCall⁺ {A} cn bA (yes refl) _          x = halt⁺ (haltOp cn A bA) x
opCall⁺ {A} cn bA (no _)     (yes refl) x = call⁺ (callOp cn A bA Unit) x (λ _ → ret tt)
opCall⁺ {A} {B} cn bA (no _) (no _)     x = call⁺ (callOp cn A bA B) x ret

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
-- plan 0.113 A3: an effectful erased arrow is a CALL with the erased slot `tt`
-- (D250) — the elaborator's `arrow-info (mk-kind Zero eff) cn base-Unit`.
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero eff} bDom bCod) m =
  λ _ → fmapT (injB bCod) (sigOpT fmt (pureHalf (interp Σ I)) (arrow-info {Unit} {Cod} (mk-kind Zero eff) cn base-Unit bCod) tt)
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One pure} bDom bCod) m =
  λ a → injB bCod (valueOf I (key (showCanonical cn) Dom Cod) (value-∈ m refl) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many pure} bDom bCod) m =
  λ a → injB bCod (valueOf I (key (showCanonical cn) Dom Cod) (value-∈ m refl) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One eff} bDom bCod) m =
  λ a → fmapT (injB bCod) (sigOpT fmt (pureHalf (interp Σ I)) (arrow-info {Dom} {Cod} (mk-kind One eff) cn bDom bCod) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many eff} bDom bCod) m =
  λ a → fmapT (injB bCod) (sigOpT fmt (pureHalf (interp Σ I)) (arrow-info {Dom} {Cod} (mk-kind Many eff) cn bDom bCod) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero eff⁺} bDom bCod) m =
  λ _ → fmap⁺ (injB bCod) (opCall⁺ cn base-Unit (isVoid? Cod) (isUnit? Cod) tt)
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One eff⁺} bDom bCod) m =
  λ a → fmap⁺ (injB bCod) (opCall⁺ cn bDom (isVoid? Cod) (isUnit? Cod) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many eff⁺} bDom bCod) m =
  λ a → fmap⁺ (injB bCod) (opCall⁺ cn bDom (isVoid? Cod) (isUnit? Cod) (prjB bDom a))
-- D311: a foreign operation declared at `prod` is still one call that returns
-- or halts (`arrow-sem` reads `prod` as `eff`), read as a tree of `T∞`.
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero prod} bDom bCod) m =
  λ _ → embed (fmapT (injB bCod) (sigOpT fmt (pureHalf (interp Σ I)) (arrow-info {Unit} {Cod} (mk-kind Zero prod) cn base-Unit bCod) tt))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One prod} bDom bCod) m =
  λ a → embed (fmapT (injB bCod) (sigOpT fmt (pureHalf (interp Σ I)) (arrow-info {Dom} {Cod} (mk-kind One prod) cn bDom bCod) (prjB bDom a)))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many prod} bDom bCod) m =
  λ a → embed (fmapT (injB bCod) (sigOpT fmt (pureHalf (interp Σ I)) (arrow-info {Dom} {Cod} (mk-kind Many prod) cn bDom bCod) (prjB bDom a)))
