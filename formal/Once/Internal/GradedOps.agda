-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.GradedOps — the semantic operations of the GRADED Spec
-- meaning (D250, plan 0.104 A.3).
--
-- The Kleisli twins (`Denotation.Meaning`'s `cata-sem`, `ana-sem`, `out-sem`,
-- `in-value`, `sigOpRefᴰ`, and `Denotation.Sub`'s coercion) run every grade in
-- `T`. These run grade `π` in `M π` (`M eff` is `T∞`, D312): at `pure` a fold is a plain fold, a pure
-- stream is plain codata, a subtyping coercion between pure arrows is a function
-- between total functions, and a pure FFI reference is its contract's graded
-- value (`semP`). `μ`/`ν` payloads are first-order, so the base-type
-- conversions `injB`/`prjB` are all the functor layers need.
------------------------------------------------------------------------

module Once.Internal.GradedOps where

open import Once.Spec.Type using (Base)
open import Once.Spec.Type using (Ty; Fun; KCtx; WFFun)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type.Poly
open import Once.Internal.Type.Sub
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Spec.Type using (wf-K; wf-Id)
open import Once.Internal.Type.WellFormed using (WellFormedF; wf-Sum; wf-Prod; IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; IsConcrete; con-base; con-fun)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
import Once.Internal.Value Carrier Carrier as Val
open import Once.Internal.Value Carrier Carrier using (⟦_⟧F; sem-fmap; sem-cata; sem-In; coerce-ν-in; coerce-ν-out)
open import Once.Internal.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Name using (CanonicalName)
open import Once.Internal.Name using (showCanonical)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Internal.Contract using (ISig; Impl; key; valueOf)
open import Once.Internal.ContractLaws using (value-∈; base-contract)
open import Once.Internal.Trace using (T; ret; call; halt; returnT; fmapT)
open import Once.Internal.Stream using (νᵈ; anaᵈ; seqF; module νᵈ)
open νᵈ using (forceᵈ)
open import Once.Internal.Iterative
  using (T∞; return∞; fmap∞; seqF∞; embed)
open Once.Internal.Iterative.T∞ using (force)
open import Once.Internal.Trace using (callOp; haltOp)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Internal.Graded
open Once.Internal.Graded.νᵖ using (forceᵖ)

------------------------------------------------------------------------
-- The grade's functor action.
------------------------------------------------------------------------

fmapM : ∀ π {X Y} → (X → Y) → M π X → M π Y
fmapM pure f m = f m
fmapM act  f m = fmapT f m
fmapM eff  f m = fmap∞ f m

------------------------------------------------------------------------
-- Base types: the graded value IS the machine value, up to the products and
-- sums `⟦_⟧ᵛ` and `Val.⟦_⟧` each build.
------------------------------------------------------------------------

injB : ∀ {m} {Δₖ : KCtx m} {A : Ty m} → Base Δₖ A → Val.⟦ A ⟧ → ⟦ A ⟧ᵛ
injB base-Unit   x = x
injB base-Void   x = x
injB base-Int    x = x
injB base-Float  x = x
injB (base-Prod a b) (x , y) = injB a x , injB b y
injB (base-Sum a b) (inj₁ x) = inj₁ (injB a x)
injB (base-Sum a b) (inj₂ y) = inj₂ (injB b y)

prjB : ∀ {m} {Δₖ : KCtx m} {A : Ty m} → Base Δₖ A → ⟦ A ⟧ᵛ → Val.⟦ A ⟧
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

cfᵛ : ∀ {m} {Δₖ : KCtx m} {F : Fun m} (C : Ty m) → WFFun Δₖ F → ⟦ ⟦ F ⟧T C ⟧ᵛ → ⟦ F ⟧F ⟦ C ⟧ᵛ
cfᵛ C (wf-K ib)     x        = prjB ib x
cfᵛ C wf-Id         x        = x
cfᵛ C (wf-Sum f g)  (inj₁ x) = inj₁ (cfᵛ C f x)
cfᵛ C (wf-Sum f g)  (inj₂ y) = inj₂ (cfᵛ C g y)
cfᵛ C (wf-Prod f g) (x , y)  = cfᵛ C f x , cfᵛ C g y

cf⁻¹ᵛ : ∀ {m} {Δₖ : KCtx m} {F : Fun m} (C : Ty m) → WFFun Δₖ F → ⟦ F ⟧F ⟦ C ⟧ᵛ → ⟦ ⟦ F ⟧T C ⟧ᵛ
cf⁻¹ᵛ C (wf-K ib)     x        = injB ib x
cf⁻¹ᵛ C wf-Id         x        = x
cf⁻¹ᵛ C (wf-Sum f g)  (inj₁ x) = inj₁ (cf⁻¹ᵛ C f x)
cf⁻¹ᵛ C (wf-Sum f g)  (inj₂ y) = inj₂ (cf⁻¹ᵛ C g y)
cf⁻¹ᵛ C (wf-Prod f g) (x , y)  = cf⁻¹ᵛ C f x , cf⁻¹ᵛ C g y

-- Sequence a layer of grade-`π` computations (at `pure`, there is nothing to
-- run). It needs the grade's UNIT — a layer with no recursive position runs
-- nothing — so it is defined at the grades that have one (`pure ⊑π π`).
seqM : ∀ {m} {π} → pure ⊑π π → (G : Fun m) {X : Set} → ⟦ G ⟧F (M π X) → M π (⟦ G ⟧F X)
seqM ⊑-pure G x = x
seqM ⊑-pa   G x = seqF G x
seqM ⊑-pe   G x = seqF∞ G x

------------------------------------------------------------------------
-- μ: introduction and the fold.
------------------------------------------------------------------------

in-valueᵛ : ∀ {m} {Δₖ : KCtx m} {F : Fun m} → WFFun Δₖ F → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᵛ → ⟦ μ-type F ⟧ᵛ
in-valueᵛ {F = F} wf x = sem-In F (cfᵛ (μ-type F) wf x)

-- The fold at a grade with a unit (a fold traverses its layer).
cata-semᵛ : ∀ {m} {Δₖ : KCtx m} {π} → pure ⊑π π → ∀ {A : Ty m} {F : Fun m} → WFFun Δₖ F
          → (⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) → ⟦ μ-type F ⟧ᵛ → M π ⟦ A ⟧ᵛ
cata-semᵛ {π = π} u {F} {A} wf alg =
  sem-cata wf (λ fc → bindM π (seqM u F fc) λ layer → alg (cf⁻¹ᵛ A wf layer))

-- The functor's action on one layer at grade `π`: run `h` at every recursive
-- position and sequence the results (a plain map at `pure`, Kleisli at `eff`).
-- What a fold does to one layer before its algebra; the fold's laws
-- (`Spec.Metatheory.Recursion`) are stated with it.
mapLayerᵛ : ∀ {m} {Δₖ : KCtx m} {π} → pure ⊑π π → ∀ {A B : Ty m} {F : Fun m} → WFFun Δₖ F
          → (⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ) → ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ ⟦ F ⟧T B ⟧ᵛ
mapLayerᵛ {π = π} u {F} {A} {B} wf h x = fmapM π (cf⁻¹ᵛ B wf) (seqM u F (sem-fmap F h (cfᵛ A wf x)))

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

-- `pure ⊑ act` at ν: a pure stream is one whose layers are finite trees that
-- emit nothing and always arrive (D313).
embνᵃ    : ∀ {H} → νᵖ H → νᵈ H
mapEmbνᵃ : ∀ (H G : SFunctor) → ⟦ G ⟧SF (νᵖ H) → ⟦ G ⟧SF (νᵈ H)
forceᵈ (embνᵃ {H} v) = ret (mapEmbνᵃ H H (forceᵖ v))
mapEmbνᵃ H (SK B)     x        = x
mapEmbνᵃ H SId        x        = embνᵃ x
mapEmbνᵃ H (G₁ S⊕ G₂) (inj₁ x) = inj₁ (mapEmbνᵃ H G₁ x)
mapEmbνᵃ H (G₁ S⊕ G₂) (inj₂ y) = inj₂ (mapEmbνᵃ H G₂ y)
mapEmbνᵃ H (G₁ S⊗ G₂) (x , y)  = mapEmbνᵃ H G₁ x , mapEmbνᵃ H G₂ y

-- `unfold c s` at coalgebra grade `π` — the stream, a VALUE (building it runs
-- nothing; the rule embeds it at the grade it is built at) — given the
-- coalgebra's FUNCTION `clo` (its term was evaluated once, when the stream was
-- built — D273, as the IR's `Ana` and `cata`'s algebra, D131) and the seed. A
-- pure ν needs a pure coalgebra function; an effectful one runs the function in
-- each forced layer — a server is such a stream (D233), its coalgebra reads the
-- next request.
ana-semᵛ : ∀ {m} {Δₖ : KCtx m} {A : Ty m} {F : Fun m} (φ : Finite) → WFFun Δₖ F
         → (⟦ A ⟧ᵛ → M (fin φ) ⟦ ⟦ F ⟧T A ⟧ᵛ) → ⟦ A ⟧ᵛ → ⟦ ν-type F φ ⟧ᵛ
ana-semᵛ {F = F} {A = A} pureᶠ wf clo a =
  anaᵖ (translateF Carrier Carrier F) (λ a′ → coerce-ν-in F _ (cfᵛ A wf (clo a′))) a
ana-semᵛ {F = F} {A = A} actᶠ wf clo a =
  anaᵈ (translateF Carrier Carrier F) (λ a′ → fmapT (λ l → coerce-ν-in F _ (cfᵛ A wf l)) (clo a′)) a

out-semᵛ : ∀ {m} {Δₖ : KCtx m} φ {F : Fun m} → WFFun Δₖ F → ⟦ ν-type F φ ⟧ᵛ → M (fin φ) ⟦ ⟦ F ⟧T (ν-type F φ) ⟧ᵛ
out-semᵛ pureᶠ {F} wf v = cf⁻¹ᵛ (ν-type F pureᶠ) wf (coerce-ν-out wf _ (forceᵖ v))
out-semᵛ actᶠ  {F} wf v = fmapT (λ layer → cf⁻¹ᵛ (ν-type F actᶠ) wf (coerce-ν-out wf _ layer)) (forceᵈ v)

------------------------------------------------------------------------
-- Subtyping coercions (D226), graded.
------------------------------------------------------------------------

⟦_⟧<:ᵛ : ∀ {m} {A B : Ty m} → A <: B → ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ
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
⟦ sub-ν {f = pureᶠ} {pureᶠ} _ ⟧<:ᵛ x = x
⟦ sub-ν {f = actᶠ}  {actᶠ}  _ ⟧<:ᵛ x = x
⟦ sub-ν {f = pureᶠ} {actᶠ}  _ ⟧<:ᵛ x = embνᵃ x
⟦ sub-ν {f = actᶠ}  {pureᶠ} () ⟧<:ᵛ
⟦ sub-rigid ⟧<:ᵛ x = x

------------------------------------------------------------------------
-- An FFI reference (`⊢sigop`), plan 0.105. A PURE contract is the
-- interpretation's pure half at its argument — a value, so a pure reference is
-- referentially transparent by its type. An effectful arrow's application is
-- the GENERIC EFFECT (`opCallᵀ`): a call the interpretation answers, an
-- emitted event, or a halt — a finite block, embedded into `T∞` at `eff`.
-- Contracts are
-- first-order (`IsConcrete`), so both sides cross by the base conversions.
------------------------------------------------------------------------

-- A foreign operation's call (the generic effect), a finite tree (`act`, D313):
-- the call, which returns or halts. The form `arrow-sem-eff` decides.
opCallᵀ : ∀ {m} {Δₖ : KCtx m} {A B : Ty m} → CanonicalName → Base Δₖ A → Dec (B ≡ Void) → Dec (B ≡ Unit) → Val.⟦ A ⟧ → T Val.⟦ B ⟧
opCallᵀ {A = A} cn bA (yes refl) _          x = halt (haltOp cn A bA) x
opCallᵀ {A = A} cn bA (no _)     (yes refl) x = call (callOp cn A bA Unit) x (λ _ → ret tt)
opCallᵀ {A = A} {B = B} cn bA (no _) (no _)     x = call (callOp cn A bA B) x ret

-- Plan 0.105 (D257 amendment 2): a reference to a SigOp the program is compiled
-- against (`m`: its declaration in `Σ`). A VALUE contract reads the
-- implementation (`valueOf`, the reading every layer shares); an effectful
-- arrow's application is its call, answered when the program runs.
sigOpRefᵛ : ∀ {m} {A : Ty m} → TargetNum → (Σ : ISig) → Impl Σ → (cn : CanonicalName) → IsConcrete A
          → (showCanonical cn , A) ∈ Σ → ⟦ A ⟧ᵛ
sigOpRefᵛ {A = A} fmt Σ I cn (con-base ib) m =
  injB ib (valueOf I (key (showCanonical cn) Unit A) (value-∈ m (base-contract (showCanonical cn) ib)) tt)
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero pure} bDom bCod) m =
  λ _ → injB bCod (valueOf I (key (showCanonical cn) Unit Cod) (value-∈ m refl) tt)
-- An effectful erased arrow is a CALL with the erased slot `tt` (D250).
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero eff} bDom bCod) m =
  λ _ → embed (fmapT (injB bCod) (opCallᵀ cn base-Unit (isVoid? Cod) (isUnit? Cod) tt))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One pure} bDom bCod) m =
  λ a → injB bCod (valueOf I (key (showCanonical cn) Dom Cod) (value-∈ m refl) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many pure} bDom bCod) m =
  λ a → injB bCod (valueOf I (key (showCanonical cn) Dom Cod) (value-∈ m refl) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One eff} bDom bCod) m =
  λ a → embed (fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) (prjB bDom a)))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many eff} bDom bCod) m =
  λ a → embed (fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) (prjB bDom a)))
sigOpRefᵛ fmt Σ I cn (con-fun {B = Cod} {k = mk-kind Zero act} bDom bCod) m =
  λ _ → fmapT (injB bCod) (opCallᵀ cn base-Unit (isVoid? Cod) (isUnit? Cod) tt)
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One act} bDom bCod) m =
  λ a → fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) (prjB bDom a))
sigOpRefᵛ fmt Σ I cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many act} bDom bCod) m =
  λ a → fmapT (injB bCod) (opCallᵀ cn bDom (isVoid? Cod) (isUnit? Cod) (prjB bDom a))

