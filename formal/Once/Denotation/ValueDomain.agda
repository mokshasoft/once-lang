-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ValueDomain — the IR-FREE monadic value domain.
--
-- Extracted from `Once.Denotation.DenotTrace` (Plan 0.58, OCP-0006): the value
-- domain `⟦_⟧ᴰ`, the `forget`/`inject` coercions, and the SigOp emission
-- `emit-D` use only `Once.Type` / `Val` / the trace monad / `SigOp.Info` — NO
-- `Once.IR` (IR enters only at `evalᴰ`, which STAYS in `DenotTrace`). This is
-- the semantic-domain vocabulary the IR-free reference meaning `⟦_⟧ᵈ` lands in.
--
-- `DenotTrace` re-exports this (`open … public`), so consumers are unchanged.
------------------------------------------------------------------------

module Once.Denotation.ValueDomain where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; sym; subst)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Internal.Type.Poly
open import Once.Type
open import Once.IRTy using (IRTy; ⌈_⌉; ⌊_⌋)
import Once.Semantics.Machine as Val
open import Once.Internal.Trace using (T; ret; call; halt; returnT; fmapT; _>>=T_)
open import Once.Semantics.Machine using (⟦_⟧F; coh; tF-coh)
open import Once.Spec.Word using (Carrier)
open import Once.Internal.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Internal.Type.WellFormed using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Semantics.Machine using (coerce-ν-in)

open import Once.Internal.Stream using (νᵈ; module νᵈ; in-νᵈ; seqF; anaᵈ; anaTree; mapAnaᵈ; anaFᵈ)
open νᵈ
open import Once.Internal.Iterative using (T∞)
open import Once.Internal.StreamInf using (νᴵ)

-- SFunctor and the `⟦_⟧F → ⟦_⟧SF` coercion sits outside it.
anaᵈ-erase : ∀ {H₁ H₂ : SFunctor} (heq : H₁ ≡ H₂) {A : Set}
             (c₁ : A → T (⟦ H₁ ⟧SF A)) (c₂ : A → T (⟦ H₂ ⟧SF A)) (a : A)
           → subst (λ H → A → T (⟦ H ⟧SF A)) heq c₁ ≡ c₂
           → subst νᵈ heq (anaᵈ H₁ c₁ a) ≡ anaᵈ H₂ c₂ a
anaᵈ-erase refl c₁ c₂ a eq = cong (λ c → anaᵈ _ c a) eq

-- Carrier equality folded in, exactly as `sem-ana-erase-full` does for the
-- pure side, so consumers never hand-thread the carrier transport.
anaᵈ-erase-full : ∀ {H₁ H₂ : SFunctor} (heq : H₁ ≡ H₂) {A₁ A₂ : Set} (ceq : A₁ ≡ A₂)
    (c₁ : A₁ → T (⟦ H₁ ⟧SF A₁)) (c₂ : A₂ → T (⟦ H₂ ⟧SF A₂)) (a : A₁)
  → subst (λ H → A₂ → T (⟦ H ⟧SF A₂)) heq
      (λ x → subst (λ Z → T (⟦ H₁ ⟧SF Z)) ceq (c₁ (subst (λ z → z) (sym ceq) x)))
    ≡ c₂
  → subst νᵈ heq (anaᵈ H₁ c₁ a) ≡ anaᵈ H₂ c₂ (subst (λ z → z) ceq a)
anaᵈ-erase-full heq refl c₁ c₂ a eq = anaᵈ-erase heq c₁ c₂ a eq

-- `subst` along a `cong`ed equation is `subst` along the equation (mirrors
-- `subst-νS-cong`). `cohᴰ (ν-type F)` is `cong νᵈ (tF-coh F)`, so consumers
-- need this to reach `anaᵈ-erase`.
subst-νᵈ-cong : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) (v : νᵈ H₁)
              → subst (λ z → z) (cong νᵈ eq) v ≡ subst νᵈ eq v
subst-νᵈ-cong refl v = refl
------------------------------------------------------------------------
-- The monadic value domain. Mirrors `Val.⟦_⟧` EXCEPT at the arrow, which
-- becomes the Kleisli arrow into `T∞` (plan 0.119 D5: the IR is ungraded, so
-- an arrow is one that need not stop; a finite block embeds).
------------------------------------------------------------------------

⟦_⟧ᴰ : Type → Set
⟦ Unit ⟧ᴰ       = ⊤
⟦ Void ⟧ᴰ       = ⊥
⟦ A * B ⟧ᴰ      = ⟦ A ⟧ᴰ × ⟦ B ⟧ᴰ
⟦ A + B ⟧ᴰ      = ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ
-- D143: the arrow's meaning is GRADE-AWARE at the quantity. A `Zero`-graded
-- argument is ERASED — it has no runtime existence — so the erased arrow's
-- meaning takes NO argument. Purity is still ignored: a pure and an effectful
-- arrow over the same A, B mean the same thing (that is what plan 0.52 M2
-- established, and it stays).
--
-- WHY THIS BELONGS IN THE SPEC. Erasure is a SEMANTIC claim. While the meaning
-- was grade-blind, "a Zero-graded argument is not represented at runtime" was a
-- promise no specification made, so no compiler could be obliged to keep it —
-- and `⌊_⌋` erasing became incoherent with `coh` (the full→runtime direction
-- has no canonical inhabitant when only ONE side forgets the argument). Making
-- both sides forget it together is what restores coherence.
⟦ A ⇒[ mk-kind Zero π ] B ⟧ᴰ = ⊤ → T∞ ⟦ B ⟧ᴰ   -- erased: no argument
⟦ A ⇒[ mk-kind One  π ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ
⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ
⟦ μ-type F ⟧ᴰ   = Val.⟦ μ-type F ⟧            -- first-order data: reuse pure
-- ν is the OTHER type that suspends computation, so like the arrow it is
-- Kleisli: forcing a layer IS a `T`-computation. A ν built by an EFFECTFUL
-- coalgebra cannot be a pure value — while it was one, `Ana` had to read its
-- coalgebra at budget `0` (discarding the effects) and the effects had to be
-- re-invented by a separate eager left-to-right unfold, which ordered events
-- the anamorphism does not order. Here the order is the order the program
-- FORCES layers, which is the order the machine runs them in.
⟦ ν-type F _ ⟧ᴰ = νᴵ (translateF Carrier Carrier F)
⟦ Int ⟧ᴰ        = Val.⟦ Int ⟧
⟦ Float ⟧ᴰ      = Val.⟦ Float ⟧
-- D243: no runtime value of a rigid parameter (used at ground instances only).
⟦ rigid _ _ ⟧ᴰ  = ⊥

------------------------------------------------------------------------
-- Plan 0.52 M2: the monadic value domain over the UNGRADED IR objects
-- (`⟦_⟧ᴰᴵ := ⟦_⟧ᴰ ∘ ⌈_⌉`), used to denote IR morphisms (evalᴰ/realize) now
-- that IR objects are `IRTy`. `cohᴰ` is the transport `⟦ ⌊T⌋ ⟧ᴰᴵ ≡ ⟦ T ⟧ᴰ`
-- (μ/ν reuse the pure-domain `coh`; the arrow is grade-blind Kleisli).

⟦_⟧ᴰᴵ : IRTy → Set
⟦ A ⟧ᴰᴵ = ⟦ ⌈ A ⌉ ⟧ᴰ

cohᴰ : ∀ (T' : Type) → ⟦ ⌊ T' ⌋ ⟧ᴰᴵ ≡ ⟦ T' ⟧ᴰ
cohᴰ Unit         = refl
cohᴰ Void         = refl
cohᴰ (A * B)      = cong₂ _×_ (cohᴰ A) (cohᴰ B)
cohᴰ (A + B)      = cong₂ _⊎_ (cohᴰ A) (cohᴰ B)
-- D143: split on the quantity. At `Zero` BOTH sides forget the argument
-- (`⌊_⌋` gives `Unit ⇛ ⌊B⌋`, `⟦_⟧ᴰ` gives `⊤ → T ⟦B⟧ᴰ`), so only the codomain
-- has to be transported — which is exactly what makes erasure coherent.
cohᴰ (A ⇒[ mk-kind Zero π ] B) = cong  (λ y → ⊤ → T∞ y) (cohᴰ B)
cohᴰ (A ⇒[ mk-kind One  π ] B) = cong₂ (λ x y → x → T∞ y) (cohᴰ A) (cohᴰ B)
cohᴰ (A ⇒[ mk-kind Many π ] B) = cong₂ (λ x y → x → T∞ y) (cohᴰ A) (cohᴰ B)
cohᴰ (μ-type F)   = coh (μ-type F)
-- ν's monadic meaning is no longer its pure one, so this transport stops
-- borrowing `coh` and names its own constructor. Structurally identical.
cohᴰ (ν-type F _) = cong νᴵ (tF-coh F)
cohᴰ Int          = refl
cohᴰ Float        = refl
cohᴰ (rigid _ _)  = refl

------------------------------------------------------------------------
-- The monadic and the pure value domains agree on FIRST-ORDER values, and
-- only there (plan 0.105). At a base type they are the same set; the coercions
-- below are identities that a SigOp's argument and result, a constant, and a
-- functor's `K` position pass through.
--
-- There is no coercion at an arrow or a ν. Erasing an effectful closure to a
-- pure function would have to RUN it, and a run needs an interpretation to
-- answer its calls: there is no meaning-free erasure, so none is defined.
------------------------------------------------------------------------

forgetᵇ : ∀ {A} → IsBaseType A → ⟦ A ⟧ᴰ → Val.⟦ A ⟧
forgetᵇ base-Unit   x = x
forgetᵇ base-Void   ()
forgetᵇ base-Int    x = x
forgetᵇ base-Float  x = x
forgetᵇ (base-Prod a b) (x , y) = forgetᵇ a x , forgetᵇ b y
forgetᵇ (base-Sum a b) (inj₁ x) = inj₁ (forgetᵇ a x)
forgetᵇ (base-Sum a b) (inj₂ y) = inj₂ (forgetᵇ b y)

injectᵇ : ∀ {A} → IsBaseType A → Val.⟦ A ⟧ → ⟦ A ⟧ᴰ
injectᵇ base-Unit   x = x
injectᵇ base-Void   ()
injectᵇ base-Int    x = x
injectᵇ base-Float  x = x
injectᵇ (base-Prod a b) (x , y) = injectᵇ a x , injectᵇ b y
injectᵇ (base-Sum a b) (inj₁ x) = inj₁ (injectᵇ a x)
injectᵇ (base-Sum a b) (inj₂ y) = inj₂ (injectᵇ b y)

------------------------------------------------------------------------
-- Plan 0.58: the `⟦_⟧ᴰ`-level functor coercion — the trace-preserving mirror
-- of `coerce-functor⁻¹`. The recursion-scheme fold must carry `⟦C⟧ᴰ` (NOT the
-- forgotten `Val.⟦C⟧`) so an EFFECTFUL-arrow carrier keeps its apply-time
-- effects (the `Val`-fold's `forget`-per-layer silently dropped them). Purely
-- structural: `Id`→carrier, `⊕`/`⊗`→structural, `K A`→`inject` (a `K` value is
-- `Val.⟦A⟧`; `inject` lifts it to `⟦A⟧ᴰ`, the identity at the base types `K`
-- holds for a `WellFormedF`).
-- The FORWARD direction, the mirror of `coerce-functor` at the `ᴰ` level.
-- `Ana` needs it to hand its coalgebra to `anaᵈ`. At `K` it forgets, exactly
-- as the inverse injects — and `WellFormedF` puts `K` only at base types,
-- where `forget` is the identity.
coerce-functor-D : ∀ {F} → WellFormedF F → ∀ C → ⟦ ⟦ F ⟧T C ⟧ᴰ → ⟦ F ⟧F ⟦ C ⟧ᴰ
coerce-functor-D (wf-K b)          C x        = forgetᵇ b x
coerce-functor-D wf-Id             C x        = x
coerce-functor-D (wf-Sum wf wg)    C (inj₁ x) = inj₁ (coerce-functor-D wf C x)
coerce-functor-D (wf-Sum wf wg)    C (inj₂ y) = inj₂ (coerce-functor-D wg C y)
coerce-functor-D (wf-Prod wf wg)   C (x , y)  = (coerce-functor-D wf C x , coerce-functor-D wg C y)

coerce-functor⁻¹-D : ∀ {F} → WellFormedF F → ∀ C → ⟦ F ⟧F ⟦ C ⟧ᴰ → ⟦ ⟦ F ⟧T C ⟧ᴰ
coerce-functor⁻¹-D (wf-K b)        C x        = injectᵇ b x
coerce-functor⁻¹-D wf-Id           C x        = x
coerce-functor⁻¹-D (wf-Sum wf wg)  C (inj₁ x) = inj₁ (coerce-functor⁻¹-D wf C x)
coerce-functor⁻¹-D (wf-Sum wf wg)  C (inj₂ y) = inj₂ (coerce-functor⁻¹-D wg C y)
coerce-functor⁻¹-D (wf-Prod wf wg) C (x , y)  = (coerce-functor⁻¹-D wf C x , coerce-functor⁻¹-D wg C y)
