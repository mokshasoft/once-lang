-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.GradedDomain — the SPEC's value domain (D250, plan 0.104 A.1).
--
-- `pure` is referential transparency. A derivation at grade `π` denotes a
-- function into `M π`, where `M pure` is the identity and `M eff` is the trace
-- monad `T`. So a pure term denotes a VALUE, and a pure arrow is a TOTAL
-- function: `⟦ Int ⇒[ pure ] Int ⟧ᵛ = ℤ → ℤ`. This is a model because the pure
-- fragment is total (D241: no general recursion, only `fold`/`unfold`; every
-- pure primitive's contract returns).
--
-- The Kleisli domain `⟦_⟧ᴰ` (`ValueDomain`) is purity-blind. It stays the
-- implementation side's (the surface-expression semantics SD and the IR's
-- `evalᴰ`), and `MeaningRelation` relates the two.
--
-- `μ` and `ν` payloads are first-order (`WellFormedF` puts `K` only at base
-- types), so no graded arrow occurs inside them: `μ` is `Val`'s data as in
-- `⟦_⟧ᴰ`, an effectful `ν` is `⟦_⟧ᴰ`'s `νᵈ`, and a pure `ν` is plain codata
-- (`νᵖ`, the final coalgebra in Set).
------------------------------------------------------------------------

module Once.Denotation.GradedDomain where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Type.Grade
open import Once.Spec.Type
open import Once.Spec.Type.Poly
open import Once.Type
open import Once.Spec.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-prod; ⊑-pp; ⊑-ep; pure⊑)
import Once.Semantics.Machine as Val
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; ⟦_⟧SF)
open import Once.Functor.Translate using (translateF)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.ValueDomain using (νᵈ)
open import Once.Spec.Iterative using (T∞; return∞; _>>=∞_; embed; ν∞; TreeEq∞)

------------------------------------------------------------------------
-- The grade's monad.
------------------------------------------------------------------------

M : Purity → Set → Set
M pure X = X
M eff  X = T X
M prod X = T∞ X

-- The identity monad's bind: application. It is OPAQUE so that a pure meaning
-- keeps the shape of its evaluation order (`m >>=ᵖ k`, not the reduct `k m`):
-- the meaning-preservation proofs relate two meanings bind by bind, exactly as
-- they do at `T`. The value is what `>>=ᵖ-β` says it is.
infixl 1 _>>=ᵖ_
opaque
  _>>=ᵖ_ : ∀ {X Y : Set} → X → (X → Y) → Y
  m >>=ᵖ k = k m




infixl 1 bindM
bindM : ∀ π {X Y} → M π X → (X → M π Y) → M π Y
bindM pure m k = m >>=ᵖ k
bindM eff  m k = m >>=T k
bindM prod m k = m >>=∞ k

-- Subeffecting is the monad morphism `M π → M π′`: the unit into a grade with
-- effects, and the embedding of the finite trees into the possibly infinite
-- ones (D311).
subM : ∀ {π π′} → π ⊑π π′ → ∀ {X} → M π X → M π′ X
subM ⊑-pure m = m
subM ⊑-eff  m = m
subM ⊑-pe   m = returnT m
subM ⊑-prod m = m
subM ⊑-pp   m = return∞ m
subM ⊑-ep   m = embed m

-- The unit of every grade: a pure value, subeffected (what the core does when a
-- variable is used at grade `π`, `⊢sub-eff (pure⊑ π) (⊢var i)`).
returnM : ∀ π {X} → X → M π X
returnM π x = subM (pure⊑ π) x


-- Two computations at a grade are EQUAL: as values or finite trees, `≡`; as
-- trees that may be infinite (`prod`), bisimilar (D201, D311).
EqM : ∀ π {X : Set} → M π X → M π X → Set
EqM pure m m′ = m ≡ m′
EqM eff  m m′ = m ≡ m′
EqM prod m m′ = TreeEq∞ _≡_ m m′

-- Every grade embeds into the completely iterative monad: the ONE erasure of
-- a grade (D311), what coherence and the observation read a computation as.
toT∞ : ∀ π {X} → M π X → T∞ X
toT∞ pure m = return∞ m
toT∞ eff  m = embed m
toT∞ prod m = m

-- The GRADED bind (D311): run a `π₁` computation, then a `π₂` one; the whole
-- is at the product `π₁ ·p π₂`. The grades form an ordered monoid, so `M` is a
-- graded monad; `bindM π` is its diagonal.
infixl 1 bindᵍ
bindᵍ : ∀ π₁ π₂ {X Y} → M π₁ X → (X → M π₂ Y) → M (π₁ ·p π₂) Y
bindᵍ pure π₂   m k = m >>=ᵖ k
bindᵍ eff  pure m k = m >>=T λ x → returnT (k x)
bindᵍ eff  eff  m k = m >>=T k
bindᵍ eff  prod m k = embed m >>=∞ k
bindᵍ prod π₂   m k = m >>=∞ λ x → toT∞ π₂ (k x)

------------------------------------------------------------------------
-- Pure codata: the final coalgebra of a first-order functor in Set.
------------------------------------------------------------------------

record νᵖ (F : SFunctor) : Set where
  coinductive
  field
    forceᵖ : ⟦ F ⟧SF (νᵖ F)


------------------------------------------------------------------------
-- The graded value domain.
------------------------------------------------------------------------

⟦_⟧ᵛ : Type → Set
⟦ Unit ⟧ᵛ       = ⊤
⟦ Void ⟧ᵛ       = ⊥
⟦ A * B ⟧ᵛ      = ⟦ A ⟧ᵛ × ⟦ B ⟧ᵛ
⟦ A + B ⟧ᵛ      = ⟦ A ⟧ᵛ ⊎ ⟦ B ⟧ᵛ
-- D143: an erased argument has no runtime existence. D250: the codomain is the
-- arrow's grade's monad, so a pure arrow is a total function.
⟦ A ⇒[ mk-kind Zero π ] B ⟧ᵛ = ⊤ → M π ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind One  π ] B ⟧ᵛ = ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ
⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ = ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ
⟦ μ-type F ⟧ᵛ   = Val.⟦ μ-type F ⟧
⟦ ν-type F pure ⟧ᵛ = νᵖ (translateF Carrier Carrier F)
⟦ ν-type F eff ⟧ᵛ  = νᵈ (translateF Carrier Carrier F)
⟦ ν-type F prod ⟧ᵛ = ν∞ (translateF Carrier Carrier F)
⟦ Int ⟧ᵛ        = Val.⟦ Int ⟧
⟦ Float ⟧ᵛ      = Val.⟦ Float ⟧
-- D243: no runtime value of a rigid parameter (used at ground instances only).
⟦ rigid _ _ ⟧ᵛ  = ⊥
