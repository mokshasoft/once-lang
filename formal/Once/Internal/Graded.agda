-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Graded — the SPEC's value domain (D250, plan 0.104 A.1).
--
-- `pure` is referential transparency. A derivation at grade `π` denotes a
-- function into `M π`, where `M pure` is the identity, `M act` the free monad
-- `T` (finite trees: it returns, D313) and `M eff` the free completely
-- iterative monad `T∞` (it need not stop, D312). So a pure term denotes a VALUE, and a pure arrow is a TOTAL
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
-- `⟦_⟧ᴰ`, an acting `ν` is `νᵈ` (its layers are trees of `T`), and a pure `ν` is plain codata
-- (`νᵖ`, the final coalgebra in Set).
------------------------------------------------------------------------

module Once.Internal.Graded where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type.Poly
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae; pureᶠ; actᶠ)
open import Once.Spec.Word using (Carrier)
import Once.Internal.Value Carrier Carrier as Val
open import Once.Internal.Polynomial using (SFunctor; ⟦_⟧SF)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Internal.Trace using (T; returnT; _>>=T_; fmapT)
open import Once.Internal.Stream using (νᵈ)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞; embed; TreeEq∞)

------------------------------------------------------------------------
-- The grade's monad.
------------------------------------------------------------------------

M : Purity → Set → Set
M pure X = X
M act  X = T X
M eff  X = T∞ X

-- The identity monad's bind: application. It is OPAQUE so that a pure meaning
-- keeps the shape of its evaluation order (`m >>=ᵖ k`, not the reduct `k m`):
-- the meaning-preservation proofs relate two meanings bind by bind, exactly as
-- they do at `T∞`. The value is what `>>=ᵖ-β` says it is.
infixl 1 _>>=ᵖ_
opaque
  _>>=ᵖ_ : ∀ {X Y : Set} → X → (X → Y) → Y
  m >>=ᵖ k = k m


infixl 1 bindM
bindM : ∀ π {X Y} → M π X → (X → M π Y) → M π Y
bindM pure m k = m >>=ᵖ k
bindM act  m k = m >>=T k
bindM eff  m k = m >>=∞ k

-- Subeffecting is the monad morphism `M π → M π′`: the unit into a grade with
-- effects, the embedding of the finite trees into the possibly infinite ones
-- (D313), and of the guarded trees into the trees (D311).
subM : ∀ {π π′} → π ⊑π π′ → ∀ {X} → M π X → M π′ X
subM ⊑-pure m = m
subM ⊑-eff  m = m
subM ⊑-pe   m = return∞ m
subM ⊑-act  m = m
subM ⊑-pa   m = returnT m
subM ⊑-ae   m = embed m

-- The unit of a grade (`pure ⊑π π`): a
-- pure value, subeffected (what the core does when a variable is used at
-- grade `π`, `⊢sub-eff u (⊢var i)`).
returnM : ∀ {π} → pure ⊑π π → ∀ {X} → X → M π X
returnM u x = subM u x


-- Two computations at a grade are EQUAL: as values or finite trees, `≡`; as
-- trees that may be infinite, bisimilar (D201, D312).
EqM : ∀ π {X : Set} → M π X → M π X → Set
EqM pure m m′ = m ≡ m′
EqM act  m m′ = m ≡ m′
EqM eff  m m′ = TreeEq∞ _≡_ m m′

-- Every grade embeds into the completely iterative monad: the ONE erasure of
-- a grade (D311), what coherence and the observation read a computation as.
toT∞ : ∀ π {X} → M π X → T∞ X
toT∞ pure m = return∞ m
toT∞ act  m = embed m
toT∞ eff  m = m

-- The GRADED bind (D311): run a `π₁` computation, then a `π₂` one; the whole
-- is at the product `π₁ ·p π₂`. The grades form an ordered monoid, so `M` is a
-- graded monad; `bindM π` is its diagonal.
infixl 1 bindᵍ
bindᵍ : ∀ π₁ π₂ {X Y} → M π₁ X → (X → M π₂ Y) → M (π₁ ·p π₂) Y
bindᵍ pure π₂   m k = m >>=ᵖ k
bindᵍ act  pure m k = fmapT k m
bindᵍ act  act  m k = m >>=T k
bindᵍ act  eff  m k = embed m >>=∞ k
bindᵍ eff  pure m k = fmap∞ k m
bindᵍ eff  act  m k = m >>=∞ λ x → embed (k x)
bindᵍ eff  eff  m k = m >>=∞ k

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
⟦ ν-type F pureᶠ ⟧ᵛ = νᵖ (translateF Carrier Carrier F)
⟦ ν-type F actᶠ ⟧ᵛ  = νᵈ (translateF Carrier Carrier F)
⟦ Int ⟧ᵛ        = Val.⟦ Int ⟧
⟦ Float ⟧ᵛ      = Val.⟦ Float ⟧
