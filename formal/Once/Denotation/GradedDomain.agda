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

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type
open import Once.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; pure⊑)
import Once.Semantics.Machine as Val
open import Once.Word using (Carrier)
open import Once.Semantics.Functor using (SFunctor; ⟦_⟧SF)
open import Once.Functor.Translate using (translateF)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.ValueDomain using (νᵈ)

------------------------------------------------------------------------
-- The grade's monad.
------------------------------------------------------------------------

M : Purity → Set → Set
M pure X = X
M eff  X = T X

-- The identity monad's bind: application. It is OPAQUE so that a pure meaning
-- keeps the shape of its evaluation order (`m >>=ᵖ k`, not the reduct `k m`):
-- the meaning-preservation proofs relate two meanings bind by bind, exactly as
-- they do at `T`. The value is what `>>=ᵖ-β` says it is.
infixl 1 _>>=ᵖ_
opaque
  _>>=ᵖ_ : ∀ {X Y : Set} → X → (X → Y) → Y
  m >>=ᵖ k = k m

opaque
  unfolding _>>=ᵖ_
  >>=ᵖ-β : ∀ {X Y : Set} (m : X) (k : X → Y) → (m >>=ᵖ k) ≡ k m
  >>=ᵖ-β m k = refl

opaque
  unfolding _>>=ᵖ_
  >>=ᵖ-assoc : ∀ {X Y Z : Set} (m : X) (f : X → Y) (g : Y → Z)
             → ((m >>=ᵖ f) >>=ᵖ g) ≡ (m >>=ᵖ λ x → f x >>=ᵖ g)
  >>=ᵖ-assoc m f g = refl

  >>=ᵖ-idʳ : ∀ {X : Set} (m : X) → (m >>=ᵖ λ x → x) ≡ m
  >>=ᵖ-idʳ m = refl


infixl 1 bindM
bindM : ∀ π {X Y} → M π X → (X → M π Y) → M π Y
bindM pure m k = m >>=ᵖ k
bindM eff  m k = m >>=T k

-- Subeffecting is the monad morphism `M pure → M eff`, the unit.
subM : ∀ {π π′} → π ⊑π π′ → ∀ {X} → M π X → M π′ X
subM ⊑-pure m = m
subM ⊑-eff  m = m
subM ⊑-pe   m = returnT m

-- The unit of every grade: a pure value, subeffected (what the core does when a
-- variable is used at grade `π`, `⊢sub-eff (pure⊑ π) (⊢var i)`).
returnM : ∀ π {X} → X → M π X
returnM π x = subM (pure⊑ π) x

-- Left identity at every grade: definitional at `eff` (T's bind on a unit), the
-- β-law of the opaque bind at `pure`.
bindM-idˡ : ∀ π {X Y} (x : X) (k : X → M π Y) → bindM π (returnM π x) k ≡ k x
bindM-idˡ pure x k = >>=ᵖ-β x k
bindM-idˡ eff  x k = refl

-- Every grade embeds into the trace monad (what compilation erases a grade to).
toT : ∀ π {X} → M π X → T X
toT pure m = returnT m
toT eff  m = m

------------------------------------------------------------------------
-- Pure codata: the final coalgebra of a first-order functor in Set.
------------------------------------------------------------------------

record νᵖ (F : SFunctor) : Set where
  coinductive
  field
    forceᵖ : ⟦ F ⟧SF (νᵖ F)

open νᵖ public

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
⟦ Int ⟧ᵛ        = Val.⟦ Int ⟧
⟦ Float ⟧ᵛ      = Val.⟦ Float ⟧
-- D243: no runtime value of a rigid parameter (used at ground instances only).
⟦ rigid _ _ ⟧ᵛ  = ⊥
