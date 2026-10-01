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

open import Once.Type
open import Once.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe)
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

returnM : ∀ π {X} → X → M π X
returnM pure x = x
returnM eff  x = returnT x

infixl 1 bindM
bindM : ∀ π {X Y} → M π X → (X → M π Y) → M π Y
bindM pure m k = k m
bindM eff  m k = m >>=T k

-- Subeffecting is the monad morphism `M pure → M eff`, the unit.
subM : ∀ {π π′} → π ⊑π π′ → ∀ {X} → M π X → M π′ X
subM ⊑-pure m = m
subM ⊑-eff  m = m
subM ⊑-pe   m = returnT m

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
⟦ Str ⟧ᵛ        = Val.⟦ Str ⟧
⟦ Buffer ⟧ᵛ     = Val.⟦ Buffer ⟧
-- D243: no runtime value of a rigid parameter (used at ground instances only).
⟦ rigid _ _ ⟧ᵛ  = ⊥
