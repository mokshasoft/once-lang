{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.Monad — the graded monads' operations preserve the
-- meaning relation (plan 0.121 §3.5).
--
-- Both sides build their computations with the same operations — a block's
-- bind, the infinite trees' bind (block by block, coinductively), the
-- embedding of blocks, the units, the graded bind and the subeffect maps —
-- so related arguments give related results. The infinite cases are a
-- copattern step over an inductive walk of the block, the shape of the
-- Spec's own definitions.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

import Once.Spec.Grade
module Once.Adequacy.SpecCore.Monad (Σ : Signature) where


open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Once.Spec.Grade as LG
import Once.Internal.Type.Sub as LS
import Once.Spec.Grade as SG
import Once.Internal.Graded as LGr
import Once.Internal.GradedOps as LOps
import Once.Internal.Trace as LTr
import Once.Internal.Iterative as LI
import Once.Spec.Effect Σ as SE
import Once.Spec.Polynomial as SPoly
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β)
open import Once.Adequacy.SpecCore.Index
open import Once.Adequacy.SpecCore.Value Σ
open T∞R

------------------------------------------------------------------------
-- Blocks
------------------------------------------------------------------------

module _ {X X′ Y Y′ : Set} {R : X → X′ → Set} {S : Y → Y′ → Set} where

  bindT-R : ∀ {m m′} {k : X → LTr.T Y} {k′ : X′ → SE.T Y′}
          → TR R m m′ → (∀ {x x′} → R x x′ → TR S (k x) (k′ x′)) → TR S (m LTr.>>=T k) (m′ SE.>>=T k′)
  bindT-R (ret r)      h = h r
  bindT-R (call c a k) h = call c a (λ b → bindT-R (k b) h)
  bindT-R (halt x a)   h = halt x a

------------------------------------------------------------------------
-- Infinite trees
------------------------------------------------------------------------

return∞-R : ∀ {X X′ : Set} {R : X → X′ → Set} {x x′} → R x x′ → T∞R R (LI.return∞ x) (SE.return∞ x′)
force∞ (return∞-R r) = ret (left r)

module _ {X X′ : Set} {R : X → X′ → Set} where

  embed-R : ∀ {m m′} → TR R m m′ → T∞R R (LI.embed m) (SE.embed m′)
  embedB-R : ∀ {m m′} → TR R m m′ → TR (SumR R (T∞R R)) (LI.embedBlock m) (SE.mapT inj₁ m′)
  force∞ (embed-R r) = embedB-R r
  embedB-R (ret r)      = ret (left r)
  embedB-R (call c a k) = call c a (λ b → embedB-R (k b))
  embedB-R (halt x a)   = halt x a

module _ {X X′ Y Y′ : Set} {R : X → X′ → Set} {S : Y → Y′ → Set}
         {k : X → LI.T∞ Y} {k′ : X′ → SE.T∞ Y′}
         (h : ∀ {x x′} → R x x′ → T∞R S (k x) (k′ x′)) where

  bind∞-R : ∀ {m m′} → T∞R R m m′ → T∞R S (m LI.>>=∞ k) (m′ SE.>>=∞ k′)
  bindB-R : ∀ {b b′} → TR (SumR R (T∞R R)) b b′ → TR (SumR S (T∞R S)) (LI.bindBlock b k) (SE.bindBlock b′ k′)
  force∞ (bind∞-R r) = bindB-R (force∞ r)
  bindB-R (ret (left r))  = force∞ (h r)
  bindB-R (ret (right r)) = ret (right (bind∞-R r))
  bindB-R (call c a k₀)   = call c a (λ b → bindB-R (k₀ b))
  bindB-R (halt x a)      = halt x a

------------------------------------------------------------------------
-- The graded operations
------------------------------------------------------------------------

module _ {X X′ Y Y′ : Set} {R : X → X′ → Set} {S : Y → Y′ → Set} where

  bindᵍ-R : ∀ {π₁ π₁′ π₂ π₂′} (p₁ : PR π₁ π₁′) (p₂ : PR π₂ π₂′) {m m′} {k : X → LGr.M π₂ Y} {k′ : X′ → SE.M π₂′ Y′}
          → MR p₁ R m m′ → (∀ {x x′} → R x x′ → MR p₂ S (k x) (k′ x′))
          → MR (pr-· p₁ p₂) S (LGr.bindᵍ π₁ π₂ m k) (SE.bindᵍ π₁′ π₂′ m′ k′)
  bindᵍ-R pr-pure p₂ {m} {m′} {k} {k′} r h = subst (λ z → MR p₂ S z (k′ m′)) (sym (>>=ᵖ-β m k)) (h r)
  bindᵍ-R pr-act pr-pure r h = bindT-R r (λ x → ret (h x))
  bindᵍ-R pr-act pr-act  r h = bindT-R r h
  bindᵍ-R pr-act pr-eff  r h = bind∞-R h (embed-R r)
  bindᵍ-R pr-eff pr-pure r h = bind∞-R (λ x → return∞-R (h x)) r
  bindᵍ-R pr-eff pr-act  r h = bind∞-R (λ x → embed-R (h x)) r
  bindᵍ-R pr-eff pr-eff  r h = bind∞-R h r

  bind-R : ∀ {π π′} (p : PR π π′) {m m′} {k : X → LGr.M π Y} {k′ : X′ → SE.M π′ Y′}
         → MR p R m m′ → (∀ {x x′} → R x x′ → MR p S (k x) (k′ x′))
         → MR p S (LGr.bindM π m k) (SE.bind π′ m′ k′)
  bind-R pr-pure {m} {m′} {k} {k′} r h = subst (λ z → S z (k′ m′)) (sym (>>=ᵖ-β m k)) (h r)
  bind-R pr-act r h = bindT-R r h
  bind-R pr-eff r h = bind∞-R h r

  fmap-R : ∀ {π π′} (p : PR π π′) {m m′} {f : X → Y} {f′ : X′ → Y′}
         → MR p R m m′ → (∀ {x x′} → R x x′ → S (f x) (f′ x′))
         → MR p S (LOps.fmapM π f m) (SE.fmap π′ f′ m′)
  fmap-R pr-pure r h = h r
  fmap-R pr-act  r h = bindT-R r (λ x → ret (h x))
  fmap-R pr-eff  r h = bind∞-R (λ x → return∞-R (h x)) r

module _ {X X′ : Set} {R : X → X′ → Set} where

  sub-R : ∀ {π π′ π₀ π₀′} (g : π Once.Spec.Grade.⊑π π₀) (g′ : π′ SG.⊑π π₀′) (p : PR π π′) (p₀ : PR π₀ π₀′) {m m′}
        → MR p R m m′ → MR p₀ R (LGr.subM g m) (SE.sub g′ m′)
  sub-R Once.Spec.Grade.⊑-pure SG.⊑-pure pr-pure pr-pure r = r
  sub-R Once.Spec.Grade.⊑-eff  SG.⊑-eff  pr-eff  pr-eff  r = r
  sub-R Once.Spec.Grade.⊑-pe   SG.⊑-pe   pr-pure pr-eff  r = return∞-R r
  sub-R Once.Spec.Grade.⊑-act  SG.⊑-act  pr-act  pr-act  r = r
  sub-R Once.Spec.Grade.⊑-pa   SG.⊑-pa   pr-pure pr-act  r = ret r
  sub-R Once.Spec.Grade.⊑-ae   SG.⊑-ae   pr-act  pr-eff  r = embed-R r

------------------------------------------------------------------------
-- The loop
------------------------------------------------------------------------

module _ {X X′ : Set} {R S : X → X′ → Set} (rs : ∀ {x x′} → R x x′ → S x x′) where

  TR-map : ∀ {m m′} → TR R m m′ → TR S m m′
  TR-map (ret r)      = ret (rs r)
  TR-map (call c a k) = call c a (λ b → TR-map (k b))
  TR-map (halt x a)   = halt x a

-- Related rounds give related loops: a copattern step over the block.
module _ {A A′ B B′ : Set} {RA : A → A′ → Set} {RB : B → B′ → Set}
         {c : A → LTr.T (B ⊎ A)} {c′ : A′ → SE.T (B′ ⊎ A′)}
         (h : ∀ {a a′} → RA a a′ → TR (SumR RB RA) (c a) (c′ a′)) where

  loop-R  : ∀ {a a′} → RA a a′ → T∞R RB (LI.loop c a) (SE.loop c′ a′)
  loopB-R : ∀ {t t′} → TR (SumR RB RA) t t′
          → TR (SumR RB (T∞R RB)) (LI.loopBlock c t) (SE.treeA (SPoly.SK B′ SPoly.S⊕ SPoly.SId) c′ t′)
  force∞ (loop-R r) = loopB-R (h r)
  loopB-R (ret (left rb))  = ret (left rb)
  loopB-R (ret (right ra)) = ret (right (loop-R ra))
  loopB-R (call o ra k)    = call o ra (λ rb → loopB-R (k rb))
  loopB-R (halt x a)       = halt x a
