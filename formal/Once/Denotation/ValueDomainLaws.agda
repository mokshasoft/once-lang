-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ValueDomainLaws
--
-- D193: coinductive laws for the EFFECTFUL final coalgebra `νᵈ`, split out
-- of the kernel for the same reason `Once.Semantics.Functor.Laws` is split
-- out of `Once.Semantics.Functor`: so a module that only needs `anaᵈ` and
-- `forceᵈ` does not drag in the coalgebraic-extensionality axiom.
--
-- WHY THIS EXISTS. `ValueDomain` states, correctly, that the erasure
-- round-trip needs "no bisimulation and no axiom, because `anaᵈ` is indexed
-- by the SFunctor" — `anaᵈ-erase` only ever needs `cong` over a coalgebra
-- EQUALITY. That is true of erasure and false of every RELATIONAL statement
-- about a ν, because relatedness of coalgebras is strictly weaker than
-- equality. `MeaningBridge` needs exactly such a statement: the two meanings
-- of an `ana` are built from coalgebras the logical relation relates, and the
-- observational relation at a ν is propositional equality.
--
-- So this module gives `νᵈ` the three things `νS` has had since plan 0.47:
-- a bisimulation, the unfold-respects-bisimulation lemma, and the
-- extensionality axiom. `_∼ᵈ_` differs from `_∼S_` in exactly the way `νᵈ`
-- differs from `νS` — the layer is a COMPUTATION (plan 0.105: a tree), so
-- bisimilarity asks for the same calls, answered alike, ending in related
-- layers: the tree relation `RelT′` at the layer relation.
------------------------------------------------------------------------

module Once.Denotation.ValueDomainLaws where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Denotation.TraceMonad using (T; ret; call; halt; RelT′; rel-ret; rel-call; rel-halt)
open import Once.Denotation.ValueDomain using (νᵈ; forceᵈ; anaᵈ; mapAnaᵈ; anaTree)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)

------------------------------------------------------------------------
-- The bisimulation
------------------------------------------------------------------------

-- Two effectful ν values are bisimilar when forcing them gives RELATED TREES:
-- the same calls, continuing relatedly at every answer, halting alike, and
-- ending in layers related with bisimilarity again at the recursive positions.
-- (Plan 0.105: before the tree, this was two fields — equal traces at every
-- budget, and `Res`-related layers; `RelT′` is both at once.)
record _∼ᵈ_ {F : SFunctor} (x y : νᵈ F) : Set where
  coinductive
  field
    force-∼ : RelT′ (⟦ F ⟧SF-rel (_∼ᵈ_ {F})) (forceᵈ x) (forceᵈ y)

open _∼ᵈ_

-- D201: `bisimᵈ-to-eq` — coalgebraic extensionality at the effectful ν — is
-- GONE, and this module is AXIOM-FREE: the observational relation at a
-- coinductive type IS bisimilarity.

------------------------------------------------------------------------
-- Bisimilarity is reflexive — coinductively, with no axiom
------------------------------------------------------------------------

mutual
  ∼ᵈ-refl : ∀ {H : SFunctor} (x : νᵈ H) → x ∼ᵈ x
  force-∼ (∼ᵈ-refl {H} x) = tree-refl H H (forceᵈ x)

  -- Structural on the forced tree.
  tree-refl : ∀ (H G : SFunctor) (m : T (⟦ G ⟧SF (νᵈ H)))
            → RelT′ (⟦ G ⟧SF-rel (_∼ᵈ_ {H})) m m
  tree-refl H G (ret x)      = rel-ret (SF-rel-refl H G x)
  tree-refl H G (call o a k) = rel-call λ b → tree-refl H G (k b)
  tree-refl H G (halt o a)   = rel-halt

  SF-rel-refl : ∀ (H G : SFunctor) (x : ⟦ G ⟧SF (νᵈ H))
              → ⟦ G ⟧SF-rel (_∼ᵈ_ {H}) x x
  SF-rel-refl H (SK B)     x        = refl
  SF-rel-refl H SId        x        = ∼ᵈ-refl x
  SF-rel-refl H (G₁ S⊕ G₂) (inj₁ x) = SF-rel-refl H G₁ x
  SF-rel-refl H (G₁ S⊕ G₂) (inj₂ y) = SF-rel-refl H G₂ y
  SF-rel-refl H (G₁ S⊗ G₂) (x , y)  = SF-rel-refl H G₁ x , SF-rel-refl H G₂ y

------------------------------------------------------------------------
-- The unfold respects the relation
------------------------------------------------------------------------

-- What a coalgebra must satisfy to unfold related seeds to bisimilar values:
-- on related seeds its computations are related trees with `R`-related layers.
-- Stated over an arbitrary seed relation so `MeaningBridge` can instantiate
-- `R := RelV A`.
CoalgRel : ∀ (H : SFunctor) {A B : Set} (R : A → B → Set)
         → (A → T (⟦ H ⟧SF A)) → (B → T (⟦ H ⟧SF B)) → Set
CoalgRel H R c₁ c₂ = ∀ {a b} → R a b → RelT′ (⟦ H ⟧SF-rel R) (c₁ a) (c₂ b)

-- Related seeds unfold to bisimilar values. The coinductive core: `anaᵈ-∼`'s
-- corecursive call sits under `mapAnaᵈ-∼`, which is structural in `G`, and the
-- tree step `anaTree-∼` is structural in the tree, so the three are mutual
-- exactly as `anaᵈ`/`anaTree`/`mapAnaᵈ` are.
mutual
  anaᵈ-∼ : ∀ (H : SFunctor) {A B : Set} {R : A → B → Set}
           {c₁ : A → T (⟦ H ⟧SF A)} {c₂ : B → T (⟦ H ⟧SF B)}
         → CoalgRel H R c₁ c₂
         → ∀ {a b} → R a b → anaᵈ H c₁ a ∼ᵈ anaᵈ H c₂ b
  force-∼ (anaᵈ-∼ H cr r) = anaTree-∼ H cr (cr r)

  anaTree-∼ : ∀ (H : SFunctor) {A B : Set} {R : A → B → Set}
              {c₁ : A → T (⟦ H ⟧SF A)} {c₂ : B → T (⟦ H ⟧SF B)}
            → CoalgRel H R c₁ c₂
            → ∀ {m₁ : T (⟦ H ⟧SF A)} {m₂ : T (⟦ H ⟧SF B)}
            → RelT′ (⟦ H ⟧SF-rel R) m₁ m₂
            → RelT′ (⟦ H ⟧SF-rel (_∼ᵈ_ {H})) (anaTree H c₁ m₁) (anaTree H c₂ m₂)
  anaTree-∼ H cr (rel-ret rr) = rel-ret (mapAnaᵈ-∼ H H cr rr)
  anaTree-∼ H cr (rel-call h) = rel-call λ b → anaTree-∼ H cr (h b)
  anaTree-∼ H cr rel-halt     = rel-halt

  -- The layer map preserves the relation, structurally in the SHAPE functor
  -- `G` while the coalgebra stays at `H`. Mirrors `mapAnaᵈ`'s own recursion.
  mapAnaᵈ-∼ : ∀ (H G : SFunctor) {A B : Set} {R : A → B → Set}
              {c₁ : A → T (⟦ H ⟧SF A)} {c₂ : B → T (⟦ H ⟧SF B)}
            → CoalgRel H R c₁ c₂
            → ∀ {x : ⟦ G ⟧SF A} {y : ⟦ G ⟧SF B}
            → ⟦ G ⟧SF-rel R x y
            → ⟦ G ⟧SF-rel (_∼ᵈ_ {H}) (mapAnaᵈ H G c₁ x) (mapAnaᵈ H G c₂ y)
  mapAnaᵈ-∼ H (SK B)     cr rel = rel
  mapAnaᵈ-∼ H SId        cr rel = anaᵈ-∼ H cr rel
  mapAnaᵈ-∼ H (G₁ S⊕ G₂) cr {inj₁ _} {inj₁ _} rel = mapAnaᵈ-∼ H G₁ cr rel
  mapAnaᵈ-∼ H (G₁ S⊕ G₂) cr {inj₂ _} {inj₂ _} rel = mapAnaᵈ-∼ H G₂ cr rel
  mapAnaᵈ-∼ H (G₁ S⊗ G₂) cr {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) =
    mapAnaᵈ-∼ H G₁ cr r₁ , mapAnaᵈ-∼ H G₂ cr r₂
