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
-- differs from `νS` — the layer is a COMPUTATION, so bisimilarity asks for
-- equal traces as well as related layers, at every budget.
------------------------------------------------------------------------

module Once.Denotation.ValueDomainLaws where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad using (T; valueT; projTrace)
open import Once.Denotation.ValueDomain using (νᵈ; forceᵈ; anaᵈ; mapAnaᵈ)
open import Once.Semantics.Functor using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)

------------------------------------------------------------------------
-- The bisimulation
------------------------------------------------------------------------

-- Two effectful ν values are bisimilar when forcing them agrees on BOTH
-- observables, at every budget: the events emitted, and the layer produced
-- (with bisimilarity again at the recursive positions).
--
-- The trace field is what `_∼S_` has no analogue of. Without it this would
-- relate values that emit different events, and `RelT`'s first component —
-- equal traces at every budget — could not be recovered from it.
record _∼ᵈ_ {F : SFunctor} (x y : νᵈ F) : Set where
  coinductive
  field
    traceᵈ-∼ : ∀ k → projTrace (forceᵈ x) k ≡ projTrace (forceᵈ y) k
    layerᵈ-∼ : ∀ k → ⟦ F ⟧SF-rel (_∼ᵈ_ {F}) (valueT (forceᵈ x) k)
                                            (valueT (forceᵈ y) k)

open _∼ᵈ_ public

-- D201: `bisimᵈ-to-eq` — coalgebraic extensionality at the effectful ν — is
-- GONE, and this module is now AXIOM-FREE.
--
-- It existed for exactly one reason: `RelV (ν-type F)` was propositional
-- equality, so the `ana` case of the meaning bridge had to convert the
-- bisimulation `anaᵈ-∼` proves into an `≡`. Bisimulation-implies-equality is
-- independent of MLTT, so that conversion could never have been discharged —
-- only assumed. Making the observational relation at a coinductive type BE
-- bisimilarity removes the need for it instead, which is the fourth and last
-- member of the ν defect class (`valid-ν-wf`, `obs-correct-Out`, `as-sum`,
-- `RelV (ν-type F)` — a ν modelled as if its layers were already available).
--
-- The PURE side's `bisimS-to-eq` (plan 0.47) stays: its six uses produce real
-- equalities that are substituted into other proofs, which is a different and
-- honest need.

------------------------------------------------------------------------
-- Bisimilarity is reflexive — coinductively, with no axiom
------------------------------------------------------------------------

-- D201: what the observational relation at a ν needs of it. `RelV (ν-type F)`
-- is bisimilarity (not propositional equality), so every site that used to
-- close a ν-shaped goal with `refl` closes it with this instead — and unlike
-- `refl`, it costs nothing beyond the coinduction the relation already is.
--
-- Mutual for `anaᵈ-∼`'s reason: the corecursive call sits under a map that is
-- structural in the SHAPE functor, so guardedness sees it.
mutual
  ∼ᵈ-refl : ∀ {H : SFunctor} (x : νᵈ H) → x ∼ᵈ x
  traceᵈ-∼ (∼ᵈ-refl x)     k = refl
  layerᵈ-∼ (∼ᵈ-refl {H} x) k = SF-rel-refl H H (valueT (forceᵈ x) k)

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
-- on related seeds it emits the same events and produces `R`-related layers,
-- at every budget. This is `RelT` at the layer type, stated over an arbitrary
-- seed relation so `MeaningBridge` can instantiate `R := RelV A`.
CoalgRel : ∀ (H : SFunctor) {A B : Set} (R : A → B → Set)
         → (A → T (⟦ H ⟧SF A)) → (B → T (⟦ H ⟧SF B)) → Set
CoalgRel H R c₁ c₂ =
  ∀ {a b} → R a b
  → (∀ k → projTrace (c₁ a) k ≡ projTrace (c₂ b) k)
  × (∀ k → ⟦ H ⟧SF-rel R (valueT (c₁ a) k) (valueT (c₂ b) k))

-- Related seeds unfold to bisimilar values. The coinductive core, and the
-- one place the guardedness checker is doing real work: `anaᵈ-∼`'s corecursive
-- call sits under `mapAnaᵈ-∼`, which is structural in `G`, so the two are
-- mutual exactly as `anaᵈ`/`mapAnaᵈ` are.
mutual
  anaᵈ-∼ : ∀ (H : SFunctor) {A B : Set} {R : A → B → Set}
           {c₁ : A → T (⟦ H ⟧SF A)} {c₂ : B → T (⟦ H ⟧SF B)}
         → CoalgRel H R c₁ c₂
         → ∀ {a b} → R a b → anaᵈ H c₁ a ∼ᵈ anaᵈ H c₂ b
  traceᵈ-∼ (anaᵈ-∼ H cr r) k = proj₁ (cr r) k
  layerᵈ-∼ (anaᵈ-∼ H {R = R} {c₁ = c₁} {c₂ = c₂} cr {a} {b} r) k =
    mapAnaᵈ-∼ H H cr (proj₂ (cr r) k)

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
