-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR.Semantics.StreamInf — streams whose layers are computations that need not
-- stop: the final coalgebra of `T∞ ∘ F`.
--
-- The IR is ungraded (plan 0.52 M2), so its arrows mean `T∞` arrows (plan
-- 0.119 D5, option (a)) and a coalgebra the IR unfolds is one: forcing a layer
-- of `νᴵ F` is a `T∞` computation. The core's streams (`Once.IR.Semantics.Stream`,
-- layers in `T`) embed into these (a block is one round).
--
-- D062's rule, as in `Once.IR.Semantics.Stream`: every corecursive call sits
-- structurally under a copattern or a constructor of the same mutual block —
-- the run's blocks are mapped by hand (never `fmap∞`), the functor by hand
-- (never `sfmap`).
------------------------------------------------------------------------

module Once.IR.Semantics.StreamInf where

open import Once.Spec.Type using (Fun)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.IR.Semantics.Trace using (T; ret; call; halt)
open import Once.IR.Semantics.Iterative using (T∞; fmap∞)
open T∞ using (force)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using (⟦_⟧F; coerce-ν-in)
open import Once.Spec.Polynomial using (SFunctor; SId; SK; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.IR.Semantics.FunctorMeaning using (translateF)

record νᴵ (F : SFunctor) : Set where
  coinductive
  field
    forceᴵ : T∞ (⟦ F ⟧SF (νᴵ F))

open νᴵ

in-νᴵ : ∀ {F} → ⟦ F ⟧SF (νᴵ F) → νᴵ F
force (forceᴵ (in-νᴵ layer)) = ret (inj₁ layer)

mutual
  anaᴵ : ∀ (H : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A)) → A → νᴵ H
  forceᴵ (anaᴵ H coalg a) = anaRun H coalg (coalg a)

  -- The coalgebra's run, its layer mapped into the stream.
  anaRun : ∀ (H : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A)) → T∞ (⟦ H ⟧SF A) → T∞ (⟦ H ⟧SF (νᴵ H))
  force (anaRun H coalg m) = anaBlock H coalg (force m)

  anaBlock : ∀ (H : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A))
           → T (⟦ H ⟧SF A ⊎ T∞ (⟦ H ⟧SF A)) → T (⟦ H ⟧SF (νᴵ H) ⊎ T∞ (⟦ H ⟧SF (νᴵ H)))
  anaBlock H coalg (ret (inj₁ l)) = ret (inj₁ (mapAnaᴵ H H coalg l))
  anaBlock H coalg (ret (inj₂ m)) = ret (inj₂ (anaRun H coalg m))
  anaBlock H coalg (call o a k)   = call o a (λ b → anaBlock H coalg (k b))
  anaBlock H coalg (halt o a)     = halt o a

  mapAnaᴵ : ∀ (H G : SFunctor) {A : Set} → (A → T∞ (⟦ H ⟧SF A)) → ⟦ G ⟧SF A → ⟦ G ⟧SF (νᴵ H)
  mapAnaᴵ H (SK B)     coalg x        = x
  mapAnaᴵ H SId        coalg a        = anaᴵ H coalg a
  mapAnaᴵ H (G₁ S⊕ G₂) coalg (inj₁ x) = inj₁ (mapAnaᴵ H G₁ coalg x)
  mapAnaᴵ H (G₁ S⊕ G₂) coalg (inj₂ y) = inj₂ (mapAnaᴵ H G₂ coalg y)
  mapAnaᴵ H (G₁ S⊗ G₂) coalg (x , y)  = (mapAnaᴵ H G₁ coalg x , mapAnaᴵ H G₂ coalg y)

-- Over a source functor.
anaFᴵ : ∀ {m} (F : Fun m) {A : Set}
      → (A → T∞ (⟦ F ⟧F A)) → A → νᴵ (translateF Carrier Carrier F)
anaFᴵ F {A} coalg = anaᴵ (translateF Carrier Carrier F) (λ a → fmap∞ (coerce-ν-in F A) (coalg a))
