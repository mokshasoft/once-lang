-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.AnaTrace — the PRODUCTIVE simulation for `ana` (Plan 0.46).
--
-- The corecursive counterpart of the finite bridge (`ElaborateTrace`): the
-- denotational `evalᴰ`-trace of an anamorphism (`ana-events`, the depth-bounded
-- unfold) agrees, EVENT-PREFIX-wise, with the operational `SS.eval` unfold
-- (`anaUnfold`) at SOME fuel. The genuine `∀k → ∃s` form: the trace GROWS with
-- the observation depth `k` (productive), matched by a larger operational fuel.
-- Discharges the `ana` case of `elaborate-trace-correct`; the `νF` value is not
-- observed (we read the SigOp trace), so no value relation on the result.
--
-- TOP-DOWN: the inductive step `ana-trace-step` is PROVEN from two precisely
-- named sub-obligations + the depth IH:
--   * `coalg-step`   — one coalgebra application corresponds: beyond a threshold
--     fuel the operational `apply coalgV` yields the operational layer `flayer`
--     with EXACTLY the denotational coalgebra trace, and `flayer` relates to the
--     denotational functor layer (`LayerRel`). [Finite — a coalgebra is one
--     `A → F(A)` step; from the bridge.]
--   * `functor-walk` — given the layers relate, the denotational functor-recursion
--     events (`events-F F`) equal the operational `mapAnaF F` events. [Structural
--     induction on `F`, recursing `ana-trace-correct` at `Id` positions — the
--     depth IH.]
-- The assembly below glues them at fuel `suc (sc ⊔ sf)` (one `suc` for the
-- decrement; `⊔` so the single operational fuel serves both `apply` and `mapAnaF`).
------------------------------------------------------------------------

module Once.Verified.AnaTrace where

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; n≤m⊔n)
open import Data.List using (List; []; _++_; take)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Once.Type using (Type; Functor; ⟦_⟧T)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval as Val using ()
open import Once.Semantics.Machine using (coerce-functor; ⟦_⟧F)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.Verified.TraceDenote using (events-F)
open import Once.Verified.DenotTrace using (ana-events; evalᴰ; forget; inject)
open import Once.Verified.TraceMonad using (valueT; projTrace)
open import Once.Verified.SourceSemantics
  using (Value; Defs; Result; runTraceEval; anaUnfold; apply; mapAnaF)

module _ (defs : Defs) where

  -- The denotational↔operational relation on one functor LAYER (filled in by
  -- `functor-walk`'s eventual proof — `K` data equal, `Id` seeds related, ⊕/⊗
  -- structural). Abstract here; `coalg-step` produces it, `functor-walk` consumes it.
  postulate
    LayerRel : ∀ {F : Functor} {A : Type} → ⟦ F ⟧F Val.⟦ A ⟧ → Value → Set

  -- (a) one coalgebra step corresponds — FINITE (from the bridge).
  postulate
    coalg-step :
      ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
        (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
      → Σ[ flayer ∈ Value ] Σ[ sc ∈ ℕ ]
          ((∀ s → sc ≤ s
              → apply s defs coalgV av
                ≡ just (flayer , projTrace (evalᴰ coalgD (inject a)) k))
           × LayerRel {F} {A}
               (coerce-functor F A (forget (valueT (evalᴰ coalgD (inject a)) k)))
               flayer)

  -- (b) the functor-walk corresponds — STRUCTURAL on `F`, recursing the depth IH
  -- (`ana-trace-correct` at `k`) at `Id` positions.
  postulate
    functor-walk :
      ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
        (a : Val.⟦ A ⟧) (flayer : Value) (k : ℕ)
      → LayerRel {F} {A}
          (coerce-functor F A (forget (valueT (evalᴰ coalgD (inject a)) k)))
          flayer
      → Σ[ sf ∈ ℕ ] Σ[ layer′ ∈ Value ]
          (∀ s → sf ≤ s
             → mapAnaF s defs F F coalgV flayer
               ≡ just
                   (layer′ ,
                    events-F F (λ seed → ana-events {F} {A} coalgD seed k)
                      (coerce-functor F A (forget (valueT (evalᴰ coalgD (inject a)) k)))))

  -- THE PRODUCTIVE CORRESPONDENCE. ∀k∃s. Base (k=0): both `[]`. Step: assemble
  -- `coalg-step` + `functor-walk` at fuel `suc (sc ⊔ sf)`.
  ana-trace-correct :
    ∀ {F : Functor} {A : Type} (coalgD : IR A (⟦ F ⟧T A)) (coalgV : Value)
      (a : Val.⟦ A ⟧) (av : Value) (k : ℕ)
    → ∃[ s ] take k (ana-events {F} {A} coalgD a k)
               ≡ take k (runTraceEval (anaUnfold s defs F coalgV av))
  ana-trace-correct coalgD coalgV a av zero    = zero , refl
  ana-trace-correct {F} {A} coalgD coalgV a av (suc k)
    with coalg-step {F} {A} coalgD coalgV a av k
  ... | (flayer , sc , apply-eq , lr)
      with functor-walk {F} {A} coalgD coalgV a flayer k lr
  ...   | (sf , layer′ , mapana-eq) = suc (sc ⊔ sf) , trace-eq
    where
    MT : List SigOpEvent
    MT = events-F F (λ seed → ana-events {F} {A} coalgD seed k)
           (coerce-functor F A (forget (valueT (evalᴰ coalgD (inject a)) k)))
    trace-eq :
      take (suc k) (ana-events {F} {A} coalgD a (suc k))
        ≡ take (suc k) (runTraceEval (anaUnfold (suc (sc ⊔ sf)) defs F coalgV av))
    trace-eq rewrite apply-eq (sc ⊔ sf) (m≤m⊔n sc sf)
                   | mapana-eq (sc ⊔ sf) (n≤m⊔n sc sf) =
      cong (λ z → take (suc k)
                    (projTrace (evalᴰ coalgD (inject a)) k ++ z))
           (sym (++-identityʳ MT))
