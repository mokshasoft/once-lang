-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceMonad — the metatheoretic trace monad `T`.
--
-- Plan 0.46 (M1). `T` is the codomain of the denotational trace
-- semantics `⟦_⟧ᴰ`: an effectful arrow `A ⇒[ eff ] B` denotes the Kleisli
-- arrow `⟦A⟧ᴰ → T ⟦B⟧ᴰ`, so a closure already IS a trace-producing
-- function and `⟦apply⟧ (clo , a) = clo a` threads the trace with no
-- "running" and no fuel.
--
-- T X = ℕ → List SigOpEvent × X  — a budget-indexed Writer.
--
--   * The Writer component (`List SigOpEvent`) accumulates the EFFECTFUL
--     SigOp events, in order (pure SigOps `tell []`).
--   * The `ℕ` is the event-OBSERVATION DEPTH (D058): it is consumed ONLY
--     by the productive `Ana` unfold (one F-layer per decrement) and is
--     threaded inertly everywhere else. It is NOT a step-fuel and NOT a
--     termination device — `⟦_⟧ᴰ` is total by structural recursion on the
--     IR; the `ℕ` is a parameter the productive part reads. (Finite
--     computations — every `Cata`, every total closure — ignore it and
--     emit a finite list; the single top-level `Ana` grows the trace with
--     the depth, which is exactly the apex's `∀ n`.)
--
-- `T` is the Reader(ℕ) ⊗ Writer(List SigOpEvent) monad: total, --safe,
-- no co-data. The observable is `projTrace`.
------------------------------------------------------------------------

module Once.Denotation.TraceMonad where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Once.Denotation.Trace using (SigOpEvent)

------------------------------------------------------------------------
-- The monad.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

T : Set → Set
T X = ℕ → List SigOpEvent × X

infixl 1 _>>=T_ _>>T_

returnT : ∀ {X} → X → T X
returnT x _ = ([] , x)

-- Kleisli sequencing: run `m`, then `f x`, concatenating their events in
-- order. Both sub-computations see the SAME observation depth `n`; the
-- prefix is taken at the top (`⟦src⟧ n = take n ∘ projTrace`), so capping
-- is a single top-level concern, not threaded here.
_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
(m >>=T f) n =
  let exr = m n
      eyr = f (proj₂ exr) n
  in (proj₁ exr ++ proj₁ eyr , proj₂ eyr)

_>>T_ : ∀ {X Y} → T X → T Y → T Y
m >>T k = m >>=T λ _ → k

fmapT : ∀ {X Y} → (X → Y) → T X → T Y
fmapT g m n = (proj₁ (m n) , g (proj₂ (m n)))

-- Emit events (the Writer `tell`).
tell : List SigOpEvent → T ⊤
tell es _ = (es , tt)

------------------------------------------------------------------------
-- Projections — the observable is `projTrace`.
------------------------------------------------------------------------

-- The trace (effectful SigOp events) at observation depth `n`.
projTrace : ∀ {X} → T X → ℕ → List SigOpEvent
projTrace m n = proj₁ (m n)

-- The value at observation depth `n` (internal; the apex observes only
-- the trace).
valueT : ∀ {X} → T X → ℕ → X
valueT m n = proj₂ (m n)

------------------------------------------------------------------------
-- Congruence at a fixed observation depth (the J-style bridge).
--
-- `(m >>=T f) k` reads `m` ONLY at `k`, so an equation between `m₁ k` and
-- `m₂ k` already determines the two binds at `k`. That is what this states.
--
-- WHY IT EXISTS. `rewrite` is `with`-abstraction, and a `with` cannot
-- generalise an occurrence sitting under a dependent `subst` chain — which is
-- exactly where the inner `⟦ e ⟧ˢ … k` sits in the `morph-app` denotation
-- (`subst T (cohᴰ B) (evalᴰ fmt ir (subst (λ z → z) (sym (cohᴰ A)) v))`).
-- Taking the equation as an explicit PARAMETER and consuming it with `cong`
-- sidesteps the abstraction entirely. Clauses whose wrapper is trivial
-- (`returnT (proj₁ v)` and friends) do not need this; clauses with a
-- subst-chain wrapper do.
bindAt : ∀ {X Y : Set} → (X → T Y) → ℕ → (List SigOpEvent × X) → (List SigOpEvent × Y)
bindAt f n exr = (proj₁ exr ++ proj₁ (f (proj₂ exr) n) , proj₂ (f (proj₂ exr) n))

>>=T-at : ∀ {X Y : Set} (m : T X) (f : X → T Y) (n : ℕ) → (m >>=T f) n ≡ bindAt f n (m n)
>>=T-at m f n = refl

>>=T-cong-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f : X → T Y) (n : ℕ)
             → m₁ n ≡ m₂ n → (m₁ >>=T f) n ≡ (m₂ >>=T f) n
>>=T-cong-at f n eq = cong (bindAt f n) eq

-- | The NESTED-bind version: the two binds may differ in BOTH the monadic
--   value and the continuation. `app`-shaped clauses need this — their
--   continuation mentions the argument's denotation, which also changes.
--
--   The continuation premise is pointwise at the SAME depth `n`, which is all
--   `bindAt` reads, so no extensionality is required.
bindAt-cong : ∀ {X Y : Set} (f₁ f₂ : X → T Y) (n : ℕ) {r₁ r₂ : List SigOpEvent × X}
            → r₁ ≡ r₂
            → (∀ x → f₁ x n ≡ f₂ x n)
            → bindAt f₁ n r₁ ≡ bindAt f₂ n r₂
bindAt-cong f₁ f₂ n {r} refl fe =
  cong₂ _,_ (cong (proj₁ r ++_) (cong proj₁ (fe (proj₂ r))))
            (cong proj₂ (fe (proj₂ r)))

>>=T-cong₂-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f₁ f₂ : X → T Y) (n : ℕ)
              → m₁ n ≡ m₂ n
              → (∀ x → f₁ x n ≡ f₂ x n)
              → (m₁ >>=T f₁) n ≡ (m₂ >>=T f₂) n
>>=T-cong₂-at f₁ f₂ n meq fe = bindAt-cong f₁ f₂ n meq fe
