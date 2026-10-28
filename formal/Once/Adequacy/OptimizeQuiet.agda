-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OptimizeQuiet — A TERM WITHOUT AN EFFECT RETURNS AT ONCE
-- (plan 0.39 A1).
--
-- The optimizer drops a sub-term only when `has-effect?` says it has none
-- (`terminal ∘ f`, `fst`/`snd ∘ ⟨ g , h ⟩`). Dropping it keeps the run only if
-- the sub-term's run is one finished block with no call and no end: it
-- returns a value at once. That is what this module proves, at every call
-- environment and input. A bind passes a finished value straight on, so
-- composites of such terms return at once too, and so does a fold whose
-- algebra does (by the fold's induction, `sem-cata-rel`).
------------------------------------------------------------------------

module Once.Adequacy.OptimizeQuiet where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR
open import Once.IRTy using (⌈_⌉F; fits-int; fits-float)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.IR.Semantics.Trace using (ret)
open import Once.Spec.Type using (Fun; K; Id; _⊕_; _⊗_)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; bindBlock; fmap∞; seqF∞; module T∞)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; cata-ev-algᴰ)
open import Once.Denotation.ValueRel using (FRel; fr-K; fr-Id; fr-inl; fr-inr; fr-pair; sem-cata-rel)
open import Once.Optimize using (has-effect?)

open T∞ using (force)

-- | A run that is one finished block: it returns a value at once. (A record,
-- so that its index is not unfolded to `force m`: a goal about `m >>=∞ k`
-- stays one.)
record Now {X : Set} (m : T∞ X) : Set where
  constructor now
  field
    value : X
    is    : force m ≡ ret (inj₁ value)
open Now public

now-ret : ∀ {X} (x : X) → Now (return∞ x)
now-ret x = now x refl

now-bind : ∀ {X Y} {m : T∞ X} {k : X → T∞ Y} → Now m → (∀ x → Now (k x)) → Now (m >>=∞ k)
now-bind {k = k} (now v e) h = now (value (h v)) (trans (cong (λ b → bindBlock b k) e) (is (h v)))

now-fmap : ∀ {X Y} {m : T∞ X} (f : X → Y) → Now m → Now (fmap∞ f m)
now-fmap f n = now-bind n (λ x → now-ret (f x))

-- A layer whose recursive positions all return at once is sequenced at once.
seqF∞-now : ∀ {m} (G : Fun m) {X : Set} {l l′} → FRel {X = T∞ X} {Y = T∞ X} (λ a _ → Now a) G l l′ → Now (seqF∞ G l)
seqF∞-now (K _)   fr-K          = now-ret _
seqF∞-now Id      (fr-Id n)     = n
seqF∞-now (G ⊕ H) (fr-inl r)    = now-fmap inj₁ (seqF∞-now G r)
seqF∞-now (G ⊕ H) (fr-inr r)    = now-fmap inj₂ (seqF∞-now H r)
seqF∞-now (G ⊗ H) (fr-pair r s) = now-bind (seqF∞-now G r) (λ u → now-bind (seqF∞-now H s) (λ v → now-ret (u , v)))

private
  ∨-split : ∀ a {b} → a ∨ b ≡ false → a ≡ false × b ≡ false
  ∨-split false e = refl , e
  ∨-split true  ()

-- | A term without an effect returns at once.
quiet-now : ∀ (fmt : TargetNum) (ρ : CallEnv) {A B} (f : IR A B) → has-effect? f ≡ false → ∀ a → Now (evalᴰ fmt ρ f a)
quiet-now fmt ρ id         q a = now-ret a
quiet-now fmt ρ (g ∘ f)    q a with ∨-split (has-effect? g) q
... | qg , qf = now-bind (quiet-now fmt ρ f qf a) (quiet-now fmt ρ g qg)
quiet-now fmt ρ fst        q a = now-ret _
quiet-now fmt ρ snd        q a = now-ret _
quiet-now fmt ρ ⟨ f , g ⟩  q a with ∨-split (has-effect? f) q
... | qf , qg = now-bind (quiet-now fmt ρ f qf a) (λ b → now-bind (quiet-now fmt ρ g qg a) (λ c → now-ret (b , c)))
quiet-now fmt ρ inl        q a = now-ret _
quiet-now fmt ρ inr        q a = now-ret _
quiet-now fmt ρ (case f g) q (inj₁ a) = quiet-now fmt ρ f (proj₁ (∨-split (has-effect? f) q)) a
quiet-now fmt ρ (case f g) q (inj₂ b) = quiet-now fmt ρ g (proj₂ (∨-split (has-effect? f) q)) b
quiet-now fmt ρ terminal   q a = now-ret _
quiet-now fmt ρ initial    q ()
quiet-now fmt ρ (curry f)  q a = now-ret _
quiet-now fmt ρ apply      () a
quiet-now fmt ρ (SigOp _)  () a
quiet-now fmt ρ (Call _)   () a
quiet-now fmt ρ (const fits-int v)   q a = now-ret _
quiet-now fmt ρ (const fits-float v) q a = now-ret _
quiet-now fmt ρ (In _)     q a = now-ret _
quiet-now fmt ρ (out-μ _)  q a = now-ret _
quiet-now fmt ρ (Cata {F} w {E} {C} alg) q (e , x) =
  sem-cata-rel (wf-⌈⌉ w) {R = λ m _ → Now m} {alg₁ = A₁} {alg₂ = A₁} step x
  where
    A₁ = cata-ev-algᴰ fmt ρ {F} {E} {C} w alg e
    -- the layer's children first, then the algebra on the layer
    step : ∀ {l l′} → FRel (λ m _ → Now m) ⌈ F ⌉F l l′ → Now (A₁ l)
    step {l} fr =
      now-bind (seqF∞-now ⌈ F ⌉F fr) (λ _ → quiet-now fmt ρ alg q _)
quiet-now fmt ρ (Out _)    () a
quiet-now fmt ρ (in-ν _)   q a = now-ret _
quiet-now fmt ρ (Ana _ _)  q a = now-ret _
quiet-now fmt ρ (Iter _)   () a
