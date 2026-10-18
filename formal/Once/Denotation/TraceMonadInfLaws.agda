-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceMonadInfLaws — `T∞` is a monad up to bisimilarity,
-- `T` embeds into it, and a run is related to a FINITE tree (the IR's) when
-- they make the same calls and end alike (D317).
------------------------------------------------------------------------

module Once.Denotation.TraceMonadInfLaws where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Lang.Trace using (T; ret; call; halt; _>>=T_; RelT′; rel-ret; rel-call; rel-halt)
open import Once.Lang.Iterative

------------------------------------------------------------------------
-- Bisimilarity is reflexive and a congruence for bind
------------------------------------------------------------------------

≈∞-refl  : ∀ {X} {R : X → X → Set} → (∀ x → R x x) → (m : T∞ X) → TreeEq∞ R m m
≈∞-reflB : ∀ {X} {R : X → X → Set} → (∀ x → R x x) → (l : T (X ⊎ T∞ X))
         → BlockEq (StepEq R (TreeEq∞ R)) l l
force≈ (≈∞-refl r m) = ≈∞-reflB r (force m)
≈∞-reflB r (ret (inj₁ x)) = ret≈ (done≈ (r x))
≈∞-reflB r (ret (inj₂ m)) = ret≈ (next≈ (≈∞-refl r m))
≈∞-reflB r (call o a k)   = call≈ (λ b → ≈∞-reflB r (k b))
≈∞-reflB r (halt o a)     = halt≈

-- The results of the first runs are related; the continuations take related
-- results to bisimilar runs: the binds are bisimilar.
≈∞-bind  : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {m m′ : T∞ X} {k k′ : X → T∞ Y}
         → TreeEq∞ R m m′ → (∀ {x y} → R x y → TreeEq∞ R′ (k x) (k′ y))
         → TreeEq∞ R′ (m >>=∞ k) (m′ >>=∞ k′)
≈∞-bindB : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {l l′ : T (X ⊎ T∞ X)} {k k′ : X → T∞ Y}
         → BlockEq (StepEq R (TreeEq∞ R)) l l′ → (∀ {x y} → R x y → TreeEq∞ R′ (k x) (k′ y))
         → BlockEq (StepEq R′ (TreeEq∞ R′)) (bindBlock l k) (bindBlock l′ k′)
force≈ (≈∞-bind h c) = ≈∞-bindB (force≈ h) c
≈∞-bindB (ret≈ (done≈ r)) c = force≈ (c r)
≈∞-bindB (ret≈ (next≈ h)) c = ret≈ (next≈ (≈∞-bind h c))
≈∞-bindB (call≈ f)        c = call≈ (λ b → ≈∞-bindB (f b) c)
≈∞-bindB halt≈            c = halt≈

-- Returning, then continuing, is continuing.
≈∞-idˡ : ∀ {X Y} (x : X) (k : X → T∞ Y) → TreeEq∞ _≡_ (return∞ x >>=∞ k) (k x)
force≈ (≈∞-idˡ x k) = ≈∞-reflB (λ _ → refl) (force (k x))

------------------------------------------------------------------------
-- A run against a FINITE tree (the IR's, which is `T` until the compiler
-- runs forever too): the same calls, read off the finite side, and the
-- results related by `R`; the run may take finitely many silent steps on the
-- way (a loop's rounds that call nothing). Inductive, so an endless silent
-- run is related to no finite tree.
------------------------------------------------------------------------

data RelB {X Y : Set} (R : X → Y → Set) : T (X ⊎ T∞ X) → T Y → Set where
  b-ret  : ∀ {x y} → R x y → RelB R (ret (inj₁ x)) (ret y)
  b-tau  : ∀ {m t} → RelB R (force m) t → RelB R (ret (inj₂ m)) t
  b-call : ∀ {o a k} {k′ : _ → T Y} → (∀ b → RelB R (k b) (k′ b)) → RelB R (call o a k) (call o a k′)
  b-halt : ∀ {o a} → RelB R (halt o a) (halt o a)

-- A run's relation is its first block's (a record, so the run is read off its type).
record RelT∞′ {X Y : Set} (R : X → Y → Set) (m : T∞ X) (t : T Y) : Set where
  constructor rel∞
  field block : RelB R (force m) t
open RelT∞′ public

rel∞-ret : ∀ {X Y} {R : X → Y → Set} {x y} → R x y → RelT∞′ R (return∞ x) (ret y)
rel∞-ret r = rel∞ (b-ret r)

RelB-bind : ∀ {X Y X′ Y′} {R : X → X′ → Set} {R′ : Y → Y′ → Set} {l : T (X ⊎ T∞ X)} {t : T X′}
              {k : X → T∞ Y} {g : X′ → T Y′}
          → RelB R l t → (∀ {a b} → R a b → RelT∞′ R′ (k a) (g b))
          → RelB R′ (bindBlock l k) (t >>=T g)
RelB-bind (b-ret r)  c = block (c r)
RelB-bind (b-tau h)  c = b-tau (RelB-bind h c)
RelB-bind (b-call h) c = b-call (λ b → RelB-bind (h b) c)
RelB-bind b-halt     c = b-halt

RelT∞′-bind : ∀ {X Y X′ Y′} {R : X → X′ → Set} {R′ : Y → Y′ → Set} {m : T∞ X} {t : T X′}
                {k : X → T∞ Y} {g : X′ → T Y′}
            → RelT∞′ R m t → (∀ {a b} → R a b → RelT∞′ R′ (k a) (g b))
            → RelT∞′ R′ (m >>=∞ k) (t >>=T g)
RelT∞′-bind (rel∞ r) c = rel∞ (RelB-bind r c)

-- Bisimilar runs are related to the same finite tree.
RelB-≈ : ∀ {X Y} {R : X → Y → Set} {l l′ : T (X ⊎ T∞ X)} {t : T Y}
       → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) l l′ → RelB R l′ t → RelB R l t
RelB-≈ (ret≈ (done≈ refl)) (b-ret r)  = b-ret r
RelB-≈ (ret≈ (next≈ e))    (b-tau h)  = b-tau (RelB-≈ (force≈ e) h)
RelB-≈ (call≈ f)           (b-call h) = b-call (λ b → RelB-≈ (f b) (h b))
RelB-≈ halt≈               b-halt     = b-halt

RelT∞′-≈ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {t : T Y}
         → TreeEq∞ _≡_ m m′ → RelT∞′ R m′ t → RelT∞′ R m t
RelT∞′-≈ e (rel∞ r) = rel∞ (RelB-≈ (force≈ e) r)

-- A finite tree's embedding is related to whatever the tree is related to.
RelB-embed : ∀ {X Y} {R : X → Y → Set} {m : T X} {t : T Y} → RelT′ R m t → RelB R (embedBlock m) t
RelB-embed (rel-ret r)  = b-ret r
RelB-embed (rel-call h) = b-call (λ b → RelB-embed (h b))
RelB-embed rel-halt     = b-halt

RelT∞′-embed : ∀ {X Y} {R : X → Y → Set} {m : T X} {t : T Y} → RelT′ R m t → RelT∞′ R (embed m) t
RelT∞′-embed r = rel∞ (RelB-embed r)
