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
open T∞ using (force)
open TreeEq∞ using (force≈)

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
open RelT∞′

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
------------------------------------------------------------------------
-- Two runs related step for step (plan 0.119 D5: the IR means `T∞` too):
-- the same blocks — the same calls, the same silent steps — and the results
-- related by `R`. Heterogeneous bisimilarity; `TreeEq∞` is its homogeneous
-- instance.
------------------------------------------------------------------------

record RelS {X Y : Set} (R : X → Y → Set) (m : T∞ X) (m′ : T∞ Y) : Set
data RelSB {X Y : Set} (R : X → Y → Set) : T (X ⊎ T∞ X) → T (Y ⊎ T∞ Y) → Set

record RelS R m m′ where
  coinductive
  field forceS : RelSB R (force m) (force m′)
open RelS

data RelSB R where
  s-ret  : ∀ {x y} → R x y → RelSB R (ret (inj₁ x)) (ret (inj₁ y))
  s-next : ∀ {m m′} → RelS R m m′ → RelSB R (ret (inj₂ m)) (ret (inj₂ m′))
  s-call : ∀ {o a k k′} → (∀ b → RelSB R (k b) (k′ b)) → RelSB R (call o a k) (call o a k′)
  s-halt : ∀ {o a} → RelSB R (halt o a) (halt o a)

relS-ret : ∀ {X Y} {R : X → Y → Set} {x y} → R x y → RelS R (return∞ x) (return∞ y)
forceS (relS-ret r) = s-ret r

RelS-bind  : ∀ {X Y X′ Y′} {R : X → X′ → Set} {R′ : Y → Y′ → Set} {m : T∞ X} {m′ : T∞ X′}
               {k : X → T∞ Y} {k′ : X′ → T∞ Y′}
           → RelS R m m′ → (∀ {a b} → R a b → RelS R′ (k a) (k′ b))
           → RelS R′ (m >>=∞ k) (m′ >>=∞ k′)
RelSB-bind : ∀ {X Y X′ Y′} {R : X → X′ → Set} {R′ : Y → Y′ → Set} {l : T (X ⊎ T∞ X)} {l′ : T (X′ ⊎ T∞ X′)}
               {k : X → T∞ Y} {k′ : X′ → T∞ Y′}
           → RelSB R l l′ → (∀ {a b} → R a b → RelS R′ (k a) (k′ b))
           → RelSB R′ (bindBlock l k) (bindBlock l′ k′)
forceS (RelS-bind h c) = RelSB-bind (forceS h) c
RelSB-bind (s-ret r)  c = forceS (c r)
RelSB-bind (s-next h) c = s-next (RelS-bind h c)
RelSB-bind (s-call f) c = s-call (λ b → RelSB-bind (f b) c)
RelSB-bind s-halt     c = s-halt

-- Two finite trees related call for call embed as related runs.
RelSB-embed : ∀ {X Y} {R : X → Y → Set} {m : T X} {t : T Y} → RelT′ R m t → RelSB R (embedBlock m) (embedBlock t)
RelSB-embed (rel-ret r)  = s-ret r
RelSB-embed (rel-call h) = s-call (λ b → RelSB-embed (h b))
RelSB-embed rel-halt     = s-halt

RelS-embed : ∀ {X Y} {R : X → Y → Set} {m : T X} {t : T Y} → RelT′ R m t → RelS R (embed m) (embed t)
forceS (RelS-embed r) = RelSB-embed r

-- Bisimilar runs are related to the same runs (on either side).
RelSB-≈ˡ : ∀ {X Y} {R : X → Y → Set} {l l′ : T (X ⊎ T∞ X)} {u : T (Y ⊎ T∞ Y)}
         → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) l l′ → RelSB R l′ u → RelSB R l u
RelS-≈ˡ  : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y}
         → TreeEq∞ _≡_ m m′ → RelS R m′ n → RelS R m n
forceS (RelS-≈ˡ e h) = RelSB-≈ˡ (force≈ e) (forceS h)
RelSB-≈ˡ (ret≈ (done≈ refl)) (s-ret r)  = s-ret r
RelSB-≈ˡ (ret≈ (next≈ e))    (s-next h) = s-next (RelS-≈ˡ e h)
RelSB-≈ˡ (call≈ f)           (s-call h) = s-call (λ b → RelSB-≈ˡ (f b) (h b))
RelSB-≈ˡ halt≈               s-halt     = s-halt

RelSB-≈ʳ : ∀ {X Y} {R : X → Y → Set} {l : T (X ⊎ T∞ X)} {u u′ : T (Y ⊎ T∞ Y)}
         → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) u u′ → RelSB R l u′ → RelSB R l u
RelS-≈ʳ  : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {n n′ : T∞ Y}
         → TreeEq∞ _≡_ n n′ → RelS R m n′ → RelS R m n
forceS (RelS-≈ʳ e h) = RelSB-≈ʳ (force≈ e) (forceS h)
RelSB-≈ʳ (ret≈ (done≈ refl)) (s-ret r)  = s-ret r
RelSB-≈ʳ (ret≈ (next≈ e))    (s-next h) = s-next (RelS-≈ʳ e h)
RelSB-≈ʳ (call≈ f)           (s-call h) = s-call (λ b → RelSB-≈ʳ (f b) (h b))
RelSB-≈ʳ halt≈               s-halt     = s-halt

-- `embed` is a monad morphism (up to bisimilarity): a finite bind embeds as the
-- bind of the embeddings.
embed-bindB : ∀ {X Y} (m : T X) (k : X → T Y)
            → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) (embedBlock (m >>=T k)) (bindBlock (embedBlock m) (λ x → embed (k x)))
embed-bindB (ret x)      k = ≈∞-reflB (λ _ → refl) (embedBlock (k x))
embed-bindB (call o a c) k = call≈ (λ b → embed-bindB (c b) k)
embed-bindB (halt o a)   k = halt≈

embed-bind : ∀ {X Y} (m : T X) (k : X → T Y) → TreeEq∞ _≡_ (embed (m >>=T k)) (embed m >>=∞ λ x → embed (k x))
force≈ (embed-bind m k) = embed-bindB m k
