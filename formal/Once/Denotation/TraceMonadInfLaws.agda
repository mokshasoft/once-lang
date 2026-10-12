-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceMonadInfLaws — `T∞` is a monad up to bisimilarity,
-- `T` embeds into it as a monad morphism, and the embedding does not change
-- what a run observes (D311, plan 0.117 C1).
------------------------------------------------------------------------

module Once.Denotation.TraceMonadInfLaws where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; [_]; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad
  using (T; ret; call; halt; _>>=T_; Interp; run; run-call; callAnswer; callEvent)
open import Once.Spec.Equivalence using (TreeEq)
import Once.Spec.Equivalence as TM
open import Once.Denotation.TraceMonadInf
open T∞
open TreeEq∞

------------------------------------------------------------------------
-- Bisimilarity is reflexive and a congruence for bind
------------------------------------------------------------------------

≈∞-refl : ∀ {X} {R : X → X → Set} → (∀ x → R x x) → (m : T∞ X) → TreeEq∞ R m m
≈∞-reflF : ∀ {X} {R : X → X → Set} → (∀ x → R x x) → (l : T∞F X (T∞ X)) → NodeEq R (TreeEq∞ R) l l
force≈ (≈∞-refl r m) = ≈∞-reflF r (force m)
≈∞-reflF r (ret∞ x)      = ret≈∞ (r x)
≈∞-reflF r (call∞ o a k) = call≈∞ (λ b → ≈∞-refl r (k b))
≈∞-reflF r (halt∞ o a)   = halt≈∞

-- The leaves of the first trees are related; the continuations take related
-- leaves to bisimilar trees: the binds are bisimilar.
≈∞-bind : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {m m′ : T∞ X} {k k′ : X → T∞ Y}
        → TreeEq∞ R m m′ → (∀ {x y} → R x y → TreeEq∞ R′ (k x) (k′ y))
        → TreeEq∞ R′ (m >>=∞ k) (m′ >>=∞ k′)
≈∞-bindF : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {l l′ : T∞F X (T∞ X)} {k k′ : X → T∞ Y}
         → NodeEq R (TreeEq∞ R) l l′ → (∀ {x y} → R x y → TreeEq∞ R′ (k x) (k′ y))
         → NodeEq R′ (TreeEq∞ R′) (bind∞F l k) (bind∞F l′ k′)
force≈ (≈∞-bind h c) = ≈∞-bindF (force≈ h) c
≈∞-bindF (ret≈∞ r)  c = force≈ (c r)
≈∞-bindF (call≈∞ f) c = call≈∞ (λ b → ≈∞-bind (f b) c)
≈∞-bindF halt≈∞     c = halt≈∞

------------------------------------------------------------------------
-- The embedding of the finite trees
------------------------------------------------------------------------

-- Related finite trees embed to bisimilar ones.
embed-≈ : ∀ {X} {R : X → X → Set} {m m′ : T X} → TreeEq R m m′ → TreeEq∞ R (embed m) (embed m′)
force≈ (embed-≈ (TM.ret≈ r))  = ret≈∞ r
force≈ (embed-≈ (TM.call≈ f)) = call≈∞ (λ b → embed-≈ (f b))
force≈ (embed-≈ TM.halt≈)     = halt≈∞

-- It is a monad morphism: binding then embedding is embedding then binding.
embed-bind : ∀ {X Y} (m : T X) (k : X → T Y)
           → TreeEq∞ _≡_ (embed (m >>=T k)) (embed m >>=∞ λ x → embed (k x))
force≈ (embed-bind (ret x) k)      = ≈∞-reflF (λ _ → refl) (force (embed (k x)))
force≈ (embed-bind (call o a c) k) = call≈∞ (λ b → embed-bind (c b) k)
force≈ (embed-bind (halt o a) k)   = halt≈∞

-- …and a run of the embedding observes the run of the tree: its first `n`
-- events are the first `n` the finite run makes.
events∞-embed : ∀ {X} (ι : Interp) (h : List SigOpEvent) (m : T X) (n : ℕ)
              → events∞ ι h (embed m) n ≡ take n (proj₁ (run ι h m))
events∞-call  : ∀ {X} (ι : Interp) (h : List SigOpEvent) o a (k : _ → T X) (r : Maybe _) (n : ℕ)
              → eventsC ι h o a (λ b → embed (k b)) r n ≡ take (suc n) (proj₁ (run-call ι h o a k r))
events∞-embed ι h m            zero    = refl
events∞-embed ι h (ret x)      (suc n) = refl
events∞-embed ι h (halt o a)   (suc zero)    = refl
events∞-embed ι h (halt o a)   (suc (suc n)) = refl
events∞-embed ι h (call o a k) (suc n) = events∞-call ι h o a k (callAnswer ι h o a) n
events∞-call ι h o a k (just b) n = cong (callEvent o a ∷_) (events∞-embed ι (h ++ [ callEvent o a ]) (k b) n)
events∞-call ι h o a k nothing  zero    = refl
events∞-call ι h o a k nothing  (suc n) = refl

------------------------------------------------------------------------
-- Rewriting a bisimilarity along bisimilarities of the trees: if `m₁ ≈ m₂`
-- and `m₁′ ≈ m₂′` as trees, a relation between `m₂`, `m₂′` is one between
-- `m₁`, `m₁′`. (What an equation is for `TreeEq`; `T∞` has bisimilarity
-- instead, D201.)
------------------------------------------------------------------------

≈∞-sym : ∀ {X} {m m′ : T∞ X} → TreeEq∞ _≡_ m m′ → TreeEq∞ _≡_ m′ m
≈∞-symF : ∀ {X} {l l′ : T∞F X (T∞ X)} → NodeEq _≡_ (TreeEq∞ _≡_) l l′ → NodeEq _≡_ (TreeEq∞ _≡_) l′ l
force≈ (≈∞-sym h) = ≈∞-symF (force≈ h)
≈∞-symF (ret≈∞ refl) = ret≈∞ refl
≈∞-symF (call≈∞ f)   = call≈∞ (λ b → ≈∞-sym (f b))
≈∞-symF halt≈∞       = halt≈∞

≈∞-rewrite : ∀ {X} {R : X → X → Set} {m₁ m₂ m₁′ m₂′ : T∞ X}
           → TreeEq∞ _≡_ m₁ m₂ → TreeEq∞ _≡_ m₁′ m₂′ → TreeEq∞ R m₂ m₂′ → TreeEq∞ R m₁ m₁′
≈∞-rewriteF : ∀ {X} {R : X → X → Set} {l₁ l₂ l₁′ l₂′ : T∞F X (T∞ X)}
            → NodeEq _≡_ (TreeEq∞ _≡_) l₁ l₂ → NodeEq _≡_ (TreeEq∞ _≡_) l₁′ l₂′ → NodeEq R (TreeEq∞ R) l₂ l₂′
            → NodeEq R (TreeEq∞ R) l₁ l₁′
force≈ (≈∞-rewrite e e′ h) = ≈∞-rewriteF (force≈ e) (force≈ e′) (force≈ h)
≈∞-rewriteF (ret≈∞ refl) (ret≈∞ refl) (ret≈∞ r)  = ret≈∞ r
≈∞-rewriteF (call≈∞ f)   (call≈∞ f′)  (call≈∞ g) = call≈∞ (λ b → ≈∞-rewrite (f b) (f′ b) (g b))
≈∞-rewriteF halt≈∞       halt≈∞       halt≈∞     = halt≈∞

-- Bisimilar trees with the leaves' relation weakened.
≈∞-map : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {m m′} → TreeEq∞ R m m′ → TreeEq∞ R′ m m′
≈∞-mapF : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y) → ∀ {l l′ : T∞F X (T∞ X)}
        → NodeEq R (TreeEq∞ R) l l′ → NodeEq R′ (TreeEq∞ R′) l l′
force≈ (≈∞-map f h) = ≈∞-mapF f (force≈ h)
≈∞-mapF f (ret≈∞ r)  = ret≈∞ (f r)
≈∞-mapF f (call≈∞ g) = call≈∞ (λ b → ≈∞-map f (g b))
≈∞-mapF f halt≈∞     = halt≈∞
