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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceMonad
  using (T; ret; call; halt; _>>=T_; Interp; run; run-call; callAnswer; callEvent)
open import Once.Spec.Equivalence using (TreeEq)
import Once.Spec.Equivalence as TM
open import Once.Spec.Iterative
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

------------------------------------------------------------------------
-- The monad laws, up to bisimilarity.
------------------------------------------------------------------------

open import Once.Spec.Iterative using (return∞)

≈∞-idˡ : ∀ {X Y} (x : X) (k : X → T∞ Y) → TreeEq∞ _≡_ (return∞ x >>=∞ k) (k x)
force≈ (≈∞-idˡ x k) = ≈∞-reflF (λ _ → refl) (force (k x))

≈∞-idʳ : ∀ {X} (m : T∞ X) → TreeEq∞ _≡_ (m >>=∞ return∞) m
≈∞-idʳF : ∀ {X} (l : T∞F X (T∞ X)) → NodeEq _≡_ (TreeEq∞ _≡_) (bind∞F l return∞) l
force≈ (≈∞-idʳ m) = ≈∞-idʳF (force m)
≈∞-idʳF (ret∞ x)      = ret≈∞ refl
≈∞-idʳF (call∞ o a k) = call≈∞ (λ b → ≈∞-idʳ (k b))
≈∞-idʳF (halt∞ o a)   = halt≈∞

≈∞-assoc : ∀ {X Y Z} (m : T∞ X) (f : X → T∞ Y) (g : Y → T∞ Z)
         → TreeEq∞ _≡_ ((m >>=∞ f) >>=∞ g) (m >>=∞ λ x → f x >>=∞ g)
≈∞-assocF : ∀ {X Y Z} (l : T∞F X (T∞ X)) (f : X → T∞ Y) (g : Y → T∞ Z)
          → NodeEq _≡_ (TreeEq∞ _≡_) (bind∞F (bind∞F l f) g) (bind∞F l λ x → f x >>=∞ g)
force≈ (≈∞-assoc m f g) = ≈∞-assocF (force m) f g
≈∞-assocF (ret∞ x)      f g = ≈∞-reflF (λ _ → refl) (bind∞F (force (f x)) g)
≈∞-assocF (call∞ o a k) f g = call≈∞ (λ b → ≈∞-assoc (k b) f g)
≈∞-assocF (halt∞ o a)   f g = halt≈∞

------------------------------------------------------------------------
-- A tree of `T∞` against a FINITE tree (the IR's, which is `T` until the
-- compiler runs forever too, plan 0.117 G): the same nodes, read off the
-- finite side, the leaves related by `R`. Inductive on the finite tree.
------------------------------------------------------------------------

open import Once.Denotation.TraceMonad using (T; ret; call; halt; _>>=T_; RelT′; rel-ret; rel-call; rel-halt)

data RelT∞′ {X Y : Set} (R : X → Y → Set) : T∞ X → T Y → Set where
  rel∞-ret  : ∀ {m x y} → force m ≡ ret∞ x → R x y → RelT∞′ R m (ret y)
  rel∞-call : ∀ {m o a k} {k′ : _ → T Y} → force m ≡ call∞ o a k
            → (∀ b → RelT∞′ R (k b) (k′ b)) → RelT∞′ R m (call o a k′)
  rel∞-halt : ∀ {m o a} → force m ≡ halt∞ o a → RelT∞′ R m (halt o a)

-- Only the root's node matters.
RelT∞′-force : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {t : T Y}
             → force m ≡ force m′ → RelT∞′ R m′ t → RelT∞′ R m t
RelT∞′-force e (rel∞-ret e′ r)  = rel∞-ret (trans e e′) r
RelT∞′-force e (rel∞-call e′ h) = rel∞-call (trans e e′) h
RelT∞′-force e (rel∞-halt e′)   = rel∞-halt (trans e e′)

RelT∞′-bind : ∀ {X Y X′ Y′} {R : X → X′ → Set} {R′ : Y → Y′ → Set} {m : T∞ X} {t : T X′}
                {k : X → T∞ Y} {g : X′ → T Y′}
            → RelT∞′ R m t → (∀ {a b} → R a b → RelT∞′ R′ (k a) (g b))
            → RelT∞′ R′ (m >>=∞ k) (t >>=T g)
RelT∞′-bind {m = m} {k = k} (rel∞-ret e r) c = RelT∞′-force (cong (λ l → bind∞F l k) e) (c r)
RelT∞′-bind {m = m} {k = k} (rel∞-call e h) c =
  rel∞-call (cong (λ l → bind∞F l k) e) (λ b → RelT∞′-bind (h b) c)
RelT∞′-bind {m = m} {k = k} (rel∞-halt e) c = rel∞-halt (cong (λ l → bind∞F l k) e)

-- A finite relation, embedded.
RelT∞′-embed : ∀ {X Y} {R : X → Y → Set} {m : T X} {t : T Y} → RelT′ R m t → RelT∞′ R (embed m) t
RelT∞′-embed (rel-ret r)  = rel∞-ret refl r
RelT∞′-embed (rel-call h) = rel∞-call refl (λ b → RelT∞′-embed (h b))
RelT∞′-embed rel-halt     = rel∞-halt refl
