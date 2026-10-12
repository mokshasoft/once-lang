-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Relation — the logical relation coherence is
-- proved with (plan 0.116 D1c).
--
-- `Same A` (the Spec's, `Spec.Equivalence`) observes to every finite depth
-- `n`, with the depth OUTSIDE: `∀ n → Obs n A x y`. A proof by induction on
-- derivations needs it INSIDE the trees: a computation's result is bound to
-- a variable, and a variable must be the same at every depth. `S A` is that
-- relation — by type, as `Obs`, but an arrow's results are related by
-- `TreeEq (S B)` — and `S⇔Same` shows the two agree, because `T` is
-- inductive: `∀ n` commutes with `TreeEq` (`∀-TreeEq`).
--
-- Also: the tree lemmas the proof composes (`TreeEq` is preserved by bind,
-- mapping and `toT`), stated over the graded monad `M π` through `toT`, so a
-- pure and an effectful meaning are compared as trees.
------------------------------------------------------------------------

module Once.Metatheory.Coherence.Relation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Type.Grade using (Purity; pure; eff; mk-kind; Zero; One; Many; _·p_)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid)
open import Once.Spec.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe)
open import Once.Spec.Equivalence using (TreeEq; ret≈; call≈; halt≈; Obs; Same)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; toT; bindM; returnM; subM; bindᵍ)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β)
open import Once.Denotation.TraceMonad using (T; ret; call; halt; _>>=T_; fmapT)

------------------------------------------------------------------------
-- Trees
------------------------------------------------------------------------

TreeEq-map : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
           → ∀ {m m′} → TreeEq R m m′ → TreeEq R′ m m′
TreeEq-map f (ret≈ r)  = ret≈ (f r)
TreeEq-map f (call≈ k) = call≈ (λ b → TreeEq-map f (k b))
TreeEq-map f halt≈     = halt≈

TreeEq-bind : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {m m′ : T X} {k k′ : X → T Y}
            → TreeEq R m m′ → (∀ {x y} → R x y → TreeEq R′ (k x) (k′ y))
            → TreeEq R′ (m >>=T k) (m′ >>=T k′)
TreeEq-bind (ret≈ r)  h = h r
TreeEq-bind (call≈ k) h = call≈ (λ b → TreeEq-bind (k b) h)
TreeEq-bind halt≈     h = halt≈

-- Every depth, outside, is every depth, inside: `T` is inductive. By
-- recursion on the depth-0 relation, which fixes the two trees' shape.
private
  un-ret : ∀ {X} {R : X → X → Set} {x y} → TreeEq R (ret x) (ret y) → R x y
  un-ret (ret≈ r) = r

  un-call : ∀ {X} {R : X → X → Set} {o a k k′} → TreeEq R (call o a k) (call o a k′) → ∀ b → TreeEq R (k b) (k′ b)
  un-call (call≈ f) = f

  go : ∀ {X} {R : ℕ → X → X → Set} {m m′ : T X}
     → TreeEq (R zero) m m′ → (∀ n → TreeEq (R n) m m′) → TreeEq (λ x y → ∀ n → R n x y) m m′
  go (ret≈ _)  h = ret≈ (λ n → un-ret (h n))
  go (call≈ f) h = call≈ (λ b → go (f b) (λ n → un-call (h n) b))
  go halt≈     h = halt≈

∀-TreeEq : ∀ {X} {R : ℕ → X → X → Set} (m m′ : T X)
         → (∀ n → TreeEq (R n) m m′) → TreeEq (λ x y → ∀ n → R n x y) m m′
∀-TreeEq m m′ h = go (h zero) h

-- …and back.
TreeEq-∀ : ∀ {X} {R : ℕ → X → X → Set} {m m′ : T X}
         → TreeEq (λ x y → ∀ n → R n x y) m m′ → ∀ n → TreeEq (R n) m m′
TreeEq-∀ h n = TreeEq-map (λ r → r n) h

------------------------------------------------------------------------
-- The graded monad, seen as trees
------------------------------------------------------------------------

toT-bindM : ∀ π {X Y} (m : M π X) (k : X → M π Y) → toT π (bindM π m k) ≡ (toT π m >>=T λ x → toT π (k x))
toT-bindM pure m k = cong ret (>>=ᵖ-β m k)
toT-bindM eff  m k = refl

-- The graded bind (D311) erases to `T`'s.
toT-bindᵍ : ∀ π₁ π₂ {X Y} (m : M π₁ X) (k : X → M π₂ Y)
          → toT (π₁ ·p π₂) (bindᵍ π₁ π₂ m k) ≡ (toT π₁ m >>=T λ x → toT π₂ (k x))
toT-bindᵍ pure π₂ m k = cong (toT π₂) (>>=ᵖ-β m k)
toT-bindᵍ eff  π₂ m k = refl

toT-returnM : ∀ π {X} (x : X) → toT π (returnM π x) ≡ ret x
toT-returnM pure x = refl
toT-returnM eff  x = refl

-- `⊢sub-eff` is invisible as a tree: the unit embeds a value as `ret`.
toT-subM : ∀ {π π′} (g : π ⊑π π′) {X} (m : M π X) → toT π′ (subM g m) ≡ toT π m
toT-subM ⊑-pure m = refl
toT-subM ⊑-eff  m = refl
toT-subM ⊑-pe   m = refl

-- Rewriting the two trees of a `TreeEq` along equations.
TreeEq-≡ : ∀ {X} {R : X → X → Set} {m₁ m₂ m₁′ m₂′ : T X} → m₁ ≡ m₂ → m₁′ ≡ m₂′
         → TreeEq R m₂ m₂′ → TreeEq R m₁ m₁′
TreeEq-≡ refl refl h = h

------------------------------------------------------------------------
-- The relation
------------------------------------------------------------------------

S : (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
S Unit        _ _ = ⊤
S Void        _ _ = ⊤
S Int         x y = x ≡ y
S Float       x y = x ≡ y
S (μ-type F)  x y = x ≡ y
S (rigid _ _) _ _ = ⊤
S (A * B) (a , b) (a′ , b′) = S A a a′ × S B b b′
S (A + B) (inj₁ a) (inj₁ a′) = S A a a′
S (A + B) (inj₂ b) (inj₂ b′) = S B b b′
S (A + B) (inj₁ _) (inj₂ _)  = ⊥
S (A + B) (inj₂ _) (inj₁ _)  = ⊥
S (A ⇒[ mk-kind Zero π ] B) f g = TreeEq (S B) (toT π (f tt)) (toT π (g tt))
S (A ⇒[ mk-kind One  π ] B) f g = ∀ a a′ → S A a a′ → TreeEq (S B) (toT π (f a)) (toT π (g a′))
S (A ⇒[ mk-kind Many π ] B) f g = ∀ a a′ → S A a a′ → TreeEq (S B) (toT π (f a)) (toT π (g a′))
S (ν-type F π) v w = Same (ν-type F π) v w

-- Computations related by `S`, as trees.
SM : ∀ π (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
SM π A m m′ = TreeEq (S A) (toT π m) (toT π m′)

mutual
  S→Same : ∀ (A : Type) {x y} → S A x y → Same A x y
  S→Same Unit        s n = tt
  S→Same Void        s n = tt
  S→Same Int         s n = s
  S→Same Float       s n = s
  S→Same (μ-type F)  s n = s
  S→Same (rigid _ _) s n = tt
  S→Same (A * B) {a , b} {a′ , b′} (sa , sb) n = S→Same A sa n , S→Same B sb n
  S→Same (A + B) {inj₁ a} {inj₁ a′} s n = S→Same A s n
  S→Same (A + B) {inj₂ b} {inj₂ b′} s n = S→Same B s n
  S→Same (A + B) {inj₁ _} {inj₂ _} ()
  S→Same (A + B) {inj₂ _} {inj₁ _} ()
  S→Same (A ⇒[ mk-kind Zero π ] B) s n = TreeEq-map (λ r → S→Same B r n) s
  S→Same (A ⇒[ mk-kind One  π ] B) s n a a′ h = TreeEq-map (λ r → S→Same B r n) (s a a′ (Same→S A h))
  S→Same (A ⇒[ mk-kind Many π ] B) s n a a′ h = TreeEq-map (λ r → S→Same B r n) (s a a′ (Same→S A h))
  S→Same (ν-type F π) s = s

  Same→S : ∀ (A : Type) {x y} → Same A x y → S A x y
  Same→S Unit        s = tt
  Same→S Void        s = tt
  Same→S Int         s = s zero
  Same→S Float       s = s zero
  Same→S (μ-type F)  s = s zero
  Same→S (rigid _ _) s = tt
  Same→S (A * B) {a , b} {a′ , b′} s = Same→S A (λ n → proj₁ (s n)) , Same→S B (λ n → proj₂ (s n))
  Same→S (A + B) {inj₁ a} {inj₁ a′} s = Same→S A s
  Same→S (A + B) {inj₂ b} {inj₂ b′} s = Same→S B s
  Same→S (A + B) {inj₁ _} {inj₂ _} s = s zero
  Same→S (A + B) {inj₂ _} {inj₁ _} s = s zero
  Same→S (A ⇒[ mk-kind Zero π ] B) {f} {g} s =
    TreeEq-map (Same→S B) (∀-TreeEq (toT π (f tt)) (toT π (g tt)) s)
  Same→S (A ⇒[ mk-kind One π ] B) {f} {g} s a a′ h =
    TreeEq-map (Same→S B) (∀-TreeEq (toT π (f a)) (toT π (g a′)) (λ n → s n a a′ (S→Same A h)))
  Same→S (A ⇒[ mk-kind Many π ] B) {f} {g} s a a′ h =
    TreeEq-map (Same→S B) (∀-TreeEq (toT π (f a)) (toT π (g a′)) (λ n → s n a a′ (S→Same A h)))
  Same→S (ν-type F π) s = s
