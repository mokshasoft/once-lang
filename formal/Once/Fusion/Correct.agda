-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Fusion.Correct
--
-- Correctness proofs for fusion rules.
--
-- fusion-compose is currently plain composition (g ∘ f), so its
-- correctness is trivial (refl).
--
-- OCP-0003 postulates eliminated: fusion-once-correct is now proven
-- by structural induction (escape-once descends structurally with no
-- semantic changes; same for fusion-once).
--
-- OCP-0003 Recursion Scheme Fusion Correctness:
-- ============================================
--
-- The recursion scheme fusion rules preserve semantics by the laws in
-- Category/Laws.agda. These laws justify the deforestation optimizations.
------------------------------------------------------------------------

module Once.Fusion.Correct where

open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Fusion
open import Once.Postulates using (extensionality)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

-- Alias for function extensionality
funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
funext = extensionality

------------------------------------------------------------------------
-- Correctness of fusion-compose
--
-- Currently fusion-compose is just (g ∘ f), so this is trivially refl.
------------------------------------------------------------------------

fusion-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                       → eval′ (fusion-compose g f) x ≡ eval′ (g ∘ f) x
fusion-compose-correct g f x = refl

------------------------------------------------------------------------
-- Congruence lemmas for recursion schemes
------------------------------------------------------------------------

open import Data.Integer using (ℤ)
open import Once.Semantics.Core ℤ using (sem-cata; sem-para; sem-ana; sem-hylo; sem-fuse; coerce-functor; coerce-functor⁻¹)

fusion-Cata-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧)
                 → eval′ alg ≡ eval′ alg'
                 → eval′ (Cata wf alg) x ≡ eval′ (Cata wf alg') x
fusion-Cata-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-cata wf (λ fa → ev (coerce-functor⁻¹ F _ fa)) x) eq

fusion-Para-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T (μ-type F * A)) A) (x : ⟦ μ-type F ⟧)
                 → eval′ alg ≡ eval′ alg'
                 → eval′ (Para wf alg) x ≡ eval′ (Para wf alg') x
fusion-Para-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-para wf (λ fx → ev (coerce-functor⁻¹ F _ fx)) x) eq

fusion-Ana-cong : ∀ {F A} (wf : _) (coalg coalg' : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧)
                → eval′ coalg ≡ eval′ coalg'
                → eval′ (Ana wf coalg) x ≡ eval′ (Ana wf coalg') x
fusion-Ana-cong {F} {A} wf coalg coalg' x eq =
  cong (λ ev → sem-ana F (λ a → coerce-functor F A (ev a)) x) eq

fusion-Hylo-cong-alg : ∀ {F G B} (wfF : _) (wfG : _)
                       (alg alg' : IR (⟦ F ⟧T B) B)
                       (coalg : IR (μ-type G) (⟦ F ⟧T (μ-type G)))
                       (x : ⟦ μ-type G ⟧)
                     → eval′ alg ≡ eval′ alg'
                     → eval′ (Hylo wfF wfG alg coalg) x ≡ eval′ (Hylo wfF wfG alg' coalg) x
fusion-Hylo-cong-alg {F} {G} wfF wfG alg alg' coalg x eq =
  cong (λ ev → sem-hylo F G wfF wfG
                         (λ fb → ev (coerce-functor⁻¹ F _ fb))
                         (λ μg → coerce-functor F (μ-type G) (eval′ coalg μg))
                         x) eq

fusion-Hylo-cong-coalg : ∀ {F G B} (wfF : _) (wfG : _)
                         (alg : IR (⟦ F ⟧T B) B)
                         (coalg coalg' : IR (μ-type G) (⟦ F ⟧T (μ-type G)))
                         (x : ⟦ μ-type G ⟧)
                       → eval′ coalg ≡ eval′ coalg'
                       → eval′ (Hylo wfF wfG alg coalg) x ≡ eval′ (Hylo wfF wfG alg coalg') x
fusion-Hylo-cong-coalg {F} {G} wfF wfG alg coalg coalg' x eq =
  cong (λ ev → sem-hylo F G wfF wfG
                         (λ fb → eval′ alg (coerce-functor⁻¹ F _ fb))
                         (λ μg → coerce-functor F (μ-type G) (ev μg))
                         x) eq

fusion-Fuse-cong-alg : ∀ {F G B} (wfF : _) (wfG : _)
                       (alg alg' : IR (⟦ F ⟧T B) B)
                       (tr : IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))
                       (x : ⟦ μ-type G ⟧)
                     → eval′ alg ≡ eval′ alg'
                     → eval′ (Fuse wfF wfG alg tr) x ≡ eval′ (Fuse wfF wfG alg' tr) x
fusion-Fuse-cong-alg {F} {G} wfF wfG alg alg' tr x eq =
  cong (λ ev → sem-fuse F G wfF wfG
                         (λ fb → ev (coerce-functor⁻¹ F _ fb))
                         (λ gx → coerce-functor F _ (eval′ tr (coerce-functor⁻¹ G _ gx)))
                         x) eq

fusion-Fuse-cong-tr : ∀ {F G B} (wfF : _) (wfG : _)
                      (alg : IR (⟦ F ⟧T B) B)
                      (tr tr' : IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G)))
                      (x : ⟦ μ-type G ⟧)
                    → eval′ tr ≡ eval′ tr'
                    → eval′ (Fuse wfF wfG alg tr) x ≡ eval′ (Fuse wfF wfG alg tr') x
fusion-Fuse-cong-tr {F} {G} wfF wfG alg tr tr' x eq =
  cong (λ ev → sem-fuse F G wfF wfG
                         (λ fb → eval′ alg (coerce-functor⁻¹ F _ fb))
                         (λ gx → coerce-functor F _ (ev (coerce-functor⁻¹ G _ gx)))
                         x) eq

------------------------------------------------------------------------
-- Correctness of fusion-once
------------------------------------------------------------------------

fusion-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                    → eval′ (fusion-once f) x ≡ eval′ f x
fusion-once-correct id x = refl
fusion-once-correct (g ∘ f) x =
  trans (fusion-compose-correct (fusion-once g) (fusion-once f) x)
        (trans (cong (eval′ (fusion-once g)) (fusion-once-correct f x))
               (fusion-once-correct g (eval′ f x)))
fusion-once-correct fst x = refl
fusion-once-correct snd x = refl
fusion-once-correct (⟨ f , g ⟩ m) x =
  cong₂ _,_ (fusion-once-correct f x) (fusion-once-correct g x)
fusion-once-correct (inl m) x = refl
fusion-once-correct (inr m) x = refl
fusion-once-correct (case f g) (inj₁ a) = fusion-once-correct f a
fusion-once-correct (case f g) (inj₂ b) = fusion-once-correct g b
fusion-once-correct terminal x = refl
fusion-once-correct initial ()
fusion-once-correct (curry f m) x =
  funext (λ b → fusion-once-correct f (x , b))
fusion-once-correct apply x = refl
fusion-once-correct arr x = refl
fusion-once-correct (SigOp n) x = refl
fusion-once-correct (const _ _ _) x = refl
fusion-once-correct (free-heap h) x = refl
fusion-once-correct (In wf m) x = refl
fusion-once-correct (out-μ wf) x = refl
fusion-once-correct (Cata wf alg) x =
  fusion-Cata-cong wf (fusion-once alg) alg x
                   (funext (λ y → fusion-once-correct alg y))
fusion-once-correct (Para wf alg) x =
  fusion-Para-cong wf (fusion-once alg) alg x
                   (funext (λ y → fusion-once-correct alg y))
fusion-once-correct (Out wf) x = refl
fusion-once-correct (in-ν wf m) x = refl
fusion-once-correct (Ana wf coalg) x =
  fusion-Ana-cong wf (fusion-once coalg) coalg x
                   (funext (λ y → fusion-once-correct coalg y))
fusion-once-correct (Hylo wfF wfG alg coalg) x =
  trans (fusion-Hylo-cong-alg wfF wfG (fusion-once alg) alg (fusion-once coalg) x
                              (funext (λ y → fusion-once-correct alg y)))
        (fusion-Hylo-cong-coalg wfF wfG alg (fusion-once coalg) coalg x
                              (funext (λ y → fusion-once-correct coalg y)))
fusion-once-correct (Fuse wfF wfG alg tr) x =
  trans (fusion-Fuse-cong-alg wfF wfG (fusion-once alg) alg (fusion-once tr) x
                              (funext (λ y → fusion-once-correct alg y)))
        (fusion-Fuse-cong-tr wfF wfG alg (fusion-once tr) tr x
                              (funext (λ y → fusion-once-correct tr y)))

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

fusion-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval′ (fusion-n n f) x ≡ eval′ f x
fusion-n-correct zero f x = refl
fusion-n-correct (suc n) f x =
  trans (fusion-n-correct n (fusion-once f) x)
        (fusion-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: fusion preserves semantics
------------------------------------------------------------------------

fusion-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval′ (fusion f) x ≡ eval′ f x
fusion-correct f x = fusion-n-correct 10 f x
