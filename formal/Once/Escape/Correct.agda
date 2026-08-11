-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Escape.Correct
--
-- Correctness proofs for escape analysis.
--
-- Key insight: AllocMode is semantically transparent - it is explicitly
-- ignored in the eval function (Once/Semantics.agda). Therefore, all
-- escape analysis rewrites that only change AllocMode are trivially
-- correct by refl.
--
-- OCP-0003 postulates eliminated: escape-compose is now concrete (plain
-- composition), so these are provable directly.
------------------------------------------------------------------------

module Once.Escape.Correct where

open import Once.Type
open import Once.IR
open import Once.CCC.Eval using (⟦_⟧; eval; appNatTr-F)
open import Once.Escape
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
-- Correctness of escape-compose
--
-- Trivially true since escape-compose g f = g ∘ f.
------------------------------------------------------------------------

escape-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                       → eval (escape-compose g f) x ≡ eval (g ∘ f) x
escape-compose-correct g f x = refl

------------------------------------------------------------------------
-- Congruence lemmas for recursion schemes
------------------------------------------------------------------------

open import Data.Integer using (ℤ)
open import Once.Word using (Carrier)
open import Once.Semantics.Value Carrier using (sem-cata; sem-para; sem-ana; sem-fuseNat; sem-fuseNat-cong; ⟦_⟧F; coerce-functor; coerce-functor⁻¹)

escape-Cata-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧)
                 → eval alg ≡ eval alg'
                 → eval (Cata wf alg) x ≡ eval (Cata wf alg') x
escape-Cata-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-cata wf (λ fa → ev (coerce-functor⁻¹ F _ fa)) x) eq

escape-Para-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T (μ-type F * A)) A) (x : ⟦ μ-type F ⟧)
                 → eval alg ≡ eval alg'
                 → eval (Para wf alg) x ≡ eval (Para wf alg') x
escape-Para-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-para wf (λ fx → ev (coerce-functor⁻¹ F _ fx)) x) eq

escape-Ana-cong : ∀ {F A} (wf : _) (coalg coalg' : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧)
                → eval coalg ≡ eval coalg'
                → eval (Ana wf coalg) x ≡ eval (Ana wf coalg') x
escape-Ana-cong {F} {A} wf coalg coalg' x eq =
  cong (λ ev → sem-ana F (λ a → coerce-functor F A (ev a)) x) eq


------------------------------------------------------------------------
-- Correctness of escape-once
--
-- escape-once descends structurally, preserving AllocMode which is
-- semantically transparent.
------------------------------------------------------------------------

escape-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                    → eval (escape-once f) x ≡ eval f x
-- D062: `escape-nt` preserves the natural transform's meaning, pointwise.
appNatTr-escape : ∀ {G F} (t : NatTr G F) {X : Set} (g : ⟦ G ⟧F X)
                → appNatTr-F (escape-nt t) g ≡ appNatTr-F t g
escape-once-correct id x = refl
escape-once-correct (g ∘ f) x =
  trans (escape-compose-correct (escape-once g) (escape-once f) x)
        (trans (cong (eval (escape-once g)) (escape-once-correct f x))
               (escape-once-correct g (eval f x)))
escape-once-correct fst x = refl
escape-once-correct snd x = refl
escape-once-correct (⟨ f , g ⟩ m) x =
  cong₂ _,_ (escape-once-correct f x) (escape-once-correct g x)
escape-once-correct (inl m) x = refl
escape-once-correct (inr m) x = refl
escape-once-correct (case f g) (inj₁ a) = escape-once-correct f a
escape-once-correct (case f g) (inj₂ b) = escape-once-correct g b
escape-once-correct terminal x = refl
escape-once-correct initial ()
escape-once-correct (curry {k = k} f m) x =
  funext (λ b → escape-once-correct f (x , b))
escape-once-correct apply x = refl
escape-once-correct arr x = refl
escape-once-correct (SigOp n) x = refl
escape-once-correct (const _ _) x = refl
escape-once-correct (free-heap h) x = refl
escape-once-correct (In wf m) x = refl
escape-once-correct (out-μ wf) x = refl
escape-once-correct (Cata wf alg) x =
  escape-Cata-cong wf (escape-once alg) alg x
                   (funext (λ y → escape-once-correct alg y))
escape-once-correct (Para wf alg) x =
  escape-Para-cong wf (escape-once alg) alg x
                   (funext (λ y → escape-once-correct alg y))
escape-once-correct (Out wf) x = refl
escape-once-correct (in-ν wf m) x = refl
escape-once-correct (Ana wf coalg) x =
  escape-Ana-cong wf (escape-once coalg) coalg x
                   (funext (λ y → escape-once-correct coalg y))
escape-once-correct (Hylo {F} {G} wfF wfG alg t) x =
  sem-fuseNat-cong F G wfF wfG
    (appNatTr-F (escape-nt t)) (appNatTr-F t)
    (λ fb → eval (escape-once alg) (coerce-functor⁻¹ F _ fb))
    (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
    (λ g → appNatTr-escape t g)
    (λ fb → escape-once-correct alg (coerce-functor⁻¹ F _ fb))
    x
escape-once-correct (Fuse {F} {G} wfF wfG alg t) x =
  sem-fuseNat-cong F G wfF wfG
    (appNatTr-F (escape-nt t)) (appNatTr-F t)
    (λ fb → eval (escape-once alg) (coerce-functor⁻¹ F _ fb))
    (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
    (λ g → appNatTr-escape t g)
    (λ fb → escape-once-correct alg (coerce-functor⁻¹ F _ fb))
    x

appNatTr-escape ntId         g        = refl
appNatTr-escape (ntK ir)     g        = escape-once-correct ir g
appNatTr-escape (ntFst t)    (x , _)  = appNatTr-escape t x
appNatTr-escape (ntSnd t)    (_ , y)  = appNatTr-escape t y
appNatTr-escape (ntCase t u) (inj₁ x) = appNatTr-escape t x
appNatTr-escape (ntCase t u) (inj₂ y) = appNatTr-escape u y
appNatTr-escape (ntInl t)    g        = cong inj₁ (appNatTr-escape t g)
appNatTr-escape (ntInr t)    g        = cong inj₂ (appNatTr-escape t g)
appNatTr-escape (ntPair t u) g        =
  cong₂ _,_ (appNatTr-escape t g) (appNatTr-escape u g)

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

escape-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval (escape-n n f) x ≡ eval f x
escape-n-correct zero f x = refl
escape-n-correct (suc n) f x =
  trans (escape-n-correct n (escape-once f) x)
        (escape-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: escape analysis preserves semantics
------------------------------------------------------------------------

escape-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval (escape f) x ≡ eval f x
escape-correct f x = escape-n-correct 10 f x
