-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Once.IR
open import Once.CCC.Eval using (⟦_⟧; eval; appNatTr-F)
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
                       → eval (fusion-compose g f) x ≡ eval (g ∘ f) x
fusion-compose-correct g f x = refl

------------------------------------------------------------------------
-- Congruence lemmas for recursion schemes
------------------------------------------------------------------------

open import Data.Integer using (ℤ)
open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Semantics.Value Carrier Carrier using (sem-cata; sem-para; sem-ana; sem-fuseNat; sem-fuseNat-cong; ⟦_⟧F; coerce-functor; coerce-functor⁻¹)

fusion-Cata-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧)
                 → eval alg ≡ eval alg'
                 → eval (Cata wf alg) x ≡ eval (Cata wf alg') x
fusion-Cata-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-cata wf (λ fa → ev (coerce-functor⁻¹ F _ fa)) x) eq

fusion-Para-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T (μ-type F * A)) A) (x : ⟦ μ-type F ⟧)
                 → eval alg ≡ eval alg'
                 → eval (Para wf alg) x ≡ eval (Para wf alg') x
fusion-Para-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-para wf (λ fx → ev (coerce-functor⁻¹ F _ fx)) x) eq

fusion-Ana-cong : ∀ {F A} (wf : _) (coalg coalg' : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧)
                → eval coalg ≡ eval coalg'
                → eval (Ana wf coalg) x ≡ eval (Ana wf coalg') x
fusion-Ana-cong {F} {A} wf coalg coalg' x eq =
  cong (λ ev → sem-ana F (λ a → coerce-functor F A (ev a)) x) eq


------------------------------------------------------------------------
-- Correctness of fusion-once
------------------------------------------------------------------------

fusion-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                    → eval (fusion-once f) x ≡ eval f x
-- D062: `fusion-nt` preserves the natural transform's meaning, pointwise.
appNatTr-fusion : ∀ {G F} (t : NatTr G F) {X : Set} (g : ⟦ G ⟧F X)
                → appNatTr-F (fusion-nt t) g ≡ appNatTr-F t g
fusion-once-correct id x = refl
fusion-once-correct (g ∘ f) x =
  trans (fusion-compose-correct (fusion-once g) (fusion-once f) x)
        (trans (cong (eval (fusion-once g)) (fusion-once-correct f x))
               (fusion-once-correct g (eval f x)))
fusion-once-correct fst x = refl
fusion-once-correct snd x = refl
fusion-once-correct (⟨ f , g ⟩) x =
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
fusion-once-correct (const _ _) x = refl
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
fusion-once-correct (Hylo {F} {G} wfF wfG alg t) x =
  sem-fuseNat-cong F G wfF wfG
    (appNatTr-F (fusion-nt t)) (appNatTr-F t)
    (λ fb → eval (fusion-once alg) (coerce-functor⁻¹ F _ fb))
    (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
    (λ g → appNatTr-fusion t g)
    (λ fb → fusion-once-correct alg (coerce-functor⁻¹ F _ fb))
    x
fusion-once-correct (Fuse {F} {G} wfF wfG alg t) x =
  sem-fuseNat-cong F G wfF wfG
    (appNatTr-F (fusion-nt t)) (appNatTr-F t)
    (λ fb → eval (fusion-once alg) (coerce-functor⁻¹ F _ fb))
    (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
    (λ g → appNatTr-fusion t g)
    (λ fb → fusion-once-correct alg (coerce-functor⁻¹ F _ fb))
    x

appNatTr-fusion ntId         g        = refl
appNatTr-fusion (ntK ir)     g        = fusion-once-correct ir g
appNatTr-fusion (ntFst t)    (x , _)  = appNatTr-fusion t x
appNatTr-fusion (ntSnd t)    (_ , y)  = appNatTr-fusion t y
appNatTr-fusion (ntCase t u) (inj₁ x) = appNatTr-fusion t x
appNatTr-fusion (ntCase t u) (inj₂ y) = appNatTr-fusion u y
appNatTr-fusion (ntInl t)    g        = cong inj₁ (appNatTr-fusion t g)
appNatTr-fusion (ntInr t)    g        = cong inj₂ (appNatTr-fusion t g)
appNatTr-fusion (ntPair t u) g        =
  cong₂ _,_ (appNatTr-fusion t g) (appNatTr-fusion u g)

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

fusion-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval (fusion-n n f) x ≡ eval f x
fusion-n-correct zero f x = refl
fusion-n-correct (suc n) f x =
  trans (fusion-n-correct n (fusion-once f) x)
        (fusion-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: fusion preserves semantics
------------------------------------------------------------------------

fusion-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval (fusion f) x ≡ eval f x
fusion-correct f x = fusion-n-correct 10 f x
