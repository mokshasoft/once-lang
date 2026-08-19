-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Optimize.Correct
--
-- Correctness proofs for the Once optimizer.
-- Each optimization rule preserves semantics.
--
-- OCP-0003 postulates were eliminated: the view functions in
-- Once.Optimize are now concrete (see the generic-codomain trick
-- documented there), enabling direct structural proofs here.
------------------------------------------------------------------------

module Once.Optimize.Correct where

open import Once.Type
open import Once.IR
open import Once.CCC.Eval using (⟦_⟧; eval; appNatTr-F)
open import Once.Optimize
open import Once.Category.Laws
open import Once.Postulates using (extensionality)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

-- Alias for function extensionality (imported from Once.Postulates)
funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
funext = extensionality

------------------------------------------------------------------------
-- Correctness of view-driven helpers
------------------------------------------------------------------------

-- | optimize-fst preserves semantics: eval (optimize-fst f) x ≡ eval (fst ∘ f) x
optimize-fst-correct : ∀ {A B C} (f : IR A (B * C)) (x : ⟦ A ⟧)
                     → eval (optimize-fst f) x ≡ eval (fst ∘ f) x
optimize-fst-correct f x with pairView f
... | is-pair g h m = refl
... | is-other-pair f = refl

-- | optimize-snd preserves semantics
optimize-snd-correct : ∀ {A B C} (f : IR A (B * C)) (x : ⟦ A ⟧)
                     → eval (optimize-snd f) x ≡ eval (snd ∘ f) x
optimize-snd-correct f x with pairView f
... | is-pair g h m = refl
... | is-other-pair f = refl

-- | optimize-post-case preserves semantics:
--   eval (optimize-post-case h k f) x ≡ eval (case h k ∘ f) x
optimize-post-case-correct : ∀ {A B C D} (h : IR A C) (k : IR B C) (f : IR D (A + B)) (x : ⟦ D ⟧)
                           → eval (optimize-post-case h k f) x ≡ eval (case h k ∘ f) x
optimize-post-case-correct h k f x with coprodView f
... | is-inl m = refl
... | is-inr m = refl
... | is-other-coprod f = refl

-- | optimize-compose-second preserves semantics
optimize-compose-second-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                                → eval (optimize-compose-second g f) x ≡ eval (g ∘ f) x
optimize-compose-second-correct g f x with composeSecondView f
... | cs-id = refl
optimize-compose-second-correct g .initial () | cs-initial
optimize-compose-second-correct g f x | cs-other f' = refl

------------------------------------------------------------------------
-- Correctness of optimize-compose
------------------------------------------------------------------------

optimize-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                         → eval (optimize-compose g f) x ≡ eval (g ∘ f) x
optimize-compose-correct g f x with has-effect? f
... | true = refl                                  -- kept as `g ∘ f`
optimize-compose-correct g f x | false with composeFirstView g
... | cf-id = refl
... | cf-terminal = refl
... | cf-fst = optimize-fst-correct f x
... | cf-snd = optimize-snd-correct f x
... | cf-case h k = optimize-post-case-correct h k f x
... | cf-other g = optimize-compose-second-correct g f x

------------------------------------------------------------------------
-- Correctness of optimize-pair
------------------------------------------------------------------------

optimize-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
                      → eval (optimize-pair f g) x ≡ eval (⟨ f , g ⟩ Heap) x
optimize-pair-correct f g x with fstSndView f | fstSndView g
-- Eta case: ⟨ fst , snd ⟩ = id. Here C = A * B so x is a pair.
optimize-pair-correct .fst .snd (a , b) | fsv-fst | fsv-snd = refl
-- Non-eta cases: optimize-pair returns ⟨ f , g ⟩ Stack; Stack vs Heap is semantically transparent.
optimize-pair-correct .fst .fst x | fsv-fst | fsv-fst = refl
optimize-pair-correct .fst g' x | fsv-fst | fsv-other .g' = refl
optimize-pair-correct .snd .fst x | fsv-snd | fsv-fst = refl
optimize-pair-correct .snd .snd x | fsv-snd | fsv-snd = refl
optimize-pair-correct .snd g' x | fsv-snd | fsv-other .g' = refl
optimize-pair-correct f' .fst x | fsv-other .f' | fsv-fst = refl
optimize-pair-correct f' .snd x | fsv-other .f' | fsv-snd = refl
optimize-pair-correct f' g' x | fsv-other .f' | fsv-other .g' = refl

------------------------------------------------------------------------
-- Correctness of optimize-case
------------------------------------------------------------------------

optimize-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧)
                      → eval (optimize-case f g) x ≡ eval (case f g) x
optimize-case-correct f g x with inlInrView f | inlInrView g
-- Eta case: [ inl , inr ] = id. Here C = A + B so eval id = identity and case inl/inr reduces.
optimize-case-correct .(inl m₁) .(inr m₂) (inj₁ a) | iiv-inl m₁ | iiv-inr m₂ = refl
optimize-case-correct .(inl m₁) .(inr m₂) (inj₂ b) | iiv-inl m₁ | iiv-inr m₂ = refl
-- Non-eta cases: optimize-case returns (case f g) so both sides are equal.
optimize-case-correct .(inl m₁) .(inl m₂) x | iiv-inl m₁ | iiv-inl m₂ = refl
optimize-case-correct .(inl m₁) g' x | iiv-inl m₁ | iiv-other .g' = refl
optimize-case-correct .(inr m₁) .(inl m₂) x | iiv-inr m₁ | iiv-inl m₂ = refl
optimize-case-correct .(inr m₁) .(inr m₂) x | iiv-inr m₁ | iiv-inr m₂ = refl
optimize-case-correct .(inr m₁) g' x | iiv-inr m₁ | iiv-other .g' = refl
optimize-case-correct f' .(inl m₂) x | iiv-other .f' | iiv-inl m₂ = refl
optimize-case-correct f' .(inr m₂) x | iiv-other .f' | iiv-inr m₂ = refl
optimize-case-correct f' g' x | iiv-other .f' | iiv-other .g' = refl

------------------------------------------------------------------------
-- Correctness of optimize-once
------------------------------------------------------------------------

-- Helper: Unit-target uniqueness (any f : _ → Unit is ≡ tt semantically)
eval-unit-unique : ∀ {A} (f : IR A Unit) (x : ⟦ A ⟧)
                 → eval f x ≡ tt
eval-unit-unique f x with eval f x
... | tt = refl

------------------------------------------------------------------------
-- Congruence lemmas: if eval alg ≡ eval alg' (as functions),
-- then recursion-scheme expressions built from them evaluate equally.
------------------------------------------------------------------------

open import Once.IR using (IR)
open import Data.Integer using (ℤ)
open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Semantics.Value Carrier Carrier using (sem-cata; sem-para; sem-ana; sem-fuseNat; sem-fuseNat-cong; ⟦_⟧F; coerce-functor; coerce-functor⁻¹)

-- Cata: if two algebras evaluate equally (pointwise), so do their Cata applications.
-- Proved by cong over the lambda inside the sem-cata call.
eval-Cata-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T A) A) (x : ⟦ μ-type F ⟧)
               → eval alg ≡ eval alg'
               → eval (Cata wf alg) x ≡ eval (Cata wf alg') x
eval-Cata-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-cata wf (λ fa → ev (coerce-functor⁻¹ F _ fa)) x) eq

eval-Para-cong : ∀ {F A} (wf : _) (alg alg' : IR (⟦ F ⟧T (μ-type F * A)) A) (x : ⟦ μ-type F ⟧)
               → eval alg ≡ eval alg'
               → eval (Para wf alg) x ≡ eval (Para wf alg') x
eval-Para-cong {F} wf alg alg' x eq =
  cong (λ ev → sem-para wf (λ fx → ev (coerce-functor⁻¹ F _ fx)) x) eq

eval-Ana-cong : ∀ {F A} (wf : _) (coalg coalg' : IR A (⟦ F ⟧T A)) (x : ⟦ A ⟧)
              → eval coalg ≡ eval coalg'
              → eval (Ana wf coalg) x ≡ eval (Ana wf coalg') x
eval-Ana-cong {F} {A} wf coalg coalg' x eq =
  cong (λ ev → sem-ana F (λ a → coerce-functor F A (ev a)) x) eq

-- D062: Hylo/Fuse now carry a NATURAL transform (`NatTr`); both denote the
-- total `sem-fuseNat (appNatTr-F t) alg`. Their optimizer-correctness uses
-- `sem-fuseNat-cong` directly (below), so the old IR-coalgebra cong lemmas
-- (`eval-{Hylo,Fuse}-cong-*`, built on the deleted `sem-hylo`/`sem-fuse`) are
-- gone. `appNatTr-optimize` lifts `optimize-nt` through the transform.

mutual
  -- | `optimize-nt` preserves the natural transform's meaning, pointwise.
  appNatTr-optimize : ∀ {G F} (t : NatTr G F) {X : Set} (g : ⟦ G ⟧F X)
                    → appNatTr-F (optimize-nt t) g ≡ appNatTr-F t g
  appNatTr-optimize ntId         g        = refl
  appNatTr-optimize (ntK ir)     g        = optimize-once-correct ir g
  appNatTr-optimize (ntFst t)    (x , _)  = appNatTr-optimize t x
  appNatTr-optimize (ntSnd t)    (_ , y)  = appNatTr-optimize t y
  appNatTr-optimize (ntCase t u) (inj₁ x) = appNatTr-optimize t x
  appNatTr-optimize (ntCase t u) (inj₂ y) = appNatTr-optimize u y
  appNatTr-optimize (ntInl t)    g        = cong inj₁ (appNatTr-optimize t g)
  appNatTr-optimize (ntInr t)    g        = cong inj₂ (appNatTr-optimize t g)
  appNatTr-optimize (ntPair t u) g        =
    cong₂ _,_ (appNatTr-optimize t g) (appNatTr-optimize u g)

  optimize-once-structural-correct :
    ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
    → eval (optimize-once-structural f) x ≡ eval f x
  optimize-once-structural-correct id x = refl
  optimize-once-structural-correct (g ∘ f) x =
    trans (optimize-compose-correct (optimize-once g) (optimize-once f) x)
          (trans (cong (eval (optimize-once g)) (optimize-once-correct f x))
                 (optimize-once-correct g (eval f x)))
  optimize-once-structural-correct fst x = refl
  optimize-once-structural-correct snd x = refl
  optimize-once-structural-correct (⟨ f , g ⟩ m) x =
    trans (optimize-pair-correct (optimize-once f) (optimize-once g) x)
          (cong₂ _,_ (optimize-once-correct f x) (optimize-once-correct g x))
  -- inl: check Void source
  optimize-once-structural-correct (inl {A} {B} m) x with A ≟Type Void
  ... | yes refl = ⊥-elim x
  ... | no _ = refl
  -- inr: check Void source
  optimize-once-structural-correct (inr {A} {B} m) x with B ≟Type Void
  ... | yes refl = ⊥-elim x
  ... | no _ = refl
  optimize-once-structural-correct (case f g) (inj₁ a) =
    trans (optimize-case-correct (optimize-once f) (optimize-once g) (inj₁ a))
          (optimize-once-correct f a)
  optimize-once-structural-correct (case f g) (inj₂ b) =
    trans (optimize-case-correct (optimize-once f) (optimize-once g) (inj₂ b))
          (optimize-once-correct g b)
  optimize-once-structural-correct terminal x = refl
  optimize-once-structural-correct initial ()
  optimize-once-structural-correct (curry f m) x =
    funext (λ b → optimize-once-correct f (x , b))
  optimize-once-structural-correct apply x = refl
  optimize-once-structural-correct arr x = refl
  optimize-once-structural-correct (SigOp {A} n) x with A ≟Type Void
  ... | yes refl = ⊥-elim x
  ... | no _ = refl
  -- const is opaque (no optimization), so structural identity holds.
  optimize-once-structural-correct (const _ _) x = refl
  optimize-once-structural-correct (free-heap h) x = refl
  optimize-once-structural-correct (In wf m) x = refl
  optimize-once-structural-correct (out-μ wf) x = refl
  -- For Cata/Para/Ana/Hylo/Fuse, optimize-once descends into algebras/coalgebras.
  -- Evaluation uses `eval alg` in a lambda. Funext on the pointwise IH gives
  -- `eval (optimize-once alg) ≡ eval alg`; we substitute into the Cata form.
  optimize-once-structural-correct (Cata {F} wf alg) x =
    eval-Cata-cong wf (optimize-once alg) alg x
                   (funext (λ y → optimize-once-correct alg y))
  optimize-once-structural-correct (Para {F} wf alg) x =
    eval-Para-cong wf (optimize-once alg) alg x
                   (funext (λ y → optimize-once-correct alg y))
  optimize-once-structural-correct (Out wf) x = refl
  optimize-once-structural-correct (in-ν wf m) x = refl
  optimize-once-structural-correct (Ana {F} wf coalg) x =
    eval-Ana-cong wf (optimize-once coalg) coalg x
                   (funext (λ y → optimize-once-correct coalg y))
  optimize-once-structural-correct (Hylo {F} {G} wfF wfG alg t) x =
    sem-fuseNat-cong F G wfF wfG
      (appNatTr-F (optimize-nt t)) (appNatTr-F t)
      (λ fb → eval (optimize-once alg) (coerce-functor⁻¹ F _ fb))
      (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
      (λ g → appNatTr-optimize t g)
      (λ fb → optimize-once-correct alg (coerce-functor⁻¹ F _ fb))
      x
  optimize-once-structural-correct (Fuse {F} {G} wfF wfG alg t) x =
    sem-fuseNat-cong F G wfF wfG
      (appNatTr-F (optimize-nt t)) (appNatTr-F t)
      (λ fb → eval (optimize-once alg) (coerce-functor⁻¹ F _ fb))
      (λ fb → eval alg (coerce-functor⁻¹ F _ fb))
      (λ g → appNatTr-optimize t g)
      (λ fb → optimize-once-correct alg (coerce-functor⁻¹ F _ fb))
      x

  optimize-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                        → eval (optimize-once f) x ≡ eval f x
  optimize-once-correct {A} {B} f x with B ≟Type Unit
  ... | yes refl with has-effect? f
  ...   | false = sym (eval-unit-unique f x)        -- collapsed to terminal (value-correct; no effect to lose)
  ...   | true  = optimize-once-structural-correct f x   -- effectful: kept structurally
  optimize-once-correct {A} {B} f x | no _ with A ≟Type Void
  ...   | yes refl = ⊥-elim x
  ...   | no _ = optimize-once-structural-correct f x

------------------------------------------------------------------------
-- Correctness of bounded optimization
------------------------------------------------------------------------

optimize-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                   → eval (optimize-n n f) x ≡ eval f x
optimize-n-correct zero f x = refl
optimize-n-correct (suc n) f x =
  trans (optimize-n-correct n (optimize-once f) x)
        (optimize-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: optimize preserves semantics
------------------------------------------------------------------------

optimize-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                 → eval (optimize f) x ≡ eval f x
optimize-correct f x = optimize-n-correct 10 f x
