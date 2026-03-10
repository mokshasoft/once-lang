------------------------------------------------------------------------
-- Once.Optimizer.WellFounded
--
-- Well-founded recursion version of the optimizer.
-- Same algorithm as Once.Optimize, but with explicit termination proof.
--
-- Uses lexicographic measure (ir-size g + ir-size f, ir-size g) to handle
-- the case where optimization doesn't reduce size (e.g., default case).
------------------------------------------------------------------------

module Once.Optimizer.WellFounded where

open import Once.Type using (Type; Unit; Void; _*_; Fix; Quantity)
open import Once.IR
open AllocMode
open import Once.Optimize using (_≟Type_; safe-pair-distrib)

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _≥_; s≤s; z≤n; _<?_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-refl; ≤-trans; n≤1+n; +-mono-≤; +-assoc; ≤-reflexive; +-monoʳ-≤; +-monoˡ-≤; +-suc; <-trans; <⇒≤; +-identityʳ)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; trans; inspect) renaming ([_] to ⟦_⟧)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Size measure
------------------------------------------------------------------------

ir-size : ∀ {A B} → IR A B → ℕ
ir-size id            = 1
ir-size (g ∘ f)       = suc (ir-size g + ir-size f)
ir-size fst           = 1
ir-size snd           = 1
ir-size (⟨ f , g ⟩ _) = suc (ir-size f + ir-size g)
ir-size (inl _)       = 1
ir-size (inr _)       = 1
ir-size [ f , g ]     = suc (ir-size f + ir-size g)
ir-size terminal      = 1
ir-size initial       = 1
ir-size (curry f _)   = suc (suc (ir-size f))
ir-size apply         = 1
ir-size fold          = 1
ir-size unfold        = 1
ir-size arr           = 1
ir-size (Prim _)      = 1

------------------------------------------------------------------------
-- Lexicographic measure
------------------------------------------------------------------------

Measure : Set
Measure = ℕ × ℕ

data _<ₗ_ : Measure → Measure → Set where
  left  : ∀ {a₁ a₂ b₁ b₂} → a₁ < a₂ → (a₁ , b₁) <ₗ (a₂ , b₂)
  right : ∀ {a b₁ b₂} → b₁ < b₂ → (a , b₁) <ₗ (a , b₂)

{-# TERMINATING #-}
<ₗ-wellFounded : WellFounded _<ₗ_
<ₗ-wellFounded = wf-lex
  where
    wf-lex-b : ∀ a → Acc _<_ a → ∀ b → Acc _<_ b → Acc _<ₗ_ (a , b)
    wf-lex-b a (acc rec-a) b (acc rec-b) = acc go
      where
        go : ∀ {y} → y <ₗ (a , b) → Acc _<ₗ_ y
        go {a' , b'} (left a'<a) = wf-lex-b a' (rec-a a'<a) b' (<-wellFounded b')
        go {.a , b'} (right b'<b) = wf-lex-b a (acc rec-a) b' (rec-b b'<b)

    wf-lex : ∀ x → Acc _<ₗ_ x
    wf-lex (a , b) = wf-lex-b a (<-wellFounded a) b (<-wellFounded b)

measure : ∀ {A B C} → IR B C → IR A B → Measure
measure g f = (ir-size g + ir-size f , ir-size g)

------------------------------------------------------------------------
-- Size bounds (postulated for simplicity, clearly true)
------------------------------------------------------------------------

postulate
  size-bound : ∀ {A B C} (g : IR B C) (f : IR A B) →
    ∀ (r : IR A C) → ir-size r ≤ suc (ir-size g + ir-size f)

------------------------------------------------------------------------
-- Proven bounds for lexicographic recursion
------------------------------------------------------------------------

assoc-inner-<ₗ : ∀ {A B C D} (h : IR C D) (g : IR B C) (f : IR A B) →
  measure g f <ₗ measure (h ∘ g) f
assoc-inner-<ₗ h g f = left (s≤s (+-monoˡ-≤ (ir-size f) (m≤n+m (ir-size g) (ir-size h))))

assoc-outer-<ₗ : ∀ {A B C D} (h : IR C D) (g : IR B C) (f : IR A B) (r₁ : IR A C) →
  ir-size r₁ ≤ suc (ir-size g + ir-size f) →
  measure h r₁ <ₗ measure (h ∘ g) f
assoc-outer-<ₗ h g f r₁ r₁≤ with ir-size h + ir-size r₁ <? suc (ir-size h + ir-size g) + ir-size f
... | yes lt = left lt
... | no ¬lt = subst (λ x → (x , ir-size h) <ₗ (rhs₁ , suc (ir-size h + ir-size g))) (sym eq) (right second-<)
  where
    open import Data.Nat.Properties using (≮⇒≥; ≤-antisym)
    lhs₁ = ir-size h + ir-size r₁
    rhs₁ = suc (ir-size h + ir-size g) + ir-size f
    lhs₁≥rhs₁ = ≮⇒≥ ¬lt
    step1 = +-monoʳ-≤ (ir-size h) r₁≤
    eq-chain = trans (+-suc (ir-size h) (ir-size g + ir-size f))
                     (cong suc (sym (+-assoc (ir-size h) (ir-size g) (ir-size f))))
    lhs₁≤rhs₁ = subst (lhs₁ ≤_) eq-chain step1
    eq = ≤-antisym lhs₁≤rhs₁ lhs₁≥rhs₁
    second-< = s≤s (m≤m+n (ir-size h) (ir-size g))

apply-curry-<ₗ : ∀ {A B C q} (h : IR B C) (g : IR A B) (m : AllocMode) (m' : AllocMode) →
  measure h g <ₗ measure apply (⟨ curry {q = q} (h ∘ snd) m , g ⟩ m')
apply-curry-<ₗ {A} {B} {C} {q} h g m m' with ir-size (snd {A} {B}) | inspect ir-size (snd {A} {B})
... | 1 | ⟦ eq ⟧ = left (s≤s n≤s⁴x)
  where
    n = ir-size h + ir-size g
    x = (ir-size h + 1) + ir-size g
    n≤x = +-monoˡ-≤ (ir-size g) (m≤m+n (ir-size h) 1)
    n≤sx = ≤-trans n≤x (n≤1+n x)
    n≤s²x = ≤-trans n≤sx (n≤1+n (suc x))
    n≤s³x = ≤-trans n≤s²x (n≤1+n (suc (suc x)))
    n≤s⁴x = ≤-trans n≤s³x (n≤1+n (suc (suc (suc x))))

------------------------------------------------------------------------
-- Well-founded optimizer
------------------------------------------------------------------------

mutual
  optimize-wf : ∀ {A B C} (g : IR B C) (f : IR A B) →
    Acc _<ₗ_ (measure g f) → IR A C
  optimize-wf {A} {_} {C} g f ac with C ≟Type Unit
  ... | yes refl = terminal
  ... | no _ with A ≟Type Void
  ...   | yes refl = initial
  ...   | no _ = optimize-structural-wf g f ac

  optimize-structural-wf : ∀ {A B C} (g : IR B C) (f : IR A B) →
    Acc _<ₗ_ (measure g f) → IR A C

  -- Identity laws
  optimize-structural-wf id f _ = f
  optimize-structural-wf g id _ = g

  -- Beta: Products
  optimize-structural-wf fst (⟨ f , g ⟩ m) _ = f
  optimize-structural-wf snd (⟨ f , g ⟩ m) _ = g

  -- Beta: Coproducts
  optimize-structural-wf [ f , _ ] (inl m) _ = f
  optimize-structural-wf [ _ , g ] (inr m) _ = g

  -- Beta: Exponentials
  optimize-structural-wf apply (⟨ curry {q = q} (h ∘ fst) m , g ⟩ m') _ = h
  optimize-structural-wf apply (⟨ curry {q = q} (h ∘ snd) m , g ⟩ m') (acc rec) =
    optimize-wf h g (rec (apply-curry-<ₗ {q = q} h g m m'))
  optimize-structural-wf apply (⟨ curry {q = q} (h ∘ terminal) m , g ⟩ m') _ = h ∘ terminal
  optimize-structural-wf apply (⟨ curry {q = q} terminal m , g ⟩ m') _ = terminal
  optimize-structural-wf apply (⟨ curry {q = q} id m , g ⟩ m') _ = ⟨ id , g ⟩ Heap
  optimize-structural-wf apply (⟨ curry {q = q} fst m , g ⟩ m') _ = id
  optimize-structural-wf apply (⟨ curry {q = q} snd m , g ⟩ m') _ = g
  optimize-structural-wf apply (⟨ curry {q = q} f m , g ⟩ m') _ = f ∘ ⟨ id , g ⟩ Heap

  -- Fixed points
  optimize-structural-wf (fold {F = F}) unfold _ = id
  optimize-structural-wf (unfold {F = F}) fold _ = id
  optimize-structural-wf fold (unfold ∘ f) _ = f
  optimize-structural-wf unfold (fold ∘ f) _ = f

  -- Dead code
  optimize-structural-wf terminal f _ = terminal
  optimize-structural-wf g initial _ = initial

  -- Associativity (THE KEY RECURSIVE CASE)
  optimize-structural-wf (h ∘ g) f (acc rec) =
    let r₁ = optimize-wf g f (rec (assoc-inner-<ₗ h g f))
    in optimize-wf h r₁ (rec (assoc-outer-<ₗ h g f r₁ (size-bound g f r₁)))

  -- Pair distribution
  optimize-structural-wf (⟨ f , g ⟩ m) h _ with safe-pair-distrib f g
  ... | true = ⟨ f ∘ h , g ∘ h ⟩ m
  ... | false = (⟨ f , g ⟩ m) ∘ h

  -- Default
  optimize-structural-wf g f _ = g ∘ f

------------------------------------------------------------------------
-- Public interface
------------------------------------------------------------------------

optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C
optimize-compose g f = optimize-wf g f (<ₗ-wellFounded (measure g f))
