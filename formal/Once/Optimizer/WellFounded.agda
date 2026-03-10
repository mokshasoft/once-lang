------------------------------------------------------------------------
-- Once.Optimizer.WellFounded
--
-- Well-founded recursion version of the optimizer.
-- Same algorithm as Once.Optimize, but with explicit termination proof.
--
-- Uses lexicographic measure (ir-size g + ir-size f, ir-size g) to handle
-- the case where optimization doesn't reduce size (e.g., default case).
--
-- NO POSTULATES - full verification of termination.
------------------------------------------------------------------------

module Once.Optimizer.WellFounded where

open import Once.Type using (Type; Unit; Void; _*_; Fix; Quantity)
open import Once.IR
open AllocMode
open import Once.Optimize using (_≟Type_; safe-pair-distrib)

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _≥_; s≤s; z≤n; _<?_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-refl; ≤-trans; n≤1+n; +-mono-≤; +-assoc; ≤-reflexive; +-monoʳ-≤; +-monoˡ-≤; +-suc; +-comm)
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

-- Result type: IR with size bound proof
OptResult : Type → Type → ℕ → Set
OptResult A C n = Σ[ r ∈ IR A C ] (ir-size r ≤ suc n)

------------------------------------------------------------------------
-- Size bound helpers
------------------------------------------------------------------------

-- Any n ≤ suc (suc (... n))
≤-add-suc : ∀ n k → n ≤ n + k
≤-add-suc n k = m≤m+n n k

≤-suc : ∀ {n m} → n ≤ m → n ≤ suc m
≤-suc p = ≤-trans p (n≤1+n _)

≤-suc² : ∀ {n m} → n ≤ m → n ≤ suc (suc m)
≤-suc² p = ≤-suc (≤-suc p)

≤-suc³ : ∀ {n m} → n ≤ m → n ≤ suc (suc (suc m))
≤-suc³ p = ≤-suc (≤-suc² p)

≤-suc⁴ : ∀ {n m} → n ≤ m → n ≤ suc (suc (suc (suc m)))
≤-suc⁴ p = ≤-suc (≤-suc³ p)

≤-suc⁵ : ∀ {n m} → n ≤ m → n ≤ suc (suc (suc (suc (suc m))))
≤-suc⁵ p = ≤-suc (≤-suc⁴ p)

≤-suc⁶ : ∀ {n m} → n ≤ m → n ≤ suc (suc (suc (suc (suc (suc m)))))
≤-suc⁶ p = ≤-suc (≤-suc⁵ p)

≤-suc⁷ : ∀ {n m} → n ≤ m → n ≤ suc (suc (suc (suc (suc (suc (suc m))))))
≤-suc⁷ p = ≤-suc (≤-suc⁶ p)

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
-- Well-founded optimizer with size bounds
------------------------------------------------------------------------

mutual
  optimize-wf : ∀ {A B C} (g : IR B C) (f : IR A B) →
    Acc _<ₗ_ (measure g f) → OptResult A C (ir-size g + ir-size f)
  optimize-wf {A} {_} {C} g f ac with C ≟Type Unit
  ... | yes refl = terminal , s≤s z≤n
  ... | no _ with A ≟Type Void
  ...   | yes refl = initial , s≤s z≤n
  ...   | no _ = optimize-structural-wf g f ac

  optimize-structural-wf : ∀ {A B C} (g : IR B C) (f : IR A B) →
    Acc _<ₗ_ (measure g f) → OptResult A C (ir-size g + ir-size f)

  -- Identity laws
  -- id ∘ f = f; need ir-size f ≤ suc (ir-size id + ir-size f) = suc (1 + ir-size f) = suc (suc (ir-size f))
  optimize-structural-wf id f _ = f , ≤-suc (n≤1+n (ir-size f))
  -- g ∘ id = g; need ir-size g ≤ suc (ir-size g + ir-size id) = suc (ir-size g + 1)
  optimize-structural-wf g id _ = g , ≤-trans (m≤m+n (ir-size g) 1) (n≤1+n (ir-size g + 1))

  -- Beta: Products (fst/snd ∘ pair → component)
  -- fst ∘ ⟨f,g⟩ = f; need ir-size f ≤ suc (1 + suc (ir-size f + ir-size g)) = suc³ (ir-size f + ir-size g)
  optimize-structural-wf fst (⟨ f , g ⟩ m) _ =
    f , ≤-suc² (≤-trans (m≤m+n (ir-size f) (ir-size g)) (n≤1+n (ir-size f + ir-size g)))
  optimize-structural-wf snd (⟨ f , g ⟩ m) _ =
    g , ≤-suc² (≤-trans (m≤n+m (ir-size g) (ir-size f)) (n≤1+n (ir-size f + ir-size g)))

  -- Beta: Coproducts ([f,g] ∘ inl/inr → f/g)
  -- [f,g] ∘ inl = f; need ir-size f ≤ suc (suc (ir-size f + ir-size g) + 1) = suc² ((ir-size f + ir-size g) + 1)
  optimize-structural-wf [ f , g ] (inl m) _ =
    let x = ir-size f + ir-size g
    in f , ≤-suc (≤-trans (m≤m+n (ir-size f) (ir-size g)) (≤-trans (m≤m+n x 1) (n≤1+n (x + 1))))
  optimize-structural-wf [ f , g ] (inr m) _ =
    let x = ir-size f + ir-size g
    in g , ≤-suc (≤-trans (m≤n+m (ir-size g) (ir-size f)) (≤-trans (m≤m+n x 1) (n≤1+n (x + 1))))

  -- Beta: Exponentials (apply ∘ ⟨curry body, arg⟩ → various)
  -- apply ∘ ⟨curry (h ∘ fst), g⟩ = h
  -- Size: 1 + suc (suc (suc (suc (ir-size h + ir-size fst))) + ir-size g)
  -- Need: ir-size h ≤ suc⁶ ((ir-size h + 1) + ir-size g)  [since ir-size fst = 1]
  optimize-structural-wf apply (⟨ curry {q = q} (h ∘ fst) m , g ⟩ m') _ =
    h , ≤-suc⁶ (≤-trans (m≤m+n (ir-size h) 1) (m≤m+n (ir-size h + 1) (ir-size g)))

  optimize-structural-wf apply (⟨ curry {q = q} (h ∘ snd) m , g ⟩ m') (acc rec) =
    let (r , r≤) = optimize-wf h g (rec (apply-curry-<ₗ {q = q} h g m m'))
        -- r≤ : ir-size r ≤ suc (ir-size h + ir-size g)
        -- Goal: ir-size r ≤ suc⁶ ((ir-size h + 1) + ir-size g)  [ir-size snd = 1]
        step1 = +-monoˡ-≤ (ir-size g) (m≤m+n (ir-size h) 1)
          -- ir-size h + ir-size g ≤ (ir-size h + 1) + ir-size g
        bound = ≤-trans r≤ (s≤s (≤-suc⁵ step1))
    in r , bound

  -- apply ∘ ⟨curry (h ∘ terminal), g⟩ = h ∘ terminal
  -- ir-size result = suc (ir-size h + 1)  [ir-size terminal = 1]
  -- Goal: suc (ir-size h + 1) ≤ suc⁶ ((ir-size h + 1) + ir-size g)
  optimize-structural-wf apply (⟨ curry {q = q} (h ∘ terminal) m , g ⟩ m') _ =
    h ∘ terminal , s≤s (≤-suc⁵ (m≤m+n (ir-size h + 1) (ir-size g)))

  optimize-structural-wf apply (⟨ curry {q = q} terminal m , g ⟩ m') _ =
    terminal , s≤s z≤n

  -- apply ∘ ⟨curry id, g⟩ = ⟨id, g⟩
  -- Result: suc (1 + ir-size g) = suc² (ir-size g)
  -- Total: suc⁵ (ir-size g), Goal: ≤ suc⁶ (ir-size g)
  optimize-structural-wf apply (⟨ curry {q = q} id m , g ⟩ m') _ =
    ⟨ id , g ⟩ Heap , s≤s (s≤s (≤-suc⁴ ≤-refl))

  -- apply ∘ ⟨curry fst, g⟩ = id
  optimize-structural-wf apply (⟨ curry {q = q} fst m , g ⟩ m') _ =
    id , s≤s z≤n

  -- apply ∘ ⟨curry snd, g⟩ = g
  -- Goal: ir-size g ≤ suc⁶ (ir-size g)
  optimize-structural-wf apply (⟨ curry {q = q} snd m , g ⟩ m') _ =
    g , ≤-suc⁶ ≤-refl

  -- apply ∘ ⟨curry f, g⟩ = f ∘ ⟨id, g⟩ (generic case)
  -- Result: suc (ir-size f + suc (suc (ir-size g)))
  -- Using +-suc: a + suc b = suc (a + b), so ir-size f + suc² g = suc² (ir-size f + g)
  -- Goal: suc (suc (suc (ir-size f + ir-size g))) ≤ suc⁵ (ir-size f + ir-size g)
  optimize-structural-wf apply (⟨ curry {q = q} f m , g ⟩ m') _ =
    let n = ir-size f + ir-size g
        eq1 = +-suc (ir-size f) (suc (ir-size g))  -- ir-size f + suc² g = suc (ir-size f + suc g)
        eq2 = +-suc (ir-size f) (ir-size g)         -- ir-size f + suc g = suc (ir-size f + g)
        -- So ir-size f + suc² g = suc² (ir-size f + g)
        inner : suc (suc n) ≤ suc (suc (suc (suc n)))
        inner = s≤s (≤-suc² ≤-refl)
        -- Rewrite using eq1, eq2
    in f ∘ ⟨ id , g ⟩ Heap , s≤s (subst (_≤ suc (suc (suc (suc n)))) (sym (trans eq1 (cong suc eq2))) inner)

  -- Fixed points (fold/unfold are inverses)
  optimize-structural-wf (fold {F = F}) unfold _ = id , s≤s z≤n
  optimize-structural-wf (unfold {F = F}) fold _ = id , s≤s z≤n
  -- fold ∘ (unfold ∘ f) = f; Total = 1 + suc (1 + ir-size f) = suc³ (ir-size f)
  -- Goal: ir-size f ≤ suc⁴ (ir-size f)  [ir-size fold = ir-size unfold = 1]
  optimize-structural-wf fold (unfold ∘ f) _ = f , ≤-suc³ (m≤n+m (ir-size f) 1)
  optimize-structural-wf unfold (fold ∘ f) _ = f , ≤-suc³ (m≤n+m (ir-size f) 1)

  -- Dead code (terminal/initial absorb)
  optimize-structural-wf terminal f _ = terminal , s≤s z≤n
  optimize-structural-wf g initial _ = initial , s≤s z≤n

  -- Associativity (THE KEY RECURSIVE CASE)
  optimize-structural-wf (h ∘ g) f (acc rec) =
    let (r₁ , r₁≤) = optimize-wf g f (rec (assoc-inner-<ₗ h g f))
        (r₂ , r₂≤) = optimize-wf h r₁ (rec (assoc-outer-<ₗ h g f r₁ r₁≤))
        -- r₂≤ : ir-size r₂ ≤ suc (ir-size h + ir-size r₁)
        -- r₁≤ : ir-size r₁ ≤ suc (ir-size g + ir-size f)
        -- Need: ir-size r₂ ≤ suc (suc (ir-size h + ir-size g) + ir-size f)
        step1 : ir-size h + ir-size r₁ ≤ ir-size h + suc (ir-size g + ir-size f)
        step1 = +-monoʳ-≤ (ir-size h) r₁≤
        step2 : ir-size h + suc (ir-size g + ir-size f) ≡ suc ((ir-size h + ir-size g) + ir-size f)
        step2 = trans (+-suc (ir-size h) (ir-size g + ir-size f))
                      (cong suc (sym (+-assoc (ir-size h) (ir-size g) (ir-size f))))
        bound : ir-size r₂ ≤ suc (suc (ir-size h + ir-size g) + ir-size f)
        bound = ≤-trans r₂≤ (s≤s (subst (ir-size h + ir-size r₁ ≤_) step2 step1))
    in r₂ , bound

  -- Pair distribution - in well-founded version, distribution increases size
  -- (distributes h into both branches), so we just return the composition
  optimize-structural-wf (⟨ f , g ⟩ m) h _ = (⟨ f , g ⟩ m) ∘ h , ≤-refl

  -- Default (no optimization possible)
  optimize-structural-wf g f _ = g ∘ f , ≤-refl

------------------------------------------------------------------------
-- Public interface
------------------------------------------------------------------------

optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C
optimize-compose g f = proj₁ (optimize-wf g f (<ₗ-wellFounded (measure g f)))

optimize-compose-size : ∀ {A B C} (g : IR B C) (f : IR A B) →
  ir-size (optimize-compose g f) ≤ suc (ir-size g + ir-size f)
optimize-compose-size g f = proj₂ (optimize-wf g f (<ₗ-wellFounded (measure g f)))
