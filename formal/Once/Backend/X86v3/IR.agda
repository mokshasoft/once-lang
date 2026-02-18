------------------------------------------------------------------------
-- Once.Backend.X86v3.IR
--
-- IR language definition for SlotMachine POC.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (m<m+n; m<n+m; +-comm; n<1+n; <-trans; m+n≤o⇒m≤o; m+n≤o⇒n≤o; +-monoˡ-<; +-monoʳ-<)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Once.Backend.X86v3.Types public

------------------------------------------------------------------------
-- IR Language
------------------------------------------------------------------------

data IR : Type → Type → Set where
  -- Category structure
  id : ∀ {A} → IR A A
  _∘_ : ∀ {A B C} → IR B C → IR A B → IR A C

  -- Product (A * B)
  ⟨_,_⟩ : ∀ {A B C} → IR A B → IR A C → IR A (B * C)
  fst-ir : ∀ {A B} → IR (A * B) A
  snd-ir : ∀ {A B} → IR (A * B) B

  -- Coproduct (A ⊕ B)
  inl-ir : ∀ {A B} → IR A (A ⊕ B)
  inr-ir : ∀ {A B} → IR B (A ⊕ B)
  case-ir : ∀ {A B C} → IR A C → IR B C → IR (A ⊕ B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → IR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → IR Void A

  -- Exponential (A ⇒ B)
  curry : ∀ {A B C} → IR (A * B) C → IR A (B ⇒ C)
  apply : ∀ {A B} → IR ((A ⇒ B) * A) B

  -- Recursive types (Fix F)
  fold-ir : ∀ {F} → IR F (Fix F)
  unfold-ir : ∀ {F} → IR (Fix F) F

infixr 9 _∘_
infixr 4 ⟨_,_⟩

------------------------------------------------------------------------
-- Semantic Evaluation
------------------------------------------------------------------------

eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
eval id x = x
eval (g ∘ f) x = eval g (eval f x)
eval ⟨ f , g ⟩ x = pair (eval f x) (eval g x)
eval fst-ir x = fst x
eval snd-ir x = snd x
eval inl-ir x = inl x
eval inr-ir x = inr x
eval (case-ir f g) x = case (eval f) (eval g) x
eval terminal x = tt
eval initial ()
eval (curry f) x = λ y → eval f (pair x y)
eval apply (closure , arg) = closure arg
eval fold-ir x = fold x
eval unfold-ir x = unfold x

------------------------------------------------------------------------
-- Evaluation Laws (PROVEN)
------------------------------------------------------------------------

eval-id : ∀ {A} (x : ⟦ A ⟧) → eval id x ≡ x
eval-id x = refl

eval-fst : ∀ {A B} (x : ⟦ A * B ⟧) → eval fst-ir x ≡ fst x
eval-fst x = refl

eval-snd : ∀ {A B} (x : ⟦ A * B ⟧) → eval snd-ir x ≡ snd x
eval-snd x = refl

eval-compose : ∀ {A B C} (f : IR A B) (g : IR B C) (x : ⟦ A ⟧) →
  eval (g ∘ f) x ≡ eval g (eval f x)
eval-compose f g x = refl

eval-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (x : ⟦ A ⟧) →
  eval ⟨ f , g ⟩ x ≡ pair (eval f x) (eval g x)
eval-pair f g x = refl

eval-terminal : ∀ {A} (x : ⟦ A ⟧) → eval terminal x ≡ tt
eval-terminal x = refl

------------------------------------------------------------------------
-- Size Measure for Termination
------------------------------------------------------------------------

ir-size : ∀ {A B} → IR A B → ℕ
ir-size id = 1
ir-size (g ∘ f) = 1 + ir-size g + ir-size f
ir-size ⟨ f , g ⟩ = 1 + ir-size f + ir-size g
ir-size fst-ir = 1
ir-size snd-ir = 1
ir-size inl-ir = 1
ir-size inr-ir = 1
ir-size (case-ir f g) = 1 + ir-size f + ir-size g
ir-size terminal = 1
ir-size initial = 1
ir-size (curry f) = 2 + ir-size f  -- Extra slot for apply's pair allocation
ir-size apply = 1
ir-size fold-ir = 1
ir-size unfold-ir = 1

------------------------------------------------------------------------
-- Size Lemmas (PROVEN)
------------------------------------------------------------------------

-- Helper: 0 < ir-size for all IR
ir-size-pos : ∀ {A B} (ir : IR A B) → 0 < ir-size ir
ir-size-pos id = s≤s z≤n
ir-size-pos (g ∘ f) = s≤s z≤n
ir-size-pos ⟨ f , g ⟩ = s≤s z≤n
ir-size-pos fst-ir = s≤s z≤n
ir-size-pos snd-ir = s≤s z≤n
ir-size-pos inl-ir = s≤s z≤n
ir-size-pos inr-ir = s≤s z≤n
ir-size-pos (case-ir f g) = s≤s z≤n
ir-size-pos terminal = s≤s z≤n
ir-size-pos initial = s≤s z≤n
ir-size-pos (curry f) = s≤s z≤n
ir-size-pos apply = s≤s z≤n
ir-size-pos fold-ir = s≤s z≤n
ir-size-pos unfold-ir = s≤s z≤n

-- Helper: n ≤ m + n (flip of m≤m+n)
n≤m+n : ∀ m n → n ≤ m + n
n≤m+n m n = subst (n ≤_) (+-comm n m) (m≤m+n n m)
  where open import Data.Nat.Properties using (m≤m+n; +-comm)

-- For compose: f is smaller than g ∘ f
-- ir-size (g ∘ f) = suc (ir-size g + ir-size f)
-- Need: ir-size f < suc (ir-size g + ir-size f)
-- i.e.: ir-size f ≤ ir-size g + ir-size f
∘-f-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-size f < ir-size (g ∘ f)
∘-f-smaller f g = s≤s (n≤m+n (ir-size g) (ir-size f))

-- For compose: g is smaller than g ∘ f
-- Need: ir-size g ≤ ir-size g + ir-size f
∘-g-smaller : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-size g < ir-size (g ∘ f)
∘-g-smaller f g = s≤s (m≤m+n (ir-size g) (ir-size f))
  where open import Data.Nat.Properties using (m≤m+n)

-- For pair: f is smaller than ⟨ f , g ⟩
-- ir-size ⟨ f , g ⟩ = suc (ir-size f + ir-size g)
-- Need: ir-size f ≤ ir-size f + ir-size g
⟨,⟩-f-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) →
  ir-size f < ir-size ⟨ f , g ⟩
⟨,⟩-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))
  where open import Data.Nat.Properties using (m≤m+n)

-- For pair: g is smaller than ⟨ f , g ⟩
-- Need: ir-size g ≤ ir-size f + ir-size g
⟨,⟩-g-smaller : ∀ {A B C} (f : IR A B) (g : IR A C) →
  ir-size g < ir-size ⟨ f , g ⟩
⟨,⟩-g-smaller f g = s≤s (n≤m+n (ir-size f) (ir-size g))

-- For curry: f is smaller than curry f
-- ir-size (curry f) = 2 + ir-size f, so we need ir-size f < 2 + ir-size f
curry-smaller : ∀ {A B C} (f : IR (A * B) C) →
  ir-size f < ir-size (curry f)
curry-smaller f = <-trans (n<1+n (ir-size f)) (n<1+n (suc (ir-size f)))
  where open import Data.Nat.Properties using (<-trans)

-- For case: f is smaller than case-ir f g
-- ir-size (case-ir f g) = suc (ir-size f + ir-size g)
case-f-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size f < ir-size (case-ir f g)
case-f-smaller f g = s≤s (m≤m+n (ir-size f) (ir-size g))
  where open import Data.Nat.Properties using (m≤m+n)

-- For case: g is smaller than case-ir f g
case-g-smaller : ∀ {A B C} (f : IR A C) (g : IR B C) →
  ir-size g < ir-size (case-ir f g)
case-g-smaller f g = s≤s (n≤m+n (ir-size f) (ir-size g))

------------------------------------------------------------------------
-- Stack Requirement
--
-- Computes the maximum stack slots needed to execute an IR in the
-- current frame. This is used to ensure frame capacity is sufficient.
--
-- Key insight: Each IR case allocates a known number of slots:
--   - id, fst, snd, terminal: 0 (no allocation)
--   - compose: f's slots + g's slots (sequential execution)
--   - pair: f's slots + g's slots + 2 (for the pair structure)
--   - curry: 2 (for the closure structure; body runs in new frame)
--   - apply: 2 (for forming env-arg pair) + body's requirement
--
-- NOTE on apply: The body's requirement is NOT statically known at the
-- apply IR itself - it depends on which closure is being applied.
-- Two approaches:
--   1. Track max body requirement in the program (global bound)
--   2. Track body requirement in closure validity
--
-- For this definition, we use 0 for apply's "body contribution" since
-- the body runs in the same frame but its requirement must be accounted
-- for separately (via program-level capacity bounds).
------------------------------------------------------------------------

-- Slot sizes for compound values (must match Dispatcher definitions)
pair-slots : ℕ
pair-slots = 2

closure-slots : ℕ
closure-slots = 2

-- Sum type slot size: tag (1) + max payload
-- For now, use fixed size since type-slots is computed at compile time
sum-slots : ℕ
sum-slots = 2  -- 1 tag + 1 payload slot (conservative estimate)

-- Stack requirement for an IR (slots allocated in current frame)
ir-stack-requirement : ∀ {A B} → IR A B → ℕ
ir-stack-requirement id = 0
ir-stack-requirement (g ∘ f) = ir-stack-requirement f + ir-stack-requirement g
ir-stack-requirement ⟨ f , g ⟩ = ir-stack-requirement f + ir-stack-requirement g + pair-slots
ir-stack-requirement fst-ir = 0
ir-stack-requirement snd-ir = 0
ir-stack-requirement inl-ir = sum-slots  -- allocates tag + payload
ir-stack-requirement inr-ir = sum-slots  -- allocates tag + payload
ir-stack-requirement (case-ir f g) = ir-stack-requirement f + ir-stack-requirement g  -- branches are mutually exclusive
ir-stack-requirement terminal = 0
ir-stack-requirement initial = 0  -- never executed (absurd)
ir-stack-requirement (curry f) = closure-slots  -- body f runs in NEW frame when applied
ir-stack-requirement apply = pair-slots  -- forms (env, arg) pair; body requirement separate
ir-stack-requirement fold-ir = 1  -- allocates heap pointer
ir-stack-requirement unfold-ir = 0  -- dereferences pointer, no allocation

------------------------------------------------------------------------
-- Stack Requirement Lemmas
------------------------------------------------------------------------

-- Compose: requirement is sum of components
∘-stack-req : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-stack-requirement (g ∘ f) ≡ ir-stack-requirement f + ir-stack-requirement g
∘-stack-req f g = refl

-- Pair: requirement is sum of components plus pair-slots
⟨,⟩-stack-req : ∀ {A B C} (f : IR A B) (g : IR A C) →
  ir-stack-requirement ⟨ f , g ⟩ ≡ ir-stack-requirement f + ir-stack-requirement g + pair-slots
⟨,⟩-stack-req f g = refl

-- After running f in compose, g still has enough capacity
-- If we start with capacity for f + g, after f we have capacity for g
∘-capacity-after-f : ∀ {A B C} (f : IR A B) (g : IR B C) (start-slot capacity : ℕ) →
  start-slot + ir-stack-requirement (g ∘ f) ≤ capacity →
  (start-slot + ir-stack-requirement f) + ir-stack-requirement g ≤ capacity
∘-capacity-after-f f g start cap pf = subst (_≤ cap) (sym (+-assoc start (ir-stack-requirement f) (ir-stack-requirement g))) pf
  where open import Data.Nat.Properties using (+-assoc)

-- After running f and g in pair, we still have capacity for pair allocation
-- Simplified: just restate in terms we need for the dispatcher
⟨,⟩-capacity-for-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (start-slot capacity : ℕ) →
  start-slot + ir-stack-requirement ⟨ f , g ⟩ ≤ capacity →
  start-slot + ir-stack-requirement f + ir-stack-requirement g + pair-slots ≤ capacity
⟨,⟩-capacity-for-pair f g start cap pf = subst (_≤ cap) eq pf
  where
    open import Data.Nat.Properties using (+-assoc)
    rf = ir-stack-requirement f
    rg = ir-stack-requirement g
    -- ir-stack-requirement ⟨ f , g ⟩ = rf + rg + pair-slots by definition
    -- So: start + (rf + rg + pair-slots) ≡ start + rf + rg + pair-slots
    -- Using +-assoc twice
    eq : start + (rf + rg + pair-slots) ≡ start + rf + rg + pair-slots
    eq = trans (sym (+-assoc start (rf + rg) pair-slots))
               (cong (_+ pair-slots) (sym (+-assoc start rf rg)))

------------------------------------------------------------------------
-- Summary
--
-- ALL definitions and lemmas are PROVEN (no postulates):
--
--   IR           - inductive data type
--   eval         - pattern matching
--   eval-*       - all refl
--   ir-size      - pattern matching
--   *-smaller    - arithmetic proofs
--   ir-stack-requirement - pattern matching
--   *-stack-req  - all refl
--   *-capacity-* - arithmetic proofs
------------------------------------------------------------------------
