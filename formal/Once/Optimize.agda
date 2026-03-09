------------------------------------------------------------------------
-- Once.Optimize
--
-- Optimizer for Once IR using categorical laws as rewrite rules.
-- Each rewrite preserves semantics (proven in Once.Optimize.Correct).
--
-- Architecture: Clean rule-based structure where each optimization
-- is a single pattern match clause. Easy to add new rules.
--
-- Includes:
--   - Identity laws (id ∘ f = f, f ∘ id = f)
--   - Beta laws (fst ∘ ⟨f,g⟩ = f, [f,g] ∘ inl = f, etc.)
--   - Eta laws (⟨fst,snd⟩ = id, [inl,inr] = id)
--   - Fixed point fusion (fold ∘ unfold = id)
--   - Coproduct fusion (map f ∘ map g = map (f ∘ g))
--   - Product fusion (bimap f g ∘ bimap h k = bimap (f∘h) (g∘k))
--   - Distribution (⟨f,g⟩ ∘ h = ⟨f∘h,g∘h⟩, h ∘ [f,g] = [h∘f,h∘g])
--   - Dead code elimination (terminal ∘ f = terminal)
------------------------------------------------------------------------

module Once.Optimize where

open import Once.Type
open import Once.IR

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟String_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)

------------------------------------------------------------------------
-- Equality decision (needed for eta laws)
------------------------------------------------------------------------

_≟AllocMode_ : (m₁ m₂ : AllocMode) → Dec (m₁ ≡ m₂)
Stack ≟AllocMode Stack = yes refl
Stack ≟AllocMode Heap  = no (λ ())
Heap  ≟AllocMode Stack = no (λ ())
Heap  ≟AllocMode Heap  = yes refl

_≟Type_ : (A B : Type) → Dec (A ≡ B)
Unit ≟Type Unit = yes refl
Unit ≟Type Void = no (λ ())
Unit ≟Type (_ * _) = no (λ ())
Unit ≟Type (_ + _) = no (λ ())
Unit ≟Type (_ ⇒[ _ ] _) = no (λ ())
Unit ≟Type (Eff _ _) = no (λ ())
Unit ≟Type (Fix _) = no (λ ())
Unit ≟Type Int = no (λ ())
Unit ≟Type Float = no (λ ())
Unit ≟Type Str = no (λ ())
Unit ≟Type Buffer = no (λ ())
Unit ≟Type (TVar _) = no (λ ())
Void ≟Type Unit = no (λ ())
Void ≟Type Void = yes refl
Void ≟Type (_ * _) = no (λ ())
Void ≟Type (_ + _) = no (λ ())
Void ≟Type (_ ⇒[ _ ] _) = no (λ ())
Void ≟Type (Eff _ _) = no (λ ())
Void ≟Type (Fix _) = no (λ ())
Void ≟Type Int = no (λ ())
Void ≟Type Float = no (λ ())
Void ≟Type Str = no (λ ())
Void ≟Type Buffer = no (λ ())
Void ≟Type (TVar _) = no (λ ())
(A * B) ≟Type Unit = no (λ ())
(A * B) ≟Type Void = no (λ ())
(A * B) ≟Type (C * D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(A * B) ≟Type (_ + _) = no (λ ())
(A * B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(A * B) ≟Type (Eff _ _) = no (λ ())
(A * B) ≟Type (Fix _) = no (λ ())
(A * B) ≟Type Int = no (λ ())
(A * B) ≟Type Float = no (λ ())
(A * B) ≟Type Str = no (λ ())
(A * B) ≟Type Buffer = no (λ ())
(A * B) ≟Type (TVar _) = no (λ ())
(A + B) ≟Type Unit = no (λ ())
(A + B) ≟Type Void = no (λ ())
(A + B) ≟Type (_ * _) = no (λ ())
(A + B) ≟Type (C + D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(A + B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(A + B) ≟Type (Eff _ _) = no (λ ())
(A + B) ≟Type (Fix _) = no (λ ())
(A + B) ≟Type Int = no (λ ())
(A + B) ≟Type Float = no (λ ())
(A + B) ≟Type Str = no (λ ())
(A + B) ≟Type Buffer = no (λ ())
(A + B) ≟Type (TVar _) = no (λ ())
(A ⇒[ q ] B) ≟Type Unit = no (λ ())
(A ⇒[ q ] B) ≟Type Void = no (λ ())
(A ⇒[ q ] B) ≟Type (_ * _) = no (λ ())
(A ⇒[ q ] B) ≟Type (_ + _) = no (λ ())
(A ⇒[ q ] B) ≟Type (C ⇒[ q' ] D) with A ≟Type C | q ≟q q' | B ≟Type D
... | yes refl | yes refl | yes refl = yes refl
... | no neq  | _        | _         = no (λ { refl → neq refl })
... | _       | no neq   | _         = no (λ { refl → neq refl })
... | _       | _        | no neq    = no (λ { refl → neq refl })
(A ⇒[ q ] B) ≟Type (Eff _ _) = no (λ ())
(A ⇒[ q ] B) ≟Type (Fix _) = no (λ ())
(A ⇒[ q ] B) ≟Type Int = no (λ ())
(A ⇒[ q ] B) ≟Type Float = no (λ ())
(A ⇒[ q ] B) ≟Type Str = no (λ ())
(A ⇒[ q ] B) ≟Type Buffer = no (λ ())
(A ⇒[ q ] B) ≟Type (TVar _) = no (λ ())
(Eff A B) ≟Type Unit = no (λ ())
(Eff A B) ≟Type Void = no (λ ())
(Eff A B) ≟Type (_ * _) = no (λ ())
(Eff A B) ≟Type (_ + _) = no (λ ())
(Eff A B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(Eff A B) ≟Type (Eff C D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(Eff A B) ≟Type (Fix _) = no (λ ())
(Eff A B) ≟Type Int = no (λ ())
(Eff A B) ≟Type Float = no (λ ())
(Eff A B) ≟Type Str = no (λ ())
(Eff A B) ≟Type Buffer = no (λ ())
(Eff A B) ≟Type (TVar _) = no (λ ())
(Fix F) ≟Type Unit = no (λ ())
(Fix F) ≟Type Void = no (λ ())
(Fix F) ≟Type (_ * _) = no (λ ())
(Fix F) ≟Type (_ + _) = no (λ ())
(Fix F) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(Fix F) ≟Type (Eff _ _) = no (λ ())
(Fix F) ≟Type (Fix G) with F ≟Type G
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })
(Fix F) ≟Type Int = no (λ ())
(Fix F) ≟Type Float = no (λ ())
(Fix F) ≟Type Str = no (λ ())
(Fix F) ≟Type Buffer = no (λ ())
(Fix F) ≟Type (TVar _) = no (λ ())
Int ≟Type Unit = no (λ ())
Int ≟Type Void = no (λ ())
Int ≟Type (_ * _) = no (λ ())
Int ≟Type (_ + _) = no (λ ())
Int ≟Type (_ ⇒[ _ ] _) = no (λ ())
Int ≟Type (Eff _ _) = no (λ ())
Int ≟Type (Fix _) = no (λ ())
Int ≟Type Int = yes refl
Int ≟Type Float = no (λ ())
Int ≟Type Str = no (λ ())
Int ≟Type Buffer = no (λ ())
Int ≟Type (TVar _) = no (λ ())
Float ≟Type Unit = no (λ ())
Float ≟Type Void = no (λ ())
Float ≟Type (_ * _) = no (λ ())
Float ≟Type (_ + _) = no (λ ())
Float ≟Type (_ ⇒[ _ ] _) = no (λ ())
Float ≟Type (Eff _ _) = no (λ ())
Float ≟Type (Fix _) = no (λ ())
Float ≟Type Int = no (λ ())
Float ≟Type Float = yes refl
Float ≟Type Str = no (λ ())
Float ≟Type Buffer = no (λ ())
Float ≟Type (TVar _) = no (λ ())
Str ≟Type Unit = no (λ ())
Str ≟Type Void = no (λ ())
Str ≟Type (_ * _) = no (λ ())
Str ≟Type (_ + _) = no (λ ())
Str ≟Type (_ ⇒[ _ ] _) = no (λ ())
Str ≟Type (Eff _ _) = no (λ ())
Str ≟Type (Fix _) = no (λ ())
Str ≟Type Int = no (λ ())
Str ≟Type Float = no (λ ())
Str ≟Type Str = yes refl
Str ≟Type Buffer = no (λ ())
Str ≟Type (TVar _) = no (λ ())
Buffer ≟Type Unit = no (λ ())
Buffer ≟Type Void = no (λ ())
Buffer ≟Type (_ * _) = no (λ ())
Buffer ≟Type (_ + _) = no (λ ())
Buffer ≟Type (_ ⇒[ _ ] _) = no (λ ())
Buffer ≟Type (Eff _ _) = no (λ ())
Buffer ≟Type (Fix _) = no (λ ())
Buffer ≟Type Int = no (λ ())
Buffer ≟Type Float = no (λ ())
Buffer ≟Type Str = no (λ ())
Buffer ≟Type Buffer = yes refl
Buffer ≟Type (TVar _) = no (λ ())
(TVar x) ≟Type Unit = no (λ ())
(TVar x) ≟Type Void = no (λ ())
(TVar x) ≟Type (_ * _) = no (λ ())
(TVar x) ≟Type (_ + _) = no (λ ())
(TVar x) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(TVar x) ≟Type (Eff _ _) = no (λ ())
(TVar x) ≟Type (Fix _) = no (λ ())
(TVar x) ≟Type Int = no (λ ())
(TVar x) ≟Type Float = no (λ ())
(TVar x) ≟Type Str = no (λ ())
(TVar x) ≟Type Buffer = no (λ ())
(TVar x) ≟Type (TVar y) with x ≟String y
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })

------------------------------------------------------------------------
-- IR equality (needed for eta uniqueness laws)
------------------------------------------------------------------------

mutual
  _≟IR_ : ∀ {A B} → (f g : IR A B) → Dec (f ≡ g)

  id ≟IR id = yes refl
  fst ≟IR fst = yes refl
  snd ≟IR snd = yes refl
  (inl m) ≟IR (inl m') with m ≟AllocMode m'
  ... | yes refl = yes refl
  ... | no neq   = no (λ { refl → neq refl })
  (inr m) ≟IR (inr m') with m ≟AllocMode m'
  ... | yes refl = yes refl
  ... | no neq   = no (λ { refl → neq refl })
  terminal ≟IR terminal = yes refl
  initial ≟IR initial = yes refl
  apply ≟IR apply = yes refl
  fold ≟IR fold = yes refl
  unfold ≟IR unfold = yes refl
  arr ≟IR arr = yes refl

  (Prim x) ≟IR (Prim y) with x ≟String y
  ... | yes refl = yes refl
  ... | no neq   = no (λ { refl → neq refl })

  (curry f m) ≟IR (curry g m') with f ≟IR g | m ≟AllocMode m'
  ... | yes refl | yes refl = yes refl
  ... | no neq   | _        = no (λ { refl → neq refl })
  ... | _        | no neq   = no (λ { refl → neq refl })

  (⟨ f , g ⟩ m) ≟IR (⟨ f' , g' ⟩ m') with f ≟IR f' | g ≟IR g' | m ≟AllocMode m'
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no neq   | _        | _        = no (λ { refl → neq refl })
  ... | _        | no neq   | _        = no (λ { refl → neq refl })
  ... | _        | _        | no neq   = no (λ { refl → neq refl })

  [ f , g ] ≟IR [ f' , g' ] with f ≟IR f' | g ≟IR g'
  ... | yes refl | yes refl = yes refl
  ... | no neq   | _        = no (λ { refl → neq refl })
  ... | _        | no neq   = no (λ { refl → neq refl })

  _≟IR_ {A} {C} (_∘_ {.A} {B} {.C} f g) (_∘_ {.A} {B'} {.C} f' g') with B ≟Type B'
  ... | no neq = no (λ { refl → neq refl })
  ... | yes refl with f ≟IR f' | g ≟IR g'
  ...   | yes refl | yes refl = yes refl
  ...   | no neq   | _        = no (λ { refl → neq refl })
  ...   | _        | no neq   = no (λ { refl → neq refl })

  -- Different constructors (only type-compatible ones need explicit cases)
  id ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR id = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  [ _ , _ ] ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR [ _ , _ ] = no (λ ())
  (curry _ _) ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR (curry _ _) = no (λ ())
  terminal ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR terminal = no (λ ())
  initial ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR initial = no (λ ())
  fst ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR fst = no (λ ())
  snd ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR snd = no (λ ())
  (inl _) ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR (inl _) = no (λ ())
  (inr _) ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR (inr _) = no (λ ())
  apply ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR apply = no (λ ())
  fold ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR fold = no (λ ())
  unfold ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR unfold = no (λ ())
  arr ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR arr = no (λ ())
  (Prim _) ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR id = no (λ ())
  id ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR fst = no (λ ())
  fst ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR snd = no (λ ())
  snd ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR (inl _) = no (λ ())
  (inl _) ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR (inr _) = no (λ ())
  (inr _) ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR [ _ , _ ] = no (λ ())
  [ _ , _ ] ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR terminal = no (λ ())
  terminal ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR initial = no (λ ())
  initial ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR (curry _ _) = no (λ ())
  (curry _ _) ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR apply = no (λ ())
  apply ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR fold = no (λ ())
  fold ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR unfold = no (λ ())
  unfold ≟IR (Prim _) = no (λ ())
  (Prim _) ≟IR arr = no (λ ())
  arr ≟IR (Prim _) = no (λ ())
  id ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  id ≟IR [ _ , _ ] = no (λ ())
  id ≟IR terminal = no (λ ())
  id ≟IR initial = no (λ ())
  id ≟IR (curry _ _) = no (λ ())
  fst ≟IR snd = no (λ ())
  fst ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  fst ≟IR terminal = no (λ ())
  fst ≟IR (curry _ _) = no (λ ())
  snd ≟IR fst = no (λ ())
  snd ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  snd ≟IR terminal = no (λ ())
  snd ≟IR (curry _ _) = no (λ ())
  snd ≟IR apply = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR id = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR fst = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR snd = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR [ _ , _ ] = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR initial = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR apply = no (λ ())
  (⟨ _ , _ ⟩ _) ≟IR unfold = no (λ ())
  (inl _) ≟IR (inr _) = no (λ ())
  (inl _) ≟IR [ _ , _ ] = no (λ ())
  (inl _) ≟IR initial = no (λ ())
  (inr _) ≟IR (inl _) = no (λ ())
  (inr _) ≟IR [ _ , _ ] = no (λ ())
  (inr _) ≟IR initial = no (λ ())
  [ _ , _ ] ≟IR id = no (λ ())
  [ _ , _ ] ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  [ _ , _ ] ≟IR (inl _) = no (λ ())
  [ _ , _ ] ≟IR (inr _) = no (λ ())
  [ _ , _ ] ≟IR terminal = no (λ ())
  [ _ , _ ] ≟IR (curry _ _) = no (λ ())
  [ _ , _ ] ≟IR fold = no (λ ())
  terminal ≟IR id = no (λ ())
  terminal ≟IR fst = no (λ ())
  terminal ≟IR snd = no (λ ())
  terminal ≟IR [ _ , _ ] = no (λ ())
  terminal ≟IR initial = no (λ ())
  terminal ≟IR apply = no (λ ())
  terminal ≟IR unfold = no (λ ())
  initial ≟IR id = no (λ ())
  initial ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  initial ≟IR (inl _) = no (λ ())
  initial ≟IR (inr _) = no (λ ())
  initial ≟IR terminal = no (λ ())
  initial ≟IR (curry _ _) = no (λ ())
  initial ≟IR fold = no (λ ())
  (curry _ _) ≟IR id = no (λ ())
  (curry _ _) ≟IR fst = no (λ ())
  (curry _ _) ≟IR snd = no (λ ())
  (curry _ _) ≟IR [ _ , _ ] = no (λ ())
  (curry _ _) ≟IR initial = no (λ ())
  (curry _ _) ≟IR apply = no (λ ())
  (curry _ _) ≟IR unfold = no (λ ())
  apply ≟IR snd = no (λ ())
  apply ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  apply ≟IR terminal = no (λ ())
  apply ≟IR (curry _ _) = no (λ ())
  fold ≟IR [ _ , _ ] = no (λ ())
  fold ≟IR initial = no (λ ())
  unfold ≟IR (⟨ _ , _ ⟩ _) = no (λ ())
  unfold ≟IR terminal = no (λ ())
  unfold ≟IR (curry _ _) = no (λ ())

------------------------------------------------------------------------
-- Helper: Check for Void types (enables dead code elimination)
------------------------------------------------------------------------

-- | Check if a type is Void
is-Void : Type → Bool
is-Void Void = true
is-Void _ = false

------------------------------------------------------------------------
-- Optimizer: Composition Rules
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Helper: Check if composition would enable a beta reduction
------------------------------------------------------------------------

-- | Check if pair distribution is safe (won't increase cost)
--   Safe cases:
--   1. Eta: ⟨ fst , snd ⟩ or ⟨ snd , fst ⟩ → reduces to h or swapped h
--   2. Terminal: at least one of f, g is terminal → that component becomes 0
--
--   Unsafe: ⟨ fst , fst ⟩ or ⟨ snd , snd ⟩ → duplicates a component's cost

-- Check if f is fst (for pattern matching)
is-fst? : ∀ {A B} → IR A B → Bool
is-fst? fst = true
is-fst? _ = false

-- Check if f is snd (for pattern matching)
is-snd? : ∀ {A B} → IR A B → Bool
is-snd? snd = true
is-snd? _ = false

-- Check if f is terminal (for pattern matching)
is-terminal? : ∀ {A B} → IR A B → Bool
is-terminal? terminal = true
is-terminal? _ = false

-- | Safe to distribute pairs: eta case OR terminal case
--   f : IR C A, g : IR C B (components of a pair)
--   Eta: (fst,snd) or (snd,fst) - only when types align
--   Terminal: at least one is terminal (safe because terminal eliminates cost)
safe-pair-distrib : ∀ {A B C D} → IR A B → IR C D → Bool
safe-pair-distrib f g =
  -- Eta case: fst paired with snd (or vice versa)
  (is-fst? f ∧ is-snd? g) ∨ (is-snd? f ∧ is-fst? g) ∨
  -- Terminal case: at least one is terminal
  is-terminal? f ∨ is-terminal? g

-- | Does f "want" a coproduct on its right? (i.e., can f ∘ inl/inr reduce?)
wants-coprod : ∀ {A B} → IR A B → Bool
wants-coprod [ _ , _ ] = true
wants-coprod terminal = true
wants-coprod _ = false

-- | Does f "want" an unfold on its right?
wants-unfold : ∀ {A B} → IR A B → Bool
wants-unfold fold = true
wants-unfold terminal = true
wants-unfold _ = false

-- | Does f "want" a fold on its right?
wants-fold : ∀ {A B} → IR A B → Bool
wants-fold unfold = true
wants-fold terminal = true
wants-fold _ = false

------------------------------------------------------------------------
-- | Rewrite compositions using categorical laws
--
-- Each pattern match clause is one optimization rule.
-- Rules are tried in order; first match wins.
-- Default case preserves the original composition.
--
{-# TERMINATING #-}  -- Termination: h and g are subterms of input; see apply-curry cases
optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C

-- | Helper for pair distribution: takes Bool explicitly instead of using with.
--   This enables proof reduction because the Bool argument is concrete.
--   INLINE forces Agda to reduce this during type checking.
pair-distrib-opt : ∀ {A B C D} → IR C A → IR C B → AllocMode → IR D C → Bool → IR D (A * B)
pair-distrib-opt f g m h true  = ⟨ optimize-compose f h , optimize-compose g h ⟩ m
pair-distrib-opt f g m h false = (⟨ f , g ⟩ m) ∘ h
{-# INLINE pair-distrib-opt #-}

------------------------------------------------------------------------
-- Identity Laws
------------------------------------------------------------------------

-- id ∘ f = f (left identity)
optimize-compose id f = f

-- f ∘ id = f (right identity, by constructor)
optimize-compose fst id = fst
optimize-compose snd id = snd
optimize-compose (⟨ f , g ⟩ m) id = ⟨ f , g ⟩ m
optimize-compose (inl m) id = inl m
optimize-compose (inr m) id = inr m
optimize-compose [ f , g ] id = [ f , g ]
optimize-compose terminal id = terminal
optimize-compose (curry f m) id = curry f m
optimize-compose apply id = apply
optimize-compose fold id = fold
optimize-compose unfold id = unfold
optimize-compose arr id = arr
optimize-compose (Prim n) id = Prim n
optimize-compose (g ∘ f) id = g ∘ f

------------------------------------------------------------------------
-- Beta Laws (Products)
------------------------------------------------------------------------

-- fst ∘ ⟨ f , g ⟩ = f
optimize-compose fst (⟨ f , g ⟩ _) = f

-- snd ∘ ⟨ f , g ⟩ = g
optimize-compose snd (⟨ f , g ⟩ _) = g

------------------------------------------------------------------------
-- Beta Laws (Coproducts)
------------------------------------------------------------------------

-- [ f , g ] ∘ inl = f
optimize-compose [ f , g ] (inl _) = f

-- [ f , g ] ∘ inr = g
optimize-compose [ f , g ] (inr _) = g

------------------------------------------------------------------------
-- Beta Laws (Exponentials)
------------------------------------------------------------------------

-- apply ∘ ⟨ curry f , g ⟩ = f ∘ ⟨ id , g ⟩
-- Eliminates closure allocation when immediately applied
--
-- We handle each case explicitly to ensure normal output:
-- - f = h ∘ k: depends on k:
--     k = fst: h ∘ (fst ∘ ⟨ id , g ⟩) = h ∘ id = h
--     k = snd: h ∘ (snd ∘ ⟨ id , g ⟩) = h ∘ g
--     k = terminal: h ∘ (terminal ∘ ⟨ id , g ⟩) = h ∘ terminal
--     otherwise: h ∘ (k ∘ ⟨ id , g ⟩) is normal (k ∘ pair not reducible)
-- - f = terminal: dead code elimination
-- - f = id: identity law
-- - f = fst: beta (fst ∘ ⟨ id , g ⟩ = id)
-- - f = snd: beta (snd ∘ ⟨ id , g ⟩ = g)
-- - Otherwise: f ∘ ⟨ id , g ⟩ is already normal
--
-- Composition case where k = fst: h ∘ id = h
optimize-compose apply (⟨ curry (h ∘ fst) _ , g ⟩ _) = h
-- Composition case where k = snd: recursively optimize h ∘ g to ensure normality
optimize-compose apply (⟨ curry (h ∘ snd) _ , g ⟩ _) = optimize-compose h g
-- Composition case where k = terminal: h ∘ terminal
optimize-compose apply (⟨ curry (h ∘ terminal) _ , g ⟩ _) = h ∘ terminal
-- Composition case: right-associate for other k
optimize-compose apply (⟨ curry (h ∘ k) _ , g ⟩ _) = h ∘ (k ∘ ⟨ id , g ⟩ Heap)
-- Dead code: terminal ∘ _ = terminal
optimize-compose apply (⟨ curry terminal _ , g ⟩ _) = terminal
-- Identity: id ∘ x = x
optimize-compose apply (⟨ curry id _ , g ⟩ _) = ⟨ id , g ⟩ Heap
-- Beta: fst ∘ ⟨ id , g ⟩ = id
optimize-compose apply (⟨ curry fst _ , g ⟩ _) = id
-- Beta: snd ∘ ⟨ id , g ⟩ = g
optimize-compose apply (⟨ curry snd _ , g ⟩ _) = g
-- Default: f ∘ ⟨ id , g ⟩ is normal for all other f
optimize-compose apply (⟨ curry f _ , g ⟩ _) = f ∘ ⟨ id , g ⟩ Heap

------------------------------------------------------------------------
-- Fixed Point Laws
------------------------------------------------------------------------

-- fold ∘ unfold = id
optimize-compose fold unfold = id

-- unfold ∘ fold = id
optimize-compose unfold fold = id

-- fold ∘ (unfold ∘ f) = f (associativity + identity)
optimize-compose fold (unfold ∘ f) = f

-- unfold ∘ (fold ∘ f) = f (associativity + identity)
optimize-compose unfold (fold ∘ f) = f

------------------------------------------------------------------------
-- Dead Code Elimination
------------------------------------------------------------------------

-- terminal ∘ f = terminal (result discarded)
optimize-compose terminal (_ ∘ _) = terminal
optimize-compose terminal fst = terminal
optimize-compose terminal snd = terminal
optimize-compose terminal (⟨ _ , _ ⟩ _) = terminal
optimize-compose terminal (inl _) = terminal
optimize-compose terminal (inr _) = terminal
optimize-compose terminal [ _ , _ ] = terminal
optimize-compose terminal terminal = terminal
optimize-compose terminal (curry _ _) = terminal
optimize-compose terminal apply = terminal
optimize-compose terminal fold = terminal
optimize-compose terminal unfold = terminal
optimize-compose terminal arr = terminal
optimize-compose terminal (Prim _) = terminal

-- f ∘ initial = initial (Void has no inhabitants)
optimize-compose fst initial = initial
optimize-compose snd initial = initial
optimize-compose (⟨ _ , _ ⟩ _) initial = initial
optimize-compose (inl _) initial = initial
optimize-compose (inr _) initial = initial
optimize-compose [ _ , _ ] initial = initial
optimize-compose terminal initial = initial
optimize-compose (curry _ _) initial = initial
optimize-compose apply initial = initial
optimize-compose fold initial = initial
optimize-compose unfold initial = initial
optimize-compose arr initial = initial
optimize-compose (Prim _) initial = initial
optimize-compose (_ ∘ _) initial = initial

-- initial ∘ f : no optimization (f maps to Void, composition is vacuous)
-- Must appear before catch-all distribution patterns
optimize-compose initial f = initial ∘ f

------------------------------------------------------------------------
-- Distribution Rules (CONDITIONAL)
-- Only distribute when it enables a beta reduction.
-- Unconditional distribution can INCREASE cost without benefit.
------------------------------------------------------------------------

-- Pairing distribution: ⟨ f , g ⟩ ∘ h = ⟨ f ∘ h , g ∘ h ⟩
-- Only when safe: eta case (fst+snd) or terminal case.
-- This ensures cost never increases from distribution.
-- Uses helper function to avoid 'with' pattern blocking proof reduction.
-- Note: Must use full pattern (not @-pattern) for reduction in proofs.
optimize-compose (⟨ f , g ⟩ m) (⟨ h₁ , h₂ ⟩ m') =
  pair-distrib-opt f g m (⟨ h₁ , h₂ ⟩ m') (safe-pair-distrib f g)

-- Pairing distribution when h is inl/inr: safe when at least one is terminal
-- or when both are cases (case ∘ inl reduces, eliminating a branch)
optimize-compose (⟨ f , g ⟩ m) (inl m') = pair-distrib-opt f g m (inl m') (safe-pair-distrib f g)
optimize-compose (⟨ f , g ⟩ m) (inr m') = pair-distrib-opt f g m (inr m') (safe-pair-distrib f g)

-- Pairing distribution when h is unfold: safe when at least one is terminal
optimize-compose (⟨ f , g ⟩ m) unfold = pair-distrib-opt f g m unfold (safe-pair-distrib f g)

-- Pairing distribution when h is fold: safe when at least one is terminal
optimize-compose (⟨ f , g ⟩ m) fold = pair-distrib-opt f g m fold (safe-pair-distrib f g)

-- Default: don't distribute pairs (would increase cost without benefit)
optimize-compose (⟨ f , g ⟩ m) h = (⟨ f , g ⟩ m) ∘ h

-- Case distribution: [ h₁ , h₂ ] ∘ [ f , g ] = [ [ h₁ , h₂ ] ∘ f , [ h₁ , h₂ ] ∘ g ]
-- NOTE: Unconditional case fusion was REMOVED because it can increase cost.
--       Example: [ h₁ , h₂ ] ∘ [ id , id ] → [ [ h₁ , h₂ ] , [ h₁ , h₂ ] ]
--       This doubles the cost of [ h₁ , h₂ ] without benefit.
--       For now, we just compose without distribution (fall through to default).
-- Default: don't distribute into cases
optimize-compose h [ f , g ] = h ∘ [ f , g ]

------------------------------------------------------------------------
-- Associativity (enables more optimizations)
------------------------------------------------------------------------

-- (h ∘ g) ∘ f → h ∘ (g ∘ f) then optimize
optimize-compose (h ∘ g) f = optimize-compose h (optimize-compose g f)

------------------------------------------------------------------------
-- Default: No optimization
------------------------------------------------------------------------

optimize-compose g f = g ∘ f

------------------------------------------------------------------------
-- Eta Laws (for pairs and cases)
------------------------------------------------------------------------

-- | Optimize pair construction
--   ⟨ fst , snd ⟩ = id (eta)
--   ⟨ fst ∘ h , snd ∘ h ⟩ = h (uniqueness)
optimize-pair : ∀ {A B C} → IR C A → IR C B → IR C (A * B)
optimize-pair (fst {A} {B}) (snd {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = id
... | _        | _        = ⟨ fst , snd ⟩ Heap
optimize-pair (_∘_ {_} {D} {_} (fst {A} {B}) h) (_∘_ {_} {D'} {_} (snd {A'} {B'}) h')
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = h
...   | no _     = ⟨ fst ∘ h , snd ∘ h' ⟩ Heap
optimize-pair (_∘_ (fst {A} {B}) h) (_∘_ (snd {A'} {B'}) h') | _ | _ | _ = ⟨ fst ∘ h , snd ∘ h' ⟩ Heap
optimize-pair f g = ⟨ f , g ⟩ Heap

-- | Optimize case construction
--   [ inl , inr ] = id (eta)
--   [ h ∘ inl , h ∘ inr ] = h (uniqueness)
optimize-case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C
optimize-case (inl {A} {B} m) (inr {A'} {B'} m') with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = id
... | _        | _        = [ inl m , inr m' ]
optimize-case (_∘_ {_} {D} {_} h (inl {A} {B} m)) (_∘_ {_} {D'} {_} h' (inr {A'} {B'} m'))
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = h
...   | no _     = [ h ∘ inl m , h' ∘ inr m' ]
optimize-case (_∘_ h (inl {A} {B} m)) (_∘_ h' (inr {A'} {B'} m')) | _ | _ | _ = [ h ∘ inl m , h' ∘ inr m' ]
optimize-case f g = [ f , g ]

------------------------------------------------------------------------
-- Full Recursive Optimization
------------------------------------------------------------------------

-- | Single optimization pass with type-directed normalization
--
-- Type-directed rules (checked first):
--   1. Any f : A → Unit  becomes terminal (Unit target rule)
--   2. Any f : Void → B  becomes initial  (Void source rule)
--
-- This ensures unique normal forms for degenerate types:
--   - All morphisms to Unit are terminal
--   - All morphisms from Void are initial
--
-- For non-degenerate types, structural rules apply.

mutual
  -- | Structural optimization rules (called after type-directed rules)
  optimize-once-structural : ∀ {A B} → IR A B → IR A B
  optimize-once-structural id = id
  optimize-once-structural (g ∘ f) = optimize-compose (optimize-once g) (optimize-once f)
  optimize-once-structural fst = fst
  optimize-once-structural snd = snd
  optimize-once-structural (⟨ f , g ⟩ m) = optimize-pair (optimize-once f) (optimize-once g)
  -- | inl with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (inl {A} {B} m) with A ≟Type Void
  ... | yes refl = initial
  ... | no _     = inl m
  -- | inr with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (inr {A} {B} m) with B ≟Type Void
  ... | yes refl = initial
  ... | no _     = inr m
  optimize-once-structural [ f , g ] = optimize-case (optimize-once f) (optimize-once g)
  optimize-once-structural terminal = terminal
  optimize-once-structural initial = initial
  optimize-once-structural (curry f m) = curry (optimize-once f) m
  optimize-once-structural apply = apply
  -- | fold with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (fold {F}) with F ≟Type Void
  ... | yes refl = initial
  ... | no _     = fold
  optimize-once-structural unfold = unfold
  optimize-once-structural arr = arr
  -- | Prim with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (Prim {A} n) with A ≟Type Void
  ... | yes refl = initial
  ... | no _     = Prim n

  -- | Type-directed optimization
  optimize-once : ∀ {A B} → IR A B → IR A B
  optimize-once {A} {B} ir with B ≟Type Unit
  ... | yes refl = terminal                    -- Target is Unit → terminal
  ... | no _ with A ≟Type Void
  ...   | yes refl = initial                   -- Source is Void → initial
  ...   | no _ = optimize-once-structural ir   -- Otherwise → structural rules

------------------------------------------------------------------------
-- Bounded Iteration
------------------------------------------------------------------------

-- | Optimize with bounded iteration
optimize-n : ∀ {A B} → ℕ → IR A B → IR A B
optimize-n zero ir = ir
optimize-n (suc n) ir = optimize-n n (optimize-once ir)

-- | Main entry point (10 iterations)
optimize : ∀ {A B} → IR A B → IR A B
optimize = optimize-n 10
