{-# OPTIONS --sized-types #-}
------------------------------------------------------------------------
-- Once.Optimize
--
-- Optimizer for Once IR using categorical laws as rewrite rules.
-- Each rewrite preserves semantics (proven in Once.Optimize.Correct).
------------------------------------------------------------------------

module Once.Optimize where

open import Once.Type
open import Once.IR

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟String_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import Size using (Size; ∞)

------------------------------------------------------------------------
-- Equality decision for Types (needed for pattern matching)
------------------------------------------------------------------------

_≟Type_ : (A B : Type) → Dec (A ≡ B)
-- Unit cases
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
-- Void cases
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
-- Product cases
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
-- Sum cases
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
-- Arrow cases
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
-- Eff cases
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
-- Fix cases
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
-- Int cases
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
-- Float cases
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
-- Str cases
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
-- Buffer cases
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
-- TVar cases
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
-- Decidable equality for IR (needed for uniqueness optimizations)
------------------------------------------------------------------------

-- Decidable equality for IR terms of the same type.
-- Many constructor combinations are type-impossible (e.g., id vs fst
-- would require A = A * B which is cyclic). Agda's pattern matching
-- automatically excludes these cases.

mutual
  _≟IR_ : ∀ {A B} → (f g : IR ∞ A B) → Dec (f ≡ g)

  -- Same constructor cases
  id ≟IR id = yes refl
  fst ≟IR fst = yes refl
  snd ≟IR snd = yes refl
  inl ≟IR inl = yes refl
  inr ≟IR inr = yes refl
  terminal ≟IR terminal = yes refl
  initial ≟IR initial = yes refl
  apply ≟IR apply = yes refl
  fold ≟IR fold = yes refl
  unfold ≟IR unfold = yes refl
  arr ≟IR arr = yes refl

  -- Recursive constructors - same constructor
  (curry f) ≟IR (curry g) with f ≟IR g
  ... | yes refl = yes refl
  ... | no neq   = no (λ { refl → neq refl })

  ⟨ f , g ⟩ ≟IR ⟨ f' , g' ⟩ with f ≟IR f' | g ≟IR g'
  ... | yes refl | yes refl = yes refl
  ... | no neq   | _        = no (λ { refl → neq refl })
  ... | _        | no neq   = no (λ { refl → neq refl })

  [ f , g ] ≟IR [ f' , g' ] with f ≟IR f' | g ≟IR g'
  ... | yes refl | yes refl = yes refl
  ... | no neq   | _        = no (λ { refl → neq refl })
  ... | _        | no neq   = no (λ { refl → neq refl })

  -- Composition vs composition - need matching intermediate types
  _≟IR_ {A} {C} (_∘_ {_} {.A} {B} {.C} f g) (_∘_ {_} {.A} {B'} {.C} f' g') with B ≟Type B'
  ... | no neq = no (λ { refl → neq refl })
  ... | yes refl with f ≟IR f' | g ≟IR g'
  ...   | yes refl | yes refl = yes refl
  ...   | no neq   | _        = no (λ { refl → neq refl })
  ...   | _        | no neq   = no (λ { refl → neq refl })

  -- Different constructor cases (type-compatible ones)
  -- Composition vs non-composition
  id ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR id = no (λ ())

  ⟨ _ , _ ⟩ ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR ⟨ _ , _ ⟩ = no (λ ())

  [ _ , _ ] ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR [ _ , _ ] = no (λ ())

  (curry _) ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR (curry _) = no (λ ())

  terminal ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR terminal = no (λ ())

  initial ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR initial = no (λ ())

  fst ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR fst = no (λ ())

  snd ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR snd = no (λ ())

  inl ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR inl = no (λ ())

  inr ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR inr = no (λ ())

  apply ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR apply = no (λ ())

  fold ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR fold = no (λ ())

  unfold ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR unfold = no (λ ())

  arr ≟IR (_ ∘ _) = no (λ ())
  (_ ∘ _) ≟IR arr = no (λ ())

  -- Remaining type-compatible different-constructor cases
  id ≟IR ⟨ _ , _ ⟩ = no (λ ())
  id ≟IR [ _ , _ ] = no (λ ())
  id ≟IR terminal = no (λ ())
  id ≟IR initial = no (λ ())
  id ≟IR (curry _) = no (λ ())

  fst ≟IR snd = no (λ ())
  fst ≟IR ⟨ _ , _ ⟩ = no (λ ())
  fst ≟IR terminal = no (λ ())
  fst ≟IR (curry _) = no (λ ())

  snd ≟IR fst = no (λ ())
  snd ≟IR ⟨ _ , _ ⟩ = no (λ ())
  snd ≟IR terminal = no (λ ())
  snd ≟IR (curry _) = no (λ ())
  snd ≟IR apply = no (λ ())

  ⟨ _ , _ ⟩ ≟IR id = no (λ ())
  ⟨ _ , _ ⟩ ≟IR fst = no (λ ())
  ⟨ _ , _ ⟩ ≟IR snd = no (λ ())
  ⟨ _ , _ ⟩ ≟IR [ _ , _ ] = no (λ ())
  ⟨ _ , _ ⟩ ≟IR initial = no (λ ())
  ⟨ _ , _ ⟩ ≟IR apply = no (λ ())
  ⟨ _ , _ ⟩ ≟IR unfold = no (λ ())

  inl ≟IR inr = no (λ ())
  inl ≟IR [ _ , _ ] = no (λ ())
  inl ≟IR initial = no (λ ())

  inr ≟IR inl = no (λ ())
  inr ≟IR [ _ , _ ] = no (λ ())
  inr ≟IR initial = no (λ ())

  [ _ , _ ] ≟IR id = no (λ ())
  [ _ , _ ] ≟IR ⟨ _ , _ ⟩ = no (λ ())
  [ _ , _ ] ≟IR inl = no (λ ())
  [ _ , _ ] ≟IR inr = no (λ ())
  [ _ , _ ] ≟IR terminal = no (λ ())
  [ _ , _ ] ≟IR (curry _) = no (λ ())
  [ _ , _ ] ≟IR fold = no (λ ())

  terminal ≟IR id = no (λ ())
  terminal ≟IR fst = no (λ ())
  terminal ≟IR snd = no (λ ())
  terminal ≟IR [ _ , _ ] = no (λ ())
  terminal ≟IR initial = no (λ ())
  terminal ≟IR apply = no (λ ())
  terminal ≟IR unfold = no (λ ())

  initial ≟IR id = no (λ ())
  initial ≟IR ⟨ _ , _ ⟩ = no (λ ())
  initial ≟IR inl = no (λ ())
  initial ≟IR inr = no (λ ())
  initial ≟IR terminal = no (λ ())
  initial ≟IR (curry _) = no (λ ())
  initial ≟IR fold = no (λ ())

  (curry _) ≟IR id = no (λ ())
  (curry _) ≟IR fst = no (λ ())
  (curry _) ≟IR snd = no (λ ())
  (curry _) ≟IR [ _ , _ ] = no (λ ())
  (curry _) ≟IR initial = no (λ ())
  (curry _) ≟IR apply = no (λ ())
  (curry _) ≟IR unfold = no (λ ())

  apply ≟IR snd = no (λ ())
  apply ≟IR ⟨ _ , _ ⟩ = no (λ ())
  apply ≟IR terminal = no (λ ())
  apply ≟IR (curry _) = no (λ ())

  fold ≟IR [ _ , _ ] = no (λ ())
  fold ≟IR initial = no (λ ())

  unfold ≟IR ⟨ _ , _ ⟩ = no (λ ())
  unfold ≟IR terminal = no (λ ())
  unfold ≟IR (curry _) = no (λ ())

------------------------------------------------------------------------
-- Optimizer: Single-step rewriting
------------------------------------------------------------------------

-- | Optimize a single composition
--
-- Applies categorical laws to simplify f ∘ g patterns.
-- Returns the simplified IR.
--
-- Note: We avoid overlapping patterns to get definitional equalities in proofs.
-- Each constructor is handled explicitly.
--
optimize-compose : ∀ {A B C} → IR ∞ B C → IR ∞ A B → IR ∞ A C

-- Left identity: id ∘ f = f (always applies when left arg is id)
optimize-compose id f = f

-- Right identity: fst ∘ id = fst, etc. (when right arg is id, left is not)
optimize-compose fst id = fst
optimize-compose snd id = snd
optimize-compose ⟨ f , g ⟩ id = ⟨ f , g ⟩
optimize-compose inl id = inl
optimize-compose inr id = inr
optimize-compose [ f , g ] id = [ f , g ]
optimize-compose terminal id = terminal
optimize-compose (curry f) id = curry f
optimize-compose apply id = apply
optimize-compose fold id = fold
optimize-compose unfold id = unfold
optimize-compose arr id = arr
optimize-compose (h ∘ g) id = h ∘ g  -- Don't simplify here, let associativity handle it

-- Product beta laws: fst ∘ ⟨ f , g ⟩ = f, snd ∘ ⟨ f , g ⟩ = g
optimize-compose fst ⟨ f , g ⟩ = f
optimize-compose snd ⟨ f , g ⟩ = g

-- Coproduct beta laws: [ f , g ] ∘ inl = f, [ f , g ] ∘ inr = g
optimize-compose [ f , g ] inl = f
optimize-compose [ f , g ] inr = g

-- Fixed point laws: fold ∘ unfold = id, unfold ∘ fold = id
optimize-compose fold unfold = id
optimize-compose unfold fold = id

-- Terminal fusion: terminal ∘ f = terminal (dead code elimination)
-- Any computation followed by discarding the result can skip the computation
optimize-compose terminal (g ∘ f) = terminal
optimize-compose terminal fst = terminal
optimize-compose terminal snd = terminal
optimize-compose terminal ⟨ f , g ⟩ = terminal
optimize-compose terminal inl = terminal
optimize-compose terminal inr = terminal
optimize-compose terminal [ f , g ] = terminal
optimize-compose terminal terminal = terminal
optimize-compose terminal (curry f) = terminal
optimize-compose terminal apply = terminal
optimize-compose terminal fold = terminal
optimize-compose terminal unfold = terminal
optimize-compose terminal arr = terminal

-- Initial absorption: f ∘ initial = initial (dead code elimination)
-- Composition with initial is initial (vacuously true, Void is empty)
optimize-compose fst initial = initial
optimize-compose snd initial = initial
optimize-compose ⟨ f , g ⟩ initial = initial
optimize-compose inl initial = initial
optimize-compose inr initial = initial
optimize-compose [ f , g ] initial = initial
optimize-compose terminal initial = initial
optimize-compose (curry f) initial = initial
optimize-compose apply initial = initial
optimize-compose fold initial = initial
optimize-compose unfold initial = initial
optimize-compose arr initial = initial
optimize-compose (h ∘ g) initial = initial

-- Pairing fusion: ⟨ f , g ⟩ ∘ h = ⟨ f ∘ h , g ∘ h ⟩
-- Distributes composition into pairs, exposing beta reductions
-- Note: id and initial cases handled above
optimize-compose ⟨ f , g ⟩ (h ∘ k) = ⟨ optimize-compose f (h ∘ k) , optimize-compose g (h ∘ k) ⟩
optimize-compose ⟨ f , g ⟩ fst = ⟨ optimize-compose f fst , optimize-compose g fst ⟩
optimize-compose ⟨ f , g ⟩ snd = ⟨ optimize-compose f snd , optimize-compose g snd ⟩
optimize-compose ⟨ f , g ⟩ ⟨ h , k ⟩ = ⟨ optimize-compose f ⟨ h , k ⟩ , optimize-compose g ⟨ h , k ⟩ ⟩
optimize-compose ⟨ f , g ⟩ inl = ⟨ optimize-compose f inl , optimize-compose g inl ⟩
optimize-compose ⟨ f , g ⟩ inr = ⟨ optimize-compose f inr , optimize-compose g inr ⟩
optimize-compose ⟨ f , g ⟩ [ h , k ] = ⟨ optimize-compose f [ h , k ] , optimize-compose g [ h , k ] ⟩
optimize-compose ⟨ f , g ⟩ terminal = ⟨ optimize-compose f terminal , optimize-compose g terminal ⟩
optimize-compose ⟨ f , g ⟩ (curry h) = ⟨ optimize-compose f (curry h) , optimize-compose g (curry h) ⟩
optimize-compose ⟨ f , g ⟩ apply = ⟨ optimize-compose f apply , optimize-compose g apply ⟩
optimize-compose ⟨ f , g ⟩ fold = ⟨ optimize-compose f fold , optimize-compose g fold ⟩
optimize-compose ⟨ f , g ⟩ unfold = ⟨ optimize-compose f unfold , optimize-compose g unfold ⟩
optimize-compose ⟨ f , g ⟩ arr = ⟨ optimize-compose f arr , optimize-compose g arr ⟩

-- Case fusion: h ∘ [ f , g ] = [ h ∘ f , h ∘ g ]
-- Distributes composition over case, exposing beta reductions
-- Note: beta laws ([ f , g ] ∘ inl/inr) and terminal handled above
-- Note: ⟨ h , k ⟩ [ f , g ] is covered by pairing fusion above
optimize-compose fst [ f , g ] = [ optimize-compose fst f , optimize-compose fst g ]
optimize-compose snd [ f , g ] = [ optimize-compose snd f , optimize-compose snd g ]
optimize-compose inl [ f , g ] = [ optimize-compose inl f , optimize-compose inl g ]
optimize-compose inr [ f , g ] = [ optimize-compose inr f , optimize-compose inr g ]
optimize-compose (curry h) [ f , g ] = [ optimize-compose (curry h) f , optimize-compose (curry h) g ]
optimize-compose apply [ f , g ] = [ optimize-compose apply f , optimize-compose apply g ]
optimize-compose fold [ f , g ] = [ optimize-compose fold f , optimize-compose fold g ]
optimize-compose unfold [ f , g ] = [ optimize-compose unfold f , optimize-compose unfold g ]
optimize-compose arr [ f , g ] = [ optimize-compose arr f , optimize-compose arr g ]

-- Associativity: normalize to right-associative form
-- (h ∘ g) ∘ f  →  h ∘ (g ∘ f)
-- This exposes more optimization opportunities
optimize-compose (h ∘ g) f = optimize-compose h (optimize-compose g f)

-- No simplification: return as-is
optimize-compose g f = g ∘ f

------------------------------------------------------------------------
-- Optimizer: Simplify pair
------------------------------------------------------------------------

-- | Optimize a pair
--
-- Applies:
--   1. Eta law: ⟨ fst , snd ⟩ = id
--   2. Uniqueness law: ⟨ fst ∘ h , snd ∘ h ⟩ = h
--
optimize-pair : ∀ {A B C} → IR ∞ C A → IR ∞ C B → IR ∞ C (A * B)
-- Eta: ⟨ fst , snd ⟩ = id
optimize-pair (fst {_} {A} {B}) (snd {_} {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = id
... | _        | _        = ⟨ fst , snd ⟩
-- Uniqueness: ⟨ fst ∘ h , snd ∘ h ⟩ = h
optimize-pair (_∘_ {_} {_} {D} {_} (fst {_} {A} {B}) h) (_∘_ {_} {_} {D'} {_} (snd {_} {A'} {B'}) h')
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = h                  -- ⟨ fst ∘ h , snd ∘ h ⟩ = h
...   | no _     = ⟨ fst ∘ h , snd ∘ h' ⟩
optimize-pair (_∘_ (fst {_} {A} {B}) h) (_∘_ (snd {_} {A'} {B'}) h') | _ | _ | _ = ⟨ fst ∘ h , snd ∘ h' ⟩
-- Default: no simplification
optimize-pair f g = ⟨ f , g ⟩

------------------------------------------------------------------------
-- Optimizer: Simplify case
------------------------------------------------------------------------

-- | Optimize a case
--
-- Applies:
--   1. Eta law: [ inl , inr ] = id
--   2. Uniqueness law: [ h ∘ inl , h ∘ inr ] = h
--
optimize-case : ∀ {A B C} → IR ∞ A C → IR ∞ B C → IR ∞ (A + B) C
-- Eta: [ inl , inr ] = id
optimize-case (inl {_} {A} {B}) (inr {_} {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = id
... | _        | _        = [ inl , inr ]
-- Uniqueness: [ h ∘ inl , h ∘ inr ] = h
optimize-case (_∘_ {_} {_} {D} {_} h (inl {_} {A} {B})) (_∘_ {_} {_} {D'} {_} h' (inr {_} {A'} {B'}))
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = h                  -- [ h ∘ inl , h ∘ inr ] = h
...   | no _     = [ h ∘ inl , h' ∘ inr ]
optimize-case (_∘_ h (inl {_} {A} {B})) (_∘_ h' (inr {_} {A'} {B'})) | _ | _ | _ = [ h ∘ inl , h' ∘ inr ]
-- Default: no simplification
optimize-case f g = [ f , g ]

------------------------------------------------------------------------
-- Optimizer: Full recursive optimization
------------------------------------------------------------------------

-- | Single optimization pass
--
-- Recursively optimize all subterms, then apply simplifications.
--
optimize-once : ∀ {A B} → IR ∞ A B → IR ∞ A B
optimize-once id = id
optimize-once (g ∘ f) = optimize-compose (optimize-once g) (optimize-once f)
optimize-once fst = fst
optimize-once snd = snd
optimize-once ⟨ f , g ⟩ = optimize-pair (optimize-once f) (optimize-once g)
optimize-once inl = inl
optimize-once inr = inr
optimize-once [ f , g ] = optimize-case (optimize-once f) (optimize-once g)
optimize-once terminal = terminal
optimize-once initial = initial
optimize-once (curry f) = curry (optimize-once f)
optimize-once apply = apply
optimize-once fold = fold
optimize-once unfold = unfold
optimize-once arr = arr

------------------------------------------------------------------------
-- Fixed-point optimization (bounded iteration)
------------------------------------------------------------------------

-- | Optimize with bounded iteration
--
-- Applies optimize-once repeatedly up to n times.
-- In practice, a small bound (e.g., 10) is sufficient.
--
optimize-n : ∀ {A B} → ℕ → IR ∞ A B → IR ∞ A B
optimize-n zero ir = ir
optimize-n (suc n) ir = optimize-n n (optimize-once ir)

-- | Main optimizer entry point
--
-- Uses a fixed bound of 10 iterations.
-- This is sufficient for most practical programs.
--
optimize : ∀ {A B} → IR ∞ A B → IR ∞ A B
optimize = optimize-n 10
