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
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Equality decision for Types (needed for pattern matching)
------------------------------------------------------------------------

_≟Type_ : (A B : Type) → Dec (A ≡ B)
Unit ≟Type Unit = yes refl
Unit ≟Type Void = no (λ ())
Unit ≟Type (_ * _) = no (λ ())
Unit ≟Type (_ + _) = no (λ ())
Unit ≟Type (_ ⇒ _) = no (λ ())
Unit ≟Type (Eff _ _) = no (λ ())
Unit ≟Type (Fix _) = no (λ ())
Void ≟Type Unit = no (λ ())
Void ≟Type Void = yes refl
Void ≟Type (_ * _) = no (λ ())
Void ≟Type (_ + _) = no (λ ())
Void ≟Type (_ ⇒ _) = no (λ ())
Void ≟Type (Eff _ _) = no (λ ())
Void ≟Type (Fix _) = no (λ ())
(A * B) ≟Type Unit = no (λ ())
(A * B) ≟Type Void = no (λ ())
(A * B) ≟Type (C * D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(A * B) ≟Type (_ + _) = no (λ ())
(A * B) ≟Type (_ ⇒ _) = no (λ ())
(A * B) ≟Type (Eff _ _) = no (λ ())
(A * B) ≟Type (Fix _) = no (λ ())
(A + B) ≟Type Unit = no (λ ())
(A + B) ≟Type Void = no (λ ())
(A + B) ≟Type (_ * _) = no (λ ())
(A + B) ≟Type (C + D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(A + B) ≟Type (_ ⇒ _) = no (λ ())
(A + B) ≟Type (Eff _ _) = no (λ ())
(A + B) ≟Type (Fix _) = no (λ ())
(A ⇒ B) ≟Type Unit = no (λ ())
(A ⇒ B) ≟Type Void = no (λ ())
(A ⇒ B) ≟Type (_ * _) = no (λ ())
(A ⇒ B) ≟Type (_ + _) = no (λ ())
(A ⇒ B) ≟Type (C ⇒ D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(A ⇒ B) ≟Type (Eff _ _) = no (λ ())
(A ⇒ B) ≟Type (Fix _) = no (λ ())
(Eff A B) ≟Type Unit = no (λ ())
(Eff A B) ≟Type Void = no (λ ())
(Eff A B) ≟Type (_ * _) = no (λ ())
(Eff A B) ≟Type (_ + _) = no (λ ())
(Eff A B) ≟Type (_ ⇒ _) = no (λ ())
(Eff A B) ≟Type (Eff C D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(Eff A B) ≟Type (Fix _) = no (λ ())
(Fix F) ≟Type Unit = no (λ ())
(Fix F) ≟Type Void = no (λ ())
(Fix F) ≟Type (_ * _) = no (λ ())
(Fix F) ≟Type (_ + _) = no (λ ())
(Fix F) ≟Type (_ ⇒ _) = no (λ ())
(Fix F) ≟Type (Eff _ _) = no (λ ())
(Fix F) ≟Type (Fix G) with F ≟Type G
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })

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
optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C

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
-- Applies eta law: ⟨ fst , snd ⟩ = id
--
optimize-pair : ∀ {A B C} → IR C A → IR C B → IR C (A * B)
optimize-pair (fst {A} {B}) (snd {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = id
... | _        | _        = ⟨ fst , snd ⟩
optimize-pair f g = ⟨ f , g ⟩

------------------------------------------------------------------------
-- Optimizer: Simplify case
------------------------------------------------------------------------

-- | Optimize a case
--
-- Applies eta law: [ inl , inr ] = id
--
optimize-case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C
optimize-case (inl {A} {B}) (inr {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = id
... | _        | _        = [ inl , inr ]
optimize-case f g = [ f , g ]

------------------------------------------------------------------------
-- Optimizer: Full recursive optimization
------------------------------------------------------------------------

-- | Single optimization pass
--
-- Recursively optimize all subterms, then apply simplifications.
--
optimize-once : ∀ {A B} → IR A B → IR A B
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
optimize-n : ∀ {A B} → ℕ → IR A B → IR A B
optimize-n zero ir = ir
optimize-n (suc n) ir = optimize-n n (optimize-once ir)

-- | Main optimizer entry point
--
-- Uses a fixed bound of 10 iterations.
-- This is sufficient for most practical programs.
--
optimize : ∀ {A B} → IR A B → IR A B
optimize = optimize-n 10
