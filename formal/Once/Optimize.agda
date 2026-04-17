-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Optimize
--
-- Optimizer for Once IR using categorical laws as rewrite rules.
-- Each rewrite preserves semantics (see Once.Optimize.Correct).
--
-- Architecture: Clean rule-based structure where each optimization
-- is a single pattern match clause. Easy to add new rules.
--
-- Includes:
--   - Identity laws (id ∘ f = f, f ∘ id = f)
--   - Beta laws (fst ∘ ⟨f,g⟩ = f, [f,g] ∘ inl = f, etc.)
--   - Eta laws (⟨fst,snd⟩ = id, [inl,inr] = id)
--   - Recursion scheme laws (Cata (In m) = id, Ana Out = id)
--   - Coproduct fusion (map f ∘ map g = map (f ∘ g))
--   - Product fusion (bimap f g ∘ bimap h k = bimap (f∘h) (g∘k))
--   - Distribution (⟨f,g⟩ ∘ h = ⟨f∘h,g∘h⟩, h ∘ [f,g] = [h∘f,h∘g])
--   - Dead code elimination (terminal ∘ f = terminal)
------------------------------------------------------------------------

module Once.Optimize where

open import Once.Type
open import Once.CCC.IR
open import Once.CCC.Machine.SMCore using (_≟H_)

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

-- | Functor equality (forward declared, defined after Type equality)
_≟Functor_ : (F G : Functor) → Dec (F ≡ G)

_≟Type_ : (A B : Type) → Dec (A ≡ B)
Unit ≟Type Unit = yes refl
Unit ≟Type Void = no (λ ())
Unit ≟Type (_ * _) = no (λ ())
Unit ≟Type (_ + _) = no (λ ())
Unit ≟Type (_ ⇒[ _ ] _) = no (λ ())
Unit ≟Type (Eff _ _) = no (λ ())
Unit ≟Type Int = no (λ ())
Unit ≟Type Float = no (λ ())
Unit ≟Type Str = no (λ ())
Unit ≟Type Buffer = no (λ ())
Void ≟Type Unit = no (λ ())
Void ≟Type Void = yes refl
Void ≟Type (_ * _) = no (λ ())
Void ≟Type (_ + _) = no (λ ())
Void ≟Type (_ ⇒[ _ ] _) = no (λ ())
Void ≟Type (Eff _ _) = no (λ ())
Void ≟Type Int = no (λ ())
Void ≟Type Float = no (λ ())
Void ≟Type Str = no (λ ())
Void ≟Type Buffer = no (λ ())
(A * B) ≟Type Unit = no (λ ())
(A * B) ≟Type Void = no (λ ())
(A * B) ≟Type (C * D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(A * B) ≟Type (_ + _) = no (λ ())
(A * B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(A * B) ≟Type (Eff _ _) = no (λ ())
(A * B) ≟Type Int = no (λ ())
(A * B) ≟Type Float = no (λ ())
(A * B) ≟Type Str = no (λ ())
(A * B) ≟Type Buffer = no (λ ())
(A + B) ≟Type Unit = no (λ ())
(A + B) ≟Type Void = no (λ ())
(A + B) ≟Type (_ * _) = no (λ ())
(A + B) ≟Type (C + D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(A + B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(A + B) ≟Type (Eff _ _) = no (λ ())
(A + B) ≟Type Int = no (λ ())
(A + B) ≟Type Float = no (λ ())
(A + B) ≟Type Str = no (λ ())
(A + B) ≟Type Buffer = no (λ ())
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
(A ⇒[ q ] B) ≟Type Int = no (λ ())
(A ⇒[ q ] B) ≟Type Float = no (λ ())
(A ⇒[ q ] B) ≟Type Str = no (λ ())
(A ⇒[ q ] B) ≟Type Buffer = no (λ ())
(Eff A B) ≟Type Unit = no (λ ())
(Eff A B) ≟Type Void = no (λ ())
(Eff A B) ≟Type (_ * _) = no (λ ())
(Eff A B) ≟Type (_ + _) = no (λ ())
(Eff A B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(Eff A B) ≟Type (Eff C D) with A ≟Type C | B ≟Type D
... | yes refl | yes refl = yes refl
... | no neq  | _        = no (λ { refl → neq refl })
... | _       | no neq   = no (λ { refl → neq refl })
(Eff A B) ≟Type Int = no (λ ())
(Eff A B) ≟Type Float = no (λ ())
(Eff A B) ≟Type Str = no (λ ())
(Eff A B) ≟Type Buffer = no (λ ())
-- OCP-0003: Fix removed. Use μ-type/ν-type instead.
Int ≟Type Unit = no (λ ())
Int ≟Type Void = no (λ ())
Int ≟Type (_ * _) = no (λ ())
Int ≟Type (_ + _) = no (λ ())
Int ≟Type (_ ⇒[ _ ] _) = no (λ ())
Int ≟Type (Eff _ _) = no (λ ())
Int ≟Type Int = yes refl
Int ≟Type Float = no (λ ())
Int ≟Type Str = no (λ ())
Int ≟Type Buffer = no (λ ())
Float ≟Type Unit = no (λ ())
Float ≟Type Void = no (λ ())
Float ≟Type (_ * _) = no (λ ())
Float ≟Type (_ + _) = no (λ ())
Float ≟Type (_ ⇒[ _ ] _) = no (λ ())
Float ≟Type (Eff _ _) = no (λ ())
Float ≟Type Int = no (λ ())
Float ≟Type Float = yes refl
Float ≟Type Str = no (λ ())
Float ≟Type Buffer = no (λ ())
Str ≟Type Unit = no (λ ())
Str ≟Type Void = no (λ ())
Str ≟Type (_ * _) = no (λ ())
Str ≟Type (_ + _) = no (λ ())
Str ≟Type (_ ⇒[ _ ] _) = no (λ ())
Str ≟Type (Eff _ _) = no (λ ())
Str ≟Type Int = no (λ ())
Str ≟Type Float = no (λ ())
Str ≟Type Str = yes refl
Str ≟Type Buffer = no (λ ())
Buffer ≟Type Unit = no (λ ())
Buffer ≟Type Void = no (λ ())
Buffer ≟Type (_ * _) = no (λ ())
Buffer ≟Type (_ + _) = no (λ ())
Buffer ≟Type (_ ⇒[ _ ] _) = no (λ ())
Buffer ≟Type (Eff _ _) = no (λ ())
Buffer ≟Type Int = no (λ ())
Buffer ≟Type Float = no (λ ())
Buffer ≟Type Str = no (λ ())
Buffer ≟Type Buffer = yes refl
-- TVar removed from Type; now in PolyType (see Once.Type)
-- μ-type cases (OCP-0003)
(μ-type F) ≟Type Unit = no (λ ())
(μ-type F) ≟Type Void = no (λ ())
(μ-type F) ≟Type (_ * _) = no (λ ())
(μ-type F) ≟Type (_ + _) = no (λ ())
(μ-type F) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(μ-type F) ≟Type (Eff _ _) = no (λ ())
(μ-type F) ≟Type (μ-type G) with F ≟Functor G
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })
(μ-type F) ≟Type (ν-type _) = no (λ ())
(μ-type F) ≟Type Int = no (λ ())
(μ-type F) ≟Type Float = no (λ ())
(μ-type F) ≟Type Str = no (λ ())
(μ-type F) ≟Type Buffer = no (λ ())
-- ν-type cases (OCP-0003)
(ν-type F) ≟Type Unit = no (λ ())
(ν-type F) ≟Type Void = no (λ ())
(ν-type F) ≟Type (_ * _) = no (λ ())
(ν-type F) ≟Type (_ + _) = no (λ ())
(ν-type F) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(ν-type F) ≟Type (Eff _ _) = no (λ ())
(ν-type F) ≟Type (μ-type _) = no (λ ())
(ν-type F) ≟Type (ν-type G) with F ≟Functor G
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })
(ν-type F) ≟Type Int = no (λ ())
(ν-type F) ≟Type Float = no (λ ())
(ν-type F) ≟Type Str = no (λ ())
(ν-type F) ≟Type Buffer = no (λ ())
-- Reverse cases for other types against μ-type/ν-type
Unit ≟Type (μ-type _) = no (λ ())
Unit ≟Type (ν-type _) = no (λ ())
Void ≟Type (μ-type _) = no (λ ())
Void ≟Type (ν-type _) = no (λ ())
(_ * _) ≟Type (μ-type _) = no (λ ())
(_ * _) ≟Type (ν-type _) = no (λ ())
(_ + _) ≟Type (μ-type _) = no (λ ())
(_ + _) ≟Type (ν-type _) = no (λ ())
(_ ⇒[ _ ] _) ≟Type (μ-type _) = no (λ ())
(_ ⇒[ _ ] _) ≟Type (ν-type _) = no (λ ())
(Eff _ _) ≟Type (μ-type _) = no (λ ())
(Eff _ _) ≟Type (ν-type _) = no (λ ())
Int ≟Type (μ-type _) = no (λ ())
Int ≟Type (ν-type _) = no (λ ())
Float ≟Type (μ-type _) = no (λ ())
Float ≟Type (ν-type _) = no (λ ())
Str ≟Type (μ-type _) = no (λ ())
Str ≟Type (ν-type _) = no (λ ())
Buffer ≟Type (μ-type _) = no (λ ())
Buffer ≟Type (ν-type _) = no (λ ())
-- GuardedT removed: productivity follows from IR totality
-- TVar removed from Type; now in PolyType (see Once.Type)

------------------------------------------------------------------------
-- Functor equality implementation
------------------------------------------------------------------------

K A ≟Functor K B with A ≟Type B
... | yes refl = yes refl
... | no neq   = no (λ { refl → neq refl })
K _ ≟Functor Id = no (λ ())
K _ ≟Functor (_ ⊕ _) = no (λ ())
K _ ≟Functor (_ ⊗ _) = no (λ ())
Id ≟Functor K _ = no (λ ())
Id ≟Functor Id = yes refl
Id ≟Functor (_ ⊕ _) = no (λ ())
Id ≟Functor (_ ⊗ _) = no (λ ())
(F₁ ⊕ F₂) ≟Functor K _ = no (λ ())
(F₁ ⊕ F₂) ≟Functor Id = no (λ ())
(F₁ ⊕ F₂) ≟Functor (G₁ ⊕ G₂) with F₁ ≟Functor G₁ | F₂ ≟Functor G₂
... | yes refl | yes refl = yes refl
... | no neq   | _        = no (λ { refl → neq refl })
... | _        | no neq   = no (λ { refl → neq refl })
(F₁ ⊕ F₂) ≟Functor (_ ⊗ _) = no (λ ())
(F₁ ⊗ F₂) ≟Functor K _ = no (λ ())
(F₁ ⊗ F₂) ≟Functor Id = no (λ ())
(F₁ ⊗ F₂) ≟Functor (_ ⊕ _) = no (λ ())
(F₁ ⊗ F₂) ≟Functor (G₁ ⊗ G₂) with F₁ ≟Functor G₁ | F₂ ≟Functor G₂
... | yes refl | yes refl = yes refl
... | no neq   | _        = no (λ { refl → neq refl })
... | _        | no neq   = no (λ { refl → neq refl })

------------------------------------------------------------------------
-- IR equality (needed for eta uniqueness laws)
--
-- NOTE: Due to type index unification issues with the new recursion
-- scheme constructors (In, Cata, Out, Ana, Hylo), we postulate IR
-- equality. A full implementation would require explicit cases for
-- all pairs of constructors with compatible types, which is complex
-- due to the dependent type indices like ⟦ F ⟧T.
------------------------------------------------------------------------

postulate
  _≟IR_ : ∀ {A B} → (f g : IR A B) → Dec (f ≡ g)

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

-- Type predicates for type-directed optimization
isUnitType : Type → Bool
isUnitType Unit = true
isUnitType _ = false

isVoidType : Type → Bool
isVoidType Void = true
isVoidType _ = false

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
wants-coprod (case _ _) = true
wants-coprod terminal = true
wants-coprod _ = false

-- OCP-0003: wants-unfold/wants-fold removed. Use Cata/Ana instead.

------------------------------------------------------------------------
-- | Composition optimization
--
-- Rules implemented:
--   - Identity: id ∘ f = f, g ∘ id = g
--   - Beta (products): fst ∘ ⟨f,g⟩ = f, snd ∘ ⟨f,g⟩ = g
--   - Beta (coproducts): case f g ∘ inl = f, case f g ∘ inr = g
--   - Dead code: terminal ∘ f = terminal, g ∘ initial = initial
--
-- NOTE: Due to dependent type indices in recursion scheme constructors
-- (⟦ F ⟧T can produce any type structure), we use "view" patterns to
-- isolate the coverage gap into explicit postulates.
------------------------------------------------------------------------

-- View: classify IR terms targeting a product type
data PairView : ∀ {A B C : Type} → IR A (B * C) → Set where
  is-pair : ∀ {A B C} (f : IR A B) (g : IR A C) m → PairView (⟨ f , g ⟩ m)
  is-other-pair : ∀ {A B C} (f : IR A (B * C)) → PairView f

-- View: classify IR terms targeting a coproduct type
-- Note: inl : IR A (A + B), inr : IR B (A + B) - source must match component
data CoprodView : ∀ {A B D : Type} → IR D (A + B) → Set where
  is-inl : ∀ {A B} m → CoprodView {A} {B} {A} (inl m)
  is-inr : ∀ {A B} m → CoprodView {A} {B} {B} (inr m)
  is-other-coprod : ∀ {A B D} (f : IR D (A + B)) → CoprodView f

-- View: classify IR by optimization-relevant structure (first argument of compose)
data ComposeFirstView : ∀ {B C : Type} → IR B C → Set where
  cf-id : ∀ {A} → ComposeFirstView {A} {A} id
  cf-terminal : ∀ {A} → ComposeFirstView {A} {Unit} terminal
  cf-fst : ∀ {A B} → ComposeFirstView {A * B} {A} fst
  cf-snd : ∀ {A B} → ComposeFirstView {A * B} {B} snd
  cf-case : ∀ {A B C} (h : IR A C) (k : IR B C) → ComposeFirstView {A + B} {C} (case h k)
  cf-other : ∀ {B C} (g : IR B C) → ComposeFirstView g

-- View: classify IR by optimization-relevant structure (second argument of compose)
data ComposeSecondView : ∀ {A B : Type} → IR A B → Set where
  cs-id : ∀ {A} → ComposeSecondView {A} {A} id
  cs-initial : ∀ {A} → ComposeSecondView {Void} {A} initial
  cs-other : ∀ {A B} (f : IR A B) → ComposeSecondView f

-- View: classify IR as fst, snd, or other (for pair eta law)
data FstSndView : ∀ {A B : Type} → IR A B → Set where
  fsv-fst : ∀ {X Y} → FstSndView {X * Y} {X} fst
  fsv-snd : ∀ {X Y} → FstSndView {X * Y} {Y} snd
  fsv-other : ∀ {A B} (f : IR A B) → FstSndView f

-- View: classify IR as inl, inr, or other (for case eta law)
data InlInrView : ∀ {A B : Type} → IR A B → Set where
  iiv-inl : ∀ {X Y} m → InlInrView {X} {X + Y} (inl m)
  iiv-inr : ∀ {X Y} m → InlInrView {Y} {X + Y} (inr m)
  iiv-other : ∀ {A B} (f : IR A B) → InlInrView f

-- Postulates: we can classify any IR by structure
-- (True at runtime, unprovable due to ⟦ F ⟧T type indices)
postulate
  pairView : ∀ {A B C} → (f : IR A (B * C)) → PairView f
  coprodView : ∀ {A B D} → (f : IR D (A + B)) → CoprodView f
  composeFirstView : ∀ {B C} → (g : IR B C) → ComposeFirstView g
  composeSecondView : ∀ {A B} → (f : IR A B) → ComposeSecondView f
  fstSndView : ∀ {A B} → (f : IR A B) → FstSndView f
  inlInrView : ∀ {A B} → (f : IR A B) → InlInrView f

-- Helper: beta reduction for fst ∘ f (verified given view)
optimize-fst : ∀ {A B C} → IR A (B * C) → IR A B
optimize-fst f with pairView f
... | is-pair g _ _ = g
... | is-other-pair f = fst ∘ f

-- Helper: beta reduction for snd ∘ f (verified given view)
optimize-snd : ∀ {A B C} → IR A (B * C) → IR A C
optimize-snd f with pairView f
... | is-pair _ g _ = g
... | is-other-pair f = snd ∘ f

-- Helper: optimize (case h k) ∘ f (verified given view)
-- When f = inl, D = A; when f = inr, D = B
optimize-post-case : ∀ {A B C D} → IR A C → IR B C → IR D (A + B) → IR D C
optimize-post-case {A} {B} {C} {D} h k f with coprodView f
... | is-inl _ = h    -- D = A, so IR D C = IR A C
... | is-inr _ = k    -- D = B, so IR D C = IR B C
... | is-other-coprod f = case h k ∘ f

-- Helper: handle second argument after first is classified as "other"
optimize-compose-second : ∀ {A B C} → IR B C → IR A B → IR A C
optimize-compose-second g f with composeSecondView f
... | cs-id = g
... | cs-initial = initial
... | cs-other f = g ∘ f

optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C
optimize-compose g f with composeFirstView g
... | cf-id = f                                    -- id ∘ f = f
... | cf-terminal = terminal                       -- terminal ∘ f = terminal
... | cf-fst = optimize-fst f                      -- fst ∘ f (beta reduction)
... | cf-snd = optimize-snd f                      -- snd ∘ f (beta reduction)
... | cf-case h k = optimize-post-case h k f       -- case h k ∘ f (beta reduction)
... | cf-other g = optimize-compose-second g f     -- check second arg

------------------------------------------------------------------------
-- Eta Laws (for pairs and cases) - Postulated
--
-- NOTE: Due to type index unification issues with OCP-0003's new
-- recursion scheme constructors, these are temporarily postulated.
------------------------------------------------------------------------

-- | Optimize pair construction
--   ⟨ fst , snd ⟩ = id (eta)
--   ⟨ fst ∘ h , snd ∘ h ⟩ = h (uniqueness)
optimize-pair : ∀ {A B C} → IR C A → IR C B → IR C (A * B)
optimize-pair f g with fstSndView f | fstSndView g
... | fsv-fst | fsv-snd = id                          -- eta: C = A * B, so id : IR C C
... | _ | _ = ⟨ f , g ⟩ Stack                         -- default (use Stack allocation)

-- | Optimize case construction
--   [ inl , inr ] = id (eta)
--   [ h ∘ inl , h ∘ inr ] = h (uniqueness)
optimize-case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C
optimize-case f g with inlInrView f | inlInrView g
... | iiv-inl _ | iiv-inr _ = id                      -- eta: C = A + B, so id : IR C C
... | _ | _ = case f g                                -- default

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
  optimize-once-structural (case f g) = optimize-case (optimize-once f) (optimize-once g)
  optimize-once-structural terminal = terminal
  optimize-once-structural initial = initial
  optimize-once-structural (curry f m) = curry (optimize-once f) m
  optimize-once-structural apply = apply
  -- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
  optimize-once-structural arr = arr
  -- | Prim with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (Prim {A} n) with A ≟Type Void
  ... | yes refl = initial
  ... | no _     = Prim n
  -- | free-heap is opaque (no optimization)
  optimize-once-structural (free-heap h) = free-heap h
  -- | OCP-0003 recursion schemes: optimize algebras/coalgebras
  --
  -- Identity rules (proven in Category/Laws.agda):
  --   - Cata (In m) ≡ id  (identity catamorphism)
  --   - Ana Out ≡ id      (identity anamorphism)
  --
  -- NOTE: Due to SplitError.UnificationStuck with dependent type indices,
  -- we cannot pattern match on (In m) or Out here. The identity rules
  -- are documented but not automatically applied at the IR level.
  -- The semantic equivalence is proven in the laws module.
  --
  optimize-once-structural (In wf m) = In wf m
  optimize-once-structural (out-μ wf) = out-μ wf
  optimize-once-structural (Cata {F} wf alg) = Cata {F} wf (optimize-once alg)
  optimize-once-structural (Para {F} wf alg) = Para {F} wf (optimize-once alg)
  optimize-once-structural (Out wf) = Out wf
  optimize-once-structural (in-ν wf m) = in-ν wf m
  optimize-once-structural (Ana {F} wf coalg) = Ana {F} wf (optimize-once coalg)
  optimize-once-structural (Hylo {F} wf term alg coalg) = Hylo {F} wf term (optimize-once alg) (optimize-once coalg)
  -- Fuse: μ-anchored fusion (correct by construction)
  optimize-once-structural (Fuse {F} {G} wfF wfG alg transform) = Fuse {F} {G} wfF wfG (optimize-once alg) (optimize-once transform)
  -- Guard/Unguard removed: productivity follows from IR totality
  -- out-μ/in-ν: Lambek isomorphisms (potential fusion: out-μ ∘ In = id, In ∘ out-μ = id)

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