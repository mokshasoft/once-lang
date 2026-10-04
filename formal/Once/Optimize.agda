-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Once.IR
open import Once.Float.Decimal using (Decimal; decimalOf; round)
import Once.IRTy as II
open import Once.CCC.Machine.SMCore using (_≟H_)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟String_)
open import Once.CanonicalName using (CanonicalName; _≟ᶜ_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)

------------------------------------------------------------------------
-- Equality decision (needed for eta laws)
--
-- 0.86 stage G: `_≟AllocMode_` stood here and is DELETED. It existed so
-- `≟IRH-diag` could compare the modes of two IR nodes; with all six
-- constructors mode-free there is nothing left to compare, and every clause
-- that used it collapsed to the functor/well-formedness comparison alone.
------------------------------------------------------------------------

-- Plan 0.99: Functor/Type equality is `Once.Type.DecEq`'s — the one copy.
open import Once.Type.DecEq using (_≟T_; _≟F_)

------------------------------------------------------------------------
-- IR heads (the eta rules below dispatch on them)
--
-- D271: a decider `_≟IR_ : Dec (f ≡ g)` stood here. No live module used it
-- (only red optimizer islands), and it could not be honest: a SigOp's
-- `pureV` semantics is a function, so `SigOpInfo` equality is undecidable —
-- it rested on `sigOpInfo-name-coherence` (equal names ⇒ equal records,
-- `⊥`) and on the postulate `≟const-irrelevant`. Deleted with both.
------------------------------------------------------------------------

-- IR head discriminator.
data IRHead : Set where
  h-id h-∘ h-⟨,⟩ h-fst h-snd h-inl h-inr h-case
    h-terminal h-initial h-curry h-apply h-arr
    h-In h-out-μ h-Cata h-Out h-in-ν h-Ana
    h-SigOp h-const h-Call : IRHead

-- Decidable equality for IRHead via tag-to-ℕ conversion. Plan 0.5 Phase B
-- / F1. Uses stdlib's `Data.Nat._≟_` for the actual comparison;
-- `headTag-inj` recovers the IRHead equation from tag equality. Adding
-- a new IRHead constructor costs 2 lines (headTag clause + headTag-inj
-- diagonal).
headTag : IRHead → ℕ
headTag h-id        = 0
headTag h-∘         = 1
headTag h-⟨,⟩       = 2
headTag h-fst       = 3
headTag h-snd       = 4
headTag h-inl       = 5
headTag h-inr       = 6
headTag h-case      = 7
headTag h-terminal  = 8
headTag h-initial   = 9
headTag h-curry     = 10
headTag h-apply     = 11
headTag h-arr       = 12
headTag h-In        = 14
headTag h-out-μ     = 15
headTag h-Cata      = 16
headTag h-Out       = 18
headTag h-in-ν      = 19
headTag h-Ana       = 20
headTag h-SigOp      = 24
headTag h-const      = 25
headTag h-Call       = 26

-- Injectivity: if tags agree, the constructors agree. 24 diagonals;
-- off-diagonal cases are automatically covered by Agda because their
-- premise (a specific ℕ equation like `0 ≡ 1`) is absurd.
headTag-inj : ∀ (h₁ h₂ : IRHead) → headTag h₁ ≡ headTag h₂ → h₁ ≡ h₂
headTag-inj h-id        h-id        _ = refl
headTag-inj h-∘         h-∘         _ = refl
headTag-inj h-⟨,⟩       h-⟨,⟩       _ = refl
headTag-inj h-fst       h-fst       _ = refl
headTag-inj h-snd       h-snd       _ = refl
headTag-inj h-inl       h-inl       _ = refl
headTag-inj h-inr       h-inr       _ = refl
headTag-inj h-case      h-case      _ = refl
headTag-inj h-terminal  h-terminal  _ = refl
headTag-inj h-initial   h-initial   _ = refl
headTag-inj h-curry     h-curry     _ = refl
headTag-inj h-apply     h-apply     _ = refl
headTag-inj h-arr       h-arr       _ = refl
headTag-inj h-In        h-In        _ = refl
headTag-inj h-out-μ     h-out-μ     _ = refl
headTag-inj h-Cata      h-Cata      _ = refl
headTag-inj h-Out       h-Out       _ = refl
headTag-inj h-in-ν      h-in-ν      _ = refl
headTag-inj h-Ana       h-Ana       _ = refl
headTag-inj h-SigOp      h-SigOp      _ = refl
headTag-inj h-const      h-const      _ = refl
headTag-inj h-Call       h-Call       _ = refl

_≟IRHead_ : (h₁ h₂ : IRHead) → Dec (h₁ ≡ h₂)
h₁ ≟IRHead h₂ with headTag h₁ Data.Nat.Properties.≟ headTag h₂
... | yes eq = yes (headTag-inj h₁ h₂ eq)
... | no  ne = no (λ heq → ne (cong headTag heq))

ir-head : ∀ {A B} → IR A B → IRHead
ir-head id = h-id
ir-head (_ ∘ _) = h-∘
ir-head (⟨ _ , _ ⟩) = h-⟨,⟩
ir-head fst = h-fst
ir-head snd = h-snd
ir-head inl = h-inl
ir-head inr = h-inr
ir-head (case _ _) = h-case
ir-head terminal = h-terminal
ir-head initial = h-initial
ir-head (curry _) = h-curry
ir-head apply = h-apply
ir-head (In _) = h-In
ir-head (out-μ _) = h-out-μ
ir-head (Cata _ _) = h-Cata
ir-head (Out _) = h-Out
ir-head (in-ν _) = h-in-ν
ir-head (Ana _ _) = h-Ana
ir-head (SigOp _) = h-SigOp
ir-head (const _ _) = h-const
ir-head (Call _) = h-Call

------------------------------------------------------------------------
-- Helper: Check for Void types (enables dead code elimination)
------------------------------------------------------------------------

-- Decidable-to-Bool conversion (avoids importing Relation.Nullary.Decidable).
dec-to-bool : ∀ {ℓ} {P : Set ℓ} → Dec P → Bool
dec-to-bool (yes _) = true
dec-to-bool (no _)  = false

-- | Check if a type is Void
is-Void : Type → Bool
is-Void Unit         = false
is-Void Void         = true
is-Void (_ * _)      = false
is-Void (_ + _)      = false
is-Void (_ ⇒[ _ ] _) = false
is-Void (μ-type _)   = false
is-Void (ν-type _ _)   = false
is-Void Int          = false
is-Void Float        = false
is-Void (rigid _ _)  = false

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
isUnitType Unit         = true
isUnitType Void         = false
isUnitType (_ * _)      = false
isUnitType (_ + _)      = false
isUnitType (_ ⇒[ _ ] _) = false
isUnitType (μ-type _)   = false
isUnitType (ν-type _ _)   = false
isUnitType Int          = false
isUnitType Float        = false
isUnitType (rigid _ _)  = false

isVoidType : Type → Bool
isVoidType Unit         = false
isVoidType Void         = true
isVoidType (_ * _)      = false
isVoidType (_ + _)      = false
isVoidType (_ ⇒[ _ ] _) = false
isVoidType (μ-type _)   = false
isVoidType (ν-type _ _)   = false
isVoidType Int          = false
isVoidType Float        = false
isVoidType (rigid _ _)  = false

-- IR predicates: use ir-head head-discriminator + decidable IRHead equality
-- to avoid enumerating all 24 IR constructors per predicate.
is-fst?      : ∀ {A B} → IR A B → Bool
is-fst?      f = dec-to-bool (ir-head f ≟IRHead h-fst)

is-snd?      : ∀ {A B} → IR A B → Bool
is-snd?      f = dec-to-bool (ir-head f ≟IRHead h-snd)

is-terminal? : ∀ {A B} → IR A B → Bool
is-terminal? f = dec-to-bool (ir-head f ≟IRHead h-terminal)

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
wants-coprod f =
  dec-to-bool (ir-head f ≟IRHead h-case) ∨
  dec-to-bool (ir-head f ≟IRHead h-terminal)

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
-- (⟦ F ⟧T can produce any type structure), we use "view" patterns
-- (see below, implemented via the generic-codomain trick)
-- to classify targets.
------------------------------------------------------------------------

-- View: classify IR terms targeting a product type
data PairView : ∀ {A B C : IRTy} → IR A (B * C) → Set where
  is-pair : ∀ {A B C} (f : IR A B) (g : IR A C) → PairView ⟨ f , g ⟩
  is-other-pair : ∀ {A B C} (f : IR A (B * C)) → PairView f

-- View: classify IR terms targeting a coproduct type
-- Note: inl : IR A (A + B), inr : IR B (A + B) - source must match component
data CoprodView : ∀ {A B D : IRTy} → IR D (A + B) → Set where
  is-inl : ∀ {A B} → CoprodView {A} {B} {A} inl
  is-inr : ∀ {A B} → CoprodView {A} {B} {B} inr
  is-other-coprod : ∀ {A B D} (f : IR D (A + B)) → CoprodView f

-- View: classify IR by optimization-relevant structure (first argument of compose)
data ComposeFirstView : ∀ {B C : IRTy} → IR B C → Set where
  cf-id : ∀ {A} → ComposeFirstView {A} {A} id
  cf-terminal : ∀ {A} → ComposeFirstView {A} {Unit} terminal
  cf-fst : ∀ {A B} → ComposeFirstView {A * B} {A} fst
  cf-snd : ∀ {A B} → ComposeFirstView {A * B} {B} snd
  cf-case : ∀ {A B C} (h : IR A C) (k : IR B C) → ComposeFirstView {A + B} {C} (case h k)
  cf-other : ∀ {B C} (g : IR B C) → ComposeFirstView g

-- View: classify IR by optimization-relevant structure (second argument of compose)
data ComposeSecondView : ∀ {A B : IRTy} → IR A B → Set where
  cs-id : ∀ {A} → ComposeSecondView {A} {A} id
  cs-initial : ∀ {A} → ComposeSecondView {Void} {A} initial
  cs-other : ∀ {A B} (f : IR A B) → ComposeSecondView f

-- View: classify IR as fst, snd, or other (for pair eta law)
data FstSndView : ∀ {A B : IRTy} → IR A B → Set where
  fsv-fst : ∀ {X Y} → FstSndView {X * Y} {X} fst
  fsv-snd : ∀ {X Y} → FstSndView {X * Y} {Y} snd
  fsv-other : ∀ {A B} (f : IR A B) → FstSndView f

-- View: classify IR as inl, inr, or other (for case eta law)
data InlInrView : ∀ {A B : IRTy} → IR A B → Set where
  iiv-inl : ∀ {X Y} → InlInrView {X} {X + Y} inl
  iiv-inr : ∀ {X Y} → InlInrView {Y} {X + Y} inr
  iiv-other : ∀ {A B} (f : IR A B) → InlInrView f

------------------------------------------------------------------------
-- View implementations (OCP-0003 compliant)
--
-- The generic-codomain trick: for views constrained to a specific target
-- shape (B * C or A + B), we use a helper with a free codomain and an
-- equality proof. This avoids SplitError.UnificationStuck on constructors
-- with stuck type indices (out-μ : IR (μ-type F) (⟦ F ⟧T (μ-type F)),
-- get handled via `eq`-matching + subst; the refl cases cover concrete
-- constructors whose target unifies.
--
-- For views over fully-generic (A B) IRs (FstSndView, InlInrView,
-- ComposeFirstView, ComposeSecondView), direct pattern-matching works
-- without the trick.
------------------------------------------------------------------------

-- PairView: target is B * C (stuck unification for generic-output constructors).
-- Specific case first; catch-all handles every other constructor uniformly
-- via subst (plan 0.5 Phase A / F2).
pairView-gen : ∀ {A B'} (f : IR A B') → ∀ {B C} → (eq : B' ≡ B * C)
             → PairView {A} {B} {C} (subst (IR A) eq f)
pairView-gen ⟨ f , g ⟩ refl = is-pair f g
pairView-gen id              eq = is-other-pair (subst (IR _) eq id)
pairView-gen (f ∘ g)         eq = is-other-pair (subst (IR _) eq (f ∘ g))
pairView-gen fst             eq = is-other-pair (subst (IR _) eq fst)
pairView-gen snd             eq = is-other-pair (subst (IR _) eq snd)
pairView-gen inl             eq = is-other-pair (subst (IR _) eq inl)
pairView-gen inr             eq = is-other-pair (subst (IR _) eq inr)
pairView-gen (case f g)      eq = is-other-pair (subst (IR _) eq (case f g))
pairView-gen terminal        eq = is-other-pair (subst (IR _) eq terminal)
pairView-gen initial         eq = is-other-pair (subst (IR _) eq initial)
pairView-gen (curry f)       eq = is-other-pair (subst (IR _) eq (curry f))
pairView-gen apply           eq = is-other-pair (subst (IR _) eq apply)
pairView-gen (In wf)       eq = is-other-pair (subst (IR _) eq (In wf))
pairView-gen (out-μ wf)      eq = is-other-pair (subst (IR _) eq (out-μ wf))
pairView-gen (Cata wf alg)   eq = is-other-pair (subst (IR _) eq (Cata wf alg))
pairView-gen (Out wf)        eq = is-other-pair (subst (IR _) eq (Out wf))
pairView-gen (in-ν wf)     eq = is-other-pair (subst (IR _) eq (in-ν wf))
pairView-gen (Ana wf coalg)  eq = is-other-pair (subst (IR _) eq (Ana wf coalg))
pairView-gen (SigOp si)      eq = is-other-pair (subst (IR _) eq (SigOp si))
pairView-gen (Call f)       eq = is-other-pair (subst (IR _) eq (Call f))
pairView-gen (const p v) eq = is-other-pair (subst (IR _) eq (const p v))

pairView : ∀ {A B C} → (f : IR A (B * C)) → PairView f
pairView f = pairView-gen f refl

-- CoprodView: target is A + B (same stuck-unification pattern as PairView)
coprodView-gen : ∀ {D B'} (f : IR D B') → ∀ {A B} → (eq : B' ≡ A + B)
               → CoprodView {A} {B} {D} (subst (IR D) eq f)
coprodView-gen inl refl = is-inl
coprodView-gen inr refl = is-inr
coprodView-gen id              eq = is-other-coprod (subst (IR _) eq id)
coprodView-gen (f ∘ g)         eq = is-other-coprod (subst (IR _) eq (f ∘ g))
coprodView-gen (⟨ f , g ⟩)   eq = is-other-coprod (subst (IR _) eq (⟨ f , g ⟩))
coprodView-gen fst             eq = is-other-coprod (subst (IR _) eq fst)
coprodView-gen snd             eq = is-other-coprod (subst (IR _) eq snd)
coprodView-gen (case f g)      eq = is-other-coprod (subst (IR _) eq (case f g))
coprodView-gen terminal        eq = is-other-coprod (subst (IR _) eq terminal)
coprodView-gen initial         eq = is-other-coprod (subst (IR _) eq initial)
coprodView-gen (curry f)       eq = is-other-coprod (subst (IR _) eq (curry f))
coprodView-gen apply           eq = is-other-coprod (subst (IR _) eq apply)
coprodView-gen (In wf)       eq = is-other-coprod (subst (IR _) eq (In wf))
coprodView-gen (out-μ wf)      eq = is-other-coprod (subst (IR _) eq (out-μ wf))
coprodView-gen (Cata wf alg)   eq = is-other-coprod (subst (IR _) eq (Cata wf alg))
coprodView-gen (Out wf)        eq = is-other-coprod (subst (IR _) eq (Out wf))
coprodView-gen (in-ν wf)     eq = is-other-coprod (subst (IR _) eq (in-ν wf))
coprodView-gen (Ana wf coalg)  eq = is-other-coprod (subst (IR _) eq (Ana wf coalg))
coprodView-gen (SigOp si)      eq = is-other-coprod (subst (IR _) eq (SigOp si))
coprodView-gen (Call f)       eq = is-other-coprod (subst (IR _) eq (Call f))
coprodView-gen (const p v) eq = is-other-coprod (subst (IR _) eq (const p v))

coprodView : ∀ {A B D} → (f : IR D (A + B)) → CoprodView f
coprodView f = coprodView-gen f refl

-- ComposeFirstView: fully generic source and target. Specific cases
-- first, then catch-all; new IR constructors cost 0 lines per view
-- (plan 0.5 Phase A / F2).
-- View enumerations: every IR constructor handled explicitly. Specials
-- get their dedicated view tag; everything else returns the "-other" tag.
-- Adding a new IR constructor costs 4 lines (one per view).

composeFirstView : ∀ {B C} → (g : IR B C) → ComposeFirstView g
composeFirstView id              = cf-id
composeFirstView terminal        = cf-terminal
composeFirstView fst             = cf-fst
composeFirstView snd             = cf-snd
composeFirstView (case h k)      = cf-case h k
composeFirstView (g ∘ h)         = cf-other (g ∘ h)
composeFirstView (⟨ f , g ⟩)   = cf-other (⟨ f , g ⟩)
composeFirstView inl             = cf-other inl
composeFirstView inr             = cf-other inr
composeFirstView initial         = cf-other initial
composeFirstView (curry f)       = cf-other (curry f)
composeFirstView apply           = cf-other apply
composeFirstView (In wf)       = cf-other (In wf)
composeFirstView (out-μ wf)      = cf-other (out-μ wf)
composeFirstView (Cata wf alg)   = cf-other (Cata wf alg)
composeFirstView (Out wf)        = cf-other (Out wf)
composeFirstView (in-ν wf)     = cf-other (in-ν wf)
composeFirstView (Ana wf coalg)  = cf-other (Ana wf coalg)
composeFirstView (SigOp si)      = cf-other (SigOp si)
composeFirstView (Call f)       = cf-other (Call f)
composeFirstView (const p v) = cf-other (const p v)

composeSecondView : ∀ {A B} → (f : IR A B) → ComposeSecondView f
composeSecondView id             = cs-id
composeSecondView initial        = cs-initial
composeSecondView (f ∘ g)        = cs-other (f ∘ g)
composeSecondView (⟨ f , g ⟩)  = cs-other (⟨ f , g ⟩)
composeSecondView fst            = cs-other fst
composeSecondView snd            = cs-other snd
composeSecondView inl            = cs-other inl
composeSecondView inr            = cs-other inr
composeSecondView (case f g)     = cs-other (case f g)
composeSecondView terminal       = cs-other terminal
composeSecondView (curry f)      = cs-other (curry f)
composeSecondView apply          = cs-other apply
composeSecondView (In wf)      = cs-other (In wf)
composeSecondView (out-μ wf)     = cs-other (out-μ wf)
composeSecondView (Cata wf alg)  = cs-other (Cata wf alg)
composeSecondView (Out wf)       = cs-other (Out wf)
composeSecondView (in-ν wf)    = cs-other (in-ν wf)
composeSecondView (Ana wf coalg) = cs-other (Ana wf coalg)
composeSecondView (SigOp si)     = cs-other (SigOp si)
composeSecondView (Call f)       = cs-other (Call f)
composeSecondView (const p v) = cs-other (const p v)

fstSndView : ∀ {A B} → (f : IR A B) → FstSndView f
fstSndView fst             = fsv-fst
fstSndView snd             = fsv-snd
fstSndView id              = fsv-other id
fstSndView (f ∘ g)         = fsv-other (f ∘ g)
fstSndView (⟨ f , g ⟩)   = fsv-other (⟨ f , g ⟩)
fstSndView inl             = fsv-other inl
fstSndView inr             = fsv-other inr
fstSndView (case f g)      = fsv-other (case f g)
fstSndView terminal        = fsv-other terminal
fstSndView initial         = fsv-other initial
fstSndView (curry f)       = fsv-other (curry f)
fstSndView apply           = fsv-other apply
fstSndView (In wf)       = fsv-other (In wf)
fstSndView (out-μ wf)      = fsv-other (out-μ wf)
fstSndView (Cata wf alg)   = fsv-other (Cata wf alg)
fstSndView (Out wf)        = fsv-other (Out wf)
fstSndView (in-ν wf)     = fsv-other (in-ν wf)
fstSndView (Ana wf coalg)  = fsv-other (Ana wf coalg)
fstSndView (SigOp si)      = fsv-other (SigOp si)
fstSndView (Call f)       = fsv-other (Call f)
fstSndView (const p v) = fsv-other (const p v)

inlInrView : ∀ {A B} → (f : IR A B) → InlInrView f
inlInrView inl             = iiv-inl
inlInrView inr             = iiv-inr
inlInrView id              = iiv-other id
inlInrView (f ∘ g)         = iiv-other (f ∘ g)
inlInrView (⟨ f , g ⟩)   = iiv-other (⟨ f , g ⟩)
inlInrView fst             = iiv-other fst
inlInrView snd             = iiv-other snd
inlInrView (case f g)      = iiv-other (case f g)
inlInrView terminal        = iiv-other terminal
inlInrView initial         = iiv-other initial
inlInrView (curry f)       = iiv-other (curry f)
inlInrView apply           = iiv-other apply
inlInrView (In wf)       = iiv-other (In wf)
inlInrView (out-μ wf)      = iiv-other (out-μ wf)
inlInrView (Cata wf alg)   = iiv-other (Cata wf alg)
inlInrView (Out wf)        = iiv-other (Out wf)
inlInrView (in-ν wf)     = iiv-other (in-ν wf)
inlInrView (Ana wf coalg)  = iiv-other (Ana wf coalg)
inlInrView (SigOp si)      = iiv-other (SigOp si)
inlInrView (Call f)       = iiv-other (Call f)
inlInrView (const p v) = iiv-other (const p v)

-- Helper: beta reduction for fst ∘ f (verified given view)
-- | Does this IR contain an observable effect (a SigOp or a heap free)?
--
-- The degenerate optimizer rules (`B ≡ Unit → terminal`, `terminal ∘ f →
-- terminal`, `fst/snd ∘ ⟨g,h⟩ → g/h`) are sound ONLY at the VALUE level:
-- every `_ → Unit` morphism denotes `tt`, and a projection discards a
-- component — both fine for the value, but they DROP any observable SigOp
-- trace the discarded sub-term would emit (e.g. the exit syscall, a test
-- `emit`), so the binary silently exits 0. We gate those drops on this
-- predicate: an effectful sub-term is never dropped (it falls through to a
-- structural form that preserves it). (`Void`-source → `initial` stays
-- unconditional: a `Void`-source morphism is never invoked.)
has-effect? : ∀ {A B} → IR A B → Bool
has-effect? id              = false
has-effect? (g ∘ f)         = has-effect? g ∨ has-effect? f
has-effect? fst             = false
has-effect? snd             = false
has-effect? (⟨ f , g ⟩)   = has-effect? f ∨ has-effect? g
has-effect? inl             = false
has-effect? inr             = false
has-effect? (case f g)      = has-effect? f ∨ has-effect? g
has-effect? terminal        = false
has-effect? initial         = false
has-effect? (curry f)       = has-effect? f
-- `apply` invokes a closure that is only known at runtime; that closure may
-- contain any SigOp (e.g. an `exit`/`emit` action threaded through a thunk),
-- so an `apply` is conservatively treated as potentially effectful. This is
-- what stops the optimizer collapsing an effect-bearing action thunk
-- (`applyEff ∘ ⟨closure,x⟩ : _ → Unit`) to `terminal`.
has-effect? apply           = true
has-effect? (SigOp _)       = true
-- D245: a call runs its table entry, which may emit or halt.
has-effect? (Call _)        = true
has-effect? (const _ _)   = false
has-effect? (In _)        = false
has-effect? (out-μ _)       = false
has-effect? (Cata _ alg)    = has-effect? alg
has-effect? (Out _)         = false
has-effect? (in-ν _)      = false
has-effect? (Ana _ coalg)   = has-effect? coalg


optimize-fst : ∀ {A B C} → IR A (B * C) → IR A B
optimize-fst f with pairView f
... | is-pair g _ = g
... | is-other-pair f = fst ∘ f

-- Helper: beta reduction for snd ∘ f (verified given view)
optimize-snd : ∀ {A B C} → IR A (B * C) → IR A C
optimize-snd f with pairView f
... | is-pair _ g = g
... | is-other-pair f = snd ∘ f

-- Helper: optimize (case h k) ∘ f (verified given view)
-- When f = inl, D = A; when f = inr, D = B
optimize-post-case : ∀ {A B C D} → IR A C → IR B C → IR D (A + B) → IR D C
optimize-post-case {A} {B} {C} {D} h k f with coprodView f
... | is-inl   = h    -- D = A, so IR D C = IR A C
... | is-inr   = k    -- D = B, so IR D C = IR B C
... | is-other-coprod f = case h k ∘ f

-- Helper: handle second argument after first is classified as "other"
optimize-compose-second : ∀ {A B C} → IR B C → IR A B → IR A C
optimize-compose-second g f with composeSecondView f
... | cs-id = g
... | cs-initial = initial
... | cs-other f = g ∘ f

optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C
-- If `f` carries an observable effect, never drop it or its components:
-- the dead-code/beta rules below (`terminal ∘ f → terminal`, `fst/snd ∘
-- ⟨g,h⟩ → g/h`) are value-correct but would erase `f`'s SigOp trace. Keep
-- `g ∘ f` verbatim (still value-correct, and the effect is preserved).
optimize-compose g f with has-effect? f
... | true = g ∘ f
optimize-compose g f | false with composeFirstView g
... | cf-id = f                                    -- id ∘ f = f
... | cf-terminal = terminal                       -- terminal ∘ f = terminal
... | cf-fst = optimize-fst f                      -- fst ∘ f (beta reduction)
... | cf-snd = optimize-snd f                      -- snd ∘ f (beta reduction)
... | cf-case h k = optimize-post-case h k f       -- case h k ∘ f (beta reduction)
... | cf-other g = optimize-compose-second g f     -- check second arg

------------------------------------------------------------------------
-- Eta Laws (for pairs and cases)
------------------------------------------------------------------------

-- | Optimize pair construction
--   ⟨ fst , snd ⟩ = id (eta)
-- Plan 0.53 preserved the pair's `AllocMode` here rather than forcing `Stack`,
-- because "an optimized pair that escapes (e.g. captured by a closure) must
-- stay on the heap in heap-mode".
--
-- Stage G removes the mode, so that distinction can no longer be expressed at
-- this node. See the ESCAPE note on `⟨_,_⟩` in `Once.IR`: this is the one
-- claim in the pair migration that is NOT discharged by the typechecker.
optimize-pair-aux : ∀ {A B C} (f : IR C A) (g : IR C B)
                  → FstSndView f → FstSndView g → IR C (A * B)
optimize-pair-aux f g fsv-fst       fsv-snd       = id
optimize-pair-aux f g fsv-fst       fsv-fst       = ⟨ f , g ⟩
optimize-pair-aux f g fsv-fst       (fsv-other _) = ⟨ f , g ⟩
optimize-pair-aux f g fsv-snd       fsv-fst       = ⟨ f , g ⟩
optimize-pair-aux f g fsv-snd       fsv-snd       = ⟨ f , g ⟩
optimize-pair-aux f g fsv-snd       (fsv-other _) = ⟨ f , g ⟩
optimize-pair-aux f g (fsv-other _) fsv-fst       = ⟨ f , g ⟩
optimize-pair-aux f g (fsv-other _) fsv-snd       = ⟨ f , g ⟩
optimize-pair-aux f g (fsv-other _) (fsv-other _) = ⟨ f , g ⟩

optimize-pair : ∀ {A B C} → IR C A → IR C B → IR C (A * B)
optimize-pair f g = optimize-pair-aux f g (fstSndView f) (fstSndView g)

-- | Optimize case construction
--   [ inl , inr ] = id (eta)
optimize-case-aux : ∀ {A B C} (f : IR A C) (g : IR B C)
                  → InlInrView f → InlInrView g → IR (A + B) C
optimize-case-aux f g iiv-inl         iiv-inr         = id
optimize-case-aux f g iiv-inl         iiv-inl         = case f g
optimize-case-aux f g iiv-inl         (iiv-other _) = case f g
optimize-case-aux f g iiv-inr         iiv-inl         = case f g
optimize-case-aux f g iiv-inr         iiv-inr         = case f g
optimize-case-aux f g iiv-inr         (iiv-other _) = case f g
optimize-case-aux f g (iiv-other _) iiv-inl         = case f g
optimize-case-aux f g (iiv-other _) iiv-inr         = case f g
optimize-case-aux f g (iiv-other _) (iiv-other _) = case f g

optimize-case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C
optimize-case f g = optimize-case-aux f g (inlInrView f) (inlInrView g)

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
  optimize-once-structural ⟨ f , g ⟩ = optimize-pair (optimize-once f) (optimize-once g)
  -- | inl with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (inl {A} {B}) with A ≟IRTy II.Void
  ... | yes refl = initial
  ... | no _     = inl
  -- | inr with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (inr {A} {B}) with B ≟IRTy II.Void
  ... | yes refl = initial
  ... | no _     = inr
  optimize-once-structural (case f g) = optimize-case (optimize-once f) (optimize-once g)
  optimize-once-structural terminal = terminal
  optimize-once-structural initial = initial
  optimize-once-structural (curry f) = curry (optimize-once f)
  optimize-once-structural apply = apply
  -- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
  -- | SigOp with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (SigOp {A} n) with A ≟T Void
  ... | yes refl = initial
  ... | no _     = SigOp n
  -- | const is opaque (constant value of a primitive type, not optimized)
  optimize-once-structural (const p v) = const p v
  -- | a call is opaque here: its entry is optimized where it is defined
  optimize-once-structural (Call f) = Call f
  -- | free-heap is opaque (no optimization)
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
  optimize-once-structural (In wf) = In wf
  optimize-once-structural (out-μ wf) = out-μ wf
  optimize-once-structural (Cata {F} wf alg) = Cata {F} wf (optimize-once alg)
  optimize-once-structural (Out wf) = Out wf
  optimize-once-structural (in-ν wf) = in-ν wf
  optimize-once-structural (Ana {F} wf coalg) = Ana {F} wf (optimize-once coalg)
  -- Guard/Unguard removed: productivity follows from IR totality
  -- out-μ/in-ν: Lambek isomorphisms (potential fusion: out-μ ∘ In = id, In ∘ out-μ = id)

  -- | Type-directed optimization
  optimize-once : ∀ {A B} → IR A B → IR A B
  optimize-once {A} {B} ir with B ≟IRTy II.Unit
  ... | yes refl with has-effect? ir
  ...   | false = terminal                     -- pure morphism to Unit → terminal
  ...   | true  = optimize-once-structural ir  -- EFFECTFUL (SigOp) → keep; collapsing would drop the observable effect
  optimize-once {A} {B} ir | no _ with A ≟IRTy II.Void
  ...   | yes refl = initial                   -- Source is Void → initial (vacuous: never invoked)
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