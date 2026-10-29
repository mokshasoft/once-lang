-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Optimize
--
-- Optimizer for Once IR using categorical laws as rewrite rules. Each pass
-- keeps the program's trace (`Once.Adequacy.OptimizePreserves`, D347); each
-- rule has an example in `Once.Optimize.Examples`.
--
-- Rules:
--   - Type-directed: a quiet map into `Unit` is `terminal`; a map out of
--     `Void` is `initial`
--   - Identity: id ∘ f = f, g ∘ id = g
--   - Associativity: (h ∘ k) ∘ f = h ∘ (k ∘ f), so the beta rules see a
--     chain's head
--   - Beta: fst ∘ ⟨f,g⟩ = f, snd ∘ ⟨f,g⟩ = g, case f g ∘ inl = f,
--     case f g ∘ inr = g, also through a chain (fst ∘ (⟨f,g⟩ ∘ k) = f ∘ k)
--   - Closure beta: apply ∘ ⟨curry f ∘ k, x⟩ = f ∘ ⟨k, x⟩
--   - Eta, up to Unit/Void: ⟨fst,snd⟩ = id, [inl,inr] = id
--   - Dead code: terminal ∘ f = terminal, g ∘ initial = initial
-- A rule that drops a term does so only when that term has no effect
-- (`has-effect?`).
------------------------------------------------------------------------

module Once.Optimize where

open import Once.Spec.Type using (var; Ty)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Type.Core
open import Once.Spec.Type using (μ; ν)
open import Once.Spec.Type using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; K; Id; _⊕_; _⊗_)
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PK; PId; _P⊕_; _P⊗_; PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PInt; PFloat; PTVar)
open import Once.Type.Poly
open import Once.Type
open import Once.IR
open import Once.IRTy using (Unit; Void; _*_; _+_; _⇛_; Int; Float; IRTy; _≟IRTy_)
import Once.IRTy as II

open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
import Data.Nat.Properties
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

------------------------------------------------------------------------
-- Equality decision (needed for eta laws)
--
-- 0.86 stage G: `_≟AllocMode_` stood here and is DELETED. It existed so
-- `≟IRH-diag` could compare the modes of two IR nodes; with all six
-- constructors mode-free there is nothing left to compare, and every clause
-- that used it collapsed to the functor/well-formedness comparison alone.
------------------------------------------------------------------------

-- Plan 0.99: Functor/Type equality is `Once.Type.DecEq`'s — the one copy.
open import Once.Type.DecEq using (_≟T_)

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
  cf-comp : ∀ {A X C} (h : IR X C) (k : IR A X) → ComposeFirstView (h ∘ k)
  cf-apply : ∀ {A B} → ComposeFirstView (apply {A} {B})
  cf-other : ∀ {B C} (g : IR B C) → ComposeFirstView g

-- View: classify IR by optimization-relevant structure (second argument of compose)
data ComposeSecondView : ∀ {A B : IRTy} → IR A B → Set where
  cs-id : ∀ {A} → ComposeSecondView {A} {A} id
  cs-initial : ∀ {A} → ComposeSecondView {Void} {A} initial
  cs-other : ∀ {A B} (f : IR A B) → ComposeSecondView f

-- View: a closure built in place (`curry f`), or another term into an arrow
data CurryView : ∀ {X A B : IRTy} → IR X (A ⇛ B) → Set where
  is-curry : ∀ {X A B} (f : IR (X * A) B) → CurryView (curry f)
  is-other-curry : ∀ {X A B} (c : IR X (A ⇛ B)) → CurryView c

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
pairView-gen (Iter b)        eq = is-other-pair (subst (IR _) eq (Iter b))
pairView-gen (SigOp si)      eq = is-other-pair (subst (IR _) eq (SigOp si))
pairView-gen (Call f)       eq = is-other-pair (subst (IR _) eq (Call f))
pairView-gen (const p v) eq = is-other-pair (subst (IR _) eq (const p v))

pairView : ∀ {A B C} → (f : IR A (B * C)) → PairView f
pairView f = pairView-gen f refl

-- CurryView: target is an arrow (the PairView pattern: a free codomain and an equation)
curryView-gen : ∀ {X T} (c : IR X T) → ∀ {A B} → (eq : T ≡ A ⇛ B) → CurryView {X} {A} {B} (subst (IR X) eq c)
curryView-gen (curry f) refl = is-curry f
curryView-gen id eq = is-other-curry (subst (IR _) eq id)
curryView-gen (f ∘ g) eq = is-other-curry (subst (IR _) eq (f ∘ g))
curryView-gen (⟨ f , g ⟩) eq = is-other-curry (subst (IR _) eq (⟨ f , g ⟩))
curryView-gen fst eq = is-other-curry (subst (IR _) eq fst)
curryView-gen snd eq = is-other-curry (subst (IR _) eq snd)
curryView-gen inl eq = is-other-curry (subst (IR _) eq inl)
curryView-gen inr eq = is-other-curry (subst (IR _) eq inr)
curryView-gen (case f g) eq = is-other-curry (subst (IR _) eq (case f g))
curryView-gen terminal eq = is-other-curry (subst (IR _) eq terminal)
curryView-gen initial eq = is-other-curry (subst (IR _) eq initial)
curryView-gen apply eq = is-other-curry (subst (IR _) eq apply)
curryView-gen (In wf) eq = is-other-curry (subst (IR _) eq (In wf))
curryView-gen (out-μ wf) eq = is-other-curry (subst (IR _) eq (out-μ wf))
curryView-gen (Cata wf alg) eq = is-other-curry (subst (IR _) eq (Cata wf alg))
curryView-gen (Out wf) eq = is-other-curry (subst (IR _) eq (Out wf))
curryView-gen (in-ν wf) eq = is-other-curry (subst (IR _) eq (in-ν wf))
curryView-gen (Ana wf coalg) eq = is-other-curry (subst (IR _) eq (Ana wf coalg))
curryView-gen (Iter b) eq = is-other-curry (subst (IR _) eq (Iter b))
curryView-gen (SigOp si) eq = is-other-curry (subst (IR _) eq (SigOp si))
curryView-gen (Call f) eq = is-other-curry (subst (IR _) eq (Call f))
curryView-gen (const p v) eq = is-other-curry (subst (IR _) eq (const p v))

curryView : ∀ {X A B} → (c : IR X (A ⇛ B)) → CurryView c
curryView c = curryView-gen c refl

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
coprodView-gen (Iter b)        eq = is-other-coprod (subst (IR _) eq (Iter b))
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
composeFirstView (g ∘ h)         = cf-comp g h
composeFirstView (⟨ f , g ⟩)   = cf-other (⟨ f , g ⟩)
composeFirstView inl             = cf-other inl
composeFirstView inr             = cf-other inr
composeFirstView initial         = cf-other initial
composeFirstView (curry f)       = cf-other (curry f)
composeFirstView apply           = cf-apply
composeFirstView (In wf)       = cf-other (In wf)
composeFirstView (out-μ wf)      = cf-other (out-μ wf)
composeFirstView (Cata wf alg)   = cf-other (Cata wf alg)
composeFirstView (Out wf)        = cf-other (Out wf)
composeFirstView (in-ν wf)     = cf-other (in-ν wf)
composeFirstView (Ana wf coalg)  = cf-other (Ana wf coalg)
composeFirstView (Iter b)        = cf-other (Iter b)
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
composeSecondView (Iter b)       = cs-other (Iter b)
composeSecondView (SigOp si)     = cs-other (SigOp si)
composeSecondView (Call f)       = cs-other (Call f)
composeSecondView (const p v) = cs-other (const p v)

-- (the beta rules read a chain's head through it: the optimizer nests to the right)
-- | A composition `p ∘ k`, or a term that is not one.
data ChainView : ∀ {A B : IRTy} → IR A B → Set where
  is-comp  : ∀ {A X B} (p : IR X B) (k : IR A X) → ChainView (p ∘ k)
  not-comp : ∀ {A B} (f : IR A B) → ChainView f

chainView : ∀ {A B} → (f : IR A B) → ChainView f
chainView (p ∘ k)        = is-comp p k
chainView id             = not-comp id
chainView (⟨ f , g ⟩)    = not-comp (⟨ f , g ⟩)
chainView fst            = not-comp fst
chainView snd            = not-comp snd
chainView inl            = not-comp inl
chainView inr            = not-comp inr
chainView (case f g)     = not-comp (case f g)
chainView terminal       = not-comp terminal
chainView initial        = not-comp initial
chainView (curry f)      = not-comp (curry f)
chainView apply          = not-comp apply
chainView (In wf)        = not-comp (In wf)
chainView (out-μ wf)     = not-comp (out-μ wf)
chainView (Cata wf alg)  = not-comp (Cata wf alg)
chainView (Out wf)       = not-comp (Out wf)
chainView (in-ν wf)      = not-comp (in-ν wf)
chainView (Ana wf coalg) = not-comp (Ana wf coalg)
chainView (Iter b)       = not-comp (Iter b)
chainView (SigOp si)     = not-comp (SigOp si)
chainView (Call f)       = not-comp (Call f)
chainView (const p v)    = not-comp (const p v)

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
fstSndView (Iter b)        = fsv-other (Iter b)
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
inlInrView (Iter b)        = iiv-other (Iter b)
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
-- Forcing a stream runs its coalgebra, and an `act` stream's may emit; the
-- IR does not say which grade a stream has (plan 0.39).
has-effect? (Out _)         = true
has-effect? (in-ν _)      = false
has-effect? (Ana _ coalg)   = has-effect? coalg
-- a loop may run forever without an event: never dead code.
has-effect? (Iter _)        = true


-- | `g ∘ id = g`; `g ∘ initial = initial`
compose-second-aux : ∀ {A B C} (g : IR B C) (f : IR A B) → ComposeSecondView f → IR A C
compose-second-aux g _ cs-id        = g
compose-second-aux g _ cs-initial   = initial
compose-second-aux g _ (cs-other f) = g ∘ f

optimize-compose-second : ∀ {A B C} → IR B C → IR A B → IR A C
optimize-compose-second g f = compose-second-aux g f (composeSecondView f)

-- | `fst ∘ ⟨ a , b ⟩ = a`, read through a chain: `fst ∘ (⟨ a , b ⟩ ∘ k) = a ∘ k`.
-- It drops `b`, so only when `b` has no effect.
fst-pair : ∀ {A B C} (a : IR A B) (b : IR A C) → Bool → IR A B
fst-pair a b true  = fst ∘ ⟨ a , b ⟩
fst-pair a b false = a

fst-chain-pair : ∀ {A X B C} (a : IR X B) (b : IR X C) (k : IR A X) → Bool → IR A B
fst-chain-pair a b k true  = fst ∘ (⟨ a , b ⟩ ∘ k)
fst-chain-pair a b k false = a ∘ k

fst-chain-aux : ∀ {A X B C} (p : IR X (B * C)) (k : IR A X) → PairView p → IR A B
fst-chain-aux _ k (is-pair a b)     = fst-chain-pair a b k (has-effect? b)
fst-chain-aux _ k (is-other-pair p) = fst ∘ (p ∘ k)

fst-chain : ∀ {A B C} (f : IR A (B * C)) → ChainView f → IR A B
fst-chain _ (is-comp p k) = fst-chain-aux p k (pairView p)
fst-chain _ (not-comp f)  = optimize-compose-second fst f

fst-aux : ∀ {A B C} (f : IR A (B * C)) → PairView f → IR A B
fst-aux _ (is-pair a b)     = fst-pair a b (has-effect? b)
fst-aux _ (is-other-pair f) = fst-chain f (chainView f)

optimize-fst : ∀ {A B C} → IR A (B * C) → IR A B
optimize-fst f = fst-aux f (pairView f)

-- | `snd ∘ ⟨ a , b ⟩ = b` (and through a chain), when `a` has no effect.
snd-pair : ∀ {A B C} (a : IR A B) (b : IR A C) → Bool → IR A C
snd-pair a b true  = snd ∘ ⟨ a , b ⟩
snd-pair a b false = b

snd-chain-pair : ∀ {A X B C} (a : IR X B) (b : IR X C) (k : IR A X) → Bool → IR A C
snd-chain-pair a b k true  = snd ∘ (⟨ a , b ⟩ ∘ k)
snd-chain-pair a b k false = b ∘ k

snd-chain-aux : ∀ {A X B C} (p : IR X (B * C)) (k : IR A X) → PairView p → IR A C
snd-chain-aux _ k (is-pair a b)     = snd-chain-pair a b k (has-effect? a)
snd-chain-aux _ k (is-other-pair p) = snd ∘ (p ∘ k)

snd-chain : ∀ {A B C} (f : IR A (B * C)) → ChainView f → IR A C
snd-chain _ (is-comp p k) = snd-chain-aux p k (pairView p)
snd-chain _ (not-comp f)  = optimize-compose-second snd f

snd-aux : ∀ {A B C} (f : IR A (B * C)) → PairView f → IR A C
snd-aux _ (is-pair a b)     = snd-pair a b (has-effect? a)
snd-aux _ (is-other-pair f) = snd-chain f (chainView f)

optimize-snd : ∀ {A B C} → IR A (B * C) → IR A C
optimize-snd f = snd-aux f (pairView f)

-- | `case h k ∘ inl = h`, `case h k ∘ inr = k`, and through a chain:
-- `case h k ∘ (inl ∘ m) = h ∘ m`. Nothing is dropped.
post-case-chain-aux : ∀ {A B C D X} (h : IR A C) (k : IR B C) (p : IR X (A + B)) (m : IR D X)
                    → CoprodView p → IR D C
post-case-chain-aux h k _ m is-inl              = h ∘ m
post-case-chain-aux h k _ m is-inr              = k ∘ m
post-case-chain-aux h k _ m (is-other-coprod p) = case h k ∘ (p ∘ m)

post-case-chain : ∀ {A B C D} (h : IR A C) (k : IR B C) (f : IR D (A + B)) → ChainView f → IR D C
post-case-chain h k _ (is-comp p m) = post-case-chain-aux h k p m (coprodView p)
post-case-chain h k _ (not-comp f)  = optimize-compose-second (case h k) f

post-case-aux : ∀ {A B C D} (h : IR A C) (k : IR B C) (f : IR D (A + B)) → CoprodView f → IR D C
post-case-aux h k _ is-inl              = h
post-case-aux h k _ is-inr              = k
post-case-aux h k _ (is-other-coprod f) = post-case-chain h k f (chainView f)

optimize-post-case : ∀ {A B C D} → IR A C → IR B C → IR D (A + B) → IR D C
optimize-post-case h k f = post-case-aux h k f (coprodView f)

-- | Closure beta: `apply ∘ ⟨ curry f ∘ k , x ⟩ = f ∘ ⟨ k , x ⟩`. The closure is
-- built in place, so applying it runs its body; `k` and `x` keep their order
-- and nothing is dropped. (Also with no `k`, and through a chain.)
beta-head : ∀ {X Y A B} (c : IR Y (A ⇛ B)) (k : IR X Y) (x : IR X A) → CurryView c → IR X B
beta-head _ k x (is-curry f)       = f ∘ ⟨ k , x ⟩
beta-head c k x (is-other-curry _) = apply ∘ ⟨ c ∘ k , x ⟩

beta-bare : ∀ {X A B} (c : IR X (A ⇛ B)) (x : IR X A) → CurryView c → IR X B
beta-bare _ x (is-curry f)       = f ∘ ⟨ id , x ⟩
beta-bare c x (is-other-curry _) = apply ∘ ⟨ c , x ⟩

closure-beta : ∀ {X A B} (c : IR X (A ⇛ B)) (x : IR X A) → ChainView c → IR X B
closure-beta _ x (is-comp h k) = beta-head h k x (curryView h)
closure-beta _ x (not-comp c)  = beta-bare c x (curryView c)

-- (through a chain the result stays right-nested, and is unchanged when no
-- closure is found: a pass must not undo the re-association)
beta-head-chain : ∀ {X Z Y A B} (c : IR Y (A ⇛ B)) (k : IR Z Y) (x : IR Z A) (m : IR X Z) → CurryView c → IR X B
beta-head-chain _ k x m (is-curry f)       = f ∘ (⟨ k , x ⟩ ∘ m)
beta-head-chain c k x m (is-other-curry _) = apply ∘ (⟨ c ∘ k , x ⟩ ∘ m)

beta-bare-chain : ∀ {X Z A B} (c : IR Z (A ⇛ B)) (x : IR Z A) (m : IR X Z) → CurryView c → IR X B
beta-bare-chain _ x m (is-curry f)       = f ∘ (⟨ id , x ⟩ ∘ m)
beta-bare-chain c x m (is-other-curry _) = apply ∘ (⟨ c , x ⟩ ∘ m)

closure-beta-chain : ∀ {X Z A B} (c : IR Z (A ⇛ B)) (x : IR Z A) (m : IR X Z) → ChainView c → IR X B
closure-beta-chain _ x m (is-comp h k) = beta-head-chain h k x m (curryView h)
closure-beta-chain _ x m (not-comp c)  = beta-bare-chain c x m (curryView c)

apply-chain-aux : ∀ {X Z A B} (p : IR Z ((A ⇛ B) * A)) (m : IR X Z) → PairView p → IR X B
apply-chain-aux _ m (is-pair c x)     = closure-beta-chain c x m (chainView c)
apply-chain-aux _ m (is-other-pair p) = apply ∘ (p ∘ m)

apply-chain : ∀ {X A B} (F : IR X ((A ⇛ B) * A)) → ChainView F → IR X B
apply-chain _ (is-comp p m) = apply-chain-aux p m (pairView p)
apply-chain _ (not-comp F)  = optimize-compose-second apply F

apply-aux : ∀ {X A B} (F : IR X ((A ⇛ B) * A)) → PairView F → IR X B
apply-aux _ (is-pair c x)     = closure-beta c x (chainView c)
apply-aux _ (is-other-pair F) = apply-chain F (chainView F)

optimize-apply : ∀ {X A B} → IR X ((A ⇛ B) * A) → IR X B
optimize-apply F = apply-aux F (pairView F)

-- | `terminal ∘ f = terminal`, when `f` has no effect (it would be dropped).
terminal-drop : ∀ {A B} (f : IR A B) → Bool → IR A Unit
terminal-drop f true  = terminal ∘ f
terminal-drop f false = terminal

-- | Composition. Each rule that drops a term checks THAT term for an effect
-- (`has-effect?`): `terminal ∘ f` checks `f`, `fst ∘ ⟨ a , b ⟩` checks `b`.
-- The others drop nothing: `id ∘ f = f`, the case and identity rules, and
-- `(h ∘ k) ∘ f = h ∘ (k ∘ f)`, which puts a chain on the right so that the
-- beta rules see its head.
compose-aux : ∀ {A B C} (g : IR B C) (f : IR A B) → ComposeFirstView g → IR A C
compose-aux _ f cf-id         = f
compose-aux _ f cf-terminal   = terminal-drop f (has-effect? f)
compose-aux _ f cf-fst        = optimize-fst f
compose-aux _ f cf-snd        = optimize-snd f
compose-aux _ f (cf-case h k) = optimize-post-case h k f
compose-aux _ f (cf-comp h k) = h ∘ (k ∘ f)
compose-aux _ f cf-apply      = optimize-apply f
compose-aux _ f (cf-other g)  = optimize-compose-second g f

optimize-compose : ∀ {A B C} → IR B C → IR A B → IR A C
optimize-compose g f = compose-aux g f (composeFirstView g)

------------------------------------------------------------------------
-- Eta Laws (for pairs and cases)
------------------------------------------------------------------------

-- | A projection path: `id`, `fst`, `snd` and their composites. Two paths are
-- compared by their structure; a general IR equality is not decidable (D271).
data Proj : IRTy → IRTy → Set where
  p-id  : ∀ {A} → Proj A A
  p-fst : ∀ {A B} → Proj (A * B) A
  p-snd : ∀ {A B} → Proj (A * B) B
  p-∘   : ∀ {A X B} → Proj X B → Proj A X → Proj A B

proj-ir : ∀ {A B} → Proj A B → IR A B
proj-ir p-id      = id
proj-ir p-fst     = fst
proj-ir p-snd     = snd
proj-ir (p-∘ p q) = proj-ir p ∘ proj-ir q

-- | The path a term is, if it is one.
proj-of   : ∀ {A B} (h : IR A B) → Maybe (Σ (Proj A B) (λ p → proj-ir p ≡ h))
proj-comp : ∀ {A X B} (f : IR X B) (g : IR A X)
          → Maybe (Σ (Proj X B) (λ p → proj-ir p ≡ f)) → Maybe (Σ (Proj A X) (λ q → proj-ir q ≡ g))
          → Maybe (Σ (Proj A B) (λ p → proj-ir p ≡ f ∘ g))
proj-of id      = just (p-id , refl)
proj-of fst     = just (p-fst , refl)
proj-of snd     = just (p-snd , refl)
proj-of (f ∘ g) = proj-comp f g (proj-of f) (proj-of g)
proj-of (⟨ f , g ⟩) = nothing
proj-of inl = nothing
proj-of inr = nothing
proj-of (case f g) = nothing
proj-of terminal = nothing
proj-of initial = nothing
proj-of (curry f) = nothing
proj-of apply = nothing
proj-of (In wf) = nothing
proj-of (out-μ wf) = nothing
proj-of (Cata wf alg) = nothing
proj-of (Out wf) = nothing
proj-of (in-ν wf) = nothing
proj-of (Ana wf coalg) = nothing
proj-of (Iter b) = nothing
proj-of (SigOp si) = nothing
proj-of (Call f) = nothing
proj-of (const p v) = nothing
proj-comp _ _ nothing           _                = nothing
proj-comp _ _ (just _)          nothing          = nothing
proj-comp _ _ (just (p , refl)) (just (q , refl)) = just (p-∘ p q , refl)

-- | Two paths out of one object are the same path.
proj-eq?  : ∀ {X P Q} (p : Proj X P) (q : Proj X Q) → Maybe (Σ (P ≡ Q) (λ e → subst (Proj X) e p ≡ q))
proj-eq?₁ : ∀ {A X X′ B B′} (p : Proj X B) (q : Proj A X) (p′ : Proj X′ B′) (q′ : Proj A X′)
          → Maybe (Σ (X ≡ X′) (λ e → subst (Proj A) e q ≡ q′))
          → Maybe (Σ (B ≡ B′) (λ e → subst (Proj A) e (p-∘ p q) ≡ p-∘ p′ q′))
proj-eq?₂ : ∀ {A X B B′} (p : Proj X B) (q : Proj A X) (p′ : Proj X B′)
          → Maybe (Σ (B ≡ B′) (λ e → subst (Proj X) e p ≡ p′))
          → Maybe (Σ (B ≡ B′) (λ e → subst (Proj A) e (p-∘ p q) ≡ p-∘ p′ q))
proj-eq? p-id      p-id        = just (refl , refl)
proj-eq? p-fst     p-fst       = just (refl , refl)
proj-eq? p-snd     p-snd       = just (refl , refl)
proj-eq? (p-∘ p q) (p-∘ p′ q′) = proj-eq?₁ p q p′ q′ (proj-eq? q q′)
{-# CATCHALL #-}
proj-eq? _         _           = nothing
proj-eq?₁ p q p′ q′ nothing             = nothing
proj-eq?₁ p q p′ _ (just (refl , refl)) = proj-eq?₂ p q p′ (proj-eq? p p′)
proj-eq?₂ p q p′ nothing             = nothing
proj-eq?₂ p q _ (just (refl , refl)) = just (refl , refl)

-- | `⟨ fst ∘ h , snd ∘ h ⟩`, for one projection path `h` (pair uniqueness), or not.
data PairUniq : ∀ {C A B : IRTy} → IR C A → IR C B → Set where
  uniq     : ∀ {C A B} (p : Proj C (A * B)) → PairUniq (fst ∘ proj-ir p) (snd ∘ proj-ir p)
  not-uniq : ∀ {C A B} (f : IR C A) (g : IR C B) → PairUniq f g

uniq-eq : ∀ {C A A′ B B′} (p : Proj C (A * B′)) (q : Proj C (A′ * B))
        → Maybe (Σ (A * B′ ≡ A′ * B) (λ e → subst (Proj C) e p ≡ q))
        → PairUniq (fst ∘ proj-ir p) (snd ∘ proj-ir q)
uniq-eq p q nothing              = not-uniq _ _
uniq-eq p _ (just (refl , refl)) = uniq p

uniq-paths : ∀ {C A A′ B B′} (h₁ : IR C (A * B′)) (h₂ : IR C (A′ * B))
           → Maybe (Σ (Proj C (A * B′)) (λ p → proj-ir p ≡ h₁)) → Maybe (Σ (Proj C (A′ * B)) (λ q → proj-ir q ≡ h₂))
           → PairUniq (fst ∘ h₁) (snd ∘ h₂)
uniq-paths _ _ nothing           _                = not-uniq _ _
uniq-paths _ _ (just _)          nothing          = not-uniq _ _
uniq-paths _ _ (just (p , refl)) (just (q , refl)) = uniq-eq p q (proj-eq? p q)

uniq-heads : ∀ {C X Y A B} (p : IR X A) (h₁ : IR C X) (q : IR Y B) (h₂ : IR C Y)
           → FstSndView p → FstSndView q → PairUniq (p ∘ h₁) (q ∘ h₂)
uniq-heads _ h₁ _ h₂ fsv-fst       fsv-snd       = uniq-paths h₁ h₂ (proj-of h₁) (proj-of h₂)
uniq-heads _ h₁ _ h₂ fsv-fst       fsv-fst       = not-uniq _ _
uniq-heads _ h₁ _ h₂ fsv-fst       (fsv-other _) = not-uniq _ _
uniq-heads _ h₁ _ h₂ fsv-snd       _             = not-uniq _ _
uniq-heads _ h₁ _ h₂ (fsv-other _) _             = not-uniq _ _

pairUniq-at : ∀ {C A B} (f : IR C A) (g : IR C B) → ChainView f → ChainView g → PairUniq f g
pairUniq-at _ _ (is-comp p h₁) (is-comp q h₂) = uniq-heads p h₁ q h₂ (fstSndView p) (fstSndView q)
pairUniq-at _ _ (is-comp _ _)  (not-comp _)   = not-uniq _ _
pairUniq-at _ _ (not-comp _)   _              = not-uniq _ _

pairUniq : ∀ {C A B} (f : IR C A) (g : IR C B) → PairUniq f g
pairUniq f g = pairUniq-at f g (chainView f) (chainView g)

-- | A quiet term into `Unit` stands for any other: `Unit` has one value.
unit-like-aux : ∀ {A B} → IR A B → Dec (B ≡ Unit) → Bool
unit-like-aux f (yes _) = not (has-effect? f)
unit-like-aux f (no _)  = false

unit-like : ∀ {A B} → IR A B → Bool
unit-like {B = B} f = unit-like-aux f (B ≟IRTy Unit)

-- | A term out of `Void` stands for any other: it is never run.
void-like : ∀ {A B} → IR A B → Bool
void-like {A} _ = isYes (A ≟IRTy Void)

-- | The first projection up to `Unit`: `fst`, or a quiet term into `Unit`
-- (whose source is then `Unit * B`). Likewise `snd`.
fst-like-aux : ∀ {A B} (f : IR (A * B) A) → FstSndView f → Bool
fst-like-aux f fsv-fst       = true
fst-like-aux f fsv-snd       = unit-like f
fst-like-aux f (fsv-other _) = unit-like f

snd-like-aux : ∀ {A B} (g : IR (A * B) B) → FstSndView g → Bool
snd-like-aux g fsv-fst       = unit-like g
snd-like-aux g fsv-snd       = true
snd-like-aux g (fsv-other _) = unit-like g

-- | The injections up to `Void`: `inl`, or any term out of `Void` (whose
-- target is then `Void + B`). Likewise `inr`.
inl-like-aux : ∀ {A B} (f : IR A (A + B)) → InlInrView f → Bool
inl-like-aux f iiv-inl       = true
inl-like-aux f iiv-inr       = void-like f
inl-like-aux f (iiv-other _) = void-like f

inr-like-aux : ∀ {A B} (g : IR B (A + B)) → InlInrView g → Bool
inr-like-aux g iiv-inl       = void-like g
inr-like-aux g iiv-inr       = true
inr-like-aux g (iiv-other _) = void-like g

-- | Eta for pairs, up to `Unit`: `⟨ fst , snd ⟩ = id`, and so is `⟨ terminal ,
-- snd ⟩` out of `Unit * B` (the `Unit` rule turns a `fst` into `Unit` into
-- `terminal` before this rule sees it).
eta-pair : ∀ {A B} (f : IR (A * B) A) (g : IR (A * B) B) → Bool → Bool → IR (A * B) (A * B)
eta-pair f g true  true  = id
eta-pair f g true  false = ⟨ f , g ⟩
eta-pair f g false _     = ⟨ f , g ⟩

pair-aux : ∀ {A B C} → IR C A → IR C B → Dec (C ≡ A * B) → IR C (A * B)
pair-aux f g (yes refl) = eta-pair f g (fst-like-aux f (fstSndView f)) (snd-like-aux g (fstSndView g))
pair-aux f g (no _)     = ⟨ f , g ⟩

-- | `⟨ fst ∘ h , snd ∘ h ⟩ = h` for a projection path `h` (it has no effect,
-- so running it once is running it twice); otherwise eta.
pair-u : ∀ {A B C} (f : IR C A) (g : IR C B) → PairUniq f g → IR C (A * B)
pair-u _ _ (uniq p)       = proj-ir p
pair-u {A} {B} {C} f g (not-uniq _ _) = pair-aux f g (C ≟IRTy (A * B))

optimize-pair : ∀ {A B C} → IR C A → IR C B → IR C (A * B)
optimize-pair f g = pair-u f g (pairUniq f g)

-- | Eta for cases, up to `Void`: `[ inl , inr ] = id`, and so is `[ initial ,
-- inr ]` into `Void + B`.
eta-case : ∀ {A B} (f : IR A (A + B)) (g : IR B (A + B)) → Bool → Bool → IR (A + B) (A + B)
eta-case f g true  true  = id
eta-case f g true  false = case f g
eta-case f g false _     = case f g

case-aux : ∀ {A B C} → IR A C → IR B C → Dec (C ≡ A + B) → IR (A + B) C
case-aux f g (yes refl) = eta-case f g (inl-like-aux f (inlInrView f)) (inr-like-aux g (inlInrView g))
case-aux f g (no _)     = case f g

optimize-case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C
optimize-case {A} {B} {C} f g = case-aux f g (C ≟IRTy (A + B))

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
--   - All quiet morphisms to Unit are terminal (an effect is kept)
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
  -- (out of `Void`, `inl`/`inr` are `initial`: the type-directed rule, before)
  optimize-once-structural inl = inl
  optimize-once-structural inr = inr
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
  optimize-once-structural (Iter b) = Iter (optimize-once b)
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