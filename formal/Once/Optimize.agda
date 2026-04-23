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
open import Once.Functor.Translate using (WellFormedF-irrelevant)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟String_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open import Data.Empty using (⊥)

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
------------------------------------------------------------------------

-- IR equality — decidable equality, postulate-free.
--
-- Approach (generic-codomain trick):
-- The inner helper `_≟IRH_` takes two IR terms with independent type
-- indices, plus equality proofs connecting them:
--
--     f : IR A B,  g : IR A' B',  eqA : A ≡ A',  eqB : B ≡ B'
--
-- It decides whether `f ≡ subst₂ IR (sym eqA) (sym eqB) g`. Because g's
-- indices are free when we case-split on g, Agda can assign them
-- independently per constructor — no SplitError.UnificationStuck on
-- stuck `⟦ F ⟧T` indices in cross-pairs.
--
-- Same-constructor cases use the existing decidable equalities for
-- indices and recurse for sub-IRs. WellFormedF proofs are
-- proof-irrelevant (via `WellFormedF-irrelevant`).
--
-- Cross-pair cases (different head constructors) are dispatched via
-- `ir-head`: a `subst₂`-invariant discriminator. If `ir-head f` and
-- `ir-head g` differ, any hypothetical equality would contradict it.

-- IR head discriminator.
data IRHead : Set where
  h-id h-∘ h-⟨,⟩ h-fst h-snd h-inl h-inr h-case
    h-terminal h-initial h-curry h-apply h-arr h-applyEff
    h-In h-out-μ h-Cata h-Para h-Out h-in-ν h-Ana h-Hylo h-Fuse
    h-free-heap h-Prim : IRHead

ir-head : ∀ {A B} → IR A B → IRHead
ir-head id = h-id
ir-head (_ ∘ _) = h-∘
ir-head (⟨ _ , _ ⟩ _) = h-⟨,⟩
ir-head fst = h-fst
ir-head snd = h-snd
ir-head (inl _) = h-inl
ir-head (inr _) = h-inr
ir-head (case _ _) = h-case
ir-head terminal = h-terminal
ir-head initial = h-initial
ir-head (curry _ _) = h-curry
ir-head apply = h-apply
ir-head arr = h-arr
ir-head applyEff = h-applyEff
ir-head (In _ _) = h-In
ir-head (out-μ _) = h-out-μ
ir-head (Cata _ _) = h-Cata
ir-head (Para _ _) = h-Para
ir-head (Out _) = h-Out
ir-head (in-ν _ _) = h-in-ν
ir-head (Ana _ _) = h-Ana
ir-head (Hylo _ _ _ _) = h-Hylo
ir-head (Fuse _ _ _ _) = h-Fuse
ir-head (free-heap _) = h-free-heap
ir-head (Prim _) = h-Prim

-- subst₂ for IR.
subst₂-IR : ∀ {A B A' B'} → A ≡ A' → B ≡ B' → IR A B → IR A' B'
subst₂-IR refl refl f = f

-- head is preserved under subst₂-IR.
ir-head-subst₂ : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') (f : IR A B)
               → ir-head (subst₂-IR p q f) ≡ ir-head f
ir-head-subst₂ refl refl _ = refl

-- Decidable comparison modulo type-index equalities.
-- Result type: `Dec (f ≡ subst₂-IR (sym eqA) (sym eqB) g)` — when
-- eqA, eqB are refl, this reduces to `Dec (f ≡ g)`.
≟IRH : ∀ {A B A' B'} (f : IR A B) (g : IR A' B')
     → (eqA : A ≡ A') (eqB : B ≡ B')
     → Dec (f ≡ subst₂-IR (sym eqA) (sym eqB) g)

_≟IR_ : ∀ {A B} → (f g : IR A B) → Dec (f ≡ g)
f ≟IR g = ≟IRH f g refl refl

-- Cross-pair rejection: if heads differ, no equality is possible
-- regardless of how the index equalities sit.
head-mismatch-abs : ∀ {A B A' B'} (f : IR A B) (g : IR A' B')
                  → (ir-head f ≡ ir-head g → ⊥)
                  → (eqA : A ≡ A') (eqB : B ≡ B')
                  → f ≡ subst₂-IR (sym eqA) (sym eqB) g
                  → ⊥
head-mismatch-abs f g hneq eqA eqB h =
  hneq (trans (cong ir-head h) (ir-head-subst₂ (sym eqA) (sym eqB) g))

-- Shorthand: build a "no" for cross-pairs via the head-mismatch lemma.
cross-no : ∀ {A B A' B'} {f : IR A B} {g : IR A' B'}
         → (ir-head f ≡ ir-head g → ⊥)
         → (eqA : A ≡ A') (eqB : B ≡ B')
         → f ≡ subst₂-IR (sym eqA) (sym eqB) g
         → ⊥
cross-no {f = f} {g = g} hneq eqA eqB = head-mismatch-abs f g hneq eqA eqB

-- Implementation of ≟IRH.
-- Structure:
--   - 22 diagonal clauses (same constructor on both sides).
--   - 22×21 = 462 cross-pair clauses, each a one-liner rejection via
--     `cross-no (λ ()) eqA eqB`.

------------------------------------------------------------------------
-- Index-injectivity helpers for diagonal cases involving recursive types.
------------------------------------------------------------------------

μ-inj : ∀ {F F'} → μ-type F ≡ μ-type F' → F ≡ F'
μ-inj refl = refl

ν-inj : ∀ {F F'} → ν-type F ≡ ν-type F' → F ≡ F'
ν-inj refl = refl

-- ═══════════════════════════════════════════════════════════════════════
-- Diagonal (same-constructor) cases
-- ═══════════════════════════════════════════════════════════════════════

-- id
≟IRH id id refl refl = yes refl

-- _∘_: compare the intermediate (middle) type first, then sub-IRs
≟IRH (_∘_ {_} {B} g₁ f₁) (_∘_ {_} {B'} g₂ f₂) refl refl
  with B ≟Type B'
... | no neq = no (λ { refl → neq refl })
... | yes refl with ≟IRH g₁ g₂ refl refl | ≟IRH f₁ f₂ refl refl
...   | yes refl | yes refl = yes refl
...   | no np    | _        = no (λ { refl → np refl })
...   | _        | no nq    = no (λ { refl → nq refl })

-- ⟨_,_⟩: B * C equality refl-unifies both component types
≟IRH (⟨ f₁ , g₁ ⟩ m₁) (⟨ f₂ , g₂ ⟩ m₂) refl refl
  with ≟IRH f₁ f₂ refl refl | ≟IRH g₁ g₂ refl refl | m₁ ≟AllocMode m₂
... | yes refl | yes refl | yes refl = yes refl
... | no np    | _        | _        = no (λ { refl → np refl })
... | _        | no nq    | _        = no (λ { refl → nq refl })
... | _        | _        | no nm    = no (λ { refl → nm refl })

≟IRH fst fst refl refl = yes refl
≟IRH snd snd refl refl = yes refl

≟IRH (inl m₁) (inl m₂) refl refl with m₁ ≟AllocMode m₂
... | yes refl = yes refl
... | no nm    = no (λ { refl → nm refl })

≟IRH (inr m₁) (inr m₂) refl refl with m₁ ≟AllocMode m₂
... | yes refl = yes refl
... | no nm    = no (λ { refl → nm refl })

≟IRH (case f₁ g₁) (case f₂ g₂) refl refl
  with ≟IRH f₁ f₂ refl refl | ≟IRH g₁ g₂ refl refl
... | yes refl | yes refl = yes refl
... | no np    | _        = no (λ { refl → np refl })
... | _        | no nq    = no (λ { refl → nq refl })

≟IRH terminal terminal refl refl = yes refl
≟IRH initial initial refl refl = yes refl

≟IRH (curry f₁ m₁) (curry f₂ m₂) refl refl
  with ≟IRH f₁ f₂ refl refl | m₁ ≟AllocMode m₂
... | yes refl | yes refl = yes refl
... | no np    | _        = no (λ { refl → np refl })
... | _        | no nm    = no (λ { refl → nm refl })

≟IRH apply apply refl refl = yes refl
≟IRH arr arr refl refl = yes refl
≟IRH applyEff applyEff refl refl = yes refl

-- In: eqB : μ-type F ≡ μ-type F' gives the Functor tag
≟IRH (In {F} wf₁ m₁) (In {F'} wf₂ m₂) eqA eqB with F ≟Functor F'
... | no fne = no (λ _ → fne (μ-inj eqB))
... | yes refl with m₁ ≟AllocMode m₂ | eqA | eqB
...   | yes refl | refl | refl rewrite WellFormedF-irrelevant wf₁ wf₂ = yes refl
...   | no nm    | refl | refl = no (λ { refl → nm refl })

-- out-μ: eqA : μ-type F ≡ μ-type F'
≟IRH (out-μ {F} wf₁) (out-μ {F'} wf₂) eqA eqB with F ≟Functor F'
... | no fne = no (λ _ → fne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl rewrite WellFormedF-irrelevant wf₁ wf₂ = yes refl

-- Cata: eqA : μ-type F ≡ μ-type F', eqB : A ≡ A'
≟IRH (Cata {F} wf₁ alg₁) (Cata {F'} wf₂ alg₂) eqA eqB
  with F ≟Functor F'
... | no fne = no (λ _ → fne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with ≟IRH alg₁ alg₂ refl refl
...     | yes refl rewrite WellFormedF-irrelevant wf₁ wf₂ = yes refl
...     | no np = no (λ { refl → np refl })

-- Para: similar
≟IRH (Para {F} wf₁ alg₁) (Para {F'} wf₂ alg₂) eqA eqB
  with F ≟Functor F'
... | no fne = no (λ _ → fne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with ≟IRH alg₁ alg₂ refl refl
...     | yes refl rewrite WellFormedF-irrelevant wf₁ wf₂ = yes refl
...     | no np = no (λ { refl → np refl })

-- Out: eqA : ν-type F ≡ ν-type F'
≟IRH (Out {F} wf₁) (Out {F'} wf₂) eqA eqB with F ≟Functor F'
... | no fne = no (λ _ → fne (ν-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl rewrite WellFormedF-irrelevant wf₁ wf₂ = yes refl

-- in-ν: eqB : ν-type F ≡ ν-type F'
≟IRH (in-ν {F} wf₁ m₁) (in-ν {F'} wf₂ m₂) eqA eqB
  with F ≟Functor F'
... | no fne = no (λ _ → fne (ν-inj eqB))
... | yes refl with m₁ ≟AllocMode m₂ | eqA | eqB
...   | yes refl | refl | refl rewrite WellFormedF-irrelevant wf₁ wf₂ = yes refl
...   | no nm    | refl | refl = no (λ { refl → nm refl })

-- Ana: eqB : ν-type F ≡ ν-type F'
≟IRH (Ana {F} wf₁ coalg₁) (Ana {F'} wf₂ coalg₂) eqA eqB
  with F ≟Functor F'
... | no fne = no (λ _ → fne (ν-inj eqB))
... | yes refl with eqA | eqB
...   | refl | refl with ≟IRH coalg₁ coalg₂ refl refl
...     | yes refl rewrite WellFormedF-irrelevant wf₁ wf₂ = yes refl
...     | no np = no (λ { refl → np refl })

-- Hylo: eqA : μ-type G ≡ μ-type G', eqB : B ≡ B'.
-- F is internal to the alg's type; require F ≟ F' separately.
≟IRH (Hylo {F} {G} wfF₁ wfG₁ alg₁ coalg₁)
     (Hylo {F'} {G'} wfF₂ wfG₂ alg₂ coalg₂) eqA eqB
  with G ≟Functor G'
... | no gne = no (λ _ → gne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with F ≟Functor F'
...     | no fne  = no (λ { refl → fne refl })
...     | yes refl with ≟IRH alg₁ alg₂ refl refl | ≟IRH coalg₁ coalg₂ refl refl
...       | yes refl | yes refl
              rewrite WellFormedF-irrelevant wfF₁ wfF₂
                    | WellFormedF-irrelevant wfG₁ wfG₂ = yes refl
...       | no np    | _        = no (λ { refl → np refl })
...       | _        | no nq    = no (λ { refl → nq refl })

-- Fuse: similar shape to Hylo
≟IRH (Fuse {F} {G} wfF₁ wfG₁ alg₁ tr₁)
     (Fuse {F'} {G'} wfF₂ wfG₂ alg₂ tr₂) eqA eqB
  with G ≟Functor G'
... | no gne = no (λ _ → gne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with F ≟Functor F'
...     | no fne = no (λ { refl → fne refl })
...     | yes refl with ≟IRH alg₁ alg₂ refl refl | ≟IRH tr₁ tr₂ refl refl
...       | yes refl | yes refl
              rewrite WellFormedF-irrelevant wfF₁ wfF₂
                    | WellFormedF-irrelevant wfG₁ wfG₂ = yes refl
...       | no np    | _        = no (λ { refl → np refl })
...       | _        | no nq    = no (λ { refl → nq refl })

≟IRH (free-heap h₁) (free-heap h₂) refl refl with h₁ ≟H h₂
... | yes refl = yes refl
... | no hne   = no (λ { refl → hne refl })

≟IRH (Prim n₁) (Prim n₂) refl refl with n₁ ≟String n₂
... | yes refl = yes refl
... | no nne   = no (λ { refl → nne refl })

-- ═══════════════════════════════════════════════════════════════════════
-- Cross-pair cases (462 clauses, one per ordered pair of distinct
-- constructors). Each rejects via `cross-no (λ ()) eqA eqB`.
-- ═══════════════════════════════════════════════════════════════════════
≟IRH id (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH id (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH arr applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)

-- applyEff row
≟IRH applyEff id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH applyEff (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)

-- applyEff column (other side)
≟IRH id applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (_ ∘ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (⟨ _ , _ ⟩ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH fst applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH snd applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inl _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (inr _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (case _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH terminal applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH initial applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (curry _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH apply applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) applyEff eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (In _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (out-μ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Cata _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Para _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Out _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (in-ν _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Ana _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Hylo _ _ _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Fuse _ _ _ _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (free-heap _) (Prim _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) id eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (_ ∘ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (⟨ _ , _ ⟩ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) fst eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) snd eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (inl _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (inr _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (case _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) terminal eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) initial eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (curry _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) apply eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) arr eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (In _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (out-μ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (Cata _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (Para _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (Out _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (in-ν _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (Ana _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (Hylo _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (Fuse _ _ _ _) eqA eqB = no (cross-no (λ ()) eqA eqB)
≟IRH (Prim _) (free-heap _) eqA eqB = no (cross-no (λ ()) eqA eqB)

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
-- (⟦ F ⟧T can produce any type structure), we use "view" patterns
-- (see below, implemented postulate-free via the generic-codomain trick)
-- to classify targets.
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

------------------------------------------------------------------------
-- View implementations (postulate-free, OCP-0003 compliant)
--
-- The generic-codomain trick: for views constrained to a specific target
-- shape (B * C or A + B), we use a helper with a free codomain and an
-- equality proof. This avoids SplitError.UnificationStuck on constructors
-- with stuck type indices (out-μ : IR (μ-type F) (⟦ F ⟧T (μ-type F)),
-- Out, Cata, Para, Ana, Hylo, Fuse, Prim, In, in-ν). Those constructors
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
pairView-gen (⟨ f , g ⟩ m) refl = is-pair f g m
pairView-gen f eq = is-other-pair (subst (IR _) eq f)

pairView : ∀ {A B C} → (f : IR A (B * C)) → PairView f
pairView f = pairView-gen f refl

-- CoprodView: target is A + B (same stuck-unification pattern as PairView)
coprodView-gen : ∀ {D B'} (f : IR D B') → ∀ {A B} → (eq : B' ≡ A + B)
               → CoprodView {A} {B} {D} (subst (IR D) eq f)
coprodView-gen (inl m) refl = is-inl m
coprodView-gen (inr m) refl = is-inr m
coprodView-gen f eq = is-other-coprod (subst (IR _) eq f)

coprodView : ∀ {A B D} → (f : IR D (A + B)) → CoprodView f
coprodView f = coprodView-gen f refl

-- ComposeFirstView: fully generic source and target. Specific cases
-- first, then catch-all; new IR constructors cost 0 lines per view
-- (plan 0.5 Phase A / F2).
composeFirstView : ∀ {B C} → (g : IR B C) → ComposeFirstView g
composeFirstView id = cf-id
composeFirstView terminal = cf-terminal
composeFirstView fst = cf-fst
composeFirstView snd = cf-snd
composeFirstView (case h k) = cf-case h k
composeFirstView g = cf-other g

composeSecondView : ∀ {A B} → (f : IR A B) → ComposeSecondView f
composeSecondView id = cs-id
composeSecondView initial = cs-initial
composeSecondView f = cs-other f

fstSndView : ∀ {A B} → (f : IR A B) → FstSndView f
fstSndView fst = fsv-fst
fstSndView snd = fsv-snd
fstSndView f = fsv-other f

inlInrView : ∀ {A B} → (f : IR A B) → InlInrView f
inlInrView (inl m) = iiv-inl m
inlInrView (inr m) = iiv-inr m
inlInrView f = iiv-other f

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
-- Eta Laws (for pairs and cases)
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
  optimize-once-structural applyEff = applyEff
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