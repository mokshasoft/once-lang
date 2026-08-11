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
import Once.IRTy as II
open import Once.CCC.Machine.SMCore using (_≟H_)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟String_)
open import Once.SigOp.Info using (_≟SigOpInfo_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)

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

-- Helpers for ≟Type's matching-constructor cases.
-- Take inner Dec results explicitly to avoid `with`-blocks
-- (case-tree artifacts under --exact-split).

≟Type-*-aux : ∀ {A B C D} → Dec (A ≡ C) → Dec (B ≡ D)
            → Dec ((A * B) ≡ (C * D))
≟Type-*-aux (yes refl) (yes refl) = yes refl
≟Type-*-aux (yes refl) (no neq)   = no (λ { refl → neq refl })
≟Type-*-aux (no neq)   (yes _)    = no (λ { refl → neq refl })
≟Type-*-aux (no neq)   (no _)     = no (λ { refl → neq refl })

≟Type-+-aux : ∀ {A B C D} → Dec (A ≡ C) → Dec (B ≡ D)
            → Dec ((A + B) ≡ (C + D))
≟Type-+-aux (yes refl) (yes refl) = yes refl
≟Type-+-aux (yes refl) (no neq)   = no (λ { refl → neq refl })
≟Type-+-aux (no neq)   (yes _)    = no (λ { refl → neq refl })
≟Type-+-aux (no neq)   (no _)     = no (λ { refl → neq refl })

≟Type-⇒-aux : ∀ {A B C D q q'}
            → Dec (A ≡ C) → Dec (q ≡ q') → Dec (B ≡ D)
            → Dec ((A ⇒[ q ] B) ≡ (C ⇒[ q' ] D))
≟Type-⇒-aux (yes refl) (yes refl) (yes refl) = yes refl
≟Type-⇒-aux (yes refl) (yes refl) (no neq)   = no (λ { refl → neq refl })
≟Type-⇒-aux (yes refl) (no neq)   (yes _)    = no (λ { refl → neq refl })
≟Type-⇒-aux (yes refl) (no neq)   (no _)     = no (λ { refl → neq refl })
≟Type-⇒-aux (no neq)   (yes _)    (yes _)    = no (λ { refl → neq refl })
≟Type-⇒-aux (no neq)   (yes _)    (no _)     = no (λ { refl → neq refl })
≟Type-⇒-aux (no neq)   (no _)     (yes _)    = no (λ { refl → neq refl })
≟Type-⇒-aux (no neq)   (no _)     (no _)     = no (λ { refl → neq refl })

≟Type-μ-aux : ∀ {F G} → Dec (F ≡ G) → Dec (μ-type F ≡ μ-type G)
≟Type-μ-aux (yes refl) = yes refl
≟Type-μ-aux (no neq)   = no (λ { refl → neq refl })

≟Type-ν-aux : ∀ {F G} → Dec (F ≡ G) → Dec (ν-type F ≡ ν-type G)
≟Type-ν-aux (yes refl) = yes refl
≟Type-ν-aux (no neq)   = no (λ { refl → neq refl })

_≟Type_ : (A B : Type) → Dec (A ≡ B)
Unit ≟Type Unit = yes refl
Unit ≟Type Void = no (λ ())
Unit ≟Type (_ * _) = no (λ ())
Unit ≟Type (_ + _) = no (λ ())
Unit ≟Type (_ ⇒[ _ ] _) = no (λ ())
Unit ≟Type Int = no (λ ())
Unit ≟Type Float = no (λ ())
Unit ≟Type Str = no (λ ())
Unit ≟Type Buffer = no (λ ())
Void ≟Type Unit = no (λ ())
Void ≟Type Void = yes refl
Void ≟Type (_ * _) = no (λ ())
Void ≟Type (_ + _) = no (λ ())
Void ≟Type (_ ⇒[ _ ] _) = no (λ ())
Void ≟Type Int = no (λ ())
Void ≟Type Float = no (λ ())
Void ≟Type Str = no (λ ())
Void ≟Type Buffer = no (λ ())
(A * B) ≟Type Unit = no (λ ())
(A * B) ≟Type Void = no (λ ())
(A * B) ≟Type (C * D) = ≟Type-*-aux (A ≟Type C) (B ≟Type D)
(A * B) ≟Type (_ + _) = no (λ ())
(A * B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(A * B) ≟Type Int = no (λ ())
(A * B) ≟Type Float = no (λ ())
(A * B) ≟Type Str = no (λ ())
(A * B) ≟Type Buffer = no (λ ())
(A + B) ≟Type Unit = no (λ ())
(A + B) ≟Type Void = no (λ ())
(A + B) ≟Type (_ * _) = no (λ ())
(A + B) ≟Type (C + D) = ≟Type-+-aux (A ≟Type C) (B ≟Type D)
(A + B) ≟Type (_ ⇒[ _ ] _) = no (λ ())
(A + B) ≟Type Int = no (λ ())
(A + B) ≟Type Float = no (λ ())
(A + B) ≟Type Str = no (λ ())
(A + B) ≟Type Buffer = no (λ ())
(A ⇒[ q ] B) ≟Type Unit = no (λ ())
(A ⇒[ q ] B) ≟Type Void = no (λ ())
(A ⇒[ q ] B) ≟Type (_ * _) = no (λ ())
(A ⇒[ q ] B) ≟Type (_ + _) = no (λ ())
(A ⇒[ q ] B) ≟Type (C ⇒[ q' ] D) = ≟Type-⇒-aux (A ≟Type C) (q ≟k q') (B ≟Type D)
(A ⇒[ q ] B) ≟Type Int = no (λ ())
(A ⇒[ q ] B) ≟Type Float = no (λ ())
(A ⇒[ q ] B) ≟Type Str = no (λ ())
(A ⇒[ q ] B) ≟Type Buffer = no (λ ())
-- OCP-0003: Fix removed. Use μ-type/ν-type instead.
Int ≟Type Unit = no (λ ())
Int ≟Type Void = no (λ ())
Int ≟Type (_ * _) = no (λ ())
Int ≟Type (_ + _) = no (λ ())
Int ≟Type (_ ⇒[ _ ] _) = no (λ ())
Int ≟Type Int = yes refl
Int ≟Type Float = no (λ ())
Int ≟Type Str = no (λ ())
Int ≟Type Buffer = no (λ ())
Float ≟Type Unit = no (λ ())
Float ≟Type Void = no (λ ())
Float ≟Type (_ * _) = no (λ ())
Float ≟Type (_ + _) = no (λ ())
Float ≟Type (_ ⇒[ _ ] _) = no (λ ())
Float ≟Type Int = no (λ ())
Float ≟Type Float = yes refl
Float ≟Type Str = no (λ ())
Float ≟Type Buffer = no (λ ())
Str ≟Type Unit = no (λ ())
Str ≟Type Void = no (λ ())
Str ≟Type (_ * _) = no (λ ())
Str ≟Type (_ + _) = no (λ ())
Str ≟Type (_ ⇒[ _ ] _) = no (λ ())
Str ≟Type Int = no (λ ())
Str ≟Type Float = no (λ ())
Str ≟Type Str = yes refl
Str ≟Type Buffer = no (λ ())
Buffer ≟Type Unit = no (λ ())
Buffer ≟Type Void = no (λ ())
Buffer ≟Type (_ * _) = no (λ ())
Buffer ≟Type (_ + _) = no (λ ())
Buffer ≟Type (_ ⇒[ _ ] _) = no (λ ())
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
(μ-type F) ≟Type (μ-type G) = ≟Type-μ-aux (F ≟Functor G)
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
(ν-type F) ≟Type (μ-type _) = no (λ ())
(ν-type F) ≟Type (ν-type G) = ≟Type-ν-aux (F ≟Functor G)
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

-- Helpers for ≟Functor's matching-constructor cases.

≟Functor-K-aux : ∀ {A B} → Dec (A ≡ B) → Dec (K A ≡ K B)
≟Functor-K-aux (yes refl) = yes refl
≟Functor-K-aux (no neq)   = no (λ { refl → neq refl })

≟Functor-⊕-aux : ∀ {F₁ F₂ G₁ G₂}
               → Dec (F₁ ≡ G₁) → Dec (F₂ ≡ G₂)
               → Dec ((F₁ ⊕ F₂) ≡ (G₁ ⊕ G₂))
≟Functor-⊕-aux (yes refl) (yes refl) = yes refl
≟Functor-⊕-aux (yes refl) (no neq)   = no (λ { refl → neq refl })
≟Functor-⊕-aux (no neq)   (yes _)    = no (λ { refl → neq refl })
≟Functor-⊕-aux (no neq)   (no _)     = no (λ { refl → neq refl })

≟Functor-⊗-aux : ∀ {F₁ F₂ G₁ G₂}
               → Dec (F₁ ≡ G₁) → Dec (F₂ ≡ G₂)
               → Dec ((F₁ ⊗ F₂) ≡ (G₁ ⊗ G₂))
≟Functor-⊗-aux (yes refl) (yes refl) = yes refl
≟Functor-⊗-aux (yes refl) (no neq)   = no (λ { refl → neq refl })
≟Functor-⊗-aux (no neq)   (yes _)    = no (λ { refl → neq refl })
≟Functor-⊗-aux (no neq)   (no _)     = no (λ { refl → neq refl })

K A ≟Functor K B = ≟Functor-K-aux (A ≟Type B)
K _ ≟Functor Id = no (λ ())
K _ ≟Functor (_ ⊕ _) = no (λ ())
K _ ≟Functor (_ ⊗ _) = no (λ ())
Id ≟Functor K _ = no (λ ())
Id ≟Functor Id = yes refl
Id ≟Functor (_ ⊕ _) = no (λ ())
Id ≟Functor (_ ⊗ _) = no (λ ())
(F₁ ⊕ F₂) ≟Functor K _ = no (λ ())
(F₁ ⊕ F₂) ≟Functor Id = no (λ ())
(F₁ ⊕ F₂) ≟Functor (G₁ ⊕ G₂) = ≟Functor-⊕-aux (F₁ ≟Functor G₁) (F₂ ≟Functor G₂)
(F₁ ⊕ F₂) ≟Functor (_ ⊗ _) = no (λ ())
(F₁ ⊗ F₂) ≟Functor K _ = no (λ ())
(F₁ ⊗ F₂) ≟Functor Id = no (λ ())
(F₁ ⊗ F₂) ≟Functor (_ ⊕ _) = no (λ ())
(F₁ ⊗ F₂) ≟Functor (G₁ ⊗ G₂) = ≟Functor-⊗-aux (F₁ ≟Functor G₁) (F₂ ≟Functor G₂)

------------------------------------------------------------------------
-- IR equality (needed for eta uniqueness laws)
------------------------------------------------------------------------

-- IR equality — a decidable equality, by structural recursion.
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
-- proof-irrelevant (via `WellFormedFI-irrelevant`).
--
-- Cross-pair cases (different head constructors) are dispatched via
-- `ir-head`: a `subst₂`-invariant discriminator. If `ir-head f` and
-- `ir-head g` differ, any hypothetical equality would contradict it.

-- IR head discriminator.
data IRHead : Set where
  h-id h-∘ h-⟨,⟩ h-fst h-snd h-inl h-inr h-case
    h-terminal h-initial h-curry h-apply h-arr
    h-In h-out-μ h-Cata h-Para h-Out h-in-ν h-Ana h-Hylo h-Fuse
    h-free-heap h-SigOp h-const : IRHead

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
headTag h-Para      = 17
headTag h-Out       = 18
headTag h-in-ν      = 19
headTag h-Ana       = 20
headTag h-Hylo      = 21
headTag h-Fuse      = 22
headTag h-free-heap = 23
headTag h-SigOp      = 24
headTag h-const      = 25

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
headTag-inj h-Para      h-Para      _ = refl
headTag-inj h-Out       h-Out       _ = refl
headTag-inj h-in-ν      h-in-ν      _ = refl
headTag-inj h-Ana       h-Ana       _ = refl
headTag-inj h-Hylo      h-Hylo      _ = refl
headTag-inj h-Fuse      h-Fuse      _ = refl
headTag-inj h-free-heap h-free-heap _ = refl
headTag-inj h-SigOp      h-SigOp      _ = refl
headTag-inj h-const      h-const      _ = refl

_≟IRHead_ : (h₁ h₂ : IRHead) → Dec (h₁ ≡ h₂)
h₁ ≟IRHead h₂ with headTag h₁ Data.Nat.Properties.≟ headTag h₂
... | yes eq = yes (headTag-inj h₁ h₂ eq)
... | no  ne = no (λ heq → ne (cong headTag heq))

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
ir-head (SigOp _) = h-SigOp
ir-head (const _ _) = h-const

-- subst₂ for IR.
subst₂-IR : ∀ {A B A' B'} → A ≡ A' → B ≡ B' → IR A B → IR A' B'
subst₂-IR refl refl f = f

-- Plan 0.52 M2: SigOp decidable equality over ERASED objects. `⌊_⌋` is not
-- injective (drops the arrow grade), so the object equalities `eqA/eqB` cannot
-- be `refl`-matched. Instead extract the SigOp's Type-PARAMETERS (which ARE
-- recoverable — they live in the `SigOpInfo`) and compare via `≟Type`.
uipK : ∀ {ℓ} {A : Set ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
uipK refl refl = refl

sigop-dom : ∀ {X Y} → IR X Y → Maybe Type
sigop-dom (SigOp {A} {B} _) = just A
sigop-dom _ = nothing

sigop-cod : ∀ {X Y} → IR X Y → Maybe Type
sigop-cod (SigOp {A} {B} _) = just B
sigop-cod _ = nothing

sigop-dom-subst : ∀ {X Y X' Y'} (p : X ≡ X') (q : Y ≡ Y') (f : IR X Y)
                → sigop-dom (subst₂-IR p q f) ≡ sigop-dom f
sigop-dom-subst refl refl f = refl

sigop-cod-subst : ∀ {X Y X' Y'} (p : X ≡ X') (q : Y ≡ Y') (f : IR X Y)
                → sigop-cod (subst₂-IR p q f) ≡ sigop-cod f
sigop-cod-subst refl refl f = refl

-- head is preserved under subst₂-IR.
ir-head-subst₂ : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') (f : IR A B)
               → ir-head (subst₂-IR p q f) ≡ ir-head f
ir-head-subst₂ refl refl _ = refl

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

-- Decidable comparison modulo type-index equalities.
-- Result type: `Dec (f ≡ subst₂-IR (sym eqA) (sym eqB) g)` — when
-- eqA, eqB are refl, this reduces to `Dec (f ≡ g)`.
--
-- Plan 0.5 Phase B / F1: split into `≟IRH` wrapper (head dispatch)
-- and `≟IRH-diag` helper (24 same-head clauses). The wrapper compares
-- heads first: if they differ, reject via `cross-no`. If they agree,
-- delegate to `≟IRH-diag`. Off-diagonal pairs inside `≟IRH-diag` are
-- covered automatically by Agda — the `heq` premise type is a specific
-- absurd equation (e.g. `h-id ≡ h-∘`) for those cases.
≟IRH : ∀ {A B A' B'} (f : IR A B) (g : IR A' B')
     → (eqA : A ≡ A') (eqB : B ≡ B')
     → Dec (f ≡ subst₂-IR (sym eqA) (sym eqB) g)
≟IRH-diag : ∀ {A B A' B'} (f : IR A B) (g : IR A' B')
          → ir-head f ≡ ir-head g
          → (eqA : A ≡ A') (eqB : B ≡ B')
          → Dec (f ≡ subst₂-IR (sym eqA) (sym eqB) g)

-- Helper: dispatch ≟IRH on the head-equality decision (no-with form).
≟IRH-aux : ∀ {A B A' B'} (f : IR A B) (g : IR A' B')
         → Dec (ir-head f ≡ ir-head g)
         → (eqA : A ≡ A') (eqB : B ≡ B')
         → Dec (f ≡ subst₂-IR (sym eqA) (sym eqB) g)
≟IRH-aux f g (yes heq) eqA eqB = ≟IRH-diag f g heq eqA eqB
≟IRH-aux f g (no hne)  eqA eqB = no (cross-no hne eqA eqB)

≟IRH f g eqA eqB = ≟IRH-aux f g (ir-head f ≟IRHead ir-head g) eqA eqB

_≟IR_ : ∀ {A B} → (f g : IR A B) → Dec (f ≡ g)
f ≟IR g = ≟IRH f g refl refl

------------------------------------------------------------------------
-- D062: decidable equality for the natural transform (`NatTr`) carried by
-- Fuse/Hylo. Same head-tag dispatch as `≟IRH`: off-diagonal pairs inside
-- `≟NatTr-diag` are pruned by Agda because the `heq` premise is an absurd
-- ℕ-equation there. The functor indices are constructor-headed, so the
-- recursive subterms always share their index (no hidden existentials).
------------------------------------------------------------------------

nt-headTag : ∀ {G F} → NatTr G F → ℕ
nt-headTag ntId         = 0
nt-headTag (ntK _)      = 1
nt-headTag (ntFst _)    = 2
nt-headTag (ntSnd _)    = 3
nt-headTag (ntCase _ _) = 4
nt-headTag (ntInl _)    = 5
nt-headTag (ntInr _)    = 6
nt-headTag (ntPair _ _) = 7

_≟NatTr_    : ∀ {G F} (t₁ t₂ : NatTr G F) → Dec (t₁ ≡ t₂)
≟NatTr-aux  : ∀ {G F} (t₁ t₂ : NatTr G F)
            → Dec (nt-headTag t₁ ≡ nt-headTag t₂) → Dec (t₁ ≡ t₂)
≟NatTr-diag : ∀ {G F} (t₁ t₂ : NatTr G F)
            → nt-headTag t₁ ≡ nt-headTag t₂ → Dec (t₁ ≡ t₂)

t₁ ≟NatTr t₂ = ≟NatTr-aux t₁ t₂ (nt-headTag t₁ Data.Nat.Properties.≟ nt-headTag t₂)

≟NatTr-aux t₁ t₂ (yes heq) = ≟NatTr-diag t₁ t₂ heq
≟NatTr-aux t₁ t₂ (no hne)  = no (λ eq → hne (cong nt-headTag eq))

≟NatTr-diag ntId ntId _ = yes refl
≟NatTr-diag (ntK i) (ntK j) _ with ≟IRH i j refl refl
... | yes refl = yes refl
... | no ne    = no (λ { refl → ne refl })
≟NatTr-diag (ntFst t) (ntFst u) _ with t ≟NatTr u
... | yes refl = yes refl
... | no ne    = no (λ { refl → ne refl })
≟NatTr-diag (ntSnd t) (ntSnd u) _ with t ≟NatTr u
... | yes refl = yes refl
... | no ne    = no (λ { refl → ne refl })
≟NatTr-diag (ntCase t₁ u₁) (ntCase t₂ u₂) _ with t₁ ≟NatTr t₂ | u₁ ≟NatTr u₂
... | yes refl | yes refl = yes refl
... | no ne    | _        = no (λ { refl → ne refl })
... | _        | no ne    = no (λ { refl → ne refl })
≟NatTr-diag (ntInl t) (ntInl u) _ with t ≟NatTr u
... | yes refl = yes refl
... | no ne    = no (λ { refl → ne refl })
≟NatTr-diag (ntInr t) (ntInr u) _ with t ≟NatTr u
... | yes refl = yes refl
... | no ne    = no (λ { refl → ne refl })
≟NatTr-diag (ntPair t₁ u₁) (ntPair t₂ u₂) _ with t₁ ≟NatTr t₂ | u₁ ≟NatTr u₂
... | yes refl | yes refl = yes refl
... | no ne    | _        = no (λ { refl → ne refl })
... | _        | no ne    = no (λ { refl → ne refl })

------------------------------------------------------------------------
-- Index-injectivity helpers for diagonal cases involving recursive types.
------------------------------------------------------------------------

μ-inj : ∀ {F F'} → μ-type F ≡ μ-type F' → F ≡ F'
μ-inj refl = refl

ν-inj : ∀ {F F'} → ν-type F ≡ ν-type F' → F ≡ F'
ν-inj refl = refl

-- ═══════════════════════════════════════════════════════════════════════
-- Diagonal-case helpers (avoid nested with-blocks under --exact-split).
-- Each helper takes the relevant sub-Dec results explicitly and is
-- exhaustively pattern-matched.
-- ═══════════════════════════════════════════════════════════════════════

≟IRH-∘-inner : ∀ {A B D} (g₁ g₂ : IR B D) (f₁ f₂ : IR A B)
             → Dec (g₁ ≡ g₂) → Dec (f₁ ≡ f₂)
             → Dec (g₁ ∘ f₁ ≡ g₂ ∘ f₂)
≟IRH-∘-inner g₁ g₂ f₁ f₂ (yes refl) (yes refl) = yes refl
≟IRH-∘-inner g₁ g₂ f₁ f₂ (yes refl) (no nq)    = no (λ { refl → nq refl })
≟IRH-∘-inner g₁ g₂ f₁ f₂ (no np)    (yes _)    = no (λ { refl → np refl })
≟IRH-∘-inner g₁ g₂ f₁ f₂ (no np)    (no _)     = no (λ { refl → np refl })

≟IRH-∘-aux : ∀ {A B B' D}
           → (g₁ : IR B D) (f₁ : IR A B)
           → (g₂ : IR B' D) (f₂ : IR A B')
           → Dec (B ≡ B')
           → Dec (g₁ ∘ f₁ ≡ g₂ ∘ f₂)
≟IRH-∘-aux g₁ f₁ g₂ f₂ (no neq)   = no (λ { refl → neq refl })
≟IRH-∘-aux g₁ f₁ g₂ f₂ (yes refl) =
  ≟IRH-∘-inner g₁ g₂ f₁ f₂ (≟IRH g₁ g₂ refl refl) (≟IRH f₁ f₂ refl refl)

≟IRH-⟨,⟩-aux : ∀ {A B C} (f₁ f₂ : IR A B) (g₁ g₂ : IR A C) (m₁ m₂ : AllocMode)
             → Dec (f₁ ≡ f₂) → Dec (g₁ ≡ g₂) → Dec (m₁ ≡ m₂)
             → Dec (⟨ f₁ , g₁ ⟩ m₁ ≡ ⟨ f₂ , g₂ ⟩ m₂)
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (yes refl) (yes refl) (yes refl) = yes refl
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (yes refl) (yes refl) (no nm)    = no (λ { refl → nm refl })
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (yes refl) (no nq)    (yes _)    = no (λ { refl → nq refl })
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (yes refl) (no nq)    (no _)     = no (λ { refl → nq refl })
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (no np)    (yes _)    (yes _)    = no (λ { refl → np refl })
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (no np)    (yes _)    (no _)     = no (λ { refl → np refl })
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (no np)    (no _)     (yes _)    = no (λ { refl → np refl })
≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂ (no np)    (no _)     (no _)     = no (λ { refl → np refl })

≟IRH-case-aux : ∀ {A B C} (f₁ f₂ : IR A C) (g₁ g₂ : IR B C)
              → Dec (f₁ ≡ f₂) → Dec (g₁ ≡ g₂)
              → Dec (case f₁ g₁ ≡ case f₂ g₂)
≟IRH-case-aux f₁ f₂ g₁ g₂ (yes refl) (yes refl) = yes refl
≟IRH-case-aux f₁ f₂ g₁ g₂ (yes refl) (no nq)    = no (λ { refl → nq refl })
≟IRH-case-aux f₁ f₂ g₁ g₂ (no np)    (yes _)    = no (λ { refl → np refl })
≟IRH-case-aux f₁ f₂ g₁ g₂ (no np)    (no _)     = no (λ { refl → np refl })

≟IRH-curry-aux : ∀ {A B C} (f₁ f₂ : IR (A * B) C) (m₁ m₂ : AllocMode)
               → Dec (f₁ ≡ f₂) → Dec (m₁ ≡ m₂)
               → Dec (curry {A} {B} {C} f₁ m₁ ≡ curry f₂ m₂)
≟IRH-curry-aux f₁ f₂ m₁ m₂ (yes refl) (yes refl) = yes refl
≟IRH-curry-aux f₁ f₂ m₁ m₂ (yes refl) (no nm)    = no (λ { refl → nm refl })
≟IRH-curry-aux f₁ f₂ m₁ m₂ (no np)    (yes _)    = no (λ { refl → np refl })
≟IRH-curry-aux f₁ f₂ m₁ m₂ (no np)    (no _)     = no (λ { refl → np refl })

-- Hylo helper: takes both alg and coalg Dec results; uses rewrite
-- on WellFormedFI-irrelevant for the matched-functor case.
≟IRH-Hylo-inner : ∀ {F G B}
                → (wfF₁ wfF₂ : _) (wfG₁ wfG₂ : _)
                → (alg₁ alg₂ : IR (⟦ F ⟧TI B) B)
                → (coalg₁ coalg₂ : NatTr G F)
                → Dec (alg₁ ≡ alg₂) → Dec (coalg₁ ≡ coalg₂)
                → Dec (Hylo {F} {G} wfF₁ wfG₁ alg₁ coalg₁
                       ≡ Hylo wfF₂ wfG₂ alg₂ coalg₂)
≟IRH-Hylo-inner wfF₁ wfF₂ wfG₁ wfG₂ alg₁ alg₂ coalg₁ coalg₂ (yes refl) (yes refl)
  rewrite WellFormedFI-irrelevant wfF₁ wfF₂
        | WellFormedFI-irrelevant wfG₁ wfG₂ = yes refl
≟IRH-Hylo-inner _ _ _ _ _ _ _ _ (yes refl) (no nq) = no (λ { refl → nq refl })
≟IRH-Hylo-inner _ _ _ _ _ _ _ _ (no np)    (yes _) = no (λ { refl → np refl })
≟IRH-Hylo-inner _ _ _ _ _ _ _ _ (no np)    (no _)  = no (λ { refl → np refl })

≟IRH-Fuse-inner : ∀ {F G B}
                → (wfF₁ wfF₂ : _) (wfG₁ wfG₂ : _)
                → (alg₁ alg₂ : IR (⟦ F ⟧TI B) B)
                → (tr₁ tr₂ : NatTr G F)
                → Dec (alg₁ ≡ alg₂) → Dec (tr₁ ≡ tr₂)
                → Dec (Fuse {F} {G} wfF₁ wfG₁ alg₁ tr₁
                       ≡ Fuse wfF₂ wfG₂ alg₂ tr₂)
≟IRH-Fuse-inner wfF₁ wfF₂ wfG₁ wfG₂ alg₁ alg₂ tr₁ tr₂ (yes refl) (yes refl)
  rewrite WellFormedFI-irrelevant wfF₁ wfF₂
        | WellFormedFI-irrelevant wfG₁ wfG₂ = yes refl
≟IRH-Fuse-inner _ _ _ _ _ _ _ _ (yes refl) (no nq) = no (λ { refl → nq refl })
≟IRH-Fuse-inner _ _ _ _ _ _ _ _ (no np)    (yes _) = no (λ { refl → np refl })
≟IRH-Fuse-inner _ _ _ _ _ _ _ _ (no np)    (no _)  = no (λ { refl → np refl })

-- ═══════════════════════════════════════════════════════════════════════
-- Diagonal (same-constructor) cases
-- ═══════════════════════════════════════════════════════════════════════

-- id
≟IRH-diag id id _ refl refl = yes refl

-- _∘_: compare the intermediate (middle) type first, then sub-IRs
≟IRH-diag (_∘_ {_} {B} g₁ f₁) (_∘_ {_} {B'} g₂ f₂) _ refl refl =
  ≟IRH-∘-aux g₁ f₁ g₂ f₂ (B ≟IRTy B')

-- ⟨_,_⟩: B * C equality refl-unifies both component types
≟IRH-diag (⟨ f₁ , g₁ ⟩ m₁) (⟨ f₂ , g₂ ⟩ m₂) _ refl refl =
  ≟IRH-⟨,⟩-aux f₁ f₂ g₁ g₂ m₁ m₂
    (≟IRH f₁ f₂ refl refl) (≟IRH g₁ g₂ refl refl) (m₁ ≟AllocMode m₂)

≟IRH-diag fst fst _ refl refl = yes refl
≟IRH-diag snd snd _ refl refl = yes refl

≟IRH-diag (inl m₁) (inl m₂) _ refl refl with m₁ ≟AllocMode m₂
... | yes refl = yes refl
... | no nm    = no (λ { refl → nm refl })

≟IRH-diag (inr m₁) (inr m₂) _ refl refl with m₁ ≟AllocMode m₂
... | yes refl = yes refl
... | no nm    = no (λ { refl → nm refl })

≟IRH-diag (case f₁ g₁) (case f₂ g₂) _ refl refl =
  ≟IRH-case-aux f₁ f₂ g₁ g₂ (≟IRH f₁ f₂ refl refl) (≟IRH g₁ g₂ refl refl)

≟IRH-diag terminal terminal _ refl refl = yes refl
≟IRH-diag initial initial _ refl refl = yes refl

≟IRH-diag (curry f₁ m₁) (curry f₂ m₂) _ refl refl =
  ≟IRH-curry-aux f₁ f₂ m₁ m₂ (≟IRH f₁ f₂ refl refl) (m₁ ≟AllocMode m₂)

≟IRH-diag apply apply _ refl refl = yes refl

-- In: eqB : μ-type F ≡ μ-type F' gives the Functor tag
≟IRH-diag (In {F} wf₁ m₁) (In {F'} wf₂ m₂) _ eqA eqB with F ≟IRFun F'
... | no fne = no (λ _ → fne (μ-inj eqB))
... | yes refl with m₁ ≟AllocMode m₂ | eqA | eqB
...   | yes refl | refl | refl rewrite WellFormedFI-irrelevant wf₁ wf₂ = yes refl
...   | no nm    | refl | refl = no (λ { refl → nm refl })

-- out-μ: eqA : μ-type F ≡ μ-type F'
≟IRH-diag (out-μ {F} wf₁) (out-μ {F'} wf₂) _ eqA eqB with F ≟IRFun F'
... | no fne = no (λ _ → fne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl rewrite WellFormedFI-irrelevant wf₁ wf₂ = yes refl

-- Cata: eqA : μ-type F ≡ μ-type F', eqB : A ≡ A'
≟IRH-diag (Cata {F} wf₁ alg₁) (Cata {F'} wf₂ alg₂) _ eqA eqB
  with F ≟IRFun F'
... | no fne = no (λ _ → fne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with ≟IRH alg₁ alg₂ refl refl
...     | yes refl rewrite WellFormedFI-irrelevant wf₁ wf₂ = yes refl
...     | no np = no (λ { refl → np refl })

-- Para: similar
≟IRH-diag (Para {F} wf₁ alg₁) (Para {F'} wf₂ alg₂) _ eqA eqB
  with F ≟IRFun F'
... | no fne = no (λ _ → fne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with ≟IRH alg₁ alg₂ refl refl
...     | yes refl rewrite WellFormedFI-irrelevant wf₁ wf₂ = yes refl
...     | no np = no (λ { refl → np refl })

-- Out: eqA : ν-type F ≡ ν-type F'
≟IRH-diag (Out {F} wf₁) (Out {F'} wf₂) _ eqA eqB with F ≟IRFun F'
... | no fne = no (λ _ → fne (ν-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl rewrite WellFormedFI-irrelevant wf₁ wf₂ = yes refl

-- in-ν: eqB : ν-type F ≡ ν-type F'
≟IRH-diag (in-ν {F} wf₁ m₁) (in-ν {F'} wf₂ m₂) _ eqA eqB
  with F ≟IRFun F'
... | no fne = no (λ _ → fne (ν-inj eqB))
... | yes refl with m₁ ≟AllocMode m₂ | eqA | eqB
...   | yes refl | refl | refl rewrite WellFormedFI-irrelevant wf₁ wf₂ = yes refl
...   | no nm    | refl | refl = no (λ { refl → nm refl })

-- Ana: eqB : ν-type F ≡ ν-type F'
≟IRH-diag (Ana {F} wf₁ coalg₁) (Ana {F'} wf₂ coalg₂) _ eqA eqB
  with F ≟IRFun F'
... | no fne = no (λ _ → fne (ν-inj eqB))
... | yes refl with eqA | eqB
...   | refl | refl with ≟IRH coalg₁ coalg₂ refl refl
...     | yes refl rewrite WellFormedFI-irrelevant wf₁ wf₂ = yes refl
...     | no np = no (λ { refl → np refl })

-- Hylo: eqA : μ-type G ≡ μ-type G', eqB : B ≡ B'.
-- F is internal to the alg's type; require F ≟ F' separately.
-- Outer with-blocks on the Functor decisions remain (no warning —
-- exhaustive on Dec). The inner sub-IR with-block is extracted into
-- ≟IRH-Hylo-inner above.
≟IRH-diag (Hylo {F} {G} wfF₁ wfG₁ alg₁ coalg₁)
     (Hylo {F'} {G'} wfF₂ wfG₂ alg₂ coalg₂) _ eqA eqB
  with G ≟IRFun G'
... | no gne = no (λ _ → gne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with F ≟IRFun F'
...     | no fne  = no (λ { refl → fne refl })
...     | yes refl =
            ≟IRH-Hylo-inner wfF₁ wfF₂ wfG₁ wfG₂ alg₁ alg₂ coalg₁ coalg₂
              (≟IRH alg₁ alg₂ refl refl) (coalg₁ ≟NatTr coalg₂)

-- Fuse: similar shape to Hylo
≟IRH-diag (Fuse {F} {G} wfF₁ wfG₁ alg₁ tr₁)
     (Fuse {F'} {G'} wfF₂ wfG₂ alg₂ tr₂) _ eqA eqB
  with G ≟IRFun G'
... | no gne = no (λ _ → gne (μ-inj eqA))
... | yes refl with eqA | eqB
...   | refl | refl with F ≟IRFun F'
...     | no fne = no (λ { refl → fne refl })
...     | yes refl =
            ≟IRH-Fuse-inner wfF₁ wfF₂ wfG₁ wfG₂ alg₁ alg₂ tr₁ tr₂
              (≟IRH alg₁ alg₂ refl refl) (tr₁ ≟NatTr tr₂)

≟IRH-diag (free-heap h₁) (free-heap h₂) _ refl refl with h₁ ≟H h₂
... | yes refl = yes refl
... | no hne   = no (λ { refl → hne refl })

≟IRH-diag (SigOp {A₁} {B₁} si₁) (SigOp {A₂} {B₂} si₂) _ eqA eqB with A₁ ≟Type A₂ | B₁ ≟Type B₂
... | no ne  | _     = no (λ heq → ne (just-injective (trans (cong sigop-dom heq) (sigop-dom-subst (sym eqA) (sym eqB) (SigOp si₂)))))
... | yes _  | no ne = no (λ heq → ne (just-injective (trans (cong sigop-cod heq) (sigop-cod-subst (sym eqA) (sym eqB) (SigOp si₂)))))
... | yes refl | yes refl rewrite uipK eqA refl | uipK eqB refl with si₁ ≟SigOpInfo si₂
...   | yes refl = yes refl
...   | no ne    = no (λ { refl → ne refl })

-- Plan 0.11: const ctor decidable equality.
-- Postulated for now — proper discharge requires decidable equality
-- on FitsInReg + per-register-fittable-type decidable equality on the
-- proof-level and machine-level values. Tractable but adds scope.
-- Trusted-base entry until then.
≟IRH-diag (const p₁ v₁) (const p₂ v₂) _ refl refl =
  ≟const-irrelevant p₁ p₂ v₁ v₂
  where
    open import Once.IRTy using (⟦_⟧-baseI)
    open import Once.Word using (Carrier)
    postulate
      ≟const-irrelevant : ∀ (q₁ q₂ : FitsInRegI _) (u₁ u₂ : ⟦ Carrier ⟧-baseI _) →
                          Dec (const q₁ u₁ ≡ const q₂ u₂)

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
is-Void (ν-type _)   = false
is-Void Int          = false
is-Void Float        = false
is-Void Str          = false
is-Void Buffer       = false

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
isUnitType (ν-type _)   = false
isUnitType Int          = false
isUnitType Float        = false
isUnitType Str          = false
isUnitType Buffer       = false

isVoidType : Type → Bool
isVoidType Unit         = false
isVoidType Void         = true
isVoidType (_ * _)      = false
isVoidType (_ + _)      = false
isVoidType (_ ⇒[ _ ] _) = false
isVoidType (μ-type _)   = false
isVoidType (ν-type _)   = false
isVoidType Int          = false
isVoidType Float        = false
isVoidType Str          = false
isVoidType Buffer       = false

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
  is-pair : ∀ {A B C} (f : IR A B) (g : IR A C) m → PairView (⟨ f , g ⟩ m)
  is-other-pair : ∀ {A B C} (f : IR A (B * C)) → PairView f

-- View: classify IR terms targeting a coproduct type
-- Note: inl : IR A (A + B), inr : IR B (A + B) - source must match component
data CoprodView : ∀ {A B D : IRTy} → IR D (A + B) → Set where
  is-inl : ∀ {A B} m → CoprodView {A} {B} {A} (inl m)
  is-inr : ∀ {A B} m → CoprodView {A} {B} {B} (inr m)
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
  iiv-inl : ∀ {X Y} m → InlInrView {X} {X + Y} (inl m)
  iiv-inr : ∀ {X Y} m → InlInrView {Y} {X + Y} (inr m)
  iiv-other : ∀ {A B} (f : IR A B) → InlInrView f

------------------------------------------------------------------------
-- View implementations (OCP-0003 compliant)
--
-- The generic-codomain trick: for views constrained to a specific target
-- shape (B * C or A + B), we use a helper with a free codomain and an
-- equality proof. This avoids SplitError.UnificationStuck on constructors
-- with stuck type indices (out-μ : IR (μ-type F) (⟦ F ⟧T (μ-type F)),
-- Out, Cata, Para, Ana, Hylo, Fuse, SigOp, In, in-ν). Those constructors
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
pairView-gen id              eq = is-other-pair (subst (IR _) eq id)
pairView-gen (f ∘ g)         eq = is-other-pair (subst (IR _) eq (f ∘ g))
pairView-gen fst             eq = is-other-pair (subst (IR _) eq fst)
pairView-gen snd             eq = is-other-pair (subst (IR _) eq snd)
pairView-gen (inl m)         eq = is-other-pair (subst (IR _) eq (inl m))
pairView-gen (inr m)         eq = is-other-pair (subst (IR _) eq (inr m))
pairView-gen (case f g)      eq = is-other-pair (subst (IR _) eq (case f g))
pairView-gen terminal        eq = is-other-pair (subst (IR _) eq terminal)
pairView-gen initial         eq = is-other-pair (subst (IR _) eq initial)
pairView-gen (curry f m)     eq = is-other-pair (subst (IR _) eq (curry f m))
pairView-gen apply           eq = is-other-pair (subst (IR _) eq apply)
pairView-gen (In wf m)       eq = is-other-pair (subst (IR _) eq (In wf m))
pairView-gen (out-μ wf)      eq = is-other-pair (subst (IR _) eq (out-μ wf))
pairView-gen (Cata wf alg)   eq = is-other-pair (subst (IR _) eq (Cata wf alg))
pairView-gen (Para wf alg)   eq = is-other-pair (subst (IR _) eq (Para wf alg))
pairView-gen (Out wf)        eq = is-other-pair (subst (IR _) eq (Out wf))
pairView-gen (in-ν wf m)     eq = is-other-pair (subst (IR _) eq (in-ν wf m))
pairView-gen (Ana wf coalg)  eq = is-other-pair (subst (IR _) eq (Ana wf coalg))
pairView-gen (Hylo wfF wfG alg coalg) eq = is-other-pair (subst (IR _) eq (Hylo wfF wfG alg coalg))
pairView-gen (Fuse wfF wfG alg tr)    eq = is-other-pair (subst (IR _) eq (Fuse wfF wfG alg tr))
pairView-gen (free-heap h)   eq = is-other-pair (subst (IR _) eq (free-heap h))
pairView-gen (SigOp si)      eq = is-other-pair (subst (IR _) eq (SigOp si))
pairView-gen (const p v) eq = is-other-pair (subst (IR _) eq (const p v))

pairView : ∀ {A B C} → (f : IR A (B * C)) → PairView f
pairView f = pairView-gen f refl

-- CoprodView: target is A + B (same stuck-unification pattern as PairView)
coprodView-gen : ∀ {D B'} (f : IR D B') → ∀ {A B} → (eq : B' ≡ A + B)
               → CoprodView {A} {B} {D} (subst (IR D) eq f)
coprodView-gen (inl m) refl = is-inl m
coprodView-gen (inr m) refl = is-inr m
coprodView-gen id              eq = is-other-coprod (subst (IR _) eq id)
coprodView-gen (f ∘ g)         eq = is-other-coprod (subst (IR _) eq (f ∘ g))
coprodView-gen (⟨ f , g ⟩ m)   eq = is-other-coprod (subst (IR _) eq (⟨ f , g ⟩ m))
coprodView-gen fst             eq = is-other-coprod (subst (IR _) eq fst)
coprodView-gen snd             eq = is-other-coprod (subst (IR _) eq snd)
coprodView-gen (case f g)      eq = is-other-coprod (subst (IR _) eq (case f g))
coprodView-gen terminal        eq = is-other-coprod (subst (IR _) eq terminal)
coprodView-gen initial         eq = is-other-coprod (subst (IR _) eq initial)
coprodView-gen (curry f m)     eq = is-other-coprod (subst (IR _) eq (curry f m))
coprodView-gen apply           eq = is-other-coprod (subst (IR _) eq apply)
coprodView-gen (In wf m)       eq = is-other-coprod (subst (IR _) eq (In wf m))
coprodView-gen (out-μ wf)      eq = is-other-coprod (subst (IR _) eq (out-μ wf))
coprodView-gen (Cata wf alg)   eq = is-other-coprod (subst (IR _) eq (Cata wf alg))
coprodView-gen (Para wf alg)   eq = is-other-coprod (subst (IR _) eq (Para wf alg))
coprodView-gen (Out wf)        eq = is-other-coprod (subst (IR _) eq (Out wf))
coprodView-gen (in-ν wf m)     eq = is-other-coprod (subst (IR _) eq (in-ν wf m))
coprodView-gen (Ana wf coalg)  eq = is-other-coprod (subst (IR _) eq (Ana wf coalg))
coprodView-gen (Hylo wfF wfG alg coalg) eq = is-other-coprod (subst (IR _) eq (Hylo wfF wfG alg coalg))
coprodView-gen (Fuse wfF wfG alg tr)    eq = is-other-coprod (subst (IR _) eq (Fuse wfF wfG alg tr))
coprodView-gen (free-heap h)   eq = is-other-coprod (subst (IR _) eq (free-heap h))
coprodView-gen (SigOp si)      eq = is-other-coprod (subst (IR _) eq (SigOp si))
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
composeFirstView (⟨ f , g ⟩ m)   = cf-other (⟨ f , g ⟩ m)
composeFirstView (inl m)         = cf-other (inl m)
composeFirstView (inr m)         = cf-other (inr m)
composeFirstView initial         = cf-other initial
composeFirstView (curry f m)     = cf-other (curry f m)
composeFirstView apply           = cf-other apply
composeFirstView (In wf m)       = cf-other (In wf m)
composeFirstView (out-μ wf)      = cf-other (out-μ wf)
composeFirstView (Cata wf alg)   = cf-other (Cata wf alg)
composeFirstView (Para wf alg)   = cf-other (Para wf alg)
composeFirstView (Out wf)        = cf-other (Out wf)
composeFirstView (in-ν wf m)     = cf-other (in-ν wf m)
composeFirstView (Ana wf coalg)  = cf-other (Ana wf coalg)
composeFirstView (Hylo wfF wfG alg coalg) = cf-other (Hylo wfF wfG alg coalg)
composeFirstView (Fuse wfF wfG alg tr)    = cf-other (Fuse wfF wfG alg tr)
composeFirstView (free-heap h)   = cf-other (free-heap h)
composeFirstView (SigOp si)      = cf-other (SigOp si)
composeFirstView (const p v) = cf-other (const p v)

composeSecondView : ∀ {A B} → (f : IR A B) → ComposeSecondView f
composeSecondView id             = cs-id
composeSecondView initial        = cs-initial
composeSecondView (f ∘ g)        = cs-other (f ∘ g)
composeSecondView (⟨ f , g ⟩ m)  = cs-other (⟨ f , g ⟩ m)
composeSecondView fst            = cs-other fst
composeSecondView snd            = cs-other snd
composeSecondView (inl m)        = cs-other (inl m)
composeSecondView (inr m)        = cs-other (inr m)
composeSecondView (case f g)     = cs-other (case f g)
composeSecondView terminal       = cs-other terminal
composeSecondView (curry f m)    = cs-other (curry f m)
composeSecondView apply          = cs-other apply
composeSecondView (In wf m)      = cs-other (In wf m)
composeSecondView (out-μ wf)     = cs-other (out-μ wf)
composeSecondView (Cata wf alg)  = cs-other (Cata wf alg)
composeSecondView (Para wf alg)  = cs-other (Para wf alg)
composeSecondView (Out wf)       = cs-other (Out wf)
composeSecondView (in-ν wf m)    = cs-other (in-ν wf m)
composeSecondView (Ana wf coalg) = cs-other (Ana wf coalg)
composeSecondView (Hylo wfF wfG alg coalg) = cs-other (Hylo wfF wfG alg coalg)
composeSecondView (Fuse wfF wfG alg tr)    = cs-other (Fuse wfF wfG alg tr)
composeSecondView (free-heap h)  = cs-other (free-heap h)
composeSecondView (SigOp si)     = cs-other (SigOp si)
composeSecondView (const p v) = cs-other (const p v)

fstSndView : ∀ {A B} → (f : IR A B) → FstSndView f
fstSndView fst             = fsv-fst
fstSndView snd             = fsv-snd
fstSndView id              = fsv-other id
fstSndView (f ∘ g)         = fsv-other (f ∘ g)
fstSndView (⟨ f , g ⟩ m)   = fsv-other (⟨ f , g ⟩ m)
fstSndView (inl m)         = fsv-other (inl m)
fstSndView (inr m)         = fsv-other (inr m)
fstSndView (case f g)      = fsv-other (case f g)
fstSndView terminal        = fsv-other terminal
fstSndView initial         = fsv-other initial
fstSndView (curry f m)     = fsv-other (curry f m)
fstSndView apply           = fsv-other apply
fstSndView (In wf m)       = fsv-other (In wf m)
fstSndView (out-μ wf)      = fsv-other (out-μ wf)
fstSndView (Cata wf alg)   = fsv-other (Cata wf alg)
fstSndView (Para wf alg)   = fsv-other (Para wf alg)
fstSndView (Out wf)        = fsv-other (Out wf)
fstSndView (in-ν wf m)     = fsv-other (in-ν wf m)
fstSndView (Ana wf coalg)  = fsv-other (Ana wf coalg)
fstSndView (Hylo wfF wfG alg coalg) = fsv-other (Hylo wfF wfG alg coalg)
fstSndView (Fuse wfF wfG alg tr)    = fsv-other (Fuse wfF wfG alg tr)
fstSndView (free-heap h)   = fsv-other (free-heap h)
fstSndView (SigOp si)      = fsv-other (SigOp si)
fstSndView (const p v) = fsv-other (const p v)

inlInrView : ∀ {A B} → (f : IR A B) → InlInrView f
inlInrView (inl m)         = iiv-inl m
inlInrView (inr m)         = iiv-inr m
inlInrView id              = iiv-other id
inlInrView (f ∘ g)         = iiv-other (f ∘ g)
inlInrView (⟨ f , g ⟩ m)   = iiv-other (⟨ f , g ⟩ m)
inlInrView fst             = iiv-other fst
inlInrView snd             = iiv-other snd
inlInrView (case f g)      = iiv-other (case f g)
inlInrView terminal        = iiv-other terminal
inlInrView initial         = iiv-other initial
inlInrView (curry f m)     = iiv-other (curry f m)
inlInrView apply           = iiv-other apply
inlInrView (In wf m)       = iiv-other (In wf m)
inlInrView (out-μ wf)      = iiv-other (out-μ wf)
inlInrView (Cata wf alg)   = iiv-other (Cata wf alg)
inlInrView (Para wf alg)   = iiv-other (Para wf alg)
inlInrView (Out wf)        = iiv-other (Out wf)
inlInrView (in-ν wf m)     = iiv-other (in-ν wf m)
inlInrView (Ana wf coalg)  = iiv-other (Ana wf coalg)
inlInrView (Hylo wfF wfG alg coalg) = iiv-other (Hylo wfF wfG alg coalg)
inlInrView (Fuse wfF wfG alg tr)    = iiv-other (Fuse wfF wfG alg tr)
inlInrView (free-heap h)   = iiv-other (free-heap h)
inlInrView (SigOp si)      = iiv-other (SigOp si)
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
-- D062: a Fuse/Hylo's natural transform may carry effectful constant-leaf
-- (ntK) IRs; recurse into them.
has-effect?-nt : ∀ {G F} → NatTr G F → Bool
has-effect? id              = false
has-effect? (g ∘ f)         = has-effect? g ∨ has-effect? f
has-effect? fst             = false
has-effect? snd             = false
has-effect? (⟨ f , g ⟩ _)   = has-effect? f ∨ has-effect? g
has-effect? (inl _)         = false
has-effect? (inr _)         = false
has-effect? (case f g)      = has-effect? f ∨ has-effect? g
has-effect? terminal        = false
has-effect? initial         = false
has-effect? (curry f _)     = has-effect? f
-- `apply` invokes a closure that is only known at runtime; that closure may
-- contain any SigOp (e.g. an `exit`/`emit` action threaded through a thunk),
-- so an `apply` is conservatively treated as potentially effectful. This is
-- what stops the optimizer collapsing an effect-bearing action thunk
-- (`applyEff ∘ ⟨closure,x⟩ : _ → Unit`) to `terminal`.
has-effect? apply           = true
has-effect? (SigOp _)       = true
has-effect? (const _ _)   = false
has-effect? (free-heap _)   = true
has-effect? (In _ _)        = false
has-effect? (out-μ _)       = false
has-effect? (Cata _ alg)    = has-effect? alg
has-effect? (Para _ alg)    = has-effect? alg
has-effect? (Out _)         = false
has-effect? (in-ν _ _)      = false
has-effect? (Ana _ coalg)   = has-effect? coalg
has-effect? (Hylo _ _ alg t) = has-effect? alg ∨ has-effect?-nt t
has-effect? (Fuse _ _ alg t) = has-effect? alg ∨ has-effect?-nt t

has-effect?-nt ntId         = false
has-effect?-nt (ntK ir)     = has-effect? ir
has-effect?-nt (ntFst t)    = has-effect?-nt t
has-effect?-nt (ntSnd t)    = has-effect?-nt t
has-effect?-nt (ntCase t u) = has-effect?-nt t ∨ has-effect?-nt u
has-effect?-nt (ntInl t)    = has-effect?-nt t
has-effect?-nt (ntInr t)    = has-effect?-nt t
has-effect?-nt (ntPair t u) = has-effect?-nt t ∨ has-effect?-nt u

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
-- Plan 0.53: preserve the pair's original AllocMode `m` instead of forcing
-- `Stack`. Forcing `Stack` was the same class of mode leak as the closure-env
-- fix: an optimized pair that escapes (e.g. captured by a closure) must stay on
-- the heap in heap-mode. The eta case `⟨fst,snd⟩ → id` is mode-independent.
optimize-pair-aux : ∀ {A B C} (m : AllocMode) (f : IR C A) (g : IR C B)
                  → FstSndView f → FstSndView g → IR C (A * B)
optimize-pair-aux m f g fsv-fst       fsv-snd       = id
optimize-pair-aux m f g fsv-fst       fsv-fst       = ⟨ f , g ⟩ m
optimize-pair-aux m f g fsv-fst       (fsv-other _) = ⟨ f , g ⟩ m
optimize-pair-aux m f g fsv-snd       fsv-fst       = ⟨ f , g ⟩ m
optimize-pair-aux m f g fsv-snd       fsv-snd       = ⟨ f , g ⟩ m
optimize-pair-aux m f g fsv-snd       (fsv-other _) = ⟨ f , g ⟩ m
optimize-pair-aux m f g (fsv-other _) fsv-fst       = ⟨ f , g ⟩ m
optimize-pair-aux m f g (fsv-other _) fsv-snd       = ⟨ f , g ⟩ m
optimize-pair-aux m f g (fsv-other _) (fsv-other _) = ⟨ f , g ⟩ m

optimize-pair : ∀ {A B C} → AllocMode → IR C A → IR C B → IR C (A * B)
optimize-pair m f g = optimize-pair-aux m f g (fstSndView f) (fstSndView g)

-- | Optimize case construction
--   [ inl , inr ] = id (eta)
optimize-case-aux : ∀ {A B C} (f : IR A C) (g : IR B C)
                  → InlInrView f → InlInrView g → IR (A + B) C
optimize-case-aux f g (iiv-inl _)   (iiv-inr _)   = id
optimize-case-aux f g (iiv-inl _)   (iiv-inl _)   = case f g
optimize-case-aux f g (iiv-inl _)   (iiv-other _) = case f g
optimize-case-aux f g (iiv-inr _)   (iiv-inl _)   = case f g
optimize-case-aux f g (iiv-inr _)   (iiv-inr _)   = case f g
optimize-case-aux f g (iiv-inr _)   (iiv-other _) = case f g
optimize-case-aux f g (iiv-other _) (iiv-inl _)   = case f g
optimize-case-aux f g (iiv-other _) (iiv-inr _)   = case f g
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
  optimize-once-structural (⟨ f , g ⟩ m) = optimize-pair m (optimize-once f) (optimize-once g)
  -- | inl with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (inl {A} {B} m) with A ≟IRTy II.Void
  ... | yes refl = initial
  ... | no _     = inl m
  -- | inr with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (inr {A} {B} m) with B ≟IRTy II.Void
  ... | yes refl = initial
  ... | no _     = inr m
  optimize-once-structural (case f g) = optimize-case (optimize-once f) (optimize-once g)
  optimize-once-structural terminal = terminal
  optimize-once-structural initial = initial
  optimize-once-structural (curry f m) = curry (optimize-once f) m
  optimize-once-structural apply = apply
  -- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
  -- | SigOp with Void source is equivalent to initial (no inhabitants)
  optimize-once-structural (SigOp {A} n) with A ≟Type Void
  ... | yes refl = initial
  ... | no _     = SigOp n
  -- | const is opaque (constant value of a primitive type, not optimized)
  optimize-once-structural (const p v) = const p v
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
  optimize-once-structural (Hylo {F} {G} wfF wfG alg t) = Hylo {F} {G} wfF wfG (optimize-once alg) (optimize-nt t)
  -- Fuse: μ-anchored fusion (correct by construction)
  optimize-once-structural (Fuse {F} {G} wfF wfG alg t) = Fuse {F} {G} wfF wfG (optimize-once alg) (optimize-nt t)
  -- Guard/Unguard removed: productivity follows from IR totality
  -- out-μ/in-ν: Lambek isomorphisms (potential fusion: out-μ ∘ In = id, In ∘ out-μ = id)

  -- | Type-directed optimization
  optimize-once : ∀ {A B} → IR A B → IR A B
  optimize-once {A} {B} ir with B ≟IRTy II.Unit
  ... | yes refl with has-effect? ir
  ...   | false = terminal                     -- pure morphism to Unit → terminal
  ...   | true  = optimize-once-structural ir  -- EFFECTFUL (SigOp/free-heap) → keep; collapsing would drop the observable effect
  optimize-once {A} {B} ir | no _ with A ≟IRTy II.Void
  ...   | yes refl = initial                   -- Source is Void → initial (vacuous: never invoked)
  ...   | no _ = optimize-once-structural ir   -- Otherwise → structural rules

  -- D062: optimization descends into a natural transform's constant-leaf IRs.
  optimize-nt : ∀ {G F} → NatTr G F → NatTr G F
  optimize-nt ntId         = ntId
  optimize-nt (ntK ir)     = ntK (optimize-once ir)
  optimize-nt (ntFst t)    = ntFst (optimize-nt t)
  optimize-nt (ntSnd t)    = ntSnd (optimize-nt t)
  optimize-nt (ntCase t u) = ntCase (optimize-nt t) (optimize-nt u)
  optimize-nt (ntInl t)    = ntInl (optimize-nt t)
  optimize-nt (ntInr t)    = ntInr (optimize-nt t)
  optimize-nt (ntPair t u) = ntPair (optimize-nt t) (optimize-nt u)

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