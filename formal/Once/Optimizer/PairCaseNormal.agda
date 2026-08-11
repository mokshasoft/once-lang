-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Optimizer.PairCaseNormal
--
-- Proofs that optimize-pair and optimize-case produce normal forms.
-- Mechanical enumeration matching the with-abstraction structure
-- of optimize-pair and optimize-case in Once.Optimize.
------------------------------------------------------------------------

module Once.Optimizer.PairCaseNormal where

open import Once.Type
open import Once.IR
open import Once.Optimize using (_≟Type_; _≟IR_; optimize-pair; optimize-case)
open import Once.Optimizer.IRReducible

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Helper: Extract normal subterms from normal compositions
------------------------------------------------------------------------

-- | A BCC term is in normal form if no reduction applies
data IsNormal : ∀ {A B} → IR A B → Set where
  -- Generators are normal
  normal-id       : ∀ {A} → IsNormal (id {A})
  normal-fst      : ∀ {A B} → IsNormal (fst {A} {B})
  normal-snd      : ∀ {A B} → IsNormal (snd {A} {B})
  normal-inl      : ∀ {A B m} → ¬ (A ≡ Void) → IsNormal (inl {A} {B} m)
  normal-inr      : ∀ {A B m} → ¬ (B ≡ Void) → IsNormal (inr {A} {B} m)
  normal-terminal : ∀ {A} → IsNormal (terminal {A})
  normal-initial  : ∀ {A} → IsNormal (initial {A})
  normal-apply    : ∀ {A B q} → IsNormal (apply {A} {B} {q})
  normal-arr      : ∀ {A B} → IsNormal (arr {A} {B})
  normal-fold     : ∀ {F} → ¬ (F ≡ Void) → IsNormal ((fold _) {F})
  normal-unfold   : ∀ {F} → IsNormal (unfold {F})
  normal-sigOp     : ∀ {A B} {n} → ¬ (A ≡ Void) → IsNormal (SigOp {A} {B} n)

  -- Composition is normal if not reducible and subterms are normal
  normal-compose : ∀ {A B C} {g : IR B C} {f : IR A B} →
                   IsNormal g → IsNormal f →
                   ¬ CompReducible g f →
                   IsNormal (g ∘ f)

  -- Pair is normal if not reducible and subterms are normal
  normal-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                IsNormal f → IsNormal g →
                ¬ PairReducible f g →
                IsNormal (⟨ f , g ⟩ m)

  -- Case is normal if not reducible and subterms are normal
  normal-case : ∀ {A B C} {f : IR A C} {g : IR B C} →
                IsNormal f → IsNormal g →
                ¬ CaseReducible f g →
                IsNormal (case f g)

  -- Curry is normal if body is normal
  normal-curry : ∀ {A B C k} {f : IR (A * B) C} {m} →
                 IsNormal f →
                 IsNormal (curry {k = k} f m)

------------------------------------------------------------------------
-- Helper: Extract normal subterms from normal compound terms
------------------------------------------------------------------------

-- | Extract the left subterm's normality from a normal composition
normal-compose-left : ∀ {A B C} {g : IR B C} {f : IR A B} →
  IsNormal (g ∘ f) → IsNormal g
normal-compose-left (normal-compose ng _ _) = ng

-- | Extract the right subterm's normality from a normal composition
normal-compose-right : ∀ {A B C} {g : IR B C} {f : IR A B} →
  IsNormal (g ∘ f) → IsNormal f
normal-compose-right (normal-compose _ nf _) = nf

------------------------------------------------------------------------
-- Proof: optimize-pair produces normal forms
------------------------------------------------------------------------

-- | optimize-pair produces normal forms when given normal inputs
--
-- The proof follows the exact structure of optimize-pair:
--   1. fst paired with snd (type check)
--   2. (fst ∘ h) paired with (snd ∘ h') (type check, then IR equality check)
--   3. Default case: just wrap in pair
optimize-pair-normal : ∀ {A B C} (f : IR C A) (g : IR C B) →
  IsNormal f → IsNormal g → IsNormal (optimize-pair f g)

-- Case 1: f = fst, g = snd
-- optimize-pair checks A ≟Type A' | B ≟Type B'
optimize-pair-normal (fst {A} {B}) (snd {A'} {B'}) nf ng with A ≟Type A' | B ≟Type B'
-- Types match: returns id
... | yes refl | yes refl = normal-id
-- Types don't match: returns ⟨ fst , snd ⟩ Heap
... | no A≢A'  | _        = normal-pair nf ng λ { red-pair-eta → A≢A' refl }
... | yes refl | no B≢B'  = normal-pair nf ng λ { red-pair-eta → B≢B' refl }

-- Case 2: f = fst ∘ h, g = snd ∘ h'
-- optimize-pair checks A ≟Type A' | B ≟Type B' | D ≟Type D', then h ≟IR h'
optimize-pair-normal (_∘_ {_} {D} (fst {A} {B}) h) (_∘_ {_} {D'} (snd {A'} {B'}) h') nf ng
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
-- All types match: check if h ≡ h'
... | yes refl | yes refl | yes refl with h ≟IR h'
-- h ≡ h': returns h (extract normality from f = fst ∘ h)
...   | yes refl = normal-compose-right nf
-- h ≢ h': returns ⟨ fst ∘ h , snd ∘ h' ⟩ Heap
...   | no h≢h' = normal-pair nf ng (fst-h-snd-h'-diff-not-reducible h≢h')
-- Types don't match: returns ⟨ fst ∘ h , snd ∘ h' ⟩ Heap
optimize-pair-normal (_∘_ (fst {A} {B}) h) (_∘_ (snd {A'} {B'}) h') nf ng
  | no A≢A' | _ | _ = normal-pair nf ng λ { red-pair-uniq → A≢A' refl }
optimize-pair-normal (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {B'}) h') nf ng
  | yes refl | no B≢B' | _ = normal-pair nf ng λ { red-pair-uniq → B≢B' refl }
optimize-pair-normal (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {.B}) h') nf ng
  | yes refl | yes refl | no D≢D' = normal-pair nf ng λ { red-pair-uniq → D≢D' refl }

-- Default case: f and g don't match the special patterns
-- Returns ⟨ f , g ⟩ Heap
-- We need to show this is not pair-reducible.
-- Since f is not fst and not (fst ∘ _), it can't be red-pair-eta or red-pair-uniq.

-- f = fst, g ≠ snd (all type-valid g patterns)
optimize-pair-normal fst fst nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst id nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (⟨ _ , _ ⟩ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (inl _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (inr _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst terminal nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (curry _ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst apply nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (fold _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal fst (SigOp _) nf ng = normal-pair nf ng λ ()
-- f = fst, g = _ ∘ _ (all composition cases)
optimize-pair-normal fst (_ ∘ _) nf ng = normal-pair nf ng λ ()

-- f = snd (never matches eta or uniq)
optimize-pair-normal snd _ nf ng = normal-pair nf ng λ ()

-- f = id
optimize-pair-normal id _ nf ng = normal-pair nf ng λ ()

-- f = ⟨ _ , _ ⟩ _
optimize-pair-normal (⟨ _ , _ ⟩ _) _ nf ng = normal-pair nf ng λ ()

-- f = inl _
optimize-pair-normal (inl _) _ nf ng = normal-pair nf ng λ ()

-- f = inr _
optimize-pair-normal (inr _) _ nf ng = normal-pair nf ng λ ()

-- f = (case _ _)
optimize-pair-normal (case _ _) _ nf ng = normal-pair nf ng λ ()

-- f = terminal
optimize-pair-normal terminal _ nf ng = normal-pair nf ng λ ()

-- f = initial
optimize-pair-normal initial _ nf ng = normal-pair nf ng λ ()

-- f = curry _ _
optimize-pair-normal (curry _ _) _ nf ng = normal-pair nf ng λ ()

-- f = apply
optimize-pair-normal apply _ nf ng = normal-pair nf ng λ ()

-- f = fold Heap
optimize-pair-normal fold _ nf ng = normal-pair nf ng λ ()

-- f = unfold
optimize-pair-normal unfold _ nf ng = normal-pair nf ng λ ()

-- f = arr
optimize-pair-normal arr _ nf ng = normal-pair nf ng λ ()

-- f = SigOp _
optimize-pair-normal (SigOp _) _ nf ng = normal-pair nf ng λ ()

-- f = non-fst ∘ _ (never matches eta or uniq because left of comp isn't fst)
optimize-pair-normal (snd ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal (id ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((⟨ _ , _ ⟩ _) ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((inl _) ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((inr _) ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((case _ _) ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal (terminal ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal (initial ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((curry _ _) ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal (apply ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((fold Heap) ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal (unfold ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal (arr ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((SigOp _) ∘ _) _ nf ng = normal-pair nf ng λ ()
optimize-pair-normal ((_ ∘ _) ∘ _) _ nf ng = normal-pair nf ng λ ()

-- f = fst ∘ h, g ≠ snd ∘ _ (all remaining g patterns)
-- fst ∘ h has domain D (where h : IR D (A * B)), so g must have domain D
-- Any g can potentially have domain D, so we need to enumerate
optimize-pair-normal (fst ∘ _) id nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) fst nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) snd nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (⟨ _ , _ ⟩ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (inl _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (inr _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (case _ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) terminal nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) initial nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (curry _ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) apply nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (fold _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) unfold nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) arr nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (SigOp _) nf ng = normal-pair nf ng λ ()

-- f = fst ∘ _, g = non-snd ∘ _
optimize-pair-normal (fst ∘ _) (id ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (fst ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((⟨ _ , _ ⟩ _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((inl _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((inr _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((case _ _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (terminal ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (initial ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((curry _ _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (apply ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((fold Heap) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (unfold ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) (arr ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((SigOp _) ∘ _) nf ng = normal-pair nf ng λ ()
optimize-pair-normal (fst ∘ _) ((_ ∘ _) ∘ _) nf ng = normal-pair nf ng λ ()

------------------------------------------------------------------------
-- Proof: optimize-case produces normal forms
------------------------------------------------------------------------

-- | optimize-case produces normal forms when given normal inputs
--
-- The proof follows the exact structure of optimize-case:
--   1. inl paired with inr (type check)
--   2. (h ∘ inl) paired with (h' ∘ inr) (type check, then IR equality check)
--   3. Default case: just wrap in case
optimize-case-normal : ∀ {A B C} (f : IR A C) (g : IR B C) →
  IsNormal f → IsNormal g → IsNormal (optimize-case f g)

-- Case 1: f = inl, g = inr
-- optimize-case checks A ≟Type A' | B ≟Type B'
optimize-case-normal (inl {A} {B} m₁) (inr {A'} {B'} m₂) nf ng with A ≟Type A' | B ≟Type B'
-- Types match: returns id
... | yes refl | yes refl = normal-id
-- Types don't match: returns [ inl m₁ , inr m₂ ]
... | no A≢A'  | _        = normal-case nf ng λ { red-case-eta → A≢A' refl }
... | yes refl | no B≢B'  = normal-case nf ng λ { red-case-eta → B≢B' refl }

-- Case 2: f = h ∘ inl, g = h' ∘ inr
-- optimize-case checks A ≟Type A' | B ≟Type B' | D ≟Type D', then h ≟IR h'
optimize-case-normal (_∘_ {_} {D} {C} h (inl {A} {B} m₁)) (_∘_ {_} {D'} {C'} h' (inr {A'} {B'} m₂)) nf ng
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
-- All types match: check if h ≡ h'
... | yes refl | yes refl | yes refl with h ≟IR h'
-- h ≡ h': returns h (extract normality from f = h ∘ inl)
...   | yes refl = normal-compose-left nf
-- h ≢ h': returns [ h ∘ inl m₁ , h' ∘ inr m₂ ]
...   | no h≢h' = normal-case nf ng λ { red-case-uniq → h≢h' refl }
-- Types don't match: returns [ h ∘ inl m₁ , h' ∘ inr m₂ ]
optimize-case-normal (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) nf ng
  | no A≢A' | _ | _ = normal-case nf ng λ { red-case-uniq → A≢A' refl }
optimize-case-normal (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) nf ng
  | yes refl | no B≢B' | _ = normal-case nf ng λ { red-case-uniq → B≢B' refl }
optimize-case-normal (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) nf ng
  | yes refl | yes refl | no D≢D' = normal-case nf ng λ { red-case-uniq → D≢D' refl }

-- Default case: f and g don't match the special patterns
-- Returns (case f g)
-- We need to show this is not case-reducible.
-- Since f is not inl and not (_ ∘ inl _), it can't be red-case-eta or red-case-uniq.

-- f = inl _, g ≠ inr _ (all type-valid g patterns)
optimize-case-normal (inl _) (inl _) nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) id nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) fst nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) snd nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) (case _ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) initial nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) apply nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) unfold nf ng = normal-case nf ng λ ()
optimize-case-normal (inl _) (SigOp _) nf ng = normal-case nf ng λ ()
-- f = inl _, g = _ ∘ _ (all composition cases)
optimize-case-normal (inl _) (_ ∘ _) nf ng = normal-case nf ng λ ()

-- f = inr _ (never matches eta or uniq)
optimize-case-normal (inr _) _ nf ng = normal-case nf ng λ ()

-- f = id
optimize-case-normal id _ nf ng = normal-case nf ng λ ()

-- f = fst
optimize-case-normal fst _ nf ng = normal-case nf ng λ ()

-- f = snd
optimize-case-normal snd _ nf ng = normal-case nf ng λ ()

-- f = ⟨ _ , _ ⟩ _
optimize-case-normal (⟨ _ , _ ⟩ _) _ nf ng = normal-case nf ng λ ()

-- f = (case _ _)
optimize-case-normal (case _ _) _ nf ng = normal-case nf ng λ ()

-- f = terminal
optimize-case-normal terminal _ nf ng = normal-case nf ng λ ()

-- f = initial
optimize-case-normal initial _ nf ng = normal-case nf ng λ ()

-- f = curry _ _
optimize-case-normal (curry _ _) _ nf ng = normal-case nf ng λ ()

-- f = apply
optimize-case-normal apply _ nf ng = normal-case nf ng λ ()

-- f = fold Heap
optimize-case-normal fold _ nf ng = normal-case nf ng λ ()

-- f = unfold
optimize-case-normal unfold _ nf ng = normal-case nf ng λ ()

-- f = arr
optimize-case-normal arr _ nf ng = normal-case nf ng λ ()

-- f = SigOp _
optimize-case-normal (SigOp _) _ nf ng = normal-case nf ng λ ()

-- f = _ ∘ non-inl (never matches eta or uniq because right of comp isn't inl)
optimize-case-normal (_ ∘ id) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ fst) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ snd) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (⟨ _ , _ ⟩ _)) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inr _)) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (case _ _)) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ terminal) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ initial) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (curry _ _)) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ apply) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ fold Heap) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ unfold) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ arr) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (SigOp _)) _ nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (_ ∘ _)) _ nf ng = normal-case nf ng λ ()

-- f = _ ∘ inl _, g ≠ _ ∘ inr _ (all remaining g patterns)
optimize-case-normal (_ ∘ (inl _)) id nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) fst nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) snd nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (⟨ _ , _ ⟩ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (inl _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (inr _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (case _ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) terminal nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) initial nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (curry _ _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) apply nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (fold _) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) unfold nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) arr nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (SigOp _) nf ng = normal-case nf ng λ ()

-- f = _ ∘ inl _, g = _ ∘ non-inr _
optimize-case-normal (_ ∘ (inl _)) (_ ∘ id) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ fst) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ snd) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (⟨ _ , _ ⟩ _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (inl _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (case _ _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ terminal) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ initial) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (curry _ _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ apply) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ fold Heap) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ unfold) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ arr) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (SigOp _)) nf ng = normal-case nf ng λ ()
optimize-case-normal (_ ∘ (inl _)) (_ ∘ (_ ∘ _)) nf ng = normal-case nf ng λ ()