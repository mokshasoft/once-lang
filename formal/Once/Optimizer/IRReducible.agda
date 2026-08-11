-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Optimizer.IRReducible
--
-- Reducibility predicates for IR terms and their decidability proofs.
-- A term is reducible if an optimization rule applies at the top level.
--
-- This module contains the mechanical case enumeration for decidability.
------------------------------------------------------------------------

module Once.Optimizer.IRReducible where

open import Once.Type
open import Once.IR
open import Once.Optimize using (_≟Type_; _≟IR_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Reducible Patterns
------------------------------------------------------------------------

-- | Composition is reducible if it matches a beta/identity/dead-code pattern
data CompReducible : ∀ {A B C} → IR B C → IR A B → Set where
  -- Identity laws
  red-id-left  : ∀ {A B} {f : IR A B} → CompReducible id f
  red-id-right : ∀ {A B} {f : IR A B} → CompReducible f id

  -- Product beta
  red-fst-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                 CompReducible fst (⟨ f , g ⟩ m)
  red-snd-pair : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
                 CompReducible snd (⟨ f , g ⟩ m)

  -- Coproduct beta
  red-case-inl : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                 CompReducible (case f g) (inl m)
  red-case-inr : ∀ {A B C} {f : IR A C} {g : IR B C} {m} →
                 CompReducible (case f g) (inr m)

  -- Exponential beta
  red-apply-curry : ∀ {A B C k} {f : IR (A * B) C} {g : IR A B} {m₁ m₂} →
                    CompReducible apply (⟨ curry {k = k} f m₁ , g ⟩ m₂)

  -- Dead code elimination
  red-terminal : ∀ {A B} {f : IR A B} → CompReducible terminal f

  -- Initial absorption
  red-initial : ∀ {A B} {f : IR A B} → CompReducible f initial

  -- Associativity (enables further reductions)
  red-assoc : ∀ {A B C D} {h : IR C D} {g : IR B C} {f : IR A B} →
              CompReducible (h ∘ g) f

-- | Pair is reducible if it matches an eta pattern
data PairReducible : ∀ {A B C} → IR C A → IR C B → Set where
  -- Eta: ⟨ fst , snd ⟩ = id
  red-pair-eta : ∀ {A B} → PairReducible (fst {A} {B}) snd

  -- Uniqueness: ⟨ fst ∘ h , snd ∘ h ⟩ = h
  red-pair-uniq : ∀ {A B C} {h : IR C (A * B)} →
                  PairReducible (fst ∘ h) (snd ∘ h)

-- | Case is reducible if it matches an eta pattern
data CaseReducible : ∀ {A B C} → IR A C → IR B C → Set where
  -- Eta: (case inl inr) = id
  red-case-eta : ∀ {A B} {m₁ m₂} → CaseReducible (inl {A} {B} m₁) (inr m₂)

  -- Uniqueness: [ h ∘ inl , h ∘ inr ] = h
  red-case-uniq : ∀ {A B C} {h : IR (A + B) C} {m₁ m₂} →
                  CaseReducible (h ∘ inl m₁) (h ∘ inr m₂)

------------------------------------------------------------------------
-- Helper lemmas for non-reducibility
------------------------------------------------------------------------

-- | ⟨ fst ∘ h , snd ∘ h' ⟩ with h ≢ h' is not pair-reducible
fst-h-snd-h'-diff-not-reducible : ∀ {A B C} {h h' : IR C (A * B)} →
  h ≢ h' → ¬ PairReducible (fst ∘ h) (snd ∘ h')
fst-h-snd-h'-diff-not-reducible h≢h' red-pair-uniq = h≢h' refl

------------------------------------------------------------------------
-- Decidability of composition reducibility
------------------------------------------------------------------------

-- | Decidability of composition reducibility
--
-- CompReducible has 10 constructors. We handle each reducible pattern
-- explicitly and show all other combinations are not reducible.
comp-reducible? : ∀ {A B C} (g : IR B C) (f : IR A B) → Dec (CompReducible g f)
-- g = id: always reducible (red-id-left)
comp-reducible? id f = yes red-id-left
-- g = terminal: always reducible (red-terminal)
comp-reducible? terminal f = yes red-terminal
-- g = h ∘ k: always reducible (red-assoc)
comp-reducible? (h ∘ k) f = yes red-assoc
-- f = id: reducible (red-id-right)
comp-reducible? fst id = yes red-id-right
comp-reducible? snd id = yes red-id-right
comp-reducible? (⟨ _ , _ ⟩ _) id = yes red-id-right
comp-reducible? (inl _) id = yes red-id-right
comp-reducible? (inr _) id = yes red-id-right
comp-reducible? (case _ _) id = yes red-id-right
comp-reducible? initial id = yes red-id-right
comp-reducible? (curry _ _) id = yes red-id-right
comp-reducible? apply id = yes red-id-right
comp-reducible? (fold _) id = yes red-id-right
comp-reducible? unfold id = yes red-id-right
comp-reducible? arr id = yes red-id-right
comp-reducible? (SigOp _) id = yes red-id-right
comp-reducible? (free-heap _) id = yes red-id-right
-- f = initial: reducible (red-initial)
comp-reducible? fst initial = yes red-initial
comp-reducible? snd initial = yes red-initial
comp-reducible? (⟨ _ , _ ⟩ _) initial = yes red-initial
comp-reducible? (inl _) initial = yes red-initial
comp-reducible? (inr _) initial = yes red-initial
comp-reducible? (case _ _) initial = yes red-initial
comp-reducible? initial initial = yes red-initial
comp-reducible? (curry _ _) initial = yes red-initial
comp-reducible? apply initial = yes red-initial
comp-reducible? (fold _) initial = yes red-initial
comp-reducible? unfold initial = yes red-initial
comp-reducible? arr initial = yes red-initial
comp-reducible? (SigOp _) initial = yes red-initial
comp-reducible? (free-heap _) initial = yes red-initial
-- g = fst, f = ⟨ _ , _ ⟩ _: reducible (red-fst-pair)
comp-reducible? fst (⟨ _ , _ ⟩ _) = yes red-fst-pair
-- g = snd, f = ⟨ _ , _ ⟩ _: reducible (red-snd-pair)
comp-reducible? snd (⟨ _ , _ ⟩ _) = yes red-snd-pair
-- g = (case _ _), f = inl _: reducible (red-case-inl)
comp-reducible? (case _ _) (inl _) = yes red-case-inl
-- g = (case _ _), f = inr _: reducible (red-case-inr)
comp-reducible? (case _ _) (inr _) = yes red-case-inr
-- g = apply, f = ⟨ curry _ _ , _ ⟩ _: reducible (red-apply-curry)
comp-reducible? apply (⟨ curry _ _ , _ ⟩ _) = yes red-apply-curry
-- All remaining cases: not reducible
-- g = fst (non-pair, non-id, non-initial f)
-- fst : IR (A * B) A, so f must have codomain A * B
comp-reducible? fst (_ ∘ _) = no λ ()
comp-reducible? fst fst = no λ ()
comp-reducible? fst snd = no λ ()
-- inl, inr have codomain A + B (not product) - type-impossible
-- terminal has codomain Unit - type-impossible
-- curry has codomain B ⇒ C - type-impossible
-- fold has codomain Fix F - type-impossible
-- arr has codomain Eff A B - type-impossible
comp-reducible? fst (case _ _) = no λ ()
comp-reducible? fst apply = no λ ()
comp-reducible? fst unfold = no λ ()
comp-reducible? fst (SigOp _) = no λ ()
-- g = snd (non-pair, non-id, non-initial f)
-- snd : IR (A * B) B, so f must have codomain A * B
comp-reducible? snd (_ ∘ _) = no λ ()
comp-reducible? snd fst = no λ ()
comp-reducible? snd snd = no λ ()
-- inl, inr, terminal, curry, fold, arr have wrong codomain - type-impossible
comp-reducible? snd (case _ _) = no λ ()
comp-reducible? snd apply = no λ ()
comp-reducible? snd unfold = no λ ()
comp-reducible? snd (SigOp _) = no λ ()
-- g = ⟨ _ , _ ⟩ _ (non-id, non-initial f)
comp-reducible? (⟨ _ , _ ⟩ _) (_ ∘ _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) fst = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) snd = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (⟨ _ , _ ⟩ _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (inl _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (inr _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (case _ _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) terminal = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (curry _ _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) apply = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (fold _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) unfold = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) arr = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (SigOp _) = no λ ()
-- g = inl _ (non-id, non-initial f)
comp-reducible? (inl _) (_ ∘ _) = no λ ()
comp-reducible? (inl _) fst = no λ ()
comp-reducible? (inl _) snd = no λ ()
comp-reducible? (inl _) (⟨ _ , _ ⟩ _) = no λ ()
comp-reducible? (inl _) (inl _) = no λ ()
comp-reducible? (inl _) (inr _) = no λ ()
comp-reducible? (inl _) (case _ _) = no λ ()
comp-reducible? (inl _) terminal = no λ ()
comp-reducible? (inl _) (curry _ _) = no λ ()
comp-reducible? (inl _) apply = no λ ()
comp-reducible? (inl _) (fold _) = no λ ()
comp-reducible? (inl _) unfold = no λ ()
comp-reducible? (inl _) arr = no λ ()
comp-reducible? (inl _) (SigOp _) = no λ ()
-- g = inr _ (non-id, non-initial f)
comp-reducible? (inr _) (_ ∘ _) = no λ ()
comp-reducible? (inr _) fst = no λ ()
comp-reducible? (inr _) snd = no λ ()
comp-reducible? (inr _) (⟨ _ , _ ⟩ _) = no λ ()
comp-reducible? (inr _) (inl _) = no λ ()
comp-reducible? (inr _) (inr _) = no λ ()
comp-reducible? (inr _) (case _ _) = no λ ()
comp-reducible? (inr _) terminal = no λ ()
comp-reducible? (inr _) (curry _ _) = no λ ()
comp-reducible? (inr _) apply = no λ ()
comp-reducible? (inr _) (fold _) = no λ ()
comp-reducible? (inr _) unfold = no λ ()
comp-reducible? (inr _) arr = no λ ()
comp-reducible? (inr _) (SigOp _) = no λ ()
-- g = (case _ _) (non-inl, non-inr, non-id, non-initial f)
-- (case _ _) : IR (A + B) C, so f must have codomain A + B
comp-reducible? (case _ _) (_ ∘ _) = no λ ()
comp-reducible? (case _ _) fst = no λ ()
comp-reducible? (case _ _) snd = no λ ()
-- ⟨_,_⟩ has codomain A * B - type-impossible
-- terminal, curry, fold, arr have wrong codomain - type-impossible
comp-reducible? (case _ _) (case _ _) = no λ ()
comp-reducible? (case _ _) apply = no λ ()
comp-reducible? (case _ _) unfold = no λ ()
comp-reducible? (case _ _) (SigOp _) = no λ ()
-- g = initial (non-id, non-initial f)
-- initial : IR Void A, so f must have codomain Void
comp-reducible? initial (_ ∘ _) = no λ ()
comp-reducible? initial fst = no λ ()
comp-reducible? initial snd = no λ ()
-- ⟨_,_⟩, inl, inr, terminal, curry, fold, arr have wrong codomain - type-impossible
comp-reducible? initial (case _ _) = no λ ()
comp-reducible? initial apply = no λ ()
comp-reducible? initial unfold = no λ ()
comp-reducible? initial (SigOp _) = no λ ()
-- g = curry _ _ (non-id, non-initial f)
comp-reducible? (curry _ _) (_ ∘ _) = no λ ()
comp-reducible? (curry _ _) fst = no λ ()
comp-reducible? (curry _ _) snd = no λ ()
comp-reducible? (curry _ _) (⟨ _ , _ ⟩ _) = no λ ()
comp-reducible? (curry _ _) (inl _) = no λ ()
comp-reducible? (curry _ _) (inr _) = no λ ()
comp-reducible? (curry _ _) (case _ _) = no λ ()
comp-reducible? (curry _ _) terminal = no λ ()
comp-reducible? (curry _ _) (curry _ _) = no λ ()
comp-reducible? (curry _ _) apply = no λ ()
comp-reducible? (curry _ _) (fold _) = no λ ()
comp-reducible? (curry _ _) unfold = no λ ()
comp-reducible? (curry _ _) arr = no λ ()
comp-reducible? (curry _ _) (SigOp _) = no λ ()
-- g = apply (non-curry-pair, non-id, non-initial f)
comp-reducible? apply (_ ∘ _) = no λ ()
comp-reducible? apply fst = no λ ()
comp-reducible? apply snd = no λ ()
-- apply ⟨ non-curry , _ ⟩ cases
-- apply : IR ((A ⇒ B) * A) B, so f must have codomain (A ⇒ B) * A
-- First component of pair must have codomain A ⇒ B (function type)
-- ⟨_,_⟩, inl, inr, terminal, fold, arr have wrong codomain - type-impossible
comp-reducible? apply (⟨ id , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ (_ ∘ _) , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ fst , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ snd , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ (case _ _) , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ initial , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ apply , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ unfold , _ ⟩ _) = no λ ()
comp-reducible? apply (⟨ (SigOp _) , _ ⟩ _) = no λ ()
-- inl, inr have codomain A + B - type-impossible
-- terminal has codomain Unit - type-impossible
-- curry has codomain B ⇒ C - handled by red-apply-curry
-- fold has codomain Fix F - type-impossible
-- arr has codomain Eff A B - type-impossible
comp-reducible? apply (case _ _) = no λ ()
comp-reducible? apply apply = no λ ()
comp-reducible? apply unfold = no λ ()
comp-reducible? apply (SigOp _) = no λ ()
-- g = (fold _) (non-id, non-initial f)
comp-reducible? (fold _) (_ ∘ _) = no λ ()
comp-reducible? (fold _) fst = no λ ()
comp-reducible? (fold _) snd = no λ ()
comp-reducible? (fold _) (⟨ _ , _ ⟩ _) = no λ ()
comp-reducible? (fold _) (inl _) = no λ ()
comp-reducible? (fold _) (inr _) = no λ ()
comp-reducible? (fold _) (case _ _) = no λ ()
comp-reducible? (fold _) terminal = no λ ()
comp-reducible? (fold _) (curry _ _) = no λ ()
comp-reducible? (fold _) apply = no λ ()
comp-reducible? (fold _) (fold _) = no λ ()
comp-reducible? (fold _) unfold = no λ ()
comp-reducible? (fold _) arr = no λ ()
comp-reducible? (fold _) (SigOp _) = no λ ()
-- g = unfold (non-id, non-initial f)
-- unfold : IR (Fix F) F, so f must have codomain Fix F
-- ⟨_,_⟩, inl, inr, terminal, curry, arr have wrong codomain - type-impossible
comp-reducible? unfold (_ ∘ _) = no λ ()
comp-reducible? unfold fst = no λ ()
comp-reducible? unfold snd = no λ ()
comp-reducible? unfold (case _ _) = no λ ()
comp-reducible? unfold apply = no λ ()
comp-reducible? unfold (fold _) = no λ ()
comp-reducible? unfold unfold = no λ ()
comp-reducible? unfold (SigOp _) = no λ ()
-- g = arr (non-id, non-initial f)
-- arr : IR (A ⇒ B) (A ⇒[ mk-kind Many eff ] B), so f must have codomain A ⇒ B
-- ⟨_,_⟩, inl, inr, terminal, fold, arr have wrong codomain - type-impossible
comp-reducible? arr (_ ∘ _) = no λ ()
comp-reducible? arr fst = no λ ()
comp-reducible? arr snd = no λ ()
comp-reducible? arr (case _ _) = no λ ()
comp-reducible? arr (curry _ _) = no λ ()
comp-reducible? arr apply = no λ ()
comp-reducible? arr unfold = no λ ()
comp-reducible? arr (SigOp _) = no λ ()
-- g = SigOp _ (non-id, non-initial f)
comp-reducible? (SigOp _) (_ ∘ _) = no λ ()
comp-reducible? (SigOp _) fst = no λ ()
comp-reducible? (SigOp _) snd = no λ ()
comp-reducible? (SigOp _) (⟨ _ , _ ⟩ _) = no λ ()
comp-reducible? (SigOp _) (inl _) = no λ ()
comp-reducible? (SigOp _) (inr _) = no λ ()
comp-reducible? (SigOp _) (case _ _) = no λ ()
comp-reducible? (SigOp _) terminal = no λ ()
comp-reducible? (SigOp _) (curry _ _) = no λ ()
comp-reducible? (SigOp _) apply = no λ ()
comp-reducible? (SigOp _) (fold _) = no λ ()
comp-reducible? (SigOp _) unfold = no λ ()
comp-reducible? (SigOp _) arr = no λ ()
comp-reducible? (SigOp _) (SigOp _) = no λ ()
comp-reducible? (SigOp _) (free-heap _) = no λ ()
comp-reducible? (⟨ _ , _ ⟩ _) (free-heap _) = no λ ()
comp-reducible? (inl _) (free-heap _) = no λ ()
comp-reducible? (inr _) (free-heap _) = no λ ()
comp-reducible? (curry _ _) (free-heap _) = no λ ()
comp-reducible? (fold _) (free-heap _) = no λ ()
-- g = free-heap: IR Unit Unit, so f : IR A Unit
comp-reducible? (free-heap _) (_ ∘ _) = no λ ()
comp-reducible? (free-heap _) fst = no λ ()
comp-reducible? (free-heap _) snd = no λ ()
comp-reducible? (free-heap _) (case _ _) = no λ ()
comp-reducible? (free-heap _) terminal = no λ ()
comp-reducible? (free-heap _) apply = no λ ()
comp-reducible? (free-heap _) unfold = no λ ()
comp-reducible? (free-heap _) (SigOp _) = no λ ()
comp-reducible? (free-heap _) (free-heap _) = no λ ()

------------------------------------------------------------------------
-- Decidability of pair reducibility
------------------------------------------------------------------------

-- | Decidability of pair reducibility
--
-- PairReducible has only 2 constructors:
--   red-pair-eta : PairReducible fst snd
--   red-pair-uniq : PairReducible (fst ∘ h) (snd ∘ h)
--
-- We check if f and g match these patterns.
pair-reducible? : ∀ {A B C} (f : IR C A) (g : IR C B) → Dec (PairReducible f g)
-- Case 1: f = fst, g = snd (eta)
pair-reducible? (fst {A} {B}) (snd {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = yes red-pair-eta
... | no A≢A'  | _        = no λ { red-pair-eta → A≢A' refl }
... | _        | no B≢B'  = no λ { red-pair-eta → B≢B' refl }
-- Case 2: f = fst ∘ h, g = snd ∘ h' (uniqueness if h ≡ h')
pair-reducible? (_∘_ {_} {D} (fst {A} {B}) h) (_∘_ {_} {D'} (snd {A'} {B'}) h')
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = yes red-pair-uniq
...   | no h≢h'  = no (fst-h-snd-h'-diff-not-reducible h≢h')
pair-reducible? (_∘_ (fst {A} {B}) h) (_∘_ (snd {A'} {B'}) h') | no A≢A' | _ | _ =
  no λ { red-pair-uniq → A≢A' refl }
pair-reducible? (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {B'}) h') | yes refl | no B≢B' | _ =
  no λ { red-pair-uniq → B≢B' refl }
pair-reducible? (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {.B}) h') | yes refl | yes refl | no D≢D' =
  no λ { red-pair-uniq → D≢D' refl }
-- All other cases: not reducible
-- f = fst, g ≠ snd
pair-reducible? fst fst = no λ ()
pair-reducible? fst (fst ∘ _) = no λ ()
pair-reducible? fst (snd ∘ _) = no λ ()
-- Remaining composition cases for f = fst
pair-reducible? fst (id ∘ _) = no λ ()
pair-reducible? fst ((⟨ _ , _ ⟩ _) ∘ _) = no λ ()
pair-reducible? fst ((inl _) ∘ _) = no λ ()
pair-reducible? fst ((inr _) ∘ _) = no λ ()
pair-reducible? fst ((case _ _) ∘ _) = no λ ()
pair-reducible? fst (terminal ∘ _) = no λ ()
pair-reducible? fst (initial ∘ _) = no λ ()
pair-reducible? fst ((curry _ _) ∘ _) = no λ ()
pair-reducible? fst (apply ∘ _) = no λ ()
pair-reducible? fst ((fold Heap) ∘ _) = no λ ()
pair-reducible? fst (unfold ∘ _) = no λ ()
pair-reducible? fst (arr ∘ _) = no λ ()
pair-reducible? fst ((SigOp _) ∘ _) = no λ ()
pair-reducible? fst ((_ ∘ _) ∘ _) = no λ ()
pair-reducible? fst id = no λ ()
pair-reducible? fst (⟨ _ , _ ⟩ _) = no λ ()
pair-reducible? fst (inl _) = no λ ()
pair-reducible? fst (inr _) = no λ ()
pair-reducible? fst terminal = no λ ()
pair-reducible? fst (curry _ _) = no λ ()
pair-reducible? fst apply = no λ ()
pair-reducible? fst (fold _) = no λ ()
pair-reducible? fst (SigOp _) = no λ ()
-- f = snd (never matches red-pair-eta or red-pair-uniq)
pair-reducible? snd _ = no λ ()
-- f = id
pair-reducible? id _ = no λ ()
-- f = ⟨ _ , _ ⟩ _
pair-reducible? (⟨ _ , _ ⟩ _) _ = no λ ()
-- f = inl _
pair-reducible? (inl _) _ = no λ ()
-- f = inr _
pair-reducible? (inr _) _ = no λ ()
-- f = terminal
pair-reducible? terminal _ = no λ ()
-- f = curry _ _
pair-reducible? (curry _ _) _ = no λ ()
-- f = apply
pair-reducible? apply _ = no λ ()
-- f = fold _
pair-reducible? (fold _) _ = no λ ()
-- f = free-heap _
pair-reducible? (free-heap _) _ = no λ ()
-- f = unfold
pair-reducible? unfold _ = no λ ()
-- f = arr
pair-reducible? arr _ = no λ ()
-- f = SigOp _
pair-reducible? (SigOp _) _ = no λ ()
-- f = snd ∘ _
pair-reducible? (snd ∘ _) _ = no λ ()
-- f = id ∘ _
pair-reducible? (id ∘ _) _ = no λ ()
-- f = (⟨ _ , _ ⟩ _) ∘ _
pair-reducible? ((⟨ _ , _ ⟩ _) ∘ _) _ = no λ ()
-- f = (inl _) ∘ _
pair-reducible? ((inl _) ∘ _) _ = no λ ()
-- f = (inr _) ∘ _
pair-reducible? ((inr _) ∘ _) _ = no λ ()
-- f = terminal ∘ _
pair-reducible? (terminal ∘ _) _ = no λ ()
-- f = initial ∘ _
pair-reducible? (initial ∘ _) _ = no λ ()
-- f = (curry _ _) ∘ _
pair-reducible? ((curry _ _) ∘ _) _ = no λ ()
-- f = (fold _) ∘ _
pair-reducible? ((fold _) ∘ _) _ = no λ ()
-- f = (free-heap _) ∘ _
pair-reducible? ((free-heap _) ∘ _) _ = no λ ()
-- f = apply ∘ _
pair-reducible? (apply ∘ _) _ = no λ ()
-- f = (fold Heap) ∘ _
pair-reducible? ((fold Heap) ∘ _) _ = no λ ()
-- f = unfold ∘ _
pair-reducible? (unfold ∘ _) _ = no λ ()
-- f = arr ∘ _
pair-reducible? (arr ∘ _) _ = no λ ()
-- f = (SigOp _) ∘ _
pair-reducible? ((SigOp _) ∘ _) _ = no λ ()
-- f = (_ ∘ _) ∘ _
pair-reducible? ((_ ∘ _) ∘ _) _ = no λ ()
-- f = (case _ _) ∘ _
pair-reducible? ((case _ _) ∘ _) _ = no λ ()
-- f = (case _ _) (non-composition)
pair-reducible? (case _ _) _ = no λ ()
-- f = initial (non-composition)
pair-reducible? initial _ = no λ ()
-- f = fst ∘ h where g is not snd ∘ _
pair-reducible? (fst ∘ _) id = no λ ()
pair-reducible? (fst ∘ _) fst = no λ ()
pair-reducible? (fst ∘ _) snd = no λ ()
pair-reducible? (fst ∘ _) (⟨ _ , _ ⟩ _) = no λ ()
pair-reducible? (fst ∘ _) (inl _) = no λ ()
pair-reducible? (fst ∘ _) (inr _) = no λ ()
pair-reducible? (fst ∘ _) (case _ _) = no λ ()
pair-reducible? (fst ∘ _) terminal = no λ ()
pair-reducible? (fst ∘ _) initial = no λ ()
pair-reducible? (fst ∘ _) (curry _ _) = no λ ()
pair-reducible? (fst ∘ _) apply = no λ ()
pair-reducible? (fst ∘ _) (fold _) = no λ ()
pair-reducible? (fst ∘ _) unfold = no λ ()
pair-reducible? (fst ∘ _) arr = no λ ()
pair-reducible? (fst ∘ _) (SigOp _) = no λ ()
-- f = fst ∘ h, g = non-snd ∘ _
pair-reducible? (fst ∘ _) (id ∘ _) = no λ ()
pair-reducible? (fst ∘ _) (fst ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((⟨ _ , _ ⟩ _) ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((inl _) ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((inr _) ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((case _ _) ∘ _) = no λ ()
pair-reducible? (fst ∘ _) (terminal ∘ _) = no λ ()
pair-reducible? (fst ∘ _) (initial ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((curry _ _) ∘ _) = no λ ()
pair-reducible? (fst ∘ _) (apply ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((fold Heap) ∘ _) = no λ ()
pair-reducible? (fst ∘ _) (unfold ∘ _) = no λ ()
pair-reducible? (fst ∘ _) (arr ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((SigOp _) ∘ _) = no λ ()
pair-reducible? (fst ∘ _) ((_ ∘ _) ∘ _) = no λ ()

------------------------------------------------------------------------
-- Decidability of case reducibility
------------------------------------------------------------------------

-- | Decidability of case reducibility
--
-- CaseReducible has only 2 constructors:
--   red-case-eta : CaseReducible (inl m₁) (inr m₂)
--   red-case-uniq : CaseReducible (h ∘ inl m₁) (h ∘ inr m₂)
case-reducible? : ∀ {A B C} (f : IR A C) (g : IR B C) → Dec (CaseReducible f g)
-- Case 1: f = inl, g = inr (eta)
case-reducible? (inl {A} {B} m₁) (inr {A'} {B'} m₂) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = yes red-case-eta
... | no A≢A'  | _        = no λ { red-case-eta → A≢A' refl }
... | _        | no B≢B'  = no λ { red-case-eta → B≢B' refl }
-- Case 2: f = h ∘ inl, g = h' ∘ inr (uniqueness if h ≡ h')
case-reducible? (_∘_ {_} {D} {C} h (inl {A} {B} m₁)) (_∘_ {_} {D'} {C'} h' (inr {A'} {B'} m₂))
  with A ≟Type A' | B ≟Type B' | D ≟Type D' | C ≟Type C'
... | yes refl | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = yes red-case-uniq
...   | no h≢h'  = no λ { red-case-uniq → h≢h' refl }
case-reducible? (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) | no A≢A' | _ | _ | _ =
  no λ { red-case-uniq → A≢A' refl }
case-reducible? (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) | yes refl | no B≢B' | _ | _ =
  no λ { red-case-uniq → B≢B' refl }
case-reducible? (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) | yes refl | yes refl | no D≢D' | _ =
  no λ { red-case-uniq → D≢D' refl }
case-reducible? (_∘_ h (inl m₁)) (_∘_ h' (inr m₂)) | yes refl | yes refl | yes refl | no C≢C' =
  no λ { red-case-uniq → C≢C' refl }
-- All other cases: not reducible
-- f = inl _, g ≠ inr _
-- inl has codomain A + B, so g must have codomain A + B too
-- ⟨_,_⟩, terminal, curry, fold, arr have wrong codomain - type-impossible
case-reducible? (inl _) (inl _) = no λ ()
case-reducible? (inl _) id = no λ ()
case-reducible? (inl _) fst = no λ ()
case-reducible? (inl _) snd = no λ ()
case-reducible? (inl _) (case _ _) = no λ ()
case-reducible? (inl _) initial = no λ ()
case-reducible? (inl _) apply = no λ ()
case-reducible? (inl _) unfold = no λ ()
case-reducible? (inl _) (SigOp _) = no λ ()
case-reducible? (inl _) (_ ∘ _) = no λ ()
-- f = inr _ (never matches red-case-eta or red-case-uniq)
case-reducible? (inr _) _ = no λ ()
-- f = id
case-reducible? id _ = no λ ()
-- f = fst
case-reducible? fst _ = no λ ()
-- f = snd
case-reducible? snd _ = no λ ()
-- f = ⟨ _ , _ ⟩ _
case-reducible? (⟨ _ , _ ⟩ _) _ = no λ ()
-- f = (case _ _)
case-reducible? (case _ _) _ = no λ ()
-- f = terminal
case-reducible? terminal _ = no λ ()
-- f = initial
case-reducible? initial _ = no λ ()
-- f = curry _ _
case-reducible? (curry _ _) _ = no λ ()
-- f = apply
case-reducible? apply _ = no λ ()
-- f = fold Heap
case-reducible? fold _ = no λ ()
-- f = unfold
case-reducible? unfold _ = no λ ()
-- f = arr
case-reducible? arr _ = no λ ()
-- f = SigOp _
case-reducible? (SigOp _) _ = no λ ()
-- f = _ ∘ id
case-reducible? (_ ∘ id) _ = no λ ()
-- f = _ ∘ fst
case-reducible? (_ ∘ fst) _ = no λ ()
-- f = _ ∘ snd
case-reducible? (_ ∘ snd) _ = no λ ()
-- f = _ ∘ (⟨ _ , _ ⟩ _)
case-reducible? (_ ∘ (⟨ _ , _ ⟩ _)) _ = no λ ()
-- f = _ ∘ (inr _)
case-reducible? (_ ∘ (inr _)) _ = no λ ()
-- f = _ ∘ (case _ _)
case-reducible? (_ ∘ (case _ _)) _ = no λ ()
-- f = _ ∘ terminal
case-reducible? (_ ∘ terminal) _ = no λ ()
-- f = _ ∘ initial
case-reducible? (_ ∘ initial) _ = no λ ()
-- f = _ ∘ (curry _ _)
case-reducible? (_ ∘ (curry _ _)) _ = no λ ()
-- f = _ ∘ apply
case-reducible? (_ ∘ apply) _ = no λ ()
-- f = _ ∘ (fold Heap)
case-reducible? (_ ∘ fold Heap) _ = no λ ()
-- f = _ ∘ unfold
case-reducible? (_ ∘ unfold) _ = no λ ()
-- f = _ ∘ arr
case-reducible? (_ ∘ arr) _ = no λ ()
-- f = _ ∘ (SigOp _)
case-reducible? (_ ∘ (SigOp _)) _ = no λ ()
-- f = _ ∘ (_ ∘ _)
case-reducible? (_ ∘ (_ ∘ _)) _ = no λ ()
-- f = h ∘ inl _, g not a composition
case-reducible? (_ ∘ (inl _)) id = no λ ()
case-reducible? (_ ∘ (inl _)) fst = no λ ()
case-reducible? (_ ∘ (inl _)) snd = no λ ()
case-reducible? (_ ∘ (inl _)) (⟨ _ , _ ⟩ _) = no λ ()
case-reducible? (_ ∘ (inl _)) (inl _) = no λ ()
case-reducible? (_ ∘ (inl _)) (inr _) = no λ ()
case-reducible? (_ ∘ (inl _)) (case _ _) = no λ ()
case-reducible? (_ ∘ (inl _)) terminal = no λ ()
case-reducible? (_ ∘ (inl _)) initial = no λ ()
case-reducible? (_ ∘ (inl _)) (curry _ _) = no λ ()
case-reducible? (_ ∘ (inl _)) apply = no λ ()
case-reducible? (_ ∘ (inl _)) (fold _) = no λ ()
case-reducible? (_ ∘ (inl _)) unfold = no λ ()
case-reducible? (_ ∘ (inl _)) arr = no λ ()
case-reducible? (_ ∘ (inl _)) (SigOp _) = no λ ()
-- f = h ∘ inl _, g = _ ∘ non-inr
case-reducible? (_ ∘ (inl _)) (_ ∘ id) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ fst) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ snd) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ (⟨ _ , _ ⟩ _)) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ (inl _)) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ (case _ _)) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ terminal) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ initial) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ (curry _ _)) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ apply) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ fold Heap) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ unfold) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ arr) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ (SigOp _)) = no λ ()
case-reducible? (_ ∘ (inl _)) (_ ∘ (_ ∘ _)) = no λ ()