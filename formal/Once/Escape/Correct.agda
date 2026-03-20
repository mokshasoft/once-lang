------------------------------------------------------------------------
-- Once.Escape.Correct
--
-- Correctness proofs for escape analysis.
--
-- Key insight: AllocMode is semantically transparent - it is explicitly
-- ignored in the eval function (Once/Semantics.agda). Therefore, all
-- escape analysis rewrites that only change AllocMode are trivially
-- correct by refl.
--
-- This is the beauty of verified optimization: we can be aggressive
-- with escape analysis because we have machine-checked proofs that
-- the rewrites preserve semantics.
--
-- This file has COMPLETE pattern coverage (no --allow-incomplete-matches).
------------------------------------------------------------------------

module Once.Escape.Correct where

open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Escape
open import Once.Postulates using (extensionality)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

------------------------------------------------------------------------
-- Correctness of escape-compose
--
-- All cases are trivially correct because AllocMode is ignored in eval.
-- The semantic value is identical regardless of Stack vs Heap mode.
-- Complete pattern coverage without --allow-incomplete-matches.
------------------------------------------------------------------------

escape-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                       → eval′ (escape-compose g f) x ≡ eval′ (g ∘ f) x

------------------------------------------------------------------------
-- Escape rules that match specific patterns
------------------------------------------------------------------------

-- Rule 1: fst ∘ ⟨ f , g ⟩ - AllocMode transparent in pair
escape-compose-correct fst (⟨ f , g ⟩ _) x = refl

-- Rule 2: snd ∘ ⟨ f , g ⟩ - AllocMode transparent in pair
escape-compose-correct snd (⟨ f , g ⟩ _) x = refl

-- Rule 3: (case f g) ∘ inl - AllocMode transparent in injection
escape-compose-correct (case f g) (inl _) x = refl

-- Rule 4: (case f g) ∘ inr - AllocMode transparent in injection
escape-compose-correct (case f g) (inr _) x = refl

-- Rule 5: apply ∘ ⟨ curry f , x ⟩ - AllocMode transparent in curry and pair
escape-compose-correct apply (⟨ curry f _ , h ⟩ _) x = refl

-- Rule 6: apply ∘ ⟨ f , x ⟩ - AllocMode transparent in pair (non-curry f)
escape-compose-correct apply (⟨ id , h ⟩ _) x = refl
escape-compose-correct apply (⟨ g ∘ g' , h ⟩ _) x = refl
escape-compose-correct apply (⟨ fst , h ⟩ _) x = refl
escape-compose-correct apply (⟨ snd , h ⟩ _) x = refl
escape-compose-correct apply (⟨ (case g g') , h ⟩ _) x = refl
escape-compose-correct apply (⟨ initial , h ⟩ _) x = refl
escape-compose-correct apply (⟨ apply , h ⟩ _) x = refl
escape-compose-correct apply (⟨ unfold , h ⟩ _) x = refl
escape-compose-correct apply (⟨ Prim _ , h ⟩ _) x = refl

-- Rules 7-8: fold ∘ inl/inr - AllocMode transparent in injection
escape-compose-correct (fold _) (inl _) x = refl
escape-compose-correct (fold _) (inr _) x = refl

-- Rules 9-10: terminal discards values - AllocMode transparent
escape-compose-correct terminal (⟨ f , g ⟩ _) x = refl
escape-compose-correct terminal (curry f _) x = refl

-- Rules 11-12: (f ∘ fst/snd) ∘ ⟨ g , h ⟩ - AllocMode transparent in pair
escape-compose-correct (f ∘ fst) (⟨ g , h ⟩ _) x = refl
escape-compose-correct (f ∘ snd) (⟨ g , h ⟩ _) x = refl

------------------------------------------------------------------------
-- First arg: id
------------------------------------------------------------------------

escape-compose-correct id f x = refl

------------------------------------------------------------------------
-- First arg: g ∘ h (composition) - enumerate inner h
------------------------------------------------------------------------

escape-compose-correct (g ∘ id) f x = refl
escape-compose-correct (g ∘ (h ∘ h')) f x = refl
escape-compose-correct (g ∘ ⟨ h , h' ⟩ _) f x = refl
escape-compose-correct (g ∘ inl _) f x = refl
escape-compose-correct (g ∘ inr _) f x = refl
escape-compose-correct (g ∘ (case h h')) f x = refl
escape-compose-correct (g ∘ terminal) f x = refl
escape-compose-correct (g ∘ initial) f x = refl
escape-compose-correct (g ∘ curry h _) f x = refl
escape-compose-correct (g ∘ apply) f x = refl
escape-compose-correct (g ∘ (fold Heap)) f x = refl
escape-compose-correct (g ∘ unfold) f x = refl
escape-compose-correct (g ∘ arr) f x = refl
escape-compose-correct (g ∘ Prim _) f x = refl

-- (g ∘ fst) with second arg NOT ⟨_,_⟩ (that's rule 11)
escape-compose-correct (g ∘ fst) id x = refl
escape-compose-correct (g ∘ fst) (f ∘ f') x = refl
escape-compose-correct (g ∘ fst) fst x = refl
escape-compose-correct (g ∘ fst) snd x = refl
escape-compose-correct (g ∘ fst) (case _ _) x = refl
escape-compose-correct (g ∘ fst) apply x = refl
escape-compose-correct (g ∘ fst) unfold x = refl
escape-compose-correct (g ∘ fst) (Prim _) x = refl

-- (g ∘ snd) with second arg NOT ⟨_,_⟩ (that's rule 12)
escape-compose-correct (g ∘ snd) id x = refl
escape-compose-correct (g ∘ snd) (f ∘ f') x = refl
escape-compose-correct (g ∘ snd) fst x = refl
escape-compose-correct (g ∘ snd) snd x = refl
escape-compose-correct (g ∘ snd) (case _ _) x = refl
escape-compose-correct (g ∘ snd) apply x = refl
escape-compose-correct (g ∘ snd) unfold x = refl
escape-compose-correct (g ∘ snd) (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: fst (with second arg NOT ⟨_,_⟩, that's rule 1)
------------------------------------------------------------------------

escape-compose-correct fst id x = refl
escape-compose-correct fst (g ∘ h) x = refl
escape-compose-correct fst fst x = refl
escape-compose-correct fst snd x = refl
escape-compose-correct fst (case _ _) x = refl
escape-compose-correct fst apply x = refl
escape-compose-correct fst unfold x = refl
escape-compose-correct fst (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: snd (with second arg NOT ⟨_,_⟩, that's rule 2)
------------------------------------------------------------------------

escape-compose-correct snd id x = refl
escape-compose-correct snd (g ∘ h) x = refl
escape-compose-correct snd fst x = refl
escape-compose-correct snd snd x = refl
escape-compose-correct snd (case _ _) x = refl
escape-compose-correct snd apply x = refl
escape-compose-correct snd unfold x = refl
escape-compose-correct snd (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: ⟨_,_⟩, inl, inr
------------------------------------------------------------------------

escape-compose-correct (⟨ g , h ⟩ _) f x = refl
escape-compose-correct (inl _) f x = refl
escape-compose-correct (inr _) f x = refl

------------------------------------------------------------------------
-- First arg: (case _ _) (with second arg NOT inl/inr, those are rules 3-4)
------------------------------------------------------------------------

escape-compose-correct (case g h) id x = refl
escape-compose-correct (case g h) (f ∘ f') x = refl
escape-compose-correct (case g h) fst x = refl
escape-compose-correct (case g h) snd x = refl
escape-compose-correct (case g h) (case f f') x = refl
escape-compose-correct (case g h) apply x = refl
escape-compose-correct (case g h) unfold x = refl
escape-compose-correct (case g h) (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: terminal (with second arg NOT ⟨_,_⟩/curry, those are rules 9-10)
------------------------------------------------------------------------

escape-compose-correct terminal id x = refl
escape-compose-correct terminal (f ∘ g) x = refl
escape-compose-correct terminal fst x = refl
escape-compose-correct terminal snd x = refl
escape-compose-correct terminal (inl _) x = refl
escape-compose-correct terminal (inr _) x = refl
escape-compose-correct terminal (case f g) x = refl
escape-compose-correct terminal terminal x = refl
escape-compose-correct terminal apply x = refl
escape-compose-correct terminal (fold _) x = refl
escape-compose-correct terminal unfold x = refl
escape-compose-correct terminal arr x = refl
escape-compose-correct terminal (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: initial
------------------------------------------------------------------------

escape-compose-correct initial (f ∘ f') x = refl
escape-compose-correct initial (case _ _) x = refl
escape-compose-correct initial apply x = refl
escape-compose-correct initial (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: curry
------------------------------------------------------------------------

escape-compose-correct (curry g _) f x = refl

------------------------------------------------------------------------
-- First arg: apply (with second arg NOT ⟨_,_⟩, those are rules 5-6)
------------------------------------------------------------------------

escape-compose-correct apply id x = refl
escape-compose-correct apply (g ∘ h) x = refl
escape-compose-correct apply fst x = refl
escape-compose-correct apply snd x = refl
escape-compose-correct apply (case _ _) x = refl
escape-compose-correct apply apply x = refl
escape-compose-correct apply unfold x = refl
escape-compose-correct apply (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: fold (with second arg NOT inl/inr, those are rules 7-8)
------------------------------------------------------------------------

escape-compose-correct (fold _) id x = refl
escape-compose-correct (fold _) (f ∘ g) x = refl
escape-compose-correct (fold _) fst x = refl
escape-compose-correct (fold _) snd x = refl
escape-compose-correct (fold _) (⟨ f , g ⟩ _) x = refl
escape-compose-correct (fold _) (case f g) x = refl
escape-compose-correct (fold _) terminal x = refl
escape-compose-correct (fold _) (curry _ _) x = refl
escape-compose-correct (fold _) apply x = refl
escape-compose-correct (fold _) (fold _) x = refl
escape-compose-correct (fold _) unfold x = refl
escape-compose-correct (fold _) arr x = refl
escape-compose-correct (fold _) (Prim _) x = refl

------------------------------------------------------------------------
-- First arg: unfold, arr, Prim
------------------------------------------------------------------------

escape-compose-correct unfold f x = refl
escape-compose-correct arr f x = refl
escape-compose-correct (Prim _) f x = refl
-- free-heap as first arg (opaque, uses default compose)
escape-compose-correct (free-heap _) _ x = refl
-- Compositions starting with fold Stack or free-heap (all use default case)
escape-compose-correct (_ ∘ (fold Stack)) _ x = refl
escape-compose-correct (_ ∘ (free-heap _)) _ x = refl
-- free-heap as second arg with fold or terminal as first arg
escape-compose-correct (fold _) (free-heap _) x = refl
escape-compose-correct terminal (free-heap _) x = refl

------------------------------------------------------------------------
-- Correctness of escape-once
--
-- Recursive structure follows optimize-once-correct pattern.
-- Each case either uses escape-compose-correct or recurses.
------------------------------------------------------------------------

escape-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                    → eval′ (escape-once f) x ≡ eval′ f x

escape-once-correct id x = refl

escape-once-correct (g ∘ f) x =
  trans (escape-compose-correct (escape-once g) (escape-once f) x)
        (trans (cong (eval′ (escape-once g)) (escape-once-correct f x))
               (escape-once-correct g (eval′ f x)))

escape-once-correct fst x = refl
escape-once-correct snd x = refl

escape-once-correct (⟨ f , g ⟩ _) x =
  cong₂ _,_ (escape-once-correct f x) (escape-once-correct g x)

escape-once-correct (inl _) x = refl
escape-once-correct (inr _) x = refl

escape-once-correct (case f g) (inj₁ a) = escape-once-correct f a
escape-once-correct (case f g) (inj₂ b) = escape-once-correct g b

escape-once-correct terminal x = refl
escape-once-correct initial ()

escape-once-correct (curry {q = q} f _) x =
  extensionality (λ b → escape-once-correct f (x , b))

escape-once-correct apply x = refl
escape-once-correct (fold _) x = refl
escape-once-correct unfold x = refl
escape-once-correct arr x = refl
escape-once-correct (Prim name) x = refl
escape-once-correct (free-heap h) x = refl

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

escape-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval′ (escape-n n f) x ≡ eval′ f x
escape-n-correct zero f x = refl
escape-n-correct (suc n) f x =
  trans (escape-n-correct n (escape-once f) x)
        (escape-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: escape analysis preserves semantics
------------------------------------------------------------------------

escape-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval′ (escape f) x ≡ eval′ f x
escape-correct f x = escape-n-correct 10 f x
