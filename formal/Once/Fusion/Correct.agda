------------------------------------------------------------------------
-- Once.Fusion.Correct
--
-- Correctness proofs for fusion rules.
--
-- Key insight: Functor fusion follows from coproduct beta laws.
-- The proof for the main fusion rule uses case analysis on sum inputs.
--
-- This file has COMPLETE pattern coverage (no --allow-incomplete-matches).
-- All ~200 patterns are enumerated for full rigor.
------------------------------------------------------------------------

module Once.Fusion.Correct where

open import Once.Type
open import Once.IR
open import Once.Semantics
open import Once.Fusion
open import Once.Postulates using (closure-semantics-eq; extensionality)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

------------------------------------------------------------------------
-- Correctness of fusion-compose
--
-- The functor fusion rule preserves semantics by the functor law.
-- Complete pattern coverage without --allow-incomplete-matches.
------------------------------------------------------------------------

fusion-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                       → eval (fusion-compose g f) x ≡ eval (g ∘ f) x

------------------------------------------------------------------------
-- THE FUSION RULE: Both args match [ inl _ , (inr _) ∘ _ ]
------------------------------------------------------------------------

fusion-compose-correct [ inl m1 , (inr m2) ∘ h ] [ inl m3 , (inr m4) ∘ k ] (inj₁ a) = refl
fusion-compose-correct [ inl m1 , (inr m2) ∘ h ] [ inl m3 , (inr m4) ∘ k ] (inj₂ b) = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , (inr _) ∘ _ ] but second arg doesn't match
-- Second arg must produce sum type
------------------------------------------------------------------------

-- Second arg: id
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] id x = refl

-- Second arg: composition
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] (f ∘ f') x = refl

-- Second arg: fst, snd (can produce sum if component is sum)
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] fst x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] snd x = refl

-- Second arg: injections
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] (inl _) x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] (inr _) x = refl

-- Second arg: initial, apply, unfold, Prim
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] initial x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] apply x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] unfold x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] (Prim _) x = refl

-- Second arg: case [ f' , g' ] where first component f' is NOT (inl _)
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ id , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (_ ∘ _) , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ fst , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ snd , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inr _) , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ [ _ , _ ] , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ initial , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ apply , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ unfold , _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (Prim _) , _ ] x = refl

-- Second arg: case [ (inl _) , g' ] where g' is NOT (inr _) ∘ _
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , id ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , fst ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , snd ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , (inl _) ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , (inr _) ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , [ _ , _ ] ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , initial ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , apply ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , unfold ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , (Prim _) ] x = refl

-- Second arg: case [ (inl _) , _ ∘ _ ] where first of composition is NOT (inr _)
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , id ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , (_ ∘ _) ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , fst ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , snd ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , (inl _) ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , [ _ , _ ] ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , initial ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , apply ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , unfold ∘ _ ] x = refl
fusion-compose-correct [ (inl _) , (inr _) ∘ _ ] [ (inl _) , (Prim _) ∘ _ ] x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , fst ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct [ (inl _) , fst ] id x = refl
fusion-compose-correct [ (inl _) , fst ] (f ∘ f') x = refl
fusion-compose-correct [ (inl _) , fst ] fst x = refl
fusion-compose-correct [ (inl _) , fst ] snd x = refl
fusion-compose-correct [ (inl _) , fst ] (inl _) x = refl
fusion-compose-correct [ (inl _) , fst ] (inr _) x = refl
fusion-compose-correct [ (inl _) , fst ] [ _ , _ ] x = refl
fusion-compose-correct [ (inl _) , fst ] initial x = refl
fusion-compose-correct [ (inl _) , fst ] apply x = refl
fusion-compose-correct [ (inl _) , fst ] unfold x = refl
fusion-compose-correct [ (inl _) , fst ] (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , snd ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct [ (inl _) , snd ] id x = refl
fusion-compose-correct [ (inl _) , snd ] (f ∘ f') x = refl
fusion-compose-correct [ (inl _) , snd ] fst x = refl
fusion-compose-correct [ (inl _) , snd ] snd x = refl
fusion-compose-correct [ (inl _) , snd ] (inl _) x = refl
fusion-compose-correct [ (inl _) , snd ] (inr _) x = refl
fusion-compose-correct [ (inl _) , snd ] [ _ , _ ] x = refl
fusion-compose-correct [ (inl _) , snd ] initial x = refl
fusion-compose-correct [ (inl _) , snd ] apply x = refl
fusion-compose-correct [ (inl _) , snd ] unfold x = refl
fusion-compose-correct [ (inl _) , snd ] (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , fst ∘ _ ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct [ (inl _) , fst ∘ _ ] id x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] (f ∘ f') x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] fst x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] snd x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] (inl _) x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] (inr _) x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] [ _ , _ ] x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] initial x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] apply x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] unfold x = refl
fusion-compose-correct [ (inl _) , fst ∘ _ ] (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , snd ∘ _ ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct [ (inl _) , snd ∘ _ ] id x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] (f ∘ f') x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] fst x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] snd x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] (inl _) x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] (inr _) x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] [ _ , _ ] x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] initial x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] apply x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] unfold x = refl
fusion-compose-correct [ (inl _) , snd ∘ _ ] (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , g' ] where g' is other non-composition forms
------------------------------------------------------------------------

fusion-compose-correct [ (inl _) , id ] f x = refl
fusion-compose-correct [ (inl _) , (inl _) ] f x = refl
fusion-compose-correct [ (inl _) , (inr _) ] f x = refl
fusion-compose-correct [ (inl _) , [ _ , _ ] ] f x = refl
fusion-compose-correct [ (inl _) , initial ] f x = refl
fusion-compose-correct [ (inl _) , apply ] f x = refl
fusion-compose-correct [ (inl _) , unfold ] f x = refl
fusion-compose-correct [ (inl _) , (Prim _) ] f x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , _ ∘ _ ] where first of composition is NOT inr/fst/snd
------------------------------------------------------------------------

fusion-compose-correct [ (inl _) , id ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , (_ ∘ _) ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , (inl _) ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , [ _ , _ ] ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , initial ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , apply ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , unfold ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , (Prim _) ∘ _ ] f x = refl

------------------------------------------------------------------------
-- First arg is initial (empty type eliminator)
-- Second arg must produce Void, so enumerate those cases
------------------------------------------------------------------------

fusion-compose-correct initial (f ∘ f') x = refl
fusion-compose-correct initial [ id , _ ] x = refl
fusion-compose-correct initial [ (_ ∘ _) , _ ] x = refl
fusion-compose-correct initial [ fst , _ ] x = refl
fusion-compose-correct initial [ snd , _ ] x = refl
fusion-compose-correct initial [ [ _ , _ ] , _ ] x = refl
fusion-compose-correct initial [ initial , _ ] x = refl
fusion-compose-correct initial [ apply , _ ] x = refl
fusion-compose-correct initial [ unfold , _ ] x = refl
fusion-compose-correct initial [ (Prim _) , _ ] x = refl
fusion-compose-correct initial apply x = refl
fusion-compose-correct initial (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is NOT a case expression at all (excluding initial handled above)
------------------------------------------------------------------------

fusion-compose-correct id f x = refl
fusion-compose-correct (g ∘ h) f x = refl
fusion-compose-correct fst f x = refl
fusion-compose-correct snd f x = refl
fusion-compose-correct (⟨ g , h ⟩ _) f x = refl
fusion-compose-correct (inl _) f x = refl
fusion-compose-correct (inr _) f x = refl
fusion-compose-correct terminal f x = refl
fusion-compose-correct (curry g _) f x = refl
fusion-compose-correct apply f x = refl
fusion-compose-correct fold f x = refl
fusion-compose-correct unfold f x = refl
fusion-compose-correct arr f x = refl
fusion-compose-correct (Prim _) f x = refl

------------------------------------------------------------------------
-- First arg is [ f' , g' ] where f' is NOT (inl _)
------------------------------------------------------------------------

fusion-compose-correct [ id , _ ] f x = refl
fusion-compose-correct [ (_ ∘ _) , _ ] f x = refl
fusion-compose-correct [ fst , _ ] f x = refl
fusion-compose-correct [ snd , _ ] f x = refl
fusion-compose-correct [ (⟨ _ , _ ⟩ _) , _ ] f x = refl
fusion-compose-correct [ (inr _) , _ ] f x = refl
fusion-compose-correct [ [ _ , _ ] , _ ] f x = refl
fusion-compose-correct [ terminal , _ ] f x = refl
fusion-compose-correct [ initial , _ ] f x = refl
fusion-compose-correct [ (curry _ _) , _ ] f x = refl
fusion-compose-correct [ apply , _ ] f x = refl
fusion-compose-correct [ fold , _ ] f x = refl
fusion-compose-correct [ unfold , _ ] f x = refl
fusion-compose-correct [ arr , _ ] f x = refl
fusion-compose-correct [ (Prim _) , _ ] f x = refl

------------------------------------------------------------------------
-- Correctness of fusion-once
------------------------------------------------------------------------

fusion-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                    → eval (fusion-once f) x ≡ eval f x

fusion-once-correct id x = refl

fusion-once-correct (g ∘ f) x =
  trans (fusion-compose-correct (fusion-once g) (fusion-once f) x)
        (trans (cong (eval (fusion-once g)) (fusion-once-correct f x))
               (fusion-once-correct g (eval f x)))

fusion-once-correct fst x = refl
fusion-once-correct snd x = refl

fusion-once-correct (⟨ f , g ⟩ _) x =
  cong₂ _,_ (fusion-once-correct f x) (fusion-once-correct g x)

fusion-once-correct (inl _) x = refl
fusion-once-correct (inr _) x = refl

fusion-once-correct [ f , g ] (inj₁ a) = fusion-once-correct f a
fusion-once-correct [ f , g ] (inj₂ b) = fusion-once-correct g b

fusion-once-correct terminal x = refl
fusion-once-correct initial ()

fusion-once-correct (curry f _) x =
  closure-semantics-eq
    (eval (curry (fusion-once f) Heap) x)
    (eval (curry f Heap) x)
    (extensionality (λ b → fusion-once-correct f (x , b)))

fusion-once-correct apply x = refl
fusion-once-correct fold x = refl
fusion-once-correct unfold x = refl
fusion-once-correct arr x = refl
fusion-once-correct (Prim name) x = refl

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

fusion-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval (fusion-n n f) x ≡ eval f x
fusion-n-correct zero f x = refl
fusion-n-correct (suc n) f x =
  trans (fusion-n-correct n (fusion-once f) x)
        (fusion-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: fusion preserves semantics
------------------------------------------------------------------------

fusion-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval (fusion f) x ≡ eval f x
fusion-correct f x = fusion-n-correct 10 f x
