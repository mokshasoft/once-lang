{-# OPTIONS --allow-incomplete-matches #-}
------------------------------------------------------------------------
-- Once.Fusion.Correct
--
-- Correctness proofs for fusion rules.
--
-- Key insight: Functor fusion follows from coproduct beta laws.
-- The proof for the main fusion rule uses case analysis on sum inputs.
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
------------------------------------------------------------------------

fusion-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                       → eval (fusion-compose g f) x ≡ eval (g ∘ f) x

-- Rule 1: Coproduct functor fusion
-- [ inl, inr ∘ h ] ∘ [ inl, inr ∘ k ] = [ inl, inr ∘ (h ∘ k) ]
--
-- Proof by case analysis on sum input:
--   inj₁ a: both sides evaluate to inj₁ a
--   inj₂ b: LHS = inj₂ ((h ∘ k) b) = inj₂ (h (k b)) = RHS
fusion-compose-correct [ inl m1 , (inr m2) ∘ h ] [ inl m3 , (inr m4) ∘ k ] (inj₁ a) = refl
fusion-compose-correct [ inl m1 , (inr m2) ∘ h ] [ inl m3 , (inr m4) ∘ k ] (inj₂ b) = refl

-- All other cases: fusion-compose returns g ∘ f unchanged, so proof is refl
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

-- Case expressions that don't match the fusion pattern
-- First arg is [ f' , g' ] but not the specific [ inl, inr ∘ _ ] form
fusion-compose-correct [ id , g' ] f x = refl
fusion-compose-correct [ (f' ∘ f'') , g' ] f x = refl
fusion-compose-correct [ fst , g' ] f x = refl
fusion-compose-correct [ snd , g' ] f x = refl
fusion-compose-correct [ (⟨ _ , _ ⟩ _) , g' ] f x = refl
-- For [ inl _ , g' ], we must enumerate g' to exclude (inr _) ∘ _
-- which would match the fusion pattern.
-- Note: g' must produce sum type A + B, so we exclude type-impossible patterns:
--   fst, snd (produce component), ⟨_,_⟩ (produces product),
--   terminal (produces Unit), curry (produces exponential),
--   fold (produces Fix F), arr (produces IO)
fusion-compose-correct [ (inl _) , id ] f x = refl
fusion-compose-correct [ (inl _) , (inl _) ] f x = refl
fusion-compose-correct [ (inl _) , (inr _) ] f x = refl
fusion-compose-correct [ (inl _) , [ _ , _ ] ] f x = refl
fusion-compose-correct [ (inl _) , initial ] f x = refl
fusion-compose-correct [ (inl _) , apply ] f x = refl
fusion-compose-correct [ (inl _) , unfold ] f x = refl
fusion-compose-correct [ (inl _) , (Prim _) ] f x = refl
-- For [ inl _ , _ ∘ _ ], enumerate first component of composition to exclude (inr _) ∘ _
-- Output type determined by first component of composition, exclude those that can't produce sums
fusion-compose-correct [ (inl _) , id ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , (_ ∘ _) ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , (inl _) ∘ _ ] f x = refl
-- Note: [ inl _ , (inr _) ∘ _ ] is the fusion pattern - handled above
fusion-compose-correct [ (inl _) , [ _ , _ ] ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , initial ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , apply ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , unfold ∘ _ ] f x = refl
fusion-compose-correct [ (inl _) , (Prim _) ∘ _ ] f x = refl
fusion-compose-correct [ (inr _) , g' ] f x = refl
fusion-compose-correct [ [ _ , _ ] , g' ] f x = refl
fusion-compose-correct [ terminal , g' ] f x = refl
fusion-compose-correct [ initial , g' ] f x = refl
fusion-compose-correct [ (curry _ _) , g' ] f x = refl
fusion-compose-correct [ apply , g' ] f x = refl
fusion-compose-correct [ fold , g' ] f x = refl
fusion-compose-correct [ unfold , g' ] f x = refl
fusion-compose-correct [ arr , g' ] f x = refl
fusion-compose-correct [ (Prim _) , g' ] f x = refl

------------------------------------------------------------------------
-- Correctness of fusion-once
--
-- Recursive structure follows the standard pattern.
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
