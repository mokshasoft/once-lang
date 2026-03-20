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
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Fusion
open import Once.Postulates using (extensionality)

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
                       → eval′ (fusion-compose g f) x ≡ eval′ (g ∘ f) x

------------------------------------------------------------------------
-- FUSION RULE 1: Right functor fusion
-- [ inl, inr ∘ h ] ∘ [ inl, inr ∘ k ] = [ inl, inr ∘ (h ∘ k) ]
------------------------------------------------------------------------

fusion-compose-correct (case (inl m1) ((inr m2) ∘ h)) (case (inl m3) ((inr m4) ∘ k)) (inj₁ a) = refl
fusion-compose-correct (case (inl m1) ((inr m2) ∘ h)) (case (inl m3) ((inr m4) ∘ k)) (inj₂ b) = refl

------------------------------------------------------------------------
-- FUSION RULE 2: Bimap fusion
-- [ inl ∘ f, inr ∘ g ] ∘ [ inl ∘ h, inr ∘ k ] = [ inl ∘ (f ∘ h), inr ∘ (g ∘ k) ]
------------------------------------------------------------------------

fusion-compose-correct (case ((inl m1) ∘ f) ((inr m2) ∘ g)) (case ((inl m3) ∘ h) ((inr m4) ∘ k)) (inj₁ a) = refl
fusion-compose-correct (case ((inl m1) ∘ f) ((inr m2) ∘ g)) (case ((inl m3) ∘ h) ((inr m4) ∘ k)) (inj₂ b) = refl

------------------------------------------------------------------------
-- FUSION RULE 3: Left functor fusion
-- [ inl ∘ f, inr ] ∘ [ inl ∘ g, inr ] = [ inl ∘ (f ∘ g), inr ]
------------------------------------------------------------------------

fusion-compose-correct (case ((inl m1) ∘ f) (inr m2)) (case ((inl m3) ∘ g) (inr m4)) (inj₁ a) = refl
fusion-compose-correct (case ((inl m1) ∘ f) (inr m2)) (case ((inl m3) ∘ g) (inr m4)) (inj₂ b) = refl

------------------------------------------------------------------------
-- FUSION RULE 4a: Mixed fusion (bimap after right fmap)
-- [ inl ∘ f, inr ∘ g ] ∘ [ inl, inr ∘ k ] = [ inl ∘ f, inr ∘ (g ∘ k) ]
------------------------------------------------------------------------

fusion-compose-correct (case ((inl m1) ∘ f) ((inr m2) ∘ g)) (case (inl m3) ((inr m4) ∘ k)) (inj₁ a) = refl
fusion-compose-correct (case ((inl m1) ∘ f) ((inr m2) ∘ g)) (case (inl m3) ((inr m4) ∘ k)) (inj₂ b) = refl

------------------------------------------------------------------------
-- FUSION RULE 4b: Mixed fusion (right fmap after bimap)
-- [ inl, inr ∘ h ] ∘ [ inl ∘ f, inr ∘ g ] = [ inl ∘ f, inr ∘ (h ∘ g) ]
------------------------------------------------------------------------

fusion-compose-correct (case (inl m1) ((inr m2) ∘ h)) (case ((inl m3) ∘ f) ((inr m4) ∘ g)) (inj₁ a) = refl
fusion-compose-correct (case (inl m1) ((inr m2) ∘ h)) (case ((inl m3) ∘ f) ((inr m4) ∘ g)) (inj₂ b) = refl

------------------------------------------------------------------------
-- FUSION RULE 5a: Mixed fusion (bimap after left fmap)
-- [ inl ∘ f, inr ∘ g ] ∘ [ inl ∘ h, inr ] = [ inl ∘ (f ∘ h), inr ∘ g ]
------------------------------------------------------------------------

fusion-compose-correct (case ((inl m1) ∘ f) ((inr m2) ∘ g)) (case ((inl m3) ∘ h) (inr m4)) (inj₁ a) = refl
fusion-compose-correct (case ((inl m1) ∘ f) ((inr m2) ∘ g)) (case ((inl m3) ∘ h) (inr m4)) (inj₂ b) = refl

------------------------------------------------------------------------
-- FUSION RULE 5b: Mixed fusion (left fmap after bimap)
-- [ inl ∘ f, inr ] ∘ [ inl ∘ h, inr ∘ k ] = [ inl ∘ (f ∘ h), inr ∘ k ]
------------------------------------------------------------------------

fusion-compose-correct (case ((inl m1) ∘ f) (inr m2)) (case ((inl m3) ∘ h) ((inr m4) ∘ k)) (inj₁ a) = refl
fusion-compose-correct (case ((inl m1) ∘ f) (inr m2)) (case ((inl m3) ∘ h) ((inr m4) ∘ k)) (inj₂ b) = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , (inr _) ∘ _ ] but second arg doesn't match
-- Second arg must produce sum type
-- Note: Rule 4b covers [ (inl _) ∘ _ , (inr _) ∘ _ ], so we exclude that
------------------------------------------------------------------------

-- Second arg: id
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) id x = refl

-- Second arg: composition
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (f ∘ f') x = refl

-- Second arg: fst, snd (can produce sum if component is sum)
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) fst x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) snd x = refl

-- Second arg: injections
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (inl _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (inr _) x = refl

-- Second arg: initial, apply, unfold, Prim
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) initial x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) apply x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) unfold x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (Prim _) x = refl

-- Second arg: case (case f' g') where first component f' is NOT (inl _) or (inl _) ∘ _
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case id _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (id ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((_ ∘ _) ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (fst ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (snd ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inr _) ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((case _ _) ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (initial ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (apply ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (unfold ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((Prim _) ∘ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case fst _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case snd _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inr _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (case _ _) _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case initial _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case apply _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case unfold _) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (Prim _) _) x = refl

-- Second arg: case [ (inl _) , g' ] where g' is NOT (inr _) ∘ _
-- (Rule 1 covers [ (inl _) , (inr _) ∘ _ ])
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) id) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) fst) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) snd) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (inl _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (inr _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (case _ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) initial) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) apply) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) unfold) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (Prim _)) x = refl

-- Second arg: case [ (inl _) , _ ∘ _ ] where first of composition is NOT (inr _)
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (id ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) ((_ ∘ _) ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (fst ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (snd ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) ((inl _) ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) ((case _ _) ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (initial ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (apply ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) (unfold ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case (inl _) ((Prim _) ∘ _)) x = refl

-- Second arg: case [ (inl _) ∘ _ , g' ] where g' is NOT (inr _) ∘ _
-- (Rule 4b covers [ (inl _) ∘ _ , (inr _) ∘ _ ])
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) id) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) fst) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) snd) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (inl _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (inr _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (case _ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) initial) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) apply) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) unfold) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (Prim _)) x = refl

-- Second arg: case [ (inl _) ∘ _ , h ∘ _ ] where h is NOT (inr _)
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (id ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((_ ∘ _) ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (fst ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (snd ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((inl _) ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((case _ _) ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (initial ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (apply ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (unfold ∘ _)) x = refl
fusion-compose-correct (case (inl _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((Prim _) ∘ _)) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , fst ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct (case (inl _) fst) id x = refl
fusion-compose-correct (case (inl _) fst) (f ∘ f') x = refl
fusion-compose-correct (case (inl _) fst) fst x = refl
fusion-compose-correct (case (inl _) fst) snd x = refl
fusion-compose-correct (case (inl _) fst) (inl _) x = refl
fusion-compose-correct (case (inl _) fst) (inr _) x = refl
fusion-compose-correct (case (inl _) fst) (case _ _) x = refl
fusion-compose-correct (case (inl _) fst) initial x = refl
fusion-compose-correct (case (inl _) fst) apply x = refl
fusion-compose-correct (case (inl _) fst) unfold x = refl
fusion-compose-correct (case (inl _) fst) (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , snd ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct (case (inl _) snd) id x = refl
fusion-compose-correct (case (inl _) snd) (f ∘ f') x = refl
fusion-compose-correct (case (inl _) snd) fst x = refl
fusion-compose-correct (case (inl _) snd) snd x = refl
fusion-compose-correct (case (inl _) snd) (inl _) x = refl
fusion-compose-correct (case (inl _) snd) (inr _) x = refl
fusion-compose-correct (case (inl _) snd) (case _ _) x = refl
fusion-compose-correct (case (inl _) snd) initial x = refl
fusion-compose-correct (case (inl _) snd) apply x = refl
fusion-compose-correct (case (inl _) snd) unfold x = refl
fusion-compose-correct (case (inl _) snd) (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , fst ∘ _ ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct (case (inl _) (fst ∘ _)) id x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) (f ∘ f') x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) fst x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) snd x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) (inl _) x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) (inr _) x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) (case _ _) x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) initial x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) apply x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) unfold x = refl
fusion-compose-correct (case (inl _) (fst ∘ _)) (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , snd ∘ _ ] - enumerate all second args
------------------------------------------------------------------------

fusion-compose-correct (case (inl _) (snd ∘ _)) id x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) (f ∘ f') x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) fst x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) snd x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) (inl _) x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) (inr _) x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) (case _ _) x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) initial x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) apply x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) unfold x = refl
fusion-compose-correct (case (inl _) (snd ∘ _)) (Prim _) x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , g' ] where g' is other non-composition forms
------------------------------------------------------------------------

fusion-compose-correct (case (inl _) id) f x = refl
fusion-compose-correct (case (inl _) (inl _)) f x = refl
fusion-compose-correct (case (inl _) (inr _)) f x = refl
fusion-compose-correct (case (inl _) (case _ _)) f x = refl
fusion-compose-correct (case (inl _) initial) f x = refl
fusion-compose-correct (case (inl _) apply) f x = refl
fusion-compose-correct (case (inl _) unfold) f x = refl
fusion-compose-correct (case (inl _) (Prim _)) f x = refl

------------------------------------------------------------------------
-- First arg is [ inl _ , _ ∘ _ ] where first of composition is NOT inr/fst/snd
------------------------------------------------------------------------

fusion-compose-correct (case (inl _) (id ∘ _)) f x = refl
fusion-compose-correct (case (inl _) ((_ ∘ _) ∘ _)) f x = refl
fusion-compose-correct (case (inl _) ((inl _) ∘ _)) f x = refl
fusion-compose-correct (case (inl _) ((case _ _) ∘ _)) f x = refl
fusion-compose-correct (case (inl _) (initial ∘ _)) f x = refl
fusion-compose-correct (case (inl _) (apply ∘ _)) f x = refl
fusion-compose-correct (case (inl _) (unfold ∘ _)) f x = refl
fusion-compose-correct (case (inl _) ((Prim _) ∘ _)) f x = refl

------------------------------------------------------------------------
-- First arg is initial (empty type eliminator)
-- Second arg must produce Void, so enumerate those cases
------------------------------------------------------------------------

fusion-compose-correct initial (f ∘ f') x = refl
fusion-compose-correct initial (case id _) x = refl
fusion-compose-correct initial (case (_ ∘ _) _) x = refl
fusion-compose-correct initial (case fst _) x = refl
fusion-compose-correct initial (case snd _) x = refl
fusion-compose-correct initial (case (case _ _) _) x = refl
fusion-compose-correct initial (case initial _) x = refl
fusion-compose-correct initial (case apply _) x = refl
fusion-compose-correct initial (case unfold _) x = refl
fusion-compose-correct initial (case (Prim _) _) x = refl
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
fusion-compose-correct (fold _) f x = refl
fusion-compose-correct unfold f x = refl
fusion-compose-correct arr f x = refl
fusion-compose-correct (Prim _) f x = refl

------------------------------------------------------------------------
-- First arg is (case f' g') where f' is NOT (inl _) or (inl _) ∘ _
-- Note: (inl _) ∘ _ forms are covered by fusion rules 2, 3, 4a, 5a, 5b
------------------------------------------------------------------------

fusion-compose-correct (case id _) f x = refl
fusion-compose-correct (case (id ∘ _) _) f x = refl
fusion-compose-correct (case ((_ ∘ _) ∘ _) _) f x = refl
fusion-compose-correct (case (fst ∘ _) _) f x = refl
fusion-compose-correct (case (snd ∘ _) _) f x = refl
fusion-compose-correct (case ((⟨ _ , _ ⟩ _) ∘ _) _) f x = refl
fusion-compose-correct (case ((inr _) ∘ _) _) f x = refl
fusion-compose-correct (case ((case _ _) ∘ _) _) f x = refl
fusion-compose-correct (case (terminal ∘ _) _) f x = refl
fusion-compose-correct (case (initial ∘ _) _) f x = refl
fusion-compose-correct (case ((curry _ _) ∘ _) _) f x = refl
fusion-compose-correct (case (apply ∘ _) _) f x = refl
fusion-compose-correct (case ((fold _) ∘ _) _) f x = refl
fusion-compose-correct (case (unfold ∘ _) _) f x = refl
fusion-compose-correct (case (arr ∘ _) _) f x = refl
fusion-compose-correct (case ((Prim _) ∘ _) _) f x = refl
fusion-compose-correct (case fst _) f x = refl
fusion-compose-correct (case snd _) f x = refl
fusion-compose-correct (case (⟨ _ , _ ⟩ _) _) f x = refl
fusion-compose-correct (case (inr _) _) f x = refl
fusion-compose-correct (case (case _ _) _) f x = refl
fusion-compose-correct (case terminal _) f x = refl
fusion-compose-correct (case initial _) f x = refl
fusion-compose-correct (case (curry _ _) _) f x = refl
fusion-compose-correct (case apply _) f x = refl
fusion-compose-correct (case (fold _) _) f x = refl
fusion-compose-correct (case unfold _) f x = refl
fusion-compose-correct (case arr _) f x = refl
fusion-compose-correct (case (Prim _) _) f x = refl

------------------------------------------------------------------------
-- First arg is [ (inl _) ∘ _ , g' ] - covers cases NOT matching fusion rules
-- Rules 2, 4a, 5a have g' = (inr _) ∘ _ AND specific second args
-- Rules 3, 5b have g' = inr _ AND specific second args
------------------------------------------------------------------------

-- g' is NOT (inr _) or (inr _) ∘ _
fusion-compose-correct (case ((inl _) ∘ _) id) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) fst) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) snd) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inl _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (case _ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) initial) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) apply) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) unfold) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (Prim _)) f x = refl

-- g' = h ∘ _ where h is NOT (inr _)
fusion-compose-correct (case ((inl _) ∘ _) (id ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((_ ∘ _) ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (fst ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (snd ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inl _) ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((case _ _) ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (initial ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (apply ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) (unfold ∘ _)) f x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((Prim _) ∘ _)) f x = refl

------------------------------------------------------------------------
-- First arg is [ (inl _) ∘ _ , (inr _) ∘ _ ] - BIMAP FORM
-- Rules 2, 4a, 5a match specific second args, need other second args
-- Rule 2: second is [ (inl _) ∘ _ , (inr _) ∘ _ ]
-- Rule 4a: second is [ inl _ , (inr _) ∘ _ ]
-- Rule 5a: second is [ (inl _) ∘ _ , inr _ ]
------------------------------------------------------------------------

-- Second arg: non-case forms
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) id x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (f ∘ f') x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) fst x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) snd x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (inl _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (inr _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) initial x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) apply x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) unfold x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (Prim _) x = refl

-- Second arg: case where first branch is NOT (inl _) or (inl _) ∘ _
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case id _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (id ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((_ ∘ _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (fst ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (snd ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inr _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((case _ _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (initial ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (apply ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (unfold ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((Prim _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case fst _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case snd _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inr _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (case _ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case initial _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case apply _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case unfold _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (Prim _) _) x = refl

-- Second arg: case [ (inl _) , g' ] where g' is NOT (inr _) ∘ _
-- (Rule 4a covers [ (inl _) , (inr _) ∘ _ ])
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) id) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) fst) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) snd) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (inl _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (inr _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (case _ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) initial) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) apply) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) unfold) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (Prim _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (id ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) ((_ ∘ _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (fst ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (snd ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) ((inl _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) ((case _ _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (initial ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (apply ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) (unfold ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case (inl _) ((Prim _) ∘ _)) x = refl

-- Second arg: case [ (inl _) ∘ _ , g' ] where g' is NOT (inr _) ∘ _ or inr _
-- (Rule 2 covers [ (inl _) ∘ _ , (inr _) ∘ _ ], Rule 5a covers [ (inl _) ∘ _ , inr _ ])
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) id) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) fst) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) snd) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (inl _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (case _ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) initial) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) apply) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) unfold) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (Prim _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (id ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((_ ∘ _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (fst ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (snd ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((inl _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((case _ _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (initial ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (apply ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) (unfold ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) ((inr _) ∘ _)) (case ((inl _) ∘ _) ((Prim _) ∘ _)) x = refl

------------------------------------------------------------------------
-- First arg is [ (inl _) ∘ _ , inr _ ] - LEFT FMAP FORM
-- Rules 3, 5b match specific second args
-- Rule 3: second is [ (inl _) ∘ _ , inr _ ]
-- Rule 5b: second is [ (inl _) ∘ _ , (inr _) ∘ _ ]
------------------------------------------------------------------------

-- Second arg: non-case forms
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) id x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (f ∘ f') x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) fst x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) snd x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (inl _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (inr _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) initial x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) apply x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) unfold x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (Prim _) x = refl

-- Second arg: case where first branch is NOT (inl _) or (inl _) ∘ _
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case id _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (id ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((_ ∘ _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (fst ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (snd ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inr _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((case _ _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (initial ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (apply ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (unfold ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((Prim _) ∘ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case fst _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case snd _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (inr _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (case _ _) _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case initial _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case apply _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case unfold _) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (Prim _) _) x = refl

-- Second arg: case [ (inl _) , g' ] where g' doesn't matter
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case (inl _) _) x = refl

-- Second arg: case [ (inl _) ∘ _ , g' ] where g' is NOT inr _ or (inr _) ∘ _
-- (Rule 3 covers [ (inl _) ∘ _ , inr _ ], Rule 5b covers [ (inl _) ∘ _ , (inr _) ∘ _ ])
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) id) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) fst) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) snd) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (inl _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (case _ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) initial) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) apply) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) unfold) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (Prim _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (id ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) ((_ ∘ _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (fst ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (snd ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) ((inl _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) ((case _ _) ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (initial ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (apply ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) (unfold ∘ _)) x = refl
fusion-compose-correct (case ((inl _) ∘ _) (inr _)) (case ((inl _) ∘ _) ((Prim _) ∘ _)) x = refl

-- free-heap cases (free-heap : IR Unit Unit is opaque, uses default case)
fusion-compose-correct (free-heap _) _ x = refl
-- case with free-heap in first branch (all use default case since no fusion rule matches)
fusion-compose-correct (case ((free-heap _) ∘ _) _) _ x = refl
fusion-compose-correct (case (free-heap _) _) _ x = refl

------------------------------------------------------------------------
-- Correctness of fusion-once
------------------------------------------------------------------------

fusion-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                    → eval′ (fusion-once f) x ≡ eval′ f x

fusion-once-correct id x = refl

fusion-once-correct (g ∘ f) x =
  trans (fusion-compose-correct (fusion-once g) (fusion-once f) x)
        (trans (cong (eval′ (fusion-once g)) (fusion-once-correct f x))
               (fusion-once-correct g (eval′ f x)))

fusion-once-correct fst x = refl
fusion-once-correct snd x = refl

fusion-once-correct (⟨ f , g ⟩ _) x =
  cong₂ _,_ (fusion-once-correct f x) (fusion-once-correct g x)

fusion-once-correct (inl _) x = refl
fusion-once-correct (inr _) x = refl

fusion-once-correct (case f g) (inj₁ a) = fusion-once-correct f a
fusion-once-correct (case f g) (inj₂ b) = fusion-once-correct g b

fusion-once-correct terminal x = refl
fusion-once-correct initial ()

fusion-once-correct (curry {q = q} f _) x =
  extensionality (λ b → fusion-once-correct f (x , b))

fusion-once-correct apply x = refl
fusion-once-correct (fold _) x = refl
fusion-once-correct unfold x = refl
fusion-once-correct arr x = refl
fusion-once-correct (Prim name) x = refl
fusion-once-correct (free-heap h) x = refl

------------------------------------------------------------------------
-- Correctness of bounded iteration
------------------------------------------------------------------------

fusion-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                 → eval′ (fusion-n n f) x ≡ eval′ f x
fusion-n-correct zero f x = refl
fusion-n-correct (suc n) f x =
  trans (fusion-n-correct n (fusion-once f) x)
        (fusion-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: fusion preserves semantics
------------------------------------------------------------------------

fusion-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
               → eval′ (fusion f) x ≡ eval′ f x
fusion-correct f x = fusion-n-correct 10 f x
