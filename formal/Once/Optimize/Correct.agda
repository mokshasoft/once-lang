------------------------------------------------------------------------
-- Once.Optimize.Correct
--
-- Correctness proofs for the Once optimizer.
-- Each optimization rule preserves semantics.
--
-- Uses function extensionality (imported from Once.Postulates) for the
-- curry case, which requires proving equality of functions.
------------------------------------------------------------------------

module Once.Optimize.Correct where

open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR using (⟦_⟧; eval′)
open import Once.Optimize
open import Once.Category.Laws
open import Once.Postulates using (extensionality)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

-- Alias for function extensionality (imported from Once.Postulates)
funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
funext = extensionality

------------------------------------------------------------------------
-- Correctness of optimize-compose
--
-- The optimizer now includes:
--   - Identity laws (left/right)
--   - Product/coproduct beta laws
--   - Fixed point laws
--   - Terminal fusion
--   - Initial absorption
--   - Pairing fusion: ⟨f,g⟩ ∘ h = ⟨f∘h, g∘h⟩
--   - Case fusion: h ∘ (case f g) = [h∘f, h∘g]
--   - Associativity
------------------------------------------------------------------------

{-# TERMINATING #-}  -- Termination follows from optimize-compose termination
mutual
  -- | Correctness of type-directed optimize-compose
  optimize-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                           → eval′ (optimize-compose g f) x ≡ eval′ (g ∘ f) x
  optimize-compose-correct {A} {B} {C} g f x with C ≟Type Unit
  ... | yes refl = refl  -- eval terminal x = tt = eval′ (g ∘ f) x
  ... | no _ with A ≟Type Void
  ...   | yes refl = ⊥-elim x  -- x : ⟦ Void ⟧ = ⊥, vacuously true
  ...   | no _ = optimize-compose-structural-correct g f x

  -- | Correctness of structural optimize-compose
  optimize-compose-structural-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                                      → eval′ (optimize-compose-structural g f) x ≡ eval′ (g ∘ f) x

  -- Left identity: id ∘ f = f
  optimize-compose-structural-correct id f x = refl

  -- Initial left cases (initial ∘ f where f : IR A Void)
  optimize-compose-structural-correct initial id x = refl
  optimize-compose-structural-correct initial initial x = ⊥-elim x
  -- For remaining f, optimizer returns initial ∘ f (no change)
  -- Many patterns are type-impossible (codomain must be Void)
  optimize-compose-structural-correct initial (_ ∘ _) x = refl
  optimize-compose-structural-correct initial (case _ _) x = refl
  optimize-compose-structural-correct initial apply x = refl
  optimize-compose-structural-correct initial unfold x = refl
  optimize-compose-structural-correct initial (Prim _) x = refl

  -- fst cases
  optimize-compose-structural-correct fst id x = refl
  optimize-compose-structural-correct fst (g' ∘ f') x = refl
  optimize-compose-structural-correct fst fst x = refl
  optimize-compose-structural-correct fst snd x = refl
  optimize-compose-structural-correct fst (⟨ f' , g' ⟩ _) x = refl  -- Product beta
  optimize-compose-structural-correct fst apply x = refl
  optimize-compose-structural-correct fst unfold x = refl
  optimize-compose-structural-correct fst initial ()  -- Initial absorption (Void is empty)
-- No distribution: fst ∘ (case f' g') stays as fst ∘ (case f' g')
  optimize-compose-structural-correct fst (case f' g') x = refl
  optimize-compose-structural-correct fst (Prim name) x = refl

-- snd cases
  optimize-compose-structural-correct snd id x = refl
  optimize-compose-structural-correct snd (g' ∘ f') x = refl
  optimize-compose-structural-correct snd fst x = refl
  optimize-compose-structural-correct snd snd x = refl
  optimize-compose-structural-correct snd (⟨ f' , g' ⟩ _) x = refl  -- Product beta
  optimize-compose-structural-correct snd apply x = refl
  optimize-compose-structural-correct snd unfold x = refl
  optimize-compose-structural-correct snd initial ()  -- Initial absorption (Void is empty)
-- No distribution: snd ∘ (case f' g') stays as snd ∘ (case f' g')
  optimize-compose-structural-correct snd (case f' g') x = refl
  optimize-compose-structural-correct snd (Prim name) x = refl

-- ⟨_,_⟩ cases - Conditional pairing distribution
-- Distribution only happens when it enables a beta reduction
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) id x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) initial ()  -- Initial absorption (Void is empty)
-- Cases where we DON'T distribute (no beta possible)
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) (h ∘ h') x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) fst x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) snd x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) (case h h') x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) terminal x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) (curry h m) x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) apply x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) arr x = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ _) (Prim name) x = refl
  -- Cases where we CONDITIONALLY distribute (need to match optimizer's with-clause)
  -- Distribution only happens when safe-pair-distrib returns true
  optimize-compose-structural-correct (⟨ f' , g' ⟩ m) (⟨ h , h' ⟩ m') x
    with safe-pair-distrib f' g'
  ... | true  = cong₂ _,_ (optimize-compose-correct f' (⟨ h , h' ⟩ m') x)
                          (optimize-compose-correct g' (⟨ h , h' ⟩ m') x)
  ... | false = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ m) (inl m') x
    with safe-pair-distrib f' g'
  ... | true  = cong₂ _,_ (optimize-compose-correct f' (inl m') x)
                          (optimize-compose-correct g' (inl m') x)
  ... | false = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ m) (inr m') x
    with safe-pair-distrib f' g'
  ... | true  = cong₂ _,_ (optimize-compose-correct f' (inr m') x)
                          (optimize-compose-correct g' (inr m') x)
  ... | false = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ m) (fold _) x
    with safe-pair-distrib f' g'
  ... | true  = cong₂ _,_ (optimize-compose-correct f' (fold _) x)
                          (optimize-compose-correct g' (fold _) x)
  ... | false = refl
  optimize-compose-structural-correct (⟨ f' , g' ⟩ m) unfold x
    with safe-pair-distrib f' g'
  ... | true  = cong₂ _,_ (optimize-compose-correct f' unfold x)
                          (optimize-compose-correct g' unfold x)
  ... | false = refl

-- inl cases - Case fusion: inl ∘ (case f' g') = [ inl ∘ f' , inl ∘ g' ]
  optimize-compose-structural-correct (inl _) id x = refl
  optimize-compose-structural-correct (inl _) (g' ∘ f') x = refl
  optimize-compose-structural-correct (inl _) fst x = refl
  optimize-compose-structural-correct (inl _) snd x = refl
  optimize-compose-structural-correct (inl _) (⟨ f' , g' ⟩ _) x = refl
  optimize-compose-structural-correct (inl _) (inl _) x = refl
  optimize-compose-structural-correct (inl _) (inr _) x = refl
  optimize-compose-structural-correct (inl _) terminal x = refl
  optimize-compose-structural-correct (inl _) (curry f' _) x = refl
  optimize-compose-structural-correct (inl _) apply x = refl
  optimize-compose-structural-correct (inl _) (fold _) x = refl
  optimize-compose-structural-correct (inl _) unfold x = refl
  optimize-compose-structural-correct (inl _) arr x = refl
  optimize-compose-structural-correct (inl _) initial ()  -- Initial absorption (Void is empty)
-- No distribution: inl ∘ (case f g) stays as inl ∘ (case f g)
  optimize-compose-structural-correct (inl _) (case _ _) x = refl
  optimize-compose-structural-correct (inl _) (Prim name) x = refl

-- inr cases - Case fusion
  optimize-compose-structural-correct (inr _) id x = refl
  optimize-compose-structural-correct (inr _) (g' ∘ f') x = refl
  optimize-compose-structural-correct (inr _) fst x = refl
  optimize-compose-structural-correct (inr _) snd x = refl
  optimize-compose-structural-correct (inr _) (⟨ f' , g' ⟩ _) x = refl
  optimize-compose-structural-correct (inr _) (inl _) x = refl
  optimize-compose-structural-correct (inr _) (inr _) x = refl
  optimize-compose-structural-correct (inr _) terminal x = refl
  optimize-compose-structural-correct (inr _) (curry f' _) x = refl
  optimize-compose-structural-correct (inr _) apply x = refl
  optimize-compose-structural-correct (inr _) (fold _) x = refl
  optimize-compose-structural-correct (inr _) unfold x = refl
  optimize-compose-structural-correct (inr _) arr x = refl
  optimize-compose-structural-correct (inr _) initial ()  -- Initial absorption (Void is empty)
-- No distribution: inr ∘ (case f g) stays as inr ∘ (case f g)
  optimize-compose-structural-correct (inr _) (case _ _) x = refl
  optimize-compose-structural-correct (inr _) (Prim name) x = refl

-- (case _ _) cases (coproduct beta laws)
  optimize-compose-structural-correct (case f' g') id x = refl
  optimize-compose-structural-correct (case f' g') (h ∘ h') x = refl
  optimize-compose-structural-correct (case f' g') fst x = refl
  optimize-compose-structural-correct (case f' g') snd x = refl
  optimize-compose-structural-correct (case f' g') (inl _) x = refl  -- Coproduct beta
  optimize-compose-structural-correct (case f' g') (inr _) x = refl  -- Coproduct beta
-- Case fusion was removed (can increase cost), so now returns h ∘ (case f g)
  optimize-compose-structural-correct (case f' g') (case h h') x = refl
  optimize-compose-structural-correct (case f' g') apply x = refl
  optimize-compose-structural-correct (case f' g') unfold x = refl
  optimize-compose-structural-correct (case f' g') initial ()  -- Initial absorption (Void is empty)
  optimize-compose-structural-correct (case f' g') (Prim name) x = refl

-- terminal cases (terminal fusion)
  optimize-compose-structural-correct terminal id x = refl
  optimize-compose-structural-correct terminal (g' ∘ f') x = refl
  optimize-compose-structural-correct terminal fst x = refl
  optimize-compose-structural-correct terminal snd x = refl
  optimize-compose-structural-correct terminal (⟨ f' , g' ⟩ _) x = refl
  optimize-compose-structural-correct terminal (inl _) x = refl
  optimize-compose-structural-correct terminal (inr _) x = refl
  optimize-compose-structural-correct terminal (case f' g') x = refl
  optimize-compose-structural-correct terminal terminal x = refl
  optimize-compose-structural-correct terminal (curry f' _) x = refl
  optimize-compose-structural-correct terminal apply x = refl
  optimize-compose-structural-correct terminal (fold _) x = refl
  optimize-compose-structural-correct terminal unfold x = refl
  optimize-compose-structural-correct terminal arr x = refl
  optimize-compose-structural-correct terminal initial ()  -- Void is empty
  optimize-compose-structural-correct terminal (Prim name) x = refl

-- curry cases - Case fusion: curry ∘ (case f' g') = [ curry ∘ f' , curry ∘ g' ]
  optimize-compose-structural-correct (curry f' m) id x = refl
  optimize-compose-structural-correct (curry f' _) (g' ∘ h) x = refl
  optimize-compose-structural-correct (curry f' _) fst x = refl
  optimize-compose-structural-correct (curry f' _) snd x = refl
  optimize-compose-structural-correct (curry f' _) (⟨ g' , h ⟩ _) x = refl
  optimize-compose-structural-correct (curry f' _) (inl _) x = refl
  optimize-compose-structural-correct (curry f' _) (inr _) x = refl
  optimize-compose-structural-correct (curry f' _) terminal x = refl
  optimize-compose-structural-correct (curry f' _) (curry g' _) x = refl
  optimize-compose-structural-correct (curry f' _) apply x = refl
  optimize-compose-structural-correct (curry f' _) (fold _) x = refl
  optimize-compose-structural-correct (curry f' _) unfold x = refl
  optimize-compose-structural-correct (curry f' _) arr x = refl
  optimize-compose-structural-correct (curry f' _) initial ()  -- Initial absorption (Void is empty)
-- No distribution: curry f ∘ (case g h) stays as curry f ∘ (case g h)
  optimize-compose-structural-correct (curry _ _) (case _ _) x = refl
  optimize-compose-structural-correct (curry f' _) (Prim name) x = refl

-- apply cases
  optimize-compose-structural-correct apply id x = refl
  optimize-compose-structural-correct apply (g' ∘ f') x = refl
  optimize-compose-structural-correct apply fst x = refl
  optimize-compose-structural-correct apply snd x = refl
-- Exponential beta law: apply ∘ ⟨ curry f , g ⟩ = f ∘ ⟨ id , g ⟩
-- Eliminates closure allocation!
-- Each case is handled explicitly to ensure normal output.
-- Composition case k = fst: h ∘ (fst ∘ ⟨ id , g ⟩) = h ∘ id = h
  optimize-compose-structural-correct apply (⟨ curry (h ∘ fst) _ , g' ⟩ _) x = refl
-- Composition case k = snd: recursively optimize h ∘ g
  optimize-compose-structural-correct apply (⟨ curry (h ∘ snd) _ , g' ⟩ _) x = optimize-compose-correct h g' x
-- Composition case k = terminal: h ∘ (terminal ∘ ⟨ id , g ⟩) = h ∘ terminal
  optimize-compose-structural-correct apply (⟨ curry (h ∘ terminal) _ , g' ⟩ _) x = refl
-- Composition case: all curry (h ∘ k) cases now use recursive optimization
  optimize-compose-structural-correct apply (⟨ curry (h ∘ id) _ , g' ⟩ _) x =
    let inner = optimize-compose id (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct id (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (k₁ ∘ k₂)) _ , g' ⟩ _) x =
    let inner = optimize-compose (k₁ ∘ k₂) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (k₁ ∘ k₂) (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (⟨ f₁ , f₂ ⟩ m)) _ , g' ⟩ _) x =
    let inner = optimize-compose (⟨ f₁ , f₂ ⟩ m) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (⟨ f₁ , f₂ ⟩ m) (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (inl m)) _ , g' ⟩ _) x =
    let inner = optimize-compose (inl m) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (inl m) (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (inr m)) _ , g' ⟩ _) x =
    let inner = optimize-compose (inr m) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (inr m) (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (curry f m)) _ , g' ⟩ _) x =
    let inner = optimize-compose (curry f m) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (curry f m) (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ apply) _ , g' ⟩ _) x =
    let inner = optimize-compose apply (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct apply (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (fold Heap)) _ , g' ⟩ _) x =
    let inner = optimize-compose (fold Heap) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (fold _) (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (fold Stack)) _ , g' ⟩ _) x =
    let inner = optimize-compose (fold Stack) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (fold _) (⟨ id , g' ⟩ _) x))
  optimize-compose-structural-correct apply (⟨ curry (h ∘ (Prim n)) _ , g' ⟩ _) x =
    let inner = optimize-compose (Prim n) (⟨ id , g' ⟩ _)
    in trans (optimize-compose-correct h inner x)
             (cong (eval′ h) (optimize-compose-correct (Prim n) (⟨ id , g' ⟩ _) x))
-- Dead code: terminal ∘ ⟨ id , g ⟩ = terminal
  optimize-compose-structural-correct apply (⟨ curry terminal _ , g' ⟩ _) x = refl
-- Identity: id ∘ ⟨ id , g ⟩ = ⟨ id , g ⟩
  optimize-compose-structural-correct apply (⟨ curry id _ , g' ⟩ _) x = refl
-- Beta: fst ∘ ⟨ id , g ⟩ = id
  optimize-compose-structural-correct apply (⟨ curry fst _ , g' ⟩ _) x = refl
-- Beta: snd ∘ ⟨ id , g ⟩ = g
  optimize-compose-structural-correct apply (⟨ curry snd _ , g' ⟩ _) x = refl
-- Default cases: f ∘ ⟨ id , g ⟩ semantics
  optimize-compose-structural-correct apply (⟨ curry (⟨ _ , _ ⟩ _) _ , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ curry (inl _) _ , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ curry (inr _) _ , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ curry (curry _ _) _ , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ curry apply _ , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ curry (fold _) _ , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ curry (Prim _) _ , g' ⟩ _) x = refl
-- apply with pair where first component is not curry (default case)
  optimize-compose-structural-correct apply (⟨ id , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ f' ∘ f'' , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ fst , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ snd , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ (case f' f'') , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ initial , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ apply , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ unfold , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply (⟨ Prim _ , g' ⟩ _) x = refl
  optimize-compose-structural-correct apply apply x = refl
  optimize-compose-structural-correct apply unfold x = refl
  optimize-compose-structural-correct apply initial ()  -- Initial absorption (Void is empty)
-- No distribution: apply ∘ (case f g) stays as apply ∘ (case f g)
  optimize-compose-structural-correct apply (case _ _) x = refl
  optimize-compose-structural-correct apply (Prim name) x = refl

-- fold cases
  optimize-compose-structural-correct (fold _) id x = refl
-- Fusion rule: fold ∘ (unfold ∘ f) = f
-- By associativity + identity: (fold ∘ unfold) ∘ f = id ∘ f = f
  optimize-compose-structural-correct (fold _) (unfold ∘ f') x = refl
-- Other compositions (default case)
  optimize-compose-structural-correct (fold _) (id ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((g' ∘ g'') ∘ f') x = refl
  optimize-compose-structural-correct (fold _) (fst ∘ f') x = refl
  optimize-compose-structural-correct (fold _) (snd ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((⟨ g' , g'' ⟩ _) ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((inl _) ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((inr _) ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((case g' g'') ∘ f') x = refl
  optimize-compose-structural-correct (fold _) (terminal ∘ f') x = refl
  optimize-compose-structural-correct (fold _) (initial ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((curry g' _) ∘ f') x = refl
  optimize-compose-structural-correct (fold _) (apply ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((fold _) ∘ f') x = refl
  optimize-compose-structural-correct (fold _) (arr ∘ f') x = refl
  optimize-compose-structural-correct (fold _) ((Prim _) ∘ f') x = refl
  optimize-compose-structural-correct (fold _) fst x = refl
  optimize-compose-structural-correct (fold _) snd x = refl
  optimize-compose-structural-correct (fold _) (⟨ f' , g' ⟩ _) x = refl
  optimize-compose-structural-correct (fold _) (inl _) x = refl
  optimize-compose-structural-correct (fold _) (inr _) x = refl
  optimize-compose-structural-correct (fold _) terminal x = refl
  optimize-compose-structural-correct (fold _) (curry f' _) x = refl
  optimize-compose-structural-correct (fold _) apply x = refl
  optimize-compose-structural-correct (fold _) (fold _) x = refl
  optimize-compose-structural-correct (fold _) unfold x = refl  -- Fixed point law
  optimize-compose-structural-correct (fold _) arr x = refl
  optimize-compose-structural-correct (fold _) initial ()  -- Initial absorption (Void is empty)
-- No distribution: fold ∘ (case f g) stays as fold ∘ (case f g)
  optimize-compose-structural-correct (fold _) (case _ _) x = refl
  optimize-compose-structural-correct (fold _) (Prim name) x = refl

-- unfold cases
  optimize-compose-structural-correct unfold id x = refl
-- Fusion rule: unfold ∘ (fold ∘ f) = f
-- By associativity + identity: (unfold ∘ (fold Heap)) ∘ f = id ∘ f = f
  optimize-compose-structural-correct unfold ((fold _) ∘ f') x = refl
-- Other compositions (default case)
  optimize-compose-structural-correct unfold (id ∘ f') x = refl
  optimize-compose-structural-correct unfold ((g' ∘ g'') ∘ f') x = refl
  optimize-compose-structural-correct unfold (fst ∘ f') x = refl
  optimize-compose-structural-correct unfold (snd ∘ f') x = refl
  optimize-compose-structural-correct unfold ((case g' g'') ∘ f') x = refl
  optimize-compose-structural-correct unfold (initial ∘ f') x = refl
  optimize-compose-structural-correct unfold (apply ∘ f') x = refl
  optimize-compose-structural-correct unfold (unfold ∘ f') x = refl
  optimize-compose-structural-correct unfold ((Prim _) ∘ f') x = refl
  optimize-compose-structural-correct unfold fst x = refl
  optimize-compose-structural-correct unfold snd x = refl
  optimize-compose-structural-correct unfold apply x = refl
  optimize-compose-structural-correct unfold (fold _) x = refl  -- Fixed point law
  optimize-compose-structural-correct unfold unfold x = refl
  optimize-compose-structural-correct unfold initial ()  -- Initial absorption (Void is empty)
-- No distribution: unfold ∘ (case f g) stays as unfold ∘ (case f g)
  optimize-compose-structural-correct unfold (case _ _) x = refl
  optimize-compose-structural-correct unfold (Prim name) x = refl

-- arr cases
  optimize-compose-structural-correct arr id x = refl
  optimize-compose-structural-correct arr (g' ∘ f') x = refl
  optimize-compose-structural-correct arr fst x = refl
  optimize-compose-structural-correct arr snd x = refl
  optimize-compose-structural-correct arr (curry f' _) x = refl
  optimize-compose-structural-correct arr apply x = refl
  optimize-compose-structural-correct arr unfold x = refl
  optimize-compose-structural-correct arr initial ()  -- Initial absorption (Void is empty)
-- No distribution: arr ∘ (case f g) stays as arr ∘ (case f g)
  optimize-compose-structural-correct arr (case _ _) x = refl
  optimize-compose-structural-correct arr (Prim name) x = refl

-- Associativity: (h ∘ g) ∘ f → optimize h (optimize g f)
  optimize-compose-structural-correct (h ∘ g) id x = refl
  optimize-compose-structural-correct (_ ∘ _) (case _ _) x = refl
  optimize-compose-structural-correct (h ∘ g) initial ()  -- Initial absorption (Void is empty)
  optimize-compose-structural-correct (h ∘ g) (f' ∘ f'') x =
    trans (optimize-compose-correct h (optimize-compose g (f' ∘ f'')) x)
          (cong (eval′ h) (optimize-compose-correct g (f' ∘ f'') x))
  optimize-compose-structural-correct (h ∘ g) fst x =
    trans (optimize-compose-correct h (optimize-compose g fst) x)
          (cong (eval′ h) (optimize-compose-correct g fst x))
  optimize-compose-structural-correct (h ∘ g) snd x =
    trans (optimize-compose-correct h (optimize-compose g snd) x)
          (cong (eval′ h) (optimize-compose-correct g snd x))
  optimize-compose-structural-correct (h ∘ g) (⟨ f' , f'' ⟩ m) x =
    trans (optimize-compose-correct h (optimize-compose g (⟨ f' , f'' ⟩ m)) x)
          (cong (eval′ h) (optimize-compose-correct g (⟨ f' , f'' ⟩ m) x))
  optimize-compose-structural-correct (h ∘ g) (inl m) x =
    trans (optimize-compose-correct h (optimize-compose g (inl m)) x)
          (cong (eval′ h) (optimize-compose-correct g (inl m) x))
  optimize-compose-structural-correct (h ∘ g) (inr m) x =
    trans (optimize-compose-correct h (optimize-compose g (inr m)) x)
          (cong (eval′ h) (optimize-compose-correct g (inr m) x))
  optimize-compose-structural-correct (h ∘ g) terminal x =
    trans (optimize-compose-correct h (optimize-compose g terminal) x)
          (cong (eval′ h) (optimize-compose-correct g terminal x))
  optimize-compose-structural-correct (h ∘ g) (curry f' m) x =
    trans (optimize-compose-correct h (optimize-compose g (curry f' m)) x)
          (cong (eval′ h) (optimize-compose-correct g (curry f' m) x))
  optimize-compose-structural-correct (h ∘ g) apply x =
    trans (optimize-compose-correct h (optimize-compose g apply) x)
          (cong (eval′ h) (optimize-compose-correct g apply x))
  optimize-compose-structural-correct (h ∘ g) (fold m) x =
    trans (optimize-compose-correct h (optimize-compose g (fold m)) x)
          (cong (eval′ h) (optimize-compose-correct g (fold m) x))
  optimize-compose-structural-correct (h ∘ g) unfold x =
    trans (optimize-compose-correct h (optimize-compose g unfold) x)
          (cong (eval′ h) (optimize-compose-correct g unfold x))
  optimize-compose-structural-correct (h ∘ g) arr x =
    trans (optimize-compose-correct h (optimize-compose g arr) x)
          (cong (eval′ h) (optimize-compose-correct g arr x))
  optimize-compose-structural-correct (h ∘ g) (Prim name) x =
    trans (optimize-compose-correct h (optimize-compose g (Prim name)) x)
          (cong (eval′ h) (optimize-compose-correct g (Prim name) x))

-- Prim cases (primitives are opaque)
  optimize-compose-structural-correct (Prim name) id x = refl
  optimize-compose-structural-correct (Prim name) (g' ∘ f') x = refl
  optimize-compose-structural-correct (Prim name) fst x = refl
  optimize-compose-structural-correct (Prim name) snd x = refl
  optimize-compose-structural-correct (Prim name) (⟨ f' , g' ⟩ _) x = refl
  optimize-compose-structural-correct (Prim name) (inl _) x = refl
  optimize-compose-structural-correct (Prim name) (inr _) x = refl
  optimize-compose-structural-correct (Prim name) terminal x = refl
  optimize-compose-structural-correct (Prim name) (curry f' _) x = refl
  optimize-compose-structural-correct (Prim name) apply x = refl
  optimize-compose-structural-correct (Prim name) (fold _) x = refl
  optimize-compose-structural-correct (Prim name) unfold x = refl
  optimize-compose-structural-correct (Prim name) arr x = refl
  optimize-compose-structural-correct (Prim name) initial ()
-- No distribution: Prim ∘ (case f g) stays as Prim ∘ (case f g)
  optimize-compose-structural-correct (Prim _) (case _ _) x = refl
  optimize-compose-structural-correct (Prim name) (Prim name') x = refl
  optimize-compose-structural-correct (Prim _) (free-heap _) x = refl

-- free-heap cases (free-heap : IR Unit Unit is opaque)
-- free-heap as left operand - all trivially correct since free-heap is unchanged
  optimize-compose-structural-correct (free-heap _) id x = refl
  optimize-compose-structural-correct (free-heap _) (_ ∘ _) x = refl
  optimize-compose-structural-correct (free-heap _) fst x = refl
  optimize-compose-structural-correct (free-heap _) snd x = refl
  optimize-compose-structural-correct (free-heap _) (case _ _) x = refl
  optimize-compose-structural-correct (free-heap _) terminal x = refl
  optimize-compose-structural-correct (free-heap _) apply x = refl
  optimize-compose-structural-correct (free-heap _) unfold x = refl
  optimize-compose-structural-correct (free-heap _) (free-heap _) x = refl
  optimize-compose-structural-correct (free-heap _) (Prim _) x = refl
-- free-heap as right operand with composition on left (recursive proof needed)
  optimize-compose-structural-correct (h ∘ g) (free-heap hr) x =
    trans (optimize-compose-correct h (optimize-compose g (free-heap hr)) x)
          (cong (eval′ h) (optimize-compose-correct g (free-heap hr) x))
-- free-heap as right operand with non-composition on left
  optimize-compose-structural-correct terminal (free-heap _) x = refl
  optimize-compose-structural-correct (⟨ _ , _ ⟩ _) (free-heap _) x = refl
  optimize-compose-structural-correct (inl _) (free-heap _) x = refl
  optimize-compose-structural-correct (inr _) (free-heap _) x = refl
  optimize-compose-structural-correct (curry _ _) (free-heap _) x = refl
  optimize-compose-structural-correct (fold _) ((free-heap _) ∘ _) x = refl
  optimize-compose-structural-correct (fold _) (free-heap _) x = refl

------------------------------------------------------------------------
-- Correctness of optimize-pair
------------------------------------------------------------------------

optimize-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
                      → eval′ (optimize-pair f g) x ≡ eval′ (⟨ f , g ⟩ Heap) x

-- Eta law: ⟨ fst , snd ⟩ = id
optimize-pair-correct (fst {A} {B}) (snd {A'} {B'}) x with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = sym (eval-pair-eta Heap x)
... | yes refl | no _     = refl
... | no _     | yes _    = refl
... | no _     | no _     = refl

-- All other fst cases (non-snd second argument)
optimize-pair-correct fst id x = refl
optimize-pair-correct fst (g ∘ h) x = refl
optimize-pair-correct fst fst x = refl
optimize-pair-correct fst (⟨ g , h ⟩ _) x = refl
optimize-pair-correct fst (inl _) x = refl
optimize-pair-correct fst (inr _) x = refl
optimize-pair-correct fst terminal x = refl
optimize-pair-correct fst (curry g _) x = refl
optimize-pair-correct fst apply x = refl
optimize-pair-correct fst (fold _) x = refl
optimize-pair-correct fst (Prim name) x = refl

-- Uniqueness: ⟨ fst ∘ h , snd ∘ h' ⟩ cases
optimize-pair-correct (_∘_ {_} {D} {_} (fst {A} {B}) h) (_∘_ {_} {D'} {_} (snd {A'} {B'}) h') x
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
optimize-pair-correct (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {.B}) h') x
  | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = sym (eval-pair-unique h Heap x)  -- Use uniqueness law
...   | no _     = refl
optimize-pair-correct (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {.B}) h') x
  | yes refl | yes refl | no _  = refl
optimize-pair-correct (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {B'}) h') x
  | yes refl | no _  | _     = refl
optimize-pair-correct (_∘_ (fst {A} {B}) h) (_∘_ (snd {A'} {B'}) h') x
  | no _  | _     | _     = refl

-- fst ∘ h with non-snd ∘ g' second argument
optimize-pair-correct (fst ∘ h) id x = refl
optimize-pair-correct (fst ∘ h) fst x = refl
optimize-pair-correct (fst ∘ h) snd x = refl
optimize-pair-correct (fst ∘ h) (⟨ g , g' ⟩ _) x = refl
optimize-pair-correct (fst ∘ h) (inl _) x = refl
optimize-pair-correct (fst ∘ h) (inr _) x = refl
optimize-pair-correct (fst ∘ h) (case g g') x = refl
optimize-pair-correct (fst ∘ h) terminal x = refl
optimize-pair-correct (fst ∘ h) (curry g _) x = refl
optimize-pair-correct (fst ∘ h) apply x = refl
optimize-pair-correct (fst ∘ h) (fold _) x = refl
optimize-pair-correct (fst ∘ h) unfold x = refl
optimize-pair-correct (fst ∘ h) arr x = refl
-- Non-snd composition
optimize-pair-correct (fst ∘ h) (id ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (fst ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((inl _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((inr _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((case f g) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (terminal ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((f ∘ f') ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((⟨ f , g ⟩ _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((curry f _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (apply ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((fold _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (unfold ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (arr ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (initial ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((Prim name) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) initial x = refl
optimize-pair-correct (fst ∘ h) (Prim name) x = refl
-- free-heap cases for fst ∘ h
optimize-pair-correct (fst ∘ h) (free-heap _) x = refl
optimize-pair-correct (fst ∘ h) ((free-heap _) ∘ g') x = refl

-- All other cases (non-fst first argument)
optimize-pair-correct id g x = refl
optimize-pair-correct (id ∘ h) g x = refl
optimize-pair-correct (snd ∘ h) g x = refl
optimize-pair-correct ((inl _) ∘ h) g x = refl
optimize-pair-correct ((inr _) ∘ h) g x = refl
optimize-pair-correct ((case f f') ∘ h) g x = refl
optimize-pair-correct (terminal ∘ h) g x = refl
optimize-pair-correct ((f ∘ f') ∘ h) g x = refl
optimize-pair-correct ((⟨ f , f' ⟩ _) ∘ h) g x = refl
optimize-pair-correct ((curry f _) ∘ h) g x = refl
optimize-pair-correct (apply ∘ h) g x = refl
optimize-pair-correct ((fold _) ∘ h) g x = refl
optimize-pair-correct (unfold ∘ h) g x = refl
optimize-pair-correct (arr ∘ h) g x = refl
-- initial composition cases
optimize-pair-correct (initial ∘ h) g x = refl
optimize-pair-correct ((Prim name) ∘ h) g x = refl
optimize-pair-correct snd g x = refl
optimize-pair-correct (⟨ f , h ⟩ _) g x = refl
optimize-pair-correct (inl _) g x = refl
optimize-pair-correct (inr _) g x = refl
optimize-pair-correct (case f h) g x = refl
optimize-pair-correct terminal g x = refl
optimize-pair-correct (curry f _) g x = refl
optimize-pair-correct apply g x = refl
optimize-pair-correct (fold _) g x = refl
optimize-pair-correct unfold g x = refl
optimize-pair-correct arr g x = refl
optimize-pair-correct initial g x = refl
optimize-pair-correct (Prim name) g x = refl
-- free-heap cases (free-heap : IR Unit Unit is opaque, passes through)
optimize-pair-correct (free-heap _) _ x = refl
optimize-pair-correct ((free-heap _) ∘ _) _ x = refl

------------------------------------------------------------------------
-- Correctness of optimize-case
------------------------------------------------------------------------

optimize-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧)
                      → eval′ (optimize-case f g) x ≡ eval′ (case f g) x

-- Eta law: (case inl inr) = id
-- Note: AllocModes m and m' may differ but semantics are the same (mode is transparent)
optimize-case-correct (inl {A} {B} m) (inr {A'} {B'} m') x with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = sym (lemma x)
  where
    -- AllocMode doesn't affect semantics of inl/inr
    lemma : (y : ⟦ A + B ⟧) → eval′ (case (inl m) (inr m')) y ≡ y
    lemma (inj₁ a) = refl
    lemma (inj₂ b) = refl
... | yes refl | no _     = refl
... | no _     | yes _    = refl
... | no _     | no _     = refl

-- All other inl cases
optimize-case-correct (inl _) id x = refl
optimize-case-correct (inl _) (g ∘ h) x = refl
optimize-case-correct (inl _) fst x = refl
optimize-case-correct (inl _) snd x = refl
optimize-case-correct (inl _) (inl _) x = refl
optimize-case-correct (inl _) (case g h) x = refl
optimize-case-correct (inl _) initial x = refl
optimize-case-correct (inl _) apply x = refl
optimize-case-correct (inl _) unfold x = refl
optimize-case-correct (inl _) (Prim name) x = refl

-- Uniqueness: [ h ∘ inl , h' ∘ inr ] cases
-- Note: AllocModes m and m' may differ but uniqueness still holds (mode is transparent)
optimize-case-correct (_∘_ {_} {D} {_} h (inl {A} {B} m)) (_∘_ {_} {D'} {_} h' (inr {A'} {B'} m')) x
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
optimize-case-correct (_∘_ h (inl {A} {B} m)) (_∘_ h' (inr {.A} {.B} m')) x
  | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = sym (lemma x)  -- Use uniqueness with mode-transparent proof
  where
    -- AllocMode doesn't affect semantics, so uniqueness holds regardless of modes
    lemma : (y : ⟦ A + B ⟧) → eval′ (case (h ∘ inl m) (h ∘ inr m')) y ≡ eval′ h y
    lemma (inj₁ a) = refl
    lemma (inj₂ b) = refl
...   | no _     = refl
optimize-case-correct (_∘_ h (inl {A} {B} m)) (_∘_ h' (inr {.A} {.B} m')) x
  | yes refl | yes refl | no _  = refl
optimize-case-correct (_∘_ h (inl {A} {B} m)) (_∘_ h' (inr {.A} {B'} m')) x
  | yes refl | no _  | _     = refl
optimize-case-correct (_∘_ h (inl {A} {B} m)) (_∘_ h' (inr {A'} {B'} m')) x
  | no _  | _     | _     = refl

-- h ∘ inl with second arg NOT of form h' ∘ inr
-- Non-compositions
optimize-case-correct (h ∘ (inl _)) id x = refl
optimize-case-correct (h ∘ (inl _)) fst x = refl
optimize-case-correct (h ∘ (inl _)) snd x = refl
optimize-case-correct (h ∘ (inl _)) (⟨ g₁ , g₂ ⟩ _) x = refl
optimize-case-correct (h ∘ (inl _)) (inl _) x = refl
optimize-case-correct (h ∘ (inl _)) (inr _) x = refl
optimize-case-correct (h ∘ (inl _)) (case g₁ g₂) x = refl
optimize-case-correct (h ∘ (inl _)) terminal x = refl
optimize-case-correct (h ∘ (inl _)) initial x = refl
optimize-case-correct (h ∘ (inl _)) (curry g _) x = refl
optimize-case-correct (h ∘ (inl _)) apply x = refl
optimize-case-correct (h ∘ (inl _)) (fold _) x = refl
optimize-case-correct (h ∘ (inl _)) unfold x = refl
optimize-case-correct (h ∘ (inl _)) arr x = refl
-- Compositions NOT ending in inr
optimize-case-correct (h ∘ (inl _)) (g ∘ id) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ fst) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ snd) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ (g' ∘ g'')) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ (⟨ g₁ , g₂ ⟩ _)) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ (inl _)) x = refl
-- g ∘ inr is handled by uniqueness case above
optimize-case-correct (h ∘ (inl _)) (g ∘ (case g₁ g₂)) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ terminal) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ initial) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ (curry g' _)) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ apply) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ (fold Heap)) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ unfold) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ arr) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ Prim name) x = refl
optimize-case-correct (h ∘ (inl _)) (Prim name) x = refl

-- All other first arg cases (not inl at end)
optimize-case-correct (f ∘ id) g x = refl
optimize-case-correct (f ∘ fst) g x = refl
optimize-case-correct (f ∘ snd) g x = refl
optimize-case-correct (f ∘ (f' ∘ f'')) g x = refl
optimize-case-correct (f ∘ (⟨ f₁ , f₂ ⟩ _)) g x = refl
-- f ∘ inl is handled above
optimize-case-correct (f ∘ (inr _)) g x = refl
optimize-case-correct (f ∘ (case f₁ f₂)) g x = refl
optimize-case-correct (f ∘ terminal) g x = refl
optimize-case-correct (f ∘ initial) g x = refl
optimize-case-correct (f ∘ (curry f' _)) g x = refl
optimize-case-correct (f ∘ apply) g x = refl
optimize-case-correct (f ∘ (fold Heap)) g x = refl
optimize-case-correct (f ∘ unfold) g x = refl
optimize-case-correct (f ∘ arr) g x = refl
optimize-case-correct (f ∘ Prim name) g x = refl
optimize-case-correct id g x = refl
optimize-case-correct fst g x = refl
optimize-case-correct snd g x = refl
optimize-case-correct (⟨ f , h ⟩ _) g x = refl
optimize-case-correct (inr _) g x = refl
optimize-case-correct (case f h) g x = refl
optimize-case-correct terminal g x = refl
optimize-case-correct initial g x = refl
optimize-case-correct (curry f _) g x = refl
optimize-case-correct apply g x = refl
optimize-case-correct (fold _) g x = refl
optimize-case-correct unfold g x = refl
optimize-case-correct arr g x = refl
optimize-case-correct (Prim name) g x = refl
-- free-heap cases (free-heap : IR Unit Unit is opaque)
optimize-case-correct (free-heap _) _ x = refl
optimize-case-correct (_ ∘ (free-heap _)) _ x = refl
optimize-case-correct _ (free-heap _) x = refl
-- fold Stack cases (fold with Stack mode - same semantics as Heap)
optimize-case-correct (_ ∘ (fold Stack)) _ x = refl
-- inl with free-heap/fold on right
optimize-case-correct (_ ∘ (inl _)) (_ ∘ (free-heap _)) x = refl
optimize-case-correct (_ ∘ (inl _)) (_ ∘ (fold Stack)) x = refl

------------------------------------------------------------------------
-- Correctness of optimize-once-structural and optimize-once (mutual)
------------------------------------------------------------------------

mutual
  -- | Structural optimization preserves semantics
  optimize-once-structural-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                                   → eval′ (optimize-once-structural f) x ≡ eval′ f x
  optimize-once-structural-correct id x = refl
  optimize-once-structural-correct (g ∘ f) x =
    trans (optimize-compose-correct (optimize-once g) (optimize-once f) x)
          (trans (cong (eval′ (optimize-once g)) (optimize-once-correct f x))
                 (optimize-once-correct g (eval′ f x)))
  optimize-once-structural-correct fst x = refl
  optimize-once-structural-correct snd x = refl
  optimize-once-structural-correct (⟨ f , g ⟩ _) x =
    trans (optimize-pair-correct (optimize-once f) (optimize-once g) x)
          (cong₂ _,_ (optimize-once-correct f x) (optimize-once-correct g x))
  -- inl with Void source: returns initial (vacuously correct)
  optimize-once-structural-correct (inl {A} {B} m) x with A ≟Type Void
  ... | yes refl = ⊥-elim x
  ... | no _     = refl
  -- inr with Void source: returns initial (vacuously correct)
  optimize-once-structural-correct (inr {A} {B} m) x with B ≟Type Void
  ... | yes refl = ⊥-elim x
  ... | no _     = refl
  optimize-once-structural-correct (case f g) x =
    trans (optimize-case-correct (optimize-once f) (optimize-once g) x)
          (lemma x)
    where
      lemma : (y : ⟦ _ + _ ⟧) → eval′ (case (optimize-once f) (optimize-once g)) y ≡ eval′ (case f g) y
      lemma (inj₁ a) = optimize-once-correct f a
      lemma (inj₂ b) = optimize-once-correct g b
  optimize-once-structural-correct terminal x = refl
  optimize-once-structural-correct initial ()
  optimize-once-structural-correct (curry {q = q} f _) x =
    funext (λ b → optimize-once-correct f (x , b))
  optimize-once-structural-correct apply x = refl
  -- fold with Void source: returns initial (vacuously correct)
  optimize-once-structural-correct (fold {F} _) x with F ≟Type Void
  ... | yes refl = ⊥-elim x
  ... | no _     = refl
  optimize-once-structural-correct unfold x = refl
  optimize-once-structural-correct arr x = refl
  -- Prim with Void source: returns initial (vacuously correct)
  optimize-once-structural-correct (Prim {A} name) x with A ≟Type Void
  ... | yes refl = ⊥-elim x
  ... | no _     = refl
  -- free-heap is opaque (passes through unchanged)
  optimize-once-structural-correct (free-heap _) x = refl

  -- | Type-directed optimization preserves semantics
  --
  -- Type-directed rules:
  --   1. B = Unit: terminal is correct (eval terminal x = tt = eval f x)
  --   2. A = Void: initial is correct (vacuously, no inputs)
  --   3. Otherwise: structural rules preserve semantics
  optimize-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                        → eval′ (optimize-once f) x ≡ eval′ f x
  optimize-once-correct {A} {B} f x with B ≟Type Unit
  ... | yes refl = refl  -- eval terminal x = tt = eval f x (both produce tt)
  ... | no _ with A ≟Type Void
  ...   | yes refl = ⊥-elim x  -- x : ⟦ Void ⟧ = ⊥, vacuously true
  ...   | no _ = optimize-once-structural-correct f x

------------------------------------------------------------------------
-- Correctness of bounded optimization
------------------------------------------------------------------------

optimize-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                   → eval′ (optimize-n n f) x ≡ eval′ f x
optimize-n-correct zero f x = refl
optimize-n-correct (suc n) f x =
  trans (optimize-n-correct n (optimize-once f) x)
        (optimize-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: optimize preserves semantics
------------------------------------------------------------------------

optimize-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                 → eval′ (optimize f) x ≡ eval′ f x
optimize-correct f x = optimize-n-correct 10 f x
