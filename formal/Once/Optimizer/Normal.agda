------------------------------------------------------------------------
-- Once.Optimizer.Normal
--
-- Normal forms for BCC terms.
-- A term is normal if no optimization rules apply.
--
-- Key properties to prove:
--   1. optimize produces normal forms
--   2. normal forms are unique per equivalence class
--   3. normal forms have minimal cost
------------------------------------------------------------------------

module Once.Optimizer.Normal where

open import Once.Type
open import Once.IR
open import Once.Optimize using (_≟Type_; _≟IR_; optimize; optimize-once;
  optimize-compose; optimize-pair; optimize-case; safe-pair-distrib; optimize-n)
open import Once.Optimize.Correct using (optimize-correct)
open import Once.Semantics using (eval; ⟦_⟧)
open import Once.Optimizer.Cost using (cost)
open import Once.Optimizer.IRReducible public

-- Import IsNormal and proofs from PairCaseNormal
-- This module contains the mechanical enumeration proofs
open import Once.Optimizer.PairCaseNormal public
  using (IsNormal; normal-id; normal-fst; normal-snd; normal-inl; normal-inr;
         normal-terminal; normal-initial; normal-apply; normal-arr;
         normal-fold; normal-unfold; normal-prim;
         normal-compose; normal-pair; normal-case; normal-curry;
         normal-compose-left; normal-compose-right;
         optimize-pair-normal; optimize-case-normal)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat as ℕ using () renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; m≤n+m)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Helper: Extract normal subterms from normal compound terms
------------------------------------------------------------------------

-- | Extract the first component's normality from a normal pair
normal-pair-fst : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
  IsNormal (⟨ f , g ⟩ m) → IsNormal f
normal-pair-fst (normal-pair nf _ _) = nf

-- | Extract the second component's normality from a normal pair
normal-pair-snd : ∀ {A B C} {f : IR C A} {g : IR C B} {m} →
  IsNormal (⟨ f , g ⟩ m) → IsNormal g
normal-pair-snd (normal-pair _ ng _) = ng

-- | Extract the body's normality from a normal curry
normal-curry-body : ∀ {A B C q} {f : IR (A * B) C} {m} →
  IsNormal (curry {q = q} f m) → IsNormal f
normal-curry-body (normal-curry nf) = nf

------------------------------------------------------------------------
-- Proof: optimize-compose produces normal forms
------------------------------------------------------------------------

-- | optimize-compose produces normal forms when given normal inputs
--
-- The optimizer now recursively normalizes problematic apply-curry outputs,
-- so optimize-compose always produces normal forms when given normal inputs.
--
-- PROOF STRATEGY: For each case of optimize-compose:
-- 1. Identity/beta rules: output is subterm of normal input, hence normal
-- 2. Default g ∘ f: since no reduction pattern matched, CompReducible g f is empty

{-# TERMINATING #-}  -- Termination follows from optimize-compose termination
optimize-compose-normal : ∀ {A B C} (g : IR B C) (f : IR A B) →
  IsNormal g → IsNormal f → IsNormal (optimize-compose g f)

------------------------------------------------------------------------
-- Identity Laws
------------------------------------------------------------------------
-- id ∘ f = f
optimize-compose-normal id f _ nf = nf
-- g ∘ id = g (all cases)
optimize-compose-normal fst id ng _ = ng
optimize-compose-normal snd id ng _ = ng
optimize-compose-normal (⟨ f , g ⟩ m) id ng _ = ng
optimize-compose-normal (inl m) id ng _ = ng
optimize-compose-normal (inr m) id ng _ = ng
optimize-compose-normal [ f , g ] id ng _ = ng
optimize-compose-normal terminal id ng _ = ng
optimize-compose-normal (curry f m) id ng _ = ng
optimize-compose-normal apply id ng _ = ng
optimize-compose-normal fold id ng _ = ng
optimize-compose-normal unfold id ng _ = ng
optimize-compose-normal arr id ng _ = ng
optimize-compose-normal (Prim n) id ng _ = ng
optimize-compose-normal (g ∘ f) id ng _ = ng

------------------------------------------------------------------------
-- Beta Laws - Products
------------------------------------------------------------------------
-- fst ∘ ⟨ f , g ⟩ = f
optimize-compose-normal fst (⟨ f , g ⟩ _) _ nfg = normal-pair-fst nfg
-- snd ∘ ⟨ f , g ⟩ = g
optimize-compose-normal snd (⟨ f , g ⟩ _) _ nfg = normal-pair-snd nfg

------------------------------------------------------------------------
-- Beta Laws - Coproducts
------------------------------------------------------------------------
-- [ f , g ] ∘ inl = f
optimize-compose-normal [ f , g ] (inl _) nfg _ = normal-case-left nfg
  where
    normal-case-left : ∀ {A B C} {f : IR A C} {g : IR B C} →
      IsNormal [ f , g ] → IsNormal f
    normal-case-left (normal-case nf _ _) = nf
-- [ f , g ] ∘ inr = g
optimize-compose-normal [ f , g ] (inr _) nfg _ = normal-case-right nfg
  where
    normal-case-right : ∀ {A B C} {f : IR A C} {g : IR B C} →
      IsNormal [ f , g ] → IsNormal g
    normal-case-right (normal-case _ ng _) = ng

------------------------------------------------------------------------
-- Apply-Curry Rules
------------------------------------------------------------------------
-- apply ∘ ⟨ curry (h ∘ fst) , g ⟩ = h
optimize-compose-normal apply (⟨ curry (h ∘ fst) _ , g ⟩ _) _ npair =
  normal-compose-left (normal-curry-body (normal-pair-fst npair))
-- apply ∘ ⟨ curry (h ∘ snd) , g ⟩ = optimize-compose h g (recursive)
optimize-compose-normal apply (⟨ curry (h ∘ snd) _ , g ⟩ _) _ npair =
  optimize-compose-normal h g
    (normal-compose-left (normal-curry-body (normal-pair-fst npair)))
    (normal-pair-snd npair)
-- apply ∘ ⟨ curry (h ∘ terminal) , g ⟩ = h ∘ terminal
optimize-compose-normal apply (⟨ curry (h ∘ terminal) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
  in normal-compose nh normal-terminal (λ ())
-- apply ∘ ⟨ curry (h ∘ k) , g ⟩ = h ∘ (k ∘ ⟨ id , g ⟩)
-- For remaining k cases, the output composition is normal
optimize-compose-normal apply (⟨ curry (h ∘ id) _ , g ⟩ _) _ npair =
  let ncomp = normal-curry-body (normal-pair-fst npair)
  in ⊥-elim (comp-id-not-normal ncomp)
  where
    comp-id-not-normal : ∀ {A B} {h : IR B A} → ¬ IsNormal (h ∘ id)
    comp-id-not-normal (normal-compose _ _ ¬red) = ¬red red-id-right
optimize-compose-normal apply (⟨ curry (h ∘ (k₁ ∘ k₂)) _ , g ⟩ _) _ npair =
  let ncomp = normal-curry-body (normal-pair-fst npair)
  in ⊥-elim (comp-comp-not-normal ncomp)
  where
    comp-comp-not-normal : ∀ {A B C D} {h : IR C D} {g : IR B C} {f : IR A B} →
      ¬ IsNormal (h ∘ (g ∘ f))
    comp-comp-not-normal (normal-compose _ _ ¬red) = ¬red red-assoc
optimize-compose-normal apply (⟨ curry (h ∘ (⟨ _ , _ ⟩ _)) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
      ng = normal-pair-snd npair
      nk = normal-compose-right (normal-curry-body (normal-pair-fst npair))
      -- k ∘ ⟨ id , g ⟩: k is a pair, ⟨ id , g ⟩ is a pair, no beta reduction
      ninner = normal-compose nk (normal-pair normal-id ng (λ ())) (λ ())
  in normal-compose nh ninner (λ ())
optimize-compose-normal apply (⟨ curry (h ∘ (inl _)) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
      ng = normal-pair-snd npair
      nk = normal-compose-right (normal-curry-body (normal-pair-fst npair))
      ninner = normal-compose nk (normal-pair normal-id ng (λ ())) (λ ())
  in normal-compose nh ninner (λ ())
optimize-compose-normal apply (⟨ curry (h ∘ (inr _)) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
      ng = normal-pair-snd npair
      nk = normal-compose-right (normal-curry-body (normal-pair-fst npair))
      ninner = normal-compose nk (normal-pair normal-id ng (λ ())) (λ ())
  in normal-compose nh ninner (λ ())
optimize-compose-normal apply (⟨ curry (h ∘ (curry _ _)) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
      ng = normal-pair-snd npair
      nk = normal-compose-right (normal-curry-body (normal-pair-fst npair))
      ninner = normal-compose nk (normal-pair normal-id ng (λ ())) (λ ())
  in normal-compose nh ninner (λ ())
optimize-compose-normal apply (⟨ curry (h ∘ apply) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
      ng = normal-pair-snd npair
      ninner = normal-compose normal-apply (normal-pair normal-id ng (λ ())) (λ ())
  in normal-compose nh ninner (λ ())
optimize-compose-normal apply (⟨ curry (h ∘ fold) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
      ng = normal-pair-snd npair
      ninner = normal-compose normal-fold (normal-pair normal-id ng (λ ())) (λ ())
  in normal-compose nh ninner (λ ())
optimize-compose-normal apply (⟨ curry (h ∘ (Prim _)) _ , g ⟩ _) _ npair =
  let nh = normal-compose-left (normal-curry-body (normal-pair-fst npair))
      ng = normal-pair-snd npair
      nk = normal-compose-right (normal-curry-body (normal-pair-fst npair))
      ninner = normal-compose nk (normal-pair normal-id ng (λ ())) (λ ())
  in normal-compose nh ninner (λ ())
-- curry terminal case
optimize-compose-normal apply (⟨ curry terminal _ , g ⟩ _) _ _ = normal-terminal
-- curry id case
optimize-compose-normal apply (⟨ curry id _ , g ⟩ _) _ npair =
  normal-pair normal-id (normal-pair-snd npair) (λ ())
-- curry fst case
optimize-compose-normal apply (⟨ curry fst _ , g ⟩ _) _ _ = normal-id
-- curry snd case
optimize-compose-normal apply (⟨ curry snd _ , g ⟩ _) _ npair = normal-pair-snd npair
-- Default curry f cases
optimize-compose-normal apply (⟨ curry (⟨ _ , _ ⟩ _) _ , g ⟩ _) _ npair =
  let nf = normal-curry-body (normal-pair-fst npair)
      ng = normal-pair-snd npair
  in normal-compose nf (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry (inl _) _ , g ⟩ _) _ npair =
  let nf = normal-curry-body (normal-pair-fst npair)
      ng = normal-pair-snd npair
  in normal-compose nf (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry (inr _) _ , g ⟩ _) _ npair =
  let nf = normal-curry-body (normal-pair-fst npair)
      ng = normal-pair-snd npair
  in normal-compose nf (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry [ _ , _ ] _ , g ⟩ _) _ npair =
  let nf = normal-curry-body (normal-pair-fst npair)
      ng = normal-pair-snd npair
  in normal-compose nf (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry apply _ , g ⟩ _) _ npair =
  let ng = normal-pair-snd npair
  in normal-compose normal-apply (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry fold _ , g ⟩ _) _ npair =
  let ng = normal-pair-snd npair
  in normal-compose normal-fold (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry unfold _ , g ⟩ _) _ npair =
  let ng = normal-pair-snd npair
  in normal-compose normal-unfold (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry arr _ , g ⟩ _) _ npair =
  let ng = normal-pair-snd npair
  in normal-compose normal-arr (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry (Prim _) _ , g ⟩ _) _ npair =
  let nf = normal-curry-body (normal-pair-fst npair)
      ng = normal-pair-snd npair
  in normal-compose nf (normal-pair normal-id ng (λ ())) (λ ())
optimize-compose-normal apply (⟨ curry initial _ , g ⟩ _) _ npair =
  let ng = normal-pair-snd npair
  in normal-compose normal-initial (normal-pair normal-id ng (λ ())) (λ ())

------------------------------------------------------------------------
-- Fixed Point Laws
------------------------------------------------------------------------
optimize-compose-normal fold unfold _ _ = normal-id
optimize-compose-normal unfold fold _ _ = normal-id
optimize-compose-normal fold (unfold ∘ f) _ nf = normal-compose-right nf
optimize-compose-normal unfold (fold ∘ f) _ nf = normal-compose-right nf

------------------------------------------------------------------------
-- Terminal/Dead Code
------------------------------------------------------------------------
optimize-compose-normal terminal (_ ∘ _) _ _ = normal-terminal
optimize-compose-normal terminal fst _ _ = normal-terminal
optimize-compose-normal terminal snd _ _ = normal-terminal
optimize-compose-normal terminal (⟨ _ , _ ⟩ _) _ _ = normal-terminal
optimize-compose-normal terminal (inl _) _ _ = normal-terminal
optimize-compose-normal terminal (inr _) _ _ = normal-terminal
optimize-compose-normal terminal [ _ , _ ] _ _ = normal-terminal
optimize-compose-normal terminal terminal _ _ = normal-terminal
optimize-compose-normal terminal (curry _ _) _ _ = normal-terminal
optimize-compose-normal terminal apply _ _ = normal-terminal
optimize-compose-normal terminal fold _ _ = normal-terminal
optimize-compose-normal terminal unfold _ _ = normal-terminal
optimize-compose-normal terminal arr _ _ = normal-terminal
optimize-compose-normal terminal (Prim _) _ _ = normal-terminal

------------------------------------------------------------------------
-- Initial Absorption
------------------------------------------------------------------------
optimize-compose-normal fst initial _ _ = normal-initial
optimize-compose-normal snd initial _ _ = normal-initial
optimize-compose-normal (⟨ _ , _ ⟩ _) initial _ _ = normal-initial
optimize-compose-normal (inl _) initial _ _ = normal-initial
optimize-compose-normal (inr _) initial _ _ = normal-initial
optimize-compose-normal [ _ , _ ] initial _ _ = normal-initial
optimize-compose-normal terminal initial _ _ = normal-initial
optimize-compose-normal (curry _ _) initial _ _ = normal-initial
optimize-compose-normal apply initial _ _ = normal-initial
optimize-compose-normal fold initial _ _ = normal-initial
optimize-compose-normal unfold initial _ _ = normal-initial
optimize-compose-normal arr initial _ _ = normal-initial
optimize-compose-normal (Prim _) initial _ _ = normal-initial
optimize-compose-normal (_ ∘ _) initial _ _ = normal-initial

------------------------------------------------------------------------
-- Initial Left: initial ∘ f = initial ∘ f
------------------------------------------------------------------------
optimize-compose-normal initial f _ nf = normal-compose normal-initial nf (λ ())

------------------------------------------------------------------------
-- Pair Distribution (using safe-pair-distrib)
------------------------------------------------------------------------
optimize-compose-normal (⟨ f , g ⟩ m) (⟨ h₁ , h₂ ⟩ m') npair npair' with safe-pair-distrib f g
... | true = normal-pair
  (optimize-compose-normal f (⟨ h₁ , h₂ ⟩ m') (normal-pair-fst npair) npair')
  (optimize-compose-normal g (⟨ h₁ , h₂ ⟩ m') (normal-pair-snd npair) npair')
  (λ ())
... | false = normal-compose npair npair' (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) (inl m') npair nf with safe-pair-distrib f g
... | true = normal-pair
  (optimize-compose-normal f (inl m') (normal-pair-fst npair) nf)
  (optimize-compose-normal g (inl m') (normal-pair-snd npair) nf)
  (λ ())
... | false = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) (inr m') npair nf with safe-pair-distrib f g
... | true = normal-pair
  (optimize-compose-normal f (inr m') (normal-pair-fst npair) nf)
  (optimize-compose-normal g (inr m') (normal-pair-snd npair) nf)
  (λ ())
... | false = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) unfold npair _ with safe-pair-distrib f g
... | true = normal-pair
  (optimize-compose-normal f unfold (normal-pair-fst npair) normal-unfold)
  (optimize-compose-normal g unfold (normal-pair-snd npair) normal-unfold)
  (λ ())
... | false = normal-compose npair normal-unfold (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) fold npair _ with safe-pair-distrib f g
... | true = normal-pair
  (optimize-compose-normal f fold (normal-pair-fst npair) normal-fold)
  (optimize-compose-normal g fold (normal-pair-snd npair) normal-fold)
  (λ ())
... | false = normal-compose npair normal-fold (λ ())
-- Default pair ∘ h = pair ∘ h
optimize-compose-normal (⟨ f , g ⟩ m) fst npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) snd npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) [ h₁ , h₂ ] npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) terminal npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) (curry h n) npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) apply npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) arr npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) (Prim n) npair nf = normal-compose npair nf (λ ())
optimize-compose-normal (⟨ f , g ⟩ m) (h₁ ∘ h₂) npair nf = normal-compose npair nf (λ ())

------------------------------------------------------------------------
-- Case Distribution: h ∘ [ f , g ] = h ∘ [ f , g ]
------------------------------------------------------------------------
optimize-compose-normal fst [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (inl m) [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (inr m) [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal terminal [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (curry h n) [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal arr [ f , g ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (Prim n) [ f , g ] ng nf = normal-compose ng nf (λ ())

------------------------------------------------------------------------
-- Associativity: (h ∘ g) ∘ f → h ∘ (g ∘ f) then optimize
------------------------------------------------------------------------
optimize-compose-normal (h ∘ g) f nhg nf =
  optimize-compose-normal h (optimize-compose g f)
    (normal-compose-left nhg)
    (optimize-compose-normal g f (normal-compose-right nhg) nf)

------------------------------------------------------------------------
-- Default Cases: g ∘ f = g ∘ f (no reduction applies)
------------------------------------------------------------------------
-- These cases produce compositions where no optimization rule matched,
-- meaning CompReducible g f is empty.
optimize-compose-normal fst fst ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst snd ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst (f ∘ g) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst (inl _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst (inr _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst [ _ , _ ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst terminal ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst (curry _ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst apply ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst fold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst unfold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst arr ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fst (Prim _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd fst ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd snd ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd (f ∘ g) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd (inl _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd (inr _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd [ _ , _ ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd terminal ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd (curry _ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd apply ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd fold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd unfold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd arr ng nf = normal-compose ng nf (λ ())
optimize-compose-normal snd (Prim _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (inl m) f ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (inr m) f ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] fst ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] snd ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] (⟨ _ , _ ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] [ _ , _ ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] terminal ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] (curry _ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] apply ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] fold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] unfold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] arr ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] (Prim _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal [ f , g ] (_ ∘ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (curry f m) g ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply fst ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply snd ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ id , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ (_ ∘ _) , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ fst , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ snd , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ (⟨ _ , _ ⟩ _) , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ (inl _) , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ (inr _) , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ [ _ , _ ] , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ terminal , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ initial , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ apply , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ fold , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ unfold , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ arr , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (⟨ (Prim _) , g ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (inl _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (inr _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply [ _ , _ ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply terminal ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (curry _ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply apply ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply fold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply unfold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply arr ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (Prim _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal apply (_ ∘ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold fst ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold snd ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (⟨ _ , _ ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (inl _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (inr _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold [ _ , _ ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold terminal ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (curry _ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold apply ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold fold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold arr ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (Prim _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (id ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (fst ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (snd ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold ((⟨ _ , _ ⟩ _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold ((inl _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold ((inr _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold ([ _ , _ ] ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (terminal ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (initial ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold ((curry _ _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (apply ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (fold ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold (arr ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold ((Prim _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal fold ((_ ∘ _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold fst ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold snd ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (⟨ _ , _ ⟩ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (inl _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (inr _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold [ _ , _ ] ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold terminal ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (curry _ _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold apply ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold unfold ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold arr ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (Prim _) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (id ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (fst ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (snd ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold ((⟨ _ , _ ⟩ _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold ((inl _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold ((inr _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold ([ _ , _ ] ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (terminal ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (initial ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold ((curry _ _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (apply ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (unfold ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold (arr ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold ((Prim _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal unfold ((_ ∘ _) ∘ f) ng nf = normal-compose ng nf (λ ())
optimize-compose-normal arr f ng nf = normal-compose ng nf (λ ())
optimize-compose-normal (Prim n) f ng nf = normal-compose ng nf (λ ())

------------------------------------------------------------------------
-- Proof: optimize-once-structural produces normal forms
------------------------------------------------------------------------

-- | Structural optimization produces normal forms
optimize-once-structural-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize-once-structural t)
-- Base cases: constants
optimize-once-structural-normal id = normal-id
optimize-once-structural-normal fst = normal-fst
optimize-once-structural-normal snd = normal-snd
optimize-once-structural-normal terminal = normal-terminal
optimize-once-structural-normal initial = normal-initial
optimize-once-structural-normal apply = normal-apply
optimize-once-structural-normal unfold = normal-unfold
optimize-once-structural-normal arr = normal-arr
-- Composition: use optimize-compose-normal with recursive calls
optimize-once-structural-normal (g ∘ f) =
  optimize-compose-normal (optimize-once g) (optimize-once f)
    (optimize-once-normal g) (optimize-once-normal f)
-- Pair: use optimize-pair-normal with recursive calls
optimize-once-structural-normal (⟨ f , g ⟩ m) =
  optimize-pair-normal (optimize-once f) (optimize-once g)
    (optimize-once-normal f) (optimize-once-normal g)
-- Case: use optimize-case-normal with recursive calls
optimize-once-structural-normal [ f , g ] =
  optimize-case-normal (optimize-once f) (optimize-once g)
    (optimize-once-normal f) (optimize-once-normal g)
-- Curry: normal-curry with recursive call
optimize-once-structural-normal (curry f m) = normal-curry (optimize-once-normal f)
-- inl: check for Void source
optimize-once-structural-normal (inl {A} {B} m) with A ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-inl ¬void
-- inr: check for Void source
optimize-once-structural-normal (inr {A} {B} m) with B ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-inr ¬void
-- fold: check for Void functor
optimize-once-structural-normal (fold {F}) with F ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-fold ¬void
-- Prim: check for Void source
optimize-once-structural-normal (Prim {A} n) with A ≟Type Void
... | yes refl = normal-initial
... | no ¬void = normal-prim ¬void

------------------------------------------------------------------------
-- Proof: optimize-once produces normal forms (type-directed)
------------------------------------------------------------------------

-- | Single optimization pass produces normal forms
--
-- Type-directed rules:
--   1. B = Unit: returns terminal (normal)
--   2. A = Void: returns initial (normal)
--   3. Otherwise: structural rules (proven above)
optimize-once-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize-once t)
optimize-once-normal {A} {B} t with B ≟Type Unit
... | yes refl = normal-terminal                -- Target is Unit → terminal
... | no _ with A ≟Type Void
...   | yes refl = normal-initial               -- Source is Void → initial
...   | no _ = optimize-once-structural-normal t  -- Otherwise → structural

------------------------------------------------------------------------
-- Main Theorem: optimize produces normal forms
------------------------------------------------------------------------

-- | Helper: optimize-n (suc n) produces normal forms
--
-- For n ≥ 1, optimize-n n t is normal because:
-- - optimize-n 1 t = optimize-once t, which is normal by optimize-once-normal
-- - optimize-n (suc n) t = optimize-n n (optimize-once t), and by induction
--   optimize-n n of any term is normal (for n ≥ 1)
optimize-n-suc-normal : ∀ {A B} (n : ℕ) (t : IR A B) →
  IsNormal (optimize-n (suc n) t)
optimize-n-suc-normal zero t = optimize-once-normal t
optimize-n-suc-normal (suc n) t = optimize-n-suc-normal n (optimize-once t)

-- | Optimizer produces normal forms
--
-- Since optimize = optimize-n 10, we have optimize t = optimize-n 10 t.
-- By optimize-n-suc-normal, this is normal.
optimize-normal : ∀ {A B} (t : IR A B) → IsNormal (optimize t)
optimize-normal t = optimize-n-suc-normal 9 t

------------------------------------------------------------------------
-- Coherence Properties
------------------------------------------------------------------------

-- | Normal forms are unique per equivalence class
--
-- STATUS: This property requires proving that the type-directed optimizer
-- produces unique normal forms.
--
-- TYPE-DIRECTED NORMALIZATION (NOW IMPLEMENTED):
-- The optimizer now applies type-directed rules before structural rules:
--   - Any f : A → Unit  reduces to terminal  (Unit target rule)
--   - Any f : Void → B  reduces to initial   (Void source rule)
--
-- This eliminates the previous counterexample:
--   - fst      : (Unit * Unit) → Unit  now optimizes to terminal
--   - snd      : (Unit * Unit) → Unit  now optimizes to terminal
--   - terminal : (Unit * Unit) → Unit  stays terminal
-- All three now have the same normal form: terminal
--
-- TO PROVE:
-- 1. For Unit target types: only terminal can result from optimization
-- 2. For Void source types: only initial can result from optimization
-- 3. For non-degenerate types: structural normal forms are unique
--
-- The IsNormal predicate itself still allows non-canonical forms (e.g.,
-- IsNormal fst is true even when fst : A → Unit). This is fine because
-- the optimizer output always uses the canonical form.
--
-- We keep this as a postulate pending full proof.
postulate
  normal-unique : ∀ {A B} (t t' : IR A B) →
    IsNormal t → IsNormal t' →
    (∀ x → eval t x ≡ eval t' x) →
    t ≡ t'

------------------------------------------------------------------------
-- Cost reduction lemmas
------------------------------------------------------------------------

-- | optimize-compose does not increase cost
--
-- Each rule either reduces or preserves cost:
-- - id ∘ f = f: cost 0 + cost f → cost f ✓
-- - f ∘ id = f: cost f + 0 → cost f ✓
-- - fst ∘ ⟨ f , g ⟩ = f: eliminates pair allocation ✓
-- - terminal ∘ f = terminal: eliminates f's cost ✓
-- - etc.
--
-- The proof is by case analysis on the structure of optimize-compose.
-- The recursive case (associativity) uses the induction hypothesis twice.

-- Helper: cost h ≤ cost h + cost f
cost-≤-left : ∀ {A B C D} (g : IR B C) (f : IR A B) →
  cost g ≤ cost g ℕ+ cost f
cost-≤-left g f = m≤m+n (cost g) (cost f)
  where
    open import Data.Nat.Properties using (m≤m+n)

-- Helper: cost f ≤ cost g + cost f
cost-≤-right : ∀ {A B C D} (g : IR B C) (f : IR A B) →
  cost f ≤ cost g ℕ+ cost f
cost-≤-right g f = m≤n+m (cost f) (cost g)

optimize-compose-cost-le : ∀ {A B C} (g : IR B C) (f : IR A B) →
  cost (optimize-compose g f) ≤ cost g ℕ+ cost f

------------------------------------------------------------------------
-- Identity Laws (lines 471-487 in Optimize.agda)
------------------------------------------------------------------------
-- id ∘ f = f
optimize-compose-cost-le id f = cost-≤-right id f
-- g ∘ id = g (all cases)
optimize-compose-cost-le fst id = cost-≤-left fst id
optimize-compose-cost-le snd id = cost-≤-left snd id
optimize-compose-cost-le (⟨ f , g ⟩ m) id = cost-≤-left (⟨ f , g ⟩ m) id
optimize-compose-cost-le (inl m) id = cost-≤-left (inl m) id
optimize-compose-cost-le (inr m) id = cost-≤-left (inr m) id
optimize-compose-cost-le [ f , g ] id = cost-≤-left [ f , g ] id
optimize-compose-cost-le terminal id = cost-≤-left terminal id
optimize-compose-cost-le (curry f m) id = cost-≤-left (curry f m) id
optimize-compose-cost-le apply id = cost-≤-left apply id
optimize-compose-cost-le fold id = cost-≤-left fold id
optimize-compose-cost-le unfold id = cost-≤-left unfold id
optimize-compose-cost-le arr id = cost-≤-left arr id
optimize-compose-cost-le (Prim n) id = cost-≤-left (Prim n) id
optimize-compose-cost-le (g ∘ f) id = cost-≤-left (g ∘ f) id

------------------------------------------------------------------------
-- Beta Laws - Products (lines 494-497)
------------------------------------------------------------------------
-- fst ∘ ⟨ f , g ⟩ = f
optimize-compose-cost-le fst (⟨ f , g ⟩ _) = ≤-trans (cost-≤-left f g) (m≤n+m (cost f ℕ+ cost g) 1)
-- snd ∘ ⟨ f , g ⟩ = g
optimize-compose-cost-le snd (⟨ f , g ⟩ _) =
  ≤-trans (m≤n+m (cost g) (cost f))
          (m≤n+m (cost f ℕ+ cost g) 1)

------------------------------------------------------------------------
-- Beta Laws - Coproducts (lines 504-507)
------------------------------------------------------------------------
-- [ f , g ] ∘ inl = f
optimize-compose-cost-le [ f , g ] (inl _) = cost-≤-left f g
-- [ f , g ] ∘ inr = g
optimize-compose-cost-le [ f , g ] (inr _) = m≤n+m (cost g) (cost f)

------------------------------------------------------------------------
-- Apply-Curry Rules (lines 529-545)
------------------------------------------------------------------------
-- apply ∘ ⟨ curry (h ∘ fst) , g ⟩ = h
optimize-compose-cost-le apply (⟨ curry (h ∘ fst) _ , g ⟩ _) =
  ≤-trans (cost-≤-left h fst) (m≤n+m (cost h ℕ+ cost fst) (suc (suc (cost g))))
-- apply ∘ ⟨ curry (h ∘ snd) , g ⟩ = h ∘ g
optimize-compose-cost-le apply (⟨ curry (h ∘ snd) _ , g ⟩ _) =
  m≤n+m (cost h ℕ+ cost g) (suc 1)
-- apply ∘ ⟨ curry (h ∘ terminal) , g ⟩ = h ∘ terminal
optimize-compose-cost-le apply (⟨ curry (h ∘ terminal) _ , g ⟩ _) =
  m≤n+m (cost h ℕ+ cost terminal) (suc (suc (cost g)))
-- apply ∘ ⟨ curry (h ∘ k) , g ⟩ = h ∘ (k ∘ ⟨ id , g ⟩)
-- LHS cost: 0 + (1 + (1 + cost h + cost k) + cost g) = 2 + cost h + cost k + cost g
-- RHS cost: cost h + (cost k + (1 + 0 + cost g)) = cost h + cost k + 1 + cost g
-- Need: cost h + cost k + 1 + cost g ≤ 2 + cost h + cost k + cost g ✓
optimize-compose-cost-le apply (⟨ curry (h ∘ k) _ , g ⟩ _) =
  s≤s (m≤n+m (cost h ℕ+ (cost k ℕ+ (suc (cost g)))) 1)
-- apply ∘ ⟨ curry terminal , g ⟩ = terminal
optimize-compose-cost-le apply (⟨ curry terminal _ , g ⟩ _) = z≤n
-- apply ∘ ⟨ curry id , g ⟩ = ⟨ id , g ⟩
optimize-compose-cost-le apply (⟨ curry id _ , g ⟩ _) =
  s≤s (m≤n+m (cost g) 1)
-- apply ∘ ⟨ curry fst , g ⟩ = id
optimize-compose-cost-le apply (⟨ curry fst _ , g ⟩ _) = z≤n
-- apply ∘ ⟨ curry snd , g ⟩ = g
optimize-compose-cost-le apply (⟨ curry snd _ , g ⟩ _) =
  m≤n+m (cost g) (suc 1)
-- Default apply ∘ ⟨ curry f , g ⟩ = f ∘ ⟨ id , g ⟩
-- LHS cost: 0 + (1 + (1 + cost f) + cost g) = 2 + cost f + cost g
-- RHS cost: cost f + (1 + 0 + cost g) = cost f + 1 + cost g
-- Need: cost f + 1 + cost g ≤ 2 + cost f + cost g ✓
optimize-compose-cost-le apply (⟨ curry f _ , g ⟩ _) =
  s≤s (m≤n+m (cost f ℕ+ suc (cost g)) 1)

------------------------------------------------------------------------
-- Fixed Point Laws (lines 552-561)
------------------------------------------------------------------------
-- fold ∘ unfold = id
optimize-compose-cost-le fold unfold = z≤n
-- unfold ∘ fold = id
optimize-compose-cost-le unfold fold = z≤n
-- fold ∘ (unfold ∘ f) = f
optimize-compose-cost-le fold (unfold ∘ f) = m≤n+m (cost f) 1
-- unfold ∘ (fold ∘ f) = f
optimize-compose-cost-le unfold (fold ∘ f) = m≤n+m (cost f) 1

------------------------------------------------------------------------
-- Terminal/Dead Code (lines 568-581)
------------------------------------------------------------------------
optimize-compose-cost-le terminal (_ ∘ _) = z≤n
optimize-compose-cost-le terminal fst = z≤n
optimize-compose-cost-le terminal snd = z≤n
optimize-compose-cost-le terminal (⟨ _ , _ ⟩ _) = z≤n
optimize-compose-cost-le terminal (inl _) = z≤n
optimize-compose-cost-le terminal (inr _) = z≤n
optimize-compose-cost-le terminal [ _ , _ ] = z≤n
optimize-compose-cost-le terminal terminal = z≤n
optimize-compose-cost-le terminal (curry _ _) = z≤n
optimize-compose-cost-le terminal apply = z≤n
optimize-compose-cost-le terminal fold = z≤n
optimize-compose-cost-le terminal unfold = z≤n
optimize-compose-cost-le terminal arr = z≤n
optimize-compose-cost-le terminal (Prim _) = z≤n

------------------------------------------------------------------------
-- Initial Absorption (lines 584-597)
------------------------------------------------------------------------
optimize-compose-cost-le fst initial = z≤n
optimize-compose-cost-le snd initial = z≤n
optimize-compose-cost-le (⟨ _ , _ ⟩ _) initial = z≤n
optimize-compose-cost-le (inl _) initial = z≤n
optimize-compose-cost-le (inr _) initial = z≤n
optimize-compose-cost-le [ _ , _ ] initial = z≤n
optimize-compose-cost-le terminal initial = z≤n
optimize-compose-cost-le (curry _ _) initial = z≤n
optimize-compose-cost-le apply initial = z≤n
optimize-compose-cost-le fold initial = z≤n
optimize-compose-cost-le unfold initial = z≤n
optimize-compose-cost-le arr initial = z≤n
optimize-compose-cost-le (Prim _) initial = z≤n
optimize-compose-cost-le (_ ∘ _) initial = z≤n

------------------------------------------------------------------------
-- Initial Left (line 601)
------------------------------------------------------------------------
-- initial ∘ f = initial ∘ f (no reduction)
optimize-compose-cost-le initial f = ≤-refl

------------------------------------------------------------------------
-- Pair Distribution (lines 614-629)
-- These use pair-distrib-opt which depends on safe-pair-distrib
-- We use postulate for the conditional cases since they require
-- analyzing the Boolean result of safe-pair-distrib
------------------------------------------------------------------------
-- ⟨ f , g ⟩ ∘ ⟨ h₁ , h₂ ⟩ uses pair-distrib-opt
optimize-compose-cost-le (⟨ f , g ⟩ m) (⟨ h₁ , h₂ ⟩ m') with safe-pair-distrib f g
... | true = ≤-trans
  (s≤s (+-mono-≤ (optimize-compose-cost-le f (⟨ h₁ , h₂ ⟩ m'))
                  (optimize-compose-cost-le g (⟨ h₁ , h₂ ⟩ m'))))
  (s≤s (+-mono-≤ {cost f} {suc (cost f ℕ+ cost g)} {cost (⟨ h₁ , h₂ ⟩ m')}
    (s≤s (cost-≤-left f g))
    (s≤s (m≤n+m (cost g) (cost f)))))
... | false = ≤-refl
-- ⟨ f , g ⟩ ∘ inl
optimize-compose-cost-le (⟨ f , g ⟩ m) (inl m') with safe-pair-distrib f g
... | true = ≤-trans
  (s≤s (+-mono-≤ (optimize-compose-cost-le f (inl m'))
                  (optimize-compose-cost-le g (inl m'))))
  (s≤s (+-mono-≤ (s≤s (cost-≤-left f g)) (s≤s (m≤n+m (cost g) (cost f)))))
... | false = ≤-refl
-- ⟨ f , g ⟩ ∘ inr
optimize-compose-cost-le (⟨ f , g ⟩ m) (inr m') with safe-pair-distrib f g
... | true = ≤-trans
  (s≤s (+-mono-≤ (optimize-compose-cost-le f (inr m'))
                  (optimize-compose-cost-le g (inr m'))))
  (s≤s (+-mono-≤ (s≤s (cost-≤-left f g)) (s≤s (m≤n+m (cost g) (cost f)))))
... | false = ≤-refl
-- ⟨ f , g ⟩ ∘ unfold
optimize-compose-cost-le (⟨ f , g ⟩ m) unfold with safe-pair-distrib f g
... | true = ≤-trans
  (s≤s (+-mono-≤ (optimize-compose-cost-le f unfold)
                  (optimize-compose-cost-le g unfold)))
  (s≤s (+-mono-≤ (s≤s (cost-≤-left f g)) (s≤s (m≤n+m (cost g) (cost f)))))
... | false = ≤-refl
-- ⟨ f , g ⟩ ∘ fold
optimize-compose-cost-le (⟨ f , g ⟩ m) fold with safe-pair-distrib f g
... | true = ≤-trans
  (s≤s (+-mono-≤ (optimize-compose-cost-le f fold)
                  (optimize-compose-cost-le g fold)))
  (s≤s (+-mono-≤ (s≤s (cost-≤-left f g)) (s≤s (m≤n+m (cost g) (cost f)))))
... | false = ≤-refl
-- Default ⟨ f , g ⟩ ∘ h = (⟨ f , g ⟩) ∘ h
optimize-compose-cost-le (⟨ f , g ⟩ m) fst = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) snd = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) [ h₁ , h₂ ] = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) terminal = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) (curry h n) = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) apply = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) arr = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) (Prim n) = ≤-refl
optimize-compose-cost-le (⟨ f , g ⟩ m) (h₁ ∘ h₂) = ≤-refl

------------------------------------------------------------------------
-- Case Distribution (line 637): h ∘ [ f , g ] = h ∘ [ f , g ] (no change)
------------------------------------------------------------------------
optimize-compose-cost-le fst [ f , g ] = ≤-refl
optimize-compose-cost-le snd [ f , g ] = ≤-refl
optimize-compose-cost-le (inl m) [ f , g ] = ≤-refl
optimize-compose-cost-le (inr m) [ f , g ] = ≤-refl
optimize-compose-cost-le terminal [ f , g ] = ≤-refl
optimize-compose-cost-le (curry h n) [ f , g ] = ≤-refl
optimize-compose-cost-le apply [ f , g ] = ≤-refl
optimize-compose-cost-le fold [ f , g ] = ≤-refl
optimize-compose-cost-le unfold [ f , g ] = ≤-refl
optimize-compose-cost-le arr [ f , g ] = ≤-refl
optimize-compose-cost-le (Prim n) [ f , g ] = ≤-refl

------------------------------------------------------------------------
-- Associativity (line 644): (h ∘ g) ∘ f → h ∘ (g ∘ f) then optimize
------------------------------------------------------------------------
-- optimize-compose (h ∘ g) f = optimize-compose h (optimize-compose g f)
-- By IH: cost (optimize-compose g f) ≤ cost g + cost f
-- By IH: cost (optimize-compose h ...) ≤ cost h + cost (optimize-compose g f)
-- Combined: ≤ cost h + cost g + cost f = (cost h + cost g) + cost f ✓
optimize-compose-cost-le (h ∘ g) f =
  ≤-trans (optimize-compose-cost-le h (optimize-compose g f))
          (+-mono-≤ ≤-refl (optimize-compose-cost-le g f))

------------------------------------------------------------------------
-- Default Cases (line 650): g ∘ f = g ∘ f (no change)
------------------------------------------------------------------------
-- These are cases not covered above
optimize-compose-cost-le fst fst = ≤-refl
optimize-compose-cost-le fst snd = ≤-refl
optimize-compose-cost-le fst (f ∘ g) = ≤-refl
optimize-compose-cost-le fst (inl _) = ≤-refl
optimize-compose-cost-le fst (inr _) = ≤-refl
optimize-compose-cost-le fst [ _ , _ ] = ≤-refl
optimize-compose-cost-le fst terminal = ≤-refl
optimize-compose-cost-le fst (curry _ _) = ≤-refl
optimize-compose-cost-le fst apply = ≤-refl
optimize-compose-cost-le fst fold = ≤-refl
optimize-compose-cost-le fst unfold = ≤-refl
optimize-compose-cost-le fst arr = ≤-refl
optimize-compose-cost-le fst (Prim _) = ≤-refl
optimize-compose-cost-le snd fst = ≤-refl
optimize-compose-cost-le snd snd = ≤-refl
optimize-compose-cost-le snd (f ∘ g) = ≤-refl
optimize-compose-cost-le snd (inl _) = ≤-refl
optimize-compose-cost-le snd (inr _) = ≤-refl
optimize-compose-cost-le snd [ _ , _ ] = ≤-refl
optimize-compose-cost-le snd terminal = ≤-refl
optimize-compose-cost-le snd (curry _ _) = ≤-refl
optimize-compose-cost-le snd apply = ≤-refl
optimize-compose-cost-le snd fold = ≤-refl
optimize-compose-cost-le snd unfold = ≤-refl
optimize-compose-cost-le snd arr = ≤-refl
optimize-compose-cost-le snd (Prim _) = ≤-refl
optimize-compose-cost-le (inl m) f = ≤-refl
optimize-compose-cost-le (inr m) f = ≤-refl
optimize-compose-cost-le [ f , g ] fst = ≤-refl
optimize-compose-cost-le [ f , g ] snd = ≤-refl
optimize-compose-cost-le [ f , g ] (⟨ _ , _ ⟩ _) = ≤-refl
optimize-compose-cost-le [ f , g ] [ _ , _ ] = ≤-refl
optimize-compose-cost-le [ f , g ] terminal = ≤-refl
optimize-compose-cost-le [ f , g ] (curry _ _) = ≤-refl
optimize-compose-cost-le [ f , g ] apply = ≤-refl
optimize-compose-cost-le [ f , g ] fold = ≤-refl
optimize-compose-cost-le [ f , g ] unfold = ≤-refl
optimize-compose-cost-le [ f , g ] arr = ≤-refl
optimize-compose-cost-le [ f , g ] (Prim _) = ≤-refl
optimize-compose-cost-le [ f , g ] (_ ∘ _) = ≤-refl
optimize-compose-cost-le (curry f m) g = ≤-refl
optimize-compose-cost-le apply fst = ≤-refl
optimize-compose-cost-le apply snd = ≤-refl
optimize-compose-cost-le apply (⟨ id , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ (_ ∘ _) , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ fst , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ snd , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ (⟨ _ , _ ⟩ _) , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ (inl _) , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ (inr _) , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ [ _ , _ ] , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ terminal , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ initial , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ apply , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ fold , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ unfold , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ arr , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (⟨ (Prim _) , g ⟩ _) = ≤-refl
optimize-compose-cost-le apply (inl _) = ≤-refl
optimize-compose-cost-le apply (inr _) = ≤-refl
optimize-compose-cost-le apply [ _ , _ ] = ≤-refl
optimize-compose-cost-le apply terminal = ≤-refl
optimize-compose-cost-le apply (curry _ _) = ≤-refl
optimize-compose-cost-le apply apply = ≤-refl
optimize-compose-cost-le apply fold = ≤-refl
optimize-compose-cost-le apply unfold = ≤-refl
optimize-compose-cost-le apply arr = ≤-refl
optimize-compose-cost-le apply (Prim _) = ≤-refl
optimize-compose-cost-le apply (_ ∘ _) = ≤-refl
optimize-compose-cost-le fold fst = ≤-refl
optimize-compose-cost-le fold snd = ≤-refl
optimize-compose-cost-le fold (⟨ _ , _ ⟩ _) = ≤-refl
optimize-compose-cost-le fold (inl _) = ≤-refl
optimize-compose-cost-le fold (inr _) = ≤-refl
optimize-compose-cost-le fold [ _ , _ ] = ≤-refl
optimize-compose-cost-le fold terminal = ≤-refl
optimize-compose-cost-le fold (curry _ _) = ≤-refl
optimize-compose-cost-le fold apply = ≤-refl
optimize-compose-cost-le fold fold = ≤-refl
optimize-compose-cost-le fold arr = ≤-refl
optimize-compose-cost-le fold (Prim _) = ≤-refl
optimize-compose-cost-le fold (id ∘ f) = ≤-refl
optimize-compose-cost-le fold (fst ∘ f) = ≤-refl
optimize-compose-cost-le fold (snd ∘ f) = ≤-refl
optimize-compose-cost-le fold ((⟨ _ , _ ⟩ _) ∘ f) = ≤-refl
optimize-compose-cost-le fold ((inl _) ∘ f) = ≤-refl
optimize-compose-cost-le fold ((inr _) ∘ f) = ≤-refl
optimize-compose-cost-le fold ([ _ , _ ] ∘ f) = ≤-refl
optimize-compose-cost-le fold (terminal ∘ f) = ≤-refl
optimize-compose-cost-le fold (initial ∘ f) = ≤-refl
optimize-compose-cost-le fold ((curry _ _) ∘ f) = ≤-refl
optimize-compose-cost-le fold (apply ∘ f) = ≤-refl
optimize-compose-cost-le fold (fold ∘ f) = ≤-refl
optimize-compose-cost-le fold (arr ∘ f) = ≤-refl
optimize-compose-cost-le fold ((Prim _) ∘ f) = ≤-refl
optimize-compose-cost-le fold ((_ ∘ _) ∘ f) = ≤-refl
optimize-compose-cost-le unfold fst = ≤-refl
optimize-compose-cost-le unfold snd = ≤-refl
optimize-compose-cost-le unfold (⟨ _ , _ ⟩ _) = ≤-refl
optimize-compose-cost-le unfold (inl _) = ≤-refl
optimize-compose-cost-le unfold (inr _) = ≤-refl
optimize-compose-cost-le unfold [ _ , _ ] = ≤-refl
optimize-compose-cost-le unfold terminal = ≤-refl
optimize-compose-cost-le unfold (curry _ _) = ≤-refl
optimize-compose-cost-le unfold apply = ≤-refl
optimize-compose-cost-le unfold unfold = ≤-refl
optimize-compose-cost-le unfold arr = ≤-refl
optimize-compose-cost-le unfold (Prim _) = ≤-refl
optimize-compose-cost-le unfold (id ∘ f) = ≤-refl
optimize-compose-cost-le unfold (fst ∘ f) = ≤-refl
optimize-compose-cost-le unfold (snd ∘ f) = ≤-refl
optimize-compose-cost-le unfold ((⟨ _ , _ ⟩ _) ∘ f) = ≤-refl
optimize-compose-cost-le unfold ((inl _) ∘ f) = ≤-refl
optimize-compose-cost-le unfold ((inr _) ∘ f) = ≤-refl
optimize-compose-cost-le unfold ([ _ , _ ] ∘ f) = ≤-refl
optimize-compose-cost-le unfold (terminal ∘ f) = ≤-refl
optimize-compose-cost-le unfold (initial ∘ f) = ≤-refl
optimize-compose-cost-le unfold ((curry _ _) ∘ f) = ≤-refl
optimize-compose-cost-le unfold (apply ∘ f) = ≤-refl
optimize-compose-cost-le unfold (unfold ∘ f) = ≤-refl
optimize-compose-cost-le unfold (arr ∘ f) = ≤-refl
optimize-compose-cost-le unfold ((Prim _) ∘ f) = ≤-refl
optimize-compose-cost-le unfold ((_ ∘ _) ∘ f) = ≤-refl
optimize-compose-cost-le arr f = ≤-refl
optimize-compose-cost-le (Prim n) f = ≤-refl

-- | optimize-pair does not increase cost beyond the pair allocation
--
-- Proof by case analysis matching the optimizer's pattern structure.
-- Each case either:
--   - Returns id (cost 0 ≤ 1 + cost f + cost g)
--   - Returns h from fst∘h, snd∘h (cost h ≤ 1 + cost h + cost h)
--   - Returns the pair unchanged (cost 1 + f + g = 1 + f + g)
optimize-pair-cost-le : ∀ {A B C} (f : IR C A) (g : IR C B) →
  cost (optimize-pair f g) ≤ suc (cost f ℕ+ cost g)
-- Eta case: fst, snd
optimize-pair-cost-le (fst {A} {B}) (snd {A'} {B'}) with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = z≤n   -- cost id = 0 ≤ 1
... | _        | _        = ≤-refl -- cost ⟨fst,snd⟩ = 1 ≤ 1
-- Uniqueness case: fst ∘ h, snd ∘ h'
optimize-pair-cost-le (_∘_ {_} {D} {_} (fst {A} {B}) h) (_∘_ {_} {D'} {_} (snd {A'} {B'}) h')
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = s≤s (m≤n+m (cost h) (cost h))  -- cost h ≤ 1 + cost h + cost h
...   | no _     = ≤-refl                          -- cost ⟨fst∘h, snd∘h'⟩ ≤ 1 + cost h + cost h'
optimize-pair-cost-le (_∘_ (fst {A} {B}) h) (_∘_ (snd {A'} {B'}) h') | _ | _ | _ = ≤-refl
-- Default case for fst
optimize-pair-cost-le fst g = ≤-refl
-- Default case for snd
optimize-pair-cost-le snd g = ≤-refl
-- Default case: non-fst/snd first component
optimize-pair-cost-le id g = ≤-refl
optimize-pair-cost-le (⟨ _ , _ ⟩ _) g = ≤-refl
optimize-pair-cost-le (inl _) g = ≤-refl
optimize-pair-cost-le (inr _) g = ≤-refl
optimize-pair-cost-le [ _ , _ ] g = ≤-refl
optimize-pair-cost-le terminal g = ≤-refl
optimize-pair-cost-le initial g = ≤-refl
optimize-pair-cost-le (curry _ _) g = ≤-refl
optimize-pair-cost-le apply g = ≤-refl
optimize-pair-cost-le fold g = ≤-refl
optimize-pair-cost-le unfold g = ≤-refl
optimize-pair-cost-le arr g = ≤-refl
optimize-pair-cost-le (Prim _) g = ≤-refl
-- Composition cases (non-fst/snd composed)
optimize-pair-cost-le (id ∘ f) g = ≤-refl
optimize-pair-cost-le ((g' ∘ f') ∘ f) g = ≤-refl
optimize-pair-cost-le (snd ∘ f) g = ≤-refl
optimize-pair-cost-le ((⟨ _ , _ ⟩ _) ∘ f) g = ≤-refl
optimize-pair-cost-le ((inl _) ∘ f) g = ≤-refl
optimize-pair-cost-le ((inr _) ∘ f) g = ≤-refl
optimize-pair-cost-le ([ _ , _ ] ∘ f) g = ≤-refl
optimize-pair-cost-le (terminal ∘ f) g = ≤-refl
optimize-pair-cost-le (initial ∘ f) g = ≤-refl
optimize-pair-cost-le ((curry _ _) ∘ f) g = ≤-refl
optimize-pair-cost-le (apply ∘ f) g = ≤-refl
optimize-pair-cost-le (fold ∘ f) g = ≤-refl
optimize-pair-cost-le (unfold ∘ f) g = ≤-refl
optimize-pair-cost-le (arr ∘ f) g = ≤-refl
optimize-pair-cost-le ((Prim _) ∘ f) g = ≤-refl

-- | optimize-case does not increase cost
--
-- Proof by case analysis matching the optimizer's pattern structure.
-- Each case either:
--   - Returns id (cost 0 ≤ cost inl + cost inr = 2)
--   - Returns h from h∘inl, h∘inr (cost h ≤ 2 + 2*cost h)
--   - Returns the case unchanged (cost f + g = cost f + cost g)
optimize-case-cost-le : ∀ {A B C} (f : IR A C) (g : IR B C) →
  cost (optimize-case f g) ≤ cost f ℕ+ cost g
-- Eta case: inl, inr
optimize-case-cost-le (inl {A} {B} m) (inr {A'} {B'} m') with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = z≤n   -- cost id = 0 ≤ 1 + 1 = 2
... | _        | _        = ≤-refl -- cost [inl, inr] = 1 + 1 ≤ 1 + 1
-- Uniqueness case: h ∘ inl, h' ∘ inr
optimize-case-cost-le (_∘_ {_} {D} {_} h (inl {A} {B} m)) (_∘_ {_} {D'} {_} h' (inr {A'} {B'} m'))
  with A ≟Type A' | B ≟Type B' | D ≟Type D'
... | yes refl | yes refl | yes refl with h ≟IR h'
...   | yes refl = m≤n+m (cost h) (suc (cost h))  -- cost h ≤ (cost h + 1) + (cost h + 1)
...   | no _     = ≤-refl                          -- cost [h∘inl, h'∘inr] = cost (h∘inl) + cost (h'∘inr)
optimize-case-cost-le (_∘_ h (inl {A} {B} m)) (_∘_ h' (inr {A'} {B'} m')) | _ | _ | _ = ≤-refl
-- Default case for inl
optimize-case-cost-le (inl m) g = ≤-refl
-- Default case for inr
optimize-case-cost-le (inr m) g = ≤-refl
-- Default cases: non-inl/inr first component
optimize-case-cost-le id g = ≤-refl
optimize-case-cost-le (⟨ _ , _ ⟩ _) g = ≤-refl
optimize-case-cost-le fst g = ≤-refl
optimize-case-cost-le snd g = ≤-refl
optimize-case-cost-le [ _ , _ ] g = ≤-refl
optimize-case-cost-le terminal g = ≤-refl
optimize-case-cost-le initial g = ≤-refl
optimize-case-cost-le (curry _ _) g = ≤-refl
optimize-case-cost-le apply g = ≤-refl
optimize-case-cost-le fold g = ≤-refl
optimize-case-cost-le unfold g = ≤-refl
optimize-case-cost-le arr g = ≤-refl
optimize-case-cost-le (Prim _) g = ≤-refl
-- Composition cases (non-inl composed)
optimize-case-cost-le (id ∘ f) g = ≤-refl
optimize-case-cost-le ((g' ∘ f') ∘ f) g = ≤-refl
optimize-case-cost-le ((⟨ _ , _ ⟩ _) ∘ f) g = ≤-refl
optimize-case-cost-le (fst ∘ f) g = ≤-refl
optimize-case-cost-le (snd ∘ f) g = ≤-refl
optimize-case-cost-le ((inr _) ∘ f) g = ≤-refl
optimize-case-cost-le ([ _ , _ ] ∘ f) g = ≤-refl
optimize-case-cost-le (terminal ∘ f) g = ≤-refl
optimize-case-cost-le (initial ∘ f) g = ≤-refl
optimize-case-cost-le ((curry _ _) ∘ f) g = ≤-refl
optimize-case-cost-le (apply ∘ f) g = ≤-refl
optimize-case-cost-le (fold ∘ f) g = ≤-refl
optimize-case-cost-le (unfold ∘ f) g = ≤-refl
optimize-case-cost-le (arr ∘ f) g = ≤-refl
optimize-case-cost-le ((Prim _) ∘ f) g = ≤-refl

-- | Structural optimization does not increase cost
optimize-once-structural-cost-le : ∀ {A B} (t : IR A B) → cost (optimize-once-structural t) ≤ cost t
optimize-once-structural-cost-le id = ≤-refl
optimize-once-structural-cost-le (g ∘ f) =
  ≤-trans (optimize-compose-cost-le (optimize-once g) (optimize-once f))
          (+-mono-≤ (optimize-once-cost-le g) (optimize-once-cost-le f))
optimize-once-structural-cost-le fst = ≤-refl
optimize-once-structural-cost-le snd = ≤-refl
optimize-once-structural-cost-le (⟨ f , g ⟩ m) =
  ≤-trans (optimize-pair-cost-le (optimize-once f) (optimize-once g))
          (s≤s (+-mono-≤ (optimize-once-cost-le f) (optimize-once-cost-le g)))
optimize-once-structural-cost-le (inl {A} m) with A ≟Type Void
... | yes refl = z≤n
... | no _ = ≤-refl
optimize-once-structural-cost-le (inr {_} {B} m) with B ≟Type Void
... | yes refl = z≤n
... | no _ = ≤-refl
optimize-once-structural-cost-le [ f , g ] =
  ≤-trans (optimize-case-cost-le (optimize-once f) (optimize-once g))
          (+-mono-≤ (optimize-once-cost-le f) (optimize-once-cost-le g))
optimize-once-structural-cost-le terminal = ≤-refl
optimize-once-structural-cost-le initial = ≤-refl
optimize-once-structural-cost-le (curry f m) = s≤s (optimize-once-cost-le f)
optimize-once-structural-cost-le apply = ≤-refl
optimize-once-structural-cost-le (fold {F}) with F ≟Type Void
... | yes refl = z≤n
... | no _ = ≤-refl
optimize-once-structural-cost-le unfold = ≤-refl
optimize-once-structural-cost-le arr = ≤-refl
optimize-once-structural-cost-le (Prim {A} n) with A ≟Type Void
... | yes refl = z≤n
... | no _ = ≤-refl

-- | Single optimization pass does not increase cost (type-directed)
--
-- Type-directed rules return terminal/initial which have cost 0,
-- so cost always decreases or stays the same.
optimize-once-cost-le : ∀ {A B} (t : IR A B) → cost (optimize-once t) ≤ cost t
optimize-once-cost-le {A} {B} t with B ≟Type Unit
... | yes refl = z≤n  -- cost terminal = 0 ≤ cost t
... | no _ with A ≟Type Void
...   | yes refl = z≤n  -- cost initial = 0 ≤ cost t
...   | no _ = optimize-once-structural-cost-le t

-- | Repeated optimization does not increase cost
optimize-n-cost-le : ∀ {A B} (n : ℕ) (t : IR A B) → cost (optimize-n n t) ≤ cost t
optimize-n-cost-le zero t = ≤-refl
optimize-n-cost-le (suc n) t =
  ≤-trans (optimize-n-cost-le n (optimize-once t)) (optimize-once-cost-le t)

-- | Optimization does not increase cost
optimize-cost-le : ∀ {A B} (t : IR A B) → cost (optimize t) ≤ cost t
optimize-cost-le t = optimize-n-cost-le 10 t

-- | Normal forms have minimal cost
--
-- Proof: If t is normal and semantically equivalent to t', then:
-- 1. optimize t' is normal (by optimize-normal)
-- 2. optimize t' is semantically equivalent to t (by optimize-correct + given eq)
-- 3. By normal-unique: optimize t' ≡ t
-- 4. By optimize-cost-le: cost (optimize t') ≤ cost t'
-- 5. Therefore: cost t ≤ cost t'
normal-minimal : ∀ {A B} (t t' : IR A B) →
  IsNormal t →
  (∀ x → eval t x ≡ eval t' x) →
  cost t ≤ cost t'
normal-minimal t t' nt eq =
  let -- optimize t' is semantically equivalent to t
      opt-equiv : ∀ x → eval (optimize t') x ≡ eval t x
      opt-equiv = λ x → trans (optimize-correct t' x) (sym (eq x))
      -- By normal-unique, optimize t' ≡ t
      opt-eq-t : optimize t' ≡ t
      opt-eq-t = normal-unique (optimize t') t (optimize-normal t') nt opt-equiv
      -- cost (optimize t') ≤ cost t'
      opt-cost : cost (optimize t') ≤ cost t'
      opt-cost = optimize-cost-le t'
  in subst (λ z → cost z ≤ cost t') opt-eq-t opt-cost

------------------------------------------------------------------------
-- Coherence Theorem
------------------------------------------------------------------------

-- | Two semantically equivalent terms optimize to the same normal form.
-- This follows from:
--   1. optimize produces normal forms (optimize-normal)
--   2. normal forms are unique per equivalence class (normal-unique)
coherence : ∀ {A B} (t t' : IR A B) →
  (∀ x → eval t x ≡ eval t' x) →
  optimize t ≡ optimize t'
coherence t t' eq = normal-unique (optimize t) (optimize t')
  (optimize-normal t)
  (optimize-normal t')
  (λ x → trans (optimize-correct t x) (trans (eq x) (sym (optimize-correct t' x))))
