------------------------------------------------------------------------
-- Catamorphisms: Generic CCC Catamorphism Lemmas
--
-- This module provides reusable lemmas for catamorphisms in CCCs:
--   - fmap-id: fmap F id ⟶* id for any functor F
--   - fmap distribution through injections
--   - cata-β-right: Right-associated catamorphism beta reduction
--
-- These lemmas are fundamental to any CCC catamorphism-based tool
-- (normalizers, compilers, optimizers).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Encoding.Catamorphisms where

open import normalizer.Syntax.CCC public

------------------------------------------------------------------------
-- Infrastructure: Congruence lemmas for ⟹*
------------------------------------------------------------------------

-- Transitivity of ⟹*
⟹*-trans : ∀ {A B} {t u v : Term A B} → t ⟹* u → u ⟹* v → t ⟹* v
⟹*-trans done⟹ q = q
⟹*-trans (step⟹ p ps) q = step⟹ p (⟹*-trans ps q)

-- Single step to multi-step
⟹→⟹* : ∀ {A B} {t u : Term A B} → t ⟹ u → t ⟹* u
⟹→⟹* p = step⟹ p done⟹

-- Congruence: composition on the right
⟹*-∘-right : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
             g ⟹* g' → (f ∘ g) ⟹* (f ∘ g')
⟹*-∘-right done⟹ = done⟹
⟹*-∘-right (step⟹ p ps) = step⟹ (⟹-∘ (⟹-refl _) p) (⟹*-∘-right ps)

-- Congruence: composition on the left
⟹*-∘-left : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
            f ⟹* f' → (f ∘ g) ⟹* (f' ∘ g)
⟹*-∘-left done⟹ = done⟹
⟹*-∘-left (step⟹ p ps) = step⟹ (⟹-∘ p (⟹-refl _)) (⟹*-∘-left ps)

-- Congruence: case/coproduct
⟹*-case : ∀ {A B C} {f f' : Term A C} {g g' : Term B C} →
          f ⟹* f' → g ⟹* g' → [ f , g ] ⟹* [ f' , g' ]
⟹*-case done⟹ done⟹ = done⟹
⟹*-case done⟹ (step⟹ q qs) = step⟹ (⟹-case (⟹-refl _) q) (⟹*-case done⟹ qs)
⟹*-case (step⟹ p ps) qs = step⟹ (⟹-case p (⟹-refl _)) (⟹*-case ps qs)

-- Congruence: pair/product
⟹*-pair : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟹* f' → g ⟹* g' → ⟨ f , g ⟩ ⟹* ⟨ f' , g' ⟩
⟹*-pair done⟹ done⟹ = done⟹
⟹*-pair done⟹ (step⟹ q qs) = step⟹ (⟹-pair (⟹-refl _) q) (⟹*-pair done⟹ qs)
⟹*-pair (step⟹ p ps) qs = step⟹ (⟹-pair p (⟹-refl _)) (⟹*-pair ps qs)

------------------------------------------------------------------------
-- The fmap-id proof: fmap F id ⟶* id
------------------------------------------------------------------------

-- First in ⟹* form, then convert to ⟶*

fmap-id⟹* : ∀ F {A} → fmap F (id {A}) ⟹* id
fmap-id⟹* Id = done⟹  -- fmap Id id = id definitionally
fmap-id⟹* One = done⟹  -- fmap One _ = id definitionally
fmap-id⟹* (Kc _) = done⟹  -- fmap (Kc _) _ = id definitionally
fmap-id⟹* (F ⊕ G) =
  -- fmap (F ⊕ G) id = [ inl ∘ fmap F id , inr ∘ fmap G id ]
  -- Goal: [ inl ∘ fmap F id , inr ∘ fmap G id ] ⟹* id
  --
  -- Step 1: By IH, fmap F id ⟹* id and fmap G id ⟹* id
  -- Step 2: inl ∘ fmap F id ⟹* inl ∘ id  (congruence)
  -- Step 3: inl ∘ id ⟹ inl               (id-right)
  -- Step 4: Similarly for inr side
  -- Step 5: [ inl , inr ] ⟹ id           (eta-case)
  let
    -- IH: fmap F id ⟹* id, fmap G id ⟹* id
    ih-F = fmap-id⟹* F
    ih-G = fmap-id⟹* G
    -- inl ∘ fmap F id ⟹* inl ∘ id ⟹* inl
    left-reduces : (inl ∘ fmap F id) ⟹* inl
    left-reduces = ⟹*-trans (⟹*-∘-right ih-F) (⟹→⟹* (⟹-id-r ⟹-inl))
    -- inr ∘ fmap G id ⟹* inr ∘ id ⟹* inr
    right-reduces : (inr ∘ fmap G id) ⟹* inr
    right-reduces = ⟹*-trans (⟹*-∘-right ih-G) (⟹→⟹* (⟹-id-r ⟹-inr))
    -- [ inl ∘ fmap F id , inr ∘ fmap G id ] ⟹* [ inl , inr ]
    case-reduces : [ inl ∘ fmap F id , inr ∘ fmap G id ] ⟹* [ inl , inr ]
    case-reduces = ⟹*-case left-reduces right-reduces
  in
    -- [ inl , inr ] ⟹ id by eta-case
    ⟹*-trans case-reduces (⟹→⟹* ⟹-η-case)

fmap-id⟹* (F ⊗ G) =
  -- fmap (F ⊗ G) id = ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩
  -- Goal: ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩ ⟹* id
  --
  -- Step 1: By IH, fmap F id ⟹* id and fmap G id ⟹* id
  -- Step 2: fmap F id ∘ fst ⟹* id ∘ fst ⟹* fst  (congruence + id-left)
  -- Step 3: Similarly for snd side
  -- Step 4: ⟨ fst , snd ⟩ ⟹ id                   (eta-pair)
  let
    ih-F = fmap-id⟹* F
    ih-G = fmap-id⟹* G
    -- fmap F id ∘ fst ⟹* id ∘ fst ⟹ fst
    left-reduces : (fmap F id ∘ fst) ⟹* fst
    left-reduces = ⟹*-trans (⟹*-∘-left ih-F) (⟹→⟹* (⟹-id-l ⟹-fst))
    -- fmap G id ∘ snd ⟹* id ∘ snd ⟹ snd
    right-reduces : (fmap G id ∘ snd) ⟹* snd
    right-reduces = ⟹*-trans (⟹*-∘-left ih-G) (⟹→⟹* (⟹-id-l ⟹-snd))
    -- ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩ ⟹* ⟨ fst , snd ⟩
    pair-reduces : ⟨ fmap F id ∘ fst , fmap G id ∘ snd ⟩ ⟹* ⟨ fst , snd ⟩
    pair-reduces = ⟹*-pair left-reduces right-reduces
  in
    -- ⟨ fst , snd ⟩ ⟹ id by eta-pair
    ⟹*-trans pair-reduces (⟹→⟹* ⟹-η-pair)

-- Convert to ⟶*
fmap-id : ∀ F {A} → fmap F (id {A}) ⟶* id
fmap-id F = ⟹*→⟶* (fmap-id⟹* F)

------------------------------------------------------------------------
-- fmap distribution through injections
------------------------------------------------------------------------

-- fmap distributes through inl: fmap (F ⊕ G) f ∘ inl ⟶* inl ∘ fmap F f
fmap-sum-inl : ∀ {A B} F G (f : Term A B) →
               (fmap (F ⊕ G) f ∘ inl) ⟶* (inl ∘ fmap F f)
fmap-sum-inl F G f = step case-inl done

-- fmap distributes through inr: fmap (F ⊕ G) f ∘ inr ⟶* inr ∘ fmap G f
fmap-through-inr : ∀ {A B} F G (f : Term A B) →
                   (fmap (F ⊕ G) f ∘ inr) ⟶* (inr ∘ fmap G f)
fmap-through-inr F G f = step case-inr done

-- Kc-pair reduces to identity via eta-pair
-- fmap (Kc X ⊗ Kc Y) f = ⟨ id ∘ fst , id ∘ snd ⟩ ⟶* id
fmap-KK-id : ∀ {A B} X Y (f : Term A B) → fmap (Kc X ⊗ Kc Y) f ⟶* id
fmap-KK-id X Y f =
  -- fmap (Kc X ⊗ Kc Y) f = ⟨ fmap (Kc X) f ∘ fst , fmap (Kc Y) f ∘ snd ⟩
  --                    = ⟨ id ∘ fst , id ∘ snd ⟩
  -- ⟶ ⟨ fst , snd ⟩ by id-left (twice)
  -- ⟶ id by eta-pair
  ⟶*-trans (⟹→⟶* (⟹-pair (⟹-id-l ⟹-fst) (⟹-id-l ⟹-snd))) (step eta-pair done)

------------------------------------------------------------------------
-- Additional congruence lemmas
------------------------------------------------------------------------

-- Congruence: if x ⟶ y, then x ∘ t ⟶* y ∘ t
-- Uses parallel reduction which has congruence rules
∘-cong-left : ∀ {A B C} {x y : Term B C} (t : Term A B) →
              x ⟶ y → (x ∘ t) ⟶* (y ∘ t)
∘-cong-left t r = ⟹→⟶* (⟹-∘ (⟶→⟹ r) (⟹-refl t))

-- Congruence: if f ⟶* f', then f ∘ g ⟶* f' ∘ g
∘-cong-left' : ∀ {A B C} {f f' : Term B C} (g : Term A B) →
               f ⟶* f' → (f ∘ g) ⟶* (f' ∘ g)
∘-cong-left' g done = done
∘-cong-left' g (step r rs) = ⟶*-trans (∘-cong-left g r) (∘-cong-left' g rs)

-- Congruence: if g ⟶* g', then f ∘ g ⟶* f ∘ g'
∘-cong-right' : ∀ {A B C} (f : Term B C) {g g' : Term A B} →
                g ⟶* g' → (f ∘ g) ⟶* (f ∘ g')
∘-cong-right' f done = done
∘-cong-right' f (step r rs) = ⟶*-trans (⟹→⟶* (⟹-∘ (⟹-refl f) (⟶→⟹ r))) (∘-cong-right' f rs)

-- Congruence for pair: if a ⟶* a' and b ⟶* b', then ⟨a,b⟩ ⟶* ⟨a',b'⟩
⟨⟩-cong : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
          f ⟶* f' → g ⟶* g' → ⟨ f , g ⟩ ⟶* ⟨ f' , g' ⟩
⟨⟩-cong done done = done
⟨⟩-cong done (step q qs) = ⟶*-trans (⟹→⟶* (⟹-pair (⟹-refl _) (⟶→⟹ q))) (⟨⟩-cong done qs)
⟨⟩-cong (step p ps) qs = ⟶*-trans (⟹→⟶* (⟹-pair (⟶→⟹ p) (⟹-refl _))) (⟨⟩-cong ps qs)

------------------------------------------------------------------------
-- Catamorphism beta reduction (right-associated version)
------------------------------------------------------------------------

-- Derived cata reduction using assoc-l and congruence
-- cata F alg ∘ (In ∘ t)
-- ⟶ (cata F alg ∘ In) ∘ t    by assoc-l
-- ⟶* (alg ∘ fmap F (cata F alg)) ∘ t    by cata-β with congruence
cata-β-right : ∀ {F A B} {alg : Term (⟦ F ⟧F A) A} {t : Term B (⟦ F ⟧F (μ F))} →
               (cata F alg ∘ (In ∘ t)) ⟶* ((alg ∘ fmap F (cata F alg)) ∘ t)
cata-β-right {F} {A} {B} {alg} {t} =
  ⟶*-trans (step assoc-l done)
           (∘-cong-left t cata-β)
