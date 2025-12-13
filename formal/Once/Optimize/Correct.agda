------------------------------------------------------------------------
-- Once.Optimize.Correct
--
-- Correctness proofs for the Once optimizer.
-- Each optimization rule preserves semantics.
--
-- POSTULATES: This module uses one postulate:
--   - funext (function extensionality): ∀ x → f x ≡ g x → f ≡ g
--
-- WHY FUNEXT IS SAFE TO POSTULATE:
--   1. It's consistent with MLTT (proven via setoid/realizability models)
--   2. It's provable in Cubical Type Theory (Agda --cubical)
--   3. It holds in the standard "sets and functions" semantics
--   4. It's standard practice (see Axiom.Extensionality.Propositional
--      in the Agda standard library)
--
-- WHY FUNEXT IS NEEDED:
--   The curry case requires proving equality of functions:
--     eval (curry (optimize-once f)) x ≡ eval (curry f) x
--   which reduces to proving two lambdas equal, requiring funext.
------------------------------------------------------------------------

module Once.Optimize.Correct where

open import Once.Type
open import Once.IR
open import Once.Semantics
open import Once.Optimize
open import Once.Category.Laws

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

------------------------------------------------------------------------
-- Correctness of optimize-compose
--
-- Type constraints determine which constructor combinations are valid:
--
-- Output types:
--   ⟨_,_⟩, fst, snd     → product
--   inl, inr            → sum
--   terminal            → Unit
--   curry               → function (A ⇒ B)
--   fold                → Fix F
--   arr                 → Eff A B
--   id, ∘, [_,_], apply, unfold → depends on context
--
-- Input requirements:
--   fst, snd   → product
--   [_,_]      → sum
--   apply      → product ((A ⇒ B) * A)
--   unfold     → Fix F
--   arr        → function (A ⇒ B)
------------------------------------------------------------------------

optimize-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                         → eval (optimize-compose g f) x ≡ eval (g ∘ f) x

-- Left identity: id ∘ f = f
optimize-compose-correct id f x = refl

-- Initial: no optimization (catch-all applies)
optimize-compose-correct initial f x = refl

-- fst cases (fst needs product input)
-- Valid: id, ∘, fst, snd, ⟨_,_⟩, [_,_], apply, unfold
-- Invalid: inl, inr, terminal, curry, fold, arr (outputs don't match)
optimize-compose-correct fst id x = refl
optimize-compose-correct fst (g' ∘ f') x = refl
optimize-compose-correct fst fst x = refl
optimize-compose-correct fst snd x = refl
optimize-compose-correct fst ⟨ f' , g' ⟩ x = refl  -- Product beta
optimize-compose-correct fst [ f' , g' ] x = refl
optimize-compose-correct fst apply x = refl
optimize-compose-correct fst unfold x = refl

-- snd cases (same constraints as fst)
optimize-compose-correct snd id x = refl
optimize-compose-correct snd (g' ∘ f') x = refl
optimize-compose-correct snd fst x = refl
optimize-compose-correct snd snd x = refl
optimize-compose-correct snd ⟨ f' , g' ⟩ x = refl  -- Product beta
optimize-compose-correct snd [ f' , g' ] x = refl
optimize-compose-correct snd apply x = refl
optimize-compose-correct snd unfold x = refl

-- ⟨_,_⟩ cases (accepts any input type)
optimize-compose-correct ⟨ f' , g' ⟩ id x = refl
optimize-compose-correct ⟨ f' , g' ⟩ (h ∘ h') x = refl
optimize-compose-correct ⟨ f' , g' ⟩ fst x = refl
optimize-compose-correct ⟨ f' , g' ⟩ snd x = refl
optimize-compose-correct ⟨ f' , g' ⟩ ⟨ h , h' ⟩ x = refl
optimize-compose-correct ⟨ f' , g' ⟩ inl x = refl
optimize-compose-correct ⟨ f' , g' ⟩ inr x = refl
optimize-compose-correct ⟨ f' , g' ⟩ [ h , h' ] x = refl
optimize-compose-correct ⟨ f' , g' ⟩ terminal x = refl
optimize-compose-correct ⟨ f' , g' ⟩ (curry h) x = refl
optimize-compose-correct ⟨ f' , g' ⟩ apply x = refl
optimize-compose-correct ⟨ f' , g' ⟩ fold x = refl
optimize-compose-correct ⟨ f' , g' ⟩ unfold x = refl
optimize-compose-correct ⟨ f' , g' ⟩ arr x = refl

-- inl cases (accepts any input type)
optimize-compose-correct inl id x = refl
optimize-compose-correct inl (g' ∘ f') x = refl
optimize-compose-correct inl fst x = refl
optimize-compose-correct inl snd x = refl
optimize-compose-correct inl ⟨ f' , g' ⟩ x = refl
optimize-compose-correct inl inl x = refl
optimize-compose-correct inl inr x = refl
optimize-compose-correct inl [ f' , g' ] x = refl
optimize-compose-correct inl terminal x = refl
optimize-compose-correct inl (curry f') x = refl
optimize-compose-correct inl apply x = refl
optimize-compose-correct inl fold x = refl
optimize-compose-correct inl unfold x = refl
optimize-compose-correct inl arr x = refl

-- inr cases (accepts any input type)
optimize-compose-correct inr id x = refl
optimize-compose-correct inr (g' ∘ f') x = refl
optimize-compose-correct inr fst x = refl
optimize-compose-correct inr snd x = refl
optimize-compose-correct inr ⟨ f' , g' ⟩ x = refl
optimize-compose-correct inr inl x = refl
optimize-compose-correct inr inr x = refl
optimize-compose-correct inr [ f' , g' ] x = refl
optimize-compose-correct inr terminal x = refl
optimize-compose-correct inr (curry f') x = refl
optimize-compose-correct inr apply x = refl
optimize-compose-correct inr fold x = refl
optimize-compose-correct inr unfold x = refl
optimize-compose-correct inr arr x = refl

-- [_,_] cases (needs sum input)
-- Valid: id, ∘, fst, snd, inl, inr, [_,_], apply, unfold
-- Invalid: ⟨_,_⟩, terminal, curry, fold, arr (outputs don't match)
optimize-compose-correct [ f' , g' ] id x = refl
optimize-compose-correct [ f' , g' ] (h ∘ h') x = refl
optimize-compose-correct [ f' , g' ] fst x = refl
optimize-compose-correct [ f' , g' ] snd x = refl
optimize-compose-correct [ f' , g' ] inl x = refl  -- Coproduct beta
optimize-compose-correct [ f' , g' ] inr x = refl  -- Coproduct beta
optimize-compose-correct [ f' , g' ] [ h , h' ] x = refl
optimize-compose-correct [ f' , g' ] apply x = refl
optimize-compose-correct [ f' , g' ] unfold x = refl

-- terminal cases (accepts any input type)
optimize-compose-correct terminal id x = refl
optimize-compose-correct terminal (g' ∘ f') x = refl
optimize-compose-correct terminal fst x = refl
optimize-compose-correct terminal snd x = refl
optimize-compose-correct terminal ⟨ f' , g' ⟩ x = refl
optimize-compose-correct terminal inl x = refl
optimize-compose-correct terminal inr x = refl
optimize-compose-correct terminal [ f' , g' ] x = refl
optimize-compose-correct terminal terminal x = refl
optimize-compose-correct terminal (curry f') x = refl
optimize-compose-correct terminal apply x = refl
optimize-compose-correct terminal fold x = refl
optimize-compose-correct terminal unfold x = refl
optimize-compose-correct terminal arr x = refl

-- curry cases (accepts any input type)
optimize-compose-correct (curry f') id x = refl
optimize-compose-correct (curry f') (g' ∘ h) x = refl
optimize-compose-correct (curry f') fst x = refl
optimize-compose-correct (curry f') snd x = refl
optimize-compose-correct (curry f') ⟨ g' , h ⟩ x = refl
optimize-compose-correct (curry f') inl x = refl
optimize-compose-correct (curry f') inr x = refl
optimize-compose-correct (curry f') [ g' , h ] x = refl
optimize-compose-correct (curry f') terminal x = refl
optimize-compose-correct (curry f') (curry g') x = refl
optimize-compose-correct (curry f') apply x = refl
optimize-compose-correct (curry f') fold x = refl
optimize-compose-correct (curry f') unfold x = refl
optimize-compose-correct (curry f') arr x = refl

-- apply cases (needs product ((A ⇒ B) * A) input)
-- Valid: id, ∘, fst, snd, ⟨_,_⟩, [_,_], apply, unfold
-- Invalid: inl, inr, terminal, curry, fold, arr
optimize-compose-correct apply id x = refl
optimize-compose-correct apply (g' ∘ f') x = refl
optimize-compose-correct apply fst x = refl
optimize-compose-correct apply snd x = refl
optimize-compose-correct apply ⟨ f' , g' ⟩ x = refl
optimize-compose-correct apply [ f' , g' ] x = refl
optimize-compose-correct apply apply x = refl
optimize-compose-correct apply unfold x = refl

-- fold cases (accepts any input type F)
optimize-compose-correct fold id x = refl
optimize-compose-correct fold (g' ∘ f') x = refl
optimize-compose-correct fold fst x = refl
optimize-compose-correct fold snd x = refl
optimize-compose-correct fold ⟨ f' , g' ⟩ x = refl
optimize-compose-correct fold inl x = refl
optimize-compose-correct fold inr x = refl
optimize-compose-correct fold [ f' , g' ] x = refl
optimize-compose-correct fold terminal x = refl
optimize-compose-correct fold (curry f') x = refl
optimize-compose-correct fold apply x = refl
optimize-compose-correct fold fold x = refl
optimize-compose-correct fold unfold x = refl  -- Fixed point law
optimize-compose-correct fold arr x = refl

-- unfold cases (needs Fix F input)
-- Valid: id, ∘, fst, snd, [_,_], apply, fold, unfold
-- Invalid: ⟨_,_⟩, inl, inr, terminal, curry, arr
optimize-compose-correct unfold id x = refl
optimize-compose-correct unfold (g' ∘ f') x = refl
optimize-compose-correct unfold fst x = refl
optimize-compose-correct unfold snd x = refl
optimize-compose-correct unfold [ f' , g' ] x = refl
optimize-compose-correct unfold apply x = refl
optimize-compose-correct unfold fold x = refl  -- Fixed point law
optimize-compose-correct unfold unfold x = refl

-- arr cases (needs function (A ⇒ B) input)
-- Valid: id, ∘, fst, snd, [_,_], curry, apply, unfold
-- Invalid: ⟨_,_⟩, inl, inr, terminal, fold, arr
optimize-compose-correct arr id x = refl
optimize-compose-correct arr (g' ∘ f') x = refl
optimize-compose-correct arr fst x = refl
optimize-compose-correct arr snd x = refl
optimize-compose-correct arr [ f' , g' ] x = refl
optimize-compose-correct arr (curry f') x = refl
optimize-compose-correct arr apply x = refl
optimize-compose-correct arr unfold x = refl

-- Associativity: (h ∘ g) ∘ f → optimize h (optimize g f)
optimize-compose-correct (h ∘ g) id x = refl
optimize-compose-correct (h ∘ g) (f' ∘ f'') x =
  trans (optimize-compose-correct h (optimize-compose g (f' ∘ f'')) x)
        (cong (eval h) (optimize-compose-correct g (f' ∘ f'') x))
optimize-compose-correct (h ∘ g) fst x =
  trans (optimize-compose-correct h (optimize-compose g fst) x)
        (cong (eval h) (optimize-compose-correct g fst x))
optimize-compose-correct (h ∘ g) snd x =
  trans (optimize-compose-correct h (optimize-compose g snd) x)
        (cong (eval h) (optimize-compose-correct g snd x))
optimize-compose-correct (h ∘ g) ⟨ f' , f'' ⟩ x =
  trans (optimize-compose-correct h (optimize-compose g ⟨ f' , f'' ⟩) x)
        (cong (eval h) (optimize-compose-correct g ⟨ f' , f'' ⟩ x))
optimize-compose-correct (h ∘ g) inl x =
  trans (optimize-compose-correct h (optimize-compose g inl) x)
        (cong (eval h) (optimize-compose-correct g inl x))
optimize-compose-correct (h ∘ g) inr x =
  trans (optimize-compose-correct h (optimize-compose g inr) x)
        (cong (eval h) (optimize-compose-correct g inr x))
optimize-compose-correct (h ∘ g) [ f' , f'' ] x =
  trans (optimize-compose-correct h (optimize-compose g [ f' , f'' ]) x)
        (cong (eval h) (optimize-compose-correct g [ f' , f'' ] x))
optimize-compose-correct (h ∘ g) terminal x =
  trans (optimize-compose-correct h (optimize-compose g terminal) x)
        (cong (eval h) (optimize-compose-correct g terminal x))
optimize-compose-correct (h ∘ g) (curry f') x =
  trans (optimize-compose-correct h (optimize-compose g (curry f')) x)
        (cong (eval h) (optimize-compose-correct g (curry f') x))
optimize-compose-correct (h ∘ g) apply x =
  trans (optimize-compose-correct h (optimize-compose g apply) x)
        (cong (eval h) (optimize-compose-correct g apply x))
optimize-compose-correct (h ∘ g) fold x =
  trans (optimize-compose-correct h (optimize-compose g fold) x)
        (cong (eval h) (optimize-compose-correct g fold x))
optimize-compose-correct (h ∘ g) unfold x =
  trans (optimize-compose-correct h (optimize-compose g unfold) x)
        (cong (eval h) (optimize-compose-correct g unfold x))
optimize-compose-correct (h ∘ g) arr x =
  trans (optimize-compose-correct h (optimize-compose g arr) x)
        (cong (eval h) (optimize-compose-correct g arr x))

------------------------------------------------------------------------
-- Correctness of optimize-pair
------------------------------------------------------------------------

optimize-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
                      → eval (optimize-pair f g) x ≡ eval ⟨ f , g ⟩ x

-- Eta law: ⟨ fst , snd ⟩ = id
-- When types match, optimize-pair returns id, so we need:
--   eval id x ≡ eval ⟨ fst , snd ⟩ x
--   x ≡ eval ⟨ fst , snd ⟩ x
-- Which is sym of eval-pair-eta
optimize-pair-correct (fst {A} {B}) (snd {A'} {B'}) x with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = sym (eval-pair-eta x)
... | yes refl | no _     = refl
... | no _     | yes _    = refl
... | no _     | no _     = refl

-- All other fst cases (where g is not snd with matching types)
-- Note: fst requires product input, so g must also accept product input
-- Invalid: [_,_] (needs sum), unfold (needs Fix), arr (needs function)
optimize-pair-correct fst id x = refl
optimize-pair-correct fst (g ∘ h) x = refl
optimize-pair-correct fst fst x = refl
optimize-pair-correct fst ⟨ g , h ⟩ x = refl
optimize-pair-correct fst inl x = refl
optimize-pair-correct fst inr x = refl
optimize-pair-correct fst terminal x = refl
optimize-pair-correct fst (curry g) x = refl
optimize-pair-correct fst apply x = refl
optimize-pair-correct fst fold x = refl

-- All other cases: no change (handle by first argument constructor)
optimize-pair-correct id g x = refl
optimize-pair-correct (f ∘ h) g x = refl
optimize-pair-correct snd g x = refl
optimize-pair-correct ⟨ f , h ⟩ g x = refl
optimize-pair-correct inl g x = refl
optimize-pair-correct inr g x = refl
optimize-pair-correct [ f , h ] g x = refl
optimize-pair-correct terminal g x = refl
optimize-pair-correct (curry f) g x = refl
optimize-pair-correct apply g x = refl
optimize-pair-correct fold g x = refl
optimize-pair-correct unfold g x = refl
optimize-pair-correct arr g x = refl

------------------------------------------------------------------------
-- Correctness of optimize-case
------------------------------------------------------------------------

optimize-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧)
                      → eval (optimize-case f g) x ≡ eval [ f , g ] x

-- Eta law: [ inl , inr ] = id
-- When types match, optimize-case returns id, so we need:
--   eval id x ≡ eval [ inl , inr ] x
--   x ≡ eval [ inl , inr ] x
-- Which is sym of eval-case-eta
optimize-case-correct (inl {A} {B}) (inr {A'} {B'}) x with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = sym (eval-case-eta x)
... | yes refl | no _     = refl
... | no _     | yes _    = refl
... | no _     | no _     = refl

-- All other inl cases (where g is not inr with matching types)
-- inl outputs sum (A + B), so g must also output sum type
-- Invalid: ⟨_,_⟩ (outputs product), terminal (outputs Unit),
--          curry (outputs function), fold (outputs Fix), arr (outputs Eff)
optimize-case-correct inl id x = refl
optimize-case-correct inl (g ∘ h) x = refl
optimize-case-correct inl fst x = refl
optimize-case-correct inl snd x = refl
optimize-case-correct inl inl x = refl
optimize-case-correct inl [ g , h ] x = refl
optimize-case-correct inl initial x = refl
optimize-case-correct inl apply x = refl
optimize-case-correct inl unfold x = refl

-- All other cases: no change (handle by first argument constructor)
optimize-case-correct id g x = refl
optimize-case-correct (f ∘ h) g x = refl
optimize-case-correct fst g x = refl
optimize-case-correct snd g x = refl
optimize-case-correct ⟨ f , h ⟩ g x = refl
optimize-case-correct inr g x = refl
optimize-case-correct [ f , h ] g x = refl
optimize-case-correct terminal g x = refl
optimize-case-correct initial g x = refl
optimize-case-correct (curry f) g x = refl
optimize-case-correct apply g x = refl
optimize-case-correct fold g x = refl
optimize-case-correct unfold g x = refl
optimize-case-correct arr g x = refl

------------------------------------------------------------------------
-- Correctness of optimize-once
------------------------------------------------------------------------

optimize-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                      → eval (optimize-once f) x ≡ eval f x
optimize-once-correct id x = refl
optimize-once-correct (g ∘ f) x =
  -- Step 1: optimize-compose-correct gives us:
  --   eval (optimize-compose (opt g) (opt f)) x ≡ eval ((opt g) ∘ (opt f)) x
  -- Step 2: This equals eval (opt g) (eval (opt f) x) by def of eval for ∘
  -- Step 3: Use IH on f: eval (opt f) x ≡ eval f x
  -- Step 4: Use IH on g with (eval f x): eval (opt g) (eval f x) ≡ eval g (eval f x)
  trans (optimize-compose-correct (optimize-once g) (optimize-once f) x)
        (trans (cong (eval (optimize-once g)) (optimize-once-correct f x))
               (optimize-once-correct g (eval f x)))
optimize-once-correct fst x = refl
optimize-once-correct snd x = refl
optimize-once-correct ⟨ f , g ⟩ x =
  trans (optimize-pair-correct (optimize-once f) (optimize-once g) x)
        (cong₂ _,_ (optimize-once-correct f x) (optimize-once-correct g x))
optimize-once-correct inl x = refl
optimize-once-correct inr x = refl
optimize-once-correct [ f , g ] x =
  trans (optimize-case-correct (optimize-once f) (optimize-once g) x)
        (lemma x)
  where
    lemma : (y : ⟦ _ + _ ⟧) → eval [ optimize-once f , optimize-once g ] y ≡ eval [ f , g ] y
    lemma (inj₁ a) = optimize-once-correct f a
    lemma (inj₂ b) = optimize-once-correct g b
optimize-once-correct terminal x = refl
optimize-once-correct initial ()
optimize-once-correct (curry f) x = cong (λ h → λ b → h (x , b)) (funext (λ p → optimize-once-correct f p))
  where
    -- POSTULATE: Function extensionality (see module header for justification)
    -- This is the ONLY postulate in the optimizer correctness proofs.
    postulate funext : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
optimize-once-correct apply x = refl
optimize-once-correct fold x = refl
optimize-once-correct unfold x = refl
optimize-once-correct arr x = refl

------------------------------------------------------------------------
-- Correctness of bounded optimization
------------------------------------------------------------------------

optimize-n-correct : ∀ {A B} (n : ℕ) (f : IR A B) (x : ⟦ A ⟧)
                   → eval (optimize-n n f) x ≡ eval f x
optimize-n-correct zero f x = refl
optimize-n-correct (suc n) f x =
  trans (optimize-n-correct n (optimize-once f) x)
        (optimize-once-correct f x)

------------------------------------------------------------------------
-- Main theorem: optimize preserves semantics
------------------------------------------------------------------------

optimize-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                 → eval (optimize f) x ≡ eval f x
optimize-correct f x = optimize-n-correct 10 f x
