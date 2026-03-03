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
open import Once.IR
open import Once.Semantics
open import Once.Optimize
open import Once.Category.Laws
open import Once.Postulates using (closure-semantics-eq; extensionality)

open import Data.Bool using (Bool; true; false; _∨_; _∧_)
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
--   - Case fusion: h ∘ [f,g] = [h∘f, h∘g]
--   - Associativity
------------------------------------------------------------------------

optimize-compose-correct : ∀ {A B C} (g : IR B C) (f : IR A B) (x : ⟦ A ⟧)
                         → eval (optimize-compose g f) x ≡ eval (g ∘ f) x

-- Left identity: id ∘ f = f
optimize-compose-correct id f x = refl

-- Initial: catch-all applies
optimize-compose-correct initial f x = refl

-- fst cases
optimize-compose-correct fst id x = refl
optimize-compose-correct fst (g' ∘ f') x = refl
optimize-compose-correct fst fst x = refl
optimize-compose-correct fst snd x = refl
optimize-compose-correct fst (⟨ f' , g' ⟩ _) x = refl  -- Product beta
optimize-compose-correct fst apply x = refl
optimize-compose-correct fst unfold x = refl
optimize-compose-correct fst initial ()  -- Initial absorption (Void is empty)
-- No distribution: fst ∘ [ f' , g' ] stays as fst ∘ [ f' , g' ]
optimize-compose-correct fst [ f' , g' ] x = refl
optimize-compose-correct fst (Prim name) x = refl

-- snd cases
optimize-compose-correct snd id x = refl
optimize-compose-correct snd (g' ∘ f') x = refl
optimize-compose-correct snd fst x = refl
optimize-compose-correct snd snd x = refl
optimize-compose-correct snd (⟨ f' , g' ⟩ _) x = refl  -- Product beta
optimize-compose-correct snd apply x = refl
optimize-compose-correct snd unfold x = refl
optimize-compose-correct snd initial ()  -- Initial absorption (Void is empty)
-- No distribution: snd ∘ [ f' , g' ] stays as snd ∘ [ f' , g' ]
optimize-compose-correct snd [ f' , g' ] x = refl
optimize-compose-correct snd (Prim name) x = refl

-- ⟨_,_⟩ cases - Conditional pairing distribution
-- Distribution only happens when it enables a beta reduction
optimize-compose-correct (⟨ f' , g' ⟩ _) id x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) initial ()  -- Initial absorption (Void is empty)
-- Cases where we DON'T distribute (no beta possible)
optimize-compose-correct (⟨ f' , g' ⟩ _) (h ∘ h') x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) fst x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) snd x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) [ h , h' ] x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) terminal x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) (curry h m) x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) apply x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) arr x = refl
optimize-compose-correct (⟨ f' , g' ⟩ _) (Prim name) x = refl
-- Cases where we CONDITIONALLY distribute (need to match optimizer's with-clause)
-- Distribution only happens when safe-pair-distrib returns true
optimize-compose-correct (⟨ f' , g' ⟩ m) (⟨ h , h' ⟩ m') x
  with safe-pair-distrib f' g'
... | true  = cong₂ _,_ (optimize-compose-correct f' (⟨ h , h' ⟩ m') x)
                        (optimize-compose-correct g' (⟨ h , h' ⟩ m') x)
... | false = refl
optimize-compose-correct (⟨ f' , g' ⟩ m) (inl m') x
  with safe-pair-distrib f' g'
... | true  = cong₂ _,_ (optimize-compose-correct f' (inl m') x)
                        (optimize-compose-correct g' (inl m') x)
... | false = refl
optimize-compose-correct (⟨ f' , g' ⟩ m) (inr m') x
  with safe-pair-distrib f' g'
... | true  = cong₂ _,_ (optimize-compose-correct f' (inr m') x)
                        (optimize-compose-correct g' (inr m') x)
... | false = refl
optimize-compose-correct (⟨ f' , g' ⟩ m) fold x
  with safe-pair-distrib f' g'
... | true  = cong₂ _,_ (optimize-compose-correct f' fold x)
                        (optimize-compose-correct g' fold x)
... | false = refl
optimize-compose-correct (⟨ f' , g' ⟩ m) unfold x
  with safe-pair-distrib f' g'
... | true  = cong₂ _,_ (optimize-compose-correct f' unfold x)
                        (optimize-compose-correct g' unfold x)
... | false = refl

-- inl cases - Case fusion: inl ∘ [ f' , g' ] = [ inl ∘ f' , inl ∘ g' ]
optimize-compose-correct (inl _) id x = refl
optimize-compose-correct (inl _) (g' ∘ f') x = refl
optimize-compose-correct (inl _) fst x = refl
optimize-compose-correct (inl _) snd x = refl
optimize-compose-correct (inl _) (⟨ f' , g' ⟩ _) x = refl
optimize-compose-correct (inl _) (inl _) x = refl
optimize-compose-correct (inl _) (inr _) x = refl
optimize-compose-correct (inl _) terminal x = refl
optimize-compose-correct (inl _) (curry f' _) x = refl
optimize-compose-correct (inl _) apply x = refl
optimize-compose-correct (inl _) fold x = refl
optimize-compose-correct (inl _) unfold x = refl
optimize-compose-correct (inl _) arr x = refl
optimize-compose-correct (inl _) initial ()  -- Initial absorption (Void is empty)
-- No distribution: inl ∘ [ f , g ] stays as inl ∘ [ f , g ]
optimize-compose-correct (inl _) [ _ , _ ] x = refl
optimize-compose-correct (inl _) (Prim name) x = refl

-- inr cases - Case fusion
optimize-compose-correct (inr _) id x = refl
optimize-compose-correct (inr _) (g' ∘ f') x = refl
optimize-compose-correct (inr _) fst x = refl
optimize-compose-correct (inr _) snd x = refl
optimize-compose-correct (inr _) (⟨ f' , g' ⟩ _) x = refl
optimize-compose-correct (inr _) (inl _) x = refl
optimize-compose-correct (inr _) (inr _) x = refl
optimize-compose-correct (inr _) terminal x = refl
optimize-compose-correct (inr _) (curry f' _) x = refl
optimize-compose-correct (inr _) apply x = refl
optimize-compose-correct (inr _) fold x = refl
optimize-compose-correct (inr _) unfold x = refl
optimize-compose-correct (inr _) arr x = refl
optimize-compose-correct (inr _) initial ()  -- Initial absorption (Void is empty)
-- No distribution: inr ∘ [ f , g ] stays as inr ∘ [ f , g ]
optimize-compose-correct (inr _) [ _ , _ ] x = refl
optimize-compose-correct (inr _) (Prim name) x = refl

-- [_,_] cases (coproduct beta laws)
optimize-compose-correct [ f' , g' ] id x = refl
optimize-compose-correct [ f' , g' ] (h ∘ h') x = refl
optimize-compose-correct [ f' , g' ] fst x = refl
optimize-compose-correct [ f' , g' ] snd x = refl
optimize-compose-correct [ f' , g' ] (inl _) x = refl  -- Coproduct beta
optimize-compose-correct [ f' , g' ] (inr _) x = refl  -- Coproduct beta
-- Case fusion was removed (can increase cost), so now returns h ∘ [ f , g ]
optimize-compose-correct [ f' , g' ] [ h , h' ] x = refl
optimize-compose-correct [ f' , g' ] apply x = refl
optimize-compose-correct [ f' , g' ] unfold x = refl
optimize-compose-correct [ f' , g' ] initial ()  -- Initial absorption (Void is empty)
optimize-compose-correct [ f' , g' ] (Prim name) x = refl

-- terminal cases (terminal fusion)
optimize-compose-correct terminal id x = refl
optimize-compose-correct terminal (g' ∘ f') x = refl
optimize-compose-correct terminal fst x = refl
optimize-compose-correct terminal snd x = refl
optimize-compose-correct terminal (⟨ f' , g' ⟩ _) x = refl
optimize-compose-correct terminal (inl _) x = refl
optimize-compose-correct terminal (inr _) x = refl
optimize-compose-correct terminal [ f' , g' ] x = refl
optimize-compose-correct terminal terminal x = refl
optimize-compose-correct terminal (curry f' _) x = refl
optimize-compose-correct terminal apply x = refl
optimize-compose-correct terminal fold x = refl
optimize-compose-correct terminal unfold x = refl
optimize-compose-correct terminal arr x = refl
optimize-compose-correct terminal initial ()  -- Void is empty
optimize-compose-correct terminal (Prim name) x = refl

-- curry cases - Case fusion: curry ∘ [ f' , g' ] = [ curry ∘ f' , curry ∘ g' ]
optimize-compose-correct (curry f' m) id x = refl
optimize-compose-correct (curry f' _) (g' ∘ h) x = refl
optimize-compose-correct (curry f' _) fst x = refl
optimize-compose-correct (curry f' _) snd x = refl
optimize-compose-correct (curry f' _) (⟨ g' , h ⟩ _) x = refl
optimize-compose-correct (curry f' _) (inl _) x = refl
optimize-compose-correct (curry f' _) (inr _) x = refl
optimize-compose-correct (curry f' _) terminal x = refl
optimize-compose-correct (curry f' _) (curry g' _) x = refl
optimize-compose-correct (curry f' _) apply x = refl
optimize-compose-correct (curry f' _) fold x = refl
optimize-compose-correct (curry f' _) unfold x = refl
optimize-compose-correct (curry f' _) arr x = refl
optimize-compose-correct (curry f' _) initial ()  -- Initial absorption (Void is empty)
-- No distribution: curry f ∘ [ g , h ] stays as curry f ∘ [ g , h ]
optimize-compose-correct (curry _ _) [ _ , _ ] x = refl
optimize-compose-correct (curry f' _) (Prim name) x = refl

-- apply cases
optimize-compose-correct apply id x = refl
optimize-compose-correct apply (g' ∘ f') x = refl
optimize-compose-correct apply fst x = refl
optimize-compose-correct apply snd x = refl
-- Exponential beta law: apply ∘ ⟨ curry f , g ⟩ = f ∘ ⟨ id , g ⟩
-- Eliminates closure allocation!
optimize-compose-correct apply (⟨ curry f' _ , g' ⟩ _) x = refl
-- apply with pair where first component is not curry (default case)
optimize-compose-correct apply (⟨ id , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ f' ∘ f'' , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ fst , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ snd , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ [ f' , f'' ] , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ initial , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ apply , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ unfold , g' ⟩ _) x = refl
optimize-compose-correct apply (⟨ Prim _ , g' ⟩ _) x = refl
optimize-compose-correct apply apply x = refl
optimize-compose-correct apply unfold x = refl
optimize-compose-correct apply initial ()  -- Initial absorption (Void is empty)
-- No distribution: apply ∘ [ f , g ] stays as apply ∘ [ f , g ]
optimize-compose-correct apply [ _ , _ ] x = refl
optimize-compose-correct apply (Prim name) x = refl

-- fold cases
optimize-compose-correct fold id x = refl
-- Fusion rule: fold ∘ (unfold ∘ f) = f
-- By associativity + identity: (fold ∘ unfold) ∘ f = id ∘ f = f
optimize-compose-correct fold (unfold ∘ f') x = refl
-- Other compositions (default case)
optimize-compose-correct fold (id ∘ f') x = refl
optimize-compose-correct fold ((g' ∘ g'') ∘ f') x = refl
optimize-compose-correct fold (fst ∘ f') x = refl
optimize-compose-correct fold (snd ∘ f') x = refl
optimize-compose-correct fold ((⟨ g' , g'' ⟩ _) ∘ f') x = refl
optimize-compose-correct fold ((inl _) ∘ f') x = refl
optimize-compose-correct fold ((inr _) ∘ f') x = refl
optimize-compose-correct fold ([ g' , g'' ] ∘ f') x = refl
optimize-compose-correct fold (terminal ∘ f') x = refl
optimize-compose-correct fold (initial ∘ f') x = refl
optimize-compose-correct fold ((curry g' _) ∘ f') x = refl
optimize-compose-correct fold (apply ∘ f') x = refl
optimize-compose-correct fold (fold ∘ f') x = refl
optimize-compose-correct fold (arr ∘ f') x = refl
optimize-compose-correct fold ((Prim _) ∘ f') x = refl
optimize-compose-correct fold fst x = refl
optimize-compose-correct fold snd x = refl
optimize-compose-correct fold (⟨ f' , g' ⟩ _) x = refl
optimize-compose-correct fold (inl _) x = refl
optimize-compose-correct fold (inr _) x = refl
optimize-compose-correct fold terminal x = refl
optimize-compose-correct fold (curry f' _) x = refl
optimize-compose-correct fold apply x = refl
optimize-compose-correct fold fold x = refl
optimize-compose-correct fold unfold x = refl  -- Fixed point law
optimize-compose-correct fold arr x = refl
optimize-compose-correct fold initial ()  -- Initial absorption (Void is empty)
-- No distribution: fold ∘ [ f , g ] stays as fold ∘ [ f , g ]
optimize-compose-correct fold [ _ , _ ] x = refl
optimize-compose-correct fold (Prim name) x = refl

-- unfold cases
optimize-compose-correct unfold id x = refl
-- Fusion rule: unfold ∘ (fold ∘ f) = f
-- By associativity + identity: (unfold ∘ fold) ∘ f = id ∘ f = f
optimize-compose-correct unfold (fold ∘ f') x = refl
-- Other compositions (default case)
optimize-compose-correct unfold (id ∘ f') x = refl
optimize-compose-correct unfold ((g' ∘ g'') ∘ f') x = refl
optimize-compose-correct unfold (fst ∘ f') x = refl
optimize-compose-correct unfold (snd ∘ f') x = refl
optimize-compose-correct unfold ([ g' , g'' ] ∘ f') x = refl
optimize-compose-correct unfold (initial ∘ f') x = refl
optimize-compose-correct unfold (apply ∘ f') x = refl
optimize-compose-correct unfold (unfold ∘ f') x = refl
optimize-compose-correct unfold ((Prim _) ∘ f') x = refl
optimize-compose-correct unfold fst x = refl
optimize-compose-correct unfold snd x = refl
optimize-compose-correct unfold apply x = refl
optimize-compose-correct unfold fold x = refl  -- Fixed point law
optimize-compose-correct unfold unfold x = refl
optimize-compose-correct unfold initial ()  -- Initial absorption (Void is empty)
-- No distribution: unfold ∘ [ f , g ] stays as unfold ∘ [ f , g ]
optimize-compose-correct unfold [ _ , _ ] x = refl
optimize-compose-correct unfold (Prim name) x = refl

-- arr cases
optimize-compose-correct arr id x = refl
optimize-compose-correct arr (g' ∘ f') x = refl
optimize-compose-correct arr fst x = refl
optimize-compose-correct arr snd x = refl
optimize-compose-correct arr (curry f' _) x = refl
optimize-compose-correct arr apply x = refl
optimize-compose-correct arr unfold x = refl
optimize-compose-correct arr initial ()  -- Initial absorption (Void is empty)
-- No distribution: arr ∘ [ f , g ] stays as arr ∘ [ f , g ]
optimize-compose-correct arr [ _ , _ ] x = refl
optimize-compose-correct arr (Prim name) x = refl

-- Associativity: (h ∘ g) ∘ f → optimize h (optimize g f)
optimize-compose-correct (h ∘ g) id x = refl
optimize-compose-correct (h ∘ g) initial ()  -- Initial absorption (Void is empty)
optimize-compose-correct (h ∘ g) (f' ∘ f'') x =
  trans (optimize-compose-correct h (optimize-compose g (f' ∘ f'')) x)
        (cong (eval h) (optimize-compose-correct g (f' ∘ f'') x))
optimize-compose-correct (h ∘ g) fst x =
  trans (optimize-compose-correct h (optimize-compose g fst) x)
        (cong (eval h) (optimize-compose-correct g fst x))
optimize-compose-correct (h ∘ g) snd x =
  trans (optimize-compose-correct h (optimize-compose g snd) x)
        (cong (eval h) (optimize-compose-correct g snd x))
optimize-compose-correct (h ∘ g) (⟨ f' , f'' ⟩ m) x =
  trans (optimize-compose-correct h (optimize-compose g (⟨ f' , f'' ⟩ m)) x)
        (cong (eval h) (optimize-compose-correct g (⟨ f' , f'' ⟩ m) x))
optimize-compose-correct (h ∘ g) (inl m) x =
  trans (optimize-compose-correct h (optimize-compose g (inl m)) x)
        (cong (eval h) (optimize-compose-correct g (inl m) x))
optimize-compose-correct (h ∘ g) (inr m) x =
  trans (optimize-compose-correct h (optimize-compose g (inr m)) x)
        (cong (eval h) (optimize-compose-correct g (inr m) x))
-- No distribution for (h ∘ g) ∘ [ f , f' ] - the default case matches first
optimize-compose-correct (_ ∘ _) [ _ , _ ] x = refl
optimize-compose-correct (h ∘ g) terminal x =
  trans (optimize-compose-correct h (optimize-compose g terminal) x)
        (cong (eval h) (optimize-compose-correct g terminal x))
optimize-compose-correct (h ∘ g) (curry f' m) x =
  trans (optimize-compose-correct h (optimize-compose g (curry f' m)) x)
        (cong (eval h) (optimize-compose-correct g (curry f' m) x))
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
optimize-compose-correct (h ∘ g) (Prim name) x =
  trans (optimize-compose-correct h (optimize-compose g (Prim name)) x)
        (cong (eval h) (optimize-compose-correct g (Prim name) x))

-- Prim cases (primitives are opaque)
optimize-compose-correct (Prim name) id x = refl
optimize-compose-correct (Prim name) (g' ∘ f') x = refl
optimize-compose-correct (Prim name) fst x = refl
optimize-compose-correct (Prim name) snd x = refl
optimize-compose-correct (Prim name) (⟨ f' , g' ⟩ _) x = refl
optimize-compose-correct (Prim name) (inl _) x = refl
optimize-compose-correct (Prim name) (inr _) x = refl
optimize-compose-correct (Prim name) terminal x = refl
optimize-compose-correct (Prim name) (curry f' _) x = refl
optimize-compose-correct (Prim name) apply x = refl
optimize-compose-correct (Prim name) fold x = refl
optimize-compose-correct (Prim name) unfold x = refl
optimize-compose-correct (Prim name) arr x = refl
optimize-compose-correct (Prim name) initial ()
-- No distribution: Prim ∘ [ f , g ] stays as Prim ∘ [ f , g ]
optimize-compose-correct (Prim _) [ _ , _ ] x = refl
optimize-compose-correct (Prim name) (Prim name') x = refl

------------------------------------------------------------------------
-- Correctness of optimize-pair
------------------------------------------------------------------------

optimize-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
                      → eval (optimize-pair f g) x ≡ eval (⟨ f , g ⟩ Heap) x

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
optimize-pair-correct fst fold x = refl
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
optimize-pair-correct (fst ∘ h) [ g , g' ] x = refl
optimize-pair-correct (fst ∘ h) terminal x = refl
optimize-pair-correct (fst ∘ h) (curry g _) x = refl
optimize-pair-correct (fst ∘ h) apply x = refl
optimize-pair-correct (fst ∘ h) fold x = refl
optimize-pair-correct (fst ∘ h) unfold x = refl
optimize-pair-correct (fst ∘ h) arr x = refl
-- Non-snd composition
optimize-pair-correct (fst ∘ h) (id ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (fst ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((inl _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((inr _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ([ f , g ] ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (terminal ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((f ∘ f') ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((⟨ f , g ⟩ _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((curry f _) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (apply ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (fold ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (unfold ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (arr ∘ g') x = refl
optimize-pair-correct (fst ∘ h) (initial ∘ g') x = refl
optimize-pair-correct (fst ∘ h) ((Prim name) ∘ g') x = refl
optimize-pair-correct (fst ∘ h) initial x = refl
optimize-pair-correct (fst ∘ h) (Prim name) x = refl

-- All other cases (non-fst first argument)
optimize-pair-correct id g x = refl
optimize-pair-correct (id ∘ h) g x = refl
optimize-pair-correct (snd ∘ h) g x = refl
optimize-pair-correct ((inl _) ∘ h) g x = refl
optimize-pair-correct ((inr _) ∘ h) g x = refl
optimize-pair-correct ([ f , f' ] ∘ h) g x = refl
optimize-pair-correct (terminal ∘ h) g x = refl
optimize-pair-correct ((f ∘ f') ∘ h) g x = refl
optimize-pair-correct ((⟨ f , f' ⟩ _) ∘ h) g x = refl
optimize-pair-correct ((curry f _) ∘ h) g x = refl
optimize-pair-correct (apply ∘ h) g x = refl
optimize-pair-correct (fold ∘ h) g x = refl
optimize-pair-correct (unfold ∘ h) g x = refl
optimize-pair-correct (arr ∘ h) g x = refl
-- initial composition cases
optimize-pair-correct (initial ∘ h) g x = refl
optimize-pair-correct ((Prim name) ∘ h) g x = refl
optimize-pair-correct snd g x = refl
optimize-pair-correct (⟨ f , h ⟩ _) g x = refl
optimize-pair-correct (inl _) g x = refl
optimize-pair-correct (inr _) g x = refl
optimize-pair-correct [ f , h ] g x = refl
optimize-pair-correct terminal g x = refl
optimize-pair-correct (curry f _) g x = refl
optimize-pair-correct apply g x = refl
optimize-pair-correct fold g x = refl
optimize-pair-correct unfold g x = refl
optimize-pair-correct arr g x = refl
optimize-pair-correct initial g x = refl
optimize-pair-correct (Prim name) g x = refl

------------------------------------------------------------------------
-- Correctness of optimize-case
------------------------------------------------------------------------

optimize-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧)
                      → eval (optimize-case f g) x ≡ eval [ f , g ] x

-- Eta law: [ inl , inr ] = id
-- Note: AllocModes m and m' may differ but semantics are the same (mode is transparent)
optimize-case-correct (inl {A} {B} m) (inr {A'} {B'} m') x with A ≟Type A' | B ≟Type B'
... | yes refl | yes refl = sym (lemma x)
  where
    -- AllocMode doesn't affect semantics of inl/inr
    lemma : (y : ⟦ A + B ⟧) → eval [ inl m , inr m' ] y ≡ y
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
optimize-case-correct (inl _) [ g , h ] x = refl
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
    lemma : (y : ⟦ A + B ⟧) → eval [ h ∘ inl m , h ∘ inr m' ] y ≡ eval h y
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
optimize-case-correct (h ∘ (inl _)) [ g₁ , g₂ ] x = refl
optimize-case-correct (h ∘ (inl _)) terminal x = refl
optimize-case-correct (h ∘ (inl _)) initial x = refl
optimize-case-correct (h ∘ (inl _)) (curry g _) x = refl
optimize-case-correct (h ∘ (inl _)) apply x = refl
optimize-case-correct (h ∘ (inl _)) fold x = refl
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
optimize-case-correct (h ∘ (inl _)) (g ∘ [ g₁ , g₂ ]) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ terminal) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ initial) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ (curry g' _)) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ apply) x = refl
optimize-case-correct (h ∘ (inl _)) (g ∘ fold) x = refl
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
optimize-case-correct (f ∘ [ f₁ , f₂ ]) g x = refl
optimize-case-correct (f ∘ terminal) g x = refl
optimize-case-correct (f ∘ initial) g x = refl
optimize-case-correct (f ∘ (curry f' _)) g x = refl
optimize-case-correct (f ∘ apply) g x = refl
optimize-case-correct (f ∘ fold) g x = refl
optimize-case-correct (f ∘ unfold) g x = refl
optimize-case-correct (f ∘ arr) g x = refl
optimize-case-correct (f ∘ Prim name) g x = refl
optimize-case-correct id g x = refl
optimize-case-correct fst g x = refl
optimize-case-correct snd g x = refl
optimize-case-correct (⟨ f , h ⟩ _) g x = refl
optimize-case-correct (inr _) g x = refl
optimize-case-correct [ f , h ] g x = refl
optimize-case-correct terminal g x = refl
optimize-case-correct initial g x = refl
optimize-case-correct (curry f _) g x = refl
optimize-case-correct apply g x = refl
optimize-case-correct fold g x = refl
optimize-case-correct unfold g x = refl
optimize-case-correct arr g x = refl
optimize-case-correct (Prim name) g x = refl

------------------------------------------------------------------------
-- Correctness of optimize-once
------------------------------------------------------------------------

optimize-once-correct : ∀ {A B} (f : IR A B) (x : ⟦ A ⟧)
                      → eval (optimize-once f) x ≡ eval f x
optimize-once-correct id x = refl
optimize-once-correct (g ∘ f) x =
  trans (optimize-compose-correct (optimize-once g) (optimize-once f) x)
        (trans (cong (eval (optimize-once g)) (optimize-once-correct f x))
               (optimize-once-correct g (eval f x)))
optimize-once-correct fst x = refl
optimize-once-correct snd x = refl
optimize-once-correct (⟨ f , g ⟩ _) x =
  trans (optimize-pair-correct (optimize-once f) (optimize-once g) x)
        (cong₂ _,_ (optimize-once-correct f x) (optimize-once-correct g x))
optimize-once-correct (inl _) x = refl
optimize-once-correct (inr _) x = refl
optimize-once-correct [ f , g ] x =
  trans (optimize-case-correct (optimize-once f) (optimize-once g) x)
        (lemma x)
  where
    lemma : (y : ⟦ _ + _ ⟧) → eval [ optimize-once f , optimize-once g ] y ≡ eval [ f , g ] y
    lemma (inj₁ a) = optimize-once-correct f a
    lemma (inj₂ b) = optimize-once-correct g b
optimize-once-correct terminal x = refl
optimize-once-correct initial ()
optimize-once-correct (curry {q = q} f _) x =
  closure-semantics-eq
    (eval (curry {q = q} (optimize-once f) Heap) x)
    (eval (curry {q = q} f Heap) x)
    (funext (λ b → optimize-once-correct f (x , b)))
optimize-once-correct apply x = refl
optimize-once-correct fold x = refl
optimize-once-correct unfold x = refl
optimize-once-correct arr x = refl
optimize-once-correct (Prim name) x = refl

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
