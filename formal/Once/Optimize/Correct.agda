------------------------------------------------------------------------
-- Once.Optimize.Correct
--
-- Correctness proofs for the Once optimizer.
-- Each optimization rule preserves semantics.
--
-- Uses function extensionality (imported from Once.Postulates) for the
-- curry case, which requires proving equality of functions.
------------------------------------------------------------------------

open import Once.Backend.MachineInterface
open import Once.Contract

module Once.Optimize.Correct
  (MI : MachineInterface)
  (CI : ContractInterface)
  where

open import Once.Type
open import Once.SemanticBaseMachine MI
open import Once.IR as IRM
open import Once.Semantics MI CI
open import Once.Optimize CI
open import Once.Category.Laws MI CI

open IRM.IRDef CI

module Correct (CS : ContractSemantics CI ⟦_⟧) where
  open SemanticsDef CS
  open Laws CS

  open import Once.Postulates ⟦_⟧ IR Closure Closure.semantics encode eval
    using (closure-semantics-eq; extensionality)

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
  optimize-compose-correct fst ⟨ f' , g' ⟩ x = refl  -- Product beta
  optimize-compose-correct fst apply x = refl
  optimize-compose-correct fst unfold x = refl
  optimize-compose-correct fst initial ()  -- Initial absorption (Void is empty)
  -- Case fusion: fst ∘ [ f' , g' ] = [ fst ∘ f' , fst ∘ g' ]
  optimize-compose-correct fst [ f' , g' ] (inj₁ a) = optimize-compose-correct fst f' a
  optimize-compose-correct fst [ f' , g' ] (inj₂ b) = optimize-compose-correct fst g' b
  optimize-compose-correct fst (Prim name _) x = refl

  -- snd cases
  optimize-compose-correct snd id x = refl
  optimize-compose-correct snd (g' ∘ f') x = refl
  optimize-compose-correct snd fst x = refl
  optimize-compose-correct snd snd x = refl
  optimize-compose-correct snd ⟨ f' , g' ⟩ x = refl  -- Product beta
  optimize-compose-correct snd apply x = refl
  optimize-compose-correct snd unfold x = refl
  optimize-compose-correct snd initial ()  -- Initial absorption (Void is empty)
  -- Case fusion: snd ∘ [ f' , g' ] = [ snd ∘ f' , snd ∘ g' ]
  optimize-compose-correct snd [ f' , g' ] (inj₁ a) = optimize-compose-correct snd f' a
  optimize-compose-correct snd [ f' , g' ] (inj₂ b) = optimize-compose-correct snd g' b
  optimize-compose-correct snd (Prim name _) x = refl

  -- ⟨_,_⟩ cases - Pairing fusion: ⟨f,g⟩ ∘ h = ⟨f∘h, g∘h⟩
  optimize-compose-correct ⟨ f' , g' ⟩ id x = refl
  optimize-compose-correct ⟨ f' , g' ⟩ initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct ⟨ f' , g' ⟩ (h ∘ h') x =
    cong₂ _,_ (optimize-compose-correct f' (h ∘ h') x) (optimize-compose-correct g' (h ∘ h') x)
  optimize-compose-correct ⟨ f' , g' ⟩ fst x =
    cong₂ _,_ (optimize-compose-correct f' fst x) (optimize-compose-correct g' fst x)
  optimize-compose-correct ⟨ f' , g' ⟩ snd x =
    cong₂ _,_ (optimize-compose-correct f' snd x) (optimize-compose-correct g' snd x)
  optimize-compose-correct ⟨ f' , g' ⟩ ⟨ h , h' ⟩ x =
    cong₂ _,_ (optimize-compose-correct f' ⟨ h , h' ⟩ x) (optimize-compose-correct g' ⟨ h , h' ⟩ x)
  optimize-compose-correct ⟨ f' , g' ⟩ inl x =
    cong₂ _,_ (optimize-compose-correct f' inl x) (optimize-compose-correct g' inl x)
  optimize-compose-correct ⟨ f' , g' ⟩ inr x =
    cong₂ _,_ (optimize-compose-correct f' inr x) (optimize-compose-correct g' inr x)
  optimize-compose-correct ⟨ f' , g' ⟩ [ h , h' ] x =
    cong₂ _,_ (optimize-compose-correct f' [ h , h' ] x) (optimize-compose-correct g' [ h , h' ] x)
  optimize-compose-correct ⟨ f' , g' ⟩ terminal x =
    cong₂ _,_ (optimize-compose-correct f' terminal x) (optimize-compose-correct g' terminal x)
  optimize-compose-correct ⟨ f' , g' ⟩ (curry h) x =
    cong₂ _,_ (optimize-compose-correct f' (curry h) x) (optimize-compose-correct g' (curry h) x)
  optimize-compose-correct ⟨ f' , g' ⟩ apply x =
    cong₂ _,_ (optimize-compose-correct f' apply x) (optimize-compose-correct g' apply x)
  optimize-compose-correct ⟨ f' , g' ⟩ fold x =
    cong₂ _,_ (optimize-compose-correct f' fold x) (optimize-compose-correct g' fold x)
  optimize-compose-correct ⟨ f' , g' ⟩ unfold x =
    cong₂ _,_ (optimize-compose-correct f' unfold x) (optimize-compose-correct g' unfold x)
  optimize-compose-correct ⟨ f' , g' ⟩ arr x =
    cong₂ _,_ (optimize-compose-correct f' arr x) (optimize-compose-correct g' arr x)
  optimize-compose-correct ⟨ f' , g' ⟩ (Prim name _) x =
    cong₂ _,_ (optimize-compose-correct f' (Prim name _) x) (optimize-compose-correct g' (Prim name _) x)

  -- inl cases - Case fusion: inl ∘ [ f' , g' ] = [ inl ∘ f' , inl ∘ g' ]
  optimize-compose-correct inl id x = refl
  optimize-compose-correct inl (g' ∘ f') x = refl
  optimize-compose-correct inl fst x = refl
  optimize-compose-correct inl snd x = refl
  optimize-compose-correct inl ⟨ f' , g' ⟩ x = refl
  optimize-compose-correct inl inl x = refl
  optimize-compose-correct inl inr x = refl
  optimize-compose-correct inl terminal x = refl
  optimize-compose-correct inl (curry f') x = refl
  optimize-compose-correct inl apply x = refl
  optimize-compose-correct inl fold x = refl
  optimize-compose-correct inl unfold x = refl
  optimize-compose-correct inl arr x = refl
  optimize-compose-correct inl initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct inl [ f' , g' ] (inj₁ a) = optimize-compose-correct inl f' a
  optimize-compose-correct inl [ f' , g' ] (inj₂ b) = optimize-compose-correct inl g' b
  optimize-compose-correct inl (Prim name _) x = refl

  -- inr cases - Case fusion
  optimize-compose-correct inr id x = refl
  optimize-compose-correct inr (g' ∘ f') x = refl
  optimize-compose-correct inr fst x = refl
  optimize-compose-correct inr snd x = refl
  optimize-compose-correct inr ⟨ f' , g' ⟩ x = refl
  optimize-compose-correct inr inl x = refl
  optimize-compose-correct inr inr x = refl
  optimize-compose-correct inr terminal x = refl
  optimize-compose-correct inr (curry f') x = refl
  optimize-compose-correct inr apply x = refl
  optimize-compose-correct inr fold x = refl
  optimize-compose-correct inr unfold x = refl
  optimize-compose-correct inr arr x = refl
  optimize-compose-correct inr initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct inr [ f' , g' ] (inj₁ a) = optimize-compose-correct inr f' a
  optimize-compose-correct inr [ f' , g' ] (inj₂ b) = optimize-compose-correct inr g' b
  optimize-compose-correct inr (Prim name _) x = refl

  -- [_,_] cases (coproduct beta laws)
  optimize-compose-correct [ f' , g' ] id x = refl
  optimize-compose-correct [ f' , g' ] (h ∘ h') x = refl
  optimize-compose-correct [ f' , g' ] fst x = refl
  optimize-compose-correct [ f' , g' ] snd x = refl
  optimize-compose-correct [ f' , g' ] inl x = refl  -- Coproduct beta
  optimize-compose-correct [ f' , g' ] inr x = refl  -- Coproduct beta
  optimize-compose-correct [ f' , g' ] [ h , h' ] x = refl
  optimize-compose-correct [ f' , g' ] apply x = refl
  optimize-compose-correct [ f' , g' ] unfold x = refl
  optimize-compose-correct [ f' , g' ] initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct [ f' , g' ] (Prim name _) x = refl

  -- terminal cases (terminal fusion)
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
  optimize-compose-correct terminal initial ()  -- Void is empty
  optimize-compose-correct terminal (Prim name _) x = refl

  -- curry cases - Case fusion: curry ∘ [ f' , g' ] = [ curry ∘ f' , curry ∘ g' ]
  optimize-compose-correct (curry f') id x = refl
  optimize-compose-correct (curry f') (g' ∘ h) x = refl
  optimize-compose-correct (curry f') fst x = refl
  optimize-compose-correct (curry f') snd x = refl
  optimize-compose-correct (curry f') ⟨ g' , h ⟩ x = refl
  optimize-compose-correct (curry f') inl x = refl
  optimize-compose-correct (curry f') inr x = refl
  optimize-compose-correct (curry f') terminal x = refl
  optimize-compose-correct (curry f') (curry g') x = refl
  optimize-compose-correct (curry f') apply x = refl
  optimize-compose-correct (curry f') fold x = refl
  optimize-compose-correct (curry f') unfold x = refl
  optimize-compose-correct (curry f') arr x = refl
  optimize-compose-correct (curry f') initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct (curry f') [ g' , h ] (inj₁ a) = optimize-compose-correct (curry f') g' a
  optimize-compose-correct (curry f') [ g' , h ] (inj₂ b) = optimize-compose-correct (curry f') h b
  optimize-compose-correct (curry f') (Prim name _) x = refl

  -- apply cases
  optimize-compose-correct apply id x = refl
  optimize-compose-correct apply (g' ∘ f') x = refl
  optimize-compose-correct apply fst x = refl
  optimize-compose-correct apply snd x = refl
  optimize-compose-correct apply ⟨ f' , g' ⟩ x = refl
  optimize-compose-correct apply apply x = refl
  optimize-compose-correct apply unfold x = refl
  optimize-compose-correct apply initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct apply [ f' , g' ] (inj₁ a) = optimize-compose-correct apply f' a
  optimize-compose-correct apply [ f' , g' ] (inj₂ b) = optimize-compose-correct apply g' b
  optimize-compose-correct apply (Prim name _) x = refl

  -- fold cases
  optimize-compose-correct fold id x = refl
  optimize-compose-correct fold (g' ∘ f') x = refl
  optimize-compose-correct fold fst x = refl
  optimize-compose-correct fold snd x = refl
  optimize-compose-correct fold ⟨ f' , g' ⟩ x = refl
  optimize-compose-correct fold inl x = refl
  optimize-compose-correct fold inr x = refl
  optimize-compose-correct fold terminal x = refl
  optimize-compose-correct fold (curry f') x = refl
  optimize-compose-correct fold apply x = refl
  optimize-compose-correct fold fold x = refl
  optimize-compose-correct fold unfold x = refl  -- Fixed point law
  optimize-compose-correct fold arr x = refl
  optimize-compose-correct fold initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct fold [ f' , g' ] (inj₁ a) = optimize-compose-correct fold f' a
  optimize-compose-correct fold [ f' , g' ] (inj₂ b) = optimize-compose-correct fold g' b
  optimize-compose-correct fold (Prim name _) x = refl

  -- unfold cases
  optimize-compose-correct unfold id x = refl
  optimize-compose-correct unfold (g' ∘ f') x = refl
  optimize-compose-correct unfold fst x = refl
  optimize-compose-correct unfold snd x = refl
  optimize-compose-correct unfold apply x = refl
  optimize-compose-correct unfold fold x = refl  -- Fixed point law
  optimize-compose-correct unfold unfold x = refl
  optimize-compose-correct unfold initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct unfold [ f' , g' ] (inj₁ a) = optimize-compose-correct unfold f' a
  optimize-compose-correct unfold [ f' , g' ] (inj₂ b) = optimize-compose-correct unfold g' b
  optimize-compose-correct unfold (Prim name _) x = refl

  -- arr cases
  optimize-compose-correct arr id x = refl
  optimize-compose-correct arr (g' ∘ f') x = refl
  optimize-compose-correct arr fst x = refl
  optimize-compose-correct arr snd x = refl
  optimize-compose-correct arr (curry f') x = refl
  optimize-compose-correct arr apply x = refl
  optimize-compose-correct arr unfold x = refl
  optimize-compose-correct arr initial ()  -- Initial absorption (Void is empty)
  optimize-compose-correct arr [ f' , g' ] (inj₁ a) = optimize-compose-correct arr f' a
  optimize-compose-correct arr [ f' , g' ] (inj₂ b) = optimize-compose-correct arr g' b
  optimize-compose-correct arr (Prim name _) x = refl

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
  optimize-compose-correct (h ∘ g) (Prim name _) x =
    trans (optimize-compose-correct h (optimize-compose g (Prim name _)) x)
          (cong (eval h) (optimize-compose-correct g (Prim name _) x))

  -- Prim cases (primitives are opaque)
  optimize-compose-correct (Prim name _) id x = refl
  optimize-compose-correct (Prim name _) (g' ∘ f') x = refl
  optimize-compose-correct (Prim name _) fst x = refl
  optimize-compose-correct (Prim name _) snd x = refl
  optimize-compose-correct (Prim name _) ⟨ f' , g' ⟩ x = refl
  optimize-compose-correct (Prim name _) inl x = refl
  optimize-compose-correct (Prim name _) inr x = refl
  optimize-compose-correct (Prim name _) terminal x = refl
  optimize-compose-correct (Prim name _) (curry f') x = refl
  optimize-compose-correct (Prim name _) apply x = refl
  optimize-compose-correct (Prim name _) fold x = refl
  optimize-compose-correct (Prim name _) unfold x = refl
  optimize-compose-correct (Prim name _) arr x = refl
  optimize-compose-correct (Prim name _) initial ()
  optimize-compose-correct (Prim name _) [ f' , g' ] (inj₁ a) = optimize-compose-correct (Prim name _) f' a
  optimize-compose-correct (Prim name _) [ f' , g' ] (inj₂ b) = optimize-compose-correct (Prim name _) g' b
  optimize-compose-correct (Prim name _) (Prim name' _) x = refl


  ------------------------------------------------------------------------
  -- Correctness of optimize-pair
  ------------------------------------------------------------------------

  optimize-pair-correct : ∀ {A B C} (f : IR C A) (g : IR C B) (x : ⟦ C ⟧)
                        → eval (optimize-pair f g) x ≡ eval ⟨ f , g ⟩ x

  -- Eta law: ⟨ fst , snd ⟩ = id
  optimize-pair-correct (fst {A} {B}) (snd {A'} {B'}) x with A ≟Type A' | B ≟Type B'
  ... | yes refl | yes refl = sym (eval-pair-eta x)
  ... | yes refl | no _     = refl
  ... | no _     | yes _    = refl
  ... | no _     | no _     = refl

  -- All other fst cases (non-snd second argument)
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
  optimize-pair-correct fst (Prim name _) x = refl

  -- Uniqueness: ⟨ fst ∘ h , snd ∘ h' ⟩ cases
  optimize-pair-correct (_∘_ {_} {D} {_} (fst {A} {B}) h) (_∘_ {_} {D'} {_} (snd {A'} {B'}) h') x
    with A ≟Type A' | B ≟Type B' | D ≟Type D'
  optimize-pair-correct (_∘_ (fst {A} {B}) h) (_∘_ (snd {.A} {.B}) h') x
    | yes refl | yes refl | yes refl with h ≟IR h'
  ...   | yes refl = sym (eval-pair-unique h x)  -- Use uniqueness law
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
  optimize-pair-correct (fst ∘ h) ⟨ g , g' ⟩ x = refl
  optimize-pair-correct (fst ∘ h) inl x = refl
  optimize-pair-correct (fst ∘ h) inr x = refl
  optimize-pair-correct (fst ∘ h) [ g , g' ] x = refl
  optimize-pair-correct (fst ∘ h) terminal x = refl
  optimize-pair-correct (fst ∘ h) (curry g) x = refl
  optimize-pair-correct (fst ∘ h) apply x = refl
  optimize-pair-correct (fst ∘ h) fold x = refl
  optimize-pair-correct (fst ∘ h) unfold x = refl
  optimize-pair-correct (fst ∘ h) arr x = refl
  -- Non-snd composition
  optimize-pair-correct (fst ∘ h) (id ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (fst ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (inl ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (inr ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) ([ f , g ] ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (terminal ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) ((f ∘ f') ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (⟨ f , g ⟩ ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) ((curry f) ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (apply ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (fold ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (unfold ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (arr ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) (initial ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) ((Prim name _) ∘ g') x = refl
  optimize-pair-correct (fst ∘ h) initial x = refl
  optimize-pair-correct (fst ∘ h) (Prim name _) x = refl

  -- All other cases (non-fst first argument)
  optimize-pair-correct id g x = refl
  optimize-pair-correct (id ∘ h) g x = refl
  optimize-pair-correct (snd ∘ h) g x = refl
  optimize-pair-correct (inl ∘ h) g x = refl
  optimize-pair-correct (inr ∘ h) g x = refl
  optimize-pair-correct ([ f , f' ] ∘ h) g x = refl
  optimize-pair-correct (terminal ∘ h) g x = refl
  optimize-pair-correct ((f ∘ f') ∘ h) g x = refl
  optimize-pair-correct (⟨ f , f' ⟩ ∘ h) g x = refl
  optimize-pair-correct ((curry f) ∘ h) g x = refl
  optimize-pair-correct (apply ∘ h) g x = refl
  optimize-pair-correct (fold ∘ h) g x = refl
  optimize-pair-correct (unfold ∘ h) g x = refl
  optimize-pair-correct (arr ∘ h) g x = refl
  -- initial composition cases
  optimize-pair-correct (initial ∘ h) g x = refl
  optimize-pair-correct ((Prim name _) ∘ h) g x = refl
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
  optimize-pair-correct initial g x = refl
  optimize-pair-correct (Prim name _) g x = refl

  ------------------------------------------------------------------------
  -- Correctness of optimize-case
  ------------------------------------------------------------------------

  optimize-case-correct : ∀ {A B C} (f : IR A C) (g : IR B C) (x : ⟦ A + B ⟧)
                        → eval (optimize-case f g) x ≡ eval [ f , g ] x

  -- Eta law: [ inl , inr ] = id
  optimize-case-correct (inl {A} {B}) (inr {A'} {B'}) x with A ≟Type A' | B ≟Type B'
  ... | yes refl | yes refl = sym (eval-case-eta x)
  ... | yes refl | no _     = refl
  ... | no _     | yes _    = refl
  ... | no _     | no _     = refl

  -- All other inl cases
  optimize-case-correct inl id x = refl
  optimize-case-correct inl (g ∘ h) x = refl
  optimize-case-correct inl fst x = refl
  optimize-case-correct inl snd x = refl
  optimize-case-correct inl inl x = refl
  optimize-case-correct inl [ g , h ] x = refl
  optimize-case-correct inl initial x = refl
  optimize-case-correct inl apply x = refl
  optimize-case-correct inl unfold x = refl
  optimize-case-correct inl (Prim name _) x = refl

  -- Uniqueness: [ h ∘ inl , h' ∘ inr ] cases
  optimize-case-correct (_∘_ {_} {D} {_} h (inl {A} {B})) (_∘_ {_} {D'} {_} h' (inr {A'} {B'})) x
    with A ≟Type A' | B ≟Type B' | D ≟Type D'
  optimize-case-correct (_∘_ h (inl {A} {B})) (_∘_ h' (inr {.A} {.B})) x
    | yes refl | yes refl | yes refl with h ≟IR h'
  ...   | yes refl = sym (eval-case-unique h x)  -- Use uniqueness law
  ...   | no _     = refl
  optimize-case-correct (_∘_ h (inl {A} {B})) (_∘_ h' (inr {.A} {.B})) x
    | yes refl | yes refl | no _  = refl
  optimize-case-correct (_∘_ h (inl {A} {B})) (_∘_ h' (inr {.A} {B'})) x
    | yes refl | no _  | _     = refl
  optimize-case-correct (_∘_ h (inl {A} {B})) (_∘_ h' (inr {A'} {B'})) x
    | no _  | _     | _     = refl

  -- h ∘ inl with second arg NOT of form h' ∘ inr
  -- Non-compositions
  optimize-case-correct (h ∘ inl) id x = refl
  optimize-case-correct (h ∘ inl) fst x = refl
  optimize-case-correct (h ∘ inl) snd x = refl
  optimize-case-correct (h ∘ inl) ⟨ g₁ , g₂ ⟩ x = refl
  optimize-case-correct (h ∘ inl) inl x = refl
  optimize-case-correct (h ∘ inl) inr x = refl
  optimize-case-correct (h ∘ inl) [ g₁ , g₂ ] x = refl
  optimize-case-correct (h ∘ inl) terminal x = refl
  optimize-case-correct (h ∘ inl) initial x = refl
  optimize-case-correct (h ∘ inl) (curry g) x = refl
  optimize-case-correct (h ∘ inl) apply x = refl
  optimize-case-correct (h ∘ inl) fold x = refl
  optimize-case-correct (h ∘ inl) unfold x = refl
  optimize-case-correct (h ∘ inl) arr x = refl
  -- Compositions NOT ending in inr
  optimize-case-correct (h ∘ inl) (g ∘ id) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ fst) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ snd) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ (g' ∘ g'')) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ ⟨ g₁ , g₂ ⟩) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ inl) x = refl
  -- g ∘ inr is handled by uniqueness case above
  optimize-case-correct (h ∘ inl) (g ∘ [ g₁ , g₂ ]) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ terminal) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ initial) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ curry g') x = refl
  optimize-case-correct (h ∘ inl) (g ∘ apply) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ fold) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ unfold) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ arr) x = refl
  optimize-case-correct (h ∘ inl) (g ∘ Prim name _) x = refl
  optimize-case-correct (h ∘ inl) (Prim name _) x = refl

  -- All other first arg cases (not inl at end)
  optimize-case-correct (f ∘ id) g x = refl
  optimize-case-correct (f ∘ fst) g x = refl
  optimize-case-correct (f ∘ snd) g x = refl
  optimize-case-correct (f ∘ (f' ∘ f'')) g x = refl
  optimize-case-correct (f ∘ ⟨ f₁ , f₂ ⟩) g x = refl
  -- f ∘ inl is handled above
  optimize-case-correct (f ∘ inr) g x = refl
  optimize-case-correct (f ∘ [ f₁ , f₂ ]) g x = refl
  optimize-case-correct (f ∘ terminal) g x = refl
  optimize-case-correct (f ∘ initial) g x = refl
  optimize-case-correct (f ∘ curry f') g x = refl
  optimize-case-correct (f ∘ apply) g x = refl
  optimize-case-correct (f ∘ fold) g x = refl
  optimize-case-correct (f ∘ unfold) g x = refl
  optimize-case-correct (f ∘ arr) g x = refl
  optimize-case-correct (f ∘ Prim name _) g x = refl
  optimize-case-correct id g x = refl
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
  optimize-case-correct (Prim name _) g x = refl

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
  optimize-once-correct (curry f) x =
    closure-semantics-eq
      (eval (curry (optimize-once f)) x)
      (eval (curry f) x)
      (funext (λ b → optimize-once-correct f (x , b)))
  optimize-once-correct apply x = refl
  optimize-once-correct fold x = refl
  optimize-once-correct unfold x = refl
  optimize-once-correct arr x = refl
  optimize-once-correct (Prim name _) x = refl

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
