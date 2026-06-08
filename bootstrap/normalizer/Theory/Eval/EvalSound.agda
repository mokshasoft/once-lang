------------------------------------------------------------------------
-- normalizer.Theory.Eval.EvalSound
--
-- The evaluator is SOUND with respect to reduction:
--
--     t ⟶ u  ⟹  ∀ x. eval t x ≡ eval u x
--
-- i.e. `eval` respects the equational theory (each reduction rule is a
-- CCC law the model validates). Consequently a SYNTACTIC fixpoint lifts
-- to a DENOTATIONAL one — which lets the REAL dispatch normalizer's
-- constructive fixpoint (TCB0.Normalizer.fixpoint-from-noredex, axiom-
-- free) drive the formal canonicity theorem. Non-degenerate, unlike the
-- refold.
--
-- One axiom: function extensionality (`funext`), needed only for the
-- congruence under `curry` (reduction changes a function value). This is
-- a standard, consistent axiom — far milder than the FALSE confluence /
-- strong-normalization postulates the rewriting developments rest on.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/EvalSound.agda
------------------------------------------------------------------------

module normalizer.Theory.Eval.EvalSound where

open import normalizer.Syntax.Types
  using (Func; Id; K; _⊕_; _⊗_; _⊎_; inj₁; inj₂; Σ; _,_; μ_)
open import normalizer.Syntax.CCC hiding (_≡_; refl; sym; trans; cong; cong₂; subst)
open import normalizer.Testing.Evaluator
  using (⟦_⟧T; ⟦_⟧FS; Fix; fix; fmap-Set; cata-Set; coherence; coherence⁻¹; eval)
open import normalizer.Theory.Eval.RefoldFixpoint using (coh-roundtrip)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

------------------------------------------------------------------------
-- Function extensionality (the single axiom).
------------------------------------------------------------------------

postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (a : A) → B a} →
           (∀ a → f a ≡ g a) → f ≡ g

------------------------------------------------------------------------
-- coherence⁻¹ is also a section (the other round-trip).
------------------------------------------------------------------------

coh-rt⁻¹ : ∀ F A (z : ⟦ ⟦ F ⟧F A ⟧T) →
           coherence⁻¹ F A (coherence F A z) ≡ z
coh-rt⁻¹ Id      A z        = refl
coh-rt⁻¹ (K _)   A z        = refl
coh-rt⁻¹ (F ⊕ G) A (inj₁ x) = cong inj₁ (coh-rt⁻¹ F A x)
coh-rt⁻¹ (F ⊕ G) A (inj₂ y) = cong inj₂ (coh-rt⁻¹ G A y)
coh-rt⁻¹ (F ⊗ G) A (x , y)  = cong₂ _,_ (coh-rt⁻¹ F A x) (coh-rt⁻¹ G A y)

------------------------------------------------------------------------
-- fmap-Set / cata-Set respect pointwise-equal arguments.
------------------------------------------------------------------------

fmap-Set-cong : ∀ F {X Y} {g h : X → Y} → (∀ z → g z ≡ h z) →
                (x : ⟦ F ⟧FS X) → fmap-Set F g x ≡ fmap-Set F h x
fmap-Set-cong Id      e x        = e x
fmap-Set-cong (K _)   e x        = refl
fmap-Set-cong (F ⊕ G) e (inj₁ x) = cong inj₁ (fmap-Set-cong F e x)
fmap-Set-cong (F ⊕ G) e (inj₂ y) = cong inj₂ (fmap-Set-cong G e y)
fmap-Set-cong (F ⊗ G) e (x , y)  = cong₂ _,_ (fmap-Set-cong F e x)
                                             (fmap-Set-cong G e y)

{-# TERMINATING #-}
cata-Set-cong : ∀ F {A} {a a' : ⟦ F ⟧FS A → A} → (∀ z → a z ≡ a' z) →
                (y : Fix F) → cata-Set F a y ≡ cata-Set F a' y
cata-Set-cong F {a = a} {a'} e (fix x) =
  trans (cong a (fmap-Set-cong F (cata-Set-cong F e) x)) (e _)

------------------------------------------------------------------------
-- eval commutes with fmap (through coherence), by induction on F.
------------------------------------------------------------------------

eval-fmap : ∀ F {A B} (h : Term A B) (z : ⟦ ⟦ F ⟧F A ⟧T) →
            eval (fmap F h) z ≡
            coherence⁻¹ F B (fmap-Set F (eval h) (coherence F A z))
eval-fmap Id      h z        = refl
eval-fmap (K _)   h z        = refl
eval-fmap (F ⊕ G) h (inj₁ x) = cong inj₁ (eval-fmap F h x)
eval-fmap (F ⊕ G) h (inj₂ y) = cong inj₂ (eval-fmap G h y)
eval-fmap (F ⊗ G) h (x , y)  = cong₂ _,_ (eval-fmap F h x) (eval-fmap G h y)

------------------------------------------------------------------------
-- Soundness: eval respects every reduction rule, pointwise.
------------------------------------------------------------------------

eval-sound : ∀ {A B} {t u : Term A B} → t ⟶ u → (x : ⟦ A ⟧T) →
             eval t x ≡ eval u x
eval-sound id-left              x        = refl
eval-sound id-right             x        = refl
eval-sound fst-pair             x        = refl
eval-sound snd-pair             x        = refl
eval-sound eta-pair             x        = refl
eval-sound case-inl             x        = refl
eval-sound case-inr             x        = refl
eval-sound eta-case             (inj₁ a) = refl
eval-sound eta-case             (inj₂ b) = refl
eval-sound pair-comp            x        = refl
eval-sound curry-β              x        = refl
eval-sound curry-β-ext          x        = refl
eval-sound curry-η              x        = refl
eval-sound (cata-β {F} {alg = alg}) x =
  cong (eval alg) (sym (eval-fmap F (cata F alg) x))
eval-sound (out-in F)           x        = coh-rt⁻¹ F (μ F) x
eval-sound (in-out F)           (fix y)  = cong fix (coh-roundtrip F (μ F) y)
eval-sound assoc-l              x        = refl
eval-sound assoc-r              x        = refl
eval-sound (⟶-∘-l {g = g} r)    x        = eval-sound r (eval g x)
eval-sound (⟶-∘-r {f = f} r)    x        = cong (eval f) (eval-sound r x)
eval-sound (⟶-pair-l {g = g} r) x        = cong (λ z → (z , eval g x)) (eval-sound r x)
eval-sound (⟶-pair-r {f = f} r) x        = cong (λ z → (eval f x , z)) (eval-sound r x)
eval-sound (⟶-case-l r)         (inj₁ a) = eval-sound r a
eval-sound (⟶-case-l r)         (inj₂ b) = refl
eval-sound (⟶-case-r r)         (inj₁ a) = refl
eval-sound (⟶-case-r r)         (inj₂ b) = eval-sound r b
eval-sound (⟶-cata {F} {C} r)   x        =
  cata-Set-cong F (λ w → eval-sound r (coherence⁻¹ F C w)) x
eval-sound (⟶-curry r)          x        = funext (λ a → eval-sound r (x , a))

------------------------------------------------------------------------
-- Lift to the reflexive-transitive closure.
------------------------------------------------------------------------

eval-sound* : ∀ {A B} {t u : Term A B} → t ⟶* u → (x : ⟦ A ⟧T) →
              eval t x ≡ eval u x
eval-sound* done       x = refl
eval-sound* (step r rs) x = trans (eval-sound r x) (eval-sound* rs x)
