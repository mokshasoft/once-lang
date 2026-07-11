------------------------------------------------------------------------
-- OCP-0009 · POC-0 — Discharging `conv-complete`
--
-- The tractable half of the adequacy scorecard: reduction-equal morphisms
-- are IDENTIFIED by `conv`. The engine is
--
--     eval-sound : t ⟶ u → ∀ x. eval t x ≡ eval u x
--
-- i.e. `eval` validates every reduction rule as a model equation. Ported
-- from `normalizer.Theory.Eval.EvalSound` and adapted to the current
-- `Func` (Id/One/Kc/⊕/⊗) and the Types-local `_≡_` (so no stdlib /
-- --guardedness entanglement). One axiom, exactly as the original:
-- function extensionality, needed only for congruence under `curry`
-- (reduction changes a function value). funext is standard and consistent
-- — far milder than the FALSE confluence/SN postulates the rewriting
-- developments rest on (OCP-0009 Motivation).
--
-- Result: `≈→conv` is PROVEN here — reduction-equal morphisms are accepted
-- by `conv`. (This is soundness of the reduction theory for `conv`; the
-- full sound+complete decision result is against observational equality
-- `_≋_` in Sound.agda, since `conv` decides a COARSER, fully-extensional
-- equality than the reduction `_≈_` — e.g. it equates `id{Unit}` and
-- `terminal`, which `_≈_` does not, the reduction system having no
-- terminal-η rule.)
------------------------------------------------------------------------

module poc.OCP0009.Complete where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv

------------------------------------------------------------------------
-- Function extensionality (the single axiom).
------------------------------------------------------------------------

postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (a : A) → B a} →
           (∀ a → f a ≡ g a) → f ≡ g

------------------------------------------------------------------------
-- Definitional equality: RST-closure of ⟶.
------------------------------------------------------------------------

data _≈_ {A B : Ty} : Term A B → Term A B → Set where
  ≈-refl : ∀ {t}     → t ≈ t
  ≈-step : ∀ {t u v} → t ⟶ u → u ≈ v → t ≈ v
  ≈-back : ∀ {t u v} → u ⟶ t → u ≈ v → t ≈ v

------------------------------------------------------------------------
-- coherence / coherence⁻¹ are mutually inverse (both round-trips).
------------------------------------------------------------------------

coh-rt⁻¹ : ∀ F A (z : ⟦ ⟦ F ⟧F A ⟧T) →
           coherence⁻¹ F A (coherence F A z) ≡ z
coh-rt⁻¹ Id      A z        = refl
coh-rt⁻¹ One     A z        = refl
coh-rt⁻¹ (Kc _)  A z        = refl
coh-rt⁻¹ (F ⊕ G) A (inj₁ x) = cong inj₁ (coh-rt⁻¹ F A x)
coh-rt⁻¹ (F ⊕ G) A (inj₂ y) = cong inj₂ (coh-rt⁻¹ G A y)
coh-rt⁻¹ (F ⊗ G) A (x , y)  = cong₂ _,_ (coh-rt⁻¹ F A x) (coh-rt⁻¹ G A y)

coh-rt : ∀ F A (y : ⟦ F ⟧FS ⟦ A ⟧T) →
         coherence F A (coherence⁻¹ F A y) ≡ y
coh-rt Id      A y        = refl
coh-rt One     A y        = refl
coh-rt (Kc _)  A y        = refl
coh-rt (F ⊕ G) A (inj₁ x) = cong inj₁ (coh-rt F A x)
coh-rt (F ⊕ G) A (inj₂ y) = cong inj₂ (coh-rt G A y)
coh-rt (F ⊗ G) A (x , y)  = cong₂ _,_ (coh-rt F A x) (coh-rt G A y)

------------------------------------------------------------------------
-- cata-Set respects pointwise-equal algebras.
--
-- `cata-Set F a (fix x) = a (map-cata-Set F F a x)`, so the congruence is
-- mutual with a congruence for `map-cata-Set` (the inlined fmap+cata).
------------------------------------------------------------------------

mutual
  {-# TERMINATING #-}
  cata-Set-cong : ∀ F {A} {a a' : ⟦ F ⟧FS A → A} → (∀ z → a z ≡ a' z) →
                  (y : Fix F) → cata-Set F a y ≡ cata-Set F a' y
  cata-Set-cong F {a = a} e (fix x) =
    trans (cong a (map-cata-cong F F e x)) (e _)

  map-cata-cong : ∀ F G {A} {a a' : ⟦ F ⟧FS A → A} → (∀ z → a z ≡ a' z) →
                  (x : ⟦ G ⟧FS (Fix F)) → map-cata-Set F G a x ≡ map-cata-Set F G a' x
  map-cata-cong F Id      e x        = cata-Set-cong F e x
  map-cata-cong F One     e x        = refl
  map-cata-cong F (Kc _)  e x        = refl
  map-cata-cong F (G ⊕ H) e (inj₁ x) = cong inj₁ (map-cata-cong F G e x)
  map-cata-cong F (G ⊕ H) e (inj₂ y) = cong inj₂ (map-cata-cong F H e y)
  map-cata-cong F (G ⊗ H) e (x , y)  = cong₂ _,_ (map-cata-cong F G e x) (map-cata-cong F H e y)

-- `map-cata-Set` is the inlined `fmap-Set ∘ cata-Set` — provably so, by
-- induction on the functor code. Bridges the two in the cata-β case below
-- (they are equal but no longer definitionally so).
map≡fmap : ∀ F G {A} (a : ⟦ F ⟧FS A → A) (x : ⟦ G ⟧FS (Fix F)) →
           map-cata-Set F G a x ≡ fmap-Set G (cata-Set F a) x
map≡fmap F Id      a x        = refl
map≡fmap F One     a x        = refl
map≡fmap F (Kc _)  a x        = refl
map≡fmap F (G ⊕ H) a (inj₁ x) = cong inj₁ (map≡fmap F G a x)
map≡fmap F (G ⊕ H) a (inj₂ y) = cong inj₂ (map≡fmap F H a y)
map≡fmap F (G ⊗ H) a (x , y)  = cong₂ _,_ (map≡fmap F G a x) (map≡fmap F H a y)

------------------------------------------------------------------------
-- eval commutes with fmap (through coherence), by induction on F.
------------------------------------------------------------------------

eval-fmap : ∀ F {A B} (h : Term A B) (z : ⟦ ⟦ F ⟧F A ⟧T) →
            eval (fmap F h) z ≡
            coherence⁻¹ F B (fmap-Set F (eval h) (coherence F A z))
eval-fmap Id      h z        = refl
eval-fmap One     h z        = refl
eval-fmap (Kc _)  h z        = refl
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
eval-sound (cata-β {F} {A} {alg = alg}) x =
  sym (cong (eval alg)
        (trans (eval-fmap F (cata F alg) x)
               (cong (coherence⁻¹ F A)
                     (sym (map≡fmap F F (λ y → eval alg (coherence⁻¹ F A y))
                                        (coherence F (μ F) x))))))
eval-sound (out-in F)           x        = coh-rt⁻¹ F (μ F) x
eval-sound (in-out F)           (fix y)  = cong fix (coh-rt F (μ F) y)
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
-- Lift soundness to the definitional equality `_≈_`.
------------------------------------------------------------------------

eval-≈ : ∀ {A B} {t u : Term A B} → t ≈ u → (x : ⟦ A ⟧T) →
         eval t x ≡ eval u x
eval-≈ ≈-refl        x = refl
eval-≈ (≈-step r e)  x = trans (eval-sound r x) (eval-≈ e x)
eval-≈ (≈-back r e)  x = trans (sym (eval-sound r x)) (eval-≈ e x)

------------------------------------------------------------------------
-- Reflexivity of the structural value-equality.
------------------------------------------------------------------------

∧-true : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-true refl refl = refl

mutual
  eq-Fix-refl : ∀ F (v : Fix F) → eq-Fix F v v ≡ true
  eq-Fix-refl F (fix x) = eq-FS-refl F F x

  eq-FS-refl : ∀ F G (x : ⟦ G ⟧FS (Fix F)) → eq-FS F G x x ≡ true
  eq-FS-refl F Id      x        = eq-Fix-refl F x
  eq-FS-refl F One     x        = refl
  eq-FS-refl F (Kc H)  x        = eq-Fix-refl H x
  eq-FS-refl F (G ⊕ H) (inj₁ x) = eq-FS-refl F G x
  eq-FS-refl F (G ⊕ H) (inj₂ y) = eq-FS-refl F H y
  eq-FS-refl F (G ⊗ H) (x , y)  = ∧-true (eq-FS-refl F G x) (eq-FS-refl F H y)

eq-val-refl : ∀ C (fo : FirstOrder C) (v : ⟦ C ⟧T) → eq-val C fo v v ≡ true
eq-val-refl Void    fo-void      v        = ⊥-elim v
eq-val-refl Unit    fo-unit      v        = refl
eq-val-refl (A * B) (fo-* fa fb) (a , b)  = ∧-true (eq-val-refl A fa a) (eq-val-refl B fb b)
eq-val-refl (A + B) (fo-+ fa fb) (inj₁ a) = eq-val-refl A fa a
eq-val-refl (A + B) (fo-+ fa fb) (inj₂ b) = eq-val-refl B fb b
eq-val-refl (μ F)   fo-μ         v        = eq-Fix-refl F v

------------------------------------------------------------------------
-- ≈→conv: reduction-equal morphisms are accepted by `conv`.
-- (Soundness of the reduction theory `_≈_` for `conv`, via eval-soundness.)
------------------------------------------------------------------------

≈→conv : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
       → t ≈ u → conv fo t u ≡ true
≈→conv {C} fo t u e =
  subst (λ z → eq-val C fo (eval t tt) z ≡ true)
        (eval-≈ e tt)
        (eq-val-refl C fo (eval t tt))
