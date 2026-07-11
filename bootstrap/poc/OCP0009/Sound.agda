------------------------------------------------------------------------
-- OCP-0009 · POC-0 — Discharging `conv-sound` down to canonicity
--
-- `conv-sound : conv fo t u ≡ true → t ≈ u` is the hard (NbE-adequacy)
-- direction. This module discharges EVERYTHING around the genuine content
-- and pins the remaining hole to a single, standard, minimal lemma:
--
--   reify-eval (canonicity) : every closed first-order morphism is
--     convertible to the canonical morphism of its value:
--         t  ≈  ↑ (eval t tt).
--
-- Proven here (postulate-free except funext, inherited via Complete):
--   · eq-val-sound   — structural value-equality reflects `_≡_`
--   · ↑ (reify)       — canonical morphism of a first-order value
--   · eval-reify      — reify is a section: eval (↑ v) tt ≡ v
--   · ≈-trans, ≈-sym  — `_≈_` is an equivalence
--   · eval-reflect, conv-sound — DERIVED from `reify-eval` + the above
--
-- So the entire `conv-sound` obligation is reduced to `reify-eval`, which is
-- exactly the canonicity / transparency content of the repo's open
-- `EvalFullCorrectness` (normalizer-vs-compiler-path.md). Proving it is a
-- Tait-style logical relation over all types — POC-0b.
------------------------------------------------------------------------

module poc.OCP0009.Sound where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv
open import poc.OCP0009.Complete using (_≈_; ≈-refl; ≈-step; ≈-back)

------------------------------------------------------------------------
-- `_≈_` is an equivalence.
------------------------------------------------------------------------

≈-trans : ∀ {A B} {t u v : Term A B} → t ≈ u → u ≈ v → t ≈ v
≈-trans ≈-refl        q = q
≈-trans (≈-step r e)  q = ≈-step r (≈-trans e q)
≈-trans (≈-back r e)  q = ≈-back r (≈-trans e q)

≈-sym : ∀ {A B} {t u : Term A B} → t ≈ u → u ≈ t
≈-sym ≈-refl       = ≈-refl
≈-sym (≈-step r e) = ≈-trans (≈-sym e) (≈-back r ≈-refl)
≈-sym (≈-back r e) = ≈-trans (≈-sym e) (≈-step r ≈-refl)

≡→≈ : ∀ {A B} {t u : Term A B} → t ≡ u → t ≈ u
≡→≈ refl = ≈-refl

------------------------------------------------------------------------
-- Structural value-equality reflects propositional equality.
------------------------------------------------------------------------

∧-elimˡ : ∀ a b → (a ∧ b) ≡ true → a ≡ true
∧-elimˡ true  true  _ = refl
∧-elimˡ true  false ()
∧-elimˡ false _     ()

∧-elimʳ : ∀ a b → (a ∧ b) ≡ true → b ≡ true
∧-elimʳ true  true  _ = refl
∧-elimʳ true  false ()
∧-elimʳ false _     ()

mutual
  eq-Fix-sound : ∀ F (v w : Fix F) → eq-Fix F v w ≡ true → v ≡ w
  eq-Fix-sound F (fix x) (fix y) p = cong fix (eq-FS-sound F F x y p)

  eq-FS-sound : ∀ F G (x y : ⟦ G ⟧FS (Fix F)) → eq-FS F G x y ≡ true → x ≡ y
  eq-FS-sound F Id      x        y        p = eq-Fix-sound F x y p
  eq-FS-sound F One     _        _        _ = refl
  eq-FS-sound F (Kc H)  x        y        p = eq-Fix-sound H x y p
  eq-FS-sound F (G ⊕ H) (inj₁ x) (inj₁ y) p = cong inj₁ (eq-FS-sound F G x y p)
  eq-FS-sound F (G ⊕ H) (inj₂ x) (inj₂ y) p = cong inj₂ (eq-FS-sound F H x y p)
  eq-FS-sound F (G ⊕ H) (inj₁ x) (inj₂ y) ()
  eq-FS-sound F (G ⊕ H) (inj₂ x) (inj₁ y) ()
  eq-FS-sound F (G ⊗ H) (x , u)  (y , v)  p =
    cong₂ _,_ (eq-FS-sound F G x y (∧-elimˡ _ _ p))
              (eq-FS-sound F H u v (∧-elimʳ _ _ p))

eq-val-sound : ∀ C (fo : FirstOrder C) (v w : ⟦ C ⟧T) → eq-val C fo v w ≡ true → v ≡ w
eq-val-sound Void    fo-void      v        _        _ = ⊥-elim v
eq-val-sound Unit    fo-unit      _        _        _ = refl
eq-val-sound (A * B) (fo-* fa fb) (a , b)  (c , d)  p =
  cong₂ _,_ (eq-val-sound A fa a c (∧-elimˡ _ _ p))
            (eq-val-sound B fb b d (∧-elimʳ _ _ p))
eq-val-sound (A + B) (fo-+ fa fb) (inj₁ a) (inj₁ c) p = cong inj₁ (eq-val-sound A fa a c p)
eq-val-sound (A + B) (fo-+ fa fb) (inj₂ b) (inj₂ d) p = cong inj₂ (eq-val-sound B fb b d p)
eq-val-sound (A + B) (fo-+ fa fb) (inj₁ a) (inj₂ d) ()
eq-val-sound (A + B) (fo-+ fa fb) (inj₂ b) (inj₁ c) ()
eq-val-sound (μ F)   fo-μ         v        w        p = eq-Fix-sound F v w p

------------------------------------------------------------------------
-- Reify: the canonical morphism of a first-order value.
------------------------------------------------------------------------

mutual
  {-# TERMINATING #-}
  ↑Fix : ∀ F → Fix F → Term Unit (μ F)
  ↑Fix F (fix x) = In ∘ ↑layer F F x

  ↑layer : ∀ F G → ⟦ G ⟧FS (Fix F) → Term Unit (⟦ G ⟧F (μ F))
  ↑layer F Id      x        = ↑Fix F x
  ↑layer F One     _        = terminal
  ↑layer F (Kc H)  x        = ↑Fix H x
  ↑layer F (G ⊕ H) (inj₁ x) = inl ∘ ↑layer F G x
  ↑layer F (G ⊕ H) (inj₂ y) = inr ∘ ↑layer F H y
  ↑layer F (G ⊗ H) (x , y)  = ⟨ ↑layer F G x , ↑layer F H y ⟩

↑ : ∀ C → FirstOrder C → ⟦ C ⟧T → Term Unit C
↑ Void    fo-void      v        = ⊥-elim v
↑ Unit    fo-unit      _        = terminal
↑ (A * B) (fo-* fa fb) (a , b)  = ⟨ ↑ A fa a , ↑ B fb b ⟩
↑ (A + B) (fo-+ fa fb) (inj₁ a) = inl ∘ ↑ A fa a
↑ (A + B) (fo-+ fa fb) (inj₂ b) = inr ∘ ↑ B fb b
↑ (μ F)   fo-μ         v        = ↑Fix F v

------------------------------------------------------------------------
-- Reify is a section of eval: eval (↑ v) tt ≡ v.
------------------------------------------------------------------------

mutual
  {-# TERMINATING #-}
  eval-reify-Fix : ∀ F (v : Fix F) → eval (↑Fix F v) tt ≡ v
  eval-reify-Fix F (fix x) = cong fix (eval-reify-layer F F x)

  eval-reify-layer : ∀ F G (x : ⟦ G ⟧FS (Fix F)) →
                     coherence G (μ F) (eval (↑layer F G x) tt) ≡ x
  eval-reify-layer F Id      x        = eval-reify-Fix F x
  eval-reify-layer F One     _        = refl
  eval-reify-layer F (Kc H)  x        = eval-reify-Fix H x
  eval-reify-layer F (G ⊕ H) (inj₁ x) = cong inj₁ (eval-reify-layer F G x)
  eval-reify-layer F (G ⊕ H) (inj₂ y) = cong inj₂ (eval-reify-layer F H y)
  eval-reify-layer F (G ⊗ H) (x , y)  = cong₂ _,_ (eval-reify-layer F G x)
                                                  (eval-reify-layer F H y)

eval-reify : ∀ C (fo : FirstOrder C) (v : ⟦ C ⟧T) → eval (↑ C fo v) tt ≡ v
eval-reify Void    fo-void      v        = ⊥-elim v
eval-reify Unit    fo-unit      _        = refl
eval-reify (A * B) (fo-* fa fb) (a , b)  = cong₂ _,_ (eval-reify A fa a) (eval-reify B fb b)
eval-reify (A + B) (fo-+ fa fb) (inj₁ a) = cong inj₁ (eval-reify A fa a)
eval-reify (A + B) (fo-+ fa fb) (inj₂ b) = cong inj₂ (eval-reify B fb b)
eval-reify (μ F)   fo-μ         v        = eval-reify-Fix F v

------------------------------------------------------------------------
-- The single remaining hole: canonicity.
--
-- Every closed first-order morphism reduces (is convertible) to the
-- canonical morphism of its value. This is the genuine NbE-adequacy /
-- transparency lemma (OCP-0009 Motivation; §6; EvalFullCorrectness).
-- Proof route: a Tait-style logical relation over all types (POC-0b).
------------------------------------------------------------------------

postulate
  reify-eval : ∀ {C} (fo : FirstOrder C) (t : Term Unit C) → t ≈ ↑ C fo (eval t tt)

------------------------------------------------------------------------
-- Everything else is DERIVED from `reify-eval`.
------------------------------------------------------------------------

-- Reflection: the evaluator reflects equality on first-order codomains.
eval-reflect : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
             → eval t tt ≡ eval u tt → t ≈ u
eval-reflect {C} fo t u e =
  ≈-trans (reify-eval fo t)
          (≈-trans (≡→≈ (cong (↑ C fo) e))
                   (≈-sym (reify-eval fo u)))

-- Soundness of `conv`: what `conv` identifies is definitionally equal.
conv-sound : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
           → conv fo t u ≡ true → t ≈ u
conv-sound {C} fo t u p = eval-reflect fo t u (eq-val-sound C fo (eval t tt) (eval u tt) p)
