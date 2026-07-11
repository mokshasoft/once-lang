------------------------------------------------------------------------
-- OCP-0009 · POC-0 — `conv` decides observational equality (finalized)
--
-- The definitional equality a type-checker actually needs is CONVERSION —
-- the equality the model induces, i.e. "same denotation". Here that is
-- observational (model) equality of IR morphisms:
--
--     t ≋ u   :=   ∀ x. eval t x ≡ eval u x
--
-- This is the MAXIMAL sound definitional equality: it validates every βη
-- law AND terminal-η (a CCC's terminal object is unique), and is sound by
-- construction (equal denotations). It is strictly COARSER than the
-- reduction convertibility `_≈_` (Complete.agda), whose rule set has no
-- terminal-η — e.g. `id{Unit} ≋ terminal` but NOT `id{Unit} ≈ terminal`.
-- So `conv` (which compares denotations) decides `_≋_`, not `_≈_`.
--
-- MAIN RESULT (this module, ZERO postulates): on closed morphisms
-- `Term Unit C` with FIRST-ORDER codomain `C`, `conv` is a SOUND and
-- COMPLETE decision procedure for `_≋_`:
--
--     conv-decides : (t ≋ u → conv fo t u ≡ true)
--                  × (conv fo t u ≡ true → t ≋ u)
--
-- The domain being `Unit` (a single point) is what makes the `∀ x` collapse
-- to one evaluation; first-order `C` is what makes value-equality decidable
-- without reification. Lifting either restriction (open terms / higher-order
-- codomains) is POC-0b (residualizing NbE). The reduction theory is related
-- by `_≈_ ⊆ _≋_` (`≈⊆≋`, = eval-soundness), so `conv` also respects `_⟶_`.
------------------------------------------------------------------------

module poc.OCP0009.Sound where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv
open import poc.OCP0009.Complete using (_≈_; eval-sound; eval-≈)

------------------------------------------------------------------------
-- Observational (model) equality — the conversion `conv` decides.
------------------------------------------------------------------------

_≋_ : ∀ {A B} → Term A B → Term A B → Set
_≋_ {A} t u = (x : ⟦ A ⟧T) → eval t x ≡ eval u x

-- Equivalence.
≋-refl  : ∀ {A B} (t : Term A B) → t ≋ t
≋-refl  t x = refl

≋-sym   : ∀ {A B} {t u : Term A B} → t ≋ u → u ≋ t
≋-sym   e x = sym (e x)

≋-trans : ∀ {A B} {t u v : Term A B} → t ≋ u → u ≋ v → t ≋ v
≋-trans e₁ e₂ x = trans (e₁ x) (e₂ x)

-- Congruence (a sample — enough to certify `_≋_` is a real conversion, not
-- just a relation). `eval` is compositional, so these are immediate.
≋-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
      f ≋ f' → g ≋ g' → (f ∘ g) ≋ (f' ∘ g')
≋-∘ {f = f} {g' = g'} ef eg x = trans (cong (eval f) (eg x)) (ef (eval g' x))

≋-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
        f ≋ f' → g ≋ g' → ⟨ f , g ⟩ ≋ ⟨ f' , g' ⟩
≋-⟨,⟩ ef eg x = cong₂ _,_ (ef x) (eg x)

------------------------------------------------------------------------
-- The reduction theory is sound for `_≋_`:  _⟶_ ⊆ _≈_ ⊆ _≋_.
-- (So `conv`, deciding `_≋_`, also accepts everything `_⟶_`/`_≈_` equate.)
------------------------------------------------------------------------

⟶⊆≋ : ∀ {A B} {t u : Term A B} → t ⟶ u → t ≋ u
⟶⊆≋ r = eval-sound r

≈⊆≋ : ∀ {A B} {t u : Term A B} → t ≈ u → t ≋ u
≈⊆≋ e = eval-≈ e

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

-- Converse (reflexivity of the check on equal values), imported shape.
open import poc.OCP0009.Complete using (eq-val-refl)

------------------------------------------------------------------------
-- MAIN: `conv` is a sound and complete decision procedure for `_≋_`
-- on closed morphisms with first-order codomain. ZERO postulates.
------------------------------------------------------------------------

-- Completeness: observationally-equal morphisms are accepted.
conv-complete : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
              → t ≋ u → conv fo t u ≡ true
conv-complete {C} fo t u e =
  subst (λ z → eq-val C fo (eval t tt) z ≡ true)
        (e tt)
        (eq-val-refl C fo (eval t tt))

-- Soundness: accepted morphisms are observationally equal. The domain is
-- `Unit`, so any `x : ⟦Unit⟧T` is definitionally `tt`; hence one evaluation
-- suffices for all `x`.
conv-sound : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
           → conv fo t u ≡ true → t ≋ u
conv-sound {C} fo t u p _ = eq-val-sound C fo (eval t tt) (eval u tt) p

-- `conv` DECIDES `_≋_`.
conv-decides : ∀ {C} (fo : FirstOrder C) (t u : Term Unit C)
             → (t ≋ u → conv fo t u ≡ true) × (conv fo t u ≡ true → t ≋ u)
conv-decides fo t u = conv-complete fo t u , conv-sound fo t u
