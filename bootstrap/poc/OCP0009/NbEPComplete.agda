------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — step 3 (adequacy), capstone: completeness
--
-- The headline result assembled from the proven pieces: `nf` IDENTIFIES
-- convertible terms, so conversion is decided by comparing normal forms.
--
--   ≈β-complete : t ≈β u → nf t ≡ nf u
--
-- for `_≈β_` = the β-computational theory (id/assoc, product-β, coproduct-β,
-- out∘in) with ⊙- and pair-congruence and the equivalence rules. It closes
-- with exactly the infrastructure already proven:
--   · β / computation rules — both sides `eval` to the SAME value ⇒ ≈V-refl;
--   · ⊙- / pair-congruence  — `eval-cong` + ≈V equivalence;
--   · then `reify-≈V` turns value-relatedness into equal normal forms.
--
-- Honest scope: `case`/`cata` CONGRUENCE and full η are NOT here — they need
-- normalising UNDER neutrals (the neutral `nCase`/`nCata` carry un-normalised
-- branches/algebras) and the η-aware (extensional) relation. That is the next
-- refinement; the β-theory completeness below is complete and proven.
------------------------------------------------------------------------

module poc.OCP0009.NbEPComplete where

open import normalizer.Syntax.Types
open import poc.OCP0009.NbEK using (Val; nThin; ≼-refl; reflect)
open import poc.OCP0009.NbEP
open import poc.OCP0009.NbEPRel
open import poc.OCP0009.NbEPFund using (eval-cong)

------------------------------------------------------------------------
-- The β-computational conversion on `Tm` (equivalence + ⊙/pair congruence
-- + the rules that hold DEFINITIONALLY in `eval`).
------------------------------------------------------------------------

infix 4 _≈β_
data _≈β_ : ∀ {A B} → Tm A B → Tm A B → Set where
  -- equivalence
  βrefl  : ∀ {A B} {t : Tm A B} → t ≈β t
  βsym   : ∀ {A B} {t u : Tm A B} → t ≈β u → u ≈β t
  βtrans : ∀ {A B} {t u v : Tm A B} → t ≈β u → u ≈β v → t ≈β v
  -- congruence (subterms are evaluated, never stored in a neutral)
  β⊙    : ∀ {A B D} {f f′ : Tm B D} {g g′ : Tm A B} →
          f ≈β f′ → g ≈β g′ → (f ⊙ g) ≈β (f′ ⊙ g′)
  βpair : ∀ {A X Y} {f f′ : Tm A X} {g g′ : Tm A Y} →
          f ≈β f′ → g ≈β g′ → pair f g ≈β pair f′ g′
  -- computation rules (both sides eval to the same value)
  β-fst    : ∀ {A X Y} {f : Tm A X} {g : Tm A Y} → (fstT ⊙ pair f g) ≈β f
  β-snd    : ∀ {A X Y} {f : Tm A X} {g : Tm A Y} → (sndT ⊙ pair f g) ≈β g
  β-case-l : ∀ {X Y D} {f : Tm X D} {g : Tm Y D} → (case f g ⊙ inlT) ≈β f
  β-case-r : ∀ {X Y D} {f : Tm X D} {g : Tm Y D} → (case f g ⊙ inrT) ≈β g
  β-idl    : ∀ {A B} {f : Tm A B} → (idT ⊙ f) ≈β f
  β-idr    : ∀ {A B} {f : Tm A B} → (f ⊙ idT) ≈β f
  β-assoc  : ∀ {A B D E} {f : Tm D E} {g : Tm B D} {h : Tm A B} →
             ((f ⊙ g) ⊙ h) ≈β (f ⊙ (g ⊙ h))
  β-out-in : ∀ {F} → (OutT {F} ⊙ InT {F}) ≈β idT

------------------------------------------------------------------------
-- Fundamental theorem for `_≈β_`: eval sends β-convertible terms to
-- ≈V-related values (at every input).
------------------------------------------------------------------------

≈β-eval : ∀ {A B D} {t u : Tm B D} → t ≈β u → (v : Val A B) →
          ≈V D (eval t v) (eval u v)
≈β-eval βrefl              v = ≈V-refl _
≈β-eval (βsym p)           v = ≈V-sym (≈β-eval p v)
≈β-eval (βtrans p q)       v = ≈V-trans (≈β-eval p v) (≈β-eval q v)
≈β-eval (β⊙ {f = f} {g′ = g′} pf pg) v =
  ≈V-trans (eval-cong f (≈β-eval pg v)) (≈β-eval pf (eval g′ v))
≈β-eval (βpair pf pg)      v = rPair (≈β-eval pf v) (≈β-eval pg v)
≈β-eval β-fst              v = ≈V-refl _
≈β-eval β-snd              v = ≈V-refl _
≈β-eval β-case-l           v = ≈V-refl _
≈β-eval β-case-r           v = ≈V-refl _
≈β-eval β-idl              v = ≈V-refl _
≈β-eval β-idr              v = ≈V-refl _
≈β-eval β-assoc            v = ≈V-refl _
≈β-eval β-out-in           v = ≈V-refl _

------------------------------------------------------------------------
-- Completeness: `nf` identifies β-convertible terms.
------------------------------------------------------------------------

≈β-complete : ∀ {A B} {t u : Tm A B} → t ≈β u → nf t ≡ nf u
≈β-complete {A} p = reify-≈V (≈β-eval p (reflect A (nThin ≼-refl)))
