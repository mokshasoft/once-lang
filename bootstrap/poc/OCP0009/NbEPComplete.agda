------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — completeness with case/cata congruence
--
--   ≈β-complete : t ≈β u → nf t ≡ nf u
--
-- Now `_≈β_` includes `case`- and `cata`-CONGRUENCE, enabled by the
-- normalise-under-neutrals engine change: the stuck neutrals carry `nf`-of-
-- branch / `nf`-of-algebra, so convertible branches give equal normal forms.
--
-- The fundamental theorem `≈β-eval` and `≈β-complete` are MUTUAL: the
-- neutral case of case/cata congruence needs `nf f ≡ nf f′` (= `≈β-complete`
-- on the branch sub-derivation) — well-founded on derivation size. Still
-- funext-free; `TERMINATING` covers the derivation+value mutual recursion.
--
-- Honest scope: full η (⟨fst,snd⟩ ≈ id on arbitrary values) still needs the
-- η-aware extensional relation — the remaining refinement.
------------------------------------------------------------------------

module poc.OCP0009.NbEPComplete where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEK
  using (Val; vPair; vInl; vInr; vIn; vNe; nThin; ≼-refl; reflect; reifyNe)
open import poc.OCP0009.NbEP
open import poc.OCP0009.NbEPRel
open import poc.OCP0009.NbEPFund using (eval-cong)

infix 4 _≈β_

data _≈β_ : ∀ {A B} → Tm A B → Tm A B → Set

≈β-eval : ∀ {A B D} {t u : Tm B D} → t ≈β u → (v : Val A B) →
          ≈V D (eval t v) (eval u v)
≈β-complete : ∀ {A B} {t u : Tm A B} → t ≈β u → nf t ≡ nf u
βcase-v : ∀ {A X Y D} {f f′ : Tm X D} {g g′ : Tm Y D} →
          f ≈β f′ → g ≈β g′ → (v : Val A (X + Y)) →
          ≈V D (vcase f g v) (vcase f′ g′ v)
βcata-v : ∀ {A} F {D} {a a′ : Tm (⟦ F ⟧F D) D} →
          a ≈β a′ → (v : Val A (μ F)) → ≈V D (vcata F a v) (vcata F a′ v)
mapCata-br : ∀ {A} F {D} {a a′ : Tm (⟦ F ⟧F D) D} → a ≈β a′ → ∀ G →
             (v : Val A (⟦ G ⟧F (μ F))) →
             ≈V (⟦ G ⟧F D) (mapCata F a G v) (mapCata F a′ G v)

data _≈β_ where
  βrefl  : ∀ {A B} {t : Tm A B} → t ≈β t
  βsym   : ∀ {A B} {t u : Tm A B} → t ≈β u → u ≈β t
  βtrans : ∀ {A B} {t u v : Tm A B} → t ≈β u → u ≈β v → t ≈β v
  β⊙    : ∀ {A B D} {f f′ : Tm B D} {g g′ : Tm A B} →
          f ≈β f′ → g ≈β g′ → (f ⊙ g) ≈β (f′ ⊙ g′)
  βpair : ∀ {A X Y} {f f′ : Tm A X} {g g′ : Tm A Y} →
          f ≈β f′ → g ≈β g′ → pair f g ≈β pair f′ g′
  βcase : ∀ {X Y D} {f f′ : Tm X D} {g g′ : Tm Y D} →
          f ≈β f′ → g ≈β g′ → case f g ≈β case f′ g′
  βcata : ∀ {F D} {a a′ : Tm (⟦ F ⟧F D) D} → a ≈β a′ → cataT F a ≈β cataT F a′
  β-fst    : ∀ {A X Y} {f : Tm A X} {g : Tm A Y} → (fstT ⊙ pair f g) ≈β f
  β-snd    : ∀ {A X Y} {f : Tm A X} {g : Tm A Y} → (sndT ⊙ pair f g) ≈β g
  β-case-l : ∀ {X Y D} {f : Tm X D} {g : Tm Y D} → (case f g ⊙ inlT) ≈β f
  β-case-r : ∀ {X Y D} {f : Tm X D} {g : Tm Y D} → (case f g ⊙ inrT) ≈β g
  β-idl    : ∀ {A B} {f : Tm A B} → (idT ⊙ f) ≈β f
  β-idr    : ∀ {A B} {f : Tm A B} → (f ⊙ idT) ≈β f
  β-assoc  : ∀ {A B D E} {f : Tm D E} {g : Tm B D} {h : Tm A B} →
             ((f ⊙ g) ⊙ h) ≈β (f ⊙ (g ⊙ h))
  β-out-in : ∀ {F} → (OutT {F} ⊙ InT {F}) ≈β idT

{-# TERMINATING #-}
≈β-eval βrefl              v = ≈V-refl _
≈β-eval (βsym p)           v = ≈V-sym (≈β-eval p v)
≈β-eval (βtrans p q)       v = ≈V-trans (≈β-eval p v) (≈β-eval q v)
≈β-eval (β⊙ {f = f} {g′ = g′} pf pg) v =
  ≈V-trans (eval-cong f (≈β-eval pg v)) (≈β-eval pf (eval g′ v))
≈β-eval (βpair pf pg)      v = rPair (≈β-eval pf v) (≈β-eval pg v)
≈β-eval (βcase pf pg)      v = βcase-v pf pg v
≈β-eval (βcata {F} pa)     v = βcata-v F pa v
≈β-eval β-fst              v = ≈V-refl _
≈β-eval β-snd              v = ≈V-refl _
≈β-eval β-case-l           v = ≈V-refl _
≈β-eval β-case-r           v = ≈V-refl _
≈β-eval β-idl              v = ≈V-refl _
≈β-eval β-idr              v = ≈V-refl _
≈β-eval β-assoc            v = ≈V-refl _
≈β-eval β-out-in           v = ≈V-refl _

≈β-complete {A} p = reify-≈V (≈β-eval p (reflect A (nThin ≼-refl)))

βcase-v pf pg (vInl a) = ≈β-eval pf a
βcase-v pf pg (vInr b) = ≈β-eval pg b
βcase-v {f = f} {f′} {g} {g′} pf pg (vNe ne) =
  reflect-≈V _ (cong (C._∘ reifyNe ne) (cong₂ C.[_,_] (≈β-complete pf) (≈β-complete pg)))

βcata-v F {a = a} {a′} pa (vIn w) =
  ≈V-trans (eval-cong a (mapCata-br F pa F w)) (≈β-eval pa (mapCata F a′ F w))
βcata-v F {a = a} {a′} pa (vNe ne) =
  reflect-≈V _ (cong (λ z → C.cata F z C.∘ reifyNe ne) (≈β-complete pa))

mapCata-br F pa Id      v          = βcata-v F pa v
mapCata-br F pa One     v          = ≈V-refl v
mapCata-br F pa (Kc H)  v          = ≈V-refl v
mapCata-br F pa (G ⊕ H) (vInl x)   = rInl (mapCata-br F pa G x)
mapCata-br F pa (G ⊕ H) (vInr y)   = rInr (mapCata-br F pa H y)
mapCata-br F {a = a} {a′} pa (G ⊕ H) (vNe ne) =
  rNe (cong (λ z → C.fmap (G ⊕ H) (C.cata F z) C.∘ reifyNe ne) (≈β-complete pa))
mapCata-br F pa (G ⊗ H) (vPair x y) = rPair (mapCata-br F pa G x) (mapCata-br F pa H y)
mapCata-br F {a = a} {a′} pa (G ⊗ H) (vNe ne) =
  rNe (cong (λ z → C.fmap (G ⊗ H) (C.cata F z) C.∘ reifyNe ne) (≈β-complete pa))
