------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — completeness with congruences AND η-pair
--
--   ≈β-complete : t ≈β u → nf t ≡ nf u
--
-- `_≈β_` = the β-computational theory + ⊙/pair/case/cata CONGRUENCE
-- (refinement 1) + **η-pair** `⟨fst,snd⟩ ≈ id` (refinement 2).
--
-- η-pair is discharged via the η-long invariant `Normal` (NbEPNormal): the
-- fundamental theorem threads `Normal B v`, and at η-pair `Normal (X*Y) v`
-- forces `v = vPair a b`, so `⟨fst,snd⟩` on it IS `v` — reflexivity. Because
-- product-`Normal` excludes `vNe`, the `mapCata`-on-a-product-neutral case is
-- unreachable, so NO commuting lemmas are needed (that was the wall the
-- extensional-relation route hit).
--
-- Honest scope: this is η-PAIR. Sum-η (`[inl,inr]≈id`) and μ-η (`In∘Out≈id`)
-- fail even on normal values (case/In wraps a neutral) and are the genuinely-
-- hard sheaf-NbE part — not included.
------------------------------------------------------------------------

module poc.OCP0009.NbEPComplete where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEK
  using (Val; vPair; vInl; vInr; vIn; vNe; nThin; ≼-refl; reflect; reifyNe)
open import poc.OCP0009.NbEP
open import poc.OCP0009.NbEPRel
open import poc.OCP0009.NbEPFund using (eval-cong)
open import poc.OCP0009.NbEPNormal

infix 4 _≈β_

data _≈β_ : ∀ {A B} → Tm A B → Tm A B → Set

≈β-eval : ∀ {A B D} {t u : Tm B D} → t ≈β u → (v : Val A B) → Normal B v →
          ≈V D (eval t v) (eval u v)
≈β-complete : ∀ {A B} {t u : Tm A B} → t ≈β u → nf t ≡ nf u
βcase-v : ∀ {A X Y D} {f f′ : Tm X D} {g g′ : Tm Y D} →
          f ≈β f′ → g ≈β g′ → (v : Val A (X + Y)) → Normal (X + Y) v →
          ≈V D (vcase f g v) (vcase f′ g′ v)
βcata-v : ∀ {A} F {D} {a a′ : Tm (⟦ F ⟧F D) D} →
          a ≈β a′ → (v : Val A (μ F)) → Normal (μ F) v → ≈V D (vcata F a v) (vcata F a′ v)
mapCata-br : ∀ {A} F {D} {a a′ : Tm (⟦ F ⟧F D) D} → a ≈β a′ → ∀ G →
             (v : Val A (⟦ G ⟧F (μ F))) → Normal (⟦ G ⟧F (μ F)) v →
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
  -- refinement 2: η for products
  η-pair   : ∀ {X Y} → pair (fstT {A = X} {B = Y}) sndT ≈β idT

{-# TERMINATING #-}
≈β-eval βrefl              v nv = ≈V-refl _
≈β-eval (βsym p)           v nv = ≈V-sym (≈β-eval p v nv)
≈β-eval (βtrans p q)       v nv = ≈V-trans (≈β-eval p v nv) (≈β-eval q v nv)
≈β-eval (β⊙ {f = f} {g′ = g′} pf pg) v nv =
  ≈V-trans (eval-cong f (≈β-eval pg v nv)) (≈β-eval pf (eval g′ v) (eval-normal g′ nv))
≈β-eval (βpair pf pg)      v nv = rPair (≈β-eval pf v nv) (≈β-eval pg v nv)
≈β-eval (βcase pf pg)      v nv = βcase-v pf pg v nv
≈β-eval (βcata {F} pa)     v nv = βcata-v F pa v nv
≈β-eval β-fst              v nv = ≈V-refl _
≈β-eval β-snd              v nv = ≈V-refl _
≈β-eval β-case-l           v nv = ≈V-refl _
≈β-eval β-case-r           v nv = ≈V-refl _
≈β-eval β-idl              v nv = ≈V-refl _
≈β-eval β-idr              v nv = ≈V-refl _
≈β-eval β-assoc            v nv = ≈V-refl _
≈β-eval β-out-in           v nv = ≈V-refl _
≈β-eval η-pair (vPair a b) (n-pair na nb) = ≈V-refl (vPair a b)

≈β-complete {A} p = reify-≈V (≈β-eval p (reflect A (nThin ≼-refl)) (reflect-normal A (nThin ≼-refl)))

βcase-v pf pg (vInl a) (n-inl na) = ≈β-eval pf a na
βcase-v pf pg (vInr b) (n-inr nb) = ≈β-eval pg b nb
βcase-v {f = f} {f′} {g} {g′} pf pg (vNe ne) n-ne+ =
  reflect-≈V _ (cong (C._∘ reifyNe ne) (cong₂ C.[_,_] (≈β-complete pf) (≈β-complete pg)))

βcata-v F {a = a} {a′} pa (vIn w) (n-in nw) =
  ≈V-trans (eval-cong a (mapCata-br F pa F w nw)) (≈β-eval pa (mapCata F a′ F w) (mapCata-normal F a′ F nw))
βcata-v F {a = a} {a′} pa (vNe ne) n-neμ =
  reflect-≈V _ (cong (λ z → C.cata F z C.∘ reifyNe ne) (≈β-complete pa))

mapCata-br F pa Id      v          nv          = βcata-v F pa v nv
mapCata-br F pa One     v          nv          = ≈V-refl v
mapCata-br F pa (Kc H)  v          nv          = ≈V-refl v
mapCata-br F pa (G ⊕ H) (vInl x)   (n-inl nx)  = rInl (mapCata-br F pa G x nx)
mapCata-br F pa (G ⊕ H) (vInr y)   (n-inr ny)  = rInr (mapCata-br F pa H y ny)
mapCata-br F {a = a} {a′} pa (G ⊕ H) (vNe ne) n-ne+ =
  rNe (cong (λ z → C.fmap (G ⊕ H) (C.cata F z) C.∘ reifyNe ne) (≈β-complete pa))
mapCata-br F pa (G ⊗ H) (vPair x y) (n-pair nx ny) =
  rPair (mapCata-br F pa G x nx) (mapCata-br F pa H y ny)
