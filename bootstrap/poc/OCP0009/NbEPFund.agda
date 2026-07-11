------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — step 3 (adequacy), piece 3: eval is a
-- congruence for the logical relation.
--
--   eval-cong : ≈V B v v′ → ≈V D (eval t v) (eval t v′)
--
-- i.e. `eval t` is a morphism of the relation `≈V` — the semantic core of
-- the fundamental theorem. Combined with the reflect/reify yoga (piece 2)
-- this gives: `nf t` is well-defined and stable under related inputs, and it
-- is the engine of completeness (piece 3b, source conversion, layers on top).
--
-- Closes by induction mirroring `eval`, ESCAPE-FREE beyond the `TERMINATING`
-- that mirrors `eval` (no funext — `{Unit,×,+,μ}`). Every former contributes
-- exactly one clause, riding on the relation from piece 2.
------------------------------------------------------------------------

module poc.OCP0009.NbEPFund where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEK
  using (Val; vUnit; vPair; vInl; vInr; vIn; vNe)
open import poc.OCP0009.NbEP
open import poc.OCP0009.NbEPRel

{-# TERMINATING #-}
eval-cong : ∀ {A B D : Ty} (t : Tm B D) {v v′ : Val A B} →
            ≈V B v v′ → ≈V D (eval t v) (eval t v′)
vfst-cong : ∀ {A X Y : Ty} {v v′ : Val A (X * Y)} →
            ≈V (X * Y) v v′ → ≈V X (vfst v) (vfst v′)
vsnd-cong : ∀ {A X Y : Ty} {v v′ : Val A (X * Y)} →
            ≈V (X * Y) v v′ → ≈V Y (vsnd v) (vsnd v′)
vout-cong : ∀ {A : Ty} {F} {v v′ : Val A (μ F)} →
            ≈V (μ F) v v′ → ≈V (⟦ F ⟧F (μ F)) (vout v) (vout v′)
vcase-cong : ∀ {A X Y D : Ty} (f : Tm X D) (g : Tm Y D) {v v′ : Val A (X + Y)} →
             ≈V (X + Y) v v′ → ≈V D (vcase f g v) (vcase f g v′)
vcata-cong : ∀ {A : Ty} F {D} (a : Tm (⟦ F ⟧F D) D) {v v′ : Val A (μ F)} →
             ≈V (μ F) v v′ → ≈V D (vcata F a v) (vcata F a v′)
mapCata-cong : ∀ {A : Ty} F {D} (a : Tm (⟦ F ⟧F D) D) G
             {v v′ : Val A (⟦ G ⟧F (μ F))} →
             ≈V (⟦ G ⟧F (μ F)) v v′ → ≈V (⟦ G ⟧F D) (mapCata F a G v) (mapCata F a G v′)

eval-cong idT        p = p
eval-cong (f ⊙ g)    p = eval-cong f (eval-cong g p)
eval-cong fstT       p = vfst-cong p
eval-cong sndT       p = vsnd-cong p
eval-cong (pair f g) p = rPair (eval-cong f p) (eval-cong g p)
eval-cong inlT       p = rInl p
eval-cong inrT       p = rInr p
eval-cong (case f g) p = vcase-cong f g p
eval-cong termT      p = rUnit
eval-cong InT        p = rIn p
eval-cong OutT       p = vout-cong p
eval-cong (cataT F a) p = vcata-cong F a p

vfst-cong (rPair p q) = p
vfst-cong (rNe eq)    = reflect-≈V _ (cong (C.fst C.∘_) eq)
vsnd-cong (rPair p q) = q
vsnd-cong (rNe eq)    = reflect-≈V _ (cong (C.snd C.∘_) eq)
vout-cong (rIn p)  = p
vout-cong (rNe eq) = reflect-≈V _ (cong (C.Out C.∘_) eq)

vcase-cong f g (rInl p) = eval-cong f p
vcase-cong f g (rInr q) = eval-cong g q
vcase-cong f g (rNe eq) = reflect-≈V _ (cong (C.[ emb f , emb g ] C.∘_) eq)

vcata-cong F a (rIn p)  = eval-cong a (mapCata-cong F a F p)
vcata-cong F a (rNe eq) = reflect-≈V _ (cong (C.cata F (emb a) C.∘_) eq)

mapCata-cong F a Id      p          = vcata-cong F a p
mapCata-cong F a One     p          = p
mapCata-cong F a (Kc H)  p          = p
mapCata-cong F a (G ⊕ H) (rInl p)   = rInl (mapCata-cong F a G p)
mapCata-cong F a (G ⊕ H) (rInr q)   = rInr (mapCata-cong F a H q)
mapCata-cong F a (G ⊕ H) (rNe eq)   = rNe (cong (C.fmap (G ⊕ H) (C.cata F (emb a)) C.∘_) eq)
mapCata-cong F a (G ⊗ H) (rPair p q) = rPair (mapCata-cong F a G p) (mapCata-cong F a H q)
mapCata-cong F a (G ⊗ H) (rNe eq)   = rNe (cong (C.fmap (G ⊗ H) (C.cata F (emb a)) C.∘_) eq)
