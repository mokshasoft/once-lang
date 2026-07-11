------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — step 3 (adequacy), piece 1: eval is natural
--
-- The first proven lemma of the adequacy development, done on the presheaf
-- foundation: the evaluator `eval` (NbEP) is a NATURAL transformation w.r.t.
-- weakening —
--
--   wkVal w (eval t v) ≡ eval t (wkVal w v)
--
-- This is exactly the coherence the Kripke fundamental theorem invokes when
-- it moves a computable value along a thinning. It closes by structural
-- induction mirroring `eval`, using only the semantic-operation naturalities
-- (`vfst`/`vsnd`/`vout`/`vcase`/`vcata`/`mapCata`) — and it is **funext-free**
-- for this `{Unit,×,+,μ}` fragment (no closures; funext enters only with `⇒`).
--
-- Reusability, concretely: this is "one lemma, extended per former" — each
-- former contributes one clause, riding on the presheaf structure, exactly
-- the anti-debt organization. (`TERMINATING` mirrors `eval`'s; a theorem once
-- the full adequacy relation lands.)
------------------------------------------------------------------------

module poc.OCP0009.NbEPNat where

open import normalizer.Syntax.Types
open import poc.OCP0009.NbEK
  using (Val; Ne; vUnit; vPair; vInl; vInr; vIn; vNe; _≼_; wkVal; wkNe;
         reflect; nFst; nSnd; nOut; nCase; nCata)
open import poc.OCP0009.NbEP

------------------------------------------------------------------------
-- reflect commutes with weakening (needed by the η-long neutral cases).
------------------------------------------------------------------------

reflect-nat : ∀ {A₁ A : Ty} B (w : A₁ ≼ A) (ne : Ne A B) →
              wkVal w (reflect B ne) ≡ reflect B (wkNe w ne)
reflect-nat Unit    w ne = refl
reflect-nat (X * Y) w ne = cong₂ vPair (reflect-nat X w (nFst ne)) (reflect-nat Y w (nSnd ne))
reflect-nat (X + Y) w ne = refl
reflect-nat (X ⇒ Y) w ne = refl
reflect-nat (μ F)   w ne = refl
reflect-nat Void    w ne = refl

{-# TERMINATING #-}
eval-nat  : ∀ {A₁ A B D : Ty} (w : A₁ ≼ A) (t : Tm B D) (v : Val A B) →
            wkVal w (eval t v) ≡ eval t (wkVal w v)
vfst-nat  : ∀ {A₁ A X Y : Ty} (w : A₁ ≼ A) (v : Val A (X * Y)) →
            wkVal w (vfst v) ≡ vfst (wkVal w v)
vsnd-nat  : ∀ {A₁ A X Y : Ty} (w : A₁ ≼ A) (v : Val A (X * Y)) →
            wkVal w (vsnd v) ≡ vsnd (wkVal w v)
vout-nat  : ∀ {A₁ A : Ty} {F} (w : A₁ ≼ A) (v : Val A (μ F)) →
            wkVal w (vout v) ≡ vout (wkVal w v)
vcase-nat : ∀ {A₁ A X Y D : Ty} (w : A₁ ≼ A) (f : Tm X D) (g : Tm Y D)
            (v : Val A (X + Y)) → wkVal w (vcase f g v) ≡ vcase f g (wkVal w v)
vcata-nat : ∀ {A₁ A : Ty} F {D} (w : A₁ ≼ A) (a : Tm (⟦ F ⟧F D) D)
            (v : Val A (μ F)) → wkVal w (vcata F a v) ≡ vcata F a (wkVal w v)
mapCata-nat : ∀ {A₁ A : Ty} F {D} (w : A₁ ≼ A) (a : Tm (⟦ F ⟧F D) D) G
            (v : Val A (⟦ G ⟧F (μ F))) →
            wkVal w (mapCata F a G v) ≡ mapCata F a G (wkVal w v)

eval-nat w idT        v = refl
eval-nat w (f ⊙ g)    v = trans (eval-nat w f (eval g v)) (cong (eval f) (eval-nat w g v))
eval-nat w fstT       v = vfst-nat w v
eval-nat w sndT       v = vsnd-nat w v
eval-nat w (pair f g) v = cong₂ vPair (eval-nat w f v) (eval-nat w g v)
eval-nat w inlT       v = refl
eval-nat w inrT       v = refl
eval-nat w (case f g) v = vcase-nat w f g v
eval-nat w termT      v = refl
eval-nat w InT        v = refl
eval-nat w OutT       v = vout-nat w v
eval-nat w (cataT F a) v = vcata-nat F w a v

vfst-nat w (vPair a b) = refl
vfst-nat w (vNe ne)    = reflect-nat _ w (nFst ne)
vsnd-nat w (vPair a b) = refl
vsnd-nat w (vNe ne)    = reflect-nat _ w (nSnd ne)
vout-nat w (vIn x)  = refl
vout-nat w (vNe ne) = reflect-nat _ w (nOut ne)

vcase-nat w f g (vInl a) = eval-nat w f a
vcase-nat w f g (vInr b) = eval-nat w g b
vcase-nat w f g (vNe ne) = reflect-nat _ w (nCase (emb f) (emb g) ne)

vcata-nat F w a (vIn x)  = trans (eval-nat w a (mapCata F a F x))
                                 (cong (eval a) (mapCata-nat F w a F x))
vcata-nat F w a (vNe ne) = reflect-nat _ w (nCata F (emb a) ne)

mapCata-nat F w a Id      v          = vcata-nat F w a v
mapCata-nat F w a One     v          = refl
mapCata-nat F w a (Kc H)  v          = refl
mapCata-nat F w a (G ⊕ H) (vInl x)   = cong vInl (mapCata-nat F w a G x)
mapCata-nat F w a (G ⊕ H) (vInr y)   = cong vInr (mapCata-nat F w a H y)
mapCata-nat F w a (G ⊕ H) (vNe ne)   = refl
mapCata-nat F w a (G ⊗ H) (vPair x y) = cong₂ vPair (mapCata-nat F w a G x)
                                                    (mapCata-nat F w a H y)
mapCata-nat F w a (G ⊗ H) (vNe ne)   = refl
