------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — refinement 2: the η-long invariant
--
-- `Normal B v` : the value `v` is η-LONG (at a product it is a `vPair`, at
-- Unit a `vUnit` — no un-expanded neutral at a negative/η type). `reflect`
-- produces normal values and `eval` PRESERVES normality (`eval-normal`).
--
-- Why this unlocks η-pair cleanly: at a product type `Normal` EXCLUDES `vNe`,
-- so the `mapCata`-on-a-product-neutral case (the one that forced the
-- commuting-lemma explosion in the extensional-relation route) is UNREACHABLE
-- for normal inputs. So η-pair (`⟨fst,snd⟩ ≈ id`) holds on normal values with
-- no commuting lemmas — the fundamental theorem just threads `Normal` and, at
-- η-pair, uses `Normal (X*Y) v ⇒ v = vPair a b` to close by reflexivity.
--
-- Scope: this gives η-PAIR (product η). Sum-η (`[inl,inr]≈id`) and μ-η
-- (`In∘Out≈id`) fail even on normal values (case/In on a neutral wraps it),
-- and are the genuinely-hard sheaf-NbE part — not covered here.
------------------------------------------------------------------------

module poc.OCP0009.NbEPNormal where

open import normalizer.Syntax.Types
open import poc.OCP0009.NbEK
  using (Val; Ne; vUnit; vPair; vInl; vInr; vIn; vNe;
         reflect; nFst; nSnd; nOut; nCase; nCata; nMap)
open import poc.OCP0009.NbEP

------------------------------------------------------------------------
-- The η-long predicate.
------------------------------------------------------------------------

data Normal {A : Ty} : ∀ B → Val A B → Set where
  n-unit   : Normal Unit vUnit
  n-pair   : ∀ {X Y} {a : Val A X} {b : Val A Y} → Normal X a → Normal Y b → Normal (X * Y) (vPair a b)
  n-inl    : ∀ {X Y} {a} → Normal X a → Normal (X + Y) (vInl a)
  n-inr    : ∀ {X Y} {b} → Normal Y b → Normal (X + Y) (vInr b)
  n-ne+    : ∀ {X Y} {ne} → Normal (X + Y) (vNe ne)
  n-in     : ∀ {F} {x} → Normal (⟦ F ⟧F (μ F)) x → Normal (μ F) (vIn x)
  n-neμ    : ∀ {F} {ne} → Normal (μ F) (vNe ne)
  n-neVoid : ∀ {ne} → Normal Void (vNe ne)
  n-ne⇒    : ∀ {X Y} {ne} → Normal (X ⇒ Y) (vNe ne)

reflect-normal : ∀ {A} B (ne : Ne A B) → Normal B (reflect B ne)
reflect-normal Unit    ne = n-unit
reflect-normal (X * Y) ne = n-pair (reflect-normal X (nFst ne)) (reflect-normal Y (nSnd ne))
reflect-normal (X + Y) ne = n-ne+
reflect-normal (μ F)   ne = n-neμ
reflect-normal Void    ne = n-neVoid
reflect-normal (X ⇒ Y) ne = n-ne⇒

------------------------------------------------------------------------
-- eval preserves normality.
------------------------------------------------------------------------

{-# TERMINATING #-}
eval-normal : ∀ {A B D} (t : Tm B D) {v : Val A B} → Normal B v → Normal D (eval t v)
vfst-normal : ∀ {A X Y} {v : Val A (X * Y)} → Normal (X * Y) v → Normal X (vfst v)
vsnd-normal : ∀ {A X Y} {v : Val A (X * Y)} → Normal (X * Y) v → Normal Y (vsnd v)
vout-normal : ∀ {A F} {v : Val A (μ F)} → Normal (μ F) v → Normal (⟦ F ⟧F (μ F)) (vout v)
vcase-normal : ∀ {A X Y D} (f : Tm X D) (g : Tm Y D) {v : Val A (X + Y)} →
               Normal (X + Y) v → Normal D (vcase f g v)
vcata-normal : ∀ {A} F {D} (a : Tm (⟦ F ⟧F D) D) {v : Val A (μ F)} →
               Normal (μ F) v → Normal D (vcata F a v)
mapCata-normal : ∀ {A} F {D} (a : Tm (⟦ F ⟧F D) D) G {v : Val A (⟦ G ⟧F (μ F))} →
                 Normal (⟦ G ⟧F (μ F)) v → Normal (⟦ G ⟧F D) (mapCata F a G v)

eval-normal idT        nv = nv
eval-normal (f ⊙ g)    nv = eval-normal f (eval-normal g nv)
eval-normal fstT       nv = vfst-normal nv
eval-normal sndT       nv = vsnd-normal nv
eval-normal (pair f g) nv = n-pair (eval-normal f nv) (eval-normal g nv)
eval-normal inlT       nv = n-inl nv
eval-normal inrT       nv = n-inr nv
eval-normal (case f g) nv = vcase-normal f g nv
eval-normal termT      nv = n-unit
eval-normal InT        nv = n-in nv
eval-normal OutT       nv = vout-normal nv
eval-normal (cataT F a) nv = vcata-normal F a nv

vfst-normal (n-pair na nb) = na
vsnd-normal (n-pair na nb) = nb

vout-normal (n-in nx)         = nx
vout-normal (n-neμ {ne = ne}) = reflect-normal _ (nOut ne)

vcase-normal f g (n-inl na)         = eval-normal f na
vcase-normal f g (n-inr nb)         = eval-normal g nb
vcase-normal f g (n-ne+ {ne = ne})  = reflect-normal _ (nCase (nf f) (nf g) ne)

vcata-normal F a (n-in nx)         = eval-normal a (mapCata-normal F a F nx)
vcata-normal F a (n-neμ {ne = ne}) = reflect-normal _ (nCata F (nf a) ne)

mapCata-normal F a Id      nv          = vcata-normal F a nv
mapCata-normal F a One     nv          = nv
mapCata-normal F a (Kc H)  nv          = nv
mapCata-normal F a (G ⊕ H) (n-inl nx)  = n-inl (mapCata-normal F a G nx)
mapCata-normal F a (G ⊕ H) (n-inr ny)  = n-inr (mapCata-normal F a H ny)
mapCata-normal F a (G ⊕ H) n-ne+       = n-ne+
mapCata-normal F a (G ⊗ H) (n-pair nx ny) =
  n-pair (mapCata-normal F a G nx) (mapCata-normal F a H ny)
