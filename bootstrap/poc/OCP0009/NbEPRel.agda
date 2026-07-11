------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — step 3 (adequacy), piece 2: the relation
--
-- The logical relation `≈V` (a per-type structural PER on semantic values)
-- and its REIFY half: reify sends related values to EQUAL normal forms.
--
--   reify-≈V : ≈V B v v' → reifyVal v ≡ reifyVal v'
--
-- Together with the fundamental theorem (piece 3: `t ≈ u → eval t ≈V eval u`)
-- this gives completeness — `nf t ≡ nf u` for convertible `t, u`, i.e. the
-- decidability of conversion via `nf`. This piece is the reusable relation +
-- half the "reflect/reify yoga", proven **escape-free** (no funext, no
-- pragma) — one constructor per former, the anti-debt organization.
------------------------------------------------------------------------

module poc.OCP0009.NbEPRel where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEK
  using (Val; Ne; vUnit; vPair; vInl; vInr; vIn; vNe; nFst; nSnd;
         reifyVal; reifyNe; reflect)

------------------------------------------------------------------------
-- The logical relation: structural on values, with neutrals related exactly
-- when their reifications agree.
------------------------------------------------------------------------

data ≈V {A : Ty} : ∀ B → Val A B → Val A B → Set where
  rUnit : ≈V Unit vUnit vUnit
  rPair : ∀ {X Y a a′ b b′} → ≈V X a a′ → ≈V Y b b′ →
          ≈V (X * Y) (vPair a b) (vPair a′ b′)
  rInl  : ∀ {X Y a a′} → ≈V X a a′ → ≈V (X + Y) (vInl a) (vInl a′)
  rInr  : ∀ {X Y b b′} → ≈V Y b b′ → ≈V (X + Y) (vInr b) (vInr b′)
  rIn   : ∀ {F x x′} → ≈V (⟦ F ⟧F (μ F)) x x′ → ≈V (μ F) (vIn x) (vIn x′)
  rNe   : ∀ {B} {ne ne′ : Ne A B} → reifyNe ne ≡ reifyNe ne′ → ≈V B (vNe ne) (vNe ne′)

------------------------------------------------------------------------
-- Reify half: related values reify to equal normal forms.
------------------------------------------------------------------------

reify-≈V : ∀ {A B} {v v′ : Val A B} → ≈V B v v′ → reifyVal v ≡ reifyVal v′
reify-≈V rUnit        = refl
reify-≈V (rPair p q)  = cong₂ C.⟨_,_⟩ (reify-≈V p) (reify-≈V q)
reify-≈V (rInl p)     = cong (C.inl C.∘_) (reify-≈V p)
reify-≈V (rInr q)     = cong (C.inr C.∘_) (reify-≈V q)
reify-≈V (rIn p)      = cong (C.In C.∘_) (reify-≈V p)
reify-≈V (rNe eq)     = eq

------------------------------------------------------------------------
-- Reflect half: neutrals with equal reifications reflect to related values
-- (η-expanding at products). Together with `reify-≈V` this is the full
-- reflect/reify yoga — proven, structural on the type, escape-free.
------------------------------------------------------------------------

reflect-≈V : ∀ {A} B {ne ne′ : Ne A B} → reifyNe ne ≡ reifyNe ne′ →
             ≈V B (reflect B ne) (reflect B ne′)
reflect-≈V Unit    eq = rUnit
reflect-≈V (X * Y) eq = rPair (reflect-≈V X (cong (C.fst C.∘_) eq))
                              (reflect-≈V Y (cong (C.snd C.∘_) eq))
reflect-≈V (X + Y) eq = rNe eq
reflect-≈V (X ⇒ Y) eq = rNe eq
reflect-≈V (μ F)   eq = rNe eq
reflect-≈V Void    eq = rNe eq

------------------------------------------------------------------------
-- The relation is an equivalence (reflexive/symmetric/transitive) — the PER
-- structure the fundamental theorem needs. (Reflexivity needs the value to
-- be in the relation's domain; here we give symmetry + transitivity, which
-- are unconditional and reused throughout the fundamental theorem.)
------------------------------------------------------------------------

≈V-refl : ∀ {A B} (v : Val A B) → ≈V B v v
≈V-refl vUnit       = rUnit
≈V-refl (vPair a b) = rPair (≈V-refl a) (≈V-refl b)
≈V-refl (vInl a)    = rInl (≈V-refl a)
≈V-refl (vInr b)    = rInr (≈V-refl b)
≈V-refl (vIn x)     = rIn (≈V-refl x)
≈V-refl (vNe ne)    = rNe refl

≈V-sym : ∀ {A B} {v v′ : Val A B} → ≈V B v v′ → ≈V B v′ v
≈V-sym rUnit       = rUnit
≈V-sym (rPair p q) = rPair (≈V-sym p) (≈V-sym q)
≈V-sym (rInl p)    = rInl (≈V-sym p)
≈V-sym (rInr q)    = rInr (≈V-sym q)
≈V-sym (rIn p)     = rIn (≈V-sym p)
≈V-sym (rNe eq)    = rNe (sym eq)

≈V-trans : ∀ {A B} {u v w : Val A B} → ≈V B u v → ≈V B v w → ≈V B u w
≈V-trans rUnit       rUnit       = rUnit
≈V-trans (rPair p q) (rPair r s) = rPair (≈V-trans p r) (≈V-trans q s)
≈V-trans (rInl p)    (rInl r)    = rInl (≈V-trans p r)
≈V-trans (rInr q)    (rInr s)    = rInr (≈V-trans q s)
≈V-trans (rIn p)     (rIn r)     = rIn (≈V-trans p r)
≈V-trans (rNe e)     (rNe e′)    = rNe (trans e e′)
