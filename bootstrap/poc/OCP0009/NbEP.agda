------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — step 1: eval into the presheaf
--
-- On the proven presheaf foundation (`NbEK`: thinnings, weakening, functor
-- laws), interpret a FRAGMENT SYNTAX `Tm` (`{Unit, ×, +, μ}`, no `⇒`) into
-- the semantic domain `Val`, and reify — giving a principled normalizer
--
--   nf : Tm A B → Term A B
--
-- `eval` is the standard NbE evaluator: β for products/coproducts, cata-β on
-- constructor-headed `vIn`, and STUCK neutrals (`nCata`/`nMap`) on μ-neutrals
-- (the inductive-only discipline). Neutral carriers are the bootstrap `Term`
-- (via `emb`), so this reuses NbEK's proven `Val`/reify unchanged.
--
-- `⇒` is the next step (step 2, Kripke). Adequacy (step 3) is the logical
-- relation over `NbEK._≼_`, using the proven functor laws. `eval`/`vcata`/
-- `mapCata` recurse over Term+Val together, so termination is the standard
-- NbE argument (a `TERMINATING` pragma here; a theorem via adequacy later).
------------------------------------------------------------------------

module poc.OCP0009.NbEP where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEK

------------------------------------------------------------------------
-- Fragment syntax `{Unit, ×, +, μ}` (no `⇒`).
------------------------------------------------------------------------

infixr 30 _⊙_
data Tm : Ty → Ty → Set where
  idT   : ∀ {A} → Tm A A
  _⊙_   : ∀ {A B D} → Tm B D → Tm A B → Tm A D
  fstT  : ∀ {A B} → Tm (A * B) A
  sndT  : ∀ {A B} → Tm (A * B) B
  pair  : ∀ {A B D} → Tm D A → Tm D B → Tm D (A * B)
  inlT  : ∀ {A B} → Tm A (A + B)
  inrT  : ∀ {A B} → Tm B (A + B)
  case  : ∀ {A B D} → Tm A D → Tm B D → Tm (A + B) D
  termT : ∀ {A} → Tm A Unit
  InT   : ∀ {F} → Tm (⟦ F ⟧F (μ F)) (μ F)
  OutT  : ∀ {F} → Tm (μ F) (⟦ F ⟧F (μ F))
  cataT : ∀ F {A} → Tm (⟦ F ⟧F A) A → Tm (μ F) A

-- Embedding into the bootstrap IR (for the neutral carriers / reified NF).
emb : ∀ {A B} → Tm A B → C.Term A B
emb idT        = C.id
emb (f ⊙ g)    = emb f C.∘ emb g
emb fstT       = C.fst
emb sndT       = C.snd
emb (pair f g) = C.⟨ emb f , emb g ⟩
emb inlT       = C.inl
emb inrT       = C.inr
emb (case f g) = C.[ emb f , emb g ]
emb termT      = C.terminal
emb InT        = C.In
emb OutT       = C.Out
emb (cataT F a) = C.cata F (emb a)

------------------------------------------------------------------------
-- Evaluation into the presheaf.
------------------------------------------------------------------------

mutual
  {-# TERMINATING #-}
  eval : ∀ {A B D} → Tm B D → Val A B → Val A D
  eval idT        v = v
  eval (f ⊙ g)    v = eval f (eval g v)
  eval fstT       v = vfst v
  eval sndT       v = vsnd v
  eval (pair f g) v = vPair (eval f v) (eval g v)
  eval inlT       v = vInl v
  eval inrT       v = vInr v
  eval (case f g) v = vcase f g v
  eval termT      v = vUnit
  eval InT        v = vIn v
  eval OutT       v = vout v
  eval (cataT F a) v = vcata F a v

  -- η-long: reflect at the result type of every neutral-producing eliminator,
  -- so a product-typed result is η-expanded (making `nf` η-complete).
  vfst : ∀ {A X Y} → Val A (X * Y) → Val A X
  vfst (vPair a _)     = a
  vfst {X = X} (vNe ne) = reflect X (nFst ne)

  vsnd : ∀ {A X Y} → Val A (X * Y) → Val A Y
  vsnd (vPair _ b)     = b
  vsnd {Y = Y} (vNe ne) = reflect Y (nSnd ne)

  vout : ∀ {A F} → Val A (μ F) → Val A (⟦ F ⟧F (μ F))
  vout (vIn w)          = w
  vout {F = F} (vNe ne) = reflect (⟦ F ⟧F (μ F)) (nOut ne)

  vcase : ∀ {A X Y D} → Tm X D → Tm Y D → Val A (X + Y) → Val A D
  vcase f g (vInl a)         = eval f a
  vcase f g (vInr b)         = eval g b
  vcase {D = D} f g (vNe ne) = reflect D (nCase (nf f) (nf g) ne)

  vcata : ∀ {A} F {D} → Tm (⟦ F ⟧F D) D → Val A (μ F) → Val A D
  vcata F a (vIn w)          = eval a (mapCata F a F w)
  vcata F {D = D} a (vNe ne) = reflect D (nCata F (nf a) ne)

  mapCata : ∀ {A} F {D} → Tm (⟦ F ⟧F D) D → ∀ G →
            Val A (⟦ G ⟧F (μ F)) → Val A (⟦ G ⟧F D)
  mapCata F a Id      v          = vcata F a v
  mapCata F a One     v          = v
  mapCata F a (Kc H)  v          = v
  mapCata F a (G ⊕ H) (vInl x)   = vInl (mapCata F a G x)
  mapCata F a (G ⊕ H) (vInr y)   = vInr (mapCata F a H y)
  mapCata F a (G ⊕ H) (vNe ne)   = vNe (nMap F (G ⊕ H) (nf a) ne)
  mapCata F a (G ⊗ H) (vPair x y) = vPair (mapCata F a G x) (mapCata F a H y)
  mapCata F a (G ⊗ H) (vNe ne)   = vNe (nMap F (G ⊗ H) (nf a) ne)

  nf : ∀ {A B} → Tm A B → C.Term A B
  nf {A} t = reifyVal (eval t (reflect A (nThin ≼-refl)))

------------------------------------------------------------------------
-- The principled normalizer.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Examples — recursion normalizes (cata-β) on the principled engine.
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

Nat : Ty
Nat = μ NatF

zero : Tm Unit Nat
zero = InT ⊙ inlT

suc : Tm Nat Nat
suc = InT ⊙ inrT

one two : Tm Unit Nat
one = suc ⊙ zero
two = suc ⊙ one

double : Tm Nat Nat
double = cataT NatF (case zero (suc ⊙ suc))

_ : nf (double ⊙ zero) ≡ nf zero
_ = refl

_ : nf (double ⊙ one) ≡ nf two
_ = refl

-- product β/η on an open term (source with a neutral component)
Sᵖ : Ty
Sᵖ = (Unit + Unit) * (Unit + Unit)

_ : nf {Sᵖ} (pair fstT sndT) ≡ nf {Sᵖ} idT
_ = refl

_ : nf {Sᵖ} (fstT ⊙ pair sndT fstT) ≡ nf {Sᵖ} sndT
_ = refl

-- η-pair on a NEUTRAL-produced product (the case the η-long correction fixes):
-- `Out` on a variable of `μ(Id⊗Id)` yields a product-typed neutral, and
-- `⟨fst,snd⟩ ∘ Out ≋ Out` now holds — before η-long reflection it did not.
PF : Func
PF = Id ⊗ Id

P : Ty
P = μ PF

_ : nf {P} (pair (fstT ⊙ OutT) (sndT ⊙ OutT)) ≡ nf {P} OutT
_ = refl
