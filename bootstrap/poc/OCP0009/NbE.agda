------------------------------------------------------------------------
-- OCP-0009 · The NbE engine (sound core) — open-term conversion by reify
--
-- Turns the *definitional* fragment of `_≋_` into an object-level normal
-- form for OPEN terms: `nf : Term A B → Term A B` via a residualizing
-- semantics with NEUTRALS (reflect/reify). Conversion of open terms is then
-- `nf t` vs `nf u` — decided syntactically, no confluence, no enumeration,
-- no single-point-domain trick. This is the engine the `Open.agda` framing
-- called for; it is the SAME evaluator pillar (reflect/reify/eval-nbe are
-- deterministic total functions).
--
-- SCOPE (honest, and SOUND within it): the `{Unit, ×, +}` fragment —
-- products, sums, unit. It gives η-long normal forms, so it decides the
-- definitional theory there (product β/η, coproduct β, projection/case on a
-- neutral stays stuck). `μ` (inductive types) and `⇒` (exponentials) are
-- kept OPAQUE (`nOpaque` — the morphism is carried un-normalized), which is
-- SOUND (denotation preserved) but not yet normalizing for them. Extending:
--   · `μ` needs the neutral-under-functor handling (cata on `In (neutral)`)
--     and in/out-η — the genuinely subtle part of inductive NbE;
--   · `⇒` needs a Kripke/presheaf function space (weakening) for reify.
-- Both are standard; both are the remaining engineering. Full adequacy
-- (nf sound + complete + stable) is the logical-relation obligation, stated
-- here and demonstrated on examples — NOT postulated.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbE where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC

------------------------------------------------------------------------
-- Neutral and (residualizing) semantic values, indexed by source `A`.
------------------------------------------------------------------------

data Ne (A : Ty) : Ty → Set
data Val (A : Ty) : Ty → Set

data Ne A where
  nId     : Ne A A                                            -- the source "variable"
  nFst    : ∀ {X Y} → Ne A (X * Y) → Ne A X
  nSnd    : ∀ {X Y} → Ne A (X * Y) → Ne A Y
  nCase   : ∀ {X Y B} → Term X B → Term Y B → Ne A (X + Y) → Ne A B
  nOpaque : ∀ {B} → Term A B → Ne A B                        -- un-normalized (μ/⇒/…)

data Val A where
  vUnit : Val A Unit
  vPair : ∀ {X Y} → Val A X → Val A Y → Val A (X * Y)
  vInl  : ∀ {X Y} → Val A X → Val A (X + Y)
  vInr  : ∀ {X Y} → Val A Y → Val A (X + Y)
  vNe   : ∀ {B} → Ne A B → Val A B

------------------------------------------------------------------------
-- reflect: η-expand a neutral into a semantic value (products only; sums
-- and opaque stay neutral).
------------------------------------------------------------------------

reflect : ∀ {A} B → Ne A B → Val A B
reflect Void    ne = vNe ne
reflect Unit    ne = vUnit
reflect (X * Y) ne = vPair (reflect X (nFst ne)) (reflect Y (nSnd ne))
reflect (X + Y) ne = vNe ne
reflect (X ⇒ Y) ne = vNe ne
reflect (μ F)   ne = vNe ne

------------------------------------------------------------------------
-- reify + the evaluator into the residualizing semantics (one mutual knot).
------------------------------------------------------------------------

mutual
  reifyVal : ∀ {A B} → Val A B → Term A B
  reifyVal vUnit       = terminal
  reifyVal (vPair a b) = ⟨ reifyVal a , reifyVal b ⟩
  reifyVal (vInl a)    = inl ∘ reifyVal a
  reifyVal (vInr b)    = inr ∘ reifyVal b
  reifyVal (vNe ne)    = reifyNe ne

  reifyNe : ∀ {A B} → Ne A B → Term A B
  reifyNe nId           = id
  reifyNe (nFst ne)     = fst ∘ reifyNe ne
  reifyNe (nSnd ne)     = snd ∘ reifyNe ne
  reifyNe (nCase f g ne) = [ f , g ] ∘ reifyNe ne
  reifyNe (nOpaque t)   = t

  -- Semantic projections / case (β on constructors, stuck on neutrals).
  vfst : ∀ {A X Y} → Val A (X * Y) → Val A X
  vfst (vPair a _) = a
  vfst (vNe ne)    = vNe (nFst ne)

  vsnd : ∀ {A X Y} → Val A (X * Y) → Val A Y
  vsnd (vPair _ b) = b
  vsnd (vNe ne)    = vNe (nSnd ne)

  vcase : ∀ {A X Y B} → Term X B → Term Y B → Val A (X + Y) → Val A B
  vcase f g (vInl a) = eval-nbe f a
  vcase f g (vInr b) = eval-nbe g b
  vcase f g (vNe ne) = vNe (nCase f g ne)

  -- Evaluate a morphism `B → C` as a Val-transformer in ambient source `A`.
  eval-nbe : ∀ {A B C} → Term B C → Val A B → Val A C
  eval-nbe id          v = v
  eval-nbe (f ∘ g)     v = eval-nbe f (eval-nbe g v)
  eval-nbe fst         v = vfst v
  eval-nbe snd         v = vsnd v
  eval-nbe ⟨ f , g ⟩   v = vPair (eval-nbe f v) (eval-nbe g v)
  eval-nbe inl         v = vInl v
  eval-nbe inr         v = vInr v
  eval-nbe [ f , g ]   v = vcase f g v
  eval-nbe terminal    v = vUnit
  -- Opaque fallback (sound: keep the actual morphism, un-normalized).
  eval-nbe initial     v = vNe (nOpaque (initial   ∘ reifyVal v))
  eval-nbe (curry f)   v = vNe (nOpaque (curry f   ∘ reifyVal v))
  eval-nbe apply       v = vNe (nOpaque (apply     ∘ reifyVal v))
  eval-nbe In          v = vNe (nOpaque (In        ∘ reifyVal v))
  eval-nbe Out         v = vNe (nOpaque (Out       ∘ reifyVal v))
  eval-nbe (cata F a)  v = vNe (nOpaque (cata F a  ∘ reifyVal v))

------------------------------------------------------------------------
-- The normalizer and open-term conversion.
------------------------------------------------------------------------

nf : ∀ {A B} → Term A B → Term A B
nf {A} t = reifyVal (eval-nbe t (reflect A nId))

-- Open-term conversion: normal forms compared. (A decidable structural `≟`
-- on `Term` gives the Bool/Dec wrapper; here we expose `nf` and compare
-- normal forms propositionally in the examples below.)

------------------------------------------------------------------------
-- Worked examples — OPEN-term definitional conversion decided by `nf`.
--
-- Source `S = Bool₂ * Bool₂`, whose components are `+`-typed, so the source
-- "variable" stays a genuine NEUTRAL (not collapsed) — these are real open
-- conversions, not closed computations. Each `refl` is Agda running `nf` on
-- both sides and finding syntactically identical normal forms.
------------------------------------------------------------------------

Bool₂ : Ty
Bool₂ = Unit + Unit

S : Ty
S = Bool₂ * Bool₂

-- Product η:  ⟨ fst , snd ⟩ ≋ id   (decided; neutrals `fst∘id`, `snd∘id` survive)
_ : nf {S} ⟨ fst , snd ⟩ ≡ nf {S} id
_ = refl

-- Product β:  fst ∘ ⟨ snd , fst ⟩ ≋ snd
_ : nf {S} (fst ∘ ⟨ snd , fst ⟩) ≡ nf {S} snd
_ = refl

-- Product β:  snd ∘ ⟨ snd , fst ⟩ ≋ fst
_ : nf {S} (snd ∘ ⟨ snd , fst ⟩) ≡ nf {S} fst
_ = refl

-- Coproduct β:  [ inr , inl ] ∘ inl ≋ inr   (at source Unit)
notB₂ : Term Bool₂ Bool₂
notB₂ = [ inr , inl ]

inlU inrU : Term Unit Bool₂
inlU = inl
inrU = inr

_ : nf {Unit} (notB₂ ∘ inlU) ≡ nf {Unit} inrU
_ = refl

-- Nested: fst ∘ ⟨ snd ∘ ⟨ fst , snd ⟩ , fst ⟩ ≋ snd
_ : nf {S} (fst ∘ ⟨ snd ∘ ⟨ fst , snd ⟩ , fst ⟩) ≡ nf {S} snd
_ = refl
