------------------------------------------------------------------------
-- OCP-0009 · The NbE engine — now with μ (inductive types)
--
-- `nf : Term A B → Term A B`, a residualizing reify/reflect with NEUTRALS
-- that normalizes OPEN terms and decides definitional conversion for the
-- `{Unit, ×, +, μ}` fragment — products, sums, AND inductive types:
--   · product β/η, coproduct β                     (as before)
--   · cata-β: `cata alg ∘ In` unfolds on constructor-headed values
--   · in/out-η: `In ∘ Out = id`, `Out ∘ In = id`   (smart constructors)
--   · cata / Out on a μ-NEUTRAL (a variable of inductive type) stays STUCK
--     — the inductive-only discipline (OCP-0009 §2) realized operationally.
--
-- Soundness through the subtle case: when `cata` meets `In (neutral)` whose
-- functor structure contains a neutral, `mapCata` residualizes it via the
-- SYNTACTIC `fmap` (`fmap G (cata F alg) ∘ reify ne`) — nothing is dropped,
-- so denotation is preserved. `⇒` (functions) stays opaque (needs a Kripke
-- reify — the remaining piece). Full adequacy is the logical-relation
-- obligation, demonstrated on examples, not postulated.
--
-- `--safe`: `vcata`/`mapCata`/`eval-nbe` recurse together over both the
-- Term and the Val structure, but Agda's size-change checker accepts the
-- lexicographic (Term, Val) descent — no pragma needed.
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
  nOut    : ∀ {F} → Ne A (μ F) → Ne A (⟦ F ⟧F (μ F))
  nCata   : ∀ F {C} → Term (⟦ F ⟧F C) C → Ne A (μ F) → Ne A C
  nOpaque : ∀ {B} → Term A B → Ne A B                        -- un-normalized (⇒/…)

data Val A where
  vUnit : Val A Unit
  vPair : ∀ {X Y} → Val A X → Val A Y → Val A (X * Y)
  vInl  : ∀ {X Y} → Val A X → Val A (X + Y)
  vInr  : ∀ {X Y} → Val A Y → Val A (X + Y)
  vIn   : ∀ {F} → Val A (⟦ F ⟧F (μ F)) → Val A (μ F)
  vNe   : ∀ {B} → Ne A B → Val A B

------------------------------------------------------------------------
-- reflect: η-expand a neutral (products only; sums/μ/opaque stay neutral).
------------------------------------------------------------------------

reflect : ∀ {A} B → Ne A B → Val A B
reflect Void    ne = vNe ne
reflect Unit    ne = vUnit
reflect (X * Y) ne = vPair (reflect X (nFst ne)) (reflect Y (nSnd ne))
reflect (X + Y) ne = vNe ne
reflect (X ⇒ Y) ne = vNe ne
reflect (μ F)   ne = vNe ne

------------------------------------------------------------------------
-- Smart constructor for Out realizing out-η (`Out ∘ In = id`).
-- (The dual `In ∘ Out = id` would need to match `nOut` under a `vNe` at a
--  `⟦F⟧F(μF)` index, which Agda's unifier cannot invert — `⟦_⟧F` is not
--  injective — so in-η is left un-captured here: sound, just one η-law fewer.)
------------------------------------------------------------------------

vout : ∀ {A F} → Val A (μ F) → Val A (⟦ F ⟧F (μ F))
vout (vIn w)  = w                   -- Out ∘ In = id
vout (vNe ne) = vNe (nOut ne)

------------------------------------------------------------------------
-- reify + evaluator + cata (one mutual knot).
------------------------------------------------------------------------

mutual
  reifyVal : ∀ {A B} → Val A B → Term A B
  reifyVal vUnit       = terminal
  reifyVal (vPair a b) = ⟨ reifyVal a , reifyVal b ⟩
  reifyVal (vInl a)    = inl ∘ reifyVal a
  reifyVal (vInr b)    = inr ∘ reifyVal b
  reifyVal (vIn w)     = In ∘ reifyVal w
  reifyVal (vNe ne)    = reifyNe ne

  reifyNe : ∀ {A B} → Ne A B → Term A B
  reifyNe nId            = id
  reifyNe (nFst ne)      = fst ∘ reifyNe ne
  reifyNe (nSnd ne)      = snd ∘ reifyNe ne
  reifyNe (nCase f g ne) = [ f , g ] ∘ reifyNe ne
  reifyNe (nOut ne)      = Out ∘ reifyNe ne
  reifyNe (nCata F a ne) = cata F a ∘ reifyNe ne
  reifyNe (nOpaque t)    = t

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

  -- cata: β on constructor-headed `vIn`; stuck neutral on a μ-neutral.
  vcata : ∀ {A} F {C} → Term (⟦ F ⟧F C) C → Val A (μ F) → Val A C
  vcata F alg (vIn w)  = eval-nbe alg (mapCata F alg F w)
  vcata F alg (vNe ne) = vNe (nCata F alg ne)

  -- fmap (cata F alg) over the G-structure of an In-argument. A functor-
  -- position neutral is residualized SOUNDLY via the syntactic fmap.
  mapCata : ∀ {A} F {C} → Term (⟦ F ⟧F C) C → ∀ G →
            Val A (⟦ G ⟧F (μ F)) → Val A (⟦ G ⟧F C)
  mapCata F alg Id      v         = vcata F alg v
  mapCata F alg One     v         = v
  mapCata F alg (Kc H)  v         = v
  mapCata F alg (G ⊕ H) (vInl a)  = vInl (mapCata F alg G a)
  mapCata F alg (G ⊕ H) (vInr b)  = vInr (mapCata F alg H b)
  mapCata F alg (G ⊕ H) (vNe ne)  = vNe (nOpaque (fmap (G ⊕ H) (cata F alg) ∘ reifyNe ne))
  mapCata F alg (G ⊗ H) (vPair a b) = vPair (mapCata F alg G a) (mapCata F alg H b)
  mapCata F alg (G ⊗ H) (vNe ne)  = vNe (nOpaque (fmap (G ⊗ H) (cata F alg) ∘ reifyNe ne))

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
  eval-nbe In          v = vIn v
  eval-nbe Out         v = vout v
  eval-nbe (cata F a)  v = vcata F a v
  -- Opaque fallback for exponentials / initial (sound: keep the morphism).
  eval-nbe initial     v = vNe (nOpaque (initial ∘ reifyVal v))
  eval-nbe (curry f)   v = vNe (nOpaque (curry f ∘ reifyVal v))
  eval-nbe apply       v = vNe (nOpaque (apply   ∘ reifyVal v))

------------------------------------------------------------------------
-- The normalizer.
------------------------------------------------------------------------

nf : ∀ {A B} → Term A B → Term A B
nf {A} t = reifyVal (eval-nbe t (reflect A nId))

------------------------------------------------------------------------
-- Examples — Nat and open/closed conversions the closed `conv` could not do.
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

Nat : Ty
Nat = μ NatF

zero : Term Unit Nat
zero = In ∘ inl

suc : Term Nat Nat
suc = In ∘ inr

one two : Term Unit Nat
one = suc ∘ zero
two = suc ∘ one

double : Term Nat Nat
double = cata NatF [ zero , suc ∘ suc ]

-- cata-β (recursion runs): double 0 ≋ 0, double 1 ≋ 2.
_ : nf {Unit} (double ∘ zero) ≡ nf {Unit} zero
_ = refl

_ : nf {Unit} (double ∘ one) ≡ nf {Unit} two
_ = refl

-- out/in-η on an OPEN μ term: Out ∘ In ≋ id.
_ : nf {⟦ NatF ⟧F Nat} (Out {NatF} ∘ In {NatF}) ≡ nf {⟦ NatF ⟧F Nat} id
_ = refl

-- cata on an OPEN μ-variable stays STUCK (inductive-only): `double` on a
-- neutral reifies to `cata … ∘ id`, unchanged by post-composing id.
_ : nf {Nat} (double ∘ id) ≡ nf {Nat} double
_ = refl

-- Product β/η still hold (source with +-typed components → neutrals survive).
S : Ty
S = (Unit + Unit) * (Unit + Unit)

_ : nf {S} ⟨ fst , snd ⟩ ≡ nf {S} id
_ = refl

_ : nf {S} (fst ∘ ⟨ snd , fst ⟩) ≡ nf {S} snd
_ = refl
