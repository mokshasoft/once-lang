------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — the presheaf foundation (proven)
--
-- The reusable base for a proven, extensible NbE: a category of THINNINGS
-- (weakenings), the semantic domain as a PRESHEAF over it (a weakening
-- action `wkVal`/`wkNe`), and the FUNCTOR LAWS of that action — proven.
--
-- Why this first: both the Kripke `⇒` (reify under a binder needs a fresh
-- variable in an extended context) and the adequacy logical relation (a
-- Kripke relation over the same thinnings) stand on exactly this. Getting it
-- right and proven once means each later former is a LOCAL extension, not a
-- global re-proof — the anti-debt discipline.
--
-- Scope: the `{Unit, ×, +, μ}` semantic domain (products, sums, inductive
-- types). `⇒` is deferred to the next step precisely because a Kripke
-- function space needs this weakening infrastructure. Everything here is
-- postulate-free and structurally terminating (no pragma), so the whole
-- module compiles under `--safe`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEK where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_]; terminal; In; Out; cata; fmap)

------------------------------------------------------------------------
-- The category of thinnings.  `A₁ ≼ A` : `A₁` is `A` extended with product
-- components (a projection `A₁ → A`).
------------------------------------------------------------------------

data _≼_ : Ty → Ty → Set where
  ≼-refl : ∀ {A}      → A ≼ A
  ≼-ext  : ∀ {A A₁ X} → A₁ ≼ A → (A₁ * X) ≼ A

infixr 30 _⊚_
_⊚_ : ∀ {A₂ A₁ A : Ty} → A₂ ≼ A₁ → A₁ ≼ A → A₂ ≼ A
≼-refl     ⊚ w = w
(≼-ext wₑ) ⊚ w = ≼-ext (wₑ ⊚ w)

-- The thinnings form a category: identity `≼-refl`, composition `_⊚_`.
⊚-idʳ : ∀ {A₁ A : Ty} (w : A₁ ≼ A) → w ⊚ ≼-refl {A} ≡ w
⊚-idʳ ≼-refl     = refl
⊚-idʳ (≼-ext w)  = cong ≼-ext (⊚-idʳ w)

⊚-assoc : ∀ {A₃ A₂ A₁ A : Ty} (w₃ : A₃ ≼ A₂) (w₂ : A₂ ≼ A₁) (w₁ : A₁ ≼ A) →
           (w₃ ⊚ w₂) ⊚ w₁ ≡ w₃ ⊚ (w₂ ⊚ w₁)
⊚-assoc ≼-refl     w₂ w₁ = refl
⊚-assoc (≼-ext w₃) w₂ w₁ = cong ≼-ext (⊚-assoc w₃ w₂ w₁)

-- A thinning is a morphism (its projection).
toMor : ∀ {A₁ A : Ty} → A₁ ≼ A → Term A₁ A
toMor ≼-refl    = id
toMor (≼-ext w) = toMor w ∘ fst

------------------------------------------------------------------------
-- The semantic domain: neutrals and values, indexed by source `A`.
-- Neutrals are headed by a THINNING (the weakenable "variable").
------------------------------------------------------------------------

data Ne (A : Ty) : Ty → Set
data Val (A : Ty) : Ty → Set

data Ne A where
  nThin : ∀ {B}     → A ≼ B → Ne A B
  nFst  : ∀ {X Y}   → Ne A (X * Y) → Ne A X
  nSnd  : ∀ {X Y}   → Ne A (X * Y) → Ne A Y
  nCase : ∀ {X Y B} → Term X B → Term Y B → Ne A (X + Y) → Ne A B
  nOut  : ∀ {F}     → Ne A (μ F) → Ne A (⟦ F ⟧F (μ F))
  nCata : ∀ F {C}   → Term (⟦ F ⟧F C) C → Ne A (μ F) → Ne A C
  -- `fmap (cata F alg)` applied to a functor-position neutral (the sound,
  -- STRUCTURAL residual — weakens without the `t ∘ id` junk that would break
  -- the strict functor laws).
  nMap  : ∀ F {C} G → Term (⟦ F ⟧F C) C → Ne A (⟦ G ⟧F (μ F)) → Ne A (⟦ G ⟧F C)

data Val A where
  vUnit : Val A Unit
  vPair : ∀ {X Y} → Val A X → Val A Y → Val A (X * Y)
  vInl  : ∀ {X Y} → Val A X → Val A (X + Y)
  vInr  : ∀ {X Y} → Val A Y → Val A (X + Y)
  vIn   : ∀ {F}   → Val A (⟦ F ⟧F (μ F)) → Val A (μ F)
  vNe   : ∀ {B}   → Ne A B → Val A B

------------------------------------------------------------------------
-- The presheaf action: weakening along a thinning.
------------------------------------------------------------------------

wkNe  : ∀ {A₁ A B : Ty} → A₁ ≼ A → Ne A B → Ne A₁ B
wkVal : ∀ {A₁ A B : Ty} → A₁ ≼ A → Val A B → Val A₁ B

wkNe w (nThin wₕ)     = nThin (w ⊚ wₕ)
wkNe w (nFst ne)      = nFst (wkNe w ne)
wkNe w (nSnd ne)      = nSnd (wkNe w ne)
wkNe w (nCase f g ne) = nCase f g (wkNe w ne)
wkNe w (nOut ne)      = nOut (wkNe w ne)
wkNe w (nCata F a ne) = nCata F a (wkNe w ne)
wkNe w (nMap F G a ne) = nMap F G a (wkNe w ne)

wkVal w vUnit       = vUnit
wkVal w (vPair a b) = vPair (wkVal w a) (wkVal w b)
wkVal w (vInl a)    = vInl (wkVal w a)
wkVal w (vInr b)    = vInr (wkVal w b)
wkVal w (vIn x)     = vIn (wkVal w x)
wkVal w (vNe ne)    = vNe (wkNe w ne)

------------------------------------------------------------------------
-- FUNCTOR LAWS (the presheaf structure) — proven.
--   wk ≼-refl        ≡ id
--   wk (w₂ ⊚ w₁)    ≡ wk w₂ ∘ wk w₁
------------------------------------------------------------------------

wkNe-id  : ∀ {A B} (ne : Ne A B) → wkNe (≼-refl {A}) ne ≡ ne
wkVal-id : ∀ {A B} (v  : Val A B) → wkVal (≼-refl {A}) v ≡ v

wkNe-id (nThin wₕ)     = refl                        -- ≼-refl ⊚ wₕ = wₕ (definitional)
wkNe-id (nFst ne)      = cong nFst (wkNe-id ne)
wkNe-id (nSnd ne)      = cong nSnd (wkNe-id ne)
wkNe-id (nCase f g ne) = cong (nCase f g) (wkNe-id ne)
wkNe-id (nOut ne)      = cong nOut (wkNe-id ne)
wkNe-id (nCata F a ne) = cong (nCata F a) (wkNe-id ne)
wkNe-id (nMap F G a ne) = cong (nMap F G a) (wkNe-id ne)

wkVal-id vUnit       = refl
wkVal-id (vPair a b) = cong₂ vPair (wkVal-id a) (wkVal-id b)
wkVal-id (vInl a)    = cong vInl (wkVal-id a)
wkVal-id (vInr b)    = cong vInr (wkVal-id b)
wkVal-id (vIn x)     = cong vIn (wkVal-id x)
wkVal-id (vNe ne)    = cong vNe (wkNe-id ne)

wkNe-comp  : ∀ {A₂ A₁ A B : Ty} (w₂ : A₂ ≼ A₁) (w₁ : A₁ ≼ A) (ne : Ne A B) →
             wkNe (w₂ ⊚ w₁) ne ≡ wkNe w₂ (wkNe w₁ ne)
wkVal-comp : ∀ {A₂ A₁ A B : Ty} (w₂ : A₂ ≼ A₁) (w₁ : A₁ ≼ A) (v : Val A B) →
             wkVal (w₂ ⊚ w₁) v ≡ wkVal w₂ (wkVal w₁ v)

wkNe-comp w₂ w₁ (nThin wₕ)     = cong nThin (⊚-assoc w₂ w₁ wₕ)
wkNe-comp w₂ w₁ (nFst ne)      = cong nFst (wkNe-comp w₂ w₁ ne)
wkNe-comp w₂ w₁ (nSnd ne)      = cong nSnd (wkNe-comp w₂ w₁ ne)
wkNe-comp w₂ w₁ (nCase f g ne) = cong (nCase f g) (wkNe-comp w₂ w₁ ne)
wkNe-comp w₂ w₁ (nOut ne)      = cong nOut (wkNe-comp w₂ w₁ ne)
wkNe-comp w₂ w₁ (nCata F a ne) = cong (nCata F a) (wkNe-comp w₂ w₁ ne)
wkNe-comp w₂ w₁ (nMap F G a ne) = cong (nMap F G a) (wkNe-comp w₂ w₁ ne)

wkVal-comp w₂ w₁ vUnit       = refl
wkVal-comp w₂ w₁ (vPair a b) = cong₂ vPair (wkVal-comp w₂ w₁ a) (wkVal-comp w₂ w₁ b)
wkVal-comp w₂ w₁ (vInl a)    = cong vInl (wkVal-comp w₂ w₁ a)
wkVal-comp w₂ w₁ (vInr b)    = cong vInr (wkVal-comp w₂ w₁ b)
wkVal-comp w₂ w₁ (vIn x)     = cong vIn (wkVal-comp w₂ w₁ x)
wkVal-comp w₂ w₁ (vNe ne)    = cong vNe (wkNe-comp w₂ w₁ ne)

------------------------------------------------------------------------
-- reflect / reify against this presheaf (the mediating pair).
------------------------------------------------------------------------

reflect : ∀ {A} B → Ne A B → Val A B
reflect Void    ne = vNe ne
reflect Unit    ne = vUnit
reflect (X * Y) ne = vPair (reflect X (nFst ne)) (reflect Y (nSnd ne))
reflect (X + Y) ne = vNe ne
reflect (X ⇒ Y) ne = vNe ne
reflect (μ F)   ne = vNe ne

reifyVal : ∀ {A B} → Val A B → Term A B
reifyNe  : ∀ {A B} → Ne A B → Term A B
reifyVal vUnit       = terminal
reifyVal (vPair a b) = ⟨ reifyVal a , reifyVal b ⟩
reifyVal (vInl a)    = inl ∘ reifyVal a
reifyVal (vInr b)    = inr ∘ reifyVal b
reifyVal (vIn x)     = In ∘ reifyVal x
reifyVal (vNe ne)    = reifyNe ne
reifyNe (nThin w)    = toMor w
reifyNe (nFst ne)    = fst ∘ reifyNe ne
reifyNe (nSnd ne)    = snd ∘ reifyNe ne
reifyNe (nCase f g ne) = [ f , g ] ∘ reifyNe ne
reifyNe (nOut ne)    = Out ∘ reifyNe ne
reifyNe (nCata F a ne) = cata F a ∘ reifyNe ne
reifyNe (nMap F G a ne) = fmap G (cata F a) ∘ reifyNe ne

------------------------------------------------------------------------
-- Next, on this foundation: (1) `eval` into the presheaf (a fragment
-- syntax without `⇒`), (2) the Kripke `⇒` function space (uses `wkVal`),
-- (3) the adequacy logical relation (a Kripke relation over `_≼_`, using
-- the functor laws above), extended ONE clause per former.
------------------------------------------------------------------------
