------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — step 2: the Kripke `⇒`
--
-- Adds the function space to the presheaf NbE, on the `{Unit, ×, ⇒}`
-- fragment (classic Kripke NbE), reusing NbEK's thinning category `_≼_`.
-- Reify-under-a-binder introduces a fresh variable in the EXTENDED context
-- `A * X` (its second projection, `nSnd (nThin ≼-refl)`) — which is exactly
-- why the presheaf/weakening infrastructure was the prerequisite: the closure
-- captured at `A` is weakened to `A * X` via `wkVal`.
--
-- Honest escapes (both standard for NbE with a function space):
--   · NO_POSITIVITY_CHECK on `Val` — the Kripke function space
--     `∀ {A'} → A' ≼ A → Val A' X → Val A' Y` puts `Val` negatively. This is
--     the known cost of an inductive domain carrying functions; the principled
--     alternatives (defunctionalised closures, or STC) remove it at real cost.
--   · TERMINATING on `eval` — standard NbE termination (a theorem via
--     adequacy, step 3).
-- `reflect`/`reify` need no pragma (structural on the type).
------------------------------------------------------------------------

module poc.OCP0009.NbEKF where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEK using (_≼_; ≼-refl; ≼-ext; _⊚_)

------------------------------------------------------------------------
-- Fragment syntax `{Unit, ×, ⇒}`.
------------------------------------------------------------------------

infixr 30 _⊙_
data Tm : Ty → Ty → Set where
  idT    : ∀ {A} → Tm A A
  _⊙_    : ∀ {A B D} → Tm B D → Tm A B → Tm A D
  fstT   : ∀ {A B} → Tm (A * B) A
  sndT   : ∀ {A B} → Tm (A * B) B
  pair   : ∀ {A B D} → Tm D A → Tm D B → Tm D (A * B)
  termT  : ∀ {A} → Tm A Unit
  curryT : ∀ {A B D} → Tm (A * B) D → Tm A (B ⇒ D)
  appT   : ∀ {A B} → Tm ((A ⇒ B) * A) B

toMor : ∀ {A₁ A : Ty} → A₁ ≼ A → C.Term A₁ A
toMor ≼-refl    = C.id
toMor (≼-ext w) = toMor w C.∘ C.fst

emb : ∀ {A B} → Tm A B → C.Term A B
emb idT        = C.id
emb (f ⊙ g)    = emb f C.∘ emb g
emb fstT       = C.fst
emb sndT       = C.snd
emb (pair f g) = C.⟨ emb f , emb g ⟩
emb termT      = C.terminal
emb (curryT f) = C.curry (emb f)
emb appT       = C.apply

------------------------------------------------------------------------
-- The semantic domain, with a Kripke function space.
------------------------------------------------------------------------

data Ne (A : Ty) : Ty → Set
{-# NO_POSITIVITY_CHECK #-}
data Val (A : Ty) : Ty → Set

data Ne A where
  nThin : ∀ {B}   → A ≼ B → Ne A B
  nFst  : ∀ {X Y} → Ne A (X * Y) → Ne A X
  nSnd  : ∀ {X Y} → Ne A (X * Y) → Ne A Y
  nApp  : ∀ {X Y} → Ne A (X ⇒ Y) → C.Term A X → Ne A Y

data Val A where
  vUnit : Val A Unit
  vPair : ∀ {X Y} → Val A X → Val A Y → Val A (X * Y)
  vLam  : ∀ {X Y} → (∀ {A₁} → A₁ ≼ A → Val A₁ X → Val A₁ Y) → Val A (X ⇒ Y)
  vNe   : ∀ {B}   → Ne A B → Val A B

------------------------------------------------------------------------
-- Weakening (the presheaf action; the Kripke closure pre-composes `_⊚_`).
------------------------------------------------------------------------

wkNe  : ∀ {A₁ A B : Ty} → A₁ ≼ A → Ne A B → Ne A₁ B
wkVal : ∀ {A₁ A B : Ty} → A₁ ≼ A → Val A B → Val A₁ B
wkNe w (nThin wₕ)  = nThin (w ⊚ wₕ)
wkNe w (nFst ne)   = nFst (wkNe w ne)
wkNe w (nSnd ne)   = nSnd (wkNe w ne)
wkNe w (nApp ne t) = nApp (wkNe w ne) (t C.∘ toMor w)
wkVal w vUnit       = vUnit
wkVal w (vPair a b) = vPair (wkVal w a) (wkVal w b)
wkVal w (vLam f)    = vLam (λ w₁ x → f (w₁ ⊚ w) x)
wkVal w (vNe ne)    = vNe (wkNe w ne)

------------------------------------------------------------------------
-- reflect / reify (mutual, structural on the type).
------------------------------------------------------------------------

reflect  : ∀ {A} B → Ne A B → Val A B
reifyVal : ∀ {A B} → Val A B → C.Term A B
reifyNe  : ∀ {A B} → Ne A B → C.Term A B

reflect Unit    ne = vUnit
reflect (X * Y) ne = vPair (reflect X (nFst ne)) (reflect Y (nSnd ne))
reflect (X ⇒ Y) ne = vLam (λ w x → reflect Y (nApp (wkNe w ne) (reifyVal x)))
reflect Void    ne = vNe ne
reflect (X + Y) ne = vNe ne
reflect (μ F)   ne = vNe ne

reifyVal vUnit       = C.terminal
reifyVal (vPair a b) = C.⟨ reifyVal a , reifyVal b ⟩
-- reify a function: bind a fresh variable = `snd` of the extended source A*X
reifyVal (vLam {X = X} f) =
  C.curry (reifyVal (f (≼-ext ≼-refl) (reflect X (nSnd (nThin ≼-refl)))))
reifyVal (vNe ne)    = reifyNe ne
reifyNe (nThin w)  = toMor w
reifyNe (nFst ne)  = C.fst C.∘ reifyNe ne
reifyNe (nSnd ne)  = C.snd C.∘ reifyNe ne
reifyNe (nApp ne t) = C.apply C.∘ C.⟨ reifyNe ne , t ⟩

------------------------------------------------------------------------
-- Evaluation (β for products and functions).
------------------------------------------------------------------------

vfst : ∀ {A X Y} → Val A (X * Y) → Val A X
vfst (vPair a _) = a
vfst (vNe ne)    = vNe (nFst ne)

vsnd : ∀ {A X Y} → Val A (X * Y) → Val A Y
vsnd (vPair _ b) = b
vsnd (vNe ne)    = vNe (nSnd ne)

-- semantic application (function β; stuck on a neutral)
vapp : ∀ {A X Y} → Val A (X ⇒ Y) → Val A X → Val A Y
vapp (vLam f) x = f ≼-refl x
vapp (vNe ne) x = vNe (nApp ne (reifyVal x))

{-# TERMINATING #-}
eval : ∀ {A B D} → Tm B D → Val A B → Val A D
eval idT        v = v
eval (f ⊙ g)    v = eval f (eval g v)
eval fstT       v = vfst v
eval sndT       v = vsnd v
eval (pair f g) v = vPair (eval f v) (eval g v)
eval termT      v = vUnit
eval (curryT f) v = vLam (λ w x → eval f (vPair (wkVal w v) x))
eval appT       v = vapp (vfst v) (vsnd v)

nf : ∀ {A B} → Tm A B → C.Term A B
nf {A} t = reifyVal (eval t (reflect A (nThin ≼-refl)))

------------------------------------------------------------------------
-- Examples — FUNCTIONS now normalize (β and η).
------------------------------------------------------------------------

B₂ : Ty
B₂ = Unit + Unit

-- η for functions: `curry (app)` (the identity-ish) reifies η-long. The two
-- sides below are the identity function on `B₂ ⇒ B₂`, decided by `nf`.
--   λ f. f      vs   λ f. λ x. f x
idFun : Tm Unit ((B₂ ⇒ B₂) ⇒ (B₂ ⇒ B₂))
idFun = curryT sndT

etaFun : Tm Unit ((B₂ ⇒ B₂) ⇒ (B₂ ⇒ B₂))
etaFun = curryT (curryT (appT ⊙ pair (sndT ⊙ fstT) sndT))

_ : nf idFun ≡ nf etaFun
_ = refl

-- β for functions: apply ∘ ⟨ curry snd , g ⟩  ≋  g  (const-id applied)
kApp : Tm B₂ B₂
kApp = appT ⊙ pair (curryT sndT) idT

_ : nf kApp ≡ nf idT
_ = refl
