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
-- NO escapes: the semantic domain `Val` is defined by RECURSION ON THE TYPE
-- (a Tarski-style presheaf semantics) rather than as an inductive datatype.
-- The Kripke function space `∀ {A'} → A' ≼ A → Val A' X → Val A' Y` then
-- lives in a Set-valued function, so there is no positivity question at all
-- (an inductive `Val` with that field needs NO_POSITIVITY_CHECK — the known
-- cost of an inductive domain carrying functions). Neutrals `Ne` stay a
-- first-order, strictly positive datatype (`nApp` stores an already-reified
-- `C.Term`). With the domain type-recursive, `eval` is structurally
-- recursive on `Tm` and `reflect`/`reify` on the type — no TERMINATING
-- pragma either, so the whole module compiles under `--safe`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
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
--
-- Neutrals: first-order and strictly positive (function arguments are
-- stored already reified, as `C.Term`s).
------------------------------------------------------------------------

data Ne (A : Ty) : Ty → Set where
  nThin : ∀ {B}   → A ≼ B → Ne A B
  nFst  : ∀ {X Y} → Ne A (X * Y) → Ne A X
  nSnd  : ∀ {X Y} → Ne A (X * Y) → Ne A Y
  nApp  : ∀ {X Y} → Ne A (X ⇒ Y) → C.Term A X → Ne A Y

-- Values, by recursion on the type: η-expanded at `Unit`/`*`/`⇒`, neutral
-- at the fragment-external types (`Void`/`+`/`μ` only enter via the initial
-- environment).
Val : Ty → Ty → Set
Val A Unit    = ⊤
Val A (X * Y) = Val A X × Val A Y
Val A (X ⇒ Y) = ∀ {A₁} → A₁ ≼ A → Val A₁ X → Val A₁ Y
Val A Void    = Ne A Void
Val A (X + Y) = Ne A (X + Y)
Val A (μ F)   = Ne A (μ F)

------------------------------------------------------------------------
-- Weakening (the presheaf action; the Kripke closure pre-composes `_⊚_`).
------------------------------------------------------------------------

wkNe : ∀ {A₁ A B : Ty} → A₁ ≼ A → Ne A B → Ne A₁ B
wkNe w (nThin wₕ)  = nThin (w ⊚ wₕ)
wkNe w (nFst ne)   = nFst (wkNe w ne)
wkNe w (nSnd ne)   = nSnd (wkNe w ne)
wkNe w (nApp ne t) = nApp (wkNe w ne) (t C.∘ toMor w)

-- `Val` is not injective in its type index, so the type is passed explicitly.
wkVal : ∀ {A₁ A : Ty} B → A₁ ≼ A → Val A B → Val A₁ B
wkVal Unit    w v       = tt
wkVal (X * Y) w (a , b) = wkVal X w a , wkVal Y w b
wkVal (X ⇒ Y) w f       = λ w₁ x → f (w₁ ⊚ w) x
wkVal Void    w ne      = wkNe w ne
wkVal (X + Y) w ne      = wkNe w ne
wkVal (μ F)   w ne      = wkNe w ne

------------------------------------------------------------------------
-- reflect / reify (mutual, structural on the type).
------------------------------------------------------------------------

reflect  : ∀ {A} B → Ne A B → Val A B
reifyVal : ∀ {A} B → Val A B → C.Term A B
reifyNe  : ∀ {A B} → Ne A B → C.Term A B

reflect Unit    ne = tt
reflect (X * Y) ne = reflect X (nFst ne) , reflect Y (nSnd ne)
reflect (X ⇒ Y) ne = λ w x → reflect Y (nApp (wkNe w ne) (reifyVal X x))
reflect Void    ne = ne
reflect (X + Y) ne = ne
reflect (μ F)   ne = ne

reifyVal Unit    v       = C.terminal
reifyVal (X * Y) (a , b) = C.⟨ reifyVal X a , reifyVal Y b ⟩
-- reify a function: bind a fresh variable = `snd` of the extended source A*X
reifyVal (X ⇒ Y) f =
  C.curry (reifyVal Y (f (≼-ext ≼-refl) (reflect X (nSnd (nThin ≼-refl)))))
reifyVal Void    ne = reifyNe ne
reifyVal (X + Y) ne = reifyNe ne
reifyVal (μ F)   ne = reifyNe ne

reifyNe (nThin w)   = toMor w
reifyNe (nFst ne)   = C.fst C.∘ reifyNe ne
reifyNe (nSnd ne)   = C.snd C.∘ reifyNe ne
reifyNe (nApp ne t) = C.apply C.∘ C.⟨ reifyNe ne , t ⟩

------------------------------------------------------------------------
-- Evaluation (β for products and functions) — structural on the term.
------------------------------------------------------------------------

eval : ∀ {A B D} → Tm B D → Val A B → Val A D
eval idT                v       = v
eval (f ⊙ g)            v       = eval f (eval g v)
eval fstT               (a , _) = a
eval sndT               (_ , b) = b
eval (pair f g)         v       = eval f v , eval g v
eval termT              v       = tt
eval (curryT {A = S} f) v       = λ w x → eval f (wkVal S w v , x)
eval appT               (f , a) = f ≼-refl a

nf : ∀ {A B} → Tm A B → C.Term A B
nf {A} {B} t = reifyVal B (eval t (reflect A (nThin ≼-refl)))

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
