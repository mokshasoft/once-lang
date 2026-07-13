------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — the FULL fragment `{Unit, ×, +, μ, ⇒}`
--
-- One engine for the whole fragment: `NbEP`'s `{Unit,×,+,μ}` (recursion)
-- and `NbEKF`'s `{Unit,×,⇒}` (Kripke functions) MERGED. The classically
-- hard sums+functions combination is hard only for positive η (sum-η needs
-- sheaf/case-tree NbE); our §2 design excludes positive η from the core, so
-- the β + negative-η theory merges cleanly — this module is the proof.
--
-- Domain design (all `--safe`, no pragmas):
--   * `Val` by RECURSION ON THE TYPE (Tarski-style presheaf semantics, as in
--     the `NbEKF` rewrite): `⇒` is the Kripke function space as a Set-valued
--     function (no positivity question), `Unit`/`×` are η-long by
--     construction, `+` is a sum-of-values-or-neutral, `Void` is neutral.
--   * `μ` via a TWO-LAYER INDUCTIVE domain: `MuVal` (a `μ`-value is `vIn` of
--     a functor layer, or neutral) and `ValF` (the functor layer, with
--     recursive positions being `MuVal`s). Plain mutual inductives —
--     strictly positive (functors have no arrows), no induction-recursion.
--   * BONUS over `NbEP`: η-long products are DEFINITIONAL in `ValF` (`⊗` has
--     only `vfPair` — no neutral constructor), so the mapCata-on-a-product-
--     neutral case that `NbEP` excluded via the `Normal` predicate is
--     unrepresentable here. The invariant became a data-type shape.
--   * `toV`/`frV` convert between the functor layer and the type-recursive
--     `Val` at `⟦ G ⟧F (μ F)` (structural on the functor code).
--
-- Termination: the same lexicographic (Tm, Val) descent as `NbEP` — every
-- call cycle either strictly shrinks the term or keeps it and shrinks the
-- value — accepted by Agda's size-change checker, no pragma.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPF where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import poc.OCP0009.NbEK using (_≼_; ≼-refl; ≼-ext; _⊚_)
open import poc.OCP0009.NbEPTm as T using ()

------------------------------------------------------------------------
-- Full fragment syntax `{Unit, ×, +, μ, ⇒}`.
------------------------------------------------------------------------

infixr 30 _⊙_
data Tm : Ty → Ty → Set where
  idT    : ∀ {A} → Tm A A
  _⊙_    : ∀ {A B D} → Tm B D → Tm A B → Tm A D
  fstT   : ∀ {A B} → Tm (A * B) A
  sndT   : ∀ {A B} → Tm (A * B) B
  pair   : ∀ {A B D} → Tm D A → Tm D B → Tm D (A * B)
  inlT   : ∀ {A B} → Tm A (A + B)
  inrT   : ∀ {A B} → Tm B (A + B)
  case   : ∀ {A B D} → Tm A D → Tm B D → Tm (A + B) D
  termT  : ∀ {A} → Tm A Unit
  InT    : ∀ {F} → Tm (⟦ F ⟧F (μ F)) (μ F)
  OutT   : ∀ {F} → Tm (μ F) (⟦ F ⟧F (μ F))
  cataT  : ∀ F {A} → Tm (⟦ F ⟧F A) A → Tm (μ F) A
  curryT : ∀ {A B D} → Tm (A * B) D → Tm A (B ⇒ D)
  appT   : ∀ {A B} → Tm ((A ⇒ B) * A) B

emb : ∀ {A B} → Tm A B → C.Term A B
emb idT         = C.id
emb (f ⊙ g)     = emb f C.∘ emb g
emb fstT        = C.fst
emb sndT        = C.snd
emb (pair f g)  = C.⟨ emb f , emb g ⟩
emb inlT        = C.inl
emb inrT        = C.inr
emb (case f g)  = C.[ emb f , emb g ]
emb termT       = C.terminal
emb InT         = C.In
emb OutT        = C.Out
emb (cataT F a) = C.cata F (emb a)
emb (curryT f)  = C.curry (emb f)
emb appT        = C.apply

-- The `{Unit,×,+,μ}` fragment injects (so `NbEPTm`'s numerals come for free).
inj : ∀ {A B} → T.Tm A B → Tm A B
inj T.idT         = idT
inj (f T.⊙ g)     = inj f ⊙ inj g
inj T.fstT        = fstT
inj T.sndT        = sndT
inj (T.pair f g)  = pair (inj f) (inj g)
inj T.inlT        = inlT
inj T.inrT        = inrT
inj (T.case f g)  = case (inj f) (inj g)
inj T.termT       = termT
inj T.InT         = InT
inj T.OutT        = OutT
inj (T.cataT F a) = cataT F (inj a)

toMor : ∀ {A₁ A : Ty} → A₁ ≼ A → C.Term A₁ A
toMor ≼-refl    = C.id
toMor (≼-ext w) = toMor w C.∘ C.fst

------------------------------------------------------------------------
-- Neutrals — the union of both engines' neutrals, first-order and strictly
-- positive (branches/arguments stored already reified, as `C.Term`s).
------------------------------------------------------------------------

data Ne (A : Ty) : Ty → Set where
  nThin : ∀ {B}     → A ≼ B → Ne A B
  nFst  : ∀ {X Y}   → Ne A (X * Y) → Ne A X
  nSnd  : ∀ {X Y}   → Ne A (X * Y) → Ne A Y
  nApp  : ∀ {X Y}   → Ne A (X ⇒ Y) → C.Term A X → Ne A Y
  nCase : ∀ {X Y B} → C.Term X B → C.Term Y B → Ne A (X + Y) → Ne A B
  nOut  : ∀ {F}     → Ne A (μ F) → Ne A (⟦ F ⟧F (μ F))
  nCata : ∀ F {D}   → C.Term (⟦ F ⟧F D) D → Ne A (μ F) → Ne A D
  nMap  : ∀ F {D} G → C.Term (⟦ F ⟧F D) D → Ne A (⟦ G ⟧F (μ F)) → Ne A (⟦ G ⟧F D)

------------------------------------------------------------------------
-- The semantic domain. `μ` gets a two-layer inductive domain; everything
-- else is by recursion on the type.
------------------------------------------------------------------------

data MuVal (A : Ty) : Func → Set
data ValF  (A : Ty) (F : Func) : Func → Set

data MuVal A where
  vIn  : ∀ {F} → ValF A F F → MuVal A F
  vNeμ : ∀ {F} → Ne A (μ F) → MuVal A F

data ValF A F where
  vfId   : MuVal A F → ValF A F Id
  vfOne  : ValF A F One
  vfKc   : ∀ {H}   → MuVal A H → ValF A F (Kc H)
  vfInl  : ∀ {G H} → ValF A F G → ValF A F (G ⊕ H)
  vfInr  : ∀ {G H} → ValF A F H → ValF A F (G ⊕ H)
  vfNe⊕  : ∀ {G H} → Ne A (⟦ G ⊕ H ⟧F (μ F)) → ValF A F (G ⊕ H)
  -- NOTE: `⊗` has NO neutral constructor — products are η-long by the shape
  -- of the datatype. (`NbEP` needed the `Normal` predicate for this.)
  vfPair : ∀ {G H} → ValF A F G → ValF A F H → ValF A F (G ⊗ H)

Val : Ty → Ty → Set
Val A Void    = Ne A Void
Val A Unit    = ⊤
Val A (X * Y) = Val A X × Val A Y
Val A (X + Y) = (Val A X ⊎ Val A Y) ⊎ Ne A (X + Y)
Val A (X ⇒ Y) = ∀ {A₁} → A₁ ≼ A → Val A₁ X → Val A₁ Y
Val A (μ F)   = MuVal A F

-- The functor layer vs the type-recursive `Val` at `⟦ G ⟧F (μ F)`:
-- conversions, structural on the functor code.
toV : ∀ {A F} G → ValF A F G → Val A (⟦ G ⟧F (μ F))
toV Id      (vfId m)     = m
toV One     vfOne        = tt
toV (Kc H)  (vfKc m)     = m
toV (G ⊕ H) (vfInl x)    = inj₁ (inj₁ (toV G x))
toV (G ⊕ H) (vfInr y)    = inj₁ (inj₂ (toV H y))
toV (G ⊕ H) (vfNe⊕ ne)   = inj₂ ne
toV (G ⊗ H) (vfPair x y) = toV G x , toV H y

frV : ∀ {A F} G → Val A (⟦ G ⟧F (μ F)) → ValF A F G
frV Id      m               = vfId m
frV One     v               = vfOne
frV (Kc H)  m               = vfKc m
frV (G ⊕ H) (inj₁ (inj₁ x)) = vfInl (frV G x)
frV (G ⊕ H) (inj₁ (inj₂ y)) = vfInr (frV H y)
frV (G ⊕ H) (inj₂ ne)       = vfNe⊕ ne
frV (G ⊗ H) (x , y)         = vfPair (frV G x) (frV H y)

------------------------------------------------------------------------
-- Weakening (the presheaf action).
------------------------------------------------------------------------

wkNe : ∀ {A₁ A B : Ty} → A₁ ≼ A → Ne A B → Ne A₁ B
wkNe w (nThin wₕ)      = nThin (w ⊚ wₕ)
wkNe w (nFst ne)       = nFst (wkNe w ne)
wkNe w (nSnd ne)       = nSnd (wkNe w ne)
wkNe w (nApp ne t)     = nApp (wkNe w ne) (t C.∘ toMor w)
wkNe w (nCase f g ne)  = nCase f g (wkNe w ne)
wkNe w (nOut ne)       = nOut (wkNe w ne)
wkNe w (nCata F a ne)  = nCata F a (wkNe w ne)
wkNe w (nMap F G a ne) = nMap F G a (wkNe w ne)

wkMu : ∀ {A₁ A F} → A₁ ≼ A → MuVal A F → MuVal A₁ F
wkF  : ∀ {A₁ A F} G → A₁ ≼ A → ValF A F G → ValF A₁ F G
wkMu w (vIn {F} x) = vIn (wkF F w x)
wkMu w (vNeμ ne)   = vNeμ (wkNe w ne)
wkF Id      w (vfId m)     = vfId (wkMu w m)
wkF One     w vfOne        = vfOne
wkF (Kc H)  w (vfKc m)     = vfKc (wkMu w m)
wkF (G ⊕ H) w (vfInl x)    = vfInl (wkF G w x)
wkF (G ⊕ H) w (vfInr y)    = vfInr (wkF H w y)
wkF (G ⊕ H) w (vfNe⊕ ne)   = vfNe⊕ (wkNe w ne)
wkF (G ⊗ H) w (vfPair x y) = vfPair (wkF G w x) (wkF H w y)

wkVal : ∀ {A₁ A : Ty} B → A₁ ≼ A → Val A B → Val A₁ B
wkVal Void    w ne              = wkNe w ne
wkVal Unit    w v               = tt
wkVal (X * Y) w (a , b)         = wkVal X w a , wkVal Y w b
wkVal (X + Y) w (inj₁ (inj₁ a)) = inj₁ (inj₁ (wkVal X w a))
wkVal (X + Y) w (inj₁ (inj₂ b)) = inj₁ (inj₂ (wkVal Y w b))
wkVal (X + Y) w (inj₂ ne)       = inj₂ (wkNe w ne)
wkVal (X ⇒ Y) w f               = λ w₁ x → f (w₁ ⊚ w) x
wkVal (μ F)   w m               = wkMu w m

------------------------------------------------------------------------
-- reflect / reify (structural on the type / the μ-domain).
------------------------------------------------------------------------

reflect  : ∀ {A} B → Ne A B → Val A B
reifyVal : ∀ {A} B → Val A B → C.Term A B
reifyMu  : ∀ {A F} → MuVal A F → C.Term A (μ F)
reifyF   : ∀ {A F} G → ValF A F G → C.Term A (⟦ G ⟧F (μ F))
reifyNe  : ∀ {A B} → Ne A B → C.Term A B

reflect Void    ne = ne
reflect Unit    ne = tt
reflect (X * Y) ne = reflect X (nFst ne) , reflect Y (nSnd ne)
reflect (X + Y) ne = inj₂ ne
reflect (X ⇒ Y) ne = λ w x → reflect Y (nApp (wkNe w ne) (reifyVal X x))
reflect (μ F)   ne = vNeμ ne

reifyVal Void    ne              = reifyNe ne
reifyVal Unit    v               = C.terminal
reifyVal (X * Y) (a , b)         = C.⟨ reifyVal X a , reifyVal Y b ⟩
reifyVal (X + Y) (inj₁ (inj₁ a)) = C.inl C.∘ reifyVal X a
reifyVal (X + Y) (inj₁ (inj₂ b)) = C.inr C.∘ reifyVal Y b
reifyVal (X + Y) (inj₂ ne)       = reifyNe ne
reifyVal (X ⇒ Y) f =
  C.curry (reifyVal Y (f (≼-ext ≼-refl) (reflect X (nSnd (nThin ≼-refl)))))
reifyVal (μ F)   m               = reifyMu m

reifyMu (vIn {F} x) = C.In C.∘ reifyF F x
reifyMu (vNeμ ne)   = reifyNe ne

reifyF Id      (vfId m)     = reifyMu m
reifyF One     vfOne        = C.terminal
reifyF (Kc H)  (vfKc m)     = reifyMu m
reifyF (G ⊕ H) (vfInl x)    = C.inl C.∘ reifyF G x
reifyF (G ⊕ H) (vfInr y)    = C.inr C.∘ reifyF H y
reifyF (G ⊕ H) (vfNe⊕ ne)   = reifyNe ne
reifyF (G ⊗ H) (vfPair x y) = C.⟨ reifyF G x , reifyF H y ⟩

reifyNe (nThin w)       = toMor w
reifyNe (nFst ne)       = C.fst C.∘ reifyNe ne
reifyNe (nSnd ne)       = C.snd C.∘ reifyNe ne
reifyNe (nApp ne t)     = C.apply C.∘ C.⟨ reifyNe ne , t ⟩
reifyNe (nCase f g ne)  = C.[ f , g ] C.∘ reifyNe ne
reifyNe (nOut ne)       = C.Out C.∘ reifyNe ne
reifyNe (nCata F a ne)  = C.cata F a C.∘ reifyNe ne
reifyNe (nMap F G a ne) = C.fmap G (C.cata F a) C.∘ reifyNe ne

------------------------------------------------------------------------
-- Evaluation — β for products, sums, functions, and cata; stuck neutrals
-- residualized. Lexicographic (Tm, Val) termination, checker-accepted.
------------------------------------------------------------------------

mutual
  eval : ∀ {A B D} → Tm B D → Val A B → Val A D
  eval idT                v       = v
  eval (f ⊙ g)            v       = eval f (eval g v)
  eval fstT               (a , _) = a
  eval sndT               (_ , b) = b
  eval (pair f g)         v       = eval f v , eval g v
  eval inlT               v       = inj₁ (inj₁ v)
  eval inrT               v       = inj₁ (inj₂ v)
  eval (case f g)         v       = vcase f g v
  eval termT              v       = tt
  eval (InT {F})          v       = vIn (frV F v)
  eval OutT               v       = vout v
  eval (cataT F a)        v       = vcata F a v
  eval (curryT {A = S} f) v       = λ w x → eval f (wkVal S w v , x)
  eval appT               (f , a) = f ≼-refl a

  vout : ∀ {A F} → Val A (μ F) → Val A (⟦ F ⟧F (μ F))
  vout (vIn {F} x)      = toV F x
  vout {F = F} (vNeμ ne) = reflect (⟦ F ⟧F (μ F)) (nOut ne)

  vcase : ∀ {A X Y D} → Tm X D → Tm Y D → Val A (X + Y) → Val A D
  vcase f g (inj₁ (inj₁ a))   = eval f a
  vcase f g (inj₁ (inj₂ b))   = eval g b
  vcase {D = D} f g (inj₂ ne) = reflect D (nCase (nf f) (nf g) ne)

  vcata : ∀ {A} F {D} → Tm (⟦ F ⟧F D) D → Val A (μ F) → Val A D
  vcata F a (vIn x)          = eval a (mapCataF F a F x)
  vcata F {D = D} a (vNeμ ne) = reflect D (nCata F (nf a) ne)

  mapCataF : ∀ {A} F {D} → Tm (⟦ F ⟧F D) D → ∀ G →
             ValF A F G → Val A (⟦ G ⟧F D)
  mapCataF F a Id      (vfId m)     = vcata F a m
  mapCataF F a One     vfOne        = tt
  mapCataF F a (Kc H)  (vfKc m)     = m
  mapCataF F a (G ⊕ H) (vfInl x)    = inj₁ (inj₁ (mapCataF F a G x))
  mapCataF F a (G ⊕ H) (vfInr y)    = inj₁ (inj₂ (mapCataF F a H y))
  mapCataF F a (G ⊕ H) (vfNe⊕ ne)   = inj₂ (nMap F (G ⊕ H) (nf a) ne)
  mapCataF F a (G ⊗ H) (vfPair x y) = mapCataF F a G x , mapCataF F a H y

  nf : ∀ {A B} → Tm A B → C.Term A B
  nf {A} {B} t = reifyVal B (eval t (reflect A (nThin ≼-refl)))

------------------------------------------------------------------------
-- Examples — recursion and functions in ONE engine.
------------------------------------------------------------------------

-- cata-β still normalizes (the `NbEP` examples, through the injection).
_ : nf (inj (T.double T.⊙ T.zero)) ≡ nf (inj T.zero)
_ = refl

_ : nf (inj (T.double T.⊙ T.one)) ≡ nf (inj T.two)
_ = refl

-- THE MONEY EXAMPLE — recursion inside a closure: `(λ n. double n) 1 ≋ 2`.
-- Function β applies the closure; cata-β runs `double` on the argument.
dblApp : Tm Unit T.Nat
dblApp = appT ⊙ pair (curryT (inj T.double ⊙ sndT)) (inj T.one)

_ : nf dblApp ≡ nf (inj T.two)
_ = refl

-- Function η (from `NbEKF`): λ f. f  ≋  λ f. λ x. f x  — decided by `nf`.
B₂ : Ty
B₂ = Unit + Unit

idFun : Tm Unit ((B₂ ⇒ B₂) ⇒ (B₂ ⇒ B₂))
idFun = curryT sndT

etaFun : Tm Unit ((B₂ ⇒ B₂) ⇒ (B₂ ⇒ B₂))
etaFun = curryT (curryT (appT ⊙ pair (sndT ⊙ fstT) sndT))

_ : nf idFun ≡ nf etaFun
_ = refl

-- Product η on a product CONTAINING a function component (reflect at `⇒`
-- under a product — the mixed case neither engine could state before).
Sᶠ : Ty
Sᶠ = (T.Nat ⇒ T.Nat) * T.Nat

_ : nf {Sᶠ} (pair fstT sndT) ≡ nf {Sᶠ} idT
_ = refl

-- Function β where the argument is an OPEN μ-neutral: (λ n. double n)
-- applied to the context variable — the closure's cata goes STUCK on the
-- neutral and residualizes, all under one `nf`.
dblOpen : Tm T.Nat T.Nat
dblOpen = appT ⊙ pair (curryT (inj T.double ⊙ sndT)) idT

_ : nf dblOpen ≡ nf (inj T.double)
_ = refl
