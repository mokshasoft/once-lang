------------------------------------------------------------------------
-- OCP-0009 · W0e/W0d — THE LINEAR CORE, OWNED.
--
-- The linearization line's object language, semantics and payoff theorem, in
-- one self-contained module that DEPENDS ON NOTHING.  No prelude import, no
-- `bootstrap/normalizer/**` (that is another POC), no `formal/Once/**`.
--
-- ★ WHY THAT MATTERS, and why this module exists at all.  `NbEPLinRec` indexes
-- `LTm` by the NORMALIZER POC's `Ty`, and `Dyn`/`Pass`/`QTT` go further,
-- borrowing its `Fix`/`⟦_⟧FS`/`Term`/`eval`.  So the shape of the linear core
-- was being decided by a peer POC's accidental choices — and the moment W0d
-- tried to use it, that peer's limits started getting recorded as OUR
-- constraints: no `ν`, no base types, "`List Int` is out".  None of those were
-- findings about the right shape (PLAN §8.3).  This POC is here to find the
-- structure we want Once to HAVE.  So the structure is declared here, top-down,
-- and `ν` and the base leaves are present BECAUSE THE THEORY WANTS THEM.
--
-- WHAT IS DECIDED HERE, as opposed to inherited:
--
--   * `LF` — polynomial functor codes, kept OBJECT-LANGUAGE-INDEPENDENT.  A
--     constant is `Kone`, an inert leaf `Kb`, or a CODE (`Kμ`/`Kν`) — never an
--     arbitrary `LTy`.  This is a real structural decision, not a copy: it is
--     exactly what makes `Fix` strictly positive with no pragma, and it is what
--     lets `Fix` and the cost-carrying `Nu` share one knot.
--   * `LTy` — with `νt` AND base leaves from the start.
--   * `⟦_⟧` — INSTRUMENTED: `⟦ A ⇒t B ⟧ = ⟦ A ⟧ → ⟦ B ⟧ × ℕ` and `Nu`'s `force`
--     carries a `ℕ`.  Both say the same thing — "the value reports its own
--     cost" — which is W0b's answer for closures (`NbEPLinDyn`) and W0e's for
--     codata (`SpikeLinNu`), now the SAME design decision rather than two.
--   * `LTm` — the full generator set, INCLUDING the three the old core was
--     missing and PLAN §8's coverage table listed as gaps: `lzero` (initial),
--     `lOutμ` (the μ destructor), and `lOut`/`lAna`/`lInν` (codata).
--
-- ★ AND THE PAYOFF THEOREM COVERS BOTH FIXPOINTS.  `dyn-linear` — a `DupFree`
-- morphism on `Free` inputs allocates nothing — now has a `ν` case, where
-- "allocates nothing" is necessarily coinductive (`FreeNu`: every observation,
-- at every depth, is free).  That is the merge of `NbEPLinDyn`'s inductive
-- statement and `SpikeLinNu`'s coinductive one into a single induction.
--
-- Base leaves are PARAMETERS: the theory says only that they are inert (they
-- carry no functor structure and cannot duplicate themselves), and nothing
-- below depends on what an `Int` is.  Committing to a carrier here would be the
-- same bottom-up mistake one level down.
--
-- `--safe --guardedness`, no sized types (hard ban), zero postulates, zero
-- holes, zero imports.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}
module poc.OCP0009.NbEPLinCore
  (Base : Set) (⟦_⟧b : Base → Set) where

------------------------------------------------------------------------
-- 0. PRELUDE.  Local, because sharing a peer POC's prelude is how the
--    coupling starts.
------------------------------------------------------------------------

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B} →
        x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

infix 3 ¬_
¬_ : Set → Set
¬ P = P → ⊥

record ⊤ : Set where
  constructor tt

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

------------------------------------------------------------------------
-- 1. POLYNOMIAL FUNCTOR CODES.
--
-- ★ `LF` mentions no `LTy`.  Its constants are the Unit leaf, an INERT base
-- leaf, or the CODE of another fixpoint — `Kμ`/`Kν`, never an arbitrary object
-- type.  That restriction is the reason `Fix` below is strictly positive with
-- no pragma AND the reason `Fix` and `Nu` can share one interpretation knot.
-- It is also the honest reading of what a functor code is FOR: codes store
-- sub-codes and leaves; a function type is never a functor position.
------------------------------------------------------------------------

infixr 6 _⊕f_
infixr 7 _⊗f_
data LF : Set where
  Idf  : LF
  Kone : LF
  Kb   : Base → LF          -- ★ inert leaf
  Kμ   : LF → LF            -- a code: the initial algebra of another functor
  Kν   : LF → LF            -- ★ a code: the final coalgebra of another functor
  _⊕f_ : LF → LF → LF
  _⊗f_ : LF → LF → LF

------------------------------------------------------------------------
-- 2. THE OBJECT LANGUAGE.
------------------------------------------------------------------------

infixr 5 _⊗t_
infixr 4 _⊕t_
infixr 3 _⇒t_
data LTy : Set where
  One  : LTy
  Zero : LTy
  _⊗t_ : LTy → LTy → LTy
  _⊕t_ : LTy → LTy → LTy
  _⇒t_ : LTy → LTy → LTy
  μt   : LF → LTy
  νt   : LF → LTy          -- ★ present because the theory wants it
  Bt   : Base → LTy        -- ★ likewise

-- the functor acting on object types
LF∙ : LF → LTy → LTy
LF∙ Idf       X = X
LF∙ Kone      X = One
LF∙ (Kb b)    X = Bt b
LF∙ (Kμ G)    X = μt G
LF∙ (Kν G)    X = νt G
LF∙ (F ⊕f G)  X = LF∙ F X ⊕t LF∙ G X
LF∙ (F ⊗f G)  X = LF∙ F X ⊗t LF∙ G X

------------------------------------------------------------------------
-- 3. ★ THE INSTRUMENTED SEMANTICS — one knot for both fixpoints.
--
-- `Fix` (inductive, a `data`) and `Nu` (coinductive, a `record` whose `force`
-- carries the step's price) share `FS`.  Putting them in ONE mutual block is
-- the payoff of §1's restriction on `LF`: neither interpretation mentions
-- `⟦_⟧`, so `⇒t`'s negative occurrence cannot taint either one's positivity.
------------------------------------------------------------------------

mutual
  FS : LF → Set → Set
  FS Idf      X = X
  FS Kone     X = ⊤
  FS (Kb b)   X = ⟦ b ⟧b
  FS (Kμ G)   X = Fix G
  FS (Kν G)   X = Nu G
  FS (F ⊕f G) X = FS F X ⊎ FS G X
  FS (F ⊗f G) X = FS F X × FS G X

  data Fix (F : LF) : Set where
    fix : FS F (Fix F) → Fix F

  -- ★ unfolding reports its own cost.  The `ν` analogue of a closure reporting
  -- its own cost — the same decision, at the other fixpoint.
  record Nu (F : LF) : Set where
    coinductive
    field force : FS F (Nu F) × ℕ
open Nu

unfix : ∀ {F} → Fix F → FS F (Fix F)
unfix (fix w) = w

-- building one layer of a `ν` costs nothing extra: the layer is already there.
mkNu : ∀ {F} → FS F (Nu F) → Nu F
force (mkNu w) = (w , zero)

⟦_⟧ : LTy → Set
⟦ One ⟧      = ⊤
⟦ Zero ⟧     = ⊥
⟦ A ⊗t B ⟧   = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⊕t B ⟧   = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒t B ⟧   = ⟦ A ⟧ → ⟦ B ⟧ × ℕ    -- ★ a function reports its own cost
⟦ μt F ⟧     = Fix F
⟦ νt F ⟧     = Nu F
⟦ Bt b ⟧     = ⟦ b ⟧b

------------------------------------------------------------------------
-- 4. THE COST (WRITER) MONAD, and the functor coherence.
------------------------------------------------------------------------

retᶜ : ∀ {X : Set} → X → X × ℕ
retᶜ x = (x , zero)

infixl 1 _>>=ᶜ_
_>>=ᶜ_ : ∀ {X Y : Set} → X × ℕ → (X → Y × ℕ) → Y × ℕ
(x , m) >>=ᶜ k = (fst (k x) , (m +ℕ snd (k x)))

-- `⟦ LF∙ F X ⟧ ≅ FS F ⟦ X ⟧` — an identity on every leaf, by construction.
coh : ∀ F X → ⟦ LF∙ F X ⟧ → FS F ⟦ X ⟧
coh Idf      X x        = x
coh Kone     X x        = x
coh (Kb b)   X x        = x
coh (Kμ G)   X x        = x
coh (Kν G)   X x        = x
coh (F ⊕f G) X (inj₁ x) = inj₁ (coh F X x)
coh (F ⊕f G) X (inj₂ y) = inj₂ (coh G X y)
coh (F ⊗f G) X (x , y)  = (coh F X x , coh G X y)

coh⁻¹ : ∀ F X → FS F ⟦ X ⟧ → ⟦ LF∙ F X ⟧
coh⁻¹ Idf      X x        = x
coh⁻¹ Kone     X x        = x
coh⁻¹ (Kb b)   X x        = x
coh⁻¹ (Kμ G)   X x        = x
coh⁻¹ (Kν G)   X x        = x
coh⁻¹ (F ⊕f G) X (inj₁ x) = inj₁ (coh⁻¹ F X x)
coh⁻¹ (F ⊕f G) X (inj₂ y) = inj₂ (coh⁻¹ G X y)
coh⁻¹ (F ⊗f G) X (x , y)  = (coh⁻¹ F X x , coh⁻¹ G X y)

------------------------------------------------------------------------
-- 5. THE LINEAR CORE.
--
-- Symmetric monoidal over `⊗t` + additive coproducts + an EXPLICIT comonoid
-- (`dup`/`drop`, the only sources of duplication) + both fixpoints.
--
-- ★ Three generators the borrowed core did not have, and PLAN §8's coverage
-- table listed as gaps: `lzero` (the initial object — "trivial to add"),
-- `lOutμ` (the μ destructor — "missing"), and the codata trio.  Deciding the
-- shape rather than inheriting it is what makes them free.
------------------------------------------------------------------------

infixr 9 _∘l_
infixr 7 _⊗l_
data LTm : LTy → LTy → Set where
  lid     : ∀ {A} → LTm A A
  _∘l_    : ∀ {A B C} → LTm B C → LTm A B → LTm A C
  _⊗l_    : ∀ {A B C D} → LTm A B → LTm C D → LTm (A ⊗t C) (B ⊗t D)
  -- unitors, associator, braiding: the SMC structure.  All free — moving data
  -- is not copying it.
  ρl      : ∀ {A} → LTm (A ⊗t One) A
  ρl⁻     : ∀ {A} → LTm A (A ⊗t One)
  lul     : ∀ {A} → LTm (One ⊗t A) A
  lul⁻    : ∀ {A} → LTm A (One ⊗t A)
  lassoc  : ∀ {A B C} → LTm ((A ⊗t B) ⊗t C) (A ⊗t (B ⊗t C))
  lassoc⁻ : ∀ {A B C} → LTm (A ⊗t (B ⊗t C)) ((A ⊗t B) ⊗t C)
  lswap   : ∀ {A B} → LTm (A ⊗t B) (B ⊗t A)
  -- ★ THE COMONOID — the only sources of duplication / discard
  dup     : ∀ {A} → LTm A (A ⊗t A)
  drop    : ∀ {A} → LTm A One
  -- additive coproducts, and the initial object
  linl    : ∀ {A B} → LTm A (A ⊕t B)
  linr    : ∀ {A B} → LTm B (A ⊕t B)
  lcase   : ∀ {A B C} → LTm A C → LTm B C → LTm (A ⊕t B) C
  lzero   : ∀ {A} → LTm Zero A
  -- initial algebra: constructor, DESTRUCTOR, fold
  lIn     : ∀ {F} → LTm (LF∙ F (μt F)) (μt F)
  lOutμ   : ∀ {F} → LTm (μt F) (LF∙ F (μt F))
  lcata   : ∀ F {A} → LTm (LF∙ F A) A → LTm (μt F) A
  -- ★ final coalgebra: observation, unfold, and the dual constructor
  lOut    : ∀ {F} → LTm (νt F) (LF∙ F (νt F))
  lAna    : ∀ F {A} → LTm A (LF∙ F A) → LTm A (νt F)
  lInν    : ∀ {F} → LTm (LF∙ F (νt F)) (νt F)
  -- closed structure
  lcurry  : ∀ {A B C} → LTm (A ⊗t B) C → LTm A (B ⇒t C)
  leval   : ∀ {A B} → LTm ((A ⇒t B) ⊗t A) B

------------------------------------------------------------------------
-- 6. ★ THE COST SEMANTICS, mutual with both recursion operators.
--
-- `dup` is the only generator with a price.  Everything structural is free;
-- building a closure is free and paid at `leval` per call; building a `ν` is
-- free and paid at `lOut` per observation; a fold pays its algebra per NODE.
--
-- `cataC`/`mapC` descend a shrinking `Fix`; `unfoldNu`/`mapU` corecurse under
-- `force`.  They are exact duals and sit in one mutual block with `Lᶜ`.
------------------------------------------------------------------------

sumF : ∀ G {X : Set} → FS G (X × ℕ) → FS G X × ℕ
sumF Idf       p        = p
sumF Kone      t        = retᶜ t
sumF (Kb _)    t        = retᶜ t
sumF (Kμ _)    t        = retᶜ t
sumF (Kν _)    t        = retᶜ t
sumF (G ⊕f H)  (inj₁ y) = (inj₁ (fst (sumF G y)) , snd (sumF G y))
sumF (G ⊕f H)  (inj₂ z) = (inj₂ (fst (sumF H z)) , snd (sumF H z))
sumF (G ⊗f H)  (y , z)  =
  ((fst (sumF G y) , fst (sumF H z)) , (snd (sumF G y) +ℕ snd (sumF H z)))

mutual
  Lᶜ : ∀ {A B} → LTm A B → ⟦ A ⟧ → ⟦ B ⟧ × ℕ
  Lᶜ lid            x              = retᶜ x
  Lᶜ (f ∘l g)       x              = Lᶜ g x >>=ᶜ Lᶜ f
  Lᶜ (f ⊗l g)       (a , b)        = Lᶜ f a >>=ᶜ λ a' → Lᶜ g b >>=ᶜ λ b' → retᶜ (a' , b')
  Lᶜ ρl             (a , tt)       = retᶜ a
  Lᶜ ρl⁻            a              = retᶜ (a , tt)
  Lᶜ lul            (tt , a)       = retᶜ a
  Lᶜ lul⁻           a              = retᶜ (tt , a)
  Lᶜ lassoc         ((a , b) , c)  = retᶜ (a , (b , c))
  Lᶜ lassoc⁻        (a , (b , c))  = retᶜ ((a , b) , c)
  Lᶜ lswap          (a , b)        = retᶜ (b , a)
  Lᶜ dup            a              = ((a , a) , suc zero)   -- ★ THE allocation
  Lᶜ drop           a              = retᶜ tt
  Lᶜ linl           a              = retᶜ (inj₁ a)
  Lᶜ linr           b              = retᶜ (inj₂ b)
  Lᶜ (lcase f g)    (inj₁ a)       = Lᶜ f a                 -- ★ only the branch taken
  Lᶜ (lcase f g)    (inj₂ b)       = Lᶜ g b
  Lᶜ lzero          ()
  Lᶜ (lIn {F})      x              = retᶜ (fix (coh F (μt F) x))
  Lᶜ (lOutμ {F})    x              = retᶜ (coh⁻¹ F (μt F) (unfix x))
  Lᶜ (lcata F alg)  x              = cataC F (λ y → Lᶜ alg (coh⁻¹ F _ y)) x
  -- ★ observing PAYS what this step reports…
  Lᶜ (lOut {F})     x              = (coh⁻¹ F (νt F) (fst (force x)) , snd (force x))
  -- ★ …and building, either way, is FREE.
  Lᶜ (lAna F c)     a              = retᶜ (unfoldNu F c a)
  Lᶜ (lInν {F})     x              = retᶜ (mkNu (coh F (νt F) x))
  Lᶜ (lcurry f)     a              = retᶜ (λ b → Lᶜ f (a , b))
  Lᶜ leval          (f , a)        = f a

  cataC : ∀ F {X : Set} → (FS F X → X × ℕ) → Fix F → X × ℕ
  cataC F alg (fix w) = sumF F (mapC F F alg w) >>=ᶜ alg

  mapC : ∀ F G {X : Set} → (FS F X → X × ℕ) → FS G (Fix F) → FS G (X × ℕ)
  mapC F Idf       alg y        = cataC F alg y
  mapC F Kone      alg y        = y
  mapC F (Kb _)    alg y        = y
  mapC F (Kμ _)    alg y        = y
  mapC F (Kν _)    alg y        = y
  mapC F (G ⊕f H)  alg (inj₁ y) = inj₁ (mapC F G alg y)
  mapC F (G ⊕f H)  alg (inj₂ z) = inj₂ (mapC F H alg z)
  mapC F (G ⊗f H)  alg (y , z)  = (mapC F G alg y , mapC F H alg z)

  unfoldNu : ∀ {A} F → LTm A (LF∙ F A) → ⟦ A ⟧ → Nu F
  force (unfoldNu {A} F c a) =
    ( mapU F F c (coh F A (fst (Lᶜ c a))) , snd (Lᶜ c a) )

  mapU : ∀ {A} F G → LTm A (LF∙ F A) → FS G ⟦ A ⟧ → FS G (Nu F)
  mapU F Idf      c y        = unfoldNu F c y
  mapU F Kone     c y        = y
  mapU F (Kb _)   c y        = y
  mapU F (Kμ _)   c y        = y
  mapU F (Kν _)   c y        = y
  mapU F (G ⊕f H) c (inj₁ y) = inj₁ (mapU F G c y)
  mapU F (G ⊕f H) c (inj₂ z) = inj₂ (mapU F H c z)
  mapU F (G ⊗f H) c (y , z)  = (mapU F G c y , mapU F H c z)

------------------------------------------------------------------------
-- 7. THE LINEAR SUBLANGUAGE — every generator but `dup`.
------------------------------------------------------------------------

data DupFree : ∀ {A B} → LTm A B → Set where
  df-id      : ∀ {A} → DupFree (lid {A})
  df-∘       : ∀ {A B C} {f : LTm B C} {g : LTm A B} →
               DupFree f → DupFree g → DupFree (f ∘l g)
  df-⊗       : ∀ {A B C D} {f : LTm A B} {g : LTm C D} →
               DupFree f → DupFree g → DupFree (f ⊗l g)
  df-ρl      : ∀ {A} → DupFree (ρl {A})
  df-ρl⁻     : ∀ {A} → DupFree (ρl⁻ {A})
  df-lul     : ∀ {A} → DupFree (lul {A})
  df-lul⁻    : ∀ {A} → DupFree (lul⁻ {A})
  df-lassoc  : ∀ {A B C} → DupFree (lassoc {A} {B} {C})
  df-lassoc⁻ : ∀ {A B C} → DupFree (lassoc⁻ {A} {B} {C})
  df-lswap   : ∀ {A B} → DupFree (lswap {A} {B})
  df-drop    : ∀ {A} → DupFree (drop {A})
  df-linl    : ∀ {A B} → DupFree (linl {A} {B})
  df-linr    : ∀ {A B} → DupFree (linr {A} {B})
  df-case    : ∀ {A B C} {f : LTm A C} {g : LTm B C} →
               DupFree f → DupFree g → DupFree (lcase f g)
  df-zero    : ∀ {A} → DupFree (lzero {A})
  df-In      : ∀ {F} → DupFree (lIn {F})
  df-Outμ    : ∀ {F} → DupFree (lOutμ {F})
  df-cata    : ∀ F {A} {alg : LTm (LF∙ F A) A} → DupFree alg → DupFree (lcata F alg)
  df-Out     : ∀ {F} → DupFree (lOut {F})
  df-Ana     : ∀ F {A} {c : LTm A (LF∙ F A)} → DupFree c → DupFree (lAna F c)
  df-Inν     : ∀ {F} → DupFree (lInν {F})
  df-curry   : ∀ {A B C} {f : LTm (A ⊗t B) C} → DupFree f → DupFree (lcurry f)
  df-eval    : ∀ {A B} → DupFree (leval {A} {B})

------------------------------------------------------------------------
-- 8. ★★ WHERE THIS STOPS, AND WHY — `Free` DOES NOT FIT IN ONE RECURSION.
--
-- The payoff theorem is NOT below.  Building it top-down surfaced a structural
-- obstruction that the borrowed core could never have shown, and it is the same
-- one the KERNEL line hit at W1e (`SpikeSNK`).  Measured, not guessed:
--
--     FreeFix is not strictly positive, because it occurs
--     in the 7th clause in the definition of Free, which occurs
--       to the left of an arrow in the 6th clause in the definition of Free,
--       which occurs in the first clause in the definition of FreeFS,
--       which occurs in the type of the constructor freeFix
--     in the definition of FreeFix.
--
-- ★ THE CAUSE.  `Free (A ⇒t B) f = (a : ⟦ A ⟧) → Free A a → …` puts `Free`
-- NEGATIVELY — and that hypothesis is not removable: it is exactly what bounds
-- `leval`, whose closure is an arbitrary semantic value (`NbEPLinDyn` calls it
-- "the case the logical relation exists for").  Meanwhile `Free (μt F)` and
-- `Free (νt F)` must be REAL, so they re-enter `Free`, and the knot closes:
-- take `A = μt F` as a closure DOMAIN and `FreeFix` occurs negatively in its
-- own definition.
--
-- ★ WHY THE BORROWED CORE NEVER SAW IT.  `NbEPLinDyn` sets `Free (μ F) x = ⊤`,
-- justified by "`Func` is `Ty`-independent, so a `Fix F` holds no functions".
-- That is true and is NOT the point.  Here `LF` has `Kν`, so **data can hold a
-- PRODUCER**, and a producer has prices — `⊤` is simply wrong.  Making `ν` a
-- real citizen is what forces the inductive half of the relation to look at
-- what the data contains, and that is what closes the loop.
--
-- ★ IT IS W1e'S FINDING, AT THE OTHER LINE.  There: "`⊩Π`'s function field puts
-- `⊩∋` negatively, so a `⊩` in `⊩∋`'s result makes `⊩` occur negatively in its
-- own definition" — and the answer was to STRATIFY.  The two lines hit the same
-- wall from opposite directions, which is worth knowing before either is
-- extended again.
--
-- ★ THE RESOLUTION, designed and not yet built.  Stratify by WHAT CAN APPEAR IN
-- A FIXPOINT PAYLOAD, which is decidable from `LF` alone:
--
--   `FS G X` is built from `⊤`, base carriers, `Fix`, `Nu`, `⊎`, `×` — it has
--   NO function space, ever.  So the freedom of a fixpoint payload never needs
--   the `⇒t` clause.
--
--   1. Define `FreeFix`/`FreeNu` and their code-indexed lifts over the DATA
--      FRAGMENT ONLY, mutually.  No arrows appear, so they are strictly
--      positive and `FreeNu` may stay a coinductive record.
--   2. Define `Free : ∀ A → ⟦ A ⟧ → Set` AFTERWARDS, as a plain function
--      recursive on the OBJECT TYPE, using (1) at `μt`/`νt`.  Its negative
--      occurrence at `⇒t` is then harmless — it is a function, not a datatype,
--      and its recursion is structural in `LTy`.
--   3. Define `FreeFS G {X}` for arbitrary `X` after `Free` (the `lcata`
--      carrier can be an arrow, which is the only place it is needed), and
--      bridge it to (1) at `X = μt F` / `X = νt F` with two small inductions on
--      the code — they agree clause by clause.
--
-- Everything above this line is independent of that choice and checks as is.
------------------------------------------------------------------------
