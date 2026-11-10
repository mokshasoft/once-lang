-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · W0e/W0d — THE LINEAR CORE, OWNED.
--
-- The linearization line's object language, semantics and payoff theorem, in
-- one self-contained module that depends on no other POC: no
-- `bootstrap/normalizer/**` (that is another POC), no `formal/Once/**`; since
-- plan 0.146 it imports the standard library's basic types (§0).
--
-- ★ WHY THAT MATTERS, and why this module exists at all.  `NbEPLinRec` indexes
-- `LTm` by the NORMALIZER POC's `Ty`, and `Dyn`/`Pass`/`QTT` go further,
-- borrowing its `Mu`/`⟦_⟧FS`/`Term`/`eval`.  So the shape of the linear core
-- was being decided by a peer POC's accidental choices — and the moment W0d
-- tried to use it, that peer's limits started getting recorded as OUR
-- constraints: no `ν`, no base types, "`List Int` is out".  None of those were
-- findings about the right shape (PLAN §8.3).  This POC is here to find the
-- structure we want Once to HAVE.  So the structure is declared here, top-down,
-- and `ν` and the base leaves are present BECAUSE THE THEORY WANTS THEM.
--
-- WHAT IS DECIDED HERE, as opposed to inherited:
--
--   * NO GENERAL FIXPOINT.  `Mu`/`Nu` are the INITIAL ALGEBRA and FINAL
--     COALGEBRA of a polynomial code, and their only eliminators are `lcata`
--     (structured fold) and `lOut` (one observation) — there is no `fold`, no
--     `unfold`, no `Hylo`, no fixpoint combinator, and no pragma anywhere.
--     Named `Mu`/`Nu`/`inμ`/`outμ`/`inν` to match Once's own `In`/`out-μ`/
--     `Out`/`in-ν` rather than the normalizer POC's `Fix`/`fix`: OCP-0003
--     removed `fold`/`unfold` from the IR precisely to keep totality and
--     productivity by construction, and the core's vocabulary should not
--     re-import the idea it rejected.  (This module broke the DEPENDENCY on
--     that POC; keeping its NAMES would have been the same mistake one level
--     down.)
--   * `LF` — polynomial functor codes, kept OBJECT-LANGUAGE-INDEPENDENT.  A
--     constant is `Kone`, an inert leaf `Kb`, or a CODE (`Kμ`/`Kν`) — never an
--     arbitrary `LTy`.  This is a real structural decision, not a copy: it is
--     exactly what makes `Mu` strictly positive with no pragma, and it is what
--     lets `Mu` and the cost-carrying `Nu` share one knot.
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
-- holes; imports: the standard library only.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- 0. PRELUDE.  The standard library's basic types (plan 0.146, Spikes/):
--    plan-ref kept a local prelude so as not to couple to a PEER POC's; the
--    stdlib is not one, `formal/` (where this core migrates) uses it, and
--    the event semantics (`LinCore.Events`) needs its arithmetic and lists.
--    Same names as before (`fst`/`snd`, `_+ℕ_`), so nothing below changed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)

module LinCore.NbEPLinCore
  (Base : Set) (⟦_⟧b : Base → Set) where

------------------------------------------------------------------------
-- 1. POLYNOMIAL FUNCTOR CODES.
--
-- ★ `LF` mentions no `LTy`.  Its constants are the Unit leaf, an INERT base
-- leaf, or the CODE of another fixpoint — `Kμ`/`Kν`, never an arbitrary object
-- type.  That restriction is the reason `Mu` below is strictly positive with
-- no pragma AND the reason `Mu` and `Nu` can share one interpretation knot.
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
infixr 3 _⇒t_ _⇛t_
data LTy : Set where
  One  : LTy
  Zero : LTy
  _⊗t_ : LTy → LTy → LTy
  _⊕t_ : LTy → LTy → LTy
  _⇒t_ : LTy → LTy → LTy
  -- ★ plan 0.146 A2 (D131): a MANY-USE closure — its body only reads its
  -- environment, so it can be applied while lent, any number of times, and is
  -- freed once (QTT's ω arrow; `⇒t` is the one-shot, 1-graded one)
  _⇛t_ : LTy → LTy → LTy
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
-- `Mu` (inductive, a `data`) and `Nu` (coinductive, a `record` whose `force`
-- carries the step's price) share `FS`.  Putting them in ONE mutual block is
-- the payoff of §1's restriction on `LF`: neither interpretation mentions
-- `⟦_⟧`, so `⇒t`'s negative occurrence cannot taint either one's positivity.
------------------------------------------------------------------------

mutual
  FS : LF → Set → Set
  FS Idf      X = X
  FS Kone     X = ⊤
  FS (Kb b)   X = ⟦ b ⟧b
  FS (Kμ G)   X = Mu G
  FS (Kν G)   X = Nu G
  FS (F ⊕f G) X = FS F X ⊎ FS G X
  FS (F ⊗f G) X = FS F X × FS G X

  data Mu (F : LF) : Set where
    inμ : FS F (Mu F) → Mu F

  -- ★ unfolding reports its own cost.  The `ν` analogue of a closure reporting
  -- its own cost — the same decision, at the other fixpoint.
  record Nu (F : LF) : Set where
    coinductive
    field force : FS F (Nu F) × ℕ
open Nu

outμ : ∀ {F} → Mu F → FS F (Mu F)
outμ (inμ w) = w

-- building one layer of a `ν` costs nothing extra: the layer is already there.
inν : ∀ {F} → FS F (Nu F) → Nu F
force (inν w) = (w , zero)

⟦_⟧ : LTy → Set
⟦ One ⟧      = ⊤
⟦ Zero ⟧     = ⊥
⟦ A ⊗t B ⟧   = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⊕t B ⟧   = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ A ⇒t B ⟧   = ⟦ A ⟧ → ⟦ B ⟧ × ℕ    -- ★ a function reports its own cost
⟦ A ⇛t B ⟧   = ⟦ A ⟧ → ⟦ B ⟧ × ℕ    -- the same meaning; the difference is in memory
⟦ μt F ⟧     = Mu F
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
-- ★ TOTALITY AND PRODUCTIVITY ARE BY CONSTRUCTION, not by a side condition.
-- The only recursion generators are `lcata` (structural on a `Mu`) and `lAna`
-- (guarded under `force`).  `lOutμ`/`lInν` are the two Lambek isomorphisms —
-- one unwrapping each, no recursion.
--
-- ⚠ Where non-termination WOULD enter if one were careless: a hylomorphism —
-- `lOutμ` used inside an `lAna` coalgebra, folding what you are unfolding.  It
-- cannot here, and for a structural reason rather than a check: `lAna`'s result
-- is a `Nu`, produced under `force`, so every cycle through it is guarded.
-- That is why `Hylo`/`Fuse` are absent rather than restricted — they are
-- optimizations over these generators, not primitives, and adding them means
-- discharging their termination argument separately.
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

-- ★ plan 0.146 A10: ONE term language.  `Tm E A B` is a morphism `A → B` that
-- OWNS its input and may READ a lent `E`: never frees it, never keeps it.  What
-- a result keeps of `E` is copied out (`bcopy`, D402's choice A), so the owner
-- frees `E` whole, once, after the scope.  `E` is not a type of the core's
-- values (there is no borrow type), so a borrow cannot escape into a result, a
-- closure's environment or a ν's seed: those bodies are closed over `One`.
-- Every generator exists at every `E`; a term with nothing lent is `LTm`.
-- `E` comes last among the implicits so that `lIn {F}`, `linl {A} {B}` still read.
data Tm : LTy → LTy → LTy → Set where
  lid     : ∀ {A E} → Tm E A A
  _∘l_    : ∀ {A B C E} → Tm E B C → Tm E A B → Tm E A C
  _⊗l_    : ∀ {A B C D E} → Tm E A B → Tm E C D → Tm E (A ⊗t C) (B ⊗t D)
  -- unitors, associator, braiding: the SMC structure.  All free — moving data
  -- is not copying it.
  ρl      : ∀ {A E} → Tm E (A ⊗t One) A
  ρl⁻     : ∀ {A E} → Tm E A (A ⊗t One)
  lul     : ∀ {A E} → Tm E (One ⊗t A) A
  lul⁻    : ∀ {A E} → Tm E A (One ⊗t A)
  lassoc  : ∀ {A B C E} → Tm E ((A ⊗t B) ⊗t C) (A ⊗t (B ⊗t C))
  lassoc⁻ : ∀ {A B C E} → Tm E (A ⊗t (B ⊗t C)) ((A ⊗t B) ⊗t C)
  lswap   : ∀ {A B E} → Tm E (A ⊗t B) (B ⊗t A)
  -- ★ THE COMONOID — the only sources of duplication / discard
  dup     : ∀ {A E} → Tm E A (A ⊗t A)
  drop    : ∀ {A E} → Tm E A One
  -- additive coproducts, and the initial object
  linl    : ∀ {A B E} → Tm E A (A ⊕t B)
  linr    : ∀ {A B E} → Tm E B (A ⊕t B)
  lcase   : ∀ {A B C E} → Tm E A C → Tm E B C → Tm E (A ⊕t B) C
  lzero   : ∀ {A E} → Tm E Zero A
  -- initial algebra: constructor, DESTRUCTOR, fold (★ reads `E` at every layer,
  -- with no copy of `E`)
  lIn     : ∀ {F E} → Tm E (LF∙ F (μt F)) (μt F)
  lOutμ   : ∀ {F E} → Tm E (μt F) (LF∙ F (μt F))
  lcata   : ∀ F {A E} → Tm E (LF∙ F A) A → Tm E (μt F) A
  -- ★ final coalgebra: observation, unfold, and the dual constructor.  A
  -- coalgebra outlives every scope, so it reads nothing lent.
  lOut    : ∀ {F E} → Tm E (νt F) (LF∙ F (νt F))
  lAna    : ∀ F {A E} → Tm One A (LF∙ F A) → Tm E A (νt F)
  lInν    : ∀ {F E} → Tm E (LF∙ F (νt F)) (νt F)
  -- closed structure.  A closure outlives every scope too.
  lcurry  : ∀ {A B C E} → Tm One (A ⊗t B) C → Tm E A (B ⇒t C)
  leval   : ∀ {A B E} → Tm E ((A ⇒t B) ⊗t A) B
  -- ★ the scope: lend `X` to a body, which also reads what was lent already;
  -- `X` comes back unchanged.
  lend    : ∀ {E X A B} → Tm (E ⊗t X) A B → Tm E (X ⊗t A) (X ⊗t B)
  -- a many-use closure: it owns `X`; its body only reads it
  lcurryB : ∀ {X A B E} → Tm X A B → Tm E X (A ⇛t B)
  -- a step that reads nothing of what is lent
  blift   : ∀ {A B E} → Tm One A B → Tm E A B
  -- reading the lent value: a part of it, its tag, inside a node (all views)
  bfst    : ∀ {E₁ E₂ A B} → Tm E₁ A B → Tm (E₁ ⊗t E₂) A B
  bsnd    : ∀ {E₁ E₂ A B} → Tm E₂ A B → Tm (E₁ ⊗t E₂) A B
  bcaseE  : ∀ {E₁ E₂ A B} → Tm E₁ A B → Tm E₂ A B → Tm (E₁ ⊕t E₂) A B
  bout    : ∀ {F A B} → Tm (LF∙ F (μt F)) A B → Tm (μt F) A B
  -- keeping it: a copy (fresh cells; a word costs nothing)
  bcopy   : ∀ {E} → Tm E One E
  -- applying a LENT many-use closure (D131: a fold's algebra, obtained once,
  -- applied at every layer): its environment is lent on to its body
  bapp    : ∀ {A B} → Tm (A ⇛t B) A B

-- a term with nothing lent
LTm : LTy → LTy → Set
LTm = Tm One

------------------------------------------------------------------------
-- 6. ★ THE COST SEMANTICS, mutual with both recursion operators.
--
-- `dup` is the only generator with a price.  Everything structural is free;
-- building a closure is free and paid at `leval` per call; building a `ν` is
-- free and paid at `lOut` per observation; a fold pays its algebra per NODE.
--
-- `cataC`/`mapC` descend a shrinking `Mu`; `unfoldNu`/`mapU` corecurse under
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
  -- a term means a function of the lent value, which it does not consume, and
  -- of its input, which it does
  Lᶜ : ∀ {E A B} → Tm E A B → ⟦ E ⟧ → ⟦ A ⟧ → ⟦ B ⟧ × ℕ
  Lᶜ lid            e         x              = retᶜ x
  Lᶜ (f ∘l g)       e         x              = Lᶜ g e x >>=ᶜ Lᶜ f e
  Lᶜ (f ⊗l g)       e         (a , b)        = Lᶜ f e a >>=ᶜ λ a' → Lᶜ g e b >>=ᶜ λ b' → retᶜ (a' , b')
  Lᶜ ρl             e         (a , tt)       = retᶜ a
  Lᶜ ρl⁻            e         a              = retᶜ (a , tt)
  Lᶜ lul            e         (tt , a)       = retᶜ a
  Lᶜ lul⁻           e         a              = retᶜ (tt , a)
  Lᶜ lassoc         e         ((a , b) , c)  = retᶜ (a , (b , c))
  Lᶜ lassoc⁻        e         (a , (b , c))  = retᶜ ((a , b) , c)
  Lᶜ lswap          e         (a , b)        = retᶜ (b , a)
  Lᶜ dup            e         a              = ((a , a) , suc zero)   -- ★ THE allocation
  Lᶜ drop           e         a              = retᶜ tt
  Lᶜ linl           e         a              = retᶜ (inj₁ a)
  Lᶜ linr           e         b              = retᶜ (inj₂ b)
  Lᶜ (lcase f g)    e         (inj₁ a)       = Lᶜ f e a               -- ★ only the branch taken
  Lᶜ (lcase f g)    e         (inj₂ b)       = Lᶜ g e b
  Lᶜ lzero          e         ()
  Lᶜ (lIn {F})      e         x              = retᶜ (inμ (coh F (μt F) x))
  Lᶜ (lOutμ {F})    e         x              = retᶜ (coh⁻¹ F (μt F) (outμ x))
  Lᶜ (lcata F alg)  e         x              = cataC F (λ y → Lᶜ alg e (coh⁻¹ F _ y)) x
  -- ★ observing PAYS what this step reports…
  Lᶜ (lOut {F})     e         x              = (coh⁻¹ F (νt F) (fst (force x)) , snd (force x))
  -- ★ …and building, either way, is FREE.
  Lᶜ (lAna F c)     e         a              = retᶜ (unfoldNu F c a)
  Lᶜ (lInν {F})     e         x              = retᶜ (inν (coh F (νt F) x))
  Lᶜ (lcurry f)     e         a              = retᶜ (λ b → Lᶜ f tt (a , b))
  Lᶜ leval          e         (f , a)        = f a
  Lᶜ (lend b)       e         (x , a)        = Lᶜ b (e , x) a >>=ᶜ λ w → retᶜ (x , w)
  Lᶜ (lcurryB b)    e         x              = retᶜ (λ a → Lᶜ b x a)
  Lᶜ (blift f)      e         a              = Lᶜ f tt a
  Lᶜ (bfst f)       (e₁ , e₂) a              = Lᶜ f e₁ a
  Lᶜ (bsnd f)       (e₁ , e₂) a              = Lᶜ f e₂ a
  Lᶜ (bcaseE f g)   (inj₁ e)  a              = Lᶜ f e a
  Lᶜ (bcaseE f g)   (inj₂ e)  a              = Lᶜ g e a
  Lᶜ (bout {F} f)   e         a              = Lᶜ f (coh⁻¹ F (μt F) (outμ e)) a
  Lᶜ bcopy          e         a              = (e , suc zero)         -- priced like `dup`
  Lᶜ bapp           f         a              = f a

  cataC : ∀ F {X : Set} → (FS F X → X × ℕ) → Mu F → X × ℕ
  cataC F alg (inμ w) = sumF F (mapC F F alg w) >>=ᶜ alg

  mapC : ∀ F G {X : Set} → (FS F X → X × ℕ) → FS G (Mu F) → FS G (X × ℕ)
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
    ( mapU F F c (coh F A (fst (Lᶜ c tt a))) , snd (Lᶜ c tt a) )

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

data DupFree : ∀ {E A B} → Tm E A B → Set where
  df-id      : ∀ {A E} → DupFree (lid {A} {E})
  df-∘       : ∀ {A B C E} {f : Tm E B C} {g : Tm E A B} →
               DupFree f → DupFree g → DupFree (f ∘l g)
  df-⊗       : ∀ {A B C D E} {f : Tm E A B} {g : Tm E C D} →
               DupFree f → DupFree g → DupFree (f ⊗l g)
  df-ρl      : ∀ {A E} → DupFree (ρl {A} {E})
  df-ρl⁻     : ∀ {A E} → DupFree (ρl⁻ {A} {E})
  df-lul     : ∀ {A E} → DupFree (lul {A} {E})
  df-lul⁻    : ∀ {A E} → DupFree (lul⁻ {A} {E})
  df-lassoc  : ∀ {A B C E} → DupFree (lassoc {A} {B} {C} {E})
  df-lassoc⁻ : ∀ {A B C E} → DupFree (lassoc⁻ {A} {B} {C} {E})
  df-lswap   : ∀ {A B E} → DupFree (lswap {A} {B} {E})
  df-drop    : ∀ {A E} → DupFree (drop {A} {E})
  df-linl    : ∀ {A B E} → DupFree (linl {A} {B} {E})
  df-linr    : ∀ {A B E} → DupFree (linr {A} {B} {E})
  df-case    : ∀ {A B C E} {f : Tm E A C} {g : Tm E B C} →
               DupFree f → DupFree g → DupFree (lcase f g)
  df-zero    : ∀ {A E} → DupFree (lzero {A} {E})
  df-In      : ∀ {F E} → DupFree (lIn {F} {E})
  df-Outμ    : ∀ {F E} → DupFree (lOutμ {F} {E})
  df-cata    : ∀ F {A E} {alg : Tm E (LF∙ F A) A} → DupFree alg → DupFree (lcata F alg)
  df-Out     : ∀ {F E} → DupFree (lOut {F} {E})
  df-Ana     : ∀ F {A E} {c : Tm One A (LF∙ F A)} → DupFree c → DupFree (lAna F {A} {E} c)
  df-Inν     : ∀ {F E} → DupFree (lInν {F} {E})
  df-curry   : ∀ {A B C E} {f : Tm One (A ⊗t B) C} → DupFree f → DupFree (lcurry {A} {B} {C} {E} f)
  df-eval    : ∀ {A B E} → DupFree (leval {A} {B} {E})

------------------------------------------------------------------------
-- 8. ★★ "ALLOCATES NOTHING" — AND WHY IT MUST BE STRATIFIED.
--
-- The obvious definition does not typecheck, and the reason is structural.
-- `Free (A ⇒t B) f = (a : ⟦ A ⟧) → Free A a → …` puts `Free` NEGATIVELY, and
-- that hypothesis is not removable: it is exactly what bounds `leval`, whose
-- closure is an arbitrary semantic value.  If `Free` at `μt`/`νt` is then a
-- DATATYPE, it occurs negatively in its own definition — take a fixpoint as a
-- closure DOMAIN and the knot closes.  Measured:
--
--     FreeMu is not strictly positive, because it occurs … to the left of an
--     arrow in the definition of Free, which occurs … in the type of the
--     constructor freeMu in the definition of FreeMu.
--
-- ⚠ THE BORROWED CORE COULD NOT HAVE SHOWN THIS.  `NbEPLinDyn` sets
-- `Free (μ F) x = ⊤`, justified by "a `Mu F` holds no functions".  True, and
-- beside the point: with `Kν` among the codes, DATA CAN HOLD A PRODUCER, and a
-- producer has prices.  Making `ν` a real citizen is what forces the inductive
-- half of the relation to inspect what the data contains — and that is what
-- closes the loop.  It is W1e's finding (`SpikeSNK`, "`⊩Π`'s function field
-- puts `⊩∋` negatively") reached from the other line.
--
-- ★ THE STRATIFICATION, and the observation that makes it work:
--
--     `FS G C` is built from `⊤`, base carriers, `Mu`, `Nu`, `⊎`, `×`.
--     IT CONTAINS NO FUNCTION SPACE, EVER.
--
-- So the freedom of a fixpoint payload never needs the `⇒t` clause.  Hence:
--
--   LAYER 1 — `FreeMu`/`FreeNu` and their lifts, over the DATA FRAGMENT ONLY.
--     No arrow occurs, so these are strictly positive and `FreeNu` may stay a
--     coinductive record.
--   LAYER 2 — `Free`, a plain FUNCTION recursive on the OBJECT TYPE, using
--     layer 1 at `μt`/`νt`.  Its negative occurrence at `⇒t` is now harmless:
--     no datatype is being defined, and the recursion is structural in `LTy`.
--   LAYER 3 — `FreeFS G {X}` for an ARBITRARY carrier, after `Free` (the
--     `lcata` carrier can be an arrow — the one place it is needed), bridged
--     to layer 1 at `X = μt F`/`νt F`.  The two agree clause by clause; the
--     bridges are the four one-line inductions below.
------------------------------------------------------------------------

-- LAYER 1 — the data fragment.  Arrow-free, hence strictly positive.
mutual
  data FreeMu (F : LF) : Mu F → Set where
    freeMu : ∀ {w} → FreeMuF F F w → FreeMu F (inμ w)

  FreeMuF : ∀ F G → FS G (Mu F) → Set
  FreeMuF F Idf      v        = FreeMu F v
  FreeMuF F Kone     _        = ⊤
  FreeMuF F (Kb _)   _        = ⊤
  FreeMuF F (Kμ G)   v        = FreeMu G v
  FreeMuF F (Kν G)   v        = FreeNu G v
  FreeMuF F (G ⊕f H) (inj₁ y) = FreeMuF F G y
  FreeMuF F (G ⊕f H) (inj₂ z) = FreeMuF F H z
  FreeMuF F (G ⊗f H) (y , z)  = FreeMuF F G y × FreeMuF F H z

  record FreeNu (F : LF) (x : Nu F) : Set where
    coinductive
    field
      costZero : snd (force x) ≡ zero        -- ★ THIS observation is free…
      next     : FreeNuF F F (fst (force x)) -- ★ …and everything after it
  FreeNuF : ∀ F G → FS G (Nu F) → Set
  FreeNuF F Idf      v        = FreeNu F v
  FreeNuF F Kone     _        = ⊤
  FreeNuF F (Kb _)   _        = ⊤
  FreeNuF F (Kμ G)   v        = FreeMu G v
  FreeNuF F (Kν G)   v        = FreeNu G v
  FreeNuF F (G ⊕f H) (inj₁ y) = FreeNuF F G y
  FreeNuF F (G ⊕f H) (inj₂ z) = FreeNuF F H z
  FreeNuF F (G ⊗f H) (y , z)  = FreeNuF F G y × FreeNuF F H z
open FreeNu

-- LAYER 2 — a FUNCTION, structural in `LTy`.  The `⇒t` clause is negative and
-- that is now fine: nothing inductive is being declared.
Free : ∀ A → ⟦ A ⟧ → Set
Free One       x        = ⊤
Free Zero      ()
Free (A ⊗t B)  (a , b)  = Free A a × Free B b
Free (A ⊕t B)  (inj₁ a) = Free A a
Free (A ⊕t B)  (inj₂ b) = Free B b
Free (A ⇒t B)  f        =
  (a : ⟦ A ⟧) → Free A a → Free B (fst (f a)) × (snd (f a) ≡ zero)
Free (A ⇛t B)  f        =
  (a : ⟦ A ⟧) → Free A a → Free B (fst (f a)) × (snd (f a) ≡ zero)
Free (μt F)    x        = FreeMu F x
Free (νt F)    x        = FreeNu F x
Free (Bt b)    x        = ⊤        -- ★ inert: a base leaf cannot allocate

-- LAYER 3 — arbitrary carrier, for `lcata`'s.
-- ⚠ the carrier is EXPLICIT.  Implicit, the recursive calls in the `⊕f`/`⊗f`
-- clauses leave it a metavariable — there is nothing in `FS H ⟦ _ ⟧` to solve
-- it against.
FreeFS : ∀ G (A : LTy) → FS G ⟦ A ⟧ → Set
FreeFS Idf      A v        = Free A v
FreeFS Kone     A _        = ⊤
FreeFS (Kb _)   A _        = ⊤
FreeFS (Kμ G)   A v        = FreeMu G v
FreeFS (Kν G)   A v        = FreeNu G v
FreeFS (G ⊕f H) A (inj₁ y) = FreeFS G A y
FreeFS (G ⊕f H) A (inj₂ z) = FreeFS H A z
FreeFS (G ⊗f H) A (y , z)  = FreeFS G A y × FreeFS H A z

-- THE BRIDGES.  Layer 3 at a fixpoint carrier IS layer 1 — the clauses match
-- one for one, and only `⊕f`/`⊗f` have any content.
muF→fs : ∀ F G (v : FS G (Mu F)) → FreeMuF F G v → FreeFS G (μt F) v
muF→fs F Idf      v        p        = p
muF→fs F Kone     v        p        = tt
muF→fs F (Kb _)   v        p        = tt
muF→fs F (Kμ _)   v        p        = p
muF→fs F (Kν _)   v        p        = p
muF→fs F (G ⊕f H) (inj₁ y) p        = muF→fs F G y p
muF→fs F (G ⊕f H) (inj₂ z) p        = muF→fs F H z p
muF→fs F (G ⊗f H) (y , z)  (p , q)  = (muF→fs F G y p , muF→fs F H z q)

fs→muF : ∀ F G (v : FS G (Mu F)) → FreeFS G (μt F) v → FreeMuF F G v
fs→muF F Idf      v        p        = p
fs→muF F Kone     v        p        = tt
fs→muF F (Kb _)   v        p        = tt
fs→muF F (Kμ _)   v        p        = p
fs→muF F (Kν _)   v        p        = p
fs→muF F (G ⊕f H) (inj₁ y) p        = fs→muF F G y p
fs→muF F (G ⊕f H) (inj₂ z) p        = fs→muF F H z p
fs→muF F (G ⊗f H) (y , z)  (p , q)  = (fs→muF F G y p , fs→muF F H z q)

nuF→fs : ∀ F G (v : FS G (Nu F)) → FreeNuF F G v → FreeFS G (νt F) v
nuF→fs F Idf      v        p        = p
nuF→fs F Kone     v        p        = tt
nuF→fs F (Kb _)   v        p        = tt
nuF→fs F (Kμ _)   v        p        = p
nuF→fs F (Kν _)   v        p        = p
nuF→fs F (G ⊕f H) (inj₁ y) p        = nuF→fs F G y p
nuF→fs F (G ⊕f H) (inj₂ z) p        = nuF→fs F H z p
nuF→fs F (G ⊗f H) (y , z)  (p , q)  = (nuF→fs F G y p , nuF→fs F H z q)

fs→nuF : ∀ F G (v : FS G (Nu F)) → FreeFS G (νt F) v → FreeNuF F G v
fs→nuF F Idf      v        p        = p
fs→nuF F Kone     v        p        = tt
fs→nuF F (Kb _)   v        p        = tt
fs→nuF F (Kμ _)   v        p        = p
fs→nuF F (Kν _)   v        p        = p
fs→nuF F (G ⊕f H) (inj₁ y) p        = fs→nuF F G y p
fs→nuF F (G ⊕f H) (inj₂ z) p        = fs→nuF F H z p
fs→nuF F (G ⊗f H) (y , z)  (p , q)  = (fs→nuF F G y p , fs→nuF F H z q)

-- `Free` transported across the functor coherence.
freeCoh : ∀ G X (v : ⟦ LF∙ G X ⟧) → Free (LF∙ G X) v → FreeFS G X (coh G X v)
freeCoh Idf      X v        fv        = fv
freeCoh Kone     X v        fv        = tt
freeCoh (Kb _)   X v        fv        = tt
freeCoh (Kμ _)   X v        fv        = fv
freeCoh (Kν _)   X v        fv        = fv
freeCoh (G ⊕f H) X (inj₁ y) fy        = freeCoh G X y fy
freeCoh (G ⊕f H) X (inj₂ z) fz        = freeCoh H X z fz
freeCoh (G ⊗f H) X (y , z)  (fy , fz) = (freeCoh G X y fy , freeCoh H X z fz)

freeCoh⁻¹ : ∀ G X (v : FS G ⟦ X ⟧) → FreeFS G X v → Free (LF∙ G X) (coh⁻¹ G X v)
freeCoh⁻¹ Idf      X v        fv        = fv
freeCoh⁻¹ Kone     X v        fv        = tt
freeCoh⁻¹ (Kb _)   X v        fv        = tt
freeCoh⁻¹ (Kμ _)   X v        fv        = fv
freeCoh⁻¹ (Kν _)   X v        fv        = fv
freeCoh⁻¹ (G ⊕f H) X (inj₁ y) fy        = freeCoh⁻¹ G X y fy
freeCoh⁻¹ (G ⊕f H) X (inj₂ z) fz        = freeCoh⁻¹ H X z fz
freeCoh⁻¹ (G ⊗f H) X (y , z)  (fy , fz) =
  (freeCoh⁻¹ G X y fy , freeCoh⁻¹ H X z fz)

------------------------------------------------------------------------
-- 9. ★★ THE OPERATIONAL LINEARITY THEOREM, OVER BOTH FIXPOINTS.
--
-- A `DupFree` morphism applied to `Free` inputs performs ZERO allocations and
-- returns a `Free` result — where at `ν` "zero allocations" is necessarily the
-- coinductive statement, because there is no total to be zero.  This is
-- `NbEPLinDyn`'s `dyn-linear` and `SpikeLinNu`'s `dynN` merged into ONE
-- induction, which is only possible now that both fixpoints live in one core.
--
-- Five-way mutual, and the cycles are discharged three different ways:
--   · `dyn-linear`/`cata-ok`/`map-ok` — STRUCTURAL, on the `DupFree` derivation
--     and on the shrinking `Mu`;
--   · `freeAna`/`freeMap` — GUARDED, under the `next` copattern;
--   · `dyn-linear (df-Ana …) → freeAna → dyn-linear` — decreasing on the
--     derivation, which is what lets the two disciplines meet.
------------------------------------------------------------------------

mutual
  dyn-linear : ∀ {E A B} {f : Tm E A B} → DupFree f → (e : ⟦ E ⟧) (x : ⟦ A ⟧) → Free A x →
               Free B (fst (Lᶜ f e x)) × (snd (Lᶜ f e x) ≡ zero)
  dyn-linear df-id           e x             fx        = (fx , refl)
  dyn-linear (df-∘ p q)      e x             fx        =
    ( fst (dyn-linear p e _ (fst (dyn-linear q e x fx)))
    , cong₂ _+ℕ_ (snd (dyn-linear q e x fx))
                 (snd (dyn-linear p e _ (fst (dyn-linear q e x fx)))) )
  dyn-linear (df-⊗ p q)      e (a , b)       (fa , fb) =
    ( ( fst (dyn-linear p e a fa) , fst (dyn-linear q e b fb) )
    , cong₂ _+ℕ_ (snd (dyn-linear p e a fa))
                 (cong₂ _+ℕ_ (snd (dyn-linear q e b fb)) refl) )
  dyn-linear df-ρl           e (a , tt)      (fa , _)  = (fa , refl)
  dyn-linear df-ρl⁻          e a             fa        = ((fa , tt) , refl)
  dyn-linear df-lul          e (tt , a)      (_ , fa)  = (fa , refl)
  dyn-linear df-lul⁻         e a             fa        = ((tt , fa) , refl)
  dyn-linear df-lassoc       e ((a , b) , c) ((fa , fb) , fc) =
    ((fa , (fb , fc)) , refl)
  dyn-linear df-lassoc⁻      e (a , (b , c)) (fa , (fb , fc)) =
    (((fa , fb) , fc) , refl)
  dyn-linear df-lswap        e (a , b)       (fa , fb) = ((fb , fa) , refl)
  dyn-linear df-drop         e a             fa        = (tt , refl)
  dyn-linear df-linl         e a             fa        = (fa , refl)
  dyn-linear df-linr         e b             fb        = (fb , refl)
  dyn-linear (df-case p q)   e (inj₁ a)      fa        = dyn-linear p e a fa
  dyn-linear (df-case p q)   e (inj₂ b)      fb        = dyn-linear q e b fb
  dyn-linear df-zero         e ()
  -- μ: the two Lambek isos wrap and unwrap; neither copies.
  dyn-linear (df-In {F})     e x             fx        =
    ( freeMu (fs→muF F F (coh F (μt F) x) (freeCoh F (μt F) x fx)) , refl )
  dyn-linear (df-Outμ {F})   e (inμ w)       (freeMu fw) =
    ( freeCoh⁻¹ F (μt F) w (muF→fs F F w fw) , refl )
  dyn-linear (df-cata F p)   e x             fx        =
    cata-ok F _ (λ w fw → dyn-linear p e (coh⁻¹ F _ w) (freeCoh⁻¹ F _ w fw)) x fx
  -- ★ ν: observing pays what the producer reports — and a `Free` producer
  --   reports zero and hands back a `Free` layer.  Both straight from `FreeNu`.
  dyn-linear (df-Out {F})    e x             fx        =
    ( freeCoh⁻¹ F (νt F) (fst (force x))
                (nuF→fs F F (fst (force x)) (next fx))
    , costZero fx )
  -- ★ building is free either way: `lAna` corecursively, `lInν` in one step
  --   because the layer is already there.
  dyn-linear (df-Ana F p)    e a             fa        = (freeAna p a fa , refl)
  dyn-linear (df-Inν {F})    e x             fx        =
    ( freeInν (fs→nuF F F (coh F (νt F) x) (freeCoh F (νt F) x fx)) , refl )
  -- the closure cases: `Free` is exactly the hypothesis `leval` needs, and the
  -- only place it is consumed.
  dyn-linear (df-curry p)    e a             fa        =
    ( (λ b fb → dyn-linear p tt (a , b) (fa , fb)) , refl )
  dyn-linear df-eval         e (f , a)       (ff , fa) = ff a fa

  freeInν : ∀ {F} {w : FS F (Nu F)} → FreeNuF F F w → FreeNu F (inν w)
  costZero (freeInν fw) = refl
  next     (freeInν fw) = fw

  cata-ok : ∀ F {X : LTy} (alg : FS F ⟦ X ⟧ → ⟦ X ⟧ × ℕ) →
            (∀ w → FreeFS F X w → Free X (fst (alg w)) × (snd (alg w) ≡ zero)) →
            ∀ (x : Mu F) → FreeMu F x →
            Free X (fst (cataC F alg x)) × (snd (cataC F alg x) ≡ zero)
  cata-ok F alg h (inμ w) (freeMu fw) =
    ( fst (h (fst (sumF F (mapC F F alg w))) (fst (map-ok F F alg h w fw)))
    , cong₂ _+ℕ_ (snd (map-ok F F alg h w fw))
                 (snd (h (fst (sumF F (mapC F F alg w)))
                         (fst (map-ok F F alg h w fw)))) )

  map-ok : ∀ F G {X : LTy} (alg : FS F ⟦ X ⟧ → ⟦ X ⟧ × ℕ) →
           (∀ w → FreeFS F X w → Free X (fst (alg w)) × (snd (alg w) ≡ zero)) →
           (y : FS G (Mu F)) → FreeMuF F G y →
           FreeFS G X (fst (sumF G (mapC F G alg y)))
           × (snd (sumF G (mapC F G alg y)) ≡ zero)
  map-ok F Idf      alg h y        fy        = cata-ok F alg h y fy
  map-ok F Kone     alg h y        fy        = (tt , refl)
  map-ok F (Kb _)   alg h y        fy        = (tt , refl)
  map-ok F (Kμ _)   alg h y        fy        = (fy , refl)
  map-ok F (Kν _)   alg h y        fy        = (fy , refl)
  map-ok F (G ⊕f H) alg h (inj₁ y) fy        = map-ok F G alg h y fy
  map-ok F (G ⊕f H) alg h (inj₂ z) fz        = map-ok F H alg h z fz
  map-ok F (G ⊗f H) alg h (y , z)  (fy , fz) =
    ( ( fst (map-ok F G alg h y fy) , fst (map-ok F H alg h z fz) )
    , cong₂ _+ℕ_ (snd (map-ok F G alg h y fy))
                 (snd (map-ok F H alg h z fz)) )

  freeAna : ∀ {A F} {c : LTm A (LF∙ F A)} → DupFree c →
            (a : ⟦ A ⟧) → Free A a → FreeNu F (unfoldNu F c a)
  costZero (freeAna dc a fa) = snd (dyn-linear dc tt a fa)
  next (freeAna {A} {F} {c} dc a fa) =
    freeMap dc F (coh F A (fst (Lᶜ c tt a)))
                 (freeCoh F A (fst (Lᶜ c tt a)) (fst (dyn-linear dc tt a fa)))

  freeMap : ∀ {A F} {c : LTm A (LF∙ F A)} → DupFree c → ∀ G →
            (y : FS G ⟦ A ⟧) → FreeFS G A y → FreeNuF F G (mapU F G c y)
  freeMap dc Idf      y        fy        = freeAna dc y fy
  freeMap dc Kone     y        fy        = tt
  freeMap dc (Kb _)   y        fy        = tt
  freeMap dc (Kμ _)   y        fy        = fy
  freeMap dc (Kν _)   y        fy        = fy
  freeMap dc (G ⊕f H) (inj₁ y) fy        = freeMap dc G y fy
  freeMap dc (G ⊕f H) (inj₂ z) fz        = freeMap dc H z fz
  freeMap dc (G ⊗f H) (y , z)  (fy , fz) =
    (freeMap dc G y fy , freeMap dc H z fz)

------------------------------------------------------------------------
-- 10. CONTROLS.
------------------------------------------------------------------------

-- ★ NEGATIVE.  `LF∙ (Idf ⊗f Idf) A = A ⊗t A`, so `dup` IS a coalgebra: the
-- producer that duplicates forever.  It builds free and pays one per
-- observation, at every depth — no `n : ℕ` bounds it, which is why the cost
-- had to move onto `force` in the first place.
badF : LF
badF = Idf ⊗f Idf

badAna : ∀ {A} → LTm A (νt badF)
badAna = lAna badF dup

badProd : Nu badF
badProd = fst (Lᶜ (badAna {One}) tt tt)

bad-build-free : snd (Lᶜ (badAna {One}) tt tt) ≡ zero
bad-build-free = refl

spineL : ℕ → Nu badF → Nu badF
spineL zero    x = x
spineL (suc n) x = spineL n (fst (fst (force x)))

bad-forever : ∀ n → snd (force (spineL n badProd)) ≡ suc zero
bad-forever zero    = refl
bad-forever (suc n) = bad-forever n

bad-not-free : ¬ (FreeNu badF badProd)
bad-not-free fn with costZero fn
... | ()

bad-not-linear : ¬ (DupFree (badAna {One}))
bad-not-linear (df-Ana _ ())

-- ★★ THE CONTROL THAT JUSTIFIES THE WHOLE REDESIGN.  `NbEPLinDyn` sets
-- `Free (μ F) x = ⊤` because "a fixpoint holds no functions".  With `Kν` among
-- the codes it can hold a PRODUCER — so here is inductive DATA that is not
-- free, and `⊤` would have called it free.  This is what forced §8's
-- stratification, and it is not reachable in the borrowed core at all.
boxF : LF
boxF = Kν badF

box-not-free : ¬ (FreeMu boxF (inμ badProd))
box-not-free (freeMu fp) with costZero fp
... | ()

-- ★ POSITIVE — and it must exist, or `FreeNu` could be vacuous and the `ν`
-- case of `dyn-linear` with it.  `lAna Idf lid` is a genuinely non-terminating
-- producer whose every step is free, proven so BY THE THEOREM.  This is the
-- case where the inductive statement ("the run costs zero") is not expressible.
goodAna : LTm One (νt Idf)
goodAna = lAna Idf lid

good-linear : DupFree goodAna
good-linear = df-Ana Idf df-id

good-free : FreeNu Idf (fst (Lᶜ goodAna tt tt))
good-free = fst (dyn-linear good-linear tt tt tt)

good-observe-free : snd (Lᶜ (lOut {Idf} ∘l goodAna) tt tt) ≡ zero
good-observe-free = snd (dyn-linear (df-∘ df-Out good-linear) tt tt tt)

-- ★ and the μ side still works: a fold with a dup-free algebra is free.
natF : LF
natF = Kone ⊕f Idf

natAlg : LTm (LF∙ natF One) One
natAlg = lcase lid lid

nat-fold-free : ∀ (n : Mu natF) → FreeMu natF n →
                snd (Lᶜ (lcata natF natAlg) tt n) ≡ zero
nat-fold-free n fn = snd (dyn-linear (df-cata natF (df-case df-id df-id)) tt n fn)
