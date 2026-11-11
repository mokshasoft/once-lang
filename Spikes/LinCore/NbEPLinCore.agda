-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.NbEPLinCore — THE LINEAR CORE (plan 0.146; D403).
--
-- Started as OCP-0009's `NbEPLinCore` (`origin/plan-ref`), and now the one
-- term language of the spike:
--
--   * `LF` — polynomial functor codes, kept OBJECT-LANGUAGE-INDEPENDENT. A
--     constant is `Kone`, an inert leaf `Kb`, or a CODE (`Kμ`/`Kν`), never an
--     arbitrary `LTy`: that is what makes `Mu` strictly positive with no pragma.
--   * `LTy` — with `νt` and base leaves from the start. ★ D405: no arrow
--     type; a closure is `Ct l X`, its environment tagged with its label.
--   * `Cx`, `Defs` — the program's labels and their bodies, each typed over
--     the labels before it (one-shot or many-use, D131).
--   * `Tm E A B` — every generator: symmetric monoidal over `⊗t`, additive
--     coproducts, an EXPLICIT comonoid (`dup`/`drop`), both fixpoints, closures,
--     a lent context `E` (A10), and the SigOps and the loop (A11).
--   * `Lᶜ` — the meaning of a term: a computation in `T∞`.
--
-- NO GENERAL FIXPOINT. `Mu`/`Nu` are the initial algebra and final coalgebra of
-- a polynomial code; the recursion generators are `lcata` (structural),
-- `lAna` (guarded) and `liter` (the loop, which may run forever).
--
-- ★ A11: ONE MEANING, as master's `evalᴰ`. The IR is ungraded (Plan 0.52 M2:
-- one exponential per `(A, B)`), so a closure, a ν layer and a loop's round are
-- all computations in the one monad `T∞`, which may perform SigOps or run
-- forever (D317, `Once.IR.Semantics.Iterative`, copied below). A term's
-- effects are visible in its run's events; no index on the term is needed.
--
-- Base leaves and SigOps are PARAMETERS: nothing below depends on what an
-- `Int` is or which operations exist.
--
-- `--safe --guardedness`, no sized types, no postulates, no holes; imports:
-- the standard library only.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import LinCore.Flat using (FTy; funit; fvoid; fw; _f*_; _f+_; ⟦_⟧F)

module LinCore.NbEPLinCore
  (Base : Set) (⟦_⟧b : Base → Set)
  -- ★ A12: the SigOps take and answer FLAT values (the Spec's `BTy`: an
  -- `Int → Int` op, an emit answering `unit`, an exit answering `void`, …)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  where

-- a flat value
⟦_⟧f : FTy Base → Set
⟦_⟧f = ⟦ ⟦_⟧b ⟧F

------------------------------------------------------------------------
-- 0. THE COMPUTATION MONAD (D317; `Once.IR.Semantics.Trace`/`.Iterative`).
--
-- `T` is finite trees: a BLOCK that calls SigOps and returns, or halts.
-- `T∞ X = νY. T (X + Y)`: a run is a block that ends with the result or with
-- the rest of the run (a silent step, what a loop's round that calls nothing
-- is).
------------------------------------------------------------------------

data T (X : Set) : Set where
  ret  : X → T X
  call : (s : Sig) → ⟦ sdom s ⟧f → (⟦ scod s ⟧f → T X) → T X
  halt : (s : Sig) → ⟦ sdom s ⟧f → T X

record T∞ (X : Set) : Set where
  coinductive
  field block : T (X ⊎ T∞ X)
open T∞ public

return∞ : ∀ {X} → X → T∞ X
block (return∞ x) = ret (inj₁ x)

infixl 1 _>>=∞_
_>>=∞_    : ∀ {X Y} → T∞ X → (X → T∞ Y) → T∞ Y
bindBlock : ∀ {X Y} → T (X ⊎ T∞ X) → (X → T∞ Y) → T (Y ⊎ T∞ Y)
block (m >>=∞ k) = bindBlock (block m) k
bindBlock (ret (inj₁ x)) k = block (k x)
bindBlock (ret (inj₂ m)) k = ret (inj₂ (m >>=∞ k))
bindBlock (call s a c)   k = call s a (λ b → bindBlock (c b) k)
bindBlock (halt s a)     k = halt s a

fmap∞ : ∀ {X Y} → (X → Y) → T∞ X → T∞ Y
fmap∞ f m = m >>=∞ λ x → return∞ (f x)

-- a SigOp that ends the program
haltT : ∀ {X} (s : Sig) → ⟦ sdom s ⟧f → T∞ X
block (haltT s x) = halt s x

-- Elgot iteration: a round's end that continues is a silent step
iterRun   : ∀ {A B : Set} → (A → T∞ (B ⊎ A)) → T∞ (B ⊎ A) → T∞ B
iterBlock : ∀ {A B : Set} → (A → T∞ (B ⊎ A)) → T ((B ⊎ A) ⊎ T∞ (B ⊎ A)) → T (B ⊎ T∞ B)
block (iterRun f m) = iterBlock f (block m)
iterBlock f (ret (inj₁ (inj₁ b))) = ret (inj₁ b)
iterBlock f (ret (inj₁ (inj₂ a))) = ret (inj₂ (iterRun f (f a)))
iterBlock f (ret (inj₂ m))        = ret (inj₂ (iterRun f m))
iterBlock f (call s x k)          = call s x (λ v → iterBlock f (k v))
iterBlock f (halt s x)            = halt s x

iter∞ : ∀ {A B : Set} → (A → T∞ (B ⊎ A)) → A → T∞ B
iter∞ f a = iterRun f (f a)

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
  Kzero : LF                -- ★ A12: the constant `Void` (the Spec's `K Void`)
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
data LTy : Set where
  One  : LTy
  Zero : LTy
  _⊗t_ : LTy → LTy → LTy
  _⊕t_ : LTy → LTy → LTy
  -- ★ D405: a CLOSURE is its environment `X`, tagged with its code: the label
  -- `l` of one lambda of the program (`Cx`). Its type names the code, so
  -- nothing at run time does: no code word, no cell. Where lambdas meet, the
  -- type is a sum of these, and the sum's tag is the run-time choice.
  Ct   : ℕ → LTy → LTy
  μt   : LF → LTy
  νt   : LF → LTy          -- ★ present because the theory wants it
  Bt   : Base → LTy        -- ★ likewise

-- the functor acting on object types
LF∙ : LF → LTy → LTy
LF∙ Idf       X = X
LF∙ Kone      X = One
LF∙ Kzero     X = Zero
LF∙ (Kb b)    X = Bt b
LF∙ (Kμ G)    X = μt G
LF∙ (Kν G)    X = νt G
LF∙ (F ⊕f G)  X = LF∙ F X ⊕t LF∙ G X
LF∙ (F ⊗f G)  X = LF∙ F X ⊗t LF∙ G X

------------------------------------------------------------------------
-- 3. ★ THE VALUES — one knot for both fixpoints.
--
-- `Mu` (inductive) and `Nu` (coinductive: observing it is a computation, as
-- master's `νᴵ`) share `FS`. Putting them in ONE mutual block is the payoff of
-- §1's restriction on `LF`: neither mentions `⟦_⟧`, so no object type can
-- taint their positivity.
------------------------------------------------------------------------

mutual
  FS : LF → Set → Set
  FS Idf      X = X
  FS Kone     X = ⊤
  FS Kzero    X = ⊥
  FS (Kb b)   X = ⟦ b ⟧b
  FS (Kμ G)   X = Mu G
  FS (Kν G)   X = Nu G
  FS (F ⊕f G) X = FS F X ⊎ FS G X
  FS (F ⊗f G) X = FS F X × FS G X

  data Mu (F : LF) : Set where
    inμ : FS F (Mu F) → Mu F

  record Nu (F : LF) : Set where
    coinductive
    field force : T∞ (FS F (Nu F))
open Nu public

outμ : ∀ {F} → Mu F → FS F (Mu F)
outμ (inμ w) = w

-- a ν built from a layer: observing it gives the layer, with no event
inν : ∀ {F} → FS F (Nu F) → Nu F
force (inν w) = return∞ w

⟦_⟧ : LTy → Set
⟦ One ⟧      = ⊤
⟦ Zero ⟧     = ⊥
⟦ A ⊗t B ⟧   = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⊕t B ⟧   = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ Ct l X ⟧   = ⟦ X ⟧                -- defunctionalised: a closure means its environment
⟦ μt F ⟧     = Mu F
⟦ νt F ⟧     = Nu F
⟦ Bt b ⟧     = ⟦ b ⟧b

------------------------------------------------------------------------
-- 4. THE FUNCTOR COHERENCE.
------------------------------------------------------------------------

-- `⟦ LF∙ F X ⟧ ≅ FS F ⟦ X ⟧` — an identity on every leaf, by construction.
coh : ∀ F X → ⟦ LF∙ F X ⟧ → FS F ⟦ X ⟧
coh Idf      X x        = x
coh Kone     X x        = x
coh Kzero    X ()
coh (Kb b)   X x        = x
coh (Kμ G)   X x        = x
coh (Kν G)   X x        = x
coh (F ⊕f G) X (inj₁ x) = inj₁ (coh F X x)
coh (F ⊕f G) X (inj₂ y) = inj₂ (coh G X y)
coh (F ⊗f G) X (x , y)  = (coh F X x , coh G X y)

coh⁻¹ : ∀ F X → FS F ⟦ X ⟧ → ⟦ LF∙ F X ⟧
coh⁻¹ Idf      X x        = x
coh⁻¹ Kone     X x        = x
coh⁻¹ Kzero    X ()
coh⁻¹ (Kb b)   X x        = x
coh⁻¹ (Kμ G)   X x        = x
coh⁻¹ (Kν G)   X x        = x
coh⁻¹ (F ⊕f G) X (inj₁ x) = inj₁ (coh⁻¹ F X x)
coh⁻¹ (F ⊕f G) X (inj₂ y) = inj₂ (coh⁻¹ G X y)
coh⁻¹ (F ⊗f G) X (x , y)  = (coh⁻¹ F X x , coh⁻¹ G X y)

------------------------------------------------------------------------
-- 4½. ★ A12: FLAT TYPES IN THE CORE. A flat type is a core type with no cell
-- (no μ, ν or arrow); its values and the core's are the same, by recursion.
------------------------------------------------------------------------

⌜_⌝ : FTy Base → LTy
⌜ funit ⌝    = One
⌜ fvoid ⌝    = Zero
⌜ fw b ⌝     = Bt b
⌜ a f* b ⌝   = ⌜ a ⌝ ⊗t ⌜ b ⌝
⌜ a f+ b ⌝   = ⌜ a ⌝ ⊕t ⌜ b ⌝

toF : ∀ a → ⟦ ⌜ a ⌝ ⟧ → ⟦ a ⟧f
toF funit    x        = x
toF fvoid    ()
toF (fw b)   x        = x
toF (a f* b) (x , y)  = (toF a x , toF b y)
toF (a f+ b) (inj₁ x) = inj₁ (toF a x)
toF (a f+ b) (inj₂ y) = inj₂ (toF b y)

fromF : ∀ a → ⟦ a ⟧f → ⟦ ⌜ a ⌝ ⟧
fromF funit    x        = x
fromF fvoid    ()
fromF (fw b)   x        = x
fromF (a f* b) (x , y)  = (fromF a x , fromF b y)
fromF (a f+ b) (inj₁ x) = inj₁ (fromF a x)
fromF (a f+ b) (inj₂ y) = inj₂ (fromF b y)

-- one SigOp call: the argument out as a flat value, the world's answer back
callT : (s : Sig) → ⟦ ⌜ sdom s ⌝ ⟧ → T∞ ⟦ ⌜ scod s ⌝ ⟧
block (callT s x) = call s (toF (sdom s) x) (λ y → ret (inj₁ (fromF (scod s) y)))

------------------------------------------------------------------------
-- 5. THE LINEAR CORE.
--
-- `dup`/`drop` are the only sources of duplication and discard. `lOutμ` and
-- `lInν` are the two Lambek isomorphisms: one unwrapping each, no recursion.
------------------------------------------------------------------------

infixr 9 _∘l_
infixr 7 _⊗l_

-- ★ D405: THE LABELS. A label's signature: its kind, environment, domain and
-- codomain. A ONE-SHOT body owns its environment; a MANY-USE one (D131) reads
-- it lent, so it can be applied while lent, at every layer of a fold.
data Kd : Set where
  once many : Kd

record Sg : Set where
  constructor sg
  field kd : Kd
        env dom cod : LTy
open Sg public

-- the labels in scope, oldest first: each body is typed over the ones before
-- it, as a lambda's body only builds the lambdas nested in it
infixl 4 _▸_
data Cx : Set where
  ε   : Cx
  _▸_ : Cx → Sg → Cx

len : Cx → ℕ
len ε       = zero
len (Γ ▸ _) = suc (len Γ)

-- label `l`, counted from the oldest: it names the same entry in every extension
data _∋[_]_ : Cx → ℕ → Sg → Set where
  here  : ∀ {Γ σ} → (Γ ▸ σ) ∋[ len Γ ] σ
  there : ∀ {Γ σ τ l} → Γ ∋[ l ] σ → (Γ ▸ τ) ∋[ l ] σ

-- ★ plan 0.146 A10: ONE term language.  `Tm E A B` is a morphism `A → B` that
-- OWNS its input and may READ a lent `E`: never frees it, never keeps it.  What
-- a result keeps of `E` is copied out (`bcopy`, D402's choice A), so the owner
-- frees `E` whole, once, after the scope.  `E` is not a type of the core's
-- values (there is no borrow type), so a borrow cannot escape into a result, a
-- closure's environment or a ν's seed: those bodies are closed over `One`.
-- Every generator exists at every `E`; a term with nothing lent is `LTm`.
-- `E` comes last among the implicits so that `lIn {F}`, `linl {A} {B}` still read.
-- ★ D405: `Γ`, the labels in scope, is a parameter: a body is not a term's
-- part but a table entry (`Defs`), so every generator is at the same `Γ`.
data Tm (Γ : Cx) : LTy → LTy → LTy → Set where
  lid     : ∀ {A E} → Tm Γ E A A
  _∘l_    : ∀ {A B C E} → Tm Γ E B C → Tm Γ E A B → Tm Γ E A C
  _⊗l_    : ∀ {A B C D E} → Tm Γ E A B → Tm Γ E C D → Tm Γ E (A ⊗t C) (B ⊗t D)
  -- unitors, associator, braiding: the SMC structure.  All free — moving data
  -- is not copying it.
  ρl      : ∀ {A E} → Tm Γ E (A ⊗t One) A
  ρl⁻     : ∀ {A E} → Tm Γ E A (A ⊗t One)
  lul     : ∀ {A E} → Tm Γ E (One ⊗t A) A
  lul⁻    : ∀ {A E} → Tm Γ E A (One ⊗t A)
  lassoc  : ∀ {A B C E} → Tm Γ E ((A ⊗t B) ⊗t C) (A ⊗t (B ⊗t C))
  lassoc⁻ : ∀ {A B C E} → Tm Γ E (A ⊗t (B ⊗t C)) ((A ⊗t B) ⊗t C)
  lswap   : ∀ {A B E} → Tm Γ E (A ⊗t B) (B ⊗t A)
  -- ★ THE COMONOID — the only sources of duplication / discard
  dup     : ∀ {A E} → Tm Γ E A (A ⊗t A)
  drop    : ∀ {A E} → Tm Γ E A One
  -- additive coproducts, and the initial object
  linl    : ∀ {A B E} → Tm Γ E A (A ⊕t B)
  linr    : ∀ {A B E} → Tm Γ E B (A ⊕t B)
  lcase   : ∀ {A B C E} → Tm Γ E A C → Tm Γ E B C → Tm Γ E (A ⊕t B) C
  lzero   : ∀ {A E} → Tm Γ E Zero A
  -- initial algebra: constructor, DESTRUCTOR, fold (★ reads `E` at every layer,
  -- with no copy of `E`)
  lIn     : ∀ {F E} → Tm Γ E (LF∙ F (μt F)) (μt F)
  lOutμ   : ∀ {F E} → Tm Γ E (μt F) (LF∙ F (μt F))
  lcata   : ∀ F {A E} → Tm Γ E (LF∙ F A) A → Tm Γ E (μt F) A
  -- ★ final coalgebra: observation, unfold, and the dual constructor.  A
  -- coalgebra outlives every scope, so it reads nothing lent.
  lOut    : ∀ {F E} → Tm Γ E (νt F) (LF∙ F (νt F))
  lAna    : ∀ F {A E} → Tm Γ One A (LF∙ F A) → Tm Γ E A (νt F)
  lInν    : ∀ {F E} → Tm Γ E (LF∙ F (νt F)) (νt F)
  -- ★ D405, closed structure, defunctionalised: a closure of label `l` is its
  -- environment, tagged (no event); applying it calls `l`'s body directly.
  -- A one-shot closure is applied owned, a many-use one (D131) lent.
  lclo    : ∀ {l k X A B E} → Γ ∋[ l ] sg k X A B → Tm Γ E X (Ct l X)
  lapp    : ∀ {l X A B E} → Γ ∋[ l ] sg once X A B → Tm Γ E (Ct l X ⊗t A) B
  -- ★ the scope: lend `X` to a body, which also reads what was lent already;
  -- `X` comes back unchanged.
  lend    : ∀ {E X A B} → Tm Γ (E ⊗t X) A B → Tm Γ E (X ⊗t A) (X ⊗t B)
  -- a step that reads nothing of what is lent
  blift   : ∀ {A B E} → Tm Γ One A B → Tm Γ E A B
  -- reading the lent value: a part of it, its tag, inside a node (all views)
  bfst    : ∀ {E₁ E₂ A B} → Tm Γ E₁ A B → Tm Γ (E₁ ⊗t E₂) A B
  bsnd    : ∀ {E₁ E₂ A B} → Tm Γ E₂ A B → Tm Γ (E₁ ⊗t E₂) A B
  bcaseE  : ∀ {E₁ E₂ A B} → Tm Γ E₁ A B → Tm Γ E₂ A B → Tm Γ (E₁ ⊕t E₂) A B
  bout    : ∀ {F A B} → Tm Γ (LF∙ F (μt F)) A B → Tm Γ (μt F) A B
  -- keeping it: a copy (fresh cells; a word costs nothing)
  bcopy   : ∀ {E} → Tm Γ E One E
  -- applying a LENT many-use closure (D131: a fold's algebra, obtained once,
  -- applied at every layer): its environment is lent on to its body
  bapp    : ∀ {l X A B} → Γ ∋[ l ] sg many X A B → Tm Γ (Ct l X) A B
  -- ★ A11: the SigOps, anywhere a term can be. `lop`: Pure or Emits, an event
  -- and the world's answer; `lhalt`: Halts, the run ends
  lop     : (s : Sig) → ∀ {E} → Tm Γ E ⌜ sdom s ⌝ ⌜ scod s ⌝
  lhalt   : (s : Sig) → ∀ {E} → Tm Γ E ⌜ sdom s ⌝ Zero
  -- ★ A11: the loop (D317): the round reads `E` and the state, and ends with
  -- the result (`inl`) or the next state (`inr`)
  liter   : ∀ {A B E} → Tm Γ E A (B ⊕t A) → Tm Γ E A B

-- a term with nothing lent
LTm : Cx → LTy → LTy → Set
LTm Γ = Tm Γ One

-- ★ D405: a label's body, by its kind: a one-shot body owns its environment,
-- a many-use body reads it lent
data Body (Γ : Cx) : Sg → Set where
  b1 : ∀ {X A B} → LTm Γ (X ⊗t A) B → Body Γ (sg once X A B)
  bω : ∀ {X A B} → Tm Γ X A B → Body Γ (sg many X A B)

-- ★ D405: the program's table, each body over the labels before it
data Defs : Cx → Set where
  ε   : Defs ε
  _▸_ : ∀ {Γ σ} → Defs Γ → Body Γ σ → Defs (Γ ▸ σ)

-- what label `l` runs: its body, over its own prefix of the table
data Look : ∀ {Γ Δ l σ} → Defs Γ → Γ ∋[ l ] σ → Defs Δ → Body Δ σ → Set where
  lk-here  : ∀ {Γ σ} {ds : Defs Γ} {b : Body Γ σ} → Look (ds ▸ b) here ds b
  lk-there : ∀ {Γ Δ l σ τ} {ds : Defs Γ} {p : Γ ∋[ l ] σ} {ds′ : Defs Δ} {b} {c : Body Γ τ}
           → Look ds p ds′ b → Look (ds ▸ c) (there p) ds′ b

------------------------------------------------------------------------
-- 6. ★ THE MEANING, mutual with the recursion operators (`evalᴰ`'s shape).
--
-- `cataC`/`travC` descend a shrinking `Mu`, children left to right, then the
-- algebra; `unfoldNu` and its helpers corecurse under `force`/`block`.
--
-- ★ D405: at the meaning `ρ` of the labels in scope. A label means a function
-- of its environment and its argument; applying a closure looks it up. The
-- recursion is structural: a body is met only when the table is built
-- (`⟦_⟧D`), over the labels before it.
------------------------------------------------------------------------

-- the meaning of the labels in scope
data Env : Cx → Set where
  ε   : Env ε
  _▸_ : ∀ {Γ σ} → Env Γ → (⟦ env σ ⟧ → ⟦ dom σ ⟧ → T∞ ⟦ cod σ ⟧) → Env (Γ ▸ σ)

lookup : ∀ {Γ l σ} → Env Γ → Γ ∋[ l ] σ → ⟦ env σ ⟧ → ⟦ dom σ ⟧ → T∞ ⟦ cod σ ⟧
lookup (ρ ▸ f) here      = f
lookup (ρ ▸ f) (there p) = lookup ρ p

module Sem {Γ : Cx} (ρ : Env Γ) where
  mutual
    -- a term means a function of the lent value, which it does not consume, and
    -- of its input, which it does
    Lᶜ : ∀ {E A B} → Tm Γ E A B → ⟦ E ⟧ → ⟦ A ⟧ → T∞ ⟦ B ⟧
    Lᶜ lid            e         x              = return∞ x
    Lᶜ (f ∘l g)       e         x              = Lᶜ g e x >>=∞ Lᶜ f e
    Lᶜ (f ⊗l g)       e         (a , b)        = Lᶜ f e a >>=∞ λ a' → fmap∞ (a' ,_) (Lᶜ g e b)
    Lᶜ ρl             e         (a , tt)       = return∞ a
    Lᶜ ρl⁻            e         a              = return∞ (a , tt)
    Lᶜ lul            e         (tt , a)       = return∞ a
    Lᶜ lul⁻           e         a              = return∞ (tt , a)
    Lᶜ lassoc         e         ((a , b) , c)  = return∞ (a , (b , c))
    Lᶜ lassoc⁻        e         (a , (b , c))  = return∞ ((a , b) , c)
    Lᶜ lswap          e         (a , b)        = return∞ (b , a)
    Lᶜ dup            e         a              = return∞ (a , a)
    Lᶜ drop           e         a              = return∞ tt
    Lᶜ linl           e         a              = return∞ (inj₁ a)
    Lᶜ linr           e         b              = return∞ (inj₂ b)
    Lᶜ (lcase f g)    e         (inj₁ a)       = Lᶜ f e a
    Lᶜ (lcase f g)    e         (inj₂ b)       = Lᶜ g e b
    Lᶜ lzero          e         ()
    Lᶜ (lIn {F})      e         x              = return∞ (inμ (coh F (μt F) x))
    Lᶜ (lOutμ {F})    e         x              = return∞ (coh⁻¹ F (μt F) (outμ x))
    Lᶜ (lcata F alg)  e         x              = cataC F (λ y → Lᶜ alg e (coh⁻¹ F _ y)) x
    Lᶜ (lOut {F})     e         x              = fmap∞ (coh⁻¹ F (νt F)) (force x)
    Lᶜ (lAna F c)     e         a              = return∞ (unfoldNu F c a)
    Lᶜ (lInν {F})     e         x              = return∞ (inν (coh F (νt F) x))
    Lᶜ (lclo p)       e         x              = return∞ x
    Lᶜ (lapp p)       e         (x , a)        = lookup ρ p x a
    Lᶜ (lend b)       e         (x , a)        = fmap∞ (x ,_) (Lᶜ b (e , x) a)
    Lᶜ (blift f)      e         a              = Lᶜ f tt a
    Lᶜ (bfst f)       (e₁ , e₂) a              = Lᶜ f e₁ a
    Lᶜ (bsnd f)       (e₁ , e₂) a              = Lᶜ f e₂ a
    Lᶜ (bcaseE f g)   (inj₁ e)  a              = Lᶜ f e a
    Lᶜ (bcaseE f g)   (inj₂ e)  a              = Lᶜ g e a
    Lᶜ (bout {F} f)   e         a              = Lᶜ f (coh⁻¹ F (μt F) (outμ e)) a
    Lᶜ bcopy          e         a              = return∞ e
    Lᶜ (bapp p)       x         a              = lookup ρ p x a
    Lᶜ (lop s)        e         x              = callT s x
    Lᶜ (lhalt s)      e         x              = haltT s (toF (sdom s) x)
    Lᶜ (liter f)      e         a              = iter∞ (Lᶜ f e) a

    cataC : ∀ F {X : Set} → (FS F X → T∞ X) → Mu F → T∞ X
    cataC F alg (inμ w) = travC F F alg w >>=∞ alg

    travC : ∀ F G {X : Set} → (FS F X → T∞ X) → FS G (Mu F) → T∞ (FS G X)
    travC F Idf      alg y        = cataC F alg y
    travC F Kone     alg y        = return∞ y
    travC F Kzero    alg ()
    travC F (Kb _)   alg y        = return∞ y
    travC F (Kμ _)   alg y        = return∞ y
    travC F (Kν _)   alg y        = return∞ y
    travC F (G ⊕f H) alg (inj₁ y) = fmap∞ inj₁ (travC F G alg y)
    travC F (G ⊕f H) alg (inj₂ z) = fmap∞ inj₂ (travC F H alg z)
    travC F (G ⊗f H) alg (y , z)  = travC F G alg y >>=∞ λ u → fmap∞ (u ,_) (travC F H alg z)

    unfoldNu : ∀ {A} F → LTm Γ A (LF∙ F A) → ⟦ A ⟧ → Nu F
    force (unfoldNu F c a) = unfoldRun F c (Lᶜ c tt a)

    -- written out, not `fmap∞`: the corecursive call must stay guarded
    unfoldRun : ∀ {A} F → LTm Γ A (LF∙ F A) → T∞ ⟦ LF∙ F A ⟧ → T∞ (FS F (Nu F))
    block (unfoldRun F c m) = unfoldBlock F c (block m)

    unfoldBlock : ∀ {A} F → LTm Γ A (LF∙ F A) → T (⟦ LF∙ F A ⟧ ⊎ T∞ ⟦ LF∙ F A ⟧) → T (FS F (Nu F) ⊎ T∞ (FS F (Nu F)))
    unfoldBlock {A} F c (ret (inj₁ y)) = ret (inj₁ (mapU F F c (coh F A y)))
    unfoldBlock F c (ret (inj₂ m))     = ret (inj₂ (unfoldRun F c m))
    unfoldBlock F c (call s x k)       = call s x (λ v → unfoldBlock F c (k v))
    unfoldBlock F c (halt s x)         = halt s x

    mapU : ∀ {A} F G → LTm Γ A (LF∙ F A) → FS G ⟦ A ⟧ → FS G (Nu F)
    mapU F Idf      c y        = unfoldNu F c y
    mapU F Kone     c y        = y
    mapU F Kzero    c ()
    mapU F (Kb _)   c y        = y
    mapU F (Kμ _)   c y        = y
    mapU F (Kν _)   c y        = y
    mapU F (G ⊕f H) c (inj₁ y) = inj₁ (mapU F G c y)
    mapU F (G ⊕f H) c (inj₂ z) = inj₂ (mapU F H c z)
    mapU F (G ⊗f H) c (y , z)  = (mapU F G c y , mapU F H c z)

open Sem public

------------------------------------------------------------------------
-- 7. ★ D405: THE TABLE'S MEANING, built in order: each body means a function
-- over the labels before it.
------------------------------------------------------------------------

-- what a body means, at the meaning of its prefix
⟦_⟧Bd : ∀ {Γ σ} → Body Γ σ → Env Γ → ⟦ env σ ⟧ → ⟦ dom σ ⟧ → T∞ ⟦ cod σ ⟧
⟦ b1 b ⟧Bd ρ x a = Lᶜ ρ b tt (x , a)
⟦ bω b ⟧Bd ρ x a = Lᶜ ρ b x a

⟦_⟧D : ∀ {Γ} → Defs Γ → Env Γ
⟦ ε ⟧D      = ε
⟦ ds ▸ b ⟧D = ⟦ ds ⟧D ▸ ⟦ b ⟧Bd ⟦ ds ⟧D

-- applying a closure means running its label's body (by induction on the label)
lookup-look : ∀ {Γ Δ l σ} {ds : Defs Γ} {p : Γ ∋[ l ] σ} {ds′ : Defs Δ} {b : Body Δ σ}
            → Look ds p ds′ b → ∀ x a → lookup ⟦ ds ⟧D p x a ≡ ⟦ b ⟧Bd ⟦ ds′ ⟧D x a
lookup-look lk-here      x a = refl
lookup-look (lk-there q) x a = lookup-look q x a
