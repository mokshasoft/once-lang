-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Core — THE LINEAR CORE (plan 0.146; D420): its types, values and
-- terms, at the target's numerics alone (D457: what is compiled sees no
-- Interpretation; the meaning, at the pure FFI answers too, is `NbEPLinCore`).
--
-- Started as OCP-0009's `NbEPLinCore` (`origin/plan-ref`), and now the one
-- term language of the spike:
--
--   * `LF` — polynomial functor codes, kept OBJECT-LANGUAGE-INDEPENDENT. A
--     constant is `Kone`, an inert leaf `Kb`, or a CODE (`Kμ`), never an
--     arbitrary `LTy`: that is what makes `Mu` strictly positive with no pragma.
--   * `LTy` — with base leaves from the start. ★ D426 part 3: the EXPONENTIAL
--     `Fn k g A B`, the Spec's `A ⇒[ mk-kind q π ] B`, meaning
--     `⟦ A ⟧ → M π ⟦ B ⟧`; a closure whose lambda one site alone receives may
--     instead be `Ct l X`, its environment tagged with its label (D422), and
--     a ν is such a closure: its label is its coalgebra, its environment its
--     seed (D423).
--   * `Cx`, `Defs` — the program's labels and their bodies, each typed over
--     the labels before it (one-shot or many-use, D131).
--   * `Tm E A B` — every generator: symmetric monoidal over `⊗t`, additive
--     coproducts, an EXPLICIT comonoid (`dup`/`drop`), both fixpoints, closures,
--     a lent context `E` (A10), and the SigOps and the loop (A11).
--   * `Lᶜ` — the meaning of a term: a computation in `T∞` (`NbEPLinCore`).
--
-- NO GENERAL FIXPOINT. `Mu` is the initial algebra of a polynomial code; the
-- recursion generators are `lcata` (structural) and `liter` (the loop, which
-- may run forever). ★ D423: a ν is DEFUNCTIONALISED (its coalgebra is a
-- label, its value its seed), so its meaning needs no coinductive type:
-- observing it is a call (`lobs`).
--
-- ★ A11: ONE MEANING, as master's `evalᴰ`. The IR is ungraded (Plan 0.52 M2:
-- one exponential per `(A, B)`), so a closure, a ν observation and a loop's round are
-- all computations in the one monad `T∞`, which may perform SigOps or run
-- forever (D317, `Once.IR.Semantics.Iterative`, copied below). A term's
-- effects are visible in its run's events.
--
-- ★ THE SPEC'S GRADES (D429): a term's grade is a judgment on it, as the
-- Spec's `⊢ t ∷ A ! π` is on its raw terms. `Blk t` is grade `act` (a finite
-- block); a label carries its arrow's grade; the loop's round is a `Blk`
-- (`⊢iter`), so is a coalgebra (`⊢unfold`). `Once.LinCore.Grade` proves that a
-- block means a finite computation and the loop the Spec's `loop` of it.
--
-- ★ B1.2 (plan 0.146): the core is MASTER'S. Its monad is master's `T`/`T∞`
-- (`Once.IR.Semantics.Trace`/`.Iterative`), its base words master's `Int` and
-- `Float`, and a SigOp is master's `SigOpInfo`, meaning its contract's block
-- (`DenotTrace.sigOpT`: a pure op returns, an effect calls, a halting op
-- halts). The target's numerics are the module's parameter; the pure FFI
-- answers are the meaning's (`NbEPLinCore`), as they are `evalᴰ`'s.
--
-- `--safe --guardedness`, no sized types, no postulates, no holes.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import Once.LinCore.Flat
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Word
import Once.Float.Word
import Once.Spec.Numerics
open import Once.Spec.Type using (Type; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
import Once.IR.Semantics.Value Carrier Carrier as Val

module Once.LinCore.Core (fmt : TargetNum) where

open Once.LinCore.Flat using (FTy; funit; fvoid; fw; _f*_; _f+_; ⟦_⟧F; Base; int; float; ⟦_⟧b; Lit)

-- ★ D450: a literal materialized at the target's format (D113: FromIR's function, now the meaning's)
lit : ∀ {b} → Lit b → ⟦ b ⟧b
lit {int}   z = Once.Spec.Word.Width.fromℤ (Once.Spec.Numerics.TargetNum.int-bits fmt) z
lit {float} d = Once.Float.Word.round (Once.Spec.Numerics.TargetNum.float-format fmt) d

open import Once.IR.Semantics.Trace using (T; ret; call; halt; CallOp; HaltOp)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; bindBlock; fmap∞; iterRun; iterBlock; iter∞)
open T∞ using (force)

-- a computation's first block (`T∞`'s field, observed); its importers read
-- `block m`, and values are built by the field itself (`force`, copatterns)
block : ∀ {X} → T∞ X → T (X ⊎ T∞ X)
block = force

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


-- ★ a FINITE BLOCK's monad, the Spec's `M act` (`Spec.Effect`: `M (fin f)`)
bindT : ∀ {X Y} → T X → (X → T Y) → T Y
bindT (ret x)      k = k x
bindT (call s a c) k = call s a (λ b → bindT (c b) k)
bindT (halt s a)   k = halt s a

fmapT : ∀ {X Y} → (X → Y) → T X → T Y
fmapT f m = bindT m λ x → ret (f x)

-- one block is a computation: the monad morphism `T → T∞` (the Spec's `embed`)
embB : ∀ {X} → T X → T (X ⊎ T∞ X)
embB (ret x)      = ret (inj₁ x)
embB (call s a k) = call s a (λ y → embB (k y))
embB (halt s a)   = halt s a

emb : ∀ {X} → T X → T∞ X
force (emb b) = embB b

------------------------------------------------------------------------
-- 1. POLYNOMIAL FUNCTOR CODES.
--
-- ★ `LF` mentions no `LTy`.  Its constants are the Unit leaf, an INERT base
-- leaf, or the CODE of another inductive type — `Kμ`, never an arbitrary
-- object type.  That restriction is the reason `Mu` below is strictly positive
-- with no pragma. It is also the honest reading of what a functor code is FOR:
-- codes store sub-codes and leaves; a function type is never a functor
-- position. ★ D423: nor is a ν (the Spec's functor constants are base types,
-- `WFFun`): a ν is a closure, and its label is not a code.
------------------------------------------------------------------------

infixr 6 _⊕f_
infixr 7 _⊗f_
data LF : Set where
  Idf  : LF
  Kone : LF
  Kzero : LF                -- ★ A12: the constant `Void` (the Spec's `K Void`)
  Kb   : Base → LF          -- ★ inert leaf
  Kμ   : LF → LF            -- a code: the initial algebra of another functor
  _⊕f_ : LF → LF → LF
  _⊗f_ : LF → LF → LF

------------------------------------------------------------------------
-- 2. THE OBJECT LANGUAGE.
------------------------------------------------------------------------

-- an arrow's quantity (the Spec's `q`): a ONE-SHOT closure owns its
-- environment; a MANY-USE one (D131) reads it lent
data Kd : Set where
  once many : Kd

-- ★ the Spec's grades (`Spec.Grade`), as far as the core tells them apart: a
-- FINITE BLOCK (`act`: finitely many events, then a value or a halt; the
-- Spec's `pure` is the block with no event) or a computation that may run
-- forever (`eff`: it contains a loop). An arrow's grade (the Spec's
-- `mk-kind q π`: `Kd` is `q`, `Gr` is `π`).
data Gr : Set where
  act eff : Gr

-- ★ the Spec's `M π`: a finite block means a `T`, the rest a `T∞`
Mg : Gr → Set → Set
Mg act X = T X
Mg eff X = T∞ X

-- the Spec's `act ⊑ eff`
up : ∀ g {X} → Mg g X → T∞ X
up act m = emb m
up eff m = m

infixr 5 _⊗t_
infixr 4 _⊕t_
data LTy : Set where
  One  : LTy
  Zero : LTy
  _⊗t_ : LTy → LTy → LTy
  _⊕t_ : LTy → LTy → LTy
  -- ★ D422: a CLOSURE is its environment `X`, tagged with its code: the label
  -- `l` of one lambda of the program (`Cx`). Its type names the code, so
  -- nothing at run time does: no code word, no cell. Where lambdas meet, the
  -- type is a sum of these, and the sum's tag is the run-time choice.
  -- ★ D423: a ν is one of these: its coalgebra's label and its seed.
  Ct   : ℕ → LTy → LTy
  -- ★ D426 part 3: THE EXPONENTIAL, the Spec's `A ⇒[ mk-kind q π ] B`: a
  -- closure whose lambda need not be known at compile time (it may be decided
  -- by data: nested through a fold's carrier or a server's state). `Ct` is
  -- its representation where one lambda reaches a site.
  Fn   : Kd → Gr → LTy → LTy → LTy
  -- ★ the Spec's `ν F`, observed in finite blocks: a value of it may come
  -- from any coalgebra, which data may decide (D423's `Ct l S` is its
  -- representation where one coalgebra reaches a site)
  Nu   : LF → LTy
  μt   : LF → LTy
  Bt   : Base → LTy        -- ★ present because the theory wants it

-- the functor acting on object types
LF∙ : LF → LTy → LTy
LF∙ Idf       X = X
LF∙ Kone      X = One
LF∙ Kzero     X = Zero
LF∙ (Kb b)    X = Bt b
LF∙ (Kμ G)    X = μt G
LF∙ (F ⊕f G)  X = LF∙ F X ⊕t LF∙ G X
LF∙ (F ⊗f G)  X = LF∙ F X ⊗t LF∙ G X

------------------------------------------------------------------------
-- 3. ★ THE VALUES.
--
-- `Mu` and `FS` in one mutual block: the payoff of §1's restriction on `LF`:
-- neither mentions `⟦_⟧`, so no object type can taint `Mu`'s positivity.
-- ★ D423: no `Nu`: a ν means its seed (it is a closure, §5).
------------------------------------------------------------------------

mutual
  FS : LF → Set → Set
  FS Idf      X = X
  FS Kone     X = ⊤
  FS Kzero    X = ⊥
  FS (Kb b)   X = ⟦ b ⟧b
  FS (Kμ G)   X = Mu G
  FS (F ⊕f G) X = FS F X ⊎ FS G X
  FS (F ⊗f G) X = FS F X × FS G X

  data Mu (F : LF) : Set where
    inμ : FS F (Mu F) → Mu F

outμ : ∀ {F} → Mu F → FS F (Mu F)
outμ (inμ w) = w

-- ★ THE FINAL COALGEBRA of `T ∘ F`, the Spec's `νM act` (`Spec.Effect`):
-- observing a value runs a finite block that gives a layer
record Nuᵐ (F : LF) : Set where
  coinductive
  field outν : T (FS F (Nuᵐ F))
open Nuᵐ

-- the unfold, as the Spec's `anaA`: each observation runs the coalgebra on the
-- seed, and the layer's seeds become the unfolds of the same coalgebra
anaN  : ∀ F {X : Set} → (X → T (FS F X)) → X → Nuᵐ F
treeN : ∀ F {X : Set} → (X → T (FS F X)) → T (FS F X) → T (FS F (Nuᵐ F))
mapN  : ∀ F G {X : Set} → (X → T (FS F X)) → FS G X → FS G (Nuᵐ F)
outν (anaN F c x) = treeN F c (c x)
treeN F c (ret l)      = ret (mapN F F c l)
treeN F c (call s a k) = call s a (λ b → treeN F c (k b))
treeN F c (halt s a)   = halt s a
mapN F Idf      c x        = anaN F c x
mapN F Kone     c x        = x
mapN F Kzero    c ()
mapN F (Kb b)   c x        = x
mapN F (Kμ G)   c x        = x
mapN F (G ⊕f H) c (inj₁ x) = inj₁ (mapN F G c x)
mapN F (G ⊕f H) c (inj₂ y) = inj₂ (mapN F H c y)
mapN F (G ⊗f H) c (x , y)  = (mapN F G c x , mapN F H c y)

⟦_⟧ : LTy → Set
⟦ One ⟧      = ⊤
⟦ Zero ⟧     = ⊥
⟦ A ⊗t B ⟧   = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⊕t B ⟧   = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ Ct l X ⟧   = ⟦ X ⟧                -- defunctionalised: a closure means its environment
⟦ Fn k g A B ⟧ = ⟦ A ⟧ → Mg g ⟦ B ⟧ -- ★ the exponential, the Spec's `⟦ A ⟧ → M π ⟦ B ⟧`
⟦ Nu F ⟧     = Nuᵐ F               -- ★ the Spec's `νM act F`
⟦ μt F ⟧     = Mu F
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
coh (F ⊕f G) X (inj₁ x) = inj₁ (coh F X x)
coh (F ⊕f G) X (inj₂ y) = inj₂ (coh G X y)
coh (F ⊗f G) X (x , y)  = (coh F X x , coh G X y)

coh⁻¹ : ∀ F X → FS F ⟦ X ⟧ → ⟦ LF∙ F X ⟧
coh⁻¹ Idf      X x        = x
coh⁻¹ Kone     X x        = x
coh⁻¹ Kzero    X ()
coh⁻¹ (Kb b)   X x        = x
coh⁻¹ (Kμ G)   X x        = x
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

-- ★ B1.2: a Spec base type (`Spec.Type.Base`, closed) is a flat type, and its
-- master value (`Val.⟦_⟧`) is the flat value, by recursion on the evidence
flat : ∀ {A : Type} → ST.Base ∅ₖ A → FTy Base
flat (ST.b-var {i = ()} _)
flat b-Unit    = funit
flat b-Void    = fvoid
flat b-Int     = fw int
flat b-Float   = fw float
flat (b-* a b) = flat a f* flat b
flat (b-+ a b) = flat a f+ flat b

toV : ∀ {A : Type} (b : ST.Base ∅ₖ A) → ⟦ flat b ⟧f → Val.⟦ A ⟧
toV (ST.b-var {i = ()} _)
toV b-Unit    x        = x
toV b-Void    ()
toV b-Int     x        = x
toV b-Float   x        = x
toV (b-* a b) (x , y)  = (toV a x , toV b y)
toV (b-+ a b) (inj₁ x) = inj₁ (toV a x)
toV (b-+ a b) (inj₂ y) = inj₂ (toV b y)

fromV : ∀ {A : Type} (b : ST.Base ∅ₖ A) → Val.⟦ A ⟧ → ⟦ flat b ⟧f
fromV (ST.b-var {i = ()} _)
fromV b-Unit    x        = x
fromV b-Void    ()
fromV b-Int     x        = x
fromV b-Float   x        = x
fromV (b-* a b) (x , y)  = (fromV a x , fromV b y)
fromV (b-+ a b) (inj₁ x) = inj₁ (fromV a x)
fromV (b-+ a b) (inj₂ y) = inj₂ (fromV b y)

-- ★ B1.2: a SigOp is master's (`SigOpInfo`): its argument and answer are base
-- types (`baseA`, `conB`)
record Sig : Set where
  constructor sig
  field
    {sA sB} : Type
    info    : SigOpInfo sA sB
open Sig

sdom scod : Sig → FTy Base
sdom s = flat (SigOpInfo.baseA (info s))
scod s = flat (SigOpInfo.conB (info s))

------------------------------------------------------------------------
-- 5. THE LINEAR CORE.
--
-- `dup`/`drop` are the only sources of duplication and discard. `lIn` and
-- `lOutμ` are the Lambek isomorphism: one wrapping, one unwrapping, no recursion.
------------------------------------------------------------------------

infixr 9 _∘l_
infixr 7 _⊗l_

-- ★ D422: THE LABELS. A label's signature: its kind, environment, domain and
-- codomain (`Kd`, `Gr`: §2). A ONE-SHOT body owns its environment; a MANY-USE
-- one (D131) reads it lent, so it can be applied while lent, at every layer of
-- a fold.
record Sg : Set where
  constructor sg
  field kd : Kd
        gr : Gr
        env dom cod : LTy
open Sg

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
-- ★ D422: `Γ`, the labels in scope, is a parameter: a body is not a term's
-- part but a table entry (`Defs`), so every generator is at the same `Γ`.
data Tm (Γ : Cx) : LTy → LTy → LTy → Set
data Blk {Γ : Cx} : ∀ {E A B} → Tm Γ E A B → Set
-- a body at its arrow's grade: an arrow of grade `act` has a finite block
Gd : ∀ {Γ E A B} → Gr → Tm Γ E A B → Set

data Tm Γ where
  lid    : ∀ {A E} → Tm Γ E A A
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
  -- ★ D422, closed structure, defunctionalised: a closure of label `l` is its
  -- environment, tagged (no event); applying it calls `l`'s body directly.
  -- A one-shot closure is applied owned, a many-use one (D131) lent.
  -- ★ D423: `lclo F` tags every environment at the `Idf` positions of a layer
  -- (`lclo Idf` tags one): what observing a ν does to the seeds its
  -- coalgebra returns. The final coalgebra is `lobs` below, no generator.
  lclo    : ∀ F {l k g X A B E} → Γ ∋[ l ] sg k g X A B → Tm Γ E (LF∙ F X) (LF∙ F (Ct l X))
  lapp    : ∀ {l g X A B E} → Γ ∋[ l ] sg once g X A B → Tm Γ E (Ct l X ⊗t A) B
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
  bapp    : ∀ {l g X A B} → Γ ∋[ l ] sg many g X A B → Tm Γ (Ct l X) A B
  -- ★ D426 part 3: THE EXPONENTIAL (the Spec's `⊢lam`/`⊢app`). The body is a
  -- SUBTERM, over the same labels, so no table and no stratification is
  -- needed and the meaning stays structural. A one-shot closure owns its
  -- environment `X` (its body closed over `One`: a borrow never escapes into
  -- it); a many-use one reads `X` lent (D131), so it is applied while lent.
  llam    : ∀ {g X A B E} (b : Tm Γ One (X ⊗t A) B) → Gd g b → Tm Γ E X (Fn once g A B)
  llamω   : ∀ {g X A B E} (b : Tm Γ X A B) → Gd g b → Tm Γ E X (Fn many g A B)
  lev     : ∀ {g A B E} → Tm Γ E (Fn once g A B ⊗t A) B
  bev     : ∀ {g A B} → Tm Γ (Fn many g A B) A B
  -- ★ THE FINAL COALGEBRA (the Spec's `⊢unfold`/`⊢out`): a ν from a many-use
  -- coalgebra of grade `act` (a value: data may decide it) and a seed; and
  -- one observation, a finite block
  lunf    : ∀ {F S E} → Tm Γ E (Fn many act S (LF∙ F S) ⊗t S) (Nu F)
  lout    : ∀ {F E} → Tm Γ E (Nu F) (LF∙ F (Nu F))
  -- ★ A15: a constant of a base type (the IR's `const`): a word, no event
  lconst  : ∀ {b E} → Lit b → Tm Γ E One (Bt b)
  -- ★ A11, B1.2: the SigOps, anywhere a term can be. `lop s` runs the op's
  -- contract block (`opB`): no event (pure), an event and the world's answer
  -- (emits, answers), or the run ends (halts: the Spec's halt by the op's
  -- contract, so the core has no `lhalt` of its own)
  lop     : (s : Sig) → ∀ {E} → Tm Γ E ⌜ sdom s ⌝ ⌜ scod s ⌝
  -- ★ A11: the loop (D317): the round reads `E` and the state, and ends with
  -- the result (`inl`) or the next state (`inr`). ★ The Spec's `⊢iter`: the
  -- round is a FINITE BLOCK (`Blk`, the Spec's grade `act`), so a round never
  -- contains a loop (structured recursion; GOAL.md: "every round of a server
  -- is computed in finite time").
  liter   : ∀ {A B E} (f : Tm Γ E A (B ⊕t A)) → Blk f → Tm Γ E A B

-- ★ THE GRADE JUDGMENT (the Spec's `⊢ t ∷ A ! act`, Curry-style over the
-- intrinsically typed terms): `t` is a finite block. Every generator but the
-- loop is one when its parts are; applying a closure is one when its label's
-- grade is `act`; building a closure is a value, whatever its body does.
data Blk {Γ} where
  k-id     : ∀ {A E} → Blk (lid {A = A} {E})
  k-∘      : ∀ {A B C E} {f : Tm Γ E B C} {g : Tm Γ E A B} → Blk f → Blk g → Blk (f ∘l g)
  k-⊗      : ∀ {A B C D E} {f : Tm Γ E A B} {g : Tm Γ E C D} → Blk f → Blk g → Blk (f ⊗l g)
  k-ρ      : ∀ {A E} → Blk (ρl {A = A} {E})
  k-ρ⁻     : ∀ {A E} → Blk (ρl⁻ {A = A} {E})
  k-lul    : ∀ {A E} → Blk (lul {A = A} {E})
  k-lul⁻   : ∀ {A E} → Blk (lul⁻ {A = A} {E})
  k-assoc  : ∀ {A B C E} → Blk (lassoc {A = A} {B} {C} {E})
  k-assoc⁻ : ∀ {A B C E} → Blk (lassoc⁻ {A = A} {B} {C} {E})
  k-swap   : ∀ {A B E} → Blk (lswap {A = A} {B} {E})
  k-dup    : ∀ {A E} → Blk (dup {A = A} {E})
  k-drop   : ∀ {A E} → Blk (drop {A = A} {E})
  k-inl    : ∀ {A B E} → Blk (linl {A = A} {B} {E})
  k-inr    : ∀ {A B E} → Blk (linr {A = A} {B} {E})
  k-case   : ∀ {A B C E} {f : Tm Γ E A C} {g : Tm Γ E B C} → Blk f → Blk g → Blk (lcase f g)
  k-zero   : ∀ {A E} → Blk (lzero {A = A} {E})
  k-in     : ∀ {F E} → Blk (lIn {F = F} {E})
  k-out    : ∀ {F E} → Blk (lOutμ {F = F} {E})
  k-cata   : ∀ {F A E} {alg : Tm Γ E (LF∙ F A) A} → Blk alg → Blk (lcata F alg)
  k-clo    : ∀ {F l k g X A B E} {p : Γ ∋[ l ] sg k g X A B} → Blk (lclo F {E = E} p)
  k-app    : ∀ {l X A B E} {p : Γ ∋[ l ] sg once act X A B} → Blk (lapp {E = E} p)
  k-lend   : ∀ {E X A B} {b : Tm Γ (E ⊗t X) A B} → Blk b → Blk (lend b)
  k-lift   : ∀ {A B E} {f : Tm Γ One A B} → Blk f → Blk (blift {E = E} f)
  k-fst    : ∀ {E₁ E₂ A B} {f : Tm Γ E₁ A B} → Blk f → Blk (bfst {E₂ = E₂} f)
  k-snd    : ∀ {E₁ E₂ A B} {f : Tm Γ E₂ A B} → Blk f → Blk (bsnd {E₁ = E₁} f)
  k-caseE  : ∀ {E₁ E₂ A B} {f : Tm Γ E₁ A B} {g : Tm Γ E₂ A B} → Blk f → Blk g → Blk (bcaseE f g)
  k-bout   : ∀ {F A B} {f : Tm Γ (LF∙ F (μt F)) A B} → Blk f → Blk (bout f)
  k-copy   : ∀ {E} → Blk (bcopy {E = E})
  k-bapp   : ∀ {l X A B} {p : Γ ∋[ l ] sg many act X A B} → Blk (bapp p)
  k-lam    : ∀ {g X A B E} {b : Tm Γ One (X ⊗t A) B} {γ : Gd g b} → Blk (llam {E = E} b γ)
  k-lamω   : ∀ {g X A B E} {b : Tm Γ X A B} {γ : Gd g b} → Blk (llamω {E = E} b γ)
  k-ev     : ∀ {A B E} → Blk (lev {g = act} {A} {B} {E})
  k-bev    : ∀ {A B} → Blk (bev {g = act} {A} {B})
  k-unf    : ∀ {F S E} → Blk (lunf {F = F} {S} {E})
  k-nout   : ∀ {F E} → Blk (lout {F = F} {E})
  k-const  : ∀ {b E} {v : Lit b} → Blk (lconst {E = E} v)
  k-op     : ∀ {s E} → Blk (lop s {E})

-- a term with nothing lent
LTm : Cx → LTy → LTy → Set
LTm Γ = Tm Γ One

-- ★ OBSERVING A ν, in the core's own generators (what `lout` runs, on the ν's
-- coalgebra and seed): the coalgebra, lent, on the seed; a copy of it beside
-- each seed of the layer, the original dropped; each pair a ν again. Linear:
-- one copy per recursive position (a stream: one), none for a leaf.
Coalg : LF → LTy → LTy
Coalg F S = Fn many act S (LF∙ F S)

-- a copy of the lent coalgebra beside each seed of a layer
strL : ∀ {Γ} F G S → Tm Γ (One ⊗t Coalg F S) (LF∙ G S) (LF∙ G (Coalg F S ⊗t S))
strL F Idf      S = (bsnd bcopy ⊗l lid) ∘l lul⁻
strL F Kone     S = lid
strL F Kzero    S = lid
strL F (Kb b)   S = lid
strL F (Kμ G)   S = lid
strL F (G ⊕f H) S = lcase (linl ∘l strL F G S) (linr ∘l strL F H S)
strL F (G ⊗f H) S = strL F G S ⊗l strL F H S

-- each pair of a layer a ν
mapNu : ∀ {Γ} F G S → LTm Γ (LF∙ G (Coalg F S ⊗t S)) (LF∙ G (Nu F))
mapNu F Idf      S = lunf
mapNu F Kone     S = lid
mapNu F Kzero    S = lid
mapNu F (Kb b)   S = lid
mapNu F (Kμ G)   S = lid
mapNu F (G ⊕f H) S = lcase (linl ∘l mapNu F G S) (linr ∘l mapNu F H S)
mapNu F (G ⊗f H) S = mapNu F G S ⊗l mapNu F H S

obsT : ∀ {Γ} F S → LTm Γ (Coalg F S ⊗t S) (LF∙ F (Nu F))
obsT F S = mapNu F F S ∘l lul ∘l (drop ⊗l lid) ∘l lend (strL F F S) ∘l lend (bsnd bev)

-- a coalgebra's meaning, on the functor's values
cohc : ∀ F S → ⟦ Coalg F S ⟧ → ⟦ S ⟧ → T (FS F ⟦ S ⟧)
cohc F S c s = fmapT (coh F S) (c s)

-- ★ D423: THE FINAL COALGEBRA, DEFUNCTIONALISED. A coalgebra of `F` on seeds
-- `S` is a one-shot label of argument `One`, whose body (over the labels
-- before it, as every body) returns a layer of seeds. A ν of it is a closure
-- `Ct l S`: its seed, tagged — so `ana` is `lclo Idf`, no cell. Observing it
-- calls the coalgebra on the seed and tags the seeds of the layer it returns
-- with the same label: no cell, no event beyond what the body does. A ν
-- built from a layer (the IR's `in-ν`) is another label, whose body returns
-- that layer (A15).
-- ★ The Spec's `⊢unfold`: a coalgebra is a finite block (grade `act`), so a
-- ν's layer is computed in finite time.
lana : ∀ {Γ l S C E} → Γ ∋[ l ] sg once act S One C → Tm Γ E S (Ct l S)
lana p = lclo Idf p

lobs : ∀ F {Γ l S E} → Γ ∋[ l ] sg once act S One (LF∙ F S) → Tm Γ E (Ct l S) (LF∙ F (Ct l S))
lobs F p = lclo F p ∘l lapp p ∘l ρl⁻

-- observing a ν is a finite block
k-obs : ∀ F {Γ l S E} {p : Γ ∋[ l ] sg once act S One (LF∙ F S)} → Blk (lobs F {E = E} p)
k-obs F = k-∘ k-clo (k-∘ k-app k-ρ⁻)

Gd act t = Blk t
Gd eff t = ⊤

-- ★ D422: a label's body, by its kind: a one-shot body owns its environment,
-- a many-use body reads it lent; at its label's grade
data Body (Γ : Cx) : Sg → Set where
  b1 : ∀ {g X A B} (b : LTm Γ (X ⊗t A) B) → Gd g b → Body Γ (sg once g X A B)
  bω : ∀ {g X A B} (b : Tm Γ X A B) → Gd g b → Body Γ (sg many g X A B)

-- ★ D422: the program's table, each body over the labels before it
data Defs : Cx → Set where
  ε   : Defs ε
  _▸_ : ∀ {Γ σ} → Defs Γ → Body Γ σ → Defs (Γ ▸ σ)

-- what label `l` runs: its body, over its own prefix of the table
data Look : ∀ {Γ Δ l σ} → Defs Γ → Γ ∋[ l ] σ → Defs Δ → Body Δ σ → Set where
  lk-here  : ∀ {Γ σ} {ds : Defs Γ} {b : Body Γ σ} → Look (ds ▸ b) here ds b
  lk-there : ∀ {Γ Δ l σ τ} {ds : Defs Γ} {p : Γ ∋[ l ] σ} {ds′ : Defs Δ} {b} {c : Body Γ τ}
           → Look ds p ds′ b → Look (ds ▸ c) (there p) ds′ b



-- the meaning of the labels in scope
data Env : Cx → Set where
  ε   : Env ε
  _▸_ : ∀ {Γ σ} → Env Γ → (⟦ env σ ⟧ → ⟦ dom σ ⟧ → Mg (gr σ) ⟦ cod σ ⟧) → Env (Γ ▸ σ)

lookup : ∀ {Γ l σ} → Env Γ → Γ ∋[ l ] σ → ⟦ env σ ⟧ → ⟦ dom σ ⟧ → Mg (gr σ) ⟦ cod σ ⟧
lookup (ρ ▸ f) here      = f
lookup (ρ ▸ f) (there p) = lookup ρ p
