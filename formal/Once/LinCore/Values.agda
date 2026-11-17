-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Values — plan 0.146 A12/A13: the core's MACHINE VALUES and
-- their EVENTS, at the target's numerics and the words a base value takes:
-- the layout a type decides (`words`), a value as it sits in memory (`MV`),
-- what a run does to memory (`Ev`, `copy`, `freeAll`, `tag`) and the ledger of
-- the lowering's temporaries (`TL`). D454: no Interpretation here; what a value
-- means and how a term runs (`er`, `Run`) are `Events`'.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; z≤n; s≤s; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m∸n≤m; m∸n+n≡m; n≤0⇒n≡0; ≤-antisym; m≤m+n; m≤n+m; <⇒≢)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; foldl)
open import Data.List.Properties using (foldl-++; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Once.LinCore.Free
  using (_≼_; []≼; ∷≼; Weave; w-[]; w-run; w-tmp; Along)
open import Once.LinCore.Free using (cmap-++; cmap-≼; cmap-weave; cmap-nil; foldl-weave; Along-++; Along-≼; Along-weave)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Word using (Carrier)
import Once.IR.Semantics.Value Carrier Carrier as Val
open import Once.LinCore.Flat using (Base; FTy; funit; fvoid; fw; _f*_; _f+_)

module Once.LinCore.Values
  (fmt : TargetNum)
  -- ★ A12: how many words a base value takes (`Spec.ABI`: one on every target)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt

------------------------------------------------------------------------
-- 0. ★ A12: THE LAYOUT, decided by the type.
--
-- A flat value takes `words` words, as `Spec.ABI` lays a base value out at the
-- boundary: `One`/`Zero` none, a pair both halves, a sum a tag word and the
-- larger alternative. ★ D419: a closure is laid out as its environment (its
-- type names its code: no code word, no cell); (D420) so is a ν, as its seed.
-- A μ is a pointer to its cell: one word. A μ node's size is its layer's.
------------------------------------------------------------------------

words : LTy → ℕ
words One       = 0
words Zero      = 0
words (A ⊗t B)  = words A + words B
words (A ⊕t B)  = suc (words A ⊔ words B)
words (Ct l X)  = words X
words (Fn k g A B) = 1      -- ★ a pointer to the closure's cell
words (Nu F)    = 1         -- ★ a pointer to the ν's cell
words (μt F)    = 1
words (Bt b)    = bw b

szμ : LF → ℕ                -- a μ node of `F`
szμ F = words (LF∙ F (μt F))

-- ★ D423 part 3: a closure of an arrow type, its environment `X`: a code word
-- and the environment. The arrow's type does not fix which lambda (data
-- decides it, GOAL.md's case for a tag), nor so the environment's size.
szc : LTy → ℕ
szc X = suc (words X)

-- ★ a ν: its coalgebra (a pointer to a closure) and its seed. The seed's type
-- is not the ν's, so neither is its size: a cell
szν : LF → LTy → ℕ
szν F S = words (Coalg F S ⊗t S)

------------------------------------------------------------------------
-- 1. MACHINE VALUES: a value as it sits in memory.
------------------------------------------------------------------------

-- ★ A12: a block's name is its SIZE and a serial number from the run's
-- counter. A `free` names the block it frees, so it carries the size its
-- `alloc` did: what free lists per size need, by the lifetimes alone.
Id : Set
Id = ℕ × ℕ

serial : Id → ℕ
serial = snd

-- serials first: two different serials are different blocks, whatever the sizes
_≟ᵢ_ : (i j : Id) → Dec (i ≡ j)
(k , n) ≟ᵢ (k′ , n′) with n ≟ n′
... | no ne = no (λ e → ne (cong snd e))
... | yes refl with k ≟ k′
...   | yes refl = yes refl
...   | no ne    = no (λ e → ne (cong fst e))

-- ★ D423 part 3: a closure's CODE: its lambda's body, over the table it was
-- built at, at its arrow's grade (one-shot: it owns its environment;
-- many-use: it reads it lent)
data Lam : Kd → Gr → LTy → LTy → LTy → Set where
  c1 : ∀ {Γ g X A B} → Defs Γ → (b : Tm Γ One (X ⊗t A) B) → Gd g b → Lam once g X A B
  cω : ∀ {Γ g X A B} → Defs Γ → (b : Tm Γ X A B) → Gd g b → Lam many g X A B


data MV : LTy → Set where
  mone  : MV One
  mpair : ∀ {A B} → MV A → MV B → MV (A ⊗t B)
  minl  : ∀ {A B} → MV A → MV (A ⊕t B)
  minr  : ∀ {A B} → MV B → MV (A ⊕t B)
  mbase : ∀ {b} → ⟦ b ⟧b → MV (Bt b)
  -- a μ node: one cell holding its layer
  mmu   : ∀ {F} → Id → MV (LF∙ F (μt F)) → MV (μt F)
  -- ★ D419: a closure is its environment, where it is (its label is its type);
  -- D420: a ν is its seed
  mct   : ∀ {l X} → MV X → MV (Ct l X)
  -- ★ D423 part 3: a closure of an arrow type: one cell, its code and its
  -- environment
  mfn   : ∀ {k g X A B} → Id → Lam k g X A B → MV X → MV (Fn k g A B)
  -- ★ a ν: one cell, holding its coalgebra and its seed
  mnu   : ∀ {F S} → Id → MV (Coalg F S ⊗t S) → MV (Nu F)


-- ★ A12: a flat value (a SigOp's answer) as it sits in memory: no cell
mvF : ∀ a → ⟦ a ⟧f → MV ⌜ a ⌝
mvF funit    x        = mone
mvF fvoid    ()
mvF (fw b)   x        = mbase x
mvF (a f* b) (x , y)  = mpair (mvF a x) (mvF b y)
mvF (a f+ b) (inj₁ x) = minl (mvF a x)
mvF (a f+ b) (inj₂ y) = minr (mvF b y)

------------------------------------------------------------------------
-- 2. EVENTS.
------------------------------------------------------------------------

-- ★ A13 (D421): a TEMPORARY block of the lowering (a fold's work stack, …),
-- of a size: no id, for it is not a value — nothing can point into it
data TEv : Set where
  tnew : ℕ → TEv
  tdel : ℕ → TEv

data Ev : Set where
  alloc : Id → Ev
  free  : Id → Ev
  peek  : Id → Ev     -- a read of a lent cell (A2): legal only while the cell is live
  io    : (o : CallOp) → Val.⟦ CallOp.cdom o ⟧ → Val.⟦ CallOp.ccod o ⟧ → Ev   -- a SigOp call and the world's answer (B1.2: master's)
  stp   : (o : HaltOp) → Val.⟦ HaltOp.hdom o ⟧ → Ev        -- a `Halts` SigOp: the run ends
  tmp   : TEv → Ev                                     -- ★ A13: a temporary born or freed

Trace : Set
Trace = List Ev

-- `dup`: copy every cell, fresh ids from the counter
copy : ∀ {A} → MV A → ℕ → MV A × ℕ × Trace
copy mone          n = (mone , n , [])
copy (mpair a b)   n with copy a n
... | (a' , n₁ , t₁) with copy b n₁
...   | (b' , n₂ , t₂) = (mpair a' b' , n₂ , t₁ ++ t₂)
copy (minl a)      n with copy a n
... | (a' , n₁ , t₁) = (minl a' , n₁ , t₁)
copy (minr b)      n with copy b n
... | (b' , n₁ , t₁) = (minr b' , n₁ , t₁)
copy (mbase x)     n = (mbase x , n , [])
-- ★ B1.4 (post-order): a cell's contents are copied first, then its own
-- cell is allocated, as `lIn` (and a closure's, a ν's construction) allocates;
-- so a copy routine is "copy what it holds, then build the cell"
copy (mmu {F} i v)     n with copy v n
... | (v' , n₁ , t₁) = (mmu (szμ F , n₁) v' , suc n₁ , t₁ ++ alloc (szμ F , n₁) ∷ [])
copy (mct x)       n with copy x n
... | (x' , n₁ , t₁) = (mct x' , n₁ , t₁)
copy (mfn {X = X} i c x) n with copy x n
... | (x' , n₁ , t₁) = (mfn (szc X , n₁) c x' , suc n₁ , t₁ ++ alloc (szc X , n₁) ∷ [])
copy (mnu {F} {S} i p) n with copy p n
... | (p' , n₁ , t₁) = (mnu (szν F S , n₁) p' , suc n₁ , t₁ ++ alloc (szν F S , n₁) ∷ [])

-- `drop`: free every cell
freeAll : ∀ {A} → MV A → Trace
freeAll mone         = []
freeAll (mpair a b)  = freeAll a ++ freeAll b
freeAll (minl a)     = freeAll a
freeAll (minr b)     = freeAll b
freeAll (mbase x)    = []
freeAll (mmu i v)    = free i ∷ freeAll v
freeAll (mct x)      = freeAll x
freeAll (mfn i c x)  = free i ∷ freeAll x
freeAll (mnu i p)    = free i ∷ freeAll p

-- ★ D419/D420: `lclo F`: each environment at an `Idf` position of the layer
-- becomes a closure, where it is (observing a ν tags the seeds its
-- coalgebra returned): no cell, no event, no counter
tag : ∀ {l X} F → MV (LF∙ F X) → MV (LF∙ F (Ct l X))
tag Idf      x            = mct x
tag Kone     x            = x
tag Kzero    ()
tag (Kb b)   x            = x
tag (Kμ G)   x            = x
tag (G ⊕f H) (minl x)     = minl (tag G x)
tag (G ⊕f H) (minr x)     = minr (tag H x)
tag (G ⊗f H) (mpair x x′) = mpair (tag G x) (tag H x′)

------------------------------------------------------------------------
-- 2½. ★ A13 (D421): TEMPORARIES. The lowering may allocate heap blocks the
-- run does not have (a fold's work stack), if the same generator frees them
-- before it finishes (the user, 2026-11-10). They are counted by size: how
-- many of each size are live. A halt or `exhausted` in between is the exit
-- exception: then they need only have been legal.
------------------------------------------------------------------------

-- the live temporaries, by size
TL : Set
TL = ℕ → ℕ

none : TL
none _ = 0

δn : ℕ → ℕ → ℕ
δn k j with k ≟ j
... | yes _ = 1
... | no _  = 0

tstep : Ev → TL → TL
tstep (alloc _)        L   = L
tstep (free _)         L   = L
tstep (peek _)         L   = L
tstep (io _ _ _)       L   = L
tstep (stp _ _)        L   = L
tstep (tmp (tnew k))   L j = L j + δn k j
tstep (tmp (tdel k))   L j = L j ∸ δn k j

-- a trace acts on the ledger, an event at a time
tplay : Trace → TL → TL
tplay t L = foldl (λ M x → tstep x M) L t

-- what an event needs of the ledger: a temporary freed is live
tpre : Ev → TL → Set
tpre (alloc _)      L = ⊤
tpre (free _)       L = ⊤
tpre (peek _)       L = ⊤
tpre (io _ _ _)     L = ⊤
tpre (stp _ _)      L = ⊤
tpre (tmp (tnew k)) L = ⊤
tpre (tmp (tdel k)) L = 1 ≤ L k

-- no temporary is freed that is not live: where the action is defined
TOK : Trace → TL → Set
TOK = Along tpre (λ M x → tstep x M)

-- legal, from none live; balanced: legal, and none live at the end
TLeg TBal : Trace → Set
TLeg t = TOK t none
TBal t = TLeg t × (∀ k → tplay t none k ≡ 0)

-- the temporaries alone, as events (a run's events with temporaries woven
-- in is a `Weave tmp`, `Free`)
tmps : List TEv → Trace
tmps = map tmp

