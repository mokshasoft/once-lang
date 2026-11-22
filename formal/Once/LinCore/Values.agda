-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Values — plan 0.146 A12/A13: the core's MACHINE VALUES and
-- their EVENTS, at the target's numerics and the words a base value takes:
-- the layout a type decides (`words`), a value as it sits in memory (`MV`),
-- what a run does to memory (`Ev`, `copy`, `freeAll`, `tag`) and the ledger of
-- the lowering's temporaries (`TL`). D457: no Interpretation here; what a value
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
open import Once.LinCore.Flat using (funit; fvoid; fw; _f*_; _f+_; Base; ⟦_⟧b)
open import Once.IR.Semantics.Trace using (CallOp; HaltOp)

------------------------------------------------------------------------
-- 0. ★ A12: THE LAYOUT, decided by the type.
--
-- A flat value takes `words` words, as `Spec.ABI` lays a base value out at the
-- boundary: `One`/`Zero` none, a pair both halves, a sum a tag word and the
-- larger alternative. ★ D422: a closure is laid out as its environment (its
-- type names its code: no code word, no cell); (D423) so is a ν, as its seed.
-- A μ is a pointer to its cell: one word. A μ node's size is its layer's.
------------------------------------------------------------------------

-- ★ D469: a type's words as the machine lays it out (a base value one word)
wsz : LTy → ℕ
wsz One          = 0
wsz Zero         = 0
wsz (A ⊗t B)     = wsz A + wsz B
wsz (A ⊕t B)     = suc (wsz A ⊔ wsz B)
wsz (Bt b)       = 1
wsz (μt F)       = 1
wsz (Fn k g A B) = 1        -- ★ a pointer to the closure's cell
wsz (Nu F)       = 1        -- ★ a pointer to the ν's cell
wsz (Ct l X)     = wsz X

-- a cell's header: word 0 its own address (no code reads it: a trampoline reads the
-- contents at `hdr` from the cell's pointer), then code, copy, free
hdr : ℕ
hdr = 4

-- ★ D469: a cell's size is its block's, as the image allocates it
szμ : LF → ℕ                -- a μ node of `F`: its layer, at least a word
szμ F = 1 ⊔ wsz (LF∙ F (μt F))

-- ★ D426 part 3: a closure of an arrow type, its environment `X`: the header
-- and the environment. The arrow's type does not fix which lambda (data
-- decides it, GOAL.md's case for a tag), nor so the environment's size.
szc : LTy → ℕ
szc X = hdr + wsz X

-- ★ a ν: its coalgebra (a pointer to a closure) and its seed. The seed's type
-- is not the ν's, so neither is its size: a cell
szν : LF → LTy → ℕ
szν F S = hdr + wsz (Coalg F S ⊗t S)

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
≟ᵢ-k : ∀ {k k′ n} → Dec (k ≡ k′) → Dec (_≡_ {A = Id} (k , n) (k′ , n))
≟ᵢ-k (yes refl) = yes refl
≟ᵢ-k (no ne)    = no (λ e → ne (cong fst e))

≟ᵢ-n : ∀ k k′ {n n′} → Dec (n ≡ n′) → Dec (_≡_ {A = Id} (k , n) (k′ , n′))
≟ᵢ-n k k′ (no ne)    = no (λ e → ne (cong snd e))
≟ᵢ-n k k′ (yes refl) = ≟ᵢ-k (k ≟ k′)

_≟ᵢ_ : (i j : Id) → Dec (i ≡ j)
(k , n) ≟ᵢ (k′ , n′) = ≟ᵢ-n k k′ (n ≟ n′)

-- ★ D426 part 3: a closure's CODE: its lambda's body, over the table it was
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
  -- ★ D422: a closure is its environment, where it is (its label is its type);
  -- D423: a ν is its seed
  mct   : ∀ {l X} → MV X → MV (Ct l X)
  -- ★ D426 part 3: a closure of an arrow type: one cell, its code and its
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

-- ★ A13 (D424): a TEMPORARY block of the lowering (a fold's work stack, …),
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
copy (mpair a b)   n =
  let (a' , n₁ , t₁) = copy a n
      (b' , n₂ , t₂) = copy b n₁
  in (mpair a' b' , n₂ , t₁ ++ t₂)
copy (minl a)      n = let (a' , n₁ , t₁) = copy a n in (minl a' , n₁ , t₁)
copy (minr b)      n = let (b' , n₁ , t₁) = copy b n in (minr b' , n₁ , t₁)
copy (mbase x)     n = (mbase x , n , [])
-- ★ B1.4 (post-order): a cell's contents are copied first, then its own
-- cell is allocated, as `lIn` (and a closure's, a ν's construction) allocates;
-- so a copy routine is "copy what it holds, then build the cell"
copy (mmu {F} i v)     n =
  let (v' , n₁ , t₁) = copy v n in (mmu (szμ F , n₁) v' , suc n₁ , t₁ ++ alloc (szμ F , n₁) ∷ [])
copy (mct x)       n = let (x' , n₁ , t₁) = copy x n in (mct x' , n₁ , t₁)
copy (mfn {X = X} i c x) n =
  let (x' , n₁ , t₁) = copy x n in (mfn (szc X , n₁) c x' , suc n₁ , t₁ ++ alloc (szc X , n₁) ∷ [])
copy (mnu {F} {S} i p) n =
  let (p' , n₁ , t₁) = copy p n in (mnu (szν F S , n₁) p' , suc n₁ , t₁ ++ alloc (szν F S , n₁) ∷ [])

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

-- ★ D422/D423: `lclo F`: each environment at an `Idf` position of the layer
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
-- 2½. ★ A13 (D424): TEMPORARIES. The lowering may allocate heap blocks the
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

δd : ∀ {P : Set} → Dec P → ℕ
δd (yes _) = 1
δd (no _)  = 0

δn : ℕ → ℕ → ℕ
δn k j = δd (k ≟ j)

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

