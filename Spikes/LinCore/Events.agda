-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Events — plan 0.146 A3: what the linear core does to MEMORY.
--
-- `NbEPLinCore.Lᶜ` is a denotation with a cost count: values are Agda values,
-- and nothing is ever freed because nothing is ever allocated. Here a value is
-- laid out the way D402's two heaps lay it out, and a run emits the cell
-- events it causes:
--
--   * FLAT (no cell; a frame slot or registers): `One`, `⊗t`, `⊕t`, base
--     words, and (D405) a closure, which is its environment — (D406) a ν
--     among them, which is its seed.
--   * CELLS (the cell heap, one id each): a μ node.
--
-- `dup` copies every cell of its value (fresh ids); `drop` frees every cell of
-- its value; `lIn` allocates one cell; `lOutμ` frees one. Nothing else touches
-- the heap: moving data is not copying it. ★ A13 (D407): the lowering's own
-- TEMPORARIES (`r-tmp`) are events beside the cells, counted by size, not
-- cells of the run; `Temps` proves them freed and erasable.
--
-- The run is a RELATION (`Run ds`, over the program's label table): applying
-- a closure runs its label's body, which is not structurally smaller. The
-- relation is checked
-- against `Lᶜ` (`sound`: a run computes the denotation), and the memory
-- theorem (`exchange`) is about every run that exists.
--
-- Plan 0.146 A10/A11: ONE run relation, over the one term language. A run reads
-- a lent value `e` (nothing lent is `mone`), its trace holds the cell events
-- and the SigOp calls in order, and it ends in an `Outcome`: it gives a value,
-- or it stopped (a `Halts` SigOp, or the memory ran out). Each theorem is
-- proved once. The world chooses every answer (`r-op`: any `y`), so a run is
-- any run the world allows.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

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
open import LinCore.Free
  using (_≼_; []≼; ∷≼; Weave; w-[]; w-run; w-tmp; Along)
open import LinCore.Free using (cmap-++; cmap-≼; cmap-weave; cmap-nil; foldl-weave; Along-++; Along-≼; Along-weave)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (subst; _≢_)
open import LinCore.Flat using (FTy; funit; fvoid; fw; _f*_; _f+_)

module LinCore.Events
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  -- ★ A12: how many words a base value takes (`Spec.ABI`: one on every target)
  (bw : Base → ℕ)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod

-- ★ D405: every statement is over the program's label table `ds`
variable
  Γ  : Cx
  ds : Defs Γ

------------------------------------------------------------------------
-- 0. ★ A12: THE LAYOUT, decided by the type.
--
-- A flat value takes `words` words, as `Spec.ABI` lays a base value out at the
-- boundary: `One`/`Zero` none, a pair both halves, a sum a tag word and the
-- larger alternative. ★ D405: a closure is laid out as its environment (its
-- type names its code: no code word, no cell); (D406) so is a ν, as its seed.
-- A μ is a pointer to its cell: one word. A μ node's size is its layer's.
------------------------------------------------------------------------

words : LTy → ℕ
words One       = 0
words Zero      = 0
words (A ⊗t B)  = words A + words B
words (A ⊕t B)  = suc (words A ⊔ words B)
words (Ct l X)  = words X
words (μt F)    = 1
words (Bt b)    = bw b

szμ : LF → ℕ                -- a μ node of `F`
szμ F = words (LF∙ F (μt F))

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

data MV : LTy → Set where
  mone  : MV One
  mpair : ∀ {A B} → MV A → MV B → MV (A ⊗t B)
  minl  : ∀ {A B} → MV A → MV (A ⊕t B)
  minr  : ∀ {A B} → MV B → MV (A ⊕t B)
  mbase : ∀ {b} → ⟦ b ⟧b → MV (Bt b)
  -- a μ node: one cell holding its layer
  mmu   : ∀ {F} → Id → MV (LF∙ F (μt F)) → MV (μt F)
  -- ★ D405: a closure is its environment, where it is (its label is its type);
  -- D406: a ν is its seed
  mct   : ∀ {l X} → MV X → MV (Ct l X)

-- what a machine value means
er : ∀ {A} → MV A → ⟦ A ⟧
er mone              = tt
er (mpair a b)       = (er a , er b)
er (minl a)          = inj₁ (er a)
er (minr b)          = inj₂ (er b)
er (mbase x)         = x
er (mmu {F} i v)     = inμ (coh F (μt F) (er v))
er (mct x)           = er x

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

-- ★ A13 (D407): a TEMPORARY block of the lowering (a fold's work stack, …),
-- of a size: no id, for it is not a value — nothing can point into it
data TEv : Set where
  tnew : ℕ → TEv
  tdel : ℕ → TEv

data Ev : Set where
  alloc : Id → Ev
  free  : Id → Ev
  peek  : Id → Ev     -- a read of a lent cell (A2): legal only while the cell is live
  io    : (s : Sig) → ⟦ sdom s ⟧f → ⟦ scod s ⟧f → Ev   -- a SigOp call and the world's answer
  stp   : (s : Sig) → ⟦ sdom s ⟧f → Ev                  -- a `Halts` SigOp: the run ends
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
copy (mmu {F} i v)     n with copy v (suc n)
... | (v' , n₁ , t₁) = (mmu (szμ F , n) v' , n₁ , alloc (szμ F , n) ∷ t₁)
copy (mct x)       n with copy x n
... | (x' , n₁ , t₁) = (mct x' , n₁ , t₁)

-- `drop`: free every cell
freeAll : ∀ {A} → MV A → Trace
freeAll mone         = []
freeAll (mpair a b)  = freeAll a ++ freeAll b
freeAll (minl a)     = freeAll a
freeAll (minr b)     = freeAll b
freeAll (mbase x)    = []
freeAll (mmu i v)    = free i ∷ freeAll v
freeAll (mct x)      = freeAll x

-- ★ D405/D406: `lclo F`: each environment at an `Idf` position of the layer
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
-- 2½. ★ A13 (D407): TEMPORARIES. The lowering may allocate heap blocks the
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

------------------------------------------------------------------------
-- 3. THE RUN.
--
-- `Run ds f e v n o t`: `f`, reading the lent `e`, takes `v` from counter `n` to
-- the outcome `o`; `gives w n′`: the result `w`, the ids `n … n′-1` being the
-- fresh ones it allocated; `t` is the events, in order.
------------------------------------------------------------------------

-- why a run did not give a value
data Why : Set where
  halted    : Why     -- a `Halts` SigOp ended the program
  exhausted : Why     -- the memory ran out (D374)

data Outcome (B : LTy) : Set where
  gives : MV B → ℕ → Outcome B
  stop  : Why → Outcome B

-- ★ A13: what a run claims of its temporaries, by how it ended
TPost : ∀ {B} → Outcome B → Trace → Set
TPost (gives _ _) t = TBal t
TPost (stop _)    t = TLeg t

-- ★ OUTCOMES ARE A MONAD (exceptions: a value, or why it stopped); its bind
-- and map, AS RELATIONS between a first outcome and the whole one, with the
-- events after the first. A stop passes through, with no events.
data Then {B C : LTy} (K : MV B → ℕ → Outcome C → Trace → Set) : Outcome B → Outcome C → Trace → Set where
  go-on   : ∀ {u n o t} → K u n o t → Then K (gives u n) o t
  stopped : ∀ {y} → Then K (stop y) (stop y) []

data Fmap {B C : LTy} (f : MV B → MV C) (R : Outcome B → Trace → Set) : Outcome C → Trace → Set where
  fm-gives : ∀ {u n t} → R (gives u n) t → Fmap f R (gives (f u) n) t
  fm-stop  : ∀ {y t} → R (stop y) t → Fmap f R (stop y) t

data Run {Γ : Cx} (ds : Defs Γ) : ∀ {E A B} → Tm Γ E A B → MV E → MV A → ℕ → Outcome B → Trace → Set

-- after a loop's round: done, or the loop again from the next state
data Next {Γ : Cx} (ds : Defs Γ) {E A B : LTy} (f : Tm Γ E A (B ⊕t A)) (e : MV E)
  : MV (B ⊕t A) → ℕ → Outcome B → Trace → Set

-- folding the recursive positions of a layer (the `Idf` positions run the
-- fold; every other position moves)
data RunMap {Γ : Cx} (ds : Defs Γ) {E A : LTy} (F : LF) (alg : Tm Γ E (LF∙ F A) A) (e : MV E)
  : (G : LF) → MV (LF∙ G (μt F)) → ℕ → Outcome (LF∙ G A) → Trace → Set

data Run {Γ} ds where
  r-id    : ∀ {E A} {e : MV E} {v : MV A} {n} → Run ds lid e v n (gives v n) []
  -- ★ sequencing is the outcome monad's bind: `f` runs on what `g` gave
  r-∘     : ∀ {E A B C} {f : Tm Γ E B C} {g : Tm Γ E A B} {e v o₁ o n t₁ t₂}
          → Run ds g e v n o₁ t₁ → Then (Run ds f e) o₁ o t₂ → Run ds (f ∘l g) e v n o (t₁ ++ t₂)
  -- in parallel: `f` on the left, then `g` on the right, paired with it
  r-⊗     : ∀ {E A B C D} {f : Tm Γ E A B} {g : Tm Γ E C D} {e a c o₁ o n t₁ t₂}
          → Run ds f e a n o₁ t₁ → Then (λ a′ n₁ → Fmap (mpair a′) (Run ds g e c n₁)) o₁ o t₂
          → Run ds (f ⊗l g) e (mpair a c) n o (t₁ ++ t₂)
  r-ρ     : ∀ {E A} {e : MV E} {a : MV A} {n} → Run ds ρl e (mpair a mone) n (gives a n) []
  r-ρ⁻    : ∀ {E A} {e : MV E} {a : MV A} {n} → Run ds ρl⁻ e a n (gives (mpair a mone) n) []
  r-λ     : ∀ {E A} {e : MV E} {a : MV A} {n} → Run ds lul e (mpair mone a) n (gives a n) []
  r-λ⁻    : ∀ {E A} {e : MV E} {a : MV A} {n} → Run ds lul⁻ e a n (gives (mpair mone a) n) []
  r-α     : ∀ {E A B C} {e : MV E} {a : MV A} {b : MV B} {c : MV C} {n}
          → Run ds lassoc e (mpair (mpair a b) c) n (gives (mpair a (mpair b c)) n) []
  r-α⁻    : ∀ {E A B C} {e : MV E} {a : MV A} {b : MV B} {c : MV C} {n}
          → Run ds lassoc⁻ e (mpair a (mpair b c)) n (gives (mpair (mpair a b) c) n) []
  r-swap  : ∀ {E A B} {e : MV E} {a : MV A} {b : MV B} {n} → Run ds lswap e (mpair a b) n (gives (mpair b a) n) []
  r-dup   : ∀ {E A} {e : MV E} {v : MV A} {n} → Run ds dup e v n (gives (mpair v (fst (copy v n))) (fst (snd (copy v n)))) (snd (snd (copy v n)))
  r-drop  : ∀ {E A} {e : MV E} {v : MV A} {n} → Run ds drop e v n (gives mone n) (freeAll v)
  r-inl   : ∀ {E A B} {e : MV E} {a : MV A} {n} → Run ds (linl {A = A} {B = B}) e a n (gives (minl a) n) []
  r-inr   : ∀ {E A B} {e : MV E} {b : MV B} {n} → Run ds (linr {A = A} {B = B}) e b n (gives (minr b) n) []
  r-case₁ : ∀ {E A B C} {f : Tm Γ E A C} {g : Tm Γ E B C} {e a o n t}
          → Run ds f e a n o t → Run ds (lcase f g) e (minl a) n o t
  r-case₂ : ∀ {E A B C} {f : Tm Γ E A C} {g : Tm Γ E B C} {e b o n t}
          → Run ds g e b n o t → Run ds (lcase f g) e (minr b) n o t
  r-In    : ∀ {E F} {e : MV E} {v : MV (LF∙ F (μt F))} {n}
          → Run ds (lIn {F = F}) e v n (gives (mmu (szμ F , n) v) (suc n)) (alloc (szμ F , n) ∷ [])
  r-Outμ  : ∀ {E F} {e : MV E} {v : MV (LF∙ F (μt F))} {i n} → Run ds (lOutμ {F = F}) e (mmu i v) n (gives v n) (free i ∷ [])
  -- ★ D405: building a closure is tagging its environment: no event (D406:
  -- likewise the seeds of a layer, which is building a ν, or observing one)
  r-clo   : ∀ {E F l k X A B} {p : Γ ∋[ l ] sg k X A B} {e : MV E} {x : MV (LF∙ F X)} {n}
          → Run ds (lclo F p) e x n (gives (tag F x) n) []
  -- applying one calls its label's body, over the body's own prefix of the
  -- table, with the environment and the argument (the body owns both)
  r-app   : ∀ {E l X A B Δ} {p : Γ ∋[ l ] sg once X A B} {ds′ : Defs Δ} {b : LTm Δ (X ⊗t A) B}
              {e : MV E} {x a o n t}
          → Look ds p ds′ (b1 b) → Run ds′ b mone (mpair x a) n o t
          → Run ds (lapp p) e (mpair (mct x) a) n o t
  -- the fold frees the node, folds its positions, runs the algebra; it reads
  -- `e` at every layer
  r-cata  : ∀ {E F A} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {i v o₁ o n t₁ t₂}
          → RunMap ds F alg e F v n o₁ t₁ → Then (Run ds alg e) o₁ o t₂
          → Run ds (lcata F alg) e (mmu i v) n o (free i ∷ (t₁ ++ t₂))
  -- ★ A8, IN-PLACE REUSE: a fold that rebuilds each node with the same functor
  -- (`lIn ∘l g`) may keep the consumed node's cell for the rebuilt node — no
  -- `free i`, no fresh `alloc`. The other rule (`r-cata`) still applies; the
  -- compiler picks. During the fold, cell `i` is live and referenced by no value.
  r-cata-reuse : ∀ {E F} {g : Tm Γ E (LF∙ F (μt F)) (LF∙ F (μt F))} {e : MV E} {i v o₁ o n t₁ t₂}
          → RunMap ds F (lIn ∘l g) e F v n o₁ t₁ → Then (λ u n₁ → Fmap (mmu i) (Run ds g e u n₁)) o₁ o t₂
          → Run ds (lcata F (lIn ∘l g)) e (mmu i v) n o (t₁ ++ t₂)
  -- A2: the scope lends `x` to the body, beside what was lent already; `x`
  -- comes back as it was
  r-lend  : ∀ {E X A B} {b : Tm Γ (E ⊗t X) A B} {e : MV E} {x : MV X} {a o n t}
          → Fmap (mpair x) (Run ds b (mpair e x) a n) o t → Run ds (lend b) e (mpair x a) n o t
  r-lift  : ∀ {E A B} {f : LTm Γ A B} {e : MV E} {a o n t} → Run ds f mone a n o t → Run ds (blift f) e a n o t
  r-fst   : ∀ {E₁ E₂ A B} {f : Tm Γ E₁ A B} {e₁ : MV E₁} {e₂ : MV E₂} {a o n t}
          → Run ds f e₁ a n o t → Run ds (bfst f) (mpair e₁ e₂) a n o t
  r-snd   : ∀ {E₁ E₂ A B} {f : Tm Γ E₂ A B} {e₁ : MV E₁} {e₂ : MV E₂} {a o n t}
          → Run ds f e₂ a n o t → Run ds (bsnd f) (mpair e₁ e₂) a n o t
  r-caseE₁ : ∀ {E₁ E₂ A B} {f : Tm Γ E₁ A B} {g : Tm Γ E₂ A B} {e : MV E₁} {a o n t}
          → Run ds f e a n o t → Run ds (bcaseE f g) (minl e) a n o t
  r-caseE₂ : ∀ {E₁ E₂ A B} {f : Tm Γ E₁ A B} {g : Tm Γ E₂ A B} {e : MV E₂} {a o n t}
          → Run ds g e a n o t → Run ds (bcaseE f g) (minr e) a n o t
  -- looking inside a lent node reads its cell
  r-out   : ∀ {F A B} {f : Tm Γ (LF∙ F (μt F)) A B} {i v a o n t}
          → Run ds f v a n o t → Run ds (bout {F = F} f) (mmu i v) a n o (peek i ∷ t)
  -- keeping the lent value: a copy
  r-copy  : ∀ {E} {e : MV E} {n}
          → Run ds bcopy e mone n (gives (fst (copy e n)) (fst (snd (copy e n)))) (snd (snd (copy e n)))
  -- applying a lent many-use closure lends its environment on to its body
  r-bapp  : ∀ {l X A B Δ} {p : Γ ∋[ l ] sg many X A B} {ds′ : Defs Δ} {b : Tm Δ X A B} {x a o n t}
          → Look ds p ds′ (bω b) → Run ds′ b x a n o t → Run ds (bapp p) (mct x) a n o t
  -- ★ A11: a SigOp: an event, and whatever the world answers (A12: a flat
  -- value, no cell)
  r-const : ∀ {E b} {v : ⟦ b ⟧b} {e : MV E} {n} → Run ds (lconst v) e mone n (gives (mbase v) n) []
  r-op    : ∀ {E} {s} {e : MV E} {x : MV ⌜ sdom s ⌝} {y n}
          → Run ds (lop s) e x n (gives (mvF (scod s) y) n) (io s (toF (sdom s) (er x)) y ∷ [])
  r-halt  : ∀ {E} {s} {e : MV E} {x : MV ⌜ sdom s ⌝} {n}
          → Run ds (lhalt s) e x n (stop halted) (stp s (toF (sdom s) (er x)) ∷ [])
  -- ★ A11: the loop: a round, then what it says (`Next`)
  r-iter  : ∀ {E A B} {f : Tm Γ E A (B ⊕t A)} {e a o₁ o n t₁ t₂}
          → Run ds f e a n o₁ t₁ → Then (Next ds f e) o₁ o t₂ → Run ds (liter f) e a n o (t₁ ++ t₂)
  -- ★ A11: the memory may run out before any term (D374; a server that never
  -- returns has no finished run to cut), or inside one, after a prefix of its
  -- events (a `dup` that copied part of its value)
  r-exh   : ∀ {E A B} {f : Tm Γ E A B} {e v n} → Run ds f e v n (stop exhausted) []
  r-cut   : ∀ {E A B} {f : Tm Γ E A B} {e v o n t t′}
          → Run ds f e v n o t → t′ ≼ t → Run ds f e v n (stop exhausted) t′
  -- ★ A13 (D407): the lowering of `f` may use temporaries of its own, woven
  -- into its events: all freed before it finishes, if it gives a value
  r-tmp   : ∀ {E A B} {f : Tm Γ E A B} {e v o n t ts t′}
          → Run ds f e v n o t → Weave tmp t ts t′ → TPost o (tmps ts) → Run ds f e v n o t′

data RunMap {Γ} ds {E} {A} F alg e where
  m-id   : ∀ {x o n t} → Run ds (lcata F alg) e x n o t → RunMap ds F alg e Idf x n o t
  m-one  : ∀ {x n} → RunMap ds F alg e Kone x n (gives x n) []
  m-b    : ∀ {b x n} → RunMap ds F alg e (Kb b) x n (gives x n) []
  m-μ    : ∀ {G x n} → RunMap ds F alg e (Kμ G) x n (gives x n) []
  m-inl  : ∀ {G H x o n t} → Fmap minl (RunMap ds F alg e G x n) o t → RunMap ds F alg e (G ⊕f H) (minl x) n o t
  m-inr  : ∀ {G H x o n t} → Fmap minr (RunMap ds F alg e H x n) o t → RunMap ds F alg e (G ⊕f H) (minr x) n o t
  m-pair : ∀ {G H x x′ o₁ o n t₁ t₂}
         → RunMap ds F alg e G x n o₁ t₁ → Then (λ y n₁ → Fmap (mpair y) (RunMap ds F alg e H x′ n₁)) o₁ o t₂
         → RunMap ds F alg e (G ⊗f H) (mpair x x′) n o (t₁ ++ t₂)

data Next {Γ} ds f e where
  done  : ∀ {b n} → Next ds f e (minl b) n (gives b n) []
  again : ∀ {a o n t} → Run ds (liter f) e a n o t → Next ds f e (minr a) n o t

------------------------------------------------------------------------
-- 4. SOUNDNESS: a run is a path through the term's meaning.
--
-- `RB m p r`: following the SigOp answers in `p`, the computation `m` ends in
-- `r`: a value, or stopped. A run that ran out (`b-cut`) has followed a prefix.
------------------------------------------------------------------------

data Io : Set where
  io-call : (s : Sig) → ⟦ sdom s ⟧f → ⟦ scod s ⟧f → Io
  io-halt : (s : Sig) → ⟦ sdom s ⟧f → Io

-- what an event shows the world
ioOf : Ev → List Io
ioOf (alloc _)  = []
ioOf (free _)   = []
ioOf (peek _)   = []
ioOf (io s x y) = io-call s x y ∷ []
ioOf (stp s x)  = io-halt s x ∷ []
ioOf (tmp _)    = []

-- what a trace shows: the homomorphism of free monoids it lifts to
ios : Trace → List Io
ios = concatMap ioOf

ios-++ : ∀ t₁ t₂ → ios (t₁ ++ t₂) ≡ ios t₁ ++ ios t₂
ios-++ = cmap-++ ioOf

ios-≼ : ∀ {t′ t} → t′ ≼ t → ios t′ ≼ ios t
ios-≼ = cmap-≼ ioOf

-- ★ A13: the temporaries show nothing to the world
ios-weave : ∀ {t ts t′} → Weave tmp t ts t′ → ios t′ ≡ ios t
ios-weave = cmap-weave ioOf (λ _ → refl)

-- a CELL event: all that `dup` and `drop` emit
data Mem : Ev → Set where
  m-alloc : ∀ {i} → Mem (alloc i)
  m-free  : ∀ {i} → Mem (free i)

mem-io : ∀ {x} → Mem x → ioOf x ≡ []
mem-io m-alloc = refl
mem-io m-free  = refl

copy-mem : ∀ {A} (v : MV A) n → All Mem (snd (snd (copy v n)))
copy-mem mone n = []
copy-mem (mpair a b) n with copy a n | copy-mem a n
... | (a' , n₁ , t₁) | ma with copy b n₁ | copy-mem b n₁
...   | (b' , n₂ , t₂) | mb = ++⁺ ma mb
copy-mem (minl a) n with copy a n | copy-mem a n
... | (a' , n₁ , t₁) | ma = ma
copy-mem (minr b) n with copy b n | copy-mem b n
... | (b' , n₁ , t₁) | mb = mb
copy-mem (mbase x) n = []
copy-mem (mmu i v) n with copy v (suc n) | copy-mem v (suc n)
... | (v' , n₁ , t₁) | mv = m-alloc ∷ mv
copy-mem (mct x) n with copy x n | copy-mem x n
... | (x' , n₁ , t₁) | mx = mx

freeAll-mem : ∀ {A} (v : MV A) → All Mem (freeAll v)
freeAll-mem mone        = []
freeAll-mem (mpair a b) = ++⁺ (freeAll-mem a) (freeAll-mem b)
freeAll-mem (minl a)    = freeAll-mem a
freeAll-mem (minr b)    = freeAll-mem b
freeAll-mem (mbase x)   = []
freeAll-mem (mmu i v)   = m-free ∷ freeAll-mem v
freeAll-mem (mct x)     = freeAll-mem x

ios-copy : ∀ {A} (v : MV A) n → ios (snd (snd (copy v n))) ≡ []
ios-copy v n = cmap-nil ioOf (All.map mem-io (copy-mem v n))

ios-freeAll : ∀ {A} (v : MV A) → ios (freeAll v) ≡ []
ios-freeAll v = cmap-nil ioOf (All.map mem-io (freeAll-mem v))

data Res (X : Set) : Set where
  returns : X → Res X
  ended   : Why → Res X

data RB {X : Set} : T (X ⊎ T∞ X) → List Io → Res X → Set where
  b-ret  : ∀ {x} → RB (ret (inj₁ x)) [] (returns x)
  b-next : ∀ {m p r} → RB (block m) p r → RB (ret (inj₂ m)) p r
  b-call : ∀ {s x k y p r} → RB (k y) p r → RB (call s x k) (io-call s x y ∷ p) r
  b-halt : ∀ {s x y} → RB (halt s x) (io-halt s x ∷ []) (ended y)
  b-cut  : ∀ {m} → RB m [] (ended exhausted)

bind-ret : ∀ {X Y} {m : T (X ⊎ T∞ X)} {k : X → T∞ Y} {p₁ p₂ x r}
         → RB m p₁ (returns x) → RB (block (k x)) p₂ r → RB (bindBlock m k) (p₁ ++ p₂) r
bind-ret b-ret      q = q
bind-ret (b-next h) q = b-next (bind-ret h q)
bind-ret (b-call h) q = b-call (bind-ret h q)

bind-end : ∀ {X Y} {m : T (X ⊎ T∞ X)} {k : X → T∞ Y} {p y}
         → RB m p (ended y) → RB (bindBlock m k) p (ended y)
bind-end (b-next h) = b-next (bind-end h)
bind-end (b-call h) = b-call (bind-end h)
bind-end b-halt     = b-halt
bind-end b-cut      = b-cut

fmap-ret : ∀ {X Y} {f : X → Y} {m : T (X ⊎ T∞ X)} {p x}
         → RB m p (returns x) → RB (bindBlock m (λ z → return∞ (f z))) p (returns (f x))
fmap-ret b-ret      = b-ret
fmap-ret (b-next h) = b-next (fmap-ret h)
fmap-ret (b-call h) = b-call (fmap-ret h)

iter-done : ∀ {A B : Set} {f : A → T∞ (B ⊎ A)} {m p b}
          → RB m p (returns (inj₁ b)) → RB (iterBlock f m) p (returns b)
iter-done b-ret      = b-ret
iter-done (b-next h) = b-next (iter-done h)
iter-done (b-call h) = b-call (iter-done h)

iter-next : ∀ {A B : Set} {f : A → T∞ (B ⊎ A)} {m p₁ p₂ a r}
          → RB m p₁ (returns (inj₂ a)) → RB (iterBlock f (block (f a))) p₂ r → RB (iterBlock f m) (p₁ ++ p₂) r
iter-next b-ret      q = b-next q
iter-next (b-next h) q = b-next (iter-next h q)
iter-next (b-call h) q = b-call (iter-next h q)

iter-end : ∀ {A B : Set} {f : A → T∞ (B ⊎ A)} {m p y}
         → RB m p (ended y) → RB (iterBlock f m) p (ended y)
iter-end (b-next h) = b-next (iter-end h)
iter-end (b-call h) = b-call (iter-end h)
iter-end b-halt     = b-halt
iter-end b-cut      = b-cut

-- following a prefix of a path is running out on the way
cut-pre : ∀ {X} {m : T (X ⊎ T∞ X)} {p r} → RB m p r → ∀ {p′} → p′ ≼ p → RB m p′ (ended exhausted)
cut-pre b-ret      []≼      = b-cut
cut-pre (b-next h) q        = b-next (cut-pre h q)
cut-pre (b-call h) []≼      = b-cut
cut-pre (b-call h) (∷≼ q)   = b-call (cut-pre h q)
cut-pre b-halt     []≼      = b-cut
cut-pre b-halt     (∷≼ []≼) = b-halt
cut-pre b-cut      []≼      = b-cut


ret-eq : ∀ {X} {x y : X} {p : List Io} → x ≡ y → p ≡ [] → RB (ret (inj₁ y)) p (returns x)
ret-eq refl refl = b-ret

-- a path, followed by no more answers (after a stop, or at the end)
++[] : ∀ {X} {m : T (X ⊎ T∞ X)} {p r} → RB m p r → RB m (p ++ []) r
++[] {m = m} {p} {r} h = subst (λ q → RB m q r) (sym (++-identityʳ p)) h


copy-er : ∀ {A} (v : MV A) n → er (fst (copy v n)) ≡ er v
copy-er mone         n = refl
copy-er (mpair a b)  n with copy a n | copy-er a n
... | (a' , n₁ , t₁) | ea with copy b n₁ | copy-er b n₁
...   | (b' , n₂ , t₂) | eb = cong₂ _,_ ea eb
copy-er (minl a)     n with copy a n | copy-er a n
... | (a' , n₁ , t₁) | ea = cong inj₁ ea
copy-er (minr b)     n with copy b n | copy-er b n
... | (b' , n₁ , t₁) | eb = cong inj₂ eb
copy-er (mbase x)    n = refl
copy-er (mmu {F} i v) n with copy v (suc n) | copy-er v (suc n)
... | (v' , n₁ , t₁) | ev = cong (λ x → inμ (coh F (μt F) x)) ev
copy-er (mct x)      n with copy x n | copy-er x n
... | (x' , n₁ , t₁) | ex = ex

-- a flat answer in memory means the answer
er-mvF : ∀ a (y : ⟦ a ⟧f) → er (mvF a y) ≡ fromF a y
er-mvF funit    y        = refl
er-mvF fvoid    ()
er-mvF (fw b)   y        = refl
er-mvF (a f* b) (x , y)  = cong₂ _,_ (er-mvF a x) (er-mvF b y)
er-mvF (a f+ b) (inj₁ x) = cong inj₁ (er-mvF a x)
er-mvF (a f+ b) (inj₂ y) = cong inj₂ (er-mvF b y)

-- `lOutμ ∘ lIn` round trip at the denotation: `coh⁻¹ ∘ coh` is the identity
coh⁻¹∘coh : ∀ F X (x : ⟦ LF∙ F X ⟧) → coh⁻¹ F X (coh F X x) ≡ x
coh⁻¹∘coh Idf      X x        = refl
coh⁻¹∘coh Kone     X x        = refl
coh⁻¹∘coh Kzero    X ()
coh⁻¹∘coh (Kb b)   X x        = refl
coh⁻¹∘coh (Kμ G)   X x        = refl
coh⁻¹∘coh (F ⊕f G) X (inj₁ x) = cong inj₁ (coh⁻¹∘coh F X x)
coh⁻¹∘coh (F ⊕f G) X (inj₂ y) = cong inj₂ (coh⁻¹∘coh G X y)
coh⁻¹∘coh (F ⊗f G) X (x , y)  = cong₂ _,_ (coh⁻¹∘coh F X x) (coh⁻¹∘coh G X y)

-- ★ D406: tagging the seeds of a layer means retyping them, nothing else
tag-er : ∀ {l X} F (x : MV (LF∙ F X)) → er (tag {l} F x) ≡ coh⁻¹ F (Ct l X) (coh F X (er x))
tag-er Idf      x            = refl
tag-er Kone     x            = refl
tag-er Kzero    ()
tag-er (Kb b)   x            = refl
tag-er (Kμ G)   x            = refl
tag-er (G ⊕f H) (minl x)     = cong inj₁ (tag-er G x)
tag-er (G ⊕f H) (minr x)     = cong inj₂ (tag-er H x)
tag-er (G ⊗f H) (mpair x x′) = cong₂ _,_ (tag-er G x) (tag-er H x′)

-- what an outcome means
erOver : ∀ {B} {Z : Set} → (MV B → Z) → Outcome B → Res Z
erOver f (gives w _) = returns (f w)
erOver f (stop y)    = ended y

erO : ∀ {B} → Outcome B → Res ⟦ B ⟧
erO = erOver er

sound-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t} → RunMap ds F alg e G x n o t
          → RB (block (travC ⟦ ds ⟧D F G (λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)) (coh G (μt F) (er x)))) (ios t)
               (erOver (λ y → coh G A (er y)) o)

sound : ∀ {E A B} {f : Tm Γ E A B} {e v o n t} → Run ds f e v n o t → RB (block (Lᶜ ⟦ ds ⟧D f (er e) (er v))) (ios t) (erO o)
sound r-id = b-ret
sound (r-∘ {t₁ = t₁} {t₂} rg th) rewrite ios-++ t₁ t₂ with th
... | go-on rf = bind-ret (sound rg) (sound rf)
... | stopped  = ++[] (bind-end (sound rg))
sound (r-⊗ {t₁ = t₁} {t₂} rf th) rewrite ios-++ t₁ t₂ with th
... | go-on (fm-gives rg) = bind-ret (sound rf) (fmap-ret (sound rg))
... | go-on (fm-stop rg)  = bind-ret (sound rf) (bind-end (sound rg))
... | stopped             = ++[] (bind-end (sound rf))
sound r-ρ    = b-ret
sound r-ρ⁻   = b-ret
sound r-λ    = b-ret
sound r-λ⁻   = b-ret
sound r-α    = b-ret
sound r-α⁻   = b-ret
sound r-swap = b-ret
sound (r-dup {v = v} {n}) = ret-eq (cong (er v ,_) (copy-er v n)) (ios-copy v n)
sound (r-drop {v = v}) = ret-eq refl (ios-freeAll v)
sound r-inl  = b-ret
sound r-inr  = b-ret
sound (r-case₁ r) = sound r
sound (r-case₂ r) = sound r
sound r-In   = b-ret
sound (r-Outμ {F = F} {v = v}) = ret-eq (sym (coh⁻¹∘coh F (μt F) (er v))) refl
sound (r-clo {F = F} {x = x}) = ret-eq (tag-er F x) refl
sound (r-app {x = x} {a = a} {o = o} {t = t} q r) =
  subst (λ m → RB (block m) (ios t) (erO o)) (sym (lookup-look q (er x) (er a))) (sound r)
sound (r-cata {F = F} {A} {alg} {e} {t₁ = t₁} {t₂} rm th) rewrite ios-++ t₁ t₂ with th
... | go-on {u = u} {o = o} ra =
  bind-ret (sound-map rm)
           (subst (λ z → RB (block (Lᶜ _ alg (er e) z)) (ios t₂) (erO o)) (sym (coh⁻¹∘coh F A (er u))) (sound ra))
... | stopped = ++[] (bind-end (sound-map rm))
sound (r-cata-reuse {F = F} {g} {e} {t₁ = t₁} {t₂} rm th) rewrite ios-++ t₁ t₂ with th
... | go-on {u = u} (fm-gives {u = u′} rg) =
  bind-ret (sound-map rm)
           (subst (λ z → RB (block (Lᶜ _ (lIn ∘l g) (er e) z)) (ios t₂) (returns (inμ (coh F (μt F) (er u′)))))
                  (sym (coh⁻¹∘coh F (μt F) (er u)))
                  (fmap-ret {f = λ x → inμ (coh F (μt F) x)} (sound rg)))
... | go-on {u = u} (fm-stop {y = y} rg) =
  bind-ret (sound-map rm)
           (subst (λ z → RB (block (Lᶜ _ (lIn ∘l g) (er e) z)) (ios t₂) (ended y))
                  (sym (coh⁻¹∘coh F (μt F) (er u)))
                  (bind-end (sound rg)))
... | stopped = ++[] (bind-end (sound-map rm))
sound (r-lend (fm-gives r)) = fmap-ret (sound r)
sound (r-lend (fm-stop r))  = bind-end (sound r)
sound (r-lift r) = sound r
sound (r-fst r) = sound r
sound (r-snd r) = sound r
sound (r-caseE₁ r) = sound r
sound (r-caseE₂ r) = sound r
sound (r-out {F} {f = f} {v = v} {a} {o} {t = t} r) =
  subst (λ z → RB (block (Lᶜ _ f z (er a))) (ios t) (erO o)) (sym (coh⁻¹∘coh F (μt F) (er v))) (sound r)
sound (r-copy {e = e} {n}) = ret-eq (copy-er e n) (ios-copy e n)
sound (r-bapp {x = x} {a = a} {o = o} {t = t} q r) =
  subst (λ m → RB (block m) (ios t) (erO o)) (sym (lookup-look q (er x) (er a))) (sound r)
sound r-const = b-ret
sound (r-op {s = s} {y = y}) = b-call (ret-eq (er-mvF (scod s) y) refl)
sound r-halt = b-halt
sound (r-iter {t₁ = t₁} {t₂} r th) rewrite ios-++ t₁ t₂ with th
... | go-on done       = ++[] (iter-done (sound r))
... | go-on (again rn) = iter-next (sound r) (sound rn)
... | stopped          = ++[] (iter-end (sound r))
sound r-exh = b-cut
sound (r-cut r q) = cut-pre (sound r) (ios-≼ q)
sound {f = f} {e = e} {v = v} {o = o} (r-tmp r w p) =
  subst (λ z → RB (block (Lᶜ _ f (er e) (er v))) z (erO o)) (sym (ios-weave w)) (sound r)

sound-map (m-id r)       = sound r
sound-map m-one          = b-ret
sound-map m-b            = b-ret
sound-map m-μ            = b-ret
sound-map (m-inl (fm-gives r)) = fmap-ret (sound-map r)
sound-map (m-inl (fm-stop r))  = bind-end (sound-map r)
sound-map (m-inr (fm-gives r)) = fmap-ret (sound-map r)
sound-map (m-inr (fm-stop r))  = bind-end (sound-map r)
sound-map (m-pair {t₁ = t₁} {t₂} r th) rewrite ios-++ t₁ t₂ with th
... | go-on (fm-gives r′) = bind-ret (sound-map r) (fmap-ret (sound-map r′))
... | go-on (fm-stop r′)  = bind-ret (sound-map r) (bind-end (sound-map r′))
... | stopped             = ++[] (bind-end (sound-map r))

------------------------------------------------------------------------
-- 4½. ★ A12: SIZES ARE DECIDED BY THE TYPE.
--
-- `Sized v`: every cell of `v` is named with the size its type gives. A run
-- keeps it: from a sized input and lent value, every value it gives is sized.
-- So the machine knows a block's size from the type at the `free`, and it is
-- the size the block was allocated with (the `free` names the same block).
------------------------------------------------------------------------

Sized : ∀ {A} → MV A → Set
Sized mone              = ⊤
Sized (mpair a b)       = Sized a × Sized b
Sized (minl a)          = Sized a
Sized (minr b)          = Sized b
Sized (mbase x)         = ⊤
Sized (mmu {F} i v)     = fst i ≡ szμ F × Sized v
Sized (mct x)           = Sized x

-- a copy is sized, whatever it copied: its cells are fresh, named by the type
copy-sized : ∀ {A} (v : MV A) n → Sized (fst (copy v n))
copy-sized mone n = tt
copy-sized (mpair a b) n with copy a n | copy-sized a n
... | (a' , n₁ , t₁) | sa with copy b n₁ | copy-sized b n₁
...   | (b' , n₂ , t₂) | sb = (sa , sb)
copy-sized (minl a) n with copy a n | copy-sized a n
... | (a' , n₁ , t₁) | sa = sa
copy-sized (minr b) n with copy b n | copy-sized b n
... | (b' , n₁ , t₁) | sb = sb
copy-sized (mbase x) n = tt
copy-sized (mmu i v) n with copy v (suc n) | copy-sized v (suc n)
... | (v' , n₁ , t₁) | s = (refl , s)
copy-sized (mct x) n with copy x n | copy-sized x n
... | (x' , n₁ , t₁) | s = s

mvF-sized : ∀ a (y : ⟦ a ⟧f) → Sized (mvF a y)
mvF-sized funit    y        = tt
mvF-sized fvoid    ()
mvF-sized (fw b)   y        = tt
mvF-sized (a f* b) (x , y)  = (mvF-sized a x , mvF-sized b y)
mvF-sized (a f+ b) (inj₁ x) = mvF-sized a x
mvF-sized (a f+ b) (inj₂ y) = mvF-sized b y

tag-sized : ∀ {l X} F (x : MV (LF∙ F X)) → Sized x → Sized (tag {l} F x)
tag-sized Idf      x            z        = z
tag-sized Kone     x            z        = z
tag-sized Kzero    ()
tag-sized (Kb b)   x            z        = z
tag-sized (Kμ G)   x            z        = z
tag-sized (G ⊕f H) (minl x)     z        = tag-sized G x z
tag-sized (G ⊕f H) (minr x)     z        = tag-sized H x z
tag-sized (G ⊗f H) (mpair x x′) (z , z′) = (tag-sized G x z , tag-sized H x′ z′)

sized-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n y n′ t}
          → RunMap ds F alg e G x n (gives y n′) t → Sized e → Sized x → Sized y

sized : ∀ {E A B} {f : Tm Γ E A B} {e v w n n′ t} → Run ds f e v n (gives w n′) t → Sized e → Sized v → Sized w
sized r-id se sv = sv
sized (r-∘ rg (go-on rf)) se sv = sized rf se (sized rg se sv)
sized (r-⊗ rf (go-on (fm-gives rg))) se (sa , sc) = (sized rf se sa , sized rg se sc)
sized r-ρ se (sa , _) = sa
sized r-ρ⁻ se sa = (sa , tt)
sized r-λ se (_ , sa) = sa
sized r-λ⁻ se sa = (tt , sa)
sized r-α se ((sa , sb) , sc) = (sa , (sb , sc))
sized r-α⁻ se (sa , (sb , sc)) = ((sa , sb) , sc)
sized r-swap se (sa , sb) = (sb , sa)
sized (r-dup {v = v} {n}) se sv = (sv , copy-sized v n)
sized r-drop se sv = tt
sized r-inl se sv = sv
sized r-inr se sv = sv
sized (r-case₁ r) se sv = sized r se sv
sized (r-case₂ r) se sv = sized r se sv
sized r-In se sv = (refl , sv)
sized r-Outμ se (_ , sv) = sv
sized (r-clo {F = F} {x = x}) se sv = tag-sized F x sv
sized (r-app q r) se (sx , sa) = sized r tt (sx , sa)
sized (r-cata rm (go-on ra)) se (_ , sv) = sized ra se (sized-map rm se sv)
sized (r-cata-reuse rm (go-on (fm-gives rg))) se (p , sv) = (p , sized rg se (sized-map rm se sv))
sized (r-lend (fm-gives r)) se (sx , sa) = (sx , sized r (se , sx) sa)
sized (r-lift r) se sv = sized r tt sv
sized (r-fst r) (se₁ , _) sv = sized r se₁ sv
sized (r-snd r) (_ , se₂) sv = sized r se₂ sv
sized (r-caseE₁ r) se sv = sized r se sv
sized (r-caseE₂ r) se sv = sized r se sv
sized (r-out r) (_ , se) sv = sized r se sv
sized (r-copy {e = e} {n}) se sv = copy-sized e n
sized (r-bapp q r) sx sv = sized r sx sv
sized r-const se sv = tt
sized (r-op {s = s} {y = y}) se sv = mvF-sized (scod s) y
sized (r-iter r (go-on done)) se sv = sized r se sv
sized (r-iter r (go-on (again rn))) se sv = sized rn se (sized r se sv)
sized (r-tmp r w p) se sv = sized r se sv

sized-map (m-id r) se sx = sized r se sx
sized-map m-one se sx = sx
sized-map m-b se sx = sx
sized-map m-μ se sx = sx
sized-map (m-inl (fm-gives r)) se sx = sized-map r se sx
sized-map (m-inr (fm-gives r)) se sx = sized-map r se sx
sized-map (m-pair r (go-on (fm-gives r′))) se (sx , sx′) = (sized-map r se sx , sized-map r′ se sx′)

------------------------------------------------------------------------
-- 5. ★ THE MEMORY THEOREM (stage 2).
--
-- A heap counts, per id, the live cells with that id (a sound heap: 0 or 1).
-- `play t h` is the heap after the events `t`; `OK t h` says every event was
-- legal when it happened: an `alloc` of a dead id, a `free` of a live one (no
-- double free, no free of a stranger).
--
-- `exchange`: if the heap holds the input's cells (beside a frame `r`: the
-- cells of whatever else is live, which the run must not touch), every run's
-- events are legal, and afterwards the heap holds the OUTPUT's cells instead
-- of the input's, and nothing else changed. The frame is the separation-logic
-- frame rule; it is what makes `⊗l` compose.
--
-- `noleak`: a run of a whole program (`One → One`) from the empty heap ends
-- with the empty heap: every cell it allocated, it freed, exactly once.
------------------------------------------------------------------------

-- the arithmetic, local and small
private
  cancelˡ : ∀ c {a b} → c + a ≡ c + b → a ≡ b
  cancelˡ zero    e = e
  cancelˡ (suc c) e = cancelˡ c (cong (λ { zero → zero ; (suc x) → x }) e)

  cancelʳ : ∀ c {a b} → a + c ≡ b + c → a ≡ b
  cancelʳ c {a} {b} e = cancelˡ c (trans (comm c a) (trans e (comm b c)))
    where comm : ∀ x y → x + y ≡ y + x
          comm = solve-∀

  ≤-cancelˡ : ∀ c {a b} → c + a ≤ c + b → a ≤ b
  ≤-cancelˡ zero    le       = le
  ≤-cancelˡ (suc c) (s≤s le) = ≤-cancelˡ c le

  ≤-cancelʳ : ∀ c {a b} → a + c ≤ b + c → a ≤ b
  ≤-cancelʳ c {a} {b} le = ≤-cancelˡ c (subst (_≤ c + b) (comm a c) (subst (a + c ≤_) (comm b c) le))
    where comm : ∀ x y → x + y ≡ y + x
          comm = solve-∀

  ≤-+ʳ : ∀ {a b} c → a ≤ b → a + c ≤ b + c
  ≤-+ʳ {a} {b} c le = subst₂′ (comm c a) (comm c b) (≤-+ˡ c le)
    where comm : ∀ x y → x + y ≡ y + x
          comm = solve-∀
          ≤-+ˡ : ∀ {a b} c → a ≤ b → c + a ≤ c + b
          ≤-+ˡ zero    le = le
          ≤-+ˡ (suc c) le = s≤s (≤-+ˡ c le)
          subst₂′ : ∀ {x x′ y y′} → x ≡ x′ → y ≡ y′ → x ≤ y → x′ ≤ y′
          subst₂′ refl refl le = le

  -- `m + k ≤ n` gives `k ≤ n ∸ m`
  sub-le : ∀ m {k n} → m + k ≤ n → k ≤ n ∸ m
  sub-le zero    le = le
  sub-le (suc m) {n = suc n} (s≤s le) = sub-le m le

  +≡0ˡ : ∀ m n → m + n ≡ 0 → m ≡ 0
  +≡0ˡ zero n e = refl
  +≡0ʳ : ∀ m n → m + n ≡ 0 → n ≡ 0
  +≡0ʳ zero n e = e

  ≤0 : ∀ {m} → m ≤ 0 → m ≡ 0
  ≤0 z≤n = refl

δ : Id → Id → ℕ
δ i j with i ≟ᵢ j
... | yes _ = 1
... | no  _ = 0

δ-same : ∀ i → δ i i ≡ 1
δ-same i with i ≟ᵢ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

δ-≢ : ∀ {i j} → i ≢ j → δ i j ≡ 0
δ-≢ {i} {j} ne with i ≟ᵢ j
... | yes p = ⊥-elim (ne p)
... | no _  = refl

δ≤1 : ∀ i j → δ i j ≤ 1
δ≤1 i j with i ≟ᵢ j
... | yes _ = s≤s z≤n
... | no  _ = z≤n

-- a cell allocated at serial `n` is no block with a serial from `suc n` on
δ-fresh : ∀ {k n i} → suc n ≤ serial i → δ (k , n) i ≡ 0
δ-fresh lt = δ-≢ (λ e → <⇒≢ lt (cong snd e))

cnt : ∀ {A} → MV A → Id → ℕ
cnt mone         i = 0
cnt (mpair a b)  i = cnt a i + cnt b i
cnt (minl a)     i = cnt a i
cnt (minr b)     i = cnt b i
cnt (mbase x)    i = 0
cnt (mmu j v)    i = δ j i + cnt v i
cnt (mct x)      i = cnt x i

-- ★ A12: a flat value has no cell
cnt-flat : ∀ a (x : MV ⌜ a ⌝) i → cnt x i ≡ 0
cnt-flat funit    mone        i = refl
cnt-flat fvoid    ()          i
cnt-flat (fw b)   (mbase x)   i = refl
cnt-flat (a f* b) (mpair x y) i = cong₂ _+_ (cnt-flat a x i) (cnt-flat b y i)
cnt-flat (a f+ b) (minl x)    i = cnt-flat a x i
cnt-flat (a f+ b) (minr y)    i = cnt-flat b y i

Heap : Set
Heap = Id → ℕ

step : Ev → Heap → Heap
step (alloc i) h j = h j + δ i j
step (free i)  h j = h j ∸ δ i j
step (peek i)  h j = h j
step (io _ _ _) h j = h j
step (stp _ _)  h j = h j
step (tmp _)    h j = h j     -- ★ A13: a temporary is not a cell of the run

-- a trace acts on the heap, an event at a time
play : Trace → Heap → Heap
play t h = foldl (λ g x → step x g) h t

-- what an event needs of the heap: a cell allocated is free, one freed or
-- read is live
okPre : Ev → Heap → Set
okPre (alloc i)  h = h i ≡ 0
okPre (free i)   h = h i ≡ 1
okPre (peek i)   h = h i ≡ 1
okPre (io _ _ _) h = ⊤
okPre (stp _ _)  h = ⊤
okPre (tmp _)    h = ⊤

-- a legal trace: where the action is defined
OK : Trace → Heap → Set
OK = Along okPre (λ g x → step x g)

-- the laws, from the free monoid's (`Free`)
OK-≼ : ∀ {t′ t h} → t′ ≼ t → OK t h → OK t′ h
OK-≼ = Along-≼

play-++ : ∀ t₁ t₂ h → play (t₁ ++ t₂) h ≡ play t₂ (play t₁ h)
play-++ t₁ t₂ h = foldl-++ (λ g x → step x g) h t₁ t₂

OK-++ : ∀ t₁ t₂ h → OK t₁ h → OK t₂ (play t₁ h) → OK (t₁ ++ t₂) h
OK-++ = Along-++

-- ★ A13: the temporaries do not touch the run's cells
play-weave : ∀ {t ts t′} → Weave tmp t ts t′ → ∀ h → play t′ h ≡ play t h
play-weave = foldl-weave (λ g x → step x g) (λ _ _ → refl)

OK-weave : ∀ {t ts t′} → Weave tmp t ts t′ → ∀ h → OK t h → OK t′ h
OK-weave = Along-weave (λ _ _ → refl) (λ _ _ → tt)

-- legal events keep a heap sound
OK-le1 : ∀ t h → OK t h → (∀ i → h i ≤ 1) → ∀ i → play t h i ≤ 1
OK-le1 []            h ok        le = le
OK-le1 (alloc i ∷ t) h (p , ok) le = OK-le1 t _ ok le′
  where
    le′ : ∀ j → h j + δ i j ≤ 1
    le′ j with i ≟ᵢ j
    ... | yes refl = subst (λ x → x + 1 ≤ 1) (sym p) (s≤s z≤n)
    ... | no  _    = subst (_≤ 1) (sym (+0 (h j))) (le j)
      where +0 : ∀ x → x + 0 ≡ x
            +0 = solve-∀
OK-le1 (free i ∷ t)  h (p , ok) le = OK-le1 t _ ok (λ j → ≤-trans (m∸n≤m (h j) (δ i j)) (le j))
OK-le1 (peek i ∷ t)  h (p , ok) le = OK-le1 t _ ok le
OK-le1 (io _ _ _ ∷ t) h (_ , ok) le = OK-le1 t _ ok le
OK-le1 (stp _ _ ∷ t)  h (_ , ok) le = OK-le1 t _ ok le
OK-le1 (tmp _ ∷ t)    h (_ , ok) le = OK-le1 t _ ok le

record Pre (h : Heap) (n : ℕ) {A} (v : MV A) (r : Heap) : Set where
  field
    le1   : ∀ i → h i ≤ 1
    above : ∀ i → n ≤ serial i → h i ≡ 0
    sub   : ∀ i → cnt v i + r i ≤ h i
open Pre

private
  +0 : ∀ x → x + 0 ≡ x
  +0 = solve-∀
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc = solve-∀
  comm : ∀ a b → a + b ≡ b + a
  comm = solve-∀

  -- two exchanges in a row are one
  chain : ∀ P U H₁ W V H → P + U ≡ H₁ + W → H₁ + V ≡ H + U → P + V ≡ H + W
  chain P U H₁ W V H e₁ e₂ = cancelʳ U (begin′)
    where
      r1 : ∀ P V U → (P + V) + U ≡ (P + U) + V
      r1 = solve-∀
      r2 : ∀ H₁ W V → (H₁ + W) + V ≡ (H₁ + V) + W
      r2 = solve-∀
      r3 : ∀ H U W → (H + U) + W ≡ (H + W) + U
      r3 = solve-∀
      begin′ : (P + V) + U ≡ (H + W) + U
      begin′ = trans (r1 P V U) (trans (cong (_+ V) e₁) (trans (r2 H₁ W V) (trans (cong (_+ W) e₂) (r3 H U W))))

  -- the halves of a pair, exchanged one after the other
  chain⊗ : ∀ P B H₁ B′ A H A′ → P + B ≡ H₁ + B′ → H₁ + A ≡ H + A′ → P + (A + B) ≡ H + (A′ + B′)
  chain⊗ P B H₁ B′ A H A′ e₁ e₂ =
    trans (r1 P A B) (trans (cong (_+ A) e₁) (trans (r2 H₁ B′ A) (trans (cong (_+ B′) e₂) (r3 H A′ B′))))
    where
      r1 : ∀ P A B → P + (A + B) ≡ (P + B) + A
      r1 = solve-∀
      r2 : ∀ H₁ B′ A → (H₁ + B′) + A ≡ (H₁ + A) + B′
      r2 = solve-∀
      r3 : ∀ H A′ B′ → (H + A′) + B′ ≡ H + (A′ + B′)
      r3 = solve-∀

  -- what an exchange leaves of the frame
  post-sub : ∀ P V H W R → P + V ≡ H + W → V + R ≤ H → W + R ≤ P
  post-sub P V H W R e le =
    ≤-cancelʳ V (subst ((W + R) + V ≤_) (trans (comm W H) (sym e)) (subst (_≤ W + H) (r W R V) (≤-+ˡ′ W le)))
    where
      r : ∀ W R V → W + (V + R) ≡ (W + R) + V
      r = solve-∀
      ≤-+ˡ′ : ∀ {a b} c → a ≤ b → c + a ≤ c + b
      ≤-+ˡ′ zero    le = le
      ≤-+ˡ′ (suc c) le = s≤s (≤-+ˡ′ c le)

-- every fresh id comes from the counter
copy-mono : ∀ {A} (v : MV A) n → n ≤ fst (snd (copy v n))
copy-mono mone n = ≤-refl
copy-mono (mpair a b) n with copy a n | copy-mono a n
... | (a' , n₁ , t₁) | m₁ with copy b n₁ | copy-mono b n₁
...   | (b' , n₂ , t₂) | m₂ = ≤-trans m₁ m₂
copy-mono (minl a) n with copy a n | copy-mono a n
... | (a' , n₁ , t₁) | m₁ = m₁
copy-mono (minr b) n with copy b n | copy-mono b n
... | (b' , n₁ , t₁) | m₁ = m₁
copy-mono (mbase x) n = ≤-refl
copy-mono (mmu i v) n with copy v (suc n) | copy-mono v (suc n)
... | (v' , n₁ , t₁) | m₁ = ≤-trans (n≤1+n n) m₁
copy-mono (mct x) n with copy x n | copy-mono x n
... | (x' , n₁ , t₁) | m₁ = m₁

copy-below : ∀ {A} (v : MV A) n i → fst (snd (copy v n)) ≤ serial i → cnt (fst (copy v n)) i ≡ 0
copy-below mone n i le = refl
copy-below (mpair a b) n i le with copy a n | copy-below a n | copy-mono a n
... | (a' , n₁ , t₁) | ba | m₁ with copy b n₁ | copy-below b n₁ | copy-mono b n₁
...   | (b' , n₂ , t₂) | bb | m₂ = cong₂ _+_ (ba i (≤-trans m₂ le)) (bb i le)
copy-below (minl a) n i le with copy a n | copy-below a n
... | (a' , n₁ , t₁) | ba = ba i le
copy-below (minr b) n i le with copy b n | copy-below b n
... | (b' , n₁ , t₁) | bb = bb i le
copy-below (mbase x) n i le = refl
copy-below (mmu j v) n i le with copy v (suc n) | copy-below v (suc n) | copy-mono v (suc n)
... | (v' , n₁ , t₁) | bv | m₁ = cong₂ _+_ (δ-fresh (≤-trans m₁ le)) (bv i le)
copy-below (mct x) n i le with copy x n | copy-below x n
... | (x' , n₁ , t₁) | bx = bx i le

-- one allocated cell, at the counter, onto a heap empty from the counter on
private
  alloc-above : ∀ k n (h : Heap) → (∀ i → n ≤ serial i → h i ≡ 0) → ∀ i → suc n ≤ serial i → step (alloc (k , n)) h i ≡ 0
  alloc-above k n h ab i le = trans (cong (h i +_) (δ-fresh le)) (trans (+0 (h i)) (ab i (≤-trans (n≤1+n n) le)))

  alloc-eq : ∀ j (h : Heap) (V : Heap) (P : Heap) → (∀ i → P i ≡ step (alloc j) h i + V i)
           → ∀ i → P i ≡ h i + (δ j i + V i)
  alloc-eq j h V P e i = trans (e i) (assoc (h i) (δ j i) (V i))

-- `dup`'s copy: legal, and it adds exactly the copy's cells
copy-ok : ∀ {A} (v : MV A) n (h : Heap) → (∀ i → n ≤ serial i → h i ≡ 0)
        → OK (snd (snd (copy v n))) h × (∀ i → play (snd (snd (copy v n))) h i ≡ h i + cnt (fst (copy v n)) i)
copy-ok mone n h ab = (tt , λ i → sym (+0 (h i)))
copy-ok (mpair a b) n h ab with copy a n | copy-ok a n h ab | copy-below a n | copy-mono a n
... | (a' , n₁ , t₁) | (oka , eqa) | ba | m₁ with copy b n₁ | copy-ok b n₁ (play t₁ h) ab₁ | copy-mono b n₁
  where ab₁ : ∀ i → n₁ ≤ serial i → play t₁ h i ≡ 0
        ab₁ i le = trans (eqa i) (cong₂ _+_ (ab i (≤-trans m₁ le)) (ba i le))
...   | (b' , n₂ , t₂) | (okb , eqb) | m₂ =
  ( OK-++ t₁ t₂ h oka okb
  , λ i → trans (cong (λ x → x i) (play-++ t₁ t₂ h)) (trans (eqb i) (trans (cong (_+ cnt b' i) (eqa i)) (assoc (h i) (cnt a' i) (cnt b' i)))))
copy-ok (minl a) n h ab with copy a n | copy-ok a n h ab
... | (a' , n₁ , t₁) | r = r
copy-ok (minr b) n h ab with copy b n | copy-ok b n h ab
... | (b' , n₁ , t₁) | r = r
copy-ok (mbase x) n h ab = (tt , λ i → sym (+0 (h i)))
copy-ok (mmu {F} j v) n h ab with copy v (suc n) | copy-ok v (suc n) (step (alloc (szμ F , n)) h) (alloc-above (szμ F) n h ab)
... | (v' , n₁ , t₁) | (ok , eq) = ((ab (szμ F , n) ≤-refl , ok) , alloc-eq (szμ F , n) h (cnt v') (play t₁ (step (alloc (szμ F , n)) h)) eq)
copy-ok (mct x) n h ab with copy x n | copy-ok x n h ab
... | (x' , n₁ , t₁) | r = r

-- freeing one live cell `j` whose contents count `V`
free-step : ∀ j (V : Heap) (h r : Heap) → (∀ i → h i ≤ 1) → (∀ i → (δ j i + V i) + r i ≤ h i)
          → h j ≡ 1 × (∀ i → step (free j) h i ≤ 1) × (∀ i → V i + r i ≤ step (free j) h i)
            × (∀ i → step (free j) h i + δ j i ≡ h i)
free-step j V h r le sb =
  ( ≤-antisym (le j) (≤-trans one≤ (sb j))
  , (λ i → ≤-trans (m∸n≤m (h i) (δ j i)) (le i))
  , (λ i → sub-le (δ j i) (subst (_≤ h i) (assoc (δ j i) (V i) (r i)) (sb i)))
  , (λ i → m∸n+n≡m (≤-trans (m≤m+n (δ j i) (V i + r i)) (subst (_≤ h i) (assoc (δ j i) (V i) (r i)) (sb i)))) )
  where
    one≤ : 1 ≤ (δ j j + V j) + r j
    one≤ = subst (λ x → 1 ≤ (x + V j) + r j) (sym (δ-same j)) (s≤s z≤n)

-- freeing a cell after freeing what it holds
free-cell : ∀ j (V : Heap) (t : Trace) (h r : Heap) → (∀ i → h i ≤ 1) → (∀ i → (δ j i + V i) + r i ≤ h i)
          → (∀ h′ → (∀ i → h′ i ≤ 1) → (∀ i → V i + r i ≤ h′ i) → OK t h′ × (∀ i → play t h′ i + V i ≡ h′ i))
          → OK (free j ∷ t) h × (∀ i → play (free j ∷ t) h i + (δ j i + V i) ≡ h i)
free-cell j V t h r le sb ih with free-step j V h r le sb
... | (hj , le′ , sb′ , back) with ih (step (free j) h) le′ sb′
...   | (ok , eq) = ((hj , ok) , λ i → trans (r1 (play t (step (free j) h) i) (V i) (δ j i)) (trans (cong (_+ δ j i) (eq i)) (back i)))
  where r1 : ∀ P V D → P + (D + V) ≡ (P + V) + D
        r1 = solve-∀

-- `drop`'s frees: legal, and they remove exactly the value's cells
free-ok : ∀ {A} (v : MV A) (h r : Heap) → (∀ i → h i ≤ 1) → (∀ i → cnt v i + r i ≤ h i)
        → OK (freeAll v) h × (∀ i → play (freeAll v) h i + cnt v i ≡ h i)
free-ok mone h r le sb = (tt , λ i → +0 (h i))
free-ok (mpair a b) h r le sb
  with free-ok a h (λ i → cnt b i + r i) le (λ i → subst (_≤ h i) (assoc (cnt a i) (cnt b i) (r i)) (sb i))
... | (oka , eqa)
  with free-ok b (play (freeAll a) h) r (OK-le1 (freeAll a) h oka le)
         (λ i → ≤-cancelʳ (cnt a i)
                  (subst (λ x → (cnt b i + r i) + cnt a i ≤ x) (sym (eqa i))
                     (subst (_≤ h i) (r2 (cnt a i) (cnt b i) (r i)) (sb i))))
  where r2 : ∀ A B R → (A + B) + R ≡ (B + R) + A
        r2 = solve-∀
...   | (okb , eqb) =
  ( OK-++ (freeAll a) (freeAll b) h oka okb
  , λ i → trans (cong (λ x → x i + (cnt a i + cnt b i)) (play-++ (freeAll a) (freeAll b) h))
            (trans (r3 (play (freeAll b) (play (freeAll a) h) i) (cnt a i) (cnt b i))
              (trans (cong (_+ cnt a i) (eqb i)) (eqa i))) )
  where r3 : ∀ P A B → P + (A + B) ≡ (P + B) + A
        r3 = solve-∀
free-ok (minl a) h r le sb = free-ok a h r le sb
free-ok (minr b) h r le sb = free-ok b h r le sb
free-ok (mbase x) h r le sb = (tt , λ i → +0 (h i))
free-ok (mmu j v) h r le sb = free-cell j (cnt v) (freeAll v) h r le sb (λ h′ le′ sb′ → free-ok v h′ r le′ sb′)
free-ok (mct x) h r le sb = free-ok x h r le sb

-- ★ D405/D406: a tagged layer holds exactly the cells it held
cnt-tag : ∀ {l X} F (x : MV (LF∙ F X)) i → cnt (tag {l} F x) i ≡ cnt x i
cnt-tag Idf      x            i = refl
cnt-tag Kone     x            i = refl
cnt-tag Kzero    ()
cnt-tag (Kb b)   x            i = refl
cnt-tag (Kμ G)   x            i = refl
cnt-tag (G ⊕f H) (minl x)     i = cnt-tag G x i
cnt-tag (G ⊕f H) (minr x)     i = cnt-tag H x i
cnt-tag (G ⊗f H) (mpair x x′) i = cong₂ _+_ (cnt-tag G x i) (cnt-tag H x′ i)

Below : ∀ {A} → MV A → ℕ → Set
Below v n = ∀ i → n ≤ serial i → cnt v i ≡ 0


mono-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n y n′ t} → RunMap ds F alg e G x n (gives y n′) t → n ≤ n′
below-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n y n′ t} → RunMap ds F alg e G x n (gives y n′) t → Below x n → Below y n′

mono : ∀ {E A B} {f : Tm Γ E A B} {e v w n n′ t} → Run ds f e v n (gives w n′) t → n ≤ n′
mono r-id          = ≤-refl
mono (r-∘ rg (go-on rf))   = ≤-trans (mono rg) (mono rf)
mono (r-⊗ rf (go-on (fm-gives rg)))   = ≤-trans (mono rf) (mono rg)
mono r-ρ           = ≤-refl
mono r-ρ⁻          = ≤-refl
mono r-λ           = ≤-refl
mono r-λ⁻          = ≤-refl
mono r-α           = ≤-refl
mono r-α⁻          = ≤-refl
mono r-swap        = ≤-refl
mono (r-dup {v = v} {n}) = copy-mono v n
mono r-drop        = ≤-refl
mono r-inl         = ≤-refl
mono r-inr         = ≤-refl
mono (r-case₁ r)   = mono r
mono (r-case₂ r)   = mono r
mono r-In          = n≤1+n _
mono r-Outμ        = ≤-refl
mono r-clo         = ≤-refl
mono (r-app q r)   = mono r
mono (r-cata rm (go-on ra)) = ≤-trans (mono-map rm) (mono ra)
mono (r-cata-reuse rm (go-on (fm-gives rg))) = ≤-trans (mono-map rm) (mono rg)
mono (r-lend (fm-gives r))    = mono r
mono (r-lift r)    = mono r
mono (r-fst r)     = mono r
mono (r-snd r)     = mono r
mono (r-caseE₁ r)  = mono r
mono (r-caseE₂ r)  = mono r
mono (r-out r)     = mono r
mono (r-copy {e = e} {n}) = copy-mono e n
mono (r-bapp q r)  = mono r
mono r-const       = ≤-refl
mono r-op          = ≤-refl
mono (r-iter r (go-on done))    = mono r
mono (r-iter r (go-on (again rn))) = ≤-trans (mono r) (mono rn)
mono (r-tmp r w p)      = mono r

mono-map (m-id r)      = mono r
mono-map m-one         = ≤-refl
mono-map m-b           = ≤-refl
mono-map m-μ           = ≤-refl
mono-map (m-inl (fm-gives r))     = mono-map r
mono-map (m-inr (fm-gives r))     = mono-map r
mono-map (m-pair r (go-on (fm-gives r′))) = ≤-trans (mono-map r) (mono-map r′)

below : ∀ {E A B} {f : Tm Γ E A B} {e v w n n′ t} → Run ds f e v n (gives w n′) t → Below v n → Below w n′
below r-id b = b
below (r-∘ rg (go-on rf)) b = below rf (below rg b)
below (r-⊗ {a = a} {c = c} rf (go-on (fm-gives rg))) b i le =
  cong₂ _+_ (below rf (λ j l → +≡0ˡ (cnt a j) (cnt c j) (b j l)) i (≤-trans (mono rg) le))
            (below rg (λ j l → +≡0ʳ (cnt a j) (cnt c j) (b j (≤-trans (mono rf) l))) i le)
below (r-ρ {a = a}) b i le = +≡0ˡ (cnt a i) 0 (b i le)
below r-ρ⁻ b i le = trans (+0 _) (b i le)
below r-λ b = b
below r-λ⁻ b = b
below (r-α {a = a} {b = bb} {c = c}) b i le = trans (sym (assoc (cnt a i) (cnt bb i) (cnt c i))) (b i le)
below (r-α⁻ {a = a} {b = bb} {c = c}) b i le = trans (assoc (cnt a i) (cnt bb i) (cnt c i)) (b i le)
below (r-swap {a = a} {b = bb}) b i le = trans (comm (cnt bb i) (cnt a i)) (b i le)
below (r-dup {v = v} {n}) b i le = cong₂ _+_ (b i (≤-trans (copy-mono v n) le)) (copy-below v n i le)
below r-drop b i le = refl
below r-inl b = b
below r-inr b = b
below (r-case₁ r) b = below r b
below (r-case₂ r) b = below r b
below (r-In {n = n}) b i le = cong₂ _+_ (δ-fresh le) (b i (≤-trans (n≤1+n n) le))
below (r-Outμ {v = v} {i = j}) b i le = +≡0ʳ (δ j i) (cnt v i) (b i le)
below (r-clo {F = F} {x = x}) b i le = trans (cnt-tag F x i) (b i le)
below (r-app q r) b = below r b
below (r-cata {i = j} {v} rm (go-on ra)) b = below ra (below-map rm (λ i le → +≡0ʳ (δ j i) (cnt v i) (b i le)))
below (r-cata-reuse {i = j} {v} rm (go-on (fm-gives rg))) b i le =
  cong₂ _+_ (+≡0ˡ (δ j i) (cnt v i) (b i (≤-trans (≤-trans (mono-map rm) (mono rg)) le)))
            (below rg (below-map rm (λ k l → +≡0ʳ (δ j k) (cnt v k) (b k l))) i le)
below (r-lend {x = x} {a} (fm-gives r)) b i le =
  cong₂ _+_ (+≡0ˡ (cnt x i) (cnt a i) (b i (≤-trans (mono r) le)))
            (below r (λ j l → +≡0ʳ (cnt x j) (cnt a j) (b j l)) i le)
below (r-lift r) b = below r b
below (r-fst r) b = below r b
below (r-snd r) b = below r b
below (r-caseE₁ r) b = below r b
below (r-caseE₂ r) b = below r b
below (r-out r) b = below r b
below (r-copy {e = e} {n}) b = copy-below e n
below (r-bapp q r) b = below r b
below r-const b i le = refl
below (r-op {s = s} {y = y}) b i le = cnt-flat (scod s) (mvF (scod s) y) i
below (r-iter r (go-on done)) b = below r b
below (r-iter r (go-on (again rn))) b = below rn (below r b)
below (r-tmp r w p) b = below r b

below-map (m-id r) b = below r b
below-map m-one b = b
below-map m-b b = b
below-map m-μ b = b
below-map (m-inl (fm-gives r)) b = below-map r b
below-map (m-inr (fm-gives r)) b = below-map r b
below-map (m-pair {x = x} {x′} r (go-on (fm-gives r′))) b i le =
  cong₂ _+_ (below-map r (λ j l → +≡0ˡ (cnt x j) (cnt x′ j) (b j l)) i (≤-trans (mono-map r′) le))
            (below-map r′ (λ j l → +≡0ʳ (cnt x j) (cnt x′ j) (b j (≤-trans (mono-map r) l))) i le)

pre-below : ∀ {h n A} {v : MV A} {r} → Pre h n v r → Below v n
pre-below {h} {v = v} {r} pre i le = +≡0ˡ (cnt v i) (r i) (≤0 (subst (cnt v i + r i ≤_) (above pre i le) (sub pre i)))

-- after a run, the same precondition holds of the output, at the new counter
post-gen : ∀ {A B} {v : MV A} {w : MV B} {n n′ t h r} → n ≤ n′ → (Below v n → Below w n′)
         → Pre h n v r → OK t h → (∀ i → play t h i + cnt v i ≡ h i + cnt w i) → Pre (play t h) n′ w r
post-gen {v = v} {w} {n} {n′} {t} {h} {r} mn bl pre ok eq = record
  { le1   = OK-le1 t h ok (le1 pre)
  ; above = λ i le →
      let n≤i = ≤-trans mn le
          e   = eq i
          e′  = trans (sym (+0 (play t h i)))
                  (trans (cong (play t h i +_) (sym (pre-below pre i n≤i)))
                    (trans e (cong₂ _+_ (above pre i n≤i) (bl (pre-below pre) i le))))
      in e′
  ; sub   = λ i → post-sub (play t h i) (cnt v i) (h i) (cnt w i) (r i) (eq i) (sub pre i) }

post : ∀ {E A B} {f : Tm Γ E A B} {e v w n n′ t h r} → Run ds f e v n (gives w n′) t → Pre h n v r → OK t h
     → (∀ i → play t h i + cnt v i ≡ h i + cnt w i) → Pre (play t h) n′ w r
post {t = t} run = post-gen {t = t} (mono run) (below run)

-- A2: a lent value's cells are in the frame (someone else owns them, and the
-- run does not touch the frame), so they stay live, and every `peek` is legal
Lent : ∀ {E} → MV E → Heap → Set
Lent e r = ∀ i → 1 ≤ cnt e i → 1 ≤ r i

-- nothing lent: a run that reads nothing
lent₀ : ∀ {r} → Lent mone r
lent₀ i ()

-- what is lent already, and the value a scope lends beside it: both are in
-- the frame of the scope's body
lent-pair : ∀ {E X} (e : MV E) (x : MV X) {r : Heap} → Lent e r → Lent (mpair e x) (λ i → cnt x i + r i)
lent-pair e x {r} lent i p = split (cnt e i) (lent i) p
  where
    split : ∀ m {k q} → (1 ≤ m → 1 ≤ q) → 1 ≤ m + k → 1 ≤ k + q
    split zero    {k} {q} f l = ≤-trans l (m≤m+n k q)
    split (suc m) {k} {q} f l = ≤-trans (f (s≤s z≤n)) (m≤n+m q k)

peek-live : ∀ {h n A E} {a : MV A} {e : MV E} {r} → Pre h n a r → Lent e r → ∀ i → 1 ≤ cnt e i → h i ≡ 1
peek-live {a = a} {r = r} pre lent i p =
  ≤-antisym (le1 pre i) (≤-trans (≤-trans (lent i p) (m≤n+m (r i) (cnt a i))) (sub pre i))

-- what a run claims of the heap, by how it ended: if it gives a value, the
-- value's cells replace the input's `V`; if it stopped, only legality is
-- claimed (what is live at an exit stays, the user's exception, 2026-11-08)
Post : ∀ {B} → Trace → Heap → Heap → Outcome B → Set
Post t h V (gives w n′) = ∀ i → play t h i + V i ≡ h i + cnt w i
Post t h V (stop _)     = ⊤

-- two steps in a row
seqP : ∀ {B} (o : Outcome B) t₁ t₂ h (V U : Heap)
     → (∀ i → play t₁ h i + V i ≡ h i + U i) → Post t₂ (play t₁ h) U o → Post (t₁ ++ t₂) h V o
seqP (stop _)     t₁ t₂ h V U e₁ e₂ = tt
seqP (gives w n′) t₁ t₂ h V U e₁ e₂ i =
  trans (cong (λ z → z i + V i) (play-++ t₁ t₂ h))
        (chain (play t₂ (play t₁ h) i) (U i) (play t₁ h i) (cnt w i) (V i) (h i) (e₂ i) (e₁ i))

-- a cell freed first
freeP : ∀ {B} (o : Outcome B) j t (h V : Heap)
      → (∀ i → step (free j) h i + δ j i ≡ h i) → Post t (step (free j) h) V o
      → Post (free j ∷ t) h (λ i → δ j i + V i) o
freeP (stop _)     j t h V back p = tt
freeP (gives w n′) j t h V back p i =
  trans (r8 (play t (step (free j) h) i) (δ j i) (V i))
    (trans (cong (_+ δ j i) (p i))
      (trans (r9 (step (free j) h i) (cnt w i) (δ j i)) (cong (_+ cnt w i) (back i))))
  where r8 : ∀ P D V → P + (D + V) ≡ (P + V) + D
        r8 = solve-∀
        r9 : ∀ H W D → (H + W) + D ≡ (H + D) + W
        r9 = solve-∀

-- a cell read first
peekP : ∀ {B} (o : Outcome B) j t (h V : Heap) → Post t h V o → Post (peek j ∷ t) h V o
peekP (stop _)     j t h V p = tt
peekP (gives w n′) j t h V p = p

-- the same input, written differently
postV : ∀ {B} (o : Outcome B) t h {V V′ : Heap} → (∀ i → V i ≡ V′ i) → Post t h V o → Post t h V′ o
postV (stop _)     t h e p   = tt
postV (gives w n′) t h e p i = trans (cong (play t h i +_) (sym (e i))) (p i)

-- ★ A13: the same claim with temporaries woven in
post-weave : ∀ {B} (o : Outcome B) {t ts t′} → Weave tmp t ts t′ → ∀ h V → Post t h V o → Post t′ h V o
post-weave (stop _)     w h V p = tt
post-weave (gives u n′) w h V p = subst (λ z → ∀ i → z i + V i ≡ h i + cnt u i) (sym (play-weave w h)) p

exchange-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t} → RunMap ds F alg e G x n o t
             → ∀ {h r} → Pre h n x r → Lent e r → OK t h × Post t h (cnt x) o

------------------------------------------------------------------------
-- ★ The theorem.
------------------------------------------------------------------------

private
  -- one cell allocated at the counter, holding `V`
  alloc1 : ∀ {h n A} {v : MV A} {r} k (V : Heap) → Pre h n v r
         → OK (alloc (k , n) ∷ []) h × (∀ i → play (alloc (k , n) ∷ []) h i + V i ≡ h i + (δ (k , n) i + V i))
  alloc1 {h} {n} k V pre = ((above pre (k , n) ≤-refl , tt) , λ i → assoc (h i) (δ (k , n) i) (V i))

  -- the precondition after the first event freed cell `j`
  pre-free : ∀ {h n A B} {v : MV A} {v′ : MV B} {r} j → Pre h n v r → (∀ i → step (free j) h i ≤ 1)
           → (∀ i → cnt v′ i + r i ≤ step (free j) h i) → Pre (step (free j) h) n v′ r
  pre-free {h} j pre le′ sb′ = record
    { le1 = le′
    ; above = λ i le → ≤0 (subst (step (free j) h i ≤_) (above pre i le) (m∸n≤m (h i) (δ j i)))
    ; sub = sb′ }

  -- the left half of a pair, its right half in the frame
  pre-l : ∀ {h n A B} {a : MV A} {c : MV B} {r} → Pre h n (mpair a c) r → Pre h n a (λ i → cnt c i + r i)
  pre-l {h} {a = a} {c} {r} pre = record
    { le1 = le1 pre ; above = above pre
    ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt c i) (r i)) (sub pre i) }

  -- then the right half, the left half's result in the frame
  pre-r : ∀ {h n A B} {a′ : MV A} {c : MV B} {r} → Pre h n a′ (λ i → cnt c i + r i) → Pre h n c (λ i → cnt a′ i + r i)
  pre-r {h} {a′ = a′} {c} {r} pre = record
    { le1 = le1 pre ; above = above pre
    ; sub = λ i → subst (_≤ h i) (sw (cnt a′ i) (cnt c i) (r i)) (sub pre i) }
    where sw : ∀ A′ B R → A′ + (B + R) ≡ B + (A′ + R)
          sw = solve-∀

  -- a reused cell in the frame, beside the node's contents
  pre-reuse : ∀ {h n F} {j} {v : MV (LF∙ F (μt F))} {r} → Pre h n (mmu j v) r → Pre h n v (λ i → δ j i + r i)
  pre-reuse {h} {j = j} {v} {r} pre = record
    { le1 = le1 pre ; above = above pre
    ; sub = λ i → subst (_≤ h i) (sw (δ j i) (cnt v i) (r i)) (sub pre i) }
    where sw : ∀ D V R → (D + V) + R ≡ V + (D + R)
          sw = solve-∀

  -- a frame that grows keeps what is lent
  lent-w : ∀ {C r : Heap} (K : Heap) → (∀ i → 1 ≤ C i → 1 ≤ r i) → ∀ i → 1 ≤ C i → 1 ≤ K i + r i
  lent-w {r = r} K lent i p = ≤-trans (lent i p) (m≤n+m (r i) (K i))

exchange : ∀ {E A B} {f : Tm Γ E A B} {e v o n t} → Run ds f e v n o t → ∀ {h r} → Pre h n v r → Lent e r
         → OK t h × Post t h (cnt v) o
exchange r-id pre lent = (tt , λ i → refl)
exchange (r-∘ {v = v} {t₁ = t₁} {t₂} rg (go-on {u = u} {o = o} rf)) {h} pre lent with exchange rg pre lent
... | (okg , eqg) with exchange rf (post rg pre okg eqg) lent
...   | (okf , eqf) = (OK-++ t₁ t₂ h okg okf , seqP o t₁ t₂ h (cnt v) (cnt u) eqg eqf)
exchange (r-∘ {t₁ = t₁} rg stopped) {h} pre lent = (OK-++ t₁ [] h (fst (exchange rg pre lent)) tt , tt)
exchange (r-⊗ {a = a} {c} {t₁ = t₁} {t₂} rf (go-on {u = a′} (fm-gives {u = c′} rg))) {h} {r} pre lent
  with exchange rf (pre-l pre) (lent-w (cnt c) lent)
... | (oka , eqa)
  with exchange rg (pre-r {a′ = a′} {c} {r} (post rf (pre-l pre) oka eqa)) (lent-w (cnt a′) lent)
...   | (okb , eqb) =
  ( OK-++ t₁ t₂ h oka okb
  , λ i → trans (cong (λ x → x i + (cnt a i + cnt c i)) (play-++ t₁ t₂ h))
            (chain⊗ (play t₂ (play t₁ h) i) (cnt c i) (play t₁ h i) (cnt c′ i) (cnt a i) (h i) (cnt a′ i) (eqb i) (eqa i)) )
exchange (r-⊗ {c = c} {t₁ = t₁} rf stopped) {h} pre lent =
  (OK-++ t₁ [] h (fst (exchange rf (pre-l pre) (lent-w (cnt c) lent))) tt , tt)
exchange (r-⊗ {c = c} {t₁ = t₁} {t₂} rf (go-on {u = a′} (fm-stop rg))) {h} {r} pre lent
  with exchange rf (pre-l pre) (lent-w (cnt c) lent)
... | (oka , eqa) =
  ( OK-++ t₁ t₂ h oka (fst (exchange rg (pre-r {a′ = a′} {c} {r} (post rf (pre-l pre) oka eqa)) (lent-w (cnt a′) lent)))
  , tt )
exchange (r-ρ {a = a}) {h} pre lent = (tt , λ i → cong (h i +_) (+0 (cnt a i)))
exchange (r-ρ⁻ {a = a}) {h} pre lent = (tt , λ i → cong (h i +_) (sym (+0 (cnt a i))))
exchange r-λ pre lent = (tt , λ i → refl)
exchange r-λ⁻ pre lent = (tt , λ i → refl)
exchange (r-α {a = a} {b} {c}) {h} pre lent = (tt , λ i → cong (h i +_) (assoc (cnt a i) (cnt b i) (cnt c i)))
exchange (r-α⁻ {a = a} {b} {c}) {h} pre lent = (tt , λ i → cong (h i +_) (sym (assoc (cnt a i) (cnt b i) (cnt c i))))
exchange (r-swap {a = a} {b}) {h} pre lent = (tt , λ i → cong (h i +_) (comm (cnt a i) (cnt b i)))
exchange (r-dup {v = v} {n}) {h} pre lent with copy-ok v n h (above pre)
... | (ok , eq) = (ok , λ i → trans (cong (_+ cnt v i) (eq i)) (r4 (h i) (cnt (fst (copy v n)) i) (cnt v i)))
  where r4 : ∀ H C V → (H + C) + V ≡ H + (V + C)
        r4 = solve-∀
exchange (r-drop {v = v}) {h} {r} pre lent with free-ok v h r (le1 pre) (sub pre)
... | (ok , eq) = (ok , λ i → trans (eq i) (sym (+0 (h i))))
exchange r-inl pre lent = (tt , λ i → refl)
exchange r-inr pre lent = (tt , λ i → refl)
exchange (r-case₁ r) pre lent = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange (r-case₂ r) pre lent = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange (r-In {F = F} {v = v}) pre lent = alloc1 (szμ F) (cnt v) pre
exchange (r-Outμ {v = v} {i = j}) {h} {r} pre lent with free-step j (cnt v) h r (le1 pre) (sub pre)
... | (hj , _ , _ , back) = ((hj , tt) , λ i → trans (r5 (step (free j) h i) (δ j i) (cnt v i)) (cong (_+ cnt v i) (back i)))
  where r5 : ∀ P D V → P + (D + V) ≡ (P + D) + V
        r5 = solve-∀
-- ★ D405: a closure is its environment: building one is no event, and
-- applying one is running its body on the environment and the argument.
-- D406: so is a ν, built (`lana`) or observed (`lobs`): no event of its own
exchange (r-clo {F = F} {x = x}) {h} pre lent = (tt , λ i → cong (h i +_) (sym (cnt-tag F x i)))
exchange (r-app q r) pre lent =
  exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent₀
exchange (r-cata {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} {o = o} ra)) {h} {r} pre lent
  with free-step j (cnt v) h r (le1 pre) (sub pre)
... | (hj , le′ , sb′ , back)
  with exchange-map rm {step (free j) h} {r} (pre-free {v′ = v} j pre le′ sb′) lent
...   | (okm , eqm)
  with exchange ra (post-gen {v = v} {w = u} {t = t₁} {r = r} (mono-map rm) (below-map rm) (pre-free {v′ = v} j pre le′ sb′) okm eqm) lent
...     | (oka , eqa) =
  ( (hj , OK-++ t₁ t₂ (step (free j) h) okm oka)
  , freeP o j (t₁ ++ t₂) h (cnt v) back (seqP o t₁ t₂ (step (free j) h) (cnt v) (cnt u) eqm eqa) )
exchange (r-cata {i = j} {v} {t₁ = t₁} rm stopped) {h} {r} pre lent
  with free-step j (cnt v) h r (le1 pre) (sub pre)
... | (hj , le′ , sb′ , back) =
  ((hj , OK-++ t₁ [] _ (fst (exchange-map rm {step (free j) h} {r} (pre-free {v′ = v} j pre le′ sb′) lent)) tt) , tt)

-- ★ A8: the reused cell sits in the frame while the node is folded and rebuilt
exchange (r-cata-reuse {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} (fm-gives {u = u′} rg))) {h} {r} pre lent
  with exchange-map rm (pre-reuse pre) (lent-w (δ j) lent)
... | (okm , eqm)
  with exchange rg (post-gen {v = v} {w = u} {t = t₁} {r = λ i → δ j i + r i} (mono-map rm) (below-map rm) (pre-reuse pre) okm eqm)
                   (lent-w (δ j) lent)
...   | (okg , eqg) =
  ( OK-++ t₁ t₂ h okm okg
  , λ i → trans (cong (λ z → z i + (δ j i + cnt v i)) (play-++ t₁ t₂ h))
            (trans (r12 (play t₂ (play t₁ h) i) (δ j i) (cnt v i))
              (trans (cong (_+ δ j i) (chain (play t₂ (play t₁ h) i) (cnt u i) (play t₁ h i) (cnt u′ i) (cnt v i) (h i) (eqg i) (eqm i)))
                (r13 (h i) (cnt u′ i) (δ j i)))) )
  where r12 : ∀ P D V → P + (D + V) ≡ (P + V) + D
        r12 = solve-∀
        r13 : ∀ H W D → (H + W) + D ≡ H + (D + W)
        r13 = solve-∀
exchange (r-cata-reuse {i = j} {t₁ = t₁} rm stopped) {h} pre lent =
  (OK-++ t₁ [] h (fst (exchange-map rm (pre-reuse pre) (lent-w (δ j) lent))) tt , tt)
exchange (r-cata-reuse {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} (fm-stop rg))) {h} {r} pre lent
  with exchange-map rm (pre-reuse pre) (lent-w (δ j) lent)
... | (okm , eqm) =
  ( OK-++ t₁ t₂ h okm
      (fst (exchange rg (post-gen {v = v} {w = u} {t = t₁} {r = λ i → δ j i + r i} (mono-map rm) (below-map rm) (pre-reuse pre) okm eqm)
                        (lent-w (δ j) lent)))
  , tt )
-- ★ A2: the body reads `x` from the frame; `x`'s cells are neither freed nor copied
exchange (r-lend {e = e} {x} {a} (fm-gives {u = w} r)) {h} {rf} pre lent
  with exchange r {h} {λ i → cnt x i + rf i}
         record { le1 = le1 pre ; above = above pre
                ; sub = λ i → subst (_≤ h i) (sw (cnt x i) (cnt a i) (rf i)) (sub pre i) }
         (lent-pair e x lent)
  where sw : ∀ E A R → (E + A) + R ≡ A + (E + R)
        sw = solve-∀
... | (ok , eq) = (ok , λ i → trans (r10 _ (cnt x i) (cnt a i)) (trans (cong (_+ cnt x i) (eq i)) (r11 (h i) (cnt w i) (cnt x i))))
  where r10 : ∀ P E A → P + (E + A) ≡ (P + A) + E
        r10 = solve-∀
        r11 : ∀ H W E → (H + W) + E ≡ H + (E + W)
        r11 = solve-∀
exchange (r-lend {e = e} {x} {a} (fm-stop r)) {h} {rf} pre lent =
  ( fst (exchange r {h} {λ i → cnt x i + rf i}
           record { le1 = le1 pre ; above = above pre
                  ; sub = λ i → subst (_≤ h i) (sw (cnt x i) (cnt a i) (rf i)) (sub pre i) }
           (lent-pair e x lent))
  , tt )
  where sw : ∀ E A R → (E + A) + R ≡ A + (E + R)
        sw = solve-∀
exchange (r-lift r) pre lent = exchange r pre lent₀
exchange (r-fst {e₁ = e₁} {e₂} r) pre lent = exchange r pre (λ i p → lent i (≤-trans p (m≤m+n (cnt e₁ i) (cnt e₂ i))))
exchange (r-snd {e₁ = e₁} {e₂} r) pre lent = exchange r pre (λ i p → lent i (≤-trans p (m≤n+m (cnt e₂ i) (cnt e₁ i))))
exchange (r-caseE₁ r) pre lent = exchange r pre lent
exchange (r-caseE₂ r) pre lent = exchange r pre lent
exchange (r-out {i = i} {v} {a} {o} {t = t} r) {h} pre lent with exchange r pre (λ j p → lent j (≤-trans p (m≤n+m (cnt v j) (δ i j))))
... | (ok , eq) = ((peek-live {a = a} {e = mmu i v} pre lent i (subst (λ x → 1 ≤ x + cnt v i) (sym (δ-same i)) (s≤s z≤n)) , ok) , peekP o i t h (cnt a) eq)
exchange (r-copy {e = e} {n}) {h} pre lent with copy-ok e n h (above pre)
... | (ok , eq) = (ok , λ i → trans (+0 _) (eq i))
-- ★ D405: a lent closure is its lent environment, lent on to the body
exchange (r-bapp q r) pre lent = exchange r pre lent
exchange r-const pre lent = (tt , λ i → refl)
exchange (r-op {s = s} {x = x} {y = y}) {h} pre lent =
  ((tt , tt) , λ i → trans (cong (h i +_) (cnt-flat (sdom s) x i)) (sym (cong (h i +_) (cnt-flat (scod s) (mvF (scod s) y) i))))
exchange r-halt pre lent = ((tt , tt) , tt)
exchange (r-iter {a = a} {t₁ = t₁} r (go-on done)) {h} pre lent with exchange r pre lent
... | (ok , eq) = (OK-++ t₁ [] h ok tt , λ i → trans (cong (λ z → z i + cnt a i) (play-++ t₁ [] h)) (eq i))
exchange (r-iter {a = a} {t₁ = t₁} {t₂} r (go-on (again {a = a′} {o = o} rn))) {h} pre lent with exchange r pre lent
... | (ok₁ , eq₁) with exchange rn (post-gen {v = a} {w = a′} {t = t₁} (mono r) (below r) pre ok₁ eq₁) lent
...   | (ok₂ , eq₂) = (OK-++ t₁ t₂ h ok₁ ok₂ , seqP o t₁ t₂ h (cnt a) (cnt a′) eq₁ eq₂)
exchange (r-iter {t₁ = t₁} r stopped) {h} pre lent = (OK-++ t₁ [] h (fst (exchange r pre lent)) tt , tt)
exchange r-exh pre lent = (tt , tt)
exchange (r-cut r q) pre lent = (OK-≼ q (fst (exchange r pre lent)) , tt)
-- ★ A13: temporaries are not the run's cells: the claim is the run's
exchange (r-tmp {v = v} {o = o} r w p) {h} pre lent with exchange r pre lent
... | (ok , po) = (OK-weave w h ok , post-weave o w h (cnt v) po)

exchange-map (m-id r) pre lent = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map m-one pre lent = (tt , λ i → refl)
exchange-map m-b pre lent = (tt , λ i → refl)
exchange-map m-μ pre lent = (tt , λ i → refl)
exchange-map (m-inl (fm-gives r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-inl (fm-stop r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-inr (fm-gives r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-inr (fm-stop r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-pair {x = x} {x′} {t₁ = t₁} {t₂} r (go-on {u = y} (fm-gives {u = y′} r′))) {h} {rf} pre lent
  with exchange-map r (pre-l pre) (lent-w (cnt x′) lent)
... | (ok₁ , eq₁)
  with exchange-map r′ (pre-r {a′ = y} {x′} {rf} (post-gen {v = x} {w = y} {t = t₁} {r = λ i → cnt x′ i + rf i} (mono-map r) (below-map r) (pre-l pre) ok₁ eq₁))
                       (lent-w (cnt y) lent)
...   | (ok₂ , eq₂) =
  ( OK-++ t₁ t₂ h ok₁ ok₂
  , λ i → trans (cong (λ z → z i + (cnt x i + cnt x′ i)) (play-++ t₁ t₂ h))
            (chain⊗ (play t₂ (play t₁ h) i) (cnt x′ i) (play t₁ h i) (cnt y′ i) (cnt x i) (h i) (cnt y i) (eq₂ i) (eq₁ i)) )
exchange-map (m-pair {x′ = x′} {t₁ = t₁} r stopped) {h} pre lent =
  (OK-++ t₁ [] h (fst (exchange-map r (pre-l pre) (lent-w (cnt x′) lent))) tt , tt)
exchange-map (m-pair {x = x} {x′} {t₁ = t₁} {t₂} r (go-on {u = y} (fm-stop r′))) {h} {rf} pre lent
  with exchange-map r (pre-l pre) (lent-w (cnt x′) lent)
... | (ok₁ , eq₁) =
  ( OK-++ t₁ t₂ h ok₁
      (fst (exchange-map r′ (pre-r {a′ = y} {x′} {rf} (post-gen {v = x} {w = y} {t = t₁} {r = λ i → cnt x′ i + rf i} (mono-map r) (below-map r) (pre-l pre) ok₁ eq₁))
                            (lent-w (cnt y) lent)))
  , tt )

-- ★ NoLeak, for a run that returns: a whole program, from the empty heap,
-- frees every cell it allocated, exactly once, and frees nothing else.
noleak : ∀ {f : LTm Γ One One} {n′ t} → Run ds f mone mone 0 (gives mone n′) t
       → OK t (λ _ → 0) × (∀ i → play t (λ _ → 0) i ≡ 0)
noleak run with exchange run {λ _ → 0} {λ _ → 0}
                  record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n } lent₀
... | (ok , eq) = (ok , λ i → trans (sym (+0 _)) (eq i))

------------------------------------------------------------------------
-- 6. ★ LIFETIMES: each block allocated is freed exactly once (the user's
--    invariant, 2026-11-08).
--
-- Stated per block, on the trace itself: the events on a block `i` are
-- lifetimes, one after another — `alloc i` (born), any number of reads
-- (`peek i`), exactly one `free i` (died) — and nothing on `i` outside them.
-- `Life dead k dead` is the language (born read* died)*. Double free, free of
-- a stranger and read of a dead cell are its consequences.
--
-- It is not proved rule by rule. The rules are proved with COUNTS (`OK`, a
-- block's count checked before every event; `exchange`), because counts add
-- up and so compose under `∘l`, `⊗l` and the frame. `life` turns legal counts
-- into lifetimes once, for every trace, by induction on the trace.
------------------------------------------------------------------------

data Kind : Set where
  born read died : Kind

-- what an event does to block `i`
kind : Id → Ev → List Kind
kind i (alloc j) with j ≟ᵢ i
... | yes _ = born ∷ []
... | no  _ = []
kind i (free j)  with j ≟ᵢ i
... | yes _ = died ∷ []
... | no  _ = []
kind i (peek j)  with j ≟ᵢ i
... | yes _ = read ∷ []
... | no  _ = []
kind i (io _ _ _) = []
kind i (stp _ _)  = []
kind i (tmp _)    = []

-- the events on block `i`, in order: a homomorphism of free monoids
on : Id → Trace → List Kind
on i = concatMap (kind i)

data St : Set where
  dead live : St

-- `Life s k s′`: from state `s`, the events `k` are lifetimes, ending in `s′`
data Life : St → List Kind → St → Set where
  done  : ∀ {s} → Life s [] s
  birth : ∀ {k s} → Life live k s → Life dead (born ∷ k) s
  use   : ∀ {k s} → Life live k s → Life live (read ∷ k) s
  death : ∀ {k s} → Life dead k s → Life live (died ∷ k) s

st : ℕ → St
st zero    = dead
st (suc _) = live

-- legal counts are lifetimes, on every trace
life : ∀ t h i → OK t h → h i ≤ 1 → Life (st (h i)) (on i t) (st (play t h i))
life []            h i _        _  = done
life (alloc j ∷ t) h i (p , ok) le with j ≟ᵢ i
... | yes refl =
  let h′ = step (alloc j) h ; z = st (play t h′ j) ; e = trans (cong (_+ δ j j) p) (δ-same j) in
  subst (λ x → Life x (born ∷ on j t) z) (cong st (sym p))
        (birth (subst (λ x → Life (st x) (on j t) z) e
                      (life t h′ j ok (subst (_≤ 1) (sym e) ≤-refl))))
... | no ne =
  let h′ = step (alloc j) h ; z = st (play t h′ i) ; e = trans (cong (h i +_) (δ-≢ ne)) (+0 (h i)) in
  subst (λ x → Life (st x) (on i t) z) e (life t h′ i ok (subst (_≤ 1) (sym e) le))
life (free j ∷ t)  h i (p , ok) le with j ≟ᵢ i
... | yes refl =
  let h′ = step (free j) h ; z = st (play t h′ j) ; e = cong₂ _∸_ p (δ-same j) in
  subst (λ x → Life x (died ∷ on j t) z) (cong st (sym p))
        (death (subst (λ x → Life (st x) (on j t) z) e
                      (life t h′ j ok (subst (_≤ 1) (sym e) z≤n))))
... | no ne =
  let h′ = step (free j) h ; z = st (play t h′ i) ; e = cong (h i ∸_) (δ-≢ ne) in
  subst (λ x → Life (st x) (on i t) z) e (life t h′ i ok (subst (_≤ 1) (sym e) le))
life (peek j ∷ t)  h i (p , ok) le with j ≟ᵢ i
... | yes refl =
  let z = st (play t h j) in
  subst (λ x → Life x (read ∷ on j t) z) (cong st (sym p))
        (use (subst (λ x → Life x (on j t) z) (cong st p) (life t h j ok le)))
... | no _ = life t h i ok le
life (io _ _ _ ∷ t) h i (_ , ok) le = life t h i ok le
life (stp _ _ ∷ t)  h i (_ , ok) le = life t h i ok le
life (tmp _ ∷ t)    h i (_ , ok) le = life t h i ok le

-- ★ the invariant, for a whole program that returns: every block it
-- allocates is freed exactly once, read only in between, and none is open at
-- the end
lifetimes : ∀ {f : LTm Γ One One} {n′ t} → Run ds f mone mone 0 (gives mone n′) t → ∀ i → Life dead (on i t) dead
lifetimes {t = t} run i with noleak run
... | (ok , empty) = subst (λ x → Life dead (on i t) (st x)) (empty i) (life t (λ _ → 0) i ok z≤n)

-- ★ the exit exception: a run that stops (a halt, or the memory running out)
-- from an input with no cells has the same lifetimes, except that a block's
-- last one may be open: the block is live at the exit
lifetimes-exit : ∀ {A B} {f : LTm Γ A B} {a : MV A} {y t} → (∀ i → cnt a i ≡ 0) → Run ds f mone a 0 (stop y) t
               → ∀ i → Σ St (λ s → Life dead (on i t) s)
lifetimes-exit {a = a} {t = t} no-cells run i =
  ( _ , life t (λ _ → 0) i
          (fst (exchange run {λ _ → 0} {λ _ → 0}
                  record { le1 = λ _ → z≤n ; above = λ _ _ → refl
                         ; sub = λ i → subst (_≤ 0) (sym (trans (+0 (cnt a i)) (no-cells i))) z≤n } lent₀))
          z≤n )
