-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Examples — plan 0.146 A6: the gate's servers, as RUNS.
--
-- The theorems of `Events` and `Act` are about every run that exists; a
-- relation with no runs would make them vacuous. These are concrete runs,
-- built rule by rule, and the theorems applied to them:
--
--   * `emit-server`: `compiler/test/loop-forever-emit.once` — each round
--     emits its counter and continues with the next. Two rounds; afterwards
--     the heap is exactly what it was (`word-server`).
--   * `list-server`: a server whose STATE IS HEAP-SHAPED — a list, rebuilt
--     by a fold every round (each old node freed, each new node allocated).
--     One round on a one-element list: two frees, two allocs, and the heap
--     afterwards holds exactly the new list (`loop-exchange`).
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _≤_)
open import Data.List using (List; []; _∷_)

module LinCore.Examples where

data B : Set where
  int unit : B

⟦_⟧B : B → Set
⟦ int ⟧B  = ℕ
⟦ unit ⟧B = ⊤

data Op : Set where
  emit succ : Op

dom cod : Op → B
dom emit = int
dom succ = int
cod emit = unit
cod succ = int

open import LinCore.NbEPLinCore B ⟦_⟧B
open import LinCore.Events B ⟦_⟧B
open import LinCore.Act B ⟦_⟧B Op dom cod

-- the events of a loop run
trace-of : ∀ {E A C} {round : ATm E A (C ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t → List AEv
trace-of {t = t} _ = t

------------------------------------------------------------------------
-- 1. `loop-forever-emit`:
--
--   round = next . (snd . pair (emit@E . id) id),   next n = inr (n + 1)
------------------------------------------------------------------------

emit-round : ATm One (Bt int) (Zero ⊕t Bt int)
emit-round =
  apure (blift dup)                                  -- pair … id: the Int, twice (a word: no cell)
  ⨾ (aop emit ⊗a apure (blift lid))                  -- emit the first
  ⨾ apure (blift (lul ∘l (drop ⊗l lid)))             -- snd: drop the emit's Unit answer
  ⨾ aop succ                                         -- n + 1
  ⨾ apure (blift linr)                               -- continue

-- one round, from the counter `x`, the world answering `tt` to the emit and
-- `x′` to the successor
emit-step : ∀ (x x′ : ℕ) n → RunA emit-round mone (mbase x) n (ret (minr (mbase x′)) n) _
emit-step x x′ n =
  a-seq (a-seq (a-seq (a-seq (a-pure (b-lift r-dup))
                             (a-⊗ (a-op {y = tt}) (a-pure (b-lift r-id))))
                      (a-pure (b-lift (r-∘ (r-⊗ r-drop r-id) r-λ))))
               (a-op {y = x′}))
        (a-pure (b-lift r-inr))

-- two rounds: 0 → 1 → 2
emit-server : Loop emit-round mone (mbase 0) 0 2 (mbase 2) 0 _
emit-server = l-suc (emit-step 0 1 0) (l-suc (emit-step 1 2 0) l-zero)

-- ★ after both rounds the heap is the one it started with
emit-server-constant : ∀ i → play (memOf (trace-of emit-server)) (λ _ → 0) i ≡ 0
emit-server-constant = snd′ (word-server emit-server {λ _ → 0} {λ _ → 0}
                         record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }
                         (λ i ()))
  where snd′ : ∀ {P Q : Set} → P × Q → Q
        snd′ (_ , q) = q

------------------------------------------------------------------------
-- 2. A server whose state is a LIST, rebuilt by a fold every round.
------------------------------------------------------------------------

-- `List Int`: nil, or an Int and the rest
ListF : LF
ListF = Kone ⊕f (Kb int ⊗f Idf)

IntList : LTy
IntList = μt ListF

-- the fold whose algebra is the constructor: frees every node, builds a fresh one
rebuild : LTm IntList IntList
rebuild = lcata ListF lIn

list-round : ATm One IntList (Zero ⊕t IntList)
list-round = apure (blift rebuild) ⨾ apure (blift linr)

-- [x], in cells 0 (the cons) and 1 (the nil)
one-list : ℕ → MV IntList
one-list x = mmu 0 (minr (mpair (mbase x) (mmu 1 (minl mone))))

-- [x] again, in fresh cells 3 (the cons) and 2 (the nil)
new-list : ℕ → MV IntList
new-list x = mmu 3 (minr (mpair (mbase x) (mmu 2 (minl mone))))

-- one round from counter 2: the cons cell 0 and the nil cell 1 are freed, a new
-- nil (2) and a new cons (3) are allocated
list-step : ∀ x → RunA list-round mone (one-list x) 2
                       (ret (minr (new-list x)) 4) _
list-step x =
  a-seq (a-pure (b-lift (r-cata (m-inr (m-pair m-b (m-id (r-cata (m-inl m-one) r-In)))) r-In)))
        (a-pure (b-lift r-inr))

list-server : Loop list-round mone (one-list 5) 2 1 (new-list 5) 4 _
list-server = l-suc (list-step 5) l-zero

-- the heap before: exactly the old list's cells, 0 and 1
heap₀ : Heap
heap₀ i = cnt (one-list 5) i

-- ★ the round's events are legal, and afterwards the heap holds exactly the
-- new list's cells (2 and 3) instead of the old one's
list-server-exchange : OK (memOf (trace-of list-server)) heap₀
                     × (∀ i → play (memOf (trace-of list-server)) heap₀ i + cnt (one-list 5) i
                            ≡ heap₀ i + cnt (new-list 5) i)
list-server-exchange = loop-exchange list-server {heap₀} {λ _ → 0}
  record { le1   = le1′
         ; above = above′
         ; sub   = λ i → sub′ i }
  (λ i ())
  where
    le1′ : ∀ i → heap₀ i ≤ 1
    le1′ zero = s≤s z≤n
    le1′ (suc zero) = s≤s z≤n
    le1′ (suc (suc i)) = z≤n
    above′ : ∀ i → 2 ≤ i → heap₀ i ≡ 0
    above′ zero ()
    above′ (suc zero) (s≤s ())
    above′ (suc (suc i)) _ = refl
    sub′ : ∀ i → cnt (one-list 5) i + 0 ≤ heap₀ i
    sub′ zero = s≤s z≤n
    sub′ (suc zero) = s≤s z≤n
    sub′ (suc (suc i)) = z≤n

-- ★ what the round actually did, by evaluation: the old cons (0) and nil (1)
-- freed, the new nil (2) and cons (3) allocated, nothing else
list-events : memOf (trace-of list-server) ≡ free 0 ∷ free 1 ∷ alloc 2 ∷ alloc 3 ∷ []
list-events = refl

-- and the heap afterwards holds exactly the new list
list-after : (play (memOf (trace-of list-server)) heap₀ 0 ≡ 0) × (play (memOf (trace-of list-server)) heap₀ 1 ≡ 0)
           × (play (memOf (trace-of list-server)) heap₀ 2 ≡ 1) × (play (memOf (trace-of list-server)) heap₀ 3 ≡ 1)
list-after = refl , refl , refl , refl

-- the emit server's two rounds touch no cell at all: its events are SigOp calls
emit-events : memOf (trace-of emit-server) ≡ []
emit-events = refl
