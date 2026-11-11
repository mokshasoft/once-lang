-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Examples — plan 0.146 A6: concrete RUNS.
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
--   * Closures, lending, in-place reuse, and (A11) SigOps inside a fold and a
--     closure, a halt with a block live, a loop that ends, a server that runs
--     out.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _≤_)
open import Data.List using (List; []; _∷_)
open import LinCore.Flat using (FTy; funit; fvoid; fw)

module LinCore.Examples where

data B : Set where
  int : B

⟦_⟧B : B → Set
⟦ int ⟧B  = ℕ

data Op : Set where
  emit succ exit : Op

-- A12: flat types, as the Spec's: an emit answers `unit`, an exit `void`
dom cod : Op → FTy B
dom emit = fw int
dom succ = fw int
dom exit = fw int
cod emit = funit
cod succ = fw int
cod exit = fvoid

open import LinCore.NbEPLinCore B ⟦_⟧B Op dom cod
open import LinCore.Events B ⟦_⟧B Op dom cod
open import LinCore.Act B ⟦_⟧B Op dom cod

-- the events of a loop run, and of a run
trace-of : ∀ {E A C} {round : Tm E A (C ⊕t A)} {e s n k s′ n′ t} → Loop round e s n k s′ n′ t → Trace
trace-of {t = t} _ = t

trace-of-run : ∀ {A C} {f : LTm A C} {v o n t} → Run f mone v n o t → Trace
trace-of-run {t = t} _ = t

------------------------------------------------------------------------
-- 1. `loop-forever-emit`:
--
--   round = next . (snd . pair (emit@E . id) id),   next n = inr (n + 1)
------------------------------------------------------------------------

emit-round : LTm (Bt int) (Zero ⊕t Bt int)
emit-round =
  linr                              -- continue
  ∘l lop succ                       -- n + 1
  ∘l (lul ∘l (drop ⊗l lid))         -- snd: drop the emit's Unit answer
  ∘l (lop emit ⊗l lid)              -- emit the first
  ∘l dup                            -- pair … id: the Int, twice (a word: no cell)

-- one round, from the counter `x`, the world answering `tt` to the emit and
-- `x′` to the successor
emit-step : ∀ (x x′ : ℕ) n → Run emit-round mone (mbase x) n (gives (minr (mbase x′)) n) _
emit-step x x′ n =
  r-∘ (r-∘ (r-∘ (r-∘ r-dup (r-⊗ (r-op {y = tt}) r-id))
                (r-∘ (r-⊗ r-drop r-id) r-λ))
           (r-op {y = x′}))
      r-inr

-- two rounds: 0 → 1 → 2
emit-server : Loop emit-round mone (mbase 0) 0 2 (mbase 2) 0 _
emit-server = l-suc (emit-step 0 1 0) (l-suc (emit-step 1 2 0) l-zero)

-- ★ after both rounds the heap is the one it started with
emit-server-constant : ∀ i → play (trace-of emit-server) (λ _ → 0) i ≡ 0
emit-server-constant = snd′ (word-server emit-server {λ _ → 0} {λ _ → 0}
                         record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }
                         lent₀)
  where snd′ : ∀ {P Q : Set} → P × Q → Q
        snd′ (_ , q) = q

-- the emit server's two rounds touch no cell at all: its events are SigOp calls
emit-events : trace-of emit-server ≡ io emit 0 tt ∷ io succ 0 1 ∷ io emit 1 tt ∷ io succ 1 2 ∷ []
emit-events = refl

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

list-round : LTm IntList (Zero ⊕t IntList)
list-round = linr ∘l rebuild

-- [x], in cells 0 (the cons) and 1 (the nil)
one-list : ℕ → MV IntList
one-list x = mmu 0 (minr (mpair (mbase x) (mmu 1 (minl mone))))

-- [x] again, in fresh cells 3 (the cons) and 2 (the nil)
new-list : ℕ → MV IntList
new-list x = mmu 3 (minr (mpair (mbase x) (mmu 2 (minl mone))))

-- one round from counter 2: the cons cell 0 and the nil cell 1 are freed, a new
-- nil (2) and a new cons (3) are allocated
list-step : ∀ x → Run list-round mone (one-list x) 2 (gives (minr (new-list x)) 4) _
list-step x =
  r-∘ (r-cata (m-inr (m-pair m-b (m-id (r-cata (m-inl m-one) r-In)))) r-In)
      r-inr

list-server : Loop list-round mone (one-list 5) 2 1 (new-list 5) 4 _
list-server = l-suc (list-step 5) l-zero

-- the heap before: exactly the old list's cells, 0 and 1
heap₀ : Heap
heap₀ i = cnt (one-list 5) i

-- ★ the round's events are legal, and afterwards the heap holds exactly the
-- new list's cells (2 and 3) instead of the old one's
list-server-exchange : OK (trace-of list-server) heap₀
                     × (∀ i → play (trace-of list-server) heap₀ i + cnt (one-list 5) i
                            ≡ heap₀ i + cnt (new-list 5) i)
list-server-exchange = loop-exchange list-server {heap₀} {λ _ → 0}
  record { le1   = le1′
         ; above = above′
         ; sub   = λ i → sub′ i }
  lent₀
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
list-events : trace-of list-server ≡ free 0 ∷ free 1 ∷ alloc 2 ∷ alloc 3 ∷ []
list-events = refl

-- and the heap afterwards holds exactly the new list
list-after : (play (trace-of list-server) heap₀ 0 ≡ 0) × (play (trace-of list-server) heap₀ 1 ≡ 0)
           × (play (trace-of list-server) heap₀ 2 ≡ 1) × (play (trace-of list-server) heap₀ 3 ≡ 1)
list-after = refl , refl , refl , refl

------------------------------------------------------------------------
-- 3. D131: a fold whose algebra is a CLOSURE, obtained once and applied at
--    every layer. The closure is a many-use one (`⇛t`); the fold borrows it
--    (`lend`, `bapp` at each layer) and it is freed once, after.
------------------------------------------------------------------------

-- the algebra, as a closure value (its environment is `One` here)
alg-closure : LTm One (LF∙ ListF IntList ⇛t IntList)
alg-closure = lcurryB lIn

-- build the closure, lend it to the fold, drop it
closure-fold : LTm IntList IntList
closure-fold = lul ∘l (drop ⊗l lid) ∘l lend (bsnd (lcata ListF bapp)) ∘l (alg-closure ⊗l lid) ∘l lul⁻

-- on [5] (cells 0, 1), from counter 2: the closure is cell 2; the new list is 4 → 3
closure-fold-run : Run closure-fold mone (one-list 5) 2 (gives (mmu 4 (minr (mpair (mbase 5) (mmu 3 (minl mone))))) 5) _
closure-fold-run =
  r-∘ (r-∘ (r-∘ (r-∘ r-λ⁻ (r-⊗ r-curryB r-id))
                (r-lend (r-snd (r-cata (m-inr (m-pair m-b (m-id (r-cata (m-inl m-one) (r-app r-In)))))
                                       (r-app r-In)))))
           (r-⊗ r-drop r-id))
      r-λ

-- ★ by evaluation: the closure allocated once (2), read once per layer
-- (peek 2, twice), never copied, freed once at the end
closure-fold-events : trace-of-run closure-fold-run
                    ≡ alloc 2 ∷ free 0 ∷ free 1 ∷ peek 2 ∷ alloc 3 ∷ peek 2 ∷ alloc 4 ∷ free 2 ∷ []
closure-fold-events = refl

------------------------------------------------------------------------
-- 4. A8: the same round, IN PLACE. Written `lcata ListF (lIn ∘l lid)` (the
--    algebra rebuilds each node with the same functor), the fold may reuse
--    each consumed node's cell for the rebuilt node.
------------------------------------------------------------------------

rebuild-in-place : LTm IntList IntList
rebuild-in-place = lcata ListF (lIn ∘l lid)

in-place-run : Run rebuild-in-place mone (one-list 5) 2 (gives (one-list 5) 2) _
in-place-run = r-cata-reuse (m-inr (m-pair m-b (m-id (r-cata-reuse (m-inl m-one) r-id)))) r-id

-- ★ by evaluation: no event at all — the list was rebuilt in its own cells
in-place-events : trace-of-run in-place-run ≡ []
in-place-events = refl

-- and it means the same as the rebuild that frees and allocates
in-place-sound : RB (block (Lᶜ rebuild-in-place tt (er (one-list 5)))) [] (returns (er (one-list 5)))
in-place-sound = sound in-place-run

------------------------------------------------------------------------
-- 5. The lifetime of one block, by evaluation: the algebra closure of §3
--    (block 2) is born, read once per layer, and dies once.
------------------------------------------------------------------------

closure-life : on 2 (trace-of-run closure-fold-run) ≡ born ∷ read ∷ read ∷ died ∷ []
closure-life = refl

closure-life-ok : Life dead (on 2 (trace-of-run closure-fold-run)) dead
closure-life-ok = birth (use (use (death done)))

------------------------------------------------------------------------
-- 6. A10: NESTED LENDING. Two scopes, and the inner body reads what the OUTER
--    one lent (a copy of it, D402's choice A). Neither lent value is touched.
------------------------------------------------------------------------

nested-lend : LTm (IntList ⊗t (Bt int ⊗t One)) (IntList ⊗t (Bt int ⊗t IntList))
nested-lend = lend (lend (bfst (bsnd bcopy)))

nested-run : Run nested-lend mone (mpair (one-list 5) (mpair (mbase 7) mone)) 2 (gives _ 4) _
nested-run = r-lend (r-lend (r-fst (r-snd r-copy)))

-- ★ by evaluation: only the copy allocates; both lent values stay as they were
nested-events : trace-of-run nested-run ≡ alloc 2 ∷ alloc 3 ∷ []
nested-events = refl

------------------------------------------------------------------------
-- 7. A11: a SigOp INSIDE A FOLD (D131: an algebra may have effects). The
--    fold emits each element, children first.
------------------------------------------------------------------------

emit-fold : LTm IntList One
emit-fold = lcata ListF (lcase lid (drop ∘l lop emit ∘l ρl))

emit-fold-run : Run emit-fold mone (one-list 5) 2 (gives mone 2) _
emit-fold-run =
  r-cata (m-inr (m-pair m-b (m-id (r-cata (m-inl m-one) (r-case₁ r-id)))))
         (r-case₂ (r-∘ (r-∘ r-ρ (r-op {y = tt})) r-drop))

-- ★ by evaluation: both cells freed, then the emit
emit-fold-events : trace-of-run emit-fold-run ≡ free 0 ∷ free 1 ∷ io emit 5 tt ∷ []
emit-fold-events = refl

------------------------------------------------------------------------
-- 8. A11: a SigOp INSIDE A CLOSURE.
------------------------------------------------------------------------

emit-closure : LTm (Bt int) One
emit-closure = leval ∘l (lcurry (lop emit ∘l lul) ⊗l lid) ∘l lul⁻

emit-closure-run : Run emit-closure mone (mbase 5) 0 (gives mone 1) _
emit-closure-run =
  r-∘ (r-∘ r-λ⁻ (r-⊗ r-curry r-id))
      (r-eval (r-∘ r-λ (r-op {y = tt})))

emit-closure-events : trace-of-run emit-closure-run ≡ alloc 0 ∷ free 0 ∷ io emit 5 tt ∷ []
emit-closure-events = refl

------------------------------------------------------------------------
-- 9. A11: a HALT with a block live: the exit exception. A nil is built, then
--    the program ends with it still live.
------------------------------------------------------------------------

halting : LTm (Bt int) (Zero ⊗t IntList)
halting = (lhalt exit ⊗l lid) ∘l (lid ⊗l (lIn ∘l linl)) ∘l ρl⁻

halting-run : Run halting mone (mbase 5) 0 (stop halted) _
halting-run =
  r-∘ (r-∘ r-ρ⁻ (r-⊗ r-id (r-∘ r-inl r-In)))
      (r-⊗!₁ r-halt)

halting-events : trace-of-run halting-run ≡ alloc 0 ∷ stp exit 5 ∷ []
halting-events = refl

-- ★ block 0 is born and never dies: legal, because the program halted
halting-open : Life dead (on 0 (trace-of-run halting-run)) live
halting-open = birth done

-- and every block's events are lifetimes, by the theorem
halting-legal : ∀ i → Agda.Builtin.Sigma.Σ St (λ s → Life dead (on i (trace-of-run halting-run)) s)
halting-legal = lifetimes-exit (λ i → refl) halting-run

------------------------------------------------------------------------
-- 10. A11: the loop as a generator: one that ends, and a server that runs out
--     after two rounds.
------------------------------------------------------------------------

count-round : LTm (One ⊕t One) (One ⊕t (One ⊕t One))
count-round = lcase (linr ∘l linr) linl

count-run : Run (liter count-round) mone (minl mone) 0 (gives mone 0) _
count-run = r-iter-next (r-case₁ (r-∘ r-inr r-inr)) (r-iter-done (r-case₂ r-inl))

ran-out : Run (liter emit-round) mone (mbase 0) 0 (stop exhausted) _
ran-out = loop-run emit-server r-exh

ran-out-events : trace-of-run ran-out ≡ io emit 0 tt ∷ io succ 0 1 ∷ io emit 1 tt ∷ io succ 1 2 ∷ []
ran-out-events = refl

-- ★ and what it did is a prefix of what the server means
ran-out-sound : RB (block (Lᶜ (liter emit-round) tt 0))
                   (io-call emit 0 tt ∷ io-call succ 0 1 ∷ io-call emit 1 tt ∷ io-call succ 1 2 ∷ [])
                   (ended exhausted)
ran-out-sound = sound ran-out
