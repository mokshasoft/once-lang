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
open import Data.List using (List; []; _∷_; _++_)
open import LinCore.Flat using (FTy; funit; fvoid; fw)

module LinCore.Examples where

data B : Set where
  int : B

⟦_⟧B : B → Set
⟦ int ⟧B  = ℕ

data Op : Set where
  emit succ exit : Op

-- A12: flat types, as the Spec's: an emit answers `unit`, an exit `void`
odom ocod : Op → FTy B
odom emit = fw int
odom succ = fw int
odom exit = fw int
ocod emit = funit
ocod succ = fw int
ocod exit = fvoid

-- an Int is one word (`Spec.ABI`)
bw : B → ℕ
bw int = 1

open import LinCore.NbEPLinCore B ⟦_⟧B Op odom ocod
open import LinCore.Events B ⟦_⟧B Op odom ocod bw
open import LinCore.Act B ⟦_⟧B Op odom ocod bw

-- the events of a loop run, and of a run
trace-of : ∀ {E A C} {round : Tm Γ E A (C ⊕t A)} {e s n k s′ n′ t} → Loop ds round e s n k s′ n′ t → Trace
trace-of {t = t} _ = t

trace-of-run : ∀ {A C} {f : LTm Γ A C} {v o n t} → Run ds f mone v n o t → Trace
trace-of-run {t = t} _ = t

------------------------------------------------------------------------
-- 1. `loop-forever-emit`:
--
--   round = next . (snd . pair (emit@E . id) id),   next n = inr (n + 1)
------------------------------------------------------------------------

emit-round : LTm ε (Bt int) (Zero ⊕t Bt int)
emit-round =
  linr                              -- continue
  ∘l lop succ                       -- n + 1
  ∘l (lul ∘l (drop ⊗l lid))         -- snd: drop the emit's Unit answer
  ∘l (lop emit ⊗l lid)              -- emit the first
  ∘l dup                            -- pair … id: the Int, twice (a word: no cell)

-- one round, from the counter `x`, the world answering `tt` to the emit and
-- `x′` to the successor
emit-step : ∀ (x x′ : ℕ) n → Run ε emit-round mone (mbase x) n (gives (minr (mbase x′)) n) _
emit-step x x′ n =
  r-∘ (r-∘ (r-∘ (r-∘ r-dup (r-⊗ (r-op {y = tt}) r-id))
                (r-∘ (r-⊗ r-drop r-id) r-λ))
           (r-op {y = x′}))
      r-inr

-- two rounds: 0 → 1 → 2
emit-server : Loop ε emit-round mone (mbase 0) 0 2 (mbase 2) 0 _
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
rebuild : LTm ε IntList IntList
rebuild = lcata ListF lIn

list-round : LTm ε IntList (Zero ⊕t IntList)
list-round = linr ∘l rebuild

-- ★ A12: a list node is 3 words (a tag, then the larger alternative: an Int
-- and a pointer), so every list block is named `(3 , serial)`
node-size : szμ ListF ≡ 3
node-size = refl

-- [x], built by a run from the empty heap: the nil in block (3 , 0), the cons
-- in block (3 , 1)
build : LTm ε (Bt int) IntList
build = lIn ∘l linr ∘l (lid ⊗l (lIn ∘l linl)) ∘l ρl⁻

one-list : ℕ → MV IntList
one-list x = mmu (3 , 1) (minr (mpair (mbase x) (mmu (3 , 0) (minl mone))))

build-run : Run ε build mone (mbase 5) 0 (gives (one-list 5) 2) _
build-run = r-∘ (r-∘ (r-∘ r-ρ⁻ (r-⊗ r-id (r-∘ r-inl r-In))) r-inr) r-In

build-events : trace-of-run build-run ≡ alloc (3 , 0) ∷ alloc (3 , 1) ∷ []
build-events = refl

-- the heap after it, and the precondition there, from the theorems
private
  pre₀ : Pre (λ _ → 0) 0 (mbase 5) (λ _ → 0)
  pre₀ = record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }

heap₀ : Heap
heap₀ = play (trace-of-run build-run) (λ _ → 0)

pre-list : Pre heap₀ 2 (one-list 5) (λ _ → 0)
pre-list with exchange build-run pre₀ lent₀
... | (ok , eq) = post build-run pre₀ ok eq

-- [x] again, in fresh blocks: the nil (3 , 2) and the cons (3 , 3)
new-list : ℕ → MV IntList
new-list x = mmu (3 , 3) (minr (mpair (mbase x) (mmu (3 , 2) (minl mone))))

-- one round from counter 2: the old cons and nil are freed, a new nil and a
-- new cons are allocated
list-step : ∀ x → Run ε list-round mone (one-list x) 2 (gives (minr (new-list x)) 4) _
list-step x =
  r-∘ (r-cata (m-inr (m-pair m-b (m-id (r-cata (m-inl m-one) r-In)))) r-In)
      r-inr

list-server : Loop ε list-round mone (one-list 5) 2 1 (new-list 5) 4 _
list-server = l-suc (list-step 5) l-zero

-- ★ the round's events are legal, and afterwards the heap holds exactly the
-- new list's cells instead of the old one's
list-server-exchange : OK (trace-of list-server) heap₀
                     × (∀ i → play (trace-of list-server) heap₀ i + cnt (one-list 5) i
                            ≡ heap₀ i + cnt (new-list 5) i)
list-server-exchange = loop-exchange list-server pre-list lent₀

-- ★ what the round actually did, by evaluation: the old cons and nil freed,
-- the new nil and cons allocated, nothing else; every block 3 words
list-events : trace-of list-server ≡ free (3 , 1) ∷ free (3 , 0) ∷ alloc (3 , 2) ∷ alloc (3 , 3) ∷ []
list-events = refl

-- and the heap afterwards holds exactly the new list
list-after : (play (trace-of list-server) heap₀ (3 , 0) ≡ 0) × (play (trace-of list-server) heap₀ (3 , 1) ≡ 0)
           × (play (trace-of list-server) heap₀ (3 , 2) ≡ 1) × (play (trace-of list-server) heap₀ (3 , 3) ≡ 1)
list-after = refl , refl , refl , refl

-- ★ A12: the new list's blocks carry the node size, by the theorem
list-sized : Sized {Zero ⊕t IntList} (minr (new-list 5))
list-sized = sized (list-step 5) tt (sized build-run tt tt)

------------------------------------------------------------------------
-- 3. ★ D405: THE PROGRAM'S LABELS. Five lambdas, oldest first; each body is
--    typed over the labels before it.
--
--      0  a fold's algebra over an Int (many-use: applied lent, D131)
--      1  the same over `One`
--      2  emit its argument          (one-shot, over `One`)
--      3  the successor              (one-shot, over `One`)
--      4  2 after 3: its environment is the two closures it composes
------------------------------------------------------------------------

σ-alg : LTy → Sg
σ-alg X = sg many X (LF∙ ListF IntList) IntList

σ-emit σ-succ σ-comp : Sg
σ-emit = sg once One (Bt int) One
σ-succ = sg once One (Bt int) (Bt int)
σ-comp = sg once (Ct 2 One ⊗t Ct 3 One) (Bt int) One

Γ₄ Γₚ : Cx
Γ₄ = ε ▸ σ-alg (Bt int) ▸ σ-alg One ▸ σ-emit ▸ σ-succ
Γₚ = Γ₄ ▸ σ-comp

-- the composition's body: ((g , f) , a) ↦ g (f a)
comp-body : LTm Γ₄ ((Ct 2 One ⊗t Ct 3 One) ⊗t Bt int) One
comp-body = lapp (there here) ∘l (lid ⊗l lapp here) ∘l lassoc

defs : Defs Γₚ
defs = ε ▸ bω lIn ▸ bω lIn ▸ b1 (lop emit ∘l lul) ▸ b1 (lop succ ∘l lul) ▸ b1 comp-body

-- the labels, in the whole program
p0 : Γₚ ∋[ 0 ] σ-alg (Bt int)
p0 = there (there (there (there here)))

p1 : Γₚ ∋[ 1 ] σ-alg One
p1 = there (there (there here))

p2 : Γₚ ∋[ 2 ] σ-emit
p2 = there (there here)

p3 : Γₚ ∋[ 3 ] σ-succ
p3 = there here

p4 : Γₚ ∋[ 4 ] σ-comp
p4 = here

-- ★ what nothing at run time records: a closure over an Int is that Int, one
-- over `One` or over two such closures is nothing; where two lambdas meet, the
-- sum's tag is the only word added
clo-words : (words (Ct 0 (Bt int)) ≡ 1) × (words (Ct 1 One) ≡ 0) × (words (Ct 4 (Ct 2 One ⊗t Ct 3 One)) ≡ 0)
clo-words = refl , refl , refl

meet-words : words (Ct 0 (Bt int) ⊕t Ct 1 One) ≡ 2
meet-words = refl

------------------------------------------------------------------------
-- 3½. D131: a fold whose algebra is a CLOSURE, obtained once and applied at
--     every layer. The closure is a many-use one (label 0); the fold borrows
--     it (`lend`, `bapp` at each layer). ★ D405: it is its environment, an
--     Int in place: building, lending, applying and dropping it are no events.
------------------------------------------------------------------------

-- build the closure, lend it to the fold, drop it
closure-fold : LTm Γₚ (Bt int ⊗t IntList) IntList
closure-fold = lul ∘l (drop ⊗l lid) ∘l lend (bsnd (lcata ListF (bapp p0))) ∘l (lclo p0 ⊗l lid)

q0 : Look defs p0 ε (bω lIn)
q0 = lk-there (lk-there (lk-there (lk-there lk-here)))

-- on 7 and [5], from counter 2: the new list is (3 , 3) → (3 , 2)
closure-fold-run : Run defs closure-fold mone (mpair (mbase 7) (one-list 5)) 2 (gives (new-list 5) 4) _
closure-fold-run =
  r-∘ (r-∘ (r-∘ (r-⊗ r-clo r-id)
                (r-lend (r-snd (r-cata (m-inr (m-pair m-b (m-id (r-cata (m-inl m-one) (r-bapp q0 r-In)))))
                                       (r-bapp q0 r-In)))))
           (r-⊗ r-drop r-id))
      r-λ

-- ★ by evaluation: only the list's own events. (Under D404 the closure was a
-- block of a code word and the Int: allocated, read once per layer, freed.)
closure-fold-events : trace-of-run closure-fold-run ≡ free (3 , 1) ∷ free (3 , 0) ∷ alloc (3 , 2) ∷ alloc (3 , 3) ∷ []
closure-fold-events = refl

------------------------------------------------------------------------
-- 4. A8: the same round, IN PLACE. Written `lcata ListF (lIn ∘l lid)` (the
--    algebra rebuilds each node with the same functor), the fold may reuse
--    each consumed node's cell for the rebuilt node.
------------------------------------------------------------------------

rebuild-in-place : LTm ε IntList IntList
rebuild-in-place = lcata ListF (lIn ∘l lid)

in-place-run : Run ε rebuild-in-place mone (one-list 5) 2 (gives (one-list 5) 2) _
in-place-run = r-cata-reuse (m-inr (m-pair m-b (m-id (r-cata-reuse (m-inl m-one) r-id)))) r-id

-- ★ by evaluation: no event at all — the list was rebuilt in its own cells
in-place-events : trace-of-run in-place-run ≡ []
in-place-events = refl

-- and it means the same as the rebuild that frees and allocates
in-place-sound : RB (block (Lᶜ ε rebuild-in-place tt (er (one-list 5)))) [] (returns (er (one-list 5)))
in-place-sound = sound in-place-run

------------------------------------------------------------------------
-- 5. The lifetime of one block, by evaluation: the nil of §2 (block (3 , 0))
--    is born when the list is built and dies in the server's round.
------------------------------------------------------------------------

nil-life : on (3 , 0) (trace-of-run build-run ++ trace-of list-server) ≡ born ∷ died ∷ []
nil-life = refl

nil-life-ok : Life dead (on (3 , 0) (trace-of-run build-run ++ trace-of list-server)) dead
nil-life-ok = birth (death done)

------------------------------------------------------------------------
-- 6. A10: NESTED LENDING. Two scopes, and the inner body reads what the OUTER
--    one lent (a copy of it, D402's choice A). Neither lent value is touched.
------------------------------------------------------------------------

nested-lend : LTm ε (IntList ⊗t (Bt int ⊗t One)) (IntList ⊗t (Bt int ⊗t IntList))
nested-lend = lend (lend (bfst (bsnd bcopy)))

nested-run : Run ε nested-lend mone (mpair (one-list 5) (mpair (mbase 7) mone)) 2 (gives _ 4) _
nested-run = r-lend (r-lend (r-fst (r-snd r-copy)))

-- ★ by evaluation: only the copy allocates; both lent values stay as they were
nested-events : trace-of-run nested-run ≡ alloc (3 , 2) ∷ alloc (3 , 3) ∷ []
nested-events = refl

------------------------------------------------------------------------
-- 7. A11: a SigOp INSIDE A FOLD (D131: an algebra may have effects). The
--    fold emits each element, children first.
------------------------------------------------------------------------

emit-fold : LTm ε IntList One
emit-fold = lcata ListF (lcase lid (drop ∘l lop emit ∘l ρl))

emit-fold-run : Run ε emit-fold mone (one-list 5) 2 (gives mone 2) _
emit-fold-run =
  r-cata (m-inr (m-pair m-b (m-id (r-cata (m-inl m-one) (r-case₁ r-id)))))
         (r-case₂ (r-∘ (r-∘ r-ρ (r-op {y = tt})) r-drop))

-- ★ by evaluation: both cells freed, then the emit
emit-fold-events : trace-of-run emit-fold-run ≡ free (3 , 1) ∷ free (3 , 0) ∷ io emit 5 tt ∷ []
emit-fold-events = refl

------------------------------------------------------------------------
-- 8. A11: a SigOp INSIDE A CLOSURE.
------------------------------------------------------------------------

emit-closure : LTm Γₚ (Bt int) One
emit-closure = lapp p2 ∘l (lclo p2 ⊗l lid) ∘l lul⁻

q2 : Look defs p2 _ (b1 (lop emit ∘l lul))
q2 = lk-there (lk-there lk-here)

emit-closure-run : Run defs emit-closure mone (mbase 5) 0 (gives mone 0) _
emit-closure-run =
  r-∘ (r-∘ r-λ⁻ (r-⊗ r-clo r-id))
      (r-app q2 (r-∘ r-λ (r-op {y = tt})))

-- the emit is the only event
emit-closure-events : trace-of-run emit-closure-run ≡ io emit 5 tt ∷ []
emit-closure-events = refl

------------------------------------------------------------------------
-- 8½. ★ D405: a COMPOSITION. Label 4's environment is the two closures it
--     composes; its body applies them by their labels, over its own prefix.
--     Three closures, no words, no events: only the SigOps.
------------------------------------------------------------------------

composed : LTm Γₚ (Bt int) One
composed = lapp p4 ∘l ((lclo p4 ∘l (lclo p2 ⊗l lclo p3) ∘l lul⁻) ⊗l lid) ∘l lul⁻

q4 : Look defs p4 _ (b1 comp-body)
q4 = lk-here

composed-run : Run defs composed mone (mbase 5) 0 (gives mone 0) _
composed-run =
  r-∘ (r-∘ r-λ⁻ (r-⊗ (r-∘ (r-∘ r-λ⁻ (r-⊗ r-clo r-clo)) r-clo) r-id))
      (r-app q4 (r-∘ (r-∘ r-α (r-⊗ r-id (r-app lk-here (r-∘ r-λ (r-op {y = 6})))))
                     (r-app (lk-there lk-here) (r-∘ r-λ (r-op {y = tt})))))

composed-events : trace-of-run composed-run ≡ io succ 5 6 ∷ io emit 6 tt ∷ []
composed-events = refl

-- and it means what it does
composed-sound : RB (block (Lᶜ ⟦ defs ⟧D composed tt 5)) (io-call succ 5 6 ∷ io-call emit 6 tt ∷ []) (returns tt)
composed-sound = sound composed-run

------------------------------------------------------------------------
-- 9. A11: a HALT with a block live: the exit exception. A nil is built, then
--    the program ends with it still live.
------------------------------------------------------------------------

halting : LTm ε (Bt int) (Zero ⊗t IntList)
halting = (lhalt exit ⊗l lid) ∘l (lid ⊗l (lIn ∘l linl)) ∘l ρl⁻

halting-run : Run ε halting mone (mbase 5) 0 (stop halted) _
halting-run =
  r-∘ (r-∘ r-ρ⁻ (r-⊗ r-id (r-∘ r-inl r-In)))
      (r-⊗!₁ r-halt)

halting-events : trace-of-run halting-run ≡ alloc (3 , 0) ∷ stp exit 5 ∷ []
halting-events = refl

-- ★ block (3 , 0) is born and never dies: legal, because the program halted
halting-open : Life dead (on (3 , 0) (trace-of-run halting-run)) live
halting-open = birth done

-- and every block's events are lifetimes, by the theorem
halting-legal : ∀ i → Agda.Builtin.Sigma.Σ St (λ s → Life dead (on i (trace-of-run halting-run)) s)
halting-legal = lifetimes-exit (λ i → refl) halting-run

------------------------------------------------------------------------
-- 10. A11: the loop as a generator: one that ends, and a server that runs out
--     after two rounds.
------------------------------------------------------------------------

count-round : LTm ε (One ⊕t One) (One ⊕t (One ⊕t One))
count-round = lcase (linr ∘l linr) linl

count-run : Run ε (liter count-round) mone (minl mone) 0 (gives mone 0) _
count-run = r-iter-next (r-case₁ (r-∘ r-inr r-inr)) (r-iter-done (r-case₂ r-inl))

ran-out : Run ε (liter emit-round) mone (mbase 0) 0 (stop exhausted) _
ran-out = loop-run emit-server r-exh

ran-out-events : trace-of-run ran-out ≡ io emit 0 tt ∷ io succ 0 1 ∷ io emit 1 tt ∷ io succ 1 2 ∷ []
ran-out-events = refl

-- ★ and what it did is a prefix of what the server means
ran-out-sound : RB (block (Lᶜ ε (liter emit-round) tt 0))
                   (io-call emit 0 tt ∷ io-call succ 0 1 ∷ io-call emit 1 tt ∷ io-call succ 1 2 ∷ [])
                   (ended exhausted)
ran-out-sound = sound ran-out
