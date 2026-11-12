-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Examples — plan 0.146 A6: concrete RUNS.
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
--     out; (D406) a ν, defunctionalised; (A13) a fold's work stack, a
--     temporary block.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
import Agda.Builtin.Sigma as Σ
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _≤_)
open import Data.Nat.Properties using (n∸n≡0)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing; _>>=_)
import Data.Maybe
import Once.LinCore.Alloc as Al
import Once.LinCore.Region as Rg
import Once.LinCore.AllocRun
open import Once.LinCore.Free using (Weave; w-[]; w-run; w-tmp)
import Once.LinCore.Flat as Fl
open import Once.Spec.Numerics using (TargetNum)
open import Once.Target.Arch using (arch-numerics; x86-64)
open import Once.IR.Semantics.Trace using (FFIAnswers; callOp; haltOp)
open import Once.Res using (stopped)
open import Once.Spec.Name using (bare)
open import Once.Spec.Type using (Int; Unit; Void; b-Int; b-Unit; b-Void)
open import Once.SigOp.Info using (SigOpInfo; mk-info'; emitsV; callsV; haltsV)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Boundary using (atTarget)
import Once.IR.Semantics.Value Carrier Carrier as Val

module Once.LinCore.Examples where

-- ★ B1.2: the core is master's: x86-64's numerics, no pure FFI answers
fmt₀ : TargetNum
fmt₀ = arch-numerics x86-64

ans₀ : FFIAnswers
ans₀ _ _ _ _ = stopped

-- master's SigOps: an emit (answers `unit`), a call the world answers (an
-- `Int → Int`), and an exit (halts)
emit-i : SigOpInfo Int Unit
emit-i = mk-info' (bare "emit") (emitsV refl) b-Int b-Unit

succ-i : SigOpInfo Int Int
succ-i = mk-info' (bare "succ") callsV b-Int b-Int

exit-i : SigOpInfo Int Void
exit-i = mk-info' (bare "exit") (haltsV refl) b-Int b-Void

-- an Int is one word (`Spec.ABI`)
bw : Fl.Base → ℕ
bw Fl.int   = 1
bw Fl.float = 1

open import Once.LinCore.NbEPLinCore fmt₀ ans₀
open import Once.LinCore.Events fmt₀ ans₀ bw
open import Once.LinCore.Act fmt₀ ans₀ bw
open import Once.LinCore.Temps fmt₀ ans₀ bw
open import Once.LinCore.Total fmt₀ ans₀ bw
open import Once.LinCore.Pass fmt₀ ans₀ renaming (Out to Outν)
open import Once.LinCore.Whole fmt₀ ans₀ bw
open import Once.LinCore.Machine fmt₀ ans₀ bw
open import Once.LinCore.Held fmt₀ ans₀ bw
module AR = Once.LinCore.AllocRun fmt₀ ans₀ bw

emit succ exit : Sig
emit = sig emit-i
succ = sig succ-i
exit = sig exit-i

-- the operations the events name (`DenotTrace.sigOpT`)
emitO succO : CallOp
emitO = callOp (bare "emit") Int b-Int Unit
succO = callOp (bare "succ") Int b-Int Int

exitH : HaltOp
exitH = haltOp (bare "exit") Int b-Int

-- an `Int` word (two base words share `Carrier`, so a literal names its own)
pattern mi x = mbase {int} x

-- what an answer is at the target (`atTarget`): an `Int` modulo 2⁶⁴
nrm : ℕ → ℕ
nrm a = atTarget fmt₀ (Int {0}) a

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

-- a round is a finite block (the Spec's `⊢iter`)
emit-blk : Blk emit-round
emit-blk = k-∘ k-inr (k-∘ k-op (k-∘ (k-∘ k-lul (k-⊗ k-drop k-id)) (k-∘ (k-⊗ k-op k-id) k-dup)))

-- one round, from the counter `x`, the world answering `tt` to the emit and
-- `x′` to the successor
emit-step : ∀ (x x′ : ℕ) n → Run ε emit-round mone (mi x) n (gives (minr (mi (nrm x′))) n) _
emit-step x x′ n =
  r-∘ (r-∘ (r-∘ (r-∘ r-dup (go-on (r-⊗ (r-op (p-call {y = tt} p-ret)) (go-on (fm-gives r-id)))))
                (go-on (r-∘ (r-⊗ r-drop (go-on (fm-gives r-id))) (go-on r-λ))))
           (go-on (r-op (p-call {y = x′} p-ret))))
      (go-on r-inr)

-- two rounds: 0 → 1 → 2
emit-server : Loop ε emit-round mone (mi 0) 0 2 (mi 2) 0 _
emit-server = l-suc (emit-step 0 1 0) (l-suc (emit-step 1 2 0) l-zero)

-- ★ after both rounds the heap is the one it started with
emit-server-constant : ∀ i → play (trace-of emit-server) (λ _ → 0) i ≡ 0
emit-server-constant = snd′ (word-server emit-server {λ _ → 0} {λ _ → 0}
                         record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }
                         lent₀)
  where snd′ : ∀ {P Q : Set} → P × Q → Q
        snd′ (_ , q) = q

-- the emit server's two rounds touch no cell at all: its events are SigOp calls
emit-events : trace-of emit-server ≡ io emitO 0 tt ∷ io succO 0 1 ∷ io emitO 1 tt ∷ io succO 1 2 ∷ []
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

list-blk : Blk list-round
list-blk = k-∘ k-inr (k-cata k-in)

-- ★ A12: a list node is 3 words (a tag, then the larger alternative: an Int
-- and a pointer), so every list block is named `(3 , serial)`
node-size : szμ ListF ≡ 3
node-size = refl

-- [x], built by a run from the empty heap: the nil in block (3 , 0), the cons
-- in block (3 , 1)
build : LTm ε (Bt int) IntList
build = lIn ∘l linr ∘l (lid ⊗l (lIn ∘l linl)) ∘l ρl⁻

one-list : ℕ → MV IntList
one-list x = mmu (3 , 1) (minr (mpair (mi x) (mmu (3 , 0) (minl mone))))

build-run : Run ε build mone (mi 5) 0 (gives (one-list 5) 2) _
build-run = r-∘ (r-∘ (r-∘ r-ρ⁻ (go-on (r-⊗ r-id (go-on (fm-gives (r-∘ r-inl (go-on r-In))))))) (go-on r-inr)) (go-on r-In)

build-events : trace-of-run build-run ≡ alloc (3 , 0) ∷ alloc (3 , 1) ∷ []
build-events = refl

-- the heap after it, and the precondition there, from the theorems
private
  pre₀ : Pre (λ _ → 0) 0 (mi 5) (λ _ → 0)
  pre₀ = record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }

heap₀ : Heap
heap₀ = play (trace-of-run build-run) (λ _ → 0)

pre-list : Pre heap₀ 2 (one-list 5) (λ _ → 0)
pre-list with exchange build-run pre₀ lent₀
... | (ok , eq) = post build-run pre₀ ok eq

-- [x] again, in fresh blocks: the nil (3 , 2) and the cons (3 , 3)
new-list : ℕ → MV IntList
new-list x = mmu (3 , 3) (minr (mpair (mi x) (mmu (3 , 2) (minl mone))))

-- one round from counter 2: the old cons and nil are freed, a new nil and a
-- new cons are allocated
list-step : ∀ x → Run ε list-round mone (one-list x) 2 (gives (minr (new-list x)) 4) _
list-step x =
  r-∘ (r-cata (m-inr (fm-gives (m-pair m-b (go-on (fm-gives (m-id (r-cata (m-inl (fm-gives m-one)) (go-on r-In))))))))
              (go-on r-In))
      (go-on r-inr)

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
σ-alg X = sg many act X (LF∙ ListF IntList) IntList

σ-emit σ-succ σ-comp : Sg
σ-emit = sg once act One (Bt int) One
σ-succ = sg once act One (Bt int) (Bt int)
σ-comp = sg once act (Ct 2 One ⊗t Ct 3 One) (Bt int) One

Γ₄ Γₚ : Cx
Γ₄ = ε ▸ σ-alg (Bt int) ▸ σ-alg One ▸ σ-emit ▸ σ-succ
Γₚ = Γ₄ ▸ σ-comp

-- the composition's body: ((g , f) , a) ↦ g (f a)
comp-body : LTm Γ₄ ((Ct 2 One ⊗t Ct 3 One) ⊗t Bt int) One
comp-body = lapp (there here) ∘l (lid ⊗l lapp here) ∘l lassoc

defs : Defs Γₚ
defs = ε ▸ bω lIn k-in ▸ bω lIn k-in ▸ b1 (lop emit ∘l lul) (k-∘ k-op k-lul) ▸ b1 (lop succ ∘l lul) (k-∘ k-op k-lul)
     ▸ b1 comp-body (k-∘ k-app (k-∘ (k-⊗ k-id k-app) k-assoc))

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
closure-fold = lul ∘l (drop ⊗l lid) ∘l lend (bsnd (lcata ListF (bapp p0))) ∘l (lclo Idf p0 ⊗l lid)

q0 : Look defs p0 ε (bω lIn k-in)
q0 = lk-there (lk-there (lk-there (lk-there lk-here)))

-- on 7 and [5], from counter 2: the new list is (3 , 3) → (3 , 2)
closure-fold-run : Run defs closure-fold mone (mpair (mi 7) (one-list 5)) 2 (gives (new-list 5) 4) _
closure-fold-run =
  r-∘ (r-∘ (r-∘ (r-⊗ r-clo (go-on (fm-gives r-id)))
                (go-on (r-lend (fm-gives (r-snd (r-cata (m-inr (fm-gives (m-pair m-b (go-on (fm-gives
                                    (m-id (r-cata (m-inl (fm-gives m-one)) (go-on (r-bapp q0 r-In)))))))))
                                       (go-on (r-bapp q0 r-In))))))))
           (go-on (r-⊗ r-drop (go-on (fm-gives r-id)))))
      (go-on r-λ)

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
in-place-run =
  r-cata-reuse (m-inr (fm-gives (m-pair m-b (go-on (fm-gives (m-id (r-cata-reuse (m-inl (fm-gives m-one)) (go-on (fm-gives r-id)))))))))
               (go-on (fm-gives r-id))

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

nested-run : Run ε nested-lend mone (mpair (one-list 5) (mpair (mi 7) mone)) 2 (gives _ 4) _
nested-run = r-lend (fm-gives (r-lend (fm-gives (r-fst (r-snd r-copy)))))

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
  r-cata (m-inr (fm-gives (m-pair m-b (go-on (fm-gives (m-id (r-cata (m-inl (fm-gives m-one)) (go-on (r-case₁ r-id)))))))))
         (go-on (r-case₂ (r-∘ (r-∘ r-ρ (go-on (r-op (p-call {y = tt} p-ret)))) (go-on r-drop))))

-- ★ by evaluation: both cells freed, then the emit
emit-fold-events : trace-of-run emit-fold-run ≡ free (3 , 1) ∷ free (3 , 0) ∷ io emitO 5 tt ∷ []
emit-fold-events = refl

------------------------------------------------------------------------
-- 8. A11: a SigOp INSIDE A CLOSURE.
------------------------------------------------------------------------

emit-closure : LTm Γₚ (Bt int) One
emit-closure = lapp p2 ∘l (lclo Idf p2 ⊗l lid) ∘l lul⁻

q2 : Look defs p2 _ (b1 (lop emit ∘l lul) _)
q2 = lk-there (lk-there lk-here)

emit-closure-run : Run defs emit-closure mone (mi 5) 0 (gives mone 0) _
emit-closure-run =
  r-∘ (r-∘ r-λ⁻ (go-on (r-⊗ r-clo (go-on (fm-gives r-id)))))
      (go-on (r-app q2 (r-∘ r-λ (go-on (r-op (p-call {y = tt} p-ret))))))

-- the emit is the only event
emit-closure-events : trace-of-run emit-closure-run ≡ io emitO 5 tt ∷ []
emit-closure-events = refl

------------------------------------------------------------------------
-- 8½. ★ D405: a COMPOSITION. Label 4's environment is the two closures it
--     composes; its body applies them by their labels, over its own prefix.
--     Three closures, no words, no events: only the SigOps.
------------------------------------------------------------------------

composed : LTm Γₚ (Bt int) One
composed = lapp p4 ∘l ((lclo Idf p4 ∘l (lclo Idf p2 ⊗l lclo Idf p3) ∘l lul⁻) ⊗l lid) ∘l lul⁻

q4 : Look defs p4 _ (b1 comp-body _)
q4 = lk-here

composed-run : Run defs composed mone (mi 5) 0 (gives mone 0) _
composed-run =
  r-∘ (r-∘ r-λ⁻ (go-on (r-⊗ (r-∘ (r-∘ r-λ⁻ (go-on (r-⊗ r-clo (go-on (fm-gives r-clo))))) (go-on r-clo))
                              (go-on (fm-gives r-id)))))
      (go-on (r-app q4 (r-∘ (r-∘ r-α (go-on (r-⊗ r-id (go-on (fm-gives (r-app lk-here (r-∘ r-λ (go-on (r-op (p-call {y = 6} p-ret))))))))))
                            (go-on (r-app (lk-there lk-here) (r-∘ r-λ (go-on (r-op (p-call {y = tt} p-ret)))))))))

composed-events : trace-of-run composed-run ≡ io succO 5 6 ∷ io emitO 6 tt ∷ []
composed-events = refl

-- and it means what it does
composed-sound : RB (block (Lᶜ ⟦ defs ⟧D composed tt 5)) (io-call succO 5 6 ∷ io-call emitO 6 tt ∷ []) (returns tt)
composed-sound = sound composed-run

------------------------------------------------------------------------
-- 9. A11: a HALT with a block live: the exit exception. A nil is built, then
--    the program ends with it still live.
------------------------------------------------------------------------

halting : LTm ε (Bt int) (Zero ⊗t IntList)
halting = (lop exit ⊗l lid) ∘l (lid ⊗l (lIn ∘l linl)) ∘l ρl⁻

halting-run : Run ε halting mone (mi 5) 0 (stop halted) _
halting-run =
  r-∘ (r-∘ r-ρ⁻ (go-on (r-⊗ r-id (go-on (fm-gives (r-∘ r-inl (go-on r-In)))))))
      (go-on (r-⊗ (r-opend p-halt) stopped))

halting-events : trace-of-run halting-run ≡ alloc (3 , 0) ∷ stp exitH 5 ∷ []
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

count-blk : Blk count-round
count-blk = k-case (k-∘ k-inr k-inr) k-inl

count-run : Run ε (liter count-round count-blk) mone (minl mone) 0 (gives mone 0) _
count-run = r-iter (r-case₁ (r-∘ r-inr (go-on r-inr))) (go-on (again (r-iter (r-case₂ r-inl) (go-on done))))

ran-out : Run ε (liter emit-round emit-blk) mone (mi 0) 0 (stop exhausted) _
ran-out = loop-run emit-server r-exh

ran-out-events : trace-of-run ran-out ≡ io emitO 0 tt ∷ io succO 0 1 ∷ io emitO 1 tt ∷ io succO 1 2 ∷ []
ran-out-events = refl

-- ★ and what it did is a prefix of what the server means
ran-out-sound : RB (block (Lᶜ ε (liter emit-round emit-blk) tt 0))
                   (io-call emitO 0 tt ∷ io-call succO 0 1 ∷ io-call emitO 1 tt ∷ io-call succO 1 2 ∷ [])
                   (ended exhausted)
ran-out-sound = sound ran-out

------------------------------------------------------------------------
-- 11. ★ D406: a ν, DEFUNCTIONALISED. The naturals from a seed: the
--     coalgebra is label 0 (the head is the seed, the next seed its
--     successor), the stream is its seed, tagged: ONE word, no cell. Two
--     observations: the two successor calls are the only events.
------------------------------------------------------------------------

NatsF : LF
NatsF = Kb int ⊗f Idf

σ-nats : Sg
σ-nats = sg once act (Bt int) One (LF∙ NatsF (Bt int))

Γν : Cx
Γν = ε ▸ σ-nats

nats-body : LTm ε (Bt int ⊗t One) (Bt int ⊗t Bt int)
nats-body = (lid ⊗l lop succ) ∘l dup ∘l ρl

defsν : Defs Γν
defsν = ε ▸ b1 nats-body (k-∘ (k-⊗ k-id k-op) (k-∘ k-dup k-ρ))

pν : Γν ∋[ 0 ] σ-nats
pν = here

-- a stream of Ints is its seed: one word
stream-words : words (Ct 0 (Bt int)) ≡ 1
stream-words = refl

-- build the stream at a seed, observe it, observe its tail
nats-two : LTm Γν (Bt int) (Bt int ⊗t (Bt int ⊗t Ct 0 (Bt int)))
nats-two = (lid ⊗l lobs NatsF pν) ∘l lobs NatsF pν ∘l lana pν

nats-two-run : Run defsν nats-two mone (mi 5) 0
                 (gives (mpair (mi 5) (mpair (mi 6) (mct (mi 7)))) 0) _
nats-two-run =
  r-∘ (r-∘ r-clo
           (go-on (r-∘ (r-∘ r-ρ⁻ (go-on (r-app lk-here (r-∘ (r-∘ r-ρ (go-on r-dup))
                                                            (go-on (r-⊗ r-id (go-on (fm-gives (r-op (p-call {y = 6} p-ret)))))))))) (go-on r-clo))))
      (go-on (r-⊗ r-id
           (go-on (fm-gives (r-∘ (r-∘ r-ρ⁻ (go-on (r-app lk-here (r-∘ (r-∘ r-ρ (go-on r-dup))
                                                            (go-on (r-⊗ r-id (go-on (fm-gives (r-op (p-call {y = 7} p-ret)))))))))) (go-on r-clo))))))

nats-two-events : trace-of-run nats-two-run ≡ io succO 5 6 ∷ io succO 6 7 ∷ []
nats-two-events = refl

-- and it means what it does
nats-two-sound : RB (block (Lᶜ ⟦ defsν ⟧D nats-two tt 5)) (io-call succO 5 6 ∷ io-call succO 6 7 ∷ []) (returns (5 , (6 , 7)))
nats-two-sound = sound nats-two-run

------------------------------------------------------------------------
-- 12. ★ A13 (D407): a fold's WORK STACK. §2's round again, its fold lowered
--     with a work stack in one temporary block of 4 words: allocated before
--     the fold descends, freed after the list is rebuilt. The temporary is
--     the fold's own: woven into its events, freed before it finishes.
------------------------------------------------------------------------

stack-weave : Weave tmp (free (3 , 1) ∷ free (3 , 0) ∷ alloc (3 , 2) ∷ alloc (3 , 3) ∷ [])
                    (tnew 4 ∷ tdel 4 ∷ [])
                    (tmp (tnew 4) ∷ free (3 , 1) ∷ free (3 , 0) ∷ alloc (3 , 2) ∷ alloc (3 , 3) ∷ tmp (tdel 4) ∷ [])
stack-weave = w-tmp (w-run (w-run (w-run (w-run (w-tmp w-[])))))

stack-step : Run ε list-round mone (one-list 5) 2 (gives (minr (new-list 5)) 4) _
stack-step =
  r-∘ (r-tmp (r-cata (m-inr (fm-gives (m-pair m-b (go-on (fm-gives (m-id (r-cata (m-inl (fm-gives m-one)) (go-on r-In))))))))
                     (go-on r-In))
             stack-weave ((tt , (s≤s z≤n , tt)) , λ k → n∸n≡0 (δn 4 k)))
      (go-on r-inr)

-- by evaluation: the block is born first and freed last, around the cells
stack-events : trace-of-run stack-step
             ≡ tmp (tnew 4) ∷ free (3 , 1) ∷ free (3 , 0) ∷ alloc (3 , 2) ∷ alloc (3 , 3) ∷ tmp (tdel 4) ∷ []
stack-events = refl

-- ★ the theorems: erased, it is §2's round, cell for cell ...
stack-plain : Run ε list-round mone (one-list 5) 2 (gives (minr (new-list 5)) 4) (erase (trace-of-run stack-step))
stack-plain = plain stack-step

stack-erased : erase (trace-of-run stack-step) ≡ trace-of list-server
stack-erased = refl

-- ... its temporaries are all freed ...
stack-temps : TBal (trace-of-run stack-step)
stack-temps = tsound stack-step

-- ... and the memory theorem holds as it was: the cells are the round's
stack-server : Loop ε list-round mone (one-list 5) 2 1 (new-list 5) 4 _
stack-server = l-suc stack-step l-zero

stack-exchange : OK (trace-of stack-server) heap₀
               × (∀ i → play (trace-of stack-server) heap₀ i + cnt (one-list 5) i ≡ heap₀ i + cnt (new-list 5) i)
stack-exchange = loop-exchange stack-server pre-list lent₀

------------------------------------------------------------------------
-- 13. ★ A14: RUNS, FOUND. A world that answers `emit` and `succ` (and, as
--     no world can, never `exit`), and the evaluator: the runs above, which
--     were built rule by rule, come out of `exec` with the same events.
------------------------------------------------------------------------

-- ★ B1.2: it answers an `Int → Int` call with the successor, a call
-- answered by `unit` with it, and nothing else
world-answer : ⊤ → (o : CallOp) → Val.⟦ CallOp.cdom o ⟧ → Data.Maybe.Maybe (Val.⟦ CallOp.ccod o ⟧ × ⊤)
world-answer _ (callOp _ Int _ Int) x = just (suc x , tt)
{-# CATCHALL #-}
world-answer _ (callOp _ _ _ Unit)  x = just (tt , tt)
{-# CATCHALL #-}
world-answer _ _                    _ = nothing

world : World
world = record { WSt = ⊤ ; answer = world-answer }

-- the counter server, two rounds of fuel: the hand-built run of §10
emit-found : Ran.trace (exec world ε 2 (liter emit-round emit-blk) mone (mi 0) 0 tt) ≡ trace-of-run ran-out
emit-found = refl

-- the list server, two rounds: §2's round, then the same on the new list
list-found : Ran.trace (exec world ε 2 (liter list-round list-blk) mone (one-list 5) 2 tt)
           ≡ free (3 , 1) ∷ free (3 , 0) ∷ alloc (3 , 2) ∷ alloc (3 , 3)
           ∷ free (3 , 3) ∷ free (3 , 2) ∷ alloc (3 , 4) ∷ alloc (3 , 5) ∷ []
list-found = refl

-- a composition of closures, through the table: §8½'s events
composed-found : Ran.trace (exec world defs 0 composed mone (mi 5) 0 tt) ≡ io succO 5 6 ∷ io emitO 6 tt ∷ []
composed-found = refl

-- the naturals, observed twice: §11's events and result
nats-found : Ran.out (exec world defsν 0 nats-two mone (mi 5) 0 tt)
           ≡ gives (mpair (mi 5) (mpair (mi 6) (mct (mi 7)))) 0
nats-found = refl

-- ★ A14 step 2: the list server, cut after two rounds — because its fuel ran out
list-cause : Ran.cause (exec world ε 2 (liter list-round list-blk) mone (one-list 5) 2 tt) ≡ out-of-fuel
list-cause = refl

------------------------------------------------------------------------
-- 14. ★ A15: an IR PROGRAM, COMPILED. The counter server written in the
--     IR (`Iter` over an `Int`, from the constant 0), translated by the
--     pass, run by the evaluator: the world sees what §1's hand-written
--     server showed it, and the run means what the IR program means.
------------------------------------------------------------------------

counter-ir : IR ε One One
counter-ir = Iter (inr ∘ snd ∘ ⟨ SigOp emit ∘ snd , SigOp succ ∘ snd ⟩)
                  (i-∘ i-inr (i-∘ i-snd (i-pair (i-∘ i-op i-snd) (i-∘ i-op i-snd)))) ∘ ⟨ terminal , const 0 ⟩

counter-ios : ios (Ran.trace (exec world ε 2 (tr counter-ir) mone mone 0 tt))
            ≡ io-call emitO 0 tt ∷ io-call succO 0 1 ∷ io-call emitO 1 tt ∷ io-call succO 1 2 ∷ []
counter-ios = refl

counter-sound : RB (block (ev ε counter-ir tt))
                   (io-call emitO 0 tt ∷ io-call succO 0 1 ∷ io-call emitO 1 tt ∷ io-call succO 1 2 ∷ [])
                   (ended exhausted)
counter-sound = whole-sound world 2 ε counter-ir tt

------------------------------------------------------------------------
-- 15. ★ A16: THE MACHINE. §8½'s composition, lowered and run: each call is
--     a frame in a heap block of its own (a temporary), entered and left
--     around the body's events; erased, the events are the run's.
------------------------------------------------------------------------

composed-machine : Out.mt (sim composed-run _ (vw mone []ᵉ) refl []ˢ end)
                 ≡ tmp (tnew 1) ∷ tmp (tnew 1) ∷ io succO 5 6 ∷ tmp (tdel 1)
                 ∷ tmp (tnew 1) ∷ io emitO 6 tt ∷ tmp (tdel 1) ∷ tmp (tdel 1) ∷ []
composed-machine = refl

------------------------------------------------------------------------
-- 16. ★ A17: THE ALLOCATOR. Cells 0 and 1 born, 0 dies, 2 is born: 2 takes
--     0's block (the lowest free one), and the region still holds two blocks.
------------------------------------------------------------------------

reuse : Data.Maybe.map (λ p → Al.own p 2 , Al.top p)
          (Al.born 0 Al.empty >>= Al.born 1 >>= Al.died 0 >>= Al.born 2)
      ≡ just (0 , 2)
reuse = refl

------------------------------------------------------------------------
-- 17. ★ A16: A SERVER ON THE MACHINE. §14's counter server, compiled from the
--     IR (its loop reads a lent environment), cut after two rounds: the
--     machine runs at least as far, and what it did up to the cut is legal.
------------------------------------------------------------------------

counter-machine : Σ.fst (machine-legal (Ran.run (exec world ε 2 (tr counter-ir) mone mone 0 tt)) _)
                ≡ io emitO 0 tt ∷ io succO 0 1 ∷ io emitO 1 tt ∷ io succO 1 2 ∷ []
counter-machine = refl

------------------------------------------------------------------------
-- 18. ★ A17: THE ALLOCATOR ON A RUN. §2's list built, then one round: the
--     size-3 class sees two births, two deaths, two births; the new nil and
--     cons take the old blocks, lowest first, and the region stays at two.
------------------------------------------------------------------------

list-ops : AR.ops 3 (trace-of-run build-run ++ trace-of list-server)
         ≡ Al.birth 0 ∷ Al.birth 1 ∷ Al.death 1 ∷ Al.death 0 ∷ Al.birth 2 ∷ Al.birth 3 ∷ []
list-ops = refl

list-blocks : Data.Maybe.map (λ p → Al.own p 2 , Al.own p 3 , Al.top p)
                (Al.born 0 Al.empty >>= Al.born 1 >>= Al.died 1 >>= Al.died 0 >>= Al.born 2 >>= Al.born 3)
            ≡ just (0 , 1 , 2)
list-blocks = refl

------------------------------------------------------------------------
-- 19. ★ D411: ONE REGION FOR EVERY SIZE. §18's events in the region: the
--     list's two blocks take words 0–2 and 3–5, and the round's new nil and
--     cons take them again: six words, the peak of size 3 (two nodes) times
--     three. Then two sizes sharing the region: a 3-word block, a 2-word
--     block above it, the 3-word one freed and taken again by a 3-word cell
--     (never by a 2-word one), and a second 2-word block above the top.
------------------------------------------------------------------------

list-region : Data.Maybe.map (λ r → Rg.wtop r , Rg.addr r 3 0 , Rg.addr r 3 1 , Rg.tops r 3)
                (Rg.grun (AR.gops (trace-of-run build-run ++ trace-of list-server)) Rg.empty)
            ≡ just (6 , 0 , 3 , 2)
list-region = refl

two-sizes : Data.Maybe.map (λ r → Rg.wtop r , Rg.addr r 3 0 , Rg.addr r 2 0 , Rg.addr r 2 1)
              (Rg.grun ((3 , Al.birth 0) ∷ (2 , Al.birth 1) ∷ (3 , Al.death 0) ∷ (3 , Al.birth 2) ∷ (2 , Al.birth 3) ∷ [])
                       Rg.empty)
          ≡ just (7 , 0 , 3 , 5)
two-sizes = refl

------------------------------------------------------------------------
-- 20. ★ D410 amended: NO LEAK AT EVERY STEP, a server's state included.
--     §2's list server as a closed program (the list [5] built, then rounds
--     forever), compiled, run on the machine and cut after two rounds. Where
--     the machine stands, the live cells are exactly those of the values it
--     holds (`held-always`): the list of the last round, nothing of the
--     lists before it.
------------------------------------------------------------------------

list-prog : LTm ε One One
list-prog = lzero ∘l (liter list-round list-blk ∘l (build ∘l lconst 5))

list-on-machine = machine-legal (Ran.run (exec world ε 2 list-prog mone mone 0 tt)) _

-- ★ where the machine stands, the events it made to get there, and the
-- theorem of them: legal, and the live cells exactly those it holds
stands : Σ.Σ Sh λ sh → Σ.Σ (Cfg sh) λ m → Σ.Σ Trace λ mt
         → OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ Owned m i)
stands with list-on-machine
... | (_ , _ , _ , _ , _ , mt , _ , sh , _ , m , _ , st) = (sh , m , mt , held-always st)

-- what it holds there, by evaluation: the last round's nil and cons
list-held : (Owned (Σ.fst (Σ.snd stands)) (3 , 0) ≡ 0) × (Owned (Σ.fst (Σ.snd stands)) (3 , 3) ≡ 0)
          × (Owned (Σ.fst (Σ.snd stands)) (3 , 4) ≡ 1) × (Owned (Σ.fst (Σ.snd stands)) (3 , 5) ≡ 1)
list-held = (refl , refl , refl , refl)

------------------------------------------------------------------------
-- 21. ★ D409 part 3: A FOLD INTO AN ARROW (the Spec's `⊢fold` at a function
--     carrier). Folding the list [7, 5] builds a closure per node, each
--     holding the one built before it: which body runs at each call is
--     decided by the list, at run time, and no label table could name the
--     chain's type. Applied to 0, it emits 7, then 5, counting up; every
--     node and every closure cell is freed, by the run and on the machine.
------------------------------------------------------------------------

-- the carrier: a function on Ints whose call is a finite block
IntFn : LTy
IntFn = Fn once act (Bt int) (Bt int)

-- nil: the identity
fn-nil : LTm ε One IntFn
fn-nil = llam lul k-lul

-- cons x f: emit x, then f on the successor
cons-body : LTm ε ((Bt int ⊗t IntFn) ⊗t Bt int) (Bt int)
cons-body = lev ∘l (lid ⊗l lop succ) ∘l lul ∘l (lop emit ⊗l lid) ∘l lassoc

fn-cons : LTm ε (Bt int ⊗t IntFn) IntFn
fn-cons = llam cons-body (k-∘ k-ev (k-∘ (k-⊗ k-id k-op) (k-∘ k-lul (k-∘ (k-⊗ k-op k-id) k-assoc))))

-- the list [7, 5]
two-list : LTm ε One IntList
two-list = lIn ∘l linr ∘l (lconst 7 ⊗l (build ∘l lconst 5)) ∘l ρl⁻

-- fold it into a function, apply that to 0
fn-prog : LTm ε One One
fn-prog = drop ∘l lev ∘l (lid ⊗l lconst 0) ∘l ρl⁻ ∘l lcata ListF (lcase fn-nil fn-cons) ∘l two-list

fn-run : Ran world ε fn-prog mone mone 0
fn-run = exec world ε 0 fn-prog mone mone 0 tt

-- its events: the list built (three 3-word nodes) and freed by the fold, a
-- closure cell born per layer (nil's, one word: its code word; each cons's,
-- three: code word, Int, the closure before it), then each freed by the
-- indirect call that runs it, outermost first
fn-events : trace-of-run (Ran.run fn-run)
          ≡ alloc (3 , 0) ∷ alloc (3 , 1) ∷ alloc (3 , 2)
          ∷ free (3 , 2) ∷ free (3 , 1) ∷ free (3 , 0)
          ∷ alloc (1 , 3) ∷ alloc (3 , 4) ∷ alloc (3 , 5)
          ∷ free (3 , 5) ∷ io emitO 7 tt ∷ io succO 0 1
          ∷ free (3 , 4) ∷ io emitO 5 tt ∷ io succO 1 2
          ∷ free (1 , 3) ∷ []
fn-events = refl

-- what the world saw
fn-io : ios (Ran.trace fn-run) ≡ io-call emitO 7 tt ∷ io-call succO 0 1 ∷ io-call emitO 5 tt ∷ io-call succO 1 2 ∷ []
fn-io = refl

-- every cell freed: the list's nodes and the closures' cells
fn-empty : ∀ i → play (Ran.trace fn-run) (λ _ → 0) i ≡ 0
fn-empty = Σ.snd (noleak (Ran.run fn-run))

-- and on the machine: the indirect calls, each in a frame, every cell freed
fn-machine = machine-noleak (Ran.run fn-run) _

------------------------------------------------------------------------
-- 22. ★ A ν WHOSE COALGEBRA DATA DECIDES (the Spec's `⊢unfold` takes any
--     coalgebra value). A `case` gives one of two coalgebras, counting up or
--     standing still, and both unfold into the one type `Nu NatsF`: no label
--     names which. The stream from 3, counting, is observed twice (3, then
--     4), then dropped: its cell, its coalgebra's, every one freed.
------------------------------------------------------------------------

NatsCo : LTy
NatsCo = Coalg NatsF (Bt int)

-- s ↦ (s, s + 1), and s ↦ (s, s): many-use closures with nothing in them
count-up stand-still : LTm ε One NatsCo
count-up    = llamω ((lid ⊗l lop succ) ∘l dup) (k-∘ (k-⊗ k-id k-op) k-dup)
stand-still = llamω dup k-dup

-- which one, decided by a sum's tag
pick : LTm ε (One ⊕t One) NatsCo
pick = lcase count-up stand-still

nu-prog : LTm ε One One
nu-prog = drop ∘l lul ∘l (lop emit ⊗l lid) ∘l lul ∘l (lop emit ⊗l lout) ∘l lout
        ∘l lunf ∘l ((pick ∘l linl) ⊗l lconst 3) ∘l ρl⁻

nu-run : Ran world ε nu-prog mone mone 0
nu-run = exec world ε 0 nu-prog mone mone 0 tt

-- what the world saw: each observation runs the coalgebra once
nu-io : ios (Ran.trace nu-run) ≡ io-call succO 3 4 ∷ io-call emitO 3 tt ∷ io-call succO 4 5 ∷ io-call emitO 4 tt ∷ []
nu-io = refl

-- its events: the coalgebra's cell (one word: its code word) and the ν's (two:
-- the coalgebra's pointer and the seed); each observation frees the ν's
-- cell, reads the coalgebra's, copies it for the new seed and drops the old,
-- and makes the new ν; dropping the stream frees its cell and its coalgebra's
nu-events : trace-of-run (Ran.run nu-run)
          ≡ alloc (1 , 0) ∷ alloc (2 , 1)
          ∷ free (2 , 1) ∷ peek (1 , 0) ∷ io succO 3 4 ∷ alloc (1 , 2) ∷ free (1 , 0) ∷ alloc (2 , 3)
          ∷ io emitO 3 tt
          ∷ free (2 , 3) ∷ peek (1 , 2) ∷ io succO 4 5 ∷ alloc (1 , 4) ∷ free (1 , 2) ∷ alloc (2 , 5)
          ∷ io emitO 4 tt
          ∷ free (2 , 5) ∷ free (1 , 4) ∷ []
nu-events = refl

-- every cell freed
nu-empty : ∀ i → play (Ran.trace nu-run) (λ _ → 0) i ≡ 0
nu-empty = Σ.snd (noleak (Ran.run nu-run))

-- and on the machine
nu-machine = machine-noleak (Ran.run nu-run) _

------------------------------------------------------------------------
-- 23. ★ A15 part 2: AN IR PROGRAM WITH AN ARROW AND ν's, COMPILED. The IR's
--     `curry`/`apply` and `Ana`/`Out`/`in-ν`, translated by the pass: a ν
--     built from a layer (Lambek's inverse) around the naturals from 3,
--     observed twice; the head of the second layer kept in a closure that
--     emits it when applied. The world sees the one coalgebra call and the
--     emit; the run means what the IR program means; nothing leaks.
------------------------------------------------------------------------

-- a closure that keeps an Int and emits it when called
emitter : IR ε (Bt int) (Fn many act One One)
emitter = curry act (SigOp emit ∘ fst) (i-∘ i-op i-fst)

-- the naturals from the seed, by an IR unfold that reads nothing
nats-ir : IR ε (One ⊗t Bt int) (Nu NatsF)
nats-ir = Ana NatsF ⟨ snd , SigOp succ ∘ snd ⟩ (i-pair i-snd (i-∘ i-op i-snd))

ho-ir : IR ε One One
ho-ir = apply ∘ ⟨ emitter ∘ fst ∘ Outν NatsF ∘ snd ∘ Outν NatsF ∘ in-ν NatsF
                    ∘ ⟨ const 1 , nats-ir ∘ ⟨ terminal , const 3 ⟩ ⟩
                , terminal ⟩

ho-run : Ran world ε (tr ho-ir) mone mone 0
ho-run = exec world ε 0 (tr ho-ir) mone mone 0 tt

-- the first observation gives the layer as it was built (no call); the
-- second runs the coalgebra once; the closure emits the head it kept
ho-ios : ios (Ran.trace ho-run) ≡ io-call succO 3 4 ∷ io-call emitO 3 tt ∷ []
ho-ios = refl

-- what the world saw is a path through the IR program's meaning
ho-sound : RB (block (ev ε ho-ir tt)) (io-call succO 3 4 ∷ io-call emitO 3 tt ∷ []) (returns tt)
ho-sound = whole-sound world 0 ε ho-ir tt

-- every cell freed: the ν's, their coalgebras', the closure's
ho-empty : ∀ i → play (Ran.trace ho-run) (λ _ → 0) i ≡ 0
ho-empty = Σ.snd (noleak (Ran.run ho-run))

-- (On the machine, `machine-noleak` covers this run as every run; its
-- instance is not spelled out here: normalising the lowered run of the pass's
-- faithful translation exceeds the type-checker's 4.8 GB heap.)

------------------------------------------------------------------------
-- 24. ★ A15 part 2: AN IR PROGRAM OF DEFINITIONS (the Spec's `Program`: each
--     calls only earlier ones). `bump` is the successor, `show` emits the
--     successor of its argument by calling `bump`; main calls `bump` on 9,
--     then `show`. Each `Call` is the core's direct call of a label.
------------------------------------------------------------------------

Defs₂ : Cx
Defs₂ = ε ▸ sg once act One (Bt int) (Bt int) ▸ sg once act One (Bt int) One

calls-P : Prog Defs₂
calls-P = (ε ▹ SigOp succ ∣ i-op) ▹ (SigOp emit ∘ Call here) ∣ i-∘ i-op i-call

calls-main : IR Defs₂ One One
calls-main = Call here ∘ Call (there here) ∘ const 9

calls-run : Ran world (trP calls-P) (tr calls-main) mone mone 0
calls-run = exec world (trP calls-P) 0 (tr calls-main) mone mone 0 tt

calls-ios : ios (Ran.trace calls-run) ≡ io-call succO 9 10 ∷ io-call succO 10 11 ∷ io-call emitO 11 tt ∷ []
calls-ios = refl

-- what the world saw is a path through the program's meaning
calls-sound : RB (block (ev ⟦ calls-P ⟧P calls-main tt))
                 (io-call succO 9 10 ∷ io-call succO 10 11 ∷ io-call emitO 11 tt ∷ []) (returns tt)
calls-sound = whole-sound world 0 calls-P calls-main tt

calls-empty : ∀ i → play (Ran.trace calls-run) (λ _ → 0) i ≡ 0
calls-empty = Σ.snd (noleak (Ran.run calls-run))

-- and on the machine: each call a frame
calls-machine = machine-noleak (Ran.run calls-run) _
