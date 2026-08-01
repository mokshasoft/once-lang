-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.FrameFreeTrace   (Plan 0.54 rung D, item 2)
--
-- THE FRAME OPS HAVE NO PRODUCER. No trace `ir-to-trace` emits contains
-- `instr-alloc-stack` / `instr-dealloc-stack` / `instr-push-frame` /
-- `instr-pop-frame` — not in the main trace, and not in any nested
-- (`instr-case-on-tag`) branch either. Each per-arch backend brackets a trace
-- with `subq $budget*8, %rsp` / `addq` of its own accord (`ir-stack-budget`), so
-- those four abstract instructions have no producer in the live codegen at all;
-- they survive only in the legacy IR-WF layer.
--
-- THIS DISCHARGES `ConcFlatSim.frame-op-absurd`, which is what the flat↔x86-64
-- correspondence asks of the emitter: every residual there is conditioned on a
-- run context containing `Emitted prog` (`prog ≡ ir-to-trace ir`), so a fetched
-- frame op at such a site is ABSURD. That deleted the eleven residuals which
-- used to condition the four frame dispatch clauses (`alloc-stack-entry`,
-- `alloc-stack-fresh-{abs,x86}`, `stack-room`, `dealloc-stack-{full,restores}`,
-- `frame-room`, `pop-frame-{empty,saved,restores}`, `pop-room`).
--
-- DEPTH: the predicate (`Once.CCC.Machine.FrameFree`) is deep, because one flat
-- step at an `instr-case-on-tag` runs a whole NESTED trace — and the stackSlot
-- invariance the slot residuals need must survive that step. `curry` bodies are
-- a separate matter: they land in the bodies list, not in this trace, so the
-- `curry` clauses stay one-liners.
--
-- Shape: the induction of `Once.CCC.Codegen.StraightTrace` (`All P` over
-- `trace-of (ir-to-trace' n l ir)`, `++⁺` at every splice). Unlike that one,
-- `Cata` is NOT excluded — the cata codegen emits no frame op either, in any of
-- its three strategies or in the compile-time functor walks `visit-walk` /
-- `rebuild-walk` — so this theorem is unconditional in `ir`.
------------------------------------------------------------------------

module Once.CCC.Codegen.FrameFreeTrace where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using
  (AbstractInstr; AbstractTrace; load-indirect-suc; mov-to-input)
open import Once.CCC.Machine.FrameFree using
  (FrameFreeI; FrameFreeT; frame-free-nest)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.IRToTrace using
  (ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier;
   CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
   cata-strategy; cata-dispatch; cata-trace-nat; cata-trace-linear;
   cata-trace-branching; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize)

-- third projection of `ir-to-trace'`'s 4-tuple / of `cata-dispatch`'s 3-tuple
-- (record patterns, so they reduce under eta — unlike IRToTrace's own
-- `private proj-trace`).
trace-of : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → AbstractTrace
trace-of (_ , _ , t , _) = t

cata-trace-of : ℕ × ℕ × AbstractTrace → AbstractTrace
cata-trace-of (_ , _ , t) = t

-- This induction carries the `All` form: it is a DATATYPE, so `++⁺` unifies at
-- every splice `t₁ ++ t₂` (the equivalent `FrameFreeT` is a recursive product,
-- under which a spliced goal has already lost its `++` structure).
-- `frame-free-nest` converts, at the nested-branch obligations only.
FrameFreeTrace : AbstractTrace → Set
FrameFreeTrace = All FrameFreeI

------------------------------------------------------------------------
-- The heap-linked-stack bricks the cata codegen is built from.
------------------------------------------------------------------------
push2-ff : ∀ topSlot tv tb → FrameFreeTrace (push2 topSlot tv tb)
push2-ff topSlot tv tb = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

pop2-ff : ∀ topSlot → FrameFreeTrace (pop2 topSlot)
pop2-ff topSlot = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

wrap-sum-ff : ∀ tag s → FrameFreeTrace (wrap-sum tag s)
wrap-sum-ff tag s = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

------------------------------------------------------------------------
-- The compile-time functor walks (Tier 2). A sum node's dispatch is ONE
-- `instr-case-on-tag`, whose two branch bodies are the walk's own recursive
-- calls — this is where the predicate's DEPTH earns its keep.
------------------------------------------------------------------------
visit-walk-ff : ∀ todoSlot tv tb F s lb → FrameFreeTrace (visit-walk todoSlot tv tb F s lb)
visit-walk-ff todoSlot tv tb (K _)   s lb = []
visit-walk-ff todoSlot tv tb Id      s lb = tt ∷ push2-ff todoSlot tv tb
visit-walk-ff todoSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (visit-walk-ff todoSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (visit-walk-ff todoSlot tv tb F (s + 4) (suc (suc lb)))
                     (tt ∷ []))))
visit-walk-ff todoSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (++⁺ (visit-walk-ff todoSlot tv tb G (s + 4) (lb + lsize F))
           (++⁺ (tt ∷ tt ∷ tt ∷ [])
                (visit-walk-ff todoSlot tv tb F (s + 4) lb)))

rebuild-walk-ff : ∀ valSlot tv tb F s lb → FrameFreeTrace (rebuild-walk valSlot tv tb F s lb)
rebuild-walk-ff valSlot tv tb (K _)   s lb = tt ∷ []
rebuild-walk-ff valSlot tv tb Id      s lb = pop2-ff valSlot
rebuild-walk-ff valSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (rebuild-walk-ff valSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
           (++⁺ (wrap-sum-ff 1 s)
                (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                     (++⁺ (rebuild-walk-ff valSlot tv tb F (s + 4) (suc (suc lb)))
                          (++⁺ (wrap-sum-ff 0 s) (tt ∷ []))))))
rebuild-walk-ff valSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
      (++⁺ (rebuild-walk-ff valSlot tv tb F (s + 4) lb)
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (rebuild-walk-ff valSlot tv tb G (s + 4) (lb + lsize F))
                     (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))))

------------------------------------------------------------------------
-- The three cata strategies: each splices the algebra trace `at` (whose
-- freeness is the caller's IH) into a fixed frame-op-free skeleton.
------------------------------------------------------------------------
cata-nat-ff : ∀ n1 l1 at → FrameFreeTrace at
            → FrameFreeTrace (cata-trace-of (cata-trace-nat n1 l1 at))
cata-nat-ff n1 l1 at ff =
  tt ∷ tt ∷
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])  -- descend-flat
      (tt ∷ tt ∷ tt ∷
       ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])       -- build-layer 0
           (tt ∷ ++⁺ ff
             -- ascend-flat: two loop instrs, ascend-body, then jmp/label
             (tt ∷ tt ∷
              ++⁺ (tt ∷ ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
                            (tt ∷ ++⁺ ff (tt ∷ [])))
                  (tt ∷ tt ∷ []))))

cata-linear-ff : ∀ n1 l1 at → FrameFreeTrace at
               → FrameFreeTrace (cata-trace-of (cata-trace-linear n1 l1 at))
cata-linear-ff n1 l1 at ff = ++⁺ descend (tt ∷ ++⁺ ff ascend)
  where
    descend : FrameFreeTrace _
    descend = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
              tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    ascend : FrameFreeTrace _
    ascend = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             ++⁺ ff (tt ∷ tt ∷ tt ∷ [])

cata-branching-ff : ∀ F n1 l1 at → FrameFreeTrace at
                  → FrameFreeTrace (cata-trace-of (cata-trace-branching F n1 l1 at))
cata-branching-ff F n1 l1 at ff =
  ++⁺ init (++⁺ flatten (++⁺ fold (tt ∷ tt ∷ tt ∷ [])))
  where
    init : FrameFreeTrace _
    init = ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
               (push2-ff n1 (n1 + 4) (n1 + 5))
    flatten : FrameFreeTrace _
    flatten = ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
                  (++⁺ (push2-ff (suc n1) (n1 + 4) (n1 + 5))
                       (++⁺ (tt ∷ tt ∷ [])
                            (++⁺ (visit-walk-ff n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4))
                                 (tt ∷ tt ∷ []))))
    fold : FrameFreeTrace _
    fold = ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
               (++⁺ (rebuild-walk-ff (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) ((l1 + 4) + lsize F))
                    (++⁺ (tt ∷ [])
                         (++⁺ ff (++⁺ (push2-ff (n1 + 2) (n1 + 4) (n1 + 5))
                                      (tt ∷ tt ∷ [])))))

cata-dispatch-ff : ∀ st n1 l1 at → FrameFreeTrace at
                 → FrameFreeTrace (cata-trace-of (cata-dispatch st n1 l1 at))
cata-dispatch-ff strat-const         n1 l1 at ff = ff
cata-dispatch-ff strat-nat           n1 l1 at ff = cata-nat-ff n1 l1 at ff
cata-dispatch-ff strat-linear        n1 l1 at ff = cata-linear-ff n1 l1 at ff
cata-dispatch-ff (strat-branching F) n1 l1 at ff = cata-branching-ff F n1 l1 at ff

------------------------------------------------------------------------
-- THE THEOREM, over arbitrary frontier `n` / label counter `l`.
------------------------------------------------------------------------
frame-free-trace' : ∀ {A B} (ir : IR A B) (n l : ℕ)
                  → FrameFreeTrace (trace-of (ir-to-trace' n l ir))
frame-free-trace' id       n l = tt ∷ []
frame-free-trace' fst      n l = tt ∷ []
frame-free-trace' snd      n l = tt ∷ []
frame-free-trace' terminal n l = []
frame-free-trace' initial  n l = tt ∷ []
frame-free-trace' (g ∘ f)  n l =
  ++⁺ (frame-free-trace' f _ _) (tt ∷ frame-free-trace' g _ _)
frame-free-trace' (⟨ f , g ⟩ Stack) n l =
  tt ∷ tt ∷
  ++⁺ (frame-free-trace' f _ _)
      (tt ∷ tt ∷ ++⁺ (frame-free-trace' g _ _) (tt ∷ tt ∷ []))
frame-free-trace' (⟨ f , g ⟩ Heap) n l =
  tt ∷ tt ∷
  ++⁺ (frame-free-trace' f _ _)
      (tt ∷ tt ∷
       ++⁺ (frame-free-trace' g _ _)
           (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))
frame-free-trace' (curry b Stack) n l = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (curry b Heap)  n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' apply n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (inl Stack) n l = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (inr Stack) n l = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (inl Heap)  n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (inr Heap)  n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
-- case is FLAT CONTROL since item 6 — plain splices, no depth obligation.
frame-free-trace' (case f g) n l =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (frame-free-trace' g _ _)
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (frame-free-trace' f _ _) (tt ∷ []))))
frame-free-trace' (In _ _)  n l = tt ∷ []
frame-free-trace' (out-μ _) n l = tt ∷ []
frame-free-trace' (Cata {F} _ alg) n l =
  cata-dispatch-ff (cata-strategy ⌈ F ⌉F) _ _ _ (frame-free-trace' alg n l)
frame-free-trace' (Para _ _)     n l = []
frame-free-trace' (Out _)        n l = tt ∷ []
frame-free-trace' (in-ν _ _)     n l = []
frame-free-trace' (Ana _ _)      n l = []
frame-free-trace' (Hylo _ _ _ _) n l = []
frame-free-trace' (Fuse _ _ _ _) n l = []
frame-free-trace' (free-heap _)  n l = tt ∷ []
frame-free-trace' (SigOp _)      n l = tt ∷ []
frame-free-trace' (const fits-int _)   n l = tt ∷ []
frame-free-trace' (const fits-float _) n l = tt ∷ []

------------------------------------------------------------------------
-- Corollaries over the public entry points, and the form the flat↔x86-64
-- correspondence consumes: a FETCH into an emitted program never yields a
-- frame op.
------------------------------------------------------------------------
frame-free-at-frontier : ∀ {A B} (ir : IR A B) (n : ℕ)
                       → FrameFreeTrace (ir-to-trace-at-frontier n ir)
frame-free-at-frontier ir n with ir-to-trace' n 0 ir | frame-free-trace' ir n 0
... | _ , _ , _ , _ | ff = ff

ir-to-trace-frame-free : ∀ {A B} (ir : IR A B) → FrameFreeTrace (ir-to-trace ir)
ir-to-trace-frame-free ir = frame-free-at-frontier ir 0

-- …and as the DEEP trace predicate, for the nested obligations downstream.
ir-to-trace-frame-free-deep : ∀ {A B} (ir : IR A B) → FrameFreeT (ir-to-trace ir)
ir-to-trace-frame-free-deep ir = frame-free-nest (ir-to-trace-frame-free ir)

module _ {FS : FrameSemantics} where
  open FlatMachine {FS}

  fetch-frame-free : ∀ {A B} (ir : IR A B) {k i}
                   → fetch (ir-to-trace ir) k ≡ just i → FrameFreeI i
  fetch-frame-free ir = fetch-All (ir-to-trace-frame-free ir)
