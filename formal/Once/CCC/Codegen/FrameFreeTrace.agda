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
-- step at an `instr-case-on-tag` runs a whole NESTED trace — and the frame-slots
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

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.FrameFreeTrace (o : CanonicalName) where

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
  (FrameFreeI; FrameFreeT; frame-free-nest; EmittableI)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.ShapeTable using (HeapModed; IsHeap)
open import Once.CCC.Codegen.IRToTrace o using
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
-- Plan 0.63 (2b): the walk proves the EMITTER FENCE (`EmittableI`), not the
-- semantic frame-freeness — closure bodies are inline now, so an emitted trace
-- genuinely DOES contain the two frame-moving markers. Every leaf below is
-- still `tt`: the fence and the old predicate differ only at those two
-- constructors.
FrameFreeTrace : AbstractTrace → Set
FrameFreeTrace = All EmittableI

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
cata-nat-ff : ∀ n1 l1 at₁ at₂ → FrameFreeTrace at₁ → FrameFreeTrace at₂
            → FrameFreeTrace (cata-trace-of (cata-trace-nat n1 l1 at₁ at₂))
-- Plan 0.63 (iii): the skeleton is `I₁ ++ at ++ (I₂ ++ at ++ I₃)` now, so the
-- walk follows that alternation directly.
cata-nat-ff n1 l1 at₁ at₂ ff ff₂ =
  tt ∷ tt ∷
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])  -- descend
      (tt ∷ tt ∷ tt ∷
       ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])       -- layer 0
           (tt ∷ ++⁺ ff                                                  -- at₁
             (tt ∷ tt ∷ tt ∷
              ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) -- layer 1
                  (tt ∷ ++⁺ ff₂ (tt ∷ tt ∷ tt ∷ [])))))                  -- at₂ ++ I₃

cata-linear-ff : ∀ n1 l1 at₁ at₂ → FrameFreeTrace at₁ → FrameFreeTrace at₂
               → FrameFreeTrace (cata-trace-of (cata-trace-linear n1 l1 at₁ at₂))
cata-linear-ff n1 l1 at₁ at₂ ff ff₂ = ++⁺ descend (tt ∷ ++⁺ ff ascend)
  where
    descend : FrameFreeTrace _
    descend = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
              tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    ascend : FrameFreeTrace _
    ascend = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             ++⁺ ff₂ (tt ∷ tt ∷ tt ∷ [])

cata-branching-ff : ∀ F n1 l1 at₁ at₂ → FrameFreeTrace at₁ → FrameFreeTrace at₂
                  → FrameFreeTrace (cata-trace-of (cata-trace-branching F n1 l1 at₁ at₂))
-- Plan 0.63 (iii): `I₁ ++ at ++ I₂` — I₁ absorbs init, flatten and the fold's
-- prefix; I₂ is the fold's tail plus the final read.
cata-branching-ff F n1 l1 at₁ at₂ ff ff₂ =
  ++⁺ I₁ (++⁺ ff I₂)
  where
    I₁ : FrameFreeTrace _
    I₁ = ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-ff n1 (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (push2-ff (suc n1) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (visit-walk-ff n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4))
             (++⁺ (tt ∷ tt ∷ [])
             (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
             (++⁺ (rebuild-walk-ff (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) ((l1 + 4) + lsize F))
                  (tt ∷ [])))))))))
    I₂ : FrameFreeTrace _
    I₂ = ++⁺ (push2-ff (n1 + 2) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ []) (tt ∷ tt ∷ tt ∷ []))

cata-dispatch-ff : ∀ st n1 l1 at₁ at₂ → FrameFreeTrace at₁ → FrameFreeTrace at₂
                 → FrameFreeTrace (cata-trace-of (cata-dispatch st n1 l1 at₁ at₂))
cata-dispatch-ff strat-const         n1 l1 at₁ at₂ ff ff₂ = ff
cata-dispatch-ff strat-nat           n1 l1 at₁ at₂ ff ff₂ = cata-nat-ff n1 l1 at₁ at₂ ff ff₂
cata-dispatch-ff strat-linear        n1 l1 at₁ at₂ ff ff₂ = cata-linear-ff n1 l1 at₁ at₂ ff ff₂
cata-dispatch-ff (strat-branching F) n1 l1 at₁ at₂ ff ff₂ = cata-branching-ff F n1 l1 at₁ at₂ ff ff₂

------------------------------------------------------------------------
-- THE THEOREM, over arbitrary frontier `n` / label counter `l`.
------------------------------------------------------------------------
-- Plan 0.63 step 2b: CONDITIONAL ON `HeapModed`. `lea-slot` joined
-- `FrameFreeI`'s ⊥ set (it is the sole creator of a stack pointer), and it
-- IS emitted — by the four STACK-mode clauses below, whose `IsHeap Stack`
-- premise is `⊥`. So the theorem is exactly as strong as it can be: a
-- heap-moded trace contains no frame op and no `lea-slot`.
frame-free-trace' : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) (n l : ℕ)
                  → FrameFreeTrace (trace-of (ir-to-trace' n l ir))
frame-free-trace' id       hm n l = tt ∷ []
frame-free-trace' fst      hm n l = tt ∷ []
frame-free-trace' snd      hm n l = tt ∷ []
frame-free-trace' terminal hm n l = []
frame-free-trace' initial  hm n l = tt ∷ []
frame-free-trace' (g ∘ f)  (hf , hg) n l =
  ++⁺ (frame-free-trace' f hf _ _) (tt ∷ frame-free-trace' g hg _ _)
frame-free-trace' (⟨ f , g ⟩ Stack) (() , _) n l
frame-free-trace' (⟨ f , g ⟩ Heap) (_ , hf , hg) n l =
  tt ∷ tt ∷
  ++⁺ (frame-free-trace' f hf _ _)
      (tt ∷ tt ∷
       ++⁺ (frame-free-trace' g hg _ _)
           (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))
frame-free-trace' (curry b Stack) (() , _) n l
-- THE BODY IS INLINE (the flip): the walk recurses into it right here, which
-- is the one-line change inlining AT THE CLAUSE buys — a strengthened "main
-- AND every body" induction would have been the alternative. The markers are
-- `tt` because the fence admits them; the body's own instructions come from
-- the same recursive `ir-to-trace'`.
frame-free-trace' (curry b Heap)  (_ , hb) n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (frame-free-trace' b hb _ _) (tt ∷ tt ∷ [])
frame-free-trace' apply hm n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (inl Stack) () n l
frame-free-trace' (inr Stack) () n l
frame-free-trace' (inl Heap)  hm n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (inr Heap)  hm n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
-- case is FLAT CONTROL since item 6 — plain splices, no depth obligation.
frame-free-trace' (case f g) (hf , hg) n l =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (frame-free-trace' g hg _ _)
           (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
                (++⁺ (frame-free-trace' f hf _ _) (tt ∷ []))))
frame-free-trace' (In _ _)  hm n l = tt ∷ []
frame-free-trace' (out-μ _) hm n l = tt ∷ []
-- D099: two independently-generated algebra copies ⇒ two recursions
frame-free-trace' (Cata {F} _ alg) hm n l =
  cata-dispatch-ff (cata-strategy ⌈ F ⌉F) _ _ _ _
    (frame-free-trace' alg hm n l) (frame-free-trace' alg hm _ _)
frame-free-trace' (Para _ _)     hm n l = []
frame-free-trace' (Out _)        hm n l = tt ∷ []
frame-free-trace' (in-ν _ _)     hm n l = []
frame-free-trace' (Ana _ _)      hm n l = []
frame-free-trace' (Hylo _ _ _ _) hm n l = []
frame-free-trace' (Fuse _ _ _ _) hm n l = []
frame-free-trace' (free-heap _)  hm n l = tt ∷ []
frame-free-trace' (SigOp _)      hm n l = tt ∷ []
frame-free-trace' (const fits-int _)   hm n l = tt ∷ []
frame-free-trace' (const fits-float _) hm n l = tt ∷ []

------------------------------------------------------------------------
-- Corollaries over the public entry points, and the form the flat↔x86-64
-- correspondence consumes: a FETCH into an emitted program never yields a
-- frame op.
------------------------------------------------------------------------
frame-free-at-frontier : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) (n : ℕ)
                       → FrameFreeTrace (ir-to-trace-at-frontier n ir)
frame-free-at-frontier ir hm n with ir-to-trace' n 0 ir | frame-free-trace' ir hm n 0
... | _ , _ , _ , _ | ff = ff

ir-to-trace-frame-free : ∀ {A B} (ir : IR A B) (hm : HeapModed ir)
                       → FrameFreeTrace (ir-to-trace ir)
ir-to-trace-frame-free ir hm = frame-free-at-frontier ir hm 0

-- (`ir-to-trace-frame-free-deep` is GONE with the flip: `FrameFreeT` is the
-- SEMANTIC predicate and an emitted trace no longer satisfies it — the markers
-- move the frame. Its one consumer, `no-nested-of-all`, needs only the fence,
-- and takes it directly.)

module _ {FS : FrameSemantics} where
  open FlatMachine {FS}

  fetch-frame-free : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) {k i}
                   → fetch (ir-to-trace ir) k ≡ just i → EmittableI i
  fetch-frame-free ir hm = fetch-All (ir-to-trace-frame-free ir hm)
