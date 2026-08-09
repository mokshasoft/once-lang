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

open import Data.Nat using (ℕ; suc; _+_; _*_)
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
   cata-trace-branching; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize;
   -- D099 / C1: the three shared blocks of the called-algebra shape.
   cata-body; cata-call-setup; cata-call; cata-trace-const;
   cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; fsize)

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
-- D099 / C1: three SHARED block witnesses, because the algebra is now emitted
-- once as a called body and every strategy uses the same three pieces. All of
-- `c-jmp`/`c-thunk`/`c-ret`/`c-label`/`instr-call-closure`/`instr-alloc-heap`/
-- `instr-load-code-addr`/`instr-save-closure-reg` are EMITTABLE (the fence this
-- walk enforces is the emitter one, not the semantic `FrameFreeI` — the call
-- and the markers DO move the frame, which is exactly why they are ⊥ there and
-- ⊤ here). `curry` already relies on the same split.
cata-body-ff : ∀ b e bb at → FrameFreeTrace at → FrameFreeTrace (cata-body b e bb at)
cata-body-ff b e bb at ff = tt ∷ tt ∷ ++⁺ ff (tt ∷ tt ∷ [])

cata-setup-ff : ∀ cl bl → FrameFreeTrace (cata-call-setup cl bl)
cata-setup-ff cl bl = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

cata-call-ff : ∀ cl k → FrameFreeTrace (cata-call cl k)
cata-call-ff cl k = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

-- The nat skeleton's three pieces, unchanged by C1 — named so the strategy
-- witnesses below are a composition rather than one long count.
nat-I₁-ff : ∀ n1 l1 → FrameFreeTrace (cata-nat-I₁ n1 l1)
nat-I₁-ff n1 l1 =
  tt ∷ tt ∷
  ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
      (tt ∷ tt ∷ tt ∷
       ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ []))

nat-I₂-ff : ∀ n1 l1 → FrameFreeTrace (cata-nat-I₂ n1 l1)
nat-I₂-ff n1 l1 =
  tt ∷ tt ∷ tt ∷ ++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) (tt ∷ [])

nat-I₃-ff : ∀ l1 → FrameFreeTrace (cata-nat-I₃ l1)
nat-I₃-ff l1 = tt ∷ tt ∷ tt ∷ []

cata-nat-ff : ∀ bb n1 l1 at → FrameFreeTrace at
            → FrameFreeTrace (cata-trace-of (cata-trace-nat bb n1 l1 at))
-- Arguments spelled out rather than `_`: the composition has to pin where each
-- block ends, and `at` is a variable, so the splits cannot be inferred.
cata-nat-ff bb n1 l1 at ff =
  ++⁺ (cata-body-ff bodyL endL bb at ff)
      (++⁺ (cata-setup-ff cl bodyL)
           (++⁺ (nat-I₁-ff n1 l1)
                (++⁺ (cata-call-ff cl k)
                     (++⁺ (nat-I₂-ff n1 l1)
                          (++⁺ (cata-call-ff cl k) (nat-I₃-ff l1))))))
  where
    bodyL = suc (suc (suc (suc (suc (suc l1)))))
    endL  = suc (suc (suc (suc (suc (suc (suc l1))))))
    cl    = suc (suc n1)
    k     = suc (suc (suc n1))

cata-const-ff : ∀ bb n1 l1 at → FrameFreeTrace at
              → FrameFreeTrace (cata-trace-of (cata-trace-const bb n1 l1 at))
cata-const-ff bb n1 l1 at ff =
  ++⁺ (cata-body-ff l1 (l1 + 1) bb at ff)
      (++⁺ (cata-setup-ff n1 l1) (cata-call-ff n1 (n1 + 1)))

cata-linear-ff : ∀ bb n1 l1 at → FrameFreeTrace at
               → FrameFreeTrace (cata-trace-of (cata-trace-linear bb n1 l1 at))
cata-linear-ff bb n1 l1 at ff =
  ++⁺ (cata-body-ff (l1 + 4) (l1 + 5) bb at ff)
      (++⁺ (cata-setup-ff (n1 + 6) (l1 + 4))
           (++⁺ lin-I₁
                (++⁺ (cata-call-ff (n1 + 6) (n1 + 7))
                     (++⁺ lin-I₂ (++⁺ (cata-call-ff (n1 + 6) (n1 + 7)) lin-I₃)))))
  where
    -- 26: the old witness split as `++⁺ (25 tt) (tt ∷ …)` right before `at`.
    lin-I₁ : FrameFreeTrace _
    lin-I₁ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₂ : FrameFreeTrace _
    lin-I₂ = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
             tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
    lin-I₃ : FrameFreeTrace _
    lin-I₃ = tt ∷ tt ∷ tt ∷ []

cata-branching-ff : ∀ F bb n1 l1 at → FrameFreeTrace at
                  → FrameFreeTrace (cata-trace-of (cata-trace-branching F bb n1 l1 at))
-- Tier 2 splices once, so it has ONE call site.
cata-branching-ff F bb n1 l1 at ff =
  ++⁺ (cata-body-ff bodyL (bodyL + 1) bb at ff)
      (++⁺ (cata-setup-ff cl bodyL)
           (++⁺ I₁ (++⁺ (cata-call-ff cl (cl + 1)) I₂)))
  where
    bodyL = l1 + 4 + lsize F + lsize F
    cl    = n1 + 7 + (4 * fsize F) + 4
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

cata-dispatch-ff : ∀ st bb n1 l1 at → FrameFreeTrace at
                 → FrameFreeTrace (cata-trace-of (cata-dispatch st bb n1 l1 at))
cata-dispatch-ff strat-const         bb n1 l1 at ff = cata-const-ff bb n1 l1 at ff
cata-dispatch-ff strat-nat           bb n1 l1 at ff = cata-nat-ff bb n1 l1 at ff
cata-dispatch-ff strat-linear        bb n1 l1 at ff = cata-linear-ff bb n1 l1 at ff
cata-dispatch-ff (strat-branching F) bb n1 l1 at ff = cata-branching-ff F bb n1 l1 at ff

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
-- C1: the algebra is generated at frontier 0 (its own frame), so its IH is
-- taken there rather than at the caller's `n`.
frame-free-trace' (Cata {F} _ alg) hm n l =
  cata-dispatch-ff (cata-strategy ⌈ F ⌉F) _ _ _ _ (frame-free-trace' alg hm 0 l)
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
