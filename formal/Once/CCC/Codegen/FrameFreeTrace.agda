-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.FrameFreeTrace   (Plan 0.54 rung D, item 2)
--
-- THE FRAME OPS HAVE NO PRODUCER. No trace `ir-to-trace` emits contains
-- `instr-alloc-stack` / `instr-dealloc-stack` / `instr-push-frame` /
-- `instr-pop-frame` — not in the main trace, and not in any block. Each per-arch backend brackets a trace
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
-- `curry` bodies land in the bodies list, not in this trace, so the `curry`
-- clauses stay one-liners. (The predicate was DEEP while the nested
-- `instr-case-on-tag` existed; plan 0.135 retired it.)
--
-- Shape: the induction of `Once.CCC.Codegen.StraightTrace` (`All P` over
-- `trace-of (ir-to-trace' n l ir)`, `++⁺` at every splice). Unlike that one,
-- `Cata` is NOT excluded — the cata codegen emits no frame op either, in any of
-- its three strategies or in the compile-time functor walks `visit-walk` /
-- `rebuild-walk` — so this theorem is unconditional in `ir`.
--
-- plan 0.123 B.4 α: the flat layout's code (`FlatLayout.put`/`get`, of a
-- length that depends on the type) is discharged by `put-All`/`get-All`: it is
-- made of slot restores and loads and the offset forms, all emittable.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.FrameFreeTrace (o : CanonicalName) where

open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Once.CCC.Label using (ℓ)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial; curry; apply; In; out-μ; Cata; Out; in-ν; Ana; Iter; SigOp; Call; const)
open import Once.IRTy using (IRTy; IRFunctor; ⟦_⟧TI; ν-type; fits-int; fits-float; ⌈_⌉F; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod) renaming (_+_ to _+ᵀ_)
open import Once.Spec.Type using (Fun; K; Id; _⊕_; _⊗_)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (blocks-layout; link-top)
open import Once.CCC.Machine.SMCore using (LabelId; AbstractTrace)
open import Once.CCC.Machine.FrameFree using
  (EmittableI)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.HeapModed using (HeapModed)
open import Once.CCC.Codegen.FlatLayout
  using (Kind; word; flat; kind; put; put-k; get; get-k; fill; put-All; put-k-All; get-All; get-k-All; fill-All; lkind; lsz)
open import Once.CCC.Codegen.Size using (size)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.IRToTrace o using
  (sigop-code; ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier; ir-to-trace-lab; ir-to-unit; strat-const; strat-box; strat-branching; cata-strategy; cata-dispatch; cata-trace-branching; cata-trace-box; cata-call-box; in-trace; out-trace; push2; pop2; wrap-sum; visit-walk; rebuild-walk; lsize; cata-body; cata-call-setup; cata-call; cata-call-from; cata-trace-const; fsize; resuspend-layer; env-entry; env-prologue; inj-trace)

-- third projection of `ir-to-trace'`'s 4-tuple / of `cata-dispatch`'s 3-tuple
-- (record patterns, so they reduce under eta — unlike IRToTrace's own
-- `private proj-trace`).
trace-of : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → AbstractTrace
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
-- plan 0.123 B.4 α: the layout code.
------------------------------------------------------------------------
put-ff : ∀ X s b o′ → FrameFreeTrace (put X s b o′)
put-ff X s b o′ = put-All {EmittableI} X s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

put-k-ff : ∀ kd n s b o′ → FrameFreeTrace (put-k kd n s b o′)
put-k-ff kd n s b o′ = put-k-All {EmittableI} kd n s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

get-ff : ∀ X k → FrameFreeTrace (get X k)
get-ff X k = get-All {EmittableI} X k (λ _ → tt) (λ _ → tt) tt

get-k-ff : ∀ kd n k → FrameFreeTrace (get-k kd n k)
get-k-ff kd n k = get-k-All {EmittableI} kd n k (λ _ → tt) (λ _ → tt) tt

fill-ff : ∀ from c → FrameFreeTrace (fill from c)
fill-ff from c = fill-All {EmittableI} from c tt (λ _ → tt)

inj-ff : ∀ t P S n → FrameFreeTrace (inj-trace t P S n)
inj-ff t P S n = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ ++⁺ (fill-ff _ (size S ∸ suc (size P))) (++⁺ (put-ff P n (suc n) 1) (tt ∷ []))

-- D380: a closure body's entry
env-entry-ff : ∀ kd E A → FrameFreeTrace (proj₂ (env-entry kd E A))
env-entry-ff word E A = []
env-entry-ff flat E A =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (get-ff A 1)
      (tt ∷ tt ∷ tt ∷
       ++⁺ (put-ff E 1 3 0) (++⁺ (put-ff A 2 3 _) (tt ∷ tt ∷ [])))

------------------------------------------------------------------------
-- The heap-linked-stack bricks the cata codegen is built from.
------------------------------------------------------------------------
push2-ff : ∀ topSlot tv tb → FrameFreeTrace (push2 topSlot tv tb)
push2-ff topSlot tv tb = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

pop2-ff : ∀ topSlot → FrameFreeTrace (pop2 topSlot)
pop2-ff topSlot = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

wrap-sum-ff : ∀ tag pk ps ss s → FrameFreeTrace (wrap-sum tag pk ps ss s)
wrap-sum-ff tag pk ps ss s =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ ++⁺ (fill-ff _ (ss ∸ suc ps)) (++⁺ (put-k-ff pk ps s (suc s) 1) (tt ∷ []))

getμ-ff : ∀ (G : Fun 0) k → FrameFreeTrace (get-k (lkind G word) (lsz G 1) k)
getμ-ff G k = get-k-ff (lkind G word) (lsz G 1) k

------------------------------------------------------------------------
-- The compile-time functor walks (Tier 2).
------------------------------------------------------------------------
visit-walk-ff : ∀ todoSlot tv tb F s lb → FrameFreeTrace (visit-walk todoSlot tv tb F s lb)
visit-walk-ff todoSlot tv tb (K _)   s lb = []
visit-walk-ff todoSlot tv tb Id      s lb = tt ∷ push2-ff todoSlot tv tb
visit-walk-ff todoSlot tv tb (F ⊕ G) s lb =
  ++⁺ (tt ∷ [])
      (++⁺ (getμ-ff G 1)
      (++⁺ (tt ∷ [])
      (++⁺ (visit-walk-ff todoSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-ff F 1)
      (++⁺ (tt ∷ [])
      (++⁺ (visit-walk-ff todoSlot tv tb F (s + 4) (suc (suc lb)))
           (tt ∷ []))))))))
visit-walk-ff todoSlot tv tb (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-ff F 0)
      (++⁺ (tt ∷ [])
      (++⁺ (visit-walk-ff todoSlot tv tb F (s + 4) lb)
      (++⁺ (tt ∷ [])
      (++⁺ (getμ-ff G (lsz F 1))
      (++⁺ (tt ∷ [])
           (visit-walk-ff todoSlot tv tb G (s + 4) (lb + lsize F))))))))

rebuild-walk-ff : ∀ valSlot tv tb ck cs F s lb → FrameFreeTrace (rebuild-walk valSlot tv tb ck cs F s lb)
rebuild-walk-ff valSlot tv tb ck cs (K _)   s lb = tt ∷ []
rebuild-walk-ff valSlot tv tb ck cs Id      s lb = pop2-ff valSlot
rebuild-walk-ff valSlot tv tb ck cs (F ⊕ G) s lb =
  ++⁺ (tt ∷ [])
      (++⁺ (getμ-ff G 1)
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-ff valSlot tv tb ck cs G (s + 4) (suc (suc lb) + lsize F))
      (++⁺ (wrap-sum-ff 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-ff F 1)
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-ff valSlot tv tb ck cs F (s + 4) (suc (suc lb)))
      (++⁺ (wrap-sum-ff 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s)
           (tt ∷ []))))))))))
rebuild-walk-ff valSlot tv tb ck cs (F ⊗ G) s lb =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-ff G (lsz F 1))
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-ff valSlot tv tb ck cs G (s + 4) (lb + lsize F))
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (getμ-ff F 0)
      (++⁺ (tt ∷ [])
      (++⁺ (rebuild-walk-ff valSlot tv tb ck cs F (s + 4) lb)
      (++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (put-k-ff (lkind F ck) (lsz F cs) (suc s) (s + 3) 0)
      (++⁺ (put-k-ff (lkind G ck) (lsz G cs) (s + 2) (s + 3) (lsz F cs))
           (tt ∷ [])))))))))))

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

cata-setup-ff : ∀ E cl k ev bl → FrameFreeTrace (cata-call-setup E cl k ev bl)
cata-setup-ff E cl k ev bl =
  ++⁺ (get-ff E 0) (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])

cata-call-from-ff : ∀ i0 → EmittableI i0 → ∀ E lk ls cl k ev pr
                  → FrameFreeTrace (cata-call-from i0 E lk ls cl k ev pr)
cata-call-from-ff i0 e0 E lk ls cl k ev pr =
  e0 ∷ tt ∷ tt ∷ tt ∷
  ++⁺ (put-ff E ev pr 0)
      (++⁺ (put-k-ff lk ls k pr _) (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []))

cata-const-ff : ∀ E G bb n1 l1 at → FrameFreeTrace at
              → FrameFreeTrace (cata-trace-of (cata-trace-const E G bb n1 l1 at))
cata-const-ff E G bb n1 l1 at ff =
  ++⁺ (cata-setup-ff E n1 (n1 + 1) (n1 + 2) l1)
      (++⁺ (cata-call-from-ff _ tt E (lkind G word) _ n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body-ff l1 (l1 + 1) bb at ff))

cata-box-ff : ∀ E G bb n1 l1 at → FrameFreeTrace at
              → FrameFreeTrace (cata-trace-of (cata-trace-box E G bb n1 l1 at))
cata-box-ff E G bb n1 l1 at ff =
  ++⁺ (cata-setup-ff E n1 (n1 + 1) (n1 + 2) l1)
      (++⁺ (cata-call-from-ff _ tt E (lkind G word) _ n1 (n1 + 1) (n1 + 2) (n1 + 3)) (cata-body-ff l1 (l1 + 1) bb at ff))

cata-branching-ff : ∀ E A F bb n1 l1 at → FrameFreeTrace at
                  → FrameFreeTrace (cata-trace-of (cata-trace-branching E A F bb n1 l1 at))
-- Tier 2 splices once, so it has ONE call site.
cata-branching-ff E A F bb n1 l1 at ff =
  ++⁺ (cata-setup-ff E cl (cl + 1) (cl + 2) bodyL)
      (++⁺ I₁ (++⁺ (cata-call-from-ff _ tt E (lkind F (kind A)) _ cl (cl + 1) (cl + 2) (cl + 3))
                   (++⁺ I₂ (cata-body-ff bodyL (bodyL + 1) bb at ff))))
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
             (++⁺ (rebuild-walk-ff (n1 + 2) (n1 + 4) (n1 + 5) (kind A) _ F (n1 + 7) ((l1 + 4) + lsize F))
                  (tt ∷ [])))))))))
    I₂ : FrameFreeTrace _
    I₂ = ++⁺ (push2-ff (n1 + 2) (n1 + 4) (n1 + 5))
             (++⁺ (tt ∷ tt ∷ []) (tt ∷ tt ∷ tt ∷ []))

cata-dispatch-ff : ∀ E A G st bb n1 l1 at → FrameFreeTrace at
                 → FrameFreeTrace (cata-trace-of (cata-dispatch E A G st bb n1 l1 at))
cata-dispatch-ff E A G strat-box           bb n1 l1 at ff = cata-box-ff E G bb n1 l1 at ff
cata-dispatch-ff E A G strat-const         bb n1 l1 at ff = cata-const-ff E G bb n1 l1 at ff
cata-dispatch-ff E A G (strat-branching F) bb n1 l1 at ff = cata-branching-ff E A F bb n1 l1 at ff

------------------------------------------------------------------------
-- THE THEOREM, over arbitrary frontier `n` / label counter `l`.
------------------------------------------------------------------------
-- Plan 0.63 step 2b: CONDITIONAL ON `HeapModed`. `lea-slot` joined
-- `FrameFreeI`'s ⊥ set (it is the sole creator of a stack pointer), and it
-- IS emitted — by the four STACK-mode clauses below, whose `IsHeap Stack`
-- premise is `⊥`. So the theorem is exactly as strong as it can be: a
-- heap-moded trace contains no frame op and no `lea-slot`.
-- Plan 0.108: neither SigOp lowering touches a frame.
sigop-frame-free : ∀ {A B} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp) → FrameFreeTrace (sigop-code si n m)
sigop-frame-free si n nothing  = tt ∷ []
sigop-frame-free si n (just _) = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

-- D366: `In`'s three shapes and `out-μ`'s.
in-ff : ∀ (r : MuRep) kd L (n : ℕ) → FrameFreeTrace (in-trace r kd L n)
in-ff mu-box  kd L n = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
in-ff mu-unit kd L n = tt ∷ []
in-ff mu-ptr  word L n = tt ∷ []
in-ff mu-ptr  flat L n = tt ∷ tt ∷ tt ∷ tt ∷ ++⁺ (put-ff L n (suc n) 0) (tt ∷ [])

out-ff : ∀ (r : MuRep) → FrameFreeTrace (out-trace r)
out-ff mu-box  = tt ∷ []
out-ff mu-unit = tt ∷ []
out-ff mu-ptr  = tt ∷ []

frame-free-trace' : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) (n l : ℕ)
                  → FrameFreeTrace (trace-of (ir-to-trace' n l ir))
frame-free-trace' id       hm n l = tt ∷ []
frame-free-trace' (fst {A} {B}) hm n l = get-ff A 0
frame-free-trace' (snd {A} {B}) hm n l = get-ff B _
frame-free-trace' terminal hm n l = []
frame-free-trace' initial  hm n l = tt ∷ []
frame-free-trace' (g ∘ f)  (hf , hg) n l =
  ++⁺ (frame-free-trace' f hf _ _) (tt ∷ frame-free-trace' g hg _ _)
-- plan 0.123 B.4 α: the pair's tail `put`s both components.
frame-free-trace' (⟨_,_⟩ {A} {B} {C} f g) (hf , hg) n l =
  tt ∷ tt ∷
  ++⁺ (frame-free-trace' f hf _ _)
      (tt ∷ tt ∷
       ++⁺ (frame-free-trace' g hg _ _)
           (tt ∷ tt ∷ tt ∷
            ++⁺ (put-ff B _ _ 0) (++⁺ (put-ff C _ _ _) (tt ∷ []))))
frame-free-trace' (curry b)  hb n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (apply {A} {B}) hm n l =
  ++⁺ (get-ff A 1)
      (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷
       ++⁺ (put-ff A _ _ 1) (tt ∷ tt ∷ tt ∷ []))
frame-free-trace' (inl {A} {B}) hm n l = inj-ff 0 A (A +ᵀ B) n
frame-free-trace' (inr {A} {B}) hm n l = inj-ff 1 B (A +ᵀ B) n
-- case is FLAT CONTROL since item 6 — plain splices, no depth obligation.
frame-free-trace' (case {A} {B} f g) (hf , hg) n l =
  ++⁺ (tt ∷ [])
      (++⁺ (get-ff B 1)
      (++⁺ (tt ∷ [])
      (++⁺ (frame-free-trace' g hg _ _)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-ff A 1)
      (++⁺ (tt ∷ [])
      (++⁺ (frame-free-trace' f hf _ _) (tt ∷ []))))))))
frame-free-trace' (Iter {E} {A} {B} b) hb n l =
  ++⁺ (get-ff E 0)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (frame-free-trace' b hb _ _)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-ff A 1)
      (++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (put-ff E _ _ 0)
      (++⁺ (put-ff A _ _ _)
      (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ [])
           (get-ff B 1)))))))))
frame-free-trace' (In {F} _) hm n l = in-ff (mu-rep F) _ _ n
frame-free-trace' (out-μ {F} _) hm n l = out-ff (mu-rep F)
-- C1: the algebra is generated at frontier 0 (its own frame), so its IH is
-- taken there rather than at the caller's `n`.
frame-free-trace' (Cata {F} _ {E} {A} alg) hm n l =
  cata-dispatch-ff E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) _ _ _ _ (frame-free-trace' alg hm 0 l)
frame-free-trace' (Out _)        hm n l = tt ∷ tt ∷ tt ∷ tt ∷ []
-- D189: the same two-cell build as `Ana`, with `id` as the block.
frame-free-trace' (in-ν _)     hm n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
-- D189: the ν suspension is `curry`'s closure record cell for cell, so
-- its walk clause is `curry`'s. The coalgebra is a named block, like the
-- closure body, emitted at frontier 0 under the ν's own label.
frame-free-trace' (Ana _ c)      hm n l =
  tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []
frame-free-trace' (SigOp si)     hm n l = sigop-frame-free si n (cmp-of (sem si))
frame-free-trace' (Call _)      hm n l = tt ∷ []
frame-free-trace' (const fits-int _)   hm n l = tt ∷ []
frame-free-trace' (const fits-float _) hm n l = tt ∷ []

------------------------------------------------------------------------
-- Corollaries over the public entry points, and the form the flat↔x86-64
-- correspondence consumes: a FETCH into an emitted program never yields a
-- frame op.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- D159: …AND EVERY EMITTED BLOCK. `FrameFreeTrace` is `All EmittableI`, a
-- plain `All`, so `link` preservation is `++⁺` — no index to thread.
------------------------------------------------------------------------
ffbds : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
      → List (LabelId × ℕ × AbstractTrace)
ffbds (_ , _ , _ , bs) = bs

BlockFrameFree : LabelId × ℕ × AbstractTrace → Set
BlockFrameFree (_ , _ , t) = FrameFreeTrace t

frame-free-blocks : ∀ (bs : List (LabelId × ℕ × AbstractTrace))
                  → All BlockFrameFree bs → FrameFreeTrace (blocks-layout bs)
frame-free-blocks []                   []       = []
frame-free-blocks ((lb , bb , t) ∷ bs) (q ∷ qs) =
  ++⁺ (tt ∷ ++⁺ q (tt ∷ [])) (frame-free-blocks bs qs)

-- D199: the re-suspension pass passes the EMITTER fence. It emits register
-- moves, offset loads/stores, a heap allocation, a code-address load and
-- flat control: its sum arm branches with `c-branch-tag-zero`/`c-jmp`/`c-label`,
-- exactly as `case` does.
resuspend-ff : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
             → FrameFreeTrace (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
resuspend-ff H E A n l lbl env (wf-K _) = []
resuspend-ff H E A n l lbl env wf-Id =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-ff E 0)
      (++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (put-ff E _ _ 0)
      (++⁺ (put-ff A _ _ _)
           (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])))))
resuspend-ff H E A n l lbl env (wf-Prod {F} {G} wfF wfG) =
  ++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-ff (⟦ F ⟧TI A) 0)
      (++⁺ (resuspend-ff H E A (suc (suc (suc (suc n)))) l lbl env wfF)
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (get-ff (⟦ G ⟧TI A) _)
      (++⁺ (resuspend-ff H E A n2 l2 lbl env wfG)
      (++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (put-ff (⟦ F ⟧TI (ν-type H)) _ _ 0)
      (++⁺ (put-ff (⟦ G ⟧TI (ν-type H)) _ _ _)
           (tt ∷ [])))))))))
  where
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF))
resuspend-ff H E A n l lbl env (wf-Sum {F} {G} wfF wfG) =
  ++⁺ (tt ∷ tt ∷ tt ∷ [])
      (++⁺ (arm G (resuspend-ff H E A n2 l2 lbl env wfG) {c = c-of G})
      (++⁺ (tt ∷ tt ∷ [])
      (++⁺ (arm F (resuspend-ff H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF) {c = c-of F})
           (tt ∷ []))))
  where
    n2 = proj₁ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
    c-of : IRFunctor → ℕ
    c-of P = size (⟦ F ⟧TI (ν-type H) +ᵀ ⟦ G ⟧TI (ν-type H)) ∸ suc (size (⟦ P ⟧TI (ν-type H)))
    arm : ∀ (P : IRFunctor) {t} → FrameFreeTrace t → ∀ {tag sz c}
        → FrameFreeTrace ((Once.CCC.Machine.SMCore.restore-input n ∷ []) ++ get (⟦ P ⟧TI A) 1 ++ t ++
                          (Once.CCC.Machine.SMCore.store-at-slot (suc (suc n)) ∷
                           Once.CCC.Machine.SMCore.instr-alloc-heap sz ∷
                           Once.CCC.Machine.SMCore.store-at-slot (suc n) ∷
                           Once.CCC.Machine.SMCore.mov-to-input ∷
                           Once.CCC.Machine.SMCore.instr-load-tag-lit tag ∷
                           Once.CCC.Machine.SMCore.store-at 0 ∷ []) ++
                          fill (suc (size (⟦ P ⟧TI (ν-type H)))) c ++
                          put (⟦ P ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1 ++
                          (Once.CCC.Machine.SMCore.load-from-slot (suc n) ∷ []))
    arm P ff {c = c} =
      ++⁺ (tt ∷ [])
          (++⁺ (get-ff (⟦ P ⟧TI A) 1)
          (++⁺ ff
          (++⁺ (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
          (++⁺ (fill-ff _ c) (++⁺ (put-ff (⟦ P ⟧TI (ν-type H)) _ _ 1) (tt ∷ []))))))

frame-free-blocks' : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) (n l : ℕ)
                   → All BlockFrameFree (ffbds (ir-to-trace' n l ir))
frame-free-blocks' id       hm n l = []
frame-free-blocks' fst      hm n l = []
frame-free-blocks' snd      hm n l = []
frame-free-blocks' terminal hm n l = []
frame-free-blocks' initial  hm n l = []
frame-free-blocks' (g ∘ f)  (hf , hg) n l =
  ++⁺ (frame-free-blocks' f hf n l) (frame-free-blocks' g hg _ _)
frame-free-blocks' ⟨ f , g ⟩ (hf , hg) n l =
  ++⁺ (frame-free-blocks' f hf _ l) (frame-free-blocks' g hg _ _)
-- D380: the body starts with its environment's entry.
frame-free-blocks' (curry {E} {A} b)  hb n l =
  ++⁺ (env-entry-ff (kind E) E A) (frame-free-trace' b hb _ (suc (suc l)))
  ∷ frame-free-blocks' b hb _ (suc (suc l))
frame-free-blocks' apply hm n l = []
frame-free-blocks' inl hm n l = []
frame-free-blocks' inr hm n l = []
frame-free-blocks' (case f g) (hf , hg) n l =
  ++⁺ (frame-free-blocks' f hf n (suc (suc l))) (frame-free-blocks' g hg _ _)
frame-free-blocks' (Iter b) hb n l = frame-free-blocks' b hb _ _
frame-free-blocks' (In _)  hm n l = []
frame-free-blocks' (out-μ _) hm n l = []
frame-free-blocks' (Cata {F} _ alg) hm n l = frame-free-blocks' alg hm 0 l
frame-free-blocks' (Out _)        hm n l = []
frame-free-blocks' (in-ν _)     hm n l = (tt ∷ []) ∷ []
-- D199: the block is `coalg ++ re-suspension`.
frame-free-blocks' (Ana {F} wf {E} {A} c)     hc n l =
  (tt ∷ tt ∷
   ++⁺ (frame-free-trace' c hc 1 (suc l))
       (resuspend-ff F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                     (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c))) (ℓ o l) 0 wf))
    ∷ frame-free-blocks' c hc 1 (suc l)
frame-free-blocks' (SigOp _)      hm n l = []
frame-free-blocks' (Call _)      hm n l = []
frame-free-blocks' (const fits-int _)   hm n l = []
frame-free-blocks' (const fits-float _) hm n l = []

frame-free-at-frontier : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) (n : ℕ)
                       → FrameFreeTrace (ir-to-trace-at-frontier n ir)
frame-free-at-frontier ir hm n =
  ++⁺ (frame-free-trace' ir hm n 0)
      (tt ∷ frame-free-blocks _ (frame-free-blocks' ir hm n 0))

ir-to-trace-frame-free : ∀ {A B} (ir : IR A B) (hm : HeapModed ir)
                       → FrameFreeTrace (ir-to-trace ir)
ir-to-trace-frame-free ir hm = frame-free-at-frontier ir hm 0

-- D244/D245: …and a program's unit placed at label counter `l`.
ir-to-trace-lab-frame-free : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) (l : ℕ)
                           → FrameFreeTrace (ir-to-trace-lab l ir)
ir-to-trace-lab-frame-free ir hm l =
  ++⁺ (frame-free-trace' ir hm 0 l)
      (tt ∷ frame-free-blocks _ (frame-free-blocks' ir hm 0 l))

-- …and the OUTERMOST unit, linked with the program's leave (D320).
ir-to-trace-top-frame-free : ∀ {A B} (ir : IR A B) (hm : HeapModed ir)
                           → FrameFreeTrace (link-top (ir-to-unit ir))
ir-to-trace-top-frame-free ir hm =
  ++⁺ (frame-free-trace' ir hm 0 0)
      (tt ∷ frame-free-blocks _ (frame-free-blocks' ir hm 0 0))

-- (`ir-to-trace-frame-free-deep` is GONE with the flip: `FrameFreeT` is the
-- SEMANTIC predicate and an emitted trace no longer satisfies it — the markers
-- move the frame.)

module _ {FS : FrameSemantics} where
  open FlatMachine {FS}

  fetch-frame-free : ∀ {A B} (ir : IR A B) (hm : HeapModed ir) {k i}
                   → fetch (ir-to-trace ir) k ≡ just i → EmittableI i
  fetch-frame-free ir hm = fetch-All (ir-to-trace-frame-free ir hm)
