-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRToTrace
--
-- Shared IR → AbstractTrace lowering used by every architecture's
-- Target instance, including X86-64 after Plan 0.10 Phase C lands.
-- New architectures only need:
--
--   * `compile-trace : AbstractTrace → arch.Program`
--     (already provided as `Once.CCC.Target.<arch>.AbstractTo<arch>.compile-trace`)
--
--   * `programToText : arch.Program → String`
--     (per-arch `Emit.agda`)
--
-- and they're done — `Once.Target.<arch>` composes them with this
-- function.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- State threading
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- `ir-to-trace'` threads a slot frontier counter so pair/curry/apply
-- can allocate the slots they need. The frontier mirrors
-- `next-slot alloc` in the verified Dispatcher's AllocState.
--
-- Convention: each operation that allocates k slots advances the
-- frontier by k. The OUTGOING frontier is what the next operation
-- sees. Reclamation (slot reuse on subsequent allocations) is a
-- caller-side concern; this function is monotone.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Coverage (Plan 0.10 Phase B)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Implemented (emit a real trace, mirroring the corresponding *WF module):
--   id           — SimpleWF
--   _∘_          — ComposeWF
--   fst, snd     — SimpleWF
--   terminal     — SimpleWF
--   initial      — SimpleWF
--   arr          — SimpleWF
--   ⟨_,_⟩        — PairWF2.pair-trace
--   curry        — CurryWF.curry-trace
--   apply        — ApplyWF.apply-setup-trace + instr-call-closure
--   SigOp        — `instr-sigop name` (per-arch decode)
--
-- Stubbed (emit `[]` — Layer 0 doesn't need these):
--   inl, inr, case
--   In, out-μ, Cata, Para, Out, in-ν, Ana, Hylo, Fuse
--   free-heap
--
-- See `plans/0.10-verification-gap-closure.md`.
------------------------------------------------------------------------

module Once.CCC.Codegen.IRToTrace where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.List using (List; []; _∷_; _++_)

open import Once.CCC.SigOp.Info using (SigOpInfo)
open SigOpInfo using (name)

open import Once.CCC.IR using (IR;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply; arr;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)

open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace;
         mov-to-output; mov-to-input; mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc; load-from-slot;
         store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack; instr-reclaim-to;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         instr-sigop; instr-load-const; instr-load-code-addr;
         instr-save-closure-reg)

------------------------------------------------------------------------
-- IR → AbstractTrace, state-passing
------------------------------------------------------------------------

-- | State-passing form. Plan 0.2.4.2 Phase C: extended to also
-- thread a label counter and accumulate closure-body traces.
--
-- Inputs:
--   slot-frontier — current next-available stack slot
--   label-counter — current next-available .L_thunk_<n> index
--   IR
--
-- Output (4-tuple):
--   slot-frontier-after — slots used by this IR's main trace
--   label-counter-after — labels used by this IR + nested bodies
--   main-trace          — the trace executed in the parent function
--   body-traces         — `(label, body-trace)` pairs for each
--                         curry encountered (this IR + nested)
--
-- The `curry` clause is the only one that allocates a new label.
-- Other clauses thread the counter and accumulate body lists.
ir-to-trace' : ∀ {A B} → ℕ → ℕ → IR A B
              → ℕ × ℕ × AbstractTrace × List (ℕ × AbstractTrace)

-- ────────────────────────────────────────────────────────────────────
-- Trivial morphisms (no slots needed; mirror SimpleWF.run-*-trace).
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l id        = n , l , (mov-to-output ∷ []) , []
-- Plan 0.2.4.5 Stage C γ-revert: uniform packed-pair convention.
-- fst / snd dereference Input1 (= pointer to packed pair record).
-- The split-input optimization (apply pre-unpacks pair into
-- Input1/Input2) was reverted because nested fst/snd (reading from
-- packed compound values) needed layout-discriminating lowering,
-- which adds context tracking complexity that's a hiding place for
-- postulates. Future: type-driven split for register-fittable
-- primitive args, layered as an optimization pass on top of the
-- uniform packed base.
ir-to-trace' n l fst       = n , l , (load-indirect ∷ []) , []
ir-to-trace' n l snd       = n , l , (load-indirect-suc ∷ []) , []
ir-to-trace' n l terminal  = n , l , (mov-to-output ∷ []) , []
ir-to-trace' n l initial   = n , l , (mov-to-output ∷ []) , []
ir-to-trace' n l arr       = n , l , (mov-to-output ∷ []) , []

-- ────────────────────────────────────────────────────────────────────
-- Compose: thread output of f into input of g via the abstract bridge.
-- Mirror ComposeWF.compose-trace = f-trace ++ mov-to-input ∷ g-trace.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l (g ∘ f)   =
  let (n1 , l1 , ft , fb) = ir-to-trace' n  l  f
      (n2 , l2 , gt , gb) = ir-to-trace' n1 l1 g
  in n2 , l2 , (ft ++ mov-to-input ∷ gt) , (fb ++ gb)

-- ────────────────────────────────────────────────────────────────────
-- ⟨ f , g ⟩ — pair construction.
-- Mirror PairWF2.pair-trace:
--   backup-slot = next-slot
--   fst-slot    = suc backup-slot
--   snd-slot    = suc fst-slot
--   pair-trace  =
--     mov-to-output ∷ store-at-slot backup-slot ∷
--     f-trace ++
--     store-at-slot fst-slot ∷ restore-input backup-slot ∷
--     g-trace ++
--     store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l (⟨ f , g ⟩ _) =
  let backup-slot = n
      fst-slot    = suc backup-slot
      snd-slot    = suc fst-slot
      f-start     = suc snd-slot
      (n1 , l1 , ft , fb) = ir-to-trace' f-start l  f
      (n2 , l2 , gt , gb) = ir-to-trace' n1 l1 g
  in n2 , l2 ,
     (mov-to-output ∷ store-at-slot backup-slot ∷
      ft ++
      store-at-slot fst-slot ∷ restore-input backup-slot ∷
      gt ++
      store-at-slot snd-slot ∷ lea-slot fst-slot ∷ []) ,
     (fb ++ gb)

-- ────────────────────────────────────────────────────────────────────
-- curry — closure construction.
-- Mirror CurryWF.curry-trace closure-slot:
--   mov-to-output ∷                       -- Output := Input1 (env ptr)
--   store-at-slot closure-slot ∷          -- closure[0] := env
--   lea-slot (suc closure-slot) ∷         -- Output := &closure[1]
--   store-at-slot (suc closure-slot) ∷    -- closure[1] := code-ptr
--   lea-slot closure-slot ∷ []            -- Output := closure address
--
-- The body's trace is emitted separately and reachable via the code
-- pointer. For Phase B we don't yet inline the body into the closure
-- record (that's what `apply-full-trace` does in the verified path);
-- runtime closure-call resolution comes via `instr-call-closure` at
-- the apply site.
-- ────────────────────────────────────────────────────────────────────

-- Plan 0.2.4.2 Phase C: closure construction with REAL code-pointer.
--
-- 1. Allocate a fresh body label `this-label = l` (the input
--    counter); bump the counter to `l+1`.
-- 2. Recursively process the body's IR with a fresh slot frame
--    (slot = 0, since the body has its own SysV stack frame —
--    Plan 0.2.4.2 D2). The body may itself contain more curries
--    contributing their bodies; we collect them.
-- 3. Emit the closure-record construction at parent's slots
--    `[closure-slot, suc closure-slot]`. Both Stack and Heap
--    AllocMode use parent's slots in this phase; Phase D will
--    migrate Heap to a static `.bss` bump pool.
-- 4. The crucial fix vs. the old emission: instead of
--    `lea-slot (suc closure-slot)` (which gives the slot's own
--    address), emit `instr-load-code-addr this-label` which
--    per-arch lowers to `lea .L_thunk_<this-label>(%rip), %rax`
--    (the body's actual code address).
--
-- The `_` for AllocMode is intentional in this phase — Stack and
-- Heap diverge only at the record-allocation step, which is still
-- "use parent's slots" for both. Phase D adds the divergence.
ir-to-trace' n l (curry body _) =
  let this-label = l
      l1         = suc l
      -- Body uses fresh slot frame (own SysV frame at runtime, D2)
      -- and shares the global label counter.
      (_ , l2 , body-trace , body-bodies) = ir-to-trace' 0 l1 body
      closure-slot = n
      next        = suc (suc closure-slot)
      this-trace  = mov-to-output ∷
                    store-at-slot closure-slot ∷
                    instr-load-code-addr this-label ∷
                    store-at-slot (suc closure-slot) ∷
                    lea-slot closure-slot ∷ []
      all-bodies  = (this-label , body-trace) ∷ body-bodies
  in next , l2 , this-trace , all-bodies

-- ────────────────────────────────────────────────────────────────────
-- apply — runtime closure call.
-- Mirror ApplyWF.apply-setup-trace + instr-call-closure:
--   pair-slot = next-slot   (used for env+arg backup)
--   apply-setup-trace pair-slot ++ instr-call-closure ∷ []
--
-- Setup loads (closure, arg) from the input pair, stores them at
-- slot/slot+1, points Input1 at the new pair. Then instr-call-closure
-- transfers control to the closure's code pointer (per-arch lowering
-- knows the calling convention).
-- ────────────────────────────────────────────────────────────────────

-- Plan 0.2.4.5 Stage C γ-revert: uniform packed-pair convention.
-- Apply receives a (closure, arg) pair pointer in Input1. It packs
-- a NEW (env, arg) pair at slots [pair-slot, pair-slot+1] for the
-- body and points Input1 at it. Body uses uniform fst/snd =
-- load-indirect / load-indirect-suc to project from packed pairs,
-- regardless of nesting level.
ir-to-trace' n l apply =
  let pair-slot = n
  in (suc (suc pair-slot)) , l ,
     (load-indirect-suc ∷                -- Output := arg-loc from input pair
      store-at-slot (suc pair-slot) ∷    -- new-pair[1] := arg-loc
      load-indirect ∷                    -- Output := closure-loc from input pair
      mov-to-input ∷                     -- Input1 := closure-loc
      instr-save-closure-reg ∷
      load-indirect ∷                    -- Output := env-loc from closure
      store-at-slot pair-slot ∷          -- new-pair[0] := env-loc
      lea-slot pair-slot ∷               -- Output := &new-pair
      mov-to-input ∷                     -- Input1 := &new-pair
      instr-call-closure ∷ []) ,
     []

-- ────────────────────────────────────────────────────────────────────
-- SigOp — per-name dispatch handled by per-arch compile-abstract.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l (SigOp si) = n , l , (instr-sigop si ∷ []) , []

-- Plan 0.11: const literal — emit a single load-const abstract instr.
ir-to-trace' n l (const p _ vM) = n , l , (instr-load-const p vM ∷ []) , []

-- ────────────────────────────────────────────────────────────────────
-- Stubbed — emit `[]`. Not needed for Layer 0; future work.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n l (inl _)       = n , l , [] , []
ir-to-trace' n l (inr _)       = n , l , [] , []
ir-to-trace' n l (case _ _)    = n , l , [] , []

ir-to-trace' n l (In _ _)       = n , l , [] , []
-- out-μ and Out: ν/μ Lambek inverses; semantically Output := Input1.
-- run-X uses `mov-to-output ∷ []`; mirror it so the discharge falls
-- out via the same `transport-trivial` pattern as id/arr/free-heap.
ir-to-trace' n l (out-μ _)      = n , l , (mov-to-output ∷ []) , []
ir-to-trace' n l (Cata _ _)     = n , l , [] , []
ir-to-trace' n l (Para _ _)     = n , l , [] , []
ir-to-trace' n l (Out _)        = n , l , (mov-to-output ∷ []) , []
ir-to-trace' n l (in-ν _ _)     = n , l , [] , []
ir-to-trace' n l (Ana _ _)      = n , l , [] , []
ir-to-trace' n l (Hylo _ _ _ _) = n , l , [] , []
ir-to-trace' n l (Fuse _ _ _ _) = n , l , [] , []

-- free-heap is semantically a no-op (returns its input unchanged).
-- run-free-heap emits `mov-to-output ∷ []` to copy Input1 → Output as
-- the identity behavior; we mirror that exactly so trace correctness
-- discharges via the same transport-trivial pattern as id/arr.
ir-to-trace' n l (free-heap _)  = n , l , (mov-to-output ∷ []) , []

------------------------------------------------------------------------
-- Public wrapper: starts at frontier 0, returns just the trace.
------------------------------------------------------------------------

-- | Plan 0.2.4.2 Phase C: helpers to project main trace / bodies
-- from `ir-to-trace'`'s 4-tuple result.
private
  proj-trace : ℕ × ℕ × AbstractTrace × List (ℕ × AbstractTrace) → AbstractTrace
  proj-trace (_ , _ , t , _) = t

  proj-bodies : ℕ × ℕ × AbstractTrace × List (ℕ × AbstractTrace) → List (ℕ × AbstractTrace)
  proj-bodies (_ , _ , _ , bs) = bs

ir-to-trace : ∀ {A B} → IR A B → AbstractTrace
ir-to-trace ir = proj-trace (ir-to-trace' 0 0 ir)

-- | Plan 0.2.4.2 Phase C: closure-body traces collected for an IR.
-- Each `(label, body-trace)` pair becomes a `.L_thunk_<label>:` block
-- in the parent function's emitted assembly, after the parent's `ret`.
ir-to-bodies : ∀ {A B} → IR A B → List (ℕ × AbstractTrace)
ir-to-bodies ir = proj-bodies (ir-to-trace' 0 0 ir)
