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
  free-heap; SigOp)

open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace;
         mov-to-output; mov-to-input;
         load-indirect; load-indirect-suc; load-from-slot;
         store-at-slot; store-indirect; store-indirect-suc;
         lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack; instr-reclaim-to;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         instr-sigop)

------------------------------------------------------------------------
-- IR → AbstractTrace, state-passing
------------------------------------------------------------------------

-- | State-passing form. The `ℕ` is the slot frontier on entry; the
-- result is `(frontier-after , trace)`.
ir-to-trace' : ∀ {A B} → ℕ → IR A B → ℕ × AbstractTrace

-- ────────────────────────────────────────────────────────────────────
-- Trivial morphisms (no slots needed; mirror SimpleWF.run-*-trace).
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n id        = n , (mov-to-output ∷ [])
ir-to-trace' n fst       = n , (load-indirect ∷ [])
ir-to-trace' n snd       = n , (load-indirect-suc ∷ [])
ir-to-trace' n terminal  = n , (mov-to-output ∷ [])
ir-to-trace' n initial   = n , (mov-to-output ∷ [])
ir-to-trace' n arr       = n , (mov-to-output ∷ [])

-- ────────────────────────────────────────────────────────────────────
-- Compose: thread output of f into input of g via the abstract bridge.
-- Mirror ComposeWF.compose-trace = f-trace ++ mov-to-input ∷ g-trace.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n (g ∘ f)   =
  let (n1 , ft) = ir-to-trace' n  f
      (n2 , gt) = ir-to-trace' n1 g
  in n2 , (ft ++ mov-to-input ∷ gt)

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

ir-to-trace' n (⟨ f , g ⟩ _) =
  let backup-slot = n
      fst-slot    = suc backup-slot
      snd-slot    = suc fst-slot
      f-start     = suc snd-slot
      (n1 , ft)   = ir-to-trace' f-start f
      (n2 , gt)   = ir-to-trace' n1      g
  in n2 ,
     (mov-to-output ∷ store-at-slot backup-slot ∷
      ft ++
      store-at-slot fst-slot ∷ restore-input backup-slot ∷
      gt ++
      store-at-slot snd-slot ∷ lea-slot fst-slot ∷ [])

-- ────────────────────────────────────────────────────────────────────
-- curry — closure construction.
-- Mirror CurryWF.curry-trace closure-slot:
--   mov-to-output ∷                       -- Output := Input (env ptr)
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

ir-to-trace' n (curry _ _) =
  let closure-slot = n
      next        = suc (suc closure-slot)
  in next ,
     (mov-to-output ∷
      store-at-slot closure-slot ∷
      lea-slot (suc closure-slot) ∷
      store-at-slot (suc closure-slot) ∷
      lea-slot closure-slot ∷ [])

-- ────────────────────────────────────────────────────────────────────
-- apply — runtime closure call.
-- Mirror ApplyWF.apply-setup-trace + instr-call-closure:
--   pair-slot = next-slot   (used for env+arg backup)
--   apply-setup-trace pair-slot ++ instr-call-closure ∷ []
--
-- Setup loads (closure, arg) from the input pair, stores them at
-- slot/slot+1, points Input at the new pair. Then instr-call-closure
-- transfers control to the closure's code pointer (per-arch lowering
-- knows the calling convention).
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n apply =
  let pair-slot = n
  in (suc (suc pair-slot)) ,
     (load-indirect-suc ∷
      store-at-slot (suc pair-slot) ∷
      load-indirect ∷
      mov-to-input ∷
      load-indirect ∷
      store-at-slot pair-slot ∷
      lea-slot pair-slot ∷
      mov-to-input ∷
      instr-call-closure ∷ [])

-- ────────────────────────────────────────────────────────────────────
-- SigOp — per-name dispatch handled by per-arch compile-abstract.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n (SigOp si) = n , (instr-sigop si ∷ [])

-- ────────────────────────────────────────────────────────────────────
-- Stubbed — emit `[]`. Not needed for Layer 0; future work.
-- ────────────────────────────────────────────────────────────────────

ir-to-trace' n (inl _)       = n , []
ir-to-trace' n (inr _)       = n , []
ir-to-trace' n (case _ _)    = n , []

ir-to-trace' n (In _ _)       = n , []
-- out-μ and Out: ν/μ Lambek inverses; semantically Output := Input.
-- run-X uses `mov-to-output ∷ []`; mirror it so the discharge falls
-- out via the same `transport-trivial` pattern as id/arr/free-heap.
ir-to-trace' n (out-μ _)      = n , (mov-to-output ∷ [])
ir-to-trace' n (Cata _ _)     = n , []
ir-to-trace' n (Para _ _)     = n , []
ir-to-trace' n (Out _)        = n , (mov-to-output ∷ [])
ir-to-trace' n (in-ν _ _)     = n , []
ir-to-trace' n (Ana _ _)      = n , []
ir-to-trace' n (Hylo _ _ _ _) = n , []
ir-to-trace' n (Fuse _ _ _ _) = n , []

-- free-heap is semantically a no-op (returns its input unchanged).
-- run-free-heap emits `mov-to-output ∷ []` to copy Input → Output as
-- the identity behavior; we mirror that exactly so trace correctness
-- discharges via the same transport-trivial pattern as id/arr.
ir-to-trace' n (free-heap _)  = n , (mov-to-output ∷ [])

------------------------------------------------------------------------
-- Public wrapper: starts at frontier 0, returns just the trace.
------------------------------------------------------------------------

ir-to-trace : ∀ {A B} → IR A B → AbstractTrace
ir-to-trace ir = proj₂ (ir-to-trace' 0 ir)
