-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRToTrace
--
-- Shared IR → AbstractTrace lowering used by every architecture's
-- Target instance EXCEPT X86-64, which has its own direct
-- `Once.CCC.Target.X86-64.CodeGen.Compile.compile-ir` path. New
-- architectures only need:
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
-- Coverage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Implemented (emit a real trace):
--   id, fst, snd, terminal, initial, arr, _∘_
--
-- Stubbed (emit `[]` — the per-arch compile-ir wraps an empty trace
-- with a trap instruction so the binary aborts at the right place):
--   ⟨_,_⟩, inl, inr, case,
--   curry, apply,
--   In, out-μ, Cata, Para, Out, in-ν, Ana, Hylo, Fuse,
--   free-heap, SigOp
--
-- The stubbed cases require slot-tracking (pair, curry) or runtime
-- support (apply, recursion schemes) that's only fully wired through
-- X86-64's direct `compile-ir`. Implementing them here is a separate
-- plan — what this module enables is "the multi-arch CLI flag works
-- end-to-end for the simple-IR subset".
--
-- See: docs/compiler/decision-log.md (Plan multi-arch — TBD).
------------------------------------------------------------------------

module Once.CCC.Codegen.IRToTrace where

open import Data.List using (List; []; _∷_; _++_)

open import Once.CCC.IR using (IR;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply; arr;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp)

open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace;
         mov-to-output; mov-to-input; load-indirect; load-indirect-suc)

------------------------------------------------------------------------
-- IR → AbstractTrace
------------------------------------------------------------------------

-- | Lower an IR term to an `AbstractTrace`. Stubbed cases emit `[]`
-- (the per-arch wrapper substitutes a trap).
ir-to-trace : ∀ {A B} → IR A B → AbstractTrace

-- Trivial morphisms (no slots needed).
ir-to-trace id        = mov-to-output ∷ []
ir-to-trace fst       = load-indirect ∷ []
ir-to-trace snd       = load-indirect-suc ∷ []
ir-to-trace terminal  = mov-to-output ∷ []   -- () passes through; representation chosen by callee
ir-to-trace initial   = mov-to-output ∷ []   -- absurd input; no runtime path reaches it
ir-to-trace arr       = mov-to-output ∷ []   -- arr is identity at the trace level

-- Compose: thread output of f into input of g via the abstract bridge.
ir-to-trace (g ∘ f)   = ir-to-trace f ++ mov-to-input ∷ ir-to-trace g

-- ────────────────────────────────────────────────────────────────────
-- Stubbed: emit `[]`. The arch's compile-ir wraps with a trap.
-- ────────────────────────────────────────────────────────────────────

-- Pair / sum: need slot tracking (next-slot counter through recursion).
ir-to-trace (⟨ _ , _ ⟩ _) = []
ir-to-trace (inl _)       = []
ir-to-trace (inr _)       = []
ir-to-trace (case _ _)    = []

-- Closures: need RIP-relative / label-rel addressing per arch.
ir-to-trace (curry _ _)   = []
ir-to-trace apply         = []

-- Recursion schemes: TODO via shared dispatcher.
ir-to-trace (In _ _)       = []
ir-to-trace (out-μ _)      = []
ir-to-trace (Cata _ _)     = []
ir-to-trace (Para _ _)     = []
ir-to-trace (Out _)        = []
ir-to-trace (in-ν _ _)     = []
ir-to-trace (Ana _ _)      = []
ir-to-trace (Hylo _ _ _ _) = []
ir-to-trace (Fuse _ _ _ _) = []

-- Heap & SigOp: TODO (per-arch SigOp dispatch lives in compile-ir).
ir-to-trace (free-heap _) = []
ir-to-trace (SigOp _)     = []
