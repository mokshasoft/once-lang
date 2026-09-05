-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.ValidAtWFHalted
--
-- Plan 0.32 choice (a), migration step 2: `ValidAtWF` is invariant under
-- the `halted` flag.
--
-- WHY: the `exec-trace-is-flat` bridge equates the flat machine's final
-- state with `exec-trace`'s only up to `forced` (halted := true) — because
-- `exec-flat` halts at end-of-program while `exec-trace` does not. To
-- transport a semantic-side `ValidAtWF` result across that bridge we need
-- it to ignore the `halted` field, which it does: every constructor reads
-- the state only through `readLoc`/`readReg` (which project
-- regs/stackMem/heapMem) and through state-independent
-- `BeforeFrontier`/`BodyCorrect`. A `halted` record-update preserves all
-- read fields definitionally, so the constructor premises pass through
-- unchanged; only nested `ValidAtWF` recurse.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.ValidAtWFHalted (o : CanonicalName) where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (LocState; halted; ValueLocation; sucLoc; module MemOps)
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
open import Once.CCC.Machine.Validity using (module ValidityDef)

module _ {FS : FrameSemantics} (program-bound : ℕ) where
  open ClosureWellFormedDef {FS} program-bound
  open MemOps {FS} using (readLoc)
  open ValidityDef {FS} program-bound using (readLoc-stack-heap-eq)

  -- `readLoc` ignores `halted`: a halted-update preserves stackMem/heapMem
  -- definitionally, so `readLoc-stack-heap-eq` collapses the two.
  rl : ∀ (s : LocState FS) (b : Bool) (loc : ValueLocation FS)
    → readLoc (record s { halted = b }) loc ≡ readLoc s loc
  rl s b loc = readLoc-stack-heap-eq (record s { halted = b }) s loc refl refl


  -- Setting `halted` to any `b` preserves `ValidAtWF`. (`forced` in the
  -- flat machine is the `b = true` instance.)
  validAtWF-set-halted : ∀ {m alloc A} {v : ⟦ A ⟧} {loc s} (b : Bool)
    → ValidAtWF m alloc {A} v loc s
    → ValidAtWF m alloc {A} v loc (record s { halted = b })
  validAtWF-set-halted b valid-unit-wf = valid-unit-wf
  validAtWF-set-halted {s = s} b (valid-pair-wf {pair-loc = pl} lm r1 r2 bf1 bf2 bf3 va vb) =
    valid-pair-wf lm (trans (rl s b pl) r1) (trans (rl s b (sucLoc pl)) r2) bf1 bf2 bf3
      (validAtWF-set-halted b va) (validAtWF-set-halted b vb)
  validAtWF-set-halted {s = s} b (valid-closure-wf body<bound {closure-loc = cl} lm r1 r2 bf1 bf2 venv bodyc) =
    valid-closure-wf body<bound lm (trans (rl s b cl) r1) (trans (rl s b (sucLoc cl)) r2) bf1 bf2
      (validAtWF-set-halted b venv) bodyc
  validAtWF-set-halted {s = s} b (valid-inl-wf {sum-loc = sl} lm tg r bf1 bf2 va) =
    valid-inl-wf lm (transport-SumTag (rl s b sl) tg) (trans (rl s b (sucLoc sl)) r) bf1 bf2 (validAtWF-set-halted b va)
  validAtWF-set-halted {s = s} b (valid-inr-wf {sum-loc = sl} lm tg r bf1 bf2 vb) =
    valid-inr-wf lm (transport-SumTag (rl s b sl) tg) (trans (rl s b (sucLoc sl)) r) bf1 bf2 (validAtWF-set-halted b vb)
  -- Stage F: an inline payload has no sub-validity to transport, so these
  -- two clauses are the pointer ones minus the recursive call.
  validAtWF-set-halted {s = s} b (valid-inl-reg-wf {sum-loc = sl} lm tg fit r bf) =
    valid-inl-reg-wf lm (transport-SumTag (rl s b sl) tg) fit (trans (rl s b (sucLoc sl)) r) bf
  validAtWF-set-halted {s = s} b (valid-inr-reg-wf {sum-loc = sl} lm tg fit r bf) =
    valid-inr-reg-wf lm (transport-SumTag (rl s b sl) tg) fit (trans (rl s b (sucLoc sl)) r) bf
  validAtWF-set-halted b (valid-μ-wf wf x v) =
    valid-μ-wf wf x (validAtWF-set-halted b v)
  validAtWF-set-halted b (valid-ν-wf wf x v) =
    valid-ν-wf wf x (validAtWF-set-halted b v)
  validAtWF-set-halted {s = s} b (valid-int-wf {loc = loc} bf r) = valid-int-wf bf (trans (rl s b loc) r)
  validAtWF-set-halted {s = s} b (valid-float-wf {loc = loc} bf r) = valid-float-wf bf (trans (rl s b loc) r)
  validAtWF-set-halted b (valid-str-wf bf) = valid-str-wf bf
  validAtWF-set-halted b (valid-buffer-wf bf) = valid-buffer-wf bf
