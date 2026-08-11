-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatHeap — the heap-model payoff: read the cata
-- descend's tag condition off a Heap-mode sum cell's `ValidAtWF` (Plan
-- 0.36 task #8).
--
-- The `ValidAtWF` cascade gave `valid-inr-wf`/`valid-inl-wf` a `SumTag`
-- field: in Heap mode the tag is `readLoc s sum-loc ≡ just (SV-Tag t)`
-- (1 = cons/inr, 0 = base/inl). These lemmas turn that, plus the Input1
-- pointer, into the `tcond` (`tag-zf (flat-read-tag …)`) that
-- `descend-iter-flat` (cons, ≠0) and `descend-base-flat` (base, =0)
-- require. `flat-read-tag (floc fs)` reads `*Input1`; the pointer fact
-- redirects it to `sum-loc`, the tag fact fixes the stored value, and
-- `tag-zf`/`sv-is-zero` decide.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatHeap where

open import Data.Bool using (true; false)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (regs; readReg; Input1; sv-as-loc; SV-Tag; ValueLocation; module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module CataNatHeap {FS : FrameSemantics} where
  open FlatMachine {FS}
  open MemOps {FS} using (readLoc)

  -- A cons cell (`SumTag Heap 1`): the descend's continue condition,
  -- `tag ≠ 0`. `flat-read-tag` redirects through the Input1 pointer to
  -- `readLoc … loc`, which the tag fact fixes to `SV-Tag 1`; `sv-is-zero
  -- (SV-Tag 1) = false`.
  cons-tcond : ∀ (fs : FlatState) (loc : ValueLocation FS)
             → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
             → readLoc (floc fs) loc ≡ just (SV-Tag 1)
             → tag-zf (flat-read-tag (floc fs)) ≡ false
  cons-tcond fs loc ptr tag rewrite ptr | tag = refl

  -- A base cell (`SumTag Heap 0`): the descend's exit condition, `tag = 0`.
  base-tcond : ∀ (fs : FlatState) (loc : ValueLocation FS)
             → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
             → readLoc (floc fs) loc ≡ just (SV-Tag 0)
             → tag-zf (flat-read-tag (floc fs)) ≡ true
  base-tcond fs loc ptr tag rewrite ptr | tag = refl
