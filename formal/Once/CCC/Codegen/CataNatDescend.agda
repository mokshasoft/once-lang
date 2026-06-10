-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatDescend — the strat-nat cata DESCEND phase,
-- toward discharging `cata-traces-agree`/`cata-value-realized` (the live
-- `cata-correct` obligation in IRObsCorrectFlat).
--
-- Built on the `exec-flat` step API (FlatStepLemmas), using the deleted
-- `CataIsEvenInduction` POC only as a technique reference.
--
-- First piece: the descend BODY — the three straight instructions a
-- cons (`inr`) node runs each iteration: `input2-inc` (depth++),
-- `load-indirect-suc` (Output := child = *(Input1[1])), `mov-to-input`
-- (Input1 := child). `load-indirect-suc` HALTS unless Input1 is a
-- pointer AND the child cell exists, so both hypotheses are required
-- (cf. the template's mem preconditions). All over OPAQUE `FlatState`.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatDescend where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (LocState; AllocState; halted; regs; readReg; Input1; Output;
         sv-as-loc; sucLoc; StoredValue; ValueLocation; AtStack; AtDynamic;
         RegOp; exec-reg-op; AbstractTrace;
         instr-reg-op; input2-inc; load-indirect-suc; mov-to-input;
         module AbstractExec; module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module CataNatDescend {FS : FrameSemantics} where
  open FlatMachine {FS}
  open AbstractExec {FS} using (exec-abstract)
  open MemOps {FS} using (readLoc)
  open FlatStepsAPI {FS}

  -- `load-indirect-suc` preserves `halted` when Input1 is a pointer
  -- (`loc`) AND the child cell `*(loc+1)` exists (`v`). Stated over a
  -- VARIABLE state `s` (so `readReg`/`readLoc` don't pre-reduce and the
  -- `rewrite`s of the hypotheses fire).
  load-suc-keeps-halted : ∀ (s : LocState FS) (alloc : AllocState {FS})
                            (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs s) Input1) ≡ just loc
    → readLoc s (sucLoc loc) ≡ just v
    → halted (proj₁ (exec-abstract load-indirect-suc s alloc)) ≡ halted s
  load-suc-keeps-halted s alloc loc v p1 p2 rewrite p1 | p2 = refl

  -- `exec-reg-op` preserves memory reads (it touches only `regs`), so the
  -- `child`-cell hypothesis about `fs` transfers across `input2-inc`.
  -- Cases on the location (`readLoc` matches it); `stackMem`/`heapMem`
  -- are unchanged by a `regs`-only record update.
  reg-op-keeps-readLoc : ∀ (op : RegOp) (s : LocState FS) (loc : ValueLocation FS)
                       → readLoc (exec-reg-op op s) loc ≡ readLoc s loc
  reg-op-keeps-readLoc op s (AtStack f k) = refl
  reg-op-keeps-readLoc op s (AtDynamic hl) = refl

  -- The descend body's three straight steps, as a `FlatSteps`-of-3.
  -- Links 1,2 preserve `halted` definitionally (reg/mem updates);
  -- link 3 (after `load`) goes through `load-suc-keeps-halted`. `ptr`/
  -- `child` are about `fs`, but `input2-inc` preserves Input1 and memory,
  -- so they reduce to the post-`input2-inc` state's reads.
  descend-body-flat : ∀ (prog : AbstractTrace) (fs : FlatState)
                        (loc : ValueLocation FS) (v : StoredValue FS)
    → halted (floc fs) ≡ false
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → fetch prog (fpc fs)             ≡ just (instr-reg-op input2-inc)
    → fetch prog (suc (fpc fs))       ≡ just load-indirect-suc
    → fetch prog (suc (suc (fpc fs))) ≡ just mov-to-input
    → FlatSteps prog 3 fs
        (flat-exec-instr mov-to-input prog
          (flat-exec-instr load-indirect-suc prog
            (flat-exec-instr (instr-reg-op input2-inc) prog fs)))
  descend-body-flat prog fs loc v hf ptr child f0 f1 f2 =
      (hf , f0)
    ∷ (hf , f1)
    ∷ (trans (load-suc-keeps-halted
                (floc (flat-exec-instr (instr-reg-op input2-inc) prog fs))
                (falloc (flat-exec-instr (instr-reg-op input2-inc) prog fs))
                loc v ptr
                (trans (reg-op-keeps-readLoc input2-inc (floc fs) (sucLoc loc)) child)) hf
      , f2)
    ∷ []
