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
open import Data.Bool using (false; true)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (LocState; AllocState; halted; regs; readReg; Input1; Output; Scratch;
         sv-as-loc; sucLoc; StoredValue; ValueLocation; AtStack; AtDynamic;
         RegOp; exec-reg-op; AbstractTrace;
         instr-reg-op; input2-inc; load-indirect-suc; mov-to-input; scratch-zero;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero;
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

  -- The descend body's resulting state: `input2-inc` (depth++) then
  -- `load-indirect-suc` (Output := child) then `mov-to-input` (Input1 :=
  -- child), all straight. Named so it can appear in result types.
  body-result : AbstractTrace → FlatState → FlatState
  body-result prog fs =
    flat-exec-instr mov-to-input prog
      (flat-exec-instr load-indirect-suc prog
        (flat-exec-instr (instr-reg-op input2-inc) prog fs))

  -- The whole 3-instr body preserves `halted` (given Input1 a pointer +
  -- the child cell present, so `load-indirect-suc` doesn't halt). `mov-to
  -- -input`/`input2-inc` are reg-ops (preserve `halted` definitionally);
  -- the `load` goes through `load-suc-keeps-halted` at the post-`input2-
  -- inc` state, where `ptr`/`child` (about `fs`) transfer (input2-inc
  -- leaves Input1 + memory). Reused as `descend-post`'s `halted` premise.
  body-keeps-halted : ∀ (prog : AbstractTrace) (fs : FlatState)
                        (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → halted (floc (body-result prog fs)) ≡ halted (floc fs)
  body-keeps-halted prog fs loc v ptr child =
    load-suc-keeps-halted
      (floc (flat-exec-instr (instr-reg-op input2-inc) prog fs))
      (falloc (flat-exec-instr (instr-reg-op input2-inc) prog fs))
      loc v ptr
      (trans (reg-op-keeps-readLoc input2-inc (floc fs) (sucLoc loc)) child)

  -- The descend body's three straight steps, as a `FlatSteps`-of-3.
  -- Links 1,2 preserve `halted` definitionally (reg/mem updates);
  -- link 3 (after `load`) goes through `body-keeps-halted`. `ptr`/
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
    → FlatSteps prog 3 fs (body-result prog fs)
  descend-body-flat prog fs loc v hf ptr child f0 f1 f2 =
      (hf , f0)
    ∷ (hf , f1)
    ∷ (trans (body-keeps-halted prog fs loc v ptr child) hf , f2)
    ∷ []

  -- The descend iteration's PRE-control: the three control instructions a
  -- continue (non-base, non-exhausted) step runs before the body —
  -- `c-label ld-top` (loop head), `c-branch-scratch-zero ld-end` (NOT
  -- taken: depth ≠ 0), `c-branch-tag-zero ld-base` (NOT taken: tag ≠ 0,
  -- i.e. an `inr`/cons node). All control instrs touch only `fpc`, so the
  -- state stays `fs` with the pc advanced 3×, and the branch conditions
  -- (over the VARIABLE `floc fs`) transfer to each intermediate state
  -- definitionally. Each step names its clean result via the matching
  -- `FlatStepsAPI` control-flow lemma (`flat-step1`) — no per-site
  -- `rewrite`/`subst` fights with the stuck `do-branch` reductions.
  descend-pre-flat : ∀ (prog : AbstractTrace) (fs : FlatState)
                       (ld-top ld-end ld-base : ℕ)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → tag-zf (flat-read-tag (floc fs)) ≡ false
    → fetch prog (fpc fs)                   ≡ just (instr-ctrl (c-label ld-top))
    → fetch prog (suc (fpc fs))             ≡ just (instr-ctrl (c-branch-scratch-zero ld-end))
    → fetch prog (suc (suc (fpc fs)))       ≡ just (instr-ctrl (c-branch-tag-zero ld-base))
    → FlatSteps prog 3 fs (record fs { fpc = suc (suc (suc (fpc fs))) })
  descend-pre-flat prog fs ld-top ld-end ld-base hf scond tcond fL fB1 fB2 =
    FlatSteps-++
      (flat-step1 hf  fL  (flat-label                prog fs ld-top))
      (FlatSteps-++
        (flat-step1 hf fB1 (flat-scratch-branch-not  prog _  ld-end  scond))
        (flat-step1 hf fB2 (flat-tag-branch-not      prog _  ld-base tcond)))

  -- The descend iteration's POST-control, for the continue (inr/cons)
  -- path: `c-jmp ld-de` (skip the inl handler) → `c-label ld-de` → `c-jmp
  -- ld-top` (loop back). The two jumps resolve via `find-label`, so this
  -- is parameterized over the label-RESOLUTION facts (`find-label prog ld
  -- ≡ just q` + the `fetch`es at `q`); `find-label` computation is
  -- localized to the concrete-prog assembly, NOT spread through the step
  -- reasoning. Result pc = `q-top` (the resolved loop head) — so the
  -- iteration returns to where it began (the fixpoint the μ-induction
  -- folds over). State stays `fs` (jumps/labels touch only `fpc`).
  descend-post-flat : ∀ (prog : AbstractTrace) (fs : FlatState)
                        (ld-de ld-top q-de q-top : ℕ)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs)        ≡ just (instr-ctrl (c-jmp ld-de))
    → find-label prog ld-de      ≡ just q-de
    → fetch prog q-de            ≡ just (instr-ctrl (c-label ld-de))
    → fetch prog (suc q-de)      ≡ just (instr-ctrl (c-jmp ld-top))
    → find-label prog ld-top     ≡ just q-top
    → FlatSteps prog 3 fs (record fs { fpc = q-top })
  descend-post-flat prog fs ld-de ld-top q-de q-top hf fJ1 de-res fL fJ2 top-res =
    FlatSteps-++
      (flat-step1 hf  fJ1 (trans (flat-jmp prog fs ld-de)
                                 (cong (λ m → do-jump m fs) de-res)))
      (FlatSteps-++
        (flat-step1 hf fL  (flat-label prog (record fs { fpc = q-de }) ld-de))
        (flat-step1 hf fJ2 (trans (flat-jmp prog (record fs { fpc = suc q-de }) ld-top)
                                  (cong (λ m → do-jump m (record fs { fpc = suc q-de })) top-res))))

  -- ONE continue (inr/cons) descend iteration: pre-control (3) ++ body
  -- (3) ++ post-control (3) = 9 steps, from the loop head `fs` back to
  -- the loop head (`fpc = q-top`, the resolved `ld-top`) with depth++ and
  -- Input1 := child (the `body-result` state). The three pieces compose
  -- via `FlatSteps-++`: end-of-pre = `record fs {fpc = +3}` = body's
  -- start; end-of-body = `body-result …` = post's start (its `halted`
  -- premise via `body-keeps-halted`). The result `record (body-result …)
  -- {fpc = q-top}` is the next iteration's input — the fixpoint the
  -- μ-induction over the cons-depth folds across.
  descend-iter-flat : ∀ (prog : AbstractTrace) (fs : FlatState)
                        (ld-top ld-end ld-inl ld-de q-de q-top : ℕ)
                        (loc : ValueLocation FS) (v : StoredValue FS)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → tag-zf (flat-read-tag (floc fs)) ≡ false
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → fetch prog (fpc fs)                               ≡ just (instr-ctrl (c-label ld-top))
    → fetch prog (suc (fpc fs))                         ≡ just (instr-ctrl (c-branch-scratch-zero ld-end))
    → fetch prog (suc (suc (fpc fs)))                   ≡ just (instr-ctrl (c-branch-tag-zero ld-inl))
    → fetch prog (suc (suc (suc (fpc fs))))             ≡ just (instr-reg-op input2-inc)
    → fetch prog (suc (suc (suc (suc (fpc fs)))))       ≡ just load-indirect-suc
    → fetch prog (suc (suc (suc (suc (suc (fpc fs)))))) ≡ just mov-to-input
    → fetch prog (suc (suc (suc (suc (suc (suc (fpc fs))))))) ≡ just (instr-ctrl (c-jmp ld-de))
    → find-label prog ld-de   ≡ just q-de
    → fetch prog q-de         ≡ just (instr-ctrl (c-label ld-de))
    → fetch prog (suc q-de)   ≡ just (instr-ctrl (c-jmp ld-top))
    → find-label prog ld-top  ≡ just q-top
    → FlatSteps prog 9 fs (record (body-result prog (record fs { fpc = suc (suc (suc (fpc fs))) })) { fpc = q-top })
  descend-iter-flat prog fs ld-top ld-end ld-inl ld-de q-de q-top loc v
                    hf scond tcond ptr child fL0 fB0 fB1 fi fl fm fJ1 de-res fLde fJ2 top-res =
    FlatSteps-++
      (descend-pre-flat prog fs ld-top ld-end ld-inl hf scond tcond fL0 fB0 fB1)
      (FlatSteps-++
        (descend-body-flat prog fsB loc v hf ptr child fi fl fm)
        (descend-post-flat prog (body-result prog fsB) ld-de ld-top q-de q-top
          (trans (body-keeps-halted prog fsB loc v ptr child) hf)
          fJ1 de-res fLde fJ2 top-res))
    where
      fsB : FlatState
      fsB = record fs { fpc = suc (suc (suc (fpc fs))) }

  -- The descend loop's BASE/EXIT path, for a base (inl, tag = 0) node with
  -- the depth counter still nonzero: `c-label ld-top` → `branch-scratch`
  -- (not taken) → `branch-tag` TAKEN (jump `ld-inl`) → `c-label ld-inl` →
  -- `scratch-zero` (Scratch := 0, the only state change) → `c-label ld-de`
  -- → `c-jmp ld-top` → `c-label ld-top` → `branch-scratch` TAKEN now
  -- (Scratch = 0, jump `ld-end`). 9 steps, ending poised at `ld-end`
  -- (descend done) with the depth counter frozen. `halted` threads through
  -- `scratch-zero` definitionally (`exec-reg-op` touches only `regs`). The
  -- post-`scratch-zero` Scratch = 0 fact drives the exit branch.
  descend-base-flat : ∀ (prog : AbstractTrace) (fs : FlatState)
                        (ld-top ld-end ld-inl ld-de q-inl q-top q-end : ℕ)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → tag-zf (flat-read-tag (floc fs)) ≡ true
    → sv-is-zero (readReg (regs (exec-reg-op scratch-zero (floc fs))) Scratch) ≡ true
    → fetch prog (fpc fs)             ≡ just (instr-ctrl (c-label ld-top))
    → fetch prog (suc (fpc fs))       ≡ just (instr-ctrl (c-branch-scratch-zero ld-end))
    → fetch prog (suc (suc (fpc fs))) ≡ just (instr-ctrl (c-branch-tag-zero ld-inl))
    → find-label prog ld-inl          ≡ just q-inl
    → fetch prog q-inl                ≡ just (instr-ctrl (c-label ld-inl))
    → fetch prog (suc q-inl)          ≡ just (instr-reg-op scratch-zero)
    → fetch prog (suc (suc q-inl))    ≡ just (instr-ctrl (c-label ld-de))
    → fetch prog (suc (suc (suc q-inl))) ≡ just (instr-ctrl (c-jmp ld-top))
    → find-label prog ld-top          ≡ just q-top
    → fetch prog q-top                ≡ just (instr-ctrl (c-label ld-top))
    → fetch prog (suc q-top)          ≡ just (instr-ctrl (c-branch-scratch-zero ld-end))
    → find-label prog ld-end          ≡ just q-end
    → FlatSteps prog 9 fs (record (record fs { floc = exec-reg-op scratch-zero (floc fs) }) { fpc = q-end })
  descend-base-flat prog fs ld-top ld-end ld-inl ld-de q-inl q-top q-end
                    hf scond tcond szcond fL fBs fBt il-res fLi fSz fLd fJt tl-res fLt2 fBs2 el-res =
    FlatSteps-++ st1 (FlatSteps-++ st2 (FlatSteps-++ st3 (FlatSteps-++ st4
      (FlatSteps-++ st5 (FlatSteps-++ st6 (FlatSteps-++ st7 (FlatSteps-++ st8 st9)))))))
    where
      s1 : LocState FS
      s1 = exec-reg-op scratch-zero (floc fs)
      A1 = record fs { fpc = suc (fpc fs) }
      A2 = record fs { fpc = suc (suc (fpc fs)) }
      A3 = record fs { fpc = q-inl }
      A5 = record (record fs { floc = s1 }) { fpc = suc (suc q-inl) }
      A6 = record (record fs { floc = s1 }) { fpc = suc (suc (suc q-inl)) }
      A7 = record (record fs { floc = s1 }) { fpc = q-top }
      A8 = record (record fs { floc = s1 }) { fpc = suc q-top }
      st1 = flat-step1 hf fL   (flat-label prog fs ld-top)
      st2 = flat-step1 hf fBs  (flat-scratch-branch-not prog A1 ld-end scond)
      st3 = flat-step1 hf fBt  (trans (flat-tag-branch-yes prog A2 ld-inl tcond)
                                      (cong (λ m → do-jump m A2) il-res))
      st4 = flat-step1 hf fLi  (flat-label prog A3 ld-inl)
      st5 = flat-step1 hf fSz  refl
      st6 = flat-step1 hf fLd  (flat-label prog A5 ld-de)
      st7 = flat-step1 hf fJt  (trans (flat-jmp prog A6 ld-top)
                                      (cong (λ m → do-jump m A6) tl-res))
      st8 = flat-step1 hf fLt2 (flat-label prog A7 ld-top)
      st9 = flat-step1 hf fBs2 (trans (flat-scratch-branch-yes prog A8 ld-end szcond)
                                      (cong (λ m → do-jump m A8) el-res))
