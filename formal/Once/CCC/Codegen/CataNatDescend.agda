-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatDescend — the strat-nat cata DESCEND phase,
-- toward discharging `cata-traces-agree`/`cata-value-realized` (the live
-- `cata-correct` obligation in IRObsCorrectFlat).
--
-- Built on the `exec-flat` step API (FlatStepLemmas), using the deleted
-- `CataIsEvenInduction` POC only as a technique reference.
--
-- First piece: the descend BODY — the three straight instructions a
-- cons (`inr`) node runs each iteration: `count-inc` (depth++),
-- `load-indirect-suc` (Output := child = *(Input1[1])), `mov-to-input`
-- (Input1 := child). `load-indirect-suc` HALTS unless Input1 is a
-- pointer AND the child cell exists, so both hypotheses are required
-- (cf. the template's mem preconditions). All over OPAQUE `FlatState`.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatDescend where

open import Once.CCC.Label using (LabelId)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (false; true)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (LocState; AllocState; halted; regs; readReg; Input1; Input2; Output; Scratch;
         writeReg; writeReg-same; writeReg-preserves; sv-succ; SV-Tag;
         sv-as-loc; sucLoc; StoredValue; ValueLocation; AtStack; AtDynamic;
         RegOp; exec-reg-op; AbstractTrace;
         instr-reg-op; count-inc; load-indirect-suc; mov-to-input; scratch-zero;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero;
         module AbstractExec; module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)

module CataNatDescend {FS : FrameSemantics} where
  open FlatMachine {FS}
  open AbstractExec {FS} using (exec-abstract)
  open MemOps {FS} using (readLoc)
  open FlatStepsAPI {FS}
  open FlatEventTrace {FS}

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
  -- `child`-cell hypothesis about `fs` transfers across `count-inc`.
  -- Cases on the location (`readLoc` matches it); `stackMem`/`heapMem`
  -- are unchanged by a `regs`-only record update.
  reg-op-keeps-readLoc : ∀ (op : RegOp) (s : LocState FS) (loc : ValueLocation FS)
                       → readLoc (exec-reg-op op s) loc ≡ readLoc s loc
  reg-op-keeps-readLoc op s (AtStack f k) = refl
  reg-op-keeps-readLoc op s (AtDynamic hl) = refl

  -- The descend body's resulting state: `count-inc` (depth++) then
  -- `load-indirect-suc` (Output := child) then `mov-to-input` (Input1 :=
  -- child), all straight. Named so it can appear in result types.
  body-result : AbstractTrace → FlatState → FlatState
  body-result prog fs =
    flat-exec-instr mov-to-input prog
      (flat-exec-instr load-indirect-suc prog
        (flat-exec-instr (instr-reg-op count-inc) prog fs))

  -- `count-inc` preserves the Input1 register (it writes Input2).
  input2-keeps-input1 : ∀ (s : LocState FS)
                      → readReg (regs (exec-reg-op count-inc s)) Input1 ≡ readReg (regs s) Input1
  input2-keeps-input1 s =
    writeReg-preserves (regs s) Input2 Input1 (sv-succ (readReg (regs s) Input2)) (λ ())

  -- The body leaves Input1 pointing at the child: `count-inc` preserves
  -- Input1, `load-indirect-suc` puts the child (`*(Input1+1)`) in Output,
  -- `mov-to-input` copies Output to Input1. So `body-result`'s Input1 = the
  -- child pointer `v`. This is the REGISTER INVARIANT the descend loop
  -- maintains (Input1 advances to the next cell each iteration). The two
  -- rewrites relocate the cons facts across `count-inc` (Input1-read +
  -- memory preserved); the load + mov then reduce definitionally.
  body-input1 : ∀ (prog : AbstractTrace) (fs : FlatState)
                  (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → readReg (regs (floc (body-result prog fs))) Input1 ≡ v
  body-input1 prog fs loc v ptr child
    rewrite trans (cong sv-as-loc (input2-keeps-input1 (floc fs))) ptr
          | trans (reg-op-keeps-readLoc count-inc (floc fs) (sucLoc loc)) child = refl

  -- The body PRESERVES the Scratch register (it writes only Input2 /
  -- Output / Input1) — so the descend's depth-counter condition (Scratch ≠
  -- 0, set by `scratch-one`) holds across every continue iteration. After
  -- the same load-reducing rewrites, three `writeReg-preserves` peel
  -- Input1 / Output / Input2 off the Scratch read.
  body-scratch : ∀ (prog : AbstractTrace) (fs : FlatState)
                   (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → readReg (regs (floc (body-result prog fs))) Scratch ≡ readReg (regs (floc fs)) Scratch
  body-scratch prog fs loc v ptr child
    rewrite trans (cong sv-as-loc (input2-keeps-input1 (floc fs))) ptr
          | trans (reg-op-keeps-readLoc count-inc (floc fs) (sucLoc loc)) child =
    trans (writeReg-preserves R2 Input1 Scratch v (λ ()))
          (trans (writeReg-preserves R1 Output Scratch v (λ ()))
                 (writeReg-preserves R0 Input2 Scratch succ-v (λ ())))
    where
      R0 = regs (floc fs)
      succ-v = sv-succ (readReg R0 Input2)
      R1 = writeReg R0 Input2 succ-v
      R2 = writeReg R1 Output v

  -- The body PRESERVES memory (`readLoc` at any location): all three
  -- instructions write only registers. After the load-reducing rewrites,
  -- `floc (body-result …)` is a chain of register updates over `floc fs`,
  -- so it agrees on `stackMem`/`heapMem` — `refl` per location shape.
  body-readLoc : ∀ (prog : AbstractTrace) (fs : FlatState)
                   (loc : ValueLocation FS) (v : StoredValue FS) (loc' : ValueLocation FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → readLoc (floc (body-result prog fs)) loc' ≡ readLoc (floc fs) loc'
  body-readLoc prog fs loc v loc' ptr child
    rewrite trans (cong sv-as-loc (input2-keeps-input1 (floc fs))) ptr
          | trans (reg-op-keeps-readLoc count-inc (floc fs) (sucLoc loc)) child
    with loc'
  ... | AtStack f k = refl
  ... | AtDynamic hl = refl

  -- The whole 3-instr body preserves `halted` (given Input1 a pointer +
  -- the child cell present, so `load-indirect-suc` doesn't halt). `mov-to
  -- -input`/`count-inc` are reg-ops (preserve `halted` definitionally);
  -- the `load` goes through `load-suc-keeps-halted` at the post-`input2-
  -- inc` state, where `ptr`/`child` (about `fs`) transfer (count-inc
  -- leaves Input1 + memory). Reused as `descend-post`'s `halted` premise.
  body-keeps-halted : ∀ (prog : AbstractTrace) (fs : FlatState)
                        (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → halted (floc (body-result prog fs)) ≡ halted (floc fs)
  body-keeps-halted prog fs loc v ptr child =
    load-suc-keeps-halted
      (floc (flat-exec-instr (instr-reg-op count-inc) prog fs))
      (falloc (flat-exec-instr (instr-reg-op count-inc) prog fs))
      loc v ptr
      (trans (reg-op-keeps-readLoc count-inc (floc fs) (sucLoc loc)) child)

  -- The descend loop-head→loop-head state transform: one continue
  -- iteration's result state (= `descend-iter-flat`'s result). `fpc` is
  -- reset to the loop head `q-top` by construction; `floc` is the body's.
  desc-step : AbstractTrace → ℕ → FlatState → FlatState
  desc-step prog q-top fs =
    record (body-result prog (record fs { fpc = suc (suc (suc (fpc fs))) })) { fpc = q-top }

  -- The state family's INVARIANT MAINTENANCE: across one iteration, Input1
  -- advances to the child pointer, Scratch is preserved (depth counter),
  -- and halted stays false. (`floc (desc-step …) = floc (body-result …)`
  -- since the `{fpc = q-top}` update preserves `floc`; then the body
  -- lemmas, whose `fs` is `record fs {fpc = …}` with the same `floc`.)
  desc-step-input1 : ∀ (prog : AbstractTrace) (q-top : ℕ) (fs : FlatState)
                       (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → readReg (regs (floc (desc-step prog q-top fs))) Input1 ≡ v
  desc-step-input1 prog q-top fs loc v ptr child =
    body-input1 prog (record fs { fpc = suc (suc (suc (fpc fs))) }) loc v ptr child

  desc-step-scratch : ∀ (prog : AbstractTrace) (q-top : ℕ) (fs : FlatState)
                        (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → readReg (regs (floc (desc-step prog q-top fs))) Scratch ≡ readReg (regs (floc fs)) Scratch
  desc-step-scratch prog q-top fs loc v ptr child =
    body-scratch prog (record fs { fpc = suc (suc (suc (fpc fs))) }) loc v ptr child

  desc-step-halted : ∀ (prog : AbstractTrace) (q-top : ℕ) (fs : FlatState)
                       (loc : ValueLocation FS) (v : StoredValue FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → halted (floc (desc-step prog q-top fs)) ≡ halted (floc fs)
  desc-step-halted prog q-top fs loc v ptr child =
    body-keeps-halted prog (record fs { fpc = suc (suc (suc (fpc fs))) }) loc v ptr child

  -- desc-step preserves memory — the memory-invariance the loop's
  -- HeapNatChain transfer (`HeapNatChain-cong`) consumes.
  desc-step-readLoc : ∀ (prog : AbstractTrace) (q-top : ℕ) (fs : FlatState)
                        (loc : ValueLocation FS) (v : StoredValue FS) (loc' : ValueLocation FS)
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → readLoc (floc (desc-step prog q-top fs)) loc' ≡ readLoc (floc fs) loc'
  desc-step-readLoc prog q-top fs loc v loc' ptr child =
    body-readLoc prog (record fs { fpc = suc (suc (suc (fpc fs))) }) loc v loc' ptr child

  -- `scratch-zero` sets Scratch := SV-Tag 0, so the descend-base exit
  -- branch fires: `sv-is-zero (SV-Tag 0) = true`. (The `szcond` premise of
  -- `descend-base-flat`.)
  scratch-zeroed : ∀ (ls : LocState FS)
    → sv-is-zero (readReg (regs (exec-reg-op scratch-zero ls)) Scratch) ≡ true
  scratch-zeroed ls = cong sv-is-zero (writeReg-same (regs ls) Scratch (SV-Tag 0))

  -- The descend body's three straight steps, as a `FlatSteps`-of-3.
  -- Links 1,2 preserve `halted` definitionally (reg/mem updates);
  -- link 3 (after `load`) goes through `body-keeps-halted`. `ptr`/
  -- `child` are about `fs`, but `count-inc` preserves Input1 and memory,
  -- so they reduce to the post-`count-inc` state's reads.
  descend-body-flat : ∀ (prog : AbstractTrace) (fs : FlatState)
                        (loc : ValueLocation FS) (v : StoredValue FS)
    → halted (floc fs) ≡ false
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → fetch prog (fpc fs)             ≡ just (instr-reg-op count-inc)
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
                       (ld-top ld-end ld-base : LabelId)
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
                        (ld-de ld-top : LabelId) (q-de q-top : ℕ)
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
                        (ld-top ld-end ld-inl ld-de : LabelId) (q-de q-top : ℕ)
                        (loc : ValueLocation FS) (v : StoredValue FS)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → tag-zf (flat-read-tag (floc fs)) ≡ false
    → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
    → readLoc (floc fs) (sucLoc loc) ≡ just v
    → fetch prog (fpc fs)                               ≡ just (instr-ctrl (c-label ld-top))
    → fetch prog (suc (fpc fs))                         ≡ just (instr-ctrl (c-branch-scratch-zero ld-end))
    → fetch prog (suc (suc (fpc fs)))                   ≡ just (instr-ctrl (c-branch-tag-zero ld-inl))
    → fetch prog (suc (suc (suc (fpc fs))))             ≡ just (instr-reg-op count-inc)
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
                        (ld-top ld-end ld-inl ld-de : LabelId) (q-inl q-top q-end : ℕ)
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

  -- THE DESCEND PHASE, assembled: descend a Nat value of cons-depth `n` by
  -- chaining `n` continue iterations (each `descend-iter-flat` at its
  -- depth, supplied as `iters d`) then the base/exit path (`base`,
  -- `descend-base-flat` at the base node). One `FlatSteps` chain of
  -- `n * 9 + 9` steps from the head state `st 0` to the descend-done state
  -- `final`. The combinators compose over the Nat recursion via
  -- `chain-steps`; the heap model (`ValidAtWF` for the Nat value) supplies
  -- the loop-head state family `st` and discharges each `iters d` / `base`.
  descend-loop-runs : ∀ (prog : AbstractTrace) (n : ℕ) (st : ℕ → FlatState) (final : FlatState)
                    → (∀ d → FlatSteps prog 9 (st d) (st (suc d)))
                    → FlatSteps prog 9 (st n) final
                    → FlatSteps prog (n * 9 + 9) (st 0) final
  descend-loop-runs prog n st final iters base =
    FlatSteps-++ (chain-steps 9 n st iters) base

  ----------------------------------------------------------------------
  -- The DESCEND phase emits NO SigOp events (trace-side `traces-agree`).
  --
  -- Every descend instruction (labels, branches, `count-inc`, `load-
  -- indirect-suc`, `mov-to-input`, jumps, `scratch-zero`) is non-`instr-
  -- sigop`, so `event-of … ≡ []` DEFINITIONALLY. We prove silence per-
  -- CHAIN (not via `flat-events-[]`): the surrounding `prog` also holds
  -- the algebra `at`, which DOES emit in the ascend phase, so `prog` is
  -- not globally silent. Mirrors `CataNatAscend`'s `ascend-pre-silent`
  -- idiom: `step1-silent` (one non-sigop step) + `++-silent` (compose).
  ----------------------------------------------------------------------

  -- A single non-`instr-sigop` step contributes nothing to the trace.
  step1-silent : ∀ {prog fs fs'} {i} (h : halted (floc fs) ≡ false)
                   (f : fetch prog (fpc fs) ≡ just i) (eq : flat-exec-instr i prog fs ≡ fs')
               → event-of i fs ≡ [] → chain-events (flat-step1 h f eq) ≡ []
  step1-silent {fs = fs} {i = i} h f eq ev =
    trans (chain-events-subst eq ((h , f) ∷ [])) (cong (_++ []) ev)

  -- The concatenation of two silent chains is silent.
  ++-silent : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
                (xs : FlatSteps prog k₁ fs₁ fs₂) (ys : FlatSteps prog k₂ fs₂ fs₃)
            → chain-events xs ≡ [] → chain-events ys ≡ []
            → chain-events (FlatSteps-++ xs ys) ≡ []
  ++-silent xs ys px py =
    trans (chain-events-++ xs ys) (trans (cong (_++ chain-events ys) px) py)

  -- The descend body's three straight steps (`count-inc`, `load-
  -- indirect-suc`, `mov-to-input`) all emit `[]` — `chain-events` of the
  -- raw cons-list reduces directly (no `subst` to step over).
  descend-body-silent : ∀ (prog : AbstractTrace) (fs : FlatState)
                          (loc : ValueLocation FS) (v : StoredValue FS)
    → (hf : halted (floc fs) ≡ false)
    → (ptr : sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc)
    → (child : readLoc (floc fs) (sucLoc loc) ≡ just v)
    → (f0 : fetch prog (fpc fs)             ≡ just (instr-reg-op count-inc))
    → (f1 : fetch prog (suc (fpc fs))       ≡ just load-indirect-suc)
    → (f2 : fetch prog (suc (suc (fpc fs))) ≡ just mov-to-input)
    → chain-events (descend-body-flat prog fs loc v hf ptr child f0 f1 f2) ≡ []
  descend-body-silent prog fs loc v hf ptr child f0 f1 f2 = refl

  -- The descend PRE-control (label + two not-taken branches) is silent.
  descend-pre-silent : ∀ (prog : AbstractTrace) (fs : FlatState) (ld-top ld-end ld-base : LabelId)
    → (hf : halted (floc fs) ≡ false)
    → (scond : sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false)
    → (tcond : tag-zf (flat-read-tag (floc fs)) ≡ false)
    → (fL  : fetch prog (fpc fs)             ≡ just (instr-ctrl (c-label ld-top)))
    → (fB1 : fetch prog (suc (fpc fs))       ≡ just (instr-ctrl (c-branch-scratch-zero ld-end)))
    → (fB2 : fetch prog (suc (suc (fpc fs))) ≡ just (instr-ctrl (c-branch-tag-zero ld-base)))
    → chain-events (descend-pre-flat prog fs ld-top ld-end ld-base hf scond tcond fL fB1 fB2) ≡ []
  descend-pre-silent prog fs ld-top ld-end ld-base hf scond tcond fL fB1 fB2 =
    trans (chain-events-++ S1 S23)
      (trans (cong (_++ chain-events S23) (step1-silent {prog = prog} hf fL eqL refl))
        (trans (chain-events-++ S2 S3)
          (cong₂ _++_
            (step1-silent {prog = prog} {fs = record fs { fpc = suc (fpc fs) }} hf fB1 eqB1 refl)
            (step1-silent {prog = prog} {fs = record fs { fpc = suc (suc (fpc fs)) }} hf fB2 eqB2 refl))))
    where
      eqL  = flat-label              prog fs ld-top
      eqB1 = flat-scratch-branch-not prog (record fs { fpc = suc (fpc fs) }) ld-end scond
      eqB2 = flat-tag-branch-not     prog (record fs { fpc = suc (suc (fpc fs)) }) ld-base tcond
      S1  = flat-step1 {prog = prog} hf fL eqL
      S2  = flat-step1 {prog = prog} hf fB1 eqB1
      S3  = flat-step1 {prog = prog} hf fB2 eqB2
      S23 = FlatSteps-++ S2 S3

  -- The descend POST-control (jmp ld-de → label ld-de → jmp ld-top) is silent.
  descend-post-silent : ∀ (prog : AbstractTrace) (fs : FlatState) (ld-de ld-top : LabelId) (q-de q-top : ℕ)
    → (hf : halted (floc fs) ≡ false)
    → (fJ1 : fetch prog (fpc fs)        ≡ just (instr-ctrl (c-jmp ld-de)))
    → (de-res : find-label prog ld-de   ≡ just q-de)
    → (fL : fetch prog q-de             ≡ just (instr-ctrl (c-label ld-de)))
    → (fJ2 : fetch prog (suc q-de)      ≡ just (instr-ctrl (c-jmp ld-top)))
    → (top-res : find-label prog ld-top ≡ just q-top)
    → chain-events (descend-post-flat prog fs ld-de ld-top q-de q-top hf fJ1 de-res fL fJ2 top-res) ≡ []
  descend-post-silent prog fs ld-de ld-top q-de q-top hf fJ1 de-res fL fJ2 top-res =
    trans (chain-events-++ S1 S23)
      (trans (cong (_++ chain-events S23) (step1-silent {prog = prog} hf fJ1 eq1 refl))
        (trans (chain-events-++ S2 S3)
          (cong₂ _++_
            (step1-silent {prog = prog} {fs = record fs { fpc = q-de }} hf fL eq2 refl)
            (step1-silent {prog = prog} {fs = record fs { fpc = suc q-de }} hf fJ2 eq3 refl))))
    where
      eq1 = trans (flat-jmp prog fs ld-de) (cong (λ m → do-jump m fs) de-res)
      eq2 = flat-label prog (record fs { fpc = q-de }) ld-de
      eq3 = trans (flat-jmp prog (record fs { fpc = suc q-de }) ld-top)
                  (cong (λ m → do-jump m (record fs { fpc = suc q-de })) top-res)
      S1  = flat-step1 {prog = prog} hf fJ1 eq1
      S2  = flat-step1 {prog = prog} hf fL eq2
      S3  = flat-step1 {prog = prog} hf fJ2 eq3
      S23 = FlatSteps-++ S2 S3

  -- ONE continue descend iteration (pre ++ body ++ post) is silent.
  descend-iter-silent : ∀ (prog : AbstractTrace) (fs : FlatState)
                          (ld-top ld-end ld-inl ld-de : LabelId) (q-de q-top : ℕ)
                          (loc : ValueLocation FS) (v : StoredValue FS)
    → (hf : halted (floc fs) ≡ false)
    → (scond : sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false)
    → (tcond : tag-zf (flat-read-tag (floc fs)) ≡ false)
    → (ptr : sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc)
    → (child : readLoc (floc fs) (sucLoc loc) ≡ just v)
    → (fL0 : fetch prog (fpc fs)                               ≡ just (instr-ctrl (c-label ld-top)))
    → (fB0 : fetch prog (suc (fpc fs))                         ≡ just (instr-ctrl (c-branch-scratch-zero ld-end)))
    → (fB1 : fetch prog (suc (suc (fpc fs)))                   ≡ just (instr-ctrl (c-branch-tag-zero ld-inl)))
    → (fi : fetch prog (suc (suc (suc (fpc fs))))             ≡ just (instr-reg-op count-inc))
    → (fl : fetch prog (suc (suc (suc (suc (fpc fs)))))       ≡ just load-indirect-suc)
    → (fm : fetch prog (suc (suc (suc (suc (suc (fpc fs)))))) ≡ just mov-to-input)
    → (fJ1 : fetch prog (suc (suc (suc (suc (suc (suc (fpc fs))))))) ≡ just (instr-ctrl (c-jmp ld-de)))
    → (de-res : find-label prog ld-de   ≡ just q-de)
    → (fLde : fetch prog q-de           ≡ just (instr-ctrl (c-label ld-de)))
    → (fJ2 : fetch prog (suc q-de)      ≡ just (instr-ctrl (c-jmp ld-top)))
    → (top-res : find-label prog ld-top ≡ just q-top)
    → chain-events (descend-iter-flat prog fs ld-top ld-end ld-inl ld-de q-de q-top loc v
                      hf scond tcond ptr child fL0 fB0 fB1 fi fl fm fJ1 de-res fLde fJ2 top-res) ≡ []
  descend-iter-silent prog fs ld-top ld-end ld-inl ld-de q-de q-top loc v
                      hf scond tcond ptr child fL0 fB0 fB1 fi fl fm fJ1 de-res fLde fJ2 top-res =
    ++-silent PRE (FlatSteps-++ BODY POST)
      (descend-pre-silent prog fs ld-top ld-end ld-inl hf scond tcond fL0 fB0 fB1)
      (++-silent BODY POST
        (descend-body-silent prog fsB loc v hf ptr child fi fl fm)
        (descend-post-silent prog (body-result prog fsB) ld-de ld-top q-de q-top
          (trans (body-keeps-halted prog fsB loc v ptr child) hf) fJ1 de-res fLde fJ2 top-res))
    where
      fsB : FlatState
      fsB = record fs { fpc = suc (suc (suc (fpc fs))) }
      PRE  = descend-pre-flat prog fs ld-top ld-end ld-inl hf scond tcond fL0 fB0 fB1
      BODY = descend-body-flat prog fsB loc v hf ptr child fi fl fm
      POST = descend-post-flat prog (body-result prog fsB) ld-de ld-top q-de q-top
               (trans (body-keeps-halted prog fsB loc v ptr child) hf) fJ1 de-res fLde fJ2 top-res

  -- `zero * k ≡ 0` for the CONSTRUCTOR `zero` (chain-steps's depth-0 length
  -- index). `*-zeroˡ` only covers the literal `0`, which reduces differently
  -- under this (2nd-argument-recursive) `_*_`; here we induct on `k` so each
  -- step reduces (`zero * suc k = zero + zero * k = zero * k`).
  zero-mul : ∀ (k : ℕ) → zero * k ≡ 0
  zero-mul zero    = refl
  zero-mul (suc k) = zero-mul k

  -- `chain-steps` of `n` silent iterations is silent (μ-induction on `n`).
  -- Length `k` is kept a VARIABLE (not the literal `9`): the depth-0 chain
  -- has length `zero * k`, and `*-zeroˡ k` reduces that uniformly — whereas
  -- a literal `zero * 9` stays stuck under this (2nd-argument-recursive)
  -- `_*_`. The base then retypes the length to `0` (`chain-events-subst-
  -- len`) so `chain-events-len0` applies.
  chain-steps-silent : ∀ (prog : AbstractTrace) (k n : ℕ) (st : ℕ → FlatState)
                         (iters : ∀ d → FlatSteps prog k (st d) (st (suc d)))
                     → (∀ d → chain-events (iters d) ≡ [])
                     → chain-events (chain-steps k n st iters) ≡ []
  chain-steps-silent prog k zero    st iters isil =
    trans (sym (chain-events-subst-len eq (chain-steps k zero st iters)))
          (chain-events-len0
            (subst (λ m → FlatSteps prog m (st 0) (st zero)) eq
                   (chain-steps k zero st iters)))
    where
      eq : zero * k ≡ 0
      eq = zero-mul k
  chain-steps-silent prog k (suc m) st iters isil =
    ++-silent (iters 0) (chain-steps k m (λ d → st (suc d)) (λ d → iters (suc d)))
      (isil 0)
      (chain-steps-silent prog k m (λ d → st (suc d)) (λ d → iters (suc d)) (λ d → isil (suc d)))

  -- THE DESCEND PHASE emits no events: `n` silent continue iterations
  -- (`chain-steps-silent`) ++ the silent base/exit path (hypothesis,
  -- supplied by the full-cata assembly via `descend-base-flat` silence).
  descend-loop-silent : ∀ (prog : AbstractTrace) (n : ℕ) (st : ℕ → FlatState) (final : FlatState)
                          (iters : ∀ d → FlatSteps prog 9 (st d) (st (suc d)))
                          (base : FlatSteps prog 9 (st n) final)
                      → (∀ d → chain-events (iters d) ≡ [])
                      → chain-events base ≡ []
                      → chain-events (descend-loop-runs prog n st final iters base) ≡ []
  descend-loop-silent prog n st final iters base isil bsil =
    ++-silent (chain-steps 9 n st iters) base
      (chain-steps-silent prog 9 n st iters isil)
      bsil
