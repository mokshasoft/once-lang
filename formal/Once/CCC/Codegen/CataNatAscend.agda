-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatAscend — the strat-nat cata ASCEND phase's
-- CONTROL wrappers, toward discharging `cata-correct` (IRObsCorrectFlat).
--
-- The ascend loop (cata-trace-nat) is
--   c-label la-top ∷ c-branch-scratch-zero la-end ∷
--   (ascend-body ++ (c-jmp la-top ∷ c-label la-end ∷ []))
-- where `ascend-body = mov-to-input ∷ build-layer 1 ++ (mov-to-input ∷ at
-- ++ (scratch-dec ∷ []))`. Each continue iteration rebuilds one `inr`
-- layer and runs the algebra `at`, decrementing the depth counter.
--
-- This module builds the iteration's PRE-control (`c-label la-top` +
-- `c-branch-scratch-zero la-end` NOT taken, i.e. depth ≠ 0) and the
-- POST-control (`c-jmp la-top`, loop back), via the same `flat-step1` +
-- label-resolution-fact idiom as `CataNatDescend`. This isolates the
-- remaining semantic gap to the iteration's MIDDLE (`build-layer` block +
-- the abstract algebra trace `at`, which carries the SigOp content) — the
-- crux of `traces-agree`, deferred to the `at`-semantics build.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatAscend where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Scratch; AbstractTrace;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module CataNatAscend {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}

  -- The ascend iteration's PRE-control (continue path, depth ≠ 0):
  -- `c-label la-top` (loop head) then `c-branch-scratch-zero la-end` NOT
  -- taken. Both touch only `fpc`; state stays `fs`, pc advances 2×. The
  -- branch condition is over the VARIABLE `floc fs`, so it transfers to
  -- the post-label state definitionally.
  ascend-pre-flat : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top la-end : ℕ)
    → halted (floc fs) ≡ false
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → fetch prog (fpc fs)       ≡ just (instr-ctrl (c-label la-top))
    → fetch prog (suc (fpc fs)) ≡ just (instr-ctrl (c-branch-scratch-zero la-end))
    → FlatSteps prog 2 fs (record fs { fpc = suc (suc (fpc fs)) })
  ascend-pre-flat prog fs la-top la-end hf scond fL fB =
    FlatSteps-++
      (flat-step1 hf fL (flat-label               prog fs la-top))
      (flat-step1 hf fB (flat-scratch-branch-not  prog _  la-end scond))

  -- The ascend iteration's POST-control: `c-jmp la-top` (loop back). The
  -- jump resolves via `find-label`, so it is parameterized over the
  -- resolution fact (`find-label prog la-top ≡ just q-latop`); result pc =
  -- `q-latop` (the resolved loop head) — the fixpoint the descending-depth
  -- induction folds over. State stays `fs` (the jump touches only `fpc`).
  ascend-post-flat : ∀ (prog : AbstractTrace) (fs : FlatState) (la-top q-latop : ℕ)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs)    ≡ just (instr-ctrl (c-jmp la-top))
    → find-label prog la-top ≡ just q-latop
    → FlatSteps prog 1 fs (record fs { fpc = q-latop })
  ascend-post-flat prog fs la-top q-latop hf fJ top-res =
    flat-step1 hf fJ (trans (flat-jmp prog fs la-top)
                            (cong (λ m → do-jump m fs) top-res))
