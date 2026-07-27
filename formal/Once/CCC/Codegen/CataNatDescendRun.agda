-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatDescendRun — the descend-loop-runs DISCHARGE
-- (Plan 0.36 task #8): run the strat-nat descend loop on a real
-- `HeapNatChain` value, by induction on the chain depth.
--
-- `descend-chain-runs` chains the per-iteration combinators over the
-- value's cons-spine:
--   * cons → `descend-iter-flat` (one continue iteration) ++ recurse,
--   * base → `descend-base-flat` (the tag-0 exit path).
-- The loop invariant (Input1 = cell pointer, Scratch = depth counter,
-- halted = false, memory) is threaded by the `desc-step-*` maintenance
-- lemmas; the `HeapNatChain` transfers to the child via `HeapNatChain
-- -cong` (descend writes no memory). States are `mkFlat ls alloc q-top`
-- so `fpc = q-top` definitionally — the `DescendCode` fetch facts (at
-- `q-top` offsets, shared across iterations) match directly.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatDescendRun where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (LocState; AllocState; halted; regs; readReg; Input1; Scratch;
         sv-as-loc; sucLoc; SV-Tag; SV-Ptr; StoredValue; ValueLocation;
         exec-reg-op; scratch-zero; AbstractTrace;
         instr-reg-op; count-inc; load-indirect-suc; mov-to-input;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero;
         module MemOps)
open import Once.CCC.Machine.Allocation using (next-slot)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.CataNatDescend using (module CataNatDescend)
open import Once.CCC.Codegen.CataNatChain using (module CataNatChain)

module CataNatDescendRun {FS : FrameSemantics} where
  open FlatMachine {FS}
  open MemOps {FS} using (readLoc)
  open FlatStepsAPI {FS}
  open CataNatDescend {FS}
  open CataNatChain {FS}

  -- The strat-nat descend loop's code facts (fetches + label resolutions),
  -- at the loop head `q-top`. Shared across iterations (the loop head pc
  -- is constant).
  record DescendCode (prog : AbstractTrace)
                     (ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end : ℕ) : Set where
    field
      cL   : fetch prog q-top                               ≡ just (instr-ctrl (c-label ld-top))
      cBs  : fetch prog (suc q-top)                         ≡ just (instr-ctrl (c-branch-scratch-zero ld-end))
      cBt  : fetch prog (suc (suc q-top))                   ≡ just (instr-ctrl (c-branch-tag-zero ld-inl))
      ci   : fetch prog (suc (suc (suc q-top)))             ≡ just (instr-reg-op count-inc)
      cl   : fetch prog (suc (suc (suc (suc q-top))))       ≡ just load-indirect-suc
      cm   : fetch prog (suc (suc (suc (suc (suc q-top))))) ≡ just mov-to-input
      cJ1  : fetch prog (suc (suc (suc (suc (suc (suc q-top)))))) ≡ just (instr-ctrl (c-jmp ld-de))
      deR  : find-label prog ld-de                          ≡ just q-de
      cLde : fetch prog q-de                                ≡ just (instr-ctrl (c-label ld-de))
      cJ2  : fetch prog (suc q-de)                          ≡ just (instr-ctrl (c-jmp ld-top))
      topR : find-label prog ld-top                         ≡ just q-top
      ilR  : find-label prog ld-inl                         ≡ just q-inl
      cLi  : fetch prog q-inl                               ≡ just (instr-ctrl (c-label ld-inl))
      cSz  : fetch prog (suc q-inl)                         ≡ just (instr-reg-op scratch-zero)
      cLd  : fetch prog (suc (suc q-inl))                   ≡ just (instr-ctrl (c-label ld-de))
      cJt  : fetch prog (suc (suc (suc q-inl)))             ≡ just (instr-ctrl (c-jmp ld-top))
      elR  : find-label prog ld-end                         ≡ just q-end

  -- The descend loop runs to completion on a depth-`m` chain: `m*9+9`
  -- steps from the loop head to SOME descend-done state. Induction on `m`.
  descend-chain-runs : ∀ (prog : AbstractTrace)
                         (ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end : ℕ)
                         (code : DescendCode prog ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end)
                         (m : ℕ) (ls : LocState FS) (alloc : AllocState {FS})
                         (loc : ValueLocation FS)
                     → sv-as-loc (readReg (regs ls) Input1) ≡ just loc
                     → readReg (regs ls) Scratch ≡ SV-Tag 1
                     → halted ls ≡ false
                     → HeapNatChain m loc ls
                     → Σ[ final ∈ FlatState ]
                         (FlatSteps prog (m * 9 + 9) (mkFlat ls alloc q-top) final
                          × next-slot (falloc final) ≡ next-slot alloc)
  descend-chain-runs prog ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end code
                     zero ls alloc loc ptr sc hlt chain =
    _ , descend-base-flat prog (mkFlat ls alloc q-top) ld-top ld-end ld-inl ld-de q-inl q-top q-end
          hlt (cong sv-is-zero sc) (chain-base-tcond (mkFlat ls alloc q-top) loc ptr chain)
          (scratch-zeroed ls)
          (DescendCode.cL code) (DescendCode.cBs code) (DescendCode.cBt code)
          (DescendCode.ilR code) (DescendCode.cLi code) (DescendCode.cSz code)
          (DescendCode.cLd code) (DescendCode.cJt code) (DescendCode.topR code)
          (DescendCode.cL code) (DescendCode.cBs code) (DescendCode.elR code)
      , refl    -- descend allocates nothing; base-flat's result is `record …
                -- {floc; fpc}`, so falloc = alloc definitionally.
  descend-chain-runs prog ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end code
                     (suc m) ls alloc loc ptr sc hlt (tag , child-loc , child-ptr , child-chain) =
    let fs = mkFlat ls alloc q-top
        iter = descend-iter-flat prog fs ld-top ld-end ld-inl ld-de q-de q-top loc (SV-Ptr child-loc)
                 hlt (cong sv-is-zero sc)
                 (chain-cons-tcond fs loc m ptr (tag , child-loc , child-ptr , child-chain))
                 ptr child-ptr
                 (DescendCode.cL code) (DescendCode.cBs code) (DescendCode.cBt code)
                 (DescendCode.ci code) (DescendCode.cl code) (DescendCode.cm code)
                 (DescendCode.cJ1 code) (DescendCode.deR code) (DescendCode.cLde code)
                 (DescendCode.cJ2 code) (DescendCode.topR code)
        ls'  = floc (desc-step prog q-top fs)
        alloc' = falloc (desc-step prog q-top fs)
        ptr' = cong sv-as-loc (desc-step-input1 prog q-top fs loc (SV-Ptr child-loc) ptr child-ptr)
        sc'  = trans (desc-step-scratch prog q-top fs loc (SV-Ptr child-loc) ptr child-ptr) sc
        hlt' = trans (desc-step-halted prog q-top fs loc (SV-Ptr child-loc) ptr child-ptr) hlt
        chain' = HeapNatChain-cong m child-loc ls ls'
                   (λ l' → desc-step-readLoc prog q-top fs loc (SV-Ptr child-loc) l' ptr child-ptr)
                   child-chain
        rec = descend-chain-runs prog ld-top ld-end ld-inl ld-de q-top q-de q-inl q-end code
                m ls' alloc' child-loc ptr' sc' hlt' chain'
    -- `alloc' = falloc (desc-step …) = alloc` definitionally (the descend
    -- body preserves falloc: count-inc reg, load-indirect-suc `, alloc`,
    -- mov reg), so the recursion's next-slot fact is already `≡ next-slot
    -- alloc`. Descend allocates nothing.
    in proj₁ rec , FlatSteps-++ iter (proj₁ (proj₂ rec)) , proj₂ (proj₂ rec)
