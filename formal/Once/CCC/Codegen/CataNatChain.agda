-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataNatChain — the descend-ready interface (Plan 0.36
-- task #8 assembly).
--
-- `HeapNatChain n loc s` says the heap `s` holds a cons-depth-`n` Nat-like
-- value at `loc`: `n` cons cells (tag 1, child pointer at `sucLoc`) ending
-- in a base cell (tag 0). It is the SEAM between
--   * the per-cell extraction (`CataNatSeam`: a value's `valid-μ-wf`
--     produces this chain — the producing half, functor-shape-specific),
--   * and the descend loop (`CataNatDescend.descend-loop-runs`: it consumes
--     the chain to discharge each iteration — the consuming half,
--     functor-agnostic).
--
-- Bundling Heap reads directly (not `ValidAtWF`) keeps the child mode out
-- of the existential `valid-inr-wf` payload mode, and exposes exactly what
-- the descend needs. This module is the CONSUMER side: chain facts → the
-- descend's `tcond` (`cons-tcond`/`base-tcond`) + the child pointer.
------------------------------------------------------------------------

module Once.CCC.Codegen.CataNatChain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (regs; readReg; Input1; sv-as-loc; SV-Tag; SV-Ptr;
         ValueLocation; LocState; sucLoc; module MemOps)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.CataNatHeap using (module CataNatHeap)

module CataNatChain {FS : FrameSemantics} where
  open FlatMachine {FS}
  open MemOps {FS} using (readLoc)
  open CataNatHeap {FS}

  -- The heap holds a cons-depth-`n` Nat value at `loc` in state `s`:
  --   base  (n=0)     : tag 0 at loc;
  --   cons  (n=suc m) : tag 1 at loc, child pointer at sucLoc loc, and the
  --                     child is a depth-m chain.
  HeapNatChain : ℕ → ValueLocation FS → LocState FS → Set
  HeapNatChain zero    loc s = readLoc s loc ≡ just (SV-Tag 0)
  HeapNatChain (suc m) loc s =
      (readLoc s loc ≡ just (SV-Tag 1))
    × Σ[ child-loc ∈ ValueLocation FS ]
        (readLoc s (sucLoc loc) ≡ just (SV-Ptr child-loc) × HeapNatChain m child-loc s)

  -- CONSUMER: at a cons cell with `Input1` pointing to `loc`, the descend's
  -- continue tag condition (`tag ≠ 0`) holds — `cons-tcond` applied to the
  -- chain's tag fact.
  chain-cons-tcond : ∀ (fs : FlatState) (loc : ValueLocation FS) (m : ℕ)
                   → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
                   → HeapNatChain (suc m) loc (floc fs)
                   → tag-zf (flat-read-tag (floc fs)) ≡ false
  chain-cons-tcond fs loc m ptr chain = cons-tcond fs loc ptr (proj₁ chain)

  -- CONSUMER: at the base cell, the descend's exit tag condition (`tag = 0`).
  chain-base-tcond : ∀ (fs : FlatState) (loc : ValueLocation FS)
                   → sv-as-loc (readReg (regs (floc fs)) Input1) ≡ just loc
                   → HeapNatChain zero loc (floc fs)
                   → tag-zf (flat-read-tag (floc fs)) ≡ true
  chain-base-tcond fs loc ptr chain = base-tcond fs loc ptr chain

  -- HeapNatChain is preserved under any state change that preserves
  -- `readLoc` (e.g. the descend body, which writes only registers). Lets
  -- the chain transfer from `floc fs` to `floc (desc-step … fs)`. Induction
  -- on the depth; each tag/child read transported by the `readLoc` equality.
  HeapNatChain-cong : ∀ (m : ℕ) (loc : ValueLocation FS) (s s' : LocState FS)
                    → (∀ loc' → readLoc s' loc' ≡ readLoc s loc')
                    → HeapNatChain m loc s → HeapNatChain m loc s'
  HeapNatChain-cong zero    loc s s' eq chain = trans (eq loc) chain
  HeapNatChain-cong (suc m) loc s s' eq (tag , cl , cp , rest) =
      trans (eq loc) tag
    , cl
    , trans (eq (sucLoc loc)) cp
    , HeapNatChain-cong m cl s s' eq rest
