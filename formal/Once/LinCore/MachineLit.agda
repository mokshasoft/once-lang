-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.MachineLit — plan 0.146 B1.6 (D450): THE CORE'S CONSTANTS ON A
-- MACHINE. A constant's payload is loaded by the machine's own literal load
-- (`instr-load-const`), which materializes it at the machine's format — the
-- core's `lit` at `fs-numerics`, the same function: so a base value's word is
-- its literal (`wordOf`), and the load writes it (`ld`), on every machine.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics; fs-ffi)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.LinCore.Flat using (Base)
import Once.LinCore.Loader

module Once.LinCore.MachineLit (Mach : FrameSemantics) (bw : Base → ℕ) where

private
  fmt = fs-numerics Mach
  ans = fs-ffi Mach

open import Once.LinCore.Core fmt
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open FlatMachine {Mach} using (FlatState; floc; fpc; flat-exec-instr)

-- the load: the machine's literal load at the payload
-- (the compiler's: `Loader`)
ldConst : ∀ {b} → Lit b → AbstractInstr
ldConst = Once.LinCore.Loader.ldConst

ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {Mach} (ldConst v) ≡ nothing
ld-nl {int}   z = refl
ld-nl {float} d = refl

-- a base value's word: its literal
wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue Mach
wordOf {int}   n = SV-Lit fits-int n
wordOf {float} n = SV-Lit fits-float n

w-int : ∀ (n : ⟦ int ⟧b) → wordOf {int} n ≡ SV-Lit fits-int n
w-int n = refl

w-float : ∀ (n : ⟦ float ⟧b) → wordOf {float} n ≡ SV-Lit fits-float n
w-float n = refl

-- ★ the load writes the constant's word, the core's `lit` (the machine's `lit-value` at its format)
ld : ∀ {b} (v : Lit b) (prog : AbstractTrace) (fs : FlatState)
   → flat-exec-instr (ldConst v) prog fs
     ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf (lit v)) }
                 ; fpc = suc (fpc fs) }
ld {int}   z prog fs = refl
ld {float} d prog fs = refl
