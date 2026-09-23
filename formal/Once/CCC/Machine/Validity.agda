-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Validity
--
-- Concrete validity definitions for SlotMachine POC.
--
-- Key insight: In SlotMachine, memory stores ValueLocations directly,
-- so ValidAt can be defined as an inductive family indexed by Type.
--
-- IMPORTANT: Closures track their body IR!
-- Since we create all closures via curry, we know exactly what IR
-- each closure contains. This enables Apply to dispatch to bodies.
------------------------------------------------------------------------

module Once.CCC.Machine.Validity where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Induction.WellFounded using (Acc; acc)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Machine.Allocation
open import Once.Semantics.Machine public
  using (sem-fst; sem-snd; sem-inl; sem-inr; sem-pair)
-- The IRTy value-domain rename is LOCAL to Validity (not re-exported), so it
-- does not collide with downstream modules' own surface `⟦_⟧` imports.
open import Once.Semantics.Machine
  using () renaming (⟦_⟧ᴵ to ⟦_⟧)
pair = sem-pair
open import Once.IR
open import Once.IR.Size

------------------------------------------------------------------------
-- ValidAt: Inductive Validity Predicate with Frontier Tracking
--
-- ValidAt alloc {A} v loc s means: value v of type A is validly represented
-- at location loc in state s, and all component locations are before
-- the allocation frontier tracked by alloc.
--
-- Structure:
--   - Pairs: loc points to fst-loc, sucLoc loc points to snd-loc
--   - Closures: loc points to env-loc, sucLoc loc points to code-loc
--               PLUS: tracks the body IR and env value
--   - Unit: always valid (no memory requirements)
--
-- Key insight: By tracking the body IR in closures, Apply can extract
-- the IR and dispatch to it recursively.
------------------------------------------------------------------------

-- `readLoc-stack-heap-eq` is the ONE thing four other modules take from this
-- file, and it never mentioned `program-bound`. Plan 0.91 S1: it lives in its
-- own bound-free module, so `ClosureWellFormedDef` / `MuValidityImpl` /
-- `ValidAtWFHalted` / the `IRObsCorrect` interface can open it WITHOUT
-- inventing a bound to pass. `ValidityDef` re-exports it, so every existing
-- use below reads exactly as before.
module ReadLocEq {FS : FrameSemantics} where
  open MemOps {FS}

  readLoc-stack-heap-eq : ∀ (s₁ s₂ : LocState FS) loc →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ loc ≡ readLoc s₂ loc
  readLoc-stack-heap-eq s₁ s₂ (AtStack f k) seq heq = cong (λ m → m f k) seq
  readLoc-stack-heap-eq s₁ s₂ (AtDynamic hl) seq heq = cong (λ m → m hl) heq

-- plan 0.98: `ValidityDef` is DELETED. It held `ValidAt` and the pure `eval`
-- alias, and `eval` is REFUTED once `Halts : B ≡ Void` makes `⟦ Void ⟧ = ⊥`.
-- D214 had already measured it dead: re-exported by `IRObsCorrect/Prelude` and
-- instantiated by NOTHING ("dead by the consumers-not-importers test; separate
-- cleanup"). This is that cleanup — forced, not chosen. `ReadLocEq` above is the
-- part four modules actually took from it, already hoisted out by D214.
