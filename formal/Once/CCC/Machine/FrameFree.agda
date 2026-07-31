-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FrameFree   (Plan 0.54 rung D, item 2)
--
-- "This instruction is one the live emitter can produce, and so is everything
-- it runs." Concretely: not a frame op, and not `instr-loop`.
--
-- NAMING DEBT (2026-07-31): the module is still called FrameFree, but the
-- predicate now also excludes `instr-loop`. Both are instructions with NO
-- PRODUCER — `ir-to-trace` emits neither (grep: both appear only in IRToTrace's
-- import list) — so both are ⊥ here and both dispatch clauses in the flat↔x86-64
-- correspondence are unreachable. Adding the loop cost no proof at all: the
-- emitter induction in `Once.CCC.Codegen.FrameFreeTrace` never produces one, so
-- every clause of it stands unchanged.
--
-- The four abstract frame instructions — `instr-alloc-stack`,
-- `instr-dealloc-stack`, `instr-push-frame`, `instr-pop-frame` — are the ONLY
-- writers of `Registers.stackSlot` in `exec-abstract` (SMCore: `incrStackSlot`,
-- `decrStackSlot`, `writeStackSlot`, at exactly those three sites). So this
-- predicate is what makes the live stack window CONSTANT along a run, which is
-- what the flat↔x86-64 slot residuals rest on.
--
-- DEEP, unlike `SMPrimitives.NoFrameOp`: one flat step at an
-- `instr-case-on-tag` / `instr-loop` runs a whole NESTED trace, so a shallow
-- predicate would let a frame op back in through a branch body. The trace-level
-- predicate is spelled out (`FrameFreeT`) rather than `All FrameFreeI` so the
-- mutual recursion is structural.
--
-- (`SMPrimitives.NoFrameOp` is the older shallow push/pop-frame fence of the
-- legacy IR-WF layer; it is not this and does not cover alloc/dealloc-stack.)
------------------------------------------------------------------------

module Once.CCC.Machine.FrameFree where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Once.CCC.Machine.SMCore using
  (AbstractInstr; AbstractTrace;
   instr-alloc-stack; instr-dealloc-stack; instr-push-frame; instr-pop-frame;
   instr-case-on-tag; instr-loop)

mutual
  FrameFreeI : AbstractInstr → Set
  FrameFreeI (instr-alloc-stack _)     = ⊥
  FrameFreeI (instr-dealloc-stack _)   = ⊥
  FrameFreeI (instr-push-frame _)      = ⊥
  FrameFreeI instr-pop-frame           = ⊥
  FrameFreeI (instr-case-on-tag t₁ t₂) = FrameFreeT t₁ × FrameFreeT t₂
  -- `instr-loop` is a RETIRED FOSSIL: the cata codegen compiles to flat control
  -- (`c-label`/`c-jmp`/`c-branch-*`), never to a structured loop instruction.
  FrameFreeI (instr-loop t)            = ⊥
  {-# CATCHALL #-}
  FrameFreeI _                         = ⊤

  FrameFreeT : AbstractTrace → Set
  FrameFreeT []       = ⊤
  FrameFreeT (i ∷ is) = FrameFreeI i × FrameFreeT is

-- Splicing two frame-free traces keeps them frame-free (every emitter clause
-- that concatenates needs this).
frame-free-++ : ∀ t₁ t₂ → FrameFreeT t₁ → FrameFreeT t₂ → FrameFreeT (t₁ ++ t₂)
frame-free-++ []       t₂ ff₁        ff₂ = ff₂
frame-free-++ (i ∷ is) t₂ (fi , ffs) ff₂ = fi , frame-free-++ is t₂ ffs ff₂

-- `FrameFreeT` and `All FrameFreeI` are interchangeable. Both forms are wanted:
-- `All` is a DATATYPE, so its append (`++⁺`) unifies at a splice `t₁ ++ t₂` —
-- which is what an induction over the emitter is made of; `FrameFreeT` is what
-- the nested `instr-case-on-tag` / `instr-loop` obligations are stated in, and
-- is structural, which is what the mutual definition above needs.
frame-free-all : ∀ t → FrameFreeT t → All FrameFreeI t
frame-free-all []       ff         = []
frame-free-all (i ∷ is) (fi , ffs) = fi ∷ frame-free-all is ffs

frame-free-nest : ∀ {t} → All FrameFreeI t → FrameFreeT t
frame-free-nest []         = tt
frame-free-nest (fi ∷ ffs) = fi , frame-free-nest ffs
