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
   instr-case-on-tag; instr-loop; lea-indexed; lea-slot;
   instr-ctrl; c-thunk; c-ret)

-- No mutual needed since Plan 0.54 item 6: with `instr-case-on-tag` in the ⊥
-- set there is NO nested trace anywhere — the predicate is shallow.
FrameFreeI : AbstractInstr → Set
FrameFreeI (instr-alloc-stack _)     = ⊥
FrameFreeI (instr-dealloc-stack _)   = ⊥
FrameFreeI (instr-push-frame _)      = ⊥
FrameFreeI instr-pop-frame           = ⊥
-- `instr-case-on-tag` is a RETIRED FOSSIL (Plan 0.54 item 6, 2026-08-01):
-- `case` compiles to flat control (`c-branch-tag-zero`/`c-jmp`/`c-label`,
-- branches inlined into the main trace) the way `Cata` always did — one flat
-- step never runs a nested trace again.
FrameFreeI (instr-case-on-tag t₁ t₂) = ⊥
-- `instr-loop` is a RETIRED FOSSIL: the cata codegen compiles to flat control
-- (`c-label`/`c-jmp`/`c-branch-*`), never to a structured loop instruction.
FrameFreeI (instr-loop t)            = ⊥
-- `lea-indexed` is a RETIRED FOSSIL too (2026-08-01): the Tier-1/Tier-2 cata
-- codegen walks HEAP-LINKED stacks (`push2`/`pop2`, "NOT lea-indexed" —
-- IRToTrace), so no emitted trace contains an indexed cursor. Retiring it
-- deletes the `lea-indexed-wf` cursor-discipline residual with its site, and
-- the pointer-bounds invariant needs no cursor case at all.
FrameFreeI (lea-indexed _)           = ⊥
-- `lea-slot` is the ONE INSTRUCTION THAT CREATES A STACK POINTER
-- (`exec-abstract (lea-slot slot)` writes `SV-Ptr (AtStack …)`; nothing else
-- in the machine does). Plan 0.63 step 2b: it is emitted only by the four
-- STACK-MODE clauses of `ir-to-trace'` (`⟨_,_⟩ Stack`, `curry _ Stack`,
-- `inl/inr Stack`), so a HEAP-MODED trace contains none — which is why the
-- walk below (`FrameFreeTrace`) is now conditional on `HeapModed`, and why
-- `FlatStackPtr`'s invariant could be simplified to "there is no stack
-- pointer". Not a fossil: it is live codegen, just not on the heap-moded
-- path the flat↔x86-64 correspondence runs over.
FrameFreeI (lea-slot _)              = ⊥
-- The two closure markers are NOT fossils — they are the opposite,
-- scaffolding ahead of their producer (Plan 0.63 step 1 added the
-- constructors; step 2b puts closure BODIES into `ir-to-trace`, which is
-- what will emit them). Until then no emitted trace contains either, and
-- this is the honest way to say so.
--
-- BOTH now MOVE THE FRAME (step 2a: the body's `subq`/`addq` reservation
-- rides on the marker), so they belong here for a second reason too — this
-- is the frame fence, and they are frame ops. What step 2 owes them is a
-- real correspondence: `c-thunk`'s is `block-step-alloc-stack`'s premise
-- set (freshness of the callee frame, from `untouched` + the high-water
-- mark, plus the honest `stack-room`), and `c-ret`'s additionally needs
-- the `FlatCorr` field relating the ghost `fret` to the machine stack.
FrameFreeI (instr-ctrl (c-thunk _ _)) = ⊥
FrameFreeI (instr-ctrl (c-ret _))     = ⊥
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
