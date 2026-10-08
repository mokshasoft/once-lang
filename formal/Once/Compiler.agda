-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Compiler — ASSEMBLY POINT
--
-- This module wires together:
--   - the abstract spec     (`Once.Adequacy`)
--   - the meaning           (`Once.Denotation.Behavior`)
--   - the trusted CPU base  (`Once.Adequacy.CPU`)
--   - the proof + compile   (`Once.Adequacy.Compile`)
--
-- and constructs a single `CorrectCompiler` value the CLI consumes.
-- This file should be one record literal: assembly only, with every
-- ingredient proved elsewhere. If the assembly typechecks, the compiler
-- is correct (modulo the postulates listed in the participating modules).
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.


open import Once.Denotation.TraceMonad using (interp)
open import Once.Spec.Contract using (ISig; Impl)
import Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds as RB
import Once.Adequacy.ArchCorrectness.RiscV64.ResourceBounds as RBr
import Once.Adequacy.ArchCorrectness.X86-32.ResourceBounds as RB32

-- Plan 0.107: the entry unit's owner is the EMITTER's (`Once.Compile.entry-owner`),
-- not a parameter — the theorem is about the program actually emitted.
open import Once.Compile using (entry-owner)

module Once.Compiler
  (x86-64-heap-room : ∀ ι → RB.HeapRoom entry-owner ι) (x86-64-stack-room : ∀ ι → RB.StackRoom entry-owner ι)
  (x86-64-call-room : ∀ ι → RB.CallRoom entry-owner ι)
  (x86-64-reg-range : ∀ ι → RB.RegRange entry-owner ι)
  (x86-64-scratch-dec-guarded : ∀ ι → RB.ScratchDecGuarded entry-owner ι)
  (x86-64-addr-no-wrap : ∀ ι → RB.AddrNoWrap entry-owner ι)
  (x86-64-lit-fits : ∀ ι → RB.LitFits entry-owner ι)
  (riscv64-heap-room : ∀ ι → RBr.HeapRoom entry-owner ι) (riscv64-stack-room : ∀ ι → RBr.StackRoom entry-owner ι)
  (riscv64-call-room : ∀ ι → RBr.CallRoom entry-owner ι)
  (riscv64-reg-range : ∀ ι → RBr.RegRange entry-owner ι)
  (riscv64-scratch-dec-guarded : ∀ ι → RBr.ScratchDecGuarded entry-owner ι)
  (riscv64-slot-addr-no-wrap : ∀ ι → RBr.SlotAddrNoWrap entry-owner ι)
  (riscv64-addr-no-wrap : ∀ ι → RBr.AddrNoWrap entry-owner ι)
  (riscv64-lit-fits : ∀ ι → RBr.LitFits entry-owner ι)
  -- …and x86-32's seven (plan 0.66 X3): the arch had none while its simulation
  -- was a whole-cloth postulate, which is precisely what a deleted apex
  -- postulate makes visible — the resources a running program needs.
  (x86-32-heap-room : ∀ ι → RB32.HeapRoom entry-owner ι) (x86-32-stack-room : ∀ ι → RB32.StackRoom entry-owner ι)
  (x86-32-call-room : ∀ ι → RB32.CallRoom entry-owner ι)
  (x86-32-reg-range : ∀ ι → RB32.RegRange entry-owner ι)
  (x86-32-scratch-dec-guarded : ∀ ι → RB32.ScratchDecGuarded entry-owner ι)
  (x86-32-addr-no-wrap : ∀ ι → RB32.AddrNoWrap entry-owner ι)
  (x86-32-lit-fits : ∀ ι → RB32.LitFits entry-owner ι) where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.Adequacy
open import Once.Denotation.Behavior using (Source; Behavior)
open Once.Denotation.Behavior.Behavior using (at)
-- The driver is where the per-arch CPU semantics are INJECTED (D054
-- wired-not-imported). Importing `Once.Adequacy.CPU` here pulls in the
-- per-arch instance postulates; that is intentional and confined to
-- this assembly point. `Once.Adequacy.Compile.WithCPU` itself stays
-- free of those imports.
open import Once.Adequacy.CPU using (Byte)
open import Once.Target.Arch using (Arch)
open import Once.Adequacy.ArchCorrectness x86-64-heap-room x86-64-stack-room x86-64-call-room
       x86-64-reg-range x86-64-scratch-dec-guarded x86-64-addr-no-wrap x86-64-lit-fits
       riscv64-heap-room riscv64-stack-room riscv64-call-room
       riscv64-reg-range riscv64-scratch-dec-guarded riscv64-slot-addr-no-wrap
       riscv64-addr-no-wrap riscv64-lit-fits
       x86-32-heap-room x86-32-stack-room x86-32-call-room
       x86-32-reg-range x86-32-scratch-dec-guarded x86-32-addr-no-wrap x86-32-lit-fits
       using (arch-correctness; BlockRunsHyp-x86-64; BlockRunsHyp-x86-32; BlockRunsHyp-riscv64)
-- plan 0.92, and an honest note on its cost: `public` here is NOT convenience.
-- `Once.Certified` cannot STATE `once-certified`'s signature without naming
-- these three types, and to name a type N levels up it must be re-exported at
-- every level in between. That propagation is exactly the property that makes
-- `public` expensive — but the alternative (Certified re-importing
-- `ArchCorrectness` with its full twenty-parameter telescope) is worse.
-- `arch-correctness` rides along on the same `using` list; splitting the import
-- to avoid that would duplicate the telescope for one name.
       public
import Once.Adequacy.Compile as VCompile

-- D162: the Haskell-facing surface. Imported HERE because `make malonzo`
-- extracts from this module, and `Once.Extract.Names` must be in that cone to
-- be extracted. It contributes nothing to the theorem below — it is stable
-- extracted NAMES plus two predicates the hand-written bridge used to compute
-- by pattern-matching MAlonzo constructors.

-- Instantiate the verified pipeline with the concrete per-arch
-- semantics AND the per-arch backend-correctness witnesses. `VC.compile` /
-- `VC.exec` / `VC.correct` are the compiler, the injected execution, and the
-- grand theorem proved against them. `arch-correctness` forces every target
-- to supply its `ArchCorrect` (proof or postulate) — the assembly point for
-- the per-arch trusted base.
-- plan 0.91 parallel track: `VC` is now scoped INSIDE `once-compiler`, because
-- it depends on the three block-table coherence hypotheses. They were the FALSE
-- postulate `block-runs` (D213); making them visible in the statement is what
-- turns a vacuous theorem into a conditional one. Plan 0.93 discharges them.

once-compiler : BlockRunsHyp-x86-64 → BlockRunsHyp-x86-32 → BlockRunsHyp-riscv64
              → CorrectCompiler
once-compiler b64 b32 brv = record
  { Arch     = Arch
  ; Source   = Source
  ; Bytes    = List Byte
  ; Behavior = Behavior
  -- Plan 0.105 (D257, D061): an interpretation's declared signatures and an
  -- implementation of them in the compiler's contract form (`Once.Spec.Contract`).
  ; Signature      = ISig
  ; Implementation = Impl
  -- Plan 0.49: the INDEPENDENT meaning is RELATIONAL. `Typed` = an executable
  -- declaratively-well-typed module; `_⊢_` links a source to it by PARSE (not
  -- the elaborator); `⟦_⟧ˢ` is the surface denotation `SD.⟦_⟧ˢ` of `main` (so
  -- `faithful` is load-bearing — typecheck + elaborate + codegen are forced).
  ; Typed    = VC.Typed
  ; _⊢_      = VC._⊢R_
  -- the signatures a typed module is compiled against: its FFI declarations
  ; sigOf    = VC.sigOfT
  -- Plan 0.58 (OCP-0006): the reference meaning is now the DIRECT, IR-free
  -- derivation denotation `VC.⟦_⟧ᵈ` (was `VC.⟦_⟧ˢ` = SD∘realize); `correctᵈ`
  -- re-composes the grand theorem with the observational bridge.
  -- …relative to an implementation of the program's signatures; the bytes run
  -- in the world those signatures and that implementation make.
  ; ⟦_⟧ˢ     = VC.⟦_⟧ᵈᴵ
  ; exec     = λ arch S I → VC.exec (interp S I) arch
  -- Behavioural equivalence = pointwise / up-to-`n` SigOp-trace prefix
  -- equality (Plan 0.44).
  ; _≈_      = λ b₁ b₂ → ∀ (n : ℕ) → at b₁ n ≡ at b₂ n
  -- Plan 0.48: `compile` carries the optimizer flag.
  ; compile  = VC.compile
  -- Plan 0.49: the two-conjunct (sound+trace / complete) relational claim.
  ; correct  = VC.correctᵈ
  }
  where
    module VC = VCompile.WithCPU (arch-correctness b64 b32 brv)
