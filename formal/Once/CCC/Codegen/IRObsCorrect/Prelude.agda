-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Prelude
--
-- D200: the import block of `IRObsCorrectFlat`, re-exported.
--
-- The split of that module (see `IRObsCorrect.Interface`) would otherwise
-- have to repeat these eighty lines in every part. They are `public` here so
-- each part imports ONE thing and reads exactly as the single file did.
--
-- The `import X as Y` forms cannot be re-exported (Agda has no `public` for a
-- qualified alias), so the five of those are repeated per part — they are one
-- line each and name no contents.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Prelude (o : CanonicalName) where
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; _∸_) public
open import Data.Nat.Properties using (n<1+n; n≤1+n; ≤-refl; <-≤-trans) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Relation.Nullary using (yes; no) public
open import Data.Bool using (false; true) public
open import Data.List using (length; take; []; _∷_; _++_; map) public
open import Data.List.Properties using (++-assoc; length-++) public
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap) public
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂) public
open import Relation.Binary.PropositionalEquality using (_≡_) public

open import Once.CCC.FrameSemantics using (FrameSemantics) public
-- SigOpInfo is over SURFACE Type (`SigOp : SigOpInfo A B → IR ⌊A⌋ ⌊B⌋`), so the
-- surface `FitsInReg`/`fits-in-reg?` stay; the μ/functor + value-domain layer is IRTy.
open import Once.Type using (Type; FitsInReg; fits-in-reg?)
  renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ; Int to Intˢ; Unit to Unitˢ) public
open import Once.Float.Decimal using (Decimal; round) public
open import Data.Integer using (ℤ) public
open import Once.IRTy using (WellFormedFI-irrelevant) public
open import Once.Denotation.ValueDomain using () renaming (⟦_⟧ᴰᴵ to ⟦_⟧) public
open import Once.IR using (IR; IRTy; Unit; AllocMode; Stack; Heap; Cata; SigOp; SigOpInfo; out-μ; _∘_;
  μ-type; ⟦_⟧TI; WellFormedFI; FitsInRegI; fits-int; fits-float; ⌊_⌋;
  -- Plan 0.68 step 0: the enumeration needs EVERY constructor in scope, not
  -- just the ones with a clause of their own before it.
  id; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial; curry; apply;
  In; Para; Out; in-ν; Ana; Hylo; Fuse; free-heap; const;
  NatTr; ν-type; _*_) public
open import Once.IRTy using (⟦_,_⟧-baseI) public
open import Once.Memory.HeapAddress using (HeapRef; mkHeapRef; ref-id; HeapLocation; heap-loc; heap-ref; sucHL) public
open import Once.Word using (Carrier) public
open import Data.Unit using (tt) public

-- Surface `FitsInReg B` ⇒ erased `FitsInRegI ⌊B⌋`: `⌊Int⌋=Int`, `⌊Float⌋=Float`
-- definitionally, so this is a match-to-refl coherence.
fits-erase : ∀ {B} → FitsInReg B → FitsInRegI ⌊ B ⌋
fits-erase fits-intˢ   = fits-int
fits-erase fits-floatˢ = fits-float
open import Once.SigOp.Info using (effect; EffectShape; Pure; Emits; Halts) public
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst; subst₂; _≢_) public
open import Once.IR.Size using (ir-size) public
open import Data.Nat.Properties using (≤-<-trans; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; +-identityʳ; +-assoc; +-suc; +-comm; <-irrefl; <-trans) public
open import Function using (case_of_) public
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.CCC.Label using (LabelId; ℓ) public
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; SV-Ptr; sv-as-loc; halted; regs; readReg; Input1; Output;
         instr-sigop; mov-to-output; mov-to-input; instr-load-const; SV-Lit; writeReg; writeReg-same; AbstractTrace;
         -- D155: the closure register's type — the entry state's one open
         -- component (see `entry-flat`).
         StoredValue; AbstractInstr; module AbstractExec; module MemOps;
         -- D171: the store instruction and the location vocabulary its
         -- read-back needs.
         store-at-slot; AtStack; current-frame;
         -- D174: the rest of `inl`/`inr`'s heap build — the first discharge in
         -- this file that ALLOCATES, so these are new to its vocabulary.
         instr-alloc-heap; instr-load-tag-lit; instr-load-code-addr; SV-Code;
         instr-call-closure; instr-save-closure-reg; store-indirect; store-indirect-suc;
         load-from-slot; load-indirect; load-indirect-suc;
         AtDynamic; sucLoc; SV-Tag; writeReg-preserves; _≟HL_) public
open import Once.CCC.Machine.Validity using (module ValidityDef) public
open import Once.CCC.Machine.ValidAtWFHalted o using (validAtWF-set-halted) public
open import Once.CCC.Machine.Allocation using (AllocState; next-slot; next-heap-ref; module FrontierInvariant) public
open import Once.CCC.Machine.Flat using (module FlatMachine) public
open import Once.CCC.Machine.SMPrimitives using (module TracePrimitives; module InstrPrimitives; module RecSchemeSemantics) public
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot) public
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI) public
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-to-trace') public
open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot) public
open import Once.CCC.Codegen.SlotBudget o using (frontier-mono; budget-of) public
open import Once.CCC.Codegen.CataIRSlotStable o using (module CataIRSlotStable) public
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef) public
import Once.CCC.Machine.ReadTypedAdequate as RTA
open import Once.Denotation.Trace using (SigOpEvent) public
import Once.Denotation.DenotTrace as DT
open import Once.Denotation.DenotTrace using (inject) public
open import Once.Denotation.TraceMonad using (projTrace) public
import Once.Denotation.TraceMonad as TM
open import Once.Adequacy.FlatEvents using (module FlatEventTrace) public

