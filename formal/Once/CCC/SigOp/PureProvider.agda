-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.SigOp.PureProvider
--
-- A PartialProvider covering every `Pure` + fits-in-reg SigOp (this
-- includes `arith.block.*`). The result is register-resident: the value
-- lives in the Output register as the abstract sentinel
-- `unit-storedvalue`, so `result-place` is discharged with the
-- `at-reg` constructor (NOT `at-loc`, whose `Output ≡ SV-Ptr loc` would
-- be refutable for a sentinel).
--
-- `output-is-sentinel` is the genuine proof that Output holds
-- `unit-storedvalue` after the SigOp step, established by reducing
-- `pure-sigop-output` on the `fits-in-reg? B ≡ just fitness` and
-- `effect si ≡ Pure` evidence.
------------------------------------------------------------------------

module Once.CCC.SigOp.PureProvider where

open import Data.Nat using (ℕ; _≤_; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; +-identityʳ; m≤m+n)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; FitsInReg; fits-in-reg?)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.IR using (IR; SigOp; SigOpInfo; AllocMode; Stack; Heap)
open import Once.SigOp.Info using (EffectShape; Pure; Emits; Halts; effect)
open import Once.CCC.Machine.SMCore
  using (LocState; ValueLocation; AtStack; SV-Ptr;
         halted; regs;
         readReg; writeReg; writeReg-same;
         Input1; Output; AbstractTrace; instr-sigop)

------------------------------------------------------------------------
-- Provider (arch-portable, parameterized by FrameSemantics)
------------------------------------------------------------------------

module PureProviderDef {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.CCC.Machine.Allocation
    using (AllocState; current-frame; next-slot; next-heap-ref)
  open import Once.CCC.Machine.Allocation
    using (module FrontierInvariant)
  open FrontierInvariant {FS}
    using (BeforeFrontier; AllocBump; mkBump; apply-bump)

  open import Once.CCC.Machine.SMCore using (module AbstractExec)
  open AbstractExec {FS}
    using (exec-trace; exec-trace-single; exec-sigop-output; exec-sigop-halts;
           unit-storedvalue)

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; at-reg; valid-primitive-wf;
           mem-preserved-from-tnhw)
  open import Once.CCC.IR.Stack using (ir-stack-requirement; ir-scratch-requirement; sigOp-stack-req)

  import Once.CCC.Machine.SMPrimitives as SMP
  open SMP.TracePrimitives {FS}

  open import Once.CCC.SigOp.Contract using (module Def)
  open Def {FS} program-bound using (Contract; PartialProvider)

  ------------------------------------------------------------------------
  -- The contract for a Pure + fits-in-reg SigOp.
  ------------------------------------------------------------------------

  pure-prim-contract : ∀ {A B} (si : SigOpInfo A B) (fitness : FitsInReg B)
    → fits-in-reg? B ≡ just fitness → effect si ≡ Pure
    → Contract Stack (SigOp si)
  pure-prim-contract {A} {B} si fitness fits-eq pure-pf
    mIn x input-loc s alloc valid-in input-before not-halted rdi-eq =
    record
      { base = record
          { final-state = final-state
          ; trace = instr-sigop si ∷ []
          ; bump = mkBump 0 0
          ; trace-is-ir-to-trace = refl
          ; trace-correct =
              cong proj₁ (exec-trace-single (instr-sigop si) s alloc not-halted)
          ; alloc-correct =
              cong proj₂ (exec-trace-single (instr-sigop si) s alloc not-halted)
          ; result-place =
              at-reg input-loc
                (valid-primitive-wf fitness input-before) input-before
                output-is-sentinel
                (valid-primitive-wf fitness input-before) input-before
          ; not-halted = final-not-halted
          ; mem-preserved-before =
              mem-preserved-from-tnhw alloc (instr-sigop si ∷ []) s final-state
                (cong proj₁ (exec-trace-single (instr-sigop si) s alloc not-halted))
                tt tt
          ; trace-twf = twf-∷ tt twf-[]
          ; trace-preserves-halted =
              exec-trace-preserves-halted-WF (instr-sigop si ∷ [])
          ; trace-no-frame-ops = (tt , tt)
          }
      ; stack-inv = record
          { max-slot-written = next-slot alloc
          ; stack-budget = ir-stack-requirement (SigOp {A} {B} si)
          ; bump-fits-stack-budget = z≤n
          ; max-slot-geq-final = ≤-refl
          ; max-slot-usage-bound =
              let n = next-slot alloc
                  eq : n +ℕ ir-stack-requirement (SigOp {A} {B} si) ≡ n
                  eq = trans (cong (n +ℕ_) (sigOp-stack-req {A} {B} si)) (+-identityʳ n)
              in subst (n ≤_) (sym eq) ≤-refl
          ; frontier-slot-stable = λ _ _ _ _ _ → inj₁ refl
          ; trace-writes-above = tt
          ; trace-slot-reads-above = tt
          ; trace-writes-below = tt
          ; trace-slot-reads-below = tt
          ; scratch-budget = ir-scratch-requirement (SigOp {A} {B} si)
          ; scratch-bounded =
              let n = next-slot alloc
                  eq : n +ℕ ir-scratch-requirement (SigOp {A} {B} si) ≡ n
                  eq = trans (cong (n +ℕ_) (sigOp-stack-req {A} {B} si)) (+-identityʳ n)
              in subst (n ≤_) (sym eq) ≤-refl
          }
      ; heap-inv = record
          { heap-budget = 0
          ; max-heap-ref-written = next-heap-ref alloc
          ; bump-fits-heap-budget = z≤n
          ; max-heap-ref-geq-final = ≤-refl
          ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
          }
      }
    where
      final-state : LocState FS
      final-state = record s
        { regs   = writeReg (regs s) Output (exec-sigop-output si s)
        ; halted = exec-sigop-halts si s
        }

      -- THE key proof: after a Pure + fits-in-reg SigOp step, Output
      -- holds the register sentinel `unit-storedvalue` (NOT a pointer).
      output-is-sentinel : readReg (regs final-state) Output ≡ unit-storedvalue
      output-is-sentinel
        rewrite writeReg-same (regs s) Output (exec-sigop-output si s)
              | pure-pf
              | fits-eq = refl

      final-not-halted : halted final-state ≡ false
      final-not-halted rewrite pure-pf = refl

  ------------------------------------------------------------------------
  -- The provider: owns every Pure + fits-in-reg SigOp, defers otherwise.
  ------------------------------------------------------------------------

  pure-prim-provider : PartialProvider
  pure-prim-provider {A} {B} si with fits-in-reg? B in fits-eq
  ... | nothing = nothing
  ... | just fitness with effect si in pure-eq
  ...   | Pure    = just (Stack , pure-prim-contract si fitness fits-eq pure-eq)
  ...   | Emits _ = nothing
  ...   | Halts _ = nothing
