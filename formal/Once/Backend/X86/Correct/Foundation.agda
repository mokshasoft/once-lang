------------------------------------------------------------------------
-- Once.Backend.X86.Correct.Foundation
--
-- Foundation lemmas for x86-64 correctness proofs.
-- Consolidates register/memory lemmas, fetch/step helpers, and
-- single-instruction execution lemmas that form the basis for
-- the main correctness proofs.
--
-- This module follows the AArch64 Foundation pattern to reduce
-- import fan-out and improve type-checking performance.
------------------------------------------------------------------------

module Once.Backend.X86.Correct.Foundation where

open import Once.Type public

-- X86 backend uses X86ContractInterface for real PrimContract proofs
open import Once.Backend.X86.Correct.PrimContract using (X86ContractInterface; PrimContract)
import Once.IR as IR
open IR.IRDef X86ContractInterface public

import Once.Semantics as Semantics
open Semantics using (Closure; encode; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity; wrap; ⟦Fix⟧) public
open import Once.SemanticBase using (⟦_⟧) public
open Semantics.SemanticsDef X86ContractInterface public

open ⟦Fix⟧ public

open import Once.Backend.X86.Syntax public
open import Once.Backend.X86.Semantics public
open Once.Backend.X86.Semantics.State public
open Once.Backend.X86.Semantics.Flags public
import Once.Backend.X86.CodeGen as CodeGen
open CodeGen using (simple-instr-count; pair-overhead; case-overhead; curry-overhead;
  injection-instr-count; apply-instr-count; case-setup-prefix-count; case-middle-count;
  pair-setup; pair-middle; pair-cleanup; inl-instrs; inr-instrs; apply-instrs;
  curry-closure-instrs; curry-thunk-setup-len-calc; curry-thunk-cleanup;
  case-setup-count; case-prefix-count; case-cleanup-count;
  case-jne-base; case-jmp-base; case-right-label-base;
  curry-thunk-label; curry-rip-offset; curry-end-label-base; curry-jmp-base;
  apply-consumed-slots; pair-setup-consumed-slots; thunk-setup-consumed-slots; curry-closure-consumed-slots;
  injection-consumed-slots; thunk-r15-slot; thunk-rbp-slot; pair-r14-slot; pair-r15-slot; pair-rbp-slot)
  public
-- Use CodeGenDef with X86ContractInterface
-- compile-x86 and compile-length now use contract-program and contract-length
-- which provide actual assembly from PrimContract for Prim nodes
open CodeGen.CodeGenDef X86ContractInterface public

-- Export contract-nonempty for compile-length>0 proof
open import Once.Backend.ContractInterface using (ContractInterface)
open ContractInterface X86ContractInterface public using (contract-nonempty; contract-length; contract-program)

------------------------------------------------------------------------
-- Re-export common helpers
------------------------------------------------------------------------

-- Common fetch lemmas (polymorphic, work with any instruction type)
open import Once.Backend.Common.Fetch
  using (fetch-0; fetch-1; fetch-2; fetch-3; fetch-append-left; fetch-append-right; fetch-past-end)
  public

-- Common memory helper lemmas (≡ᵇ-refl needed for RegisterLemmas)
-- Note: readMem-writeMem-same is also defined in RegisterLemmas, so we don't re-export from Common
open import Once.Backend.Common.Memory
  using (≡ᵇ-refl)
  renaming (n≢n+word-size-bool to n≢n+word-size; n+word-size≢n-bool to n+word-size≢n; readMem-writeMem-diff-bool to readMem-writeMem-diff-common)
  public

-- NOTE: All encode-* postulates eliminated in X86 via validity-based proofs.
-- encode-pair-construct and encode-closure-construct removed (unused)

-- IRSize: parameterized with X86ContractInterface
open import Once.Backend.Common.IRSize X86ContractInterface public
  using (ir-size; ∘-f-smaller; ∘-g-smaller; ⟨,⟩-f-smaller; ⟨,⟩-g-smaller;
         [,]-f-smaller; [,]-g-smaller; curry-smaller)

------------------------------------------------------------------------
-- Re-export from helper modules (consolidated imports)
------------------------------------------------------------------------

-- FetchStep: fetch and step lemmas
open import Once.Backend.X86.Correct.FetchStep public

-- InstrExec: instruction execution lemmas
open import Once.Backend.X86.Correct.InstrExec public

-- RegisterLemmas: register read/write lemmas
open import Once.Backend.X86.Correct.RegisterLemmas public

------------------------------------------------------------------------
-- Additional imports for client modules
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _∸_; _≡ᵇ_; _<_; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_) public
open import Data.Bool using (Bool; true; false; if_then_else_) public
open import Data.List using (List; []; _∷_; _++_; length) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect)
  renaming ([_] to ⟦_⟧ᵢ)
  public

------------------------------------------------------------------------
-- Helper: true ≢ false
------------------------------------------------------------------------

true≢false : true ≡ false → ⊥
true≢false ()
