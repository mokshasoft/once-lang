------------------------------------------------------------------------
-- Once.Platform.X86-64
--
-- x86-64 platform instantiation.
-- This is the SINGLE place that chooses Word64Interface for x86-64.
--
-- Part of OCP-0003: Orthogonal IR design.
--
-- ARCHITECTURE:
--   - Once.Contract: ContractInterface (machine-independent)
--   - Once.IR: IR (machine-independent)
--   - Once.Semantics: eval (machine-dependent)
--
-- This module provides:
--   1. ⟦_⟧ from SemanticBaseMachine Word64Interface
--   2. PlaceholderInterface for frontend modules
--   3. PlaceholderSemantics for evaluation
--   4. Instantiated IR and eval
------------------------------------------------------------------------

module Once.Platform.X86-64 where

open import Once.Type
open import Once.Backend.Word64 using (Word64Interface)
open import Once.Backend.MachineInterface using (MachineInterface)
open import Once.Contract

------------------------------------------------------------------------
-- Core Semantic Instantiation
------------------------------------------------------------------------

-- Instantiate SemanticBaseMachine with Word64Interface
open import Once.SemanticBaseMachine Word64Interface public
  using ( ⟦_⟧; ⟦Fix⟧; wrap; unwrap
        ; Closure; env-addr; semantics
        ; encode; encode-pair-addr; encode-inl-addr; encode-inr-addr
        ; encode-closure-addr; encode-int; encode-float; encode-str; encode-buffer
        ; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity
        ; int-add; int-sub; int-mul; int-div; int-mod; int-neg
        ; int-lt; int-eq; int-zero; int-one
        )

------------------------------------------------------------------------
-- Placeholder Contract (for frontend modules)
------------------------------------------------------------------------

-- Frontend modules that only need eval (not compilation) can use
-- PlaceholderInterface. It produces a "nop" instruction to satisfy
-- the nonempty requirement.

open import Data.Unit using (⊤; tt)
open import Data.Nat using (_≥_; s≤s; z≤n)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)

PlaceholderInterface : ContractInterface
PlaceholderInterface = record
  { Contract = λ A B → ⊤
  ; contract-assembly = λ _ → "    nop" ∷ []
  ; contract-nonempty = λ _ → s≤s z≤n
  }

------------------------------------------------------------------------
-- IR (parameterized by ⟦_⟧, uses PlaceholderInterface)
------------------------------------------------------------------------

open import Once.IR ⟦_⟧ public using (module IRDef)
open IRDef PlaceholderInterface public

------------------------------------------------------------------------
-- Semantics (using PlaceholderInterface)
------------------------------------------------------------------------

-- With the new design, Prim carries embedded semantics.
-- No ContractSemantics needed - eval just uses the embedded sem function.

open import Once.Semantics Word64Interface public
  using (module SemanticsDef)

open SemanticsDef PlaceholderInterface public

------------------------------------------------------------------------
-- Convenience: trivial contract for Prim
------------------------------------------------------------------------

-- | Placeholder contract value for Prim constructors
trivial : ∀ {A B : Type} → ContractInterface.Contract PlaceholderInterface A B
trivial = tt

------------------------------------------------------------------------
-- Backward Compatibility Aliases
------------------------------------------------------------------------

TrivialInterface : ContractInterface
TrivialInterface = PlaceholderInterface
