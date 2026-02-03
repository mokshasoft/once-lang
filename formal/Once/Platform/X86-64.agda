------------------------------------------------------------------------
-- Once.Platform.X86_64
--
-- x86-64 platform instantiation.
-- This is the SINGLE place that chooses Word64Interface for x86-64.
--
-- All x86-64 specific code imports from this module.
-- The Machine modules remain fully portable.
--
-- Part of OCP-0003: Migration to machine word semantics.
------------------------------------------------------------------------

module Once.Platform.X86-64 where

open import Once.Type
open import Once.Backend.Word64 using (Word64Interface)
open import Once.Backend.MachineInterface using (MachineInterface)

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
        ; semanticBundle
        )

------------------------------------------------------------------------
-- Contract Interface
------------------------------------------------------------------------

-- Import ContractInterfaceMachine with our ⟦_⟧
open import Once.Backend.ContractInterfaceMachine ⟦_⟧ public
  using (ContractInterface)

------------------------------------------------------------------------
-- IR Definition
------------------------------------------------------------------------

-- Import IRMachine with our ⟦_⟧
open import Once.IRMachine ⟦_⟧ public
  using (module IRDef)

------------------------------------------------------------------------
-- Semantics Definition
------------------------------------------------------------------------

-- Import SemanticsMachine with Word64Interface
open import Once.SemanticsMachine Word64Interface public
  using (Closure-η; module SemanticsDef)

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
  { Contract = λ {A} {B} _ → ⊤
  ; contract-assembly = λ {A} {B} {sem} _ → "    nop" ∷ []
  ; contract-nonempty = λ {A} {B} {sem} _ → s≤s z≤n
  }

-- | Placeholder contract type
PlaceholderContract : ∀ {A B : Type} → (⟦ A ⟧ → ⟦ B ⟧) → Set
PlaceholderContract {A} {B} _ = ⊤

-- | Trivial contract value for Prim constructors
trivial : ∀ {A B : Type} {sem : ⟦ A ⟧ → ⟦ B ⟧} → PlaceholderContract {A} {B} sem
trivial {A} {B} {sem} = tt

------------------------------------------------------------------------
-- Default IR and Semantics (using PlaceholderInterface)
------------------------------------------------------------------------

-- For convenience, provide default IR and eval using PlaceholderInterface
open IRDef PlaceholderInterface public
open SemanticsDef PlaceholderInterface public

------------------------------------------------------------------------
-- Backward Compatibility Aliases
------------------------------------------------------------------------

-- TrivialContract/TrivialInterface aliases for migration
TrivialContract : ∀ {A B : Type} → (⟦ A ⟧ → ⟦ B ⟧) → Set
TrivialContract {A} {B} = PlaceholderContract {A} {B}

TrivialInterface : ContractInterface
TrivialInterface = PlaceholderInterface
