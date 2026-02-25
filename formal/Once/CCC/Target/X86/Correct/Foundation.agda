------------------------------------------------------------------------
-- Once.CCC.Target.X86.Correct.Foundation
--
-- Foundation lemmas for x86-64 correctness proofs.
-- Consolidates register/memory lemmas, fetch/step helpers, and
-- single-instruction execution lemmas that form the basis for
-- the main correctness proofs.
--
-- This module follows the AArch64 Foundation pattern to reduce
-- import fan-out and improve type-checking performance.
------------------------------------------------------------------------

module Once.CCC.Target.X86.Correct.Foundation where

open import Once.Type public
open import Once.IR public
open import Once.Semantics
  using (⟦_⟧; eval; Closure; encode; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity; wrap; ⟦Fix⟧)
  public

open ⟦Fix⟧ public

open import Once.Target.X86.Syntax public
open import Once.Target.X86.Semantics public
open Once.Target.X86.Semantics.State public
open Once.Target.X86.Semantics.Flags public
open import Once.CCC.Target.X86.CodeGen public

------------------------------------------------------------------------
-- Re-export common helpers
------------------------------------------------------------------------

-- Common fetch lemmas (polymorphic, work with any instruction type)
open import Once.CCC.Fetch
  using (fetch-0; fetch-1; fetch-2; fetch-3; fetch-append-left; fetch-append-right; fetch-past-end)
  public

-- Common memory helper lemmas (≡ᵇ-refl needed for RegisterLemmas)
-- Note: readMem-writeMem-same is also defined in RegisterLemmas, so we don't re-export from Common
open import Once.CCC.Memory
  using (≡ᵇ-refl)
  renaming (n≢n+word-size-bool to n≢n+word-size; n+word-size≢n-bool to n+word-size≢n; readMem-writeMem-diff-bool to readMem-writeMem-diff-common)
  public

-- Import encoding axioms from centralized Once.Postulates
-- NOTE: Most encode-* postulates eliminated in X86 via validity-based proofs.
-- Only encode-pair-construct still used (in IR/Pair.agda).
open import Once.Postulates
  using ( encode-pair-construct )
  public

------------------------------------------------------------------------
-- Re-export from helper modules (consolidated imports)
------------------------------------------------------------------------

-- FetchStep: fetch and step lemmas
open import Once.CCC.Target.X86.Correct.FetchStep public

-- InstrExec: instruction execution lemmas
open import Once.CCC.Target.X86.Correct.InstrExec public

-- RegisterLemmas: register read/write lemmas
open import Once.CCC.Target.X86.Correct.RegisterLemmas public

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
