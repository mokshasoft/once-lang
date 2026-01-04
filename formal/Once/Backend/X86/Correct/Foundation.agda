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
open import Once.IR public
open import Once.Semantics
  using (⟦_⟧; eval; Closure; encode; encode-unit; encode-fix-wrap; encode-fix-unwrap; encode-arr-identity; wrap; ⟦Fix⟧)
  public

open ⟦Fix⟧ public

open import Once.Backend.X86.Syntax public
open import Once.Backend.X86.Semantics public
open Once.Backend.X86.Semantics.State public
open Once.Backend.X86.Semantics.Flags public
open import Once.Backend.X86.CodeGen public

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
  renaming (n≢n+8-bool to n≢n+8; n+8≢n-bool to n+8≢n; readMem-writeMem-diff-bool to readMem-writeMem-diff-common)
  public

-- Import encoding axioms from centralized Once.Postulates
open import Once.Postulates
  using ( encode-pair-fst; encode-pair-snd
        ; encode-inl-tag; encode-inl-val
        ; encode-inr-tag; encode-inr-val
        ; encode-pair-construct
        ; encode-inl-construct; encode-inr-construct
        ; encode-closure-construct
        )
  public

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
-- Encoded memory postulate (for initial state)
------------------------------------------------------------------------

postulate
  encodedMemory : Memory

------------------------------------------------------------------------
-- State predicates (for correctness proofs)
------------------------------------------------------------------------

-- | State transformation predicate
-- Captures what running an IR term does to the state.
IRCorrectAt : ∀ {A B : Type} → IR A B → ⟦ A ⟧ → State → State → Set
IRCorrectAt ir x s s' =
  run (compile-x86 ir) s ≡ just s'
  × halted s' ≡ true
  × readReg (regs s') rax ≡ encode (eval ir x)

-- | Valid input state predicate
ValidInputState : ∀ {A : Type} → ⟦ A ⟧ → State → Set
ValidInputState x s =
  halted s ≡ false
  × pc s ≡ 0
  × readReg (regs s) rdi ≡ encode x
  × memory s ≡ encodedMemory

-- | The main correctness property we want to prove for each IR term
-- This will be proven by mutual recursion on IR structure.
IRCorrect : ∀ {A B : Type} → IR A B → Set
IRCorrect {A} {B} ir = ∀ (x : ⟦ A ⟧) (s : State) →
  ValidInputState x s →
  ∃[ s' ] IRCorrectAt ir x s s'

------------------------------------------------------------------------
-- Initial state with input
------------------------------------------------------------------------

-- | Create initial state with input value in rdi
initWithInput : ∀ {A : Type} → ⟦ A ⟧ → State
initWithInput x = mkstate
  (writeReg emptyRegFile rdi (encode x))
  encodedMemory
  initFlags
  0
  false

-- | Property: input is correctly placed in rdi
initWithInput-rdi : ∀ {A : Type} (x : ⟦ A ⟧) →
  readReg (regs (initWithInput x)) rdi ≡ encode x
initWithInput-rdi x = readReg-writeReg-same emptyRegFile rdi (encode x)

-- | Property: initial state is not halted
initWithInput-halted : ∀ {A : Type} (x : ⟦ A ⟧) →
  halted (initWithInput x) ≡ false
initWithInput-halted x = refl

-- | Property: initial pc is 0
initWithInput-pc : ∀ {A : Type} (x : ⟦ A ⟧) →
  pc (initWithInput x) ≡ 0
initWithInput-pc x = refl

-- | Property: initial memory is encodedMemory
initWithInput-memory : ∀ {A : Type} (x : ⟦ A ⟧) →
  memory (initWithInput x) ≡ encodedMemory
initWithInput-memory x = refl

------------------------------------------------------------------------
-- Helper: true ≢ false
------------------------------------------------------------------------

true≢false : true ≡ false → ⊥
true≢false ()
