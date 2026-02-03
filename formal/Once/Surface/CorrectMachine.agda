------------------------------------------------------------------------
-- Once.Surface.CorrectMachine
--
-- Correctness of elaboration from surface syntax to IR.
-- Proves that elaboration preserves semantics.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- PORTABILITY:
--   This module works with any MachineInterface instantiation:
--   - Word64Interface for x86-64, AArch64
--   - Word32Interface for x86-32, RISC-V 32
--
-- Unlike Once.Surface.Correct (which uses ℤ), this module uses
-- machine word semantics - ⟦ Int ⟧ = Word.
--
-- STATUS: Stub - proof structure established, details pending
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.Surface.CorrectMachine (MI : MachineInterface) where

private
  module MI' = MachineInterface MI

open import Once.Type
open import Once.SemanticBaseMachine MI using (⟦_⟧; Closure; env-addr; semantics; encode)
open import Once.Backend.ContractInterfaceMachine ⟦_⟧
open import Once.IRMachine ⟦_⟧
open import Once.SemanticsMachine MI as SM using (Closure-η; module SemanticsDef)
open import Once.Surface.Syntax using (Ctx; ∅; lookup; Expr; var; lam; app; pair; fst'; snd'; inl'; inr'; case'; unit; absurd; let'; int; str; add; sub; mul; div; mod'; neg; lt; le; gt; ge; ne) renaming (_,_ to _▸_; eq to eq')
import Once.Surface.Syntax as S
open import Once.Surface.Semantics MI using (Env; ε; _∷_; envLookup; evalSurface)
open import Once.Surface.ElaborateMachine MI

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- Parameterized Correctness Module
------------------------------------------------------------------------

-- | Correctness is parameterized by ContractInterface
--
module CorrectDef (CI : ContractInterface) where
  open ContractInterface CI
  open IRDef CI
  open SM.SemanticsDef CI using (eval)
  open ElaborateDef CI

  ------------------------------------------------------------------------
  -- Environment interpretation
  ------------------------------------------------------------------------

  -- Convert environment to nested product (environment as value)
  interpEnv : ∀ {n} {Γ : Ctx n} → Env Γ → ⟦ ⟦ Γ ⟧ᶜ ⟧
  interpEnv ε       = tt
  interpEnv (v ∷ ρ) = (interpEnv ρ , v)

  ------------------------------------------------------------------------
  -- Main correctness theorem
  ------------------------------------------------------------------------
  --
  -- The key theorem: elaboration preserves semantics.
  --
  -- For any surface expression e in environment ρ:
  --   evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)
  --
  -- This ensures that the compilation to IR doesn't change program behavior.
  --
  -- STATUS: Postulated for now. The proof structure follows Once.Surface.Correct
  -- but needs adaptation for the parameterized modules.
  --
  postulate
    elaborate-correct : ∀ {n} {Γ : Ctx n} {A} (ρ : Env Γ) (e : Expr Γ A) →
                        evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)

  ------------------------------------------------------------------------
  -- Supporting lemmas (postulated)
  ------------------------------------------------------------------------

  postulate
    -- Projection from environment
    proj-correct : ∀ {n} {Γ : Ctx n} (ρ : Env Γ) (i : Fin n) →
                   envLookup ρ i ≡ eval (proj {n} {Γ} i) (interpEnv ρ)

    -- Distribution over sums
    distribute-inl : ∀ {Γ A B : Type} (γ : ⟦ Γ ⟧) (a : ⟦ A ⟧) →
                     eval (distribute {Γ} {A} {B}) (γ , inj₁ a) ≡ inj₁ (γ , a)

    distribute-inr : ∀ {Γ A B : Type} (γ : ⟦ Γ ⟧) (b : ⟦ B ⟧) →
                     eval (distribute {Γ} {A} {B}) (γ , inj₂ b) ≡ inj₂ (γ , b)

------------------------------------------------------------------------
-- Key Property: Word-Based Semantics
------------------------------------------------------------------------
--
-- With this parameterized correctness module:
--
--   ⟦ Int ⟧ = Word (from MachineInterface)
--
-- The elaborate-correct theorem ensures that:
--   - Surface arithmetic (add, sub, mul, etc.) uses word operations
--   - IR arithmetic (addIR, subIR, mulIR, etc.) uses word operations
--   - These are THE SAME word operations from MachineInterface
--
-- No encode gap! No ℤ-to-Word conversion postulates needed.
--
-- The trust boundary is now:
--   Word64Interface.word-add ≡ x86 ADD instruction
--   (stated once in Word64.agda, not scattered across proofs)
--
------------------------------------------------------------------------
