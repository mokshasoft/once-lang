-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.IR.Stack
--
-- Stack requirement calculations and capacity lemmas for IR.
--
-- Used by the Dispatcher for stack capacity verification.
------------------------------------------------------------------------

module Once.CCC.IR.Stack where

open import Data.Nat using (ℕ; zero; suc; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-assoc; ≤-refl)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.CCC.IR
open import Once.CCC.IR.Size using (ir-size)

------------------------------------------------------------------------
-- Stack Layout Constants
------------------------------------------------------------------------

-- | Number of slots needed to store a pair (two words)
pair-slots : ℕ
pair-slots = 2

-- | Number of slots needed to store a closure (env-addr + code-ptr)
closure-slots : ℕ
closure-slots = 2

------------------------------------------------------------------------
-- Stack Requirement
------------------------------------------------------------------------

ir-stack-requirement : ∀ {A B} → IR A B → ℕ
ir-stack-requirement id = 0
ir-stack-requirement (g ∘ f) = ir-stack-requirement f +ℕ ir-stack-requirement g
ir-stack-requirement (⟨ f , g ⟩ _) = 1 +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots
ir-stack-requirement fst = 0
ir-stack-requirement snd = 0
ir-stack-requirement (inl _) = pair-slots
ir-stack-requirement (inr _) = pair-slots
ir-stack-requirement (case f g) = ir-stack-requirement f +ℕ ir-stack-requirement g
ir-stack-requirement terminal = 0
ir-stack-requirement initial = 0
ir-stack-requirement (curry _ _) = pair-slots
ir-stack-requirement apply = pair-slots
ir-stack-requirement arr = 0
-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
-- Recursion schemes (OCP-0003) - WellFormedF proofs are ignored for stack
-- In: constructs μ-value, similar to fold
ir-stack-requirement (In _ _) = 1
-- Cata: tail-recursive consumption, needs stack for intermediate results
-- Uses a while-loop pattern at runtime
ir-stack-requirement (Cata _ alg) = ir-stack-requirement alg +ℕ pair-slots
-- Out: extracts from ν-value, constant
ir-stack-requirement (Out _) = 0
-- Ana: produces ν-value lazily, needs stack for coalgebra
ir-stack-requirement (Ana _ coalg) = ir-stack-requirement coalg +ℕ pair-slots
-- Hylo: fused cata ∘ ana, combines both requirements
ir-stack-requirement (Hylo _ alg coalg) = ir-stack-requirement alg +ℕ ir-stack-requirement coalg +ℕ pair-slots
-- Guard/Unguard removed: productivity follows from IR totality
-- Other
ir-stack-requirement (free-heap _) = 0
ir-stack-requirement (Prim _) = 0  -- Primitives manage own stack

------------------------------------------------------------------------
-- Stack Requirement Lemmas
------------------------------------------------------------------------

∘-stack-req : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-stack-requirement (g ∘ f) ≡ ir-stack-requirement f +ℕ ir-stack-requirement g
∘-stack-req f g = refl

⟨,⟩-stack-req : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) →
  ir-stack-requirement (⟨ f , g ⟩ m) ≡ 1 +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots
⟨,⟩-stack-req f g m = refl

prim-stack-req : ∀ {A B} (name : String) →
  ir-stack-requirement (Prim {A} {B} name) ≡ 0
prim-stack-req _ = refl

------------------------------------------------------------------------
-- Capacity Lemmas
------------------------------------------------------------------------

⟨,⟩-capacity-for-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) (slot cap : ℕ) →
  slot +ℕ ir-stack-requirement (⟨ f , g ⟩ m) ≤ cap →
  (slot +ℕ 1) +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots ≤ cap
⟨,⟩-capacity-for-pair f g m slot cap pf =
  let rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      ps = pair-slots
      step1 : slot +ℕ (1 +ℕ rf +ℕ rg +ℕ ps) ≤ cap
      step1 = pf
      step2 : (slot +ℕ 1) +ℕ (rf +ℕ rg +ℕ ps) ≤ cap
      step2 = subst (_≤ cap) (sym (+-assoc slot 1 (rf +ℕ rg +ℕ ps))) step1
      step3 : (slot +ℕ 1) +ℕ ((rf +ℕ rg) +ℕ ps) ≤ cap
      step3 = step2
      step4 : ((slot +ℕ 1) +ℕ (rf +ℕ rg)) +ℕ ps ≤ cap
      step4 = subst (_≤ cap) (sym (+-assoc (slot +ℕ 1) (rf +ℕ rg) ps)) step3
      step5 : (((slot +ℕ 1) +ℕ rf) +ℕ rg) +ℕ ps ≤ cap
      step5 = subst (λ x → x +ℕ ps ≤ cap) (sym (+-assoc (slot +ℕ 1) rf rg)) step4
  in step5