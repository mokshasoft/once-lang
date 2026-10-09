-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.IR.Stack
--
-- Stack requirement calculations and capacity lemmas for IR.
--
-- Used by the Dispatcher for stack capacity verification.
------------------------------------------------------------------------

module Once.CCC.IR.Stack where

open import Data.Nat using (ℕ; suc; _≤_; _⊔_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.IR
open import Once.IRTy using (WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.SigOp.Info using (SigOpInfo)
import Once.CCC.Machine.SMPrimitives as SMP

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
-- Product Depth for Layer Processing
--
-- Computes the maximum nesting depth of Products in a functor.
-- Each level of Product nesting requires one save-slot during
-- layer processing (to preserve input-loc while processing components).
------------------------------------------------------------------------


-- | Maximum Product nesting depth in a well-formed functor
--
-- K, Id: no Products, depth 0
-- Sum: max of branches (Sum doesn't add save-slots)
-- Prod: 1 + max of components (Product needs 1 save-slot)
--
product-depth : ∀ {F} → WellFormedFI F → ℕ
product-depth (wf-K _) = 0
product-depth wf-Id = 0
product-depth (wf-Sum wfL wfR) = product-depth wfL ⊔ product-depth wfR
product-depth (wf-Prod wfL wfR) = suc (product-depth wfL ⊔ product-depth wfR)

------------------------------------------------------------------------
-- Sum Depth for Wrapper Allocation (OCP-0003 Option B)
--
-- For Option B (allocate new wrapper), each Sum layer allocates 2 slots
-- for the wrapper container. The slots accumulate as we nest Sums,
-- because wrapper slots are OUTPUT (persist), not temporary.
--
-- Example: Sum (Sum A B) C
--   If inj₁ (inj₁ a): inner wrapper (2 slots) + outer wrapper (2 slots) = 4 slots
--   If inj₂ c: outer wrapper (2 slots) = 2 slots
--   Maximum = 4 = 2 * sum-depth
------------------------------------------------------------------------

-- | Maximum Sum nesting depth in a well-formed functor
--
-- K, Id: no Sums, depth 0
-- Sum: 1 + max of branches (Sum adds 1 level of wrapper nesting)
-- Prod: max of components (Product doesn't add wrapper nesting)
--
sum-depth : ∀ {F} → WellFormedFI F → ℕ
sum-depth (wf-K _) = 0
sum-depth wf-Id = 0
sum-depth (wf-Sum wfL wfR) = suc (sum-depth wfL ⊔ sum-depth wfR)
sum-depth (wf-Prod wfL wfR) = sum-depth wfL ⊔ sum-depth wfR

------------------------------------------------------------------------
-- Stack Requirement
------------------------------------------------------------------------

ir-stack-requirement : ∀ {A B} → IR A B → ℕ
-- D062: stack requirement of a Fuse/Hylo's natural transform.
ir-stack-requirement id = 0
ir-stack-requirement (g ∘ f) = ir-stack-requirement f +ℕ ir-stack-requirement g
ir-stack-requirement ⟨ f , g ⟩ = 1 +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots
ir-stack-requirement fst = 0
ir-stack-requirement snd = 0
ir-stack-requirement inl = pair-slots
ir-stack-requirement inr = pair-slots
ir-stack-requirement (case f g) = ir-stack-requirement f +ℕ ir-stack-requirement g
ir-stack-requirement terminal = 0
ir-stack-requirement initial = 0
ir-stack-requirement (curry _) = pair-slots
ir-stack-requirement apply = pair-slots
-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
-- Recursion schemes (OCP-0003) - WellFormedFI proofs are ignored for stack
-- In: constructs μ-value, similar to fold
ir-stack-requirement (In _) = 1
-- out-μ: destructs μ-value (Lambek inverse of In), constant
ir-stack-requirement (out-μ _) = 0
-- Cata: tail-recursive consumption, needs stack for intermediate results
-- Uses a while-loop pattern at runtime
-- product-depth accounts for save-slots needed during Product layer processing
-- sum-depth * 2 accounts for Sum wrapper slots (OCP-0003 Option B)
ir-stack-requirement (Cata wfF alg) = product-depth wfF +ℕ (sum-depth wfF *ℕ 2) +ℕ ir-stack-requirement alg +ℕ pair-slots
-- Para: paramorphism, like Cata but with access to original structure
-- product-depth accounts for save-slots needed during Product layer processing
-- sum-depth * 2 accounts for Sum wrapper slots (OCP-0003 Option B)
-- Out: extracts from ν-value, constant
ir-stack-requirement (Out _) = 0
-- in-ν: constructs ν-value (Lambek inverse of Out)
ir-stack-requirement (in-ν _) = 1
-- Ana: produces ν-value lazily, needs stack for coalgebra
ir-stack-requirement (Ana _ coalg) = ir-stack-requirement coalg +ℕ pair-slots
-- Hylo: fused cata ∘ ana, combines both requirements
-- Fuse: μ-anchored fusion (correct by construction)
-- Guard/Unguard removed: productivity follows from IR totality
-- Other
ir-stack-requirement (SigOp _) = 0  -- Primitives manage own stack
ir-stack-requirement (Call _) = 0   -- the callee has its own frame
ir-stack-requirement (const _ _) = 0  -- Pure register write, no stack


------------------------------------------------------------------------
-- Scratch Requirement (alias for stack requirement)
--
-- OCP-0003: scratch-bounded uses ir-scratch-requirement relative to OUTPUT.
-- For now, scratch requirement equals stack requirement. Later phases may
-- refine this to track only temporary (non-output) slots.
------------------------------------------------------------------------

ir-scratch-requirement : ∀ {A B} → IR A B → ℕ
ir-scratch-requirement = ir-stack-requirement

-- (D271: the layer-capacity model — `layer-capacity`, its Sum/Prod lemmas and
-- `layer-cap-bound` — is deleted. Nothing outside this module used it, and its
-- two postulated cases `sum-`/`prod-layer-cap-bound` were FALSE, as the comments
-- here said (a Sum of two `Id` layers needs 2 + the whole cata's requirement).)

------------------------------------------------------------------------
-- Stack Requirement Lemmas
------------------------------------------------------------------------

∘-stack-req : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-stack-requirement (g ∘ f) ≡ ir-stack-requirement f +ℕ ir-stack-requirement g
∘-stack-req f g = refl

⟨,⟩-stack-req : ∀ {A B C} (f : IR A B) (g : IR A C) →
  ir-stack-requirement ⟨ f , g ⟩ ≡ 1 +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots
⟨,⟩-stack-req f g = refl

sigOp-stack-req : ∀ {A B} (si : SigOpInfo A B) →
  ir-stack-requirement (SigOp {A} {B} si) ≡ 0
sigOp-stack-req _ = refl

------------------------------------------------------------------------
-- Capacity Lemmas
------------------------------------------------------------------------

⟨,⟩-capacity-for-pair : ∀ {A B C} (f : IR A B) (g : IR A C) (slot cap : ℕ) →
  slot +ℕ ir-stack-requirement ⟨ f , g ⟩ ≤ cap →
  (slot +ℕ 1) +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots ≤ cap
⟨,⟩-capacity-for-pair f g slot cap pf =
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

