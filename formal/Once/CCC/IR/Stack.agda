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

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-assoc; ≤-refl)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.CCC.IR
open import Once.CCC.IR.Size using (ir-size)
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

open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)

-- | Maximum Product nesting depth in a well-formed functor
--
-- K, Id: no Products, depth 0
-- Sum: max of branches (Sum doesn't add save-slots)
-- Prod: 1 + max of components (Product needs 1 save-slot)
--
product-depth : ∀ {F} → WellFormedF F → ℕ
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
sum-depth : ∀ {F} → WellFormedF F → ℕ
sum-depth (wf-K _) = 0
sum-depth wf-Id = 0
sum-depth (wf-Sum wfL wfR) = suc (sum-depth wfL ⊔ sum-depth wfR)
sum-depth (wf-Prod wfL wfR) = sum-depth wfL ⊔ sum-depth wfR

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
ir-stack-requirement (Para wfF alg) = product-depth wfF +ℕ (sum-depth wfF *ℕ 2) +ℕ ir-stack-requirement alg +ℕ pair-slots
-- Out: extracts from ν-value, constant
ir-stack-requirement (Out _) = 0
-- in-ν: constructs ν-value (Lambek inverse of Out)
ir-stack-requirement (in-ν _ _) = 1
-- Ana: produces ν-value lazily, needs stack for coalgebra
ir-stack-requirement (Ana _ coalg) = ir-stack-requirement coalg +ℕ pair-slots
-- Hylo: fused cata ∘ ana, combines both requirements
ir-stack-requirement (Hylo _ _ alg coalg) = ir-stack-requirement alg +ℕ ir-stack-requirement coalg +ℕ pair-slots
-- Fuse: μ-anchored fusion (correct by construction)
ir-stack-requirement (Fuse _ _ alg transform) = ir-stack-requirement alg +ℕ ir-stack-requirement transform +ℕ pair-slots
-- Guard/Unguard removed: productivity follows from IR totality
-- Other
ir-stack-requirement (free-heap _) = 0
ir-stack-requirement (Prim _) = 0  -- Primitives manage own stack

------------------------------------------------------------------------
-- Layer Capacity
--
-- Capacity needed for layer processing, based on current layer functor.
------------------------------------------------------------------------

-- | Capacity needed for layer processing
--
-- This is the capacity needed to process a single layer of functor F,
-- where the layer may contain μ-values of functor G with algebra alg.
--
-- The capacity is: product-depth wfF + sum-depth wfF * 2 + ir-stack-requirement alg + pair-slots
--
-- Note: This depends on wfF (current layer) not wfG (μ-type functor).
-- This ensures capacity decreases as we recurse into Product/Sum sub-layers.
--
-- OCP-0003: Added sum-depth * 2 for Sum wrapper slots (Option B).
--
layer-capacity : ∀ {F G A} → WellFormedF F → WellFormedF G → IR (⟦ G ⟧T A) A → ℕ
layer-capacity wfF wfG alg = product-depth wfF +ℕ (sum-depth wfF *ℕ 2) +ℕ ir-stack-requirement alg +ℕ pair-slots

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

------------------------------------------------------------------------
-- Layer Capacity Lemmas
--
-- These lemmas support capacity proofs in process-layer for Product cases.
------------------------------------------------------------------------

open import Data.Nat.Properties using (+-comm; +-suc; m≤m⊔n; m≤n⊔m; +-monoˡ-≤; +-monoʳ-≤; ≤-trans)
open import Data.Nat using (s≤s)

-- | Cata stack requirement equals layer capacity at the same functor
--
-- ir-stack-requirement (Cata wfG alg) = layer-capacity wfG wfG alg
--
cata-req-eq-layer-cap : ∀ {G A} (wfG : WellFormedF G) (alg : IR (⟦ G ⟧T A) A) →
  ir-stack-requirement (Cata wfG alg) ≡ layer-capacity wfG wfG alg
cata-req-eq-layer-cap wfG alg = refl

-- | Layer capacity for Product left component after using 1 slot
--
-- If we have capacity for layer-capacity (wf-Prod wfL wfR) at slot n,
-- then after using 1 slot (at slot n+1), we have capacity for layer-capacity wfL.
--
-- TODO: Update proof to account for sum-depth * 2 in layer-capacity
layer-capacity-prod-left : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg ≤ cap →
  suc slot +ℕ layer-capacity wfL wfG alg ≤ cap
layer-capacity-prod-left wfL wfR wfG alg slot cap pf = SMP.!!

-- | Layer capacity for Product right component after using 1 slot
-- TODO: Update proof to account for sum-depth * 2 in layer-capacity
layer-capacity-prod-right : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg ≤ cap →
  suc slot +ℕ layer-capacity wfR wfG alg ≤ cap
layer-capacity-prod-right wfL wfR wfG alg slot cap pf = SMP.!!

-- | Layer capacity for Sum left component
-- For Sum with Option B: outer capacity includes wrapper slots (+2) that inner doesn't need yet
-- TODO: Update proof to account for sum-depth * 2 in layer-capacity
layer-capacity-sum-left : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg ≤ cap →
  slot +ℕ layer-capacity wfL wfG alg ≤ cap
layer-capacity-sum-left wfL wfR wfG alg slot cap pf = SMP.!!

-- | Layer capacity for Sum right component
-- TODO: Update proof to account for sum-depth * 2 in layer-capacity
layer-capacity-sum-right : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg ≤ cap →
  slot +ℕ layer-capacity wfR wfG alg ≤ cap
layer-capacity-sum-right wfL wfR wfG alg slot cap pf = SMP.!!