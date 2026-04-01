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

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_) renaming (_+_ to _+ℕ_)
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
ir-stack-requirement (Cata wfF alg) = product-depth wfF +ℕ ir-stack-requirement alg +ℕ pair-slots
-- Para: paramorphism, like Cata but with access to original structure
-- product-depth accounts for save-slots needed during Product layer processing
ir-stack-requirement (Para wfF alg) = product-depth wfF +ℕ ir-stack-requirement alg +ℕ pair-slots
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
-- The capacity is: product-depth wfF + ir-stack-requirement alg + pair-slots
--
-- Note: This depends on wfF (current layer) not wfG (μ-type functor).
-- This ensures capacity decreases as we recurse into Product sub-layers.
--
layer-capacity : ∀ {F G A} → WellFormedF F → WellFormedF G → IR (⟦ G ⟧T A) A → ℕ
layer-capacity wfF wfG alg = product-depth wfF +ℕ ir-stack-requirement alg +ℕ pair-slots

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
layer-capacity-prod-left : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg ≤ cap →
  suc slot +ℕ layer-capacity wfL wfG alg ≤ cap
layer-capacity-prod-left wfL wfR wfG alg slot cap pf =
  let dL = product-depth wfL
      dR = product-depth wfR
      d = dL ⊔ dR
      ra = ir-stack-requirement alg
      ps = pair-slots
      -- layer-capacity (wf-Prod wfL wfR) wfG alg = suc d + ra + ps (left-associated)
      --   = suc (d + ra) + ps = suc ((d + ra) + ps) definitionally
      -- layer-capacity wfL wfG alg = dL + ra + ps
      -- Have: slot + layer-capacity (wf-Prod wfL wfR) wfG alg ≤ cap
      --     = slot + suc ((d + ra) + ps) ≤ cap
      -- Need: suc slot + (dL + ra + ps) ≤ cap
      --     = suc slot + ((dL + ra) + ps) ≤ cap
      --
      -- Key insight: suc d + ra + ps = suc (d + ra) + ps = suc ((d + ra) + ps)
      -- And we need: suc slot + ((dL + ra) + ps) ≤ cap

      -- step1: slot + suc ((d + ra) + ps) ≤ cap  (from pf)
      step1 : slot +ℕ suc ((d +ℕ ra) +ℕ ps) ≤ cap
      step1 = pf  -- layer-capacity (wf-Prod wfL wfR) = suc d + ra + ps = suc ((d+ra)+ps) definitionally

      -- step2: suc (slot + ((d + ra) + ps)) ≤ cap  (using +-suc)
      step2 : suc (slot +ℕ ((d +ℕ ra) +ℕ ps)) ≤ cap
      step2 = subst (_≤ cap) (+-suc slot ((d +ℕ ra) +ℕ ps)) step1

      -- step3: dL ≤ d
      dL≤d : dL ≤ d
      dL≤d = m≤m⊔n dL dR

      -- step4: dL + ra ≤ d + ra  (+-monoˡ-≤ adds on right)
      step4 : dL +ℕ ra ≤ d +ℕ ra
      step4 = +-monoˡ-≤ ra dL≤d

      -- step5: (dL + ra) + ps ≤ (d + ra) + ps
      step5 : (dL +ℕ ra) +ℕ ps ≤ (d +ℕ ra) +ℕ ps
      step5 = +-monoˡ-≤ ps step4

      -- step6: slot + ((dL + ra) + ps) ≤ slot + ((d + ra) + ps) (+-monoʳ-≤ adds on left)
      step6 : slot +ℕ ((dL +ℕ ra) +ℕ ps) ≤ slot +ℕ ((d +ℕ ra) +ℕ ps)
      step6 = +-monoʳ-≤ slot step5

      -- step7: suc (slot + ((dL + ra) + ps)) ≤ suc (slot + ((d + ra) + ps))
      step7 : suc (slot +ℕ ((dL +ℕ ra) +ℕ ps)) ≤ suc (slot +ℕ ((d +ℕ ra) +ℕ ps))
      step7 = s≤s step6

      -- suc slot + x = suc (slot + x) definitionally
      -- So suc slot + ((dL+ra)+ps) = suc (slot + ((dL+ra)+ps))
  in ≤-trans step7 step2

-- | Layer capacity for Product right component after using 1 slot
layer-capacity-prod-right : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg ≤ cap →
  suc slot +ℕ layer-capacity wfR wfG alg ≤ cap
layer-capacity-prod-right wfL wfR wfG alg slot cap pf =
  let dL = product-depth wfL
      dR = product-depth wfR
      d = dL ⊔ dR
      ra = ir-stack-requirement alg
      ps = pair-slots

      step1 : slot +ℕ suc ((d +ℕ ra) +ℕ ps) ≤ cap
      step1 = pf

      step2 : suc (slot +ℕ ((d +ℕ ra) +ℕ ps)) ≤ cap
      step2 = subst (_≤ cap) (+-suc slot ((d +ℕ ra) +ℕ ps)) step1

      dR≤d : dR ≤ d
      dR≤d = m≤n⊔m dL dR

      step4 : dR +ℕ ra ≤ d +ℕ ra
      step4 = +-monoˡ-≤ ra dR≤d

      step5 : (dR +ℕ ra) +ℕ ps ≤ (d +ℕ ra) +ℕ ps
      step5 = +-monoˡ-≤ ps step4

      step6 : slot +ℕ ((dR +ℕ ra) +ℕ ps) ≤ slot +ℕ ((d +ℕ ra) +ℕ ps)
      step6 = +-monoʳ-≤ slot step5

      step7 : suc (slot +ℕ ((dR +ℕ ra) +ℕ ps)) ≤ suc (slot +ℕ ((d +ℕ ra) +ℕ ps))
      step7 = s≤s step6

  in ≤-trans step7 step2

-- | Layer capacity for Sum left component (no slot used)
layer-capacity-sum-left : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg ≤ cap →
  slot +ℕ layer-capacity wfL wfG alg ≤ cap
layer-capacity-sum-left wfL wfR wfG alg slot cap pf =
  let dL = product-depth wfL
      dR = product-depth wfR
      d = dL ⊔ dR
      ra = ir-stack-requirement alg
      ps = pair-slots
      -- layer-capacity (wf-Sum wfL wfR) = d + ra + ps = (d + ra) + ps
      -- layer-capacity wfL = dL + ra + ps = (dL + ra) + ps
      dL≤d : dL ≤ d
      dL≤d = m≤m⊔n dL dR
      step1 : dL +ℕ ra ≤ d +ℕ ra
      step1 = +-monoˡ-≤ ra dL≤d
      step2 : (dL +ℕ ra) +ℕ ps ≤ (d +ℕ ra) +ℕ ps
      step2 = +-monoˡ-≤ ps step1
      step3 : slot +ℕ ((dL +ℕ ra) +ℕ ps) ≤ slot +ℕ ((d +ℕ ra) +ℕ ps)
      step3 = +-monoʳ-≤ slot step2
  in ≤-trans step3 pf

-- | Layer capacity for Sum right component (no slot used)
layer-capacity-sum-right : ∀ {FL FR G A}
  (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
  (alg : IR (⟦ G ⟧T A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg ≤ cap →
  slot +ℕ layer-capacity wfR wfG alg ≤ cap
layer-capacity-sum-right wfL wfR wfG alg slot cap pf =
  let dL = product-depth wfL
      dR = product-depth wfR
      d = dL ⊔ dR
      ra = ir-stack-requirement alg
      ps = pair-slots
      dR≤d : dR ≤ d
      dR≤d = m≤n⊔m dL dR
      step1 : dR +ℕ ra ≤ d +ℕ ra
      step1 = +-monoˡ-≤ ra dR≤d
      step2 : (dR +ℕ ra) +ℕ ps ≤ (d +ℕ ra) +ℕ ps
      step2 = +-monoˡ-≤ ps step1
      step3 : slot +ℕ ((dR +ℕ ra) +ℕ ps) ≤ slot +ℕ ((d +ℕ ra) +ℕ ps)
      step3 = +-monoʳ-≤ slot step2
  in ≤-trans step3 pf