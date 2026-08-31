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

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; s≤s) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc; ≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; m≤n+m; m≤m+n; +-monoˡ-≤; +-monoʳ-≤; ⊔-monoˡ-≤; ⊔-lub; *-monoˡ-≤; m+n≤o⇒m≤o; m+n≤o⇒n≤o)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.IR
open import Once.IR.Size using (ir-size)
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
ir-stack-requirement-nt : ∀ {G F} → NatTr G F → ℕ
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
-- OCP-0003: fold/unfold removed. Use In/Cata/Out/Ana instead.
-- Recursion schemes (OCP-0003) - WellFormedFI proofs are ignored for stack
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
ir-stack-requirement (Hylo _ _ alg t) = ir-stack-requirement alg +ℕ ir-stack-requirement-nt t +ℕ pair-slots
-- Fuse: μ-anchored fusion (correct by construction)
ir-stack-requirement (Fuse _ _ alg t) = ir-stack-requirement alg +ℕ ir-stack-requirement-nt t +ℕ pair-slots
-- Guard/Unguard removed: productivity follows from IR totality
-- Other
ir-stack-requirement (free-heap _) = 0
ir-stack-requirement (SigOp _) = 0  -- Primitives manage own stack
ir-stack-requirement (const _ _) = 0  -- Pure register write, no stack

ir-stack-requirement-nt ntId         = 0
ir-stack-requirement-nt (ntK ir)     = ir-stack-requirement ir
ir-stack-requirement-nt (ntFst t)    = ir-stack-requirement-nt t
ir-stack-requirement-nt (ntSnd t)    = ir-stack-requirement-nt t
ir-stack-requirement-nt (ntCase t u) = ir-stack-requirement-nt t +ℕ ir-stack-requirement-nt u
ir-stack-requirement-nt (ntInl t)    = ir-stack-requirement-nt t
ir-stack-requirement-nt (ntInr t)    = ir-stack-requirement-nt t
ir-stack-requirement-nt (ntPair t u) = ir-stack-requirement-nt t +ℕ ir-stack-requirement-nt u

------------------------------------------------------------------------
-- Scratch Requirement (alias for stack requirement)
--
-- OCP-0003: scratch-bounded uses ir-scratch-requirement relative to OUTPUT.
-- For now, scratch requirement equals stack requirement. Later phases may
-- refine this to track only temporary (non-output) slots.
------------------------------------------------------------------------

ir-scratch-requirement : ∀ {A B} → IR A B → ℕ
ir-scratch-requirement = ir-stack-requirement

------------------------------------------------------------------------
-- Layer Capacity (Redesigned OCP-0003)
--
-- The capacity model is fundamentally based on:
-- 1. Each Product level needs 1 save-slot
-- 2. Each Sum level needs 2 wrapper-slots
-- 3. The algebra needs ir-stack-requirement alg + pair-slots for output
--
-- The key insight is that capacity is computed from the FUNCTOR STRUCTURE
-- (product-depth, sum-depth), not from recursion depth. With reclamation,
-- each level reuses slots from completed subtrees.
--
-- For the capacity INEQUALITY LEMMAS to work, we need:
--   layer-capacity (wf-Prod wfL wfR) ≥ 1 + max(layer-capacity wfL, layer-capacity wfR)
--   layer-capacity (wf-Sum wfL wfR) ≥ 2 + max(layer-capacity wfL, layer-capacity wfR)
--
-- The formula: product-depth wfF + sum-depth wfF * 2 + ir-stack-requirement alg + pair-slots
-- satisfies these because:
--   product-depth (wf-Prod wfL wfR) = suc (product-depth wfL ⊔ product-depth wfR)
--   sum-depth (wf-Sum wfL wfR) = suc (sum-depth wfL ⊔ sum-depth wfR)
------------------------------------------------------------------------

-- | Layer capacity based on functor structure
--
-- This uses the structural product-depth and sum-depth of F.
-- The Id case is special: it requires ir-stack-requirement (Cata wfG alg)
-- because processing Id recurses into the full Cata.
--
-- For non-Id functors: product-depth wfF + sum-depth wfF * 2 + alg + ps
-- For Id: ir-stack-requirement (Cata wfG alg)
-- | Layer capacity based on functor structure
--
-- Key insight: Allocation models differ between Sum and Prod:
--
-- - Sum: Only ONE child is processed (inj₁ or inj₂). The wrapper (2 slots)
--   is allocated at the child's reclaimed position.
--   Final bound: reclaimable + 2 ≤ start + capChild + 2 = start + (2 + capChild)
--   So layer-capacity Sum = 2 + max(capL, capR)
--
-- - Prod: BOTH children are processed sequentially. Left child's output persists
--   while right child runs, so capacities ADD rather than share via reclaim.
--   Final bound: start + 1 + capL + capR (save-slot + left output + right processing)
--   So layer-capacity Prod = 1 + capL + capR
--
-- Note: The MAX formula for Prod would only be correct with "perfect scratch reclaim"
-- where left child fully reclaims before right child starts. The current implementation
-- does not enforce this invariant, so we use SUM to be sound.
--
-- D131: the algebra carries an environment `E`; the capacity formulas are
-- unchanged (the environment is a value the fold holds, not extra layer work).
layer-capacity : ∀ {F G E A} → WellFormedFI F → WellFormedFI G → IR (E * ⟦ G ⟧TI A) A → ℕ
layer-capacity wf-Id wfG alg = ir-stack-requirement (Cata wfG alg)
layer-capacity (wf-K _) _ alg = ir-stack-requirement alg +ℕ pair-slots
-- Sum: wrapper (2 slots) allocated AFTER child reclaims, so add 2 to max child capacity
-- NOT max(child, 2) - the wrapper is allocated at reclaimed position, not overlapping
layer-capacity (wf-Sum wfL wfR) wfG alg = 2 +ℕ (layer-capacity wfL wfG alg ⊔ layer-capacity wfR wfG alg)
-- Prod: both children processed sequentially, outputs persist, so ADD capacities
layer-capacity (wf-Prod wfL wfR) wfG alg = 1 +ℕ layer-capacity wfL wfG alg +ℕ layer-capacity wfR wfG alg

------------------------------------------------------------------------
-- Stack Requirement Lemmas
------------------------------------------------------------------------

∘-stack-req : ∀ {A B C} (f : IR A B) (g : IR B C) →
  ir-stack-requirement (g ∘ f) ≡ ir-stack-requirement f +ℕ ir-stack-requirement g
∘-stack-req f g = refl

⟨,⟩-stack-req : ∀ {A B C} (f : IR A B) (g : IR A C) (m : AllocMode) →
  ir-stack-requirement (⟨ f , g ⟩ m) ≡ 1 +ℕ ir-stack-requirement f +ℕ ir-stack-requirement g +ℕ pair-slots
⟨,⟩-stack-req f g m = refl

sigOp-stack-req : ∀ {A B} (si : SigOpInfo A B) →
  ir-stack-requirement (SigOp {A} {B} si) ≡ 0
sigOp-stack-req _ = refl

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

-- Note: ir-stack-requirement (Cata wfG alg) uses a flat formula based on
-- product-depth/sum-depth, while layer-capacity uses a recursive formula.
-- These compute the same upper bound but via different structures.
-- The recursive layer-capacity is used for the capacity inequality lemmas.

-- | Layer capacity for Product left component after using 1 slot
--
-- If we have capacity for layer-capacity (wf-Prod wfL wfR) at slot n,
-- then after using 1 slot (at slot n+1), we have capacity for layer-capacity wfL.
--
-- With SUM definition:
--   layer-capacity (wf-Prod wfL wfR) = 1 + capL + capR
--   Given: slot + (1 + capL + capR) ≤ cap
--   Need: suc slot + capL ≤ cap
--   Since: capL ≤ capL + capR, this follows from monotonicity
layer-capacity-prod-left : ∀ {FL FR G E A}
  (wfL : WellFormedFI FL) (wfR : WellFormedFI FR) (wfG : WellFormedFI G)
  (alg : IR (E * ⟦ G ⟧TI A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg ≤ cap →
  suc slot +ℕ layer-capacity wfL wfG alg ≤ cap
layer-capacity-prod-left wfL wfR wfG alg slot cap pf =
  let capL = layer-capacity wfL wfG alg
      capR = layer-capacity wfR wfG alg
      -- capL ≤ capL + capR
      cap-mono : capL ≤ capL +ℕ capR
      cap-mono = m≤m+n capL capR
      -- suc slot + capL ≤ suc slot + (capL + capR)
      step1 : suc slot +ℕ capL ≤ suc slot +ℕ (capL +ℕ capR)
      step1 = +-monoʳ-≤ (suc slot) cap-mono
      -- Convert pf: slot + (1 + capL + capR) ≤ cap  to  suc slot + (capL + capR) ≤ cap
      -- layer-capacity (wf-Prod wfL wfR) = 1 + capL + capR = suc (capL + capR)
      -- slot + suc (capL + capR) = suc slot + (capL + capR) by +-suc
      eq : slot +ℕ suc (capL +ℕ capR) ≡ suc slot +ℕ (capL +ℕ capR)
      eq = +-suc slot (capL +ℕ capR)
      step2 : suc slot +ℕ (capL +ℕ capR) ≤ cap
      step2 = subst (_≤ cap) eq pf
  in ≤-trans step1 step2

-- | Layer capacity for Product right component after using 1 slot
--
-- With SUM definition:
--   layer-capacity (wf-Prod wfL wfR) = 1 + capL + capR
--   Given: slot + (1 + capL + capR) ≤ cap
--   Need: suc slot + capR ≤ cap
--   Since: capR ≤ capL + capR, this follows from monotonicity
layer-capacity-prod-right : ∀ {FL FR G E A}
  (wfL : WellFormedFI FL) (wfR : WellFormedFI FR) (wfG : WellFormedFI G)
  (alg : IR (E * ⟦ G ⟧TI A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg ≤ cap →
  suc slot +ℕ layer-capacity wfR wfG alg ≤ cap
layer-capacity-prod-right wfL wfR wfG alg slot cap pf =
  let capL = layer-capacity wfL wfG alg
      capR = layer-capacity wfR wfG alg
      -- capR ≤ capL + capR
      cap-mono : capR ≤ capL +ℕ capR
      cap-mono = m≤n+m capR capL
      -- suc slot + capR ≤ suc slot + (capL + capR)
      step1 : suc slot +ℕ capR ≤ suc slot +ℕ (capL +ℕ capR)
      step1 = +-monoʳ-≤ (suc slot) cap-mono
      -- Convert pf: slot + (1 + capL + capR) ≤ cap  to  suc slot + (capL + capR) ≤ cap
      eq : slot +ℕ suc (capL +ℕ capR) ≡ suc slot +ℕ (capL +ℕ capR)
      eq = +-suc slot (capL +ℕ capR)
      step2 : suc slot +ℕ (capL +ℕ capR) ≤ cap
      step2 = subst (_≤ cap) eq pf
  in ≤-trans step1 step2

-- | Layer capacity for Sum left component
-- With reclamation, Sum formula: 2 + (capL ⊔ capR)
--
--   Given: slot + (2 + (capL ⊔ capR)) ≤ cap
--   Need: slot + capL ≤ cap
--   Since capL ≤ capL ⊔ capR ≤ 2 + (capL ⊔ capR), this follows from monotonicity
layer-capacity-sum-left : ∀ {FL FR G E A}
  (wfL : WellFormedFI FL) (wfR : WellFormedFI FR) (wfG : WellFormedFI G)
  (alg : IR (E * ⟦ G ⟧TI A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg ≤ cap →
  slot +ℕ layer-capacity wfL wfG alg ≤ cap
layer-capacity-sum-left wfL wfR wfG alg slot cap pf =
  let capL = layer-capacity wfL wfG alg
      capR = layer-capacity wfR wfG alg
      -- capL ≤ capL ⊔ capR ≤ 2 + (capL ⊔ capR)
      cap-mono : capL ≤ 2 +ℕ (capL ⊔ capR)
      cap-mono = ≤-trans (m≤m⊔n capL capR) (m≤n+m (capL ⊔ capR) 2)
      -- slot + capL ≤ slot + (2 + (capL ⊔ capR))
      step1 : slot +ℕ capL ≤ slot +ℕ (2 +ℕ (capL ⊔ capR))
      step1 = +-monoʳ-≤ slot cap-mono
  in ≤-trans step1 pf

-- | Layer capacity for Sum right component
-- Symmetric to sum-left, using m≤n⊔m
layer-capacity-sum-right : ∀ {FL FR G E A}
  (wfL : WellFormedFI FL) (wfR : WellFormedFI FR) (wfG : WellFormedFI G)
  (alg : IR (E * ⟦ G ⟧TI A) A) (slot cap : ℕ) →
  slot +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg ≤ cap →
  slot +ℕ layer-capacity wfR wfG alg ≤ cap
layer-capacity-sum-right wfL wfR wfG alg slot cap pf =
  let capL = layer-capacity wfL wfG alg
      capR = layer-capacity wfR wfG alg
      -- capR ≤ capL ⊔ capR ≤ 2 + (capL ⊔ capR)
      cap-mono : capR ≤ 2 +ℕ (capL ⊔ capR)
      cap-mono = ≤-trans (m≤n⊔m capL capR) (m≤n+m (capL ⊔ capR) 2)
      -- slot + capR ≤ slot + (2 + (capL ⊔ capR))
      step1 : slot +ℕ capR ≤ slot +ℕ (2 +ℕ (capL ⊔ capR))
      step1 = +-monoʳ-≤ slot cap-mono
  in ≤-trans step1 pf

------------------------------------------------------------------------
-- Sum Wrapper Capacity Lemmas (OCP-0003 Option B with Reclamation)
--
-- With reclamation, Sum processing is:
--   1. Process child -> uses capChild slots, reclaims to reclaimable
--   2. Allocate wrapper at reclaimable position -> uses 2 more slots
-- Final: reclaimable + 2 ≤ start + capChild + 2
--
-- Formula: layer-capacity (wf-Sum wfL wfR) = 2 + (capL ⊔ capR)
--
-- The lemma shows: capChild + 2 ≤ 2 + (capL ⊔ capR)
-- Which follows from capChild ≤ capL ⊔ capR (monotonicity of ⊔).
------------------------------------------------------------------------

-- | Sum child capacity + wrapper ≤ Sum parent capacity (left child)
--
-- capL + 2 ≤ 2 + (capL ⊔ capR)
-- Since capL ≤ capL ⊔ capR, we have capL + 2 ≤ (capL ⊔ capR) + 2 = 2 + (capL ⊔ capR)
sum-wrapper-fits-left : ∀ {FL FR G E A}
  (wfL : WellFormedFI FL) (wfR : WellFormedFI FR) (wfG : WellFormedFI G)
  (alg : IR (E * ⟦ G ⟧TI A) A) →
  layer-capacity wfL wfG alg +ℕ 2 ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
sum-wrapper-fits-left wfL wfR wfG alg =
  let capL = layer-capacity wfL wfG alg
      capR = layer-capacity wfR wfG alg
      -- capL ≤ capL ⊔ capR
      cap-mono : capL ≤ capL ⊔ capR
      cap-mono = m≤m⊔n capL capR
      -- capL + 2 ≤ (capL ⊔ capR) + 2
      step1 : capL +ℕ 2 ≤ (capL ⊔ capR) +ℕ 2
      step1 = +-monoˡ-≤ 2 cap-mono
      -- (capL ⊔ capR) + 2 = 2 + (capL ⊔ capR) by commutativity
      eq : (capL ⊔ capR) +ℕ 2 ≡ 2 +ℕ (capL ⊔ capR)
      eq = +-comm (capL ⊔ capR) 2
  in subst (capL +ℕ 2 ≤_) eq step1

-- | Sum child capacity + wrapper ≤ Sum parent capacity (right child)
-- Symmetric using m≤n⊔m
sum-wrapper-fits-right : ∀ {FL FR G E A}
  (wfL : WellFormedFI FL) (wfR : WellFormedFI FR) (wfG : WellFormedFI G)
  (alg : IR (E * ⟦ G ⟧TI A) A) →
  layer-capacity wfR wfG alg +ℕ 2 ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
sum-wrapper-fits-right wfL wfR wfG alg =
  let capL = layer-capacity wfL wfG alg
      capR = layer-capacity wfR wfG alg
      -- capR ≤ capL ⊔ capR
      cap-mono : capR ≤ capL ⊔ capR
      cap-mono = m≤n⊔m capL capR
      -- capR + 2 ≤ (capL ⊔ capR) + 2
      step1 : capR +ℕ 2 ≤ (capL ⊔ capR) +ℕ 2
      step1 = +-monoˡ-≤ 2 cap-mono
      -- (capL ⊔ capR) + 2 = 2 + (capL ⊔ capR) by commutativity
      eq : (capL ⊔ capR) +ℕ 2 ≡ 2 +ℕ (capL ⊔ capR)
      eq = +-comm (capL ⊔ capR) 2
  in subst (capR +ℕ 2 ≤_) eq step1

------------------------------------------------------------------------
-- Capacity Conversion Lemma
--
-- ir-stack-requirement (Cata wfG alg) ≥ layer-capacity wfF wfG alg
-- for any sub-functor wfF.
--
-- This allows converting from the flat formula (used for total capacity)
-- to the recursive formula (used for layer-specific capacity).
--
-- The proof is by structural induction on wfF:
-- - K: alg + ps ≤ pd(G) + sd(G)*2 + alg + ps (trivially since pd,sd ≥ 0)
-- - Id: layer-capacity = ir-stack-requirement by definition
-- - Sum: 2 + (capL ⊔ capR) ≤ ir-req - BLOCKED when children contain Id
-- - Prod: 1 + (capL ⊔ capR) ≤ ir-req - BLOCKED when children contain Id
------------------------------------------------------------------------

-- Helper: ir-req ≥ pair-slots (= 2)
-- ir-stack-requirement (Cata wfG alg) = pd + sd*2 + alg + ps ≥ ps = 2
-- Proof: n ≤ m + n for any m
private
  ir-req-geq-ps : ∀ {G E A} (wfG : WellFormedFI G) (alg : IR (E * ⟦ G ⟧TI A) A) →
    pair-slots ≤ ir-stack-requirement (Cata wfG alg)
  ir-req-geq-ps wfG alg = m≤n+m pair-slots (product-depth wfG +ℕ sum-depth wfG *ℕ 2 +ℕ ir-stack-requirement alg)

-- Core lemma: layer-capacity wfF wfG alg ≤ ir-stack-requirement (Cata wfG alg)
-- for any sub-functor wfF of wfG
layer-cap-bound : ∀ {F G E A}
  (wfF : WellFormedFI F) (wfG : WellFormedFI G) (alg : IR (E * ⟦ G ⟧TI A) A) →
  layer-capacity wfF wfG alg ≤ ir-stack-requirement (Cata wfG alg)
-- K case: alg + ps ≤ pd + sd*2 + alg + ps
-- Proof: m≤n+m gives alg+ps ≤ (pd+sd*2) + (alg+ps)
--        sym(+-assoc) gives (pd+sd*2) + (alg+ps) = ((pd+sd*2) + alg) + ps = ir-req
layer-cap-bound (wf-K _) wfG alg =
  let pd = product-depth wfG
      sd2 = sum-depth wfG *ℕ 2
      algReq = ir-stack-requirement alg
      ps = pair-slots
      -- alg + ps ≤ (pd + sd2) + (alg + ps)
      step1 : algReq +ℕ ps ≤ (pd +ℕ sd2) +ℕ (algReq +ℕ ps)
      step1 = m≤n+m (algReq +ℕ ps) (pd +ℕ sd2)
      -- (pd + sd2) + (alg + ps) = ((pd + sd2) + alg) + ps
      assoc-eq : (pd +ℕ sd2) +ℕ (algReq +ℕ ps) ≡ ((pd +ℕ sd2) +ℕ algReq) +ℕ ps
      assoc-eq = sym (+-assoc (pd +ℕ sd2) algReq ps)
  in subst (algReq +ℕ ps ≤_) assoc-eq step1
-- Id case: layer-capacity = ir-stack-requirement by definition
layer-cap-bound wf-Id wfG alg = ≤-refl
-- Sum case: 2 + (capL ⊔ capR) ≤ ir-req
-- BLOCKED: This is false when children contain Id!
--
-- Example: wf-Sum wf-Id (wf-K Unit) with wfG containing at least one Sum
--   ir-req = pd(G) + sd(G)*2 + alg + ps
--   capL = layer-capacity wf-Id = ir-req (by definition)
--   layer-capacity = 2 + (capL ⊔ capR) = 2 + ir-req > ir-req ✗
--
-- The issue: layer-capacity for Id gives full cata capacity, but when nested
-- inside Sum, the Sum's wrapper slots (2) add more, causing overcounting.
layer-cap-bound (wf-Sum wfL wfR) wfG alg = SMP.!!
-- Prod case: 1 + (capL ⊔ capR) ≤ ir-req
-- BLOCKED: This is false when children contain Id!
--
-- Example: wf-Prod wf-Id wf-Id with wfG = wf-Prod wf-Id wf-Id
--   capL = capR = ir-stack-requirement (Cata wfG alg) = 1 + alg + ps
--   layer-capacity = 1 + (capL ⊔ capR) = 1 + (1 + alg + ps) = 2 + alg + ps
--   ir-req = product-depth wfG + 0 + alg + ps = 1 + alg + ps
--   2 + alg + ps > 1 + alg + ps  ✗
--
-- The issue: layer-capacity for Id gives full cata capacity, but when nested
-- inside Product, the Product's save-slot adds 1 more, causing overcounting.
--
-- This is a fundamental limitation: runtime recursion depth (via Id) can exceed
-- the structural depth (product-depth) tracked by ir-stack-requirement.
--
-- The proof would require either:
-- 1. Changing layer-capacity wf-Id to not include full ir-req, or
-- 2. Tracking "remaining capacity" instead of "required capacity", or
-- 3. A more sophisticated capacity model that accounts for data depth
layer-cap-bound (wf-Prod wfL wfR) wfG alg = SMP.!!

-- Main conversion lemma
ir-stack-req-geq-layer-cap : ∀ {G E A}
  (wfG : WellFormedFI G)
  (alg : IR (E * ⟦ G ⟧TI A) A)
  (slot cap : ℕ) →
  slot +ℕ ir-stack-requirement (Cata wfG alg) ≤ cap →
  slot +ℕ layer-capacity wfG wfG alg ≤ cap
ir-stack-req-geq-layer-cap wfG alg slot cap pf =
  ≤-trans (+-monoʳ-≤ slot (layer-cap-bound wfG wfG alg)) pf