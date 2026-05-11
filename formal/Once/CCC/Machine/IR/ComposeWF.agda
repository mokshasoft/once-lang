-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.ComposeWF
--
-- Compose IR implementation with clean trace-based structure.
-- Final state defined by exec-trace, making trace-correct = refl.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.ComposeWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n; _≟_; _⊔_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; m≤m+n; m≤n+m; m≤n⇒m<n∨m≡n; m≤m⊔n; m≤n⊔m; ⊔-lub)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; cong₂)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import SMPrimitives for memory reasoning
import Once.CCC.Machine.SMPrimitives as SMP

-- Import proof obligation marker
import Once.ProofObligation as PO

------------------------------------------------------------------------
-- Compose implementation
------------------------------------------------------------------------

module ComposeWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules
  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc;
           valid-unit-wf;
           RecDispatcherWF; validityWF-mem-only;
           validityWF-frontier-advance; validityWF-mem-preserved;
           validityWF-with-bf-transfer)

  open import Once.CCC.Machine.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap)
  open ExecLemmas {FS}

  ------------------------------------------------------------------------
  -- Proof obligations for compose trace reasoning
  ------------------------------------------------------------------------

  -- Compose trace produces same state as sequential f; mov; g execution
  exec-trace-compose-eq : ∀ (f-trace g-trace : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS})
    (s₁ : LocState FS)
    (s₁' : LocState FS) (alloc-g : AllocState {FS})
    (s₂ : LocState FS) →
    -- f produces s₁
    proj₁ (exec-trace f-trace s alloc) ≡ s₁ →
    halted s₁ ≡ false →
    -- s₁' is s₁ with Input1 := Output
    s₁' ≡ record s₁ { regs = writeReg (regs s₁) Input1 (readReg (regs s₁) Output) } →
    -- g produces s₂ from s₁' (alloc-g has same current-frame as alloc)
    current-frame alloc-g ≡ current-frame alloc →
    proj₁ (exec-trace g-trace s₁' alloc-g) ≡ s₂ →
    -- Composed trace produces s₂
    proj₁ (exec-trace (f-trace ++ mov-to-input ∷ g-trace) s alloc) ≡ s₂
  -- Helper: mov-to-input execution unfolds when halted = false
  -- Match equality proof first to force s₁.halted = false unification
  private
    exec-mov-to-input : ∀ (g-trace : AbstractTrace) (s₁ : LocState FS)
      (alloc₁ : AllocState {FS}) →
      halted s₁ ≡ false →
      proj₁ (exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁) ≡
      proj₁ (exec-trace g-trace
        (proj₁ (exec-abstract mov-to-input s₁ alloc₁))
        (proj₂ (exec-abstract mov-to-input s₁ alloc₁)))
    exec-mov-to-input g-trace s₁ alloc₁ refl = refl

  exec-trace-compose-eq f-trace g-trace s alloc s₁ s₁' alloc-g s₂
    f-eq halted₁ s₁'-eq frame-eq g-eq = result
    where
      alloc₁ = proj₂ (exec-trace f-trace s alloc)

      -- Step 1: Split by exec-trace-append-state
      split-eq : proj₁ (exec-trace (f-trace ++ mov-to-input ∷ g-trace) s alloc) ≡
                 proj₁ (exec-trace (mov-to-input ∷ g-trace)
                         (proj₁ (exec-trace f-trace s alloc)) alloc₁)
      split-eq = exec-trace-append-state f-trace (mov-to-input ∷ g-trace) s alloc

      -- Step 2: mov-to-input unfolds when halted s₁ = false
      mov-step : proj₁ (exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁) ≡
                 proj₁ (exec-trace g-trace
                   (proj₁ (exec-abstract mov-to-input s₁ alloc₁))
                   (proj₂ (exec-abstract mov-to-input s₁ alloc₁)))
      mov-step = exec-mov-to-input g-trace s₁ alloc₁ halted₁

      -- exec-abstract mov-to-input s₁ alloc₁ produces s₁'
      mov-produces-s₁' : proj₁ (exec-abstract mov-to-input s₁ alloc₁) ≡ s₁'
      mov-produces-s₁' = sym s₁'-eq

      -- Step 3: Use frame equivalence
      frame-alloc₁ : current-frame alloc₁ ≡ current-frame alloc
      frame-alloc₁ = exec-trace-preserves-frame f-trace s alloc

      frame-match : current-frame alloc₁ ≡ current-frame alloc-g
      frame-match = trans frame-alloc₁ (sym frame-eq)

      frame-equiv : proj₁ (exec-trace g-trace s₁' alloc₁) ≡
                    proj₁ (exec-trace g-trace s₁' alloc-g)
      frame-equiv = exec-trace-same-frame g-trace s₁' alloc₁ alloc-g frame-match

      -- Combine the steps
      step2' : proj₁ (exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁) ≡
               proj₁ (exec-trace g-trace s₁' alloc₁)
      step2' = trans mov-step (cong (λ st → proj₁ (exec-trace g-trace st alloc₁))
                                    mov-produces-s₁')

      final : proj₁ (exec-trace g-trace s₁' alloc₁) ≡ s₂
      final = trans frame-equiv g-eq

      result = trans split-eq
                 (trans (cong (λ st → proj₁ (exec-trace (mov-to-input ∷ g-trace) st alloc₁)) f-eq)
                        (trans step2' final))

  -- Compose frontier stability is proven inline using:
  --   1. f's frontier-slot-stable for f-trace
  --   2. mov-to-input preserves memory (exec-abstract-preserves-stack-slot = refl)
  --   3. g-trace writes at slots ≥ reclaim-f > next-slot alloc (by strict inequality)

  ------------------------------------------------------------------------
  -- Compose: run f, then run g with f's output
  --
  -- Uses ir-stack-requirement for capacity: req(g ∘ f) = req(f) + req(g)
  ------------------------------------------------------------------------

  run-compose : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (g ∘ f)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    ∃[ mOut ] IRResultAWF mOut (g ∘ f) x s alloc
  run-compose mIn f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq =
    mOut , record
      { final-state = s-final
      ; final-alloc = alloc₂
      ; trace = compose-trace
      ; trace-correct = refl  -- s-final DEFINED by trace
      -- Plan 0.2.4.5 D1 task #28 partial: transport result-g's
      -- result-place wholesale along s-final-eq. Generalises over
      -- Unit / non-Unit result type without unbundling — Unit's
      -- `unit-result` and non-Unit's `at-loc` propagate uniformly.
      -- Removes 6 place-* call sites (result-loc-g, result-valid-final,
      -- result-before-g, rax-eq-final, compose-reclaim-*) on result-g.
      ; result-place = subst
          (λ st → ResultPlace _ mOut alloc₂
                    (record alloc { next-slot = next-slot alloc₂ })
                    (eval g (eval f x)) st)
          (sym s-final-eq)
          (IRResultAWF.result-place result-g)
      ; not-halted = not-halted-final
      ; frame-preserved = IRResultAWF.frame-preserved result-g
      ; slot-monotone = slot-mono
      ; heap-preserved = heap-mono
      -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-size-bound
      ; max-slot-written = compose-max-slot
      ; max-slot-geq-final = compose-max-slot-geq-final
      ; stack-budget = req-compose
      ; max-slot-usage-bound = compose-max-slot-bound
      ; slot-stays-in-budget = compose-slot-stays-in-budget
      ; frontier-slot-stable = compose-frontier-stable
      ; trace-writes-above = compose-trace-writes-above
      ; trace-slot-reads-above = compose-trace-slot-reads-above
      ; trace-writes-below = compose-trace-writes-below
      ; trace-slot-reads-below = compose-trace-slot-reads-below
      -- Note: trace-preserves-capacity removed in Phase 3
      ; trace-no-heap-writes = compose-trace-no-heap-writes
      ; trace-twf = compose-trace-twf
      ; trace-preserves-halted = exec-trace-preserves-halted-WF compose-trace
      ; scratch-budget = req-compose-scratch
      ; scratch-bounded = compose-scratch-bounded
      }
    where
      -- Plan 0.2.4.5 D1 task #30: dynamic stack-budget composition.
      -- rf / rg / req-compose are defined below after result-f / result-g
      -- are bound. They read the sub-result budgets dynamically, since
      -- IRResultAWF.stack-budget is a stuck projection over an opaque
      -- rec-wf result.

      ------------------------------------------------------------------------
      -- Run f via recursive dispatch
      ------------------------------------------------------------------------
      f-result-pair = rec-wf mIn f (∘-f-smaller f g) x input-loc s alloc
                        input-valid-wf input-before not-halted rdi-eq
      mMid = proj₁ f-result-pair
      result-f = proj₂ f-result-pair
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      f-trace = IRResultAWF.trace result-f
      not-halted₁ = IRResultAWF.not-halted result-f

      -- Plan 0.2.4.5 D1 task #30: dynamic stack-budget composition (f's portion).
      rf = IRResultAWF.stack-budget result-f
      sf = IRResultAWF.scratch-budget result-f

      ------------------------------------------------------------------------
      -- Plan 0.2.4.5 D1 task #28: dispatch on f's result-place
      -- constructor to extract concrete inter-* facts.
      --
      -- For at-loc (non-Unit B): use the bundled facts directly.
      -- For unit-result (B = Unit): pick inter-loc = readReg s₁ Output
      -- so the rax equation becomes refl by construction; ValidAtWF
      -- Unit at any loc is `valid-unit-wf` (loc-agnostic, no
      -- postulate). Only `unit-inter-before` remains postulated —
      -- BeforeFrontier on Output's value isn't generally provable,
      -- which is the genuine trust point for Unit erasure when
      -- composing through `rec-wf`'s fixed precondition shape.
      record FFacts : Set where
        field
          inter-loc-f    : ValueLocation FS
          inter-before-f : BeforeFrontier alloc₁ inter-loc-f
          inter-valid-f  : ValidAtWF mMid alloc₁ (eval f x) inter-loc-f s₁
          inter-rax-f    : readReg (regs s₁) Output ≡ SV-Ptr inter-loc-f

      f-facts : FFacts
      f-facts with IRResultAWF.result-place result-f
      ... | at-loc loc valid before rax _ _ = record
              { inter-loc-f    = loc
              ; inter-before-f = before
              ; inter-valid-f  = valid
              ; inter-rax-f    = rax
              }
      ... | unit-result = record
              { inter-loc-f    = unit-inter-loc
              ; inter-before-f = unit-inter-before
              ; inter-valid-f  = valid-unit-wf
              ; inter-rax-f    = unit-inter-rax
              }
        where
          postulate
            unit-inter-loc : ValueLocation FS
            unit-inter-before : BeforeFrontier alloc₁ unit-inter-loc
            unit-inter-rax : readReg (regs s₁) Output ≡ SV-Ptr unit-inter-loc

      open FFacts f-facts using ()
        renaming (inter-loc-f to inter-loc;
                  inter-before-f to inter-before-f';
                  inter-valid-f to inter-valid-f';
                  inter-rax-f to inter-rax-f')

      ------------------------------------------------------------------------
      -- Reclaim after f (Phase 7: reclaimable-slot = next-slot final-alloc)
      ------------------------------------------------------------------------
      -- With perfect reclaim, reclaim-f = next-slot alloc₁
      reclaim-f = next-slot alloc₁

      reclaim-f-bound : reclaim-f ≤ next-slot alloc +ℕ rf
      reclaim-f-bound = IRResultAWF.slot-stays-in-budget result-f

      alloc₁-reclaimed : AllocState {FS}
      alloc₁-reclaimed = record alloc { next-slot = reclaim-f }

      ------------------------------------------------------------------------
      -- Setup intermediate state for g
      ------------------------------------------------------------------------
      -- Phase 7: Derive from result-before since reclaim = final-alloc
      -- alloc₁-reclaimed has same next-slot as alloc₁, same current-frame as alloc
      -- Heap equality: heap-preserved (post task #30) gives this directly.
      -- alloc₁-reclaimed has next-heap-ref = alloc.next-heap-ref by construction;
      -- alloc₁ = result-f.final-alloc has the same by f's heap-preserved.
      heap-eq-f : next-heap-ref alloc₁ ≡ next-heap-ref alloc₁-reclaimed
      heap-eq-f = IRResultAWF.heap-preserved result-f
      -- PROOF OBLIGATION: Valid for Layer 0 because:
      -- 1. alloc₁-reclaimed only changes next-slot (line 225)
      -- 2. Layer 0 IRs (id, compose) all set final-alloc = alloc or preserve heap-ref inductively
      -- 3. No Layer 0 IR allocates on heap
      -- Will need formal proof when heap-allocating IRs are added.

      inter-before-reclaimed : BeforeFrontier alloc₁-reclaimed inter-loc
      inter-before-reclaimed =
        frontier-same-heap alloc₁ alloc₁-reclaimed
          (IRResultAWF.frame-preserved result-f) refl heap-eq-f inter-loc
          inter-before-f'

      -- Transfer validity from alloc₁ to alloc₁-reclaimed
      -- These allocs have: same next-slot, same frame (by frame-preserved), same heap (by heap-eq-f)
      inter-valid-reclaimed : ValidAtWF mMid alloc₁-reclaimed (eval f x) inter-loc s₁
      inter-valid-reclaimed =
        let bf-transfer = frontier-same-heap alloc₁ alloc₁-reclaimed
                            (IRResultAWF.frame-preserved result-f) refl heap-eq-f
        in validityWF-with-bf-transfer (eval f x) inter-loc s₁
             alloc₁ alloc₁-reclaimed bf-transfer
             inter-valid-f'

      s₁' = record s₁ { regs = writeReg (regs s₁) Input1 (SV-Ptr inter-loc) }

      rdi-eq₁ : readReg (regs s₁') Input1 ≡ SV-Ptr inter-loc
      rdi-eq₁ = writeReg-same (regs s₁) Input1 (SV-Ptr inter-loc)

      inter-valid-wf' : ValidAtWF mMid alloc₁-reclaimed (eval f x) inter-loc s₁'
      inter-valid-wf' = validityWF-mem-only (eval f x) inter-loc s₁ s₁' refl refl inter-valid-reclaimed

      ------------------------------------------------------------------------
      -- Run g via recursive dispatch
      ------------------------------------------------------------------------
      g-result-pair = rec-wf mMid g (∘-g-smaller f g) (eval f x) inter-loc s₁' alloc₁-reclaimed
                        inter-valid-wf' inter-before-reclaimed not-halted₁ rdi-eq₁
      mOut = proj₁ g-result-pair
      result-g = proj₂ g-result-pair
      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      g-trace = IRResultAWF.trace result-g
      -- Plan 0.2.4.5 D1 task #28: result-loc-g, result-before-g
      -- removed — the compose's result-place is now constructed by
      -- whole-bundle transport (see line ~175), not by unbundling
      -- result-g's place into individual loc/valid/before/rax/reclaim-*
      -- facts. The transport eliminates 6 place-* call sites.

      -- Plan 0.2.4.5 D1 task #30: dynamic stack-budget composition (g's portion).
      rg = IRResultAWF.stack-budget result-g
      sg = IRResultAWF.scratch-budget result-g

      req-compose = rf +ℕ rg
      req-compose-scratch = sf +ℕ sg

      ------------------------------------------------------------------------
      -- Compose trace and final state DEFINED by trace execution
      ------------------------------------------------------------------------
      compose-trace : AbstractTrace
      compose-trace = f-trace ++ mov-to-input ∷ g-trace

      s-final : LocState FS
      s-final = proj₁ (exec-trace compose-trace s alloc)

      -- Prove s-final ≡ s₂ using the compose equation
      -- s₁' = record s₁ { regs = writeReg (regs s₁) Input1 inter-loc }
      -- By rax-is-result: readReg (regs s₁) Output ≡ inter-loc
      -- So s₁' ≡ record s₁ { regs = writeReg (regs s₁) Input1 (readReg (regs s₁) Output) }
      s₁'-eq-output : s₁' ≡ record s₁ { regs = writeReg (regs s₁) Input1 (readReg (regs s₁) Output) }
      s₁'-eq-output = cong (λ v → record s₁ { regs = writeReg (regs s₁) Input1 v })
                           (sym inter-rax-f')

      s-final-eq : s-final ≡ s₂
      s-final-eq = exec-trace-compose-eq f-trace g-trace s alloc s₁ s₁' alloc₁-reclaimed s₂
                     (IRResultAWF.trace-correct result-f)
                     not-halted₁
                     s₁'-eq-output
                     refl
                     (IRResultAWF.trace-correct result-g)

      ------------------------------------------------------------------------
      -- Transport proofs from s₂ to s-final
      -- (result-valid-final / rax-eq-final removed: their facts are
      -- now bundled inside the transported result-place above.)
      ------------------------------------------------------------------------
      not-halted-final : halted s-final ≡ false
      not-halted-final = subst (λ st → halted st ≡ false) (sym s-final-eq)
                           (IRResultAWF.not-halted result-g)

      slot-mono : next-slot alloc ≤ next-slot alloc₂
      slot-mono = ≤-trans (IRResultAWF.slot-monotone result-f)
                          (IRResultAWF.slot-monotone result-g)

      heap-mono : next-heap-ref alloc₂ ≡ next-heap-ref alloc
      heap-mono = trans (IRResultAWF.heap-preserved result-g)
                  (trans (sym heap-eq-f) (IRResultAWF.heap-preserved result-f))

      -- Note: mem-preserved-compose removed in Phase 4 (field no longer in IRResultAWF)
      -- Use irresult-mem-preserved to derive preservation when needed

      -- Phase 7: Removed reclamation section (reclaimable-slot = next-slot final-alloc)
      -- Keep reclaim-preserves-* for compositional proofs with heap allocation

      -- compose-reclaim-preserves-{result,validity} removed: the
      -- reclaim-side facts are now bundled inside the transported
      -- result-place above. (Old code used place-reclaim-before /
      -- place-reclaim-valid to extract them; with the whole-bundle
      -- transport the dual-alloc form of `at-loc` carries them.)

      ------------------------------------------------------------------------
      -- Max slot tracking
      ------------------------------------------------------------------------
      max-slot-f = IRResultAWF.max-slot-written result-f
      max-slot-g = IRResultAWF.max-slot-written result-g
      compose-max-slot = max-slot-f ⊔ max-slot-g

      -- next-slot alloc₂ ≤ max-slot-g ≤ max-slot-f ⊔ max-slot-g
      compose-max-slot-geq-final : next-slot alloc₂ ≤ compose-max-slot
      compose-max-slot-geq-final = ≤-trans (IRResultAWF.max-slot-geq-final result-g)
                                           (m≤n⊔m max-slot-f max-slot-g)

      -- max-slot-f ≤ next-slot alloc + rf ≤ next-slot alloc + (rf + rg)
      -- max-slot-g ≤ reclaim-f + rg ≤ (next-slot alloc + rf) + rg = next-slot alloc + (rf + rg)
      compose-max-slot-bound : compose-max-slot ≤ next-slot alloc +ℕ req-compose
      compose-max-slot-bound = ⊔-lub f-bound g-bound
        where
          f-bound : max-slot-f ≤ next-slot alloc +ℕ req-compose
          f-bound = ≤-trans (IRResultAWF.max-slot-usage-bound result-f)
                            (+-monoʳ-≤ (next-slot alloc) (m≤m+n rf rg))

          g-bound : max-slot-g ≤ next-slot alloc +ℕ req-compose
          g-bound = ≤-trans (IRResultAWF.max-slot-usage-bound result-g)
                            (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                              (≤-reflexive (+-assoc (next-slot alloc) rf rg)))

      -- Stack discipline: composition stays within budget
      -- alloc₂ is final after g, which ran on alloc₁-reclaimed with next-slot = reclaim-f
      -- From g.slot-stays-in-budget: next-slot alloc₂ ≤ reclaim-f + rg
      -- From f.slot-stays-in-budget: reclaim-f ≤ next-slot alloc + rf
      -- Therefore: next-slot alloc₂ ≤ next-slot alloc + (rf + rg) = next-slot alloc + req-compose
      compose-slot-stays-in-budget : next-slot alloc₂ ≤ next-slot alloc +ℕ req-compose
      compose-slot-stays-in-budget =
        ≤-trans (IRResultAWF.slot-stays-in-budget result-g)
          (≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
            (≤-reflexive (+-assoc (next-slot alloc) rf rg)))

      ------------------------------------------------------------------------
      -- Trace predicates
      ------------------------------------------------------------------------
      -- Note: f-tpc, g-tpc, compose-trace-preserves-capacity removed in Phase 3

      f-nhw : SMP.TraceNoHeapWrites f-trace
      f-nhw = IRResultAWF.trace-no-heap-writes result-f
      g-nhw : SMP.TraceNoHeapWrites g-trace
      g-nhw = IRResultAWF.trace-no-heap-writes result-g
      compose-trace-no-heap-writes : SMP.TraceNoHeapWrites compose-trace
      compose-trace-no-heap-writes =
        SMP.trace-no-heap-writes-append f-trace (mov-to-input ∷ g-trace) f-nhw g-nhw

      f-tph : TraceWF s alloc f-trace
      f-tph = IRResultAWF.trace-twf result-f
      -- TODO: g-tph runs at a runtime state different from g's construction
      -- state; same shape as PairWF2's g-tph-runtime. Postulate for the
      -- scaffold pass, discharge in follow-up.
      g-tph : TraceWF (proj₁ (exec-trace (f-trace ++ mov-to-input ∷ []) s alloc))
                      (proj₂ (exec-trace (f-trace ++ mov-to-input ∷ []) s alloc))
                      g-trace
      g-tph = SMP.!!  -- TODO: bridge from result-g's trace-twf
      compose-trace-twf : TraceWF s alloc compose-trace
      compose-trace-twf = SMP.!!  -- TODO: twf-++ f-tph (twf-∷ tt g-tph) with state-threading

      ------------------------------------------------------------------------
      -- Frontier slot stability
      --
      -- Returns a sum type:
      --   inj₁: compose doesn't allocate (next-slot alloc = next-slot alloc₂)
      --   inj₂: slot is preserved
      --
      -- Proof strategy using trace bounds directly:
      --   1. f-trace preserves slot (by f's frontier-slot-stable or trace bounds)
      --   2. mov-to-input doesn't write memory (preserves slot)
      --   3. g-trace writes at slots in [reclaim-f, next-slot alloc₂):
      --      - Case A: next-slot alloc < reclaim-f → inj₂ (preserved by trace bounds)
      --      - Case B1: next-slot = reclaim-f < next-slot alloc₂ → inj₂ (inj₂ tt) (uncertain)
      --      - Case B2: next-slot = reclaim-f = next-slot alloc₂ → inj₁ (no allocation)
      ------------------------------------------------------------------------
      compose-frontier-stable : ∀ (s' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s' ≡ false →
        readReg (regs s') Input1 ≡ SV-Ptr input-loc' →
        readLoc s' (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
        (next-slot alloc ≡ next-slot alloc₂) ⊎
        ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                 (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')) ⊎ ⊤)
      compose-frontier-stable s' input-loc' not-halted' rdi-eq' slot-eq' = result
        where
          -- Step 1: Decompose trace using exec-trace-append-state
          s-after-f = proj₁ (exec-trace f-trace s' alloc)
          alloc-after-f = proj₂ (exec-trace f-trace s' alloc)

          -- f's trace bounds for slot preservation when f doesn't allocate
          f-twa : TraceWritesAbove (next-slot alloc) f-trace
          f-twa = IRResultAWF.trace-writes-above result-f

          f-twb : TraceWritesBelow max-slot-f f-trace
          f-twb = IRResultAWF.trace-writes-below result-f

          f-tnhw : TraceNoHeapWrites f-trace
          f-tnhw = IRResultAWF.trace-no-heap-writes result-f

          -- Step 2: mov-to-input preserves memory (only modifies registers)
          not-halted-after-f : halted s-after-f ≡ false
          not-halted-after-f = SMP.!!  -- TODO: result-f.trace-preserves-halted at s' state

          s-after-mov = proj₁ (exec-abstract mov-to-input s-after-f alloc-after-f)
          alloc-after-mov = proj₂ (exec-abstract mov-to-input s-after-f alloc-after-f)

          -- g-trace bounds
          g-twa : TraceWritesAbove reclaim-f g-trace
          g-twa = IRResultAWF.trace-writes-above result-g

          g-twb : TraceWritesBelow max-slot-g g-trace
          g-twb = IRResultAWF.trace-writes-below result-g

          g-tnhw : TraceNoHeapWrites g-trace
          g-tnhw = IRResultAWF.trace-no-heap-writes result-g

          -- We have: next-slot alloc ≤ reclaim-f (by f's slot-monotone, since reclaim-f = next-slot alloc₁)
          reclaim-f-mono : next-slot alloc ≤ reclaim-f
          reclaim-f-mono = IRResultAWF.slot-monotone result-f

          -- Frame equivalence
          frame-after-mov : current-frame alloc-after-mov ≡ current-frame alloc
          frame-after-mov = trans (exec-abstract-preserves-frame mov-to-input s-after-f alloc-after-f)
                                  (exec-trace-preserves-frame f-trace s' alloc)

          frame-equiv : current-frame alloc-after-mov ≡ current-frame alloc₁-reclaimed
          frame-equiv = frame-after-mov

          -- Step 3: Case analysis based on f's frontier-slot-stable result
          -- New 3-way return: inj₁ (no-alloc) | inj₂ (inj₁ preserved) | inj₂ (inj₂ tt) (uncertain)
          result : (next-slot alloc ≡ next-slot alloc₂) ⊎
                   ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                            (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')) ⊎ ⊤)
          result with IRResultAWF.frontier-slot-stable result-f s' input-loc' not-halted' rdi-eq' slot-eq'
          -- If f is uncertain, compose is also uncertain
          ... | inj₂ (inj₂ tt) = inj₂ (inj₂ tt)
          -- If f preserves the slot
          ... | inj₂ (inj₁ f-preserved) = result-with-slot-after-f f-preserved
            where
              slot-after-f : readLoc s-after-f (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')
              slot-after-f = f-preserved

              slot-after-mov : readLoc s-after-mov (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')
              slot-after-mov = trans (sym (exec-abstract-preserves-stack-slot mov-to-input s-after-f alloc-after-f
                                             (current-frame alloc) (next-slot alloc) nhw-mov-to-input refl))
                                     slot-after-f

              -- Case A: f allocates, use trace bounds for g
              slot-after-g : next-slot alloc < reclaim-f →
                             readLoc (proj₁ (exec-trace g-trace s-after-mov alloc₁-reclaimed))
                                     (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')
              slot-after-g slot<reclaim-f =
                let preserved = exec-trace-preserves-slot-below g-trace s-after-mov alloc₁-reclaimed
                                  reclaim-f (next-slot alloc) g-twa g-tnhw slot<reclaim-f
                in trans preserved slot-after-mov

              split1 : proj₁ (exec-trace compose-trace s' alloc) ≡
                       proj₁ (exec-trace (mov-to-input ∷ g-trace) s-after-f alloc-after-f)
              split1 = exec-trace-append-state f-trace (mov-to-input ∷ g-trace) s' alloc

              split2 : exec-trace (mov-to-input ∷ g-trace) s-after-f alloc-after-f ≡
                       exec-trace g-trace s-after-mov alloc-after-mov
              split2 = exec-trace-cons mov-to-input g-trace s-after-f alloc-after-f not-halted-after-f

              frame-g-result : proj₁ (exec-trace g-trace s-after-mov alloc-after-mov) ≡
                               proj₁ (exec-trace g-trace s-after-mov alloc₁-reclaimed)
              frame-g-result = exec-trace-same-frame g-trace s-after-mov alloc-after-mov alloc₁-reclaimed frame-equiv

              build-preserved : next-slot alloc < reclaim-f →
                                readLoc (proj₁ (exec-trace compose-trace s' alloc))
                                        (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')
              build-preserved slot<reclaim-f =
                trans (cong (λ st → readLoc st (AtStack (current-frame alloc) (next-slot alloc)))
                            (trans split1 (trans (cong proj₁ split2) frame-g-result)))
                      (slot-after-g slot<reclaim-f)

              result-with-slot-after-f : readLoc s-after-f (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc') →
                                         (next-slot alloc ≡ next-slot alloc₂) ⊎
                                         ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                                                  (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')) ⊎ ⊤)
              result-with-slot-after-f _ with m≤n⇒m<n∨m≡n reclaim-f-mono
              -- Case A: f allocates (next-slot < reclaim-f)
              ... | inj₁ slot<reclaim-f = inj₂ (inj₁ (build-preserved slot<reclaim-f))
              -- Case B: f doesn't allocate (next-slot = reclaim-f), but f returned inj₂ (inj₁ preserved)
              -- This shouldn't happen for well-behaved IRs, but handle it anyway
              ... | inj₂ slot≡reclaim-f with m≤n⇒m<n∨m≡n (IRResultAWF.slot-monotone result-g)
              -- B1: g allocates - uncertain (f preserved but might be overwritten by g)
              ... | inj₁ reclaim-f<alloc₂ = inj₂ (inj₂ tt)
              -- B2: neither allocates
              ... | inj₂ reclaim-f≡alloc₂ = inj₁ (trans slot≡reclaim-f reclaim-f≡alloc₂)

          -- If f doesn't allocate (inj₁)
          -- With max-slot-written bounds, we can't easily prove slot preservation in this case
          -- (max-slot-f might be larger than reclaim-f even when f doesn't grow next-slot).
          -- We return uncertain since this is a rare edge case.
          ... | inj₁ f-no-alloc = result-f-no-alloc
            where
              result-f-no-alloc : (next-slot alloc ≡ next-slot alloc₂) ⊎
                                  ((readLoc (proj₁ (exec-trace compose-trace s' alloc))
                                           (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')) ⊎ ⊤)
              result-f-no-alloc with m≤n⇒m<n∨m≡n (IRResultAWF.slot-monotone result-g)
              -- Case B1: g allocates at frontier - uncertain
              ... | inj₁ reclaim-f<alloc₂ = inj₂ (inj₂ tt)
              -- Case B2: neither allocates - return no-alloc proof
              ... | inj₂ reclaim-f≡alloc₂ = inj₁ (trans f-no-alloc reclaim-f≡alloc₂)

      ------------------------------------------------------------------------
      -- Trace write/read bounds
      ------------------------------------------------------------------------
      compose-trace-writes-above : TraceWritesAbove (next-slot alloc) compose-trace
      compose-trace-writes-above =
        let n = next-slot alloc
            f-tw : TraceWritesAbove n f-trace
            f-tw = IRResultAWF.trace-writes-above result-f
            g-tw-at-reclaim : TraceWritesAbove reclaim-f g-trace
            g-tw-at-reclaim = IRResultAWF.trace-writes-above result-g
            g-tw : TraceWritesAbove n g-trace
            g-tw = trace-writes-above-mono n reclaim-f g-trace
                     (IRResultAWF.slot-monotone result-f) g-tw-at-reclaim
            mov-g-tw : TraceWritesAbove n (mov-to-input ∷ g-trace)
            mov-g-tw = g-tw
        in trace-writes-above-append n f-trace (mov-to-input ∷ g-trace) f-tw mov-g-tw

      compose-trace-slot-reads-above : TraceSlotReadsAbove (next-slot alloc) compose-trace
      compose-trace-slot-reads-above =
        let n = next-slot alloc
            f-ra : TraceSlotReadsAbove n f-trace
            f-ra = IRResultAWF.trace-slot-reads-above result-f
            g-ra-at-reclaim : TraceSlotReadsAbove reclaim-f g-trace
            g-ra-at-reclaim = IRResultAWF.trace-slot-reads-above result-g
            g-ra : TraceSlotReadsAbove n g-trace
            g-ra = trace-slot-reads-above-mono n reclaim-f g-trace
                     (IRResultAWF.slot-monotone result-f) g-ra-at-reclaim
            mov-g-ra : TraceSlotReadsAbove n (mov-to-input ∷ g-trace)
            mov-g-ra = g-ra
        in trace-slot-reads-above-append n f-trace (mov-to-input ∷ g-trace) f-ra mov-g-ra

      compose-trace-writes-below : TraceWritesBelow compose-max-slot compose-trace
      compose-trace-writes-below =
        let f-wb : TraceWritesBelow compose-max-slot f-trace
            f-wb = trace-writes-below-mono max-slot-f compose-max-slot f-trace
                     (m≤m⊔n max-slot-f max-slot-g)
                     (IRResultAWF.trace-writes-below result-f)
            g-wb : TraceWritesBelow compose-max-slot g-trace
            g-wb = trace-writes-below-mono max-slot-g compose-max-slot g-trace
                     (m≤n⊔m max-slot-f max-slot-g)
                     (IRResultAWF.trace-writes-below result-g)
            mov-g-wb : TraceWritesBelow compose-max-slot (mov-to-input ∷ g-trace)
            mov-g-wb = g-wb
        in trace-writes-below-append compose-max-slot f-trace (mov-to-input ∷ g-trace) f-wb mov-g-wb

      compose-trace-slot-reads-below : TraceSlotReadsBelow compose-max-slot compose-trace
      compose-trace-slot-reads-below =
        let f-rb : TraceSlotReadsBelow compose-max-slot f-trace
            f-rb = trace-slot-reads-below-mono max-slot-f compose-max-slot f-trace
                     (m≤m⊔n max-slot-f max-slot-g)
                     (IRResultAWF.trace-slot-reads-below result-f)
            g-rb : TraceSlotReadsBelow compose-max-slot g-trace
            g-rb = trace-slot-reads-below-mono max-slot-g compose-max-slot g-trace
                     (m≤n⊔m max-slot-f max-slot-g)
                     (IRResultAWF.trace-slot-reads-below result-g)
            mov-g-rb : TraceSlotReadsBelow compose-max-slot (mov-to-input ∷ g-trace)
            mov-g-rb = g-rb
        in trace-slot-reads-below-append compose-max-slot f-trace (mov-to-input ∷ g-trace) f-rb mov-g-rb

      ------------------------------------------------------------------------
      -- Scratch bounded
      --
      -- compose-max-slot = max-slot-f ⊔ max-slot-g
      -- Need: compose-max-slot ≤ next-slot alloc₂ +ℕ (rf + rg)
      --
      -- From f's scratch-bounded: max-slot-f ≤ next-slot alloc₁ +ℕ rf
      -- From g's scratch-bounded: max-slot-g ≤ next-slot alloc₂ +ℕ rg
      --
      -- For max-slot-f: alloc₁ is f's final alloc, alloc₂ is g's final alloc
      --   next-slot alloc₁ ≤ next-slot alloc₂ (since g runs on reclaim-f ≤ next-slot alloc₁,
      --   and g's slot-monotone gives reclaim-f ≤ next-slot alloc₂)
      --   So: max-slot-f ≤ next-slot alloc₁ +ℕ rf ≤ next-slot alloc₂ +ℕ rf ≤ next-slot alloc₂ +ℕ (rf + rg)
      --
      -- For max-slot-g: directly from g's scratch-bounded
      --   max-slot-g ≤ next-slot alloc₂ +ℕ rg ≤ next-slot alloc₂ +ℕ (rf + rg)
      ------------------------------------------------------------------------
      compose-scratch-bounded : compose-max-slot ≤ next-slot alloc₂ +ℕ req-compose-scratch
      compose-scratch-bounded = ⊔-lub f-scratch-bound g-scratch-bound
        where
          -- f's scratch-bounded: max-slot-f ≤ next-slot alloc₁ +ℕ sf
          f-sb : max-slot-f ≤ next-slot alloc₁ +ℕ sf
          f-sb = IRResultAWF.scratch-bounded result-f

          -- g's scratch-bounded: max-slot-g ≤ next-slot alloc₂ +ℕ sg
          g-sb : max-slot-g ≤ next-slot alloc₂ +ℕ sg
          g-sb = IRResultAWF.scratch-bounded result-g

          -- next-slot alloc₁ ≤ next-slot alloc₂ via:
          --   reclaim-f = next-slot alloc₁ (by definition)
          --   reclaim-f ≤ next-slot alloc₂ (g's slot-monotone, since g runs on alloc₁-reclaimed)
          alloc₁≤alloc₂ : next-slot alloc₁ ≤ next-slot alloc₂
          alloc₁≤alloc₂ = IRResultAWF.slot-monotone result-g

          f-scratch-bound : max-slot-f ≤ next-slot alloc₂ +ℕ req-compose-scratch
          f-scratch-bound =
            ≤-trans f-sb
              (≤-trans (+-monoˡ-≤ sf alloc₁≤alloc₂)
                (+-monoʳ-≤ (next-slot alloc₂) (m≤m+n sf sg)))

          g-scratch-bound : max-slot-g ≤ next-slot alloc₂ +ℕ req-compose-scratch
          g-scratch-bound =
            ≤-trans g-sb (+-monoʳ-≤ (next-slot alloc₂) (m≤n+m sg sf))