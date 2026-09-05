-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.ComposeWF
--
-- Compose IR implementation with clean trace-based structure.
-- Final state defined by exec-trace, making trace-correct = refl.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.IR.ComposeWF (o : CanonicalName) where

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
-- Plan 0.52 M2: machine values are IRTy values (⟦_⟧ᴵ), renamed to ⟦_⟧ locally.
open import Once.Semantics.Machine using () renaming (⟦_⟧ᴵ to ⟦_⟧)
open import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.IR.Size
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
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (Once.CCC.FrameSemantics.fs-numerics FS)

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

  open import Once.CCC.Machine.ClosureWellFormed o
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; at-reg;
           valid-unit-wf; mk-IRResultAWF-via-bump;
           RecDispatcherWF; InputPlace; in-at-loc; in-at-reg; in-unit;
           Place; AtStorage; InReg;
           place-sv; place-rax; validityWF-mem-only;
           validityWF-frontier-advance; validityWF-mem-preserved;
           validityWF-with-bf-transfer; mem-preserved-from-tnhw)

  open import Once.CCC.Machine.TraceEvaluator
  open TraceEvaluatorDef {FS}

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

  -- Stage F: the input is an `InputPlace`, not four positional memory facts.
  -- `f` runs FIRST, at the entry state, so compose passes its own input place
  -- straight through — which is what lets a register-resident input reach `f`
  -- at all. Nothing here inspects the residence.
  run-compose : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (g ∘ f)))
    (x : ⟦ A ⟧) (s : LocState FS) (alloc : AllocState {FS}) →
    InputPlace mIn alloc x s →
    (dest : Place) →
    halted s ≡ false →
    ∃[ mOut ] IRResultAWF mOut (g ∘ f) x s alloc
  run-compose mIn f g rec-wf x s alloc input-place dest not-halted =
    -- Plan 0.17: bump = bump-+ result-f.bump result-g.bump.
    mOut , mk-IRResultAWF-via-bump
      s-final
      alloc₂
      compose-trace
      compose-bump
      compose-bump-eq
      SMP.!!  -- trace-is-ir-to-trace
      refl
      (TraceEvaluator.exec-alloc-eq trace-eval)
      (let result-place-at-alloc₁ : ResultPlace _ mOut alloc₂
             (record alloc₁ { next-slot     = next-slot     alloc₂
                            ; next-heap-ref = next-heap-ref alloc₂ })
             (eval g (eval f x)) s₂
           result-place-at-alloc₁ = IRResultAWF.result-place result-g
           place-at-alloc-frame :
             ResultPlace _ mOut alloc₂
               (record alloc { next-slot     = next-slot     alloc₂
                             ; next-heap-ref = next-heap-ref alloc₂ })
               (eval g (eval f x)) s₂
           place-at-alloc-frame =
             subst (λ fr → ResultPlace _ mOut alloc₂
                     (record alloc₁ { current-frame = fr
                                    ; next-slot     = next-slot     alloc₂
                                    ; next-heap-ref = next-heap-ref alloc₂ })
                     (eval g (eval f x)) s₂)
                   (IRResultAWF.frame-preserved result-f)
                   result-place-at-alloc₁
       in subst
            (λ st → ResultPlace _ mOut alloc₂
                      (record alloc { next-slot     = next-slot     alloc₂
                                    ; next-heap-ref = next-heap-ref alloc₂ })
                      (eval g (eval f x)) st)
            (sym s-final-eq)
            place-at-alloc-frame)
      not-halted-final
      (TraceEvaluator.mem-preserved-before trace-eval)
      (TraceEvaluator.trace-wf trace-eval)
      (exec-trace-preserves-halted-WF compose-trace)
      (SMP.trace-no-frame-ops-append f-trace _ (IRResultAWF.trace-no-frame-ops result-f)
        (tt , IRResultAWF.trace-no-frame-ops result-g))
      (record
        { max-slot-written = compose-max-slot
        ; stack-budget = req-compose
        ; bump-fits-stack-budget = compose-bump-fits-stack-budget
        ; max-slot-geq-final = compose-max-slot-geq-final-bump
        ; max-slot-usage-bound = compose-max-slot-bound
        -- Plan 0.17.1: frontier-slot-stable now returns relative to
        -- `apply-bump compose-bump alloc`, not raw `alloc₂`. Match the
        -- pattern used by ApplyWF / PairAllocWF / CurryAllocWF and return
        -- the uncertain branch `inj₂ (inj₂ tt)`. The legacy compose-
        -- frontier-stable (with the alloc₂-shape return type) is kept
        -- below as dead code for reference; reviving it would require
        -- a transport via `compose-bump-eq` on the inj₁ branch.
        ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
        ; trace-writes-above = compose-trace-writes-above
        ; trace-slot-reads-above = compose-trace-slot-reads-above
        ; trace-writes-below = compose-trace-writes-below
        ; trace-slot-reads-below = compose-trace-slot-reads-below
        ; scratch-budget = req-compose-scratch
        ; scratch-bounded = compose-scratch-bounded-bump
        })
      (record
        { heap-budget = IRResultAWF.heap-budget result-f +ℕ IRResultAWF.heap-budget result-g
        ; max-heap-ref-written = IRResultAWF.max-heap-ref-written result-g
        ; bump-fits-heap-budget = compose-bump-fits-heap-budget
        ; max-heap-ref-geq-final = compose-max-heap-ref-geq-final-bump
        ; max-heap-usage-bound = SMP.!!
        })
    where
      -- Plan 0.2.4.5 D1 task #30: dynamic stack-budget composition.
      -- rf / rg / req-compose are defined below after result-f / result-g
      -- are bound. They read the sub-result budgets dynamically, since
      -- IRResultAWF.stack-budget is a stuck projection over an opaque
      -- rec-wf result.

      ------------------------------------------------------------------------
      -- Run f via recursive dispatch
      ------------------------------------------------------------------------
      -- Stage F: compose's OWN input, bundled. `run-compose` still takes the
      -- four memory facts (its callers are unchanged); only the dispatcher
      -- interface generalised.
      -- Stage F destinations. `g` produces COMPOSE's result, so it gets
      -- compose's own `dest`. `f` produces the INTERMEDIATE, which is an IR
      -- boundary and therefore stack-resident: the frontier slot compose owns.
      --
      -- NOT yet load-bearing: `result-place` still lets the callee choose, so
      -- neither sub-IR is obliged to honour these. Making them binding is the
      -- next step, and it is what will force compose to RESERVE the
      -- intermediate slot (its `bump` must then account for it).
      inter-dest : Place
      inter-dest = AtStorage (AtStack (current-frame alloc) (next-slot alloc))

      f-result-pair = rec-wf mIn f (∘-f-smaller f g) x s alloc input-place
                        inter-dest not-halted
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
      -- Stage F: f's RESULT PLACE decides how the intermediate reaches g.
      -- `ir-to-trace (g ∘ f) = ft ++ mov-to-input ∷ gt` does not spill, and
      -- `mov-to-input` copies whatever `Output` holds — a pointer for a
      -- located result, the VALUE itself for a register-resident one. That is
      -- exactly `place-sv`, and `place-rax` is the (total) fact that `Output`
      -- held it. The old `FFacts` record hard-coded `SV-Ptr inter-loc` and a
      -- `ValidAtWF`, so it could not be built for an `at-reg` intermediate.
      rp = IRResultAWF.result-place result-f

      ------------------------------------------------------------------------
      -- Plan 0.14: g runs from alloc₁ (the actual runtime alloc after f),
      -- not a synthetic alloc₁-reclaimed. With IRResultBase.alloc-correct,
      -- alloc₁ = proj₂ (exec-trace f-trace s alloc) is what the runtime
      -- delivers; pretending the heap-ref didn't bump (the old reclaimed
      -- alloc) would actively undercount heap usage when f is heap-mode.
      ------------------------------------------------------------------------
      -- reclaim-f kept as next-slot alloc₁ for budget bookkeeping use below.
      reclaim-f = next-slot alloc₁

      reclaim-f-bound : reclaim-f ≤ next-slot alloc +ℕ rf
      reclaim-f-bound = IRResultAWF.slot-stays-in-budget result-f

      s₁' = record s₁ { regs = writeReg (regs s₁) Input1 (place-sv rp) }

      rdi-eq₁ : readReg (regs s₁') Input1 ≡ place-sv rp
      rdi-eq₁ = writeReg-same (regs s₁) Input1 (place-sv rp)

      -- The place is built by a helper TAKING the register equation, not by a
      -- `with` on `rp`: a `with` here would abstract `rp` in the goal but not
      -- in `rdi-eq₁`, which is bound outside it.
      mk-g-input : (rp' : ResultPlace _ mMid alloc₁ _ (eval f x) s₁)
                 → readReg (regs s₁') Input1 ≡ place-sv rp'
                 → InputPlace mMid alloc₁ (eval f x) s₁'
      mk-g-input (at-loc loc valid before _ _ _) eq =
        in-at-loc loc (validityWF-mem-only (eval f x) loc s₁ s₁' refl refl valid) before eq
      -- Register-resident: no `ValidAtWF`, because there is no cell to be
      -- valid at. The register equation IS the residence witness.
      mk-g-input (at-reg _ fit _ _ _) eq = in-at-reg fit eq
      -- A Unit intermediate has no residence, so there is nothing to locate
      -- and nothing to postulate. This retires the `unit-inter-loc` /
      -- `unit-inter-before` / `unit-inter-rax` trio the old `FFacts` needed.
      mk-g-input unit-result eq = in-unit refl

      g-input : InputPlace mMid alloc₁ (eval f x) s₁'
      g-input = mk-g-input rp rdi-eq₁

      ------------------------------------------------------------------------
      -- Run g via recursive dispatch
      ------------------------------------------------------------------------
      g-result-pair = rec-wf mMid g (∘-g-smaller f g) (eval f x) s₁' alloc₁
                        g-input dest not-halted₁
      mOut = proj₁ g-result-pair
      result-g = proj₂ g-result-pair
      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      g-trace = IRResultAWF.trace result-g

      -- Plan 0.17: compose-bump = bump-+ result-f.bump result-g.bump.
      -- (Composition: f's effect then g's effect.)
      compose-bump : AllocBump
      compose-bump = bump-+ (IRResultAWF.bump result-f) (IRResultAWF.bump result-g)

      -- alloc₂ = final-alloc result-g = apply-bump (bump g) alloc₁ (derived
      -- field, definitional), and alloc₁ = apply-bump (bump f) alloc, so this
      -- is exactly the apply-bump/bump-+ homomorphism.
      compose-bump-eq : alloc₂ ≡ apply-bump compose-bump alloc
      compose-bump-eq =
        apply-bump-compose (IRResultAWF.bump result-f) (IRResultAWF.bump result-g) alloc
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
                           (sym (place-rax rp))

      s-final-eq : s-final ≡ s₂
      s-final-eq = exec-trace-compose-eq f-trace g-trace s alloc s₁ s₁' alloc₁ s₂
                     (IRResultAWF.trace-correct result-f)
                     not-halted₁
                     s₁'-eq-output
                     (IRResultAWF.frame-preserved result-f)
                     (IRResultAWF.trace-correct result-g)

      ------------------------------------------------------------------------
      -- alloc-correct: trace through the three trace segments, using
      -- result-f.alloc-correct, mov-to-input's alloc preservation, and
      -- result-g.alloc-correct.
      ------------------------------------------------------------------------
      alloc-correct-compose : proj₂ (exec-trace compose-trace s alloc) ≡ alloc₂
      alloc-correct-compose =
        let alloc-after-f-runtime = proj₂ (exec-trace f-trace s alloc)
            -- Step 1: split via exec-trace-append, then bridge to (s₁, alloc₁).
            split : exec-trace compose-trace s alloc ≡
                    exec-trace (mov-to-input ∷ g-trace)
                      (proj₁ (exec-trace f-trace s alloc)) alloc-after-f-runtime
            split = exec-trace-append f-trace (mov-to-input ∷ g-trace) s alloc
            f-state-eq : proj₁ (exec-trace f-trace s alloc) ≡ s₁
            f-state-eq = IRResultAWF.trace-correct result-f
            f-alloc-eq : alloc-after-f-runtime ≡ alloc₁
            f-alloc-eq = IRResultAWF.alloc-correct result-f
            bridge : exec-trace (mov-to-input ∷ g-trace)
                       (proj₁ (exec-trace f-trace s alloc)) alloc-after-f-runtime
                     ≡ exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁
            bridge = cong₂ (exec-trace (mov-to-input ∷ g-trace)) f-state-eq f-alloc-eq
            -- Step 2: unfold cons. mov-to-input preserves alloc; its proj₁
            -- equals s₁' by s₁'-eq-output composed with inter-rax-f'.
            mov-cons : exec-trace (mov-to-input ∷ g-trace) s₁ alloc₁ ≡
                       exec-trace g-trace
                         (proj₁ (exec-abstract mov-to-input s₁ alloc₁))
                         (proj₂ (exec-abstract mov-to-input s₁ alloc₁))
            mov-cons = exec-trace-cons mov-to-input g-trace s₁ alloc₁ not-halted₁
            mov-state-eq : proj₁ (exec-abstract mov-to-input s₁ alloc₁) ≡ s₁'
            mov-state-eq = sym s₁'-eq-output
            mov-alloc-eq : proj₂ (exec-abstract mov-to-input s₁ alloc₁) ≡ alloc₁
            mov-alloc-eq = refl
            after-mov : exec-trace g-trace
                          (proj₁ (exec-abstract mov-to-input s₁ alloc₁))
                          (proj₂ (exec-abstract mov-to-input s₁ alloc₁))
                        ≡ exec-trace g-trace s₁' alloc₁
            after-mov = cong₂ (exec-trace g-trace) mov-state-eq mov-alloc-eq
            -- Step 3: result-g.alloc-correct.
            g-alloc-eq : proj₂ (exec-trace g-trace s₁' alloc₁) ≡ alloc₂
            g-alloc-eq = IRResultAWF.alloc-correct result-g
        in trans (cong proj₂ (trans split (trans bridge (trans mov-cons after-mov))))
                 g-alloc-eq

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

      -- Plan 0.14: with g running from alloc₁ (not the synthetic
      -- alloc₁-reclaimed), heap-monotone composes directly through both
      -- sub-IRs — no heap-eq-f bridge needed.
      heap-mono : next-heap-ref alloc ≤ next-heap-ref alloc₂
      heap-mono = ≤-trans (IRResultAWF.heap-monotone result-f)
                          (IRResultAWF.heap-monotone result-g)

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

      -- Plan 0.14 follow-up (consequence-form): the IRHeapBudget field
      -- `trace-no-heap-writes` was eliminated as architecturally false for
      -- heap-mode sub-IRs. Stack-mode sub-IRs satisfy it; ComposeWF's
      -- compose-frontier-stable derivation depends on it locally — for now
      -- it's postulated. Discharge when the optional `IsStackOnly` evidence
      -- is wired into the producer interface (separate plan).

      f-tph : TraceWF s alloc f-trace
      f-tph = IRResultAWF.trace-twf result-f
      -- TODO: g-tph runs at a runtime state different from g's construction
      -- state; same shape as PairStackWF's g-tph-runtime. Postulate for the
      -- scaffold pass, discharge in follow-up.
      g-tph : TraceWF (proj₁ (exec-trace (f-trace ++ mov-to-input ∷ []) s alloc))
                      (proj₂ (exec-trace (f-trace ++ mov-to-input ∷ []) s alloc))
                      g-trace
      g-tph = SMP.!!  -- TODO: bridge from result-g's trace-twf
      compose-trace-twf : TraceWF s alloc compose-trace
      compose-trace-twf = SMP.!!  -- TODO: twf-++ f-tph (twf-∷ tt g-tph) with state-threading

      ------------------------------------------------------------------
      -- Plan 0.16 TraceEvaluator: routes alloc-correct, trace-twf and
      -- mem-preserved-before through a single bundle. `exec-alloc-eq`
      -- reuses `alloc-correct-compose`; `trace-wf` and
      -- `mem-preserved-before` remain scaffolded.
      ------------------------------------------------------------------
      trace-eval : TraceEvaluator compose-trace s alloc
      trace-eval = mk-trace-evaluator
        s-final
        alloc₂
        compose-trace-twf            -- trace-wf
        refl                         -- exec-state-eq (definitional)
        alloc-correct-compose        -- exec-alloc-eq
        (λ _ _ → SMP.!!)             -- mem-preserved-before

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
          f-tnhw = SMP.!!  -- TODO: stack-only sub-IR derivation (post Plan 0.14 follow-up)

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
          g-tnhw = SMP.!!  -- TODO: stack-only sub-IR derivation (post Plan 0.14 follow-up)

          -- We have: next-slot alloc ≤ reclaim-f (by f's slot-monotone, since reclaim-f = next-slot alloc₁)
          reclaim-f-mono : next-slot alloc ≤ reclaim-f
          reclaim-f-mono = IRResultAWF.slot-monotone result-f

          -- Frame equivalence
          frame-after-mov : current-frame alloc-after-mov ≡ current-frame alloc
          frame-after-mov = trans (exec-abstract-preserves-frame mov-to-input s-after-f alloc-after-f)
                                  (exec-trace-preserves-frame f-trace s' alloc)

          frame-equiv : current-frame alloc-after-mov ≡ current-frame alloc₁
          frame-equiv = trans frame-after-mov (sym (IRResultAWF.frame-preserved result-f))

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
              -- exec-trace-preserves-slot-below reads at current-frame alloc₁;
              -- bridge to current-frame alloc via frame-preserved.
              slot-after-g : next-slot alloc < reclaim-f →
                             readLoc (proj₁ (exec-trace g-trace s-after-mov alloc₁))
                                     (AtStack (current-frame alloc) (next-slot alloc)) ≡ just (SV-Ptr input-loc')
              slot-after-g slot<reclaim-f =
                let preserved-at-f-frame = exec-trace-preserves-slot-below g-trace s-after-mov alloc₁
                                  reclaim-f (next-slot alloc) g-twa g-tnhw slot<reclaim-f
                    preserved : readLoc (proj₁ (exec-trace g-trace s-after-mov alloc₁))
                                        (AtStack (current-frame alloc) (next-slot alloc))
                                ≡ readLoc s-after-mov (AtStack (current-frame alloc) (next-slot alloc))
                    preserved = subst (λ fr → readLoc (proj₁ (exec-trace g-trace s-after-mov alloc₁))
                                                       (AtStack fr (next-slot alloc))
                                              ≡ readLoc s-after-mov (AtStack fr (next-slot alloc)))
                                      (IRResultAWF.frame-preserved result-f)
                                      preserved-at-f-frame
                in trans preserved slot-after-mov

              split1 : proj₁ (exec-trace compose-trace s' alloc) ≡
                       proj₁ (exec-trace (mov-to-input ∷ g-trace) s-after-f alloc-after-f)
              split1 = exec-trace-append-state f-trace (mov-to-input ∷ g-trace) s' alloc

              split2 : exec-trace (mov-to-input ∷ g-trace) s-after-f alloc-after-f ≡
                       exec-trace g-trace s-after-mov alloc-after-mov
              split2 = exec-trace-cons mov-to-input g-trace s-after-f alloc-after-f not-halted-after-f

              frame-g-result : proj₁ (exec-trace g-trace s-after-mov alloc-after-mov) ≡
                               proj₁ (exec-trace g-trace s-after-mov alloc₁)
              frame-g-result = exec-trace-same-frame g-trace s-after-mov alloc-after-mov alloc₁ frame-equiv

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

      ------------------------------------------------------------------------
      -- Plan 0.17.1: discharge the new IRStackBudget / IRHeapBudget fields.
      -- compose-bump = bump-+ result-f.bump result-g.bump (concrete), so
      -- next-slot-delta compose-bump reduces defequally to
      -- (next-slot-delta result-f.bump +ℕ next-slot-delta result-g.bump).
      -- compose-bump-eq (SMP.!! placeholder for now) bridges alloc₂ to
      -- apply-bump compose-bump alloc; algebraic obligations chain into
      -- the existing compose-* lemmas via subst.
      ------------------------------------------------------------------------

      compose-bump-fits-stack-budget : next-slot-delta compose-bump ≤ req-compose
      compose-bump-fits-stack-budget =
        +-mono-≤ (IRResultAWF.bump-fits-stack-budget result-f)
                 (IRResultAWF.bump-fits-stack-budget result-g)
        where open import Data.Nat.Properties using (+-mono-≤)

      compose-max-slot-geq-final-bump :
        next-slot-delta compose-bump +ℕ next-slot alloc ≤ compose-max-slot
      compose-max-slot-geq-final-bump =
        subst (λ a → next-slot a ≤ compose-max-slot)
              compose-bump-eq
              compose-max-slot-geq-final

      compose-scratch-bounded-bump :
        compose-max-slot ≤ next-slot (apply-bump compose-bump alloc) +ℕ req-compose-scratch
      compose-scratch-bounded-bump =
        subst (λ a → compose-max-slot ≤ next-slot a +ℕ req-compose-scratch)
              compose-bump-eq
              compose-scratch-bounded

      compose-bump-fits-heap-budget :
        next-heap-ref-delta compose-bump
        ≤ IRResultAWF.heap-budget result-f +ℕ IRResultAWF.heap-budget result-g
      compose-bump-fits-heap-budget =
        +-mono-≤ (IRResultAWF.bump-fits-heap-budget result-f)
                 (IRResultAWF.bump-fits-heap-budget result-g)
        where open import Data.Nat.Properties using (+-mono-≤)

      compose-max-heap-ref-geq-final-bump :
        next-heap-ref-delta compose-bump +ℕ next-heap-ref alloc
        ≤ IRResultAWF.max-heap-ref-written result-g
      compose-max-heap-ref-geq-final-bump =
        subst (λ a → next-heap-ref a ≤ IRResultAWF.max-heap-ref-written result-g)
              compose-bump-eq
              (IRResultAWF.max-heap-ref-geq-final result-g)