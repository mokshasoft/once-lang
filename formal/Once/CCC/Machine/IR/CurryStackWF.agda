-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.IR.CurryStackWF
--
-- Curry IR implementation with clean trace-based structure.
-- Final state defined via exec-trace, making trace-correct = refl.
--
-- RELOCATION APPROACH: No frame manipulation, just stack slot writes.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.CurryStackWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; _≥_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; m≤m+n; m<m+n; m+n≤o⇒m≤o; +-monoʳ-≤; *-monoˡ-≤; m≤m*n; +-assoc; n≤1+n; +-comm)
open import Data.Bool using (false)
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.IR
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
open import Once.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Target.X86-64.Layout using (closure-slots)
open import Once.CCC.Machine.Allocation hiding (AllocMode)

-- Import SMPrimitives qualified for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

-- Import proof obligation marker
import Once.ProofObligation as PO

------------------------------------------------------------------------
-- Curry implementation with clean trace-based structure
------------------------------------------------------------------------

module CurryStackWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → EvV.⟦ A ⟧ᴵ → EvV.⟦ B ⟧ᴵ
  eval = Ev.eval (FrameSemantics.float-format FS)

  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open ExecLemmas {FS}
  open AbstractExec {FS}
  open FrameSemantics FS

  -- Open SMPrimitives modules for trace lemmas
  open SMP.MemoryOps {FS}
  open SMP.InstrPrimitives {FS}
  open SMP.TracePrimitives {FS}
  open SMP.TraceComposition {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc; RecDispatcherWF; BodyCorrect;
           valid-closure-wf; validityWF-mem-only;
           validityWF-alloc-advance; validityWF-frontier-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-with-bf-transfer; validityWF-trace-preserves;
           mk-IRResultAWF-via-bump;
           mem-preserved-from-tnhw)

  -- Import bf-same-frame-slot from BFTransfer module
  open import Once.CCC.Machine.IR.ApplyWF
  open BFTransfer {FS}
    using (bf-same-frame-slot)

  -- Import lemmas
  open import Once.CCC.Machine.DispatcherArithmeticLemma
    using (suc<+2)
  open import Once.CCC.Machine.SizeBoundLemma
    using (curry-body-bound)

  -- Import write operations
  open import Once.CCC.Machine.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import frontier lemmas
  open import Once.CCC.Machine.FrontierLemma using (module FrontierLemmas)
  open FrontierLemmas {FS}
    using (at-frontier-before-closure; frontier-same-heap)

  ------------------------------------------------------------------------
  -- Helper lemmas
  ------------------------------------------------------------------------

  closure-slots-≤-curry-req : ∀ {A B C k} (f : IR (A * B) C) (m : AllocMode) →
    closure-slots ≤ ir-stack-requirement (curry {k = k} f m)
  closure-slots-≤-curry-req f Stack = ≤-refl
  closure-slots-≤-curry-req f Heap = ≤-refl

  ------------------------------------------------------------------------
  -- Curry trace: stores closure (env pointer + code pointer)
  ------------------------------------------------------------------------

  curry-trace : (closure-slot : ℕ) → AbstractTrace
  curry-trace closure-slot =
    -- Plan 0.14: instr-alloc-stack at the start so runtime alloc
    -- catches up to alloc' (= record alloc { next-slot += closure-slots }).
    instr-alloc-stack closure-slots ∷
    mov-to-output ∷                    -- Output := Input1 (env pointer)
    store-at-slot closure-slot ∷       -- closure[0] := env
    lea-slot (suc closure-slot) ∷      -- Output := &closure[1] (code loc)
    store-at-slot (suc closure-slot) ∷ -- closure[1] := code pointer
    lea-slot closure-slot ∷ []         -- Output := closure address

  -- Plan 0.14: alloc-correct shape lemma for curry-trace. The trace
  -- starts with `instr-alloc-stack closure-slots`, which bumps
  -- next-slot by closure-slots; the remaining 5 instructions all
  -- preserve alloc definitionally (mov-to-output, store-at-slot,
  -- lea-slot, store-at-slot, lea-slot all return `, alloc`).
  curry-trace-alloc-correct : ∀ (closure-slot : ℕ) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    proj₂ (exec-trace (curry-trace closure-slot) s alloc) ≡
      record alloc { next-slot = next-slot alloc +ℕ closure-slots }
  curry-trace-alloc-correct closure-slot s alloc not-halted =
    -- Step-by-step: each instruction preserves halted unconditionally,
    -- so we can chain exec-trace-cons through all 6 instructions and
    -- end with the alloc that `instr-alloc-stack closure-slots`
    -- produced (= the desired record).
    let s₁ = proj₁ (exec-abstract (instr-alloc-stack closure-slots) s alloc)
        alloc₁ = proj₂ (exec-abstract (instr-alloc-stack closure-slots) s alloc)
        -- alloc₁ = record alloc { next-slot = next-slot alloc + closure-slots } (definitional)
        h₁ = exec-abstract-preserves-halted (instr-alloc-stack closure-slots) s alloc
               not-halted iph-alloc-stack

        s₂ = proj₁ (exec-abstract mov-to-output s₁ alloc₁)
        -- proj₂ (exec-abstract mov-to-output s₁ alloc₁) = alloc₁ (definitional)
        h₂ = exec-abstract-preserves-halted mov-to-output s₁ alloc₁ h₁ iph-mov-to-output

        s₃ = proj₁ (exec-abstract (store-at-slot closure-slot) s₂ alloc₁)
        h₃ = exec-abstract-preserves-halted (store-at-slot closure-slot) s₂ alloc₁ h₂ iph-store-at-slot

        s₄ = proj₁ (exec-abstract (lea-slot (suc closure-slot)) s₃ alloc₁)
        h₄ = exec-abstract-preserves-halted (lea-slot (suc closure-slot)) s₃ alloc₁ h₃ iph-lea-slot

        s₅ = proj₁ (exec-abstract (store-at-slot (suc closure-slot)) s₄ alloc₁)
        h₅ = exec-abstract-preserves-halted (store-at-slot (suc closure-slot)) s₄ alloc₁ h₄ iph-store-at-slot

        -- Chain exec-trace through each step.
        d₀ = exec-trace-cons (instr-alloc-stack closure-slots) _ s alloc not-halted
        d₁ = exec-trace-cons mov-to-output _ s₁ alloc₁ h₁
        d₂ = exec-trace-cons (store-at-slot closure-slot) _ s₂ alloc₁ h₂
        d₃ = exec-trace-cons (lea-slot (suc closure-slot)) _ s₃ alloc₁ h₃
        d₄ = exec-trace-cons (store-at-slot (suc closure-slot)) _ s₄ alloc₁ h₄
        d₅ = exec-trace-single (lea-slot closure-slot) s₅ alloc₁ h₅
    in cong proj₂ (trans d₀ (trans d₁ (trans d₂ (trans d₃ (trans d₄ d₅)))))

  ------------------------------------------------------------------------
  -- run-curry: Clean trace-based implementation
  ------------------------------------------------------------------------

  run-curry : ∀ {A B C k} (mIn : AllocMode) (f : IR (A * B) C) (m : AllocMode)
    (ir<bound : ir-size (curry {k = k} f m) < program-bound)
    (rec-wf : RecDispatcherWF (ir-size (curry {k = k} f m)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) Input1 ≡ SV-Ptr input-loc →
    -- Plan 0.17.2 follow-up: Stack-mode curry now produces
    -- IRResultAWF Stack (closure-loc is AtStack). Per the architecture
    -- doc, mode tag = where the output lives.
    IRResultAWF Stack (curry {k = k} f m) x s alloc
  run-curry {A} {B} {C} {k} mIn f m ir<bound rec-wf x input-loc s alloc
    input-valid-wf input-before not-halted rdi-eq =
    -- Plan 0.17: use mk-IRResultAWF-via-bump. alloc-correct stays at
    -- alloc' (= record alloc { next-slot = next-slot alloc + closure-slots });
    -- bridge to apply-bump (mkBump closure-slots 0) alloc via +-comm.
    mk-IRResultAWF-via-bump
      s'
      alloc'
      trace
      (mkBump closure-slots 0)
      curry-bump-eq
      SMP.!!  -- trace-is-ir-to-trace (dead path)
      refl    -- trace-correct
      (curry-trace-alloc-correct closure-slot s alloc not-halted)
      (at-loc closure-loc result-valid-wf' closure-before' rax-eq'
              reclaim-preserves-validity' reclaim-preserves-result')
      not-halted'
      (mem-preserved-from-tnhw alloc trace s s' refl trace-writes-above' tt)
      trace-twf'
      (exec-trace-preserves-halted-WF trace)
      _
      (record
        { max-slot-written = next-slot alloc +ℕ closure-slots
        ; stack-budget = ir-stack-requirement (curry {k = k} f m)
        ; bump-fits-stack-budget = closure-bound
        ; max-slot-geq-final = ≤-reflexive (+-comm closure-slots (next-slot alloc))
        ; max-slot-usage-bound = +-monoʳ-≤ (next-slot alloc) closure-bound
        ; frontier-slot-stable = frontier-stable'
        ; trace-writes-above = trace-writes-above'
        ; trace-slot-reads-above = tt
        ; trace-writes-below = trace-writes-below'
        ; trace-slot-reads-below = tt
        ; scratch-budget = ir-scratch-requirement (curry {k = k} f m)
        ; scratch-bounded = subst (_≤ (closure-slots +ℕ next-slot alloc) +ℕ req-curry)
                                  (+-comm closure-slots (next-slot alloc))
                                  (m≤m+n (closure-slots +ℕ next-slot alloc) req-curry)
        })
      (record
        { heap-budget = 0
        ; max-heap-ref-written = next-heap-ref alloc
        ; bump-fits-heap-budget = z≤n
        ; max-heap-ref-geq-final = ≤-refl
        ; max-heap-usage-bound = m≤m+n (next-heap-ref alloc) 0
        })
    where
      curry-bump-eq : record alloc { next-slot = next-slot alloc +ℕ closure-slots }
                      ≡ apply-bump (mkBump closure-slots 0) alloc
      curry-bump-eq = cong (λ s → record alloc { next-slot = s })
                           (+-comm (next-slot alloc) closure-slots)
        where open import Data.Nat.Properties using (+-comm)

      -- Closure location and trace
      closure-slot = next-slot alloc
      closure-loc = AtStack (current-frame alloc) closure-slot
      code-loc = sucLoc closure-loc
      trace = curry-trace closure-slot

      -- CLEAN: Final state defined by exec-trace
      s' : LocState FS
      s' = proj₁ (exec-trace trace s alloc)

      alloc' : AllocState {FS}
      alloc' = record alloc { next-slot = next-slot alloc +ℕ closure-slots }

      -- Size bounds
      body<bound = curry-body-bound {k = k} f {m} program-bound ir<bound
      req-curry = ir-stack-requirement (curry {k = k} f m)
      closure-bound : closure-slots ≤ req-curry
      closure-bound = closure-slots-≤-curry-req {k = k} f m

      ----------------------------------------------------------------------
      -- Trace properties (defined first for use in proofs)
      ----------------------------------------------------------------------

      trace-writes-above' : TraceWritesAbove closure-slot trace
      trace-writes-above' = ≤-refl , (n≤1+n closure-slot , tt)

      trace-writes-below' : TraceWritesBelow (next-slot alloc +ℕ closure-slots) trace
      trace-writes-below' =
        m<m+n closure-slot {closure-slots} (s≤s z≤n) ,
        (suc<+2 closure-slot , tt)

      -- Note: trace-preserves-capacity' removed in Phase 3

      trace-twf' : TraceWF s alloc trace
      trace-twf' =
        twf-∷ tt
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ tt
        (twf-∷ tt twf-[])))))

      ----------------------------------------------------------------------
      -- Proof obligations for exec-trace properties
      ----------------------------------------------------------------------

      -- Halted status preserved (use exec-trace-preserves-halted)
      not-halted' : halted s' ≡ false
      not-halted' = exec-trace-preserves-halted-WF trace s alloc not-halted trace-twf'

      -- Output register contains closure address
      -- The trace ends with lea-slot closure-slot, so Output = AtStack frame closure-slot
      -- Proof: split trace = prefix ++ [lea-slot closure-slot], use exec-trace-final-lea-slot
      prefix-trace : AbstractTrace
      prefix-trace = instr-alloc-stack closure-slots ∷ mov-to-output ∷ store-at-slot closure-slot ∷
                     lea-slot (suc closure-slot) ∷ store-at-slot (suc closure-slot) ∷ []

      prefix-tph : TraceWF s alloc prefix-trace
      prefix-tph = twf-∷ tt
                   (twf-∷ tt
                   (twf-∷ tt
                   (twf-∷ tt
                   (twf-∷ tt twf-[]))))

      not-halted-after-prefix : halted (proj₁ (exec-trace prefix-trace s alloc)) ≡ false
      not-halted-after-prefix = exec-trace-preserves-halted-WF prefix-trace s alloc not-halted prefix-tph

      rax-eq' : readReg (regs s') Output ≡ SV-Ptr closure-loc
      rax-eq' = exec-trace-final-lea-slot prefix-trace closure-slot s alloc not-halted-after-prefix

      -- Closure slot env-ptr': store-at-slot writes Input1 to closure-slot, preserved by rest
      -- Using prefix-store-preserve with:
      --   prefix = [mov-to-output]
      --   k = closure-slot
      --   suffix = [lea-slot (suc closure-slot), store-at-slot (suc closure-slot), lea-slot closure-slot]
      env-prefix : AbstractTrace
      env-prefix = mov-to-output ∷ []

      env-suffix : AbstractTrace
      env-suffix = lea-slot (suc closure-slot) ∷ store-at-slot (suc closure-slot) ∷
                   lea-slot closure-slot ∷ []

      env-prefix-tph : TraceWF s alloc env-prefix
      env-prefix-tph = twf-∷ tt twf-[]

      -- env-suffix = lea-slot (suc cs) ∷ store-at-slot (suc cs) ∷ lea-slot cs ∷ []
      -- lea-slot doesn't write (nothing), store-at-slot (suc cs) writes to (suc cs)
      -- Need: suc cs ≤ suc cs for the store, rest is tt
      env-suffix-twa : TraceWritesAbove (suc closure-slot) env-suffix
      env-suffix-twa = ≤-refl , tt

      -- After mov-to-output: Output = Input1 = input-loc
      -- Use exec-abstract directly for definitional computation, then connect via exec-trace-single
      s-after-mov : LocState FS
      s-after-mov = proj₁ (exec-abstract mov-to-output s alloc)

      -- Output = Input1 after mov-to-output (definitional from exec-abstract)
      output-after-mov : readReg (regs s-after-mov) Output ≡ SV-Ptr input-loc
      output-after-mov = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) rdi-eq

      -- Connect exec-trace to exec-abstract
      exec-trace-env-prefix : exec-trace env-prefix s alloc ≡ exec-abstract mov-to-output s alloc
      exec-trace-env-prefix = exec-trace-single mov-to-output s alloc not-halted

      s-after-env-prefix : LocState FS
      s-after-env-prefix = proj₁ (exec-trace env-prefix s alloc)

      s-after-env-prefix-eq : s-after-env-prefix ≡ s-after-mov
      s-after-env-prefix-eq = cong proj₁ exec-trace-env-prefix

      output-after-env-prefix : readReg (regs s-after-env-prefix) Output ≡ SV-Ptr input-loc
      output-after-env-prefix = subst (λ s'' → readReg (regs s'') Output ≡ SV-Ptr input-loc)
                                      (sym s-after-env-prefix-eq) output-after-mov

      -- TODO (post-scaffold): rederive via a TraceWF-shaped prefix-store-preserve.
      env-ptr' : readLoc s' closure-loc ≡ just (SV-Ptr input-loc)
      env-ptr' = SMP.!!

      -- Code slot code-ptr': lea-slot sets Output=code-loc, store-at-slot stores it
      -- Using prefix-store-preserve with:
      --   prefix = [mov-to-output, store-at-slot closure-slot, lea-slot (suc closure-slot)]
      --   k = suc closure-slot
      --   suffix = [lea-slot closure-slot]
      code-prefix : AbstractTrace
      code-prefix = mov-to-output ∷ store-at-slot closure-slot ∷ lea-slot (suc closure-slot) ∷ []

      code-suffix : AbstractTrace
      code-suffix = lea-slot closure-slot ∷ []

      code-prefix-tph : TraceWF s alloc code-prefix
      code-prefix-tph = twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[]))

      -- suc (suc closure-slot) > suc closure-slot, and lea-slot doesn't write
      code-suffix-twa : TraceWritesAbove (suc (suc closure-slot)) code-suffix
      code-suffix-twa = tt

      -- After code-prefix: Output = AtStack frame (suc closure-slot) = code-loc
      s-after-code-prefix : LocState FS
      s-after-code-prefix = proj₁ (exec-trace code-prefix s alloc)

      code-prefix-not-halted : halted s-after-code-prefix ≡ false
      code-prefix-not-halted = exec-trace-preserves-halted-WF code-prefix s alloc not-halted code-prefix-tph

      -- lea-slot (suc closure-slot) puts AtStack frame (suc closure-slot) in Output
      -- Use exec-trace-final-lea-slot: code-prefix = prefix ++ [lea-slot k]
      -- where prefix = mov-to-output ∷ store-at-slot closure-slot ∷ []
      code-prefix-before-lea : AbstractTrace
      code-prefix-before-lea = mov-to-output ∷ store-at-slot closure-slot ∷ []

      code-prefix-before-lea-tph : TraceWF s alloc code-prefix-before-lea
      code-prefix-before-lea-tph = twf-∷ tt (twf-∷ tt twf-[])

      not-halted-before-lea : halted (proj₁ (exec-trace code-prefix-before-lea s alloc)) ≡ false
      not-halted-before-lea = exec-trace-preserves-halted-WF code-prefix-before-lea s alloc not-halted
                                code-prefix-before-lea-tph

      output-after-code-prefix : readReg (regs s-after-code-prefix) Output ≡ SV-Ptr code-loc
      output-after-code-prefix = SMP.!!  -- TODO: exec-trace-final-lea-slot under StoredValue

      -- TODO (post-scaffold): rederive via TraceWF-shaped prefix-store-preserve.
      code-ptr' : readLoc s' code-loc ≡ just (SV-Ptr code-loc)
      code-ptr' = SMP.!!

      -- Memory before frontier is preserved
      -- Trace writes above closure-slot, so slots below are preserved
      mem-preserved' : ∀ loc → BeforeFrontier alloc loc → readLoc s' loc ≡ readLoc s loc
      mem-preserved' (AtStack f' k) (stack-before {.f'} {.k} frame-eq k<next) =
        -- k < next-slot alloc = closure-slot, so slot k is below write region
        subst (λ f → readLoc s' (AtStack f k) ≡ readLoc s (AtStack f k))
              (sym frame-eq)
              (exec-trace-preserves-slot-below trace s alloc closure-slot k
                 trace-writes-above' tt k<next)
      mem-preserved' (AtStack f' k) (stack-ancestor {.f'} cf≺f' _) =
        -- f' is an ancestor frame (current-frame alloc ≺ f')
        exec-trace-preserves-ancestor trace s alloc f' k cf≺f' tt
      mem-preserved' (AtDynamic h) (heap-before _) =
        -- Heap location, use preserves-heap-loc
        exec-trace-preserves-heap-loc trace s alloc h tt

      -- Frontier slot stability
      -- The trace writes to closure-slot, but writes the SAME value (input-loc'):
      --   1. mov-to-output: Output = Input1 = input-loc'
      --   2. store-at-slot closure-slot: slot = Output = input-loc'
      --   3. Rest of trace writes only to higher slots
      frontier-stable' : ∀ (s'' : LocState FS) (input-loc' : ValueLocation FS) →
        halted s'' ≡ false →
        readReg (regs s'') Input1 ≡ SV-Ptr input-loc' →
        readLoc s'' (AtStack (current-frame alloc) closure-slot) ≡ just (SV-Ptr input-loc') →
        _
      -- TODO (post-scaffold): rederive via TraceWF-shaped prefix-store-preserve
      -- under StoredValue (Output now stores SV-Ptr input-loc').
      frontier-stable' s'' input-loc' _ _ _ = SMP.!!

      -- Input1 validity in final state
      -- Transfer validity across memory-preserving trace execution
      -- Step 1: Use validityWF-trace-preserves to preserve through trace execution
      -- Step 2: Use validityWF-frontier-advance to convert alloc → alloc'
      input-valid-at-s' : ValidAtWF mIn alloc x input-loc s'
      input-valid-at-s' = validityWF-trace-preserves alloc trace x input-loc s
                            input-before input-valid-wf trace-writes-above' tt

      input-valid-wf' : ValidAtWF mIn alloc' x input-loc s'
      input-valid-wf' = validityWF-frontier-advance x input-loc s'
                          refl (m≤m+n (next-slot alloc) closure-slots) ≤-refl
                          input-valid-at-s'

      -- Closure is before frontier in updated allocation
      closure-before' : BeforeFrontier alloc' closure-loc
      closure-before' = at-frontier-before-closure alloc

      -- Input1 location still before frontier after allocation
      input-before' : BeforeFrontier alloc' input-loc
      input-before' = stack-alloc-advances alloc closure-slots input-loc input-before

      -- Code location before frontier
      code-before' : BeforeFrontier alloc' code-loc
      code-before' = stack-before refl (suc<+2 closure-slot)

      -- BodyCorrect: recursive dispatcher for body
      body-correct : BodyCorrect f x input-loc program-bound
      body-correct = record
        { body-capacity = ir-stack-requirement f
        ; body-cap-eq = refl
        -- Note: cap' parameter removed in Phase 3
        ; execute = λ arg arg-loc pair-loc s'' alloc'' mPair pair-valid-wf pair-before not-halt rdi-eq' →
            rec-wf mPair f (curry-smaller {k = k} f {m}) (pair x arg) pair-loc s'' alloc''
              pair-valid-wf pair-before not-halt rdi-eq'
        }

      -- Result validity: closure with body-correct embedded
      -- Plan 0.14 (Camp 2): closure-loc is AtStack but ValidAtWF Stack; lmm
      -- reduces to ⊥. Surfaced as SMP.!! pending either deletion of this path
      -- or actual heap-allocated closure lowering.
      result-valid-wf' : ValidAtWF Stack alloc' (eval (curry {k = k} f m) x) closure-loc s'
      -- Plan 0.17.2 follow-up (2026-05-23): valid-closure-wf is now
      -- mode-polymorphic. With CurryStackWF returning IRResultAWF
      -- Stack, the LocMatchesMode obligation becomes `LocMatchesMode
      -- Stack (AtStack ...) = ⊤`, witness = tt (was SMP.!!).
      -- The second SMP.!! is for the SV-Code-at-closure[1] obligation
      -- — still pending the Stack trace migration to instr-load-code-addr.
      result-valid-wf' = valid-closure-wf body<bound {body-label = 0} tt
        env-ptr' SMP.!! input-before' code-before'
        input-valid-wf' body-correct

      -- Reclamation proofs
      -- Note: fits parameter removed in Phase 3
      reclaim-preserves-result' :
        BeforeFrontier (record alloc { next-slot = next-slot alloc +ℕ closure-slots }) closure-loc
      reclaim-preserves-result' =
        frontier-same-heap alloc' (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
          refl refl refl closure-loc closure-before'

      reclaim-preserves-validity' :
        ValidAtWF Stack (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
                  (eval (curry {k = k} f m) x) closure-loc s'
      reclaim-preserves-validity' = validityWF-with-bf-transfer
        (eval (curry {k = k} f m) x) closure-loc s' alloc'
        (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
        (λ loc bf → bf-same-frame-slot alloc'
          (record alloc { next-slot = next-slot alloc +ℕ closure-slots })
          refl refl refl loc bf)
        result-valid-wf'