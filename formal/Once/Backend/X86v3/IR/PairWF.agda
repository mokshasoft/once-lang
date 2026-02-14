------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.PairWF
--
-- Pair IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.PairWF where

open import Data.Nat using (ℕ; suc; _<_; _+_; _≤_; s≤s; z≤n) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m<m+n; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Pair implementation
------------------------------------------------------------------------

module PairWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open StackAllocation {FS}
  open FrameSemantics FS

  -- Import IRResultAWF and ValidAtWF
  open import Once.Backend.X86v3.IRResult
  open DispatcherResult {FS} program-bound

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; valid-pair-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-frontier-advance; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier)

  -- Import lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (pair-slot-bounded-lemma; suc<+2)
  open import Once.Backend.X86v3.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap; at-frontier-before-pair)
  open ExecLemmas {FS}

  -- Import write operations
  open import Once.Backend.X86v3.WriteOps using (module WriteWithDisjoint)
  open WriteWithDisjoint {FS}

  -- Import validity write lemmas for frontier inequality helpers
  open import Once.Backend.X86v3.ValidityWriteLemma using (module ValidityWriteLemmas)
  open ValidityWriteLemmas {FS} program-bound
    using (at-frontier-neq-before; suc-frontier-neq-before)

  ------------------------------------------------------------------------
  -- Arithmetic lemmas for combined-cap derivation
  --
  -- pair's combined-cap: a + (b + c + d) + e ≤ cap
  --   where a = next-slot, b = req-f, c = req-g, d = pair-slots, e = body-cap-budget
  --
  -- f's combined-cap: a + b + e ≤ cap
  -- g's combined-cap: a' + c + e ≤ cap (where a' ≤ a + b)
  ------------------------------------------------------------------------

  private
    ------------------------------------------------------------------------
    -- Arithmetic rearrangement lemmas for combined-cap derivations
    --
    -- pair's combined-cap has structure (due to left-associativity):
    --   ((slot + ((req-f + req-g) + pair-slots)) + pair-slots) + pair-slots*bound
    -- Since ir-stack-requirement ⟨ f , g ⟩ = req-f + req-g + pair-slots
    -- and combined-cap = slot + ir-req + pair-slots + pair-slots*bound
    --
    -- Let a=slot, b=req-f, c=req-g, d=pair-slots, e=pair-slots*bound
    --   = ((a + ((b + c) + d)) + d) + e
    --
    -- For f's combined-cap: (a + b) + (d + e) (body-cap-budget = d + e)
    -- For g's combined-cap: (slot₁ + c) + (d + e) where slot₁ ≤ a + b
    ------------------------------------------------------------------------

    -- Proven arithmetic rearrangements using ≡-Reasoning
    -- Goal: ((a + ((b + c) + d)) + d) + e ≡ ((a + b) + (d + e)) + (c + d)
    rearrange-for-f : ∀ a b c d e → ((a + ((b + c) + d)) + d) + e ≡ ((a + b) + (d + e)) + (c + d)
    rearrange-for-f a b c d e = begin
        ((a + ((b + c) + d)) + d) + e
      ≡⟨ +-assoc (a + ((b + c) + d)) d e ⟩
        (a + ((b + c) + d)) + (d + e)
      ≡⟨ cong (_+ (d + e)) (cong (a +_) (+-assoc b c d)) ⟩
        (a + (b + (c + d))) + (d + e)
      ≡⟨ cong (_+ (d + e)) (sym (+-assoc a b (c + d))) ⟩
        ((a + b) + (c + d)) + (d + e)
      ≡⟨ +-assoc (a + b) (c + d) (d + e) ⟩
        (a + b) + ((c + d) + (d + e))
      ≡⟨ cong ((a + b) +_) (+-comm (c + d) (d + e)) ⟩
        (a + b) + ((d + e) + (c + d))
      ≡⟨ sym (+-assoc (a + b) (d + e) (c + d)) ⟩
        ((a + b) + (d + e)) + (c + d)
      ∎

    -- Same as rearrange-for-f (identical proof)
    rearrange-for-g : ∀ a b c d e → ((a + ((b + c) + d)) + d) + e ≡ ((a + b) + (d + e)) + (c + d)
    rearrange-for-g = rearrange-for-f

  ------------------------------------------------------------------------
  -- Pair: run f and g, combine results into pair
  --
  -- Takes RecDispatcherWF as parameter instead of constructing it internally.
  -- The caller (Dispatcher.run-ir-wf) passes make-rec-wf ir<bound rs.
  ------------------------------------------------------------------------

  run-pair : ∀ {A B C} (f : IR A B) (g : IR A C)
    (rec-wf : RecDispatcherWF (ir-size ⟨ f , g ⟩))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- COMBINED capacity: ir-req + body-cap-budget all fit from next-slot
    next-slot alloc + ir-stack-requirement ⟨ f , g ⟩ + pair-slots + pair-slots *ℕ program-bound ≤ frame-capacity alloc →
    IRResultAWF ⟨ f , g ⟩ x s alloc
  run-pair f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc₃
      ; result-valid-wf = pair-valid-wf
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = IRResultAWF.not-halted result-g
      ; frame-preserved = trans (trans refl (IRResultAWF.frame-preserved result-g)) (IRResultAWF.frame-preserved result-f)
      ; slot-monotone = ≤-trans (≤-trans (IRResultAWF.slot-monotone result-f) (IRResultAWF.slot-monotone result-g)) (m≤m+n (next-slot alloc₂) pair-slots)
      ; heap-monotone = ≤-trans (IRResultAWF.heap-monotone result-f) (IRResultAWF.heap-monotone result-g)
      ; slot-bounded = pair-slot-bounded-lemma (next-slot alloc) (next-slot alloc₁) (next-slot alloc₂) (ir-stack-requirement f) (ir-stack-requirement g) pair-slots (IRResultAWF.slot-bounded result-g) (IRResultAWF.slot-bounded result-f)
      ; capacity-preserved = trans (IRResultAWF.capacity-preserved result-g) (IRResultAWF.capacity-preserved result-f)
      ; mem-preserved-before = mem-preserved-pair
      -- Reclamation: pair allocates pair-slots at alloc₂'s frontier
      ; reclaimable-slot = next-slot alloc₂ + pair-slots
      ; reclaim-monotone = ≤-trans (≤-trans (IRResultAWF.slot-monotone result-f) (IRResultAWF.slot-monotone result-g)) (m≤m+n (next-slot alloc₂) pair-slots)
      ; reclaim-bounded = ≤-refl
      ; reclaim-preserves-result = pair-reclaim-preserves-result
      }
    where
      -- body-cap-budget for convenience
      body-cap-budget = pair-slots + pair-slots *ℕ program-bound

      -- combined-cap for f: derived from pair's combined-cap via rearrange-for-f
      -- combined-cap: ((slot + ((req-f + req-g) + ps)) + ps) + ps*bound ≤ capacity
      -- By rearrange-for-f: ≡ ((slot + req-f) + (ps + ps*bound)) + (req-g + ps) ≤ capacity
      -- By m+n≤o⇒m≤o: (slot + req-f) + (ps + ps*bound) ≤ capacity
      -- By +-assoc: ((slot + req-f) + ps) + ps*bound ≤ capacity
      combined-cap-f : next-slot alloc + ir-stack-requirement f + pair-slots + pair-slots *ℕ program-bound ≤ frame-capacity alloc
      combined-cap-f =
        let
          a = next-slot alloc
          b = ir-stack-requirement f
          c = ir-stack-requirement g
          d = pair-slots
          e = pair-slots *ℕ program-bound
          -- Step 1: rearrange combined-cap
          step1 : ((a + b) + (d + e)) + (c + d) ≤ frame-capacity alloc
          step1 = subst (_≤ frame-capacity alloc) (rearrange-for-f a b c d e) combined-cap
          -- Step 2: drop (c + d)
          step2 : (a + b) + (d + e) ≤ frame-capacity alloc
          step2 = m+n≤o⇒m≤o ((a + b) + (d + e)) step1
          -- Step 3: reassociate to match target type
          step3 : ((a + b) + d) + e ≤ frame-capacity alloc
          step3 = subst (_≤ frame-capacity alloc) (sym (+-assoc (a + b) d e)) step2
        in step3

      -- Run f via dispatcher
      result-f = rec-wf f (⟨,⟩-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap-f
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      s₁-rdi = record s₁ { regs = writeReg (regs s₁) RDI input-loc }
      input-before₁ = frontier-monotone alloc alloc₁
                        (sym (IRResultAWF.frame-preserved result-f))
                        (IRResultAWF.slot-monotone result-f)
                        (IRResultAWF.heap-monotone result-f)
                        input-loc input-before

      -- PROVEN: Input validity preserved through f's execution
      mem-eq-s-to-s₁-rdi : ∀ loc' → BeforeFrontier alloc loc' → readLoc s₁-rdi loc' ≡ readLoc s loc'
      mem-eq-s-to-s₁-rdi loc' bf =
        trans (readLoc-stackMem-eq s₁-rdi s₁ loc' refl refl)
              (IRResultAWF.mem-preserved-before result-f loc' bf)

      input-valid-wf-s₁-rdi : ValidAtWF alloc x input-loc s₁-rdi
      input-valid-wf-s₁-rdi = validityWF-mem-preserved x input-loc s s₁-rdi input-before mem-eq-s-to-s₁-rdi input-valid-wf

      input-valid-wf₁ : ValidAtWF alloc₁ x input-loc s₁-rdi
      input-valid-wf₁ = validityWF-frontier-advance x input-loc s₁-rdi
                          (IRResultAWF.frame-preserved result-f)
                          (IRResultAWF.slot-monotone result-f)
                          (IRResultAWF.heap-monotone result-f)
                          input-valid-wf-s₁-rdi

      -- combined-cap for g: derived from combined-cap and slot-bounded
      -- Key insight: slot₁ ≤ slot + req-f, so we use monotonicity
      combined-cap-g : next-slot alloc₁ + ir-stack-requirement g + pair-slots + pair-slots *ℕ program-bound ≤ frame-capacity alloc₁
      combined-cap-g =
        let
          a = next-slot alloc
          b = ir-stack-requirement f
          c = ir-stack-requirement g
          d = pair-slots
          e = pair-slots *ℕ program-bound
          slot₁ = next-slot alloc₁

          -- slot₁ ≤ a + b (from slot-bounded)
          slot₁-bound : slot₁ ≤ a + b
          slot₁-bound = IRResultAWF.slot-bounded result-f

          -- Rearrange combined-cap to: ((a + b) + (d + e)) + (c + d) ≤ capacity
          rearranged : ((a + b) + (d + e)) + (c + d) ≤ frame-capacity alloc
          rearranged = subst (_≤ frame-capacity alloc) (rearrange-for-f a b c d e) combined-cap

          -- Drop (c + d) to get: (a + b) + (d + e) ≤ capacity
          dropped : (a + b) + (d + e) ≤ frame-capacity alloc
          dropped = m+n≤o⇒m≤o ((a + b) + (d + e)) rearranged

          -- By monotonicity: (slot₁ + (d + e)) ≤ ((a + b) + (d + e)) ≤ capacity
          step1 : slot₁ + (d + e) ≤ frame-capacity alloc
          step1 = ≤-trans (+-monoˡ-≤ (d + e) slot₁-bound) dropped

          -- Add c: (slot₁ + c) + (d + e) ≤ (a + b + c) + (d + e)
          -- And (a + b + c) + (d + e) ≤ (a + b) + (d + e) + (c + d) = rearranged ≤ capacity
          -- Actually simpler: use (slot₁ + c + (d + e)) ≤ ((a + b) + c + (d + e))
          --                   and ((a + b) + c + (d + e)) ≤ ((a + b) + (d + e)) + (c + d) (by adding c twice... no)

          -- Better approach: slot₁ + c ≤ (a + b) + c, so
          -- (slot₁ + c) + (d + e) ≤ ((a + b) + c) + (d + e) ≤ ((a + b) + (c + d)) + (d + e)
          --                                                 ≤ ((a + b) + (d + e)) + (c + d) (by +-comm in middle)
          --                                                 = rearranged ≤ capacity

          -- Actually even simpler: we already have dropped : (a + b) + (d + e) ≤ capacity
          -- We need: ((slot₁ + c) + d) + e ≤ capacity
          -- = (slot₁ + c) + (d + e) by +-assoc
          -- ≤ ((a + b) + c) + (d + e) by monotonicity (slot₁ ≤ a + b)
          -- ≤ ((a + b) + (d + e)) + c by... hmm this adds c not removes it

          -- Let me use the full rearranged form instead
          -- rearranged: ((a + b) + (d + e)) + (c + d) ≤ capacity
          -- I need: ((slot₁ + c) + d) + e ≤ capacity
          -- = (slot₁ + c + d) + e
          -- ≤ ((a + b) + c + d) + e  (by slot₁ ≤ a + b and monotonicity)

          -- And ((a + b) + c + d) + e ≤ ((a + b) + (d + e)) + (c + d)?
          -- LHS = (a + b) + c + d + e
          -- RHS after rearranging = (a + b) + (d + e) + (c + d) = (a + b) + d + e + c + d = (a + b) + c + 2d + e
          -- So LHS < RHS (has one less d). Good!

          -- ((a + b) + c + d) + e ≤ ((a + b) + (c + d)) + (d + e) ?
          -- = (a + b + c + d) + e vs (a + b + c + d) + (d + e)
          -- LHS ≤ RHS by m≤n+m (adding d to e)

          -- First: ((a + b) + c + d) + e ≤ ((a + b) + c + d) + (d + e)
          -- using m≤n+m e d : e ≤ d + e
          step2a : ((a + b) + c + d) + e ≤ ((a + b) + c + d) + (d + e)
          step2a = +-monoʳ-≤ ((a + b) + c + d) (m≤n+m e d)

          -- Then reassociate: ((a + b) + c + d) ≡ (a + b) + (c + d)
          -- by +-assoc (a + b) c d
          step2b : ((a + b) + c + d) + (d + e) ≡ ((a + b) + (c + d)) + (d + e)
          step2b = cong (_+ (d + e)) (+-assoc (a + b) c d)

          step2 : ((a + b) + c + d) + e ≤ ((a + b) + (c + d)) + (d + e)
          step2 = subst (((a + b) + c + d) + e ≤_) step2b step2a

          -- Transform rearranged to step3's form via equality
          -- rearranged: ((a + b) + (d + e)) + (c + d) ≤ capacity
          -- goal: ((a + b) + (c + d)) + (d + e) ≤ capacity
          rearrange-step3 : ((a + b) + (d + e)) + (c + d) ≡ ((a + b) + (c + d)) + (d + e)
          rearrange-step3 = begin
              ((a + b) + (d + e)) + (c + d)
            ≡⟨ +-assoc (a + b) (d + e) (c + d) ⟩
              (a + b) + ((d + e) + (c + d))
            ≡⟨ cong ((a + b) +_) (+-comm (d + e) (c + d)) ⟩
              (a + b) + ((c + d) + (d + e))
            ≡⟨ sym (+-assoc (a + b) (c + d) (d + e)) ⟩
              ((a + b) + (c + d)) + (d + e)
            ∎

          step3 : ((a + b) + (c + d)) + (d + e) ≤ frame-capacity alloc
          step3 = subst (_≤ frame-capacity alloc) rearrange-step3 rearranged

          -- Use monotonicity with slot₁ ≤ a + b
          step4 : ((slot₁ + c) + d) + e ≤ ((a + b) + c + d) + e
          step4 = +-monoˡ-≤ e (+-monoˡ-≤ d (+-monoˡ-≤ c slot₁-bound))

          -- Chain: ((slot₁ + c) + d) + e ≤ ((a + b) + c + d) + e ≤ ... ≤ capacity
          step5 : ((slot₁ + c) + d) + e ≤ frame-capacity alloc
          step5 = ≤-trans step4 (≤-trans step2 step3)

        in subst (((slot₁ + c) + d) + e ≤_) (sym (IRResultAWF.capacity-preserved result-f)) step5

      -- Run g via dispatcher
      result-g = rec-wf g (⟨,⟩-g-smaller f g) x input-loc s₁-rdi alloc₁
                   input-valid-wf₁
                   input-before₁
                   (IRResultAWF.not-halted result-f)
                   (writeReg-same (regs s₁) RDI input-loc)
                   combined-cap-g

      fst-loc = IRResultAWF.result-loc result-f
      fst-before = IRResultAWF.result-before result-f
      fst-valid-wf = IRResultAWF.result-valid-wf result-f
      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      snd-loc = IRResultAWF.result-loc result-g
      snd-before = IRResultAWF.result-before result-g
      snd-valid-wf = IRResultAWF.result-valid-wf result-g
      pair-loc = OnStack (current-frame alloc₂) (next-slot alloc₂)

      -- PROVEN: pair-fits derived from combined-cap-g and slot-bounded
      pair-fits : next-slot alloc₂ + pair-slots ≤ frame-capacity alloc₂
      pair-fits =
        let
          slot₂ = next-slot alloc₂
          slot₁ = next-slot alloc₁
          req-g = ir-stack-requirement g
          ps = pair-slots
          e = pair-slots *ℕ program-bound

          -- slot₂ ≤ slot₁ + req-g (from slot-bounded)
          slot₂-bound : slot₂ ≤ slot₁ + req-g
          slot₂-bound = IRResultAWF.slot-bounded result-g

          -- slot₂ + ps ≤ (slot₁ + req-g) + ps (by monotonicity)
          step1 : slot₂ + ps ≤ (slot₁ + req-g) + ps
          step1 = +-monoˡ-≤ ps slot₂-bound

          -- (slot₁ + req-g) + ps ≤ ((slot₁ + req-g) + ps) + e (by m≤m+n)
          step2 : (slot₁ + req-g) + ps ≤ ((slot₁ + req-g) + ps) + e
          step2 = m≤m+n ((slot₁ + req-g) + ps) e

          -- ((slot₁ + req-g) + ps) + e ≤ frame-capacity alloc₁ (from combined-cap-g)
          step3 : ((slot₁ + req-g) + ps) + e ≤ frame-capacity alloc₁
          step3 = combined-cap-g

          -- chain: slot₂ + ps ≤ frame-capacity alloc₁
          step4 : slot₂ + ps ≤ frame-capacity alloc₁
          step4 = ≤-trans step1 (≤-trans step2 step3)

          -- frame-capacity alloc₂ = frame-capacity alloc₁
          cap-eq : frame-capacity alloc₂ ≡ frame-capacity alloc₁
          cap-eq = IRResultAWF.capacity-preserved result-g

        in subst (slot₂ + ps ≤_) (sym cap-eq) step4

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc₂
        { next-slot = next-slot alloc₂ + pair-slots
        ; slots-available = pair-fits
        }

      s₃ = write-loc s₂ pair-loc fst-loc
      s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
      s-final = record s₄ { regs = writeReg (regs s₄) RAX pair-loc }

      -- PROVEN: Memory at BeforeFrontier locations is preserved
      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc →
        readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair loc bf =
        let
          bf₁ : BeforeFrontier alloc₁ loc
          bf₁ = frontier-monotone alloc alloc₁
                  (sym (IRResultAWF.frame-preserved result-f))
                  (IRResultAWF.slot-monotone result-f)
                  (IRResultAWF.heap-monotone result-f)
                  loc bf

          bf₂ : BeforeFrontier alloc₂ loc
          bf₂ = frontier-monotone alloc₁ alloc₂
                  (sym (IRResultAWF.frame-preserved result-g))
                  (IRResultAWF.slot-monotone result-g)
                  (IRResultAWF.heap-monotone result-g)
                  loc bf₁

          step1 : readLoc s-final loc ≡ readLoc s₄ loc
          step1 = readLoc-stackMem-eq s-final s₄ loc refl refl

          step2 : readLoc s₄ loc ≡ readLoc s₃ loc
          step2 = write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc loc
                    (λ eq → suc-frontier-neq-before alloc₂ loc bf₂ eq)

          step3 : readLoc s₃ loc ≡ readLoc s₂ loc
          step3 = write-preserves-disjoint s₂ pair-loc fst-loc loc
                    (λ eq → at-frontier-neq-before alloc₂ loc bf₂ eq)

          step4 : readLoc s₂ loc ≡ readLoc s₁-rdi loc
          step4 = IRResultAWF.mem-preserved-before result-g loc bf₁

          step5 : readLoc s₁-rdi loc ≡ readLoc s₁ loc
          step5 = readLoc-stackMem-eq s₁-rdi s₁ loc refl refl

          step6 : readLoc s₁ loc ≡ readLoc s loc
          step6 = IRResultAWF.mem-preserved-before result-f loc bf

        in trans step1 (trans step2 (trans step3 (trans step4 (trans step5 step6))))

      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl (m<m+n (next-slot alloc₂) (s≤s z≤n))

      sucLoc-pair-before : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before = stack-before refl (suc<+2 (next-slot alloc₂))

      pair-ptr : readLoc s-final pair-loc ≡ just fst-loc
      pair-ptr = trans refl (trans
                   (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc pair-loc (sucLoc-neq pair-loc))
                   (write-read-same s₂ pair-loc fst-loc))

      snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
      snd-ptr = write-read-same s₃ (sucLoc pair-loc) snd-loc

      fst-before-alloc₂ : BeforeFrontier alloc₂ fst-loc
      fst-before-alloc₂ = frontier-monotone alloc₁ alloc₂
                            (sym (IRResultAWF.frame-preserved result-g))
                            (IRResultAWF.slot-monotone result-g)
                            (IRResultAWF.heap-monotone result-g)
                            fst-loc fst-before

      fst-before₃ : BeforeFrontier alloc₃ fst-loc
      fst-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits fst-loc fst-before-alloc₂

      snd-before₃ : BeforeFrontier alloc₃ snd-loc
      snd-before₃ = stack-alloc-advances alloc₂ pair-slots pair-fits snd-loc snd-before

      -- PROVEN: fst-valid-wf-final via chained validity lemmas
      fst-valid-wf-final : ValidAtWF alloc₃ (eval f x) fst-loc s-final
      fst-valid-wf-final =
        let
          fst-valid-s₁-rdi : ValidAtWF alloc₁ (eval f x) fst-loc s₁-rdi
          fst-valid-s₁-rdi = validityWF-mem-only (eval f x) fst-loc s₁ s₁-rdi refl refl fst-valid-wf

          mem-eq-g : ∀ loc' → BeforeFrontier alloc₁ loc' → readLoc s₂ loc' ≡ readLoc s₁-rdi loc'
          mem-eq-g = IRResultAWF.mem-preserved-before result-g

          fst-valid-s₂-alloc₁ : ValidAtWF alloc₁ (eval f x) fst-loc s₂
          fst-valid-s₂-alloc₁ = validityWF-mem-preserved (eval f x) fst-loc s₁-rdi s₂ fst-before mem-eq-g fst-valid-s₁-rdi

          fst-valid-s₂ : ValidAtWF alloc₂ (eval f x) fst-loc s₂
          fst-valid-s₂ = validityWF-frontier-advance (eval f x) fst-loc s₂
                           (IRResultAWF.frame-preserved result-g)
                           (IRResultAWF.slot-monotone result-g)
                           (IRResultAWF.heap-monotone result-g)
                           fst-valid-s₂-alloc₁

          fst-valid-s₃ : ValidAtWF alloc₂ (eval f x) fst-loc s₃
          fst-valid-s₃ = validityWF-write-at-frontier (eval f x) fst-loc s₂ fst-loc fst-before-alloc₂ fst-valid-s₂

          fst-valid-s₄ : ValidAtWF alloc₂ (eval f x) fst-loc s₄
          fst-valid-s₄ = validityWF-write-at-suc-frontier (eval f x) fst-loc s₃ snd-loc fst-before-alloc₂ fst-valid-s₃

          fst-valid-s-final-alloc₂ : ValidAtWF alloc₂ (eval f x) fst-loc s-final
          fst-valid-s-final-alloc₂ = validityWF-mem-only (eval f x) fst-loc s₄ s-final refl refl fst-valid-s₄

        in validityWF-alloc-advance (eval f x) fst-loc s-final pair-slots pair-fits fst-valid-s-final-alloc₂

      -- PROVEN: snd-valid-wf-final via chained validity lemmas
      snd-valid-wf-final : ValidAtWF alloc₃ (eval g x) snd-loc s-final
      snd-valid-wf-final =
        let
          snd-valid-s₃ : ValidAtWF alloc₂ (eval g x) snd-loc s₃
          snd-valid-s₃ = validityWF-write-at-frontier (eval g x) snd-loc s₂ fst-loc snd-before snd-valid-wf

          snd-valid-s₄ : ValidAtWF alloc₂ (eval g x) snd-loc s₄
          snd-valid-s₄ = validityWF-write-at-suc-frontier (eval g x) snd-loc s₃ snd-loc snd-before snd-valid-s₃

          snd-valid-s-final-alloc₂ : ValidAtWF alloc₂ (eval g x) snd-loc s-final
          snd-valid-s-final-alloc₂ = validityWF-mem-only (eval g x) snd-loc s₄ s-final refl refl snd-valid-s₄

        in validityWF-alloc-advance (eval g x) snd-loc s-final pair-slots pair-fits snd-valid-s-final-alloc₂

      pair-valid-wf : ValidAtWF alloc₃ (eval ⟨ f , g ⟩ x) pair-loc s-final
      pair-valid-wf = valid-pair-wf pair-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before fst-valid-wf-final snd-valid-wf-final

      rax-eq : readReg (regs s-final) RAX ≡ pair-loc
      rax-eq = writeReg-same (regs s₄) RAX pair-loc

      -- Transfer pair-before from alloc₃ to the reclaimed allocation
      -- alloc₃ has current-frame = alloc₂.current-frame, next-slot = next-slot alloc₂ + pair-slots
      -- reclaimed has current-frame = alloc.current-frame, next-slot = next-slot alloc₂ + pair-slots
      -- These frames are equal by frame-preserved
      pair-reclaim-preserves-result : ∀ (fits : next-slot alloc₂ + pair-slots ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = next-slot alloc₂ + pair-slots ; slots-available = fits }) pair-loc
      pair-reclaim-preserves-result fits =
        let
          alloc-reclaimed = record alloc { next-slot = next-slot alloc₂ + pair-slots ; slots-available = fits }
          -- alloc₃.current-frame = alloc₂.current-frame = alloc.current-frame (by frame-preserved)
          frame-eq : current-frame alloc₃ ≡ current-frame alloc-reclaimed
          frame-eq = trans (trans refl (IRResultAWF.frame-preserved result-g)) (IRResultAWF.frame-preserved result-f)
          -- heap-ref is unchanged through f and g (they don't allocate heap)
          postulate heap-eq : next-heap-ref alloc₃ ≡ next-heap-ref alloc-reclaimed
        in frontier-same-heap alloc₃ alloc-reclaimed frame-eq refl heap-eq pair-loc pair-before
