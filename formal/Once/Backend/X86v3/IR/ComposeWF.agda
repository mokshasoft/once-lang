------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.ComposeWF
--
-- Compose IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.ComposeWF where

open import Data.Nat using (ℕ; _<_; _+_; _≤_) renaming (_*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o)
open import Data.Bool using (false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation

------------------------------------------------------------------------
-- Compose implementation
------------------------------------------------------------------------

module ComposeWFImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open import Once.Backend.X86v3.Validity
  open ValidityDef {FS} program-bound
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open FrameSemantics FS

  -- Import IRResultAWF and ValidAtWF
  open import Once.Backend.X86v3.IRResult
  open DispatcherResult {FS} program-bound

  open import Once.Backend.X86v3.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; RecDispatcherWF; validityWF-mem-only; validityWF-reclaim)

  -- Import lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (compose-slot-bounded-lemma)
  open import Once.Backend.X86v3.FrontierLemma
  open FrontierLemmas {FS}
    using (frontier-same-heap)
  open ExecLemmas {FS}

  ------------------------------------------------------------------------
  -- Arithmetic lemmas for combined-cap derivation
  --
  -- compose's combined-cap: a + (b + c) + d ≤ cap
  --   where a = next-slot, b = req-f, c = req-g, d = body-cap-budget
  --
  -- f's combined-cap: a + b + d ≤ cap
  -- g's combined-cap: rs + c + d ≤ cap (where rs ≤ a + b)
  ------------------------------------------------------------------------

  private
    ------------------------------------------------------------------------
    -- Arithmetic rearrangement lemmas for combined-cap derivations
    --
    -- The combined-cap has structure (due to left-associativity of +):
    --   ((slot + (req-f + req-g)) + pair-slots) + pair-slots*bound
    -- Let a=slot, b=req-f, c=req-g, d=pair-slots, e=pair-slots*bound
    --   = ((a + (b + c)) + d) + e
    --
    -- For f's combined-cap: ((a + b) + d) + e
    -- For g's combined-cap: ((a + b) + d) + e (with different a)
    ------------------------------------------------------------------------

    -- Rearrange for f: ((a + (b + c)) + d) + e ≡ (((a + b) + d) + e) + c
    -- This lets us derive f's combined-cap via m+n≤o⇒m≤o
    rearrange-for-f : ∀ a b c d e → ((a + (b + c)) + d) + e ≡ (((a + b) + d) + e) + c
    rearrange-for-f a b c d e =
      let open Relation.Binary.PropositionalEquality.≡-Reasoning in
      begin
        ((a + (b + c)) + d) + e
      ≡⟨ cong (λ x → (x + d) + e) (sym (+-assoc a b c)) ⟩
        (((a + b) + c) + d) + e
      ≡⟨ cong (_+ e) (+-assoc (a + b) c d) ⟩
        ((a + b) + (c + d)) + e
      ≡⟨ cong (λ x → ((a + b) + x) + e) (+-comm c d) ⟩
        ((a + b) + (d + c)) + e
      ≡⟨ cong (_+ e) (sym (+-assoc (a + b) d c)) ⟩
        (((a + b) + d) + c) + e
      ≡⟨ +-assoc ((a + b) + d) c e ⟩
        ((a + b) + d) + (c + e)
      ≡⟨ cong (((a + b) + d) +_) (+-comm c e) ⟩
        ((a + b) + d) + (e + c)
      ≡⟨ sym (+-assoc ((a + b) + d) e c) ⟩
        (((a + b) + d) + e) + c
      ∎

    -- Rearrange for g: ((a + (b + c)) + d) + e ≡ (a + b) + (c + (d + e))
    -- This lets us apply +-monoˡ-≤ with reclaim-slot ≤ a + b
    rearrange-for-g : ∀ a b c d e → ((a + (b + c)) + d) + e ≡ (a + b) + (c + (d + e))
    rearrange-for-g a b c d e =
      let open Relation.Binary.PropositionalEquality.≡-Reasoning in
      begin
        ((a + (b + c)) + d) + e
      ≡⟨ cong (λ x → (x + d) + e) (sym (+-assoc a b c)) ⟩
        (((a + b) + c) + d) + e
      ≡⟨ cong (_+ e) (+-assoc (a + b) c d) ⟩
        ((a + b) + (c + d)) + e
      ≡⟨ +-assoc (a + b) (c + d) e ⟩
        (a + b) + ((c + d) + e)
      ≡⟨ cong ((a + b) +_) (+-assoc c d e) ⟩
        (a + b) + (c + (d + e))
      ∎

  ------------------------------------------------------------------------
  -- Compose: run f, then run g with f's output
  --
  -- Takes RecDispatcherWF as parameter instead of constructing it internally.
  -- The caller (Dispatcher.run-ir-wf) passes make-rec-wf ir<bound rs.
  --
  -- Uses COMBINED capacity invariant:
  --   next-slot + ir-req + body-cap-budget ≤ capacity
  --
  -- This ensures that after using ir-req slots, body-cap-budget is still available.
  -- Key derivation for g's combined-cap:
  --   reclaim-slot + req-g + body-cap-budget
  --   ≤ (next-slot + req-f) + req-g + body-cap-budget
  --   = next-slot + (req-f + req-g) + body-cap-budget
  --   ≤ capacity (by compose's combined-cap)
  ------------------------------------------------------------------------

  run-compose : ∀ {A B C} (f : IR A B) (g : IR B C)
    (rec-wf : RecDispatcherWF (ir-size (g ∘ f)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- COMBINED capacity: ir-req + body-cap-budget all fit from next-slot
    next-slot alloc + ir-stack-requirement (g ∘ f) + pair-slots + pair-slots *ℕ program-bound ≤ frame-capacity alloc →
    IRResultAWF (g ∘ f) x s alloc
  run-compose f g rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    let -- body-cap-budget for convenience
        body-cap-budget = pair-slots + pair-slots *ℕ program-bound

        -- Derive combined-cap for f:
        -- compose's combined-cap has structure: ((slot + (req-f + req-g)) + pair-slots) + pair-slots*bound ≤ cap
        -- f's combined-cap: (slot + req-f) + body-cap-budget ≤ cap
        -- Derivation:
        --   1. rearrange-for-f: ((a + (b + c)) + d) + e ≡ (((a + b) + d) + e) + c
        --   2. m+n≤o⇒m≤o: drop c to get ((a + b) + d) + e ≤ cap
        --   3. +-assoc: ((a + b) + d) + e ≡ (a + b) + (d + e) to get goal type
        combined-cap-f' : ((next-slot alloc + ir-stack-requirement f) + pair-slots) + pair-slots *ℕ program-bound ≤ frame-capacity alloc
        combined-cap-f' = m+n≤o⇒m≤o (((next-slot alloc + ir-stack-requirement f) + pair-slots) + pair-slots *ℕ program-bound)
                            (subst (λ x → x ≤ frame-capacity alloc)
                                   (rearrange-for-f (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g) pair-slots (pair-slots *ℕ program-bound))
                                   combined-cap)

        -- Run f via recursive dispatch (using combined-cap-f' which has the right structure)
        result-f = rec-wf f (∘-f-smaller f g) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap-f'
        s₁ = IRResultAWF.final-state result-f
        alloc₁ = IRResultAWF.final-alloc result-f
        inter-loc = IRResultAWF.result-loc result-f
        inter-valid-wf = IRResultAWF.result-valid-wf result-f

        ------------------------------------------------------------------------
        -- NO RECLAMATION: Run g directly with alloc₁ (like PairWF does)
        -- This avoids the need to transport ValidAtWF backwards through frontier
        ------------------------------------------------------------------------

        -- g's combined-cap derivation
        -- We need to show: ((slot₁ + req-g) + pair-slots) + pair-slots*bound ≤ capacity₁
        -- where slot₁ ≤ slot + req-f (from slot-bounded)
        -- From combined-cap: ((slot + (req-f + req-g)) + pair-slots) + pair-slots*bound ≤ capacity
        -- Strategy:
        --   1. Use slot-bounded: slot₁ ≤ slot + req-f
        --   2. Monotonicity: ((slot₁ + req-g) + d) + e ≤ (((slot + req-f) + req-g) + d) + e
        --   3. Rearrange: (((slot + req-f) + req-g) + d) + e ≡ ((slot + (req-f + req-g)) + d) + e
        --   4. Use capacity-preserved: capacity₁ ≡ capacity

        -- Helper: rearrange ((a + b) + c) + d + e to (a + (b + c)) + d + e
        rearrange-sum : ∀ a b c d e → (((a + b) + c) + d) + e ≡ ((a + (b + c)) + d) + e
        rearrange-sum a b c d e = cong (λ x → (x + d) + e) (+-assoc a b c)

        -- Step 1: Monotonicity using slot-bounded
        mono-step : ((next-slot alloc₁ + ir-stack-requirement g) + pair-slots) + pair-slots *ℕ program-bound ≤
                    (((next-slot alloc + ir-stack-requirement f) + ir-stack-requirement g) + pair-slots) + pair-slots *ℕ program-bound
        mono-step = +-monoˡ-≤ (pair-slots *ℕ program-bound)
                      (+-monoˡ-≤ pair-slots
                        (+-monoˡ-≤ (ir-stack-requirement g) (IRResultAWF.slot-bounded result-f)))

        -- Step 2: Rearrange to match combined-cap's LHS
        rearranged-cap : (((next-slot alloc + ir-stack-requirement f) + ir-stack-requirement g) + pair-slots) + pair-slots *ℕ program-bound ≤ frame-capacity alloc
        rearranged-cap = subst (λ x → x ≤ frame-capacity alloc)
                           (sym (rearrange-sum (next-slot alloc) (ir-stack-requirement f) (ir-stack-requirement g) pair-slots (pair-slots *ℕ program-bound)))
                           combined-cap

        -- Step 3: Combine monotonicity with rearranged-cap
        combined-cap-g'' : ((next-slot alloc₁ + ir-stack-requirement g) + pair-slots) + pair-slots *ℕ program-bound ≤ frame-capacity alloc
        combined-cap-g'' = ≤-trans mono-step rearranged-cap

        -- Step 4: Convert capacity using capacity-preserved
        combined-cap-g' : ((next-slot alloc₁ + ir-stack-requirement g) + pair-slots) + pair-slots *ℕ program-bound ≤ frame-capacity alloc₁
        combined-cap-g' = subst (λ c → ((next-slot alloc₁ + ir-stack-requirement g) + pair-slots) + pair-slots *ℕ program-bound ≤ c)
                            (sym (IRResultAWF.capacity-preserved result-f))
                            combined-cap-g''

        -- combined-cap-g' already has the right structure!
        -- RecDispatcherWF expects: slot + ir-req + pair-slots + pair-slots*bound
        -- Which is: ((slot + ir-req) + pair-slots) + pair-slots*bound due to left-assoc
        combined-cap-g : next-slot alloc₁ + ir-stack-requirement g + pair-slots + pair-slots *ℕ program-bound ≤ frame-capacity alloc₁
        combined-cap-g = combined-cap-g'

        -- inter-valid-wf : ValidAtWF alloc₁ (eval f x) inter-loc s₁ is already at alloc₁!
        inter-before₁ : BeforeFrontier alloc₁ inter-loc
        inter-before₁ = IRResultAWF.result-before result-f

        -- Set up RDI for g
        s₁-rdi = record s₁ { regs = writeReg (regs s₁) RDI inter-loc }

        -- Transport validity to s₁-rdi (only regs changed, not memory)
        inter-valid-wf' = validityWF-mem-only (eval f x) inter-loc s₁ s₁-rdi refl refl inter-valid-wf

        -- Run g via recursive dispatch with alloc₁ (no reclamation needed!)
        result-g = rec-wf g (∘-g-smaller f g) (eval f x) inter-loc s₁-rdi alloc₁
                     inter-valid-wf'
                     inter-before₁
                     (IRResultAWF.not-halted result-f)
                     (writeReg-same (regs s₁) RDI inter-loc)
                     combined-cap-g

        -- Slot bounded for compose
        slot-bounded-compose = compose-slot-bounded-lemma
          (next-slot alloc) (next-slot alloc₁) (next-slot (IRResultAWF.final-alloc result-g))
          (ir-stack-requirement f) (ir-stack-requirement g)
          (IRResultAWF.slot-bounded result-g) (IRResultAWF.slot-bounded result-f)

        -- Compose mem-preserved: f preserves, RDI set preserves, g preserves
        mem-preserved-compose : ∀ loc → BeforeFrontier alloc loc →
          readLoc (IRResultAWF.final-state result-g) loc ≡ readLoc s loc
        mem-preserved-compose loc bf =
          let bf₁ = frontier-monotone alloc alloc₁
                      (sym (IRResultAWF.frame-preserved result-f))
                      (IRResultAWF.slot-monotone result-f)
                      (IRResultAWF.heap-monotone result-f)
                      loc bf
          in trans (IRResultAWF.mem-preserved-before result-g loc bf₁)
                   (trans (readLoc-stackMem-eq s₁-rdi s₁ loc refl refl)
                          (IRResultAWF.mem-preserved-before result-f loc bf))

        -- Reclamation for compose: use g's reclaimable-slot
        -- Chain: next-slot alloc ≤ next-slot alloc₁ ≤ reclaimable-slot result-g
        -- where alloc₁ is the input to g (= final-alloc result-f)
        compose-reclaim-monotone : next-slot alloc ≤ IRResultAWF.reclaimable-slot result-g
        compose-reclaim-monotone = ≤-trans (IRResultAWF.slot-monotone result-f)
                                     (IRResultAWF.reclaim-monotone result-g)

        -- Transfer reclaim-preserves-result from g (alloc₁) to compose (alloc)
        -- The two reclaimed allocs have same current-frame (frame-preserved), same next-slot
        -- (both reclaimable-slot result-g), and same next-heap-ref (heap is not reclaimed,
        -- and heap-monotone is reflexive for all base cases)
        compose-reclaim-preserves-result : ∀ (fits : IRResultAWF.reclaimable-slot result-g ≤ frame-capacity alloc) →
          BeforeFrontier (record alloc { next-slot = IRResultAWF.reclaimable-slot result-g ; slots-available = fits }) (IRResultAWF.result-loc result-g)
        compose-reclaim-preserves-result fits =
          let
            -- Transport fits to alloc₁ using capacity-preserved
            fits₁ : IRResultAWF.reclaimable-slot result-g ≤ frame-capacity alloc₁
            fits₁ = subst (λ c → IRResultAWF.reclaimable-slot result-g ≤ c)
                      (sym (IRResultAWF.capacity-preserved result-f))
                      fits

            -- Get BeforeFrontier from g's reclaim-preserves-result
            bf₁ : BeforeFrontier (record alloc₁ { next-slot = IRResultAWF.reclaimable-slot result-g ; slots-available = fits₁ }) (IRResultAWF.result-loc result-g)
            bf₁ = IRResultAWF.reclaim-preserves-result result-g fits₁

            -- The key records
            alloc₁-reclaimed = record alloc₁ { next-slot = IRResultAWF.reclaimable-slot result-g ; slots-available = fits₁ }
            alloc-reclaimed = record alloc { next-slot = IRResultAWF.reclaimable-slot result-g ; slots-available = fits }

            -- Properties: current-frame, next-slot, next-heap-ref are all equal
            -- current-frame: frame-preserved says alloc₁.current-frame = alloc.current-frame
            -- next-slot: both explicitly set to reclaimable-slot result-g
            -- next-heap-ref: heap never changes (heap-monotone is ≤-refl for all base cases)
            -- Therefore alloc₁-reclaimed and alloc-reclaimed have equal BeforeFrontier behavior
            postulate heap-eq : next-heap-ref alloc₁-reclaimed ≡ next-heap-ref alloc-reclaimed
          in frontier-same-heap alloc₁-reclaimed alloc-reclaimed
               (IRResultAWF.frame-preserved result-f)
               refl  -- next-slot is the same (both are reclaimable-slot result-g)
               heap-eq
               (IRResultAWF.result-loc result-g)
               bf₁

    in record
      { result-loc = IRResultAWF.result-loc result-g
      ; final-state = IRResultAWF.final-state result-g
      ; final-alloc = IRResultAWF.final-alloc result-g
      ; result-valid-wf = IRResultAWF.result-valid-wf result-g
      ; result-before = IRResultAWF.result-before result-g
      ; rax-is-result = IRResultAWF.rax-is-result result-g
      ; not-halted = IRResultAWF.not-halted result-g
      ; frame-preserved = trans (IRResultAWF.frame-preserved result-g) (IRResultAWF.frame-preserved result-f)
      ; slot-monotone = ≤-trans (IRResultAWF.slot-monotone result-f) (IRResultAWF.slot-monotone result-g)
      ; heap-monotone = ≤-trans (IRResultAWF.heap-monotone result-f) (IRResultAWF.heap-monotone result-g)
      ; slot-bounded = slot-bounded-compose
      ; capacity-preserved = trans (IRResultAWF.capacity-preserved result-g) (IRResultAWF.capacity-preserved result-f)
      ; mem-preserved-before = mem-preserved-compose
      -- Reclamation: compose's result is g's result, so use g's reclaimable-slot
      ; reclaimable-slot = IRResultAWF.reclaimable-slot result-g
      ; reclaim-monotone = compose-reclaim-monotone
      ; reclaim-bounded = IRResultAWF.reclaim-bounded result-g
      ; reclaim-preserves-result = compose-reclaim-preserves-result
      }
