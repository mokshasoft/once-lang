------------------------------------------------------------------------
-- Once.Backend.X86v3.IR.PairWF
--
-- Pair IR implementation with ValidAtWF.
-- Extracted from Dispatcher.agda to minimize the mutual block.
--
-- Takes RecDispatcherWF as parameter for recursive dispatch to f and g.
--
-- Uses LINEAR capacity formula: pair-slots * ir-size
------------------------------------------------------------------------

module Once.Backend.X86v3.IR.PairWF where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m<m+n; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; m+n≤o⇒m≤o; *-monoʳ-≤; m≤m*n; *-distribˡ-+; *-suc; n≤1+n)
open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Once.Backend.Common.FrameSemantics using (FrameSemantics)
open import Once.Backend.Common.SlotMachine
open import Once.Backend.X86v3.Types
open import Once.Backend.X86v3.IR
open import Once.Backend.X86v3.Allocation hiding (AllocMode)

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
    using (ValidAtWF; IRResultAWF; RecDispatcherWF;
           valid-pair-boxed-wf; valid-pair-unboxed-wf;
           validityWF-mem-only; validityWF-mem-preserved;
           validityWF-frontier-advance; validityWF-alloc-advance;
           validityWF-write-at-frontier; validityWF-write-at-suc-frontier;
           validityWF-with-bf-transfer)

  -- NOTE: Global capacity invariants removed - using dynamic capacity threading instead

  -- Import lemmas
  open import Once.Backend.X86v3.DispatcherArithmeticLemma
    using (suc<+2; compose-f-cap; compose-g-cap; pair-slot-bounded-lemma; pair-alloc-fits)
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

  -- Import ApplyWF for bf-same-frame-slot
  open import Once.Backend.X86v3.IR.ApplyWF
  open ApplyWFImpl {FS} program-bound
    using (bf-same-frame-slot)

  ------------------------------------------------------------------------
  -- Pair: run f and g, combine results into pair
  --
  -- Uses LINEAR capacity: pair-slots * ir-size covers ir-req + recursion
  --
  -- Key derivations (same pattern as compose):
  --   slot + pair-slots * sf ≤ slot + pair-slots * size (since sf < size)
  --   slot₁ + pair-slots * sg ≤ slot + pair-slots * size (via slot-bounded)
  --   pair allocation fits since pair-slots ≤ pair-slots * size
  ------------------------------------------------------------------------

  run-pair : ∀ {A B C} (mIn : AllocMode) (f : IR A B) (g : IR A C) (m : AllocMode)
    (rec-wf : RecDispatcherWF (ir-size (⟨ f , g ⟩ Heap)))
    (x : ⟦ A ⟧) (input-loc : ValueLocation FS)
    (s : LocState FS) (alloc : AllocState {FS}) →
    ValidAtWF mIn alloc x input-loc s →
    BeforeFrontier alloc input-loc →
    halted s ≡ false →
    readReg (regs s) RDI ≡ input-loc →
    -- Capacity using ir-stack-requirement
    next-slot alloc +ℕ ir-stack-requirement (⟨ f , g ⟩ m) ≤ frame-capacity alloc →
    IRResultAWF m (⟨ f , g ⟩ m) x s alloc  -- Output mode is the pair's AllocMode m

  -- Stack mode: unboxed inline representation (TODO: implement properly)
  run-pair {A} {B} {C} mIn f g Stack rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    postulate-run-pair-stack
    where postulate postulate-run-pair-stack : IRResultAWF Stack (⟨ f , g ⟩ Stack) x s alloc

  -- Heap mode: boxed representation (fully implemented)
  run-pair {A} {B} {C} mIn f g Heap rec-wf x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap =
    record
      { result-loc = pair-loc
      ; final-state = s-final
      ; final-alloc = alloc₃
      ; result-valid-wf = pair-valid-wf-final
      ; result-before = pair-before
      ; rax-is-result = rax-eq
      ; not-halted = not-halted-final
      ; frame-preserved = frame-preserved-pair
      ; slot-monotone = slot-monotone-pair
      ; heap-monotone = heap-monotone-pair
      ; heap-preserved = heap-preserved-pair
      ; capacity-preserved = capacity-preserved-pair
      ; mem-preserved-before = mem-preserved-pair
      ; reclaimable-slot = pair-reclaim
      ; reclaim-monotone = pair-reclaim-monotone
      ; reclaim-bounded = pair-reclaim-bounded
      ; reclaim-preserves-result = pair-reclaim-preserves
      ; reclaim-preserves-validity = pair-reclaim-preserves-validity
      ; reclaim-size-bound = pair-reclaim-size-bound
      }
    where
      -- Stack requirement abbreviations
      rf = ir-stack-requirement f
      rg = ir-stack-requirement g
      req-pair = ir-stack-requirement (⟨ f , g ⟩ Heap)
      -- Heap mode: ps = heap-type-slots (B * C) = 2 (always for boxed pairs)
      ps : ℕ
      ps = 2  -- heap-type-slots (B * C) = 2 for all B, C

      -- ps ≥ 2 is trivial for Heap mode
      ps≥2 : 2 ≤ ps
      ps≥2 = ≤-refl

      -- Derived: ps ≥ 1 from ps ≥ 2
      ps≥1 : 1 ≤ ps
      ps≥1 = s≤s z≤n

      ------------------------------------------------------------------------
      -- Derive capacity for f
      -- req-pair = rf + rg + ps
      -- So: slot + req-pair ≤ cap → slot + rf ≤ cap
      ------------------------------------------------------------------------

      -- Helper: req-pair expands to rf + rg + ps
      req-pair-eq : req-pair ≡ rf +ℕ rg +ℕ ps
      req-pair-eq = refl

      -- combined-cap rewritten: slot + rf + rg + ps ≤ cap
      combined-cap-expanded : next-slot alloc +ℕ rf +ℕ rg +ℕ ps ≤ frame-capacity alloc
      combined-cap-expanded = ⟨,⟩-capacity-for-pair f g Heap (next-slot alloc) (frame-capacity alloc) combined-cap

      -- Derive: slot + rf ≤ cap
      -- From slot + rf + rg + ps ≤ cap, extract slot + rf by removing rg + ps
      -- First, reassociate: ((slot + rf) + rg) + ps = (slot + rf) + (rg + ps)
      combined-cap-reassoc : (next-slot alloc +ℕ rf) +ℕ (rg +ℕ ps) ≤ frame-capacity alloc
      combined-cap-reassoc = subst (_≤ frame-capacity alloc) (+-assoc (next-slot alloc +ℕ rf) rg ps)
                               combined-cap-expanded

      -- Now extract slot + rf: (slot + rf) ≤ (slot + rf + rg + ps) ≤ cap
      combined-cap-f : next-slot alloc +ℕ rf ≤ frame-capacity alloc
      combined-cap-f = ≤-trans (m≤m+n (next-slot alloc +ℕ rf) (rg +ℕ ps)) combined-cap-reassoc

      -- Run f via recursive dispatch
      f-exec-result : ∃[ mOut ] IRResultAWF mOut f x s alloc
      f-exec-result = rec-wf mIn f (⟨,⟩-f-smaller f g {Heap}) x input-loc s alloc input-valid-wf input-before not-halted rdi-eq combined-cap-f
      mF = proj₁ f-exec-result
      result-f = proj₂ f-exec-result
      s₁ = IRResultAWF.final-state result-f
      alloc₁ = IRResultAWF.final-alloc result-f
      fst-loc = IRResultAWF.result-loc result-f
      fst-valid-wf = IRResultAWF.result-valid-wf result-f

      ------------------------------------------------------------------------
      -- Reclaim after f: Reset slot to reclaimable-slot
      ------------------------------------------------------------------------
      reclaim-f = IRResultAWF.reclaimable-slot result-f

      -- reclaim-f is bounded by f's stack requirement
      reclaim-f-bound : reclaim-f ≤ next-slot alloc +ℕ rf
      reclaim-f-bound = IRResultAWF.reclaim-size-bound result-f

      -- Derive that reclaim fits in capacity: reclaim-f ≤ slot + rf ≤ cap
      reclaim-f-fits : reclaim-f ≤ frame-capacity alloc
      reclaim-f-fits = ≤-trans reclaim-f-bound combined-cap-f

      -- Create reclaimed allocation
      alloc₁-reclaimed : AllocState {FS}
      alloc₁-reclaimed = record alloc
        { next-slot = reclaim-f
        ; slots-available = reclaim-f-fits
        }

      ------------------------------------------------------------------------
      -- Derive capacity for g
      ------------------------------------------------------------------------

      capacity₁-eq : frame-capacity alloc₁ ≡ frame-capacity alloc
      capacity₁-eq = IRResultAWF.capacity-preserved result-f

      -- Derive capacity for g using reclaimed allocation
      -- Chain: reclaim-f + rg ≤ slot + rf + rg ≤ slot + rf + rg + ps ≤ cap
      combined-cap-g : reclaim-f +ℕ rg ≤ frame-capacity alloc
      combined-cap-g = ≤-trans (+-monoˡ-≤ rg reclaim-f-bound)
                         (≤-trans (m≤m+n (next-slot alloc +ℕ rf +ℕ rg) ps) combined-cap-expanded)

      -- Run g via recursive dispatch WITH RECLAIMED ALLOCATION
      -- g needs same input as f, but input validity is preserved through f
      input-before₁-reclaimed : BeforeFrontier alloc₁-reclaimed input-loc
      input-before₁-reclaimed = frontier-monotone alloc alloc₁-reclaimed
                                  refl  -- frame preserved (same frame)
                                  (IRResultAWF.reclaim-monotone result-f)  -- slot ≤ reclaim-f
                                  ≤-refl  -- heap same
                                  input-loc input-before

      -- Input validity preserved through f's execution (memory at input-loc unchanged)
      -- Step 1: Memory preserved means validity preserved across state change (same alloc)
      input-valid-wf-s1 : ValidAtWF mIn alloc x input-loc s₁
      input-valid-wf-s1 = validityWF-mem-preserved x input-loc s s₁
                            input-before
                            (λ loc bf → IRResultAWF.mem-preserved-before result-f loc bf)
                            input-valid-wf

      -- Step 2: Frontier advanced to reclaimed, so validity transfers (same state)
      input-valid-wf₁-reclaimed : ValidAtWF mIn alloc₁-reclaimed x input-loc s₁
      input-valid-wf₁-reclaimed = validityWF-frontier-advance x input-loc s₁
                                    refl  -- frame preserved
                                    (IRResultAWF.reclaim-monotone result-f)  -- slot ≤ reclaim-f
                                    ≤-refl  -- heap same
                                    input-valid-wf-s1

      -- Set up RDI for g's input
      s₁' = record s₁ { regs = writeReg (regs s₁) RDI input-loc }
      rdi-eq₁ : readReg (regs s₁') RDI ≡ input-loc
      rdi-eq₁ = writeReg-same (regs s₁) RDI input-loc

      input-valid-wf₁' : ValidAtWF mIn alloc₁-reclaimed x input-loc s₁'
      input-valid-wf₁' = validityWF-mem-only x input-loc s₁ s₁' refl refl input-valid-wf₁-reclaimed

      g-exec-result : ∃[ mOut ] IRResultAWF mOut g x s₁' alloc₁-reclaimed
      g-exec-result = rec-wf mIn g (⟨,⟩-g-smaller f g {Heap}) x input-loc s₁' alloc₁-reclaimed
                        input-valid-wf₁' input-before₁-reclaimed (IRResultAWF.not-halted result-f) rdi-eq₁ combined-cap-g
      mG = proj₁ g-exec-result
      result-g = proj₂ g-exec-result

      s₂ = IRResultAWF.final-state result-g
      alloc₂ = IRResultAWF.final-alloc result-g
      snd-loc = IRResultAWF.result-loc result-g
      snd-valid-wf = IRResultAWF.result-valid-wf result-g

      ------------------------------------------------------------------------
      -- Pair allocation (using reclaimed allocations)
      ------------------------------------------------------------------------
      reclaim-g = IRResultAWF.reclaimable-slot result-g

      reclaim-g-bound : reclaim-g ≤ reclaim-f +ℕ rg
      reclaim-g-bound = IRResultAWF.reclaim-size-bound result-g

      capacity₂-eq : frame-capacity alloc₂ ≡ frame-capacity alloc
      capacity₂-eq = IRResultAWF.capacity-preserved result-g

      -- Derive capacity for pair allocation using ps (mode-dependent slot size)
      -- Chain: reclaim-g + ps ≤ reclaim-f + rg + ps ≤ slot + rf + rg + ps ≤ cap
      reclaim-g-plus-ps-fits : reclaim-g +ℕ ps ≤ frame-capacity alloc
      reclaim-g-plus-ps-fits = ≤-trans (+-monoˡ-≤ ps reclaim-g-bound)
                                  (≤-trans (+-monoˡ-≤ ps (+-monoˡ-≤ rg reclaim-f-bound))
                                     combined-cap-expanded)

      -- Create reclaimed allocation for pair allocation at reclaim-g position
      -- reclaim-g ≤ reclaim-f + rg ≤ cap
      reclaim-g-fits : reclaim-g ≤ frame-capacity alloc
      reclaim-g-fits = ≤-trans reclaim-g-bound combined-cap-g
      alloc₂-reclaimed : AllocState {FS}
      alloc₂-reclaimed = record alloc
        { next-slot = reclaim-g
        ; slots-available = reclaim-g-fits
        }

      -- Pair allocation fits at reclaim-g position (using mode-dependent ps)
      pair-fits-at-reclaim : reclaim-g +ℕ ps ≤ frame-capacity alloc
      pair-fits-at-reclaim = reclaim-g-plus-ps-fits

      -- Pair location at reclaim-g position (in alloc's frame)
      pair-loc = OnStack (current-frame alloc) reclaim-g

      alloc₃ : AllocState {FS}
      alloc₃ = record alloc
        { next-slot = reclaim-g +ℕ ps
        ; slots-available = pair-fits-at-reclaim
        }

      -- Write fst and snd pointers to pair
      s₃ = write-loc s₂ pair-loc fst-loc
      s₄ = write-loc s₃ (sucLoc pair-loc) snd-loc
      s-final = record s₄ { regs = writeReg (regs s₄) RAX pair-loc }

      -- Pair before frontier (at reclaim-g, which is before alloc₃'s frontier)
      pair-before : BeforeFrontier alloc₃ pair-loc
      pair-before = stack-before refl (m<m+n reclaim-g {ps} ps≥1)

      -- fst-loc is BeforeFrontier in alloc₃
      -- Chain: fst-loc before alloc₁ → before alloc₁-reclaimed → before alloc₂-reclaimed → before alloc₃
      fst-before₃ : BeforeFrontier alloc₃ fst-loc
      fst-before₃ = frontier-monotone alloc₁-reclaimed alloc₃
                      refl
                      (≤-trans (IRResultAWF.reclaim-monotone result-g) (m≤m+n reclaim-g ps))
                      ≤-refl
                      fst-loc
                      (IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits)

      -- snd-loc is BeforeFrontier in alloc₃
      snd-before₃ : BeforeFrontier alloc₃ snd-loc
      snd-before₃ = frontier-monotone alloc₂-reclaimed alloc₃
                      refl
                      (m≤m+n reclaim-g ps)
                      ≤-refl
                      snd-loc
                      (IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits)

      -- suc reclaim-g < reclaim-g + ps when ps ≥ 2
      -- Proof: suc (suc reclaim-g) ≤ reclaim-g + 2 ≤ reclaim-g + ps
      suc<+ps : suc reclaim-g < reclaim-g +ℕ ps
      suc<+ps = ≤-trans (suc<+2 reclaim-g) (+-monoʳ-≤ reclaim-g ps≥2)

      sucLoc-pair-before₃ : BeforeFrontier alloc₃ (sucLoc pair-loc)
      sucLoc-pair-before₃ = stack-before refl suc<+ps

      fst-ptr : readLoc s-final pair-loc ≡ just fst-loc
      fst-ptr = trans (readLoc-stackMem-eq s-final s₄ pair-loc refl refl)
                      (trans (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc pair-loc
                               (sucLoc-neq pair-loc))
                             (write-read-same s₂ pair-loc fst-loc))

      snd-ptr : readLoc s-final (sucLoc pair-loc) ≡ just snd-loc
      snd-ptr = trans (readLoc-stackMem-eq s-final s₄ (sucLoc pair-loc) refl refl)
                      (write-read-same s₃ (sucLoc pair-loc) snd-loc)

      ------------------------------------------------------------------------
      -- Validity transfer for fst through write operations
      --
      -- fst-valid-wf : ValidAtWF alloc₁ (eval f x) fst-loc s₁
      -- We need: ValidAtWF alloc₃ (eval f x) fst-loc s-final
      --
      -- With reclaim-based allocation, we need to be careful:
      -- - pair-loc = OnStack (current-frame alloc) reclaim-g
      -- - fst-loc is BeforeFrontier alloc₁-reclaimed (from reclaim-preserves-result)
      -- - The writes at pair-loc and sucLoc pair-loc are disjoint from fst-loc
      ------------------------------------------------------------------------

      -- fst-loc is BeforeFrontier in alloc₁-reclaimed
      fst-before-reclaimed : BeforeFrontier alloc₁-reclaimed fst-loc
      fst-before-reclaimed = IRResultAWF.reclaim-preserves-result result-f reclaim-f-fits

      -- fst validity at s₁ with alloc₁-reclaimed
      -- Use reclaim-preserves-validity to handle reclamation (slot decreasing)
      fst-valid-s1-reclaimed : ValidAtWF mF alloc₁-reclaimed (eval f x) fst-loc s₁
      fst-valid-s1-reclaimed = IRResultAWF.reclaim-preserves-validity result-f reclaim-f-fits

      -- Step 1: s₁ → s₁' (register write only)
      fst-valid-s1' : ValidAtWF mF alloc₁-reclaimed (eval f x) fst-loc s₁'
      fst-valid-s1' = validityWF-mem-only (eval f x) fst-loc s₁ s₁' refl refl fst-valid-s1-reclaimed

      -- Step 2: s₁' → s₂ (g execution, memory preserved at BeforeFrontier alloc₁-reclaimed)
      fst-valid-s2-reclaimed : ValidAtWF mF alloc₁-reclaimed (eval f x) fst-loc s₂
      fst-valid-s2-reclaimed = validityWF-mem-preserved (eval f x) fst-loc s₁' s₂
                                 fst-before-reclaimed
                                 (λ loc bf → IRResultAWF.mem-preserved-before result-g loc bf)
                                 fst-valid-s1'

      -- Transfer fst validity to alloc₂-reclaimed
      fst-valid-s2-alloc2r : ValidAtWF mF alloc₂-reclaimed (eval f x) fst-loc s₂
      fst-valid-s2-alloc2r = validityWF-frontier-advance (eval f x) fst-loc s₂
                               refl
                               (IRResultAWF.reclaim-monotone result-g)
                               ≤-refl
                               fst-valid-s2-reclaimed

      -- fst-loc is before alloc₂-reclaimed's frontier (for write disjointness)
      fst-before-alloc2r : BeforeFrontier alloc₂-reclaimed fst-loc
      fst-before-alloc2r = frontier-monotone alloc₁-reclaimed alloc₂-reclaimed
                             refl
                             (IRResultAWF.reclaim-monotone result-g)
                             ≤-refl
                             fst-loc fst-before-reclaimed

      -- Step 3: s₂ → s₃ (write at pair-loc = frontier of alloc₂-reclaimed)
      fst-valid-s3 : ValidAtWF mF alloc₂-reclaimed (eval f x) fst-loc s₃
      fst-valid-s3 = validityWF-write-at-frontier (eval f x) fst-loc s₂ fst-loc
                       fst-before-alloc2r fst-valid-s2-alloc2r

      -- Step 4: s₃ → s₄ (write at sucLoc pair-loc = suc-frontier of alloc₂-reclaimed)
      fst-valid-s4 : ValidAtWF mF alloc₂-reclaimed (eval f x) fst-loc s₄
      fst-valid-s4 = validityWF-write-at-suc-frontier (eval f x) fst-loc s₃ snd-loc
                       fst-before-alloc2r fst-valid-s3

      -- Step 5: s₄ → s-final (register write)
      fst-valid-sfinal-alloc2r : ValidAtWF mF alloc₂-reclaimed (eval f x) fst-loc s-final
      fst-valid-sfinal-alloc2r = validityWF-mem-only (eval f x) fst-loc s₄ s-final refl refl fst-valid-s4

      -- Step 6: alloc₂-reclaimed → alloc₃ (ps-slot allocation)
      fst-valid-wf₃ : ValidAtWF mF alloc₃ (eval f x) fst-loc s-final
      fst-valid-wf₃ = validityWF-alloc-advance (eval f x) fst-loc s-final ps pair-fits-at-reclaim
                        fst-valid-sfinal-alloc2r

      ------------------------------------------------------------------------
      -- Validity transfer for snd through write operations
      ------------------------------------------------------------------------

      -- snd-loc is BeforeFrontier in alloc₂-reclaimed
      snd-before-alloc2r : BeforeFrontier alloc₂-reclaimed snd-loc
      snd-before-alloc2r = IRResultAWF.reclaim-preserves-result result-g reclaim-g-fits

      -- snd validity at s₂ with alloc₂-reclaimed
      -- Use reclaim-preserves-validity to handle reclamation (slot decreasing)
      snd-valid-s2-reclaimed : ValidAtWF mG alloc₂-reclaimed (eval g x) snd-loc s₂
      snd-valid-s2-reclaimed = IRResultAWF.reclaim-preserves-validity result-g reclaim-g-fits

      snd-valid-wf₃ : ValidAtWF mG alloc₃ (eval g x) snd-loc s-final
      snd-valid-wf₃ = validityWF-alloc-advance (eval g x) snd-loc s-final ps pair-fits-at-reclaim
                        (validityWF-mem-only (eval g x) snd-loc s₄ s-final refl refl
                          (validityWF-write-at-suc-frontier (eval g x) snd-loc s₃ snd-loc
                            snd-before-alloc2r
                            (validityWF-write-at-frontier (eval g x) snd-loc s₂ fst-loc
                              snd-before-alloc2r
                              snd-valid-s2-reclaimed)))

      -- Heap mode: use valid-pair-boxed-wf constructor
      pair-valid-wf-final : ValidAtWF Heap alloc₃ (pair (eval f x) (eval g x)) pair-loc s-final
      pair-valid-wf-final = valid-pair-boxed-wf fst-ptr snd-ptr fst-before₃ snd-before₃ sucLoc-pair-before₃ fst-valid-wf₃ snd-valid-wf₃

      rax-eq : readReg (regs s-final) RAX ≡ pair-loc
      rax-eq = writeReg-same (regs s₄) RAX pair-loc

      not-halted-final : halted s-final ≡ false
      not-halted-final = IRResultAWF.not-halted result-g

      frame-preserved-pair : current-frame alloc₃ ≡ current-frame alloc
      frame-preserved-pair = refl  -- alloc₃ is based on alloc directly

      slot-monotone-pair : next-slot alloc ≤ next-slot alloc₃
      slot-monotone-pair = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                   (≤-trans (IRResultAWF.reclaim-monotone result-g)
                                            (m≤m+n reclaim-g ps))

      heap-monotone-pair : next-heap-ref alloc ≤ next-heap-ref alloc₃
      heap-monotone-pair = ≤-refl  -- alloc₃ based on alloc, heap unchanged

      heap-preserved-pair : next-heap-ref alloc₃ ≡ next-heap-ref alloc
      heap-preserved-pair = refl  -- alloc₃ based on alloc

      capacity-preserved-pair : frame-capacity alloc₃ ≡ frame-capacity alloc
      capacity-preserved-pair = refl  -- alloc₃ based on alloc

      mem-preserved-pair : ∀ loc → BeforeFrontier alloc loc → readLoc s-final loc ≡ readLoc s loc
      mem-preserved-pair loc bf =
        let -- Transfer bf to alloc₁-reclaimed and alloc₂-reclaimed
            bf-reclaimed : BeforeFrontier alloc₁-reclaimed loc
            bf-reclaimed = frontier-monotone alloc alloc₁-reclaimed
                             refl
                             (IRResultAWF.reclaim-monotone result-f)
                             ≤-refl
                             loc bf
            bf-reclaimed2 : BeforeFrontier alloc₂-reclaimed loc
            bf-reclaimed2 = frontier-monotone alloc alloc₂-reclaimed
                              refl
                              (≤-trans (IRResultAWF.reclaim-monotone result-f) (IRResultAWF.reclaim-monotone result-g))
                              ≤-refl
                              loc bf
            step-g = IRResultAWF.mem-preserved-before result-g loc bf-reclaimed
            step-reg-g = readLoc-stackMem-eq s₁' s₁ loc refl refl
            step-f = IRResultAWF.mem-preserved-before result-f loc bf
        in trans (readLoc-stackMem-eq s-final s₄ loc refl refl)
                 (trans (write-preserves-disjoint s₃ (sucLoc pair-loc) snd-loc loc
                          (λ eq → suc-frontier-neq-before alloc₂-reclaimed loc bf-reclaimed2 eq))
                        (trans (write-preserves-disjoint s₂ pair-loc fst-loc loc
                                 (λ eq → at-frontier-neq-before alloc₂-reclaimed loc bf-reclaimed2 eq))
                               (trans step-g (trans step-reg-g step-f))))

      ------------------------------------------------------------------------
      -- Reclamation: pair-reclaim = reclaim-g +ℕ ps (mode-dependent)
      --
      -- With reclaim-based allocation, we can prove reclaim-size-bound:
      --   reclaim-g ≤ reclaim-f + rg
      --   reclaim-f ≤ slot + rf
      --   pair-reclaim ≤ slot + rf + rg + ps = slot + req-pair ✓
      ------------------------------------------------------------------------
      pair-reclaim = reclaim-g +ℕ ps

      pair-reclaim-monotone : next-slot alloc ≤ pair-reclaim
      pair-reclaim-monotone = ≤-trans (IRResultAWF.reclaim-monotone result-f)
                                      (≤-trans (IRResultAWF.reclaim-monotone result-g)
                                               (m≤m+n reclaim-g ps))

      pair-reclaim-bounded : pair-reclaim ≤ next-slot alloc₃
      pair-reclaim-bounded = ≤-refl  -- next-slot alloc₃ = reclaim-g +ℕ ps

      pair-reclaim-preserves : ∀ (fits : pair-reclaim ≤ frame-capacity alloc) →
        BeforeFrontier (record alloc { next-slot = pair-reclaim ; slots-available = fits }) pair-loc
      pair-reclaim-preserves fits =
        frontier-same-heap alloc₃
          (record alloc { next-slot = pair-reclaim ; slots-available = fits })
          refl refl refl
          pair-loc pair-before

      -- Validity at reclaimed allocation - PROVEN via bf-same-frame-slot
      -- The two allocations have the same current-frame, next-slot, and next-heap-ref.
      -- Only slots-available differs (proof-irrelevant).
      pair-reclaim-preserves-validity : ∀ (fits : pair-reclaim ≤ frame-capacity alloc) →
        ValidAtWF Heap (record alloc { next-slot = pair-reclaim ; slots-available = fits })
                  (pair (eval f x) (eval g x)) pair-loc s-final
      pair-reclaim-preserves-validity fits = validityWF-with-bf-transfer
        (pair (eval f x) (eval g x)) pair-loc s-final alloc₃
        (record alloc { next-slot = pair-reclaim ; slots-available = fits })
        (λ loc bf → bf-same-frame-slot alloc₃
          (record alloc { next-slot = pair-reclaim ; slots-available = fits })
          refl refl refl loc bf)
        pair-valid-wf-final

      -- reclaim-size-bound: pair-reclaim ≤ slot + ir-stack-requirement
      -- Uses pair-slot-bounded-lemma to chain:
      --   reclaim-g ≤ reclaim-f + rg (g's bound)
      --   reclaim-f ≤ slot + rf      (f's bound)
      --   reclaim-g + ps ≤ slot + ((rf + rg) + ps) = slot + req-pair ✓
      pair-reclaim-size-bound : pair-reclaim ≤ next-slot alloc +ℕ req-pair
      pair-reclaim-size-bound = pair-slot-bounded-lemma (next-slot alloc) reclaim-f reclaim-g rf rg ps
                                  reclaim-g-bound reclaim-f-bound

