------------------------------------------------------------------------
-- Once.CCC.Machine.IR.CataLayer
--
-- The Cata layer-processing mutual block, extracted from RecTrace
-- (Plan 0.27): a ~2500-line {-# TERMINATING #-} mutual block
-- (process-layer / process-layer-prod / cata-dispatched-new). Split out
-- so RecTrace holds the reusable infrastructure (ProcessedLayerResult,
-- trace helpers, the temporary validity bridges) and this module holds
-- the recursion. The TERMINATING pragma here is the well-founded-recursion
-- target; isolating it makes that future refactor local.
------------------------------------------------------------------------

module Once.CCC.Machine.IR.CataLayer where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _⊔_; _∸_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; <-≤-trans; ≤-<-trans; m≤m+n; m<m+n; m≤n+m; n≤1+n; n<1+n; m≤m⊔n; m≤n⊔m; n≤m⊔n; ⊔-lub; ⊔-monoˡ-≤; ⊔-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; <⇒≢; +-comm; +-assoc; +-suc; +-identityʳ; m∸n+n≡m)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; ≢-sym)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.IR
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_; μ-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseType;
  base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum;
  WellFormedF-irrelevant)
open import Once.CCC.Eval using (eval)
open import Once.CCC.IR.Size
open import Once.CCC.IR.Stack
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.CCC.Machine.FrontierLemma

-- Import functor dispatch helpers
open import Once.CCC.Machine.IR.FunctorDispatch

-- Import SMPrimitives for trace predicates
import Once.CCC.Machine.SMPrimitives as SMP

-- Import TreeTrace for recursive control flow
open import Once.CCC.Machine.SMCore using (TreeTrace; ε; instr; _▸_; branch; call-sub; flat)

-- Import semantic operations
open import Once.Semantics.Core ℕ using (⟦μ⟧; ⟦_⟧F; sem-In; sem-Out; sem-In-Out; sem-cata; sem-cata-compute; sem-fmap; coerce-struct⁻¹; coerce-functor; coerce-functor⁻¹; coerce-round-trip; coerce⁻¹-round-trip)

-- RecTrace provides ProcessedLayerResult + trace helpers + bridges.
open import Once.CCC.Machine.IR.RecTrace
-- LambekValidity provides out-μ-valid (unwrap the μ-value's ValidAtWF).
import Once.CCC.Machine.IR.LambekValidity as LV
-- Plan 0.27 Option B: well-founded recursion on μ-value size (replaces
-- the {-# TERMINATING #-} pragma).
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Once.CCC.Machine.IR.MuSize using (μ-size; child-measure; child-sum-<;
  child-bound-Id; child-bound-inj₁; child-bound-inj₂;
  child-bound-prod-left; child-bound-prod-right;
  functor-size; fsize-inj-left; fsize-inj-right; fsize-prod-left; fsize-prod-right)

module CataLayerImpl {FS : FrameSemantics} (program-bound : ℕ) where
  open FrontierInvariant {FS}
  open MemOps {FS}
  open WriteOps {FS}
  open AbstractExec {FS}
  open ExecLemmas {FS}
  open FrameSemantics FS

  open SMP.TracePrimitives {FS}
  open SMP.RecSchemeSemantics {FS}
  open SMP.TraceComposition {FS}
  open FrontierLemmas {FS}

  open import Once.CCC.Machine.ClosureWellFormed
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; IRResultAWF; ResultPlace; unit-result; at-loc;
           place-loc; place-valid; place-before; place-rax; RecDispatcherWF;
           validityWF-mem-only; validityWF-mem-preserved; validityWF-trace-preserves;
           validityWF-frontier-advance;
           validityWF-alloc-advance; validityWF-with-bf-transfer;
           valid-μ-wf; valid-primitive-wf;
           valid-unit-wf; valid-int-wf; valid-float-wf; valid-str-wf; valid-buffer-wf;
           valid-pair-wf; valid-inl-wf; valid-inr-wf;
           irresult-mem-preserved; mk-IRResultAWF-via-bump)

  -- Import μLayerValid for layer validity
  open import Once.CCC.Machine.IR.MuValidity
  open MuValidityImpl {FS} program-bound
    using (μLayerValid; μValid; μ-valid;
           μlayer-K; μlayer-Id; μlayer-inl; μlayer-inr; μlayer-prod;
           μLayerValid-mem-only; μLayerValid-frontier-advance;
           μLayerValid-mem-preserved; μValid-frontier-advance)

  -- Reusable infrastructure (ProcessedLayerResult, helpers, bridges).
  open RecTraceImpl {FS} program-bound
  open LV.LambekValidityImpl {FS} program-bound using (out-μ-valid)

  -- An AllocState is determined by its three fields (via record-η), so an
  -- AllocState equality follows from per-field equalities. Used to discharge
  -- the bump-tracked `final-alloc-eq` fields of ProcessedLayerResult.
  cong₃-alloc : ∀ {A B C : Set} (f : A → B → C → AllocState {FS}) {x y u v p q}
              → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
  cong₃-alloc f {x} {y} {u} {v} {p} {q} ex eu ep =
    trans (cong (λ z → f z u p) ex)
          (trans (cong (λ z → f y z p) eu) (cong (λ z → f y v z) ep))

  alloc-≡-by-fields : ∀ {a1 a2 : AllocState {FS}}
    → current-frame a1 ≡ current-frame a2
    → next-slot a1 ≡ next-slot a2
    → next-heap-ref a1 ≡ next-heap-ref a2
    → a1 ≡ a2
  alloc-≡-by-fields ef es eh = cong₃-alloc mkAllocState ef es eh

  -- The Sum case's bump: the sub-layer's slots are reclaimed (back to the
  -- sub-layer's final next-slot) then a 2-slot wrapper is allocated, so the
  -- net AllocBump is `bump-+ sub-bump (mkBump 2 0)`. Given the sub-layer's
  -- bump-eq and the wrapper's per-field preservation, this rebuilds the
  -- whole `final-alloc ≡ apply-bump bump alloc` field. Reused by inl and inr.
  sum-bump-eq : ∀ (sub-bump : AllocBump)
                  (alloc alloc-sub alloc-wrap alloc-setup : AllocState {FS})
    → alloc-setup ≡ alloc
    → alloc-sub ≡ apply-bump sub-bump alloc-setup
    → current-frame alloc-wrap ≡ current-frame alloc-sub
    → next-slot alloc-wrap ≡ next-slot alloc-sub +ℕ 2
    → next-heap-ref alloc-wrap ≡ next-heap-ref alloc-sub
    → alloc-wrap ≡ apply-bump (bump-+ sub-bump (mkBump 2 0)) alloc
  sum-bump-eq sub-bump alloc alloc-sub alloc-wrap alloc-setup
              setup-eq sub-eq wframe wslot wheap =
    alloc-≡-by-fields
      (trans wframe (trans (cong current-frame sub-eq) (cong current-frame setup-eq)))
      (trans wslot
        (trans (cong (_+ℕ 2) sub-slot)
          (trans (+-assoc d ns 2)
            (trans (cong (d +ℕ_) (+-comm ns 2)) (sym (+-assoc d 2 ns))))))
      (trans wheap (trans sub-heap (cong (_+ℕ next-heap-ref alloc) (sym (+-identityʳ hd)))))
    where
      d  = next-slot-delta sub-bump
      ns = next-slot alloc
      hd = next-heap-ref-delta sub-bump
      sub-slot : next-slot alloc-sub ≡ d +ℕ ns
      sub-slot = trans (cong next-slot sub-eq) (cong (λ a → d +ℕ next-slot a) setup-eq)
      sub-heap : next-heap-ref alloc-sub ≡ hd +ℕ next-heap-ref alloc
      sub-heap = trans (cong next-heap-ref sub-eq) (cong (λ a → hd +ℕ next-heap-ref a) setup-eq)

  private
    -- Helper for Sum left branch: proves reclaimable-slot ≤ start + layer-capacity
    -- Used for both slot-usage-bound and slot-stays-in-budget (they're identical when reclaimable-slot = next-slot final-alloc)
    sum-left-slot-budget : ∀ {FL FR G A}
      (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
      (alg : IR (⟦ G ⟧T A) A)
      (alloc : AllocState {FS})
      (l-reclaimable : ℕ)
      (alloc-after-wrapper : AllocState {FS})
      (wrapper-next-slot-eq : next-slot alloc-after-wrapper ≡ l-reclaimable +ℕ 2)
      (slot-usage-bound-inj1 : l-reclaimable ≤ next-slot alloc +ℕ layer-capacity wfL wfG alg)
      → next-slot alloc-after-wrapper ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
    sum-left-slot-budget wfL wfR wfG alg alloc l-reclaimable alloc-after-wrapper wrapper-next-slot-eq child-bound =
      let step1 : l-reclaimable +ℕ 2 ≤ (next-slot alloc +ℕ layer-capacity wfL wfG alg) +ℕ 2
          step1 = +-monoˡ-≤ 2 child-bound
          step2 : (next-slot alloc +ℕ layer-capacity wfL wfG alg) +ℕ 2 ≡ next-slot alloc +ℕ (layer-capacity wfL wfG alg +ℕ 2)
          step2 = +-assoc (next-slot alloc) (layer-capacity wfL wfG alg) 2
          fits : layer-capacity wfL wfG alg +ℕ 2 ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
          fits = sum-wrapper-fits-left wfL wfR wfG alg
          step3 : next-slot alloc +ℕ (layer-capacity wfL wfG alg +ℕ 2) ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
          step3 = +-monoʳ-≤ (next-slot alloc) fits
      in subst (_≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg)
               (sym wrapper-next-slot-eq)
               (≤-trans (subst (l-reclaimable +ℕ 2 ≤_) step2 step1) step3)

    -- Helper for Sum right branch: proves reclaimable-slot ≤ start + layer-capacity
    sum-right-slot-budget : ∀ {FL FR G A}
      (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
      (alg : IR (⟦ G ⟧T A) A)
      (alloc : AllocState {FS})
      (r-reclaimable : ℕ)
      (alloc-after-wrapper : AllocState {FS})
      (wrapper-next-slot-eq : next-slot alloc-after-wrapper ≡ r-reclaimable +ℕ 2)
      (slot-usage-bound-inj2 : r-reclaimable ≤ next-slot alloc +ℕ layer-capacity wfR wfG alg)
      → next-slot alloc-after-wrapper ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
    sum-right-slot-budget wfL wfR wfG alg alloc r-reclaimable alloc-after-wrapper wrapper-next-slot-eq child-bound =
      let step1 : r-reclaimable +ℕ 2 ≤ (next-slot alloc +ℕ layer-capacity wfR wfG alg) +ℕ 2
          step1 = +-monoˡ-≤ 2 child-bound
          step2 : (next-slot alloc +ℕ layer-capacity wfR wfG alg) +ℕ 2 ≡ next-slot alloc +ℕ (layer-capacity wfR wfG alg +ℕ 2)
          step2 = +-assoc (next-slot alloc) (layer-capacity wfR wfG alg) 2
          fits : layer-capacity wfR wfG alg +ℕ 2 ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
          fits = sum-wrapper-fits-right wfL wfR wfG alg
          step3 : next-slot alloc +ℕ (layer-capacity wfR wfG alg +ℕ 2) ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
          step3 = +-monoʳ-≤ (next-slot alloc) fits
      in subst (_≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg)
               (sym wrapper-next-slot-eq)
               (≤-trans (subst (r-reclaimable +ℕ 2 ≤_) step2 step1) step3)

    -- Helper for Prod: compositional proof using both children's slot budgets
    -- With SUM formula: layer-capacity (wf-Prod wfL wfR) = 1 + capL + capR
    -- Proof chain:
    --   next-slot final-alloc ≤ l-reclaimable + capR (from r-slot-budget + alloc-for-right-eq)
    --                        �� (suc (next-slot alloc) + capL) + capR (from l-slot-usage)
    --                        = next-slot alloc + (1 + capL + capR)
    --                        = next-slot alloc + layer-capacity (wf-Prod wfL wfR)
    prod-slot-budget : ∀ {FL FR G A}
      (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
      (alg : IR (⟦ G ⟧T A) A)
      (alloc : AllocState {FS})
      (l-reclaimable : ℕ)
      (final-alloc : AllocState {FS})
      -- l-reclaimable bounded by left child's capacity
      (l-slot-usage : l-reclaimable ≤ suc (next-slot alloc) +ℕ layer-capacity wfL wfG alg)
      -- right child's slot-stays-in-budget starting from l-reclaimable
      (r-slot-budget : next-slot final-alloc ≤ l-reclaimable +ℕ layer-capacity wfR wfG alg)
      → next-slot final-alloc ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
    prod-slot-budget wfL wfR wfG alg alloc l-reclaimable final-alloc l-slot-usage r-slot-budget =
      let capL = layer-capacity wfL wfG alg
          capR = layer-capacity wfR wfG alg
          -- Step 1: r-slot-budget gives next-slot final-alloc ≤ l-reclaimable + capR
          -- Step 2: l-slot-usage gives l-reclaimable ≤ suc (next-slot alloc) + capL
          -- Step 3: Monotonicity: l-reclaimable + capR ≤ (suc (next-slot alloc) + capL) + capR
          step3 : l-reclaimable +ℕ capR ≤ (suc (next-slot alloc) +ℕ capL) +ℕ capR
          step3 = +-monoˡ-≤ capR l-slot-usage
          -- Step 4: Rearrange: (suc n + capL) + capR = suc n + (capL + capR)
          step4 : (suc (next-slot alloc) +ℕ capL) +ℕ capR ≡ suc (next-slot alloc) +ℕ (capL +ℕ capR)
          step4 = +-assoc (suc (next-slot alloc)) capL capR
          -- Step 5: suc n + (capL + capR) = n + suc (capL + capR) = n + (1 + capL + capR)
          step5 : suc (next-slot alloc) +ℕ (capL +ℕ capR) ≡ next-slot alloc +ℕ suc (capL +ℕ capR)
          step5 = sym (+-suc (next-slot alloc) (capL +ℕ capR))
          -- Step 6: Combine
          combined-eq : (suc (next-slot alloc) +ℕ capL) +ℕ capR ≡ next-slot alloc +ℕ suc (capL +ℕ capR)
          combined-eq = trans step4 step5
      in ≤-trans r-slot-budget (subst (l-reclaimable +ℕ capR ≤_) combined-eq step3)

  -- Plan 0.27 Option B: accessibility predecessor — the structural step
  -- the μ-value recursion decreases on (replaces {-# TERMINATING #-}).
  acc-rs : ∀ {n m} → Acc _<_ n → m < n → Acc _<_ m
  acc-rs (acc rs) lt = rs lt

  ------------------------------------------------------------------------
  -- Plan 0.27 perf: REIFIED cata-recursion capability (Dispatcher pattern).
  --
  -- The well-founded recursion used to be a single mutual block of
  -- process-layer / process-layer-prod / cata-dispatched-new. Removing the
  -- {-# TERMINATING #-} pragma made Agda's termination checker (foetus)
  -- analyse that whole block: 3 huge functions + ~17 with-generated
  -- auxiliaries in one SCC. That blew the typecheck past 26 min (type-
  -- checking the same module WITH the pragma is ~2 min — the cost is
  -- foetus on the oversized mixed Acc+structural SCC).
  --
  -- Fix (mirrors Dispatcher.make-rec-wf / run-ir-wf): process-layer no
  -- longer calls cata-dispatched-new directly; it takes this reified
  -- capability "run the catamorphism on any μ-value of size < n". That
  -- breaks the call cycle, so foetus sees TWO small independent SCCs:
  -- {process-layer, process-layer-prod} (structural on the functor) and
  -- {make-cata-rec, cata-dispatched-new} (the Acc recursion). SCCs are
  -- computed from the call graph, not the `mutual` grouping, so no block
  -- split is needed — only the cycle has to be cut.
  ------------------------------------------------------------------------
  CataRecBound : ∀ {G A} (wfG : WellFormedF G) (alg : IR (⟦ G ⟧T A) A) (n : ℕ) → Set
  CataRecBound {G} {A} wfG alg n =
    ∀ {mv} (c : ⟦μ⟧ G) → μ-size wfG c < n
    → (mIn : AllocMode) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
    → ValidAtWF mv alloc c input-loc s
    → BeforeFrontier alloc input-loc
    → halted s ≡ false
    → readReg (regs s) Input1 ≡ SV-Ptr input-loc
    → ∃[ mOut ] IRResultAWF mOut (Cata wfG alg) c s alloc

  ------------------------------------------------------------------------
  -- Plan 0.27 perf: REIFIED FUNCTOR-recursion capability. process-layer
  -- descends FL/FR structurally; routing those calls through this
  -- capability (built by make-proc-rec from an `Acc _<_ (functor-size F)`)
  -- makes process-layer/process-layer-prod NON-recursive to foetus — their
  -- heavy clause bodies (passing big setup expressions like s-setup) leave
  -- the termination SCC, which was the Termination.Graph blow-up. `nf`
  -- bounds the functor-size of the sub-layers this capability may process;
  -- `n` is the shared μ-children measure bound (unchanged across the
  -- functor descent). Mirrors CataRecBound + the Dispatcher's make-rec-wf.
  ------------------------------------------------------------------------
  ProcLayerCap : ∀ {G A} (wfG : WellFormedF G) (alg : IR (⟦ G ⟧T A) A) (n nf : ℕ) → Set
  ProcLayerCap {G} {A} wfG alg n nf =
    ∀ {mv F} (wfF : WellFormedF F) → functor-size F < nf
    → (layer : ⟦ F ⟧F (⟦μ⟧ G)) (mIn : AllocMode) (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
    → child-measure F wfG layer < n
    → ValidAtWF mv alloc {⟦ F ⟧T (μ-type G)} (coerce-functor⁻¹ F (μ-type G) layer) input-loc s
    → BeforeFrontier alloc input-loc
    → halted s ≡ false
    → readReg (regs s) Input1 ≡ SV-Ptr input-loc
    → ∃[ mOut ] ProcessedLayerResult wfG alg mOut wfF layer s alloc

  mutual
    -- | Process an F-layer within μG context
    --
    -- Dispatches on functor structure:
    --   K: constant, no recursion - just return the value
    --   Id: recursive position - compute cata and return result
    --   Sum: process taken branch, wrap result in inj₁/inj₂
    --   Prod: process both components, combine results
    --
    -- Key: layer-valid provides μLayerValid proof which enables:
    --   K: use valid-primitive-wf with BeforeFrontier
    --   Id: extract μValid for recursive call
    --   Sum/Prod: decompose structurally
    -- Capacity model: Each layer F needs layer-capacity wfF wfG alg slots.
    -- For Product: layer-capacity (wf-Prod L R) = 1 + max(L, R) - save-slot + child
    -- For Sum: layer-capacity (wf-Sum L R) = 2 + max(L, R) - wrapper + child
    -- For Id: layer-capacity wf-Id wfG = ir-stack-requirement (Cata wfG alg)
    -- For K: layer-capacity (wf-K _) = ir-stack-requirement alg + pair-slots
    process-layer : ∀ {mv F G A}
      (wfF : WellFormedF F) (wfG : WellFormedF G)
      (alg : IR (⟦ G ⟧T A) A)
      (dispatch : RecDispatcherWF (ir-size (Cata wfG alg)))
      (layer : ⟦ F ⟧F (⟦μ⟧ G))
      (mIn : AllocMode)
      (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      -- Plan 0.27 Option B: well-founded recursion on μ-value size.
      -- `n` bounds the total size of the children at this layer's Id
      -- positions; `rec` is the reified capability to run the cata on any
      -- child of size < n (the Id case's decrease lives inside it). Taking
      -- the capability instead of recursing into cata-dispatched-new keeps
      -- process-layer out of the Acc recursion's SCC (see CataRecBound).
      (n : ℕ) (rec : CataRecBound wfG alg n)
      -- Functor-recursion capability: process sub-layers (FL/FR) of strictly
      -- smaller functor-size. Routing the Sum/Prod descent through it keeps
      -- process-layer out of the termination SCC (see ProcLayerCap).
      (procRec : ProcLayerCap wfG alg n (functor-size F))
      (size-bound : child-measure F wfG layer < n)
      -- Plan 0.27: layer validity is the layer's OWN ValidAtWF (mode-poly
      -- `mv`), not the lossy mode-agnostic μLayerValid. coerce-functor⁻¹
      -- bridges the Set-level layer to its Type-interp form.
      → ValidAtWF mv alloc {⟦ F ⟧T (μ-type G)} (coerce-functor⁻¹ F (μ-type G) layer) input-loc s
      → BeforeFrontier alloc input-loc
      → halted s ≡ false
      → readReg (regs s) Input1 ≡ SV-Ptr input-loc
      → ∃[ mOut ] ProcessedLayerResult wfG alg mOut wfF layer s alloc

    -- K case: constant layer, no recursion
    -- The processed layer is just the constant value itself
    process-layer (wf-K {T} isBase) wfG alg dispatch k-val mIn input-loc s alloc
      n rec procRec size-bound _ input-before not-halted rdi-eq =
      -- For K T: ⟦ K T ⟧F X = ⟦ T ⟧ for any X
      -- The processed layer is the same constant: k-val : ⟦ T ⟧
      -- sem-fmap (K T) f k-val = k-val (fmap for K is identity)
      mIn , record
        { processed = k-val
        ; trace = k-trace
        ; final-state = s-after
        ; final-alloc = alloc
        ; bump = bump-0
        ; final-alloc-eq = refl
        ; trace-no-frame-ops = tt , tt
        ; trace-correct = cong proj₁ (exec-trace-single mov-to-output s alloc not-halted)
        ; alloc-correct = cong proj₂ (exec-trace-single mov-to-output s alloc not-halted)
        ; result-place = at-loc input-loc
            (validityWF-mem-only k-val input-loc s s-after refl refl (valid-basetype-wf isBase input-before))
            input-before
            (trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) rdi-eq)
            (validityWF-mem-only k-val input-loc s s-after refl refl (valid-basetype-wf isBase input-before))
            input-before
        ; not-halted = not-halted
        ; semantic-correct = refl  -- sem-fmap K f x = x, coerce-struct⁻¹ K _ x = x
        ; frame-preserved = refl
        ; slot-monotone = ≤-refl
        -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-preserves-*
        -- slot-usage-bound: K case uses 0 slots, so next-slot alloc ≤ next-slot alloc + layer-capacity
        -- layer-capacity (wf-K _) wfG alg = ir-stack-requirement alg + pair-slots
        ; slot-usage-bound = m≤m+n (next-slot alloc) (layer-capacity (wf-K isBase) wfG alg)
        -- max-slot-used: K case doesn't write any slots
        ; max-slot-used = next-slot alloc
        ; max-slot-geq-final = ≤-refl
        ; max-slot-usage-bound = m≤m+n (next-slot alloc) (layer-capacity (wf-K isBase) wfG alg)
        -- slot-stays-in-budget: K doesn't allocate, final-alloc = alloc
        ; slot-stays-in-budget = m≤m+n (next-slot alloc) (layer-capacity (wf-K isBase) wfG alg)
        ; heap-monotone = ≤-refl
        ; heap-preserved = refl  -- final-alloc = alloc, so heap unchanged
        ; mem-preserved = λ loc _ → exec-abstract-mov-to-output-preserves-mem s alloc loc
        -- Trace region bounds: mov-to-output writes/reads no slots
        ; trace-writes-above = tt
        ; trace-writes-below = tt
        ; trace-slot-reads-above = tt
        ; trace-slot-reads-below = tt
        -- Trace preservation properties
        ; trace-twf = twf-∷ tt twf-[]
        -- scratch-bounded: K case has final-alloc = alloc, so same as max-slot-usage-bound
        ; scratch-bounded = m≤m+n (next-slot alloc) (layer-capacity (wf-K isBase) wfG alg)
        }
      where
        k-trace : AbstractTrace
        k-trace = mov-to-output ∷ []

        -- Use proj₁ (exec-abstract ...) to get state consistent with exec-abstract-mov-to-output-preserves-mem
        s-after : LocState FS
        s-after = proj₁ (exec-abstract mov-to-output s alloc)

    -- Id case: recursive position, compute cata on μ-value
    -- The processed layer is the cata result
    process-layer wf-Id wfG alg dispatch μ-val mIn input-loc s alloc
      n rec procRec size-bound μ-val-valid input-before not-halted rdi-eq =
      mRec , record
        { processed = rec-val  -- The cata result
        ; trace = rec-trace
        ; final-state = s-rec
        ; final-alloc = alloc-rec
        ; bump = IRResultAWF.bump rec-result
        ; final-alloc-eq = refl
        ; trace-no-frame-ops = IRResultAWF.trace-no-frame-ops rec-result
        ; trace-correct = IRResultAWF.trace-correct rec-result
        ; alloc-correct = IRResultAWF.alloc-correct rec-result
        ; result-place = at-loc rec-loc rec-valid rec-before rec-rax rec-valid rec-before
        ; not-halted = rec-not-halted
        ; semantic-correct = refl  -- sem-fmap Id f x = f x, coerce-struct⁻¹ Id _ x = x
        ; frame-preserved = IRResultAWF.frame-preserved rec-result
        ; slot-monotone = rec-slot-mono
        -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-preserves-*
        -- slot-usage-bound: IRResultAWF.slot-stays-in-budget gives exactly this bound
        ; slot-usage-bound = bridge-slot-bound (next-slot alloc-rec ≤_)
            (IRResultAWF.slot-stays-in-budget rec-result)
        -- max-slot-used: Use IRResultAWF.max-slot-written for consistent trace-writes-below type
        ; max-slot-used = IRResultAWF.max-slot-written rec-result
        ; max-slot-geq-final = IRResultAWF.max-slot-geq-final rec-result
        ; max-slot-usage-bound = bridge-slot-bound (IRResultAWF.max-slot-written rec-result ≤_)
            (IRResultAWF.max-slot-usage-bound rec-result)
        -- slot-stays-in-budget: Id delegates to Cata, which provides this property
        -- layer-capacity wf-Id = ir-stack-requirement (Cata wfG alg), so this says:
        --   next-slot final-alloc ≤ next-slot alloc + ir-stack-requirement (Cata wfG alg)
        ; slot-stays-in-budget = bridge-slot-bound (next-slot alloc-rec ≤_)
            (IRResultAWF.slot-stays-in-budget rec-result)
        -- Plan 0.14 Phase B.0: IRResultAWF.heap-preserved removed; rec-result
        -- comes from Cata which is stack-only (heap-budget = 0), so heap-preserved
        -- is derivable via CWF.heap-preserved-of. SMP.!! placeholder until the
        -- "stack-only sub-IR" precondition is wired through.
        ; heap-monotone = IRResultAWF.heap-monotone rec-result
        ; heap-preserved = SMP.!!
        ; mem-preserved = irresult-mem-preserved rec-result
        -- Trace region bounds from IRResultAWF
        -- IRResultAWF uses max-slot-written as bound, which equals our max-slot-used
        ; trace-writes-above = IRResultAWF.trace-writes-above rec-result
        ; trace-writes-below = IRResultAWF.trace-writes-below rec-result
        ; trace-slot-reads-above = IRResultAWF.trace-slot-reads-above rec-result
        ; trace-slot-reads-below = IRResultAWF.trace-slot-reads-below rec-result
        -- Trace preservation properties
        ; trace-twf = IRResultAWF.trace-twf rec-result
        -- scratch-bounded (INPUT-relative): Id delegates to Cata
        -- layer-capacity wf-Id = ir-stack-requirement (Cata wfG alg)
        -- Use max-slot-usage-bound which is INPUT-relative
        ; scratch-bounded = bridge-slot-bound (IRResultAWF.max-slot-written rec-result ≤_)
            (IRResultAWF.max-slot-usage-bound rec-result)
        }
      where
        -- Plan 0.27: μ-val-valid is now the layer validity itself (the Id
        -- position IS the μ-value, ValidAtWF{μ-type G} directly) — no
        -- μValid→μValidAtWF bridge needed.

        -- Recursive call: compute cata on μ-val via the reified capability
        -- (the Id position's μ-value has size < n by child-bound-Id; `rec`
        -- supplies the structurally-smaller Acc internally).
        cata-call = rec μ-val (child-bound-Id wfG μ-val size-bound) mIn input-loc s alloc
                      μ-val-valid input-before not-halted rdi-eq
        mRec = proj₁ cata-call
        rec-result = proj₂ cata-call

        -- Plan 0.2.4.5 D1 task #28: place-* uses retained here.
        -- Where-block enables multi-clause dispatch but the result-place
        -- field requires explicit at-loc construction since the cata's
        -- result-place type doesn't align with ProcessedLayerResult's
        -- (different reclaim-alloc indexing).
        rec-val = eval (Cata wfG alg) μ-val
        s-rec = IRResultAWF.final-state rec-result
        alloc-rec = IRResultAWF.final-alloc rec-result
        rec-place = IRResultAWF.result-place rec-result
        rec-loc = place-loc rec-place
        rec-trace = IRResultAWF.trace rec-result
        rec-valid = place-valid rec-place
        rec-before = place-before rec-place
        rec-rax = place-rax rec-place
        rec-not-halted = IRResultAWF.not-halted rec-result
        rec-slot-mono = IRResultAWF.slot-monotone rec-result

        -- Plan 0.2.4.5 D1 task #30: dynamic-budget bridge.
        -- cata-dispatched-new sets stack-budget = ir-stack-requirement (Cata wfG alg)
        -- which is definitionally equal to layer-capacity wf-Id wfG alg, but Agda
        -- can't reduce the projection on the opaque rec-result. Local trust point
        -- discharged by the producer's literal setting (RecTrace run-Cata at line ~3823).
        postulate
          stack-budget-rec-eq : IRResultAWF.stack-budget rec-result ≡ layer-capacity wf-Id wfG alg

        bridge-slot-bound : ∀ (P : ℕ → Set) →
          P (next-slot alloc +ℕ IRResultAWF.stack-budget rec-result) →
          P (next-slot alloc +ℕ layer-capacity wf-Id wfG alg)
        bridge-slot-bound P pf = subst (λ b → P (next-slot alloc +ℕ b)) stack-budget-rec-eq pf

    -- Sum inj₁ case (LINEAR): process left branch, update pointer in-place, return container
    --
    -- Linear trace structure:
    --   1. load-indirect-suc  -- Output := payload-loc (read from sucLoc input-loc)
    --   2. mov-to-input       -- Input1 := payload-loc
    --   3. [sub-trace]        -- recursive processing, Output := processed-result-loc
    --   4. store-indirect-suc -- *(sucLoc input-loc)... wait, Input1 changed!
    --
    -- Issue: After step 2-3, Input1 = payload-loc, but step 4 needs Input1 = input-loc
    -- Solution: Save input-loc to stack before step 1, restore after step 3
    --
    -- Correct linear trace:
    --   1. store-at-slot save-slot   -- Save input-loc
    --   2. load-indirect-suc         -- Output := payload-loc
    --   3. mov-to-input              -- Input1 := payload-loc
    --   4. [sub-trace]               -- Output := processed-result-loc
    --   5. restore-input save-slot   -- Input1 := input-loc (restored)
    --   6. store-indirect-suc        -- *(sucLoc input-loc) := processed-result-loc
    --   7. mov-to-output             -- Output := input-loc
    --
    -- Result: result-loc = input-loc (the Sum container with updated pointer)
    --
    process-layer {G = G} (wf-Sum {FL} {FR} wfL wfR) wfG alg dispatch (inj₁ l-layer) mIn input-loc s alloc
      n rec procRec size-bound (valid-inl-wf {payload-loc = payload-loc} {mA = mA} lmm payload-ptr payload-bf sucLoc-bf l-layer-valid) input-before not-halted rdi-eq =
      let
        -- Step 1: Setup trace - load payload pointer and set Input1
        -- This transforms s (where Input1 = input-loc) to s-setup (where Input1 = payload-loc)
        setup-trace : AbstractTrace
        setup-trace = load-indirect-suc ∷ mov-to-input ∷ []

        -- Execute setup trace to get state where Input1 = payload-loc
        s-after-load : LocState FS
        s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)

        alloc-after-load : AllocState {FS}
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)

        -- After load-indirect-suc: Output = payload-loc (from sucLoc input-loc)
        -- The payload-ptr proof tells us: readLoc s (sucLoc input-loc) ≡ just (SV-Ptr payload-loc)
        -- exec-abstract load-indirect-suc reads from sucLoc(Input1) = sucLoc(input-loc)
        -- and writes the result to Output

        -- Then mov-to-input copies Output to Input1
        s-setup : LocState FS
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)

        alloc-setup : AllocState {FS}
        alloc-setup = proj₂ (exec-abstract mov-to-input s-after-load alloc-after-load)

        -- At s-setup: Input1 = payload-loc, so rdi-eq is satisfied for recursive call
        -- Proof: load-indirect-suc sets Output to value at sucLoc(Input1)
        --        Since Input1 = input-loc and payload-ptr says sucLoc(input-loc) contains payload-loc,
        --        Output = payload-loc
        --        Then mov-to-input copies Output to Input1, so Input1 = payload-loc
        rdi-setup : readReg (regs s-setup) Input1 ≡ SV-Ptr payload-loc
        rdi-setup = setup-trace-sets-input s alloc input-loc (SV-Ptr payload-loc) not-halted rdi-eq payload-ptr

        -- The setup trace (load-indirect-suc ; mov-to-input) writes only
        -- registers, so it preserves memory and alloc.  Transfer the left
        -- payload's validity along the state change (mem-preserved) and the
        -- alloc identity (subst).  Mode = the payload's own mode mA (as in
        -- the Prod case), independent of the explicit recursion mode.
        l-layer-valid-setup : ValidAtWF mA alloc-setup {⟦ FL ⟧T (μ-type G)} (coerce-functor⁻¹ FL (μ-type G) l-layer) payload-loc s-setup
        l-layer-valid-setup =
          subst (λ al → ValidAtWF mA al (coerce-functor⁻¹ FL (μ-type G) l-layer) payload-loc s-setup)
            (sym (setup-trace-preserves-alloc s alloc))
            (validityWF-mem-preserved (coerce-functor⁻¹ FL (μ-type G) l-layer) payload-loc s s-setup
              payload-bf
              (λ loc' _ → trans (exec-abstract-mov-to-input-preserves-mem s-after-load alloc-after-load loc')
                                (exec-abstract-load-indirect-suc-preserves-mem s alloc loc'))
              l-layer-valid)

        payload-bf-setup : BeforeFrontier alloc-setup payload-loc
        payload-bf-setup = subst (λ a → BeforeFrontier a payload-loc)
                             (sym (setup-trace-preserves-alloc s alloc)) payload-bf

        -- Halted preserved through setup
        not-halted-setup : halted s-setup ≡ false
        not-halted-setup = setup-trace-preserves-halted s alloc input-loc (SV-Ptr payload-loc) not-halted rdi-eq payload-ptr

        -- Step 2: Process left sub-layer (recursive call)
        (mL , l-result) = procRec wfL (fsize-inj-left _ _) l-layer mIn payload-loc s-setup alloc-setup
                            (child-bound-inj₁ wfG l-layer size-bound) l-layer-valid-setup payload-bf-setup not-halted-setup rdi-setup

        -- Extract recursive results
        l-processed = ProcessedLayerResult.processed l-result
        s-after-sub = ProcessedLayerResult.final-state l-result
        l-result-loc = place-loc (ProcessedLayerResult.result-place l-result)
        sub-trace = ProcessedLayerResult.trace l-result
        -- Architectural split: compile-time vs runtime alloc
        -- Use ProcessedLayerResult.final-alloc for frontier properties (has frontier invariants)
        alloc-after-sub = ProcessedLayerResult.final-alloc l-result
        -- Runtime execution result (for trace composition proofs only)
        alloc-after-sub-runtime = proj₂ (exec-trace sub-trace s-setup alloc-setup)
        l-valid = place-valid (ProcessedLayerResult.result-place l-result)
        l-before = place-before (ProcessedLayerResult.result-place l-result)
        l-rax = place-rax (ProcessedLayerResult.result-place l-result)
        l-not-halted = ProcessedLayerResult.not-halted l-result

        -- Wrap in inj₁
        processed = inj₁ l-processed

        ------------------------------------------------------------------------
        -- Frontier Allocation Model for Sum Wrapper
        --
        -- The cata algebra (F A → A) can produce arbitrary-sized output at the
        -- frontier. For example, dupEven might produce 1 or 2 list cells per
        -- element. The algebra allocates as it runs, appending to the frontier.
        --
        -- For LAYER PROCESSING (this code), we need to build an F A structure
        -- to pass to the algebra. For Sum, this means wrapping the recursive
        -- result in an inj₁/inj₂ container.
        --
        -- NON-LINEAR (shared data) approach - allocate new wrapper at frontier:
        --   1. Process payload recursively → result-loc in rax
        --   2. Allocate 2 slots at frontier for Sum wrapper [tag, ptr]
        --   3. Write result-loc to wrapper slot 1 (pointer to processed payload)
        --   4. Return wrapper address in rax
        --
        -- TAG HANDLING: In the abstract model, we do NOT write the tag slot.
        --   - valid-inl-wf only checks the pointer slot (sucLoc sum-loc), not the tag
        --   - The Agda type (inj₁ vs inj₂) tracks which variant we have
        --   - getTag is a simplified placeholder; actual tags are backend-specific
        --   - Concrete backends (x86, etc.) write actual tag values during codegen
        -- The tag slot (wrapper-base) remains uninitialized in this abstract model.
        --
        -- LINEAR (unique data) approach - update container in place:
        --   1. Save input-loc to stack
        --   2. Process payload recursively → result-loc in rax
        --   3. Restore input-loc, update input-loc+1 to point to result-loc
        --   4. Return input-loc (original container, now updated)
        ------------------------------------------------------------------------

        -- NOTE: Wrapper definitions (wrapper-base, wrapper-trace, etc.) are below
        -- after l-reclaimable is defined, since wrapper-base = l-reclaimable.

        -- Trace execution correctness
        -- Full trace: setup ++ sub ++ wrapper
        -- exec-trace executes left-to-right
        setup-exec-eq : exec-trace setup-trace s alloc ≡ (s-setup , alloc-setup)
        setup-exec-eq = setup-trace-exec s alloc input-loc (SV-Ptr payload-loc) not-halted rdi-eq payload-ptr

        -- After setup ++ sub: state uses trace-correct, alloc uses runtime
        -- Note: alloc-after-sub ≠ alloc-after-sub-runtime (architectural mismatch)
        -- This proof only needed for trace composition, so use runtime value
        setup-sub-exec-runtime-eq : exec-trace (setup-trace ++ sub-trace) s alloc ≡ (s-after-sub , alloc-after-sub-runtime)
        setup-sub-exec-runtime-eq =
          trans (exec-trace-append setup-trace sub-trace s alloc)
                (trans (cong (λ p → exec-trace sub-trace (proj₁ p) (proj₂ p)) setup-exec-eq)
                       (cong₂ _,_ (ProcessedLayerResult.trace-correct l-result) refl))

        -- NOTE: trace-correct-inj1 is defined after full-trace below.

        -- Invariant composition using setup-trace-preserves-alloc
        alloc-setup-eq : alloc-setup ≡ alloc
        alloc-setup-eq = setup-trace-preserves-alloc s alloc

        -- Frontier invariants from ProcessedLayerResult (apply to alloc-after-sub = final-alloc)
        frame-preserved-inj1 : current-frame alloc-after-sub ≡ current-frame alloc
        frame-preserved-inj1 =
          trans (ProcessedLayerResult.frame-preserved l-result)
                (cong current-frame alloc-setup-eq)

        -- Bridge: runtime and compile-time allocs have same frame
        runtime-compile-frame-eq : current-frame alloc-after-sub-runtime ≡ current-frame alloc-after-sub
        runtime-compile-frame-eq =
          trans (SMP.TracePrimitives.exec-trace-preserves-frame sub-trace s-setup alloc-setup)
                (trans (cong current-frame alloc-setup-eq)
                       (sym frame-preserved-inj1))

        slot-monotone-inj1 : next-slot alloc ≤ next-slot alloc-after-sub
        slot-monotone-inj1 =
          subst (λ al → next-slot al ≤ next-slot alloc-after-sub)
                alloc-setup-eq
                (ProcessedLayerResult.slot-monotone l-result)

        -- Slot usage bound: sub-result uses ≤ product-depth wfL slots,
        -- which is ≤ product-depth wfL ⊔ product-depth wfR = product-depth (wf-Sum wfL wfR)
        -- Reclamation: inherit from sub-result
        l-reclaimable : ℕ
        l-reclaimable = next-slot (ProcessedLayerResult.final-alloc l-result)

        reclaim-mono-inj1 : next-slot alloc ≤ l-reclaimable
        reclaim-mono-inj1 = subst (λ al → next-slot al ≤ l-reclaimable)
                                  alloc-setup-eq
                                  (ProcessedLayerResult.slot-monotone l-result)

        reclaim-bounded-inj1 : l-reclaimable ≡ next-slot alloc-after-sub
        reclaim-bounded-inj1 = refl

        ------------------------------------------------------------------------
        -- Wrapper definitions
        ------------------------------------------------------------------------

        -- OCP-0003: ACTUAL RECLAMATION
        -- The wrapper must be allocated at l-reclaimable (child's reclaimable-slot),
        -- NOT at next-slot alloc-after-sub. This enables tight slot-usage-bound proofs.
        --
        -- With actual reclamation:
        --   wrapper-base = l-reclaimable
        --   next-slot alloc-after-wrapper = l-reclaimable + 2
        --   reclaimable-slot = l-reclaimable + 2 (tight allocation for Sum)
        --
        -- Proof: l-reclaimable + 2 ≤ (start + capL) + 2 ≤ start + (2 + (capL ⊔ capR))
        --        = start + layer-capacity (wf-Sum wfL wfR)

        -- Wrapper base is at child's reclaimable-slot (ACTUAL RECLAMATION)
        wrapper-base : ℕ
        wrapper-base = l-reclaimable

        -- Reclaim instruction to reset next-slot before wrapper allocation
        reclaim-instr : AbstractInstr
        reclaim-instr = instr-reclaim-to l-reclaimable

        -- State after reclaim: same LocState, updated alloc with next-slot = l-reclaimable
        alloc-reclaimed : AllocState {FS}
        alloc-reclaimed = record alloc-after-sub { next-slot = l-reclaimable }

        -- Wrapper allocation trace (same structure, but now starts from reclaimed position):
        --   1. instr-alloc-stack 2: reserve slots [wrapper-base, wrapper-base+1]
        --   2. store-at-slot (wrapper-base+1): write result pointer (rax) to ptr slot
        --   3. lea-slot wrapper-base: put wrapper address in rax
        -- Note: tag slot (wrapper-base) is not written; see TAG HANDLING above.
        wrapper-trace : AbstractTrace
        wrapper-trace = instr-alloc-stack 2 ∷
                        store-at-slot (suc wrapper-base) ∷
                        lea-slot wrapper-base ∷
                        []

        -- Combined reclaim + wrapper trace
        reclaim-wrapper-trace : AbstractTrace
        reclaim-wrapper-trace = reclaim-instr ∷ wrapper-trace

        -- Full trace: setup ++ sub-trace ++ reclaim-instr ∷ wrapper-trace
        full-trace : AbstractTrace
        full-trace = setup-trace ++ sub-trace ++ reclaim-wrapper-trace

        -- Execute reclaim + wrapper trace from alloc-after-sub
        -- After reclaim-instr, alloc changes to alloc-reclaimed (next-slot = l-reclaimable)
        s-after-wrapper : LocState FS
        s-after-wrapper = proj₁ (exec-trace reclaim-wrapper-trace s-after-sub alloc-after-sub)

        alloc-after-wrapper : AllocState {FS}
        alloc-after-wrapper = proj₂ (exec-trace reclaim-wrapper-trace s-after-sub alloc-after-sub)

        -- The wrapper location at wrapper-base (= l-reclaimable, child's reclaimed slot)
        wrapper-loc : ValueLocation FS
        wrapper-loc = AtStack (current-frame alloc-after-sub) wrapper-base

        ------------------------------------------------------------------------

        -- Full trace ends at (s-after-wrapper, alloc-after-wrapper)
        -- Note: uses reclaim-wrapper-trace instead of just wrapper-trace
        -- Bridge runtime and compile-time alloc using exec-trace-same-frame
        trace-correct-inj1 : proj₁ (exec-trace full-trace s alloc) ≡ s-after-wrapper
        trace-correct-inj1 =
          trans (cong proj₁ (exec-trace-append (setup-trace ++ sub-trace) reclaim-wrapper-trace s alloc))
                (trans (cong (λ p → proj₁ (exec-trace reclaim-wrapper-trace (proj₁ p) (proj₂ p))) setup-sub-exec-runtime-eq)
                       (exec-trace-same-frame reclaim-wrapper-trace s-after-sub alloc-after-sub-runtime alloc-after-sub
                         runtime-compile-frame-eq))

        -- Plan 0.14: alloc-correct for inj1 layer.
        -- runtime alloc-after-sub ≡ alloc-after-sub (via l-result.alloc-correct).
        -- alloc-after-wrapper = proj₂ exec-trace reclaim-wrapper-trace s-after-sub alloc-after-sub (def).
        alloc-after-sub-runtime-eq-construction :
          alloc-after-sub-runtime ≡ alloc-after-sub
        alloc-after-sub-runtime-eq-construction = ProcessedLayerResult.alloc-correct l-result

        alloc-correct-inj1 : proj₂ (exec-trace full-trace s alloc) ≡ alloc-after-wrapper
        alloc-correct-inj1 =
          trans (cong proj₂ (exec-trace-append (setup-trace ++ sub-trace) reclaim-wrapper-trace s alloc))
                (trans (cong (λ p → proj₂ (exec-trace reclaim-wrapper-trace (proj₁ p) (proj₂ p))) setup-sub-exec-runtime-eq)
                       (cong (λ a → proj₂ (exec-trace reclaim-wrapper-trace s-after-sub a))
                             alloc-after-sub-runtime-eq-construction))

        -- Slot usage bound: sub-result bound applies since alloc-setup ≡ alloc
        -- Child's bound uses layer-capacity wfL wfG alg
        slot-usage-bound-inj1 : l-reclaimable ≤ next-slot alloc +ℕ layer-capacity wfL wfG alg
        slot-usage-bound-inj1 = subst (λ al → l-reclaimable ≤ next-slot al +ℕ layer-capacity wfL wfG alg)
                                      alloc-setup-eq
                                      (ProcessedLayerResult.slot-usage-bound l-result)

        -- Max slot used: maximum of child's max-slot-used and wrapper allocation (l-reclaimable + 2)
        -- The child may have written above l-reclaimable before reclamation
        l-max-slot-used : ℕ
        l-max-slot-used = ProcessedLayerResult.max-slot-used l-result

        max-slot-used-inj1 : ℕ
        max-slot-used-inj1 = l-max-slot-used ⊔ (l-reclaimable +ℕ 2)

        -- l-max-slot-used ≤ start + layer-capacity wfL (from child's bound, adjusted for alloc-setup ≡ alloc)
        l-max-slot-usage-bound : l-max-slot-used ≤ next-slot alloc +ℕ layer-capacity wfL wfG alg
        l-max-slot-usage-bound = subst (λ al → l-max-slot-used ≤ next-slot al +ℕ layer-capacity wfL wfG alg)
                                       alloc-setup-eq
                                       (ProcessedLayerResult.max-slot-usage-bound l-result)

        heap-monotone-inj1 : next-heap-ref alloc ≤ next-heap-ref alloc-after-sub
        heap-monotone-inj1 =
          subst (λ al → next-heap-ref al ≤ next-heap-ref alloc-after-sub)
                alloc-setup-eq
                (ProcessedLayerResult.heap-monotone l-result)

        -- heap-preserved: chains through sub-result and setup-alloc equality
        heap-preserved-inj1 : next-heap-ref alloc-after-sub ≡ next-heap-ref alloc
        heap-preserved-inj1 =
          trans (ProcessedLayerResult.heap-preserved l-result)
                (cong next-heap-ref alloc-setup-eq)

        -- Note: capacity-preserved-inj1 removed in Phase 3

        -- Memory preservation: setup preserves all memory, then sub preserves below frontier
        mem-preserved-inj1 : ∀ loc → BeforeFrontier alloc loc → readLoc s-after-sub loc ≡ readLoc s loc
        mem-preserved-inj1 loc bf =
          let bf-setup = subst (λ al → BeforeFrontier al loc) (sym alloc-setup-eq) bf
              sub-pres = ProcessedLayerResult.mem-preserved l-result loc bf-setup
              setup-pres-stack = setup-trace-preserves-stackMem s alloc
              setup-pres-heap = setup-trace-preserves-heapMem s alloc
          in trans sub-pres (readLoc-stackMem-eq s-setup s loc setup-pres-stack setup-pres-heap)

        -- Trace properties for setup trace
        -- load-indirect-suc and mov-to-input don't write to slots
        setup-twa : TraceWritesAbove (next-slot alloc) setup-trace
        setup-twa = tt  -- Neither instruction writes slots

        -- Use next-slot alloc-after-wrapper as bound (= l-reclaimable + 2 via wrapper-next-slot-eq)
        setup-twb : TraceWritesBelow (next-slot alloc-after-wrapper) setup-trace
        setup-twb = tt  -- Neither instruction writes slots

        setup-tsra : TraceSlotReadsAbove (next-slot alloc) setup-trace
        setup-tsra = tt  -- Neither instruction reads slots

        -- Use next-slot alloc-after-wrapper as bound (= l-reclaimable + 2 via wrapper-next-slot-eq)
        setup-tsrb : TraceSlotReadsBelow (next-slot alloc-after-wrapper) setup-trace
        setup-tsrb = tt  -- Neither instruction reads slots

        setup-tph : TraceWF s alloc setup-trace
        setup-tph = twf-∷ (load-indirect-suc-twf {alloc = alloc} input-loc (SV-Ptr payload-loc) rdi-eq payload-ptr)
                          (twf-∷ tt twf-[])

        -- Note: setup-tpc removed in Phase 3

        setup-tnhw : TraceNoHeapWrites setup-trace
        setup-tnhw = tt

        ------------------------------------------------------------------------
        -- Wrapper trace properties with ACTUAL RECLAMATION
        --
        -- reclaim-wrapper-trace = [instr-reclaim-to l-reclaimable,
        --                          instr-alloc-stack 2,
        --                          store-at-slot (suc wrapper-base),
        --                          lea-slot wrapper-base]
        --
        -- After reclaim: next-slot = l-reclaimable (= wrapper-base)
        -- After alloc-stack 2: next-slot = l-reclaimable + 2
        ------------------------------------------------------------------------

        -- TracePreservesHaltedP for reclaim-wrapper-trace
        reclaim-wrapper-tph : ∀ {s alloc} → TraceWF s alloc reclaim-wrapper-trace
        reclaim-wrapper-tph = twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[])))

        -- Note: reclaim-wrapper-tpc removed in Phase 3

        -- TraceNoHeapWrites for reclaim-wrapper-trace
        reclaim-wrapper-tnhw : TraceNoHeapWrites reclaim-wrapper-trace
        reclaim-wrapper-tnhw = tt

        -- Wrapper trace writes above l-reclaimable (= wrapper-base)
        -- reclaim-instr doesn't write to slots, wrapper writes at suc wrapper-base
        wrapper-twa : TraceWritesAbove wrapper-base reclaim-wrapper-trace
        wrapper-twa = n≤1+n wrapper-base , tt  -- store-at-slot (suc wrapper-base) writes above wrapper-base

        -- Wrapper trace writes below l-reclaimable + 2
        -- reclaim-instr doesn't write to slots, store-at-slot (suc wrapper-base) writes at suc wrapper-base < wrapper-base + 2
        wrapper-twb : TraceWritesBelow (wrapper-base +ℕ 2) reclaim-wrapper-trace
        wrapper-twb = subst (λ x → suc wrapper-base < x) (sym (+-comm wrapper-base 2))
                            (n<1+n (suc wrapper-base)) , tt

        -- Wrapper trace reads no slots (doesn't include slot reads)
        wrapper-tsra : TraceSlotReadsAbove (next-slot alloc) reclaim-wrapper-trace
        wrapper-tsra = tt

        wrapper-tsrb : TraceSlotReadsBelow (wrapper-base +ℕ 2) reclaim-wrapper-trace
        wrapper-tsrb = tt

        -- reclaim-wrapper-trace preserves halted=false
        reclaim-wrapper-not-halted : halted s-after-sub ≡ false → halted s-after-wrapper ≡ false
        reclaim-wrapper-not-halted nh = exec-trace-preserves-halted-WF reclaim-wrapper-trace s-after-sub alloc-after-sub nh reclaim-wrapper-tph

        -- Final alloc after reclaim + wrapper: next-slot = l-reclaimable + 2
        -- Frame is preserved, heap is preserved, capacity is preserved
        wrapper-frame-preserved : current-frame alloc-after-wrapper ≡ current-frame alloc-after-sub
        wrapper-frame-preserved = SMP.TracePrimitives.exec-trace-preserves-frame reclaim-wrapper-trace s-after-sub alloc-after-sub

        wrapper-heap-preserved : next-heap-ref alloc-after-wrapper ≡ next-heap-ref alloc-after-sub
        wrapper-heap-preserved = SMP.RecSchemeSemantics.exec-trace-preserves-heap-ref reclaim-wrapper-trace s-after-sub alloc-after-sub

        -- Note: wrapper-capacity-preserved removed in Phase 3

        -- next-slot = l-reclaimable + 2 after reclaim + wrapper
        wrapper-next-slot-eq : next-slot alloc-after-wrapper ≡ l-reclaimable +ℕ 2
        wrapper-next-slot-eq =
          let -- Split exec-trace into reclaim + wrapper
              trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub l-not-halted
              -- After reclaim: alloc has next-slot = l-reclaimable
              -- wrapper-trace-advances-slot: proj₂ (exec-trace wrapper-trace ...) has next-slot = start + 2
              alloc-after-wrapper-eq : proj₂ (exec-trace wrapper-trace s-after-sub alloc-reclaimed) ≡ wrapper-alloc-result alloc-reclaimed
              alloc-after-wrapper-eq = wrapper-trace-advances-slot wrapper-base s-after-sub alloc-reclaimed l-not-halted
              -- wrapper-alloc-result alloc-reclaimed has next-slot = l-reclaimable + 2
          in trans (cong (λ p → next-slot (proj₂ p)) trace-split)
                   (cong next-slot alloc-after-wrapper-eq)

        -- wrapper-before-frontier: wrapper-base = l-reclaimable < l-reclaimable + 2 = next-slot alloc-after-wrapper
        wrapper-before-frontier : wrapper-base < next-slot alloc-after-wrapper
        wrapper-before-frontier = subst (λ x → wrapper-base < x) (sym wrapper-next-slot-eq)
                                        (m<m+n wrapper-base {2} (s≤s z≤n))

        -- After lea-slot, Output register contains SV-Ptr wrapper-loc
        -- reclaim-instr doesn't change regs, so wrapper-trace-output still applies
        wrapper-rax-result : readReg (regs s-after-wrapper) Output ≡ SV-Ptr wrapper-loc
        wrapper-rax-result =
          let trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub l-not-halted
              output-eq = wrapper-trace-output wrapper-base s-after-sub alloc-reclaimed l-not-halted
          in trans (cong (λ p → readReg (regs (proj₁ p)) Output) trace-split) output-eq

        -- The pointer slot (wrapper-base + 1) was written with l-result-loc
        wrapper-ptr-written : readLoc s-after-wrapper (sucLoc wrapper-loc) ≡ just (SV-Ptr l-result-loc)
        wrapper-ptr-written =
          let trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub l-not-halted
              -- Before wrapper-trace: rax = l-result-loc (from child's rax-is-result)
              rax-before = place-rax (ProcessedLayerResult.result-place l-result)
              -- wrapper-trace-ptr-written: slot (suc base) contains original Output value
              ptr-eq : readLoc (proj₁ (exec-trace wrapper-trace s-after-sub alloc-reclaimed))
                               (AtStack (current-frame alloc-reclaimed) (suc wrapper-base)) ≡
                       just (readReg (regs s-after-sub) Output)
              ptr-eq = wrapper-trace-ptr-written wrapper-base s-after-sub alloc-reclaimed l-not-halted
          in trans (cong (λ p → readLoc (proj₁ p) (sucLoc wrapper-loc)) trace-split)
                   (trans ptr-eq (cong just rax-before))

        -- Memory preservation: reclaim doesn't change memory, wrapper writes above l-reclaimable
        -- For locations BeforeFrontier alloc, their slot < next-slot alloc ≤ l-reclaimable = wrapper-base
        wrapper-mem-preserved : ∀ loc → BeforeFrontier alloc loc →
                                readLoc s-after-wrapper loc ≡ readLoc s-after-sub loc
        wrapper-mem-preserved loc bf =
          let trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub l-not-halted
              -- loc is BeforeFrontier alloc, and next-slot alloc ≤ l-reclaimable = wrapper-base
              -- So loc is BeforeFrontier alloc-reclaimed as well
              -- frame-preserved-inj1 : current-frame alloc-after-sub ≡ current-frame alloc
              -- alloc-reclaimed = record alloc-after-sub { next-slot = l-reclaimable }
              -- So current-frame alloc-reclaimed = current-frame alloc-after-sub
              bf-reclaimed : BeforeFrontier alloc-reclaimed loc
              bf-reclaimed = frontier-monotone alloc alloc-reclaimed
                               (sym frame-preserved-inj1)
                               reclaim-mono-inj1
                               (subst (next-heap-ref alloc ≤_) (sym heap-preserved-inj1) ≤-refl)
                               loc bf
              -- wrapper-trace preserves memory at bf-reclaimed locations
              mem-eq = wrapper-trace-mem-preserved wrapper-base s-after-sub alloc-reclaimed loc l-not-halted refl bf-reclaimed
          in trans (cong (λ p → readLoc (proj₁ p) loc) trace-split) mem-eq

        -- For processed-valid (valid-inl-wf), we need:
        -- 1. BeforeFrontier alloc-after-wrapper l-result-loc
        --    l-before : BeforeFrontier alloc-after-sub l-result-loc
        --    With actual reclamation, l-result-loc's slot < l-reclaimable = wrapper-base
        --    Since next-slot alloc-after-wrapper = l-reclaimable + 2 > l-reclaimable,
        --    l-result-loc is still before the new frontier.
        -- TODO (post-scaffold): alloc-setup-eq chain doesn't reduce under
        -- StoredValue because exec-abstract load-indirect-suc has a
        -- non-trivial with-block on sv-as-loc Input1. The proof composes
        -- but cong needs an explicit witness from the InstrWF chain.
        l-before-wrapper : BeforeFrontier alloc-after-wrapper l-result-loc
        l-before-wrapper = SMP.!!

        -- 2. BeforeFrontier alloc-after-wrapper (sucLoc wrapper-loc)
        --    sucLoc wrapper-loc = AtStack frame (suc wrapper-base) = AtStack frame (suc l-reclaimable)
        --    suc l-reclaimable < l-reclaimable + 2 = next-slot alloc-after-wrapper
        wb+2≡sswb : wrapper-base +ℕ 2 ≡ suc (suc wrapper-base)
        wb+2≡sswb = +-comm wrapper-base 2

        suc-wrapper-lt : suc wrapper-base < next-slot alloc-after-wrapper
        suc-wrapper-lt = subst (λ x → suc wrapper-base < x)
                               (trans (sym wb+2≡sswb) (sym wrapper-next-slot-eq))
                               (n<1+n (suc wrapper-base))

        suc-wrapper-before : BeforeFrontier alloc-after-wrapper (sucLoc wrapper-loc)
        suc-wrapper-before = stack-before (sym wrapper-frame-preserved) suc-wrapper-lt

        -- 3. ValidAtWF for l-processed at l-result-loc in alloc-after-wrapper
        --    With actual reclamation, reclaim-instr doesn't change memory, wrapper writes at suc l-reclaimable.
        --    l-result-loc's slot < l-reclaimable (child result is before child's reclaimable-slot),
        --    so it's disjoint from the wrapper write at suc l-reclaimable.

        l-valid-wrapper : ValidAtWF mL alloc-after-wrapper l-processed l-result-loc s-after-wrapper
        l-valid-wrapper =
          -- Strategy:
          -- TODO (post-scaffold): alloc-setup-eq chain doesn't reduce
          -- under StoredValue (load-indirect-suc has a with-block on
          -- sv-as-loc Input1); rederive once that propagates.
          SMP.!!

        -- Plan 0.14 (Camp 2): wrapper-loc is AtStack so wrapper-mode = Stack
        -- (matching the function's returned mode). lmm = tt then.
        processed-valid-proof : ValidAtWF Stack alloc-after-wrapper processed wrapper-loc s-after-wrapper
        processed-valid-proof = valid-inl-wf tt wrapper-ptr-written l-before-wrapper suc-wrapper-before l-valid-wrapper

        -- result-before: wrapper-base = l-reclaimable < l-reclaimable + 2 = next-slot alloc-after-wrapper
        result-before-proof : BeforeFrontier alloc-after-wrapper wrapper-loc
        result-before-proof = stack-before (sym wrapper-frame-preserved) wrapper-before-frontier

        -- slot-usage-bound proof (reused for slot-stays-in-budget)
        -- Since reclaimable-slot = next-slot final-alloc, both fields need the same proof
        slot-usage-and-budget-proof : next-slot alloc-after-wrapper ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
        slot-usage-and-budget-proof = sum-left-slot-budget wfL wfR wfG alg alloc l-reclaimable alloc-after-wrapper wrapper-next-slot-eq slot-usage-bound-inj1

      in
      -- Plan 0.14 (Camp 2): wrapper-loc is AtStack, so wrapper mode = Stack.
      -- This is independent of sub-layer's mode mL (which may be Stack or Heap).
      Stack , record
        { processed = processed
        ; trace = full-trace
        ; final-state = s-after-wrapper
        ; final-alloc = alloc-after-wrapper
        ; bump = bump-+ (ProcessedLayerResult.bump l-result) (mkBump 2 0)
        ; final-alloc-eq = sum-bump-eq (ProcessedLayerResult.bump l-result)
            alloc alloc-after-sub alloc-after-wrapper alloc-setup
            (setup-trace-preserves-alloc s alloc)
            (ProcessedLayerResult.final-alloc-eq l-result)
            wrapper-frame-preserved wrapper-next-slot-eq wrapper-heap-preserved
        ; trace-no-frame-ops =
            SMP.trace-no-frame-ops-append setup-trace (sub-trace ++ reclaim-wrapper-trace)
              (tt , tt , tt)
              (SMP.trace-no-frame-ops-append sub-trace reclaim-wrapper-trace
                (ProcessedLayerResult.trace-no-frame-ops l-result)
                (tt , tt , tt , tt , tt))
        ; trace-correct = trace-correct-inj1
        ; alloc-correct = alloc-correct-inj1
        ; result-place = at-loc wrapper-loc processed-valid-proof result-before-proof wrapper-rax-result processed-valid-proof result-before-proof
        ; not-halted = reclaim-wrapper-not-halted l-not-halted
        ; semantic-correct = cong inj₁ (ProcessedLayerResult.semantic-correct l-result)
        ; frame-preserved = trans wrapper-frame-preserved frame-preserved-inj1
        -- slot-monotone: next-slot alloc ≤ l-reclaimable + 2 = next-slot alloc-after-wrapper
        ; slot-monotone = subst (λ x → next-slot alloc ≤ x) (sym wrapper-next-slot-eq)
                                (≤-trans reclaim-mono-inj1 (m≤m+n l-reclaimable 2))
        -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-preserves-*
        ; slot-usage-bound = slot-usage-and-budget-proof
        -- max-slot-used: max of child's max-slot-used and wrapper allocation
        ; max-slot-used = max-slot-used-inj1
        -- max-slot-geq-final: next-slot final-alloc ≤ max-slot-used
        -- next-slot alloc-after-wrapper = l-reclaimable + 2 (by wrapper-next-slot-eq)
        -- l-reclaimable + 2 ≤ max-slot-used-inj1 (by n≤m⊔n)
        ; max-slot-geq-final = subst (_≤ max-slot-used-inj1) (sym wrapper-next-slot-eq)
                                     (n≤m⊔n l-max-slot-used (l-reclaimable +ℕ 2))
        ; max-slot-usage-bound =
            -- max-slot-used-inj1 = l-max-slot-used ⊔ (l-reclaimable + 2)
            -- Need: max-slot-used-inj1 ≤ next-slot alloc + layer-capacity (wf-Sum wfL wfR)
            let -- l-max-slot-used ≤ next-slot alloc + layer-capacity wfL (from l-max-slot-usage-bound)
                -- layer-capacity wfL ≤ layer-capacity (wf-Sum wfL wfR)
                -- layer-capacity (wf-Sum wfL wfR) = 2 + (capL ⊔ capR) ≥ capL ⊔ capR ≥ capL
                child-cap-bound : layer-capacity wfL wfG alg ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
                child-cap-bound = ≤-trans (m≤m⊔n (layer-capacity wfL wfG alg) (layer-capacity wfR wfG alg))
                                          (m≤n+m (layer-capacity wfL wfG alg ⊔ layer-capacity wfR wfG alg) 2)
                l-max-bound : l-max-slot-used ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                l-max-bound = ≤-trans l-max-slot-usage-bound (+-monoʳ-≤ (next-slot alloc) child-cap-bound)
                -- l-reclaimable + 2 ≤ next-slot alloc + layer-capacity (wf-Sum wfL wfR) (from slot-usage-bound proof)
                wrapper-bound : l-reclaimable +ℕ 2 ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                wrapper-bound =
                  let step1 = +-monoˡ-≤ 2 slot-usage-bound-inj1
                      step2 = +-assoc (next-slot alloc) (layer-capacity wfL wfG alg) 2
                      fits = sum-wrapper-fits-left wfL wfR wfG alg
                      step3 = +-monoʳ-≤ (next-slot alloc) fits
                  in ≤-trans (subst (l-reclaimable +ℕ 2 ≤_) step2 step1) step3
            in ⊔-lub l-max-bound wrapper-bound
        ; slot-stays-in-budget = slot-usage-and-budget-proof
        -- heap-monotone: heap unchanged by wrapper trace
        ; heap-monotone = subst (λ x → next-heap-ref alloc ≤ x) (sym wrapper-heap-preserved) heap-monotone-inj1
        -- heap-preserved: chain through wrapper (preserves heap) and sub-result (heap-preserved-inj1)
        ; heap-preserved = trans wrapper-heap-preserved heap-preserved-inj1
        -- mem-preserved: memory below original frontier preserved through full trace
        -- Chain: wrapper-mem-preserved ∘ mem-preserved-inj1
        -- wrapper-mem-preserved now takes BeforeFrontier alloc directly
        ; mem-preserved = λ loc bf → trans (wrapper-mem-preserved loc bf) (mem-preserved-inj1 loc bf)
        -- Trace region bounds: full-trace = setup-trace ++ sub-trace ++ reclaim-wrapper-trace
        -- sub-trace bounds are relative to alloc-setup, but alloc-setup ≡ alloc
        -- With max-slot-used = l-max-slot-used ⊔ (l-reclaimable + 2), proofs go through
        ; trace-writes-above = SMP.trace-writes-above-append (next-slot alloc) setup-trace (sub-trace ++ reclaim-wrapper-trace)
            setup-twa (SMP.trace-writes-above-append (next-slot alloc) sub-trace reclaim-wrapper-trace
              (subst (λ al → TraceWritesAbove (next-slot al) sub-trace) alloc-setup-eq
                     (ProcessedLayerResult.trace-writes-above l-result))
              (SMP.trace-writes-above-mono (next-slot alloc) l-reclaimable reclaim-wrapper-trace
                     reclaim-mono-inj1 wrapper-twa))
        -- trace-writes-below: Using max-slot-used = l-max-slot-used ⊔ (l-reclaimable + 2)
        -- setup: no writes (tt)
        -- sub-trace: writes below l-max-slot-used ≤ max-slot-used (via m≤m⊔n)
        -- wrapper: writes below l-reclaimable + 2 ≤ max-slot-used (via n≤m⊔n)
        ; trace-writes-below = SMP.trace-writes-below-append max-slot-used-inj1 setup-trace (sub-trace ++ reclaim-wrapper-trace)
            tt (SMP.trace-writes-below-append max-slot-used-inj1 sub-trace reclaim-wrapper-trace
              (SMP.trace-writes-below-mono l-max-slot-used max-slot-used-inj1 sub-trace
                 (m≤m⊔n l-max-slot-used (l-reclaimable +ℕ 2))
                 (ProcessedLayerResult.trace-writes-below l-result))
              (SMP.trace-writes-below-mono (l-reclaimable +ℕ 2) max-slot-used-inj1 reclaim-wrapper-trace
                 (n≤m⊔n l-max-slot-used (l-reclaimable +ℕ 2)) wrapper-twb))
        ; trace-slot-reads-above = SMP.trace-slot-reads-above-append (next-slot alloc) setup-trace (sub-trace ++ reclaim-wrapper-trace)
            setup-tsra (SMP.trace-slot-reads-above-append (next-slot alloc) sub-trace reclaim-wrapper-trace
              (subst (λ al → TraceSlotReadsAbove (next-slot al) sub-trace) alloc-setup-eq
                     (ProcessedLayerResult.trace-slot-reads-above l-result))
              wrapper-tsra)
        -- trace-slot-reads-below: Using max-slot-used = l-max-slot-used ⊔ (l-reclaimable + 2)
        ; trace-slot-reads-below = SMP.trace-slot-reads-below-append max-slot-used-inj1 setup-trace (sub-trace ++ reclaim-wrapper-trace)
            tt (SMP.trace-slot-reads-below-append max-slot-used-inj1 sub-trace reclaim-wrapper-trace
              (SMP.trace-slot-reads-below-mono l-max-slot-used max-slot-used-inj1 sub-trace
                 (m≤m⊔n l-max-slot-used (l-reclaimable +ℕ 2))
                 (ProcessedLayerResult.trace-slot-reads-below l-result))
              (SMP.trace-slot-reads-below-mono (l-reclaimable +ℕ 2) max-slot-used-inj1 reclaim-wrapper-trace
                 (n≤m⊔n l-max-slot-used (l-reclaimable +ℕ 2)) wrapper-tsrb))
        ; trace-twf = twf-++ not-halted setup-tph
            (subst (λ st → TraceWF st (proj₂ (exec-trace setup-trace s alloc)) (sub-trace ++ reclaim-wrapper-trace))
                   (sym (cong proj₁ setup-exec-eq))
              (subst (λ al → TraceWF s-setup al (sub-trace ++ reclaim-wrapper-trace))
                     (sym (cong proj₂ setup-exec-eq))
                (twf-++ not-halted-setup (ProcessedLayerResult.trace-twf l-result) reclaim-wrapper-tph)))
        -- scratch-bounded = max-slot-usage-bound (same proof, INPUT-relative)
        ; scratch-bounded =
            let child-cap-bound : layer-capacity wfL wfG alg ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
                child-cap-bound = ≤-trans (m≤m⊔n (layer-capacity wfL wfG alg) (layer-capacity wfR wfG alg))
                                          (m≤n+m (layer-capacity wfL wfG alg ⊔ layer-capacity wfR wfG alg) 2)
                l-max-bound : l-max-slot-used ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                l-max-bound = ≤-trans l-max-slot-usage-bound (+-monoʳ-≤ (next-slot alloc) child-cap-bound)
                wrapper-bound : l-reclaimable +ℕ 2 ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                wrapper-bound =
                  let step1 = +-monoˡ-≤ 2 slot-usage-bound-inj1
                      step2 = +-assoc (next-slot alloc) (layer-capacity wfL wfG alg) 2
                      fits = sum-wrapper-fits-left wfL wfR wfG alg
                      step3 = +-monoʳ-≤ (next-slot alloc) fits
                  in ≤-trans (subst (l-reclaimable +ℕ 2 ≤_) step2 step1) step3
            in ⊔-lub l-max-bound wrapper-bound
        }

    ------------------------------------------------------------------------
    -- Sum inj₂ case: process right branch, allocate new wrapper (Option B)
    --
    -- OCP-0003: For the general (non-linear) case, we allocate a new wrapper
    -- at the frontier. This mirrors the inj₁ case exactly.
    --
    -- Trace structure:
    --   1. setup-trace: load payload-loc into Input1
    --   2. sub-trace: process payload recursively
    --   3. wrapper-trace: allocate Sum wrapper at frontier
    ------------------------------------------------------------------------
    process-layer {G = G} (wf-Sum {FL} {FR} wfL wfR) wfG alg dispatch (inj₂ r-layer) mIn input-loc s alloc
      n rec procRec size-bound (valid-inr-wf {payload-loc = payload-loc} {mB = mB} lmm payload-ptr payload-bf sucLoc-bf r-layer-valid) input-before not-halted rdi-eq =
      let
        -- Step 1: Setup trace - load payload pointer and set Input1
        -- This transforms s (where Input1 = input-loc) to s-setup (where Input1 = payload-loc)
        setup-trace : AbstractTrace
        setup-trace = load-indirect-suc ∷ mov-to-input ∷ []

        -- Execute setup trace to get state where Input1 = payload-loc
        s-after-load : LocState FS
        s-after-load = proj₁ (exec-abstract load-indirect-suc s alloc)

        alloc-after-load : AllocState {FS}
        alloc-after-load = proj₂ (exec-abstract load-indirect-suc s alloc)

        -- Then mov-to-input copies Output to Input1
        s-setup : LocState FS
        s-setup = proj₁ (exec-abstract mov-to-input s-after-load alloc-after-load)

        alloc-setup : AllocState {FS}
        alloc-setup = proj₂ (exec-abstract mov-to-input s-after-load alloc-after-load)

        -- At s-setup: Input1 = payload-loc
        rdi-setup : readReg (regs s-setup) Input1 ≡ SV-Ptr payload-loc
        rdi-setup = setup-trace-sets-input s alloc input-loc (SV-Ptr payload-loc) not-halted rdi-eq payload-ptr

        -- TODO (post-scaffold): same alloc-setup non-reduction issue as
        -- left-layer above. Postulate the three transfers.
        r-layer-valid-setup : ValidAtWF mB alloc-setup {⟦ FR ⟧T (μ-type G)} (coerce-functor⁻¹ FR (μ-type G) r-layer) payload-loc s-setup
        r-layer-valid-setup =
          subst (λ al → ValidAtWF mB al (coerce-functor⁻¹ FR (μ-type G) r-layer) payload-loc s-setup)
            (sym (setup-trace-preserves-alloc s alloc))
            (validityWF-mem-preserved (coerce-functor⁻¹ FR (μ-type G) r-layer) payload-loc s s-setup
              payload-bf
              (λ loc' _ → trans (exec-abstract-mov-to-input-preserves-mem s-after-load alloc-after-load loc')
                                (exec-abstract-load-indirect-suc-preserves-mem s alloc loc'))
              r-layer-valid)

        payload-bf-setup : BeforeFrontier alloc-setup payload-loc
        payload-bf-setup = subst (λ a → BeforeFrontier a payload-loc)
                             (sym (setup-trace-preserves-alloc s alloc)) payload-bf

        not-halted-setup : halted s-setup ≡ false
        not-halted-setup = setup-trace-preserves-halted s alloc input-loc (SV-Ptr payload-loc) not-halted rdi-eq payload-ptr

        -- Step 2: Process right sub-layer (recursive call)
        (mR , r-result) = procRec wfR (fsize-inj-right _ _) r-layer mIn payload-loc s-setup alloc-setup
                            (child-bound-inj₂ wfG r-layer size-bound) r-layer-valid-setup payload-bf-setup not-halted-setup rdi-setup

        -- Extract recursive results
        r-processed = ProcessedLayerResult.processed r-result
        s-after-sub = ProcessedLayerResult.final-state r-result
        r-result-loc = place-loc (ProcessedLayerResult.result-place r-result)
        sub-trace = ProcessedLayerResult.trace r-result
        -- Architectural split: compile-time vs runtime alloc
        -- Use ProcessedLayerResult.final-alloc for frontier properties (has frontier invariants)
        alloc-after-sub = ProcessedLayerResult.final-alloc r-result
        -- Runtime execution result (for trace composition proofs only)
        alloc-after-sub-runtime = proj₂ (exec-trace sub-trace s-setup alloc-setup)
        r-valid = place-valid (ProcessedLayerResult.result-place r-result)
        r-before = place-before (ProcessedLayerResult.result-place r-result)
        r-rax = place-rax (ProcessedLayerResult.result-place r-result)
        r-not-halted = ProcessedLayerResult.not-halted r-result

        -- Wrap in inj₂
        processed = inj₂ r-processed

        -- Trace execution correctness
        -- Full trace: setup ++ sub ++ wrapper
        setup-exec-eq : exec-trace setup-trace s alloc ≡ (s-setup , alloc-setup)
        setup-exec-eq = setup-trace-exec s alloc input-loc (SV-Ptr payload-loc) not-halted rdi-eq payload-ptr

        -- After setup ++ sub: state uses trace-correct, alloc uses runtime
        -- Note: alloc-after-sub ≠ alloc-after-sub-runtime (architectural mismatch)
        -- This proof only needed for trace composition, so use runtime value
        setup-sub-exec-runtime-eq : exec-trace (setup-trace ++ sub-trace) s alloc ≡ (s-after-sub , alloc-after-sub-runtime)
        setup-sub-exec-runtime-eq =
          trans (exec-trace-append setup-trace sub-trace s alloc)
                (trans (cong (λ p → exec-trace sub-trace (proj₁ p) (proj₂ p)) setup-exec-eq)
                       (cong₂ _,_ (ProcessedLayerResult.trace-correct r-result) refl))

        -- Invariant composition using setup-trace-preserves-alloc
        alloc-setup-eq : alloc-setup ≡ alloc
        alloc-setup-eq = setup-trace-preserves-alloc s alloc

        frame-preserved-inj2 : current-frame alloc-after-sub ≡ current-frame alloc
        frame-preserved-inj2 =
          trans (ProcessedLayerResult.frame-preserved r-result)
                (cong current-frame alloc-setup-eq)

        -- Bridge: runtime and compile-time allocs have same frame
        runtime-compile-frame-eq : current-frame alloc-after-sub-runtime ≡ current-frame alloc-after-sub
        runtime-compile-frame-eq =
          trans (SMP.TracePrimitives.exec-trace-preserves-frame sub-trace s-setup alloc-setup)
                (trans (cong current-frame alloc-setup-eq)
                       (sym frame-preserved-inj2))

        slot-monotone-inj2 : next-slot alloc ≤ next-slot alloc-after-sub
        slot-monotone-inj2 =
          subst (λ al → next-slot al ≤ next-slot alloc-after-sub)
                alloc-setup-eq
                (ProcessedLayerResult.slot-monotone r-result)

        -- Slot usage bound: sub-result uses ≤ product-depth wfR slots
        -- Reclamation: inherit from sub-result
        r-reclaimable : ℕ
        r-reclaimable = next-slot (ProcessedLayerResult.final-alloc r-result)

        ------------------------------------------------------------------------
        -- ACTUAL RECLAMATION Model for Sum Wrapper (OCP-0003)
        --
        -- With actual reclamation, we allocate the wrapper at r-reclaimable
        -- (child's reclaimable-slot), not at next-slot alloc-after-sub.
        -- This enables tight slot-usage-bound proofs.
        ------------------------------------------------------------------------

        -- Wrapper allocation: place wrapper at child's reclaimable-slot (ACTUAL RECLAMATION)
        wrapper-base : ℕ
        wrapper-base = r-reclaimable

        -- Reclaim instruction to reset next-slot before wrapper allocation
        reclaim-instr : AbstractInstr
        reclaim-instr = instr-reclaim-to r-reclaimable

        -- State after reclaim: same LocState, updated alloc with next-slot = r-reclaimable
        alloc-reclaimed : AllocState {FS}
        alloc-reclaimed = record alloc-after-sub { next-slot = r-reclaimable }

        -- Wrapper allocation trace (same structure, but starts from reclaimed position):
        --   1. instr-alloc-stack 2: reserve slots [wrapper-base, wrapper-base+1]
        --   2. store-at-slot (wrapper-base+1): write result pointer (rax) to ptr slot
        --   3. lea-slot wrapper-base: put wrapper address in rax
        wrapper-trace : AbstractTrace
        wrapper-trace = instr-alloc-stack 2 ∷
                        store-at-slot (suc wrapper-base) ∷
                        lea-slot wrapper-base ∷
                        []

        -- Combined reclaim + wrapper trace
        reclaim-wrapper-trace : AbstractTrace
        reclaim-wrapper-trace = reclaim-instr ∷ wrapper-trace

        -- Full trace: setup ++ sub-trace ++ reclaim-instr ∷ wrapper-trace
        full-trace : AbstractTrace
        full-trace = setup-trace ++ sub-trace ++ reclaim-wrapper-trace

        -- Execute reclaim + wrapper trace from alloc-after-sub
        s-after-wrapper : LocState FS
        s-after-wrapper = proj₁ (exec-trace reclaim-wrapper-trace s-after-sub alloc-after-sub)

        alloc-after-wrapper : AllocState {FS}
        alloc-after-wrapper = proj₂ (exec-trace reclaim-wrapper-trace s-after-sub alloc-after-sub)

        -- The wrapper location at wrapper-base (= r-reclaimable, child's reclaimed slot)
        wrapper-loc : ValueLocation FS
        wrapper-loc = AtStack (current-frame alloc-after-sub) wrapper-base

        -- Full trace ends at (s-after-wrapper, alloc-after-wrapper)
        -- Note: uses reclaim-wrapper-trace instead of just wrapper-trace
        trace-correct-inj2 : proj₁ (exec-trace full-trace s alloc) ≡ s-after-wrapper
        trace-correct-inj2 =
          trans (cong proj₁ (exec-trace-append (setup-trace ++ sub-trace) reclaim-wrapper-trace s alloc))
                (trans (cong (λ p → proj₁ (exec-trace reclaim-wrapper-trace (proj₁ p) (proj₂ p))) setup-sub-exec-runtime-eq)
                       (exec-trace-same-frame reclaim-wrapper-trace s-after-sub alloc-after-sub-runtime alloc-after-sub
                         runtime-compile-frame-eq))

        -- Plan 0.14: alloc-correct for inj2 (symmetric to inj1).
        alloc-after-sub-runtime-eq-construction :
          alloc-after-sub-runtime ≡ alloc-after-sub
        alloc-after-sub-runtime-eq-construction = ProcessedLayerResult.alloc-correct r-result

        alloc-correct-inj2 : proj₂ (exec-trace full-trace s alloc) ≡ alloc-after-wrapper
        alloc-correct-inj2 =
          trans (cong proj₂ (exec-trace-append (setup-trace ++ sub-trace) reclaim-wrapper-trace s alloc))
                (trans (cong (λ p → proj₂ (exec-trace reclaim-wrapper-trace (proj₁ p) (proj₂ p))) setup-sub-exec-runtime-eq)
                       (cong (λ a → proj₂ (exec-trace reclaim-wrapper-trace s-after-sub a))
                             alloc-after-sub-runtime-eq-construction))

        reclaim-mono-inj2 : next-slot alloc ≤ r-reclaimable
        reclaim-mono-inj2 = subst (λ al → next-slot al ≤ r-reclaimable)
                                  alloc-setup-eq
                                  (ProcessedLayerResult.slot-monotone r-result)

        reclaim-bounded-inj2 : r-reclaimable ≡ next-slot alloc-after-sub
        reclaim-bounded-inj2 = refl

        -- Slot usage bound: sub-result bound applies since alloc-setup ≡ alloc
        -- Child's bound uses layer-capacity wfR wfG alg
        slot-usage-bound-inj2 : r-reclaimable ≤ next-slot alloc +ℕ layer-capacity wfR wfG alg
        slot-usage-bound-inj2 = subst (λ al → r-reclaimable ≤ next-slot al +ℕ layer-capacity wfR wfG alg)
                                      alloc-setup-eq
                                      (ProcessedLayerResult.slot-usage-bound r-result)

        -- Max slot used: maximum of child's max-slot-used and wrapper allocation (r-reclaimable + 2)
        -- The child may have written above r-reclaimable before reclamation
        r-max-slot-used : ℕ
        r-max-slot-used = ProcessedLayerResult.max-slot-used r-result

        max-slot-used-inj2 : ℕ
        max-slot-used-inj2 = r-max-slot-used ⊔ (r-reclaimable +ℕ 2)

        -- r-max-slot-used ≤ start + layer-capacity wfR (from child's bound, adjusted for alloc-setup ≡ alloc)
        r-max-slot-usage-bound : r-max-slot-used ≤ next-slot alloc +ℕ layer-capacity wfR wfG alg
        r-max-slot-usage-bound = subst (λ al → r-max-slot-used ≤ next-slot al +ℕ layer-capacity wfR wfG alg)
                                       alloc-setup-eq
                                       (ProcessedLayerResult.max-slot-usage-bound r-result)

        heap-monotone-inj2 : next-heap-ref alloc ≤ next-heap-ref alloc-after-sub
        heap-monotone-inj2 =
          subst (λ al → next-heap-ref al ≤ next-heap-ref alloc-after-sub)
                alloc-setup-eq
                (ProcessedLayerResult.heap-monotone r-result)

        -- heap-preserved: chains through sub-result and setup-alloc equality
        heap-preserved-inj2 : next-heap-ref alloc-after-sub ≡ next-heap-ref alloc
        heap-preserved-inj2 =
          trans (ProcessedLayerResult.heap-preserved r-result)
                (cong next-heap-ref alloc-setup-eq)

        -- Note: capacity-preserved-inj2 removed in Phase 3

        -- Memory preservation: setup preserves all memory, then sub preserves below frontier
        mem-preserved-inj2 : ∀ loc → BeforeFrontier alloc loc → readLoc s-after-sub loc ≡ readLoc s loc
        mem-preserved-inj2 loc bf =
          let bf-setup = subst (λ al → BeforeFrontier al loc) (sym alloc-setup-eq) bf
              sub-pres = ProcessedLayerResult.mem-preserved r-result loc bf-setup
              setup-pres-stack = setup-trace-preserves-stackMem s alloc
              setup-pres-heap = setup-trace-preserves-heapMem s alloc
          in trans sub-pres (readLoc-stackMem-eq s-setup s loc setup-pres-stack setup-pres-heap)

        -- Trace properties for setup trace
        setup-twa : TraceWritesAbove (next-slot alloc) setup-trace
        setup-twa = tt  -- Neither instruction writes slots

        -- Use next-slot alloc-after-wrapper as bound (= r-reclaimable + 2 via wrapper-next-slot-eq)
        setup-twb : TraceWritesBelow (next-slot alloc-after-wrapper) setup-trace
        setup-twb = tt  -- Neither instruction writes slots

        setup-tsra : TraceSlotReadsAbove (next-slot alloc) setup-trace
        setup-tsra = tt  -- Neither instruction reads slots

        -- Use next-slot alloc-after-wrapper as bound (= r-reclaimable + 2 via wrapper-next-slot-eq)
        setup-tsrb : TraceSlotReadsBelow (next-slot alloc-after-wrapper) setup-trace
        setup-tsrb = tt  -- Neither instruction reads slots

        setup-tph : TraceWF s alloc setup-trace
        setup-tph = twf-∷ (load-indirect-suc-twf {alloc = alloc} input-loc (SV-Ptr payload-loc) rdi-eq payload-ptr)
                          (twf-∷ tt twf-[])

        -- Note: setup-tpc removed in Phase 3

        setup-tnhw : TraceNoHeapWrites setup-trace
        setup-tnhw = tt

        ------------------------------------------------------------------------
        -- Wrapper trace properties with ACTUAL RECLAMATION
        --
        -- reclaim-wrapper-trace = [instr-reclaim-to r-reclaimable,
        --                          instr-alloc-stack 2,
        --                          store-at-slot (suc wrapper-base),
        --                          lea-slot wrapper-base]
        --
        -- After reclaim: next-slot = r-reclaimable (= wrapper-base)
        -- After alloc-stack 2: next-slot = r-reclaimable + 2
        ------------------------------------------------------------------------

        -- TracePreservesHaltedP for reclaim-wrapper-trace
        reclaim-wrapper-tph : ∀ {s alloc} → TraceWF s alloc reclaim-wrapper-trace
        reclaim-wrapper-tph = twf-∷ tt (twf-∷ tt (twf-∷ tt (twf-∷ tt twf-[])))

        -- Note: reclaim-wrapper-tpc removed in Phase 3

        -- TraceNoHeapWrites for reclaim-wrapper-trace
        reclaim-wrapper-tnhw : TraceNoHeapWrites reclaim-wrapper-trace
        reclaim-wrapper-tnhw = tt

        -- Wrapper trace writes above r-reclaimable (= wrapper-base)
        -- reclaim-instr doesn't write to slots, wrapper writes at suc wrapper-base
        wrapper-twa : TraceWritesAbove wrapper-base reclaim-wrapper-trace
        wrapper-twa = n≤1+n wrapper-base , tt  -- store-at-slot (suc wrapper-base) writes above wrapper-base

        -- Wrapper trace writes below r-reclaimable + 2
        -- reclaim-instr doesn't write to slots, store-at-slot (suc wrapper-base) writes at suc wrapper-base < wrapper-base + 2
        wrapper-twb : TraceWritesBelow (wrapper-base +ℕ 2) reclaim-wrapper-trace
        wrapper-twb = subst (λ x → suc wrapper-base < x) (sym (+-comm wrapper-base 2))
                            (n<1+n (suc wrapper-base)) , tt

        -- Wrapper trace reads no slots (doesn't include slot reads)
        wrapper-tsra : TraceSlotReadsAbove (next-slot alloc) reclaim-wrapper-trace
        wrapper-tsra = tt

        wrapper-tsrb : TraceSlotReadsBelow (wrapper-base +ℕ 2) reclaim-wrapper-trace
        wrapper-tsrb = tt

        -- reclaim-wrapper-trace preserves halted=false
        reclaim-wrapper-not-halted : halted s-after-sub ≡ false → halted s-after-wrapper ≡ false
        reclaim-wrapper-not-halted nh = exec-trace-preserves-halted-WF reclaim-wrapper-trace s-after-sub alloc-after-sub nh reclaim-wrapper-tph

        -- Final alloc after reclaim + wrapper: next-slot = r-reclaimable + 2
        -- Frame is preserved, heap is preserved, capacity is preserved
        wrapper-frame-preserved : current-frame alloc-after-wrapper ≡ current-frame alloc-after-sub
        wrapper-frame-preserved = SMP.TracePrimitives.exec-trace-preserves-frame reclaim-wrapper-trace s-after-sub alloc-after-sub

        wrapper-heap-preserved : next-heap-ref alloc-after-wrapper ≡ next-heap-ref alloc-after-sub
        wrapper-heap-preserved = SMP.RecSchemeSemantics.exec-trace-preserves-heap-ref reclaim-wrapper-trace s-after-sub alloc-after-sub

        -- Note: wrapper-capacity-preserved removed in Phase 3

        -- next-slot = r-reclaimable + 2 after reclaim + wrapper
        wrapper-next-slot-eq : next-slot alloc-after-wrapper ≡ r-reclaimable +ℕ 2
        wrapper-next-slot-eq =
          let -- Split exec-trace into reclaim + wrapper
              trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub r-not-halted
              -- After reclaim: alloc has next-slot = r-reclaimable
              -- wrapper-trace-advances-slot: proj₂ (exec-trace wrapper-trace ...) has next-slot = start + 2
              alloc-after-wrapper-eq : proj₂ (exec-trace wrapper-trace s-after-sub alloc-reclaimed) ≡ wrapper-alloc-result alloc-reclaimed
              alloc-after-wrapper-eq = wrapper-trace-advances-slot wrapper-base s-after-sub alloc-reclaimed r-not-halted
              -- wrapper-alloc-result alloc-reclaimed has next-slot = r-reclaimable + 2
          in trans (cong (λ p → next-slot (proj₂ p)) trace-split)
                   (cong next-slot alloc-after-wrapper-eq)

        -- wrapper-before-frontier: wrapper-base = r-reclaimable < r-reclaimable + 2 = next-slot alloc-after-wrapper
        wrapper-before-frontier : wrapper-base < next-slot alloc-after-wrapper
        wrapper-before-frontier = subst (λ x → wrapper-base < x) (sym wrapper-next-slot-eq)
                                        (m<m+n wrapper-base {2} (s≤s z≤n))

        -- After lea-slot, Output register contains wrapper-loc
        -- reclaim-instr doesn't change regs, so wrapper-trace-output still applies
        wrapper-rax-result : readReg (regs s-after-wrapper) Output ≡ SV-Ptr wrapper-loc
        wrapper-rax-result =
          let trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub r-not-halted
              output-eq = wrapper-trace-output wrapper-base s-after-sub alloc-reclaimed r-not-halted
          in trans (cong (λ p → readReg (regs (proj₁ p)) Output) trace-split) output-eq

        -- The pointer slot (wrapper-base + 1) was written with SV-Ptr r-result-loc
        wrapper-ptr-written : readLoc s-after-wrapper (sucLoc wrapper-loc) ≡ just (SV-Ptr r-result-loc)
        wrapper-ptr-written =
          let trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub r-not-halted
              -- Before wrapper-trace: rax = r-result-loc (from child's rax-is-result)
              rax-before = place-rax (ProcessedLayerResult.result-place r-result)
              -- wrapper-trace-ptr-written: slot (suc base) contains original Output value
              ptr-eq : readLoc (proj₁ (exec-trace wrapper-trace s-after-sub alloc-reclaimed))
                               (AtStack (current-frame alloc-reclaimed) (suc wrapper-base)) ≡
                       just (readReg (regs s-after-sub) Output)
              ptr-eq = wrapper-trace-ptr-written wrapper-base s-after-sub alloc-reclaimed r-not-halted
          in trans (cong (λ p → readLoc (proj₁ p) (sucLoc wrapper-loc)) trace-split)
                   (trans ptr-eq (cong just rax-before))

        -- Memory preservation: reclaim doesn't change memory, wrapper writes above r-reclaimable
        -- For locations BeforeFrontier alloc, their slot < next-slot alloc ≤ r-reclaimable = wrapper-base
        wrapper-mem-preserved : ∀ loc → BeforeFrontier alloc loc →
                                readLoc s-after-wrapper loc ≡ readLoc s-after-sub loc
        wrapper-mem-preserved loc bf =
          let trace-split = exec-trace-cons reclaim-instr wrapper-trace s-after-sub alloc-after-sub r-not-halted
              -- loc is BeforeFrontier alloc, and next-slot alloc ≤ r-reclaimable = wrapper-base
              -- So loc is BeforeFrontier alloc-reclaimed as well
              -- frame-preserved-inj2 : current-frame alloc-after-sub ≡ current-frame alloc
              -- alloc-reclaimed = record alloc-after-sub { next-slot = r-reclaimable }
              -- So current-frame alloc-reclaimed = current-frame alloc-after-sub
              bf-reclaimed : BeforeFrontier alloc-reclaimed loc
              bf-reclaimed = frontier-monotone alloc alloc-reclaimed
                               (sym frame-preserved-inj2)
                               reclaim-mono-inj2
                               (subst (next-heap-ref alloc ≤_) (sym heap-preserved-inj2) ≤-refl)
                               loc bf
              -- wrapper-trace preserves memory at bf-reclaimed locations
              mem-eq = wrapper-trace-mem-preserved wrapper-base s-after-sub alloc-reclaimed loc r-not-halted refl bf-reclaimed
          in trans (cong (λ p → readLoc (proj₁ p) loc) trace-split) mem-eq

        -- For processed-valid (valid-inr-wf), we need:
        -- 1. BeforeFrontier alloc-after-wrapper r-result-loc
        --    With actual reclamation, r-result-loc's slot < r-reclaimable = wrapper-base
        --    Since next-slot alloc-after-wrapper = r-reclaimable + 2 > r-reclaimable,
        --    r-result-loc is still before the new frontier.
        -- TODO (post-scaffold): same alloc-setup non-reduction issue.
        r-before-wrapper : BeforeFrontier alloc-after-wrapper r-result-loc
        r-before-wrapper = SMP.!!

        -- 2. BeforeFrontier alloc-after-wrapper (sucLoc wrapper-loc)
        --    sucLoc wrapper-loc = AtStack frame (suc wrapper-base) = AtStack frame (suc r-reclaimable)
        --    suc r-reclaimable < r-reclaimable + 2 = next-slot alloc-after-wrapper
        wb+2≡sswb : wrapper-base +ℕ 2 ≡ suc (suc wrapper-base)
        wb+2≡sswb = +-comm wrapper-base 2

        suc-wrapper-lt : suc wrapper-base < next-slot alloc-after-wrapper
        suc-wrapper-lt = subst (λ x → suc wrapper-base < x)
                               (trans (sym wb+2≡sswb) (sym wrapper-next-slot-eq))
                               (n<1+n (suc wrapper-base))

        suc-wrapper-before : BeforeFrontier alloc-after-wrapper (sucLoc wrapper-loc)
        suc-wrapper-before = stack-before (sym wrapper-frame-preserved) suc-wrapper-lt

        -- 3. ValidAtWF for r-processed at r-result-loc in alloc-after-wrapper
        --    With actual reclamation, reclaim-instr doesn't change memory, wrapper writes at suc r-reclaimable.
        --    r-result-loc's slot < r-reclaimable (child result is before child's reclaimable-slot),
        --    so it's disjoint from the wrapper write at suc r-reclaimable.

        -- TODO (post-scaffold): same alloc-setup non-reduction issue.
        r-valid-wrapper : ValidAtWF mR alloc-after-wrapper r-processed r-result-loc s-after-wrapper
        r-valid-wrapper = SMP.!!

        -- Plan 0.14 (Camp 2): wrapper-loc is AtStack so wrapper-mode = Stack.
        processed-valid-proof : ValidAtWF Stack alloc-after-wrapper processed wrapper-loc s-after-wrapper
        processed-valid-proof = valid-inr-wf tt wrapper-ptr-written r-before-wrapper suc-wrapper-before r-valid-wrapper

        -- result-before: wrapper-base < next-slot alloc-after-wrapper
        result-before-proof : BeforeFrontier alloc-after-wrapper wrapper-loc
        result-before-proof = stack-before (sym wrapper-frame-preserved) wrapper-before-frontier

        -- slot-usage-bound proof (reused for slot-stays-in-budget)
        -- Since reclaimable-slot = next-slot final-alloc, both fields need the same proof
        slot-usage-and-budget-proof-inj2 : next-slot alloc-after-wrapper ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
        slot-usage-and-budget-proof-inj2 = sum-right-slot-budget wfL wfR wfG alg alloc r-reclaimable alloc-after-wrapper wrapper-next-slot-eq slot-usage-bound-inj2

      in
      -- Plan 0.14 (Camp 2): wrapper at AtStack means returned mode = Stack.
      Stack , record
        { processed = processed
        ; trace = full-trace
        ; final-state = s-after-wrapper
        ; final-alloc = alloc-after-wrapper
        ; bump = bump-+ (ProcessedLayerResult.bump r-result) (mkBump 2 0)
        ; final-alloc-eq = sum-bump-eq (ProcessedLayerResult.bump r-result)
            alloc alloc-after-sub alloc-after-wrapper alloc-setup
            (setup-trace-preserves-alloc s alloc)
            (ProcessedLayerResult.final-alloc-eq r-result)
            wrapper-frame-preserved wrapper-next-slot-eq wrapper-heap-preserved
        ; trace-no-frame-ops =
            SMP.trace-no-frame-ops-append setup-trace (sub-trace ++ reclaim-wrapper-trace)
              (tt , tt , tt)
              (SMP.trace-no-frame-ops-append sub-trace reclaim-wrapper-trace
                (ProcessedLayerResult.trace-no-frame-ops r-result)
                (tt , tt , tt , tt , tt))
        ; trace-correct = trace-correct-inj2
        ; alloc-correct = alloc-correct-inj2
        ; result-place = at-loc wrapper-loc processed-valid-proof
            result-before-proof wrapper-rax-result
            processed-valid-proof result-before-proof
        -- not-halted: reclaim-wrapper trace preserves halted=false
        ; not-halted = reclaim-wrapper-not-halted r-not-halted
        ; semantic-correct = cong inj₂ (ProcessedLayerResult.semantic-correct r-result)
        -- frame-preserved: reclaim-wrapper trace preserves frame
        ; frame-preserved = trans wrapper-frame-preserved frame-preserved-inj2
        -- slot-monotone: next-slot alloc ≤ r-reclaimable + 2 = next-slot alloc-after-wrapper
        ; slot-monotone = subst (λ x → next-slot alloc ≤ x) (sym wrapper-next-slot-eq)
                                (≤-trans reclaim-mono-inj2 (m≤m+n r-reclaimable 2))
        -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-preserves-*
        ; slot-usage-bound = slot-usage-and-budget-proof-inj2
        -- max-slot-used: max of child's max-slot-used and wrapper allocation
        ; max-slot-used = max-slot-used-inj2
        -- max-slot-geq-final: next-slot final-alloc ≤ max-slot-used
        -- next-slot alloc-after-wrapper = r-reclaimable + 2 (by wrapper-next-slot-eq)
        -- r-reclaimable + 2 ≤ max-slot-used-inj2 (by n≤m⊔n)
        ; max-slot-geq-final = subst (_≤ max-slot-used-inj2) (sym wrapper-next-slot-eq)
                                     (n≤m⊔n r-max-slot-used (r-reclaimable +ℕ 2))
        ; max-slot-usage-bound =
            -- max-slot-used-inj2 = r-max-slot-used ⊔ (r-reclaimable + 2)
            -- Need: max-slot-used-inj2 ≤ next-slot alloc + layer-capacity (wf-Sum wfL wfR)
            let -- r-max-slot-used ≤ next-slot alloc + layer-capacity wfR (from r-max-slot-usage-bound)
                -- layer-capacity wfR ≤ layer-capacity (wf-Sum wfL wfR) = 2 + (capL ⊔ capR) ≥ capR
                child-cap-bound : layer-capacity wfR wfG alg ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
                child-cap-bound = ≤-trans (n≤m⊔n (layer-capacity wfL wfG alg) (layer-capacity wfR wfG alg))
                                          (m≤n+m (layer-capacity wfL wfG alg ⊔ layer-capacity wfR wfG alg) 2)
                r-max-bound : r-max-slot-used ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                r-max-bound = ≤-trans r-max-slot-usage-bound (+-monoʳ-≤ (next-slot alloc) child-cap-bound)
                -- r-reclaimable + 2 ≤ next-slot alloc + layer-capacity (wf-Sum wfL wfR) (from slot-usage-bound proof)
                wrapper-bound : r-reclaimable +ℕ 2 ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                wrapper-bound =
                  let step1 = +-monoˡ-≤ 2 slot-usage-bound-inj2
                      step2 = +-assoc (next-slot alloc) (layer-capacity wfR wfG alg) 2
                      fits = sum-wrapper-fits-right wfL wfR wfG alg
                      step3 = +-monoʳ-≤ (next-slot alloc) fits
                  in ≤-trans (subst (r-reclaimable +ℕ 2 ≤_) step2 step1) step3
            in ⊔-lub r-max-bound wrapper-bound
        ; slot-stays-in-budget = slot-usage-and-budget-proof-inj2
        -- heap-monotone: heap unchanged by wrapper trace
        ; heap-monotone = subst (λ x → next-heap-ref alloc ≤ x) (sym wrapper-heap-preserved) heap-monotone-inj2
        -- heap-preserved: chain through wrapper (preserves heap) and sub-result (heap-preserved-inj2)
        ; heap-preserved = trans wrapper-heap-preserved heap-preserved-inj2
        -- mem-preserved: memory below original frontier preserved through full trace
        ; mem-preserved = λ loc bf → trans (wrapper-mem-preserved loc bf) (mem-preserved-inj2 loc bf)
        -- Trace region bounds: full-trace = setup-trace ++ sub-trace ++ reclaim-wrapper-trace
        -- sub-trace bounds are relative to alloc-setup, but alloc-setup ≡ alloc
        -- With max-slot-used = r-max-slot-used ⊔ (r-reclaimable + 2), proofs go through
        ; trace-writes-above = SMP.trace-writes-above-append (next-slot alloc) setup-trace (sub-trace ++ reclaim-wrapper-trace)
            setup-twa (SMP.trace-writes-above-append (next-slot alloc) sub-trace reclaim-wrapper-trace
              (subst (λ al → TraceWritesAbove (next-slot al) sub-trace) alloc-setup-eq
                     (ProcessedLayerResult.trace-writes-above r-result))
              (SMP.trace-writes-above-mono (next-slot alloc) r-reclaimable reclaim-wrapper-trace
                     reclaim-mono-inj2 wrapper-twa))
        -- trace-writes-below: Using max-slot-used = r-max-slot-used ⊔ (r-reclaimable + 2)
        ; trace-writes-below = SMP.trace-writes-below-append max-slot-used-inj2 setup-trace (sub-trace ++ reclaim-wrapper-trace)
            tt (SMP.trace-writes-below-append max-slot-used-inj2 sub-trace reclaim-wrapper-trace
              (SMP.trace-writes-below-mono r-max-slot-used max-slot-used-inj2 sub-trace
                 (m≤m⊔n r-max-slot-used (r-reclaimable +ℕ 2))
                 (ProcessedLayerResult.trace-writes-below r-result))
              (SMP.trace-writes-below-mono (r-reclaimable +ℕ 2) max-slot-used-inj2 reclaim-wrapper-trace
                 (n≤m⊔n r-max-slot-used (r-reclaimable +ℕ 2)) wrapper-twb))
        ; trace-slot-reads-above = SMP.trace-slot-reads-above-append (next-slot alloc) setup-trace (sub-trace ++ reclaim-wrapper-trace)
            setup-tsra (SMP.trace-slot-reads-above-append (next-slot alloc) sub-trace reclaim-wrapper-trace
              (subst (λ al → TraceSlotReadsAbove (next-slot al) sub-trace) alloc-setup-eq
                     (ProcessedLayerResult.trace-slot-reads-above r-result))
              wrapper-tsra)
        -- trace-slot-reads-below: Using max-slot-used = r-max-slot-used ⊔ (r-reclaimable + 2)
        ; trace-slot-reads-below = SMP.trace-slot-reads-below-append max-slot-used-inj2 setup-trace (sub-trace ++ reclaim-wrapper-trace)
            tt (SMP.trace-slot-reads-below-append max-slot-used-inj2 sub-trace reclaim-wrapper-trace
              (SMP.trace-slot-reads-below-mono r-max-slot-used max-slot-used-inj2 sub-trace
                 (m≤m⊔n r-max-slot-used (r-reclaimable +ℕ 2))
                 (ProcessedLayerResult.trace-slot-reads-below r-result))
              (SMP.trace-slot-reads-below-mono (r-reclaimable +ℕ 2) max-slot-used-inj2 reclaim-wrapper-trace
                 (n≤m⊔n r-max-slot-used (r-reclaimable +ℕ 2)) wrapper-tsrb))
        ; trace-twf = twf-++ not-halted setup-tph
            (subst (λ st → TraceWF st (proj₂ (exec-trace setup-trace s alloc)) (sub-trace ++ reclaim-wrapper-trace))
                   (sym (cong proj₁ setup-exec-eq))
              (subst (λ al → TraceWF s-setup al (sub-trace ++ reclaim-wrapper-trace))
                     (sym (cong proj₂ setup-exec-eq))
                (twf-++ not-halted-setup (ProcessedLayerResult.trace-twf r-result) reclaim-wrapper-tph)))
        -- scratch-bounded = max-slot-usage-bound (same proof, INPUT-relative)
        ; scratch-bounded =
            let child-cap-bound : layer-capacity wfR wfG alg ≤ layer-capacity (wf-Sum wfL wfR) wfG alg
                child-cap-bound = ≤-trans (n≤m⊔n (layer-capacity wfL wfG alg) (layer-capacity wfR wfG alg))
                                          (m≤n+m (layer-capacity wfL wfG alg ⊔ layer-capacity wfR wfG alg) 2)
                r-max-bound : r-max-slot-used ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                r-max-bound = ≤-trans r-max-slot-usage-bound (+-monoʳ-≤ (next-slot alloc) child-cap-bound)
                wrapper-bound : r-reclaimable +ℕ 2 ≤ next-slot alloc +ℕ layer-capacity (wf-Sum wfL wfR) wfG alg
                wrapper-bound =
                  let step1 = +-monoˡ-≤ 2 slot-usage-bound-inj2
                      step2 = +-assoc (next-slot alloc) (layer-capacity wfR wfG alg) 2
                      fits = sum-wrapper-fits-right wfL wfR wfG alg
                      step3 = +-monoʳ-≤ (next-slot alloc) fits
                  in ≤-trans (subst (r-reclaimable +ℕ 2 ≤_) step2 step1) step3
            in ⊔-lub r-max-bound wrapper-bound
        }

    -- Product case: delegate to helper (enables where clauses)
    process-layer (wf-Prod wfL wfR) wfG alg dispatch (l-comp , r-comp) mIn input-loc s alloc
      n rec procRec size-bound (valid-pair-wf {fst-loc = fst-loc} {snd-loc = snd-loc} lmm fst-ptr snd-ptr fst-bf snd-bf sucLoc-bf l-layer-valid r-layer-valid) input-before not-halted rdi-eq =
      process-layer-prod wfL wfR wfG alg dispatch l-comp r-comp mIn
        input-loc fst-loc snd-loc s alloc n rec procRec size-bound
        fst-ptr snd-ptr fst-bf snd-bf sucLoc-bf l-layer-valid r-layer-valid
        input-before not-halted rdi-eq

    ------------------------------------------------------------------------
    -- Product Case Helper (Refactored per lessons-learned.md)
    --
    -- Extracted to module level to enable where clauses for complex proofs.
    -- The let-block limitation in Agda prevents where clauses inside let.
    ------------------------------------------------------------------------

    process-layer-prod : ∀ {mvL mvR FL FR G A}
      (wfL : WellFormedF FL) (wfR : WellFormedF FR) (wfG : WellFormedF G)
      (alg : IR (⟦ G ⟧T A) A)
      (dispatch : RecDispatcherWF (ir-size (Cata wfG alg)))
      (l-comp : ⟦ FL ⟧F (⟦μ⟧ G)) (r-comp : ⟦ FR ⟧F (⟦μ⟧ G))
      (mIn : AllocMode)
      (input-loc fst-loc snd-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      (n : ℕ) (rec : CataRecBound wfG alg n)
      (procRec : ProcLayerCap wfG alg n (functor-size (FL ⊗ FR)))
      (size-bound : child-measure (FL ⊗ FR) wfG (l-comp , r-comp) < n)
      (fst-ptr : readLoc s input-loc ≡ just (SV-Ptr fst-loc))
      (snd-ptr : readLoc s (sucLoc input-loc) ≡ just (SV-Ptr snd-loc))
      (fst-bf : BeforeFrontier alloc fst-loc)
      (snd-bf : BeforeFrontier alloc snd-loc)
      (sucLoc-bf : BeforeFrontier alloc (sucLoc input-loc))
      (l-layer-valid : ValidAtWF mvL alloc {⟦ FL ⟧T (μ-type G)} (coerce-functor⁻¹ FL (μ-type G) l-comp) fst-loc s)
      (r-layer-valid : ValidAtWF mvR alloc {⟦ FR ⟧T (μ-type G)} (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s)
      (input-before : BeforeFrontier alloc input-loc)
      (not-halted : halted s ≡ false)
      (rdi-eq : readReg (regs s) Input1 ≡ SV-Ptr input-loc)
      → ∃[ mOut ] ProcessedLayerResult wfG alg mOut (wf-Prod wfL wfR) (l-comp , r-comp) s alloc
    process-layer-prod {mvL} {mvR} {FL} {FR} {G} {A} wfL wfR wfG alg dispatch l-comp r-comp mIn
      input-loc fst-loc snd-loc s alloc n rec procRec size-bound
      fst-ptr snd-ptr fst-bf snd-bf sucLoc-bf l-layer-valid r-layer-valid
      input-before not-halted rdi-eq =
      mR , record
        { processed = processed
        ; trace = full-trace
        ; final-state = ProcessedLayerResult.final-state r-result
        ; final-alloc = final-alloc
        ; bump = SMP.!!          -- Prod bump: needs left+setup+right bump composition (future)
        ; final-alloc-eq = SMP.!!
        ; trace-no-frame-ops =
            SMP.trace-no-frame-ops-append left-setup-trace (l-trace ++ right-setup-trace ++ r-trace)
              (tt , tt , tt , tt , tt)
              (SMP.trace-no-frame-ops-append l-trace (right-setup-trace ++ r-trace)
                (ProcessedLayerResult.trace-no-frame-ops l-result)
                (SMP.trace-no-frame-ops-append right-setup-trace r-trace
                  (tt , tt , tt , tt , tt)
                  (ProcessedLayerResult.trace-no-frame-ops r-result)))
        ; trace-correct = trace-correct-proof
        ; alloc-correct = SMP.!!  -- Plan 0.14: complete migration in dedicated pass
        ; result-place = at-loc (place-loc (ProcessedLayerResult.result-place r-result))
            processed-valid-proof
            (place-before (ProcessedLayerResult.result-place r-result))
            (place-rax (ProcessedLayerResult.result-place r-result))
            processed-valid-proof
            (place-before (ProcessedLayerResult.result-place r-result))
        ; not-halted = ProcessedLayerResult.not-halted r-result
        ; semantic-correct = cong₂ _,_ (ProcessedLayerResult.semantic-correct l-result)
                                       (ProcessedLayerResult.semantic-correct r-result)
        ; frame-preserved = trans (ProcessedLayerResult.frame-preserved r-result)
                                  alloc-for-right-frame
        -- Chain: next-slot alloc < alloc-for-left ≤ l-reclaimable = alloc-for-right ≤ final-alloc
        ; slot-monotone = ≤-trans (incr-next-slot-mono alloc)
                                  (≤-trans l-reclaim-mono r-slot-mono)
        -- Slot reclamation: save-slot is temporary, can be reclaimed after Product completes
        -- Phase 7: Removed reclaimable-slot, reclaim-monotone, reclaim-bounded, reclaim-preserves-*
        ; slot-usage-bound = slot-usage-bound-prod
        -- max-slot-used: max of both children's max-slot-used
        ; max-slot-used = max-slot-used-prod
        ; max-slot-geq-final = reclaimable-geq-max
        ; max-slot-usage-bound = max-slot-usage-bound-prod
        -- slot-stays-in-budget: Final frontier within layer capacity
        -- Uses prod-slot-budget helper with the new SUM formula:
        --   layer-capacity (wf-Prod wfL wfR) = 1 + capL + capR
        -- Proof chain:
        --   next-slot final-alloc ≤ l-reclaimable + capR (from r-slot-stays-in-budget)
        --                        ≤ (suc (next-slot alloc) + capL) + capR (from l-slot-usage)
        --                        = next-slot alloc + (1 + capL + capR) = next-slot alloc + layer-capacity
        ; slot-stays-in-budget = slot-stays-in-budget-prod
        -- heap-monotone: alloc.heap = alloc-for-right.heap ≤ final-alloc.heap
        ; heap-monotone = subst (λ h → h ≤ next-heap-ref final-alloc) alloc-for-right-heap
                                (ProcessedLayerResult.heap-monotone r-result)
        -- heap-preserved: chain through r-result.heap-preserved and alloc-for-right-heap
        ; heap-preserved = trans (ProcessedLayerResult.heap-preserved r-result) alloc-for-right-heap
        ; mem-preserved = mem-preserved-proof
        ; trace-writes-above = trace-writes-above-proof
        ; trace-writes-below = trace-writes-below-proof
        ; trace-slot-reads-above = trace-slot-reads-above-proof
        ; trace-slot-reads-below = trace-slot-reads-below-proof
        ; trace-twf = SMP.!!  -- TODO: twf-++ chain (left-setup + l-result + right-setup + r-result)
        -- scratch-bounded: max-slot-used ≤ next-slot alloc + layer-capacity
        -- This is exactly max-slot-usage-bound-prod (INPUT-relative bounds)
        ; scratch-bounded = max-slot-usage-bound-prod
        }
      where
        -- Save slot for input-loc preservation
        save-slot : ℕ
        save-slot = next-slot alloc

        ------------------------------------------------------------------------
        -- Slot Reclamation for Product
        -- Phase 6: Perfect scratch reclaim - reclaimable-slot-prod, reclaim-monotone-prod,
        -- and reclaim-bounded-prod defined after final-alloc (see below)
        ------------------------------------------------------------------------

        ------------------------------------------------------------------------
        -- Phase 1: Left Setup
        ------------------------------------------------------------------------
        left-setup-trace : AbstractTrace
        left-setup-trace = prod-left-setup-trace save-slot

        s-left-setup : LocState FS
        s-left-setup = proj₁ (exec-trace left-setup-trace s alloc)

        alloc-left-setup : AllocState {FS}
        alloc-left-setup = proj₂ (exec-trace left-setup-trace s alloc)

        rdi-left-setup : readReg (regs s-left-setup) Input1 ≡ SV-Ptr fst-loc
        rdi-left-setup = prod-left-setup-input save-slot s alloc input-loc fst-loc
                           not-halted rdi-eq fst-ptr

        alloc-left-setup-eq : alloc-left-setup ≡ alloc
        alloc-left-setup-eq = prod-left-setup-alloc save-slot s alloc not-halted

        alloc-for-left : AllocState {FS}
        alloc-for-left = incr-next-slot alloc

        -- Transfer l-layer-valid through setup
        -- Now we can use a proper proof with where clause helpers
        l-layer-valid-setup : ValidAtWF mvL alloc-for-left {⟦ FL ⟧T (μ-type G)} (coerce-functor⁻¹ FL (μ-type G) l-comp) fst-loc s-left-setup
        l-layer-valid-setup = l-layer-valid-setup-proof
          where
            -- Step 1: Transfer through state change using validityWF-mem-preserved
            l-layer-valid-state : ValidAtWF mvL alloc {⟦ FL ⟧T (μ-type G)} (coerce-functor⁻¹ FL (μ-type G) l-comp) fst-loc s-left-setup
            l-layer-valid-state = validityWF-mem-preserved (coerce-functor⁻¹ FL (μ-type G) l-comp) fst-loc s s-left-setup
              fst-bf mem-eq l-layer-valid
              where
                mem-eq : ∀ loc' → BeforeFrontier alloc loc' → readLoc s-left-setup loc' ≡ readLoc s loc'
                mem-eq loc' bf' = prod-left-setup-mem-eq save-slot s alloc loc' not-halted loc'-neq-slot
                  where
                    -- BeforeFrontier alloc loc' implies loc' is not at save-slot
                    -- because save-slot = next-slot alloc, and BeforeFrontier requires < next-slot
                    loc'-neq-slot : loc' ≢ AtStack (current-frame alloc) save-slot
                    loc'-neq-slot eq = Data.Nat.Properties.<-irrefl refl (bf-slot-contradiction alloc loc' save-slot bf' eq)

            -- Step 2: Transfer through alloc change using validityWF-frontier-advance
            l-layer-valid-setup-proof : ValidAtWF mvL alloc-for-left {⟦ FL ⟧T (μ-type G)} (coerce-functor⁻¹ FL (μ-type G) l-comp) fst-loc s-left-setup
            l-layer-valid-setup-proof = validityWF-frontier-advance (coerce-functor⁻¹ FL (μ-type G) l-comp) fst-loc s-left-setup
              refl (incr-next-slot-mono alloc) ≤-refl l-layer-valid-state

        fst-bf-setup : BeforeFrontier alloc-for-left fst-loc
        fst-bf-setup = frontier-monotone alloc alloc-for-left
                         refl (incr-next-slot-mono alloc) ≤-refl fst-loc fst-bf

        not-halted-left-setup : halted s-left-setup ≡ false
        not-halted-left-setup = SMP.!!  -- TODO: prod-left-setup-halted-helper under StoredValue

        ------------------------------------------------------------------------
        -- Phase 2: Left Processing
        ------------------------------------------------------------------------
        l-result-pair : ∃[ mOut ] ProcessedLayerResult wfG alg mOut wfL l-comp s-left-setup alloc-for-left
        l-result-pair = procRec wfL (fsize-prod-left _ _) l-comp mIn fst-loc s-left-setup alloc-for-left
                          (child-bound-prod-left wfG l-comp r-comp size-bound) l-layer-valid-setup fst-bf-setup not-halted-left-setup rdi-left-setup

        mL : AllocMode
        mL = proj₁ l-result-pair

        l-result : ProcessedLayerResult wfG alg mL wfL l-comp s-left-setup alloc-for-left
        l-result = proj₂ l-result-pair

        l-processed : ⟦ ⟦ FL ⟧T A ⟧
        l-processed = ProcessedLayerResult.processed l-result

        s-l : LocState FS
        s-l = ProcessedLayerResult.final-state l-result

        alloc-l : AllocState {FS}
        alloc-l = ProcessedLayerResult.final-alloc l-result

        l-loc : ValueLocation FS
        l-loc = place-loc (ProcessedLayerResult.result-place l-result)

        l-trace : AbstractTrace
        l-trace = ProcessedLayerResult.trace l-result

        l-not-halted : halted s-l ≡ false
        l-not-halted = ProcessedLayerResult.not-halted l-result

        l-slot-mono : next-slot alloc-for-left ≤ next-slot alloc-l
        l-slot-mono = ProcessedLayerResult.slot-monotone l-result

        slot-mono-full : next-slot alloc ≤ next-slot alloc-l
        slot-mono-full = ≤-trans (incr-next-slot-mono alloc) l-slot-mono

        frame-pres-full : current-frame alloc-l ≡ current-frame alloc
        frame-pres-full = trans (ProcessedLayerResult.frame-preserved l-result)
                                (incr-next-slot-frame alloc)

        heap-mono-full : next-heap-ref alloc ≤ next-heap-ref alloc-l
        heap-mono-full = subst (λ h → h ≤ next-heap-ref alloc-l)
                               (incr-next-slot-heap alloc)
                               (ProcessedLayerResult.heap-monotone l-result)

        ------------------------------------------------------------------------
        -- Slot Reclamation After Left Processing
        --
        -- After left completes, reclaim to l-reclaimable. Right processing
        -- starts from this reclaimed position, enabling capacity sharing.
        ------------------------------------------------------------------------
        l-reclaimable : ℕ
        l-reclaimable = next-slot (ProcessedLayerResult.final-alloc l-result)

        -- Reclaimed allocation for right processing
        -- Uses alloc-for-left as base (same frame/heap as alloc after save-slot)
        -- but with next-slot reset to l-reclaimable
        alloc-for-right : AllocState {FS}
        alloc-for-right = record alloc-for-left { next-slot = l-reclaimable }

        -- Properties of alloc-for-right
        alloc-for-right-frame : current-frame alloc-for-right ≡ current-frame alloc
        alloc-for-right-frame = incr-next-slot-frame alloc

        alloc-for-right-heap : next-heap-ref alloc-for-right ≡ next-heap-ref alloc
        alloc-for-right-heap = incr-next-slot-heap alloc

        -- l-reclaimable bounds
        l-reclaim-mono : next-slot alloc-for-left ≤ l-reclaimable
        l-reclaim-mono = ProcessedLayerResult.slot-monotone l-result

        l-reclaim-bounded : l-reclaimable ≡ next-slot alloc-l
        l-reclaim-bounded = refl

        -- slot-usage-bound from l-result: l-reclaimable ≤ next-slot alloc-for-left + layer-capacity wfL
        l-slot-usage : l-reclaimable ≤ next-slot alloc-for-left +ℕ layer-capacity wfL wfG alg
        l-slot-usage = ProcessedLayerResult.slot-usage-bound l-result

        r-layer-valid-transferred : ValidAtWF mvR alloc-for-right {⟦ FR ⟧T (μ-type G)} (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s-l
        r-layer-valid-transferred =
          -- Transfer through alloc → alloc-for-right using frontier-advance
          -- Chain: next-slot alloc < next-slot alloc-for-left ≤ l-reclaimable = next-slot alloc-for-right
          validityWF-frontier-advance (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s-l
            alloc-for-right-frame
            slot-mono-to-right
            heap-mono-to-right
            r-layer-valid-at-s-l
          where
            -- Slot monotonicity: next-slot alloc ≤ next-slot alloc-for-right
            slot-mono-to-right : next-slot alloc ≤ next-slot alloc-for-right
            slot-mono-to-right = ≤-trans (incr-next-slot-mono alloc) l-reclaim-mono

            -- Heap monotonicity (heap unchanged)
            heap-mono-to-right : next-heap-ref alloc ≤ next-heap-ref alloc-for-right
            heap-mono-to-right = subst (next-heap-ref alloc ≤_) (sym alloc-for-right-heap) ≤-refl

            -- First transfer r-layer-valid through the state changes
            r-layer-valid-at-s-left-setup : ValidAtWF mvR alloc {⟦ FR ⟧T (μ-type G)} (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s-left-setup
            r-layer-valid-at-s-left-setup = validityWF-mem-preserved (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s s-left-setup
              snd-bf
              (λ loc' bf' → prod-left-setup-mem-eq save-slot s alloc loc' not-halted
                (λ eq → Data.Nat.Properties.<-irrefl refl (bf-slot-contradiction alloc loc' save-slot bf' eq)))
              r-layer-valid

            -- Then through left processing
            r-layer-valid-at-s-l : ValidAtWF mvR alloc {⟦ FR ⟧T (μ-type G)} (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s-l
            r-layer-valid-at-s-l = validityWF-mem-preserved (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s-left-setup s-l
              snd-bf
              (λ loc' bf' → ProcessedLayerResult.mem-preserved l-result loc'
                (frontier-monotone alloc alloc-for-left refl (incr-next-slot-mono alloc) ≤-refl loc' bf'))
              r-layer-valid-at-s-left-setup

        r-snd-bf : BeforeFrontier alloc-for-right snd-loc
        r-snd-bf = frontier-monotone alloc alloc-for-right
                     (sym alloc-for-right-frame)
                     (≤-trans (incr-next-slot-mono alloc) l-reclaim-mono)
                     (subst (next-heap-ref alloc ≤_) (sym alloc-for-right-heap) ≤-refl)
                     snd-loc snd-bf

        ------------------------------------------------------------------------
        -- Phase 3: Right Setup
        ------------------------------------------------------------------------
        right-setup-trace : AbstractTrace
        right-setup-trace = prod-right-setup-trace save-slot

        -- Right setup uses alloc-for-right (reclaimed allocation)
        -- The frame is the same, so stack access at save-slot still works
        s-right-setup : LocState FS
        s-right-setup = proj₁ (exec-trace right-setup-trace s-l alloc-for-right)

        -- Input1 = SV-Ptr snd-loc after right setup
        rdi-right-setup : readReg (regs s-right-setup) Input1 ≡ SV-Ptr snd-loc
        rdi-right-setup = SMP.!!  -- TODO: prod-right-setup-input under StoredValue
          where
            -- Stack at save-slot still contains input-loc (preserved through left processing)
            stack-preserved : readLoc s-l (AtStack (current-frame alloc) save-slot) ≡
                              readLoc s-left-setup (AtStack (current-frame alloc) save-slot)
            stack-preserved = ProcessedLayerResult.mem-preserved l-result
              (AtStack (current-frame alloc) save-slot)
              (slot-at-next-bf alloc)

            -- After left-setup, stack[save-slot] = input-loc
            stack-has-input : readLoc s-left-setup (AtStack (current-frame alloc) save-slot) ≡ just (SV-Ptr input-loc)
            stack-has-input = SMP.RecSchemeSemantics.prod-left-setup-saves-input save-slot s alloc input-loc not-halted rdi-eq

            -- So s-l still has input-loc at save-slot
            stack-at-s-l : readLoc s-l (AtStack (current-frame alloc) save-slot) ≡ just (SV-Ptr input-loc)
            stack-at-s-l = trans stack-preserved stack-has-input

            -- sucLoc input-loc still points to SV-Ptr snd-loc (memory preserved)
            snd-ptr-at-s-l : readLoc s-l (sucLoc input-loc) ≡ just (SV-Ptr snd-loc)
            snd-ptr-at-s-l = trans
              (ProcessedLayerResult.mem-preserved l-result (sucLoc input-loc)
                (frontier-monotone alloc alloc-for-left refl (incr-next-slot-mono alloc) ≤-refl
                  (sucLoc input-loc) sucLoc-bf))
              (trans (prod-left-setup-mem-eq save-slot s alloc (sucLoc input-loc) not-halted
                (λ eq → Data.Nat.Properties.<-irrefl refl (bf-slot-contradiction alloc (sucLoc input-loc) save-slot sucLoc-bf eq)))
                snd-ptr)

            -- TODO (post-scaffold): rederive once prod-right-setup-input-helper
            -- signature is restated under StoredValue.
            rdi-right-setup-proof : readReg (regs s-right-setup) Input1 ≡ SV-Ptr snd-loc
            rdi-right-setup-proof = SMP.!!

        not-halted-right-setup : halted s-right-setup ≡ false
        not-halted-right-setup = SMP.TracePrimitives.exec-trace-preserves-halted-WF
                                   right-setup-trace s-l alloc-for-right l-not-halted
                                   (twf-∷ (SMP.!!) (twf-∷ tt
                                     (twf-∷ (SMP.!!) (twf-∷ tt twf-[]))))

        r-layer-valid-right-setup : ValidAtWF mvR alloc-for-right {⟦ FR ⟧T (μ-type G)} (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s-right-setup
        r-layer-valid-right-setup = validityWF-mem-preserved (coerce-functor⁻¹ FR (μ-type G) r-comp) snd-loc s-l s-right-setup
          r-snd-bf
          (λ loc' bf' → SMP.RecSchemeSemantics.prod-right-setup-mem-helper save-slot s-l alloc-for-right loc' l-not-halted
            (λ _ → SMP.!!))  -- The constraint is not used by the helper
          r-layer-valid-transferred

        ------------------------------------------------------------------------
        -- Phase 4: Right Processing
        ------------------------------------------------------------------------
        r-result-pair : ∃[ mOut ] ProcessedLayerResult wfG alg mOut wfR r-comp s-right-setup alloc-for-right
        r-result-pair = procRec wfR (fsize-prod-right _ _) r-comp mIn snd-loc s-right-setup alloc-for-right
                          (child-bound-prod-right wfG l-comp r-comp size-bound) r-layer-valid-right-setup r-snd-bf not-halted-right-setup rdi-right-setup

        mR : AllocMode
        mR = proj₁ r-result-pair

        r-result : ProcessedLayerResult wfG alg mR wfR r-comp s-right-setup alloc-for-right
        r-result = proj₂ r-result-pair

        r-processed : ⟦ ⟦ FR ⟧T A ⟧
        r-processed = ProcessedLayerResult.processed r-result

        processed : ⟦ ⟦ FL ⊗ FR ⟧T A ⟧
        processed = (l-processed , r-processed)

        r-trace : AbstractTrace
        r-trace = ProcessedLayerResult.trace r-result

        -- r-result uses alloc-for-right, so slot-monotone is from alloc-for-right
        r-slot-mono : next-slot alloc-for-right ≤ next-slot (ProcessedLayerResult.final-alloc r-result)
        r-slot-mono = ProcessedLayerResult.slot-monotone r-result

        final-alloc : AllocState {FS}
        final-alloc = ProcessedLayerResult.final-alloc r-result

        -- Phase 6: Perfect scratch reclaim
        reclaimable-slot-prod : ℕ
        reclaimable-slot-prod = next-slot final-alloc

        -- reclaim-monotone: next-slot alloc ≤ reclaimable-slot-prod = next-slot final-alloc
        reclaim-monotone-prod : next-slot alloc ≤ reclaimable-slot-prod
        reclaim-monotone-prod = ≤-trans (incr-next-slot-mono alloc) (≤-trans l-reclaim-mono r-slot-mono)

        -- reclaim-bounded: reclaimable-slot-prod = next-slot final-alloc (perfect reclaim)
        reclaim-bounded-prod : reclaimable-slot-prod ≡ next-slot final-alloc
        reclaim-bounded-prod = refl

        -- slot-stays-in-budget: next-slot final-alloc ≤ next-slot alloc + layer-capacity
        -- Uses prod-slot-budget helper with the SUM formula (1 + capL + capR)
        r-slot-stays-in-budget : next-slot final-alloc ≤ l-reclaimable +ℕ layer-capacity wfR wfG alg
        r-slot-stays-in-budget = ProcessedLayerResult.slot-stays-in-budget r-result

        slot-stays-in-budget-prod : next-slot final-alloc ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
        slot-stays-in-budget-prod = prod-slot-budget wfL wfR wfG alg alloc l-reclaimable final-alloc
                                      l-slot-usage r-slot-stays-in-budget

        -- Slot usage bound: reclaimable-slot-prod ≤ next-slot alloc + layer-capacity
        -- Since reclaimable-slot-prod = next-slot final-alloc, this equals slot-stays-in-budget
        slot-usage-bound-prod : reclaimable-slot-prod ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
        slot-usage-bound-prod = slot-stays-in-budget-prod

        -- Max slot used: max of both children's max-slot-used
        -- Product doesn't allocate any wrapper, so we just take the max
        l-max-slot-used : ℕ
        l-max-slot-used = ProcessedLayerResult.max-slot-used l-result

        r-max-slot-used : ℕ
        r-max-slot-used = ProcessedLayerResult.max-slot-used r-result

        r-reclaimable : ℕ
        r-reclaimable = next-slot (ProcessedLayerResult.final-alloc r-result)

        max-slot-used-prod : ℕ
        max-slot-used-prod = l-max-slot-used ⊔ r-max-slot-used

        -- Bounds for max-slot-used components
        l-max-slot-usage : l-max-slot-used ≤ next-slot alloc-for-left +ℕ layer-capacity wfL wfG alg
        l-max-slot-usage = ProcessedLayerResult.max-slot-usage-bound l-result

        r-max-slot-usage : r-max-slot-used ≤ next-slot alloc-for-right +ℕ layer-capacity wfR wfG alg
        r-max-slot-usage = ProcessedLayerResult.max-slot-usage-bound r-result

        -- Phase 6: reclaimable-slot-prod = next-slot final-alloc ≤ max-slot-used-prod
        -- Chain: reclaimable-slot-prod ≡ r-reclaimable (by perfect reclaim)
        --        r-reclaimable ≤ r-max-slot-used ≤ max-slot-used-prod
        reclaimable-geq-max : reclaimable-slot-prod ≤ max-slot-used-prod
        reclaimable-geq-max =
          let r-reclaim-leq-max : r-reclaimable ≤ r-max-slot-used
              r-reclaim-leq-max = ProcessedLayerResult.max-slot-geq-final r-result
              -- r-reclaimable ≡ next-slot final-alloc = reclaimable-slot-prod (by r-result's perfect reclaim)
              r-eq-prod : r-reclaimable ≡ reclaimable-slot-prod
              r-eq-prod = refl
          in subst (_≤ max-slot-used-prod) r-eq-prod
               (≤-trans r-reclaim-leq-max (n≤m⊔n l-max-slot-used r-max-slot-used))

        -- max-slot-used-prod ≤ next-slot alloc + layer-capacity (wf-Prod wfL wfR)
        -- layer-capacity (wf-Prod wfL wfR) = 1 + (capL ⊔ capR)
        -- l-max-slot-used ≤ suc (next-slot alloc) + capL ≤ next-slot alloc + 1 + capL ≤ next-slot alloc + 1 + (capL ⊔ capR)
        -- r-max-slot-used: Right child starts from l-reclaimable, and the key is that left and right
        -- share the capacity via max, not sum. The reclamation allows r to reuse l's slots.
        -- r-max-slot-used ≤ l-reclaimable + capR
        -- Since l-reclaimable ≤ l-max-slot-used (by max-slot-geq-reclaim), and l-max-slot-used ≤ suc n + capL:
        -- r-max-slot-used ≤ l-reclaimable + capR ≤ (suc n + capL) + capR
        -- But this gives capL + capR, not max(capL, capR)!
        -- max-slot-usage-bound-prod: max(l-max, r-max) ≤ next-slot alloc + layer-capacity
        -- With SUM formula: layer-capacity (wf-Prod wfL wfR) = 1 + capL + capR
        -- l-max ≤ suc (next-slot alloc) + capL ≤ next-slot alloc + (1 + capL + capR)
        -- r-max ≤ l-reclaimable + capR ≤ (suc (next-slot alloc) + capL) + capR = next-slot alloc + (1 + capL + capR)
        max-slot-usage-bound-prod : max-slot-used-prod ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
        max-slot-usage-bound-prod =
          let capL = layer-capacity wfL wfG alg
              capR = layer-capacity wfR wfG alg
              -- l-max-slot-used ≤ suc (next-slot alloc) + capL
              l-bound = l-max-slot-usage
              -- suc (next-slot alloc) + capL = next-slot alloc + suc capL
              suc-eq : suc (next-slot alloc) +ℕ capL ≡ next-slot alloc +ℕ suc capL
              suc-eq = sym (+-suc (next-slot alloc) capL)
              l-bound-rearranged : l-max-slot-used ≤ next-slot alloc +ℕ suc capL
              l-bound-rearranged = subst (l-max-slot-used ≤_) suc-eq l-bound
              -- suc capL ≤ suc (capL + capR) = 1 + capL + capR = layer-capacity (wf-Prod ...)
              l-cap-fit : suc capL ≤ suc (capL +ℕ capR)
              l-cap-fit = s≤s (m≤m+n capL capR)
              l-final : l-max-slot-used ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
              l-final = ≤-trans l-bound-rearranged (+-monoʳ-≤ (next-slot alloc) l-cap-fit)

              -- r-max-slot-used ≤ l-reclaimable + capR (from r-max-slot-usage and alloc-for-right)
              -- l-reclaimable ≤ suc (next-slot alloc) + capL (from l-slot-usage)
              -- so: r-max ≤ l-reclaimable + capR ≤ (suc (next-slot alloc) + capL) + capR
              r-step1 : l-reclaimable +ℕ capR ≤ (suc (next-slot alloc) +ℕ capL) +ℕ capR
              r-step1 = +-monoˡ-≤ capR l-slot-usage
              -- (suc n + capL) + capR = suc n + (capL + capR) = n + suc (capL + capR)
              combined-eq : (suc (next-slot alloc) +ℕ capL) +ℕ capR ≡ next-slot alloc +ℕ suc (capL +ℕ capR)
              combined-eq = trans (+-assoc (suc (next-slot alloc)) capL capR)
                                  (sym (+-suc (next-slot alloc) (capL +ℕ capR)))
              r-final : r-max-slot-used ≤ next-slot alloc +ℕ layer-capacity (wf-Prod wfL wfR) wfG alg
              r-final = ≤-trans r-max-slot-usage
                          (≤-trans r-step1 (≤-reflexive combined-eq))
          in ⊔-lub l-final r-final

        full-trace : AbstractTrace
        full-trace = left-setup-trace ++ l-trace ++ right-setup-trace ++ r-trace

        ------------------------------------------------------------------------
        -- Trace composition proofs (now possible with where clause)
        ------------------------------------------------------------------------

        -- Left setup execution
        left-setup-exec : exec-trace left-setup-trace s alloc ≡ (s-left-setup , alloc-left-setup)
        left-setup-exec = refl

        -- Trace correctness composition
        trace-correct-proof : proj₁ (exec-trace full-trace s alloc) ≡
                              ProcessedLayerResult.final-state r-result
        trace-correct-proof = trans step1 (trans step2 (trans step3 (trans step4 step5)))
          where
            -- Step 1: Decompose full-trace, extracting left-setup-trace
            step1 : proj₁ (exec-trace full-trace s alloc) ≡
                    proj₁ (exec-trace (l-trace ++ right-setup-trace ++ r-trace) s-left-setup alloc-left-setup)
            step1 = cong proj₁ (SMP.TraceComposition.exec-trace-append left-setup-trace (l-trace ++ right-setup-trace ++ r-trace) s alloc)

            -- Step 2: alloc-left-setup = alloc, so substitute
            step2 : proj₁ (exec-trace (l-trace ++ right-setup-trace ++ r-trace) s-left-setup alloc-left-setup) ≡
                    proj₁ (exec-trace (l-trace ++ right-setup-trace ++ r-trace) s-left-setup alloc)
            step2 = cong (λ a → proj₁ (exec-trace (l-trace ++ right-setup-trace ++ r-trace) s-left-setup a))
                         alloc-left-setup-eq

            -- Step 3: Decompose, extracting l-trace
            -- After l-trace, state is s-l (using exec-trace-incr-next-slot)
            alloc-after-l : AllocState {FS}
            alloc-after-l = proj₂ (exec-trace l-trace s-left-setup alloc)

            -- The states after l-trace are the same regardless of alloc vs alloc-for-left
            l-state-eq : proj₁ (exec-trace l-trace s-left-setup alloc) ≡ s-l
            l-state-eq = trans (exec-trace-incr-next-slot l-trace s-left-setup alloc)
                               (ProcessedLayerResult.trace-correct l-result)

            -- The frames are preserved through l-trace
            frame-after-l-alloc : current-frame alloc-after-l ≡ current-frame alloc
            frame-after-l-alloc = SMP.TracePrimitives.exec-trace-preserves-frame l-trace s-left-setup alloc

            frame-after-l-eq : current-frame alloc-after-l ≡ current-frame alloc-l
            frame-after-l-eq = trans frame-after-l-alloc
                                     (trans (sym (incr-next-slot-frame alloc))
                                            (sym (ProcessedLayerResult.frame-preserved l-result)))

            step3 : proj₁ (exec-trace (l-trace ++ right-setup-trace ++ r-trace) s-left-setup alloc) ≡
                    proj₁ (exec-trace (right-setup-trace ++ r-trace) s-l alloc-after-l)
            step3 = trans (cong proj₁ (SMP.TraceComposition.exec-trace-append l-trace (right-setup-trace ++ r-trace) s-left-setup alloc))
                          (cong (λ s' → proj₁ (exec-trace (right-setup-trace ++ r-trace) s' alloc-after-l)) l-state-eq)

            -- Step 4: Bridge from alloc-after-l to alloc-for-right (same current-frame)
            -- The frames are equal: alloc-after-l has frame = alloc, alloc-for-right has frame = alloc
            frame-after-l-to-right : current-frame alloc-after-l ≡ current-frame alloc-for-right
            frame-after-l-to-right = trans frame-after-l-alloc (sym alloc-for-right-frame)

            step4 : proj₁ (exec-trace (right-setup-trace ++ r-trace) s-l alloc-after-l) ≡
                    proj₁ (exec-trace (right-setup-trace ++ r-trace) s-l alloc-for-right)
            step4 = SMP.TracePrimitives.exec-trace-same-frame (right-setup-trace ++ r-trace) s-l alloc-after-l alloc-for-right frame-after-l-to-right

            -- Step 5: Decompose right-setup and r-trace (now using alloc-for-right)
            -- After right-setup, alloc is preserved (prod-right-setup-alloc-helper)
            alloc-after-right-setup : AllocState {FS}
            alloc-after-right-setup = proj₂ (exec-trace right-setup-trace s-l alloc-for-right)

            right-setup-alloc-eq : alloc-after-right-setup ≡ alloc-for-right
            right-setup-alloc-eq = SMP.RecSchemeSemantics.prod-right-setup-alloc-helper save-slot s-l alloc-for-right l-not-halted

            step5 : proj₁ (exec-trace (right-setup-trace ++ r-trace) s-l alloc-for-right) ≡
                    ProcessedLayerResult.final-state r-result
            step5 = trans step5a (trans step5b (ProcessedLayerResult.trace-correct r-result))
              where
                -- Decompose the trace
                step5a : proj₁ (exec-trace (right-setup-trace ++ r-trace) s-l alloc-for-right) ≡
                         proj₁ (exec-trace r-trace s-right-setup alloc-after-right-setup)
                step5a = cong proj₁ (SMP.TraceComposition.exec-trace-append right-setup-trace r-trace s-l alloc-for-right)

                -- Substitute alloc back to alloc-for-right
                step5b : proj₁ (exec-trace r-trace s-right-setup alloc-after-right-setup) ≡
                         proj₁ (exec-trace r-trace s-right-setup alloc-for-right)
                step5b = cong (λ a → proj₁ (exec-trace r-trace s-right-setup a)) right-setup-alloc-eq

        -- Memory preservation composition
        mem-preserved-proof : ∀ loc → BeforeFrontier alloc loc →
                              readLoc (ProcessedLayerResult.final-state r-result) loc ≡ readLoc s loc
        mem-preserved-proof loc bf = trans step4 (trans step3 (trans step2 step1))
          where
            -- Preserved through left setup (except save-slot, but bf excludes that)
            step1 : readLoc s-left-setup loc ≡ readLoc s loc
            step1 = prod-left-setup-mem-eq save-slot s alloc loc not-halted
              (λ eq → Data.Nat.Properties.<-irrefl refl (bf-slot-contradiction alloc loc save-slot bf eq))

            -- Preserved through left processing
            bf-for-left : BeforeFrontier alloc-for-left loc
            bf-for-left = frontier-monotone alloc alloc-for-left refl (incr-next-slot-mono alloc) ≤-refl loc bf

            step2 : readLoc s-l loc ≡ readLoc s-left-setup loc
            step2 = ProcessedLayerResult.mem-preserved l-result loc bf-for-left

            -- Preserved through right setup (now using alloc-for-right)
            bf-for-right : BeforeFrontier alloc-for-right loc
            bf-for-right = frontier-monotone alloc alloc-for-right
                             (sym alloc-for-right-frame)
                             (≤-trans (incr-next-slot-mono alloc) l-reclaim-mono)
                             (subst (next-heap-ref alloc ≤_) (sym alloc-for-right-heap) ≤-refl)
                             loc bf

            step3 : readLoc s-right-setup loc ≡ readLoc s-l loc
            step3 = SMP.RecSchemeSemantics.prod-right-setup-mem-helper save-slot s-l alloc-for-right loc l-not-halted
              (λ _ → SMP.!!)  -- The callback is ignored in the implementation

            -- Preserved through right processing
            step4 : readLoc (ProcessedLayerResult.final-state r-result) loc ≡ readLoc s-right-setup loc
            step4 = ProcessedLayerResult.mem-preserved r-result loc bf-for-right

        -- Validity proof: need pair container allocation (like Sum inj₁ has wrapper allocation)
        -- Currently result-loc = r-result-loc (just the right component)
        -- But processed = (l-processed, r-processed), which needs a pair container
        -- Fix: add pair-wrapper-trace to allocate [fst-ptr, snd-ptr] at frontier
        processed-valid-proof : ValidAtWF mR final-alloc processed
                                  (place-loc (ProcessedLayerResult.result-place r-result))
                                  (ProcessedLayerResult.final-state r-result)
        processed-valid-proof = SMP.!!  -- BLOCKED: missing pair container allocation

        -- Setup trace halted preservation proofs
        left-setup-tph : ∀ {s alloc} → TraceWF s alloc left-setup-trace
        left-setup-tph = twf-∷ tt (twf-∷ tt
                          (twf-∷ (SMP.!!) (twf-∷ tt twf-[])))

        right-setup-tph : ∀ {s alloc} → TraceWF s alloc right-setup-trace
        right-setup-tph = twf-∷ (SMP.!!) (twf-∷ tt
                            (twf-∷ (SMP.!!) (twf-∷ tt twf-[])))

        -- Note: left-setup-tpc and right-setup-tpc removed in Phase 3

        -- Trace region bounds
        -- full-trace = left-setup-trace ++ l-trace ++ right-setup-trace ++ r-trace
        -- left-setup writes to save-slot = next-slot alloc
        -- right-setup reads from save-slot = next-slot alloc

        -- Left setup: mov-to-output writes nothing, store-at-slot writes save-slot, others nothing
        left-setup-twa : TraceWritesAbove (next-slot alloc) left-setup-trace
        left-setup-twa = ≤-refl , tt  -- store-at-slot writes to save-slot = next-slot alloc

        left-setup-twb : TraceWritesBelow max-slot-used-prod left-setup-trace
        left-setup-twb = save-slot<max , tt
          where
            -- save-slot < max-slot-used-prod because:
            -- save-slot = next-slot alloc < suc save-slot ≤ l-reclaimable ≤ l-max-slot-used ≤ max-slot-used-prod
            l-reclaim-leq-max : l-reclaimable ≤ l-max-slot-used
            l-reclaim-leq-max = ProcessedLayerResult.max-slot-geq-final l-result
            save-slot<max : save-slot < max-slot-used-prod
            save-slot<max = <-≤-trans (n<1+n save-slot)
                              (≤-trans l-reclaim-mono
                                (≤-trans l-reclaim-leq-max
                                  (m≤m⊔n l-max-slot-used r-max-slot-used)))

        -- Right setup: load-from-slot reads, others read nothing; no writes
        right-setup-twa : TraceWritesAbove (next-slot alloc) right-setup-trace
        right-setup-twa = tt  -- No slot writes

        right-setup-twb : TraceWritesBelow max-slot-used-prod right-setup-trace
        right-setup-twb = tt  -- No slot writes

        -- l-trace bounds (from l-result, converted via monotonicity)
        l-trace-twa : TraceWritesAbove (next-slot alloc) l-trace
        l-trace-twa = SMP.trace-writes-above-mono (next-slot alloc) (next-slot alloc-for-left) l-trace
                        (n≤1+n (next-slot alloc))
                        (ProcessedLayerResult.trace-writes-above l-result)

        -- Using max-slot-used-prod: l-max-slot-used ≤ max-slot-used-prod (via m≤m⊔n)
        l-trace-twb : TraceWritesBelow max-slot-used-prod l-trace
        l-trace-twb = SMP.trace-writes-below-mono l-max-slot-used max-slot-used-prod l-trace
                        (m≤m⊔n l-max-slot-used r-max-slot-used)
                        (ProcessedLayerResult.trace-writes-below l-result)

        -- r-trace bounds (from r-result, using alloc-for-right)
        r-trace-twa : TraceWritesAbove (next-slot alloc) r-trace
        r-trace-twa = SMP.trace-writes-above-mono (next-slot alloc) (next-slot alloc-for-right) r-trace
                        (≤-trans (incr-next-slot-mono alloc) l-reclaim-mono)
                        (ProcessedLayerResult.trace-writes-above r-result)

        -- Using max-slot-used-prod: r-max-slot-used ≤ max-slot-used-prod (via n≤m⊔n)
        r-trace-twb : TraceWritesBelow max-slot-used-prod r-trace
        r-trace-twb = SMP.trace-writes-below-mono r-max-slot-used max-slot-used-prod r-trace
                        (n≤m⊔n l-max-slot-used r-max-slot-used)
                        (ProcessedLayerResult.trace-writes-below r-result)

        trace-writes-above-proof : TraceWritesAbove (next-slot alloc) full-trace
        trace-writes-above-proof =
          SMP.trace-writes-above-append (next-slot alloc) left-setup-trace (l-trace ++ right-setup-trace ++ r-trace)
            left-setup-twa
            (SMP.trace-writes-above-append (next-slot alloc) l-trace (right-setup-trace ++ r-trace)
              l-trace-twa
              (SMP.trace-writes-above-append (next-slot alloc) right-setup-trace r-trace
                right-setup-twa r-trace-twa))

        trace-writes-below-proof : TraceWritesBelow max-slot-used-prod full-trace
        trace-writes-below-proof =
          SMP.trace-writes-below-append max-slot-used-prod left-setup-trace (l-trace ++ right-setup-trace ++ r-trace)
            left-setup-twb
            (SMP.trace-writes-below-append max-slot-used-prod l-trace (right-setup-trace ++ r-trace)
              l-trace-twb
              (SMP.trace-writes-below-append max-slot-used-prod right-setup-trace r-trace
                right-setup-twb r-trace-twb))

        -- Slot reads: left-setup reads nothing, right-setup reads save-slot
        left-setup-tsra : TraceSlotReadsAbove (next-slot alloc) left-setup-trace
        left-setup-tsra = tt  -- No slot reads

        left-setup-tsrb : TraceSlotReadsBelow max-slot-used-prod left-setup-trace
        left-setup-tsrb = tt  -- No slot reads

        right-setup-tsra : TraceSlotReadsAbove (next-slot alloc) right-setup-trace
        right-setup-tsra = ≤-refl , tt  -- load-from-slot reads save-slot = next-slot alloc

        -- right-setup reads save-slot; need save-slot < max-slot-used-prod
        -- save-slot = next-slot alloc < suc (next-slot alloc) = next-slot alloc-for-left
        -- next-slot alloc-for-left ≤ l-max-slot-used (since max-slot-used tracks all writes including alloc)
        -- Actually: save-slot < next-slot alloc-for-left ≤ l-reclaimable ≤ l-max-slot-used ≤ max-slot-used-prod
        right-setup-tsrb : TraceSlotReadsBelow max-slot-used-prod right-setup-trace
        right-setup-tsrb = save-slot<max , tt
          where
            -- l-result.reclaimable-slot ≤ l-result.max-slot-used (from max-slot-geq-reclaim)
            l-reclaim-leq-max : l-reclaimable ≤ l-max-slot-used
            l-reclaim-leq-max = ProcessedLayerResult.max-slot-geq-final l-result
            -- save-slot < suc save-slot ≤ l-reclaimable ≤ l-max-slot-used ≤ max-slot-used-prod
            save-slot<max : save-slot < max-slot-used-prod
            save-slot<max = <-≤-trans (n<1+n save-slot)
                              (≤-trans l-reclaim-mono
                                (≤-trans l-reclaim-leq-max
                                  (m≤m⊔n l-max-slot-used r-max-slot-used)))

        -- l-trace and r-trace slot reads (from results, converted via monotonicity)
        l-trace-tsra : TraceSlotReadsAbove (next-slot alloc) l-trace
        l-trace-tsra = SMP.trace-slot-reads-above-mono (next-slot alloc) (next-slot alloc-for-left) l-trace
                         (n≤1+n (next-slot alloc))
                         (ProcessedLayerResult.trace-slot-reads-above l-result)

        -- Using max-slot-used-prod: l-max-slot-used ≤ max-slot-used-prod (via m≤m⊔n)
        l-trace-tsrb : TraceSlotReadsBelow max-slot-used-prod l-trace
        l-trace-tsrb = SMP.trace-slot-reads-below-mono l-max-slot-used max-slot-used-prod l-trace
                         (m≤m⊔n l-max-slot-used r-max-slot-used)
                         (ProcessedLayerResult.trace-slot-reads-below l-result)

        r-trace-tsra : TraceSlotReadsAbove (next-slot alloc) r-trace
        r-trace-tsra = SMP.trace-slot-reads-above-mono (next-slot alloc) (next-slot alloc-for-right) r-trace
                         (≤-trans (incr-next-slot-mono alloc) l-reclaim-mono)
                         (ProcessedLayerResult.trace-slot-reads-above r-result)

        -- Using max-slot-used-prod: r-max-slot-used ≤ max-slot-used-prod (via n≤m⊔n)
        r-trace-tsrb : TraceSlotReadsBelow max-slot-used-prod r-trace
        r-trace-tsrb = SMP.trace-slot-reads-below-mono r-max-slot-used max-slot-used-prod r-trace
                         (n≤m⊔n l-max-slot-used r-max-slot-used)
                         (ProcessedLayerResult.trace-slot-reads-below r-result)

        trace-slot-reads-above-proof : TraceSlotReadsAbove (next-slot alloc) full-trace
        trace-slot-reads-above-proof =
          SMP.trace-slot-reads-above-append (next-slot alloc) left-setup-trace (l-trace ++ right-setup-trace ++ r-trace)
            left-setup-tsra
            (SMP.trace-slot-reads-above-append (next-slot alloc) l-trace (right-setup-trace ++ r-trace)
              l-trace-tsra
              (SMP.trace-slot-reads-above-append (next-slot alloc) right-setup-trace r-trace
                right-setup-tsra r-trace-tsra))

        trace-slot-reads-below-proof : TraceSlotReadsBelow max-slot-used-prod full-trace
        trace-slot-reads-below-proof =
          SMP.trace-slot-reads-below-append max-slot-used-prod left-setup-trace (l-trace ++ right-setup-trace ++ r-trace)
            left-setup-tsrb
            (SMP.trace-slot-reads-below-append max-slot-used-prod l-trace (right-setup-trace ++ r-trace)
              l-trace-tsrb
              (SMP.trace-slot-reads-below-append max-slot-used-prod right-setup-trace r-trace
                right-setup-tsrb r-trace-tsrb))

  ------------------------------------------------------------------------
  -- make-proc-rec: builds the functor-recursion capability from an
  -- accessibility witness on functor-size. process-layer/process-layer-prod
  -- (above) call the `procRec` PARAMETER for sub-layer descent, so foetus
  -- treats them as NON-recursive (it does not track parameter applications)
  -- — their heavy bodies leave the termination SCC. The only recursive SCC
  -- here is {make-proc-rec} itself (self-recursive on the structurally
  -- smaller Acc `rs fs<`), which is tiny. Standalone (not in a mutual
  -- block): it calls process-layer, which never calls back.
  ------------------------------------------------------------------------
  make-proc-rec : ∀ {G A} {wfG : WellFormedF G} {alg : IR (⟦ G ⟧T A) A} {n : ℕ}
    (dispatch : RecDispatcherWF (ir-size (Cata wfG alg)))
    (rec : CataRecBound wfG alg n)
    → ∀ {nf} → Acc _<_ nf → ProcLayerCap wfG alg n nf
  make-proc-rec {wfG = wfG} {alg = alg} {n = n} dispatch rec (acc rs)
    wfF fs< layer mIn input-loc s alloc sb validity bf nh rdi =
    process-layer wfF wfG alg dispatch layer mIn input-loc s alloc n rec
      (make-proc-rec dispatch rec (rs fs<)) sb validity bf nh rdi

  ------------------------------------------------------------------------
  -- Plan 0.27 perf: SEPARATE mutual block for the μ-Acc recursion
  -- {make-cata-rec, cata-dispatched-new} + cata-only helpers. process-layer
  -- /process-layer-prod are above (their own non-recursive defs). No
  -- forward-ref break: process-layer/-prod use none of these.
  ------------------------------------------------------------------------
  mutual
    ------------------------------------------------------------------------
    -- Cata Dispatched (New Architecture)
    --
    -- Uses two-phase approach:
    --   1. process-layer: compute ⟦ G ⟧F A' from ⟦ G ⟧F (⟦μ⟧ G)
    --   2. apply algebra: compute alg (processed-layer)
    ------------------------------------------------------------------------

    -- Helper: readLoc ignores changes to regs field
    -- Pattern matching helps Agda see the definitional equality
    readLoc-regs-irrelevant : ∀ (s : LocState FS) (r : Registers FS) (loc : ValueLocation FS) →
      readLoc (record s { regs = r }) loc ≡ readLoc s loc
    readLoc-regs-irrelevant s r (AtStack f k) = refl
    readLoc-regs-irrelevant s r (AtDynamic hl) = refl

    -- Helper: mov-to-input state equals manual Input1 write when Output = target
    -- exec-abstract mov-to-input s alloc = (record s { regs = writeReg (regs s) Input1 (readReg (regs s) Output) }, alloc)
    -- When Output = target-loc, this equals (record s { regs = writeReg (regs s) Input1 target-loc }, alloc)
    exec-mov-to-input-state : ∀ (s : LocState FS) (alloc : AllocState {FS}) (target-loc : ValueLocation FS) →
      readReg (regs s) Output ≡ SV-Ptr target-loc →
      proj₁ (exec-abstract mov-to-input s alloc) ≡ record s { regs = writeReg (regs s) Input1 (SV-Ptr target-loc) }
    exec-mov-to-input-state s alloc target-loc output-eq =
      cong (λ loc → record s { regs = writeReg (regs s) Input1 loc }) output-eq

    -- Builds the reified cata-recursion capability from an accessibility
    -- witness: a child of size < n yields a structurally-smaller Acc
    -- (rs lt), which justifies the recursive cata-dispatched-new call.
    -- {make-cata-rec, cata-dispatched-new} is the ONLY SCC foetus analyses
    -- for the well-founded recursion — process-layer/process-layer-prod are
    -- out of it (they take the capability as a parameter).
    make-cata-rec : ∀ {G A} {wfG : WellFormedF G} {alg : IR (⟦ G ⟧T A) A} {n : ℕ}
      (dispatch : RecDispatcherWF (ir-size (Cata wfG alg)))
      → Acc _<_ n → CataRecBound wfG alg n
    make-cata-rec {wfG = wfG} {alg = alg} dispatch (acc rs) c lt mIn input-loc s alloc valid bf nh rdi =
      cata-dispatched-new wfG alg dispatch c mIn input-loc s alloc (rs lt) valid bf nh rdi

    -- cata-dispatched-new delegates to process-layer for layer handling
    -- and to dispatcher for algebra execution.
    -- Plan 0.27: validity is mode-polymorphic (mv) and the layer validity
    -- is the μ-value's own ValidAtWF unwrapped via out-μ-valid — NO
    -- extract-μLayerValid / μValid→μValidAtWF bridges.
    cata-dispatched-new : ∀ {mv G A}
      (wfG : WellFormedF G)
      (alg : IR (⟦ G ⟧T A) A)
      (dispatch : RecDispatcherWF (ir-size (Cata wfG alg)))
      (x : ⟦μ⟧ G)
      (mIn : AllocMode)
      (input-loc : ValueLocation FS)
      (s : LocState FS) (alloc : AllocState {FS})
      -- Plan 0.27 Option B: accessibility on the μ-value's size — the
      -- well-foundedness witness (replaces {-# TERMINATING #-}).
      (wf-acc : Acc _<_ (μ-size wfG x))
      → ValidAtWF mv alloc x input-loc s
      → BeforeFrontier alloc input-loc
      → halted s ≡ false
      → readReg (regs s) Input1 ≡ SV-Ptr input-loc
      → ∃[ mOut ] IRResultAWF mOut (Cata wfG alg) x s alloc
    cata-dispatched-new {mv} {G} {A} wfG alg dispatch x mIn input-loc s alloc
      wf-acc x-valid input-before not-halted rdi-eq =
      let
        -- Step 1: Destruct to get layer
        layer : ⟦ G ⟧F (⟦μ⟧ G)
        layer = sem-Out wfG x

        -- Step 1b: layer validity = the μ-value's own ValidAtWF, unwrapped
        -- to the layer via out-μ-valid (eval (out-μ wfG) x ≡ coerce⁻¹ layer
        -- definitionally). No extract-μLayerValid bridge.
        layer-valid : ValidAtWF mv alloc {⟦ G ⟧T (μ-type G)} (coerce-functor⁻¹ G (μ-type G) layer) input-loc s
        layer-valid = out-μ-valid wfG x x-valid

        -- Step 2: Process layer to get ⟦ G ⟧F A
        (mLayer , layer-result) = process-layer wfG wfG alg dispatch layer mIn input-loc s alloc
                                    (μ-size wfG x) (make-cata-rec dispatch wf-acc)
                                    (make-proc-rec dispatch (make-cata-rec dispatch wf-acc) (<-wellFounded (functor-size G)))
                                    (child-sum-< wfG x) layer-valid input-before not-halted rdi-eq

        -- Extract layer processing results
        processed-layer = ProcessedLayerResult.processed layer-result
        s-layer = ProcessedLayerResult.final-state layer-result
        alloc-layer = ProcessedLayerResult.final-alloc layer-result
        layer-loc = place-loc (ProcessedLayerResult.result-place layer-result)
        layer-trace = ProcessedLayerResult.trace layer-result
        layer-valid-wf = place-valid (ProcessedLayerResult.result-place layer-result)
        layer-before = place-before (ProcessedLayerResult.result-place layer-result)
        layer-rax = place-rax (ProcessedLayerResult.result-place layer-result)
        layer-not-halted = ProcessedLayerResult.not-halted layer-result
        layer-sem-correct = ProcessedLayerResult.semantic-correct layer-result

        -- Step 3: Bridge state with mov-to-input for algebra
        s-bridged : LocState FS
        s-bridged = record s-layer { regs = writeReg (regs s-layer) Input1 (SV-Ptr layer-loc) }

        rdi-bridged : readReg (regs s-bridged) Input1 ≡ SV-Ptr layer-loc
        rdi-bridged = writeReg-same (regs s-layer) Input1 (SV-Ptr layer-loc)

        layer-valid-bridged : ValidAtWF mLayer alloc-layer processed-layer layer-loc s-bridged
        layer-valid-bridged = validityWF-mem-only processed-layer layer-loc s-layer s-bridged refl refl layer-valid-wf

        -- Step 4: Apply algebra via dispatcher
        -- alg has smaller size than Cata
        alg-bound : ir-size alg < ir-size (Cata wfG alg)
        alg-bound = alg-size-bound wfG alg

        -- Slot usage bounds for composition proofs
        layer-slot-usage-bound : next-slot (ProcessedLayerResult.final-alloc layer-result)
                                  ≤ next-slot alloc +ℕ layer-capacity wfG wfG alg
        layer-slot-usage-bound = ProcessedLayerResult.slot-usage-bound layer-result

        layer-cap-bounded : layer-capacity wfG wfG alg ≤ ir-stack-requirement (Cata wfG alg)
        layer-cap-bounded = layer-cap-bound wfG wfG alg

        -- Call dispatcher on algebra
        dispatch-result : ∃[ mOut ] IRResultAWF mOut alg processed-layer s-bridged alloc-layer
        dispatch-result = dispatch mLayer alg alg-bound processed-layer
                            layer-loc s-bridged alloc-layer
                            layer-valid-bridged layer-before layer-not-halted rdi-bridged
        mAlg : AllocMode
        mAlg = proj₁ dispatch-result
        alg-result : IRResultAWF mAlg alg processed-layer s-bridged alloc-layer
        alg-result = proj₂ dispatch-result

        -- Step 5: Build final IRResultAWF
        -- Trace: layer-trace ++ mov-to-input ∷ alg-trace
        final-trace = layer-trace ++ mov-to-input ∷ IRResultAWF.trace alg-result

        -- Semantic correctness via sem-cata-compute:
        --   sem-cata wfG alg x = alg (sem-fmap G (sem-cata wfG alg) (sem-Out wfG x))
        --                      = alg processed-layer  (by layer-sem-eq)
        --                      = eval alg processed-layer

        -- Key semantic equality: eval (Cata wfG alg) x ≡ eval alg processed-layer
        -- Proof chain:
        --   eval (Cata wfG alg) x
        --   = sem-cata wfG (λ fa → eval alg (coerce⁻¹ fa)) x           [by def of eval for Cata]
        --   = sem-cata ... (sem-In G layer)                            [since x = sem-In G (sem-Out wfG x)]
        --   = (λ fa → eval alg (coerce⁻¹ fa)) (sem-fmap G (sem-cata ...) layer)  [by sem-cata-compute]
        --   = eval alg (coerce⁻¹ (sem-fmap G (eval (Cata wfG alg)) layer))      [β-reduction + def eq]
        --   = eval alg processed-layer                                 [by layer-sem-correct]
        cata-sem-eq : eval (Cata wfG alg) x ≡ eval alg processed-layer
        cata-sem-eq =
          trans (cong (sem-cata wfG (λ fa → eval alg (coerce-struct⁻¹ G A fa)))
                      (sym (sem-In-Out wfG x)))
                (trans (sem-cata-compute wfG (λ fa → eval alg (coerce-struct⁻¹ G A fa)) layer)
                       (cong (eval alg) (sym layer-sem-correct)))

        -- Extract layer processing properties for composition
        layer-frame-preserved = ProcessedLayerResult.frame-preserved layer-result
        layer-slot-mono = ProcessedLayerResult.slot-monotone layer-result
        layer-heap-mono = ProcessedLayerResult.heap-monotone layer-result
        -- Note: layer-cap-preserved removed in Phase 3

        -- Compositional proofs
        frame-preserved-proof : current-frame (IRResultAWF.final-alloc alg-result) ≡ current-frame alloc
        frame-preserved-proof = trans (IRResultAWF.frame-preserved alg-result) layer-frame-preserved

        slot-mono-proof : next-slot alloc ≤ next-slot (IRResultAWF.final-alloc alg-result)
        slot-mono-proof = ≤-trans layer-slot-mono (IRResultAWF.slot-monotone alg-result)

        -- heap-pres-proof: chain alg-result.heap-preserved + layer-heap-preserved.
        -- alg-result runs on alloc-layer, so gives ≡ between alg-final and alloc-layer.
        -- layer-heap-preserved gives ≡ between alloc-layer and alloc.
        -- Plan 0.14 Phase B.0: IRResultAWF.heap-preserved removed; alg-result
        -- comes from a stack-only sub-IR (heap-budget = 0), so derivable via
        -- CWF.heap-preserved-of. SMP.!! placeholder pending the "stack-only" hypothesis.
        heap-pres-proof : next-heap-ref (IRResultAWF.final-alloc alg-result) ≡ next-heap-ref alloc
        heap-pres-proof = SMP.!!

        -- Note: cap-preserved-proof removed in Phase 3

        -- Runtime alloc after layer processing (needed for heap-ref preservation)
        layer-runtime-alloc : AllocState {FS}
        layer-runtime-alloc = proj₂ (exec-trace layer-trace s alloc)

        -- Heap-ref preservation: layer processing doesn't modify heap
        -- Since trace-no-heap-writes holds for layer-trace, heap ref is preserved
        layer-runtime-heap-preserved : next-heap-ref layer-runtime-alloc ≡ next-heap-ref alloc
        layer-runtime-heap-preserved = exec-trace-preserves-heap-ref layer-trace s alloc

        -- For alloc-layer: use ProcessedLayerResult.heap-preserved
        -- For polynomial functors (K, Sum, Prod), heap is unchanged
        layer-heap-preserved : next-heap-ref alloc-layer ≡ next-heap-ref alloc
        layer-heap-preserved = ProcessedLayerResult.heap-preserved layer-result

        -- Memory preservation composition
        layer-mem-pres = ProcessedLayerResult.mem-preserved layer-result
        alg-mem-pres = irresult-mem-preserved alg-result

        mem-preserved-proof : ∀ loc → BeforeFrontier alloc loc →
          readLoc (IRResultAWF.final-state alg-result) loc ≡ readLoc s loc
        mem-preserved-proof loc bf =
          let bf-layer = frontier-monotone alloc alloc-layer
                          (sym layer-frame-preserved) layer-slot-mono layer-heap-mono loc bf
              -- s-bridged = record s-layer { regs = ... }
              bridged-eq = readLoc-regs-irrelevant s-layer (writeReg (regs s-layer) Input1 (SV-Ptr layer-loc)) loc
          in trans (alg-mem-pres loc bf-layer) (trans bridged-eq (layer-mem-pres loc bf))

        -- Trace correctness: compose layer-trace ++ mov-to-input ∷ alg-trace
        alg-trace = IRResultAWF.trace alg-result
        final-state = IRResultAWF.final-state alg-result

        -- State after mov-to-input (using runtime alloc)
        s-after-mov : LocState FS
        s-after-mov = proj₁ (exec-abstract mov-to-input s-layer layer-runtime-alloc)

        -- Key: s-after-mov equals s-bridged (up to definitional equality via layer-rax)
        s-after-mov-eq-bridged : s-after-mov ≡ s-bridged
        s-after-mov-eq-bridged = exec-mov-to-input-state s-layer layer-runtime-alloc layer-loc layer-rax

        -- Alloc after mov-to-input (unchanged)
        alloc-after-mov : AllocState {FS}
        alloc-after-mov = proj₂ (exec-abstract mov-to-input s-layer layer-runtime-alloc)

        -- Step 1: Split trace via exec-trace-append
        trace-step1 : exec-trace final-trace s alloc ≡
                      exec-trace (mov-to-input ∷ alg-trace) s-layer layer-runtime-alloc
        trace-step1 = trans
          (exec-trace-append layer-trace (mov-to-input ∷ alg-trace) s alloc)
          (cong (λ st → exec-trace (mov-to-input ∷ alg-trace) st layer-runtime-alloc)
                (ProcessedLayerResult.trace-correct layer-result))

        -- Step 2: Execute mov-to-input via exec-trace-cons
        trace-step2 : exec-trace (mov-to-input ∷ alg-trace) s-layer layer-runtime-alloc ≡
                      exec-trace alg-trace s-after-mov alloc-after-mov
        trace-step2 = exec-trace-cons mov-to-input alg-trace s-layer layer-runtime-alloc layer-not-halted

        -- Step 3: Substitute s-after-mov with s-bridged
        trace-step3 : exec-trace alg-trace s-after-mov alloc-after-mov ≡
                      exec-trace alg-trace s-bridged alloc-after-mov
        trace-step3 = cong (λ st → exec-trace alg-trace st alloc-after-mov) s-after-mov-eq-bridged

        -- Key: alloc-after-mov and alloc-layer have the same current-frame
        -- This follows from frame-preserved property of ProcessedLayerResult
        -- alloc-after-mov = proj₂ (exec-abstract mov-to-input s-layer layer-runtime-alloc)
        -- mov-to-input preserves alloc, so alloc-after-mov ≡ layer-runtime-alloc
        alloc-after-mov-eq : alloc-after-mov ≡ layer-runtime-alloc
        alloc-after-mov-eq = refl  -- mov-to-input doesn't change alloc

        -- Bridge runtime to compile-time alloc via frame preservation
        layer-runtime-frame-eq : current-frame layer-runtime-alloc ≡ current-frame alloc-layer
        layer-runtime-frame-eq =
          trans (SMP.TracePrimitives.exec-trace-preserves-frame layer-trace s alloc)
                (sym (ProcessedLayerResult.frame-preserved layer-result))

        alloc-frame-eq : current-frame alloc-after-mov ≡ current-frame alloc-layer
        alloc-frame-eq = trans (cong current-frame alloc-after-mov-eq) layer-runtime-frame-eq

        -- Use exec-trace-same-frame: state depends only on current-frame
        alg-trace-frame-indep : proj₁ (exec-trace alg-trace s-bridged alloc-after-mov) ≡
                                proj₁ (exec-trace alg-trace s-bridged alloc-layer)
        alg-trace-frame-indep = exec-trace-same-frame alg-trace s-bridged alloc-after-mov alloc-layer alloc-frame-eq

        -- Final trace composition (for state only)
        trace-correct-proof : proj₁ (exec-trace final-trace s alloc) ≡ final-state
        trace-correct-proof = trans (cong proj₁ (trans trace-step1 (trans trace-step2 trace-step3)))
          (trans alg-trace-frame-indep (IRResultAWF.trace-correct alg-result))

        -- Plan 0.14: alloc-correct parallel to trace-correct-proof.
        -- After all trace-step{1,2,3}, alloc is at alloc-after-mov (= alloc-layer
        -- by mov-to-input preserves alloc + alloc-after-mov-eq + layer-result.alloc-correct).
        -- Bridge alloc-after-mov ≡ alloc-layer, then use alg-result.alloc-correct.
        alloc-after-mov-eq-alloc-layer : alloc-after-mov ≡ alloc-layer
        alloc-after-mov-eq-alloc-layer =
          trans alloc-after-mov-eq  -- = layer-runtime-alloc (refl, mov preserves)
                (ProcessedLayerResult.alloc-correct layer-result)

        alg-trace-alloc-bridge :
          proj₂ (exec-trace alg-trace s-bridged alloc-after-mov) ≡
          proj₂ (exec-trace alg-trace s-bridged alloc-layer)
        alg-trace-alloc-bridge = cong (λ a → proj₂ (exec-trace alg-trace s-bridged a))
                                      alloc-after-mov-eq-alloc-layer

        alloc-correct-proof : proj₂ (exec-trace final-trace s alloc) ≡
                              IRResultAWF.final-alloc alg-result
        alloc-correct-proof =
          trans (cong proj₂ (trans trace-step1 (trans trace-step2 trace-step3)))
                (trans alg-trace-alloc-bridge (IRResultAWF.alloc-correct alg-result))

        -- Max slot written: max of layer's max-slot-used and alg's max-slot-written
        layer-max-slot = ProcessedLayerResult.max-slot-used layer-result
        alg-max-slot = IRResultAWF.max-slot-written alg-result
        cata-max-slot = layer-max-slot ⊔ alg-max-slot

        cata-max-slot-geq-final : next-slot (IRResultAWF.final-alloc alg-result) ≤ cata-max-slot
        cata-max-slot-geq-final = ≤-trans (IRResultAWF.max-slot-geq-final alg-result) (n≤m⊔n layer-max-slot alg-max-slot)

        -- Plan 0.17.x: the cata's AllocBump composes the layer's bump (now a
        -- ProcessedLayerResult field) with the algebra's bump, via the
        -- apply-bump/bump-+ homomorphism. (Was an ∸-reconstruction; the bump
        -- field makes it clean and exact.)
        cata-bump : AllocBump
        cata-bump = bump-+ (ProcessedLayerResult.bump layer-result) (IRResultAWF.bump alg-result)

        cata-final-alloc-eq : IRResultAWF.final-alloc alg-result ≡ apply-bump cata-bump alloc
        cata-final-alloc-eq =
          trans (cong (apply-bump (IRResultAWF.bump alg-result))
                      (ProcessedLayerResult.final-alloc-eq layer-result))
                (apply-bump-compose (ProcessedLayerResult.bump layer-result)
                                    (IRResultAWF.bump alg-result) alloc)

        -- NOTE: With IRResultAWF field types changed to use max-slot-written,
        -- we can now prove TraceWritesBelow cata-max-slot final-trace where
        -- cata-max-slot = layer-max-slot ⊔ alg-max-slot.

        cata-result-place-stub : ResultPlace A mAlg
          (IRResultAWF.final-alloc alg-result)
          (record alloc { next-slot     = next-slot     (IRResultAWF.final-alloc alg-result)
                        ; next-heap-ref = next-heap-ref (IRResultAWF.final-alloc alg-result) })
          (eval (Cata wfG alg) x)
          (IRResultAWF.final-state alg-result)
        cata-result-place-stub = cata-result-place-postulate
          {G} {A} {wfG} {alg} {mAlg} {x} {s} {alloc}
          {IRResultAWF.final-alloc alg-result} {IRResultAWF.final-state alg-result}

        cata-result : IRResultAWF mAlg {μ-type G} {A} (Cata wfG alg) x s alloc
        cata-result =
          mk-IRResultAWF-via-bump
            (IRResultAWF.final-state alg-result)
            (IRResultAWF.final-alloc alg-result)
            final-trace
            cata-bump
            cata-final-alloc-eq
            SMP.!!                       -- trace-is-ir-to-trace
            trace-correct-proof
            alloc-correct-proof
            cata-result-place-stub
            (IRResultAWF.not-halted alg-result)
            mem-preserved-proof
            (let third : TraceWF (proj₁ (exec-abstract mov-to-input s-layer alloc-layer))
                                 (proj₂ (exec-abstract mov-to-input s-layer alloc-layer)) alg-trace
                 third = subst (λ st → TraceWF st alloc-layer alg-trace)
                           (sym s-after-mov-eq-bridged) (IRResultAWF.trace-twf alg-result)
                 second : TraceWF (proj₁ (exec-trace layer-trace s alloc))
                                  (proj₂ (exec-trace layer-trace s alloc)) (mov-to-input ∷ alg-trace)
                 second = subst (λ st → TraceWF st (proj₂ (exec-trace layer-trace s alloc))
                                          (mov-to-input ∷ alg-trace))
                            (sym (ProcessedLayerResult.trace-correct layer-result))
                            (subst (λ al → TraceWF s-layer al (mov-to-input ∷ alg-trace))
                              (sym (ProcessedLayerResult.alloc-correct layer-result))
                              (twf-∷ tt third))
             in twf-++ not-halted (ProcessedLayerResult.trace-twf layer-result) second)
            (exec-trace-preserves-halted-WF final-trace)
            (SMP.trace-no-frame-ops-append layer-trace (mov-to-input ∷ alg-trace)
              (ProcessedLayerResult.trace-no-frame-ops layer-result)
              (tt , IRResultAWF.trace-no-frame-ops alg-result))
            (record
              { max-slot-written = cata-max-slot
              ; stack-budget = ir-stack-requirement (Cata wfG alg)
              ; bump-fits-stack-budget = SMP.!!    -- Plan 0.17.1 TODO
              ; max-slot-geq-final =
                  subst (_≤ cata-max-slot) (cong next-slot cata-final-alloc-eq) cata-max-slot-geq-final
              ; max-slot-usage-bound = SMP.!!
              ; frontier-slot-stable = λ _ _ _ _ _ → inj₂ (inj₂ tt)
              ; trace-writes-above = SMP.trace-writes-above-append (next-slot alloc) layer-trace
                  (mov-to-input ∷ IRResultAWF.trace alg-result)
                  (ProcessedLayerResult.trace-writes-above layer-result)
                  (SMP.trace-writes-above-mono (next-slot alloc) (next-slot alloc-layer)
                    (IRResultAWF.trace alg-result) layer-slot-mono
                    (IRResultAWF.trace-writes-above alg-result))
              ; trace-slot-reads-above = SMP.trace-slot-reads-above-append (next-slot alloc) layer-trace
                  (mov-to-input ∷ IRResultAWF.trace alg-result)
                  (ProcessedLayerResult.trace-slot-reads-above layer-result)
                  (SMP.trace-slot-reads-above-mono (next-slot alloc) (next-slot alloc-layer)
                    (IRResultAWF.trace alg-result) layer-slot-mono
                    (IRResultAWF.trace-slot-reads-above alg-result))
              ; trace-writes-below = SMP.trace-writes-below-append cata-max-slot layer-trace
                  (mov-to-input ∷ IRResultAWF.trace alg-result)
                  (SMP.trace-writes-below-mono layer-max-slot cata-max-slot layer-trace
                     (m≤m⊔n layer-max-slot alg-max-slot)
                     (ProcessedLayerResult.trace-writes-below layer-result))
                  (SMP.trace-writes-below-mono alg-max-slot cata-max-slot (IRResultAWF.trace alg-result)
                     (m≤n⊔m layer-max-slot alg-max-slot)
                     (IRResultAWF.trace-writes-below alg-result))
              ; trace-slot-reads-below = SMP.trace-slot-reads-below-append cata-max-slot layer-trace
                  (mov-to-input ∷ IRResultAWF.trace alg-result)
                  (SMP.trace-slot-reads-below-mono layer-max-slot cata-max-slot layer-trace
                     (m≤m⊔n layer-max-slot alg-max-slot)
                     (ProcessedLayerResult.trace-slot-reads-below layer-result))
                  (SMP.trace-slot-reads-below-mono alg-max-slot cata-max-slot (IRResultAWF.trace alg-result)
                     (m≤n⊔m layer-max-slot alg-max-slot)
                     (IRResultAWF.trace-slot-reads-below alg-result))
              ; scratch-budget = ir-scratch-requirement (Cata wfG alg)
              ; scratch-bounded = SMP.!!
              })
            (record
              { heap-budget = 0
              ; max-heap-ref-written = next-heap-ref (IRResultAWF.final-alloc alg-result)
              ; bump-fits-heap-budget = SMP.!!     -- Plan 0.17.1 TODO
              ; max-heap-ref-geq-final =
                  subst (_≤ next-heap-ref (IRResultAWF.final-alloc alg-result))
                    (cong next-heap-ref cata-final-alloc-eq) ≤-refl
              ; max-heap-usage-bound = subst (next-heap-ref (IRResultAWF.final-alloc alg-result) ≤_)
                  (sym (+-identityʳ (next-heap-ref alloc)))
                  (≤-reflexive heap-pres-proof)
              })

      in
      mAlg , cata-result

  ------------------------------------------------------------------------
  -- IMPLEMENTATION PLAN: Eliminate rec-scheme-semantic postulate
  --
  -- The proof chains IRResultAWF proofs from:
  --   1. Recursive calls (structural IH on sub-μ-values)
  --   2. F-layer construction (existing inl/inr/pair handlers)
  --   3. Algebra dispatch (smaller IR)
  --
  -- TRACE STRUCTURE for Cata on μF:
  --   For each recursive position in layer = sem-Out wf x:
  --     recursive-trace ++ mov-to-input ∷ []
  --   Then:
  --     layer-construction-trace (inl/inr/pair)
  --     mov-to-input ∷ alg-trace
  --
  -- CHAINING (like compose):
  --   Each IRResultAWF has:
  --     - result-loc: where result is stored
  --     - final-state: state after trace
  --     - result-valid-wf: ValidAtWF for result
  --
  --   Chain by:
  --     1. Execute trace₁, get IRResultAWF₁
  --     2. mov-to-input bridges Output to Input1
  --     3. Execute trace₂ from IRResultAWF₁.final-state
  --     4. Combine proofs (validityWF-mem-preserved, etc.)
  --
  -- EXAMPLE: NatF = K Unit ⊕ Id
  --
  --   Zero (inj₁ tt):
  --     trace = inl-trace ++ mov-to-input ∷ alg-trace
  --     Proof: valid-inl-wf for input, alg's IRResultAWF for output
  --
  --   Suc m (inj₂ m):
  --     trace = cata-trace m ++ mov-to-input ∷ inr-trace ++
  --             mov-to-input ∷ alg-trace
  --     Proof: IH gives ValidAtWF for recursive result,
  --            valid-inr-wf for constructed sum,
  --            alg's IRResultAWF for output
  --
  -- TERMINATING justified: structural recursion on μ-values (well-founded)
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Recursive Dispatch: Architectural Analysis
  --
  -- CURRENT ISSUE:
  -- The current cata-dispatch-layer traverses the functor structure
  -- via pattern matching on wfF, but the return type expects the FULL
  -- Cata result. This causes a mismatch because:
  --
  --   1. K case: We have a constant, need to build full processed layer
  --   2. Id case: We have recursive result, need to wrap it in context
  --   3. Sum/Prod: We recurse but lose the inj₁/inj₂/pair structure
  --
  -- SEMANTIC EQUATION (what we need to compute):
  --   sem-cata wfG alg' (In layer) = alg' (sem-fmap G (sem-cata wfG alg') layer)
  --
  -- For G = K Unit ⊕ Id (naturals):
  --   layer = inj₁ tt  → processed = inj₁ tt              → result = alg' (inj₁ tt)
  --   layer = inj₂ m   → processed = inj₂ (cata alg' m)   → result = alg' (inj₂ ...)
  --
  -- SOLUTION: Two-Phase Architecture
  --
  -- Phase 1: process-layer
  --   Input1:  layer : ⟦ G ⟧F (⟦μ⟧ G)  (layer with μ-values at Id positions)
  --   Output: processed : ⟦ G ⟧F A'    (layer with fold results at Id positions)
  --           + trace, state, validity proofs
  --
  --   Implementation by functor induction:
  --   - K: processed = k-val (no change)
  --   - Id: processed = cata alg' μ-sub (recursive call)
  --   - Sum (inj₁ l): recurse on l, wrap result in inj₁
  --   - Sum (inj₂ r): recurse on r, wrap result in inj₂
  --   - Prod (l, r): recurse on both, combine as (processed-l, processed-r)
  --
  -- Phase 2: apply-algebra
  --   Input1:  processed : ⟦ G ⟧F A'
  --   Output: result : A' = alg' processed
  --
  -- RETURN TYPE for process-layer:
  --   record ProcessedLayerResult {G A'} (wfG : WellFormedF G)
  --     (layer : ⟦ G ⟧F (⟦μ⟧ G)) (s : LocState FS) (alloc : AllocState) : Set where
  --     field
  --       processed : ⟦ G ⟧F ⟦ A' ⟧
  --       trace : AbstractTrace
  --       final-state : LocState FS
  --       final-alloc : AllocState
  --       result-loc : ValueLocation FS  -- Where processed is stored
  --       processed-valid : ValidAtWF m final-alloc processed result-loc final-state
  --       semantic-eq : processed ≡ sem-fmap G (sem-cata wfG alg') layer
  --       ... other invariants ...
  --
  -- BENEFITS:
  --   1. Clean separation: layer processing vs algebra application
  --   2. Return type matches semantics: processed : ⟦ G ⟧F A'
  --   3. Sum/Prod cases naturally rebuild structure
  --   4. cata-dispatched just chains: process-layer → apply-algebra
  --
  -- STATUS: The two-phase approach is NOW IMPLEMENTED via:
  --   - process-layer: Phase 1 (layer processing by functor induction)
  --   - cata-dispatched-new: Phase 2 (destruct → process-layer → apply algebra)
  --
  -- These are used by RecCoreWF.run-cata-core.
  ------------------------------------------------------------------------
