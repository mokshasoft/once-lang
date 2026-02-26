------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.Validity
--
-- Concrete validity definitions for SlotMachine POC.
--
-- Key insight: In SlotMachine, memory stores ValueLocations directly,
-- so ValidAt can be defined as an inductive family indexed by Type.
--
-- IMPORTANT: Closures track their body IR!
-- Since we create all closures via curry, we know exactly what IR
-- each closure contains. This enables Apply to dispatch to bodies.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Dispatcher.Validity where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Induction.WellFounded using (Acc; acc)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.SlotMachine
open import Once.CCC.Target.X86v3.Dispatcher.Allocation
open import Once.CCC.Target.X86v3.Types public
open import Once.CCC.IR

------------------------------------------------------------------------
-- ValidAt: Inductive Validity Predicate with Frontier Tracking
--
-- ValidAt alloc {A} v loc s means: value v of type A is validly represented
-- at location loc in state s, and all component locations are before
-- the allocation frontier tracked by alloc.
--
-- Structure:
--   - Pairs: loc points to fst-loc, sucLoc loc points to snd-loc
--   - Closures: loc points to env-loc, sucLoc loc points to code-loc
--               PLUS: tracks the body IR and env value
--   - Unit: always valid (no memory requirements)
--
-- Key insight: By tracking the body IR in closures, Apply can extract
-- the IR and dispatch to it recursively.
------------------------------------------------------------------------

-- ValidityDef is now parameterized by program-bound for termination
-- All IRs in the program have ir-size < program-bound
-- This enables Apply to call run-ir on body using rs (body<bound)
-- Also parameterized by PrimSem for primitive evaluation
module ValidityDef {FS : FrameSemantics} (program-bound : ℕ) (primSem : PrimSem) where
  open MemOps {FS}
  open FrontierInvariant {FS}

  -- Forward declaration for mutual recursion between ValidAt and valid-closure
  -- valid-closure needs to reference ValidAt for env validity

  data ValidAt (alloc : AllocState {FS}) : {A : Type} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set where

    -- Unit is always valid at any location
    valid-unit : ∀ {loc s} →
      ValidAt alloc {Unit} tt loc s

    -- Pair validity: memory contains pointers to valid components
    -- Components must be before frontier (tracked recursively)
    -- IMPORTANT: sucLoc pair-loc must also be before frontier (for validity-write proofs)
    valid-pair : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
      {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s pair-loc ≡ just fst-loc →
      readLoc s (sucLoc pair-loc) ≡ just snd-loc →
      BeforeFrontier alloc fst-loc →
      BeforeFrontier alloc snd-loc →
      BeforeFrontier alloc (sucLoc pair-loc) →  -- NEW: sucLoc is also before frontier
      ValidAt alloc a fst-loc s →
      ValidAt alloc b snd-loc s →
      ValidAt alloc {A * B} (a , b) pair-loc s

    -- Sum type validity: tagged union
    -- Memory layout: sum-loc's first slot stores tag, sucLoc sum-loc stores payload-loc
    -- Tag is implicit in which constructor (valid-inl vs valid-inr) is used
    -- For execution, tag is encoded in memory (0 = left, 1 = right)
    valid-inl : ∀ {A B} {a : ⟦ A ⟧}
      {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s (sucLoc sum-loc) ≡ just payload-loc →
      BeforeFrontier alloc payload-loc →
      BeforeFrontier alloc (sucLoc sum-loc) →
      ValidAt alloc a payload-loc s →
      ValidAt alloc {A + B} (inl a) sum-loc s

    valid-inr : ∀ {A B} {b : ⟦ B ⟧}
      {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s (sucLoc sum-loc) ≡ just payload-loc →
      BeforeFrontier alloc payload-loc →
      BeforeFrontier alloc (sucLoc sum-loc) →
      ValidAt alloc b payload-loc s →
      ValidAt alloc {A + B} (inr b) sum-loc s

    -- Recursive type validity: pointer to heap-allocated unfolded value
    -- Memory layout: fix-loc stores pointer to unfolded-loc on heap
    valid-fold : ∀ {F} {v : ⟦ F ⟧}
      {fix-loc unfolded-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s fix-loc ≡ just unfolded-loc →
      BeforeFrontier alloc unfolded-loc →
      ValidAt alloc v unfolded-loc s →
      ValidAt alloc {Fix F} (fold v) fix-loc s

    -- Closure validity: tracks the body IR that created this closure!
    --
    -- A closure created by (curry body) with captured env has:
    --   - semantic value: λ arg → eval primSem body (pair env arg)
    --   - memory layout: closure-loc → env-loc, sucLoc closure-loc → code marker
    --   - body IR: stored for Apply to dispatch to
    --   - body<bound: proof that ir-size body < program-bound (enables termination in Apply)
    --
    -- This is the key insight: we create all closures, so we know their bodies.
    -- Curry captures (ir-size body < program-bound) when building the closure.
    -- Apply uses this with (rs body<bound) to recurse.
    -- IMPORTANT: sucLoc closure-loc must also be before frontier (for validity-write proofs)
    valid-closure : ∀ {EnvType q A B}
      {body : IR (EnvType * A) B}
      {env : ⟦ EnvType ⟧}
      (body<bound : ir-size body < program-bound) →  -- Size bound (not Acc!)
      {closure-loc env-loc code-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s closure-loc ≡ just env-loc →
      readLoc s (sucLoc closure-loc) ≡ just code-loc →
      BeforeFrontier alloc env-loc →
      BeforeFrontier alloc code-loc →
      BeforeFrontier alloc (sucLoc closure-loc) →
      ValidAt alloc env env-loc s →
      -- The semantic value matches: closure = λ arg → eval primSem body (pair env arg)
      ValidAt alloc {A ⇒[ q ] B} (λ arg → eval primSem body (pair env arg)) closure-loc s

  ------------------------------------------------------------------------
  -- PairValid record (extracted structure from valid-pair)
  ------------------------------------------------------------------------

  record PairValid (alloc : AllocState {FS}) {A B : Type}
                   (p : ⟦ A * B ⟧)
                   (pair-loc : ValueLocation FS)
                   (s : LocState FS) : Set where
    field
      fst-loc : ValueLocation FS
      snd-loc : ValueLocation FS
      fst-ptr : readLoc s pair-loc ≡ just fst-loc
      snd-ptr : readLoc s (sucLoc pair-loc) ≡ just snd-loc
      fst-before : BeforeFrontier alloc fst-loc
      snd-before : BeforeFrontier alloc snd-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc pair-loc)  -- NEW
      fst-valid : ValidAt alloc (fst p) fst-loc s
      snd-valid : ValidAt alloc (snd p) snd-loc s

  ------------------------------------------------------------------------
  -- ClosureValid record (extracted structure from valid-closure)
  -- NOW INCLUDES THE BODY IR AND SIZE BOUND!
  ------------------------------------------------------------------------

  record ClosureValid (alloc : AllocState {FS}) {q : Quantity} {A B : Type}
                      (f : ⟦ A ⇒[ q ] B ⟧)
                      (closure-loc : ValueLocation FS)
                      (s : LocState FS) : Set where
    field
      EnvType : Type
      body : IR (EnvType * A) B
      env : ⟦ EnvType ⟧
      body<bound : ir-size body < program-bound       -- Size bound (not Acc!)
      env-loc : ValueLocation FS
      code-loc : ValueLocation FS
      env-ptr : readLoc s closure-loc ≡ just env-loc
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just code-loc
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      env-valid : ValidAt alloc env env-loc s
      -- Proof that f is the closure we expect
      f-is-closure : f ≡ (λ arg → eval primSem body (pair env arg))

  ------------------------------------------------------------------------
  -- SumValid records (extracted structure from valid-inl/valid-inr)
  ------------------------------------------------------------------------

  record InlValid (alloc : AllocState {FS}) {A B : Type}
                  (v : ⟦ A + B ⟧)
                  (sum-loc : ValueLocation FS)
                  (s : LocState FS) : Set where
    field
      a : ⟦ A ⟧
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just payload-loc
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAt alloc a payload-loc s
      v-is-inl : v ≡ inl a

  record InrValid (alloc : AllocState {FS}) {A B : Type}
                  (v : ⟦ A + B ⟧)
                  (sum-loc : ValueLocation FS)
                  (s : LocState FS) : Set where
    field
      b : ⟦ B ⟧
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just payload-loc
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAt alloc b payload-loc s
      v-is-inr : v ≡ inr b

  ------------------------------------------------------------------------
  -- FoldValid record (extracted structure from valid-fold)
  ------------------------------------------------------------------------

  record FoldValid (alloc : AllocState {FS}) {F : Type}
                   (v : ⟦ Fix F ⟧)
                   (fix-loc : ValueLocation FS)
                   (s : LocState FS) : Set where
    field
      unfolded : ⟦ F ⟧
      unfolded-loc : ValueLocation FS
      unfolded-ptr : readLoc s fix-loc ≡ just unfolded-loc
      unfolded-before : BeforeFrontier alloc unfolded-loc
      unfolded-valid : ValidAt alloc unfolded unfolded-loc s
      v-is-fold : v ≡ fold unfolded

  ------------------------------------------------------------------------
  -- Decomposition lemmas
  ------------------------------------------------------------------------

  decomposePair : ∀ {alloc A B} {p : ⟦ A * B ⟧} {loc s} →
    ValidAt alloc p loc s → PairValid alloc p loc s
  decomposePair (valid-pair {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) = record
    { fst-loc = fl
    ; snd-loc = sl
    ; fst-ptr = fp
    ; snd-ptr = sp
    ; fst-before = fb
    ; snd-before = sb
    ; sucLoc-before = slb
    ; fst-valid = fv
    ; snd-valid = sv
    }

  decomposeClosure : ∀ {alloc q A B} {f : ⟦ A ⇒[ q ] B ⟧} {loc s} →
    ValidAt alloc {A ⇒[ q ] B} f loc s → ClosureValid alloc {q} f loc s
  decomposeClosure (valid-closure {EnvType} {_} {_} {_} {body} {env}
                     bb {env-loc = el} {code-loc = cl} ep cp eb cb slb ev) = record
    { EnvType = EnvType
    ; body = body
    ; env = env
    ; body<bound = bb
    ; env-loc = el
    ; code-loc = cl
    ; env-ptr = ep
    ; code-ptr = cp
    ; env-before = eb
    ; code-before = cb
    ; sucLoc-before = slb
    ; env-valid = ev
    ; f-is-closure = refl
    }

  decomposeInl : ∀ {alloc A B} {a : ⟦ A ⟧} {loc s} →
    ValidAt alloc {A + B} (inl {A} {B} a) loc s → InlValid alloc {A} {B} (inl a) loc s
  decomposeInl {A = A} {B = B} {a = a} (valid-inl {payload-loc = pl} pp pb slb pv) = record
    { a = a
    ; payload-loc = pl
    ; payload-ptr = pp
    ; payload-before = pb
    ; sucLoc-before = slb
    ; payload-valid = pv
    ; v-is-inl = refl
    }

  decomposeInr : ∀ {alloc A B} {b : ⟦ B ⟧} {loc s} →
    ValidAt alloc {A + B} (inr {A} {B} b) loc s → InrValid alloc {A} {B} (inr b) loc s
  decomposeInr {A = A} {B = B} {b = b} (valid-inr {payload-loc = pl} pp pb slb pv) = record
    { b = b
    ; payload-loc = pl
    ; payload-ptr = pp
    ; payload-before = pb
    ; sucLoc-before = slb
    ; payload-valid = pv
    ; v-is-inr = refl
    }

  decomposeFold : ∀ {alloc F} {v : ⟦ F ⟧} {loc s} →
    ValidAt alloc {Fix F} (fold v) loc s → FoldValid alloc (fold v) loc s
  decomposeFold {v = v} (valid-fold {unfolded-loc = ul} up ub uv) = record
    { unfolded = v
    ; unfolded-loc = ul
    ; unfolded-ptr = up
    ; unfolded-before = ub
    ; unfolded-valid = uv
    ; v-is-fold = refl
    }

  ------------------------------------------------------------------------
  -- Composition lemmas
  ------------------------------------------------------------------------

  composePair : ∀ {alloc A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧)
    (pair-loc fst-loc snd-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s pair-loc ≡ just fst-loc →
    readLoc s (sucLoc pair-loc) ≡ just snd-loc →
    BeforeFrontier alloc fst-loc →
    BeforeFrontier alloc snd-loc →
    BeforeFrontier alloc (sucLoc pair-loc) →  -- NEW
    ValidAt alloc a fst-loc s →
    ValidAt alloc b snd-loc s →
    ValidAt alloc (pair a b) pair-loc s
  composePair a b pair-loc fst-loc snd-loc s fp sp fb sb slb fv sv =
    valid-pair fp sp fb sb slb fv sv

  -- Compose a closure validity from its components
  composeClosure : ∀ {alloc EnvType q A B}
    (body : IR (EnvType * A) B) (env : ⟦ EnvType ⟧)
    (body<bound : ir-size body < program-bound) →      -- Size bound (not Acc!)
    (closure-loc env-loc code-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s closure-loc ≡ just env-loc →
    readLoc s (sucLoc closure-loc) ≡ just code-loc →
    BeforeFrontier alloc env-loc →
    BeforeFrontier alloc code-loc →
    BeforeFrontier alloc (sucLoc closure-loc) →
    ValidAt alloc env env-loc s →
    ValidAt alloc {A ⇒[ q ] B} (λ arg → eval primSem body (pair env arg)) closure-loc s
  composeClosure {_} {_} {_} {_} {_} body env bb closure-loc env-loc code-loc s ep cp eb cb slb ev =
    valid-closure {body = body} {env = env} bb ep cp eb cb slb ev

  -- Compose sum validity (inl)
  composeInl : ∀ {alloc A B} (a : ⟦ A ⟧)
    (sum-loc payload-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s (sucLoc sum-loc) ≡ just payload-loc →
    BeforeFrontier alloc payload-loc →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ValidAt alloc a payload-loc s →
    ValidAt alloc {A + B} (inl a) sum-loc s
  composeInl a sum-loc payload-loc s pp pb slb pv = valid-inl pp pb slb pv

  -- Compose sum validity (inr)
  composeInr : ∀ {alloc A B} (b : ⟦ B ⟧)
    (sum-loc payload-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s (sucLoc sum-loc) ≡ just payload-loc →
    BeforeFrontier alloc payload-loc →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ValidAt alloc b payload-loc s →
    ValidAt alloc {A + B} (inr b) sum-loc s
  composeInr b sum-loc payload-loc s pp pb slb pv = valid-inr pp pb slb pv

  -- Compose fold validity
  composeFold : ∀ {alloc F} (v : ⟦ F ⟧)
    (fix-loc unfolded-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s fix-loc ≡ just unfolded-loc →
    BeforeFrontier alloc unfolded-loc →
    ValidAt alloc v unfolded-loc s →
    ValidAt alloc {Fix F} (fold v) fix-loc s
  composeFold v fix-loc unfolded-loc s up ub uv = valid-fold up ub uv

  ------------------------------------------------------------------------
  -- Validity depends only on memory
  ------------------------------------------------------------------------

  -- Helper for readLoc equality
  readLoc-stack-heap-eq : ∀ (s₁ s₂ : LocState FS) loc →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ loc ≡ readLoc s₂ loc
  readLoc-stack-heap-eq s₁ s₂ (OnStack f k) seq heq = cong (λ m → m f k) seq
  readLoc-stack-heap-eq s₁ s₂ (OnHeap hl) seq heq
    with heapMem s₁ hl | heapMem s₂ hl | cong (λ m → m hl) heq
  ... | just hl₁ | just hl₂ | eq = cong (λ x → just (OnHeap x)) (just-injective eq)
    where
      just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
      just-injective refl = refl
  ... | nothing | nothing | _ = refl
  ... | just _ | nothing | ()
  ... | nothing | just _ | ()

  validity-mem-only : ∀ {alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    ValidAt alloc v loc s₁ → ValidAt alloc v loc s₂

  validity-mem-only {alloc} {Unit} tt loc s₁ s₂ stack-eq heap-eq valid-unit = valid-unit

  validity-mem-only {alloc} {A * B} (a , b) loc s₁ s₂ stack-eq heap-eq
    (valid-pair {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair fp' sp' fb sb slb fv' sv'
    where
      fp' : readLoc s₂ loc ≡ just fl
      fp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ loc stack-eq heap-eq)) fp

      sp' : readLoc s₂ (sucLoc loc) ≡ just sl
      sp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) sp

      fv' : ValidAt alloc a fl s₂
      fv' = validity-mem-only a fl s₁ s₂ stack-eq heap-eq fv

      sv' : ValidAt alloc b sl s₂
      sv' = validity-mem-only b sl s₁ s₂ stack-eq heap-eq sv

  validity-mem-only {alloc} {A ⇒[ _ ] B} .(λ arg → eval primSem body (pair env arg)) loc s₁ s₂ stack-eq heap-eq
    (valid-closure {EnvType} {_} {_} {_} {body} {env} ba {env-loc = el} {code-loc = cl} ep cp eb cb slb ev) =
    valid-closure {body = body} {env = env} ba ep' cp' eb cb slb ev'
    where
      ep' : readLoc s₂ loc ≡ just el
      ep' = trans (sym (readLoc-stack-heap-eq s₁ s₂ loc stack-eq heap-eq)) ep

      cp' : readLoc s₂ (sucLoc loc) ≡ just cl
      cp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) cp

      ev' : ValidAt alloc env el s₂
      ev' = validity-mem-only env el s₁ s₂ stack-eq heap-eq ev

  validity-mem-only {alloc} {A + B} .(inl a) loc s₁ s₂ stack-eq heap-eq
    (valid-inl {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just pl
      pp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) pp

      pv' : ValidAt alloc a pl s₂
      pv' = validity-mem-only a pl s₁ s₂ stack-eq heap-eq pv

  validity-mem-only {alloc} {A + B} .(inr b) loc s₁ s₂ stack-eq heap-eq
    (valid-inr {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just pl
      pp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) pp

      pv' : ValidAt alloc b pl s₂
      pv' = validity-mem-only b pl s₁ s₂ stack-eq heap-eq pv

  validity-mem-only {alloc} {Fix F} .(fold v) loc s₁ s₂ stack-eq heap-eq
    (valid-fold {v = v} {unfolded-loc = ul} up ub uv) =
    valid-fold up' ub uv'
    where
      up' : readLoc s₂ loc ≡ just ul
      up' = trans (sym (readLoc-stack-heap-eq s₁ s₂ loc stack-eq heap-eq)) up

      uv' : ValidAt alloc v ul s₂
      uv' = validity-mem-only v ul s₁ s₂ stack-eq heap-eq uv

------------------------------------------------------------------------
-- Summary
--
--   Type, ⟦_⟧, fst, snd, pair  - from Types module
--
--   ValidAt       - inductive validity predicate
--   valid-closure - tracks body IR and env
--
--   PairValid     - extracted pair structure
--   ClosureValid  - extracted closure structure with body IR
--
--   decomposePair, decomposeClosure  - extraction
--   composePair, composeClosure      - composition
--   validity-mem-only                - memory-only dependence
--
-- KEY INSIGHT: Since we create all closures via curry, we know their
-- body IRs. decomposeClosure extracts this, enabling Apply to dispatch
-- to the body.
------------------------------------------------------------------------
