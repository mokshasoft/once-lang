-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.Validity
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

module Once.CCC.Machine.Validity where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Induction.WellFounded using (Acc; acc)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore hiding (AllocMode; Stack; Heap)
open import Once.CCC.Machine.Allocation
open import Once.Semantics.Machine public
  using (sem-fst; sem-snd; sem-inl; sem-inr; sem-pair)
-- The IRTy value-domain rename is LOCAL to Validity (not re-exported), so it
-- does not collide with downstream modules' own surface `⟦_⟧` imports.
open import Once.Semantics.Machine
  using () renaming (⟦_⟧ᴵ to ⟦_⟧)
pair = sem-pair
open import Once.IR
import Once.CCC.Eval as Ev
open import Once.IR.Size

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
-- Also parameterized by SigOpSem for primitive evaluation
module ValidityDef {FS : FrameSemantics} (program-bound : ℕ) where
  -- Plan 0.73 (D113): `eval` is target-relative at `Float` — a float literal
  -- has no format-free machine value. Inside a module already fixed to this
  -- target's `FrameSemantics`, THE evaluator is the one at its float format,
  -- so it is named once here and used unqualified below.
  eval : ∀ {A B} → IR A B → ⟦ A ⟧ → ⟦ B ⟧
  eval = Ev.eval (FrameSemantics.float-format FS)

  open MemOps {FS}
  open FrontierInvariant {FS}

  -- Forward declaration for mutual recursion between ValidAt and valid-closure
  -- valid-closure needs to reference ValidAt for env validity

  data ValidAt (alloc : AllocState {FS}) : {A : IRTy} → ⟦ A ⟧ → ValueLocation FS → LocState FS → Set where

    -- Unit is always valid at any location
    valid-unit : ∀ {loc s} →
      ValidAt alloc {Unit} tt loc s

    -- Pair validity: memory contains pointers to valid components.
    -- Plan 0.13.2: pointer reads now produce `just (SV-Ptr loc)`.
    valid-pair : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧}
      {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s pair-loc ≡ just (SV-Ptr fst-loc) →
      readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc) →
      BeforeFrontier alloc fst-loc →
      BeforeFrontier alloc snd-loc →
      BeforeFrontier alloc (sucLoc pair-loc) →
      ValidAt alloc a fst-loc s →
      ValidAt alloc b snd-loc s →
      ValidAt alloc {A * B} (a , b) pair-loc s

    -- Sum type validity: payload at sucLoc sum-loc.
    -- Plan 0.13.2: pointer reads return `just (SV-Ptr loc)`.
    valid-inl : ∀ {A B} {a : ⟦ A ⟧}
      {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
      BeforeFrontier alloc payload-loc →
      BeforeFrontier alloc (sucLoc sum-loc) →
      ValidAt alloc a payload-loc s →
      ValidAt alloc {A + B} (sem-inl a) sum-loc s

    valid-inr : ∀ {A B} {b : ⟦ B ⟧}
      {sum-loc payload-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
      BeforeFrontier alloc payload-loc →
      BeforeFrontier alloc (sucLoc sum-loc) →
      ValidAt alloc b payload-loc s →
      ValidAt alloc {A + B} (sem-inr b) sum-loc s

    -- OCP-0003: valid-fold removed. Use valid-μ/valid-ν (postulated) instead.
    -- The validity for μ-type and ν-type values is postulated because their
    -- semantics (sem-In, sem-cata, sem-CoOut, sem-ana) are postulated.

    -- Closure validity: tracks the body IR that created this closure!
    --
    -- A closure created by (curry body) with captured env has:
    --   - semantic value: λ arg → eval body (pair env arg)
    --   - memory layout: closure-loc → env-loc, sucLoc closure-loc → code marker
    --   - body IR: stored for Apply to dispatch to
    --   - body<bound: proof that ir-size body < program-bound (enables termination in Apply)
    --
    -- This is the key insight: we create all closures, so we know their bodies.
    -- Curry captures (ir-size body < program-bound) when building the closure.
    -- Apply uses this with (rs body<bound) to recurse.
    -- IMPORTANT: sucLoc closure-loc must also be before frontier (for validity-write proofs)
    -- Plan 0.13.2: env and code pointers wrapped as SV-Ptr in memory.
    -- (The semantic question of whether the code slot should hold
    -- SV-Code rather than a SV-Ptr is deferred — Plan 0.13.2 Phase E.)
    valid-closure : ∀ {EnvType A B}
      {body : IR (EnvType * A) B}
      {env : ⟦ EnvType ⟧}
      (body<bound : ir-size body < program-bound) →
      {closure-loc env-loc code-loc : ValueLocation FS} {s : LocState FS} →
      readLoc s closure-loc ≡ just (SV-Ptr env-loc) →
      readLoc s (sucLoc closure-loc) ≡ just (SV-Ptr code-loc) →
      BeforeFrontier alloc env-loc →
      BeforeFrontier alloc code-loc →
      BeforeFrontier alloc (sucLoc closure-loc) →
      ValidAt alloc env env-loc s →
      ValidAt alloc {A ⇛ B} (λ arg → eval body (pair env arg)) closure-loc s

  ------------------------------------------------------------------------
  -- PairValid record (extracted structure from valid-pair)
  ------------------------------------------------------------------------

  record PairValid (alloc : AllocState {FS}) {A B : IRTy}
                   (p : ⟦ A * B ⟧)
                   (pair-loc : ValueLocation FS)
                   (s : LocState FS) : Set where
    field
      fst-loc : ValueLocation FS
      snd-loc : ValueLocation FS
      fst-ptr : readLoc s pair-loc ≡ just (SV-Ptr fst-loc)
      snd-ptr : readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc)
      fst-before : BeforeFrontier alloc fst-loc
      snd-before : BeforeFrontier alloc snd-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc pair-loc)
      fst-valid : ValidAt alloc (sem-fst p) fst-loc s
      snd-valid : ValidAt alloc (sem-snd p) snd-loc s

  ------------------------------------------------------------------------
  -- ClosureValid record (extracted structure from valid-closure)
  -- NOW INCLUDES THE BODY IR AND SIZE BOUND!
  ------------------------------------------------------------------------

  record ClosureValid (alloc : AllocState {FS}) {A B : IRTy}
                      (f : ⟦ A ⇛ B ⟧)
                      (closure-loc : ValueLocation FS)
                      (s : LocState FS) : Set where
    field
      EnvType : IRTy
      body : IR (EnvType * A) B
      env : ⟦ EnvType ⟧
      body<bound : ir-size body < program-bound
      env-loc : ValueLocation FS
      code-loc : ValueLocation FS
      env-ptr : readLoc s closure-loc ≡ just (SV-Ptr env-loc)
      code-ptr : readLoc s (sucLoc closure-loc) ≡ just (SV-Ptr code-loc)
      env-before : BeforeFrontier alloc env-loc
      code-before : BeforeFrontier alloc code-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc closure-loc)
      env-valid : ValidAt alloc env env-loc s
      f-is-closure : f ≡ (λ arg → eval body (pair env arg))

  ------------------------------------------------------------------------
  -- SumValid records (extracted structure from valid-inl/valid-inr)
  ------------------------------------------------------------------------

  record InlValid (alloc : AllocState {FS}) {A B : IRTy}
                  (v : ⟦ A + B ⟧)
                  (sum-loc : ValueLocation FS)
                  (s : LocState FS) : Set where
    field
      a : ⟦ A ⟧
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc)
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAt alloc a payload-loc s
      v-is-inl : v ≡ sem-inl a

  record InrValid (alloc : AllocState {FS}) {A B : IRTy}
                  (v : ⟦ A + B ⟧)
                  (sum-loc : ValueLocation FS)
                  (s : LocState FS) : Set where
    field
      b : ⟦ B ⟧
      payload-loc : ValueLocation FS
      payload-ptr : readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc)
      payload-before : BeforeFrontier alloc payload-loc
      sucLoc-before : BeforeFrontier alloc (sucLoc sum-loc)
      payload-valid : ValidAt alloc b payload-loc s
      v-is-inr : v ≡ sem-inr b

  -- OCP-0003: FoldValid record removed. Use μ-type/ν-type validity instead.

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

  decomposeClosure : ∀ {alloc A B} {f : ⟦ A ⇛ B ⟧} {loc s} →
    ValidAt alloc {A ⇛ B} f loc s → ClosureValid alloc f loc s
  decomposeClosure (valid-closure {EnvType} {_} {_} {body} {env}
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
    ValidAt alloc {A + B} (sem-inl a) loc s → InlValid alloc {A} {B} (sem-inl a) loc s
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
    ValidAt alloc {A + B} (sem-inr b) loc s → InrValid alloc {A} {B} (sem-inr b) loc s
  decomposeInr {A = A} {B = B} {b = b} (valid-inr {payload-loc = pl} pp pb slb pv) = record
    { b = b
    ; payload-loc = pl
    ; payload-ptr = pp
    ; payload-before = pb
    ; sucLoc-before = slb
    ; payload-valid = pv
    ; v-is-inr = refl
    }

  -- OCP-0003: decomposeFold removed. Use μ-type/ν-type validity instead.

  ------------------------------------------------------------------------
  -- Composition lemmas
  ------------------------------------------------------------------------

  composePair : ∀ {alloc A B} (a : ⟦ A ⟧) (b : ⟦ B ⟧)
    (pair-loc fst-loc snd-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s pair-loc ≡ just (SV-Ptr fst-loc) →
    readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc) →
    BeforeFrontier alloc fst-loc →
    BeforeFrontier alloc snd-loc →
    BeforeFrontier alloc (sucLoc pair-loc) →
    ValidAt alloc a fst-loc s →
    ValidAt alloc b snd-loc s →
    ValidAt alloc (pair a b) pair-loc s
  composePair a b pair-loc fst-loc snd-loc s fp sp fb sb slb fv sv =
    valid-pair fp sp fb sb slb fv sv

  composeClosure : ∀ {alloc EnvType A B}
    (body : IR (EnvType * A) B) (env : ⟦ EnvType ⟧)
    (body<bound : ir-size body < program-bound) →
    (closure-loc env-loc code-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s closure-loc ≡ just (SV-Ptr env-loc) →
    readLoc s (sucLoc closure-loc) ≡ just (SV-Ptr code-loc) →
    BeforeFrontier alloc env-loc →
    BeforeFrontier alloc code-loc →
    BeforeFrontier alloc (sucLoc closure-loc) →
    ValidAt alloc env env-loc s →
    ValidAt alloc {A ⇛ B} (λ arg → eval body (pair env arg)) closure-loc s
  composeClosure {_} {_} {_} {_} body env bb closure-loc env-loc code-loc s ep cp eb cb slb ev =
    valid-closure {body = body} {env = env} bb ep cp eb cb slb ev

  composeInl : ∀ {alloc A B} (a : ⟦ A ⟧)
    (sum-loc payload-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
    BeforeFrontier alloc payload-loc →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ValidAt alloc a payload-loc s →
    ValidAt alloc {A + B} (sem-inl a) sum-loc s
  composeInl a sum-loc payload-loc s pp pb slb pv = valid-inl pp pb slb pv

  composeInr : ∀ {alloc A B} (b : ⟦ B ⟧)
    (sum-loc payload-loc : ValueLocation FS) (s : LocState FS) →
    readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
    BeforeFrontier alloc payload-loc →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ValidAt alloc b payload-loc s →
    ValidAt alloc {A + B} (sem-inr b) sum-loc s
  composeInr b sum-loc payload-loc s pp pb slb pv = valid-inr pp pb slb pv

  -- Compose fold validity
  -- OCP-0003: composeFold removed. Use μ-type/ν-type validity instead.

  ------------------------------------------------------------------------
  -- Validity depends only on memory
  ------------------------------------------------------------------------

  -- Helper for readLoc equality
  readLoc-stack-heap-eq : ∀ (s₁ s₂ : LocState FS) loc →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ loc ≡ readLoc s₂ loc
  readLoc-stack-heap-eq s₁ s₂ (AtStack f k) seq heq = cong (λ m → m f k) seq
  readLoc-stack-heap-eq s₁ s₂ (AtDynamic hl) seq heq = cong (λ m → m hl) heq

  validity-mem-only : ∀ {alloc A} (v : ⟦ A ⟧) loc (s₁ s₂ : LocState FS) →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    ValidAt alloc v loc s₁ → ValidAt alloc v loc s₂

  validity-mem-only {alloc} {Unit} tt loc s₁ s₂ stack-eq heap-eq valid-unit = valid-unit

  validity-mem-only {alloc} {A * B} (a , b) loc s₁ s₂ stack-eq heap-eq
    (valid-pair {fst-loc = fl} {snd-loc = sl} fp sp fb sb slb fv sv) =
    valid-pair fp' sp' fb sb slb fv' sv'
    where
      fp' : readLoc s₂ loc ≡ just (SV-Ptr fl)
      fp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ loc stack-eq heap-eq)) fp

      sp' : readLoc s₂ (sucLoc loc) ≡ just (SV-Ptr sl)
      sp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) sp

      fv' : ValidAt alloc a fl s₂
      fv' = validity-mem-only a fl s₁ s₂ stack-eq heap-eq fv

      sv' : ValidAt alloc b sl s₂
      sv' = validity-mem-only b sl s₁ s₂ stack-eq heap-eq sv

  validity-mem-only {alloc} {A ⇛ B} .(λ arg → eval body (pair env arg)) loc s₁ s₂ stack-eq heap-eq
    (valid-closure {EnvType} {_} {_} {body} {env} ba {env-loc = el} {code-loc = cl} ep cp eb cb slb ev) =
    valid-closure {body = body} {env = env} ba ep' cp' eb cb slb ev'
    where
      ep' : readLoc s₂ loc ≡ just (SV-Ptr el)
      ep' = trans (sym (readLoc-stack-heap-eq s₁ s₂ loc stack-eq heap-eq)) ep

      cp' : readLoc s₂ (sucLoc loc) ≡ just (SV-Ptr cl)
      cp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) cp

      ev' : ValidAt alloc env el s₂
      ev' = validity-mem-only env el s₁ s₂ stack-eq heap-eq ev

  validity-mem-only {alloc} {A + B} .(sem-inl a) loc s₁ s₂ stack-eq heap-eq
    (valid-inl {a = a} {payload-loc = pl} pp pb slb pv) =
    valid-inl pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just (SV-Ptr pl)
      pp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) pp

      pv' : ValidAt alloc a pl s₂
      pv' = validity-mem-only a pl s₁ s₂ stack-eq heap-eq pv

  validity-mem-only {alloc} {A + B} .(sem-inr b) loc s₁ s₂ stack-eq heap-eq
    (valid-inr {b = b} {payload-loc = pl} pp pb slb pv) =
    valid-inr pp' pb slb pv'
    where
      pp' : readLoc s₂ (sucLoc loc) ≡ just (SV-Ptr pl)
      pp' = trans (sym (readLoc-stack-heap-eq s₁ s₂ (sucLoc loc) stack-eq heap-eq)) pp

      pv' : ValidAt alloc b pl s₂
      pv' = validity-mem-only b pl s₁ s₂ stack-eq heap-eq pv

  -- OCP-0003: validity-mem-only case for Fix removed.
  -- Use μ-type/ν-type validity instead.

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