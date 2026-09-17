# Emptiness probes — `block-runs`

**These are deliberately NOT in `formal/Once/`.** `ApexInconsistent.boom` has
type `⊥`. Compiling it as part of the tree would make the build inconsistent
and every `Everything.agda` island backstop would (correctly) reject it. They
live here as text, and are copied into `formal/Once/Probe/` only to be run.

MERGE.md requires an emptiness probe before a residual is accepted. D213
established that OLD residuals owe one too. This file is what makes that
re-runnable: without it the probes are untracked working files that vanish with
the checkout.

## How to run

```sh
cd formal
mkdir -p Once/Probe
# paste the two modules below into Once/Probe/{BlockRunsRefute,ApexInconsistent}.agda
rm -f _build/2.8.0/agda/Once/Probe/*.agdai        # agda keys on content hash; touch is NOT enough
timeout 540 ./scripts/agda-safe.sh MODULE=Once/Probe/ApexInconsistent.agda
```

A pass means the probe **refuted** the residual. Confirm the run actually did
work — `grep -c Checking` must be ≥ 1, and both probe modules must appear:

```
Checking Once.Probe.ApexInconsistent
Checking Once.Probe.BlockRunsRefute
EXIT=0
```

Last run: 2026-09-16, post-D214 telescope. `boom : ⊥` compiles; `block-runs`
is still false.

## The idea

`CalleeRuns` is handed a *memory* fact — `valid-closure-reg-wf` carries a free
implicit `body-label` tied to nothing but `readLoc s (sucLoc cl) ≡ just
(SV-Code body-label)` — and is asked to conclude a *program* fact,
`find-thunk (ir-to-trace ir) ℓ ≡ just j`. So fabricate a heap in which every
cell reads `just (SV-Code lbl)`, build the witness at a label no program ever
minted, and instantiate at `ir = id {Unit}`, which emits no blocks at all. The
`()` is the whole argument.

Label uniqueness would not save it: uniqueness says no two blocks collide, not
that this label belongs to any block.

## `Once/Probe/BlockRunsRefute.agda`

```agda
-- PROBE (not part of the build): is `block-runs` CONSISTENT as stated?
open import Once.CanonicalName using (CanonicalName)

module Once.Probe.BlockRunsRefute (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Interface o
open import Once.CCC.Machine.SMCore using (mkAllocState; mkLocState; mkRegs)
open import Data.Nat using (s≤s; z≤n)
import Once.CCC.FrameSemantics as FSem
import Once.IRTy

module Refute {FS : FrameSemantics}
              (fr : FSem.FrameSemantics.Frame FS) where
  open Core {FS}
  open FrontierInvariant {FS} using (heap-before)
  open ClosureWellFormedDef {FS} using (valid-unit-wf)

  lbl : LabelId
  lbl = ℓ o 0

  -- an allocator whose heap frontier is 1 (so ref 0 is BeforeFrontier)
  bad-alloc : AllocState {FS}
  bad-alloc = mkAllocState fr [] 0 0 1 (λ _ → 0)

  cloc : ValueLocation FS
  cloc = AtDynamic (heap-loc (mkHeapRef 0) 0)

  eloc : ValueLocation FS
  eloc = AtDynamic (heap-loc (mkHeapRef 0) 9)

  bad-heap : HeapLocation → Maybe (StoredValue FS)
  bad-heap (heap-loc r zero)    = just (SV-Ptr eloc)
  bad-heap (heap-loc r (suc n)) = just (SV-Code lbl)

  bad-st : LocState FS
  bad-st = mkLocState (mkRegs (SV-Tag 0) (SV-Tag 0) (SV-Tag 0) (SV-Tag 0))
                      (λ _ _ → nothing) bad-heap false

  bad-valid : ValidAtWF Heap bad-alloc
                {Unit Once.IRTy.⇛ Unit}
                (λ arg → evalᴰ (terminal {Unit Once.IRTy.* Unit}) (tt , arg))
                cloc bad-st
  bad-valid = valid-closure-wf {body = terminal} {env = tt}
                {alloc = bad-alloc} {closure-loc = cloc} {env-loc = eloc}
                {s = bad-st} {mEnv = Heap} {body-label = lbl}
                tt refl refl
                (heap-before (s≤s z≤n))
                (heap-before (s≤s z≤n))
                valid-unit-wf

  refute : CalleeRuns (ir-to-trace (id {Unit})) → ⊥
  refute cr with cr {Unit} {Unit} {Unit} terminal tt lbl bad-valid refl
  ... | (_ , () , _)
```

## `Once/Probe/ApexInconsistent.agda`

```agda
-- PROBE (not part of the build): the apex axiom `block-runs`, at the very
-- telescope `FlatFromObs` is instantiated with, proves ⊥.
open import Data.Nat using (ℕ)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Target.Arch using (arch-numerics)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CanonicalName using (CanonicalName)
import Once.CCC.FrameSemantics

module Once.Probe.ApexInconsistent (o : CanonicalName)
  (arch : Arch) (FS : FrameSemantics)
  (fmt-agree : Once.CCC.FrameSemantics.fs-numerics FS ≡ arch-numerics arch)
  (entry-frame : FrameSemantics.Frame FS)
  (asem : ArchSemantics) where

open import Data.Empty using (⊥)
open import Once.IR using (IR; Unit; id)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.Adequacy.ArchCorrectness.FlatFromObs o arch FS fmt-agree entry-frame asem
  using (block-runs)
open import Once.Probe.BlockRunsRefute o using (module Refute)

open IRObsCorrectFlatness {FS} using (BlockRuns)
open Refute {FS} entry-frame using (refute)

boom : ⊥
boom = refute (BlockRuns.closures (block-runs (id {Unit})))

------------------------------------------------------------------------
-- The NEIGHBOURING postulate `entry-size` used to be refuted here too, by
-- `boom-size = 1+n≰n (≤-trans (entry-size (iter program-bound))
--                             (iter-big program-bound))`.
-- Plan 0.91 S1 / D214 DELETED `entry-size` and the whole `program-bound`
-- telescope, so that half of this probe no longer even typechecks — which is
-- the point. `boom` above is what still stands.
------------------------------------------------------------------------
```

## `CodeResolves` (plan 0.91 S3) — REFUTED, 2026-09-17

The S3 premise proposed to replace `block-runs`. It is FALSE for every program:

    boom : ∀ (prog : AbstractTrace) → CodeResolves prog bad-alloc bad-st → ⊥

Run with the `.agdai` deleted; `Checking Once.Probe.CodeResolvesRefute` present,
0 errors, 0 unsolved metas. The definition has since been deleted, so this probe
cannot be re-run — it is kept here as the evidence for D216.

The refutation needs no fabricated heap of its own. It reuses `BlockRunsRefute`'s
`bad-valid` and decomposes ONE closure value TWO ways:

```agda
f : ⟦ Unit ⇛ Unit ⟧
f = λ arg → evalᴰ (terminal {Unit * Unit}) (tt , arg)

cvw₁ = decomposeClosureWF bad-valid
cvw₂ = record cvw₁ { body = terminal ∘ id ; f-is-closure = refl }

boom prog cr with cr f cloc cvw₁ | cr f cloc cvw₂
... | lb₁ , (j₁ , fe₁ , sp₁) , _ | lb₂ , (j₂ , fe₂ , sp₂) , _
      with just-injective (trans (sym fe₂) fe₁)
...   | refl = case trans (sym (sp₁ 1 _ refl)) (sp₂ 1 _ refl) of λ ()
```

`ClosureValidWF` ties `f` to the body's DENOTATION, not its syntax —

    f-is-closure : f ≡ (λ arg → evalᴰ body (env , arg))

— so `record cvw₁ { body = … }` is legal for any body with the same denotation,
and `evalᴰ (terminal ∘ id) ≡ evalᴰ terminal` definitionally (`returnT x _ = ([] , x)`,
`n ∸ 0 = n`, and η for pairs). But `CodeResolves`' conclusion mentions the body's
TEXT, and `find-thunk` is a function, so both resolve to the same `j`:

    ir-to-trace' n l terminal = n , l , []                 , []
    ir-to-trace' n l id       = n , l , (mov-to-output ∷ []) , []

`block-layout` then puts `c-ret` at index 1 of one block and `mov-to-output` at
index 1 of the other, both at `j+1`. `λ ()` closes it.
