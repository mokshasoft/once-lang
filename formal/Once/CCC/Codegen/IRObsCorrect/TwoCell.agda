-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell
--
-- D200: the TWO-CELL BUILDS — `curry` and `Ana` emit the SAME ten
-- instructions (D190), differing only in what goes in the code cell and where
-- the result is placed, so `TwoCellBuild` is factored out and each clause
-- supplies only its `ResultPlace`. `in-ν` (plan 0.88) is the same build again,
-- with a layer in cell 0 and the identity block in cell 1.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.TwoCell (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (LocState; readReg; Input1; writeReg-same; Output; SV-Ptr; module LocState; AbstractTrace; AllocState; sucLoc; StoredValue)
open LocState using (regs; halted)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (_*_; WellFormedFI; ⟦_⟧TI; ν-type)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IRTy as IRTy′
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Internal.Trace as TM

open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Run o tbl
open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Build o tbl
open import Once.CCC.Codegen.IRObsCorrect.BlockCall o tbl
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl
open import Once.CCC.Codegen.IRObsCorrect.AnaForce o tbl
open import Data.List.Relation.Unary.All using (_∷_; [])

module TwoCellC {FS : FrameSemantics} where

  open Core {FS}
  open NuV

  curry-denot-[] : ∀ {A B C} (body : IR (A * B) C) (m : AllocMode)
                   {x : ⟦ A ⟧} (s : LocState FS)
                 → ∀ k → eventsAt s (⟪ evalᴰ (curry body) x ⟫ k) ≡ []
  curry-denot-[] body m s k = refl


  open TwoCellRunC {FS}
  open TwoCellBuildC {FS}
  module BC = BlockCallC {FS}
  module NF = NuForceC {FS}
  open NF using (SeedKept)
  module AF = AnaForceC {FS}

  -- plan 0.125 S3: the closure's `runs` is PROVED, from the body's own
  -- correctness (`ihb`) through the block-call lemma (S2). The block is the
  -- head of this fragment's `BlocksAt`; the body's blocks are its tail.
  obs-correct-curry : ∀ {A B C} (body : IR (A * B) C) → IRObsCorrectF body → IRObsCorrectF (curry body)
  obs-correct-curry {A} {B} {C} body ihb n l prog base ss cr span ((j , feq , sp , lab) ∷ bl′) _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = sym (denot-[] k)
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-of TCR.run (sym (denot-[] k))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   (λ _ → TCB.cf-fs10)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf') (λ _ → TCB.sf-fs10)
      }
    where
      -- D339: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      -- D190: the ten-instruction build is shared with `Ana`; `emitted n l
      -- (curry body)` IS `two-cell-trace n l`, so `span` passes straight in.
      module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span
      module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (curry body) x ⟫ k) ≡ []
      denot-[] k = refl

      -- ── THE THREE INPUT RESIDENCES. The env cell receives whatever `Input1`
      -- held, so each residence picks the matching closure witness: a POINTER
      -- env gets `valid-closure-wf`, a register literal and a unit env get
      -- D181's `valid-closure-reg-wf`. Without that constructor the last two —
      -- and a unit env is `main`'s — would be unprovable.
      -- THE CLOSURE'S RUN. Every call of the block (`CallRuns`' premises) is
      -- a block call of `body` on the pair `(x , a)`: cell 1 is the argument
      -- the caller supplies, cell 0 holds what this closure's env cell holds,
      -- and `mk` says why that is a valid `x` there (one per residence).
      EnvCell : Set
      EnvCell = ∀ (fs : FlatState) (pre : AllocState {FS}) (pl : ValueLocation FS)
              → falloc fs ≡ enter-call pre
              → (∀ l′ → Live (falloc TCR.fs10) l′ → Live pre l′)
              → (∀ l′ → Live (falloc TCR.fs10) l′ → readLoc (floc fs) l′ ≡ readLoc (floc TCR.fs10) l′)
              → Live pre pl
              → readLoc (floc fs) pl ≡ readLoc (floc TCR.fs10) TCR.obj-loc
              → CellAt {prog = prog} (BC.callee-alloc _ fs) A x pl (BC.callee-loc _ fs)

      runs-from : EnvCell
                → CallRuns {prog = prog} {B} {C} (VAt {prog = prog} B) (VAt {prog = prog} C)
                    (falloc TCR.fs10) (floc TCR.fs10) TCR.obj-loc j (λ arg → evalᴰ body (x , arg))
      runs-from mk fs pre a pl ret-pc k′ rs′ pc nh′ fr fa ns incl agree i1 lpl slb c0 c1 =
        BC.block-call body ihb (suc (suc l)) prog (ℓ o l) _ j ss cr sp bl′ lab fs pre Heap (x , a) ret-pc k′ rs′ pc nh′ fr fa ns
          (in-loc pl (valid-pair-wf (live-heap lpl) (BC.live-callee _ fs pre fa _ slb) (mk fs pre pl fa incl agree lpl c0) c1′)
                  (BC.live-callee _ fs pre fa pl lpl) i1)
        where
          c1′ = cellWF-heap-transport (Live pre) (λ _ b → b) (λ l′ b → BC.callee-heap _ fs l′ b)
                  (BC.live-callee _ fs pre fa) a (sucLoc pl) slb c1

      place-of : InputAt mIn alloc x s
               → ResultPlace (B IRTy′.⇛ C) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                             (retVal (evalᴰ (curry body) x)) (floc TCR.fs10)
      place-of (in-reg fit eq) =
        at-loc TCR.obj-loc (mk-valid eq) TCB.before TCB.out-eq (mk-valid eq) TCB.before
        where
          ev≡in : TCR.cell0v ≡ readReg (regs s) Input1
          ev≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ prim-sv fit x)
                   → ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {B IRTy′.⇛ C}
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid e =
            valid-closure-reg-wf {env = x} tt (rep-prim fit)
              (trans TCB.cell0-fs10 (cong just (trans ev≡in e))) TCB.code-fs10 TCB.before-suc
              feq (runs-from mk)
            where
              mk : EnvCell
              mk fs pre pl fa incl agree lpl c0 =
                cell-inline (rep-prim fit)
                  (trans (BC.callee-heap _ fs pl lpl) (trans c0 (trans TCB.cell0-fs10 (cong just (trans ev≡in e)))))
      place-of (in-unit refl) =
        at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before
        where
          mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {B IRTy′.⇛ C}
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid =
            valid-closure-reg-wf {env = x} tt (rep-unit refl TCR.cell0v)
              TCB.cell0-fs10 TCB.code-fs10 TCB.before-suc
              feq (runs-from mk)
            where
              mk : EnvCell
              mk fs pre pl fa incl agree lpl c0 =
                cell-inline (rep-unit refl TCR.cell0v) (trans (BC.callee-heap _ fs pl lpl) (trans c0 TCB.cell0-fs10))
      place-of (in-loc loc valid bf eq) =
        at-loc TCR.obj-loc (mk-valid eq) TCB.before TCB.out-eq (mk-valid eq) TCB.before
        where
          ev≡ptr : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc) → TCR.cell0v ≡ SV-Ptr loc
          ev≡ptr e = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) e

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc)
                   → ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {B IRTy′.⇛ C}
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid e =
            valid-closure-wf tt
              (trans TCB.cell0-fs10 (cong just (ev≡ptr e))) TCB.code-fs10
              (live-lift TCB.bf-advance bf) TCB.before-suc
              feq (runs-from mk)
            where
              lb : Live (falloc TCR.fs10) loc
              lb = live-lift TCB.bf-advance bf

              mk : EnvCell
              mk fs pre pl fa incl agree lpl c0 =
                cell-ptr (trans (BC.callee-heap _ fs pl lpl) (trans c0 (trans TCB.cell0-fs10 (cong just (ev≡ptr e)))))
                         (BC.live-callee _ fs pre fa loc (incl loc lb))
                         (validityWF-heap-transport (Live (falloc TCR.fs10)) (λ _ b → b)
                            (λ l′ b → trans (BC.callee-heap _ fs l′ (incl l′ b)) (agree l′ b))
                            (λ l′ b → BC.live-callee _ fs pre fa l′ (incl l′ b))
                            x loc lb (TCB.valid-transport x loc (live→bf bf) valid))

      place : ResultPlace (B IRTy′.⇛ C) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                          (retVal (evalᴰ (curry body) x)) (floc TCR.fs10)
      place = place-of inp

  -- The suspension both introductions build: cell 0 the seed, cell 1 the
  -- block, and the block's force.
  module Susp (n l : ℕ) (prog : AbstractTrace) (base : ℕ) (s : LocState FS) (alloc : AllocState {FS})
              (cl : StoredValue FS) (rs : List ℕ) (n≤ : AllocState.next-slot alloc ≤ n) (nh : halted s ≡ false)
              (span : SpanAt prog base (two-cell-trace n l)) where
    module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span
    module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span

    kept : SeedKept alloc s (falloc TCR.fs10) (floc TCR.fs10)
    kept = (λ _ b → live-lift TCB.bf-advance b) , (λ l′ b → TCB.mem-pres l′ (live-ns n b))

    cell0v≡in : TCR.cell0v ≡ readReg (regs s) Input1
    cell0v≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

    susp : ∀ {F} {v : ⟦ ν-type F ⟧} (j : ℕ) → find-thunk prog (ℓ o l) ≡ just j
         → ForceRuns {prog = prog} {F} (λ m′ a′ v′ l′ s″ → NuV {prog = prog} {F} m′ a′ v′ l′ s″)
             (falloc TCR.fs10) (floc TCR.fs10) TCR.cell0v j v
         → ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {ν-type F} v TCR.obj-loc (floc TCR.fs10)
    susp j feq fr = valid-ν-wf nv
      where
        nv : NuV _ _ _ _ _
        nu-mode  nv = refl
        nu-heap  nv = tt
        nu-seed  nv = TCR.cell0v
        nu-lbl   nv = ℓ o l
        nu-j     nv = j
        nu-cell0 nv = TCB.cell0-fs10
        nu-cell1 nv = TCB.code-fs10
        nu-live1 nv = TCB.before-suc
        nu-code  nv = feq
        nu-force nv = fr

  -- D189: `Ana` — DISCHARGED, and it is `obs-correct-curry` with the other
  -- witness.
  --
  -- That is the whole content of the representation decision. A ν is a
  -- suspension: the seed in cell 0, the coalgebra's code address in cell 1.
  -- A closure is a suspension too — the env in cell 0, the body's code
  -- address in cell 1 — so the ten instructions are the same ten, the run is
  -- the same run, and the two clauses differ only in which `ValidAtWF`
  -- constructor they hand the two cells to. `TwoCellBuild` (D190) is
  -- everything before that choice; this clause is the choice.
  --
  -- The seed's residence is where D187's `CellAt` pays: a pointer seed, a
  -- register-sized seed and a `Unit` seed are ONE constructor here, whereas
  -- `curry` still needs `valid-closure-wf`/`valid-closure-reg-wf` to say the
  -- same thing twice.
  ------------------------------------------------------------------------
  -- D273: the seed is the pair `(e , a)`; nothing here depends on its shape.
  obs-correct-Ana : ∀ {F} (wf : WellFormedFI F) {E A} (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A))
                  → IRObsCorrectF coalg → IRObsCorrectF (Ana wf coalg)
  obs-correct-Ana {F} wf {E} {A} coalg ihc n l prog base ss cr span ((j , feq , sp , lab) ∷ bl′) _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = sym (denot-[] k)
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-of TCR.run (sym (denot-[] k))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   (λ _ → TCB.cf-fs10)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf') (λ _ → TCB.sf-fs10)
      }
    where
      -- D339: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span
      module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span

      -- Building a suspension RUNS NOTHING: the coalgebra is stored, not
      -- called, so neither side emits. (`Out` is where the events appear.)
      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (Ana wf coalg) x ⟫ k) ≡ []
      denot-[] k = refl

      cell0v≡in : TCR.cell0v ≡ readReg (regs s) Input1
      cell0v≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

      -- plan 0.125 S3: the ν's force is PROVED (`AnaForce`): this cell is an
      -- `Ana` suspension of the seed (`ana-p`), and every such is a `NuV`.
      module AB  = AF.AnaBlock wf coalg ihc l prog ss cr
      module ABB = AB.Block j feq sp lab bl′

      -- the seed cell, one clause per input residence
      seed-cell : InputAt mIn alloc x s → CellAt {prog = prog} (falloc TCR.fs10) (E IRTy′.* A) x TCR.obj-loc (floc TCR.fs10)
      seed-cell (in-reg fit e) = cell-inline (rep-prim fit) (trans TCB.cell0-fs10 (cong just (trans cell0v≡in e)))
      seed-cell (in-unit e)    = cell-inline (rep-unit e TCR.cell0v) TCB.cell0-fs10
      seed-cell (in-loc loc valid bf e) =
        cell-ptr (trans TCB.cell0-fs10 (cong just (trans cell0v≡in e))) (live-lift TCB.bf-advance bf)
                 (TCB.valid-transport x loc (live→bf bf) valid)

      mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {ν-type F}
                   (retVal (evalᴰ (Ana wf coalg) x)) TCR.obj-loc (floc TCR.fs10)
      mk-valid = valid-ν-wf (ABB.ana-nu (AB.ana-p x tt TCB.code-fs10 TCB.before-suc (seed-cell inp)))

      place : ResultPlace (ν-type F) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                          (retVal (evalᴰ (Ana wf coalg) x)) (floc TCR.fs10)
      place = at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before

  ------------------------------------------------------------------------
  -- plan 0.88: `in-ν` — DISCHARGED, and it is `obs-correct-Ana` at the other
  -- ORIGIN. `ir-to-trace' n l (in-ν _)` is `two-cell-trace n l` (D189: the
  -- layer goes in cell 0, the identity block's address in cell 1), so the run
  -- is `TwoCellRun`'s; what differs is only the cell-0 content the witness
  -- names (`from-layer`).
  --
  -- Unlike a seed `(e , a)`, a layer CAN be `Unit` (`⟦ K Unit ⟧TI X`), so its
  -- cell has all three residences, as a closure's environment does.
  ------------------------------------------------------------------------
  obs-correct-in-ν : ∀ {F} (wf : WellFormedFI F) → IRObsCorrectF (in-ν wf)
  obs-correct-in-ν {F} wf n l prog base ss cr span ((j , feq , sp , lab) ∷ []) _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = sym (denot-[] k)
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-of TCR.run (sym (denot-[] k))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   (λ _ → TCB.cf-fs10)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf') (λ _ → TCB.sf-fs10)
      }
    where
      -- D339: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span
      module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span

      -- Wrapping a layer RUNS NOTHING.
      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (in-ν wf) x ⟫ k) ≡ []
      denot-[] k = refl

      cell0v≡in : TCR.cell0v ≡ readReg (regs s) Input1
      cell0v≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

      module SU = Susp n l prog base s alloc cl rs n≤ nh span

      mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {ν-type F}
                   (retVal (evalᴰ (in-ν wf) x)) TCR.obj-loc (floc TCR.fs10)
      mk-valid = SU.susp j feq
        (NF.force-layer wf l prog j mIn x s alloc ss cr sp lab inp
           (falloc TCR.fs10) (floc TCR.fs10) TCR.cell0v SU.kept SU.cell0v≡in)

      place : ResultPlace (ν-type F) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                          (retVal (evalᴰ (in-ν wf) x)) (floc TCR.fs10)
      place = at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before

  ------------------------------------------------------------------------
  -- D188: `apply` — DISCHARGED against the block-table premise.
  --
  -- Sixteen instructions build the callee's `(env , arg)` pair on the heap and
  -- point `Input1` at it; the seventeenth calls. Everything about those
  -- seventeen is proved (D183/D185); what the premise supplies is the callee's
  -- own run, and nothing else.
  ------------------------------------------------------------------------

