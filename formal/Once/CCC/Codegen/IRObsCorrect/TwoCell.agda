-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell
--
-- D200: the TWO-CELL BUILDS — `curry` and `Ana` emit the SAME ten
-- instructions (D190), differing only in what goes in the code cell and where
-- the result is placed, so `TwoCellBuild` is factored out and each clause
-- supplies only its `ResultPlace`.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.TwoCell (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Run o tbl
open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Build o tbl

module TwoCellC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}

  curry-denot-[] : ∀ {A B C} (body : IR (A * B) C) (m : AllocMode)
                   {x : ⟦ A ⟧} (s : LocState FS)
                 → eventsAt s (evalᴰ (curry body) x) ≡ []
  curry-denot-[] body m s = refl


  open TwoCellRunC {FS}
  open TwoCellBuildC {FS}

  obs-correct-curry : ∀ {A B C} (body : IR (A * B) C) → IRObsCorrectF (curry body)
  obs-correct-curry {A} {B} {C} body n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k =
    record
      { traces-agree   = sym (denot-[] k)
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) refl refl (log-of TCR.run _ (sym (denot-[] k))) (λ { refl → place })
                   (λ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   TCB.cf-fs10
                   (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf')
      }
    where
      -- D190: the ten-instruction build is shared with `Ana`; `emitted n l
      -- (curry body)` IS `two-cell-trace n l`, so `span` passes straight in.
      module TCR = TwoCellRun n l prog base s alloc cl n≤ nh span
      module TCB = TwoCellBuild n l prog base s alloc cl n≤ nh span

      denot-[] : ∀ k → eventsAt s (evalᴰ (curry body) x) ≡ []
      denot-[] k = refl

      -- ── THE THREE INPUT RESIDENCES. The env cell receives whatever `Input1`
      -- held, so each residence picks the matching closure witness: a POINTER
      -- env gets `valid-closure-wf`, a register literal and a unit env get
      -- D181's `valid-closure-reg-wf`. Without that constructor the last two —
      -- and a unit env is `main`'s — would be unprovable.
      place-of : InputAt mIn alloc x s
               → ResultPlace (B IRTy.⇛ C) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                             (retVal (evalᴰ (curry body) x)) (floc TCR.fs10)
      place-of (in-reg fit eq) =
        at-loc TCR.obj-loc (mk-valid eq) TCB.before TCB.out-eq (mk-valid eq) TCB.before
        where
          ev≡in : TCR.cell0v ≡ readReg (regs s) Input1
          ev≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ prim-sv fit x)
                   → ValidAtWF Heap (falloc TCR.fs10)
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid e =
            valid-closure-reg-wf {body = body} {env = x} tt (rep-prim fit)
              (trans TCB.cell0-fs10 (cong just (trans ev≡in e))) TCB.code-fs10 TCB.before-suc
      place-of (in-unit refl) =
        at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before
        where
          mk-valid : ValidAtWF Heap (falloc TCR.fs10)
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid =
            valid-closure-reg-wf {body = body} {env = x} tt (rep-unit refl TCR.cell0v)
              TCB.cell0-fs10 TCB.code-fs10 TCB.before-suc
      place-of (in-loc loc valid bf eq) =
        at-loc TCR.obj-loc (mk-valid eq) TCB.before TCB.out-eq (mk-valid eq) TCB.before
        where
          ev≡ptr : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc) → TCR.cell0v ≡ SV-Ptr loc
          ev≡ptr e = trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) e

          mk-valid : ∀ (e : readReg (regs s) Input1 ≡ SV-Ptr loc)
                   → ValidAtWF Heap (falloc TCR.fs10)
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid e =
            valid-closure-wf {body = body} {env = x} tt
              (trans TCB.cell0-fs10 (cong just (ev≡ptr e))) TCB.code-fs10
              (TCB.bf-advance bf) TCB.before-suc (TCB.valid-transport x loc bf valid)

      place : ResultPlace (B IRTy.⇛ C) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                          (retVal (evalᴰ (curry body) x)) (floc TCR.fs10)
      place = place-of inp

  ------------------------------------------------------------------------
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
  obs-correct-Ana : ∀ {F} (wf : WellFormedFI F) {E A} (coalg : IR (E IRTy.* A) (⟦ F ⟧TI A))
                  → IRObsCorrectF (Ana wf coalg)
  obs-correct-Ana {F} wf {E} {A} coalg n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh inp k =
    record
      { traces-agree   = sym (denot-[] k)
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) refl refl (log-of TCR.run _ (sym (denot-[] k))) (λ { refl → place })
                   (λ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   TCB.cf-fs10
                   (λ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf')
      }
    where
      module TCR = TwoCellRun n l prog base s alloc cl n≤ nh span
      module TCB = TwoCellBuild n l prog base s alloc cl n≤ nh span

      -- Building a suspension RUNS NOTHING: the coalgebra is stored, not
      -- called, so neither side emits. (`Out` is where the events appear.)
      denot-[] : ∀ k → eventsAt s (evalᴰ (Ana wf coalg) x) ≡ []
      denot-[] k = refl

      cell0v≡in : TCR.cell0v ≡ readReg (regs s) Input1
      cell0v≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

      -- THE SEED CELL — one clause per residence, one constructor for all three.
      cell-of : InputAt mIn alloc x s
              → CellAt (falloc TCR.fs10) (E IRTy.* A) x TCR.obj-loc (floc TCR.fs10)
      cell-of (in-reg fit eq) =
        cell-inline (rep-prim fit)
          (trans TCB.cell0-fs10 (cong just (trans cell0v≡in eq)))
      cell-of (in-unit ())
      cell-of (in-loc loc valid bf eq) =
        cell-ptr (trans TCB.cell0-fs10 (cong just (trans cell0v≡in eq)))
                 (TCB.bf-advance bf) (TCB.valid-transport x loc bf valid)

      mk-valid : ValidAtWF Heap (falloc TCR.fs10)
                   (retVal (evalᴰ (Ana wf coalg) x)) TCR.obj-loc (floc TCR.fs10)
      mk-valid = valid-ν-susp-wf wf {coalg = coalg} {seed = x} tt
                   (cell-of inp) TCB.code-fs10 TCB.before-suc

      place : ResultPlace (ν-type F) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                          (retVal (evalᴰ (Ana wf coalg) x)) (floc TCR.fs10)
      place = at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before

  ------------------------------------------------------------------------
  -- D188: `apply` — DISCHARGED against the block-table premise.
  --
  -- Sixteen instructions build the callee's `(env , arg)` pair on the heap and
  -- point `Input1` at it; the seventeenth calls. Everything about those
  -- seventeen is proved (D183/D185); what the premise supplies is the callee's
  -- own run, and nothing else.
  ------------------------------------------------------------------------

