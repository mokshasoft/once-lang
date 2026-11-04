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
open import Once.CCC.Machine.SMCore using (LocState; readReg; Input1; writeReg-same; Output; SV-Ptr; module LocState; AbstractTrace; AllocState; sucLoc; StoredValue; block-layout; e-thunk; offsetLoc)
open LocState using (regs; halted)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (_*_; WellFormedFI; ⟦_⟧TI; ν-type; IRTy)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IRTy as IRTy′
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM

open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Run o tbl
open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Build o tbl
open import Once.CCC.Codegen.IRObsCorrect.BlockCall o tbl
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl
open import Once.CCC.Codegen.IRObsCorrect.AnaForce o tbl
open import Once.CCC.Codegen.IRObsCorrect.CurryPro o tbl using (module CurryProC)
open import Once.CCC.Codegen.IRObsCorrect.Inj o tbl using (module InjC)
import Once.CCC.Machine.FlatPut as FlatPut
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; kind)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.IRToTrace o using (env-entry; env-prologue)
open import Data.Product using (Σ)
open import Once.Memory.HeapAddress using (heap-loc)
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
  module CP = CurryProC {FS}
  module InjC′ = InjC {FS}

  -- plan 0.135 S3: the closure's `runs` is PROVED, from the body's own
  -- correctness (`ihb`) through the block-call lemma (S2). The block is the
  -- head of this fragment's `BlocksAt`; the body's blocks are its tail.
  obs-correct-curry : ∀ {A B C} (body : IR (A * B) C) → IRObsCorrectF body → IRObsCorrectF (curry body)
  obs-correct-curry {A} {B} {C} body ihb n l prog base ss cr span ((j , feq , sp , lab) ∷ bl′) _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = trans TCR.silent (sym (denot-[] k))
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-of TCR.run (trans TCR.silent (sym (denot-[] k)))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   (λ _ → TCB.cf-fs10)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf') (λ _ → TCB.sf-fs10)
                   (λ _ → TCB.blocks-kept)
      }
    where
      -- D359: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      -- D190: the ten-instruction build is shared with `Ana`; `emitted n l
      -- (curry body)` IS `two-cell-trace n l`, so `span` passes straight in.
      module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span
      module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (curry body) x ⟫ k) ≡ []
      denot-[] k = refl

      -- ── THE THREE INPUT RESIDENCES. The env cell receives whatever `Input1`
      -- held; at a call, that word is handed on (D380) and is the
      -- environment's register form: a node's pointer or a flat value's
      -- address (`in-loc`), a scalar (`in-reg`), or anything at all for a
      -- `Unit` (`in-unit`). `EnvSrc` is that word as a value to put (D384).
      EnvSrc : Set
      EnvSrc = ∀ (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) (pl : ValueLocation FS)
             → falloc fs ≡ enter-call pre
             → (∀ l′ → Live (falloc TCR.fs10) l′ → Live pre l′)
             → BlocksKept (falloc TCR.fs10) pre
             → (∀ l′ → Live (falloc TCR.fs10) l′ → readLoc (floc fs) l′ ≡ readLoc (floc TCR.fs10) l′)
             → Live pre pl
             → readLoc (floc fs) pl ≡ readLoc (floc TCR.fs10) TCR.obj-loc
             → Σ (StoredValue FS) (λ w → readLoc (BC.callee-loc bb fs) pl ≡ just w
                                       × FlatPut.Src {FS} {prog} (BC.callee-alloc bb fs) (BC.callee-loc bb fs) A x w)

      word-size : kind A ≡ word → size A ≡ 1
      word-size = ws A
        where ws : ∀ (T′ : IRTy) → kind T′ ≡ word → size T′ ≡ 1
              ws (_ IRTy′.⇛ _) _ = refl
              ws (IRTy′.μ-type _) _ = refl
              ws (IRTy′.ν-type _) _ = refl
              ws IRTy′.Int _ = refl
              ws IRTy′.Float _ = refl
              ws IRTy′.Unit ()
              ws IRTy′.Void ()
              ws (_ IRTy′.* _) ()
              ws (_ IRTy′.+ _) ()

      -- a word-kind environment is its cell
      src→cell : ∀ {a st w pl} → kind A ≡ word → readLoc st pl ≡ just w
               → FlatPut.Src {FS} {prog} a st A x w → CellAt {prog = prog} a A x pl st
      src→cell kw r (FlatPut.src-node nd lv v) = cell-ptr nd r lv v
      src→cell kw r (FlatPut.src-scalar fit)   = cell-inline (rep-prim fit) r
      src→cell kw r (FlatPut.src-flat fl _ _)  = ⊥-elim (flat≠word fl kw)
        where flat≠word : ∀ {T′ : IRTy} → IsFlat T′ → kind T′ ≡ word → ⊥
              flat≠word {IRTy′.Unit} _ ()
              flat≠word {_ IRTy′.* _} _ ()
              flat≠word {_ IRTy′.+ _} _ ()
      src→cell kw r FlatPut.src-unit           = ⊥-elim (unit≠word kw)
        where unit≠word : kind IRTy′.Unit ≡ word → ⊥
              unit≠word ()

      l1 = suc (suc l)
      ENT : Kind → ℕ × AbstractTrace
      ENT kd = env-entry kd A B
      BT : Kind → AbstractTrace
      BT kd = proj₂ (ENT kd) DL.++ emitted (proj₁ (ENT kd)) l1 body
      BB : Kind → ℕ
      BB kd = proj₁ (ir-to-trace' (proj₁ (ENT kd)) l1 body)

      -- THE CLOSURE'S RUN, by the environment's kind: a word environment's
      -- call pair IS the body's input; a flat one's is rebuilt (`CurryPro`).
      runs-from : EnvSrc
                → CallRuns {prog = prog} {B} {C} (VAt {prog = prog} B) (VAt {prog = prog} C)
                    (falloc TCR.fs10) (floc TCR.fs10) TCR.obj-loc j (λ arg → evalᴰ body (x , arg))
      runs-from mk fs pre a pl ret-pc k′ rs′ pc nh′ fr fa ns incl bkp agree i1 lpl slb c0 c1 =
        by (kind A) refl sp lab bl′
        where
          lplC : ∀ bb → Live (BC.callee-alloc bb fs) pl
          lplC bb = BC.live-callee bb fs pre fa pl lpl
          ms = λ bb → mk bb fs pre pl fa incl bkp agree lpl c0
          w  = λ bb → proj₁ (ms bb)
          c0′ = λ bb → proj₁ (proj₂ (ms bb))
          srcE = λ bb → proj₂ (proj₂ (ms bb))
          c1′ = λ bb → cellWF-heap-transport (Live pre) (λ _ b → b) (λ l′ b → BC.callee-heap bb fs l′ b)
                  (BC.live-callee bb fs pre fa) (BC.bk-enter bb fs pre fa) a (sucLoc pl) slb c1

          by : ∀ (kd : Kind) → kind A ≡ kd
             → SpanAt prog j (block-layout (ℓ o l , BB (kind A) , BT (kind A)))
             → LabelsAt prog (suc j) (BT (kind A))
             → BlocksAt prog (blocks (proj₁ (ENT (kind A))) l1 body)
             → CalleeRunP {prog = prog} {C} (ResultPlaceP {C} (VAt {prog = prog} C)) fs ret-pc rs′ (evalᴰ body (x , a)) k′
          by word kw sp′ lab′ bl″ =
            BC.block-call body ihb l1 prog (ℓ o l) _ j ss cr
              (subst (λ kd → SpanAt prog j (block-layout (ℓ o l , BB kd , BT kd))) kw sp′)
              (subst (λ kd → BlocksAt prog (blocks (proj₁ (ENT kd)) l1 body)) kw bl″)
              (subst (λ kd → LabelsAt prog (suc j) (BT kd)) kw lab′)
              fs pre Heap (x , a) ret-pc k′ rs′ pc nh′ fr fa ns
              (in-loc pl (valid-pair-wf (live-heap lpl) (BC.live-callee _ fs pre fa _ slb)
                            (src→cell kw (c0′ (BB word)) (srcE (BB word)))
                            (subst (λ z → CellAt {prog = prog} _ B a z _) (sym (off1 lpl (word-size kw))) (c1′ (BB word))))
                      (lplC (BB word)) i1)
            where
              off1 : ∀ {l′} → Live pre l′ → size A ≡ 1 → offsetLoc l′ (size A) ≡ sucLoc l′
              off1 {AtDynamic (heap-loc r o′)} _ e = cong (λ z → AtDynamic (heap-loc r (z + o′))) e
          by flat kf sp′ lab′ bl″ =
            BC.entry-call-gen {C} {ResultPlace {prog = prog} C} {ResultPlaceP {C} (VAt {prog = prog} C)} BC.place-across
              (env-prologue A B DL.++ emitted 4 l1 body) (evalᴰ body (x , a)) prog (e-thunk (ℓ o l)) (BB flat) j sp″ fs pre ret-pc k′ rs′ pc nh′ fr fa
              (CP.Pro.body-runs body ihb l1 prog ss cr j (BC.Layout.body-span prog (e-thunk (ℓ o l)) (BB flat) j (env-prologue A B DL.++ emitted 4 l1 body) sp″)
                 (subst (λ kd → BlocksAt prog (blocks (proj₁ (ENT kd)) l1 body)) kf bl″)
                 (subst (λ kd → LabelsAt prog (suc j) (BT kd)) kf lab′)
                 (BC.callee-loc (BB flat) fs) (BC.callee-alloc (BB flat) fs) (fclosure fs) (ret-pc ∷ rs′) k′ x a
                 (trans (cong AllocState.next-slot fa) ns) nh′ i1 (lplC (BB flat)) (c0′ (BB flat)) (srcE (BB flat))
                 (c1′ (BB flat)))
            where
              sp″ = subst (λ kd → SpanAt prog j (block-layout (ℓ o l , BB kd , BT kd))) kf sp′

      place-of : InputAt mIn alloc x s
               → ResultPlace (B IRTy′.⇛ C) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                             (retVal (evalᴰ (curry body) x)) (floc TCR.fs10)
      place-of (in-reg fit eq) =
        at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before
        where
          cell0 : readLoc (floc TCR.fs10) TCR.obj-loc ≡ just (prim-sv fit x)
          cell0 = trans TCB.cell0-fs10 (cong just (trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq))

          mk : EnvSrc
          mk bb fs pre pl fa incl bkp agree lpl c0 =
            prim-sv fit x , trans (BC.callee-heap bb fs pl lpl) (trans c0 cell0) , FlatPut.src-scalar fit

          mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {B IRTy′.⇛ C}
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid = valid-closure-reg-wf tt cell0 TCB.code-fs10 TCB.before-suc feq (runs-from mk)
      place-of (in-unit refl) =
        at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before
        where
          mk : EnvSrc
          mk bb fs pre pl fa incl bkp agree lpl c0 =
            TCR.cell0v , trans (BC.callee-heap bb fs pl lpl) (trans c0 TCB.cell0-fs10) , FlatPut.src-unit

          mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {B IRTy′.⇛ C}
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid = valid-closure-reg-wf tt TCB.cell0-fs10 TCB.code-fs10 TCB.before-suc feq (runs-from mk)
      place-of (in-loc loc valid bf eq) =
        at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before
        where
          cell0 : readLoc (floc TCR.fs10) TCR.obj-loc ≡ just (SV-Ptr loc)
          cell0 = trans TCB.cell0-fs10 (cong just (trans (writeReg-same (regs s) Output (readReg (regs s) Input1)) eq))

          lb : Live (falloc TCR.fs10) loc
          lb = live-lift TCB.bf-advance bf

          mk : EnvSrc
          mk bb fs pre pl fa incl bkp agree lpl c0 =
            SV-Ptr loc , trans (BC.callee-heap bb fs pl lpl) (trans c0 cell0) ,
            InjC′.src-loc {prog} A
              (validityWF-heap-transport (Live (falloc TCR.fs10)) (λ _ b → b)
                 (λ l′ b → trans (BC.callee-heap bb fs l′ (incl l′ b)) (agree l′ b))
                 (λ l′ b → BC.live-callee bb fs pre fa l′ (incl l′ b))
                 (bk-trans {a = falloc TCR.fs10} {b = pre} {c = BC.callee-alloc bb fs} bkp (BC.bk-enter bb fs pre fa) incl)
                 x loc lb (TCB.valid-transport x loc (live→bf bf) valid))
              (BC.live-callee bb fs pre fa loc (incl loc lb))

          mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {B IRTy′.⇛ C}
                       (retVal (evalᴰ (curry body) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid = valid-closure-wf tt cell0 TCB.code-fs10 lb TCB.before-suc feq (runs-from mk)

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
    kept = (λ _ b → live-lift TCB.bf-advance b) , TCB.blocks-kept , (λ l′ b → TCB.mem-pres l′ (live-ns n b))

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
      { traces-agree   = trans TCR.silent (sym (denot-[] k))
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-of TCR.run (trans TCR.silent (sym (denot-[] k)))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   (λ _ → TCB.cf-fs10)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf') (λ _ → TCB.sf-fs10)
                   (λ _ → TCB.blocks-kept)
      }
    where
      -- D359: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span
      module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span

      -- Building a suspension RUNS NOTHING: the coalgebra is stored, not
      -- called, so neither side emits. (`Out` is where the events appear.)
      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (Ana wf coalg) x ⟫ k) ≡ []
      denot-[] k = refl

      cell0v≡in : TCR.cell0v ≡ readReg (regs s) Input1
      cell0v≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

      -- plan 0.135 S3: the ν's force is PROVED (`AnaForce`): this cell is an
      -- `Ana` suspension of the seed (`ana-p`), and every such is a `NuV`.
      module AB  = AF.AnaBlock wf coalg ihc l prog ss cr
      module ABB = AB.Block j feq sp lab bl′

      -- plan 0.123 α2: the seed is a pair, so it is in memory; cell 0 is its pointer
      seed : InputAt mIn alloc x s → AB.AnaP Heap (falloc TCR.fs10) (retVal (evalᴰ (Ana wf coalg) x)) TCR.obj-loc (floc TCR.fs10)
      seed (in-loc loc valid bf e) =
        AB.ana-p x tt (trans TCB.cell0-fs10 (cong just (trans cell0v≡in e))) (live-lift TCB.bf-advance bf)
                 (TCB.valid-transport x loc (live→bf bf) valid) TCB.code-fs10 TCB.before-suc
      seed (in-reg () _)
      seed (in-unit ())

      mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {ν-type F}
                   (retVal (evalᴰ (Ana wf coalg) x)) TCR.obj-loc (floc TCR.fs10)
      mk-valid = valid-ν-wf (ABB.ana-nu (seed inp))

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
      { traces-agree   = trans TCR.silent (sym (denot-[] k))
      ; value-realized =
          realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-of TCR.run (trans TCR.silent (sym (denot-[] k)))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j bf' → TCB.mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → TCB.mem-pres (AtDynamic hl) bf')
                   (λ _ → TCB.cf-fs10)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc TCR.fs10) { next-slot = m })
                                     (sym TCB.cf-fs10) ≤-refl TCB.heapref-≤ loc' bf') (λ _ → TCB.sf-fs10)
                   (λ _ → TCB.blocks-kept)
      }
    where
      -- D359: the old premise, from the invariant.
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

