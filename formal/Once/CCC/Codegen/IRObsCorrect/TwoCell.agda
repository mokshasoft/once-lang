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
open import Once.CCC.Machine.SMCore using (LocState; readReg; Input1; writeReg-same; Output; SV-Ptr; module LocState; AbstractTrace; AllocState; sucLoc; StoredValue; block-layout; e-thunk; offsetLoc; SV-Code; module AllocState)
open LocState using (regs; halted)
open AllocState using (current-frame; next-heap-ref; saved-frames)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Data.List.Relation.Unary.Any using (here; there)
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
open import Once.CCC.Codegen.IRToTrace o using (env-entry; env-prologue; with-copy; two-cell)
open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Copy o tbl using (module CopyTwoCellC)
open import Data.Product using (Σ)
open import Once.Memory.HeapAddress using (heap-loc)
open import Data.List.Relation.Unary.All using (_∷_; [])

module TwoCellC {FS : FrameSemantics} where

  open Core {FS}
  open NuV

  curry-denot-[] : ∀ {A B C π} (body : IR (A * B) C) (m : AllocMode)
                   {x : ⟦ A ⟧} (s : LocState FS)
                 → ∀ k → eventsAt s (⟪ evalᴰ (curry {π = π} body) x ⟫ k) ≡ []
  curry-denot-[] body m s k = refl


  open TwoCellRunC {FS}
  open TwoCellBuildC {FS}
  module BC = BlockCallC {FS}
  module NF = NuForceC {FS}
  open NF using (SeedKept)
  module AF = AnaForceC {FS}
  module CP = CurryProC {FS}
  module InjC′ = InjC {FS}
  module CTC = CopyTwoCellC {FS}

  -- D399 (β2): where the closure's ENVIRONMENT is, in the build's end state:
  -- the word in cell 0 is a scalar (`env-reg`), anything for a `Unit`
  -- (`env-unit`), or the address of a value valid there (`env-loc`) — the
  -- caller's value (a word environment, D386) or its copy (a flat one, D399).
  data EnvRes {prog : AbstractTrace} (A : IRTy) (x : ⟦ A ⟧) (aE : AllocState {FS}) (sE : LocState FS)
              : StoredValue FS → Set where
    env-reg  : (fit : FitsInRegI A) → EnvRes A x aE sE (prim-sv fit x)
    env-unit : ∀ {cv} → A ≡ IRTy′.Unit → EnvRes A x aE sE cv
    env-loc  : ∀ {m loc} → Live aE loc → ValidAtWF {prog = prog} m aE {A} x loc sE → EnvRes A x aE sE (SV-Ptr loc)

  -- plan 0.135 S3: the closure's `runs` is PROVED, from the body's own
  -- correctness (`ihb`) through the block-call lemma (S2). The block is the
  -- head of this fragment's `BlocksAt`; the body's blocks are its tail.
  -- D399: stated over the build's END STATE (`fsE`), whichever build it was.
  module CurryCore {A B C π} (body : IR (A * B) C) (ihb : IRObsCorrectF body)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ) (ss : AllSlotStable prog) (cr : BlockRuns prog)
    (j : ℕ) (feq : find-thunk prog (ℓ o l) ≡ just j)
    (sp : SpanAt prog j (block-layout (ℓ o l , proj₁ (ir-to-trace' (proj₁ (env-entry (kind A) A B)) (suc (suc l)) body)
                                      , proj₂ (env-entry (kind A) A B) DL.++ emitted (proj₁ (env-entry (kind A) A B)) (suc (suc l)) body)))
    (lab : LabelsAt prog (suc j) (proj₂ (env-entry (kind A) A B) DL.++ emitted (proj₁ (env-entry (kind A) A B)) (suc (suc l)) body))
    (bl′ : BlocksAt prog (blocks (proj₁ (env-entry (kind A) A B)) (suc (suc l)) body))
    (x : ⟦ A ⟧) (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ) (k : ℕ)
    (len : ℕ) (fsE : FlatState) (run : FlatSteps prog len (entry-flat base s alloc cl rs) fsE)
    (silent : chain-events run ≡ []) (nhE : halted (floc fsE) ≡ false)
    (atE : fpc fsE ≡ length (emitted n l (curry {π = π} body)) + base)
    (retE : fret fsE ≡ rs) (linkE : flink fsE ≡ nothing)
    (mem-pres : ∀ (loc : ValueLocation FS) → BeforeFrontier (record alloc { next-slot = n }) loc
              → readLoc (floc fsE) loc ≡ readLoc s loc)
    (cfE : current-frame (falloc fsE) ≡ current-frame alloc)
    (href : next-heap-ref alloc ≤ next-heap-ref (falloc fsE))
    (sfE : saved-frames (falloc fsE) ≡ saved-frames alloc)
    (bkE : BlocksKept alloc (falloc fsE))
    (objhl : HeapLocation) (cv : StoredValue FS)
    (cell0 : readLoc (floc fsE) (AtDynamic objhl) ≡ just cv)
    (code : readLoc (floc fsE) (sucLoc (AtDynamic objhl)) ≡ just (SV-Code (ℓ o l)))
    (before : Live (falloc fsE) (AtDynamic objhl))
    (before-suc : Live (falloc fsE) (sucLoc (AtDynamic objhl)))
    (out-eq : readReg (regs (floc fsE)) Output ≡ SV-Ptr (AtDynamic objhl))
    (env : EnvRes {prog} A x (falloc fsE) (floc fsE) cv)
    where

    obj-loc : ValueLocation FS
    obj-loc = AtDynamic objhl

    denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (curry {π = π} body) x ⟫ k) ≡ []
    denot-[] k = refl

    -- D400: the environment's footprint, which the closure carries
    env-foot : ∀ {cv′} → EnvRes {prog} A x (falloc fsE) (floc fsE) cv′ → Foot
    env-foot (env-reg _)  = []
    env-foot (env-unit _) = []
    env-foot (env-loc {loc = loc} _ v) = loc ∷ foot A loc v

    env-foot-live : ∀ {cv′} (r : EnvRes {prog} A x (falloc fsE) (floc fsE) cv′) → ∀ l′ → l′ ∈ᶠ env-foot r → Live (falloc fsE) l′
    env-foot-live (env-reg _)  l′ ()
    env-foot-live (env-unit _) l′ ()
    env-foot-live (env-loc {loc = loc} lb v) l′ (here b) = blk-live0 loc lb b
    env-foot-live (env-loc {loc = loc} lb v) l′ (there f) = foot-live A loc v l′ f

    EF : Foot
    EF = env-foot env

    -- ── `EnvSrc`: the env word, handed on at a call (D386), as a value to put (D390).
    EnvSrc : Set
    EnvSrc = ∀ (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) (pl : ValueLocation FS)
           → falloc fs ≡ enter-call pre
           → (∀ l′ → l′ ∈ᶠ EF → Live pre l′)
           → (∀ l′ → l′ ∈ᶠ EF → InBlk (falloc fsE) l′ → InBlk pre l′)
           → (∀ l′ → l′ ∈ᶠ EF → readLoc (floc fs) l′ ≡ readLoc (floc fsE) l′)
           → Live pre pl
           → readLoc (floc fs) pl ≡ readLoc (floc fsE) obj-loc
           → Σ (StoredValue FS) (λ w → readLoc (BC.callee-loc bb fs) pl ≡ just w
                                     × FlatPut.Src {FS} {prog} (BC.callee-alloc bb fs) (BC.callee-loc bb fs) A x w)

    word-size : kind A ≡ word → size A ≡ 1
    word-size = ws A
      where ws : ∀ (T′ : IRTy) → kind T′ ≡ word → size T′ ≡ 1
            ws (_ IRTy′.⇛[ _ ] _) _ = refl
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
                  (falloc fsE) (floc fsE) EF obj-loc j (λ arg → evalᴰ body (x , arg))
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

    -- the env word, from where the environment is
    mk-gen : ∀ {cv′} (r : EnvRes {prog} A x (falloc fsE) (floc fsE) cv′) → readLoc (floc fsE) obj-loc ≡ just cv′
           → ∀ (bb : ℕ) (fs : FlatState) (pre : AllocState {FS}) (pl : ValueLocation FS)
           → falloc fs ≡ enter-call pre
           → (∀ l′ → l′ ∈ᶠ env-foot r → Live pre l′)
           → (∀ l′ → l′ ∈ᶠ env-foot r → InBlk (falloc fsE) l′ → InBlk pre l′)
           → (∀ l′ → l′ ∈ᶠ env-foot r → readLoc (floc fs) l′ ≡ readLoc (floc fsE) l′)
           → Live pre pl
           → readLoc (floc fs) pl ≡ readLoc (floc fsE) obj-loc
           → Σ (StoredValue FS) (λ w → readLoc (BC.callee-loc bb fs) pl ≡ just w
                                     × FlatPut.Src {FS} {prog} (BC.callee-alloc bb fs) (BC.callee-loc bb fs) A x w)
    mk-gen (env-reg fit) c bb fs pre pl fa incl bkp agree lpl c0 =
      prim-sv fit x , trans (BC.callee-heap bb fs pl lpl) (trans c0 c) , FlatPut.src-scalar fit
    mk-gen {cv′} (env-unit refl) c bb fs pre pl fa incl bkp agree lpl c0 =
      cv′ , trans (BC.callee-heap bb fs pl lpl) (trans c0 c) , FlatPut.src-unit
    mk-gen r@(env-loc {loc = loc} lb v) c bb fs pre pl fa incl bkp agree lpl c0 =
      SV-Ptr loc , trans (BC.callee-heap bb fs pl lpl) (trans c0 c) ,
      InjC′.src-loc {prog} A (FT.v-tr A v (here (blk-refl loc)) (λ l′ f → there f))
        (BC.live-callee bb fs pre fa loc (incl loc (here (blk-refl loc))))
      where
        module FT = FootTransport {prog = prog} {a₁ = falloc fsE} {a₂ = BC.callee-alloc bb fs}
                      {s₁ = floc fsE} {s₂ = BC.callee-loc bb fs}
                      (_∈ᶠ env-foot r)
                      (λ l′ q → trans (BC.callee-heap bb fs l′ (incl l′ q)) (agree l′ q))
                      (λ l′ q _ → BC.live-callee bb fs pre fa l′ (incl l′ q))
                      (λ l′ q _ ib → BC.bk-enter bb fs pre fa l′ (incl l′ q) (bkp l′ q ib))

    mk : EnvSrc
    mk = mk-gen env cell0

    mk-valid : ValidAtWF {prog = prog} Heap (falloc fsE) {B IRTy′.⇛[ π ] C}
                 (retVal (evalᴰ (curry {π = π} body) x)) obj-loc (floc fsE)
    mk-valid = by-env env cell0
      where
        by-env : ∀ {cv′} → EnvRes {prog} A x (falloc fsE) (floc fsE) cv′ → readLoc (floc fsE) obj-loc ≡ just cv′
               → ValidAtWF {prog = prog} Heap (falloc fsE) {B IRTy′.⇛[ π ] C} (retVal (evalᴰ (curry {π = π} body) x)) obj-loc (floc fsE)
        by-env (env-reg fit)        c = valid-closure-reg-wf tt c code before-suc (env-foot-live env) feq (runs-from mk)
        by-env (env-unit _)         c = valid-closure-reg-wf tt c code before-suc (env-foot-live env) feq (runs-from mk)
        by-env (env-loc lb _)       c = valid-closure-wf tt c code lb before-suc (env-foot-live env) feq (runs-from mk)

    place : ResultPlace (B IRTy′.⇛[ π ] C) Heap (falloc fsE) (falloc fsE)
                        (retVal (evalᴰ (curry {π = π} body) x)) (floc fsE)
    place = at-loc obj-loc mk-valid before out-eq mk-valid before

    result : MachineRefinesObsF prog base n l (curry {π = π} body) x s alloc cl rs k
    result = record
      { traces-agree   = trans silent (sym (denot-[] k))
      ; value-realized =
          realized len fsE Heap (falloc fsE) run (λ _ → nhE) (λ _ → atE) (λ ()) (λ _ → retE) (λ _ → linkE)
                   (log-of run (trans silent (sym (denot-[] k)))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j′ bf' → mem-pres (AtStack fr j′) bf')
                   (λ _ hl bf' → mem-pres (AtDynamic hl) bf')
                   (λ _ → cfE)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc fsE) { next-slot = m })
                                     (sym cfE) ≤-refl href loc' bf') (λ _ → sfE)
                   (λ _ → bkE)
      }

  obs-correct-curry : ∀ {A B C π} (body : IR (A * B) C) → IRObsCorrectF body → IRObsCorrectF (curry {π = π} body)
  obs-correct-curry {A} {B} {C} {π} body ihb n l prog base ss cr span ((j , feq , sp , lab) ∷ bl′) _ mIn x s alloc cl ns0 nh inp k rs =
    by-kind (kind A) refl
    where
      n≤ = ns≤ {alloc} n ns0

      at-kd : ∀ kd → kind A ≡ kd → length (with-copy kd A n (λ m → two-cell m (ℓ o l))) + base ≡ length (emitted n l (curry {π = π} body)) + base
      at-kd kd e = cong (λ kd′ → length (with-copy kd′ A n (λ m → two-cell m (ℓ o l))) + base) (sym e)

      by-kind : ∀ kd → kind A ≡ kd → MachineRefinesObsF prog base n l (curry {π = π} body) x s alloc cl rs k
      -- a WORD environment: the plain build; cell 0 is what `Input1` held
      by-kind word kw = CC.result
        where
          span′ : SpanAt prog base (two-cell-trace n l)
          span′ = subst (λ kd → SpanAt prog base (with-copy kd A n (λ m → two-cell m (ℓ o l)))) kw span
          module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span′
          module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span′

          cell0v≡in : TCR.cell0v ≡ readReg (regs s) Input1
          cell0v≡in = writeReg-same (regs s) Output (readReg (regs s) Input1)

          envr : ∀ {cv} → cv ≡ TCR.cell0v → InputAt mIn alloc x s → EnvRes {prog} A x (falloc TCR.fs10) (floc TCR.fs10) cv
          envr e (in-reg fit eq) = subst (EnvRes {prog} A x _ _) (sym (trans e (trans cell0v≡in eq))) (env-reg fit)
          envr e (in-unit u)     = env-unit u
          envr e (in-loc loc valid bf eq) =
            subst (EnvRes {prog} A x _ _) (sym (trans e (trans cell0v≡in eq)))
                  (env-loc (live-lift TCB.bf-advance bf) (TCB.valid-transport x loc (live→bf bf) valid))

          module CC = CurryCore body ihb n l prog base ss cr j feq sp lab bl′ x s alloc cl rs k
                        10 TCR.fs10 TCR.run TCR.silent TCR.nh10 (at-kd word kw) refl refl
                        TCB.mem-pres TCB.cf-fs10 TCB.heapref-≤ TCB.sf-fs10 TCB.blocks-kept
                        TCR.obj-hl TCR.cell0v TCB.cell0-fs10 TCB.code-fs10 TCB.before TCB.before-suc TCB.out-eq
                        (envr refl inp)
      -- D399 (β2): a FLAT environment is copied first; cell 0 is the copy
      by-kind flat kf = CC.result
        where
          span′ : SpanAt prog base (CTC.copy-two-cell-trace A n l)
          span′ = subst (λ kd → SpanAt prog base (with-copy kd A n (λ m → two-cell m (ℓ o l)))) kf span
          module CR = CTC.CopyRun A kf n l prog base s alloc cl rs n≤ nh span′ (InjC′.mk-src {prog} A inp)

          module CC = CurryCore body ihb n l prog base ss cr j feq sp lab bl′ x s alloc cl rs k
                        _ CR.fsF CR.run CR.silent CR.nhF (at-kd flat kf) refl refl
                        CR.mem-pres CR.cf-F CR.heapref-≤ CR.sf-F CR.blocks-kept
                        CR.TCR.obj-hl _ CR.cell0 CR.TCB.code-fs10 CR.TCB.before CR.TCB.before-suc CR.TCB.out-eq
                        (env-loc CR.copy-live CR.copy-valid)

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

    -- D400: with the seed's footprint, which the force is told is kept
    susp : ∀ {F} {v : ⟦ ν-type F ⟧} (j : ℕ) → find-thunk prog (ℓ o l) ≡ just j
         → (E : Foot) → (∀ l′ → l′ ∈ᶠ E → Live (falloc TCR.fs10) l′)
         → ForceRuns {prog = prog} {F} (λ m′ a′ v′ l′ s″ → NuV {prog = prog} {F} m′ a′ v′ l′ s″)
             (falloc TCR.fs10) (floc TCR.fs10) E TCR.cell0v j v
         → ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {ν-type F} v TCR.obj-loc (floc TCR.fs10)
    susp j feq E el fr = valid-ν-wf nv
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
        nu-fp    nv = E
        nu-fp-live nv = el
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
      { traces-agree   = trans CR.silent (sym (denot-[] k))
      ; value-realized =
          realized _ CR.fsF Heap (falloc CR.fsF) CR.run (λ _ → CR.nhF) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl) (log-of CR.run (trans CR.silent (sym (denot-[] k)))) (λ { refl → place })
                   (m≤m+n k _)
                   (λ _ fr j bf' → CR.mem-pres (AtStack fr j) bf')
                   (λ _ hl bf' → CR.mem-pres (AtDynamic hl) bf')
                   (λ _ → CR.cf-F)
                   (λ _ m loc' bf' → frontier-monotone
                                     (record alloc { next-slot = m })
                                     (record (falloc CR.fsF) { next-slot = m })
                                     (sym CR.cf-F) ≤-refl CR.heapref-≤ loc' bf') (λ _ → CR.sf-F)
                   (λ _ → CR.blocks-kept)
      }
    where
      -- D359: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      -- D399 (β1): the seed pair is copied first; cell 0 is the copy
      module CR = CTC.CopyRun (E IRTy′.* A) refl n l prog base s alloc cl rs n≤ nh span (InjC′.mk-src {prog} (E IRTy′.* A) inp)

      -- Building a suspension RUNS NOTHING: the coalgebra is stored, not
      -- called, so neither side emits. (`Out` is where the events appear.)
      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (Ana wf coalg) x ⟫ k) ≡ []
      denot-[] k = refl

      -- plan 0.135 S3: the ν's force is PROVED (`AnaForce`): this cell is an
      -- `Ana` suspension of the seed (`ana-p`), and every such is a `NuV`.
      module AB  = AF.AnaBlock wf coalg ihc l prog ss cr
      module ABB = AB.Block j feq sp lab bl′

      mk-valid : ValidAtWF {prog = prog} Heap (falloc CR.fsF) {ν-type F}
                   (retVal (evalᴰ (Ana wf coalg) x)) CR.obj-loc (floc CR.fsF)
      mk-valid = valid-ν-wf (ABB.ana-nu (AB.ana-p x tt CR.cell0 CR.copy-live CR.copy-valid CR.TCB.code-fs10 CR.TCB.before-suc))

      place : ResultPlace (ν-type F) Heap (falloc CR.fsF) (falloc CR.fsF)
                          (retVal (evalᴰ (Ana wf coalg) x)) (floc CR.fsF)
      place = at-loc CR.obj-loc mk-valid CR.TCB.before CR.TCB.out-eq mk-valid CR.TCB.before

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
    by-kind (kind L) refl
    where
      L = ⟦ F ⟧TI (ν-type F)

      -- D359: the old premise, from the invariant.
      n≤ = ns≤ {alloc} n ns0

      -- Wrapping a layer RUNS NOTHING.
      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (in-ν wf) x ⟫ k) ≡ []
      denot-[] k = refl

      at-kd : ∀ kd → kind L ≡ kd → length (with-copy kd L n (λ m → two-cell m (ℓ o l))) + base ≡ length (emitted n l (in-ν wf)) + base
      at-kd kd e = cong (λ kd′ → length (with-copy kd′ L n (λ m → two-cell m (ℓ o l))) + base) (sym e)

      by-kind : ∀ kd → kind L ≡ kd → MachineRefinesObsF prog base n l (in-ν wf) x s alloc cl rs k
      -- a WORD layer: the plain build, cell 0 what `Input1` held
      by-kind word kw = record
        { traces-agree   = trans TCR.silent (sym (denot-[] k))
        ; value-realized =
            realized 10 TCR.fs10 Heap (falloc TCR.fs10) TCR.run (λ _ → TCR.nh10) (λ _ → at-kd word kw) (λ ()) (λ _ → refl) (λ _ → refl) (log-of TCR.run (trans TCR.silent (sym (denot-[] k)))) (λ { refl → place })
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
          span′ : SpanAt prog base (two-cell-trace n l)
          span′ = subst (λ kd → SpanAt prog base (with-copy kd L n (λ m → two-cell m (ℓ o l)))) kw span
          module TCR = TwoCellRun n l prog base s alloc cl rs n≤ nh span′
          module TCB = TwoCellBuild n l prog base s alloc cl rs n≤ nh span′
          module SU = Susp n l prog base s alloc cl rs n≤ nh span′

          mk-valid : ValidAtWF {prog = prog} Heap (falloc TCR.fs10) {ν-type F}
                       (retVal (evalᴰ (in-ν wf) x)) TCR.obj-loc (floc TCR.fs10)
          mk-valid = SU.susp j feq (NF.in-foot inp) (λ l′ e → proj₁ SU.kept l′ (NF.in-foot-live inp l′ e))
            (NF.force-layer wf l prog j mIn x s alloc ss cr sp lab inp
               (falloc TCR.fs10) (floc TCR.fs10) TCR.cell0v SU.kept SU.cell0v≡in)

          place : ResultPlace (ν-type F) Heap (falloc TCR.fs10) (falloc TCR.fs10)
                              (retVal (evalᴰ (in-ν wf) x)) (floc TCR.fs10)
          place = at-loc TCR.obj-loc mk-valid TCB.before TCB.out-eq mk-valid TCB.before
      -- D399 (β1): a FLAT layer is copied first; the suspension keeps the copy
      by-kind flat kf = record
        { traces-agree   = trans CR.silent (sym (denot-[] k))
        ; value-realized =
            realized _ CR.fsF Heap (falloc CR.fsF) CR.run (λ _ → CR.nhF) (λ _ → at-kd flat kf) (λ ()) (λ _ → refl) (λ _ → refl) (log-of CR.run (trans CR.silent (sym (denot-[] k)))) (λ { refl → place })
                     (m≤m+n k _)
                     (λ _ fr j bf' → CR.mem-pres (AtStack fr j) bf')
                     (λ _ hl bf' → CR.mem-pres (AtDynamic hl) bf')
                     (λ _ → CR.cf-F)
                     (λ _ m loc' bf' → frontier-monotone
                                       (record alloc { next-slot = m })
                                       (record (falloc CR.fsF) { next-slot = m })
                                       (sym CR.cf-F) ≤-refl CR.heapref-≤ loc' bf') (λ _ → CR.sf-F)
                     (λ _ → CR.blocks-kept)
        }
        where
          span′ : SpanAt prog base (CTC.copy-two-cell-trace L n l)
          span′ = subst (λ kd → SpanAt prog base (with-copy kd L n (λ m → two-cell m (ℓ o l)))) kf span
          module CR = CTC.CopyRun L kf n l prog base s alloc cl rs n≤ nh span′ (InjC′.mk-src {prog} L inp)
          module SU = Susp (suc (suc n)) l prog CR.base₂ CR.s₂ CR.A₁ cl rs CR.n≤₂ CR.nh₂ CR.span₂

          mk-valid : ValidAtWF {prog = prog} Heap (falloc CR.fsF) {ν-type F}
                       (retVal (evalᴰ (in-ν wf) x)) CR.obj-loc (floc CR.fsF)
          mk-valid = SU.susp j feq (NF.in-foot CR.copy-input₂) (λ l′ e → proj₁ SU.kept l′ (NF.in-foot-live CR.copy-input₂ l′ e))
            (NF.force-layer wf l prog j CR.copy-mode x CR.s₂ CR.A₁ ss cr sp lab CR.copy-input₂
               (falloc CR.fsF) (floc CR.fsF) SU.TCR.cell0v SU.kept SU.cell0v≡in)

          place : ResultPlace (ν-type F) Heap (falloc CR.fsF) (falloc CR.fsF)
                              (retVal (evalᴰ (in-ν wf) x)) (floc CR.fsF)
          place = at-loc CR.obj-loc mk-valid CR.TCB.before CR.TCB.out-eq mk-valid CR.TCB.before

  ------------------------------------------------------------------------
  -- D188: `apply` — DISCHARGED against the block-table premise.
  --
  -- Sixteen instructions build the callee's `(env , arg)` pair on the heap and
  -- point `Input1` at it; the seventeenth calls. Everything about those
  -- seventeen is proved (D183/D185); what the premise supplies is the callee's
  -- own run, and nothing else.
  ------------------------------------------------------------------------

