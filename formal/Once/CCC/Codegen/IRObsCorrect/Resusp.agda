-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp
--
-- plan 0.125 S3: THE RE-SUSPENSION (`resuspend-layer`, IRToTrace, D199) does
-- what `AnaDen.rsd` says. It runs at the end of the `Ana` block, after the
-- coalgebra: Output holds the coalgebra's layer `y : ⟦ G ⟧TI A`, slot 0 holds
-- the forced suspension's seed pair `(e , a)`, and the code rebuilds the
-- layer with every recursive position `a′` replaced by a FRESH suspension of
-- the pair `(e , a′)` whose code cell is the block's own label.
--
-- Parametric in what a fresh suspension IS (`R`, `mk-child`): `AnaForce`
-- instantiates it with its inductive `AnaP`. The run emits nothing, allocates
-- only fresh heap cells, writes only the current frame's slots at or above
-- `n`, and leaves the control state as it found it.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl
open import Once.CCC.Codegen.IRToTrace o using (resuspend-layer)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; StoredValue; readReg; Output
        ; SV-Code; SV-Ptr; sucLoc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; IsBaseTypeI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Id o tbl using (module ResuspIdC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Prod o tbl using (module ResuspProdC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Sum o tbl using (module ResuspSumC)
import Once.CCC.Machine.ValueRel as CWF
open import Data.Sum using (inj₁)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain

module ResuspC {FS : FrameSemantics} where

  open Core {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; current-frame; saved-frames)
  open NuForceC {FS} using (module AnaDen)
  open CWF.ClosureWellFormedBase {FS} using (fo-base)

  module Resusp {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
                (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
                (prog : AbstractTrace) (lbl-n : ℕ)
                (R : VTy (ν-type F))
                -- a fresh suspension of `(e , a′)` with this block's code is an `R`
                (mk-child : ∀ {alloc ν-loc s} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                          → LocMatchesMode Heap ν-loc
                          → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                          → Live alloc (sucLoc ν-loc)
                          → CellAt {prog = prog} alloc (E IRTy′.* A) (e , a′) ν-loc s
                          → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
                -- …and stays one while what was live stays live and unchanged
                (R-tr : ∀ {a a′ : AllocState {FS}} {s s′ : LocState FS}
                      → (∀ l → Live a l → Live a′ l)
                      → (∀ l → Live a l → readLoc s′ l ≡ readLoc s l)
                      → ∀ {m v lc} → R m a v lc s → R m a′ v lc s′)
                where

    rsd = AnaDen.rsd wf coalg e

    -- the re-suspension's text at frontier `n`, labels from `l`
    rtrace : ∀ {G : IRFunctor} → WellFormedFI G → ℕ → ℕ → AbstractTrace
    rtrace wG n l = proj₂ (proj₂ (resuspend-layer n l (ℓ o lbl-n) 0 wG))

    -- where a value is when it is in Output: a heap cell, a register literal,
    -- or nothing at all (`Unit`)
    data OutAt {C : IRTy} (alloc : AllocState {FS}) (c : ValueDomain.⟦ C ⟧ᴰᴵ) (st : LocState FS) : Set where
      out-loc  : ∀ {m} (loc : ValueLocation FS) → ValidAtWF {prog = prog} m alloc {C} c loc st → Live alloc loc
               → readReg (regs st) Output ≡ SV-Ptr loc → OutAt alloc c st
      out-reg  : (fit : FitsInRegI C) → readReg (regs st) Output ≡ prim-sv fit c → OutAt alloc c st
      out-unit : C ≡ IRTy′.Unit → OutAt alloc c st

    record RRuns {G : IRFunctor} (wG : WellFormedFI G) (n l : ℕ) (σ : FlatState)
                 (y : ValueDomain.⟦ ⟦ G ⟧TI A ⟧ᴰᴵ) : Set where
      field
        steps    : ℕ
        settle   : FlatState
        run      : FlatSteps prog steps σ settle
        nh       : halted (floc settle) ≡ false
        pc       : fpc settle ≡ DL.length (rtrace wG n l) + fpc σ
        ret      : fret settle ≡ fret σ
        lnk      : flink settle ≡ nothing
        ev       : chain-events run ≡ []
        log      : LocState.ev-log (floc settle) ≡ LocState.ev-log (floc σ)
        left     : LocState.left (floc settle) ≡ LocState.left (floc σ)
        out-mode : AllocMode
        out      : ResultPlaceP {⟦ G ⟧TI (ν-type F)} (LayerV G {ν-type F} R) out-mode
                     (falloc settle) (falloc settle) (rsd wG y) (floc settle)
        -- below the scratch region nothing moves: the caller's frames, the
        -- slots under `n` (slot 0 among them), the heap before the frontier
        mem      : ∀ (loc : ValueLocation FS) → BeforeFrontier (record (falloc σ) { next-slot = n }) loc
                 → readLoc (floc settle) loc ≡ readLoc (floc σ) loc
        cf       : current-frame (falloc settle) ≡ current-frame (falloc σ)
        sf       : saved-frames (falloc settle) ≡ saved-frames (falloc σ)
        bf-mono  : ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record (falloc σ) { next-slot = m }) loc
                 → BeforeFrontier (record (falloc settle) { next-slot = m }) loc

    ----------------------------------------------------------------------
    -- THE PROOF, by induction on `wG` (one module per case: `Resusp.Id`,
    -- `Resusp.Prod`, `Resusp.Sum`). It is stated there in a stronger form
    -- (`RBase.RRuns′`): the inputs are valid at a BASE allocator no later
    -- than the start, the stack frontier comes back unchanged, and the
    -- result survives any later state that keeps its footprint — which is
    -- what a product needs of its second component, whose result must
    -- outlive the write of the fresh pair's second cell.
    ----------------------------------------------------------------------
    private
      module B = ResuspBaseC.RBase {FS} wf coalg e prog lbl-n R mk-child
      open ResuspBaseC {FS} using (SegA; seg-bf; live-from; Kp; Prot)

      resusp-K : ∀ {C} (ib : IsBaseTypeI C) → B.Resusp′ (wf-K ib)
      resusp-K {C} ib n l σ y pl b hb span lab nh lk ns n≥1 sl0 lpl cE (B.out-loc {m} loc v bf rax) = record
        { steps = 0 ; settle = σ ; run = [] ; nh = nh ; pc = refl ; ret = refl ; lnk = lk
        ; ev = chain-events-nil {prog} {σ} ; log = refl ; left = refl
        ; out-mode = m
        ; rout = B.ro-loc loc (live-from b (falloc σ) hb loc bf) rax
                   (λ {a′} {s′} bft rd → valid→fo {m = m} {alloc = a′} {A = C} {v = y} {loc = loc} {s = s′} (fo-base ib)
                      (B.v-tr {b} {a′} {floc σ} {s′}
                         ((λ l′ x → bft l′ (live-from b (falloc σ) hb l′ x)) , (λ l′ x → rd l′ (live-from b (falloc σ) hb l′ x , inj₁ x)))
                         {m} {C} {y} {loc} bf v))
        ; seg = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }
        }
      resusp-K ib n l σ y pl b hb span lab nh lk ns n≥1 sl0 lpl cE (B.out-reg fit rax) = record
        { steps = 0 ; settle = σ ; run = [] ; nh = nh ; pc = refl ; ret = refl ; lnk = lk
        ; ev = chain-events-nil {prog} {σ} ; log = refl ; left = refl
        ; out-mode = Heap
        ; rout = B.ro-reg fit rax
        ; seg = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }
        }
      resusp-K ib n l σ y pl b hb span lab nh lk ns n≥1 sl0 lpl cE (B.out-unit u) = record
        { steps = 0 ; settle = σ ; run = [] ; nh = nh ; pc = refl ; ret = refl ; lnk = lk
        ; ev = chain-events-nil {prog} {σ} ; log = refl ; left = refl
        ; out-mode = Heap
        ; rout = B.ro-unit u
        ; seg = record { mem = λ _ _ → refl ; cf = refl ; sf = refl ; ns = refl ; href = ≤-refl }
        }

      resusp′ : ∀ {G : IRFunctor} (wG : WellFormedFI G) → B.Resusp′ wG
      resusp′ (wf-K ib)     = resusp-K ib
      resusp′ wf-Id         = ResuspIdC.RId.resusp-Id {FS} wf coalg e prog lbl-n R mk-child
      resusp′ (wf-Prod f g) = ResuspProdC.RProd.resusp-Prod {FS} wf coalg e prog lbl-n R mk-child f g (resusp′ f) (resusp′ g)
      resusp′ (wf-Sum f g)  = ResuspSumC.RSum.resusp-Sum {FS} wf coalg e prog lbl-n R mk-child f g (resusp′ f) (resusp′ g)

      out-in : ∀ {C} {alloc : AllocState {FS}} {c : ValueDomain.⟦ C ⟧ᴰᴵ} {st : LocState FS}
             → OutAt {C} alloc c st → B.OutAt′ {C} alloc c st
      out-in (out-loc loc v bf rax) = B.out-loc loc v bf rax
      out-in (out-reg fit rax)      = B.out-reg fit rax
      out-in (out-unit u)           = B.out-unit u

      runs-out : ∀ {G : IRFunctor} {wG : WellFormedFI G} {n l σ y} → B.RRuns′ wG n l σ y (falloc σ) → RRuns wG n l σ y
      runs-out r = record
        { steps    = B.RRuns′.steps r
        ; settle   = B.RRuns′.settle r
        ; run      = B.RRuns′.run r
        ; nh       = B.RRuns′.nh r
        ; pc       = B.RRuns′.pc r
        ; ret      = B.RRuns′.ret r
        ; lnk      = B.RRuns′.lnk r
        ; ev       = B.RRuns′.ev r
        ; log      = B.RRuns′.log r
        ; left     = B.RRuns′.left r
        ; out-mode = B.RRuns′.out-mode r
        ; out      = B.ro→rp (B.RRuns′.rout r)
        ; mem      = SegA.mem (B.RRuns′.seg r)
        ; cf       = SegA.cf (B.RRuns′.seg r)
        ; sf       = SegA.sf (B.RRuns′.seg r)
        ; bf-mono  = seg-bf (B.RRuns′.seg r)
        }

    resusp : ∀ {G : IRFunctor} (wG : WellFormedFI G) (n l : ℕ) (σ : FlatState)
               (y : ValueDomain.⟦ ⟦ G ⟧TI A ⟧ᴰᴵ) (pl : ValueLocation FS)
           → SpanAt prog (fpc σ) (rtrace wG n l)
           → LabelsAt prog (fpc σ) (rtrace wG n l)
           → halted (floc σ) ≡ false → flink σ ≡ nothing
           → next-slot (falloc σ) ≡ 0 → 1 ≤ n
           → readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl)
           → Live (falloc σ) pl
           → CellAt {prog = prog} (falloc σ) E e pl (floc σ)
           → OutAt {⟦ G ⟧TI A} (falloc σ) y (floc σ)
           → RRuns wG n l σ y
    resusp wG n l σ y pl span lab nh lk ns n≥1 sl0 lpl cE oA =
      runs-out (resusp′ wG n l σ y pl (falloc σ) ≤-refl span lab nh lk ns n≥1 sl0 lpl cE (out-in oA))
