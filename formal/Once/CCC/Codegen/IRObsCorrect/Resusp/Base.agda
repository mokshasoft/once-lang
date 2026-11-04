-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Base
--
-- plan 0.135 S3 / plan 0.123 α2: the vocabulary the re-suspension's proof
-- (`Resusp`) is stated in, split out so each case of the induction can live
-- in its own module.
--
--   * `SegA a₀ n σ σ′`: what a run from `σ` to `σ′` leaves alone at frontier
--     `n`, measured against a base allocator (below-frontier memory, the
--     frame, the stack frontier) and that the heap frontier only grows.
--     Segments compose.
--   * `RRuns′`: `Resusp.RRuns` with the segment in place of the frontier
--     fields, and its result as an `ROut` — a re-suspended layer that stays
--     valid at every later state keeping its footprint (`Prot`), which is
--     what a later `put` of it needs.
--   * the bridges into the flat puts: an input layer as a `FlatPut.Src`, a
--     re-suspended one as a `FlatPutLay.LSrc`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Base (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl
open import Once.CCC.Codegen.IRToTrace o using (resuspend-layer)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Code; SV-Ptr; sucLoc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-K; wf-Id; wf-Sum; wf-Prod
                            ; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
import Once.CCC.Machine.ValueRel as CWF
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatPutLay as FlatPutLay
open import Once.CCC.Codegen.IRObsCorrect.Inj o tbl using (module InjC)

module ResuspBaseC {FS : FrameSemantics} where

  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix)
  open Resolve {FS} using (NoLabel)

  open Core {FS}
  open Mach {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)
  open NuForceC {FS} using (module AnaDen)
  open CWF.ClosureWellFormedBase {FS} using (CellAtP; fo-base; fo-unit; unit-wf)
  private module IC = InjC {FS}

  ------------------------------------------------------------------------
  -- LIVENESS. A live location is a heap cell below the heap frontier, so it
  -- is live whatever the stack frontier says.
  ------------------------------------------------------------------------
  live-from : ∀ (a a′ : AllocState {FS}) → next-heap-ref a ≤ next-heap-ref a′ → ∀ l → Live a l → Live a′ l
  live-from a a′ hr (AtDynamic _) (BeforeFrontier.heap-before r) = BeforeFrontier.heap-before (<-≤-trans r hr)

  -- Everything live stays live and reads the same.
  Kp : AllocState {FS} → LocState FS → AllocState {FS} → LocState FS → Set
  Kp a s a′ s′ = (∀ l → Live a l → Live a′ l) × (∀ l → Live a l → readLoc s′ l ≡ readLoc s l)

  kp-∘ : ∀ {a s a′ s′ a″ s″} → Kp a s a′ s′ → Kp a′ s′ a″ s″ → Kp a s a″ s″
  kp-∘ (b₁ , r₁) (b₂ , r₂) = (λ l x → b₂ l (b₁ l x)) , (λ l x → trans (r₂ l (b₁ l x)) (r₁ l x))

  ------------------------------------------------------------------------
  -- A SEGMENT of a run, at frontier `n`, measured against a BASE allocator
  -- `a₀`: what is below `a₀`'s frontier (with the stack frontier at `n`)
  -- reads the same at the end. `Seg` is the segment measured against its
  -- own start. Measured against a common base, segments compose by `trans`
  -- alone — which matters, because a later segment may write a heap cell an
  -- earlier one allocated (a product's second cell), live at its own start.
  ------------------------------------------------------------------------
  record SegA (a₀ : AllocState {FS}) (n : ℕ) (fs fs′ : FlatState) : Set where
    field
      mem  : ∀ (loc : ValueLocation FS) → BeforeFrontier (record a₀ { next-slot = n }) loc
           → readLoc (floc fs′) loc ≡ readLoc (floc fs) loc
      cf   : current-frame (falloc fs′) ≡ current-frame (falloc fs)
      sf   : saved-frames (falloc fs′) ≡ saved-frames (falloc fs)
      ns   : next-slot (falloc fs′) ≡ next-slot (falloc fs)
      href : next-heap-ref (falloc fs) ≤ next-heap-ref (falloc fs′)

  Seg : ℕ → FlatState → FlatState → Set
  Seg n fs fs′ = SegA (falloc fs) n fs fs′

  -- what is below one frontier is below a later one
  bf-step : ∀ {a a′ : AllocState {FS}} (m m′ : ℕ) → current-frame a′ ≡ current-frame a → m ≤ m′
          → next-heap-ref a ≤ next-heap-ref a′
          → ∀ loc → BeforeFrontier (record a { next-slot = m }) loc → BeforeFrontier (record a′ { next-slot = m′ }) loc
  bf-step {a} {a′} m m′ cf m≤ hr = frontier-monotone (record a { next-slot = m }) (record a′ { next-slot = m′ }) (sym cf) m≤ hr

  segA-∘ : ∀ {a₀ n fs fs′ fs″} → SegA a₀ n fs fs′ → SegA a₀ n fs′ fs″ → SegA a₀ n fs fs″
  segA-∘ p q = record
    { mem  = λ loc bf → trans (SegA.mem q loc bf) (SegA.mem p loc bf)
    ; cf   = trans (SegA.cf q) (SegA.cf p)
    ; sf   = trans (SegA.sf q) (SegA.sf p)
    ; ns   = trans (SegA.ns q) (SegA.ns p)
    ; href = ≤-trans (SegA.href p) (SegA.href q)
    }

  -- a segment measured against a later base, at a higher frontier, is one
  -- measured against an earlier base at a lower frontier
  seg-rebase : ∀ {a₀ a₁ n n₁ fs fs′} → SegA a₁ n₁ fs fs′
             → current-frame a₁ ≡ current-frame a₀ → n ≤ n₁ → next-heap-ref a₀ ≤ next-heap-ref a₁
             → SegA a₀ n fs fs′
  seg-rebase {a₀} {a₁} {n} {n₁} p cf le hr = record
    { mem  = λ loc bf → SegA.mem p loc (bf-step {a₀} {a₁} n n₁ cf le hr loc bf)
    ; cf   = SegA.cf p ; sf = SegA.sf p ; ns = SegA.ns p ; href = SegA.href p }

  -- the frontier field of `RRuns`, from a segment
  seg-bf : ∀ {a₀ n fs fs′} → SegA a₀ n fs fs′
         → ∀ (m : ℕ) (loc : ValueLocation FS) → BeforeFrontier (record (falloc fs) { next-slot = m }) loc
         → BeforeFrontier (record (falloc fs′) { next-slot = m }) loc
  seg-bf {fs = fs} {fs′} p m = bf-step {falloc fs} {falloc fs′} m m (SegA.cf p) ≤-refl (SegA.href p)

  -- a control step moves only the pc
  segA-pc : ∀ {a₀ n fs fs′} (k : ℕ) → SegA a₀ n fs fs′ → SegA a₀ n fs (record fs′ { fpc = k })
  segA-pc k p = record { mem = SegA.mem p ; cf = SegA.cf p ; sf = SegA.sf p ; ns = SegA.ns p ; href = SegA.href p }

  -- …and what a segment says about the cells live at its base
  seg-live-read : ∀ {a₀ n fs fs′} → SegA a₀ n fs fs′ → ∀ l → Live a₀ l → readLoc (floc fs′) l ≡ readLoc (floc fs) l
  seg-live-read {n = n} p l b = SegA.mem p l (live-ns n b)

  ------------------------------------------------------------------------
  -- WHERE THE PARTS OF A TEXT SIT: a span and a label scope, split along `++`.
  ------------------------------------------------------------------------
  span-take : ∀ (prog : AbstractTrace) (xs : AbstractTrace) {ys : AbstractTrace} (b : ℕ)
            → SpanAt prog b (xs ++ ys) → SpanAt prog b xs
  span-take prog xs {ys} b sp k i e = sp k i (fetch-++-left xs ys k i e)

  span-drop : ∀ (prog : AbstractTrace) (xs : AbstractTrace) {ys : AbstractTrace} (b : ℕ)
            → SpanAt prog b (xs ++ ys) → SpanAt prog (length xs + b) ys
  span-drop prog xs {ys} b sp k i e =
    subst (λ m → fetch prog m ≡ just i) (trans (cong (_+ b) (+-comm (length xs) k)) (+-assoc k (length xs) b))
          (sp (length xs + k) i (trans (fetch-++-right xs ys k) e))

  labels-take : ∀ (prog : AbstractTrace) (xs : AbstractTrace) {ys : AbstractTrace} (b : ℕ)
              → LabelsAt prog b (xs ++ ys) → LabelsAt prog b xs
  labels-take prog xs {ys} b la m j eq = la m j (fl-go-prefix xs ys m 0 j eq)

  labels-drop : ∀ (prog : AbstractTrace) (xs : AbstractTrace) {ys : AbstractTrace} (b : ℕ)
              → LabelsAt prog b (xs ++ ys)
              → (∀ m j → find-label ys m ≡ just j → NoLabel m xs)
              → LabelsAt prog (length xs + b) ys
  labels-drop prog xs {ys} b la nl m j eq =
    subst (λ z → find-label prog m ≡ just z) (+-assoc j (length xs) b) (la m (j + length xs) scan)
    where
      scan : find-label (xs ++ ys) m ≡ just (j + length xs)
      scan = trans (fl-go-skip xs ys m 0 (nl m j eq))
                   (trans (fl-go-shift ys m (length xs) 0) (cong (mmap (_+ length xs)) eq))

  ------------------------------------------------------------------------
  -- THE FOOTPRINT a re-suspended layer may depend on: what was live at the
  -- caller's base `b` (the input layer and the environment), and what the
  -- run itself allocated (at or above `h`, its start's heap frontier).
  ------------------------------------------------------------------------
  loc-ref : ValueLocation FS → ℕ
  loc-ref (AtStack _ _)  = 0
  loc-ref (AtDynamic hl) = HeapRef.ref-id (HeapLocation.heap-ref hl)

  live-ref : ∀ {a : AllocState {FS}} {l} → Live a l → loc-ref l < next-heap-ref a
  live-ref {l = AtDynamic _} (BeforeFrontier.heap-before r) = r

  Prot : AllocState {FS} → ℕ → AllocState {FS} → ValueLocation FS → Set
  Prot b h a l = Live a l × (Live b l ⊎ h ≤ loc-ref l)

  -- a later, wider footprint
  prot-mono : ∀ {b h h′ a a′ l} → h′ ≤ h → (∀ l → Live a l → Live a′ l) → Prot b h a l → Prot b h′ a′ l
  prot-mono le bft (lv , inj₁ x) = bft _ lv , inj₁ x
  prot-mono le bft (lv , inj₂ y) = bft _ lv , inj₂ (≤-trans le y)

  ------------------------------------------------------------------------
  -- THE PROOF'S OWN VOCABULARY, at one `Ana` block.
  ------------------------------------------------------------------------
  module RBase {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
               (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
               (prog : AbstractTrace) (lbl-n : ℕ)
               (R : VTy (ν-type F))
               -- a fresh suspension: cell 0 the seed pair's pointer, cell 1 this block's code
               (mk-child : ∀ {alloc ν-loc s pl′} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                         → LocMatchesMode Heap ν-loc
                         → readLoc s ν-loc ≡ just (SV-Ptr pl′) → Live alloc pl′
                         → ValidAtWF {prog = prog} Heap alloc {E IRTy′.* A} (e , a′) pl′ s
                         → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                         → Live alloc (sucLoc ν-loc)
                         → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
               -- …and stays one while what was live stays live, unchanged, its blocks kept
               (R-tr : ∀ {a a′ : AllocState {FS}} {s s′ : LocState FS}
                     → (∀ l → Live a l → Live a′ l) → (∀ l → Live a l → readLoc s′ l ≡ readLoc s l)
                     → BlocksKept a a′
                     → ∀ {m v l} → R m a v l s → R m a′ v l s′)
               where

    X : IRTy
    X = ν-type F

    rsd = AnaDen.rsd wf coalg e

    rtrace : ∀ {G : IRFunctor} → WellFormedFI G → ℕ → ℕ → AbstractTrace
    rtrace wG n l = proj₂ (proj₂ (resuspend-layer F E A n l (ℓ o lbl-n) 0 wG))

    data OutAt′ {C : IRTy} (alloc : AllocState {FS}) (c : ValueDomain.⟦ C ⟧ᴰᴵ) (st : LocState FS) : Set where
      out-loc  : ∀ {m} (loc : ValueLocation FS) → ValidAtWF {prog = prog} m alloc {C} c loc st → Live alloc loc
               → readReg (regs st) Output ≡ SV-Ptr loc → OutAt′ alloc c st
      out-reg  : (fit : FitsInRegI C) → readReg (regs st) Output ≡ prim-sv fit c → OutAt′ alloc c st
      out-unit : C ≡ IRTy′.Unit → OutAt′ alloc c st

    LV : (G : IRFunctor) → VTy (⟦ G ⟧TI X)
    LV G = LayerV G {X} R

    -- A RESULT THAT SURVIVES whatever keeps its footprint: the layer is
    -- valid at every later state that keeps live what was live, keeps its
    -- blocks, and leaves the footprint alone.
    data ROut (G : IRFunctor) (m : AllocMode) (b : AllocState {FS}) (h : ℕ) (a : AllocState {FS})
              (s : LocState FS) (v : ValueDomain.⟦ ⟦ G ⟧TI X ⟧ᴰᴵ) : Set where
      ro-unit : ⟦ G ⟧TI X ≡ IRTy′.Unit → ROut G m b h a s v
      ro-reg  : (fit : FitsInRegI (⟦ G ⟧TI X)) → readReg (regs s) Output ≡ prim-sv fit v → ROut G m b h a s v
      ro-loc  : (loc : ValueLocation FS) → Live a loc → readReg (regs s) Output ≡ SV-Ptr loc
              → (∀ {a′ s′} → (∀ l → Live a l → Live a′ l) → BlocksKept a a′
                 → (∀ l → Prot b h a l → readLoc s′ l ≡ readLoc s l)
                 → LV G m a′ v loc s′)
              → ROut G m b h a s v

    ro→rp : ∀ {G m b h a s v} → ROut G m b h a s v → ResultPlaceP {⟦ G ⟧TI X} (LV G) m a a v s
    ro→rp (ro-unit u) = rp-unit u
    ro→rp (ro-reg fit rax) = rp-reg fit rax
    ro→rp (ro-loc loc lv rax f) =
      rp-loc loc (f (λ _ x → x) (λ _ _ ib → ib) (λ _ _ → refl)) lv rax (f (λ _ x → x) (λ _ _ ib → ib) (λ _ _ → refl)) lv

    record RRuns′ {G : IRFunctor} (wG : WellFormedFI G) (n l : ℕ) (σ : FlatState)
                  (y : ValueDomain.⟦ ⟦ G ⟧TI A ⟧ᴰᴵ) (b : AllocState {FS}) : Set where
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
        left     : ending (floc settle) ≡ ending (floc σ)
        out-mode : AllocMode
        rout     : ROut G out-mode b (next-heap-ref (falloc σ)) (falloc settle) (floc settle) (rsd wG y)
        seg      : Seg n σ settle
        -- D381: the blocks live at the start keep their sizes
        bk       : BlocksKept (falloc σ) (falloc settle)

    -- THE CASE STATEMENT, one functor at a time. The inputs are valid at a
    -- BASE `b` no later than the start (its blocks kept), and the result's
    -- footprint is what is live at `b` plus what the run allocates.
    Resusp′ : ∀ {G : IRFunctor} → WellFormedFI G → Set
    Resusp′ {G} wG =
      ∀ (n l : ℕ) (σ : FlatState) (y : ValueDomain.⟦ ⟦ G ⟧TI A ⟧ᴰᴵ) (pl : ValueLocation FS)
        (b : AllocState {FS}) → next-heap-ref b ≤ next-heap-ref (falloc σ) → BlocksKept b (falloc σ)
      → SpanAt prog (fpc σ) (rtrace wG n l)
      → LabelsAt prog (fpc σ) (rtrace wG n l)
      → halted (floc σ) ≡ false → flink σ ≡ nothing
      → next-slot (falloc σ) ≡ 0 → 1 ≤ n
      → readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl)
      → Live b pl
      → CellAt {prog = prog} b E e pl (floc σ)
      → OutAt′ {⟦ G ⟧TI A} b y (floc σ)
      → RRuns′ wG n l σ y b

    ----------------------------------------------------------------------
    -- BRIDGES INTO THE PUTS.
    ----------------------------------------------------------------------
    -- an input value, where a read or the caller left it, as a value to put
    out→src : ∀ {C : IRTy} {a s} {c : ValueDomain.⟦ C ⟧ᴰᴵ} → OutAt′ {C} a c s
            → FlatPut.Src {FS} {prog} a s C c (readReg (regs s) Output)
    out→src {C} {a} {s} {c} (out-loc loc v lv rax) = subst (FlatPut.Src {FS} {prog} a s C c) (sym rax) (IC.src-loc {prog} C v lv)
    out→src {C} {a} {s} {c} (out-reg fit rax) = subst (FlatPut.Src {FS} {prog} a s C c) (sym rax) (FlatPut.src-scalar fit)
    out→src (out-unit refl) = FlatPut.src-unit

    -- a read's result, as an input
    place→out : ∀ {C : IRTy} {m a ca s} {c : ValueDomain.⟦ C ⟧ᴰᴵ} → ResultPlace {prog = prog} C m a ca c s → OutAt′ {C} a c s
    place→out (at-loc loc v lv rax _ _) = out-loc loc v lv rax
    place→out (at-reg fit rax) = out-reg fit rax
    place→out unit-result = out-unit refl

    open FlatPutLay.PutLay {FS} {prog} R R-tr public using (LSrc; ls-node; ls-scalar; ls-flat; ls-unit; PutOutL; module PutOutL; put-lay-run)

    -- a `Unit` layer is valid anywhere
    unit-lay : ∀ {G} (wG : WellFormedFI G) {v} → ⟦ G ⟧TI X ≡ IRTy′.Unit → ∀ {m a l s} → LV G m a v l s
    unit-lay (wf-K base-Unit) refl = fo-unit unit-wf
    unit-lay (wf-K base-Void) ()
    unit-lay (wf-K base-Int) ()
    unit-lay (wf-K base-Float) ()
    unit-lay (wf-K (base-Prod _ _)) ()
    unit-lay (wf-K (base-Sum _ _)) ()
    unit-lay wf-Id ()
    unit-lay (wf-Sum _ _) ()
    unit-lay (wf-Prod _ _) ()

    -- a re-suspended layer, read at a later state that keeps its footprint,
    -- as a value to put
    rout→src : ∀ {G} (wG : WellFormedFI G) {m b h a s v a′ s′}
             → ROut G m b h a s v
             → (∀ l → Live a l → Live a′ l) → BlocksKept a a′ → (∀ l → Prot b h a l → readLoc s′ l ≡ readLoc s l)
             → LSrc a′ s′ wG v (readReg (regs s) Output)
    rout→src wG (ro-unit u) bft bk rd = ls-unit u (unit-lay wG u)
    rout→src wG {s = s} {v = v} {a′} {s′} (ro-reg fit rax) bft bk rd =
      subst (LSrc a′ s′ wG v) (sym rax) (ls-scalar fit)
    rout→src wG {s = s} {v = v} {a′} {s′} (ro-loc loc lv rax f) bft bk rd =
      subst (LSrc a′ s′ wG v) (sym rax) (by wG (f bft bk rd))
      where
        by : ∀ {G} (wG : WellFormedFI G) {m v} → LV G m a′ v loc s′ → LSrc a′ s′ wG v (SV-Ptr loc)
        by wf-Id r = ls-node tt (bft loc lv) r
        by (wf-K base-Unit) r = ls-flat tt (bft loc lv) r
        by (wf-K base-Void) {v = ()} r
        by (wf-K base-Int) (CWF.ClosureWellFormedBase.fo-int ())
        by (wf-K base-Float) (CWF.ClosureWellFormedBase.fo-float ())
        by (wf-K (base-Prod _ _)) r = ls-flat tt (bft loc lv) r
        by (wf-K (base-Sum _ _)) r = ls-flat tt (bft loc lv) r
        by (wf-Sum _ _) r = ls-flat tt (bft loc lv) r
        by (wf-Prod _ _) r = ls-flat tt (bft loc lv) r

    -- the inputs, carried along a segment at the same base
    kp-base : ∀ {b a₀ n fs fs′} → (∀ l → Live b l → Live a₀ l) → SegA a₀ n fs fs′ → Kp b (floc fs) b (floc fs′)
    kp-base bl p = (λ _ x → x) , (λ l x → seg-live-read p l (bl l x))
