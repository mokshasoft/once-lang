-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Base
--
-- plan 0.125 S3: the vocabulary the re-suspension's proof (`Resusp`) is
-- stated in, split out so each case of the induction can live in its own
-- module.
--
--   * `Seg n σ σ′`: what a run from `σ` to `σ′` leaves alone at frontier
--     `n` (below-frontier memory, the frame, the stack frontier) and that
--     the heap frontier only grows. Segments compose.
--   * `RRuns′`: `Resusp.RRuns` with the segment in place of the three
--     frontier fields — STRONGER, because it also says the stack frontier
--     comes back unchanged, which the induction needs (a product's second
--     component is run after the first, at `next-slot ≡ 0` again).
--   * the transports of a forced layer (`lay-tr`) and the cell lemmas that
--     turn "Output held it, and it was stored there" into a `CellAt`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Base (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.NuForce o tbl
open import Once.CCC.Codegen.IRToTrace o using (resuspend-layer)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Code; SV-Ptr; SV-Tag; sucLoc; writeReg-preserves; writeReg-same
        ; store-at-slot; restore-input; load-from-slot; load-indirect; load-indirect-suc; store-indirect
        ; store-indirect-suc; mov-to-input; instr-alloc-heap; instr-load-code-addr; instr-load-tag-lit; sv-as-loc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-K; wf-Id; wf-Sum; wf-Prod)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
import Once.CCC.Machine.ValueRel as CWF
open import Once.CCC.Machine.SMPrimitives using (module RecSchemeSemantics; nhw-store-at-slot; nhw-restore-input)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ)
open import Data.List.Properties using (++-identityʳ)
open import Once.CCC.Machine.FlatLog using (LogFree)
open import Data.Nat using (z≤n)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)

module ResuspBaseC {FS : FrameSemantics} where

  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix)
  open Resolve {FS} using (NoLabel)

  open Core {FS}
  open Mach {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)
  open NuForceC {FS} using (module AnaDen)
  open CWF.ClosureWellFormedBase {FS}
    using (CellAtP; fo-base; pair-wf; inl-wf; inr-wf; inl-reg-wf; inr-reg-wf; transport-SumTag; SumTag; SumV)
  open RecSchemeSemantics {FS} using (exec-abstract-restore-input-sets-input)

  ------------------------------------------------------------------------
  -- ONE STRAIGHT STEP, and what it does to the registers, the slots and the
  -- heap. Stated over the structured machine (`exec-abstract i s a`), which
  -- is what `flat-step-straight` threads.
  ------------------------------------------------------------------------
  St : AbstractInstr → FlatState → FlatState
  St = flat-step-straight

  X : AbstractInstr → LocState FS → AllocState {FS} → LocState FS
  X i s a = proj₁ (exec-abstract i s a)

  -- registers
  reg-store : ∀ k s a r → readReg (regs (X (store-at-slot k) s a)) r ≡ readReg (regs s) r
  reg-store k s a r = cong (λ q → readReg q r) (SMCore.MemOps.writeLoc-regs s (AtStack (current-frame a) k) (readReg (regs s) Output))

  in-alloc : ∀ m s a → readReg (regs (X (instr-alloc-heap m) s a)) Input1 ≡ readReg (regs s) Input1
  in-alloc m s a = writeReg-preserves (regs s) Output Input1 (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (next-heap-ref a)) 0))) (λ ())

  out-alloc : ∀ m s a → readReg (regs (X (instr-alloc-heap m) s a)) Output
            ≡ SV-Ptr (AtDynamic (heap-loc (mkHeapRef (next-heap-ref a)) 0))
  out-alloc m s a = writeReg-same (regs s) Output (SV-Ptr (AtDynamic (heap-loc (mkHeapRef (next-heap-ref a)) 0)))

  in-restore : ∀ k s a v → readLoc s (AtStack (current-frame a) k) ≡ just v
             → readReg (regs (X (restore-input k) s a)) Input1 ≡ v
  in-restore k s a v r = exec-abstract-restore-input-sets-input k s a v r

  out-restore : ∀ k s a v → readLoc s (AtStack (current-frame a) k) ≡ just v
              → readReg (regs (X (restore-input k) s a)) Output ≡ readReg (regs s) Output
  out-restore k s a v r with readLoc s (AtStack (current-frame a) k) | r
  ... | .(just v) | refl = writeReg-preserves (regs s) Input1 Output v (λ ())

  out-lind : ∀ s a loc v → readReg (regs s) Input1 ≡ SV-Ptr loc → readLoc s loc ≡ just v
           → readReg (regs (X load-indirect s a)) Output ≡ v
  out-lind s a loc v e r = exec-abstract-load-indirect-output s a loc v e r

  out-lind-suc : ∀ s a loc v → readReg (regs s) Input1 ≡ SV-Ptr loc → readLoc s (sucLoc loc) ≡ just v
               → readReg (regs (X load-indirect-suc s a)) Output ≡ v
  out-lind-suc s a loc v e r = exec-abstract-load-indirect-suc-output s a loc v e r

  out-lslot : ∀ k s a v → readLoc s (AtStack (current-frame a) k) ≡ just v
            → readReg (regs (X (load-from-slot k) s a)) Output ≡ v
  out-lslot k s a v r = load-slot-result k s a v r

  in-lslot : ∀ k s a v → readLoc s (AtStack (current-frame a) k) ≡ just v
           → readReg (regs (X (load-from-slot k) s a)) Input1 ≡ readReg (regs s) Input1
  in-lslot k s a v r = load-slot-preserves-input k s a v r

  in-sind : ∀ s a loc → sv-as-loc (readReg (regs s) Input1) ≡ just loc
          → readReg (regs (X store-indirect s a)) Input1 ≡ readReg (regs s) Input1
  in-sind s a loc e = store-ind-preserves-input s a loc e

  in-sind-suc : ∀ s a loc → sv-as-loc (readReg (regs s) Input1) ≡ just loc
              → readReg (regs (X store-indirect-suc s a)) Input1 ≡ readReg (regs s) Input1
  in-sind-suc s a loc e with sv-as-loc (readReg (regs s) Input1) | e
  ... | .(just loc) | refl =
    cong (λ r → readReg r Input1) (SMCore.MemOps.writeLoc-regs s (sucLoc loc) (readReg (regs s) Output))

  in-movin : ∀ s a → readReg (regs (X mov-to-input s a)) Input1 ≡ readReg (regs s) Output
  in-movin s a = writeReg-same (regs s) Input1 (readReg (regs s) Output)

  in-code : ∀ lb s a → readReg (regs (X (instr-load-code-addr lb) s a)) Input1 ≡ readReg (regs s) Input1
  in-code lb s a = writeReg-preserves (regs s) Output Input1 (SV-Code lb) (λ ())

  out-code : ∀ lb s a → readReg (regs (X (instr-load-code-addr lb) s a)) Output ≡ SV-Code lb
  out-code lb s a = writeReg-same (regs s) Output (SV-Code lb)

  in-tag : ∀ t s a → readReg (regs (X (instr-load-tag-lit t) s a)) Input1 ≡ readReg (regs s) Input1
  in-tag t s a = writeReg-preserves (regs s) Output Input1 (SV-Tag t) (λ ())

  out-tag : ∀ t s a → readReg (regs (X (instr-load-tag-lit t) s a)) Output ≡ SV-Tag t
  out-tag t s a = writeReg-same (regs s) Output (SV-Tag t)

  -- slots, read at a frame `f` the run never leaves
  slot-idx : ValueLocation FS → ℕ
  slot-idx (AtStack _ k) = k
  slot-idx (AtDynamic _) = 0

  sl-same : ∀ k s a f → current-frame a ≡ f
          → readLoc (X (store-at-slot k) s a) (AtStack f k) ≡ just (readReg (regs s) Output)
  sl-same k s a f refl = SMCore.MemOps.writeLoc-read-same-stack s (current-frame a) k (readReg (regs s) Output)

  sl-other : ∀ k j s a f → j ≢ k
           → readLoc (X (store-at-slot k) s a) (AtStack f j) ≡ readLoc s (AtStack f j)
  sl-other k j s a f j≢k =
    SMCore.MemOps.writeLoc-preserves-other s (AtStack (current-frame a) k) (AtStack f j) (readReg (regs s) Output) (λ eq → j≢k (sym (cong slot-idx eq)))

  sl-keep : ∀ i s a f j → InstrNoHeapWrite i → instr-writes-slot i ≡ nothing
          → readLoc (X i s a) (AtStack f j) ≡ readLoc s (AtStack f j)
  sl-keep i s a f j nhw nws = exec-abstract-preserves-stack-slot i s a f j nhw nws

  sl-sind : ∀ s a hl f j → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
          → readLoc (X store-indirect s a) (AtStack f j) ≡ readLoc s (AtStack f j)
  sl-sind s a hl f j e = store-ind-preserves-slot s a hl j e

  sl-sind-suc : ∀ s a hl f j → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
              → readLoc (X store-indirect-suc s a) (AtStack f j) ≡ readLoc s (AtStack f j)
  sl-sind-suc s a hl f j e = store-ind-suc-preserves-slot s a hl j e

  -- a slot fact at the run's frame, re-read at the step's own frame
  at-cf : ∀ (s : LocState FS) (a : AllocState {FS}) {f k v} → current-frame a ≡ f
        → readLoc s (AtStack f k) ≡ just v → readLoc s (AtStack (current-frame a) k) ≡ just v
  at-cf s a refl r = r

  -- heap cells
  hp-keep : ∀ i s a hl → InstrNoHeapWrite i → readLoc (X i s a) (AtDynamic hl) ≡ readLoc s (AtDynamic hl)
  hp-keep i s a hl nhw = heap-untouched i s a hl nhw

  hp-sind-other : ∀ s a hl hl′ → sv-as-loc (readReg (regs s) Input1) ≡ just (AtDynamic hl)
                → AtDynamic {FS} hl ≢ AtDynamic hl′
                → readLoc (X store-indirect s a) (AtDynamic hl′) ≡ readLoc s (AtDynamic hl′)
  hp-sind-other s a hl hl′ e ne with sv-as-loc (readReg (regs s) Input1) | e
  ... | .(just (AtDynamic hl)) | refl =
    SMCore.MemOps.writeLoc-preserves-other s (AtDynamic hl) (AtDynamic hl′) (readReg (regs s) Output) ne

  ------------------------------------------------------------------------
  -- A SILENT RUN: a chain with its two bookkeeping facts — it emits no
  -- events and leaves the log alone — built one named step at a time, so
  -- neither fact ever evaluates the chain.
  ------------------------------------------------------------------------
  SRun : AbstractTrace → ℕ → FlatState → FlatState → Set
  SRun prog k fs fs′ =
    Σ (FlatSteps prog k fs fs′) (λ r → (chain-events r ≡ []) × (LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs)))

  s-nil : ∀ {prog fs} → SRun prog 0 fs fs
  s-nil {prog} {fs} = [] , chain-events-nil {prog} {fs} , refl

  s-at : ∀ {prog fs k fs″} {i : AbstractInstr} (fs′ : FlatState)
       → (halted (floc fs) ≡ false × fetch prog (fpc fs) ≡ just i)
       → flat-exec-instr i prog fs ≡ fs′
       → event-of i fs ≡ [] → LogFree i
       → SRun prog k fs′ fs″ → SRun prog (suc k) fs fs″
  s-at {prog} {fs} {i = i} fs′ h eq e lf (r , ev , lg) =
    step-at fs′ h eq r
    , trans (cong (event-of i fs ++_) (chain-events-subst-start (sym eq) r)) (trans (cong (_++ chain-events r) e) ev)
    , trans lg (trans (cong (λ z → LocState.ev-log (floc z)) (sym eq))
                      (trans (log-step i lf prog fs) (++-identityʳ (LocState.ev-log (floc fs)))))

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
               (mk-child : ∀ {alloc ν-loc s} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                         → LocMatchesMode Heap ν-loc
                         → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                         → Live alloc (sucLoc ν-loc)
                         → CellAt {prog = prog} alloc (E IRTy′.* A) (e , a′) ν-loc s
                         → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
               where

    rsd = AnaDen.rsd wf coalg e

    rtrace : ∀ {G : IRFunctor} → WellFormedFI G → ℕ → ℕ → AbstractTrace
    rtrace wG n l = proj₂ (proj₂ (resuspend-layer n l (ℓ o lbl-n) 0 wG))

    data OutAt′ {C : IRTy} (alloc : AllocState {FS}) (c : ValueDomain.⟦ C ⟧ᴰᴵ) (st : LocState FS) : Set where
      out-loc  : ∀ {m} (loc : ValueLocation FS) → ValidAtWF {prog = prog} m alloc {C} c loc st → Live alloc loc
               → readReg (regs st) Output ≡ SV-Ptr loc → OutAt′ alloc c st
      out-reg  : (fit : FitsInRegI C) → readReg (regs st) Output ≡ prim-sv fit c → OutAt′ alloc c st
      out-unit : C ≡ IRTy′.Unit → OutAt′ alloc c st

    LV : (G : IRFunctor) → VTy (⟦ G ⟧TI (ν-type F))
    LV G = LayerV G {ν-type F} R

    -- A RESULT THAT SURVIVES whatever keeps its footprint: the layer is
    -- valid at every later state that keeps live what was live and leaves
    -- the footprint alone.
    data ROut (G : IRFunctor) (m : AllocMode) (b : AllocState {FS}) (h : ℕ) (a : AllocState {FS})
              (s : LocState FS) (v : ValueDomain.⟦ ⟦ G ⟧TI (ν-type F) ⟧ᴰᴵ) : Set where
      ro-unit : ⟦ G ⟧TI (ν-type F) ≡ IRTy′.Unit → ROut G m b h a s v
      ro-reg  : (fit : FitsInRegI (⟦ G ⟧TI (ν-type F))) → readReg (regs s) Output ≡ prim-sv fit v → ROut G m b h a s v
      ro-loc  : (loc : ValueLocation FS) → Live a loc → readReg (regs s) Output ≡ SV-Ptr loc
              → (∀ {a′ s′} → (∀ l → Live a l → Live a′ l) → (∀ l → Prot b h a l → readLoc s′ l ≡ readLoc s l)
                 → LV G m a′ v loc s′)
              → ROut G m b h a s v

    ro→rp : ∀ {G m b h a s v} → ROut G m b h a s v → ResultPlaceP {⟦ G ⟧TI (ν-type F)} (LV G) m a a v s
    ro→rp (ro-unit u) = rp-unit u
    ro→rp (ro-reg fit rax) = rp-reg fit rax
    ro→rp (ro-loc loc lv rax f) = rp-loc loc (f (λ _ x → x) (λ _ _ → refl)) lv rax (f (λ _ x → x) (λ _ _ → refl)) lv

    -- …and stored at `q`, a cell of a later state
    ro→cell : ∀ {G m b h a s v a′ s′ q} → ROut G m b h a s v
            → (∀ l → Live a l → Live a′ l) → (∀ l → Prot b h a l → readLoc s′ l ≡ readLoc s l)
            → readLoc s′ q ≡ just (readReg (regs s) Output)
            → CellAtP {⟦ G ⟧TI (ν-type F)} (LV G) a′ v q s′
    ro→cell {s = s} (ro-unit u) bft rd eq = cell-inline (rep-unit u (readReg (regs s) Output)) eq
    ro→cell (ro-reg fit rax) bft rd eq = cell-inline (rep-prim fit) (trans eq (cong just rax))
    ro→cell (ro-loc loc lv rax f) bft rd eq = cell-ptr (trans eq (cong just rax)) (bft _ lv) (f bft rd)

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
        left     : LocState.left (floc settle) ≡ LocState.left (floc σ)
        out-mode : AllocMode
        rout     : ROut G out-mode b (next-heap-ref (falloc σ)) (falloc settle) (floc settle) (rsd wG y)
        seg      : Seg n σ settle

    -- THE CASE STATEMENT, one functor at a time. The inputs are valid at a
    -- BASE `b` no later than the start, and the result's footprint is what
    -- is live at `b` plus what the run allocates.
    Resusp′ : ∀ {G : IRFunctor} → WellFormedFI G → Set
    Resusp′ {G} wG =
      ∀ (n l : ℕ) (σ : FlatState) (y : ValueDomain.⟦ ⟦ G ⟧TI A ⟧ᴰᴵ) (pl : ValueLocation FS)
        (b : AllocState {FS}) → next-heap-ref b ≤ next-heap-ref (falloc σ)
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
    -- TRANSPORTS AND CELLS.
    ----------------------------------------------------------------------
    v-tr : ∀ {a a′ s s′} → Kp a s a′ s′ → ∀ {m C} {c : ValueDomain.⟦ C ⟧ᴰᴵ} {loc} → Live a loc
         → ValidAtWF {prog = prog} m a {C} c loc s → ValidAtWF {prog = prog} m a′ {C} c loc s′
    v-tr {a} (bft , rd) {c = c} {loc} q v = validityWF-heap-transport (Live a) (λ _ b → b) rd bft c loc q v

    cell-sv : ∀ {a C c cl st} → CellAt {prog = prog} a C c cl st → StoredValue FS
    cell-sv (cell-ptr {comp-loc = cl′} _ _ _) = SV-Ptr cl′
    cell-sv (cell-inline {c = c} rep _)       = inline-sv rep c

    cell-read : ∀ {a C c cl st} (ce : CellAt {prog = prog} a C c cl st) → readLoc st cl ≡ just (cell-sv ce)
    cell-read (cell-ptr r _ _)    = r
    cell-read (cell-inline rep r) = r

    -- a cell copied verbatim to `q`
    cell-copy : ∀ {a s a′ s′ C c cl q} → Kp a s a′ s′ → readLoc s′ q ≡ readLoc s cl
              → CellAt {prog = prog} a C c cl s → CellAt {prog = prog} a′ C c q s′
    cell-copy k@(bft , rd) eq (cell-ptr r bf v) = cell-ptr (trans eq r) (bft _ bf) (v-tr k bf v)
    cell-copy k eq (cell-inline rep r) = cell-inline rep (trans eq r)

    -- a cell, loaded into Output
    cell→out : ∀ {a s a′ s′ C c cl} → Kp a s a′ s′ → (ce : CellAt {prog = prog} a C c cl s)
             → readReg (regs s′) Output ≡ cell-sv ce → OutAt′ {C} a′ c s′
    cell→out k@(bft , rd) (cell-ptr {comp-loc = cl′} r bf v) o = out-loc cl′ (v-tr k bf v) (bft _ bf) o
    cell→out k (cell-inline (rep-prim fit) r) o = out-reg fit o
    cell→out k (cell-inline (rep-unit eq _) r) o = out-unit eq

    -- what was in Output, stored at `q`
    out→cell : ∀ {a s a′ s′ C c q} → Kp a s a′ s′ → OutAt′ {C} a c s
             → readLoc s′ q ≡ just (readReg (regs s) Output) → CellAt {prog = prog} a′ C c q s′
    out→cell k@(bft , rd) (out-loc loc v bf rax) eq = cell-ptr (trans eq (cong just rax)) (bft _ bf) (v-tr k bf v)
    out→cell k (out-reg fit rax) eq = cell-inline (rep-prim fit) (trans eq (cong just rax))
    out→cell {s = s} k (out-unit u) eq = cell-inline (rep-unit u (readReg (regs s) Output)) eq

    -- a sum node from its payload cell
    cell→inl : ∀ {G₁ G₂ : IRFunctor} {a v loc s} → CellAtP {⟦ G₁ ⟧TI (ν-type F)} (LV G₁) a v (sucLoc loc) s
             → LocMatchesMode Heap loc → SumTag Heap 0 s loc → Live a (sucLoc loc)
             → SumV {⟦ G₁ ⟧TI (ν-type F)} {⟦ G₂ ⟧TI (ν-type F)} (LV G₁) (LV G₂) Heap a (inj₁ v) loc s
    cell→inl (cell-ptr r bf v) lmm tg slb = inl-wf lmm tg r bf slb v
    cell→inl (cell-inline rep r) lmm tg slb = inl-reg-wf lmm tg rep r slb

    cell→inr : ∀ {G₁ G₂ : IRFunctor} {a v loc s} → CellAtP {⟦ G₂ ⟧TI (ν-type F)} (LV G₂) a v (sucLoc loc) s
             → LocMatchesMode Heap loc → SumTag Heap 1 s loc → Live a (sucLoc loc)
             → SumV {⟦ G₁ ⟧TI (ν-type F)} {⟦ G₂ ⟧TI (ν-type F)} (LV G₁) (LV G₂) Heap a (inj₂ v) loc s
    cell→inr (cell-ptr r bf v) lmm tg slb = inr-wf lmm tg r bf slb v
    cell→inr (cell-inline rep r) lmm tg slb = inr-reg-wf lmm tg rep r slb

    -- the inputs, carried along a segment at the same base
    kp-base : ∀ {b a₀ n fs fs′} → (∀ l → Live b l → Live a₀ l) → SegA a₀ n fs fs′ → Kp b (floc fs) b (floc fs′)
    kp-base bl p = (λ _ x → x) , (λ l x → seg-live-read p l (bl l x))
