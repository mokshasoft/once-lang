-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair.Chain
--
-- D207: `⟨ f , g ⟩`, built top-down — the KEYSTONE first.
--
-- `pair` is the only clause that reads memory back across a sub-run:
--
--   mov-to-output ∷ store-at-slot backup ∷
--   ft ++ store-at-slot fst ∷ restore-input backup ∷
--   gt ++ <nine-instruction heap pair build>
--
-- `restore-input backup` hands `g` the SAME input `f` was given. That is
-- meaningful only if `f`'s run left slot `backup` alone, and establishing
-- exactly that is what D202 (pass the IHs), D204 (say what a run preserves)
-- and D206 (say it about the right frontier) were for. This module proves it.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Chain (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore using (AllocState; LocState; AbstractTrace; StoredValue; mov-to-output; store-at-slot; readReg; Input1; writeReg-preserves; Output; restore-input; instr-alloc-heap; mov-to-input; load-from-slot; store-indirect; store-indirect-suc; sv-as-loc; AbstractInstr; module LocState; module AllocState)
open AllocState using (current-frame; saved-frames; next-slot; next-heap-ref)
open LocState using (halted; regs)
open import Once.IRTy using (IRTy)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in)
open import Once.CCC.Label using (module LabelId)
open LabelId using (idx)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Nat using (s≤s)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Build o tbl using (module PairBuildC)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (put)
import Once.CCC.Machine.FlatPut as FlatPut
open import Data.Nat using (_⊔_)
open import Once.IRTy using () renaming (_*_ to _*ᵀ_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.ValueDomain as ValueDomain
import Once.IR.Semantics.Trace as TM
open import Once.Denotation.Approx using (done; NotCut)
open import Once.Res using (returns; is-stopped)

module PairC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  module PBC = PairBuildC {FS}
  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix)
  open Resolve {FS} using (found-in-window; noLabel-outside; NoLabel)

  ----------------------------------------------------------------------
  -- THE KEYSTONE: the backup slot survives `f`'s run.
  --
  -- Stated over an ARBITRARY settled state reached by a fragment emitted at
  -- `f-start`, which is what the induction hypothesis hands over. `backup`
  -- is `n`, four below `f-start`, so it is inside the window
  -- `mem-pres` now promises — and was NOT inside the window the first two
  -- attempts promised, which is the whole point of D205/D206.
  ----------------------------------------------------------------------
  backup-survives :
    ∀ {A B} (f : IR A B) (n : ℕ) (alloc : AllocState {FS})
      (s : LocState FS) (settle : LocState FS)
    → (∀ (loc : ValueLocation FS)
       → BeforeFrontier (record alloc { next-slot = suc (suc (suc (suc n))) }) loc
       → SMCore.MemOps.readLoc settle loc ≡ SMCore.MemOps.readLoc s loc)
    → SMCore.MemOps.readLoc settle (AtStack (current-frame alloc) n)
      ≡ SMCore.MemOps.readLoc s (AtStack (current-frame alloc) n)
  backup-survives f n alloc s settle mp =
    mp (AtStack (current-frame alloc) n)
       (BeforeFrontier.stack-before refl n<f-start)
    where
      -- `backup = n`, `f-start = n + 4`: the slot is strictly inside the
      -- window, with the three other stashes (`fst`, `snd`, `pair`) between.
      n<f-start : n < suc (suc (suc (suc n)))
      n<f-start = s≤s (≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (n≤1+n (suc (suc n)))))

  ----------------------------------------------------------------------
  -- The run, up to the restore.
  ----------------------------------------------------------------------
  module PairRun
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    where

    backup fst-stash snd-stash pair-stash f-start : ℕ
    backup     = n
    fst-stash  = suc n
    snd-stash  = suc (suc n)
    pair-stash = suc (suc (suc n))
    f-start    = suc (suc (suc (suc n)))

    -- the two prologue rows: `Output := Input1`, then stash it
    p1 p2 : FlatState
    p1 = flat-exec-instr mov-to-output          prog (entry-flat base s alloc cl rs)
    p2 = flat-exec-instr (store-at-slot backup) prog p1

    -- Neither row touches the allocator, so the frontier `f` starts from is
    -- the caller's.
    alloc-p2 : falloc p2 ≡ alloc
    alloc-p2 = refl

    -- `Input1` is untouched by both rows (one writes Output, the other
    -- memory), which is why `f` can be handed the caller's own input
    -- residence unchanged.
    input1-p2 : readReg (regs (floc p2)) Input1 ≡ readReg (regs s) Input1
    -- `store-at-slot` is a `writeLoc`, which leaves the registers alone, and
    -- `mov-to-output` writes Output — so `Input1` comes through both rows.
    input1-p2 = writeReg-preserves (regs s) Output Input1
                  (readReg (regs s) Input1) (λ ())

    -- What the prologue WROTE: slot `backup` now holds the input, and that is
    -- what `restore-input backup` will read back after `f` has run.
    backup-written : SMCore.MemOps.readLoc (floc p2) (AtStack (current-frame alloc) backup)
                   ≡ just (readReg (regs (floc p1)) Output)
    backup-written =
      SMCore.MemOps.writeLoc-read-same-stack (floc p1) (current-frame alloc) backup
        (readReg (regs (floc p1)) Output)

    ------------------------------------------------------------------------
    -- THE PAYOFF. Composing the two: slot `backup` holds the input after the
    -- prologue (`backup-written`), and `f`'s run leaves it alone
    -- (`backup-survives`, which is `mem-pres` at a slot four below `f`'s
    -- frontier) — so `restore-input backup` hands `g` exactly what `f` got.
    --
    -- This is the whole content of D202/D204/D206 discharged in one `trans`.
    -- Before those, none of the three facts this needs could even be stated:
    -- the IH was not passed, the obligation said nothing about memory, and
    -- then it said it about the caller's frontier instead of `f`'s.
    ------------------------------------------------------------------------
    restore-ok :
      ∀ (settle : LocState FS)
      → (∀ (loc : ValueLocation FS)
         → BeforeFrontier (record alloc { next-slot = f-start }) loc
         → SMCore.MemOps.readLoc settle loc ≡ SMCore.MemOps.readLoc (floc p2) loc)
      → SMCore.MemOps.readLoc settle (AtStack (current-frame alloc) backup)
        ≡ just (readReg (regs (floc p1)) Output)
    restore-ok settle mp =
      trans (backup-survives f n alloc (floc p2) settle mp) backup-written

  -- D212: `fetch-drop2` DELETED — written for the span splits, never used by
  -- them (0 reachable names in the AST dump).

  -- …and the index shuffle it forces on the span: a fragment `k` steps into
  -- a segment that begins `d` instructions after `base` is at `d + k + base`
  -- in the program, which `SpanAt` wants as `k + (d + base)`.
  span-shift : ∀ (d k b : ℕ) → d + k + b ≡ k + (d + b)
  span-shift d k b =
    trans (cong (_+ b) (+-comm d k)) (+-assoc k d b)

  ----------------------------------------------------------------------
  -- The emitted trace, decomposed. Stated as an EQUATION so the splits can
  -- rewrite by it rather than re-deriving the emitter's `let`.
  ----------------------------------------------------------------------
  module PairShape {A B C : IRTy} (f : IR A B) (g : IR A C) (n l : ℕ) where

    backup fst-stash snd-stash pair-stash f-start : ℕ
    backup     = n
    fst-stash  = suc n
    snd-stash  = suc (suc n)
    pair-stash = suc (suc (suc n))
    f-start    = suc (suc (suc (suc n)))

    ft : AbstractTrace
    ft = emitted f-start l f

    n1 l1 : ℕ
    n1 = proj₁ (ir-to-trace' f-start l f)
    l1 = proj₁ (proj₂ (ir-to-trace' f-start l f))

    gt : AbstractTrace
    gt = emitted n1 l1 g

    pre mid tail : AbstractTrace
    pre  = mov-to-output ∷ store-at-slot backup ∷ []
    mid  = store-at-slot fst-stash ∷ restore-input backup ∷ []
    -- plan 0.123 B.4 α: the block, both components put into it (`Pair.Build`)
    tail = instr-alloc-heap (2 ⊔ size (B *ᵀ C)) ∷
           store-at-slot pair-stash ∷
           (put B fst-stash pair-stash 0 ++
            put C snd-stash pair-stash (size B) ++
            load-from-slot pair-stash ∷ [])

    -- THE DECOMPOSITION. `refl`: this is the emitter's own `let`, spelled out.
    -- (`store-at-slot snd-stash` heads the tail in the emitter; it is written
    -- here as the last element of `gt`'s segment boundary — see `shape`.)
    shape : emitted n l ⟨ f , g ⟩
          ≡ pre ++ ft ++ mid ++ gt ++ (store-at-slot snd-stash ∷ tail)
    shape = refl

    -- `f`'s span: strip the two-instruction prologue, then `f`'s own trace is
    -- a PREFIX of everything that follows it.
    span-f : ∀ (prog : AbstractTrace) (base : ℕ)
           → SpanAt prog base (emitted n l ⟨ f , g ⟩)
           → SpanAt prog (suc (suc base)) ft
    span-f prog base span k i eq =
      subst (λ m → fetch prog m ≡ just i) (span-shift 2 k base)
            (span (suc (suc k)) i
              (fetch-++-left ft (mid ++ gt ++ (store-at-slot snd-stash ∷ tail)) k i eq))

    -- The index re-association `g`'s split needs. `span` is applied at
    -- `2 + (length ft + (2 + k))`; `SpanAt` wants `k + (2 + (length ft + (2 +
    -- base)))`. The `k` travels out through one more `+` than `span-f`'s does,
    -- so this is its own equation rather than another `span-shift`.
    g-shift : ∀ (base k : ℕ)
            → suc (suc (length ft + suc (suc k))) + base
              ≡ k + suc (suc (length ft + suc (suc base)))
    g-shift base k = solve-it (length ft) base k
      where
        -- Pure `+` arithmetic; the hand-written `trans` chain was an
        -- off-by-one factory, so it is discharged by the ring solver.
        solve-it : ∀ (a b c : ℕ)
                 → suc (suc (a + suc (suc c))) + b
                   ≡ c + suc (suc (a + suc (suc b)))
        solve-it a b c = solve 3 (λ x y z →
            con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ z)))) :+ y
          , z :+ (con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ y))))))
          refl a b c

    -- `g`'s span: past the prologue, `f`'s trace and the two mid rows. The
    -- offset is `2 + length ft + 2`, and the index shuffle is the same one,
    -- applied at that depth.
    -- plan 0.88: the LABEL channel, at the same two offsets. `f` resolves its
    -- own labels in a prefix (`label-prefix`); `g`'s sit past `ft` and the two
    -- mid rows, so the scan skips `ft` — which needs `NoLabel`, and that is the
    -- window argument: a label `gt` resolves is at or above `l1`, and every
    -- label of `ft` is below it.
    labels-f : ∀ (prog : AbstractTrace) (base : ℕ)
             → LabelsAt prog base (emitted n l ⟨ f , g ⟩)
             → LabelsAt prog (suc (suc base)) ft
    labels-f prog base la m j eq =
      subst (λ z → find-label prog m ≡ just z) (+-assoc j 2 base)
            (la m (j + 2) scan)
      where
        scan : find-label (emitted n l ⟨ f , g ⟩) m ≡ just (j + 2)
        scan = fl-go-prefix ft (mid ++ gt ++ (store-at-slot snd-stash ∷ tail)) m 2 (j + 2)
                 (trans (fl-go-shift ft m 2 0) (cong (mmap (_+ 2)) eq))

    labels-g : ∀ (prog : AbstractTrace) (base : ℕ)
             → LabelsAt prog base (emitted n l ⟨ f , g ⟩)
             → LabelsAt prog (suc (suc (length ft + suc (suc base)))) gt
    labels-g prog base la m j eq =
      subst (λ z → find-label prog m ≡ just z) arith (la m (j + gbase) scan)
      where
        gbase : ℕ
        gbase = suc (suc (2 + length ft))

        post : AbstractTrace
        post = store-at-slot snd-stash ∷ tail

        inW : l1 ≤ idx m
        inW = proj₁ (found-in-window gt m j eq (labels-in g n1 l1))

        noF : NoLabel m ft
        noF = noLabel-outside m ft (labels-in f f-start l)
                (λ w → 1+n≰n (≤-trans (proj₂ w) inW))

        scan : find-label (emitted n l ⟨ f , g ⟩) m ≡ just (j + gbase)
        scan = trans (fl-go-skip ft (mid ++ gt ++ post) m 2 noF)
                     (fl-go-prefix gt post m gbase (j + gbase)
                        (trans (fl-go-shift gt m gbase 0) (cong (mmap (_+ gbase)) eq)))

        arith : (j + gbase) + base ≡ j + suc (suc (length ft + suc (suc base)))
        arith = trans (+-assoc j gbase base)
                      (cong (j +_) (cong (λ z → suc (suc z))
                        (trans (cong suc (sym (+-suc (length ft) base)))
                               (sym (+-suc (length ft) (suc base))))))

    span-g : ∀ (prog : AbstractTrace) (base : ℕ)
           → SpanAt prog base (emitted n l ⟨ f , g ⟩)
           → SpanAt prog (suc (suc (length ft + suc (suc base)))) gt
    span-g prog base span k i eq =
      subst (λ m → fetch prog m ≡ just i)
            (g-shift base k)
            (span (suc (suc (length ft + suc (suc k)))) i
              (trans (cong (fetch (ft ++ mid ++ gt ++ (store-at-slot snd-stash ∷ tail)))
                           refl)
                     (trans (fetch-++-right ft
                               (mid ++ gt ++ (store-at-slot snd-stash ∷ tail))
                               (suc (suc k)))
                            (fetch-++-left gt (store-at-slot snd-stash ∷ tail) k i eq))))

  ----------------------------------------------------------------------
  -- `PairTrace`: the pair's events split by its segments. Here, beside
  -- `PairChainG.RUN`, so `RUN-events` is stated over RUN's own pieces
  -- (plan 0.144's `context-form-mismatch` pattern).
  ----------------------------------------------------------------------
  module PairTrace where
    open import Data.List.Properties using (++-identityʳ)

    pair-chain-events :
      ∀ {prog : AbstractTrace} {kP kF kM kG kT : ℕ}
        {e0 s1 s2 s3 s4 : FlatState}
        (preS  : FlatSteps prog kP e0 s1)
        (cF    : FlatSteps prog kF s1 s2)
        (midS  : FlatSteps prog kM s2 s3)
        (cG    : FlatSteps prog kG s3 s4)
        {s5 : FlatState}
        (tailS : FlatSteps prog kT s4 s5)
      → chain-events preS  ≡ []
      → chain-events midS  ≡ []
      → chain-events tailS ≡ []
      → chain-events (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS (FlatSteps-++ cG tailS))))
        ≡ chain-events cF ++ chain-events cG
    pair-chain-events preS cF midS cG tailS pre[] mid[] tail[] =
      trans (chain-events-++ preS after-pre)
            (trans (cong (_++ chain-events after-pre) pre[]) ev-after-pre)
      where
        after-g = FlatSteps-++ cG tailS

        ev-after-g : chain-events after-g ≡ chain-events cG
        ev-after-g =
          trans (chain-events-++ cG tailS)
                (trans (cong (chain-events cG ++_) tail[])
                       (++-identityʳ (chain-events cG)))

        after-f = FlatSteps-++ midS after-g

        ev-after-f : chain-events after-f ≡ chain-events cG
        ev-after-f =
          trans (chain-events-++ midS after-g)
                (trans (cong (_++ chain-events after-g) mid[]) ev-after-g)

        after-pre = FlatSteps-++ cF after-f

        ev-after-pre : chain-events after-pre ≡ chain-events cF ++ chain-events cG
        ev-after-pre =
          trans (chain-events-++ cF after-f)
                (cong (chain-events cF ++_) ev-after-f)

    -- The two shorter runs: `g` stopped (no tail), `f` stopped (no mid, no `g`).
    pair-chain-events-g :
      ∀ {prog : AbstractTrace} {kP kF kM kG : ℕ} {e0 s1 s2 s3 s4 : FlatState}
        (preS : FlatSteps prog kP e0 s1) (cF : FlatSteps prog kF s1 s2)
        (midS : FlatSteps prog kM s2 s3) (cG : FlatSteps prog kG s3 s4)
      → chain-events preS ≡ [] → chain-events midS ≡ []
      → chain-events (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG)))
        ≡ chain-events cF ++ chain-events cG
    pair-chain-events-g preS cF midS cG pre[] mid[] =
      trans (chain-events-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG)))
      (trans (cong (_++ chain-events (FlatSteps-++ cF (FlatSteps-++ midS cG))) pre[])
      (trans (chain-events-++ cF (FlatSteps-++ midS cG))
             (cong (chain-events cF ++_)
                   (trans (chain-events-++ midS cG) (cong (_++ chain-events cG) mid[])))))

    pair-chain-events-f :
      ∀ {prog : AbstractTrace} {kP kF : ℕ} {e0 s1 s2 : FlatState}
        (preS : FlatSteps prog kP e0 s1) (cF : FlatSteps prog kF s1 s2)
      → chain-events preS ≡ []
      → chain-events (FlatSteps-++ preS cF) ≡ chain-events cF
    pair-chain-events-f preS cF pre[] =
      trans (chain-events-++ preS cF) (cong (_++ chain-events cF) pre[])

  ----------------------------------------------------------------------
  -- CLUSTER `PairChain`: THE RUN.
  --
  -- The step chain for `⟨ f , g ⟩` and the seven scalar/state fields of
  -- `ValueRealized` that are about the run rather than about the value:
  -- `steps`, `settle`, `run`, `live`, `at-end`, `no-ret`, `no-link`.
  --
  --   pre(2) ++ f's chain ++ mid(2) ++ g's chain ++ snd-store(1) ++ tail(8)
  --
  -- The two sub-IR chains arrive as `ValueRealized` records (the caller
  -- applies `ihf`/`ihg`); everything else is this module's work. Each sub-run
  -- starts at an `entry-flat`, NOT at the state the previous segment reached,
  -- so `handover-eq` is spent TWICE — once at the end of the prologue and once
  -- after `restore-input`.
  --
  -- Nested rather than flat so the states `p2`/`m2` that the two hand-overs
  -- talk about can be NAMED before the records that mention them are taken.
  ----------------------------------------------------------------------
  module PairChain
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩))
    where

    module PS = PairShape f g n l
    module PR = PairRun f g n l prog base s alloc cl rs n≤ nh
    module VR = ValueRealized

    ------------------------------------------------------------------
    -- D158's hand-over, restated locally (it lives inside `CompC`, which
    -- this module does not import). A state with `fpc ≡ b`, `fret ≡ []`
    -- and `flink ≡ nothing` IS an entry state at `b`, by eta on the record.
    ------------------------------------------------------------------
    handover-eq : ∀ (b : ℕ) (fs : FlatState) (rs : List ℕ)
                → fpc fs ≡ b → fret fs ≡ rs → flink fs ≡ nothing
                → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs) rs
    handover-eq b (mkFlatFull lo al pc rt cls lk) _ refl refl refl = refl

    -- the two `+`-shuffles the fetches need (`span` hands out `k + base`,
    -- the machine is at `… + suc (suc base)`).
    shift2 : ∀ (a b : ℕ) → a + suc (suc b) ≡ suc (suc (a + b))
    shift2 a b = trans (+-suc a (suc b)) (cong suc (+-suc a b))

    plus1 : ∀ (a : ℕ) → a + 1 ≡ suc a
    plus1 a = trans (+-suc a 0) (cong suc (+-identityʳ a))

    -- the whole emitted text, spelled out once (`PS.shape` is `refl`, so this
    -- is the same list — it just reads).
    body : AbstractTrace
    body = PS.ft ++ PS.mid ++ PS.gt ++ (store-at-slot PS.snd-stash ∷ PS.tail)

    rest-after-ft : AbstractTrace
    rest-after-ft = PS.mid ++ PS.gt ++ (store-at-slot PS.snd-stash ∷ PS.tail)

    tail-text : AbstractTrace
    tail-text = store-at-slot PS.snd-stash ∷ PS.tail

    -- `length (emitted n l ⟨ f , g ⟩)` decomposed. The two literal segments
    -- (`pre`, `mid`) and the nine-instruction tail contribute definitionally;
    -- only the two sub-traces need `length-++`.
    len-emitted : length (emitted n l ⟨ f , g ⟩)
                ≡ suc (suc (length PS.ft + suc (suc (length PS.gt + length tail-text))))
    len-emitted =
      cong (λ z → suc (suc z))
        (trans (length-++ PS.ft {rest-after-ft})
               (cong (length PS.ft +_)
                     (cong (λ z → suc (suc z))
                           (length-++ PS.gt {tail-text}))))

    ------------------------------------------------------------------
    -- THE PROLOGUE: `Output := Input1`, then stash it at `backup`.
    ------------------------------------------------------------------
    fs0 : FlatState
    fs0 = entry-flat base s alloc cl rs

    nh0 : halted (floc fs0) ≡ false
    nh0 = nh

    nh1 : halted (floc PR.p1) ≡ false
    nh1 = exec-abstract-preserves-halted-WF mov-to-output s alloc nh0 tt

    -- …and `f`'s own `halted ≡ false` precondition, which the caller owes
    -- `ihf` before it can produce `vrf`.
    nh2 : halted (floc PR.p2) ≡ false
    nh2 = exec-abstract-preserves-halted-WF (store-at-slot PS.backup)
            (floc PR.p1) (falloc PR.p1) nh1 tt

    -- `f` is emitted four slots above the caller's frontier, so `ihf`'s
    -- `next-slot alloc ≤ n` premise is the caller's own, weakened.
    n≤f-start : n ≤ PS.f-start
    n≤f-start = ≤-trans (n≤1+n n)
                  (≤-trans (n≤1+n (suc n))
                    (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n))))))

    ns-p2 : next-slot (falloc PR.p2) ≤ PS.f-start
    ns-p2 = ≤-trans n≤ n≤f-start

    pre-chain : FlatSteps prog 2 fs0 PR.p2
    pre-chain = (nh0 , span 0 mov-to-output refl)
              ∷ (nh1 , span 1 (store-at-slot PS.backup) refl)
              ∷ []

    -- …and the prologue's end state is an entry state for `f`, at `2 + base`.
    handF : PR.p2 ≡ entry-flat (suc (suc base))
                      (floc PR.p2) (falloc PR.p2) (fclosure PR.p2) rs
    handF = handover-eq (suc (suc base)) PR.p2 rs refl refl refl


  -- Plan 0.105: `WithF`/`WithG` are SIBLINGS of `PairChain`, not nested in it:
  -- applying a module copies its nested modules too, so nesting made every
  -- `PC`/`PCF` application copy `g`'s whole run again (the 30 s cap).
  ------------------------------------------------------------------
  -- `f`'s run, as the induction hypothesis hands it over.
  ------------------------------------------------------------------
  -- plan 0.97: …AND THE PREMISE THAT `f` REACHED ITS END. Everything in
  -- this module is about what happens AFTER `f`: the two mid rows, `g`'s
  -- entry state, `g`'s run, the tail. None of it happens if `f` ended the
  -- program. Taking the equation as a module parameter is what makes that
  -- structural — the caller cannot instantiate `WithF` without deciding.
  module PairChainF
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩))
    {xf : ValueDomain.⟦ A ⟧ᴰᴵ} {kf : ℕ}
    (vrf : ValueRealized prog (suc (suc base)) (PairShape.f-start f g n l) l f xf
             (floc (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) (falloc (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) (fclosure (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) rs kf)
    {vf : ValueDomain.⟦ B ⟧ᴰᴵ} {rf : ℕ}
    (sfeq : resultAt (floc (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) (⟪ evalᴰ f xf ⟫ kf) ≡ returns (done vf rf))
    where
    open PairChain f g n l prog base s alloc cl rs n≤ nh span


    fsF : FlatState
    fsF = VR.settle vrf

    chainF : FlatSteps prog (VR.steps vrf) PR.p2 fsF
    chainF = subst (λ st → FlatSteps prog (VR.steps vrf) st fsF)
                   (sym handF) (VR.run vrf)

    endF : fpc fsF ≡ length PS.ft + suc (suc base)
    endF = VR.at-end vrf sfeq

    liveF : halted (floc fsF) ≡ false
    liveF = VR.live vrf (cong is-stopped sfeq)

    -- `f` returned, so it was not cut (plan 0.119 D5).
    ncF : NotCut (resultAt (floc (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) (⟪ evalᴰ f xf ⟫ kf))
    ncF = subst NotCut (sym sfeq) tt

    -- `falloc PR.p2` IS `alloc` (`PairRun.alloc-p2`), so `f`'s frame
    -- equation is already the caller's.
    cf-fsF : current-frame (falloc fsF) ≡ current-frame alloc
    cf-fsF = VR.frame-pres vrf sfeq

    ------------------------------------------------------------------
    -- THE MID ROWS: stash `f`'s result at `fst-stash`, then put the
    -- caller's own input back in `Input1` from `backup`.
    ------------------------------------------------------------------
    m1 m2 : FlatState
    m1 = flat-exec-instr (store-at-slot PS.fst-stash) prog fsF
    m2 = flat-exec-instr (restore-input PS.backup)    prog m1

    -- their two fetches, read off the span at `2 + length ft` and
    -- `3 + length ft`.
    in-mid0 : fetch (emitted n l ⟨ f , g ⟩) (suc (suc (length PS.ft)))
            ≡ just (store-at-slot PS.fst-stash)
    in-mid0 = trans (cong (fetch body) (sym (+-identityʳ (length PS.ft))))
                    (fetch-++-right PS.ft rest-after-ft 0)

    in-mid1 : fetch (emitted n l ⟨ f , g ⟩) (suc (suc (suc (length PS.ft))))
            ≡ just (restore-input PS.backup)
    in-mid1 = trans (cong (fetch body) (sym (plus1 (length PS.ft))))
                    (fetch-++-right PS.ft rest-after-ft 1)

    mid0-fetch : fetch prog (fpc fsF) ≡ just (store-at-slot PS.fst-stash)
    mid0-fetch =
      subst (λ m → fetch prog m ≡ just (store-at-slot PS.fst-stash))
            (trans (sym (shift2 (length PS.ft) base)) (sym endF))
            (span (suc (suc (length PS.ft))) (store-at-slot PS.fst-stash) in-mid0)

    mid1-fetch : fetch prog (fpc m1) ≡ just (restore-input PS.backup)
    mid1-fetch =
      subst (λ m → fetch prog m ≡ just (restore-input PS.backup))
            (cong suc (trans (sym (shift2 (length PS.ft) base)) (sym endF)))
            (span (suc (suc (suc (length PS.ft)))) (restore-input PS.backup) in-mid1)

    nhM1 : halted (floc m1) ≡ false
    nhM1 = exec-abstract-preserves-halted-WF (store-at-slot PS.fst-stash)
             (floc fsF) (falloc fsF) liveF tt

    mid-chain : FlatSteps prog 2 fsF m2
    mid-chain = (liveF , mid0-fetch) ∷ (nhM1 , mid1-fetch) ∷ []

    -- the frame has not moved through either row.
    cf-m1 : current-frame (falloc m1) ≡ current-frame alloc
    cf-m1 =
      trans (exec-abstract-preserves-frame (store-at-slot PS.fst-stash)
               (floc fsF) (falloc fsF))
            cf-fsF

    cf-m2 : current-frame (falloc m2) ≡ current-frame alloc
    cf-m2 =
      trans (exec-abstract-preserves-frame (restore-input PS.backup)
               (floc m1) (falloc m1))
            cf-m1

    ------------------------------------------------------------------
    -- THE KEYSTONE, SPENT. `restore-input backup` does not halt, because
    -- the slot it reads is still the caller's input: `PR.restore-ok` says
    -- `f`'s run left `backup` alone (that IS `vr-mem-pres vrf` at `f`'s
    -- own frontier — D202/D204/D206), and `store-at-slot fst-stash` writes
    -- one slot ABOVE it.
    --
    -- This is the premise `ihg` cannot be applied without: `IRObsCorrectF`
    -- asks for `halted s ≡ false` at `floc m2`.
    ------------------------------------------------------------------
    read-backup-fsF : SMCore.MemOps.readLoc (floc fsF)
                        (AtStack (current-frame alloc) PS.backup)
                      ≡ just (readReg (regs (floc PR.p1)) Output)
    read-backup-fsF = PR.restore-ok (floc fsF) (vr-mem-pres vrf ncF)

    aF : AllocState {FS}
    aF = record alloc { next-slot = PS.fst-stash }

    bf-backup : BeforeFrontier aF (AtStack (current-frame alloc) PS.backup)
    bf-backup = BeforeFrontier.stack-before refl (n<1+n n)

    read-backup-m1 : SMCore.MemOps.readLoc (floc m1)
                       (AtStack (current-frame alloc) PS.backup)
                     ≡ just (readReg (regs (floc PR.p1)) Output)
    read-backup-m1 =
      trans (store-slot-preserves-before PS.fst-stash (floc fsF) aF (falloc fsF)
               (AtStack (current-frame alloc) PS.backup) cf-fsF ≤-refl bf-backup)
            read-backup-fsF

    wf-restore : InstrWF (floc m1) (falloc m1) (restore-input PS.backup)
    wf-restore =
      readReg (regs (floc PR.p1)) Output ,
      subst (λ fr → SMCore.MemOps.readLoc (floc m1) (AtStack fr PS.backup)
                    ≡ just (readReg (regs (floc PR.p1)) Output))
            (sym cf-m1) read-backup-m1

    nhM2 : halted (floc m2) ≡ false
    nhM2 = exec-abstract-preserves-halted-WF (restore-input PS.backup)
             (floc m1) (falloc m1) nhM1 wf-restore

    -- the restore found its slot, so it moved no allocator
    alloc-m2 : falloc m2 ≡ falloc fsF
    alloc-m2 = cong (λ mv → proj₂ (SMCore.AbstractExec.exec-restore-input-with-value {FS} mv (floc m1) (falloc m1)))
                    (proj₂ wf-restore)

    -- `g` is emitted at `2 + length ft + 2 + base`, which is where the
    -- machine now is — so this state is `g`'s entry state.
    bg : ℕ
    bg = suc (suc (length PS.ft + suc (suc base)))

    handG : m2 ≡ entry-flat bg (floc m2) (falloc m2) (fclosure m2) rs
    handG = handover-eq bg m2 rs
              (cong (λ z → suc (suc z)) endF) (VR.no-ret vrf sfeq) (VR.no-link vrf ncF)

    ------------------------------------------------------------------
    -- THE SLOT `fst-stash`, WRITTEN HERE AND READ IN THE TAIL.
    ------------------------------------------------------------------
    fv : StoredValue FS
    fv = readReg (regs (floc fsF)) Output

    read-fst-m1 : SMCore.MemOps.readLoc (floc m1)
                    (AtStack (current-frame (falloc fsF)) PS.fst-stash) ≡ just fv
    read-fst-m1 =
      SMCore.MemOps.writeLoc-read-same-stack (floc fsF)
        (current-frame (falloc fsF)) PS.fst-stash fv

    read-fst-m1' : SMCore.MemOps.readLoc (floc m1)
                     (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
    read-fst-m1' =
      subst (λ fr → SMCore.MemOps.readLoc (floc m1) (AtStack fr PS.fst-stash) ≡ just fv)
            cf-fsF read-fst-m1

    -- `restore-input` writes a REGISTER; the slot comes through.
    read-fst-m2 : SMCore.MemOps.readLoc (floc m2)
                    (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
    read-fst-m2 =
      trans (exec-abstract-preserves-stack-slot (restore-input PS.backup)
               (floc m1) (falloc m1) (current-frame alloc) PS.fst-stash
               Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
            read-fst-m1'


  ------------------------------------------------------------------
  -- `g`'s run.
  ------------------------------------------------------------------
  module PairChainG
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩))
    {xf : ValueDomain.⟦ A ⟧ᴰᴵ} {kf : ℕ}
    (vrf : ValueRealized prog (suc (suc base)) (PairShape.f-start f g n l) l f xf
             (floc (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) (falloc (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) (fclosure (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) rs kf)
    {vf : ValueDomain.⟦ B ⟧ᴰᴵ} {rf : ℕ}
    (sfeq : resultAt (floc (PairRun.p2 f g n l prog base s alloc cl rs n≤ nh)) (⟪ evalᴰ f xf ⟫ kf) ≡ returns (done vf rf))
    {xg : ValueDomain.⟦ A ⟧ᴰᴵ} {kg : ℕ}
    (vrg : ValueRealized prog (PairChainF.bg f g n l prog base s alloc cl rs n≤ nh span vrf sfeq) (PairShape.n1 f g n l) (PairShape.l1 f g n l) g xg
             (floc (PairChainF.m2 f g n l prog base s alloc cl rs n≤ nh span vrf sfeq)) (falloc (PairChainF.m2 f g n l prog base s alloc cl rs n≤ nh span vrf sfeq)) (fclosure (PairChainF.m2 f g n l prog base s alloc cl rs n≤ nh span vrf sfeq)) rs kg)
    {vg : ValueDomain.⟦ C ⟧ᴰᴵ} {rg : ℕ}
    (sgeq : resultAt (floc (PairChainF.m2 f g n l prog base s alloc cl rs n≤ nh span vrf sfeq)) (⟪ evalᴰ g xg ⟫ kg) ≡ returns (done vg rg))
    where
    open PairChain f g n l prog base s alloc cl rs n≤ nh span
    open PairChainF f g n l prog base s alloc cl rs n≤ nh span vrf sfeq


    fsG : FlatState
    fsG = VR.settle vrg

    chainG : FlatSteps prog (VR.steps vrg) m2 fsG
    chainG = subst (λ st → FlatSteps prog (VR.steps vrg) st fsG)
                   (sym handG) (VR.run vrg)

    endG : fpc fsG ≡ length PS.gt + bg
    endG = VR.at-end vrg sgeq

    liveG : halted (floc fsG) ≡ false
    liveG = VR.live vrg (cong is-stopped sgeq)

    -- `g` returned, so it was not cut.
    ncG : NotCut (resultAt (floc m2) (⟪ evalᴰ g xg ⟫ kg))
    ncG = subst NotCut (sym sgeq) tt

    cf-fsG : current-frame (falloc fsG) ≡ current-frame alloc
    cf-fsG = trans (VR.frame-pres vrg sgeq) cf-m2

    -- `fst-stash` is `suc n`, strictly below `f`'s emission frontier
    -- `n + 4 ≤ n1`, so it is inside the window `g`'s run preserves.
    fst<f-start : suc n < PS.f-start
    fst<f-start = s≤s (s≤s (≤-trans (n≤1+n n) (n≤1+n (suc n))))

    fst<n1 : suc n < PS.n1
    fst<n1 = <-≤-trans fst<f-start (frontier-mono f PS.f-start l)

    bf-fst-g : BeforeFrontier (record (falloc m2) { next-slot = PS.n1 })
                 (AtStack (current-frame alloc) PS.fst-stash)
    bf-fst-g = BeforeFrontier.stack-before (sym cf-m2) fst<n1

    read-fst-fsG : SMCore.MemOps.readLoc (floc fsG)
                     (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
    read-fst-fsG =
      trans (VR.stack-pres vrg ncG (current-frame alloc) PS.fst-stash bf-fst-g)
            read-fst-m2
    ----------------------------------------------------------------
    -- THE TAIL'S FETCHES. The nine rows begin at
    -- `2 + length ft + 2 + length gt` in the emitted text, which is
    -- where `g`'s run left the pc.
    ----------------------------------------------------------------
    tail-shift : ∀ (a b k b0 : ℕ)
               → suc (suc (a + suc (suc (b + k)))) + b0
                 ≡ k + (b + suc (suc (a + suc (suc b0))))
    tail-shift a b k b0 = solve 4 (λ x y z w →
        con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ (y :+ z))))) :+ w
      , z :+ (y :+ (con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ w)))))))
      refl a b k b0

    tail-span : ∀ (k : ℕ) (i : AbstractInstr)
              → fetch tail-text k ≡ just i
              → fetch prog (k + (length PS.gt + bg)) ≡ just i
    tail-span k i eq =
      subst (λ m → fetch prog m ≡ just i)
            (tail-shift (length PS.ft) (length PS.gt) k base)
            (span (suc (suc (length PS.ft + suc (suc (length PS.gt + k))))) i
                  (trans (fetch-++-right PS.ft rest-after-ft
                            (suc (suc (length PS.gt + k))))
                         (trans (fetch-++-right PS.gt tail-text k) eq)))

    tfetch : ∀ (k : ℕ) (i : AbstractInstr)
           → fetch tail-text k ≡ just i → fetch prog (k + fpc fsG) ≡ just i
    tfetch k i eq =
      subst (λ m → fetch prog (k + m) ≡ just i) (sym endG) (tail-span k i eq)

    ----------------------------------------------------------------
    -- THE TAIL (`Pair.Build`): `f`'s result, valid where `f` placed it and
    -- kept by `g`'s run, and `g`'s, put into a fresh block.
    ----------------------------------------------------------------
    -- what `f`'s allocator held live, `g`'s run kept (it is heap: the two
    -- mid rows touch the stack and the registers only)
    live-m2 : ∀ l → Live (falloc fsF) l → Live (falloc m2) l
    live-m2 l lv = subst (λ a′ → Live a′ l) (sym alloc-m2) lv

    bftB : ∀ l → Live (falloc fsF) l → Live (falloc fsG) l
    bftB (AtDynamic hl) lv with live-m2 (AtDynamic hl) lv
    ... | BeforeFrontier.heap-before p with VR.bf-mono vrg ncG 0 (AtDynamic hl) (BeforeFrontier.heap-before p)
    ...   | BeforeFrontier.heap-before q = BeforeFrontier.heap-before q

    keepFG : ∀ l → Live (falloc fsF) l → SMCore.MemOps.readLoc (floc fsG) l ≡ SMCore.MemOps.readLoc (floc fsF) l
    keepFG (AtDynamic hl) lv with live-m2 (AtDynamic hl) lv
    ... | BeforeFrontier.heap-before p =
      trans (VR.heap-pres vrg ncG hl (BeforeFrontier.heap-before p))
            (mem-untouched (restore-input PS.backup) (floc m1) (falloc m1) (AtDynamic hl)
               Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)

    bkB : BlocksKept (falloc fsF) (falloc fsG)
    bkB = subst (λ a′ → BlocksKept a′ (falloc fsG)) alloc-m2 (VR.blocks-kept vrg ncG)

    srcB = FlatPut.src-tr {FS} {prog} keepFG (PBC.src-of-place {prog} (VR.place vrf sfeq))
    srcC = PBC.src-of-place {prog} (VR.place vrg sgeq)

    rsB : SMCore.MemOps.readLoc (floc fsG) (AtStack (current-frame (falloc fsG)) (suc n)) ≡ just fv
    rsB = subst (λ fr → SMCore.MemOps.readLoc (floc fsG) (AtStack fr (suc n)) ≡ just fv) (sym cf-fsG) read-fst-fsG

    module T = PBC.Tail {prog} n B C fsG tfetch liveG fv (falloc fsF) bftB bkB srcB rsB srcC

    tail-chain : FlatSteps prog (length tail-text) fsG T.settle
    tail-chain = T.run

    tail-silent : chain-events tail-chain ≡ []
    tail-silent = T.silent

    ----------------------------------------------------------------
    -- ══ THE SEVEN FIELDS ══
    ----------------------------------------------------------------
    STEPS : ℕ
    STEPS = 2 + (VR.steps vrf + (2 + (VR.steps vrg + length tail-text)))

    SETTLE : FlatState
    SETTLE = T.settle

    RUN : FlatSteps prog STEPS (entry-flat base s alloc cl rs) SETTLE
    RUN = FlatSteps-++ pre-chain
            (FlatSteps-++ chainF
              (FlatSteps-++ mid-chain
                (FlatSteps-++ chainG tail-chain)))

    -- plan 0.119 D5: the pair's control steps cover `f`'s and `g`'s.
    RUN-ctrls : chain-ctrls (VR.run vrf) + chain-ctrls (VR.run vrg) ≤ chain-ctrls RUN
    RUN-ctrls =
      subst₂ (λ a b → a + b ≤ chain-ctrls RUN)
             (chain-ctrls-subst-start (sym handF) (VR.run vrf))
             (chain-ctrls-subst-start (sym handG) (VR.run vrg))
             (ctrls-5 pre-chain chainF mid-chain chainG tail-chain)

    -- The pair's events, over RUN's OWN pieces: the straight segments' `[]`s
    -- are decided here, where they are these names (plan 0.144: stated in
    -- `Pair` over `Proof`'s copies of the pieces, this took 1850 s).
    RUN-events : chain-events RUN ≡ chain-events chainF ++ chain-events chainG
    RUN-events = PairTrace.pair-chain-events pre-chain chainF mid-chain chainG tail-chain refl refl tail-silent

    LIVE : halted (floc SETTLE) ≡ false
    LIVE = T.hfin

    at-end-arith : ∀ (a b c b0 : ℕ)
                 → c + (b + suc (suc (a + suc (suc b0))))
                   ≡ suc (suc (a + suc (suc (b + c)))) + b0
    at-end-arith a b c b0 = solve 4 (λ x y z w →
        z :+ (y :+ (con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ w))))))
      , con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ (y :+ z))))) :+ w)
      refl a b c b0

    ATEND : fpc SETTLE ≡ length (emitted n l ⟨ f , g ⟩) + base
    ATEND =
      trans (cong (length tail-text +_) endG)
      (trans (at-end-arith (length PS.ft) (length PS.gt) (length tail-text) base)
             (cong (_+ base) (sym len-emitted)))

    NORET : fret SETTLE ≡ rs
    NORET = VR.no-ret vrg sgeq

    NOLINK : flink SETTLE ≡ nothing
    NOLINK = VR.no-link vrg ncG
