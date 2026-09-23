-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Pair
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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Pair (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in)
open import Once.CCC.Label using (idx)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Nat using (s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module PairC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
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
       → MemOps.readLoc settle loc ≡ MemOps.readLoc s loc)
    → MemOps.readLoc settle (AtStack (current-frame alloc) n)
      ≡ MemOps.readLoc s (AtStack (current-frame alloc) n)
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
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
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
    p1 = flat-exec-instr mov-to-output          prog (entry-flat base s alloc cl)
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
    backup-written : MemOps.readLoc (floc p2) (AtStack (current-frame alloc) backup)
                   ≡ just (readReg (regs (floc p1)) Output)
    backup-written =
      MemOps.writeLoc-read-same-stack (floc p1) (current-frame alloc) backup
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
         → MemOps.readLoc settle loc ≡ MemOps.readLoc (floc p2) loc)
      → MemOps.readLoc settle (AtStack (current-frame alloc) backup)
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
    tail = instr-alloc-heap 2 ∷
           store-at-slot pair-stash ∷
           mov-to-input ∷
           load-from-slot fst-stash ∷
           store-indirect ∷
           load-from-slot snd-stash ∷
           store-indirect-suc ∷
           load-from-slot pair-stash ∷ []

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
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩))
    where

    module PS = PairShape f g n l
    module PR = PairRun f g n l prog base s alloc cl n≤ nh
    module VR = ValueRealized

    ------------------------------------------------------------------
    -- D158's hand-over, restated locally (it lives inside `CompC`, which
    -- this module does not import). A state with `fpc ≡ b`, `fret ≡ []`
    -- and `flink ≡ nothing` IS an entry state at `b`, by eta on the record.
    ------------------------------------------------------------------
    handover-eq : ∀ (b : ℕ) (fs : FlatState)
                → fpc fs ≡ b → fret fs ≡ [] → flink fs ≡ nothing
                → fs ≡ entry-flat b (floc fs) (falloc fs) (fclosure fs)
    handover-eq b (mkFlatFull lo al pc rt cls lk) refl refl refl = refl

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
                ≡ suc (suc (length PS.ft + suc (suc (length PS.gt + 9))))
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
    fs0 = entry-flat base s alloc cl

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
                      (floc PR.p2) (falloc PR.p2) (fclosure PR.p2)
    handF = handover-eq (suc (suc base)) PR.p2 refl refl refl

    ------------------------------------------------------------------
    -- `f`'s run, as the induction hypothesis hands it over.
    ------------------------------------------------------------------
    -- plan 0.97: …AND THE PREMISE THAT `f` REACHED ITS END. Everything in
    -- this module is about what happens AFTER `f`: the two mid rows, `g`'s
    -- entry state, `g`'s run, the tail. None of it happens if `f` ended the
    -- program. Taking the equation as a module parameter is what makes that
    -- structural — the caller cannot instantiate `WithF` without deciding.
    module WithF {xf : DT.⟦ A ⟧ᴰᴵ} {kf : ℕ}
      (vrf : ValueRealized prog (suc (suc base)) PS.f-start l f xf
               (floc PR.p2) (falloc PR.p2) (fclosure PR.p2) kf)
      (sfeq : TM.stoppedT (evalᴰ f xf) kf ≡ false)
      where

      fsF : FlatState
      fsF = VR.settle vrf

      chainF : FlatSteps prog (VR.steps vrf) PR.p2 fsF
      chainF = subst (λ st → FlatSteps prog (VR.steps vrf) st fsF)
                     (sym handF) (VR.run vrf)

      endF : fpc fsF ≡ length PS.ft + suc (suc base)
      endF = VR.at-end vrf sfeq

      liveF : halted (floc fsF) ≡ false
      liveF = VR.live vrf sfeq

      -- `falloc PR.p2` IS `alloc` (`PairRun.alloc-p2`), so `f`'s frame
      -- equation is already the caller's.
      cf-fsF : current-frame (falloc fsF) ≡ current-frame alloc
      cf-fsF = VR.frame-pres vrf

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
      read-backup-fsF : MemOps.readLoc (floc fsF)
                          (AtStack (current-frame alloc) PS.backup)
                        ≡ just (readReg (regs (floc PR.p1)) Output)
      read-backup-fsF = PR.restore-ok (floc fsF) (vr-mem-pres vrf)

      aF : AllocState {FS}
      aF = record alloc { next-slot = PS.fst-stash }

      bf-backup : BeforeFrontier aF (AtStack (current-frame alloc) PS.backup)
      bf-backup = BeforeFrontier.stack-before refl (n<1+n n)

      read-backup-m1 : MemOps.readLoc (floc m1)
                         (AtStack (current-frame alloc) PS.backup)
                       ≡ just (readReg (regs (floc PR.p1)) Output)
      read-backup-m1 =
        trans (store-slot-preserves-before PS.fst-stash (floc fsF) aF (falloc fsF)
                 (AtStack (current-frame alloc) PS.backup) cf-fsF ≤-refl bf-backup)
              read-backup-fsF

      wf-restore : InstrWF (floc m1) (falloc m1) (restore-input PS.backup)
      wf-restore =
        readReg (regs (floc PR.p1)) Output ,
        subst (λ fr → MemOps.readLoc (floc m1) (AtStack fr PS.backup)
                      ≡ just (readReg (regs (floc PR.p1)) Output))
              (sym cf-m1) read-backup-m1

      nhM2 : halted (floc m2) ≡ false
      nhM2 = exec-abstract-preserves-halted-WF (restore-input PS.backup)
               (floc m1) (falloc m1) nhM1 wf-restore

      -- `g` is emitted at `2 + length ft + 2 + base`, which is where the
      -- machine now is — so this state is `g`'s entry state.
      bg : ℕ
      bg = suc (suc (length PS.ft + suc (suc base)))

      handG : m2 ≡ entry-flat bg (floc m2) (falloc m2) (fclosure m2)
      handG = handover-eq bg m2
                (cong (λ z → suc (suc z)) endF) (VR.no-ret vrf) (VR.no-link vrf)

      ------------------------------------------------------------------
      -- THE SLOT `fst-stash`, WRITTEN HERE AND READ IN THE TAIL.
      ------------------------------------------------------------------
      fv : StoredValue FS
      fv = readReg (regs (floc fsF)) Output

      read-fst-m1 : MemOps.readLoc (floc m1)
                      (AtStack (current-frame (falloc fsF)) PS.fst-stash) ≡ just fv
      read-fst-m1 =
        MemOps.writeLoc-read-same-stack (floc fsF)
          (current-frame (falloc fsF)) PS.fst-stash fv

      read-fst-m1' : MemOps.readLoc (floc m1)
                       (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
      read-fst-m1' =
        subst (λ fr → MemOps.readLoc (floc m1) (AtStack fr PS.fst-stash) ≡ just fv)
              cf-fsF read-fst-m1

      -- `restore-input` writes a REGISTER; the slot comes through.
      read-fst-m2 : MemOps.readLoc (floc m2)
                      (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
      read-fst-m2 =
        trans (exec-abstract-preserves-stack-slot (restore-input PS.backup)
                 (floc m1) (falloc m1) (current-frame alloc) PS.fst-stash
                 Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
              read-fst-m1'

      ------------------------------------------------------------------
      -- `g`'s run.
      ------------------------------------------------------------------
      module WithG {xg : DT.⟦ A ⟧ᴰᴵ} {kg : ℕ}
        (vrg : ValueRealized prog bg PS.n1 PS.l1 g xg
                 (floc m2) (falloc m2) (fclosure m2) kg)
        (sgeq : TM.stoppedT (evalᴰ g xg) kg ≡ false)
        where

        fsG : FlatState
        fsG = VR.settle vrg

        chainG : FlatSteps prog (VR.steps vrg) m2 fsG
        chainG = subst (λ st → FlatSteps prog (VR.steps vrg) st fsG)
                       (sym handG) (VR.run vrg)

        endG : fpc fsG ≡ length PS.gt + bg
        endG = VR.at-end vrg sgeq

        liveG : halted (floc fsG) ≡ false
        liveG = VR.live vrg sgeq

        cf-fsG : current-frame (falloc fsG) ≡ current-frame alloc
        cf-fsG = trans (VR.frame-pres vrg) cf-m2

        -- `fst-stash` is `suc n`, strictly below `f`'s emission frontier
        -- `n + 4 ≤ n1`, so it is inside the window `g`'s run preserves.
        fst<f-start : suc n < PS.f-start
        fst<f-start = s≤s (s≤s (≤-trans (n≤1+n n) (n≤1+n (suc n))))

        fst<n1 : suc n < PS.n1
        fst<n1 = <-≤-trans fst<f-start (frontier-mono f PS.f-start l)

        bf-fst-g : BeforeFrontier (record (falloc m2) { next-slot = PS.n1 })
                     (AtStack (current-frame alloc) PS.fst-stash)
        bf-fst-g = BeforeFrontier.stack-before (sym cf-m2) fst<n1

        read-fst-fsG : MemOps.readLoc (floc fsG)
                         (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
        read-fst-fsG =
          trans (VR.stack-pres vrg (current-frame alloc) PS.fst-stash bf-fst-g)
                read-fst-m2

        ----------------------------------------------------------------
        -- THE TAIL: the nine-instruction heap build, at pair's own stashes
        -- (`NineStepPres`'s shape with `n := snd-stash`). Written out with
        -- `flat-step-straight` exactly as that module defines it, so the two
        -- families of states are definitionally the same.
        ----------------------------------------------------------------
        u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : FlatState
        u1  = fsG
        u2  = flat-step-straight (store-at-slot PS.snd-stash)   u1
        u3  = flat-step-straight (instr-alloc-heap 2)           u2
        u4  = flat-step-straight (store-at-slot PS.pair-stash)  u3
        u5  = flat-step-straight mov-to-input                   u4
        u6  = flat-step-straight (load-from-slot PS.fst-stash)  u5
        u7  = flat-step-straight store-indirect                 u6
        u8  = flat-step-straight (load-from-slot PS.snd-stash)  u7
        u9  = flat-step-straight store-indirect-suc             u8
        u10 = flat-step-straight (load-from-slot PS.pair-stash) u9

        -- the pair node, as the bump allocator hands it out at `u3`.
        hl : HeapLocation
        hl = heap-loc (mkHeapRef (next-heap-ref (falloc u2))) 0

        -- the frame, carried forward row by row.
        cf-u2 : current-frame (falloc u2) ≡ current-frame alloc
        cf-u2 = trans (exec-abstract-preserves-frame (store-at-slot PS.snd-stash)
                         (floc u1) (falloc u1)) cf-fsG
        cf-u3 : current-frame (falloc u3) ≡ current-frame alloc
        cf-u3 = trans (exec-abstract-preserves-frame (instr-alloc-heap 2)
                         (floc u2) (falloc u2)) cf-u2
        cf-u4 : current-frame (falloc u4) ≡ current-frame alloc
        cf-u4 = trans (exec-abstract-preserves-frame (store-at-slot PS.pair-stash)
                         (floc u3) (falloc u3)) cf-u3
        cf-u5 : current-frame (falloc u5) ≡ current-frame alloc
        cf-u5 = trans (exec-abstract-preserves-frame mov-to-input
                         (floc u4) (falloc u4)) cf-u4
        cf-u6 : current-frame (falloc u6) ≡ current-frame alloc
        cf-u6 = trans (exec-abstract-preserves-frame (load-from-slot PS.fst-stash)
                         (floc u5) (falloc u5)) cf-u5
        cf-u7 : current-frame (falloc u7) ≡ current-frame alloc
        cf-u7 = trans (exec-abstract-preserves-frame store-indirect
                         (floc u6) (falloc u6)) cf-u6
        cf-u8 : current-frame (falloc u8) ≡ current-frame alloc
        cf-u8 = trans (exec-abstract-preserves-frame (load-from-slot PS.snd-stash)
                         (floc u7) (falloc u7)) cf-u7
        cf-u9 : current-frame (falloc u9) ≡ current-frame alloc
        cf-u9 = trans (exec-abstract-preserves-frame store-indirect-suc
                         (floc u8) (falloc u8)) cf-u8

        -- The two windows the stash reads are measured in. A stash at or
        -- above `n` is NOT before the caller's frontier, so the preservation
        -- lemmas are spent against a frontier raised to the next stash.
        aS aP : AllocState {FS}
        aS = record alloc { next-slot = PS.snd-stash }
        aP = record alloc { next-slot = PS.pair-stash }

        bf-fst-S : BeforeFrontier aS (AtStack (current-frame alloc) PS.fst-stash)
        bf-fst-S = BeforeFrontier.stack-before refl (n<1+n (suc n))

        bf-snd-P : BeforeFrontier aP (AtStack (current-frame alloc) PS.snd-stash)
        bf-snd-P = BeforeFrontier.stack-before refl (n<1+n (suc (suc n)))

        ----------------------------------------------------------------
        -- (i) `fst-stash` survives to `u5`, where `i6` loads it.
        ----------------------------------------------------------------
        read-fst-u2 : MemOps.readLoc (floc u2)
                        (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
        read-fst-u2 =
          trans (store-slot-preserves-before PS.snd-stash (floc u1) aS (falloc u1)
                   (AtStack (current-frame alloc) PS.fst-stash) cf-fsG ≤-refl bf-fst-S)
                read-fst-fsG

        read-fst-u3 : MemOps.readLoc (floc u3)
                        (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
        read-fst-u3 =
          trans (mem-untouched (instr-alloc-heap 2) (floc u2) (falloc u2)
                   (AtStack (current-frame alloc) PS.fst-stash) nhw-instr-alloc-heap refl)
                read-fst-u2

        read-fst-u4 : MemOps.readLoc (floc u4)
                        (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
        read-fst-u4 =
          trans (store-slot-preserves-before PS.pair-stash (floc u3) aS (falloc u3)
                   (AtStack (current-frame alloc) PS.fst-stash) cf-u3
                   (n≤1+n PS.snd-stash) bf-fst-S)
                read-fst-u3

        read-fst-u5 : MemOps.readLoc (floc u5)
                        (AtStack (current-frame alloc) PS.fst-stash) ≡ just fv
        read-fst-u5 =
          trans (mem-untouched mov-to-input (floc u4) (falloc u4)
                   (AtStack (current-frame alloc) PS.fst-stash) nhw-mov-to-input refl)
                read-fst-u4

        wf-load-fst : InstrWF (floc u5) (falloc u5) (load-from-slot PS.fst-stash)
        wf-load-fst =
          fv , subst (λ fr → MemOps.readLoc (floc u5) (AtStack fr PS.fst-stash) ≡ just fv)
                     (sym cf-u5) read-fst-u5

        ----------------------------------------------------------------
        -- (ii) the pointer in `Input1`, before and after `i6`.
        ----------------------------------------------------------------
        rdi5 : sv-as-loc (readReg (regs (floc u5)) Input1) ≡ just (AtDynamic hl)
        rdi5 = refl

        rdi6 : sv-as-loc (readReg (regs (floc u6)) Input1) ≡ just (AtDynamic hl)
        rdi6 = trans (cong sv-as-loc
                        (load-slot-preserves-input PS.fst-stash (floc u5) (falloc u5)
                           fv (proj₂ wf-load-fst)))
                     rdi5

        wf-store-ind : InstrWF (floc u6) (falloc u6) store-indirect
        wf-store-ind = AtDynamic hl , rdi6

        ----------------------------------------------------------------
        -- (iii) `snd-stash`, written by the tail's own first row.
        ----------------------------------------------------------------
        sv : StoredValue FS
        sv = readReg (regs (floc u1)) Output

        read-snd-u2 : MemOps.readLoc (floc u2)
                        (AtStack (current-frame (falloc u1)) PS.snd-stash) ≡ just sv
        read-snd-u2 =
          MemOps.writeLoc-read-same-stack (floc u1)
            (current-frame (falloc u1)) PS.snd-stash sv

        read-snd-u2' : MemOps.readLoc (floc u2)
                         (AtStack (current-frame alloc) PS.snd-stash) ≡ just sv
        read-snd-u2' =
          subst (λ fr → MemOps.readLoc (floc u2) (AtStack fr PS.snd-stash) ≡ just sv)
                cf-fsG read-snd-u2

        read-snd-u3 : MemOps.readLoc (floc u3)
                        (AtStack (current-frame alloc) PS.snd-stash) ≡ just sv
        read-snd-u3 =
          trans (mem-untouched (instr-alloc-heap 2) (floc u2) (falloc u2)
                   (AtStack (current-frame alloc) PS.snd-stash) nhw-instr-alloc-heap refl)
                read-snd-u2'

        read-snd-u4 : MemOps.readLoc (floc u4)
                        (AtStack (current-frame alloc) PS.snd-stash) ≡ just sv
        read-snd-u4 =
          trans (store-slot-preserves-before PS.pair-stash (floc u3) aP (falloc u3)
                   (AtStack (current-frame alloc) PS.snd-stash) cf-u3 ≤-refl bf-snd-P)
                read-snd-u3

        read-snd-u5 : MemOps.readLoc (floc u5)
                        (AtStack (current-frame alloc) PS.snd-stash) ≡ just sv
        read-snd-u5 =
          trans (mem-untouched mov-to-input (floc u4) (falloc u4)
                   (AtStack (current-frame alloc) PS.snd-stash) nhw-mov-to-input refl)
                read-snd-u4

        read-snd-u6 : MemOps.readLoc (floc u6)
                        (AtStack (current-frame alloc) PS.snd-stash) ≡ just sv
        read-snd-u6 =
          trans (mem-untouched (load-from-slot PS.fst-stash) (floc u5) (falloc u5)
                   (AtStack (current-frame alloc) PS.snd-stash) nhw-load-from-slot refl)
                read-snd-u5

        read-snd-u7 : MemOps.readLoc (floc u7)
                        (AtStack (current-frame alloc) PS.snd-stash) ≡ just sv
        read-snd-u7 =
          trans (store-ind-preserves-slot (floc u6) (falloc u6) hl PS.snd-stash rdi6)
                read-snd-u6

        wf-load-snd : InstrWF (floc u7) (falloc u7) (load-from-slot PS.snd-stash)
        wf-load-snd =
          sv , subst (λ fr → MemOps.readLoc (floc u7) (AtStack fr PS.snd-stash) ≡ just sv)
                     (sym cf-u7) read-snd-u7

        rdi8 : sv-as-loc (readReg (regs (floc u8)) Input1) ≡ just (AtDynamic hl)
        rdi8 =
          trans (cong sv-as-loc
                   (trans (load-slot-preserves-input PS.snd-stash (floc u7) (falloc u7)
                             sv (proj₂ wf-load-snd))
                          (store-ind-preserves-input (floc u6) (falloc u6)
                             (AtDynamic hl) rdi6)))
                rdi6

        wf-store-ind-suc : InstrWF (floc u8) (falloc u8) store-indirect-suc
        wf-store-ind-suc = AtDynamic hl , rdi8

        ----------------------------------------------------------------
        -- (iv) `pair-stash`, the pointer the run hands back.
        ----------------------------------------------------------------
        pv : StoredValue FS
        pv = readReg (regs (floc u3)) Output

        read-pair-u4 : MemOps.readLoc (floc u4)
                         (AtStack (current-frame (falloc u3)) PS.pair-stash) ≡ just pv
        read-pair-u4 =
          MemOps.writeLoc-read-same-stack (floc u3)
            (current-frame (falloc u3)) PS.pair-stash pv

        read-pair-u4' : MemOps.readLoc (floc u4)
                          (AtStack (current-frame alloc) PS.pair-stash) ≡ just pv
        read-pair-u4' =
          subst (λ fr → MemOps.readLoc (floc u4) (AtStack fr PS.pair-stash) ≡ just pv)
                cf-u3 read-pair-u4

        read-pair-u5 : MemOps.readLoc (floc u5)
                         (AtStack (current-frame alloc) PS.pair-stash) ≡ just pv
        read-pair-u5 =
          trans (mem-untouched mov-to-input (floc u4) (falloc u4)
                   (AtStack (current-frame alloc) PS.pair-stash) nhw-mov-to-input refl)
                read-pair-u4'

        read-pair-u6 : MemOps.readLoc (floc u6)
                         (AtStack (current-frame alloc) PS.pair-stash) ≡ just pv
        read-pair-u6 =
          trans (mem-untouched (load-from-slot PS.fst-stash) (floc u5) (falloc u5)
                   (AtStack (current-frame alloc) PS.pair-stash) nhw-load-from-slot refl)
                read-pair-u5

        read-pair-u7 : MemOps.readLoc (floc u7)
                         (AtStack (current-frame alloc) PS.pair-stash) ≡ just pv
        read-pair-u7 =
          trans (store-ind-preserves-slot (floc u6) (falloc u6) hl PS.pair-stash rdi6)
                read-pair-u6

        read-pair-u8 : MemOps.readLoc (floc u8)
                         (AtStack (current-frame alloc) PS.pair-stash) ≡ just pv
        read-pair-u8 =
          trans (mem-untouched (load-from-slot PS.snd-stash) (floc u7) (falloc u7)
                   (AtStack (current-frame alloc) PS.pair-stash) nhw-load-from-slot refl)
                read-pair-u7

        read-pair-u9 : MemOps.readLoc (floc u9)
                         (AtStack (current-frame alloc) PS.pair-stash) ≡ just pv
        read-pair-u9 =
          trans (store-ind-suc-preserves-slot (floc u8) (falloc u8) hl PS.pair-stash rdi8)
                read-pair-u8

        wf-load-pair : InstrWF (floc u9) (falloc u9) (load-from-slot PS.pair-stash)
        wf-load-pair =
          pv , subst (λ fr → MemOps.readLoc (floc u9) (AtStack fr PS.pair-stash) ≡ just pv)
                     (sym cf-u9) read-pair-u9

        ----------------------------------------------------------------
        -- THE NINE `halted ≡ false` OBLIGATIONS. Rows 1-4 are
        -- unconditional; rows 5-9 each spend a witness an EARLIER row of
        -- this same chain established.
        ----------------------------------------------------------------
        nhU2 : halted (floc u2) ≡ false
        nhU2 = exec-abstract-preserves-halted-WF (store-at-slot PS.snd-stash)
                 (floc u1) (falloc u1) liveG tt
        nhU3 : halted (floc u3) ≡ false
        nhU3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2)
                 (floc u2) (falloc u2) nhU2 tt
        nhU4 : halted (floc u4) ≡ false
        nhU4 = exec-abstract-preserves-halted-WF (store-at-slot PS.pair-stash)
                 (floc u3) (falloc u3) nhU3 tt
        nhU5 : halted (floc u5) ≡ false
        nhU5 = exec-abstract-preserves-halted-WF mov-to-input
                 (floc u4) (falloc u4) nhU4 tt
        nhU6 : halted (floc u6) ≡ false
        nhU6 = exec-abstract-preserves-halted-WF (load-from-slot PS.fst-stash)
                 (floc u5) (falloc u5) nhU5 wf-load-fst
        nhU7 : halted (floc u7) ≡ false
        nhU7 = exec-abstract-preserves-halted-WF store-indirect
                 (floc u6) (falloc u6) nhU6 wf-store-ind
        nhU8 : halted (floc u8) ≡ false
        nhU8 = exec-abstract-preserves-halted-WF (load-from-slot PS.snd-stash)
                 (floc u7) (falloc u7) nhU7 wf-load-snd
        nhU9 : halted (floc u9) ≡ false
        nhU9 = exec-abstract-preserves-halted-WF store-indirect-suc
                 (floc u8) (falloc u8) nhU8 wf-store-ind-suc
        nhU10 : halted (floc u10) ≡ false
        nhU10 = exec-abstract-preserves-halted-WF (load-from-slot PS.pair-stash)
                  (floc u9) (falloc u9) nhU9 wf-load-pair

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

        tail-chain : FlatSteps prog 9 fsG u10
        tail-chain =
            (liveG , tfetch 0 (store-at-slot PS.snd-stash)   refl)
          ∷ (nhU2  , tfetch 1 (instr-alloc-heap 2)           refl)
          ∷ (nhU3  , tfetch 2 (store-at-slot PS.pair-stash)  refl)
          ∷ (nhU4  , tfetch 3 mov-to-input                   refl)
          ∷ (nhU5  , tfetch 4 (load-from-slot PS.fst-stash)  refl)
          ∷ (nhU6  , tfetch 5 store-indirect                 refl)
          ∷ (nhU7  , tfetch 6 (load-from-slot PS.snd-stash)  refl)
          ∷ (nhU8  , tfetch 7 store-indirect-suc             refl)
          ∷ (nhU9  , tfetch 8 (load-from-slot PS.pair-stash) refl)
          ∷ []

        ----------------------------------------------------------------
        -- ══ THE SEVEN FIELDS ══
        ----------------------------------------------------------------
        STEPS : ℕ
        STEPS = 2 + (VR.steps vrf + (2 + (VR.steps vrg + 9)))

        SETTLE : FlatState
        SETTLE = u10

        RUN : FlatSteps prog STEPS (entry-flat base s alloc cl) SETTLE
        RUN = FlatSteps-++ pre-chain
                (FlatSteps-++ chainF
                  (FlatSteps-++ mid-chain
                    (FlatSteps-++ chainG tail-chain)))

        LIVE : halted (floc SETTLE) ≡ false
        LIVE = nhU10

        at-end-arith : ∀ (a b b0 : ℕ)
                     → 9 + (b + suc (suc (a + suc (suc b0))))
                       ≡ suc (suc (a + suc (suc (b + 9)))) + b0
        at-end-arith a b b0 = solve 3 (λ x y w →
            con 9 :+ (y :+ (con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ w))))))
          , con 1 :+ (con 1 :+ (x :+ (con 1 :+ (con 1 :+ (y :+ con 9))))) :+ w)
          refl a b b0

        ATEND : fpc SETTLE ≡ length (emitted n l ⟨ f , g ⟩) + base
        ATEND =
          trans (cong (9 +_) endG)
          (trans (at-end-arith (length PS.ft) (length PS.gt) base)
                 (cong (_+ base) (sym len-emitted)))

        NORET : fret SETTLE ≡ []
        NORET = VR.no-ret vrg

        NOLINK : flink SETTLE ≡ nothing
        NOLINK = VR.no-link vrg

  ----------------------------------------------------------------------
  -- THE RESULT PLACE (cluster PairPlace).
  --
  -- The tail allocates a two-cell heap node and writes `f`'s result into
  -- cell 0 and `g`'s into cell 1. So `⟨ f , g ⟩`'s residence is `Heap`, its
  -- continuation allocator is the one the tail leaves, and its witness is
  -- `valid-pair-wf` over two `CellAt`s.
  --
  -- PARAMETERISED, not computed: the cluster takes the two settle states and
  -- the two `ResultPlace`s the induction hypotheses hand over, plus exactly
  -- the allocator facts `ValueRealized` now exports about each run
  -- (`frame-pres`, slot stability, heap monotonicity) and the two cross-run
  -- memory facts `g`'s run owes (`mem-F→G`, from its `stack-pres`/`heap-pres`,
  -- and `fst-cell-gs`, its `stack-pres` at `fst-stash`).
  --
  -- NOTE on the frontier the tail is measured against. `PairTail` instantiates
  -- `NineStepPres` at the CALLER's `alloc`, which forces
  -- `next-heap-ref (falloc gs) ≡ next-heap-ref alloc` — false as soon as `f` or
  -- `g` allocates (`f = inl` suffices). This module instantiates it at
  -- `record (falloc gs) { next-slot = snd-stash }` instead, where both of
  -- `NineStepPres`'s premises are `refl`, and weakens the caller's
  -- `BeforeFrontier`s into it with `frontier-monotone`. The nine states are the
  -- same nine either way, so nothing downstream has to choose.
  ----------------------------------------------------------------------
  module PairPlace
    {B C : IRTy}
    (n : ℕ)
    (alloc : AllocState {FS})
    (n≤ : next-slot alloc ≤ n)
    -- the state `f` settled in, and the state `g` settled in (= the tail's
    -- start state)
    (fsF gs : FlatState)
    -- what the two runs did to the allocator: `ValueRealized.frame-pres`
    -- (D210), `flat-run-keeps-next-slot`, and heap monotonicity
    (cf-fsF : current-frame (falloc fsF) ≡ current-frame alloc)
    (cf-gs  : current-frame (falloc gs)  ≡ current-frame alloc)
    (ns-fsF : next-slot (falloc fsF) ≡ next-slot alloc)
    (ns-gs  : next-slot (falloc gs)  ≡ next-slot alloc)
    (hr-gs  : next-heap-ref (falloc fsF) ≤ next-heap-ref (falloc gs))
    -- the two component values and the residences the IHs realized them at
    (vB : ⟦ B ⟧) (vC : ⟦ C ⟧)
    (mf mg : AllocMode) (caf cag : AllocState {FS})
    (placeF : ResultPlace B mf (falloc fsF) caf vB (floc fsF))
    (placeG : ResultPlace C mg (falloc gs)  cag vC (floc gs))
    -- what the two mid rows and `g`'s run leave alone …
    (mem-F→G : ∀ (loc : ValueLocation FS)
             → BeforeFrontier (falloc fsF) loc
             → MemOps.readLoc (floc gs) loc ≡ MemOps.readLoc (floc fsF) loc)
    -- … and that `f`'s result is still in its stash when `g` is done
    (fst-cell-gs : MemOps.readLoc (floc gs)
                     (AtStack (current-frame alloc) (suc n))
                 ≡ just (readReg (regs (floc fsF)) Output))
    where

    fst-stash snd-stash pair-stash : ℕ
    fst-stash  = suc n
    snd-stash  = suc (suc n)
    pair-stash = suc (suc (suc n))

    -- The frontier the tail's own preservation is measured against: `g`'s
    -- allocator with the stash bound. Both of `NineStepPres`'s premises are
    -- `refl` here, which is the point.
    a' : AllocState {FS}
    a' = record (falloc gs) { next-slot = snd-stash }

    module NSP = NineStepPres snd-stash
                   (load-from-slot fst-stash)   -- i6
                   (load-from-slot snd-stash)   -- i8
                   gs (floc gs) a' refl refl

    u2 u3 u4 u5 u6 u7 u8 u9 u10 : FlatState
    u2 = NSP.u2 ; u3 = NSP.u3 ; u4 = NSP.u4 ; u5 = NSP.u5 ; u6 = NSP.u6
    u7 = NSP.u7 ; u8 = NSP.u8 ; u9 = NSP.u9 ; u10 = NSP.u10

    hl : HeapLocation
    hl = NSP.hl

    pair-loc : ValueLocation FS
    pair-loc = AtDynamic hl

    FR : Once.CCC.FrameSemantics.Frame FS
    FR = current-frame alloc

    -- ── the frame, row by row ────────────────────────────────────────────
    cf-u2 : current-frame (falloc u2) ≡ current-frame alloc
    cf-u2  = trans (exec-abstract-preserves-frame (store-at-slot snd-stash) (floc gs) (falloc gs)) cf-gs
    cf-u3 : current-frame (falloc u3) ≡ current-frame alloc
    cf-u3  = trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc u2) (falloc u2)) cf-u2
    cf-u4 : current-frame (falloc u4) ≡ current-frame alloc
    cf-u4  = trans (exec-abstract-preserves-frame (store-at-slot pair-stash) (floc u3) (falloc u3)) cf-u3
    cf-u5 : current-frame (falloc u5) ≡ current-frame alloc
    cf-u5  = trans (exec-abstract-preserves-frame mov-to-input (floc u4) (falloc u4)) cf-u4
    cf-u6 : current-frame (falloc u6) ≡ current-frame alloc
    cf-u6  = trans (exec-abstract-preserves-frame (load-from-slot fst-stash) (floc u5) (falloc u5)) cf-u5
    cf-u7 : current-frame (falloc u7) ≡ current-frame alloc
    cf-u7  = trans (exec-abstract-preserves-frame store-indirect (floc u6) (falloc u6)) cf-u6
    cf-u8 : current-frame (falloc u8) ≡ current-frame alloc
    cf-u8  = trans (exec-abstract-preserves-frame (load-from-slot snd-stash) (floc u7) (falloc u7)) cf-u7
    cf-u9 : current-frame (falloc u9) ≡ current-frame alloc
    cf-u9  = trans (exec-abstract-preserves-frame store-indirect-suc (floc u8) (falloc u8)) cf-u8
    cf-u10 : current-frame (falloc u10) ≡ current-frame alloc
    cf-u10 = trans (exec-abstract-preserves-frame (load-from-slot pair-stash) (floc u9) (falloc u9)) cf-u9

    -- A stash write above a slot, read at the CALLER's frame rather than the
    -- running allocator's.
    slot-below-at : ∀ (j k : ℕ) (st : LocState FS) (aa : AllocState {FS})
                  → current-frame aa ≡ current-frame alloc → j < k
                  → MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st aa)) (AtStack FR j)
                    ≡ MemOps.readLoc st (AtStack FR j)
    slot-below-at j k st aa cf j<k =
      subst (λ fr → MemOps.readLoc (proj₁ (exec-abstract (store-at-slot k) st aa)) (AtStack fr j)
                    ≡ MemOps.readLoc st (AtStack fr j))
            cf (store-at-slot-preserves-below j k st aa j<k)

    -- ── the heap frontier ────────────────────────────────────────────────
    heapref-u2 : next-heap-ref (falloc u2) ≡ next-heap-ref (falloc gs)
    heapref-u2 = exec-abstract-preserves-heap-ref (store-at-slot snd-stash) (floc gs) (falloc gs) tt

    heapref-u10 : next-heap-ref (falloc u10) ≡ suc (next-heap-ref (falloc u2))
    heapref-u10 =
      trans (exec-abstract-preserves-heap-ref (load-from-slot pair-stash) (floc u9) (falloc u9) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc u8) (falloc u8) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot snd-stash) (floc u7) (falloc u7) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect (floc u6) (falloc u6) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot fst-stash) (floc u5) (falloc u5) tt)
     (trans (exec-abstract-preserves-heap-ref mov-to-input (floc u4) (falloc u4) tt)
            (exec-abstract-preserves-heap-ref (store-at-slot pair-stash) (floc u3) (falloc u3) tt))))))

    before : BeforeFrontier (falloc u10) pair-loc
    before = BeforeFrontier.heap-before
               (subst (λ m → next-heap-ref (falloc u2) < m) (sym heapref-u10) (n<1+n _))

    before-suc : BeforeFrontier (falloc u10) (sucLoc pair-loc)
    before-suc = BeforeFrontier.heap-before
                   (subst (λ m → next-heap-ref (falloc u2) < m) (sym heapref-u10) (n<1+n _))

    gs≤u10 : next-heap-ref (falloc gs) ≤ next-heap-ref (falloc u10)
    gs≤u10 =
      subst (λ m → next-heap-ref (falloc gs) ≤ m) (sym heapref-u10)
        (subst (λ r → next-heap-ref (falloc gs) ≤ suc r) (sym heapref-u2) (n≤1+n _))

    -- ── the slot frontier ────────────────────────────────────────────────
    nextslot-u10 : next-slot (falloc u10) ≡ next-slot (falloc gs)
    nextslot-u10 =
      trans (exec-abstract-preserves-next-slot (load-from-slot pair-stash) (floc u9) (falloc u9) tt)
     (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc u8) (falloc u8) tt)
     (trans (exec-abstract-preserves-next-slot (load-from-slot snd-stash) (floc u7) (falloc u7) tt)
     (trans (exec-abstract-preserves-next-slot store-indirect (floc u6) (falloc u6) tt)
     (trans (exec-abstract-preserves-next-slot (load-from-slot fst-stash) (floc u5) (falloc u5) tt)
     (trans (exec-abstract-preserves-next-slot mov-to-input (floc u4) (falloc u4) tt)
     (trans (exec-abstract-preserves-next-slot (store-at-slot pair-stash) (floc u3) (falloc u3) tt)
     (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc u2) (falloc u2) tt)
            (exec-abstract-preserves-next-slot (store-at-slot snd-stash) (floc gs) (falloc gs) tt))))))))

    -- ── the four conditional witnesses, in dependency order ──────────────
    fv gv pv : StoredValue FS
    fv = readReg (regs (floc fsF)) Output   -- f's result, in its stash
    gv = readReg (regs (floc gs))  Output   -- g's result, stashed by row 2
    pv = readReg (regs (floc u3))  Output   -- the node pointer, stashed by row 4

    -- Row 3 hands out the block; rows 4-5 carry the pointer into `Input1`.
    out-u3 : pv ≡ SV-Ptr pair-loc
    out-u3 = writeReg-same (regs (floc u2)) Output (SV-Ptr (AtDynamic hl))

    out-u4 : readReg (regs (floc u4)) Output ≡ SV-Ptr pair-loc
    out-u4 =
      trans (cong (λ r → readReg r Output)
                  (MemOps.writeLoc-regs (floc u3)
                     (AtStack (current-frame (falloc u3)) pair-stash) pv))
            out-u3

    rdi-u5 : sv-as-loc (readReg (regs (floc u5)) Input1) ≡ just pair-loc
    rdi-u5 =
      trans (cong sv-as-loc
                  (writeReg-same (regs (floc u4)) Input1 (readReg (regs (floc u4)) Output)))
            (cong sv-as-loc out-u4)

    -- Row 6 reads `fst-stash`. What is there is `f`'s result: rows 2-5 write
    -- `snd-stash`, the heap, `pair-stash` and a register.
    fst-u5 : MemOps.readLoc (floc u5) (AtStack FR fst-stash) ≡ just fv
    fst-u5 =
      trans (exec-abstract-preserves-stack-slot mov-to-input (floc u4) (falloc u4)
               FR fst-stash nhw-mov-to-input refl)
     (trans (slot-below-at fst-stash pair-stash (floc u3) (falloc u3) cf-u3 (n≤1+n _))
     (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc u2) (falloc u2)
               FR fst-stash nhw-instr-alloc-heap refl)
     (trans (slot-below-at fst-stash snd-stash (floc gs) (falloc gs) cf-gs ≤-refl)
            fst-cell-gs)))

    wf-load-fst : InstrWF (floc u5) (falloc u5) (load-from-slot fst-stash)
    wf-load-fst =
      fv , subst (λ fr → MemOps.readLoc (floc u5) (AtStack fr fst-stash) ≡ just fv)
                 (sym cf-u5) fst-u5

    rdi-u6 : sv-as-loc (readReg (regs (floc u6)) Input1) ≡ just pair-loc
    rdi-u6 =
      trans (cong sv-as-loc
              (load-slot-preserves-input fst-stash (floc u5) (falloc u5) fv (proj₂ wf-load-fst)))
            rdi-u5

    out-u6 : readReg (regs (floc u6)) Output ≡ fv
    out-u6 = load-slot-result fst-stash (floc u5) (falloc u5) fv (proj₂ wf-load-fst)

    -- CELL 0, written by `store-indirect` at row 7.
    cell0-u7 : MemOps.readLoc (floc u7) pair-loc ≡ just fv
    cell0-u7 = trans (store-ind-result (floc u6) (falloc u6) hl rdi-u6)
                     (cong just out-u6)

    -- Row 8 reads `snd-stash`, which row 2 wrote with `g`'s result.
    snd-u2 : MemOps.readLoc (floc u2) (AtStack FR snd-stash) ≡ just gv
    snd-u2 =
      subst (λ fr → MemOps.readLoc (floc u2) (AtStack fr snd-stash) ≡ just gv)
            cf-gs
            (MemOps.writeLoc-read-same-stack (floc gs) (current-frame (falloc gs)) snd-stash gv)

    snd-u7 : MemOps.readLoc (floc u7) (AtStack FR snd-stash) ≡ just gv
    snd-u7 =
      trans (store-ind-preserves-slot (floc u6) (falloc u6) hl snd-stash rdi-u6)
     (trans (exec-abstract-preserves-stack-slot (load-from-slot fst-stash) (floc u5) (falloc u5)
               FR snd-stash nhw-load-from-slot refl)
     (trans (exec-abstract-preserves-stack-slot mov-to-input (floc u4) (falloc u4)
               FR snd-stash nhw-mov-to-input refl)
     (trans (slot-below-at snd-stash pair-stash (floc u3) (falloc u3) cf-u3 ≤-refl)
     (trans (exec-abstract-preserves-stack-slot (instr-alloc-heap 2) (floc u2) (falloc u2)
               FR snd-stash nhw-instr-alloc-heap refl)
            snd-u2))))

    wf-load-snd : InstrWF (floc u7) (falloc u7) (load-from-slot snd-stash)
    wf-load-snd =
      gv , subst (λ fr → MemOps.readLoc (floc u7) (AtStack fr snd-stash) ≡ just gv)
                 (sym cf-u7) snd-u7

    rdi-u7 : sv-as-loc (readReg (regs (floc u7)) Input1) ≡ just pair-loc
    rdi-u7 =
      trans (cong sv-as-loc (store-ind-preserves-input (floc u6) (falloc u6) pair-loc rdi-u6))
            rdi-u6

    rdi-u8 : sv-as-loc (readReg (regs (floc u8)) Input1) ≡ just pair-loc
    rdi-u8 =
      trans (cong sv-as-loc
              (load-slot-preserves-input snd-stash (floc u7) (falloc u7) gv (proj₂ wf-load-snd)))
            rdi-u7

    out-u8 : readReg (regs (floc u8)) Output ≡ gv
    out-u8 = load-slot-result snd-stash (floc u7) (falloc u7) gv (proj₂ wf-load-snd)

    -- CELL 1, written by `store-indirect-suc` at row 9.
    cell1-u9 : MemOps.readLoc (floc u9) (sucLoc pair-loc) ≡ just gv
    cell1-u9 = trans (store-ind-suc-result (floc u8) (falloc u8) hl rdi-u8)
                     (cong just out-u8)

    -- …and both cells carried to the end: the only writes left are the OTHER
    -- cell of the same block and two register-only loads.
    cell0-u10 : MemOps.readLoc (floc u10) pair-loc ≡ just fv
    cell0-u10 =
      trans (heap-untouched (load-from-slot pair-stash) (floc u9) (falloc u9) hl nhw-load-from-slot)
     (trans (store-ind-suc-preserves-heap (floc u8) (falloc u8) hl hl rdi-u8 (sucHL-≢ hl))
     (trans (heap-untouched (load-from-slot snd-stash) (floc u7) (falloc u7) hl nhw-load-from-slot)
            cell0-u7))

    cell1-u10 : MemOps.readLoc (floc u10) (sucLoc pair-loc) ≡ just gv
    cell1-u10 =
      trans (heap-untouched (load-from-slot pair-stash) (floc u9) (falloc u9)
               (sucHL hl) nhw-load-from-slot)
            cell1-u9

    -- THE RESULT POINTER: row 10 loads the stashed node pointer.
    pair-u4 : MemOps.readLoc (floc u4) (AtStack FR pair-stash) ≡ just pv
    pair-u4 =
      subst (λ fr → MemOps.readLoc (floc u4) (AtStack fr pair-stash) ≡ just pv)
            cf-u3
            (MemOps.writeLoc-read-same-stack (floc u3) (current-frame (falloc u3)) pair-stash pv)

    pair-u9 : MemOps.readLoc (floc u9) (AtStack FR pair-stash) ≡ just pv
    pair-u9 =
      trans (store-ind-suc-preserves-slot (floc u8) (falloc u8) hl pair-stash rdi-u8)
     (trans (exec-abstract-preserves-stack-slot (load-from-slot snd-stash) (floc u7) (falloc u7)
               FR pair-stash nhw-load-from-slot refl)
     (trans (store-ind-preserves-slot (floc u6) (falloc u6) hl pair-stash rdi-u6)
     (trans (exec-abstract-preserves-stack-slot (load-from-slot fst-stash) (floc u5) (falloc u5)
               FR pair-stash nhw-load-from-slot refl)
     (trans (exec-abstract-preserves-stack-slot mov-to-input (floc u4) (falloc u4)
               FR pair-stash nhw-mov-to-input refl)
            pair-u4))))

    wf-load-pair : InstrWF (floc u9) (falloc u9) (load-from-slot pair-stash)
    wf-load-pair =
      pv , subst (λ fr → MemOps.readLoc (floc u9) (AtStack fr pair-stash) ≡ just pv)
                 (sym cf-u9) pair-u9

    out-u10 : readReg (regs (floc u10)) Output ≡ SV-Ptr pair-loc
    out-u10 = trans (load-slot-result pair-stash (floc u9) (falloc u9) pv (proj₂ wf-load-pair))
                    out-u3

    ------------------------------------------------------------------------
    -- THE TRANSPORTS. Each component's validity is stated at its OWN settle
    -- state; the node's is stated at the tail's. Three moves: memory (the
    -- tail's own preservation, composed with what `g`'s run preserves),
    -- frontier (the allocation advanced it), and the `BeforeFrontier`s.
    ------------------------------------------------------------------------
    tail-pres : ∀ (loc : ValueLocation FS) → BeforeFrontier a' loc
              → MemOps.readLoc (floc u10) loc ≡ MemOps.readLoc (floc gs) loc
    tail-pres = NSP.mem-pres-from nhw-load-from-slot refl nhw-load-from-slot refl
                  ≤-refl rdi-u6 rdi-u8

    bf-weaken-F : ∀ (loc : ValueLocation FS)
                → BeforeFrontier (falloc fsF) loc → BeforeFrontier a' loc
    bf-weaken-F =
      frontier-monotone (falloc fsF) a' (trans cf-fsF (sym cf-gs))
        (≤-trans (≤-reflexive ns-fsF) (≤-trans n≤ (≤-trans (n≤1+n n) (n≤1+n (suc n)))))
        hr-gs

    bf-weaken-G : ∀ (loc : ValueLocation FS)
                → BeforeFrontier (falloc gs) loc → BeforeFrontier a' loc
    bf-weaken-G =
      frontier-monotone (falloc gs) a' refl
        (≤-trans (≤-reflexive ns-gs) (≤-trans n≤ (≤-trans (n≤1+n n) (n≤1+n (suc n)))))
        ≤-refl

    mem-F→u10 : ∀ (loc : ValueLocation FS) → BeforeFrontier (falloc fsF) loc
              → MemOps.readLoc (floc u10) loc ≡ MemOps.readLoc (floc fsF) loc
    mem-F→u10 loc bf = trans (tail-pres loc (bf-weaken-F loc bf)) (mem-F→G loc bf)

    mem-G→u10 : ∀ (loc : ValueLocation FS) → BeforeFrontier (falloc gs) loc
              → MemOps.readLoc (floc u10) loc ≡ MemOps.readLoc (floc gs) loc
    mem-G→u10 loc bf = tail-pres loc (bf-weaken-G loc bf)

    transF : ∀ {m'} {E : IRTy} (w : ⟦ E ⟧) (lc : ValueLocation FS)
           → BeforeFrontier (falloc fsF) lc
           → ValidAtWF m' (falloc fsF) {E} w lc (floc fsF)
           → ValidAtWF m' (falloc u10) {E} w lc (floc u10)
    transF w lc bf vd =
      validityWF-frontier-advance w lc (floc u10)
        (trans cf-u10 (sym cf-fsF))
        (≤-reflexive (trans ns-fsF (sym (trans nextslot-u10 ns-gs))))
        (≤-trans hr-gs gs≤u10)
        (validityWF-mem-preserved w lc (floc fsF) (floc u10) bf mem-F→u10 vd)

    transG : ∀ {m'} {E : IRTy} (w : ⟦ E ⟧) (lc : ValueLocation FS)
           → BeforeFrontier (falloc gs) lc
           → ValidAtWF m' (falloc gs) {E} w lc (floc gs)
           → ValidAtWF m' (falloc u10) {E} w lc (floc u10)
    transG w lc bf vd =
      validityWF-frontier-advance w lc (floc u10)
        (trans cf-u10 (sym cf-gs))
        (≤-reflexive (sym nextslot-u10))
        gs≤u10
        (validityWF-mem-preserved w lc (floc gs) (floc u10) bf mem-G→u10 vd)

    bfF-u10 : ∀ (lc : ValueLocation FS)
            → BeforeFrontier (falloc fsF) lc → BeforeFrontier (falloc u10) lc
    bfF-u10 =
      frontier-monotone (falloc fsF) (falloc u10) (trans cf-fsF (sym cf-u10))
        (≤-reflexive (trans ns-fsF (sym (trans nextslot-u10 ns-gs))))
        (≤-trans hr-gs gs≤u10)

    bfG-u10 : ∀ (lc : ValueLocation FS)
            → BeforeFrontier (falloc gs) lc → BeforeFrontier (falloc u10) lc
    bfG-u10 =
      frontier-monotone (falloc gs) (falloc u10) (trans cf-gs (sym cf-u10))
        (≤-reflexive (sym nextslot-u10)) gs≤u10

    ------------------------------------------------------------------------
    -- A `ResultPlace` IS a `CellAt` once the cell holds what `Output` held.
    -- Three residences, three cell shapes (D187): a pointer is `cell-ptr` with
    -- the component's validity carried across; a register literal and a `Unit`
    -- are `cell-inline`, which needs no validity at all.
    --
    -- Written as a helper over the transports rather than twice, because the
    -- two components differ ONLY in which state they came from. (`with` is
    -- unavailable here for the same reason it is in `Sum`: the place is a
    -- module parameter, not a pattern.)
    ------------------------------------------------------------------------
    cell-of : ∀ {D : IRTy} {v : ⟦ D ⟧} {m : AllocMode} {aS ca : AllocState {FS}}
                (src : LocState FS) (cl : ValueLocation FS)
              → MemOps.readLoc (floc u10) cl ≡ just (readReg (regs src) Output)
              → (∀ {m'} {E : IRTy} (w : ⟦ E ⟧) (lc : ValueLocation FS)
                 → BeforeFrontier aS lc
                 → ValidAtWF m' aS {E} w lc src
                 → ValidAtWF m' (falloc u10) {E} w lc (floc u10))
              → (∀ (lc : ValueLocation FS) → BeforeFrontier aS lc
                 → BeforeFrontier (falloc u10) lc)
              → ResultPlace D m aS ca v src
              → CellAt (falloc u10) D v cl (floc u10)
    cell-of src cl rd tr bfw (at-loc loc valid bef rax _ _) =
      cell-ptr (trans rd (cong just rax)) (bfw loc bef) (tr _ loc bef valid)
    cell-of src cl rd tr bfw (at-reg fit rax) =
      cell-inline (rep-prim fit) (trans rd (cong just rax))
    cell-of src cl rd tr bfw unit-result =
      cell-inline (rep-unit refl (readReg (regs src) Output)) rd

    cellF : CellAt (falloc u10) B vB pair-loc (floc u10)
    cellF = cell-of (floc fsF) pair-loc cell0-u10 transF bfF-u10 placeF

    cellG : CellAt (falloc u10) C vC (sucLoc pair-loc) (floc u10)
    cellG = cell-of (floc gs) (sucLoc pair-loc) cell1-u10 transG bfG-u10 placeG

    ------------------------------------------------------------------------
    -- THE THREE FIELDS. `out-mode` is `Heap` because the node is a heap block;
    -- `cont-alloc` is the allocator the tail leaves, so the continuation's
    -- copy of the witness is the SAME witness (`inl`/`inr` do this too).
    ------------------------------------------------------------------------
    out-mode : AllocMode
    out-mode = Heap

    cont-alloc : AllocState {FS}
    cont-alloc = falloc u10

    validity : ValidAtWF Heap (falloc u10) {B * C} (vB , vC) pair-loc (floc u10)
    validity = valid-pair-wf tt before-suc cellF cellG

    place : ResultPlace (B * C) Heap (falloc u10) (falloc u10) (vB , vC) (floc u10)
    place = at-loc pair-loc validity before out-u10 validity before


  ----------------------------------------------------------------------
  -- THE PRESERVATION QUARTET (D206 / D208 / D210) for `⟨ f , g ⟩`.
  --
  -- `stack-pres`, `heap-pres`, `frame-pres` and `bf-mono` over the FIVE
  -- segments the clause runs:
  --
  --   prologue (2 rows)  ·  f's run  ·  mid (2 rows)  ·  g's run  ·  tail (9)
  --
  -- THE POINT THAT HAD TO BE CHECKED FIRST, and it HOLDS: the prologue writes
  -- slot `backup = n` and the mid rows write slot `fst-stash = suc n`, both AT
  -- OR ABOVE the fragment's own frontier `n`. The claim is only about what is
  -- STRICTLY BELOW `n` — `BeforeFrontier`'s `stack-before` constructor is
  -- `k < next-slot alloc`, and the record here has `next-slot := n` — so
  -- `store-slot-preserves-before`'s premise `next-slot alloc ≤ k` reads `n ≤ n`
  -- for the prologue's write and `n ≤ suc n` for the mid's. Both are immediate;
  -- neither write is visible. (`stack-ancestor` and `heap-before` locations are
  -- missed by a stack write of ANY index, which is that lemma's other two
  -- clauses.) So there is no blocker here.
  --
  -- WHERE THE TAIL IS MEASURED FROM — and this is a correction to `PairTail`.
  -- `PairTail` instantiates `NineStepPres` at the CALLER's `alloc`, which
  -- forces the premise `next-heap-ref (falloc gs) ≡ next-heap-ref alloc`: "`g`
  -- allocated nothing". That is false for a general `g` (`⟨ f , inl ⟩`
  -- allocates), so `PairTail.tail-mem-pres` cannot be instantiated in the real
  -- clause. The fix costs nothing: instantiate the nine at `g`'s OWN allocator
  -- (`tail-alloc` below), where the two premises are `refl`, and carry the
  -- caller's window over to that allocator with the two induction hypotheses'
  -- `bf-mono` first. `PairTail` is left untouched.
  ----------------------------------------------------------------------

  -- The prologue and the mid rows as TOP-LEVEL functions, so that `PairPres`'s
  -- own TELESCOPE can name the states its two induction hypotheses run from
  -- (a module parameter cannot mention a definition from the module's body).
  pair-p1 pair-p2 : AbstractTrace → ℕ → ℕ → LocState FS → AllocState {FS}
                  → StoredValue FS → FlatState
  pair-p1 prog base n s alloc cl =
    flat-exec-instr mov-to-output prog (entry-flat base s alloc cl)
  pair-p2 prog base n s alloc cl =
    flat-exec-instr (store-at-slot n) prog (pair-p1 prog base n s alloc cl)

  pair-m1 pair-m2 : AbstractTrace → ℕ → FlatState → FlatState
  pair-m1 prog n fsF = flat-exec-instr (store-at-slot (suc n)) prog fsF
  pair-m2 prog n fsF = flat-exec-instr (restore-input n) prog (pair-m1 prog n fsF)

  module PairPres
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    -- `f`'s induction hypothesis, at the state the two prologue rows leave.
    -- Its placement `bf₀` is free: preservation does not care where the
    -- fragment sits, only what frontier it was emitted at (`f-start`).
    {xf : ⟦ A ⟧} {kf bf₀ : ℕ}
    (vrF : ValueRealized prog bf₀ (suc (suc (suc (suc n)))) l f xf
             (floc (pair-p2 prog base n s alloc cl)) alloc
             (fclosure (pair-p2 prog base n s alloc cl)) kf)
    -- `g`'s, at the state the two mid rows leave. `n1`/`l1` are `f`'s output
    -- frontier and label base; all this module needs of them is `n ≤ n1`,
    -- which the caller supplies as `frontier-mono f f-start l` composed with
    -- `n ≤ f-start`.
    (n1 l1 : ℕ) (n≤n1 : n ≤ n1)
    {xg : ⟦ A ⟧} {kg bg : ℕ}
    (vrG : ValueRealized prog bg n1 l1 g xg
             (floc (pair-m2 prog n (ValueRealized.settle vrF)))
             (falloc (pair-m2 prog n (ValueRealized.settle vrF)))
             (fclosure (pair-m2 prog n (ValueRealized.settle vrF))) kg)
    where

    module VR = ValueRealized

    backup fst-stash snd-stash pair-stash f-start : ℕ
    backup     = n
    fst-stash  = suc n
    snd-stash  = suc (suc n)
    pair-stash = suc (suc (suc n))
    f-start    = suc (suc (suc (suc n)))

    -- The five segments' boundary states.
    p1 p2 : FlatState
    p1 = pair-p1 prog base n s alloc cl
    p2 = pair-p2 prog base n s alloc cl

    fsF : FlatState
    fsF = VR.settle vrF

    m1 m2 : FlatState
    m1 = pair-m1 prog n fsF
    m2 = pair-m2 prog n fsF

    gs : FlatState
    gs = VR.settle vrG

    -- The nine-instruction heap build, measured against `g`'s OWN allocator
    -- (see the header note): both of `NineStepPres`'s premises are then `refl`.
    tail-alloc : AllocState {FS}
    tail-alloc = record (falloc gs) { next-slot = snd-stash }

    module NSP = NineStepPres snd-stash
                   (load-from-slot fst-stash)   -- i6: the fst component
                   (load-from-slot snd-stash)   -- i8: the snd component
                   gs (floc gs) tail-alloc refl refl

    settle : FlatState
    settle = NSP.u10

    pair-hl : HeapLocation
    pair-hl = NSP.hl

    ------------------------------------------------------------------
    -- The two allocator chains the frame/frontier arguments need. Neither
    -- reduces: `falloc NSP.u10` is a nest of nine `exec-abstract`s and the
    -- `with`-blocks inside the loads and the indirect stores block it.
    ------------------------------------------------------------------
    cf-tail : current-frame (falloc NSP.u10) ≡ current-frame (falloc gs)
    cf-tail =
      trans (exec-abstract-preserves-frame (load-from-slot pair-stash) (floc NSP.u9) (falloc NSP.u9))
     (trans (exec-abstract-preserves-frame store-indirect-suc (floc NSP.u8) (falloc NSP.u8))
     (trans (exec-abstract-preserves-frame (load-from-slot snd-stash) (floc NSP.u7) (falloc NSP.u7))
     (trans (exec-abstract-preserves-frame store-indirect (floc NSP.u6) (falloc NSP.u6))
     (trans (exec-abstract-preserves-frame (load-from-slot fst-stash) (floc NSP.u5) (falloc NSP.u5))
     (trans (exec-abstract-preserves-frame mov-to-input (floc NSP.u4) (falloc NSP.u4))
     (trans (exec-abstract-preserves-frame (store-at-slot pair-stash) (floc NSP.u3) (falloc NSP.u3))
     (trans (exec-abstract-preserves-frame (instr-alloc-heap 2) (floc NSP.u2) (falloc NSP.u2))
            (exec-abstract-preserves-frame (store-at-slot snd-stash) (floc gs) (falloc gs)))))))))

    -- Rows 4-10 do not allocate, so the heap frontier they leave is the one
    -- `instr-alloc-heap 2` set at row 3 — one above `u2`'s.
    heapref-tail : next-heap-ref (falloc NSP.u10) ≡ suc (next-heap-ref (falloc NSP.u2))
    heapref-tail =
      trans (exec-abstract-preserves-heap-ref (load-from-slot pair-stash) (floc NSP.u9) (falloc NSP.u9) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc NSP.u8) (falloc NSP.u8) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot snd-stash) (floc NSP.u7) (falloc NSP.u7) tt)
     (trans (exec-abstract-preserves-heap-ref store-indirect (floc NSP.u6) (falloc NSP.u6) tt)
     (trans (exec-abstract-preserves-heap-ref (load-from-slot fst-stash) (floc NSP.u5) (falloc NSP.u5) tt)
     (trans (exec-abstract-preserves-heap-ref mov-to-input (floc NSP.u4) (falloc NSP.u4) tt)
            (exec-abstract-preserves-heap-ref (store-at-slot pair-stash) (floc NSP.u3) (falloc NSP.u3) tt))))))

    heapref-gs≤ : next-heap-ref (falloc gs) ≤ next-heap-ref (falloc NSP.u10)
    heapref-gs≤ =
      ≤-trans (≤-reflexive (sym NSP.heapref-u2))
              (≤-trans (n≤1+n (next-heap-ref (falloc NSP.u2)))
                       (≤-reflexive (sym heapref-tail)))

    -- The two mid rows: a stack write and a stack read. Neither allocates and
    -- neither is a frame op.
    cf-mid : current-frame (falloc m2) ≡ current-frame (falloc fsF)
    cf-mid =
      trans (exec-abstract-preserves-frame (restore-input backup) (floc m1) (falloc m1))
            (exec-abstract-preserves-frame (store-at-slot fst-stash) (floc fsF) (falloc fsF))

    heapref-mid : next-heap-ref (falloc m2) ≡ next-heap-ref (falloc fsF)
    heapref-mid =
      trans (exec-abstract-preserves-heap-ref (restore-input backup) (floc m1) (falloc m1) tt)
            (exec-abstract-preserves-heap-ref (store-at-slot fst-stash) (floc fsF) (falloc fsF) tt)

    ------------------------------------------------------------------
    -- Carrying the caller's window `BeforeFrontier (alloc @ n)` forward,
    -- one segment at a time.
    ------------------------------------------------------------------
    n≤f-start : n ≤ f-start
    n≤f-start =
      ≤-trans (n≤1+n n)
              (≤-trans (n≤1+n (suc n))
                       (≤-trans (n≤1+n (suc (suc n))) (n≤1+n (suc (suc (suc n))))))

    -- … to `f`'s own frontier, which is where `f`'s hypothesis speaks.
    bf-f : ∀ (loc : ValueLocation FS)
         → BeforeFrontier (record alloc { next-slot = n }) loc
         → BeforeFrontier (record alloc { next-slot = f-start }) loc
    bf-f = frontier-monotone (record alloc { next-slot = n })
                             (record alloc { next-slot = f-start })
                             refl n≤f-start ≤-refl

    bf-after-f : ∀ (m : ℕ) (loc : ValueLocation FS)
               → BeforeFrontier (record alloc { next-slot = m }) loc
               → BeforeFrontier (record (falloc fsF) { next-slot = m }) loc
    bf-after-f = VR.bf-mono vrF

    bf-mid : ∀ (m : ℕ) (loc : ValueLocation FS)
           → BeforeFrontier (record (falloc fsF) { next-slot = m }) loc
           → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
    bf-mid m = frontier-monotone (record (falloc fsF) { next-slot = m })
                                 (record (falloc m2) { next-slot = m })
                                 (sym cf-mid) ≤-refl (≤-reflexive (sym heapref-mid))

    bf-after-g : ∀ (m : ℕ) (loc : ValueLocation FS)
               → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
               → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
    bf-after-g = VR.bf-mono vrG

    bf-to-m2 : ∀ (m : ℕ) (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = m }) loc
             → BeforeFrontier (record (falloc m2) { next-slot = m }) loc
    bf-to-m2 m loc b = bf-mid m loc (bf-after-f m loc b)

    bf-to-gs : ∀ (m : ℕ) (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = m }) loc
             → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
    bf-to-gs m loc b = bf-after-g m loc (bf-to-m2 m loc b)

    bf-tail : ∀ (m : ℕ) (loc : ValueLocation FS)
            → BeforeFrontier (record (falloc gs) { next-slot = m }) loc
            → BeforeFrontier (record (falloc NSP.u10) { next-slot = m }) loc
    bf-tail m = frontier-monotone (record (falloc gs) { next-slot = m })
                                  (record (falloc NSP.u10) { next-slot = m })
                                  (sym cf-tail) ≤-refl heapref-gs≤

    ------------------------------------------------------------------
    -- D210: FRAMEPRES. The frame does not move: nine rows of it in the tail,
    -- `g`'s own `frame-pres`, two rows in the mid, `f`'s own `frame-pres`.
    -- (The prologue's two rows are already inside `f`'s hypothesis, whose
    -- `alloc` index IS the caller's — `falloc p2` reduces to `alloc`.)
    ------------------------------------------------------------------
    frame-pres-pair : current-frame (falloc NSP.u10) ≡ current-frame alloc
    frame-pres-pair =
      trans cf-tail (trans (VR.frame-pres vrG) (trans cf-mid (VR.frame-pres vrF)))

    ------------------------------------------------------------------
    -- D206: BFMONO, at an ARBITRARY slot bound `m` — which is exactly why
    -- each hypothesis' own `bf-mono` is stated that way: they chain.
    ------------------------------------------------------------------
    bf-mono-pair : ∀ (m : ℕ) (loc : ValueLocation FS)
                 → BeforeFrontier (record alloc { next-slot = m }) loc
                 → BeforeFrontier (record (falloc NSP.u10) { next-slot = m }) loc
    bf-mono-pair m loc b = bf-tail m loc (bf-to-gs m loc b)

    ------------------------------------------------------------------
    -- D208: STACKPRES / HEAPPRES. The two halves of ONE five-segment `trans`
    -- chain, so they are derived from it rather than proved twice.
    --
    -- The two freshness read-backs `rdi6`/`rdi8` are the only thing the
    -- memory argument needs that this cluster does not prove: they say the
    -- pointer the two indirect stores write through IS the block row 3
    -- allocated. They are register facts about `NSP.u6`/`NSP.u8` and belong
    -- with the `place` cluster, so they enter here as parameters.
    ------------------------------------------------------------------
    ------------------------------------------------------------------
    -- plan 0.97: THE SAME CHAIN, STOPPED SHORT. If `g` ends the program the
    -- nine-row tail never executes, so the preservation argument is needed at
    -- `gs` — and at `fsF`, for the run that stops inside `f`. These are the
    -- SAME legs `mem-pres-pair` spends, named at the two earlier boundaries
    -- rather than re-proved. (`mem-pres-to-fsF` does not mention `vrG`; only
    -- this module's telescope does, which is why the `f`-stopped clause
    -- rebuilds it from the prologue instead of instantiating `PairPres`.)
    ------------------------------------------------------------------
    mem-pres-to-fsF : ∀ (loc : ValueLocation FS)
                    → BeforeFrontier (record alloc { next-slot = n }) loc
                    → MemOps.readLoc (floc fsF) loc ≡ MemOps.readLoc s loc
    mem-pres-to-fsF loc b =
      trans (vr-mem-pres vrF loc (bf-f loc b))
      (trans (store-slot-preserves-before backup (floc p1)
                (record alloc { next-slot = n }) (falloc p1) loc
                (exec-abstract-preserves-frame mov-to-output s alloc) ≤-refl b)
             (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl))

    w-g-outer : ∀ (loc : ValueLocation FS)
              → BeforeFrontier (record alloc { next-slot = n }) loc
              → BeforeFrontier (record (falloc m2) { next-slot = n1 }) loc
    w-g-outer loc b =
      frontier-monotone (record (falloc m2) { next-slot = n })
                        (record (falloc m2) { next-slot = n1 })
                        refl n≤n1 ≤-refl
                        loc (bf-to-m2 n loc b)

    mem-pres-to-gs : ∀ (loc : ValueLocation FS)
                   → BeforeFrontier (record alloc { next-slot = n }) loc
                   → MemOps.readLoc (floc gs) loc ≡ MemOps.readLoc s loc
    mem-pres-to-gs loc b =
      trans (vr-mem-pres vrG loc (w-g-outer loc b))
      (trans (mem-untouched (restore-input backup) (floc m1) (falloc m1) loc
                Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
      (trans (store-slot-preserves-before fst-stash (floc fsF)
                (record alloc { next-slot = n }) (falloc fsF) loc
                (VR.frame-pres vrF) (n≤1+n n) b)
             (mem-pres-to-fsF loc b)))

    frame-pres-to-gs : current-frame (falloc gs) ≡ current-frame alloc
    frame-pres-to-gs =
      trans (VR.frame-pres vrG) (trans cf-mid (VR.frame-pres vrF))

    module Fill
      (rdi6 : sv-as-loc (readReg (regs (floc NSP.u6)) Input1) ≡ just (AtDynamic NSP.hl))
      (rdi8 : sv-as-loc (readReg (regs (floc NSP.u8)) Input1) ≡ just (AtDynamic NSP.hl))
      where

      -- the window, at the two allocators the two sub-arguments speak of
      w-gs : ∀ (loc : ValueLocation FS)
           → BeforeFrontier (record alloc { next-slot = n }) loc
           → BeforeFrontier (record (falloc gs) { next-slot = snd-stash }) loc
      w-gs loc b =
        frontier-monotone (record (falloc gs) { next-slot = n })
                          (record (falloc gs) { next-slot = snd-stash })
                          refl (≤-trans (n≤1+n n) (n≤1+n (suc n))) ≤-refl
                          loc (bf-to-gs n loc b)

      w-g : ∀ (loc : ValueLocation FS)
          → BeforeFrontier (record alloc { next-slot = n }) loc
          → BeforeFrontier (record (falloc m2) { next-slot = n1 }) loc
      w-g loc b =
        frontier-monotone (record (falloc m2) { next-slot = n })
                          (record (falloc m2) { next-slot = n1 })
                          refl n≤n1 ≤-refl
                          loc (bf-to-m2 n loc b)

      mem-pres-pair : ∀ (loc : ValueLocation FS)
                    → BeforeFrontier (record alloc { next-slot = n }) loc
                    → MemOps.readLoc (floc NSP.u10) loc ≡ MemOps.readLoc s loc
      mem-pres-pair loc b =
        -- (5) the nine-instruction tail: two stack writes at `snd-stash` and
        --     `pair-stash`, two heap writes into the block it just allocated.
        trans (NSP.mem-pres-from
                 nhw-load-from-slot refl nhw-load-from-slot refl
                 ≤-refl rdi6 rdi8 loc (w-gs loc b))
        -- (4) `g`'s run, at `g`'s own emission frontier `n1`
       (trans (vr-mem-pres vrG loc (w-g loc b))
        -- (3b) `restore-input backup` — a register write; no memory at all
       (trans (mem-untouched (restore-input backup) (floc m1) (falloc m1) loc
                 Once.CCC.Machine.SMPrimitives.nhw-restore-input refl)
        -- (3a) `store-at-slot fst-stash` — slot `suc n`, ABOVE the window
       (trans (store-slot-preserves-before fst-stash (floc fsF)
                 (record alloc { next-slot = n }) (falloc fsF) loc
                 (VR.frame-pres vrF) (n≤1+n n) b)
        -- (2) `f`'s run, at `f`'s own emission frontier `f-start = n + 4`
       (trans (vr-mem-pres vrF loc (bf-f loc b))
        -- (1b) `store-at-slot backup` — slot `n`, the window's own bound
       (trans (store-slot-preserves-before backup (floc p1)
                 (record alloc { next-slot = n }) (falloc p1) loc
                 (exec-abstract-preserves-frame mov-to-output s alloc) ≤-refl b)
        -- (1a) `mov-to-output` — a register write
              (mem-untouched mov-to-output s alloc loc nhw-mov-to-output refl))))))

      stack-pres-pair : ∀ (fr : FrameSemantics.Frame FS) (j : ℕ)
                      → BeforeFrontier (record alloc { next-slot = n }) (AtStack fr j)
                      → MemOps.readLoc (floc NSP.u10) (AtStack fr j)
                        ≡ MemOps.readLoc s (AtStack fr j)
      stack-pres-pair fr j = mem-pres-pair (AtStack fr j)

      heap-pres-pair : ∀ (hl : HeapLocation)
                     → BeforeFrontier (record alloc { next-slot = n }) (AtDynamic hl)
                     → MemOps.readLoc (floc NSP.u10) (AtDynamic hl)
                       ≡ MemOps.readLoc s (AtDynamic hl)
      heap-pres-pair hl = mem-pres-pair (AtDynamic hl)

  ----------------------------------------------------------------------
  -- THE TRACE HALF, as its own cluster.
  --
  -- `evalᴰ ⟨ f , g ⟩ a = evalᴰ f a >>=T λ b → evalᴰ g a >>=T λ c → returnT (b , c)`
  -- — TWO nested binds, so the budget threads twice and `returnT` contributes
  -- a `++ []` the outer `take` must be told to ignore. On the machine side the
  -- emitted trace is `pre ++ ft ++ mid ++ gt ++ tail` where every row outside
  -- the two sub-IR fragments is a register/memory op, emitting nothing.
  --
  -- So both sides are the SAME concatenation observed at `k`, with `g`'s
  -- budget threaded as `k ∸ length (projTrace (evalᴰ f x) k)` — which is
  -- exactly the budget `ihg` is instantiated at. `take-++-threaded` splits
  -- each side, and `minus-take` says the residual budget cannot tell whether
  -- the prefix was truncated (D203). Structurally this is `Comp.agda`'s
  -- `traces` field with one extra step: pair's trailing `returnT`.
  ----------------------------------------------------------------------
  module PairTrace {A B C : IRTy} (f : IR A B) (g : IR A C)
                   (x : ⟦ A ⟧) (k : ℕ) where

    -- `List` and `++-identityʳ` are not in the Prelude's re-export list; kept
    -- local to this module so no other cluster's header is disturbed.
    -- plan 0.91 S2: `List` now comes from the prelude (it is needed there for
    -- `BlocksAt`), and a second local binding of the same datatype is an
    -- ambiguity rather than a shadow.
    open import Data.List.Properties using (++-identityʳ)

    -- The denotation's two segments and the budget between them.
    dEvF : List SigOpEvent
    dEvF = projTrace (evalᴰ f x) k

    -- What `f` LEFT of the budget — the number `ihg` must be applied at.
    kg : ℕ
    kg = k ∸ length dEvF

    dEvG : List SigOpEvent
    dEvG = projTrace (evalᴰ g x) kg

    -- THE INNER BIND, NAMED. `⟨ f , g ⟩` is a bind of a bind, and plan 0.97
    -- made the outer one's concatenation depend on whether `f` stopped — so
    -- the middle term can no longer be left implicit. Naming it lets the
    -- split be stated for BOTH outcomes with the same `join-es`.
    innerT : TM.T ⟦ B IRTy.* C ⟧
    innerT = evalᴰ g x TM.>>=T λ c → TM.returnT (TM.valueT (evalᴰ f x) k , c)

    dEvI : List SigOpEvent
    dEvI = projTrace innerT kg

    -- The inner bind's own trace is `g`'s: `returnT` emits nothing, whether
    -- or not `g` stopped (`join-es _ dEvG []`).
    inner-eq : ∀ (sg : TM.Stopped) → TM.stoppedT (evalᴰ g x) kg ≡ sg → dEvI ≡ dEvG
    inner-eq false q = trans (cong (λ z → TM.join-es z dEvG []) q) (++-identityʳ dEvG)
    inner-eq true  q = cong (λ z → TM.join-es z dEvG []) q

    dEvI≡dEvG : dEvI ≡ dEvG
    dEvI≡dEvG = inner-eq (TM.stoppedT (evalᴰ g x) kg) refl

    -- THE DENOTATIONAL SPLIT. `_>>=T_` concatenates and threads, so the outer
    -- bind is `dEvF ++ …` — UNLESS `f` stopped, in which case it is `dEvF`
    -- and `g` never ran at all. One equation, both outcomes.
    denot-split-of : ∀ (sf : TM.Stopped) → TM.stoppedT (evalᴰ f x) k ≡ sf
                   → projTrace (evalᴰ ⟨ f , g ⟩ x) k ≡ TM.join-es sf dEvF dEvG
    denot-split-of sf q = trans (cong (λ z → TM.join-es z dEvF dEvI) q)
                                (cong (TM.join-es sf dEvF) dEvI≡dEvG)

    denot-split : TM.stoppedT (evalᴰ f x) k ≡ false
                → projTrace (evalᴰ ⟨ f , g ⟩ x) k ≡ dEvF ++ dEvG
    denot-split = denot-split-of false

    -- …and the stopped one: `f`'s events ARE the pair's.
    denot-split-stopped : TM.stoppedT (evalᴰ f x) k ≡ true
                        → projTrace (evalᴰ ⟨ f , g ⟩ x) k ≡ dEvF
    denot-split-stopped = denot-split-of true

    -- D203's key fact: truncating `f`'s prefix does not change what is left.
    budget-eq : k ∸ length (take k dEvF) ≡ kg
    budget-eq = TM.minus-take k dEvF

    ------------------------------------------------------------------------
    -- THE CORE, at the level of event LISTS — no machine, no chain. Given
    -- the two fragments' own agreements (each at ITS budget), the composite
    -- agrees at `k`.
    ------------------------------------------------------------------------
    pair-traces-of-events :
      ∀ (mEvF mEvG : List SigOpEvent)
      → TM.stoppedT (evalᴰ f x) k ≡ false
      → take k  mEvF ≡ take k  dEvF
      → take kg mEvG ≡ take kg dEvG
      → take k (mEvF ++ mEvG) ≡ take k (projTrace (evalᴰ ⟨ f , g ⟩ x) k)
    pair-traces-of-events mEvF mEvG qf tf tg =
      trans (TM.take-++-threaded k mEvF mEvG)
      (trans (cong₂ _++_ tf tail-eq)
      (trans (sym (TM.take-++-threaded k dEvF dEvG))
             (sym (cong (take k) (denot-split qf)))))
      where
        tail-eq : take (k ∸ length (take k mEvF)) mEvG
                ≡ take (k ∸ length (take k dEvF)) dEvG
        tail-eq =
          trans (cong (λ m → take (k ∸ length m) mEvG) tf)
          (trans (cong (λ j → take j mEvG) budget-eq)
          (trans tg
                 (sym (cong (λ j → take j dEvG) budget-eq))))

    ------------------------------------------------------------------------
    -- The same, over a chain whose events the caller has already split. This
    -- is the form to use if the assembled chain is nested differently from
    -- the five-segment splice below: supply the split, however it is proved.
    ------------------------------------------------------------------------
    pair-traces-of-split :
      ∀ {prog : AbstractTrace} {kk : ℕ} {st st' : FlatState}
        (c : FlatSteps prog kk st st')
        (mEvF mEvG : List SigOpEvent)
      → chain-events c ≡ mEvF ++ mEvG
      → TM.stoppedT (evalᴰ f x) k ≡ false
      → take k  mEvF ≡ take k  dEvF
      → take kg mEvG ≡ take kg dEvG
      → take k (chain-events c) ≡ take k (projTrace (evalᴰ ⟨ f , g ⟩ x) k)
    pair-traces-of-split c mEvF mEvG es qf tf tg =
      trans (cong (take k) es) (pair-traces-of-events mEvF mEvG qf tf tg)

    ------------------------------------------------------------------------
    -- THE FIVE-SEGMENT SPLICE. `pre ∙ ft ∙ mid ∙ gt ∙ tail`, right-nested —
    -- the shape `FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS
    -- (FlatSteps-++ cG tailS)))` — with the three emitter-owned segments
    -- silent. (For a concrete chain of register/memory rows each silence
    -- premise is `refl`: `ev-of-loc` returns `[]` for every non-`instr-sigop`,
    -- which is how `Sum`'s ten-step build discharges its own trace half.)
    ------------------------------------------------------------------------
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

    ------------------------------------------------------------------------
    -- THE FIELD. Everything above, assembled at the standard nesting: this
    -- IS `traces-agree` for `⟨ f , g ⟩`, given the two sub-runs' own trace
    -- agreements and the three silence facts.
    ------------------------------------------------------------------------
    pair-traces :
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
      → TM.stoppedT (evalᴰ f x) k ≡ false
      → take k  (chain-events cF) ≡ take k  dEvF
      → take kg (chain-events cG) ≡ take kg dEvG
      → take k (chain-events (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS (FlatSteps-++ cG tailS)))))
        ≡ take k (projTrace (evalᴰ ⟨ f , g ⟩ x) k)
    pair-traces preS cF midS cG tailS pre[] mid[] tail[] qf tf tg =
      pair-traces-of-split
        (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS (FlatSteps-++ cG tailS))))
        (chain-events cF) (chain-events cG)
        (pair-chain-events preS cF midS cG tailS pre[] mid[] tail[])
        qf tf tg

    ------------------------------------------------------------------------
    -- plan 0.97: THE RUN THAT STOPS INSIDE `f`. Two segments, not five: the
    -- prologue and `f` itself. The pair's observable IS `f`'s.
    ------------------------------------------------------------------------
    pair-traces-stopped :
      ∀ {prog : AbstractTrace} {kP kF : ℕ} {e0 s1 s2 : FlatState}
        (preS : FlatSteps prog kP e0 s1) (cF : FlatSteps prog kF s1 s2)
      → chain-events preS ≡ []
      → TM.stoppedT (evalᴰ f x) k ≡ true
      → take k (chain-events cF) ≡ take k dEvF
      → take k (chain-events (FlatSteps-++ preS cF))
        ≡ take k (projTrace (evalᴰ ⟨ f , g ⟩ x) k)
    pair-traces-stopped preS cF pre[] qf tf =
      trans (cong (take k)
              (trans (chain-events-++ preS cF)
                     (cong (_++ chain-events cF) pre[])))
      (trans tf (sym (cong (take k) (denot-split-stopped qf))))

    ------------------------------------------------------------------------
    -- …and THE RUN THAT STOPS INSIDE `g`. Four segments — the tail rows that
    -- assemble the pair never run — but the same two-segment observable,
    -- because a stopped `g` still contributes everything it emitted.
    ------------------------------------------------------------------------
    pair-traces-stopped-g :
      ∀ {prog : AbstractTrace} {kP kF kM kG : ℕ} {e0 s1 s2 s3 s4 : FlatState}
        (preS : FlatSteps prog kP e0 s1) (cF : FlatSteps prog kF s1 s2)
        (midS : FlatSteps prog kM s2 s3) (cG : FlatSteps prog kG s3 s4)
      → chain-events preS ≡ []
      → chain-events midS ≡ []
      → TM.stoppedT (evalᴰ f x) k ≡ false
      → take k  (chain-events cF) ≡ take k  dEvF
      → take kg (chain-events cG) ≡ take kg dEvG
      → take k (chain-events (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG))))
        ≡ take k (projTrace (evalᴰ ⟨ f , g ⟩ x) k)
    pair-traces-stopped-g preS cF midS cG pre[] mid[] qf tf tg =
      pair-traces-of-split
        (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG)))
        (chain-events cF) (chain-events cG) es qf tf tg
      where
        ev-after-f : chain-events (FlatSteps-++ midS cG) ≡ chain-events cG
        ev-after-f = trans (chain-events-++ midS cG)
                           (cong (_++ chain-events cG) mid[])

        es : chain-events (FlatSteps-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG)))
           ≡ chain-events cF ++ chain-events cG
        es = trans (chain-events-++ preS (FlatSteps-++ cF (FlatSteps-++ midS cG)))
             (trans (cong (_++ chain-events (FlatSteps-++ cF (FlatSteps-++ midS cG))) pre[])
             (trans (chain-events-++ cF (FlatSteps-++ midS cG))
                    (cong (chain-events cF ++_) ev-after-f)))

