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

open import Once.CanonicalName using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Pair.Chain (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in)
open import Once.CCC.Label using (idx)
open import Data.Nat.Properties using (1+n≰n)
open import Data.Nat using (s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con)

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
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩))
    {xf : DT.⟦ A ⟧ᴰᴵ} {kf : ℕ}
    (vrf : ValueRealized prog (suc (suc base)) (PairShape.f-start f g n l) l f xf
             (floc (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) (falloc (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) (fclosure (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) kf)
    (sfeq : stopsAt (floc (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) (evalᴰ f xf) ≡ false)
    where
    open PairChain f g n l prog base s alloc cl n≤ nh span


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
  module PairChainG
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (emitted n l ⟨ f , g ⟩))
    {xf : DT.⟦ A ⟧ᴰᴵ} {kf : ℕ}
    (vrf : ValueRealized prog (suc (suc base)) (PairShape.f-start f g n l) l f xf
             (floc (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) (falloc (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) (fclosure (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) kf)
    (sfeq : stopsAt (floc (PairRun.p2 f g n l prog base s alloc cl n≤ nh)) (evalᴰ f xf) ≡ false)
    {xg : DT.⟦ A ⟧ᴰᴵ} {kg : ℕ}
    (vrg : ValueRealized prog (PairChainF.bg f g n l prog base s alloc cl n≤ nh span vrf sfeq) (PairShape.n1 f g n l) (PairShape.l1 f g n l) g xg
             (floc (PairChainF.m2 f g n l prog base s alloc cl n≤ nh span vrf sfeq)) (falloc (PairChainF.m2 f g n l prog base s alloc cl n≤ nh span vrf sfeq)) (fclosure (PairChainF.m2 f g n l prog base s alloc cl n≤ nh span vrf sfeq)) kg)
    (sgeq : stopsAt (floc (PairChainF.m2 f g n l prog base s alloc cl n≤ nh span vrf sfeq)) (evalᴰ g xg) ≡ false)
    where
    open PairChain f g n l prog base s alloc cl n≤ nh span
    open PairChainF f g n l prog base s alloc cl n≤ nh span vrf sfeq


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
    -- Named THROUGH `NineSteps` (profile 2026-09-29), at the arguments
    -- `PairPres`' `NineStepPres` is applied at, so the two families are
    -- the same names rather than two definitionally-equal chains.
    u1 : FlatState
    u1 = fsG
    -- …and at LITERAL arguments (profile 2026-09-30): `PS.snd-stash`,
    -- `PairPlace.snd-stash` and `PairPres.gs`/`fsG` are equal only by
    -- unfolding, and conversion unfolds the nine steps before it gets to
    -- the arguments. Every instantiation spells the same four terms.
    open NineSteps (suc (suc n)) (load-from-slot (suc n)) (load-from-slot (suc (suc n))) (VR.settle vrg)
      using (u2; u3; u4; u5; u6; u7; u8; u9; u10)

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
    -- Every link lands on its NAMED state `uₖ` (`step-at`), so no link's
    -- state is re-derived by conversion (profile 2026-09-29: this chain
    -- was 52% of `PairAssemble.agda`'s checking).
    tail-chain =
        step-at u2  (liveG , tfetch 0 (store-at-slot PS.snd-stash)   refl) refl
      ( step-at u3  (nhU2  , tfetch 1 (instr-alloc-heap 2)           refl) refl
      ( step-at u4  (nhU3  , tfetch 2 (store-at-slot PS.pair-stash)  refl) refl
      ( step-at u5  (nhU4  , tfetch 3 mov-to-input                   refl) refl
      ( step-at u6  (nhU5  , tfetch 4 (load-from-slot PS.fst-stash)  refl) refl
      ( step-at u7  (nhU6  , tfetch 5 store-indirect                 refl) refl
      ( step-at u8  (nhU7  , tfetch 6 (load-from-slot PS.snd-stash)  refl) refl
      ( step-at u9  (nhU8  , tfetch 7 store-indirect-suc             refl) refl
      ( step-at u10 (nhU9  , tfetch 8 (load-from-slot PS.pair-stash) refl) refl
        [] ))))))))

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
