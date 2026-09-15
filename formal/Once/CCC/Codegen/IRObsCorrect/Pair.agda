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
open import Data.Nat using (s≤s)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module PairC {FS : FrameSemantics} (program-bound : ℕ) where

  open Core {FS} program-bound
  open Mach {FS} program-bound

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

  ----------------------------------------------------------------------
  -- D209: THE TAIL, instantiated.
  --
  -- The nine instructions after `g`'s run are `NineStepPres` at pair's own
  -- stashes — `n := snd-stash`, so `suc n = pair-stash`, with the two cell
  -- sources as `i6` / `i8`:
  --
  --   store-at-slot snd-stash ∷ instr-alloc-heap 2 ∷
  --   store-at-slot pair-stash ∷ mov-to-input ∷
  --   load-from-slot fst-stash ∷ store-indirect ∷
  --   load-from-slot snd-stash ∷ store-indirect-suc ∷
  --   load-from-slot pair-stash ∷ []
  --
  -- The module is applied to the state `g` settled in, which is exactly what
  -- D209's generalisation over the start state was for: `inl`/`inr`/`curry`/
  -- `Ana` start theirs one `mov-to-output` from entry, `pair` starts it two
  -- sub-IR runs in, and the nine steps are the same nine.
  ----------------------------------------------------------------------
  module PairTail
    {A B C : IRTy} (f : IR A B) (g : IR A C)
    (n : ℕ) (gs : FlatState) (s : LocState FS) (alloc : AllocState {FS})
    (heapref-gs : next-heap-ref (falloc gs) ≡ next-heap-ref alloc)
    (cf-gs      : current-frame (falloc gs) ≡ current-frame alloc)
    where

    -- `n := snd-stash`; `suc n` is then `pair-stash`, as the emitter lays
    -- them out.
    module NSP = NineStepPres (suc (suc n))
                   (load-from-slot (suc n))        -- i6: the fst component
                   (load-from-slot (suc (suc n)))  -- i8: the snd component
                   gs s alloc heapref-gs cf-gs

    -- The pair node the two indirect stores write.
    pair-loc : ValueLocation FS
    pair-loc = AtDynamic NSP.hl

    -- …and it is fresh: `g` left the heap frontier where the caller had it
    -- (`heapref-gs`), and the stash before the allocation does not move it.
    pair-fresh : next-heap-ref alloc ≤ ref-id (heap-ref NSP.hl)
    pair-fresh = NSP.fresh

    -- What the tail leaves alone, relative to `g`'s settled state. Pair's
    -- three stashes are `snd-stash`, `pair-stash` (the tail's own) and
    -- `fst-stash` (read, never written here), all at or above `n`, so the
    -- caller's window below `n` is untouched.
    tail-mem-pres :
        next-slot alloc ≤ suc (suc n)
      → sv-as-loc (readReg (regs (floc NSP.u6)) Input1) ≡ just (AtDynamic NSP.hl)
      → sv-as-loc (readReg (regs (floc NSP.u8)) Input1) ≡ just (AtDynamic NSP.hl)
      → (loc : ValueLocation FS)
      → BeforeFrontier (record alloc { next-slot = suc (suc n) }) loc
      → MemOps.readLoc (floc NSP.u10) loc ≡ MemOps.readLoc (floc gs) loc
    tail-mem-pres ns≤ rdi6 rdi8 =
      NSP.mem-pres-from nhw-load-from-slot refl nhw-load-from-slot refl ns≤ rdi6 rdi8
