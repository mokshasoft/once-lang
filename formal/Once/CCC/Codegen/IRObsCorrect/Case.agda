-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Case
--
-- plan 0.88: `case f g` — THE ONE CONSTRUCTOR WITH CONTROL FLOW.
--
--   c-branch-tag-zero (ℓ o l) ∷ load-indirect-suc ∷ mov-to-input ∷
--   gt ++
--   c-jmp (ℓ o (suc l)) ∷ c-label (ℓ o l) ∷ load-indirect-suc ∷ mov-to-input ∷
--   ft ++
--   c-label (ℓ o (suc l)) ∷ []
--
-- Note the INVERSION: the trace runs `g` first, because the branch tests for
-- the `inl` tag and jumps FORWARD over `g`'s arm to reach `f`'s. The emitter
-- nonetheless generates `f` first (`ir-to-trace' n (suc (suc l)) f`, then `g`
-- at its outputs), so labels and blocks are ordered `f`-then-`g` while the
-- text is ordered `g`-then-`f`. Every split below has to keep those two
-- orders straight; `Pair` never had to, because there the two agree.
--
-- The two arms CONVERGE. `inl` jumps to `c-label (ℓ o l)`, runs the two
-- unpack rows and `ft`, and falls through the final `c-label`; `inr` falls
-- through the branch, runs the unpack rows and `gt`, and `c-jmp` carries it to
-- that same final label. Both leave the pc at `base + length (emitted …)`,
-- which is what `ValueRealized.at-end` asks for regardless of the tag.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.IRObsCorrect.Case (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in; LabelsIn; LabelIn; li-none; li-lab; in-range)
open import Once.CCC.Codegen.LabelRange o using (label-mono)
open import Once.CCC.Label using (idx)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label)
open import Data.Nat.Properties using (1+n≰n)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Sum using (inj₁; inj₂)
open import Once.IRTy using () renaming (_+_ to _+ᵀ_)
open import Data.Nat using (s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IR
import Once.CCC.Eval as Ev
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.Denotation.TraceMonad as TM

module CaseC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix; flat-step1;
                                flat-tag-branch-yes; flat-tag-branch-not; flat-jmp; flat-label)
  open Resolve {FS} using (found-in-window; noLabel-outside; NoLabel; fl-hit)
  open ClosureWellFormedDef {FS} using (SumTag)

  ----------------------------------------------------------------------
  -- THE SHAPE, and the four premise splits that ride on it.
  ----------------------------------------------------------------------
  module CaseShape {A B C : IRTy} (f : IR A C) (g : IR B C) (n l : ℕ) where

    -- `f` is emitted FIRST, two labels up; `g` continues from its outputs.
    ft : AbstractTrace
    ft = emitted n (suc (suc l)) f

    n1 l1 : ℕ
    n1 = proj₁ (ir-to-trace' n (suc (suc l)) f)
    l1 = proj₁ (proj₂ (ir-to-trace' n (suc (suc l)) f))

    gt : AbstractTrace
    gt = emitted n1 l1 g

    pre mid post : AbstractTrace
    pre  = instr-ctrl (c-branch-tag-zero (ℓ o l)) ∷ load-indirect-suc ∷ mov-to-input ∷ []
    mid  = instr-ctrl (c-jmp (ℓ o (suc l))) ∷ instr-ctrl (c-label (ℓ o l)) ∷
           load-indirect-suc ∷ mov-to-input ∷ []
    post = instr-ctrl (c-label (ℓ o (suc l))) ∷ []

    shape : emitted n l (case f g) ≡ pre ++ gt ++ mid ++ ft ++ post
    shape = refl

    ------------------------------------------------------------------
    -- The two label WINDOWS this clause itself occupies: `ℓ o l` (the
    -- `inl` entry) and `ℓ o (suc l)` (the join). Both sit BELOW the
    -- children's base `suc (suc l)`, which is exactly what lets a scan for
    -- one of `f`'s or `g`'s labels pass the branch row and the mid row.
    ------------------------------------------------------------------
    pre-li : LabelsIn l (suc (suc l)) pre
    pre-li = li-lab refl ≤-refl (s≤s (n≤1+n l)) ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ

    mid-li : LabelsIn l (suc (suc l)) mid
    mid-li = li-lab refl (n≤1+n l) ≤-refl
           ∷ᴬ li-lab refl ≤-refl (s≤s (n≤1+n l))
           ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ []ᴬ

    ------------------------------------------------------------------
    -- THE SPANS. `gt` sits past the three-row branch prologue, `ft` past
    -- that, all of `gt`, and the four-row mid.
    ------------------------------------------------------------------
    span-shift : ∀ (d k b : ℕ) → d + k + b ≡ k + (d + b)
    span-shift d k b = trans (cong (_+ b) (+-comm d k)) (+-assoc k d b)

    span-g : ∀ (prog : AbstractTrace) (base : ℕ)
           → SpanAt prog base (emitted n l (case f g))
           → SpanAt prog (suc (suc (suc base))) gt
    span-g prog base span k i eq =
      subst (λ m → fetch prog m ≡ just i) (span-shift 3 k base)
            (span (suc (suc (suc k))) i
              (fetch-++-left gt (mid ++ ft ++ post) k i eq))

    fbase : ℕ → ℕ
    fbase b = suc (suc (suc (length gt + suc (suc (suc (suc b))))))

    f-shift : ∀ (base k : ℕ)
            → suc (suc (suc (length gt + suc (suc (suc (suc k))))))  + base
              ≡ k + fbase base
    f-shift base k = solve-it (length gt) base k
      where
        solve-it : ∀ (a b c : ℕ)
                 → suc (suc (suc (a + suc (suc (suc (suc c)))))) + b
                   ≡ c + suc (suc (suc (a + suc (suc (suc (suc b))))))
        solve-it = solve 3 (λ a b c →
          con 3 :+ (a :+ (con 4 :+ c)) :+ b := c :+ (con 3 :+ (a :+ (con 4 :+ b))))
          refl

    span-f : ∀ (prog : AbstractTrace) (base : ℕ)
           → SpanAt prog base (emitted n l (case f g))
           → SpanAt prog (fbase base) ft
    span-f prog base span k i eq =
      subst (λ m → fetch prog m ≡ just i) (f-shift base k)
            (span (suc (suc (suc (length gt + suc (suc (suc (suc k))))))) i
              (trans (fetch-++-right gt (mid ++ ft ++ post) (suc (suc (suc (suc k)))))
                     (fetch-++-left ft post k i eq)))

    ------------------------------------------------------------------
    -- WHERE THE TWO JUMPS LAND.
    --
    -- The `inl` entry `ℓ o l` sits in the mid row, the join `ℓ o (suc l)` in
    -- the final row. Both scans pass `gt` (whose labels are at or above `l1`,
    -- and `l1` is above `suc l` because `f` was emitted first and took two
    -- labels), and the join's scan additionally passes the mid row's own
    -- `c-label (ℓ o l)` — `l ≢ suc l` — and all of `ft`.
    ------------------------------------------------------------------
    just-injL : ∀ {a b : LabelId} → (just a) ≡ (just b) → a ≡ b
    just-injL refl = refl

    l<l1 : suc l ≤ l1
    l<l1 = ≤-trans (n≤1+n (suc l)) (label-mono f n (suc (suc l)))

    noG-l : NoLabel (ℓ o l) gt
    noG-l = noLabel-outside (ℓ o l) gt (labels-in g n1 l1)
              (λ w → 1+n≰n (≤-trans l<l1 (proj₁ w)))

    noG-e : NoLabel (ℓ o (suc l)) gt
    noG-e = noLabel-outside (ℓ o (suc l)) gt (labels-in g n1 l1)
              (λ w → 1+n≰n (≤-trans (label-mono f n (suc (suc l))) (proj₁ w)))

    -- `ft`'s labels start at `suc (suc l)`; the join is one below that.
    noF-e : NoLabel (ℓ o (suc l)) ft
    noF-e = noLabel-outside (ℓ o (suc l)) ft (labels-in f n (suc (suc l)))
              (λ w → 1+n≰n (proj₁ w))

    -- …and the mid row's own label is `ℓ o l`, not the join.
    noMid-e : NoLabel (ℓ o (suc l)) mid
    noMid-e = (λ ()) ∷ᴬ (λ eq → 1+n≰n (≤-reflexive (sym (cong idx (just-injL eq)))))
            ∷ᴬ (λ ()) ∷ᴬ (λ ()) ∷ᴬ []ᴬ

    inl-at : ℕ
    inl-at = 4 + length gt

    join-at : ℕ
    join-at = ((3 + length gt) + 4) + length ft

    inl-scan : find-label (emitted n l (case f g)) (ℓ o l) ≡ just inl-at
    inl-scan = trans (fl-go-skip gt (mid ++ ft ++ post) (ℓ o l) 3 noG-l)
                     (fl-hit (ℓ o l) (load-indirect-suc ∷ mov-to-input ∷ (ft ++ post)) inl-at)

    join-scan : find-label (emitted n l (case f g)) (ℓ o (suc l)) ≡ just join-at
    join-scan =
      trans (fl-go-skip gt (mid ++ ft ++ post) (ℓ o (suc l)) 3 noG-e)
        (trans (fl-go-skip mid (ft ++ post) (ℓ o (suc l)) (3 + length gt) noMid-e)
          (trans (fl-go-skip ft post (ℓ o (suc l)) ((3 + length gt) + 4) noF-e)
                 (fl-hit (ℓ o (suc l)) [] join-at)))

    inl-target : ∀ (prog : AbstractTrace) (base : ℕ)
               → LabelsAt prog base (emitted n l (case f g))
               → find-label prog (ℓ o l) ≡ just (inl-at + base)
    inl-target prog base la = la (ℓ o l) inl-at inl-scan

    join-target : ∀ (prog : AbstractTrace) (base : ℕ)
                → LabelsAt prog base (emitted n l (case f g))
                → find-label prog (ℓ o (suc l)) ≡ just (join-at + base)
    join-target prog base la = la (ℓ o (suc l)) join-at join-scan

    ------------------------------------------------------------------
    -- THE BLOCK CHANNEL. `ir-to-trace' n l (case f g)` ends `… , (fb ++ gb)`
    -- — `f` first, as the EMISSION order has it, not the text order.
    ------------------------------------------------------------------
    blocks-f : ∀ (prog : AbstractTrace) → BlocksAt prog (blocks n l (case f g))
             → BlocksAt prog (blocks n (suc (suc l)) f)
    blocks-f prog bl = proj₁ (++⁻ (blocks n (suc (suc l)) f) bl)

    blocks-g : ∀ (prog : AbstractTrace) → BlocksAt prog (blocks n l (case f g))
             → BlocksAt prog (blocks n1 l1 g)
    blocks-g prog bl = proj₂ (++⁻ (blocks n (suc (suc l)) f) bl)

    ------------------------------------------------------------------
    -- THE LABEL CHANNEL, and it is the one that needed new machinery.
    --
    -- `g` is easy: its text starts three rows in, and the branch row is not a
    -- label DEFINITION (`label-of?` matches `c-label` only — a
    -- `c-branch-tag-zero` is a reference, which is why `once-label-of` sees it
    -- and `label-of?` does not), so the scan walks straight into `gt`.
    --
    -- `f` is where the windows are spent. Its text sits past `gt` AND past the
    -- mid row, and the mid row DEFINES `ℓ o l`. Both misses are
    -- `noLabel-outside`: a label `ft` resolves is at or above `suc (suc l)`,
    -- while `mid`'s two labels are below it and `gt`'s are at or above `l1`.
    ------------------------------------------------------------------
    labels-g : ∀ (prog : AbstractTrace) (base : ℕ)
             → LabelsAt prog base (emitted n l (case f g))
             → LabelsAt prog (suc (suc (suc base))) gt
    labels-g prog base la m j eq =
      subst (λ z → find-label prog m ≡ just z) (+-assoc j 3 base) (la m (j + 3) scan)
      where
        scan : find-label (emitted n l (case f g)) m ≡ just (j + 3)
        scan = fl-go-prefix gt (mid ++ ft ++ post) m 3 (j + 3)
                 (trans (fl-go-shift gt m 3 0) (cong (mmap (_+ 3)) eq))

    labels-f : ∀ (prog : AbstractTrace) (base : ℕ)
             → LabelsAt prog base (emitted n l (case f g))
             → LabelsAt prog (fbase base) ft
    labels-f prog base la m j eq =
      subst (λ z → find-label prog m ≡ just z) arith (la m (j + off) scan)
      where
        off : ℕ
        off = (3 + length gt) + 4

        inW : (suc (suc l) ≤ idx m) × (idx m < l1)
        inW = found-in-window ft m j eq (labels-in f n (suc (suc l)))

        noG : NoLabel m gt
        noG = noLabel-outside m gt (labels-in g n1 l1)
                (λ w → 1+n≰n (≤-trans (proj₂ inW) (proj₁ w)))

        noMid : NoLabel m mid
        noMid = noLabel-outside m mid mid-li
                  (λ w → 1+n≰n (≤-trans (proj₂ w) (proj₁ inW)))

        scan : find-label (emitted n l (case f g)) m ≡ just (j + off)
        scan = trans (fl-go-skip gt (mid ++ ft ++ post) m 3 noG)
                     (trans (fl-go-skip mid (ft ++ post) m (3 + length gt) noMid)
                            (fl-go-prefix ft post m off (j + off)
                               (trans (fl-go-shift ft m off 0) (cong (mmap (_+ off)) eq))))

        arith : (j + off) + base ≡ j + fbase base
        arith = trans (+-assoc j off base) (cong (j +_) (solve-it (length gt) base))
          where
            solve-it : ∀ (a b : ℕ)
                     → ((3 + a) + 4) + b
                       ≡ suc (suc (suc (a + suc (suc (suc (suc b))))))
            solve-it = solve 2 (λ a b →
              ((con 3 :+ a) :+ con 4) :+ b := con 3 :+ (a :+ (con 4 :+ b))) refl

  ----------------------------------------------------------------------
  -- THE BRANCH READS THE INPUT'S OWN TAG.
  --
  -- `flat-read-tag s` is `readLoc s loc` at the location `Input1` points to,
  -- and `valid-inl-wf`/`valid-inr-wf` carry exactly that read — `SumTag m t s
  -- sum-loc` IS `readLoc s sum-loc ≡ just (SV-Tag t)`. So the branch condition
  -- is not a new fact about the machine; it is the input residence, read.
  --
  -- This is the part plan 0.88 recorded as having "no model anywhere". It does
  -- not need one: the tag the emitter wrote in `inl`/`inr` is the tag the
  -- validity witness remembers, and `flat-tag-branch-yes`/`-not` take it.
  ----------------------------------------------------------------------

  -- `SumTag` is defined BY CASES on the mode, so it is stuck on the abstract
  -- `mIn` a clause is handed. Both cases are the same equation.
  sumTag-read : ∀ (m : AllocMode) (t : ℕ) (s : LocState FS) (loc : ValueLocation FS)
              → SumTag m t s loc → readLoc s loc ≡ just (SV-Tag t)
  sumTag-read Heap  t s loc e = e
  sumTag-read Stack t s loc e = e

  tag-inl : ∀ {A B} {a : ⟦ A ⟧} {m : AllocMode} {alloc : AllocState {FS}}
              {loc : ValueLocation FS} {s : LocState FS}
          → ValidAtWF m alloc {A +ᵀ B} (inj₁ a) loc s
          → readReg (regs s) Input1 ≡ SV-Ptr loc
          → tag-zf (flat-read-tag s) ≡ true
  tag-inl {m = m} {loc = loc} {s = s} (valid-inl-wf _ tg _ _ _ _) rd
    rewrite rd = cong tag-zf (sumTag-read m 0 s loc tg)
  tag-inl {m = m} {loc = loc} {s = s} (valid-inl-reg-wf _ tg _ _ _) rd
    rewrite rd = cong tag-zf (sumTag-read m 0 s loc tg)

  tag-inr : ∀ {A B} {b : ⟦ B ⟧} {m : AllocMode} {alloc : AllocState {FS}}
              {loc : ValueLocation FS} {s : LocState FS}
          → ValidAtWF m alloc {A +ᵀ B} (inj₂ b) loc s
          → readReg (regs s) Input1 ≡ SV-Ptr loc
          → tag-zf (flat-read-tag s) ≡ false
  tag-inr {m = m} {loc = loc} {s = s} (valid-inr-wf _ tg _ _ _ _) rd
    rewrite rd = cong tag-zf (sumTag-read m 1 s loc tg)
  tag-inr {m = m} {loc = loc} {s = s} (valid-inr-reg-wf _ tg _ _ _) rd
    rewrite rd = cong tag-zf (sumTag-read m 1 s loc tg)

  -- …AND THE UNPACK ROW IS WELL-FORMED FOR THE SAME REASON. `load-indirect-suc`
  -- owes `InstrWF`: `Input1` must resolve to a location whose successor cell
  -- can be read. For a sum that IS the residence — the payload cell — so the
  -- witness is the validity's own `readLoc s (sucLoc sum-loc)` field, in all
  -- four shapes (pointer or inline payload, either tag).
  unpack-wf : ∀ {A' B' : IRTy} {v : ⟦ A' +ᵀ B' ⟧} {m : AllocMode}
                {alloc : AllocState {FS}} {loc : ValueLocation FS} {s' : LocState FS}
            → ValidAtWF m alloc {A' +ᵀ B'} v loc s'
            → readReg (regs s') Input1 ≡ SV-Ptr loc
            → InstrWF s' alloc load-indirect-suc
  unpack-wf {loc = loc} (valid-inl-wf _ _ r _ _ _)   rd = loc , cong sv-as-loc rd , (_ , r)
  unpack-wf {loc = loc} (valid-inr-wf _ _ r _ _ _)   rd = loc , cong sv-as-loc rd , (_ , r)
  unpack-wf {loc = loc} (valid-inl-reg-wf _ _ _ r _) rd = loc , cong sv-as-loc rd , (_ , r)
  unpack-wf {loc = loc} (valid-inr-reg-wf _ _ _ r _) rd = loc , cong sv-as-loc rd , (_ , r)

  ----------------------------------------------------------------------
  -- THE RUN. Both arms share the branch row; they differ in whether it is
  -- taken, and they rejoin at the final `c-label`.
  ----------------------------------------------------------------------
  module CaseRun {A B C : IRTy} (f : IR A C) (g : IR B C)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (span : SpanAt prog base (emitted n l (case f g)))
    where

    open CaseShape f g n l

    -- The emitted length, in the form the two arms' end-pcs take.
    len-eq : length (emitted n l (case f g)) ≡ suc join-at
    len-eq = trans step (solve-it (length gt) (length ft))
      where
        step : length (emitted n l (case f g))
             ≡ 3 + (length gt + (4 + (length ft + 1)))
        step = trans (length-++ pre {gt ++ mid ++ ft ++ post})
                 (cong (3 +_)
                   (trans (length-++ gt {mid ++ ft ++ post})
                     (cong (length gt +_)
                       (trans (length-++ mid {ft ++ post})
                              (cong (4 +_) (length-++ ft {post}))))))
        solve-it : ∀ (a b : ℕ) → 3 + (a + (4 + (b + 1))) ≡ suc (((3 + a) + 4) + b)
        solve-it = solve 2 (λ a b →
          con 3 :+ (a :+ (con 4 :+ (b :+ con 1))) := con 1 :+ (((con 3 :+ a) :+ con 4) :+ b))
          refl

    ------------------------------------------------------------------
    -- THE FETCHES. The three straight rows of each arm, the `c-jmp`, and the
    -- two `c-label`s — each read out of `span` at its own offset. Everything
    -- past `gt` goes through one helper, because `fetch-++-right` indexes as
    -- `length gt + j` while the offsets read `j + length gt`.
    ------------------------------------------------------------------
    gt-at : ∀ (j : ℕ) (i : AbstractInstr)
          → fetch (mid ++ ft ++ post) j ≡ just i
          → fetch prog ((3 + (j + length gt)) + base) ≡ just i
    gt-at j i e =
      span (3 + (j + length gt)) i
        (subst (λ z → fetch (gt ++ mid ++ ft ++ post) z ≡ just i)
               (+-comm (length gt) j)
               (trans (fetch-++-right gt (mid ++ ft ++ post) j) e))

    at-branch : fetch prog (0 + base) ≡ just (instr-ctrl (c-branch-tag-zero (ℓ o l)))
    at-branch = span 0 _ refl

    at-unpack-r : fetch prog (1 + base) ≡ just load-indirect-suc
    at-unpack-r = span 1 _ refl

    at-movin-r : fetch prog (2 + base) ≡ just mov-to-input
    at-movin-r = span 2 _ refl

    at-jmp : fetch prog ((3 + length gt) + base) ≡ just (instr-ctrl (c-jmp (ℓ o (suc l))))
    at-jmp = gt-at 0 _ refl

    at-inl-label : fetch prog (inl-at + base) ≡ just (instr-ctrl (c-label (ℓ o l)))
    at-inl-label = gt-at 1 _ refl

    at-unpack-l : fetch prog ((5 + length gt) + base) ≡ just load-indirect-suc
    at-unpack-l = gt-at 2 _ refl

    at-movin-l : fetch prog ((6 + length gt) + base) ≡ just mov-to-input
    at-movin-l = gt-at 3 _ refl

    at-join-label : fetch prog (join-at + base) ≡ just (instr-ctrl (c-label (ℓ o (suc l))))
    at-join-label =
      subst (λ z → fetch prog (z + base) ≡ just (instr-ctrl (c-label (ℓ o (suc l)))))
            (solve-j (length gt) (length ft))
            (gt-at (4 + length ft) _
              (trans (fetch-++-right mid (ft ++ post) (length ft))
                     (subst (λ z → fetch (ft ++ post) z ≡ just (instr-ctrl (c-label (ℓ o (suc l)))))
                            (+-identityʳ (length ft))
                            (fetch-++-right ft post 0))))
      where
        solve-j : ∀ (a b : ℕ) → 3 + ((4 + b) + a) ≡ ((3 + a) + 4) + b
        solve-j = solve 2 (λ a b →
          con 3 :+ ((con 4 :+ b) :+ a) := ((con 3 :+ a) :+ con 4) :+ b) refl

    ------------------------------------------------------------------
    -- THE TWO PROLOGUES. Both are three steps: the branch row, then the
    -- arm's `load-indirect-suc` (Output := the sum's payload cell) and
    -- `mov-to-input` (hand it to the arm). They differ ONLY in whether the
    -- branch falls through or jumps, and that is decided by the input's own
    -- tag — `tag-inr` / `tag-inl`.
    ------------------------------------------------------------------
    module Prologue (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS)
                    (nh : halted s ≡ false)
                    (iwf : InstrWF s alloc load-indirect-suc)
                    (la : LabelsAt prog base (emitted n l (case f g)))
                    where

      fs0 : FlatState
      fs0 = entry-flat base s alloc cl

      -- ── the `inr` arm: the branch falls through.
      r1 r2 r3 : FlatState
      r1 = record fs0 { fpc = suc base }
      r2 = flat-exec-instr load-indirect-suc prog r1
      r3 = flat-exec-instr mov-to-input      prog r2

      nh-r1 : halted (floc r1) ≡ false
      nh-r1 = nh
      nh-r2 : halted (floc r2) ≡ false
      nh-r2 = exec-abstract-preserves-halted-WF load-indirect-suc (floc r1) (falloc r1) nh-r1 iwf

      run-r : tag-zf (flat-read-tag (floc fs0)) ≡ false → FlatSteps prog 3 fs0 r3
      run-r cond =
        FlatSteps-++ (flat-step1 nh at-branch (flat-tag-branch-not prog fs0 (ℓ o l) cond))
                     ((nh-r1 , at-unpack-r) ∷ (nh-r2 , at-movin-r) ∷ [])

      -- ── the `inl` arm: the branch jumps to `ℓ o l`, which is the mid row's
      -- own `c-label`; executing that label is the second step.
      i1 i2 i3 i4 : FlatState
      i1 = record fs0 { fpc = inl-at + base }
      i2 = record i1  { fpc = suc (inl-at + base) }
      i3 = flat-exec-instr load-indirect-suc prog i2
      i4 = flat-exec-instr mov-to-input      prog i3

      nh-i2 : halted (floc i2) ≡ false
      nh-i2 = nh
      nh-i3 : halted (floc i3) ≡ false
      nh-i3 = exec-abstract-preserves-halted-WF load-indirect-suc (floc i2) (falloc i2) nh-i2 iwf

      run-i : tag-zf (flat-read-tag (floc fs0)) ≡ true → FlatSteps prog 4 fs0 i4
      run-i cond =
        FlatSteps-++
          (flat-step1 nh at-branch
            (trans (flat-tag-branch-yes prog fs0 (ℓ o l) cond)
                   (cong (λ mj → do-jump mj fs0) (inl-target prog base la))))
          (FlatSteps-++ (flat-step1 nh at-inl-label refl)
                        ((nh-i2 , at-unpack-l) ∷ (nh-i3 , at-movin-l) ∷ []))
