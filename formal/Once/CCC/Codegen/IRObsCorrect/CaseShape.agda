-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CaseShape
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

module Once.CCC.Codegen.IRObsCorrect.CaseShape (o : CanonicalName) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.LabelScope o using (labels-in; LabelsIn; LabelIn; li-none; li-lab; in-range)
open import Once.CCC.Codegen.LabelRange o using (label-mono)
open import Once.CCC.Label using (idx)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-branch-tag-zero; c-jmp; c-label)
open import Data.Nat.Properties using (1+n≰n)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ)
open import Data.List.Properties using () renaming (++-identityʳ to ++-idʳ)
open import Once.IRTy using () renaming (_+_ to _+ᵀ_)
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

------------------------------------------------------------------------
-- THE `+` SHUFFLES, HOISTED TO THE TOP LEVEL.
--
-- Every one of these is a fact about ℕ and nothing else. Left in the `where`
-- blocks that used them, each inherited the whole enclosing telescope — `FS`,
-- both IR morphisms, the frontier and the label base — and was re-elaborated
-- at every module instantiation. That, and not the proofs themselves, is what
-- made this module cost 4.8 GB to typecheck.
--
-- The offsets they relate: the branch row is 3 wide, the mid row 4, the final
-- label 1; `ft` is emitted at `3 + (|gt| + (4 + base))`, the `inl` entry sits
-- at `(4 + |gt|) + base`, and the join at `((3 + |gt|) + 4) + |ft|`.
------------------------------------------------------------------------
-- Public, not private: the second half of this clause lives in `Case` and
-- needs them too.
shuffle-f : ∀ (a b c : ℕ)
          → suc (suc (suc (a + suc (suc (suc (suc c)))))) + b
            ≡ c + suc (suc (suc (a + suc (suc (suc (suc b))))))
shuffle-f = solve 3 (λ a b c →
  con 3 :+ (a :+ (con 4 :+ c)) :+ b := c :+ (con 3 :+ (a :+ (con 4 :+ b)))) refl

shuffle-lf : ∀ (a b : ℕ)
           → ((3 + a) + 4) + b ≡ suc (suc (suc (a + suc (suc (suc (suc b))))))
shuffle-lf = solve 2 (λ a b →
  ((con 3 :+ a) :+ con 4) :+ b := con 3 :+ (a :+ (con 4 :+ b))) refl

shuffle-len : ∀ (a b : ℕ) → 3 + (a + (4 + (b + 1))) ≡ suc (((3 + a) + 4) + b)
shuffle-len = solve 2 (λ a b →
  con 3 :+ (a :+ (con 4 :+ (b :+ con 1))) := con 1 :+ (((con 3 :+ a) :+ con 4) :+ b)) refl

shuffle-join : ∀ (a b : ℕ) → 3 + ((4 + b) + a) ≡ ((3 + a) + 4) + b
shuffle-join = solve 2 (λ a b →
  con 3 :+ ((con 4 :+ b) :+ a) := ((con 3 :+ a) :+ con 4) :+ b) refl

shuffle-jmp : ∀ (a b : ℕ) → a + (3 + b) ≡ (3 + a) + b
shuffle-jmp = solve 2 (λ a b → a :+ (con 3 :+ b) := (con 3 :+ a) :+ b) refl

shuffle-i4 : ∀ (a b : ℕ) → 3 + ((4 + a) + b) ≡ 3 + (a + (4 + b))
shuffle-i4 = solve 2 (λ a b →
  con 3 :+ ((con 4 :+ a) :+ b) := con 3 :+ (a :+ (con 4 :+ b))) refl

shuffle-end : ∀ (a b c : ℕ) → b + (3 + (a + (4 + c))) ≡ (((3 + a) + 4) + b) + c
shuffle-end = solve 3 (λ a b c →
  b :+ (con 3 :+ (a :+ (con 4 :+ c))) := (((con 3 :+ a) :+ con 4) :+ b) :+ c) refl


module ShapeC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open FlatStepsAPI {FS} using (fl-go-skip; fl-go-shift; fl-go-prefix; flat-step1;
                                flat-tag-branch-yes; flat-tag-branch-not; flat-jmp; flat-label)
  open Resolve {FS} using (found-in-window; noLabel-outside; NoLabel; fl-hit)
  open ClosureWellFormedDef {FS} using (SumTag; InlineRep; rep-prim; rep-unit)

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
    f-shift base k = shuffle-f (length gt) base k

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
        arith = trans (+-assoc j off base) (cong (j +_) (shuffle-lf (length gt) base))

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

  -- WHAT THE UNPACK ROW PUTS IN `Output`: the payload cell, verbatim. The
  -- `with`-chain is `load-ind-suc-preserves-input`'s (Machine.agda:72) — the
  -- two resolutions have to be forced before `exec-load-with-value` reduces.
  load-suc-out : ∀ (s' : LocState FS) (alloc' : AllocState {FS})
                   (loc : ValueLocation FS) (v : StoredValue FS)
               → sv-as-loc (readReg (regs s') Input1) ≡ just loc
               → readLoc s' (sucLoc loc) ≡ just v
               → readReg (regs (proj₁ (exec-abstract load-indirect-suc s' alloc'))) Output ≡ v
  load-suc-out s' alloc' loc v eq cell
    with sv-as-loc (readReg (regs s') Input1) | eq
  ... | .(just loc) | refl with readLoc s' (sucLoc loc) | cell
  ...   | .(just v) | refl = writeReg-same (regs s') Output v

  ----------------------------------------------------------------------
  -- THE ARM'S INPUT. After the two unpack rows, `Input1` holds the payload —
  -- which is exactly the residence the arm's `IRObsCorrectF` asks for. The
  -- mode is the PAYLOAD's, not the sum's, so it comes back existentially: a
  -- pointer payload lands in `in-loc`, an inline one in `in-reg`.
  --
  -- Neither row touches memory (`load-indirect-suc` reads it, `mov-to-input`
  -- moves a register), so the payload's own `ValidAtWF` transports unchanged.
  ----------------------------------------------------------------------
  mem-unpack : ∀ (s' : LocState FS) (alloc' : AllocState {FS}) (lc : ValueLocation FS)
             → readLoc (proj₁ (exec-abstract load-indirect-suc s' alloc')) lc ≡ readLoc s' lc
  mem-unpack s' alloc' lc = mem-untouched load-indirect-suc s' alloc' lc nhw-load-indirect-suc refl

  arm-input-l : ∀ {A' B' : IRTy} {a : ⟦ A' ⟧} {m : AllocMode} {alloc : AllocState {FS}}
                  {loc : ValueLocation FS} {s' : LocState FS} (s'' : LocState FS)
              → ValidAtWF m alloc {A' +ᵀ B'} (inj₁ a) loc s'
              → readReg (regs s') Input1 ≡ SV-Ptr loc
              → readReg (regs s'') Input1
                ≡ readReg (regs (proj₁ (exec-abstract load-indirect-suc s' alloc))) Output
              → (∀ lc → readLoc s'' lc ≡ readLoc s' lc)
              → Σ AllocMode (λ mA → InputAt mA alloc a s'')
  arm-input-l {alloc = alloc} {loc = loc} {s' = s'} s''
              (valid-inl-wf {payload-loc = pl} {mA = mA} _ _ r bfp _ va) rd mv me =
    mA , in-loc pl (validityWF-mem-preserved _ pl s' s'' bfp (λ lc _ → me lc) va) bfp
           (trans mv (load-suc-out s' alloc loc (SV-Ptr pl) (cong sv-as-loc rd) r))
  -- An INLINE payload is either a register-fitting primitive or a unit, and
  -- `InputAt` has a constructor for each — `in-reg` and `in-unit`.
  arm-input-l {alloc = alloc} {loc = loc} {s' = s'} s''
              (valid-inl-reg-wf _ _ (rep-prim fit) r _) rd mv me =
    Heap , in-reg fit (trans mv (load-suc-out s' alloc loc _ (cong sv-as-loc rd) r))
  arm-input-l s'' (valid-inl-reg-wf _ _ (rep-unit e _) _ _) _ _ _ = Heap , in-unit e

  arm-input-r : ∀ {A' B' : IRTy} {b : ⟦ B' ⟧} {m : AllocMode} {alloc : AllocState {FS}}
                  {loc : ValueLocation FS} {s' : LocState FS} (s'' : LocState FS)
              → ValidAtWF m alloc {A' +ᵀ B'} (inj₂ b) loc s'
              → readReg (regs s') Input1 ≡ SV-Ptr loc
              → readReg (regs s'') Input1
                ≡ readReg (regs (proj₁ (exec-abstract load-indirect-suc s' alloc))) Output
              → (∀ lc → readLoc s'' lc ≡ readLoc s' lc)
              → Σ AllocMode (λ mB → InputAt mB alloc b s'')
  arm-input-r {alloc = alloc} {loc = loc} {s' = s'} s''
              (valid-inr-wf {payload-loc = pl} {mB = mB} _ _ r bfp _ vb) rd mv me =
    mB , in-loc pl (validityWF-mem-preserved _ pl s' s'' bfp (λ lc _ → me lc) vb) bfp
           (trans mv (load-suc-out s' alloc loc (SV-Ptr pl) (cong sv-as-loc rd) r))
  arm-input-r {alloc = alloc} {loc = loc} {s' = s'} s''
              (valid-inr-reg-wf _ _ (rep-prim fit) r _) rd mv me =
    Heap , in-reg fit (trans mv (load-suc-out s' alloc loc _ (cong sv-as-loc rd) r))
  arm-input-r s'' (valid-inr-reg-wf _ _ (rep-unit e _) _ _) _ _ _ = Heap , in-unit e

  ----------------------------------------------------------------------
  -- THE RUN. Both arms share the branch row; they differ in whether it is
  -- taken, and they rejoin at the final `c-label`.
