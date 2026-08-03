-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.ShapeAt   (Plan 0.62 M1 — gate G1)
--
-- THE SHAPE-LEVEL ERASURE OF `ValidAtWF`: what a representation of an IRTy
-- LOOKS LIKE in memory — written pointer cells, tag cells, literal cells —
-- with the SEMANTIC VALUE dropped and every exact-value equation turned into
-- an existential. This is the typing the dataflow disciplines
-- (`branch-tag-scrutinee-wf`, `load-indirect{,-suc}-target-ptr`) rest on:
-- e.g. "the branch scrutinee points at a written TAG cell" is exactly what
-- `shape-inl`/`shape-inr` say about a sum representation.
--
-- DESIGN CONSTRAINT (D076): `valid→shape` MUST be a plain projection — the
-- value-correctness layer refines this one, so the shape layer must never
-- say anything `ValidAtWF` does not. That is gate G1, proven below.
--
-- Dropped relative to `ValidAtWF`: the value index, `BodyCorrect` and
-- `ir-size body < program-bound` (a closure's SHAPE is its two cells and its
-- env's shape — body correctness is the value layer's business). Kept: the
-- mode index, `LocMatchesMode`, every `readLoc` equation (existential where
-- the value occurred), `BeforeFrontier`, and the μ/ν layer recursion.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.ShapeAt (FS : FrameSemantics) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IRTy; Unit; Int; Float; Str; Buffer; _*_; _+_; _⇛_;
  μ-type; ν-type; ⟦_⟧TI; WellFormedFI)
open import Once.Type using ()
  renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ;
            Int to Intˢ; Float to Floatˢ)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.CCC.Machine.SMCore
  hiding (AllocMode; Stack; Heap)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Machine.Allocation hiding (AllocMode)
open import Once.IR using (AllocMode; Stack; Heap)
open MemOps {FS} using (readLoc)
open FrontierInvariant {FS} using (BeforeFrontier)

-- The sum-tag cell fact, shape form (definitionally equal to
-- `ClosureWellFormedDef.SumTag`, restated here so this module does not
-- depend on `program-bound`). MODE-INDEPENDENT (D078): both modes write
-- the tag.
TagAt : AllocMode → ℕ → LocState FS → ValueLocation FS → Set
TagAt Heap  t s loc = readLoc s loc ≡ just (SV-Tag t)
TagAt Stack t s loc = readLoc s loc ≡ just (SV-Tag t)

-- mode-eliminated read form (both clauses are the same equation)
tag-at-read : ∀ (m : AllocMode) (t : ℕ) (s : LocState FS) (loc : ValueLocation FS)
            → TagAt m t s loc → readLoc s loc ≡ just (SV-Tag t)
tag-at-read Heap  t s loc x = x
tag-at-read Stack t s loc x = x

data ShapeAt : AllocMode → AllocState {FS} →
     IRTy → ValueLocation FS → LocState FS → Set where

  shape-unit : ∀ {m alloc loc s} →
    ShapeAt m alloc Unit loc s

  shape-pair : ∀ {m A B}
    {alloc : AllocState {FS}}
    {pair-loc fst-loc snd-loc : ValueLocation FS} {s : LocState FS}
    {mA mB : AllocMode} →
    LocMatchesMode m pair-loc →
    readLoc s pair-loc ≡ just (SV-Ptr fst-loc) →
    readLoc s (sucLoc pair-loc) ≡ just (SV-Ptr snd-loc) →
    BeforeFrontier alloc fst-loc →
    BeforeFrontier alloc snd-loc →
    BeforeFrontier alloc (sucLoc pair-loc) →
    ShapeAt mA alloc A fst-loc s →
    ShapeAt mB alloc B snd-loc s →
    ShapeAt m alloc (A * B) pair-loc s

  -- a closure's shape: env-pointer cell + code cell + the env's shape (at
  -- its own, EXISTENTIAL type — same non-structural recursion `ValidAtWF`
  -- has, which is why this is a datatype)
  shape-closure : ∀ {m EnvType A B}
    {alloc : AllocState {FS}}
    {closure-loc env-loc : ValueLocation FS} {s : LocState FS}
    {mEnv : AllocMode}
    {body-label : ℕ} →
    LocMatchesMode m closure-loc →
    readLoc s closure-loc ≡ just (SV-Ptr env-loc) →
    readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label) →
    BeforeFrontier alloc env-loc →
    BeforeFrontier alloc (sucLoc closure-loc) →
    ShapeAt mEnv alloc EnvType env-loc s →
    ShapeAt m alloc (A ⇛ B) closure-loc s

  shape-inl : ∀ {m A B}
    {alloc : AllocState {FS}}
    {sum-loc payload-loc : ValueLocation FS} {s : LocState FS}
    {mA : AllocMode} →
    LocMatchesMode m sum-loc →
    TagAt m 0 s sum-loc →
    readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
    BeforeFrontier alloc payload-loc →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ShapeAt mA alloc A payload-loc s →
    ShapeAt m alloc (A + B) sum-loc s

  shape-inr : ∀ {m A B}
    {alloc : AllocState {FS}}
    {sum-loc payload-loc : ValueLocation FS} {s : LocState FS}
    {mB : AllocMode} →
    LocMatchesMode m sum-loc →
    TagAt m 1 s sum-loc →
    readLoc s (sucLoc sum-loc) ≡ just (SV-Ptr payload-loc) →
    BeforeFrontier alloc payload-loc →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ShapeAt mB alloc B payload-loc s →
    ShapeAt m alloc (A + B) sum-loc s

  shape-μ : ∀ {m F}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (wf : WellFormedFI F) →
    ShapeAt m alloc (⟦ F ⟧TI (μ-type F)) loc s →
    ShapeAt m alloc (μ-type F) loc s

  shape-ν : ∀ {m F}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (wf : WellFormedFI F) →
    ShapeAt m alloc (⟦ F ⟧TI (ν-type F)) loc s →
    ShapeAt m alloc (ν-type F) loc s

  shape-int : ∀ {m}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    {n : ⟦ Intˢ ⟧} →
    BeforeFrontier alloc loc →
    readLoc s loc ≡ just (SV-Lit fits-intˢ n) →
    ShapeAt m alloc Int loc s

  shape-float : ∀ {m}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    {x : ⟦ Floatˢ ⟧} →
    BeforeFrontier alloc loc →
    readLoc s loc ≡ just (SV-Lit fits-floatˢ x) →
    ShapeAt m alloc Float loc s

  shape-str : ∀ {m}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS} →
    BeforeFrontier alloc loc →
    ShapeAt m alloc Str loc s

  shape-buffer : ∀ {m}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS} →
    BeforeFrontier alloc loc →
    ShapeAt m alloc Buffer loc s

------------------------------------------------------------------------
-- GATE G1 (D076): the erasure is a PROJECTION of `ValidAtWF` — every
-- constructor maps 1:1, dropping only the value, `BodyCorrect` and the
-- body-size bound. If this ever stops being a plain structural map, the
-- shape domain has drifted from the value layer and must be re-aligned.
------------------------------------------------------------------------
module Project (program-bound : ℕ) where
  open import Data.Nat using (ℕ)
  open import Once.CCC.Machine.ClosureWellFormed using (module ClosureWellFormedDef)
  open ClosureWellFormedDef {FS} program-bound
    using (ValidAtWF; valid-unit-wf; valid-pair-wf; valid-closure-wf;
           valid-inl-wf; valid-inr-wf; valid-μ-wf; valid-ν-wf;
           valid-int-wf; valid-float-wf; valid-str-wf; valid-buffer-wf;
           SumTag)

  tag-of : ∀ (m : AllocMode) (t : ℕ) (s : LocState FS) (loc : ValueLocation FS)
         → SumTag m t s loc → TagAt m t s loc
  tag-of Heap  t s loc st = st
  tag-of Stack t s loc st = st

  valid→shape : ∀ {m} {alloc : AllocState {FS}} {A : IRTy} {x}
                  {loc : ValueLocation FS} {s : LocState FS}
              → ValidAtWF m alloc {A} x loc s → ShapeAt m alloc A loc s
  valid→shape valid-unit-wf = shape-unit
  valid→shape (valid-pair-wf lm r1 r2 b1 b2 b3 va vb) =
    shape-pair lm r1 r2 b1 b2 b3 (valid→shape va) (valid→shape vb)
  valid→shape (valid-closure-wf b< lm r1 r2 b1 b2 venv bc) =
    shape-closure lm r1 r2 b1 b2 (valid→shape venv)
  valid→shape (valid-inl-wf {m = m} lm tg r b1 b2 vp) =
    shape-inl lm (tag-of m 0 _ _ tg) r b1 b2 (valid→shape vp)
  valid→shape (valid-inr-wf {m = m} lm tg r b1 b2 vp) =
    shape-inr lm (tag-of m 1 _ _ tg) r b1 b2 (valid→shape vp)
  valid→shape (valid-μ-wf wf x lv) = shape-μ wf (valid→shape lv)
  valid→shape (valid-ν-wf wf x lv) = shape-ν wf (valid→shape lv)
  valid→shape (valid-int-wf b r)   = shape-int b r
  valid→shape (valid-float-wf b r) = shape-float b r
  valid→shape (valid-str-wf b)     = shape-str b
  valid→shape (valid-buffer-wf b)  = shape-buffer b
