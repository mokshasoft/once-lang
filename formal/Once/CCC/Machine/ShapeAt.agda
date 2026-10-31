-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Machine.ShapeAt (FS : FrameSemantics) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using ()
open import Once.IRTy using (IRTy; FitsInRegI; fits-int; fits-float; Unit; _*_; _⇛_; _+_; WellFormedFI; ⟦_⟧TI; μ-type; ν-type; Int; Float)
import Once.Internal.Type as SpecTy
open import Once.Type using () renaming (fits-int to fits-intˢ; fits-float to fits-floatˢ)
open import Once.Denotation.ValueDomain using () renaming (⟦_⟧ᴰ to ⟦_⟧; ⟦_⟧ᴰᴵ to ⟦_⟧ᴵ)
open import Once.CCC.Machine.SMCore
  hiding (AllocMode; Stack; Heap)
open import Once.CCC.Machine.Locations using (ValueLocation)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.Spec.Name using (CanonicalName)
open import Once.CCC.Machine.Allocation
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

-- Stage F: the register-resident stored value, RESTATED here for the same
-- reason `TagAt` is — this module stays independent of `ClosureWellFormed`.
-- `valid→shape` splits on `fit` so both definitions reduce to the same
-- `SV-Lit`, so no bridging lemma is needed.
prim-sv-at : ∀ {B : IRTy} → FitsInRegI B → ⟦ B ⟧ᴵ → StoredValue FS
prim-sv-at fits-int   v = SV-Lit fits-intˢ   v
prim-sv-at fits-float v = SV-Lit fits-floatˢ v

-- …and likewise `InlineRep`. `valid→shape` maps one to the other constructor
-- for constructor, which is also where both `inline-sv`s reduce.
data InlineRepAt (A : IRTy) : Set where
  rep-prim-at : FitsInRegI A → InlineRepAt A
  rep-unit-at : A ≡ Unit → StoredValue FS → InlineRepAt A

inline-sv-at : ∀ {A : IRTy} → InlineRepAt A → ⟦ A ⟧ᴵ → StoredValue FS
inline-sv-at (rep-prim-at fit)  a = prim-sv-at fit a
inline-sv-at (rep-unit-at _ sv) _ = sv

-- D187: the shape mirror of `CellAt` — what a compound's CELL holds, which
-- since the pair split is a pointer OR the component itself. Forward-declared
-- so the two datatypes can be mutual, exactly as `CellAt`/`ValidAtWF` are.
data CellShapeAt (alloc : AllocState {FS}) :
     IRTy → ValueLocation FS → LocState FS → Set
data ShapeAt : AllocMode → AllocState {FS} →
     IRTy → ValueLocation FS → LocState FS → Set

data CellShapeAt alloc where
  cell-shape-ptr : ∀ {C : IRTy} {cl comp-loc : ValueLocation FS} {s : LocState FS}
                     {mC : AllocMode} →
                   readLoc s cl ≡ just (SV-Ptr comp-loc) →
                   BeforeFrontier alloc comp-loc →
                   ShapeAt mC alloc C comp-loc s →
                   CellShapeAt alloc C cl s
  cell-shape-inline : ∀ {C : IRTy} {cl : ValueLocation FS} {s : LocState FS}
                        {c : ⟦ C ⟧ᴵ} (rep : InlineRepAt C) →
                      readLoc s cl ≡ just (inline-sv-at rep c) →
                      CellShapeAt alloc C cl s

data ShapeAt where

  shape-unit : ∀ {m alloc loc s} →
    ShapeAt m alloc Unit loc s

  shape-pair : ∀ {m A B}
    {alloc : AllocState {FS}}
    {pair-loc : ValueLocation FS} {s : LocState FS} →
    LocMatchesMode m pair-loc →
    BeforeFrontier alloc (sucLoc pair-loc) →
    CellShapeAt alloc A pair-loc s →
    CellShapeAt alloc B (sucLoc pair-loc) s →
    ShapeAt m alloc (A * B) pair-loc s

  -- a closure's shape: env-pointer cell + code cell. plan 0.125 S1: no env
  -- SHAPE — the value layer no longer carries the environment's validity
  -- (its type is hidden, so it is not a subterm of `A ⇛ B`; `CallRuns` is
  -- what speaks for it), and this layer must not say more than that one.
  shape-closure : ∀ {m A B}
    {alloc : AllocState {FS}}
    {closure-loc env-loc : ValueLocation FS} {s : LocState FS}
    {body-label : LabelId} →
    LocMatchesMode m closure-loc →
    readLoc s closure-loc ≡ just (SV-Ptr env-loc) →
    readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label) →
    BeforeFrontier alloc env-loc →
    BeforeFrontier alloc (sucLoc closure-loc) →
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

  -- Stage F: the INLINE-payload sums. The payload cell holds the value, so
  -- there is no payload location, no payload shape, and no payload mode.
  --
  -- The value stays an IMPLICIT, exactly as `shape-int`/`shape-float` keep
  -- theirs: `ShapeAt` drops the value INDEX, but a constructor may still
  -- mention a value it does not index on. That keeps `valid→shape` a plain
  -- projection, which is D076's constraint on this layer — these say neither
  -- more nor less than `valid-inl-reg-wf` / `valid-inr-reg-wf` do.
  -- D181: a closure whose ENVIRONMENT is inline — its first cell holds the
  -- value, not a pointer, so there is no env SHAPE to recurse into.
  shape-closure-reg : ∀ {m EnvType A B}
    {alloc : AllocState {FS}}
    {closure-loc : ValueLocation FS} {s : LocState FS}
    {env : ⟦ EnvType ⟧ᴵ}
    {body-label : LabelId} →
    LocMatchesMode m closure-loc →
    (rep : InlineRepAt EnvType) →
    readLoc s closure-loc ≡ just (inline-sv-at rep env) →
    readLoc s (sucLoc closure-loc) ≡ just (SV-Code body-label) →
    BeforeFrontier alloc (sucLoc closure-loc) →
    ShapeAt m alloc (A ⇛ B) closure-loc s

  shape-inl-reg : ∀ {m A B}
    {alloc : AllocState {FS}}
    {sum-loc : ValueLocation FS} {s : LocState FS}
    {a : ⟦ A ⟧ᴵ} →
    LocMatchesMode m sum-loc →
    TagAt m 0 s sum-loc →
    (rep : InlineRepAt A) →
    readLoc s (sucLoc sum-loc) ≡ just (inline-sv-at rep a) →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ShapeAt m alloc (A + B) sum-loc s

  shape-inr-reg : ∀ {m A B}
    {alloc : AllocState {FS}}
    {sum-loc : ValueLocation FS} {s : LocState FS}
    {b : ⟦ B ⟧ᴵ} →
    LocMatchesMode m sum-loc →
    TagAt m 1 s sum-loc →
    (rep : InlineRepAt B) →
    readLoc s (sucLoc sum-loc) ≡ just (inline-sv-at rep b) →
    BeforeFrontier alloc (sucLoc sum-loc) →
    ShapeAt m alloc (A + B) sum-loc s

  shape-μ : ∀ {m F}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    (wf : WellFormedFI F) →
    ShapeAt m alloc (⟦ F ⟧TI (μ-type F)) loc s →
    ShapeAt m alloc (μ-type F) loc s

  -- D189: a ν is a SUSPENSION, not an available layer — seed cell plus
  -- coalgebra code cell, mirroring `shape-closure`. plan 0.125 S1: the seed
  -- is OPAQUE in the value layer (`NuV.nu-seed`: its type is not a subterm of
  -- `ν-type F`), so its cell holds SOME stored value and has no shape.
  shape-ν-susp : ∀ {m F}
    {alloc : AllocState {FS}}
    {ν-loc : ValueLocation FS} {s : LocState FS}
    {seed : StoredValue FS} {coalg-label : LabelId} →
    LocMatchesMode m ν-loc →
    readLoc s ν-loc ≡ just seed →
    readLoc s (sucLoc ν-loc) ≡ just (SV-Code coalg-label) →
    BeforeFrontier alloc (sucLoc ν-loc) →
    ShapeAt m alloc (ν-type F) ν-loc s

  shape-int : ∀ {m}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    {n : ⟦ SpecTy.Int ⟧} →
    BeforeFrontier alloc loc →
    readLoc s loc ≡ just (SV-Lit fits-intˢ n) →
    ShapeAt m alloc Int loc s

  shape-float : ∀ {m}
    {alloc : AllocState {FS}}
    {loc : ValueLocation FS} {s : LocState FS}
    {x : ⟦ SpecTy.Float ⟧} →
    BeforeFrontier alloc loc →
    readLoc s loc ≡ just (SV-Lit fits-floatˢ x) →
    ShapeAt m alloc Float loc s



------------------------------------------------------------------------
-- GATE G1 (D076): the erasure is a PROJECTION of `ValidAtWF` — every case
-- maps 1:1, dropping only the value, what a closure or a ν DOES (`CallRuns`,
-- `nu-force`) and `Live`'s heap-only half. If this ever stops being a plain
-- structural map, the shape domain has drifted from the value layer and must
-- be re-aligned. `ValidAtWF` is a function on the type, so the projection
-- splits on the type; μ layers are `ValidFO`, projected by their own pair.
------------------------------------------------------------------------
module Project (o : CanonicalName) (tbl : List IRFun) {prog : AbstractTrace} where
  open import Data.Nat using (ℕ)
  open import Data.Empty using (⊥-elim)
  open import Relation.Binary.PropositionalEquality using (subst; sym)
  open import Once.IRTy using (Void)
  open import Once.CCC.Machine.ValueRel
    using (module ClosureWellFormedBase; module ClosureWellFormedDef)
  open ClosureWellFormedBase {FS}
    using (Live; live→bf; CellAtP; cell-ptr; cell-inline; InlineRep; rep-prim; rep-unit;
           unit-wf; pair-wf; inl-wf; inr-wf; inl-reg-wf; inr-reg-wf; int-wf; float-wf;
           ValidFO; fo-unit; fo-pair; fo-sum; fo-int; fo-float; fo-μwf; SumTag; wrap)
  open ClosureWellFormedDef {FS} {prog}
    using (ValidAtWF; CellAt; closure-wf; closure-reg-wf; NuV; module NuV)
  open NuV using (nu-mode; nu-heap; nu-cell0; nu-cell1; nu-live1)

  tag-of : ∀ (m : AllocMode) (t : ℕ) (s : LocState FS) (loc : ValueLocation FS)
         → SumTag m t s loc → TagAt m t s loc
  tag-of Heap  t s loc st = st
  tag-of Stack t s loc st = st

  -- `inline-sv` (ClosureWellFormed's) and `inline-sv-at` (the local
  -- restatement) reduce to the same stored value only once the rep is split.
  rep-of : ∀ {A} → InlineRep A → InlineRepAt A
  rep-of (rep-prim fit)  = rep-prim-at fit
  rep-of (rep-unit u sv) = rep-unit-at u sv

  rep-read : ∀ {A} {r : Maybe (StoredValue FS)} {a} (rep : InlineRep A)
           → r ≡ just (ClosureWellFormedBase.inline-sv {FS} rep a)
           → r ≡ just (inline-sv-at (rep-of rep) a)
  rep-read (rep-prim fits-int)   r = r
  rep-read (rep-prim fits-float) r = r
  rep-read (rep-unit u sv)       r = r

  -- The first-order layer (μ), mutual with its cells.
  fo→shape : ∀ {m} {alloc : AllocState {FS}} {A : IRTy} {x}
               {loc : ValueLocation FS} {s : LocState FS}
           → ValidFO m alloc {A} x loc s → ShapeAt m alloc A loc s
  focell→shape : ∀ {alloc : AllocState {FS}} {C : IRTy} {c}
                   {cl : ValueLocation FS} {s : LocState FS}
               → CellAtP {C} (λ m′ a′ → ValidFO m′ a′ {C}) alloc c cl s → CellShapeAt alloc C cl s
  fo→shape (fo-unit unit-wf) = shape-unit
  fo→shape (fo-pair (pair-wf lm slb c₁ c₂)) =
    shape-pair lm (live→bf slb) (focell→shape c₁) (focell→shape c₂)
  fo→shape (fo-sum (inl-wf {m = m} lm tg pp pb slb pv)) =
    shape-inl lm (tag-of m 0 _ _ tg) pp (live→bf pb) (live→bf slb) (fo→shape pv)
  fo→shape (fo-sum (inr-wf {m = m} lm tg pp pb slb pv)) =
    shape-inr lm (tag-of m 1 _ _ tg) pp (live→bf pb) (live→bf slb) (fo→shape pv)
  fo→shape (fo-sum (inl-reg-wf {m = m} {a = a} lm tg rep pp slb)) =
    shape-inl-reg {a = a} lm (tag-of m 0 _ _ tg) (rep-of rep) (rep-read rep pp) (live→bf slb)
  fo→shape (fo-sum (inr-reg-wf {m = m} {b = b} lm tg rep pp slb)) =
    shape-inr-reg {b = b} lm (tag-of m 1 _ _ tg) (rep-of rep) (rep-read rep pp) (live→bf slb)
  fo→shape (fo-int (int-wf b r))     = shape-int (live→bf b) r
  fo→shape (fo-float (float-wf b r)) = shape-float (live→bf b) r
  fo→shape (fo-μwf wf x lv) = shape-μ wf (fo→shape lv)

  focell→shape (cell-ptr r bf v) = cell-shape-ptr r (live→bf bf) (fo→shape v)
  focell→shape {c = c} (cell-inline rep r) = cell-shape-inline {c = c} (rep-of rep) (rep-read rep r)

  cell→shape : ∀ {alloc : AllocState {FS}} {C : IRTy} {c}
                 {cl : ValueLocation FS} {s : LocState FS}
             → CellAt alloc C c cl s → CellShapeAt alloc C cl s
  valid→shape : ∀ {m} {alloc : AllocState {FS}} {A : IRTy} {x}
                  {loc : ValueLocation FS} {s : LocState FS}
              → ValidAtWF m alloc {A} x loc s → ShapeAt m alloc A loc s
  valid→shape {A = Unit} (wrap unit-wf) = shape-unit
  valid→shape {A = Void} (wrap ())
  valid→shape {A = A * B} (wrap (pair-wf lm slb c₁ c₂)) =
    shape-pair lm (live→bf slb) (cell→shape c₁) (cell→shape c₂)
  valid→shape {A = A + B} (wrap (inl-wf {m = m} lm tg pp pb slb pv)) =
    shape-inl lm (tag-of m 0 _ _ tg) pp (live→bf pb) (live→bf slb) (valid→shape pv)
  valid→shape {A = A + B} (wrap (inr-wf {m = m} lm tg pp pb slb pv)) =
    shape-inr lm (tag-of m 1 _ _ tg) pp (live→bf pb) (live→bf slb) (valid→shape pv)
  valid→shape {A = A + B} (wrap (inl-reg-wf {m = m} {a = a} lm tg rep pp slb)) =
    shape-inl-reg {a = a} lm (tag-of m 0 _ _ tg) (rep-of rep) (rep-read rep pp) (live→bf slb)
  valid→shape {A = A + B} (wrap (inr-reg-wf {m = m} {b = b} lm tg rep pp slb)) =
    shape-inr-reg {b = b} lm (tag-of m 1 _ _ tg) (rep-of rep) (rep-read rep pp) (live→bf slb)
  valid→shape {A = A ⇛ B} (wrap (closure-wf lm ep cp eb slb fd runs)) =
    shape-closure lm ep cp (live→bf eb) (live→bf slb)
  valid→shape {A = A ⇛ B} (wrap (closure-reg-wf {env = e} lm rep ep cp slb fd runs)) =
    shape-closure-reg {env = e} lm (rep-of rep) (rep-read rep ep) cp (live→bf slb)
  valid→shape {A = μ-type F} (wrap lv) = fo→shape lv
  -- D189: the suspension projects cell-wise, exactly as the closure does.
  valid→shape {A = ν-type F} (wrap nv) =
    shape-ν-susp (subst (λ m′ → LocMatchesMode m′ _) (sym (nu-mode nv)) (nu-heap nv))
                 (nu-cell0 nv) (nu-cell1 nv) (live→bf (nu-live1 nv))
  valid→shape {A = Int} (wrap (int-wf b r))     = shape-int (live→bf b) r
  valid→shape {A = Float} (wrap (float-wf b r)) = shape-float (live→bf b) r

  cell→shape (cell-ptr r bf v) = cell-shape-ptr r (live→bf bf) (valid→shape v)
  cell→shape {c = c} (cell-inline rep r) = cell-shape-inline {c = c} (rep-of rep) (rep-read rep r)
