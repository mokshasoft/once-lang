-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.LabelClash   (D100)
--
-- The sibling of `Once.Adequacy.NameClash`, one level down. That module states
-- and PROVES `DistinctSymbols` — the `.globl` function symbols of a module are
-- pairwise distinct. This one states `DistinctLabels` — the `.L…` LOCAL labels
-- the codegen invents (the `once`-provenance jump targets and the
-- `thunk`-provenance closure-body entries) are pairwise distinct too.
--
-- WHY IT EXISTS. `as` rejects a file that defines a symbol twice, local labels
-- included. Nothing stated that, so nothing proved it, and on 2026-08-06 the
-- emitter shipped
--
--     layer5-cata-nat.s:332: Error: symbol `.L_thunk_once_4main_10' is
--                                   already defined
--
-- through a green tree (61 exit tests, three arches). No theorem below the
-- toolchain boundary could have been false: `find-label` is a FIRST-MATCH scan
-- on every arch and the flat machine resolves labels the same way, so with a
-- label defined twice both machines still pick the same one and the simulation
-- is TRUE. The only layer that rejects the text is the assembler — which is
-- `<arch>-loader-faithful`, stated with no precondition at all. The axiom was
-- not merely trusted, it was FALSE for every program the emitter duplicated.
--
-- WHY NOT ON `assemble-correct`. That field already carries `DistinctSymbols`
-- — and it is VACUOUS: once `asm-sem` was DEFINED as `exec-bytes ∘ assemble`
-- (`FlatFromObs.flat-from-obs`), the field collapsed to `λ _ _ _ _ _ → refl`
-- and consumed its premise for nothing. The trust point had moved to
-- `loader-faithful`; the precondition did not move with it. THAT is the general
-- trap, and it is why this premise is attached to `asm-trace-correct`, which is
-- where the toolchain is actually trusted today.
--
-- STATUS: `program-labels-distinct` is a NAMED RESIDUAL, class
-- **deferred proof / codegen**, and it is FALSE for the emitter as it stands —
-- `cata-dispatch` uses the IH for its algebra trace TWICE at the same label
-- range, which is exactly D099's defect. That is the point: the invariant is
-- what forces the cata fix rather than letting the assembler silently drop one
-- copy of the label. Route: the disjoint-range argument at every splice, on
-- `Once.CCC.Codegen.LabelRange`'s existing bricks (counter monotonicity DONE,
-- containment/`LabelScope` DONE, uniqueness next).
------------------------------------------------------------------------

module Once.Adequacy.LabelClash where

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Bool using (false)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)

open import Once.Parser.Module.Core using (Module)
open import Once.Target.Arch using (Arch)
import Once.Compile as C

------------------------------------------------------------------------
-- The predicate, over the REAL codegen output.
--
-- `C.moduleLabels` is defined in `Once.Compile` on the SAME `CompiledFun` list
-- `compileFromModule` renders, threading the SAME label counter
-- `compileAllWithTarget` threads — so a wrong set is a type error here rather
-- than a regression in the exit tests. `C.Heap`/`false` are the apex's own
-- pipeline settings (`compileFromModule C.Heap C.Build false arch m`), fixed
-- the same way `DistinctSymbols` fixes them.
------------------------------------------------------------------------

DistinctLabels : Arch → Module → Set
DistinctLabels arch m = AllPairs _≢_ (C.moduleLabels arch C.Heap false m)

postulate
  -- RESIDUAL (deferred proof / codegen). The obligation the apex owes so that
  -- `<arch>-loader-faithful` may assume the text it is handed is assemblable.
  -- Currently FALSE — see the header. Discharging it is the cata-label fork
  -- (D089's splice path vs. re-generating the algebra at successive counters);
  -- the wiring below is identical either way, only the proof differs.
  program-labels-distinct : ∀ (arch : Arch) (m : Module) → DistinctLabels arch m
