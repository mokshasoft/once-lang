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
-- STATUS (CORRECTED 2026-09-08, plan 0.89 Phase D2). This block used to say
-- the residual "is FALSE for the emitter as it stands — `cata-dispatch` uses
-- the IH for its algebra trace TWICE at the same label range". THAT IS NO
-- LONGER SO, and the note was stale for a month: D099/C1 (2026-08-10) made the
-- algebra a CALLED BODY generated once, and all four strategies now splice
-- `at` exactly once, inside `cata-body` — checked, `cata-trace-{nat,linear,
-- branching,const}`. The invariant did its job: it forced the cata fix, which
-- landed.
--
-- So `program-labels-distinct` is a NAMED RESIDUAL, class **deferred proof /
-- codegen**, and it is now BELIEVED TRUE. Every label is drawn from the
-- monotone counter and consumed once — `curry` takes `l`, `l+1` and hands the
-- body `l+2`; `case` takes `l`, `l+1` and compiles its branches above them;
-- `cata` takes from `l1` on — and D161 made the cross-function threading one
-- walk (`irToAsm` now compiles the LINKED program, so its counter advance
-- already covers the bodies' labels; the old `l₁ ⊔ l₂` reconciliation of two
-- walks is gone).
--
-- ROUTE, unchanged in shape: the disjoint-range argument at every splice, on
-- `Once.CCC.Codegen.LabelRange`'s bricks — counter monotonicity DONE
-- (`label-mono`), containment DONE (`LabelScope.labels-in`), and since D160 the
-- entry-vs-blocks separation DONE too (`scope-ok`, which carries exactly the
-- window and `NoCross` facts a uniqueness proof needs). Uniqueness is next.
--
-- PHASE D2's QUESTION, answered: the plan asked whether the invariant needs
-- restating "once on the unit" before investing. It does not. The module-level
-- form is already the one wired into `asm-trace-correct`, it is read off the
-- same `ir'` the backend compiles so it cannot drift, and a unit-level restatement
-- would add a second expression of the same fact — the exact disease this
-- branch exists to remove. The investment belongs in the DISCHARGE.
------------------------------------------------------------------------

module Once.Adequacy.LabelClash where

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Bool using (false)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)

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

------------------------------------------------------------------------
-- D169 — AND THE OTHER HALF, for the same namespace.
--
-- `DistinctLabels` is `as`'s rejection ("symbol already defined").
-- `LabelsResolvable` is `ld`'s ("undefined reference"), for LOCAL labels —
-- the exact analogue of D167's `SymbolsResolvable` one namespace up, and the
-- module-level form of `EmittedWF.labels-resolvable`, which has been stated
-- since D100 with NO CONSUMER.
--
-- It is not idle. A `c-jmp` names a `c-label`, and `instr-load-code-addr`
-- names a `c-thunk` — and until D159 the closure body was INLINED, so the
-- `c-thunk` it names lived in text the modelled program never contained. That
-- is the riscv64 defect `AbstractToRiscV` records verbatim: "the `lla`
-- referenced an undefined symbol — a link failure caught by the exit tests and
-- invisible to the proofs". With bodies as named blocks in the linked image,
-- the property is finally STATABLE over what is emitted.
------------------------------------------------------------------------

LabelsResolvable : Arch → Module → Set
LabelsResolvable arch m =
  All (_∈ C.moduleLabels arch C.Heap false m) (C.moduleLabelRefs arch C.Heap false m)

postulate
  -- RESIDUAL (deferred proof / codegen), the sibling of the one below: every
  -- jump, branch and code-address the emitted text names is defined in it.
  -- D160 is the input its proof wants — `linked-agree` / `scope-ok` already
  -- carry the label windows and the entry-vs-blocks disjointness over exactly
  -- this program.
  program-labels-resolvable : ∀ (arch : Arch) (m : Module) → LabelsResolvable arch m

postulate
  -- RESIDUAL (deferred proof / codegen). The obligation the apex owes so that
  -- `<arch>-loader-faithful` may assume the text it is handed is assemblable.
  -- Currently FALSE — see the header. Discharging it is the cata-label fork
  -- (D089's splice path vs. re-generating the algebra at successive counters);
  -- the wiring below is identical either way, only the proof differs.
  program-labels-distinct : ∀ (arch : Arch) (m : Module) → DistinctLabels arch m
