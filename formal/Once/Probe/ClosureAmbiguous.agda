-- PROBE (not part of the build): does a STATE determine a closure's DENOTATION?
--
-- It does not. `valid-closure-wf` binds `{body}` and `{body-label}` as FREE
-- IMPLICITS whose only tie to the state is the code cell's contents, and
-- `valid-unit-wf : ∀ {m alloc loc s} → ValidAtWF m alloc {Unit} tt loc s` is
-- UNCONDITIONAL. So one heap cell carries two different closure denotations.
--
-- This is the gate for plan 0.91's second S3 design. If both witnesses below
-- typecheck, then NO predicate on the state — `CodeWF` included — can supply
-- `CalleeRuns`' second conjunct (that the block at `j` computes
-- `evalᴰ body envArg`), because the state does not know which `body` it means.
open import Once.CanonicalName using (CanonicalName)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Target.Arch using (arch-numerics)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Once.CCC.FrameSemantics

module Once.Probe.ClosureAmbiguous (o : CanonicalName)
  (arch : Arch) (FS : FrameSemantics)
  (fmt-agree : Once.CCC.FrameSemantics.fs-numerics FS ≡ arch-numerics arch)
  (entry-frame : FrameSemantics.Frame FS)
  (asem : ArchSemantics) where

open import Data.Integer using (ℤ; +_)
open import Data.Nat using (s≤s; z≤n)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Once.IR using (IR; Unit; Int; terminal; const; _∘_; _*_; _⇛_; Heap)
open import Once.IRTy using (fits-int)
open import Once.CCC.Codegen.IRObsCorrect.Interface o using (⟦_⟧; module Core)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
open import Once.CCC.Machine.Allocation using (module FrontierInvariant)
open import Once.Probe.BlockRunsRefute o using (module Refute)

open Core {FS} using (evalᴰ)
open ClosureWellFormedDef {FS} using (ValidAtWF; valid-closure-wf; valid-unit-wf)
open FrontierInvariant {FS} using (heap-before)
open Refute {FS} entry-frame using (bad-alloc; bad-st; cloc; eloc; lbl)

-- Two bodies of the SAME type with DIFFERENT denotations. `intLit n` in
-- Once/Surface/Elaborate.agda:68 is exactly this shape.
body₀ body₁ : IR (Unit * Unit) Int
body₀ = const fits-int (+ 0) ∘ terminal
body₁ = const fits-int (+ 1) ∘ terminal

-- …and the two closure values they denote. These are DIFFERENT functions.
f₀ f₁ : ⟦ Unit ⇛ Int ⟧
f₀ = λ arg → evalᴰ body₀ (tt , arg)
f₁ = λ arg → evalᴰ body₁ (tt , arg)

-- ONE cell. TWO denotations. Same `bad-st`, same `cloc`, same `lbl`.
valid₀ : ValidAtWF Heap bad-alloc {Unit ⇛ Int} f₀ cloc bad-st
valid₀ = valid-closure-wf {body = body₀} {env = tt}
           {alloc = bad-alloc} {closure-loc = cloc} {env-loc = eloc}
           {s = bad-st} {mEnv = Heap} {body-label = lbl}
           tt refl refl
           (heap-before (s≤s z≤n)) (heap-before (s≤s z≤n))
           valid-unit-wf

valid₁ : ValidAtWF Heap bad-alloc {Unit ⇛ Int} f₁ cloc bad-st
valid₁ = valid-closure-wf {body = body₁} {env = tt}
           {alloc = bad-alloc} {closure-loc = cloc} {env-loc = eloc}
           {s = bad-st} {mEnv = Heap} {body-label = lbl}
           tt refl refl
           (heap-before (s≤s z≤n)) (heap-before (s≤s z≤n))
           valid-unit-wf
