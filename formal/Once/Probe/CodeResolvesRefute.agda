-- PROBE (not part of the build): is `CodeResolves` — plan 0.91 S3's proposed
-- replacement for `block-runs` — actually TRUE?
--
-- It is not. It is FALSE, for a reason that also explains `block-runs` (D213).
--
-- `ClosureValidWF` ties `f` to the body's DENOTATION, not to its syntax:
--     f-is-closure : f ≡ (λ arg → evalᴰ body (env , arg))
-- so `body` is UNDERDETERMINED — `terminal` and `terminal ∘ id` have the same
-- denotation (`returnT a >>=T k` reduces to `k a`) and therefore the same `f`.
--
-- But `CodeResolves`' conclusion mentions the body's TEXT:
--     emitted 0 lbase (ClosureValidWF.body cvw)
-- and `find-thunk` is a FUNCTION, so both decompositions resolve to the SAME j.
-- Two different texts are then forced to span at the same place:
--     ir-to-trace' n l terminal = n , l , []                 , []
--     ir-to-trace' n l id       = n , l , (mov-to-output ∷ []) , []
-- `block-layout` puts `c-ret` at index 1 of the first and `mov-to-output` at
-- index 1 of the second. Both cannot hold.
open import Once.CanonicalName using (CanonicalName)
open import Once.Adequacy.CPU.Interface using (Arch; ArchSemantics)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Target.Arch using (arch-numerics)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Once.CCC.FrameSemantics

module Once.Probe.CodeResolvesRefute (o : CanonicalName)
  (arch : Arch) (FS : FrameSemantics)
  (fmt-agree : Once.CCC.FrameSemantics.fs-numerics FS ≡ arch-numerics arch)
  (entry-frame : FrameSemantics.Frame FS)
  (asem : ArchSemantics) where

open import Data.Empty using (⊥)
open import Data.Product using (∃-syntax; proj₁; proj₂; _,_)
open import Data.Maybe using (just)
open import Once.IR using (IR; Unit; id; terminal; _∘_)
open import Once.CCC.Codegen.IRObsCorrectFlat o using (module IRObsCorrectFlatness)
open import Once.CCC.Machine.ClosureWellFormed o using (module ClosureWellFormedDef)
open import Once.Probe.BlockRunsRefute o using (module Refute)

open IRObsCorrectFlatness {FS} using (CodeResolves; BlockAt; blocks; emitted)
open ClosureWellFormedDef {FS} using (ClosureValidWF; decomposeClosureWF)
open Refute {FS} entry-frame using (bad-alloc; bad-st; cloc; bad-valid)

open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Once.CCC.Machine.SMCore using (AbstractTrace; mov-to-output; mov-to-input; instr-ctrl; c-ret)
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.IRTy as IRTy
-- the denotation brackets, from the same place BlockRunsRefute gets them
open import Once.CCC.Codegen.IRObsCorrect.Interface o using (⟦_⟧; module Core)
-- `evalᴰ` lives in the FS-parameterised `Core`, not at Interface's top level —
-- the same `open Core {FS}` BlockRunsRefute uses.
open Core {FS} using (evalᴰ)
open import Data.Unit using (tt)
open FlatMachine {FS} using (fetch)

-- The SAME closure value, decomposed two ways. `f` is written out rather than
-- left to unification: `⟦ Unit ⇛ Unit ⟧` is a function type and solving it from
-- the witness is where the elaborator spends its time.
f : ⟦ Unit IRTy.⇛ Unit ⟧
f = λ arg → evalᴰ (terminal {Unit IRTy.* Unit}) (tt , arg)

cvw₁ : ClosureValidWF bad-alloc {Unit} {Unit} f cloc bad-st
cvw₁ = decomposeClosureWF bad-valid

-- Only `body` differs. Every state-facing field is literally the same field of
-- `cvw₁`, and `f-is-closure` still holds by `refl` because
-- `evalᴰ (terminal ∘ id) ≡ evalᴰ terminal` definitionally
-- (`returnT a >>=T k` reduces to `k a`: `returnT x _ = ([] , x)` and `n ∸ 0 = n`).
cvw₂ : ClosureValidWF bad-alloc {Unit} {Unit} f cloc bad-st
cvw₂ = record cvw₁ { body = terminal ∘ id ; f-is-closure = refl }

-- `CodeResolves` must therefore place BOTH bodies' texts at the same position:
--   emitted 0 lb terminal        = []
--   emitted 0 lb (terminal ∘ id) = mov-to-output ∷ mov-to-input ∷ []
-- so `block-layout` puts `c-ret` at index 1 of the first and `mov-to-output` at
-- index 1 of the second, and `find-thunk` — a function — gives them the same j.
boom : ∀ (prog : AbstractTrace) → CodeResolves prog bad-alloc bad-st → ⊥
boom prog cr with cr f cloc cvw₁ | cr f cloc cvw₂
... | lb₁ , (j₁ , fe₁ , sp₁) , _ | lb₂ , (j₂ , fe₂ , sp₂) , _
      with just-injective (trans (sym fe₂) fe₁)
...   | refl = case trans (sym (sp₁ 1 _ refl)) (sp₂ 1 _ refl) of λ ()
