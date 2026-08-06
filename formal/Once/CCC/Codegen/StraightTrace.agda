-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.StraightTrace
--
-- Plan 0.32 choice (a), migration step 2: the load-bearing lemma that
-- lets the `exec-trace-is-flat` bridge lift the straight-line WF proofs
-- onto `exec-flat`.
--
-- The flat machine's `exec-flat` is THE abstract semantics; `exec-trace`
-- survives only as `Flat.exec-trace-is-flat`, a theorem about it on
-- JUMP-FREE traces (`Straight prog = All StraightStep prog`). To apply
-- that bridge to a compiled IR we must know `ir-to-trace ir` is straight.
--
-- KEY FACT (live codegen): the ONLY `ir-to-trace'` clause that emits a
-- non-straight `instr-ctrl` into the MAIN trace is `Cata` (its flat loop
-- labels/jumps). Every other IR — including `case` (whose branch bodies
-- are ARGUMENTS to `instr-case-on-tag`, not main-trace elements) and
-- `curry` (whose body lands in the separate bodies list) — produces a
-- straight main trace. So `StraightIR` excludes exactly `Cata`, and the
-- splicing constructors `_∘_` / `⟨_,_⟩` recurse into their sub-IRs.
--
-- `Cata` itself "goes fully flat" (FlatSimulation) — it never rides this
-- bridge.
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.StraightTrace (o : CanonicalName) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.PropositionalEquality using (refl)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.IRTy using (fits-int; fits-float)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier)
open import Once.CCC.Machine.Flat using (module FlatMachine)

------------------------------------------------------------------------
-- StraightIR: the main trace of `ir` contains no `instr-ctrl`.
-- Recurse only where sub-traces are spliced into the MAIN trace
-- (`_∘_`, `⟨_,_⟩`).
--
-- TWO obstructions, not one. `Cata` was always here (its flat loop). `case`
-- JOINED IT with the flip (plan 0.63 2b): its branch bodies used to be
-- ARGUMENTS to `instr-case-on-tag` — off the main trace — and it now compiles
-- to FLAT control, emitting `c-branch-tag-zero`/`c-jmp`/`c-label` into the
-- main trace directly. `curry` joined for the same reason: the flip put the
-- closure BODY inline, bracketed by `c-jmp`/`c-thunk` … `c-ret`/`c-label`,
-- instead of in the separate bodies list.
--
-- Both became FALSE while sitting in the catch-all below silently claiming
-- `⊤`; the `case`/`curry` clauses of `straight-trace'` could no longer be
-- proven, which is how it surfaced. The catch-all is why it stayed quiet.
------------------------------------------------------------------------
StraightIR : ∀ {A B} → IR A B → Set
StraightIR (g ∘ f)       = StraightIR g × StraightIR f
StraightIR (⟨ f , g ⟩ m) = StraightIR f × StraightIR g
StraightIR (Cata _ _)    = ⊥
StraightIR (case _ _)    = ⊥
StraightIR (curry _ _)   = ⊥
{-# CATCHALL #-}
StraightIR _             = ⊤

------------------------------------------------------------------------
-- The proof, FS-polymorphic (the conclusion `Straight {FS}` is indexed
-- by FrameSemantics; the trace itself is FS-free).
------------------------------------------------------------------------
module _ {FS : FrameSemantics} where
  open FlatMachine {FS}

  -- third projection of the `ir-to-trace'` 4-tuple (record projections,
  -- so it reduces under eta — unlike the private `proj-trace`).
  trace-of : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → AbstractTrace
  trace-of (_ , _ , t , _) = t

  -- NB: every concrete non-`instr-ctrl` instruction is a `StraightStep`
  -- via `λ _ _ → refl` — `flat-exec-instr` falls through its catch-all
  -- to `flat-step-straight`.
  --
  -- General lemma over arbitrary frontier `n` / label counter `l`.
  straight-trace' : ∀ {A B} (ir : IR A B) → StraightIR ir → (n l : ℕ)
    → Straight (trace-of (ir-to-trace' n l ir))
  straight-trace' id          _        n l = (λ _ _ → refl) ∷ []
  straight-trace' (g ∘ f)     (sg , sf) n l =
    ++⁺ (straight-trace' f sf _ _) ((λ _ _ → refl) ∷ straight-trace' g sg _ _)
  straight-trace' (⟨ f , g ⟩ Stack) (sf , sg) n l =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    ++⁺ (straight-trace' f sf _ _)
        ((λ _ _ → refl) ∷ (λ _ _ → refl) ∷
         ++⁺ (straight-trace' g sg _ _)
             ((λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []))
  straight-trace' (⟨ f , g ⟩ Heap)  (sf , sg) n l =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    ++⁺ (straight-trace' f sf _ _)
        ((λ _ _ → refl) ∷ (λ _ _ → refl) ∷
         ++⁺ (straight-trace' g sg _ _)
             ((λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
              (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
              (λ _ _ → refl) ∷ []))
  straight-trace' fst         _ n l = (λ _ _ → refl) ∷ []
  straight-trace' snd         _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (inl Stack) _ n l =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
  straight-trace' (inr Stack) _ n l =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
  straight-trace' (inl Heap)  _ n l =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
  straight-trace' (inr Heap)  _ n l =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
  straight-trace' (case f g)  () n l
  straight-trace' terminal    _ n l = []
  straight-trace' initial     _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (curry b Stack) () n l
  straight-trace' (curry b Heap)  () n l
  straight-trace' apply       _ n l =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
  straight-trace' (In _ _)    _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (out-μ _)   _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (Cata _ _)  ()
  straight-trace' (Para _ _)  _ n l = []
  straight-trace' (Out _)     _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (in-ν _ _)  _ n l = []
  straight-trace' (Ana _ _)   _ n l = []
  straight-trace' (Hylo _ _ _ _) _ n l = []
  straight-trace' (Fuse _ _ _ _) _ n l = []
  straight-trace' (free-heap _)  _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (SigOp _)   _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (const fits-int _)   _ n l = (λ _ _ → refl) ∷ []
  straight-trace' (const fits-float _) _ n l = (λ _ _ → refl) ∷ []

  ----------------------------------------------------------------------
  -- Corollaries over the public entry points.
  ----------------------------------------------------------------------
  straight-ir-to-trace-at-frontier : ∀ {A B} (ir : IR A B) (n : ℕ)
    → StraightIR ir → Straight (ir-to-trace-at-frontier n ir)
  straight-ir-to-trace-at-frontier ir n si
    with ir-to-trace' n 0 ir | straight-trace' ir si n 0
  ... | _ , _ , _ , _ | st = st

  straight-ir-to-trace : ∀ {A B} (ir : IR A B)
    → StraightIR ir → Straight (ir-to-trace ir)
  straight-ir-to-trace ir = straight-ir-to-trace-at-frontier ir 0
