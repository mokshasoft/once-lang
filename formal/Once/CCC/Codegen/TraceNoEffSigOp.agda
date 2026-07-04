-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.TraceNoEffSigOp  (Plan 0.58 Phase 1)
--
-- `NoEffectfulSigOp ir` ⇒ the MAIN trace `ir-to-trace ir` emits no
-- SigOp events (`flat-events ≡ []`). This discharges `traces-agree` for
-- every IR whose main trace contains no `Emits`/`Halts` `instr-sigop`
-- (a PURE `instr-sigop` — arith block — already emits `[]`, so the gate
-- only forbids effectful ones). `EmitsNoSigOp` (Plan 0.36) was retired;
-- this is its replacement, and WIDER (pure sigops are allowed).
--
-- Mirrors `StraightTrace.straight-trace'`: recurse only where sub-traces
-- splice into the MAIN trace (`∘`, `⟨,⟩`); `case`/`curry` bodies live off
-- the main trace so their sigops don't reach `flat-events (ir-to-trace)`.
------------------------------------------------------------------------

module Once.CCC.Codegen.TraceNoEffSigOp where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.IR using (IR; AllocMode; Stack; Heap;
  id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply; arr;
  In; out-μ; Cata; Para; Out; in-ν; Ana; Hylo; Fuse;
  free-heap; SigOp; const)
open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure)
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-sigop)
open import Once.CCC.Codegen.IRToTrace using (ir-to-trace'; ir-to-trace; ir-to-trace-at-frontier)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.CCC.Machine.Flat using (module FlatMachine)

------------------------------------------------------------------------
-- The gate: the MAIN trace of `ir` carries no effectful `instr-sigop`.
-- Recurse only on the main-trace-splicing constructors (`∘`, `⟨,⟩`);
-- a `SigOp` must be `Pure`. `Cata` is excluded (owned by `cata-correct`).
------------------------------------------------------------------------
NoEffectfulSigOp : ∀ {A B} → IR A B → Set
NoEffectfulSigOp (g ∘ f)       = NoEffectfulSigOp g × NoEffectfulSigOp f
NoEffectfulSigOp (⟨ f , g ⟩ m) = NoEffectfulSigOp f × NoEffectfulSigOp g
NoEffectfulSigOp (SigOp si)    = effect si ≡ Pure
NoEffectfulSigOp (Cata _ _)    = ⊥
{-# CATCHALL #-}
NoEffectfulSigOp _             = ⊤

module _ {FS : FrameSemantics} where
  open FlatEventTrace {FS} using (event-of; flat-events; flat-events-[])
  open FlatMachine {FS} using (fetch; fetch-All; FlatState)

  -- A single instruction emits nothing from any state.
  NonEmitting : AbstractInstr → Set
  NonEmitting i = ∀ fs → event-of i fs ≡ []

  -- Third projection of the `ir-to-trace'` 4-tuple (mirror `StraightTrace`).
  trace-of : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → AbstractTrace
  trace-of (_ , _ , t , _) = t

  -- A pure `instr-sigop` emits `[]`: `event-of (instr-sigop si) = ev-of-loc …`
  -- reduces through `effect si ≡ Pure` to `[]`.
  sigop-pure-nonemitting : ∀ {A B} (si : SigOpInfo A B) → effect si ≡ Pure → NonEmitting (instr-sigop si)
  sigop-pure-nonemitting si eff fs rewrite eff = refl

  -- The proof, mirroring `straight-trace'` clause-for-clause (same instr
  -- counts). Every non-sigop instr is `NonEmitting` by `refl` (`ev-of-loc`
  -- catch-all); `∘`/`⟨,⟩` splice via `++⁺`; `SigOp` uses the gate's `Pure`.
  trace-noeff' : ∀ {A B} (ir : IR A B) → NoEffectfulSigOp ir → (n l : ℕ)
    → All NonEmitting (trace-of (ir-to-trace' n l ir))
  trace-noeff' id          _        n l = (λ _ → refl) ∷ []
  trace-noeff' (g ∘ f)     (ng , nf) n l =
    ++⁺ (trace-noeff' f nf _ _) ((λ _ → refl) ∷ trace-noeff' g ng _ _)
  trace-noeff' (⟨ f , g ⟩ Stack) (nf , ng) n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷
    ++⁺ (trace-noeff' f nf _ _)
        ((λ _ → refl) ∷ (λ _ → refl) ∷
         ++⁺ (trace-noeff' g ng _ _)
             ((λ _ → refl) ∷ (λ _ → refl) ∷ []))
  trace-noeff' (⟨ f , g ⟩ Heap)  (nf , ng) n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷
    ++⁺ (trace-noeff' f nf _ _)
        ((λ _ → refl) ∷ (λ _ → refl) ∷
         ++⁺ (trace-noeff' g ng _ _)
             ((λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
              (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
              (λ _ → refl) ∷ []))
  trace-noeff' fst         _ n l = (λ _ → refl) ∷ []
  trace-noeff' snd         _ n l = (λ _ → refl) ∷ []
  trace-noeff' (inl Stack) _ n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
  trace-noeff' (inr Stack) _ n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
  trace-noeff' (inl Heap)  _ n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
  trace-noeff' (inr Heap)  _ n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
  trace-noeff' (case f g)  _ n l = (λ _ → refl) ∷ []
  trace-noeff' terminal    _ n l = []
  trace-noeff' initial     _ n l = (λ _ → refl) ∷ []
  trace-noeff' arr         _ n l = (λ _ → refl) ∷ []
  trace-noeff' (curry b Stack) _ n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
  trace-noeff' (curry b Heap)  _ n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
  trace-noeff' apply       _ n l =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    (λ _ → refl) ∷ (λ _ → refl) ∷ []
  trace-noeff' (In _ _)    _ n l = (λ _ → refl) ∷ []
  trace-noeff' (out-μ _)   _ n l = (λ _ → refl) ∷ []
  trace-noeff' (Cata _ _)  ()
  trace-noeff' (Para _ _)  _ n l = []
  trace-noeff' (Out _)     _ n l = (λ _ → refl) ∷ []
  trace-noeff' (in-ν _ _)  _ n l = []
  trace-noeff' (Ana _ _)   _ n l = []
  trace-noeff' (Hylo _ _ _ _) _ n l = []
  trace-noeff' (Fuse _ _ _ _) _ n l = []
  trace-noeff' (free-heap _)  _ n l = (λ _ → refl) ∷ []
  trace-noeff' (SigOp si)  eff n l = sigop-pure-nonemitting si eff ∷ []
  trace-noeff' (const fits-int   _) _ n l = (λ _ → refl) ∷ []
  trace-noeff' (const fits-float _) _ n l = (λ _ → refl) ∷ []

  -- Corollary over the public entry points (mirror `StraightTrace`).
  trace-noeff-at-frontier : ∀ {A B} (ir : IR A B) (n : ℕ)
    → NoEffectfulSigOp ir → All NonEmitting (ir-to-trace-at-frontier n ir)
  trace-noeff-at-frontier ir n ne
    with ir-to-trace' n 0 ir | trace-noeff' ir ne n 0
  ... | _ , _ , _ , _ | ne' = ne'

  trace-noeff : ∀ {A B} (ir : IR A B)
    → NoEffectfulSigOp ir → All NonEmitting (ir-to-trace ir)
  trace-noeff ir = trace-noeff-at-frontier ir 0

  -- The headline lemma: a `NoEffectfulSigOp` IR's main trace emits nothing.
  -- Discharges `traces-agree`'s machine side (`= []`) for the pure fragment.
  noeff-flat-[] : ∀ {A B} (ir : IR A B) → NoEffectfulSigOp ir
    → ∀ (fuel : ℕ) (fs : FlatState) → flat-events fuel (ir-to-trace ir) fs ≡ []
  noeff-flat-[] ir ne =
    flat-events-[] (ir-to-trace ir) (λ pc i eq → fetch-All (trace-noeff ir ne) eq)
