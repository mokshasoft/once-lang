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
open import Data.Sum using (inj₁; inj₂)
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
open import Once.Denotation.DenotTrace using (evalᴰ; ⟦_⟧ᴰ; forget; emit-D; rec-trace-D)
open import Once.Denotation.TraceMonad using (projTrace; valueT; _>>=T_; returnT)
open import Once.CCC.Codegen.StraightRunSteps using (projTrace->>=T)

------------------------------------------------------------------------
-- The gate: the MAIN trace of `ir` carries no effectful `instr-sigop`.
-- Recurse only on the main-trace-splicing constructors (`∘`, `⟨,⟩`);
-- a `SigOp` must be `Pure`. `Cata` is excluded (owned by `cata-correct`).
------------------------------------------------------------------------
-- Denot-clean fragment: `evalᴰ` emits `[]` (both sides of `traces-agree`).
-- `apply` runs a RUNTIME closure (unknown events) and the recursion schemes
-- (`Cata`/`Ana`/`Para`/`Hylo`/`Fuse`) emit their fold trace via `rec-trace-D`,
-- so they are excluded; `case` recurses on its branches (`evalᴰ (case f g)`
-- dispatches to `evalᴰ f`/`evalᴰ g`). Everything else (leaves, `In`/`out-μ`/
-- `Out`/`const`/`free-heap` — `rec-trace-D ≡ []`, `curry` — `returnT`) is `⊤`.
NoEffectfulSigOp : ∀ {A B} → IR A B → Set
NoEffectfulSigOp (g ∘ f)        = NoEffectfulSigOp g × NoEffectfulSigOp f
NoEffectfulSigOp (⟨ f , g ⟩ m)  = NoEffectfulSigOp f × NoEffectfulSigOp g
NoEffectfulSigOp (case f g)     = NoEffectfulSigOp f × NoEffectfulSigOp g
NoEffectfulSigOp (SigOp si)     = effect si ≡ Pure
NoEffectfulSigOp apply          = ⊥
NoEffectfulSigOp (Cata _ _)     = ⊥
NoEffectfulSigOp (Ana _ _)      = ⊥
NoEffectfulSigOp (Para _ _)     = ⊥
NoEffectfulSigOp (Hylo _ _ _ _) = ⊥
NoEffectfulSigOp (Fuse _ _ _ _) = ⊥
{-# CATCHALL #-}
NoEffectfulSigOp _              = ⊤

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
  trace-noeff' apply       ()
  trace-noeff' (In _ _)    _ n l = (λ _ → refl) ∷ []
  trace-noeff' (out-μ _)   _ n l = (λ _ → refl) ∷ []
  trace-noeff' (Cata _ _)  ()
  trace-noeff' (Para _ _)  ()
  trace-noeff' (Out _)     _ n l = (λ _ → refl) ∷ []
  trace-noeff' (in-ν _ _)  _ n l = []
  trace-noeff' (Ana _ _)   ()
  trace-noeff' (Hylo _ _ _ _) ()
  trace-noeff' (Fuse _ _ _ _) ()
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

------------------------------------------------------------------------
-- Denot side: a `NoEffectfulSigOp` IR's denotation emits no events.
-- FS-free (pure denotational). Together with `noeff-flat-[]` this gives
-- `traces-agree ≡ []` for the whole denot-clean fragment.
------------------------------------------------------------------------

-- A pure SigOp's denotational emission is `[]` (`emit-D` dispatches on effect).
emit-D-pure : ∀ {A B} (si : SigOpInfo A B) x → effect si ≡ Pure → emit-D si x ≡ []
emit-D-pure si x eff rewrite eff = refl

noeff-denot-[] : ∀ {A B} (ir : IR A B) → NoEffectfulSigOp ir
               → ∀ (a : ⟦ A ⟧ᴰ) (k : ℕ) → projTrace (evalᴰ ir a) k ≡ []
-- `returnT` leaves.
noeff-denot-[] id          _ a k = refl
noeff-denot-[] fst         _ a k = refl
noeff-denot-[] snd         _ a k = refl
noeff-denot-[] (inl _)     _ a k = refl
noeff-denot-[] (inr _)     _ a k = refl
noeff-denot-[] terminal    _ a k = refl
noeff-denot-[] arr         _ a k = refl
noeff-denot-[] (curry _ _) _ a k = refl
-- Kleisli composition: split via `projTrace->>=T`, both parts `[]` by IH.
noeff-denot-[] (g ∘ f) (ng , nf) a k
  rewrite projTrace->>=T (evalᴰ f a) (evalᴰ g) k
        | noeff-denot-[] f nf a k
        | noeff-denot-[] g ng (valueT (evalᴰ f a) k) k = refl
noeff-denot-[] (⟨ f , g ⟩ m) (nf , ng) a k
  rewrite projTrace->>=T (evalᴰ f a) (λ b → evalᴰ g a >>=T λ c → returnT (b , c)) k
        | noeff-denot-[] f nf a k
        | projTrace->>=T (evalᴰ g a) (λ c → returnT (valueT (evalᴰ f a) k , c)) k
        | noeff-denot-[] g ng a k = refl
-- `case` dispatches to a branch by the input tag.
noeff-denot-[] (case f g) (nf , ng) (inj₁ a) k = noeff-denot-[] f nf a k
noeff-denot-[] (case f g) (nf , ng) (inj₂ b) k = noeff-denot-[] g ng b k
-- Pure `SigOp`.
noeff-denot-[] (SigOp si) eff a k = emit-D-pure si (forget a) eff
-- Catch-all denot (`rec-trace-D ≡ []` for these pure constructors).
noeff-denot-[] (In _ _)    _ a k = refl
noeff-denot-[] (out-μ _)   _ a k = refl
noeff-denot-[] (Out _)     _ a k = refl
noeff-denot-[] (in-ν _ _)  _ a k = refl
noeff-denot-[] (free-heap _) _ a k = refl
noeff-denot-[] (const fits-int   _) _ a k = refl
noeff-denot-[] (const fits-float _) _ a k = refl
-- Excluded fragment (gate is `⊥`).
noeff-denot-[] apply         ()
noeff-denot-[] (Cata _ _)    ()
noeff-denot-[] (Ana _ _)     ()
noeff-denot-[] (Para _ _)    ()
noeff-denot-[] (Hylo _ _ _ _) ()
noeff-denot-[] (Fuse _ _ _ _) ()
