-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Behavior — WHAT THIS COMPILER CLAIMS
--
-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  CRITICAL READING NOTE — DO NOT GET THIS WRONG.                  ║
-- ║                                                                  ║
-- ║  Once programs DO NOT RETURN A VALUE.                            ║
-- ║                                                                  ║
-- ║  `main : Eff Unit Unit` is fixed by `validateMain`. The trailing ║
-- ║  `Unit` is meaningless — there is nothing for a program to       ║
-- ║  return because there is no caller above `main`. What a program  ║
-- ║  *does* is INVOKE SIGNATURE OPERATIONS (SigOps): the exit call,  ║
-- ║  a write syscall, `arith.add.int`, etc. The observable behaviour ║
-- ║  is THE SEQUENCE OF SIGOP CALLS the program performs and their  ║
-- ║  arguments — i.e. an EFFECT TRACE.                               ║
-- ║                                                                  ║
-- ║  The exit code (Layer 0's only observable) is not a "return      ║
-- ║  value." It is *the argument* to the program's final             ║
-- ║  the exit-syscall SigOp call. There is no other channel by which ║
-- ║  exit codes leave the program; "the program returns 42" is       ║
-- ║  shorthand for "the program calls an exit syscall."              ║
-- ║                                                                  ║
-- ║  Anyone tempted to project a "return value" from `evalSurface`   ║
-- ║  is reading the semantics wrong. `evalSurface ε e : ⟦ T ⟧Type`   ║
-- ║  collapses effectful arrows to plain function arrows             ║
-- ║  (⟦ A ⇒[_] B ⟧ = ⟦ A ⟧ → ⟦ B ⟧); for `Eff Unit Unit` this is     ║
-- ║  `⊤ → ⊤`, which carries NO INFORMATION. The actual effect        ║
-- ║  semantics flows through `generic-semI`, which is the SigOp      ║
-- ║  dispatcher.                                                     ║
-- ║                                                                  ║
-- ║  Therefore `Behavior` MUST be effect-trace-shaped (or a          ║
-- ║  projection thereof), not "exit-code-shaped" thought of as a     ║
-- ║  return value.                                                   ║
-- ║                                                                  ║
-- ║  COMPILER CORRECTNESS IS TRACE PRESERVATION ONLY.                ║
-- ║                                                                  ║
-- ║  The compile-correct theorem says: the compiled bytes invoke    ║
-- ║  the same SigOp calls (same name, args, order) as the source    ║
-- ║  intends. It DOES NOT say anything about what those SigOp       ║
-- ║  calls *do* — whether the exit syscall terminates, whether      ║
-- ║  a write syscall outputs bytes, etc. That is the                ║
-- ║  INTERPRETATION's responsibility, proven separately per SigOp   ║
-- ║  (or postulated by the Once programmer using their interpretation║
-- ║  layer in `Strata/Interpretations/...`).                         ║
-- ║                                                                  ║
-- ║  End-to-end behavioural correctness is the COMPOSITION of:       ║
-- ║    - compiler's trace preservation (this module)                 ║
-- ║    - interpretation's protocol conformance (separate, per impl) ║
-- ║                                                                  ║
-- ║  Don't conflate the two. Don't put protocol obligations on the   ║
-- ║  compiler. Don't put trace obligations on the interpretation.    ║
-- ╚══════════════════════════════════════════════════════════════════╝
--
-- For Layer 0 the only SigOp a program can call is the exit syscall,
-- so the trace is always `[(<exit-syscall>, N)]`. The argument N is
-- what humans call "the exit code." We could pick any of these
-- equivalent shapes for `Behavior`:
--
--   (a) `Behavior = List SigOpEvent`
--       — the full trace; richest, future-proof for richer effects.
--   (b) `Behavior = Maybe ℕ`
--       — the argument of the final exit-syscall event, or `nothing`
--         if the program didn't call exit. Coarser but matches what
--         Layer 0 cares about.
--
-- We pick (b) for Layer 0 since it's the smallest correct observable.
-- Layer-1+ work will widen to (a).
--
-- This is a CHOICE of observable, not a derived consequence of CCC
-- / structural-recursion laws. Those laws prove equalities between
-- source terms; this declares what counts as observably-equivalent
-- to the outside world.
------------------------------------------------------------------------

module Once.Denotation.Behavior where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n)
open import Data.List using (List; []; _∷_; _++_; length; take)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Once.Denotation.Trace using (SigOpEvent)
import Once.Grammar as G

------------------------------------------------------------------------
-- Behavior — THE observable: the ordered sequence of SigOp invocations
-- a program makes (name + arguments). A Once program returns nothing;
-- this trace is the only thing observable. An exit syscall with arg N is just one
-- SigOp whose argument is `N` — there is no privileged "exit code."
--
-- EVENT-COUNT-INDEXED (D058): `Behavior n` = the first `n` EFFECTFUL SigOp
-- events, in order. The `n` counts effectful SigOps emitted — NOT execution
-- steps. A (possibly infinite) trace is the family of its event-prefixes;
-- `correct : ∀ n → exec n ≡ ⟦ src ⟧ n` is then "the same effectful SigOps in
-- the same order at every depth" — the inductive form of trace-equality for
-- TOTAL+PRODUCTIVE systems (≡ Colist bisimilarity; no co-data, nothing assumed
-- finite, NO completion). `Behavior n` is well-defined because the system is
-- PRODUCTIVE (the first `n` events fire after finitely much work); any step-fuel
-- inside an interpreter is an INTERNAL totality device, never this index.
-- (Was wrongly documented "prefix within `n` STEPS"; step-indexing was a
-- productivity-avoidance compromise — see D058.)
------------------------------------------------------------------------

-- D179: the index's meaning is now STRUCTURAL, not documented.
--
-- The header above has always said `Behavior n` is "the first `n` events", and
-- that any step-fuel is internal and "never this index". Nothing enforced it:
-- `ℕ → List SigOpEvent` admits families that RETRACT — where observing further
-- rewrites what was already observed — which is not a trace of anything.
--
-- `extends` says the only thing a prefix family may do: observing one event
-- further APPENDS. That is what makes the index an observation count rather
-- than an interpreter's fuel, and it is what lets composition thread a BUDGET
-- (f consumes some of it, g gets the rest) instead of capping each component
-- at the same `n` and then being unable to join the halves.
--
-- This is a SPEC change of the OCP-0005 kind: it does not alter what the spec
-- CLAIMS, it makes the claim unsayable to violate (cf. D159's relocatable
-- codomain). `TraceMonad` stays OUTSIDE the spec — it is HOW this family is
-- computed, and it must support `extends` or `runMainᵈ` will not typecheck.
record Behavior : Set where
  constructor mkBehavior
  field
    at      : ℕ → List SigOpEvent
    -- "the first `n` events" entails BOTH of these, and the header has always
    -- claimed it. They are not chosen for what a downstream proof needs —
    -- they are what the sentence above says.
    extends : ∀ n → ∃[ rest ] (at (suc n) ≡ at n ++ rest)
    bounded : ∀ n → length (at n) ≤ n
    -- D179: a family that has not filled its budget is FINISHED.
    --
    -- Without this the other two still admit a family that produces at the
    -- wrong RATE: `at₁ n` = the first `min n ∣L∣` events and `at₂ n` = the
    -- first `min (n/2) ∣L∣` are both bounded chains converging on the same
    -- trace `L`, yet they differ at `n = 1`. Since `_≋_` is pointwise, the two
    -- would count as different behaviours — so `≋` would be comparing rate as
    -- well as trace, and a compiler could be observationally correct and still
    -- fail it for reaching its third event one index later than the meaning.
    --
    -- With it, `at` is pinned to ONE family per trace (`at-stable` below), so
    -- pointwise equality IS trace equality — the inductive stand-in for
    -- bisimilarity this header has always claimed, now earned rather than
    -- asserted. Still no co-data and no completion.
    saturates : ∀ n → length (at n) < n → at (suc n) ≡ at n

open Behavior public

------------------------------------------------------------------------
-- Canonicity: `at n` IS "the first `n` events" of what you would see later.
--
-- This is the whole reason `saturates` is a field. It says the family is
-- determined by its limit, so two Behaviors agree pointwise exactly when they
-- are prefix families of the same trace.
--
-- Each field is used exactly once, which is the evidence that the three are
-- the right set rather than a set: `bounded` for the base case, `extends`
-- when the later index has already passed `n`, `saturates` when it has not.
------------------------------------------------------------------------

private
  take-all : ∀ n (xs : List SigOpEvent) → length xs ≤ n → take n xs ≡ xs
  take-all zero    []       _       = refl
  take-all (suc n) []       _       = refl
  take-all (suc n) (x ∷ xs) (s≤s h) = cong (x ∷_) (take-all n xs h)

  take-++-≤ : ∀ n (xs ys : List SigOpEvent) → n ≤ length xs → take n (xs ++ ys) ≡ take n xs
  take-++-≤ zero    xs       ys _       = refl
  take-++-≤ (suc n) (x ∷ xs) ys (s≤s h) = cong (x ∷_) (take-++-≤ n xs ys h)

  -- One index further leaves everything already observed untouched.
  step : ∀ (b : Behavior) n m → n ≤ m → take n (at b m) ≡ take n (at b (suc m))
  step b n m n≤m = go (m≤n⇒m<n∨m≡n (bounded b m))
    where
      go : length (at b m) < m ⊎ length (at b m) ≡ m
         → take n (at b m) ≡ take n (at b (suc m))
      -- `b` has not filled its budget at `m`, so it is finished: nothing moves.
      go (inj₁ lt) = cong (take n) (sym (saturates b m lt))
      -- `b` filled its budget, so `n ≤ m = length (at b m)`: the new events
      -- land beyond what `take n` can see.
      go (inj₂ eq) with extends b m
      ... | r , ext = sym (trans (cong (take n) ext)
                                 (take-++-≤ n (at b m) r (subst (n ≤_) (sym eq) n≤m)))

at-stable : ∀ (b : Behavior) n m → n ≤ m → at b n ≡ take n (at b m)
-- `n ≤ 0` forces `n ≡ 0` (matching `z≤n`), and `bounded` then forces
-- `at b 0 ≡ []`, which is what `take 0` gives.
at-stable b .zero zero z≤n = sym (take-all zero (at b zero) (bounded b zero))
at-stable b n (suc m) n≤sm = go (m≤n⇒m<n∨m≡n n≤sm)
  where
    go : n < suc m ⊎ n ≡ suc m → at b n ≡ take n (at b (suc m))
    go (inj₁ (s≤s n≤m)) = trans (at-stable b n m n≤m) (step b n m n≤m)
    go (inj₂ refl)      = sym (take-all n (at b n) (bounded b n))

------------------------------------------------------------------------
-- Source — a COMPLETE compilation unit, anchored at the raw program TEXT
-- (Framing A; Plan 0.51 resolver-into-apex; Plan 0.52 front-end-into-apex).
--
-- The object whose correctness we assert is the user's program SOURCE TEXT
-- together with its resolved import environment (`ModuleMap`, built by trusted
-- I/O). Anchoring at `String` (not a pre-parsed `GModule`) pulls the WHOLE
-- front-end — lexer + parser — INSIDE the verified `compile`
-- (`Once.Adequacy.SourceTrace.srcToModule` = `parseStrict` then `resolveImports`),
-- so lexer/parser correctness becomes part of the apex
-- (`Once.Adequacy.FrontEndBridge`) rather than a trusted step. Likewise the
-- import resolver (`Once.Spec.Resolution`). Both are the spec-anticipated
-- "separate compilation" / complete-program absorption, leaving
-- `Once.Adequacy`'s `compile`/`correct` arity untouched. (Text-anchoring also
-- matches what the binary actually has — raw source — so the apex `compile` is
-- the function the CLI can route through.)
------------------------------------------------------------------------

open import Data.String using (String)
open import Once.Parser.Module.Resolve using (ModuleMap)

record Source : Set where
  constructor mkSource
  field
    srcImports : ModuleMap     -- resolved import environment (trusted I/O)
    srcText    : String        -- the user's program source text

------------------------------------------------------------------------
-- ⟦_⟧ — extracts the exit-syscall argument from a program's
-- effect-tree denotation. Postulated until the connector to the
-- effect-tracking interpreter lands.
--
-- IMPORTANT: this CANNOT be `extract-from-evalSurface ∘ evalSurface ε`
-- because `evalSurface` flattens `Eff Unit Unit` to `⊤ → ⊤` and
-- discards SigOp arguments via the postulated `generic-semI`.
-- Discharging this requires a richer effect-tracking interpreter
-- (free monad over SigOp, or similar) — substantive new work,
-- NOT just connector plumbing.
------------------------------------------------------------------------

-- `⟦_⟧ : Source → Behavior` is no longer postulated here. It is a real
-- definition in `Once.Adequacy.SourceTrace` (the SigOp trace of `main`,
-- via `obs`, projected to the exit code). It lives there rather than
-- here because it pulls in the whole compiler front-end (`Once.Compile`)
-- and this module is kept light (the per-arch CPU instances import it).
