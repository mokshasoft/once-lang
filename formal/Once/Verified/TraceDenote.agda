-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.TraceDenote — the step/fuel-indexed trace denotation
-- of the CCC IR (Plan 0.24, Phase B).
--
-- `obs fuel ir x` runs `ir` on input `x`, returning the SigOp events it
-- emits (the observable trace prefix) and its output value (`just v`
-- when the run completes within `fuel`, `nothing` when it runs out —
-- which can only happen inside a productive coinductive unfold).
--
-- The effect structure lives in exactly four constructors:
--   SigOp     — emit an event
--   _∘_       — run f, then g on f's result (sequencing)
--   ⟨_,_⟩     — run f, then g, on the same input (pairing)
--   case      — dispatch on the sum value
-- Every other constructor is value-pure (no SigOp of its own) and is
-- delegated to the value evaluator `eval` with an empty event list.
--
-- NOTE (Plan 0.24 Phase B, remaining): the recursion-scheme
-- constructors (Cata/Para/Ana/Hylo/Fuse/In/out-μ/Out/in-ν) are
-- currently in the value-pure catch-all. That is faithful for folds
-- and unfolds whose algebra/coalgebra performs no SigOp (all current
-- programs). An *effectful* fold emits finitely many events; an
-- *effectful* `Ana` is the productive/reactive case and is where the
-- `fuel` parameter becomes load-bearing (recurse through the unfold,
-- decrementing fuel). Those event-collecting versions are the next
-- sub-step; the `fuel` index is already threaded so they slot in
-- without changing the interface.
------------------------------------------------------------------------

module Once.Verified.TraceDenote where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_; μ-type; ⟦_⟧T)
open import Once.CCC.IR
open import Once.CCC.Eval using (eval; ⟦_⟧)
open import Once.CCC.SigOp.Info using (semM)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine
  using (sem-pair; sem-cata; sem-fmap; coerce-functor⁻¹; ⟦_⟧F)
open import Once.Verified.Trace using (SigOpEvent; mkEvent)

------------------------------------------------------------------------
-- The step-indexed denotation.
--
-- Result: (events emitted , output value | `nothing` if out of fuel).
-- Structural recursion on the IR (the `fuel` index is threaded
-- unchanged through the effect-structural constructors; it is consumed
-- only by the — not-yet-written — recursion-scheme cases).
------------------------------------------------------------------------

-- Functor traversals used by the effectful-cata clause of `obs`.
--
-- `events-F F p fc` foldMaps the children of one functor layer into a
-- single event list, left-to-right (functor order = fold order). For
-- the Writer carrier the projection `p` reads each child's accumulated
-- events. `seq-F F` sequences a layer of `Maybe`-valued children into a
-- `Maybe` of a values-layer (a child that ran out of fuel ⇒ `nothing`).
-- Both recurse structurally on the polynomial functor code.

events-F : ∀ F {X} → (X → List SigOpEvent) → ⟦ F ⟧F X → List SigOpEvent
events-F (K _)   p x        = []
events-F Id      p x        = p x
events-F (F ⊕ G) p (inj₁ x) = events-F F p x
events-F (F ⊕ G) p (inj₂ y) = events-F G p y
events-F (F ⊗ G) p (x , y)  = events-F F p x ++ events-F G p y

-- Writer algebra for the effectful-cata events fold. Lifted to top
-- level (rather than a `where` inside `obs`) so the correctness proofs
-- can name it; mutually recursive with `obs` (the `obs n alg` call is
-- on the structurally-smaller algebra). Carrier pairs each folded child
-- value with the events emitted producing it.
cata-ev-alg : ∀ {F C} → ℕ → IR (⟦ F ⟧T C) C
            → ⟦ F ⟧F (List SigOpEvent × ⟦ C ⟧) → List SigOpEvent × ⟦ C ⟧

-- STEP-INDEXED to match the top-level observable: `Behavior n` is "the
-- prefix observed within `n` steps" (Once.Verified.Behavior). So the fuel
-- `n` decrements per evaluation step exactly as `eval` does, and `obs 0`
-- observes nothing. ONLY the trace (`proj₁`) is step-bounded; the VALUE
-- (`proj₂`) stays the denotational `eval ir x` — it is internal plumbing
-- (composition threads it), and the apex observes only the trace. So
-- `proj₂ (obs n ir x) = just (eval ir x)` for every `n`, while `proj₁`
-- accumulates only the events reachable within `n` steps. This makes
-- `obs ↔ eval` (`compiled-main-trace`) and `flat-events ↔ obs`
-- (`ir-flat-correct`) provable ∀ n for both finite (Cata) and productive
-- (Ana) traces — no stabilization or termination baked in.
obs : ∀ {A B} → ℕ → IR A B → ⟦ A ⟧ → List SigOpEvent × Maybe ⟦ B ⟧
obs zero    ir x = ([] , just (eval ir x))
obs (suc n) (SigOp si) x = (mkEvent si x ∷ [] , just (semM si x))
obs (suc n) (g ∘ f) x =
  (proj₁ (obs n f x) ++ proj₁ (obs n g (eval f x)) , just (eval (g ∘ f) x))
obs (suc n) (⟨ f , g ⟩ m) x =
  (proj₁ (obs n f x) ++ proj₁ (obs n g x) , just (eval (⟨ f , g ⟩ m) x))
obs (suc n) (case f g) (inj₁ a) = (proj₁ (obs n f a) , just (eval (case f g) (inj₁ a)))
obs (suc n) (case f g) (inj₂ b) = (proj₁ (obs n g b) , just (eval (case f g) (inj₂ b)))
-- effectful catamorphism. VALUE is `eval`'s cata value directly; EVENTS are
-- the real fold (`sem-cata` over the carrier `List SigOpEvent × ⟦C⟧`, running
-- `obs n alg` per layer in post-order). NOTE: this clause's FOLD structure is
-- not yet fully fuel-bounded — it is the LAST clause to be made step-conforming
-- (the general constructors above conform first, top-down); the fold's own
-- fuel-bounding lands when the cata leaf is wired to the ∀-n bridge.
obs (suc n) (Cata {F} wf {C} alg) x =
  (proj₁ (sem-cata wf (cata-ev-alg {F} {C} n alg) x) , just (eval (Cata wf alg) x))
-- value-pure constructors (no SigOp of their own): no events.
obs (suc n) c x = ([] , just (eval c x))

cata-ev-alg {F} {C} n alg fc =
  (events-F F proj₁ fc ++ proj₁ (obs n alg z) , eval alg z)
  where z = coerce-functor⁻¹ F C (sem-fmap F proj₂ fc)

------------------------------------------------------------------------
-- `EmitsNoSigOp ir` — the structural "pure coincidence" gate.
--
-- Plan 0.36 (2026-06-10): observable-correctness is refinement of `obs`
-- (the SigOp trace). For a `SigOp`-free IR the trace is empty, so the
-- observable degenerates to the value — this is why Layer-0 value
-- correctness silently sufficed. We make that coincidence EXPLICIT and
-- GATED: `pure-refines` may only take the value-only shortcut when
-- `EmitsNoSigOp ir` holds. An effectful constructor (e.g. a `Cata`
-- whose algebra contains a `SigOp`) fails this predicate, so the type
-- checker refuses the shortcut and forces the real `traces-agree` work.
--
-- Defined structurally on `IR`, mirroring `obs`'s event structure:
-- `SigOp` is the sole emitter (⊥); `∘`/`⟨,⟩`/`case` and the recursion
-- schemes recurse into their sub-IRs; every other constructor is a leaf
-- that emits nothing (⊤).
------------------------------------------------------------------------

-- The cata's observable VALUE is `eval`'s cata value, by construction
-- of the `obs` clause above. This is the value half of the cata's
-- `MachineRefinesObs` bridge (Plan 0.36): it lets `value-realized`
-- reuse the existing `ValidAtWF (eval …)` machinery unchanged.
-- (`obs`'s value is the denotational `eval` value at every fuel — `obs 0`
-- and `obs (suc n)` both deliver it — so this holds for all `n`.)
obs-cata-value : ∀ {F C} (n : ℕ) (wf : WellFormedF F)
                 (alg : IR (⟦ F ⟧T C) C) (x : ⟦ μ-type F ⟧)
               → proj₂ (obs n (Cata wf alg) x) ≡ just (eval (Cata wf alg) x)
obs-cata-value zero    wf alg x = refl
obs-cata-value (suc n) wf alg x = refl

EmitsNoSigOp : ∀ {A B} → IR A B → Set
EmitsNoSigOp (SigOp si)               = ⊥
EmitsNoSigOp (g ∘ f)                  = EmitsNoSigOp g × EmitsNoSigOp f
EmitsNoSigOp (⟨ f , g ⟩ _)            = EmitsNoSigOp f × EmitsNoSigOp g
EmitsNoSigOp (case f g)               = EmitsNoSigOp f × EmitsNoSigOp g
EmitsNoSigOp (curry f _)              = EmitsNoSigOp f
EmitsNoSigOp (Cata _ alg)             = EmitsNoSigOp alg
EmitsNoSigOp (Para _ alg)             = EmitsNoSigOp alg
EmitsNoSigOp (Ana _ coalg)            = EmitsNoSigOp coalg
EmitsNoSigOp (Hylo _ _ alg coalg)     = EmitsNoSigOp alg × EmitsNoSigOp coalg
EmitsNoSigOp (Fuse _ _ alg transform) = EmitsNoSigOp alg × EmitsNoSigOp transform
-- leaves: id / fst / snd / inl / inr / terminal / initial / apply / arr
--         / In / out-μ / Out / in-ν — emit nothing.
EmitsNoSigOp _                        = ⊤
