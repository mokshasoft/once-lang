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
open import Data.Nat using (ℕ)
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

obs : ∀ {A B} → ℕ → IR A B → ⟦ A ⟧ → List SigOpEvent × Maybe ⟦ B ⟧
obs n (SigOp si) x = (mkEvent si x ∷ [] , just (semM si x))
obs n (g ∘ f) x with obs n f x
... | ev₁ , just y  with obs n g y
...   | ev₂ , r = (ev₁ ++ ev₂ , r)
obs n (g ∘ f) x | ev₁ , nothing = (ev₁ , nothing)
obs n (⟨ f , g ⟩ _) x with obs n f x
... | ev₁ , just b  with obs n g x
...   | ev₂ , just c  = (ev₁ ++ ev₂ , just (sem-pair b c))
...   | ev₂ , nothing = (ev₁ ++ ev₂ , nothing)
obs n (⟨ f , g ⟩ _) x | ev₁ , nothing = (ev₁ , nothing)
obs n (case f g) (inj₁ a) = obs n f a
obs n (case f g) (inj₂ b) = obs n g b
-- effectful catamorphism. The VALUE component is `eval`'s cata value
-- directly (so `obs-cata-value` is `refl`, matching the value-pure
-- convention); the EVENTS are the real fold: a `sem-cata` over the
-- carrier `List SigOpEvent × ⟦C⟧` pairing each folded child value with
-- the events emitted producing it, running `obs n alg` at each layer in
-- post-order (children's events first, then this layer's). For a
-- `SigOp`-free `alg` every layer emits `[]`, recovering `([] , just …)`.
obs n (Cata {F} wf {C} alg) x =
  (proj₁ (sem-cata wf (cata-ev-alg {F} {C} n alg) x) , just (eval (Cata wf alg) x))
-- value-pure constructors (no SigOp of their own): no events.
obs n c x = ([] , just (eval c x))

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
obs-cata-value : ∀ {F C} (n : ℕ) (wf : WellFormedF F)
                 (alg : IR (⟦ F ⟧T C) C) (x : ⟦ μ-type F ⟧)
               → proj₂ (obs n (Cata wf alg) x) ≡ just (eval (Cata wf alg) x)
obs-cata-value n wf alg x = refl

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
