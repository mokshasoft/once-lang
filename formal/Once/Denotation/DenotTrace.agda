-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.DenotTrace — the denotational (monadic) trace semantics.
--
-- Plan 0.46. `⟦_⟧ᴰ` is the SOURCE OBSERVABLE: a compositional,
-- effect-graded, monadic interpretation of the CCC IR into the trace
-- monad `T` (Once.Denotation.TraceMonad). It is fuel-free (totality is
-- structural recursion on the IR), event-indexed (the `ℕ` of `T` is the
-- observation depth, consumed only by `Ana`), and HIGHER-ORDER-CORRECT:
--
--   ⟦ A ⇒[ k ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
--
-- so a closure already IS a trace-producing (Kleisli) function and
-- `⟦apply⟧ (clo , a) = clo a` threads the closure's events with no
-- "running" and no fuel — closing the closure-effect gap denotationally.
--
-- (M1b: this file defines the value domain `⟦_⟧ᴰ`. The IR interpretation
-- `⟦_⟧ᴰ : IR A B → ⟦A⟧ᴰ → T ⟦B⟧ᴰ` is added in M1c.)
--
-- Data (`μ`/`ν`) and base types reuse the existing PURE value domain
-- (`Once.CCC.Eval.⟦_⟧`): effects live on arrows, not inside first-order
-- data. (Effects-in-data — a `μ` whose layers carry effectful closures —
-- is a later refinement; flagged, not silently dropped.)
------------------------------------------------------------------------

module Once.Denotation.DenotTrace where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Type
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type;
         Int; Float; Str; Buffer; Functor; K; Id; _⊕_; _⊗_; ⟦_⟧T)
open import Once.IR
  using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal;
         initial; curry; apply; SigOp; Cata; In; Out; Ana;
         out-μ; free-heap; const; Para; Hylo; Fuse)
open import Once.IRTy using (⌈_⌉; ⌈_⌉F; ⌊_⌋; ⟦_⟧TI; ⌈⟧TI-commute; μ-type; ν-type; _*_; _+_)
open import Once.CCC.Eval as Val using (eval; appNatTr-F)
-- Plan 0.73 (D113): the TARGET'S FLOAT FORMAT. `⟦_⟧ᴰ` is a MACHINE-level
-- denotation, and D113 makes a float literal's machine value target-relative,
-- so the reference meaning is too. Threaded as an explicit argument rather
-- than a module parameter: `evalᴰ` is recursive, and a recursive function in
-- a parameterised module stops reducing downstream at a variable instance.
open import Once.Target.Arch using (TargetNum; int-bits; float-format)   -- pure value domain `Val.⟦_⟧` + `eval`
open import Once.SigOp.Info
  using (SigOpInfo; semM; effect; EffectShape; Pure; Emits; Halts)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine
  using (sem-cata; sem-ana; sem-para; sem-In; sem-fuseNat-events;
         sem-fmap; coerce-functor; coerce-functor⁻¹; ⟦_⟧F; coh)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Once.Denotation.Trace using (SigOpEvent; mkEvent)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; valueT; projTrace)
open import Once.Denotation.TraceDenote using (events-F)

-- Plan 0.58 (OCP-0006): the IR-FREE value domain `⟦_⟧ᴰ` + `forget`/`inject` +
-- `emit-D` moved to `Once.Denotation.ValueDomain` and re-exported here
-- (consumers unchanged), so the reference meaning `⟦_⟧ᵈ` can land in `⟦_⟧ᴰ`
-- without `Once.IR` (IR enters only at `evalᴰ` below).
open import Once.Denotation.ValueDomain public

------------------------------------------------------------------------
-- The recursion-scheme trace in the T-convention.
--   * `Cata` — a `cata-ev-alg`-style post-order fold (`sem-cata`) whose
--     per-layer events come from the NATIVE `evalᴰ alg` (effects hidden
--     inside a fold algebra, even behind closures, are captured).
--   * `Ana` — the depth-bounded unfold (`ana-events`): at depth `suc m`,
--     emit the coalgebra step's events (`evalᴰ coalg`) then recurse at `m`
--     on the functor's recursive positions in canonical order (`events-F`).
--     The observation depth is the unfold depth — a semantic, commensurable
--     notion (one machine loop iteration per layer), NOT machine steps.
--     Total by structural recursion on the depth; handles silent/sparse
--     unfolds (no "accumulate until n events" divergence).
--   * `In`/`Out` — pure constructor/destructor (`[]`).
--   * `Para`/`Hylo`/`Fuse` — DERIVED schemes, defined DENOTATIONALLY by their
--     `cata`/`ana` composition (they are not structured-recursion primitives;
--     `Cata`+`Ana` are the basis). Their trace is the trace of that fold,
--     reusing the SAME `cata`-trace algebra the value side already uses
--     (`sem-para`/`sem-fuse`/`sem-hylo` are `sem-cata`/`fuseS`-based): `Para`
--     via `sem-cata` over `para-ev-algᴰ`; `Hylo`/`Fuse` via `sem-hylo`/
--     `sem-fuse` with `cata-ev-algᴰ` as the (trace-carrying) F-algebra. The
--     `transform`/`coalg` is treated as the pure value-function, exactly as
--     `eval` does (its own events — absent for the structural deforestation
--     transforms these schemes carry — are not separately threaded). This
--     retires the `rec-trace-rest` postulate with no IR change.
------------------------------------------------------------------------

-- (P5: `coerce-functor⁻¹-D` moved to `Once.Denotation.ValueDomain` — it is
-- pure value-domain vocabulary; re-exported here via the public import.)

------------------------------------------------------------------------
-- `evalᴰ` — the monadic IR interpretation (the source observable). The
-- structural cases are NATIVE (so `curry`/`apply` build/run genuine
-- Kleisli closures, closing the closure-effect gap fuel-free); `SigOp`
-- tells its event; recursion schemes delegate their trace to
-- `rec-trace-D` with the value via the pure `eval`.
------------------------------------------------------------------------

evalᴰ        : (fmt : TargetNum) → ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T ⟦ B ⟧ᴰᴵ
rec-trace-D  : (fmt : TargetNum) → ∀ {A B} → IR A B → Val.⟦ ⌈ A ⌉ ⟧ → ℕ → List SigOpEvent
-- The events algebra for the `Cata` fold: children's events (`events-F`)
-- followed by this layer's algebra events (`evalᴰ fmt alg` on the rebuilt functor
-- layer). Plan 0.58: value carried in the MONADIC domain `⟦C⟧ᴰ` (NOT forgotten
-- to `Val.⟦C⟧`) so an effectful-arrow carrier keeps its apply-time effects.
cata-ev-algᴰ : (fmt : TargetNum) → ∀ {F C} → ℕ → IR (⟦ F ⟧TI C) C
             → ⟦ ⌈ F ⌉F ⟧F (List SigOpEvent × ⟦ C ⟧ᴰᴵ) → List SigOpEvent × ⟦ C ⟧ᴰᴵ
-- `Para`'s trace algebra. `sem-para`'s algebra sees `⟦F⟧F (μF × A)` (each
-- child: its substructure `μF` + its folded result `A`); we fold into
-- `A = List × value`, applying the para-algebra `alg` to the `(μF , value)`
-- layer per node and collecting its events.
para-ev-algᴰ : (fmt : TargetNum) → ∀ {F C} → ℕ → IR (⟦ F ⟧TI (μ-type F * C)) C
             → ⟦ ⌈ F ⌉F ⟧F (Val.⟦ ⌈ μ-type F ⌉ ⟧ × (List SigOpEvent × Val.⟦ ⌈ C ⌉ ⟧))
             → List SigOpEvent × Val.⟦ ⌈ C ⌉ ⟧
-- The depth-bounded unfold trace: events of the first `n` unfold layers,
-- in canonical (functor left-to-right) order, from the seed `a`.
ana-events   : (fmt : TargetNum) → ∀ {F A} → IR A (⟦ F ⟧TI A) → Val.⟦ ⌈ A ⌉ ⟧ → ℕ → List SigOpEvent

evalᴰ fmt id            a        = returnT a
evalᴰ fmt (g ∘ f)       a        = evalᴰ fmt f a >>=T evalᴰ fmt g
evalᴰ fmt (⟨ f , g ⟩ _) a        = evalᴰ fmt f a >>=T λ b → evalᴰ fmt g a >>=T λ c → returnT (b , c)
evalᴰ fmt fst           p        = returnT (proj₁ p)
evalᴰ fmt snd           p        = returnT (proj₂ p)
evalᴰ fmt (inl _)       a        = returnT (inj₁ a)
evalᴰ fmt (inr _)       b        = returnT (inj₂ b)
evalᴰ fmt (case f g)    (inj₁ a) = evalᴰ fmt f a
evalᴰ fmt (case f g)    (inj₂ b) = evalᴰ fmt g b
evalᴰ fmt terminal      _        = returnT tt
evalᴰ fmt initial       ()
evalᴰ fmt (curry f _)   a        = returnT (λ b → evalᴰ fmt f (a , b))
evalᴰ fmt apply         p        = proj₁ p (proj₂ p)
evalᴰ fmt (SigOp {A} {B} si) a   = λ n →
  ( emit-D si (subst (λ z → z) (coh A) (forget a))
  , subst (λ z → z) (sym (cohᴰ B)) (inject (semM si fmt (subst (λ z → z) (coh A) (forget a)))) )
-- Recursion schemes: VALUE comes from this denotation's OWN trace-fold, NOT a
-- parallel pure `eval` — `⟦_⟧ᴰ` has ONE model (the trace semantics), exactly
-- like `⟦_⟧ˢ`. (The old catch-all routed `Cata`/`Ana` values through the pure
-- `eval`, a second value model that diverged from the trace for EFFECTFUL
-- algebras — the same category-error as the retired ℤ proof-model.) `Cata`'s
-- value is `proj₂` of its post-order fold; `Ana`'s is `sem-ana` over the
-- coalgebra's OWN (forgotten) trace-value. Structurally identical to `⟦_⟧ˢ`.
evalᴰ fmt (Cata {F} wf {C} alg)  a = λ n →
  let r = sem-cata (wf-⌈⌉ wf) (cata-ev-algᴰ fmt {F} {C} n alg) (forget a)
  in (proj₁ r , proj₂ r)
evalᴰ fmt (Ana {F} wf {A} coalg) a = λ n →
  ( ana-events fmt {F} {A} coalg (forget a) n
  , inject (sem-ana ⌈ F ⌉F (λ a' → coerce-functor ⌈ F ⌉F ⌈ A ⌉
              (subst (λ T → Val.⟦ T ⟧) (⌈⟧TI-commute F A)
                (forget (valueT (evalᴰ fmt coalg (inject a')) 0)))) (forget a)) )
evalᴰ fmt ir            a        = λ n → (rec-trace-D fmt ir (forget a) n , inject (eval fmt ir (forget a)))

-- Cata is FINITE: emit its FULL fold trace (the observation depth `n` never
-- truncates a terminating fold — it bounds only the productive `Ana`). This is
-- what makes Cata and Ana COMPOSE: a Cata nested in an Ana layer emits fully,
-- matching the machine that runs that layer's fold to completion. The
-- event-prefix `take` is applied once, at the observable (⟦_⟧IR / traces-agree).
rec-trace-D fmt (Cata {F} wf {C} alg)   x n = proj₁ (sem-cata (wf-⌈⌉ wf) (cata-ev-algᴰ fmt {F} {C} n alg) x)
rec-trace-D fmt (Ana {F} wf {A} coalg)  x n = ana-events fmt {F} {A} coalg x n
rec-trace-D fmt (In wf m)               x n = []
rec-trace-D fmt (Out wf)                x n = []
-- Pure non-recursion-scheme constructors: no observable SigOp ⇒ no events.
rec-trace-D fmt (out-μ wf)              x n = []
-- DERIVED schemes — the trace of the `cata`/`fuse` fold that DEFINES them
-- (reusing the value side's `sem-para`/`sem-fuse`/`sem-hylo`), `proj₁` = trace.
rec-trace-D fmt (Para {F} wf {C} alg)   x n = proj₁ (sem-para (wf-⌈⌉ wf) (para-ev-algᴰ fmt {F} {C} n alg) x)
-- D062 / approach A: Hylo/Fuse carry a NATURAL transformation (`NatTr`), so
-- the transform realizes no effects — its event contribution is `[]` per layer
-- (threaded as the monoid unit by `sem-fuseNat-events`), and all accumulation
-- is the algebra's, folded structurally in post-order over the total
-- `fuseNatW`. The transform's VALUE still reshapes each layer, via the
-- (effect-free) `appNatTr-F`. This is the trace of the total structural fold
-- `cataS (alg ∘ transform)` — and `fuseW` is gone from the meaning's use-chain.
-- (fuse ≡ hylo: both clauses are identical.)
rec-trace-D fmt (Hylo {F} {G} wfF wfG {B} alg t) x n =
  proj₁ (sem-fuseNat-events _++_ [] ⌈ F ⌉F ⌈ G ⌉F (wf-⌈⌉ wfF) (wf-⌈⌉ wfG) (appNatTr-F fmt t)
    (λ fb → let r = evalᴰ fmt alg (inject (subst (λ T → Val.⟦ T ⟧) (sym (⌈⟧TI-commute F B)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ B ⌉ fb)))
            in (projTrace r n , forget (valueT r n)))
    x)
rec-trace-D fmt (Fuse {F} {G} wfF wfG {B} alg t) x n =
  proj₁ (sem-fuseNat-events _++_ [] ⌈ F ⌉F ⌈ G ⌉F (wf-⌈⌉ wfF) (wf-⌈⌉ wfG) (appNatTr-F fmt t)
    (λ fb → let r = evalᴰ fmt alg (inject (subst (λ T → Val.⟦ T ⟧) (sym (⌈⟧TI-commute F B)) (coerce-functor⁻¹ ⌈ F ⌉F ⌈ B ⌉ fb)))
            in (projTrace r n , forget (valueT r n)))
    x)
rec-trace-D fmt (free-heap r)           x n = []
rec-trace-D fmt (const f v)         x n = []
-- Structural / pure constructors: never reached here (they have explicit
-- `evalᴰ` clauses), and emit no recursion-scheme events ⇒ `[]`.
rec-trace-D fmt _                       x n = []

cata-ev-algᴰ fmt {F} {C} n alg fc =
  ( events-F ⌈ F ⌉F proj₁ fc ++ projTrace (evalᴰ fmt alg z) n
  , valueT (evalᴰ fmt alg z) n )
  where z = subst (λ T → ⟦ T ⟧ᴰ) (sym (⌈⟧TI-commute F C)) (coerce-functor⁻¹-D ⌈ F ⌉F ⌈ C ⌉ (sem-fmap ⌈ F ⌉F proj₂ fc))

-- `Para`'s fold. Children events come from each child's `List` part
-- (`proj₁ ∘ proj₂`); the algebra runs on the `(μF , value)` layer
-- (`(proj₁ , proj₂ ∘ proj₂)` per position) and its events follow.
para-ev-algᴰ fmt {F} {C} n alg fc =
  ( events-F ⌈ F ⌉F (λ p → proj₁ (proj₂ p)) fc ++ projTrace (evalᴰ fmt alg (inject z')) n
  , forget (valueT (evalᴰ fmt alg (inject z')) n) )
  where z = coerce-functor⁻¹ ⌈ F ⌉F ⌈ μ-type F * C ⌉
              (sem-fmap ⌈ F ⌉F (λ p → (proj₁ p , proj₂ (proj₂ p))) fc)
        z' = subst (λ T → Val.⟦ T ⟧) (sym (⌈⟧TI-commute F (μ-type F * C))) z

ana-events fmt         coalg a zero    = []
ana-events fmt {F} {A} coalg a (suc m) =
  projTrace step m ++ events-F ⌈ F ⌉F (λ seed → ana-events fmt {F} {A} coalg seed m) layer
  where
    step  = evalᴰ fmt coalg (inject a)
    layer = coerce-functor ⌈ F ⌉F ⌈ A ⌉ (subst (λ T → Val.⟦ T ⟧) (⌈⟧TI-commute F A) (forget (valueT step m)))

------------------------------------------------------------------------
-- `liftFn` — the erasure-transported IR morphism denotation as a surface
-- Kleisli arrow. `evalᴰ fmt ir : ⟦⌊A⌋⟧ᴰᴵ → T ⟦⌊B⌋⟧ᴰᴵ`; `cohᴰ` transports it to
-- `⟦A⟧ᴰ → T ⟦B⟧ᴰ` (grade-blind erasure). The shared building block for the
-- adequacy bridges: `SD.liftD = returnT ∘ liftFn fmt`, and `RelV (A⇒B)`/`cata-bridge`
-- compare against `liftFn fmt (realize… )` (Plan 0.52 M2).
------------------------------------------------------------------------

liftFn : (fmt : TargetNum) → ∀ {A B : Type} → IR ⌊ A ⌋ ⌊ B ⌋ → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
liftFn fmt {A} {B} ir v = subst T (cohᴰ B) (evalᴰ fmt ir (subst (λ z → z) (sym (cohᴰ A)) v))
