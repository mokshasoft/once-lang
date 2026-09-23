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
-- (`Once.Semantics.Machine.⟦_⟧`): effects live on arrows, not inside first-order
-- data. (Effects-in-data — a `μ` whose layers carry effectful closures —
-- is a later refinement; flagged, not silently dropped.)
------------------------------------------------------------------------

module Once.Denotation.DenotTrace where

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.List using (List; []; _∷_; _++_; take; length)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Type
  using (Type; Unit; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type;
         Int; Float; Str; Buffer; Functor; K; Id; _⊕_; _⊗_; ⟦_⟧T)
open import Once.IR
  using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal;
         initial; curry; apply; SigOp; Cata; In; Out; Ana; in-ν;
         out-μ; const)
open import Once.IRTy
  using (⌈_⌉; ⌈_⌉F; ⌊_⌋; ⟦_⟧TI; ⌈⟧TI-commute; μ-type; ν-type; _*_; _+_; IRFunctor; WellFormedFI;
         fits-int; fits-float; FitsInRegI; ⟦_,_⟧-baseI)
open import Once.Float.Decimal using (round; Decimal)
open import Data.Integer using (ℤ)
import Once.Word as OnceWord
-- plan 0.98: `eval` is NO LONGER IMPORTED. The Spec's meaning is `evalᴰ`, and
-- after the enumeration above nothing in it routes through the pure model.
-- D224 deleted `eval` outright (it is REFUTED: `IR A Void` is inhabited while
-- `⟦ Void ⟧ = ⊥`), together with `Para`/`Hylo`/`Fuse`, so there is no tie left
-- to cut.
import Once.Semantics.Machine as Val
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
  using (sem-cata; sem-ana; sem-In; sem-Out;
         sem-fmap; coerce-functor; coerce-functor⁻¹; ⟦_⟧F; coh; coerce-ν-out;
         coerce-ν-in)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Once.Denotation.Trace using (SigOpEvent; mkEvent)
open import Once.Res using (Res; returns; stopped; mapRes)
open import Once.Denotation.TraceMonad using (T; mkT; returnT; _>>=T_; valueT; stoppedT; projTrace; fmapT)
open import Data.Bool using (false)
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
--   * `Ana` — BUILDS a suspension (`anaᵈ`) and emits nothing, exactly as
--     `curry` builds a closure and emits nothing. Effects fire on DEMAND.
--   * `In` — pure constructor (`[]`).
--   * `Out` — the ν DESTRUCTOR, and the emitter of the `Ana` pair: forcing one
--     layer runs the coalgebra once and emits that layer's events. `Out` is to
--     `Ana` what `apply` is to `curry`. The trace order is therefore the order
--     the program forces layers, which is the order the machine runs them —
--     no traversal is chosen by the semantics, which is what lets a functor
--     with several recursive positions have a well-defined trace at all.
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
-- tells its event; every recursion scheme computes its trace and its value
-- from ONE model (its own monadic fold).
--
-- plan 0.98: `evalᴰ` IS ENUMERATED — there is no catch-all. The catch-all it
-- replaces routed six constructors to the pure `eval`, and the fact that
-- `SigOp` never reached it was an accident of CLAUSE ORDER rather than
-- anything the typechecker held. It now holds it: `eval` is applied at
-- exactly `In`, `out-μ` and `const` — three constructors with no sub-IR, so
-- no SigOp, so nothing that can halt. That is what makes the pure `eval`
-- (which cannot produce a value at `Void`) a legitimate value model here and
-- ONLY here.
------------------------------------------------------------------------

evalᴰ        : (fmt : TargetNum) → ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T ⟦ B ⟧ᴰᴵ
-- The two PURE leaves, named once. `In` and `out-μ` have no sub-IR, so their
-- whole meaning is a Lambek coercion over `sem-In` / `sem-Out`; naming them
-- here is what stops `DenotPrefix`'s `evalᴰ-good` restating the expression and
-- drifting from it (it used to say `eval fmt (In wf) …`, and `eval` is gone).
in-val    : ∀ (F : IRFunctor) → Val.⟦ ⌈ ⟦ F ⟧TI (μ-type F) ⌉ ⟧ → Val.⟦ ⌈ μ-type F ⌉ ⟧
out-μ-val : ∀ (F : IRFunctor) → WellFormedFI F
          → Val.⟦ ⌈ μ-type F ⌉ ⟧ → Val.⟦ ⌈ ⟦ F ⟧TI (μ-type F) ⌉ ⟧
-- A literal's machine value, materialised at the TARGET's width/format (D115):
-- the payload is source syntax, and this is the single point at which it
-- becomes bits.
const-val : (fmt : TargetNum) → ∀ {A} → FitsInRegI A
          → ⟦ ℤ , Decimal ⟧-baseI A → Val.⟦ ⌈ A ⌉ ⟧
-- The events algebra for the `Cata` fold: children's events (`events-F`)
-- followed by this layer's algebra events (`evalᴰ fmt alg` on the rebuilt functor
-- layer). Plan 0.58: value carried in the MONADIC domain `⟦C⟧ᴰ` (NOT forgotten
-- to `Val.⟦C⟧`) so an effectful-arrow carrier keeps its apply-time effects.
-- D131: the algebra reads a fixed environment, so the trace algebra takes the
-- environment VALUE — obtained once by the caller, outside the fold.
-- D179: the fold's carrier is a COMPUTATION, and the layer is sequenced
-- (`seqF`) before the algebra runs. The `ℕ` is gone: the budget now lives in
-- `T` and is threaded by `_>>=T_`, so the children share one budget instead of
-- each receiving the full `n` and having their traces concatenated. That
-- concatenation is what made `length (at n) ≤ n` false for a `k`-layer fold.
cata-ev-algᴰ : (fmt : TargetNum) → ∀ {F E C} → IR (E * ⟦ F ⟧TI C) C → ⟦ E ⟧ᴰᴵ
             → ⟦ ⌈ F ⌉F ⟧F (T ⟦ C ⟧ᴰᴵ) → T ⟦ C ⟧ᴰᴵ

const-val fmt fits-int   v = OnceWord.Width.fromℤ (int-bits fmt) v
const-val fmt fits-float v = round (float-format fmt) v

in-val F x = sem-In ⌈ F ⌉F (coerce-functor ⌈ F ⌉F ⌈ μ-type F ⌉
               (subst (λ T → Val.⟦ T ⟧) (⌈⟧TI-commute F (μ-type F)) x))
out-μ-val F wf x = subst (λ T → Val.⟦ T ⟧) (sym (⌈⟧TI-commute F (μ-type F)))
                     (coerce-functor⁻¹ ⌈ F ⌉F ⌈ μ-type F ⌉ (sem-Out (wf-⌈⌉ wf) x))

evalᴰ fmt id            a        = returnT a
evalᴰ fmt (g ∘ f)       a        = evalᴰ fmt f a >>=T evalᴰ fmt g
evalᴰ fmt (⟨ f , g ⟩) a        = evalᴰ fmt f a >>=T λ b → evalᴰ fmt g a >>=T λ c → returnT (b , c)
evalᴰ fmt fst           p        = returnT (proj₁ p)
evalᴰ fmt snd           p        = returnT (proj₂ p)
evalᴰ fmt inl           a        = returnT (inj₁ a)
evalᴰ fmt inr           b        = returnT (inj₂ b)
evalᴰ fmt (case f g)    (inj₁ a) = evalᴰ fmt f a
evalᴰ fmt (case f g)    (inj₂ b) = evalᴰ fmt g b
evalᴰ fmt terminal      _        = returnT tt
evalᴰ fmt initial       ()
evalᴰ fmt (curry f)   a        = returnT (λ b → evalᴰ fmt f (a , b))
evalᴰ fmt apply         p        = proj₁ p (proj₂ p)
-- plan 0.97: THE ONE CLAUSE WHERE A PROGRAM STOPS. `Halts` and `Emits` used
-- to be indistinguishable here — one event each, value `tt`, computation
-- continues — so the Spec said a program carries on after `exit`. `stops-D`
-- is the difference.
evalᴰ fmt (SigOp {A} {B} si) a   =
  mkT (λ n → emit-Dᵇ si (subst (λ z → z) (coh A) (forget a)) n)
      (mapRes (λ v → subst (λ z → z) (sym (cohᴰ B)) (inject v))
              (semM si fmt (subst (λ z → z) (coh A) (forget a))))
-- Recursion schemes: VALUE comes from this denotation's OWN trace-fold, NOT a
-- parallel pure `eval` — `⟦_⟧ᴰ` has ONE model (the trace semantics), exactly
-- like `⟦_⟧ˢ`. (The old catch-all routed `Cata`/`Ana` values through the pure
-- `eval`, a second value model that diverged from the trace for EFFECTFUL
-- algebras — the same category-error as the retired ℤ proof-model.) `Cata`'s
-- value is `proj₂` of its post-order fold; `Ana`'s is `sem-ana` over the
-- coalgebra's OWN (forgotten) trace-value. Structurally identical to `⟦_⟧ˢ`.
-- D131: `a` is the pair `(env , μ-value)`. The environment is projected ONCE,
-- here, and closed over by the per-layer algebra — the fold never rebuilds it.
evalᴰ fmt (Cata {F} wf {E} {C} alg)  a =
  sem-cata (wf-⌈⌉ wf) (cata-ev-algᴰ fmt {F} {E} {C} alg (proj₁ a)) (forget (proj₂ a))
-- D179: `Ana` BUILDS the suspension and emits NOTHING — exactly as `curry`
-- builds a closure and emits nothing, with `apply` firing the effects. The
-- coalgebra runs when a layer is FORCED, at `Out`.
--
-- What this replaces: the value used to be `sem-ana` over the coalgebra read
-- at budget `0` (i.e. with its effects DISCARDED, because a pure `ν` could not
-- carry them), and the discarded effects were then re-invented by `ana-events`
-- as an eager left-to-right unfold to depth `n`. Those two traversals disagree
-- whenever the functor has more than one recursive position, because the
-- left child's newly-discovered events DISPLACE the right child's. No order
-- is invented here, so nothing can disagree.
evalᴰ fmt (Ana {F} wf {A} coalg) a =
  returnT (anaFᵈ ⌈ F ⌉F
            (λ a' → fmapT (λ x → coerce-functor-D ⌈ F ⌉F ⌈ A ⌉
                                   (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute F A) x))
                          (evalᴰ fmt coalg a'))
            a)
-- D179: `Out` is the EMITTER. Forcing one layer runs the coalgebra once, and
-- its events are that layer's. The trace order is therefore the order the
-- program forces layers — which is the order the machine runs them.
evalᴰ fmt (Out {F} wf) v =
  fmapT (λ layer → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute F (ν-type F)))
                     (coerce-functor⁻¹-D ⌈ F ⌉F ⌈ ν-type F ⌉
                       (coerce-ν-out (wf-⌈⌉ wf) _ layer)))
        (forceᵈ v)
-- plan 0.93: `in-ν` gets a NATIVE clause. It used to fall to the catch-all
-- below, and the catch-all FORGETS its input — `inject (eval fmt ir (forget a))`.
-- At `ν-type F` that round trip is lossy: `forgetν` reads each child at budget
-- ZERO and drops its events (ValueDomain.agda:63-64), so a child built by an
-- EMITTING `Ana` was specified as silent. The machine does no such thing — it
-- leaves the child's suspension pointer untouched — so the SPEC was wrong, not
-- the compiler.
--
-- The fix is the introduction form the value domain was missing, `in-νᵈ`: force
-- yields the layer AS GIVEN, children included, emitting nothing. Symmetric with
-- `Ana` (D179): both BUILD a suspension and emit NOTHING; the events come at
-- `Out`, when a layer is forced. The coercion chain is `anaFᵈ`'s
-- (ValueDomain.agda:198) with the recursion removed — `in-ν` has a layer
-- already, so there is no coalgebra to run.
evalᴰ fmt (in-ν {F} wf) a =
  returnT (in-νᵈ (coerce-ν-in ⌈ F ⌉F ⟦ ⌈ ν-type F ⌉ ⟧ᴰ
                    (coerce-functor-D ⌈ F ⌉F ⌈ ν-type F ⌉
                      (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute F (ν-type F)) a))))
-- plan 0.98: the six clauses that USED TO BE A CATCH-ALL, split by what they
-- actually are. `In`, `out-μ` and `const` have no sub-IR at all, so they can
-- emit nothing and cannot halt — the pure `eval` is their whole meaning, and
-- these are the ONLY three places it is applied.
-- plan 0.98: these are the bodies of `eval`'s own `In`/`out-μ`/`const`
-- clauses, INLINED. Each is a leaf — `sem-In`, `sem-Out`, and the literal's
-- materialisation at the target's width/format — so there is nothing to
-- delegate, and `evalᴰ` stops routing any part of the Spec's meaning through
-- the pure model. (`eval` cannot be a total `IR A B → ⟦A⟧ → ⟦B⟧` once
-- `Halts : B ≡ Void`, because `⟦ Void ⟧ = ⊥`.)
evalᴰ fmt (In {F} _) a = mkT (λ _ → []) (returns (inject (in-val F (forget a))))
evalᴰ fmt (out-μ {F} wf) a = mkT (λ _ → []) (returns (inject (out-μ-val F wf (forget a))))
evalᴰ fmt (const {A} fits v) a = mkT (λ _ → []) (returns (inject (const-val fmt {A} fits v)))

cata-ev-algᴰ fmt {F} {E} {C} alg env fc =
  seqF ⌈ F ⌉F fc >>=T λ layer →
    evalᴰ fmt alg (env , subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute F C))
                             (coerce-functor⁻¹-D ⌈ F ⌉F ⌈ C ⌉ layer))

------------------------------------------------------------------------
-- `liftFn` — the erasure-transported IR morphism denotation as a surface
-- Kleisli arrow. `evalᴰ fmt ir : ⟦⌊A⌋⟧ᴰᴵ → T ⟦⌊B⌋⟧ᴰᴵ`; `cohᴰ` transports it to
-- `⟦A⟧ᴰ → T ⟦B⟧ᴰ` (grade-blind erasure). The shared building block for the
-- adequacy bridges: `SD.liftD = returnT ∘ liftFn fmt`, and `RelV (A⇒B)`/`cata-bridge`
-- compare against `liftFn fmt (realize… )` (Plan 0.52 M2).
------------------------------------------------------------------------

liftFn : (fmt : TargetNum) → ∀ {A B : Type} → IR ⌊ A ⌋ ⌊ B ⌋ → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
liftFn fmt {A} {B} ir v = subst T (cohᴰ B) (evalᴰ fmt ir (subst (λ z → z) (sym (cohᴰ A)) v))
