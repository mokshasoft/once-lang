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

open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import Once.Type
  using (Type; Unit; _*_; μ-type; ν-type)
open import Once.CanonicalName using (CanonicalName)
open import Once.IR
  using (IR; Call; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal;
         initial; curry; apply; SigOp; Cata; In; Out; Ana; in-ν;
         out-μ; const)
open import Once.IRTy
  using (⌈_⌉; ⌈_⌉F; ⌊_⌋; ⟦_⟧TI; ⌈⟧TI-commute; μ-type; ν-type; _*_; WellFormedFI; fits-int; fits-float; IRTy)
open import Once.Float.Decimal using (round)
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
open import Once.Target.Arch using (TargetNum; module TargetNum)
open TargetNum using (int-bits; float-format)   -- pure value domain `Val.⟦_⟧` + `eval`
open import Once.SigOp.Info
  using (SigOpInfo; SigOpSem; pureV; primV; emitsV; haltsV; ffiV; callsV; FFIAnswers; module SigOpInfo)
open SigOpInfo using (name; baseA; sem; conB)
open import Once.Arith.Prim using (primSem)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Semantics.Machine
  using (sem-cata; sem-In; sem-Out; ⟦_⟧F; coerce-ν-out; coerce-ν-in)
open import Once.IRTy.WF using (wf-⌈⌉)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Once.Denotation.TraceMonad using (T; ret; call; halt; callOp; haltOp; returnT; _>>=T_; fmapT; resT)

-- Plan 0.58 (OCP-0006): the IR-FREE value domain `⟦_⟧ᴰ` + `forget`/`inject` +
-- `emit-D` moved to `Once.Denotation.ValueDomain` and re-exported here
-- (consumers unchanged), so the reference meaning `⟦_⟧ᵈ` can land in `⟦_⟧ᴰ`
-- without `Once.IR` (IR enters only at `evalᴰ` below).
open import Once.Denotation.ValueDomain

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

------------------------------------------------------------------------
-- D244/D245: the CALL ENVIRONMENT. An internal call (`Call f`) means the entry
-- `f` of the program it belongs to. `ρ f A B` is that entry as a Kleisli arrow
-- at the call's type (the direct-call morphism `once_f : A → B`, D064). The environment is built from the program's function
-- table (`Once.Denotation.Program`), each entry in the environment of the
-- entries before it, and it never needs the entry itself because there is no
-- recursion (D241). A name the table does not define at `B` is an UNLINKED call.
-- The compiler never emits one, and linkedness is what the apex carries.
------------------------------------------------------------------------

-- The call environment: the program's own definitions (D244), and the
-- interpretation's PURE FFI contracts (plan 0.105, D061). A pure FFI value is
-- a fixed function of its argument — it sees no history — so referencing it
-- is referentially transparent by its type.
record CallEnv : Set where
  constructor callEnv
  field
    callsE : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T ⟦ B ⟧ᴰᴵ
    ffiE   : FFIAnswers
open CallEnv

-- A SigOp's meaning, read off its contract. An internal or pure FFI operation
-- returns a value; an emitting one is a call answered by `⊤`; an answering one
-- is a call the interpretation answers; a halting one ends the program.
sigOpSemT : (fmt : TargetNum) → FFIAnswers → ∀ {A B} → SigOpInfo A B → SigOpSem A B → Val.⟦ A ⟧ → T Val.⟦ B ⟧
sigOpSemT fmt ans si (pureV f)     x = ret (Val.eraseᵍ (f fmt x))
sigOpSemT fmt ans si (primV p)     x = ret (Val.eraseᵍ (primSem p fmt x))
sigOpSemT fmt ans {A} si (emitsV refl) x = call (callOp (name si) A (baseA si) Unit) x (λ _ → ret tt)
sigOpSemT fmt ans {A} si (haltsV refl) x = halt (haltOp (name si) A (baseA si)) x
sigOpSemT fmt ans {A} {B} si ffiV  x = resT (ans (name si) A B x)
sigOpSemT fmt ans {A} {B} si callsV x = call (callOp (name si) A (baseA si) B) x ret

sigOpT : (fmt : TargetNum) → FFIAnswers → ∀ {A B} → SigOpInfo A B → Val.⟦ A ⟧ → T Val.⟦ B ⟧
sigOpT fmt ans si = sigOpSemT fmt ans si (sem si)

evalᴰ        : (fmt : TargetNum) → CallEnv → ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T ⟦ B ⟧ᴰᴵ
cata-ev-algᴰ : (fmt : TargetNum) → CallEnv → ∀ {F E C} → WellFormedFI F → IR (E * ⟦ F ⟧TI C) C → ⟦ E ⟧ᴰᴵ
             → ⟦ ⌈ F ⌉F ⟧F (T ⟦ C ⟧ᴰᴵ) → T ⟦ C ⟧ᴰᴵ

evalᴰ fmt ρ id            a        = returnT a
evalᴰ fmt ρ (g ∘ f)       a        = evalᴰ fmt ρ f a >>=T evalᴰ fmt ρ g
evalᴰ fmt ρ (⟨ f , g ⟩) a        = evalᴰ fmt ρ f a >>=T λ b → evalᴰ fmt ρ g a >>=T λ c → returnT (b , c)
evalᴰ fmt ρ fst           p        = returnT (proj₁ p)
evalᴰ fmt ρ snd           p        = returnT (proj₂ p)
evalᴰ fmt ρ inl           a        = returnT (inj₁ a)
evalᴰ fmt ρ inr           b        = returnT (inj₂ b)
evalᴰ fmt ρ (case f g)    (inj₁ a) = evalᴰ fmt ρ f a
evalᴰ fmt ρ (case f g)    (inj₂ b) = evalᴰ fmt ρ g b
evalᴰ fmt ρ terminal      _        = returnT tt
evalᴰ fmt ρ initial       ()
evalᴰ fmt ρ (curry f)   a        = returnT (λ b → evalᴰ fmt ρ f (a , b))
evalᴰ fmt ρ apply         p        = proj₁ p (proj₂ p)
-- A SigOp's argument and result are first-order (`baseA`, `conB`), so they
-- cross between the two value domains unchanged.
evalᴰ fmt ρ (SigOp {A} {B} si) a   =
  fmapT (λ v → subst (λ z → z) (sym (cohᴰ B)) (injectᵇ (conB si) v))
        (sigOpT fmt (ffiE ρ) si (forgetᵇ (baseA si) (subst (λ z → z) (cohᴰ A) a)))
evalᴰ fmt ρ (Call {A} {B} f) a = callsE ρ f A B a
evalᴰ fmt ρ (Cata {F} wf {E} {C} alg)  a =
  sem-cata (wf-⌈⌉ wf) (cata-ev-algᴰ fmt ρ {F} {E} {C} wf alg (proj₁ a)) (proj₂ a)
-- D273: the coalgebra reads the FIXED environment `proj₁ a` at every layer.
evalᴰ fmt ρ (Ana {F} wf {E} {A} coalg) a =
  returnT (anaFᵈ ⌈ F ⌉F
            (λ a' → fmapT (λ x → coerce-functor-D (wf-⌈⌉ wf) ⌈ A ⌉
                                   (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute F A) x))
                          (evalᴰ fmt ρ coalg (proj₁ a , a')))
            (proj₂ a))
evalᴰ fmt ρ (Out {F} wf) v =
  fmapT (λ layer → subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute F (ν-type F)))
                     (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ ν-type F ⌉
                       (coerce-ν-out (wf-⌈⌉ wf) _ layer)))
        (forceᵈ v)
evalᴰ fmt ρ (in-ν {F} wf) a =
  returnT (in-νᵈ (coerce-ν-in ⌈ F ⌉F ⟦ ⌈ ν-type F ⌉ ⟧ᴰ
                    (coerce-functor-D (wf-⌈⌉ wf) ⌈ ν-type F ⌉
                      (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute F (ν-type F)) a))))
-- μ values are first-order: the layer crosses by the functor coercion.
evalᴰ fmt ρ (In {F} wf) a =
  returnT (sem-In ⌈ F ⌉F (coerce-functor-D (wf-⌈⌉ wf) ⌈ μ-type F ⌉
                            (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute F (μ-type F)) a)))
evalᴰ fmt ρ (out-μ {F} wf) a =
  returnT (subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute F (μ-type F)))
             (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ μ-type F ⌉ (sem-Out (wf-⌈⌉ wf) a)))
evalᴰ fmt ρ (const fits-int v)   a = returnT (OnceWord.Width.fromℤ (int-bits fmt) v)
evalᴰ fmt ρ (const fits-float v) a = returnT (round (float-format fmt) v)

-- The fold's per-layer step: sequence the layer's children, then run the
-- algebra on the layer.
cata-ev-algᴰ fmt ρ {F} {E} {C} wf alg env fc =
  seqF ⌈ F ⌉F fc >>=T λ layer →
    evalᴰ fmt ρ alg (env , subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute F C))
                             (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ C ⌉ layer))

liftFn : (fmt : TargetNum) → CallEnv → ∀ {A B : Type} → IR ⌊ A ⌋ ⌊ B ⌋ → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
liftFn fmt ρ {A} {B} ir v = subst T (cohᴰ B) (evalᴰ fmt ρ ir (subst (λ z → z) (sym (cohᴰ A)) v))
