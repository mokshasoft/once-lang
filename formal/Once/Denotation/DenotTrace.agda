-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
         Int; Float; Str; Buffer; Functor; ⟦_⟧T)
open import Once.CCC.IR
  using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal;
         initial; curry; apply; arr; SigOp; Cata; In; Out; Ana;
         out-μ; free-heap; const; Para; Hylo; Fuse)
open import Once.CCC.Eval as Val using (eval; appNatTr-F)   -- pure value domain `Val.⟦_⟧` + `eval`
open import Once.CCC.SigOp.Info
  using (SigOpInfo; semM; effect; EffectShape; Pure; Emits; Halts)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine
  using (sem-cata; sem-ana; sem-para; sem-In; sem-fuseNat-events;
         sem-fmap; coerce-functor; coerce-functor⁻¹; ⟦_⟧F)
open import Once.Denotation.Trace using (SigOpEvent; mkEvent)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; valueT; projTrace)
open import Once.Denotation.TraceDenote using (events-F)

------------------------------------------------------------------------
-- The monadic value domain. Mirrors `Val.⟦_⟧` EXCEPT at the arrow, which
-- becomes the Kleisli arrow into `T`.
------------------------------------------------------------------------

⟦_⟧ᴰ : Type → Set
⟦ Unit ⟧ᴰ       = ⊤
⟦ Void ⟧ᴰ       = ⊥
⟦ A * B ⟧ᴰ      = ⟦ A ⟧ᴰ × ⟦ B ⟧ᴰ
⟦ A + B ⟧ᴰ      = ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ
⟦ A ⇒[ _ ] B ⟧ᴰ = ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ          -- the monadic arrow
⟦ μ-type F ⟧ᴰ   = Val.⟦ μ-type F ⟧            -- first-order data: reuse pure
⟦ ν-type F ⟧ᴰ   = Val.⟦ ν-type F ⟧
⟦ Int ⟧ᴰ        = Val.⟦ Int ⟧
⟦ Float ⟧ᴰ      = Val.⟦ Float ⟧
⟦ Str ⟧ᴰ        = Val.⟦ Str ⟧
⟦ Buffer ⟧ᴰ     = Val.⟦ Buffer ⟧

------------------------------------------------------------------------
-- Forgetful coercions between the monadic and the pure value domains.
-- They are the identity on every type EXCEPT the arrow: `forget` runs a
-- closure and drops its trace; `inject` lifts a pure function to a
-- trace-less (pure) closure. Closure runs use observation depth `zero` —
-- a closure is a TOTAL function, so its value is depth-independent.
-- Needed to interface with the pure `semM`/`eval` for base operations.
------------------------------------------------------------------------

mutual
  forget : ∀ {A} → ⟦ A ⟧ᴰ → Val.⟦ A ⟧
  forget {Unit}       x        = x
  forget {Void}       ()
  forget {A * B}      (a , b)  = (forget a , forget b)
  forget {A + B}      (inj₁ a) = inj₁ (forget a)
  forget {A + B}      (inj₂ b) = inj₂ (forget b)
  forget {A ⇒[ _ ] B} clo      = λ va → forget (valueT (clo (inject va)) zero)
  forget {μ-type F}   x        = x
  forget {ν-type F}   x        = x
  forget {Int}        x        = x
  forget {Float}      x        = x
  forget {Str}        x        = x
  forget {Buffer}     x        = x

  inject : ∀ {A} → Val.⟦ A ⟧ → ⟦ A ⟧ᴰ
  inject {Unit}       x        = x
  inject {Void}       ()
  inject {A * B}      (a , b)  = (inject a , inject b)
  inject {A + B}      (inj₁ a) = inj₁ (inject a)
  inject {A + B}      (inj₂ b) = inj₂ (inject b)
  inject {A ⇒[ _ ] B} pf       = λ da → returnT (inject (pf (forget da)))
  inject {μ-type F}   x        = x
  inject {ν-type F}   x        = x
  inject {Int}        x        = x
  inject {Float}      x        = x
  inject {Str}        x        = x
  inject {Buffer}     x        = x

------------------------------------------------------------------------
-- The effectful-SigOp emission (unconditional: the budget is consumed by
-- `Ana`, not by individual SigOps; the first-`n` prefix is taken at the
-- top). Pure SigOps emit nothing, in lockstep with the machine.
------------------------------------------------------------------------

emit-D : ∀ {A B} → SigOpInfo A B → Val.⟦ A ⟧ → List SigOpEvent
emit-D si x with effect si
... | Pure    = []
... | Emits _ = mkEvent si x ∷ []
... | Halts _ = mkEvent si x ∷ []

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

------------------------------------------------------------------------
-- `evalᴰ` — the monadic IR interpretation (the source observable). The
-- structural cases are NATIVE (so `curry`/`apply` build/run genuine
-- Kleisli closures, closing the closure-effect gap fuel-free); `SigOp`
-- tells its event; recursion schemes delegate their trace to
-- `rec-trace-D` with the value via the pure `eval`.
------------------------------------------------------------------------

evalᴰ        : ∀ {A B} → IR A B → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
rec-trace-D  : ∀ {A B} → IR A B → Val.⟦ A ⟧ → ℕ → List SigOpEvent
-- The events algebra for the `Cata` fold: children's events (`events-F`)
-- followed by this layer's algebra events (`evalᴰ alg` on the rebuilt,
-- injected functor layer). Value carried in the pure domain (via `eval`).
cata-ev-algᴰ : ∀ {F C} → ℕ → IR (⟦ F ⟧T C) C
             → ⟦ F ⟧F (List SigOpEvent × Val.⟦ C ⟧) → List SigOpEvent × Val.⟦ C ⟧
-- `Para`'s trace algebra. `sem-para`'s algebra sees `⟦F⟧F (μF × A)` (each
-- child: its substructure `μF` + its folded result `A`); we fold into
-- `A = List × value`, applying the para-algebra `alg` to the `(μF , value)`
-- layer per node and collecting its events.
para-ev-algᴰ : ∀ {F C} → ℕ → IR (⟦ F ⟧T (μ-type F * C)) C
             → ⟦ F ⟧F (Val.⟦ μ-type F ⟧ × (List SigOpEvent × Val.⟦ C ⟧))
             → List SigOpEvent × Val.⟦ C ⟧
-- The depth-bounded unfold trace: events of the first `n` unfold layers,
-- in canonical (functor left-to-right) order, from the seed `a`.
ana-events   : ∀ {F A} → IR A (⟦ F ⟧T A) → Val.⟦ A ⟧ → ℕ → List SigOpEvent

evalᴰ id            a        = returnT a
evalᴰ (g ∘ f)       a        = evalᴰ f a >>=T evalᴰ g
evalᴰ (⟨ f , g ⟩ _) a        = evalᴰ f a >>=T λ b → evalᴰ g a >>=T λ c → returnT (b , c)
evalᴰ fst           p        = returnT (proj₁ p)
evalᴰ snd           p        = returnT (proj₂ p)
evalᴰ (inl _)       a        = returnT (inj₁ a)
evalᴰ (inr _)       b        = returnT (inj₂ b)
evalᴰ (case f g)    (inj₁ a) = evalᴰ f a
evalᴰ (case f g)    (inj₂ b) = evalᴰ g b
evalᴰ terminal      _        = returnT tt
evalᴰ initial       ()
evalᴰ (curry f _)   a        = returnT (λ b → evalᴰ f (a , b))
evalᴰ apply         p        = proj₁ p (proj₂ p)
evalᴰ arr           f        = returnT f
evalᴰ (SigOp si)    a        = λ n → (emit-D si (forget a) , inject (semM si (forget a)))
-- Recursion schemes: VALUE comes from this denotation's OWN trace-fold, NOT a
-- parallel pure `eval` — `⟦_⟧ᴰ` has ONE model (the trace semantics), exactly
-- like `⟦_⟧ˢ`. (The old catch-all routed `Cata`/`Ana` values through the pure
-- `eval`, a second value model that diverged from the trace for EFFECTFUL
-- algebras — the same category-error as the retired ℤ proof-model.) `Cata`'s
-- value is `proj₂` of its post-order fold; `Ana`'s is `sem-ana` over the
-- coalgebra's OWN (forgotten) trace-value. Structurally identical to `⟦_⟧ˢ`.
evalᴰ (Cata {F} wf {C} alg)  a = λ n →
  let r = sem-cata wf (cata-ev-algᴰ {F} {C} n alg) (forget a)
  in (proj₁ r , inject (proj₂ r))
evalᴰ (Ana {F} wf {A} coalg) a = λ n →
  ( ana-events {F} {A} coalg (forget a) n
  , inject (sem-ana F (λ a' → coerce-functor F _
              (forget (valueT (evalᴰ coalg (inject a')) 0))) (forget a)) )
evalᴰ ir            a        = λ n → (rec-trace-D ir (forget a) n , inject (eval ir (forget a)))

-- Cata is FINITE: emit its FULL fold trace (the observation depth `n` never
-- truncates a terminating fold — it bounds only the productive `Ana`). This is
-- what makes Cata and Ana COMPOSE: a Cata nested in an Ana layer emits fully,
-- matching the machine that runs that layer's fold to completion. The
-- event-prefix `take` is applied once, at the observable (⟦_⟧IR / traces-agree).
rec-trace-D (Cata {F} wf {C} alg)   x n = proj₁ (sem-cata wf (cata-ev-algᴰ {F} {C} n alg) x)
rec-trace-D (Ana {F} wf {A} coalg)  x n = ana-events {F} {A} coalg x n
rec-trace-D (In wf m)               x n = []
rec-trace-D (Out wf)                x n = []
-- Pure non-recursion-scheme constructors: no observable SigOp ⇒ no events.
rec-trace-D (out-μ wf)              x n = []
-- DERIVED schemes — the trace of the `cata`/`fuse` fold that DEFINES them
-- (reusing the value side's `sem-para`/`sem-fuse`/`sem-hylo`), `proj₁` = trace.
rec-trace-D (Para {F} wf {C} alg)   x n = proj₁ (sem-para wf (para-ev-algᴰ {F} {C} n alg) x)
-- D062 / approach A: Hylo/Fuse carry a NATURAL transformation (`NatTr`), so
-- the transform realizes no effects — its event contribution is `[]` per layer
-- (threaded as the monoid unit by `sem-fuseNat-events`), and all accumulation
-- is the algebra's, folded structurally in post-order over the total
-- `fuseNatW`. The transform's VALUE still reshapes each layer, via the
-- (effect-free) `appNatTr-F`. This is the trace of the total structural fold
-- `cataS (alg ∘ transform)` — and `fuseW` is gone from the meaning's use-chain.
-- (fuse ≡ hylo: both clauses are identical.)
rec-trace-D (Hylo {F} {G} wfF wfG {B} alg t) x n =
  proj₁ (sem-fuseNat-events _++_ [] F G wfF wfG (appNatTr-F t)
    (λ fb → let r = evalᴰ alg (inject (coerce-functor⁻¹ F B fb))
            in (projTrace r n , forget (valueT r n)))
    x)
rec-trace-D (Fuse {F} {G} wfF wfG {B} alg t) x n =
  proj₁ (sem-fuseNat-events _++_ [] F G wfF wfG (appNatTr-F t)
    (λ fb → let r = evalᴰ alg (inject (coerce-functor⁻¹ F B fb))
            in (projTrace r n , forget (valueT r n)))
    x)
rec-trace-D (free-heap r)           x n = []
rec-trace-D (const f v)         x n = []
-- Structural / pure constructors: never reached here (they have explicit
-- `evalᴰ` clauses), and emit no recursion-scheme events ⇒ `[]`.
rec-trace-D _                       x n = []

cata-ev-algᴰ {F} {C} n alg fc =
  ( events-F F proj₁ fc ++ projTrace (evalᴰ alg (inject z)) n
  , forget (valueT (evalᴰ alg (inject z)) n) )
  where z = coerce-functor⁻¹ F C (sem-fmap F proj₂ fc)

-- `Para`'s fold. Children events come from each child's `List` part
-- (`proj₁ ∘ proj₂`); the algebra runs on the `(μF , value)` layer
-- (`(proj₁ , proj₂ ∘ proj₂)` per position) and its events follow.
para-ev-algᴰ {F} {C} n alg fc =
  ( events-F F (λ p → proj₁ (proj₂ p)) fc ++ projTrace (evalᴰ alg (inject z)) n
  , forget (valueT (evalᴰ alg (inject z)) n) )
  where z = coerce-functor⁻¹ F (μ-type F * C)
              (sem-fmap F (λ p → (proj₁ p , proj₂ (proj₂ p))) fc)

ana-events         coalg a zero    = []
ana-events {F} {A} coalg a (suc m) =
  projTrace step m ++ events-F F (λ seed → ana-events {F} {A} coalg seed m) layer
  where
    step  = evalᴰ coalg (inject a)
    layer = coerce-functor F A (forget (valueT step m))
