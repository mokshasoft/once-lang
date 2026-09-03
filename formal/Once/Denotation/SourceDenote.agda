-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.SourceDenote — `⟦_⟧ˢ`, THE source semantics (Plan 0.46 / OCP-0006).
--
-- The single anchor: a typed, FUEL-FREE, total+productive denotational trace
-- semantics directly over the intrinsically-typed surface `Expr` — independent of
-- `elaborate` (so the elaborator stays load-bearing: `⟦ elaborate e ⟧ᴰ ≡ ⟦ e ⟧ˢ`).
--
-- It is a structural fold of `Expr` into the SAME trace monad `T` that `⟦_⟧ᴰ`
-- (the IR view) targets — one meaning, two syntaxes. Totality is Agda's checker
-- (structural recursion on `Expr`); productivity is the `Ana` observation depth.
-- THERE IS NO FUEL: `T`'s `ℕ` is the event-observation depth (D058), consumed
-- only by `Ana`. A fuel parameter here would be a bug (it is how general recursion
-- leaked into the retired `SS.eval`).
--
-- TOP-DOWN (Plan 0.46): the effect/recursion constructors route, for now, to the
-- explicit `⟦⟧ˢ-todo` hole — each is an obligation the apex will demand, not an
-- island. Discharge them as the elaborate-correctness proof (M3) reaches them.
------------------------------------------------------------------------

module Once.Denotation.SourceDenote where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ)
import Once.Word as OnceWord
open import Data.List using (List; []; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Once.Type
  using (Type; Unit; Void; Int; Str; _*_; _+_; _⇒[_]_; Functor; ⟦_⟧T; μ-type)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ∅; ⟦_⟧ᶜ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; projTrace; valueT)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; forget; inject; emit-D; coerce-functor⁻¹-D; cohᴰ; liftFn)
open import Once.Float.Dyadic using (encode)
open import Once.Float.Decimal using (Decimal; decimalOf; round)
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.IR using (IR; ⌊_⌋)
open import Once.CCC.Eval as Val using ()
open import Once.Functor.Translate using (WellFormedF; con-fun; base-Unit)
open import Once.Semantics.Machine
  using (sem-cata; sem-ana; sem-fmap; coerce-functor; coerce-functor⁻¹; ⟦_⟧F)
open import Once.SigOp.Info using (semM)
open import Once.Arith.SigOp.Builders
open import Once.CanonicalName using (bare)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- Environment lookup: `⟦Γ⟧ᶜ` is the nested product (`∅ ↦ Unit`,
-- `Γ , A ↦ ⟦Γ⟧ᶜ * A`), so `⟦ ⟦Γ⟧ᶜ ⟧ᴰ` is `… × ⟦A⟧ᴰ`; de-Bruijn `zero`
-- is the most recent binding (`proj₂`), `suc i` recurses into `proj₁`.
------------------------------------------------------------------------

lookupᴰ : ∀ {n} (Γ : Ctx n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → ⟦ lookup Γ i ⟧ᴰ
lookupᴰ (Γ , A ^ q) fzero    dγ = proj₂ dγ
lookupᴰ (Γ , A ^ q) (fsuc i) dγ = lookupᴰ Γ i (proj₁ dγ)

------------------------------------------------------------------------
-- The `Cata` fold's per-layer trace+value algebra, over a ⟦_⟧ˢ algebra
-- CLOSURE (`⟦⟦F⟧T C⟧ᴰ → T ⟦C⟧ᴰ`) rather than an IR — the elaborate-free
-- analogue of `DenotTrace.cata-ev-algᴰ`. Carrier pairs the post-order
-- event trace with the folded (pure) value; children's events precede this
-- layer's algebra events (`projTrace (algClo …)`), value via `forget ∘ valueT`.
------------------------------------------------------------------------

-- Takes the algebra COMPUTATION `T (closure)` (= `⟦alg⟧ˢ tt`) and binds it
-- per layer (`algComp >>=T λ algClo → algClo (inject z)`), THREADING the
-- algebra's build trace per layer — mirroring exactly what `DenotTrace`'s
-- `cata-ev-algᴰ` does with `evalᴰ alg (inject z)`. (It does NOT pre-extract a
-- closure and drop its build trace; that discard was the flaw that forced a
-- `build-pure` assumption + a `morph-app` purity constraint. Threading makes
-- `faithful`'s cata case follow from the algebra IH + monad-assoc alone, and
-- handles an effectful build correctly — the trace agrees per layer on both
-- sides.)
cata-ev-algˢ : ∀ {F C} → ℕ → T (⟦ ⟦ F ⟧T C ⟧ᴰ → T ⟦ C ⟧ᴰ)
             → ⟦ F ⟧F (List SigOpEvent × ⟦ C ⟧ᴰ) → List SigOpEvent × ⟦ C ⟧ᴰ
cata-ev-algˢ {F} {C} n algComp fc =
  ( events-F F proj₁ fc ++ projTrace step n
  , valueT step n )
  where z    = coerce-functor⁻¹-D F C (sem-fmap F proj₂ fc)
        step = algComp >>=T λ algClo → algClo z

------------------------------------------------------------------------
-- The `Ana` depth-bounded unfold TRACE over a ⟦_⟧ˢ coalgebra CLOSURE — the
-- elaborate-free analogue of `DenotTrace.ana-events`. At depth `suc m`: emit the
-- coalgebra step's events then recurse at `m` on the functor's recursive
-- positions (`events-F`). Structural on `m` (Agda certifies termination of the
-- TRACE prefix; the produced codata is productive — `sem-ana` for the value).
------------------------------------------------------------------------

-- Threads the coalgebra COMPUTATION `T (closure)` (= `⟦coalg⟧ˢ tt`) per step
-- (`coalgComp >>=T λ coalgClo → coalgClo (inject a)`), mirroring `DenotTrace`'s
-- `ana-events` (`evalᴰ coalg (inject a)`) — same per-layer build threading as
-- `cata-ev-algˢ`, removing the discard that forced `build-pure`.
ana-eventsˢ : ∀ {F A} → T (⟦ A ⟧ᴰ → T ⟦ ⟦ F ⟧T A ⟧ᴰ) → Val.⟦ A ⟧ → ℕ → List SigOpEvent
ana-eventsˢ coalgComp a zero    = []
ana-eventsˢ {F} {A} coalgComp a (suc m) =
  projTrace step m
    ++ events-F F (λ seed → ana-eventsˢ {F} {A} coalgComp seed m) layer
  where step  = coalgComp >>=T λ coalgClo → coalgClo (inject a)
        layer = coerce-functor F A (forget (valueT step m))

------------------------------------------------------------------------
-- `liftD` — the surface denotation of a PRE-BUILT CCC morphism `ir : IR ⌊A⌋ ⌊B⌋`
-- (the meaning of `lift-morphism`/`morph-app`). `evalᴰ ir : ⟦⌊A⌋⟧ᴰᴵ → T ⟦⌊B⌋⟧ᴰᴵ`;
-- `cohᴰ` transports it to the surface Kleisli arrow `⟦A⟧ᴰ → T ⟦B⟧ᴰ` (grade-blind
-- erasure). Named so adequacy proofs (`RealizeAgrees`/`CataFold`) can refer to the
-- transported form without re-importing the `⟦_⟧ˢ`-mixfix (Plan 0.52 M2).
------------------------------------------------------------------------

liftD : (fmt : TargetNum) → ∀ {A B : Type} → IR ⌊ A ⌋ ⌊ B ⌋ → T (⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ)
liftD fmt {A} {B} ir = returnT (liftFn fmt ir)

------------------------------------------------------------------------
-- THE SOURCE SEMANTICS. Structural on `Expr`; arrows are Kleisli arrows
-- into `T`; `apply`/`let`/`case` thread the trace via `_>>=T_`.
------------------------------------------------------------------------

-- Plan 0.73 (D113): the format, threaded as an explicit argument. A float
-- literal has no target-free machine value, so a machine-level source
-- denotation is target-relative — see `⟦ float d _ ⟧ˢ` below, which is that
-- fact in one clause. Not a module parameter: `⟦_⟧ˢ` is recursive, and a
-- recursive function in a parameterised module stops reducing downstream.
⟦_⟧ˢ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
     → Expr Γ Ψ A → TargetNum → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → T ⟦ A ⟧ᴰ
⟦ var {Γ = Γ} i ⟧ˢ fmt dγ = returnT (lookupᴰ Γ i dγ)
⟦ lam q _ e ⟧ˢ fmt    dγ = returnT (λ a → ⟦ e ⟧ˢ fmt (dγ , a))
⟦ app f x ⟧ˢ fmt      dγ = ⟦ f ⟧ˢ fmt dγ >>=T λ vf → ⟦ x ⟧ˢ fmt dγ >>=T λ vx → vf vx
⟦ pair a b ⟧ˢ fmt     dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (va , vb)
-- D127: the combinators. These are the SAME four expressions as the
-- corresponding `⟦_⟧ᶜ` clauses in `Once.Denotation.Meaning`, and that is not a
-- coincidence to be maintained by hand — `realize-agrees` is what holds them
-- together, and it now compares like with like at every combinator.
⟦ comp' f g ⟧ˢ fmt    dγ = ⟦ f ⟧ˢ fmt dγ >>=T λ vf → ⟦ g ⟧ˢ fmt dγ >>=T λ vg →
                           returnT (λ a → vg a >>=T vf)
⟦ copair' f g ⟧ˢ fmt  dγ = ⟦ f ⟧ˢ fmt dγ >>=T λ vf → ⟦ g ⟧ˢ fmt dγ >>=T λ vg →
                           returnT (λ ab → [ vf , vg ]′ ab)
⟦ fork' f g ⟧ˢ fmt    dγ = ⟦ f ⟧ˢ fmt dγ >>=T λ vf → ⟦ g ⟧ˢ fmt dγ >>=T λ vg →
                           returnT (λ a → vf a >>=T λ b → vg a >>=T λ c → returnT (b , c))
⟦ curry' f ⟧ˢ fmt     dγ = ⟦ f ⟧ˢ fmt dγ >>=T λ vf →
                           returnT (λ a → returnT (λ b → vf (a , b)))
⟦ fst' e ⟧ˢ fmt       dγ = ⟦ e ⟧ˢ fmt dγ >>=T λ v → returnT (proj₁ v)
⟦ snd' e ⟧ˢ fmt       dγ = ⟦ e ⟧ˢ fmt dγ >>=T λ v → returnT (proj₂ v)
⟦ inl' e ⟧ˢ fmt       dγ = ⟦ e ⟧ˢ fmt dγ >>=T λ v → returnT (inj₁ v)
⟦ inr' e ⟧ˢ fmt       dγ = ⟦ e ⟧ˢ fmt dγ >>=T λ v → returnT (inj₂ v)
⟦ case' s l r ⟧ˢ fmt  dγ = ⟦ s ⟧ˢ fmt dγ >>=T λ v →
                         [ (λ a → ⟦ l ⟧ˢ fmt (dγ , a)) , (λ b → ⟦ r ⟧ˢ fmt (dγ , b)) ]′ v
⟦ unit ⟧ˢ fmt         dγ = returnT tt
⟦ absurd e ⟧ˢ fmt     dγ = ⟦ e ⟧ˢ fmt dγ >>=T λ v → ⊥-elim v
⟦ let' e1 e2 ⟧ˢ fmt   dγ = ⟦ e1 ⟧ˢ fmt dγ >>=T λ v1 → ⟦ e2 ⟧ˢ fmt (dγ , v1)
-- D054: an `Int` literal MEANS its two's-complement machine word, via
-- `Once.Word.fromℤ` — the same function the elaborator's `intLit` and the
-- blocked arith path use. It used to be `absℤ` (absolute value), so `-5` would
-- have meant 5; harmless only because no negative literal can be written yet,
-- and plan 0.73 F3 was about to change that.
-- D115: at THIS target's width, from the threaded numerics — NOT a baked
-- `Word64`. `Int` is signed two's complement (D054), so `-5` denotes
-- `2^w - 5` and is width-relative exactly as a float literal is
-- format-relative. This is the same clause as `⟦ float … ⟧`, one type over.
⟦ int n ⟧ˢ fmt        dγ = returnT (OnceWord.Width.fromℤ (int-bits fmt) n)
-- A float literal denotes ITSELF. This is 0.72 P2's payoff at the denotation:
-- `⟦ Float ⟧` IS `Dyadic`, so there is no encoder, no rounding and no abstract
-- `semM` between the literal and its meaning — unlike `str` below. The IR side
-- (`floatLit d = const fits-float d ∘ terminal`) evaluates to the same `d`, so
-- the two agree DEFINITIONALLY, exactly as they do for `int`.
-- D113: a float literal MEANS its encoding at the target's format. This is
-- the clause that makes the source denotation target-relative, and the only
-- one that does.
⟦ float d ⟧ˢ fmt      dγ = returnT (round (float-format fmt) d)
-- str: `str-lit-semM` is ABSTRACT (postulated, unlike the computing lit-int-semM),
-- so the literal's value can't be the clean `s`; denote via its own SigOp `semM`
-- (= `strLit`'s evalᴰ), matching the IR by construction (like arith).
⟦ str s ⟧ˢ fmt        dγ = returnT (semM (str-lit-info s) fmt tt)
-- Arith / comparison / div-mod: all elaborate to `SigOp <op>-info` (Pure), so
-- denote them through the SAME `semM` — `⟦ op a b ⟧ˢ` is then DEFINITIONALLY the
-- IR side `⟦ <op>IR ∘ ⟨a,b⟩ ⟧ᴰ`, making M3's elaborate-correctness trivial here.
⟦ add a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM add-info fmt (va , vb))
⟦ sub a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM sub-info fmt (va , vb))
⟦ mul a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM mul-info fmt (va , vb))
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
⟦ fadd a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM fadd-info fmt (va , vb))
⟦ fsub a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM fsub-info fmt (va , vb))
⟦ fmul a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM fmul-info fmt (va , vb))
⟦ fdiv a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM fdiv-info fmt (va , vb))
⟦ i2f a ⟧ˢ fmt       dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → returnT (semM i2f-info fmt va)
⟦ div a b ⟧ˢ fmt      dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM div-info fmt (va , vb))
⟦ mod' a b ⟧ˢ fmt     dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM mod-info fmt (va , vb))
⟦ neg e ⟧ˢ fmt        dγ = ⟦ e ⟧ˢ fmt dγ >>=T λ v → returnT (semM neg-info fmt v)
⟦ lt a b ⟧ˢ fmt       dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM lt-info fmt (va , vb))
⟦ le a b ⟧ˢ fmt       dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM le-info fmt (va , vb))
⟦ gt a b ⟧ˢ fmt       dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM gt-info fmt (va , vb))
⟦ ge a b ⟧ˢ fmt       dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM ge-info fmt (va , vb))
⟦ eq a b ⟧ˢ fmt       dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM eq-info fmt (va , vb))
⟦ ne a b ⟧ˢ fmt       dγ = ⟦ a ⟧ˢ fmt dγ >>=T λ va → ⟦ b ⟧ˢ fmt dγ >>=T λ vb → returnT (semM ne-info fmt (va , vb))
-- effApp: a SUSPENDED effect (`Unit ⇒[eff] B`) — the Eff design (D018). The
-- effectful application is deferred into the Unit-thunk; its trace fires when the
-- thunk is applied (at the top-level main run), threaded by `T`. No fork: the old
-- immediate-vs-suspended mismatch was SS.eval (retired) vs the IR; one semantics
-- now, and the Eff type IS suspended.
⟦ effApp f x ⟧ˢ fmt   dγ = returnT (λ _ → ⟦ f ⟧ˢ fmt dγ >>=T λ vf → ⟦ x ⟧ˢ fmt dγ >>=T λ vx → vf vx)
-- IR embedding: `lift-morphism`/`morph-app` inject a PRE-BUILT CCC morphism into
-- the surface; their meaning IS the IR's denotation `evalᴰ ir` (definitionally
-- matching elaborate, which maps them straight to `ir`). Not the IR-pivot — these
-- are leaves embedding a fixed morphism, not the elaboration of a user subterm.
-- Plan 0.52 M2: `ir : IR ⌊A⌋ ⌊B⌋`, so `evalᴰ ir : ⟦⌊A⌋⟧ᴰᴵ → T ⟦⌊B⌋⟧ᴰᴵ`;
-- `cohᴰ` transports it to the surface `⟦A⟧ᴰ → T ⟦B⟧ᴰ` (grade-blind erasure).
⟦ lift-morphism {A = A} {B = B} ir ⟧ˢ fmt dγ = liftD fmt {A} {B} ir
⟦ arr' f ⟧ˢ fmt       dγ = ⟦ f ⟧ˢ fmt dγ
⟦ morph-app {A = A} {B = B} ir e ⟧ˢ fmt dγ =
  ⟦ e ⟧ˢ fmt dγ >>=T λ v → subst T (cohᴰ B) (evalᴰ fmt ir (subst (λ z → z) (sym (cohᴰ A)) v))
-- Cata: the structural fold. D131 — the algebra is OBTAINED ONCE, here, and
-- the fold sees a PURE closure (`returnT valg`) at every layer. It used to
-- pass `⟦ alg ⟧ˢ fmt tt` — a computation — straight into `cata-ev-algˢ`, which
-- re-ran it per layer; an algebra that emits while being BUILT then emitted
-- once per layer. Binding it here is the same rule every other combinator arm
-- follows (D130) and matches both `⟦_⟧ᶜ` and the elaboration (`cataM ∘ ealg`).
⟦ cata {F = F} {A = A} wf alg ⟧ˢ fmt dγ =
  ⟦ alg ⟧ˢ fmt tt >>=T λ valg →
  returnT (λ x → λ n →
    let r = sem-cata wf (cata-ev-algˢ {F} {A} n (returnT valg)) x
    in (proj₁ r , proj₂ r))
-- Ana: the productive unfold. Coalgebra CLOSED (∅) → `⟦coalg⟧ˢ tt` is the
-- closure. TRACE via `ana-eventsˢ` (depth-bounded prefix, the SOLE T-ℕ consumer);
-- VALUE via `sem-ana` (the codata), mirroring `eval (Ana …)` but elaborate-free.
⟦ ana {F = F} {A = A} wf coalg ⟧ˢ fmt dγ =
  returnT (λ a → λ n →
    ( ana-eventsˢ {F} {A} (⟦ coalg ⟧ˢ fmt tt) (forget a) n
    , inject (sem-ana F (λ a' → coerce-functor F _
                  (forget (valueT (valueT (⟦ coalg ⟧ˢ fmt tt) 0 (inject a')) 0))) (forget a)) ))
-- Effect primitives (sigOp/closure/poly): named external ops resolved to
-- `generic-info name`, emitting + valued via the SAME emit-D/semM the IR uses
-- (definitionally = elaborate's `SigOp (generic-info name) ∘ terminal`). sigOp
-- DISPATCHES ON RESULT-TYPE SHAPE (matching elaborate): at an arrow it is a
-- CLOSURE applying the SigOp to its arg (so the effect fires at apply, not at
-- pair-build); at non-arrow it runs on terminal `tt`. closure/poly never wrap.
⟦ sigOp {A = (Dom ⇒[ k ] Cod)} name (con-fun bDom cCod) ⟧ˢ fmt dγ =
  returnT (λ arg → λ n → ( emit-D (arrow-info {Dom} {Cod} k name bDom cCod) (forget arg)
                         , inject (semM (arrow-info {Dom} {Cod} k name bDom cCod) fmt (forget arg)) ))
-- VALUE-position references (non-arrow sigOp, closure, poly): `Pure` via
-- `value-info` (effects live on arrows, fire on application — D018), so they
-- emit `[]` at build. This is what makes `build-pure` hold for these leaves;
-- interpretation-agnostic (no `classify-name`). Matches elaborate's
-- `SigOp (value-info name) ∘ terminal` ⇒ `faithful` stays `refl`.
⟦ sigOp {A = A} name conc ⟧ˢ fmt   dγ = λ n → (emit-D (value-info {Unit} {A} name base-Unit conc) tt , inject (semM (value-info {Unit} {A} name base-Unit conc) fmt tt))
⟦ closure {A = A} name ⟧ˢ fmt dγ = λ n → (emit-D (internal-info {A} (bare name)) tt , inject (semM (internal-info {A} (bare name)) fmt tt))
⟦ poly name PT ⟧ˢ fmt         dγ = λ n → (emit-D (internal-info {PT} (bare name)) tt , inject (semM (internal-info {PT} (bare name)) fmt tt))
