-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Meaning — the reference meaning as a DIRECT denotation of
-- typing DERIVATIONS (Plan 0.58 north star, OCP-0006).
--
-- This is the IR-FREE reference semantics: recursion on the typing derivation,
-- landing in the value domain `⟦_⟧ᴰ` / trace monad `T`. It replaces the
-- `SD.⟦ realize _ ⟧ˢ` route, whose only IR contact is `Surface.Expr`'s
-- `lift-morphism`/`morph-app` leaves (a morphism represented AS `IR`) — note
-- the imports below contain NO `Once.IR`, NO `evalᴰ`.
--
-- D127: TWO REALMS, `⟦_⟧ᶜ` AND `⟦_⟧ᵢ`. The separate value realm `⟦_⟧ᵍ` and
-- morphism realm `⟦_⟧ᵐ` are gone with the judgments they denoted. A
-- combinator's arms are now context-indexed, so their meanings are produced
-- UNDER an environment and the combinator composes what comes back; at a
-- closed arm the environment is unused and the clause is the old `⟦_⟧ᵐ` one
-- verbatim. That is the sense in which this generalises rather than replaces.
------------------------------------------------------------------------

module Once.Denotation.Meaning where

open import Data.Integer using (ℤ)
import Data.Integer as ℤ
import Once.Word as OnceWord
open import Once.Float.Dyadic using (encode)
open import Once.Float.Decimal using (Decimal; decimalOf; round; negate)
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _++_)

open import Once.Type
  using (Type; Unit; Void; Int; _*_; _+_; _⇒[_]_; μ-type; Functor; ⟦_⟧T; Purity)
open import Once.CanonicalName using (CanonicalName; showCanonical; bare)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; valueT; projTrace)
-- P5: the value-domain vocabulary comes from the IR-free `ValueDomain`
-- (NOT `DenotTrace`, whose `evalᴰ` is implementation).
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; emit-D; inject; forget; coerce-functor⁻¹-D)
open import Once.Semantics.Machine using (sem-In; coerce-functor; sem-cata; sem-fmap; coerce-functor⁻¹; ⟦_⟧F)
open import Once.Functor.Translate using (WellFormedF; IsBaseType; IsConcrete; base-Unit; con-base; con-fun)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.CCC.Eval as Val using ()
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; svar; SVar) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ; lookup to lookupᵗ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (SigOpInfo; semM)
open import Once.Arith.SigOp.Builders
  using (value-info; arrow-info; str-lit-info;
         add-info; sub-info; mul-info; div-info; mod-info; neg-info;
         fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info;
         lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.TypeCheck.Judgment
  using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
         t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
         t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
         t-compose-check; t-case-copair-check; t-pair-morph-check;
         t-curry-check; t-cata-check;
         t-embed; t-lam; t-pair-lit-check;
         t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
         t-initial-app-check; t-subsume; t-arg-driven-app-check; t-var-poly-instantiate;
         t-var-poly-instantiate-infer;
         t-int; t-float; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified;
         t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-neg-float; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-let; t-case;
         t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
         t-terminal-app; t-apply-app-infer; t-app; t-effApp)

------------------------------------------------------------------------
-- P1 scaffolds (discharged in P2). NAMED and narrow — each is exactly one
-- rule's semantics that needs machinery this file does not yet set up.
------------------------------------------------------------------------

-- m-cata: the event-tracking structural fold, IR-free — a direct-algebra mirror
-- of SD's `cata-ev-algᴰ` (`evalᴰ alg` replaced by the direct algebra `dalg`).
-- DEFINITIONALLY matches `evalᴰ (Cata wf alg)` when `dalg = evalᴰ alg`, so the
-- `bridgeᵈ` cata case reduces to the (recursive) morphism bridge.
cata-ev-algᴰ-D : ∀ {F : Functor} {A : Type} → ℕ → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ)
               → ⟦ F ⟧F (List SigOpEvent × ⟦ A ⟧ᴰ) → List SigOpEvent × ⟦ A ⟧ᴰ
cata-ev-algᴰ-D {F} {A} n dalg fc =
  ( events-F F proj₁ fc ++ₗ projTrace (dalg z) n
  , valueT (dalg z) n )
  where z = coerce-functor⁻¹-D F A (sem-fmap F proj₂ fc)

cata-sem : ∀ {F : Functor} {A : Type} → WellFormedF F
         → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ) → ⟦ μ-type F ⟧ᴰ → T ⟦ A ⟧ᴰ
cata-sem {F} {A} wf dalg v = λ n →
  let r = sem-cata wf (cata-ev-algᴰ-D {F} {A} n dalg) (forget v)
  in (proj₁ r , proj₂ r)

-- g-In: the initial-algebra constructor `⟦F⟧T (μF) → μF` at the value level.
-- DEFINITIONALLY `eval (In wf Heap) ∘ forget` (first-order data is pure), so the
-- `bridgeᵈ` case for `g-In` is a `forget`-coercion step.
in-value : ∀ {F : Functor} → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ → ⟦ μ-type F ⟧ᴰ
in-value {F} x = sem-In F (coerce-functor F (μ-type F) (forget x))

-- m-named / m-named-resolved: the named arrow's meaning, IR-free. This is
-- DEFINITIONALLY `evalᴰ (SigOp (value-info cn))` (same RHS), so the `bridgeᵈ`
-- case for a named morphism is `refl`.
-- Plan 0.74 J5: takes the target's numerics, because `semM` does now.
named-sem : ∀ {A B : Type} → TargetNum → CanonicalName → IsBaseType A → IsConcrete B → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
named-sem {A} {B} fmt cn bA cB a =
  λ _ → (emit-D (value-info {A} {B} cn bA cB) (forget a) , inject (semM (value-info {A} {B} cn bA cB) fmt (forget a)))


------------------------------------------------------------------------
-- (P3) The env — IR-free positional lookup into `⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ`.
------------------------------------------------------------------------

lookupᴰ : ∀ {n} (Γ : Ctx n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ lookupᵗ Γ i ⟧ᴰ
lookupᴰ (Γ , A ^ q) zero    (dγ , a) = a
lookupᴰ (Γ , A ^ q) (suc i) (dγ , a) = lookupᴰ Γ i dγ

svarᴰ : ∀ {n} {Γ : Ctx n} {Ψ A} → SVar Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ A ⟧ᴰ
svarᴰ {Γ = Γ} (svar i) dγ = lookupᴰ Γ i dγ

-- A closed named/sigop value reference (matches SD's `poly`/`closure`), IR-free.
sigOpValᴰ : ∀ {B} → TargetNum → SigOpInfo Unit B → T ⟦ B ⟧ᴰ
sigOpValᴰ fmt si = λ _ → (emit-D si tt , inject (semM si fmt tt))

-- An EXTERNAL sigop reference (`t-var-qualified/resolved/import`, realized to
-- SD's `sigOp`). DISPATCHES ON RESULT-TYPE SHAPE exactly like SD's `sigOp`: at
-- an ARROW type the reference is a first-order function POINTER whose effect
-- fires on APPLICATION (`arrow-info` respects the arrow's `Purity`), NOT a pure
-- `value-info` value. This is the migration's headline case (a SigOp result may
-- be a first-order fn pointer); dispatching here keeps the direct meaning FAITHFUL
-- to SD (⇒ `sigop-ref-bridge`'s arrow case is `refl`), where an un-dispatched
-- `value-info` would wrongly drop the pointee's effect.
-- Split on the WITNESS (not `A`'s shape) so `con-base` reduces at an abstract
-- base `A` — `con-fun` forces the arrow shape for the closure form.
sigOpRefᴰ : ∀ {A} → TargetNum → CanonicalName → IsConcrete A → T ⟦ A ⟧ᴰ
sigOpRefᴰ {A = A} fmt cn (con-base ib) = sigOpValᴰ fmt (value-info {Unit} {A} cn base-Unit (con-base ib))
sigOpRefᴰ fmt cn (con-fun {A = Dom} {B = Cod} {k = k} bDom cCod) =
  returnT (λ arg → λ n → ( emit-D (arrow-info {Dom} {Cod} k cn bDom cCod) (forget arg)
                         , inject (semM (arrow-info {Dom} {Cod} k cn bDom cCod) fmt (forget arg)) ))

Env : NamedCtx → Set
Env ctx = ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜᵗ ⟧ᴰ

------------------------------------------------------------------------
-- (P3) The CHECK / INFER realms — the fusion of `realize` then `SD`, made
-- IR-free: morphisms via `⟦_⟧ᵐ`, values via `⟦_⟧ᵍ`, locals via `lookupᴰ`.
------------------------------------------------------------------------

⟦_⟧ᶜ : ∀ {ctx e A Ψ} → ctx ⊢ᶜ e ∶ A ⨾ Ψ → TargetNum → Env ctx → T ⟦ A ⟧ᴰ
⟦_⟧ᵢ : ∀ {ctx e A Ψ} → ctx ⊢ᵢ e ∶ A ⨾ Ψ → TargetNum → Env ctx → T ⟦ A ⟧ᴰ

------------------------------------------------------------------------
-- D127: the categorical combinators, CONTEXT-INDEXED.
--
-- These were `⟦_⟧ᵐ`, a separate realm denoting `⟦A⟧ᴰ → T⟦B⟧ᴰ` with no
-- environment because a `⊢ᵐ` arm was closed by construction. The meanings
-- below are the SAME functions, now produced under an environment: each arm
-- is evaluated at `dγ` first, and the combinator combines the two Kleisli
-- functions that come back. At a closed arm `dγ` is unused and the two agree
-- clause for clause — which is what makes this a generalisation rather than
-- a redefinition.
--
-- The leaves are `returnT` of the plain categorical generator, as they were.
------------------------------------------------------------------------
⟦ t-id-check _ _              ⟧ᶜ fmt dγ = returnT (λ a  → returnT a)
⟦ t-fst-check _ _             ⟧ᶜ fmt dγ = returnT (λ ab → returnT (proj₁ ab))
⟦ t-snd-check _ _             ⟧ᶜ fmt dγ = returnT (λ ab → returnT (proj₂ ab))
⟦ t-terminal-morph-check _ _  ⟧ᶜ fmt dγ = returnT (λ _  → returnT tt)
⟦ t-initial-morph-check _ _   ⟧ᶜ fmt dγ = returnT (λ v  → ⊥-elim v)
⟦ t-inl-morph-check _ _       ⟧ᶜ fmt dγ = returnT (λ a  → returnT (inj₁ a))
⟦ t-inr-morph-check _ _       ⟧ᶜ fmt dγ = returnT (λ b  → returnT (inj₂ b))
⟦ t-compose-check _ df dg ⟧ᶜ fmt dγ =
  (⟦ df ⟧ᶜ fmt) dγ >>=T λ vf → (⟦ dg ⟧ᶜ fmt) dγ >>=T λ vg →
  returnT (λ a → vg a >>=T vf)
⟦ t-case-copair-check df dg ⟧ᶜ fmt dγ =
  (⟦ df ⟧ᶜ fmt) dγ >>=T λ vf → (⟦ dg ⟧ᶜ fmt) dγ >>=T λ vg →
  returnT (λ ab → [ vf , vg ]′ ab)
⟦ t-pair-morph-check df dg ⟧ᶜ fmt dγ =
  (⟦ df ⟧ᶜ fmt) dγ >>=T λ vf → (⟦ dg ⟧ᶜ fmt) dγ >>=T λ vg →
  returnT (λ a → vf a >>=T λ b → vg a >>=T λ c → returnT (b , c))
⟦ t-curry-check df ⟧ᶜ fmt dγ =
  (⟦ df ⟧ᶜ fmt) dγ >>=T λ vf → returnT (λ a → returnT (λ b → vf (a , b)))
-- The algebra is typed in the CLEARED context (plan 0.76 holds the widening
-- back for its own decision), so it runs on the empty environment — the same
-- `tt` the telescope rules use.
⟦ t-cata-check wfF dalg ⟧ᶜ fmt dγ =
  (⟦ dalg ⟧ᶜ fmt) tt >>=T λ valg → returnT (cata-sem wfF valg)
⟦ t-embed d ⟧ᶜ fmt              dγ = (⟦ d ⟧ᵢ fmt) dγ
⟦ t-lam _ d ⟧ᶜ fmt              dγ = returnT (λ a → (⟦ d ⟧ᶜ fmt) (dγ , a))
⟦ t-pair-lit-check da db ⟧ᶜ fmt dγ = (⟦ da ⟧ᶜ fmt) dγ >>=T λ a → (⟦ db ⟧ᶜ fmt) dγ >>=T λ b → returnT (a , b)
⟦ t-In-app-check _ d ⟧ᶜ fmt     dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → returnT (in-value v)
⟦ t-apply-check dp ⟧ᶜ fmt       dγ = (⟦ dp ⟧ᵢ fmt) dγ >>=T λ fa → proj₁ fa (proj₂ fa)
⟦ t-inl-app-check d ⟧ᶜ fmt      dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → returnT (inj₁ v)
⟦ t-inr-app-check d ⟧ᶜ fmt      dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → returnT (inj₂ v)
⟦ t-initial-app-check d ⟧ᶜ fmt  dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → ⊥-elim v
⟦ t-subsume d ⟧ᶜ fmt            dγ = (⟦ d ⟧ᶜ fmt) dγ
⟦ t-arg-driven-app-check _ darg df ⟧ᶜ fmt dγ = (⟦ df ⟧ᶜ fmt) dγ >>=T λ vf → (⟦ darg ⟧ᵢ fmt) dγ >>=T λ vx → vf vx
-- Plan 0.58 (telescope): a same-module def reference MEANS its closed body
-- (the body derivation is the rule's premise). Env-independent — the body is
-- typed in the empty local context (the prefix env), so discard `dγ` and feed
-- `tt`. Structural recursion (bodyD is a premise ⇒ a subterm).
⟦ t-var-poly-instantiate _ _ _ _ _ _ bodyD ⟧ᶜ fmt dγ = (⟦ bodyD ⟧ᶜ fmt) tt

⟦ t-int n ⟧ᵢ fmt                dγ = returnT (OnceWord.Width.fromℤ (int-bits fmt) n)
-- D113, in the INFER realm: same clause, same reason as `g-float` above.
⟦ t-float i f l p ⟧ᵢ fmt          dγ = returnT (round (float-format fmt) (decimalOf i f l))
⟦ t-str s ⟧ᵢ fmt                dγ = returnT (semM (str-lit-info s) fmt tt)
⟦ t-unit ⟧ᵢ fmt                 dγ = returnT tt
⟦ t-unit-var ⟧ᵢ fmt             dγ = returnT tt
⟦ t-var-local {eV = eV} _ _ ⟧ᵢ fmt dγ = returnT (svarᴰ eV dγ)
⟦_⟧ᵢ {A = A} (t-var-qualified {name = name} {alias = alias} _ conc) fmt dγ = sigOpRefᴰ {A = A} fmt (bare (alias ++ "." ++ name)) conc
⟦_⟧ᵢ {A = A} (t-var-resolved {cn = cn} _ conc) fmt dγ = sigOpRefᴰ {A = A} fmt cn conc
⟦_⟧ᵢ {A = A} (t-var-import {x = x} _ _ _ conc) fmt dγ = sigOpRefᴰ {A = A} fmt (bare x) conc
-- Plan 0.58 / D071: an infer-mode ground telescope reference MEANS its body —
-- the context projection Γ(x). The body is closed (typed in the telescope
-- prefix over the empty local env), so its meaning runs on `tt`. Structural
-- recursion (bodyD is a premise ⇒ a subterm) — same as the check-mode rule.
⟦ t-var-poly-instantiate-infer _ _ _ _ _ _ _ bodyD ⟧ᵢ fmt dγ = (⟦ bodyD ⟧ᶜ fmt) tt
⟦ t-annot d ⟧ᵢ fmt              dγ = (⟦ d ⟧ᶜ fmt) dγ
⟦ t-pair da db ⟧ᵢ fmt           dγ = (⟦ da ⟧ᵢ fmt) dγ >>=T λ a → (⟦ db ⟧ᵢ fmt) dγ >>=T λ b → returnT (a , b)
⟦ t-neg d ⟧ᵢ fmt                dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ v → returnT (semM neg-info fmt v)
-- PLAN 0.73 F3. `-3.14` MEANS the target's representation of the decimal
-- −3.14 — `round` applied to the NEGATED payload, not the word-level negation
-- of `round 3.14`. That reading is the honest one: the literal names a
-- decimal, and rounding is what the target does to a decimal (D116).
--
-- It is also the only reading available: a word-level float negation would be
-- `semM` at a float `neg-info`, and `MArithIR` is Int-only (F4). The two
-- readings agree — `round` splits sign from magnitude at `signBit (sig d)` /
-- `∣ sig d ∣`, so negating `sig` moves the sign bit and nothing else — but
-- that is a fact to PIN, not a coincidence to lean on.
⟦ t-neg-float i f l p ⟧ᵢ fmt      dγ = returnT (round (float-format fmt) (negate (decimalOf i f l)))
⟦ t-let d₁ d₂ ⟧ᵢ fmt            dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ v → (⟦ d₂ ⟧ᵢ fmt) (dγ , v)
⟦ t-case ds dl dr ⟧ᵢ fmt        dγ = (⟦ ds ⟧ᵢ fmt) dγ >>=T λ v →
                                   [ (λ a → (⟦ dl ⟧ᵢ fmt) (dγ , a)) , (λ b → (⟦ dr ⟧ᵢ fmt) (dγ , b)) ]′ v
⟦ t-binop-arith {op = OpAdd} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM add-info fmt (a , b))
⟦ t-binop-arith {op = OpSub} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM sub-info fmt (a , b))
⟦ t-binop-arith {op = OpMul} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM mul-info fmt (a , b))
-- PLAN 0.75 F4: the same three at `Float`, reading the same `semM` accessor —
-- so the float family is not a second story about what arithmetic means, it is
-- the same story with `Once.Float.Arith`'s operations behind it.
⟦ t-binop-arith-float {op = OpAdd} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fadd-info fmt (a , b))
⟦ t-binop-arith-float {op = OpSub} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fsub-info fmt (a , b))
⟦ t-binop-arith-float {op = OpMul} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fmul-info fmt (a , b))
-- `/` joins them: the quotient is correctly rounded (the sticky bit lives in
-- `FA.fdiv`) and total, so it denotes like the other three.
⟦ t-binop-arith-float {op = OpDiv} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fdiv-info fmt (a , b))
-- `%` is NOT a float arithmetic op (see `isFloatArithmeticOp`): IEEE's `fmod`
-- is a different function and needs its own decision. The witness refutes it
-- here exactly as it refutes the comparisons.
⟦ t-binop-arith-float {op = OpMod} () _ _ ⟧ᵢ
⟦ t-binop-arith-float {op = OpLt}  () _ _ ⟧ᵢ
⟦ t-binop-arith-float {op = OpLe}  () _ _ ⟧ᵢ
⟦ t-binop-arith-float {op = OpGt}  () _ _ ⟧ᵢ
⟦ t-binop-arith-float {op = OpGe}  () _ _ ⟧ᵢ
⟦ t-binop-arith-float {op = OpEq}  () _ _ ⟧ᵢ
⟦ t-binop-arith-float {op = OpNe}  () _ _ ⟧ᵢ
-- D125: the mixed forms. The widening is ITS OWN BIND, not an inline
-- application of `semM i2f-info` inside the operator's argument — so the
-- meaning mirrors the elaborated term `fadd (i2f e₁) e₂` exactly, bind for
-- bind. Inlining it typechecks and computes the same VALUE, but produces a
-- different TRACE SHAPE from `realize-infer`'s, and `MeaningBridge` then has to
-- neutralise an `++ []` that need never have appeared. Matching the shape is
-- what keeps that bridge `refl`.
⟦ t-binop-arith-float-il {op = OpAdd} _ d₁ d₂ ⟧ᵢ fmt dγ = ((⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → returnT (semM i2f-info fmt a)) >>=T λ a′ → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fadd-info fmt (a′ , b))
⟦ t-binop-arith-float-il {op = OpSub} _ d₁ d₂ ⟧ᵢ fmt dγ = ((⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → returnT (semM i2f-info fmt a)) >>=T λ a′ → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fsub-info fmt (a′ , b))
⟦ t-binop-arith-float-il {op = OpMul} _ d₁ d₂ ⟧ᵢ fmt dγ = ((⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → returnT (semM i2f-info fmt a)) >>=T λ a′ → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fmul-info fmt (a′ , b))
⟦ t-binop-arith-float-il {op = OpDiv} _ d₁ d₂ ⟧ᵢ fmt dγ = ((⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → returnT (semM i2f-info fmt a)) >>=T λ a′ → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM fdiv-info fmt (a′ , b))
⟦ t-binop-arith-float-il {op = OpMod} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpLt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpLe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpGt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpGe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpEq} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpNe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → ((⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM i2f-info fmt b)) >>=T λ b′ → returnT (semM fadd-info fmt (a , b′))
⟦ t-binop-arith-float-ir {op = OpSub} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → ((⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM i2f-info fmt b)) >>=T λ b′ → returnT (semM fsub-info fmt (a , b′))
⟦ t-binop-arith-float-ir {op = OpMul} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → ((⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM i2f-info fmt b)) >>=T λ b′ → returnT (semM fmul-info fmt (a , b′))
⟦ t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → ((⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM i2f-info fmt b)) >>=T λ b′ → returnT (semM fdiv-info fmt (a , b′))
⟦ t-binop-arith-float-ir {op = OpMod} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpLt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpLe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpGt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpGe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpEq} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpNe} () _ _ ⟧ᵢ
⟦ t-binop-arith {op = OpDiv} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM div-info fmt (a , b))
⟦ t-binop-arith {op = OpMod} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM mod-info fmt (a , b))
⟦_⟧ᵢ (t-binop-arith {op = OpLt} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpLe} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpGt} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpGe} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpEq} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpNe} () _ _) fmt
⟦ t-binop-cmp {op = OpLt} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM lt-info fmt (a , b))
⟦ t-binop-cmp {op = OpLe} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM le-info fmt (a , b))
⟦ t-binop-cmp {op = OpGt} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM gt-info fmt (a , b))
⟦ t-binop-cmp {op = OpGe} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM ge-info fmt (a , b))
⟦ t-binop-cmp {op = OpEq} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM eq-info fmt (a , b))
⟦ t-binop-cmp {op = OpNe} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM ne-info fmt (a , b))
⟦_⟧ᵢ (t-binop-cmp {op = OpAdd} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpSub} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpMul} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpDiv} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpMod} () _ _) fmt
⟦ t-id-app d ⟧ᵢ fmt             dγ = (⟦ d ⟧ᵢ fmt) dγ
⟦ t-fst-app d ⟧ᵢ fmt            dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ v → returnT (proj₁ v)
⟦ t-snd-app d ⟧ᵢ fmt            dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ v → returnT (proj₂ v)
⟦ t-terminal-app d ⟧ᵢ fmt       dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ _ → returnT tt
⟦ t-apply-app-infer d ⟧ᵢ fmt    dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ fa → proj₁ fa (proj₂ fa)
⟦ t-app _ df dx ⟧ᵢ fmt          dγ = (⟦ df ⟧ᵢ fmt) dγ >>=T λ vf → (⟦ dx ⟧ᶜ fmt) dγ >>=T λ vx → vf vx
⟦ t-effApp _ df dx ⟧ᵢ fmt       dγ = returnT (λ _ → (⟦ df ⟧ᵢ fmt) dγ >>=T λ vf → (⟦ dx ⟧ᶜ fmt) dγ >>=T λ vx → vf vx)
