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
open import Once.Res using (mapRes)
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
  using (Type; Unit; Void; Int; _*_; _+_; _⇒[_]_; μ-type; Functor; ⟦_⟧T; Purity; mk-kind; Quantity; Zero; One; Many; Ground; extractGround)
open import Once.CanonicalName using (CanonicalName; own; showCanonical; bare; canonical; NotOwn)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Data.Maybe using (just)
open import Once.Denotation.TraceMonad using (T; ret; returnT; _>>=T_; fmapT; Interp; sig; impl)
open import Data.List.Membership.Propositional using (_∈_)
-- P5: the value-domain vocabulary comes from the IR-free `ValueDomain`
-- (NOT `DenotTrace`, whose `evalᴰ` is implementation).
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; injectᵇ; forgetᵇ; coerce-functor⁻¹-D; coerce-functor-D; anaFᵈ; forceᵈ; seqF; in-νᵈ)
open import Once.Denotation.DenotTrace using (sigOpT)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0; lookupᴰUsed)
open import Once.Denotation.PhaseV using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; returnM; bindM; _>>=ᵖ_)
open import Once.Denotation.GradedOps
  using (fmapM; cata-semᵛ; ana-semᵛ; out-semᵛ; in-valueᵛ; sigOpRefᵛ; ⟦_⟧<:ᵛ)
open import Once.Semantics.Machine using (sem-In; coerce-functor; sem-cata; sem-fmap; coerce-functor⁻¹; coerce-ν-out; coerce-ν-in; ⟦_⟧F)
open import Once.Functor.Translate using (WellFormedF; IsBaseType; IsConcrete; base-Unit; con-base; con-fun)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceDenote using (events-F)
open import Data.List using (List; take) renaming (_++_ to _++ₗ_)
import Data.List as L
open import Data.Nat using (ℕ)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; svar; SVar; Usage; _↾_; _⊑ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; _+ᵘ_; _*ᵘ_; _⊔ᵘ_; zeroUsage; _∷_) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ; lookup to lookupᵗ)
open import Once.TypeCheck.Classify using (NamedCtx; PolyCtx; Imports; lookupImport)
open import Once.Denotation.DefEnv using (DefEnvOf; defAt; tailAt; ImpEnvOf; impAt)
open import Once.Type.Rigid using (KindedInstance; ground-kinded)
open import Once.TypeCheck.Raw using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.SigOp.Info using (semP; int-prim; int-pure)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Type.Sub using (sub-arr; <:-refl)
open import Once.SigOp.Info using (SigOpInfo; conB; FFIAnswers)
open import Once.Arith.SigOp.Builders
  using (value-info; arrow-info;
         add-info; sub-info; mul-info; div-info; mod-info; neg-info;
         fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info;
         lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.TypeCheck.Judgment
  using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_; _⊢ᵈ_∶_⇒[_]↦_⨾_;
         t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
         t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
         t-compose-check-g; t-compose-check-f; d-infer; d-lam; d-compose; d-id; d-fst; d-snd; d-terminal; d-initial; d-case; d-pair; d-cata; t-case-copair-check; t-pair-morph-check;
         t-curry-check; t-cata-check; t-ana-check;
         t-sub; t-lam; t-pair-lit-check;
         t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
         t-initial-app-check; t-app-spine;
         t-var-poly-instantiate;
         t-var-poly-instantiate-infer; d-poly;
         t-int; t-float; t-unit; t-unit-var; t-var-local; t-var-qualified;
         t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-neg-float; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-let; t-case;
         t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
         t-terminal-app; t-apply-app-infer; t-apply-eff-app-infer; t-Out-app-infer; t-Out-eff-app-infer; t-app; t-effApp)

------------------------------------------------------------------------
-- P1 scaffolds (discharged in P2). NAMED and narrow — each is exactly one
-- rule's semantics that needs machinery this file does not yet set up.
------------------------------------------------------------------------

-- m-cata: the event-tracking structural fold, IR-free — a direct-algebra mirror
-- of SD's `cata-ev-algᴰ` (`evalᴰ alg` replaced by the direct algebra `dalg`).
-- DEFINITIONALLY matches `evalᴰ (Cata wf alg)` when `dalg = evalᴰ alg`, so the
-- `bridgeᵈ` cata case reduces to the (recursive) morphism bridge.
-- D179: carrier is a COMPUTATION and the layer is sequenced (`seqF`) before
-- the algebra runs, so the children share ONE budget. The `ℕ` is gone — it
-- lives in `T` now. Mirrors `DenotTrace.cata-ev-algᴰ` exactly.
-- Plan 0.105: the layer crosses by the FIRST-ORDER coercion, so it takes the
-- functor's well-formedness (as `DenotTrace.cata-ev-algᴰ` does).
cata-ev-algᴰ-D : ∀ {F : Functor} {A : Type} → WellFormedF F → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ)
               → ⟦ F ⟧F (T ⟦ A ⟧ᴰ) → T ⟦ A ⟧ᴰ
cata-ev-algᴰ-D {F} {A} wf dalg fc =
  seqF F fc >>=T λ layer → dalg (coerce-functor⁻¹-D wf A layer)

-- `⟦ μ-type F ⟧ᴰ` IS the machine's μ (first-order data), so the fold reads it
-- as it is.
cata-sem : ∀ {F : Functor} {A : Type} → WellFormedF F
         → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ) → ⟦ μ-type F ⟧ᴰ → T ⟦ A ⟧ᴰ
cata-sem {F} {A} wf dalg v = sem-cata wf (cata-ev-algᴰ-D {F} {A} wf dalg) v

-- D192: the DUAL of `cata-sem`. A ν is a suspension in the meaning too — the
-- coalgebra is stored, not run, so this emits nothing and `out` is where the
-- events appear. Mirrors `⟦ ana … ⟧ˢ` (SourceDenote) exactly, which is what
-- the two-meanings agreement will need.
-- The coalgebra arrives as a COMPUTATION and is bound INSIDE the suspension,
-- not outside. That is deliberate and it is not the cata's shape: `⟦ ana ⟧ˢ`
-- and `evalᴰ (Ana …)` both read the closed coalgebra at the budget the layer
-- is forced at, and `FaithfulLemmas` relates the surface node to `IR.Ana`
-- through exactly that. Binding it outside would make this clause disagree
-- with both.
-- D233: at any grade — the value domain of a stream does not depend on it.
ana-sem : ∀ {F : Functor} {A : Type} {π : Purity} → WellFormedF F
        → T (⟦ A ⟧ᴰ → T ⟦ ⟦ F ⟧T A ⟧ᴰ) → ⟦ A ⟧ᴰ → T ⟦ Once.Type.ν-type F π ⟧ᴰ
ana-sem {F} {A} wf cT a =
  returnT (anaFᵈ F (λ a' → fmapT (coerce-functor-D wf A)
                             (cT >>=T λ clo → clo a')) a)

-- D194: FORCING a layer — the ν's eliminator, and the one place a ν emits.
-- `ana-sem` stores the coalgebra; this is where it runs. Mirrors
-- `evalᴰ (Out wf)` exactly, minus the IRTy transports (those live on the
-- other side of `⌈_⌉`).
out-sem : ∀ {F : Functor} {π : Purity} → WellFormedF F
        → ⟦ Once.Type.ν-type F π ⟧ᴰ → T ⟦ ⟦ F ⟧T (Once.Type.ν-type F π) ⟧ᴰ
out-sem {F} {π} wf v =
  fmapT (λ layer → coerce-functor⁻¹-D wf (Once.Type.ν-type F π)
                     (coerce-ν-out wf _ layer))
        (forceᵈ v)

-- g-In: the initial-algebra constructor `⟦F⟧T (μF) → μF` at the value level,
-- through the first-order layer coercion (plan 0.105: `forget` is gone; a μ
-- layer holds base values and children only).
in-value : ∀ {F : Functor} → WellFormedF F → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ → ⟦ μ-type F ⟧ᴰ
in-value {F} wf x = sem-In F (coerce-functor-D wf (μ-type F) x)

-- m-named / m-named-resolved: the named arrow's meaning, IR-free — a pure
-- FFI contract (`value-info` is `ffiV`, plan 0.105), so its value is the
-- interpretation's pure half at the argument.
named-sem : ∀ {A B : Type} → TargetNum → FFIAnswers → CanonicalName → IsBaseType A → IsBaseType B → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
named-sem {A} {B} fmt φ cn bA bB a =
  fmapT (injectᵇ bB) (sigOpT fmt φ (value-info {A} {B} cn bA bB) (forgetᵇ bA a))


------------------------------------------------------------------------
-- (P3) The env — IR-free positional lookup into `⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ`.
------------------------------------------------------------------------

lookupᴰ : ∀ {n} (Γ : Ctx n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ lookupᵗ Γ i ⟧ᴰ
lookupᴰ (Γ , A ^ q) zero    (dγ , a) = a
lookupᴰ (Γ , A ^ q) (suc i) (dγ , a) = lookupᴰ Γ i dγ

svarᴰ : ∀ {n} {Γ : Ctx n} {Ψ A} → SVar Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ A ⟧ᴰ
svarᴰ {Γ = Γ} (svar i) dγ = lookupᴰ Γ i dγ

-- | D142/D143: the RUNTIME reading. `SVar Γ Ψ A` carries its own usage
--   (`svar i : SVar Γ (singleUse i One) _`), so the environment holds exactly
--   that one variable — the chain collapses to a single projection, as
--   `lookupᴰUsed` does.
svarᴰRun : ∀ {n} {Γ : Ctx n} {Ψ A} (v : SVar Γ Ψ A) → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᴰ → ⟦ A ⟧ᴰ
svarᴰRun {Γ = Γ} (svar i) dγ = lookupᴰUsed Γ i dγ

-- A closed named/sigop value reference, IR-free: the contract's computation
-- (`sigOpT`, the IR's own dispatch), read into the value domain.
sigOpValᴰ : ∀ {B} → TargetNum → FFIAnswers → SigOpInfo Unit B → T ⟦ B ⟧ᴰ
sigOpValᴰ fmt φ si = fmapT (injectᵇ (conB si)) (sigOpT fmt φ si tt)

-- An EXTERNAL sigop reference (`t-var-qualified/resolved/import`). At an ARROW
-- type the reference is a first-order function POINTER whose effect fires on
-- APPLICATION (`arrow-info` respects the arrow's `Purity`). Split on the
-- WITNESS (not `A`'s shape) so `con-base` reduces at an abstract base `A`.
sigOpRefᴰ : ∀ {A} → TargetNum → FFIAnswers → CanonicalName → IsConcrete A → T ⟦ A ⟧ᴰ
sigOpRefᴰ {A = A} fmt φ cn (con-base ib) = sigOpValᴰ fmt φ (value-info {Unit} {A} cn base-Unit ib)
-- D143: at an ERASED arrow the symbol never receives its argument, so the
-- reference degenerates to the value form, as in `Elaborate` and `SourceDenote`.
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Zero π} bDom bCod) =
  returnT (λ _ → sigOpValᴰ fmt φ (value-info cn base-Unit bCod))
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind One π} bDom bCod) =
  returnT (λ arg → fmapT (injectᵇ bCod) (sigOpT fmt φ (arrow-info {Dom} {Cod} (mk-kind One π) cn bDom bCod) (forgetᵇ bDom arg)))
sigOpRefᴰ fmt φ cn (con-fun {A = Dom} {B = Cod} {k = mk-kind Many π} bDom bCod) =
  returnT (λ arg → fmapT (injectᵇ bCod) (sigOpT fmt φ (arrow-info {Dom} {Cod} (mk-kind Many π) cn bDom bCod) (forgetᵇ bDom arg)))

returnᵖ : ∀ {X : Set} → X → X
returnᵖ x = x

fmapᵖ : ∀ {X Y : Set} → (X → Y) → X → Y
fmapᵖ f x = f x

svarᵛRun : ∀ {n} {Γ : Ctx n} {Ψ A} (v : SVar Γ Ψ A) → ⟦ ⟦ Γ ↾ Ψ ⟧ᶜᵗ ⟧ᵛ → ⟦ A ⟧ᵛ
svarᵛRun {Γ = Γ} (svar i) dγ = lookupᵛUsed Γ i dγ

DefFamily : Once.Type.PolyType → Set
DefFamily s = (U : Type) → KindedInstance s U → ⟦ U ⟧ᵛ

DefMeanings : PolyCtx → Set
DefMeanings = DefEnvOf DefFamily

-- D246: …and the meaning of every in-scope module ENTRY at its type: an FFI
-- declaration means its contract, a monomorphic definition its body. A
-- reference to either is a call of the entry (`t-var-import`).
ImpMeanings : Imports → Set
ImpMeanings = ImpEnvOf (λ U → ⟦ U ⟧ᵛ)

record Meanings (polys : PolyCtx) (imps : Imports) : Set where
  constructor meanings
  field
    defs    : DefMeanings polys
    entries : ImpMeanings imps
    -- Plan 0.105 (D257 amendment 2): the interpretation the program runs in —
    -- its declared signatures and their implementation…
    world   : Interp
    -- …which declare what a qualified or resolved reference names (another
    -- module's FFI signature, inlined into the import table).
    decl-qual : ∀ {name alias T} → lookupImport imps (alias ++ "." ++ name) ≡ just T
              → (alias ++ "." ++ name , T) ∈ sig world
    decl-res  : ∀ {cn T} → NotOwn cn → lookupImport imps (showCanonical cn) ≡ just T
              → (showCanonical cn , T) ∈ sig world
open Meanings public

MeaningsOf : NamedCtx → Set
MeaningsOf ctx = Meanings (NamedCtx.polys ctx) (NamedCtx.imports ctx)

-- So the meaning runs over `Γ ↾ Ψ` — exactly the variables the derivation uses
-- — for the same reason `elaborate` and `⟦_⟧ˢ` do.
Env : NamedCtx → Set
Env ctx = ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜᵗ ⟧ᵛ

EnvRun : (ctx : NamedCtx) → Usage (NamedCtx.size ctx) → Set
EnvRun ctx Ψ = ⟦ ⟦ NamedCtx.debruijn ctx ↾ Ψ ⟧ᶜᵗ ⟧ᵛ

------------------------------------------------------------------------
-- (P3) The CHECK / INFER realms — the fusion of `realize` then `SD`, made
-- IR-free: morphisms via `⟦_⟧ᵐ`, values via `⟦_⟧ᵍ`, locals via `lookupᴰ`.
------------------------------------------------------------------------

⟦_⟧ᶜ : ∀ {ctx e A Ψ} → ctx ⊢ᶜ e ∶ A ⨾ Ψ → TargetNum → MeaningsOf ctx → EnvRun ctx Ψ → ⟦ A ⟧ᵛ
⟦_⟧ᵢ : ∀ {ctx e A Ψ} → ctx ⊢ᵢ e ∶ A ⨾ Ψ → TargetNum → MeaningsOf ctx → EnvRun ctx Ψ → ⟦ A ⟧ᵛ
-- Plan 0.94 §10: a domain-given derivation denotes the term AS the arrow
-- `A ⇒[π] B` it is determined to be.
-- Plan 0.94 §13: evaluate both, keep the second — what `seq` emits. A subterm
-- evaluation REACHES is run even where its value is not used.
seqᴰ : ∀ {X Y : Set} → T X → T Y → T Y
seqᴰ m₁ m₂ = (m₁ >>=T λ x → m₂ >>=T λ y → returnT (x , y)) >>=T λ v → returnT (proj₂ v)

⟦_⟧ᵈ : ∀ {ctx e A π B Ψ} → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → TargetNum → MeaningsOf ctx → EnvRun ctx Ψ
     → ⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ

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
-- The leaves are `returnᵖ` of the plain categorical generator, as they were.
------------------------------------------------------------------------
⟦_⟧ᶜ {ctx = ctx} (t-id-check {π = π}     ) fmt ρ dγ = λ a  → returnM π a
⟦_⟧ᶜ {ctx = ctx} (t-fst-check {π = π}    ) fmt ρ dγ = λ ab → returnM π (proj₁ ab)
⟦_⟧ᶜ {ctx = ctx} (t-snd-check {π = π}    ) fmt ρ dγ = λ ab → returnM π (proj₂ ab)
⟦_⟧ᶜ {ctx = ctx} (t-terminal-morph-check {π = π}) fmt ρ dγ = λ _  → returnM π tt
⟦_⟧ᶜ {ctx = ctx} (t-initial-morph-check  ) fmt ρ dγ = λ v  → ⊥-elim v
⟦_⟧ᶜ {ctx = ctx} (t-inl-morph-check {π = π}) fmt ρ dγ = λ a  → returnM π (inj₁ a)
⟦_⟧ᶜ {ctx = ctx} (t-inr-morph-check {π = π}) fmt ρ dγ = λ b  → returnM π (inj₂ b)
⟦_⟧ᶜ {ctx = ctx} (t-compose-check-g {π = π} dg df) fmt ρ dγ =
  (⟦ df ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ (Many *ᵘ _)) dγ) >>=ᵖ λ vf → (⟦ dg ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ _ (Many *ᵘ _))) dγ) >>=ᵖ λ vg →
  λ a → bindM π (vg a) vf
⟦_⟧ᶜ {ctx = ctx} (t-compose-check-f {π = π} wf p dg) fmt ρ dγ =
  fmapᵖ ⟦ p ⟧<:ᵛ ((⟦ wf ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ (Many *ᵘ _)) dγ)) >>=ᵖ λ vf → (⟦ dg ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ _ (Many *ᵘ _))) dγ) >>=ᵖ λ vg →
  λ a → bindM π (vg a) vf
⟦_⟧ᶜ {ctx = ctx} (t-case-copair-check df dg) fmt ρ dγ =
  (⟦ df ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ vf → (⟦ dg ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ vg →
  returnᵖ (λ ab → [ vf , vg ]′ ab)
⟦_⟧ᶜ {ctx = ctx} (t-pair-morph-check {π = π} df dg) fmt ρ dγ =
  (⟦ df ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ vf → (⟦ dg ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ vg →
  λ a → bindM π (vf a) λ b → bindM π (vg a) λ c → returnM π (b , c)
⟦_⟧ᶜ {ctx = ctx} (t-curry-check {π₀ = π₀} df) fmt ρ dγ =
  (⟦ df ⟧ᶜ fmt ρ) dγ >>=ᵖ λ vf → λ a → returnM π₀ (λ b → vf (a , b))
-- PLAN 0.101 (D265, D273): the algebra / coalgebra is typed in the ambient
-- context, so it reads the term's own environment `dγ`.
⟦_⟧ᶜ {ctx = ctx} (t-cata-check {π = π} wfF dalg) fmt ρ dγ =
  (⟦ dalg ⟧ᶜ fmt ρ) dγ >>=ᵖ λ valg → λ v → cata-semᵛ π wfF valg v
⟦_⟧ᶜ {ctx = ctx} (t-ana-check {π₀ = π₀} {π = π} wfF dcoalg) fmt ρ dγ =
  λ a → ana-semᵛ π π₀ wfF (returnM π₀ ((⟦ dcoalg ⟧ᶜ fmt ρ) dγ)) a
-- D226: the mode switch maps the inferred computation's RESULT along `p`.
⟦_⟧ᶜ {ctx = ctx} (t-sub d p) fmt ρ dγ = fmapᵖ ⟦ p ⟧<:ᵛ ((⟦ d ⟧ᵢ fmt ρ) dγ)
-- D143: the arrow's declared quantity `q` decides whether the meaning receives
-- an argument; the binder's usage `q'` decides whether it enters the body's
-- environment. `q' ≤q q` (the rule's own premise) rules out the off-diagonal
-- cases — an erased arrow cannot have a body that uses its argument.
⟦_⟧ᶜ {ctx = ctx} (t-lam {A = A} {q = Zero} {q' = Zero} {π = π} _ d) fmt ρ dγ = λ _ → returnM π ((⟦ d ⟧ᶜ fmt ρ) (bindᵛ0 {Γ = NamedCtx.debruijn ctx} {A = A} dγ))
⟦_⟧ᶜ {ctx = ctx} (t-lam {A = A} {q = One}  {q' = Zero} {π = π} _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᶜ fmt ρ) (bindᵛ0 {Γ = NamedCtx.debruijn ctx} {A = A} dγ))
⟦_⟧ᶜ {ctx = ctx} (t-lam {A = A} {q = Many} {q' = Zero} {π = π} _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᶜ fmt ρ) (bindᵛ0 {Γ = NamedCtx.debruijn ctx} {A = A} dγ))
⟦_⟧ᶜ {ctx = ctx} (t-lam {A = A} {q = One}  {q' = One} {π = π}  _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᶜ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} One  dγ a))
⟦_⟧ᶜ {ctx = ctx} (t-lam {A = A} {q = Many} {q' = One} {π = π}  _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᶜ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} One  dγ a))
⟦_⟧ᶜ {ctx = ctx} (t-lam {A = A} {q = Many} {q' = Many} {π = π} _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᶜ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} Many dγ a))
⟦_⟧ᶜ {ctx = ctx} (t-pair-lit-check da db) fmt ρ dγ = (⟦ da ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ db ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → returnᵖ (a , b)
⟦_⟧ᶜ {ctx = ctx} (t-In-app-check wfF d) fmt ρ dγ = (⟦ d ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ v → returnᵖ (in-valueᵛ wfF v)
⟦_⟧ᶜ {ctx = ctx} (t-apply-check dp) fmt ρ dγ = (⟦ dp ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ fa → proj₁ fa (proj₂ fa)
⟦_⟧ᶜ {ctx = ctx} (t-inl-app-check d) fmt ρ dγ = (⟦ d ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ v → returnᵖ (inj₁ v)
⟦_⟧ᶜ {ctx = ctx} (t-inr-app-check d) fmt ρ dγ = (⟦ d ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ v → returnᵖ (inj₂ v)
⟦_⟧ᶜ {ctx = ctx} (t-initial-app-check d) fmt ρ dγ = (⟦ d ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ v → ⊥-elim v
-- D243: a use of a polymorphic definition means the definition's family at
-- the use's kinded instance — the context projection Γ(x) at T. The body is
-- typed once, where it is declared; nothing is re-typed here.
⟦_⟧ᶜ {ctx = ctx} {A = T′} (t-var-poly-instantiate {x = x} _ _ lp _ ki) fmt ρ dγ =
  defAt (NamedCtx.polys ctx) x (defs ρ) lp T′ ki

⟦_⟧ᵢ {ctx = ctx} (t-int n) fmt ρ dγ = returnᵖ (OnceWord.Width.fromℤ (int-bits fmt) n)
-- D113, in the INFER realm: same clause, same reason as `g-float` above.
⟦_⟧ᵢ {ctx = ctx} (t-float i f l p) fmt ρ dγ = returnᵖ (round (float-format fmt) (decimalOf i f l))
-- plan 0.98: `semM` is `Res`-valued, so a literal's meaning LIFTS its result
-- rather than wrapping a value. `str-lit-info` is a `Pure` contract, so this
-- is `returnᵖ` in every reachable case — but the type no longer lets the
-- clause assume that, which is the point.
⟦_⟧ᵢ {ctx = ctx} (t-unit) fmt ρ dγ = returnᵖ tt
⟦_⟧ᵢ {ctx = ctx} (t-unit-var) fmt ρ dγ = returnᵖ tt
⟦_⟧ᵢ {ctx = ctx} (t-var-local {eV = eV} _) fmt ρ dγ = returnᵖ (svarᵛRun eV dγ)
-- Plan 0.105 (D257 amendment 2): a qualified or resolved reference names a
-- SigOp the program is compiled against — its meaning is that declaration's
-- implementation (`decl-*`: the world declares it).
⟦_⟧ᵢ {A = A} (t-var-qualified {name = name} {alias = alias} lk conc) fmt ρ dγ =
  sigOpRefᵛ {A = A} fmt (sig (world ρ)) (impl (world ρ)) (bare (alias ++ "." ++ name)) conc (decl-qual ρ {name = name} {alias = alias} lk)
-- D248: an own-module resolved reference names a module entry (a call of it).
⟦_⟧ᵢ {ctx = ctx} (t-var-resolved {cn = own x} _ lk _) fmt ρ dγ = impAt (NamedCtx.imports ctx) x (entries ρ) lk
⟦_⟧ᵢ {A = A} (t-var-resolved {cn = canonical L.[]} _ lk conc) fmt ρ dγ =
  sigOpRefᵛ {A = A} fmt (sig (world ρ)) (impl (world ρ)) (canonical L.[]) conc (decl-res ρ {cn = canonical L.[]} tt lk)
⟦_⟧ᵢ {A = A} (t-var-resolved {cn = canonical (a L.∷ b L.∷ rest)} _ lk conc) fmt ρ dγ =
  sigOpRefᵛ {A = A} fmt (sig (world ρ)) (impl (world ρ)) (canonical (a L.∷ b L.∷ rest)) conc (decl-res ρ {cn = canonical (a L.∷ b L.∷ rest)} tt lk)
-- D246: a reference to a module ENTRY is a call of it, and means the entry —
-- read from the scope's import environment (an FFI entry's is its contract).
⟦_⟧ᵢ {ctx = ctx} (t-var-import {x = x} _ _ lk _) fmt ρ dγ = impAt (NamedCtx.imports ctx) x (entries ρ) lk
-- Plan 0.58 / D071: an infer-mode ground telescope reference MEANS its body —
-- the context projection Γ(x). The body is closed (typed in the telescope
-- prefix over the empty local env), so its meaning runs on `tt`. Structural
-- recursion (bodyD is a premise ⇒ a subterm) — same as the check-mode rule.
⟦_⟧ᵢ {ctx = ctx} (t-var-poly-instantiate-infer {x = x} {schema = s} {g = g} _ _ lp _ eT) fmt ρ dγ =
  subst (λ X → ⟦ X ⟧ᵛ) (sym eT) (defAt (NamedCtx.polys ctx) x (defs ρ) lp (extractGround s g) (ground-kinded s g))
⟦_⟧ᵢ {ctx = ctx} (t-annot _ d) fmt ρ dγ = (⟦ d ⟧ᶜ fmt ρ) dγ
⟦_⟧ᵢ {ctx = ctx} (t-pair da db) fmt ρ dγ = (⟦ da ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ db ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → returnᵖ (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-neg d) fmt ρ dγ = (⟦ d ⟧ᵢ fmt ρ) dγ >>=ᵖ λ v → semP neg-info int-prim fmt v
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
⟦_⟧ᵢ {ctx = ctx} (t-neg-float i f l p) fmt ρ dγ = returnᵖ (round (float-format fmt) (negate (decimalOf i f l)))
-- D143: at `q = Zero` the bound value is ERASED — `e₁` is not evaluated and the
-- body runs on the unextended environment, matching `elaborate` and `⟦_⟧ˢ`.
⟦_⟧ᵢ {ctx = ctx} (t-let {A = A} {q = Zero} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) fmt ρ dγ =
  (⟦ d₂ ⟧ᵢ fmt ρ) (bindᵛ0 {Γ = NamedCtx.debruijn ctx} {A = A} (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ))
⟦_⟧ᵢ {ctx = ctx} (t-let {A = A} {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) fmt ρ dγ =
  (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) dγ) >>=ᵖ λ v →
  (⟦ d₂ ⟧ᵢ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} One (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) dγ) v)
⟦_⟧ᵢ {ctx = ctx} (t-let {A = A} {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) fmt ρ dγ =
  (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) dγ) >>=ᵖ λ v →
  (⟦ d₂ ⟧ᵢ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} Many (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) dγ) v)
⟦_⟧ᵢ {ctx = ctx} (t-case {A = A} {B = B} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr) fmt ρ dγ =
  (⟦ ds ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ) >>=ᵖ λ v →
  [ (λ a → (⟦ dl ⟧ᵢ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} qL (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) a))
  , (λ b → (⟦ dr ⟧ᵢ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = B} qR (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ)) b)) ]′ v
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith {op = OpAdd} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP add-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith {op = OpSub} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP sub-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith {op = OpMul} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP mul-info int-prim fmt (a , b)
-- PLAN 0.75 F4: the same three at `Float`, reading the same `semM` accessor —
-- so the float family is not a second story about what arithmetic means, it is
-- the same story with `Once.Float.Arith`'s operations behind it.
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float {op = OpAdd} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fadd-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float {op = OpSub} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fsub-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float {op = OpMul} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fmul-info int-prim fmt (a , b)
-- `/` joins them: the quotient is correctly rounded (the sticky bit lives in
-- `FA.fdiv`) and total, so it denotes like the other three.
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float {op = OpDiv} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fdiv-info int-prim fmt (a , b)
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
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) fmt ρ dγ = ((⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → semP i2f-info int-prim fmt a) >>=ᵖ λ a′ → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fadd-info int-prim fmt (a′ , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) fmt ρ dγ = ((⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → semP i2f-info int-prim fmt a) >>=ᵖ λ a′ → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fsub-info int-prim fmt (a′ , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) fmt ρ dγ = ((⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → semP i2f-info int-prim fmt a) >>=ᵖ λ a′ → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fmul-info int-prim fmt (a′ , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) fmt ρ dγ = ((⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → semP i2f-info int-prim fmt a) >>=ᵖ λ a′ → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP fdiv-info int-prim fmt (a′ , b)
⟦ t-binop-arith-float-il {op = OpMod} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpLt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpLe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpGt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpGe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpEq} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-il {op = OpNe} () _ _ ⟧ᵢ
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → ((⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP i2f-info int-prim fmt b) >>=ᵖ λ b′ → semP fadd-info int-prim fmt (a , b′)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → ((⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP i2f-info int-prim fmt b) >>=ᵖ λ b′ → semP fsub-info int-prim fmt (a , b′)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → ((⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP i2f-info int-prim fmt b) >>=ᵖ λ b′ → semP fmul-info int-prim fmt (a , b′)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → ((⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP i2f-info int-prim fmt b) >>=ᵖ λ b′ → semP fdiv-info int-prim fmt (a , b′)
⟦ t-binop-arith-float-ir {op = OpMod} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpLt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpLe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpGt} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpGe} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpEq} () _ _ ⟧ᵢ
⟦ t-binop-arith-float-ir {op = OpNe} () _ _ ⟧ᵢ
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith {op = OpDiv} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP div-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-arith {op = OpMod} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP mod-info int-prim fmt (a , b)
⟦_⟧ᵢ (t-binop-arith {op = OpLt} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpLe} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpGt} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpGe} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpEq} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpNe} () _ _) fmt
⟦_⟧ᵢ {ctx = ctx} (t-binop-cmp {op = OpLt} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP lt-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-cmp {op = OpLe} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP le-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-cmp {op = OpGt} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP gt-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-cmp {op = OpGe} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP ge-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-cmp {op = OpEq} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP eq-info int-prim fmt (a , b)
⟦_⟧ᵢ {ctx = ctx} (t-binop-cmp {op = OpNe} _ d₁ d₂) fmt ρ dγ = (⟦ d₁ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ a → (⟦ d₂ ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ b → semP ne-info int-prim fmt (a , b)
⟦_⟧ᵢ (t-binop-cmp {op = OpAdd} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpSub} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpMul} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpDiv} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpMod} () _ _) fmt
⟦_⟧ᵢ {ctx = ctx} (t-id-app d) fmt ρ dγ = (⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ)
⟦_⟧ᵢ {ctx = ctx} (t-fst-app d) fmt ρ dγ = (⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ v → returnᵖ (proj₁ v)
⟦_⟧ᵢ {ctx = ctx} (t-snd-app d) fmt ρ dγ = (⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ v → returnᵖ (proj₂ v)
⟦_⟧ᵢ {ctx = ctx} (t-Out-app-infer {F = F} wfF ceq d) fmt ρ dγ =
  subst (λ Z → ⟦ Z ⟧ᵛ) ceq
    ((⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx}
                    (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ)
       >>=ᵖ out-semᵛ Once.Type.pure wfF)
-- D233: forcing an EFFECTFUL stream at the surface — the stream is evaluated
-- now, the force runs when the suspension is applied (as `t-apply-eff-app-infer`).
⟦_⟧ᵢ {ctx = ctx} (t-Out-eff-app-infer {F = F} wfF ceq d) fmt ρ dγ =
  (⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx}
                  (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ v →
  returnᵖ (λ _ → subst (λ Z → T ⟦ Z ⟧ᵛ) ceq (out-semᵛ Once.Type.eff wfF v))
⟦_⟧ᵢ {ctx = ctx} (t-terminal-app d) fmt ρ dγ = (⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ _ → returnᵖ tt
⟦_⟧ᵢ {ctx = ctx} (t-apply-app-infer d) fmt ρ dγ = (⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ fa → proj₁ fa (proj₂ fa)
-- D222 / plan 0.95 A′: the EFF closure's elimination is a SUSPENSION — but only
-- the APPLICATION is suspended, not the evaluation of the pair.
--
-- The scope matters and the bridge is what pins it. `realize` emits
-- `morph-app (curry (apply ∘ fst)) (realize-infer d)`, and `morph-app`
-- evaluates its ARGUMENT and then applies the morphism — so the pair is built
-- eagerly and the `curry` suspends only `apply`. Writing the meaning as
-- `returnᵖ (λ _ → ⟦ d ⟧ᵢ … >>=ᵖ …)` would suspend the pair's own evaluation
-- too, and the two would disagree about WHEN the pair's events appear.
--
-- It is also the right reading on its own terms: constructing `(f , a)` is not
-- the effect; running `f a` is. Contrast `t-effApp`, whose meaning suspends
-- everything — there `elaborate` puts the head's and argument's evaluation
-- INSIDE the `curry` too (Surface/Elaborate.agda:393-395), so the two agree.
⟦_⟧ᵢ {ctx = ctx} (t-apply-eff-app-infer d) fmt ρ dγ = (⟦ d ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ) >>=ᵖ λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa))
-- D143: at an ERASED arrow the argument is NOT evaluated — the meaning takes
-- none, so `vf` is applied to `tt`. The spec's counterpart of the elaborator
-- not emitting `x`, and the reason `Ψ₂` vanishes from the index.
⟦_⟧ᵢ {ctx = ctx} (t-app {q = Zero} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ df dx) fmt ρ dγ =
  (⟦ df ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ) >>=ᵖ λ vf → vf tt
⟦_⟧ᵢ {ctx = ctx} (t-app {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ df dx) fmt ρ dγ =
  (⟦ df ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) dγ) >>=ᵖ λ vf →
  (⟦ dx ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) dγ) >>=ᵖ λ vx → vf vx
⟦_⟧ᵢ {ctx = ctx} (t-app {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ df dx) fmt ρ dγ =
  (⟦ df ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) dγ) >>=ᵖ λ vf →
  (⟦ dx ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) dγ) >>=ᵖ λ vx → vf vx
⟦_⟧ᵢ {ctx = ctx} (t-effApp _ df dx) fmt ρ dγ = returnᵖ (λ _ → (⟦ df ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ (Many *ᵘ _)) dγ) >>=ᵖ λ vf → (⟦ dx ⟧ᶜ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ _ (Many *ᵘ _))) dγ) >>=ᵖ λ vx → vf vx)
-- D230: the spine — the head, given the argument's type, applied to it.
⟦_⟧ᵢ {ctx = ctx} (t-app-spine _ darg df) fmt ρ dγ = (⟦ df ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ vf → (⟦ darg ⟧ᵢ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ _ _)) dγ) >>=ᵖ λ vx → vf vx

-- Plan 0.94 §10: the domain-given realm. `d-infer` is the inferred term under
-- its arrow conversion; `d-lam` is `t-lam` at `Many`; `d-compose` is `compose`.
⟦_⟧ᵈ {ctx = ctx} (d-infer {B = B} w a g) fmt ρ dγ = fmapᵖ ⟦ sub-arr {q = Many} a (<:-refl B) g ⟧<:ᵛ ((⟦ w ⟧ᵢ fmt ρ) dγ)
-- D243: a polymorphic head means the definition's family at the arrow
-- instance, converted to the given grade.
⟦_⟧ᵈ {ctx = ctx} (d-poly {x = x} {A = A} {B = B} {π′ = π′} _ _ lp _ _ _ ki g) fmt ρ dγ =
  fmapᵖ ⟦ sub-arr {q = Many} (<:-refl A) (<:-refl B) g ⟧<:ᵛ (defAt (NamedCtx.polys ctx) x (defs ρ) lp _ ki)
⟦_⟧ᵈ {ctx = ctx} (d-lam {A = A} {q' = Zero} {π = π} _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᵢ fmt ρ) (bindᵛ0 {Γ = NamedCtx.debruijn ctx} {A = A} dγ))
⟦_⟧ᵈ {ctx = ctx} (d-lam {A = A} {q' = One} {π = π}  _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᵢ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} One  dγ a))
⟦_⟧ᵈ {ctx = ctx} (d-lam {A = A} {q' = Many} {π = π} _ d) fmt ρ dγ = λ a → returnM π ((⟦ d ⟧ᵢ fmt ρ) (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} Many dγ a))
⟦_⟧ᵈ {ctx = ctx} (d-compose {π = π} dg df) fmt ρ dγ =
  (⟦ df ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ (Many *ᵘ _)) dγ) >>=ᵖ λ vf → (⟦ dg ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ _ (Many *ᵘ _))) dγ) >>=ᵖ λ vg →
  λ a → bindM π (vg a) vf
⟦_⟧ᵈ {ctx = ctx} (d-id {π = π}) fmt ρ dγ = λ a  → returnM π a
⟦_⟧ᵈ {ctx = ctx} (d-fst {π = π}) fmt ρ dγ = λ ab → returnM π (proj₁ ab)
⟦_⟧ᵈ {ctx = ctx} (d-snd {π = π}) fmt ρ dγ = λ ab → returnM π (proj₂ ab)
⟦_⟧ᵈ {ctx = ctx} (d-terminal {π = π}) fmt ρ dγ = λ _  → returnM π tt
⟦_⟧ᵈ {ctx = ctx} d-initial  fmt ρ dγ = λ v  → ⊥-elim v
⟦_⟧ᵈ {ctx = ctx} (d-case df dg) fmt ρ dγ =
  (⟦ df ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ vf → (⟦ dg ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ vg →
  returnᵖ (λ ab → [ vf , vg ]′ ab)
⟦_⟧ᵈ {ctx = ctx} (d-pair {π = π} df dg) fmt ρ dγ =
  (⟦ df ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ _ _) dγ) >>=ᵖ λ vf → (⟦ dg ⟧ᵈ fmt ρ) (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ʳ _ _) dγ) >>=ᵖ λ vg →
  λ a → bindM π (vf a) λ b → bindM π (vg a) λ c → returnM π (b , c)
⟦_⟧ᵈ {ctx = ctx} (d-cata {π = π} wfF dalg) fmt ρ dγ =
  (⟦ dalg ⟧ᵢ fmt ρ) dγ >>=ᵖ λ valg → λ v → cata-semᵛ π wfF valg v
