-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ResolveFaithful — Plan 0.51 / 3b: discharge of
-- `MainRealizeAgrees.resolveExpr-faithful` (the resolver preserves SD denotation).
--
-- Induction on the elaborated `Expr`. The ~30 STRUCTURAL constructors need only
-- the IHs: `resolveExpr-C` is `refl` (resolution commutes structurally, same
-- `Acc`), so `resolveExpr (C …)` reduces DEFINITIONALLY to `C (resolveExpr …)`;
-- and `>>=T` at fuel `k` consumes only the sub-trace `m k`, so the pointwise-`k`
-- IH `rewrite`s cleanly. Binders (`lam`/`case'`) close over the bound var → use
-- `Once.Postulates.extensionality` (funext).
--
-- Plan 0.55 D#3 (DONE): the broad `resolveExpr-faithful-hard` catch-all is GONE.
-- morph-app/cata/ana are structural (IH + closure `cong`); the only genuinely-hard
-- constructors are `sigOp` (name→closure rewrite) and `poly` (body splice), each now
-- an explicit clause with its `nothing`/`failure` sub-branch PROVEN (`refl`) and the
-- open denotational fact isolated to a NARROW named postulate
-- (`resolveExpr-sigOp-closure-faithful`; plan 0.103 1c deleted the inconsistent poly-splice one).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Once.Denotation.Phase using (restrictᴰ; bindᴰ; bindᴰ0)

-- Plan 0.73 (D113): this module's statements mention the source denotation,
-- which is target-relative at `Float`, so the format is a parameter here. It
-- is a MODULE parameter rather than a per-lemma argument because everything
-- below is a PROOF — downstream uses these as facts, never reduces them — so
-- the "recursive function in a parameterised module stops reducing" trap does
-- not apply. The denotations themselves take it as an explicit argument.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.ResolveFaithful (fmt : TargetNum) (ρ : CallEnv) where

open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Res using (mapRes)

open import Data.Nat using (ℕ; _<_; _∸_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List; []; length)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Once.Type using (Type; Int; Float; Unit; _+_; Quantity; Zero; One; Many)
import Once.Type as T
open import Once.Functor.Translate using (IsConcrete; con-fun; con-base)
open import Once.Surface.Syntax as Srf using (Expr; Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; cohᴰ; anaFᵈ; coerce-functor-D)
open import Once.Arith.SigOp.Builders
open import Once.Denotation.TraceMonad using (T; _>>=T_; returnT; fmapT; >>=T-identityʳ)
open import Once.Res using (Res; stopped; returns)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Semantics.Machine using (sem-cata; sem-ana; coerce-functor)
import Once.Denotation.SourceDenote as SD
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; PolyCtx; Imports;
  resolvePolyCase; applySplice; checkElab; checkElabV; CheckElabResult; VerifiedCheckResult)
open import Once.TypeCheck.Classify using (lookupPolyPrefix; lookupImport; ctxWithImportsAndPolys)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- Plan 0.103 phase 1c: LINKING IS SUBSTITUTION.
--
-- A surface term is open over the definitions context: `poly x A` is a
-- definition reference, meant in a definitions environment (`SD.DefsSem`).
-- `resolveExpr` substitutes each reference by the definition's closed, linked
-- body; the compiled program's environment is `σ₀` (a reference linking left
-- in place is an internal call). The theorem below is the SUBSTITUTION LEMMA:
-- the linked term in `σ₀` means the unlinked term in the environment `σR` of
-- the linked references' meanings. There is no statement relating a
-- reference's own meaning to a body — the former `resolveExpr-poly-splice-
-- faithful` did exactly that, for an ARBITRARY body, and derived ⊥.
------------------------------------------------------------------------

σ₀ : SD.DefsSem
σ₀ = SD.internalDefs fmt ρ

-- The meaning of a linked reference: what `resolveExpr` puts at `poly x A`.
σR : PolyCtx → (String → Imports) → Imports → ℕ → SD.DefsSem
-- D245: the CALLS are the program's (`ρ`); only the surface references read
-- the linked meaning.
σR polys imps userFns fresh = SD.defsSem ρ (λ x A →
  SD.⟦ resolveExpr {Γ = Srf.∅} {Ψ = Srf.zeroUsage} polys imps userFns fresh (Srf.poly x A) ⟧ˢ fmt σ₀ tt)

-- A SigOp reference reads only the CALL environment (plan 0.105: an FFI value
-- is its pure half), never the references — so two definitions environments
-- with the same calls mean it alike. The surface meaning dispatches on the
-- type's shape, so the fact is stated per shape.
sigOp-σ-irrel : ∀ {n} {Γ : Srf.Ctx n} {A : Type} (c : CallEnv) (r r′ : String → (U : Type) → T ⟦ U ⟧ᴰ)
  (s : CanonicalName) (conc : IsConcrete A) (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ)
  → SD.⟦ Srf.sigOp {Γ = Γ} {A = A} s conc ⟧ˢ fmt (SD.defsSem c r) dγ ≡ SD.⟦ Srf.sigOp {Γ = Γ} {A = A} s conc ⟧ˢ fmt (SD.defsSem c r′) dγ
sigOp-σ-irrel {A = _ T.⇒[ T.mk-kind Zero _ ] _} c r r′ s (con-fun _ _) dγ = refl
sigOp-σ-irrel {A = _ T.⇒[ T.mk-kind One _ ] _}  c r r′ s (con-fun _ _) dγ = refl
sigOp-σ-irrel {A = _ T.⇒[ T.mk-kind Many _ ] _} c r r′ s (con-fun _ _) dγ = refl
sigOp-σ-irrel {A = _ T.⇒[ _ ] _} c r r′ s (con-base ()) dγ
sigOp-σ-irrel {A = T.Unit}       c r r′ s (con-base _) dγ = refl
sigOp-σ-irrel {A = T.Void}       c r r′ s (con-base _) dγ = refl
sigOp-σ-irrel {A = T.Int}        c r r′ s (con-base _) dγ = refl
sigOp-σ-irrel {A = T.Float}      c r r′ s (con-base _) dγ = refl
sigOp-σ-irrel {A = T.rigid _ _}  c r r′ s (con-base _) dγ = refl
sigOp-σ-irrel {A = _ T.* _}      c r r′ s (con-base _) dγ = refl
sigOp-σ-irrel {A = _ T.+ _}      c r r′ s (con-base _) dγ = refl
sigOp-σ-irrel {A = T.μ-type _}   c r r′ s (con-base ()) dγ
sigOp-σ-irrel {A = T.ν-type _ _} c r r′ s (con-base ()) dγ

-- A linked reference is CLOSED: `poly x A` either stays (an internal call,
-- environment-free) or becomes `closed r` — so its meaning does not depend on
-- the context it sits in. Explicit-argument forms, so both sides reduce on
-- the same lookup / elaboration answers.
splice-ctx-indep :
  ∀ {n} {Γ : Srf.Ctx n} {A : Type}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys)) (imps : String → Imports) (userFns : Imports)
    (fresh : ℕ) (x : String) {schema body prefix}
    (polyEq : lookupPolyPrefix polys x ≡ just (schema , body , prefix))
    (r : VerifiedCheckResult (ctxWithImportsAndPolys (imps x) prefix) body A) (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ)
  → SD.⟦ applySplice {Γ = Γ} polys pAcc imps userFns fresh x A polyEq r ⟧ˢ fmt σ₀ dγ
      ≡ SD.⟦ applySplice {Γ = Srf.∅} polys pAcc imps userFns fresh x A polyEq r ⟧ˢ fmt σ₀ tt
splice-ctx-indep polys pAcc imps userFns fresh x polyEq (CheckElabResult.failure _ , _) dγ = refl
splice-ctx-indep polys (acc rec) imps userFns fresh x polyEq (CheckElabResult.success Srf.[] eE _ _ , _) dγ = refl

poly-ctx-indep :
  ∀ {n} {Γ : Srf.Ctx n} {A : Type}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys)) (imps : String → Imports) (userFns : Imports)
    (fresh : ℕ) (x : String) (lp : Maybe _) (eqLP : lookupPolyPrefix polys x ≡ lp)
    (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ)
  → SD.⟦ resolvePolyCase {Γ = Γ} polys pAcc imps userFns fresh x A lp eqLP ⟧ˢ fmt σ₀ dγ
      ≡ SD.⟦ resolvePolyCase {Γ = Srf.∅} polys pAcc imps userFns fresh x A lp eqLP ⟧ˢ fmt σ₀ tt
poly-ctx-indep polys pAcc imps userFns fresh x nothing eqLP dγ = refl
poly-ctx-indep {A = A} polys pAcc imps userFns fresh x (just (_ , body , prefix)) eqLP dγ =
  splice-ctx-indep polys pAcc imps userFns fresh x eqLP
    (checkElabV (ctxWithImportsAndPolys (imps x) prefix) body A) dγ

-- Two-sided bind congruence: related heads and pointwise-equal continuations
-- give equal computations (plan 0.105: equality of trees, no budget).
bind2-faithful : ∀ {X Y} (mR mU : T X) (gR gU : X → T Y)
  → mR ≡ mU → (∀ v → gR v ≡ gU v)
  → (mR >>=T gR) ≡ (mU >>=T gU)
bind2-faithful mR mU gR gU me ge = cong₂ _>>=T_ me (extensionality ge)

-- | The BINARY-OPERAND shape, shared by every two-operand constructor: `comp'`,
--   `pair`, `copair'`, `fork'` and the fifteen arithmetic ops. Operand `a` runs
--   on the `+ˡ` narrowing of the erased environment, `b` on the `+ʳ`, and the
--   continuation `g` combines them — the resolver never touches `g`, so the two
--   sides differ only in the operands.
--
--   Stating this ONCE is what makes the bind congruence usable. `(m >>=T f) k`
--   REDUCES, so a congruence whose `m` or `f` is left to inference poses an
--   unsolvable higher-order constraint (`_f (_m k) k ≐ proj₂ …`) that Agda
--   silently defers rather than rejects. Here every monadic argument is fixed by
--   an explicit parameter, so nothing is inferred.
binop-le-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ₁ Ψ₂ Ψ' : Usage n} {A B C : Type}
    (polys : PolyCtx) (imps : String → Imports) (userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
    (le₁ : Ψ₁ Srf.⊑ᵘ Ψ') (le₂ : Ψ₂ Srf.⊑ᵘ Ψ')
    (g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ Ψ' ⟧ᶜ ⟧ᴰ)
    (ihA : SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le₁ dγ)
                   ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₁ dγ))
    (ihB : SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le₂ dγ)
                   ≡ SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₂ dγ))
   
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
      SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb))
      ≡ ((SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
          SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb))
binop-le-faithful {Γ = Γ} polys imps userFns fresh a b le₁ le₂ g dγ ihA ihB =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ Ea) (SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) Ea)
    (λ va → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ Eb >>=T λ vb → g va vb)
    (λ va → SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) Eb >>=T λ vb → g va vb)
    ihA
    (λ va → bind2-faithful
                (SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ Eb) (SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) Eb)
                (λ vb → g va vb) (λ vb → g va vb)
                ihB
                (λ vb → refl))
  where
    Ea = restrictᴰ {Γ = Γ} le₁ dγ
    Eb = restrictᴰ {Γ = Γ} le₂ dγ

-- | The common case of `binop-le-faithful`: both operands narrow out of the
--   SUM usage `Ψ₁ +ᵘ Ψ₂` — every arithmetic op, `pair`, and the four D127
--   combinators.
binop-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type}
    (polys : PolyCtx) (imps : String → Imports) (userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
    (g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ (Ψ₁ Srf.+ᵘ Ψ₂) ⟧ᶜ ⟧ᴰ)
    (ihA : SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ)
                   ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (ihB : SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)
                   ≡ SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
   
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
      SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb))
      ≡ ((SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
          SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb))
binop-faithful {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {C = C} polys imps userFns fresh a b g dγ ihA ihB =
  binop-le-faithful {C = C} polys imps userFns fresh a b
    (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) g dγ ihA ihB

-- | The SUSPENDED binary shape (`effApp`, D018): the application sits inside a
--   `returnT (λ _ → …)` thunk, so the equation is between THUNKS and has to pass
--   through funext. `extensionality`'s implicit function arguments cannot be
--   recovered from a `(m >>=T f) j` proof — `(m >>=T f) j` REDUCES, so the match
--   is higher-order — hence `inner` carries an explicit signature that pins them.
thunk-binop-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ₁ Ψ₂ Ψ' : Usage n} {A B C : Type}
    (polys : PolyCtx) (imps : String → Imports) (userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
    (le₁ : Ψ₁ Srf.⊑ᵘ Ψ') (le₂ : Ψ₂ Srf.⊑ᵘ Ψ')
    (g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ Ψ' ⟧ᶜ ⟧ᴰ)
    (ihA : SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} le₁ dγ)
                   ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₁ dγ))
    (ihB : SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} le₂ dγ)
                   ≡ SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₂ dγ))
   
  → returnT (λ (_ : Data.Unit.⊤) →
       SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
         (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
       SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
         (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb)
      ≡ returnT (λ (_ : Data.Unit.⊤) →
       SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh)
         (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
       SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh)
         (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb)
thunk-binop-faithful {Γ = Γ} {C = C} polys imps userFns fresh a b le₁ le₂ g dγ ihA ihB =
  cong returnT (extensionality (λ _ → inner))
  where
    Ea = restrictᴰ {Γ = Γ} le₁ dγ
    Eb = restrictᴰ {Γ = Γ} le₂ dγ
    inner : (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ Ea >>=T λ va →
             SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ Eb >>=T λ vb → g va vb)
              ≡ (SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) Ea >>=T λ va →
                 SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) Eb >>=T λ vb → g va vb)
    inner = binop-le-faithful {C = C} polys imps userFns fresh a b le₁ le₂ g dγ ihA ihB

-- | The UNARY-OPERAND shape: one sub-expression under an arbitrary narrowing
--   `le`, then a continuation the resolver leaves alone (`morph-app`, `fst'`,
--   `snd'`, `inl'`, `inr'`, and `app` at an erased argument). Same discipline as
--   `binop-faithful`: the monadic argument and the continuation are PARAMETERS.
unop-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ Ψ' : Usage n} {A C : Type}
    (polys : PolyCtx) (imps : String → Imports) (userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ A) (le : Ψ Srf.⊑ᵘ Ψ') (g : ⟦ A ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ Ψ' ⟧ᶜ ⟧ᴰ)
    (ih : SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le dγ)
                  ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le dγ))
   
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} le dγ) >>=T g))
      ≡ ((SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le dγ) >>=T g))
unop-faithful {Γ = Γ} polys imps userFns fresh a le g dγ ih =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le dγ))
    (SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le dγ))
    g g
    ih (λ v → refl)

------------------------------------------------------------------------
-- The faithfulness theorem.
------------------------------------------------------------------------

resolveExpr-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ : Usage n} {A : Type}
    (polys : PolyCtx) (imps : String → Imports) (userFns : Imports) (fresh : ℕ)
    (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ Srf.↾ Ψ ⟧ᶜ ⟧ᴰ)
  → SD.⟦ resolveExpr polys imps userFns fresh e ⟧ˢ fmt σ₀ dγ
      ≡ SD.⟦ e ⟧ˢ fmt (σR polys imps userFns fresh) dγ
-- Leaves (resolveExpr unchanged ⇒ definitionally equal).
resolveExpr-faithful polys imps userFns fresh (Srf.var i) dγ = refl
resolveExpr-faithful polys imps userFns fresh Srf.unit dγ = refl
-- D226: a conversion maps the result and leaves the trace; resolution commutes.
resolveExpr-faithful polys imps userFns fresh (Srf.coerce p e) dγ =
  cong (fmapT ⟦ p ⟧<:) (resolveExpr-faithful polys imps userFns fresh e dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.int z) dγ = refl
-- A float literal has no names in it, so resolution is the identity and the
-- denotation is unchanged — `refl`, exactly as for `int`.
resolveExpr-faithful polys imps userFns fresh (Srf.float d) dγ = refl
resolveExpr-faithful polys imps userFns fresh (Srf.closure s) dγ = refl
resolveExpr-faithful polys imps userFns fresh (Srf.lift-morphism m) dγ = refl
-- Unary / binary (structural ⇒ the IH, under the shared continuation).
-- Plan 0.105: equations of trees — a bind congruence over the IH.
resolveExpr-faithful polys imps userFns fresh (Srf.fst' p) dγ =
  cong (_>>=T (λ v → returnT (proj₁ v)))
    (resolveExpr-faithful polys imps userFns fresh p dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.snd' p) dγ =
  cong (_>>=T (λ v → returnT (proj₂ v)))
    (resolveExpr-faithful polys imps userFns fresh p dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.inl' e) dγ =
  cong (_>>=T (λ v → returnT (inj₁ v)))
    (resolveExpr-faithful polys imps userFns fresh e dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.inr' e) dγ =
  cong (_>>=T (λ v → returnT (inj₂ v)))
    (resolveExpr-faithful polys imps userFns fresh e dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.neg e) dγ =
  cong (_>>=T (λ v → SD.sigOpˢ fmt σ₀ neg-info v))
    (resolveExpr-faithful polys imps userFns fresh e dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.absurd e) dγ =
  cong (_>>=T (λ v → ⊥-elim v))
    (resolveExpr-faithful polys imps userFns fresh e dγ)
-- `morph-app`'s wrapper is a dependent `subst` chain, so `rewrite` (which IS
-- `with`-abstraction) cannot generalise the inner occurrence. `unop-faithful`
-- takes the monadic argument and the continuation as PARAMETERS instead, and
-- the IH is taken directly at the narrowed environment the goal carries.
resolveExpr-faithful polys imps userFns fresh
    (Srf.morph-app {Γ = Γ} {Ψ = Ψₑ} {A = A} {B = B} ir a) dγ =
  unop-faithful {C = B} polys imps userFns fresh a
    (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψₑ) (Srf.⊑ᵘ-+ʳ Srf.zeroUsage (Many Srf.*ᵘ Ψₑ)))
    (λ v → subst T (cohᴰ B) (evalᴰ fmt ρ ir (subst (λ z → z) (sym (cohᴰ A)) v)))
    dγ (resolveExpr-faithful polys imps userFns fresh a
          (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψₑ)
                        (Srf.⊑ᵘ-+ʳ Srf.zeroUsage (Many Srf.*ᵘ Ψₑ))) dγ))
-- `app` splits on the arrow's quantity because its DENOTATION does: at `Zero`
-- the argument is erased and never evaluated, so only the function's IH is
-- needed. Each IH is transported to the environment the goal carries.
-- `app` splits on the arrow's quantity because its DENOTATION does: at `Zero`
-- the argument is ERASED and never evaluated, so only the function's IH exists
-- to use. No `rewrite` anywhere here — the continuation sits under a dependent
-- chain, so the equations are passed as PARAMETERS to the bind congruences.
resolveExpr-faithful polys imps userFns fresh
    (Srf.app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = Zero} f a) dγ =
  unop-faithful {C = B} polys imps userFns fresh f
    (Srf.⊑ᵘ-+ˡ Ψ₁ (Zero Srf.*ᵘ Ψ₂)) (λ vf → vf tt)
    dγ (resolveExpr-faithful polys imps userFns fresh f
          (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Zero Srf.*ᵘ Ψ₂)) dγ))
resolveExpr-faithful polys imps userFns fresh
    (Srf.app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = One} f a) dγ =
  binop-le-faithful {C = B} polys imps userFns fresh f a
    (Srf.⊑ᵘ-+ˡ Ψ₁ (One Srf.*ᵘ Ψ₂))
    (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*One Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (One Srf.*ᵘ Ψ₂)))
    (λ vf vx → vf vx) dγ
    (resolveExpr-faithful polys imps userFns fresh f
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (One Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh a
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*One Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (One Srf.*ᵘ Ψ₂))) dγ))
resolveExpr-faithful polys imps userFns fresh
    (Srf.app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = Many} f a) dγ =
  binop-le-faithful {C = B} polys imps userFns fresh f a
    (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂))
    (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂)))
    (λ vf vx → vf vx) dγ
    (resolveExpr-faithful polys imps userFns fresh f
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh a
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) dγ))
-- D127: the combinators resolve componentwise; both arms' IHs rewrite and the
-- meaning is a function of the two results, so `refl` closes each.
resolveExpr-faithful polys imps userFns fresh (Srf.comp' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {C = C} {π = π} a b) dγ =
  binop-le-faithful {C = A T.⇒[ T.mk-kind Many π ] C} polys imps userFns fresh a b (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) (λ va vb → returnT (λ a → vb a >>=T va)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.copair' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} a b) dγ =
  binop-faithful {C = (A T.+ B) T.⇒[ T.mk-kind Many π ] C} polys imps userFns fresh a b (λ va vb → returnT (λ ab → [ va , vb ]′ ab)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.fork' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} a b) dγ =
  binop-faithful {C = A T.⇒[ T.mk-kind Many T.pure ] (B T.* C)} polys imps userFns fresh a b (λ va vb → returnT (λ a → va a >>=T λ x → vb a >>=T λ y → returnT (x , y))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.curry' f) dγ =
  cong (_>>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b)))))
    (resolveExpr-faithful polys imps userFns fresh f dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} a b) dγ =
  binop-faithful {C = A T.* B} polys imps userFns fresh a b (λ va vb → returnT (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.add {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ add-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.sub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ sub-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.mul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ mul-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
resolveExpr-faithful polys imps userFns fresh (Srf.fadd {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ fadd-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.fsub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ fsub-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.fmul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ fmul-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.fdiv {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ fdiv-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.i2f a) dγ =
  cong (_>>=T (λ va → SD.sigOpˢ fmt σ₀ i2f-info va))
    (resolveExpr-faithful polys imps userFns fresh a dγ)
resolveExpr-faithful polys imps userFns fresh (Srf.div {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ div-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.mod' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ mod-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.lt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ lt-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.le {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ le-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.gt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ gt-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.ge {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ ge-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.eq {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ eq-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
resolveExpr-faithful polys imps userFns fresh (Srf.ne {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → SD.sigOpˢ fmt σ₀ ne-info (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ))
-- Binders. `lam` splits on the arrow's quantity AND the binder's body usage,
-- matching its denotation. Over the ERASED environment the body's environment
-- is literally the `bindᴰ`/`bindᴰ0` the goal carries, so every IH lands with no
-- transport — and at `q' = Zero` no witness of `A` is required at all.
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} Zero prf b) dγ =
  cong returnT (extensionality (λ _ → (
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ))))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} One prf b) dγ =
  cong returnT (extensionality (λ a → (
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ))))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} Many prf b) dγ =
  cong returnT (extensionality (λ a → (
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ))))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = One} {A = A} One prf b) dγ =
  cong returnT (extensionality (λ a → (
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} One dγ a))))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = One} {A = A} Many prf b) dγ =
  cong returnT (extensionality (λ a → (
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} One dγ a))))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Many} {A = A} Many prf b) dγ =
  cong returnT (extensionality (λ a → (
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} Many dγ a))))
-- `let'` splits on the bound variable's usage. At `Zero` the bound value is
-- ERASED — `e₁` is never evaluated, so only the body's IH exists to use, and it
-- lands on the unextended environment.
-- D143: at an ERASED binder the body runs on the UNEXTENDED environment
-- (`bindᴰ0`), so `e₁` is never evaluated and no witness of `A` is needed —
-- which is precisely why the theorem must be stated over the ERASED
-- environment: over the full one this clause would demand an inhabitant of a
-- type that erasure exists to discard.
resolveExpr-faithful polys imps userFns fresh
    (Srf.let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} e₁ e₂) dγ =
  resolveExpr-faithful polys imps userFns fresh e₂
    (bindᴰ0 {Γ = Γ} {A = A} (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₂ (Zero Srf.*ᵘ Ψ₁)) dγ))
resolveExpr-faithful polys imps userFns fresh
    (Srf.let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} e₁ e₂) dγ =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh e₁ ⟧ˢ fmt σ₀ E₁) (SD.⟦ e₁ ⟧ˢ fmt (σR polys imps userFns fresh) E₁)
    (λ v → SD.⟦ resolveExpr polys imps userFns fresh e₂ ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    (λ v → SD.⟦ e₂ ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    (resolveExpr-faithful polys imps userFns fresh e₁ E₁)
    (λ v → resolveExpr-faithful polys imps userFns fresh e₂ (bindᴰ {Γ = Γ} {A = A} One E₂ v))
  where
    E₁ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*One Ψ₁) (Srf.⊑ᵘ-+ʳ Ψ₂ (One Srf.*ᵘ Ψ₁))) dγ
    E₂ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₂ (One Srf.*ᵘ Ψ₁)) dγ
resolveExpr-faithful polys imps userFns fresh
    (Srf.let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} e₁ e₂) dγ =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh e₁ ⟧ˢ fmt σ₀ E₁) (SD.⟦ e₁ ⟧ˢ fmt (σR polys imps userFns fresh) E₁)
    (λ v → SD.⟦ resolveExpr polys imps userFns fresh e₂ ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
    (λ v → SD.⟦ e₂ ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
    (resolveExpr-faithful polys imps userFns fresh e₁ E₁)
    (λ v → resolveExpr-faithful polys imps userFns fresh e₂ (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
  where
    E₁ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₁) (Srf.⊑ᵘ-+ʳ Ψ₂ (Many Srf.*ᵘ Ψ₁))) dγ
    E₂ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₂ (Many Srf.*ᵘ Ψ₁)) dγ
-- `case'`: the scrutinee narrows, then each branch runs on the JOIN narrowed to
-- its own usage and extended by its binder. Parameters throughout — the branch
-- bodies sit under `[_,_]′`, which `with` cannot see into.
-- `case'`: the scrutinee narrows, then each branch runs on the JOIN narrowed to
-- its own side and extended by its binder. Parameters throughout — the branch
-- bodies sit under `[_,_]′`, which `with` cannot abstract over. The branch IHs
-- `case'`: the scrutinee narrows, then each branch runs on the JOIN narrowed to
-- its own side and extended by its binder. Over the ERASED environment every one
-- of those is exactly the environment the goal already carries, so each IH lands
-- directly — no transport. Parameters throughout: the branch bodies sit under
-- `[_,_]′`, which `with` cannot abstract over.
resolveExpr-faithful polys imps userFns fresh
    (Srf.case' {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr}
               {A = A} {B = B} s l r) dγ =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh s ⟧ˢ fmt σ₀ Es) (SD.⟦ s ⟧ˢ fmt (σR polys imps userFns fresh) Es)
    (λ v → [ (λ a → SD.⟦ resolveExpr polys imps userFns fresh l ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
           , (λ b → SD.⟦ resolveExpr polys imps userFns fresh r ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v)
    (λ v → [ (λ a → SD.⟦ l ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
           , (λ b → SD.⟦ r ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v)
    (resolveExpr-faithful polys imps userFns fresh s Es)
    (λ { (inj₁ a) → resolveExpr-faithful polys imps userFns fresh l (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a)
       ; (inj₂ b) → resolveExpr-faithful polys imps userFns fresh r (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b) })
  where
    Eall = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψs (Ψₗ Srf.⊔ᵘ Ψᵣ)) dγ
    Es = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψs (Ψₗ Srf.⊔ᵘ Ψᵣ)) dγ
    Eₗ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) Eall
    Eᵣ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) Eall

resolveExpr-faithful polys imps userFns fresh
    (Srf.effApp {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} f x) dγ =
  thunk-binop-faithful {C = B} polys imps userFns fresh f x (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) (λ vf vx → vf vx) dγ
    (resolveExpr-faithful polys imps userFns fresh f (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh x (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) dγ))
-- cata: D131 — the algebra is BOUND, so both sides are `⟦alg⟧ˢ dγ >>=T` the
-- same continuation and the whole clause is ONE `cong` over the algebra
-- denotation (the IH at the same environment — plan 0.101, the algebra lives
-- in the context).
resolveExpr-faithful polys imps userFns fresh (Srf.cata {F = F} {A = A} wf alg) dγ =
  cong (λ ac → (ac >>=T λ valg →
                  returnT (λ x → sem-cata wf (SD.cata-ev-algˢ {F} {A} wf (returnT valg)) x)))
       (( resolveExpr-faithful polys imps userFns fresh alg dγ))
-- ana: dual of cata (D273) — the coalgebra is BOUND once at the same
-- environment, so the clause is ONE `cong` over the coalgebra denotation.
resolveExpr-faithful polys imps userFns fresh (Srf.ana {F = F} {A = A} wf coalg) dγ =
  cong (λ ac → (ac >>=T λ clo →
                  returnT (λ a → returnT (anaFᵈ F
                    (λ a' → fmapT (coerce-functor-D wf A) (clo a')) a))))
       (( resolveExpr-faithful polys imps userFns fresh coalg dγ))
-- sigOp: D246 — the resolver passes it through, and a SigOp reads no environment.
resolveExpr-faithful {Γ = Γ} {A = A} polys imps userFns fresh (Srf.sigOp s conc) dγ =
  sigOp-σ-irrel {Γ = Γ} {A = A} ρ _ _ s conc dγ
-- poly: the substitution lemma's variable case — the linked reference means
-- `σR x A` by definition, up to its context-independence.
resolveExpr-faithful {Γ = Γ} {A = A} polys imps userFns fresh (Srf.poly x T) dγ =
  (poly-ctx-indep {Γ = Γ} {A = A} polys (<-wellFounded (length polys)) imps userFns fresh x
                   (lookupPolyPrefix polys x) refl dγ)
-- closed: a closed term runs on the empty environment on both sides.
resolveExpr-faithful polys imps userFns fresh (Srf.closed e) dγ =
  resolveExpr-faithful polys imps userFns fresh e tt