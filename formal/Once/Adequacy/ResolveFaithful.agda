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
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; inject; forget; evalᴰ; cohᴰ; anaFᵈ; coerce-functor-D)
open import Once.SigOp.Info using (semM)
open import Once.Arith.SigOp.Builders
open import Once.Denotation.TraceMonad using (T; mkT; atT; Stopped; stoppedT; projTrace;
                                              _>>=T_; returnT; resT-lift; fmapT;
                                              >>=T-cong-at; >>=T-cong₂-at;
                                              bindRes-idʳ; >>=T-identityʳ)
open import Once.Res using (Res; stopped; returns)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Semantics.Machine using (sem-cata; sem-ana; coerce-functor)
import Once.Denotation.SourceDenote as SD
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; PolyCtx; Imports;
  resolvePolyCase; applySplice; checkElab; CheckElabResult)
open import Once.TypeCheck.Classify using (lookupPolyPrefix; lookupImport; ctxWithImportsAndPolys)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- plan 0.97: THE BUDGET VIEW. These statements were written when `T X` WAS
-- `ℕ → List SigOpEvent × X`; `atT` is that view of the record.
--
-- plan 0.98: A PAIR AGAIN. 0.97 made it a triple — trace, stop flag, value —
-- and every statement written against it had to carry the flag through the
-- middle. The flag and the value were always one fact ("did this return, and
-- with what"), and `Res` is that fact, so the third component is gone and
-- `T-ext-at` is a `cong₂` on the record's two fields.
------------------------------------------------------------------------
infixl 5 _⟨$⟩_
_⟨$⟩_ : ∀ {X : Set} → T X → ℕ → List SigOpEvent × Res X
_⟨$⟩_ = atT

T-ext-at : ∀ {X : Set} {l r : T X} → (∀ n → l ⟨$⟩ n ≡ r ⟨$⟩ n) → l ≡ r
T-ext-at {l = mkT t₁ r₁} {r = mkT t₂ r₂} h =
  cong₂ mkT (extensionality (λ n → cong proj₁ (h n)))
            (cong proj₂ (h 0))

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

-- A SigOp reference does not read the definitions environment. The surface
-- meaning dispatches on the type's shape, so the fact is stated per shape.
sigOp-σ-irrel : ∀ {n} {Γ : Srf.Ctx n} {A : Type} (σ σ′ : SD.DefsSem)
  (s : CanonicalName) (conc : IsConcrete A) (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ)
  → SD.⟦ Srf.sigOp {Γ = Γ} {A = A} s conc ⟧ˢ fmt σ dγ ≡ SD.⟦ Srf.sigOp {Γ = Γ} {A = A} s conc ⟧ˢ fmt σ′ dγ
sigOp-σ-irrel {A = _ T.⇒[ T.mk-kind Zero _ ] _} σ σ′ s (con-fun _ _) dγ = refl
sigOp-σ-irrel {A = _ T.⇒[ T.mk-kind One _ ] _}  σ σ′ s (con-fun _ _) dγ = refl
sigOp-σ-irrel {A = _ T.⇒[ T.mk-kind Many _ ] _} σ σ′ s (con-fun _ _) dγ = refl
sigOp-σ-irrel {A = _ T.⇒[ _ ] _} σ σ′ s (con-base ()) dγ
sigOp-σ-irrel {A = T.Unit}       σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.Void}       σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.Int}        σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.Float}      σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.Str}        σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.Buffer}     σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.rigid _ _}  σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = _ T.* _}      σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = _ T.+ _}      σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.μ-type _}   σ σ′ s conc dγ = refl
sigOp-σ-irrel {A = T.ν-type _ _} σ σ′ s conc dγ = refl

-- A linked reference is CLOSED: `poly x A` either stays (an internal call,
-- environment-free) or becomes `closed r` — so its meaning does not depend on
-- the context it sits in. Explicit-argument forms, so both sides reduce on
-- the same lookup / elaboration answers.
splice-ctx-indep :
  ∀ {n} {Γ : Srf.Ctx n} {A : Type}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys)) (imps : String → Imports) (userFns : Imports)
    (fresh : ℕ) (x : String) {schema body prefix}
    (polyEq : lookupPolyPrefix polys x ≡ just (schema , body , prefix))
    (r : CheckElabResult Srf.∅ A) (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ)
  → SD.⟦ applySplice {Γ = Γ} polys pAcc imps userFns fresh x A polyEq r ⟧ˢ fmt σ₀ dγ
      ≡ SD.⟦ applySplice {Γ = Srf.∅} polys pAcc imps userFns fresh x A polyEq r ⟧ˢ fmt σ₀ tt
splice-ctx-indep polys pAcc imps userFns fresh x polyEq (CheckElabResult.failure _) dγ = refl
splice-ctx-indep polys (acc rec) imps userFns fresh x polyEq (CheckElabResult.success Srf.[] eE _ _) dγ = refl

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
    (checkElab (ctxWithImportsAndPolys (imps x) prefix) body A) dγ

-- Two-sided bind congruence at each budget: `>>=T` at `j` reads `m j`, then
-- runs the continuation at what `m` LEFT (`j ∸ length (proj₁ (m j))`). The
-- continuation premise is pointwise at every budget, so it covers that one.
bind2-faithful : ∀ {X Y} (mR mU : T X) (gR gU : X → T Y)
  → (∀ j → mR ⟨$⟩ j ≡ mU ⟨$⟩ j) → (∀ v j → gR v ⟨$⟩ j ≡ gU v ⟨$⟩ j)
  → ∀ j → (mR >>=T gR) ⟨$⟩ j ≡ (mU >>=T gU) ⟨$⟩ j
-- plan 0.98: NO LONGER A REWRITE. The old proof rewrote the three components of
-- `mU`'s budget view and then named `valueT mU j` — the value `mU` returned — to
-- instantiate the continuation premise. Both halves of that are now unwritable:
-- a stopped `m` NEVER BUILDS its sequel (`bindRes tr stopped f = mkT tr stopped`
-- does not mention `f`), so `m >>=T g` is STUCK on `T.resT m` and rewriting the
-- trace cannot fire; and `valueT mU j` needs a `Returns?` witness that a
-- quantified `mU` cannot supply, because `mU` may genuinely stop.
-- `>>=T-cong₂-at` is the statement that survives: it splits on the result and,
-- in the stopped branch, never needs the continuation premise at all.
bind2-faithful mR mU gR gU me ge j =
  >>=T-cong₂-at {m₁ = mR} {m₂ = mU} gR gU j (me j) (λ v → T-ext-at (ge v))

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
    (ihA : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le₁ dγ) ⟨$⟩ j
                   ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₁ dγ) ⟨$⟩ j)
    (ihB : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le₂ dγ) ⟨$⟩ j
                   ≡ SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₂ dγ) ⟨$⟩ j)
    (k : ℕ)
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
      SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb) ⟨$⟩ k)
      ≡ ((SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
          SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb) ⟨$⟩ k)
binop-le-faithful {Γ = Γ} polys imps userFns fresh a b le₁ le₂ g dγ ihA ihB k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ Ea) (SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) Ea)
    (λ va → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ Eb >>=T λ vb → g va vb)
    (λ va → SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) Eb >>=T λ vb → g va vb)
    ihA
    (λ va j → bind2-faithful
                (SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ Eb) (SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) Eb)
                (λ vb → g va vb) (λ vb → g va vb)
                ihB
                (λ vb j' → refl) j)
    k
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
    (ihA : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) ⟨$⟩ j
                   ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) ⟨$⟩ j)
    (ihB : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) ⟨$⟩ j
                   ≡ SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) ⟨$⟩ j)
    (k : ℕ)
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
      SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb) ⟨$⟩ k)
      ≡ ((SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
          SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh)
            (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb) ⟨$⟩ k)
binop-faithful {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {C = C} polys imps userFns fresh a b g dγ ihA ihB k =
  binop-le-faithful {C = C} polys imps userFns fresh a b
    (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) g dγ ihA ihB k

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
    (ihA : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} le₁ dγ) ⟨$⟩ j
                   ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₁ dγ) ⟨$⟩ j)
    (ihB : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
                     (restrictᴰ {Γ = Γ} le₂ dγ) ⟨$⟩ j
                   ≡ SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le₂ dγ) ⟨$⟩ j)
    (k : ℕ)
  → returnT (λ (_ : Data.Unit.⊤) →
       SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
         (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
       SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀
         (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb) ⟨$⟩ k
      ≡ returnT (λ (_ : Data.Unit.⊤) →
       SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh)
         (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
       SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh)
         (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb) ⟨$⟩ k
thunk-binop-faithful {Γ = Γ} {C = C} polys imps userFns fresh a b le₁ le₂ g dγ ihA ihB k =
  cong (λ h → [] , returns h) (extensionality (λ _ → inner))
  where
    Ea = restrictᴰ {Γ = Γ} le₁ dγ
    Eb = restrictᴰ {Γ = Γ} le₂ dγ
    inner : (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ Ea >>=T λ va →
             SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt σ₀ Eb >>=T λ vb → g va vb)
              ≡ (SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) Ea >>=T λ va →
                 SD.⟦ b ⟧ˢ fmt (σR polys imps userFns fresh) Eb >>=T λ vb → g va vb)
    inner = T-ext-at (binop-le-faithful {C = C} polys imps userFns fresh a b le₁ le₂ g dγ ihA ihB)

-- | The UNARY-OPERAND shape: one sub-expression under an arbitrary narrowing
--   `le`, then a continuation the resolver leaves alone (`morph-app`, `fst'`,
--   `snd'`, `inl'`, `inr'`, and `app` at an erased argument). Same discipline as
--   `binop-faithful`: the monadic argument and the continuation are PARAMETERS.
unop-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ Ψ' : Usage n} {A C : Type}
    (polys : PolyCtx) (imps : String → Imports) (userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ A) (le : Ψ Srf.⊑ᵘ Ψ') (g : ⟦ A ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ Ψ' ⟧ᶜ ⟧ᴰ)
    (ih : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le dγ) ⟨$⟩ j
                  ≡ SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le dγ) ⟨$⟩ j)
    (k : ℕ)
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀
        (restrictᴰ {Γ = Γ} le dγ) >>=T g) ⟨$⟩ k)
      ≡ ((SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le dγ) >>=T g) ⟨$⟩ k)
unop-faithful {Γ = Γ} polys imps userFns fresh a le g dγ ih k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} le dγ))
    (SD.⟦ a ⟧ˢ fmt (σR polys imps userFns fresh) (restrictᴰ {Γ = Γ} le dγ))
    g g
    ih (λ v j → refl) k

------------------------------------------------------------------------
-- The faithfulness theorem.
------------------------------------------------------------------------

resolveExpr-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ : Usage n} {A : Type}
    (polys : PolyCtx) (imps : String → Imports) (userFns : Imports) (fresh : ℕ)
    (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ Srf.↾ Ψ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ resolveExpr polys imps userFns fresh e ⟧ˢ fmt σ₀ dγ ⟨$⟩ k
      ≡ SD.⟦ e ⟧ˢ fmt (σR polys imps userFns fresh) dγ ⟨$⟩ k
-- Leaves (resolveExpr unchanged ⇒ definitionally equal).
resolveExpr-faithful polys imps userFns fresh (Srf.var i) dγ k = refl
resolveExpr-faithful polys imps userFns fresh Srf.unit dγ k = refl
-- D226: a conversion maps the result and leaves the trace; resolution commutes.
resolveExpr-faithful polys imps userFns fresh (Srf.coerce p e) dγ k =
  cong (λ r → proj₁ r , mapRes ⟦ p ⟧<: (proj₂ r)) (resolveExpr-faithful polys imps userFns fresh e dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.int z) dγ k = refl
-- A float literal has no names in it, so resolution is the identity and the
-- denotation is unchanged — `refl`, exactly as for `int`.
resolveExpr-faithful polys imps userFns fresh (Srf.float d) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.str s) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.closure s) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.lift-morphism m) dγ k = refl
-- Unary / binary (structural ⇒ the IH, under the shared continuation).
-- plan 0.98: these were `rewrite`s of the three components of the budget view.
-- They no longer fire: a stopped computation never builds its sequel, so
-- `m >>=T g` is STUCK on `T.resT m` and rewriting `m`'s trace at `k` rewrites
-- nothing inside it. `>>=T-cong-at` is the same fact stated so it survives —
-- it splits on the result first, and the trace only exists to be concatenated
-- in the branch where there was one.
resolveExpr-faithful polys imps userFns fresh (Srf.fst' p) dγ k =
  >>=T-cong-at (λ v → returnT (proj₁ v)) k
    (resolveExpr-faithful polys imps userFns fresh p dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.snd' p) dγ k =
  >>=T-cong-at (λ v → returnT (proj₂ v)) k
    (resolveExpr-faithful polys imps userFns fresh p dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.inl' e) dγ k =
  >>=T-cong-at (λ v → returnT (inj₁ v)) k
    (resolveExpr-faithful polys imps userFns fresh e dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.inr' e) dγ k =
  >>=T-cong-at (λ v → returnT (inj₂ v)) k
    (resolveExpr-faithful polys imps userFns fresh e dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.neg e) dγ k =
  >>=T-cong-at (λ v → resT-lift (semM neg-info fmt v)) k
    (resolveExpr-faithful polys imps userFns fresh e dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.absurd e) dγ k =
  >>=T-cong-at (λ v → ⊥-elim v) k
    (resolveExpr-faithful polys imps userFns fresh e dγ k)
-- `morph-app`'s wrapper is a dependent `subst` chain, so `rewrite` (which IS
-- `with`-abstraction) cannot generalise the inner occurrence. `unop-faithful`
-- takes the monadic argument and the continuation as PARAMETERS instead, and
-- the IH is taken directly at the narrowed environment the goal carries.
resolveExpr-faithful polys imps userFns fresh
    (Srf.morph-app {Γ = Γ} {Ψ = Ψₑ} {A = A} {B = B} ir a) dγ k =
  unop-faithful {C = B} polys imps userFns fresh a
    (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψₑ) (Srf.⊑ᵘ-+ʳ Srf.zeroUsage (Many Srf.*ᵘ Ψₑ)))
    (λ v → subst T (cohᴰ B) (evalᴰ fmt ρ ir (subst (λ z → z) (sym (cohᴰ A)) v)))
    dγ (resolveExpr-faithful polys imps userFns fresh a
          (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψₑ)
                        (Srf.⊑ᵘ-+ʳ Srf.zeroUsage (Many Srf.*ᵘ Ψₑ))) dγ)) k
-- `app` splits on the arrow's quantity because its DENOTATION does: at `Zero`
-- the argument is erased and never evaluated, so only the function's IH is
-- needed. Each IH is transported to the environment the goal carries.
-- `app` splits on the arrow's quantity because its DENOTATION does: at `Zero`
-- the argument is ERASED and never evaluated, so only the function's IH exists
-- to use. No `rewrite` anywhere here — the continuation sits under a dependent
-- chain, so the equations are passed as PARAMETERS to the bind congruences.
resolveExpr-faithful polys imps userFns fresh
    (Srf.app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = Zero} f a) dγ k =
  unop-faithful {C = B} polys imps userFns fresh f
    (Srf.⊑ᵘ-+ˡ Ψ₁ (Zero Srf.*ᵘ Ψ₂)) (λ vf → vf tt)
    dγ (resolveExpr-faithful polys imps userFns fresh f
          (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Zero Srf.*ᵘ Ψ₂)) dγ)) k
resolveExpr-faithful polys imps userFns fresh
    (Srf.app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = One} f a) dγ k =
  binop-le-faithful {C = B} polys imps userFns fresh f a
    (Srf.⊑ᵘ-+ˡ Ψ₁ (One Srf.*ᵘ Ψ₂))
    (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*One Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (One Srf.*ᵘ Ψ₂)))
    (λ vf vx → vf vx) dγ
    (resolveExpr-faithful polys imps userFns fresh f
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (One Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh a
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*One Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (One Srf.*ᵘ Ψ₂))) dγ)) k
resolveExpr-faithful polys imps userFns fresh
    (Srf.app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = Many} f a) dγ k =
  binop-le-faithful {C = B} polys imps userFns fresh f a
    (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂))
    (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂)))
    (λ vf vx → vf vx) dγ
    (resolveExpr-faithful polys imps userFns fresh f
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh a
       (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) dγ)) k
-- D127: the combinators resolve componentwise; both arms' IHs rewrite and the
-- meaning is a function of the two results, so `refl` closes each.
resolveExpr-faithful polys imps userFns fresh (Srf.comp' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {C = C} {π = π} a b) dγ k =
  binop-le-faithful {C = A T.⇒[ T.mk-kind Many π ] C} polys imps userFns fresh a b (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) (λ va vb → returnT (λ a → vb a >>=T va)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.copair' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} a b) dγ k =
  binop-faithful {C = (A T.+ B) T.⇒[ T.mk-kind Many π ] C} polys imps userFns fresh a b (λ va vb → returnT (λ ab → [ va , vb ]′ ab)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fork' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} a b) dγ k =
  binop-faithful {C = A T.⇒[ T.mk-kind Many T.pure ] (B T.* C)} polys imps userFns fresh a b (λ va vb → returnT (λ a → va a >>=T λ x → vb a >>=T λ y → returnT (x , y))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.curry' f) dγ k =
  >>=T-cong-at (λ vf → returnT (λ a → returnT (λ b → vf (a , b)))) k
    (resolveExpr-faithful polys imps userFns fresh f dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} a b) dγ k =
  binop-faithful {C = A T.* B} polys imps userFns fresh a b (λ va vb → returnT (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.add {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → resT-lift (semM add-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.sub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → resT-lift (semM sub-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.mul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → resT-lift (semM mul-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
resolveExpr-faithful polys imps userFns fresh (Srf.fadd {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → resT-lift (semM fadd-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fsub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → resT-lift (semM fsub-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fmul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → resT-lift (semM fmul-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fdiv {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → resT-lift (semM fdiv-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.i2f a) dγ k =
  >>=T-cong-at (λ va → resT-lift (semM i2f-info fmt va)) k
    (resolveExpr-faithful polys imps userFns fresh a dγ k)
resolveExpr-faithful polys imps userFns fresh (Srf.div {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → resT-lift (semM div-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.mod' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → resT-lift (semM mod-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.lt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → resT-lift (semM lt-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.le {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → resT-lift (semM le-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.gt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → resT-lift (semM gt-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.ge {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → resT-lift (semM ge-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.eq {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → resT-lift (semM eq-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.ne {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → resT-lift (semM ne-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
-- Binders. `lam` splits on the arrow's quantity AND the binder's body usage,
-- matching its denotation. Over the ERASED environment the body's environment
-- is literally the `bindᴰ`/`bindᴰ0` the goal carries, so every IH lands with no
-- transport — and at `q' = Zero` no witness of `A` is required at all.
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} Zero prf b) dγ k =
  cong (λ h → [] , returns h) (extensionality (λ _ → T-ext-at (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} One prf b) dγ k =
  cong (λ h → [] , returns h) (extensionality (λ a → T-ext-at (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} Many prf b) dγ k =
  cong (λ h → [] , returns h) (extensionality (λ a → T-ext-at (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = One} {A = A} One prf b) dγ k =
  cong (λ h → [] , returns h) (extensionality (λ a → T-ext-at (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} One dγ a) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = One} {A = A} Many prf b) dγ k =
  cong (λ h → [] , returns h) (extensionality (λ a → T-ext-at (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} One dγ a) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Many} {A = A} Many prf b) dγ k =
  cong (λ h → [] , returns h) (extensionality (λ a → T-ext-at (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} Many dγ a) j)))
-- `let'` splits on the bound variable's usage. At `Zero` the bound value is
-- ERASED — `e₁` is never evaluated, so only the body's IH exists to use, and it
-- lands on the unextended environment.
-- D143: at an ERASED binder the body runs on the UNEXTENDED environment
-- (`bindᴰ0`), so `e₁` is never evaluated and no witness of `A` is needed —
-- which is precisely why the theorem must be stated over the ERASED
-- environment: over the full one this clause would demand an inhabitant of a
-- type that erasure exists to discard.
resolveExpr-faithful polys imps userFns fresh
    (Srf.let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} e₁ e₂) dγ k =
  resolveExpr-faithful polys imps userFns fresh e₂
    (bindᴰ0 {Γ = Γ} {A = A} (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₂ (Zero Srf.*ᵘ Ψ₁)) dγ)) k
resolveExpr-faithful polys imps userFns fresh
    (Srf.let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} e₁ e₂) dγ k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh e₁ ⟧ˢ fmt σ₀ E₁) (SD.⟦ e₁ ⟧ˢ fmt (σR polys imps userFns fresh) E₁)
    (λ v → SD.⟦ resolveExpr polys imps userFns fresh e₂ ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    (λ v → SD.⟦ e₂ ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    (resolveExpr-faithful polys imps userFns fresh e₁ E₁)
    (λ v → resolveExpr-faithful polys imps userFns fresh e₂ (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    k
  where
    E₁ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*One Ψ₁) (Srf.⊑ᵘ-+ʳ Ψ₂ (One Srf.*ᵘ Ψ₁))) dγ
    E₂ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₂ (One Srf.*ᵘ Ψ₁)) dγ
resolveExpr-faithful polys imps userFns fresh
    (Srf.let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} e₁ e₂) dγ k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh e₁ ⟧ˢ fmt σ₀ E₁) (SD.⟦ e₁ ⟧ˢ fmt (σR polys imps userFns fresh) E₁)
    (λ v → SD.⟦ resolveExpr polys imps userFns fresh e₂ ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
    (λ v → SD.⟦ e₂ ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
    (resolveExpr-faithful polys imps userFns fresh e₁ E₁)
    (λ v → resolveExpr-faithful polys imps userFns fresh e₂ (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
    k
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
               {A = A} {B = B} s l r) dγ k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh s ⟧ˢ fmt σ₀ Es) (SD.⟦ s ⟧ˢ fmt (σR polys imps userFns fresh) Es)
    (λ v → [ (λ a → SD.⟦ resolveExpr polys imps userFns fresh l ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
           , (λ b → SD.⟦ resolveExpr polys imps userFns fresh r ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v)
    (λ v → [ (λ a → SD.⟦ l ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
           , (λ b → SD.⟦ r ⟧ˢ fmt (σR polys imps userFns fresh) (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v)
    (resolveExpr-faithful polys imps userFns fresh s Es)
    (λ { (inj₁ a) → resolveExpr-faithful polys imps userFns fresh l (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a)
       ; (inj₂ b) → resolveExpr-faithful polys imps userFns fresh r (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b) })
    k
  where
    Eall = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψs (Ψₗ Srf.⊔ᵘ Ψᵣ)) dγ
    Es = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψs (Ψₗ Srf.⊔ᵘ Ψᵣ)) dγ
    Eₗ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) Eall
    Eᵣ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) Eall

resolveExpr-faithful polys imps userFns fresh
    (Srf.effApp {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} f x) dγ k =
  thunk-binop-faithful {C = B} polys imps userFns fresh f x (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) (λ vf vx → vf vx) dγ
    (resolveExpr-faithful polys imps userFns fresh f (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ (Many Srf.*ᵘ Ψ₂)) dγ))
    (resolveExpr-faithful polys imps userFns fresh x (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ (Many Srf.*ᵘ Ψ₂))) dγ)) k
-- cata: D131 — the algebra is BOUND, so both sides are `⟦alg⟧ˢ tt >>=T` the
-- same continuation and the whole clause is ONE `cong` over the algebra
-- denotation (the IH at empty env `tt`, lifted to a full T-value by funext
-- over fuel). The bind is why the trace is no longer syntactically `[]`.
resolveExpr-faithful polys imps userFns fresh (Srf.cata {F = F} {A = A} wf alg) dγ k =
  cong (λ ac → (ac >>=T λ valg →
                  returnT (λ x → sem-cata wf (SD.cata-ev-algˢ {F} {A} (returnT valg)) x)) ⟨$⟩ k)
       (T-ext-at (λ j → resolveExpr-faithful polys imps userFns fresh alg tt j))
-- ana: dual of cata — a closure over the CLOSED coalgebra `⟦coalg⟧ˢ tt`.
-- D179: the coalgebra now appears ONCE (inside the suspension) instead of
-- twice (in `ana-eventsˢ` for the trace and in `sem-ana` for the value), so
-- this is a single `cong` over the coalgebra denotation with nothing to
-- reconcile between the halves.
resolveExpr-faithful polys imps userFns fresh (Srf.ana {F = F} {A = A} wf coalg) dγ k =
  cong (λ ac → [] , returns (λ a → returnT (anaFᵈ F
         (λ a' → fmapT (coerce-functor-D F A) (ac >>=T λ clo → clo a')) a)))
       (T-ext-at (λ j → resolveExpr-faithful polys imps userFns fresh coalg tt j))
-- sigOp: D246 — the resolver passes it through, and a SigOp reads no environment.
resolveExpr-faithful {Γ = Γ} {A = A} polys imps userFns fresh (Srf.sigOp s conc) dγ k =
  cong (_⟨$⟩ k) (sigOp-σ-irrel {Γ = Γ} {A = A} σ₀ (σR polys imps userFns fresh) s conc dγ)
-- poly: the substitution lemma's variable case — the linked reference means
-- `σR x A` by definition, up to its context-independence.
resolveExpr-faithful {Γ = Γ} {A = A} polys imps userFns fresh (Srf.poly x T) dγ k =
  cong (_⟨$⟩ k) (poly-ctx-indep {Γ = Γ} {A = A} polys (<-wellFounded (length polys)) imps userFns fresh x
                   (lookupPolyPrefix polys x) refl dγ)
-- closed: a closed term runs on the empty environment on both sides.
resolveExpr-faithful polys imps userFns fresh (Srf.closed e) dγ k =
  resolveExpr-faithful polys imps userFns fresh e tt k