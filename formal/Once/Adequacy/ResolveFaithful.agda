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
-- (`resolveExpr-sigOp-closure-faithful` / `resolveExpr-poly-splice-faithful`).
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
module Once.Adequacy.ResolveFaithful (fmt : TargetNum) where

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using ([]; length)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Product using (_,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Once.Type using (Type; Int; Float; Unit; _+_; Quantity; Zero; One; Many)
import Once.Type as T
open import Once.Functor.Translate using (IsConcrete)
open import Once.Surface.Syntax as Srf using (Expr; Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; inject; forget; evalᴰ; cohᴰ)
open import Once.SigOp.Info using (semM)
open import Once.Arith.SigOp.Builders
open import Once.Denotation.TraceMonad using (T; _>>=T_; valueT; returnT)
open import Once.Semantics.Machine using (sem-cata; sem-ana; coerce-functor)
import Once.Denotation.SourceDenote as SD
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; PolyCtx; Imports;
  resolvePolyCase; applySplice; checkElab; CheckElabResult)
open import Once.TypeCheck.Classify using (lookupPoly; removePoly; lookupImport; ctxWithImportsAndPolys)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- The two NARROW denotational residuals (Plan 0.55 D#3). The former broad
-- `resolveExpr-faithful-hard` (any constructor) is REPLACED by:
--   (1) the `sigOp → closure` rewrite no-op (name ∈ userFns) — `emit-D`/`semM` for
--       `value-info s` vs `value-info (bare (showCanonical s))` coincide, and the
--       arrow-vs-value shape at a userFn agrees; a genuine denotational fact.
--   (2) the `poly` SPLICE (matched poly + body elaborates) — the inlined body
--       denotes as the poly placeholder. The `nothing`/`failure` sub-branches are
--       PROVEN (`refl`, poly unchanged). [[feedback_enumerate_over_catchall_postulate]]
------------------------------------------------------------------------

postulate
  resolveExpr-sigOp-closure-faithful :
    ∀ {n} {Γ : Srf.Ctx n} {A : Type}
      (s : CanonicalName) (conc : IsConcrete A) (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → SD.⟦ Srf.closure {Γ = Γ} {A = A} (showCanonical s) ⟧ˢ fmt dγ k
        ≡ SD.⟦ Srf.sigOp {Γ = Γ} {A = A} s conc ⟧ˢ fmt dγ k

  resolveExpr-poly-splice-faithful :
    ∀ {n} {Γ : Srf.Ctx n} {A : Type}
      (polys : PolyCtx) (pAcc : Acc _<_ (length polys)) (imps userFns : Imports) (fresh : ℕ)
      (x : String) {schema : _} {body : _} {Ψ0 : _} {eE : _} {d f : ℕ}
      (polyEq : lookupPoly polys x ≡ just (schema , body))
      (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → SD.⟦ applySplice {Γ = Γ} polys pAcc imps userFns fresh x A polyEq (CheckElabResult.success Ψ0 eE d f) ⟧ˢ fmt dγ k
        ≡ SD.⟦ Srf.poly {Γ = Γ} x A ⟧ˢ fmt dγ k

-- The `poly` case, J-style over the `lookupPoly` outcome (`lp`/`eqLP` explicit) so
-- `resolvePolyCase` reduces WITHOUT the documented `rewrite polyEq` with-abstraction
-- trap (Elaborate:3262). nothing / checkElab-failure ⇒ poly unchanged ⇒ refl; the
-- checkElab-success SPLICE ⇒ the narrow `resolveExpr-poly-splice-faithful`.
resolveExpr-poly-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {A : Type}
    (polys : PolyCtx) (pAcc : Acc _<_ (length polys)) (imps userFns : Imports) (fresh : ℕ)
    (x : String)
    (lp : Maybe _) (eqLP : lookupPoly polys x ≡ lp)
    (dγ : ⟦ ⟦ Γ Srf.↾ Srf.zeroUsage ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ resolvePolyCase {Γ = Γ} polys pAcc imps userFns fresh x A lp eqLP ⟧ˢ fmt dγ k
      ≡ SD.⟦ Srf.poly {Γ = Γ} x A ⟧ˢ fmt dγ k
resolveExpr-poly-faithful polys pAcc imps userFns fresh x nothing eqLP dγ k = refl
resolveExpr-poly-faithful {A = A} polys pAcc imps userFns fresh x (just (schema , body)) eqLP dγ k
  with checkElab (ctxWithImportsAndPolys imps (removePoly x polys)) body A
... | CheckElabResult.failure _ = refl
... | CheckElabResult.success Ψ0 eE d f =
      resolveExpr-poly-splice-faithful polys pAcc imps userFns fresh x eqLP dγ k

-- Two-sided bind congruence at each fuel: `>>=T` at `j` consumes only `m j`
-- (and the continuation at `proj₂ (m j)`), so pointwise equalities of BOTH the
-- monad value and the continuation transfer.
bind2-faithful : ∀ {X Y} (mR mU : T X) (gR gU : X → T Y)
  → (∀ j → mR j ≡ mU j) → (∀ v j → gR v j ≡ gU v j)
  → ∀ j → (mR >>=T gR) j ≡ (mU >>=T gU) j
bind2-faithful mR mU gR gU me ge j rewrite me j | ge (proj₂ (mU j)) j = refl

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
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
    (le₁ : Ψ₁ Srf.⊑ᵘ Ψ') (le₂ : Ψ₂ Srf.⊑ᵘ Ψ')
    (g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ Ψ' ⟧ᶜ ⟧ᴰ)
    (ihA : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt (restrictᴰ {Γ = Γ} le₁ dγ) j
                   ≡ SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} le₁ dγ) j)
    (ihB : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt (restrictᴰ {Γ = Γ} le₂ dγ) j
                   ≡ SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} le₂ dγ) j)
    (k : ℕ)
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt
        (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
      SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt
        (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb) k)
      ≡ ((SD.⟦ a ⟧ˢ fmt
            (restrictᴰ {Γ = Γ} le₁ dγ) >>=T λ va →
          SD.⟦ b ⟧ˢ fmt
            (restrictᴰ {Γ = Γ} le₂ dγ) >>=T λ vb → g va vb) k)
binop-le-faithful {Γ = Γ} polys imps userFns fresh a b le₁ le₂ g dγ ihA ihB k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt Ea) (SD.⟦ a ⟧ˢ fmt Ea)
    (λ va → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt Eb >>=T λ vb → g va vb)
    (λ va → SD.⟦ b ⟧ˢ fmt Eb >>=T λ vb → g va vb)
    ihA
    (λ va j → bind2-faithful
                (SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt Eb) (SD.⟦ b ⟧ˢ fmt Eb)
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
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
    (g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ (Ψ₁ Srf.+ᵘ Ψ₂) ⟧ᶜ ⟧ᴰ)
    (ihA : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) j
                   ≡ SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) j)
    (ihB : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) j
                   ≡ SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) j)
    (k : ℕ)
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt
        (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
      SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt
        (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb) k)
      ≡ ((SD.⟦ a ⟧ˢ fmt
            (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
          SD.⟦ b ⟧ˢ fmt
            (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb) k)
binop-faithful {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {C = C} polys imps userFns fresh a b g dγ ihA ihB k =
  binop-le-faithful {C = C} polys imps userFns fresh a b
    (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) g dγ ihA ihB k

-- | The SUSPENDED binary shape (`effApp`, D018): the application sits inside a
--   `returnT (λ _ → …)` thunk, so the equation is between THUNKS and has to pass
--   through funext. `extensionality`'s implicit function arguments cannot be
--   recovered from a `(m >>=T f) j` proof — `(m >>=T f) j` REDUCES, so the match
--   is higher-order — hence `inner` carries an explicit signature that pins them.
thunk-binop-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ₁ A) (b : Expr Γ Ψ₂ B)
    (g : ⟦ A ⟧ᴰ → ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ (Ψ₁ Srf.+ᵘ Ψ₂) ⟧ᶜ ⟧ᴰ)
    (ihA : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) j
                   ≡ SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) j)
    (ihB : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt
                     (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) j
                   ≡ SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) j)
    (k : ℕ)
  → returnT (λ (_ : Data.Unit.⊤) →
       SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt
         (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
       SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt
         (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb) k
      ≡ returnT (λ (_ : Data.Unit.⊤) →
       SD.⟦ a ⟧ˢ fmt
         (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ) >>=T λ va →
       SD.⟦ b ⟧ˢ fmt
         (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ) >>=T λ vb → g va vb) k
thunk-binop-faithful {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {C = C} polys imps userFns fresh a b g dγ ihA ihB k =
  cong (λ h → [] , h) (extensionality (λ _ → inner))
  where
    Ea = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ
    Eb = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ
    inner : (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt Ea >>=T λ va →
             SD.⟦ resolveExpr polys imps userFns fresh b ⟧ˢ fmt Eb >>=T λ vb → g va vb)
              ≡ (SD.⟦ a ⟧ˢ fmt Ea >>=T λ va →
                 SD.⟦ b ⟧ˢ fmt Eb >>=T λ vb → g va vb)
    inner = extensionality (binop-faithful {C = C} polys imps userFns fresh a b g dγ ihA ihB)

-- | The UNARY-OPERAND shape: one sub-expression under an arbitrary narrowing
--   `le`, then a continuation the resolver leaves alone (`morph-app`, `fst'`,
--   `snd'`, `inl'`, `inr'`, and `app` at an erased argument). Same discipline as
--   `binop-faithful`: the monadic argument and the continuation are PARAMETERS.
unop-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ Ψ' : Usage n} {A C : Type}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (a : Expr Γ Ψ A) (le : Ψ Srf.⊑ᵘ Ψ') (g : ⟦ A ⟧ᴰ → T ⟦ C ⟧ᴰ)
    (dγ : ⟦ ⟦ Γ Srf.↾ Ψ' ⟧ᶜ ⟧ᴰ)
    (ih : ∀ j → SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt (restrictᴰ {Γ = Γ} le dγ) j
                  ≡ SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} le dγ) j)
    (k : ℕ)
  → ((SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt
        (restrictᴰ {Γ = Γ} le dγ) >>=T g) k)
      ≡ ((SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} le dγ) >>=T g) k)
unop-faithful {Γ = Γ} polys imps userFns fresh a le g dγ ih k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh a ⟧ˢ fmt (restrictᴰ {Γ = Γ} le dγ))
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} le dγ))
    g g
    ih (λ v j → refl) k

------------------------------------------------------------------------
-- The faithfulness theorem.
------------------------------------------------------------------------

resolveExpr-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ : Usage n} {A : Type}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ Srf.↾ Ψ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ resolveExpr polys imps userFns fresh e ⟧ˢ fmt dγ k
      ≡ SD.⟦ e ⟧ˢ fmt dγ k
-- Leaves (resolveExpr unchanged ⇒ definitionally equal).
resolveExpr-faithful polys imps userFns fresh (Srf.var i) dγ k = refl
resolveExpr-faithful polys imps userFns fresh Srf.unit dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.arr' e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.int z) dγ k = refl
-- A float literal has no names in it, so resolution is the identity and the
-- denotation is unchanged — `refl`, exactly as for `int`.
resolveExpr-faithful polys imps userFns fresh (Srf.float d) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.str s) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.closure s) dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.lift-morphism m) dγ k = refl
-- Unary / binary (structural ⇒ rewrite the IHs).
resolveExpr-faithful polys imps userFns fresh (Srf.fst' p) dγ k rewrite resolveExpr-faithful polys imps userFns fresh p dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.snd' p) dγ k rewrite resolveExpr-faithful polys imps userFns fresh p dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.inl' e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.inr' e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.neg e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.absurd e) dγ k rewrite resolveExpr-faithful polys imps userFns fresh e dγ k = refl
-- `morph-app`'s wrapper is a dependent `subst` chain, so `rewrite` (which IS
-- `with`-abstraction) cannot generalise the inner occurrence. `unop-faithful`
-- takes the monadic argument and the continuation as PARAMETERS instead, and
-- the IH is taken directly at the narrowed environment the goal carries.
resolveExpr-faithful polys imps userFns fresh
    (Srf.morph-app {Γ = Γ} {Ψ = Ψₑ} {A = A} {B = B} ir a) dγ k =
  unop-faithful {C = B} polys imps userFns fresh a
    (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*Many Ψₑ) (Srf.⊑ᵘ-+ʳ Srf.zeroUsage (Many Srf.*ᵘ Ψₑ)))
    (λ v → subst T (cohᴰ B) (evalᴰ fmt ir (subst (λ z → z) (sym (cohᴰ A)) v)))
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
  binop-faithful {C = A T.⇒[ T.mk-kind Many π ] C} polys imps userFns fresh a b (λ va vb → returnT (λ a → vb a >>=T va)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.copair' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} a b) dγ k =
  binop-faithful {C = (A T.+ B) T.⇒[ T.mk-kind Many π ] C} polys imps userFns fresh a b (λ va vb → returnT (λ ab → [ va , vb ]′ ab)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fork' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} a b) dγ k =
  binop-faithful {C = A T.⇒[ T.mk-kind Many T.pure ] (B T.* C)} polys imps userFns fresh a b (λ va vb → returnT (λ a → va a >>=T λ x → vb a >>=T λ y → returnT (x , y))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.curry' f) dγ k rewrite resolveExpr-faithful polys imps userFns fresh f dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} a b) dγ k =
  binop-faithful {C = A T.* B} polys imps userFns fresh a b (λ va vb → returnT (va , vb)) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.add {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → returnT (semM add-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.sub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → returnT (semM sub-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.mul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → returnT (semM mul-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
resolveExpr-faithful polys imps userFns fresh (Srf.fadd {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → returnT (semM fadd-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fsub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → returnT (semM fsub-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fmul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → returnT (semM fmul-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.fdiv {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Float} polys imps userFns fresh a b (λ va vb → returnT (semM fdiv-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.i2f a) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.div {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → returnT (semM div-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.mod' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = Int} polys imps userFns fresh a b (λ va vb → returnT (semM mod-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.lt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → returnT (semM lt-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.le {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → returnT (semM le-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.gt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → returnT (semM gt-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.ge {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → returnT (semM ge-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.eq {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → returnT (semM eq-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
resolveExpr-faithful polys imps userFns fresh (Srf.ne {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ k =
  binop-faithful {C = (Unit + Unit)} polys imps userFns fresh a b (λ va vb → returnT (semM ne-info fmt (va , vb))) dγ
    (resolveExpr-faithful polys imps userFns fresh a (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh b (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
-- Binders. `lam` splits on the arrow's quantity AND the binder's body usage,
-- matching its denotation. Over the ERASED environment the body's environment
-- is literally the `bindᴰ`/`bindᴰ0` the goal carries, so every IH lands with no
-- transport — and at `q' = Zero` no witness of `A` is required at all.
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} Zero prf b) dγ k =
  cong (λ h → [] , h) (extensionality (λ _ → extensionality (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} One prf b) dγ k =
  cong (λ h → [] , h) (extensionality (λ a → extensionality (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Zero} {A = A} Many prf b) dγ k =
  cong (λ h → [] , h) (extensionality (λ a → extensionality (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ0 {Γ = Γ} {A = A} dγ) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = One} {A = A} One prf b) dγ k =
  cong (λ h → [] , h) (extensionality (λ a → extensionality (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} One dγ a) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = One} {A = A} Many prf b) dγ k =
  cong (λ h → [] , h) (extensionality (λ a → extensionality (λ j →
    resolveExpr-faithful polys imps userFns fresh b (bindᴰ {Γ = Γ} {A = A} One dγ a) j)))
resolveExpr-faithful polys imps userFns fresh
    (Srf.lam {Γ = Γ} {q' = Many} {A = A} Many prf b) dγ k =
  cong (λ h → [] , h) (extensionality (λ a → extensionality (λ j →
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
    (SD.⟦ resolveExpr polys imps userFns fresh e₁ ⟧ˢ fmt E₁) (SD.⟦ e₁ ⟧ˢ fmt E₁)
    (λ v → SD.⟦ resolveExpr polys imps userFns fresh e₂ ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    (λ v → SD.⟦ e₂ ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    (resolveExpr-faithful polys imps userFns fresh e₁ E₁)
    (λ v → resolveExpr-faithful polys imps userFns fresh e₂ (bindᴰ {Γ = Γ} {A = A} One E₂ v))
    k
  where
    E₁ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-trans (Srf.⊑ᵘ-*One Ψ₁) (Srf.⊑ᵘ-+ʳ Ψ₂ (One Srf.*ᵘ Ψ₁))) dγ
    E₂ = restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₂ (One Srf.*ᵘ Ψ₁)) dγ
resolveExpr-faithful polys imps userFns fresh
    (Srf.let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} e₁ e₂) dγ k =
  bind2-faithful
    (SD.⟦ resolveExpr polys imps userFns fresh e₁ ⟧ˢ fmt E₁) (SD.⟦ e₁ ⟧ˢ fmt E₁)
    (λ v → SD.⟦ resolveExpr polys imps userFns fresh e₂ ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
    (λ v → SD.⟦ e₂ ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} Many E₂ v))
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
    (SD.⟦ resolveExpr polys imps userFns fresh s ⟧ˢ fmt Es) (SD.⟦ s ⟧ˢ fmt Es)
    (λ v → [ (λ a → SD.⟦ resolveExpr polys imps userFns fresh l ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
           , (λ b → SD.⟦ resolveExpr polys imps userFns fresh r ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v)
    (λ v → [ (λ a → SD.⟦ l ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
           , (λ b → SD.⟦ r ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v)
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
  thunk-binop-faithful {C = B} polys imps userFns fresh f x (λ vf vx → vf vx) dγ
    (resolveExpr-faithful polys imps userFns fresh f (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ˡ Ψ₁ Ψ₂) dγ))
    (resolveExpr-faithful polys imps userFns fresh x (restrictᴰ {Γ = Γ} (Srf.⊑ᵘ-+ʳ Ψ₁ Ψ₂) dγ)) k
-- cata: D131 — the algebra is BOUND, so both sides are `⟦alg⟧ˢ tt >>=T` the
-- same continuation and the whole clause is ONE `cong` over the algebra
-- denotation (the IH at empty env `tt`, lifted to a full T-value by funext
-- over fuel). The bind is why the trace is no longer syntactically `[]`.
resolveExpr-faithful polys imps userFns fresh (Srf.cata {F = F} {A = A} wf alg) dγ k =
  cong (λ ac → (ac >>=T λ valg →
                  returnT (λ x → λ n →
                    let r = sem-cata wf (SD.cata-ev-algˢ {F} {A} n (returnT valg)) x
                    in (proj₁ r , proj₂ r))) k)
       (extensionality (λ j → resolveExpr-faithful polys imps userFns fresh alg tt j))
-- ana: dual of cata — a closure over the CLOSED coalgebra `⟦coalg⟧ˢ tt` (appears
-- in both `ana-eventsˢ` and `sem-ana`). One `cong` over the coalgebra denotation.
resolveExpr-faithful polys imps userFns fresh (Srf.ana {F = F} {A = A} wf coalg) dγ k =
  cong (λ ac → [] , (λ a → λ n →
         ( SD.ana-eventsˢ {F} {A} ac (forget a) n
         , inject (sem-ana F (λ a' → coerce-functor F _
                     (forget (valueT (valueT ac 0 (inject a')) 0))) (forget a)) )))
       (extensionality (λ j → resolveExpr-faithful polys imps userFns fresh coalg tt j))
-- sigOp: the resolver rewrites to `closure` iff the name is a user fn (else
-- unchanged). nothing ⇒ refl; just ⇒ the narrow sigOp→closure denotational no-op.
resolveExpr-faithful {Γ = Γ} {A = A} polys imps userFns fresh (Srf.sigOp s conc) dγ k
  with lookupImport userFns (showCanonical s)
... | just _  = resolveExpr-sigOp-closure-faithful {Γ = Γ} {A = A} s conc dγ k
... | nothing = refl
-- poly: J-style aux over the `lookupPoly` outcome (dodges the with-abstraction trap).
resolveExpr-faithful {Γ = Γ} {A = A} polys imps userFns fresh (Srf.poly x T) dγ k =
  resolveExpr-poly-faithful {Γ = Γ} {A = A} polys (<-wellFounded (length polys)) imps userFns fresh x
    (lookupPoly polys x) refl dγ k
