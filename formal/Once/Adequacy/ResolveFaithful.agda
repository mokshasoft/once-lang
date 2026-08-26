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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.Type using (Type; Int)
open import Once.Functor.Translate using (IsConcrete)
open import Once.Surface.Syntax as Srf using (Expr; Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; inject; forget)
open import Once.Denotation.TraceMonad using (T; _>>=T_; valueT)
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
      (s : CanonicalName) (conc : IsConcrete A) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → SD.⟦ Srf.closure {Γ = Γ} {A = A} (showCanonical s) ⟧ˢ fmt dγ k
        ≡ SD.⟦ Srf.sigOp {Γ = Γ} {A = A} s conc ⟧ˢ fmt dγ k

  resolveExpr-poly-splice-faithful :
    ∀ {n} {Γ : Srf.Ctx n} {A : Type}
      (polys : PolyCtx) (pAcc : Acc _<_ (length polys)) (imps userFns : Imports) (fresh : ℕ)
      (x : String) {schema : _} {body : _} {Ψ0 : _} {eE : _} {d f : ℕ}
      (polyEq : lookupPoly polys x ≡ just (schema , body))
      (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
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
    (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
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

------------------------------------------------------------------------
-- The faithfulness theorem.
------------------------------------------------------------------------

resolveExpr-faithful :
  ∀ {n} {Γ : Srf.Ctx n} {Ψ : Usage n} {A : Type}
    (polys : PolyCtx) (imps userFns : Imports) (fresh : ℕ)
    (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ resolveExpr polys imps userFns fresh e ⟧ˢ fmt dγ k ≡ SD.⟦ e ⟧ˢ fmt dγ k
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
resolveExpr-faithful polys imps userFns fresh (Srf.morph-app m a) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.app f a) dγ k rewrite resolveExpr-faithful polys imps userFns fresh f dγ k | resolveExpr-faithful polys imps userFns fresh a dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.pair a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.add a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.sub a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.mul a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
resolveExpr-faithful polys imps userFns fresh (Srf.fadd a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.fsub a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.fmul a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.div a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.mod' a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.lt a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.le a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.gt a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.ge a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.eq a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.ne a b) dγ k rewrite resolveExpr-faithful polys imps userFns fresh a dγ k | resolveExpr-faithful polys imps userFns fresh b dγ k = refl
-- Binders.
resolveExpr-faithful polys imps userFns fresh (Srf.lam q prf b) dγ k =
  cong ([] ,_)
    (extensionality (λ a → extensionality (λ j →
      resolveExpr-faithful polys imps userFns fresh b (dγ , a) j)))
resolveExpr-faithful polys imps userFns fresh (Srf.let' e₁ e₂) dγ k
  rewrite resolveExpr-faithful polys imps userFns fresh e₁ dγ k
        | resolveExpr-faithful polys imps userFns fresh e₂ (dγ , proj₂ (SD.⟦ e₁ ⟧ˢ fmt dγ k)) k = refl
resolveExpr-faithful polys imps userFns fresh (Srf.case' s l r) dγ k
  rewrite resolveExpr-faithful polys imps userFns fresh s dγ k
        | extensionality (λ a → extensionality (λ j → resolveExpr-faithful polys imps userFns fresh l (dγ , a) j))
        | extensionality (λ b → extensionality (λ j → resolveExpr-faithful polys imps userFns fresh r (dγ , b) j)) = refl
-- effApp: D018 closure `returnT (λ _ → ⟦f⟧ >>=T λ vf → ⟦x⟧ >>=T λ vx → vf vx)`.
-- Funext over the Unit arg + fuel; the body is a nested bind closed by bind2.
resolveExpr-faithful polys imps userFns fresh (Srf.effApp f x) dγ k =
  cong ([] ,_) (extensionality (λ _ → extensionality
    (bind2-faithful (SD.⟦ resolveExpr polys imps userFns fresh f ⟧ˢ fmt dγ) (SD.⟦ f ⟧ˢ fmt dγ) _ _
      (λ j → resolveExpr-faithful polys imps userFns fresh f dγ j)
      (λ vf → bind2-faithful (SD.⟦ resolveExpr polys imps userFns fresh x ⟧ˢ fmt dγ) (SD.⟦ x ⟧ˢ fmt dγ)
                (λ vx → vf vx) (λ vx → vf vx)
                (λ j → resolveExpr-faithful polys imps userFns fresh x dγ j)
                (λ vx j → refl)))))
-- cata: a closure folding `sem-cata` over the CLOSED algebra `⟦alg⟧ˢ tt`. One
-- `cong` over the algebra denotation (the IH at empty env tt, lifted to a full
-- T-value by funext over fuel); the fold structure is otherwise identical.
resolveExpr-faithful polys imps userFns fresh (Srf.cata {F = F} {A = A} wf alg) dγ k =
  cong (λ ac → [] , (λ x → λ n →
         let r = sem-cata wf (SD.cata-ev-algˢ {F} {A} n ac) x in (proj₁ r , proj₂ r)))
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
