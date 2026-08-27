-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RealizeAgrees — the proof behind `RealizeBridge.realize-agrees`
-- (Plan 0.49 piece 3). `checkElab`'s emitted term `se` denotes the same as the
-- canonical `realize` term read off its typing witness `w` (which `realize`
-- consumes, INDEPENDENT of `checkElab`'s term). A wrong elaboration breaks the apex.
--
-- Stated over the ELABORATOR EQUATION (`inferElabV`/`checkElabV ≡ (success … , w)`),
-- NOT an arbitrary derivation: the witness `w` is then exactly the elaborator's
-- own output, so `se` is well-defined (an arbitrary `⊢ᶜ` derivation over-generates
-- — `t-embed (t-pair …)` vs the `t-pair-lit-check` the checker actually emits).
-- Induct on `e`, fold the elaborator via `with inferElabV ctx a in eqa` (now clean
-- because the multi-`with` `inferElabV` clauses were refactored to aux helpers).
-- `faithful`-style agreements: `_>>=T_` threads each sub at the same depth `k`.
--
-- WIP: leaves + `RPair` (infer) validate the equation-form technique end to end;
-- the rest route through `infer-agreeV-todo`/`check-agreeV-todo`
-- ([[feedback_scaffold_then_discharge]] — to be emptied).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)
-- plan 0.74 J6 step 3: `⊝-fromℤ` — negating a literal IS the negated literal.
import Once.Word as OnceWord
import Data.List as DL

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.RealizeAgrees (fmt : TargetNum) where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-mono-<; +-mono-≤; m≤m+n; m≤n+m; +-suc; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import Once.Type
open import Once.Type using (Type; Int; Unit; Void; Float; Str; Buffer; _*_; _+_; μ-type; ν-type;
                             Purity; pure; eff; mk-kind; Many; One; Zero; _⇒[_]_; isUnit?; ⟦_⟧T; Functor)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx; extendNamedCtx; lookupSigEffect; lookupImport; lookupLocal; composeMid; ctxWithImportsAndPolys)
open import Once.TypeCheck.Elaborate using (success; failure; VerifiedInferResult; VerifiedCheckResult)
import Once.TypeCheck.Elaborate as E
open import Once.IR as IR using (IR)
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.SigEffect using (SigEffect) renaming (halts to se-halts; emits to se-emits)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Once.Adequacy.ResolveFaithful fmt using (bind2-faithful)
open import Once.TypeCheck.Completeness using (morph-elab; checkG-realize)
open import Data.Maybe.Properties using (just-injective)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Postulates using (extensionality)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Once.TypeCheck.Judgment using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; _⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_; t-int; t-str; t-unit; t-pair; t-neg; t-neg-float; t-let; t-binop-arith; t-binop-cmp; g-int; g-neg-int; g-neg-float; g-terminal; g-pair; g-inl; g-inr; g-In; extractMorphWitness)
open import Once.Denotation.Realize using (realize; realize-infer; realize-global; realize-morph)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Surface.Syntax as Surface using (Expr; Usage; ⟦_⟧ᶜ; pair; neg; let'; sigOp; lift-morphism)
open Surface.Usage using () renaming (_∷_ to _∷ᵘ_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ)
open import Once.Adequacy.CataFold fmt using (cata-fold-eq)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.SigOp.Info using (mk-info'; haltsV; emitsV; pureV; ffi-concrete)
open import Once.Arith.SigOp.Builders using (generic-semM)
import Once.Denotation.SourceDenote as SD
open import Once.CanonicalName using (CanonicalName; showCanonical; bare)
open import Once.Functor.Translate using (WellFormedF; IsBaseType; IsConcrete; con-base; con-fun; base-Unit)
open import Once.Functor.Decide using (wellFormedF?; isBaseType?; isConcrete?)

private
  Env : NamedCtx → Set
  Env ctx = ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜ ⟧ᴰ

-- Agreement of the elaborator's emitted term `se` with `realize`(its witness),
-- over the elaborator equation. (Forward sigs for the mutual block + scaffolds.)
InferAgreeV : (ctx : NamedCtx) (e : RawExpr) {A : Type} {Ψ : Usage (NamedCtx.size ctx)}
              {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ} {w : ctx ⊢ᵢ e ∶ A ⨾ Ψ}
            → E.inferElabV ctx e ≡ (success A Ψ se d f , w) → Set
InferAgreeV ctx e {se = se} {w = w} _ =
  ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k

CheckAgreeV : (ctx : NamedCtx) (e : RawExpr) (T : Type) {Ψ : Usage (NamedCtx.size ctx)}
              {se : Expr (NamedCtx.debruijn ctx) Ψ T} {d f : ℕ} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ}
            → E.checkElabV ctx e T ≡ (success Ψ se d f , w) → Set
CheckAgreeV ctx e T {se = se} {w = w} _ =
  ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k

-- `infer-agreeV` is now TOTAL (every RawExpr constructor handled; the RApp
-- apply head is a morph-app congruence, `other` rides `agree-RApp-other-aux`).
-- Only check-mode's
-- non-`t-embed` specials (RLam/RVar-bbc/RPair-product/RInt-vlift/literals)
-- remain as a postulate.
postulate
  -- The RVar residual: ONLY `poly` (rides the `bbc-other-poly-witness` gap). The 6
  -- bare builtins (id/fst/snd/terminal/initial/inl/inr) are now DISCHARGED below.
  check-agreeV-RVar-poly-todo : ∀ (ctx : NamedCtx) (x : String) (T : Type) {fe snd Ψ se d f w}
    → E.checkElabV-RVar-bbc-other-aux ctx x T (failure fe , snd) ≡ (success Ψ se d f , w)
    → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
  -- Plan 0.58 / D071: the INFER-mode twin — the ground telescope reference's
  -- `poly` emission rides the `bbc-other-poly-infer-witness` gap the same way.
  infer-agreeV-RVar-poly-todo : ∀ (ctx : NamedCtx) (x : String) {A Ψ se d f w}
    → E.inferElabV-RVar-poly-aux ctx x (E.classifyBareBuiltin x) refl ≡ (success A Ψ se d f , w)
    → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
  -- (Plan 0.55 D#2: `check-RApp-todo` ELIMINATED — all RApp check views discharged
  -- by explicit `agree-check-RApp` clauses; the residual is the narrow
  -- `agree-cata-denotes` denotational leaf. See below.)

-- DISCHARGED bbc-id leaf: `spec id = lift-morphism IR.id`, `realize-morph (m-id) =
-- IR.id`, so the sole success leaf (arrow target A⇒A, both lookups absent, A≟A) is
-- `refl`; every other target / lookup-found branch fails ⇒ absurd success-eq.
check-agreeV-RVar-id : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-id-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
check-agreeV-RVar-id ctx (X ⇒[ mk-kind Many π ] Y) eq
  with E.inspectLookupLocal ctx "id" | E.inspectLookupImport ctx "id" | eq
... | E.llv-not-found _ | E.liv-not-found _ | eq' with X E.≟T Y | eq'
...   | yes refl | refl = λ dγ k → refl
...   | no _     | ()
check-agreeV-RVar-id ctx (X ⇒[ mk-kind Many π ] Y) eq
  | E.llv-not-found _ | E.liv-found _ | ()
check-agreeV-RVar-id ctx (X ⇒[ mk-kind Many π ] Y) eq
  | E.llv-found _ | _ | ()
check-agreeV-RVar-id ctx Unit ()
check-agreeV-RVar-id ctx Void ()
check-agreeV-RVar-id ctx Int ()
check-agreeV-RVar-id ctx Float ()
check-agreeV-RVar-id ctx Str ()
check-agreeV-RVar-id ctx Buffer ()
check-agreeV-RVar-id ctx (_ * _) ()
check-agreeV-RVar-id ctx (_ + _) ()
check-agreeV-RVar-id ctx (μ-type _) ()
check-agreeV-RVar-id ctx (ν-type _) ()
check-agreeV-RVar-id ctx (_ ⇒[ mk-kind One _ ] _) ()
check-agreeV-RVar-id ctx (_ ⇒[ mk-kind Zero _ ] _) ()

-- DISCHARGED bbc-fst leaf: success at `(A * B) ⇒[Many π] A'` (lookups absent, A≟A');
-- `spec fst = lift-morphism IR.fst`, `realize-morph (m-fst) = IR.fst` ⇒ `refl`. All
-- other targets make `checkElabV-RVar-bbc-fst-failure-aux` reduce to `failure`, so
-- the success premise is a constructor clash Agda coverage prunes (no absurd matrix).
check-agreeV-RVar-fst : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-fst-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
check-agreeV-RVar-fst ctx ((A * B) ⇒[ mk-kind Many π ] A') eq
  with E.inspectLookupLocal ctx "fst" | E.inspectLookupImport ctx "fst" | eq
... | E.llv-not-found _ | E.liv-not-found _ | eq' with A E.≟T A' | eq'
...   | yes refl | refl = λ dγ k → refl
...   | no _     | ()
check-agreeV-RVar-fst ctx ((A * B) ⇒[ mk-kind Many π ] A') eq
  | E.llv-not-found _ | E.liv-found _ | ()
check-agreeV-RVar-fst ctx ((A * B) ⇒[ mk-kind Many π ] A') eq
  | E.llv-found _ | _ | ()

-- DISCHARGED bbc-snd (as fst, success at `(A * B) ⇒[Many π] B'` with B≟B').
check-agreeV-RVar-snd : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-snd-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
check-agreeV-RVar-snd ctx ((A * B) ⇒[ mk-kind Many π ] B') eq
  with E.inspectLookupLocal ctx "snd" | E.inspectLookupImport ctx "snd" | eq
... | E.llv-not-found _ | E.liv-not-found _ | eq' with B E.≟T B' | eq'
...   | yes refl | refl = λ dγ k → refl
...   | no _     | ()
check-agreeV-RVar-snd ctx ((A * B) ⇒[ mk-kind Many π ] B') eq
  | E.llv-not-found _ | E.liv-found _ | ()
check-agreeV-RVar-snd ctx ((A * B) ⇒[ mk-kind Many π ] B') eq
  | E.llv-found _ | _ | ()

-- DISCHARGED bbc-terminal: success at the canonical target; every other target makes
-- the elaborator dispatch fail (absurd success-eq). Codomain-fixed ⇒ quantity must
-- be concrete, so enumerate Many/One/Zero × codomain as plain top-level () (no
-- with-abstraction); non-arrow targets auto-prune via the premise clash.
check-agreeV-RVar-terminal : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-terminal-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many π ] Unit) eq
  with E.inspectLookupLocal ctx "terminal" | E.inspectLookupImport ctx "terminal" | eq
... | E.llv-not-found _ | E.liv-not-found _ | refl = λ dγ k → refl
... | E.llv-not-found _ | E.liv-found _ | ()
... | E.llv-found _ | _ | ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Unit) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Unit) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Void) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Void) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Void) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Int) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Int) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Int) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Float) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Float) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Float) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Str) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Str) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Str) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] Buffer) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] Buffer) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] Buffer) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (_ * _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (_ * _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (_ * _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (_ + _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (_ + _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (_ + _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (μ-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (μ-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (μ-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Many _ ] (ν-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind One _ ] (ν-type _)) ()
check-agreeV-RVar-terminal ctx (A ⇒[ mk-kind Zero _ ] (ν-type _)) ()

-- DISCHARGED bbc-initial: success at `Void ⇒[Many π] A` (no type-eq, lookups only).
check-agreeV-RVar-initial : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-initial-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
check-agreeV-RVar-initial ctx (Void ⇒[ mk-kind Many π ] A) eq
  with E.inspectLookupLocal ctx "initial" | E.inspectLookupImport ctx "initial" | eq
... | E.llv-not-found _ | E.liv-not-found _ | refl = λ dγ k → refl
... | E.llv-not-found _ | E.liv-found _ | ()
... | E.llv-found _ | _ | ()

-- DISCHARGED bbc-inl: success at the canonical target; every other target makes
-- the elaborator dispatch fail (absurd success-eq). Codomain-fixed ⇒ quantity must
-- be concrete, so enumerate Many/One/Zero × codomain as plain top-level () (no
-- with-abstraction); non-arrow targets auto-prune via the premise clash.
check-agreeV-RVar-inl : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-inl-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many π ] (A' + B)) eq
  with E.inspectLookupLocal ctx "inl" | E.inspectLookupImport ctx "inl" | eq
... | E.llv-not-found _ | E.liv-not-found _ | eq' with A E.≟T A' | eq'
...   | yes refl | refl = λ dγ k → refl
...   | no _     | ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many π ] (A' + B)) eq
  | E.llv-not-found _ | E.liv-found _ | ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many π ] (A' + B)) eq
  | E.llv-found _ | _ | ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (_ + _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (_ + _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Unit) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Unit) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Unit) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Void) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Void) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Void) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Int) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Int) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Int) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Float) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Float) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Float) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Str) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Str) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Str) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] Buffer) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] Buffer) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] Buffer) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (_ * _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (_ * _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (_ * _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (μ-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (μ-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (μ-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Many _ ] (ν-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind One _ ] (ν-type _)) ()
check-agreeV-RVar-inl ctx (A ⇒[ mk-kind Zero _ ] (ν-type _)) ()

-- DISCHARGED bbc-inr: success at the canonical target; every other target makes
-- the elaborator dispatch fail (absurd success-eq). Codomain-fixed ⇒ quantity must
-- be concrete, so enumerate Many/One/Zero × codomain as plain top-level () (no
-- with-abstraction); non-arrow targets auto-prune via the premise clash.
check-agreeV-RVar-inr : ∀ (ctx : NamedCtx) (T : Type) {fe snd Ψ se d f w}
  → E.checkElabV-RVar-bbc-inr-aux ctx T (failure fe , snd) ≡ (success Ψ se d f , w)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many π ] (A + B')) eq
  with E.inspectLookupLocal ctx "inr" | E.inspectLookupImport ctx "inr" | eq
... | E.llv-not-found _ | E.liv-not-found _ | eq' with B E.≟T B' | eq'
...   | yes refl | refl = λ dγ k → refl
...   | no _     | ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many π ] (A + B')) eq
  | E.llv-not-found _ | E.liv-found _ | ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many π ] (A + B')) eq
  | E.llv-found _ | _ | ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (_ + _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (_ + _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Unit) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Unit) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Unit) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Void) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Void) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Void) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Int) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Int) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Int) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Float) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Float) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Float) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Str) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Str) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Str) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] Buffer) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] Buffer) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] Buffer) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (_ * _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (_ * _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (_ * _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (_ ⇒[ _ ] _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (μ-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (μ-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (μ-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Many _ ] (ν-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind One _ ] (ν-type _)) ()
check-agreeV-RVar-inr ctx (B ⇒[ mk-kind Zero _ ] (ν-type _)) ()

-- RPair folded top-level (no `with`): take both sub-results explicitly +
-- their sub-IHs as functions; the de-withed `inferElabV-RPair-aux` reduces by
-- pattern-matching them. success/success is the real case; a `failure` sub
-- makes the aux a `failure`, so the success equation is absurd.
agree-RPair : ∀ {ctx : NamedCtx} {a b : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RPair a b ∶ A ⨾ Ψ}
  (rA : VerifiedInferResult ctx a) (rB : VerifiedInferResult ctx b)
  → E.inferElabV-RPair-aux ctx a b rA rB ≡ (success A Ψ se d f , w)
  → (∀ {Aₐ Ψₐ aE dₐ fₐ} {wA : ctx ⊢ᵢ a ∶ Aₐ ⨾ Ψₐ}
       → rA ≡ (success Aₐ Ψₐ aE dₐ fₐ , wA) → ∀ dγ k → SD.⟦ aE ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer wA ⟧ˢ fmt dγ k)
  → (∀ {Bᵦ Ψᵦ bE dᵦ fᵦ} {wB : ctx ⊢ᵢ b ∶ Bᵦ ⨾ Ψᵦ}
       → rB ≡ (success Bᵦ Ψᵦ bE dᵦ fᵦ , wB) → ∀ dγ k → SD.⟦ bE ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer wB ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RPair (success Aₐ Ψₐ aE dₐ fₐ , wA) (success Bᵦ Ψᵦ bE dᵦ fᵦ , wB) refl subA subB dγ k
  rewrite subA refl dγ k | subB refl dγ k = refl
agree-RPair (failure _ , _) _ () subA subB
agree-RPair (success _ _ _ _ _ , _) (failure _ , _) () subA subB

-- RUnaryOp(neg) folded top-level (avoids mutual-block `...|` ambiguity,
-- [[feedback_mutual_block_syntax]]): takes the sub-result explicitly + the
-- sub-IH as a function (applied only in the Int branch). Non-Int/failure subs
-- make `inferElabV-RUnaryOp-aux` a `failure`, so the success equation is absurd.
agree-RUnaryOp : ∀ {ctx : NamedCtx} {e : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RUnaryOp Raw.OpNeg e ∶ A ⨾ Ψ}
  (rE : VerifiedInferResult ctx e)
  → E.inferElabV-RUnaryOp-aux ctx e rE ≡ (success A Ψ se d f , w)
  → (∀ {Ψ' eE' d' fr'} {wE' : ctx ⊢ᵢ e ∶ Int ⨾ Ψ'}
       → rE ≡ (success Int Ψ' eE' d' fr' , wE')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer wE' ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RUnaryOp (success Int Ψ eE d fr , wE) refl subAg dγ k rewrite subAg refl dγ k = refl
agree-RUnaryOp (failure _ , _) () subAg
agree-RUnaryOp (success Once.Type.Unit _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Void _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Float _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Str _ _ _ _ , _) () subAg
agree-RUnaryOp (success Once.Type.Buffer _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.* _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.+ _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (_ Once.Type.⇒[ _ ] _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (Once.Type.μ-type _) _ _ _ _ , _) () subAg
agree-RUnaryOp (success (Once.Type.ν-type _) _ _ _ _ , _) () subAg

-- RBinOp folded top-level (mirrors `inferElabV-RBinOp-aux`'s left-type /
-- right-type / op dispatch). Both operands must elaborate to `Int`; any other
-- left/right shape makes the aux `failure`, so the success equation is absurd
-- (`()`). For the 11 success ops the witness is `t-binop-{arith,cmp} refl w₁ w₂`
-- and `se` is the matching arithmetic/comparison IR; `realize-infer` rebuilds
-- the SAME IR over `realize-infer w₁/w₂`, so rewriting both operand IHs at
-- `(dγ,k)` (the binary op denotation is fuel-`k`-pointwise, as for `agree-RPair`)
-- closes each case with `refl`.
agree-RBinOp : ∀ {ctx : NamedCtx} (op : Raw.BinOp) {e₁ e₂ : RawExpr} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RBinOp op e₁ e₂ ∶ A ⨾ Ψ}
  (r₁ : VerifiedInferResult ctx e₁) (r₂ : VerifiedInferResult ctx e₂)
  → E.inferElabV-RBinOp-aux ctx op e₁ e₂ r₁ r₂ ≡ (success A Ψ se d f , w)
  → (∀ {A₁ Ψ₁ e₁E d₁ f₁} {w₁ : ctx ⊢ᵢ e₁ ∶ A₁ ⨾ Ψ₁}
       → r₁ ≡ (success A₁ Ψ₁ e₁E d₁ f₁ , w₁) → ∀ dγ k → SD.⟦ e₁E ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ k)
  → (∀ {A₂ Ψ₂ e₂E d₂ f₂} {w₂ : ctx ⊢ᵢ e₂ ∶ A₂ ⨾ Ψ₂}
       → r₂ ≡ (success A₂ Ψ₂ e₂E d₂ f₂ , w₂) → ∀ dγ k → SD.⟦ e₂E ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w₂ ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
-- left operand fails to be Int → aux is `failure`
agree-RBinOp op (failure _ , _) _ () s₁ s₂
agree-RBinOp op (success Unit          _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Void          _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Str           _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success Buffer        _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ * _)       _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ + _)       _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (_ ⇒[ _ ] _)  _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (μ-type _)    _ _ _ _ , _) _ () s₁ s₂
agree-RBinOp op (success (ν-type _)    _ _ _ _ , _) _ () s₁ s₂
-- left is Int, right fails to be Int → aux is `failure`
agree-RBinOp op (success Int _ _ _ _ , _) (failure _ , _)                  () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Unit          _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Void          _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Str           _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success Buffer        _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ * _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ + _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (_ ⇒[ _ ] _)  _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (μ-type _)    _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Int _ _ _ _ , _) (success (ν-type _)    _ _ _ _ , _) () s₁ s₂
-- both Int → the op picks the IR; rewrite both operand IHs at (dγ,k)
agree-RBinOp Raw.OpAdd (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpSub (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpMul (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpDiv (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpMod (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpLt (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpLe (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpGt (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpGe (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpEq (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpNe (success Int _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
-- PLAN 0.75 F4: `Float` on the left is no longer absurd — it selects the float
-- family. Same shape as the integer block above: a mismatched right operand
-- still makes the aux a `failure`, and the three real ops rewrite both operand
-- IHs. `/`, `%` and the comparisons stay absurd at `Float`, which is what
-- `isFloatArithmeticOp` buys.
agree-RBinOp op (success Float _ _ _ _ , _) (failure _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Unit       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Void       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Str       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success Buffer       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (_ * _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (_ + _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (_ ⇒[ _ ] _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (μ-type _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp op (success Float _ _ _ _ , _) (success (ν-type _)       _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpAdd (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpSub (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpMul (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpDiv (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpMod (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLt (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLe (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGt (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGe (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpEq (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpNe (success Float _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
-- D125: the mixed forms are no longer absurd — the `Int` side widens. Same
-- two-IH rewrite; the `i2f` node sits inside the elaborated term on one side
-- and inside `realize-infer`'s output on the other, so it cancels.
agree-RBinOp Raw.OpAdd (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpAdd (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpSub (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpSub (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpMul (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpMul (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) refl s₁ s₂ dγ k
  rewrite s₁ refl dγ k | s₂ refl dγ k = refl
agree-RBinOp Raw.OpDiv (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpDiv (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpMod (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpMod (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLt (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLt (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLe (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpLe (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGt (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGt (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGe (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpGe (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpEq (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpEq (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpNe (success Int _ _ _ _ , _) (success Float _ _ _ _ , _) () s₁ s₂
agree-RBinOp Raw.OpNe (success Float _ _ _ _ , _) (success Int _ _ _ _ , _) () s₁ s₂

-- RLet folded with-free via two levels (e₂'s context depends on e₁'s type A):
-- `agree-RLet` matches the e₁ result, `agree-RLet2` the e₂ result; the let'
-- agreement threads `v1` through `_>>=T_` by inline rewrite (rewrite the bound
-- IH at `(dγ,k)` — fixing `v1` — then the body IH at the now-fixed
-- `(dγ, proj₂ ⟦realize w₁⟧)`). The e₂ IH
-- is passed as a function of A (only knowable after matching e₁).
agree-RLet2 : ∀ {ctx : NamedCtx} {x e₁ e₂ A B} {Ψ₁ : Usage (NamedCtx.size ctx)}
  {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ B} {d f} {w : ctx ⊢ᵢ Raw.RLet x e₁ e₂ ∶ B ⨾ Ψ}
  (e₁E : Expr (NamedCtx.debruijn ctx) Ψ₁ A) (d₁ f₁ : ℕ) (w₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁)
  (rE2 : VerifiedInferResult (extendNamedCtx ctx x A) e₂)
  → E.inferElabV-RLet-aux2 ctx x e₁ e₂ e₁E d₁ f₁ w₁ rE2 ≡ (success B Ψ se d f , w)
  → (∀ dγ k → SD.⟦ e₁E ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ k)
  → (∀ {B' q Ψ₂' e₂E d₂' f₂'} {w₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B' ⨾ (q ∷ᵘ Ψ₂')}
       → rE2 ≡ (success B' (q ∷ᵘ Ψ₂') e₂E d₂' f₂' , w₂)
       → ∀ dγ' k → SD.⟦ e₂E ⟧ˢ fmt dγ' k ≡ SD.⟦ realize-infer w₂ ⟧ˢ fmt dγ' k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RLet2 e₁E d₁ f₁ w₁ (success B (q ∷ᵘ Ψ₂) e₂E d₂ f₂ , w₂) refl e₁ag e₂IH dγ k
  rewrite e₁ag dγ k | e₂IH refl (dγ , proj₂ (SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ k)) k = refl
agree-RLet2 e₁E d₁ f₁ w₁ (failure _ , _) () e₁ag e₂IH

agree-RLet : ∀ {ctx : NamedCtx} {x e₁ e₂ B} {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ B} {d f} {w : ctx ⊢ᵢ Raw.RLet x e₁ e₂ ∶ B ⨾ Ψ}
  (rE1 : VerifiedInferResult ctx e₁)
  → E.inferElabV-RLet-aux ctx x e₁ e₂ rE1 ≡ (success B Ψ se d f , w)
  → (∀ {A Ψ₁ e₁E d₁ f₁} {w₁ : ctx ⊢ᵢ e₁ ∶ A ⨾ Ψ₁}
       → rE1 ≡ (success A Ψ₁ e₁E d₁ f₁ , w₁) → ∀ dγ k → SD.⟦ e₁E ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w₁ ⟧ˢ fmt dγ k)
  → (∀ {A} → (rE2 : VerifiedInferResult (extendNamedCtx ctx x A) e₂)
       → E.inferElabV (extendNamedCtx ctx x A) e₂ ≡ rE2
       → ∀ {B' q Ψ₂' e₂E d₂' f₂'} {w₂ : extendNamedCtx ctx x A ⊢ᵢ e₂ ∶ B' ⨾ (q ∷ᵘ Ψ₂')}
         → rE2 ≡ (success B' (q ∷ᵘ Ψ₂') e₂E d₂' f₂' , w₂)
         → ∀ dγ' k → SD.⟦ e₂E ⟧ˢ fmt dγ' k ≡ SD.⟦ realize-infer w₂ ⟧ˢ fmt dγ' k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RLet {ctx} {x} {e₁} {e₂} (success A Ψ₁ e₁E d₁ f₁ , w₁) eq e₁IH e₂IH dγ k =
  agree-RLet2 e₁E d₁ f₁ w₁ (E.inferElabV (extendNamedCtx ctx x A) e₂) eq
              (e₁IH refl) (λ p → e₂IH (E.inferElabV (extendNamedCtx ctx x A) e₂) refl p) dγ k
agree-RLet (failure _ , _) () e₁IH e₂IH

-- THE MASQUERADE (Plan 0.50): at a `Many`-arrow, the elaborator's effect-aware
-- `lift-morphism (IR.SigOp (ext-resolved-info cn π))` denotes the same as
-- `realize`'s `sigOp cn`. Now `refl` (after the effect-as-leaf-annotation fix):
-- both read the effect off the arrow's `Purity` via the SHARED `isUnit?`, and
-- `emit-D` collapses `Emits`/`Halts` (the event reads only the name = `cn`),
-- `semM` collapses to `tt`. `pure` → both `value-info`; `eff` → one `isUnit?`
-- case-split, the `Unit` branch one `lookupSigEffect` split, every leaf `refl`.
masq : ∀ {ctx : NamedCtx} {Dom Cod : Type} (cn : CanonicalName) (π : Purity)
       (bDom : IsBaseType Dom) (cCod : IsConcrete Cod)
       (dγ : Env ctx) (k : ℕ)
     → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {π = π} (IR.SigOp (E.ext-resolved-info {Dom} {Cod} ctx cn π bDom cCod)) ⟧ˢ fmt dγ k
      ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many π ] Cod} cn (con-fun bDom cCod) ⟧ˢ fmt dγ k
-- `Cod ≡ Unit` branch: the arrow is an effect contract. `emit-D` collapses
-- `Emits`/`Halts` to the same event (it reads only `name = cn`), so every
-- `lookupSigEffect` outcome — `se-halts`, `se-emits`, `nothing` — denotes the
-- same thing as `realize`'s `sigOp cn` (whose `arrow-info-eff cn (isUnit? Unit)`
-- = `emitsV`). All three leaves are `refl`. No `with` (mse is an explicit arg).
masq-unit : ∀ {ctx : NamedCtx} {Dom : Type} (cn : CanonicalName) (mse : Maybe SigEffect)
            (bDom : IsBaseType Dom) (cCod : IsConcrete Unit)
            (dγ : Env ctx) (k : ℕ)
          → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {π = eff} (IR.SigOp (E.ext-resolved-info-aux {Dom} {Unit} cn eff (yes refl) mse bDom cCod)) ⟧ˢ fmt dγ k
           ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many eff ] Unit} cn (con-fun bDom cCod) ⟧ˢ fmt dγ k
masq-unit cn (just se-halts) bDom cCod dγ k = cong (λ f → returnT f k) (liftFn-SigOp (E.ext-resolved-info-aux cn eff (yes refl) (just se-halts) bDom cCod) bDom)
masq-unit cn (just se-emits) bDom cCod dγ k = cong (λ f → returnT f k) (liftFn-SigOp (E.ext-resolved-info-aux cn eff (yes refl) (just se-emits) bDom cCod) bDom)
masq-unit cn nothing         bDom cCod dγ k = cong (λ f → returnT f k) (liftFn-SigOp (E.ext-resolved-info-aux cn eff (yes refl) nothing bDom cCod) bDom)

-- The outer dispatch on `isUnit? Cod` is a `with` (NOT a Dec-arg helper): the
-- scrutinee appears in the GOAL via `⟦ sigOp … ⟧ˢ` (which computes `isUnit? Cod`
-- internally), and only the `yes refl` UNIFICATION (`Cod := Unit`) reduces that
-- hidden occurrence. A helper taking the `Dec` explicitly would leave the RHS's
-- `isUnit? Cod` stuck. `masq` is a leaf equality lemma — opaque downstream — so
-- the `with` blocks no later proof's reduction. The inner mse split lives in the
-- with-free `masq-unit`, keeping this a single, flat `with`.
masq {ctx} {Dom} {Cod} cn pure bDom cCod dγ k = cong (λ f → returnT f k) (liftFn-SigOp (E.ext-resolved-info ctx cn pure bDom cCod) bDom)
masq {ctx} {Dom} {Cod} cn eff bDom cCod dγ k with isUnit? Cod
... | no ¬p = cong (λ f → returnT f k) (liftFn-SigOp (E.ext-resolved-info-aux cn eff (no ¬p) (lookupSigEffect (NamedCtx.sigEffects ctx) (showCanonical cn)) bDom cCod) bDom)
... | yes refl = masq-unit {ctx} {Dom} cn (lookupSigEffect (NamedCtx.sigEffects ctx) (showCanonical cn)) bDom cCod dγ k

-- The RQualified analogue of `masq`. `ext-arrow-info` decides its Unit-codomain
-- via `E._≟T_ Unit` (NOT the `isUnit?` realize's `sigOp` uses), so the bridge
-- cross-checks both deciders. `pure` is `refl` on both sides. For `eff`:
-- `Cod ≟T Unit = yes` ⇒ `Cod := Unit`, realize's `isUnit? Unit` also fires, and
-- the `lookupSigEffect` split is all `refl` (emit-D reads only the name, so
-- haltsV/emitsV collapse, exactly as in `masq-unit`); `Cod ≟T Unit = no ¬p` ⇒
-- both sides `pureV` once `isUnit? Cod` is forced to `no` (its `yes` corner
-- contradicts ¬p).
masq-arrow : ∀ {ctx : NamedCtx} {Dom Cod : Type} (alias name : String) (π : Purity)
       (bDom : IsBaseType Dom) (cCod : IsConcrete Cod)
       (dγ : Env ctx) (k : ℕ)
     → SD.⟦ lift-morphism {Γ = NamedCtx.debruijn ctx} {π = π} (IR.SigOp (E.ext-arrow-info {Dom} {Cod} ctx alias name π bDom cCod)) ⟧ˢ fmt dγ k
      ≡ SD.⟦ sigOp {Γ = NamedCtx.debruijn ctx} {A = Dom ⇒[ mk-kind Many π ] Cod} (bare (alias ++ "." ++ name)) (con-fun bDom cCod) ⟧ˢ fmt dγ k
masq-arrow {ctx} {Dom} {Cod} alias name pure bDom cCod dγ k = cong (λ f → returnT f k) (liftFn-SigOp (E.ext-arrow-info ctx alias name pure bDom cCod) bDom)
masq-arrow {ctx} {Dom} {Cod} alias name eff bDom cCod dγ k with Cod E.≟T Unit
... | yes refl with lookupSigEffect (NamedCtx.sigEffects ctx) (alias ++ "." ++ name)
...   | just se-halts = cong (λ f → returnT f k) (liftFn-SigOp (mk-info' (bare (alias ++ "." ++ name)) (haltsV refl) bDom (ffi-concrete cCod)) bDom)
...   | just se-emits = cong (λ f → returnT f k) (liftFn-SigOp (mk-info' (bare (alias ++ "." ++ name)) (emitsV refl) bDom (ffi-concrete cCod)) bDom)
...   | nothing       = cong (λ f → returnT f k) (liftFn-SigOp (mk-info' (bare (alias ++ "." ++ name)) (emitsV refl) bDom (ffi-concrete cCod)) bDom)
masq-arrow {ctx} {Dom} {Cod} alias name eff bDom cCod dγ k | no ¬p with isUnit? Cod
... | no _     = cong (λ f → returnT f k) (liftFn-SigOp (mk-info' (bare (alias ++ "." ++ name)) (pureV (generic-semM (alias ++ "." ++ name))) bDom (ffi-concrete cCod)) bDom)
... | yes refl = ⊥-elim (¬p refl)

-- RResolved agreement, dispatched on the import-lookup result exactly as the
-- elaborator's `inferElabV-RResolved-aux` does. A `Many`-arrow type resolves to
-- the effect-aware `lift-morphism (SigOp (ext-resolved-info …))` whose
-- agreement with realize's `sigOp cn` IS the `masq`-erade; every other type
-- resolves to `sigOp cn` directly (= realize) so agreement is `refl`. The type
-- shapes are ENUMERATED (not a catch-all): the aux's `just ty` clause sits
-- behind the `just (Many-arrow)` clause, so on an abstract type it would not
-- reduce — mirroring `Completeness`'s `go`. `nothing` ⇒ the aux fails, so the
-- success-eq is absurd.
-- `failure` and `success` are distinct constructors of `InferElabResult`, so a
-- proof identifying them is absurd (used to discharge the `nothing`-lookup case,
-- where the elaborator fails but the agreement obligation assumes success).
fail≢succ : ∀ {n} {Δ : Surface.Ctx n} {te} {A} {Ψ} {se : Surface.Expr Δ Ψ A} {d f}
          → failure {Δ = Δ} te ≡ success A Ψ se d f → ⊥
fail≢succ ()

-- Plan 0.58 de-with drivers: pattern-match the concreteness decision GENUINELY
-- (as helper params), so the arrow/value aux commits to a `success`/`failure`
-- clause. The caller passes `(isBaseType? A) refl`/`(isConcrete? ty) refl`; the
-- application stays well-typed at the goal even when those are stuck.
agree-RResolved-arrowᴴ : ∀ (ctx : NamedCtx) (cn : CanonicalName) {A B : Type} (π : Purity)
  (lkup : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just (A ⇒[ mk-kind Many π ] B))
  (mbA : Maybe (IsBaseType A)) (eqbA : isBaseType? A ≡ mbA)
  (mcB : Maybe (IsConcrete B)) (eqcB : isConcrete? B ≡ mcB)
  {A' Ψ se d f w}
  → E.inferElabV-RResolved-arrow-aux ctx cn lkup mbA eqbA mcB eqcB ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RResolved-arrowᴴ ctx cn {A} {B} π lkup (just bA) eqbA (just cB) eqcB refl dγ k = masq {ctx} {A} {B} cn π bA cB dγ k
agree-RResolved-arrowᴴ ctx cn π lkup nothing eqbA _ eqcB eqS dγ k = ⊥-elim (fail≢succ (cong proj₁ eqS))
agree-RResolved-arrowᴴ ctx cn π lkup (just _) eqbA nothing eqcB eqS dγ k = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RResolved-valueᴴ : ∀ (ctx : NamedCtx) (cn : CanonicalName) (ty : Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ just ty)
  (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
  {A' Ψ se d f w}
  → E.inferElabV-RResolved-value-aux ctx cn ty lkup mc eqc ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RResolved-valueᴴ ctx cn ty lkup (just conc) eqc refl dγ k = refl
agree-RResolved-valueᴴ ctx cn ty lkup nothing eqc eqS dγ k = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RResolved : ∀ (ctx : NamedCtx) (cn : CanonicalName) (lhs : Maybe Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (showCanonical cn) ≡ lhs)
  {A Ψ se d f w}
  → E.inferElabV-RResolved-aux ctx cn lhs lkup ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RResolved ctx cn (just (A ⇒[ mk-kind Many π ] B)) lkup eqS dγ k =
  agree-RResolved-arrowᴴ ctx cn π lkup (isBaseType? A) refl (isConcrete? B) refl eqS dγ k
agree-RResolved ctx cn (just (A ⇒[ mk-kind One  π ] B)) lkup eqS dγ k =
  agree-RResolved-valueᴴ ctx cn (A ⇒[ mk-kind One π ] B) lkup (isConcrete? (A ⇒[ mk-kind One π ] B)) refl eqS dγ k
agree-RResolved ctx cn (just (A ⇒[ mk-kind Zero π ] B)) lkup eqS dγ k =
  agree-RResolved-valueᴴ ctx cn (A ⇒[ mk-kind Zero π ] B) lkup (isConcrete? (A ⇒[ mk-kind Zero π ] B)) refl eqS dγ k
agree-RResolved ctx cn (just Unit)        lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn Unit   lkup (isConcrete? Unit)   refl eqS dγ k
agree-RResolved ctx cn (just Void)        lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn Void   lkup (isConcrete? Void)   refl eqS dγ k
agree-RResolved ctx cn (just Int)         lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn Int    lkup (isConcrete? Int)    refl eqS dγ k
agree-RResolved ctx cn (just Float)       lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn Float  lkup (isConcrete? Float)  refl eqS dγ k
agree-RResolved ctx cn (just Str)         lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn Str    lkup (isConcrete? Str)    refl eqS dγ k
agree-RResolved ctx cn (just Buffer)      lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn Buffer lkup (isConcrete? Buffer) refl eqS dγ k
agree-RResolved ctx cn (just (A * B))     lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn (A * B) lkup (isConcrete? (A * B)) refl eqS dγ k
agree-RResolved ctx cn (just (A + B))     lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn (A + B) lkup (isConcrete? (A + B)) refl eqS dγ k
agree-RResolved ctx cn (just (μ-type F))  lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn (μ-type F) lkup (isConcrete? (μ-type F)) refl eqS dγ k
agree-RResolved ctx cn (just (ν-type F))  lkup eqS dγ k = agree-RResolved-valueᴴ ctx cn (ν-type F) lkup (isConcrete? (ν-type F)) refl eqS dγ k
agree-RResolved ctx cn nothing lkup eq dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))

-- RVar (non-unit): cases the lookup-aux. Local → the bound SExpr IS realize's
-- `eE`; import → both elaborator and `realize-infer` emit `sigOp (bare x)`;
-- neither-found → the success equation is absurd. No `masq` (unlike RResolved,
-- whose aux emits a `lift-morphism` for arrows).
agree-RVar-importᴴ : ∀ (ctx : NamedCtx) (x : String) (¬u : ¬ (x ≡ "unit"))
  (eq-loc : lookupLocal ctx x ≡ nothing) (ty : Type)
  (eq-imp : lookupImport (NamedCtx.imports ctx) x ≡ just ty)
  (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
  {A' Ψ se d f w}
  → E.inferElabV-RVar-import-value-aux ctx x ¬u eq-loc ty eq-imp mc eqc ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RVar-importᴴ ctx x ¬u eq-loc ty eq-imp (just conc) eqc refl dγ k = refl
agree-RVar-importᴴ ctx x ¬u eq-loc ty eq-imp nothing eqc eqS dγ k = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RVar : ∀ (ctx : NamedCtx) (x : String) (¬u : ¬ (x ≡ "unit"))
  (locLhs : Maybe (∃[ A ] ∃[ Ψ ] (Surface.SVar (NamedCtx.debruijn ctx) Ψ A)))
  (eq-loc : lookupLocal ctx x ≡ locLhs)
  (impLhs : Maybe Type) (eq-imp : lookupImport (NamedCtx.imports ctx) x ≡ impLhs)
  {A Ψ se d f w}
  → E.inferElabV-RVar-lookup-aux ctx x ¬u locLhs eq-loc impLhs eq-imp ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RVar ctx x ¬u (just (A , Ψ , se)) eq-loc impLhs eq-imp refl dγ k = refl
agree-RVar ctx x ¬u nothing eq-loc (just ty) eq-imp eqS dγ k =
  agree-RVar-importᴴ ctx x ¬u eq-loc ty eq-imp (isConcrete? ty) refl eqS dγ k
-- Plan 0.58 / D071: both lookups failed → the POLY FALLBACK (a ground
-- telescope name infers at its declared type). Its success rides the
-- premise-erased witness, so agreement is the narrow infer-poly residual.
agree-RVar ctx x ¬u nothing eq-loc nothing eq-imp eq dγ k =
  infer-agreeV-RVar-poly-todo ctx x eq dγ k

-- RQualified agreement, dispatched on the import-lookup of the dotted path,
-- exactly as `inferElabV-RQualified-aux` does. A `Many`-arrow resolves to the
-- effect-aware `lift-morphism (SigOp (ext-arrow-info …))` whose agreement with
-- realize's `sigOp (bare (alias.name))` is `masq-arrow`; every other type
-- resolves to that same `sigOp` directly (= realize) so agreement is `refl`.
-- `nothing` ⇒ the aux fails, so the success-eq is absurd.
agree-RQualified-arrowᴴ : ∀ (ctx : NamedCtx) (name alias : String) {A B : Type} (π : Purity)
  (lkup : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just (A ⇒[ mk-kind Many π ] B))
  (mbA : Maybe (IsBaseType A)) (eqbA : isBaseType? A ≡ mbA)
  (mcB : Maybe (IsConcrete B)) (eqcB : isConcrete? B ≡ mcB)
  {A' Ψ se d f w}
  → E.inferElabV-RQualified-arrow-aux ctx name alias lkup mbA eqbA mcB eqcB ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RQualified-arrowᴴ ctx name alias {A} {B} π lkup (just bA) eqbA (just cB) eqcB refl dγ k = masq-arrow {ctx} {A} {B} alias name π bA cB dγ k
agree-RQualified-arrowᴴ ctx name alias π lkup nothing eqbA _ eqcB eqS dγ k = ⊥-elim (fail≢succ (cong proj₁ eqS))
agree-RQualified-arrowᴴ ctx name alias π lkup (just _) eqbA nothing eqcB eqS dγ k = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RQualified-valueᴴ : ∀ (ctx : NamedCtx) (name alias : String) (ty : Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ just ty)
  (mc : Maybe (IsConcrete ty)) (eqc : isConcrete? ty ≡ mc)
  {A' Ψ se d f w}
  → E.inferElabV-RQualified-value-aux ctx name alias ty lkup mc eqc ≡ (success A' Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RQualified-valueᴴ ctx name alias ty lkup (just conc) eqc refl dγ k = refl
agree-RQualified-valueᴴ ctx name alias ty lkup nothing eqc eqS dγ k = ⊥-elim (fail≢succ (cong proj₁ eqS))

agree-RQualified : ∀ (ctx : NamedCtx) (name alias : String) (lhs : Maybe Type)
  (lkup : lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name) ≡ lhs)
  {A Ψ se d f w}
  → E.inferElabV-RQualified-aux ctx name alias lhs lkup ≡ (success A Ψ se d f , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RQualified ctx name alias (just (A ⇒[ mk-kind Many π ] B)) lkup eqS dγ k =
  agree-RQualified-arrowᴴ ctx name alias π lkup (isBaseType? A) refl (isConcrete? B) refl eqS dγ k
agree-RQualified ctx name alias (just (A ⇒[ mk-kind One  π ] B)) lkup eqS dγ k =
  agree-RQualified-valueᴴ ctx name alias (A ⇒[ mk-kind One π ] B) lkup (isConcrete? (A ⇒[ mk-kind One π ] B)) refl eqS dγ k
agree-RQualified ctx name alias (just (A ⇒[ mk-kind Zero π ] B)) lkup eqS dγ k =
  agree-RQualified-valueᴴ ctx name alias (A ⇒[ mk-kind Zero π ] B) lkup (isConcrete? (A ⇒[ mk-kind Zero π ] B)) refl eqS dγ k
agree-RQualified ctx name alias (just Unit)        lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias Unit   lkup (isConcrete? Unit)   refl eqS dγ k
agree-RQualified ctx name alias (just Void)        lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias Void   lkup (isConcrete? Void)   refl eqS dγ k
agree-RQualified ctx name alias (just Int)         lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias Int    lkup (isConcrete? Int)    refl eqS dγ k
agree-RQualified ctx name alias (just Float)       lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias Float  lkup (isConcrete? Float)  refl eqS dγ k
agree-RQualified ctx name alias (just Str)         lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias Str    lkup (isConcrete? Str)    refl eqS dγ k
agree-RQualified ctx name alias (just Buffer)      lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias Buffer lkup (isConcrete? Buffer) refl eqS dγ k
agree-RQualified ctx name alias (just (A * B))     lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias (A * B) lkup (isConcrete? (A * B)) refl eqS dγ k
agree-RQualified ctx name alias (just (A + B))     lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias (A + B) lkup (isConcrete? (A + B)) refl eqS dγ k
agree-RQualified ctx name alias (just (μ-type F))  lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias (μ-type F) lkup (isConcrete? (μ-type F)) refl eqS dγ k
agree-RQualified ctx name alias (just (ν-type F))  lkup eqS dγ k = agree-RQualified-valueᴴ ctx name alias (ν-type F) lkup (isConcrete? (ν-type F)) refl eqS dγ k
agree-RQualified ctx name alias nothing lkup eq dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))

-- RApp agreement, dispatched on the app-head VIEW (a parameter of
-- `inferElabV-RApp-dispatch`, so we case it directly — no `with` on
-- `classifyAppHeadView`). 9 check-only/initial heads FAIL in infer mode, so the
-- success-eq is absurd. The 5 builtin-combinator heads emit `morph-app IR.X arg`
-- (unary `>>=T`, same morphism both sides ⇒ `rewrite` the arg IH) or `arr' arg`
-- (denotational identity ⇒ the arg IH directly); their `realize-infer (t-X-app)`
-- is the same shape over the witness. `ahv-apply` emits `morph-app apply argE`
-- (same morphism both sides ⇒ arg-IH congruence); `ahv-other` (generic
-- app/effApp; also needs the FUNCTION-position agreement) rides
-- `agree-RApp-other-aux` below.
-- ahv-other (infer) — the verified counterpart of `inferElabV-RApp-other-aux`.
-- The elaborator emits `app fE xE` (pure arrow) or `effApp fE xE` (Many-eff
-- arrow), and `realize-infer (t-app …) = app (realize-infer wF) (realize wX)`
-- (resp. `effApp …`) — the SAME shape — so the agreement is a plain
-- application congruence: the FUNCTION position rides `fInferIH` (f is inferred)
-- and the ARGUMENT position rides `argCheckIH` (the arg is CHECKED at f's
-- domain). The app denotation is a nested `_>>=T_`, closed by `bind2-faithful`
-- (outer = fInferIH; inner = argCheckIH with a definitionally-equal
-- continuation ⇒ `refl`). effApp wraps the same body in `returnT (λ _ → …)`, so
-- it is the app proof under `extensionality`. Every non-arrow / eff-One/Zero f
-- makes the elaborator fail ⇒ success-eq absurd. The `lhs`/`eqAH` arguments
-- mirror `inferElabV-RApp-other-aux` exactly (so the dispatch reduces).
agree-RApp-other-aux : ∀ {ctx : NamedCtx} (f arg : RawExpr) {A Ψ se d fr w}
  (lhs : Maybe E.PolyBuiltinApp) (eqAH : E.classifyAppHead f ≡ lhs)
  → E.inferElabV-RApp-other-aux ctx f arg lhs eqAH ≡ (success A Ψ se d fr , w)
  → (fInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ f ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx f ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize w' ⟧ˢ fmt dγ k)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RApp-other-aux f arg (just _) eqAH () fInferIH argCheckIH
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH dγ k
  with E.inferElabV ctx f | eq
... | failure _ , _ | ()
... | success Unit       _ _ _ _ , _ | ()
... | success Void       _ _ _ _ , _ | ()
... | success Int        _ _ _ _ , _ | ()
... | success Float      _ _ _ _ , _ | ()
... | success Str        _ _ _ _ , _ | ()
... | success Buffer     _ _ _ _ , _ | ()
... | success (_ * _)      _ _ _ _ , _ | ()
... | success (_ + _)      _ _ _ _ , _ | ()
... | success (μ-type _)   _ _ _ _ , _ | ()
... | success (ν-type _)   _ _ _ _ , _ | ()
... | success (A ⇒[ mk-kind q pure ] B) Ψ₁ fE df ff , wF | eq₁
      with E.checkElabV ctx arg A in xeq | eq₁
...   | failure _ , _ | ()
...   | success Ψ₂ xE dx fx , wX | refl =
        bind2-faithful (SD.⟦ fE ⟧ˢ fmt dγ) (SD.⟦ realize-infer wF ⟧ˢ fmt dγ)
          (λ vf → SD.⟦ xE ⟧ˢ fmt dγ >>=T λ vx → vf vx)
          (λ vf → SD.⟦ realize wX ⟧ˢ fmt dγ >>=T λ vx → vf vx)
          (λ j → fInferIH refl dγ j)
          (λ vf j → bind2-faithful (SD.⟦ xE ⟧ˢ fmt dγ) (SD.⟦ realize wX ⟧ˢ fmt dγ)
                      (λ vx → vf vx) (λ vx → vf vx)
                      (λ j' → argCheckIH xeq dγ j') (λ _ _ → refl) j)
          k
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH dγ k
  | success (A ⇒[ mk-kind Many eff ] B) Ψ₁ fE df ff , wF | eq₁
      with E.checkElabV ctx arg A in xeq | eq₁
...   | failure _ , _ | ()
...   | success Ψ₂ xE dx fx , wX | refl =
        cong (λ g → returnT g k)
          (extensionality (λ _ → extensionality (λ j →
            bind2-faithful (SD.⟦ fE ⟧ˢ fmt dγ) (SD.⟦ realize-infer wF ⟧ˢ fmt dγ)
              (λ vf → SD.⟦ xE ⟧ˢ fmt dγ >>=T λ vx → vf vx)
              (λ vf → SD.⟦ realize wX ⟧ˢ fmt dγ >>=T λ vx → vf vx)
              (λ j' → fInferIH refl dγ j')
              (λ vf j' → bind2-faithful (SD.⟦ xE ⟧ˢ fmt dγ) (SD.⟦ realize wX ⟧ˢ fmt dγ)
                          (λ vx → vf vx) (λ vx → vf vx)
                          (λ j'' → argCheckIH xeq dγ j'') (λ _ _ → refl) j')
              j)))
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH dγ k
  | success (A ⇒[ mk-kind One eff ] B) _ _ _ _ , _ | ()
agree-RApp-other-aux {ctx} f arg nothing eqAH eq fInferIH argCheckIH dγ k
  | success (A ⇒[ mk-kind Zero eff ] B) _ _ _ _ , _ | ()

agree-RApp : ∀ (ctx : NamedCtx) (f arg : RawExpr) {A Ψ se d fr w}
  (vw : E.AppHeadView f) (veq : E.classifyAppHeadView f ≡ vw)
  → E.inferElabV-RApp-dispatch ctx f arg vw veq ≡ (success A Ψ se d fr , w)
  → (argIH : ∀ {A' Ψ' argE d' fr'} {w' : ctx ⊢ᵢ arg ∶ A' ⨾ Ψ'}
       → E.inferElabV ctx arg ≡ (success A' Ψ' argE d' fr' , w')
       → ∀ dγ k → SD.⟦ argE ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  -- function-position + checked-arg IHs (only `ahv-other` consumes them).
  → (fInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ f ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx f ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize w' ⟧ˢ fmt dγ k)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
-- check-only / infer-failing heads: the dispatch is `failure`, so success-eq absurd.
agree-RApp ctx f arg E.ahv-inl            veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-inr            veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-initial        veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-pair-applied   veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-compose-applied veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-case-applied   veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-In             veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-cata           veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
agree-RApp ctx f arg E.ahv-curry          veq eq argIH fInferIH argCheckIH dγ k = ⊥-elim (fail≢succ (cong proj₁ eq))
-- ahv-id : any-typed arg, result morph-app id.
agree-RApp ctx f arg E.ahv-id veq eq argIH fInferIH argCheckIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success T Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
-- ahv-terminal : any-typed arg, result morph-app terminal.
agree-RApp ctx f arg E.ahv-terminal veq eq argIH fInferIH argCheckIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success T Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
-- ahv-fst : arg must be a product; other shapes fail.
agree-RApp ctx f arg E.ahv-fst veq eq argIH fInferIH argCheckIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (A * B) Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
... | success Unit _ _ _ _ , _ | ()
... | success Void _ _ _ _ , _ | ()
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
-- ahv-snd : arg must be a product; other shapes fail.
agree-RApp ctx f arg E.ahv-snd veq eq argIH fInferIH argCheckIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success (A * B) Ψ argE d fr , w | refl rewrite argIH refl dγ k = refl
... | success Unit _ _ _ _ , _ | ()
... | success Void _ _ _ _ , _ | ()
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
-- (Plan 0.52 M1: `ahv-arr` agree clause retired with the surface `arr` builtin.)
-- ahv-apply / ahv-other : genuine semantic content (deferred).
-- ahv-apply: arg must infer to `(A ⇒[Many,pure] B) * A`; se = `morph-app apply argE`
-- (elaborator emits the apply MORPHISM directly — no specApply lambda / weakening),
-- witness `t-apply-app-infer w`, realize = `morph-app apply (realize-infer w)` ⇒ a
-- plain morph-app congruence (rewrite the arg IH). Every other arg-type fails ⇒ absurd.
agree-RApp ctx f arg E.ahv-apply veq eq argIH fInferIH argCheckIH dγ k with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success Unit _ _ _ _ , _ | ()
... | success Void _ _ _ _ , _ | ()
... | success Int _ _ _ _ , _ | ()
... | success Float _ _ _ _ , _ | ()
... | success Str _ _ _ _ , _ | ()
... | success Buffer _ _ _ _ , _ | ()
... | success (_ + _) _ _ _ _ , _ | ()
... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
... | success (μ-type _) _ _ _ _ , _ | ()
... | success (ν-type _) _ _ _ _ , _ | ()
... | success (Unit * _) _ _ _ _ , _ | ()
... | success (Void * _) _ _ _ _ , _ | ()
... | success (Int * _) _ _ _ _ , _ | ()
... | success (Float * _) _ _ _ _ , _ | ()
... | success (Str * _) _ _ _ _ , _ | ()
... | success (Buffer * _) _ _ _ _ , _ | ()
... | success ((_ * _) * _) _ _ _ _ , _ | ()
... | success ((_ + _) * _) _ _ _ _ , _ | ()
... | success ((μ-type _) * _) _ _ _ _ , _ | ()
... | success ((ν-type _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind Many eff ] _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind One pure ] _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind One eff ] _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind Zero pure ] _) * _) _ _ _ _ , _ | ()
... | success ((_ ⇒[ mk-kind Zero eff ] _) * _) _ _ _ _ , _ | ()
... | success ((A ⇒[ mk-kind Many pure ] B) * A') Ψ argE d fr , w | eq₁ with A E.≟T A' | eq₁
...   | yes refl | refl rewrite argIH refl dγ k = refl
...   | no _     | ()
-- ahv-other: the dispatch reduces to `inferElabV-RApp-other ctx f arg =
-- inferElabV-RApp-other-aux ctx f arg (classifyAppHead f) refl`, so `eq` already
-- has the aux's type; delegate (the IHs ride f-infer and arg-check).
agree-RApp ctx f arg E.ahv-other veq eq argIH fInferIH argCheckIH dγ k =
  agree-RApp-other-aux f arg (E.classifyAppHead f) refl eq fInferIH argCheckIH dγ k

-- RAnnot infers by CHECKING `e` against the annotation `T₀`; witness is
-- `t-annot witness`, se is the check-elaborated `eE`, and
-- `realize-infer (t-annot witness) = realize witness`, so agreement IS the
-- supplied `check-agreeV ctx e T₀` IH. A check failure makes the eq absurd.
agree-RAnnot : ∀ {ctx : NamedCtx} {e : RawExpr} {T₀ : Type} {A Ψ}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f} {w : ctx ⊢ᵢ Raw.RAnnot e T₀ ∶ A ⨾ Ψ}
  (r : VerifiedCheckResult ctx e T₀)
  → E.inferElabV-RAnnot-aux ctx e T₀ r ≡ (success A Ψ se d f , w)
  → (∀ {Ψ' eE' d' fr' w'} → r ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize w' ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w ⟧ˢ fmt dγ k
agree-RAnnot (success Ψ' eE' d' fr' , witness) refl IH dγ k = IH refl dγ k
agree-RAnnot (failure _ , _) () IH

------------------------------------------------------------------------
-- `checkG-realize` (`m ≡ realize-global gd`) now lives in Once.TypeCheck.
-- Completeness (moved there for the const-morph-strong value-lift discharge);
-- imported above and reused here for the check-mode value-lift agree cases.

------------------------------------------------------------------------
-- morph-realize (consumed by the RApp morph-lift cases below): the IR
-- `extract-morph-eff` reads off the elaborated morphism expr equals
-- `realize-morph` of the witness's `extractMorphWitness`. DISCHARGED via
-- `morph-elab` (whose strengthened `StrongElab` carries `m ≡ realize-morph mᵐ`)
-- + checkElabV determinism: matching `ce`/`ce'` against the shared `checkElabV`
-- value unifies our (E, W) with morph-elab's; `just`-injectivity on the extract
-- equations then identifies m/mᵐ with morph-elab's, and `cons'` closes it.
morph-realize : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {π : Purity}
    {E : Expr (NamedCtx.debruijn ctx) Surface.zeroUsage (A ⇒[ mk-kind Many π ] B)} {d fr : ℕ}
    {W : ctx ⊢ᶜ e ∶ (A ⇒[ mk-kind Many π ] B) ⨾ Surface.zeroUsage}
    {m : IR ⌊ A ⌋ ⌊ B ⌋} {mᵐ : ctx ⊢ᵐ e ∶ A ⇨[ π ] B}
  → E.checkElabV ctx e (A ⇒[ mk-kind Many π ] B) ≡ (success Surface.zeroUsage E d fr , W)
  → E.extract-morph-eff E ≡ just (m , refl)
  → extractMorphWitness W ≡ just mᵐ
  → m ≡ realize-morph mᵐ
morph-realize {ctx = ctx} {e = e} {A = A} {B = B} {π = π} {mᵐ = mᵐ} ce ex exw
  with morph-elab mᵐ
... | (m' , mᵐ' , E' , d' , fr' , W' , ce' , ex' , exw' , cons')
      with E.checkElabV ctx e (A ⇒[ mk-kind Many π ] B) | ce | ce'
...     | _ | refl | refl =
          trans (cong proj₁ (just-injective (trans (sym ex) ex')))
            (trans cons' (cong realize-morph (sym (just-injective (trans (sym exw) exw')))))

-- compose helper: mirror `checkComposeGo` with `composeMid`'s result `mid` and
-- `eqB` as EXPLICIT parameters (so the `t-morph-lift (m-compose eqB …)` witness's
-- `eqB` is a parameter, not a `with`-generalized scrutinee that would clash with
-- the witness implicit). `just B` ⇒ both arms checked + rewritten via morph-realize.
agree-compose : ∀ (ctx : NamedCtx) (f_inner arg : RawExpr) (A C : Type) (π : Purity)
  (mid : Maybe Type) (eqB : composeMid ctx f_inner arg A ≡ mid)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ (A ⇒[ mk-kind Many π ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RVar "compose") f_inner) arg ∶ (A ⇒[ mk-kind Many π ] C) ⨾ Ψ}
  → E.checkComposeGo ctx f_inner arg A C π mid eqB ≡ (success Ψ se d fr , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-compose ctx f_inner arg A C π nothing eqB ()
agree-compose ctx f_inner arg A C π (just B) eqB disp dγ k
  with E.checkElabV ctx arg (A ⇒[ mk-kind Many π ] B) in eqg | disp
... | failure _ , _ | ()
... | success Ψg gE dg frg , wG | disp'
      with E.checkElabV ctx f_inner (B ⇒[ mk-kind Many π ] C) in eqf | disp'
...   | failure _ , _ | ()
...   | success Ψf fE df frf , wF | disp''
        with E.extract-morph-eff fE in exf | E.extract-morph-eff gE in exg | extractMorphWitness wF in exwf | extractMorphWitness wG in exwg | disp''
...     | just (m_f , refl) | just (m_g , refl) | just mFᵐ | just mGᵐ | refl
          rewrite morph-realize eqf exf exwf | morph-realize eqg exg exwg = refl
...     | nothing | _ | _ | _ | ()
...     | just _  | nothing | _ | _ | ()
...     | just _  | just _  | nothing | _ | ()
...     | just _  | just _  | just _  | nothing | ()

-- Plan 0.52 (pure⊑eff): the `case` analogue of `agree-compose`, reasoning over
-- `checkCaseGo` (grade-poly, no clause-split) so it is immune to the eff-clause.
agree-caseGo : ∀ (ctx : NamedCtx) (f_inner arg : RawExpr) (A B C : Type) (π : Purity)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ ((A + B) ⇒[ mk-kind Many π ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RVar "case") f_inner) arg ∶ ((A + B) ⇒[ mk-kind Many π ] C) ⨾ Ψ}
  → E.checkCaseGo ctx f_inner arg A B C π ≡ (success Ψ se d fr , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-caseGo ctx f_inner arg A B C π disp dγ k
  with E.checkElabV ctx f_inner (A ⇒[ mk-kind Many π ] C) in eqf | disp
... | failure _ , _ | ()
... | success Ψf fE df frf , wF | disp'
      with E.checkElabV ctx arg (B ⇒[ mk-kind Many π ] C) in eqg | disp'
...   | failure _ , _ | ()
...   | success Ψg gE dg frg , wG | disp''
        with E.extract-morph-eff fE in exf | E.extract-morph-eff gE in exg | extractMorphWitness wF in exwf | extractMorphWitness wG in exwg | disp''
...     | just (m_f , refl) | just (m_g , refl) | just mFᵐ | just mGᵐ | refl
          rewrite morph-realize eqf exf exwf | morph-realize eqg exg exwg = refl
...     | nothing | _ | _ | _ | ()
...     | just _  | nothing | _ | _ | ()
...     | just _  | just _  | nothing | _ | ()
...     | just _  | just _  | just _  | nothing | ()

-- eff-clause agreement for compose/case. Mirror the elaborator's eff-clause:
-- the genuinely-eff Go succeeds (passthrough ⇒ delegate at eff), OR the pure
-- fallback wraps in arr'/t-subsume — and since `⟦arr' x⟧ = ⟦x⟧` and `realize
-- (t-subsume w) = arr' (realize w)` (both definitional), the subsumed goal
-- reduces to the pure Go agreement.
agree-compose-eff : ∀ (ctx : NamedCtx) (f_inner arg : RawExpr) (A C : Type)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ (A ⇒[ mk-kind Many eff ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RVar "compose") f_inner) arg ∶ (A ⇒[ mk-kind Many eff ] C) ⨾ Ψ}
  → E.checkCompose ctx (Raw.RApp (Raw.RVar "compose") f_inner) arg (A ⇒[ mk-kind Many eff ] C)
      ≡ (success Ψ se d fr , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-compose-eff ctx f_inner arg A C disp dγ k
  with E.checkComposeGo ctx f_inner arg A C eff (composeMid ctx f_inner arg A) refl in eqEff | disp
... | success Ψe eEe de fre , we | refl =
      agree-compose ctx f_inner arg A C eff (composeMid ctx f_inner arg A) refl eqEff dγ k
... | failure _ , _ | disp'
      with E.checkComposeGo ctx f_inner arg A C pure (composeMid ctx f_inner arg A) refl in eqPure | disp'
...   | success Ψp eEp dp frp , wp | refl =
        agree-compose ctx f_inner arg A C pure (composeMid ctx f_inner arg A) refl eqPure dγ k
...   | failure _ , _ | ()

agree-caseGo-eff : ∀ (ctx : NamedCtx) (f_inner arg : RawExpr) (A B C : Type)
  {Ψ : Usage (NamedCtx.size ctx)} {se : Expr (NamedCtx.debruijn ctx) Ψ ((A + B) ⇒[ mk-kind Many eff ] C)}
  {d fr : ℕ} {w : ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RVar "case") f_inner) arg ∶ ((A + B) ⇒[ mk-kind Many eff ] C) ⨾ Ψ}
  → E.checkCase ctx (Raw.RApp (Raw.RVar "case") f_inner) arg ((A + B) ⇒[ mk-kind Many eff ] C)
      ≡ (success Ψ se d fr , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-caseGo-eff ctx f_inner arg A B C disp dγ k
  with E.checkCaseGo ctx f_inner arg A B C eff in eqEff | disp
... | success Ψe eEe de fre , we | refl =
      agree-caseGo ctx f_inner arg A B C eff eqEff dγ k
... | failure _ , _ | disp'
      with E.checkCaseGo ctx f_inner arg A B C pure in eqPure | disp'
...   | success Ψp eEp dp frp , wp | refl =
        agree-caseGo ctx f_inner arg A B C pure eqPure dγ k
...   | failure _ , _ | ()

------------------------------------------------------------------------
-- Companion of `checkElabV-RApp-other-argdriven-aux` (the `ahv-other`
-- infer-failure fallback). `lhs`/`eqAH` are explicit so the dispatch reduces
-- (`just _` ⇒ elaborator failed ⇒ success-eq absurd). On `nothing`: `arg` is
-- inferred, `f` is CHECKED at `X ⇒[Many,pure] T`, `se = app fE argE`, and
-- `realize (t-arg-driven-app-check _ wArg wF) = app (realize wF)
-- (realize-infer wArg)` — the SAME shape ⇒ application congruence (`fCheckIH`
-- on the function, `argInferIH` on the argument; nested `bind2-faithful`).
agree-check-RApp-argdriven-aux : ∀ {ctx : NamedCtx} (f arg : RawExpr) (T : Type)
  (errInfer : E.TypeError) {Ψ se d fr w}
  (lhs : Maybe E.PolyBuiltinApp) (eqAH : E.classifyAppHead f ≡ lhs)
  → E.checkElabV-RApp-other-argdriven-aux ctx f arg T errInfer lhs eqAH ≡ (success Ψ se d fr , w)
  → (fCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ f ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx f T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize w' ⟧ˢ fmt dγ k)
  → (argInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ arg ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx arg ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-check-RApp-argdriven-aux f arg T errInfer (just _) eqAH () fCheckIH argInferIH
-- Plan 0.52: dispatch on classifyEffArrow (mirrors the elaborator). Both the
-- eff branch (f at pure codomain, se = arr'(app …), arr' transparent) and the
-- plain branch give the SAME application congruence.
agree-check-RApp-argdriven-aux {ctx} f arg T errInfer nothing eqAH eq fCheckIH argInferIH dγ k
  with E.inferElabV ctx arg | eq
... | failure _ , _ | ()
... | success X Ψx argE dx frx , wArg | eq₁ with E.classifyEffArrow T
...   | E.eav-eff A B
        with E.checkElabV ctx f (X ⇒[ mk-kind Many pure ] (A ⇒[ mk-kind Many pure ] B)) in feq2 | eq₁
...     | failure _ , _ | ()
...     | success Ψf fE df frf , wF | refl =
          bind2-faithful (SD.⟦ fE ⟧ˢ fmt dγ) (SD.⟦ realize wF ⟧ˢ fmt dγ)
            (λ vf → SD.⟦ argE ⟧ˢ fmt dγ >>=T λ vx → vf vx)
            (λ vf → SD.⟦ realize-infer wArg ⟧ˢ fmt dγ >>=T λ vx → vf vx)
            (λ j → fCheckIH feq2 dγ j)
            (λ vf j → bind2-faithful (SD.⟦ argE ⟧ˢ fmt dγ) (SD.⟦ realize-infer wArg ⟧ˢ fmt dγ)
                        (λ vx → vf vx) (λ vx → vf vx)
                        (λ j' → argInferIH refl dγ j') (λ _ _ → refl) j)
            k
agree-check-RApp-argdriven-aux {ctx} f arg T errInfer nothing eqAH eq fCheckIH argInferIH dγ k
  | success X Ψx argE dx frx , wArg | eq₁ | E.eav-other _
        with E.checkElabV ctx f (X ⇒[ mk-kind Many pure ] T) in feq2 | eq₁
...     | failure _ , _ | ()
...     | success Ψf fE df frf , wF | refl =
          bind2-faithful (SD.⟦ fE ⟧ˢ fmt dγ) (SD.⟦ realize wF ⟧ˢ fmt dγ)
            (λ vf → SD.⟦ argE ⟧ˢ fmt dγ >>=T λ vx → vf vx)
            (λ vf → SD.⟦ realize-infer wArg ⟧ˢ fmt dγ >>=T λ vx → vf vx)
            (λ j → fCheckIH feq2 dγ j)
            (λ vf j → bind2-faithful (SD.⟦ argE ⟧ˢ fmt dγ) (SD.⟦ realize-infer wArg ⟧ˢ fmt dγ)
                        (λ vx → vf vx) (λ vx → vf vx)
                        (λ j' → argInferIH refl dγ j') (λ _ _ → refl) j)
            k

------------------------------------------------------------------------
-- check-mode RApp agreement, dispatched on the app-head VIEW (a parameter of
-- `checkElabV-RApp-dispatch`). The `t-embed` views (id/fst/snd/terminal) infer
-- `RApp f arg`, match `T`, and delegate to the supplied infer IH (since
-- `realize (t-embed w) = realize-infer w`). The arg-driven `ahv-other` failure
-- branch rides `agree-check-RApp-argdriven-aux`; the morphism-emitting views
-- (In/curry/pair/case/compose/cata) ride the output-driven morphism bridges.
-- Plan 0.52 M1: the agreement mirror of `embedOrSubsume-no` (the `T ≟T T'` = no
-- recovery at every infer-then-check site). When the inferred pure arrow `T'`
-- subsumes to the expected eff arrow `T`, the elaborator emits `arr' eE` with
-- `t-subsume (t-embed w)`; since `⟦arr' f⟧ = ⟦f⟧` and `realize (t-subsume …)`
-- re-wraps in `arr'`, the agreement is EXACTLY the inferred-expr IH (`iIH`).
-- Every non-subsuming shape makes `embedOrSubsume-no` fail ⇒ success-eq absurd.
agree-embedOrSubsume-no : ∀ {ctx : NamedCtx} {e : RawExpr} (T' T : Type)
    {Ψ : Surface.Usage (NamedCtx.size ctx)}
    (eE : Expr (NamedCtx.debruijn ctx) Ψ T') (d fr : ℕ) (wᵢ : ctx ⊢ᵢ e ∶ T' ⨾ Ψ)
    {Ψ' se d' fr'} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ'}
  → E.embedOrSubsume-no ctx e T' T eE d fr wᵢ ≡ (success Ψ' se d' fr' , w)
  → (iIH : ∀ dγ k → SD.⟦ eE ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer wᵢ ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (A ⇒[ mk-kind Many eff ] B) eE d fr wᵢ eq iIH dγ k
  with A E.≟T A' | B E.≟T B' | eq
... | yes refl | yes refl | refl = iIH dγ k
... | yes refl | no _     | ()
... | no _     | _        | ()
agree-embedOrSubsume-no Unit                          T eE d fr wᵢ () iIH
agree-embedOrSubsume-no Void                          T eE d fr wᵢ () iIH
agree-embedOrSubsume-no Int                           T eE d fr wᵢ () iIH
agree-embedOrSubsume-no Float                         T eE d fr wᵢ () iIH
agree-embedOrSubsume-no Str                           T eE d fr wᵢ () iIH
agree-embedOrSubsume-no Buffer                        T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (_ * _)                       T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (_ + _)                       T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (μ-type _)                    T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (ν-type _)                    T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (_ ⇒[ mk-kind Many eff ] _)   T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (_ ⇒[ mk-kind One _ ] _)      T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (_ ⇒[ mk-kind Zero _ ] _)     T eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') Unit                          eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') Void                          eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') Int                           eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') Float                         eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') Str                           eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') Buffer                        eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (_ * _)                       eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (_ + _)                       eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (μ-type _)                    eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (ν-type _)                    eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (_ ⇒[ mk-kind Many pure ] _)  eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (_ ⇒[ mk-kind One _ ] _)      eE d fr wᵢ () iIH
agree-embedOrSubsume-no (A' ⇒[ mk-kind Many pure ] B') (_ ⇒[ mk-kind Zero _ ] _)     eE d fr wᵢ () iIH

-- The agreement for the WHOLE `embedOrSubsume` combinator (every infer-then-check
-- site = `embedOrSubsume ctx e T (inferElabV ctx e)`). Embed (`T ≟T T'` = yes):
-- `t-embed`, so the agreement IS the infer IH; subsume (no): `agree-embedOrSubsume-no`
-- (identity via `arr'`); failure: success-eq absurd. One lemma → every catch-all
-- check-agree clause is a one-liner, with NO proof-side `with T ≟T T'` alignment.
-- PLAN 0.73 F3: the infer result is a PARAMETER, `rInf`, not fixed to
-- `E.inferElabV ctx e`.
--
-- The neg dispatch is why. A proof that has with-abstracted `negOperandView e`
-- can no longer reduce `inferElabV ctx (RUnaryOp OpNeg e)` — that unfolds back
-- into the view, which is stuck under the abstraction — but it CAN name the
-- form the view already reduced to. `agree-RUnaryOp` was stated this way from
-- the start, over `inferElabV-RUnaryOp-aux ctx e rE`; this brings the
-- check-mode lemma into line so both can be used in the same branch.
--
-- Matching `rInf` directly rather than `with`-ing it is what keeps the two
-- ends definitionally connected at the call site.
agree-embedOrSubsume-at : ∀ {ctx : NamedCtx} {e : RawExpr} (T : Type)
    (rInf : VerifiedInferResult ctx e)
    {Ψ se d f} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ}
  → E.embedOrSubsume ctx e T rInf ≡ (success Ψ se d f , w)
  → (inferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ e ∶ T' ⨾ Ψ'}
       → rInf ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-embedOrSubsume-at T (failure _ , _) () inferIH
agree-embedOrSubsume-at T (success T' Ψ' eE' d' fr' , wᵢ) eq inferIH dγ k
  with T E.≟T T' | eq
... | yes refl | refl = inferIH refl dγ k
... | no _     | eq₂ =
      agree-embedOrSubsume-no T' T eE' d' fr' wᵢ eq₂ (λ dγ' k' → inferIH refl dγ' k') dγ k

agree-embedOrSubsume : ∀ {ctx : NamedCtx} {e : RawExpr} (T : Type)
    {Ψ se d f} {w : ctx ⊢ᶜ e ∶ T ⨾ Ψ}
  → E.embedOrSubsume ctx e T (E.inferElabV ctx e) ≡ (success Ψ se d f , w)
  → (inferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ e ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx e ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-embedOrSubsume {ctx = ctx} {e = e} T eq inferIH dγ k =
  agree-embedOrSubsume-at T (E.inferElabV ctx e) eq inferIH dγ k

-- Plan 0.55 D#2: the SINGLE genuinely-hard leaf of the "recurse on OUTPUT"
-- redesign — the cata denotational bridge. `⟦ Surface.cata wfF algE ⟧ˢ` folds via
-- `sem-cata` over `cata-ev-algˢ n (⟦algE⟧ˢ tt)`; `⟦ lift-morphism (IR.Cata wfF
-- m-alg) ⟧ˢ = returnT (evalᴰ (Cata wfF m-alg))` folds via `sem-cata` over
-- `cata-ev-algᴰ n m-alg`. Given the algebra extracts (`⟦algE⟧ˢ tt ≡ returnT (evalᴰ
-- m-alg)` by the algebra's own faithfulness), the two `cata-ev-alg`s agree by
-- monad-left-identity (`returnT a >>=T f = f a`) + a `sem-cata` algebra-congruence
-- under the fold. NARROW: confined to this one clause (was smeared across the
-- `check-RApp-todo` view catch-all). [[feedback_enumerate_over_catchall_postulate]]
-- Plan 0.58: DISCHARGED. The algebra's SD denotation equals `returnT` of its
-- extracted IR's `evalᴰ` — structural recursion on `algE` (`lift-morphism`
-- definitional, `arr'` transparent, `cata` rides `cata-fold-eq` with the
-- recursively-obtained inner faithfulness; everything else extracts to `nothing`
-- so the hypothesis is absurd).
-- Over `extract-morph-eff-aux` with a GENERAL result type `T` + the `T ≡ A⇒B`
-- equation: `var`'s neutral `lookup Γ i` then unifies with `T` (no split-stuck),
-- and every non-morphism constructor extracts to `nothing` (aux's catch-all) so
-- the hypothesis is absurd. `just` is only produced by `lift-morphism`/`arr'`/
-- `cata`, where `teq` is forced to `refl` (so the `subst` is the identity).
faithful-aux : ∀ {n} {Γ : Surface.Ctx n} {Ψ : Usage n} {RT A B} {π : Purity}
    (E : Expr Γ Ψ RT) (teq : RT ≡ (A ⇒[ mk-kind Many π ] B)) {m : IR ⌊ A ⌋ ⌊ B ⌋} {ψ0 : Ψ ≡ Surface.zeroUsage}
  → E.extract-morph-eff-aux E teq ≡ just (m , ψ0)
  → ∀ (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ)
  → SD.⟦ E ⟧ˢ fmt dγ ≡ subst (λ Ty → T ⟦ Ty ⟧ᴰ) (sym teq) (SD.liftD fmt m)
faithful-aux (Surface.lift-morphism m') refl eq dγ =
  cong (λ mm → SD.liftD fmt mm) (cong proj₁ (just-injective eq))
faithful-aux {Γ = Γ} (Surface.cata wfF' algE') refl eq dγ
  with E.extract-morph-eff algE' in innerEq | eq
... | just (m' , refl) | refl =
      extensionality (λ k → cata-fold-eq {Γ = Γ} wfF' algE' m' (faithful-aux algE' refl innerEq tt) dγ k)
faithful-aux (Surface.var i) teq () dγ
faithful-aux (Surface.arr' e) refl eq dγ = faithful-aux e refl eq dγ
faithful-aux (Surface.lam _ _ _) teq () dγ
faithful-aux (Surface.app _ _) teq () dγ
faithful-aux (Surface.effApp _ _) teq () dγ
faithful-aux (Surface.sigOp _ _) teq () dγ
faithful-aux (Surface.closure _) teq () dγ
faithful-aux (Surface.poly _ _) teq () dγ
faithful-aux (Surface.morph-app _ _) teq () dγ
faithful-aux (Surface.ana _ _) teq () dγ
faithful-aux (Surface.absurd _) teq () dγ
faithful-aux (Surface.fst' _) teq () dγ
faithful-aux (Surface.snd' _) teq () dγ
faithful-aux (Surface.case' _ _ _) teq () dγ

extract-morph-eff-denotes : ∀ {A B} {π : Purity}
    (algE : Expr Surface.∅ Surface.zeroUsage (A ⇒[ mk-kind Many π ] B)) {m : IR ⌊ A ⌋ ⌊ B ⌋}
  → E.extract-morph-eff algE ≡ just (m , refl)
  → SD.⟦ algE ⟧ˢ fmt tt ≡ SD.liftD fmt m
extract-morph-eff-denotes algE eq = faithful-aux algE refl eq tt

agree-cata-denotes : ∀ {n} {Γ : Surface.Ctx n} {F : Functor} {A : Type} {π : Purity}
    {wfF : WellFormedF F}
    {algE : Expr Surface.∅ Surface.zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A)}
    {m-alg : IR ⌊ ⟦ F ⟧T A ⌋ ⌊ A ⌋}
  → E.extract-morph-eff algE ≡ just (m-alg , refl)
  → ∀ (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ Surface.cata {Γ = Γ} wfF algE ⟧ˢ fmt dγ k
      ≡ SD.⟦ Surface.lift-morphism {Γ = Γ} {π = π} (IR.Cata (wf-⌊⌋ wfF) (subst (λ o → IR o ⌊ A ⌋) (⌊⟧T-commute F A) m-alg)) ⟧ˢ fmt dγ k
agree-cata-denotes {Γ = Γ} {wfF = wfF} {algE = algE} {m-alg = m-alg} eq dγ k =
  cata-fold-eq {Γ = Γ} wfF algE m-alg (extract-morph-eff-denotes algE eq) dγ k

-- morph-realize enriched to ALSO return the `extract-morph-eff` equation (needed to
-- feed `agree-cata-denotes`). Same `morph-elab` + checkElabV-determinism derivation
-- as `morph-realize`, but exposes the elaborated morphism `m` with BOTH its extract
-- equation and `m ≡ realize-morph mᵐ`.
algebra-morph-recover : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {π : Purity}
    {E : Expr (NamedCtx.debruijn ctx) Surface.zeroUsage (A ⇒[ mk-kind Many π ] B)} {d fr : ℕ}
    {W : ctx ⊢ᶜ e ∶ (A ⇒[ mk-kind Many π ] B) ⨾ Surface.zeroUsage}
    {mᵐ : ctx ⊢ᵐ e ∶ A ⇨[ π ] B}
  → E.checkElabV ctx e (A ⇒[ mk-kind Many π ] B) ≡ (success Surface.zeroUsage E d fr , W)
  → extractMorphWitness W ≡ just mᵐ
  → ∃-syntax (λ (m : IR ⌊ A ⌋ ⌊ B ⌋) → (E.extract-morph-eff E ≡ just (m , refl)) × (m ≡ realize-morph mᵐ))
algebra-morph-recover {ctx = ctx} {e = e} {A = A} {B = B} {π = π} {mᵐ = mᵐ} ce exw
  with morph-elab mᵐ
... | (m' , mᵐ' , E' , d' , fr' , W' , ce' , ex' , exw' , cons')
      with E.checkElabV ctx e (A ⇒[ mk-kind Many π ] B) | ce | ce'
...     | _ | refl | refl =
          m' , ex'
             , trans cons' (cong realize-morph
                 (sym (just-injective (trans (sym exw) exw'))))

-- Plan 0.55 D#2: bare-`μF` `In` agreement over `checkInGo` (`mw`/`eqW` explicit to
-- dodge the `wellFormedF? F` dependent-`with`, as for cata). Emits `morph-app (In
-- wfF Heap) argE`; `realize (t-In-app-check _ wArg) = morph-app (In wfF Heap)
-- (realize wArg)` — SAME morph-app congruence as `ahv-initial` (rewrite arg IH).
agree-checkInGo : ∀ (ctx : NamedCtx) (arg : RawExpr) (F : Functor)
    (mw : Maybe (WellFormedF F)) (eqW : wellFormedF? F ≡ mw)
    {Ψ : Usage (NamedCtx.size ctx)}
    {se : Expr (NamedCtx.debruijn ctx) Ψ (μ-type F)}
    {d fr : ℕ}
    {w : ctx ⊢ᶜ Raw.RApp (Raw.RVar "In") arg ∶ μ-type F ⨾ Ψ}
  → E.checkInGo ctx arg F mw eqW ≡ (success Ψ se d fr , w)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize w' ⟧ˢ fmt dγ k)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-checkInGo ctx arg F nothing eqW ()
agree-checkInGo ctx arg F (just wfF) eqW disp argCheckIH dγ k
  with E.checkElabV ctx arg (⟦ F ⟧T (μ-type F)) in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , wArg | refl rewrite argCheckIH aeq dγ k = refl

-- Plan 0.55 D#2: the cata agreement over `checkCataGo` (mirrors `agree-caseGo` /
-- `agree-compose`). `mw`/`eqW` are EXPLICIT so `checkCataGo` reduces on `just wfF`
-- WITHOUT the `wellFormedF? F` dependent-`with` hazard (the same device as
-- `checkCataGoV-pure-J`). The lone success leaf is the cata denotational bridge
-- (`agree-cata-denotes`) composed with the algebra's `extract ≡ realize-morph`
-- (`algebra-morph-recover`); `realize (t-morph-lift (m-cata _ mᵐ)) = lift-morphism
-- (IR.Cata wfF (realize-morph mᵐ))` is definitional (Realize:124/135).
agree-checkCataGo : ∀ (ctx : NamedCtx) (alg : RawExpr) (F : Functor) (A : Type) (π : Purity)
    (mw : Maybe (WellFormedF F)) (eqW : wellFormedF? F ≡ mw)
    {Ψ : Usage (NamedCtx.size ctx)}
    {se : Expr (NamedCtx.debruijn ctx) Ψ (μ-type F ⇒[ mk-kind Many π ] A)}
    {d fr : ℕ}
    {w : ctx ⊢ᶜ Raw.RApp (Raw.RVar "cata") alg ∶ (μ-type F ⇒[ mk-kind Many π ] A) ⨾ Ψ}
  → E.checkCataGo ctx alg F A π mw eqW ≡ (success Ψ se d fr , w)
  → ∀ (dγ : Env ctx) (k : ℕ) → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-checkCataGo ctx alg F A π nothing eqW ()
agree-checkCataGo ctx alg F A π (just wfF) eqW disp dγ k
  with E.checkElabV (ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx))
                    alg (⟦ F ⟧T A ⇒[ mk-kind Many π ] A) in eqAlg | disp
... | failure _ , _ | ()
... | success Surface.[] algE dA frA , wArg | disp₁
      with extractMorphWitness wArg in exw | disp₁
...   | nothing | ()
...   | just mᵐ | refl
        with algebra-morph-recover eqAlg exw
...     | (m-alg , exEff , eqRealize) =
          trans (agree-cata-denotes {Γ = NamedCtx.debruijn ctx} {wfF = wfF} {algE = algE} exEff dγ k)
                (cong (λ z → SD.⟦ Surface.lift-morphism {Γ = NamedCtx.debruijn ctx} {π = π} (IR.Cata (wf-⌊⌋ wfF) (subst (λ o → IR o ⌊ A ⌋) (⌊⟧T-commute F A) z)) ⟧ˢ fmt dγ k) eqRealize)

agree-check-RApp : ∀ (ctx : NamedCtx) (f arg : RawExpr) (T : Type) {Ψ se d fr w}
  (vw : E.AppHeadView f) (veq : E.classifyAppHeadView f ≡ vw)
  → E.checkElabV-RApp-dispatch ctx f arg T vw veq ≡ (success Ψ se d fr , w)
  → (inferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ Raw.RApp f arg ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx (Raw.RApp f arg) ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  → (argCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ arg ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx arg T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize w' ⟧ˢ fmt dγ k)
  → (argInferIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᵢ arg ∶ T' ⨾ Ψ'}
       → E.inferElabV ctx arg ≡ (success T' Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize-infer w' ⟧ˢ fmt dγ k)
  -- check-f IH (only `ahv-other`'s arg-driven path consumes it).
  → (fCheckIH : ∀ {T' Ψ' eE' d' fr'} {w' : ctx ⊢ᶜ f ∶ T' ⨾ Ψ'}
       → E.checkElabV ctx f T' ≡ (success Ψ' eE' d' fr' , w')
       → ∀ dγ k → SD.⟦ eE' ⟧ˢ fmt dγ k ≡ SD.⟦ realize w' ⟧ˢ fmt dγ k)
  → ∀ dγ k → SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize w ⟧ˢ fmt dγ k
agree-check-RApp ctx f arg T E.ahv-id veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T E.≟T T' | eq₁
...   | yes refl | refl = inferIH refl dγ k
...   | no _     | eq₂ = agree-embedOrSubsume-no T' T eE d fr w eq₂ (λ dγ' k' → inferIH refl dγ' k') dγ k
agree-check-RApp ctx f arg T E.ahv-fst veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T E.≟T T' | eq₁
...   | yes refl | refl = inferIH refl dγ k
...   | no _     | eq₂ = agree-embedOrSubsume-no T' T eE d fr w eq₂ (λ dγ' k' → inferIH refl dγ' k') dγ k
agree-check-RApp ctx f arg T E.ahv-snd veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T E.≟T T' | eq₁
...   | yes refl | refl = inferIH refl dγ k
...   | no _     | eq₂ = agree-embedOrSubsume-no T' T eE d fr w eq₂ (λ dγ' k' → inferIH refl dγ' k') dγ k
agree-check-RApp ctx f arg T E.ahv-terminal veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | failure _ , _ | ()
... | success T' Ψ eE d fr , w | eq₁ with T E.≟T T' | eq₁
...   | yes refl | refl = inferIH refl dγ k
...   | no _     | eq₂ = agree-embedOrSubsume-no T' T eE d fr w eq₂ (λ dγ' k' → inferIH refl dγ' k') dγ k
-- ahv-initial: arg checked at Void; se = morph-app initial argE (unary >>=T),
-- witness t-initial-app-check w, realize = morph-app initial (realize w) ⇒
-- rewrite the arg check IH.
agree-check-RApp ctx f arg T E.ahv-initial veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkElabV ctx arg Void in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | refl rewrite argCheckIH aeq dγ k = refl
-- (Plan 0.52 M1: `ahv-arr` check-agree clauses retired with the surface `arr` builtin.)
-- ahv-inl/inr: direct sum target → morph-app (inl/inr Heap) argE (rewrite arg
-- check IH); pure-arrow→sum target → value-lift via checkG (rewrite checkG-realize).
-- ahv-In: arrow→μ target → value-lift via checkG; bare μ target → morph-app In.
-- All other targets make the dispatch fail ⇒ Agda prunes them via `disp` clash.
agree-check-RApp ctx f arg (A + B) E.ahv-inl veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkElabV ctx arg A in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | refl rewrite argCheckIH aeq dγ k = refl
agree-check-RApp ctx f arg (X ⇒[ mk-kind Many π ] (A + B)) E.ahv-inl veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inspectCheckG ctx X (Raw.RApp (Raw.RVar "inl") arg) (A + B) | disp
... | E.cgv-nothing _ | ()
... | E.cgv-just {m} {gd} cgeq | refl rewrite checkG-realize gd cgeq = refl
agree-check-RApp ctx f arg (A + B) E.ahv-inr veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkElabV ctx arg B in aeq | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | refl rewrite argCheckIH aeq dγ k = refl
agree-check-RApp ctx f arg (X ⇒[ mk-kind Many π ] (A + B)) E.ahv-inr veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inspectCheckG ctx X (Raw.RApp (Raw.RVar "inr") arg) (A + B) | disp
... | E.cgv-nothing _ | ()
... | E.cgv-just {m} {gd} cgeq | refl rewrite checkG-realize gd cgeq = refl
agree-check-RApp ctx f arg (X ⇒[ mk-kind Many π ] (μ-type F)) E.ahv-In veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inspectCheckG ctx X (Raw.RApp (Raw.RVar "In") arg) (μ-type F) | disp
... | E.cgv-nothing _ | ()
... | E.cgv-just {m} {gd} cgeq | refl rewrite checkG-realize gd cgeq = refl
-- ahv-In at a bare `μ-type F` target (Plan 0.55 D#2): checkInGo builds `morph-app
-- (In wfF Heap) argE` — delegate to agree-checkInGo (arg-check congruence).
agree-check-RApp ctx f arg (μ-type F) E.ahv-In veq disp inferIH argCheckIH argInferIH fCheckIH dγ k =
  agree-checkInGo ctx arg F (wellFormedF? F) refl disp argCheckIH dγ k
-- ahv-curry: checkCurry emits `lift-morphism (curry mf Heap)`, witness
-- `t-morph-lift (m-curry mFᵐ)`; `realize` is `lift-morphism (curry
-- (realize-morph mFᵐ) Heap)` — rewrite by the morph-realize bridge (mf ≡
-- realize-morph mFᵐ). Non-arrow-arrow targets ⇒ dispatch fails ⇒ pruned by `disp`.
agree-check-RApp ctx f arg (A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C)) E.ahv-curry veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkElabV ctx arg ((A * B) ⇒[ mk-kind Many pure ] C) in eqarg | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | disp'
      with E.extract-morph-eff argE in exf | extractMorphWitness w in exw | disp'
...   | just (mf , refl) | just mFᵐ | refl rewrite morph-realize eqarg exf exw = refl
...   | just (mf , refl) | nothing  | ()
...   | nothing          | _        | ()
-- ahv-curry at an EFF outer arrow (Plan 0.55 D#2): checkCurry subsumes the pure
-- curry via `arr'`/`t-subsume`. `⟦arr' x⟧ = ⟦x⟧` and `realize (t-subsume w) = arr'
-- (realize w)` are transparent, so this is the SAME morph-realize rewrite as pure.
agree-check-RApp ctx f arg (A ⇒[ mk-kind Many eff ] (B ⇒[ mk-kind Many pure ] C)) E.ahv-curry veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkElabV ctx arg ((A * B) ⇒[ mk-kind Many pure ] C) in eqarg | disp
... | failure _ , _ | ()
... | success Ψ argE d fr , w | disp'
      with E.extract-morph-eff argE in exf | extractMorphWitness w in exw | disp'
...   | just (mf , refl) | just mFᵐ | refl rewrite morph-realize eqarg exf exw = refl
...   | just (mf , refl) | nothing  | ()
...   | nothing          | _        | ()
-- ahv-pair-applied: checkPair emits `lift-morphism ⟨mf,mg⟩`, witness
-- `t-morph-lift (m-pair mFᵐ mGᵐ)`; rewrite by morph-realize on BOTH components.
agree-check-RApp ctx (Raw.RApp (Raw.RVar "pair") f_inner) arg (A ⇒[ mk-kind Many pure ] (B * C)) E.ahv-pair-applied veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkElabV ctx f_inner (A ⇒[ mk-kind Many pure ] B) in eqf | disp
... | failure _ , _ | ()
... | success Ψf fE df frf , wF | disp'
      with E.checkElabV ctx arg (A ⇒[ mk-kind Many pure ] C) in eqg | disp'
...   | failure _ , _ | ()
...   | success Ψg gE dg frg , wG | disp''
        with E.extract-morph-eff fE in exf | E.extract-morph-eff gE in exg | extractMorphWitness wF in exwf | extractMorphWitness wG in exwg | disp''
...     | just (mf , refl) | just (mg , refl) | just mFᵐ | just mGᵐ | refl
          rewrite morph-realize eqf exf exwf | morph-realize eqg exg exwg = refl
...     | nothing | _ | _ | _ | ()
...     | just _  | nothing | _ | _ | ()
...     | just _  | just _  | nothing | _ | ()
...     | just _  | just _  | just _  | nothing | ()
-- ahv-pair-applied at an EFF outer arrow (Plan 0.55 D#2): checkPair subsumes the
-- pure pair via `arr'`/`t-subsume` (both transparent) — SAME morph-realize rewrite.
agree-check-RApp ctx (Raw.RApp (Raw.RVar "pair") f_inner) arg (A ⇒[ mk-kind Many eff ] (B * C)) E.ahv-pair-applied veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkElabV ctx f_inner (A ⇒[ mk-kind Many pure ] B) in eqf | disp
... | failure _ , _ | ()
... | success Ψf fE df frf , wF | disp'
      with E.checkElabV ctx arg (A ⇒[ mk-kind Many pure ] C) in eqg | disp'
...   | failure _ , _ | ()
...   | success Ψg gE dg frg , wG | disp''
        with E.extract-morph-eff fE in exf | E.extract-morph-eff gE in exg | extractMorphWitness wF in exwf | extractMorphWitness wG in exwg | disp''
...     | just (mf , refl) | just (mg , refl) | just mFᵐ | just mGᵐ | refl
          rewrite morph-realize eqf exf exwf | morph-realize eqg exg exwg = refl
...     | nothing | _ | _ | _ | ()
...     | just _  | nothing | _ | _ | ()
...     | just _  | just _  | nothing | _ | ()
...     | just _  | just _  | just _  | nothing | ()
-- ahv-case-applied: checkCase emits `lift-morphism (case m_f m_g)`, witness
-- `t-morph-lift (m-case mFᵐ mGᵐ)`; rewrite both components.
-- Plan 0.52: case π (checkCase now has a separate eff-clause, so it no longer
-- reduces at abstract π). pure → checkCaseGo directly (agree-caseGo); eff → the
-- eff-clause (agree-caseGo-eff: passthrough or subsumed-pure).
agree-check-RApp ctx (Raw.RApp (Raw.RVar "case") f_inner) arg ((A + B) ⇒[ mk-kind Many pure ] C) E.ahv-case-applied veq disp inferIH argCheckIH argInferIH fCheckIH dγ k =
  agree-caseGo ctx f_inner arg A B C pure disp dγ k
agree-check-RApp ctx (Raw.RApp (Raw.RVar "case") f_inner) arg ((A + B) ⇒[ mk-kind Many eff ] C) E.ahv-case-applied veq disp inferIH argCheckIH argInferIH fCheckIH dγ k =
  agree-caseGo-eff ctx f_inner arg A B C disp dγ k
-- ahv-compose-applied: delegate to agree-compose (mirrors checkCompose →
-- checkComposeGo with composeMid + eqB explicit).
-- Plan 0.52: case π (as for `case`). pure → agree-compose over checkComposeGo;
-- eff → agree-compose-eff (the eff-clause: passthrough or subsumed-pure).
agree-check-RApp ctx (Raw.RApp (Raw.RVar "compose") f_inner) arg (A ⇒[ mk-kind Many pure ] C) E.ahv-compose-applied veq disp inferIH argCheckIH argInferIH fCheckIH dγ k =
  agree-compose ctx f_inner arg A C pure (composeMid ctx f_inner arg A) refl disp dγ k
agree-check-RApp ctx (Raw.RApp (Raw.RVar "compose") f_inner) arg (A ⇒[ mk-kind Many eff ] C) E.ahv-compose-applied veq disp inferIH argCheckIH argInferIH fCheckIH dγ k =
  agree-compose-eff ctx f_inner arg A C disp dγ k
-- ahv-apply (check): checkApply infers the arg; se = morph-app apply argE,
-- witness t-apply-check w, realize = morph-app apply (realize-infer w) ⇒ plain
-- morph-app congruence via the inferred-arg IH. Non-`(Many-pure-arrow * A)` args fail.
-- Plan 0.52: `apply p` now routes its check through the named embedOrSubsume
-- (infer the whole app, embed at T or subsume) — identical shape to ahv-other.
agree-check-RApp ctx f arg T E.ahv-apply veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | success T' Ψ eE d fr , w | eq₁ with T E.≟T T' | eq₁
...   | yes refl | refl = inferIH refl dγ k
...   | no _     | eq₂ = agree-embedOrSubsume-no T' T eE d fr w eq₂ (λ dγ' k' → inferIH refl dγ' k') dγ k
agree-check-RApp ctx f arg T E.ahv-apply veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  | failure _ , _ | ()
-- ahv-other (check): the dispatch first tries `inferElabV (RApp f arg)` and on
-- success matches `T` — that is the `t-embed` path (`realize (t-embed w) =
-- realize-infer w` ⇒ the supplied `inferIH`). On infer-failure it falls to the
-- ARG-DRIVEN application: `arg` is inferred, `f` is CHECKED at `X ⇒[Many,pure]
-- T`, and `se = app fE argE` with `realize (t-arg-driven-app-check _ wArg wF) =
-- app (realize wF) (realize-infer wArg)` — the SAME shape. So it is the
-- application congruence again, now with the FUNCTION on `fCheckIH` (f checked)
-- and the ARGUMENT on `argInferIH` (arg inferred). `classifyAppHead f = just _`
-- contradicts ahv-other ⇒ the elaborator fails ⇒ success-eq absurd.
agree-check-RApp ctx f arg T E.ahv-other veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.inferElabV ctx (Raw.RApp f arg) | disp
... | success T' Ψ eE d fr , w | eq₁ with T E.≟T T' | eq₁
...   | yes refl | refl = inferIH refl dγ k
...   | no _     | eq₂ = agree-embedOrSubsume-no T' T eE d fr w eq₂ (λ dγ' k' → inferIH refl dγ' k') dγ k
agree-check-RApp ctx f arg T E.ahv-other veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  | failure errInfer , _ | disp₁ =
    agree-check-RApp-argdriven-aux f arg T errInfer
      (E.classifyAppHead f) refl disp₁ fCheckIH argInferIH dγ k
-- ahv-cata (Plan 0.55 D#2): the elaborated `se` is a `Surface.cata` node (a bare
-- morphism), so drive the agreement by the OUTPUT via `agree-checkCataGo` — no view
-- catch-all. pure: `checkCata` reduces DIRECTLY to `checkCataGo … pure`. eff: the
-- eff clause tries the eff-Go (genuine-eff algebra) then subsumes a pure-Go via
-- `arr'`/`t-subsume`; both `arr'` wrappers are denotationally transparent
-- (`⟦arr' x⟧ = ⟦x⟧`, `realize (t-subsume w) = arr' (realize w)`), so each branch is
-- the corresponding `agree-checkCataGo`.
agree-check-RApp ctx f arg (μ-type F ⇒[ mk-kind Many pure ] A) E.ahv-cata veq disp inferIH argCheckIH argInferIH fCheckIH dγ k =
  agree-checkCataGo ctx arg F A pure (wellFormedF? F) refl disp dγ k
agree-check-RApp ctx f arg (μ-type F ⇒[ mk-kind Many eff ] A) E.ahv-cata veq disp inferIH argCheckIH argInferIH fCheckIH dγ k
  with E.checkCataGo ctx arg F A eff (wellFormedF? F) refl in eqEff | disp
... | success Ψe eEe de fre , we | refl =
      agree-checkCataGo ctx arg F A eff (wellFormedF? F) refl eqEff dγ k
... | failure _ , _ | disp₁
      with E.checkCataGo ctx arg F A pure (wellFormedF? F) refl in eqPure | disp₁
...   | success Ψp eEp dp frp , wp | refl =
        agree-checkCataGo ctx arg F A pure (wellFormedF? F) refl eqPure dγ k
...   | failure _ , _ | ()
-- Plan 0.55 D#2 (catch-all ELIMINATED): no `check-RApp-todo` catch-all. Every
-- (view × target) the dispatch can make SUCCEED now has an explicit agree clause
-- (id/fst/snd/terminal/apply/other via infer-embed; initial/inl/inr via morph-app or
-- checkG value-lift; In/curry/pair/case/compose/cata via the morphism/subsume
-- bridges). Every OTHER (view × target) makes the dispatch reduce to `failure`, so
-- `disp : … ≡ (success …)` is a constructor clash Agda's coverage checker prunes
-- automatically — no absurd (view × target) matrix. [[feedback_recurse_on_output_not_dispatch]]

------------------------------------------------------------------------
-- Well-founded measure for the infer/check mutual recursion. The same-size
-- `check-agreeV e → infer-agreeV e` (the t-embed fallback) together with the
-- strictly-smaller `infer-agreeV (RAnnot e T) → check-agreeV e` make the SCC
-- mutual, and foetus cannot see termination through the `with`-auxes. We make
-- it explicit via `Acc` on a lexicographic measure `(size, phase)` flattened to
-- `μe+μe` (infer, phase 0) / `suc (μe+μe)` (check, phase 1): check→infer at the
-- same `e` drops the phase (strictly <), infer→check is on a strictly smaller
-- subterm, and every other recursive call shrinks the subterm.
μ : RawExpr → ℕ
μ (Raw.RVar _)            = 1
μ (Raw.RQualified _ _)    = 1
μ (Raw.RResolved _)       = 1
μ (Raw.RApp f x)          = suc (μ f +ℕ μ x)
μ (Raw.RLam _ b)          = suc (μ b)
μ (Raw.RLet _ e₁ e₂)      = suc (μ e₁ +ℕ μ e₂)
μ (Raw.RPair a b)         = suc (μ a +ℕ μ b)
μ (Raw.RDestruct s _ l _ r) = suc (μ s +ℕ (μ l +ℕ μ r))
μ Raw.RUnit               = 1
μ (Raw.RInt _)            = 1
μ (Raw.RFloat _ _ _ _)      = 1
μ (Raw.RStringLit _)      = 1
μ (Raw.RAnnot e _)        = suc (μ e)
μ (Raw.RBinOp _ a b)      = suc (μ a +ℕ μ b)
μ (Raw.RUnaryOp _ e)      = suc (μ e)
μ (Raw.RAna _ e)          = suc (μ e)

mInfer mCheck : RawExpr → ℕ
mInfer e = μ e +ℕ μ e
mCheck e = suc (μ e +ℕ μ e)

-- doubling is strictly monotone
dbl-< : ∀ {m n} → m < n → m +ℕ m < n +ℕ n
dbl-< h = +-mono-< h h

-- check-mode strictly dominates infer-mode at the same expression (phase drop)
infer<check : ∀ e → mInfer e < mCheck e
infer<check e = ≤-refl

-- `RAnnot e T` (infer) strictly dominates its checked body `e` (check)
check<infer-annot : ∀ e T → mCheck e < mInfer (Raw.RAnnot e T)
check<infer-annot e T = s≤s (≤-reflexive (sym (+-suc (μ e) (μ e))))

-- check→check on a strictly-smaller subterm: `μ sub < μ par` ⇒
-- `mCheck sub < mCheck par`. Stated over the ℕ measures (NOT the exprs — `μ` is
-- not injective, so expr indices wouldn't infer).
mC-sub : ∀ {m n : ℕ} → m < n → suc (m +ℕ m) < suc (n +ℕ n)
mC-sub h = s≤s (dbl-< h)

-- check→infer on a strictly-smaller subterm: `mInfer sub < mCheck par`.
mIC-sub : ∀ {m n : ℕ} → m < n → m +ℕ m < suc (n +ℕ n)
mIC-sub h = ≤-trans (dbl-< h) (n≤1+n _)

-- infer→check on a strictly-smaller subterm: `mCheck sub < mInfer par`. Used
-- when an INFER node (e.g. `RApp f arg`, ahv-other) drives a CHECK on a child
-- (`checkElabV ctx arg A`). From `m < n` (child μ < parent μ), `suc m + suc m ≤
-- n + n` (+-mono-≤), and `suc m + suc m ≡ suc (suc (m + m))` (+-suc) ⇒ goal.
mCI-sub : ∀ {m n : ℕ} → m < n → suc (m +ℕ m) < n +ℕ n
mCI-sub {m} {n} h = subst (_≤ n +ℕ n) (cong suc (+-suc m m)) (+-mono-≤ h h)

-- generic subterm size bounds (raw ℕ; instantiate with the μ of children)
μ<-l : ∀ a b → a < suc (a +ℕ b)
μ<-l a b = s≤s (m≤m+n a b)
μ<-r : ∀ a b → b < suc (a +ℕ b)
μ<-r a b = s≤s (m≤n+m b a)
μ<-d-s : ∀ s l r → s < suc (s +ℕ (l +ℕ r))
μ<-d-s s l r = s≤s (m≤m+n s (l +ℕ r))
μ<-d-l : ∀ s l r → l < suc (s +ℕ (l +ℕ r))
μ<-d-l s l r = s≤s (≤-trans (m≤m+n l r) (m≤n+m (l +ℕ r) s))
μ<-d-r : ∀ s l r → r < suc (s +ℕ (l +ℕ r))
μ<-d-r s l r = s≤s (≤-trans (m≤n+m r l) (m≤n+m (l +ℕ r) s))

mutual
  infer-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (ac : Acc _<_ (mInfer e)) {A Ψ se d f w}
    (eq : E.inferElabV ctx e ≡ (success A Ψ se d f , w)) → InferAgreeV ctx e eq
  infer-agreeV ctx (Raw.RInt n)       _ refl dγ k = refl
  -- RFloat: K3 removed F4's decision, so there is nothing to name and this is
  -- the `RInt` clause verbatim. The absurd `nothing` branch went with it —
  -- a float literal can no longer fail to elaborate.
  infer-agreeV ctx (Raw.RFloat i f l _) _ refl dγ k = refl
  infer-agreeV ctx (Raw.RStringLit s) _ refl dγ k = refl
  infer-agreeV ctx Raw.RUnit          _ refl dγ k = refl
  -- RPair: with-free — delegate to the top-level `agree-RPair`, passing both
  -- sub-results + sub-IHs (each with a strictly-smaller `Acc` from `rec`).
  infer-agreeV ctx (Raw.RPair a b) (acc rec) eq dγ k =
    agree-RPair (E.inferElabV ctx a) (E.inferElabV ctx b) eq
      (λ p → infer-agreeV ctx a (rec (dbl-< (μ<-l (μ a) (μ b)))) p)
      (λ p → infer-agreeV ctx b (rec (dbl-< (μ<-r (μ a) (μ b)))) p) dγ k
  -- PLAN 0.74 J6 step 3. `- 5` now elaborates to the LITERAL `-5`, while
  -- `realize-infer` still reads `neg (int 5)` off the derivation
  -- `t-neg (t-int 5)` — the derivation is indexed by the RAW expression and
  -- did not change. So the two sides are no longer the same term and
  -- agreement is a real step: `⊝ (fromℤ n) ≡ fromℤ (- n)`.
  --
  -- That `realize-agrees` is stated OBSERVATIONALLY is what makes the fold
  -- affordable. A syntactic `se ≡ realize w` would have forced `realize` to
  -- fold too, and with it every proof that reads the derivation.
  infer-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) (acc rec) eq dγ k
    with E.negOperandView e | eq
  ... | E.nov-int n | refl =
          cong (λ v → (DL.List.[] , v)) (sym (OnceWord.Width.⊝-fromℤ (int-bits fmt) n))
  -- PLAN 0.73 F3. `refl`, and the contrast with the `Int` branch above is the
  -- whole content: there `realize-infer` keeps `neg (int n)` and the two sides
  -- are reconciled by `⊝-fromℤ`; here `Surface.neg` is Int-typed, so the
  -- reference elaboration had no float negation to keep and folded to the same
  -- literal the elaborator produces. Nothing to reconcile — which is also why
  -- this branch checks NOTHING about `round`, and why the pins in
  -- `Once.Float.Decimal` are where that is checked (D117).
  ... | E.nov-float i f l p | refl = refl
  -- NAME the abstracted equation: in this branch its type has already reduced
  -- through `inferElabV-neg-aux … nothing` to the plain aux, which is what
  -- `agree-RUnaryOp` is stated over. The un-refined `eq` has not.
  ... | E.nov-other .e  | eq′ =
          agree-RUnaryOp (E.inferElabV ctx e) eq′
            (λ p → infer-agreeV ctx e (rec (dbl-< ≤-refl)) p) dγ k
  infer-agreeV ctx (Raw.RLet x e₁ e₂) (acc rec) eq dγ k =
    agree-RLet (E.inferElabV ctx e₁) eq
      (λ p → infer-agreeV ctx e₁ (rec (dbl-< (μ<-l (μ e₁) (μ e₂)))) p)
      (λ {A} rE2 eqRE2 p → infer-agreeV (extendNamedCtx ctx x A) e₂ (rec (dbl-< (μ<-r (μ e₁) (μ e₂)))) (trans eqRE2 p)) dγ k
  infer-agreeV ctx (Raw.RResolved cn) _ eq dγ k =
    agree-RResolved ctx cn (lookupImport (NamedCtx.imports ctx) (showCanonical cn)) refl eq dγ k
  -- RVar: mirror inferElabV's `x ≟ "unit"` dispatch (bring `eq` into the `with`
  -- so it specialises); unit → `unit`, else the lookup-aux via `agree-RVar`.
  infer-agreeV ctx (Raw.RVar x) _ eq dγ k with StrProp._≟_ x "unit" | eq
  ... | yes refl | refl = refl
  ... | no ¬unit | eq' =
        agree-RVar ctx x ¬unit (lookupLocal ctx x) refl
                   (lookupImport (NamedCtx.imports ctx) x) refl eq' dγ k
  -- RLam / RAna: `inferElabV` always fails (no infer rule), so the success
  -- equation is absurd.
  infer-agreeV ctx (Raw.RLam _ _) _ ()
  infer-agreeV ctx (Raw.RAna _ _) _ ()
  -- RBinOp: with-free — delegate to top-level `agree-RBinOp`, passing both
  -- operand results explicitly + their sub-IHs (mirrors RPair).
  infer-agreeV ctx (Raw.RBinOp op e₁ e₂) (acc rec) eq dγ k =
    agree-RBinOp op (E.inferElabV ctx e₁) (E.inferElabV ctx e₂) eq
      (λ p → infer-agreeV ctx e₁ (rec (dbl-< (μ<-l (μ e₁) (μ e₂)))) p)
      (λ p → infer-agreeV ctx e₂ (rec (dbl-< (μ<-r (μ e₁) (μ e₂)))) p) dγ k
  -- RQualified: dispatch on the dotted-path import-lookup (with-free top-level).
  infer-agreeV ctx (Raw.RQualified name alias) _ eq dγ k =
    agree-RQualified ctx name alias
      (lookupImport (NamedCtx.imports ctx) (alias ++ "." ++ name)) refl eq dγ k
  -- RApp: dispatch on the app-head view. arg-infer / f-infer / arg-check IHs
  -- each carry a strictly-smaller `Acc` (dbl-</μ<-l/μ<-r/mCI-sub).
  infer-agreeV ctx (Raw.RApp f arg) (acc rec) eq dγ k =
    agree-RApp ctx f arg (E.classifyAppHeadView f) refl eq
      (λ p → infer-agreeV ctx arg (rec (dbl-< (μ<-r (μ f) (μ arg)))) p)
      (λ p → infer-agreeV ctx f (rec (dbl-< (μ<-l (μ f) (μ arg)))) p)
      (λ {T'} p → check-agreeV ctx arg T' (rec (mCI-sub (μ<-r (μ f) (μ arg)))) p) dγ k
  -- RAnnot: infers by CHECKING the body against the annotation; delegate to
  -- `check-agreeV` (phase drops to check, which is strictly < this infer node).
  infer-agreeV ctx (Raw.RAnnot e T₀) (acc rec) eq dγ k =
    agree-RAnnot (E.checkElabV ctx e T₀) eq
      (λ p → check-agreeV ctx e T₀ (rec (check<infer-annot e T₀)) p) dγ k
  -- RDestruct (case): mirror the de-withed elaborator auxes (scrutinee type;
  -- left branch in ctx,xL:A; right branch in ctx,xR:B; branch-type match). The
  -- emitted `case' scrutE eLE eRE` denotes `⟦scrutE⟧ >>=T copair-of-branches`;
  -- `realize-infer (t-case …)` is the SAME shape; close by `bind2-faithful`
  -- with each sub-IH carrying a strictly-smaller `Acc`.
  infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) (acc rec) eq dγ k
    with E.inferElabV ctx scrut in seq | eq
  ... | failure _ , _ | ()
  ... | success Unit   _ _ _ _ , _ | ()
  ... | success Void   _ _ _ _ , _ | ()
  ... | success Int    _ _ _ _ , _ | ()
  ... | success Float  _ _ _ _ , _ | ()
  ... | success Str    _ _ _ _ , _ | ()
  ... | success Buffer _ _ _ _ , _ | ()
  ... | success (_ * _)      _ _ _ _ , _ | ()
  ... | success (_ ⇒[ _ ] _) _ _ _ _ , _ | ()
  ... | success (μ-type _)   _ _ _ _ , _ | ()
  ... | success (ν-type _)   _ _ _ _ , _ | ()
  ... | success (A + B) Ψs scrutE ds fs , wS | eq₁
        with E.inferElabV (extendNamedCtx ctx xL A) eL in leq | eq₁
  ...     | failure _ , _ | ()
  ...     | success C₁ (qℓ ∷ᵘ Ψₗ) eLE dL fL , wL | eq₂
            with E.inferElabV (extendNamedCtx ctx xR B) eR in req | eq₂
  ...       | failure _ , _ | ()
  ...       | success C₂ (qr ∷ᵘ Ψᵣ) eRE dR fR , wR | eq₃
              with C₁ E.≟T C₂ | eq₃
  ...         | no _     | ()
  ...         | yes refl | refl =
                bind2-faithful (SD.⟦ scrutE ⟧ˢ fmt dγ) (SD.⟦ realize-infer wS ⟧ˢ fmt dγ)
                  (λ v → [ (λ a → SD.⟦ eLE ⟧ˢ fmt (dγ , a)) , (λ b → SD.⟦ eRE ⟧ˢ fmt (dγ , b)) ]′ v)
                  (λ v → [ (λ a → SD.⟦ realize-infer wL ⟧ˢ fmt (dγ , a)) , (λ b → SD.⟦ realize-infer wR ⟧ˢ fmt (dγ , b)) ]′ v)
                  (λ j → infer-agreeV ctx scrut (rec (dbl-< (μ<-d-s (μ scrut) (μ eL) (μ eR)))) seq dγ j)
                  (λ { (inj₁ a) j → infer-agreeV (extendNamedCtx ctx xL A) eL (rec (dbl-< (μ<-d-l (μ scrut) (μ eL) (μ eR)))) leq (dγ , a) j
                     ; (inj₂ b) j → infer-agreeV (extendNamedCtx ctx xR B) eR (rec (dbl-< (μ<-d-r (μ scrut) (μ eL) (μ eR)))) req (dγ , b) j })
                  k

  check-agreeV : ∀ (ctx : NamedCtx) (e : RawExpr) (T : Type) (ac : Acc _<_ (mCheck e)) {Ψ se d f w}
    (eq : E.checkElabV ctx e T ≡ (success Ψ se d f , w)) → CheckAgreeV ctx e T eq
  -- Generic infer-and-match fallback (checkElabV's catch-all): the check
  -- witness is `t-embed w` over the infer witness `w`, `se` is the infer-
  -- elaborated `eE`, and `realize (t-embed w) = realize-infer w`, so agreement
  -- is EXACTLY `infer-agreeV` of the same expr (the phase drops, so the `Acc`
  -- is strictly smaller via `infer<check`). Mirror the fallback's two `with`s
  -- (inferElabV result; `T ≟T T'`), threading `eq` so it reduces.
  -- Infer-then-check (generic catch-all = `embedOrSubsume`): ONE bridge lemma.
  check-agreeV ctx (Raw.RBinOp op a b) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RBinOp op a b) (rec (infer<check (Raw.RBinOp op a b))) p) dγ k
  -- PLAN 0.73 F3: the neg node has a specialised check clause now, so this
  -- mirrors `checkElabV-neg-dispatch`'s three-way split — the `RInt`/`RFloat`
  -- branches like `check-agreeV`'s own literal clauses above, the rest like
  -- the generic fallback it used to be in full.
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T (acc rec) eq dγ k
    with E.negOperandView e | eq
  ... | E.nov-int n | eq₁ with E.isRIntVliftTarget? T | eq₁
  ...   | just (X , π , refl) | refl = refl
  ...   | nothing | eq₂ with T E.≟T Int | eq₂
  -- The SAME `⊝-fromℤ` step the infer branch spends: the elaborator folded to
  -- the literal `-n` while `realize (t-embed (t-neg (t-int n)))` still reads
  -- `neg (int n)` off the derivation.
  ...     | yes refl | refl =
            cong (λ v → (DL.List.[] , v)) (sym (OnceWord.Width.⊝-fromℤ (int-bits fmt) n))
  ...     | no _     | ()
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T (acc rec) eq dγ k
    | E.nov-float i f l p | eq₁ with E.isRFloatVliftTarget? T | eq₁
  ...   | just (X , π , refl) | refl = refl
  ...   | nothing | eq₂ with T E.≟T Float | eq₂
  -- Nothing to spend here: `realize-infer (t-neg-float …)` folded too, because
  -- `Surface.neg` is Int-typed and there was no float negation to keep.
  ...     | yes refl | refl = refl
  ...     | no _     | ()
  -- NOT a literal: the generic fallback, but named at the form the abstracted
  -- view has already reduced to — `inferElabV ctx (RUnaryOp OpNeg e)` would
  -- unfold back into the stuck view.
  check-agreeV ctx (Raw.RUnaryOp Raw.OpNeg e) T (acc rec) eq dγ k
    | E.nov-other .e | eq₁ =
      agree-embedOrSubsume-at T (E.inferElabV-RUnaryOp-aux ctx e (E.inferElabV ctx e)) eq₁
        (λ p → agree-RUnaryOp (E.inferElabV ctx e) p
                 (λ q → infer-agreeV ctx e (rec (mIC-sub ≤-refl)) q))
        dγ k
  check-agreeV ctx (Raw.RLet x e₁ e₂) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RLet x e₁ e₂) (rec (infer<check (Raw.RLet x e₁ e₂))) p) dγ k
  check-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RDestruct scrut xL eL xR eR) (rec (infer<check (Raw.RDestruct scrut xL eL xR eR))) p) dγ k
  check-agreeV ctx (Raw.RAnnot e T₀) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RAnnot e T₀) (rec (infer<check (Raw.RAnnot e T₀))) p) dγ k
  check-agreeV ctx (Raw.RQualified name alias) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RQualified name alias) (rec (infer<check (Raw.RQualified name alias))) p) dγ k
  check-agreeV ctx (Raw.RResolved cn) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RResolved cn) (rec (infer<check (Raw.RResolved cn))) p) dγ k
  -- RUnit / RStringLit: generic fallback over a literal whose inferred type is
  -- fixed (Unit / Str); case `T ≟T <that>` (the fallback's `T ≟T T'`), so `eq`
  -- reduces. `yes refl` delegates to `infer-agreeV` of the literal.
  check-agreeV ctx Raw.RUnit T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx Raw.RUnit (rec (infer<check Raw.RUnit)) p) dγ k
  check-agreeV ctx (Raw.RStringLit s) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RStringLit s) (rec (infer<check (Raw.RStringLit s))) p) dγ k
  -- RInt: vlift target (X ⇒[Many,pure] Int) emits `lift-morphism (intLit n)`,
  -- witness `t-value-lift (g-int n)`; `realize-global (g-int n) = intLit n`, so
  -- the two `lift-morphism`s coincide ⇒ `refl`. Otherwise the generic fallback
  -- (inferred type Int) delegates to `infer-agreeV`.
  check-agreeV ctx (Raw.RInt n) T (acc rec) eq dγ k with E.isRIntVliftTarget? T | eq
  ... | just (X , π , refl) | refl = refl
  ... | nothing | eq' with T E.≟T Int | eq'
  ...   | yes refl | refl = infer-agreeV ctx (Raw.RInt n) (rec (infer<check (Raw.RInt n))) refl dγ k
  ...   | no _     | ()
  -- RFloat mirrors it, with _ the acceptance decision as a THIRD scrutinee: the
  -- K3: only ONE scrutinee left. The acceptance decision used to be named in
  -- BOTH branches — the fallback runs `inferElabV`, which dispatched on the
  -- same decision, so leaving it unnamed left the equation stuck. There is no
  -- decision now, and the two absurd branches went with it.
  check-agreeV ctx (Raw.RFloat i f l _) T (acc rec) eq dγ k
    with E.isRFloatVliftTarget? T | eq
  ... | just (X , π , refl) | refl = refl
  ... | nothing | eq' with T E.≟T Float | eq'
  ...   | yes refl | refl = refl
  ...   | no _     | ()
  -- RPair: product target → bidirectional component check (pair denotation is
  -- fuel-`k`-pointwise, rewrite both component agreements); pure-arrow→product
  -- vlift → `lift-morphism m` vs `realize-global gd`, bridged by `checkG-realize`;
  -- else the generic infer-and-match fallback.
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ k with E.classifyRPairTarget T | eq
  ... | E.rpt-prod A B | eq'
        with E.checkElabV ctx a A in eqa | eq'
  ...     | failure _ , _ | ()
  ...     | success Ψ₁ aE da fa , wA | eq''
            with E.checkElabV ctx b B in eqb | eq''
  ...         | failure _ , _ | ()
  ...         | success Ψ₂ bE db fb , wB | refl
                rewrite check-agreeV ctx a A (rec (mC-sub (μ<-l (μ a) (μ b)))) eqa dγ k
                      | check-agreeV ctx b B (rec (mC-sub (μ<-r (μ a) (μ b)))) eqb dγ k = refl
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ k | E.rpt-vlift X A B π | eq'
        with E.inspectCheckG ctx X (Raw.RPair a b) (A * B) | eq'
  ...     | E.cgv-nothing _ | ()
  ...     | E.cgv-just {m} {gd} cgeq | refl rewrite checkG-realize gd cgeq = refl
  check-agreeV ctx (Raw.RPair a b) T (acc rec) eq dγ k | E.rpt-other T' | eq'
        with E.inferElabV ctx (Raw.RPair a b) in ieq | eq'
  ...     | failure _ , _ | ()
  ...     | success T'' Ψ eE d fr , w | eq₂ with T' E.≟T T'' | eq₂
  ...       | yes refl | refl = infer-agreeV ctx (Raw.RPair a b) (rec (infer<check (Raw.RPair a b))) ieq dγ k
  ...       | no _     | ()
  -- RLam: only checks against a pure arrow `A ⇒[Many/One/Zero,pure] B`; the body
  -- is checked in `ctx,x:A`. `se = lam q leq bodyE`, witness `t-lam leq wBody`,
  -- and `⟦lam q _ e⟧ = returnT (λ a → ⟦e⟧ (dγ,a))`, so agreement = the body
  -- `check-agreeV` lifted through the bound value (funext over `a` then fuel `j`).
  -- Every non-pure-arrow target fails ⇒ absurd success-eq.
  check-agreeV ctx (Raw.RLam x body) (A ⇒[ mk-kind q pure ] B) (acc rec) eq dγ k
    with E.checkElabV (extendNamedCtx ctx x A) body B in eqBody | eq
  ... | failure _ , _ | ()
  ... | success (q' ∷ᵘ Ψ) bodyE d fr , wBody | eq₁ with E.decideLeq q' q | eq₁
  ...   | just leq  | refl =
          cong (λ f → returnT f k)
            (extensionality (λ a → extensionality (λ j →
              check-agreeV (extendNamedCtx ctx x A) body B (rec (mC-sub ≤-refl)) eqBody (dγ , a) j)))
  ...   | nothing   | ()
  check-agreeV ctx (Raw.RLam x body) Unit         _ ()
  check-agreeV ctx (Raw.RLam x body) Void         _ ()
  check-agreeV ctx (Raw.RLam x body) Int          _ ()
  check-agreeV ctx (Raw.RLam x body) Float        _ ()
  check-agreeV ctx (Raw.RLam x body) Str          _ ()
  check-agreeV ctx (Raw.RLam x body) Buffer       _ ()
  check-agreeV ctx (Raw.RLam x body) (_ * _)      _ ()
  check-agreeV ctx (Raw.RLam x body) (_ + _)      _ ()
  check-agreeV ctx (Raw.RLam x body) (μ-type _)   _ ()
  check-agreeV ctx (Raw.RLam x body) (ν-type _)   _ ()
  -- Plan 0.52 M1: lambda at an eff arrow via pure ⊑ eff subsumption. `se = arr'
  -- (lam Many …)`, witness `t-subsume (t-lam …)`; `⟦arr' f⟧ = ⟦f⟧` so the proof
  -- is the pure RLam body argument verbatim. One/Zero-eff still fail (no clause).
  check-agreeV ctx (Raw.RLam x body) (A ⇒[ mk-kind Many eff ] B) (acc rec) eq dγ k
    with E.checkElabV (extendNamedCtx ctx x A) body B in eqBody | eq
  ... | failure _ , _ | ()
  ... | success (q' ∷ᵘ Ψ) bodyE d fr , wBody | eq₁ with E.decideLeq q' Many | eq₁
  ...   | just leq  | refl =
          cong (λ f → returnT f k)
            (extensionality (λ a → extensionality (λ j →
              check-agreeV (extendNamedCtx ctx x A) body B (rec (mC-sub ≤-refl)) eqBody (dγ , a) j)))
  ...   | nothing   | ()
  check-agreeV ctx (Raw.RLam x body) (_ ⇒[ mk-kind One eff ] _) _ ()
  check-agreeV ctx (Raw.RLam x body) (_ ⇒[ mk-kind Zero eff ] _) _ ()
  -- RApp: dispatch on the app-head view; t-embed views delegate to infer,
  -- the rest route through agree-check-RApp (todo residual for now).
  check-agreeV ctx (Raw.RApp f arg) T (acc rec) eq dγ k =
    agree-check-RApp ctx f arg T (E.classifyAppHeadView f) refl eq
      (λ p → infer-agreeV ctx (Raw.RApp f arg) (rec (infer<check (Raw.RApp f arg))) p)
      (λ {T'} p → check-agreeV ctx arg T' (rec (mC-sub (μ<-r (μ f) (μ arg)))) p)
      (λ p → infer-agreeV ctx arg (rec (mIC-sub (μ<-r (μ f) (μ arg)))) p)
      (λ {T'} p → check-agreeV ctx f T' (rec (mC-sub (μ<-l (μ f) (μ arg)))) p) dγ k
  -- RAna: no infer rule (`inferElabV` always fails) and no check rule either, so
  -- the generic `checkElabV` fallback (`with inferElabV ctx e`) is always
  -- `failure` ⇒ success-eq absurd.
  check-agreeV ctx (Raw.RAna a e) T (acc rec) eq dγ k =
    agree-embedOrSubsume T eq (λ p → infer-agreeV ctx (Raw.RAna a e) (rec (infer<check (Raw.RAna a e))) p) dγ k
  -- RVar (the ONLY shape that reached the former catch-all). Infer-success bridges
  -- through embed (t-embed ⇒ infer-agreeV) or subsume (agree-embedOrSubsume-no),
  -- exactly like `ahv-apply`. Infer-failure dispatches the bare builtins / poly to
  -- their PRECISE named obligations (each `refl` once navigated; poly = the gap).
  check-agreeV ctx (Raw.RVar x) T (acc rec) eq dγ k
    with E.inferElabV ctx (Raw.RVar x) in ieq | eq
  ... | success T' Ψ' eE' d' f' , wi | eq'
        with T E.≟T T' | eq'
  ...     | yes refl | refl =
            infer-agreeV ctx (Raw.RVar x) (rec (infer<check (Raw.RVar x))) ieq dγ k
  ...     | no _ | eq₂ =
            agree-embedOrSubsume-no T' T eE' d' f' wi eq₂
              (λ dγ' k' → infer-agreeV ctx (Raw.RVar x) (rec (infer<check (Raw.RVar x))) ieq dγ' k') dγ k
  check-agreeV ctx (Raw.RVar x) T (acc rec) eq dγ k
    | failure fe , snd | eq' with E.classifyBareBuiltin x | eq'
  ...   | E.bbc-id       | eq'' = check-agreeV-RVar-id            ctx T eq'' dγ k
  ...   | E.bbc-fst      | eq'' = check-agreeV-RVar-fst           ctx T eq'' dγ k
  ...   | E.bbc-snd      | eq'' = check-agreeV-RVar-snd           ctx T eq'' dγ k
  ...   | E.bbc-terminal | eq'' = check-agreeV-RVar-terminal      ctx T eq'' dγ k
  ...   | E.bbc-initial  | eq'' = check-agreeV-RVar-initial       ctx T eq'' dγ k
  ...   | E.bbc-inl      | eq'' = check-agreeV-RVar-inl           ctx T eq'' dγ k
  ...   | E.bbc-inr      | eq'' = check-agreeV-RVar-inr           ctx T eq'' dγ k
  ...   | E.bbc-other    | eq'' = check-agreeV-RVar-poly-todo     ctx x T eq'' dγ k

------------------------------------------------------------------------
-- THE BRIDGE (Plan 0.50: de-island). `realize-agrees` of the EXACT type
-- `RealizeBridge`/`Compile.main-realize-agrees` consume. Mirrors `check-sound`'s
-- own case-split (`checkElab = proj₁ ∘ checkElabV`): casing `checkElabV` reduces
-- `cc` to a `success`/`failure` equation; `success` ⇒ the goal is `check-agreeV`'s
-- conclusion; `failure` is absurd. RealizeBridge re-exports this.
------------------------------------------------------------------------
realize-agrees : ∀ (ctx : NamedCtx) (e : RawExpr) (A : Type)
  {Ψ : Usage (NamedCtx.size ctx)}
  {se : Expr (NamedCtx.debruijn ctx) Ψ A} {d f : ℕ}
  (cc : E.checkElab ctx e A ≡ success Ψ se d f)
  (dγ : ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜ ⟧ᴰ) (k : ℕ) →
  SD.⟦ se ⟧ˢ fmt dγ k ≡ SD.⟦ realize (check-sound ctx e A cc) ⟧ˢ fmt dγ k
realize-agrees ctx e A cc dγ k with E.checkElabV ctx e A in eqV
... | success Ψ' eE' d' fr' , w' with cc
...   | refl = check-agreeV ctx e A (<-wellFounded (mCheck e)) eqV dγ k
realize-agrees ctx e A cc dγ k | failure _ , _ with cc
... | ()
