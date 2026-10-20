-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Def — a definition of the compiler's telescope,
-- as the Spec's (plan 0.121 §3.6, F6).
--
-- The compiler checks a definition's body once, at its schema with rigid
-- parameters, and elaborates it; the Spec's walk asks for a `Body` (the body
-- checked at the schema's type, naming a core term) and that the schema is
-- the body's principal type. Both come from the two typing bridges, at the
-- Spec's kinds of the schema:
--   * the check: the compiler's derivation as the Spec's (`Check.fwdᶜ`), at
--     the term the compiler's telescope holds — the translation of the
--     abstracted elaboration (`Abs.tm-abs`);
--   * principality: a Spec check at a smaller type gives the compiler's
--     (`Back.bwdᶜ`), at a type below the compiler's (`subᶜ-L`), which the
--     compiler's `PrincipalAt` rules out unless the two are the same
--     (`below-complete`).
-- What either bridge asks of the scope is a parameter (`h-…`), the walk's.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Once.Lang.Contract using (ISig)
open import Once.Lang.Name using (showCanonical)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
import Once.Lang.Type as LT
import Once.Lang.Type.Grade as LG
import Once.Lang.Type.WellFormed as LW
import Once.Lang.Core.PolyTy as LP
import Once.Lang.Type.Poly as TP
import Once.Lang.Elaboration as E
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
open import Once.Lang.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Adequacy.SpecCore.Type using (TyR)
open import Once.Adequacy.SpecCore.Poly using (declS)
open import Once.Adequacy.SpecCore.Schema using (CleanSig; ptyS; defsS; kindsS)
import Once.Adequacy.SpecFront.Scope as Sc

module Once.Adequacy.SpecFront.Def
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (nm : Fin s → CanonicalName) (clean : CleanSig S)
  {imps sg : Imports} {polys : PolyCtx} {ps : List String} (V : E.View S imps sg polys)
  -- what the compiler's typing asks of the scope (`Check`)
  (h-imp : ∀ {x T} (lk : lookupImport imps x ≡ just T)
         → (nm (E.ImportAt.entryOf (E.View.imported V lk)) ≡ canonical (x ∷ []))
           × (LP.Schema.arity (S LP.!! E.ImportAt.entryOf (E.View.imported V lk)) ≡ 0))
  (h-poly : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → nm (E.View.entry V lp) ≡ canonical (x ∷ []))
  (h-ground : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
            → TP.Ground sc → LP.Schema.arity (S LP.!! E.View.entry V lp) ≡ 0)
  (h-open : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → ¬ TP.Ground sc → 0 < LP.Schema.arity (S LP.!! E.View.entry V lp))
  (h-occ : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p)) i
         → ST.Occurs i (ptyS (LP.Schema.type (S LP.!! E.View.entry V lp))))
  (h-arrow : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p)) {sd sco π′}
           → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
           → Σ[ X ∈ LP.Ty (LP.Schema.arity (S LP.!! E.View.entry V lp)) ]
             Σ[ Y ∈ LP.Ty (LP.Schema.arity (S LP.!! E.View.entry V lp)) ]
               (LP.Schema.type (S LP.!! E.View.entry V lp) ≡ X LP.⇒[ LG.mk-kind LG.Many π′ ] Y)
               × (∀ i → ST.Occurs i (ptyS Y) → ST.Occurs i (ptyS X)))
  -- what the Spec's typing asks of it (`Back`), at every kind context
  (b-name : ∀ d → Σ[ x ∈ String ] nm d ≡ canonical (x ∷ []))
  (b-sig : ∀ {m} (Δ : ST.KCtx m) {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ LT.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ T ⌜ t ⌝ᵈ)
  (b-mono : ∀ {m} (Δ : ST.KCtx m) {d x} → nm d ≡ canonical (x ∷ []) → ¬ (x ∈ ps) → x ≢ "main"
          → (lookupImport sg x ≡ nothing)
            × Σ[ T ∈ LT.Type ] (lookupImport imps x ≡ just T)
              × (∀ τ → TyR Δ T (SC.Schema.type (defsS S SC.!! d) ST.⟨ τ ⟩)))
  (b-ps : ∀ {d x} → nm d ≡ canonical (x ∷ []) → 0 < SC.Schema.arity (defsS S SC.!! d) → x ∈ ps)
  (b-poly : ∀ {m} (Δ : ST.KCtx m) {d x} → nm d ≡ canonical (x ∷ []) → x ∈ ps → Sc.PolyAt (defsS S) imps polys Δ d x)
  (b-own-sig : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ))
  where

open import Data.Fin using (toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (_<?_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; subst)

import Once.Lang.Context as LC
import Once.Spec.Grade as SG
import Once.Spec.Sub as SS
import Once.Spec.Context as SCx
open import Once.Lang.Type.DecEq using (_≟T_; _≟tk_)
open import Once.Lang.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.Lang.Typing.Scope using (NamedCtx; mkCtx)
open import Once.Lang.Principal using (PrincipalAt; below-complete)
open import Once.Lang.Core.AbsTy using (absTy; absF; ar-bound; ar-kind; ConstFree; ConstFreeF; cf-var; cf-Unit; cf-Void; cf-Int; cf-Float; cf-*; cf-+; cf-⇒; cf-μ; cf-ν; cf-K; cf-Id; cf-⊕; cf-⊗)
import Once.Lang.Core.Abstract S as A
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Poly using (module Translate)
open Translate S Σ sigop-S using (ptmS)
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Adequacy.SpecFront.AbsR using (cf-R)
open import Once.Spec.Core.Typing Σ (defsS S) using (_⊩_⊢[_]_∷_!_)

private
  S′ : SC.Defs s
  S′ = defsS S

  -- the definitions' scope, empty of locals
  C₀ : NamedCtx
  C₀ = mkCtx 0 [] LC.∅ imps polys sg

------------------------------------------------------------------------
-- A definition's body, at the Spec's kinds of its schema
------------------------------------------------------------------------

module _ {m} (κ : LP.KCtx m) where

  private
    Δ : ST.KCtx m
    Δ = kindsS κ

  open import Once.Adequacy.SpecFront.Check S Σ sigop-S nm clean V h-imp h-poly h-ground h-open h-occ h-arrow Δ
    using (fwdᶜ; fwdᵢ; Chk; Syn)
  open import Once.Adequacy.SpecFront.Back Σ S′ nm {imps} {sg} {polys} {ps} Δ b-name (b-sig Δ) (b-mono Δ) b-ps (b-poly Δ) b-own-sig
    using (bwdᶜ; BChk)
  open import Once.Adequacy.SpecFront.Locals Σ S′ nm Δ using (LR; lr-∅)
  open import Once.Adequacy.SpecFront.Types Δ using (back; subᶜ-L)
  open import Once.Adequacy.SpecFront.Abs S Σ sigop-S using (tm-abs)
  import Once.Spec.Surface.Typing Σ S′ nm as SU
  module EV = E S

  -- The body checks at its type, naming the term the compiler's telescope holds.
  body-check : ∀ {e e′ A A′ Ψ} (D : C₀ ⊢ᶜ e ∶ A ⨾ Ψ) → RX ps [] e e′ → TyR Δ A A′
             → SU._⊢_⇐_↝_ Δ SU.∅ e′ A′ (ptmS (A.absTm κ (proj₁ (EV.elabᶜ V D))))
  body-check D rx rA =
    let c = fwdᶜ D lr-∅ rx rA in subst (SU._⊢_⇐_↝_ Δ SU.∅ _ _) (sym (tm-abs κ (Chk.rt c))) (Chk.der c)

  -- R8: a body without a signature synthesizes its type, naming the term the
  -- compiler's telescope holds.
  body-synth : ∀ {e e′ A Ψ} (D : C₀ ⊢ᵢ e ∶ A ⨾ Ψ) → RX ps [] e e′
             → Σ[ A′ ∈ ST.Ty m ] TyR Δ A A′ × SU._⊢_⇒_↝_ Δ SU.∅ e′ A′ (ptmS (A.absTm κ (proj₁ (EV.elabᵢ V D))))
  body-synth D rx =
    let c = fwdᵢ D lr-∅ rx in Syn.A′ c , Syn.ra c , subst (SU._⊢_⇒_↝_ Δ SU.∅ _ _) (sym (tm-abs κ (Syn.rt c))) (Syn.der c)

  -- The type is the body's principal one.
  principal : ∀ {e e′ A A′} → PrincipalAt C₀ e A → RX ps [] e e′ → TyR Δ A A′
            → ∀ {X t} → X SS.<:ᶜ A′ → SU._⊢_⇐_↝_ Δ SU.∅ e′ X t → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] t ∷ X ! SG.pure → X ≡ A′
  principal {A = A} pr rx rA {X} sub chk T = at (X₀ ≟T A)
    where
      X₀ = proj₁ (back X)
      rX = proj₂ (back X)
      at : Dec (X₀ ≡ A) → X ≡ _
      at (yes refl) = TyR-uniqueˢ rX rA
      at (no ne)    = ⊥-elim (pr (below-complete (subᶜ-L sub rX rA) ne) (BChk.der (proj₂ (bwdᶜ chk rx lr-∅ rX T))))
