-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.WalkBack — the Spec's walk is a typed telescope
-- of the compiler's (plan 0.121 `complete`; the converse of `Walk`).
--
-- The compiler's telescope is built alongside the Spec's walk, in a scope
-- the walk keeps (`WalkState`). The Spec's definitions table agrees with the
-- translation of the compiler's up to the numbering of each schema's
-- variables (`Rel`, `SchemaRen`), which the Spec leaves free. A definition
-- with a signature (`step`): its body, moved to the compiler's numbering
-- (`TyRen`) and table (`DefsRen`), is the compiler's check (`Def.body-check←`);
-- and its type is principal for the compiler as for the Spec
-- (`Def.principal←`, reading a compiler check back the other way).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Lang.Contract using (ISig)
open import Once.Lang.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
open import Once.Spec.Numerics using (TargetNum)
import Once.Lang.Type as LT
import Once.Lang.Type.WellFormed as LW
import Once.Spec.Type as ST
open import Once.Lang.Typing.Scope using (Imports; lookupImport)
open import Once.Adequacy.SpecCore.Type using (TyR)
open import Once.Adequacy.SpecCore.Poly using (declS)

module Once.Adequacy.SpecFront.WalkBack
  (Σ : Signature) {Fs : ISig}
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
  (fmt : TargetNum) (ps : List String) (sg : Imports)
  (h-sig : ∀ {m} (Δ : ST.KCtx m) {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ LT.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ T ⌜ t ⌝ᵈ)
  (h-own-sig : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ))
  (h-psig : ∀ {x} → x ∈ ps → lookupImport sg x ≡ nothing)
  (h-word : ∀ {c t} → (c ∶ t) ∈ Σ → WordName c)
  where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)

import Once.Lang.Core.PolyTy as LP
import Once.Lang.Core.Telescope as TL
import Once.Lang.Context as LCx
import Once.Spec.Core.Syntax as SC
open SC.Schema using (arity; kinds; type)
import Once.Spec.Surface.Program as SPr
import Once.Spec.Grade as SG
import Once.Spec.Context as SCx
import Once.Spec.Sub as SS
import Once.Lang.Elaboration as E
open import Once.Lang.Typing using (_⊢ᶜ_∶_⨾_)
open import Once.Lang.Principal using (PrincipalAt)
open import Once.Lang.Module using (Scope; scope; ctxOf)
open import Once.Lang.Core.Translate using (SigSig; ImpSig; TeleSig; SigCF; viewOf)
import Once.Lang.Core.Abstract as A
import Once.Lang.Core.PolyTyping
import Once.Spec.Surface.Typing
import Once.Spec.Core.Typing
open import Once.Adequacy.SpecCore.Schema using (defsS; kindsS)
open import Once.Adequacy.SpecCore.Poly using (module Translate)
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Adequacy.SpecFront.SchemaRen using (SchRen; ρ-of; ρ-inv; kinds-ren; schemaOf-ren)
import Once.Adequacy.SpecFront.DefsRen as DefsRen
import Once.Adequacy.SpecFront.TyRen as TyRen
import Once.Metatheory.TermModel.TySubst as TySubst
open import Once.Adequacy.SpecFront.WalkState {Fs} Σ ps using (WInv)
open import Once.Adequacy.SpecFront.Walk Σ sigop-S fmt ps sg h-sig h-own-sig h-psig h-word using (module AtState)

------------------------------------------------------------------------
-- The two definitions tables, up to numbering
------------------------------------------------------------------------

-- The Spec's table and (the translation of) the compiler's agree schema by
-- schema, each way.
record Rel {s} (S′ S₂ : SC.Defs s) : Set where
  field
    ρ⇒   : ∀ d → Fin (arity (S₂ SC.!! d)) → Fin (arity (S′ SC.!! d))
    ren⇒ : ∀ d → SchRen (S′ SC.!! d) (S₂ SC.!! d) (ρ⇒ d)
    ρ⇐   : ∀ d → Fin (arity (S′ SC.!! d)) → Fin (arity (S₂ SC.!! d))
    ren⇐ : ∀ d → SchRen (S₂ SC.!! d) (S′ SC.!! d) (ρ⇐ d)
open Rel

-- A definition read both ways extends it.
rel-▷ : ∀ {s} {S′ S₂ : SC.Defs s} {T sc sc₂} → Rel S′ S₂ → SPr.SchemaOf T sc → SPr.SchemaOf T sc₂
      → Rel (S′ SC.▷ sc) (S₂ SC.▷ sc₂)
rel-▷ r so so₂ = record
  { ρ⇒   = λ { zero → ρ-of so so₂ ; (suc d) → ρ⇒ r d }
  ; ren⇒ = λ { zero → schemaOf-ren so so₂ ; (suc d) → ren⇒ r d }
  ; ρ⇐   = λ { zero → ρ-of so₂ so ; (suc d) → ρ⇐ r d }
  ; ren⇐ = λ { zero → schemaOf-ren so₂ so ; (suc d) → ren⇐ r d }
  }

------------------------------------------------------------------------
-- A definition with a signature
------------------------------------------------------------------------

module Step {s} {S : LP.Sig Fs s} {imps tele} (ss : SigSig Fs sg) (is : ImpSig S imps) (ts : TeleSig S tele)
            (sgcf : SigCF S) (nm : Fin s → CanonicalName) (w : WInv S (scope sg imps tele) is ts nm)
            {S′ : SC.Defs s} (r : Rel S′ (defsS S)) where

  module At = AtState ss is ts sgcf nm w
  private
    module TR  = TyRen Σ S′ nm
    module TS  = TySubst Σ S′
    module DR⇒ = DefsRen Σ S′ (defsS S) nm (ρ⇒ r)
    module DR⇐ = DefsRen Σ (defsS S) S′ nm (ρ⇐ r)
    module TP′ = Translate S Σ sigop-S
    module PT  = Once.Lang.Core.PolyTyping S
    module SU₂ = Once.Spec.Surface.Typing Σ (defsS S) nm
    module SC₂ = Once.Spec.Core.Typing Σ (defsS S)

    -- (every usage over no locals is the empty one)
    u0 : ∀ {m} {Δ : LP.KCtx m} {Ψ : LCx.Usage 0} {t B π}
       → PT._⊩_⊢[_]_∷_!_ Δ PT.∅ Ψ t B π → PT._⊩_⊢[_]_∷_!_ Δ PT.∅ LCx.Usage.[] t B π
    u0 {Ψ = LCx.Usage.[]} d = d

  -- The body checks in the compiler, at its type, which is principal there.
  step : ∀ {a} (κ : LP.KCtx a) {T sc e e′ A A′}
       → TyR (kindsS κ) A A′ → SPr.SchemaOf T (SC.schema a (kindsS κ) A′) → SPr.SchemaOf T sc
       → SPr.Body Σ S′ nm sc e′ → SPr.Principal Σ S′ nm sc e′ → RX [] e e′
       → (Σ[ Ψ ∈ LCx.Usage 0 ] ctxOf (scope sg imps tele) ⊢ᶜ e ∶ A ⨾ Ψ) × PrincipalAt (ctxOf (scope sg imps tele)) e A
  step {a} κ {T} {sc} {e} {e′} {A} {A′} rA so₂ so b pr rx = chk , At.principal← κ rx rA typed pr₂
    where
      sc₂ = SC.schema a (kindsS κ) A′
      σ  = ρ-of so₂ so
      σ⁻ = ρ-of so so₂
      -- the Spec's numbering to the compiler's, and back
      module B  = TR.Bij σ σ⁻ (ρ-inv so₂ so) (ρ-inv so so₂) {Δ = kinds sc} {Δ′ = kindsS κ} (kinds-ren so₂ so)
      module B⁻ = TR.Bij σ⁻ σ (ρ-inv so so₂) (ρ-inv so₂ so) {Δ = kindsS κ} {Δ′ = kinds sc} (kinds-ren so so₂)

      to-A′ : type sc ST.⟨ B.sv ⟩ ≡ A′
      to-A′ = trans (SchRen.ty (schemaOf-ren so₂ so) ST.var) (TR.⟨⟩-id A′)

      to-sc : A′ ST.⟨ B⁻.sv ⟩ ≡ type sc
      to-sc = trans (SchRen.ty (schemaOf-ren so so₂) ST.var) (TR.⟨⟩-id (type sc))

      -- the body's term, renumbered and moved to the compiler's table
      tm = DR⇒.rn (SPr.Body.term b SC.⟪ B.sv ⟫ₜ)

      chk : Σ[ Ψ ∈ LCx.Usage 0 ] ctxOf (scope sg imps tele) ⊢ᶜ e ∶ A ⨾ Ψ
      chk = At.body-check← κ
              (subst (λ X → SU₂._⊢_⇐_↝_ (kindsS κ) SU₂.∅ e′ X tm) to-A′ (DR⇒.chk (ren⇒ r) (B.chk (SPr.Body.check b))))
              (subst (λ X → SC₂._⊩_⊢[_]_∷_!_ (kindsS κ) SCx.∅ SCx.[] tm X SG.pure) to-A′
                     (DR⇒.core (ren⇒ r) (TS.ty-subst-⊢ B.sv B.rσ (SPr.Body.typed b))))
              rx rA

      -- a compiler check, typed in the core
      typed : ∀ {X Ψ} (D : ctxOf (scope sg imps tele) ⊢ᶜ e ∶ X ⨾ Ψ) → _
      typed D = TP′.trD (u0 (A.abs-⊢ S κ sgcf (proj₂ (E.elabᶜ S (viewOf ss is ts) D))))

      -- the compiler's reading of the Spec's principality
      pr₂ : ∀ {X t} → X SS.<:ᶜ A′
          → SU₂._⊢_⇐_↝_ (kindsS κ) SU₂.∅ e′ X t
          → SC₂._⊩_⊢[_]_∷_!_ (kindsS κ) SCx.∅ SCx.[] t X SG.pure
          → X ≡ A′
      pr₂ {X} sub c T₀ =
        trans (sym (B⁻.back X))
              (trans (cong (ST._⟨ B.sv ⟩)
                       (pr (subst (X ST.⟨ B⁻.sv ⟩ SS.<:ᶜ_) to-sc (TR.<:ᶜ-⟨⟩ B⁻.sv sub))
                           (B⁻.chk (DR⇐.chk (ren⇐ r) c))
                           (TS.ty-subst-⊢ B⁻.sv B⁻.rσ (DR⇐.core (ren⇐ r) T₀))))
                     to-A′)
