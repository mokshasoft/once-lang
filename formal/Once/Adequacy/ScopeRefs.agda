-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ScopeRefs — the references of a scope, related (plan 0.122
-- §5.6, stage e).
--
-- `MeaningBridgeS` relates a reference to a table entry through `Refs.entry`:
-- the entry's meaning against the realization's `ref` (a call of a
-- monomorphic entry by its name, a spliced telescope entry). The entries a
-- checked body references are the ones its View finds (`InView`); for those,
-- the scope's by-name relation (`MRel`: imports against calls, telescope
-- definitions against the reference environment) and the scope's agreement
-- with the table (`Agree`) give the relation — each at the View's own schema
-- equation, moved to any other (`move`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Type using (TySub)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Denotation.SourceDenote using (DefsSem; module DefsSem)
open import Once.Adequacy.SourceRefl using (RelDefs)

module Once.Adequacy.ScopeRefs (fmt : TargetNum) (Σ : Signature) (σ₀ : TySub 0 0) (σ : DefsSem) (σ-self : RelDefs fmt σ σ) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Binary.HeterogeneousEquality as H
open H using (_≅_)
open import Once.Postulates using (extensionality)
open import Once.Spec.Name using (CanonicalName; canonical)
import Once.Spec.Context
open import Once.Spec.Type using (Type; KCtx; ∅ₖ; Respects; _⟨_⟩)
open import Once.Spec.Grade using (pure)
open import Once.Spec.Core.Syntax using (Defs; _!!_; Schema; module Schema; schema)
open Schema using (type; arity; kinds)
open import Once.Internal.Iterative using (T∞)
open import Once.Internal.Typing.Scope using (NamedCtx; lookupImport; lookupPolyPrefix)
open import Once.Internal.Type.Schema using (schemaOf; kinded-instance)
open import Once.Internal.Type.Instance using (rigidOf; KindedInstance)
open import Once.Adequacy.SpecFront.SchemaOf using (ki-of; ki-of-τ)
open import Once.Denotation.SpecDomain Σ σ₀ using (⟦_⟧ᵛ; ⟦wk₀⟧ᵛ)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.GradedRelation Σ σ₀ using (RelGM)
open import Once.Adequacy.MeaningBridge fmt Σ σ₀ σ using (MRel; imprel-at; envrel-at; callSD)
open DefsSem using (refs)
open import Once.Denotation.RefMeanings Σ σ₀ using (Meanings)

-- Both sides of the relation, along type and value equations.
RelGM-≅ : ∀ {A B : Type} → A ≡ B → ∀ {v v′ t t′} → v ≅ v′ → t ≅ t′ → RelGM pure A v t → RelGM pure B v′ t′
RelGM-≅ refl H.refl H.refl h = h

module _ {s : ℕ} {S : Defs s} where

  import Once.TypeCheck.View Σ S as TV
  open import Once.Adequacy.CoreMeaningBridge fmt Σ S σ₀ using (Agree; module Agree; refSemAt; refSemAt-Δ)
  import Once.Spec.Core.Meaning Σ fmt S as SM

  -- The relation `Refs.entry` asks, at a schema equation.
  private
    module G (nm : Fin s → CanonicalName) (inline : Fin s → Bool) (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set) (δ : SM.DefSem) where
      import Once.Denotation.RealizeS Σ S nm Ok OkS inline ∅ₖ as RS

      Goal : (d : Fin s) {sc : Schema} → S !! d ≡ sc → Set
      Goal d {sc} e = ∀ (τ : TySub (arity sc) 0) (r : Respects (kinds sc) ∅ₖ τ)
                    → ∀ {n} {Γ : Once.Spec.Context.Ctx 0 n} {dγ}
                    → RelGM pure (type sc ⟨ τ ⟩) (refSemAt δ d e τ r) ((SD.⟦ RS.ref {Γ = Γ} d (type sc ⟨ τ ⟩) (inline d) ⟧ˢ fmt σ) dγ)

      -- (an entry's relation does not depend on the equation it is read at)
      move : ∀ (d : Fin s) {sc sc′} (e : S !! d ≡ sc) (e′ : S !! d ≡ sc′) → Goal d e → Goal d e′
      move d refl refl g = g


  private
    refSemAt-≅ : (δ : SM.DefSem) (d : Fin s) {sc : Schema} (e : S !! d ≡ sc) {τ τ′ : TySub (arity sc) 0} {Δ Δ′ : KCtx 0}
                 (r : Respects (kinds sc) Δ τ) (r′ : Respects (kinds sc) Δ′ τ′) → τ ≡ τ′ → refSemAt δ d e τ r ≅ refSemAt δ d e τ′ r′
    refSemAt-≅ δ d e r r′ refl = H.≡-to-≅ (refSemAt-Δ δ d e _ r r′)

  open import Once.Internal.Core.TySubstZero Σ S using (⟨⟩-0)

  -- The references of a scope with no locals: the entries its View finds.
  module _ (ctx : NamedCtx 0) (nm : Fin s → CanonicalName) (inline : Fin s → Bool) (V : TV.Views ctx) (OkS : CanonicalName → Type → Set)
           (h-imp : ∀ {x T} (lk : lookupImport (NamedCtx.imports ctx) x ≡ just T)
                  → nm (TV.ImportAt.entryOf (TV.View.imported V lk)) ≡ canonical (x ∷ []))
           (h-call : ∀ {x T} (lk : lookupImport (NamedCtx.imports ctx) x ≡ just T)
                   → inline (TV.ImportAt.entryOf (TV.View.imported V lk)) ≡ false)
           (h-poly : ∀ {x sc b p} (lp : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (sc , b , p))
                   → nm (TV.View.entry V lp) ≡ canonical (x ∷ []))
           (h-inl : ∀ {x sc b p} (lp : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (sc , b , p))
                  → inline (TV.View.entry V lp) ≡ true)
           (δ : SM.DefSem) (ρ : Meanings (NamedCtx.polys ctx) (NamedCtx.imports ctx) (NamedCtx.sig ctx))
           (ag : Agree V ρ δ) (er : MRel ctx ρ) where

    open G nm inline (TV.InView V) OkS δ
    import Once.Denotation.RealizeS Σ S nm (TV.InView V) OkS inline ∅ₖ as RS

    private
      -- a called entry's realization is a call of it by name…
      sd-call : ∀ (d : Fin s) {x} {A : Type} {n} {Γ : Once.Spec.Context.Ctx 0 n} {dγ} → inline d ≡ false → nm d ≡ canonical (x ∷ [])
              → (SD.⟦ RS.ref {Γ = Γ} d A (inline d) ⟧ˢ fmt σ) dγ ≡ callSD x A
      sd-call d e n rewrite e | n = refl

      -- …and an inlined one's, the reference environment's at its name
      sd-poly : ∀ (d : Fin s) {x} {A : Type} {n} {Γ : Once.Spec.Context.Ctx 0 n} {dγ} → inline d ≡ true → nm d ≡ canonical (x ∷ [])
              → (SD.⟦ RS.ref {Γ = Γ} d A (inline d) ⟧ˢ fmt σ) dγ ≡ refs σ x A
      sd-poly d e n rewrite e | n = refl

    refs-entry : ∀ (d : Fin s) → TV.InView V d → Goal d refl
    refs-entry d (TV.iv-imp {x = x} {T = T} lk refl) = move d mono refl g
      where
        mono = TV.ImportAt.mono (TV.View.imported V lk)
        g : Goal d mono
        g τ r {dγ = dγ} =
          RelGM-≅ (sym (⟨⟩-0 τ T))
            (H.trans (H.sym (H.≡-subst-removable id (sym (⟦wk₀⟧ᵛ T)) _))
                     (H.trans (H.≡-to-≅ (Agree.agree-import ag {Δ = ∅ₖ} lk))
                              (refSemAt-≅ δ d mono (λ ()) r (extensionality (λ ())))))
            (H.trans (H.cong (callSD x) (H.≡-to-≅ (sym (⟨⟩-0 τ T)))) (H.≡-to-≅ (sym (sd-call d (h-call lk) (h-imp lk)))))
            (imprel-at (NamedCtx.imports ctx) x (proj₁ (proj₂ er)) lk)
    refs-entry d (TV.iv-poly {x = x} {sc = psc} lp refl) = move d (TV.View.entryIs V lp) refl g
      where
        g : Goal d (TV.View.entryIs V lp)
        g τ r {dγ = dγ} =
          let ki = ki-of {Δ = ∅ₖ} psc τ r in
          RelGM-≅ {A = rigidOf psc ⟨ τ ⟩} refl
            (H.trans (H.≡-to-≅ (Agree.agree-inst ag lp ki))
                     (H.trans (H.≡-subst-removable (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance psc ki))) _)
                              (refSemAt-≅ δ d (TV.View.entryIs V lp) _ r (ki-of-τ {Δ = ∅ₖ} psc τ r))))
            (H.≡-to-≅ (sym (sd-poly d (h-inl lp) (h-poly lp))))
            (envrel-at (NamedCtx.polys ctx) x (proj₁ er) lp (rigidOf psc ⟨ τ ⟩) ki)
