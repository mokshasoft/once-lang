-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Def — a definition of the compiler's telescope,
-- as the Spec's (plan 0.121 §3.6, F6).
--
-- The compiler checks a definition's body once, over its schema's parameters
-- (plan 0.122), and elaborates it; the Spec's walk asks for a `Body` (the body
-- checked at the schema's type, naming a core term) and that the schema is
-- the body's principal type. Both come from the two typing bridges, at the
-- Spec's kinds of the schema:
--   * the check: the compiler's derivation as the Spec's (`Check.fwdᶜ`), at
--     the term the compiler's telescope holds — the elaboration itself
--     (plan 0.122: the elaborator emits the Spec's core);
--   * principality: a Spec check at a smaller type gives the compiler's
--     (`Back.bwdᶜ`), at a type below the compiler's (`subᶜ-L`), which the
--     compiler's `PrincipalAt` rules out unless the two are the same
--     (`below-complete`).
-- What either bridge asks of the scope is a parameter (`h-…`), the walk's.
-- Conversely (`complete`): a Spec check or synthesis of the body gives the
-- compiler's (`body-check←`, `body-synth←`, by `Back`), and a type principal
-- in the Spec is principal in the compiler (`principal←`): a compiler check at
-- a type strictly below (`Below.below-sound`) is the Spec's, by `Check`.
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
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
import Once.Spec.Grade as LG
import Once.Internal.Type.WellFormed as LW
import Once.Internal.Type.Poly as TP
import Once.Internal.Elaboration as E
import Once.TypeCheck.View as TView
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
open import Once.Internal.Type using (wk₀)
open import Once.Internal.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Adequacy.SpecCore.Type using (TyR)
import Once.Adequacy.SpecFront.Scope as Sc

module Once.Adequacy.SpecFront.Def
  (Σ : Signature) {s : ℕ} (S : SC.Defs s) (nm : Fin s → CanonicalName)
  {imps sg : Imports} {polys : PolyCtx} {ps : List String} (V : TView.View Σ S imps sg polys)
  -- what the compiler's typing asks of the scope (`Check`)
  (h-imp : ∀ {x T} (lk : lookupImport imps x ≡ just T)
         → nm (TView.ImportAt.entryOf (TView.View.imported V lk)) ≡ canonical (x ∷ []))
  (h-poly : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → nm (TView.View.entry V lp) ≡ canonical (x ∷ []))
  (h-ground : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
            → TP.Ground sc → SC.Schema.arity (S SC.!! TView.View.entry V lp) ≡ 0)
  (h-open : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p))
          → ¬ TP.Ground sc → 0 < SC.Schema.arity (S SC.!! TView.View.entry V lp))
  (h-arrow : ∀ {x sc b p} (lp : lookupPolyPrefix polys x ≡ just (sc , b , p)) {sd sco π′}
           → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
           → Σ[ X ∈ ST.Ty (SC.Schema.arity (S SC.!! TView.View.entry V lp)) ]
             Σ[ Y ∈ ST.Ty (SC.Schema.arity (S SC.!! TView.View.entry V lp)) ]
               (SC.Schema.type (S SC.!! TView.View.entry V lp) ≡ X ST.⇒[ LG.mk-kind LG.Many π′ ] Y)
               × (∀ i → ST.Occurs i Y → ST.Occurs i X))
  -- what the Spec's typing asks of it (`Back`), at every kind context
  (b-name : ∀ d → Σ[ x ∈ String ] nm d ≡ canonical (x ∷ []))
  (b-sig : ∀ {m} (Δ : ST.KCtx m) {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ ST.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ (wk₀ T) ⌜ t ⌝ᵈ)
  (b-mono : ∀ {m} (Δ : ST.KCtx m) {d x} → nm d ≡ canonical (x ∷ []) → ¬ (x ∈ ps) → x ≢ "main"
          → (lookupImport sg x ≡ nothing)
            × Σ[ T ∈ ST.Type ] (lookupImport imps x ≡ just T)
              × (∀ τ → TyR Δ (wk₀ T) (SC.Schema.type (S SC.!! d) ST.⟨ τ ⟩)))
  (b-ps : ∀ {d x} → nm d ≡ canonical (x ∷ []) → 0 < SC.Schema.arity (S SC.!! d) → x ∈ ps)
  (b-poly : ∀ {m} (Δ : ST.KCtx m) {d x} → nm d ≡ canonical (x ∷ []) → x ∈ ps → Sc.PolyAt S imps polys Δ d x)
  (b-own-sig : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ))
  -- …nor an FFI declaration's (R11, D330)
  (b-psig : ∀ {x} → x ∈ ps → lookupImport sg x ≡ nothing)
  -- …and every declaration of Σ has a word name (D329)
  (b-word : ∀ {c t} → (c ∶ t) ∈ Σ → WordName c)
  where

open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; subst)

import Once.Internal.Context as LC
import Once.Spec.Grade as SG
import Once.Spec.Sub as SS
import Once.Spec.Context as SCx
open import Once.Internal.Type.DecEq using (_≟T_)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.Internal.Typing.Scope using (NamedCtx; mkCtx)
open import Once.Internal.Principal using (PrincipalAt; below-complete)
open import Once.Adequacy.SpecFront.Below using (below-sound)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.TermR S using (TmR-≡)
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Spec.Core.Typing Σ S using (_⊩_⊢[_]_∷_!_)

private
  module EV = E Σ S

  -- a usage of no variables
  use0 : (Ψ : SCx.Usage 0) → Ψ ≡ SCx.[]
  use0 SCx.[] = refl

------------------------------------------------------------------------
-- A definition's body, at its kinds
------------------------------------------------------------------------

module _ {m} (Δ : ST.KCtx m) where

  private
    -- the definitions' scope, empty of locals
    C₀ : NamedCtx m
    C₀ = mkCtx 0 [] LC.∅ imps polys sg Δ

  open import Once.Adequacy.SpecFront.Check Σ S nm V h-imp h-poly h-ground h-open h-arrow Δ
    using (fwdᶜ; fwdᵢ; Chk; Syn)
  open import Once.Adequacy.SpecFront.Back Σ S nm {imps} {sg} {polys} {ps} Δ b-name (b-sig Δ) (b-mono Δ) b-ps (b-poly Δ) b-own-sig b-psig b-word
    using (bwdᶜ; bwdᵢ; BChk; BSyn)
  open import Once.Adequacy.SpecFront.Locals Σ S nm Δ using (LR; lr-∅)
  open import Once.Adequacy.SpecFront.Types Δ using (back; subᶜ-L; subᶜ-S; below-R)
  import Once.Spec.Surface.Typing Σ S nm as SU

  -- The body checks at its type, naming the term the compiler's telescope holds.
  body-check : ∀ {e e′ A A′ Ψ} (D : C₀ ⊢ᶜ e ∶ A ⨾ Ψ) → RX [] e e′ → TyR Δ A A′
             → SU._⊢_⇐_↝_ Δ SU.∅ e′ A′ (proj₁ (EV.elabᶜ V D))
  body-check D rx rA =
    let c = fwdᶜ D lr-∅ rx rA in subst (SU._⊢_⇐_↝_ Δ SU.∅ _ _) (sym (TmR-≡ (Chk.rt c))) (proj₁ (Chk.der c))

  -- R8: a body without a signature synthesizes its type, naming the term the
  -- compiler's telescope holds.
  body-synth : ∀ {e e′ A Ψ} (D : C₀ ⊢ᵢ e ∶ A ⨾ Ψ) → RX [] e e′
             → Σ[ A′ ∈ ST.Ty m ] TyR Δ A A′ × SU._⊢_⇒_↝_ Δ SU.∅ e′ A′ (proj₁ (EV.elabᵢ V D))
  body-synth D rx =
    let c = fwdᵢ D lr-∅ rx in Syn.A′ c , Syn.ra c , subst (SU._⊢_⇒_↝_ Δ SU.∅ _ _) (sym (TmR-≡ (Syn.rt c))) (proj₁ (Syn.der c))

  -- The type is the body's principal one.
  principal : ∀ {e e′ A A′} → PrincipalAt C₀ e A → RX [] e e′ → TyR Δ A A′
            → ∀ {X t} → X SS.<:ᶜ A′ → SU._⊢_⇐_↝_ Δ SU.∅ e′ X t → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] t ∷ X ! SG.pure → X ≡ A′
  principal {A = A} pr rx rA {X} sub chk T = at (X₀ ≟T A)
    where
      X₀ = proj₁ (back X)
      rX = proj₂ (back X)
      at : Dec (X₀ ≡ A) → X ≡ _
      at (yes refl) = TyR-uniqueˢ rX rA
      at (no ne)    = ⊥-elim (pr (below-complete (subᶜ-L sub rX rA) ne) (BChk.der (proj₂ (bwdᶜ chk rx lr-∅ rX T))))

  ----------------------------------------------------------------------
  -- Conversely (plan 0.121 `complete`)
  ----------------------------------------------------------------------

  -- A Spec check of the body gives the compiler's…
  body-check← : ∀ {e e′ A A′ t} → SU._⊢_⇐_↝_ Δ SU.∅ e′ A′ t → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] t ∷ A′ ! SG.pure
              → RX [] e e′ → TyR Δ A A′ → Σ[ Ψ ∈ LC.Usage 0 ] C₀ ⊢ᶜ e ∶ A ⨾ Ψ
  body-check← chk T rx rA = _ , BChk.der (proj₂ (bwdᶜ chk rx lr-∅ rA T))

  -- …as does a synthesis, at a related type…
  body-synth← : ∀ {e e′ A′ t} → SU._⊢_⇒_↝_ Δ SU.∅ e′ A′ t → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] t ∷ A′ ! SG.pure
              → RX [] e e′ → Σ[ A ∈ ST.Ty m ] TyR Δ A A′ × Σ[ Ψ ∈ LC.Usage 0 ] C₀ ⊢ᵢ e ∶ A ⨾ Ψ
  body-synth← syn T rx = let b = proj₂ (bwdᵢ syn rx lr-∅ T) in BSyn.A b , BSyn.ra b , _ , BSyn.der b

  -- …and a type principal in the Spec is principal in the compiler: a check
  -- strictly below is the Spec's (`Check`), at a type strictly below, typed
  -- in the core by its elaboration.
  principal← : ∀ {e e′ A A′} → RX [] e e′ → TyR Δ A A′
             → (∀ {X t} → X SS.<:ᶜ A′ → SU._⊢_⇐_↝_ Δ SU.∅ e′ X t → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] t ∷ X ! SG.pure → X ≡ A′)
             → PrincipalAt C₀ e A
  principal← {A = A} rx rA pr {X} m {Ψ} D =
    let (sX , nX) = below-sound A m
        (X′ , rX) = below-R sX rA
        t = proj₁ (EV.elabᶜ V D)
        typed = subst (λ Φ → Δ ⊩ SCx.∅ ⊢[ Φ ] t ∷ X ! SG.pure) (use0 Ψ) (proj₂ (EV.elabᶜ V D))
        eq = pr (subᶜ-S sX rX rA) (body-check D rx rX)
                (subst (λ Y → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] t ∷ Y ! SG.pure) (TyR-≡ rX) typed)
    in nX (TyR-uniqueˡ rX (subst (TyR Δ A) (sym eq) rA))
