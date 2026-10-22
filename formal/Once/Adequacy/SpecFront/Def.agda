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
open import Once.Internal.Contract using (ISig)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Grade as LG
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as LW
import Once.Internal.Core.PolyTy as LP
import Once.Internal.Type.Poly as TP
import Once.Internal.Elaboration as E
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
open import Once.Internal.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Adequacy.SpecCore.Type using (TyR)
open import Once.Adequacy.SpecCore.Poly using (declS)
open import Once.Adequacy.SpecCore.Schema using (CleanSig; ptyS; defsS; kindsS)
import Once.Adequacy.SpecFront.Scope as Sc

module Once.Adequacy.SpecFront.Def
  {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) (Σ : Signature)
  (sigop-S : ∀ {c A} → WordName c → (showCanonical c , A) ∈ Fs → (c ∶ declS A) ∈ Σ)
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
  -- …nor an FFI declaration's (R11, D330)
  (b-psig : ∀ {x} → x ∈ ps → lookupImport sg x ≡ nothing)
  -- …and every declaration of Σ has a word name (D329)
  (b-word : ∀ {c t} → (c ∶ t) ∈ Σ → WordName c)
  where

open import Data.Fin using (toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (_<?_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; subst)

import Once.Internal.Context as LC
import Once.Spec.Grade as SG
import Once.Spec.Sub as SS
import Once.Spec.Context as SCx
open import Once.Internal.Type.DecEq using (_≟T_; _≟tk_)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.Internal.Typing.Scope using (NamedCtx; mkCtx)
open import Once.Internal.Principal using (PrincipalAt; below-complete)
open import Once.Adequacy.SpecFront.Below using (below-sound)
open import Once.Internal.Core.AbsTy using (absTy; absF; ar-bound; ar-kind; ConstFree; ConstFreeF; cf-var; cf-Unit; cf-Void; cf-Int; cf-Float; cf-*; cf-+; cf-⇒; cf-μ; cf-ν; cf-K; cf-Id; cf-⊕; cf-⊗)
import Once.Internal.Core.Abstract S as A
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
  open import Once.Adequacy.SpecFront.Back Σ S′ nm {imps} {sg} {polys} {ps} Δ b-name (b-sig Δ) (b-mono Δ) b-ps (b-poly Δ) b-own-sig b-psig b-word
    using (bwdᶜ; bwdᵢ; BChk; BSyn)
  open import Once.Adequacy.SpecFront.Locals Σ S′ nm Δ using (LR; lr-∅)
  open import Once.Adequacy.SpecFront.Types Δ using (back; subᶜ-L; subᶜ-S; below-R)
  open import Once.Adequacy.SpecFront.Abs S Σ sigop-S using (tm-abs; ty-abs)
  import Once.Spec.Surface.Typing Σ S′ nm as SU
  module EV = E S

  -- The body checks at its type, naming the term the compiler's telescope holds.
  body-check : ∀ {e e′ A A′ Ψ} (D : C₀ ⊢ᶜ e ∶ A ⨾ Ψ) → RX [] e e′ → TyR Δ A A′
             → SU._⊢_⇐_↝_ Δ SU.∅ e′ A′ (ptmS (A.absTm κ (proj₁ (EV.elabᶜ V D))))
  body-check D rx rA =
    let c = fwdᶜ D lr-∅ rx rA in subst (SU._⊢_⇐_↝_ Δ SU.∅ _ _) (sym (tm-abs κ (Chk.rt c))) (Chk.der c)

  -- R8: a body without a signature synthesizes its type, naming the term the
  -- compiler's telescope holds.
  body-synth : ∀ {e e′ A Ψ} (D : C₀ ⊢ᵢ e ∶ A ⨾ Ψ) → RX [] e e′
             → Σ[ A′ ∈ ST.Ty m ] TyR Δ A A′ × SU._⊢_⇒_↝_ Δ SU.∅ e′ A′ (ptmS (A.absTm κ (proj₁ (EV.elabᵢ V D))))
  body-synth D rx =
    let c = fwdᵢ D lr-∅ rx in Syn.A′ c , Syn.ra c , subst (SU._⊢_⇒_↝_ Δ SU.∅ _ _) (sym (tm-abs κ (Syn.rt c))) (Syn.der c)

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
              → RX [] e e′ → Σ[ A ∈ LT.Type ] TyR Δ A A′ × Σ[ Ψ ∈ LC.Usage 0 ] C₀ ⊢ᵢ e ∶ A ⨾ Ψ
  body-synth← syn T rx = let b = proj₂ (bwdᵢ syn rx lr-∅ T) in BSyn.A b , BSyn.ra b , _ , BSyn.der b

  -- …and a type principal in the Spec is principal in the compiler: a check
  -- strictly below is the Spec's (`Check`), at a type strictly below.
  principal← : ∀ {e e′ A A′} → RX [] e e′ → TyR Δ A A′
             → (∀ {X Ψ} (D : C₀ ⊢ᶜ e ∶ X ⨾ Ψ)
                → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] ptmS (A.absTm κ (proj₁ (EV.elabᶜ V D))) ∷ ptyS (absTy κ X) ! SG.pure)
             → (∀ {X t} → X SS.<:ᶜ A′ → SU._⊢_⇐_↝_ Δ SU.∅ e′ X t → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] t ∷ X ! SG.pure → X ≡ A′)
             → PrincipalAt C₀ e A
  principal← {A = A} rx rA typed pr {X} m D =
    let (sX , nX) = below-sound A m
        (X′ , rX) = below-R sX rA
        eq = pr (subᶜ-S sX rX rA) (body-check D rx rX)
                (subst (λ Y → Δ ⊩ SCx.∅ ⊢[ SCx.[] ] _ ∷ Y ! SG.pure) (ty-abs κ rX) (typed D))
    in nX (TyR-uniqueˡ rX (subst (TyR Δ A) (sym eq) rA))

