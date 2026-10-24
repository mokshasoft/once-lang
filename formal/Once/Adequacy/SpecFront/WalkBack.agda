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
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
import Once.Spec.Type as LT
import Once.Internal.Type.WellFormed as LW
open import Once.Internal.Type using (wk₀)
import Once.Spec.Type as ST
open import Once.Internal.Typing.Scope using (Imports; lookupImport)
open import Once.Adequacy.SpecCore.Type using (TyR; TyR-≡)

module Once.Adequacy.SpecFront.WalkBack
  (Σ : Signature) (ps : List String) (sg : Imports)
  (h-sig : ∀ {m} (Δ : ST.KCtx m) {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ ST.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ (wk₀ T) ⌜ t ⌝ᵈ)
  (h-own-sig : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ))
  (h-psig : ∀ {x} → x ∈ ps → lookupImport sg x ≡ nothing)
  (h-word : ∀ {c t} → (c ∶ t) ∈ Σ → WordName c)
  where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)

import Once.Spec.Core.Program Σ as SP
import Once.Internal.Context as LCx
import Once.Spec.Core.Syntax as SC
open SC.Schema using (arity; kinds; type)
import Once.Spec.Surface.Program as SPr
import Once.Spec.Grade as SG
import Once.Spec.Context as SCx
import Once.Spec.Sub as SS
open import Once.Internal.Principal using (PrincipalAt)
open import Once.Internal.Module using (Scope; scope; ctxOf; ctxOfAt)
open import Once.Internal.Core.Translate Σ using (SigSig; ImpSig; TeleSig; viewOf)
import Once.Spec.Surface.Typing
import Once.Spec.Core.Typing
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Adequacy.SpecFront.SchemaRen using (SchRen; ρ-of; ρ-inv; kinds-ren; schemaOf-ren)
import Once.Adequacy.SpecFront.DefsRen as DefsRen
import Once.Adequacy.SpecFront.TyRen as TyRen
import Once.Metatheory.TermModel.TySubst as TySubst
open import Once.Adequacy.SpecFront.WalkState Σ ps using (WInv)
open import Once.Adequacy.SpecFront.Def Σ ps sg h-sig h-psig h-word using (body-check←; body-synth←; principal←)
open import Once.Internal.Module using (CheckRun; MonoWit)
open import Once.Adequacy.ModuleProgram Σ using (Names)

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

module Step {s} {S : SC.Defs s} {imps tele} (ss : SigSig sg) (is : ImpSig S imps) (ts : TeleSig S tele)
            (N : Names S is ts) (w : WInv S (scope sg imps tele) is ts (Names.nm N))
            {S′ : SC.Defs s} (r : Rel S′ S) where

  private
    nm = Names.nm N
    module TR  = TyRen Σ S′ nm
    module TS  = TySubst Σ S′
    module DR⇒ = DefsRen Σ S′ S nm (ρ⇒ r)
    module DR⇐ = DefsRen Σ S S′ nm (ρ⇐ r)
    module SU₂ = Once.Spec.Surface.Typing Σ S nm
    module SC₂ = Once.Spec.Core.Typing Σ S

  -- The body checks in the compiler, at its type, which is principal there.
  step : ∀ {a} (κ : ST.KCtx a) {T sc e e′ A A′}
       → TyR κ A A′ → SPr.SchemaOf T (SC.schema a κ A′) → SPr.SchemaOf T sc
       → SPr.Body Σ S′ nm sc e′ → SPr.Principal Σ S′ nm sc e′ → RX [] e e′
       → (Σ[ Ψ ∈ LCx.Usage 0 ] CheckRun (ctxOfAt κ (scope sg imps tele)) e A Ψ) × PrincipalAt (ctxOfAt κ (scope sg imps tele)) e A
  step {a} κ {T} {sc} {e} {e′} {A} {A′} rA so₂ so b pr rx = go (TyR-≡ rA)
    where
      sc₂ = SC.schema a κ A′
      σ  = ρ-of so₂ so
      σ⁻ = ρ-of so so₂
      -- the Spec's numbering to the compiler's, and back
      module B  = TR.Bij σ σ⁻ (ρ-inv so₂ so) (ρ-inv so so₂) {Δ = kinds sc} {Δ′ = κ} (kinds-ren so₂ so)
      module B⁻ = TR.Bij σ⁻ σ (ρ-inv so so₂) (ρ-inv so₂ so) {Δ = κ} {Δ′ = kinds sc} (kinds-ren so so₂)

      to-A′ : type sc ST.⟨ B.sv ⟩ ≡ A′
      to-A′ = trans (SchRen.ty (schemaOf-ren so₂ so) ST.var) (TR.⟨⟩-id A′)

      to-sc : A′ ST.⟨ B⁻.sv ⟩ ≡ type sc
      to-sc = trans (SchRen.ty (schemaOf-ren so so₂) ST.var) (TR.⟨⟩-id (type sc))

      -- the body's term, renumbered and moved to the compiler's table
      tm = DR⇒.rn (SPr.Body.term b SC.⟪ B.sv ⟫ₜ)

      chk : Σ[ Ψ ∈ LCx.Usage 0 ] CheckRun (ctxOfAt κ (scope sg imps tele)) e A′ Ψ
      chk = body-check← ss is ts N w κ
              (subst (λ X → SU₂._⊢_⇐_↝_ κ SU₂.∅ e′ X tm) to-A′ (DR⇒.chk (ren⇒ r) (B.chk (SPr.Body.check b))))
              (subst (λ X → SC₂._⊩_⊢[_]_∷_!_ κ SCx.∅ SCx.[] tm X SG.pure) to-A′
                     (DR⇒.core (ren⇒ r) (TS.ty-subst-⊢ B.sv B.rσ (SPr.Body.typed b))))
              rx

      -- the compiler's reading of the Spec's principality
      pr₂ : ∀ {X t} → X SS.<:ᶜ A′
          → SU₂._⊢_⇐_↝_ κ SU₂.∅ e′ X t
          → SC₂._⊩_⊢[_]_∷_!_ κ SCx.∅ SCx.[] t X SG.pure
          → X ≡ A′
      pr₂ {X} sub c T₀ =
        trans (sym (B⁻.back X))
              (trans (cong (ST._⟨ B.sv ⟩)
                       (pr (subst (X ST.⟨ B⁻.sv ⟩ SS.<:ᶜ_) to-sc (TR.<:ᶜ-⟨⟩ B⁻.sv sub))
                           (B⁻.chk (DR⇐.chk (ren⇐ r) c))
                           (TS.ty-subst-⊢ B⁻.sv B⁻.rσ (DR⇐.core (ren⇐ r) T₀))))
                     to-A′)

      go : A ≡ A′ → (Σ[ Ψ ∈ LCx.Usage 0 ] CheckRun (ctxOfAt κ (scope sg imps tele)) e A Ψ) × PrincipalAt (ctxOfAt κ (scope sg imps tele)) e A
      go refl = chk , principal← ss is ts N w κ rx pr₂

  private
    module SU′ = Once.Spec.Surface.Typing Σ S′ nm
    module SC′ = Once.Spec.Core.Typing Σ S′

  -- A definition without a signature: its body synthesizes in the compiler,
  -- at a related type, which is principal there.
  step-nosig : ∀ {e e′ A t}
             → SU′._⊢_⇒_↝_ ST.∅ₖ SU′.∅ e′ A t → SC′._⊩_⊢[_]_∷_!_ ST.∅ₖ SCx.∅ SCx.[] t A SG.pure
             → SPr.Principal Σ S′ nm (SC.schema 0 ST.∅ₖ A) e′ → RX [] e e′
             → (Σ[ Ψ ∈ LCx.Usage 0 ] MonoWit nothing (ctxOf (scope sg imps tele)) e A Ψ) × PrincipalAt (ctxOf (scope sg imps tele)) e A
  step-nosig {e} {e′} {A} {t} syn typ pr rx =
    body-synth← ss is ts N w ST.∅ₖ (DR⇒.syn (ren⇒ r) syn) (DR⇒.core (ren⇒ r) typ) rx , principal← ss is ts N w ST.∅ₖ rx pr₂
    where

      pr₂ : ∀ {X t′} → X SS.<:ᶜ A
          → SU₂._⊢_⇐_↝_ ST.∅ₖ SU₂.∅ e′ X t′
          → SC₂._⊩_⊢[_]_∷_!_ ST.∅ₖ SCx.∅ SCx.[] t′ X SG.pure
          → X ≡ A
      pr₂ {X} {t′} sub c T₀ =
        pr sub (DR⇐.chk (ren⇐ r) c) (DR⇐.core (ren⇐ r) T₀)

------------------------------------------------------------------------
-- The walk
------------------------------------------------------------------------

open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Sum using (inj₂)
open import Data.Bool using (false)
open import Once.Internal.Module using (ModTele; []; ffi; mono; poly; addImp; addPoly)
open import Once.Internal.Core.Translate Σ using (t-def; wkI; wkT; impDefs; monoSchema)
open import Once.Adequacy.ModuleProgram Σ using (names-mono; names-poly; monoDef; polyDef)
open import Once.Internal.Type.Schema using (schemaOf)
open import Once.Internal.Type.Instance using (kindsOf)
import Once.Internal.Type.Instance
import Once.Parser as Parser
import Once.Compile as C
import Once.TypeCheck.Elaborate as TE
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys)
open import Once.Adequacy.SpecCore.Type using (tyR; r-unit; r-void; r-int; r-float; r-*; r-+; r-⇒; r-μ; r-ν; r-var;
                                               FunR; r-K; r-Id; r-⊕; r-⊗)
open import Once.Adequacy.SpecFront.SchemaRen using (ren-0)
open import Once.Adequacy.SpecFront.WalkState Σ ps using (winv-mono; winv-poly; _∷ⁿ_)
open import Once.Adequacy.SpecFront.Walk Σ ps sg h-sig h-own-sig h-psig h-word using (EntriesOK; eok-mono; eok-poly)
open import Once.Adequacy.SpecFront.Align Σ using (Align; al-nil; al-skip; al-mono; al-nosig; al-poly)
open import Once.Adequacy.SpecFront.WalkMain Σ using (MainsW; MainW; entry-concrete)
open import Once.Spec.Core.Program Σ using (Entry; entry; EffUU)
open import Once.Internal.Module using (MainsEffUU; MainIn)
import Once.Spec.Sub as LS
import Once.Spec.Grade as LG
open import Once.Adequacy.SpecGrammar.Conv using (toPoly)
open import Once.Adequacy.SpecCore.Type using (sub-L)
open import Once.Functor.Decide using (isConcrete?-complete)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open EntriesOK

private
  all-head : ∀ {X : Set} {P : X → Set} {x xs} → All P (x ∷ xs) → P x
  all-head (h ∷ _) = h

  -- (mirrors `inferType`'s `with`)
  infer-ok : ∀ ctx polys body {A Ψ eE d f} → TE.inferElab (ctxWithImportsAndPolys ctx polys) body ≡ TE.success A Ψ eE d f
           → C.inferType ctx polys body ≡ inj₂ A
  infer-ok ctx polys body eq rewrite eq = refl

  r-EffUU : ∀ {Δ : ST.KCtx 0} → TyR Δ (LT.Unit LT.⇒[ LG.mk-kind LG.Many LG.eff ] LT.Unit) EffUU
  r-EffUU = r-⇒ refl r-unit r-unit

  nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
  nothing≢just ()

  module TR0 = TyRen Σ SC.[] (λ ())

  -- an entry's type, read by the compiler
  entry-eff : ∀ {ty sc ρ} → SchRen (monoSchema ty) sc ρ → Entry sc
            → ty LS.<: LT.Unit LT.⇒[ LG.mk-kind LG.Many LG.eff ] LT.Unit
  entry-eff {ty} {ρ = ρ} R (entry {A = A} p) =
    let eqA = trans (sym (TR0.⟨⟩-id A)) (trans (TR0.⟨⟩-pt A {τ = ST.var} {τ′ = λ i → ST.var (ρ i)} (λ ()))
                                               (trans (SchRen.ty R ST.var) (TR0.⟨⟩-id _)))
    in sub-L p (subst (TyR ST.∅ₖ ty) (sym eqA) (tyR ty)) r-EffUU

-- A definition without variables extends the relation.
rel-▷0 : ∀ {s} {S′ S₂ : SC.Defs s} {k₁ k₂ : ST.KCtx 0} {A A₂} → Rel S′ S₂ → A ≡ A₂
       → Rel (S′ SC.▷ SC.schema 0 k₁ A) (S₂ SC.▷ SC.schema 0 k₂ A₂)
rel-▷0 r refl = record
  { ρ⇒   = λ { zero → λ i → i ; (suc d) → ρ⇒ r d }
  ; ren⇒ = λ { zero → ren-0 ; (suc d) → ren⇒ r d }
  ; ρ⇐   = λ { zero → λ i → i ; (suc d) → ρ⇐ r d }
  ; ren⇐ = λ { zero → ren-0 ; (suc d) → ren⇐ r d }
  }

-- The Spec's walk, as the compiler's telescope; where the walk's steps
-- defining `main` define entries, so do the telescope's, and where some
-- step does, some entry is `main`.
walk← : ∀ {s} {S : SC.Defs s} {imps tele es ds}
          (tl : SP.Tele S) (ss : SigSig sg) (is : ImpSig S imps) (ts : TeleSig S tele) (N : Names S is ts)
          {S′ : SC.Defs s} {tl′ s″} {S″ : SC.Defs s″} {nm″ tl″}
        → Rel S′ S → (wk : SPr.Walk Σ S′ (Names.nm N) tl′ ds S″ nm″ tl″) → Align ds es
        → WInv S (scope sg imps tele) is ts (Names.nm N) → EntriesOK (scope sg imps tele) es
        → Σ[ mt ∈ ModTele (scope sg imps tele) es ] (MainsW wk → MainsEffUU mt) × (MainW wk → MainIn mt)
walk← tl ss is ts N r SPr.w-end al-nil w o = [] , (λ _ → tt) , (λ ())
walk← tl ss is ts N r (SPr.w-skip _ wk) (al-skip SPr.nd-sig al)    w o = walk← tl ss is ts N r wk al w o
walk← tl ss is ts N r (SPr.w-skip _ wk) (al-skip SPr.nd-alias al)  w o = walk← tl ss is ts N r wk al w o
walk← tl ss is ts N r (SPr.w-skip _ wk) (al-skip SPr.nd-import al) w o = walk← tl ss is ts N r wk al w o
-- a monomorphic definition with a signature
walk← {S = S} {imps} {tele} tl ss is ts N r (SPr.w-sig {sc = sc} so b pr wk) (al-mono {x = x} {e = e} {ty = ty} so₂ rx al) w o =
  mono refl refl P W mt , (λ { (h , hs) → (λ m → eff-at (h m)) , ms hs }) , (λ { (inj₁ (m , en)) → inj₁ (m , eff-at en) ; (inj₂ m) → inj₂ (mi m) })
  where
    fi = Parser.mkFunInfo x (just ty) e false
    st = Step.step ss is ts N w r ST.∅ₖ (tyR ty) so₂ so b pr rx
    Ψ = proj₁ (proj₁ st)
    W = proj₂ (proj₁ st)
    P = proj₂ st
    rest = walk← (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss
                 (impDefs (x Data.String.== "main") is) (wkT ts) (names-mono (x Data.String.== "main") x ty N) (rel-▷ r so so₂) wk al
                 (winv-mono w (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o)
    mt = proj₁ rest
    ms = proj₁ (proj₂ rest)
    mi = proj₂ (proj₂ rest)
    -- an entry's type, the compiler's
    eff-at : Entry sc → ty LS.<: LT.Unit LT.⇒[ LG.mk-kind LG.Many LG.eff ] LT.Unit
    eff-at = entry-eff (schemaOf-ren so₂ so)
-- a telescope definition
walk← {S = S} {imps} {tele} tl ss is ts N r (SPr.w-sig so b pr wk) (al-poly {x = x} {T = T} {e = e} so₂ nmono rx al) w o =
  poly P W mt , (λ { (_ , hs) → ms hs }) , (λ { (inj₁ (_ , en)) → ⊥-elim (not-entry en) ; (inj₂ m) → mi m })
  where
    pfi = Parser.mkPolyFunInfo x T e
    κ = kindsOf T
    st = Step.step ss is ts N w r κ (tyR _) so₂ so b pr rx
    Ψ = proj₁ (proj₁ st)
    W = proj₂ (proj₁ st)
    P = proj₂ st
    rest = walk← (polyDef {S = S} {sc = scope sg imps tele} {pfi = pfi} {Ψ = Ψ} tl ss is ts N W) ss (wkI is) (t-def zero refl (wkT ts))
                 (names-poly pfi N) (rel-▷ r so so₂) wk al
                 (winv-poly pfi w (all-head (kinds o)) (all-head (fresh o))) (eok-poly o)
    mt = proj₁ rest
    ms = proj₁ (proj₂ rest)
    mi = proj₂ (proj₂ rest)
    -- `main` is no telescope definition: its type is a concrete ground one
    not-entry : Entry _ → ⊥
    not-entry en =
      let (g′ , c) = entry-concrete T so en
          (c′ , eq) = isConcrete?-complete c
      in nothing≢just (trans (sym (nmono g′)) eq)
-- one without a signature: the type its body synthesizes
walk← {S = S} {imps} {tele} tl ss is ts N r (SPr.w-nosig {A = A₀} syn typ pr wk) (al-nosig {x = x} {e = e} rx al) w o =
  mono refl (infer-ok _ _ e (cong proj₁ (proj₂ (proj₂ (proj₂ (proj₂ W)))))) P W mt
  , (λ { (h , hs) → (λ m → sub-L (h m) rA r-EffUU) , ms hs }) , (λ { (inj₁ (m , p)) → inj₁ (m , sub-L p rA r-EffUU) ; (inj₂ m) → inj₂ (mi m) })
  where
    st = Step.step-nosig ss is ts N w r syn typ pr rx
    ty = A₀
    rA : TyR ST.∅ₖ ty ty
    rA = tyR ty
    Ψ = proj₁ (proj₁ st)
    W = proj₂ (proj₁ st)
    P = proj₂ st
    fi = Parser.mkFunInfo x nothing e false
    rest = walk← (monoDef {S = S} {sc = scope sg imps tele} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss
                 (impDefs (x Data.String.== "main") is) (wkT ts) (names-mono (x Data.String.== "main") x ty N)
                 (rel-▷0 r refl) wk al
                 (winv-mono w (proj₂ (all-head (kinds o))) (all-head (nosig o)) (all-head (fresh o))) (eok-mono ty o)
    mt = proj₁ rest
    ms = proj₁ (proj₂ rest)
    mi = proj₂ (proj₂ rest)
