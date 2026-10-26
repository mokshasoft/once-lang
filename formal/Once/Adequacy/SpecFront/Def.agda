-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Def — a definition of the compiler's telescope,
-- as the Spec's (plan 0.121 §3.6, F6; plan 0.122 §5.6, stage f).
--
-- At a walk state the checker's scope has a Pack (`packOfAt`): the table, the
-- names, the View. The checker is complete for the Spec's derivation there:
-- a Spec check of a body, typed in the core, is annotated (`Annotate`, a
-- reference read by its name — the walk's scope facts and the distinct names
-- give the View's lookup that finds it), and the checker accepts the
-- annotated derivation (`Completeness`). So
--   * the Spec's check or synthesis of a body is the checker's run
--     (`body-check←`, `body-synth←`);
--   * the compiler's principality (the checker rejects the body at every
--     type strictly below its type, `Principal.PrincipalAt`) is the Spec's
--     (`principal`): a Spec check at a type below would be accepted; and
--     conversely (`principal←`): an accepted check is the Spec's
--     (`SpecWitness`), at the type the Spec's principality rules out.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Name using (showCanonical; WordName)
open import Once.Spec.Name using (NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
import Once.Type.Concrete as LW
open import Once.Type.Core using (wk₀)
import Once.Spec.Type as ST
open import Once.TypeCheck.Scope using (Imports; lookupImport)

module Once.Adequacy.SpecFront.Def
  (Σ : Signature) (ps : List String) (sg : Imports)
  -- a declaration of Σ is the signature table's, at its type
  (h-sig : ∀ {m} {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ ST.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × (wk₀ {m} T ≡ ⌜ t ⌝ᵈ))
  -- a polymorphic definition's name is no FFI declaration's (R11, D330)
  (h-psig : ∀ {x} → x ∈ ps → lookupImport sg x ≡ nothing)
  -- every declaration of Σ has a word name (D329)
  (h-word : ∀ {c t} → (c ∶ t) ∈ Σ → WordName c)
  where

open import Data.Fin using (Fin)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong; subst)
open import Data.List.Membership.DecPropositional Data.String._≟_ using (_∈?_)

import Once.Spec.Grade as SG
import Once.Spec.Sub as SS
import Once.Spec.Context as SCx
import Once.Spec.Core.Syntax as SC
import Once.Spec.Surface.Typing as SUT
import Once.Spec.Surface.Program as SPr
import Once.Spec.Core.Typing
import Once.Type.Honest
open import Once.Spec.Name using (canonical)
open import Once.Type.DecEq using (_≟T_)
open import Once.Core.Decl using (⌜declS⌝)
open import Once.Module using (scope; ctxOfAt)
open import Once.Principal using (PrincipalAt; Fails; below-complete)
open import Once.Core.Translate Σ using (SigSig; ImpSig; TeleSig; u0)
import Once.TypeCheck.ElaborateSound as TEˢ
import Once.TypeCheck.Elaborate as TE
import Once.TypeCheck.View as TV
open import Once.TypeCheck.SpecWitness using (Pack; OkOf; OkSOf)
import Once.TypeCheck.UseCore as UC
open import Once.TypeCheck.Completeness using (check-completeVS; infer-completeVS)
open import Once.Adequacy.ModuleProgram Σ using (Names; packOfAt)
open import Once.Adequacy.SpecFront.Below using (below-sound)
open import Once.Adequacy.SpecFront.Expr using (RX; rx-≡)
open import Once.Adequacy.SpecFront.WalkState Σ ps using (WInv)
import Once.Adequacy.SpecFront.Scope as Sc
import Once.Adequacy.SpecFront.Annotate as Annotate

module _ {s} {S : SC.Defs s} {imps tele} (ss : SigSig sg) (is : ImpSig S imps) (ts : TeleSig S tele)
         (N : Names S is ts) (w : WInv S (scope sg imps tele) is ts (Names.nm N)) {m} (κ : ST.KCtx m) where

  private
    nm = Names.nm N
    ctx = ctxOfAt κ (scope sg imps tele)

    P : Pack ctx
    P = packOfAt κ {sc = scope sg imps tele} ss is ts N

    -- a definition a source names, not `main`, is the one the View finds by its name
    ok-def : ∀ {c} (d : Fin s) → nm d ≡ c → c ≢ canonical ("main" ∷ []) → OkOf P d
    ok-def d refl nmain = at (WInv.named w d)
      where
        at : Σ[ x ∈ String ] nm d ≡ canonical (x ∷ []) → OkOf P d
        at (x , ex) with x ∈? ps
        ... | yes x∈ =
          let pa = WInv.poly-at w ex x∈
              e  = trans (Pack.h-poly P (Sc.PolyAt.lp pa)) (sym ex)
          in TV.iv-poly (h-psig x∈) (Sc.PolyAt.lki pa) (Sc.PolyAt.lp pa) (WInv.inj w e (λ mn → nmain (trans (sym e) mn)))
        ... | no x∉ =
          let (nsig , T , lk) = WInv.mono-at w ex x∉ (λ xm → nmain (trans ex (cong (λ y → canonical (y ∷ [])) xm)))
              e = trans (Pack.h-imp P lk) (sym ex)
          in TV.iv-imp nsig lk (WInv.inj w e (λ mn → nmain (trans (sym e) mn)))

    -- a declaration of Σ is an honest, concrete FFI declaration of the scope's signature
    ok-sig : ∀ {c t} → NotGenerator c → (c ∶ t) ∈ Σ
           → Σ[ T ∈ ST.Type ] ((c ∶ Once.Core.Decl.declS T) ∈ Σ) × (⌜ t ⌝ᵈ ≡ ⌜ Once.Core.Decl.declS T ⌝ᵈ)
               × OkSOf P c T × LW.IsConcrete T × Once.Type.Honest.HonestFFI T
    ok-sig ng mem =
      let (T , lk , k , r) = h-sig {m} ng mem
          dc = TV.View.declares (Pack.V P) lk
          h  = TV.Declared.honest dc
      in T , TV.Declared.member dc (h-word mem) refl , trans (sym r) (sym (⌜declS⌝ k h)) , (lk , h-word mem) , k , h

    module A = Annotate Σ S nm (OkOf P) (OkSOf P) κ ok-def ok-sig

    fails-success : ∀ {e X Ψ eE dd f} {wt : TEˢ.checkSoundOf ctx e X (TE.success Ψ eE dd f)}
                  → Fails (proj₁ (TEˢ.checkElabV ctx e X)) → TEˢ.checkElabV ctx e X ≡ (TE.success Ψ eE dd f , wt) → ⊥
    fails-success fl eq with subst (λ r → Fails (proj₁ r)) eq fl
    ... | ()

  -- A Spec check of the body, typed in the core, is the checker's run.
  body-check← : ∀ {e e′ A t} → SUT._⊢_⇐_↝_ Σ S nm κ SUT.∅ e′ A t
              → Once.Spec.Core.Typing._⊩_⊢[_]_∷_!_ Σ S κ SCx.∅ SCx.[] t A SG.pure → RX [] e e′
              → ∃[ Ψ ] ∃[ eE ] ∃[ dd ] ∃[ f ] Σ[ wt ∈ TEˢ.checkSoundOf ctx e A (TE.success Ψ eE dd f) ]
                  (TEˢ.checkElabV ctx e A ≡ (TE.success Ψ eE dd f , wt))
  body-check← {e} {e′} {A} chk T rx = go (rx-≡ rx) (proj₂ (A.ann⇐ chk rx T))
    where
      go : e ≡ e′ → A.A⇐ SUT.∅ e′ A SCx.[] → _
      go refl (A.a⇐ D u _) = _ , check-completeVS P u

  -- …as is a synthesis.
  body-synth← : ∀ {e e′ A t} → SUT._⊢_⇒_↝_ Σ S nm κ SUT.∅ e′ A t
              → Once.Spec.Core.Typing._⊩_⊢[_]_∷_!_ Σ S κ SCx.∅ SCx.[] t A SG.pure → RX [] e e′
              → ∃[ Ψ ] ∃[ eE ] ∃[ dd ] ∃[ f ] Σ[ wt ∈ TEˢ.soundOf ctx e (TE.success A Ψ eE dd f) ]
                  (TEˢ.inferElabV ctx e ≡ (TE.success A Ψ eE dd f , wt))
  body-synth← {e} {e′} {A} syn T rx = go (rx-≡ rx) (proj₂ (A.ann⇒ syn rx T))
    where
      go : e ≡ e′ → A.A⇒ SUT.∅ e′ A SCx.[] → _
      go refl (A.a⇒ D u _) = _ , infer-completeVS P u

  -- The compiler's principal type is the Spec's: a Spec check at a type
  -- strictly below would be accepted by the checker.
  principal : ∀ {e e′ A} → PrincipalAt ctx e A → RX [] e e′ → SPr.Principal Σ S nm (SC.schema m κ A) e′
  principal {A = A} pr rx {X} sub chk T with X ≟T A
  ... | yes eq = eq
  ... | no ne =
    let (_ , _ , _ , _ , _ , eq) = body-check← chk T rx in ⊥-elim (fails-success (pr (below-complete sub ne)) eq)

  -- …and conversely: an accepted check at a type below is the Spec's
  -- derivation, typed in the core by its usage, at a type the Spec's
  -- principality says is not below.
  principal← : ∀ {e e′ A} → RX [] e e′ → SPr.Principal Σ S nm (SC.schema m κ A) e′ → PrincipalAt ctx e A
  principal← {e} {e′} {A} rx pr {X} m with TE.checkElab ctx e X | TEˢ.checkElab-sound ctx e X
  ... | TE.failure _ | _ = Once.Principal.fails
  ... | TE.success Ψ eE dd f | wt =
    let (sX , nX) = below-sound A m
        (t , (D , u) , _) = proj₂ wt P
        D′ = subst (λ z → SUT._⊢_⇐_↝_ Σ S nm κ SUT.∅ z X t) (rx-≡ rx) D
    in ⊥-elim (nX (pr sX D′ (u0 (UC.typ⇐ Σ S nm (OkOf P) (OkSOf P) κ u))))
