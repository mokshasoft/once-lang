-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreEnv — plan 0.103 6b, leg C.1: THE SURFACE ENVIRONMENT OF
-- A CORE TELESCOPE.
--
-- Leg B (`CoreMeaningBridge`) holds in any surface environment that `Agree`s
-- with the core's `δ`. The telescope walk builds that environment FROM `δ`,
-- entry by entry along the scope's signature (`ImpSig`/`TeleSig`, the View's
-- data), so the agreement holds by construction:
--   * a definition means its core entry at the instance (`entrySem`);
--   * an FFI declaration means the Spec's reference to its declaration of Σ
--     (`sigSem`: the world's model, or the Spec's call).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

open import Once.Spec.Type using (TySub)

module Once.Adequacy.CoreEnv (fmt : TargetNum) (Σ : Signature) {s : ℕ} (S : Defs s) (σ₀ : TySub 0 0) where

open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
import Data.String.Properties as StrProp
open import Data.Unit using (tt)
open import Function using (id)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst-sym-subst)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

import Once.Compile as C
import Once.Parser as Parser
open Parser.PolyFunInfo using (pfunType)
open import Once.Spec.Type using (Type; KCtx; ∅ₖ)
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Name using (showCanonical; WordName)
open import Once.Contract using (ISig)
open import Once.Type.Core using (wk₀; none)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Concrete using (IsConcrete)
open import Once.TypeCheck.Scope using (lookupImport; lookupPolyPrefix)
open import Once.Core.Decl using (toISig; ∈-toISig; ⌜⌝ᵈ-concrete; declS; ⌜declS⌝)
open import Once.Core.TySubstZero Σ S using (⟨⟩-0)
open import Once.Functor.Translate using (IsConcrete-irrelevant)
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.RefMeanings Σ σ₀ using (DefMeanings; ImpMeanings; Meanings; meanings)
open import Once.Denotation.SpecDomain Σ σ₀ using (⟦_⟧ᵛ; ⟦wk₀⟧ᵛ)
import Once.Spec.Core.Meaning Σ fmt S as SM
import Once.Core.Translate Σ as TR
open TR using (SigSig; ImpSig; TeleSig; viewOf; telFind; sigAt) renaming (impAt to impView)
open import Once.TypeCheck.View Σ S using (Declared; def)
open import Once.Adequacy.CoreMeaningBridge fmt Σ S σ₀ using (refSemAt-Δ; entrySem; impSem; sigSem; Agree)

------------------------------------------------------------------------
-- An FFI declaration of the scope is Σ's, at its type
------------------------------------------------------------------------

sigConc : ∀ {sg} → SigSig sg → ∀ {x T} → lookupImport sg x ≡ just T → IsConcrete T
sigConc TR.[] ()
sigConc {(n , T₀) ∷ rest} (TR.s-ffi k h m ss) {x} eq with StrProp._≟_ n x
... | yes refl with eq
...   | refl = k
sigConc {(n , T₀) ∷ rest} (TR.s-ffi k h m ss) {x} eq | no _ = sigConc ss eq

-- The declared type, read back, is the declaration's.
module _ (δ : SM.DefSem) where

  impEnv : ∀ {imps} → ImpSig S imps → ImpMeanings imps
  impEnv TR.[]                          = tt
  impEnv (TR.i-def {x = x} {T = T} d e is) = subst id (⟦wk₀⟧ᵛ T) (impSem δ {∅ₖ} {x} (def d e)) , impEnv is

  defEnv : ∀ {ps} → TeleSig S ps → DefMeanings (C.buildPolyCtx ps)
  defEnv TR.[]                        = tt
  defEnv (TR.t-def {p = p} d e ts)    = (λ U ki → entrySem δ d {pfunType p} e ki) , defEnv ts

  ----------------------------------------------------------------------
  -- Agreement
  ----------------------------------------------------------------------

  agree-imp : ∀ {imps} (is : ImpSig S imps) {Δ : KCtx 0} {x U} (lk : lookupImport imps x ≡ just U)
            → subst id (sym (⟦wk₀⟧ᵛ U)) (impAt imps x (impEnv is) lk) ≡ impSem δ {Δ} (impView is lk)
  agree-imp TR.[] ()
  agree-imp {(n , T₀) ∷ rest} (TR.i-def d e is) {x = x} lk with StrProp._≟_ n x
  ... | yes refl with lk
  ...   | refl = trans (subst-sym-subst (⟦wk₀⟧ᵛ T₀)) (refSemAt-Δ δ d e none (λ ()) (λ ()))
  agree-imp {(n , T₀) ∷ rest} (TR.i-def d e is) lk | no _ = agree-imp is lk

  agree-def : ∀ {ps} (ts : TeleSig S ps) {Δ : KCtx 0} {U : Type} {x sc body prefix}
                (lp : lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix)) (ki : KindedInstance Δ sc U)
            → defAt (C.buildPolyCtx ps) x (defEnv ts) lp U ki ≡ entrySem δ (proj₁ (telFind ts lp)) {sc} (proj₂ (telFind ts lp)) ki
  agree-def TR.[] () ki
  agree-def {Parser.mkPolyFunInfo n ty b ∷ ps} (TR.t-def d e ts) {x = x} lp ki with StrProp._≟_ n x
  ... | yes refl with lp
  ...   | refl = refl
  agree-def {Parser.mkPolyFunInfo n ty b ∷ ps} (TR.t-def d e ts) lp ki | no _ = agree-def ts lp ki

  -- Plan 0.105 (D257 amendment 2): the scope's environment runs in the core's
  -- world — its signature with its implementation. D274: a reference to Σ
  -- reads the declaration the scope's signature correspondence records.
  -- A declaration of Σ means the Spec's reference to it.
  sigEnv : ∀ {sg} → SigSig sg → ∀ {cn T} → WordName cn → lookupImport sg (showCanonical cn) ≡ just T → IsConcrete T → ⟦ T ⟧ᵛ
  sigEnv ss {cn} {T} wn lk k = subst id (⟦wk₀⟧ᵛ T) (sigSem δ cn wn k (sigAt ss lk))

  envOf : ∀ {sg imps ps} → SigSig sg → ImpSig S imps → TeleSig S ps → Meanings (C.buildPolyCtx ps) imps sg
  envOf ss is ts = meanings (defEnv ts) (impEnv is) (λ {cn} {T} wn lk k → sigEnv ss {cn} {T} wn lk k)

  agree-res : ∀ {sg} (ss : SigSig sg) {cn T} (wn : WordName cn) (lk : lookupImport sg (showCanonical cn) ≡ just T) (k : IsConcrete T)
            → subst id (sym (⟦wk₀⟧ᵛ T)) (sigEnv ss {cn} wn lk k) ≡ sigSem δ cn wn k (sigAt ss lk)
  agree-res ss {cn} {T} wn lk k = subst-sym-subst (⟦wk₀⟧ᵛ T)

  agree : ∀ {sg imps ps} (ss : SigSig sg) (is : ImpSig S imps) (ts : TeleSig S ps)
        → Agree (viewOf ss is ts) (envOf ss is ts) δ
  agree ss is ts = record
    { agree-inst      = λ lp ki → agree-def ts lp ki
    ; agree-import    = λ lk → agree-imp is lk
    ; agree-resolved  = λ wn lk k → agree-res ss wn lk k
    }
