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
--   * an FFI declaration means its contract (`sigOpRefᵛ`), in the world of
--     the core's signature `Σ` and implementation.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Adequacy.CoreEnv (fmt : TargetNum) (Σ : Signature) {s : ℕ} (S : Defs s) where

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
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Internal.Contract using (ISig)
open import Once.Internal.Type using (wk₀; none)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Weaken using (⟦wk₀⟧ᵛ)
open import Once.Internal.Graded using (⟦_⟧ᵛ)
open import Once.Internal.GradedOps using (sigOpRefᵛ)
open import Once.Internal.Trace using (interp)
open import Once.Internal.Typing.Scope using (lookupImport; lookupPolyPrefix)
open import Once.Internal.Core.Decl using (toISig; ∈-toISig; ⌜⌝ᵈ-concrete; declS; ⌜declS⌝)
open import Once.Internal.Core.TySubstZero Σ S using (⟨⟩-0)
open import Once.Functor.Translate using (IsConcrete-irrelevant)
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.Meaning using (DefMeanings; ImpMeanings; Meanings; meanings)
import Once.Internal.Core.Meaning Σ S as GM
import Once.Internal.Core.Translate Σ as TR
open TR using (SigSig; ImpSig; TeleSig; viewOf; telFind; sigAt) renaming (impAt to impView)
open import Once.Internal.Elaboration Σ S using (Declared; def)
open import Once.Adequacy.CoreMeaningBridge fmt Σ S using (refSemAt-Δ; entrySem; impSem; sigSem; Agree)

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
declT : ∀ {x T} → IsConcrete T → Declared x T → ⌜ declS T ⌝ᵈ ≡ T
declT {T = T} k D = trans (⌜declS⌝ {0} k (Declared.honest D)) (⟨⟩-0 none T)

sigRes : ∀ {sg} → SigSig sg → ∀ {cn T} → WordName cn → lookupImport sg (showCanonical cn) ≡ just T → (showCanonical cn , T) ∈ toISig Σ
sigRes ss {cn} wn lk =
  subst (λ X → (showCanonical cn , X) ∈ toISig Σ) (declT (sigConc ss lk) (sigAt ss lk))
        (∈-toISig (Declared.member (sigAt ss lk) {cn} wn refl))

-- A reference along a type equation is the reference at the other type.
sigOpRef-≅ : ∀ {I : ISig} (impl : _) (cn : CanonicalName) {A B : Type} (e : A ≡ B) (kA : IsConcrete A) (kB : IsConcrete B)
               (m : (showCanonical cn , A) ∈ I)
           → sigOpRefᵛ {A = B} fmt I impl cn kB (subst (λ X → (showCanonical cn , X) ∈ I) e m) ≅ sigOpRefᵛ {A = A} fmt I impl cn kA m
sigOpRef-≅ impl cn refl kA kB m rewrite IsConcrete-irrelevant kA kB = H.refl

------------------------------------------------------------------------
-- The environment of a scope, from the core's
------------------------------------------------------------------------

module _ (δ : GM.DefSem) where

  impEnv : ∀ {imps} → ImpSig S imps → ImpMeanings imps
  impEnv TR.[]                          = tt
  impEnv (TR.i-def {x = x} {T = T} d e is) = subst id (⟦wk₀⟧ᵛ {0} T) (impSem δ {∅ₖ} {x} (def d e)) , impEnv is

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
  envOf : ∀ {sg imps ps} → SigSig sg → ImpSig S imps → TeleSig S ps → Meanings (C.buildPolyCtx ps) imps sg
  envOf ss is ts = meanings (defEnv ts) (impEnv is) (interp (toISig Σ) (GM.impl δ)) (λ {cn} wn lk → sigRes ss {cn} wn lk)

  agree-res : ∀ {sg} (ss : SigSig sg) {cn T} (wn : WordName cn) (lk : lookupImport sg (showCanonical cn) ≡ just T) (k : IsConcrete T)
            → subst id (sym (⟦wk₀⟧ᵛ T)) (sigOpRefᵛ {A = T} fmt (toISig Σ) (GM.impl δ) cn k (sigRes ss {cn} wn lk))
              ≡ sigSem δ cn wn k (sigAt ss lk)
  agree-res ss {cn} {T} wn lk k =
    H.≅-to-≡ (H.trans (H.≡-subst-removable id (sym (⟦wk₀⟧ᵛ T)) _)
             (H.trans (sigOpRef-≅ (GM.impl δ) cn (declT (sigConc ss lk) D) (⌜⌝ᵈ-concrete (declS T)) k m₀)
                      (H.sym (H.≡-subst-removable (λ X → ⟦ X ⟧ᵛ) (⌜declS⌝ k (Declared.honest D)) _))))
    where
      D  = sigAt ss lk
      m₀ = ∈-toISig (Declared.member D {cn} wn refl)

  -- THE AGREEMENT, by construction.
  agree : ∀ {sg imps ps} (ss : SigSig sg) (is : ImpSig S imps) (ts : TeleSig S ps)
        → Agree (viewOf ss is ts) (envOf ss is ts) δ
  agree ss is ts = record
    { agree-inst      = λ lp ki → agree-def ts lp ki
    ; agree-import    = λ lk → agree-imp is lk
    ; agree-resolved  = λ wn lk k → agree-res ss wn lk k
    }
