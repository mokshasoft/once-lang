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
--   * a definition means its core entry at the instance (`refSem`);
--   * an FFI declaration means its contract (`sigOpRefᵛ`).
-- The one fact not about `δ` is that a qualified or resolved (not own) name
-- never finds a definition: a definition's name is a valid identifier (the
-- extractor's guard), and such a name is not (it has a dot, or is empty).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)
open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; sigOf)
open import Once.Denotation.TraceMonad using (interp)

open import Once.Spec.Contract using (ISig)
module Once.Adequacy.CoreEnv (fmt : TargetNum) {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Data.String using (String) renaming ()
import Data.String.Properties as StrProp
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Compile as C
open C.PolyFunInfo using (pfunType)
open import Once.Type.Rigid using (KindedInstance; ground-kinded)
open import Once.TypeCheck.Classify using (lookupImport; lookupPolyPrefix)
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.Meaning using (DefMeanings; ImpMeanings; Meanings; meanings)
import Once.Spec.Core.Meaning S as GM
import Once.Spec.Core.Translate as TR
open TR using (SigSig; ImpSig; TeleSig; mono-inst; poly-inst; telFind; viewOf) renaming (impAt to impView; sigAt to sigView)
open import Once.Spec.Elaboration S using (Declared)
open import Once.Adequacy.CoreMeaningBridge fmt S using (refSem; impSem; Agree)

------------------------------------------------------------------------
-- The environment of a scope, from the core's
------------------------------------------------------------------------

module _ (δ : GM.DefSem) where

  impEnv : ∀ {imps} → ImpSig S imps → ImpMeanings imps
  impEnv TR.[]                                = tt
  impEnv (TR.i-def d e is)                    = refSem δ (mono-inst {S = S} e) , impEnv is

  defEnv : ∀ {ps} → TeleSig S ps → DefMeanings (C.buildPolyCtx ps)
  defEnv TR.[]                        = tt
  defEnv (TR.t-def {p = p} d e ts)    = (λ U ki → refSem δ (poly-inst {S = S} {sc = pfunType p} e ki)) , defEnv ts


  ----------------------------------------------------------------------
  -- Agreement
  ----------------------------------------------------------------------

  agree-imp : ∀ {imps} (is : ImpSig S imps) {x U} (lk : lookupImport imps x ≡ just U)
            → impAt imps x (impEnv is) lk ≡ impSem δ (impView {S = S} is lk)
  agree-imp TR.[] ()
  agree-imp {(n , T₀) ∷ rest} (TR.i-def d e is) {x} lk with StrProp._≟_ n x
  ... | yes refl with lk
  ...   | refl = refl
  agree-imp {(n , T₀) ∷ rest} (TR.i-def d e is) {x} lk | no _ = agree-imp is lk

  agree-def : ∀ {ps} (ts : TeleSig S ps) {x sc body prefix U}
                (lp : lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix)) (ki : KindedInstance sc U)
            → defAt (C.buildPolyCtx ps) x (defEnv ts) lp U ki ≡ refSem δ (poly-inst {S = S} {sc = sc} (proj₂ (telFind {S = S} ts lp)) ki)
  agree-def TR.[] () ki
  agree-def {C.mkPolyFunInfo n ty b ∷ ps} (TR.t-def d e ts) {x} lp ki with StrProp._≟_ n x
  ... | yes refl with lp
  ...   | refl = refl
  agree-def {C.mkPolyFunInfo n ty b ∷ ps} (TR.t-def d e ts) {x} lp ki | no _ = agree-def ts lp ki

  -- Plan 0.105 (D257 amendment 2): the scope's environment runs in the core's
  -- world — its signatures with its implementation. D274: a reference to Σ
  -- reads the declaration the scope's signature correspondence records.
  envOf : ∀ {sg imps ps} → SigSig (sigOf S) sg → ImpSig S imps → TeleSig S ps → Meanings (C.buildPolyCtx ps) imps sg
  envOf ss is ts = meanings (defEnv ts) (impEnv is) (interp (sigOf S) (GM.impl δ))
    (λ lk → Declared.member (sigView {S = S} ss lk))
    (λ lk → Declared.member (sigView {S = S} ss lk))

  -- THE AGREEMENT, by construction.
  agree : ∀ {sg imps ps} (ss : SigSig (sigOf S) sg) (is : ImpSig S imps) (ts : TeleSig S ps)
        → Agree (viewOf {S = S} ss is ts) (envOf ss is ts) δ
  agree ss is ts = record
    { agree-inst      = λ lp ng ki → agree-def ts lp ki
    ; agree-ground    = λ {x} {sc} lp g → agree-def ts lp (ground-kinded sc g)
    ; agree-import    = λ lk → agree-imp is lk
    ; agree-qualified = λ lk k → refl
    ; agree-resolved  = λ lk k → refl
    ; agree-world     = refl
    }
