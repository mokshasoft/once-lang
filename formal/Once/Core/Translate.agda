-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.Core.Translate — plan 0.103 phase 6c: a module's scope against
-- its core table.
--
-- A well-typed module (the surface telescope, D241) IS a Spec core
-- program (D239) over a signature `Σ` that declares its FFI entries
-- (`Adequacy.ModuleProgram` builds it). Here: the correspondence between the
-- surface scope and the core table — each FFI declaration one of Σ's
-- (`SigSig`), each monomorphic definition an arity-0 entry (`ImpSig`), each
-- telescope definition an entry at its schema (`TeleSig`) — which the
-- checker's `View` is built from.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Context using (Usage)

module Once.Core.Translate (Σ : Signature) where

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe
import Once.TypeCheck.Scope
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using () renaming (_≟_ to _≟str_; _==_ to _==str_)
open import Data.Bool using (Bool; true; false)
import Data.String.Properties as StrProp
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

import Once.Spec.Grade as T
open import Once.Spec.Type using (Type; ∅ₖ)
import Once.Spec.Type
open import Once.Spec.Signature using (_∶_)
open import Once.Spec.Name using (CanonicalName)
open import Once.Name using (showCanonical; WordName)
open import Once.Type.Honest using (HonestFFI)
open import Once.Type.Concrete using (IsConcrete)
open import Once.Type.Instance using (rigidOf; kindsOf)
open import Once.Type.Schema using (schemaOf)
open import Once.Core.Decl using (declS)
import Once.Compile as C
import Once.Parser as Parser
open Parser.FunInfo using (funName; funBody; funType)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.TypeCheck.Scope using (lookupImport; lookupPolyPrefix)
import Once.Spec.Context as Ctx
open import Once.Spec.Context using ([])
import Once.Spec.Context as SCx
open import Once.Module using (Scope; emptyScope; ModTele; teleSig; []; ffi; mono; poly; MainIn; EffUU; ctxOf; ctxOfAt; addImp)
import Once.Module as Mod
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.Spec.Core.Syntax using (Defs; _▷_; _!!_; Schema; schema)
import Once.Spec.Core.Syntax as SCS
open import Once.Spec.Core.Program Σ using (Tele; def; Entry; entry)
open import Once.Internal.Core.Telescope Σ using (Program; program)
open import Once.Spec.Sub using (_<:_)
open import Once.Type.SubDecide using (_<:?_)
import Once.Spec.Core.Typing as Ty
import Once.TypeCheck.View as TView

monoSchema : Type → Schema
monoSchema ty = schema 0 ∅ₖ ty

-- The surface scope against the table: each FFI declaration is one of Σ's
-- (honest, under its name), each monomorphic definition an arity-0 entry,
-- each telescope definition an entry at its schema.
data SigSig : List _ → Set where
  []    : SigSig []
  s-ffi : ∀ {x T sg} → IsConcrete T → HonestFFI T → (∀ {c} → WordName c → showCanonical c ≡ x → (c ∶ declS T) ∈ Σ) → SigSig sg
        → SigSig ((x , T) ∷ sg)

data ImpSig {s} (S : Defs s) : C.FunCtx → Set where
  []    : ImpSig S []
  i-def : ∀ {x T imps} (d : Fin s) → S !! d ≡ monoSchema T → ImpSig S imps → ImpSig S ((x , T) ∷ imps)

data TeleSig {s} (S : Defs s) : List Parser.PolyFunInfo → Set where
  []    : TeleSig S []
  t-def : ∀ {p ps} (d : Fin s) → S !! d ≡ schemaOf (pfunType p) → TeleSig S ps → TeleSig S (p ∷ ps)

wkI : ∀ {s} {S : Defs s} {sc : Schema} {imps} → ImpSig S imps → ImpSig (S ▷ sc) imps
wkI []              = []
wkI (i-def d e is)  = i-def (suc d) e (wkI is)

impDefs : ∀ {s} {S : Defs s} (b : Bool) {x T imps} → ImpSig S imps → ImpSig (S ▷ monoSchema T) (C.extendDefs-at b imps x T)
impDefs true  is = wkI is
impDefs false is = i-def zero refl (wkI is)

wkT : ∀ {s} {S : Defs s} {sc : Schema} {ps} → TeleSig S ps → TeleSig (S ▷ sc) ps
wkT []             = []
wkT (t-def d e ts) = t-def (suc d) e (wkT ts)

module _ {s} {S : Defs s} where

  module VS = TView Σ S

  impAt : ∀ {imps} → ImpSig S imps → ∀ {x T′} → lookupImport imps x ≡ just T′ → VS.ImportAt x T′
  impAt [] ()
  impAt {(n , T₀) ∷ rest} (i-def d e is) {x} eq with StrProp._≟_ n x
  ... | yes _ with just-injective eq
  ...   | refl = VS.def d e
  impAt {(n , T₀) ∷ rest} (i-def d e is) {x} eq | no _ = impAt is eq

  sigAt : ∀ {sg} → SigSig sg → ∀ {x T′} → lookupImport sg x ≡ just T′ → VS.Declared x T′
  sigAt [] ()
  sigAt {(n , T₀) ∷ rest} (s-ffi k h m ss) {x} eq with StrProp._≟_ n x
  ... | yes refl with just-injective eq
  ...   | refl = VS.declared h m
  sigAt {(n , T₀) ∷ rest} (s-ffi k h m ss) {x} eq | no _ = sigAt ss eq

  telFind : ∀ {ps} → TeleSig S ps → ∀ {x sc body prefix}
          → lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix)
          → Σ-syntax (Fin s) (λ d → S !! d ≡ schemaOf sc)
  telFind [] ()
  telFind {p ∷ ps} (t-def d e ts) {x} eq with StrProp._≟_ (pfunName p) x
  ... | yes _ with just-injective eq
  ...   | refl = d , e
  telFind {p ∷ ps} (t-def d e ts) {x} eq | no _ = telFind ts eq

  viewOf : ∀ {sg imps ps} → SigSig sg → ImpSig S imps → TeleSig S ps → VS.View imps sg (C.buildPolyCtx ps)
  viewOf ss is ts = record
    { imported = impAt is
    ; declares = sigAt ss
    ; entry    = λ lp → proj₁ (telFind ts lp)
    ; entryIs  = λ lp → proj₂ (telFind ts lp)
    }

u0 : ∀ {m s} {S : Defs s} {Δ : Once.Spec.Type.KCtx m} {Ψ : Usage 0} {t A π}
   → Ty._⊩_⊢[_]_∷_!_ Σ S Δ SCx.∅ Ψ t A π → Ty._⊩_⊢[_]_∷_!_ Σ S Δ SCx.∅ [] t A π
u0 {Ψ = []} d = d

programAt : ∀ {s} {S : Defs s} → Tele S → (d : Fin s) → Entry (S !! d) → Program
programAt tl d e = program tl d e

mainEntry : ∀ {ty} → ty <: EffUU → Entry (monoSchema ty)
mainEntry p = entry p

-- Each FFI declaration of the module is one of Σ's, under its name.
SigIn : ∀ {sc es} → ModTele sc es → Set
SigIn mt = ∀ {x T} → (x , T) ∈ teleSig mt → ∀ {c} → WordName c → showCanonical c ≡ x → (c ∶ declS T) ∈ Σ
