-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.Internal.Core.Translate — plan 0.103 phase 6c: MODULES → PROGRAMS.
--
-- INTERNAL (D333). A well-typed module (the surface telescope, D241) IS a Spec core
-- program (D239) over a signature `Σ` that declares its FFI entries: walking it in declaration order,
--   * an FFI declaration extends the signature Σ in scope, never the
--     definitions (D274): a reference to it is a `sigop`;
--   * a monomorphic definition becomes an arity-0 entry, its body elaborated
--     (6b) in its scope;
--   * a polymorphic definition becomes a `∀` entry: its body, typed once over
--     its parameters, elaborated there (plan 0.122: no abstraction step);
--   * `main` — the first `main : Eff Unit Unit`, exactly as the compiler finds it —
--     is an entry like any other (D253); the program runs a REFERENCE to it,
--     and its telescope is the whole module.
-- The correspondence between the surface scope and the core signature
-- (`ImpSig`/`TeleSig`) is what the elaboration's `View` is built from.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Internal.Core.Translate (Σ : Signature) where

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe
import Once.Internal.Typing.Scope
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
open import Once.Internal.Name using (showCanonical)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type.Instance using (rigidOf; kindsOf)
open import Once.Internal.Type.Schema using (schemaOf)
open import Once.Internal.Core.Decl using (declS)
import Once.Compile as C
import Once.Parser as Parser
open Parser.FunInfo using (funName; funBody; funType)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.Internal.Typing.Scope using (lookupImport; lookupPolyPrefix)
open import Once.Internal.Context as Ctx using (Usage)
open import Once.Spec.Context using ([])
import Once.Spec.Context as SCx
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_)
open import Once.Internal.Module using (Scope; emptyScope; ModTele; teleSig; []; ffi; mono; poly; MainIn; EffUU; ctxOf; ctxOfAt; addImp; MonoBody)
import Once.Internal.Module as Mod
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.Spec.Core.Syntax using (Defs; _▷_; _!!_; Schema; schema)
import Once.Spec.Core.Syntax as SCS
open import Once.Spec.Core.Program Σ using (Tele; def; Entry; entry)
open import Once.Internal.Core.Telescope Σ using (Program; program)
open import Once.Spec.Sub using (_<:_)
open import Once.Type.Sub using (_<:?_)
import Once.Spec.Core.Typing as Ty
import Once.Internal.Elaboration as E

monoSchema : Type → Schema
monoSchema ty = schema 0 ∅ₖ ty

-- The surface scope against the table: each FFI declaration is one of Σ's
-- (honest, under its name), each monomorphic definition an arity-0 entry,
-- each telescope definition an entry at its schema.
data SigSig : List _ → Set where
  []    : SigSig []
  s-ffi : ∀ {x T sg} → IsConcrete T → HonestFFI T → (∀ {c} → showCanonical c ≡ x → (c ∶ declS T) ∈ Σ) → SigSig sg
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

  module ES = E Σ S

  impAt : ∀ {imps} → ImpSig S imps → ∀ {x T′} → lookupImport imps x ≡ just T′ → ES.ImportAt x T′
  impAt [] ()
  impAt {(n , T₀) ∷ rest} (i-def d e is) {x} eq with StrProp._≟_ n x
  ... | yes _ with just-injective eq
  ...   | refl = ES.def d e
  impAt {(n , T₀) ∷ rest} (i-def d e is) {x} eq | no _ = impAt is eq

  sigAt : ∀ {sg} → SigSig sg → ∀ {x T′} → lookupImport sg x ≡ just T′ → ES.Declared x T′
  sigAt [] ()
  sigAt {(n , T₀) ∷ rest} (s-ffi k h m ss) {x} eq with StrProp._≟_ n x
  ... | yes refl with just-injective eq
  ...   | refl = ES.declared h m
  sigAt {(n , T₀) ∷ rest} (s-ffi k h m ss) {x} eq | no _ = sigAt ss eq

  telFind : ∀ {ps} → TeleSig S ps → ∀ {x sc body prefix}
          → lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix)
          → Σ-syntax (Fin s) (λ d → S !! d ≡ schemaOf sc)
  telFind [] ()
  telFind {p ∷ ps} (t-def d e ts) {x} eq with StrProp._≟_ (pfunName p) x
  ... | yes _ with just-injective eq
  ...   | refl = d , e
  telFind {p ∷ ps} (t-def d e ts) {x} eq | no _ = telFind ts eq

  viewOf : ∀ {sg imps ps} → SigSig sg → ImpSig S imps → TeleSig S ps → ES.View imps sg (C.buildPolyCtx ps)
  viewOf ss is ts = record
    { imported = impAt is
    ; declares = sigAt ss
    ; entry    = λ lp → proj₁ (telFind ts lp)
    ; entryIs  = λ lp → proj₂ (telFind ts lp)
    }

private
  u0 : ∀ {m s} {S : Defs s} {Δ : Once.Spec.Type.KCtx m} {Ψ : Usage 0} {t A π}
     → Ty._⊩_⊢[_]_∷_!_ Σ S Δ SCx.∅ Ψ t A π → Ty._⊩_⊢[_]_∷_!_ Σ S Δ SCx.∅ [] t A π
  u0 {Ψ = []} d = d

elabM : ∀ {s} {S : Defs s} (ft : Data.Maybe.Maybe Type) {ctx : Once.Internal.Typing.Scope.NamedCtx 0} {e ty Ψ}
      → E.Views Σ S ctx → MonoBody ft ctx e ty Ψ
      → E.Elab Σ S (Once.Internal.Typing.Scope.NamedCtx.kinds ctx) (Once.Internal.Typing.Scope.NamedCtx.debruijn ctx) Ψ ty
elabM {S = S} (just _) V D = E.elabᶜ Σ S V D
elabM {S = S} nothing  V D = E.elabᵢ Σ S V D

-- A monomorphic definition: an arity-0 entry, its body elaborated in scope.
monoDef : ∀ {s} {S : Defs s} {sc fi ty Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
        → MonoBody (funType fi) (ctxOf sc) (funBody fi) ty Ψ → Tele (S ▷ monoSchema ty)
monoDef {S = S} {fi = fi} {ty = ty} tl ss is ts D =
  let (t , d) = elabM {S = S} (funType fi) (viewOf ss is ts) D in def tl (monoSchema ty) t (u0 d)

-- A telescope definition: an entry at its schema, its body elaborated over its
-- parameters.
polyDef : ∀ {s} {S : Defs s} {sc pfi Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
        → ctxOfAt (kindsOf (pfunType pfi)) sc ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ → Tele (S ▷ schemaOf (pfunType pfi))
polyDef {S = S} {pfi = pfi} tl ss is ts D =
  let (t , d) = E.elabᶜ Σ S (viewOf ss is ts) D in def tl (schemaOf (pfunType pfi)) t (u0 d)

programAt : ∀ {s} {S : Defs s} → Tele S → (d : Fin s) → Entry (S !! d) → Program
programAt tl d e = program tl d e

mainEntry : ∀ {ty} → ty <: EffUU → Entry (monoSchema ty)
mainEntry p = entry p

-- Each FFI declaration of the module is one of Σ's, under its name.
SigIn : ∀ {sc es} → ModTele sc es → Set
SigIn mt = ∀ {x T} → (x , T) ∈ teleSig mt → ∀ {c} → showCanonical c ≡ x → (c ∶ declS T) ∈ Σ

mutual
  toProgram : ∀ {s} {S : Defs s} {sc es} → Tele S → SigSig (Scope.sig sc) → ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc)
            → (mt : ModTele sc es) → MainIn mt → SigIn mt → Program
  toProgram tl ss is ts [] () u
  toProgram tl ss is ts (ffi _ _ c h g rest) mi u = toProgram tl (s-ffi c h (u (here refl)) ss) is ts rest mi (λ m → u (there m))
  toProgram {S = S} {sc = sc} tl ss is ts (poly {pfi = pfi} {Ψ = Ψ} pr D rest) mi u =
    toProgram (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts D)
              ss (wkI is) (t-def zero refl (wkT ts)) rest mi u
  toProgram {S = S} {sc = sc} tl ss is ts (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr g D rest) mi u =
    monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi u

  monoPick : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
           → (D : MonoBody (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → ((funName fi ≡ "main") × (ty <: EffUU)) ⊎ MainIn rest
           → SigIn rest → Program
  monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest (inj₁ (_ , e)) u =
    monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest e u
  monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest (inj₂ mi′) u =
    monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi′ (funName fi ≟str "main") (ty <:? EffUU) u

  monoDispatch : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
               → (D : MonoBody (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
               → (rest : ModTele (addImp sc (funName fi) ty) es) → MainIn rest
               → Dec (funName fi ≡ "main") → Dec (ty <: EffUU) → SigIn rest → Program
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi′ (yes _) (yes e) u =
    monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest e u
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi′ (yes _) (no _) u =
    monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi′ u
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi′ (no _) _ u =
    monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi′ u

  monoNext : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
           → (D : MonoBody (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → MainIn rest → SigIn rest → Program
  monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest mi′ u =
    toProgram (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D)
              ss (impDefs (funName fi ==str "main") is) (wkT ts) rest mi′ u

  -- `main`: an entry like any other (D253); the program refers to it.
  monoHere : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
           → (D : MonoBody (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → ty <: EffUU → SigIn rest → Program
  monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D rest e u =
    toProgramFrom (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D)
                  ss (impDefs (funName fi ==str "main") is) (wkT ts) zero (mainEntry e) rest u

  -- The entries after `main`: the telescope goes on, `main`'s entry is weakened.
  toProgramFrom : ∀ {s} {S : Defs s} {sc es} → Tele S → SigSig (Scope.sig sc) → ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc)
                → (d : Fin s) → Entry (S !! d) → (mt : ModTele sc es) → SigIn mt → Program
  toProgramFrom tl ss is ts d e [] u = programAt tl d e
  toProgramFrom tl ss is ts d e (ffi _ _ c h g rest) u = toProgramFrom tl (s-ffi c h (u (here refl)) ss) is ts d e rest (λ m → u (there m))
  toProgramFrom {S = S} {sc = sc} tl ss is ts d e (poly {pfi = pfi} {Ψ = Ψ} pr D rest) u =
    toProgramFrom (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts D)
                  ss (wkI is) (t-def zero refl (wkT ts)) (suc d) e rest u
  toProgramFrom {S = S} {sc = sc} tl ss is ts d e (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr g D rest) u =
    toProgramFrom (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D)
                  ss (impDefs (funName fi ==str "main") is) (wkT ts) (suc d) e rest u

-- A typed module's core program, over the signatures it is compiled against.
toProgram₀ : ∀ {es} (mt : ModTele emptyScope es) → MainIn mt → SigIn mt → Program
toProgram₀ mt mi u = toProgram {S = SCS.[]} Tele.[] [] [] [] mt mi u
