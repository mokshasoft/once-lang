-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Module — what it MEANS for a resolved module to be well-typed
-- and to have a valid entry point (Plan 0.84). No proof lives here.
--
-- READ THIS BEFORE TRUSTING `correct`. Unlike `Once.Spec.Parsing`, this
-- module is NOT clean, and the split exists to make that visible rather than
-- to hide it behind a proof module:
--
--   * `ModuleTyped m` is defined by RUNNING the front end —
--     `ModuleTyped-ef m (extractFunctions (extractAliases m) m)`. The spec's
--     notion of "well-typed" therefore quantifies over whatever the extractor
--     happens to produce, instead of over the module's own syntax.
--   * `AllFunsTyped` names `ctxWithImportsAndPolys` from
--     `Once.TypeCheck.Elaborate` — the ELABORATOR — and `resolveFunType`,
--     `extendFunCtx`, `buildPolyCtx`, `collectSigEffects` from `Once.Compile`.
--
-- Its BODY premise is honest: `_⊢ᶜ_∶_⨾_`, the declarative judgment, with no
-- elaborator function in it. It is the CONTEXT CONSTRUCTION and the function
-- list that come from the implementation.
--
-- Recorded as D137's open hole; **plan 0.59 owns closing it.** Do not paper
-- over it by moving these definitions back next to their proofs.
------------------------------------------------------------------------

module Once.Spec.Module where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Spec.Contract using (ISig)

open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.Type.Rigid using (rigidOf; RigidFree)
open import Once.Functor.Translate using (IsConcrete)
open import Once.Type.Honest using (HonestFFI)
open import Once.Surface.Context using (zeroUsage)
import Once.Compile as C
import Once.Parser.Module.Core as P
open import Once.TypeCheck.Classify using (NamedCtx; ctxWithImportsAndPolys; topCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)

open C.FunInfo using (funName; funBody; funType; funIsPrimitive)
open C.PolyFunInfo using (pfunName; pfunType; pfunBody)

------------------------------------------------------------------------
-- D241/D242 (plan 0.103 6c′): THE MODULE IS ONE TELESCOPE.
--
-- Every definition is typed in its SCOPE — exactly the definitions declared
-- before it — so general recursion (a definition seeing itself, or a cycle
-- through a later one) cannot be stated. It is the surface twin of the core
-- `Tele` (D239), and elaborates into it entry by entry.
------------------------------------------------------------------------

-- What is in scope at an entry, latest first. D274: the program's SIGNATURE Σ
-- (its FFI declarations — generators, assumed) is kept apart from its
-- DEFINITIONS (built from them): a reference to Σ is a SigOp, a reference to a
-- definition is a call of it.
record Scope : Set where
  constructor scope
  field
    sig  : ISig                  -- the signatures declared so far (Σ)
    imps : C.FunCtx              -- monomorphic definitions
    tele : List C.PolyFunInfo    -- telescope definitions

emptyScope : Scope
emptyScope = scope [] C.emptyFunCtx []

ctxOf : Scope → NamedCtx
ctxOf sc = ctxWithImportsAndPolys (topCtx (Scope.sig sc) (Scope.imps sc)) (C.buildPolyCtx (Scope.tele sc))

addSig : Scope → String → Type → Scope
addSig sc x ty = scope ((x , ty) ∷ Scope.sig sc) (Scope.imps sc) (Scope.tele sc)

addImp : Scope → String → Type → Scope
addImp sc x ty = scope (Scope.sig sc) (C.extendFunCtx (Scope.imps sc) x ty) (Scope.tele sc)

addPoly : Scope → C.PolyFunInfo → Scope
addPoly sc p = scope (Scope.sig sc) (Scope.imps sc) (p ∷ Scope.tele sc)

data ModTele : Scope → List C.Entry → Set where
  []   : ∀ {sc} → ModTele sc []
  -- An FFI declaration: its type, CONCRETE — a SigOp is a first-order
  -- contract (D061/D071) — HONEST (D231: `pure` means no side effects), and
  -- GROUND (D243: it cannot mention a definition's parameter). No body: it
  -- is a GENERATOR, and extends the signature Σ, not the definitions (D274).
  ffi  : ∀ {sc fi ty es}
       → funIsPrimitive fi ≡ true → funType fi ≡ just ty → IsConcrete ty → HonestFFI ty → RigidFree ty
       → ModTele (addSig sc (funName fi) ty) es
       → ModTele sc (C.e-fun fi ∷ es)
  -- A monomorphic definition, typed at its (declared or inferred) type.
  mono : ∀ {sc fi ty es Ψ}
       → funIsPrimitive fi ≡ false
       → C.resolveFunType (topCtx (Scope.sig sc) (Scope.imps sc)) (C.buildPolyCtx (Scope.tele sc)) (funType fi) (funBody fi) ≡ inj₂ ty
       → RigidFree ty                    -- D243: a monomorphic type is GROUND
       → ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ
       → ModTele (addImp sc (funName fi) ty) es
       → ModTele sc (C.e-fun fi ∷ es)
  -- D243: a telescope definition, typed ONCE, at its schema with rigid
  -- parameters. A use is at a kinded instance of it.
  poly : ∀ {sc pfi es Ψ}
       → ctxOf sc ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ
       → ModTele (addPoly sc pfi) es
       → ModTele sc (C.e-poly pfi ∷ es)

------------------------------------------------------------------------
-- Plan 0.105 (D257 amendment 2): THE INTERPRETATION SIGNATURES A MODULE IS
-- COMPILED AGAINST — its FFI declarations. Read off the entries (what
-- compiling a user program sees: each primitive's name and declared type),
-- and off a typing of them, which agree (`teleSig≡entrySig`): the signatures
-- do not depend on which derivation types the module.
------------------------------------------------------------------------

entrySig-fun : C.FunInfo → Bool → Maybe Type → ISig → ISig
entrySig-fun fi true  (just ty) rest = (funName fi , ty) ∷ rest
entrySig-fun fi true  nothing   rest = rest
entrySig-fun fi false _         rest = rest

entrySig : List C.Entry → ISig
entrySig []                = []
entrySig (C.e-fun fi ∷ es)  = entrySig-fun fi (funIsPrimitive fi) (funType fi) (entrySig es)
entrySig (C.e-poly _ ∷ es) = entrySig es

teleSig : ∀ {sc es} → ModTele sc es → ISig
teleSig []                                    = []
teleSig (ffi {fi = fi} {ty = ty} _ _ _ _ _ rest) = (funName fi , ty) ∷ teleSig rest
teleSig (mono _ _ _ _ rest)                   = teleSig rest
teleSig (poly _ rest)                         = teleSig rest

teleSig≡entrySig : ∀ {sc es} (mt : ModTele sc es) → teleSig mt ≡ entrySig es
teleSig≡entrySig []                                       = refl
teleSig≡entrySig (ffi {fi = fi} {ty = ty} ep et _ _ _ rest) rewrite ep | et = cong ((funName fi , ty) ∷_) (teleSig≡entrySig rest)
teleSig≡entrySig (mono {fi = fi} ep _ _ _ rest)            rewrite ep = teleSig≡entrySig rest
teleSig≡entrySig (poly _ rest)                            = teleSig≡entrySig rest

-- A module's signatures, when it extracts.
moduleSig-ef : (String ⊎ List C.Entry) → ISig
moduleSig-ef (inj₁ _)  = []
moduleSig-ef (inj₂ es) = entrySig es

moduleSig : P.Module → ISig
moduleSig m = moduleSig-ef (C.extractFunctions (C.extractAliases m) m)

ModuleTyped-ef : P.Module → (String ⊎ List C.Entry) → Set
ModuleTyped-ef m (inj₁ _)  = ⊥
ModuleTyped-ef m (inj₂ es) = ModTele emptyScope es

ModuleTyped : P.Module → Set
ModuleTyped m = ModuleTyped-ef m (C.extractFunctions (C.extractAliases m) m)

------------------------------------------------------------------------
-- The entry point: a monomorphic definition `main : IO Unit`.
------------------------------------------------------------------------

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- Every monomorphic definition named `main` is at `IO Unit` (the compiler's
-- entry point is at that type).
MainsEffUU : ∀ {sc es} → ModTele sc es → Set
MainsEffUU []                                  = ⊤
MainsEffUU (ffi _ _ _ _ _ rest)                = MainsEffUU rest
MainsEffUU (mono {fi = fi} {ty = ty} _ _ _ _ rest) = (funName fi ≡ "main" → ty ≡ EffUU) × MainsEffUU rest
MainsEffUU (poly _ rest)                       = MainsEffUU rest

-- Some monomorphic definition is `main : IO Unit`.
MainIn : ∀ {sc es} → ModTele sc es → Set
MainIn []                                  = ⊥
MainIn (ffi _ _ _ _ _ rest)                = MainIn rest
MainIn (mono {fi = fi} {ty = ty} _ _ _ _ rest) = ((funName fi ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest
MainIn (poly _ rest)                       = MainIn rest

HasValidMain-ef : ∀ (m : P.Module) (ef : String ⊎ List C.Entry) → ModuleTyped-ef m ef → Set
HasValidMain-ef m (inj₂ _) mt = MainsEffUU mt × MainIn mt

HasValidMain : ∀ (m : P.Module) → ModuleTyped m → Set
HasValidMain m mt = HasValidMain-ef m (C.extractFunctions (C.extractAliases m) m) mt
