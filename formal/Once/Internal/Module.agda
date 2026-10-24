-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Module — what it MEANS for a resolved module to be well-typed
-- and to have a valid entry point (Plan 0.84). No proof lives here.
--
-- READ THIS BEFORE TRUSTING `correct`. Unlike `Once.Internal.Parsing`, this
-- module is NOT clean, and the split exists to make that visible rather than
-- to hide it behind a proof module:
--
--   * `ModuleTyped m` is defined by RUNNING the front end —
--     `ModuleTyped-ef m (extractFunctions m)`. The spec's
--     notion of "well-typed" therefore quantifies over whatever the extractor
--     happens to produce, instead of over the module's own syntax.
--   * `AllFunsTyped` names `ctxWithImportsAndPolys` from
--     `Once.TypeCheck.Elaborate` — the ELABORATOR — and `resolveFunType`,
--     `extendFunCtx`, `buildPolyCtx`, `collectSigEffects` from `Once.Compile`.
--
-- Its BODY premise is the checker's own run with its witness: the Spec's
-- derivation and the term it realizes to (`MonoWit`, `TypeCheck.SpecWitness`;
-- plan 0.122). It is the CONTEXT CONSTRUCTION and the function list that come
-- from the implementation.
--
-- Recorded as D137's open hole; **plan 0.59 owns closing it.** Do not paper
-- over it by moving these definitions back next to their proofs.
------------------------------------------------------------------------

module Once.Internal.Module where

open import Once.Internal.Type.Instance using (kindsOf)
open import Once.TypeCheck.Classify using (ctxAt)
open import Once.Spec.Type using (KCtx)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; Σ; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Once.Internal.Contract using (ISig)

open import Once.Spec.Grade using (mk-kind; Many; eff)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Type using (Type; Ty; Unit; _⇒[_]_)
open import Once.Internal.Type.Instance using (rigidOf)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type.Honest using (HonestFFI)
import Once.Compile as C
open import Once.Internal.Principal using (PrincipalAt)
import Once.Parser as Parser
import Once.Parser.Module.Core as P
open import Once.Internal.Typing.Scope using (NamedCtx)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys; topCtx)
import Once.Internal.Context as Surface
import Once.Surface.Syntax as SS
open import Once.TypeCheck.SpecWitness using (WI; WC)
import Once.TypeCheck.Elaborate as TE
open import Data.Nat using (ℕ)
open import Once.Internal.Syntax using (RawExpr)

open Parser.FunInfo using (funName; funBody; funType; funIsPrimitive)
open Parser.PolyFunInfo using (pfunType; pfunBody)

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
    tele : List Parser.PolyFunInfo    -- telescope definitions

emptyScope : Scope
emptyScope = scope [] C.emptyFunCtx []

ctxOf : Scope → NamedCtx 0
ctxOf sc = ctxWithImportsAndPolys (topCtx (Scope.sig sc) (Scope.imps sc)) (C.buildPolyCtx (Scope.tele sc))

-- The scope where a polymorphic body is typed: over its parameters, of kinds Δ.
ctxOfAt : ∀ {m} → KCtx m → Scope → NamedCtx m
ctxOfAt Δ sc = ctxAt Δ (topCtx (Scope.sig sc) (Scope.imps sc)) (C.buildPolyCtx (Scope.tele sc))

addSig : Scope → String → Type → Scope
addSig sc x ty = scope ((x , ty) ∷ Scope.sig sc) (Scope.imps sc) (Scope.tele sc)

-- D324: `main` never enters the definitions' context (`C.extendDefs`).
addImp : Scope → String → Type → Scope
addImp sc x ty = scope (Scope.sig sc) (C.extendDefs (Scope.imps sc) x ty) (Scope.tele sc)

addPoly : Scope → Parser.PolyFunInfo → Scope
addPoly sc p = scope (Scope.sig sc) (Scope.imps sc) (p ∷ Scope.tele sc)

-- R8 (plan 0.121): a monomorphic definition's body — CHECKED at its signature,
-- or, without one, SYNTHESIZING its type (D323; the Spec's `w-sig`/`w-nosig`).
-- Its witness is the checker's own result: the term it built and the Spec's
-- derivation, whose realization that term is (`TypeCheck.SpecWitness`; plan
-- 0.122 §5.6).
CheckRun : ∀ {m} (ctx : NamedCtx m) → RawExpr → (A : Ty m) → Surface.Usage (NamedCtx.size ctx) → Set
CheckRun ctx e A Ψ = Σ[ eE ∈ SS.Expr (NamedCtx.debruijn ctx) Ψ A ] Σ[ d ∈ ℕ ] Σ[ f ∈ ℕ ] Σ[ w ∈ WC ctx e A Ψ eE ]
                       (TE.checkElabV ctx e A ≡ (TE.success Ψ eE d f , w))

MonoWit : Maybe Type → (ctx : NamedCtx 0) → RawExpr → Type → Surface.Usage (NamedCtx.size ctx) → Set
MonoWit (just _) ctx e ty Ψ = CheckRun ctx e ty Ψ
MonoWit nothing  ctx e ty Ψ = Σ[ eE ∈ SS.Expr (NamedCtx.debruijn ctx) Ψ ty ] Σ[ d ∈ ℕ ] Σ[ f ∈ ℕ ] Σ[ w ∈ WI ctx e ty Ψ eE ]
                                (TE.inferElabV ctx e ≡ (TE.success ty Ψ eE d f , w))

-- A pair, read along an equation on its first component.
pair-at : ∀ {a b} {A : Set a} {B : A → Set b} (r : Σ A B) {x : A} (q : proj₁ r ≡ x) → r ≡ (x , subst B q (proj₂ r))
pair-at (_ , _) refl = refl

data ModTele : Scope → List Parser.Entry → Set where
  []   : ∀ {sc} → ModTele sc []
  -- An FFI declaration: its type, CONCRETE — a SigOp is a first-order
  -- contract (D061/D071) — and HONEST (D231: `pure` means no side effects);
  -- it is ground (a `Type`, D243). No body: it
  -- is a GENERATOR, and extends the signature Σ, not the definitions (D274).
  ffi  : ∀ {sc fi ty es}
       → funIsPrimitive fi ≡ true → funType fi ≡ just ty → IsConcrete ty → HonestFFI ty
       → ModTele (addSig sc (funName fi) ty) es
       → ModTele sc (Parser.e-fun fi ∷ es)
  -- A monomorphic definition, typed and compiled at its (declared or
  -- synthesized) type `ty`, which is its PRINCIPAL type (D314/D321). `main`
  -- too: the entry converts it to `Eff Unit Unit` (D315, plan 0.121 R7).
  mono : ∀ {sc fi ty es Ψ}
       → funIsPrimitive fi ≡ false
       → C.resolveFunType (topCtx (Scope.sig sc) (Scope.imps sc)) (C.buildPolyCtx (Scope.tele sc)) (funType fi) (funBody fi) ≡ inj₂ ty
       → PrincipalAt (ctxOf sc) (funBody fi) ty
       → MonoWit (funType fi) (ctxOf sc) (funBody fi) ty Ψ
       → ModTele (addImp sc (funName fi) ty) es
       → ModTele sc (Parser.e-fun fi ∷ es)
  -- D243: a telescope definition, typed ONCE, over its schema's parameters
  -- (plan 0.122). A use is at a kinded instance of it.
  poly : ∀ {sc pfi es Ψ}
       → PrincipalAt (ctxOfAt (kindsOf (pfunType pfi)) sc) (pfunBody pfi) (rigidOf (pfunType pfi))
       → CheckRun (ctxOfAt (kindsOf (pfunType pfi)) sc) (pfunBody pfi) (rigidOf (pfunType pfi)) Ψ
       → ModTele (addPoly sc pfi) es
       → ModTele sc (Parser.e-poly pfi ∷ es)

------------------------------------------------------------------------
-- Plan 0.105 (D257 amendment 2): THE INTERPRETATION SIGNATURES A MODULE IS
-- COMPILED AGAINST — its FFI declarations. Read off the entries (what
-- compiling a user program sees: each primitive's name and declared type),
-- and off a typing of them, which agree (`teleSig≡entrySig`): the signatures
-- do not depend on which derivation types the module.
------------------------------------------------------------------------

entrySig-fun : Parser.FunInfo → Bool → Maybe Type → ISig → ISig
entrySig-fun fi true  (just ty) rest = (funName fi , ty) ∷ rest
entrySig-fun fi true  nothing   rest = rest
entrySig-fun fi false _         rest = rest

entrySig : List Parser.Entry → ISig
entrySig []                = []
entrySig (Parser.e-fun fi ∷ es)  = entrySig-fun fi (funIsPrimitive fi) (funType fi) (entrySig es)
entrySig (Parser.e-poly _ ∷ es) = entrySig es

teleSig : ∀ {sc es} → ModTele sc es → ISig
teleSig []                                    = []
teleSig (ffi {fi = fi} {ty = ty} _ _ _ _ rest) = (funName fi , ty) ∷ teleSig rest
teleSig (mono _ _ _ _ rest)                    = teleSig rest
teleSig (poly _ _ rest)                        = teleSig rest


-- A module's signatures, when it extracts.
moduleSig-ef : (String ⊎ List Parser.Entry) → ISig
moduleSig-ef (inj₁ _)  = []
moduleSig-ef (inj₂ es) = entrySig es

moduleSig : P.Resolved → ISig
moduleSig m = moduleSig-ef (Parser.extractFunctions m)

ModuleTyped-ef : P.Resolved → (String ⊎ List Parser.Entry) → Set
ModuleTyped-ef m (inj₁ _)  = ⊥
ModuleTyped-ef m (inj₂ es) = ModTele emptyScope es

ModuleTyped : P.Resolved → Set
ModuleTyped m = ModuleTyped-ef m (Parser.extractFunctions m)

------------------------------------------------------------------------
-- The entry point: a monomorphic definition `main`, usable as `Eff Unit Unit`.
------------------------------------------------------------------------

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- Every monomorphic definition named `main` is usable as `Eff Unit Unit` (the
-- entry converts it, D315).
MainsEffUU : ∀ {sc es} → ModTele sc es → Set
MainsEffUU []                                  = ⊤
MainsEffUU (ffi _ _ _ _ rest)                = MainsEffUU rest
MainsEffUU (mono {fi = fi} {ty = ty} _ _ _ _ rest) = (funName fi ≡ "main" → ty <: EffUU) × MainsEffUU rest
MainsEffUU (poly _ _ rest)                     = MainsEffUU rest

-- Some monomorphic definition is `main`, usable as `Eff Unit Unit`.
MainIn : ∀ {sc es} → ModTele sc es → Set
MainIn []                                  = ⊥
MainIn (ffi _ _ _ _ rest)                = MainIn rest
MainIn (mono {fi = fi} {ty = ty} _ _ _ _ rest) = ((funName fi ≡ "main") × (ty <: EffUU)) ⊎ MainIn rest
MainIn (poly _ _ rest)                     = MainIn rest

HasValidMain-ef : ∀ (m : P.Resolved) (ef : String ⊎ List Parser.Entry) → ModuleTyped-ef m ef → Set
HasValidMain-ef m (inj₂ _) mt = MainsEffUU mt × MainIn mt

HasValidMain : ∀ (m : P.Resolved) → ModuleTyped m → Set
HasValidMain m mt = HasValidMain-ef m (Parser.extractFunctions m) mt
