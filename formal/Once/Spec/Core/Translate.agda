-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Core.Translate — plan 0.103 phase 6c: MODULES → PROGRAMS.
--
-- SPEC. A well-typed module (the surface telescope, D241) IS a core program
-- (D239): walking it in declaration order,
--   * an FFI declaration extends the scope (a reference to it is a `sigop`);
--   * a monomorphic definition becomes an arity-0 entry, its body elaborated
--     (6b) in its scope;
--   * a polymorphic definition becomes a `∀` entry: its body, typed once at its
--     rigid schema, elaborated and ABSTRACTED (D243);
--   * `main` — the first `main : IO Unit`, exactly as the compiler finds it —
--     is an entry like any other (D253); the program runs a REFERENCE to it,
--     and its telescope is the whole module.
-- The correspondence between the surface scope and the core signature
-- (`ImpSig`/`TeleSig`) is what the elaboration's `View` is built from.
------------------------------------------------------------------------

module Once.Spec.Core.Translate where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String) renaming (_≟_ to _≟str_)
import Data.String.Properties as StrProp
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import Once.Type as T
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Honest using (HonestFFI)
open import Once.Functor.Translate using (IsConcrete)
open import Once.Type.Rigid using (RigidFree; RigidFreeF; KindedInstance; ground-kinded; rigidOf;
  rf-Unit; rf-Void; rf-Int; rf-Float; rf-Str; rf-Buffer; rf-*; rf-+; rf-⇒; rf-μ; rf-ν; rf-K; rf-Id; rf-⊕; rf-⊗)
import Once.Compile as C
open C.FunInfo using (funName; funBody; funType; funIsPrimitive)
open C.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.TypeCheck.Classify using (lookupImport; lookupPolyPrefix)
open import Once.Surface.Context as Ctx using (Usage)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.Spec.Module using (Scope; scope; emptyScope; ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf; addImp; addPoly)
open import Once.Spec.Contract using (ISig)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Once.Spec.Core.Telescope as TL
open import Once.Spec.Core.PolyTy
open import Once.Spec.Core.AbsTy
open import Once.Spec.Core.Schema using (schemaOf; schemaOf-cf; kindsOf; kinded-instance)
open import Once.Spec.Core.Telescope using (Tele; def; Program; program; noKinds)
import Once.Spec.Core.PolyTyping as PT
import Once.Spec.Core.Abstract as A
import Once.Spec.Elaboration as E

------------------------------------------------------------------------
-- A monomorphic definition's core schema
------------------------------------------------------------------------

monoSchema : T.Type → Schema
monoSchema ty = schema 0 noKinds ⌈ ty ⌉

-- A ground type embeds constant-free.
mutual
  ground-cf : ∀ {m} {A : T.Type} → RigidFree A → ConstFree {m} ⌈ A ⌉
  ground-cf rf-Unit   = cf-Unit
  ground-cf rf-Void   = cf-Void
  ground-cf rf-Int    = cf-Int
  ground-cf rf-Float  = cf-Float
  ground-cf rf-Str    = cf-Str
  ground-cf rf-Buffer = cf-Buffer
  ground-cf (rf-* a b) = cf-* (ground-cf a) (ground-cf b)
  ground-cf (rf-+ a b) = cf-+ (ground-cf a) (ground-cf b)
  ground-cf (rf-⇒ a b) = cf-⇒ (ground-cf a) (ground-cf b)
  ground-cf (rf-μ f) = cf-μ (groundF-cf f)
  ground-cf (rf-ν f) = cf-ν (groundF-cf f)

  groundF-cf : ∀ {m} {F : T.Functor} → RigidFreeF F → ConstFreeF {m} ⌈ F ⌉F
  groundF-cf (rf-K a) = cf-K (ground-cf a)
  groundF-cf rf-Id = cf-Id
  groundF-cf (rf-⊕ f g) = cf-⊕ (groundF-cf f) (groundF-cf g)
  groundF-cf (rf-⊗ f g) = cf-⊗ (groundF-cf f) (groundF-cf g)

SigCF : ∀ {s} → Sig s → Set
SigCF {s} S = ∀ (d : Fin s) → ConstFree (type (S !! d))

------------------------------------------------------------------------
-- The scope ↔ signature correspondence
------------------------------------------------------------------------

-- What each imported name is in the core signature.
data ImpSig {s} (S : Sig s) : C.FunCtx → Set where
  []    : ImpSig S []
  -- An FFI entry keeps its concreteness: its meaning is its contract, which
  -- exists only at a concrete type.
  -- Plan 0.105: and its declaration in the signatures the program is compiled against.
  i-ffi : ∀ {x T imps} → IsConcrete T → HonestFFI T → RigidFree T → (x , T) ∈ sigOf S → ImpSig S imps → ImpSig S ((x , T) ∷ imps)
  i-def : ∀ {x T imps} (d : Fin s) → S !! d ≡ monoSchema T → ImpSig S imps → ImpSig S ((x , T) ∷ imps)

-- Each telescope definition's core entry.
data TeleSig {s} (S : Sig s) : List C.PolyFunInfo → Set where
  []    : TeleSig S []
  t-def : ∀ {p ps} (d : Fin s) → S !! d ≡ schemaOf (pfunType p) → TeleSig S ps → TeleSig S (p ∷ ps)

wkI : ∀ {s} {S : Sig s} {sc : Schema} {imps} → ImpSig S imps → ImpSig (S ▷ sc) imps
wkI []              = []
wkI (i-ffi c h g m is)  = i-ffi c h g m (wkI is)
wkI (i-def d e is)  = i-def (suc d) e (wkI is)

wkT : ∀ {s} {S : Sig s} {sc : Schema} {ps} → TeleSig S ps → TeleSig (S ▷ sc) ps
wkT []             = []
wkT (t-def d e ts) = t-def (suc d) e (wkT ts)

------------------------------------------------------------------------
-- The elaboration View of a scope
------------------------------------------------------------------------

module _ {s} {S : Sig s} where

  module ES = E S

  -- A monomorphic entry at its (only) instance.
  mono-inst : ∀ {d : Fin s} {T′ : T.Type} → S !! d ≡ monoSchema T′ → ES.InstanceOf d T′
  mono-inst {d} {T′} e =
    subst (λ sc → Σ-syntax (GSub (arity sc)) (λ τ → Respects (kinds sc) τ × (type sc ⟪ τ ⟫ ≡ T′)))
          (sym e) ((λ ()) , (λ ()) , ⌈⌉-⟪⟫ T′ (λ ()))

  -- A telescope entry at a kinded instance of its schema.
  poly-inst : ∀ {d : Fin s} {sc : T.PolyType} {T′ : T.Type} → S !! d ≡ schemaOf sc → KindedInstance sc T′
            → ES.InstanceOf d T′
  poly-inst {d} {sc} {T′} e ki =
    subst (λ sch → Σ-syntax (GSub (arity sch)) (λ τ → Respects (kinds sch) τ × (type sch ⟪ τ ⟫ ≡ T′)))
          (sym e) (kinded-instance sc ki)

  impAt : ∀ {imps} → ImpSig S imps → ∀ {x T′} → lookupImport imps x ≡ just T′ → ES.ImportAt x T′
  impAt [] ()
  impAt {(n , T₀) ∷ rest} (i-ffi c h g m is) {x} eq with StrProp._≟_ n x
  ... | yes refl with just-injective eq
  ...   | refl = ES.ffi h g m
  impAt {(n , T₀) ∷ rest} (i-ffi c h g m is) {x} eq | no _ = impAt is eq
  impAt {(n , T₀) ∷ rest} (i-def d e is) {x} eq with StrProp._≟_ n x
  ... | yes _ with just-injective eq
  ...   | refl = ES.def d (mono-inst e)
  impAt {(n , T₀) ∷ rest} (i-def d e is) {x} eq | no _ = impAt is eq

  -- The entry a telescope reference finds, with its schema.
  telFind : ∀ {ps} → TeleSig S ps → ∀ {x sc body prefix}
          → lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix)
          → Σ-syntax (Fin s) (λ d → S !! d ≡ schemaOf sc)
  telFind [] ()
  telFind {p ∷ ps} (t-def d e ts) {x} eq with StrProp._≟_ (pfunName p) x
  ... | yes _ with just-injective eq
  ...   | refl = d , e
  telFind {p ∷ ps} (t-def d e ts) {x} eq | no _ = telFind ts eq

  viewOf : ∀ {imps ps} → ImpSig S imps → TeleSig S ps → ES.View imps (C.buildPolyCtx ps)
  viewOf is ts = record
    { imported = impAt is
    ; entry    = λ lp → proj₁ (telFind ts lp)
    ; ground   = λ {x} {sc} lp g → poly-inst {sc = sc} (proj₂ (telFind ts lp)) (ground-kinded sc g)
    ; inst     = λ {x} {sc} lp _ ki → poly-inst {sc = sc} (proj₂ (telFind ts lp)) ki
    }

------------------------------------------------------------------------
-- The walk
------------------------------------------------------------------------

private
  -- Every usage over the empty local context is the empty usage.
  u0 : ∀ {s} {S : Sig s} {m} {Δ : KCtx m} {Ψ : Usage 0} {t A π}
     → PT._⊩_⊢[_]_∷_!_ S Δ PT.∅ Ψ t A π → PT._⊩_⊢[_]_∷_!_ S Δ PT.∅ Usage.[] t A π
  u0 {Ψ = Usage.[]} d = d

-- The walk's `main` selection is TOP-LEVEL (not `where`-bound), so a proof can
-- follow it: the first `main : IO Unit`, exactly as the compiler's `findMain`
-- picks it.
module _ {s} {S : Sig s} {sc : Scope} {fi : C.FunInfo} {ty : T.Type} {Ψ : Usage 0} where


  monoElab : ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc)
           → ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ → E.Elab S Ctx.∅ Ψ ty
  monoElab is ts D = E.elabᶜ S (viewOf is ts) D

  -- The body at its type, as a core derivation over no type variables.
  monoBody : (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc)) → SigCF S → RigidFree ty
           → (D : ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
           → PT._⊩_⊢[_]_∷_!_ S noKinds PT.∅ Usage.[] (A.absTm S noKinds (proj₁ (monoElab is ts D))) ⌈ ty ⌉ T.pure
  monoBody is ts sg g D =
    subst (λ X → PT._⊩_⊢[_]_∷_!_ S noKinds PT.∅ Usage.[] (A.absTm S noKinds (proj₁ (monoElab is ts D))) X T.pure)
          (absTy-ground noKinds g) (u0 (A.abs-⊢ S noKinds sg (proj₂ (monoElab is ts D))))

-- The signature extended by a definition's entry stays constant-free.
monoSg : ∀ {s} {S : Sig s} {ty : T.Type} → SigCF S → RigidFree ty → SigCF (S ▷ monoSchema ty)
monoSg sg g zero    = ground-cf g
monoSg sg g (suc d) = sg d

polySg : ∀ {s} {S : Sig s} → SigCF S → (pfi : C.PolyFunInfo) → SigCF (S ▷ schemaOf (pfunType pfi))
polySg sg pfi zero    = schemaOf-cf (pfunType pfi)
polySg sg pfi (suc d) = sg d

-- A telescope definition: typed once at its rigid schema, elaborated, abstracted.
module _ {s} {S : Sig s} {sc : Scope} {pfi : C.PolyFunInfo} {Ψ : Usage 0} where

  polyElab : ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc)
           → ctxOf sc ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ → E.Elab S Ctx.∅ Ψ (rigidOf (pfunType pfi))
  polyElab is ts D = E.elabᶜ S (viewOf is ts) D

  polyBody : (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc)) (sg : SigCF S)
           → (D : ctxOf sc ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ)
           → PT._⊩_⊢[_]_∷_!_ S (kindsOf (pfunType pfi)) PT.∅ Usage.[]
               (A.absTm S (kindsOf (pfunType pfi)) (proj₁ (polyElab is ts D)))
               (absTy (kindsOf (pfunType pfi)) (rigidOf (pfunType pfi))) T.pure
  polyBody is ts sg D = u0 (A.abs-⊢ S (kindsOf (pfunType pfi)) sg (proj₂ (polyElab is ts D)))

-- A definition's telescope entry.
monoDef : ∀ {s} {S : Sig s} {sc fi ty Ψ} → Tele S → (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
        → SigCF S → RigidFree ty → ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ → Tele (S ▷ monoSchema ty)
monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D =
  def tl (monoSchema ty) (A.absTm S noKinds (proj₁ (monoElab {S = S} {sc = sc} {fi = fi} is ts D)))
                         (monoBody {S = S} {sc = sc} {fi = fi} is ts sg g D)

polyDef : ∀ {s} {S : Sig s} {sc pfi Ψ} → Tele S → (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
        → SigCF S → ctxOf sc ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ → Tele (S ▷ schemaOf (pfunType pfi))
polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl is ts sg D =
  def tl (schemaOf (pfunType pfi))
         (A.absTm S (kindsOf (pfunType pfi)) (proj₁ (polyElab {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} is ts D)))
         (polyBody {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} is ts sg D)

-- D253: the program names the entry `main : IO Unit`.
programAt : ∀ {s} {S : Sig s} → Tele S → (d : Fin s) → S !! d ≡ monoSchema EffUU → Program
programAt tl d e = program tl d e

-- Plan 0.105 (D257 amendment 2): the interpretation signatures a typed module
-- is compiled against — its FFI declarations, as its typing fixes them.
teleSig : ∀ {sc es} → ModTele sc es → ISig
teleSig []                                    = []
teleSig (ffi {fi = fi} {ty = ty} _ _ _ _ _ rest) = (funName fi , ty) ∷ teleSig rest
teleSig (mono _ _ _ _ rest)                   = teleSig rest
teleSig (poly _ rest)                         = teleSig rest

-- The walk's invariant: the declarations still ahead are in the signatures.
SigIn : ∀ {sc es} → ModTele sc es → ∀ {s} → Sig s → Set
SigIn mt S = ∀ {d} → d ∈ teleSig mt → d ∈ sigOf S

mutual
  toProgram : ∀ {s} {S : Sig s} {sc es} → Tele S → ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc) → SigCF S
            → (mt : ModTele sc es) → MainIn mt → SigIn mt S → Program
  toProgram tl is ts sg [] () u
  toProgram tl is ts sg (ffi _ _ c h g rest) mi u = toProgram tl (i-ffi c h g (u (here refl)) is) ts sg rest mi (λ m → u (there m))
  toProgram {S = S} {sc = sc} tl is ts sg (poly {pfi = pfi} {Ψ = Ψ} D rest) mi u =
    toProgram (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl is ts sg D)
              (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) rest mi u
  toProgram {S = S} {sc = sc} tl is ts sg (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er g D rest) mi u =
    monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi u

  monoPick : ∀ {s} {S : Sig s} {sc fi ty es Ψ} → Tele S → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
           → SigCF S → RigidFree ty → (D : ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → ((funName fi ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest
           → SigIn rest S → Program
  monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest (inj₁ (_ , e)) u =
    monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest e u
  monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest (inj₂ mi′) u =
    monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi′ (funName fi ≟str "main") (ty ≟T EffUU) u

  monoDispatch : ∀ {s} {S : Sig s} {sc fi ty es Ψ} → Tele S → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
               → SigCF S → RigidFree ty → (D : ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
               → (rest : ModTele (addImp sc (funName fi) ty) es) → MainIn rest
               → Dec (funName fi ≡ "main") → Dec (ty ≡ EffUU) → SigIn rest S → Program
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi′ (yes _) (yes e) u =
    monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest e u
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi′ (yes _) (no _) u =
    monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi′ u
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi′ (no _) _ u =
    monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi′ u

  monoNext : ∀ {s} {S : Sig s} {sc fi ty es Ψ} → Tele S → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
           → SigCF S → RigidFree ty → (D : ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → MainIn rest → SigIn rest S → Program
  monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest mi′ u =
    toProgram (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D)
              (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g) rest mi′ u

  -- `main`: an entry like any other (D253); the program refers to it.
  monoHere : ∀ {s} {S : Sig s} {sc fi ty es Ψ} → Tele S → (is : ImpSig S (Scope.imps sc)) → TeleSig S (Scope.tele sc)
           → SigCF S → RigidFree ty → (D : ctxOf sc ⊢ᶜ funBody fi ∶ ty ⨾ Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → ty ≡ EffUU → SigIn rest S → Program
  monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D rest e u =
    toProgramFrom (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D)
                  (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g) zero (cong monoSchema e) rest u

  -- The entries after `main`: the telescope goes on, `main`'s entry is weakened.
  toProgramFrom : ∀ {s} {S : Sig s} {sc es} → Tele S → ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc) → SigCF S
                → (d : Fin s) → S !! d ≡ monoSchema EffUU → (mt : ModTele sc es) → SigIn mt S → Program
  toProgramFrom tl is ts sg d e [] u = programAt tl d e
  toProgramFrom tl is ts sg d e (ffi _ _ c h g rest) u = toProgramFrom tl (i-ffi c h g (u (here refl)) is) ts sg d e rest (λ m → u (there m))
  toProgramFrom {S = S} {sc = sc} tl is ts sg d e (poly {pfi = pfi} {Ψ = Ψ} D rest) u =
    toProgramFrom (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl is ts sg D)
                  (wkI is) (t-def zero refl (wkT ts)) (polySg sg pfi) (suc d) e rest u
  toProgramFrom {S = S} {sc = sc} tl is ts sg d e (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er g D rest) u =
    toProgramFrom (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl is ts sg g D)
                  (i-def zero refl (wkI is)) (wkT ts) (monoSg sg g) (suc d) e rest u

-- A typed module's core program, over the signatures it is compiled against.
toProgram₀ : ∀ {es} (mt : ModTele emptyScope es) → MainIn mt → Program
toProgram₀ mt mi = toProgram {S = [] (teleSig mt)} TL.[] [] [] (λ ()) mt mi (λ m → m)
