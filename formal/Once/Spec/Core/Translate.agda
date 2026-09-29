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
--     is the program's body, in the scope of the definitions before it.
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
open import Once.Type.Rigid using (RigidFree; RigidFreeF; KindedInstance; ground-kinded; rigidOf;
  rf-Unit; rf-Void; rf-Int; rf-Float; rf-Str; rf-Buffer; rf-*; rf-+; rf-⇒; rf-μ; rf-ν; rf-K; rf-Id; rf-⊕; rf-⊗)
import Once.Compile as C
open C.FunInfo using (funName; funBody; funType; funIsPrimitive)
open C.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.TypeCheck.Classify using (lookupImport; lookupPolyPrefix)
open import Once.Surface.Context as Ctx using (Usage)
open import Once.Spec.Module using (Scope; scope; ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf; addImp; addPoly)
open import Once.Spec.Core.PolyTy
open import Once.Spec.Core.AbsTy
open import Once.Spec.Core.Schema using (schemaOf; schemaOf-cf; kindsOf; kinded-instance)
open import Once.Spec.Core.Telescope using (Tele; def; Program; program; noKinds; IOUnit)
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
  i-ffi : ∀ {x T imps} → HonestFFI T → RigidFree T → ImpSig S imps → ImpSig S ((x , T) ∷ imps)
  i-def : ∀ {x T imps} (d : Fin s) → S !! d ≡ monoSchema T → ImpSig S imps → ImpSig S ((x , T) ∷ imps)

-- Each telescope definition's core entry.
data TeleSig {s} (S : Sig s) : List C.PolyFunInfo → Set where
  []    : TeleSig S []
  t-def : ∀ {p ps} (d : Fin s) → S !! d ≡ schemaOf (pfunType p) → TeleSig S ps → TeleSig S (p ∷ ps)

wkI : ∀ {s} {S : Sig s} {sc : Schema} {imps} → ImpSig S imps → ImpSig (S ▷ sc) imps
wkI []              = []
wkI (i-ffi h g is)  = i-ffi h g (wkI is)
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

  impAt : ∀ {imps} → ImpSig S imps → ∀ {x T′} → lookupImport imps x ≡ just T′ → ES.ImportAt T′
  impAt [] ()
  impAt {(n , T₀) ∷ rest} (i-ffi h g is) {x} eq with StrProp._≟_ n x
  ... | yes _ with just-injective eq
  ...   | refl = ES.ffi h g
  impAt {(n , T₀) ∷ rest} (i-ffi h g is) {x} eq | no _ = impAt is eq
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

toProgram : ∀ {s} {S : Sig s} {sc es} → Tele S → ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc) → SigCF S
          → (mt : ModTele sc es) → MainIn mt → Program
toProgram tl is ts sg [] ()
toProgram tl is ts sg (ffi _ _ _ h g rest) mi = toProgram tl (i-ffi h g is) ts sg rest mi
toProgram {S = S} {sc = sc} tl is ts sg (poly {pfi = pfi} D rest) mi =
  let Δ        = kindsOf (pfunType pfi)
      (t , Dc) = E.elabᶜ S (viewOf is ts) D
      Dp       = u0 (A.abs-⊢ S Δ sg Dc)
  in toProgram (def tl (schemaOf (pfunType pfi)) (A.absTm S Δ t) Dp)
               (wkI is) (t-def zero refl (wkT ts))
               (λ { zero → schemaOf-cf (pfunType pfi) ; (suc d) → sg d })
               rest mi
toProgram {S = S} {sc = sc} tl is ts sg (mono {fi = fi} {ty = ty} ep er g D rest) mi = pick mi
  where
    elabD = E.elabᶜ S (viewOf is ts) D
    t  = proj₁ elabD
    Dc = proj₂ elabD
    -- The body at its type, as a core derivation over no type variables.
    body : PT._⊩_⊢[_]_∷_!_ S noKinds PT.∅ Usage.[] (A.absTm S noKinds t) ⌈ ty ⌉ T.pure
    body = subst (λ X → PT._⊩_⊢[_]_∷_!_ S noKinds PT.∅ Usage.[] (A.absTm S noKinds t) X T.pure)
                 (absTy-ground noKinds g) (u0 (A.abs-⊢ S noKinds sg Dc))
    continue : MainIn rest → Program
    continue mi′ = toProgram (def tl (monoSchema ty) (A.absTm S noKinds t) body)
                             (i-def zero refl (wkI is)) (wkT ts)
                             (λ { zero → ground-cf g ; (suc d) → sg d })
                             rest mi′
    -- `main`: the body in the scope of the definitions before it.
    here : ty ≡ EffUU → Program
    here refl = program tl (A.absTm S noKinds t) (u0 (A.abs-⊢ S noKinds sg Dc))
    dispatch : MainIn rest → Dec (funName fi ≡ "main") → Dec (ty ≡ EffUU) → Program
    dispatch mi′ (yes _) (yes e) = here e
    dispatch mi′ _       _       = continue mi′
    pick : ((funName fi ≡ "main") × (ty ≡ EffUU)) ⊎ MainIn rest → Program
    pick (inj₁ (_ , e)) = here e
    pick (inj₂ mi′)     = dispatch mi′ (funName fi ≟str "main") (ty ≟T EffUU)
