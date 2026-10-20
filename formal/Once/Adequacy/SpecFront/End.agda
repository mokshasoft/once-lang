-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.End — the compiler's typed telescope, to its end
-- (plan 0.121 §3.6, F6).
--
-- Past the FFI declarations, the compiler's telescope holds definitions only
-- (`EntryKind`), each one more entry of the core signature, named by its
-- canonical name (`endOf`: the last state, the walk's end). The core program
-- the compiler builds from it (`toProgram`) is that end's telescope, its
-- entry a definition named `main` (`prog-end`).
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.String using (String)
open import Once.Lang.Contract using (ISig)
open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.End {Fs : ISig} (Σ : Signature) (ps : List String) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Data.String

import Once.Lang.Core.PolyTy as LP
import Once.Lang.Core.Telescope as TL
import Once.Parser as Parser
open Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Lang.Module using (Scope; ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf; addImp; MonoBody)
open import Once.TypeCheck.Classify using (topCtx)
import Once.Compile as C
open import Once.Lang.Type.WellFormed using (RigidFree)
open import Once.Lang.Principal using (PrincipalAt)
open import Once.Lang.Core.Translate
  using (SigSig; ImpSig; TeleSig; SigCF; SigIn; t-def; wkI; wkT; impDefs; monoDef; polyDef; monoSg; polySg; mainEntry;
         toProgram; toProgramFrom)
open import Once.Lang.Type.Sub using (_<:_)
import Once.Type.Sub
import Once.Lang.Core.Translate
open import Once.Adequacy.SpecFront.WalkState {Fs} Σ ps using (_∷ⁿ_)
import Once.Adequacy.SpecFront.Polys

-- The entries: definitions (no FFI declaration), polymorphic exactly when one of `ps`.
EntryKind : Parser.Entry → Set
EntryKind = Once.Adequacy.SpecFront.Polys.EntryKind ps

record End : Set where
  constructor end
  field
    {s}  : ℕ
    {S}  : LP.Sig Fs s
    tl   : TL.Tele S
    nm   : Fin s → CanonicalName

-- (the walk's step on the kinds, so the walk and `endOf` agree)
all-tail : ∀ {a} {X : Set a} {P : X → Set} {x xs} → All P (x ∷ xs) → All P xs
all-tail (_ ∷ t) = t

private
  t≢f : true ≡ false → ⊥
  t≢f ()

no-ffi : ∀ {fi es} → funIsPrimitive fi ≡ true → All EntryKind (Parser.e-fun fi ∷ es) → ⊥
no-ffi ep ((ep′ , _) ∷ _) = t≢f (trans (sym ep) ep′)

endOf : ∀ {s} {S : LP.Sig Fs s} {sc es} → TL.Tele S → SigSig Fs (Scope.sig sc) → ImpSig S (Scope.imps sc) → TeleSig S (Scope.tele sc)
      → SigCF S → (Fin s → CanonicalName) → (mt : ModTele sc es) → All EntryKind es → End
endOf tl ss is ts sgcf nm [] _ = end tl nm
endOf tl ss is ts sgcf nm (ffi ep _ _ _ _ _) ks = ⊥-elim (no-ffi ep ks)
endOf {S = S} {sc} tl ss is ts sgcf nm (poly {pfi = pfi} {Ψ = Ψ} pr D rest) ks =
  endOf (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts sgcf D) ss (wkI is) (t-def zero refl (wkT ts)) (polySg sgcf pfi)
        (canonical (pfunName pfi ∷ []) ∷ⁿ nm) rest (all-tail ks)
endOf {S = S} {sc} tl ss is ts sgcf nm (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr g D rest) ks =
  endOf (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts) (monoSg sgcf g)
        (canonical (funName fi ∷ []) ∷ⁿ nm) rest (all-tail ks)

------------------------------------------------------------------------
-- The compiler's core program is the end's telescope
------------------------------------------------------------------------

-- A core program is an end's telescope, its entry named `main`.
EndsAt : End → TL.Program Fs → Set
EndsAt (end {S = S} tl nm) p = Σ[ d ∈ Fin _ ] Σ[ me ∈ TL.MainEntry (LP._!!_ S d) ] (p ≡ TL.program tl d me) × (nm d ≡ canonical ("main" ∷ []))

-- after `main`: the entry, weakened along
from-end : ∀ {s} {S : LP.Sig Fs s} {sc es} (tl : TL.Tele S) (ss : SigSig Fs (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
           (sgcf : SigCF S) (nm : Fin s → CanonicalName) (d : Fin s) (me : TL.MainEntry (LP._!!_ S d)) → nm d ≡ canonical ("main" ∷ [])
         → (mt : ModTele sc es) (u : SigIn mt S) (ks : All EntryKind es)
         → EndsAt (endOf tl ss is ts sgcf nm mt ks) (toProgramFrom tl ss is ts sgcf d me mt u)
from-end tl ss is ts sgcf nm d me h [] u ks = d , me , refl , h
from-end tl ss is ts sgcf nm d me h (ffi ep _ _ _ _ _) u ks = ⊥-elim (no-ffi ep ks)
from-end {S = S} {sc} tl ss is ts sgcf nm d me h (poly {pfi = pfi} {Ψ = Ψ} pr D rest) u ks =
  from-end (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts sgcf D) ss (wkI is) (t-def zero refl (wkT ts)) (polySg sgcf pfi)
           (canonical (pfunName pfi ∷ []) ∷ⁿ nm) (suc d) me h rest u (all-tail ks)
from-end {S = S} {sc} tl ss is ts sgcf nm d me h (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr g D rest) u ks =
  from-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts) (monoSg sgcf g)
           (canonical (funName fi ∷ []) ∷ⁿ nm) (suc d) me h rest u (all-tail ks)

prog-end : ∀ {s} {S : LP.Sig Fs s} {sc es} (tl : TL.Tele S) (ss : SigSig Fs (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
           (sgcf : SigCF S) (nm : Fin s → CanonicalName)
         → (mt : ModTele sc es) (mi : MainIn mt) (u : SigIn mt S) (ks : All EntryKind es)
         → EndsAt (endOf tl ss is ts sgcf nm mt ks) (toProgram tl ss is ts sgcf mt mi u)
-- a `mono` entry: `main` here (picked, or dispatched on), or later
mono-end : ∀ {s} {S : LP.Sig Fs s} {sc es fi ty Ψ} (tl : TL.Tele S) (ss : SigSig Fs (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
           (sgcf : SigCF S) (nm : Fin s → CanonicalName)
           (ep : funIsPrimitive fi ≡ false)
           (er : C.resolveFunType (topCtx (Scope.sig sc) (Scope.imps sc)) (C.buildPolyCtx (Scope.tele sc)) (funType fi) (funBody fi) ≡ inj₂ ty)
           (pr : PrincipalAt (ctxOf sc) (funBody fi) ty) (g : RigidFree ty) (D : MonoBody (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           (rest : ModTele (addImp sc (funName fi) ty) es) (mi′ : MainIn rest)
         → (dm : Dec (funName fi ≡ "main")) (de : Dec (ty <: EffUU)) (u : SigIn rest S) (ks : All EntryKind (Parser.e-fun fi ∷ es))
         → EndsAt (endOf tl ss is ts sgcf nm (mono {sc = sc} {fi = fi} {ty = ty} {es = es} {Ψ = Ψ} ep er pr g D rest) ks)
                  (Once.Lang.Core.Translate.monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D rest mi′ dm de u)

prog-end tl ss is ts sgcf nm [] () u ks
prog-end tl ss is ts sgcf nm (ffi ep _ _ _ _ _) mi u ks = ⊥-elim (no-ffi ep ks)
prog-end {S = S} {sc} tl ss is ts sgcf nm (poly {pfi = pfi} {Ψ = Ψ} pr D rest) mi u ks =
  prog-end (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts sgcf D) ss (wkI is) (t-def zero refl (wkT ts)) (polySg sgcf pfi)
           (canonical (pfunName pfi ∷ []) ∷ⁿ nm) rest mi u (all-tail ks)
prog-end {S = S} {sc} tl ss is ts sgcf nm (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr g D rest) (inj₁ (em , e)) u ks =
  from-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts) (monoSg sgcf g)
           (canonical (funName fi ∷ []) ∷ⁿ nm) zero (mainEntry e) (cong (λ x → canonical (x ∷ [])) em) rest u (all-tail ks)
prog-end {S = S} {sc} tl ss is ts sgcf nm (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr g D rest) (inj₂ mi′) u ks =
  mono-end tl ss is ts sgcf nm ep er pr g D rest mi′ (funName fi Data.String.≟ "main") (Once.Type.Sub._<:?_ ty EffUU) u ks

mono-end {S = S} {sc} {fi = fi} {ty} {Ψ} tl ss is ts sgcf nm ep er pr g D rest mi′ (yes em) (yes e) u ks =
  from-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts) (monoSg sgcf g)
           (canonical (funName fi ∷ []) ∷ⁿ nm) zero (mainEntry e) (cong (λ x → canonical (x ∷ [])) em) rest u (all-tail ks)
mono-end {S = S} {sc} {fi = fi} {ty} {Ψ} tl ss is ts sgcf nm ep er pr g D rest mi′ (yes _) (no _) u ks =
  prog-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts) (monoSg sgcf g)
           (canonical (funName fi ∷ []) ∷ⁿ nm) rest mi′ u (all-tail ks)
mono-end {S = S} {sc} {fi = fi} {ty} {Ψ} tl ss is ts sgcf nm ep er pr g D rest mi′ (no _) _ u ks =
  prog-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts sgcf g D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts) (monoSg sgcf g)
           (canonical (funName fi ∷ []) ∷ⁿ nm) rest mi′ u (all-tail ks)
