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
open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.End (Σ : Signature) (ps : List String) where

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

import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Program Σ as SP
import Once.Internal.Core.Telescope Σ as TL
import Once.Parser as Parser
open Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Internal.Module using (Scope; ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf; addImp; MonoBody; MonoWit)
open import Once.TypeCheck.Classify using (topCtx)
import Once.Compile as C
open import Once.Internal.Principal using (PrincipalAt)
open import Once.Internal.Core.Translate Σ
  using (SigSig; ImpSig; TeleSig; SigIn; t-def; wkI; wkT; impDefs; mainEntry)
open import Once.Adequacy.ModuleProgram Σ using (Names; names-mono; names-poly; monoDef; polyDef; toProgram; toProgramFrom)
import Once.Adequacy.ModuleProgram Σ as MP
open import Once.Spec.Sub using (_<:_)
import Once.Type.Sub
import Once.Internal.Core.Translate Σ as TR
open import Once.Adequacy.SpecFront.WalkState Σ ps using (_∷ⁿ_)
import Once.Adequacy.SpecFront.Polys

-- The entries: definitions (no FFI declaration), polymorphic exactly when one of `ps`.
EntryKind : Parser.Entry → Set
EntryKind = Once.Adequacy.SpecFront.Polys.EntryKind ps

record End : Set where
  constructor end
  field
    {s}  : ℕ
    {S}  : SC.Defs s
    tl   : SP.Tele S
    nm   : Fin s → CanonicalName

-- (the walk's step on the kinds, so the walk and `endOf` agree)
all-tail : ∀ {a} {X : Set a} {P : X → Set} {x xs} → All P (x ∷ xs) → All P xs
all-tail (_ ∷ t) = t

private
  t≢f : true ≡ false → ⊥
  t≢f ()

no-ffi : ∀ {fi es} → funIsPrimitive fi ≡ true → All EntryKind (Parser.e-fun fi ∷ es) → ⊥
no-ffi ep ((ep′ , _) ∷ _) = t≢f (trans (sym ep) ep′)

endOf : ∀ {s} {S : SC.Defs s} {sc es} → SP.Tele S → SigSig (Scope.sig sc) → (is : ImpSig S (Scope.imps sc)) → (ts : TeleSig S (Scope.tele sc))
      → Names S is ts → (mt : ModTele sc es) → All EntryKind es → End
endOf tl ss is ts N [] _ = end tl (Names.nm N)
endOf tl ss is ts N (ffi ep _ _ _ _) ks = ⊥-elim (no-ffi ep ks)
endOf {S = S} {sc} tl ss is ts N (poly {pfi = pfi} {Ψ = Ψ} pr D W rest) ks =
  endOf (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts N W) ss (wkI is) (t-def zero refl (wkT ts))
        (names-poly pfi N) rest (all-tail ks)
endOf {S = S} {sc} tl ss is ts N (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr D W rest) ks =
  endOf (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
        (names-mono (funName fi Data.String.== "main") (funName fi) ty N) rest (all-tail ks)

------------------------------------------------------------------------
-- The compiler's core program is the end's telescope
------------------------------------------------------------------------

-- A core program is an end's telescope, its entry named `main`.
EndsAt : End → TL.Program → Set
EndsAt e p = Σ[ d ∈ Fin (End.s e) ] Σ[ me ∈ SP.Entry (SC._!!_ (End.S e) d) ] (p ≡ TL.program (End.tl e) d me) × (End.nm e d ≡ canonical ("main" ∷ []))

-- after `main`: the entry, weakened along
from-end : ∀ {s} {S : SC.Defs s} {sc es} (tl : SP.Tele S) (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
           (N : Names S is ts) (d : Fin s) (me : SP.Entry (SC._!!_ S d)) → Names.nm N d ≡ canonical ("main" ∷ [])
         → (mt : ModTele sc es) (u : SigIn mt) (ks : All EntryKind es)
         → EndsAt (endOf tl ss is ts N mt ks) (toProgramFrom tl ss is ts N d me mt u)
from-end tl ss is ts N d me h [] u ks = d , me , refl , h
from-end tl ss is ts N d me h (ffi ep _ _ _ _) u ks = ⊥-elim (no-ffi ep ks)
from-end {S = S} {sc} tl ss is ts N d me h (poly {pfi = pfi} {Ψ = Ψ} pr D W rest) u ks =
  from-end (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts N W) ss (wkI is) (t-def zero refl (wkT ts))
           (names-poly pfi N) (suc d) me h rest u (all-tail ks)
from-end {S = S} {sc} tl ss is ts N d me h (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr D W rest) u ks =
  from-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
           (names-mono (funName fi Data.String.== "main") (funName fi) ty N) (suc d) me h rest u (all-tail ks)

prog-end : ∀ {s} {S : SC.Defs s} {sc es} (tl : SP.Tele S) (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
           (N : Names S is ts)
         → (mt : ModTele sc es) (mi : MainIn mt) (u : SigIn mt) (ks : All EntryKind es)
         → EndsAt (endOf tl ss is ts N mt ks) (toProgram tl ss is ts N mt mi u)
-- a `mono` entry: `main` here (picked, or dispatched on), or later
mono-end : ∀ {s} {S : SC.Defs s} {sc es fi ty Ψ} (tl : SP.Tele S) (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
           (N : Names S is ts)
           (ep : funIsPrimitive fi ≡ false)
           (er : C.resolveFunType (topCtx (Scope.sig sc) (Scope.imps sc)) (C.buildPolyCtx (Scope.tele sc)) (funType fi) (funBody fi) ≡ inj₂ ty)
           (pr : PrincipalAt (ctxOf sc) (funBody fi) ty) (D : MonoBody (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           (W : MonoWit (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           (rest : ModTele (addImp sc (funName fi) ty) es) (mi′ : MainIn rest)
         → (dm : Dec (funName fi ≡ "main")) (de : Dec (ty <: EffUU)) (u : SigIn rest) (ks : All EntryKind (Parser.e-fun fi ∷ es))
         → EndsAt (endOf tl ss is ts N (mono {sc = sc} {fi = fi} {ty = ty} {es = es} {Ψ = Ψ} ep er pr D W rest) ks)
                  (MP.monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ dm de u)

prog-end tl ss is ts N [] () u ks
prog-end tl ss is ts N (ffi ep _ _ _ _) mi u ks = ⊥-elim (no-ffi ep ks)
prog-end {S = S} {sc} tl ss is ts N (poly {pfi = pfi} {Ψ = Ψ} pr D W rest) mi u ks =
  prog-end (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts N W) ss (wkI is) (t-def zero refl (wkT ts))
           (names-poly pfi N) rest mi u (all-tail ks)
prog-end {S = S} {sc} tl ss is ts N (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr D W rest) (inj₁ (em , e)) u ks =
  from-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
           (names-mono (funName fi Data.String.== "main") (funName fi) ty N) zero (mainEntry e) (cong (λ x → canonical (x ∷ [])) em) rest u (all-tail ks)
prog-end {S = S} {sc} tl ss is ts N (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr D W rest) (inj₂ mi′) u ks =
  mono-end tl ss is ts N ep er pr D W rest mi′ (funName fi Data.String.≟ "main") (Once.Type.Sub._<:?_ ty EffUU) u ks

mono-end {S = S} {sc} {fi = fi} {ty} {Ψ} tl ss is ts N ep er pr D W rest mi′ (yes em) (yes e) u ks =
  from-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
           (names-mono (funName fi Data.String.== "main") (funName fi) ty N) zero (mainEntry e) (cong (λ x → canonical (x ∷ [])) em) rest u (all-tail ks)
mono-end {S = S} {sc} {fi = fi} {ty} {Ψ} tl ss is ts N ep er pr D W rest mi′ (yes _) (no _) u ks =
  prog-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
           (names-mono (funName fi Data.String.== "main") (funName fi) ty N) rest mi′ u (all-tail ks)
mono-end {S = S} {sc} {fi = fi} {ty} {Ψ} tl ss is ts N ep er pr D W rest mi′ (no _) _ u ks =
  prog-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
           (names-mono (funName fi Data.String.== "main") (funName fi) ty N) rest mi′ u (all-tail ks)
