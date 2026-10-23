-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.EndNames — the walk's names, at its end (plan
-- 0.121 §3.6, F6).
--
-- Each step of the compiler's telescope names its definition by its
-- canonical name (`canonical [x]`, `End.endOf`). At the end every name is an
-- entry's (`named-end`), and no two coincide when the entries' names are
-- distinct and new (`distinct-end`) — the Spec's `Denotes.distinct`.
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.String using (String)
open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.EndNames (Σ : Signature) (ps : List String) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (Injective)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

import Once.Spec.Core.Syntax as SC
import Once.Spec.Core.Program Σ as SP
import Once.Parser as Parser
open Parser.FunInfo using (funName)
open Parser.PolyFunInfo using (pfunName)
open import Once.Spec.Name using (CanonicalName; canonical)
import Once.Spec.Name
open import Once.Internal.Module using (Scope; ModTele; []; ffi; mono; poly)
open import Once.Internal.Core.Translate Σ using (SigSig; ImpSig; TeleSig; t-def; wkI; wkT; impDefs; monoDef; polyDef)
open import Once.Adequacy.SpecFront.WalkState Σ ps using (_∷ⁿ_)
open import Once.Adequacy.SpecFront.End Σ ps using (EntryKind; End; endOf; no-ffi; all-tail)
import Data.String

names : List Parser.Entry → List String
names = map Parser.entryNameOf

-- A naming's names are canonical single names, each in `L`.
NamedIn : ∀ {s} → (Fin s → CanonicalName) → List String → Set
NamedIn nm L = ∀ d → Σ[ x ∈ String ] (nm d ≡ canonical (x ∷ [])) × (x ∈ L)

-- …none of them `canonical [y]`.
Fresh : ∀ {s} → (Fin s → CanonicalName) → String → Set
Fresh nm y = ∀ d → nm d ≢ canonical (y ∷ [])

private
  one-inj : ∀ {x y : String} → canonical (x ∷ []) ≡ canonical (y ∷ []) → x ≡ y
  one-inj refl = refl

  step-named : ∀ {s} {nm : Fin s → CanonicalName} {L x} → NamedIn nm L
             → NamedIn (canonical (x ∷ []) ∷ⁿ nm) (x ∷ L)
  step-named n zero    = _ , refl , here refl
  step-named n (suc d) = let (y , e , m) = n d in y , e , there m

  back : ∀ {y x : String} {L es} → (y ∈ (x ∷ L) ⊎ y ∈ es) → (y ∈ L ⊎ y ∈ (x ∷ es))
  back (inj₁ (here e)) = inj₂ (here e)
  back (inj₁ (there m)) = inj₁ m
  back (inj₂ m) = inj₂ (there m)

  step-inj : ∀ {s} {nm : Fin s → CanonicalName} {c} → Injective _≡_ _≡_ nm → (∀ d → nm d ≢ c) → Injective _≡_ _≡_ (c ∷ⁿ nm)
  step-inj i f {zero}  {zero}  e = refl
  step-inj i f {zero}  {suc b} e = ⊥-elim (f b (sym e))
  step-inj i f {suc a} {zero}  e = ⊥-elim (f a e)
  step-inj i f {suc a} {suc b} e = cong suc (i e)

  step-fresh : ∀ {s} {nm : Fin s → CanonicalName} {x} {ys : List String} → All (x ≢_) ys → All (Fresh nm) ys
             → All (Fresh (canonical (x ∷ []) ∷ⁿ nm)) ys
  step-fresh [] [] = []
  step-fresh (n ∷ ns) (f ∷ fs) = fr n f ∷ step-fresh ns fs
    where
      fr : ∀ {y} → _ ≢ y → Fresh _ y → Fresh _ y
      fr n′ f′ zero    e = n′ (one-inj e)
      fr n′ f′ (suc d) e = f′ d e

-- Every name at the end is a walked entry's, or was already one.
named-end : ∀ {s} {S : SC.Defs s} {sc es} (tl : SP.Tele S) (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
            (nm : Fin s → CanonicalName) (mt : ModTele sc es) (ks : All EntryKind es) {L}
          → NamedIn nm L → ∀ d → Σ[ x ∈ String ] (End.nm (endOf tl ss is ts nm mt ks) d ≡ canonical (x ∷ [])) × (x ∈ L ⊎ x ∈ names es)
named-end tl ss is ts nm [] ks n d = let (x , e , m) = n d in x , e , inj₁ m
named-end tl ss is ts nm (ffi ep _ _ _ _) ks n d = ⊥-elim (no-ffi ep ks)
named-end {S = S} {sc} tl ss is ts nm (poly {pfi = pfi} {Ψ = Ψ} pr D _ rest) ks {L} n d =
  let (x , e , m) = named-end (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts D) ss (wkI is) (t-def zero refl (wkT ts))
                              (canonical (pfunName pfi ∷ []) ∷ⁿ nm) rest (all-tail ks) (step-named {L = L} n) d
  in x , e , back m
named-end {S = S} {sc} tl ss is ts nm (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr D _ rest) ks {L} n d =
  let (x , e , m) = named-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
                              (canonical (funName fi ∷ []) ∷ⁿ nm) rest (all-tail ks) (step-named {L = L} n) d
  in x , e , back m

-- No two names at the end coincide.
distinct-end : ∀ {s} {S : SC.Defs s} {sc es} (tl : SP.Tele S) (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
               (nm : Fin s → CanonicalName) (mt : ModTele sc es) (ks : All EntryKind es)
             → Injective _≡_ _≡_ nm → AllPairs _≢_ (names es) → All (Fresh nm) (names es)
             → Injective _≡_ _≡_ (End.nm (endOf tl ss is ts nm mt ks))
distinct-end tl ss is ts nm [] ks i u f = i
distinct-end tl ss is ts nm (ffi ep _ _ _ _) ks i u f = ⊥-elim (no-ffi ep ks)
distinct-end {S = S} {sc} tl ss is ts nm (poly {pfi = pfi} {Ψ = Ψ} pr D _ rest) ks i (h ∷ u) (f ∷ fs) =
  distinct-end (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts D) ss (wkI is) (t-def zero refl (wkT ts))
               (canonical (pfunName pfi ∷ []) ∷ⁿ nm) rest (all-tail ks) (step-inj i f) u (step-fresh h fs)
distinct-end {S = S} {sc} tl ss is ts nm (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr D _ rest) ks i (h ∷ u) (f ∷ fs) =
  distinct-end (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts D) ss (impDefs (funName fi Data.String.== "main") is) (wkT ts)
               (canonical (funName fi ∷ []) ∷ⁿ nm) rest (all-tail ks) (step-inj i f) u (step-fresh h fs)
