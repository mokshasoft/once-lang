-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SigFacts — the program's signature, as the
-- compiler's scope holds it (plan 0.121 §3.6, F6).
--
-- The extractor admits a module only if its entries' names are distinct
-- (`guardDistinct`, D249); the signature's table (`entrySig`) keeps a subset
-- of them, so its keys are distinct, and so are Σ's rendered names
-- (`uniq-of`) and, a fortiori, its names (`one-name`). Past the FFI
-- declarations the scope holds the table reversed (`Prefix`); a declaration
-- of Σ is found there by its rendered name, at its compiler type (`sig-at`),
-- which is concrete, honest and ground (the FFI entry's facts) and related
-- to the declaration's Spec type (`h-sig-of`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SigFacts where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
import Data.String.Properties as StrProp

open import Once.Internal.Contract using (ISig)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
open import Once.Internal.Type.WellFormed using (IsConcrete; RigidFree)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Internal.Name using (showCanonical)
open import Once.Spec.Signature using (Signature; Decl; _∶_; OneName; ⌜_⌝ᵈ)
import Once.Spec.Type as ST
import Once.Parser as Parser
open import Once.Internal.Module using (entrySig)
open import Once.Internal.Typing.Scope using (Imports; lookupImport)
open import Once.Adequacy.SpecInterp using (declTy)
open import Once.Internal.Core.Decl using (toISig)
open import Once.Adequacy.SpecCore.Type using (TyR)
open import Once.Adequacy.SpecCore.DeclType using (declS-declTy)
open import Once.Adequacy.SpecFront.Extract using (FFIFacts)
import Once.Adequacy.SpecFront.Types
import Once.Internal.Module

keys : ISig → List String
keys = map proj₁

rname : Decl → String
rname d = showCanonical (Decl.name d)

------------------------------------------------------------------------
-- Distinct names
------------------------------------------------------------------------

private
  fun-keys : ∀ {P : String → Set} n ft b p {rest : ISig} → P n → All P (keys rest)
           → All P (keys (Once.Internal.Module.entrySig-fun (Parser.mkFunInfo n ft b p) p ft rest))
  fun-keys n (just _) b true  h a = h ∷ a
  fun-keys n nothing  b true  h a = a
  fun-keys n (just _) b false h a = a
  fun-keys n nothing  b false h a = a

  fun-distinct : ∀ n ft b p {rest : ISig} → All (n ≢_) (keys rest) → AllPairs _≢_ (keys rest)
               → AllPairs _≢_ (keys (Once.Internal.Module.entrySig-fun (Parser.mkFunInfo n ft b p) p ft rest))
  fun-distinct n (just _) b true  h a = h ∷ a
  fun-distinct n nothing  b true  h a = a
  fun-distinct n (just _) b false h a = a
  fun-distinct n nothing  b false h a = a

-- the table's keys are among the entries' names
keys-all : ∀ {P : String → Set} es → All P (map Parser.entryNameOf es) → All P (keys (entrySig es))
keys-all [] [] = []
keys-all (Parser.e-fun (Parser.mkFunInfo n ft b p) ∷ es) (h ∷ a) = fun-keys n ft b p h (keys-all es a)
keys-all (Parser.e-poly _ ∷ es) (_ ∷ a) = keys-all es a

keys-distinct : ∀ es → AllPairs _≢_ (map Parser.entryNameOf es) → AllPairs _≢_ (keys (entrySig es))
keys-distinct [] [] = []
keys-distinct (Parser.e-fun (Parser.mkFunInfo n ft b p) ∷ es) (h ∷ a) = fun-distinct n ft b p (keys-all es h) (keys-distinct es a)
keys-distinct (Parser.e-poly _ ∷ es) (_ ∷ a) = keys-distinct es a

toISig-keys : ∀ Σ → keys (toISig Σ) ≡ map rname Σ
toISig-keys [] = refl
toISig-keys ((c ∶ t) ∷ Σ) = cong (showCanonical c ∷_) (toISig-keys Σ)

-- Σ's rendered names are distinct…
uniq-of : ∀ Σ es → toISig Σ ≡ entrySig es → AllPairs _≢_ (map Parser.entryNameOf es) → Unique (map rname Σ)
uniq-of Σ es e d = subst (AllPairs _≢_) (trans (cong keys (sym e)) (toISig-keys Σ)) (keys-distinct es d)

-- …and so are its names
one-name : ∀ Σ → Unique (map rname Σ) → OneName Σ
one-name [] [] = []
one-name (d ∷ Σ) (h ∷ u) = ne-map Σ h ∷ one-name Σ u
  where
    ne-map : ∀ Σ′ → All (rname d ≢_) (map rname Σ′) → All (Decl.name d ≢_) (map Decl.name Σ′)
    ne-map [] [] = []
    ne-map (d′ ∷ Σ′) (n ∷ a) = (λ e → n (cong showCanonical e)) ∷ ne-map Σ′ a

------------------------------------------------------------------------
-- A declaration in the scope's table
------------------------------------------------------------------------

private
  mem-acc : ∀ {A : Set} (xs : List A) {acc x} → x ∈ acc → x ∈ (xs ʳ++ acc)
  mem-acc []       m = m
  mem-acc (y ∷ xs) m = mem-acc xs (there m)

  mem-ʳ++ : ∀ {A : Set} (xs : List A) {acc x} → x ∈ xs → x ∈ (xs ʳ++ acc)
  mem-ʳ++ (y ∷ xs) (here refl) = mem-acc xs (here refl)
  mem-ʳ++ (y ∷ xs) (there m)   = mem-ʳ++ xs m

  shift : ∀ {A : Set} {x y : A} {xs acc} → (x ∈ xs ⊎ x ∈ (y ∷ acc)) → (x ∈ (y ∷ xs) ⊎ x ∈ acc)
  shift (inj₁ m)         = inj₁ (there m)
  shift (inj₂ (here e))  = inj₁ (here e)
  shift (inj₂ (there m)) = inj₂ m

  ʳ++-mem : ∀ {A : Set} (xs : List A) {acc x} → x ∈ (xs ʳ++ acc) → (x ∈ xs ⊎ x ∈ acc)
  ʳ++-mem []       m = inj₂ m
  ʳ++-mem (y ∷ xs) m = shift (ʳ++-mem xs m)

  not-in : ∀ {k v} {L : ISig} → All (k ≢_) (keys L) → (k , v) ∈ L → ⊥
  not-in (n ∷ _) (here refl) = n refl
  not-in (_ ∷ a) (there m)   = not-in a m

  -- distinct keys: one value per key
  func : ∀ {L : ISig} → AllPairs _≢_ (keys L) → ∀ {k v v′} → (k , v) ∈ L → (k , v′) ∈ L → v′ ≡ v
  func (_ ∷ _) (here refl) (here refl) = refl
  func (h ∷ _) (here refl) (there m′)  = ⊥-elim (not-in h m′)
  func (h ∷ _) (there m)   (here refl) = ⊥-elim (not-in h m)
  func (_ ∷ u) (there m)   (there m′)  = func u m m′

  -- (mirrors `lookupImport`'s `with`)
  lookup-func : ∀ (L : ISig) {k v} → (k , v) ∈ L → (∀ {v′} → (k , v′) ∈ L → v′ ≡ v) → lookupImport L k ≡ just v
  lookup-func ((n , ty) ∷ rest) {k} m f with StrProp._≟_ n k
  ... | yes refl = cong just (f (here refl))
  ... | no ne    = lookup-func rest (rest-mem m) (λ m′ → f (there m′))
    where
      rest-mem : ∀ {v} → (k , v) ∈ ((n , ty) ∷ rest) → (k , v) ∈ rest
      rest-mem (here refl) = ⊥-elim (ne refl)
      rest-mem (there m′)  = m′


-- a declaration of Σ, in its table
mem-toISig : ∀ {Σ c t} → (c ∶ t) ∈ Σ → (showCanonical c , declTy t) ∈ toISig Σ
mem-toISig {(c ∶ t) ∷ Σ} (here refl) = here refl
mem-toISig {_ ∷ Σ}       (there m)   = there (mem-toISig m)

-- the FFI entries' facts, at a key of their table
facts-at : ∀ {fs k T} → All FFIFacts fs → (k , T) ∈ entrySig fs → IsConcrete T × HonestFFI T × RigidFree T
facts-at {Parser.e-fun (Parser.mkFunInfo n ft b p) ∷ fs} ((refl , ty , refl , c , h , g) ∷ fa) (here refl) = c , h , g
facts-at {Parser.e-fun (Parser.mkFunInfo n ft b p) ∷ fs} ((refl , ty , refl , c , h , g) ∷ fa) (there m)   = facts-at fa m
facts-at {Parser.e-poly _ ∷ fs} (() ∷ fa) m

-- A declaration of Σ, in the scope's (reversed) table at its rendered name.
sig-at : ∀ Σ fs → toISig Σ ≡ entrySig fs → AllPairs _≢_ (keys (entrySig fs)) → ∀ {c t} → (c ∶ t) ∈ Σ
       → lookupImport (entrySig fs ʳ++ []) (showCanonical c) ≡ just (declTy t)
sig-at Σ fs e u M =
  let m₀ = subst (_ ∈_) e (mem-toISig M)
  in lookup-func (entrySig fs ʳ++ []) (mem-ʳ++ (entrySig fs) m₀) (λ m′ → func u m₀ (from (ʳ++-mem (entrySig fs) m′)))
  where
    from : ∀ {x : String × LT.Type} → (x ∈ entrySig fs ⊎ x ∈ []) → x ∈ entrySig fs
    from (inj₁ m) = m
    from (inj₂ ())

-- `Walk`'s `h-sig`, for the scope past the FFI declarations.
h-sig-of : ∀ Σ fs → toISig Σ ≡ entrySig fs → AllPairs _≢_ (keys (entrySig fs)) → All FFIFacts fs
         → ∀ {m} (Δ : ST.KCtx m) {c t} → (c ∶ t) ∈ Σ
         → Σ[ T ∈ LT.Type ] (lookupImport (entrySig fs ʳ++ []) (showCanonical c) ≡ just T) × IsConcrete T × TyR Δ T ⌜ t ⌝ᵈ
h-sig-of Σ fs e u fa Δ {c} {t} M =
  let (k , h , g) = facts-at fa (subst (_ ∈_) e (mem-toISig M))
  in declTy t , sig-at Σ fs e u M , k
     , subst (λ t′ → TyR Δ (declTy t) ⌜ t′ ⌝ᵈ) (declS-declTy t) (Once.Adequacy.SpecFront.Types.decl-R Δ k h g)
