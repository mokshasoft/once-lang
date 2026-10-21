-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Start — the walk's first state (plan 0.121 §3.6,
-- F6).
--
-- Past the FFI declarations the scope is their table, no definition yet.
-- The definitions' entries are what `Walk.EntriesOK` asks of them there:
-- distinct names (`distinct-rest`), none a declaration of the table
-- (`nosig-rest`: the extractor's guard keeps every entry name distinct, the
-- FFI ones included), new to the (empty) definitions.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Start where

open import Data.List using (List; []; _∷_; _++_; map; _ʳ++_)
open import Data.List.Properties using (map-++)
import Data.List.Properties
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
import Data.String.Properties as StrProp

open import Once.Internal.Contract using (ISig)
import Once.Parser as Parser
open import Once.Internal.Module using (entrySig)
open import Once.Internal.Typing.Scope using (lookupImport)
open import Once.Adequacy.SpecFront.SigFacts using (keys; keys-all; mem-toISig)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Once.Spec.Signature using (Signature; _∶_)
open import Once.Spec.Name using (canonical)
open import Once.Adequacy.SpecInterp using (toISig)
open import Relation.Nullary using (¬_)

private
  split : ∀ (xs ys : List String) → AllPairs _≢_ (xs ++ ys) → All (λ x → All (x ≢_) ys) xs × AllPairs _≢_ ys
  split []       ys u       = [] , u
  split (x ∷ xs) ys (h ∷ u) = let (a , r) = split xs ys u in AllP.++⁻ʳ xs h ∷ a , r

  all-ʳ++ : ∀ {A : Set} {P : A → Set} (xs : List A) {acc} → All P xs → All P acc → All P (xs ʳ++ acc)
  all-ʳ++ []       [] b = b
  all-ʳ++ (x ∷ xs) (p ∷ a) b = all-ʳ++ xs a (p ∷ b)

  -- (mirrors `lookupImport`'s `with`)
  lookup-none : ∀ (L : ISig) {x} → All (_≢ x) (keys L) → lookupImport L x ≡ nothing
  lookup-none [] _ = refl
  lookup-none ((n , ty) ∷ rest) {x} (h ∷ a) with StrProp._≟_ n x
  ... | yes e = ⊥-elim (h e)
  ... | no _  = lookup-none rest a

  flip-all : ∀ {xs : List String} {y} → All (λ x → All (x ≢_) (y ∷ [])) xs → All (_≢ y) xs
  flip-all [] = []
  flip-all ((n ∷ []) ∷ a) = n ∷ flip-all a

  pointwise : ∀ {xs ys : List String} → All (λ x → All (x ≢_) ys) xs → All (λ y → All (_≢ y) xs) ys
  pointwise {xs} {[]} a = []
  pointwise {xs} {y ∷ ys} a = flip-all (All.map (λ { (n ∷ _) → n ∷ [] }) a) ∷ pointwise (All.map (λ { (_ ∷ r) → r }) a)

names : List Parser.Entry → List String
names = map Parser.entryNameOf

-- the definitions' names are distinct…
distinct-rest : ∀ fs es → AllPairs _≢_ (names (fs ++ es)) → AllPairs _≢_ (names es)
distinct-rest fs es u = proj₁ (split′ (subst (AllPairs _≢_) (map-++ Parser.entryNameOf fs es) u))
  where
    split′ : AllPairs _≢_ (names fs ++ names es) → AllPairs _≢_ (names es) × All (λ x → All (x ≢_) (names es)) (names fs)
    split′ u′ = let (a , r) = split (names fs) (names es) u′ in r , a

-- …and none a declaration in the scope's table
nosig-rest : ∀ fs es → AllPairs _≢_ (names (fs ++ es)) → All (λ x → lookupImport (entrySig fs ʳ++ []) x ≡ nothing) (names es)
nosig-rest fs es u =
  let (a , _) = split (names fs) (names es) (subst (AllPairs _≢_) (map-++ Parser.entryNameOf fs es) u)
  in All.map (λ {y} h → lookup-none (entrySig fs ʳ++ []) (keys-ʳ++ (keys-all fs h))) (pointwise a)
  where
    keys-ʳ++ : ∀ {P : String → Set} {L : ISig} → All P (keys L) → All P (keys (L ʳ++ []))
    keys-ʳ++ {P} {L} a′ = subst (All P) (sym (Data.List.Properties.map-ʳ++ proj₁ L)) (all-ʳ++ (keys L) a′ [])

-- new to no definition
fresh-start : ∀ es → All (λ x → All (x ≢_) ([] ++ [])) (names es)
fresh-start es = All.tabulate (λ _ → [])

-- A definition's name is not a declaration of Σ.
not-sig : ∀ (Σ : Signature) fs es → toISig Σ ≡ entrySig fs → AllPairs _≢_ (names (fs ++ es))
        → ∀ {x t} → x ∈ names es → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ)
not-sig Σ fs es e u {x} mx M =
  let (a , _) = split (names fs) (names es) (subst (AllPairs _≢_) (map-++ Parser.entryNameOf fs es) u)
      mk = ∈-map⁺ proj₁ (subst (_ ∈_) e (mem-toISig M))
      inF = All.lookup (keys-all {P = _∈ names fs} fs (All.tabulate (λ m → m))) mk
  in All.lookup (All.lookup a inF) mx refl
