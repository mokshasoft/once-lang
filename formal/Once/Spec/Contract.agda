-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Contract — THE COMPILER'S CONTRACT FORM (plan 0.105, D257
-- amendment 2; D061's three times).
--
-- Compiling a user program sees only an interpretation's DECLARED signatures
-- (`ISig`) and trusts them; each interpretation's author discharges their
-- contracts OFF-LINE. WHAT a declaration owes is the compiler's decision
-- (`contractOf`, read off the declared type as the elaborator reads it, D225):
-- interpretations follow the compiler.
------------------------------------------------------------------------

module Once.Spec.Contract where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Membership.DecPropositional as DecMem
open import Once.Type using (Type; _⇒[_]_; mk-kind; Zero; One; Many; Void; isVoid?; isUnit?) renaming (Unit to UnitT)
import Once.Type as Ty
open import Once.Type.DecEq using (_≟T_)

-- A CONTRACT KEY: a SigOp as an interpretation declares it — its RENDERED
-- canonical path (the import table's key, the symbol the linker matches) with
-- its domain and codomain. Inside the program a SigOp's identity stays its
-- `CanonicalName`; this is the identity at the interpretation boundary.
record Key : Set where
  constructor key
  field
    kname : String
    kdom  : Type
    kcod  : Type
open Key public


_≟K_ : DecidableEquality Key
key n A B ≟K key n′ A′ B′ = go (n ≟ˢ n′) (A ≟T A′) (B ≟T B′)
  where
    go : Dec (n ≡ n′) → Dec (A ≡ A′) → Dec (B ≡ B′) → Dec (key n A B ≡ key n′ A′ B′)
    go (yes refl) (yes refl) (yes refl) = yes refl
    go (no ¬p) _ _ = no λ { refl → ¬p refl }
    go (yes _) (no ¬p) _ = no λ { refl → ¬p refl }
    go (yes _) (yes _) (no ¬p) = no λ { refl → ¬p refl }

open import Data.List.Membership.Propositional using (_∈_)

_∈K?_ : (k : Key) (ks : List Key) → Dec (k ∈ ks)
_∈K?_ = DecMem._∈?_ _≟K_

-- An interpretation's declared signatures: each SigOp's canonical name and
-- declared FFI type.
ISig : Set
ISig = List (String × Type)

-- What a declaration owes, in the compiler's contract form: a VALUE (a pure
-- contract — referentially transparent, D250 — or a zero-multiplicity
-- reference, which the meaning reads as a value), an ANSWER to a call (an
-- effectful arrow into data), or nothing (an effectful arrow into `Unit`
-- emits, into `Void` halts).
data Contract : Set where
  value   : Key → Contract
  answers : Key → Contract
  effect  : Contract

contract-eff : String → (A B : Type) → Dec (B ≡ Void) → Dec (B ≡ UnitT) → Contract
contract-eff c A B (yes _) _       = effect
contract-eff c A B (no _)  (yes _) = effect
contract-eff c A B (no _)  (no _)  = answers (key c A B)

contractOf : String → Type → Contract
contractOf c (A ⇒[ mk-kind Zero π ]    B) = value (key c UnitT B)
contractOf c (A ⇒[ mk-kind One  Ty.pure ] B) = value (key c A B)
contractOf c (A ⇒[ mk-kind Many Ty.pure ] B) = value (key c A B)
contractOf c (A ⇒[ mk-kind One  Ty.eff ]  B) = contract-eff c A B (isVoid? B) (isUnit? B)
contractOf c (A ⇒[ mk-kind Many Ty.eff ]  B) = contract-eff c A B (isVoid? B) (isUnit? B)
contractOf c T                            = value (key c UnitT T)

valueKeys answerKeys : ISig → List Key
valueKeys []            = []
valueKeys ((c , T) ∷ Σ) = go (contractOf c T)
  where go : Contract → List Key
        go (value k) = k ∷ valueKeys Σ
        go _         = valueKeys Σ
answerKeys []            = []
answerKeys ((c , T) ∷ Σ) = go (contractOf c T)
  where go : Contract → List Key
        go (answers k) = k ∷ answerKeys Σ
        go _           = answerKeys Σ

