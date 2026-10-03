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
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String) renaming (_≟_ to _≟ˢ_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Membership.DecPropositional as DecMem
open import Once.Type using (Type; _⇒[_]_; mk-kind; Zero; One; Many; Void; isVoid?; isUnit?) renaming (Unit to UnitT)
import Once.Type as Ty
open import Once.Type.DecEq using (_≟T_)
open import Data.Empty using (⊥-elim)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Denotation.Trace using (SigOpEvent)

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
open import Data.List.Relation.Unary.Any using (here; there)

_∈K?_ : (k : Key) (ks : List Key) → Dec (k ∈ ks)
_∈K?_ = DecMem._∈?_ _≟K_

-- A decision on a membership that holds is `yes` (of the decided proof).
yes-of : ∀ {k ks} → k ∈ ks → Σ (k ∈ ks) (λ p₀ → (k ∈K? ks) ≡ yes p₀)
yes-of {k} {ks} p = go (k ∈K? ks)
  where go : (d : Dec (k ∈ ks)) → Σ (k ∈ ks) (λ p₀ → d ≡ yes p₀)
        go (yes p₀) = p₀ , refl
        go (no ¬p)  = ⊥-elim (¬p p)

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

-- The value and answer keys a signature declares. Built by top-level steps (no
-- `where`), so a proof can follow a declaration to its key.
value-step answer-step : Contract → List Key → List Key
value-step (value k)   ks = k ∷ ks
value-step (answers _) ks = ks
value-step effect      ks = ks
answer-step (value _)   ks = ks
answer-step (answers k) ks = k ∷ ks
answer-step effect      ks = ks

valueKeys answerKeys : ISig → List Key
valueKeys []            = []
valueKeys ((c , T) ∷ Σ) = value-step (contractOf c T) (valueKeys Σ)
answerKeys []            = []
answerKeys ((c , T) ∷ Σ) = answer-step (contractOf c T) (answerKeys Σ)

-- A declaration's key is declared.
private
  value-there : ∀ {k ks} (ct : Contract) → k ∈ ks → k ∈ value-step ct ks
  value-there (value _)   m = there m
  value-there (answers _) m = m
  value-there effect      m = m
  answer-there : ∀ {k ks} (ct : Contract) → k ∈ ks → k ∈ answer-step ct ks
  answer-there (value _)   m = m
  answer-there (answers _) m = there m
  answer-there effect      m = m

value-∈ : ∀ {Σ x T k} → (x , T) ∈ Σ → contractOf x T ≡ value k → k ∈ valueKeys Σ
value-∈ {(c , T) ∷ Σ} (here refl) eq rewrite eq = here refl
value-∈ {(c , T) ∷ Σ} (there m)   eq = value-there (contractOf c T) (value-∈ m eq)

answer-∈ : ∀ {Σ x T k} → (x , T) ∈ Σ → contractOf x T ≡ answers k → k ∈ answerKeys Σ
answer-∈ {(c , T) ∷ Σ} (here refl) eq rewrite eq = here refl
answer-∈ {(c , T) ∷ Σ} (there m)   eq = answer-there (contractOf c T) (answer-∈ m eq)

------------------------------------------------------------------------
-- WHAT AN INTERPRETATION'S AUTHOR OWES: an implementation of its declared
-- signatures `Σ` in the compiler's contract form, discharged OFF-LINE
-- (proved, or postulated for an unverified target). It is TOTAL on `Σ`:
--   * `answerI`: an answering declaration's result for an argument, given the
--     calls the program made before it — what it answers is the author's
--     business;
--   * `pureI`: a value declaration's value at an argument. It sees no history:
--     a pure contract is referentially transparent (D250).
-- An emitting or halting declaration owes no value. A declaration nobody can
-- implement (an answering call into an empty type) makes `Impl Σ` empty: its
-- author cannot discharge it, and no compiler claim becomes false.
------------------------------------------------------------------------

record Impl (Σ : ISig) : Set where
  field
    answerI : List SigOpEvent → (k : Key) → k ∈ answerKeys Σ → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
    pureI   : (k : Key) → k ∈ valueKeys Σ → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
open Impl public

-- THE reading of a declared value contract: through the membership DECISION,
-- so every reader (the Spec's meaning, the IR, the machines) takes the same
-- position of `Σ` — the typing's proof only rules the `no` branch out.
valueOf-at : ∀ {Σ} → Impl Σ → (k : Key) → k ∈ valueKeys Σ → Dec (k ∈ valueKeys Σ) → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
valueOf-at I k p (yes p₀) = pureI I k p₀
valueOf-at I k p (no ¬p)  = ⊥-elim (¬p p)

valueOf : ∀ {Σ} → Impl Σ → (k : Key) → k ∈ valueKeys Σ → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
valueOf {Σ} I k p = valueOf-at I k p (k ∈K? valueKeys Σ)

-- A first-order constant (not an arrow) is a value contract at `Unit → A`.
base-contract : ∀ {A} (x : String) → IsBaseType A → contractOf x A ≡ value (key x UnitT A)
base-contract x base-Unit        = refl
base-contract x base-Void        = refl
base-contract x base-Int         = refl
base-contract x base-Float       = refl
base-contract x (base-Prod a b)  = refl
base-contract x (base-Sum a b)   = refl
base-contract x base-rigid       = refl
