{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Observation — what a run is observed as (D058, D061).
--
-- An INTERPRETATION of the signature Σ is what the world provides: the value
-- of each constant and pure arrow, and an answer to each call, which may
-- depend on the calls made before it (the history). A halting operation
-- (answer type `void`) is not answered: the run ends there. An
-- Interpretation's author provides it off-line; the compiler never sees one.
--
-- What a program DOES is the sequence of its calls against an
-- Interpretation; its first `n` are `events ι n`. That is the whole
-- observable: correctness of a compiled program is equality of these
-- sequences, at every depth, for every Interpretation.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Observation (Σ : Signature) where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Once.Spec.Grade using (mk-kind; pure; act; eff⁺; eff)
open import Once.Spec.Signature
  using (BTy; unit; void; int; float; _*_; _+_; ⟦_⟧ᵇ; DeclType; constant; arrow; _∶_; argAt;
         Op; module Op; arg; Layer; call; Event; eventOf)
open Op using (ans)
open import Once.Spec.Effect Σ using (T∞; Step; done; node; module T∞)
open T∞ using (force)

-- The declarations whose meaning is a value.
Value : DeclType → Set
Value (constant b)                = ⊤
Value (arrow a (mk-kind q pure) b) = ⊤
Value (arrow a (mk-kind q act) b)  = ⊥
Value (arrow a (mk-kind q eff⁺) b) = ⊥
Value (arrow a (mk-kind q eff) b)  = ⊥

⟦_⟧ᵈ : DeclType → Set
⟦ constant b ⟧ᵈ           = ⟦ b ⟧ᵇ
⟦ arrow a (mk-kind q π) b ⟧ᵈ = ⟦ argAt q a ⟧ᵇ → ⟦ b ⟧ᵇ

-- What a call is answered with: nothing at `void` (the run halts), a value
-- otherwise.
Answer : BTy → Set
Answer void    = ⊤
Answer unit    = ⟦ unit ⟧ᵇ
Answer int     = ⟦ int ⟧ᵇ
Answer float   = ⟦ float ⟧ᵇ
Answer (a * b) = ⟦ a * b ⟧ᵇ
Answer (a + b) = ⟦ a + b ⟧ᵇ

History : Set
History = List Event

record Interp : Set where
  field
    value  : ∀ {c t} → (c ∶ t) ∈ Σ → Value t → ⟦ t ⟧ᵈ
    answer : (o : Op Σ) → History → ⟦ arg o ⟧ᵇ → Answer (ans o)
open Interp

-- Continue from an answer, unless the operation halts.
resume : (b : BTy) → Answer b → ∀ {X : Set} → (⟦ b ⟧ᵇ → X) → Maybe X
resume void    _ k = nothing
resume unit    v k = just (k v)
resume int     v k = just (k v)
resume float   v k = just (k v)
resume (a * b) v k = just (k v)
resume (a + b) v k = just (k v)

-- The first `n` calls a computation makes against `ι`, after the history `h`.
events     : ∀ {X} → Interp → History → T∞ X → ℕ → List Event
stepEvents : ∀ {X} → Interp → History → Step X (T∞ X) → ℕ → List Event
next       : ∀ {X} → Interp → History → Maybe (T∞ X) → ℕ → List Event
events ι h m zero    = []
events ι h m (suc n) = stepEvents ι h (force m) n
stepEvents ι h (done x)            n = []
stepEvents ι h (node (call o a k)) n =
  eventOf o a ∷ next ι (h ++ [ eventOf o a ]) (resume (ans o) (answer ι o h a) k) n
next ι h (just m) n = events ι h m n
next ι h nothing  n = []

------------------------------------------------------------------------
-- A behaviour is a PREFIX FAMILY (D179): observing one call further only
-- extends what was observed, the `n`-th observation has at most `n` calls,
-- and one that stops short is complete.
------------------------------------------------------------------------

open import Data.List using (length)
open import Data.Nat using (_≤_; _<_)
open import Data.Product using (∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

record PrefixFamily (tr : ℕ → List Event) : Set where
  field
    bounded    : ∀ k → length (tr k) ≤ k
    saturating : ∀ k → length (tr k) < k → tr (suc k) ≡ tr k
    coherent   : ∀ k → ∃[ rest ] (tr (suc k) ≡ tr k ++ rest)
