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
-- Interpretation; its first `n` are `events ι n`, a `Delay` (D317): they
-- arrive once the run has made `n` calls or ended, and never if it goes on
-- forever without another call. That is the whole observable: correctness
-- of a compiled program is that these arrive at the same sequences, or both
-- never arrive, at every depth, for every Interpretation.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Spec.Observation (Σ : Signature) where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (mk-kind; pure; act; eff)
open import Once.Spec.Signature
  using (BTy; unit; void; int; float; _*_; _+_; ⟦_⟧ᵇ; DeclType; constant; arrow; _∶_; argAt;
         Op; module Op; arg; Layer; call; Event; eventOf)
open Op using (ans)
open import Once.Spec.Effect Σ using (T; roll; done; node; T∞; module T∞)
open T∞ using (force)
open import Once.Spec.Delay using (Delay; module Delay; mapD; _⇓_)
open Delay using (step)

-- The declarations whose meaning is a value.
Value : DeclType → Set
Value (constant b)                 = ⊤
Value (arrow a (mk-kind q pure) b) = ⊤
Value (arrow a (mk-kind q act) b)  = ⊥
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

------------------------------------------------------------------------
-- Observing a run
------------------------------------------------------------------------

-- How a run ends, as far as it is observed: with a value, halted by an
-- operation that answers nothing, or cut where the observation stops.
data End (X : Set) : Set where
  returned : X → End X
  halted   : End X
  cut      : End X

-- The first `n` calls a computation makes against `ι`, in a world that has
-- seen the calls `h`, and how it ends. A block's end is one step of the
-- delay: a run that goes on forever without another call never arrives.
-- What the world has seen (what it answers from) and what the run has made
-- (what is observed) are kept apart, so observing `m >>= f` observes `m`'s
-- calls and then `f`'s.
observe     : ∀ {X} → Interp → History → T∞ X → ℕ → Delay (History × End X)
observeFrom : ∀ {X} → Interp → History → History → T∞ X → ℕ → Delay (History × End X)
blockObs    : ∀ {X} → Interp → History → History → T (X ⊎ T∞ X) → ℕ → (History × End X) ⊎ Delay (History × End X)
answerObs   : ∀ {X} → Interp → History → History → Maybe (T (X ⊎ T∞ X)) → ℕ → (History × End X) ⊎ Delay (History × End X)
observe ι h m n = observeFrom ι h [] m n
-- … having made the calls `c` so far.
step (observeFrom ι h c m n) = blockObs ι h c (force m) n
blockObs ι h c t                          zero    = inj₁ (c , cut)
blockObs ι h c (roll (done (inj₁ x)))     (suc n) = inj₁ (c , returned x)
blockObs ι h c (roll (done (inj₂ m)))     (suc n) = inj₂ (observeFrom ι h c m (suc n))
blockObs ι h c (roll (node (call o a k))) (suc n) =
  answerObs ι (h ++ [ eventOf o a ]) (c ++ [ eventOf o a ]) (resume (ans o) (answer ι o h a) k) n
answerObs ι h c nothing  n = inj₁ (c , halted)
answerObs ι h c (just t) n = blockObs ι h c t n

-- The calls alone.
events : ∀ {X} → Interp → History → T∞ X → ℕ → Delay History
events ι h m n = mapD proj₁ (observe ι h m n)

------------------------------------------------------------------------
-- A behaviour is a PREFIX FAMILY (D179): the `n`-th observation has at most
-- `n` calls, observing one call further only extends what was observed (and
-- arrives whenever the shorter one does not stop at the bound), and one that
-- stops short is complete.
------------------------------------------------------------------------

record PrefixFamily (tr : ℕ → Delay History) : Set where
  field
    bounded    : ∀ k {h} → tr k ⇓ h → length h ≤ k
    coherent   : ∀ k {h′} → tr (suc k) ⇓ h′ → ∃[ h ] ∃[ rest ] (tr k ⇓ h × h′ ≡ h ++ rest)
    saturating : ∀ k {h} → tr k ⇓ h → length h < k → tr (suc k) ⇓ h
