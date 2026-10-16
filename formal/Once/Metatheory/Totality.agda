{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Totality — total and productive
-- (`Spec.Metatheory.Totality`).
--
--   * a run's events are a prefix family: one event per node, and a run that
--     ended stays ended;
--   * a definition cannot name itself or a later one: the name resolves to
--     the module's own entry, which the definitions signature does not yet
--     hold, and Σ is empty;
--   * the stream and the echo server are typed; the stream's first layer
--     calls `tick`, and each round of the server makes two calls, so at
--     depth `n` it has made `n`.
------------------------------------------------------------------------

module Once.Metatheory.Totality where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; length; [_])
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (_≟_)
open import Relation.Nullary.Decidable using (toWitnessFalse)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (0≤q; ⊑-pe)
open import Once.Spec.Name using (CanonicalName; canonical; GenWord; genWords)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (TySub; Respects; ∅ₖ)
open import Once.Spec.Signature using (Signature; call; BTy; void; unit; int; float; _*_; _+_)
open import Once.Spec.Type using (wf-Id)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Resolution
open import Once.Spec.Surface.Program
open import Once.Spec.Core.Syntax using (Defs; [])
import Once.Spec.Context
import Once.Spec.Type
import Once.Spec.Grade
open import Once.Spec.Examples
import Once.Spec.Effect as Effect
import Once.Spec.Observation as Observation
import Once.Spec.Core.Typing as CoreTyping
import Once.Spec.Core.Meaning as Meaning
import Once.Spec.Surface.Typing as SurfaceTyping
open import Once.Spec.Metatheory using (Totality)

------------------------------------------------------------------------
-- A run is a prefix family
------------------------------------------------------------------------

module Prefix (Σ : Signature) (ι : Observation.Interp Σ) where
  open Effect Σ using (T∞; Step; done; node; module T∞)
  open T∞ using (force)
  open Observation Σ using (History; events; stepEvents; next; resume; PrefixFamily)

  bounded  : ∀ {X} h (m : T∞ X) k → length (events ι h m k) ≤ k
  boundedS : ∀ {X} h (s : Step X (T∞ X)) k → length (stepEvents ι h s k) ≤ suc k
  boundedN : ∀ {X} h (b : BTy) v (k′ : _ → T∞ X) k → length (next ι h (resume b v k′) k) ≤ k
  bounded h m zero    = z≤n
  bounded h m (suc k) = boundedS h (force m) k
  boundedS h (done x)            k = z≤n
  boundedS h (node (call o a k′)) k = s≤s (boundedN _ _ _ k′ k)
  boundedN h void    v k′ k = z≤n
  boundedN h unit    v k′ k = bounded h (k′ v) k
  boundedN h int     v k′ k = bounded h (k′ v) k
  boundedN h float   v k′ k = bounded h (k′ v) k
  boundedN h (a * b) v k′ k = bounded h (k′ v) k
  boundedN h (a + b) v k′ k = bounded h (k′ v) k

  saturating  : ∀ {X} h (m : T∞ X) k → length (events ι h m k) < k → events ι h m (suc k) ≡ events ι h m k
  saturatingS : ∀ {X} h (s : Step X (T∞ X)) k → length (stepEvents ι h s k) < suc k
              → stepEvents ι h s (suc k) ≡ stepEvents ι h s k
  saturatingN : ∀ {X} h (b : BTy) v (k′ : _ → T∞ X) k → length (next ι h (resume b v k′) k) < k
              → next ι h (resume b v k′) (suc k) ≡ next ι h (resume b v k′) k
  saturating h m zero    ()
  saturating h m (suc k) l = saturatingS h (force m) k l
  saturatingS h (done x)             k l = refl
  saturatingS h (node (call o a k′)) k (s≤s l) = cong (_ ∷_) (saturatingN _ _ _ k′ k l)
  saturatingN h void    v k′ k l = refl
  saturatingN h unit    v k′ k l = saturating h (k′ v) k l
  saturatingN h int     v k′ k l = saturating h (k′ v) k l
  saturatingN h float   v k′ k l = saturating h (k′ v) k l
  saturatingN h (a * b) v k′ k l = saturating h (k′ v) k l
  saturatingN h (a + b) v k′ k l = saturating h (k′ v) k l

  coherent  : ∀ {X} h (m : T∞ X) k → ∃[ rest ] (events ι h m (suc k) ≡ events ι h m k ++ rest)
  coherentS : ∀ {X} h (s : Step X (T∞ X)) k → ∃[ rest ] (stepEvents ι h s (suc k) ≡ stepEvents ι h s k ++ rest)
  coherentN : ∀ {X} h (b : BTy) v (k′ : _ → T∞ X) k
            → ∃[ rest ] (next ι h (resume b v k′) (suc k) ≡ next ι h (resume b v k′) k ++ rest)
  coherent h m zero    = events ι h m 1 , refl
  coherent h m (suc k) = coherentS h (force m) k
  coherentS h (done x)             k = [] , refl
  coherentS h (node (call o a k′)) k = cons (coherentN _ _ _ k′ k)
    where cons : ∀ {x : Observation.Event Σ} {A B : List _} → ∃[ r ] (A ≡ B ++ r) → ∃[ r ] (x ∷ A ≡ (x ∷ B) ++ r)
          cons (r , e) = r , cong (_ ∷_) e
  coherentN h void    v k′ k = [] , refl
  coherentN h unit    v k′ k = coherent h (k′ v) k
  coherentN h int     v k′ k = coherent h (k′ v) k
  coherentN h float   v k′ k = coherent h (k′ v) k
  coherentN h (a * b) v k′ k = coherent h (k′ v) k
  coherentN h (a + b) v k′ k = coherent h (k′ v) k

  observable : ∀ h {X} (m : T∞ X) → PrefixFamily (events ι h m)
  observable h m = record { bounded = bounded h m ; saturating = saturating h m ; coherent = coherent h m }

------------------------------------------------------------------------
-- No general recursion
------------------------------------------------------------------------

module Unreachable (Σ : Signature) (empty : Σ ≡ []) (nm : Fin 0 → CanonicalName) where
  open SurfaceTyping Σ {0} [] nm

  private
    noMem : ∀ {Σ′ : Signature} {d} → Σ′ ≡ [] → ¬ (d ∈ Σ′)
    noMem refl ()

  noSynth : ∀ {m Δ n} {L : Locals m n} {x A t} → ¬ _⊢_⇒_↝_ Δ L (RResolved (canonical (x ∷ []))) A t
  noSynth (s-sigop _ mem) = noMem empty mem
  noSynth (s-def () _ _ _)

  noCheck : ∀ {m Δ n} {L : Locals m n} {x A t} → ¬ _⊢_⇐_↝_ Δ L (RResolved (canonical (x ∷ []))) A t
  noCheck (c-sub s _)        = noSynth s
  noCheck (c-sigop⁺ _ mem _) = noMem empty mem
  noCheck (c-poly () _ _ _ _)

private
  notGenF : ¬ GenWord "f"
  notGenF = toWitnessFalse {a? = any? ("f" ≟_) genWords} tt

  noFirst : ∀ {K V : Set} {x : K} {v : V} → ¬ FirstAt x v []
  noFirst ()

  -- With no imports, `f` resolves to the module's own entry.
  resolvesOwn : ∀ {e} → Resolves (env [] []) [] (RVar "f") e → e ≡ RResolved (canonical ("f" ∷ []))
  resolvesOwn (r-local ())
  resolvesOwn (r-name _ (rn-gen g))         = ⊥-elim (notGenF g)
  resolvesOwn (r-name _ (rn-import _ fa _)) = ⊥-elim (noFirst fa)
  resolvesOwn (r-name _ (rn-own _ _))       = refl

  checkOwn : ∀ {Σ} → Σ ≡ [] → ∀ {nm : Fin 0 → CanonicalName} {m Δ n} {L : SurfaceTyping.Locals Σ [] nm m n} {e A t}
           → e ≡ RResolved (canonical ("f" ∷ [])) → ¬ SurfaceTyping._⊢_⇐_↝_ Σ [] nm Δ L e A t
  checkOwn em {nm} refl = Unreachable.noCheck _ em nm

  selfDecls : List Decl
  selfDecls = Module.decls selfReference

  forwardDecls : List Decl
  forwardDecls = Module.decls forwardReference

  sigSelf : ∀ {Σ} → SignatureOf [] selfDecls Σ → Σ ≡ []
  sigSelf (_ , _ , so-other ns-tsig (so-other ns-def so-nil) , im-other ni-tsig (im-other ni-def im-nil) , e) = e

  sigForward : ∀ {Σ} → SignatureOf [] forwardDecls Σ → Σ ≡ []
  sigForward (_ , _ , so-other ns-tsig (so-other ns-def (so-other ns-tsig (so-other ns-def so-nil)))
                    , im-other ni-tsig (im-other ni-def (im-other ni-tsig (im-other ni-def im-nil))) , e) = e

  unSelf : ∀ {um} → Unaliased [] selfDecls um → um ≡ []
  unSelf (un-other nu-tsig (un-other nu-def un-nil)) = refl

  unForward : ∀ {um} → Unaliased [] forwardDecls um → um ≡ []
  unForward (un-other nu-tsig (un-other nu-def (un-other nu-tsig (un-other nu-def un-nil)))) = refl

  selfWalk : ∀ {Σ} → Σ ≡ [] → ∀ {rs} → ResolvesDecls (env [] []) selfDecls rs
           → ∀ {s′} {S′ : Defs s′} {nm′ tl′} {nm : Fin 0 → CanonicalName} {tl}
           → ¬ Walk Σ [] nm tl rs S′ nm′ tl′
  selfWalk em (rd-other nf-tsig (rd-def r rd-nil)) (w-sig _ b _) = checkOwn em (resolvesOwn r) (Body.check b)
  selfWalk em (rd-other nf-tsig (rd-def r rd-nil)) (w-skip () _)

  forwardWalk : ∀ {Σ} → Σ ≡ [] → ∀ {rs} → ResolvesDecls (env [] []) forwardDecls rs
              → ∀ {s′} {S′ : Defs s′} {nm′ tl′} {nm : Fin 0 → CanonicalName} {tl}
              → ¬ Walk Σ [] nm tl rs S′ nm′ tl′
  forwardWalk em (rd-other nf-tsig (rd-def r _)) (w-sig _ b _) = checkOwn em (resolvesOwn r) (Body.check b)
  forwardWalk em (rd-other nf-tsig (rd-def r _)) (w-skip () _)

  envOf : ∀ {um ds} → um ≡ [] → aliases ds ≡ [] → env um (aliases ds) ≡ env [] []
  envOf refl e = cong (env []) e

no-self-reference : ∀ {Σ p} → ¬ Denotes [] selfReference Σ p
no-self-reference D =
  selfWalk (sigSelf (Denotes.signature D))
           (subst′ (envOf (unSelf (Denotes.unaliases D)) refl) (Denotes.resolves D))
           (Denotes.walk D)
  where subst′ : ∀ {E E′ ds rs} → E ≡ E′ → ResolvesDecls E ds rs → ResolvesDecls E′ ds rs
        subst′ refl r = r

no-forward-reference : ∀ {Σ p} → ¬ Denotes [] forwardReference Σ p
no-forward-reference D =
  forwardWalk (sigForward (Denotes.signature D))
              (subst′ (envOf (unForward (Denotes.unaliases D)) refl) (Denotes.resolves D))
              (Denotes.walk D)
  where subst′ : ∀ {E E′ ds rs} → E ≡ E′ → ResolvesDecls E ds rs → ResolvesDecls E′ ds rs
        subst′ refl r = r

------------------------------------------------------------------------
-- The stream and the server
------------------------------------------------------------------------

module TickTyping = CoreTyping tickΣ []
module EchoTyping = CoreTyping echoΣ []

stream-typed : TickTyping._⊩_⊢[_]_∷_!_ ∅ₖ Once.Spec.Context.∅ [] ticker (Once.Spec.Type.ν Once.Spec.Type.Id Once.Spec.Grade.eff) Once.Spec.Grade.pure
stream-typed = TickTyping.⊢unfold wf-Id (TickTyping.⊢sigop (here refl)) TickTyping.⊢lit-int

server-typed : EchoTyping._⊩_⊢[_]_∷_!_ ∅ₖ Once.Spec.Context.∅ [] echoServer Once.Spec.Type.Void Once.Spec.Grade.eff
server-typed =
  EchoTyping.⊢iter
    (EchoTyping.⊢lam 0≤q (EchoTyping.⊢inr (EchoTyping.⊢lam 0≤q (EchoTyping.⊢inr
      (EchoTyping.⊢app (EchoTyping.⊢sigop (there (here refl)))
                       (EchoTyping.⊢app (EchoTyping.⊢sigop (here refl)) EchoTyping.⊢unit))))))
    EchoTyping.⊢unit

module Runs (fmt : TargetNum) (δ : Meaning.DefSem echoΣ fmt []) (σ : TySub 0 0) (r : Respects ∅ₖ ∅ₖ σ) where
  open Effect echoΣ using (T∞; module T∞)
  open T∞ using (force)
  open Observation echoΣ using (History; events; stepEvents)

  ι = Meaning.DefSem.interp δ
  run = Meaning.⟦_⟧ echoΣ fmt [] server-typed δ σ r tt

  evForce : ∀ {X} {h} {m m′ : T∞ X} n → force m ≡ force m′ → events ι h m n ≡ events ι h m′ n
  evForce zero    e = refl
  evForce (suc n) e = cong (λ s → stepEvents ι _ s n) e

  -- Each round is a read and a write, and then the next round.
  runs : ∀ n (h : History) → length (events ι h run n) ≡ n
  runs zero          h = refl
  runs (suc zero)    h = refl
  runs (suc (suc n)) h = cong (λ k → suc (suc k)) (trans (cong length (evForce {m′ = run} n refl)) (runs n _))

totality : Totality
totality = record
  { observable           = λ Σ ι h m → Prefix.observable Σ ι h m
  ; no-self-reference    = no-self-reference
  ; no-forward-reference = no-forward-reference
  ; stream-typed         = stream-typed
  ; stream-emits         = λ fmt δ → _ , _ , _ , refl
  ; server-typed         = server-typed
  ; server-runs          = λ fmt δ n → Runs.runs fmt δ _ _ n []
  }
