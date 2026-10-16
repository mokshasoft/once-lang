{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Totality — total and productive
-- (`Spec.Metatheory.Totality`).
--
--   * a run's calls are a prefix family, from every history
--     (`Once.Metatheory.Prefix`);
--   * a definition cannot name itself or a later one: the name resolves to
--     the module's own entry, which the definitions signature does not yet
--     hold, and Σ is empty;
--   * the stream and the echo server are typed; the stream's first layer
--     calls `tick`, and each round of the server makes two calls, so at
--     depth `n` it has made `n`;
--   * the silent loop is typed, and past depth zero what it does never
--     arrives: each round ends where it began.
------------------------------------------------------------------------

module Once.Metatheory.Totality where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; length; [_])
open import Data.List.Properties using (++-identityʳ; ++-assoc; length-++)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (_≟_)
open import Relation.Nullary.Decidable using (toWitnessFalse)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; +-identityʳ; +-assoc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (0≤q; ⊑-pa; ⊑-act)
open import Once.Spec.Name using (CanonicalName; canonical; GenWord; genWords)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (TySub; Respects; ∅ₖ)
open import Once.Spec.Signature using (Signature; call)
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
open import Once.Spec.Delay using (_⇓_; now⇓; later⇓)
open import Once.Metatheory.DelayLaws using (mapD⇓; mapD⇓⁻)
import Once.Metatheory.Prefix as Prefix
import Data.Empty

------------------------------------------------------------------------
-- A run is a prefix family
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
  selfWalk em (rd-other nf-tsig (rd-def r rd-nil)) (w-sig _ b _ _) = checkOwn em (resolvesOwn r) (Body.check b)
  selfWalk em (rd-other nf-tsig (rd-def r rd-nil)) (w-skip () _)

  forwardWalk : ∀ {Σ} → Σ ≡ [] → ∀ {rs} → ResolvesDecls (env [] []) forwardDecls rs
              → ∀ {s′} {S′ : Defs s′} {nm′ tl′} {nm : Fin 0 → CanonicalName} {tl}
              → ¬ Walk Σ [] nm tl rs S′ nm′ tl′
  forwardWalk em (rd-other nf-tsig (rd-def r _)) (w-sig _ b _ _) = checkOwn em (resolvesOwn r) (Body.check b)
  forwardWalk em (rd-other nf-tsig (rd-def r _)) (w-skip () _)

  envOf : ∀ {um ds} → um ≡ [] → aliases ds ≡ [] → env um (aliases ds) ≡ env [] []
  envOf refl e = cong (env []) e

no-self-reference : ∀ {Σ p} → ¬ Denotes [] selfReference Σ p
no-self-reference D =
  selfWalk (sigSelf (Denotes.signature D))
           (subst′ (envOf {ds = selfDecls} (unSelf (Denotes.unaliases D)) refl) (Denotes.resolves D))
           (Denotes.walk D)
  where subst′ : ∀ {E E′ ds rs} → E ≡ E′ → ResolvesDecls E ds rs → ResolvesDecls E′ ds rs
        subst′ refl r = r

no-forward-reference : ∀ {Σ p} → ¬ Denotes [] forwardReference Σ p
no-forward-reference D =
  forwardWalk (sigForward (Denotes.signature D))
              (subst′ (envOf {ds = forwardDecls} (unForward (Denotes.unaliases D)) refl) (Denotes.resolves D))
              (Denotes.walk D)
  where subst′ : ∀ {E E′ ds rs} → E ≡ E′ → ResolvesDecls E ds rs → ResolvesDecls E′ ds rs
        subst′ refl r = r

------------------------------------------------------------------------
-- The stream and the server
------------------------------------------------------------------------

module TickTyping   = CoreTyping tickΣ []
module EchoTyping   = CoreTyping echoΣ []
module SilentTyping = CoreTyping [] []

stream-typed : TickTyping._⊩_⊢[_]_∷_!_ ∅ₖ Once.Spec.Context.∅ Once.Spec.Context.[] ticker (Once.Spec.Type.ν Once.Spec.Type.Id Once.Spec.Grade.act) Once.Spec.Grade.pure
stream-typed = TickTyping.⊢unfold ⊑-act wf-Id (TickTyping.⊢sigop (here refl)) TickTyping.⊢lit-int

server-typed : EchoTyping._⊩_⊢[_]_∷_!_ ∅ₖ Once.Spec.Context.∅ Once.Spec.Context.[] echoServer Once.Spec.Type.Void Once.Spec.Grade.eff
server-typed =
  EchoTyping.⊢iter
    (EchoTyping.⊢lam 0≤q (EchoTyping.⊢inr
      (EchoTyping.⊢app (EchoTyping.⊢sigop (there (here refl)))
                       (EchoTyping.⊢app (EchoTyping.⊢sigop (here refl)) EchoTyping.⊢unit))))
    EchoTyping.⊢unit

silent-typed : SilentTyping._⊩_⊢[_]_∷_!_ ∅ₖ Once.Spec.Context.∅ Once.Spec.Context.[] silentLoop Once.Spec.Type.Void Once.Spec.Grade.eff
silent-typed =
  SilentTyping.⊢iter (SilentTyping.⊢lam 0≤q (SilentTyping.⊢sub-eff ⊑-pa (SilentTyping.⊢inr SilentTyping.⊢unit))) SilentTyping.⊢unit

module Runs (fmt : TargetNum) (δ : Meaning.DefSem echoΣ fmt []) (σ : TySub 0 0) (r : Respects ∅ₖ ∅ₖ σ) where
  open Observation echoΣ using (History; observeFrom)

  ι = Meaning.DefSem.interp δ
  run = Meaning.⟦_⟧ echoΣ fmt [] server-typed δ σ r tt

  private
    len2 : ∀ (c : History) e₁ e₂ n → length ((c ++ [ e₁ ]) ++ [ e₂ ]) + n ≡ length c + suc (suc n)
    len2 c e₁ e₂ n =
      trans (cong (_+ n) (trans (length-++ (c ++ [ e₁ ])) (cong (_+ 1) (length-++ c))))
            (trans (+-assoc (length c + 1) 1 n) (+-assoc (length c) 1 (suc n)))

  -- Each round is a read and a write, and then the next round.
  runs : ∀ n h (c : History) → ∃[ o ] (observeFrom ι h c run n ⇓ o × length (proj₁ o) ≡ length c + n)
  runs zero                h c = _ , now⇓ refl , sym (+-identityʳ (length c))
  runs (suc zero)          h c = _ , now⇓ refl , length-++ c
  runs (suc (suc zero))    h c = _ , now⇓ refl , trans (sym (+-identityʳ _)) (len2 c _ _ zero)
  runs (suc (suc (suc n))) h c =
    let r = runs (suc n) _ _ in
    proj₁ r , later⇓ refl (proj₁ (proj₂ r)) , trans (proj₂ (proj₂ r)) (len2 c _ _ (suc n))

module Silent (fmt : TargetNum) (δ : Meaning.DefSem [] fmt []) (σ : TySub 0 0) (r : Respects ∅ₖ ∅ₖ σ) where
  open Observation [] using (History; observeFrom)

  ι = Meaning.DefSem.interp δ
  run = Meaning.⟦_⟧ [] fmt [] silent-typed δ σ r tt

  -- Each round ends where it began: one more step of the delay, forever.
  never : ∀ n h c {o} → ¬ (observeFrom ι h c run (suc n) ⇓ o)
  never n h c (now⇓ ())
  never n h c (later⇓ refl d⇓) = never n h c d⇓

private
  server-runs : ∀ fmt (δ : Meaning.DefSem echoΣ fmt []) n
              → ∃[ h ] (Observation.events echoΣ (Meaning.DefSem.interp δ) []
                          (Meaning.⟦_⟧ echoΣ fmt [] server-typed δ (λ ()) (λ ()) tt) n ⇓ h × length h ≡ n)
  server-runs fmt δ n = pick (Runs.runs fmt δ (λ ()) (λ ()) n [] [])
    where
      pick : ∃[ o ] (Observation.observeFrom echoΣ (Meaning.DefSem.interp δ) [] [] (Runs.run fmt δ (λ ()) (λ ())) n ⇓ o
                     × length (proj₁ o) ≡ 0 + n)
           → ∃[ h ] (Observation.events echoΣ (Meaning.DefSem.interp δ) []
                       (Meaning.⟦_⟧ echoΣ fmt [] server-typed δ (λ ()) (λ ()) tt) n ⇓ h × length h ≡ n)
      pick (o , o⇓ , eq) = proj₁ o , mapD⇓ o⇓ , eq

  silent-never : ∀ fmt (δ : Meaning.DefSem [] fmt []) n {h}
               → ∃[ o ] (Observation.observeFrom [] (Meaning.DefSem.interp δ) [] [] (Silent.run fmt δ (λ ()) (λ ())) (suc n) ⇓ o
                         × proj₁ o ≡ h)
               → Data.Empty.⊥
  silent-never fmt δ n (o , o⇓ , _) = Silent.never fmt δ (λ ()) (λ ()) n [] [] o⇓

totality : Totality
totality = record
  { observable           = λ Σ ι h m → Prefix.observable Σ ι h m
  ; no-self-reference    = no-self-reference
  ; no-forward-reference = no-forward-reference
  ; stream-typed         = stream-typed
  ; stream-emits         = λ fmt δ → _ , _ , _ , refl
  ; server-typed         = server-typed
  ; server-runs          = server-runs
  ; silent-typed         = silent-typed
  ; silent-never         = λ fmt δ n h d⇓ → silent-never fmt δ n (mapD⇓⁻ d⇓)
  }
