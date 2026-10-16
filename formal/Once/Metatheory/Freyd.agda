{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Freyd — effects form a Freyd category, up to what is
-- observed (`Spec.Metatheory.Freyd`).
--
-- Over a larger signature with a fresh operation (the PROBE, named longer
-- than every name of Σ), a central computation commutes with one call of
-- the probe. Observed to one visible step, the probe-first order makes the
-- probe's call; so does the other order, and since every call of the
-- computation is an operation of Σ, the computation returned before any
-- call. A run that returns without a call reads nothing from the world, so
-- the computation is observed as that `return`. Dropped before `return tt`,
-- a discardable computation is found the same way. The pairing laws then
-- follow because sameness respects `>>=`.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Freyd (Σ : Signature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; concatMap; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Properties using (length-++; ∷-injectiveˡ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-trans; +-comm; n≮n)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (CanonicalName; canonical; module CanonicalName)
open import Once.Spec.Grade using (Many)
open import Once.Spec.Signature
  using (Decl; module Decl; _∶_; operation; unit; Op; module Op; op; eventOf; Event; module Event)
import Once.Spec.Effect as Effect
import Once.Spec.Observation as Observation
import Once.Spec.Equivalence as Equivalence
import Once.Metatheory.Bisim as Bisim
import Once.Metatheory.Observe as Observe
import Once.Metatheory.Run as RunM
import Once.Metatheory.RunLaws as RunLaws
import Once.Metatheory.Trace as Trace
import Once.Metatheory.Coherence.Relation as Relation
open import Once.Spec.Metatheory using (Freyd; Central; Commute; pairK; lift; liftBlock; liftOp)

open Effect Σ
open Observation Σ using (World; End; returned; halted; returned≈; halted≈)
open Equivalence Σ using (_≃_)
open Bisim Σ
open RunM Σ
open RunLaws Σ using (run-det; run-det-calls; module Seq)
open Trace Σ using (MaybeEnd; cut≈; end≈)
open Relation Σ

open νM using (outν)
open _≈ν_ using (force≈)

------------------------------------------------------------------------
-- Bisimilar computations are observed the same
------------------------------------------------------------------------

≈→≃ : ∀ {Σ₀ : Signature} {X : Set} {m m′ : Effect.T∞ Σ₀ X} → Effect._≈_ Σ₀ m m′ → Equivalence._≃_ Σ₀ m m′
≈→≃ {Σ₀} p w = Observe.trace-≈ Σ₀ w [] p

------------------------------------------------------------------------
-- Computations related to themselves; a run with no call
------------------------------------------------------------------------

private
  reflEnd : ∀ {X : Set} {e : Maybe (End X)} → MaybeEnd _≡_ e e
  reflEnd {e = nothing}             = cut≈
  reflEnd {e = just (returned x)}   = end≈ (returned≈ refl)
  reflEnd {e = just halted}         = end≈ halted≈

Related-refl : ∀ {X : Set} (m : T∞ X) → Related _≡_ m m
Related-refl m = Related-self (λ _ → reflEnd)

-- A run that returns without a call reads nothing from the world: it is the
-- run in every world, to every depth past zero.
private
  noCallB : ∀ {X} {w₀ h₀ k} {t : T (X ⊎ T∞ X)} {y : X} → RunB w₀ h₀ t (suc k) [] (just (returned y))
          → ∀ (w : World) h n → RunB w h t (suc n) [] (just (returned y))
  noCallB {t = roll (done (inj₁ x))} rb-ret w h n = rb-ret
  noCallB {t = roll (done (inj₂ m))} (rb-next r) w h n = rb-next (noCallB {t = force m} r w h n)

noCallSame : ∀ {X} {m : T∞ X} {y : X} → (∀ (w : World) h n → Run w h m (suc n) [] (just (returned y))) → m ≃ return∞ y
noCallSame {X} {m} {y} G = toObserved (related fw bw)
  where
    fw : Sim _≡_ m (return∞ y)
    fw w h zero    (run rb-cut) = nothing , run rb-cut , cut≈
    fw w h (suc n) {d} {e} r = fin (run-det-calls w r (G w h n)) (run-det w r (G w h n))
      where fin : d ≡ [] → e ≡ just (returned y) → ∃[ e′ ] (Run w h (return∞ y) (suc n) d e′ × MaybeEnd _≡_ e e′)
            fin refl refl = just (returned y) , run rb-ret , end≈ (returned≈ refl)
    bw : Sim (λ a b → b ≡ a) (return∞ y) m
    bw w h zero    (run rb-cut) = nothing , run rb-cut , cut≈
    bw w h (suc n) (run rb-ret) = just (returned y) , G w h n , end≈ (returned≈ refl)

------------------------------------------------------------------------
-- The probe: a fresh operation over a larger signature
------------------------------------------------------------------------

private
  allParts : Signature → List String
  allParts Σ₀ = concatMap (λ d → CanonicalName.parts (Decl.name d)) Σ₀

  fresh : CanonicalName
  fresh = canonical (allParts Σ ++ ("probe" ∷ []))

  ≤-parts : ∀ {Σ₀ : Signature} {c t} → (c ∶ t) ∈ Σ₀ → length (CanonicalName.parts c) ≤ length (allParts Σ₀)
  ≤-parts {c ∶ t ∷ Σ₀} (here refl) =
    subst (length (CanonicalName.parts c) ≤_) (sym (length-++ (CanonicalName.parts c))) (m≤m+n _ _)
  ≤-parts {d ∷ Σ₀} (there p) =
    ≤-trans (≤-parts p) (subst (length (allParts Σ₀) ≤_) (sym (length-++ (CanonicalName.parts (Decl.name d)))) (m≤n+m _ _))

  -- No name of Σ is the probe's.
  fresh≢ : ∀ {c t} → (c ∶ t) ∈ Σ → ¬ (c ≡ fresh)
  fresh≢ {c} p refl = n≮n (length (allParts Σ)) (subst (_≤ length (allParts Σ)) lenFresh (≤-parts p))
    where lenFresh : length (allParts Σ ++ ("probe" ∷ [])) ≡ suc (length (allParts Σ))
          lenFresh = trans (length-++ (allParts Σ)) (+-comm (length (allParts Σ)) 1)

  Σ′ : Signature
  Σ′ = (fresh ∶ operation unit Many unit) ∷ Σ

  module E′ = Effect Σ′
  module O′ = Observation Σ′
  module R′ = RunM Σ′
  module RL′ = RunLaws Σ′
  module Rel′ = Relation Σ′
  module Tr′ = Trace Σ′

  probeOp : Op Σ′
  probeOp = op (here refl)

  probeEv : Event
  probeEv = eventOf probeOp tt

  probe : E′.T∞ ⊤
  probe = E′.embed (E′.performT (call probeOp tt (λ b → b)))

  w′ : O′.World
  w′ = Rel′.aWorld

  ι : Σ ⊆ Σ′
  ι = there

  -- Every call a lifted computation makes is a call of Σ.
  firstCall : ∀ {X} {h} (t : T (X ⊎ T∞ X)) {n v d e} → R′.RunB w′ h (liftBlock ι t) n (v ∷ d) e
            → Σ[ o ∈ Op Σ ] ∃[ a ] (v ≡ eventOf o a)
  firstCall (roll (done (inj₂ m))) (R′.rb-next r) = firstCall (force m) r
  firstCall (roll (node (call o a k))) (R′.rb-call r) = o , a , refl

  notProbe : ∀ {X} {h} (t : T (X ⊎ T∞ X)) {n d e} → R′.RunB w′ h (liftBlock ι t) n (probeEv ∷ d) e → ⊥
  notProbe t r = go (firstCall t r)
    where go : Σ[ o ∈ Op Σ ] ∃[ a ] (probeEv ≡ eventOf o a) → ⊥
          go (o , a , eq) = fresh≢ (Op.declared o) (sym (cong Event.ev-name eq))

  -- A lifted run that returns without a call is a run of Σ that does.
  liftNoCall : ∀ {X} {h k} (t : T (X ⊎ T∞ X)) {y : X} → R′.RunB w′ h (liftBlock ι t) (suc k) [] (just (O′.returned y))
             → ∀ (w : World) h n → RunB w h t (suc n) [] (just (returned y))
  liftNoCall (roll (done (inj₁ x))) R′.rb-ret w h n = rb-ret
  liftNoCall (roll (done (inj₂ m))) (R′.rb-next r) w h n = rb-next (liftNoCall (force m) r w h n)
  liftNoCall (roll (node (call o a k))) ()

  -- The probe first, observed to one call.
  probeRun : ∀ {X} {m : T∞ X} → R′.Run w′ [] (probe E′.>>=∞ λ u → lift ι m E′.>>=∞ λ y → E′.return∞ (y , u)) 1 (probeEv ∷ []) nothing
  probeRun = R′.run (R′.rb-call (R′.ra-go R′.rb-cut))

------------------------------------------------------------------------
-- A central computation is pure
------------------------------------------------------------------------

central-pure : ∀ {Y : Set} (m : T∞ Y) → Central Σ m → Σ[ y ∈ Y ] m ≃ return∞ y
central-pure {Y} m c = found (RL′.Seq.split w′ k (lift ι m) (proj₁ (proj₂ matched)))
  where
    k : Y → E′.T∞ (Y × ⊤)
    k y = probe E′.>>=∞ λ u → E′.return∞ (y , u)
    matched : ∃[ e ] (R′.Run w′ [] (lift ι m E′.>>=∞ k) 1 (probeEv ∷ []) e × Tr′.MaybeEnd (λ a b → b ≡ a) nothing e)
    matched = Rel′.bwd (Rel′.fromObserved (c ι probe)) w′ [] 1 probeRun
    returned-first : ∀ {x d₁ d₂} → probeEv ∷ [] ≡ d₁ ++ d₂ → R′.Run w′ [] (lift ι m) 1 d₁ (just (O′.returned x))
                   → Σ[ y ∈ Y ] m ≃ return∞ y
    returned-first {x} {[]} eq (R′.run p) = x , noCallSame (λ w h n → run (liftNoCall (force m) p w h n))
    returned-first {x} {v ∷ d₁} eq (R′.run p) = ⊥-elim (notProbe (force m) (subst (λ u → R′.RunB w′ [] _ 1 (u ∷ d₁) _) (∷-injectiveˡ (sym eq)) p))
    found : RL′.Seq.Split w′ k (R′.Run w′ [] (lift ι m) 1) [] 1 (probeEv ∷ []) _ → Σ[ y ∈ Y ] m ≃ return∞ y
    found (RL′.Seq.returns eq p q) = returned-first eq p
    found (RL′.Seq.stops s (R′.run p)) = ⊥-elim (notProbe (force m) p)

------------------------------------------------------------------------
-- A discardable computation is pure
------------------------------------------------------------------------

discard-pure : ∀ {Y : Set} (m : T∞ Y) → (∀ {W : Set} (k : T∞ W) → (m >>=∞ λ _ → k) ≃ k) → Σ[ y ∈ Y ] m ≃ return∞ y
discard-pure {Y} m h = found (Seq.split aWorld (λ _ → return∞ tt) m (proj₁ (proj₂ matched)))
  where
    matched : ∃[ e ] (Run aWorld [] (m >>=∞ λ _ → return∞ tt) 1 [] e × MaybeEnd (λ a b → b ≡ a) (just (returned tt)) e)
    matched = bwd (fromObserved (h (return∞ tt))) aWorld [] 1 (run rb-ret)
    returned-first : ∀ {x d₁ d₂} → [] ≡ d₁ ++ d₂ → Run aWorld [] m 1 d₁ (just (returned x)) → Σ[ y ∈ Y ] m ≃ return∞ y
    returned-first {x} {[]} eq (run p) = x , noCallSame (λ w h₁ n → run (noCallB p w h₁ n))
    notStop : ∀ {e₀} {e : Maybe (End ⊤)} → RunLaws.Stops Σ e₀ e → e ≡ just (returned tt) → ⊥
    notStop RunLaws.halts ()
    notStop RunLaws.cuts  ()
    found : Seq.Split aWorld (λ _ → return∞ tt) (Run aWorld [] m 1) [] 1 [] (proj₁ matched) → Σ[ y ∈ Y ] m ≃ return∞ y
    found (Seq.returns eq p q) = returned-first eq p
    found (Seq.stops s p) = ⊥-elim (notStop s (endOf (proj₂ (proj₂ matched))))
      where endOf : ∀ {e} → MaybeEnd (λ a b → b ≡ a) (just (returned tt)) e → e ≡ just (returned tt)
            endOf (end≈ (returned≈ refl)) = refl

------------------------------------------------------------------------
-- A pure computation is central
------------------------------------------------------------------------

module _ {Σ″ : Signature} where
  private
    module E″ = Effect Σ″
    module B″ = Bisim Σ″

    byForce″ : ∀ {X} (m m′ : E″.T∞ X) → E″.force m ≡ E″.force m′ → E″._≈_ m m′
    E″._≈ν_.force≈ (byForce″ m m′ e) = subst (E″.BlockEq _ (E″.force m)) e (B″.≈-reflB (E″.force m))

  pureCentral : ∀ {Y : Set} (y : Y) (ι : Σ ⊆ Σ″) {W : Set} (n : E″.T∞ W) → Commute Σ″ (lift ι (return∞ y)) n
  pureCentral y ι n =
    ≈→≃ (B″.≈-trans (byForce″ _ (n E″.>>=∞ λ w → E″.return∞ (y , w)) refl)
                    (B″.≈-sym (B″.≈-bind (B″.≈-refl n) (λ w → byForce″ _ _ refl))))

pure-central : ∀ {Y : Set} (y : Y) → Central Σ (return∞ y)
pure-central y ι n = pureCentral y ι n

------------------------------------------------------------------------
-- The pairing laws, up to what is observed
------------------------------------------------------------------------

module _ {X Y Z : Set} where
  pair-β₁ : ∀ (f : X → T∞ Y) (g : X → T∞ Z) → (∀ x → Central Σ (g x))
          → ∀ x → (pairK Σ f g x >>=∞ λ p → return∞ (proj₁ p)) ≃ f x
  pair-β₁ f g c x = toObserved (≈-Relatedˡ L≈ (≈-Relatedʳ (≈-sym (idʳ (f x))) (bindRel (Related-refl (f x)) inner)))
    where
      z₀ = proj₁ (central-pure (g x) (c x))
      gz = proj₂ (central-pure (g x) (c x))
      L≈ : (pairK Σ f g x >>=∞ λ p → return∞ (proj₁ p)) ≈ (f x >>=∞ λ y → g x >>=∞ λ z → return∞ y)
      L≈ = ≈-trans (assoc (f x) _ _) (≈-bind (≈-refl (f x)) λ y →
             ≈-trans (assoc (g x) _ _) (≈-bind (≈-refl (g x)) λ z → idˡ (y , z) _))
      inner : ∀ {y y′} → y ≡ y′ → Related _≡_ (g x >>=∞ λ z → return∞ y) (return∞ y′)
      inner {y} refl = ≈-Relatedʳ (≈-sym (idˡ z₀ (λ z → return∞ y))) (bindRel (fromObserved gz) λ _ → returnRel refl)

  pair-β₂ : ∀ (f : X → T∞ Y) (g : X → T∞ Z) → (∀ x → Central Σ (f x))
          → ∀ x → (pairK Σ f g x >>=∞ λ p → return∞ (proj₂ p)) ≃ g x
  pair-β₂ f g c x = toObserved (≈-Relatedˡ L≈ (≈-Relatedʳ R≈ (bindRel (fromObserved fy) λ _ → Related-refl (g x >>=∞ return∞))))
    where
      y₀ = proj₁ (central-pure (f x) (c x))
      fy = proj₂ (central-pure (f x) (c x))
      L≈ : (pairK Σ f g x >>=∞ λ p → return∞ (proj₂ p)) ≈ (f x >>=∞ λ y → g x >>=∞ return∞)
      L≈ = ≈-trans (assoc (f x) _ _) (≈-bind (≈-refl (f x)) λ y →
             ≈-trans (assoc (g x) _ _) (≈-bind (≈-refl (g x)) λ z → idˡ (y , z) _))
      R≈ : g x ≈ (return∞ y₀ >>=∞ λ y → g x >>=∞ return∞)
      R≈ = ≈-sym (≈-trans (idˡ y₀ _) (idʳ (g x)))

module _ {X Y Z : Set} where
  pair-η : ∀ (h : X → T∞ (Y × Z)) → (∀ x → Central Σ (h x))
         → ∀ x → pairK Σ (λ x → h x >>=∞ λ p → return∞ (proj₁ p)) (λ x → h x >>=∞ λ p → return∞ (proj₂ p)) x ≃ h x
  pair-η h c x = toObserved (Related-trans trans (≈-Relatedˡ L≈ (≈-Relatedʳ R≈ both)) back)
    where
      p₀ = proj₁ (central-pure (h x) (c x))
      hp = proj₂ (central-pure (h x) (c x))
      L≈ : pairK Σ (λ x → h x >>=∞ λ p → return∞ (proj₁ p)) (λ x → h x >>=∞ λ p → return∞ (proj₂ p)) x
           ≈ (h x >>=∞ λ p → h x >>=∞ λ q → return∞ (proj₁ p , proj₂ q))
      L≈ = ≈-trans (assoc (h x) _ _) (≈-bind (≈-refl (h x)) λ p →
             ≈-trans (idˡ (proj₁ p) _)
               (≈-trans (assoc (h x) _ _) (≈-bind (≈-refl (h x)) λ q → idˡ (proj₂ q) _)))
      R≈ : return∞ p₀ ≈ (return∞ p₀ >>=∞ λ p → return∞ p₀ >>=∞ λ q → return∞ (proj₁ p , proj₂ q))
      R≈ = ≈-sym (≈-trans (idˡ p₀ _) (idˡ p₀ _))
      both : Related _≡_ (h x >>=∞ λ p → h x >>=∞ λ q → return∞ (proj₁ p , proj₂ q))
                         (return∞ p₀ >>=∞ λ p → return∞ p₀ >>=∞ λ q → return∞ (proj₁ p , proj₂ q))
      both = bindRel (fromObserved hp) λ { refl → bindRel (fromObserved hp) λ { refl → returnRel refl } }
      back : Related _≡_ (return∞ p₀) (h x)
      back = Related-mono sym (Related-flip (fromObserved hp))

freyd : Freyd Σ
freyd = record
  { pure-central = pure-central
  ; central-pure = central-pure
  ; discard-pure = discard-pure
  ; pair-β₁ = pair-β₁
  ; pair-β₂ = pair-β₂
  ; pair-η  = pair-η
  }
