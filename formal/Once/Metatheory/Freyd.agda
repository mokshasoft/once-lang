{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Freyd — effects form a Freyd category
-- (`Spec.Metatheory.Freyd`).
--
-- `T∞` has no silent node, so a computation that is not a value is
-- observably one: its root is a call. Over a larger signature with a fresh
-- operation (the PROBE), a root call does not commute with a call of the
-- probe, so a central computation is a value (A′, plan 0.119). Dropped before
-- `return∞ tt`, a root call changes the root, so a discardable computation is
-- a value too. The pairing laws are then `T∞`'s monad laws.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Freyd (Σ : Signature) where

open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (gen)
open import Once.Spec.Grade using (mk-kind; Many; eff)
open import Once.Spec.Signature using (_∶_; arrow; unit; op; e-eff; Effectful; BTy)
import Once.Spec.Effect as Effect
import Once.Metatheory.Bisim as Bisim
open import Once.Spec.Metatheory using (Freyd; Central; pairK; lift; liftBlock)

open Effect Σ
open T∞ using (force)
open _≈_ using (force≈)
open Bisim Σ

private
  ret-≈ : ∀ {Y} {m : T∞ Y} {y} → force m ≡ roll (done (inj₁ y)) → m ≈ return∞ y
  force≈ (ret-≈ {y = y} e) = subst (λ t → BlockEq _≈_ t (roll (done (inj₁ y)))) (sym e) return≈

  -- A block that calls, or ends to continue, is not one that returns.
  noND : ∀ {X : Set} {R : T∞ X → T∞ X → Set} {o a k} {x : X} → ¬ BlockEq R (roll (node (call o a k))) (roll (done (inj₁ x)))
  noND ()
  noNextRet : ∀ {X : Set} {R : T∞ X → T∞ X → Set} {m} {x : X} → ¬ BlockEq R (roll (done (inj₂ m))) (roll (done (inj₁ x)))
  noNextRet ()

  -- The larger signature with the probe, and one call of it.
  Σ′ : Signature
  Σ′ = (gen "probe" ∶ arrow unit (mk-kind Many eff) unit) ∷ Σ

  module E′ = Effect Σ′
  module B′ = Bisim Σ′

  probe : E′.T∞ ⊤
  probe = E′.perform (call (op (here refl) e-eff) tt (λ b → b))

  -- A lifted call of Σ is not the probe's.
  clash : ∀ {Z : Set} {nm dm q π an} {d : (nm ∶ arrow dm (mk-kind q π) an) ∈ Σ} {ef : Effectful π} {a k k′}
        → ¬ E′.BlockEq {X = Z} E′._≈_ (E′.roll (E′.node (call (op (there d) ef) a k))) (E′.roll (E′.node (call (op (here refl) e-eff) tt k′)))
  clash ()

  -- A block that ends to continue is not one that calls.
  clashNext : ∀ {Z : Set} {m k′}
            → ¬ E′.BlockEq {X = Z} E′._≈_ (E′.roll (E′.done (inj₂ m))) (E′.roll (E′.node (call (op (here refl) e-eff) tt k′)))
  clashNext ()

-- The central computation against the probe: each run's first block.
private
  probeRel : ∀ {Y : Set} (m : T∞ Y) → Central Σ m
           → E′.BlockEq E′._≈_ (E′.bindBlock (liftBlock there (force m)) (λ y → probe E′.>>=∞ λ w → E′.return∞ (y , w)))
                               (E′.bindBlock (E′.T∞.force probe) (λ w → lift there m E′.>>=∞ λ y → E′.return∞ (y , w)))
  probeRel m c = E′._≈_.force≈ (c there probe)

central-pureB : ∀ {Y : Set} (m : T∞ Y) (t : T (Y ⊎ T∞ Y)) → force m ≡ t → Central Σ m → Σ[ y ∈ Y ] m ≈ return∞ y
central-pureB m (roll (done (inj₁ y))) e c = y , ret-≈ e
central-pureB {Y} m (roll (done (inj₂ m′))) e c =
  ⊥-elim (clashNext (subst (λ t → E′.BlockEq {X = Y × ⊤} E′._≈_
                                    (E′.bindBlock (liftBlock there t) (λ y → probe E′.>>=∞ λ w → E′.return∞ (y , w)))
                                    (E′.bindBlock (E′.T∞.force probe) (λ w → lift there m E′.>>=∞ λ y → E′.return∞ (y , w))))
                           e (probeRel m c)))
central-pureB {Y} m (roll (node (call (op d ef) a k))) e c =
  ⊥-elim (clash (subst (λ t → E′.BlockEq {X = Y × ⊤} E′._≈_
                                (E′.bindBlock (liftBlock there t) (λ y → probe E′.>>=∞ λ w → E′.return∞ (y , w)))
                                (E′.bindBlock (E′.T∞.force probe) (λ w → lift there m E′.>>=∞ λ y → E′.return∞ (y , w))))
                       e (probeRel m c)))

central-pure : ∀ {Y : Set} (m : T∞ Y) → Central Σ m → Σ[ y ∈ Y ] m ≈ return∞ y
central-pure m = central-pureB m (force m) refl

discard-pureB : ∀ {Y : Set} (m : T∞ Y) (t : T (Y ⊎ T∞ Y)) → force m ≡ t
              → (∀ {W : Set} (k : T∞ W) → (m >>=∞ λ _ → k) ≈ k) → Σ[ y ∈ Y ] m ≈ return∞ y
discard-pureB m (roll (done (inj₁ y))) e h = y , ret-≈ e
discard-pureB m (roll (done (inj₂ m′))) e h =
  ⊥-elim (noNextRet (subst (λ t → BlockEq _≈_ (bindBlock t (λ _ → return∞ tt)) (roll (done (inj₁ tt)))) e (force≈ (h (return∞ tt)))))
discard-pureB m (roll (node (call o a k))) e h =
  ⊥-elim (noND (subst (λ t → BlockEq _≈_ (bindBlock t (λ _ → return∞ tt)) (roll (done (inj₁ tt)))) e (force≈ (h (return∞ tt)))))

discard-pure : ∀ {Y : Set} (m : T∞ Y) → (∀ {W : Set} (k : T∞ W) → (m >>=∞ λ _ → k) ≈ k) → Σ[ y ∈ Y ] m ≈ return∞ y
discard-pure m = discard-pureB m (force m) refl

module PureCentral {Σ″ : Signature} where
  private
    module E″ = Effect Σ″
    module B″ = Bisim Σ″

  byForce″ : ∀ {X} (m m′ : E″.T∞ X) → E″.T∞.force m ≡ E″.T∞.force m′ → m E″.≈ m′
  E″._≈_.force≈ (byForce″ m m′ e) = subst (E″.BlockEq E″._≈_ (E″.T∞.force m)) e (B″.≈-reflB (E″.T∞.force m))

pure-central : ∀ {Y : Set} (y : Y) → Central Σ (return∞ y)
pure-central y {Σ″} ι n =
  B″.≈-trans (byForce″ _ (n E″.>>=∞ λ w → E″.return∞ (y , w)) refl)
             (B″.≈-sym (B″.≈-bind (B″.≈-refl n) (λ w → byForce″ _ _ refl)))
  where
    module E″ = Effect Σ″
    module B″ = Bisim Σ″
    open PureCentral {Σ″}

β₁-at : ∀ {Y Z : Set} (m : T∞ Y) (n : T∞ Z) → Σ[ z ∈ Z ] n ≈ return∞ z
      → ((m >>=∞ λ y → n >>=∞ λ z → return∞ (y , z)) >>=∞ λ p → return∞ (proj₁ p)) ≈ m
β₁-at m n (z₀ , nz) =
  ≈-trans (assoc m _ _)
    (≈-trans (≈-bind (≈-refl m) (λ y →
               ≈-trans (assoc n _ _)
                 (≈-trans (≈-bind nz (λ z → idˡ (y , z) _)) (idˡ z₀ _))))
             (idʳ m))

β₂-at : ∀ {Y Z : Set} (m : T∞ Y) (n : T∞ Z) → Σ[ y ∈ Y ] m ≈ return∞ y
      → ((m >>=∞ λ y → n >>=∞ λ z → return∞ (y , z)) >>=∞ λ p → return∞ (proj₂ p)) ≈ n
β₂-at m n (y₀ , my) =
  ≈-trans (assoc m _ _)
    (≈-trans (≈-bind my (λ y → ≈-refl _))
      (≈-trans (idˡ y₀ _)
        (≈-trans (assoc n _ _)
          (≈-trans (≈-bind (≈-refl n) (λ z → idˡ (y₀ , z) _)) (idʳ n)))))

η-at : ∀ {Y Z : Set} (m : T∞ (Y × Z)) → Σ[ p ∈ Y × Z ] m ≈ return∞ p
     → ((m >>=∞ λ p → return∞ (proj₁ p)) >>=∞ λ y → (m >>=∞ λ p → return∞ (proj₂ p)) >>=∞ λ z → return∞ (y , z)) ≈ m
η-at m (p₀ , mp) =
  ≈-trans (≈-bind (proj-at proj₁) (λ y → ≈-refl _))
    (≈-trans (idˡ (proj₁ p₀) _)
      (≈-trans (≈-bind (proj-at proj₂) (λ z → ≈-refl _))
        (≈-trans (idˡ (proj₂ p₀) _) (≈-sym mp))))
  where
    proj-at : ∀ {C : Set} (π : _ → C) → (m >>=∞ λ p → return∞ (π p)) ≈ return∞ (π p₀)
    proj-at π = ≈-trans (≈-bind mp (λ p → ≈-refl _)) (idˡ p₀ _)

freyd : Freyd Σ
freyd = record
  { pure-central = pure-central
  ; central-pure = central-pure
  ; discard-pure = discard-pure
  ; pair-β₁ = λ f g c x → β₁-at (f x) (g x) (central-pure (g x) (c x))
  ; pair-β₂ = λ f g c x → β₂-at (f x) (g x) (central-pure (f x) (c x))
  ; pair-η  = λ h c x → η-at (h x) (central-pure (h x) (c x))
  }
