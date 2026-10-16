{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.RunLaws — how runs compose.
--
-- A run in a world that has seen `h ++ h′` is a run from `h′` against the
-- Interpretation that answers as if it had seen `h` first (`shift`,
-- `unshift`). A run of `m >>= f` is a run of `m` that stops, or one that
-- returns `x` followed by a run of `f x` from where it returned, with the
-- depth that is left (`split`, `bind-stop`, `bind-ret`). Bisimilar
-- computations have the same runs (`run-≈`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.RunLaws (Σ : Signature) where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Once.Spec.Signature using (BTy; void; unit; int; float; _*_; _+_; eventOf; module Op)
open Op using (ans)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ
open import Once.Metatheory.Run Σ
open import Once.Metatheory.Observe Σ using (transfer)

open T∞ using (force)

------------------------------------------------------------------------
-- The world's history
------------------------------------------------------------------------

-- Answering as if the world had seen `h` first.
_⇑_ : Interp → History → Interp
ι ⇑ h = record { value = Interp.value ι ; answer = λ o h′ a → Interp.answer ι o (h ++ h′) a }

module _ (ι : Interp) (h : History) where
  open Interp ι using (answer)

  private
    shiftB : ∀ {X g h′ t n d} {e : End X} → g ≡ h ++ h′ → RunB ι g t n d e → RunB (ι ⇑ h) h′ t n d e
    shiftA : ∀ {X g h′ mt n d} {e : End X} → g ≡ h ++ h′ → RunA ι g mt n d e → RunA (ι ⇑ h) h′ mt n d e
    shiftB q rb-cut = rb-cut
    shiftB q rb-ret = rb-ret
    shiftB q (rb-next r) = rb-next (shiftB q r)
    shiftB {h′ = h′} refl (rb-call {o = o} {a} r) = rb-call (shiftA (++-assoc h h′ [ eventOf o a ]) r)
    shiftA q ra-halt = ra-halt
    shiftA q (ra-go r) = ra-go (shiftB q r)

    unshiftB : ∀ {X g h′ t n d} {e : End X} → h ++ h′ ≡ g → RunB (ι ⇑ h) h′ t n d e → RunB ι g t n d e
    unshiftA : ∀ {X g h′ mt n d} {e : End X} → h ++ h′ ≡ g → RunA (ι ⇑ h) h′ mt n d e → RunA ι g mt n d e
    unshiftB q rb-cut = rb-cut
    unshiftB q rb-ret = rb-ret
    unshiftB q (rb-next r) = rb-next (unshiftB q r)
    unshiftB {h′ = h′} refl (rb-call {o = o} {a} r) = rb-call (unshiftA (sym (++-assoc h h′ [ eventOf o a ])) r)
    unshiftA q ra-halt = ra-halt
    unshiftA q (ra-go r) = ra-go (unshiftB q r)

  shift : ∀ {X h′} {m : T∞ X} {n d e} → Run ι (h ++ h′) m n d e → Run (ι ⇑ h) h′ m n d e
  shift (run r) = run (shiftB refl r)

  unshift : ∀ {X h′} {m : T∞ X} {n d e} → Run (ι ⇑ h) h′ m n d e → Run ι (h ++ h′) m n d e
  unshift (run r) = run (unshiftB refl r)

------------------------------------------------------------------------
-- Bisimilar computations have the same runs
------------------------------------------------------------------------

module _ (ι : Interp) where

  private
    landed : ∀ {X h} {m : T∞ X} {n d e} → Made ι h m n [] (d , e) → Run ι h m n d e
    landed (d′ , e′ , refl , r) = r

  run-≈ : ∀ {X} {m m′ : T∞ X} → m ≈ m′ → ∀ {h n d e} → Run ι h m n d e → Run ι h m′ n d e
  run-≈ {m′ = m′} p {h} {n} r = landed {m = m′} (run-complete ι h [] m′ n (transfer ι h p n (run-sound ι r [])))

------------------------------------------------------------------------
-- Sequencing
------------------------------------------------------------------------

-- How a run that does not return ends, before and after a continuation.
data Stops {X Y : Set} : End X → End Y → Set where
  halts : Stops halted halted
  cuts  : Stops cut cut

module Seq (ι : Interp) {X Y : Set} (f : X → T∞ Y) where
  open Interp ι using (answer)

  private
    snoc : ∀ (h : History) v d → (h ++ [ v ]) ++ d ≡ h ++ (v ∷ d)
    snoc h v d = ++-assoc h [ v ] d

  -- A run that stops stops the same way after `>>= f`.
  bind-stopB : ∀ {h t n d} {e₀ : End X} {e : End Y} → Stops e₀ e → RunB ι h t n d e₀ → RunB ι h (bindBlock t f) n d e
  stopRes    : ∀ (b : BTy) (v : Answer b) {k : _ → T (X ⊎ T∞ X)} {h n d} {e₀ : End X} {e : End Y}
             → Stops e₀ e → RunA ι h (resume b v k) n d e₀ → RunA ι h (resume b v (λ r → bindBlock (k r) f)) n d e
  bind-stopB s rb-cut = stopCut s
    where stopCut : ∀ {h t} {e : End Y} → Stops {X} cut e → RunB ι h t zero [] e
          stopCut cuts = rb-cut
  bind-stopB s (rb-next r) = rb-next (bind-stopB s r)
  bind-stopB s (rb-call {h = h} {o = o} {a = a} r) = rb-call (stopRes (ans o) (answer o h a) s r)
  stopRes void    v halts ra-halt = ra-halt
  stopRes unit    v s (ra-go r) = ra-go (bind-stopB s r)
  stopRes int     v s (ra-go r) = ra-go (bind-stopB s r)
  stopRes float   v s (ra-go r) = ra-go (bind-stopB s r)
  stopRes (a * b) v s (ra-go r) = ra-go (bind-stopB s r)
  stopRes (a + b) v s (ra-go r) = ra-go (bind-stopB s r)

  -- A run that returns `x`, then a run of `f x` with the depth left.
  bind-retB : ∀ {h t n d₁ x d₂} {e : End Y} → RunB ι h t n d₁ (returned x)
            → RunB ι (h ++ d₁) (force (f x)) (n ∸ length d₁) d₂ e → RunB ι h (bindBlock t f) n (d₁ ++ d₂) e
  retRes    : ∀ (b : BTy) (v : Answer b) {k : _ → T (X ⊎ T∞ X)} {h n d₁ x d₂} {e : End Y}
            → RunA ι h (resume b v k) n d₁ (returned x) → RunB ι (h ++ d₁) (force (f x)) (n ∸ length d₁) d₂ e
            → RunA ι h (resume b v (λ r → bindBlock (k r) f)) n (d₁ ++ d₂) e
  bind-retB {h = h} rb-ret q = subst (λ g → RunB ι g _ _ _ _) (++-identityʳ h) q
  bind-retB (rb-next r) q = rb-next (bind-retB r q)
  bind-retB {h = h} (rb-call {o = o} {a} {d = d₁} r) q =
    rb-call (retRes (ans o) (answer o h a) r (subst (λ g → RunB ι g _ _ _ _) (sym (snoc h (eventOf o a) d₁)) q))
  retRes void    v () q
  retRes unit    v (ra-go r) q = ra-go (bind-retB r q)
  retRes int     v (ra-go r) q = ra-go (bind-retB r q)
  retRes float   v (ra-go r) q = ra-go (bind-retB r q)
  retRes (a * b) v (ra-go r) q = ra-go (bind-retB r q)
  retRes (a + b) v (ra-go r) q = ra-go (bind-retB r q)

  bind-stop : ∀ {h} {m : T∞ X} {n d} {e₀ : End X} {e : End Y} → Stops e₀ e → Run ι h m n d e₀ → Run ι h (m >>=∞ f) n d e
  bind-stop s (run r) = run (bind-stopB s r)

  bind-ret : ∀ {h} {m : T∞ X} {n d₁ x d₂} {e : End Y} → Run ι h m n d₁ (returned x)
           → Run ι (h ++ d₁) (f x) (n ∸ length d₁) d₂ e → Run ι h (m >>=∞ f) n (d₁ ++ d₂) e
  bind-ret (run r) (run q) = run (bind-retB r q)

  -- A run of `m >>= f`, taken apart: what `P` says of the run of `m`.
  data Split (P : History → End X → Set) (h : History) (n : ℕ) (d : History) (e : End Y) : Set where
    returns : ∀ {x d₁ d₂} → d ≡ d₁ ++ d₂ → P d₁ (returned x)
            → RunB ι (h ++ d₁) (force (f x)) (n ∸ length d₁) d₂ e → Split P h n d e
    stops   : ∀ {e₀} → Stops e₀ e → P d e₀ → Split P h n d e

  mapSplit : ∀ {P P′ : History → End X → Set} {h n d e} → (∀ {d₀ e₀} → P d₀ e₀ → P′ d₀ e₀) → Split P h n d e → Split P′ h n d e
  mapSplit g (returns q p r) = returns q (g p) r
  mapSplit g (stops s p)     = stops s (g p)

  private

    cutAt : ∀ {Z h t d} {e : End Z} → RunB ι h t zero d e → d ≡ [] × e ≡ cut
    cutAt rb-cut = refl , refl

    atZero : ∀ {h t d e} → d ≡ [] × e ≡ cut → Split (RunB ι h t zero) h zero d e
    atZero (refl , refl) = stops cuts rb-cut

    -- One call further out: the calls and the world both start with it.
    callSplit : ∀ {h o a k n d e}
              → Split (RunA ι (h ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n) (h ++ [ eventOf o a ]) n d e
              → Split (RunB ι h (roll (node (call o a k))) (suc n)) h (suc n) (eventOf o a ∷ d) e
    callSplit {h = h} {o} {a} (returns {d₁ = d₁} q p r) =
      returns (cong (eventOf o a ∷_) q) (rb-call p) (subst (λ g → RunB ι g _ _ _ _) (snoc h (eventOf o a) d₁) r)
    callSplit (stops s p) = stops s (rb-call p)

  splitB   : ∀ {h} (t : T (X ⊎ T∞ X)) {n d e} → RunB ι h (bindBlock t f) n d e → Split (RunB ι h t n) h n d e
  splitRes : ∀ (b : BTy) (v : Answer b) (k : _ → T (X ⊎ T∞ X)) {h n d e}
           → RunA ι h (resume b v (λ r → bindBlock (k r) f)) n d e → Split (RunA ι h (resume b v k) n) h n d e
  splitB (roll (done (inj₁ x))) {zero}  r = atZero (cutAt r)
  splitB {h} (roll (done (inj₁ x))) {suc n} r = returns refl rb-ret (subst (λ g → RunB ι g _ _ _ _) (sym (++-identityʳ h)) r)
  splitB (roll (done (inj₂ m))) {zero}  r = atZero (cutAt r)
  splitB (roll (done (inj₂ m))) {suc n} (rb-next r) = mapSplit rb-next (splitB (force m) r)
  splitB (roll (node (call o a k))) {zero} r = atZero (cutAt r)
  splitB {h} (roll (node (call o a k))) {suc n} (rb-call r) = callSplit (splitRes (ans o) (answer o h a) k r)
  splitRes void    v k ra-halt = stops halts ra-halt
  splitRes unit    v k (ra-go r) = mapSplit ra-go (splitB (k v) r)
  splitRes int     v k (ra-go r) = mapSplit ra-go (splitB (k v) r)
  splitRes float   v k (ra-go r) = mapSplit ra-go (splitB (k v) r)
  splitRes (a * b) v k (ra-go r) = mapSplit ra-go (splitB (k v) r)
  splitRes (a + b) v k (ra-go r) = mapSplit ra-go (splitB (k v) r)

  split : ∀ {h} (m : T∞ X) {n d e} → Run ι h (m >>=∞ f) n d e → Split (Run ι h m n) h n d e
  split m (run r) = mapSplit run (splitB (force m) r)

------------------------------------------------------------------------
-- A run's end is determined
------------------------------------------------------------------------

module _ (ι : Interp) where
  private
    detB : ∀ {X h t n d d′} {e e′ : End X} → RunB ι h t n d e → RunB ι h t n d′ e′ → e ≡ e′
    detA : ∀ {X h mt n d d′} {e e′ : End X} → RunA ι h mt n d e → RunA ι h mt n d′ e′ → e ≡ e′
    detB rb-cut      rb-cut       = refl
    detB rb-ret      rb-ret       = refl
    detB (rb-next r) (rb-next r′) = detB r r′
    detB (rb-call r) (rb-call r′) = detA r r′
    detA ra-halt     ra-halt      = refl
    detA (ra-go r)   (ra-go r′)   = detB r r′

  run-det : ∀ {X h} {m : T∞ X} {n d d′ e e′} → Run ι h m n d e → Run ι h m n d′ e′ → e ≡ e′
  run-det (run r) (run r′) = detB r r′
