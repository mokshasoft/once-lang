{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.RunLaws — how runs compose.
--
-- A run in a world that has seen `h ++ h′` is a run from `h′` in the world
-- that answers as if it had seen `h` first (`shift`, `unshift`). Bisimilar
-- computations have the same runs (`run-≈`). A run of `m >>= f` is a run of
-- `m` that stops, or one that returns `x` followed by a run of `f x` from
-- where it returned, with the depth that is left (`split`, `bind-stop`,
-- `bind-ret`). A run's end is determined (`run-det`).
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
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Signature using (Op; module Op; arg; ⟦_⟧ᵇ; NotEmpty; notEmpty?; eventOf)
open Op using (ans)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ using (World; module World; History; End; returned; halted)
open import Once.Metatheory.Run Σ
open import Once.Metatheory.Bisim Σ using (_≈B_; return≈; next≈)

open _≈ν_ using (force≈)

------------------------------------------------------------------------
-- The world's history
------------------------------------------------------------------------

-- Answering as if the world had seen `h` first.
_⇑_ : World → History → World
w ⇑ h = record { answer = λ o h′ a p → World.answer w o (h ++ h′) a p }

module _ (w : World) (h : History) where
  private
    shiftB : ∀ {X g h′ t n d} {e : Maybe (End X)} → g ≡ h ++ h′ → RunB w g t n d e → RunB (w ⇑ h) h′ t n d e
    shiftA : ∀ {X g h′ o a k D n d} {e : Maybe (End X)} → g ≡ h ++ h′ → RunA w g o a k D n d e → RunA (w ⇑ h) h′ o a k D n d e
    shiftB q rb-cut = rb-cut
    shiftB q rb-ret = rb-ret
    shiftB q (rb-next r) = rb-next (shiftB q r)
    shiftB q (rb-call r) = rb-call (shiftA q r)
    shiftA q (ra-go r) = goS q r
      where goS : ∀ {X g h′ o a} {k : _ → T (X ⊎ T∞ X)} {p n d} {e : Maybe (End X)} → g ≡ h ++ h′
                → RunB w (g ++ [ eventOf o a ]) (k (World.answer w o g a p)) n d e → RunA (w ⇑ h) h′ o a k (yes p) n d e
            goS {h′ = h′} {o = o} {a} refl r = ra-go (shiftB (++-assoc h h′ [ eventOf o a ]) r)
    shiftA q ra-halt = ra-halt
    shiftA q ra-cut  = ra-cut

    unshiftB : ∀ {X g h′ t n d} {e : Maybe (End X)} → h ++ h′ ≡ g → RunB (w ⇑ h) h′ t n d e → RunB w g t n d e
    unshiftA : ∀ {X g h′ o a k D n d} {e : Maybe (End X)} → h ++ h′ ≡ g → RunA (w ⇑ h) h′ o a k D n d e → RunA w g o a k D n d e
    unshiftB q rb-cut = rb-cut
    unshiftB q rb-ret = rb-ret
    unshiftB q (rb-next r) = rb-next (unshiftB q r)
    unshiftB q (rb-call r) = rb-call (unshiftA q r)
    unshiftA q (ra-go r) = goU q r
      where goU : ∀ {X g h′ o a} {k : _ → T (X ⊎ T∞ X)} {p n d} {e : Maybe (End X)} → h ++ h′ ≡ g
                → RunB (w ⇑ h) (h′ ++ [ eventOf o a ]) (k (World.answer w o (h ++ h′) a p)) n d e → RunA w g o a k (yes p) n d e
            goU {h′ = h′} {o = o} {a} refl r = ra-go (unshiftB (sym (++-assoc h h′ [ eventOf o a ])) r)
    unshiftA q ra-halt = ra-halt
    unshiftA q ra-cut  = ra-cut

  shift : ∀ {X h′} {m : T∞ X} {n d e} → Run w (h ++ h′) m n d e → Run (w ⇑ h) h′ m n d e
  shift (run r) = run (shiftB refl r)

  unshift : ∀ {X h′} {m : T∞ X} {n d e} → Run (w ⇑ h) h′ m n d e → Run w (h ++ h′) m n d e
  unshift (run r) = run (unshiftB refl r)

------------------------------------------------------------------------
-- Bisimilar computations have the same runs
------------------------------------------------------------------------

module _ (w : World) where
  private
    runB-≈ : ∀ {X h n d} {t t′ : T (X ⊎ T∞ X)} {e : Maybe (End X)} → t ≈B t′ → RunB w h t n d e → RunB w h t′ n d e
    runA-≈ : ∀ {X h o a n d} {k k′ : _ → T (X ⊎ T∞ X)} {D} {e : Maybe (End X)} → (∀ b → k b ≈B k′ b)
           → RunA w h o a k D n d e → RunA w h o a k′ D n d e
    runB-≈ _ rb-cut = rb-cut
    runB-≈ {t′ = roll (done (inj₁ _))} return≈ rb-ret = rb-ret
    runB-≈ {t′ = roll (done (inj₂ _))} (done≈ ()) rb-ret
    runB-≈ {t′ = roll (done (inj₂ m′))} (next≈ p) (rb-next r) = rb-next (runB-≈ (force≈ p) r)
    runB-≈ {t′ = roll (done (inj₁ _))} (done≈ ()) (rb-next r)
    runB-≈ (node≈ e) (rb-call r) = rb-call (runA-≈ e r)
    runA-≈ e (ra-go r) = ra-go (runB-≈ (e _) r)
    runA-≈ e ra-halt = ra-halt
    runA-≈ e ra-cut  = ra-cut

  run-≈ : ∀ {X} {m m′ : T∞ X} → m ≈ m′ → ∀ {h n d e} → Run w h m n d e → Run w h m′ n d e
  run-≈ p (run r) = run (runB-≈ (force≈ p) r)

------------------------------------------------------------------------
-- Sequencing
------------------------------------------------------------------------

-- How a run that does not return ends, before and after a continuation.
data Stops {X Y : Set} : Maybe (End X) → Maybe (End Y) → Set where
  halts : Stops (just halted) (just halted)
  cuts  : Stops nothing nothing

module Seq (w : World) {X Y : Set} (f : X → T∞ Y) where
  open World w using (answer)

  private
    snoc : ∀ (h : History) v d → (h ++ [ v ]) ++ d ≡ h ++ (v ∷ d)
    snoc h v d = ++-assoc h [ v ] d

    stopCut : ∀ {h t} {e : Maybe (End Y)} → Stops {X} nothing e → RunB w h t zero [] e
    stopCut cuts = rb-cut

  -- A run that stops stops the same way after `>>= f`.
  bind-stopB : ∀ {h t n d} {e₀ : Maybe (End X)} {e : Maybe (End Y)} → Stops e₀ e → RunB w h t n d e₀ → RunB w h (bindBlock t f) n d e
  stopA      : ∀ {h o a} {k : _ → T (X ⊎ T∞ X)} {D n d} {e₀ : Maybe (End X)} {e : Maybe (End Y)}
             → Stops e₀ e → RunA w h o a k D n d e₀ → RunA w h o a (λ r → bindBlock (k r) f) D n d e
  bind-stopB s rb-cut = stopCut s
  bind-stopB s (rb-next r) = rb-next (bind-stopB s r)
  bind-stopB s (rb-call r) = rb-call (stopA s r)
  stopA s (ra-go r) = ra-go (bind-stopB s r)
  stopA halts ra-halt = ra-halt
  stopA cuts ra-cut   = ra-cut

  -- A run that returns `x`, then a run of `f x` with the depth left.
  bind-retB : ∀ {h t n d₁ x d₂} {e : Maybe (End Y)} → RunB w h t n d₁ (just (returned x))
            → RunB w (h ++ d₁) (force (f x)) (n ∸ length d₁) d₂ e → RunB w h (bindBlock t f) n (d₁ ++ d₂) e
  retA      : ∀ {h o a} {k : _ → T (X ⊎ T∞ X)} {D n d₁ x d₂} {e : Maybe (End Y)}
            → RunA w h o a k D n d₁ (just (returned x)) → RunB w ((h ++ [ eventOf o a ]) ++ d₁) (force (f x)) (n ∸ length d₁) d₂ e
            → RunA w h o a (λ r → bindBlock (k r) f) D n (d₁ ++ d₂) e
  bind-retB {h = h} rb-ret q = subst (λ g → RunB w g _ _ _ _) (++-identityʳ h) q
  bind-retB (rb-next r) q = rb-next (bind-retB r q)
  bind-retB {h = h} (rb-call {o = o} {a} {d = d₁} r) q =
    rb-call (retA r (subst (λ g → RunB w g _ _ _ _) (sym (snoc h (eventOf o a) d₁)) q))
  retA (ra-go r) q = ra-go (bind-retB r q)

  bind-stop : ∀ {h} {m : T∞ X} {n d} {e₀ : Maybe (End X)} {e : Maybe (End Y)} → Stops e₀ e → Run w h m n d e₀ → Run w h (m >>=∞ f) n d e
  bind-stop s (run r) = run (bind-stopB s r)

  bind-ret : ∀ {h} {m : T∞ X} {n d₁ x d₂} {e : Maybe (End Y)} → Run w h m n d₁ (just (returned x))
           → Run w (h ++ d₁) (f x) (n ∸ length d₁) d₂ e → Run w h (m >>=∞ f) n (d₁ ++ d₂) e
  bind-ret (run r) (run q) = run (bind-retB r q)

  -- A run of `m >>= f`, taken apart: what `P` says of the run of `m`.
  data Split (P : History → Maybe (End X) → Set) (h : History) (n : ℕ) (d : History) (e : Maybe (End Y)) : Set where
    returns : ∀ {x d₁ d₂} → d ≡ d₁ ++ d₂ → P d₁ (just (returned x))
            → RunB w (h ++ d₁) (force (f x)) (n ∸ length d₁) d₂ e → Split P h n d e
    stops   : ∀ {e₀} → Stops e₀ e → P d e₀ → Split P h n d e

  mapSplit : ∀ {P P′ : History → Maybe (End X) → Set} {h n d e} → (∀ {d₀ e₀} → P d₀ e₀ → P′ d₀ e₀) → Split P h n d e → Split P′ h n d e
  mapSplit g (returns q p r) = returns q (g p) r
  mapSplit g (stops s p)     = stops s (g p)

  private
    cutAt : ∀ {Z h t d} {e : Maybe (End Z)} → RunB w h t zero d e → d ≡ [] × e ≡ nothing
    cutAt rb-cut = refl , refl

    atZero : ∀ {h t d e} → d ≡ [] × e ≡ nothing → Split (RunB w h t zero) h zero d e
    atZero (refl , refl) = stops cuts rb-cut

    -- One call further out: the calls and the world both start with it.
    callSplit : ∀ {h o a k n d e}
              → Split (RunA w h o a k (notEmpty? (ans o)) n) (h ++ [ eventOf o a ]) n d e
              → Split (RunB w h (roll (node (call o a k))) (suc n)) h (suc n) (eventOf o a ∷ d) e
    callSplit {h = h} {o} {a} (returns {d₁ = d₁} q p r) =
      returns (cong (eventOf o a ∷_) q) (rb-call p) (subst (λ g → RunB w g _ _ _ _) (snoc h (eventOf o a) d₁) r)
    callSplit (stops s p) = stops s (rb-call p)

  splitB : ∀ {h} (t : T (X ⊎ T∞ X)) {n d e} → RunB w h (bindBlock t f) n d e → Split (RunB w h t n) h n d e
  splitA : ∀ {h o a} (k : _ → T (X ⊎ T∞ X)) (D : Dec (NotEmpty (ans o))) {n d e}
         → RunA w h o a (λ r → bindBlock (k r) f) D n d e → Split (RunA w h o a k D n) (h ++ [ eventOf o a ]) n d e
  splitB (roll (done (inj₁ x))) {zero}  r = atZero (cutAt r)
  splitB {h} (roll (done (inj₁ x))) {suc n} r = returns refl rb-ret (subst (λ g → RunB w g _ _ _ _) (sym (++-identityʳ h)) r)
  splitB (roll (done (inj₂ m))) {zero}  r = atZero (cutAt r)
  splitB (roll (done (inj₂ m))) {suc n} (rb-next r) = mapSplit rb-next (splitB (force m) r)
  splitB (roll (node (call o a k))) {zero} r = atZero (cutAt r)
  splitB (roll (node (call o a k))) {suc n} (rb-call r) = callSplit (splitA k (notEmpty? (Op.ans o)) r)
  splitA k (yes p) (ra-go r) = mapSplit ra-go (splitB (k _) r)
  splitA k (no ¬p) ra-halt   = stops halts ra-halt
  splitA k (no ¬p) ra-cut    = stops cuts ra-cut

  split : ∀ {h} (m : T∞ X) {n d e} → Run w h (m >>=∞ f) n d e → Split (Run w h m n) h n d e
  split m (run r) = mapSplit run (splitB (force m) r)

------------------------------------------------------------------------
-- A run's end is determined
------------------------------------------------------------------------

module _ (w : World) where
  private
    detB : ∀ {X h t n d d′} {e e′ : Maybe (End X)} → RunB w h t n d e → RunB w h t n d′ e′ → e ≡ e′
    detA : ∀ {X h o a k D n d d′} {e e′ : Maybe (End X)} → RunA w h o a k D n d e → RunA w h o a k D n d′ e′ → e ≡ e′
    detB rb-cut      rb-cut       = refl
    detB rb-ret      rb-ret       = refl
    detB (rb-next r) (rb-next r′) = detB r r′
    detB (rb-call r) (rb-call r′) = detA r r′
    detA (ra-go r)   (ra-go r′)   = detB r r′
    detA ra-halt     ra-halt      = refl
    detA ra-cut      ra-cut       = refl

  run-det : ∀ {X h} {m : T∞ X} {n d d′ e e′} → Run w h m n d e → Run w h m n d′ e′ → e ≡ e′
  run-det (run r) (run r′) = detB r r′
