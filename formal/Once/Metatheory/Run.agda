{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Run — a finished observation, as an inductive relation.
--
-- `Run ι h m n d e`: against `ι`, in a world that has seen `h`, the
-- computation `m` observed to depth `n` makes the calls `d` and ends `e`.
-- It is exactly what `observeFrom` arrives at (`run-sound`,
-- `run-complete`), with the `Delay` steps unrolled into the derivation: a
-- block's end is a step of the derivation (`rb-next`), so a silent loop has
-- no run past depth zero. Stated inductively, runs compose by plain
-- induction: the runs of `m >>= f` are a run of `m`, then of `f` from where it
-- returned (`Once.Metatheory.Sequencing`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Run (Σ : Signature) where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Signature using (Event; eventOf; module Op)
open Op using (ans)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ
open import Once.Spec.Delay using (Delay; module Delay; _⇓_; now⇓; later⇓)

open Delay using (step)
open T∞ using (force)

module _ (ι : Interp) where
  open Interp ι using (answer)

  data RunB {X : Set} : History → T (X ⊎ T∞ X) → ℕ → History → End X → Set
  data RunA {X : Set} : History → Maybe (T (X ⊎ T∞ X)) → ℕ → History → End X → Set

  data RunB {X} where
    rb-cut  : ∀ {h t} → RunB h t zero [] cut
    rb-ret  : ∀ {h x n} → RunB h (roll (done (inj₁ x))) (suc n) [] (returned x)
    rb-next : ∀ {h m n d e} → RunB h (force m) (suc n) d e → RunB h (roll (done (inj₂ m))) (suc n) d e
    rb-call : ∀ {h o a k n d e}
            → RunA (h ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n d e
            → RunB h (roll (node (call o a k))) (suc n) (eventOf o a ∷ d) e

  data RunA {X} where
    ra-halt : ∀ {h n} → RunA h nothing n [] halted
    ra-go   : ∀ {h t n d e} → RunB h t n d e → RunA h (just t) n d e

  Run : ∀ {X} → History → T∞ X → ℕ → History → End X → Set
  Run h m n d e = RunB h (force m) n d e

  ----------------------------------------------------------------------
  -- A run is what the observation arrives at
  ----------------------------------------------------------------------

  private
    S : Set → Set
    S X = (History × End X) ⊎ Delay (History × End X)

    -- A step of a delay that arrives at `o`.
    data Arrives {X : Set} (o : History × End X) : S X → Set where
      here  : Arrives o (inj₁ o)
      later : ∀ {d} → d ⇓ o → Arrives o (inj₂ d)

    arrive : ∀ {X} {d : Delay (History × End X)} {o} → Arrives o (step d) → d ⇓ o
    arrive′ : ∀ {X} {d : Delay (History × End X)} {o} {s} → step d ≡ s → Arrives o s → d ⇓ o
    arrive {d = d} a = arrive′ {d = d} refl a
    arrive′ e here      = now⇓ e
    arrive′ e (later x) = later⇓ e x

    snoc++ : ∀ (c : History) (v : Event) d → (c ++ [ v ]) ++ d ≡ c ++ (v ∷ d)
    snoc++ c v d = ++-assoc c [ v ] d

  run-soundB : ∀ {X} {h t n d} {e : End X} → RunB h t n d e → ∀ c → Arrives (c ++ d , e) (blockObs ι h c t n)
  run-soundA : ∀ {X} {h mt n d} {e : End X} → RunA h mt n d e → ∀ c → Arrives (c ++ d , e) (answerObs ι h c mt n)
  run-soundB rb-cut c rewrite ++-identityʳ c = here
  run-soundB rb-ret c rewrite ++-identityʳ c = here
  run-soundB (rb-next r) c = later (arrive (run-soundB r c))
  run-soundB (rb-call {o = o} {a} {d = d} r) c = subst (λ x → Arrives (x , _) _) (snoc++ c (eventOf o a) d) (run-soundA r (c ++ [ eventOf o a ]))
  run-soundA ra-halt c rewrite ++-identityʳ c = here
  run-soundA (ra-go r) c = run-soundB r c

  run-sound : ∀ {X} {h} {m : T∞ X} {n d e} → Run h m n d e → ∀ c → observeFrom ι h c m n ⇓ (c ++ d , e)
  run-sound r c = arrive (run-soundB r c)

  -- What the observation arrives at is a run, and the calls it made.
  Made : ∀ {X} → History → (T∞ X) → ℕ → History → History × End X → Set
  Made h m n c o = ∃[ d ] ∃[ e ] (o ≡ (c ++ d , e) × Run h m n d e)

  private
    MadeB : ∀ {X} → History → T (X ⊎ T∞ X) → ℕ → History → History × End X → Set
    MadeB h t n c o = ∃[ d ] ∃[ e ] (o ≡ (c ++ d , e) × RunB h t n d e)

    MadeA : ∀ {X} → History → Maybe (T (X ⊎ T∞ X)) → ℕ → History → History × End X → Set
    MadeA h mt n c o = ∃[ d ] ∃[ e ] (o ≡ (c ++ d , e) × RunA h mt n d e)

    -- `c` with nothing after it.
    none : ∀ {X} (c : History) {e : End X} → (c , e) ≡ (c ++ [] , e)
    none c rewrite ++-identityʳ c = refl

  run-complete : ∀ {X} h c (m : T∞ X) n {o} → observeFrom ι h c m n ⇓ o → Made h m n c o
  private
    compB : ∀ {X} h c (t : T (X ⊎ T∞ X)) n {o} {d₀ : Delay (History × End X)}
          → step d₀ ≡ blockObs ι h c t n → d₀ ⇓ o → MadeB h t n c o
    compA : ∀ {X} h c (mt : Maybe (T (X ⊎ T∞ X))) n {o} {d₀ : Delay (History × End X)}
          → step d₀ ≡ answerObs ι h c mt n → d₀ ⇓ o → MadeA h mt n c o
    compNext : ∀ {X} h c (m : T∞ X) n {o d′} → _≡_ {A = S X} (inj₂ (observeFrom ι h c m (suc n))) (inj₂ d′) → d′ ⇓ o
             → MadeB h (roll (done (inj₂ m))) (suc n) c o
    compCall : ∀ {X} h c o a k n {out} → MadeA (h ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n (c ++ [ eventOf o a ]) out
             → MadeB {X} h (roll (node (call o a k))) (suc n) c out
    inj₁-inj : ∀ {X} {a b : History × End X} → _≡_ {A = S X} (inj₁ a) (inj₁ b) → a ≡ b
    inj₁-inj refl = refl
    clash₁ : ∀ {X} {a : History × End X} {d} {P : Set} → _≡_ {A = S X} (inj₁ a) (inj₂ d) → P
    clash₁ ()
    clash₂ : ∀ {X} {a : History × End X} {d} {P : Set} → _≡_ {A = S X} (inj₂ d) (inj₁ a) → P
    clash₂ ()

    compB h c t zero e (now⇓ e′) = [] , cut , trans (sym (inj₁-inj (trans (sym e) e′))) (none c) , rb-cut
    compB h c t zero e (later⇓ e′ _) = clash₁ (trans (sym e) e′)
    compB h c (roll (done (inj₁ x))) (suc n) e (now⇓ e′) =
      [] , returned x , trans (sym (inj₁-inj (trans (sym e) e′))) (none c) , rb-ret
    compB h c (roll (done (inj₁ x))) (suc n) e (later⇓ e′ _) = clash₁ (trans (sym e) e′)
    compB h c (roll (done (inj₂ m))) (suc n) e (now⇓ e′) = clash₂ (trans (sym e) e′)
    compB h c (roll (done (inj₂ m))) (suc n) e (later⇓ e′ d⇓) = compNext h c m n (trans (sym e) e′) d⇓
    compB h c (roll (node (call o a k))) (suc n) e d⇓ =
      compCall h c o a k n (compA (h ++ [ eventOf o a ]) (c ++ [ eventOf o a ]) (resume (ans o) (answer o h a) k) n e d⇓)
    compA h c nothing n e (now⇓ e′) = [] , halted , trans (sym (inj₁-inj (trans (sym e) e′))) (none c) , ra-halt
    compA h c nothing n e (later⇓ e′ _) = clash₁ (trans (sym e) e′)
    compA h c (just t) n e d⇓ = goA (compB h c t n e d⇓)
      where
        goA : ∀ {o} → MadeB h t n c o → MadeA h (just t) n c o
        goA (d , e″ , eq , r) = d , e″ , eq , ra-go r
    compNext h c m n refl d⇓ = goN (run-complete h c m (suc n) d⇓)
      where
        goN : ∀ {o} → Made h m (suc n) c o → MadeB h (roll (done (inj₂ m))) (suc n) c o
        goN (d , e , eq , r) = d , e , eq , rb-next r
    compCall h c o a k n (d , e , eq , r) = eventOf o a ∷ d , e , trans eq (cong (_, e) (snoc++ c (eventOf o a) d)) , rb-call r
  run-complete h c m n d⇓ = compB h c (force m) n refl d⇓
