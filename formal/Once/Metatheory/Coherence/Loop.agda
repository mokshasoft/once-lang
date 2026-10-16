{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Loop — loops over related rounds are related.
--
-- A run of `loop c a` is a run of the round `c a`, then (if it ended with
-- the next state) a run of the loop from there. Rounds may be silent, so the
-- depth need not fall from one round to the next; the proof goes by
-- induction on the run itself. While it walks through a round it keeps what
-- the round has done so far (`Pend`): at the round's end the whole round is
-- matched with the other loop's round, which ends the same way.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.Loop (Σ : Signature) where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties using (∸-+-assoc)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Signature using (BTy; void; unit; int; float; _*_; eventOf; module Op)
open import Once.Spec.Signature as S using ()
open Op using (ans)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ using (Interp; module Interp; History; End; returned; halted; cut; Answer; resume)
open import Once.Spec.Type using (Type; _+_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (EndRel; returned≈; halted≈; cut≈; Same)
open import Once.Metatheory.Run Σ
open import Once.Metatheory.RunLaws Σ using (Stops; halts; cuts)
open import Once.Metatheory.Coherence.Relation Σ using (Sim; Related; related; fwd; bwd; Related-flip; Related-mono)

open T∞ using (force)

-- The relation on a round's end: the loop's result, or the next state.
SumR : ∀ {A B : Set} → (B → B → Set) → (A → A → Set) → B ⊎ A → B ⊎ A → Set
SumR RB RA (inj₁ b) (inj₁ b′) = RB b b′
SumR RB RA (inj₂ a) (inj₂ a′) = RA a a′
SumR RB RA (inj₁ _) (inj₂ _)  = ⊥
SumR RB RA (inj₂ _) (inj₁ _)  = ⊥

------------------------------------------------------------------------
-- A round's run, continued by the loop
------------------------------------------------------------------------

module Rounds (ι : Interp) {A B : Set} (c : A → T (B ⊎ A)) where
  open Interp ι using (answer)

  private
    snoc : ∀ (h : History) v d → (h ++ [ v ]) ++ d ≡ h ++ (v ∷ d)
    snoc h v d = ++-assoc h [ v ] d

    stopCut : ∀ {Z W : Set} {h t} {e : End W} → Stops {Z} cut e → RunB ι h t zero [] e
    stopCut cuts = rb-cut

  -- A round that ends the loop.
  retLoop : ∀ (t : T (B ⊎ A)) {h n d b} → RunB ι h (mapT inj₁ t) n d (returned (inj₁ b)) → RunB ι h (loopBlock c t) n d (returned b)
  retRes  : ∀ (β : BTy) (v : Answer β) (k : _ → T (B ⊎ A)) {h n d b}
          → RunA ι h (resume β v (λ r → mapT inj₁ (k r))) n d (returned (inj₁ b))
          → RunA ι h (resume β v (λ r → loopBlock c (k r))) n d (returned b)
  retLoop (roll (done (inj₁ b))) rb-ret = rb-ret
  retLoop (roll (done (inj₂ a))) ()
  retLoop (roll (node (call o x k))) {h} (rb-call r) = rb-call (retRes (ans o) (answer o h x) k r)
  retRes void    v k ()
  retRes unit    v k (ra-go r) = ra-go (retLoop (k v) r)
  retRes int     v k (ra-go r) = ra-go (retLoop (k v) r)
  retRes float   v k (ra-go r) = ra-go (retLoop (k v) r)
  retRes (p * q) v k (ra-go r) = ra-go (retLoop (k v) r)
  retRes (p S.+ q) v k (ra-go r) = ra-go (retLoop (k v) r)

  -- A round that stops the run.
  stopLoop : ∀ (t : T (B ⊎ A)) {h n d} {e₀ : End (B ⊎ A)} {e : End B} → Stops e₀ e
           → RunB ι h (mapT inj₁ t) n d e₀ → RunB ι h (loopBlock c t) n d e
  stopRes  : ∀ (β : BTy) (v : Answer β) (k : _ → T (B ⊎ A)) {h n d} {e₀ : End (B ⊎ A)} {e : End B} → Stops e₀ e
           → RunA ι h (resume β v (λ r → mapT inj₁ (k r))) n d e₀
           → RunA ι h (resume β v (λ r → loopBlock c (k r))) n d e
  stopLoop (roll (done x)) s rb-cut = stopCut s
  stopLoop (roll (done x)) () rb-ret
  stopLoop (roll (node (call o x k))) s rb-cut = stopCut s
  stopLoop (roll (node (call o x k))) {h} s (rb-call r) = rb-call (stopRes (ans o) (answer o h x) k s r)
  stopRes void    v k halts ra-halt = ra-halt
  stopRes unit    v k s (ra-go r) = ra-go (stopLoop (k v) s r)
  stopRes int     v k s (ra-go r) = ra-go (stopLoop (k v) s r)
  stopRes float   v k s (ra-go r) = ra-go (stopLoop (k v) s r)
  stopRes (p * q) v k s (ra-go r) = ra-go (stopLoop (k v) s r)
  stopRes (p S.+ q) v k s (ra-go r) = ra-go (stopLoop (k v) s r)

  -- A round that continues with the next state, then the loop from there.
  contLoop : ∀ (t : T (B ⊎ A)) {h n d₁ a d₂} {e : End B} → RunB ι h (mapT inj₁ t) n d₁ (returned (inj₂ a))
           → RunB ι (h ++ d₁) (loopBlock c (c a)) (n ∸ length d₁) d₂ e → RunB ι h (loopBlock c t) n (d₁ ++ d₂) e
  contRes  : ∀ (β : BTy) (v : Answer β) (k : _ → T (B ⊎ A)) {h n d₁ a d₂} {e : End B}
           → RunA ι h (resume β v (λ r → mapT inj₁ (k r))) n d₁ (returned (inj₂ a))
           → RunB ι (h ++ d₁) (loopBlock c (c a)) (n ∸ length d₁) d₂ e
           → RunA ι h (resume β v (λ r → loopBlock c (k r))) n (d₁ ++ d₂) e
  contLoop (roll (done (inj₁ b))) ()
  contLoop (roll (done (inj₂ a))) {h} rb-ret q = rb-next (subst (λ g → RunB ι g _ _ _ _) (++-identityʳ h) q)
  contLoop (roll (node (call o x k))) {h} (rb-call {d = d₁} r) q =
    rb-call (contRes (ans o) (answer o h x) k r (subst (λ g → RunB ι g _ _ _ _) (sym (snoc h (eventOf o x) d₁)) q))
  contRes void    v k () q
  contRes unit    v k (ra-go r) q = ra-go (contLoop (k v) r q)
  contRes int     v k (ra-go r) q = ra-go (contLoop (k v) r q)
  contRes float   v k (ra-go r) q = ra-go (contLoop (k v) r q)
  contRes (p * q′) v k (ra-go r) q = ra-go (contLoop (k v) r q)
  contRes (p S.+ q′) v k (ra-go r) q = ra-go (contLoop (k v) r q)

------------------------------------------------------------------------
-- Loops over related rounds
------------------------------------------------------------------------

module _ {A B : Set} (RA : A → A → Set) (RB : B → B → Set) (f f′ : A → T (B ⊎ A))
         (hf : ∀ {a a′} → RA a a′ → Sim (SumR RB RA) (embed (f a)) (embed (f′ a′))) where

  module Go (ι : Interp) where
    open Interp ι using (answer)
    open Rounds ι f′ using (retLoop; stopLoop; contLoop)

    -- What the round `t` has left to do, matched against the whole round
    -- `t′₀` it is part of, which started at `h₀`, `n₀` and has made `dpre`.
    Pend : History → T (B ⊎ A) → ℕ → History → History → T (B ⊎ A) → ℕ → Set
    Pend h₀ t′₀ n₀ dpre h t n = ∀ {d e} → RunB ι h (mapT inj₁ t) n d e
                              → ∃[ e′ ] (RunB ι h₀ (mapT inj₁ t′₀) n₀ (dpre ++ d) e′ × EndRel (SumR RB RA) e e′)

    Out : History → T (B ⊎ A) → ℕ → History → End B → Set
    Out h₀ t′₀ n₀ d e = ∃[ e′ ] (RunB ι h₀ (loopBlock f′ t′₀) n₀ d e′ × EndRel RB e e′)

    private
      at : ∀ {X : Set} {h₀ dpre h n₀ n} {t : T (X ⊎ T∞ X)} {d} {e : End X} → h₀ ++ dpre ≡ h → n₀ ∸ length dpre ≡ n → RunB ι h t n d e
         → RunB ι (h₀ ++ dpre) t (n₀ ∸ length dpre) d e
      at refl refl r = r

      noCalls : ∀ {h₀ t′₀ n₀ dpre} {e′ : End (B ⊎ A)} → RunB ι h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ → RunB ι h₀ (mapT inj₁ t′₀) n₀ dpre e′
      noCalls {dpre = dpre} r = subst (λ x → RunB ι _ _ _ x _) (++-identityʳ dpre) r

      deeper : ∀ (n₀ : ℕ) (dpre : History) v {n} → n₀ ∸ length dpre ≡ suc n → n₀ ∸ length (dpre ++ [ v ]) ≡ n
      deeper n₀ dpre v en =
        trans (cong (n₀ ∸_) (length-++ dpre)) (trans (sym (∸-+-assoc n₀ (length dpre) 1)) (cong (_∸ 1) en))

      cutCase : ∀ {h₀ t′₀ n₀ dpre} → ∃[ e′ ] (RunB ι h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ × EndRel (SumR RB RA) cut e′)
              → Out h₀ t′₀ n₀ (dpre ++ []) cut
      cutCase {t′₀ = t′₀} (_ , r′ , cut≈) = cut , stopLoop t′₀ cuts r′ , cut≈

      retCase : ∀ {h₀ t′₀ n₀ dpre b} → ∃[ e′ ] (RunB ι h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ × EndRel (SumR RB RA) (returned (inj₁ b)) e′)
              → Out h₀ t′₀ n₀ (dpre ++ []) (returned b)
      retCase {t′₀ = t′₀} (returned (inj₁ b′) , r′ , returned≈ s) = returned b′ , retLoop t′₀ r′ , returned≈ s
      retCase (returned (inj₂ _) , r′ , returned≈ ())

      haltCase : ∀ {h₀ t′₀ n₀ dpre} → ∃[ e′ ] (RunB ι h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ × EndRel (SumR RB RA) halted e′)
               → Out h₀ t′₀ n₀ (dpre ++ []) halted
      haltCase {t′₀ = t′₀} (_ , r′ , halted≈) = halted , stopLoop t′₀ halts r′ , halted≈

    -- A new round of each loop, from related states.
    start : ∀ {a a′} → RA a a′ → ∀ h n → Pend h (f′ a′) n [] h (f a) n
    start {a′ = a′} s h n q = unw (hf s ι h n (run q))
      where unw : ∀ {d e} → ∃[ e′ ] (Run ι h (embed (f′ a′)) n d e′ × EndRel (SumR RB RA) e e′)
                → ∃[ e′ ] (RunB ι h (mapT inj₁ (f′ a′)) n d e′ × EndRel (SumR RB RA) e e′)
            unw (e′ , run r′ , er) = e′ , r′ , er

    loopB   : ∀ {h₀ t′₀ n₀ dpre} (t : T (B ⊎ A)) {h n d e} → Pend h₀ t′₀ n₀ dpre h t n
            → h₀ ++ dpre ≡ h → n₀ ∸ length dpre ≡ n → RunB ι h (loopBlock f t) n d e → Out h₀ t′₀ n₀ (dpre ++ d) e
    loopRes : ∀ {h₀ t′₀ n₀ dpre} (β : BTy) (v : Answer β) (k : _ → T (B ⊎ A)) {h n d e}
            → (∀ {d e} → RunA ι h (resume β v (λ r → mapT inj₁ (k r))) n d e
                       → ∃[ e′ ] (RunB ι h₀ (mapT inj₁ t′₀) n₀ (dpre ++ d) e′ × EndRel (SumR RB RA) e e′))
            → h₀ ++ dpre ≡ h → n₀ ∸ length dpre ≡ n → RunA ι h (resume β v (λ r → loopBlock f (k r))) n d e
            → Out h₀ t′₀ n₀ (dpre ++ d) e
    nextCase : ∀ {h₀ t′₀ n₀ dpre a h n d e} → h₀ ++ dpre ≡ h → n₀ ∸ length dpre ≡ suc n
             → RunB ι h (loopBlock f (f a)) (suc n) d e
             → ∃[ e′ ] (RunB ι h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ × EndRel (SumR RB RA) (returned (inj₂ a)) e′)
             → Out h₀ t′₀ n₀ (dpre ++ d) e

    loopB (roll (done (inj₁ b))) K eh en rb-cut = cutCase (K rb-cut)
    loopB (roll (done (inj₁ b))) K eh en rb-ret = retCase (K rb-ret)
    loopB (roll (done (inj₂ a))) K eh en rb-cut = cutCase (K rb-cut)
    loopB (roll (done (inj₂ a))) K eh en (rb-next r) = nextCase eh en r (K rb-ret)
    loopB (roll (node (call o x k))) K eh en rb-cut = cutCase (K rb-cut)
    loopB {h₀} {n₀ = n₀} {dpre = dpre} (roll (node (call o x k))) {h} K eh en (rb-call {d = d} r) =
      subst (λ z → Out _ _ _ z _) (++-assoc dpre [ eventOf o x ] d)
        (loopRes (ans o) (answer o h x) k (λ q → moveCall (K (rb-call q)))
          (trans (sym (++-assoc h₀ dpre [ eventOf o x ])) (cong (_++ [ eventOf o x ]) eh)) (deeper n₀ dpre (eventOf o x) en) r)
      where moveCall : ∀ {d e} → ∃[ e′ ] (RunB ι h₀ _ _ (dpre ++ (eventOf o x ∷ d)) e′ × EndRel (SumR RB RA) e e′)
                     → ∃[ e′ ] (RunB ι h₀ _ _ ((dpre ++ [ eventOf o x ]) ++ d) e′ × EndRel (SumR RB RA) e e′)
            moveCall {d} (e′ , r′ , er) = e′ , subst (λ z → RunB ι h₀ _ _ z e′) (sym (++-assoc dpre [ eventOf o x ] d)) r′ , er

    loopRes void    v k K eh en ra-halt = haltCase (K ra-halt)
    loopRes unit    v k K eh en (ra-go r) = loopB (k v) (λ q → K (ra-go q)) eh en r
    loopRes int     v k K eh en (ra-go r) = loopB (k v) (λ q → K (ra-go q)) eh en r
    loopRes float   v k K eh en (ra-go r) = loopB (k v) (λ q → K (ra-go q)) eh en r
    loopRes (p * q) v k K eh en (ra-go r) = loopB (k v) (λ q′ → K (ra-go q′)) eh en r
    loopRes (p S.+ q) v k K eh en (ra-go r) = loopB (k v) (λ q′ → K (ra-go q′)) eh en r

    nextCase {h₀} {t′₀} {n₀} {dpre} {a} {h} {n} eh en r (returned (inj₂ a′) , r′ , returned≈ s) =
      fin (loopB (f a) (start s h (suc n)) (++-identityʳ h) refl r)
      where fin : ∀ {d e} → Out h (f′ a′) (suc n) ([] ++ d) e → Out h₀ t′₀ n₀ (dpre ++ d) e
            fin (e′ , q , er) =
              e′ , contLoop t′₀ (noCalls {h₀} {t′₀} {n₀} {dpre} r′) (at {h₀ = h₀} {dpre} {h} {n₀} {suc n} eh en q) , er
    nextCase eh en r (returned (inj₁ _) , r′ , returned≈ ())

  loopSim : ∀ {a a′} → RA a a′ → Sim RB (loop f a) (loop f′ a′)
  loopSim {a} {a′} s ι h n (run r) = fin (Go.loopB ι {t′₀ = f′ a′} {dpre = []} (f a) (Go.start ι s h n) (++-identityʳ h) refl r)
    where fin : ∀ {d e} → Go.Out ι h (f′ a′) n ([] ++ d) e → ∃[ e′ ] (Run ι h (loop f′ a′) n d e′ × EndRel RB e e′)
          fin (e′ , r′ , er) = e′ , run r′ , er

-- Both ways round.
loopRel : ∀ {A B : Set} (RA : A → A → Set) (RB : B → B → Set) (f f′ : A → T (B ⊎ A))
        → (∀ {a a′} → RA a a′ → Related (SumR RB RA) (embed (f a)) (embed (f′ a′)))
        → ∀ {a a′} → RA a a′ → Related RB (loop f a) (loop f′ a′)
loopRel RA RB f f′ hf s =
  related (loopSim RA RB f f′ (λ r → fwd (hf r)) s)
          (loopSim (flip RA) (flip RB) f′ f (λ r → fwd (Related-mono (λ {x} {y} q → turn {x} {y} q) (Related-flip (hf r)))) s)
  where
    turn : ∀ {x y} → flip (SumR RB RA) x y → SumR (flip RB) (flip RA) x y
    turn {inj₁ _} {inj₁ _} r = r
    turn {inj₂ _} {inj₂ _} r = r
    turn {inj₁ _} {inj₂ _} ()
    turn {inj₂ _} {inj₁ _} ()

-- At a type: rounds that are the same at `B + A` from states the same at `A`.
loopSame : ∀ (A B : Type) (f f′ : ⟦ A ⟧ᵛ → T (⟦ B ⟧ᵛ ⊎ ⟦ A ⟧ᵛ))
         → (∀ {a a′} → Same A a a′ → Related (Same (B + A)) (embed (f a)) (embed (f′ a′)))
         → ∀ {a a′} → Same A a a′ → Related (Same B) (loop f a) (loop f′ a′)
loopSame A B f f′ hf = loopRel (Same A) (Same B) f f′ λ s → Related-mono (λ {x} {y} q → split {x} {y} q) (hf s)
  where
    split : ∀ {x y} → Same (B + A) x y → SumR (Same B) (Same A) x y
    split {inj₁ _} {inj₁ _} r = r
    split {inj₂ _} {inj₂ _} r = r
    split {inj₁ _} {inj₂ _} ()
    split {inj₂ _} {inj₁ _} ()
