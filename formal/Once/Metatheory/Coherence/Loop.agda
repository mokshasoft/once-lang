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
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Signature using (eventOf; Op; module Op; arg; ⟦_⟧ᵇ; NotEmpty; notEmpty?)
open Op using (ans)
open import Once.Spec.Polynomial using (SK; SId; _S⊕_)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ using (World; module World; History; End; returned; halted; EndRel; returned≈; halted≈)
open import Once.Spec.Type using (Type; _+_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Metatheory.Trace Σ using (MaybeEnd; cut≈; end≈)
open import Once.Metatheory.Run Σ
open import Once.Metatheory.RunLaws Σ using (Stops; halts; cuts)
open import Once.Metatheory.Coherence.Relation Σ using (Sim; Related; related; fwd; bwd; Related-flip; Related-mono)

-- The loop's block for a round's block: the stream unfold's, at `K B ⊕ Id`.
loopBlock : ∀ {A B : Set} → (A → T (B ⊎ A)) → T (B ⊎ A) → T (B ⊎ T∞ B)
loopBlock {B = B} c t = treeA (SK B S⊕ SId) c t

-- The relation on a round's end: the loop's result, or the next state.
SumR : ∀ {A B : Set} → (B → B → Set) → (A → A → Set) → B ⊎ A → B ⊎ A → Set
SumR RB RA (inj₁ b) (inj₁ b′) = RB b b′
SumR RB RA (inj₂ a) (inj₂ a′) = RA a a′
SumR RB RA (inj₁ _) (inj₂ _)  = ⊥
SumR RB RA (inj₂ _) (inj₁ _)  = ⊥

------------------------------------------------------------------------
-- A round's run, continued by the loop
------------------------------------------------------------------------

module Rounds (w : World) {A B : Set} (c : A → T (B ⊎ A)) where
  open World w using (answer)

  private
    snoc : ∀ (h : History) v d → (h ++ [ v ]) ++ d ≡ h ++ (v ∷ d)
    snoc h v d = ++-assoc h [ v ] d

    stopCut : ∀ {Z W : Set} {h t} {e : Maybe (End W)} → Stops {Z} nothing e → RunB w h t zero [] e
    stopCut cuts = rb-cut

  -- A round that ends the loop.
  retLoop : ∀ (t : T (B ⊎ A)) {h n d b} → RunB w h (mapT inj₁ t) n d (just (returned (inj₁ b)))
          → RunB w h (loopBlock c t) n d (just (returned b))
  retA    : ∀ {h o a} (k : ⟦ ans o ⟧ᵇ → T (B ⊎ A)) {D n d b}
          → RunA w h o a (λ r → mapT inj₁ (k r)) D n d (just (returned (inj₁ b)))
          → RunA w h o a (λ r → loopBlock c (k r)) D n d (just (returned b))
  retLoop (roll (done (inj₁ b))) rb-ret = rb-ret
  retLoop (roll (done (inj₂ a))) ()
  retLoop (roll (node (call o x k))) (rb-call r) = rb-call (retA k r)
  retA k (ra-go r) = ra-go (retLoop (k _) r)

  -- A round that stops the run.
  stopLoop : ∀ (t : T (B ⊎ A)) {h n d} {e₀ : Maybe (End (B ⊎ A))} {e : Maybe (End B)} → Stops e₀ e
           → RunB w h (mapT inj₁ t) n d e₀ → RunB w h (loopBlock c t) n d e
  stopA    : ∀ {h o a} (k : ⟦ ans o ⟧ᵇ → T (B ⊎ A)) {D n d} {e₀ : Maybe (End (B ⊎ A))} {e : Maybe (End B)} → Stops e₀ e
           → RunA w h o a (λ r → mapT inj₁ (k r)) D n d e₀ → RunA w h o a (λ r → loopBlock c (k r)) D n d e
  stopLoop (roll (done x)) s rb-cut = stopCut s
  stopLoop (roll (done x)) () rb-ret
  stopLoop (roll (node (call o x k))) s rb-cut = stopCut s
  stopLoop (roll (node (call o x k))) s (rb-call r) = rb-call (stopA k s r)
  stopA k s (ra-go r) = ra-go (stopLoop (k _) s r)
  stopA k halts ra-halt = ra-halt
  stopA k cuts ra-cut   = ra-cut

  -- A round that continues with the next state, then the loop from there.
  contLoop : ∀ (t : T (B ⊎ A)) {h n d₁ a d₂} {e : Maybe (End B)} → RunB w h (mapT inj₁ t) n d₁ (just (returned (inj₂ a)))
           → RunB w (h ++ d₁) (loopBlock c (c a)) (n ∸ length d₁) d₂ e → RunB w h (loopBlock c t) n (d₁ ++ d₂) e
  contA    : ∀ {h o a} (k : ⟦ ans o ⟧ᵇ → T (B ⊎ A)) {D n d₁ a′ d₂} {e : Maybe (End B)}
           → RunA w h o a (λ r → mapT inj₁ (k r)) D n d₁ (just (returned (inj₂ a′)))
           → RunB w ((h ++ [ eventOf o a ]) ++ d₁) (loopBlock c (c a′)) (n ∸ length d₁) d₂ e
           → RunA w h o a (λ r → loopBlock c (k r)) D n (d₁ ++ d₂) e
  contLoop (roll (done (inj₁ b))) ()
  contLoop (roll (done (inj₂ a))) {h} rb-ret q = rb-next (subst (λ g → RunB w g _ _ _ _) (++-identityʳ h) q)
  contLoop (roll (node (call o x k))) {h} (rb-call {d = d₁} r) q =
    rb-call (contA k r (subst (λ g → RunB w g _ _ _ _) (sym (snoc h (eventOf o x) d₁)) q))
  contA k (ra-go r) q = ra-go (contLoop (k _) r q)

------------------------------------------------------------------------
-- Loops over related rounds
------------------------------------------------------------------------

module _ {A B : Set} (RA : A → A → Set) (RB : B → B → Set) (f f′ : A → T (B ⊎ A))
         (hf : ∀ {a a′} → RA a a′ → Sim (SumR RB RA) (embed (f a)) (embed (f′ a′))) where

  module Go (w : World) where
    open World w using (answer)
    open Rounds w f′ using (retLoop; stopLoop; contLoop)

    -- What the round `t` has left to do, matched against the whole round
    -- `t′₀` it is part of, which started at `h₀`, `n₀` and has made `dpre`.
    Pend : History → T (B ⊎ A) → ℕ → History → History → T (B ⊎ A) → ℕ → Set
    Pend h₀ t′₀ n₀ dpre h t n = ∀ {d e} → RunB w h (mapT inj₁ t) n d e
                              → ∃[ e′ ] (RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ d) e′ × MaybeEnd (SumR RB RA) e e′)

    Out : History → T (B ⊎ A) → ℕ → History → Maybe (End B) → Set
    Out h₀ t′₀ n₀ d e = ∃[ e′ ] (RunB w h₀ (loopBlock f′ t′₀) n₀ d e′ × MaybeEnd RB e e′)

    private
      at : ∀ {X : Set} {h₀ dpre h n₀ n} {t : T (X ⊎ T∞ X)} {d} {e : Maybe (End X)} → h₀ ++ dpre ≡ h → n₀ ∸ length dpre ≡ n → RunB w h t n d e
         → RunB w (h₀ ++ dpre) t (n₀ ∸ length dpre) d e
      at refl refl r = r

      noCalls : ∀ {h₀ t′₀ n₀ dpre} {e′ : Maybe (End (B ⊎ A))} → RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ → RunB w h₀ (mapT inj₁ t′₀) n₀ dpre e′
      noCalls {dpre = dpre} r = subst (λ x → RunB w _ _ _ x _) (++-identityʳ dpre) r

      deeper : ∀ (n₀ : ℕ) (dpre : History) v {n} → n₀ ∸ length dpre ≡ suc n → n₀ ∸ length (dpre ++ [ v ]) ≡ n
      deeper n₀ dpre v en =
        trans (cong (n₀ ∸_) (length-++ dpre)) (trans (sym (∸-+-assoc n₀ (length dpre) 1)) (cong (_∸ 1) en))

      cutCase : ∀ {h₀ t′₀ n₀ dpre} → ∃[ e′ ] (RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ × MaybeEnd (SumR RB RA) nothing e′)
              → Out h₀ t′₀ n₀ (dpre ++ []) nothing
      cutCase {t′₀ = t′₀} (_ , r′ , cut≈) = nothing , stopLoop t′₀ cuts r′ , cut≈

      retCase : ∀ {h₀ t′₀ n₀ dpre b} → ∃[ e′ ] (RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ × MaybeEnd (SumR RB RA) (just (returned (inj₁ b))) e′)
              → Out h₀ t′₀ n₀ (dpre ++ []) (just (returned b))
      retCase {t′₀ = t′₀} (just (returned (inj₁ b′)) , r′ , end≈ (returned≈ s)) = just (returned b′) , retLoop t′₀ r′ , end≈ (returned≈ s)
      retCase (just (returned (inj₂ _)) , r′ , end≈ (returned≈ ()))

      haltCase : ∀ {h₀ t′₀ n₀ dpre d} → ∃[ e′ ] (RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ d) e′ × MaybeEnd (SumR RB RA) (just halted) e′)
               → Out h₀ t′₀ n₀ (dpre ++ d) (just halted)
      haltCase {t′₀ = t′₀} (_ , r′ , end≈ halted≈) = just halted , stopLoop t′₀ halts r′ , end≈ halted≈

      cutCaseD : ∀ {h₀ t′₀ n₀ dpre d} → ∃[ e′ ] (RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ d) e′ × MaybeEnd (SumR RB RA) nothing e′)
               → Out h₀ t′₀ n₀ (dpre ++ d) nothing
      cutCaseD {t′₀ = t′₀} (_ , r′ , cut≈) = nothing , stopLoop t′₀ cuts r′ , cut≈

    -- A new round of each loop, from related states.
    start : ∀ {a a′} → RA a a′ → ∀ h n → Pend h (f′ a′) n [] h (f a) n
    start {a′ = a′} s h n q = unw (hf s w h n (run q))
      where unw : ∀ {d e} → ∃[ e′ ] (Run w h (embed (f′ a′)) n d e′ × MaybeEnd (SumR RB RA) e e′)
                → ∃[ e′ ] (RunB w h (mapT inj₁ (f′ a′)) n d e′ × MaybeEnd (SumR RB RA) e e′)
            unw (e′ , run r′ , er) = e′ , r′ , er

    loopB   : ∀ {h₀ t′₀ n₀ dpre} (t : T (B ⊎ A)) {h n d e} → Pend h₀ t′₀ n₀ dpre h t n
            → h₀ ++ dpre ≡ h → n₀ ∸ length dpre ≡ n → RunB w h (loopBlock f t) n d e → Out h₀ t′₀ n₀ (dpre ++ d) e
    loopA   : ∀ {h₀ t′₀ n₀ dpre} {h o a} (k : ⟦ ans o ⟧ᵇ → T (B ⊎ A)) {D n d e}
            → (∀ {d e} → RunA w h o a (λ r → mapT inj₁ (k r)) D n d e
                       → ∃[ e′ ] (RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ d) e′ × MaybeEnd (SumR RB RA) e e′))
            → h₀ ++ dpre ≡ h ++ [ eventOf o a ] → n₀ ∸ length dpre ≡ n → RunA w h o a (λ r → loopBlock f (k r)) D n d e
            → Out h₀ t′₀ n₀ (dpre ++ d) e
    nextCase : ∀ {h₀ t′₀ n₀ dpre a h n d e} → h₀ ++ dpre ≡ h → n₀ ∸ length dpre ≡ suc n
             → RunB w h (loopBlock f (f a)) (suc n) d e
             → ∃[ e′ ] (RunB w h₀ (mapT inj₁ t′₀) n₀ (dpre ++ []) e′ × MaybeEnd (SumR RB RA) (just (returned (inj₂ a))) e′)
             → Out h₀ t′₀ n₀ (dpre ++ d) e

    loopB (roll (done (inj₁ b))) K eh en rb-cut = cutCase (K rb-cut)
    loopB (roll (done (inj₁ b))) K eh en rb-ret = retCase (K rb-ret)
    loopB (roll (done (inj₂ a))) K eh en rb-cut = cutCase (K rb-cut)
    loopB (roll (done (inj₂ a))) K eh en (rb-next r) = nextCase eh en r (K rb-ret)
    loopB (roll (node (call o x k))) K eh en rb-cut = cutCase (K rb-cut)
    loopB {h₀} {n₀ = n₀} {dpre = dpre} (roll (node (call o x k))) {h} K eh en (rb-call {d = d} r) =
      subst (λ z → Out _ _ _ z _) (++-assoc dpre [ eventOf o x ] d)
        (loopA k (λ q → moveCall (K (rb-call q)))
          (trans (sym (++-assoc h₀ dpre [ eventOf o x ])) (cong (_++ [ eventOf o x ]) eh)) (deeper n₀ dpre (eventOf o x) en) r)
      where moveCall : ∀ {d e} → ∃[ e′ ] (RunB w h₀ _ _ (dpre ++ (eventOf o x ∷ d)) e′ × MaybeEnd (SumR RB RA) e e′)
                     → ∃[ e′ ] (RunB w h₀ _ _ ((dpre ++ [ eventOf o x ]) ++ d) e′ × MaybeEnd (SumR RB RA) e e′)
            moveCall {d} (e′ , r′ , er) = e′ , subst (λ z → RunB w h₀ _ _ z e′) (sym (++-assoc dpre [ eventOf o x ] d)) r′ , er

    loopA k K eh en (ra-go r) = loopB (k _) (λ q → K (ra-go q)) eh en r
    loopA {dpre = dpre} k K eh en ra-halt = haltCase {dpre = dpre} {d = []} (K ra-halt)
    loopA {dpre = dpre} k K eh en ra-cut  = cutCaseD {dpre = dpre} {d = []} (K ra-cut)

    nextCase {h₀} {t′₀} {n₀} {dpre} {a} {h} {n} eh en r (just (returned (inj₂ a′)) , r′ , end≈ (returned≈ s)) =
      fin (loopB (f a) (start s h (suc n)) (++-identityʳ h) refl r)
      where fin : ∀ {d e} → Out h (f′ a′) (suc n) ([] ++ d) e → Out h₀ t′₀ n₀ (dpre ++ d) e
            fin (e′ , q , er) =
              e′ , contLoop t′₀ (noCalls {h₀} {t′₀} {n₀} {dpre} r′) (at {h₀ = h₀} {dpre} {h} {n₀} {suc n} eh en q) , er
    nextCase eh en r (just (returned (inj₁ _)) , r′ , end≈ (returned≈ ()))

  loopSim : ∀ {a a′} → RA a a′ → Sim RB (loop f a) (loop f′ a′)
  loopSim {a} {a′} s w h n (run r) = fin (Go.loopB w {t′₀ = f′ a′} {dpre = []} (f a) (Go.start w s h n) (++-identityʳ h) refl r)
    where fin : ∀ {d e} → Go.Out w h (f′ a′) n ([] ++ d) e → ∃[ e′ ] (Run w h (loop f′ a′) n d e′ × MaybeEnd RB e e′)
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
