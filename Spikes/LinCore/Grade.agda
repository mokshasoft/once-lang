-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Grade — THE GRADE MEANS WHAT THE SPEC SAYS (plan 0.146 §3).
--
-- The Spec means a derivation of grade `π` in `M π` (`Spec.Core.Meaning`,
-- D317: `M act = T`, finite blocks; `M eff = T∞`), and its loop takes a round
-- of grade `act`: `loop : (A → T (B ⊎ A)) → A → T∞ B` (`Spec.Effect`). The
-- core means every term in `T∞`; this module shows the two agree:
--
--   * a FINITE computation is one whose first block ends with a value or a
--     halt, never with a silent step (`Finite`): it is a block of `T`,
--     embedded (`toT`, `emb-toT`);
--   * ★ every term the grade judgment calls a block (`Blk`) means a finite
--     computation, at every lent value and input (`blk-finite`), when the
--     labels of grade `act` do (`EnvOK`), which every table's do (`defs-ok`);
--   * ★ so the loop means the Spec's `loop` of a round in `T` (`liter-loop`):
--     every round of a server is computed in finite time (GOAL.md).
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import LinCore.Flat using (FTy)

module LinCore.Grade
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Pass Base ⟦_⟧b Sig sdom scod using (_≈_; block≈; Bl; ≈ret; ≈call; ≈halt; iter-cong)

------------------------------------------------------------------------
-- 1. FINITE computations: the first block, with no silent step in it.
------------------------------------------------------------------------

data Fin {X : Set} : T (X ⊎ T∞ X) → Set where
  f-ret  : ∀ {x} → Fin (ret (inj₁ x))
  f-call : ∀ {s a k} → (∀ y → Fin (k y)) → Fin (call s a k)
  f-halt : ∀ {s a} → Fin (halt s a)


record Finite {X : Set} (m : T∞ X) : Set where
  constructor fin
  field unfin : Fin (block m)
open Finite public

-- the embedding of a block into `T∞` (the Spec's monad morphism `act ⊑ eff`)
embB : ∀ {X} → T X → T (X ⊎ T∞ X)
embB (ret x)      = ret (inj₁ x)
embB (call s a k) = call s a (λ y → embB (k y))
embB (halt s a)   = halt s a

emb : ∀ {X} → T X → T∞ X
block (emb b) = embB b

-- a finite computation IS a block
toT : ∀ {X} {b : T (X ⊎ T∞ X)} → Fin b → T X
toT (f-ret {x = x})       = ret x
toT (f-call {s} {a} φ)    = call s a (λ y → toT (φ y))
toT (f-halt {s} {a})      = halt s a

emb-Bl : ∀ {X} {b : T (X ⊎ T∞ X)} (φ : Fin b) → Bl (embB (toT φ)) b
emb-Bl f-ret      = ≈ret
emb-Bl (f-call φ) = ≈call (λ y → emb-Bl (φ y))
emb-Bl f-halt     = ≈halt

emb-toT : ∀ {X} {m : T∞ X} (φ : Finite m) → emb (toT (unfin φ)) ≈ m
block≈ (emb-toT φ) = emb-Bl (unfin φ)

Bl-emb : ∀ {X} {b : T (X ⊎ T∞ X)} (φ : Fin b) → Bl b (embB (toT φ))
Bl-emb f-ret      = ≈ret
Bl-emb (f-call φ) = ≈call (λ y → Bl-emb (φ y))
Bl-emb f-halt     = ≈halt

toT-emb : ∀ {X} {m : T∞ X} (φ : Finite m) → m ≈ emb (toT (unfin φ))
block≈ (toT-emb φ) = Bl-emb (unfin φ)

------------------------------------------------------------------------
-- 2. The monad keeps finite computations finite.
------------------------------------------------------------------------

fin-return : ∀ {X} {x : X} → Finite (return∞ x)
fin-return = fin f-ret

fin-bindB : ∀ {X Y} {b : T (X ⊎ T∞ X)} {k : X → T∞ Y} → Fin b → (∀ x → Finite (k x)) → Fin (bindBlock b k)
fin-bindB (f-ret {x = x}) fk = unfin (fk x)
fin-bindB (f-call φ)      fk = f-call (λ y → fin-bindB (φ y) fk)
fin-bindB f-halt          fk = f-halt

fin-bind : ∀ {X Y} {m : T∞ X} {k : X → T∞ Y} → Finite m → (∀ x → Finite (k x)) → Finite (m >>=∞ k)
fin-bind (fin φ) fk = fin (fin-bindB φ fk)

fin-fmap : ∀ {X Y} {m : T∞ X} (f : X → Y) → Finite m → Finite (fmap∞ f m)
fin-fmap f φ = fin-bind φ (λ _ → fin f-ret)

------------------------------------------------------------------------
-- 3. ★ A BLOCK MEANS A FINITE COMPUTATION.
------------------------------------------------------------------------

-- the labels of grade `act` mean finite computations
EnvOK : ∀ {Γ} → Env Γ → Set
EnvOK {Γ} ρ = ∀ {l k X A B} (p : Γ ∋[ l ] sg k act X A B) x a → Finite (lookup ρ p x a)

module _ {Γ : Cx} (ρ : Env Γ) (ok : EnvOK ρ) where
  mutual
    blk-finite : ∀ {E A B} {t : Tm Γ E A B} → Blk t → ∀ e x → Finite (Lᶜ ρ t e x)
    blk-finite k-id                 e x              = fin f-ret
    blk-finite (k-∘ φ ψ)            e x              = fin-bind (blk-finite ψ e x) (blk-finite φ e)
    blk-finite (k-⊗ φ ψ)            e (a , b)        = fin-bind (blk-finite φ e a) (λ a′ → fin-fmap (a′ ,_) (blk-finite ψ e b))
    blk-finite k-ρ                  e (a , tt)       = fin f-ret
    blk-finite k-ρ⁻                 e x              = fin f-ret
    blk-finite k-lul                e (tt , a)       = fin f-ret
    blk-finite k-lul⁻               e x              = fin f-ret
    blk-finite k-assoc              e ((a , b) , c)  = fin f-ret
    blk-finite k-assoc⁻             e (a , (b , c))  = fin f-ret
    blk-finite k-swap               e (a , b)        = fin f-ret
    blk-finite k-dup                e x              = fin f-ret
    blk-finite k-drop               e x              = fin f-ret
    blk-finite k-inl                e x              = fin f-ret
    blk-finite k-inr                e x              = fin f-ret
    blk-finite (k-case φ ψ)         e (inj₁ a)       = blk-finite φ e a
    blk-finite (k-case φ ψ)         e (inj₂ b)       = blk-finite ψ e b
    blk-finite k-zero               e ()
    blk-finite k-in                 e x              = fin f-ret
    blk-finite k-out                e x              = fin f-ret
    blk-finite (k-cata {F} φ)       e x              = cata-finite F (λ y → blk-finite φ e (coh⁻¹ F _ y)) x
    blk-finite k-clo                e x              = fin f-ret
    blk-finite (k-app {p = p})      e (x , a)        = ok p x a
    blk-finite (k-lend φ)           e (x , a)        = fin-fmap (x ,_) (blk-finite φ (e , x) a)
    blk-finite (k-lift φ)           e a              = blk-finite φ tt a
    blk-finite (k-fst φ)            (e₁ , e₂) a      = blk-finite φ e₁ a
    blk-finite (k-snd φ)            (e₁ , e₂) a      = blk-finite φ e₂ a
    blk-finite (k-caseE φ ψ)        (inj₁ e) a       = blk-finite φ e a
    blk-finite (k-caseE φ ψ)        (inj₂ e) a       = blk-finite ψ e a
    blk-finite (k-bout {F} φ)       e a              = blk-finite φ (coh⁻¹ F (μt F) (outμ e)) a
    blk-finite k-copy               e a              = fin f-ret
    blk-finite (k-bapp {p = p})     x a              = ok p x a
    blk-finite k-const              e x              = fin f-ret
    blk-finite k-op                 e x              = fin (f-call (λ y → f-ret))
    blk-finite k-halt               e x              = fin f-halt

    -- the fold of a finite algebra is finite: it descends a finite tree
    cata-finite : ∀ F {X : Set} {alg : FS F X → T∞ X} → (∀ y → Finite (alg y)) → ∀ x → Finite (cataC ρ F alg x)
    cata-finite F fa (inμ w) = fin-bind (trav-finite F F fa w) fa

    trav-finite : ∀ F G {X : Set} {alg : FS F X → T∞ X} → (∀ y → Finite (alg y))
                → ∀ y → Finite (travC ρ F G alg y)
    trav-finite F Idf      fa y        = cata-finite F fa y
    trav-finite F Kone     fa y        = fin f-ret
    trav-finite F Kzero    fa ()
    trav-finite F (Kb _)   fa y        = fin f-ret
    trav-finite F (Kμ _)   fa y        = fin f-ret
    trav-finite F (G ⊕f H) fa (inj₁ y) = fin-fmap inj₁ (trav-finite F G fa y)
    trav-finite F (G ⊕f H) fa (inj₂ z) = fin-fmap inj₂ (trav-finite F H fa z)
    trav-finite F (G ⊗f H) fa (y , z)  =
      fin-bind (trav-finite F G fa y) (λ u → fin-fmap (u ,_) (trav-finite F H fa z))

-- ★ every table's labels of grade `act` mean finite computations: their
-- bodies are blocks (`Body` holds the grade judgment), over the labels before
defs-ok : ∀ {Γ} (ds : Defs Γ) → EnvOK ⟦ ds ⟧D
defs-ok (ds ▸ b1 b β) here      x a = blk-finite ⟦ ds ⟧D (defs-ok ds) β tt (x , a)
defs-ok (ds ▸ bω b β) here      x a = blk-finite ⟦ ds ⟧D (defs-ok ds) β x a
defs-ok (ds ▸ _)      (there p) x a = defs-ok ds p x a

------------------------------------------------------------------------
-- 4. ★ THE LOOP IS THE SPEC'S: the unfold of a round in `T`.
------------------------------------------------------------------------

-- `Spec.Effect.loop`, over the core's `T∞`: each round runs the block `c a`;
-- where it ends with a `B` the loop returns it, with the next state it goes on
loop : ∀ {A B : Set} → (A → T (B ⊎ A)) → A → T∞ B
loop c = iter∞ (λ a → emb (c a))

-- the round of `liter f φ`, as a block of `T`
round : ∀ {Γ E A B} (ds : Defs Γ) {f : Tm Γ E A (B ⊕t A)} → Blk f → ⟦ E ⟧ → ⟦ A ⟧ → T ⟦ B ⊕t A ⟧
round ds φ e a = toT (unfin (blk-finite ⟦ ds ⟧D (defs-ok ds) φ e a))

-- ★ a loop of the core means the Spec's loop of its round
liter-loop : ∀ {Γ E A B} (ds : Defs Γ) {f : Tm Γ E A (B ⊕t A)} (φ : Blk f) e a
           → Lᶜ ⟦ ds ⟧D (liter f φ) e a ≈ loop (round ds φ e) a
liter-loop ds φ e a = iter-cong (λ a′ → toT-emb (rd a′)) (toT-emb (rd a))
  where rd = blk-finite ⟦ ds ⟧D (defs-ok ds) φ e
