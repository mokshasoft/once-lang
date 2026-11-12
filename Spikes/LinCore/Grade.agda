-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Grade — THE GRADE MEANS WHAT THE SPEC SAYS (plan 0.146 §3).
--
-- The Spec means a derivation of grade `π` in `M π` (`Spec.Core.Meaning`,
-- D317: `M act = T`, finite blocks; `M eff = T∞`), and its loop takes a round
-- of grade `act`: `loop : (A → T (B ⊎ A)) → A → T∞ B` (`Spec.Effect`). The
-- core means a block both ways: `Lᶜ`, in `T∞`, and `Lᴮ`, by induction on the
-- grade judgment, in `T` (as an arrow of grade `act` means, `⟦ Fn k act A B ⟧`).
-- This module shows the two agree:
--
--   * ★ every block's computation IS its block, embedded (`blk-coh`:
--     `Lᶜ t ≈ emb (Lᴮ φ)`), at every table, lent value and input;
--   * so a block means a finite computation (`blk-finite`);
--   * ★ and the loop means the Spec's `loop` of its round's block
--     (`liter-loop`): every round of a server is computed in finite time
--     (GOAL.md).
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; cong; cong₂; subst)
open import Agda.Builtin.Sigma using (fst; snd)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import LinCore.Flat using (FTy)

module LinCore.Grade
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Bisim Base ⟦_⟧b Sig sdom scod
  using (_≈_; block≈; Bl; ≈ret; ≈call; ≈halt; ≈-refl; ≈-trans; ≈-blk; Bl-refl; >>=-cong; iter-cong)

------------------------------------------------------------------------
-- 1. The embedding `T → T∞` is a monad morphism, up to bisimilarity.
------------------------------------------------------------------------

-- two computations with the same first block
same : ∀ {X} {m m′ : T∞ X} → block m ≡ block m′ → m ≈ m′
same e = ≈-blk e ≈-refl

ret≈ : ∀ {X} {x : X} → return∞ x ≈ emb (ret x)
ret≈ = same refl

emb-bindB : ∀ {X Y} (m : T X) (k : X → T Y)
          → Bl (bindBlock (embB m) (λ x → emb (k x))) (embB (bindT m k))
emb-bindB (ret x)      k = Bl-refl (embB (k x))
emb-bindB (call s a c) k = ≈call (λ y → emb-bindB (c y) k)
emb-bindB (halt s a)   k = ≈halt

emb-bind : ∀ {X Y} (m : T X) (k : X → T Y) → (emb m >>=∞ λ x → emb (k x)) ≈ emb (bindT m k)
block≈ (emb-bind m k) = emb-bindB m k

bind≈ : ∀ {X Y} {m : T∞ X} {a : T X} {k : X → T∞ Y} {c : X → T Y}
      → m ≈ emb a → (∀ x → k x ≈ emb (c x)) → (m >>=∞ k) ≈ emb (bindT a c)
bind≈ {a = a} {c = c} p q = ≈-trans (>>=-cong p q) (emb-bind a c)

fmap≈ : ∀ {X Y} {m : T∞ X} {a : T X} (f : X → Y) → m ≈ emb a → fmap∞ f m ≈ emb (fmapT f a)
fmap≈ f p = bind≈ p (λ _ → ret≈)

------------------------------------------------------------------------
-- 2. ★ A BLOCK'S COMPUTATION IS ITS BLOCK.
------------------------------------------------------------------------

module _ {Γ : Cx} (ρ : Env Γ) where
  mutual
    blk-coh : ∀ {E A B} {t : Tm Γ E A B} (φ : Blk t) e x → Lᶜ ρ t e x ≈ emb (Lᴮ ρ φ e x)
    blk-coh k-id            e x             = ret≈
    blk-coh (k-∘ φ ψ)       e x             = bind≈ (blk-coh ψ e x) (blk-coh φ e)
    blk-coh (k-⊗ φ ψ)       e (a , b)       = bind≈ (blk-coh φ e a) (λ a′ → fmap≈ (a′ ,_) (blk-coh ψ e b))
    blk-coh k-ρ             e (a , tt)      = ret≈
    blk-coh k-ρ⁻            e x             = ret≈
    blk-coh k-lul           e (tt , a)      = ret≈
    blk-coh k-lul⁻          e x             = ret≈
    blk-coh k-assoc         e ((a , b) , c) = ret≈
    blk-coh k-assoc⁻        e (a , (b , c)) = ret≈
    blk-coh k-swap          e (a , b)       = ret≈
    blk-coh k-dup           e x             = ret≈
    blk-coh k-drop          e x             = ret≈
    blk-coh k-inl           e x             = ret≈
    blk-coh k-inr           e x             = ret≈
    blk-coh (k-case φ ψ)    e (inj₁ a)      = blk-coh φ e a
    blk-coh (k-case φ ψ)    e (inj₂ b)      = blk-coh ψ e b
    blk-coh k-zero          e ()
    blk-coh k-in            e x             = ret≈
    blk-coh k-out           e x             = ret≈
    blk-coh (k-cata {F} φ)  e x             = cata-coh F (λ y → blk-coh φ e (coh⁻¹ F _ y)) x
    blk-coh k-clo           e x             = ret≈
    blk-coh k-app           e (x , a)       = ≈-refl
    blk-coh (k-lend φ)      e (x , a)       = fmap≈ (x ,_) (blk-coh φ (e , x) a)
    blk-coh (k-lift φ)      e a             = blk-coh φ tt a
    blk-coh (k-fst φ)       (e₁ , e₂) a     = blk-coh φ e₁ a
    blk-coh (k-snd φ)       (e₁ , e₂) a     = blk-coh φ e₂ a
    blk-coh (k-caseE φ ψ)   (inj₁ e) a      = blk-coh φ e a
    blk-coh (k-caseE φ ψ)   (inj₂ e) a      = blk-coh ψ e a
    blk-coh (k-bout {F} φ)  e a             = blk-coh φ (coh⁻¹ F (μt F) (outμ e)) a
    blk-coh k-copy          e a             = ret≈
    blk-coh k-bapp          x a             = ≈-refl
    blk-coh k-lam           e x             = ret≈
    blk-coh k-lamω          e x             = ret≈
    blk-coh k-ev            e (f , a)       = ≈-refl
    blk-coh k-bev           f a             = ≈-refl
    blk-coh k-const         e x             = ret≈
    blk-coh k-unf           e x             = ret≈
    blk-coh k-nout          e v             = ≈-refl
    blk-coh k-op            e x             = same refl
    blk-coh k-halt          e x             = same refl

    -- the fold of a block algebra is the block fold
    cata-coh : ∀ F {X : Set} {alg : FS F X → T∞ X} {algB : FS F X → T X}
             → (∀ y → alg y ≈ emb (algB y)) → ∀ x → cataC ρ F alg x ≈ emb (cataB ρ F algB x)
    cata-coh F fa (inμ w) = bind≈ (trav-coh F F fa w) fa

    trav-coh : ∀ F G {X : Set} {alg : FS F X → T∞ X} {algB : FS F X → T X}
             → (∀ y → alg y ≈ emb (algB y)) → ∀ y → travC ρ F G alg y ≈ emb (travB ρ F G algB y)
    trav-coh F Idf      fa y        = cata-coh F fa y
    trav-coh F Kone     fa y        = ret≈
    trav-coh F Kzero    fa ()
    trav-coh F (Kb _)   fa y        = ret≈
    trav-coh F (Kμ _)   fa y        = ret≈
    trav-coh F (G ⊕f H) fa (inj₁ y) = fmap≈ inj₁ (trav-coh F G fa y)
    trav-coh F (G ⊕f H) fa (inj₂ z) = fmap≈ inj₂ (trav-coh F H fa z)
    trav-coh F (G ⊗f H) fa (y , z)  = bind≈ (trav-coh F G fa y) (λ u → fmap≈ (u ,_) (trav-coh F H fa z))

------------------------------------------------------------------------
-- 3. So a block means a FINITE computation: the first block, with no silent
-- step in it.
------------------------------------------------------------------------

data Fin {X : Set} : T (X ⊎ T∞ X) → Set where
  f-ret  : ∀ {x} → Fin (ret (inj₁ x))
  f-call : ∀ {s a k} → (∀ y → Fin (k y)) → Fin (call s a k)
  f-halt : ∀ {s a} → Fin (halt s a)

record Finite {X : Set} (m : T∞ X) : Set where
  constructor fin
  field unfin : Fin (block m)
open Finite public

fin-embB : ∀ {X} (b : T X) → Fin (embB b)
fin-embB (ret x)      = f-ret
fin-embB (call s a k) = f-call (λ y → fin-embB (k y))
fin-embB (halt s a)   = f-halt

Fin-Bl : ∀ {X} {b b′ : T (X ⊎ T∞ X)} → Bl b b′ → Fin b′ → Fin b
Fin-Bl ≈ret      f-ret      = f-ret
Fin-Bl (≈call f) (f-call φ) = f-call (λ y → Fin-Bl (f y) (φ y))
Fin-Bl ≈halt     f-halt     = f-halt

blk-finite : ∀ {Γ} (ρ : Env Γ) {E A B} {t : Tm Γ E A B} → Blk t → ∀ e x → Finite (Lᶜ ρ t e x)
blk-finite ρ φ e x = fin (Fin-Bl (block≈ (blk-coh ρ φ e x)) (fin-embB (Lᴮ ρ φ e x)))

------------------------------------------------------------------------
-- 4. ★ THE LOOP IS THE SPEC'S: the unfold of a round in `T`.
------------------------------------------------------------------------

-- `Spec.Effect.loop`, over the core's `T∞`: each round runs the block `c a`;
-- where it ends with a `B` the loop returns it, with the next state it goes on
loop : ∀ {A B : Set} → (A → T (B ⊎ A)) → A → T∞ B
loop c = iter∞ (λ a → emb (c a))

-- ★ a loop of the core means the Spec's loop of its round's block
liter-loop : ∀ {Γ} (ρ : Env Γ) {E A B} {f : Tm Γ E A (B ⊕t A)} (φ : Blk f) e a
           → Lᶜ ρ (liter f φ) e a ≈ loop (Lᴮ ρ φ e) a
liter-loop ρ φ e a = iter-cong (blk-coh ρ φ e) (blk-coh ρ φ e a)

------------------------------------------------------------------------
-- 5. ★ OBSERVING A ν IS RUNNING `obsT` on its coalgebra and seed: the
-- core's own generators mean the Spec's observation (`outν` of an `anaA`).
------------------------------------------------------------------------

mk≈ : ∀ {X} {m m′ : T∞ X} → Bl (block m) (block m′) → m ≈ m′
block≈ (mk≈ b) = b

module _ {Γ : Cx} (ρ : Env Γ) (F : LF) (S : LTy) where
  private
    C = Coalg F S

  -- what `strL` and `mapNu` do to a layer's values
  strM : ∀ G → ⟦ C ⟧ → ⟦ LF∙ G S ⟧ → ⟦ LF∙ G (C ⊗t S) ⟧
  strM Idf      c s        = (c , s)
  strM Kone     c x        = x
  strM Kzero    c ()
  strM (Kb b)   c x        = x
  strM (Kμ G)   c x        = x
  strM (G ⊕f H) c (inj₁ x) = inj₁ (strM G c x)
  strM (G ⊕f H) c (inj₂ y) = inj₂ (strM H c y)
  strM (G ⊗f H) c (x , y)  = (strM G c x , strM H c y)

  mapM : ∀ G → ⟦ LF∙ G (C ⊗t S) ⟧ → ⟦ LF∙ G (Nu F) ⟧
  mapM Idf      cs       = anaN F (cohc F S (fst cs)) (snd cs)
  mapM Kone     x        = x
  mapM Kzero    ()
  mapM (Kb b)   x        = x
  mapM (Kμ G)   x        = x
  mapM (G ⊕f H) (inj₁ x) = inj₁ (mapM G x)
  mapM (G ⊕f H) (inj₂ y) = inj₂ (mapM H y)
  mapM (G ⊗f H) (x , y)  = (mapM G x , mapM H y)

  str-coh : ∀ G (c : ⟦ C ⟧) w → Lᶜ ρ (strL F G S) (tt , c) w ≈ emb (ret (strM G c w))
  str-coh Idf      c s        = same refl
  str-coh Kone     c x        = ret≈
  str-coh Kzero    c ()
  str-coh (Kb b)   c x        = ret≈
  str-coh (Kμ G)   c x        = ret≈
  str-coh (G ⊕f H) c (inj₁ x) = bind≈ (str-coh G c x) (λ _ → ret≈)
  str-coh (G ⊕f H) c (inj₂ y) = bind≈ (str-coh H c y) (λ _ → ret≈)
  str-coh (G ⊗f H) c (x , y)  = bind≈ (str-coh G c x) (λ a′ → fmap≈ (a′ ,_) (str-coh H c y))

  map-coh : ∀ G w → Lᶜ ρ (mapNu F G S) tt w ≈ emb (ret (mapM G w))
  map-coh Idf      cs       = ret≈
  map-coh Kone     x        = ret≈
  map-coh Kzero    ()
  map-coh (Kb b)   x        = ret≈
  map-coh (Kμ G)   x        = ret≈
  map-coh (G ⊕f H) (inj₁ x) = bind≈ (map-coh G x) (λ _ → ret≈)
  map-coh (G ⊕f H) (inj₂ y) = bind≈ (map-coh H y) (λ _ → ret≈)
  map-coh (G ⊗f H) (x , y)  = bind≈ (map-coh G x) (λ a′ → fmap≈ (a′ ,_) (map-coh H y))

  -- at each value, the core's layer is the Spec's
  pointwise : ∀ G (c : ⟦ C ⟧) w
            → mapM G (strM G c w) ≡ coh⁻¹ G (Nu F) (mapN F G (cohc F S c) (coh G S w))
  pointwise Idf      c s        = refl
  pointwise Kone     c x        = refl
  pointwise Kzero    c ()
  pointwise (Kb b)   c x        = refl
  pointwise (Kμ G)   c x        = refl
  pointwise (G ⊕f H) c (inj₁ x) = cong inj₁ (pointwise G c x)
  pointwise (G ⊕f H) c (inj₂ y) = cong inj₂ (pointwise H c y)
  pointwise (G ⊗f H) c (x , y)  = cong₂ _,_ (pointwise G c x) (pointwise H c y)

  -- the coalgebra's block, followed by the layer's pieces, is the Spec's
  -- observation of the unfold, block for block
  chain : ∀ (c : ⟦ C ⟧) (m : T ⟦ LF∙ F S ⟧)
        → Bl (embB (bindT (bindT (bindT (bindT (fmapT (c ,_) m)
                                                 (λ p → ret (fst p , strM F (fst p) (snd p))))
                                          (λ q → ret (tt , snd q)))
                                   (λ r → ret (snd r)))
                            (λ w → ret (mapM F w))))
             (embB (fmapT (coh⁻¹ F (Nu F)) (treeN F (cohc F S c) (fmapT (coh F S) m))))
  chain c (ret w)      = subst (λ z → Bl (ret (inj₁ z)) (ret (inj₁ _))) (sym (pointwise F c w)) ≈ret
  chain c (call s a k) = ≈call (λ y → chain c (k y))
  chain c (halt s a)   = ≈halt

  obs-coh : ∀ (c : ⟦ C ⟧) (s : ⟦ S ⟧) {E} (e : ⟦ E ⟧)
          → Lᶜ ρ (obsT F S) tt (c , s) ≈ Lᶜ ρ (lout {F = F} {E = E}) e (anaN F (cohc F S c) s)
  obs-coh c s e =
    ≈-trans (bind≈ (bind≈ (bind≈ (bind≈ (fmap≈ (c ,_) ≈-refl)
                                        (λ p → fmap≈ (fst p ,_) (str-coh F (fst p) (snd p))))
                                 (λ q → same refl))
                          (λ r → ret≈))
                   (map-coh F))
            (mk≈ (chain c (c s)))
