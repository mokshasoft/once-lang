{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Recursion — structured recursion
-- (`Spec.Metatheory.Recursion`).
--
-- The fold: a `μ` value is a finite tree, so a map that commutes with the
-- constructor agrees with the fold by induction (`fold-unique`); a pure
-- function that commutes with the algebras commutes with the folds
-- (`fold-fusion`). Both at every grade (`Lawful`).
--
-- The unfold: forcing it runs the coalgebra and unfolds the rest
-- (`unfold-out`), at each finite grade; it is the only map that does
-- (`unfold-unique`: every stream is a final coalgebra).
--
-- The loop is the unfold at `K B ⊕ Id`, and it is observed as its unrolling
-- (`loop-unroll`): the two traces differ by one silent step at the end of the
-- first round, after which they are the same trace.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Recursion (Σ : Signature) where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Spec.Grade using (Finite; pureᶠ; actᶠ; fin; Purity; pure; act; eff)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (foldM; layerM; traverseM)
open import Once.Spec.Signature using (⟦_⟧ᵇ; Op; module Op; arg; NotEmpty; notEmpty?; Event; eventOf)
open import Once.Spec.Observation Σ using (World; module World; History; End; returned; halted; Tr; module Tr; trace; blockD; after; EndRel; halted≈; StepRel; _≈ᵗ⟨_⟩_; module _≈ᵗ⟨_⟩_)
open import Once.Spec.Delay using (Delay; module Delay; _⇓_; now⇓; later⇓)
open import Once.Spec.Metatheory using (Recursion)
open import Once.Metatheory.Bisim Σ
open import Once.Metatheory.Lawful Σ
open import Once.Metatheory.Unfold Σ using (module Unfold)
open import Once.Metatheory.Trace Σ using (reflStep)

open νM using (outν)
open _≈ν_ using (force≈)
open Op using (ans)

------------------------------------------------------------------------
-- The fold
------------------------------------------------------------------------

module Fold (π : Purity) (G : SFunctor) where
  open Lawful (lawful π)

  fmap-cong : ∀ {X Y} (f : X → Y) {m m′ : M π X} → EqM π m m′ → EqM π (fmap π f m) (fmap π f m′)
  fmap-cong f p = eq-trans (fmap-bind f _) (eq-trans (bind-cong p (λ x → eq-refl _)) (eq-sym (fmap-bind f _)))

  -- `fmap` after a `bind`, a `bind` after an `fmap`, two `fmap`s, `fmap` of a unit.
  fmap-after : ∀ {A B C} (h : B → C) (m : M π A) (k : A → M π B)
             → EqM π (fmap π h (bind π m k)) (bind π m λ a → fmap π h (k a))
  fmap-after h m k =
    eq-trans (fmap-bind h _)
      (eq-trans (bind-assoc m k _) (bind-cong (eq-refl m) (λ a → eq-sym (fmap-bind h (k a)))))

  bind-fmap : ∀ {A B C} (h : A → B) (m : M π A) (k : B → M π C)
            → EqM π (bind π (fmap π h m) k) (bind π m λ a → k (h a))
  bind-fmap h m k =
    eq-trans (bind-cong (fmap-bind h m) (λ b → eq-refl (k b)))
      (eq-trans (bind-assoc m _ k) (bind-cong (eq-refl m) (λ a → bind-idˡ (h a) k)))

  fmap-fmap : ∀ {A B C} (h : B → C) (h′ : A → B) (m : M π A)
            → EqM π (fmap π h (fmap π h′ m)) (fmap π (λ a → h (h′ a)) m)
  fmap-fmap h h′ m =
    eq-trans (fmap-bind h _)
      (eq-trans (bind-fmap h′ m _) (eq-sym (fmap-bind _ m)))

  fmap-return : ∀ {A B} (h : A → B) (a : A) → EqM π (fmap π h (return π a)) (return π (h a))
  fmap-return h a = eq-trans (fmap-bind h _) (bind-idˡ a _)

  -- A layer of the fold is the traversal by the fold.
  layer≡ : ∀ {X} (alg : ⟦ G ⟧SF X → M π X) (H : SFunctor) (x : ⟦ H ⟧SF (μS G))
         → layerM π G H alg x ≡ traverseM π H (foldM π G alg) x
  layer≡ alg (SK B)     x        = refl
  layer≡ alg SId        x        = refl
  layer≡ alg (H₁ S⊕ H₂) (inj₁ x) = cong (fmap π inj₁) (layer≡ alg H₁ x)
  layer≡ alg (H₁ S⊕ H₂) (inj₂ y) = cong (fmap π inj₂) (layer≡ alg H₂ y)
  layer≡ alg (H₁ S⊗ H₂) (x , y)  =
    cong₂ (λ a b → bind π a λ u → bind π b λ v → return π (u , v)) (layer≡ alg H₁ x) (layer≡ alg H₂ y)

  fold-in : ∀ {X} (alg : ⟦ G ⟧SF X → M π X) (x : ⟦ G ⟧SF (μS G))
          → EqM π (foldM π G alg (inS x)) (bind π (traverseM π G (foldM π G alg) x) alg)
  fold-in alg x = subst (λ t → EqM π (foldM π G alg (inS x)) (bind π t alg)) (layer≡ alg G x) (eq-refl _)

  module Unique {X : Set} (alg : ⟦ G ⟧SF X → M π X) (h : μS G → M π X)
                (hyp : ∀ x → EqM π (h (inS x)) (bind π (traverseM π G h x) alg)) where
    unique : ∀ v → EqM π (h v) (foldM π G alg v)
    layer  : ∀ H (x : ⟦ H ⟧SF (μS G)) → EqM π (traverseM π H h x) (layerM π G H alg x)
    unique (inS x) = eq-trans (hyp x) (bind-cong (layer G x) (λ l → eq-refl (alg l)))
    layer (SK B)     x        = eq-refl _
    layer SId        x        = unique x
    layer (H₁ S⊕ H₂) (inj₁ x) = fmap-cong inj₁ (layer H₁ x)
    layer (H₁ S⊕ H₂) (inj₂ y) = fmap-cong inj₂ (layer H₂ y)
    layer (H₁ S⊗ H₂) (x , y)  = bind-cong (layer H₁ x) (λ u → bind-cong (layer H₂ y) (λ v → eq-refl _))

  module Fusion {X Y : Set} (alg : ⟦ G ⟧SF X → M π X) (alg′ : ⟦ G ⟧SF Y → M π Y) (g : X → Y)
                (hyp : ∀ l → EqM π (fmap π g (alg l)) (alg′ (sfmap G g l))) where
    fusion : ∀ v → EqM π (fmap π g (foldM π G alg v)) (foldM π G alg′ v)
    layer  : ∀ H (x : ⟦ H ⟧SF (μS G))
           → EqM π (fmap π (sfmap H g) (layerM π G H alg x)) (layerM π G H alg′ x)
    fusion (inS x) =
      eq-trans (fmap-after g (layerM π G G alg x) alg)
        (eq-trans (bind-cong (eq-refl _) hyp)
          (eq-trans (eq-sym (bind-fmap (sfmap G g) (layerM π G G alg x) alg′))
            (bind-cong (layer G x) (λ l → eq-refl (alg′ l)))))
    layer (SK B)     x        = fmap-return (sfmap (SK B) g) x
    layer SId        x        = fusion x
    layer (H₁ S⊕ H₂) (inj₁ x) =
      eq-trans (fmap-fmap (sfmap (H₁ S⊕ H₂) g) inj₁ _)
        (eq-trans (eq-sym (fmap-fmap inj₁ (sfmap H₁ g) _)) (fmap-cong inj₁ (layer H₁ x)))
    layer (H₁ S⊕ H₂) (inj₂ y) =
      eq-trans (fmap-fmap (sfmap (H₁ S⊕ H₂) g) inj₂ _)
        (eq-trans (eq-sym (fmap-fmap inj₂ (sfmap H₂ g) _)) (fmap-cong inj₂ (layer H₂ y)))
    layer (H₁ S⊗ H₂) (x , y)  =
      eq-trans (fmap-after (sfmap (H₁ S⊗ H₂) g) L₁ _)
        (eq-trans (bind-cong (eq-refl L₁) (λ u →
                    eq-trans (fmap-after (sfmap (H₁ S⊗ H₂) g) L₂ _)
                      (bind-cong (eq-refl L₂) (λ v → fmap-return (sfmap (H₁ S⊗ H₂) g) (u , v)))))
          (eq-trans (eq-sym (bind-cong (eq-refl L₁) (λ u → bind-fmap (sfmap H₂ g) L₂ _)))
            (eq-trans (eq-sym (bind-fmap (sfmap H₁ g) L₁ _))
              (bind-cong (layer H₁ x) (λ u′ → bind-cong (layer H₂ y) (λ v′ → eq-refl _))))))
      where
        L₁ = layerM π G H₁ alg x
        L₂ = layerM π G H₂ alg y

------------------------------------------------------------------------
-- The unfold
------------------------------------------------------------------------

module UnfoldEq (G : SFunctor) where
  open Unfold G

  unfold-out : ∀ (f : Finite) {X : Set} (c : X → Mᶠ f (⟦ G ⟧SF X)) (x : X)
             → EqM (fin f) (outν (ana f G c x)) (fmap (fin f) (sfmap G (ana f G c)) (c x))
  unfold-out f c x = unfold-out≈ f c x

-- Every stream is a final coalgebra: a coalgebra morphism into it is the
-- unfold, up to bisimilarity.
module Final (G : SFunctor) {X : Set} where
  private
    E : ∀ (f : Finite) → Mᶠ f (⟦ G ⟧SF (νM f G)) → Mᶠ f (⟦ G ⟧SF (νM f G)) → Set
    E f = EqLayer f (LayerEq G _≈ν_)

  module P (c : X → ⟦ G ⟧SF X) (g : X → νM pureᶠ G) (hyp : ∀ x → E pureᶠ (outν (g x)) (sfmap G g (c x))) where
    up  : ∀ (v : νM pureᶠ G) (x : X) → v ≈ν g x → v ≈ν ana pureᶠ G c x
    upL : ∀ (H : SFunctor) (s : ⟦ H ⟧SF (νM pureᶠ G)) (l : ⟦ H ⟧SF X) → LayerEq H _≈ν_ s (sfmap H g l)
        → LayerEq H _≈ν_ s (mapP G H c l)
    force≈ (up v x p) = upL G (outν v) (c x) (≈ν-transL G (force≈ p) (hyp x))
    upL (SK B)     s        l        q = q
    upL SId        s        l        q = up s l q
    upL (H₁ S⊕ H₂) (inj₁ s) (inj₁ l) q = upL H₁ s l q
    upL (H₁ S⊕ H₂) (inj₂ s) (inj₂ l) q = upL H₂ s l q
    upL (H₁ S⊕ H₂) (inj₁ s) (inj₂ l) ()
    upL (H₁ S⊕ H₂) (inj₂ s) (inj₁ l) ()
    upL (H₁ S⊗ H₂) (s , s′) (l , l′) (q , q′) = upL H₁ s l q , upL H₂ s′ l′ q′

  module A (c : X → T (⟦ G ⟧SF X)) (g : X → νM actᶠ G)
           (hyp : ∀ x → E actᶠ (outν (g x)) (c x >>=T λ l → returnT (sfmap G g l))) where
    up  : ∀ (v : νM actᶠ G) (x : X) → v ≈ν g x → v ≈ν ana actᶠ G c x
    upB : ∀ (s : T (⟦ G ⟧SF (νM actᶠ G))) (t : T (⟦ G ⟧SF X))
        → BlockEq (LayerEq G _≈ν_) s (t >>=T λ l → returnT (sfmap G g l)) → BlockEq (LayerEq G _≈ν_) s (treeA G c t)
    upL : ∀ (H : SFunctor) (s : ⟦ H ⟧SF (νM actᶠ G)) (l : ⟦ H ⟧SF X) → LayerEq H _≈ν_ s (sfmap H g l)
        → LayerEq H _≈ν_ s (mapA G H c l)
    force≈ (up v x p) = upB (outν v) (c x) (≈ν-transB {G = G} (force≈ p) (hyp x))
    upB (roll (done l′)) (roll (done l)) (done≈ q) = done≈ (upL G l′ l q)
    upB (roll (node (call o a k′))) (roll (node (call .o .a k))) (node≈ e) = node≈ λ b → upB (k′ b) (k b) (e b)
    upB (roll (done l′)) (roll (node (call o a k))) ()
    upB (roll (node (call o a k′))) (roll (done l)) ()
    upL (SK B)     s        l        q = q
    upL SId        s        l        q = up s l q
    upL (H₁ S⊕ H₂) (inj₁ s) (inj₁ l) q = upL H₁ s l q
    upL (H₁ S⊕ H₂) (inj₂ s) (inj₂ l) q = upL H₂ s l q
    upL (H₁ S⊕ H₂) (inj₁ s) (inj₂ l) ()
    upL (H₁ S⊕ H₂) (inj₂ s) (inj₁ l) ()
    upL (H₁ S⊗ H₂) (s , s′) (l , l′) (q , q′) = upL H₁ s l q , upL H₂ s′ l′ q′

  unfold-unique : ∀ (f : Finite) (c : X → Mᶠ f (⟦ G ⟧SF X)) (g : X → νM f G)
                → (∀ x → EqLayer f (LayerEq G _≈ν_) (outν (g x)) (fmap (fin f) (sfmap G g) (c x)))
                → ∀ x → g x ≈ν ana f G c x
  unfold-unique pureᶠ c g hyp x = P.up c g hyp (g x) x (≈ν-refl (g x))
  unfold-unique actᶠ  c g hyp x = A.up c g hyp (g x) x (≈ν-refl (g x))

------------------------------------------------------------------------
-- The loop is observed as its unrolling
------------------------------------------------------------------------

module Unroll {A B : Set} (c : A → T (B ⊎ A)) (w : World) where
  open World w using (answer)
  open Delay using (step)
  open Tr using (next)
  open _≈ᵗ⟨_⟩_ using (same)

  private
    G : SFunctor
    G = SK B S⊕ SId
    k : B ⊎ A → T∞ B
    k = [ return∞ , loop c ]′
    S : Set
    S = End B ⊎ (Event × Tr B)

  -- The loop's block and the unrolled one, for a round's block `t`.
  L R′ : T (B ⊎ A) → T (B ⊎ T∞ B)
  L t  = treeA G c t
  R′ t = bindBlock (mapT inj₁ t) k

  -- Their visible steps: the same, or the same call with the same rounds
  -- to come.
  data UStep : S → S → Set where
    same≡ : ∀ {o} → UStep o o
    call≈ : ∀ {h o a} {κ : ⟦ Op.ans o ⟧ᵇ → T (B ⊎ A)} (d : Dec (NotEmpty (ans o)))
          → UStep (inj₂ (eventOf o a , after w h o a (λ b → L (κ b)) d)) (inj₂ (eventOf o a , after w h o a (λ b → R′ (κ b)) d))

  match : ∀ (h : History) (t : T (B ⊎ A)) o → blockD w h (L t) ⇓ o → ∃[ o′ ] (blockD w h (R′ t) ⇓ o′ × UStep o o′)
  match h (roll (done (inj₁ b)))     o a = o , a , same≡
  match h (roll (done (inj₂ a′)))    o (now⇓ ())
  match h (roll (done (inj₂ a′)))    o (later⇓ refl a) = o , a , same≡
  match h (roll (node (call oₒ x κ))) o (now⇓ refl) = _ , now⇓ refl , call≈ (notEmpty? (ans oₒ))
  match h (roll (node (call oₒ x κ))) o (later⇓ () _)

  match′ : ∀ (h : History) (t : T (B ⊎ A)) o′ → blockD w h (R′ t) ⇓ o′ → ∃[ o ] (blockD w h (L t) ⇓ o × UStep o o′)
  match′ h (roll (done (inj₁ b)))     o′ a = o′ , a , same≡
  match′ h (roll (done (inj₂ a′)))    o′ a = o′ , later⇓ refl a , same≡
  match′ h (roll (node (call oₒ x κ))) o′ (now⇓ refl) = _ , now⇓ refl , call≈ (notEmpty? (ans oₒ))
  match′ h (roll (node (call oₒ x κ))) o′ (later⇓ () _)

  roundsSim : ∀ (h : History) (o : Op Σ) (a : ⟦ arg o ⟧ᵇ) (κ : ⟦ Op.ans o ⟧ᵇ → T (B ⊎ A)) (d : Dec (NotEmpty (ans o)))
            → after w h o a (λ b → L (κ b)) d ≈ᵗ⟨ _≡_ ⟩ after w h o a (λ b → R′ (κ b)) d
  stepU : ∀ {o o′} → UStep o o′ → StepRel _≡_ _≈ᵗ⟨ _≡_ ⟩_ o o′
  lift  : ∀ {d : Delay S} {o} → ∃[ o′ ] (d ⇓ o′ × UStep o o′) → ∃[ o′ ] (d ⇓ o′ × StepRel _≡_ _≈ᵗ⟨ _≡_ ⟩_ o o′)
  lift′ : ∀ {d : Delay S} {o′} → ∃[ o ] (d ⇓ o × UStep o o′) → ∃[ o ] (d ⇓ o × StepRel _≡_ _≈ᵗ⟨ _≡_ ⟩_ o o′)
  same (roundsSim h o a κ (yes p)) =
      (λ o₁ a₁ → lift (match (h ++ [ eventOf o a ]) (κ (answer o h a p)) o₁ a₁))
    , (λ o₁ a₁ → lift′ (match′ (h ++ [ eventOf o a ]) (κ (answer o h a p)) o₁ a₁))
  same (roundsSim h o a κ (no _)) = (λ { _ (now⇓ refl) → _ , now⇓ refl , halted≈ ; _ (later⇓ () _) })
                                  , (λ { _ (now⇓ refl) → _ , now⇓ refl , halted≈ ; _ (later⇓ () _) })
  stepU {o} same≡ = reflStep (λ _ → refl) o
  stepU (call≈ {h} {o} {a} {κ} d) = refl , roundsSim h o a κ d
  lift (o′ , a , r) = o′ , a , stepU r
  lift′ (o , a , r) = o , a , stepU r

  loop-unroll : ∀ (a : A) → trace w [] (loop c a) ≈ᵗ⟨ _≡_ ⟩ trace w [] (embed (c a) >>=∞ k)
  same (loop-unroll a) = (λ o a₁ → lift (match [] (c a) o a₁)) , (λ o a₁ → lift′ (match′ [] (c a) o a₁))

recursion : Recursion Σ
recursion = record
  { fold-in       = λ π G alg x → Fold.fold-in π G alg x
  ; fold-unique   = λ π G alg h hyp → Fold.Unique.unique π G alg h hyp
  ; fold-fusion   = λ π G alg alg′ g hyp → Fold.Fusion.fusion π G alg alg′ g hyp
  ; unfold-out    = λ f G c x → UnfoldEq.unfold-out G f c x
  ; unfold-unique = λ f G c g hyp x → Final.unfold-unique G f c g hyp x
  ; loop-unroll   = λ c a w → Unroll.loop-unroll c w a
  }
