-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Recursion — structured recursion
-- (`Spec.Metatheory.Recursion`).
--
-- The fold: a `μ` value is a finite tree, so a map that commutes with the
-- constructor agrees with the fold by induction (`fold-unique`); a pure
-- function that commutes with the algebras commutes with the folds
-- (`fold-fusion`). Both at every grade with a unit (`Lawful`).
--
-- The unfold: forcing it runs the coalgebra and unfolds the rest
-- (`unfold-out`), at each grade.
--
-- The server: `iter∞ f` satisfies its equation (`iter-unfold`), and is its
-- only solution (`iter-unique`) — a bisimulation up to the equation, whose
-- every round begins with an event.
--
-- Not `--safe`: `Lawful`'s `act` instance and the `act` unfold use function
-- extensionality (`Once.Postulates`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Recursion (Σ : Signature) where

open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Once.Postulates using (extensionality)
open import Once.Spec.Grade using (Purity; pure; act; eff⁺; eff; _⊑π_)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ
  using (foldM; layerM; traverseM; anaM; anaP; mapP; anaA; treeA; mapA; anaE; treeE; stepE; mapE; anaG; rootG; treeG; stepG; mapG)
open import Once.Spec.Metatheory using (Recursion)
open import Once.Metatheory.Bisim Σ
open import Once.Metatheory.Lawful Σ

open T∞ using (force)
open _≈_ using (force≈)
open νM using (outν)

------------------------------------------------------------------------
-- The fold
------------------------------------------------------------------------

module Fold (π : Purity) (e : pure ⊑π π) (G : SFunctor) where
  open Lawful (lawful π e)

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

  fmap-return : ∀ {A B} (h : A → B) (a : A) → EqM π (fmap π h (return e a)) (return e (h a))
  fmap-return h a = eq-trans (fmap-bind h _) (bind-idˡ a _)

  module Unique {X : Set} (alg : ⟦ G ⟧SF X → M π X) (h : μS G → M π X)
                (hyp : ∀ x → EqM π (h (inS x)) (bind π (traverseM π e G h x) alg)) where
    unique : ∀ v → EqM π (h v) (foldM π e G alg v)
    layer  : ∀ H (x : ⟦ H ⟧SF (μS G)) → EqM π (traverseM π e H h x) (layerM π e G H alg x)
    unique (inS x) = eq-trans (hyp x) (bind-cong (layer G x) (λ l → eq-refl (alg l)))
    layer (SK B)     x        = eq-refl _
    layer SId        x        = unique x
    layer (H₁ S⊕ H₂) (inj₁ x) = fmap-cong inj₁ (layer H₁ x)
    layer (H₁ S⊕ H₂) (inj₂ y) = fmap-cong inj₂ (layer H₂ y)
    layer (H₁ S⊗ H₂) (x , y)  = bind-cong (layer H₁ x) (λ u → bind-cong (layer H₂ y) (λ v → eq-refl _))

  module Fusion {X Y : Set} (alg : ⟦ G ⟧SF X → M π X) (alg′ : ⟦ G ⟧SF Y → M π Y) (g : X → Y)
                (hyp : ∀ l → EqM π (fmap π g (alg l)) (alg′ (sfmap G g l))) where
    fusion : ∀ v → EqM π (fmap π g (foldM π e G alg v)) (foldM π e G alg′ v)
    layer  : ∀ H (x : ⟦ H ⟧SF (μS G))
           → EqM π (fmap π (sfmap H g) (layerM π e G H alg x)) (layerM π e G H alg′ x)
    fusion (inS x) =
      eq-trans (fmap-after g (layerM π e G G alg x) alg)
        (eq-trans (bind-cong (eq-refl _) hyp)
          (eq-trans (eq-sym (bind-fmap (sfmap G g) (layerM π e G G alg x) alg′))
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
        L₁ = layerM π e G H₁ alg x
        L₂ = layerM π e G H₂ alg y

------------------------------------------------------------------------
-- The unfold
------------------------------------------------------------------------

module Unfold (G : SFunctor) where
  mapP≡ : ∀ {X} (c : X → ⟦ G ⟧SF X) H (l : ⟦ H ⟧SF X) → mapP G H c l ≡ sfmap H (anaP G c) l
  mapP≡ c (SK B)     l        = refl
  mapP≡ c SId        l        = refl
  mapP≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapP≡ c H₁ x)
  mapP≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapP≡ c H₂ y)
  mapP≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapP≡ c H₁ x) (mapP≡ c H₂ y)

  mapA≡ : ∀ {X} (c : X → T (⟦ G ⟧SF X)) H (l : ⟦ H ⟧SF X) → mapA G H c l ≡ sfmap H (anaA G c) l
  mapA≡ c (SK B)     l        = refl
  mapA≡ c SId        l        = refl
  mapA≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapA≡ c H₁ x)
  mapA≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapA≡ c H₂ y)
  mapA≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapA≡ c H₁ x) (mapA≡ c H₂ y)

  mapE≡ : ∀ {X} (c : X → T∞ (⟦ G ⟧SF X)) H (l : ⟦ H ⟧SF X) → mapE G H c l ≡ sfmap H (anaE G c) l
  mapE≡ c (SK B)     l        = refl
  mapE≡ c SId        l        = refl
  mapE≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapE≡ c H₁ x)
  mapE≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapE≡ c H₂ y)
  mapE≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapE≡ c H₁ x) (mapE≡ c H₂ y)

  mapG≡ : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) H (l : ⟦ H ⟧SF X) → mapG G H c l ≡ sfmap H (anaG G c) l
  mapG≡ c (SK B)     l        = refl
  mapG≡ c SId        l        = refl
  mapG≡ c (H₁ S⊕ H₂) (inj₁ x) = cong inj₁ (mapG≡ c H₁ x)
  mapG≡ c (H₁ S⊕ H₂) (inj₂ y) = cong inj₂ (mapG≡ c H₂ y)
  mapG≡ c (H₁ S⊗ H₂) (x , y)  = cong₂ _,_ (mapG≡ c H₁ x) (mapG≡ c H₂ y)

  doneEq : ∀ {X} {x y : X} → x ≡ y → StepEq {X = X} {Y = T∞ X} _≈_ (done x) (done y)
  doneEq refl = done≈

  treeA≡ : ∀ {X} (c : X → T (⟦ G ⟧SF X)) (t : T (⟦ G ⟧SF X))
         → treeA G c t ≡ (t >>=T λ l → returnT (sfmap G (anaA G c) l))
  treeA≡ c (roll (done l))            = cong (λ z → roll (done z)) (mapA≡ c G l)
  treeA≡ c (roll (node (call o a k))) =
    cong (λ k → roll (node (call o a k))) (extensionality λ b → treeA≡ c (k b))

  treeE≈ : ∀ {X} (c : X → T∞ (⟦ G ⟧SF X)) (t : T∞ (⟦ G ⟧SF X))
         → treeE G c t ≈ (t >>=∞ λ l → return∞ (sfmap G (anaE G c) l))
  treeE≈S : ∀ {X} (c : X → T∞ (⟦ G ⟧SF X)) (s : Step (⟦ G ⟧SF X) (T∞ (⟦ G ⟧SF X)))
          → StepEq _≈_ (stepE G c s) (bindStep s λ l → return∞ (sfmap G (anaE G c) l))
  force≈ (treeE≈ c t) = treeE≈S c (force t)
  treeE≈S c (done l)            = doneEq (mapE≡ c G l)
  treeE≈S c (node (call o a k)) = node≈ λ b → treeE≈ c (k b)

  treeG≈ : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) (t : T∞ (⟦ G ⟧SF X))
         → treeG G c t ≈ (t >>=∞ λ l → return∞ (sfmap G (anaG G c) l))
  treeG≈S : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) (s : Step (⟦ G ⟧SF X) (T∞ (⟦ G ⟧SF X)))
          → StepEq _≈_ (stepG G c s) (bindStep s λ l → return∞ (sfmap G (anaG G c) l))
  force≈ (treeG≈ c t) = treeG≈S c (force t)
  treeG≈S c (done l)            = doneEq (mapG≡ c G l)
  treeG≈S c (node (call o a k)) = node≈ λ b → treeG≈ c (k b)

  rootG≈ : ∀ {X} (c : X → T⁺ (⟦ G ⟧SF X)) (r : T⁺ (⟦ G ⟧SF X))
         → forget⁺ (rootG G c r) ≈ forget⁺ (r >>=⁺ λ l → return∞ (sfmap G (anaG G c) l))
  force≈ (rootG≈ c (call⁺ (call o a k))) = node≈ λ b → treeG≈ c (k b)

  unfold-out : ∀ π {X : Set} (c : X → M π (⟦ G ⟧SF X)) (x : X)
             → EqM π (outν (anaM π G c x)) (fmap π (sfmap G (anaM π G c)) (c x))
  unfold-out pure c x = mapP≡ c G (c x)
  unfold-out act  c x = treeA≡ c (c x)
  unfold-out eff⁺ c x = rootG≈ c (c x)
  unfold-out eff  c x = treeE≈ c (c x)

------------------------------------------------------------------------
-- The server
------------------------------------------------------------------------

module Server {A B : Set} (f : A → B ⊎ T⁺ (B ⊎ A)) where
  -- The equation's right-hand side, at a solution `g`.
  rhs : (A → T∞ B) → B ⊎ T⁺ (B ⊎ A) → T∞ B
  rhs g = [ return∞ , (λ m → forget⁺ m >>=∞ [ return∞ , g ]′) ]′

  iter-unfoldT : ∀ (t : T∞ (B ⊎ A)) → iterTree f t ≈ (t >>=∞ [ return∞ , iter∞ f ]′)
  iter-unfoldS : ∀ (s : Step (B ⊎ A) (T∞ (B ⊎ A))) → StepEq _≈_ (iterStep f s) (bindStep s [ return∞ , iter∞ f ]′)
  force≈ (iter-unfoldT t) = iter-unfoldS (force t)
  iter-unfoldS (done (inj₁ b))     = done≈
  iter-unfoldS (done (inj₂ a))     = ≈-reflS (iterStart f (f a))
  iter-unfoldS (node (call o x k)) = node≈ λ r → iter-unfoldT (k r)

  iter-unfoldU : ∀ (u : B ⊎ T⁺ (B ⊎ A)) → StepEq _≈_ (iterStart f u) (force (rhs (iter∞ f) u))
  iter-unfoldU (inj₁ b)                    = done≈
  iter-unfoldU (inj₂ (call⁺ (call o x k))) = node≈ λ r → iter-unfoldT (k r)

  iter-unfold : ∀ (a : A) → iter∞ f a ≈ rhs (iter∞ f) (f a)
  force≈ (iter-unfold a) = iter-unfoldU (f a)

  module Unique (g : A → T∞ B) (hyp : ∀ a → g a ≈ rhs g (f a)) where
    -- A tree bisimilar to `t >>= [ return , g ]` is bisimilar to `iterTree f t`.
    upT : ∀ (m : T∞ B) (t : T∞ (B ⊎ A)) → m ≈ (t >>=∞ [ return∞ , g ]′) → m ≈ iterTree f t
    upS : ∀ (s₁ : Step B (T∞ B)) (s : Step (B ⊎ A) (T∞ (B ⊎ A)))
        → StepEq _≈_ s₁ (bindStep s [ return∞ , g ]′) → StepEq _≈_ s₁ (iterStep f s)
    upU : ∀ (s₁ : Step B (T∞ B)) (u : B ⊎ T⁺ (B ⊎ A))
        → StepEq _≈_ s₁ (force (rhs g u)) → StepEq _≈_ s₁ (iterStart f u)
    force≈ (upT m t p) = upS (force m) (force t) (force≈ p)
    upS s₁ (done (inj₁ b))     p         = p
    upS s₁ (done (inj₂ a))     p         = upU s₁ (f a) (≈-transS p (force≈ (hyp a)))
    upS s₁ (node (call o x k)) (node≈ e) = node≈ λ r → upT _ (k r) (e r)
    upU s₁ (inj₁ b)                    p         = p
    upU s₁ (inj₂ (call⁺ (call o x k))) (node≈ e) = node≈ λ r → upT _ (k r) (e r)

    iter-unique : ∀ a → g a ≈ iter∞ f a
    force≈ (iter-unique a) = upU (force (g a)) (f a) (force≈ (hyp a))

------------------------------------------------------------------------
-- All of it
------------------------------------------------------------------------

recursion : Recursion Σ
recursion = record
  { fold-unique = λ π e G alg h hyp → Fold.Unique.unique π e G alg h hyp
  ; fold-fusion = λ π e G alg alg′ g hyp → Fold.Fusion.fusion π e G alg alg′ g hyp
  ; unfold-out  = λ π G c x → Unfold.unfold-out G π c x
  ; iter-unfold = λ f a → Server.iter-unfold f a
  ; iter-unique = λ f g hyp a → Server.Unique.iter-unique f g hyp a
  }
