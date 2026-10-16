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
-- (`unfold-out`), at each grade a coalgebra may have.
--
-- The loop: its first block is the round's, ending at the loop of the next
-- state (`loop-out`); it is the only map that is (`loop-unique`: `T∞ B` is the
-- final coalgebra of `T (B + −)`); and it is observed as its unrolling
-- (`loop-unroll`): the two observations differ by one step of the delay at the
-- end of the first round.
--
-- Not `--safe`: `Lawful`'s `act` instance and the `act` unfold use function
-- extensionality (`Once.Postulates`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Recursion (Σ : Signature) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
import Data.Empty
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Postulates using (extensionality)
open import Once.Spec.Grade using (Purity; pure; act; eff; _⊑π_; ⊑-pa; ⊑-act)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (foldM; layerM; traverseM; anaM; anaP; mapP; anaA; treeA; mapA)
open import Once.Spec.Signature using (BTy; ⟦_⟧ᵇ; void; unit; int; float; _*_; _+_; module Op)
open import Once.Spec.Observation Σ using (Interp; module Interp; History; End; observe; blockObs; answerObs; resume)
open import Once.Spec.Delay using (Delay; module Delay; _⇓_; now⇓; later⇓; _≈D_)
open import Once.Spec.Metatheory using (Recursion)
open import Once.Metatheory.Bisim Σ
open import Once.Metatheory.Lawful Σ
open import Once.Metatheory.Unfold Σ using (module Unfold)

open T∞ using (force)
open _≈_ using (force≈)
open νM using (outν)

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

  treeA≡ : ∀ {X} (c : X → T (⟦ G ⟧SF X)) (t : T (⟦ G ⟧SF X))
         → treeA G c t ≡ (t >>=T λ l → returnT (sfmap G (anaA G c) l))
  treeA≡ c (roll (done l))            = cong (λ z → roll (done z)) (mapA≡ c G l)
  treeA≡ c (roll (node (call o a k))) =
    cong (λ k → roll (node (call o a k))) (extensionality λ b → treeA≡ c (k b))

  unfold-out : ∀ {π} (g : π ⊑π act) {X : Set} (c : X → M π (⟦ G ⟧SF X)) (x : X)
             → EqM π (outν (anaM g G c x)) (fmap π (sfmap G (anaM g G c)) (c x))
  unfold-out ⊑-pa  c x = mapP≡ c G (c x)
  unfold-out ⊑-act c x = treeA≡ c (c x)


module Loop {A B : Set} (c : A → T (B ⊎ A)) where
  -- Where a round ends: with the result, or with the loop from the next state.
  next : (A → T∞ B) → B ⊎ A → B ⊎ T∞ B
  next g = [ inj₁ , (λ a′ → inj₂ (g a′)) ]′

  loopBlock≡ : ∀ (t : T (B ⊎ A)) → loopBlock c t ≡ mapT (next (loop c)) t
  loopBlock≡ (roll (done (inj₁ b)))     = refl
  loopBlock≡ (roll (done (inj₂ a)))     = refl
  loopBlock≡ (roll (node (call o x k))) =
    cong (λ k → roll (node (call o x k))) (extensionality λ r → loopBlock≡ (k r))

  loop-out : ∀ (a : A) → force (loop c a) ≡ mapT (next (loop c)) (c a)
  loop-out a = loopBlock≡ (c a)

  module Unique (g : A → T∞ B) (hyp : ∀ a → BlockEq _≈_ (force (g a)) (mapT (next g) (c a))) where
    -- A computation bisimilar to `g a` is bisimilar to the loop from `a`.
    up  : ∀ (m : T∞ B) (a : A) → m ≈ g a → m ≈ loop c a
    upB : ∀ (s : T (B ⊎ T∞ B)) (t : T (B ⊎ A)) → BlockEq _≈_ s (mapT (next g) t) → BlockEq _≈_ s (loopBlock c t)
    force≈ (up m a p) = upB (force m) (c a) (≈-transB (force≈ p) (hyp a))
    upB s (roll (done (inj₁ b)))     p         = p
    upB s (roll (done (inj₂ a′)))    (next≈ q) = next≈ (up _ a′ q)
    upB s (roll (node (call o x k))) (node≈ e) = node≈ λ r → upB _ (k r) (e r)

    loop-unique : ∀ a → g a ≈ loop c a
    loop-unique a = up (g a) a (≈-refl (g a))

  module Unroll (ι : Interp) where
    open Interp ι using (answer)
    open Delay using (step)

    -- The unrolled loop runs the round's block, then the loop at once.
    unrolled : A → T∞ B
    unrolled a = embed (c a) >>=∞ [ return∞ , loop c ]′

    S : Set
    S = (History × End B) ⊎ Delay (History × End B)

    -- One step of the two observations: the same, or one extra step on the left.
    data Rel : S → S → Set where
      same  : ∀ {s} → Rel s s
      extra : ∀ {d} → Rel (inj₂ d) (step d)

    rel  : ∀ h cs (t : T (B ⊎ A)) n
         → Rel (blockObs ι h cs (loopBlock c t) n) (blockObs ι h cs (bindBlock (mapT inj₁ t) [ return∞ , loop c ]′) n)
    relA : ∀ h cs (b : BTy) v (k : ⟦ b ⟧ᵇ → T (B ⊎ A)) n
         → Rel (answerObs ι h cs (resume b v (λ r → loopBlock c (k r))) n)
               (answerObs ι h cs (resume b v (λ r → bindBlock (mapT inj₁ (k r)) [ return∞ , loop c ]′)) n)
    rel h cs t                          zero    = same
    rel h cs (roll (done (inj₁ b)))     (suc n) = same
    rel h cs (roll (done (inj₂ a′)))    (suc n) = extra
    rel h cs (roll (node (call o x k))) (suc n) = relA _ _ (Op.ans o) (answer o h x) k n
    relA h cs void    v k n = same
    relA h cs unit    v k n = rel h cs (k v) n
    relA h cs int     v k n = rel h cs (k v) n
    relA h cs float   v k n = rel h cs (k v) n
    relA h cs (a * b) v k n = rel h cs (k v) n
    relA h cs (a + b) v k n = rel h cs (k v) n

    private
      sameStep : ∀ {d d′ : Delay (History × End B)} {o} → step d ≡ step d′ → d ⇓ o → d′ ⇓ o
      sameStep p (now⇓ e)      = now⇓ (trans (sym p) e)
      sameStep p (later⇓ e d⇓) = later⇓ (trans (sym p) e) d⇓

      inj₂-inj : ∀ {d d′ : Delay (History × End B)} → _≡_ {A = S} (inj₂ d) (inj₂ d′) → d ≡ d′
      inj₂-inj refl = refl

      inj₂≢inj₁ : ∀ {d : Delay (History × End B)} {o} → _≡_ {A = S} (inj₂ d) (inj₁ o) → Data.Empty.⊥
      inj₂≢inj₁ ()

      fwd : ∀ {sL sR} {dL dR : Delay (History × End B)} {o} → Rel sL sR → step dL ≡ sL → step dR ≡ sR → dL ⇓ o → dR ⇓ o
      fwd same eL eR d⇓ = sameStep (trans eL (sym eR)) d⇓
      fwd extra eL eR (now⇓ e) = ⊥-elim (inj₂≢inj₁ (trans (sym eL) e))
      fwd extra eL eR (later⇓ e d⇓) = sameStep (sym eR) (subst (_⇓ _) (sym (inj₂-inj (trans (sym eL) e))) d⇓)

      bwd : ∀ {sL sR} {dL dR : Delay (History × End B)} {o} → Rel sL sR → step dL ≡ sL → step dR ≡ sR → dR ⇓ o → dL ⇓ o
      bwd same eL eR d⇓ = sameStep (trans eR (sym eL)) d⇓
      bwd extra eL eR d⇓ = later⇓ eL (sameStep eR d⇓)

    loop-unroll : ∀ (a : A) (h : History) n → observe ι h (loop c a) n ≈D observe ι h (unrolled a) n
    loop-unroll a h n =
        (λ o d⇓ → o , fwd (rel h [] (c a) n) refl refl d⇓ , refl)
      , (λ o d⇓ → o , bwd (rel h [] (c a) n) refl refl d⇓ , refl)


recursion : Recursion Σ
recursion = record
  { fold-unique = λ π G alg h hyp → Fold.Unique.unique π G alg h hyp
  ; fold-fusion = λ π G alg alg′ g hyp → Fold.Fusion.fusion π G alg alg′ g hyp
  ; unfold-out  = λ g G c x → UnfoldEq.unfold-out G g c x
  ; loop-out    = λ c a → Loop.loop-out c a
  ; loop-unique = λ c g hyp a → Loop.Unique.loop-unique c g hyp a
  ; loop-unroll = λ c a ι h n → Loop.Unroll.loop-unroll c ι a h n
  }
