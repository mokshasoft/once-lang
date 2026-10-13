-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Relation — the logical relation coherence is
-- proved with (plan 0.116 D1c).
--
-- `Same A` (the Spec's, `Spec.Equivalence`) observes to every finite depth
-- `n`, with the depth OUTSIDE: `∀ n → Obs n A x y`. A proof by induction on
-- derivations needs it INSIDE the trees: a computation's result is bound to
-- a variable, and a variable must be the same at every depth. `S A` is that
-- relation — by type, as `Obs`, but an arrow's results are related by
-- BISIMILARITY of their trees (`TreeEq∞ (S B)`, every grade read in the
-- completely iterative monad through `toT∞`, D311) — and `S⇔Same` shows the
-- two agree: the observation is monotone in the depth (`Obs-mono`), so a
-- relation at every finite depth is one at every node (`N→≈∞`).
--
-- Also: the tree lemmas the proof composes (bisimilarity is preserved by
-- bind, mapping and `toT∞`), stated over the graded monad `M π`.
------------------------------------------------------------------------

module Once.Metatheory.Coherence.Relation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Type.Grade using (Purity; pure; eff⁺; eff; prod; mk-kind; Zero; One; Many; _·p_)
open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; rigid)
open import Once.Spec.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-prod; ⊑-pp; ⊑-ep; ⊑-g; ⊑-ge; ⊑-gp)
open import Once.Spec.Guarded using (T⁺; forget⁺; _>>=⁺_; _⁺=<<_; fmap⁺)
open import Once.Denotation.GuardedLaws using (forget-bind⁺; forget-⁺bind)
open import Once.Spec.Equivalence using (TreeEq; ret≈; call≈; halt≈; Obs; Same; TreeEqN; LayerEq; νᵖ-upto; νᵈ-upto; ν∞-upto; ν⁺-upto)
open import Once.Spec.Polynomial using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF)
open import Once.Spec.Graded using (⟦_⟧ᵛ; M; toT∞; bindM; returnM; subM; bindᵍ)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β)
open import Once.Spec.Trace using (T; ret; call; halt; _>>=T_; fmapT; returnT)
open import Once.Spec.Iterative
  using (T∞; T∞F; ret∞; call∞; halt∞; return∞; _>>=∞_; embed; TreeEq∞; NodeEq; ret≈∞; call≈∞; halt≈∞)
open Once.Spec.Iterative.T∞ using (force)
open Once.Spec.Iterative.TreeEq∞ using (force≈)
open Once.Spec.Iterative.ν∞ using (force∞)
open import Once.Denotation.TraceMonadInfLaws using (≈∞-refl; ≈∞-reflF; ≈∞-rewrite; ≈∞-map; ≈∞-mapF; ≈∞-bind; embed-bind; ≈∞-idˡ)
open import Once.Spec.Graded using (_>>=ᵖ_)

------------------------------------------------------------------------
-- Trees
------------------------------------------------------------------------

TreeEq-map : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
           → ∀ {m m′} → TreeEq R m m′ → TreeEq R′ m m′
TreeEq-map f (ret≈ r)  = ret≈ (f r)
TreeEq-map f (call≈ k) = call≈ (λ b → TreeEq-map f (k b))
TreeEq-map f halt≈     = halt≈

TreeEq-bind : ∀ {X Y} {R : X → X → Set} {R′ : Y → Y → Set} {m m′ : T X} {k k′ : X → T Y}
            → TreeEq R m m′ → (∀ {x y} → R x y → TreeEq R′ (k x) (k′ y))
            → TreeEq R′ (m >>=T k) (m′ >>=T k′)
TreeEq-bind (ret≈ r)  h = h r
TreeEq-bind (call≈ k) h = call≈ (λ b → TreeEq-bind (k b) h)
TreeEq-bind halt≈     h = halt≈

-- Every depth, outside, is every depth, inside: `T` is inductive. By
-- recursion on the depth-0 relation, which fixes the two trees' shape.
private
  un-ret : ∀ {X} {R : X → X → Set} {x y} → TreeEq R (ret x) (ret y) → R x y
  un-ret (ret≈ r) = r

  un-call : ∀ {X} {R : X → X → Set} {o a k k′} → TreeEq R (call o a k) (call o a k′) → ∀ b → TreeEq R (k b) (k′ b)
  un-call (call≈ f) = f

  go : ∀ {X} {R : ℕ → X → X → Set} {m m′ : T X}
     → TreeEq (R zero) m m′ → (∀ n → TreeEq (R n) m m′) → TreeEq (λ x y → ∀ n → R n x y) m m′
  go (ret≈ _)  h = ret≈ (λ n → un-ret (h n))
  go (call≈ f) h = call≈ (λ b → go (f b) (λ n → un-call (h n) b))
  go halt≈     h = halt≈

∀-TreeEq : ∀ {X} {R : ℕ → X → X → Set} (m m′ : T X)
         → (∀ n → TreeEq (R n) m m′) → TreeEq (λ x y → ∀ n → R n x y) m m′
∀-TreeEq m m′ h = go (h zero) h

-- …and back.
TreeEq-∀ : ∀ {X} {R : ℕ → X → X → Set} {m m′ : T X}
         → TreeEq (λ x y → ∀ n → R n x y) m m′ → ∀ n → TreeEq (R n) m m′
TreeEq-∀ h n = TreeEq-map (λ r → r n) h

------------------------------------------------------------------------
-- Trees of the completely iterative monad
------------------------------------------------------------------------

-- A tree bisimilar to itself.
≈refl : ∀ {X} (m : T∞ X) → TreeEq∞ _≡_ m m
≈refl = ≈∞-refl (λ _ → refl)

-- A leaf, related.
retT≈ : ∀ {X} {R : X → X → Set} {x y} → R x y → TreeEq∞ R (return∞ x) (return∞ y)
force≈ (retT≈ r) = ret≈∞ r

private
  ≡→≈ : ∀ {X} {m m′ : T∞ X} → m ≡ m′ → TreeEq∞ _≡_ m m′
  ≡→≈ {m = m} refl = ≈refl m

  ret-≈ : ∀ {X} (x : X) → TreeEq∞ _≡_ (embed (returnT x)) (return∞ x)
  force≈ (ret-≈ x) = ret≈∞ refl

  retβ-≈ : ∀ {X Y} (m : X) (k : X → Y) → TreeEq∞ _≡_ (return∞ (m >>=ᵖ k)) (return∞ m >>=∞ λ x → return∞ (k x))
  force≈ (retβ-≈ m k) = ret≈∞ (>>=ᵖ-β m k)

------------------------------------------------------------------------
-- The graded monad, seen as trees of `T∞`
------------------------------------------------------------------------

toT∞-bindM : ∀ π {X Y} (m : M π X) (k : X → M π Y)
           → TreeEq∞ _≡_ (toT∞ π (bindM π m k)) (toT∞ π m >>=∞ λ x → toT∞ π (k x))
toT∞-bindM pure m k = retβ-≈ m k
toT∞-bindM eff⁺ m k =
  ≈∞-rewrite (≡→≈ (cong embed (forget-bind⁺ m (λ x → forget⁺ (k x))))) (≈refl _)
             (embed-bind (forget⁺ m) (λ x → forget⁺ (k x)))
toT∞-bindM eff  m k = embed-bind m k
toT∞-bindM prod m k = ≈refl (m >>=∞ k)

-- The graded bind (D311) erases to `T∞`'s.
toT∞-bindᵍ : ∀ π₁ π₂ {X Y} (m : M π₁ X) (k : X → M π₂ Y)
           → TreeEq∞ _≡_ (toT∞ (π₁ ·p π₂) (bindᵍ π₁ π₂ m k)) (toT∞ π₁ m >>=∞ λ x → toT∞ π₂ (k x))
toT∞-bindᵍ pure π₂ m k =
  ≈∞-rewrite (≡→≈ (cong (toT∞ π₂) (>>=ᵖ-β m k))) (≈∞-idˡ m (λ x → toT∞ π₂ (k x))) (≈refl (toT∞ π₂ (k m)))
toT∞-bindᵍ eff⁺ pure m k =
  ≈∞-rewrite (≡→≈ (cong embed (forget-bind⁺ m (λ x → returnT (k x))))) (≈refl _)
             (≈∞-rewrite (embed-bind (forget⁺ m) (λ x → returnT (k x))) (≈refl _)
                         (≈∞-bind {R = _≡_} (≈refl (embed (forget⁺ m))) λ { refl → ret-≈ _ }))
toT∞-bindᵍ eff⁺ eff⁺ m k =
  ≈∞-rewrite (≡→≈ (cong embed (forget-bind⁺ m (λ x → forget⁺ (k x))))) (≈refl _)
             (embed-bind (forget⁺ m) (λ x → forget⁺ (k x)))
toT∞-bindᵍ eff⁺ eff  m k =
  ≈∞-rewrite (≡→≈ (cong embed (forget-bind⁺ m k))) (≈refl _) (embed-bind (forget⁺ m) k)
toT∞-bindᵍ eff⁺ prod m k = ≈refl (embed (forget⁺ m) >>=∞ k)
toT∞-bindᵍ eff eff⁺ m k =
  ≈∞-rewrite (≡→≈ (cong embed (forget-⁺bind m k))) (≈refl _) (embed-bind m (λ x → forget⁺ (k x)))
toT∞-bindᵍ eff pure m k =
  ≈∞-rewrite (embed-bind m (λ x → returnT (k x))) (≈refl _)
             (≈∞-bind {R = _≡_} (≈refl (embed m)) λ { refl → ret-≈ _ })
toT∞-bindᵍ eff eff  m k = embed-bind m k
toT∞-bindᵍ eff prod m k = ≈refl (embed m >>=∞ k)
toT∞-bindᵍ prod π₂  m k = ≈refl (m >>=∞ λ x → toT∞ π₂ (k x))

toT∞-returnM : ∀ {π} (u : pure ⊑π π) {X} (x : X) → TreeEq∞ _≡_ (toT∞ π (returnM u x)) (return∞ x)
toT∞-returnM ⊑-pure x = ≈refl (return∞ x)
toT∞-returnM ⊑-pe   x = ret-≈ x
toT∞-returnM ⊑-pp   x = ≈refl (return∞ x)

-- `⊢sub-eff` is invisible as a tree: the unit embeds a value as a leaf, and a
-- finite tree is itself in `T∞`.
toT∞-subM : ∀ {π π′} (g : π ⊑π π′) {X} (m : M π X) → TreeEq∞ _≡_ (toT∞ π′ (subM g m)) (toT∞ π m)
toT∞-subM ⊑-pure m = ≈refl (return∞ m)
toT∞-subM ⊑-eff  m = ≈refl (embed m)
toT∞-subM ⊑-pe   m = ret-≈ m
toT∞-subM ⊑-prod m = ≈refl m
toT∞-subM ⊑-pp   m = ≈refl (return∞ m)
toT∞-subM ⊑-ep   m = ≈refl (embed m)
toT∞-subM ⊑-g    m = ≈refl (embed (forget⁺ m))
toT∞-subM ⊑-ge   m = ≈refl (embed (forget⁺ m))
toT∞-subM ⊑-gp   m = ≈refl (embed (forget⁺ m))

------------------------------------------------------------------------
-- Depth: a relation to every finite depth is one at every node
------------------------------------------------------------------------

-- Map the leaves, at one depth.
TreeEqN-map : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
            → ∀ n {m m′ : T∞ X} → TreeEqN n R m m′ → TreeEqN n R′ m m′
TreeEqN-mapF : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
             → ∀ n {l l′ : T∞F X (T∞ X)} → NodeEq R (TreeEqN n R) l l′ → NodeEq R′ (TreeEqN n R′) l l′
TreeEqN-map f zero    h = tt
TreeEqN-map f (suc n) h = TreeEqN-mapF f n h
TreeEqN-mapF f n (ret≈∞ r)  = ret≈∞ (f r)
TreeEqN-mapF f n (call≈∞ g) = call≈∞ (λ b → TreeEqN-map f n (g b))
TreeEqN-mapF f n halt≈∞     = halt≈∞

-- One node less, with the leaves' relation weakened.
TreeEqN-mono : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
             → ∀ n {m m′ : T∞ X} → TreeEqN (suc n) R m m′ → TreeEqN n R′ m m′
TreeEqN-monoF : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
              → ∀ n {l l′ : T∞F X (T∞ X)} → NodeEq R (TreeEqN (suc n) R) l l′ → NodeEq R′ (TreeEqN n R′) l l′
TreeEqN-mono f zero    h = tt
TreeEqN-mono f (suc n) h = TreeEqN-monoF f n h
TreeEqN-monoF f n (ret≈∞ r)  = ret≈∞ (f r)
TreeEqN-monoF f n (call≈∞ g) = call≈∞ (λ b → TreeEqN-mono f n (g b))
TreeEqN-monoF f n halt≈∞     = halt≈∞

-- A bisimilarity is a relation to every depth.
≈∞→N : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
     → ∀ {m m′ : T∞ X} → TreeEq∞ R m m′ → ∀ n → TreeEqN n R′ m m′
≈∞→NF : ∀ {X} {R R′ : X → X → Set} → (∀ {x y} → R x y → R′ x y)
      → ∀ {l l′ : T∞F X (T∞ X)} → NodeEq R (TreeEq∞ R) l l′ → ∀ n → NodeEq R′ (TreeEqN n R′) l l′
≈∞→N f h zero    = tt
≈∞→N f h (suc n) = ≈∞→NF f (force≈ h) n
≈∞→NF f (ret≈∞ r)  n = ret≈∞ (f r)
≈∞→NF f (call≈∞ g) n = call≈∞ (λ b → ≈∞→N f (g b) n)
≈∞→NF f halt≈∞     n = halt≈∞

-- And back: a relation family monotone in the depth, holding to every
-- depth, holds at every node, with every depth's relation at the leaves.
module Depth {X : Set} (R : ℕ → X → X → Set) (mono : ∀ {n x y} → R (suc n) x y → R n x y) where
  R∀ : X → X → Set
  R∀ x y = ∀ n → R n x y

  private
    Hyp : T∞F X (T∞ X) → T∞F X (T∞ X) → Set
    Hyp l l′ = ∀ n → NodeEq (R (suc n)) (TreeEqN n (R (suc n))) l l′

    leafR : ∀ {j} {Q : T∞ X → T∞ X → Set} {x y} → NodeEq (R (suc j)) Q (ret∞ x) (ret∞ y) → R (suc j) x y
    leafR (ret≈∞ r) = r

  N→≈∞ : ∀ {m m′ : T∞ X} → (∀ n → TreeEqN n (R n) m m′) → TreeEq∞ R∀ m m′
  N→≈F : ∀ (l l′ : T∞F X (T∞ X)) → Hyp l l′ → NodeEq R∀ (TreeEq∞ R∀) l l′
  callH : ∀ {o a k o′ a′ k′} → NodeEq (R 1) (TreeEqN 0 (R 1)) (call∞ o a k) (call∞ o′ a′ k′)
        → Hyp (call∞ o a k) (call∞ o′ a′ k′) → NodeEq R∀ (TreeEq∞ R∀) (call∞ o a k) (call∞ o′ a′ k′)
  haltH : ∀ {o a o′ a′} → NodeEq (R 1) (TreeEqN 0 (R 1)) (halt∞ {R = T∞ X} o a) (halt∞ o′ a′)
        → NodeEq R∀ (TreeEq∞ R∀) (halt∞ o a) (halt∞ o′ a′)
  force≈ (N→≈∞ {m} {m′} h) = N→≈F (force m) (force m′) (λ n → h (suc n))
  N→≈F (ret∞ x)      (ret∞ y)        h = ret≈∞ (λ n → mono (leafR (h n)))
  N→≈F (call∞ o a k) (call∞ o′ a′ k′) h = callH (h 0) h
  N→≈F (halt∞ o a)   (halt∞ o′ a′)    h = haltH (h 0)
  N→≈F (ret∞ x)      (call∞ o a k)    h with h 0
  ... | ()
  N→≈F (ret∞ x)      (halt∞ o a)      h with h 0
  ... | ()
  N→≈F (call∞ o a k) (ret∞ x)         h with h 0
  ... | ()
  N→≈F (call∞ o a k) (halt∞ o′ a′)    h with h 0
  ... | ()
  N→≈F (halt∞ o a)   (ret∞ x)         h with h 0
  ... | ()
  N→≈F (halt∞ o a)   (call∞ o′ a′ k)  h with h 0
  ... | ()
  callH {k = k} {k′ = k′} (call≈∞ _) h = call≈∞ (λ b → N→≈∞ (λ n → kids n b))
    where
      kids : ∀ n b → TreeEqN n (R n) (k b) (k′ b)
      kids zero    b = tt
      kids (suc j) b = TreeEqN-map mono (suc j) {k b} {k′ b} (child (h (suc j)) b)
        where child : NodeEq (R (suc (suc j))) (TreeEqN (suc j) (R (suc (suc j)))) _ _
                    → ∀ b → TreeEqN (suc j) (R (suc (suc j))) (k b) (k′ b)
              child (call≈∞ g) = g
  haltH halt≈∞ = halt≈∞

------------------------------------------------------------------------
-- The relation
------------------------------------------------------------------------

S : (A : Type) → ⟦ A ⟧ᵛ → ⟦ A ⟧ᵛ → Set
S Unit        _ _ = ⊤
S Void        _ _ = ⊤
S Int         x y = x ≡ y
S Float       x y = x ≡ y
S (μ-type F)  x y = x ≡ y
S (rigid _ _) _ _ = ⊤
S (A * B) (a , b) (a′ , b′) = S A a a′ × S B b b′
S (A + B) (inj₁ a) (inj₁ a′) = S A a a′
S (A + B) (inj₂ b) (inj₂ b′) = S B b b′
S (A + B) (inj₁ _) (inj₂ _)  = ⊥
S (A + B) (inj₂ _) (inj₁ _)  = ⊥
S (A ⇒[ mk-kind Zero π ] B) f g = TreeEq∞ (S B) (toT∞ π (f tt)) (toT∞ π (g tt))
S (A ⇒[ mk-kind One  π ] B) f g = ∀ a a′ → S A a a′ → TreeEq∞ (S B) (toT∞ π (f a)) (toT∞ π (g a′))
S (A ⇒[ mk-kind Many π ] B) f g = ∀ a a′ → S A a a′ → TreeEq∞ (S B) (toT∞ π (f a)) (toT∞ π (g a′))
S (ν-type F π) v w = Same (ν-type F π) v w

-- Computations related by `S`, as trees.
SM : ∀ π (A : Type) → M π ⟦ A ⟧ᵛ → M π ⟦ A ⟧ᵛ → Set
SM π A m m′ = TreeEq∞ (S A) (toT∞ π m) (toT∞ π m′)

------------------------------------------------------------------------
-- The observation is monotone in the depth
------------------------------------------------------------------------

LayerEq-map : ∀ (G : SFunctor) {X} {R R′ : X → X → Set} → (∀ {a b} → R a b → R′ a b)
            → ∀ {x y} → LayerEq G R x y → LayerEq G R′ x y
LayerEq-map (SK B)   f e = e
LayerEq-map SId      f r = f r
LayerEq-map (G S⊕ H) f {inj₁ x} {inj₁ y} r = LayerEq-map G f r
LayerEq-map (G S⊕ H) f {inj₂ x} {inj₂ y} r = LayerEq-map H f r
LayerEq-map (G S⊕ H) f {inj₁ _} {inj₂ _} ()
LayerEq-map (G S⊕ H) f {inj₂ _} {inj₁ _} ()
LayerEq-map (G S⊗ H) f (r , r′) = LayerEq-map G f r , LayerEq-map H f r′

νᵖ-mono : ∀ (H : SFunctor) n {v w} → νᵖ-upto H (suc n) v w → νᵖ-upto H n v w
νᵖ-mono H zero    h = tt
νᵖ-mono H (suc n) h = LayerEq-map H (νᵖ-mono H n) h

νᵈ-mono : ∀ (H : SFunctor) n {v w} → νᵈ-upto H (suc n) v w → νᵈ-upto H n v w
νᵈ-mono H zero    h = tt
νᵈ-mono H (suc n) h = TreeEq-map (LayerEq-map H (νᵈ-mono H n)) h

ν⁺-mono : ∀ (H : SFunctor) n {v w} → ν⁺-upto H (suc n) v w → ν⁺-upto H n v w
ν⁺-mono H zero    h = tt
ν⁺-mono H (suc n) h = TreeEq-map (LayerEq-map H (ν⁺-mono H n)) h

ν∞-mono : ∀ (H : SFunctor) n {v w} → ν∞-upto H (suc n) v w → ν∞-upto H n v w
ν∞-mono H zero    h = tt
ν∞-mono H (suc n) {v} {w} h = TreeEqN-mono (LayerEq-map H (ν∞-mono H n)) (suc n) {force∞ v} {force∞ w} h

Obs-mono : ∀ n (A : Type) {x y} → Obs (suc n) A x y → Obs n A x y
Obs-mono n Unit        h = tt
Obs-mono n Void        h = tt
Obs-mono n Int         h = h
Obs-mono n Float       h = h
Obs-mono n (μ-type F)  h = h
Obs-mono n (rigid _ _) h = tt
Obs-mono n (A * B) {a , b} {a′ , b′} (ha , hb) = Obs-mono n A ha , Obs-mono n B hb
Obs-mono n (A + B) {inj₁ a} {inj₁ a′} h = Obs-mono n A h
Obs-mono n (A + B) {inj₂ b} {inj₂ b′} h = Obs-mono n B h
Obs-mono n (A + B) {inj₁ _} {inj₂ _} ()
Obs-mono n (A + B) {inj₂ _} {inj₁ _} ()
Obs-mono n (A ⇒[ mk-kind Zero π ] B) h = TreeEqN-mono (Obs-mono n B) n h
Obs-mono n (A ⇒[ mk-kind One  π ] B) h a a′ s = TreeEqN-mono (Obs-mono n B) n (h a a′ s)
Obs-mono n (A ⇒[ mk-kind Many π ] B) h a a′ s = TreeEqN-mono (Obs-mono n B) n (h a a′ s)
Obs-mono n (ν-type F pure) h = νᵖ-mono _ n h
Obs-mono n (ν-type F eff)  h = νᵈ-mono _ n h
Obs-mono n (ν-type F prod) h = ν∞-mono _ n h
Obs-mono n (ν-type F eff⁺) h = ν⁺-mono _ n h

------------------------------------------------------------------------
-- `S` is the Spec's `Same`
------------------------------------------------------------------------

mutual
  S→Same : ∀ (A : Type) {x y} → S A x y → Same A x y
  S→Same Unit        s n = tt
  S→Same Void        s n = tt
  S→Same Int         s n = s
  S→Same Float       s n = s
  S→Same (μ-type F)  s n = s
  S→Same (rigid _ _) s n = tt
  S→Same (A * B) {a , b} {a′ , b′} (sa , sb) n = S→Same A sa n , S→Same B sb n
  S→Same (A + B) {inj₁ a} {inj₁ a′} s n = S→Same A s n
  S→Same (A + B) {inj₂ b} {inj₂ b′} s n = S→Same B s n
  S→Same (A + B) {inj₁ _} {inj₂ _} ()
  S→Same (A + B) {inj₂ _} {inj₁ _} ()
  S→Same (A ⇒[ mk-kind Zero π ] B) s n = ≈∞→N (λ r → S→Same B r n) s n
  S→Same (A ⇒[ mk-kind One  π ] B) s n a a′ h = ≈∞→N (λ r → S→Same B r n) (s a a′ (Same→S A h)) n
  S→Same (A ⇒[ mk-kind Many π ] B) s n a a′ h = ≈∞→N (λ r → S→Same B r n) (s a a′ (Same→S A h)) n
  S→Same (ν-type F π) s = s

  Same→S : ∀ (A : Type) {x y} → Same A x y → S A x y
  Same→S Unit        s = tt
  Same→S Void        s = tt
  Same→S Int         s = s zero
  Same→S Float       s = s zero
  Same→S (μ-type F)  s = s zero
  Same→S (rigid _ _) s = tt
  Same→S (A * B) {a , b} {a′ , b′} s = Same→S A (λ n → proj₁ (s n)) , Same→S B (λ n → proj₂ (s n))
  Same→S (A + B) {inj₁ a} {inj₁ a′} s = Same→S A s
  Same→S (A + B) {inj₂ b} {inj₂ b′} s = Same→S B s
  Same→S (A + B) {inj₁ _} {inj₂ _} s = s zero
  Same→S (A + B) {inj₂ _} {inj₁ _} s = s zero
  Same→S (A ⇒[ mk-kind Zero π ] B) s =
    ≈∞-map (Same→S B) (Depth.N→≈∞ (λ n → Obs n B) (λ {n} → Obs-mono n B) s)
  Same→S (A ⇒[ mk-kind One π ] B) s a a′ h =
    ≈∞-map (Same→S B) (Depth.N→≈∞ (λ n → Obs n B) (λ {n} → Obs-mono n B) (λ n → s n a a′ (S→Same A h)))
  Same→S (A ⇒[ mk-kind Many π ] B) s a a′ h =
    ≈∞-map (Same→S B) (Depth.N→≈∞ (λ n → Obs n B) (λ {n} → Obs-mono n B) (λ n → s n a a′ (S→Same A h)))
  Same→S (ν-type F π) s = s
