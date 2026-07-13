------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3B — REPRESENTATION UNIQUENESS
--
-- The insertion representation of a permutation is CANONICAL: two `Perm`s
-- with the same action are the same term —
--
--   applyP-inj : IsL xs → (p q : Perm xs ys) →
--                (∀ l → applyP p l ≡ applyP q l) → p ≡ q
--
-- This is the hinge of completeness: once the key lemma (stage 3E) puts
-- every morphism in the form `topn ∘ permM (pOf f) ∘ ntop`, equal wirings
-- force equal `Perm`s — hence literally identical canonical morphisms.
--
-- Method: probe with distinguished leaves.
--   * `insPos lx i` — where the inserted head landed; pulling it back
--     yields the head (`applyP-headval`), and `goL`-preimages are UNIQUE
--     (`goL-pre`), so equal actions force equal insertion positions;
--   * `insPos-inj` — equal positions force equal insertions, INCLUDING
--     the a-priori-different middle types (index unification collapses
--     them at `here`/`here`; `goR`-injectivity recurses the rest);
--   * `skipIns i` — embeds tail positions past the insertion; pulling
--     back gives `goR` (`applyP-tailval`), so the tails' actions agree
--     pointwise and induction closes.
--
-- The `IsL` hypothesis supplies the one thing raw `Perm`s lack: heads are
-- LEAF types, hence inhabited, hence probeable. (For an `I`-insertion the
-- action genuinely underdetermines the representation — uniqueness is a
-- theorem about list shapes, and stage 1 certified our normal forms are
-- exactly those.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonU where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; sym; trans; cong
        ; Reveal_·_is_; ⟪_⟫; inspect )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( Leaf; ℓ₁; ℓ₂; goL; goR; goL-inj; goR-inj )
open import poc.OCP0009.NbEPMonP
  using ( Lf; lf₁; lf₂; IsL; lnil; lcons
        ; Ins; here; there; Perm; pnil; pcons
        ; applyI; applyP )

lfLeaf : ∀ {x} → Lf x → Leaf x
lfLeaf lf₁ = ℓ₁
lfLeaf lf₂ = ℓ₂

subst-Ins : ∀ {x ys ys' zs} → ys ≡ ys' → Ins x ys zs → Ins x ys' zs
subst-Ins refl i = i

------------------------------------------------------------------------
-- Distinguished probes.
------------------------------------------------------------------------

insPos : ∀ {x ys zs} → Leaf x → Ins x ys zs → Leaf zs
insPos lx here      = goL lx
insPos lx (there i) = goR (insPos lx i)

skipIns : ∀ {x ys zs} → Ins x ys zs → Leaf ys → Leaf zs
skipIns here      l        = goR l
skipIns (there i) (goL ly) = goL ly
skipIns (there i) (goR l)  = goR (skipIns i l)

------------------------------------------------------------------------
-- Pulling the probes back through an insertion.
------------------------------------------------------------------------

applyI-insPos : ∀ {x ys zs} (lx : Leaf x) (i : Ins x ys zs) →
                applyI i (insPos lx i) ≡ goL lx
applyI-insPos lx here      = refl
applyI-insPos lx (there i)
  with applyI i (insPos lx i) | applyI-insPos lx i
... | goL lx' | eq = cong goL (goL-inj eq)
... | goR _   | ()

applyI-skip : ∀ {x ys zs} (i : Ins x ys zs) (l : Leaf ys) →
              applyI i (skipIns i l) ≡ goR l
applyI-skip here      l        = refl
applyI-skip (there i) (goL ly) = refl
applyI-skip (there i) (goR l)
  with applyI i (skipIns i l) | applyI-skip i l
... | goL _  | ()
... | goR l' | eq = cong (λ z → goR (goR z)) (goR-inj eq)

------------------------------------------------------------------------
-- `goL`-preimages are unique.
------------------------------------------------------------------------

goL-pre : ∀ {x ys zs} (i : Ins x ys zs) (l : Leaf zs) {lx : Leaf x} →
          applyI i l ≡ goL lx → l ≡ insPos lx i
goL-pre here      l        eq = eq
goL-pre (there i) (goL ly) ()
goL-pre (there i) (goR l)  eq
  with applyI i l | inspect (applyI i) l
goL-pre (there i) (goR l) eq | goL lx' | ⟪ w ⟫ =
  cong goR (goL-pre i l (trans w (cong goL (goL-inj eq))))
goL-pre (there i) (goR l) () | goR _   | ⟪ _ ⟫

------------------------------------------------------------------------
-- Equal positions force equal insertions — middle types included.
------------------------------------------------------------------------

insPos-inj : ∀ {x ys ys' zs} (lx : Leaf x)
             (i : Ins x ys zs) (j : Ins x ys' zs) →
             insPos lx i ≡ insPos lx j →
             Σ (ys ≡ ys') (λ e → subst-Ins e i ≡ j)
insPos-inj lx here      here      eq = refl , refl
insPos-inj lx here      (there j) ()
insPos-inj lx (there i) here      ()
insPos-inj lx (there i) (there j) eq
  with insPos-inj lx i j (goR-inj eq)
... | refl , refl = refl , refl

------------------------------------------------------------------------
-- The head and tail values of `applyP (pcons p i)` at the probes.
------------------------------------------------------------------------

applyP-headval : ∀ {x xs ys zs} (p : Perm xs ys) (i : Ins x ys zs)
                 (lx : Leaf x) →
                 applyP (pcons p i) (insPos lx i) ≡ goL lx
applyP-headval p i lx
  with applyI i (insPos lx i) | applyI-insPos lx i
... | goL lx' | eq = cong goL (goL-inj eq)
... | goR _   | ()

applyP-tailval : ∀ {x xs ys zs} (p : Perm xs ys) (i : Ins x ys zs)
                 (l : Leaf ys) →
                 applyP (pcons p i) (skipIns i l) ≡ goR (applyP p l)
applyP-tailval p i l
  with applyI i (skipIns i l) | applyI-skip i l
... | goL _  | ()
... | goR l' | eq = cong (λ z → goR (applyP p z)) (goR-inj eq)

-- If `applyP (pcons q j)` hits the head, `applyI j` already did.
applyP-goL : ∀ {x xs ys zs} (q : Perm xs ys) (j : Ins x ys zs)
             (l : Leaf zs) {lx : Leaf x} →
             applyP (pcons q j) l ≡ goL lx → applyI j l ≡ goL lx
applyP-goL q j l eq with applyI j l
applyP-goL q j l eq | goL lx' = cong goL (goL-inj eq)
applyP-goL q j l () | goR _

------------------------------------------------------------------------
-- THE THEOREM: equal actions ⇒ identical representations.
------------------------------------------------------------------------

applyP-inj : ∀ {xs ys} → IsL xs → (p q : Perm xs ys) →
             (∀ l → applyP p l ≡ applyP q l) → p ≡ q
applyP-inj lnil         pnil        pnil        h = refl
applyP-inj (lcons lx r) (pcons p i) (pcons q j) h
  with insPos-inj (lfLeaf lx) i j
         (goL-pre j (insPos (lfLeaf lx) i)
            (applyP-goL q j (insPos (lfLeaf lx) i)
               (trans (sym (h (insPos (lfLeaf lx) i)))
                      (applyP-headval p i (lfLeaf lx)))))
... | refl , refl =
  cong (λ z → pcons z i)
       (applyP-inj r p q (λ l →
          goR-inj (trans (sym (applyP-tailval p i l))
                  (trans (h (skipIns i l))
                         (applyP-tailval q i l)))))
