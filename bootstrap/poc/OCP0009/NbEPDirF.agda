------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 4 — FOLD FUSION via semantic cata-uniqueness
--
-- `NbEPDirC` flagged fold fusion as the one recursion law NOT provable by
-- directed reduction (`⟶*`): it needs `cata`-UNIQUENESS, an induction
-- principle on `μ`. That principle lives at the SEMANTIC level — the
-- evaluator's `Fix`/`cata-Set` — and this module supplies it.
--
--   FUSION (Set semantics): if  h ∘ alg = alg' ∘ fmap h  (the fusion
--   condition), then  h ∘ cata alg = cata alg'.
--
-- Proven by induction on `Fix F`, mutually with the functor-code descent —
-- exactly mirroring the evaluator's `cata-Set`/`map-cata-Set` pair, so it
-- terminates with no pragma. This is the semantic ingredient the directed
-- `⟶*` layer cannot see: reduction gives the fold's COMPUTATION
-- (`cata-run`), the semantic model gives its UNIVERSAL PROPERTY (fusion).
-- Scope: `μ`/`Cata`/folds only — no `ana`/`Hylo`/`ν`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirF where

open import normalizer.Syntax.Types
  using ( Func; Id; One; Kc; _⊕_; _⊗_
        ; _⊎_; inj₁; inj₂; _×_; _,_
        ; _≡_; refl; trans; cong; cong₂ )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧FS; Fix; fix; fmap-Set; cata-Set; map-cata-Set )

------------------------------------------------------------------------
-- Fold fusion, by induction on the fixpoint (the uniqueness ingredient).
------------------------------------------------------------------------

mutual
  -- The fold-fusion law: a fusion condition on the algebras lifts to the
  -- folds themselves.
  cata-fuse : ∀ F {A B : Set} (h : A → B)
              (alg : ⟦ F ⟧FS A → A) (alg' : ⟦ F ⟧FS B → B) →
              (∀ z → h (alg z) ≡ alg' (fmap-Set F h z)) →
              ∀ y → h (cata-Set F alg y) ≡ cata-Set F alg' y
  cata-fuse F h alg alg' cond (fix x) =
    trans (cond (map-cata-Set F F alg x))
          (cong alg' (map-fuse F F h alg alg' cond x))

  -- The same, descended over the functor CODE (mirrors `map-cata-Set`):
  -- `fmap h` commutes with the fold's mapped recursion.
  map-fuse : ∀ F G {A B : Set} (h : A → B)
             (alg : ⟦ F ⟧FS A → A) (alg' : ⟦ F ⟧FS B → B) →
             (∀ z → h (alg z) ≡ alg' (fmap-Set F h z)) →
             ∀ x → fmap-Set G h (map-cata-Set F G alg x) ≡ map-cata-Set F G alg' x
  map-fuse F Id      h alg alg' cond x        = cata-fuse F h alg alg' cond x
  map-fuse F One     h alg alg' cond x        = refl
  map-fuse F (Kc _)  h alg alg' cond x        = refl
  map-fuse F (G ⊕ H) h alg alg' cond (inj₁ y) =
    cong inj₁ (map-fuse F G h alg alg' cond y)
  map-fuse F (G ⊕ H) h alg alg' cond (inj₂ z) =
    cong inj₂ (map-fuse F H h alg alg' cond z)
  map-fuse F (G ⊗ H) h alg alg' cond (y , z) =
    cong₂ _,_ (map-fuse F G h alg alg' cond y)
              (map-fuse F H h alg alg' cond z)

-- The headline: fold fusion.
fusion : ∀ F {A B : Set} (h : A → B)
         (alg : ⟦ F ⟧FS A → A) (alg' : ⟦ F ⟧FS B → B) →
         (∀ z → h (alg z) ≡ alg' (fmap-Set F h z)) →
         ∀ y → h (cata-Set F alg y) ≡ cata-Set F alg' y
fusion = cata-fuse
