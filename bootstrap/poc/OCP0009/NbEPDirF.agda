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
  using ( Ty; Func; Id; One; Kc; _⊕_; _⊗_; ⟦_⟧F
        ; _⊎_; inj₁; inj₂; _×_; _,_
        ; _≡_; refl; trans; cong; cong₂ )
open import normalizer.Syntax.CCC as C
  using ( Term; _∘_; cata; fmap )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; ⟦_⟧FS; Fix; fix; fmap-Set; cata-Set; map-cata-Set
        ; eval; coherence; coherence⁻¹ )

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

------------------------------------------------------------------------
-- Lifting fusion to Once IR programs, through the evaluator.
--
-- `eval (cata F alg) = cata-Set F (eval alg ∘ coherence⁻¹)` and
-- `eval (f ∘ g) = eval f ∘ eval g` (definitional), so the Set-level fusion
-- above applies verbatim to IR-fold DENOTATIONS. The only glue is the
-- coherence round-trip and `eval`-commutes-with-`fmap` (re-derived here,
-- since `EvalSound` is stale against the current `Func`).
------------------------------------------------------------------------

-- coherence ∘ coherence⁻¹ ≡ id.
coh-rt : ∀ F {A} (z : ⟦ F ⟧FS ⟦ A ⟧T) → coherence F A (coherence⁻¹ F A z) ≡ z
coh-rt Id      z        = refl
coh-rt One     z        = refl
coh-rt (Kc G)  z        = refl
coh-rt (F ⊕ G) (inj₁ x) = cong inj₁ (coh-rt F x)
coh-rt (F ⊕ G) (inj₂ y) = cong inj₂ (coh-rt G y)
coh-rt (F ⊗ G) (x , y)  = cong₂ _,_ (coh-rt F x) (coh-rt G y)

-- eval commutes with fmap, through coherence.
eval-fmap : ∀ F {A B} (h : Term A B) (z : ⟦ ⟦ F ⟧F A ⟧T) →
            eval (fmap F h) z ≡
            coherence⁻¹ F B (fmap-Set F (eval h) (coherence F A z))
eval-fmap Id      h z        = refl
eval-fmap One     h z        = refl
eval-fmap (Kc G)  h z        = refl
eval-fmap (F ⊕ G) h (inj₁ x) = cong inj₁ (eval-fmap F h x)
eval-fmap (F ⊕ G) h (inj₂ y) = cong inj₂ (eval-fmap G h y)
eval-fmap (F ⊗ G) h (x , y)  = cong₂ _,_ (eval-fmap F h x) (eval-fmap G h y)

-- Fold fusion for IR programs: if `h ∘ alg` and `alg' ∘ fmap h` denote the
-- same function, then so do `h ∘ cata alg` and `cata alg'`.
fusion-eval : ∀ F {A B : Ty} (h : Term A B)
              (alg : Term (⟦ F ⟧F A) A) (alg' : Term (⟦ F ⟧F B) B) →
              (∀ x → eval (h ∘ alg) x ≡ eval (alg' ∘ fmap F h) x) →
              ∀ y → eval (h ∘ cata F alg) y ≡ eval (cata F alg') y
fusion-eval F {A} {B} h alg alg' cond =
  cata-fuse F (eval h)
    (λ z → eval alg  (coherence⁻¹ F A z))
    (λ z → eval alg' (coherence⁻¹ F B z))
    cond°
  where
  cond° : ∀ z → eval h (eval alg (coherence⁻¹ F A z))
              ≡ eval alg' (coherence⁻¹ F B (fmap-Set F (eval h) z))
  cond° z = trans (cond (coherence⁻¹ F A z)) (cong (eval alg') glue)
    where
    glue : eval (fmap F h) (coherence⁻¹ F A z)
         ≡ coherence⁻¹ F B (fmap-Set F (eval h) z)
    glue = trans (eval-fmap F h (coherence⁻¹ F A z))
                 (cong (λ w → coherence⁻¹ F B (fmap-Set F (eval h) w))
                       (coh-rt F z))
