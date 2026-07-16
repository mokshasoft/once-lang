------------------------------------------------------------------------
-- OCP-0009 · LINEARIZATION step 2 — LINEAR RECURSION SCHEMES
--
-- "The critical-path gap" (PATHS.md): the SMCC we proved adequacy for has no
-- `μ`/`Cata`; this IR's strength is the schemes, and they do NOT all
-- linearize equally. This module makes that precise on a FREE linear category
-- with an EXPLICIT comonoid (`dup`/`drop`) and recursion (`lIn`/`lcata`):
--
--   * `LTm`       — linear morphisms: tensor `⊗l`, unitors, coproducts
--                   (additive), the comonoid `dup`/`drop`, and `lIn`/`lcata`;
--   * `DupFree`   — "uses no `dup`" (an inductive predicate with a clause for
--                   every constructor EXCEPT `dup`): the linear morphisms;
--   * `fmapL`     — the polynomial functor map, built from `⊗l`/`lcase` — no
--                   duplication (each half of a product used once);
--   * `fmapL-df`  — …and it PRESERVES `DupFree`;
--   * `cata-linear` — **`Cata` is linear**: a fold with a dup-free algebra is
--                   dup-free (consumes each constructor layer exactly once);
--   * `paraL`/`para-not-df` — **`Para` inherently duplicates**: its defining
--                   pairing `⟨In∘fmap fst, alg⟩ = (·⊗·)∘dup` contains a `dup`
--                   that no rewriting removes — `¬ DupFree (paraPairL alg)`.
--
-- So the paramorphism's access to the substructure IS a comonoid `dup` baked
-- into the scheme (cf. `NbEPDirIR.para-recon-id`, `NbEPLinFox.fox-pair-nat`):
-- Cata linearizes for free; Para's non-linearity is localized to one `dup`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPLinRec where

open import normalizer.Syntax.Types
  using ( Ty; Unit; _*_; _+_; μ_; ⟦_⟧F
        ; Func; Id; One; Kc; _⊕_; _⊗_
        ; ⊥; ¬_ )

------------------------------------------------------------------------
-- A free LINEAR category: symmetric monoidal (⊗l over the object product
-- `*`) + additive coproducts + an explicit comonoid + initial-algebra cata.
------------------------------------------------------------------------

infixr 9 _∘l_
infixr 7 _⊗l_

data LTm : Ty → Ty → Set where
  lid   : ∀ {A} → LTm A A
  _∘l_  : ∀ {A B C} → LTm B C → LTm A B → LTm A C
  _⊗l_  : ∀ {A B C D} → LTm A B → LTm C D → LTm (A * C) (B * D)
  -- unitors (the ones the recovered projections land on)
  ρl    : ∀ {A} → LTm (A * Unit) A
  ρl⁻   : ∀ {A} → LTm A (A * Unit)
  lul   : ∀ {A} → LTm (Unit * A) A
  lul⁻  : ∀ {A} → LTm A (Unit * A)
  -- the comonoid — the ONLY sources of duplication / discard
  dup   : ∀ {A} → LTm A (A * A)
  drop  : ∀ {A} → LTm A Unit
  -- additive coproducts (needed for the ⊕ functors)
  linl  : ∀ {A B} → LTm A (A + B)
  linr  : ∀ {A B} → LTm B (A + B)
  lcase : ∀ {A B C} → LTm A C → LTm B C → LTm (A + B) C
  -- initial algebra
  lIn   : ∀ {F} → LTm (⟦ F ⟧F (μ F)) (μ F)
  lcata : ∀ F {A} → LTm (⟦ F ⟧F A) A → LTm (μ F) A

------------------------------------------------------------------------
-- The recovered cartesian operations (Fox layer, `NbEPLinFox` concretely).
------------------------------------------------------------------------

fstL : ∀ {A B} → LTm (A * B) A
fstL = ρl ∘l (lid ⊗l drop)

sndL : ∀ {A B} → LTm (A * B) B
sndL = lul ∘l (drop ⊗l lid)

⟨_,_⟩L : ∀ {C A B} → LTm C A → LTm C B → LTm C (A * B)
⟨ f , g ⟩L = (f ⊗l g) ∘l dup

------------------------------------------------------------------------
-- The polynomial functor map — dup-free by construction.
------------------------------------------------------------------------

fmapL : ∀ F {A B} → LTm A B → LTm (⟦ F ⟧F A) (⟦ F ⟧F B)
fmapL Id      f = f
fmapL One     _ = lid
fmapL (Kc _)  _ = lid
fmapL (F ⊕ G) f = lcase (linl ∘l fmapL F f) (linr ∘l fmapL G f)
fmapL (F ⊗ G) f = fmapL F f ⊗l fmapL G f

------------------------------------------------------------------------
-- Linearity = "uses no `dup`". Every constructor has a clause EXCEPT `dup`.
------------------------------------------------------------------------

data DupFree : ∀ {A B} → LTm A B → Set where
  df-id   : ∀ {A} → DupFree (lid {A})
  df-∘    : ∀ {A B C} {f : LTm B C} {g : LTm A B} →
            DupFree f → DupFree g → DupFree (f ∘l g)
  df-⊗    : ∀ {A B C D} {f : LTm A B} {g : LTm C D} →
            DupFree f → DupFree g → DupFree (f ⊗l g)
  df-ρl   : ∀ {A} → DupFree (ρl {A})
  df-ρl⁻  : ∀ {A} → DupFree (ρl⁻ {A})
  df-lul  : ∀ {A} → DupFree (lul {A})
  df-lul⁻ : ∀ {A} → DupFree (lul⁻ {A})
  df-drop : ∀ {A} → DupFree (drop {A})
  df-linl : ∀ {A B} → DupFree (linl {A} {B})
  df-linr : ∀ {A B} → DupFree (linr {A} {B})
  df-case : ∀ {A B C} {f : LTm A C} {g : LTm B C} →
            DupFree f → DupFree g → DupFree (lcase f g)
  df-In   : ∀ {F} → DupFree (lIn {F})
  df-cata : ∀ F {A} {alg : LTm (⟦ F ⟧F A) A} →
            DupFree alg → DupFree (lcata F alg)
  -- (no `df-dup`: `dup` is the one non-linear generator)

-- `dup` is not dup-free (there is no constructor for it).
dup-not-df : ∀ {A} → ¬ DupFree (dup {A})
dup-not-df ()

------------------------------------------------------------------------
-- `fmap` is linear, and `Cata` preserves linearity.
------------------------------------------------------------------------

fmapL-df : ∀ F {A B} {f : LTm A B} → DupFree f → DupFree (fmapL F f)
fmapL-df Id      df = df
fmapL-df One     df = df-id
fmapL-df (Kc _)  df = df-id
fmapL-df (F ⊕ G) df =
  df-case (df-∘ df-linl (fmapL-df F df)) (df-∘ df-linr (fmapL-df G df))
fmapL-df (F ⊗ G) df = df-⊗ (fmapL-df F df) (fmapL-df G df)

-- Cata is LINEAR: a fold with a dup-free algebra stays dup-free.
cata-linear : ∀ F {A} {alg : LTm (⟦ F ⟧F A) A} →
              DupFree alg → DupFree (lcata F alg)
cata-linear F = df-cata F

------------------------------------------------------------------------
-- Para INHERENTLY duplicates. The recovered pairing carries a `dup`, and no
-- dup-free derivation of it exists — the non-linearity is essential.
------------------------------------------------------------------------

paraPairL : ∀ {F A} → LTm (⟦ F ⟧F (μ F * A)) A → LTm (μ F) (μ F * A)
paraPairL {F} alg = lcata F ⟨ lIn ∘l fmapL F fstL , alg ⟩L

paraL : ∀ {F A} → LTm (⟦ F ⟧F (μ F * A)) A → LTm (μ F) A
paraL alg = sndL ∘l paraPairL alg

-- The pairing cannot be linear: it reduces to a `dup`.
pair-not-df : ∀ {C A B} {f : LTm C A} {g : LTm C B} → ¬ DupFree (⟨ f , g ⟩L)
pair-not-df (df-∘ _ df-dup) = dup-not-df df-dup

-- Hence neither the paramorphism's pairing nor the paramorphism itself is
-- linear: `Para` bakes in exactly one comonoid `dup`.
paraPair-not-df : ∀ {F A} (alg : LTm (⟦ F ⟧F (μ F * A)) A) →
                  ¬ DupFree (paraPairL alg)
paraPair-not-df alg (df-cata _ dfp) = pair-not-df dfp

para-not-df : ∀ {F A} (alg : LTm (⟦ F ⟧F (μ F * A)) A) → ¬ DupFree (paraL alg)
para-not-df alg (df-∘ _ dfpp) = paraPair-not-df alg dfpp
