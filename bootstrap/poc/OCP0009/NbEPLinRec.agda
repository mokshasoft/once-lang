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
  using ( Ty; Unit; _*_; _+_; _⇒_; μ_; ⟦_⟧F
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
  -- MONOIDAL CLOSURE (linearization-6).  `_*_` is the tensor here, so `lcurry`
  -- is the ⊗-curry: it SPLITS the environment (captured `A`) from the argument
  -- (`B`) instead of duplicating a shared source, and `leval` consumes the
  -- closure and its argument exactly once each.  Neither generator duplicates —
  -- see `df-lcurry`/`df-leval` below.  Every duplication a closure performs is
  -- a `dup` INSIDE its body, contributed by the source pairing it came from.
  lcurry : ∀ {A B C} → LTm (A * B) C → LTm A (B ⇒ C)
  leval  : ∀ {A B} → LTm ((A ⇒ B) * A) B

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
  -- CLOSURE: both exponential generators are linear.  `lcurry` is dup-free
  -- exactly when its body is (the closure copies nothing the body did not
  -- already copy); `leval` is dup-free outright.
  df-lcurry : ∀ {A B C} {f : LTm (A * B) C} → DupFree f → DupFree (lcurry f)
  df-leval  : ∀ {A B} → DupFree (leval {A} {B})
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

-- The recovered projections are dup-free (drop the OTHER factor — affine, not
-- duplicating): needed to place `Fuse`'s `NatTr` on the linear side.
fstL-df : ∀ {A B} → DupFree (fstL {A} {B})
fstL-df = df-∘ df-ρl (df-⊗ df-id df-drop)

sndL-df : ∀ {A B} → DupFree (sndL {A} {B})
sndL-df = df-∘ df-lul (df-⊗ df-drop df-id)

------------------------------------------------------------------------
-- FUSE and the NatTr linearity split.
--
-- `Fuse alg τ = cata (alg ∘ ⟦τ⟧)` carries a structural `NatTr` (as in
-- `NbEPDirIR`). Here the interpretation `⟦_⟧Lnt` lands in the LINEAR `LTm`,
-- and the split is exact: of the eight constructors, only `lntPair` — the one
-- mapping a source functor into a PRODUCT target — needs a `dup`. `lntFst`/
-- `lntSnd` PROJECT (drop the other half — affine), `lntInl`/`lntInr`/`lntCase`
-- reshape coproducts, `lntK`/`lntId` are point/identity. So `Fuse` is LINEAR
-- exactly when its `NatTr` avoids the diagonal `lntPair` — the linear
-- analogue of the `NatTr`-totality argument PATHS.md flagged as needed.
------------------------------------------------------------------------

data LNatTr : Func → Func → Set where
  lntId   : LNatTr Id Id
  lntK    : ∀ {G₁ G₂} → LTm (μ G₁) (μ G₂) → LNatTr (Kc G₁) (Kc G₂)
  lntFst  : ∀ {G₁ G₂ F} → LNatTr G₁ F → LNatTr (G₁ ⊗ G₂) F
  lntSnd  : ∀ {G₁ G₂ F} → LNatTr G₂ F → LNatTr (G₁ ⊗ G₂) F
  lntCase : ∀ {G₁ G₂ F} → LNatTr G₁ F → LNatTr G₂ F → LNatTr (G₁ ⊕ G₂) F
  lntInl  : ∀ {G F₁ F₂} → LNatTr G F₁ → LNatTr G (F₁ ⊕ F₂)
  lntInr  : ∀ {G F₁ F₂} → LNatTr G F₂ → LNatTr G (F₁ ⊕ F₂)
  lntPair : ∀ {G F₁ F₂} → LNatTr G F₁ → LNatTr G F₂ → LNatTr G (F₁ ⊗ F₂)

⟦_⟧Lnt : ∀ {G F} → LNatTr G F → ∀ {X} → LTm (⟦ G ⟧F X) (⟦ F ⟧F X)
⟦ lntId ⟧Lnt {X}         = lid
⟦ lntK m ⟧Lnt {X}        = m
⟦ lntFst τ ⟧Lnt {X}      = ⟦ τ ⟧Lnt {X} ∘l fstL
⟦ lntSnd τ ⟧Lnt {X}      = ⟦ τ ⟧Lnt {X} ∘l sndL
⟦ lntCase τ₁ τ₂ ⟧Lnt {X} = lcase (⟦ τ₁ ⟧Lnt {X}) (⟦ τ₂ ⟧Lnt {X})
⟦ lntInl τ ⟧Lnt {X}      = linl ∘l ⟦ τ ⟧Lnt {X}
⟦ lntInr τ ⟧Lnt {X}      = linr ∘l ⟦ τ ⟧Lnt {X}
⟦ lntPair τ₁ τ₂ ⟧Lnt {X} = ⟨ ⟦ τ₁ ⟧Lnt {X} , ⟦ τ₂ ⟧Lnt {X} ⟩L

-- The linear NatTrs: everything but the diagonal `lntPair` (and `lntK` of a
-- linear constant).
data LinearNat : ∀ {G F} → LNatTr G F → Set where
  ln-id   : LinearNat lntId
  ln-K    : ∀ {G₁ G₂} {m : LTm (μ G₁) (μ G₂)} → DupFree m → LinearNat (lntK m)
  ln-fst  : ∀ {G₁ G₂ F} {τ : LNatTr G₁ F} → LinearNat τ → LinearNat (lntFst {G₂ = G₂} τ)
  ln-snd  : ∀ {G₁ G₂ F} {τ : LNatTr G₂ F} → LinearNat τ → LinearNat (lntSnd {G₁ = G₁} τ)
  ln-case : ∀ {G₁ G₂ F} {τ₁ : LNatTr G₁ F} {τ₂ : LNatTr G₂ F} →
            LinearNat τ₁ → LinearNat τ₂ → LinearNat (lntCase τ₁ τ₂)
  ln-inl  : ∀ {G F₁ F₂} {τ : LNatTr G F₁} → LinearNat τ → LinearNat (lntInl {F₂ = F₂} τ)
  ln-inr  : ∀ {G F₁ F₂} {τ : LNatTr G F₂} → LinearNat τ → LinearNat (lntInr {F₁ = F₁} τ)
  -- (no `ln-pair`)

-- A linear NatTr interprets to a dup-free morphism (uniformly in the carrier).
natL-df : ∀ {G F} {τ : LNatTr G F} → LinearNat τ → ∀ {X} → DupFree (⟦ τ ⟧Lnt {X})
natL-df ln-id           {X} = df-id
natL-df (ln-K dm)       {X} = dm
natL-df (ln-fst ln)     {X} = df-∘ (natL-df ln {X}) fstL-df
natL-df (ln-snd ln)     {X} = df-∘ (natL-df ln {X}) sndL-df
natL-df (ln-case l₁ l₂) {X} = df-case (natL-df l₁ {X}) (natL-df l₂ {X})
natL-df (ln-inl ln)     {X} = df-∘ df-linl (natL-df ln {X})
natL-df (ln-inr ln)     {X} = df-∘ df-linr (natL-df ln {X})

fuseL : ∀ {G F B} → LNatTr G F → LTm (⟦ F ⟧F B) B → LTm (μ G) B
fuseL {G} {B = B} τ alg = lcata G (alg ∘l ⟦ τ ⟧Lnt {B})

-- Fuse is LINEAR given a linear NatTr and a linear algebra.
fuse-linear : ∀ {G F B} {τ : LNatTr G F} {alg : LTm (⟦ F ⟧F B) B} →
              LinearNat τ → DupFree alg → DupFree (fuseL τ alg)
fuse-linear {G = G} {B = B} ln dalg = df-cata G (df-∘ dalg (natL-df ln {B}))

-- …and the diagonal `lntPair` is exactly where a `Fuse` NatTr duplicates.
ntPair-dups : ∀ {G F₁ F₂} {τ₁ : LNatTr G F₁} {τ₂ : LNatTr G F₂} →
              ∀ {X} → ¬ DupFree (⟦ lntPair τ₁ τ₂ ⟧Lnt {X})
ntPair-dups {X = X} = pair-not-df
