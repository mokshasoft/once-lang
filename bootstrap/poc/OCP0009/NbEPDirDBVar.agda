------------------------------------------------------------------------
-- OCP-0009 · W3, THE FLOOR — a VARIANCE (polarity) judgment over the real
--                             kernel syntax.
--
-- W2's eliminator (`tr`, the directed transport) cannot be stated without a
-- motive condition: transport along `p : Hom A t u` moves a family `B` over
-- `A` only if `B` is COVARIANT in the transported variable (NbEPDirJ's
-- meta-level fee, to be internalized).  This module is that condition, in
-- its cheapest honest form: a syntactic POLARITY judgment `Pos x B` /
-- `Neg x B` on the RAW kernel types, additive-only (no existing module is
-- touched; a JUDGMENT does not move the reduction side — W1g's own
-- measurement).
--
-- The ruleset is a deliberate FLOOR — sound-looking, minimal, growable:
--
--   * a family in which `x` does not occur is both `Pos` and `Neg`
--     (constant functors — this is the case ordinary non-dependent
--     transport uses, via `wk-pos` below);
--   * `El (var x)` is `Pos` — the tautological family: at `U` a path IS a
--     map, and transporting along it is applying it;
--   * `Π` flips the domain, `Σ'` is covariant in both — `NbEPDirV`'s
--     semantic content, syntactified;
--   * ★ `Hom` is CONTRAVARIANT in its first endpoint and COVARIANT in its
--     second (`pos-Hom` / `neg-Hom`).  This is the pair of rules the whole
--     eliminator story pivots on:
--       - the COMPOSITION motive `Hom A a (var x)` is `Pos`, so transport
--         derives `trans : Hom A a t → Hom A t u → Hom A a u`;
--       - the SYM motive `Hom A (var x) b` is NOT `Pos` (negative control
--         below) — it is `Neg` — so transport CANNOT derive `sym`.  And it
--         must not: `SpikeNoSym` shows `sym` is FALSE at `U`, so the
--         variance premise is guarding a semantic boundary.
--
-- ⚠ HONEST LABELS.  (i) This is RAW-syntactic polarity, not yet the typed,
-- `⊢ty`-mutual judgment the full W3 scopes (Nuyts–Devriese-shaped); the
-- refinement is open.  (ii) The rules are validated INFORMALLY against the
-- categorical semantics here; the mechanized validation is `tr`'s `fund`
-- case at consolidation, where `Pos` must produce a semantic transport
-- action.  Neither caveat affects the controls below, which are purely
-- syntactic facts.
--
-- THE SPEC THIS LICENSES (consolidation session, not this module):
--
--   ⊢tr : (Γ ▹ A) ⊢ty B → Pos vz B
--       → Γ ⊢ p ∷ Hom A t u
--       → Γ ⊢ e ∷ subTy (single t) B
--       → Γ ⊢ tr B p e ∷ subTy (single u) B
--
-- with annotation-directed, term-level reduction (the `hrefl` pattern —
-- `SpikeHomRefl` design (B)): `tr` computes on `hrefl` (the J-equation
-- `tr B (hrefl c s) e ⟶ e`), applies the map at the tautological motive
-- (`tr` at `El (var vz)` along a universe path IS application — directed
-- univalence computing a third time), and discards at constant motives.
-- Exact rule set to be settled by spike at consolidation.
--
-- ⚠ SETTLED — and the spec above is SUPERSEDED — by `SpikeTr`
-- (2026-08-01): the motive is a CODE (`tr d p e`, motive `El d`), the
-- premise is `PosC` (a strict subset of `Pos` — constant motives are
-- excluded, they never need `tr`), and the rules are PATH-KEYED, five of
-- them (unkeyed J and unkeyed taut both break raw confluence, measured
-- there; a pointwise-composition rule at `⌜Π⌝`-ambient motives is forced
-- by canonicity).  `Pos` below is untouched: it remains the semantic
-- statement; `PosC` is its computing fragment.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBVar where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; Ren; extR; renTy; renTm )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. Occurrence — a Boolean check, so concrete controls compute to `refl`.
------------------------------------------------------------------------

data 𝔹 : Set where
  true false : 𝔹

infixr 5 _∨_
_∨_ : 𝔹 → 𝔹 → 𝔹
true  ∨ _ = true
false ∨ b = b

eqv : Var Γ → Var Γ → 𝔹
eqv vz     vz     = true
eqv vz     (vs _) = false
eqv (vs _) vz     = false
eqv (vs x) (vs y) = eqv x y

occTy : Var Γ → RTy Γ → 𝔹
occTm : Var Γ → RTm Γ → 𝔹

occTy x base        = false
occTy x U           = false
occTy x (Π A B)     = occTy x A ∨ occTy (vs x) B
occTy x (Σ' A B)    = occTy x A ∨ occTy (vs x) B
occTy x (El t)      = occTm x t
occTy x (Hom A t u) = occTy x A ∨ occTm x t ∨ occTm x u

occTm x (var y)    = eqv x y
occTm x (lam t)    = occTm (vs x) t
occTm x (app t u)  = occTm x t ∨ occTm x u
occTm x (pair a b) = occTm x a ∨ occTm x b
occTm x (fst p)    = occTm x p
occTm x (snd p)    = occTm x p
occTm x ⌜base⌝     = false
occTm x (⌜Π⌝ c d)  = occTm x c ∨ occTm (vs x) d
occTm x (⌜Σ⌝ c d)  = occTm x c ∨ occTm (vs x) d

------------------------------------------------------------------------
-- 2. ★ THE POLARITY JUDGMENT.
------------------------------------------------------------------------

data Pos {Γ} : Var Γ → RTy Γ → Set
data Neg {Γ} : Var Γ → RTy Γ → Set

data Pos {Γ} where
  pos-const : {x : Var Γ} {B : RTy Γ} → occTy x B ≡ false → Pos x B
  pos-El    : {x : Var Γ} → Pos x (El (var x))
  pos-Π     : {x : Var Γ} {A : RTy Γ} {B : RTy (Γ ∙)} →
              Neg x A → Pos (vs x) B → Pos x (Π A B)
  pos-Σ     : {x : Var Γ} {A : RTy Γ} {B : RTy (Γ ∙)} →
              Pos x A → Pos (vs x) B → Pos x (Σ' A B)
  -- ★ the second endpoint of `Hom` is covariant — the COMPOSITION motive
  pos-Hom   : {x : Var Γ} {H : RTy Γ} {a : RTm Γ} →
              occTy x H ≡ false → occTm x a ≡ false →
              Pos x (Hom H a (var x))

data Neg {Γ} where
  neg-const : {x : Var Γ} {B : RTy Γ} → occTy x B ≡ false → Neg x B
  neg-Π     : {x : Var Γ} {A : RTy Γ} {B : RTy (Γ ∙)} →
              Pos x A → Neg (vs x) B → Neg x (Π A B)
  neg-Σ     : {x : Var Γ} {A : RTy Γ} {B : RTy (Γ ∙)} →
              Neg x A → Neg (vs x) B → Neg x (Σ' A B)
  -- ★ the first endpoint of `Hom` is CONTRAVARIANT — where `sym` dies
  neg-Hom   : {x : Var Γ} {H : RTy Γ} {b : RTm Γ} →
              occTy x H ≡ false → occTm x b ≡ false →
              Neg x (Hom H (var x) b)

-- deliberately ABSENT, and each absence is content:
--   * no `pos-El` beyond the bare variable — a code built by application is
--     opaque to this floor;
--   * no `Neg` counterpart of `pos-El` — the tautological family is
--     covariant only;
--   * no `Pos` for `Hom _ (var x) _` — that is `sym`'s motive.

------------------------------------------------------------------------
-- 3. Weakened families are constant — the rule ordinary transport uses.
------------------------------------------------------------------------

Avoids : Ren Γ Δ → Var Δ → Set
Avoids {Γ} ρ x = (y : Var Γ) → eqv x (ρ y) ≡ false

avoids-ext : {ρ : Ren Γ Δ} {x : Var Δ} →
             Avoids ρ x → Avoids (extR ρ) (vs x)
avoids-ext h vz     = refl
avoids-ext h (vs y) = h y

∨-false : {a b : 𝔹} → a ≡ false → b ≡ false → (a ∨ b) ≡ false
∨-false refl refl = refl

occ-ren-ty : {ρ : Ren Γ Δ} {x : Var Δ} →
             Avoids ρ x → (A : RTy Γ) → occTy x (renTy ρ A) ≡ false
occ-ren-tm : {ρ : Ren Γ Δ} {x : Var Δ} →
             Avoids ρ x → (t : RTm Γ) → occTm x (renTm ρ t) ≡ false

occ-ren-ty h base     = refl
occ-ren-ty h U        = refl
occ-ren-ty h (Π A B)  =
  ∨-false (occ-ren-ty h A) (occ-ren-ty (avoids-ext h) B)
occ-ren-ty h (Σ' A B) =
  ∨-false (occ-ren-ty h A) (occ-ren-ty (avoids-ext h) B)
occ-ren-ty h (El t)   = occ-ren-tm h t
occ-ren-ty h (Hom A t u) =
  ∨-false (occ-ren-ty h A) (∨-false (occ-ren-tm h t) (occ-ren-tm h u))

occ-ren-tm h (var y)    = h y
occ-ren-tm h (lam t)    = occ-ren-tm (avoids-ext h) t
occ-ren-tm h (app t u)  = ∨-false (occ-ren-tm h t) (occ-ren-tm h u)
occ-ren-tm h (pair a b) = ∨-false (occ-ren-tm h a) (occ-ren-tm h b)
occ-ren-tm h (fst p)    = occ-ren-tm h p
occ-ren-tm h (snd p)    = occ-ren-tm h p
occ-ren-tm h ⌜base⌝     = refl
occ-ren-tm h (⌜Π⌝ c d)  =
  ∨-false (occ-ren-tm h c) (occ-ren-tm (avoids-ext h) d)
occ-ren-tm h (⌜Σ⌝ c d)  =
  ∨-false (occ-ren-tm h c) (occ-ren-tm (avoids-ext h) d)

avoids-wk : Avoids (vs {Γ}) vz
avoids-wk y = refl

-- any weakened family is a covariant motive (and a contravariant one)
wk-pos : (B : RTy Γ) → Pos vz (renTy vs B)
wk-pos B = pos-const (occ-ren-ty avoids-wk B)

wk-neg : (B : RTy Γ) → Neg vz (renTy vs B)
wk-neg B = neg-const (occ-ren-ty avoids-wk B)

------------------------------------------------------------------------
-- 4. ★★ THE CONTROLS.
------------------------------------------------------------------------

-- POSITIVE, general: the COMPOSITION motive over any ambient `A`, `a`.
-- With `⊢tr` this is `trans : Hom A a t → Hom A t u → Hom A a u`.
comp-pos : (A : RTy Γ) (a : RTm Γ) →
           Pos vz (Hom (renTy vs A) (renTm vs a) (var vz))
comp-pos A a = pos-Hom (occ-ren-ty avoids-wk A) (occ-ren-tm avoids-wk a)

-- POSITIVE: the tautological motive — transport along a universe path is
-- application (directed univalence, again).
taut-pos : Pos (vz {Γ = Γ ∙}) (El (var vz))
taut-pos = pos-El

-- ★★★ NEGATIVE — `sym`'s motive is NOT covariant.  Concrete instance so
-- every occurrence check computes: in scope `(ε ∙) ∙`, the motive
-- `Hom base (var vz) (var (vs vz))` (transported variable in the FIRST
-- endpoint).  The only candidate rule is `pos-const` — `pos-Hom` wants the
-- variable in the SECOND endpoint, the head rules want other heads — and
-- `pos-const` is refuted by computation: the occurrence check yields `true`.
sym-motive : RTy ((ε ∙) ∙)
sym-motive = Hom base (var vz) (var (vs vz))

sym-motive-not-pos : Pos vz sym-motive → (∀ {P : Set} → P)
sym-motive-not-pos (pos-const ())

-- ...and the judgment KNOWS WHY: the motive is NEGATIVE — first endpoints
-- are contravariant.  A path `t ⟶ u` acts on `Hom _ y b` by
-- PRE-composition, against the direction of travel.
sym-motive-neg : Neg vz sym-motive
sym-motive-neg = neg-Hom refl refl

-- Π flips: a function INTO a covariant family, OUT of a constant domain,
-- is covariant — and the domain position genuinely flips (both measured
-- by the type checker accepting these).
flip-pos : Pos (vz {Γ = Γ ∙}) (Π base (El (var (vs vz))))
flip-pos = pos-Π (neg-const refl) pos-El
