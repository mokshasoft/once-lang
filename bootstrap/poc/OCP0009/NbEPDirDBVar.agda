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

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; ap-cong₃
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝
        ; ⌜Hom⌝-cong₃; tr-cong₃; ⌜Id⌝-cong₃; jsub-cong₃; Id-cong₃
        ; Ren; extR; renTy; renTm; Sub; extS; subTm
        ; renTm-renTm; subTm-renTm; renTm-subTm; subTm-cong )

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
occTy x (Id A t u) = occTy x A ∨ occTm x t ∨ occTm x u
occTy x Unit        = false
occTy x Nat         = false

occTm x (var y)    = eqv x y
occTm x (lam t)    = occTm (vs x) t
occTm x (app t u)  = occTm x t ∨ occTm x u
occTm x (pair a b) = occTm x a ∨ occTm x b
occTm x (fst p)    = occTm x p
occTm x (snd p)    = occTm x p
occTm x ⌜base⌝     = false
occTm x (⌜Π⌝ c d)  = occTm x c ∨ occTm (vs x) d
occTm x (⌜Σ⌝ c d)  = occTm x c ∨ occTm (vs x) d
occTm x (⌜Hom⌝ c a b) = occTm x c ∨ occTm x a ∨ occTm x b
occTm x (⌜Id⌝ c a b) = occTm x c ∨ occTm x a ∨ occTm x b
occTm x (hrefl c t)   = occTm x c ∨ occTm x t
occTm x (idrefl c t)   = occTm x c ∨ occTm x t
occTm x (tr d p e)    = occTm (vs x) d ∨ occTm x p ∨ occTm x e
occTm x (jsub d p e)    = occTm (vs x) d ∨ occTm x p ∨ occTm x e
occTm x (ap c b p)    = occTm x c ∨ occTm (vs x) b ∨ occTm x p
occTm x ⌜Nat⌝         = false
occTm x ⌜Unit⌝        = false
occTm x unit          = false
occTm x nzero         = false
occTm x (nsuc n)      = occTm x n
occTm x (natrec z s n) = occTm x z ∨ occTm (vs (vs x)) s ∨ occTm x n

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
occ-ren-ty h Unit     = refl
occ-ren-ty h Nat      = refl
occ-ren-ty h U        = refl
occ-ren-ty h (Π A B)  =
  ∨-false (occ-ren-ty h A) (occ-ren-ty (avoids-ext h) B)
occ-ren-ty h (Σ' A B) =
  ∨-false (occ-ren-ty h A) (occ-ren-ty (avoids-ext h) B)
occ-ren-ty h (El t)   = occ-ren-tm h t
occ-ren-ty h (Hom A t u) =
  ∨-false (occ-ren-ty h A) (∨-false (occ-ren-tm h t) (occ-ren-tm h u))
occ-ren-ty h (Id A t u) =
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
occ-ren-tm h (⌜Hom⌝ c a b) =
  ∨-false (occ-ren-tm h c) (∨-false (occ-ren-tm h a) (occ-ren-tm h b))
occ-ren-tm h (⌜Id⌝ c a b) =
  ∨-false (occ-ren-tm h c) (∨-false (occ-ren-tm h a) (occ-ren-tm h b))
occ-ren-tm h (hrefl c t)   = ∨-false (occ-ren-tm h c) (occ-ren-tm h t)
occ-ren-tm h (idrefl c t)   = ∨-false (occ-ren-tm h c) (occ-ren-tm h t)
occ-ren-tm h ⌜Nat⌝      = refl
occ-ren-tm h ⌜Unit⌝     = refl
occ-ren-tm h unit       = refl
occ-ren-tm h nzero      = refl
occ-ren-tm h (nsuc n)   = occ-ren-tm h n
occ-ren-tm h (natrec z s n) =
  ∨-false (occ-ren-tm h z)
          (∨-false (occ-ren-tm (avoids-ext (avoids-ext h)) s) (occ-ren-tm h n))
occ-ren-tm h (tr d p e)    =
  ∨-false (occ-ren-tm (avoids-ext h) d)
          (∨-false (occ-ren-tm h p) (occ-ren-tm h e))
occ-ren-tm h (jsub d p e)    =
  ∨-false (occ-ren-tm (avoids-ext h) d)
          (∨-false (occ-ren-tm h p) (occ-ren-tm h e))
occ-ren-tm h (ap c b p)    =
  ∨-false (occ-ren-tm h c)
          (∨-false (occ-ren-tm (avoids-ext h) b) (occ-ren-tm h p))

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

------------------------------------------------------------------------
-- 5. ★ `PosC` — THE `tr` LICENSE (SpikeTr, 2026-08-01): the fragment of
--    covariance that comes WITH a computation rule.  `Pos` above is the
--    semantic statement; `⊢tr`'s premise is this strictly smaller
--    judgment on motive CODES (`tr d p e` has motive `El d`).
--
--    Deliberately absent, each absence content (SpikeTr §8):
--      * no `posc-const` — a constant motive's action is the identity,
--        and substitution cannot even see it (`const-motive-invisible`);
--        licensing it without a rule is a canonicity hole;
--      * no `⌜Π⌝`/`⌜Σ⌝` congruence rules — covariant compound motives
--        without a computation rule are the same hole; those transports
--        are derivable pointwise per instance (the `⊢hom-id` pattern).
------------------------------------------------------------------------

data PosC {Γ} : Var Γ → RTm Γ → Set where
  posc-var : {x : Var Γ} → PosC x (var x)
  posc-Hom : {x : Var Γ} {c a : RTm Γ} →
             occTm x c ≡ false → occTm x a ≡ false →
             PosC x (⌜Hom⌝ c a (var x))

-- the composition motive is licensed over any ambient code and source —
-- with `⊢tr` this is `trans : Hom (El c) a t → Hom (El c) t u → Hom (El c) a u`
comp-posc : (c a : RTm Γ) →
            PosC vz (⌜Hom⌝ (renTm vs c) (renTm vs a) (var vz))
comp-posc c a = posc-Hom (occ-ren-tm avoids-wk c) (occ-ren-tm avoids-wk a)

-- the tautological motive is licensed — transport along a universe path
-- is application (directed univalence, computing)
taut-posc : PosC (vz {Γ = Γ ∙}) (var vz)
taut-posc = posc-var

-- ★★★ NEGATIVE — `sym`'s motive CODE, marker in the FIRST (contravariant)
-- endpoint: refuted by PATTERN alone (`posc-Hom` wants the marker in the
-- second endpoint, `posc-var` wants a bare variable).
sym-code : RTm ((ε ∙) ∙)
sym-code = ⌜Hom⌝ ⌜base⌝ (var vz) (var (vs vz))

sym-code-not-posc : PosC vz sym-code → (∀ {P : Set} → P)
sym-code-not-posc ()

-- NEGATIVE — the loop motive `⌜Hom⌝ c (var x) (var x)` (marker at BOTH
-- endpoints) fails the vz-freeness premise by computation.
loop-code-not-posc : PosC (vz {Γ = Γ ∙}) (⌜Hom⌝ ⌜base⌝ (var vz) (var vz)) →
                     (∀ {P : Set} → P)
loop-code-not-posc (posc-Hom _ ())

------------------------------------------------------------------------
-- 6. OCCURRENCE TRANSPORT — what typed renaming/substitution and `sr`
--    need to carry `PosC` through `⊢tr` (consolidation, 2026-08-01).
------------------------------------------------------------------------

∨-inl : {x y : 𝔹} → x ≡ true → (x ∨ y) ≡ true
∨-inl refl = refl

∨-inr : (x : 𝔹) {y : 𝔹} → y ≡ true → (x ∨ y) ≡ true
∨-inr true  h = refl
∨-inr false h = h

∨-false₁ : (x : 𝔹) {y : 𝔹} → (x ∨ y) ≡ false → x ≡ false
∨-false₁ false h = refl

∨-false₂ : (x : 𝔹) {y : 𝔹} → (x ∨ y) ≡ false → y ≡ false
∨-false₂ false h = h

eqv-refl : (x : Var Γ) → eqv x x ≡ true
eqv-refl vz     = refl
eqv-refl (vs x) = eqv-refl x

-- Renaming transports occurrence pointwise: if the renaming carries the
-- tracked variable exactly (`eqv x' (ρ y) ≡ eqv x y`), occurrence of the
-- image equals occurrence of the source.
ext-eq : {ρ : Ren Γ Δ} {x : Var Γ} {x' : Var Δ} →
         (∀ y → eqv x' (ρ y) ≡ eqv x y) →
         ∀ y → eqv (vs x') (extR ρ y) ≡ eqv (vs x) y
ext-eq h vz     = refl
ext-eq h (vs y) = h y

occ-ren-eq : {ρ : Ren Γ Δ} {x : Var Γ} {x' : Var Δ} →
             (∀ y → eqv x' (ρ y) ≡ eqv x y) →
             (t : RTm Γ) → occTm x' (renTm ρ t) ≡ occTm x t
occ-ren-eq h (var y)    = h y
occ-ren-eq h (lam t)    = occ-ren-eq (ext-eq h) t
occ-ren-eq h (app t u)  = cong₂ _∨_ (occ-ren-eq h t) (occ-ren-eq h u)
occ-ren-eq h (pair a b) = cong₂ _∨_ (occ-ren-eq h a) (occ-ren-eq h b)
occ-ren-eq h (fst p)    = occ-ren-eq h p
occ-ren-eq h (snd p)    = occ-ren-eq h p
occ-ren-eq h ⌜base⌝     = refl
occ-ren-eq h (⌜Π⌝ c d)  =
  cong₂ _∨_ (occ-ren-eq h c) (occ-ren-eq (ext-eq h) d)
occ-ren-eq h (⌜Σ⌝ c d)  =
  cong₂ _∨_ (occ-ren-eq h c) (occ-ren-eq (ext-eq h) d)
occ-ren-eq h (⌜Hom⌝ c a b) =
  cong₂ _∨_ (occ-ren-eq h c) (cong₂ _∨_ (occ-ren-eq h a) (occ-ren-eq h b))
occ-ren-eq h (⌜Id⌝ c a b) =
  cong₂ _∨_ (occ-ren-eq h c) (cong₂ _∨_ (occ-ren-eq h a) (occ-ren-eq h b))
occ-ren-eq h (hrefl c t)   = cong₂ _∨_ (occ-ren-eq h c) (occ-ren-eq h t)
occ-ren-eq h (idrefl c t)   = cong₂ _∨_ (occ-ren-eq h c) (occ-ren-eq h t)
occ-ren-eq h ⌜Nat⌝      = refl
occ-ren-eq h ⌜Unit⌝     = refl
occ-ren-eq h unit       = refl
occ-ren-eq h nzero      = refl
occ-ren-eq h (nsuc n)   = occ-ren-eq h n
occ-ren-eq h (natrec z s n) =
  cong₂ _∨_ (occ-ren-eq h z)
            (cong₂ _∨_ (occ-ren-eq (ext-eq (ext-eq h)) s) (occ-ren-eq h n))
occ-ren-eq h (tr d p e)    =
  cong₂ _∨_ (occ-ren-eq (ext-eq h) d)
            (cong₂ _∨_ (occ-ren-eq h p) (occ-ren-eq h e))
occ-ren-eq h (jsub d p e)    =
  cong₂ _∨_ (occ-ren-eq (ext-eq h) d)
            (cong₂ _∨_ (occ-ren-eq h p) (occ-ren-eq h e))
occ-ren-eq h (ap c b p)    =
  cong₂ _∨_ (occ-ren-eq h c)
            (cong₂ _∨_ (occ-ren-eq (ext-eq h) b) (occ-ren-eq h p))

-- Substitution KILLS occurrence: if the substitution's images avoid the
-- tracked target variable on every source variable the term can mention,
-- the result avoids it too.
ext-occ : {σ : Sub Γ Δ} {x : Var Γ} {x' : Var Δ} →
          (∀ y → eqv x y ≡ false → occTm x' (σ y) ≡ false) →
          ∀ y → eqv (vs x) y ≡ false → occTm (vs x') (extS σ y) ≡ false
ext-occ h vz     _ = refl
ext-occ {σ = σ} h (vs y) e =
  trans (occ-ren-eq (λ _ → refl) (σ y)) (h y e)

occ-sub : {σ : Sub Γ Δ} {x : Var Γ} {x' : Var Δ} →
          (∀ y → eqv x y ≡ false → occTm x' (σ y) ≡ false) →
          (t : RTm Γ) → occTm x t ≡ false → occTm x' (subTm σ t) ≡ false
occ-sub h ⌜Nat⌝      e = refl
occ-sub h ⌜Unit⌝     e = refl
occ-sub h unit       e = refl
occ-sub h nzero      e = refl
occ-sub h (nsuc n)   e = occ-sub h n e
occ-sub {x = x} h (natrec z s n) e =
  ∨-false (occ-sub h z (∨-false₁ (occTm x z) e))
          (∨-false (occ-sub (ext-occ (ext-occ h)) s
                     (∨-false₁ (occTm (vs (vs x)) s) (∨-false₂ (occTm x z) e)))
                   (occ-sub h n
                     (∨-false₂ (occTm (vs (vs x)) s) (∨-false₂ (occTm x z) e))))
occ-sub h (var y)    e = h y e
occ-sub h (lam t)    e = occ-sub (ext-occ h) t e
occ-sub {x = x} h (app t u) e =
  ∨-false (occ-sub h t (∨-false₁ (occTm x t) e))
          (occ-sub h u (∨-false₂ (occTm x t) e))
occ-sub {x = x} h (pair a b) e =
  ∨-false (occ-sub h a (∨-false₁ (occTm x a) e))
          (occ-sub h b (∨-false₂ (occTm x a) e))
occ-sub h (fst p)    e = occ-sub h p e
occ-sub h (snd p)    e = occ-sub h p e
occ-sub h ⌜base⌝     e = refl
occ-sub {x = x} h (⌜Π⌝ c d) e =
  ∨-false (occ-sub h c (∨-false₁ (occTm x c) e))
          (occ-sub (ext-occ h) d (∨-false₂ (occTm x c) e))
occ-sub {x = x} h (⌜Σ⌝ c d) e =
  ∨-false (occ-sub h c (∨-false₁ (occTm x c) e))
          (occ-sub (ext-occ h) d (∨-false₂ (occTm x c) e))
occ-sub {x = x} h (⌜Hom⌝ c a b) e =
  ∨-false (occ-sub h c (∨-false₁ (occTm x c) e))
          (∨-false (occ-sub h a (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e)))
                   (occ-sub h b (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e))))
occ-sub {x = x} h (⌜Id⌝ c a b) e =
  ∨-false (occ-sub h c (∨-false₁ (occTm x c) e))
          (∨-false (occ-sub h a (∨-false₁ (occTm x a) (∨-false₂ (occTm x c) e)))
                   (occ-sub h b (∨-false₂ (occTm x a) (∨-false₂ (occTm x c) e))))
occ-sub {x = x} h (hrefl c t) e =
  ∨-false (occ-sub h c (∨-false₁ (occTm x c) e))
          (occ-sub h t (∨-false₂ (occTm x c) e))
occ-sub {x = x} h (idrefl c t) e =
  ∨-false (occ-sub h c (∨-false₁ (occTm x c) e))
          (occ-sub h t (∨-false₂ (occTm x c) e))
occ-sub {x = x} h (tr d p q) e =
  ∨-false (occ-sub (ext-occ h) d (∨-false₁ (occTm (vs x) d) e))
          (∨-false (occ-sub h p (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
                   (occ-sub h q (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e))))
occ-sub {x = x} h (jsub d p q) e =
  ∨-false (occ-sub (ext-occ h) d (∨-false₁ (occTm (vs x) d) e))
          (∨-false (occ-sub h p (∨-false₁ (occTm x p) (∨-false₂ (occTm (vs x) d) e)))
                   (occ-sub h q (∨-false₂ (occTm x p) (∨-false₂ (occTm (vs x) d) e))))
occ-sub {x = x} h (ap c b p) e =
  ∨-false (occ-sub h c (∨-false₁ (occTm x c) e))
          (∨-false (occ-sub (ext-occ h) b (∨-false₁ (occTm (vs x) b) (∨-false₂ (occTm x c) e)))
                   (occ-sub h p (∨-false₂ (occTm (vs x) b) (∨-false₂ (occTm x c) e))))

-- Two substitutions agreeing on every OCCURRING variable act equally
-- (SpikeTr §9, promoted) — how `sr`'s `tr-pw` case bridges the swap
-- renaming to a typed substitution on a variable-avoiding motive.
ext-agree : {σ τ : Sub Γ Δ} (f : Var (Γ ∙) → 𝔹) →
            ((y : Var Γ) → f (vs y) ≡ true → σ y ≡ τ y) →
            (x : Var (Γ ∙)) → f x ≡ true → extS σ x ≡ extS τ x
ext-agree f g vz     _ = refl
ext-agree f g (vs y) o = cong (renTm vs) (g y o)

subTm-occ : {σ τ : Sub Γ Δ} (m : RTm Γ) →
            ((x : Var Γ) → occTm x m ≡ true → σ x ≡ τ x) →
            subTm σ m ≡ subTm τ m
subTm-occ ⌜Nat⌝      h = refl
subTm-occ ⌜Unit⌝     h = refl
subTm-occ unit       h = refl
subTm-occ nzero      h = refl
subTm-occ (nsuc n)   h = cong nsuc (subTm-occ n h)
subTm-occ (natrec z s n) h =
  natrec-cong₃
    (subTm-occ z (λ x o → h x (∨-inl o)))
    (subTm-occ s (ext-agree (λ x → occTm x s)
       (ext-agree (λ x → occTm (vs x) s)
         (λ y o → h y (∨-inr (occTm y z) (∨-inl o))))))
    (subTm-occ n (λ x o → h x (∨-inr (occTm x z) (∨-inr (occTm (vs (vs x)) s) o))))
subTm-occ (var y)    h = h y (eqv-refl y)
subTm-occ (lam m)    h = cong lam (subTm-occ m (ext-agree (λ x → occTm x m) h))
subTm-occ (app m k)  h = cong₂ app
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (pair m k) h = cong₂ pair
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (fst m)    h = cong fst (subTm-occ m h)
subTm-occ (snd m)    h = cong snd (subTm-occ m h)
subTm-occ ⌜base⌝     h = refl
subTm-occ (⌜Π⌝ m k)  h = cong₂ ⌜Π⌝
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (ext-agree (λ x → occTm x k) (λ y o → h y (∨-inr (occTm y m) o))))
subTm-occ (⌜Σ⌝ m k)  h = cong₂ ⌜Σ⌝
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (ext-agree (λ x → occTm x k) (λ y o → h y (∨-inr (occTm y m) o))))
subTm-occ (⌜Hom⌝ m k l) h =
  ⌜Hom⌝-cong₃
    (subTm-occ m (λ x o → h x (∨-inl o)))
    (subTm-occ k (λ x o → h x (∨-inr (occTm x m) (∨-inl o))))
    (subTm-occ l (λ x o → h x (∨-inr (occTm x m) (∨-inr (occTm x k) o))))
subTm-occ (⌜Id⌝ m k l) h =
  ⌜Id⌝-cong₃
    (subTm-occ m (λ x o → h x (∨-inl o)))
    (subTm-occ k (λ x o → h x (∨-inr (occTm x m) (∨-inl o))))
    (subTm-occ l (λ x o → h x (∨-inr (occTm x m) (∨-inr (occTm x k) o))))
subTm-occ (hrefl m k) h = cong₂ hrefl
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (idrefl m k) h = cong₂ idrefl
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (tr m k l) h =
  tr-cong₃
    (subTm-occ m (ext-agree (λ x → occTm x m) (λ y o → h y (∨-inl o))))
    (subTm-occ k (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inl o))))
    (subTm-occ l (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inr (occTm x k) o))))
subTm-occ (jsub m k l) h =
  jsub-cong₃
    (subTm-occ m (ext-agree (λ x → occTm x m) (λ y o → h y (∨-inl o))))
    (subTm-occ k (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inl o))))
    (subTm-occ l (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inr (occTm x k) o))))
subTm-occ (ap m k l) h =
  ap-cong₃
    (subTm-occ m (λ x o → h x (∨-inl o)))
    (subTm-occ k (ext-agree (λ x → occTm x k) (λ y o → h y (∨-inr (occTm y m) (∨-inl o)))))
    (subTm-occ l (λ x o → h x (∨-inr (occTm x m) (∨-inr (occTm (vs x) k) o))))

------------------------------------------------------------------------
-- 7. `PosC` survives renaming and substitution — `⊢tr` moves under both.
------------------------------------------------------------------------

posc-ren : {ρ : Ren Γ Δ} {d : RTm (Γ ∙)} →
           PosC vz d → PosC vz (renTm (extR ρ) d)
posc-ren posc-var = posc-var
posc-ren {ρ = ρ} (posc-Hom {c = c} {a = a} hc ha) =
  posc-Hom (trans (occ-ren-eq inv c) hc) (trans (occ-ren-eq inv a) ha)
  where
  inv : ∀ y → eqv vz (extR ρ y) ≡ eqv vz y
  inv vz     = refl
  inv (vs y) = refl

posc-sub : {σ : Sub Γ Δ} {d : RTm (Γ ∙)} →
           PosC vz d → PosC vz (subTm (extS σ) d)
posc-sub posc-var = posc-var
posc-sub {σ = σ} (posc-Hom {c = c} {a = a} hc ha) =
  posc-Hom (occ-sub hs c hc) (occ-sub hs a ha)
  where
  hs : ∀ y → eqv vz y ≡ false → occTm vz (extS σ y) ≡ false
  hs vz ()
  hs (vs y) _ = occ-ren-tm avoids-wk (σ y)

------------------------------------------------------------------------
-- ★ W2b (G1) — THE CANONICITY PACKAGE'S CLASSIFIERS, promoted from
-- `SpikeCanon`: `Pw`/`StkC` as total Booleans, and the pointwise
-- body/domain FUNCTIONS (the spine recursion happens at rule-firing
-- time, not in the reduction relation — SpikeCanon finding 2).
------------------------------------------------------------------------

-- pw-able codes: decode to Π-unfoldable types (⌜Hom⌝-spines over ⌜Π⌝).
pw? : RTm Γ → 𝔹
pw? (⌜Π⌝ γ δ)     = true
pw? (⌜Hom⌝ C a b) = pw? C
pw? _             = false

-- permanently stable codes: J-able, and NEVER ⌜Π⌝-able — not even
-- under substitution (constructor-headed spines only).
stkC? : RTm Γ → 𝔹
stkC? ⌜base⌝        = true
stkC? (⌜Σ⌝ c d)     = true
-- ★ the two-former kernel: ⌜Id⌝ joins the STABLE J-able shapes — its
-- decode is inert (never Π), so paths at Id-coded types are J-only.
stkC? (⌜Id⌝ c a b)  = true
-- ★ stage C: ⌜Unit⌝ is a STABLE J-able shape — inert decode, never
-- ⌜Π⌝-able, so paths at it are J-only (exactly the ⌜base⌝/⌜Σ⌝/⌜Id⌝
-- verdict).
stkC? ⌜Unit⌝        = true
-- ★★ ⌜Nat⌝ is NOT J-able, and this is the axis's one real cost.
-- `stkC?` is the J-ABILITY key (it is what `tr-J-Hom` and `ap-J` test),
-- and `tr-J-Nat` BREAKS SUBJECT REDUCTION: `Hom-Nat-z` reads
-- `Hom Nat nzero n ⟶ Unit` for ANY `n`, so `Hom Nat nzero nzero` and
-- `Hom Nat nzero (nsuc j)` are convertible, and a `hrefl ⌜Nat⌝ nzero`
-- NO LONGER PINS ITS ENDPOINTS — which is exactly what J assumes.  The
-- counterexample is written out in SPIKE-WF.md §7.  The sharp statement
-- is not "datatype codes are exotic" but **ORDERED types cannot be
-- J-able, because their path space is proof-irrelevant**: only `Nat` is
-- poisoned, and precisely because only `Nat` has the collapsing `Hom`.
-- So ⌜Nat⌝ is neither `pw?` nor `stkC?` — the THIRD code kind (see
-- `codeCanon`'s three-way split in NbEPDirDBCanon).  Transport along an
-- order path is recovered by the tt-path rule (≤-coercion), not by J.
stkC? ⌜Nat⌝         = false
stkC? (⌜Hom⌝ C a b) = stkC? C
stkC? _             = false

pwDom : RTm Γ → RTm Γ
pwDom (⌜Π⌝ γ δ)     = γ
pwDom (⌜Hom⌝ C a b) = pwDom C
pwDom t             = t

pwBody : RTm Γ → RTm (Γ ∙)
pwBody (⌜Π⌝ γ δ)     = δ
pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C)
                             (app (renTm vs a) (var vz))
                             (app (renTm vs b) (var vz))
pwBody t             = renTm vs t

-- (Γ, end, Πb) → (Γ, x, end′): the Π-binder becomes x, the old
-- endpoint goes to junk (typed-dead — the motive's components are
-- vz-free by `⊢tr`'s premises).
pwShift : Ren ((Γ ∙) ∙) ((Γ ∙) ∙)
pwShift vz     = vs vz
pwShift (vs y) = vs y

stk⊥pw : (C : RTm Γ) → stkC? C ≡ true → pw? C ≡ false
stk⊥pw (var x) ()
stk⊥pw (lam t) ()
stk⊥pw (app t u) ()
stk⊥pw (pair a b) ()
stk⊥pw (fst t) ()
stk⊥pw (snd t) ()
stk⊥pw ⌜base⌝ h = refl
stk⊥pw (⌜Π⌝ γ δ) ()
stk⊥pw (⌜Σ⌝ c d) h = refl
stk⊥pw (⌜Hom⌝ C a b) h = stk⊥pw C h
stk⊥pw (⌜Id⌝ C a b) h = refl
stk⊥pw ⌜Nat⌝ ()
stk⊥pw ⌜Unit⌝ h = refl
stk⊥pw (hrefl c t) ()
stk⊥pw (idrefl c t) ()
stk⊥pw (tr d p e) ()
stk⊥pw (jsub d p e) ()
stk⊥pw (ap c b p) ()

-- renaming EQUALITIES.
pw?-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → pw? (renTm ρ C) ≡ pw? C
pw?-ren ρ (var x)       = refl
pw?-ren ρ (lam t)       = refl
pw?-ren ρ (app t u)     = refl
pw?-ren ρ (pair a b)    = refl
pw?-ren ρ (fst t)       = refl
pw?-ren ρ (snd t)       = refl
pw?-ren ρ ⌜base⌝        = refl
pw?-ren ρ ⌜Nat⌝         = refl
pw?-ren ρ ⌜Unit⌝        = refl
pw?-ren ρ unit          = refl
pw?-ren ρ nzero         = refl
pw?-ren ρ (nsuc n)      = refl
pw?-ren ρ (natrec z s n) = refl
pw?-ren ρ (⌜Π⌝ γ δ)     = refl
pw?-ren ρ (⌜Σ⌝ c d)     = refl
pw?-ren ρ (⌜Hom⌝ C a b) = pw?-ren ρ C
pw?-ren ρ (⌜Id⌝ C a b) = refl
pw?-ren ρ (hrefl c t)   = refl
pw?-ren ρ (idrefl c t)   = refl
pw?-ren ρ (tr d p e)    = refl
pw?-ren ρ (jsub d p e)    = refl
pw?-ren ρ (ap c b p)    = refl

stkC?-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → stkC? (renTm ρ C) ≡ stkC? C
stkC?-ren ρ (var x)       = refl
stkC?-ren ρ (lam t)       = refl
stkC?-ren ρ (app t u)     = refl
stkC?-ren ρ (pair a b)    = refl
stkC?-ren ρ (fst t)       = refl
stkC?-ren ρ (snd t)       = refl
stkC?-ren ρ ⌜base⌝        = refl
stkC?-ren ρ ⌜Nat⌝         = refl
stkC?-ren ρ ⌜Unit⌝        = refl
stkC?-ren ρ unit          = refl
stkC?-ren ρ nzero         = refl
stkC?-ren ρ (nsuc n)      = refl
stkC?-ren ρ (natrec z s n) = refl
stkC?-ren ρ (⌜Π⌝ γ δ)     = refl
stkC?-ren ρ (⌜Σ⌝ c d)     = refl
stkC?-ren ρ (⌜Hom⌝ C a b) = stkC?-ren ρ C
stkC?-ren ρ (⌜Id⌝ C a b) = refl
stkC?-ren ρ (hrefl c t)   = refl
stkC?-ren ρ (idrefl c t)   = refl
stkC?-ren ρ (tr d p e)    = refl
stkC?-ren ρ (jsub d p e)    = refl
stkC?-ren ρ (ap c b p)    = refl

-- ★ directed `ap` (SpikeAp, refined at the fund landing): the SOURCE
-- ambient key.  `flat?` codes decode to SN-only-membership interps
-- (base, stuck Hom) — exactly what the semantic ap case can feed its
-- body instances with.  `⌜Σ⌝` is EXCLUDED: Σ-memberships carry
-- componentwise structure the path argument cannot supply; ap at
-- Σ-typed sources joins the G3 Σ-frontier ledger.
flat? : RTm Γ → 𝔹
flat? ⌜base⌝        = true
flat? (⌜Hom⌝ c a b) = stkC? c
flat? _             = false

flat→stk : (c : RTm Γ) → flat? c ≡ true → stkC? c ≡ true
flat→stk ⌜base⌝        h = refl
flat→stk (⌜Hom⌝ c a b) h = h
flat→stk (⌜Id⌝ c a b) ()
flat→stk (var _) ()
flat→stk (lam _) ()
flat→stk (app _ _) ()
flat→stk (pair _ _) ()
flat→stk (fst _) ()
flat→stk (snd _) ()
flat→stk (⌜Π⌝ _ _) ()
flat→stk (⌜Σ⌝ _ _) ()
flat→stk (hrefl _ _) ()
flat→stk (idrefl _ _) ()
flat→stk (tr _ _ _) ()
flat→stk (jsub _ _ _) ()
flat→stk (ap _ _ _) ()

flat?-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → flat? (renTm ρ C) ≡ flat? C
flat?-ren ρ (var x)        = refl
flat?-ren ρ (lam t)        = refl
flat?-ren ρ (app t u)      = refl
flat?-ren ρ (pair a b)     = refl
flat?-ren ρ (fst t)        = refl
flat?-ren ρ (snd t)        = refl
flat?-ren ρ ⌜base⌝         = refl
flat?-ren ρ ⌜Nat⌝          = refl
flat?-ren ρ ⌜Unit⌝         = refl
flat?-ren ρ unit           = refl
flat?-ren ρ nzero          = refl
flat?-ren ρ (nsuc n)       = refl
flat?-ren ρ (natrec z s n) = refl
flat?-ren ρ (⌜Π⌝ c d)      = refl
flat?-ren ρ (⌜Σ⌝ c d)      = refl
flat?-ren ρ (⌜Hom⌝ c a b)  = stkC?-ren ρ c
flat?-ren ρ (⌜Id⌝ c a b)  = refl
flat?-ren ρ (hrefl c t)    = refl
flat?-ren ρ (idrefl c t)    = refl
flat?-ren ρ (tr d p e)     = refl
flat?-ren ρ (jsub d p e)     = refl
flat?-ren ρ (ap c b p)     = refl


-- weakening commutes with a renaming (both composites are
-- definitionally `x ↦ vs (ρ x)`).
wk-ren-tm : (ρ : Ren Γ Δ) (t : RTm Γ) →
            renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
wk-ren-tm ρ t = trans (renTm-renTm t) (sym (renTm-renTm t))

pwDom-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → pw? C ≡ true →
            pwDom (renTm ρ C) ≡ renTm ρ (pwDom C)
pwDom-ren ρ (var x) ()
pwDom-ren ρ (lam t) ()
pwDom-ren ρ (app t u) ()
pwDom-ren ρ (pair a b) ()
pwDom-ren ρ (fst t) ()
pwDom-ren ρ (snd t) ()
pwDom-ren ρ ⌜base⌝ ()
pwDom-ren ρ (⌜Π⌝ γ δ) h = refl
pwDom-ren ρ (⌜Σ⌝ c d) ()
pwDom-ren ρ (⌜Hom⌝ C a b) h = pwDom-ren ρ C h
pwDom-ren ρ (⌜Id⌝ C a b) ()
pwDom-ren ρ (hrefl c t) ()
pwDom-ren ρ (idrefl c t) ()
pwDom-ren ρ (tr d p e) ()
pwDom-ren ρ (jsub d p e) ()
pwDom-ren ρ (ap c b p) ()

pwBody-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → pw? C ≡ true →
             pwBody (renTm ρ C) ≡ renTm (extR ρ) (pwBody C)
pwBody-ren ρ (var x) ()
pwBody-ren ρ (lam t) ()
pwBody-ren ρ (app t u) ()
pwBody-ren ρ (pair a b) ()
pwBody-ren ρ (fst t) ()
pwBody-ren ρ (snd t) ()
pwBody-ren ρ ⌜base⌝ ()
pwBody-ren ρ (⌜Π⌝ γ δ) h = refl
pwBody-ren ρ (⌜Σ⌝ c d) ()
pwBody-ren ρ (⌜Hom⌝ C a b) h =
  ⌜Hom⌝-cong₃ (pwBody-ren ρ C h)
              (cong (λ z → app z (var vz)) (sym (wk-ren-tm ρ a)))
              (cong (λ z → app z (var vz)) (sym (wk-ren-tm ρ b)))
pwBody-ren ρ (⌜Id⌝ C a b) ()
pwBody-ren ρ (hrefl c t) ()
pwBody-ren ρ (idrefl c t) ()
pwBody-ren ρ (tr d p e) ()
pwBody-ren ρ (jsub d p e) ()
pwBody-ren ρ (ap c b p) ()

-- substitution PRESERVES the keys (one direction only — a substitution
-- can CREATE pw-ability at a variable head, which is exactly why
-- `stkC?` excludes neutrals) and commutes with body/domain.
wk-sub-tm : (σ : Sub Γ Δ) (t : RTm Γ) →
            subTm (extS σ) (renTm vs t) ≡ renTm vs (subTm σ t)
wk-sub-tm σ t = trans (subTm-renTm t) (sym (renTm-subTm t))

pw?-sub : (σ : Sub Γ Δ) (C : RTm Γ) → pw? C ≡ true →
          pw? (subTm σ C) ≡ true
pw?-sub σ (var x) ()
pw?-sub σ (lam t) ()
pw?-sub σ (app t u) ()
pw?-sub σ (pair a b) ()
pw?-sub σ (fst t) ()
pw?-sub σ (snd t) ()
pw?-sub σ ⌜base⌝ ()
pw?-sub σ (⌜Π⌝ γ δ) h = refl
pw?-sub σ (⌜Σ⌝ c d) ()
pw?-sub σ (⌜Hom⌝ C a b) h = pw?-sub σ C h
pw?-sub σ (⌜Id⌝ C a b) ()
pw?-sub σ (hrefl c t) ()
pw?-sub σ (idrefl c t) ()
pw?-sub σ (tr d p e) ()
pw?-sub σ (jsub d p e) ()
pw?-sub σ (ap c b p) ()

stkC?-sub : (σ : Sub Γ Δ) (C : RTm Γ) → stkC? C ≡ true →
            stkC? (subTm σ C) ≡ true
stkC?-sub σ (var x) ()
stkC?-sub σ (lam t) ()
stkC?-sub σ (app t u) ()
stkC?-sub σ (pair a b) ()
stkC?-sub σ (fst t) ()
stkC?-sub σ (snd t) ()
stkC?-sub σ ⌜base⌝ h = refl
stkC?-sub σ (⌜Π⌝ γ δ) ()
stkC?-sub σ (⌜Σ⌝ c d) h = refl
stkC?-sub σ (⌜Hom⌝ C a b) h = stkC?-sub σ C h
stkC?-sub σ (⌜Id⌝ C a b) h = refl
stkC?-sub σ ⌜Nat⌝ ()
stkC?-sub σ ⌜Unit⌝ h = refl
stkC?-sub σ (hrefl c t) ()
stkC?-sub σ (idrefl c t) ()
stkC?-sub σ (tr d p e) ()
stkC?-sub σ (jsub d p e) ()
stkC?-sub σ (ap c b p) ()

flat?-sub : (σ : Sub Γ Δ) (C : RTm Γ) → flat? C ≡ true →
            flat? (subTm σ C) ≡ true
flat?-sub σ ⌜base⌝        h = refl
flat?-sub σ (⌜Hom⌝ c a b) h = stkC?-sub σ c h
flat?-sub σ (⌜Id⌝ c a b) ()
flat?-sub σ (var _) ()
flat?-sub σ (lam _) ()
flat?-sub σ (app _ _) ()
flat?-sub σ (pair _ _) ()
flat?-sub σ (fst _) ()
flat?-sub σ (snd _) ()
flat?-sub σ (⌜Π⌝ _ _) ()
flat?-sub σ (⌜Σ⌝ _ _) ()
flat?-sub σ (hrefl _ _) ()
flat?-sub σ (idrefl _ _) ()
flat?-sub σ (tr _ _ _) ()
flat?-sub σ (jsub _ _ _) ()
flat?-sub σ (ap _ _ _) ()

pwDom-sub : (σ : Sub Γ Δ) (C : RTm Γ) → pw? C ≡ true →
            pwDom (subTm σ C) ≡ subTm σ (pwDom C)
pwDom-sub σ (var x) ()
pwDom-sub σ (lam t) ()
pwDom-sub σ (app t u) ()
pwDom-sub σ (pair a b) ()
pwDom-sub σ (fst t) ()
pwDom-sub σ (snd t) ()
pwDom-sub σ ⌜base⌝ ()
pwDom-sub σ (⌜Π⌝ γ δ) h = refl
pwDom-sub σ (⌜Σ⌝ c d) ()
pwDom-sub σ (⌜Hom⌝ C a b) h = pwDom-sub σ C h
pwDom-sub σ (⌜Id⌝ C a b) ()
pwDom-sub σ (hrefl c t) ()
pwDom-sub σ (idrefl c t) ()
pwDom-sub σ (tr d p e) ()
pwDom-sub σ (jsub d p e) ()
pwDom-sub σ (ap c b p) ()

pwBody-sub : (σ : Sub Γ Δ) (C : RTm Γ) → pw? C ≡ true →
             pwBody (subTm σ C) ≡ subTm (extS σ) (pwBody C)
pwBody-sub σ (var x) ()
pwBody-sub σ (lam t) ()
pwBody-sub σ (app t u) ()
pwBody-sub σ (pair a b) ()
pwBody-sub σ (fst t) ()
pwBody-sub σ (snd t) ()
pwBody-sub σ ⌜base⌝ ()
pwBody-sub σ (⌜Π⌝ γ δ) h = refl
pwBody-sub σ (⌜Σ⌝ c d) ()
pwBody-sub σ (⌜Hom⌝ C a b) h =
  ⌜Hom⌝-cong₃ (pwBody-sub σ C h)
              (cong (λ z → app z (var vz)) (sym (wk-sub-tm σ a)))
              (cong (λ z → app z (var vz)) (sym (wk-sub-tm σ b)))
pwBody-sub σ (⌜Id⌝ C a b) ()
pwBody-sub σ (hrefl c t) ()
pwBody-sub σ (idrefl c t) ()
pwBody-sub σ (tr d p e) ()
pwBody-sub σ (jsub d p e) ()
pwBody-sub σ (ap c b p) ()

-- `pwShift` never outputs `vz` — the inner motive `tr-pw` builds is
-- vz-free STRUCTURALLY (what discharges `⊢tr`'s occurrence premises
-- for the pointwise instance).
avoids-pwShift : Avoids (pwShift {Γ}) vz
avoids-pwShift vz     = refl
avoids-pwShift (vs y) = refl

pw⊥stk : (C : RTm Γ) → pw? C ≡ true → stkC? C ≡ false
pw⊥stk (var x) ()
pw⊥stk (lam t) ()
pw⊥stk (app t u) ()
pw⊥stk (pair a b) ()
pw⊥stk (fst t) ()
pw⊥stk (snd t) ()
pw⊥stk ⌜base⌝ ()
pw⊥stk (⌜Π⌝ γ δ) h = refl
pw⊥stk (⌜Σ⌝ c d) ()
pw⊥stk (⌜Hom⌝ C a b) h = pw⊥stk C h
pw⊥stk (⌜Id⌝ C a b) ()
pw⊥stk (hrefl c t) ()
pw⊥stk (idrefl c t) ()
pw⊥stk (tr d p e) ()
pw⊥stk (jsub d p e) ()
pw⊥stk (ap c b p) ()

-- a renaming IS a variable-image substitution — lets `subTm-occ`'s
-- occurrence-agreement machinery reach mixed ren/sub equations.
ren-as-sub : (ρ : Ren Γ Δ) (t : RTm Γ) →
             renTm ρ t ≡ subTm (λ x → var (ρ x)) t
ren-as-sub ρ (var x)    = refl
ren-as-sub ρ (lam t)    =
  cong lam (trans (ren-as-sub (extR ρ) t)
                  (subTm-cong ptw t))
  where
  ptw : ∀ x → var (extR ρ x) ≡ extS (λ y → var (ρ y)) x
  ptw vz     = refl
  ptw (vs x) = refl
ren-as-sub ρ (app t u)  = cong₂ app (ren-as-sub ρ t) (ren-as-sub ρ u)
ren-as-sub ρ (pair a b) = cong₂ pair (ren-as-sub ρ a) (ren-as-sub ρ b)
ren-as-sub ρ (fst t)    = cong fst (ren-as-sub ρ t)
ren-as-sub ρ (snd t)    = cong snd (ren-as-sub ρ t)
ren-as-sub ρ ⌜base⌝     = refl
ren-as-sub ρ (⌜Π⌝ c d)  =
  cong₂ ⌜Π⌝ (ren-as-sub ρ c)
        (trans (ren-as-sub (extR ρ) d) (subTm-cong ptw d))
  where
  ptw : ∀ x → var (extR ρ x) ≡ extS (λ y → var (ρ y)) x
  ptw vz     = refl
  ptw (vs x) = refl
ren-as-sub ρ (⌜Σ⌝ c d)  =
  cong₂ ⌜Σ⌝ (ren-as-sub ρ c)
        (trans (ren-as-sub (extR ρ) d) (subTm-cong ptw d))
  where
  ptw : ∀ x → var (extR ρ x) ≡ extS (λ y → var (ρ y)) x
  ptw vz     = refl
  ptw (vs x) = refl
ren-as-sub ρ (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (ren-as-sub ρ c) (ren-as-sub ρ a) (ren-as-sub ρ b)
ren-as-sub ρ (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (ren-as-sub ρ c) (ren-as-sub ρ a) (ren-as-sub ρ b)
ren-as-sub ρ (hrefl c t) =
  cong₂ hrefl (ren-as-sub ρ c) (ren-as-sub ρ t)
ren-as-sub ρ (idrefl c t) =
  cong₂ idrefl (ren-as-sub ρ c) (ren-as-sub ρ t)
ren-as-sub ρ (tr d p e) =
  tr-cong₃ (trans (ren-as-sub (extR ρ) d) (subTm-cong ptw d))
           (ren-as-sub ρ p) (ren-as-sub ρ e)
  where
  ptw : ∀ x → var (extR ρ x) ≡ extS (λ y → var (ρ y)) x
  ptw vz     = refl
  ptw (vs x) = refl
ren-as-sub ρ (jsub d p e) =
  jsub-cong₃ (trans (ren-as-sub (extR ρ) d) (subTm-cong ptw d))
           (ren-as-sub ρ p) (ren-as-sub ρ e)
  where
  ptw : ∀ x → var (extR ρ x) ≡ extS (λ y → var (ρ y)) x
  ptw vz     = refl
  ptw (vs x) = refl
ren-as-sub ρ ⌜Nat⌝ = refl
ren-as-sub ρ ⌜Unit⌝ = refl
ren-as-sub ρ unit  = refl
ren-as-sub ρ nzero = refl
ren-as-sub ρ (nsuc n) = cong nsuc (ren-as-sub ρ n)
ren-as-sub ρ (natrec z s n) =
  natrec-cong₃ (ren-as-sub ρ z)
    (trans (ren-as-sub (extR (extR ρ)) s) (subTm-cong ptw2 s))
    (ren-as-sub ρ n)
  where
  ptw2 : ∀ x → var (extR (extR ρ) x) ≡ extS (extS (λ y → var (ρ y))) x
  ptw2 vz          = refl
  ptw2 (vs vz)     = refl
  ptw2 (vs (vs x)) = refl
ren-as-sub ρ (ap c b p) =
  ap-cong₃ (ren-as-sub ρ c)
           (trans (ren-as-sub (extR ρ) b) (subTm-cong ptw b))
           (ren-as-sub ρ p)
  where
  ptw : ∀ x → var (extR ρ x) ≡ extS (λ y → var (ρ y)) x
  ptw vz     = refl
  ptw (vs x) = refl

-- the pointwise body preserves NON-occurrence (one binder deeper).
pwBody-occ : {x : Var Γ} (C : RTm Γ) → pw? C ≡ true →
             occTm x C ≡ false → occTm (vs x) (pwBody C) ≡ false
pwBody-occ (var y) () o
pwBody-occ (lam t) () o
pwBody-occ (app t u) () o
pwBody-occ (pair a b) () o
pwBody-occ (fst t) () o
pwBody-occ (snd t) () o
pwBody-occ ⌜base⌝ () o
pwBody-occ {x = x} (⌜Π⌝ γ δ) h o = ∨-false₂ (occTm x γ) o
pwBody-occ (⌜Σ⌝ c d) () o
pwBody-occ {x = x} (⌜Hom⌝ C a b) h o =
  ∨-false (pwBody-occ C h (∨-false₁ (occTm x C) o))
    (∨-false
      (∨-false (occ-shift a (∨-false₁ (occTm x a) (∨-false₂ (occTm x C) o)))
               refl)
      (∨-false (occ-shift b (∨-false₂ (occTm x a) (∨-false₂ (occTm x C) o)))
               refl))
  where
  occ-shift : {x : Var Γ} (t : RTm Γ) → occTm x t ≡ false →
              occTm (vs x) (renTm vs t) ≡ false
  occ-shift {x = x} t o' =
    trans (occ-ren-eq (λ y → refl) t) o'
pwBody-occ (hrefl c t) () o
pwBody-occ (idrefl c t) () o
pwBody-occ (tr d p e) () o
pwBody-occ (⌜Id⌝ c a b) () o
pwBody-occ (jsub d p e) () o
pwBody-occ (ap c b p) () o
