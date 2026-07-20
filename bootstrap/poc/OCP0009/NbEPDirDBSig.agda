------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 29 — a SELF-CONTAINED dependent Π/Σ calculus with
--                            genuine PAIRS (the Σ intro/elim the kernel lacked)
--
-- A standalone demonstration of the [A1] design (HANDOFF §3): dependent Σ with
-- INTRODUCTION and ELIMINATION terms — `pair`/`fst`/`snd` — which the committed
-- kernel (`NbEPDirDBPi`…) has only as a type former (`Σ'`). Rather than extend
-- the shared syntax (which would cascade through the whole metatheory), this is
-- a fresh, self-contained mini type theory: its own Cx/Var/Ty/Tm, substitution,
-- reduction, conversion, and typing — touching nothing already built.
--
--   * Syntax: `Ty` = `base`/`Pi`/`Sig`/`El` (mutual with `Tm`); `Tm` =
--     `var`/`lam`/`app`/`pair`/`fst`/`snd`.
--   * Substitution: renaming + parallel substitution on both sorts.
--   * Reduction `_⟶_`: β (`app (lam t) u ⟶ t[u]`) AND Σ-β (`fst (pair a b) ⟶ a`,
--     `snd (pair a b) ⟶ b`), + congruences. Conversion `_≅_`/`_≅ᵀ_` = the R-S-T
--     closure, PLUS Π-η and **Σ-η** (surjective pairing `p ≅ pair (fst p)(snd p)`).
--   * Typing: DEPENDENT `⊢app` (`app t u ∷ B[u]`), `⊢pair`
--     (`b ∷ B[a] → pair a b ∷ Sig A B`), `⊢fst` (`∷ A`), `⊢snd`
--     (`∷ B[fst p]` — the second projection's type depends on the first!), `⊢conv`.
--   * Demonstrations: the identity `λx.x ∷ Π base base`; a GENUINELY DEPENDENT
--     PAIR in `Sig base (El (var vz))` with both projections and their β-steps;
--     Σ-η at work.
--
-- Scope: a design demo, not wired into the committed metatheory — so it does not
-- extend `sr`/confluence to pairs (that is the invasive integrated pass). It
-- shows the Σ-term design end-to-end. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBSig where

open import normalizer.Syntax.Types using ( _≡_; refl )

------------------------------------------------------------------------
-- Scopes and the mutual dependent syntax (with Σ intro/elim).
------------------------------------------------------------------------

data Cx : Set where
  ε  : Cx
  _∙ : Cx → Cx

data Var : Cx → Set where
  vz : ∀ {Γ} → Var (Γ ∙)
  vs : ∀ {Γ} → Var Γ → Var (Γ ∙)

data Ty : Cx → Set
data Tm : Cx → Set

data Ty where
  base : ∀ {Γ} → Ty Γ
  Pi   : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ
  Sig  : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ
  El   : ∀ {Γ} → Tm Γ → Ty Γ

data Tm where
  var  : ∀ {Γ} → Var Γ → Tm Γ
  lam  : ∀ {Γ} → Tm (Γ ∙) → Tm Γ
  app  : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ
  pair : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ
  fst  : ∀ {Γ} → Tm Γ → Tm Γ
  snd  : ∀ {Γ} → Tm Γ → Tm Γ

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- Renaming and parallel substitution (both sorts).
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

renTy : Ren Γ Δ → Ty Γ → Ty Δ
renTm : Ren Γ Δ → Tm Γ → Tm Δ
renTy ρ base      = base
renTy ρ (Pi A B)  = Pi (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Sig A B) = Sig (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (El t)    = El (renTm ρ t)
renTm ρ (var x)    = var (ρ x)
renTm ρ (lam t)    = lam (renTm (extR ρ) t)
renTm ρ (app t u)  = app (renTm ρ t) (renTm ρ u)
renTm ρ (pair a b) = pair (renTm ρ a) (renTm ρ b)
renTm ρ (fst p)    = fst (renTm ρ p)
renTm ρ (snd p)    = snd (renTm ρ p)

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → Tm Δ

extS : Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = renTm vs (σ x)

subTy : Sub Γ Δ → Ty Γ → Ty Δ
subTm : Sub Γ Δ → Tm Γ → Tm Δ
subTy σ base      = base
subTy σ (Pi A B)  = Pi (subTy σ A) (subTy (extS σ) B)
subTy σ (Sig A B) = Sig (subTy σ A) (subTy (extS σ) B)
subTy σ (El t)    = El (subTm σ t)
subTm σ (var x)    = σ x
subTm σ (lam t)    = lam (subTm (extS σ) t)
subTm σ (app t u)  = app (subTm σ t) (subTm σ u)
subTm σ (pair a b) = pair (subTm σ a) (subTm σ b)
subTm σ (fst p)    = fst (subTm σ p)
subTm σ (snd p)    = snd (subTm σ p)

single : Tm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- Reduction — β for Π AND Σ-β for pairs — and conversion (with η).
------------------------------------------------------------------------

infix 3 _⟶_ _⟶ᵀ_
data _⟶_ : {Γ : Cx} → Tm Γ → Tm Γ → Set where
  β      : (t : Tm (Γ ∙)) (u : Tm Γ) → app (lam t) u ⟶ subTm (single u) t
  βfst   : (a b : Tm Γ) → fst (pair a b) ⟶ a
  βsnd   : (a b : Tm Γ) → snd (pair a b) ⟶ b
  ξ-lam  : {t t' : Tm (Γ ∙)} → t ⟶ t' → lam t ⟶ lam t'
  ξ-appˡ : {t t' u : Tm Γ} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ : {t u u' : Tm Γ} → u ⟶ u' → app t u ⟶ app t u'
  ξ-pairˡ : {a a' b : Tm Γ} → a ⟶ a' → pair a b ⟶ pair a' b
  ξ-pairʳ : {a b b' : Tm Γ} → b ⟶ b' → pair a b ⟶ pair a b'
  ξ-fst  : {p p' : Tm Γ} → p ⟶ p' → fst p ⟶ fst p'
  ξ-snd  : {p p' : Tm Γ} → p ⟶ p' → snd p ⟶ snd p'

data _⟶ᵀ_ : {Γ : Cx} → Ty Γ → Ty Γ → Set where
  ξ-El   : {t t' : Tm Γ} → t ⟶ t' → El t ⟶ᵀ El t'
  ξ-Piˡ  : {A A' : Ty Γ} {B : Ty (Γ ∙)} → A ⟶ᵀ A' → Pi A B ⟶ᵀ Pi A' B
  ξ-Piʳ  : {A : Ty Γ} {B B' : Ty (Γ ∙)} → B ⟶ᵀ B' → Pi A B ⟶ᵀ Pi A B'
  ξ-Sigˡ : {A A' : Ty Γ} {B : Ty (Γ ∙)} → A ⟶ᵀ A' → Sig A B ⟶ᵀ Sig A' B
  ξ-Sigʳ : {A : Ty Γ} {B B' : Ty (Γ ∙)} → B ⟶ᵀ B' → Sig A B ⟶ᵀ Sig A B'

infix 3 _⟶*_
data _⟶*_ : {Γ : Cx} → Tm Γ → Tm Γ → Set where
  done : {t : Tm Γ} → t ⟶* t
  step : {t u v : Tm Γ} → t ⟶ u → u ⟶* v → t ⟶* v

infix 3 _≅_ _≅ᵀ_
data _≅_ : {Γ : Cx} → Tm Γ → Tm Γ → Set where
  cred : {t u : Tm Γ}   → t ⟶ u → t ≅ u
  crfl : {t : Tm Γ}     → t ≅ t
  csym : {t u : Tm Γ}   → t ≅ u → u ≅ t
  ctrn : {t u v : Tm Γ} → t ≅ u → u ≅ v → t ≅ v
  ηΠ   : (t : Tm Γ)     → t ≅ lam (app (renTm vs t) (var vz))     -- function η
  ηΣ   : (p : Tm Γ)     → p ≅ pair (fst p) (snd p)                -- surjective pairing

data _≅ᵀ_ : {Γ : Cx} → Ty Γ → Ty Γ → Set where
  credᵀ : {A B : Ty Γ}   → A ⟶ᵀ B → A ≅ᵀ B
  crflᵀ : {A : Ty Γ}     → A ≅ᵀ A
  csymᵀ : {A B : Ty Γ}   → A ≅ᵀ B → B ≅ᵀ A
  ctrnᵀ : {A B C : Ty Γ} → A ≅ᵀ B → B ≅ᵀ C → A ≅ᵀ C

------------------------------------------------------------------------
-- Typed contexts and the typing judgment (dependent app / pair / snd).
------------------------------------------------------------------------

data Ctx : Set
⌊_⌋ : Ctx → Cx

data Ctx where
  ◇   : Ctx
  _▹_ : (Γ : Ctx) → Ty ⌊ Γ ⌋ → Ctx

⌊ ◇ ⌋     = ε
⌊ Γ ▹ A ⌋ = ⌊ Γ ⌋ ∙

infix 3 _∋_∷_
data _∋_∷_ : (Γ : Ctx) → Var ⌊ Γ ⌋ → Ty ⌊ Γ ⌋ → Set where
  here  : ∀ {Γ} {A : Ty ⌊ Γ ⌋} → (Γ ▹ A) ∋ vz ∷ renTy vs A
  there : ∀ {Γ} {A B : Ty ⌊ Γ ⌋} {x} →
          Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A

infix 3 _⊢_∷_
data _⊢_∷_ : (Γ : Ctx) → Tm ⌊ Γ ⌋ → Ty ⌊ Γ ⌋ → Set where
  ⊢var  : ∀ {Γ x A}     → Γ ∋ x ∷ A → Γ ⊢ var x ∷ A
  ⊢lam  : ∀ {Γ A B t}   → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Pi A B
  ⊢app  : ∀ {Γ A B t u} → Γ ⊢ t ∷ Pi A B → Γ ⊢ u ∷ A →
                          Γ ⊢ app t u ∷ subTy (single u) B
  ⊢pair : ∀ {Γ A B a b} → Γ ⊢ a ∷ A → Γ ⊢ b ∷ subTy (single a) B →
                          Γ ⊢ pair a b ∷ Sig A B
  ⊢fst  : ∀ {Γ A B p}   → Γ ⊢ p ∷ Sig A B → Γ ⊢ fst p ∷ A
  ⊢snd  : ∀ {Γ A B p}   → Γ ⊢ p ∷ Sig A B →
                          Γ ⊢ snd p ∷ subTy (single (fst p)) B
  ⊢conv : ∀ {Γ t A B}   → Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B

------------------------------------------------------------------------
-- Demonstrations.
------------------------------------------------------------------------

-- The identity: `◇ ⊢ λx.x ∷ Π base base`.
⊢id : ◇ ⊢ lam (var vz) ∷ Pi base base
⊢id = ⊢lam (⊢var here)

-- A GENUINELY DEPENDENT PAIR. Context `x : base, y : El x`. The pair `(x , y)`
-- inhabits `Sig base (El (var vz))` — the second component's type `El (var vz)`
-- DEPENDS on the first. Its `snd`'s type `El (fst p)` depends on the projection.
Γ₁ : Ctx
Γ₁ = (◇ ▹ base) ▹ El (var vz)

-- x = var (vs vz) ∷ base ; y = var vz ∷ El x  (scope pinned to ⌊Γ₁⌋).
X Y : Tm ⌊ Γ₁ ⌋
X = var (vs vz)
Y = var vz

⊢x : Γ₁ ⊢ X ∷ base
⊢x = ⊢var (there here)

⊢y : Γ₁ ⊢ Y ∷ El X
⊢y = ⊢var here

-- `(x , y) ∷ Sig base (El (var vz))`.  (`b ∷ B[x] = El x`, and `B[x]` computes.)
⊢pairxy : Γ₁ ⊢ pair X Y ∷ Sig base (El (var vz))
⊢pairxy = ⊢pair {B = El (var vz)} ⊢x ⊢y

-- First projection: `∷ base`, and it β-reduces to `x`.
⊢fstxy : Γ₁ ⊢ fst (pair X Y) ∷ base
⊢fstxy = ⊢fst ⊢pairxy

fst-β : fst (pair X Y) ⟶ X
fst-β = βfst X Y

-- Second projection: `∷ El (fst (x,y))` — a DEPENDENT type — and β-reduces to `y`.
⊢sndxy : Γ₁ ⊢ snd (pair X Y) ∷ El (fst (pair X Y))
⊢sndxy = ⊢snd ⊢pairxy

snd-β : snd (pair X Y) ⟶ Y
snd-β = βsnd X Y

-- Σ-η (surjective pairing): the pair is convertible to `(fst p , snd p)`.
Ση-xy : pair X Y ≅ pair (fst (pair X Y)) (snd (pair X Y))
Ση-xy = ηΣ (pair X Y)
