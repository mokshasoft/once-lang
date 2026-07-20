------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 30 — a SELF-CONTAINED universe: a Tarski `U` whose
--                            codes DECODE BY REDUCTION
--
-- The standalone [A3] demonstration (HANDOFF §3): a universe `U` with codes
-- (terms of type `U`) and a decoding `El`, so a type can be NAMED by a term —
-- the ingredient the committed kernel's raw `El` lacks. As with `NbEPDirDBSig`
-- (dHoTT-29), a fresh self-contained mini type theory, touching nothing built.
--
-- Coquand-style: `El` is a type former and codes decode by TYPE REDUCTION —
-- `El ⌜Unit⌝ ⟶ᵀ Unit`, `El (⌜Π⌝ c d) ⟶ᵀ Π (El c) (El d)`. The codes are
-- genuinely DEPENDENT: `⌜Π⌝`'s codomain code lives under the decoded domain
-- (`(Γ ▹ El c) ⊢ d ∷ U`). Decoding is thus computation, and a term of a decoded
-- type is one of the coded type up to conversion.
--
--   * `Ty` = `U`/`El`/`Unit`/`Π`; `Tm` = `var`/`lam`/`app`/`tt`/`⌜Unit⌝`/`⌜Π⌝`.
--   * Reduction: β, plus the DECODING rules `El-⌜Unit⌝`/`El-⌜Π⌝`.
--   * Typing: `⊢⌜Unit⌝`/`⊢⌜Π⌝` (codes inhabit `U`, dependently), `⊢El`-free —
--     a term lands in `El c` via `⊢conv` across the decoding.
--   * Demos: `⌜Unit⌝ ∷ U` decodes to `Unit` and `tt ∷ El ⌜Unit⌝`; `⌜Π⌝ ⌜Unit⌝
--     ⌜Unit⌝ ∷ U` decodes to `Π Unit Unit` and `λx.x ∷ El (⌜Π⌝ ⌜Unit⌝ ⌜Unit⌝)`.
--
-- `--safe`, ZERO axioms. A design demo (not wired into the committed metatheory).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBUniv where

open import normalizer.Syntax.Types using ( _≡_; refl )

------------------------------------------------------------------------
-- Scopes and the mutual syntax (types name-able by codes).
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
  U    : ∀ {Γ} → Ty Γ                 -- the universe
  El   : ∀ {Γ} → Tm Γ → Ty Γ          -- decode a code
  Unit : ∀ {Γ} → Ty Γ
  Π    : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ

data Tm where
  var   : ∀ {Γ} → Var Γ → Tm Γ
  lam   : ∀ {Γ} → Tm (Γ ∙) → Tm Γ
  app   : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ
  tt    : ∀ {Γ} → Tm Γ
  ⌜Unit⌝ : ∀ {Γ} → Tm Γ               -- code for `Unit`
  ⌜Π⌝    : ∀ {Γ} → Tm Γ → Tm (Γ ∙) → Tm Γ  -- code for a `Π` (dependent codomain)

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
renTy ρ U        = U
renTy ρ (El t)   = El (renTm ρ t)
renTy ρ Unit     = Unit
renTy ρ (Π A B)  = Π (renTy ρ A) (renTy (extR ρ) B)
renTm ρ (var x)    = var (ρ x)
renTm ρ (lam t)    = lam (renTm (extR ρ) t)
renTm ρ (app t u)  = app (renTm ρ t) (renTm ρ u)
renTm ρ tt         = tt
renTm ρ ⌜Unit⌝     = ⌜Unit⌝
renTm ρ (⌜Π⌝ c d)  = ⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → Tm Δ

extS : Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = renTm vs (σ x)

subTy : Sub Γ Δ → Ty Γ → Ty Δ
subTm : Sub Γ Δ → Tm Γ → Tm Δ
subTy σ U        = U
subTy σ (El t)   = El (subTm σ t)
subTy σ Unit     = Unit
subTy σ (Π A B)  = Π (subTy σ A) (subTy (extS σ) B)
subTm σ (var x)    = σ x
subTm σ (lam t)    = lam (subTm (extS σ) t)
subTm σ (app t u)  = app (subTm σ t) (subTm σ u)
subTm σ tt         = tt
subTm σ ⌜Unit⌝     = ⌜Unit⌝
subTm σ (⌜Π⌝ c d)  = ⌜Π⌝ (subTm σ c) (subTm (extS σ) d)

single : Tm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- Reduction — β, plus DECODING of codes — and conversion.
------------------------------------------------------------------------

infix 3 _⟶_ _⟶ᵀ_
data _⟶_ : {Γ : Cx} → Tm Γ → Tm Γ → Set where
  β      : (t : Tm (Γ ∙)) (u : Tm Γ) → app (lam t) u ⟶ subTm (single u) t
  ξ-lam  : {t t' : Tm (Γ ∙)} → t ⟶ t' → lam t ⟶ lam t'
  ξ-appˡ : {t t' u : Tm Γ} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ : {t u u' : Tm Γ} → u ⟶ u' → app t u ⟶ app t u'

data _⟶ᵀ_ : {Γ : Cx} → Ty Γ → Ty Γ → Set where
  El-⌜Unit⌝ : El (⌜Unit⌝ {Γ}) ⟶ᵀ Unit
  El-⌜Π⌝    : (c : Tm Γ) (d : Tm (Γ ∙)) → El (⌜Π⌝ c d) ⟶ᵀ Π (El c) (El d)
  ξ-El      : {t t' : Tm Γ} → t ⟶ t' → El t ⟶ᵀ El t'
  ξ-Πˡ      : {A A' : Ty Γ} {B : Ty (Γ ∙)} → A ⟶ᵀ A' → Π A B ⟶ᵀ Π A' B
  ξ-Πʳ      : {A : Ty Γ} {B B' : Ty (Γ ∙)} → B ⟶ᵀ B' → Π A B ⟶ᵀ Π A B'

infix 3 _⟶ᵀ*_
data _⟶ᵀ*_ : {Γ : Cx} → Ty Γ → Ty Γ → Set where
  doneᵀ : {A : Ty Γ} → A ⟶ᵀ* A
  stepᵀ : {A B C : Ty Γ} → A ⟶ᵀ B → B ⟶ᵀ* C → A ⟶ᵀ* C

infix 3 _≅ᵀ_
data _≅ᵀ_ : {Γ : Cx} → Ty Γ → Ty Γ → Set where
  credᵀ : {A B : Ty Γ}   → A ⟶ᵀ B → A ≅ᵀ B
  crflᵀ : {A : Ty Γ}     → A ≅ᵀ A
  csymᵀ : {A B : Ty Γ}   → A ≅ᵀ B → B ≅ᵀ A
  ctrnᵀ : {A B C : Ty Γ} → A ≅ᵀ B → B ≅ᵀ C → A ≅ᵀ C

red→≅ᵀ : {A B : Ty Γ} → A ⟶ᵀ* B → A ≅ᵀ B
red→≅ᵀ doneᵀ       = crflᵀ
red→≅ᵀ (stepᵀ r p) = ctrnᵀ (credᵀ r) (red→≅ᵀ p)

------------------------------------------------------------------------
-- Typed contexts and the typing judgment.
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
  ⊢var   : ∀ {Γ x A}   → Γ ∋ x ∷ A → Γ ⊢ var x ∷ A
  ⊢tt    : ∀ {Γ}       → Γ ⊢ tt ∷ Unit
  ⊢lam   : ∀ {Γ A B t} → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B
  ⊢app   : ∀ {Γ A B t u} → Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A →
                           Γ ⊢ app t u ∷ subTy (single u) B
  -- codes inhabit the universe; `⌜Π⌝`'s codomain code is DEPENDENT.
  ⊢⌜Unit⌝ : ∀ {Γ}      → Γ ⊢ ⌜Unit⌝ ∷ U
  ⊢⌜Π⌝    : ∀ {Γ c d}  → Γ ⊢ c ∷ U → (Γ ▹ El c) ⊢ d ∷ U → Γ ⊢ ⌜Π⌝ c d ∷ U
  ⊢conv  : ∀ {Γ t A B} → Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B

------------------------------------------------------------------------
-- Demonstrations — codes decode, and terms inhabit decoded types.
------------------------------------------------------------------------

-- `⌜Unit⌝ ∷ U`, and it decodes to `Unit`.
⊢⌜Unit⌝-code : ◇ ⊢ ⌜Unit⌝ ∷ U
⊢⌜Unit⌝-code = ⊢⌜Unit⌝

decode-Unit : El (⌜Unit⌝ {ε}) ≅ᵀ Unit
decode-Unit = credᵀ El-⌜Unit⌝

-- `tt ∷ El ⌜Unit⌝` — a term of the DECODED type, via conversion.
⊢tt-at-El : ◇ ⊢ tt ∷ El ⌜Unit⌝
⊢tt-at-El = ⊢conv ⊢tt (csymᵀ decode-Unit)

-- `⌜Π⌝ ⌜Unit⌝ ⌜Unit⌝ ∷ U` — a code for `Unit → Unit`.
⊢⌜Π⌝-code : ◇ ⊢ ⌜Π⌝ ⌜Unit⌝ ⌜Unit⌝ ∷ U
⊢⌜Π⌝-code = ⊢⌜Π⌝ ⊢⌜Unit⌝ ⊢⌜Unit⌝

-- ...and it decodes (by reduction) to `Π Unit Unit`.
decode-Π : El (⌜Π⌝ (⌜Unit⌝ {ε}) ⌜Unit⌝) ≅ᵀ Π Unit Unit
decode-Π = red→≅ᵀ (stepᵀ (El-⌜Π⌝ ⌜Unit⌝ ⌜Unit⌝)
                   (stepᵀ (ξ-Πˡ El-⌜Unit⌝)
                   (stepᵀ (ξ-Πʳ El-⌜Unit⌝) doneᵀ)))

-- `λx.x ∷ Π Unit Unit`, hence `∷ El (⌜Π⌝ ⌜Unit⌝ ⌜Unit⌝)` by conversion —
-- a term inhabiting a NAMED (coded) type.
⊢id-at-El : ◇ ⊢ lam (var vz) ∷ El (⌜Π⌝ ⌜Unit⌝ ⌜Unit⌝)
⊢id-at-El = ⊢conv (⊢lam (⊢var here)) (csymᵀ decode-Π)
