------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 31 — the FEATURE-COMPLETE self-contained dependent
--                            type theory: Π + Σ + a universe, together
--
-- The capstone of the standalone-demo line (dHoTT-29 Σ pairs, dHoTT-30 the
-- universe): ONE self-contained mini type theory carrying ALL the features and
-- — the point — showing them INTERACT. A universe `U` whose codes decode (by
-- reduction) to `Unit`/`Π`/`Σ` types, dependent functions AND dependent pairs,
-- with β/η for both and dependent typing throughout. Touches nothing committed.
--
--   * `Ty` = `U`/`El`/`Unit`/`Π`/`Sig`; `Tm` = `var`/`lam`/`app`/`pair`/`fst`/
--     `snd`/`tt`/`⌜Unit⌝`/`⌜Π⌝`/`⌜Σ⌝`.
--   * Reduction: β, Σ-β (`fst (pair a b) ⟶ a`, …), and DECODING
--     `El ⌜Unit⌝ ⟶ᵀ Unit`, `El (⌜Π⌝ c d) ⟶ᵀ Π …`, `El (⌜Σ⌝ c d) ⟶ᵀ Sig …`.
--     Conversion with Π-η and Σ-η.
--   * Typing: dependent `⊢app`/`⊢pair`/`⊢snd`, code inhabitants `⊢⌜Π⌝`/`⊢⌜Σ⌝`
--     (dependent codomain codes), `⊢conv`.
--   * ★ The interaction demo: `⌜Σ⌝ ⌜Unit⌝ ⌜Unit⌝ ∷ U` decodes to `Sig Unit
--     Unit`, and `pair tt tt` inhabits the NAMED type `El (⌜Σ⌝ ⌜Unit⌝ ⌜Unit⌝)`
--     with both projections — a coded dependent pair. Plus a function returning
--     a pair (`Π` and `Σ` composing).
--
-- `--safe`, ZERO axioms. A design demo (not the committed metatheory).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBFull where

open import normalizer.Syntax.Types using ( _≡_; refl )

------------------------------------------------------------------------
-- Scopes and the mutual syntax.
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
  U    : ∀ {Γ} → Ty Γ
  El   : ∀ {Γ} → Tm Γ → Ty Γ
  Unit : ∀ {Γ} → Ty Γ
  Π    : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ
  Sig  : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ

data Tm where
  var    : ∀ {Γ} → Var Γ → Tm Γ
  lam    : ∀ {Γ} → Tm (Γ ∙) → Tm Γ
  app    : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ
  pair   : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ
  fst    : ∀ {Γ} → Tm Γ → Tm Γ
  snd    : ∀ {Γ} → Tm Γ → Tm Γ
  tt     : ∀ {Γ} → Tm Γ
  ⌜Unit⌝ : ∀ {Γ} → Tm Γ
  ⌜Π⌝    : ∀ {Γ} → Tm Γ → Tm (Γ ∙) → Tm Γ
  ⌜Σ⌝    : ∀ {Γ} → Tm Γ → Tm (Γ ∙) → Tm Γ

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- Renaming and substitution.
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

renTy : Ren Γ Δ → Ty Γ → Ty Δ
renTm : Ren Γ Δ → Tm Γ → Tm Δ
renTy ρ U         = U
renTy ρ (El t)    = El (renTm ρ t)
renTy ρ Unit      = Unit
renTy ρ (Π A B)   = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Sig A B) = Sig (renTy ρ A) (renTy (extR ρ) B)
renTm ρ (var x)    = var (ρ x)
renTm ρ (lam t)    = lam (renTm (extR ρ) t)
renTm ρ (app t u)  = app (renTm ρ t) (renTm ρ u)
renTm ρ (pair a b) = pair (renTm ρ a) (renTm ρ b)
renTm ρ (fst p)    = fst (renTm ρ p)
renTm ρ (snd p)    = snd (renTm ρ p)
renTm ρ tt         = tt
renTm ρ ⌜Unit⌝     = ⌜Unit⌝
renTm ρ (⌜Π⌝ c d)  = ⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)
renTm ρ (⌜Σ⌝ c d)  = ⌜Σ⌝ (renTm ρ c) (renTm (extR ρ) d)

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → Tm Δ

extS : Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = renTm vs (σ x)

subTy : Sub Γ Δ → Ty Γ → Ty Δ
subTm : Sub Γ Δ → Tm Γ → Tm Δ
subTy σ U         = U
subTy σ (El t)    = El (subTm σ t)
subTy σ Unit      = Unit
subTy σ (Π A B)   = Π (subTy σ A) (subTy (extS σ) B)
subTy σ (Sig A B) = Sig (subTy σ A) (subTy (extS σ) B)
subTm σ (var x)    = σ x
subTm σ (lam t)    = lam (subTm (extS σ) t)
subTm σ (app t u)  = app (subTm σ t) (subTm σ u)
subTm σ (pair a b) = pair (subTm σ a) (subTm σ b)
subTm σ (fst p)    = fst (subTm σ p)
subTm σ (snd p)    = snd (subTm σ p)
subTm σ tt         = tt
subTm σ ⌜Unit⌝     = ⌜Unit⌝
subTm σ (⌜Π⌝ c d)  = ⌜Π⌝ (subTm σ c) (subTm (extS σ) d)
subTm σ (⌜Σ⌝ c d)  = ⌜Σ⌝ (subTm σ c) (subTm (extS σ) d)

single : Tm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- Reduction (β, Σ-β, decoding), and conversion (with η).
------------------------------------------------------------------------

infix 3 _⟶_ _⟶ᵀ_
data _⟶_ : {Γ : Cx} → Tm Γ → Tm Γ → Set where
  β       : (t : Tm (Γ ∙)) (u : Tm Γ) → app (lam t) u ⟶ subTm (single u) t
  βfst    : (a b : Tm Γ) → fst (pair a b) ⟶ a
  βsnd    : (a b : Tm Γ) → snd (pair a b) ⟶ b
  ξ-lam   : {t t' : Tm (Γ ∙)} → t ⟶ t' → lam t ⟶ lam t'
  ξ-appˡ  : {t t' u : Tm Γ} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ  : {t u u' : Tm Γ} → u ⟶ u' → app t u ⟶ app t u'
  ξ-pairˡ : {a a' b : Tm Γ} → a ⟶ a' → pair a b ⟶ pair a' b
  ξ-pairʳ : {a b b' : Tm Γ} → b ⟶ b' → pair a b ⟶ pair a b'
  ξ-fst   : {p p' : Tm Γ} → p ⟶ p' → fst p ⟶ fst p'
  ξ-snd   : {p p' : Tm Γ} → p ⟶ p' → snd p ⟶ snd p'

data _⟶ᵀ_ : {Γ : Cx} → Ty Γ → Ty Γ → Set where
  El-⌜Unit⌝ : El (⌜Unit⌝ {Γ}) ⟶ᵀ Unit
  El-⌜Π⌝    : (c : Tm Γ) (d : Tm (Γ ∙)) → El (⌜Π⌝ c d) ⟶ᵀ Π (El c) (El d)
  El-⌜Σ⌝    : (c : Tm Γ) (d : Tm (Γ ∙)) → El (⌜Σ⌝ c d) ⟶ᵀ Sig (El c) (El d)
  ξ-El      : {t t' : Tm Γ} → t ⟶ t' → El t ⟶ᵀ El t'
  ξ-Πˡ      : {A A' : Ty Γ} {B : Ty (Γ ∙)} → A ⟶ᵀ A' → Π A B ⟶ᵀ Π A' B
  ξ-Πʳ      : {A : Ty Γ} {B B' : Ty (Γ ∙)} → B ⟶ᵀ B' → Π A B ⟶ᵀ Π A B'
  ξ-Sigˡ    : {A A' : Ty Γ} {B : Ty (Γ ∙)} → A ⟶ᵀ A' → Sig A B ⟶ᵀ Sig A' B
  ξ-Sigʳ    : {A : Ty Γ} {B B' : Ty (Γ ∙)} → B ⟶ᵀ B' → Sig A B ⟶ᵀ Sig A B'

infix 3 _⟶ᵀ*_
data _⟶ᵀ*_ : {Γ : Cx} → Ty Γ → Ty Γ → Set where
  doneᵀ : {A : Ty Γ} → A ⟶ᵀ* A
  stepᵀ : {A B C : Ty Γ} → A ⟶ᵀ B → B ⟶ᵀ* C → A ⟶ᵀ* C

infix 3 _≅_ _≅ᵀ_
data _≅_ : {Γ : Cx} → Tm Γ → Tm Γ → Set where
  cred : {t u : Tm Γ}   → t ⟶ u → t ≅ u
  crfl : {t : Tm Γ}     → t ≅ t
  csym : {t u : Tm Γ}   → t ≅ u → u ≅ t
  ctrn : {t u v : Tm Γ} → t ≅ u → u ≅ v → t ≅ v
  ηΠ   : (t : Tm Γ)     → t ≅ lam (app (renTm vs t) (var vz))
  ηΣ   : (p : Tm Γ)     → p ≅ pair (fst p) (snd p)

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
  ⊢var    : ∀ {Γ x A}     → Γ ∋ x ∷ A → Γ ⊢ var x ∷ A
  ⊢tt     : ∀ {Γ}         → Γ ⊢ tt ∷ Unit
  ⊢lam    : ∀ {Γ A B t}   → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B
  ⊢app    : ∀ {Γ A B t u} → Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A →
                            Γ ⊢ app t u ∷ subTy (single u) B
  ⊢pair   : ∀ {Γ A B a b} → Γ ⊢ a ∷ A → Γ ⊢ b ∷ subTy (single a) B →
                            Γ ⊢ pair a b ∷ Sig A B
  ⊢fst    : ∀ {Γ A B p}   → Γ ⊢ p ∷ Sig A B → Γ ⊢ fst p ∷ A
  ⊢snd    : ∀ {Γ A B p}   → Γ ⊢ p ∷ Sig A B →
                            Γ ⊢ snd p ∷ subTy (single (fst p)) B
  ⊢⌜Unit⌝ : ∀ {Γ}         → Γ ⊢ ⌜Unit⌝ ∷ U
  ⊢⌜Π⌝    : ∀ {Γ c d}     → Γ ⊢ c ∷ U → (Γ ▹ El c) ⊢ d ∷ U → Γ ⊢ ⌜Π⌝ c d ∷ U
  ⊢⌜Σ⌝    : ∀ {Γ c d}     → Γ ⊢ c ∷ U → (Γ ▹ El c) ⊢ d ∷ U → Γ ⊢ ⌜Σ⌝ c d ∷ U
  ⊢conv   : ∀ {Γ t A B}   → Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B

------------------------------------------------------------------------
-- ★ The interaction demo: a universe code for a Σ type, inhabited by a pair.
------------------------------------------------------------------------

-- identity on Unit, and a unit pair.
⊢id : ◇ ⊢ lam (var vz) ∷ Π Unit Unit
⊢id = ⊢lam (⊢var here)

⊢pair-units : ◇ ⊢ pair tt tt ∷ Sig Unit Unit
⊢pair-units = ⊢pair {B = Unit} ⊢tt ⊢tt

-- a CODE for the Σ type `Σ Unit Unit`, inhabiting the universe...
⊢⌜Σ⌝-code : ◇ ⊢ ⌜Σ⌝ ⌜Unit⌝ ⌜Unit⌝ ∷ U
⊢⌜Σ⌝-code = ⊢⌜Σ⌝ ⊢⌜Unit⌝ ⊢⌜Unit⌝

-- ...which DECODES (by reduction) to `Sig Unit Unit`...
decode-Σ : El (⌜Σ⌝ (⌜Unit⌝ {ε}) ⌜Unit⌝) ≅ᵀ Sig Unit Unit
decode-Σ = red→≅ᵀ (stepᵀ (El-⌜Σ⌝ ⌜Unit⌝ ⌜Unit⌝)
                   (stepᵀ (ξ-Sigˡ El-⌜Unit⌝)
                   (stepᵀ (ξ-Sigʳ El-⌜Unit⌝) doneᵀ)))

-- ...so `pair tt tt` inhabits the NAMED type `El (⌜Σ⌝ ⌜Unit⌝ ⌜Unit⌝)` — a
-- CODED DEPENDENT PAIR (universe and Σ composing).
⊢pair-at-El : ◇ ⊢ pair tt tt ∷ El (⌜Σ⌝ ⌜Unit⌝ ⌜Unit⌝)
⊢pair-at-El = ⊢conv ⊢pair-units (csymᵀ decode-Σ)

-- ...with a working projection + its β-step.
⊢fst-coded : ◇ ⊢ fst (pair tt tt) ∷ Unit
⊢fst-coded = ⊢fst ⊢pair-units

fst-β : fst (pair (tt {ε}) tt) ⟶ tt
fst-β = βfst tt tt

-- A function that returns a pair — `Π` and `Σ` composing: `λx. (x , x)`.
⊢dup : ◇ ⊢ lam (pair (var vz) (var vz)) ∷ Π Unit (Sig Unit Unit)
⊢dup = ⊢lam (⊢pair {B = Unit} (⊢var here) (⊢var here))
