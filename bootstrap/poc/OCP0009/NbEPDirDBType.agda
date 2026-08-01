------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 21 — INTRINSIC TYPING + CONVERSION over the dependent
--                            de Bruijn base: `Id = core(Hom)` as the conv rule
--
-- The next slice after the experiment (`NbEPDirDBPi`, dHoTT-20 — which settled
-- that dependent Π/Σ substitution is strictly stable). Here the RAW dependent
-- syntax becomes a CHECKED kernel: a typing judgment with the CONVERSION rule,
-- where the definitional equality IS the design's `core(Hom)` — the symmetric
-- completion of the directed reduction `Hom = ⟶*`.
--
--   * `_⟶_` / `_⟶ᵀ_` — β-reduction on terms and its congruence onto types
--     (through `El`/`Π`/`Σ`). `Hom = _⟶*_` is the directed identity type (as
--     in every prior rung); `Core t u = Hom t u × Hom u t` its groupoid core.
--   * `_≅_` / `_≅ᵀ_` — CONVERSION = the reflexive-symmetric-transitive closure
--     of reduction: the definitional equality a typechecker uses. `hom→≅` and
--     `core→≅` witness that it is exactly the symmetric completion of `Hom`,
--     i.e. `Id = core(Hom)` made operational (the relation NbE decides).
--   * `Ctx` / `_∋_∷_` / `_⊢_∷_` — typed contexts, variable typing, and the
--     TYPING JUDGMENT: `⊢var`, `⊢lam`, DEPENDENT `⊢app` (the codomain is
--     substituted, `app t u ∷ B[u]`), and the load-bearing `⊢conv`
--     (`Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B`) — conversion entering typing.
--   * Concrete: `⊢id` (`◇ ⊢ λx.x ∷ Π base base`), a dependent-app derivation,
--     and `conv-El` — a term re-typed across a β-computation in its type, the
--     conversion rule doing real work.
--
-- Honest ceiling: this is a DECLARATIVE kernel — the typing/conversion rules,
-- with `Id = core(Hom)` as definitional equality, on the strict-substitution
-- dependent base. The metatheory (subject reduction, and DECIDING `≅ᵀ` by the
-- NbE engine — the "decided by NbE" half of the design) is the next slice; the
-- substitution machinery it needs is already proven in `NbEPDirDBPi`.
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBType where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; Sub; subTy; subTm; renTy; renTm )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Single substitution (what β and dependent `app` plug in).
------------------------------------------------------------------------

single : RTm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- Reduction — the directed `Hom`. β on terms; congruence onto types.
------------------------------------------------------------------------

infix 3 _⟶_ _⟶ᵀ_
data _⟶_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  β       : (t : RTm (Γ ∙)) (u : RTm Γ) → app (lam t) u ⟶ subTm (single u) t
  βfst    : (a b : RTm Γ) → fst (pair a b) ⟶ a
  βsnd    : (a b : RTm Γ) → snd (pair a b) ⟶ b
  ξ-lam   : {t t' : RTm (Γ ∙)} → t ⟶ t' → lam t ⟶ lam t'
  ξ-appˡ  : {t t' u : RTm Γ} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ  : {t u u' : RTm Γ} → u ⟶ u' → app t u ⟶ app t u'
  ξ-pairˡ : {a a' b : RTm Γ} → a ⟶ a' → pair a b ⟶ pair a' b
  ξ-pairʳ : {a b b' : RTm Γ} → b ⟶ b' → pair a b ⟶ pair a b'
  ξ-fst   : {p p' : RTm Γ} → p ⟶ p' → fst p ⟶ fst p'
  ξ-snd   : {p p' : RTm Γ} → p ⟶ p' → snd p ⟶ snd p'
  ξ-⌜Π⌝ˡ  : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶ c' → ⌜Π⌝ c d ⟶ ⌜Π⌝ c' d
  ξ-⌜Π⌝ʳ  : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶ d' → ⌜Π⌝ c d ⟶ ⌜Π⌝ c d'
  ξ-⌜Σ⌝ˡ  : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶ c' → ⌜Σ⌝ c d ⟶ ⌜Σ⌝ c' d
  ξ-⌜Σ⌝ʳ  : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶ d' → ⌜Σ⌝ c d ⟶ ⌜Σ⌝ c d'

data _⟶ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  El-⌜base⌝ : El (⌜base⌝ {Γ}) ⟶ᵀ base
  El-⌜Π⌝    : (c : RTm Γ) (d : RTm (Γ ∙)) → El (⌜Π⌝ c d) ⟶ᵀ Π (El c) (El d)
  El-⌜Σ⌝    : (c : RTm Γ) (d : RTm (Γ ∙)) → El (⌜Σ⌝ c d) ⟶ᵀ Σ' (El c) (El d)
  ξ-El : {t t' : RTm Γ} → t ⟶ t' → El t ⟶ᵀ El t'
  ξ-Πˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ A' → Π A B ⟶ᵀ Π A' B
  ξ-Πʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ B' → Π A B ⟶ᵀ Π A B'
  ξ-Σˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ A' → Σ' A B ⟶ᵀ Σ' A' B
  ξ-Σʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ B' → Σ' A B ⟶ᵀ Σ' A B'
  -- ★ W2: `Hom` COMPUTES, like `El` (SpikeHomTy's clauses, promoted).
  -- `Hom-U` is DIRECTED UNIVALENCE as a computation rule: a path between
  -- codes IS a map between their decodings.  `Hom-Π` is the POINTWISE family
  -- (item 2: naturality is not carried; item 3: it must not be).  There is
  -- deliberately NO rule at `base` (discrete by generation, item 4), none at
  -- `Σ'` (its unfolding needs transport, a term former W2's eliminator will
  -- introduce — deferred, not dropped), none at a stuck `El`, none at `Hom`.
  Hom-U : (c d : RTm Γ) → Hom U c d ⟶ᵀ Π (El c) (El (renTm vs d))
  Hom-Π : (A : RTy Γ) (B : RTy (Γ ∙)) (f g : RTm Γ) →
          Hom (Π A B) f g ⟶ᵀ
          Π A (Hom B (app (renTm vs f) (var vz)) (app (renTm vs g) (var vz)))
  ξ-Homᵀ : {A A' : RTy Γ} {t u : RTm Γ} → A ⟶ᵀ A' → Hom A t u ⟶ᵀ Hom A' t u
  ξ-Homˡ : {A : RTy Γ} {t t' u : RTm Γ} → t ⟶ t' → Hom A t u ⟶ᵀ Hom A t' u
  ξ-Homʳ : {A : RTy Γ} {t u u' : RTm Γ} → u ⟶ u' → Hom A t u ⟶ᵀ Hom A t u'

infix 3 _⟶*_
data _⟶*_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  done : {t : RTm Γ} → t ⟶* t
  step : {t u v : RTm Γ} → t ⟶ u → u ⟶* v → t ⟶* v

-- ⚠ READING CORRECTED (W2 §4.0): `_⟶*_` is NOT the directed identity type —
-- reduction is too small to be a path type (`SpikeVar`).  The internal `Hom`
-- is now the TYPE FORMER above.  The meta-level relation keeps only its
-- operational role, renamed `Hom⟶`; `Core⟶` is its symmetric core, and it is
-- what conversion completes.
Hom⟶ : RTm Γ → RTm Γ → Set
Hom⟶ t u = t ⟶* u

infixr 4 _,,_
record _×_ (P Q : Set) : Set where
  constructor _,,_
  field π₁ : P
        π₂ : Q

Core⟶ : RTm Γ → RTm Γ → Set
Core⟶ t u = Hom⟶ t u × Hom⟶ u t

------------------------------------------------------------------------
-- Conversion = definitional equality = the R-S-T closure of reduction.
-- This is `core(Hom)`: the symmetric completion of the directed `Hom`.
------------------------------------------------------------------------

infix 3 _≅_ _≅ᵀ_
data _≅_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  cred : {t u : RTm Γ}   → t ⟶ u → t ≅ u
  crfl : {t : RTm Γ}     → t ≅ t
  csym : {t u : RTm Γ}   → t ≅ u → u ≅ t
  ctrn : {t u v : RTm Γ} → t ≅ u → u ≅ v → t ≅ v

data _≅ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  credᵀ : {A B : RTy Γ}   → A ⟶ᵀ B → A ≅ᵀ B
  crflᵀ : {A : RTy Γ}     → A ≅ᵀ A
  csymᵀ : {A B : RTy Γ}   → A ≅ᵀ B → B ≅ᵀ A
  ctrnᵀ : {A B C : RTy Γ} → A ≅ᵀ B → B ≅ᵀ C → A ≅ᵀ C

-- Reduction (and its core) lands in the conversion the typechecker uses.
hom→≅ : {t u : RTm Γ} → Hom⟶ t u → t ≅ u
hom→≅ done       = crfl
hom→≅ (step r p) = ctrn (cred r) (hom→≅ p)

core→≅ : {t u : RTm Γ} → Core⟶ t u → t ≅ u
core→≅ c = hom→≅ (_×_.π₁ c)

------------------------------------------------------------------------
-- Typed contexts (telescopes of types) and their underlying de Bruijn depth.
------------------------------------------------------------------------

data Ctx : Set
⌊_⌋ : Ctx → Cx

data Ctx where
  ◇   : Ctx
  _▹_ : (Γ : Ctx) → RTy ⌊ Γ ⌋ → Ctx

⌊ ◇ ⌋     = ε
⌊ Γ ▹ A ⌋ = ⌊ Γ ⌋ ∙

------------------------------------------------------------------------
-- Variable typing (looked-up types are weakened into the deeper context).
------------------------------------------------------------------------

infix 3 _∋_∷_
data _∋_∷_ : (Γ : Ctx) → Var ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set where
  here  : ∀ {Γ} {A : RTy ⌊ Γ ⌋} → (Γ ▹ A) ∋ vz ∷ renTy vs A
  there : ∀ {Γ} {A B : RTy ⌊ Γ ⌋} {x} →
          Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A

------------------------------------------------------------------------
-- THE TYPING JUDGMENT — dependent `app`, and the conversion rule.
------------------------------------------------------------------------

-- TYPE FORMATION, mutual with term typing (2026-07-30, "option A").
--
-- WHY IT EXISTS. Without it the judgment derives terms at MEANINGLESS types:
-- `El (lam (var vz))` is a normal type whose code is neither a constructor nor
-- neutral, so it has no semantic counterpart, yet `⊢lam` would happily type
-- `λx.t ∷ Π (El (lam y)) B`. That makes a normalization theorem for `_⊢_∷_`
-- unprovable (`NbEPDirDBLR`; the counterexample is `SpikeSNK.¬⊩elLam`). Not an
-- inconsistency — a well-formedness defect, and this closes it.
--
-- ⚠ MINIMAL BY DESIGN: only `⊢lam` and `⊢pair` gain a premise. Everywhere else
-- the type is recovered from the subderivations by syntactic validity —
-- `⊢app`'s `Π A B` comes from the IH on the function and `⊢ty` is invertible at
-- `Π`, `⊢fst`/`⊢snd` likewise at `Σ'`, and `⊢⌜Π⌝`/`⊢⌜Σ⌝` conclude at `U`, which
-- is well-formed outright. Adding premises those rules do not need would cost
-- cascade for nothing.
infix 3 _⊢_∷_
infix 3 _⊢ty_
data _⊢_∷_ : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set
data _⊢ty_ : (Γ : Ctx) → RTy ⌊ Γ ⌋ → Set

data _⊢_∷_ where
  ⊢var  : ∀ {Γ x A}     → Γ ∋ x ∷ A → Γ ⊢ var x ∷ A
  ⊢lam  : ∀ {Γ A B t}   → Γ ⊢ty A → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B
  ⊢app  : ∀ {Γ A B t u} → Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A →
                          Γ ⊢ app t u ∷ subTy (single u) B
  ⊢pair : ∀ {Γ A B a b} → (Γ ▹ A) ⊢ty B →
                          Γ ⊢ a ∷ A → Γ ⊢ b ∷ subTy (single a) B →
                          Γ ⊢ pair a b ∷ Σ' A B
  ⊢fst  : ∀ {Γ A B p}   → Γ ⊢ p ∷ Σ' A B → Γ ⊢ fst p ∷ A
  ⊢snd  : ∀ {Γ A B p}   → Γ ⊢ p ∷ Σ' A B →
                          Γ ⊢ snd p ∷ subTy (single (fst p)) B
  ⊢⌜base⌝ : ∀ {Γ}       → Γ ⊢ ⌜base⌝ ∷ U
  ⊢⌜Π⌝  : ∀ {Γ c d}     → Γ ⊢ c ∷ U → (Γ ▹ El c) ⊢ d ∷ U → Γ ⊢ ⌜Π⌝ c d ∷ U
  ⊢⌜Σ⌝  : ∀ {Γ c d}     → Γ ⊢ c ∷ U → (Γ ▹ El c) ⊢ d ∷ U → Γ ⊢ ⌜Σ⌝ c d ∷ U
  ⊢conv : ∀ {Γ t A B}   → Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B

data _⊢ty_ where
  ty-base : ∀ {Γ}     → Γ ⊢ty base
  ty-U    : ∀ {Γ}     → Γ ⊢ty U
  ty-Π    : ∀ {Γ A B} → Γ ⊢ty A → (Γ ▹ A) ⊢ty B → Γ ⊢ty Π A B
  ty-Σ    : ∀ {Γ A B} → Γ ⊢ty A → (Γ ▹ A) ⊢ty B → Γ ⊢ty Σ' A B
  ty-El   : ∀ {Γ c}   → Γ ⊢ c ∷ U → Γ ⊢ty El c
  -- W2: `Hom` FORMATION — both endpoints at the same (well-formed) type.
  ty-Hom  : ∀ {Γ A t u} → Γ ⊢ty A → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ty Hom A t u

-- CONTEXT well-formedness. Needed because `⊢var`'s type comes from a lookup:
-- syntactic validity at `⊢var` is exactly "a lookup in a well-formed context
-- yields a well-formed type", and `⊢lam` maintains it via its new premise.
infix 3 ⊢ctx_
data ⊢ctx_ : Ctx → Set where
  c-◇ : ⊢ctx ◇
  c-▹ : ∀ {Γ A} → ⊢ctx Γ → Γ ⊢ty A → ⊢ctx (Γ ▹ A)

------------------------------------------------------------------------
-- Concrete derivations — the kernel is non-vacuous.
------------------------------------------------------------------------

-- The identity function: `◇ ⊢ λx.x ∷ Π base base`.
⊢id : ◇ ⊢ lam (var vz) ∷ Π base base
⊢id = ⊢lam ty-base (⊢var here)

-- A dependent-`app` derivation: `(◇ ▹ base) ⊢ (λx.x) y ∷ base`.
⊢appex : (◇ ▹ base) ⊢ app (lam (var vz)) (var vz) ∷ base
⊢appex = ⊢app (⊢lam ty-base (⊢var here)) (⊢var here)

-- β-reduction is directed `Hom`, and reduction ⊆ conversion. The redex
-- `(λx.x) y` reduces to `y`, and the two are convertible.
βex : app (lam (var vz)) (var vz) ⟶ var (vz {ε})
βex = β (var vz) (var vz)

conv-βex : app (lam (var vz)) (var vz) ≅ var (vz {ε})
conv-βex = hom→≅ (step βex done)

-- THE CONVERSION RULE AT WORK: a term whose type contains a β-redex may be
-- re-typed at the reduct — definitional equality (core(Hom)) identifying types
-- that differ by a computation. This is exactly why dependent typing needs
-- `Id = core(Hom)` in the conversion rule.
conv-El : ∀ {Γ t u u'} → Γ ⊢ t ∷ El u → u ⟶ u' → Γ ⊢ t ∷ El u'
conv-El d r = ⊢conv d (credᵀ (ξ-El r))
