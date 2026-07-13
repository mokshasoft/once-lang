------------------------------------------------------------------------
-- OCP-0009 · INDUCTION-INDUCTION (the last §5 expressivity row)
--
-- Induction-induction (II): a type `Ctx : Set` and a FAMILY OVER IT
-- `Ty : Ctx → Set` defined SIMULTANEOUSLY — `Ty`'s index is the very type
-- being defined, and constructors interleave (`_▷_` extends a context by a
-- type over it; `π` forms a type over an EXTENDED context). Neither can be
-- defined first; this is strictly beyond indexed inductive families
-- (`NbEPIndexed`) and beyond IR (`NbEPUniv` — there the second component is
-- a recursive FUNCTION; here it is a second inductively-defined FAMILY).
--
-- The example is THE motivating one (Chapman; Danielsson; Nordvall
-- Forsberg's thesis): the intrinsically-typed SYNTAX OF A DEPENDENT TYPE
-- THEORY — contexts and types over them, well-formed BY CONSTRUCTION. This
-- is exactly the shape a native `Spec/Kernel` (plan §9) would take, so this
-- row is not exotica: II is the natural home of "the DT kernel as data."
--
-- Demonstrated:
--   * the II pair `Ctx`/`Ty` (contexts ∣ ι, Π over an extended context);
--   * variables and a Π-CHAIN example (`(x:ι) → (y:ι) → ι` as one code);
--   * the SIMULTANEOUS eliminator in action: the standard model
--     `⟦_⟧C : Ctx → Set` / `⟦_⟧T : Ty Γ → ⟦Γ⟧C → Set` by mutual recursion —
--     dependent types decode to genuine Agda dependent types;
--   * a consistency-flavored corollary in the `NbEPCon0` spirit: with `ι`
--     modeled EMPTY, no closed type over the empty context that ends in `ι`
--     is inhabited — while `ι ⇒ ι` still is (`Π` guards vacuously).
--
-- Consistency-strength note (for the ledger): II, like IR, goes beyond
-- plain MLTT+inductives, but is modest here — finitary II is constructible
-- from indexed inductives + extensionality tricks in theory, and Agda
-- implements it as a sound core feature. `--safe` certifies no escape
-- hatches, as with IR.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPII where

open import normalizer.Syntax.Types
  using ( ⊤; tt; ⊥; ¬_; Σ; _,_ )

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡₁_ {A : Set₁} (x : A) : A → Set₁ where
  refl₁ : x ≡₁ x

------------------------------------------------------------------------
-- The inductive-inductive pair: contexts, and types over them.
------------------------------------------------------------------------

infixl 5 _▷_
data Ctx : Set
data Ty  : Ctx → Set

data Ctx where
  ∙   : Ctx
  _▷_ : (Γ : Ctx) → Ty Γ → Ctx

data Ty where
  ι  : ∀ {Γ} → Ty Γ
  π  : ∀ {Γ} (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
  wk : ∀ {Γ A} → Ty Γ → Ty (Γ ▷ A)      -- weakening, as a constructor

------------------------------------------------------------------------
-- Example codes — well-formed by construction.
------------------------------------------------------------------------

-- `(x : ι) → ι` over the empty context.
ι⇒ι : Ty ∙
ι⇒ι = π ι (wk ι)

-- A Π-chain: `(x : ι) → (y : ι) → ι`.
ι⇒ι⇒ι : Ty ∙
ι⇒ι⇒ι = π ι (π ι (wk (wk ι)))

------------------------------------------------------------------------
-- The SIMULTANEOUS eliminator, exercised: the standard model. `ι` is
-- interpreted by a parameter — instantiated below both ways.
------------------------------------------------------------------------

module Model (I : Set) where

  ⟦_⟧C : Ctx → Set
  ⟦_⟧T : ∀ {Γ} → Ty Γ → ⟦ Γ ⟧C → Set

  ⟦ ∙ ⟧C     = ⊤
  ⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → ⟦ A ⟧T γ)

  ⟦ ι ⟧T      γ       = I
  ⟦ π A B ⟧T  γ       = (x : ⟦ A ⟧T γ) → ⟦ B ⟧T (γ , x)
  ⟦ wk A ⟧T   (γ , _) = ⟦ A ⟧T γ

-- Dependent types decode to genuine Agda dependent types:
open Model ℕ renaming (⟦_⟧C to ⟦_⟧Cℕ; ⟦_⟧T to ⟦_⟧Tℕ)

_ : ⟦ ι⇒ι⇒ι ⟧Tℕ tt ≡₁ (ℕ → ℕ → ℕ)
_ = refl₁

-- ...and are inhabited as expected.
_ : ⟦ ι⇒ι⇒ι ⟧Tℕ tt
_ = λ x y → x

------------------------------------------------------------------------
-- Consistency-flavored corollary (the `NbEPCon0` spirit at the II rung):
-- with `ι` modeled EMPTY, the base type over the empty context is
-- uninhabited — the II syntax proves nothing about an abstract base —
-- while `ι ⇒ ι` remains inhabited (vacuously).
------------------------------------------------------------------------

open Model ⊥ renaming (⟦_⟧C to ⟦_⟧C⊥; ⟦_⟧T to ⟦_⟧T⊥)

ι-empty : ¬ (⟦ ι {∙} ⟧T⊥ tt)
ι-empty b = b

ι⇒ι-inhabited : ⟦ ι⇒ι ⟧T⊥ tt
ι⇒ι-inhabited = λ x → x
