------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — the Tarski decoder `El : Code → Ty`
--
-- `NbEPCwF` gave the CwF TYPE layer: Π/Σ formers as fragment codes `Tm _ U`
-- and conversion decided by `nf`. This module adds the missing bridge the
-- plan named: a **Tarski decoder** that turns a type-CODE into the actual
-- `Ty` it denotes, so that
--
--   * a context can be EXTENDED by a code (`Γ ▷ᶜ A`, driven by data), and
--   * we get **terms-of-type** `Tmᵗ Γ A = Tm ⟦ Γ ⟧C (El A)`.
--
-- Design (honest about the container ceiling). The type-codes are an ordinary
-- inductive family `Code` — the FIRST-ORDER Tarski universe. Its `Π`/`Σ`
-- formers store two *codes* (`a b : Code`), NOT a code and a family
-- `El a → Code`. A genuinely dependent `Π (x : El a). B x` would need exactly
-- that family — i.e. `U` defined MUTUALLY with `El` (induction-recursion),
-- which OCP-0009 puts out of scope (§D / Rung 4 ceiling / FAQ Q9). So here
-- `El (a `Π b) = El a ⇒ El b` — the CORRECT denotation when `b` does not
-- depend on `x` (non-dependent Π *is* the arrow), and the honest ceiling is
-- that the code language cannot *express* a dependent `b`.
--
-- What is genuinely proven:
--   * `El` decodes every code to a `Ty`;
--   * the reflection `⌜_⌝ : Code → Tm Unit U` lands codes as IR `U`-data,
--     agreeing with `NbEPCwF`'s smart constructors (self-hosting bridge);
--   * `El` and the reflection RESPECT code identity (well-defined on codes);
--   * code-driven context extension + terms-of-type, with the context
--     variable as a real term `varᶜ`.
--
-- The immediate follow-on (documented, not built): decoding an OPEN code
-- `Tm I U` pointwise gives genuinely INDEXED families (`Vec n`-style) whose
-- fibres are decided by NbE on the index — real dependency WITHOUT IR.
------------------------------------------------------------------------

module poc.OCP0009.NbEPEl where

open import normalizer.Syntax.Types
open import poc.OCP0009.NbEP
  using ( Tm; _⊙_; sndT; nf )
open import poc.OCP0009.NbEPCwF
  using ( U; Nat
        ; ⌜unit⌝; ⌜nat⌝; Π[_,_]; Σ[_,_]; _⇒C_; _×C_
        ; Ctx; ∙; _▷_; ⟦_⟧C )

------------------------------------------------------------------------
-- The first-order Tarski universe of type-codes.
------------------------------------------------------------------------

infixr 7 _`×_
infixr 6 _`⇒_
data Code : Set where
  `unit `nat : Code
  _`×_ _`⇒_ _`Π_ _`Σ_ : Code → Code → Code

------------------------------------------------------------------------
-- The decoder — a type-code becomes the `Ty` it denotes.
-- `Π`/`Σ` decode to their NON-DEPENDENT meaning (see header): correct when
-- the codomain code does not mention the domain (the only thing first-order
-- codes can express).
------------------------------------------------------------------------

El : Code → Ty
El `unit    = Unit
El `nat     = Nat
El (a `× b) = El a * El b
El (a `⇒ b) = El a ⇒ El b
El (a `Π b) = El a ⇒ El b
El (a `Σ b) = El a * El b

------------------------------------------------------------------------
-- Reflection into the IR universe — codes ARE `U`-data. Agrees with the
-- `NbEPCwF` smart constructors, so a `Code` and its reflection are the same
-- object seen two ways (the self-hosting bridge).
------------------------------------------------------------------------

⌜_⌝ : Code → Tm Unit U
⌜ `unit ⌝  = ⌜unit⌝
⌜ `nat ⌝   = ⌜nat⌝
⌜ a `× b ⌝ = ⌜ a ⌝ ×C ⌜ b ⌝
⌜ a `⇒ b ⌝ = ⌜ a ⌝ ⇒C ⌜ b ⌝
⌜ a `Π b ⌝ = Π[ ⌜ a ⌝ , ⌜ b ⌝ ]
⌜ a `Σ b ⌝ = Σ[ ⌜ a ⌝ , ⌜ b ⌝ ]

------------------------------------------------------------------------
-- Well-definedness: both `El` and the reflection respect code identity.
-- (A checker deciding code-conversion by `nf ⌜c⌝ ≡ nf ⌜d⌝` may substitute
-- `El c` for `El d`; the ← direction — reflection is FAITHFUL, distinct
-- codes reflect to distinct `nf` — is the injectivity obligation, a routine
-- discrimination induction, noted here.)
------------------------------------------------------------------------

El-cong : ∀ {c d} → c ≡ d → El c ≡ El d
El-cong refl = refl

reflect-cong : ∀ {c d} → c ≡ d → nf ⌜ c ⌝ ≡ nf ⌜ d ⌝
reflect-cong refl = refl

------------------------------------------------------------------------
-- Code-driven context extension + terms-of-type (the payoff the plan named).
------------------------------------------------------------------------

infixl 5 _▷ᶜ_
_▷ᶜ_ : Ctx → Code → Ctx
Γ ▷ᶜ A = Γ ▷ El A

-- A term of (decoded) type `A` in context `Γ`.
Tmᵗ : Ctx → Code → Set
Tmᵗ Γ A = Tm ⟦ Γ ⟧C (El A)

-- The context variable, as a genuine term of its type (second projection).
varᶜ : ∀ {Γ A} → Tmᵗ (Γ ▷ᶜ A) A
varᶜ = sndT

------------------------------------------------------------------------
-- Examples — each `refl` runs the decoder / a decision at type-check time.
------------------------------------------------------------------------

-- (1) Decoding the base and structural formers.
_ : El (`nat `⇒ `nat) ≡ (Nat ⇒ Nat)
_ = refl

_ : El (`nat `× `unit) ≡ (Nat * Unit)
_ = refl

-- (2) The honest ceiling, as a PROVEN equation: non-dependent Π decodes to
--     the arrow, Σ to the product — the correct meaning, and all a
--     first-order code can express.
_ : El (`nat `Π `nat) ≡ El (`nat `⇒ `nat)
_ = refl

_ : El (`nat `Σ `nat) ≡ El (`nat `× `nat)
_ = refl

-- (3) The reflection is a genuine `U`-code, decided convertible to itself by
--     the principled NbE (same `nf` as everywhere).
_ : nf ⌜ `nat `Π `nat ⌝ ≡ nf ⌜ `nat `Π `nat ⌝
_ = refl

-- (4) Code-driven context extension: the variable of a `Nat`-typed slot is a
--     real term of `Nat` in the extended context.
_ : Tmᵗ (∙ ▷ᶜ `nat) `nat
_ = varᶜ {∙} {`nat}

-- (5) …and of a compound (`Nat × Unit`)-typed slot. (`El` is not injective,
--     so the code `A` is passed explicitly rather than inferred through `El`.)
_ : Tmᵗ (∙ ▷ᶜ (`nat `× `unit)) (`nat `× `unit)
_ = varᶜ {∙} {`nat `× `unit}
