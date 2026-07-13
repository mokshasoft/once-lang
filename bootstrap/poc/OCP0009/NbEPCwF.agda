------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — the CwF / dependent layer (Rung 2)
--
-- The banked result (`NbEPComplete`) decides OPEN-term conversion for the
-- `{Unit, ×, +, μ}` fragment. This module cashes that where the proposal §6
-- Rung 2 asks: **Π/Σ over the total core, with types that mention terms**.
--
-- The universe of type-codes is a `μ`-type built from the existing `Func`
-- grammar (Tarski-style, exactly as `Universe.agda`), so it lives ENTIRELY
-- inside the `{Unit, ×, +, μ}` fragment — `U = μ UF`, no `⇒`. Therefore the
-- type-formers `Π`/`Σ`/`⇒`/`×` are ordinary fragment morphisms `Tm _ U`, and
-- **type conversion IS the principled `nf`** — the same, already-proven,
-- funext-free decision procedure. No new engine, no new axiom.
--
-- What is NEW here over `Universe.agda` (which was CLOSED codes only, and
-- explicitly deferred "a later type-code mentioning an earlier VARIABLE — an
-- OPEN U-valued morphism, the neutrals/NbE frontier — awaits NbE"):
--
--   * **contexts** as telescopes with an environment object `⟦ Γ ⟧C`;
--   * a **type in context** `Typ Γ = Tm ⟦ Γ ⟧C U` — an OPEN code that may
--     mention the context variable (via projections / `idT`);
--   * **dependent-type conversion under a context** `Γ ⊢ A ≅ B := nf A ≡ nf B`,
--     decided by the principled NbE — INCLUDING computation under the context
--     (β/cata on the variable), which the closed `Universe.conv` could not do;
--   * the **CwF laws**: Π/Σ respect conversion (congruence, from `≈β` +
--     `≈β-complete`), and the type-substitution laws `Π[A,B][σ] ≡ Π[A[σ],B[σ]]`
--     hold **definitionally under `nf`** (`refl`) — types are presheaves.
--
-- Honest scope. This is the type-FORMATION + type-CONVERSION-in-context layer
-- (the CwF's `Ty`/substitution structure) on the proven open-term NbE.
--   * Context extension here is by a CLOSED `Ty` (`Γ ▷ A`, `⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C * A`).
--     Extending by a *decoded* dependent code needs a Tarski decoder
--     `El : U → Ty` — the IR/self-hosting bridge, a later increment.
--   * Term-of-type (`Tm Γ A` for `A : Typ Γ`) likewise awaits `El`; this rung
--     delivers the type layer, which is where dependency lives.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPCwF where

open import normalizer.Syntax.Types
open import poc.OCP0009.NbEP
  using ( Tm; idT; _⊙_; fstT; sndT; pair; inlT; inrT; termT; InT; nf )
open import poc.OCP0009.NbEPComplete
  using ( _≈β_; βrefl; β⊙; βpair; ≈β-complete )

------------------------------------------------------------------------
-- The universe of type-codes — a polynomial functor over `Func`, in the
-- fragment. Tags: unit | nat | prod A B | arr A B | pi A B | sigma A B.
-- (Same shape as `Universe.UF`, now consumed by the principled NbE.)
------------------------------------------------------------------------

UF : Func
UF = One                       -- unit
   ⊕ One                       -- nat
   ⊕ (Id ⊗ Id)                 -- prod  A B
   ⊕ (Id ⊗ Id)                 -- arr   A B
   ⊕ (Id ⊗ Id)                 -- pi    A B   (Π)
   ⊕ (Id ⊗ Id)                 -- sigma A B   (Σ)

U : Ty
U = μ UF

------------------------------------------------------------------------
-- Smart constructors — type-formers as fragment morphisms into `U`.
-- Nullary codes are `Tm A U` for any source `A` (constant); binary formers
-- take their two argument codes over the SAME source `A`, so they apply to
-- OPEN codes (codes with a free context variable) uniformly.
------------------------------------------------------------------------

⌜unit⌝ : ∀ {A} → Tm A U
⌜unit⌝ = InT ⊙ inlT ⊙ termT

⌜nat⌝ : ∀ {A} → Tm A U
⌜nat⌝ = InT ⊙ inrT ⊙ inlT ⊙ termT

-- The binary formers' constructor SPINES — fixed morphisms `Tm (U * U) U`.
-- Factoring the spine out keeps each former a single `⊙` over `pair a b`, so
-- former-congruence reaches the pairing directly (no deep ⊙-threading).
prodSpine arrSpine piSpine sigmaSpine : Tm (U * U) U
prodSpine  = InT ⊙ inrT ⊙ inrT ⊙ inlT
arrSpine   = InT ⊙ inrT ⊙ inrT ⊙ inrT ⊙ inlT
piSpine    = InT ⊙ inrT ⊙ inrT ⊙ inrT ⊙ inrT ⊙ inlT
sigmaSpine = InT ⊙ inrT ⊙ inrT ⊙ inrT ⊙ inrT ⊙ inrT

-- Binary formers, from two codes over a common source `A`.
Π[_,_] Σ[_,_] _⇒C_ _×C_ : ∀ {A} → Tm A U → Tm A U → Tm A U
Π[ a , b ] = piSpine    ⊙ pair a b
Σ[ a , b ] = sigmaSpine ⊙ pair a b
a ⇒C b     = arrSpine   ⊙ pair a b
a ×C b     = prodSpine  ⊙ pair a b

------------------------------------------------------------------------
-- Contexts as telescopes. A context denotes an ENVIRONMENT OBJECT `⟦ Γ ⟧C`
-- (the source over which its types/substitutions live). Extension is by a
-- closed `Ty` (see header for why decoded-code extension awaits `El`).
------------------------------------------------------------------------

infixl 5 _▷_
data Ctx : Set where
  ∙   : Ctx
  _▷_ : Ctx → Ty → Ctx

⟦_⟧C : Ctx → Ty
⟦ ∙ ⟧C     = Unit
⟦ Γ ▷ A ⟧C = ⟦ Γ ⟧C * A

-- A type in context Γ: an (open) code over the environment object.
Typ : Ctx → Set
Typ Γ = Tm ⟦ Γ ⟧C U

-- A substitution Δ ⇒ Γ is an environment morphism (the CwF base category).
Sub : Ctx → Ctx → Set
Sub Δ Γ = Tm ⟦ Δ ⟧C ⟦ Γ ⟧C

-- Type substitution = precomposition (types are presheaves on the base).
infix 8 _[_]
_[_] : ∀ {Δ Γ} → Typ Γ → Sub Δ Γ → Typ Δ
A [ σ ] = A ⊙ σ

-- The last variable of `Γ ▷ U`, AS A TYPE-CODE (a genuine open code): the
-- second projection out of the extended environment.
vzU : ∀ {Γ} → Typ (Γ ▷ U)
vzU = sndT

-- Weaken a type past a fresh (closed) variable: precompose with the
-- first projection.
wkT : ∀ {Γ A} → Typ Γ → Typ (Γ ▷ A)
wkT A = A ⊙ fstT

------------------------------------------------------------------------
-- Dependent-type conversion under a context — the principled NbE, routed.
--   Γ ⊢ A ≅ B  :=  nf A ≡ nf B
-- Decided by the SAME `nf` as term conversion (Dec follows from decidable
-- equality on `Term`, as in `Decidable.agda`; here we exhibit the decisions
-- as `refl`, which literally RUNS `nf` at type-check time).
------------------------------------------------------------------------

infix 4 _⊢_≅_
_⊢_≅_ : ∀ Γ → Typ Γ → Typ Γ → Set
Γ ⊢ A ≅ B = nf A ≡ nf B

------------------------------------------------------------------------
-- CwF congruence: the type-formers RESPECT conversion. Proven from the
-- banked `≈β` congruences + `≈β-complete` — no re-derivation, exactly the
-- `Universe.agda` discipline but now for the principled NbE.
------------------------------------------------------------------------

Π-cong : ∀ {A} {a₁ a₂ b₁ b₂ : Tm A U}
       → a₁ ≈β a₂ → b₁ ≈β b₂ → Π[ a₁ , b₁ ] ≈β Π[ a₂ , b₂ ]
Π-cong ea eb = β⊙ βrefl (βpair ea eb)

Σ-cong : ∀ {A} {a₁ a₂ b₁ b₂ : Tm A U}
       → a₁ ≈β a₂ → b₁ ≈β b₂ → Σ[ a₁ , b₁ ] ≈β Σ[ a₂ , b₂ ]
Σ-cong ea eb = β⊙ βrefl (βpair ea eb)

-- …and therefore the formers respect the DECIDED conversion `≅` (via `nf`).
Π-cong-nf : ∀ {Γ} {a₁ a₂ b₁ b₂ : Typ Γ}
          → a₁ ≈β a₂ → b₁ ≈β b₂ → Γ ⊢ Π[ a₁ , b₁ ] ≅ Π[ a₂ , b₂ ]
Π-cong-nf ea eb = ≈β-complete (Π-cong ea eb)

Σ-cong-nf : ∀ {Γ} {a₁ a₂ b₁ b₂ : Typ Γ}
          → a₁ ≈β a₂ → b₁ ≈β b₂ → Γ ⊢ Σ[ a₁ , b₁ ] ≅ Σ[ a₂ , b₂ ]
Σ-cong-nf ea eb = ≈β-complete (Σ-cong ea eb)

------------------------------------------------------------------------
-- The CwF type-substitution laws. Types are presheaves: substitution
-- commutes with every former. These hold DEFINITIONALLY under `nf`
-- (`eval (F ⊙ σ) ρ` and `eval (F[σ]) ρ` reduce to the same value), so each
-- is `refl` — a machine-checked equation, not an axiom.
------------------------------------------------------------------------

Π-subst : ∀ {Δ Γ} (a b : Typ Γ) (σ : Sub Δ Γ)
        → Δ ⊢ (Π[ a , b ]) [ σ ] ≅ Π[ a [ σ ] , b [ σ ] ]
Π-subst a b σ = refl

Σ-subst : ∀ {Δ Γ} (a b : Typ Γ) (σ : Sub Δ Γ)
        → Δ ⊢ (Σ[ a , b ]) [ σ ] ≅ Σ[ a [ σ ] , b [ σ ] ]
Σ-subst a b σ = refl

⇒-subst : ∀ {Δ Γ} (a b : Typ Γ) (σ : Sub Δ Γ)
        → Δ ⊢ (a ⇒C b) [ σ ] ≅ (a [ σ ]) ⇒C (b [ σ ])
⇒-subst a b σ = refl

------------------------------------------------------------------------
-- Examples — every `refl` RUNS the dependent-conversion decision.
------------------------------------------------------------------------

-- Nat, as a concrete environment object for the closed examples.
NatF : Func
NatF = One ⊕ Id
Nat : Ty
Nat = μ NatF

-- (1) CLOSED codes — the `Universe.agda` regime, reproduced under NbE.
--     Π (Nat, Nat) ≅ Π (Nat, Nat) in the empty context.
_ : ∙ ⊢ Π[ ⌜nat⌝ , ⌜nat⌝ ] ≅ Π[ ⌜nat⌝ , ⌜nat⌝ ]
_ = refl

-- (2) OPEN codes — THE NEW CAPABILITY. In context `∙ ▷ U` the last variable
--     is a type `X := vzU`. The family `X ↦ Π(X, X)` is an OPEN code, and it
--     converts to itself under the context — decided by NbE on a neutral.
ΠXX : Typ (∙ ▷ U)
ΠXX = Π[ vzU , vzU ]

_ : (∙ ▷ U) ⊢ ΠXX ≅ ΠXX
_ = refl

-- (3) COMPUTATION UNDER THE CONTEXT — the sharpest new thing. The family
--     `X ↦ Π(fst⟨X, Nat⟩, X)` has a β-redex (`fst ∘ ⟨-,-⟩`) UNDER the context
--     variable. NbE computes it away, so it is convertible to `X ↦ Π(X, X)`.
--     `Universe.conv` (closed, no evaluation under a variable) could not see
--     this; the principled `nf` decides it by `refl`.
ΠfstXX : Typ (∙ ▷ U)
ΠfstXX = Π[ fstT ⊙ pair vzU ⌜nat⌝ , vzU ]

_ : (∙ ▷ U) ⊢ ΠfstXX ≅ ΠXX
_ = refl

-- (4) A weakened closed type ignores the fresh variable: `wkT ⌜nat⌝` in
--     `∙ ▷ U` converts to the plain `⌜nat⌝` code (constant under the context).
_ : (∙ ▷ U) ⊢ wkT ⌜nat⌝ ≅ ⌜nat⌝
_ = refl

-- (5) The substitution law, applied at a concrete instance: substituting the
--     weakening `fstT : Sub (∙ ▷ U ▷ Nat) (∙ ▷ U)` into `Π[vzU,vzU]` commutes
--     with the former (the general law `Π-subst` is proven above).
_ : (∙ ▷ U ▷ Nat) ⊢ (Π[ vzU , vzU ] [ fstT ]) ≅ Π[ vzU ⊙ fstT , vzU ⊙ fstT ]
_ = refl
