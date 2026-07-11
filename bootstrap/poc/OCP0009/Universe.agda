------------------------------------------------------------------------
-- OCP-0009 · POC-1b — a universe with Π/Σ, extending Code; type conversion
--
-- "Extend Code with CwF constructors and prove conversion", done the way §5
-- / normalizer-vs-compiler-path.md mandate: as a CONSERVATIVE EXTENSION of
-- the one reified IR, not a parallel model. Concretely, the CwF's TYPE layer
-- — a Tarski-style universe with `Π`/`Σ`/base formers — is a new `μ`-type
-- built from the *existing* `Func` grammar (Id/One/⊕/⊗). Type-codes are
-- therefore ordinary IR data (`Term Unit U`, `U = μ UF`), and:
--
--   * `Π`/`Σ` are IR CONSTRUCTORS (morphisms `piC`/`sigmaC : Term (U*U) U`);
--   * TYPE CONVERSION is `conv fo-U` — the SAME evaluator/decision procedure,
--     inheriting soundness+completeness for free (Sound.conv-decides);
--   * the CwF congruence laws (`Π`/`Σ` respect conversion) are proven from
--     the already-proven `_≋_` congruences (Sound.≋-∘, ≋-⟨,⟩).
--
-- No new decision engine, no new axiom (funext only, inherited). This is the
-- type-FORMATION + type-CONVERSION layer of the CwF on the real IR.
--
-- Scope (honest): CLOSED type-codes. A genuinely dependent context — a later
-- type-code mentioning an earlier *variable* — is an OPEN `U`-valued morphism
-- of `μ`-domain, i.e. the neutrals/NbE frontier. The *former* structure and
-- its conversion are here and proven; dependency-through-contexts awaits NbE.
------------------------------------------------------------------------

module poc.OCP0009.Universe where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
open import normalizer.Testing.Evaluator hiding (fst; snd)
open import poc.OCP0009.Conv  using (conv; FirstOrder; fo-μ)
open import poc.OCP0009.Sound using (_≋_; ≋-refl; ≋-∘; ≋-⟨,⟩; conv-sound; conv-decides)

------------------------------------------------------------------------
-- The universe functor — a polynomial functor over the existing `Func`.
-- Tags: unit | nat | prod A B | arr A B | pi A B | sigma A B.
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

fo-U : FirstOrder U
fo-U = fo-μ

------------------------------------------------------------------------
-- Smart constructors (type-formers as IR morphisms into `U`).
------------------------------------------------------------------------

⌜unit⌝ : Term Unit U
⌜unit⌝ = In ∘ inl

⌜nat⌝ : Term Unit U
⌜nat⌝ = In ∘ inr ∘ inl

prodC arrC piC sigmaC : Term (U * U) U
prodC  = In ∘ inr ∘ inr ∘ inl
arrC   = In ∘ inr ∘ inr ∘ inr ∘ inl
piC    = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inl
sigmaC = In ∘ inr ∘ inr ∘ inr ∘ inr ∘ inr

-- Applied formers, from two closed codes.
Π[_,_] Σ[_,_] _⇒C_ _×C_ :
  Term Unit U → Term Unit U → Term Unit U
Π[ A , B ] = piC    ∘ ⟨ A , B ⟩
Σ[ A , B ] = sigmaC ∘ ⟨ A , B ⟩
A ⇒C B     = arrC   ∘ ⟨ A , B ⟩
A ×C B     = prodC  ∘ ⟨ A , B ⟩

------------------------------------------------------------------------
-- Type conversion IS the proven `conv`, at the universe type.
------------------------------------------------------------------------

TyConv : Term Unit U → Term Unit U → Bool
TyConv = conv fo-U

-- Decidability of type conversion, inherited (sound + complete for `_≋_`).
TyConv-decides : (A B : Term Unit U)
               → (A ≋ B → TyConv A B ≡ true) × (TyConv A B ≡ true → A ≋ B)
TyConv-decides = conv-decides fo-U

------------------------------------------------------------------------
-- CwF congruence: the type-formers RESPECT type conversion. Proven from the
-- already-proven `_≋_` congruences — no re-derivation.
------------------------------------------------------------------------

-- (`_≋_` reduces to a function type, so the morphism implicits of ≋-∘/≋-⟨,⟩
-- are not inferrable from ≋-proofs — pin them explicitly.)
Π-cong : ∀ {A₁ A₂ B₁ B₂ : Term Unit U}
       → A₁ ≋ A₂ → B₁ ≋ B₂ → Π[ A₁ , B₁ ] ≋ Π[ A₂ , B₂ ]
Π-cong {A₁} {A₂} {B₁} {B₂} eA eB =
  ≋-∘ {f = piC} {f' = piC} {g = ⟨ A₁ , B₁ ⟩} {g' = ⟨ A₂ , B₂ ⟩}
      (≋-refl piC)
      (≋-⟨,⟩ {f = A₁} {f' = A₂} {g = B₁} {g' = B₂} eA eB)

Σ-cong : ∀ {A₁ A₂ B₁ B₂ : Term Unit U}
       → A₁ ≋ A₂ → B₁ ≋ B₂ → Σ[ A₁ , B₁ ] ≋ Σ[ A₂ , B₂ ]
Σ-cong {A₁} {A₂} {B₁} {B₂} eA eB =
  ≋-∘ {f = sigmaC} {f' = sigmaC} {g = ⟨ A₁ , B₁ ⟩} {g' = ⟨ A₂ , B₂ ⟩}
      (≋-refl sigmaC)
      (≋-⟨,⟩ {f = A₁} {f' = A₂} {g = B₁} {g' = B₂} eA eB)

------------------------------------------------------------------------
-- Executing examples (each `refl` runs `TyConv` at type-check time).
------------------------------------------------------------------------

-- Reflexivity: Π (Nat, Nat) ≡ Π (Nat, Nat).
_ : TyConv Π[ ⌜nat⌝ , ⌜nat⌝ ] Π[ ⌜nat⌝ , ⌜nat⌝ ] ≡ true
_ = refl

-- Π and Σ over the same codes are DISTINCT types (different formers).
_ : TyConv Π[ ⌜nat⌝ , ⌜nat⌝ ] Σ[ ⌜nat⌝ , ⌜nat⌝ ] ≡ false
_ = refl

-- Π disagreeing in an argument code is a distinct type.
_ : TyConv Π[ ⌜nat⌝ , ⌜nat⌝ ] Π[ ⌜unit⌝ , ⌜nat⌝ ] ≡ false
_ = refl

-- Nested former equality: Π (Nat, Nat ⇒ Nat) ≡ itself.
_ : TyConv Π[ ⌜nat⌝ , (⌜nat⌝ ⇒C ⌜nat⌝) ] Π[ ⌜nat⌝ , (⌜nat⌝ ⇒C ⌜nat⌝) ] ≡ true
_ = refl

-- An actual type-conversion PROOF object (what a checker transports along).
Π-nat-nat-refl : Π[ ⌜nat⌝ , ⌜nat⌝ ] ≋ Π[ ⌜nat⌝ , ⌜nat⌝ ]
Π-nat-nat-refl = conv-sound fo-U Π[ ⌜nat⌝ , ⌜nat⌝ ] Π[ ⌜nat⌝ , ⌜nat⌝ ] refl
