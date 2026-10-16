{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Typing — which expressions are well-typed, and the core
-- term each one means.
--
-- Bidirectional (D316, amended): an expression SYNTHESIZES its type
-- (`L ⊢ e ⇒ A ↝ t`), is CHECKED against a given type (`L ⊢ e ⇐ A ↝ t`), or
-- checks as an arrow out of a given domain, its codomain synthesized
-- (`L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t`). The modes say where a type comes from: a
-- λ only checks, an annotation turns checking into synthesis, and a
-- synthesized type may be used where a supertype is expected. Each rule names
-- the CORE TERM the expression means (`Spec.Core`); usage (linearity) is the
-- core term's, checked by the core judgment (`Spec.Surface.Program`).
--
-- The categorical generators (`id`, `fst`, `compose`, `cata`, …) are their
-- definitions in the core (`Spec.Core.Derived`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Name using (CanonicalName)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

module Once.Spec.Surface.Typing (Σ : Signature) {s : ℕ} (S : Defs s) (defName : Fin s → CanonicalName) where

open import Data.Fin using (zero; suc)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; _<_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Quantity; Many; Finite; pureᶠ; actᶠ; fin; Purity; pure; act; eff; mk-kind; _⊑π_; EffGrade)
open import Once.Spec.Name using (gen; NotGenerator)
open import Once.Spec.Type
  using (Ty; Type; Fun; KCtx; TySub; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; K; Id; _⊕_; _⊗_;
         WFFun; Respects; _⟨_⟩; _⟨_⟩F; Occurs)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Signature using (_∶_; ⌜_⌝; ⌜_⌝ᵈ)
open import Once.Spec.Float.Decimal using (decimalOf; negate)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Core.Syntax
  using (Tm; var; lam; app; let′; unit; pair; inl; inr; case; lit; lit-int; lit-float; prim; Prim;
         p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-lt; p-le; p-gt; p-ge; p-eq; p-ne;
         p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; coerce; sigop; ref; _!!_; module Schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Derived

------------------------------------------------------------------------
-- The local scope: named variables, innermost first
------------------------------------------------------------------------

data Locals (m : ℕ) : ℕ → Set where
  ∅     : Locals m 0
  _▹_∶_ : ∀ {n} → Locals m n → String → Ty m → Locals m (suc n)

-- `x` names variable `i`, of type `A`: its innermost binder (shadowing).
data _∋_⦂_at_ {m} : ∀ {n} → Locals m n → String → Ty m → Fin n → Set where
  here  : ∀ {n} {L : Locals m n} {x A} → (L ▹ x ∶ A) ∋ x ⦂ A at zero
  there : ∀ {n} {L : Locals m n} {x y A B i} → x ≢ y → L ∋ x ⦂ A at i → (L ▹ y ∶ B) ∋ x ⦂ A at suc i

-- A ground type, inside a polymorphic definition.
↑ : ∀ {m} → Type → Ty m
↑ A = A ⟨ (λ ()) ⟩

-- An arrow used `Many` times.
_⇒⟨_⟩_ : ∀ {m} → Ty m → Purity → Ty m → Ty m
A ⇒⟨ π ⟩ B = A ⇒[ mk-kind Many π ] B
infixr 30 _⇒⟨_⟩_

------------------------------------------------------------------------
-- The operators, and the heads with rules of their own
------------------------------------------------------------------------

data IntArith : BinOp → Prim → Set where
  ia-add : IntArith OpAdd p-add
  ia-sub : IntArith OpSub p-sub
  ia-mul : IntArith OpMul p-mul
  ia-div : IntArith OpDiv p-div
  ia-mod : IntArith OpMod p-mod

-- `%` has no float meaning.
data FloatArith : BinOp → Prim → Set where
  fa-add : FloatArith OpAdd p-fadd
  fa-sub : FloatArith OpSub p-fsub
  fa-mul : FloatArith OpMul p-fmul
  fa-div : FloatArith OpDiv p-fdiv

data Compare : BinOp → Prim → Set where
  cmp-lt : Compare OpLt p-lt
  cmp-le : Compare OpLe p-le
  cmp-gt : Compare OpGt p-gt
  cmp-ge : Compare OpGe p-ge
  cmp-eq : Compare OpEq p-eq
  cmp-ne : Compare OpNe p-ne

-- The generators applied by rules of their own.
specialGenerators : List String
specialGenerators = "id" ∷ "fst" ∷ "snd" ∷ "terminal" ∷ "inl" ∷ "inr" ∷ "initial"
                  ∷ "curry" ∷ "apply" ∷ "In" ∷ "cata" ∷ "ana" ∷ "Out" ∷ []

-- An application whose head is a generator with rules of its own; every
-- other application is typed by the general rules.
data SpecialHead : Expr → Set where
  sh-gen     : ∀ {g} → g ∈ specialGenerators → SpecialHead (RResolved (gen g))
  sh-pair    : ∀ {f} → SpecialHead (RApp (RResolved (gen "pair")) f)
  sh-compose : ∀ {f} → SpecialHead (RApp (RResolved (gen "compose")) f)
  sh-case    : ∀ {f} → SpecialHead (RApp (RResolved (gen "case")) f)

------------------------------------------------------------------------
-- The judgment
------------------------------------------------------------------------

module _ {m : ℕ} (Δ : KCtx m) where

  data _⊢_⇒_↝_ {n} (L : Locals m n) : Expr → Ty m → Tm S m n → Set
  data _⊢_⇐_↝_ {n} (L : Locals m n) : Expr → Ty m → Tm S m n → Set
  data _⊢_⇐_⇒[_]↦_↝_ {n} (L : Locals m n) : Expr → Ty m → Purity → Ty m → Tm S m n → Set

  ------------------------------------------------------------------
  -- Synthesis
  ------------------------------------------------------------------

  data _⊢_⇒_↝_ {n} L where
    s-int    : ∀ (i : ℤ) → L ⊢ RInt i ⇒ Int ↝ lit (lit-int i)
    s-float  : ∀ i f l → L ⊢ RFloat i f l ⇒ Float ↝ lit (lit-float (decimalOf i f l))
    s-unit   : L ⊢ RUnit ⇒ Unit ↝ unit
    s-unit-g : L ⊢ RResolved (gen "unit") ⇒ Unit ↝ unit

    -- A local variable.
    s-var : ∀ {x A i} → L ∋ x ⦂ A at i → L ⊢ RVar x ⇒ A ↝ var i

    -- A declaration of the signature, at its declared type.
    s-sigop : ∀ {c t} → NotGenerator c → (c ∶ t) ∈ Σ → L ⊢ RResolved c ⇒ ⌜ t ⌝ᵈ ↝ sigop c t

    -- An earlier definition with no type variables.
    s-def : ∀ {c} (d : Fin s) → defName d ≡ c → (τ : TySub (arity (S !! d)) m) → arity (S !! d) ≡ 0
          → L ⊢ RResolved c ⇒ type (S !! d) ⟨ τ ⟩ ↝ ref d τ

    s-annot : ∀ {e T t} → L ⊢ e ⇐ ↑ T ↝ t → L ⊢ RAnnot e T ⇒ ↑ T ↝ t

    s-pair : ∀ {a b A B ta tb} → L ⊢ a ⇒ A ↝ ta → L ⊢ b ⇒ B ↝ tb → L ⊢ RPair a b ⇒ A * B ↝ pair ta tb

    s-neg       : ∀ {e t} → L ⊢ e ⇒ Int ↝ t → L ⊢ RNeg e ⇒ Int ↝ prim p-neg t
    s-neg-float : ∀ i f l → L ⊢ RNeg (RFloat i f l) ⇒ Float ↝ lit (lit-float (negate (decimalOf i f l)))

    -- The binder's usage `q` is the body's (the core judgment checks it).
    s-let : ∀ {x e₁ e₂ A B t₁ t₂} (q : Quantity)
          → L ⊢ e₁ ⇒ A ↝ t₁ → (L ▹ x ∶ A) ⊢ e₂ ⇒ B ↝ t₂
          → L ⊢ RLet x e₁ e₂ ⇒ B ↝ let′ q t₁ t₂
    s-case : ∀ {e xl el xr er A B C ts tl tr} (ql qr : Quantity)
           → L ⊢ e ⇒ A + B ↝ ts
           → (L ▹ xl ∶ A) ⊢ el ⇒ C ↝ tl → (L ▹ xr ∶ B) ⊢ er ⇒ C ↝ tr
           → L ⊢ RDestruct e xl el xr er ⇒ C ↝ case ql qr ts tl tr

    s-arith : ∀ {op p e₁ e₂ t₁ t₂} → IntArith op p
            → L ⊢ e₁ ⇒ Int ↝ t₁ → L ⊢ e₂ ⇒ Int ↝ t₂ → L ⊢ RBinOp op e₁ e₂ ⇒ Int ↝ prim p (pair t₁ t₂)
    s-arith-float : ∀ {op p e₁ e₂ t₁ t₂} → FloatArith op p
                  → L ⊢ e₁ ⇒ Float ↝ t₁ → L ⊢ e₂ ⇒ Float ↝ t₂ → L ⊢ RBinOp op e₁ e₂ ⇒ Float ↝ prim p (pair t₁ t₂)
    -- An `Int` operand of a float operation widens (D125).
    s-arith-float-il : ∀ {op p e₁ e₂ t₁ t₂} → FloatArith op p
                     → L ⊢ e₁ ⇒ Int ↝ t₁ → L ⊢ e₂ ⇒ Float ↝ t₂
                     → L ⊢ RBinOp op e₁ e₂ ⇒ Float ↝ prim p (pair (prim p-i2f t₁) t₂)
    s-arith-float-ir : ∀ {op p e₁ e₂ t₁ t₂} → FloatArith op p
                     → L ⊢ e₁ ⇒ Float ↝ t₁ → L ⊢ e₂ ⇒ Int ↝ t₂
                     → L ⊢ RBinOp op e₁ e₂ ⇒ Float ↝ prim p (pair t₁ (prim p-i2f t₂))
    s-compare : ∀ {op p e₁ e₂ t₁ t₂} → Compare op p
              → L ⊢ e₁ ⇒ Int ↝ t₁ → L ⊢ e₂ ⇒ Int ↝ t₂ → L ⊢ RBinOp op e₁ e₂ ⇒ Unit + Unit ↝ prim p (pair t₁ t₂)

    -- Generators applied to a synthesizing argument.
    s-id-app       : ∀ {e T t} → L ⊢ e ⇒ T ↝ t → L ⊢ RApp (RResolved (gen "id")) e ⇒ T ↝ app (idᶜ T pure) t
    s-fst-app      : ∀ {e A B t} → L ⊢ e ⇒ A * B ↝ t → L ⊢ RApp (RResolved (gen "fst")) e ⇒ A ↝ app (fstᶜ A B pure) t
    s-snd-app      : ∀ {e A B t} → L ⊢ e ⇒ A * B ↝ t → L ⊢ RApp (RResolved (gen "snd")) e ⇒ B ↝ app (sndᶜ A B pure) t
    s-terminal-app : ∀ {e T t} → L ⊢ e ⇒ T ↝ t → L ⊢ RApp (RResolved (gen "terminal")) e ⇒ Unit ↝ app (terminalᶜ T pure) t
    s-apply-app    : ∀ {e A B t} → L ⊢ e ⇒ (A ⇒⟨ pure ⟩ B) * A ↝ t
                   → L ⊢ RApp (RResolved (gen "apply")) e ⇒ B ↝ app (applyᶜ A B) t
    -- Applying an effectful arrow builds the suspension `Unit ⇒[ π ] B`.
    s-apply-eff-app : ∀ {e A B π t} → EffGrade π → L ⊢ e ⇒ (A ⇒⟨ π ⟩ B) * A ↝ t
                    → L ⊢ RApp (RResolved (gen "apply")) e ⇒ Unit ⇒⟨ π ⟩ B ↝ app (applyEffᶜ π A B) t
    s-Out-app : ∀ {e F t} → WFFun Δ F → L ⊢ e ⇒ ν F pureᶠ ↝ t
              → L ⊢ RApp (RResolved (gen "Out")) e ⇒ ⟦ F ⟧F (ν F pureᶠ) ↝ app (outᶜ F) t
    s-Out-act-app : ∀ {e F t} → WFFun Δ F → L ⊢ e ⇒ ν F actᶠ ↝ t
                  → L ⊢ RApp (RResolved (gen "Out")) e ⇒ Unit ⇒⟨ act ⟩ ⟦ F ⟧F (ν F actᶠ) ↝ app (outActᶜ F) t

    -- Application: the head's type synthesized, the argument checked; or the
    -- argument's type synthesized and the head checked from that domain.
    s-app : ∀ {f x A B q tf tx} → ¬ SpecialHead f
          → L ⊢ f ⇒ A ⇒[ mk-kind q pure ] B ↝ tf → L ⊢ x ⇐ A ↝ tx
          → L ⊢ RApp f x ⇒ B ↝ app tf tx
    s-effApp : ∀ {f x A B π tf tx} → ¬ SpecialHead f → EffGrade π
             → L ⊢ f ⇒ A ⇒⟨ π ⟩ B ↝ tf → L ⊢ x ⇐ A ↝ tx
             → L ⊢ RApp f x ⇒ Unit ⇒⟨ π ⟩ B ↝ effAppᶜ π tf tx
    s-app-spine : ∀ {f x X T tf tx} → ¬ SpecialHead f
                → L ⊢ x ⇒ X ↝ tx → L ⊢ f ⇐ X ⇒[ pure ]↦ T ↝ tf
                → L ⊢ RApp f x ⇒ T ↝ app tf tx

  ------------------------------------------------------------------
  -- Checking
  ------------------------------------------------------------------

  data _⊢_⇐_↝_ {n} L where
    -- The generators as morphisms, at any grade.
    c-id       : ∀ {T π} → L ⊢ RResolved (gen "id") ⇐ T ⇒⟨ π ⟩ T ↝ idᶜ T π
    c-fst      : ∀ {A B π} → L ⊢ RResolved (gen "fst") ⇐ (A * B) ⇒⟨ π ⟩ A ↝ fstᶜ A B π
    c-snd      : ∀ {A B π} → L ⊢ RResolved (gen "snd") ⇐ (A * B) ⇒⟨ π ⟩ B ↝ sndᶜ A B π
    c-terminal : ∀ {A π} → L ⊢ RResolved (gen "terminal") ⇐ A ⇒⟨ π ⟩ Unit ↝ terminalᶜ A π
    c-initial  : ∀ {A π} → L ⊢ RResolved (gen "initial") ⇐ Void ⇒⟨ π ⟩ A ↝ initialᶜ A π
    c-inl      : ∀ {A B π} → L ⊢ RResolved (gen "inl") ⇐ A ⇒⟨ π ⟩ (A + B) ↝ inlᶜ A B π
    c-inr      : ∀ {A B π} → L ⊢ RResolved (gen "inr") ⇐ B ⇒⟨ π ⟩ (A + B) ↝ inrᶜ A B π

    -- `compose f g`: `g`'s codomain from its domain, or `f`'s type synthesized.
    c-compose-g : ∀ {f g A B C π tf tg}
                → L ⊢ g ⇐ A ⇒[ π ]↦ B ↝ tg → L ⊢ f ⇐ B ⇒⟨ π ⟩ C ↝ tf
                → L ⊢ RApp (RApp (RResolved (gen "compose")) f) g ⇐ A ⇒⟨ π ⟩ C ↝ composeᶜ A π tf tg
    c-compose-f : ∀ {f g A B C C′ π π′ tf tg}
                → L ⊢ f ⇒ B ⇒⟨ π′ ⟩ C′ ↝ tf → (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C)
                → L ⊢ g ⇐ A ⇒⟨ π ⟩ B ↝ tg
                → L ⊢ RApp (RApp (RResolved (gen "compose")) f) g ⇐ A ⇒⟨ π ⟩ C
                    ↝ composeᶜ A π (coerce (B ⇒⟨ π′ ⟩ C′) (B ⇒⟨ π ⟩ C) tf) tg
    c-case : ∀ {f g A B C π tf tg}
           → L ⊢ f ⇐ A ⇒⟨ π ⟩ C ↝ tf → L ⊢ g ⇐ B ⇒⟨ π ⟩ C ↝ tg
           → L ⊢ RApp (RApp (RResolved (gen "case")) f) g ⇐ (A + B) ⇒⟨ π ⟩ C ↝ caseᶜ A B π tf tg
    c-pair : ∀ {f g A B C π tf tg}
           → L ⊢ f ⇐ A ⇒⟨ π ⟩ B ↝ tf → L ⊢ g ⇐ A ⇒⟨ π ⟩ C ↝ tg
           → L ⊢ RApp (RApp (RResolved (gen "pair")) f) g ⇐ A ⇒⟨ π ⟩ (B * C) ↝ pairᶜ A π tf tg
    c-curry : ∀ {f A B C π₀ π t} → L ⊢ f ⇐ (A * B) ⇒⟨ π ⟩ C ↝ t
            → L ⊢ RApp (RResolved (gen "curry")) f ⇐ A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C) ↝ curryᶜ A B π₀ π t
    c-cata : ∀ {alg F A π t} → WFFun Δ F
           → L ⊢ alg ⇐ ⟦ F ⟧F A ⇒⟨ π ⟩ A ↝ t
           → L ⊢ RApp (RResolved (gen "cata")) alg ⇐ μ F ⇒⟨ π ⟩ A ↝ cataᶜ F π t
    -- `ana` into a stream: a coalgebra at a finite grade, into `ν F f`,
    -- built by an arrow that runs nothing more (D317).
    c-ana : ∀ {c F A π₀ f t} → π₀ ⊑π act → WFFun Δ F
          → L ⊢ c ⇐ A ⇒⟨ fin f ⟩ ⟦ F ⟧F A ↝ t
          → L ⊢ RApp (RResolved (gen "ana")) c ⇐ A ⇒⟨ π₀ ⟩ ν F f ↝ anaᶜ F A π₀ t
    -- `ana` into `Eff`: THE LOOP. Its round is a finite block that ends with
    -- a `B` or the next state; `T∞ B` is the final coalgebra of `T (B + −)`
    -- (D317).
    c-loop : ∀ {c A B t}
           → L ⊢ c ⇐ A ⇒⟨ act ⟩ (B + A) ↝ t
           → L ⊢ RApp (RResolved (gen "ana")) c ⇐ A ⇒⟨ eff ⟩ B ↝ loopᶜ A t

    -- A synthesized type where a supertype is expected: its conversion.
    c-sub : ∀ {e A B t} → L ⊢ e ⇒ A ↝ t → A <: B → L ⊢ e ⇐ B ↝ coerce A B t

    c-lam : ∀ {x body A B q π t} → (L ▹ x ∶ A) ⊢ body ⇐ B ↝ t
          → L ⊢ RLam x body ⇐ A ⇒[ mk-kind q π ] B ↝ lam A q π t
    c-pair-lit : ∀ {a b A B ta tb} → L ⊢ a ⇐ A ↝ ta → L ⊢ b ⇐ B ↝ tb → L ⊢ RPair a b ⇐ A * B ↝ pair ta tb

    c-In-app : ∀ {e F t} → WFFun Δ F → L ⊢ e ⇐ ⟦ F ⟧F (μ F) ↝ t
             → L ⊢ RApp (RResolved (gen "In")) e ⇐ μ F ↝ app (inᶜ F) t
    c-apply-app : ∀ {e A B t} → L ⊢ e ⇒ (A ⇒⟨ pure ⟩ B) * A ↝ t
                → L ⊢ RApp (RResolved (gen "apply")) e ⇐ B ↝ app (applyᶜ A B) t
    c-inl-app : ∀ {e A B t} → L ⊢ e ⇐ A ↝ t → L ⊢ RApp (RResolved (gen "inl")) e ⇐ A + B ↝ app (inlᶜ A B pure) t
    c-inr-app : ∀ {e A B t} → L ⊢ e ⇐ B ↝ t → L ⊢ RApp (RResolved (gen "inr")) e ⇐ A + B ↝ app (inrᶜ A B pure) t
    c-initial-app : ∀ {e T t} → L ⊢ e ⇐ Void ↝ t → L ⊢ RApp (RResolved (gen "initial")) e ⇐ T ↝ app (initialᶜ T pure) t

    -- A polymorphic definition, at an instance that respects its kinds.
    c-poly : ∀ {c} (d : Fin s) → defName d ≡ c → 0 < arity (S !! d)
           → (τ : TySub (arity (S !! d)) m) → Respects (kinds (S !! d)) Δ τ
           → L ⊢ RResolved c ⇐ type (S !! d) ⟨ τ ⟩ ↝ ref d τ

  ------------------------------------------------------------------
  -- An arrow out of a given domain, its codomain synthesized
  ------------------------------------------------------------------

  data _⊢_⇐_⇒[_]↦_↝_ {n} L where
    d-infer : ∀ {g A A′ B π π′ t}
            → L ⊢ g ⇒ A′ ⇒⟨ π′ ⟩ B ↝ t → A <: A′ → π′ ⊑π π
            → L ⊢ g ⇐ A ⇒[ π ]↦ B ↝ coerce (A′ ⇒⟨ π′ ⟩ B) (A ⇒⟨ π ⟩ B) t
    -- A polymorphic definition whose codomain's variables all occur in its
    -- domain: the domain determines the instance.
    d-poly : ∀ {c} (d : Fin s) → defName d ≡ c → 0 < arity (S !! d)
           → ∀ {sd sc π′ A B π} → type (S !! d) ≡ sd ⇒⟨ π′ ⟩ sc
           → (∀ i → Occurs i sc → Occurs i sd)
           → (τ : TySub (arity (S !! d)) m) → Respects (kinds (S !! d)) Δ τ
           → sd ⟨ τ ⟩ ≡ A → sc ⟨ τ ⟩ ≡ B → π′ ⊑π π
           → L ⊢ RResolved c ⇐ A ⇒[ π ]↦ B ↝ coerce (A ⇒⟨ π′ ⟩ B) (A ⇒⟨ π ⟩ B) (ref d τ)
    d-lam : ∀ {x body A B π t} → (L ▹ x ∶ A) ⊢ body ⇒ B ↝ t
          → L ⊢ RLam x body ⇐ A ⇒[ π ]↦ B ↝ lam A Many π t
    d-compose : ∀ {f g A M B π tf tg}
              → L ⊢ g ⇐ A ⇒[ π ]↦ M ↝ tg → L ⊢ f ⇐ M ⇒[ π ]↦ B ↝ tf
              → L ⊢ RApp (RApp (RResolved (gen "compose")) f) g ⇐ A ⇒[ π ]↦ B ↝ composeᶜ A π tf tg
    d-id       : ∀ {A π} → L ⊢ RResolved (gen "id") ⇐ A ⇒[ π ]↦ A ↝ idᶜ A π
    d-fst      : ∀ {A B π} → L ⊢ RResolved (gen "fst") ⇐ (A * B) ⇒[ π ]↦ A ↝ fstᶜ A B π
    d-snd      : ∀ {A B π} → L ⊢ RResolved (gen "snd") ⇐ (A * B) ⇒[ π ]↦ B ↝ sndᶜ A B π
    d-terminal : ∀ {A π} → L ⊢ RResolved (gen "terminal") ⇐ A ⇒[ π ]↦ Unit ↝ terminalᶜ A π
    d-initial  : ∀ {π} → L ⊢ RResolved (gen "initial") ⇐ Void ⇒[ π ]↦ Void ↝ initialᶜ Void π
    d-case : ∀ {f g A B C π tf tg}
           → L ⊢ f ⇐ A ⇒[ π ]↦ C ↝ tf → L ⊢ g ⇐ B ⇒[ π ]↦ C ↝ tg
           → L ⊢ RApp (RApp (RResolved (gen "case")) f) g ⇐ (A + B) ⇒[ π ]↦ C ↝ caseᶜ A B π tf tg
    d-pair : ∀ {f g A B C π tf tg}
           → L ⊢ f ⇐ A ⇒[ π ]↦ B ↝ tf → L ⊢ g ⇐ A ⇒[ π ]↦ C ↝ tg
           → L ⊢ RApp (RApp (RResolved (gen "pair")) f) g ⇐ A ⇒[ π ]↦ (B * C) ↝ pairᶜ A π tf tg
    d-cata : ∀ {alg F A π t} → WFFun Δ F
           → L ⊢ alg ⇒ ⟦ F ⟧F A ⇒⟨ π ⟩ A ↝ t
           → L ⊢ RApp (RResolved (gen "cata")) alg ⇐ μ F ⇒[ π ]↦ A ↝ cataᶜ F π t
