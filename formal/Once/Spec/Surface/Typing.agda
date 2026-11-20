{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Typing — which expressions are well-typed, and the core
-- term each one means.
--
-- Bidirectional (D316, amended): an expression SYNTHESIZES its type
-- (`L ⊢ e ⇒ A ↝ t`), is CHECKED against a given type (`L ⊢ e ⇐ A ↝ t`), or
-- checks as an arrow out of a given domain, its least codomain synthesized
-- (`L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t`). The modes say where a type comes from: a
-- λ only checks, an annotation turns checking into synthesis, and a
-- synthesized type may be used where a supertype is expected. Each rule names
-- the CORE TERM the expression means (`Spec.Core`); usage (linearity) is the
-- core term's, checked by the core judgment (`Spec.Surface.Program`).
--
-- ONE RULE PER FORM AND MODE (plan 0.151): which rule types an expression is
-- decided by its form, read through the classes below (`CheckHead`,
-- `DomainForm`, …), never by whether another rule fails (`Spec.Metatheory`).
-- A rejected expression breaks the one rule for its form, or its form has no
-- rule in that mode.
--
-- The generators are a table (`Spec.Surface.Generators`): the structure maps
-- are typed by three rules over it, one per mode; each combinator has its
-- universal property as its rule. Each generator means its definition in the
-- core (`Spec.Core.Derived`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Name using (CanonicalName)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

module Once.Spec.Surface.Typing (Σ : Signature) {s : ℕ} (S : Defs s) (defName : Fin s → CanonicalName) where

open import Data.Fin using (zero; suc)
open import Data.Integer using (ℤ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; _<_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Quantity; Many; Finite; fin; Purity; pure; act; eff; mk-kind; _⊑π_)
open import Once.Spec.Type
  using (Ty; Type; Fun; KCtx; TySub; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F;
         WFFun; Respects; _⟨_⟩; Occurs)
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_)
open import Once.Spec.Signature using (_∶_; ⌜_⌝ᵈ)
open import Once.Spec.Theory using (⌜_⌝ⁿ; Neg; Has; symCod; ‵neg)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Float.Decimal using (signedDecimal)
open import Once.Spec.Surface.Operator using (BinOp; BinSym; binSym)
open BinSym
open import Once.Spec.Surface.Generators
  using (Gen; kind; IsConstant; IsMap; FromDomain; FromCodomain; IsCombinator;
         Constant; Morphism; Final)
open Gen
open import Once.Spec.Core.Syntax
  using (Tm; var; lam; app; let′; pair; case; lit; lit-int; lit-float; prim; num; coerce; sigop; ref;
         _!!_; module Schema)
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
-- The classes of forms that decide the rule
------------------------------------------------------------------------

-- A name of a definition with type variables: checked at an instance, never
-- synthesized.
data PolyName (c : CanonicalName) : Set where
  poly : (d : Fin s) → defName d ≡ c → 0 < arity (S !! d) → PolyName c

-- ... whose codomain's variables all occur in its domain: the domain
-- determines the instance.
data PolyFromDomain (c : CanonicalName) : Set where
  poly-dom : (d : Fin s) → defName d ≡ c → 0 < arity (S !! d)
           → ∀ {sd sc π′} → type (S !! d) ≡ sd ⇒⟨ π′ ⟩ sc → (∀ i → Occurs i sc → Occurs i sd)
           → PolyFromDomain c

-- A combinator given fewer arms than it takes: its application is the
-- combinator's own form, not an application.
data PartialCombinator : Expr → Set where
  pc-bare : ∀ {g k} → IsCombinator k (kind g) → PartialCombinator (RGen g)
  pc-one  : ∀ {g a} → IsCombinator 2 (kind g) → PartialCombinator (RApp (RGen g) a)

-- A head that never synthesizes: applied by the argument's type.
data CheckHead : Expr → Set where
  ch-lam   : ∀ {x b} → CheckHead (RLam x b)
  ch-poly  : ∀ {c} → PolyName c → CheckHead (RResolved c)
  ch-map   : ∀ {g} → IsMap (kind g) → CheckHead (RGen g)
  ch-comb₁ : ∀ {g a} → IsCombinator 1 (kind g) → CheckHead (RApp (RGen g) a)
  ch-comb₂ : ∀ {g a b} → IsCombinator 2 (kind g) → CheckHead (RApp (RApp (RGen g) a) b)

-- A form that synthesizes and also has a checking rule of its own, which is
-- the one used when it is checked.
data OwnCheck : Expr → Set where
  oc-pair : ∀ {a b} → OwnCheck (RPair a b)
  oc-map  : ∀ {g e} → FromCodomain (kind g) → OwnCheck (RApp (RGen g) e)

-- A form that is checked only through its synthesized type (or, a pair, by
-- its parts): if it checks, it synthesizes.
data SynthForm : Expr → Set where
  sf-int     : ∀ {i} → SynthForm (RInt i)
  sf-float   : ∀ {sg i f l} → SynthForm (RFloat sg i f l)
  sf-unit    : SynthForm RUnit
  sf-var     : ∀ {x} → SynthForm (RVar x)
  sf-name    : ∀ {c} → ¬ PolyName c → SynthForm (RResolved c)
  sf-const   : ∀ {g} → IsConstant (kind g) → SynthForm (RGen g)
  sf-annot   : ∀ {e T} → SynthForm (RAnnot e T)
  sf-pair    : ∀ {a b} → SynthForm a → SynthForm b → SynthForm (RPair a b)
  sf-neg     : ∀ {e} → SynthForm (RNeg e)
  sf-binop   : ∀ {op a b} → SynthForm (RBinOp op a b)
  sf-let     : ∀ {x a b} → SynthForm (RLet x a b)
  sf-destruct : ∀ {e xl el xr er} → SynthForm (RDestruct e xl el xr er)
  sf-app     : ∀ {f x} → ¬ PartialCombinator f → ¬ OwnCheck (RApp f x) → SynthForm (RApp f x)

-- A form with a domain-given rule.
data DomainForm : Expr → Set where
  df-synth   : ∀ {e} → SynthForm e → DomainForm e
  df-lam     : ∀ {x b} → SynthForm b → DomainForm (RLam x b)
  df-poly    : ∀ {c} → PolyFromDomain c → DomainForm (RResolved c)
  df-map     : ∀ {g} → FromDomain (kind g) → DomainForm (RGen g)
  df-compose : ∀ {f g} → DomainForm f → DomainForm g → DomainForm (RApp (RApp (RGen compose) f) g)
  df-case    : ∀ {f g} → DomainForm f → DomainForm g → DomainForm (RApp (RApp (RGen case) f) g)
  df-pair    : ∀ {f g} → DomainForm f → DomainForm g → DomainForm (RApp (RApp (RGen pair) f) g)
  df-cata    : ∀ {a} → SynthForm a → DomainForm (RApp (RGen cata) a)

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
    s-float  : ∀ sg i f l → L ⊢ RFloat sg i f l ⇒ Float ↝ lit (lit-float (signedDecimal sg i f l))
    s-unit   : L ⊢ RUnit ⇒ Unit ↝ Once.Spec.Core.Syntax.unit

    -- A constant of the table.
    s-const : ∀ {g k T t} → Constant Δ g k T t → L ⊢ RGen g ⇒ T ↝ t

    -- A local variable.
    s-var : ∀ {x A i} → L ∋ x ⦂ A at i → L ⊢ RVar x ⇒ A ↝ var i

    -- A declaration of the signature, at its declared type.
    s-sigop : ∀ {c t} → (c ∶ t) ∈ Σ → L ⊢ RResolved c ⇒ ⌜ t ⌝ᵈ ↝ sigop c t

    -- An earlier definition with no type variables.
    s-def : ∀ {c} (d : Fin s) → defName d ≡ c → (τ : TySub (arity (S !! d)) m) → arity (S !! d) ≡ 0
          → L ⊢ RResolved c ⇒ type (S !! d) ⟨ τ ⟩ ↝ ref d τ

    -- An annotation: `e` checked at `T`, which may lie above `e`'s own
    -- type. It is how a definition states a wider type for itself: the
    -- widening is written in the body, along conversions; a signature only
    -- confirms the body's type (`Spec.Surface.Program.Principal`).
    s-annot : ∀ {e T t} → L ⊢ e ⇐ ↑ T ↝ t → L ⊢ RAnnot e T ⇒ ↑ T ↝ t

    s-pair : ∀ {a b A B ta tb} → L ⊢ a ⇒ A ↝ ta → L ⊢ b ⇒ B ↝ tb → L ⊢ RPair a b ⇒ A * B ↝ pair ta tb

    -- `-e` at a number type that has `Neg`.
    s-neg : ∀ {e A t} (h : Has A Neg)
          → L ⊢ e ⇒ ⌜ A ⌝ⁿ ↝ t → L ⊢ RNeg e ⇒ ⌜ A ⌝ⁿ ↝ prim (num h ‵neg) t

    -- The binder's usage `q` is the body's (the core judgment checks it).
    s-let : ∀ {x e₁ e₂ A B t₁ t₂} (q : Quantity)
          → L ⊢ e₁ ⇒ A ↝ t₁ → (L ▹ x ∶ A) ⊢ e₂ ⇒ B ↝ t₂
          → L ⊢ RLet x e₁ e₂ ⇒ B ↝ let′ q t₁ t₂
    -- The branches meet at the join of their types, each composed with its
    -- conversion.
    s-case : ∀ {e xl el xr er A B Cl Cr C ts tl tr} (ql qr : Quantity)
           → L ⊢ e ⇒ A + B ↝ ts
           → (L ▹ xl ∶ A) ⊢ el ⇒ Cl ↝ tl → (L ▹ xr ∶ B) ⊢ er ⇒ Cr ↝ tr → Cl ⊔ Cr ≔ C
           → L ⊢ RDestruct e xl el xr er ⇒ C ↝ case ql qr ts (coerce Cl C tl) (coerce Cr C tr)

    -- A binary operator at a number type that has the operator's theory.
    s-binop : ∀ {op e₁ e₂ A t₁ t₂} (h : Has A (theory (binSym op)))
            → L ⊢ e₁ ⇒ ⌜ A ⌝ⁿ ↝ t₁ → L ⊢ e₂ ⇒ ⌜ A ⌝ⁿ ↝ t₂
            → L ⊢ RBinOp op e₁ e₂ ⇒ symCod A (shape (binSym op)) ↝ prim (num h (symbol (binSym op))) (pair t₁ t₂)
    -- Operands of different number types have no rule: an `Int` meets `Float`
    -- arithmetic through `toFloat` (D408).

    -- Application of a head that synthesizes: the argument checked at its
    -- domain; running an arrow of grade `π` gives `𝕋 π` of its codomain.
    s-app : ∀ {f x A B q π tf tx} → ¬ PartialCombinator f → ¬ CheckHead f
          → L ⊢ f ⇒ A ⇒[ mk-kind q π ] B ↝ tf → L ⊢ x ⇐ A ↝ tx
          → L ⊢ RApp f x ⇒ 𝕋 π B ↝ appᵀ π tf tx
    -- Application of a head that never synthesizes: the argument's type
    -- synthesized, and the head checked as a pure arrow out of it.
    s-app-spine : ∀ {f x X T tf tx} → CheckHead f
                → L ⊢ x ⇒ X ↝ tx → L ⊢ f ⇐ X ⇒[ pure ]↦ T ↝ tf
                → L ⊢ RApp f x ⇒ T ↝ app tf tx

  ------------------------------------------------------------------
  -- Checking
  ------------------------------------------------------------------

  data _⊢_⇐_↝_ {n} L where
    -- A structure map, at an instance of the table.
    c-map : ∀ {g k A π B t} → Morphism Δ g k A π B t → L ⊢ RGen g ⇐ A ⇒⟨ π ⟩ B ↝ t
    -- A structure map whose codomain fixes its instance, applied: the
    -- argument checked at the domain.
    c-map-app : ∀ {g k e A B tg t} → FromCodomain (kind g) → Morphism Δ g k A pure B tg
              → L ⊢ e ⇐ A ↝ t → L ⊢ RApp (RGen g) e ⇐ B ↝ app tg t

    -- `compose f g`: the middle object is `g`'s codomain from the domain when
    -- `g` has a domain-given form, `f`'s synthesized domain otherwise.
    c-compose-g : ∀ {f g A B C π tf tg} → DomainForm g
                → L ⊢ g ⇐ A ⇒[ π ]↦ B ↝ tg → L ⊢ f ⇐ B ⇒⟨ π ⟩ C ↝ tf
                → L ⊢ RApp (RApp (RGen compose) f) g ⇐ A ⇒⟨ π ⟩ C ↝ composeᶜ A π tf tg
    c-compose-f : ∀ {f g A B C C′ π π′ tf tg} → ¬ DomainForm g
                → L ⊢ f ⇒ B ⇒⟨ π′ ⟩ C′ ↝ tf → (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C)
                → L ⊢ g ⇐ A ⇒⟨ π ⟩ B ↝ tg
                → L ⊢ RApp (RApp (RGen compose) f) g ⇐ A ⇒⟨ π ⟩ C
                    ↝ composeᶜ A π (coerce (B ⇒⟨ π′ ⟩ C′) (B ⇒⟨ π ⟩ C) tf) tg
    -- The mediating morphisms.
    c-case : ∀ {f g A B C π tf tg}
           → L ⊢ f ⇐ A ⇒⟨ π ⟩ C ↝ tf → L ⊢ g ⇐ B ⇒⟨ π ⟩ C ↝ tg
           → L ⊢ RApp (RApp (RGen case) f) g ⇐ (A + B) ⇒⟨ π ⟩ C ↝ caseᶜ A B π tf tg
    c-pair : ∀ {f g A B C π tf tg}
           → L ⊢ f ⇐ A ⇒⟨ π ⟩ B ↝ tf → L ⊢ g ⇐ A ⇒⟨ π ⟩ C ↝ tg
           → L ⊢ RApp (RApp (RGen pair) f) g ⇐ A ⇒⟨ π ⟩ (B * C) ↝ pairᶜ A π tf tg
    c-curry : ∀ {f A B C π₀ π t} → L ⊢ f ⇐ (A * B) ⇒⟨ π ⟩ C ↝ t
            → L ⊢ RApp (RGen curry) f ⇐ A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C) ↝ curryᶜ A B π₀ π t
    c-cata : ∀ {alg F A π t} → WFFun Δ F
           → L ⊢ alg ⇐ ⟦ F ⟧F A ⇒⟨ π ⟩ A ↝ t
           → L ⊢ RApp (RGen cata) alg ⇐ μ F ⇒⟨ π ⟩ A ↝ cataᶜ F π t
    -- `ana c`: into the final coalgebra `X` of `G` (a stream, or `T∞ B` at
    -- `eff`), from a coalgebra of `G` (D317).
    c-ana : ∀ {c A π₀ X G ρ k t} → Final Δ A π₀ X G ρ k
          → L ⊢ c ⇐ A ⇒⟨ ρ ⟩ G A ↝ t
          → L ⊢ RApp (RGen ana) c ⇐ A ⇒⟨ π₀ ⟩ X ↝ k t

    -- A synthesized type where a supertype is expected: its conversion.
    c-sub : ∀ {e A B t} → ¬ OwnCheck e → L ⊢ e ⇒ A ↝ t → A <: B → L ⊢ e ⇐ B ↝ coerce A B t

    c-lam : ∀ {x body A B q π t} → (L ▹ x ∶ A) ⊢ body ⇐ B ↝ t
          → L ⊢ RLam x body ⇐ A ⇒[ mk-kind q π ] B ↝ lam A q π t
    c-pair-lit : ∀ {a b A B ta tb} → L ⊢ a ⇐ A ↝ ta → L ⊢ b ⇐ B ↝ tb → L ⊢ RPair a b ⇐ A * B ↝ pair ta tb

    -- A polymorphic definition, at an instance that respects its kinds.
    c-poly : ∀ {c} (d : Fin s) → defName d ≡ c → 0 < arity (S !! d)
           → (τ : TySub (arity (S !! d)) m) → Respects (kinds (S !! d)) Δ τ
           → L ⊢ RResolved c ⇐ type (S !! d) ⟨ τ ⟩ ↝ ref d τ

  ------------------------------------------------------------------
  -- An arrow out of a given domain, its least codomain synthesized
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
    -- A structure map whose domain fixes its instance, at its least codomain.
    d-map : ∀ {g k A π B t} → FromDomain (kind g) → Morphism Δ g k A π B t
          → (∀ {k′ B′} {t′ : Tm S m n} → Morphism Δ g k′ A π B′ t′ → B <:ᶜ B′)
          → L ⊢ RGen g ⇐ A ⇒[ π ]↦ B ↝ t
    d-compose : ∀ {f g A M B π tf tg}
              → L ⊢ g ⇐ A ⇒[ π ]↦ M ↝ tg → L ⊢ f ⇐ M ⇒[ π ]↦ B ↝ tf
              → L ⊢ RApp (RApp (RGen compose) f) g ⇐ A ⇒[ π ]↦ B ↝ composeᶜ A π tf tg
    -- The copairing's codomain is the join of the branches' codomains, each
    -- branch composed with its conversion.
    d-case : ∀ {f g A B Cf Cg C π tf tg}
           → L ⊢ f ⇐ A ⇒[ π ]↦ Cf ↝ tf → L ⊢ g ⇐ B ⇒[ π ]↦ Cg ↝ tg → Cf ⊔ Cg ≔ C
           → L ⊢ RApp (RApp (RGen case) f) g ⇐ (A + B) ⇒[ π ]↦ C
               ↝ caseᶜ A B π (coerce (A ⇒⟨ π ⟩ Cf) (A ⇒⟨ π ⟩ C) tf) (coerce (B ⇒⟨ π ⟩ Cg) (B ⇒⟨ π ⟩ C) tg)
    d-pair : ∀ {f g A B C π tf tg}
           → L ⊢ f ⇐ A ⇒[ π ]↦ B ↝ tf → L ⊢ g ⇐ A ⇒[ π ]↦ C ↝ tg
           → L ⊢ RApp (RApp (RGen pair) f) g ⇐ A ⇒[ π ]↦ (B * C) ↝ pairᶜ A π tf tg
    -- The fold's codomain is the algebra's: the least `A` it is an algebra on.
    d-cata : ∀ {alg F A₁ A π′ π t} → WFFun Δ F
           → L ⊢ alg ⇒ A₁ ⇒⟨ π′ ⟩ A ↝ t → ⟦ F ⟧F A <: A₁ → π′ ⊑π π
           → L ⊢ RApp (RGen cata) alg ⇐ μ F ⇒[ π ]↦ A
               ↝ cataᶜ F π (coerce (A₁ ⇒⟨ π′ ⟩ A) (⟦ F ⟧F A ⇒⟨ π ⟩ A) t)

------------------------------------------------------------------------
-- The rule a derivation ends with
------------------------------------------------------------------------

-- The rules by name, per mode: what a rejection names (plan 0.149), and what
-- `Spec.Metatheory` claims is decided by the form (`one-rule`).
module Rule where
  data Synth : Set where
    s-int s-float s-unit s-const s-var s-sigop s-def s-annot s-pair s-neg s-let s-case s-binop
      s-app s-app-spine : Synth

  data Check : Set where
    c-map c-map-app c-compose-g c-compose-f c-case c-pair c-curry c-cata c-ana c-sub c-lam c-pair-lit
      c-poly : Check

  data Domain : Set where
    d-infer d-poly d-lam d-map d-compose d-case d-pair d-cata : Domain

module _ {m : ℕ} {Δ : KCtx m} {n} {L : Locals m n} where

  ruleOf⇒ : ∀ {e A t} → _⊢_⇒_↝_ Δ L e A t → Rule.Synth
  ruleOf⇒ (s-int _)             = Rule.s-int
  ruleOf⇒ (s-float _ _ _ _)     = Rule.s-float
  ruleOf⇒ s-unit                = Rule.s-unit
  ruleOf⇒ (s-const _)           = Rule.s-const
  ruleOf⇒ (s-var _)             = Rule.s-var
  ruleOf⇒ (s-sigop _)           = Rule.s-sigop
  ruleOf⇒ (s-def _ _ _ _)       = Rule.s-def
  ruleOf⇒ (s-annot _)           = Rule.s-annot
  ruleOf⇒ (s-pair _ _)          = Rule.s-pair
  ruleOf⇒ (s-neg _ _)           = Rule.s-neg
  ruleOf⇒ (s-let _ _ _)         = Rule.s-let
  ruleOf⇒ (s-case _ _ _ _ _ _)  = Rule.s-case
  ruleOf⇒ (s-binop _ _ _)       = Rule.s-binop
  ruleOf⇒ (s-app _ _ _ _)       = Rule.s-app
  ruleOf⇒ (s-app-spine _ _ _)   = Rule.s-app-spine

  ruleOf⇐ : ∀ {e A t} → _⊢_⇐_↝_ Δ L e A t → Rule.Check
  ruleOf⇐ (c-map _)                 = Rule.c-map
  ruleOf⇐ (c-map-app _ _ _)         = Rule.c-map-app
  ruleOf⇐ (c-compose-g _ _ _)       = Rule.c-compose-g
  ruleOf⇐ (c-compose-f _ _ _ _)     = Rule.c-compose-f
  ruleOf⇐ (c-case _ _)              = Rule.c-case
  ruleOf⇐ (c-pair _ _)              = Rule.c-pair
  ruleOf⇐ (c-curry _)               = Rule.c-curry
  ruleOf⇐ (c-cata _ _)              = Rule.c-cata
  ruleOf⇐ (c-ana _ _)               = Rule.c-ana
  ruleOf⇐ (c-sub _ _ _)             = Rule.c-sub
  ruleOf⇐ (c-lam _)                 = Rule.c-lam
  ruleOf⇐ (c-pair-lit _ _)          = Rule.c-pair-lit
  ruleOf⇐ (c-poly _ _ _ _ _)        = Rule.c-poly

  ruleOf↦ : ∀ {e A π B t} → _⊢_⇐_⇒[_]↦_↝_ Δ L e A π B t → Rule.Domain
  ruleOf↦ (d-infer _ _ _)                     = Rule.d-infer
  ruleOf↦ (d-poly _ _ _ _ _ _ _ _ _ _)        = Rule.d-poly
  ruleOf↦ (d-lam _)                           = Rule.d-lam
  ruleOf↦ (d-map _ _ _)                       = Rule.d-map
  ruleOf↦ (d-compose _ _)                     = Rule.d-compose
  ruleOf↦ (d-case _ _ _)                      = Rule.d-case
  ruleOf↦ (d-pair _ _)                        = Rule.d-pair
  ruleOf↦ (d-cata _ _ _ _)                    = Rule.d-cata
