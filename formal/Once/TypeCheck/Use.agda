-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Use — how many times a typed expression uses each local
-- (plan 0.122 §2b-3).
--
-- The Spec's surface typing (`Spec.Surface.Typing`) names the core term an
-- expression means and tracks no usage: the core typing checks it. The
-- compiler needs the usage of each subexpression to realize it point-free
-- (an arrow's environment is the product of the locals it uses), so it
-- annotates the Spec's derivation with it: `Use d Ψ` says the expression `d`
-- types uses its locals `Ψ` times, one constructor per rule of the Spec's
-- judgment, carrying only how the rule combines its premises' usages.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx)

module Once.TypeCheck.Use (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) {m : ℕ} (Δ : KCtx m) where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; One; Many)
open import Once.Spec.Context using (Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; Ctx; _▸_; lookup)
import Once.Spec.Context
open import Once.Internal.Context using (_⊔ᵘ_)
open import Once.Type.Grade using (_≤qᵇ_)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU hiding (_⊢_⇒_↝_; _⊢_⇐_↝_; _⊢_⇐_⇒[_]↦_↝_)
open import Once.Spec.Type using (Ty)
open import Once.Spec.Grade using (Purity)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Spec.Core.Syntax using (Tm)
open import Once.Spec.Type using (Type)
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Internal.Type using (wk₀)
open import Once.Internal.Type.WellFormed using (IsConcrete)

-- The Spec's judgment, at the kinds `Δ`.
_⊢_⇒_↝_ : ∀ {n} → Locals m n → Expr → Ty m → Tm S m n → Set
_⊢_⇒_↝_ = SU._⊢_⇒_↝_ Δ

_⊢_⇐_↝_ : ∀ {n} → Locals m n → Expr → Ty m → Tm S m n → Set
_⊢_⇐_↝_ = SU._⊢_⇐_↝_ Δ

_⊢_⇐_⇒[_]↦_↝_ : ∀ {n} → Locals m n → Expr → Ty m → Purity → Ty m → Tm S m n → Set
_⊢_⇐_⇒[_]↦_↝_ = SU._⊢_⇐_⇒[_]↦_↝_ Δ

-- The locals' types, as the context the realization runs in.
ctxOf : ∀ {n} → Locals m n → Ctx m n
ctxOf ∅           = Once.Spec.Context.∅
ctxOf (L ▹ _ ∶ A) = ctxOf L ▸ A

-- The local a name finds has the type the context gives it.
lookup-at : ∀ {n} {L : Locals m n} {x A i} → L ∋ x ⦂ A at i → lookup (ctxOf L) i ≡ A
lookup-at here        = refl
lookup-at (there _ v) = lookup-at v

------------------------------------------------------------------------
-- The annotation
------------------------------------------------------------------------

data Use⇒ {n} {L : Locals m n} : ∀ {e A t} → L ⊢ e ⇒ A ↝ t → Usage n → Set
data Use⇐ {n} {L : Locals m n} : ∀ {e A t} → L ⊢ e ⇐ A ↝ t → Usage n → Set
data Use↦ {n} {L : Locals m n} : ∀ {e A π B t} → L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t → Usage n → Set

data Use⇒ {n} {L} where
  u-int      : ∀ {i} → Use⇒ (s-int i) zeroUsage
  u-float    : ∀ {i f l} → Use⇒ (s-float i f l) zeroUsage
  u-unit     : Use⇒ s-unit zeroUsage
  u-unit-g   : Use⇒ s-unit-g zeroUsage
  -- A local is used once.
  u-var      : ∀ {x A i} {v : L ∋ x ⦂ A at i} → Use⇒ (s-var v) (singleUse i One)
  -- A declaration of the signature, read at the ground type it declares.
  u-sigop    : ∀ {c t ng mem} {T : Type} → IsConcrete T → ⌜ t ⌝ᵈ ≡ wk₀ {m} T → Use⇒ (s-sigop {c = c} {t = t} ng mem) zeroUsage
  u-def      : ∀ {c d e τ a} → Use⇒ (s-def {c = c} d e τ a) zeroUsage
  u-annot    : ∀ {e T t} {d : L ⊢ e ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇒ (s-annot {T = T} d) Ψ
  u-pair     : ∀ {a b A B ta tb} {da : L ⊢ a ⇒ A ↝ ta} {db : L ⊢ b ⇒ B ↝ tb} {Ψ₁ Ψ₂}
             → Use⇒ da Ψ₁ → Use⇒ db Ψ₂ → Use⇒ (s-pair da db) (Ψ₁ +ᵘ Ψ₂)
  u-neg      : ∀ {e t} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-neg d) Ψ
  u-neg-float : ∀ {i f l} → Use⇒ (s-neg-float i f l) zeroUsage
  -- The body's usage of the bound variable scales the bound expression's.
  u-let      : ∀ {x e₁ e₂ A B t₁ t₂ q} {d₁ : L ⊢ e₁ ⇒ A ↝ t₁} {d₂ : (L ▹ x ∶ A) ⊢ e₂ ⇒ B ↝ t₂} {Ψ₁ Ψ₂}
             → Use⇒ d₁ Ψ₁ → Use⇒ d₂ (q ∷ Ψ₂) → Use⇒ (s-let q d₁ d₂) (Ψ₂ +ᵘ (q *ᵘ Ψ₁))
  -- The branches run at the join of their usages.
  u-case     : ∀ {e xl el xr er A B Cl Cr C ts tl tr ql qr}
               {ds : L ⊢ e ⇒ _ ↝ ts} {dl : (L ▹ xl ∶ A) ⊢ el ⇒ Cl ↝ tl} {dr : (L ▹ xr ∶ B) ⊢ er ⇒ Cr ↝ tr} {j}
               {Ψs Ψₗ Ψᵣ}
             → Use⇒ ds Ψs → Use⇒ dl (ql ∷ Ψₗ) → Use⇒ dr (qr ∷ Ψᵣ)
             → Use⇒ (s-case {C = C} ql qr ds dl dr j) (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
  u-arith    : ∀ {op p e₁ e₂ t₁ t₂} {o} {d₁ : L ⊢ e₁ ⇒ _ ↝ t₁} {d₂ : L ⊢ e₂ ⇒ _ ↝ t₂} {Ψ₁ Ψ₂}
             → Use⇒ d₁ Ψ₁ → Use⇒ d₂ Ψ₂ → Use⇒ (s-arith {op = op} {p = p} o d₁ d₂) (Ψ₁ +ᵘ Ψ₂)
  u-arith-float : ∀ {op p e₁ e₂ t₁ t₂} {o} {d₁ : L ⊢ e₁ ⇒ _ ↝ t₁} {d₂ : L ⊢ e₂ ⇒ _ ↝ t₂} {Ψ₁ Ψ₂}
                → Use⇒ d₁ Ψ₁ → Use⇒ d₂ Ψ₂ → Use⇒ (s-arith-float {op = op} {p = p} o d₁ d₂) (Ψ₁ +ᵘ Ψ₂)
  u-arith-float-il : ∀ {op p e₁ e₂ t₁ t₂} {o} {d₁ : L ⊢ e₁ ⇒ _ ↝ t₁} {d₂ : L ⊢ e₂ ⇒ _ ↝ t₂} {Ψ₁ Ψ₂}
                   → Use⇒ d₁ Ψ₁ → Use⇒ d₂ Ψ₂ → Use⇒ (s-arith-float-il {op = op} {p = p} o d₁ d₂) (Ψ₁ +ᵘ Ψ₂)
  u-arith-float-ir : ∀ {op p e₁ e₂ t₁ t₂} {o} {d₁ : L ⊢ e₁ ⇒ _ ↝ t₁} {d₂ : L ⊢ e₂ ⇒ _ ↝ t₂} {Ψ₁ Ψ₂}
                   → Use⇒ d₁ Ψ₁ → Use⇒ d₂ Ψ₂ → Use⇒ (s-arith-float-ir {op = op} {p = p} o d₁ d₂) (Ψ₁ +ᵘ Ψ₂)
  u-compare  : ∀ {op p e₁ e₂ t₁ t₂} {o} {d₁ : L ⊢ e₁ ⇒ _ ↝ t₁} {d₂ : L ⊢ e₂ ⇒ _ ↝ t₂} {Ψ₁ Ψ₂}
             → Use⇒ d₁ Ψ₁ → Use⇒ d₂ Ψ₂ → Use⇒ (s-compare {op = op} {p = p} o d₁ d₂) (Ψ₁ +ᵘ Ψ₂)
  -- A generator applied: its argument, in an application.
  u-id-app       : ∀ {e T t} {d : L ⊢ e ⇒ T ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-id-app d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-fst-app      : ∀ {e A B t} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-fst-app {A = A} {B = B} d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-snd-app      : ∀ {e A B t} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-snd-app {A = A} {B = B} d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-terminal-app : ∀ {e T t} {d : L ⊢ e ⇒ T ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-terminal-app d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-apply-app    : ∀ {e A B t} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-apply-app {A = A} {B = B} d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-apply-eff-app : ∀ {e A B π t g} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ
                  → Use⇒ (s-apply-eff-app {A = A} {B = B} {π = π} g d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-Out-app      : ∀ {e F t w} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-Out-app {F = F} w d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-Out-act-app  : ∀ {e F t w} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-Out-act-app {F = F} w d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  -- An application uses its argument as often as the arrow's quantity says.
  u-app      : ∀ {f x A B q tf tx ns} {df : L ⊢ f ⇒ _ ↝ tf} {dx : L ⊢ x ⇐ A ↝ tx} {Ψ₁ Ψ₂}
             → Use⇒ df Ψ₁ → Use⇐ dx Ψ₂ → Use⇒ (s-app {B = B} {q = q} ns df dx) (Ψ₁ +ᵘ (q *ᵘ Ψ₂))
  u-effApp   : ∀ {f x A B π tf tx ns g} {df : L ⊢ f ⇒ _ ↝ tf} {dx : L ⊢ x ⇐ A ↝ tx} {Ψ₁ Ψ₂}
             → Use⇒ df Ψ₁ → Use⇐ dx Ψ₂ → Use⇒ (s-effApp {B = B} {π = π} ns g df dx) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  u-app-spine : ∀ {f x X T tf tx ns} {dx : L ⊢ x ⇒ X ↝ tx} {df : L ⊢ f ⇐ X ⇒[ _ ]↦ T ↝ tf} {Ψ₁ Ψ₂}
              → Use⇒ dx Ψ₂ → Use↦ df Ψ₁ → Use⇒ (s-app-spine ns dx df) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))

data Use⇐ {n} {L} where
  u-id       : ∀ {T π} → Use⇐ (c-id {T = T} {π = π}) zeroUsage
  u-fst      : ∀ {A B π} → Use⇐ (c-fst {A = A} {B = B} {π = π}) zeroUsage
  u-snd      : ∀ {A B π} → Use⇐ (c-snd {A = A} {B = B} {π = π}) zeroUsage
  u-terminal : ∀ {A π} → Use⇐ (c-terminal {A = A} {π = π}) zeroUsage
  u-initial  : ∀ {A π} → Use⇐ (c-initial {A = A} {π = π}) zeroUsage
  u-inl      : ∀ {A B π} → Use⇐ (c-inl {A = A} {B = B} {π = π}) zeroUsage
  u-inr      : ∀ {A B π} → Use⇐ (c-inr {A = A} {B = B} {π = π}) zeroUsage
  -- A composition runs `g` once per use of the composite.
  u-compose-g : ∀ {f g A B C π tf tg} {dg : L ⊢ g ⇐ A ⇒[ π ]↦ B ↝ tg} {df : L ⊢ f ⇐ _ ↝ tf} {Ψ₁ Ψ₂}
              → Use↦ dg Ψ₂ → Use⇐ df Ψ₁ → Use⇐ (c-compose-g {C = C} dg df) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  u-compose-f : ∀ {f g A B C C′ π π′ tf tg} {df : L ⊢ f ⇒ _ ↝ tf} {p} {dg : L ⊢ g ⇐ _ ↝ tg} {Ψ₁ Ψ₂}
              → Use⇒ df Ψ₁ → Use⇐ dg Ψ₂
              → Use⇐ (c-compose-f {A = A} {B = B} {C = C} {C′ = C′} {π = π} {π′ = π′} df p dg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  u-case     : ∀ {f g A B C π tf tg} {df : L ⊢ f ⇐ _ ↝ tf} {dg : L ⊢ g ⇐ _ ↝ tg} {Ψ₁ Ψ₂}
             → Use⇐ df Ψ₁ → Use⇐ dg Ψ₂ → Use⇐ (c-case {A = A} {B = B} {C = C} {π = π} df dg) (Ψ₁ +ᵘ Ψ₂)
  u-pair     : ∀ {f g A B C π tf tg} {df : L ⊢ f ⇐ _ ↝ tf} {dg : L ⊢ g ⇐ _ ↝ tg} {Ψ₁ Ψ₂}
             → Use⇐ df Ψ₁ → Use⇐ dg Ψ₂ → Use⇐ (c-pair {A = A} {B = B} {C = C} {π = π} df dg) (Ψ₁ +ᵘ Ψ₂)
  u-curry    : ∀ {f A B C π₀ π t} {d : L ⊢ f ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-curry {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} d) Ψ
  -- The recursion formers run their arm once per layer.
  u-cata     : ∀ {alg F A π t w} {d : L ⊢ alg ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-cata {F = F} {A = A} {π = π} w d) (Many *ᵘ Ψ)
  u-ana      : ∀ {c F A π₀ f t g w} {d : L ⊢ c ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-ana {F = F} {A = A} {π₀ = π₀} {f = f} g w d) (Many *ᵘ Ψ)
  u-loop     : ∀ {c A B t} {d : L ⊢ c ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-loop {A = A} {B = B} d) (Many *ᵘ Ψ)
  u-sub      : ∀ {e A B t} {d : L ⊢ e ⇒ A ↝ t} {p} {Ψ} → Use⇒ d Ψ → Use⇐ (c-sub {B = B} d p) Ψ
  -- A lambda binds a variable its body uses at most as often as the arrow allows.
  u-lam      : ∀ {x body A B q π t} {d : (L ▹ x ∶ A) ⊢ body ⇐ B ↝ t} {q′ Ψ}
             → (q′ ≤qᵇ q) ≡ true → Use⇐ d (q′ ∷ Ψ) → Use⇐ (c-lam {q = q} {π = π} d) Ψ
  u-pair-lit : ∀ {a b A B ta tb} {da : L ⊢ a ⇐ A ↝ ta} {db : L ⊢ b ⇐ B ↝ tb} {Ψ₁ Ψ₂}
             → Use⇐ da Ψ₁ → Use⇐ db Ψ₂ → Use⇐ (c-pair-lit da db) (Ψ₁ +ᵘ Ψ₂)
  u-In-app   : ∀ {e F t w} {d : L ⊢ e ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-In-app {F = F} w d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-apply-app : ∀ {e A B t} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇐ (c-apply-app {A = A} {B = B} d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-inl-app  : ∀ {e A B t} {d : L ⊢ e ⇐ A ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-inl-app {B = B} d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-inr-app  : ∀ {e A B t} {d : L ⊢ e ⇐ B ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-inr-app {A = A} d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-initial-app : ∀ {e T t} {d : L ⊢ e ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-initial-app {T = T} d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  u-poly     : ∀ {c d e a τ r} → Use⇐ (c-poly {c = c} d e a τ r) zeroUsage

data Use↦ {n} {L} where
  u-infer    : ∀ {g A A′ B π π′ t} {d : L ⊢ g ⇒ _ ↝ t} {p o} {Ψ}
             → Use⇒ d Ψ → Use↦ (d-infer {A = A} {A′ = A′} {B = B} {π = π} {π′ = π′} d p o) Ψ
  u-poly     : ∀ {c d e a sd sc π′ A B π ty oc τ r ea eb o}
             → Use↦ (d-poly {c = c} d e a {sd = sd} {sc = sc} {π′ = π′} {A = A} {B = B} {π = π} ty oc τ r ea eb o) zeroUsage
  u-lam      : ∀ {x body A B π t} {d : (L ▹ x ∶ A) ⊢ body ⇒ B ↝ t} {q′ Ψ}
             → Use⇒ d (q′ ∷ Ψ) → Use↦ (d-lam {π = π} d) Ψ
  u-compose  : ∀ {f g A M B π tf tg} {dg : L ⊢ g ⇐ A ⇒[ π ]↦ M ↝ tg} {df : L ⊢ f ⇐ M ⇒[ π ]↦ B ↝ tf} {Ψ₁ Ψ₂}
             → Use↦ dg Ψ₂ → Use↦ df Ψ₁ → Use↦ (d-compose dg df) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  u-id       : ∀ {A π} → Use↦ (d-id {A = A} {π = π}) zeroUsage
  u-fst      : ∀ {A B π} → Use↦ (d-fst {A = A} {B = B} {π = π}) zeroUsage
  u-snd      : ∀ {A B π} → Use↦ (d-snd {A = A} {B = B} {π = π}) zeroUsage
  u-terminal : ∀ {A π} → Use↦ (d-terminal {A = A} {π = π}) zeroUsage
  u-initial  : ∀ {π} → Use↦ (d-initial {π = π}) zeroUsage
  u-case     : ∀ {f g A B Cf Cg C π tf tg} {df : L ⊢ f ⇐ A ⇒[ π ]↦ Cf ↝ tf} {dg : L ⊢ g ⇐ B ⇒[ π ]↦ Cg ↝ tg} {j} {Ψ₁ Ψ₂}
             → Use↦ df Ψ₁ → Use↦ dg Ψ₂ → Use↦ (d-case {C = C} df dg j) (Ψ₁ +ᵘ Ψ₂)
  u-pair     : ∀ {f g A B C π tf tg} {df : L ⊢ f ⇐ A ⇒[ π ]↦ B ↝ tf} {dg : L ⊢ g ⇐ A ⇒[ π ]↦ C ↝ tg} {Ψ₁ Ψ₂}
             → Use↦ df Ψ₁ → Use↦ dg Ψ₂ → Use↦ (d-pair df dg) (Ψ₁ +ᵘ Ψ₂)
  u-cata     : ∀ {alg F A π t w} {d : L ⊢ alg ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use↦ (d-cata {F = F} {A = A} {π = π} w d) (Many *ᵘ Ψ)
