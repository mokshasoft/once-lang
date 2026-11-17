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
open import Once.Spec.Type using (KCtx; Type)

-- `Ok`/`OkS`: the entries / declarations a reference may name — the checker's, the ones its View
-- finds (`TypeCheck.View.InView`); the Spec's rule admits any.
module Once.TypeCheck.Use (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set) {m : ℕ} (Δ : KCtx m) where

open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Grade using (Quantity; One; Many)
open import Once.Spec.Context using (Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; Ctx; _▸_; lookup)
import Once.Spec.Context
open import Once.Context using (_⊔ᵘ_)
open import Once.Type.Grade using (_≤qᵇ_)
import Once.Spec.Surface.Typing Σ S nm as SU
open import Once.Spec.Surface.Generators using (Constant; Morphism; Final)
open import Once.Spec.Sub using (_<:ᶜ_)
open SU hiding (_⊢_⇒_↝_; _⊢_⇐_↝_; _⊢_⇐_⇒[_]↦_↝_)
open import Once.Spec.Type using (Ty)
open import Once.Spec.Grade using (Purity; pure)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Spec.Core.Syntax using (Tm)
open import Once.Spec.Type using (Type)
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Type.Core using (wk₀)
open import Once.Type.Concrete using (IsConcrete)
open import Once.Type.Honest using (HonestFFI)
open import Once.Core.Decl using (declS; ⌜declS⌝)
open import Once.Spec.Signature using (_∶_)
open import Data.List.Membership.Propositional using (_∈_)

-- The Spec's judgment, at the kinds `Δ`.
_⊢_⇒_↝_ : ∀ {n} → Locals m n → Expr → Ty m → Tm S m n → Set
_⊢_⇒_↝_ = SU._⊢_⇒_↝_ Δ

_⊢_⇐_↝_ : ∀ {n} → Locals m n → Expr → Ty m → Tm S m n → Set
_⊢_⇐_↝_ = SU._⊢_⇐_↝_ Δ

_⊢_⇐_⇒[_]↦_↝_ : ∀ {n} → Locals m n → Expr → Ty m → Purity → Ty m → Tm S m n → Set
_⊢_⇐_⇒[_]↦_↝_ = SU._⊢_⇐_⇒[_]↦_↝_ Δ

-- A context with the locals' types, in order (the names forgotten).
data Shape : ∀ {n} → Locals m n → Ctx m n → Set where
  sh-∅ : Shape ∅ Once.Spec.Context.∅
  sh-▸ : ∀ {n} {L : Locals m n} {Γ x A} → Shape L Γ → Shape (L ▹ x ∶ A) (Γ ▸ A)

-- The local a name finds has the type a context of that shape gives it.
lookup-shape : ∀ {n} {L : Locals m n} {Γ x A i} → Shape L Γ → L ∋ x ⦂ A at i → lookup Γ i ≡ A
lookup-shape (sh-▸ sh) here        = refl
lookup-shape (sh-▸ sh) (there _ v) = lookup-shape sh v

-- The locals' own context.
ctxOf : ∀ {n} → Locals m n → Ctx m n
ctxOf ∅           = Once.Spec.Context.∅
ctxOf (L ▹ _ ∶ A) = ctxOf L ▸ A

shape-of : ∀ {n} (L : Locals m n) → Shape L (ctxOf L)
shape-of ∅           = sh-∅
shape-of (L ▹ _ ∶ A) = sh-▸ (shape-of L)

lookup-at : ∀ {n} {L : Locals m n} {x A i} → L ∋ x ⦂ A at i → lookup (ctxOf L) i ≡ A
lookup-at {L = L} = lookup-shape (shape-of L)

------------------------------------------------------------------------
-- The annotation
------------------------------------------------------------------------

data Use⇒ {n} {L : Locals m n} : ∀ {e A t} → L ⊢ e ⇒ A ↝ t → Usage n → Set
data Use⇐ {n} {L : Locals m n} : ∀ {e A t} → L ⊢ e ⇐ A ↝ t → Usage n → Set
data Use↦ {n} {L : Locals m n} : ∀ {e A π B t} → L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t → Usage n → Set

data Use⇒ {n} {L} where
  u-int      : ∀ {i} → Use⇒ (s-int i) zeroUsage
  u-float    : ∀ {sg i f l} → Use⇒ (s-float sg i f l) zeroUsage
  u-unit     : Use⇒ s-unit zeroUsage
  -- A constant of the table is closed.
  u-const    : ∀ {g k T t} {c : Constant Δ g k T t} → Use⇒ (s-const c) zeroUsage
  -- A local is used once.
  u-var      : ∀ {x A i} {v : L ∋ x ⦂ A at i} → Use⇒ (s-var v) (singleUse i One)
  -- A declaration of the signature, read at the ground type it declares.
  -- (an honest one: the checker's sigops are the module's FFI declarations)
  u-sigop    : ∀ {c} {T : Type} {mem : (c ∶ declS T) ∈ Σ} {ok : OkS c T} → IsConcrete T → HonestFFI T → Use⇒ (s-sigop {c = c} {t = declS T} mem) zeroUsage
  u-def      : ∀ {c d e τ a} {ok : Ok d} → Use⇒ (s-def {c = c} d e τ a) zeroUsage
  u-annot    : ∀ {e T t} {d : L ⊢ e ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇒ (s-annot {T = T} d) Ψ
  u-pair     : ∀ {a b A B ta tb} {da : L ⊢ a ⇒ A ↝ ta} {db : L ⊢ b ⇒ B ↝ tb} {Ψ₁ Ψ₂}
             → Use⇒ da Ψ₁ → Use⇒ db Ψ₂ → Use⇒ (s-pair da db) (Ψ₁ +ᵘ Ψ₂)
  u-neg      : ∀ {e A t} {h} {d : L ⊢ e ⇒ _ ↝ t} {Ψ} → Use⇒ d Ψ → Use⇒ (s-neg {A = A} h d) Ψ
  -- The body's usage of the bound variable scales the bound expression's.
  u-let      : ∀ {x e₁ e₂ A B t₁ t₂ q} {d₁ : L ⊢ e₁ ⇒ A ↝ t₁} {d₂ : (L ▹ x ∶ A) ⊢ e₂ ⇒ B ↝ t₂} {Ψ₁ Ψ₂}
             → Use⇒ d₁ Ψ₁ → Use⇒ d₂ (q ∷ Ψ₂) → Use⇒ (s-let q d₁ d₂) (Ψ₂ +ᵘ (q *ᵘ Ψ₁))
  -- The branches run at the join of their usages.
  u-case     : ∀ {e xl el xr er A B Cl Cr C ts tl tr ql qr}
               {ds : L ⊢ e ⇒ _ ↝ ts} {dl : (L ▹ xl ∶ A) ⊢ el ⇒ Cl ↝ tl} {dr : (L ▹ xr ∶ B) ⊢ er ⇒ Cr ↝ tr} {j}
               {Ψs Ψₗ Ψᵣ}
             → Use⇒ ds Ψs → Use⇒ dl (ql ∷ Ψₗ) → Use⇒ dr (qr ∷ Ψᵣ)
             → Use⇒ (s-case {C = C} ql qr ds dl dr j) (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
  u-binop    : ∀ {op e₁ e₂ A t₁ t₂} {h} {d₁ : L ⊢ e₁ ⇒ _ ↝ t₁} {d₂ : L ⊢ e₂ ⇒ _ ↝ t₂} {Ψ₁ Ψ₂}
             → Use⇒ d₁ Ψ₁ → Use⇒ d₂ Ψ₂ → Use⇒ (s-binop {op = op} {A = A} h d₁ d₂) (Ψ₁ +ᵘ Ψ₂)
  -- An application uses its argument as often as the arrow's quantity says,
  -- at every grade (an effectful one suspends the same call).
  u-app      : ∀ {f x A B q π tf tx pc ch} {df : L ⊢ f ⇒ _ ↝ tf} {dx : L ⊢ x ⇐ A ↝ tx} {Ψ₁ Ψ₂}
             → Use⇒ df Ψ₁ → Use⇐ dx Ψ₂ → Use⇒ (s-app {B = B} {q = q} {π = π} pc ch df dx) (Ψ₁ +ᵘ (q *ᵘ Ψ₂))
  u-app-spine : ∀ {f x X T tf tx ch} {dx : L ⊢ x ⇒ X ↝ tx} {df : L ⊢ f ⇐ X ⇒[ _ ]↦ T ↝ tf} {Ψ₁ Ψ₂}
              → Use⇒ dx Ψ₂ → Use↦ df Ψ₁ → Use⇒ (s-app-spine ch dx df) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))

data Use⇐ {n} {L} where
  -- A structure map is closed.
  u-map      : ∀ {g k A π B t} {mo : Morphism Δ g k A π B t} → Use⇐ (c-map mo) zeroUsage
  -- … and applied, it uses its argument in an application.
  u-map-app  : ∀ {g k e A B tg t fc} {mo : Morphism Δ g k A pure B tg} {d : L ⊢ e ⇐ A ↝ t} {Ψ}
             → Use⇐ d Ψ → Use⇐ (c-map-app fc mo d) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  -- A composition runs `g` once per use of the composite.
  u-compose-g : ∀ {f g A B C π tf tg df′} {dg : L ⊢ g ⇐ A ⇒[ π ]↦ B ↝ tg} {df : L ⊢ f ⇐ _ ↝ tf} {Ψ₁ Ψ₂}
              → Use↦ dg Ψ₂ → Use⇐ df Ψ₁ → Use⇐ (c-compose-g {C = C} df′ dg df) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  u-compose-f : ∀ {f g A B C C′ π π′ tf tg ndf} {df : L ⊢ f ⇒ _ ↝ tf} {p} {dg : L ⊢ g ⇐ _ ↝ tg} {Ψ₁ Ψ₂}
              → Use⇒ df Ψ₁ → Use⇐ dg Ψ₂
              → Use⇐ (c-compose-f {A = A} {B = B} {C = C} {C′ = C′} {π = π} {π′ = π′} ndf df p dg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  u-case     : ∀ {f g A B C π tf tg} {df : L ⊢ f ⇐ _ ↝ tf} {dg : L ⊢ g ⇐ _ ↝ tg} {Ψ₁ Ψ₂}
             → Use⇐ df Ψ₁ → Use⇐ dg Ψ₂ → Use⇐ (c-case {A = A} {B = B} {C = C} {π = π} df dg) (Ψ₁ +ᵘ Ψ₂)
  u-pair     : ∀ {f g A B C π tf tg} {df : L ⊢ f ⇐ _ ↝ tf} {dg : L ⊢ g ⇐ _ ↝ tg} {Ψ₁ Ψ₂}
             → Use⇐ df Ψ₁ → Use⇐ dg Ψ₂ → Use⇐ (c-pair {A = A} {B = B} {C = C} {π = π} df dg) (Ψ₁ +ᵘ Ψ₂)
  u-curry    : ∀ {f A B C π₀ π t} {d : L ⊢ f ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-curry {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} d) Ψ
  -- The recursion formers run their arm once per layer.
  u-cata     : ∀ {alg F A π t w} {d : L ⊢ alg ⇐ _ ↝ t} {Ψ} → Use⇐ d Ψ → Use⇐ (c-cata {F = F} {A = A} {π = π} w d) (Many *ᵘ Ψ)
  u-ana      : ∀ {c A π₀ X G ρ k t} {fi : Final Δ A π₀ X G ρ k} {d : L ⊢ c ⇐ _ ↝ t} {Ψ}
             → Use⇐ d Ψ → Use⇐ (c-ana fi d) (Many *ᵘ Ψ)
  u-sub      : ∀ {e A B t noc} {d : L ⊢ e ⇒ A ↝ t} {p} {Ψ} → Use⇒ d Ψ → Use⇐ (c-sub {B = B} noc d p) Ψ
  -- A lambda binds a variable its body uses at most as often as the arrow allows.
  u-lam      : ∀ {x body A B q π t} {d : (L ▹ x ∶ A) ⊢ body ⇐ B ↝ t} {q′ Ψ}
             → (q′ ≤qᵇ q) ≡ true → Use⇐ d (q′ ∷ Ψ) → Use⇐ (c-lam {q = q} {π = π} d) Ψ
  u-pair-lit : ∀ {a b A B ta tb} {da : L ⊢ a ⇐ A ↝ ta} {db : L ⊢ b ⇐ B ↝ tb} {Ψ₁ Ψ₂}
             → Use⇐ da Ψ₁ → Use⇐ db Ψ₂ → Use⇐ (c-pair-lit da db) (Ψ₁ +ᵘ Ψ₂)
  u-poly     : ∀ {c d e a τ r} {ok : Ok d} → Use⇐ (c-poly {c = c} d e a τ r) zeroUsage

data Use↦ {n} {L} where
  u-infer    : ∀ {g A A′ B π π′ t} {d : L ⊢ g ⇒ _ ↝ t} {p o} {Ψ}
             → Use⇒ d Ψ → Use↦ (d-infer {A = A} {A′ = A′} {B = B} {π = π} {π′ = π′} d p o) Ψ
  u-poly     : ∀ {c d e a sd sc π′ A B π ty oc τ r ea eb o} {ok : Ok d}
             → Use↦ (d-poly {c = c} d e a {sd = sd} {sc = sc} {π′ = π′} {A = A} {B = B} {π = π} ty oc τ r ea eb o) zeroUsage
  u-lam      : ∀ {x body A B π t} {d : (L ▹ x ∶ A) ⊢ body ⇒ B ↝ t} {q′ Ψ}
             → Use⇒ d (q′ ∷ Ψ) → Use↦ (d-lam {π = π} d) Ψ
  u-map      : ∀ {g k A π B t fd} {mo : Morphism Δ g k A π B t}
               {least : ∀ {k′ B′} {t′ : Tm S m n} → Morphism Δ g k′ A π B′ t′ → B <:ᶜ B′} → Use↦ (d-map fd mo least) zeroUsage
  u-compose  : ∀ {f g A M B π tf tg} {dg : L ⊢ g ⇐ A ⇒[ π ]↦ M ↝ tg} {df : L ⊢ f ⇐ M ⇒[ π ]↦ B ↝ tf} {Ψ₁ Ψ₂}
             → Use↦ dg Ψ₂ → Use↦ df Ψ₁ → Use↦ (d-compose dg df) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  u-case     : ∀ {f g A B Cf Cg C π tf tg} {df : L ⊢ f ⇐ A ⇒[ π ]↦ Cf ↝ tf} {dg : L ⊢ g ⇐ B ⇒[ π ]↦ Cg ↝ tg} {j} {Ψ₁ Ψ₂}
             → Use↦ df Ψ₁ → Use↦ dg Ψ₂ → Use↦ (d-case {C = C} df dg j) (Ψ₁ +ᵘ Ψ₂)
  u-pair     : ∀ {f g A B C π tf tg} {df : L ⊢ f ⇐ A ⇒[ π ]↦ B ↝ tf} {dg : L ⊢ g ⇐ A ⇒[ π ]↦ C ↝ tg} {Ψ₁ Ψ₂}
             → Use↦ df Ψ₁ → Use↦ dg Ψ₂ → Use↦ (d-pair df dg) (Ψ₁ +ᵘ Ψ₂)
  u-cata     : ∀ {alg F A₁ A π′ π t w p o} {d : L ⊢ alg ⇒ _ ↝ t} {Ψ}
             → Use⇒ d Ψ → Use↦ (d-cata {F = F} {A₁ = A₁} {A = A} {π′ = π′} {π = π} w d p o) (Many *ᵘ Ψ)
