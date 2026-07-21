------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 43c — the SEMANTIC counterpart of NbEPDirDTT:
--   genuinely-dependent CONSISTENCY for the type-level-`if` mechanism, closed
--   CLEANLY via the intrinsic (induction-recursion) model.  `--safe`, zero axioms.
--
-- NbEPDirDTT delivered the genuinely-dependent RAW calculus (type-level `𝕀`) +
-- its syntactic metatheory; its set-model M3c is blocked on Church-style typing +
-- a heterogeneous derivation-irrelevance proof (a large dedicated build — the
-- Curry-style term `lam (var vz)` has BOTH types `Π 𝔹 𝔹` and `Π ⊥ ⊥`, machine-
-- checked, so the interpretation cannot be derivation-irrelevant as posed).
--
-- Here the SAME dependency mechanism — a TYPE-LEVEL large elimination
-- `IfT A B t` (`if t then A else B`) — is modelled INTRINSICALLY: TYPES are
-- SEMANTIC (`⟦Γ⟧ → Set`) and `Tm` is defined MUTUALLY with `⟦_⟧` by IR, so
-- `IfT`'s condition is the meta term-interp (no re-typing) and the dependent
-- eliminator `bif`'s result type is the semantic `If` (no substitution lemma, no
-- coherence).  ★ `consistency`; ★ a genuinely-dependent term whose TYPE depends
-- on a boolean.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDTTSem where

open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma    using ( Σ; _,_; fst; snd )

data Empty : Set where
record ⊤ : Set where
  constructor ⋆
data Two : Set where 0₂ 1₂ : Two

If : Two → Set → Set → Set
If 1₂ A B = A
If 0₂ A B = B

-- the dependent boolean eliminator, at the meta level.
ifv : (t : Two) (P Q : Set) → P → Q → If t P Q
ifv 1₂ P Q p q = p
ifv 0₂ P Q p q = q

------------------------------------------------------------------------
-- Contexts + environment interpretation (induction-recursion).
------------------------------------------------------------------------

data Con : Set₁
⟦_⟧C : Con → Set

data Con where
  ε   : Con
  _▷_ : (Γ : Con) → (⟦ Γ ⟧C → Set) → Con

⟦ ε ⟧C     = ⊤
⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → A γ)

Ty : Con → Set₁
Ty Γ = ⟦ Γ ⟧C → Set

⊥T : ∀ {Γ} → Ty Γ
⊥T _ = Empty

𝔹T : ∀ {Γ} → Ty Γ
𝔹T _ = Two

ΠT : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
ΠT A B γ = (x : A γ) → B (γ , x)

------------------------------------------------------------------------
-- Terms + interpretation + the type-level `IfT` (all mutual: `IfT` and `bif`
-- both mention `⟦_⟧`).
------------------------------------------------------------------------

data Tm : (Γ : Con) → Ty Γ → Set₁
⟦_⟧ : ∀ {Γ A} → Tm Γ A → (γ : ⟦ Γ ⟧C) → A γ

-- ★ the type-level large elimination: a type that DEPENDS ON A BOOLEAN TERM.
IfT : ∀ {Γ} (A B : Ty Γ) → Tm Γ 𝔹T → Ty Γ
IfT A B t γ = If (⟦ t ⟧ γ) (A γ) (B γ)

data Tm where
  vz  : ∀ {Γ A} → Tm (Γ ▷ A) (λ γ → A (fst γ))
  vs  : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▷ B) (λ γ → A (fst γ))
  lam : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} → Tm (Γ ▷ A) B → Tm Γ (ΠT A B)
  app : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
        Tm Γ (ΠT A B) → (u : Tm Γ A) → Tm Γ (λ γ → B (γ , ⟦ u ⟧ γ))
  b0  : ∀ {Γ} → Tm Γ 𝔹T
  b1  : ∀ {Γ} → Tm Γ 𝔹T
  -- ★ the DEPENDENT eliminator: its result type `IfT A B c` depends on `c`.
  bif : ∀ {Γ} {A B : Ty Γ} (c : Tm Γ 𝔹T) → Tm Γ A → Tm Γ B → Tm Γ (IfT A B c)

⟦ vz ⟧       (γ , a) = a
⟦ vs t ⟧     (γ , _) = ⟦ t ⟧ γ
⟦ lam t ⟧    γ       = λ x → ⟦ t ⟧ (γ , x)
⟦ app f u ⟧  γ       = ⟦ f ⟧ γ (⟦ u ⟧ γ)
⟦ b0 ⟧       γ       = 0₂
⟦ b1 ⟧       γ       = 1₂
⟦ bif {A = A} {B = B} c a b ⟧ γ = ifv (⟦ c ⟧ γ) (A γ) (B γ) (⟦ a ⟧ γ) (⟦ b ⟧ γ)

------------------------------------------------------------------------
-- ★ CONSISTENCY, and a genuinely-dependent term.
------------------------------------------------------------------------

consistency : Tm ε ⊥T → Empty
consistency t = ⟦ t ⟧ ⋆

-- a genuinely-dependent type over `ε ▷ 𝔹T`: `if (var vz) then 𝔹 else (𝔹 → 𝔹)`.
DepFam : Ty (ε ▷ 𝔹T)
DepFam = IfT (λ _ → Two) (λ γ → (Two → Two)) vz

-- ★ a term whose TYPE genuinely depends on the boolean:
--   `bif b1 …` lands in `IfT _ _ b1`, which computes to the `then`-branch `Two`.
dep-true : Tm ε (IfT (λ _ → Two) (λ _ → (Two → Two)) b1)
dep-true = bif b1 b1 (lam {A = λ _ → Two} vz)

check-then : ⟦ dep-true ⟧ ⋆ ≡ 1₂
check-then = refl

-- and at `b0` the SAME eliminator lands in the `else`-branch `Two → Two`:
dep-false : Tm ε (IfT (λ _ → Two) (λ _ → (Two → Two)) b0)
dep-false = bif b0 b1 (lam {A = λ _ → Two} vz)

check-else : ⟦ dep-false ⟧ ⋆ 0₂ ≡ 0₂
check-else = refl
