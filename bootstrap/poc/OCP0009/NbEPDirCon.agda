------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 39 — the SOUNDNESS BRIDGE: a set model of a type
--            theory WITH a universe ⇒ CONSISTENCY, one level up.
--
-- The rung (dHoTT-38) showed the tower's SHAPE (`El (code A) ≡ A`, level-
-- parametric).  This turns a rung into an actual relative-consistency claim:
-- interpret a syntactic type theory that HAS a universe into the meta-theory's
-- SETS, and read off consistency.  The syntactic universe `U` is modelled by
-- `Set ℓ`, which lives ONE LEVEL UP (`Set (lsuc ℓ)`) — exactly why `Once_{n+1}`
-- (an extra universe) can prove `Con(Once_n)`, and `Once_n` cannot prove its own.
--
--   * a SYNTAX (intrinsically well-typed, de Bruijn): a universe `U`, Tarski
--     codes `Code` (`c⊥` for the empty type, `c→` for functions) with `El`
--     decoding, `code`/`var`/`lam`/`app`.  `El (c→ a b)` is directly the arrow
--     (so NO conversion — the tractable, faithful core);
--   * a MODEL `⟦_⟧` into `Set`, parametric in the level `ℓ`: `⟦U⟧ = Set ℓ`,
--     `⟦El c⟧ = Lift ⟦c⟧`, `⟦c⊥⟧ = Empty`, `⟦c→ a b⟧ = ⟦a⟧ → ⟦b⟧`; contexts to
--     iterated products, terms to functions — a total, compositional
--     interpretation (SOUNDNESS by construction);
--   * ★ **`consistency : Tm ∅ (El c⊥) → Empty`** — a closed term of the empty
--     type interprets to an element of the empty set, i.e. is impossible.
--
-- LEVEL-PARAMETRIC ⇒ the generic rung.  `Interp ℓ` proves the SAME calculus
-- consistent using `Set ℓ`/`Set (lsuc ℓ)`, for EVERY `ℓ` — the uniform step whose
-- iteration (`ℓ := ℓ₀, lsuc ℓ₀, …`) is the ladder `Con(Once_n) ⊢ Once_{n+1}`.
-- Gödel intact: the model needs `Set (lsuc ℓ)`, strictly above the `Set ℓ` the
-- object universe uses, so the theory never models ITSELF.
--
-- HONEST SCOPE.  This is the simply-typed-WITH-a-universe fragment (types depend
-- on codes, not on terms) — the tractable core that carries the level-
-- stratification and the whole soundness⇒consistency argument.  Interpreting the
-- FULL dependent kernel (`NbEPDirDBType`: term-dependency, `El`-conversion,
-- Π/Σ over `El`) is the larger soundness proof (conversion must be respected).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirCon where

open import Agda.Primitive using ( Level; lzero; lsuc; _⊔_ )
open import Agda.Builtin.Sigma using ( Σ; _,_; fst; snd )
open import Agda.Builtin.Unit  using ( ⊤; tt )

data Empty {ℓ} : Set ℓ where

record Lift {a} (ℓ : Level) (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A
open Lift

------------------------------------------------------------------------
-- Syntax — intrinsically well-typed, with a Tarski universe.
------------------------------------------------------------------------

data Code : Set where
  c⊥ : Code                  -- code of the empty type
  c→ : Code → Code → Code    -- code of a (non-dependent) function type

data Ty : Set where
  U  : Ty                    -- the universe
  El : Code → Ty             -- decoding

infixl 5 _▷_
data Con : Set where
  ∅   : Con
  _▷_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀ {Γ A}   → Var (Γ ▷ A) A
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▷ B) A

data Tm : Con → Ty → Set where
  var  : ∀ {Γ A}     → Var Γ A → Tm Γ A
  lam  : ∀ {Γ a b}   → Tm (Γ ▷ El a) (El b) → Tm Γ (El (c→ a b))
  app  : ∀ {Γ a b}   → Tm Γ (El (c→ a b)) → Tm Γ (El a) → Tm Γ (El b)
  code : ∀ {Γ}       → Code → Tm Γ U

------------------------------------------------------------------------
-- The set model, parametric in the level `ℓ` — SOUNDNESS by construction.
------------------------------------------------------------------------

module Interp (ℓ : Level) where

  ⟦_⟧C : Code → Set ℓ
  ⟦ c⊥ ⟧C     = Empty
  ⟦ c→ a b ⟧C = ⟦ a ⟧C → ⟦ b ⟧C

  -- the universe is a set ONE LEVEL UP.
  ⟦_⟧T : Ty → Set (lsuc ℓ)
  ⟦ U ⟧T    = Set ℓ
  ⟦ El c ⟧T = Lift (lsuc ℓ) ⟦ c ⟧C

  ⟦_⟧Con : Con → Set (lsuc ℓ)
  ⟦ ∅ ⟧Con     = Lift (lsuc ℓ) ⊤
  ⟦ Γ ▷ A ⟧Con = Σ ⟦ Γ ⟧Con (λ _ → ⟦ A ⟧T)

  ⟦_⟧V : ∀ {Γ A} → Var Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧T
  ⟦ vz ⟧V   (_ , a) = a
  ⟦ vs x ⟧V (γ , _) = ⟦ x ⟧V γ

  ⟦_⟧M : ∀ {Γ A} → Tm Γ A → ⟦ Γ ⟧Con → ⟦ A ⟧T
  ⟦ var x ⟧M   γ = ⟦ x ⟧V γ
  ⟦ lam t ⟧M   γ = lift (λ a → lower (⟦ t ⟧M (γ , lift a)))
  ⟦ app f u ⟧M γ = lift (lower (⟦ f ⟧M γ) (lower (⟦ u ⟧M γ)))
  ⟦ code c ⟧M  γ = ⟦ c ⟧C

  -- ★ CONSISTENCY: a closed term of the empty type is impossible, because it
  --   would interpret to an element of the empty set.
  consistency : Tm ∅ (El c⊥) → Empty {ℓ}
  consistency t = lower (⟦ t ⟧M (lift tt))

------------------------------------------------------------------------
-- The relative-consistency claim, at the ground level (and, by `Interp`,
-- at every level uniformly — the ladder's generic rung).
------------------------------------------------------------------------

consistency : Tm ∅ (El c⊥) → Empty {lzero}
consistency = Interp.consistency lzero
