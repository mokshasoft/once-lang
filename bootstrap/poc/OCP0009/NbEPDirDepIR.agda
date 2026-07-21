------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 41 (M2–M4) — DEPENDENT CONSISTENCY, via the standard
--            model as an INDUCTION-RECURSION.
--
-- The dependency project's payoff: `Tm ε ⊥ → Empty` for a genuinely DEPENDENT
-- type theory (dependent Π + an empty type), machine-checked, `--safe`, zero
-- axioms.  The route sidesteps the semantic substitution lemma entirely:
--
--   * TYPES are SEMANTIC — a type over Γ is a CODE-FAMILY `⟦Γ⟧ → Û` (into the
--     meta dependent Tarski universe of dHoTT-41 M1);
--   * the term syntax `Tm` is a genuine deep inductive family, defined MUTUALLY
--     with its interpretation `⟦_⟧` by INDUCTION-RECURSION;
--   * so `app`'s result type is the SEMANTIC instantiation `b (γ , ⟦u⟧ γ)` —
--     dependency is meta-level function application, and SUBSTITUTION and
--     CONVERSION are FREE (no syntactic substitution lemma).
--
-- M2 (`Con`/`⟦_⟧C`/`Ty`), M3 (`Tm`/`⟦_⟧`), M4 (`consistency`) — all here.
--
-- HONEST SCOPE.  This models dependent Π + ⊥ (the DEPENDENCY feature); the
-- OBJECT-LEVEL universe-as-a-type is separate (dHoTT-39 level-stratification,
-- dHoTT-40 El-conversion) — here `U` is the META `Û`.  A single calculus with
-- ALL THREE features needs the RAW-syntax route (dHoTT-41 M1 `NbEPDirDep` +
-- the syntactic substitution lemma) — more faithful, harder.  The three hard
-- features are each now shown consistent.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDepIR where

open import Agda.Builtin.Sigma using ( Σ; _,_; fst; snd )

data Empty : Set where

record ⊤ : Set where
  constructor tt

------------------------------------------------------------------------
-- The meta dependent Tarski universe (as in dHoTT-41 M1).
------------------------------------------------------------------------

data Û : Set
Êl : Û → Set

data Û where
  ⊥̂ : Û
  π̂ : (a : Û) → (Êl a → Û) → Û

Êl ⊥̂       = Empty
Êl (π̂ a b) = (x : Êl a) → Êl (b x)

------------------------------------------------------------------------
-- M2 — contexts with their environment interpretation (induction-recursion);
-- a type is a code-family.
------------------------------------------------------------------------

data Con : Set
⟦_⟧C : Con → Set

data Con where
  ε   : Con
  _▷_ : (Γ : Con) → (⟦ Γ ⟧C → Û) → Con

⟦ ε ⟧C     = ⊤
⟦ Γ ▷ A ⟧C = Σ ⟦ Γ ⟧C (λ γ → Êl (A γ))

Ty : Con → Set
Ty Γ = ⟦ Γ ⟧C → Û

------------------------------------------------------------------------
-- M3 — terms with their interpretation (induction-recursion).  Semantic types
-- make `app`'s codomain the instantiation `b (γ , ⟦u⟧ γ)` — no substitution.
------------------------------------------------------------------------

data Tm : (Γ : Con) → Ty Γ → Set
⟦_⟧ : {Γ : Con} {A : Ty Γ} → Tm Γ A → (γ : ⟦ Γ ⟧C) → Êl (A γ)

data Tm where
  vz  : {Γ : Con} {A : Ty Γ}   → Tm (Γ ▷ A) (λ γ → A (fst γ))
  vs  : {Γ : Con} {A B : Ty Γ} → Tm Γ A → Tm (Γ ▷ B) (λ γ → A (fst γ))
  lam : {Γ : Con} {a : Ty Γ} {b : Ty (Γ ▷ a)} →
        Tm (Γ ▷ a) b → Tm Γ (λ γ → π̂ (a γ) (λ x → b (γ , x)))
  app : {Γ : Con} {a : Ty Γ} {b : Ty (Γ ▷ a)} →
        Tm Γ (λ γ → π̂ (a γ) (λ x → b (γ , x))) → (u : Tm Γ a) →
        Tm Γ (λ γ → b (γ , ⟦ u ⟧ γ))

⟦ vz ⟧    (γ , a) = a
⟦ vs t ⟧  (γ , _) = ⟦ t ⟧ γ
⟦ lam t ⟧ γ       = λ x → ⟦ t ⟧ (γ , x)
⟦ app f u ⟧ γ     = ⟦ f ⟧ γ (⟦ u ⟧ γ)

------------------------------------------------------------------------
-- M4 — CONSISTENCY: no closed term of the empty type.
------------------------------------------------------------------------

consistency : Tm ε (λ _ → ⊥̂) → Empty
consistency t = ⟦ t ⟧ tt
