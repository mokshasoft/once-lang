------------------------------------------------------------------------
-- Once.Surface.Correct
--
-- Correctness of elaboration from surface syntax to IR.
-- Proves that elaboration preserves semantics.
------------------------------------------------------------------------

module Once.Surface.Correct where

open import Once.Type
open import Once.IR
open import Once.Semantics as IR using (⟦_⟧; eval)
open import Once.Surface.Syntax using (Ctx; ∅; lookup; Expr; var; lam; app; pair; fst'; snd'; inl'; inr'; case'; unit; absurd) renaming (_,_ to _▸_)
open import Once.Surface.Semantics using (Env; ε; _∷_; envLookup; evalSurface)
open import Once.Surface.Elaborate using (⟦_⟧ᶜ; proj; swap'; distribute; elaborate)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- Postulates (imported from central registry)
------------------------------------------------------------------------

-- All postulates are centralized in Once.Postulates for transparency.
-- See that module for documentation of each assumption.
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- Environment interpretation
------------------------------------------------------------------------

-- Convert environment to nested product (environment as value)
--
-- interpEnv ρ converts the heterogeneous environment ρ to a nested
-- product value that can be passed to elaborated IR morphisms.
interpEnv : ∀ {n} {Γ : Ctx n} → Env Γ → ⟦ ⟦ Γ ⟧ᶜ ⟧
interpEnv ε       = tt
interpEnv (v ∷ ρ) = (interpEnv ρ , v)

------------------------------------------------------------------------
-- Projection correctness
------------------------------------------------------------------------

-- Looking up a variable in the environment equals projecting from
-- the interpreted environment.
proj-correct : ∀ {n} {Γ : Ctx n} (ρ : Env Γ) (i : Fin n) →
               envLookup ρ i ≡ eval (proj i) (interpEnv ρ)
proj-correct (v ∷ ρ) Fin.zero    = refl
proj-correct (v ∷ ρ) (Fin.suc i) = proj-correct ρ i

------------------------------------------------------------------------
-- Distribution correctness
------------------------------------------------------------------------

-- The distribute combinator correctly pushes environment through sums.
distribute-inl : ∀ {Γ A B} (γ : ⟦ Γ ⟧) (a : ⟦ A ⟧) →
                 eval (distribute {Γ} {A} {B}) (γ , inj₁ a) ≡ inj₁ (γ , a)
distribute-inl γ a = refl

distribute-inr : ∀ {Γ A B} (γ : ⟦ Γ ⟧) (b : ⟦ B ⟧) →
                 eval (distribute {Γ} {A} {B}) (γ , inj₂ b) ≡ inj₂ (γ , b)
distribute-inr γ b = refl

------------------------------------------------------------------------
-- Case analysis helper
------------------------------------------------------------------------

-- Helper that mirrors evalSurface's case behavior, with an equation.
-- We need this to relate the with-pattern in evalSurface to our proofs.
-- When evalSurface ρ s ≡ v, then evalSurface ρ (case' s l r) computes
-- based on v (which is either inj₁ a or inj₂ b).
case-analysis-inl : ∀ {n} {Γ : Ctx n} {A B C}
                    (ρ : Env Γ) (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                    (a : ⟦ A ⟧) → evalSurface ρ s ≡ inj₁ a →
                    evalSurface ρ (case' s l r) ≡ evalSurface (a ∷ ρ) l
case-analysis-inl ρ s l r a eq with evalSurface ρ s | eq
... | inj₁ x | refl = refl

case-analysis-inr : ∀ {n} {Γ : Ctx n} {A B C}
                    (ρ : Env Γ) (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                    (b : ⟦ B ⟧) → evalSurface ρ s ≡ inj₂ b →
                    evalSurface ρ (case' s l r) ≡ evalSurface (b ∷ ρ) r
case-analysis-inr ρ s l r b eq with evalSurface ρ s | eq
... | inj₂ y | refl = refl

------------------------------------------------------------------------
-- Main correctness theorem (mutually recursive)
------------------------------------------------------------------------

-- We use mutual recursion because the case proof needs the IH for
-- subexpressions, and the main theorem needs the case lemmas.

mutual
  -- Main theorem: elaboration preserves semantics
  elaborate-correct : ∀ {n} {Γ : Ctx n} {A} (ρ : Env Γ) (e : Expr Γ A) →
                      evalSurface ρ e ≡ eval (elaborate e) (interpEnv ρ)
  elaborate-correct ρ (var i) = proj-correct ρ i
  elaborate-correct ρ (lam e) = extensionality λ a → elaborate-correct (a ∷ ρ) e
  elaborate-correct ρ (app f x) = cong₂ (λ f' x' → f' x') (elaborate-correct ρ f) (elaborate-correct ρ x)
  elaborate-correct ρ (pair a b) = cong₂ _,_ (elaborate-correct ρ a) (elaborate-correct ρ b)
  elaborate-correct ρ (fst' p) = cong proj₁ (elaborate-correct ρ p)
  elaborate-correct ρ (snd' p) = cong proj₂ (elaborate-correct ρ p)
  elaborate-correct ρ (inl' a) = cong inj₁ (elaborate-correct ρ a)
  elaborate-correct ρ (inr' b) = cong inj₂ (elaborate-correct ρ b)
  elaborate-correct ρ (case' s l r) = case-correct ρ s l r (evalSurface ρ s) refl
  elaborate-correct ρ unit = refl
  elaborate-correct ρ (absurd v) with evalSurface ρ v
  ... | ()

  -- Case dispatch: routes to inl or inr case based on scrutinee value
  case-correct : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                 (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                 (v : ⟦ A ⟧ ⊎ ⟦ B ⟧) → evalSurface ρ s ≡ v →
                 evalSurface ρ (case' s l r) ≡ eval (elaborate (case' s l r)) (interpEnv ρ)
  case-correct ρ s l r (inj₁ a) eq = case-correct-inl ρ s l r a eq
  case-correct ρ s l r (inj₂ b) eq = case-correct-inr ρ s l r b eq

  -- Case correctness for left injection
  --
  -- Proof outline:
  --   LHS: evalSurface ρ (case' s l r)
  --      = evalSurface (a ∷ ρ) l                           [by eq-s and evalSurface definition]
  --   RHS: eval ([ el , er ] ∘ distribute ∘ ⟨ id , es ⟩) γ
  --      = eval [ el , er ] (eval distribute (γ , eval es γ))
  --      = eval [ el , er ] (eval distribute (γ , inj₁ a)) [by IH for s]
  --      = eval [ el , er ] (inj₁ (γ , a))                 [by distribute-inl]
  --      = eval el (γ , a)                                 [by case rule]
  --      = evalSurface (a ∷ ρ) l                           [by IH for l]
  --
  case-correct-inl : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                     (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                     (a : ⟦ A ⟧) → evalSurface ρ s ≡ inj₁ a →
                     evalSurface ρ (case' s l r) ≡ eval (elaborate (case' s l r)) (interpEnv ρ)
  case-correct-inl {Γ = Γ} {A} {B} {C} ρ s l r a eq-s =
    trans lhs-simp (trans ih-l (sym rhs-eq))
    where
      γ  = interpEnv ρ
      el = elaborate l
      er = elaborate r
      es = elaborate s

      -- LHS simplification: evalSurface ρ (case' s l r) ≡ evalSurface (a ∷ ρ) l
      lhs-simp : evalSurface ρ (case' s l r) ≡ evalSurface (a ∷ ρ) l
      lhs-simp = case-analysis-inl ρ s l r a eq-s

      -- IH for l: evalSurface (a ∷ ρ) l ≡ eval el (γ , a)
      ih-l : evalSurface (a ∷ ρ) l ≡ eval el (γ , a)
      ih-l = elaborate-correct (a ∷ ρ) l

      -- IH for s: eval es γ ≡ inj₁ a
      ih-s : eval es γ ≡ inj₁ a
      ih-s = trans (sym (elaborate-correct ρ s)) eq-s

      -- RHS chain: eval (elaborate (case' s l r)) γ ≡ eval el (γ , a)
      rhs-step1 : eval [ el , er ] (eval distribute (γ , eval es γ)) ≡
                  eval [ el , er ] (eval distribute (γ , inj₁ a))
      rhs-step1 = cong (λ v → eval [ el , er ] (eval distribute (γ , v))) ih-s

      rhs-step2 : eval [ el , er ] (eval distribute (γ , inj₁ a)) ≡
                  eval [ el , er ] (inj₁ (γ , a))
      rhs-step2 = cong (eval [ el , er ]) (distribute-inl {⟦ Γ ⟧ᶜ} {A} {B} γ a)

      rhs-eq : eval (elaborate (case' s l r)) γ ≡ eval el (γ , a)
      rhs-eq = trans rhs-step1 rhs-step2

  -- Case correctness for right injection (symmetric to left case)
  case-correct-inr : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                     (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                     (b : ⟦ B ⟧) → evalSurface ρ s ≡ inj₂ b →
                     evalSurface ρ (case' s l r) ≡ eval (elaborate (case' s l r)) (interpEnv ρ)
  case-correct-inr {Γ = Γ} {A} {B} {C} ρ s l r b eq-s =
    trans lhs-simp (trans ih-r (sym rhs-eq))
    where
      γ  = interpEnv ρ
      el = elaborate l
      er = elaborate r
      es = elaborate s

      -- LHS simplification: evalSurface ρ (case' s l r) ≡ evalSurface (b ∷ ρ) r
      lhs-simp : evalSurface ρ (case' s l r) ≡ evalSurface (b ∷ ρ) r
      lhs-simp = case-analysis-inr ρ s l r b eq-s

      -- IH for r: evalSurface (b ∷ ρ) r ≡ eval er (γ , b)
      ih-r : evalSurface (b ∷ ρ) r ≡ eval er (γ , b)
      ih-r = elaborate-correct (b ∷ ρ) r

      -- IH for s: eval es γ ≡ inj₂ b
      ih-s : eval es γ ≡ inj₂ b
      ih-s = trans (sym (elaborate-correct ρ s)) eq-s

      -- RHS chain: eval (elaborate (case' s l r)) γ ≡ eval er (γ , b)
      rhs-step1 : eval [ el , er ] (eval distribute (γ , eval es γ)) ≡
                  eval [ el , er ] (eval distribute (γ , inj₂ b))
      rhs-step1 = cong (λ v → eval [ el , er ] (eval distribute (γ , v))) ih-s

      rhs-step2 : eval [ el , er ] (eval distribute (γ , inj₂ b)) ≡
                  eval [ el , er ] (inj₂ (γ , b))
      rhs-step2 = cong (eval [ el , er ]) (distribute-inr {⟦ Γ ⟧ᶜ} {A} {B} γ b)

      rhs-eq : eval (elaborate (case' s l r)) γ ≡ eval er (γ , b)
      rhs-eq = trans rhs-step1 rhs-step2
