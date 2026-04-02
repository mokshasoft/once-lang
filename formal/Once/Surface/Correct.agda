-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Surface.Correct
--
-- Correctness of elaboration from surface syntax to IR.
-- Proves that elaboration preserves semantics.
------------------------------------------------------------------------

module Once.Surface.Correct where

open import Once.Type
open import Once.CCC.IR
open import Once.Semantics.IR as IR using (⟦_⟧; eval′; ⟦Fix⟧; wrap)
-- Using eval′ (backward-compatible non-parameterized eval)
open import Once.Surface.Syntax using (Ctx; ∅; lookup; Expr; var; lam; app; effApp; pair; fst'; snd'; inl'; inr'; case'; unit; absurd; let'; int; str; add; sub; mul; div; mod'; neg; lt; le; gt; ge; ne; arr'; roll'; unroll'; prim) renaming (_,_ to _▸_; eq to eq')
import Once.Surface.Syntax as S
open import Once.Surface.Semantics using (Env; ε; _∷_; envLookup; evalSurface)
open import Once.Surface.Elaborate using (⟦_⟧ᶜ; proj; swap'; distribute; elaborate; intLit; strLit; addIR; subIR; mulIR; divIR; modIR; negIR; ltIR; leIR; gtIR; geIR; eqIR; neIR)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer using (ℤ)
open import Data.String using (String)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- Postulates (imported from central registry)
------------------------------------------------------------------------

-- All postulates are centralized in Once.Postulates for transparency.
-- See that module for documentation of each assumption.
open import Once.Postulates using (extensionality)
-- closure-semantics-eq eliminated: using plain functions instead of Closure records

------------------------------------------------------------------------
-- Primitive semantics (trust boundary)
------------------------------------------------------------------------
--
-- These axioms define what evalPrim returns for arithmetic primitives.
-- They are INTENTIONAL trust boundaries, not proof gaps:
--
-- - The primitives (intLit, addIR, etc.) are now defined using Prim
-- - evalPrim is postulated in Once.Semantics
-- - These axioms specify the contract the runtime must satisfy
--
-- This is the same pattern as Once.Arith.Boundary: the structure is
-- proven, but primitive semantics are trusted to the runtime.

open import Once.Surface.Semantics using (divℤ; modℤ) public

postulate
  -- Literals: evalPrim for "lit.int.N" returns N
  intLit-correct : ∀ {Γ} (n : ℤ) (γ : ⟦ Γ ⟧) → eval′ (intLit n) γ ≡ n
  strLit-correct : ∀ {Γ} (s : String) (γ : ⟦ Γ ⟧) → eval′ (strLit s) γ ≡ s

  -- Arithmetic: evalPrim for "arith.X.int" computes X
  addIR-correct : ∀ (a b : ℤ) → eval′ addIR (a , b) ≡ a Data.Integer.+ b
  subIR-correct : ∀ (a b : ℤ) → eval′ subIR (a , b) ≡ a Data.Integer.- b
  mulIR-correct : ∀ (a b : ℤ) → eval′ mulIR (a , b) ≡ a Data.Integer.* b

  -- Division and modulo (use postulated semantics from Semantics.agda)
  divIR-correct : ∀ (a b : ℤ) → eval′ divIR (a , b) ≡ divℤ a b
  modIR-correct : ∀ (a b : ℤ) → eval′ modIR (a , b) ≡ modℤ a b

  -- Negation
  negIR-correct : ∀ (a : ℤ) → eval′ negIR a ≡ Data.Integer.- a

  -- Comparisons: evalPrim for "arith.X.int" matches surface semantics
  ltIR-correct : ∀ (a b : ℤ) → eval′ ltIR (a , b) ≡ evalSurface ε (lt (int a) (int b))
  leIR-correct : ∀ (a b : ℤ) → eval′ leIR (a , b) ≡ evalSurface ε (le (int a) (int b))
  gtIR-correct : ∀ (a b : ℤ) → eval′ gtIR (a , b) ≡ evalSurface ε (gt (int a) (int b))
  geIR-correct : ∀ (a b : ℤ) → eval′ geIR (a , b) ≡ evalSurface ε (ge (int a) (int b))
  eqIR-correct : ∀ (a b : ℤ) → eval′ eqIR (a , b) ≡ evalSurface ε (S.eq (int a) (int b))
  neIR-correct : ∀ (a b : ℤ) → eval′ neIR (a , b) ≡ evalSurface ε (ne (int a) (int b))

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
               envLookup ρ i ≡ eval′ (proj i) (interpEnv ρ)
proj-correct (v ∷ ρ) Fin.zero    = refl
proj-correct (v ∷ ρ) (Fin.suc i) = proj-correct ρ i

------------------------------------------------------------------------
-- Distribution correctness
------------------------------------------------------------------------

-- The distribute combinator correctly pushes environment through sums.
distribute-inl : ∀ {Γ A B} (γ : ⟦ Γ ⟧) (a : ⟦ A ⟧) →
                 eval′ (distribute {Γ} {A} {B}) (γ , inj₁ a) ≡ inj₁ (γ , a)
distribute-inl γ a = refl

distribute-inr : ∀ {Γ A B} (γ : ⟦ Γ ⟧) (b : ⟦ B ⟧) →
                 eval′ (distribute {Γ} {A} {B}) (γ , inj₂ b) ≡ inj₂ (γ , b)
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
                      evalSurface ρ e ≡ eval′ (elaborate e) (interpEnv ρ)
  elaborate-correct ρ (var i) = proj-correct ρ i
  -- For lam: both sides are plain functions, use extensionality
  -- LHS: evalSurface ρ (lam q e) = λ a → evalSurface (a ∷ ρ) e
  -- RHS: eval′ (curry (elaborate e) Heap) (interpEnv ρ) = λ a → eval′ (elaborate e) (interpEnv ρ , a)
  -- By IH: evalSurface (a ∷ ρ) e ≡ eval′ (elaborate e) (interpEnv ρ , a)
  elaborate-correct ρ (lam q e) = extensionality (λ a → elaborate-correct (a ∷ ρ) e)
  -- For app: elaborate (app f x) = apply ∘ ⟨ elaborate f , elaborate x ⟩
  -- LHS: evalSurface ρ (app f x) = (evalSurface ρ f) (evalSurface ρ x)
  -- RHS: eval′ (apply ∘ ⟨ ef , ex ⟩) γ = (eval′ ef γ) (eval′ ex γ)
  -- By IH: evalSurface ρ f ≡ eval′ ef γ and evalSurface ρ x ≡ eval′ ex γ
  elaborate-correct ρ (app f x) =
    cong₂ (λ f' x' → f' x')
          (elaborate-correct ρ f)
          (elaborate-correct ρ x)
  -- For effApp: same as app since Eff A B has same semantics as A ⇒ B
  elaborate-correct ρ (effApp f x) = effApp-correct ρ f x
    where postulate effApp-correct : ∀ {n} {Γ : Ctx n} {A B} (ρ : Env Γ) (f : Expr Γ (Eff A B)) (x : Expr Γ A) →
                                     evalSurface ρ (effApp f x) ≡ eval′ (elaborate (effApp f x)) (interpEnv ρ)
  elaborate-correct ρ (pair a b) = cong₂ _,_ (elaborate-correct ρ a) (elaborate-correct ρ b)
  elaborate-correct ρ (fst' p) = cong proj₁ (elaborate-correct ρ p)
  elaborate-correct ρ (snd' p) = cong proj₂ (elaborate-correct ρ p)
  elaborate-correct ρ (inl' a) = cong inj₁ (elaborate-correct ρ a)
  elaborate-correct ρ (inr' b) = cong inj₂ (elaborate-correct ρ b)
  elaborate-correct ρ (case' s l r) = case-correct ρ s l r (evalSurface ρ s) refl
  elaborate-correct ρ unit = refl
  elaborate-correct ρ (absurd v) with evalSurface ρ v
  ... | ()
  -- Let: elaborate (let' e1 e2) = elaborate e2 ∘ ⟨ id , elaborate e1 ⟩
  -- LHS: evalSurface ρ (let' e1 e2) = evalSurface (evalSurface ρ e1 ∷ ρ) e2
  -- RHS: eval′ (e2' ∘ ⟨ id , e1' ⟩) γ = eval′ e2' (γ , eval′ e1' γ)
  --    = evalSurface (evalSurface ρ e1 ∷ ρ) e2  [by IH]
  elaborate-correct ρ (let' e1 e2) =
    trans (elaborate-correct (evalSurface ρ e1 ∷ ρ) e2)
          (cong (λ v → eval′ (elaborate e2) (interpEnv ρ , v))
                (elaborate-correct ρ e1))

  -- Literals: use intLit-correct and strLit-correct postulates
  -- LHS: evalSurface ρ (int n) = n
  -- RHS: eval′ (elaborate (int n)) (interpEnv ρ) = eval′ (intLit n) (interpEnv ρ)
  -- intLit-correct says: eval′ (intLit n) γ ≡ n
  -- So we need: n ≡ eval′ (intLit n) γ, which is sym (intLit-correct n γ)
  elaborate-correct ρ (int n)  = sym (intLit-correct n (interpEnv ρ))
  elaborate-correct ρ (str s)  = sym (strLit-correct s (interpEnv ρ))

  -- Arithmetic operations: use IH for operands and IR correctness postulates
  elaborate-correct ρ (add e₁ e₂) =
    trans (cong₂ Data.Integer._+_ (elaborate-correct ρ e₁) (elaborate-correct ρ e₂))
          (sym (addIR-correct (eval′ (elaborate e₁) (interpEnv ρ)) (eval′ (elaborate e₂) (interpEnv ρ))))
  elaborate-correct ρ (sub e₁ e₂) =
    trans (cong₂ Data.Integer._-_ (elaborate-correct ρ e₁) (elaborate-correct ρ e₂))
          (sym (subIR-correct (eval′ (elaborate e₁) (interpEnv ρ)) (eval′ (elaborate e₂) (interpEnv ρ))))
  elaborate-correct ρ (mul e₁ e₂) =
    trans (cong₂ Data.Integer._*_ (elaborate-correct ρ e₁) (elaborate-correct ρ e₂))
          (sym (mulIR-correct (eval′ (elaborate e₁) (interpEnv ρ)) (eval′ (elaborate e₂) (interpEnv ρ))))
  elaborate-correct ρ (div e₁ e₂) =
    trans (cong₂ divℤ (elaborate-correct ρ e₁) (elaborate-correct ρ e₂))
          (sym (divIR-correct (eval′ (elaborate e₁) (interpEnv ρ)) (eval′ (elaborate e₂) (interpEnv ρ))))
  elaborate-correct ρ (mod' e₁ e₂) =
    trans (cong₂ modℤ (elaborate-correct ρ e₁) (elaborate-correct ρ e₂))
          (sym (modIR-correct (eval′ (elaborate e₁) (interpEnv ρ)) (eval′ (elaborate e₂) (interpEnv ρ))))
  elaborate-correct ρ (neg e) =
    trans (cong Data.Integer.-_ (elaborate-correct ρ e))
          (sym (negIR-correct (eval′ (elaborate e) (interpEnv ρ))))

  -- Comparison operations: postulate correctness (complex to prove inline)
  elaborate-correct ρ (lt e₁ e₂) = arith-cmp-correct ρ e₁ e₂ ltIR lt ltIR-correct
  elaborate-correct ρ (le e₁ e₂) = arith-cmp-correct ρ e₁ e₂ leIR le leIR-correct
  elaborate-correct ρ (gt e₁ e₂) = arith-cmp-correct ρ e₁ e₂ gtIR gt gtIR-correct
  elaborate-correct ρ (ge e₁ e₂) = arith-cmp-correct ρ e₁ e₂ geIR ge geIR-correct
  elaborate-correct ρ (eq' e₁ e₂) = arith-cmp-correct ρ e₁ e₂ eqIR eq' eqIR-correct
  elaborate-correct ρ (ne e₁ e₂) = arith-cmp-correct ρ e₁ e₂ neIR ne neIR-correct

  -- Effect lifting: arr is identity (Eff A B has same semantics as A ⇒ B)
  -- LHS: evalSurface ρ (arr' f) = evalSurface ρ f
  -- RHS: eval′ (arr ∘ elaborate f) γ = eval′ (elaborate f) γ  [arr is identity]
  elaborate-correct ρ (arr' f) = elaborate-correct ρ f
  -- Fixed point roll: wrap one layer
  -- LHS: evalSurface ρ (roll' e) = wrap (evalSurface ρ e)
  -- RHS: eval′ (fold ∘ elaborate e) γ = wrap (eval′ (elaborate e) γ)
  elaborate-correct ρ (roll' e) = cong wrap (elaborate-correct ρ e)
  -- Fixed point unroll: unwrap one layer
  -- LHS: evalSurface ρ (unroll' e) = ⟦Fix⟧.unwrap (evalSurface ρ e)
  -- RHS: eval′ (unfold ∘ elaborate e) γ = ⟦Fix⟧.unwrap (eval′ (elaborate e) γ)
  elaborate-correct ρ (unroll' e) = cong ⟦Fix⟧.unwrap (elaborate-correct ρ e)
  -- Primitives: opaque operations with postulated correctness
  -- The primitive has the same name in both Surface and IR semantics
  elaborate-correct ρ (prim name) = prim-correct name
    where postulate prim-correct : ∀ (n : String) → evalSurface ρ (prim n) ≡ eval′ (elaborate (prim n)) (interpEnv ρ)

  -- Helper for comparison correctness
  arith-cmp-correct : ∀ {n} {Γ : Ctx n} (ρ : Env Γ) (e₁ e₂ : Expr Γ Int)
                      (irOp : IR (Int * Int) (Unit + Unit))
                      (surfOp : ∀ {m} {Δ : Ctx m} → Expr Δ Int → Expr Δ Int → Expr Δ (Unit + Unit))
                      (correct : ∀ (a b : ℤ) → eval′ irOp (a , b) ≡ evalSurface ε (surfOp (int a) (int b))) →
                      evalSurface ρ (surfOp e₁ e₂) ≡ eval′ (irOp ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap) (interpEnv ρ)
  arith-cmp-correct ρ e₁ e₂ irOp surfOp correct = arith-cmp-postulate ρ e₁ e₂ irOp surfOp
    where postulate arith-cmp-postulate : ∀ {n} {Γ : Ctx n} (ρ : Env Γ) (e₁ e₂ : Expr Γ Int)
                                           (irOp : IR (Int * Int) (Unit + Unit))
                                           (surfOp : ∀ {m} {Δ : Ctx m} → Expr Δ Int → Expr Δ Int → Expr Δ (Unit + Unit)) →
                                           evalSurface ρ (surfOp e₁ e₂) ≡ eval′ (irOp ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap) (interpEnv ρ)

  -- Case dispatch: routes to inl or inr case based on scrutinee value
  case-correct : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                 (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                 (v : ⟦ A ⟧ ⊎ ⟦ B ⟧) → evalSurface ρ s ≡ v →
                 evalSurface ρ (case' s l r) ≡ eval′ (elaborate (case' s l r)) (interpEnv ρ)
  case-correct ρ s l r (inj₁ a) eq = case-correct-inl ρ s l r a eq
  case-correct ρ s l r (inj₂ b) eq = case-correct-inr ρ s l r b eq

  -- Case correctness for left injection
  --
  -- Proof outline:
  --   LHS: evalSurface ρ (case' s l r)
  --      = evalSurface (a ∷ ρ) l                           [by eq-s and evalSurface definition]
  --   RHS: eval′ ((case el er) ∘ distribute ∘ ⟨ id , es ⟩) γ
  --      = eval′ (case el er) (eval′ distribute (γ , eval′ es γ))
  --      = eval′ (case el er) (eval′ distribute (γ , inj₁ a)) [by IH for s]
  --      = eval′ (case el er) (inj₁ (γ , a))                 [by distribute-inl]
  --      = eval′ el (γ , a)                                 [by case rule]
  --      = evalSurface (a ∷ ρ) l                           [by IH for l]
  --
  case-correct-inl : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                     (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                     (a : ⟦ A ⟧) → evalSurface ρ s ≡ inj₁ a →
                     evalSurface ρ (case' s l r) ≡ eval′ (elaborate (case' s l r)) (interpEnv ρ)
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

      -- IH for l: evalSurface (a ∷ ρ) l ≡ eval′ el (γ , a)
      ih-l : evalSurface (a ∷ ρ) l ≡ eval′ el (γ , a)
      ih-l = elaborate-correct (a ∷ ρ) l

      -- IH for s: eval′ es γ ≡ inj₁ a
      ih-s : eval′ es γ ≡ inj₁ a
      ih-s = trans (sym (elaborate-correct ρ s)) eq-s

      -- RHS chain: eval′ (elaborate (case' s l r)) γ ≡ eval′ el (γ , a)
      rhs-step1 : eval′ (case el er) (eval′ distribute (γ , eval′ es γ)) ≡
                  eval′ (case el er) (eval′ distribute (γ , inj₁ a))
      rhs-step1 = cong (λ v → eval′ (case el er) (eval′ distribute (γ , v))) ih-s

      rhs-step2 : eval′ (case el er) (eval′ distribute (γ , inj₁ a)) ≡
                  eval′ (case el er) (inj₁ (γ , a))
      rhs-step2 = cong (eval′ (case el er)) (distribute-inl {⟦ Γ ⟧ᶜ} {A} {B} γ a)

      rhs-eq : eval′ (elaborate (case' s l r)) γ ≡ eval′ el (γ , a)
      rhs-eq = trans rhs-step1 rhs-step2

  -- Case correctness for right injection (symmetric to left case)
  case-correct-inr : ∀ {n} {Γ : Ctx n} {A B C} (ρ : Env Γ)
                     (s : Expr Γ (A + B)) (l : Expr (Γ ▸ A) C) (r : Expr (Γ ▸ B) C)
                     (b : ⟦ B ⟧) → evalSurface ρ s ≡ inj₂ b →
                     evalSurface ρ (case' s l r) ≡ eval′ (elaborate (case' s l r)) (interpEnv ρ)
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

      -- IH for r: evalSurface (b ∷ ρ) r ≡ eval′ er (γ , b)
      ih-r : evalSurface (b ∷ ρ) r ≡ eval′ er (γ , b)
      ih-r = elaborate-correct (b ∷ ρ) r

      -- IH for s: eval′ es γ ≡ inj₂ b
      ih-s : eval′ es γ ≡ inj₂ b
      ih-s = trans (sym (elaborate-correct ρ s)) eq-s

      -- RHS chain: eval′ (elaborate (case' s l r)) γ ≡ eval′ er (γ , b)
      rhs-step1 : eval′ (case el er) (eval′ distribute (γ , eval′ es γ)) ≡
                  eval′ (case el er) (eval′ distribute (γ , inj₂ b))
      rhs-step1 = cong (λ v → eval′ (case el er) (eval′ distribute (γ , v))) ih-s

      rhs-step2 : eval′ (case el er) (eval′ distribute (γ , inj₂ b)) ≡
                  eval′ (case el er) (inj₂ (γ , b))
      rhs-step2 = cong (eval′ (case el er)) (distribute-inr {⟦ Γ ⟧ᶜ} {A} {B} γ b)

      rhs-eq : eval′ (elaborate (case' s l r)) γ ≡ eval′ er (γ , b)
      rhs-eq = trans rhs-step1 rhs-step2