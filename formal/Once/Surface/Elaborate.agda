------------------------------------------------------------------------
-- Once.Surface.Elaborate
--
-- Elaboration from surface syntax to IR.
-- Converts lambda/variable expressions to point-free combinators.
--
-- TECHNICAL DEBT: Currently uses postulated contracts.
-- TODO: Replace Prim nodes with Domain (ArithExpr) - see OCP-0003 Phase 4
------------------------------------------------------------------------

open import Once.Contract

module Once.Surface.Elaborate (CI : ContractInterface) where

open import Once.Type
open import Once.IR
open import Once.Surface.Syntax

open IRDef CI
open ContractInterface CI

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Integer as ℤ using (ℤ; +_; _<?_; _≤?_; _≟_) renaming (_+_ to _ℤ+_; _-_ to _ℤ-_; _*_ to _ℤ*_; -_ to ℤ-_)
open import Relation.Nullary using (yes; no)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Unit using (tt; ⊤)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _P,_)

------------------------------------------------------------------------
-- Arrow Quantity Coercion (postulated - quantities erased at runtime)
------------------------------------------------------------------------

postulate
  coerceIRArrow : ∀ {Γ A B q q'} → IR Γ (A ⇒[ q ] B) → IR Γ (A ⇒[ q' ] B)

------------------------------------------------------------------------
-- Arithmetic IR Primitives (TECHNICAL DEBT: postulated contracts)
------------------------------------------------------------------------
--
-- TODO: Replace these with Domain (ArithExpr) expressions.
-- The Arith domain compiler will provide real contracts with proofs.
--

-- Helper to create postulated contract
-- TECHNICAL DEBT: This should be provided by domain compilers with real proofs
postulate
  makeContract : ∀ (A B : Type) → Contract A B

-- Literals: constant morphisms that ignore input environment
intLit : ℤ → ∀ {Γ} → IR Γ Int
intLit n = Prim ("lit.int." ++ showℤ n) (makeContract Unit Int) ∘ terminal

strLit : String → ∀ {Γ} → IR Γ Str
strLit s = Prim ("lit.str." ++ s) (makeContract Unit Str) ∘ terminal

-- Arithmetic operations (Int * Int → Int)
addIR : IR (Int * Int) Int
addIR = Prim "arith.add.int" (makeContract (Int * Int) Int)

subIR : IR (Int * Int) Int
subIR = Prim "arith.sub.int" (makeContract (Int * Int) Int)

mulIR : IR (Int * Int) Int
mulIR = Prim "arith.mul.int" (makeContract (Int * Int) Int)

divIR : IR (Int * Int) Int
divIR = Prim "arith.div.int" (makeContract (Int * Int) Int)

modIR : IR (Int * Int) Int
modIR = Prim "arith.mod.int" (makeContract (Int * Int) Int)

-- Unary negation
negIR : IR Int Int
negIR = Prim "arith.neg.int" (makeContract Int Int)

-- Comparison operations (Int * Int → Bool, where Bool = Unit + Unit)
ltIR : IR (Int * Int) (Unit + Unit)
ltIR = Prim "arith.lt.int" (makeContract (Int * Int) (Unit + Unit))

leIR : IR (Int * Int) (Unit + Unit)
leIR = Prim "arith.le.int" (makeContract (Int * Int) (Unit + Unit))

gtIR : IR (Int * Int) (Unit + Unit)
gtIR = Prim "arith.gt.int" (makeContract (Int * Int) (Unit + Unit))

geIR : IR (Int * Int) (Unit + Unit)
geIR = Prim "arith.ge.int" (makeContract (Int * Int) (Unit + Unit))

eqIR : IR (Int * Int) (Unit + Unit)
eqIR = Prim "arith.eq.int" (makeContract (Int * Int) (Unit + Unit))

neIR : IR (Int * Int) (Unit + Unit)
neIR = Prim "arith.ne.int" (makeContract (Int * Int) (Unit + Unit))

------------------------------------------------------------------------
-- Context Interpretation
------------------------------------------------------------------------

-- | Interpret context as a product type (environment type)
⟦_⟧ᶜ : ∀ {n} → Ctx n → Type
⟦ ∅ ⟧ᶜ         = Unit
⟦ Γ , A ^ q ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

-- | Project variable from environment (de Bruijn index)
proj : ∀ {n} {Γ : Ctx n} (i : Fin n) → IR ⟦ Γ ⟧ᶜ (lookup Γ i)
proj {Γ = Γ , A ^ q} Fin.zero    = snd
proj {Γ = Γ , A ^ q} (Fin.suc i) = proj i ∘ fst

------------------------------------------------------------------------
-- Helper Combinators
------------------------------------------------------------------------

-- | Swap product components
swap' : ∀ {X Y} → IR (X * Y) (Y * X)
swap' = ⟨ snd , fst ⟩

-- | Distribute environment over sum
distribute : ∀ {Γ A B} → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute {Γ} {A} {B} = distrib' ∘ swap'
  where
    curryInlSwap : IR A (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInlSwap = curry (inl ∘ swap')

    curryInrSwap : IR B (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInrSwap = curry (inr ∘ swap')

    curryDistrib : IR (A + B) (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryDistrib = [ curryInlSwap , curryInrSwap ]

    distrib' : IR ((A + B) * Γ) ((Γ * A) + (Γ * B))
    distrib' = apply ∘ ⟨ curryDistrib ∘ fst , snd ⟩

------------------------------------------------------------------------
-- Elaboration
------------------------------------------------------------------------

-- | Elaborate surface expression to IR
elaborate : ∀ {n} {Γ : Ctx n} {A} → Expr Γ A → IR ⟦ Γ ⟧ᶜ A

-- Variable: project from environment
elaborate (var i) = proj i

-- Lambda: curry and coerce quantity
elaborate (lam q e) = coerceIRArrow (curry (elaborate e))

-- Application: apply composition
elaborate (app f x) = apply ∘ ⟨ coerceIRArrow (elaborate f) , elaborate x ⟩

-- Pair
elaborate (pair a b) = ⟨ elaborate a , elaborate b ⟩

-- Projections
elaborate (fst' p) = fst ∘ elaborate p
elaborate (snd' p) = snd ∘ elaborate p

-- Sum introduction
elaborate (inl' a) = inl ∘ elaborate a
elaborate (inr' b) = inr ∘ elaborate b

-- Case: distribute environment over sum
elaborate (case' s l r) =
  [ elaborate l , elaborate r ] ∘ distribute ∘ ⟨ id , elaborate s ⟩

-- Unit
elaborate unit = terminal

-- Absurd (void elimination)
elaborate (absurd v) = initial ∘ elaborate v

-- Let binding
elaborate (let' e1 e2) = elaborate e2 ∘ ⟨ id , elaborate e1 ⟩

-- Literals
elaborate (int n) = intLit n
elaborate (str s) = strLit s

-- Arithmetic operations
elaborate (add e₁ e₂) = addIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (sub e₁ e₂) = subIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (mul e₁ e₂) = mulIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (div e₁ e₂) = divIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (mod' e₁ e₂) = modIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩

-- Unary negation
elaborate (neg e) = negIR ∘ elaborate e

-- Comparison operations
elaborate (lt e₁ e₂) = ltIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (le e₁ e₂) = leIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (gt e₁ e₂) = gtIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (ge e₁ e₂) = geIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (eq e₁ e₂) = eqIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
elaborate (ne e₁ e₂) = neIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩
