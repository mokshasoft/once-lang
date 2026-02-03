------------------------------------------------------------------------
-- Once.Surface.ElaborateMachine
--
-- Elaboration from surface syntax to IR, parameterized by MachineInterface.
-- Converts lambda/variable expressions to point-free combinators.
--
-- Part of OCP-0003: PrimContract - Unified Interface for Domain Compilers
--
-- PORTABILITY:
--   This module works with any MachineInterface instantiation:
--   - Word64Interface for x86-64, AArch64
--   - Word32Interface for x86-32, RISC-V 32
--
-- Unlike Once.Surface.Elaborate (which uses ℤ), this module uses
-- machine word operations directly - no encode gap for arithmetic.
------------------------------------------------------------------------

open import Once.Backend.MachineInterface

module Once.Surface.ElaborateMachine (MI : MachineInterface) where

private
  module MI' = MachineInterface MI

open import Once.Type
open import Once.SemanticBaseMachine MI using (⟦_⟧; Closure; int-add; int-sub; int-mul; int-div; int-mod; int-neg; int-lt; int-eq)
open import Once.Backend.ContractInterfaceMachine ⟦_⟧
open import Once.IRMachine ⟦_⟧
open import Once.Surface.Syntax

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Integer as ℤ using (ℤ; +_)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _P,_)
open import Data.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Parameterized Elaborate Module
------------------------------------------------------------------------

-- | Elaborate is parameterized by ContractInterface to support different backends
--
module ElaborateDef (CI : ContractInterface) where
  open ContractInterface CI
  open IRDef CI

  ------------------------------------------------------------------------
  -- Arrow Quantity Coercion
  ------------------------------------------------------------------------
  --
  -- IR arrows are created with a specific quantity by curry.
  -- When elaborating graded lambdas, we need to coerce the quantity.
  -- Quantities are erased at runtime - this is semantically safe.
  --
  postulate
    coerceIRArrowMachine : ∀ {Γ A B q q'} → IR Γ (A ⇒[ q ] B) → IR Γ (A ⇒[ q' ] B)

  ------------------------------------------------------------------------
  -- Arithmetic IR Primitives (using MachineInterface word operations)
  ------------------------------------------------------------------------
  --
  -- These primitives use word operations directly from MachineInterface.
  -- No encode gap - the semantic function IS the machine operation.

  -- Literals: constant morphisms that ignore input environment
  -- The value is converted to a Word using word-from-ℤ
  intLit : ℤ → ∀ {Γ} → IR Γ Int
  intLit n = Prim ("lit.int." ++ showℤ n) (λ _ → MI'.word-from-ℤ n) trivial ∘ terminal
    where postulate trivial : Contract (λ _ → MI'.word-from-ℤ n)

  strLit : String → ∀ {Γ} → IR Γ Str
  strLit s = Prim ("lit.str." ++ s) (λ _ → s) trivial ∘ terminal
    where postulate trivial : Contract (λ _ → s)

  -- Arithmetic operations (Int * Int → Int)
  -- Use word operations from MachineInterface - no ℤ arithmetic!
  addIR : IR (Int * Int) Int
  addIR = Prim "arith.add.int" int-add trivial
    where postulate trivial : Contract int-add

  subIR : IR (Int * Int) Int
  subIR = Prim "arith.sub.int" int-sub trivial
    where postulate trivial : Contract int-sub

  mulIR : IR (Int * Int) Int
  mulIR = Prim "arith.mul.int" int-mul trivial
    where postulate trivial : Contract int-mul

  divIR : IR (Int * Int) Int
  divIR = Prim "arith.div.int" int-div trivial
    where postulate trivial : Contract int-div

  modIR : IR (Int * Int) Int
  modIR = Prim "arith.mod.int" int-mod trivial
    where postulate trivial : Contract int-mod

  -- Unary negation (Int → Int)
  negIR : IR Int Int
  negIR = Prim "arith.neg.int" int-neg trivial
    where postulate trivial : Contract int-neg

  -- Helper: convert Word comparison result to sum type
  -- Uses word-to-bool from MachineInterface
  word-to-sum : MI'.Word → ⟦ Unit + Unit ⟧
  word-to-sum w with MI'.word-to-bool w
  ... | true  = inj₁ tt
  ... | false = inj₂ tt

  -- Comparison operations (Int * Int → Bool, where Bool = Unit + Unit)
  -- Use word comparisons from MachineInterface, convert to sum type
  ltIR : IR (Int * Int) (Unit + Unit)
  ltIR = Prim "arith.lt.int" (λ p → word-to-sum (int-lt p)) trivial
    where postulate trivial : Contract (λ p → word-to-sum (int-lt p))

  leIR : IR (Int * Int) (Unit + Unit)
  leIR = Prim "arith.le.int" (λ p → word-to-sum (MI'.word-le p)) trivial
    where postulate trivial : Contract (λ p → word-to-sum (MI'.word-le p))

  gtIR : IR (Int * Int) (Unit + Unit)
  gtIR = Prim "arith.gt.int" (λ p → word-to-sum (MI'.word-gt p)) trivial
    where postulate trivial : Contract (λ p → word-to-sum (MI'.word-gt p))

  geIR : IR (Int * Int) (Unit + Unit)
  geIR = Prim "arith.ge.int" (λ p → word-to-sum (MI'.word-ge p)) trivial
    where postulate trivial : Contract (λ p → word-to-sum (MI'.word-ge p))

  eqIR : IR (Int * Int) (Unit + Unit)
  eqIR = Prim "arith.eq.int" (λ p → word-to-sum (int-eq p)) trivial
    where postulate trivial : Contract (λ p → word-to-sum (int-eq p))

  neIR : IR (Int * Int) (Unit + Unit)
  neIR = Prim "arith.ne.int" (λ p → word-to-sum (MI'.word-ne p)) trivial
    where postulate trivial : Contract (λ p → word-to-sum (MI'.word-ne p))

  ------------------------------------------------------------------------
  -- Context Interpretation
  ------------------------------------------------------------------------

  -- | Interpret context as a product type (environment type)
  --
  -- The context (A₀, A₁, ..., Aₙ₋₁) becomes the nested product
  -- (...((Unit * A₀) * A₁) * ... * Aₙ₋₁)
  --
  ⟦_⟧ᶜ : ∀ {n} → Ctx n → Type
  ⟦ ∅ ⟧ᶜ         = Unit
  ⟦ Γ , A ^ q ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

  -- | Project variable from environment (de Bruijn index 0 = rightmost)
  proj : ∀ {n} {Γ : Ctx n} (i : Fin n) → IR ⟦ Γ ⟧ᶜ (lookup Γ i)
  proj {Γ = Γ , A ^ q} Fin.zero    = snd
  proj {Γ = Γ , A ^ q} (Fin.suc i) = proj i ∘ fst

  -- | Helper: swap product components
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

  -- Lambda: λ^q x.e becomes curry of (elaborate e)
  -- Uses coerceIRArrowMachine for the parameterized version
  elaborate (lam q e) = coerceIRArrowMachine (curry (elaborate e))

  -- Application: f x becomes apply ∘ ⟨f, x⟩
  elaborate (app f x) = apply ∘ ⟨ coerceIRArrowMachine (elaborate f) , elaborate x ⟩

  -- Pair: (a, b) becomes ⟨a, b⟩
  elaborate (pair a b) = ⟨ elaborate a , elaborate b ⟩

  -- Projections
  elaborate (fst' p) = fst ∘ elaborate p
  elaborate (snd' p) = snd ∘ elaborate p

  -- Sum introduction
  elaborate (inl' a) = inl ∘ elaborate a
  elaborate (inr' b) = inr ∘ elaborate b

  -- Case: distribute environment over sum, then case on result
  elaborate (case' s l r) =
    [ elaborate l , elaborate r ] ∘ distribute ∘ ⟨ id , elaborate s ⟩

  -- Unit
  elaborate unit = terminal

  -- Absurd (void elimination)
  elaborate (absurd v) = initial ∘ elaborate v

  -- Let binding
  elaborate (let' e1 e2) = elaborate e2 ∘ ⟨ id , elaborate e1 ⟩

  -- Integer literal (uses word-from-ℤ to convert to machine word)
  elaborate (int n) = intLit n

  -- String literal
  elaborate (str s) = strLit s

  -- Arithmetic operations (use machine word operations, not ℤ)
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
