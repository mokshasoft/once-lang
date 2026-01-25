------------------------------------------------------------------------
-- Once.Surface.Elaborate
--
-- Elaboration from surface syntax to IR.
-- Converts lambda/variable expressions to point-free combinators.
------------------------------------------------------------------------

module Once.Surface.Elaborate where

open import Once.Type
open import Once.IR
open import Once.Surface.Syntax
open import Once.Postulates using (coerceIRArrow)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.String using (String; _++_)

------------------------------------------------------------------------
-- Arithmetic IR Primitives
------------------------------------------------------------------------
--
-- These primitives are the interface between Surface.Syntax arithmetic
-- and the IR. They use the Prim constructor for opaque runtime operations.
--
-- Semantics are defined by evalPrim in Once.Semantics (trust boundary).

-- Literals: constant morphisms that ignore input environment
-- The value is encoded in the primitive name for runtime interpretation.
intLit : ℤ → ∀ {Γ} → IR Γ Int
intLit n = Prim ("lit.int." ++ showℤ n) ∘ terminal

strLit : String → ∀ {Γ} → IR Γ Str
strLit s = Prim ("lit.str." ++ s) ∘ terminal

-- Arithmetic operations (Int * Int → Int)
addIR : IR (Int * Int) Int
addIR = Prim "arith.add.int"

subIR : IR (Int * Int) Int
subIR = Prim "arith.sub.int"

mulIR : IR (Int * Int) Int
mulIR = Prim "arith.mul.int"

divIR : IR (Int * Int) Int
divIR = Prim "arith.div.int"

modIR : IR (Int * Int) Int
modIR = Prim "arith.mod.int"

-- Unary negation (Int → Int)
negIR : IR Int Int
negIR = Prim "arith.neg.int"

-- Comparison operations (Int * Int → Bool, where Bool = Unit + Unit)
ltIR : IR (Int * Int) (Unit + Unit)
ltIR = Prim "arith.lt.int"

leIR : IR (Int * Int) (Unit + Unit)
leIR = Prim "arith.le.int"

gtIR : IR (Int * Int) (Unit + Unit)
gtIR = Prim "arith.gt.int"

geIR : IR (Int * Int) (Unit + Unit)
geIR = Prim "arith.ge.int"

eqIR : IR (Int * Int) (Unit + Unit)
eqIR = Prim "arith.eq.int"

neIR : IR (Int * Int) (Unit + Unit)
neIR = Prim "arith.ne.int"

-- | Interpret context as a product type (environment type)
--
-- The context (A₀, A₁, ..., Aₙ₋₁) becomes the nested product
-- (...((Unit * A₀) * A₁) * ... * Aₙ₋₁)
--
-- We use left-nested products so newest binding is easiest to access.
--
⟦_⟧ᶜ : ∀ {n} → Ctx n → Type
⟦ ∅ ⟧ᶜ         = Unit
⟦ Γ , A ^ q ⟧ᶜ = ⟦ Γ ⟧ᶜ * A

-- | Project variable from environment (de Bruijn index 0 = rightmost)
--
-- Given context (Γ, A), index 0 projects A (using snd),
-- index n+1 projects from Γ (using fst then recursing).
--
proj : ∀ {n} {Γ : Ctx n} (i : Fin n) → IR ⟦ Γ ⟧ᶜ (lookup Γ i)
proj {Γ = Γ , A ^ q} Fin.zero    = snd
proj {Γ = Γ , A ^ q} (Fin.suc i) = proj i ∘ fst

-- | Helper: swap product components
swap' : ∀ {X Y} → IR (X * Y) (Y * X)
swap' = ⟨ snd , fst ⟩ Heap

-- | Distribute environment over sum (distributivity isomorphism)
--
--   Γ * (A + B) → (Γ * A) + (Γ * B)
--
-- Uses curry/apply to thread environment through case:
-- 1. Swap to get (A + B) * Γ
-- 2. Case on sum, currying the injection to capture Γ
-- 3. Apply to reconstruct result
--
distribute : ∀ {Γ A B} → IR (Γ * (A + B)) ((Γ * A) + (Γ * B))
distribute {Γ} {A} {B} = distrib' ∘ swap'
  where
    curryInlSwap : IR A (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInlSwap = curry (inl Heap ∘ swap') Heap

    curryInrSwap : IR B (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryInrSwap = curry (inr Heap ∘ swap') Heap

    curryDistrib : IR (A + B) (Γ ⇒ ((Γ * A) + (Γ * B)))
    curryDistrib = [ curryInlSwap , curryInrSwap ]

    distrib' : IR ((A + B) * Γ) ((Γ * A) + (Γ * B))
    distrib' = apply ∘ ⟨ curryDistrib ∘ fst , snd ⟩ Heap

-- | Elaborate surface expression to IR
--
-- elaborate e produces an IR morphism from the environment type to
-- the result type: IR ⟦Γ⟧ᶜ A
--
-- Key insight: lambdas extend the environment (product), variables
-- project from the environment, and applications compose appropriately.
--
elaborate : ∀ {n} {Γ : Ctx n} {A} → Expr Γ A → IR ⟦ Γ ⟧ᶜ A

-- Variable: project from environment
elaborate (var i) = proj i

-- Lambda: λ^q x.e becomes curry of (elaborate e)
-- Context (Γ, A) has type ⟦Γ⟧ᶜ * A = ⟦Γ,A⟧ᶜ
-- IR curry always produces (A ⇒ B), so we coerce to (A ⇒[ q ] B)
-- The quantity q is enforced during type checking, not during elaboration
elaborate (lam q e) = coerceIRArrow (curry (elaborate e) Heap)

-- Application: f x becomes apply ∘ ⟨f, x⟩
-- IR's apply only works with unrestricted arrows, so coerce to Many
elaborate (app f x) = apply ∘ ⟨ coerceIRArrow (elaborate f) , elaborate x ⟩ Heap

-- Effect application: same as app but for Eff A B
-- Eff A B is semantically an effectful morphism A → B
elaborate (effApp f x) = apply ∘ ⟨ coerceEffToArrow (elaborate f) , elaborate x ⟩ Heap
  where
    -- Coerce Eff A B to A ⇒ B for IR's apply
    coerceEffToArrow : ∀ {E A B} → IR E (Eff A B) → IR E (A ⇒[ Many ] B)
    coerceEffToArrow = unsafeCoerce
      where postulate unsafeCoerce : ∀ {E A B} → IR E (Eff A B) → IR E (A ⇒[ Many ] B)

-- Pair: (a, b) becomes ⟨a, b⟩
elaborate (pair a b) = ⟨ elaborate a , elaborate b ⟩ Heap

-- Projections: compose with projection
elaborate (fst' p) = fst ∘ elaborate p
elaborate (snd' p) = snd ∘ elaborate p

-- Sum introduction
elaborate (inl' a) = inl Heap ∘ elaborate a
elaborate (inr' b) = inr Heap ∘ elaborate b

-- Case: distribute environment over sum, then case on result
-- s : Expr Γ (A + B), l : Expr (Γ,A) C, r : Expr (Γ,B) C
-- Result: [ el , er ] ∘ distribute ∘ ⟨ id , es ⟩
elaborate (case' s l r) =
  [ elaborate l , elaborate r ] ∘ distribute ∘ ⟨ id , elaborate s ⟩ Heap

-- Unit
elaborate unit = terminal

-- Absurd (void elimination)
elaborate (absurd v) = initial ∘ elaborate v

-- Let binding: let x = e1 in e2
-- Pairs current environment with computed value, then evaluates e2
-- ⟨ id , e1 ⟩ : Γ → Γ × A  (extend environment with bound value)
-- elaborate e2 : Γ × A → B  (e2 in extended context)
elaborate (let' e1 e2) = elaborate e2 ∘ ⟨ id , elaborate e1 ⟩ Heap

-- Integer literal: constant that ignores environment
elaborate (int n) = intLit n

-- String literal: constant that ignores environment
elaborate (str s) = strLit s

-- Arithmetic operations: pair operands, then apply primitive
elaborate (add e₁ e₂) = addIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (sub e₁ e₂) = subIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (mul e₁ e₂) = mulIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (div e₁ e₂) = divIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (mod' e₁ e₂) = modIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap

-- Unary negation
elaborate (neg e) = negIR ∘ elaborate e

-- Comparison operations
elaborate (lt e₁ e₂) = ltIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (le e₁ e₂) = leIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (gt e₁ e₂) = gtIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (ge e₁ e₂) = geIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (eq e₁ e₂) = eqIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap
elaborate (ne e₁ e₂) = neIR ∘ ⟨ elaborate e₁ , elaborate e₂ ⟩ Heap

-- Effect lifting: arr f lifts pure function to effectful morphism
-- IR arr : (A ⇒ B) → Eff A B
elaborate (arr' f) = arr ∘ elaborate f

-- Fixed point constructors
-- roll wraps one layer: F → Fix F
elaborate (roll' e) = fold ∘ elaborate e

-- unroll unwraps one layer: Fix F → F
elaborate (unroll' e) = unfold ∘ elaborate e

-- Imported primitive: call external function by name
-- Like intLit/strLit, ignores environment and produces the result
elaborate (prim name) = Prim name ∘ terminal
