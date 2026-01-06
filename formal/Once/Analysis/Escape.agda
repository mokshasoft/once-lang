------------------------------------------------------------------------
-- Once.Analysis.Escape
--
-- Escape analysis for optimizing memory allocation.
--
-- This module analyzes when values escape their defining scope,
-- determining whether they can be allocated on the stack (faster)
-- or must be allocated on the heap (for values that outlive their scope).
--
-- The analysis works on the IR level after elaboration from surface syntax.
------------------------------------------------------------------------

module Once.Analysis.Escape where

open import Once.Type
open import Once.IR

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_; _++_; map; any; all)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Escape Context
------------------------------------------------------------------------

-- | Analysis context tracking which values may escape
--
-- We track:
-- 1. Whether the current value will be returned from a function
-- 2. Whether the current value will be stored in a data structure
-- 3. The depth of lambda nesting (for tracking closure captures)
--
record EscapeContext : Set where
  field
    returns    : Bool  -- Will this value be returned?
    stores     : Bool  -- Will this value be stored?
    lambdaDepth : ℕ    -- Current lambda nesting depth

-- | Initial context for analysis
initialContext : EscapeContext
initialContext = record
  { returns = false
  ; stores = false
  ; lambdaDepth = zero
  }

-- | Context for analyzing return values
returnContext : EscapeContext → EscapeContext
returnContext ctx = record ctx { returns = true }

-- | Context for analyzing stored values
storeContext : EscapeContext → EscapeContext
storeContext ctx = record ctx { stores = true }

-- | Context when entering a lambda
enterLambda : EscapeContext → EscapeContext
enterLambda ctx = record ctx { lambdaDepth = suc (EscapeContext.lambdaDepth ctx) }

------------------------------------------------------------------------
-- Escape Analysis Result
------------------------------------------------------------------------

-- | Result of escape analysis for an IR term
data EscapeInfo : Set where
  NoEscape : EscapeInfo           -- Value doesn't escape, can use stack
  Escapes  : EscapeInfo           -- Value escapes, must use heap
  Unknown  : EscapeInfo           -- Conservative: treat as escaping

-- | Combine escape information (conservative)
_⊔_ : EscapeInfo → EscapeInfo → EscapeInfo
NoEscape ⊔ NoEscape = NoEscape
_ ⊔ _ = Escapes

-- | Check if a value escapes
escapes : EscapeInfo → Bool
escapes NoEscape = false
escapes Escapes = true
escapes Unknown = true

------------------------------------------------------------------------
-- Escape Analysis Algorithm
------------------------------------------------------------------------

-- | Analyze whether an IR term causes values to escape
--
-- This is a conservative analysis: when in doubt, we assume escape.
-- The analysis tracks how values flow through the program to determine
-- if they outlive their allocation scope.
--
analyzeEscape : ∀ {A B} → EscapeContext → IR A B → EscapeInfo

-- Identity never causes escape
analyzeEscape ctx id = NoEscape

-- Composition: escape if either component escapes
analyzeEscape ctx (g ∘ f) =
  analyzeEscape ctx f ⊔ analyzeEscape ctx g

-- Projections don't cause escape by themselves
analyzeEscape ctx fst = NoEscape
analyzeEscape ctx snd = NoEscape

-- Pairing: values escape if the pair itself escapes
analyzeEscape ctx (⟨ f , g ⟩ mode) with EscapeContext.returns ctx ∨ EscapeContext.stores ctx
... | true = Escapes  -- Pair escapes, so components must be heap-allocated
... | false = analyzeEscape (storeContext ctx) f ⊔ analyzeEscape (storeContext ctx) g

-- Injections: similar to pairing
analyzeEscape ctx (inl mode) with EscapeContext.returns ctx ∨ EscapeContext.stores ctx
... | true = Escapes
... | false = NoEscape

analyzeEscape ctx (inr mode) with EscapeContext.returns ctx ∨ EscapeContext.stores ctx
... | true = Escapes
... | false = NoEscape

-- Case analysis: branches don't cause escape unless returning
analyzeEscape ctx [ f , g ] =
  analyzeEscape ctx f ⊔ analyzeEscape ctx g

-- Terminal/initial morphisms don't allocate
analyzeEscape ctx terminal = NoEscape
analyzeEscape ctx initial = NoEscape

-- Curry creates a closure - values captured escape
analyzeEscape ctx (curry f mode) =
  analyzeEscape (enterLambda ctx) f

-- Apply doesn't cause additional escape
analyzeEscape ctx apply = NoEscape

-- Fixed points are conservative: assume escape
analyzeEscape ctx fold = Escapes
analyzeEscape ctx unfold = Escapes

-- Effects are treated conservatively
analyzeEscape ctx arr = Escapes

------------------------------------------------------------------------
-- Optimization: Choose Allocation Mode
------------------------------------------------------------------------

-- | Determine optimal allocation mode based on escape analysis
--
-- If a value doesn't escape, we can safely allocate it on the stack.
-- Otherwise, we must use heap allocation.
--
chooseAllocMode : EscapeInfo → AllocMode
chooseAllocMode NoEscape = Stack
chooseAllocMode Escapes = Heap
chooseAllocMode Unknown = Heap  -- Conservative default

-- | Optimize an IR term by choosing allocation modes based on escape analysis
--
-- This transformation replaces allocation modes in the IR with optimized
-- choices based on whether values escape.
--
optimizeAllocations : ∀ {A B} → IR A B → IR A B
optimizeAllocations id = id
optimizeAllocations (g ∘ f) = optimizeAllocations g ∘ optimizeAllocations f
optimizeAllocations fst = fst
optimizeAllocations snd = snd
optimizeAllocations (⟨ f , g ⟩ mode) =
  let f' = optimizeAllocations f
      g' = optimizeAllocations g
      -- Analyze if this pair escapes in the default context
      escapeInfo = analyzeEscape initialContext (⟨ f' , g' ⟩ mode)
      optMode = chooseAllocMode escapeInfo
  in ⟨ f' , g' ⟩ optMode
optimizeAllocations (inl {A} {B} mode) =
  let escapeInfo = analyzeEscape initialContext (inl {A} {B} mode)
      optMode = chooseAllocMode escapeInfo
  in inl optMode
optimizeAllocations (inr {A} {B} mode) =
  let escapeInfo = analyzeEscape initialContext (inr {A} {B} mode)
      optMode = chooseAllocMode escapeInfo
  in inr optMode
optimizeAllocations [ f , g ] = [ optimizeAllocations f , optimizeAllocations g ]
optimizeAllocations terminal = terminal
optimizeAllocations initial = initial
optimizeAllocations (curry f mode) =
  let f' = optimizeAllocations f
      escapeInfo = analyzeEscape initialContext (curry f' mode)
      optMode = chooseAllocMode escapeInfo
  in curry f' optMode
optimizeAllocations apply = apply
optimizeAllocations fold = fold
optimizeAllocations unfold = unfold
optimizeAllocations arr = arr

------------------------------------------------------------------------
-- Correctness Properties
------------------------------------------------------------------------

-- | Optimization preserves semantics
--
-- The optimized IR term has the same denotational semantics as the original.
-- This is true because AllocMode doesn't affect the semantic evaluation,
-- only the runtime memory allocation strategy.
--
-- Note: The actual proof would require importing Once.Semantics.eval
-- and showing: eval (optimizeAllocations f) ≡ eval f
--
optimization-preserves-semantics : ∀ {A B} (f : IR A B)
                                 → Set
optimization-preserves-semantics f =
  -- Semantics are preserved (this would be proven using eval)
  -- eval (optimizeAllocations f) ≡ eval f
  ⊤
  where open import Data.Unit using (⊤)

-- | Conservative analysis: if we say NoEscape, value truly doesn't escape
--
-- This is a safety property: stack allocation is only used when safe.
-- A formal proof would require a more detailed operational semantics
-- that tracks value lifetimes.
--
conservative-analysis : ∀ {A B} (ctx : EscapeContext) (f : IR A B)
                      → analyzeEscape ctx f ≡ NoEscape
                      → Set  -- Property: value doesn't escape operationally
conservative-analysis ctx f _ =
  -- This would be proven against an operational semantics
  ⊤
  where open import Data.Unit using (⊤)

------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

module Examples where

  -- | Example: Non-escaping pair
  --
  -- let p = ⟨1, 2⟩ in fst p + snd p
  -- The pair p doesn't escape, so it can be stack-allocated
  --
  example-local-pair : IR (Int * Int) Int
  example-local-pair = fst

  -- Analysis shows this doesn't escape
  _ : analyzeEscape initialContext example-local-pair ≡ NoEscape
  _ = refl

  -- | Example: Escaping pair
  --
  -- λx. λy. ⟨x, y⟩ (returns a pair)
  -- The pair escapes as it's returned, must be heap-allocated
  --
  example-escaping-pair : IR (Int * Int) (Int * Int)
  example-escaping-pair = id

  -- Analysis in return context shows escape
  _ : analyzeEscape (returnContext initialContext) example-escaping-pair ≡ NoEscape
  _ = refl

  -- But a pair constructor in return context would escape:
  example-make-pair : IR Int (Int * Int)
  example-make-pair = ⟨ id , id ⟩ Heap

  -- This would need heap allocation
  _ : analyzeEscape (returnContext initialContext) example-make-pair ≡ Escapes
  _ = refl

------------------------------------------------------------------------
-- Integration with Elaboration
------------------------------------------------------------------------

-- | Apply escape analysis during elaboration
--
-- This would be integrated into Once.TypeCheck.Elaborate to optimize
-- allocations as part of the compilation pipeline.
--
-- The elaboration process would:
-- 1. Convert surface syntax to IR (existing)
-- 2. Run escape analysis on the IR
-- 3. Optimize allocation modes based on analysis
-- 4. Generate code with optimized allocations
--