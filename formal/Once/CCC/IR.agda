-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.IR
--
-- The core IR based on Cartesian Closed Categories.
--
-- This is THE IR for Once - the categorical foundation that everything
-- else compiles to. Surface syntax is sugar on top.
--
-- Structure:
--   - Category: id, _∘_
--   - Products: ⟨_,_⟩, fst, snd
--   - Coproducts: inl, inr, case
--   - Terminal/Initial: terminal, initial
--   - Exponentials: curry, apply
--   - Recursive types: fold, unfold
--   - Effects: arr
--   - Primitives: SigOp (opaque external operations)
--   - Memory: free-heap (explicit deallocation)
------------------------------------------------------------------------

module Once.CCC.IR where

open import Data.String using (String)

-- Import and re-export Type
open import Once.Type public

-- Import WellFormedF for recursion scheme constructors
open import Once.Functor.Translate using (WellFormedF)

-- HeapRef and ValueLocation: needed for the LocMatchesMode predicate below.
open import Once.CCC.Machine.SMCore
  using (HeapRef; ValueLocation; AtStack; AtDynamic)

-- Eval semantics universes — `const` carries values at BOTH levels,
-- mirroring `SigOpInfo`'s `semI` + `semM` pattern. The proof-level
-- value (signed integers, etc.) is used by `Once.Semantics.IR.eval′`;
-- the machine-level value (unsigned, etc.) by `Once.CCC.Eval.eval`.
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
import Once.Semantics.Core ℤ as I
import Once.Semantics.Core ℕ as M

-- SigOpInfo: the descriptor carried by every signature operation.
open import Once.CCC.SigOp.Info public
  using (SigOpInfo; mk-info; name; semI; semM; effect;
         EffectShape; Pure; Emits; Halts)

------------------------------------------------------------------------
-- Allocation Mode
--
-- Specifies stack vs heap allocation for compound values.
-- Used by escape analysis and code generation.
------------------------------------------------------------------------

data AllocMode : Set where
  Stack : AllocMode  -- Allocate inline on stack (non-escaping)
  Heap  : AllocMode  -- Allocate on heap (escaping)

------------------------------------------------------------------------
-- LocMatchesMode: link between mode and location shape
--
-- Plan 0.14 (Camp 2): make the mode tag in ValidAtWF semantically
-- meaningful. A compound value's representation lives where its mode
-- says: Stack-mode compounds at AtStack locations, Heap-mode at
-- AtDynamic. The Place stage's "mode matches loc shape" discipline is
-- surfaced into the proof system here, so any ValidAtWF Heap … loc …
-- carries the witness loc = AtDynamic _.
--
-- Note: only used by compound-type ValidAtWF constructors (pair /
-- inl / inr / closure / μ / ν). Primitives can live at any loc
-- regardless of mode because writeLoc (since Plan 0.14) accepts
-- primitive StoredValues in heap cells and any StoredValue in stack
-- cells.
------------------------------------------------------------------------

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

LocMatchesMode : ∀ {FS} → AllocMode → ValueLocation FS → Set
LocMatchesMode Stack (AtStack _ _)  = ⊤
LocMatchesMode Stack (AtDynamic _)  = ⊥
LocMatchesMode Heap  (AtStack _ _)  = ⊥
LocMatchesMode Heap  (AtDynamic _)  = ⊤

------------------------------------------------------------------------
-- Allocator (Plan 0.2.4.5)
--
-- The replacement for AllocMode under the IR-destination-passing
-- design. Per-allocation choice between:
--
--   Stack   - frame-bound; codegen lowers to frontier-bump (no
--             runtime call). Implicit free on frame pop.
--
--   Dynamic - runtime call to alloc/free SigOps. Pool, Arena, malloc
--             all collapse into Dynamic at the IR level — the
--             specific allocator (function symbol) is a
--             Place-time decision, not a runtime/link-time concern.
--
-- The IR itself does NOT pick this — it's chosen upstream by the
-- Place pass (Plan 0.2.4.6) and threaded as a destination
-- annotation. AllocMode's role in IR signatures is being phased
-- out; Allocator carries the same binary distinction with explicit
-- naming aligned with the Allocator-vs-Place architecture.
------------------------------------------------------------------------

data Allocator : Set where
  Stack-allocator   : Allocator
  Dynamic-allocator : Allocator

------------------------------------------------------------------------
-- IR Language
--
-- CCC-based intermediate representation.
------------------------------------------------------------------------

data IR : Type → Type → Set where
  -- Category structure
  id : ∀ {A} → IR A A
  _∘_ : ∀ {A B C} → IR B C → IR A B → IR A C

  -- Product (A * B)
  ⟨_,_⟩ : ∀ {A B C} → IR A B → IR A C → AllocMode → IR A (B * C)
  fst : ∀ {A B} → IR (A * B) A
  snd : ∀ {A B} → IR (A * B) B

  -- Coproduct (A + B)
  inl : ∀ {A B} → AllocMode → IR A (A + B)
  inr : ∀ {A B} → AllocMode → IR B (A + B)
  case : ∀ {A B C} → IR A C → IR B C → IR (A + B) C

  -- Terminal object (Unit)
  terminal : ∀ {A} → IR A Unit

  -- Initial object (Void)
  initial : ∀ {A} → IR Void A

  -- Exponential (A ⇒[ k ] B). Plan 0.5.1: unified apply for any kind.
  -- Callers typically use `pureK q` (pure) or `effK` (effectful).
  curry : ∀ {A B C k} → IR (A * B) C → AllocMode → IR A (B ⇒[ k ] C)
  apply : ∀ {A B k} → IR ((A ⇒[ k ] B) * A) B

  -- Effect lifting: coerce a pure arrow to an effectful one.
  -- Both sides are `_⇒[_]_` types distinguished only by kind; `arr`
  -- takes a pure arrow and tags it as effectful. Runtime: identity.
  arr : ∀ {A B q} → IR (A ⇒[ mk-kind q pure ] B) (A ⇒[ mk-kind Many eff ] B)

  -- applyEff removed in plan 0.5.1: `apply {k = effK}` handles
  -- effectful application. Runtime is identical (same code); the
  -- distinction was only type-level tagging.

  -- fold/unfold removed by OCP-0003: use In/Cata/Out/Ana instead
  -- (Total and productive by construction)

  --------------------------------------------------------------------------
  -- Recursion Schemes (OCP-0003: Total/Productive)
  --
  -- These replace general fold/unfold with structured recursion that
  -- guarantees termination (cata) or productivity (ana).
  --
  -- All constructors require WellFormedF proofs to ensure functors only
  -- use K with base types, enabling postulate-free semantic evaluation.
  --------------------------------------------------------------------------

  -- Initial algebra operations (inductive types, total recursion)
  -- In: F(μF) → μF (constructor)
  In : ∀ {F} → WellFormedF F → AllocMode → IR (⟦ F ⟧T (μ-type F)) (μ-type F)

  -- out-μ: μF → F(μF) (destructor, inverse of In)
  -- By Lambek's Lemma, In is an isomorphism, so its inverse exists.
  -- This enables pattern-matching on μ-types inside Hylo coalgebras,
  -- which is essential for proper fusion in observation primitives.
  -- See OCP-0003 "Lambek Isomorphisms" section.
  out-μ : ∀ {F} → WellFormedF F → IR (μ-type F) (⟦ F ⟧T (μ-type F))

  -- Cata: given IR morphism (F(A) → A), produce μF → A
  -- This is the universal property of initial algebras.
  -- Total by Lambek's Lemma: μF is well-founded.
  Cata : ∀ {F} → WellFormedF F → ∀ {A} → IR (⟦ F ⟧T A) A → IR (μ-type F) A

  -- Para: paramorphism (fold with access to original substructure)
  -- Total by derivation from Cata (structural recursion on well-founded μF).
  -- The algebra receives F(μF × A), giving access to both the original
  -- substructure and the recursive result.
  Para : ∀ {F} → WellFormedF F → ∀ {A}
       → IR (⟦ F ⟧T (μ-type F * A)) A
       → IR (μ-type F) A

  -- Final coalgebra operations (coinductive types, productive corecursion)
  -- Out: νF → F(νF) (observation/destructor)
  Out : ∀ {F} → WellFormedF F → IR (ν-type F) (⟦ F ⟧T (ν-type F))

  -- in-ν: F(νF) → νF (constructor, inverse of Out)
  -- By Lambek's Lemma (dual), Out is an isomorphism, so its inverse exists.
  -- Provides symmetry with μ-type operations.
  in-ν : ∀ {F} → WellFormedF F → AllocMode → IR (⟦ F ⟧T (ν-type F)) (ν-type F)

  -- Ana: given IR morphism (A → F(A)), produce A → νF
  -- Productivity follows from IR totality: coalgebras are IR morphisms,
  -- IR morphisms are total, therefore each coalgebra step terminates and
  -- produces one F-layer. See IR/Totality.agda and IR/Productivity.agda.
  Ana : ∀ {F} → WellFormedF F → ∀ {A} → IR A (⟦ F ⟧T A) → IR A (ν-type F)

  -- Guard/Unguard removed: GuardedT was unnecessary.
  -- Productivity follows from IR totality, not type-level guardedness.
  -- See IR/Totality.agda for the proof that all IR coalgebras are "guarded".

  -- Hylo: fusion of cata and ana (deforestation) - CORRECT BY CONSTRUCTION
  -- cata alg ∘ ana coalg, computed directly without intermediate structure
  --
  -- OCP-0003: Hylo is now based on Fuse, removing the need for TerminatesOn.
  -- Termination is guaranteed by requiring μG as input:
  -- - Input1 is μG (well-founded inductive type)
  -- - Coalgebra produces F-layers from μG values
  -- - Recursion is structural on μG
  --
  -- Semantically: Hylo alg coalg ≡ Fuse alg (coalg ∘ In)
  -- The coalgebra wraps In to convert the pre-destructed G-layer to F-layer.
  --
  -- NO TERMINATING PRAGMA NEEDED - termination follows from Fuse!
  --
  Hylo : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
       → IR (⟦ F ⟧T B) B                          -- algebra: F(B) → B
       → IR (μ-type G) (⟦ F ⟧T (μ-type G))        -- coalgebra: μG → F(μG)
       → IR (μ-type G) B

  -- Fuse: μ-anchored fusion (deforestation) - CORRECT BY CONSTRUCTION
  --
  -- OCP-0003: Structured fusion that is provably terminating.
  -- Unlike Hylo, termination is guaranteed by the type structure:
  -- - Input1 is μG (well-founded inductive type)
  -- - Transform receives pre-destructed G-layer via out-μ
  -- - Recursion is structural on μG - each recursive call on strict subterm
  --
  -- The transform converts G-layers to F-layers without changing recursive depth:
  --   transform : G(μG) → F(μG)
  --
  -- Semantically: Fuse alg transform = cata (alg ∘ transform)
  -- But computed via direct recursion for deforestation.
  --
  -- NO TERMINATING PRAGMA NEEDED - termination is structural!
  --
  Fuse : ∀ {F G} → WellFormedF F → WellFormedF G → ∀ {B}
       → IR (⟦ F ⟧T B) B                              -- algebra: F(B) → B
       → IR (⟦ G ⟧T (μ-type G)) (⟦ F ⟧T (μ-type G))   -- transform: G(μG) → F(μG)
       → IR (μ-type G) B

  -- Explicit heap deallocation
  -- Added by escape analysis when heap values can be freed.
  free-heap : HeapRef → IR Unit Unit

  -- Constant / global element of a primitive type.
  --
  -- Categorically: a morphism 1 → A picking out the value `v ∈ A`.
  -- In any concrete CCC, every element corresponds to such a global
  -- element; this ctor names the syntactic form.
  --
  -- Restricted to types `A` for which `FitsInReg A` is inhabited
  -- (Int, Float — see `Once.Type.FitsInReg`).
  -- This restriction prevents nonsense like `const … (λ x → x)`
  -- (function-typed constants are not compilable). Compound
  -- constants are built structurally via `⟨_,_⟩`, `inl`, `inr`
  -- composed with primitive `const`s. Unit constants don't go
  -- through `const` — they are produced by `terminal` (Unit is
  -- erased throughout the IR semantics post Plan 0.2.4.5).
  --
  -- Carries values at BOTH semantic levels (proof-level `I.⟦A⟧` with
  -- Int ≡ ℤ, machine-level `M.⟦A⟧` with Int ≡ ℕ), mirroring
  -- `SigOpInfo.semI` / `semM`. CCC doesn't define a conversion;
  -- the user supplies both.
  const : ∀ {A} → FitsInReg A → I.⟦ A ⟧ → M.⟦ A ⟧ → IR Unit A

  -- Signature operations (opaque escape hatch).
  -- Carries a `SigOpInfo` (name + sem at both levels) so the IR
  -- is self-describing; no external `SigOpSem` parameter needed.
  SigOp : ∀ {A B} → SigOpInfo A B → IR A B

infixr 9 _∘_
infixr 4 ⟨_,_⟩