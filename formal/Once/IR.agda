-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IR
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
--   - Exponentials: curry, apply (ungraded `_⇛_` objects, Plan 0.52 M2)
--   - Recursive types: In/out-μ/Cata/Para, Out/in-ν/Ana, Hylo/Fuse
--   - Primitives: SigOp (opaque external operations)
--   - Memory: free-heap (explicit deallocation)
------------------------------------------------------------------------

module Once.IR where

open import Data.String using (String)

-- Plan 0.52 M2: IR OBJECTS are the UNGRADED `Once.IRTy` (pure/eff arrows are
-- the SAME object, so `arr` is retired). Re-exported so consumers get
-- `Unit`/`_*_`/`_+_`/`_⇛_`/`μ-type`/`⟦_⟧TI`/`WellFormedFI`/`FitsInRegI`/… as IRTy.
open import Once.IRTy public

-- Surface `Type` + `⌊_⌋`, for the `SigOp` FFI boundary ONLY: its objects stay
-- IRTy (`IR ⌊ A ⌋ ⌊ B ⌋`) while the contract `SigOpInfo A B` is surface-typed
-- (the value semantics lives on `Type`). Aliased `T` to avoid the shared
-- constructor names (`Unit`, `_*_`, `μ-type`, …).
open import Once.Type as T using (Type)

-- HeapRef: the `free-heap` constructor's payload (a heap reference). From the
-- lightweight shared HeapAddress module (stdlib-only), NOT the machine.
-- 0.47: `ValueLocation`/`LocMatchesMode` moved OUT — the mode↔location-shape
-- link is a machine-validity predicate (now `Once.CCC.Machine.LocMatchesMode`),
-- not IR syntax. So the IR no longer imports `Once.CCC.Machine.Locations`
-- (→ `FrameSemantics` → `Memory.*`) and is a pure syntax tier modulo HeapRef.
open import Once.Memory.HeapAddress using (HeapRef)

-- D054/0.47: `const` carries the literal's machine-carrier value
-- (`⟦ Carrier ⟧-base A` — the machine `Word` carrier for Int, `Float` for
-- Float), NOT a Core interpretation. This keeps the IR a pure syntax tier
-- with NO dependency on Once.Semantics.Value (`Once.Word` is a primitive,
-- not the semantics layer — like `Memory.HeapAddress` above).
-- `Int`'s denotation IS `Word` per D054. `Carrier` is the WIDTH-AGNOSTIC
-- residue carrier (Once.Word.Carrier): the target word size is threaded
-- from the arch into the modular ops (`norm`/`fromℤ` at codegen/arith,
-- D059), never baked into this literal's type. Literals are non-negative
-- (negation is a separate `OpNeg`).
open import Once.Word using (Carrier)

-- SigOpInfo: the descriptor carried by every signature operation.
open import Once.SigOp.Info public
  using (SigOpInfo; mk-info; name; semM; effect;
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

-- 0.47: `LocMatchesMode` (the mode↔location-shape link) moved to
-- `Once.CCC.Machine.LocMatchesMode` — it is a machine-validity predicate over
-- `ValueLocation`, not IR syntax. Keeping it here forced the IR to import the
-- machine's `Locations`/`FrameSemantics`/`Memory.*`. Its consumers (the
-- compound-type `ValidAtWF` constructors) now import it from there.

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

-- D062 / approach A: `NatTr` (defined mutually below) is the IR-level
-- container-morphism syntax — a natural transformation `G ⇒ F` between the
-- polynomial functors. The structural recursion schemes `Fuse`/`Hylo` carry
-- their transform AS a `NatTr`, so naturality — hence totality of the fold —
-- is by construction (a divergent / value-synthesizing transform is
-- unrepresentable). The meaning translates `NatTr` to `Once.Semantics.Functor.NatSF`
-- and folds it with the pragma-free `fuseNT`/`fuseNTW`; no `fuseW`.
data IR   : IRTy → IRTy → Set
data NatTr : IRFunctor → IRFunctor → Set

data IR where
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

  -- Exponential (A ⇛ B) — the UNGRADED arrow object (Plan 0.52 M2).
  -- The grade lived only on the surface `Type`; here it is erased, so
  -- there is one exponential object per (A, B) and no pure/eff distinction.
  curry : ∀ {A B C} → IR (A * B) C → AllocMode → IR A (B ⇛ C)
  apply : ∀ {A B} → IR ((A ⇛ B) * A) B

  -- `arr` RETIRED (Plan 0.52 M2): it coerced `A ⇒[pure] B` to
  -- `A ⇒[eff] B`, but with the grade erased both are the SAME object
  -- `A ⇛ B`, so `arr` is the identity morphism `id` — removed. The
  -- surface pure→eff lift is now the typing rule `t-subsume`, whose
  -- realization is the identity (no `arr'` wrapper needed post-M2).

  -- fold/unfold removed by OCP-0003: use In/Cata/Out/Ana instead
  -- (Total and productive by construction)

  --------------------------------------------------------------------------
  -- Recursion Schemes (OCP-0003: Total/Productive)
  --
  -- These replace general fold/unfold with structured recursion that
  -- guarantees termination (cata) or productivity (ana).
  --
  -- All constructors require WellFormedFI proofs to ensure functors only
  -- use K with base types, so semantic evaluation is defined for all of them.
  --------------------------------------------------------------------------

  -- Initial algebra operations (inductive types, total recursion)
  -- In: F(μF) → μF (constructor)
  In : ∀ {F} → WellFormedFI F → AllocMode → IR (⟦ F ⟧TI (μ-type F)) (μ-type F)

  -- out-μ: μF → F(μF) (destructor, inverse of In)
  -- By Lambek's Lemma, In is an isomorphism, so its inverse exists.
  -- This enables pattern-matching on μ-types inside Hylo coalgebras,
  -- which is essential for proper fusion in observation primitives.
  -- See OCP-0003 "Lambek Isomorphisms" section.
  out-μ : ∀ {F} → WellFormedFI F → IR (μ-type F) (⟦ F ⟧TI (μ-type F))

  -- Cata: given IR morphism (F(A) → A), produce μF → A
  -- This is the universal property of initial algebras.
  -- Total by Lambek's Lemma: μF is well-founded.
  Cata : ∀ {F} → WellFormedFI F → ∀ {A} → IR (⟦ F ⟧TI A) A → IR (μ-type F) A

  -- Para: paramorphism (fold with access to original substructure)
  -- Total by derivation from Cata (structural recursion on well-founded μF).
  -- The algebra receives F(μF × A), giving access to both the original
  -- substructure and the recursive result.
  Para : ∀ {F} → WellFormedFI F → ∀ {A}
       → IR (⟦ F ⟧TI (μ-type F * A)) A
       → IR (μ-type F) A

  -- Final coalgebra operations (coinductive types, productive corecursion)
  -- Out: νF → F(νF) (observation/destructor)
  Out : ∀ {F} → WellFormedFI F → IR (ν-type F) (⟦ F ⟧TI (ν-type F))

  -- in-ν: F(νF) → νF (constructor, inverse of Out)
  -- By Lambek's Lemma (dual), Out is an isomorphism, so its inverse exists.
  -- Provides symmetry with μ-type operations.
  in-ν : ∀ {F} → WellFormedFI F → AllocMode → IR (⟦ F ⟧TI (ν-type F)) (ν-type F)

  -- Ana: given IR morphism (A → F(A)), produce A → νF
  -- Productivity follows from IR totality: coalgebras are IR morphisms,
  -- IR morphisms are total, therefore each coalgebra step terminates and
  -- produces one F-layer. See IR/Totality.agda and IR/Productivity.agda.
  Ana : ∀ {F} → WellFormedFI F → ∀ {A} → IR A (⟦ F ⟧TI A) → IR A (ν-type F)

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
  -- Termination follows from Fuse.
  --
  Hylo : ∀ {F G} → WellFormedFI F → WellFormedFI G → ∀ {B}
       → IR (⟦ F ⟧TI B) B                          -- algebra: F(B) → B
       → NatTr G F                                  -- structural coalgebra: μG --out-μ--> G ⇒ F
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
  -- Termination is structural.
  --
  Fuse : ∀ {F G} → WellFormedFI F → WellFormedFI G → ∀ {B}
       → IR (⟦ F ⟧TI B) B                              -- algebra: F(B) → B
       → NatTr G F                                      -- natural transform: G ⇒ F
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
  -- Carries the literal's machine-carrier value `⟦ Carrier ⟧-base A`
  -- (the `Word` carrier for Int, `Float` for Float) — Value-free, so the IR
  -- is a pure syntax tier. (D054: an `Int` literal denotes a `Word`; the
  -- carrier is width-agnostic and the target word size is threaded from the
  -- arch into `norm`/`fromℤ` at codegen/arith. Non-negative; neg is `OpNeg`.)
  const : ∀ {A} → FitsInRegI A → ⟦ Carrier ⟧-baseI A → IR Unit A

  -- Signature operations (opaque escape hatch).
  -- Carries a `SigOpInfo` (name + sem at both levels) so the IR
  -- is self-describing; no external `SigOpSem` parameter needed.
  -- FFI boundary (Plan 0.52 M2): the contract `SigOpInfo A B` is surface-typed
  -- (its value semantics `M.⟦A⟧→M.⟦B⟧` lives on `Type`); the IR OBJECTS it
  -- connects are the erased `⌊ A ⌋`, `⌊ B ⌋`.
  SigOp : ∀ {A B : Type} → SigOpInfo A B → IR ⌊ A ⌋ ⌊ B ⌋

------------------------------------------------------------------------
-- NatTr — IR-level natural transformations between polynomial functors
--
-- The compilable, manifestly-natural witness carried by `Fuse`/`Hylo`.
-- Mirrors `Once.Semantics.Functor.NatSF` one level up (over the object-language
-- `Functor`/`Type` rather than `SFunctor`/`Set`), so the IR stays
-- interpretation-agnostic. Source eliminators (`ntFst`/`ntSnd`/`ntCase`)
-- and target introductions (`ntInl`/`ntInr`/`ntPair`) interleave; leaves are
-- the identity on the recursive position (`ntId`) and a pure constant map,
-- itself an IR morphism (`ntK`) — the reason `NatTr` is mutual with `IR`.
--
-- By construction a `NatTr` only routes/copies/discards the recursive
-- positions, never inspecting or synthesizing μ-substructure; its meaning
-- (`Once.Semantics.Functor.appNatSF` after translation) is a genuine natural
-- transformation (`appNatSF-natural`), hence the folds `fuseNT`/`fuseNTW`
-- that consume it are total without any the termination pragma.
data NatTr where
  ntId   : NatTr Id Id
  ntK    : ∀ {A B} → IR A B → NatTr (K A) (K B)
  ntFst  : ∀ {G₁ G₂ F} → NatTr G₁ F → NatTr (G₁ ⊗ G₂) F
  ntSnd  : ∀ {G₁ G₂ F} → NatTr G₂ F → NatTr (G₁ ⊗ G₂) F
  ntCase : ∀ {G₁ G₂ F} → NatTr G₁ F → NatTr G₂ F → NatTr (G₁ ⊕ G₂) F
  ntInl  : ∀ {G F₁ F₂} → NatTr G F₁ → NatTr G (F₁ ⊕ F₂)
  ntInr  : ∀ {G F₁ F₂} → NatTr G F₂ → NatTr G (F₁ ⊕ F₂)
  ntPair : ∀ {G F₁ F₂} → NatTr G F₁ → NatTr G F₂ → NatTr G (F₁ ⊗ F₂)

infixr 9 _∘_
infixr 4 ⟨_,_⟩