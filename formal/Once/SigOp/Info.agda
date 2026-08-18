-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.SigOp.Info
--
-- The signature-operation descriptor carried by every `SigOp` IR node.
--
-- A `SigOpInfo A B` is a self-describing escape hatch: it identifies
-- an externally-defined morphism A → B by its `name`, and carries
-- the semantic function at both levels of interpretation:
--
--   - semI : ⟦A⟧ᶻ → ⟦B⟧ᶻ   — frontend / proof semantics (Int ≡ ℤ)
--   - semM : ⟦A⟧ⁿ → ⟦B⟧ⁿ   — machine semantics (Int ≡ ℕ)
--
-- Both fields are definitional for pure operations (e.g. arithmetic),
-- trivially Unit-valued for termination effects (exit), or
-- postulated for environment-reading effects (read). Each provider
-- module (each interpretation's provider/contract module,
-- `Once/Arith/SigOp/IntLit.agda`, …) constructs its `SigOpInfo`s
-- with whichever semantic shape is appropriate.
--
-- Decidable equality on `SigOpInfo` compares only `name`. Two
-- `SigOpInfo`s with the same name are identified as equal; the
-- surface-to-IR elaborator is a function, so same name ⟹ same
-- info by construction.
--
-- This module is the CCC-layer abstract machinery for signature
-- operations; it has no knowledge of specific type constructors
-- (Int, Float, etc.). Per D047 (SigOp rename) and plan 0.2.4.1.
------------------------------------------------------------------------

module Once.SigOp.Info where

open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; _≟_)
open import Once.CanonicalName using (CanonicalName; _≟ᶜ_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type; Unit)
-- Plan 0.58 (OCP-0006): a SigOp is an FFI/register-ABI boundary, so its argument
-- and result types must be CONCRETE (`IsBaseType` — no arrows, no `μ`/`ν`). This is
-- enforced BY CONSTRUCTION here: a `SigOpInfo` cannot be built at a non-base type.
open import Once.Functor.Translate using (IsBaseType; IsConcrete)

-- | Frontend / proof-level interpretation (Int ≡ ℤ).
-- (Core ℤ `as I` removed: semI deleted — the machine `semM` is the meaning.)

-- | Machine-level interpretation (Int ≡ ℕ).
open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
import Once.Semantics.Value Carrier Dyadic as M

------------------------------------------------------------------------
-- EffectShape — the SigOp's effect *shape*, indexed by codomain
-- (Plan 0.25).
--
-- Classifies what a SigOp does observably. CCC's abstract machine
-- dispatches per shape to derive machine output, halt-flag, and
-- trace-event payload from `semM` + the tag — so per-SigOp facts
-- (formerly `exec-sigop-output` / `exec-sigop-halts` postulates) are
-- no longer needed at this layer.
--
-- The coherence requirement `Emits`/`Halts` ⇒ `R ≡ Unit` is built
-- INTO the constructors: those two carry a `B ≡ Unit` proof, so a
-- producer cannot declare a non-Unit-codomain SigOp as `Emits`/`Halts`
-- (the constructor simply won't construct). For `Pure`, B is
-- unconstrained.
--
-- Layer 0 needs `Pure` + `Halts` (`Emits` is reserved for the next
-- syscall layer). New shapes (e.g. `ReadsWorld` for a `read` syscall)
-- grow the type additively; each new constructor earns one generic
-- CCC dispatch case + one `respects-semM` lemma — the closed type
-- is what enforces "faithful classification" as a discipline.
------------------------------------------------------------------------

data EffectShape (B : Type) : Set where
  -- | Pure value computation. No trace event, no halt; the machine
  -- output is `wrap (semM x)`. Codomain unrestricted.
  Pure  : EffectShape B
  -- | Observable event, continues. The event records the SigOp's
  -- input; codomain must be `Unit` (reserved for a `write`/emitting syscall etc.).
  Emits : B ≡ Unit → EffectShape B
  -- | Observable event, ends the program. The event records the
  -- SigOp's input (e.g. the exit code); codomain must be `Unit`.
  -- Used by the exit syscall.
  Halts : B ≡ Unit → EffectShape B

------------------------------------------------------------------------
-- SigOpSem — the SigOp's semantics, UNIFYING value and effect (Plan
-- 0.38 M0.2).
--
-- A SigOp carries EITHER a proven pure value (an internal producer —
-- `arith.*`, `lit.*`, `arith.block.*` — whose value Once derives and
-- proves) OR an effect CONTRACT (an external op — a syscall — whose
-- value is the producer's off-line concern, NOT CCC's). For an
-- effect contract there is NO value field: the machine output is `tt`
-- by the `B ≡ Unit` coherence the constructor carries.
--
-- This makes it STRUCTURALLY IMPOSSIBLE to bake an opaque external
-- value into an effectful SigOp: an effectful op carries a contract,
-- never a value. The earlier `generic-semM` syscall laundering cannot
-- be expressed — the only place an opaque value can still live is a
-- `pureV` (the named-pure-value `closure`/`poly` positions, a separate
-- function-linking concern, NOT a syscall contract).
------------------------------------------------------------------------

data SigOpSem (A B : Type) : Set where
  -- | Internal producer: a proven machine value function.
  pureV : (M.⟦ A ⟧ → M.⟦ B ⟧) → SigOpSem A B
  -- | External op, observable, continues. Value is `tt` (B ≡ Unit).
  emitsV : B ≡ Unit → SigOpSem A B
  -- | External op, observable, terminates the machine. Value is `tt`.
  haltsV : B ≡ Unit → SigOpSem A B

------------------------------------------------------------------------
-- Linkage — how a `SigOp`'s result type is provided (Plan 0.58 / D071).
--
-- A `SigOp` node is the IR's carrier for a NAMED morphism. D071 splits the
-- two kinds a name can denote:
--
--   • `ffi-concrete` — a genuine FFI / register-ABI boundary (D061). Such a
--     boundary passes CONCRETE values (base scalars or first-order function
--     pointers), so it carries an `IsConcrete B` witness. This keeps the
--     Plan-0.58 concreteness discipline intact for real syscalls/intrinsics.
--
--   • `internal-ref` — a same-module definition reference (`poly`/`closure`,
--     D064). The linked value is a code/closure pointer produced by internal
--     linkage (`once_<name>`), representable at ANY source type — so it needs
--     NO concreteness witness. This is what dissolves the totality wall D071
--     diagnosed: an internal reference of arbitrary type (`μNat → Int`, …) is
--     a projection from the definition context Γ, not an FFI value.
--
-- The tag is proof-irrelevant carry-along (`conB` is never read); it records
-- the FFI/internal distinction structurally rather than as a separate IR node.
------------------------------------------------------------------------

data Linkage (B : Type) : Set where
  ffi-concrete : IsConcrete B → Linkage B
  internal-ref : Linkage B

------------------------------------------------------------------------
-- SigOpInfo
------------------------------------------------------------------------

-- | Descriptor for a signature operation `name : A → B`.
--
-- Decoupled from the CCC structure: every `SigOp` in the IR carries
-- an info value, making the IR self-describing. No `SigOpSem`
-- parameter threading through eval / desugar / correctness proofs.
--
-- The `effect` tag (Plan 0.25) classifies the SigOp's observable
-- shape and is consumed by CCC's per-class abstract-machine dispatch
-- and `respects-semM` lemmas — replacing the per-SigOp
-- `exec-sigop-output` / `exec-sigop-halts` / `exec-sigop-respects-semM`
-- postulates with proven facts.
record SigOpInfo (A B : Type) : Set where
  constructor mk-info'
  field
    name : CanonicalName            -- Plan 0.50: the resolved [path…, name] identity
    sem  : SigOpSem A B              -- proven value (internal) OR effect contract (external)
    -- Plan 0.58: the ARGUMENT is a base type (a register/ABI scalar — a
    -- higher-order callback arg is out of scope). Proof-irrelevant.
    baseA : IsBaseType A
    -- Plan 0.58 / D071: the RESULT's linkage — an FFI boundary carries an
    -- `IsConcrete B` witness; an internal definition reference carries none
    -- (`internal-ref`). Proof-irrelevant carry-along (never read).
    conB  : Linkage B

open SigOpInfo public

------------------------------------------------------------------------
-- Derived accessors — `semM` and `effect` are now DERIVED from `sem`
-- (not stored fields), so every existing reader (`semM si x`,
-- `effect si`) is unchanged while the underlying representation can no
-- longer carry an opaque external value.
--
-- `semM` of an effect contract is `tt` (B ≡ Unit by the constructor's
-- coherence) — the machine output the `Emits`/`Halts` codegen produces.
------------------------------------------------------------------------

semM : ∀ {A B} → SigOpInfo A B → M.⟦ A ⟧ → M.⟦ B ⟧
semM si = go (sem si)
  where
    go : ∀ {A B} → SigOpSem A B → M.⟦ A ⟧ → M.⟦ B ⟧
    go (pureV f)     = f
    go (emitsV refl) = λ _ → tt
    go (haltsV refl) = λ _ → tt

effect : ∀ {A B} → SigOpInfo A B → EffectShape B
effect si = go (sem si)
  where
    go : ∀ {A B} → SigOpSem A B → EffectShape B
    go (pureV _)  = Pure
    go (emitsV e) = Emits e
    go (haltsV e) = Halts e

------------------------------------------------------------------------
-- Compatibility constructor — maps the old `(value, effect)` pair into
-- `SigOpSem`, DROPPING the value for effect contracts (`Emits`/`Halts`):
-- an effectful op's value is `tt` by coherence, so the supplied
-- function is discarded — this is exactly what makes the syscall
-- laundering unrepresentable. `Pure` keeps its value as `pureV`.
------------------------------------------------------------------------

mk-info : ∀ {A B} → CanonicalName → (M.⟦ A ⟧ → M.⟦ B ⟧) → EffectShape B
        → IsBaseType A → IsConcrete B → SigOpInfo A B
mk-info nm f Pure      bA cB = mk-info' nm (pureV f)     bA (ffi-concrete cB)
mk-info nm f (Emits e) bA cB = mk-info' nm (emitsV e)    bA (ffi-concrete cB)
mk-info nm f (Halts e) bA cB = mk-info' nm (haltsV e)    bA (ffi-concrete cB)

------------------------------------------------------------------------
-- Name-only equality
------------------------------------------------------------------------

-- | `SigOpInfo`s are compared structurally by `name` only.
_≟SigOpInfo-name_ : ∀ {A B} (si₁ si₂ : SigOpInfo A B) → Dec (name si₁ ≡ name si₂)
si₁ ≟SigOpInfo-name si₂ = name si₁ ≟ᶜ name si₂

-- | Name coherence (axiomatic).
--
-- Two `SigOpInfo`s with equal names are considered equal. The
-- semantic fields (`semI`, `semM`) are not compared — they are
-- derived data, not identity. The surface-to-IR elaborator is a
-- function, so in practice same-name-implies-same-record by
-- construction; this postulate makes that coherence visible to the
-- optimizer's decidable IR equality.
--
-- Under D047, a SigOp is a member of the signature Σ identified by
-- its `name`. Equality of signature elements is equality of names.
postulate
  sigOpInfo-name-coherence :
    ∀ {A B} (si₁ si₂ : SigOpInfo A B) → name si₁ ≡ name si₂ → si₁ ≡ si₂

-- | Decidable equality on `SigOpInfo` (via name + coherence).
_≟SigOpInfo_ : ∀ {A B} (si₁ si₂ : SigOpInfo A B) → Dec (si₁ ≡ si₂)
si₁ ≟SigOpInfo si₂ with si₁ ≟SigOpInfo-name si₂
... | yes eq = yes (sigOpInfo-name-coherence si₁ si₂ eq)
... | no ne = no (λ { refl → ne refl })
