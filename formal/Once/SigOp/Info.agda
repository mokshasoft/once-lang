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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Once.Type using (Type; Unit; Void)
open import Once.Res using (Res; stopped; returns; is-stopped; mapRes)
open import Data.Bool using (Bool; true; false)
-- Plan 0.58 (OCP-0006): a SigOp is an FFI/register-ABI boundary, so its argument
-- and result types must be CONCRETE (`IsBaseType` — no arrows, no `μ`/`ν`). This is
-- enforced BY CONSTRUCTION here: a `SigOpInfo` cannot be built at a non-base type.
open import Once.Functor.Translate using (IsBaseType; IsConcrete; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum)

-- | Frontend / proof-level interpretation (Int ≡ ℤ).
-- (Core ℤ `as I` removed: semI deleted — the machine `semM` is the meaning.)

-- | Machine-level interpretation (Int ≡ ℕ).
open import Once.Word using (Carrier)
-- Plan 0.74 J5 (D059): a SigOp's machine semantics is TARGET-RELATIVE.
open import Once.Target.Arch using (TargetNum)
open import Once.Float.Dyadic using (Dyadic)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Arith.Prim using (ArithPrim; primSem)

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
  -- | Observable event, ENDS THE PROGRAM. The event records the SigOp's
  -- input (e.g. the exit code), and the codomain is `Void`: the call does
  -- not return, so there is no result for it to have. Used by the exit
  -- syscall.
  --
  -- plan 0.98: this index was `B ≡ Unit`, IDENTICAL to `Emits`'. That is
  -- what made a halting SigOp indistinguishable IN THE TYPE from an emitting
  -- one — so the surface path could drop the distinction, and the dropped bit
  -- had to be stashed in a name-keyed side table. `Void` puts it back in the
  -- type, where both presentations of the meaning read it.
  Halts : B ≡ Void → EffectShape B
  -- | plan 0.105: observable event, continues WITH AN ANSWER the
  -- interpretation supplies (an input: `getpid`, `fd_read`). The codomain is
  -- data.
  Answers : EffectShape B

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
  --
  -- PLAN 0.74 J5 (D059) — it takes the TARGET'S NUMERICS. It used to be a
  -- closed `M.⟦ A ⟧ → M.⟦ B ⟧`, and `Arith/SigOp/Builders` accordingly
  -- computed `arith.neg.int` with `Word64.⊝` on every target. That is not an
  -- untidy import: `Denotation/Meaning`'s `⟦ t-neg d ⟧ᵢ` reaches this
  -- function, so on x86-32 the SPEC said `⟦ neg (int 5) ⟧ = 2^64 - 5`, which
  -- is not even a 32-bit word, while literals in the same expression were
  -- already width-correct. Nothing was red because `block-semM` and
  -- `ArithSimX86-32` baked 64 as well — two sides wrong together, the same
  -- shape as D114's `isInt?` and the `absℤ` bug.
  --
  -- D250: the result is GRADED (`M.⟦_⟧ᵍ`): a contract is a value of its declared
  -- type, so a pure one's function pointer is total. The machine reads its
  -- erasure (`semM`).
  pureV : (TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧ᵍ) → SigOpSem A B
  -- | plan 0.105: a PURE FFI contract. Its value is the interpretation's
  -- (D061): the compiler knows only its name and declared types.
  ffiV : SigOpSem A B
  -- | plan 0.105: an EFFECTFUL FFI contract answering data. A call: the
  -- interpretation answers it, given the calls before it.
  callsV : SigOpSem A B
  -- | External op, observable, continues. Value is `tt` (B ≡ Unit).
  emitsV : B ≡ Unit → SigOpSem A B
  -- | External op, observable, TERMINATES the machine. There is no value:
  -- the call does not return (`B ≡ Void`), which is why `semM` lands in
  -- `Res` rather than producing one.
  haltsV : B ≡ Void → SigOpSem A B
  -- | D255: a compiler-minted arithmetic primitive. Its meaning is FIXED by the
  -- primitive (`primSem`), so "this SigOp is addition" is a constructor match.
  primV : ArithPrim A B → SigOpSem A B

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
    -- plan 0.105: the RESULT is a base type too — a register/ABI value, never
    -- a closure. (Plan 0.58 had `IsConcrete B`; D245 moved definition
    -- references to `Call`, and FFI contracts are first-order, so no SigOp
    -- returns a function.)
    conB  : IsBaseType B

open SigOpInfo public

------------------------------------------------------------------------
-- Derived accessors — `semM` and `effect` are now DERIVED from `sem`
-- (not stored fields), so every existing reader (`semM si x`,
-- `effect si`) is unchanged while the underlying representation can no
-- longer carry an opaque external value.
--
-- `semM` of an EMITTING contract is `tt` (`B ≡ Unit` by the constructor's
-- coherence). A HALTING contract has no value at all — plan 0.98 — so `semM`
-- lands in `Res`: a SigOp's semantics either RETURNS a value or ENDS the
-- program. That keeps it total while making "a halting op has no result" a
-- fact of the type rather than a flag somebody has to remember to consult.
------------------------------------------------------------------------

-- PLAN 0.74 J5: the target's numerics come FIRST, before the argument, so a
-- partially-applied `semM si tn` is still the old shape and reads naturally at
-- the call sites that already have a `TargetNum` in hand (the denotation
-- threads one as `fmt`; the machine has `fs-numerics FS`).
-- plan 0.98: HOISTED OUT OF THEIR `where`s. `effect` and `semM` are two
-- readings of the SAME field, and after 0.98 a consumer that has matched on
-- one has to conclude about the other — 0.97 got that for free because its
-- `stops-D si` was DEFINED as `stops-D-of (effect si)`, so the two could not
-- disagree by construction. They can now, and the honest replacement is a
-- LEMMA relating them (`semM-stops` below). A `where`-bound dispatch cannot
-- carry one: neither reduces on `sem si` for a variable `si`, so there is
-- nothing to case-split. As top-level functions of `SigOpSem` there is.
-- plan 0.105: what an FFI contract returns is not the compiler's to compute.
-- `FFIAnswers` is that value, supplied by whoever has the interpretation (the
-- machine builds it from the interpretation and its event log); internal
-- operations ignore it.
-- It is PARTIAL (D257 (A)): a world provides some contracts, not every
-- conceivable one (some codomains are empty), so an unprovided one is
-- `stopped` — unreachable for a program linked against that world.
FFIAnswers : Set
FFIAnswers = CanonicalName → (A B : Type) → M.⟦ A ⟧ → Res M.⟦ B ⟧

-- A base value in the graded domain (they coincide at first-order types).
liftᵇ : ∀ {B} → IsBaseType B → M.⟦ B ⟧ → M.⟦ B ⟧ᵍ
liftᵇ base-Unit        x       = x
liftᵇ base-Void        x       = x
liftᵇ base-Int         x       = x
liftᵇ base-Float       x       = x
liftᵇ (base-Prod a b)  (x , y) = liftᵇ a x , liftᵇ b y
liftᵇ (base-Sum a b)   (inj₁ x) = inj₁ (liftᵇ a x)
liftᵇ (base-Sum a b)   (inj₂ y) = inj₂ (liftᵇ b y)

eraseᵇ-liftᵇ : ∀ {B} (b : IsBaseType B) (x : M.⟦ B ⟧) → M.eraseᵍ (liftᵇ b x) ≡ x
eraseᵇ-liftᵇ base-Unit        x        = refl
eraseᵇ-liftᵇ base-Void        x        = refl
eraseᵇ-liftᵇ base-Int         x        = refl
eraseᵇ-liftᵇ base-Float       x        = refl
eraseᵇ-liftᵇ (base-Prod a b)  (x , y)  = cong₂ _,_ (eraseᵇ-liftᵇ a x) (eraseᵇ-liftᵇ b y)
eraseᵇ-liftᵇ (base-Sum a b)   (inj₁ x) = cong inj₁ (eraseᵇ-liftᵇ a x)
eraseᵇ-liftᵇ (base-Sum a b)   (inj₂ y) = cong inj₂ (eraseᵇ-liftᵇ b y)

semM-of : ∀ {A B} → FFIAnswers → CanonicalName → SigOpSem A B → TargetNum → M.⟦ A ⟧ → Res M.⟦ B ⟧
semM-of ans n (pureV f)     = λ tn x → returns (M.eraseᵍ (f tn x))
semM-of ans n (emitsV refl) = λ _ _ → returns tt
semM-of ans n (haltsV refl) = λ _ _ → stopped
semM-of ans n (primV p)     = λ tn x → returns (M.eraseᵍ (primSem p tn x))
semM-of {A} {B} ans n ffiV   = λ _ x → ans n A B x
semM-of {A} {B} ans n callsV = λ _ x → ans n A B x

effect-of : ∀ {A B} → SigOpSem A B → EffectShape B
effect-of (pureV _)  = Pure
effect-of (emitsV e) = Emits e
effect-of (haltsV e) = Halts e
effect-of (primV _)  = Pure
effect-of ffiV       = Pure
effect-of callsV     = Answers

semM : ∀ {A B} → FFIAnswers → SigOpInfo A B → TargetNum → M.⟦ A ⟧ → Res M.⟦ B ⟧
semM ans si = semM-of ans (name si) (sem si)

effect : ∀ {A B} → SigOpInfo A B → EffectShape B
effect si = effect-of (sem si)

-- plan 0.105: WHOSE IMPLEMENTATION A SigOp IS — read off the constructor, the
-- same split `EmittedWF.sigop-owed` makes. An INTERNAL SigOp is the compiler's:
-- a proven value function whose body the compiler emits (an arith block). An
-- EXTERNAL one is an interpretation's contract: the binary calls a symbol it
-- does not define. The machine dispatches on THIS, never on the effect shape —
-- a pure FFI contract is `Pure` and still external.
data Internal {A B : Type} : SigOpSem A B → Set where
  int-pure : ∀ {f} → Internal (pureV f)
  int-prim : ∀ {p} → Internal (primV p)

data External {A B : Type} : SigOpSem A B → Set where
  ext-ffi   : External ffiV
  ext-calls : External callsV
  ext-emits : ∀ {e} → External (emitsV e)
  ext-halts : ∀ {e} → External (haltsV e)

sigop-owner : ∀ {A B} (s : SigOpSem A B) → Internal s ⊎ External s
sigop-owner (pureV _)  = inj₁ int-pure
sigop-owner (primV _)  = inj₁ int-prim
sigop-owner ffiV       = inj₂ ext-ffi
sigop-owner callsV     = inj₂ ext-calls
sigop-owner (emitsV _) = inj₂ ext-emits
sigop-owner (haltsV _) = inj₂ ext-halts

-- An internal SigOp is pure: it neither logs nor halts.
internal-pure : ∀ {A B} {s : SigOpSem A B} → Internal s → effect-of s ≡ Pure
internal-pure int-pure = refl
internal-pure int-prim = refl

-- D250: an INTERNAL contract's graded value — what the Spec means by the
-- compiler's own pure SigOps (arithmetic, literals). A pure FFI contract's
-- value is the program's interpretation's, read from its environment
-- (D257 (A)), never computed here.
semP : ∀ {A B} (si : SigOpInfo A B) → Internal (sem si) → TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧ᵍ
semP {A} {B} si = semP-of (sem si)
  where
    semP-of : (s : SigOpSem A B) → Internal s → TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧ᵍ
    semP-of (pureV f) int-pure = f
    semP-of (primV p) int-prim = primSem p

-- | WHICH CONTRACT SHAPES END THE PROGRAM. 0.97 called this `stops-D-of` and
--   kept it in the denotation; it belongs beside the contract it reads.
stops-shape : ∀ {B} → EffectShape B → Bool
stops-shape Pure      = false
stops-shape (Emits _) = false
stops-shape (Halts _) = true
stops-shape Answers   = false


------------------------------------------------------------------------
-- Compatibility constructor — maps the old `(value, effect)` pair into
-- `SigOpSem`, DROPPING the value for effect contracts (`Emits`/`Halts`):
-- an effectful op's value is `tt` by coherence, so the supplied
-- function is discarded — this is exactly what makes the syscall
-- laundering unrepresentable. `Pure` keeps its value as `pureV`.
------------------------------------------------------------------------

mk-info : ∀ {A B} → CanonicalName → (TargetNum → M.⟦ A ⟧ → M.⟦ B ⟧ᵍ) → EffectShape B
        → IsBaseType A → IsBaseType B → SigOpInfo A B
mk-info nm f Pure      bA cB = mk-info' nm (pureV f)     bA cB
mk-info nm f (Emits e) bA cB = mk-info' nm (emitsV e)    bA cB
mk-info nm f (Halts e) bA cB = mk-info' nm (haltsV e)    bA cB
mk-info nm f Answers   bA cB = mk-info' nm callsV        bA cB

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
