-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.Arch — the single, shared target-architecture enum.
--
-- The architecture of the COMPILED BINARY (not the host the compiler runs
-- on). Owned by neither the codegen (`Once.Compile`) nor the verified CPU
-- interface (`Once.Adequacy.CPU.Interface`) — both import it, so there is
-- ONE `Arch` type across the pipeline and no relabelling map between a
-- "codegen Arch" and a "verified Arch".
------------------------------------------------------------------------

module Once.Target.Arch where

-- Supported architectures.
data Arch : Set where
  x86-64  : Arch
  x86-32  : Arch
  riscv64 : Arch

------------------------------------------------------------------------
-- The target's FLOAT FORMAT (plan 0.73, D113/D114).
--
-- A `Float`'s denotation is the TARGET'S representation, so a program's
-- machine-level meaning is target-relative at `Float` — `1.5` is `0x3FC00000`
-- at 32 bits and `0x3FF8000000000000` at 64. This is the function that carries
-- the arch into the meaning, and it lives here because "which format does this
-- target use" is a fact about the TARGET, owned by neither the codegen nor the
-- denotation.
--
-- It must AGREE with `FrameSemantics.float-format` of the arch's frame
-- semantics, and that agreement is not left to inspection: each arch's
-- correspondence carries `fmt-eq : float-format FS ≡ binaryNN`, discharged by
-- `refl`, so a disagreement is a type error rather than a wrong binary.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Integer using (ℤ)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Float.Dyadic using (FloatFormat; binary32; binary64)
import Once.Word as OnceWord

------------------------------------------------------------------------
-- THE TARGET'S NUMERIC FACTS, in one record (plan 0.74, D115).
--
-- `Float` needed the format (D113) and `Int` needs the width for exactly the
-- same reason: `⟦ Int ⟧` is the RESIDUE, so `-5` denotes `2^w - 5` and is
-- width-relative just as a float literal is format-relative. One record
-- rather than two parallel `Arch → _` maps, so a target's numeric facts
-- cannot drift apart.
------------------------------------------------------------------------

record TargetNum : Set where
  constructor mkTargetNum
  field
    -- | The machine word in BITS. `Int` is a signed two's-complement word of
    -- this width (D054), so it also fixes the literal range: an `Int` holds
    -- `-2^(int-bits-1) … 2^(int-bits-1)-1`, and a literal outside it is a
    -- TYPE ERROR (D115).
    int-bits     : ℕ
    float-format : FloatFormat

    -- | The SIGN BIT of this target's canonical quiet NaN (plan 0.75 F4).
    --
    -- A target fact, and the targets disagree: x86's SSE default QNaN is
    -- `0xfff8000000000000` — sign bit SET — while RISC-V's canonical NaN is
    -- `0x7ff8000000000000` with sign 0. Verified against the hardware:
    -- `inf + (-inf)` on x86-64 gives `0xfff8000000000000`.
    --
    -- It rides HERE, beside the format, for D109/D112's reason: a numeric fact
    -- baked where all targets must be served is the mistake those two
    -- decisions exist to forbid. Only invalid operations can observe it
    -- (`∞ + (−∞)`, `0 × ∞`), which is why it is one bit rather than a pattern.
    nan-sign     : ℕ

    -- | THE TARGET HAS AT LEAST ONE BIT (plan 0.74 J6, D115).
    --
    -- Only the arch can supply this, and it is not ceremony: the exactness
    -- theorem below is FALSE at `int-bits ≡ 0`. There `half ≡ modulus ≡ 1`,
    -- `InRange` admits `-1`, and `fromℤ (-1)` is `0` — a literal that is
    -- accepted and then silently means something else, which is the whole
    -- failure mode D115 exists to forbid. A zero-bit target is not a target,
    -- and this field is where that gets said.
    int-bits-pos : 0 < int-bits

open TargetNum public

------------------------------------------------------------------------
-- THE INT CONTRACT (plan 0.74 J6, D115)
--
-- The gate was DECORATIVE until this existed. `AdmissibleM` decided that a
-- literal fits, carried the witness as far as the compile driver, and dropped
-- it; the machine then called the TOTAL `fromℤ`, which wraps. Nothing tied the
-- decision to what got materialised, so accepting `2147483648` at 32 bits and
-- silently meaning `-2147483648` was not ruled out by any proof.
--
-- So the evidence has to be CONSUMED, not carried. `tn-lower` takes the
-- `InRange` witness as an ARGUMENT — there is no way to lower a literal
-- without one — and `tn-exact` is what that argument buys: read the word back
-- as a signed integer and you get the integer the programmer wrote.
--
-- WHY IT IS THE ARCH'S. The width is the arch's, so the range is the arch's,
-- so the promise "I materialise the literals I accept, exactly" is the arch's
-- to make. A target that lowers literals some other way owes `tn-exact` about
-- ITS lowering, not a promise to call `fromℤ`.
--
-- The FLOAT half of the contract is D116's and is deliberately NOT here yet:
-- a float literal always lowers, ROUNDING when the target cannot hold it
-- exactly, so its obligation is totality plus an ERROR BOUND rather than a
-- domain restriction. That bound is what plan 0.74's K-series builds; adding
-- half of it now would be worse than adding none.
------------------------------------------------------------------------

-- | `int-bits ≡ suc b`, the shape `Once.Word`'s width-positive lemmas want.
pos⇒suc : ∀ {n : ℕ} → 0 < n → Σ ℕ (λ b → n ≡ suc b)
pos⇒suc {suc b} _ = b , refl

-- | The target's word for a literal it ACCEPTS. Total under the evidence, so
-- `fromℤ`'s wrap is unreachable as semantics rather than merely unlikely.
tn-lower : (tn : TargetNum) (z : ℤ)
         → OnceWord.Width.InRange (int-bits tn) z
         → OnceWord.Width.Word (int-bits tn)
tn-lower tn z p = OnceWord.Width.toWord (int-bits tn) z p

-- | …and it means what it says.
tn-exact : (tn : TargetNum) (z : ℤ) (p : OnceWord.Width.InRange (int-bits tn) z)
         → OnceWord.Width.toℤ (int-bits tn) (tn-lower tn z p) ≡ z
tn-exact tn z p with pos⇒suc (int-bits-pos tn)
... | (b , eqb) = OnceWord.Width.toℤ∘fromℤ (int-bits tn) b eqb z p

arch-numerics : Arch → TargetNum
arch-numerics x86-64  = mkTargetNum 64 binary64 1 (s≤s z≤n)
arch-numerics x86-32  = mkTargetNum 32 binary32 1 (s≤s z≤n)
arch-numerics riscv64 = mkTargetNum 64 binary64 0 (s≤s z≤n)

-- | Derived, so existing callers are unchanged.
arch-int-bits : Arch → ℕ
arch-int-bits a = int-bits (arch-numerics a)

arch-float-format : Arch → FloatFormat
arch-float-format a = float-format (arch-numerics a)

-- | The target's name, for diagnostics. Here rather than in the compiler
-- because it is a fact about the target, and because an error that says which
-- target refused a literal is the whole point of refusing per target.
open import Data.String using (String)

archName : Arch → String
archName x86-64  = "x86-64"
archName x86-32  = "x86-32"
archName riscv64 = "riscv64"
