-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Float.Arith — WHAT `x + y` MEANS FOR FLOATS (plan 0.75 F4).
--
-- D054 fixed the shape of this module before it existed. `Int` means "whatever
-- the target CPU's `add` computes", and its `⊕` is a DEFINITION —
-- `norm tn (x + y)` — in which ℤ appears "only as scaffolding inside the
-- definition of the modular op, never as a promise to the programmer". D113
-- extends that to the second numeric type in as many words:
--
--     IEEE `fadd` ROUNDS. Exact dyadic `+` does not. They are different
--     functions.
--
-- …and demotes `Dyadic` "to the role ℤ has for `Int`": the literal payload and
-- the parked exact spec. THAT ROLE IS THIS MODULE. `fadd` is defined the way
-- `⊕` is — do the operation exactly in the scaffolding domain, then apply the
-- target's normalisation — and rounding is what `norm` is for floats.
--
-- SO THERE IS NO NEW TRUST POINT. `+`, `−` and `×` are closed on binary
-- rationals: the exact result of each is representable, so rounding ONCE at
-- the end IS correct rounding, which is exactly what IEEE-754 requires of
-- them. Postulating `fadd` would have made the OPERATION a trust point where
-- `Int`'s is a definition, and would be the straddle D113 rejects.
--
-- ROUND EACH OPERAND FIRST, THEN OPERATE — never "operate exactly, then
-- round". The two are different functions and the difference is observable at
-- the first example anybody tries:
--
--     0.1 + 0.2   hardware  0x3fd3333333333334
--                 exact-then-round  0x3fd3333333333333
--
-- Nothing here can get that wrong, because these operations take BIT PATTERNS
-- (`⟦ Float ⟧` is the target's representation, D113) and the literals were
-- already rounded once at the backend (D116/D117). It is written down because
-- it is the thing a reader will wonder about.
--
-- WHY NOT `Dyadic`. `Dyadic.shift` is a `ℕ`, so it cannot express the exponent
-- of a large value — D117 hit this and says so: `roundSig` returns its
-- exponent as a `ℤ` "and that signed exponent is what `Dyadic` structurally
-- cannot express". Arithmetic needs both directions at once (`2^80 + 2^-80`),
-- so the scaffolding here carries a ℤ exponent. `Dyadic` keeps its own job,
-- which is to be the encoder's input shape.
--
-- DIVISION IS NOT HERE, and that is a scope decision rather than an oversight.
-- A quotient is not a binary rational, so a single rounding at the end is NOT
-- correct rounding for it — getting it right needs a sticky bit through the
-- division, and getting it wrong means silently differing from the hardware,
-- which is D114's failure mode exactly. `Int`'s own `div-semM` is still a
-- postulate, so float division would be WORSE than its integer twin rather
-- than equal to it. `1.5 / 2.0` stays a type error until it is done properly.
------------------------------------------------------------------------

module Once.Float.Arith where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; NonZero)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
import Data.Integer as ℤ
import Data.Integer.Properties as ℤ
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import Once.Float.Dyadic
  using (FloatFormat; sig-bits; exp-bits; bias; bitLen; signBit; modPow;
         binary32; binary64)
open import Once.Float.Decimal using (divRHE; packAt; infinity; signedZero)

------------------------------------------------------------------------
-- THE SCAFFOLDING: an exact binary rational, `sigB · 2 ^ expB`
--
-- Both fields signed. The significand because the value is, the exponent
-- because arithmetic reaches both ends of the range — which is precisely what
-- `Dyadic`'s `ℕ` shift cannot do (D117).
------------------------------------------------------------------------

record Bin : Set where
  constructor _·2^_
  field
    sigB : ℤ
    expB : ℤ

open Bin public

-- | Align to the SMALLER exponent and add. Exact: both shifts are
-- multiplications by a power of two, never a division, so nothing is lost.
-- Split out rather than written with a `let` so it reduces for abstract
-- arguments — the same reason `round` projects instead of destructuring.
addAt : ℤ → ℤ → ℤ → ℤ → ℤ → Bin
addAt a p b q m =
  ((a ℤ.* (+ (2 ^ ∣ p ℤ.- m ∣))) ℤ.+ (b ℤ.* (+ (2 ^ ∣ q ℤ.- m ∣)))) ·2^ m

_+B_ : Bin → Bin → Bin
x +B y = addAt (sigB x) (expB x) (sigB y) (expB y) (expB x ℤ.⊓ expB y)

-- | Exact, and trivially so: exponents add, significands multiply.
_*B_ : Bin → Bin → Bin
x *B y = (sigB x ℤ.* sigB y) ·2^ (expB x ℤ.+ expB y)

negB : Bin → Bin
negB x = (ℤ.- sigB x) ·2^ expB x

isZeroB : Bin → Bool
isZeroB x = ∣ sigB x ∣ ℕ.≡ᵇ 0

signB : Bin → ℕ
signB x = signBit (sigB x)

------------------------------------------------------------------------
-- THE VALUE OF A BIT PATTERN
--
-- Not every pattern is a number, so `decode` lands in a three-way view rather
-- than in `Bin`. ±∞ is REACHABLE — D118 made overflow produce it, so `1e41` at
-- binary32 IS an infinity — and once infinities exist `∞ + (−∞)` exists, so
-- NaN has to be here too. Enumerated rather than defaulted: a "not a number"
-- that silently decoded as some number is the D114 shape.
------------------------------------------------------------------------

data FloatVal : Set where
  fv-fin : Bin → FloatVal
  fv-inf : ℕ → FloatVal      -- the sign bit
  fv-nan : FloatVal

-- | ± the magnitude, by the sign bit.
applySign : ℕ → ℕ → ℤ
applySign sb m = if sb ℕ.≡ᵇ 0 then + m else ℤ.- (+ m)

-- | The exponent a stored exponent `se` denotes, for a significand read as an
-- INTEGER (leading bit included, fraction not shifted down): `se − bias − p`.
normExp : FloatFormat → ℕ → ℤ
normExp F se = (+ se) ℤ.- (+ (bias F + sig-bits F))

-- | …and the subnormal exponent, which is the `se ≡ 1` exponent, not `se ≡ 0`.
subExp : FloatFormat → ℤ
subExp F = (+ 1) ℤ.- (+ (bias F + sig-bits F))

-- | THE canonical quiet NaN: exponent all ones, quiet bit set, sign CLEAR and
-- payload zero. One value, at every target — and that is D055's rule, not a
-- convenience.
--
-- THE TARGETS GENUINELY DISAGREE, and by more than a sign bit. Measured:
--
--                     ∞ + (−∞)              0xfff8000000000456 + 1
--     x86-64     0xfff8000000000000      0xfff8000000000456   (payload kept)
--     riscv64    0x7ff8000000000000      0x7ff8000000000000   (canonicalised)
--
-- x86 sets the sign on an invalid operation AND propagates an operand's NaN
-- payload; RISC-V produces one canonical NaN for every NaN-producing case and
-- never propagates. So this is exactly D055's situation — "the one arithmetic
-- op where the target silicon disagrees" — and D055 already decided what to do
-- about it:
--
--     Once's `/` and `%` are total functions over `Word`, following RISC-V's
--     defined results. … One uniform semantics across every target, instead of
--     "traps on x86, returns a value on RISC-V". The meaning of `a / 0` does
--     not depend on which backend you compiled with.
--
-- PARAMETERISING THE SIGN WAS THE WRONG FIX, and it is the one this module
-- shipped with first. It made the MEANING of `∞ + (−∞)` depend on the backend,
-- which is precisely what D055 forbids — and it captured only a fraction of
-- the divergence, so it would not even have been sound.
--
-- BACKEND OBLIGATION, in D055's own shape. RISC-V is native: emit the bare
-- instruction, the hardware already produces this value. x86 must CANONICALISE
-- — replace a NaN result with this pattern — and the check is elidable
-- wherever the compiler can prove the result is not a NaN, exactly as the
-- div-by-zero guard is elidable where the divisor is provably nonzero. Cost
-- lands only where the hardware forces it; everyone gets the same answer.
--
-- It is OBSERVABLE, so this is not academic: `emitF` writes the whole machine
-- word, so a program can print the difference.
nan : FloatFormat → ℕ
nan F = ((2 ^ exp-bits F) ∸ 1) * (2 ^ sig-bits F) + 2 ^ (sig-bits F ∸ 1)

-- Each decision is a separate aux taking its scrutinee as an ARGUMENT, the
-- `packHi`/`packSE` convention: a proof that cases on the decision reduces.
decodeMax : FloatFormat → ℕ → ℕ → FloatVal
decodeMax F sb frac = if frac ℕ.≡ᵇ 0 then fv-inf sb else fv-nan

-- | `se ≡ 0` is zero or a SUBNORMAL. Once never PRODUCES a subnormal (D118 —
-- underflow gives zero), but it can be handed one by an external op, and
-- decoding it as zero would be a silent value substitution. Reading it
-- correctly costs one clause, so it is read correctly. The asymmetry is real
-- and deliberate: we decode more than we encode.
decodeAt : FloatFormat → ℕ → ℕ → ℕ → Bool → Bool → FloatVal
decodeAt F sb se frac true  _     = fv-fin (applySign sb frac ·2^ subExp F)
decodeAt F sb se frac false true  = decodeMax F sb frac
decodeAt F sb se frac false false =
  fv-fin (applySign sb (2 ^ sig-bits F + frac) ·2^ normExp F se)

decode : FloatFormat → ℕ → FloatVal
decode F w =
  decodeAt F
    (_/_ w (2 ^ (exp-bits F + sig-bits F)) {{m^n≢0 2 (exp-bits F + sig-bits F)}})
    (_/_ (modPow w (exp-bits F + sig-bits F)) (2 ^ sig-bits F) {{m^n≢0 2 (sig-bits F)}})
    (modPow w (sig-bits F))
    (_/_ (modPow w (exp-bits F + sig-bits F)) (2 ^ sig-bits F) {{m^n≢0 2 (sig-bits F)}} ℕ.≡ᵇ 0)
    (_/_ (modPow w (exp-bits F + sig-bits F)) (2 ^ sig-bits F) {{m^n≢0 2 (sig-bits F)}}
       ℕ.≡ᵇ ((2 ^ exp-bits F) ∸ 1))

------------------------------------------------------------------------
-- THE ONE ROUNDING, for a binary scaffolding value
--
-- The decimal twin (`Once.Float.Decimal.roundSig`) has to scale by powers of
-- ten to find a binary exponent at all. Here there is nothing to convert: the
-- value is ALREADY binary, so rounding is a right shift by however many bits
-- exceed the format's `P = sig-bits + 1`, with `divRHE`'s round-half-even
-- deciding the dropped bits. Zero bits to drop is the common case and is
-- exactly the identity.
--
-- `packAt` then does the rest, and it is the SAME `packAt` a literal goes
-- through — so overflow gives ±∞ and underflow gives zero for arithmetic
-- results by the same code that gives them for literals (D118), rather than by
-- a second story that could drift.
------------------------------------------------------------------------

roundMagAt : ℕ → ℕ → ℕ × ℕ
roundMagAt n zero    = n , 0
roundMagAt n (suc k) = divRHE n (2 ^ suc k) {{m^n≢0 2 (suc k)}} , suc k

roundMag : FloatFormat → ℕ → ℕ × ℕ
roundMag F n = roundMagAt n (bitLen n ∸ suc (sig-bits F))

-- Projected rather than destructured, for the reason `round` gives: a
-- `where (m , k) = …` would stop this reducing for an abstract argument.
roundB : FloatFormat → Bin → ℕ
roundB F b =
  packAt F (signBit (sigB b))
           (proj₁ (roundMag F ∣ sigB b ∣))
           (expB b ℤ.+ (+ proj₂ (roundMag F ∣ sigB b ∣)))

------------------------------------------------------------------------
-- THE OPERATIONS
--
-- The special-case tables are IEEE-754's and are ENUMERATED — nine cases each,
-- no catch-all. A catch-all here would route `∞ + (−∞)` to whatever the finite
-- branch computes, which is the shape of defect this codebase keeps finding.
------------------------------------------------------------------------

-- | Sign of a product: XOR of the operand signs.
xorS : ℕ → ℕ → ℕ
xorS s t = if s ℕ.≡ᵇ t then 0 else 1

negV : FloatVal → FloatVal
negV (fv-fin x) = fv-fin (negB x)
negV (fv-inf s) = fv-inf (xorS s 1)
negV fv-nan     = fv-nan

addV : FloatFormat → FloatVal → FloatVal → ℕ
addV F fv-nan     _          = nan F
addV F (fv-inf _) fv-nan     = nan F
addV F (fv-fin _) fv-nan     = nan F
-- The one invalid case for addition: ∞ + (−∞).
addV F (fv-inf s) (fv-inf t) = if s ℕ.≡ᵇ t then infinity F s else nan F
addV F (fv-inf s) (fv-fin _) = infinity F s
addV F (fv-fin _) (fv-inf t) = infinity F t
addV F (fv-fin x) (fv-fin y) = roundB F (x +B y)

mulV : FloatFormat → FloatVal → FloatVal → ℕ
mulV F fv-nan     _          = nan F
mulV F (fv-inf _) fv-nan     = nan F
mulV F (fv-fin _) fv-nan     = nan F
mulV F (fv-inf s) (fv-inf t) = infinity F (xorS s t)
-- …and the invalid case for multiplication: 0 × ∞.
mulV F (fv-inf s) (fv-fin y) =
  if isZeroB y then nan F else infinity F (xorS s (signB y))
mulV F (fv-fin x) (fv-inf t) =
  if isZeroB x then nan F else infinity F (xorS (signB x) t)
mulV F (fv-fin x) (fv-fin y) = roundB F (x *B y)

------------------------------------------------------------------------
-- DIVISION — the one operation whose exact result is not a `Bin`
--
-- `x +B y` and `x *B y` are exact: dyadics are closed under both, so `roundB`
-- receives the true value and rounds it once. A QUOTIENT of two dyadics is in
-- general not a dyadic (`1/3`), so there is nothing exact to hand `roundB`.
--
-- The standard remedy, and the only subtle part of this module: compute enough
-- quotient bits that the rounding position is strictly above the last one, and
-- fold the fact that the division was inexact into that last bit — the STICKY
-- BIT. `roundB`'s half-even then gives the correctly-rounded quotient, because
-- the only case it can get wrong is an exact tie, and a non-zero remainder is
-- exactly the evidence that the tie is not exact.
--
-- WHY THE LSB IS A SAFE PLACE TO PUT IT. `roundB` targets `sig-bits F + 1`
-- significant bits. `g` below is chosen so the quotient has at least one more
-- bit than that, so its LSB lies strictly BELOW the rounding position. Setting
-- it can therefore never move the value across a rounding boundary; it can
-- only turn "discarded bits are exactly one half" into "strictly more than one
-- half", which is precisely the tie-break IEEE asks for.

-- | Set the low bit — the sticky fold. `2 * (q / 2)` clears it, `+ 1` sets it.
setLow : ℕ → ℕ
setLow q = 2 * (q / 2) + 1

stickyAt : ℕ → ℕ → ℕ
stickyAt q r = if r ℕ.≡ᵇ 0 then q else setLow q

-- | The guard shift, and the `+ 3` is load-bearing.
--
-- `roundB` targets `T = sig-bits F + 1` bits, and `bitLen q ≥ bitLen n ∸ bitLen
-- my`, so `g = (T + 2 + bitLen my) ∸ bitLen mx` guarantees `bitLen q ≥ T + 2`:
-- at least TWO discarded bits.
--
-- Two, not one. With a single discarded bit that bit IS the round bit, and
-- folding the sticky into it corrupts the very decision it is meant to inform —
-- `1.0 / 3.0` then answers one ulp high (`…556` for `…555`), which is the first
-- pin below and how this was caught.
guardShift : FloatFormat → ℕ → ℕ → ℕ
guardShift F mx my = (sig-bits F + 3 + bitLen my) ∸ bitLen mx

-- | Quotient of `n` by a divisor given as `suc d`. The divisor arrives ALREADY
-- KNOWN NON-ZERO, as a `suc` pattern rather than as a `NonZero` instance,
-- because the zero divisor is not an edge case to be defaulted — it is a
-- different IEEE result (a signed infinity), enumerated in `divV`.
stickyQuot : ℕ → ℕ → ℕ
stickyQuot n d = stickyAt (n / suc d) (n % suc d)

-- | The quotient of two finite dyadics whose divisor magnitude is `suc d`,
-- carrying its own stickiness. Exact when the division is exact.
--
-- `guardShift` is called twice rather than bound in a `where`, the same
-- convention `roundB` follows: a `where`-bound tuple stops the whole thing
-- reducing for an abstract argument.
divBin : FloatFormat → Bin → ℕ → ℤ → ℕ → Bin
divBin F x sy eY d =
  applySign (xorS (signB x) sy)
            (stickyQuot (∣ sigB x ∣ * 2 ^ guardShift F ∣ sigB x ∣ (suc d)) d)
    ·2^ (expB x ℤ.- eY ℤ.- (+ guardShift F ∣ sigB x ∣ (suc d)))

-- | IEEE's division table, enumerated like the other two. Two invalid cases
-- (`∞/∞`, `0/0`) and one that is NOT invalid and must not be confused with
-- them: a finite non-zero over zero is a signed infinity, which is `divideByZero`,
-- not `invalid`. D055 already decided Once has no traps, so both simply return
-- their value.
divV : FloatFormat → FloatVal → FloatVal → ℕ
divV F fv-nan     _          = nan F
divV F (fv-inf _) fv-nan     = nan F
divV F (fv-fin _) fv-nan     = nan F
divV F (fv-inf s) (fv-inf t) = nan F
divV F (fv-inf s) (fv-fin y) = infinity F (xorS s (signB y))
divV F (fv-fin x) (fv-inf t) = signedZero F (xorS (signB x) t)
-- The finite/finite table, split on the two MAGNITUDES so the non-zero divisor
-- reaches `divBin` as a `suc` and nothing has to invent a value for zero.
divV F (fv-fin x) (fv-fin y) with ∣ sigB x ∣ | ∣ sigB y ∣
... | zero  | zero  = nan F                                          -- 0/0 invalid
... | suc _ | zero  = infinity F (xorS (signB x) (signB y))          -- x/0
... | zero  | suc d = signedZero F (xorS (signB x) (signB y))        -- 0/y
... | suc _ | suc d = roundB F (divBin F x (signB y) (expB y) d)

-- | The four operations, on BIT PATTERNS at a format. No target parameter
-- beyond the format: the answer is the same on every target BY DECISION
-- (D055), and the backends conform to it rather than the other way round.
fadd fsub fmul fdiv : FloatFormat → ℕ → ℕ → ℕ
fadd F a b = addV F (decode F a) (decode F b)
fsub F a b = addV F (decode F a) (negV (decode F b))
fmul F a b = mulV F (decode F a) (decode F b)
fdiv F a b = divV F (decode F a) (decode F b)

-- | Negation is a SIGN-BIT FLIP, not a decode/round round-trip. IEEE says so —
-- negation is exact and defined on every pattern including NaN — and a
-- round-trip would collapse `−0` to `+0` and canonicalise a NaN, neither of
-- which negation is allowed to do.
fnegAt : FloatFormat → ℕ → Bool → ℕ
fnegAt F w true  = w ∸ 2 ^ (exp-bits F + sig-bits F)
fnegAt F w false = w + 2 ^ (exp-bits F + sig-bits F)

fneg : FloatFormat → ℕ → ℕ
fneg F w = fnegAt F w (2 ^ (exp-bits F + sig-bits F) ℕ.≤ᵇ w)

-- | `Int` → `Float`, CORRECTLY ROUNDED (plan 0.75 F4, D125).
--
-- One line, and that is the argument. An integer `z` IS the exact binary value
-- `z · 2^0`, so the conversion is the SAME `roundB` every arithmetic result
-- goes through — not a second rounding story that could drift from the first.
-- IEEE-754 lists `convertFromInt` as a correctly-rounded operation beside `+`,
-- and this is that sentence in code.
--
-- Integers with `|z| ≤ 2 ^ (sig-bits F + 1)` convert EXACTLY (`bitLen` is then
-- within the format's `P`, so `roundMag` drops nothing). That threshold is
-- what D123's channel warns above, and only for LITERALS — a runtime value's
-- error is bounded by half an ulp like every other rounding, which is why
-- there is no per-site diagnostic.
i2f : FloatFormat → ℤ → ℕ
i2f F z = roundB F (z ·2^ (+ 0))

------------------------------------------------------------------------
-- PINNED, and against the RIGHT authority
--
-- `round`'s pins say "glibc", and for a LITERAL that is exact: turning `3.14`
-- into a bit pattern is decimal→binary conversion, which is `strtod`, which is
-- glibc. ARITHMETIC IS NOT. `a + b` on doubles compiles to the CPU's own IEEE
-- instruction (`addsd`), so the authority for these patterns is the HARDWARE,
-- reached through a compiled C program — which is the same authority D113 says
-- Once's `Float` is promising to match ("in the end it is the hardware that
-- promises what it calculates").
--
-- Generated by gcc 14.3.0 / glibc 2.40 on x86-64: operands printed by
-- `memcpy`ing the double, results likewise, so nothing is routed through a
-- decimal round-trip on the way out.
--
-- These pins are the whole check on this module, for D117's reason: the
-- meaning and the codegen will both call THESE functions, so their
-- correspondence is `refl`-shaped and holds whatever they compute.
------------------------------------------------------------------------

-- `0.1 + 0.2`. THE case, and the one that separates this definition from the
-- wrong one: adding the two exact DECIMALS and rounding once gives
-- `0x3fd3333333333333`, one ulp below. Each operand is rounded first, then
-- added — which is what the machine does and what D113 requires.
_ : fadd binary64 0x3fb999999999999a 0x3fc999999999999a ≡ 0x3fd3333333333334
_ = refl

-- …and `0.1 + 0.7`, where exact-then-round errs the other way
-- (`0x3fe999999999999a`), so the pin is not accidentally one-sided.
_ : fadd binary64 0x3fb999999999999a 0x3fe6666666666666 ≡ 0x3fe9999999999999
_ = refl

-- Exact cases: nothing to round, so these check the ALIGNMENT and the field
-- packing rather than the rounding.
_ : fadd binary64 0x3ff8000000000000 0x4004000000000000 ≡ 0x4010000000000000
_ = refl

_ : fsub binary64 0x4010000000000000 0x3ff8000000000000 ≡ 0x4004000000000000
_ = refl

_ : fmul binary64 0x3ff8000000000000 0x4004000000000000 ≡ 0x400e000000000000
_ = refl

-- `3.14 * 2.0` — an inexact operand times an exact one, so the product is
-- exactly representable and the answer must be the operand's fraction with the
-- exponent bumped. A rounding bug that happened to be a no-op on ties would
-- survive the cases above and die here.
_ : fmul binary64 0x40091eb851eb851f 0x4000000000000000 ≡ 0x40191eb851eb851f
_ = refl

-- Cancellation to zero. The sign is `+0` — Once collapses the two zeros
-- (`Once.Float.Dyadic`'s carrier note, D124), and IEEE agrees here anyway.
_ : fadd binary64 0x3ff0000000000000 0xbff0000000000000 ≡ 0
_ = refl

-- OVERFLOW from arithmetic reaches ±∞ through the SAME `packAt` a literal
-- does, which is what D118 buys: one story, not two.
_ : fmul binary64 0x7e37e43c8800759c 0x7e37e43c8800759c ≡ 0x7ff0000000000000
_ = refl

-- The special-case table, against the machine's own answers.
_ : fadd binary64 0x7ff0000000000000 0x3ff0000000000000 ≡ 0x7ff0000000000000
_ = refl

-- ∞ + (−∞) and 0 × ∞ are INVALID, and Once answers with THE canonical NaN on
-- every target (D055). These two pins are therefore the RISC-V patterns and
-- deliberately NOT x86's — x86 answers `0xfff8000000000000` in hardware and
-- the backend must canonicalise. That divergence is the whole point of the
-- decision, so the pin records the DECIDED value, not the measured one.
_ : fadd binary64 0x7ff0000000000000 0xfff0000000000000 ≡ 0x7ff8000000000000
_ = refl

_ : fmul binary64 0 0x7ff0000000000000 ≡ 0x7ff8000000000000
_ = refl

------------------------------------------------------------------------
-- DIVISION, against the machine
--
-- These are the pins the sticky bit exists for. `1.0 / 3.0` and `7.0 / 11.0`
-- are non-terminating in binary, so their quotients are inexact by
-- construction and every discarded bit has to be accounted for.
--
-- ⭐ `0.1 / 0.3` is the sharp one. It answers `…556`, ONE ULP ABOVE
-- `1.0 / 3.0`'s `…555`, even though both are `0.333…` — the operands are
-- themselves rounded, so the true quotient falls the other side of the
-- boundary. A division that truncated, or that rounded without the remainder,
-- gets `…555` here and passes every other pin in this block.

_ : fdiv binary64 0x3ff0000000000000 0x4008000000000000 ≡ 0x3fd5555555555555
_ = refl

_ : fdiv binary64 0x401c000000000000 0x4026000000000000 ≡ 0x3fe45d1745d1745d
_ = refl

_ : fdiv binary64 0x3fb999999999999a 0x3fd3333333333333 ≡ 0x3fd5555555555556
_ = refl

-- Exact quotients: the remainder is zero, so the sticky fold must be a no-op.
_ : fdiv binary64 0x3ff0000000000000 0x4000000000000000 ≡ 0x3fe0000000000000
_ = refl

_ : fdiv binary64 0x4018000000000000 0x4008000000000000 ≡ 0x4000000000000000
_ = refl

-- An inexact operand over an exact one: the answer is the operand's fraction
-- with the exponent decremented, so a bug in the guard shift shows up here.
_ : fdiv binary64 0x40091eb851eb851f 0x4000000000000000 ≡ 0x3ff91eb851eb851f
_ = refl

-- Signs are the XOR, on both sides.
_ : fdiv binary64 0xc01c000000000000 0x4000000000000000 ≡ 0xc00c000000000000
_ = refl

_ : fdiv binary64 0x3ff0000000000000 0xc010000000000000 ≡ 0xbfd0000000000000
_ = refl

-- The division table. `x/0` is a signed INFINITY and `0/0` is invalid; they are
-- different answers and the enumeration keeps them apart. As with `fadd`'s
-- invalid case these are the DECIDED (RISC-V) NaN, not x86's.
_ : fdiv binary64 0x3ff0000000000000 0 ≡ 0x7ff0000000000000
_ = refl

_ : fdiv binary64 0xbff0000000000000 0 ≡ 0xfff0000000000000
_ = refl

_ : fdiv binary64 0 0 ≡ 0x7ff8000000000000
_ = refl

_ : fdiv binary64 0x7ff0000000000000 0x7ff0000000000000 ≡ 0x7ff8000000000000
_ = refl

_ : fdiv binary64 0x3ff0000000000000 0x7ff0000000000000 ≡ 0
_ = refl

_ : fdiv binary64 0x7ff0000000000000 0x4000000000000000 ≡ 0x7ff0000000000000
_ = refl

-- Negation is a bit flip and is exact on every pattern.
_ : fneg binary64 0x3ff8000000000000 ≡ 0xbff8000000000000
_ = refl

_ : fneg binary64 0xbff8000000000000 ≡ 0x3ff8000000000000
_ = refl

------------------------------------------------------------------------
-- The SAME operations at binary32, because the format is a parameter and this
-- is where that gets checked rather than asserted.
------------------------------------------------------------------------

_ : fadd binary32 0x3fc00000 0x40200000 ≡ 0x40800000
_ = refl

-- Division at binary32: the same function, a different precision, and the
-- quotient lands on a different bit — which is what makes the format a
-- parameter rather than a constant.
_ : fdiv binary32 0x3f800000 0x40400000 ≡ 0x3eaaaaab
_ = refl

_ : fdiv binary32 0x40e00000 0x41300000 ≡ 0x3f22e8ba
_ = refl

_ : fadd binary32 0x3dcccccd 0x3e4ccccd ≡ 0x3e99999a
_ = refl

-- `16777216 + 1` at binary32 is an exact TIE, and round-half-to-even keeps the
-- even one — so the answer is `16777216`, not `16777218`. The literal
-- `16777217` is the value K3's own pins use, one type over.
_ : fadd binary32 0x4b800000 0x3f800000 ≡ 0x4b800000
_ = refl

_ : fmul binary32 0x4048f5c3 0x40000000 ≡ 0x40c8f5c3
_ = refl

-- Overflow at the NARROWER format, from operands that are finite at binary64 —
-- the asymmetry D113 exists to make expressible.
_ : fmul binary32 0x7e967699 0x41200000 ≡ 0x7f800000
_ = refl

------------------------------------------------------------------------
-- `Int` → `Float`, pinned (D125)
--
-- Measured on BOTH targets, which is what licenses the decision: unlike
-- division-by-zero (D055) and unlike NaN, the hardware AGREES here, so there
-- is no answer to choose and no backend guard to write.
--
--     (double)(2^53 + 1)   x86-64  0x4340000000000000
--                          riscv64 0x4340000000000000
------------------------------------------------------------------------

_ : i2f binary64 (+ 1) ≡ 0x3ff0000000000000
_ = refl

_ : i2f binary64 (ℤ.- (+ 1)) ≡ 0xbff0000000000000
_ = refl

_ : i2f binary64 (+ 0) ≡ 0
_ = refl

-- The exactness threshold, from both sides. `2^53` converts exactly; `2^53+1`
-- has no binary64 representation and rounds to `2^53` — the same value, which
-- is precisely the precision loss D125 decided to allow and to bound.
_ : i2f binary64 (+ 9007199254740992) ≡ 0x4340000000000000
_ = refl

_ : i2f binary64 (+ 9007199254740993) ≡ 0x4340000000000000
_ = refl

-- …and at binary32, where the threshold is `2^24` and the SAME literal the
-- float pins already use sits on it.
_ : i2f binary32 (+ 16777216) ≡ 0x4b800000
_ = refl

_ : i2f binary32 (+ 16777217) ≡ 0x4b800000
_ = refl

-- A mixed expression end to end: `1 + 1.5` is `i2f 1` added to the literal.
_ : fadd binary64 (i2f binary64 (+ 1)) 0x3ff8000000000000 ≡ 0x4004000000000000
_ = refl

------------------------------------------------------------------------
-- COMMUTATIVITY of `fadd` and `fmul`
--
-- Needed by the backend, not by taste: `compile-go` leaves one operand in the
-- destination register, so the emitter's aliasing case computes `b ⊙ a` where
-- the tree says `a ⊙ b`. The integer path discharges that with `Once.Word`'s
-- `⊕-comm`; this is the float twin.
--
-- IT IS TRUE HERE AND WOULD NOT BE ON THE HARDWARE. x86 PROPAGATES an operand's
-- NaN payload, so `nan₁ + nan₂` and `nan₂ + nan₁` differ on the metal. Once
-- canonicalises (D055's rule, applied to NaN), and the canonical NaN has no
-- payload to propagate — so commutativity holds exactly. The decision to
-- canonicalise bought this proof.
------------------------------------------------------------------------

private
  -- `x ≡ᵇ y` is symmetric, which is the only fact the ±∞ cases need.
  ≡ᵇ-sym : ∀ m n → (m ℕ.≡ᵇ n) ≡ (n ℕ.≡ᵇ m)
  ≡ᵇ-sym zero    zero    = refl
  ≡ᵇ-sym zero    (suc _) = refl
  ≡ᵇ-sym (suc _) zero    = refl
  ≡ᵇ-sym (suc m) (suc n) = ≡ᵇ-sym m n

  ≡ᵇ⇒≡ : ∀ m n → (m ℕ.≡ᵇ n) ≡ true → m ≡ n
  ≡ᵇ⇒≡ zero    zero    _  = refl
  ≡ᵇ⇒≡ (suc m) (suc n) eq = cong suc (≡ᵇ⇒≡ m n eq)

-- Exact addition on the scaffolding commutes: the alignment exponent is a
-- `⊓` (commutative) and the significands are added in `ℤ`.
-- The implicits of `+-comm` are spelled out: after the `⊓` is turned around
-- both sides share the alignment exponent, but the two SUMMANDS are large
-- terms Agda will not guess.
+B-comm : ∀ x y → x +B y ≡ y +B x
+B-comm (a ·2^ p) (b ·2^ q) rewrite ℤ.⊓-comm p q =
  cong (_·2^ (q ℤ.⊓ p))
       (ℤ.+-comm (a ℤ.* (+ (2 ^ ∣ p ℤ.- (q ℤ.⊓ p) ∣)))
                 (b ℤ.* (+ (2 ^ ∣ q ℤ.- (q ℤ.⊓ p) ∣))))

*B-comm : ∀ x y → x *B y ≡ y *B x
*B-comm (a ·2^ p) (b ·2^ q) = cong₂ _·2^_ (ℤ.*-comm a b) (ℤ.+-comm p q)

-- The ±∞ pair is the only case with a decision in it. `≡ᵇ-sym` turns the
-- scrutinee around; the aux takes the decision as an ARGUMENT (the
-- `cfm-build-gated` convention) so the `if` reduces on both sides at once.
addV-inf-aux : ∀ F s t (b : Bool) → (t ℕ.≡ᵇ s) ≡ b
             → (if b then infinity F s else nan F)
             ≡ (if b then infinity F t else nan F)
addV-inf-aux F s t true  eq = cong (infinity F) (sym (≡ᵇ⇒≡ t s eq))
addV-inf-aux F s t false _  = refl

addV-comm : ∀ F x y → addV F x y ≡ addV F y x
addV-comm F fv-nan     fv-nan     = refl
addV-comm F fv-nan     (fv-inf _) = refl
addV-comm F fv-nan     (fv-fin _) = refl
addV-comm F (fv-inf _) fv-nan     = refl
addV-comm F (fv-fin _) fv-nan     = refl
addV-comm F (fv-inf s) (fv-fin _) = refl
addV-comm F (fv-fin _) (fv-inf t) = refl
addV-comm F (fv-fin x) (fv-fin y) = cong (roundB F) (+B-comm x y)
addV-comm F (fv-inf s) (fv-inf t) rewrite ≡ᵇ-sym s t =
  addV-inf-aux F s t (t ℕ.≡ᵇ s) refl

xorS-comm : ∀ m n → xorS m n ≡ xorS n m
xorS-comm m n rewrite ≡ᵇ-sym m n = refl

-- The `0 × ∞` decision, taken as an argument for the same reason.
mulV-inf-fin-aux : ∀ F s w (b : Bool)
                 → (if b then nan F else infinity F (xorS s w))
                 ≡ (if b then nan F else infinity F (xorS w s))
mulV-inf-fin-aux F s w true  = refl
mulV-inf-fin-aux F s w false = cong (infinity F) (xorS-comm s w)

mulV-comm : ∀ F x y → mulV F x y ≡ mulV F y x
mulV-comm F fv-nan     fv-nan     = refl
mulV-comm F fv-nan     (fv-inf _) = refl
mulV-comm F fv-nan     (fv-fin _) = refl
mulV-comm F (fv-inf _) fv-nan     = refl
mulV-comm F (fv-fin _) fv-nan     = refl
mulV-comm F (fv-fin x) (fv-fin y) = cong (roundB F) (*B-comm x y)
mulV-comm F (fv-inf s) (fv-inf t) = cong (infinity F) (xorS-comm s t)
mulV-comm F (fv-inf s) (fv-fin y) = mulV-inf-fin-aux F s (signB y) (isZeroB y)
mulV-comm F (fv-fin x) (fv-inf t) = sym (mulV-inf-fin-aux F t (signB x) (isZeroB x))

fadd-comm : ∀ F a b → fadd F a b ≡ fadd F b a
fadd-comm F a b = addV-comm F (decode F a) (decode F b)

fmul-comm : ∀ F a b → fmul F a b ≡ fmul F b a
fmul-comm F a b = mulV-comm F (decode F a) (decode F b)

-- Pinned against the hardware, because a commutativity proof that held of the
-- wrong function would be no comfort.
_ : fadd binary64 0x3fb999999999999a 0x3fc999999999999a
  ≡ fadd binary64 0x3fc999999999999a 0x3fb999999999999a
_ = refl
