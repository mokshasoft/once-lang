-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Warnings — THE WARNING CHANNEL (plan 0.74 K4, D116)
--
-- Once had none, and its absence is why the interim rejection existed: with
-- no way to SAY "this rounded", the only honest thing left was to refuse.
-- K3 removed the refusal; this is what replaces it.
--
-- A PURE QUERY, NOT AN EFFECT. `roundingWarnings arch m` is a function of the
-- parsed module and the target — it is not threaded through `compile` and it
-- does not appear in `correct`. Warnings do not change what is compiled, so
-- they must not change the pipeline's type; keeping them a separate
-- observation is precisely what stops them leaking into the theorem.
--
-- THE WARNING CARRIES THE ERROR, EXACTLY. Both sides are exact — the literal
-- is a `Decimal` and the stored value is `m · 2^E` — so their difference is an
-- exact rational and no floating point is involved in computing it. That is
-- why `Warning`'s constructors carry NUMBERS rather than a rendered `String`:
-- a message is a projection, and a projection is not checkable. `TypeError`
-- already works this way (`FloatNotRepresentable` carries the decimal "so the
-- message can quote it back"), and this mirrors it deliberately.
--
-- IT REPLACES A DEAD ERROR. `TypeError.FloatNotRepresentable (int frac flen)`
-- is now unreachable — K3 made every float literal well-typed. `FloatRounded`
-- carries those same three fields plus the figures: what used to abort the
-- compile now reports.
--
-- IT SAYS WHERE. `at` is the literal's source offset, carried from the lexer
-- through `TFloat` and `RFloat`. "Some literal somewhere was rounded" is
-- nearly useless in a large module, and a warning that cannot be located is a
-- warning that gets ignored — which is how a warning channel dies.
--
-- The offset is DIAGNOSTIC METADATA and goes no further than this: the
-- elaborator drops it, so it never reaches `Surface.Expr`, the IR, the machine
-- or any correspondence proof. A position cannot change what is compiled, and
-- the fact that it stops here is what says so.
------------------------------------------------------------------------

module Once.Warnings where

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
import Data.Integer as ℤ
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String; length) renaming (_++_ to _<>_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Target.Arch using (Arch; arch-float-format)
open import Once.Float.Dyadic using (FloatFormat; binary32; binary64)
open import Once.Float.Decimal
  using (Decimal; _/10^_; decimalOf; round; roundSig; storedExp; maxFiniteExp)
open import Once.TypeCheck.Raw using
  ( RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct
  ; RUnit; RInt; RFloat; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna )
open import Once.Parser.Module.Core using
  (Module; mkModule; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias;
   DImport)

------------------------------------------------------------------------
-- An exact rational, unnormalised
--
-- `num / den`. No `gcd`, because nothing here needs a canonical form — the
-- figures are reported, not compared. Unnormalised and EXACT beats normalised
-- and approximate: the point of the payload change was that this difference
-- can be computed without floating point at all.
------------------------------------------------------------------------

record ExactQ : Set where
  constructor _/Q_
  field
    num : ℤ
    den : ℕ

open ExactQ public

------------------------------------------------------------------------
-- The warnings
------------------------------------------------------------------------

data Warning : Set where
  -- The literal was stored inexactly. Carries the digits AS WRITTEN (the
  -- dead `FloatNotRepresentable`'s three fields), the pattern actually
  -- emitted, and the error BOTH ways.
  --
  -- BOTH, and absolute FIRST, deliberately. Here is `3.1` at three formats:
  --
  --     binary64   3.1                    +8.9e-17   +0.2 ulp
  --     binary32   3.0999999046325684     −9.5e-08   −0.4 ulp
  --     4-bit sig  3.0                    −0.1       −0.4 ulp
  --
  -- The ulp figure is ~0.4 in all three. A ulp-ONLY warning would hide the
  -- one case a warning exists for — a 3% error on a narrow target.
  FloatRounded : (int frac flen : ℕ) (at : ℕ) (stored : ℕ) (absErr ulps : ExactQ) → Warning

  -- Too large for the format: stored as ±∞ (plan 0.74 K2).
  FloatOverflow : (int frac flen : ℕ) (at : ℕ) → Warning

  -- Too small: stored as zero. Once models no subnormals, so this fires where
  -- IEEE would still have had digits — a STATED limitation, and the reason it
  -- is a distinct constructor rather than a `FloatRounded` with a large error.
  FloatUnderflow : (int frac flen : ℕ) (at : ℕ) → Warning

------------------------------------------------------------------------
-- Classifying one literal
------------------------------------------------------------------------

-- | `max 0 E` and `max 0 (−E)`. Exactly one is non-zero, and together they
-- write `2^E` as `2^posPart / 2^negPart` without needing a signed power.
posPart negPart : ℤ → ℕ
posPart (+ n)      = n
posPart -[1+ _ ]   = 0
negPart (+ _)      = 0
negPart -[1+ n ]   = suc n

-- | The error of storing `sig/10^e` as `m · 2^E`, and the same in ulps.
--
--   stored − literal  =  (m·2^p·10^e − sig·2^q) / (10^e·2^q)      p,q as above
--   one ulp           =  2^E = 2^p/2^q
--   ulps              =  (m·2^p·10^e − sig·2^q) / (10^e·2^p)
--
-- Same numerator both times — only the denominator differs — which is what
-- makes "absolute or ulps" a presentation choice rather than two computations.
errorOf : (sig : ℕ) (e : ℕ) (m : ℕ) (E : ℤ) → ExactQ × ExactQ
errorOf sig e m E =
  (n /Q (10 ^ e * 2 ^ q)) , (n /Q (10 ^ e * 2 ^ p))
  where
    p = posPart E
    q = negPart E
    n : ℤ
    n = (+ (m * 2 ^ p * 10 ^ e)) ℤ.- (+ (sig * 2 ^ q))

-- | The warning this literal deserves at this format, if any.
--
-- `nothing` means STORED EXACTLY — the common case, and it must stay silent or
-- the channel is noise. An exactly-representable literal has a zero error
-- numerator, and that is the test.
--
-- Top-level auxes rather than a `where` chain, matching this codebase's
-- convention: each takes its scrutinee as an argument, so a caller that has
-- already decided can reduce through it.
warn-exact : ℕ → ℕ → ℕ → ℕ → FloatFormat → ExactQ → ExactQ → Maybe Warning
warn-exact i f l at F ((+ zero) /Q _) u = nothing            -- exact: say nothing
warn-exact i f l at F a               u =
  just (FloatRounded i f l at (round F (decimalOf i f l)) a u)

warn-under : ℕ → ℕ → ℕ → ℕ → ℕ → Maybe Warning
warn-under i f l at zero    = nothing                        -- 0.0 IS exactly 0.0
warn-under i f l at (suc _) = just (FloatUnderflow i f l at)

warn-hi : ℕ → ℕ → ℕ → ℕ → FloatFormat → ℕ → ℕ → ℤ → Bool → Maybe Warning
warn-hi i f l at F sig m E true  = just (FloatOverflow i f l at)
warn-hi i f l at F sig m E false =
  warn-exact i f l at F (proj₁ (errorOf sig l m E)) (proj₂ (errorOf sig l m E))

warn-at : ℕ → ℕ → ℕ → ℕ → FloatFormat → ℕ → ℕ → ℤ → ℤ → Maybe Warning
warn-at i f l at F sig m E -[1+ _ ]  = warn-under i f l at sig     -- underflowed
warn-at i f l at F sig m E (+ zero)  = warn-under i f l at sig
warn-at i f l at F sig m E (+ suc e) =
  warn-hi i f l at F sig m E (maxFiniteExp F ℕ.<ᵇ suc e)

floatWarning : FloatFormat → ℕ → ℕ → ℕ → ℕ → Maybe Warning
floatWarning F i f l at =
  warn-at i f l at F sig
          (proj₁ (roundSig F sig l)) (proj₂ (roundSig F sig l))
          (storedExp F (proj₁ (roundSig F sig l)) (proj₂ (roundSig F sig l)))
  where sig = i * 10 ^ l + f

------------------------------------------------------------------------
-- Walking the module
--
-- ENUMERATED, no catch-all, for the reason `rawIntLits` gives: a catch-all
-- would silently return `[]` for a constructor added later, and the literal it
-- failed to look at is exactly the one whose rounding would go unreported.
------------------------------------------------------------------------

rawFloatLits : RawExpr → List (ℕ × ℕ × ℕ × ℕ)
rawFloatLits (RFloat i f l p)      = (i , f , l , p) ∷ []
rawFloatLits (RApp f x)          = rawFloatLits f ++ rawFloatLits x
rawFloatLits (RLam _ b)          = rawFloatLits b
rawFloatLits (RLet _ e b)        = rawFloatLits e ++ rawFloatLits b
rawFloatLits (RPair a b)         = rawFloatLits a ++ rawFloatLits b
rawFloatLits (RDestruct s _ l _ r) = rawFloatLits s ++ rawFloatLits l ++ rawFloatLits r
rawFloatLits (RAnnot e _)        = rawFloatLits e
rawFloatLits (RBinOp _ a b)      = rawFloatLits a ++ rawFloatLits b
-- PLAN 0.73 F3: `-3.14` is ONE literal to the elaborator, but the warning
-- channel still sees the TOKEN `3.14` and reports its offset — which is the
-- right offset, since `-` is a token of its own. Every figure the warning
-- carries is unaffected by the sign: `round` splits into `signBit (sig d)` and
-- `∣ sig d ∣`, so a negated literal rounds with the same absolute error and
-- the same ulp count as its positive twin.
rawFloatLits (RUnaryOp _ e)      = rawFloatLits e
rawFloatLits (RAna _ e)          = rawFloatLits e
rawFloatLits (RVar _)            = []
rawFloatLits (RQualified _ _)    = []
rawFloatLits (RResolved _)       = []
rawFloatLits RUnit               = []
rawFloatLits (RInt _)            = []
rawFloatLits (RStringLit _)      = []

declFloatLits : Decl → List (ℕ × ℕ × ℕ × ℕ)
declFloatLits (DFunDef _ _ body)   = rawFloatLits body
declFloatLits (DTypeSig _ _)       = []
declFloatLits (DSignature _ _ _ _) = []
declFloatLits (DTypeAlias _ _ _)   = []
declFloatLits (DImport _)          = []

moduleFloatLits : Module → List (ℕ × ℕ × ℕ × ℕ)
moduleFloatLits (mkModule ds) = go ds
  where
    go : List Decl → List (ℕ × ℕ × ℕ × ℕ)
    go []       = []
    go (d ∷ ds) = declFloatLits d ++ go ds

-- | THE query. A function of the module and the target, and of nothing else.
roundingWarnings : Arch → Module → List Warning
roundingWarnings arch m = go (moduleFloatLits m)
  where
    F = arch-float-format arch
    go : List (ℕ × ℕ × ℕ × ℕ) → List Warning
    go [] = []
    go ((i , f , l , p) ∷ rest) = keep (floatWarning F i f l p)
      where
        keep : Maybe Warning → List Warning
        keep nothing  = go rest
        keep (just w) = w ∷ go rest

------------------------------------------------------------------------
-- PINNED
--
-- The figures are the whole point of this module, so they are checked against
-- errors computed elsewhere (Python `fractions`, exact rational arithmetic).
-- `refl` decides them by evaluation.
--
-- The fractions are UNNORMALISED here, so a pin states the numerator and the
-- denominator this computation actually produces; the VALUE is what was
-- checked externally.
------------------------------------------------------------------------

private
  -- 3.1 at binary64: stored slightly HIGH, by 1/11258999068426240 ≈ +8.9e-17.
  -- 3.1 at binary64: stored slightly HIGH. `2 / (10·2^51)` is
  -- `1/11258999068426240` ≈ +8.9e-17, and `2/10` is +0.2 ulp — both exactly
  -- the figures in this plan's own table, computed here without any floating
  -- point at all.
  _ : floatWarning binary64 3 1 1 0
        ≡ just (FloatRounded 3 1 1 0 (round binary64 (decimalOf 3 1 1))
                             ((+ 2) /Q (10 ^ 1 * 2 ^ 51))
                             ((+ 2) /Q (10 ^ 1 * 2 ^ 0)))
  _ = refl

  -- …and at binary32 it is stored LOW, and the SIGN says so. `−4/(10·2^22)`
  -- is `−1/10485760` ≈ −9.5e-08, and `−4/10` is −0.4 ulp — again the table's
  -- own figures.
  --
  -- THIS PAIR IS THE ARGUMENT FOR REPORTING BOTH. The ulp figure is 0.2 and
  -- 0.4 — same order — while the absolute error differs by nine orders of
  -- magnitude. On a narrow enough format the ulps stay ~0.4 while the absolute
  -- error reaches 3%, and a ulp-only warning would report the harmless case
  -- and the catastrophic one identically.
  _ : floatWarning binary32 3 1 1 0
        ≡ just (FloatRounded 3 1 1 0 (round binary32 (decimalOf 3 1 1))
                             (-[1+ 3 ] /Q (10 ^ 1 * 2 ^ 22))
                             (-[1+ 3 ] /Q (10 ^ 1 * 2 ^ 0)))
  _ = refl

  -- An exactly-representable literal is SILENT at both formats. If this ever
  -- returns a warning the channel has become noise, which is the failure mode
  -- a warning system dies of.
  _ : floatWarning binary64 5 0 1 0 ≡ nothing
  _ = refl

  _ : floatWarning binary32 5 0 1 0 ≡ nothing
  _ = refl

  _ : floatWarning binary64 2 75 2 0 ≡ nothing
  _ = refl

  -- 0.0 is exactly 0.0 — the underflow branch must not fire on it.
  _ : floatWarning binary32 0 0 1 0 ≡ nothing
  _ = refl

  -- 16777217 is exact at binary64 and ROUNDED at binary32 — the literal K3
  -- stopped rejecting. Silent on one target, a warning on the other, which is
  -- the whole reason the query takes an `Arch`.
  _ : floatWarning binary64 16777217 0 1 0 ≡ nothing
  _ = refl

  -- THE POSITION SURVIVES THE WALK. `3.14` at offset 42 is reported AT 42 —
  -- the whole point of the lexer/parser threading.
  _ : rawFloatLits (RFloat 3 14 2 42) ≡ (3 , 14 , 2 , 42) ∷ []
  _ = refl

  _ : floatWarning binary32 3 1 1 42
        ≡ just (FloatRounded 3 1 1 42 (round binary32 (decimalOf 3 1 1))
                             (-[1+ 3 ] /Q (10 ^ 1 * 2 ^ 22))
                             (-[1+ 3 ] /Q (10 ^ 1 * 2 ^ 0)))
  _ = refl

------------------------------------------------------------------------
-- RENDERING
--
-- The message is a PROJECTION of the numbers above, written here so the
-- numbers stay the thing that is checked. `TypeError`'s `renderError` works
-- the same way and for the same reason.
--
-- The absolute error is shown as an EXACT FRACTION. A decimal rendering wants
-- scientific notation (`-9.5e-08`), which is real formatting work and not
-- worth faking with a truncation — the fraction is exact and the ulps figure
-- is the one a reader compares at a glance.
------------------------------------------------------------------------

showQ : ExactQ → String
showQ q = showℤ (num q) <> "/" <> showNat (den q)

-- | The fraction numeral, PADDED to its digit count.
--
-- The payload stores `0.01` as `frac = 1, flen = 2` (D116: the payload is the
-- decimal the programmer wrote, and `flen` is part of it). Printing `frac`
-- alone renders that as `0.1` — a DIFFERENT literal from the one in the source,
-- which is the one thing a diagnostic may never do. The digit count is not
-- decoration; it is where the leading zeros live.
zeros : ℕ → String
zeros zero    = ""
zeros (suc n) = "0" <> zeros n

showFrac : ℕ → ℕ → String
showFrac f l = zeros (l ∸ length (showNat f)) <> showNat f

showLit : ℕ → ℕ → ℕ → String
showLit i f l = showNat i <> "." <> showFrac f l <> " (" <> showNat l <> " frac digits)"

renderWarning : Warning → String
renderWarning (FloatRounded i f l at stored absErr ulps) =
  "warning: float literal " <> showLit i f l <> " at offset " <> showNat at
    <> " is not exact at this target; stored as 0x-pattern " <> showNat stored
    <> ", absolute error " <> showQ absErr
    <> ", " <> showQ ulps <> " ulp"
renderWarning (FloatOverflow i f l at) =
  "warning: float literal " <> showLit i f l <> " at offset " <> showNat at
    <> " is too large for this target's format; stored as infinity"
renderWarning (FloatUnderflow i f l at) =
  "warning: float literal " <> showLit i f l <> " at offset " <> showNat at
    <> " is too small for this target's format; stored as zero"
    <> " (Once models no subnormals)"

-- | The compiler's entry point: every rounding warning this module has for
-- this target, rendered. `Once.Compile` re-exports it and the CLI prints it,
-- which is what keeps this module ON the apex path rather than beside it.
warningsFor : Arch → Module → List String
warningsFor arch m = go (roundingWarnings arch m)
  where
    go : List Warning → List String
    go []       = []
    go (w ∷ ws) = renderWarning w ∷ go ws
