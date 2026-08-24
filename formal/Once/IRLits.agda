-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.IRLits — THE LITERALS THE MACHINE ACTUALLY MATERIALISES
-- (plan 0.74 J6 step 2, D115).
--
-- `Once.Denotation.Admissible` walks the SOURCE and says which literals the
-- programmer wrote. This walks the IR and says which literals the machine
-- will LOAD. They are not the same list, and the difference is exactly where
-- the compiler is wrong.
--
-- WHY THE SECOND LIST HAS TO EXIST. The gate was decorative because both
-- sides read the SOURCE: `cfm-build-gated` dispatched on `admissibleM?`, the
-- very predicate the spec states, so "the backend agrees with the spec" held
-- by SHARING A TRAVERSAL rather than by proof. `Admissible.agda` already says
-- that is wrong — "The backend walks the IR instead, and that the two agree
-- is a PROOF obligation, not something faked by sharing a traversal" — and
-- this is the IR walk that obligation needs.
--
-- WHAT IT EXPOSES IMMEDIATELY. `-2147483648` parses as
-- `RUnaryOp OpNeg (RInt 2147483648)` and nothing folds the sign, so the
-- SOURCE list holds `-2147483648` (in range at 32 bits) while THIS list
-- holds `2147483648` (out of range). Gating on this list makes completeness
-- — "a program whose literals the target can express compiles" — unprovable
-- until the elaborator stops manufacturing the magnitude. That is the point:
-- the red lands on the elaborator, which is where the defect is.
--
-- ENUMERATED, no catch-all, for the reason `rawIntLits` gives: a catch-all
-- would silently return `[]` for a constructor added later, and the literal
-- it failed to look at is precisely the one that would be materialised
-- unchecked.
------------------------------------------------------------------------

module Once.IRLits where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Integer using (ℤ)

open import Once.Float.Decimal using (Decimal; decimalOf; round)
open import Once.IRTy using (IRTy; FitsInRegI; fits-int; fits-float; ⟦_,_⟧-baseI)
open import Once.IR using (IR; NatTr)

open IR
open NatTr

------------------------------------------------------------------------
-- The `const` payload, split by which numeric type it carries.
--
-- Mirrors `LitPayload`: an `Int` literal's payload is a `ℤ` and IS checked;
-- a `Float` literal's payload is a `Dyadic` and is NOT, because a float
-- literal always lowers, rounding where the target cannot hold it (D116).
------------------------------------------------------------------------

constLits : ∀ {A : IRTy} (p : FitsInRegI A) → ⟦ ℤ , Decimal ⟧-baseI A → List ℤ
constLits fits-int   z = z ∷ []
constLits fits-float _ = []

------------------------------------------------------------------------
-- The traversal. Mutual with `NatTr`, which `Hylo`/`Fuse` carry.
------------------------------------------------------------------------

irIntLits : ∀ {A B : IRTy} → IR A B → List ℤ
ntIntLits : ∀ {G F} → NatTr G F → List ℤ

irIntLits id            = []
irIntLits (g ∘ f)       = irIntLits g ++ irIntLits f
irIntLits (⟨ f , g ⟩ _) = irIntLits f ++ irIntLits g
irIntLits fst           = []
irIntLits snd           = []
irIntLits (inl _)       = []
irIntLits (inr _)       = []
irIntLits (case f g)    = irIntLits f ++ irIntLits g
irIntLits terminal      = []
irIntLits initial       = []
irIntLits (curry f _)   = irIntLits f
irIntLits apply         = []
irIntLits (In _ _)      = []
irIntLits (out-μ _)     = []
irIntLits (Cata _ alg)  = irIntLits alg
irIntLits (Para _ alg)  = irIntLits alg
irIntLits (Out _)       = []
irIntLits (in-ν _ _)    = []
irIntLits (Ana _ coalg) = irIntLits coalg
irIntLits (Hylo _ _ alg nt) = irIntLits alg ++ ntIntLits nt
irIntLits (Fuse _ _ alg nt) = irIntLits alg ++ ntIntLits nt
irIntLits (free-heap _) = []
irIntLits (const p v)   = constLits p v
irIntLits (SigOp _)     = []

ntIntLits ntId          = []
ntIntLits (ntK f)       = irIntLits f
ntIntLits (ntFst nt)    = ntIntLits nt
ntIntLits (ntSnd nt)    = ntIntLits nt
ntIntLits (ntCase l r)  = ntIntLits l ++ ntIntLits r
ntIntLits (ntInl nt)    = ntIntLits nt
ntIntLits (ntInr nt)    = ntIntLits nt
ntIntLits (ntPair l r)  = ntIntLits l ++ ntIntLits r
