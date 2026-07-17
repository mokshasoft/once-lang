-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.PreserveCore  (Plan 0.54 Phase B / Option 2)
--
-- The ARCH-GENERIC register CCC-preservation framework. Parameterised by the
-- small per-arch base — the concrete register file, `writeReg`, the
-- "not-CCC" predicate, and the enumerated `AgreeCCC` with its three lemmas
-- (refl / trans / write-a-non-CCC-register-agrees) — plus the emit's
-- `writes`/`confined`. Everything downstream (the lift, the write-sequence
-- lowering, `step-of` and its preservation) is IDENTICAL across arches and
-- lives here ONCE. Each arch's `Preserve` provides only the base and re-exports.
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_; proj₁)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (map⁺)

open import Once.Arith.Backend.XInstr.Syntax using (XInstr)

module Once.Arith.Backend.PreserveCore
  {Word Reg RegFile : Set}
  (writeReg           : RegFile → Reg → Word → RegFile)
  (NotCCC             : Reg → Set)
  (AgreeCCC           : RegFile → RegFile → Set)
  (agree-refl-ccc     : ∀ rf → AgreeCCC rf rf)
  (AgreeCCC-trans     : ∀ {a b c} → AgreeCCC a b → AgreeCCC b c → AgreeCCC a c)
  (write-nonccc-agrees : ∀ rf w v → NotCCC w → AgreeCCC rf (writeReg rf w v))
  (writes             : XInstr → List Reg)
  (confined           : ∀ i → All NotCCC (writes i))
  where

-- A register-file step "preserves CCC" if it agrees on the CCC registers.
PreservesCCC-rf : (RegFile → RegFile) → Set
PreservesCCC-rf f = ∀ rf → AgreeCCC rf (f rf)

-- Block = list of steps; CCC-preservation composes.
runFns : List (RegFile → RegFile) → RegFile → RegFile
runFns []       rf = rf
runFns (f ∷ fs) rf = runFns fs (f rf)

preserves-runFns : ∀ fs → All PreservesCCC-rf fs → PreservesCCC-rf (runFns fs)
preserves-runFns []       _          rf = agree-refl-ccc rf
preserves-runFns (f ∷ fs) (pf ∷ pfs) rf =
  AgreeCCC-trans (pf rf) (preserves-runFns fs pfs (f rf))

-- Write a footprint of (register, value) pairs; a non-CCC footprint preserves CCC.
write-regs : List (Reg × Word) → RegFile → RegFile
write-regs []             rf = rf
write-regs ((w , v) ∷ ps) rf = write-regs ps (writeReg rf w v)

write-regs-preserves : ∀ ps → All (λ p → NotCCC (proj₁ p)) ps →
                       PreservesCCC-rf (write-regs ps)
write-regs-preserves []             _          rf = agree-refl-ccc rf
write-regs-preserves ((w , v) ∷ ps) (nc ∷ ncs) rf =
  AgreeCCC-trans (write-nonccc-agrees rf w v nc) (write-regs-preserves ps ncs (writeReg rf w v))

-- Instruction i's register step (write its footprint) preserves CCC — from `confined`.
step-of : XInstr → (Reg → Word) → RegFile → RegFile
step-of i val = write-regs (map (λ r → (r , val r)) (writes i))

step-of-preserves : ∀ i val → PreservesCCC-rf (step-of i val)
step-of-preserves i val = write-regs-preserves _ (map⁺ (confined i))
