-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandRen — the renaming of refs (D468, 3c3b): the
-- primitive run's fresh refs to the expanded run's reused ones, on heap cells,
-- locations and values.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandRen {FS : FrameSemantics} where

open import Data.Nat using (ℕ)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Once.CCC.Machine.SMCore using (StoredValue; SV-Ptr; SV-Tag; SV-Lit; SV-Code)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)

------------------------------------------------------------------------
-- The renaming of refs, on locations and values
------------------------------------------------------------------------

ref-of : HeapLocation → ℕ
ref-of hl = HeapRef.ref-id (HeapLocation.heap-ref hl)

rhl : (ℕ → ℕ) → HeapLocation → HeapLocation
rhl ρ hl = heap-loc (mkHeapRef (ρ (ref-of hl))) (HeapLocation.heap-offset hl)

rloc : (ℕ → ℕ) → ValueLocation FS → ValueLocation FS
rloc ρ (AtStack f k)  = AtStack f k
rloc ρ (AtDynamic hl) = AtDynamic (rhl ρ hl)

rv : (ℕ → ℕ) → StoredValue FS → StoredValue FS
rv ρ (SV-Ptr loc)  = SV-Ptr (rloc ρ loc)
rv ρ (SV-Tag n)    = SV-Tag n
rv ρ (SV-Lit p v)  = SV-Lit p v
rv ρ (SV-Code l)   = SV-Code l

-- a block's base pointer, and a record word's location
blk : ℕ → StoredValue FS
blk b = SV-Ptr (AtDynamic (heap-loc (mkHeapRef b) 0))

rec-loc : ℕ → HeapLocation
rec-loc k = heap-loc (mkHeapRef 0) k

