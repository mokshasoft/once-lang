-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatRegTagWF
--
-- REGISTER-TAG well-formedness: the two counter registers `Scratch` and
-- `Count` always hold an `SV-Tag`.
--
-- This is what makes the counter instructions correspond to their x86
-- lowerings. Abstractly `sv-succ`/`sv-pred` COERCE a non-tag to a tag
-- (`sv-pred (SV-Ptr p) = SV-Tag 0`) while the concrete `add`/`sub` work on the
-- ENCODING, and `sv-is-zero` recognises only tags while `cmp` compares
-- encodings. So on a non-tag the two machines genuinely disagree, and
-- `branch-scratch-nontag` / `scratch-dec-nontag` / `count-inc-nontag` were
-- postulated to paper over exactly that.
--
-- The invariant is a STATE invariant — local, per instruction, compositional —
-- and NOT a whole-program dataflow fact. That is only true because plan 0.54 D
-- item 4 split the tally off `Input2` into its own `Count` register: the four
-- writers of `Scratch` (`scratch-one`, `scratch-zero`, `scratch-dec`,
-- `scratch-load-count`) and the two writers of `Count` (`count-zero`,
-- `count-inc`) ALL produce a tag unconditionally, the last two by reading a
-- register this very invariant says is a tag. Before the split,
-- `mov-output-to-input2` (`Input2 := Output`) could put an arbitrary value in
-- the tally, so no such invariant existed — and that instruction is documented
-- as intended for future nested-pair codegen, so the property was false by
-- design intent, not merely unproven.
--
-- Proved by induction over `exec-abstract`, mutually with `regtag-trace` /
-- `regtag-case` / `regtag-loop` so the nested `instr-case-on-tag` / `instr-loop`
-- traces are covered (mirroring `FlatStoreWF`). Lifted to `flat-exec-instr` at
-- the end. NO new postulates: `instr-sigop` writes only `Output` and `halted`,
-- so a SigOp cannot disturb a counter.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatRegTagWF (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Machine.SMCore
open FrameSemantics FS using (Frame)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- "Holds a tag". Stated as an existential EQUATION rather than a predicate
-- with a catch-all (`IsTag (SV-Tag _) = ⊤; IsTag _ = ⊥`), because a catch-all
-- does not survive the case-tree translation and would not reduce at the use
-- sites — the same trap as `enc-sv`'s `SV-Lit` clause.
------------------------------------------------------------------------
IsTag : StoredValue FS → Set
IsTag sv = Σ ℕ (λ n → sv ≡ SV-Tag n)

record RegTagWF (ls : LocState FS) : Set where
  constructor mkRegTagWF
  field
    scratch-tag : IsTag (readReg (regs ls) Scratch)
    count-tag   : IsTag (readReg (regs ls) Count)
open RegTagWF public

------------------------------------------------------------------------
-- The two coercions land on tags GIVEN a tag (that is the whole content: on a
-- non-tag they also land on a tag, but at a value the concrete machine does
-- not compute).
------------------------------------------------------------------------
sv-succ-tag : ∀ (v : StoredValue FS) → IsTag v → IsTag (sv-succ v)
sv-succ-tag .(SV-Tag n) (n , refl) = suc n , refl

sv-pred-tag : ∀ (v : StoredValue FS) → IsTag v → IsTag (sv-pred v)
sv-pred-tag .(SV-Tag zero)    (zero  , refl) = zero , refl
sv-pred-tag .(SV-Tag (suc n)) (suc n , refl) = n , refl

------------------------------------------------------------------------
-- Register writes. `Scratch`/`Count` are preserved by a write to any OTHER
-- register; the two writes that DO hit them carry a tag.
------------------------------------------------------------------------
regtag-write-other : ∀ {ls} (x : AbstractReg) (v : StoredValue FS)
  → (readReg (writeReg (regs ls) x v) Scratch ≡ readReg (regs ls) Scratch)
  → (readReg (writeReg (regs ls) x v) Count   ≡ readReg (regs ls) Count)
  → RegTagWF ls → RegTagWF (record ls { regs = writeReg (regs ls) x v })
regtag-write-other {ls} x v sc-p ct-p wf = record
  { scratch-tag = (proj₁ (scratch-tag wf)) , trans sc-p (proj₂ (scratch-tag wf))
  ; count-tag   = (proj₁ (count-tag wf))   , trans ct-p (proj₂ (count-tag wf)) }

-- Input1 / Input2 / Output writes: both counters untouched (definitional).
regtag-write-in1 : ∀ {ls} (v : StoredValue FS) → RegTagWF ls
                 → RegTagWF (record ls { regs = writeReg (regs ls) Input1 v })
regtag-write-in1 {ls} v wf = regtag-write-other {ls} Input1 v refl refl wf

regtag-write-in2 : ∀ {ls} (v : StoredValue FS) → RegTagWF ls
                 → RegTagWF (record ls { regs = writeReg (regs ls) Input2 v })
regtag-write-in2 {ls} v wf = regtag-write-other {ls} Input2 v refl refl wf

regtag-write-out : ∀ {ls} (v : StoredValue FS) → RegTagWF ls
                 → RegTagWF (record ls { regs = writeReg (regs ls) Output v })
regtag-write-out {ls} v wf = regtag-write-other {ls} Output v refl refl wf
