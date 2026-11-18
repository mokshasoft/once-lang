-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.AsBlock — AN ARITHMETIC PRIMITIVE AS ITS BLOCK (D459).
--
-- A primitive that is not a comparison is one operation over its own input:
-- the block `aop (input fst) (input snd)` (or `aop (input)` for a unary one).
-- `as-block` replaces the primitive's contract by that block's (`blockV`), at
-- the same types and base derivations, named by the block's digest as
-- master's `block-info` is; every other SigOp (a comparison, a block, an
-- external op) is kept. Its meaning: `AsBlockSound`.
------------------------------------------------------------------------

module Once.Arith.SigOp.AsBlock where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Arith.Type using (NumType)
open import Once.Spec.Type using (Type; Base; ∅ₖ)
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; mk-info'; blockV; ffiV; callsV; emitsV; haltsV; primV; module SigOpInfo)
open import Once.Arith.Prim using (ArithPrim; p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-fneg; p-cmp; p-fcmp)
open import Once.Arith.Machine.IR using (MArithIR; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f; shape-as-type; numtype-as-type)
open import Once.Arith.Machine.Shape using (InputShape; shape-int; shape-float; shape-pair; here-int; here-flt; go-fst; go-snd)
open import Once.Arith.SigOp.Block using (block-name)

-- a primitive's block: its body over the input, at the primitive's types
record Lifted (A B : Type) : Set where
  constructor lifted
  field
    {sh} : InputShape
    {n}  : NumType
    body : MArithIR sh n
    eA   : A ≡ shape-as-type sh
    eB   : B ≡ numtype-as-type n

-- the two inputs of a binary op
pII pFF : InputShape
pII = shape-pair shape-int shape-int
pFF = shape-pair shape-float shape-float

-- ★ a primitive's block (a comparison has none: its answer is a bit, which a
-- block does not return)
prim-block : ∀ {A B} → ArithPrim A B → Maybe (Lifted A B)
prim-block p-add  = just (lifted {sh = pII} (aadd (ainput (go-fst here-int)) (ainput (go-snd here-int))) refl refl)
prim-block p-sub  = just (lifted {sh = pII} (asub (ainput (go-fst here-int)) (ainput (go-snd here-int))) refl refl)
prim-block p-mul  = just (lifted {sh = pII} (amul (ainput (go-fst here-int)) (ainput (go-snd here-int))) refl refl)
prim-block p-div  = just (lifted {sh = pII} (adiv (ainput (go-fst here-int)) (ainput (go-snd here-int))) refl refl)
prim-block p-mod  = just (lifted {sh = pII} (amod (ainput (go-fst here-int)) (ainput (go-snd here-int))) refl refl)
prim-block p-neg  = just (lifted {sh = shape-int} (aneg (ainput here-int)) refl refl)
prim-block p-fadd = just (lifted {sh = pFF} (aadd (ainput (go-fst here-flt)) (ainput (go-snd here-flt))) refl refl)
prim-block p-fsub = just (lifted {sh = pFF} (asub (ainput (go-fst here-flt)) (ainput (go-snd here-flt))) refl refl)
prim-block p-fmul = just (lifted {sh = pFF} (amul (ainput (go-fst here-flt)) (ainput (go-snd here-flt))) refl refl)
prim-block p-fdiv = just (lifted {sh = pFF} (adiv (ainput (go-fst here-flt)) (ainput (go-snd here-flt))) refl refl)
prim-block p-i2f  = just (lifted {sh = shape-int} (ai2f (ainput here-int)) refl refl)
prim-block p-fneg = just (lifted {sh = shape-float} (aneg (ainput here-flt)) refl refl)
prim-block (p-cmp o)    = nothing
prim-block (p-fcmp h o) = nothing

-- an op's block: a primitive's, if it has one; a block's own (rebuilt under
-- its canonical name, as master's `bare-sigop`)
block-of : ∀ {A B} → SigOpSem A B → Maybe (Lifted A B)
block-of (primV p)        = prim-block p
block-of (blockV e eA eB) = just (lifted e eA eB)
block-of ffiV             = nothing
block-of callsV           = nothing
block-of (emitsV e)       = nothing
block-of (haltsV e)       = nothing

-- the name and the contract, the block's when there is one (master's
-- `block-info`: named by its digest, its contract its body)
name-at : ∀ {A B} → CanonicalName → Maybe (Lifted A B) → CanonicalName
name-at nm nothing                 = nm
name-at nm (just (lifted e eA eB)) = bare (block-name e)

sem-at : ∀ {A B} → SigOpSem A B → Maybe (Lifted A B) → SigOpSem A B
sem-at s nothing                 = s
sem-at s (just (lifted e eA eB)) = blockV e eA eB

-- ★ the op as its block, at the same types and base derivations
as-block : ∀ {A B} → SigOpInfo A B → SigOpInfo A B
as-block si = mk-info' (name-at (SigOpInfo.name si) (block-of (SigOpInfo.sem si)))
                       (sem-at (SigOpInfo.sem si) (block-of (SigOpInfo.sem si)))
                       (SigOpInfo.baseA si) (SigOpInfo.conB si)


------------------------------------------------------------------------
-- ★ What it gives: a CANONICAL op — a block is named by its digest, a
-- primitive is one with no block (a comparison). What the image's arith
-- table needs of every op it calls (`LinCore.ImageOwned`).
------------------------------------------------------------------------

CanonicalAt : ∀ {A B} → CanonicalName → SigOpSem A B → Set
CanonicalAt nm (blockV e eA eB) = nm ≡ bare (block-name e)
CanonicalAt nm (primV p)        = prim-block p ≡ nothing
CanonicalAt nm ffiV             = ⊤
CanonicalAt nm callsV           = ⊤
CanonicalAt nm (emitsV e)       = ⊤
CanonicalAt nm (haltsV e)       = ⊤

Canonical : ∀ {A B} → SigOpInfo A B → Set
Canonical si = CanonicalAt (SigOpInfo.name si) (SigOpInfo.sem si)

private
  canon-prim : ∀ {A B} nm (p : ArithPrim A B) → CanonicalAt (name-at nm (prim-block p)) (sem-at (primV p) (prim-block p))
  canon-prim nm p-add  = refl
  canon-prim nm p-sub  = refl
  canon-prim nm p-mul  = refl
  canon-prim nm p-div  = refl
  canon-prim nm p-mod  = refl
  canon-prim nm p-neg  = refl
  canon-prim nm p-fadd = refl
  canon-prim nm p-fsub = refl
  canon-prim nm p-fmul = refl
  canon-prim nm p-fdiv = refl
  canon-prim nm p-i2f  = refl
  canon-prim nm p-fneg = refl
  canon-prim nm (p-cmp o)    = refl
  canon-prim nm (p-fcmp h o) = refl

  canon-at : ∀ {A B} nm (s : SigOpSem A B) → CanonicalAt (name-at nm (block-of s)) (sem-at s (block-of s))
  canon-at nm (primV p)        = canon-prim nm p
  canon-at nm (blockV e eA eB) = refl
  canon-at nm ffiV             = tt
  canon-at nm callsV           = tt
  canon-at nm (emitsV e)       = tt
  canon-at nm (haltsV e)       = tt

-- ★ every op, as its block, is canonical
as-block-canonical : ∀ {A B} (si : SigOpInfo A B) → Canonical (as-block si)
as-block-canonical si = canon-at (SigOpInfo.name si) (SigOpInfo.sem si)
