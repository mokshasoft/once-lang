-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.BlockSem — WHAT AN ARITH BLOCK MEANS: the definitional
-- machine evaluator of its body (`block-semM`).
--
-- Plan 0.129 B5: below `Once.SigOp.Info`, because a block's contract is its
-- body (`blockV e`) and its meaning is read off the body here; it was in
-- `Arith.SigOp.Block`, which builds `SigOpInfo`s and so sits above `Info`.
------------------------------------------------------------------------

module Once.Arith.SigOp.BlockSem where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Once.Arith.CmpOp using (cmp-bit)
open import Once.Arith.Machine.Shape using (InputShape; shape-unit; shape-int; shape-float; shape-pair; InputPath; Fst; Snd; Path; here-int; here-flt; go-fst; go-snd)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f; acmp; numtype-as-type; shape-as-type)
import Once.Spec.Word as OnceWord
-- PLAN 0.74 J5: was `module W = OnceWord.Word64`. `block-semM` is the
-- definitional modular-`Word` evaluator an arith BLOCK denotes, and a block
-- is lowered by all three backends, so its width is the target's.
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open TargetNum using (int-bits; float-format)
module W (tn : TargetNum) = OnceWord.Width (int-bits tn)

open import Once.Spec.Float.Decimal using (round)
import Once.Spec.Float.Arith as FA
open import Once.Arith.Type using (NumType; NInt; NFloat)
import Once.IR.Semantics.Value OnceWord.Carrier OnceWord.Carrier as M

-- | Machine-level semantics for the block (D054).
--
-- The machine layer denotes `Int` as a modular `Word` (= the CPU's
-- `add`), so `block-semM` is the definitional `Word` evaluator,
-- mirroring `eval-arith` (the ℤ spec) op-for-op with the modular
-- operations from `Once.Arith.Word`: wraparound IS the defined meaning, so
-- the evaluator is total on every input.
--
-- `M.⟦ Int ⟧` is `ℕ` (machine `IntRep`), and `Word` is `ℕ`, so the
-- result carrier matches definitionally.

-- | Project a `Word` leaf out of a machine-typed input tree. Parallel
-- to `project` (AbsState) but over `M.⟦ shape-as-type sh ⟧` rather
-- than `⟦ sh ⟧S`.
-- PLAN 0.75 F4: TAKES THE KIND, and that is a correctness fix rather than
-- bookkeeping. At the machine level BOTH leaves are `Carrier` — a bit pattern
-- (D113) — so a kind-blind projection would happily read an `Int` leaf's word
-- as a float pattern for an `ainput` at `NFloat`, and the types could not
-- object because the carriers are equal. Silent type confusion, invisible to
-- every gate: exactly the shape this branch has found three times.
--
-- Asking for the kind makes a mismatched path `nothing`, which the caller
-- defaults. Recognition only ever builds paths that land on the right leaf;
-- this is what says so.
projectM : NumType → ∀ (sh : InputShape) → InputPath → M.⟦ shape-as-type sh ⟧ → Maybe OnceWord.Carrier
projectM _      shape-unit       _         _       = nothing
projectM NInt   shape-int        []        z       = just z
projectM NInt   shape-int        (_ ∷ _)   _       = nothing
projectM NFloat shape-int        _         _       = nothing
projectM NFloat shape-float      []        w       = just w
projectM NFloat shape-float      (_ ∷ _)   _       = nothing
projectM NInt   shape-float      _         _       = nothing
projectM _      (shape-pair _ _) []        _       = nothing
projectM k      (shape-pair l _) (Fst ∷ p) (x , _) = projectM k l p x
projectM k      (shape-pair _ r) (Snd ∷ p) (_ , y) = projectM k r p y

-- | THE machine-side read, along a TYPED path — total, so no default. The
-- `Maybe` version above survives only for the untyped `InputPath` callers; a
-- node built by `ainput` always has the typed one, and `projectM-path` below
-- says the two agree, which is what lets the old callers keep working while
-- the invented `0` becomes unreachable rather than merely unlikely.
readLeafM : ∀ {sh n} → Path sh n → M.⟦ shape-as-type sh ⟧ → OnceWord.Carrier
readLeafM here-int   z       = z
readLeafM here-flt   w       = w
readLeafM (go-fst p) (x , _) = readLeafM p x
readLeafM (go-snd p) (_ , y) = readLeafM p y

-- | Default-zero for an out-of-shape path (mirrors `eval-arith`'s
-- `+ 0` rule; well-formed IRs never hit it).
maybe-zeroM : Maybe OnceWord.Carrier → OnceWord.Carrier
maybe-zeroM (just w) = w
maybe-zeroM nothing  = 0

-- PLAN 0.75 F4: kind-indexed, and the ops DISPATCH ON THE KIND. `Once.Word`'s
-- modular ops for `Int`, `Once.Spec.Float.Arith`'s for `Float`, both reading the
-- target out of the `TargetNum` they are handed — the same `semM` the per-op
-- float SigOps use, so the blocked and per-op paths agree by construction
-- rather than by two definitions that must be kept in step.
-- The result type is `Carrier` OUTRIGHT, not `M.⟦ numtype-as-type n ⟧`. Both
-- reduce to it, but only once `n` is concrete — and a theorem stated over an
-- abstract `n` (`BlockSemBridge.eval≡semM`) needs the two sides to be the same
-- type BEFORE any clause is written. `block-info` does the casing instead,
-- where `n` is available.
block-semM : ∀ {sh n} → MArithIR sh n → TargetNum
           → M.⟦ shape-as-type sh ⟧ → OnceWord.Carrier
block-semM (alit z)        tn _   = W.fromℤ tn z
block-semM (aflit d)       tn _   = round (float-format tn) d
-- SPLIT ON THE KIND even though the two bodies are identical: the result type
-- `M.⟦ numtype-as-type n ⟧` does not reduce while `n` is a variable, and both
-- branches reduce it to the same `Carrier`. The duplication is the type
-- checker's price for the carrier being shared, not a real case distinction.
block-semM {sh} (ainput p) tn inp = readLeafM p inp
block-semM {n = NInt}   (aadd a b) tn inp = W._⊕_  tn (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NFloat} (aadd a b) tn inp = FA.fadd (float-format tn) (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NInt}   (asub a b) tn inp = W._⊖_  tn (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NFloat} (asub a b) tn inp = FA.fsub (float-format tn) (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NInt}   (amul a b) tn inp = W._⊗_  tn (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NFloat} (amul a b) tn inp = FA.fmul (float-format tn) (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NInt}   (adiv a b) tn inp = W._/ˢ_ tn (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NFloat} (adiv a b) tn inp = FA.fdiv (float-format tn) (block-semM a tn inp) (block-semM b tn inp)
block-semM (amod a b)      tn inp = W._%ˢ_ tn (block-semM a tn inp) (block-semM b tn inp)
block-semM {n = NInt}   (aneg a)   tn inp = W.⊝_   tn (block-semM a tn inp)
block-semM {n = NFloat} (aneg a)   tn inp = FA.fneg (float-format tn) (block-semM a tn inp)
block-semM (ai2f a)        tn inp = FA.i2f (float-format tn) (W.toℤ tn (block-semM a tn inp))
block-semM (acmp o a b)    tn inp = cmp-bit (int-bits tn) o (block-semM a tn inp) (block-semM b tn inp)

-- | …at the block's declared codomain, graded: what its contract denotes.
-- Split on the kind so `M.⟦ numtype-as-type n ⟧ᵍ` reduces to `block-semM`'s
-- `Carrier`; the two branches are otherwise identical.
block-semP : ∀ {sh n} → MArithIR sh n → TargetNum → M.⟦ shape-as-type sh ⟧ → M.⟦ numtype-as-type n ⟧ᵍ
block-semP {n = NInt}   e = block-semM e
block-semP {n = NFloat} e = block-semM e
