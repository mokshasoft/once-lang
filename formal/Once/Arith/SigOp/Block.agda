-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.Block
--
-- Plan 0.20 Phase E — the `arith.block.<digest>` SigOpInfo family
-- and the `blockProvider` that lowers them.
--
-- D-arith-1 / D-arith-7: from CCC's perspective an arith block is a
-- single opaque SigOp. It carries
--   - name = "arith.block." ++ digest of the recognised MArithIR
--   - semI = eval-arith body (lifted from ⟦sh⟧S to ⟦shape-as-type sh⟧)
--   - semM = the definitional modular-`Word` evaluator (D054); the
--           machine layer denotes `Int` as the CPU's `add`.
--
-- The Provider recognises any SigOp whose name starts with
-- `"arith.block."` and discharges its `Contract` via the same
-- `mkPurePrimResult` machinery used by `add-int-proof`
-- (`Once.Arith.SigOp.Proofs.agda:137`). The block is pure from CCC's
-- view: no heap alloc, no halt, scratch usage stays in BeforeFrontier.
------------------------------------------------------------------------

module Once.Arith.SigOp.Block where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_<?_ to _<ℤ?_)
import Data.Integer as ℤ
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Type using (Type; Int)
open import Once.SigOp.Info using (SigOpInfo; mk-info; name; Pure)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Int; base-Float; base-Prod; con-base)
open import Once.CanonicalName using (bare)

open import Once.Arith.Machine.AbsState
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair; ⟦_⟧S; InputPath; Side; Fst; Snd;
         Path; here-int; here-flt; go-fst; go-snd; ⌊_⌋ᴾ)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f;
         numtype-as-type;
         shape-as-type; ArithBlock; mk-block)
import Once.Word as OnceWord
-- PLAN 0.74 J5: was `module W = OnceWord.Word64`. `block-semM` is the
-- definitional modular-`Word` evaluator an arith BLOCK denotes, and a block
-- is lowered by all three backends, so its width is the target's.
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
module W (tn : TargetNum) = OnceWord.Width (int-bits tn)

open import Once.Float.Dyadic using (Dyadic)
open import Once.Float.Decimal using (Decimal; sig; exp10; round)
import Once.Float.Arith as FA
open import Once.Arith.Type using (NumType; NInt; NFloat)
import Once.Semantics.Value OnceWord.Carrier OnceWord.Carrier as M
-- (Core ℤ as I removed: block-info's semI deleted — block-semM is the meaning.)

------------------------------------------------------------------------
-- Digest computation (deterministic serialisation)
------------------------------------------------------------------------

-- | Render a path as alphanumeric-only chars. `F`=Fst, `S`=Snd, `Z`
-- terminates. The terminator gives a delimiter-free encoding that is
-- still injective in the path's contents.
show-side : Side → String
show-side Fst = "F"
show-side Snd = "S"

show-path : InputPath → String
show-path []       = "Z"
show-path (s ∷ p)  = show-side s ++ show-path p

-- | Render a ℤ literal as alphanumeric chars: positive `+n` → `n_`,
-- negative `-n` → `n<n>_`. Trailing `_` delimits so the digest is
-- linearly reconstructible without spaces.
show-zlit : ℤ → String
show-zlit (+_ n)         = showℕ n ++ "_"
show-zlit (-[1+_] n)     = "n" ++ showℕ (suc n) ++ "_"

-- | …and a `Decimal` payload, as its two fields (plan 0.75 F4). Rendered
-- UNNORMALISED, because the payload is: `0.5` and `0.50` are distinct records
-- (D116) and therefore distinct blocks. They round to the same word, so the
-- two bodies are identical — a missed sharing opportunity, never a wrong
-- answer, and `Once.Float.Decimal` pins the pair agreeing.
show-dlit : Decimal → String
show-dlit d = show-zlit (sig d) ++ showℕ (exp10 d) ++ "_"

-- | Render an MArithIR tree as a stable, alphanumeric-only digest.
-- Plan 0.20 Phase G: the digest is used as the suffix of an assembly
-- symbol (`once_arith.block.<digest>`), so it must avoid spaces /
-- parens / arithmetic punctuation that GNU `as` doesn't accept in
-- symbol names. Operators map to capital-letter mnemonics:
--   A = add, B = sub, M = mul, G = neg.
-- Leaves: `L` for literal, `I` for input projection. Terminators
-- (`_`, `Z`) keep the encoding prefix-free.
--
-- PLAN 0.75 F4: `F` for a float literal and `C` for the D125 widening. The
-- digest must SEPARATE the kinds — `1 + 2` at `Int` and at `Float` are
-- different blocks needing different instructions, and a digest that collided
-- them would link one body for both. The `NumType` index does not appear in
-- the string because it is DETERMINED by the leaves: a tree containing `F` or
-- `C` is a float tree and no other tree is.
show-arith-ir : ∀ {sh n} → MArithIR sh n → String
show-arith-ir (alit z)     = "L" ++ show-zlit z
show-arith-ir (aflit d)    = "F" ++ show-dlit d
show-arith-ir (ainput p)   = "I" ++ show-path ⌊ p ⌋ᴾ
show-arith-ir (aadd a b)   = "A" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (asub a b)   = "B" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (amul a b)   = "M" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (adiv a b)   = "D" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (amod a b)   = "R" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (aneg a)     = "G" ++ show-arith-ir a
show-arith-ir (ai2f a)     = "C" ++ show-arith-ir a

-- | The digest is just the serialisation. (A hash function would be
-- stable across re-renders and shorter; the plan's "64-bit hex digest"
-- is a Phase E follow-up. The serialisation is sufficient for
-- correctness; only symbol-table size suffers.)
block-digest : ∀ {sh n} → MArithIR sh n → String
block-digest e = show-arith-ir e

-- | The canonical name for an arith block.
block-name : ∀ {sh n} → MArithIR sh n → String
block-name e = "arith.block." ++ block-digest e

------------------------------------------------------------------------
-- Bridge: ⟦ shape-as-type sh ⟧ ↔ ⟦ sh ⟧S
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SigOpInfo family
------------------------------------------------------------------------

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
-- modular ops for `Int`, `Once.Float.Arith`'s for `Float`, both reading the
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

-- | The block's `SigOpInfo`.
--
-- `semI` is definitional (`eval-arith` lifted through `toShape-I`),
-- so any downstream evaluator that reduces through proof-level
-- semantics gets the arith result directly. `semM` is the
-- definitional modular-`Word` evaluator (`block-semM`).
-- A block's input shape is a tuple of `Unit`/`Int` ⇒ its `shape-as-type` is base.
shape-as-type-base : ∀ (sh : InputShape) → IsBaseType (shape-as-type sh)
shape-as-type-base shape-unit       = base-Unit
shape-as-type-base shape-int        = base-Int
shape-as-type-base shape-float      = base-Float
shape-as-type-base (shape-pair l r) = base-Prod (shape-as-type-base l) (shape-as-type-base r)

-- …and the codomain's, which used to be the constant `base-Int`.
numtype-as-type-base : ∀ (n : NumType) → IsBaseType (numtype-as-type n)
numtype-as-type-base NInt   = base-Int
numtype-as-type-base NFloat = base-Float

-- Split on the kind so `M.⟦ numtype-as-type n ⟧` reduces to `block-semM`'s
-- `Carrier`; the two branches are otherwise identical.
block-info : ∀ {sh n} → MArithIR sh n → SigOpInfo (shape-as-type sh) (numtype-as-type n)
block-info {sh} {NInt} e = mk-info
  (bare (block-name e))
  (block-semM e)
  Pure  -- arith blocks are observably pure (no event, no halt)
  (shape-as-type-base sh) (con-base (numtype-as-type-base NInt))
block-info {sh} {NFloat} e = mk-info
  (bare (block-name e))
  (block-semM e)
  Pure
  (shape-as-type-base sh) (con-base (numtype-as-type-base NFloat))
