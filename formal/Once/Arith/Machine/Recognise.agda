-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Machine.Recognise
--
-- Plan 0.20 Phase B — the recognition pass.
--
-- Given a CCC morphism `IR A B`, attempt to classify it as a pure
-- arith block: an expression tree built only from
--   - `intLit n` (== `const fits-int n |n| ∘ terminal`)
--   - input projections (`snd`, `fst`, compositions thereof)
--   - the arithmetic SigOps `arith.{add,sub,mul,neg}.int`
--
-- A subtree containing `apply`, `case`, `cata`, μ-constructors,
-- closure references, or non-arith SigOps is *not* an arith block:
-- recognition returns `nothing` and the caller leaves the subtree
-- as ordinary CCC.
--
-- The recogniser is intentionally type-AGNOSTIC: it pattern-matches
-- on IR constructors without ever forcing the codomain from outside,
-- which avoids the dependent-pattern-matching dead-ends triggered by
-- `out-μ` and friends (whose indices unify badly with a fixed
-- product/Int target). Phase C's validity theorem layers typing on
-- top: when recognition succeeds and the IR is well-typed at Int,
-- the abstract trace matches eval-arith.
------------------------------------------------------------------------

module Once.Arith.Machine.Recognise where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type using (Type; Unit; Int)
open import Once.CCC.IR
open import Once.CCC.SigOp.Info using (SigOpInfo; name)

open import Once.Arith.Machine.AbsState
  using (InputShape; shape-int; shape-pair; InputPath;
         Side; Fst; Snd)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; aneg; ArithBlock;
         mk-block)

------------------------------------------------------------------------
-- Projection-path recognition
------------------------------------------------------------------------

-- | Recognise a CCC morphism that's a pure projection chain.
--
-- Returns the `InputPath` corresponding to "from the input, walk
-- this sequence of Fst/Snd to reach the result." Composition is
-- ordered "rightmost first": `snd ∘ fst` is the path `[Fst, Snd]`.
--
-- Returns `nothing` for non-projection morphisms.
recognise-path : ∀ {A B} → IR A B → Maybe InputPath
recognise-path id        = just []
recognise-path fst       = just (Fst ∷ [])
recognise-path snd       = just (Snd ∷ [])
recognise-path (f ∘ g)   with recognise-path g | recognise-path f
... | just pg | just pf  = just (pg ++ pf)
... | just _  | nothing  = nothing
... | nothing | _        = nothing
recognise-path _         = nothing

------------------------------------------------------------------------
-- Arith body recognition (type-agnostic on IR's codomain)
------------------------------------------------------------------------

-- | Recognise a CCC morphism as an arith body over `sh`.
--
-- The IR's codomain is left fully generic so that Agda's case tree
-- only ever dispatches on the morphism's CONSTRUCTOR; we never
-- pin the codomain to `Int` or `Int * Int` from outside. SigOp
-- arithmetic ops are identified by `name` (string compare), which
-- carries enough information without forcing index unification.
{-# TERMINATING #-}
recognise-body : (sh : InputShape) → ∀ {A B} → IR A B → Maybe (MArithIR sh)

-- Binary-op SigOp ∘ ⟨_,_⟩ — pattern-matches three constructors deep.
recognise-body sh (SigOp si ∘ ⟨ a , b ⟩ _) with name si ≟ "arith.add.int"
... | yes _  with recognise-body sh a | recognise-body sh b
...   | just ra | just rb = just (aadd ra rb)
...   | just _  | nothing = nothing
...   | nothing | _       = nothing
recognise-body sh (SigOp si ∘ ⟨ a , b ⟩ _) | no _ with name si ≟ "arith.sub.int"
...   | yes _ with recognise-body sh a | recognise-body sh b
...     | just ra | just rb = just (asub ra rb)
...     | just _  | nothing = nothing
...     | nothing | _       = nothing
recognise-body sh (SigOp si ∘ ⟨ a , b ⟩ _) | no _ | no _ with name si ≟ "arith.mul.int"
...     | yes _ with recognise-body sh a | recognise-body sh b
...       | just ra | just rb = just (amul ra rb)
...       | just _  | nothing = nothing
...       | nothing | _       = nothing
recognise-body sh (SigOp si ∘ ⟨ a , b ⟩ _) | no _ | no _ | no _ = nothing

-- Unary-op SigOp ∘ e — `arith.neg.int`.
recognise-body sh (SigOp si ∘ e) with name si ≟ "arith.neg.int"
... | yes _ with recognise-body sh e
...   | just r  = just (aneg r)
...   | nothing = nothing
recognise-body sh (SigOp si ∘ e) | no _ = nothing

-- Literal: `const fits-int z _ ∘ rhs` where `rhs` is `terminal`
-- is the surface elaborator's intLit shape. We test rhs via a
-- Bool helper to keep the case-tree of `recognise-body` from
-- forcing an intermediate `Unit` type (which collides with
-- `out-μ`'s codomain unification).
recognise-body sh (const fits-int z _ ∘ rhs) with is-terminal? rhs
  where
    is-terminal? : ∀ {X Y} → IR X Y → Bool
    is-terminal? terminal = true
    is-terminal? _        = false
... | true  = just (alit z)
... | false = nothing
recognise-body sh (const fits-float _ _ ∘ _) = nothing

-- Otherwise: try projection-chain.
recognise-body sh other with recognise-path other
... | just p  = just (ainput p)
... | nothing = nothing

------------------------------------------------------------------------
-- Block-level entry
------------------------------------------------------------------------

-- | Top-level entry. The caller (a higher-level extraction pass)
-- strips enclosing `curry` layers off the source lambda and
-- supplies the resulting `InputShape` plus the body IR.
recognise : (sh : InputShape) → ∀ {A B} → IR A B → Maybe ArithBlock
recognise sh ir with recognise-body sh ir
... | just body = just (mk-block sh body)
... | nothing   = nothing
