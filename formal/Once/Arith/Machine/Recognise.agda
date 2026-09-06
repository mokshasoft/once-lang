-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Integer using (ℤ; +_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type using (Type; Unit; Int)
open import Once.IR
open import Once.SigOp.Info using (SigOpInfo; name)
open import Once.CanonicalName using (bare; _≟ᶜ_)

open import Once.Arith.Machine.AbsState
  using (InputShape; shape-int; shape-float; shape-pair; InputPath;
         Side; Fst; Snd; Path; typePath?)
-- PLAN 0.75 F4: the abstract-machine compile path is pinned at `NInt`, and
-- that restriction is STATED rather than assumed. Its instruction set
-- (`add-rrr`, `div-rrr`, …) is integer-register shaped, so a float block has
-- no lowering here yet; saying so in the type means the gate sees the gap
-- instead of a float tree silently taking the integer path.
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f;
         numtype-as-type; ArithBlock;
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
recognise-body : (sh : InputShape) → ∀ {A B} → IR A B → Maybe (MArithIR sh NInt)
-- `recognise-binop` recognises the two operands of a binary op. Its codomain
-- `Y` is a FREE variable, so matching `⟨_,_⟩` instantiates `Y := B * C` freely —
-- unlike matching the pair directly under `SigOp _ ∘ _`, where the middle object
-- is the SigOp's ERASED domain `⌊Dom⌋` and `⌊Dom⌋ ≟ B * C` is unification-stuck
-- (`⌊_⌋` non-invertible). Plan 0.52 M2.
recognise-binop : (sh : InputShape) → ∀ {X Y} → IR X Y → Maybe (MArithIR sh NInt × MArithIR sh NInt)
recognise-binop sh (⟨ a , b ⟩) with recognise-body sh a | recognise-body sh b
... | just ra | just rb = just (ra , rb)
... | _       | _       = nothing
recognise-binop sh _ = nothing

-- Binary/unary-op `SigOp si ∘ e` — dispatch on `name si`; `e` stays GENERIC so
-- the pair operand is recognised by `recognise-binop` (no stuck product index).
recognise-body sh (SigOp si ∘ e) with name si ≟ᶜ bare "arith.add.int"
... | yes _ with recognise-binop sh e
...   | just (ra , rb) = just (aadd ra rb)
...   | nothing        = nothing
recognise-body sh (SigOp si ∘ e) | no _ with name si ≟ᶜ bare "arith.sub.int"
...   | yes _ with recognise-binop sh e
...     | just (ra , rb) = just (asub ra rb)
...     | nothing        = nothing
recognise-body sh (SigOp si ∘ e) | no _ | no _ with name si ≟ᶜ bare "arith.mul.int"
...     | yes _ with recognise-binop sh e
...       | just (ra , rb) = just (amul ra rb)
...       | nothing        = nothing
recognise-body sh (SigOp si ∘ e) | no _ | no _ | no _ with name si ≟ᶜ bare "arith.div.int"
...       | yes _ with recognise-binop sh e
...         | just (ra , rb) = just (adiv ra rb)
...         | nothing        = nothing
recognise-body sh (SigOp si ∘ e) | no _ | no _ | no _ | no _ with name si ≟ᶜ bare "arith.mod.int"
...         | yes _ with recognise-binop sh e
...           | just (ra , rb) = just (amod ra rb)
...           | nothing        = nothing
recognise-body sh (SigOp si ∘ e) | no _ | no _ | no _ | no _ | no _ with name si ≟ᶜ bare "arith.neg.int"
...           | yes _ with recognise-body sh e
...             | just r  = just (aneg r)
...             | nothing = nothing
recognise-body sh (SigOp si ∘ e) | no _ | no _ | no _ | no _ | no _ | no _ = nothing

-- Literal: `const fits-int z _ ∘ rhs` where `rhs` is `terminal`
-- is the surface elaborator's intLit shape. We test rhs via a
-- Bool helper to keep the case-tree of `recognise-body` from
-- forcing an intermediate `Unit` type (which collides with
-- `out-μ`'s codomain unification).
recognise-body sh (const fits-int v ∘ rhs) with is-terminal? rhs
  where
    is-terminal? : ∀ {X Y} → IR X Y → Bool
    is-terminal? terminal = true
    is-terminal? _        = false
-- D115: `const`'s payload is a `ℤ` now, and `alit` always took one, so the
-- `+ v` injection is gone. That injection was itself the symptom — it forced
-- every recognised literal to be non-negative, which is exactly the
-- restriction the absolute-value denotation was hiding.
... | true  = just (alit v)
... | false = nothing
recognise-body sh (const fits-float _ ∘ _) = nothing

-- Otherwise: try projection-chain. The chain gives an UNTYPED path; `typePath?`
-- establishes that it lands on an `Int` leaf before an `ainput` can be built.
-- Refusing is the point: a chain landing on a float leaf used to be recognised
-- and then evaluate to `0`.
recognise-body sh other with recognise-path other
... | just p  with typePath? sh NInt p
...   | just tp = just (ainput tp)
...   | nothing = nothing
recognise-body sh other | nothing = nothing


------------------------------------------------------------------------
-- FLOAT body recognition (plan 0.75 F4, step 2)
--
-- A SEPARATE function rather than a `NumType`-indexed one, and deliberately:
-- the integer chain above is proven and heavily `with`-structured, and giving
-- it an extra index would rewrite every continuation for no gain. The two are
-- MUTUALLY recursive in one place only — `arith.i2f`, D125's widening, which
-- is the single node where a float tree contains an integer one.
--
-- The SigOp names are what separate the kinds. `arith.add.int` and
-- `arith.add.float` are different instructions on every target, so matching by
-- name is exactly the right discrimination and no type index is needed.
------------------------------------------------------------------------

{-# TERMINATING #-}
recognise-body-float : (sh : InputShape) → ∀ {A B} → IR A B → Maybe (MArithIR sh NFloat)

recognise-binop-float : (sh : InputShape) → ∀ {X Y} → IR X Y
                      → Maybe (MArithIR sh NFloat × MArithIR sh NFloat)
recognise-binop-float sh (⟨ a , b ⟩) with recognise-body-float sh a | recognise-body-float sh b
... | just ra | just rb = just (ra , rb)
... | _       | _       = nothing
recognise-binop-float sh _ = nothing

recognise-body-float sh (SigOp si ∘ e) with name si ≟ᶜ bare "arith.add.float"
... | yes _ with recognise-binop-float sh e
...   | just (ra , rb) = just (aadd ra rb)
...   | nothing        = nothing
recognise-body-float sh (SigOp si ∘ e) | no _ with name si ≟ᶜ bare "arith.sub.float"
...   | yes _ with recognise-binop-float sh e
...     | just (ra , rb) = just (asub ra rb)
...     | nothing        = nothing
recognise-body-float sh (SigOp si ∘ e) | no _ | no _ with name si ≟ᶜ bare "arith.mul.float"
...     | yes _ with recognise-binop-float sh e
...       | just (ra , rb) = just (amul ra rb)
...       | nothing        = nothing
recognise-body-float sh (SigOp si ∘ e) | no _ | no _ | no _ with name si ≟ᶜ bare "arith.div.float"
...       | yes _ with recognise-binop-float sh e
...         | just (ra , rb) = just (adiv ra rb)
...         | nothing        = nothing
-- D125's widening: the operand is an INTEGER tree, so this is the one place
-- the two recognisers meet.
recognise-body-float sh (SigOp si ∘ e) | no _ | no _ | no _ | no _ with name si ≟ᶜ bare "arith.i2f"
...         | yes _ with recognise-body sh e
...           | just r  = just (ai2f r)
...           | nothing = nothing
recognise-body-float sh (SigOp si ∘ e) | no _ | no _ | no _ | no _ | no _ = nothing

-- A float LITERAL. The payload stays a `Decimal` — the one rounding happens at
-- the backend, at the target's format (D117).
recognise-body-float sh (const fits-float d ∘ rhs) with is-terminal-f? rhs
  where
    is-terminal-f? : ∀ {X Y} → IR X Y → Bool
    is-terminal-f? terminal = true
    is-terminal-f? _        = false
... | true  = just (aflit d)
... | false = nothing
recognise-body-float sh (const fits-int _ ∘ _) = nothing

-- The float twin, and the SAME refusal one type over: a chain landing on an
-- `Int` leaf is not a float input.
recognise-body-float sh other with recognise-path other
... | just p  with typePath? sh NFloat p
...   | just tp = just (ainput tp)
...   | nothing = nothing
recognise-body-float sh other | nothing = nothing

------------------------------------------------------------------------
-- Block-level entry
------------------------------------------------------------------------

-- | Top-level entry. The caller (a higher-level extraction pass)
-- strips enclosing `curry` layers off the source lambda and
-- supplies the resulting `InputShape` plus the body IR.
-- | Top-level entry, now taking the KIND the caller wants. `Once.Arith.Machine.
-- Rewrite` reads it off the morphism's CODOMAIN — a block returning `Int` is an
-- integer block and one returning `Float` is a float block — so recognition
-- never has to guess.
recognise : (sh : InputShape) (n : NumType) → ∀ {A B} → IR A B → Maybe ArithBlock
recognise sh NInt ir with recognise-body sh ir
... | just body = just (mk-block sh NInt body)
... | nothing   = nothing
recognise sh NFloat ir with recognise-body-float sh ir
... | just body = just (mk-block sh NFloat body)
... | nothing   = nothing
