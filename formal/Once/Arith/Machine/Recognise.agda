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

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Integer using (ℤ; +_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type using (Type; Unit; Int)
open import Once.IR
open import Once.SigOp.Info using (SigOpInfo; name; sem; SigOpSem; primV)
open import Once.Arith.Prim using (p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f)
open import Once.IRTy using (⌊_⌋)
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
-- D163: recognition must see terms UP TO THE CCC LAWS, because the elaborator
-- no longer hands it normal forms. QTT (plan 0.86) wraps every operand in a
-- usage restriction — `envˡ` / `envʳ`, i.e. `restrictEnv`, which is `fst` where
-- a variable is dropped and `⟨ … ∘ fst , snd ⟩` where it is kept. That pair is
-- not a projection, so the old `recognise-path` returned `nothing` for every
-- arith operand and NO arith block was ever built again. The bare
-- `arith.<op>.int` SigOp then reached the emitter as a call to a symbol nothing
-- defines: 19 exit tests and 119 cabal tests, all `undefined reference`.
--
-- The fix is PRODUCT BETA — `fst ∘ ⟨a,b⟩ ≡ a`, `snd ∘ ⟨a,b⟩ ≡ b` — applied
-- while walking, so an environment reshuffle collapses back to the projection
-- it denotes. `recognise-path-through` carries the path accumulated SO FAR into
-- the morphism being applied, which is what lets it choose a component: a pair
-- consumes one step and recurses into that side. Its indices are free, the
-- `recognise-binop` trick (a pinned product index is unification-stuck).
-- the two shapes of an operator's operands
binop : ∀ {X Y : Set} → (X → X → Y) → Maybe (X × X) → Maybe Y
binop k (just (a , b)) = just (k a b)
binop k nothing        = nothing

unop : ∀ {X Y : Set} → (X → Y) → Maybe X → Maybe Y
unop k (just a) = just (k a)
unop k nothing  = nothing

-- ENVIRONMENT PLUMBING: projections, pairing, `terminal` and their
-- composites. Its meaning is a value and no event, so a literal may absorb it.
plumbing? : ∀ {X Y} → IR X Y → Bool
plumbing? id          = true
plumbing? fst         = true
plumbing? snd         = true
plumbing? terminal    = true
plumbing? ⟨ f , g ⟩   = plumbing? f ∧ plumbing? g
plumbing? (f ∘ g)     = plumbing? f ∧ plumbing? g
{-# CATCHALL #-}
plumbing? _           = false

-- A literal's right-hand side: `terminal`, after plumbing.
is-terminal? : ∀ {X Y} → IR X Y → Bool
is-terminal? terminal       = true
is-terminal? (terminal ∘ g) = plumbing? g
{-# CATCHALL #-}
is-terminal? _              = false

recognise-path         : ∀ {A B} → IR A B → Maybe InputPath
recognise-path-through : ∀ {A B} → IR A B → InputPath → Maybe InputPath
pair-path              : ∀ {A B} → Bool → IR A B → InputPath → Maybe InputPath

-- `recognise-path-through m p` is the path of `p ∘ m` — apply `m`, then follow
-- `p`. Everything is one recursion on that, which is what makes the pair case
-- expressible: a projection step arriving at `⟨a,b⟩` SELECTS a component
-- instead of extending the path.
recognise-path m = recognise-path-through m []

recognise-path-through id  p = just p
recognise-path-through fst p = just (Fst ∷ p)
recognise-path-through snd p = just (Snd ∷ p)
-- product beta: `fst ∘ ⟨a,b⟩ ≡ a`, `snd ∘ ⟨a,b⟩ ≡ b`. This is the case QTT's
-- `restrictEnv` needs — its "variable kept" shape is exactly `⟨ … ∘ fst , snd ⟩`.
-- A pair is navigated only when the component NOT taken is plumbing: its
-- meaning is a value and no event, so reading through the pair drops nothing.
recognise-path-through (⟨ a , b ⟩) (Fst ∷ p) = pair-path (plumbing? b) a p
recognise-path-through (⟨ a , b ⟩) (Snd ∷ p) = pair-path (plumbing? a) b p
-- landing ON the pair: a product, not an `Int` leaf.
recognise-path-through (⟨ a , b ⟩) []        = nothing
-- `p ∘ (f ∘ g)` = apply g, then f, then p — so `f` consumes `p` and `g`
-- consumes the result. (`f` may itself be a pair; that is why the recursion
-- goes through here rather than through `recognise-path`.)
recognise-path-through (f ∘ g) p with recognise-path-through f p
... | just pf = recognise-path-through g pf
... | nothing = nothing
recognise-path-through _ _ = nothing

pair-path true  m p = recognise-path-through m p
pair-path false m p = nothing

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
-- D255: `SigOp si ∘ e` is an arithmetic op when its semantics IS one — the
-- compiler's primitive (`primV`), whose meaning is fixed by it — not when its
-- name looks like one.
recognise-prim : (sh : InputShape) → ∀ {X Y A} → SigOpSem X Y → IR A ⌊ X ⌋ → Maybe (MArithIR sh NInt)
binop-at       : (sh : InputShape) → ∀ {X Y Z W} → Bool → IR Z X → IR Z Y → IR W Z
               → Maybe (MArithIR sh NInt × MArithIR sh NInt)
recognise-binop sh (⟨ a , b ⟩) with recognise-body sh a | recognise-body sh b
... | just ra | just rb = just (ra , rb)
... | _       | _       = nothing
-- D163: `⟨a,b⟩ ∘ h ≡ ⟨ a ∘ h , b ∘ h ⟩` — composition distributes over pairing.
-- QTT hands the operand pair an environment restriction `h`, and pushing it
-- into the components is what lets each one be recognised on its own.
-- …and only when `h` is plumbing: distributing runs `h` twice, which means
-- the same only when `h`'s meaning is a value and no event.
recognise-binop sh (⟨ a , b ⟩ ∘ h) = binop-at sh (plumbing? h) a b h
recognise-binop sh _ = nothing

binop-at sh true a b h with recognise-body sh (a ∘ h) | recognise-body sh (b ∘ h)
... | just ra | just rb = just (ra , rb)
... | _       | _       = nothing
binop-at sh false a b h = nothing

recognise-prim sh (primV p-add) e = binop aadd (recognise-binop sh e)
recognise-prim sh (primV p-sub) e = binop asub (recognise-binop sh e)
recognise-prim sh (primV p-mul) e = binop amul (recognise-binop sh e)
recognise-prim sh (primV p-div) e = binop adiv (recognise-binop sh e)
recognise-prim sh (primV p-mod) e = binop amod (recognise-binop sh e)
recognise-prim sh (primV p-neg) e = unop aneg (recognise-body sh e)
{-# CATCHALL #-}
recognise-prim sh _             e = nothing

-- Binary/unary-op `SigOp si ∘ e` — dispatch on `name si`; `e` stays GENERIC so
-- the pair operand is recognised by `recognise-binop` (no stuck product index).
-- D163: RE-ASSOCIATE FIRST. `∘` is a constructor, so `(f ∘ g) ∘ h` is a
-- different TERM from `f ∘ (g ∘ h)` even though the CCC law identifies them,
-- and every clause below matches on the right-nested form. QTT (plan 0.86)
-- composes a usage restriction onto each operand, and `effApp` composes
-- another on top, so operands arrive left-nested to arbitrary depth —
-- `((SigOp fdiv ∘ ⟨…⟩) ∘ envˡ) ∘ envʳ`. One clause, applied repeatedly,
-- normalises all of it; it strictly reduces left-nesting, so it terminates.
recognise-body sh ((f ∘ g) ∘ h) = recognise-body sh (f ∘ (g ∘ h))

recognise-body sh (SigOp si ∘ e) = recognise-prim sh (sem si) e


-- Literal: `const fits-int z _ ∘ rhs` where `rhs` is `terminal`
-- is the surface elaborator's intLit shape. We test rhs via a
-- Bool helper to keep the case-tree of `recognise-body` from
-- forcing an intermediate `Unit` type (which collides with
-- `out-μ`'s codomain unification).
-- D163: `terminal ∘ h` IS `terminal` when `h` is environment plumbing (its
-- meaning is a value and no event; in the Kleisli meaning terminality holds
-- only for such an `h`). QTT's `envʳ` composes one on: a literal operand
-- arrives as `const v ∘ (terminal ∘ envʳ)`, and refusing it here is what
-- stopped `alit` being built. An arbitrary `h` is refused: lifting would drop
-- its events.
recognise-body sh (const fits-int v ∘ rhs) with is-terminal? rhs
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
recognise-prim-float : (sh : InputShape) → ∀ {X Y A} → SigOpSem X Y → IR A ⌊ X ⌋ → Maybe (MArithIR sh NFloat)
binop-at-float       : (sh : InputShape) → ∀ {X Y Z W} → Bool → IR Z X → IR Z Y → IR W Z
                     → Maybe (MArithIR sh NFloat × MArithIR sh NFloat)
recognise-binop-float sh (⟨ a , b ⟩) with recognise-body-float sh a | recognise-body-float sh b
... | just ra | just rb = just (ra , rb)
... | _       | _       = nothing
-- D163: distribution, the float twin. See the int version.
recognise-binop-float sh (⟨ a , b ⟩ ∘ h) = binop-at-float sh (plumbing? h) a b h
recognise-binop-float sh _ = nothing

binop-at-float sh true a b h with recognise-body-float sh (a ∘ h) | recognise-body-float sh (b ∘ h)
... | just ra | just rb = just (ra , rb)
... | _       | _       = nothing
binop-at-float sh false a b h = nothing

recognise-prim-float sh (primV p-fadd) e = binop aadd (recognise-binop-float sh e)
recognise-prim-float sh (primV p-fsub) e = binop asub (recognise-binop-float sh e)
recognise-prim-float sh (primV p-fmul) e = binop amul (recognise-binop-float sh e)
recognise-prim-float sh (primV p-fdiv) e = binop adiv (recognise-binop-float sh e)
recognise-prim-float sh (primV p-i2f)  e = unop ai2f (recognise-body sh e)
{-# CATCHALL #-}
recognise-prim-float sh _              e = nothing

-- D163: re-associate first — the float twin. See the int version.
recognise-body-float sh ((f ∘ g) ∘ h) = recognise-body-float sh (f ∘ (g ∘ h))

recognise-body-float sh (SigOp si ∘ e) = recognise-prim-float sh (sem si) e


-- A float LITERAL. The payload stays a `Decimal` — the one rounding happens at
-- the backend, at the target's format (D117).
-- D163: as the int twin — `terminal` after plumbing only.
recognise-body-float sh (const fits-float d ∘ rhs) with is-terminal? rhs
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
