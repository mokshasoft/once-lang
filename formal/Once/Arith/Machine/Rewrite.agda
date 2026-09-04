-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.Rewrite
--
-- Plan 0.20 Phase G — the IR-rewrite pass.
--
-- The elaborator emits per-op arith SigOps (`arith.add.int`, etc.).
-- For codegen we want each maximal arith subtree replaced by a single
-- `arith.block.<digest>` SigOp whose body is the recognised
-- `MArithIR`. This module walks an `IR A B` top-down, tries
-- recognition at every node, and lifts a subtree into a block SigOp
-- whenever recognition succeeds AND the recognised IR contains at
-- least one arithmetic operation. Pure literals / projections are
-- left untouched; the existing `const` / `fst` / `snd` codegen
-- handles them better than a one-instruction block.
--
-- The pass also returns the list of `ArithBlock`s it produced.
-- Codegen walks that list to emit each block's body as a standalone
-- assembly subroutine (`once_arith.block.<digest>:`) after the main
-- program text.
------------------------------------------------------------------------

module Once.Arith.Machine.Rewrite where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type using (Type; Unit; Int; _*_; _+_; _⇒[_]_)
open import Once.IR
import Once.IRTy as II
open import Once.SigOp.Info using (SigOpInfo)

open import Once.Arith.Machine.AbsState
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair)
-- PLAN 0.75 F4: the abstract-machine compile path is pinned at `NInt`, and
-- that restriction is STATED rather than assumed. Its instruction set
-- (`add-rrr`, `div-rrr`, …) is integer-register shaped, so a float block has
-- no lowering here yet; saying so in the type means the gate sees the gap
-- instead of a float tree silently taking the integer path.
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f;
         numtype-as-type;
         ArithBlock; mk-block; shape-as-type)
open Once.Arith.Machine.IR.ArithBlock using (block-shape; block-body)
open import Once.Arith.Machine.Recognise using (recognise; recognise-body; recognise-body-float)
open import Once.Arith.SigOp.Block using (block-info)

------------------------------------------------------------------------
-- Type → InputShape, with definitional bridge back to Type
------------------------------------------------------------------------

-- | If `A` is a tree of `Unit`, `Int`, and `_*_`, return the matching
-- `InputShape` together with the proof `A ≡ shape-as-type sh`. The
-- proof lets us coerce a recognised block's SigOp (whose domain is
-- `shape-as-type sh`) back into the IR's domain `A`.
-- Plan 0.52 M2: `IR` objects are `IRTy`, so this walks the ERASED domain and
-- returns `A ≡ ⌊ shape-as-type sh ⌋` (`⌊_⌋` commutes with Unit/Int/`_*_`).
shape-of : (A : II.IRTy) → Maybe (Σ[ sh ∈ InputShape ] (A ≡ ⌊ shape-as-type sh ⌋))
shape-of II.Unit                           = just (shape-unit , refl)
shape-of II.Int                            = just (shape-int  , refl)
shape-of (l II.* r)                        with shape-of l | shape-of r
... | just (sl , refl) | just (sr , refl)  = just (shape-pair sl sr , refl)
... | _                | _                 = nothing
shape-of _                                 = nothing

------------------------------------------------------------------------
-- "Worth wrapping" predicate
------------------------------------------------------------------------

-- | True for arith trees containing at least one arithmetic operation
-- (`aadd` / `asub` / `amul` / `aneg`). Pure leaves (`alit` / `ainput`)
-- aren't lifted; the existing `const` / projection codegen produces
-- tighter code.
-- PLAN 0.75 F4: kind-polymorphic. "Does this tree contain an operation?" is
-- about the tree's SHAPE — a bare leaf is not worth lifting into its own
-- symbol at either kind. `ai2f` counts as an op: `1 + 1.5`'s widening is real
-- work the block should own.
has-op : ∀ {sh n} → MArithIR sh n → Bool
has-op (alit _)    = false
has-op (aflit _)   = false
has-op (ai2f _)    = true
has-op (ainput _)  = false
has-op (aadd _ _)  = true
has-op (asub _ _)  = true
has-op (amul _ _)  = true
has-op (adiv _ _)  = true
has-op (amod _ _)  = true
has-op (aneg _)    = true

------------------------------------------------------------------------
-- Block-as-IR construction
------------------------------------------------------------------------

-- | Build the `IR A Int` whose runtime behaviour is the recognised
-- arith block. The domain `A` is whatever `shape-of` returned a
-- shape for; the body is the recognised `MArithIR sh NInt`.
block-as-ir : ∀ {A sh n} → A ≡ ⌊ shape-as-type sh ⌋ → MArithIR sh n
            → IR A ⌊ numtype-as-type n ⌋
-- D143: the codomain is written out. `⌊_⌋` interprets the quantity now, so it
-- is no longer structurally invertible and Agda cannot solve `⌊ ? ⌋ = ⌊ … ⌋`.
block-as-ir {A} {sh} {n} eq body =
  subst (λ T → IR T ⌊ numtype-as-type n ⌋) (sym eq) (SigOp (block-info body))

------------------------------------------------------------------------
-- Recognition attempt parameterised on the IR's domain
------------------------------------------------------------------------

try-lift : ∀ {A B} → IR A B → Maybe (IR A B × ArithBlock)
try-lift {A} {II.Int} ir                           with shape-of A
... | nothing                                       = nothing
... | just (sh , eq)                                with recognise-body sh ir
...   | nothing                                     = nothing
...   | just body                                   with has-op body
...     | false                                     = nothing
...     | true                                      =
            just (block-as-ir eq body , mk-block sh NInt body)
-- PLAN 0.75 F4 step 2: a FLOAT codomain lifts too. The codomain is what picks
-- the kind — a block returning `Float` is a float block — so recognition never
-- has to guess, and `recognise-body-float` matches the `.float` SigOp names
-- that the elaborator emits.
--
-- This is the clause that makes float blocks REACHABLE, and it lands after the
-- lowering it depends on, not before: the emitters render real `addsd` /
-- `fadd.d`, and seven of the eight float instructions have a discharged
-- correspondence.
try-lift {A} {II.Float} ir                         with shape-of A
... | nothing                                       = nothing
... | just (sh , eq)                                with recognise-body-float sh ir
...   | nothing                                     = nothing
...   | just body                                   with has-op body
...     | false                                     = nothing
...     | true                                      =
            just (block-as-ir eq body , mk-block sh NFloat body)
-- Any other codomain: never lift.
try-lift {_} {_} _ = nothing

------------------------------------------------------------------------
-- The rewrite pass
------------------------------------------------------------------------

-- | Walk the IR, lifting maximal arith subtrees. Returns the rewritten
-- IR plus the list of `ArithBlock`s discovered (in document order;
-- caller may dedup by digest).
--
-- The walk attempts `try-lift` at every node first. If the lift
-- succeeds, the entire subtree becomes one block SigOp and recursion
-- stops there. Otherwise the walk recurses into the IR's children
-- per-constructor.
{-# TERMINATING #-}
rewrite-ir : ∀ {A B} → IR A B → IR A B × List ArithBlock
rewrite-ir ir with try-lift ir
... | just (ir' , blk) = ir' , (blk ∷ [])
... | nothing          = walk ir
  where
    walk : ∀ {A B} → IR A B → IR A B × List ArithBlock
    -- D062: arith-block lifting descends into a Fuse/Hylo natural transform's
    -- constant-leaf IRs.
    walk-nt : ∀ {G F} → NatTr G F → NatTr G F × List ArithBlock
    walk id                = id , []
    walk (g ∘ f)           =
      let (g' , bg) = rewrite-ir g
          (f' , bf) = rewrite-ir f
      in (g' ∘ f') , (bg ++ bf)
    walk fst               = fst , []
    walk snd               = snd , []
    walk (⟨ f , g ⟩ m)     =
      let (f' , bf) = rewrite-ir f
          (g' , bg) = rewrite-ir g
      in ⟨ f' , g' ⟩ m , (bf ++ bg)
    walk (inl m)           = inl m , []
    walk (inr m)           = inr m , []
    walk (case f g)        =
      let (f' , bf) = rewrite-ir f
          (g' , bg) = rewrite-ir g
      in case f' g' , (bf ++ bg)
    walk terminal          = terminal , []
    walk initial           = initial , []
    walk (curry f m)       =
      let (f' , bf) = rewrite-ir f
      in (curry f' m) , bf
    walk apply             = apply , []
    walk (In w m)          = In w m , []
    walk (out-μ w)         = out-μ w , []
    walk (Cata w f)        =
      let (f' , bf) = rewrite-ir f
      in Cata w f' , bf
    walk (Para w f)        =
      let (f' , bf) = rewrite-ir f
      in Para w f' , bf
    walk (Out w)           = Out w , []
    walk (in-ν w m)        = in-ν w m , []
    walk (Ana w f)         =
      let (f' , bf) = rewrite-ir f
      in Ana w f' , bf
    walk (Hylo w₁ w₂ f g)  =
      let (f' , bf) = rewrite-ir f
          (g' , bg) = walk-nt g
      in Hylo w₁ w₂ f' g' , (bf ++ bg)
    walk (Fuse w₁ w₂ f g)  =
      let (f' , bf) = rewrite-ir f
          (g' , bg) = walk-nt g
      in Fuse w₁ w₂ f' g' , (bf ++ bg)
    walk (free-heap r)     = free-heap r , []
    walk (const p v)   = const p v , []
    walk (SigOp si)        = SigOp si , []

    walk-nt ntId         = ntId , []
    walk-nt (ntK ir)     = let (ir' , b) = rewrite-ir ir in ntK ir' , b
    walk-nt (ntFst t)    = let (t' , b) = walk-nt t in ntFst t' , b
    walk-nt (ntSnd t)    = let (t' , b) = walk-nt t in ntSnd t' , b
    walk-nt (ntCase t u) = let (t' , bt) = walk-nt t
                               (u' , bu) = walk-nt u in ntCase t' u' , (bt ++ bu)
    walk-nt (ntInl t)    = let (t' , b) = walk-nt t in ntInl t' , b
    walk-nt (ntInr t)    = let (t' , b) = walk-nt t in ntInr t' , b
    walk-nt (ntPair t u) = let (t' , bt) = walk-nt t
                               (u' , bu) = walk-nt u in ntPair t' u' , (bt ++ bu)
