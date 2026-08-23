-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.BlockSemBridge  (Plan 0.54 rung B / B2.3 piece 5)
--
-- Spec alignment between the two arith value evaluators:
--   * `eval-arith-W` (WordSem, over the ℤ-valued input tree `⟦ sh ⟧S`) — the
--     value `block-correct` establishes on the abstract machine.
--   * `block-semM`   (Block, over the Word-valued input tree
--     `M.⟦ shape-as-type sh ⟧`) — the value the FLAT machine computes (rung A)
--     and the concrete `val` produces.
-- They differ ONLY in the input representation (ℤ-tree vs Word-tree), so the
-- bridge is `toWord` (apply `fromℤ` at the int leaves) + a structural induction.
-- At `bits = 64` the two evaluators use the SAME `Word64` operations.
--
-- This is the piece that lets `block-correct`'s value transfer to the flat/
-- concrete side (B2.3): the arith result the concrete machine holds equals
-- `block-semM input`, which is what rung A's `pure-sigop-output = semM` expects.
------------------------------------------------------------------------

module Once.Arith.SigOp.BlockSemBridge where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Once.Arith.Machine.Shape
  using (InputShape; shape-unit; shape-int; shape-pair; ⟦_⟧S; InputPath; Side; Fst; Snd; project)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; adiv; amod; aneg; shape-as-type)
open import Once.Arith.Machine.WordSem using (module Sem)

import Once.Word as OnceWord
open import Once.Float.Dyadic using (Dyadic)
import Once.Semantics.Value OnceWord.Carrier OnceWord.Carrier as M
open import Once.Arith.SigOp.Block using (block-semM; projectM; maybe-zeroM)

open import Once.Target.Arch using (TargetNum; int-bits)

------------------------------------------------------------------------
-- PLAN 0.74 J5 — parameterised by the TARGET, because every definition
-- below reads a width and there were TWO bakes here, not one:
--
--     open Sem 64                    -- the ℤ→Word arith evaluator
--     module W = OnceWord.Word64     -- the input-tree bridge
--
-- `eval≡semM` is the statement that those two agree, so baking the same 64
-- into both made it agree with itself. On x86-32 both sides were wrong
-- together, which is exactly why nothing was red.
------------------------------------------------------------------------

module _ (tn : TargetNum) where

  open Sem (int-bits tn) using (eval-arith-W)
  module W = OnceWord.Width (int-bits tn)

  ------------------------------------------------------------------------
  -- The input representation bridge: ℤ-tree → Word-tree (fromℤ at leaves).
  ------------------------------------------------------------------------

  toWord : ∀ (sh : InputShape) → ⟦ sh ⟧S → M.⟦ shape-as-type sh ⟧
  toWord shape-unit       tt      = tt
  toWord shape-int        z       = W.fromℤ z
  toWord (shape-pair l r) (x , y) = toWord l x , toWord r y

  ------------------------------------------------------------------------
  -- Leaf commute: projecting the Word-tree = mapping fromℤ over the ℤ-project.
  ------------------------------------------------------------------------

  project-commute : ∀ (sh : InputShape) (p : InputPath) (env : ⟦ sh ⟧S)
                  → projectM sh p (toWord sh env) ≡ mapMaybe W.fromℤ (project sh p env)
  project-commute shape-unit       p         env       = refl
  project-commute shape-int        []        z         = refl
  project-commute shape-int        (_ ∷ _)   z         = refl
  project-commute (shape-pair l r) []        (x , y)   = refl
  project-commute (shape-pair l r) (Fst ∷ p) (x , y)   = project-commute l p x
  project-commute (shape-pair l r) (Snd ∷ p) (x , y)   = project-commute r p y

  ------------------------------------------------------------------------
  -- Piece 5: the two evaluators agree, modulo the input bridge.
  ------------------------------------------------------------------------

  -- Leaf: `eval-arith-W (ainput p)` = `maybe-zeroM (mapMaybe fromℤ (project …))`.
  ainput-leaf : ∀ (sh : InputShape) (p : InputPath) (env : ⟦ sh ⟧S)
              → eval-arith-W {sh} (ainput p) env ≡ maybe-zeroM (mapMaybe W.fromℤ (project sh p env))
  -- The `nothing` case USED TO BE `refl` and no longer is, which is a real
  -- consequence of un-baking the width: `fromℤ (+ 0)` is `0 % 2^bits`, and
  -- that computes to `0` only when `bits` is a literal. At an abstract width
  -- it needs the lemma. Every `refl` that quietly depended on the width being
  -- 64 shows up exactly like this.
  ainput-leaf sh p env with project sh p env
  ... | just z  = refl
  ... | nothing = W.fromℤ-0

  eval≡semM : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S)
            → eval-arith-W e env ≡ block-semM e tn (toWord sh env)
  eval≡semM (alit z)   env = refl
  eval≡semM {sh} (ainput p) env =
    trans (ainput-leaf sh p env)
          (cong maybe-zeroM (sym (project-commute sh p env)))
  eval≡semM (aadd a b) env = cong₂ W._⊕_  (eval≡semM a env) (eval≡semM b env)
  eval≡semM (asub a b) env = cong₂ W._⊖_  (eval≡semM a env) (eval≡semM b env)
  eval≡semM (amul a b) env = cong₂ W._⊗_  (eval≡semM a env) (eval≡semM b env)
  eval≡semM (adiv a b) env = cong₂ W._/ˢ_ (eval≡semM a env) (eval≡semM b env)
  eval≡semM (amod a b) env = cong₂ W._%ˢ_ (eval≡semM a env) (eval≡semM b env)
  eval≡semM (aneg a)   env = cong  W.⊝_   (eval≡semM a env)
