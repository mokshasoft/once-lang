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
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair; ⟦_⟧S; InputPath; Side; Fst; Snd; project; projectF;
         Path; here-int; here-flt; go-fst; go-snd; readLeaf; ⌊_⌋ᴾ)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f;
         numtype-as-type; shape-as-type)
open import Once.Arith.Machine.WordSem using (module Sem)
open import Once.Arith.Type using (NumType; NInt; NFloat)
import Once.Float.Arith as FA

import Once.Word as OnceWord
open import Once.Float.Dyadic using (Dyadic)
import Once.Semantics.Value OnceWord.Carrier OnceWord.Carrier as M
open import Once.Arith.SigOp.Block using (block-semM; projectM; maybe-zeroM; readLeafM)

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

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

  open Sem (int-bits tn) (float-format tn) using (eval-arith-W)
  F = float-format tn
  module W = OnceWord.Width (int-bits tn)

  ------------------------------------------------------------------------
  -- The input representation bridge: ℤ-tree → Word-tree (fromℤ at leaves).
  ------------------------------------------------------------------------

  toWord : ∀ (sh : InputShape) → ⟦ sh ⟧S → M.⟦ shape-as-type sh ⟧
  toWord shape-unit       tt      = tt
  toWord shape-int        z       = W.fromℤ z
  -- PLAN 0.75 F4: the IDENTITY on a float leaf. `⟦ shape-float ⟧S` is already
  -- the bit pattern and `M.⟦ Float ⟧` is the same `Carrier` — there is no
  -- spec-level float value to narrow from, which is D113 showing through at
  -- the one place the `Int` leaf needs `fromℤ`.
  toWord shape-float      w       = w
  toWord (shape-pair l r) (x , y) = toWord l x , toWord r y

  ------------------------------------------------------------------------
  -- Leaf commute: projecting the Word-tree = mapping fromℤ over the ℤ-project.
  ------------------------------------------------------------------------

  -- STATED AT `NInt`, and it has to be: this is the ℤ-spec bridge, `project`
  -- only ever finds `Int` leaves, and there is no ℤ spec for a float to bridge
  -- to. With a kind-blind `projectM` the statement would be FALSE at a float
  -- leaf — `just w` on the left, `nothing` on the right — which is how the
  -- kind parameter earned its place.
  project-commute : ∀ (sh : InputShape) (p : InputPath) (env : ⟦ sh ⟧S)
                  → projectM NInt sh p (toWord sh env) ≡ mapMaybe W.fromℤ (project sh p env)
  project-commute shape-unit       p         env       = refl
  project-commute shape-int        []        z         = refl
  project-commute shape-int        (_ ∷ _)   z         = refl
  project-commute shape-float      p         w         = refl
  project-commute (shape-pair l r) []        (x , y)   = refl
  project-commute (shape-pair l r) (Fst ∷ p) (x , y)   = project-commute l p x
  project-commute (shape-pair l r) (Snd ∷ p) (x , y)   = project-commute r p y

  ------------------------------------------------------------------------
  -- Piece 5: the two evaluators agree, modulo the input bridge.
  ------------------------------------------------------------------------

  -- PLAN 0.75 F4: the FLOAT leaf's commute, and it is `refl` at every shape —
  -- `toWord` is the identity on a float leaf, because there is no spec-level
  -- float value to narrow from (D113). The `Int` twin above needs `fromℤ`
  -- precisely where this one needs nothing.
  projectF-commute : ∀ (sh : InputShape) (p : InputPath) (env : ⟦ sh ⟧S)
                   → projectM NFloat sh p (toWord sh env) ≡ projectF sh p env
  projectF-commute shape-unit       p         env     = refl
  projectF-commute shape-int        p         env     = refl
  projectF-commute shape-float      []        w       = refl
  projectF-commute shape-float      (_ ∷ _)   w       = refl
  projectF-commute (shape-pair l r) []        (x , y) = refl
  projectF-commute (shape-pair l r) (Fst ∷ p) (x , y) = projectF-commute l p x
  projectF-commute (shape-pair l r) (Snd ∷ p) (x , y) = projectF-commute r p y

  -- PLAN 0.75 F4: kind-indexed, and the FLOAT clauses are structurally the
  -- same `cong`s. That is the point rather than a coincidence: both evaluators
  -- call `Once.Float.Arith`'s operations at the SAME format — `F` here is
  -- literally `float-format tn` — so there is nothing to reconcile, exactly as
  -- there is nothing to reconcile between two `⊕`s at the same width.
  -- With both `ainput` reads TOTAL, the four leaf lemmas above collapse to one
  -- induction on the typed path — and it is `refl` at every leaf. The old
  -- lemmas had to reconcile two `Maybe`s and their two invented defaults;
  -- there are no defaults left to reconcile.
  readLeaf-commute : ∀ {sh} (p : Path sh NInt) (env : ⟦ sh ⟧S)
                   → readLeafM p (toWord sh env) ≡ W.fromℤ (readLeaf p env)
  readLeaf-commute here-int   z       = refl
  readLeaf-commute (go-fst p) (x , y) = readLeaf-commute p x
  readLeaf-commute (go-snd p) (x , y) = readLeaf-commute p y

  readLeafF-commute : ∀ {sh} (p : Path sh NFloat) (env : ⟦ sh ⟧S)
                    → readLeafM p (toWord sh env) ≡ readLeaf p env
  readLeafF-commute here-flt   w       = refl
  readLeafF-commute (go-fst p) (x , y) = readLeafF-commute p x
  readLeafF-commute (go-snd p) (x , y) = readLeafF-commute p y

  eval≡semM : ∀ {sh n} (e : MArithIR sh n) (env : ⟦ sh ⟧S)
            → eval-arith-W e env ≡ block-semM e tn (toWord sh env)
  eval≡semM (alit z)   env = refl
  eval≡semM (aflit d)  env = refl
  eval≡semM {sh} {NInt}   (ainput p) env = sym (readLeaf-commute p env)
  eval≡semM {sh} {NFloat} (ainput p) env = sym (readLeafF-commute p env)
  eval≡semM {n = NInt}   (aadd a b) env = cong₂ W._⊕_  (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NFloat} (aadd a b) env = cong₂ (FA.fadd F) (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NInt}   (asub a b) env = cong₂ W._⊖_  (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NFloat} (asub a b) env = cong₂ (FA.fsub F) (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NInt}   (amul a b) env = cong₂ W._⊗_  (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NFloat} (amul a b) env = cong₂ (FA.fmul F) (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NInt}   (adiv a b) env = cong₂ W._/ˢ_ (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NFloat} (adiv a b) env = cong₂ (FA.fdiv F) (eval≡semM a env) (eval≡semM b env)
  eval≡semM (amod a b) env = cong₂ W._%ˢ_ (eval≡semM a env) (eval≡semM b env)
  eval≡semM {n = NInt}   (aneg a)   env = cong  W.⊝_   (eval≡semM a env)
  eval≡semM {n = NFloat} (aneg a)   env = cong  (FA.fneg F) (eval≡semM a env)
  eval≡semM (ai2f a)   env = cong (λ w → FA.i2f F (W.toℤ w)) (eval≡semM a env)
