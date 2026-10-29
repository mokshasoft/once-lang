-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Optimize.Examples — ONE PASS OF THE OPTIMIZER ON EACH RULE
-- (plans 0.39, 0.129).
--
-- Each example is a term whose one pass (`optimize-once`) fires the named
-- rule of `Once.Optimize`, checked by `refl`; the `Call`s are effects, so
-- the guard and the rules that keep an effect can be seen. That the result
-- has the input's trace is `OptimizePreserves.optimize-rel`; these say the
-- rule FIRES.
--
-- Elaborated programs reach some rules only (`compiler/test/OptimizeSpec.hs`
-- builds those from source). The rest are here only: `case h k ∘ inl/inr`
-- and `[inl, inr]` (the elaborator puts a distribution between a sum and its
-- `case`), `terminal ∘ f`, `g ∘ initial` and a `SigOp` out of `Void` (each
-- needs an effect under a dropped or `Void`-sourced term).
------------------------------------------------------------------------

module Once.Optimize.Examples where

open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.IR
open import Once.IRTy using (IRTy; Int; Unit; Void; _*_; _+_; fits-int)
open import Once.Spec.Name using (bare)
open import Once.Spec.Type using (b-Void; b-Unit) renaming (Void to VoidT; Unit to UnitT)
open import Once.SigOp.Info using (SigOpInfo; mk-info'; emitsV)
open import Once.Optimize using (optimize-once)

private
  -- an effect: a call
  eff : ∀ {A B} → IR A B
  eff = Call (bare "f")

  -- an event out of `Void`
  never : SigOpInfo VoidT UnitT
  never = mk-info' (bare "e") (emitsV refl) b-Void b-Unit

  one : IR Unit Int
  one = const fits-int (+ 1)

-- A morphism into `Unit` with no effect is `terminal`.
unit-target : optimize-once (fst {Unit} {Int}) ≡ terminal
unit-target = refl

-- A morphism out of `Void` is `initial`.
void-source : optimize-once (inl {Void} {Int}) ≡ initial
void-source = refl

-- The guard: an effect is never dropped (`fst ∘ ⟨g,h⟩` stays when `h` calls).
guard : optimize-once (fst ∘ ⟨ id {Int} , eff {Int} {Int} ⟩) ≡ fst ∘ ⟨ id , eff ⟩
guard = refl

-- id ∘ f = f
id-left : optimize-once (id ∘ fst {Int} {Int}) ≡ fst
id-left = refl

-- f ∘ id = f
id-right : optimize-once (inl {Int} {Int} ∘ id) ≡ inl
id-right = refl

-- …also after a projection that finds no pair (eta leaves `snd ∘ id` behind)
id-right-proj : optimize-once (snd {Int} {Int} ∘ id) ≡ snd
id-right-proj = refl

-- terminal ∘ f = terminal, f quiet once optimized (an effectful `case` arm it
-- never takes)
terminal-left : optimize-once (terminal ∘ (case (eff {Int} {Int}) id ∘ inr {Int} {Int})) ≡ terminal
terminal-left = refl

-- g ∘ initial = initial (an effectful `g`, so the whole is not `terminal`)
initial-right : optimize-once (eff {Int} {Unit} ∘ initial {Int}) ≡ initial
initial-right = refl

-- a SigOp out of `Void` is `initial` (it is an effect into `Unit`, so the
-- `Unit` rule keeps it for the structural one)
sigop-void : optimize-once (SigOp never) ≡ initial
sigop-void = refl

-- fst ∘ ⟨g,h⟩ = g
fst-pair : optimize-once (fst ∘ ⟨ snd {Int} {Int} , fst ⟩) ≡ snd
fst-pair = refl

-- snd ∘ ⟨g,h⟩ = h
snd-pair : optimize-once (snd ∘ ⟨ snd {Int} {Int} , fst ⟩) ≡ fst
snd-pair = refl

-- case h k ∘ inl = h
case-inl : optimize-once (case id (one ∘ terminal) ∘ inl {Int} {Int}) ≡ id
case-inl = refl

-- case h k ∘ inr = k
case-inr : optimize-once (case id (one ∘ terminal) ∘ inr {Int} {Int}) ≡ one ∘ terminal
case-inr = refl

-- ⟨fst, snd⟩ = id
pair-eta : optimize-once (⟨ fst {Int} {Int} , snd ⟩) ≡ id
pair-eta = refl

-- [inl, inr] = id
case-eta : optimize-once (case (inl {Int} {Int}) inr) ≡ id
case-eta = refl

-- ⟨fst, snd⟩ = id up to `Unit`: a `fst` into `Unit` is `terminal` first
pair-eta-unit : optimize-once (⟨ id ∘ fst {Unit} {Int} , snd ⟩) ≡ id
pair-eta-unit = refl

-- [inl, inr] = id up to `Void`: an `inl` out of `Void` is `initial` first
case-eta-void : optimize-once (case (inl {Void} {Int}) inr) ≡ id
case-eta-void = refl

-- the guard reads only the dropped term: `fst ∘ ⟨g,h⟩ = g` when `g` calls
fst-pair-effect : optimize-once (fst ∘ ⟨ eff {Int} {Int} , id ⟩) ≡ eff
fst-pair-effect = refl

-- (h ∘ k) ∘ f = h ∘ (k ∘ f): the chain goes to the right
reassoc : optimize-once ((eff {Int} {Int} ∘ eff {Int}) ∘ eff {Int}) ≡ eff ∘ (eff ∘ eff)
reassoc = refl

-- fst ∘ (⟨g,h⟩ ∘ k) = g ∘ k (`h` quiet)
fst-chain : optimize-once (fst ∘ (⟨ eff {Int} {Int} , id ⟩ ∘ eff {Int})) ≡ eff ∘ eff
fst-chain = refl

-- snd ∘ (⟨g,h⟩ ∘ k) = h ∘ k (`g` quiet)
snd-chain : optimize-once (snd ∘ (⟨ id , eff {Int} {Int} ⟩ ∘ eff {Int})) ≡ eff ∘ eff
snd-chain = refl

-- case h k ∘ (inl ∘ m) = h ∘ m
case-chain : optimize-once (case (eff {Int} {Int}) (one ∘ terminal) ∘ (inl {Int} {Int} ∘ eff {Int})) ≡ eff ∘ eff
case-chain = refl

-- apply ∘ ⟨curry f ∘ k, x⟩ = f ∘ ⟨k, x⟩: a closure built in place is applied
closure-beta : optimize-once (apply ∘ ⟨ curry (eff {Int} {Int} ∘ snd {Unit} {Int}) ∘ terminal , id ⟩)
             ≡ (eff ∘ snd) ∘ ⟨ terminal , id ⟩
closure-beta = refl

-- …with no `k`: apply ∘ ⟨curry f, x⟩ = f ∘ ⟨id, x⟩
closure-beta-bare : optimize-once (apply ∘ ⟨ curry (eff {Int} {Int} ∘ snd {Int} {Int}) , id ⟩)
                  ≡ (eff ∘ snd) ∘ ⟨ id , id ⟩
closure-beta-bare = refl
