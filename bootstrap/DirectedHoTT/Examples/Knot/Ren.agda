------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ RENAMING AND WEAKENING of the kernel's syntax,
-- object-level: `Lib/SynRen` at the Knot's signature.  Nothing here is
-- about the Knot's rows — it is the generic traversal, instantiated.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Ren where

open import normalizer.Syntax.Types using ( refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( lt-z; lt-s )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynTravM using ( VarsAt )
open import DirectedHoTT.Lib.SynRen
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms

-- the kernel's variables are terms: sort 1, the `var` row (Tm row 0)
KVars : VarsAt KSig 1
KVars = varsAt KSig 1 refl

open Ren KOK {v = 1} {kv = 0} (nthᵍ-s nthᵍ-z) nthʰ-z KVars public

-- ★ weakening a quoted term: `renTm vs`, object-level, typed
⊢wk-quote : {Γ : Cx} (t : RTm Γ) {Θ : Ctx} → Θ ⊢ wk 1 (dep Γ) (quoteTm t) ∷ K 1 (nsuc (dep Γ))
⊢wk-quote {Γ} t = ⊢wkS (lt-s lt-z) (⊢dep' Γ) (⊢quoteTm t)
