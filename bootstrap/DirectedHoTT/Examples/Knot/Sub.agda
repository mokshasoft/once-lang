------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ SUBSTITUTION of the kernel's syntax, object-level:
-- `Lib/SynSub` at the Knot's signature.  `sub0 t u` is `subTm (single u) t`
-- — what `β` needs — typed at every depth.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Sub where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( lt-z; lt-s )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynSub
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Terms
open import DirectedHoTT.Examples.Knot.Ren using ( KVars )

open Sub KOK {v = 1} {kv = 0} (nthᵍ-s nthᵍ-z) nthʰ-z KVars public

-- ★ the body of a `lam` at depth `suc |Γ|`, instantiated at an argument
⊢β-quote : {Γ : Cx} (t : RTm (Γ ∙)) (u : RTm Γ) {Θ : Ctx} →
           Θ ⊢ sub0 1 (dep Γ) (quoteTm t) (quoteTm u) ∷ K 1 (dep Γ)
⊢β-quote {Γ} t u = ⊢sub0 (lt-s lt-z) (⊢dep' Γ) (⊢quoteTm t) (⊢quoteTm u)
