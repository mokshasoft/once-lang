------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ SUBSTITUTION of the kernel's syntax, object-level:
-- `Lib/SynSub` at the Knot's signature.  `sub0 t u` is `subTm (single u) t`
-- — what `β` needs — typed at every depth.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Sub where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import normalizer.Syntax.Types using ( _≡_; refl )
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

------------------------------------------------------------------------
-- ★ CLOSEDNESS: substitution commutes with substitution.
--   ⚠ `TRAVMs-sub` is one `refl` that costs ~30 s (the substitution kit's
--   weakening carries the description); a structural proof needs the
--   kits' closedness laws in `Lib/SynTravM` — an optimisation, not a gap.
------------------------------------------------------------------------

TRAVMs-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (TRAVM {Δ}) ≡ TRAVM
TRAVMs-sub σ = refl

SINGLE-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (SINGLE {Δ}) ≡ SINGLE
SINGLE-sub σ = refl

sub0-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) (s : ℕ) (d t u : RTm Δ) → subTm σ (sub0 s d t u) ≡ sub0 s (subTm σ d) (subTm σ t) (subTm σ u)
sub0-sub σ s d t u =
  cong₄ (λ D T M S → app (app (ielim D (pair T (nsuc (subTm σ d))) M (subTm σ t)) (subTm σ d)) (app (app S (subTm σ d)) (subTm σ u)))
        (SD-sub σ KSig) (tag-sub σ s) (TRAVMs-sub σ) (SINGLE-sub σ)
