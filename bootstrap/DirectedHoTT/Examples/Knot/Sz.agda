------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ THE SIZE of a term of the kernel's syntax,
-- object-level: the library fold (`Lib/TelFoldS`, `sizeAlg`) at the
-- Knot's signature.  No Knot-specific method is written: a sorted
-- syntax folds like a flat one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Sz where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Lib.Sugar using ( conₗ; tag; Lt )
open import DirectedHoTT.Lib.Tel using ( Tel; Tels; NthT; dihN )
open import DirectedHoTT.Lib.TelAt using ( NthST )
open import DirectedHoTT.Lib.TelFold using ( sizeAlg; foldK )
open import DirectedHoTT.Lib.TelFoldS using ( sortFolds; ⊢foldₛ; fold-ιₛ )
open import DirectedHoTT.Lib.MethAt using ( methAt )
open import DirectedHoTT.Lib.Sorted using ( Dₛₜ )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Sig

private
  variable
    Γ : Cx

-- the method: the size algebra, sort by sort
szM : RTm Γ
szM {Γ} = methAt (sortFolds sizeAlg (stels {Δ = Γ} KSig))

⊢szM : {Γ : Ctx} → Γ ⊢ szM ∷ MethTy (SI 2) KD Nat
⊢szM = ⊢foldₛ sizeAlg ⊢⌜Nat⌝ (sigOK KOK)

-- ★ `sz s d t`: the size of `t : K s d`
sz : ℕ → RTm Γ → RTm Γ → RTm Γ
sz s d t = ielim KD (pair (tag s) d) szM t

⊢sz : {Γ : Ctx} {s : ℕ} {d t : RTm ⌊ Γ ⌋} → Lt s 2 → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ K s d → Γ ⊢ sz s d t ∷ Nat
⊢sz lt dd dt = ⊢ielim ⊢SI ⊢KD ty-Nat ⊢szM (⊢ix lt dd) dt

-- ★ …and it computes, one node at a time: `1 + Σ (sizes of the recursive fields)`
sz-con : {s c k : ℕ} {Ts : Tels (Γ ∙) c} {T : Tel (Γ ∙)} {d p : RTm Γ} →
         NthST (stels KSig) s Ts → NthT Ts k T →
         sz s d (conₗ k p) ⟶* nsuc (foldK sizeAlg T (dihN (single (pair (tag s) d)) T KD szM p))
sz-con ns nt = fold-ιₛ sizeAlg ns nt
