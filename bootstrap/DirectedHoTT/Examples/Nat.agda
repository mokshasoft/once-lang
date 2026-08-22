------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE A: the datatype core.  THE
-- ACCEPTANCE TEST (SPIKE-WF §7): written FIRST, the kernel is landed
-- under it until it greens.
--
--   ★ numerals; `⊢plus` by `natrec`; `plus-computes : 2+1 ⟶* 3`.
--   ★ `⊢unit'` — the unit former types.
--
-- NOT here, and NOT an oversight: Id-rewriting ON NUMBERS.  `jsub`
-- takes a CODE family (`(Γ ▹ A) ⊢ d ∷ U`), and `Nat` has no code until
-- ⌜Nat⌝ ∈ U — that is stage C (N-in).  Stage A's `Nat` is a type-level
-- former only, so Id-at-Nat is reachable but its motive is not.
-- (Stage B adds: le-computes / lt-empty / the order demos.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Nat where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Id; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; idrefl; jsub
        ; subTm )
-- ★ the PRIMITIVES now live in `…LibNat`; re-exported so every existing
--   importer of this module keeps working unchanged.
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Spec.Typing
  using ( single; _⟶_; _⟶*_; done; step
        ; natrec-zero; natrec-suc; ξ-nsuc
        ; Ctx; ◇; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec
        ; _⊢ty_; ty-Nat; ty-Unit )

n1 n2 n3 : {Γ : Cx} → RTm Γ
n1 = nsuc nzero
n2 = nsuc (nsuc nzero)
n3 = nsuc (nsuc (nsuc nzero))

plus-computes : {Γ : Cx} → plusTm {Γ} n2 n1 ⟶* n3
plus-computes =
  step (natrec-suc _ _ _)
    (step (ξ-nsuc (natrec-suc _ _ _))
      (step (ξ-nsuc (ξ-nsuc (natrec-zero _ _)))
        done))

⊢unit' : {Γ : Ctx} → Γ ⊢ unit ∷ Unit
⊢unit' = ⊢unit
