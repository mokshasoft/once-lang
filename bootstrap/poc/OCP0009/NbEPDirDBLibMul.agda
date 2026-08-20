------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — MULTIPLICATION.
--
-- ⚠ WHY THIS DID NOT EXIST BEFORE.  Nothing in the WF axis needed it:
--   the measures are all `plus`/`monus`, and gap A's four equations never
--   multiply.  GAP B does — `d ∣ n` is `Σ k. n ≡ d * k`, so divisibility
--   cannot even be STATED without it.
--
-- ★ SHAPE: `natrec` on the LEFT argument, exactly like `plusTm`.  `m * n`
--   is `m` copies of `n` summed.  ⚠ `n` crosses the two binders
--   `natrec-suc` introduces (the predecessor and the IH), so it appears
--   WEAKENED TWICE in the step.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibMul where

open import normalizer.Syntax.Types using ( _≡_; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTm; var; vz; nzero; natrec; Nat; Sub; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ⌊_⌋; _▹_; _⊢_∷_; ⊢var; here; ⊢nzero; ⊢natrec; ty-Nat
        ; _⟶*_; done; step; natrec-zero; natrec-suc )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w² )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )

mulTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
mulTm m n = natrec nzero (plusTm (w (w n)) (var vz)) m

⊢mul : {Γ : Ctx} {m n : RTm ⌊ Γ ⌋} →
       Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ mulTm m n ∷ Nat
⊢mul dm dn = ⊢natrec ty-Nat ⊢nzero (⊢plus (⊢wk (⊢wk dn)) (⊢var here)) dm

-- ★ the two computation rules, which hold by `natrec`'s own reduction.
mul-zero : {Γ : Cx} (n : RTm Γ) → mulTm nzero n ⟶* nzero
mul-zero n = step (natrec-zero _ _) done

-- ★ SUBSTITUTION-NATURALITY.  ⚠ NOT definitional, and the reason is the
--   same one `descLeftTm` had: `n` sits under the two binders `natrec-suc`
--   introduces, so it appears as `w (w n)` and a substitution has to be
--   pushed past both.  `sub-w²` is exactly that.
mulTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (m n : RTm Γ) →
            subTm σ (mulTm m n) ≡ mulTm (subTm σ m) (subTm σ n)
mulTm-sub {σ = σ} m n =
  cong (λ t → natrec nzero (plusTm t (var vz)) (subTm σ m)) (sub-w² {σ = σ} n)
