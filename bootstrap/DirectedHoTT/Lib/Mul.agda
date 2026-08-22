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
module DirectedHoTT.Lib.Mul where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; var; vz; nzero; nsuc; natrec; Nat; Sub; subTm
        ; Ren; renTm; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _▹_; _⊢_∷_; ⊢var; here; ⊢nzero; ⊢natrec; ty-Nat
        ; _⟶*_; done; step; natrec-zero; natrec-suc; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Spec.Typing using ( single )
open import DirectedHoTT.Lib.Wk using ( w; sub-w; sub-w²; ren-sub )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )

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

mul-suc : {Γ : Cx} (m n : RTm Γ) → mulTm (nsuc m) n ⟶* plusTm n (mulTm m n)
mul-suc m n =
  subst (λ t → mulTm (nsuc m) n ⟶* t) peel
        (step (natrec-suc nzero (plusTm (w (w n)) (var vz)) m) done)
  where
    inner : subTm (extS (single m)) (w (w n)) ≡ w n
    inner = trans (sub-w {σ = single m} (w n)) (cong w (wk-single {v = m} n))

    peel = trans (cong (λ t → subTm (single (mulTm m n))
                                (natrec (var vz) (nsuc (var vz)) t))
                       inner)
                 (cong (λ t → natrec (mulTm m n) (nsuc (var vz)) t)
                       (wk-single {v = mulTm m n} n))

-- ⚠ AND `renTm` DOES NOT DISTRIBUTE THROUGH `mulTm` EITHER, for the same
--   reason — so the IH VARIABLE's type needs its own peel.  `assocB` got
--   away without one because `plusTm` renames definitionally; the moment a
--   `mulTm` is in the motive, `⊢var here` no longer has the shape the
--   branch wants.  ⭐ A renaming IS a substitution (`ren-sub`), so
--   `mulTm-sub` supplies this too — no second induction.
mulTm-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (m n : RTm Γ) →
            renTm ρ (mulTm m n) ≡ mulTm (renTm ρ m) (renTm ρ n)
mulTm-ren {ρ = ρ} m n =
  trans (ren-sub (mulTm m n))
    (trans (mulTm-sub {σ = λ v → var (ρ v)} m n)
           (cong₂ mulTm (sym (ren-sub m)) (sym (ren-sub n))))
