------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — ORDER PRIMITIVES (`ordtr`, strong induction).
--
-- ★ WHY THIS MODULE EXISTS.  Seven `Lib*` modules build on
--   `⊢strong-base'`/`⊢strong-step`, including the lexicographic recursors.
--   They lived in `…ExamplesOrd` only because that is where stage E was
--   first demonstrated, which made LIBRARIES import EXAMPLES.
--
-- ⚠ `…ExamplesOrd` re-exports this module `public`, so every existing
--   importer keeps working unchanged.  Only `Lib*` importers were
--   repointed.
--
-- ★★★ WHAT IS ACTUALLY BEING SHOWN HERE — STRONG INDUCTION WITHOUT `Acc`.
--
--     aux : (n : Nat) → (m : Nat) → m ≤ n → P m       -- by natrec on n
--
--   Recall the encoding: `k < m` IS `Hom Nat (nsuc k) m`.  The successor
--   peel that would be a lemma anywhere else is a single REDUCTION step
--   (`Hom-Nat-ss`), and the impossible branch is discharged because
--   `Hom Nat (nsuc k) nzero` COMPUTES to `base`.  No fuel, no `Acc`, no
--   `TERMINATING` — the measure never appears, because the ORDER reduces.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Ord where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTy; Hom; Nat; U; El; RTm; nzero; nsuc; ordtr; absurd )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢conv; ⊢nzero; ⊢nsuc; ⊢ordtr; ⊢absurd
        ; Hom-Nat-sz; Hom-Nat-ss )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; stepᵀ; doneᵀ )

-- ★★ …and transitivity types at OPEN naturals, which is the whole
--    reason the former exists.  No numerals, no case split, no `Acc`.
⊢trans : {Γ : Ctx} {a t u p q : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ t ∷ Nat → Γ ⊢ u ∷ Nat →
         Γ ⊢ p ∷ Hom Nat a t → Γ ⊢ q ∷ Hom Nat t u →
         Γ ⊢ ordtr a t u p q ∷ Hom Nat a u
⊢trans = ⊢ordtr

------------------------------------------------------------------------
-- ★★★ THE CROWN JEWEL'S TWO HALVES — STRONG INDUCTION WITHOUT `Acc`.
--
--     aux : (n : Nat) → (m : Nat) → m ≤ n → P m       -- by natrec on n
--
--   Recall the encoding: `k < m` IS `Hom Nat (nsuc k) m`, because
--   `nsuc k ≤ m` and `k < m` are the same statement.
------------------------------------------------------------------------

-- ★ THE BASE CASE (n = 0).  Needs only stage D, and already worked
--   before `ordtr`: `Hom Nat (nsuc k) nzero` COMPUTES to `base`, so the
--   impossible branch is discharged by ex falso.  There is no
--   "impossible" tactic and no absurd-pattern machinery — the empty
--   type is what the order REDUCES TO.
⊢strong-base : {Γ : Ctx} {C k p : RTm ⌊ Γ ⌋} →
               Γ ⊢ C ∷ U → Γ ⊢ p ∷ Hom Nat (nsuc k) nzero →
               Γ ⊢ absurd C p ∷ El C
⊢strong-base {k = k} dC dp =
  ⊢absurd dC (⊢conv dp (red→≅ᵀ (stepᵀ (Hom-Nat-sz k) doneᵀ)))

-- ★★ THE STEP CASE (n = suc n').  THIS is what `ordtr` was the gate
--    for: from `k < m` and `m ≤ suc n` conclude `k ≤ n`.
--
--    Compose to get `nsuc k ≤ nsuc n`, then let the ORDER COMPUTE:
--    `Hom Nat (nsuc k) (nsuc n) ⟶ᵀ Hom Nat k n` by `Hom-Nat-ss`.  The
--    successor-peel that would be a lemma anywhere else is a single
--    reduction step here, and the whole step case is five lines.
⊢strong-step : {Γ : Ctx} {k m n p q : RTm ⌊ Γ ⌋} →
               Γ ⊢ k ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat →
               Γ ⊢ p ∷ Hom Nat (nsuc k) m →       -- k < m
               Γ ⊢ q ∷ Hom Nat m (nsuc n) →       -- m ≤ suc n
               Γ ⊢ ordtr (nsuc k) m (nsuc n) p q ∷ Hom Nat k n   -- k ≤ n
⊢strong-step {k = k} {n = n} dk dm dn dp dq =
  ⊢conv (⊢ordtr (⊢nsuc dk) dm (⊢nsuc dn) dp dq)
        (red→≅ᵀ (stepᵀ (Hom-Nat-ss k n) doneᵀ))

-- ★ and the descent is REAL: `k < m` and `m ≤ suc n` really do give a
--   proof at the SMALLER bound `n`, so `natrec`'s structural recursion
--   on `n` carries the whole strong induction.  No fuel, no `Acc`, no
--   `TERMINATING` — the measure never appears because the ORDER is the
--   thing that reduces.

-- ★★ …and the GENERAL base case needs `ordtr` TOO.
--
-- ⚠ CORRECTION to the older handoffs' §4, which said the `n = 0` half
--   "needs only stage D and already works".  That is true only when the
--   bound is LITERALLY `nzero`.  In the real strong induction the
--   recursor hands you `k < m` and `m ≤ 0` for an OPEN `m`, and getting
--   from those to `k < 0` is a composition — so stage E gates BOTH
--   halves, not just the step.  `Hom Nat (nsuc k) nzero` then computes
--   to `base` and ex falso finishes it.
⊢strong-base' : {Γ : Ctx} {C k m lt le : RTm ⌊ Γ ⌋} →
                Γ ⊢ C ∷ U → Γ ⊢ k ∷ Nat → Γ ⊢ m ∷ Nat →
                Γ ⊢ lt ∷ Hom Nat (nsuc k) m →     -- k < m
                Γ ⊢ le ∷ Hom Nat m nzero →        -- m ≤ 0
                Γ ⊢ absurd C (ordtr (nsuc k) m nzero lt le) ∷ El C
⊢strong-base' {k = k} dC dk dm dlt dle =
  ⊢absurd dC (⊢conv (⊢ordtr (⊢nsuc dk) dm ⊢nzero dlt dle)
                    (red→≅ᵀ (stepᵀ (Hom-Nat-sz k) doneᵀ)))

-- ★★ the step case in the form the recursor actually hands you: `k < m`
--    and `m ≤ suc n` give `k ≤ n`, i.e. the IH applies at the SMALLER
--    bound.  (`⊢strong-step` above, with the first bound a successor.)
⊢strong-descend : {Γ : Ctx} {k m n lt le : RTm ⌊ Γ ⌋} →
                  Γ ⊢ k ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat →
                  Γ ⊢ lt ∷ Hom Nat (nsuc k) m →   -- k < m
                  Γ ⊢ le ∷ Hom Nat m (nsuc n) →   -- m ≤ suc n
                  Γ ⊢ ordtr (nsuc k) m (nsuc n) lt le ∷ Hom Nat k n
⊢strong-descend = ⊢strong-step
