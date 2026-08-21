------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — GAP B LAYER 2: gcd MEETS THE DIVISIBILITY SPEC.
--
-- ⚠⚠ THE MOTIVE IS A CONJUNCTION, AND THAT IS FORCED, NOT A CHOICE.
--   gcd's `a > b` branch recurses at `(a ∸ b , b)`, so the IH gives
--   `d ∣ (a ∸ b)`; reaching `d ∣ a` needs `a ≡ (a ∸ b) + b` (`monusPlus`)
--   AND the second conjunct `d ∣ b`.  Symmetrically for `d ∣ b` in the
--   `a ≤ b` branch.  ⇒ **neither `gcd ∣ a` nor `gcd ∣ b` is provable
--   alone by this recursion**; they are ONE pass with two projections.
--
-- ★ AND IT IS A CODE.  `amrec-ind`'s motive lives in `U`, because `⊢jsub`
--   transports code families — the same constraint that forced certificate
--   irrelevance in `amrec-unfold-Id`.  `⊢dvdCode` was built to clear it.
--
-- ⇒ this file is step 5 of `GAP-B-LAYER2-PLAN.md`; `IndStep` is step 7.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdDvd where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs
        ; RTy; RTm; Nat; U; El; Σ'
        ; var; fst; snd; ⌜Nat⌝
        ; subTm; renTm; Ren; extR; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢fst; ⊢snd )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; asN )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( QCode; ⊢QCode; QCode-sub; QCode-ren )
open import poc.OCP0009.NbEPDirDBLibAmrecInd using ( PAtR )

------------------------------------------------------------------------
-- ★★★ THE MOTIVE.  Slot [1] is the ARGUMENT (the pair), slot [0] the
--   RESULT (gcd of it) — the order `amrec-ind` fixes.
--
--     P (x , v)  :=  v ∣ fst x  ∧  v ∣ snd x
------------------------------------------------------------------------

gcdP : {Γ : Cx} → RTm ((Γ ∙) ∙)
gcdP = QCode (fst (var (vs vz))) (snd (var (vs vz))) (var vz)

⊢gcdP : {Δ : Ctx} → ((Δ ▹ PairT) ▹ El ⌜Nat⌝) ⊢ gcdP ∷ U
⊢gcdP = ⊢QCode (⊢fst dx) (⊢snd dx) (asN (⊢var here))
  where
    -- ⚠ `PairT = Σ' Nat Nat` is CLOSED, so `renTy vs (renTy vs PairT)`
    --   computes back to `PairT` and this needs no cast.
    dx = ⊢var (there here)

------------------------------------------------------------------------
-- ★★ …AND `PAtR` AT IT.  `amrec-ind` states every premise through `PAtR`;
--   this is the one peel that turns those statements into readable
--   divisibility goals.
--
-- ⚠ THREE REWRITES, NOT ZERO: the ambient renaming, then the argument
--   slot, then the result slot — and each needs `QCode`'s naturality
--   because `dvdCode` contains a `mulTm`, which commutes with neither
--   `subTm` nor `renTm` definitionally.
------------------------------------------------------------------------

PAtR-gcd : {Δ Θ : Ctx} (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (y val : RTm ⌊ Θ ⌋) →
           PAtR ρ gcdP y val ≡ QCode (fst y) (snd y) val
PAtR-gcd ρ y val =
  trans (cong (λ t → subTm (single val) (subTm (extS (single y)) t))
              (QCode-ren {ρ = extR (extR ρ)}
                         (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
    (trans (cong (subTm (single val))
                 (QCode-sub {σ = extS (single y)}
                            (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
      (trans (QCode-sub {σ = single val} (fst (w y)) (snd (w y)) (var vz))
             (cong (λ u → QCode (fst u) (snd u) val)
                   (wk-single {v = val} y))))
