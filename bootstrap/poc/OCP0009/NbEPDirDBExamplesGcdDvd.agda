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
        ; var; fst; snd; ⌜Nat⌝; nzero; nsuc
        ; subTm; renTm; Ren; extR; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; asN )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( QCode; ⊢QCode; QCode-sub; QCode-ren
        ; ⊢Q-intro; ⊢Q-fst; ⊢Q-snd
        ; ⊢dvd-zero; ⊢dvd-refl; ⊢dvd-plus; ⊢dvd-cong; ⊢congPL )
open import poc.OCP0009.NbEPDirDBLibDvd using ( dvdT )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; ⊢symN; ⊢transN )
open import poc.OCP0009.NbEPDirDBLibMonusPlus using ( monusPlus )
open import poc.OCP0009.NbEPDirDBLibMonusLe using ( monusLe )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( Prv; prv )
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

------------------------------------------------------------------------
-- ★★★★★ THE FOUR LEAVES OF `IndStep`, AS TOP-LEVEL `Def`-BACKED LEMMAS.
--
-- ★ THIS IS THE MATHEMATICAL CONTENT of gap B layer 2; everything left
--   after it is `natrec` plumbing.  Each leaf is stated at an ARBITRARY
--   context with the components as explicit terms — the `⊢strong-base'`
--   pattern, applied before the plumbing rather than after an OOM.
--
-- ⚠ NOTE WHERE THE IH IS AND IS NOT USED.  The two BASE leaves discharge
--   the spec outright; only the two RECURSIVE leaves consume the induction
--   hypothesis — and each consumes BOTH conjuncts.  That is the concrete
--   form of "the motive must be a conjunction".
------------------------------------------------------------------------

-- ★ 1.  b = 0 :  gcd (a , 0) = a.   Need `a ∣ a` and `a ∣ 0`.
gcdLeaf-b0 : {Γ : Ctx} {u : RTm ⌊ Γ ⌋} → Γ ⊢ u ∷ Nat →
             Prv Γ (El (QCode u nzero u))
gcdLeaf-b0 du = prv _ (⊢Q-intro ⊢nzero du (⊢dvd-refl du) (⊢dvd-zero du))

-- ★ 2.  a = 0, b = suc b' :  gcd (0 , b) = b.   `b ∣ 0` and `b ∣ b`.
gcdLeaf-a0 : {Γ : Ctx} {b' : RTm ⌊ Γ ⌋} → Γ ⊢ b' ∷ Nat →
             Prv Γ (El (QCode nzero (nsuc b') (nsuc b')))
gcdLeaf-a0 db =
  prv _ (⊢Q-intro (⊢nsuc db) (⊢nsuc db)
                  (⊢dvd-zero (⊢nsuc db)) (⊢dvd-refl (⊢nsuc db)))

-- ★★ 3.  a ≤ b  (`a ∸ b ≡ 0`) :  recurse at `(a , b ∸ a)`.
--    The IH gives `v ∣ a` and `v ∣ (b ∸ a)`; the first conjunct is
--    immediate, the second is `⊢dvd-plus` then `monusLe`.
gcdLeaf-le : {Γ : Ctx} {a b v h₁ h₂ e : RTm ⌊ Γ ⌋} →
             Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat →
             Γ ⊢ e ∷ IdN (monusTm a b) nzero →
             Γ ⊢ h₁ ∷ dvdT v a → Γ ⊢ h₂ ∷ dvdT v (monusTm b a) →
             Prv Γ (El (QCode a b v))
gcdLeaf-le {b = b} {v = v} da db dv de dh1 dh2 =
  prv _ (⊢Q-intro db dv dh1 dvb)
  where
    dsum = ⊢plus (⊢monus db da) da
    dvb  = ⊢dvd-cong dv dsum db
             (⊢symN db dsum (monusLe da db de))
             (⊢dvd-plus dv (⊢monus db da) da dh2 dh1)

-- ★★ 4.  a > b  (`a ∸ b ≡ suc p`) :  recurse at `(a ∸ b , b)`.
--    The IH gives `v ∣ (a ∸ b)` and `v ∣ b`; the SECOND conjunct is
--    immediate, the first is `⊢dvd-plus` then `monusPlus`.
gcdLeaf-gt : {Γ : Ctx} {a b v p h₁ h₂ e : RTm ⌊ Γ ⌋} →
             Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat → Γ ⊢ p ∷ Nat →
             Γ ⊢ e ∷ IdN (monusTm a b) (nsuc p) →
             Γ ⊢ h₁ ∷ dvdT v (monusTm a b) → Γ ⊢ h₂ ∷ dvdT v b →
             Prv Γ (El (QCode a b v))
gcdLeaf-gt {a = a} {v = v} da db dv dp de dh1 dh2 =
  prv _ (⊢Q-intro db dv dva dh2)
  where
    dsum  = ⊢plus (⊢monus da db) db
    dsum' = ⊢plus (⊢nsuc dp) db
    deq   = ⊢transN dsum dsum' da
              (⊢congPL db (⊢monus da db) (⊢nsuc dp) de)
              (⊢symN da dsum' (monusPlus da db dp de))
    dva   = ⊢dvd-cong dv dsum da deq
              (⊢dvd-plus dv (⊢monus da db) db dh1 dh2)
