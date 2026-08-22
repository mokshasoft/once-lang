------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — DIVISIBILITY, GAP B's MISSING PREDICATE.
--
-- ⚠ WHY GAP B EXISTS AT ALL.  `gcd` is currently a NAME, not a
--   specification: its type `Π PairT (El ⌜Nat⌝)` is equally consistent
--   with the term computing `min`.  Nothing anywhere in the development
--   says what gcd is FOR.  This module supplies the predicate that lets
--   the specification be stated.
--
-- ★ THE ENCODING, and it needs nothing new from the kernel:
--
--       d ∣ n   :=   Σ k : Nat.  n ≡ d * k
--
--   `Σ'` and `Id` are both present, so this is a definition rather than a
--   kernel extension.  `…LibMul` supplies the `*`, which did not exist
--   before gap B needed it.
--
-- ⚠⚠ THE ORIENTATION IS `n ≡ k * d`, NOT `n ≡ d * k`, AND IT IS FORCED.
--   `mulTm` recurses on its FIRST argument, so `k * d` COMPUTES when the
--   WITNESS is a numeral while `d` stays a variable — which is exactly the
--   direction the base cases need:
--
--     `d ∣ 0`  takes k := 0 and `mulTm nzero d ⟶* nzero`     — definitional
--     `d ∣ d`  takes k := 1 and reduces to `plus d 0`, closed by `⊢plus0`
--
--   Written `d * k` both would be STUCK at the variable `d` and each would
--   need its own induction.  Same predicate, and one choice is free where
--   the other is two proofs.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibDvd where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; RTm; Σ'; Nat; var; vz; pair; fst; snd; subTy; nzero; nsuc
        ; U; El; Id; ⌜Σ⌝; ⌜Id⌝; ⌜Nat⌝ )
open import normalizer.Syntax.Types using ( _≡_; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBLibStrong using ( natAsEl; elAsNat )
open import poc.OCP0009.NbEPDirDBType
  using ( ⊢⌜Σ⌝; ⊢⌜Id⌝; ⊢⌜Nat⌝
        ; Ctx; ⌊_⌋; _▹_; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; ⊢pair; ⊢fst; ⊢snd; ⊢nzero; ty-Nat; ty-Σ; wk-single )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMul using ( mulTm; ⊢mul; mulTm-sub )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; ⊢tyIdN )

------------------------------------------------------------------------
-- ★ THE PREDICATE.
------------------------------------------------------------------------

dvdT : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ
dvdT d n = Σ' Nat (IdN (w n) (mulTm (var vz) (w d)))

⊢dvdT : {Γ : Ctx} {d n : RTm ⌊ Γ ⌋} →
        Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ty dvdT d n
⊢dvdT dd dn =
  ty-Σ ty-Nat (⊢tyIdN (⊢wk dn) (⊢mul (⊢var here) (⊢wk dd)))

------------------------------------------------------------------------
-- ★★ INTRO AND ELIM.  One peel each, and it is the same peel: the Σ's
--   body instantiated at the witness.
------------------------------------------------------------------------

dvd-at : {Γ : Cx} (d n k : RTm Γ) →
         subTy (single k) (IdN (w n) (mulTm (var vz) (w d)))
       ≡ IdN n (mulTm k d)
dvd-at d n k =
  cong₂ IdN (wk-single {v = k} n)
            (trans (mulTm-sub {σ = single k} (var vz) (w d))
                   (cong (mulTm k) (wk-single {v = k} d)))

dvd-intro : {Γ : Ctx} {d n k p : RTm ⌊ Γ ⌋} →
            Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat →
            Γ ⊢ p ∷ IdN n (mulTm k d) →
            Γ ⊢ pair k p ∷ dvdT d n
dvd-intro {d = d} {n = n} {k = k} dd dn dk dp =
  ⊢pair (⊢tyIdN (⊢wk dn) (⊢mul (⊢var here) (⊢wk dd)))
        dk
        (⊢-cast (sym (dvd-at d n k)) dp)

-- the witness, and the equation it witnesses
dvd-wit : {Γ : Ctx} {d n h : RTm ⌊ Γ ⌋} → Γ ⊢ h ∷ dvdT d n → Γ ⊢ fst h ∷ Nat
dvd-wit dh = ⊢fst dh

dvd-eq : {Γ : Ctx} {d n h : RTm ⌊ Γ ⌋} → Γ ⊢ h ∷ dvdT d n →
         Γ ⊢ snd h ∷ IdN n (mulTm (fst h) d)
dvd-eq {d = d} {n = n} {h = h} dh = ⊢-cast (dvd-at d n (fst h)) (⊢snd dh)

------------------------------------------------------------------------
-- ★★★★★ …AND THE PREDICATE IS CODE-EXPRESSIBLE.  THIS IS THE GATE ON
--   GAP B's LAYER 2, AND IT IS OPEN.
--
-- ⚠ WHY IT WAS IN DOUBT.  `⊢jsub` transports a CODE FAMILY, so any
--   induction principle over `amrec` must take a motive in `U`, not an
--   arbitrary `RTy`.  That constraint is what stopped `amrec-unfold-Id`
--   from being a plain unfold and forced certificate irrelevance instead
--   (recorded in `…LibAmrec`'s header).  A general `amrec-ind` inherits
--   it — so a predicate that CANNOT be written as a code is unreachable
--   by that route no matter how the combinator is shaped.
--
-- ★ `dvdT` can: `Σ'` and `Id` both have codes (`⌜Σ⌝`, `⌜Id⌝`) with typing
--   AND decoding rules, and `Nat` has `⌜Nat⌝`.  So the divisibility
--   specification is expressible in `U`, and gap B's layer 2 is not
--   blocked at the STATEMENT — only at the missing combinator.
------------------------------------------------------------------------

dvdCode : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
dvdCode d n = ⌜Σ⌝ ⌜Nat⌝ (⌜Id⌝ ⌜Nat⌝ (w n) (mulTm (var vz) (w d)))

⊢dvdCode : {Γ : Ctx} {d n : RTm ⌊ Γ ⌋} →
           Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ dvdCode d n ∷ U
⊢dvdCode dd dn =
  ⊢⌜Σ⌝ ⊢⌜Nat⌝
    (⊢⌜Id⌝ ⊢⌜Nat⌝
       (natAsEl (⊢wk dn))
       (natAsEl (⊢mul (elAsNat (⊢var here)) (⊢wk dd))))
