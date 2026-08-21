------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — THE TWO MOTIVES, THROUGH ONE PLUMBING.
--
-- ★★★ THIS IS THE AMORTISATION EVIDENCE, and it is the only form of it
--   that counts: `…ExamplesGcdIndG`'s `Motive` record has TWO INSTANCES.
--
--     divisibility   `gcd (a,b) ∣ a  ∧  gcd (a,b) ∣ b`     a `⌜Σ⌝` motive
--     maximality     `∀e. e∣a → e∣b → e ∣ gcd (a,b)`        a `⌜Π⌝` motive
--
--   Each supplies six facts about its motive and four leaves.  Neither
--   supplies a `natrec`, a context, a renaming or a split.
--
-- ⚠ THE LEAF SIGNATURES ARE WHERE THE TWO CUSTOMERS MEET, and getting
--   that interface right is what made one plumbing serve both: the record
--   hands a leaf the induction hypothesis as `El (PC …)` — the motive AT
--   THE RECURSIVE CALL — and asks for `El (PC …)` at the current pair.
--   The `⌜Σ⌝` customer projects the IH's two conjuncts; the `⌜Π⌝` customer
--   decodes it to a function type.  Neither shape leaks into the plumbing.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdMotives where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDBPi using ( Cx; RTm; El; Nat; nzero; nsuc )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢conv; csymᵀ )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( Prv; prv; prvOk )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( QCode; ⊢QCode; QCode-sub; QCode-ren; QCode-red; QCode-redU
        ; ⊢Q-fst; ⊢Q-snd )
open import poc.OCP0009.NbEPDirDBLibMax
  using ( MaxCode; ⊢MaxCode; MaxCode-sub; MaxCode-ren
        ; MaxCode-red; MaxCode-redU; El-max
        ; maxLeaf-b0; maxLeaf-a0; maxLeaf-le; maxLeaf-gt )
open import poc.OCP0009.NbEPDirDBExamplesGcdDvd
  using ( gcdLeaf-b0; gcdLeaf-a0; gcdLeaf-le; gcdLeaf-gt )
open import poc.OCP0009.NbEPDirDBExamplesGcdIndG using ( Motive )

open Motive

------------------------------------------------------------------------
-- ★ CUSTOMER 1 — the divisibility spec.  A `⌜Σ⌝` motive; the leaves
--   PROJECT the induction hypothesis' two conjuncts.
------------------------------------------------------------------------

dvdMotive : Motive
PC       dvdMotive = QCode
⊢PC      dvdMotive = ⊢QCode
PC-sub   dvdMotive = QCode-sub
PC-ren   dvdMotive = QCode-ren
PC-redV  dvdMotive = QCode-red
PC-redU  dvdMotive = QCode-redU
leaf-b0  dvdMotive = gcdLeaf-b0
leaf-a0  dvdMotive = gcdLeaf-a0
leaf-le  dvdMotive da db dv de dih =
  gcdLeaf-le da db dv de (⊢Q-fst dih) (⊢Q-snd dih)
leaf-gt  dvdMotive da db dv dp de dih =
  gcdLeaf-gt da db dv dp de (⊢Q-fst dih) (⊢Q-snd dih)

------------------------------------------------------------------------
-- ★ CUSTOMER 2 — maximality.  A `⌜Π⌝` motive; the leaves DECODE the
--   induction hypothesis to a function type and apply it.
------------------------------------------------------------------------

maxMotive : Motive
PC       maxMotive = MaxCode
⊢PC      maxMotive = ⊢MaxCode
PC-sub   maxMotive = MaxCode-sub
PC-ren   maxMotive = MaxCode-ren
PC-redV  maxMotive = MaxCode-red
PC-redU  maxMotive = MaxCode-redU
leaf-b0  maxMotive {u = u} du =
  prv _ (⊢conv (maxLeaf-b0 du) (csymᵀ (red→≅ᵀ (El-max u nzero u))))
leaf-a0  maxMotive {b = b} db =
  prv _ (⊢conv (maxLeaf-a0 db)
               (csymᵀ (red→≅ᵀ (El-max nzero (nsuc b) (nsuc b)))))
leaf-le  maxMotive {a = a} {b = b} {v = v} da db dv de dih =
  prv _ (⊢conv (maxLeaf-le da db dv
                  (⊢conv dih (red→≅ᵀ (El-max a (monusTm b a) v))))
               (csymᵀ (red→≅ᵀ (El-max a b v))))
leaf-gt  maxMotive {a = a} {b = b} {v = v} da db dv dp de dih =
  prv _ (⊢conv (maxLeaf-gt da db dv
                  (⊢conv dih (red→≅ᵀ (El-max (monusTm a b) b v))))
               (csymᵀ (red→≅ᵀ (El-max a b v))))
