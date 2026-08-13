------------------------------------------------------------------------
-- OCP-0009 — ★★★ gcd THROUGH `⊢amrecΠ`.  ROUTE 3 of 3.
--
--   ROUTE 1  `…GcdAgda`    pure Agda, `Acc` on `a + b`
--   ROUTE 2  `…GcdKernel`  over the kernel, hand-rolled auxiliary
--   ROUTE 3  this file     over the kernel, THROUGH THE LIBRARY
--
-- ★ THE STEP IS SHARED (`…GcdStep`) — routes 2 and 3 differ ONLY in what
--   turns a step into a total function.  Everything below is the price of
--   route 3, and it is one `open`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdLib where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs; RTy; El; Nat; Π; RTm; var; nzero; nsuc
        ; natrec; app; pair; fst; snd; ⌜Nat⌝; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; _⊢_∷_; ⊢nzero; ⊢nsuc; ⊢pair; ty-Nat
        ; ⊢⌜Nat⌝; _⟶*_; done; step; β; ξ-appˡ; ξ-nsuc; ξ-natrecᶻ
        ; natrec-zero; natrec-suc; βfst; βsnd )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; n1; n2; n3 )
open import poc.OCP0009.NbEPDirDBExamplesDiv
  using ( monusTm; monus-zero; monus-suc; pred-zero; pred-suc; monus-computes )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( module AmTΠ )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoTm )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLTm )
open import poc.OCP0009.NbEPDirDBLibArithMonus using ( monusLtTm; pred* )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( msr; ⊢msr; gcdStp; ⊢gcdStp; gcd-computes-b0; X20; msr-2-0 )

------------------------------------------------------------------------
-- ★★★ gcd, THROUGH THE COMBINATOR.
------------------------------------------------------------------------

open AmTΠ ◇ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt; amrec-step-z; amrec-step-s )

gcdTm : RTm ε
gcdTm = amrecTm

-- ★ A CLOSED, WELL-TYPED SUBTRACTIVE EUCLID — total by construction, no
--   `TERMINATING`, no fuel, no `Acc`, nothing added to the kernel.
⊢gcd : ◇ ⊢ gcdTm ∷ Π PairT (El ⌜Nat⌝)
⊢gcd = ⊢amrecΠ

------------------------------------------------------------------------
-- ★★★★ END TO END — D7's IDEAL SHAPE COMPOSING WITH THE CALLER'S HALF.
--
--   `gcd-computes-b0` above is already universally quantified in the IH,
--   because a step function never inspects it.  That IS the shape
--   `amrec-step-s` consumes, so the two compose with no glue at all:
--
--       app gcdTm (2 , 0) ⟶* 2
--
--   ⚠ Before D7's ideal shape this was NOT expressible — `amrec-unfold-s`
--     landed on the auxiliary's branch and the caller's theorem was about
--     `app (app stp x) ih`, so the two did not meet.  This one line is the
--     entire point of closing D7.
------------------------------------------------------------------------

-- ★★★ `gcd (2 , 0) = 2`, THROUGH THE WHOLE COMBINATOR.
gcd-2-0 : app gcdTm X20 ⟶* n2
gcd-2-0 = amrec-step-s X20 n1 msr-2-0 gcd-computes-b0
