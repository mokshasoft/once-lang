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
  using ( msr; ⊢msr; gcdStp; ⊢gcdStp; gcd-computes-b0; X20; msr-2-0
        ; gcd-b0-var )

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

------------------------------------------------------------------------
-- ★★★ GAP A, SECOND HALF — THE ASSEMBLED `gcdTm` AT A **VARIABLE**.
--
-- ⚠⚠ WHY `gcd-2-0` ABOVE IS WEAKER THAN IT READS.  It is the ONLY
--   end-to-end test of the assembled combinator, and it is a literal.  The
--   obstruction to generalising it is REAL, not laziness: the measure is
--   `μ (a , b) = a + b` with `plusTm m n = natrec n (nsuc vz) m`, i.e. it
--   recurses on its FIRST argument.  So `μ (a , 0)` is `natrec 0 _ a`,
--   which at a VARIABLE `a` is STUCK (`natstk? a = true`) — and both
--   `amrec-step-z`/`-s` are conditional on the measure reaching a numeral.
--   No reduction sequence exists, so no ⟶* theorem can be stated at a
--   bare variable.
--
-- ★ WHAT **IS** REACHABLE, and it is most of what was wanted: split `a`
--   ONE constructor and the measure fires again, for an ARBITRARY tail.
--   `μ (suc n , 0) ⟶* nsuc (n + 0)` is a SYNTACTIC successor whatever `n`
--   is, so `amrec-step-s` applies with `k := n + 0`.  Together the two
--   lemmas below cover every `a`, and neither is a literal test.
------------------------------------------------------------------------

-- ⚠ PINNED AT `ε`, like `X20` above: the numerals are context-polymorphic,
--   so `pair nzero nzero` on its own leaves `Γ` unsolved.
X00 : RTm ε
X00 = pair nzero nzero

-- the measure at `(0 , 0)` — reaches `0`, so the vacuous branch is taken
msr-0-0 : subTm (single X00) msr ⟶* nzero
msr-0-0 =
  ⟶*-trans (⟶*-natrecⁿ (step (βfst nzero nzero) done))
    (⟶*-trans (step (ξ-natrecᶻ (βsnd nzero nzero)) done)
      (step (natrec-zero _ _) done))

-- ★ the measure at `(suc n , 0)` for an ARBITRARY `n` — one `natrec-suc`,
--   and it lands on a successor whose predecessor is `n + 0`.
msr-suc-0 : (n : RTm ε) →
            subTm (single (pair (nsuc n) nzero)) msr ⟶* nsuc (plusTm n nzero)
msr-suc-0 n =
  ⟶*-trans (⟶*-natrecⁿ (step (βfst (nsuc n) nzero) done))
    (⟶*-trans (step (ξ-natrecᶻ (βsnd (nsuc n) nzero)) done)
      (step (natrec-suc _ _ n) done))

-- ★★★ `gcd (0 , 0) = 0`, through the whole combinator.
gcd-0-0 : app gcdTm X00 ⟶* nzero
gcd-0-0 = amrec-step-z X00 msr-0-0 (gcd-b0-var nzero)

-- ★★★★ `gcd (suc n , 0) = suc n` — THROUGH THE WHOLE COMBINATOR, for an
--   ARBITRARY `n`.  This is gap A's target for the assembled function: one
--   proof covering infinitely many inputs, not a literal.  `n` may itself
--   be open; nothing below inspects it.
gcd-suc-0 : (n : RTm ε) → app gcdTm (pair (nsuc n) nzero) ⟶* nsuc n
gcd-suc-0 n =
  amrec-step-s (pair (nsuc n) nzero) (plusTm n nzero)
               (msr-suc-0 n) (gcd-b0-var (nsuc n))

-- ⛔ WHAT IS STILL MISSING, stated so the pair above is not over-read: a
--   SINGLE statement `∀ a. gcd (a , 0) = a`.  The two lemmas cover every
--   numeral between them, but as two families rather than one theorem, and
--   a bare variable is still unreachable by ⟶* for the stuckness reason
--   above.  Closing that needs the INTERNAL propositional form —
--   `Π Nat (Id Nat (app gcdTm (pair (var vz) nzero)) (var vz))` — proved by
--   dependent `natrec` with these two as its branches.
