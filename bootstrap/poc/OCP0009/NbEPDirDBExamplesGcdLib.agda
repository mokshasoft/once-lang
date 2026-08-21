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
        ; natrec; app; pair; fst; snd; ⌜Nat⌝; subTm; lam )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; _⊢_∷_; _⊢ty_; ⊢nzero; ⊢nsuc; ⊢pair; ty-Nat
        ; ⊢⌜Nat⌝; _⟶*_; done; step; β; ξ-appˡ; ξ-nsuc; ξ-natrecᶻ
        ; natrec-zero; natrec-suc; βfst; βsnd
        ; ⊢var; here; there; ⊢conv; ⊢natrec; ⊢lam; ⊢app; csymᵀ )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Idˡ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ; ⟶*-appʳ; ⟶*-pairʳ; ⟶*-pairˡ )
open import poc.OCP0009.NbEPDirDBLibStrong using ( reflTm )
open import poc.OCP0009.NbEPDirDBLibNat
  using ( plusTm )
open import poc.OCP0009.NbEPDirDBExamplesNat
  using ( n1; n2; n3 )
open import poc.OCP0009.NbEPDirDBLibMonus
  using ( monusTm; monus-zero; monus-suc; pred-zero; pred-suc )
open import poc.OCP0009.NbEPDirDBExamplesDiv
  using ( monus-computes )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( module AmTΠ )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asN )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; ⊢tyIdN; reflN; ⊢reflN )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoTm )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLTm )
open import poc.OCP0009.NbEPDirDBLibArithMonus using ( monusLtTm; pred* )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( msr; ⊢msr; gcdStp; ⊢gcdStp; gcd-computes-b0; X20; msr-2-0
        ; gcd-b0-var; gcd-le-term; le-mh-1; recCert; recRed; _⟫_
        ; gcd-gt-term; gt-mh-1 )

------------------------------------------------------------------------
-- ★★★ gcd, THROUGH THE COMBINATOR.
------------------------------------------------------------------------

-- ★ every parameter is now context-polymorphic, so the combinator can be
--   instantiated at ANY context — which is what a proof under a binder
--   needs.  `GcdAt ◇` is the closed instance used throughout below.
module GcdAt (Δ : Ctx) where
  open AmTΠ Δ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp public
    using ( amrecTm; ⊢amrecΠ; ⊢amrecPt; amrec-step-z; amrec-step-s
          ; amrec-β; auxIH; aux-cycle; aux-step-s; descS-at; ihS-atP )

open GcdAt ◇
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt; amrec-step-z; amrec-step-s
        ; amrec-β; auxIH; aux-cycle; aux-step-s; descS-at; ihS-atP )

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

------------------------------------------------------------------------
-- ★★★★ GAP A, FINISHED — THE **INTERNAL** THEOREM.
--
-- The two lemmas above are META-level: they are Agda functions producing
-- reduction sequences, one per shape of `a`.  What was still missing is a
-- SINGLE statement, and one that lives INSIDE the object language:
--
--     ⊢gcd-b0 : ◇ ⊢ gcdB0Tm ∷ Π Nat (IdN (gcd (var vz , 0)) (var vz))
--
-- ⚠ THE OBSTRUCTION THAT MADE THIS HARD was never the Id-kit; it was that
--   a dependent `natrec`'s SUCCESSOR BRANCH lives under a binder, so it
--   must talk about `gcd (suc x , 0)` for a VARIABLE `x`.  `gcd-suc-0`
--   above is stated at `ε`, and a closed-context lemma cannot be used
--   there.  Making the whole gcd construction context-polymorphic is what
--   unblocked it — see the commit that generalised `gcdStp`.
------------------------------------------------------------------------

-- gcd at an arbitrary context, and the two computation lemmas there
gcdAt : (Δ : Ctx) → RTm ⌊ Δ ⌋
gcdAt Δ = GcdAt.amrecTm Δ

-- the zero case, also at an arbitrary context
X00At : {Δ : Ctx} → RTm ⌊ Δ ⌋
X00At = pair nzero nzero

msr-0-0At : {Δ : Ctx} → subTm (single (X00At {Δ})) msr ⟶* nzero
msr-0-0At =
  ⟶*-trans (⟶*-natrecⁿ (step (βfst nzero nzero) done))
    (⟶*-trans (step (ξ-natrecᶻ (βsnd nzero nzero)) done)
      (step (natrec-zero _ _) done))

msr-suc-0At : {Δ : Ctx} (n : RTm ⌊ Δ ⌋) →
              subTm (single (pair (nsuc n) nzero)) msr ⟶* nsuc (plusTm n nzero)
msr-suc-0At n =
  ⟶*-trans (⟶*-natrecⁿ (step (βfst (nsuc n) nzero) done))
    (⟶*-trans (step (ξ-natrecᶻ (βsnd (nsuc n) nzero)) done)
      (step (natrec-suc _ _ n) done))

-- ★ `gcd (suc n , 0) ⟶* suc n` AT ANY CONTEXT — the successor branch's
--   computational content.
gcd-suc-0At : {Δ : Ctx} (n : RTm ⌊ Δ ⌋) →
              app (gcdAt Δ) (pair (nsuc n) nzero) ⟶* nsuc n
gcd-suc-0At {Δ} n =
  GcdAt.amrec-step-s Δ (pair (nsuc n) nzero) (plusTm n nzero)
                     (msr-suc-0At n) (gcd-b0-var (nsuc n))

-- the motive: `gcd (a , 0) ≡ a`, as an object-language TYPE
gcdB0B : {Δ : Ctx} (a : RTm ⌊ Δ ⌋) → RTy ⌊ Δ ⌋
gcdB0B {Δ} a = IdN (app (gcdAt Δ) (pair a nzero)) a

⊢gcdB0Mot : {Δ : Ctx} → (Δ ▹ Nat) ⊢ty gcdB0B {Δ ▹ Nat} (var vz)
⊢gcdB0Mot {Δ} =
  ⊢tyIdN (asN (⊢app (GcdAt.⊢amrecΠ (Δ ▹ Nat))
                    (⊢pair ty-Nat (⊢var here) ⊢nzero)))
         (⊢var here)

-- ★ the proof TERM.  ⚠ the IH is NEVER USED: splitting `a` is not there to
--   supply an induction hypothesis, it is there to UN-STICK THE MEASURE.
--   Once `a` is `suc x`, `μ (suc x , 0)` is a syntactic successor and the
--   combinator computes on its own.  A structural recursion whose IH is
--   dead is exactly the signature of "the obstruction was stuckness".
gcdB0Tm : {Δ : Ctx} → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
gcdB0Tm a = natrec (reflN nzero) (reflN (nsuc (var (vs vz)))) a

⊢gcdB0 : {Δ : Ctx} {a : RTm ⌊ Δ ⌋} → Δ ⊢ a ∷ Nat → Δ ⊢ gcdB0Tm a ∷ gcdB0B a
⊢gcdB0 {Δ} da = ⊢natrec ⊢gcdB0Mot zB sB da
  where
    zB = ⊢conv (⊢reflN ⊢nzero)
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ (GcdAt.amrec-step-z Δ X00At msr-0-0At
                                     (gcd-b0-var nzero)))))
    sB = ⊢conv (⊢reflN (⊢nsuc (⊢var (there here))))
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ (gcd-suc-0At {(Δ ▹ Nat) ▹ gcdB0B {Δ ▹ Nat} (var vz)} (var (vs vz))))))

-- ★★★★ GAP A, CLOSED.  A single closed term of a single object-language
--   type, saying `∀ a. gcd (a , 0) = a`.  Not a family of meta-level
--   reduction sequences — one theorem, INTERNAL to the theory.
⊢gcd-b0-Π : ◇ ⊢ lam (gcdB0Tm {◇ ▹ Nat} (var vz))
                ∷ Π Nat (gcdB0B {◇ ▹ Nat} (var vz))
⊢gcd-b0-Π = ⊢lam ty-Nat (⊢gcdB0 {◇ ▹ Nat} (⊢var here))

------------------------------------------------------------------------
-- ★★★★★ A RECURSING RUN — `gcd (1,1) = 1`, THROUGH A REAL RECURSIVE CALL.
--
-- ⚠⚠ WHY THIS IS THE FIRST ONE.  Every earlier end-to-end result here
--   (`gcd-0-0`, `gcd-2-0`, `gcd-suc-0`) bottoms out in the step function
--   IMMEDIATELY — the measure hits its base case and the recursion never
--   re-enters.  They therefore test the combinator's plumbing but not its
--   recursion.  This one takes the `a ≤ b` branch, so the step calls its
--   `ih`, and that call has to land back on the auxiliary and unfold
--   AGAIN.  Expressing that is exactly what `aux-cycle` was built for.
--
--   The trace, four lines and one turn of the loop:
--     amrec-β    unfold the combinator at (1,1); bound is μ(1,1) = 2
--     aux-cycle  step ⇒ recursive call at (1 , 1∸1), auxiliary now at bound 1
--     ⟶*-pairʳ   compute the argument 1∸1 ⇒ 0   (in ARGUMENT position)
--     aux-step-s at (1,0) the step returns directly — `gcd-b0-var`
------------------------------------------------------------------------

X11 : RTm ⌊ ◇ ⌋
X11 = pair n1 n1

-- μ (1,1) = 1 + 1 = 2, i.e. `suc 1` — so the cycle's bound premise holds.
msr-1-1 : subTm (single X11) msr ⟶* nsuc n1
msr-1-1 =
    ⟶*-natrecⁿ (step (βfst n1 n1) done)
  ⟫ step (ξ-natrecᶻ (βsnd n1 n1)) done
  ⟫ step (natrec-suc _ _ nzero) done
  ⟫ step (ξ-nsuc (natrec-zero _ _)) done

gcd-1-1 : app amrecTm X11 ⟶* n1
gcd-1-1 =
    amrec-β X11
  ⟫ aux-cycle X11 X11 μ11 n1 p₀ Y {q = q} msr-1-1
      (λ ih → recRed (gcd-le-term nzero nzero ih le-mh-1))
  ⟫ ⟶*-appˡ (⟶*-appʳ (⟶*-pairʳ le-mh-1))
  ⟫ aux-step-s X11 (pair n1 nzero) n1 nzero c₁ done (gcd-b0-var n1)
  where
    μ11 : RTm ⌊ ◇ ⌋
    μ11 = subTm (single X11) msr

    p₀ : RTm ⌊ ◇ ⌋
    p₀ = reflTm μ11

    -- the recursive call's argument: (1 , 1∸1), not yet computed
    Y : RTm ⌊ ◇ ⌋
    Y = pair (nsuc nzero) (monusTm (nsuc nzero) (nsuc nzero))

    -- ⚠ the certificate is a FAMILY in `ih` — it is BUILT from the `ih`
    --   the auxiliary hands over, which is why `aux-cycle` takes it so.
    q : RTm ⌊ ◇ ⌋ → RTm ⌊ ◇ ⌋
    q ih = recCert (gcd-le-term nzero nzero ih le-mh-1)

    c₁ : RTm ⌊ ◇ ⌋
    c₁ = descS-at X11 X11 n1 p₀ Y (q (ihS-atP X11 X11 n1 p₀))

------------------------------------------------------------------------
-- ★★★★★ TWO TURNS — `gcd (2,1) = 1`.
--
-- ⚠ This is the one that shows the cycle really is a LOOP and not a
--   one-off, and it exercises BOTH recursive branches, which `gcd (1,1)`
--   did not:
--
--     (2,1)  2∸1 = 1 ≠ 0  ⇒  the a>b branch  ⇒  recurse at (2∸1 , 1)
--     (1,1)  1∸1 = 0      ⇒  the a≤b branch  ⇒  recurse at (1 , 1∸1)
--     (1,0)  base case    ⇒  return 1
--
--   So turn 1 is `gcd-gt-term`, turn 2 is `gcd-le-term`, and NOTHING
--   between them is bespoke: each turn is one `aux-cycle` plus a
--   reduction that computes the recursive argument.  The bound descends
--   3 ⇒ 2 ⇒ 1 and the auxiliary's INDEX stays `X21` throughout — which is
--   precisely why index and argument had to be separated.
------------------------------------------------------------------------

X21 : RTm ⌊ ◇ ⌋
X21 = pair n2 n1

-- μ (2,1) = 2 + 1 = 3
msr-2-1 : subTm (single X21) msr ⟶* nsuc n2
msr-2-1 =
    ⟶*-natrecⁿ (step (βfst n2 n1) done)
  ⟫ step (ξ-natrecᶻ (βsnd n2 n1)) done
  ⟫ step (natrec-suc _ _ (nsuc nzero)) done
  ⟫ step (ξ-nsuc (natrec-suc _ _ nzero)) done
  ⟫ step (ξ-nsuc (ξ-nsuc (natrec-zero _ _))) done

gcd-2-1 : app amrecTm X21 ⟶* n1
gcd-2-1 =
    amrec-β X21
  ⟫ aux-cycle X21 X21 μ21 n2 p₀ Y₁ {q = q₁} msr-2-1
      (λ ih → recRed (gcd-gt-term n1 nzero nzero ih (gt-mh-1 nzero)))
  ⟫ ⟶*-appˡ (⟶*-appʳ (⟶*-pairˡ (gt-mh-1 nzero)))   -- 2∸1 ⇒ 1, so arg is (1,1)
  ⟫ aux-cycle X21 X11 n2 n1 c₁ Y₂ {q = q₂} done
      (λ ih → recRed (gcd-le-term nzero nzero ih le-mh-1))
  ⟫ ⟶*-appˡ (⟶*-appʳ (⟶*-pairʳ le-mh-1))           -- 1∸1 ⇒ 0, so arg is (1,0)
  ⟫ aux-step-s X21 (pair n1 nzero) n1 nzero c₂ done (gcd-b0-var n1)
  where
    μ21 : RTm ⌊ ◇ ⌋
    μ21 = subTm (single X21) msr

    p₀ : RTm ⌊ ◇ ⌋
    p₀ = reflTm μ21

    Y₁ : RTm ⌊ ◇ ⌋              -- (2∸1 , 1), uncomputed
    Y₁ = pair (monusTm (nsuc n1) (nsuc nzero)) (nsuc nzero)

    q₁ : RTm ⌊ ◇ ⌋ → RTm ⌊ ◇ ⌋
    q₁ ih = recCert (gcd-gt-term n1 nzero nzero ih (gt-mh-1 nzero))

    c₁ : RTm ⌊ ◇ ⌋
    c₁ = descS-at X21 X21 n2 p₀ Y₁ (q₁ (ihS-atP X21 X21 n2 p₀))

    Y₂ : RTm ⌊ ◇ ⌋              -- (1 , 1∸1), uncomputed
    Y₂ = pair (nsuc nzero) (monusTm (nsuc nzero) (nsuc nzero))

    q₂ : RTm ⌊ ◇ ⌋ → RTm ⌊ ◇ ⌋
    q₂ ih = recCert (gcd-le-term nzero nzero ih le-mh-1)

    c₂ : RTm ⌊ ◇ ⌋
    c₂ = descS-at X21 X11 n1 c₁ Y₂ (q₂ (ihS-atP X21 X11 n1 c₁))

------------------------------------------------------------------------
-- ★★★ GAP A'S LAST PIECE — EQUATIONS 3 AND 4 INTERNALLY.  ⛔ STATEMENTS
--     ONLY; the proof terms are OPEN and the obstruction is below.
--
-- The reduction forms (`gcd-gt-term`/`gcd-le-term`) are as strong as a
-- REDUCTION can be: `monusTm` recurses on its second argument, so their
-- premise cannot be discharged at a variable `b`.  The internal form
-- replaces that premise with an `Id`, which a variable CAN satisfy.
------------------------------------------------------------------------

-- the hypothesis, internalised: "the descent lands on a successor"
gcdGtH : {Δ : Ctx} (a b d : RTm ⌊ Δ ⌋) → RTy ⌊ Δ ⌋
gcdGtH a b d = IdN (monusTm (nsuc a) (nsuc b)) (nsuc d)

-- …and on zero
gcdLeH : {Δ : Ctx} (a b : RTm ⌊ Δ ⌋) → RTy ⌊ Δ ⌋
gcdLeH a b = IdN (monusTm (nsuc a) (nsuc b)) nzero

-- ★ equation 3, internally: gcd (suc a , suc b) = gcd (a∸b , suc b)
gcdGtB : {Δ : Ctx} (a b : RTm ⌊ Δ ⌋) → RTy ⌊ Δ ⌋
gcdGtB {Δ} a b =
  IdN (app (gcdAt Δ) (pair (nsuc a) (nsuc b)))
      (app (gcdAt Δ) (pair (monusTm (nsuc a) (nsuc b)) (nsuc b)))

-- ★ equation 4, internally: gcd (suc a , suc b) = gcd (suc a , b∸a)
gcdLeB : {Δ : Ctx} (a b : RTm ⌊ Δ ⌋) → RTy ⌊ Δ ⌋
gcdLeB {Δ} a b =
  IdN (app (gcdAt Δ) (pair (nsuc a) (nsuc b)))
      (app (gcdAt Δ) (pair (nsuc a) (monusTm (nsuc b) (nsuc a))))

------------------------------------------------------------------------
-- ⛔⛔ THE OBSTRUCTION, and it is NOT the one I expected.
--
-- ⚠ FIRST, A CORRECTION.  I claimed the `AmTΠ` cycle work would unlock
--   these.  IT DOES NOT.  `aux-cycle` needs `n ⟶* nsuc k` — the measure
--   REDUCING to a successor.  At a variable pair the measure is
--   `plusTm (fst (a,b)) (snd (a,b))`, whose `natrec` is stuck on the
--   neutral `a`, so no bound premise is ever available and every unfold
--   lemma in the library is inapplicable.  The cycle closed gap C; it has
--   no purchase here.
--
-- ⚠ SECOND, WHY `⊢gcd-b0-Π` (equation 1) IS NOT A TEMPLATE.  That proof
--   is `natrec (reflN nzero) (reflN (nsuc (var (vs vz)))) a` — it never
--   uses its IH, because `gcd (a,0) = a` holds by the OUTER natrec's ZERO
--   branch, which fires whatever `a` is.  Equations 3/4 are the recursive
--   branches: their content IS the recursive call, so no such shortcut.
--
-- ★ WHAT IS ACTUALLY NEEDED — one missing lemma, statable now:
--
--     amrec-unfold-Id : Δ ⊢ p ∷ IdN μx (nsuc k) →
--                       Δ ⊢ ? ∷ IdN (app amrecTm x) (app (app stp x) ih)
--
--   i.e. the combinator's fixpoint equation as an INTERNAL identity
--   rather than a reduction.  Every unfold lemma in `NbEPDirDBLibAmrec`
--   is `⟶*`-valued; that is what confines them to concrete measures.
--
--   ⇒ THE NEXT DELIVERABLE IS IN THE WF LIBRARY, NOT IN THE GCD EXAMPLE.
--     That is the finding; it relocates the remaining work.
--
------------------------------------------------------------------------
-- ⚠⚠ CORRECTION, SECOND PASS (same day).  The paragraph above said
--   equations 3/4 "follow by `jsub`" once that lemma exists.  BOTH halves
--   of that were wrong, and the second half is the expensive one.
--
-- ⛔ (i) `amrec-unfold-Id` DOES NOT FOLLOW BY `jsub` EITHER.  `⊢jsub`
--   transports a CODE FAMILY `d` over a variable `v : El ⌜Nat⌝`; the
--   family may not mention the proof, and it must be well-typed at `U`
--   for an ARBITRARY `v`.  It must also mention `auxIH x v`, or it says
--   nothing about the unfolding — and `auxIH x v` only reaches an `El _`
--   once it is applied to a carrier AND to a certificate of type
--   `Hom Nat (μ of that carrier) v`, which at an arbitrary `v` has no
--   inhabitant to weaken in from `Δ`.  So the certificate must be BOUND
--   INSIDE the family (`⌜Π⌝` over `⌜Hom⌝ ⌜Nat⌝ (w μx) (var vz)` — the
--   only formable option), and the transport's source is then quantified
--   over ALL certificates while the combinator supplies exactly one,
--   `reflTm μx`.  ⇒ the source obligation IS certificate irrelevance.
--
-- ⛔ (ii) AND EVEN WITH IT, 3/4 DO NOT FOLLOW.  Their right-hand side is
--   a FRESH `app gcdTm Y` — the auxiliary at bound `μ Y` with certificate
--   `reflTm (μ Y)` — whereas the left-hand side's recursive call is
--   `app (app (auxIH X k) Y) descS`: bound `k`, and the auxiliary's index
--   still `X`.  Relating those is bound-and-certificate irrelevance
--   again.  ⚠ Note also that the MEASURE is not the obstruction here, as
--   the block above implies: `μ (suc a , suc b) ⟶* nsuc (a + suc b)`
--   fires at VARIABLES, so the cycle lemmas do apply.  What does not
--   compute is `monusTm`'s branch selection — which is exactly what
--   `gcdGtH`/`gcdLeH` internalise.
--
-- ★ SO THE MISSING THEOREM IS IRRELEVANCE, and it is reachable at a price
--   the CALLER pays once.  It follows from STEP EXTENSIONALITY — "the
--   step's answer depends on its IH only pointwise" — by INTERNAL
--   induction on the bound:
--     · bound `0`      the IH that branch hands over is `⊢strong-base'`,
--                      i.e. EX FALSO, so any two certificates agree for
--                      free — and `Id (El C) a b` is reachable by
--                      `absurd`, being `El (⌜Id⌝ C a b)` up to `El-⌜Id⌝`;
--     · bound `suc k`  both sides reduce to `app (app stp y) ihᵢ`, the two
--                      IHs differ only in the certificate they pass down,
--                      and that difference is the induction hypothesis
--                      at `k`.
--   Extensionality is the STANDARD side condition — Agda's own
--   `Induction.WellFounded.FixPoint` demands precisely it — and gcd's
--   step can discharge it, using its IH exactly once (`RecCall`).
--
--   ⇒ THE INTERFACE CHANGE: `AmTΠ` takes an extensionality premise, and
--     the induction is stated with `⊢auxIH`/`⊢aux-app` (landed in the WF
--     library alongside this note: the auxiliary at an arbitrary bound
--     had NO typing lemma at all, only reductions, so nothing INTERNAL
--     about the recursion was even statable).
------------------------------------------------------------------------
