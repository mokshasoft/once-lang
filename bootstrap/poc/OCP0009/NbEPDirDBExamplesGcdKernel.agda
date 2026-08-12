------------------------------------------------------------------------
-- OCP-0009 — gcd OVER THE KERNEL, WITH NO COMBINATOR.  ROUTE 2 of 3.
--
--   ROUTE 1  `…GcdAgda`    pure Agda, `Acc` on `a + b`
--   ROUTE 2  this file     the WF axis, bounded auxiliary BY HAND
--   ROUTE 3  `…GcdLib`     the WF axis, through `⊢amrecΠ`
--
-- ★ THE STEP IS SHARED (`…GcdStep`), so routes 2 and 3 differ ONLY in
--   what turns a step into a total function.  Everything below is what
--   `⊢amrecΠ` does for you, written out.
--
-- ⚠ WHAT THIS IMPORTS FROM THE LIBRARY, and why it is still "no
--   combinator": `aIHTat` is a TYPE ABBREVIATION — the shape of an IH —
--   and the shared step could not be typed without naming it.  What is
--   NOT imported is `module AmT`/`AmTΠ`, the recursor itself.  That is
--   the thing being measured.
--
-- ★★ IT IS SHORTER IN LEMMAS AND FAR MORE EXPENSIVE — AND THOSE ARE THE
--    SAME FACT.  `LibAmrec` needs ten naturality lemmas (`aAuxB-sub`,
--    `mot-at`, `mot-s`, `stp-w²`, `stp-w⁴`, `ih₀-w⁵`, `cancelZ`,
--    `cancelS`, `cancelΠ`, `aIHT-fit`).  Here: ZERO — at a CONCRETE
--    carrier `renTy vs PairT` and `renTm (extR vs) msr` just COMPUTE, so
--    every one of those obligations discharges by `refl`.
--
--    ⚠⚠ I PREDICTED THAT WOULD MAKE THIS CHEAP.  MEASURED, IDLE BOX, COLD,
--    ON THE SAME SHARED STEP:
--
--        route 2, hand-rolled auxiliary   31.7 s / 1.94 GB
--        route 3, through `⊢amrecΠ`        4.0 s / 0.36 GB
--
--    8× slower, 5× more memory.  ★ "It computes" is not a saving — it is
--    the EXPENSIVE path once the terms are big, because Agda re-normalises
--    the concrete carrier at every obligation instead of applying a NAME.
--    `LibAmrec`'s ten lemmas are `Def`-backed, so the traversal phases walk
--    a reference; that is `agda-cost-is-elaborated-term-size` and D10's
--    lever, showing up a third time.
--
--    ⇒ the library does NOT only buy genericity.  Its naturality layer is
--      also a PERFORMANCE mechanism, and a caller with a single concrete
--      carrier still wants it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdKernel where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π
        ; RTm; var; nzero; nsuc; natrec; lam; app; absurd; ordtr
        ; fst; snd; ⌜Nat⌝
        ; renTy; renTm; subTy; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢fst; ⊢snd; ⊢⌜Nat⌝
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep using ( msr; ⊢msr; gcdStp; ⊢gcdStp )

------------------------------------------------------------------------
-- THE BOUNDED AUXILIARY'S TYPE — `(x : A) → μ x ≤ n → P x`.
------------------------------------------------------------------------

auxB : {Γ : Cx} (n : RTm Γ) → RTy Γ
auxB n = Π PairT (Π (Hom Nat msr (w n)) (El ⌜Nat⌝))

⊢auxB : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ Nat → Γ ⊢ty auxB n
⊢auxB dn = ty-Π ⊢PairT (ty-Π (ty-Hom ty-Nat ⊢msr (⊢wk dn)) (ty-El ⊢⌜Nat⌝))

-- the natrec motive: the bound IS the recursion variable
auxMot : RTy (ε ∙ ∙)
auxMot = auxB (var vz)

⊢auxMot : ((◇ ▹ PairT) ▹ Nat) ⊢ty auxMot
⊢auxMot = ⊢auxB (⊢var here)

------------------------------------------------------------------------
-- n = 0 : `μ y < μ x ≤ 0` is impossible, so the IH is EX FALSO.
-- ctx inside `ihZ`: [0]=lt [1]=y [2]=le [3]=x [4]=x₀
------------------------------------------------------------------------

ihZ : RTm (ε ∙ ∙ ∙)
ihZ =
  lam (lam (absurd ⌜Nat⌝
    (ordtr (nsuc (plusTm (fst (var (vs vz))) (snd (var (vs vz)))))
           (plusTm (fst (var (vs (vs (vs vz))))) (snd (var (vs (vs (vs vz))))))
           nzero (var vz) (var (vs (vs vz))))))

⊢ihZ : (((◇ ▹ PairT) ▹ PairT) ▹ Hom Nat msr nzero) ⊢ ihZ
     ∷ aIHTat PairT ⌜Nat⌝ msr
               (plusTm (fst (var (vs vz))) (snd (var (vs vz))))
⊢ihZ =
  ⊢lam ⊢PairT
    (⊢lam (ty-Hom ty-Nat (⊢nsuc ⊢msr)
            (⊢wk (⊢plus (⊢fst (⊢var (there here))) (⊢snd (⊢var (there here))))))
      (⊢strong-base' ⊢⌜Nat⌝
        (⊢plus (⊢fst (⊢var (there here))) (⊢snd (⊢var (there here))))
        (⊢plus (⊢fst (⊢var (there (there (there here)))))
               (⊢snd (⊢var (there (there (there here))))))
        (⊢var here) (⊢var (there (there here)))))

zBr : RTm (ε ∙)
zBr = lam (lam (app (app (w (w (w gcdStp))) (var (vs vz))) ihZ))

⊢zBr : (◇ ▹ PairT) ⊢ zBr ∷ auxB nzero
⊢zBr =
  ⊢lam ⊢PairT
    (⊢lam (ty-Hom ty-Nat ⊢msr ⊢nzero)
      (⊢app (⊢app (⊢wk (⊢wk (⊢wk ⊢gcdStp))) (⊢var (there here))) ⊢ihZ))

------------------------------------------------------------------------
-- n = suc n' : the IH at n' is a CONTEXT VARIABLE, and `⊢strong-step` is
-- the descent — μ y < μ x and μ x ≤ suc n' give μ y ≤ n'.
-- ctx inside `ihS`: [0]=lt [1]=y [2]=le [3]=x [4]=IH [5]=n' [6]=x₀
------------------------------------------------------------------------

ihS : RTm (ε ∙ ∙ ∙ ∙ ∙)
ihS =
  lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))
    (ordtr (nsuc (plusTm (fst (var (vs vz))) (snd (var (vs vz)))))
           (plusTm (fst (var (vs (vs (vs vz))))) (snd (var (vs (vs (vs vz))))))
           (nsuc (var (vs (vs (vs (vs (vs vz))))))) (var vz) (var (vs (vs vz))))))

⊢ihS : (((((◇ ▹ PairT) ▹ Nat) ▹ auxMot) ▹ PairT)
          ▹ Hom Nat msr (nsuc (var (vs (vs vz))))) ⊢ ihS
     ∷ aIHTat PairT ⌜Nat⌝ msr
               (plusTm (fst (var (vs vz))) (snd (var (vs vz))))
⊢ihS =
  ⊢lam ⊢PairT
    (⊢lam (ty-Hom ty-Nat (⊢nsuc ⊢msr)
            (⊢wk (⊢plus (⊢fst (⊢var (there here))) (⊢snd (⊢var (there here))))))
      (⊢app (⊢app (⊢var (there (there (there (there here))))) (⊢var (there here)))
            (⊢strong-step
              (⊢plus (⊢fst (⊢var (there here))) (⊢snd (⊢var (there here))))
              (⊢plus (⊢fst (⊢var (there (there (there here)))))
                     (⊢snd (⊢var (there (there (there here))))))
              (⊢var (there (there (there (there (there here))))))
              (⊢var here) (⊢var (there (there here))))))

sBr : RTm (ε ∙ ∙ ∙)
sBr =
  lam (lam (app (app (w (w (w (w (w gcdStp))))) (var (vs vz))) ihS))

⊢sBr : (((◇ ▹ PairT) ▹ Nat) ▹ auxMot) ⊢ sBr ∷ auxB (nsuc (var (vs vz)))
⊢sBr =
  ⊢lam ⊢PairT
    (⊢lam (ty-Hom ty-Nat ⊢msr (⊢nsuc (⊢var (there (there here)))))
      (⊢app (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk ⊢gcdStp))))) (⊢var (there here)))
            ⊢ihS))

------------------------------------------------------------------------
-- ★★★ THE RECURSOR, AND gcd.
--
-- ⚠ Note the Π wrapper: ONE line, no casts.  `LibAmrec`'s `⊢amrecΠ` needs
--   `mot-at m`, `cancelΠ`, `wᶠ¹-single` and `wk-single` for the same three
--   applications — again, purely because its data are abstract.
------------------------------------------------------------------------

auxTm : RTm (ε ∙) → RTm (ε ∙)
auxTm n = natrec zBr sBr n

⊢aux : {n : RTm (ε ∙)} → (◇ ▹ PairT) ⊢ n ∷ Nat →
       (◇ ▹ PairT) ⊢ auxTm n ∷ auxB n
⊢aux dn = ⊢natrec ⊢auxMot ⊢zBr ⊢sBr dn

gcdKTm : RTm ε
gcdKTm = lam (app (app (auxTm msr) (var vz)) (reflTm msr))

⊢gcdK : ◇ ⊢ gcdKTm ∷ Π PairT (El ⌜Nat⌝)
⊢gcdK = ⊢lam ⊢PairT (⊢app (⊢app (⊢aux ⊢msr) (⊢var here)) (⊢le-refl ⊢msr))
