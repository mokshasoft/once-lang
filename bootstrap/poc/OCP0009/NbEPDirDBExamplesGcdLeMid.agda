------------------------------------------------------------------------
-- OCP-0009 — EQUATION 4: gcd's STEP, WITH THE DESCENT ABSTRACTED.
--
-- ★ WHAT THIS IS FOR.  Equation 4's `⟶*` premise is unsatisfiable at
--   variables, so the descent must be rewritten PROPOSITIONALLY (see
--   `⊢monusLe`, the bridge).  Transport needs the step application as a
--   ONE-HOLE context with the descent as the hole — that is `midAt`.
--
-- ★★ HOW IT WAS FOUND, and the technique is the reusable part: NOT by
--   hand-composing gcd's substitution stack, which is where this kind of
--   work usually dies.  Instead state the chain with a deliberately WRONG
--   target (`⟶* nzero`) and read the real endpoint out of Agda's
--   mismatch message, one layer at a time.  Four probes gave `Zt`/`St`,
--   then `W`, then the shape, then the descent.
--
-- ⚠ AND THE ONE THAT COST A CYCLE: after the substitution stack the
--   descent is NOT syntactically `monus (nsuc a') (nsuc b')` — it is the
--   SUBSTITUTED form `D3'`, equal only propositionally (`wkS3`/`wkS3e`).
--   That is exactly why `gcd-le-term` carries `mhAt` to rewrite it, so the
--   propositional route pays at the same place the reductional one did.
--
-- ⇒ `subTm (single (D3' a' b')) F` is the chain's endpoint;
--   `subTm (single nzero) F` is where `natrec-zero` fires and gcd's
--   existing tail chain runs unchanged.  `congAt F` bridges them.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdLeMid where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTm; pair; nsuc; nzero; natrec; app; subTm; extS; renTm; vs; var; vz )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶*_; _⟶_; β; βfst; βsnd; ξ-appˡ; natrec-suc; single )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-appˡ; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBExamplesDiv using ( monusTm )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; G1z; gcdInn1; G2z; gcdInn2; G3z; G3s; one; _⟫_ )

gXx : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
gXx x y = pair (nsuc x) (nsuc y)

R1' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
R1' x y = natrec (subTm (single (gXx x y)) G1z)
                 (subTm (extS (extS (single (gXx x y)))) gcdInn1) y

W' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
W' x y = subTm (single (R1' x y))
           (subTm (extS (single y)) (renTm vs (renTm vs x)))

R2' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
R2' x y = natrec (subTm (single (R1' x y))
                    (subTm (extS (single y))
                      (subTm (extS (extS (single (gXx x y)))) G2z)))
                 (subTm (extS (extS (single (R1' x y))))
                   (subTm (extS (extS (extS (single y))))
                     (subTm (extS (extS (extS (extS (single (gXx x y)))))) gcdInn2)))
                 (W' x y)

-- ★ the third natrec's branches, with the SAME substitution stack pushed onto
-- `G3z`/`G3s` separately — sound because `subTm` distributes over `natrec`
Z3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
Z3' x y = subTm (single (R2' x y))
            (subTm (extS (single (W' x y)))
              (subTm (extS (extS (single (R1' x y))))
                (subTm (extS (extS (extS (single y))))
                  (subTm (extS (extS (extS (extS (single (gXx x y)))))) G3z))))

S3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm ((Γ ∙) ∙)
S3' x y = subTm (extS (extS (single (R2' x y))))
            (subTm (extS (extS (extS (single (W' x y)))))
              (subTm (extS (extS (extS (extS (single (R1' x y))))))
                (subTm (extS (extS (extS (extS (extS (single y))))))
                  (subTm (extS (extS (extS (extS (extS (extS (single (gXx x y))))))))
                         G3s))))

-- ⚠ the descent as the substitution stack ACTUALLY leaves it — equal to
--   `monus (nsuc a') (nsuc b')` only PROPOSITIONALLY (`wkS3`/`wkS3e`),
--   which is exactly why `gcd-le-term` needs `mhAt` to rewrite it.
D3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
D3' x y = subTm (single (R2' x y))
            (subTm (extS (single (W' x y)))
              (subTm (extS (extS (single (R1' x y))))
                (subTm (extS (extS (extS (single y))))
                  (subTm (extS (extS (extS (extS (single (gXx x y))))))
                         (monusTm (nsuc (var (vs vz)))
                                  (nsuc (var (vs (vs (vs vz))))))))))

midAt : {Γ : Cx} (a' b' ih d : RTm Γ) → RTm Γ
midAt a' b' ih d = app (natrec (Z3' a' b') (S3' a' b') d) ih

MID : {Γ : Cx} (a' b' ih : RTm Γ) → RTm Γ
MID a' b' ih = midAt a' b' ih (D3' a' b')

-- ★★★ THE mh-FREE PREFIX.  Every step here unfolds a CONSTRUCTOR-headed
--     scrutinee, so none of it needs the branch premise — which is why the
--     chain can be split here at all.
gcd-le-prefix : {Γ : Cx} (a' b' ih : RTm Γ) →
                app (app gcdStp (pair (nsuc a') (nsuc b'))) ih ⟶* MID a' b' ih
gcd-le-prefix a' b' ih =
  ( one (ξ-appˡ (β gcdBody (gXx a' b')))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βsnd _ _)))
  ⟫ ⟶*-appˡ (one (natrec-suc (subTm (single (gXx a' b')) G1z)
                             (subTm (extS (extS (single (gXx a' b')))) gcdInn1)
                             b'))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βfst _ _)))
  ⟫ ⟶*-appˡ (one (natrec-suc _ _ (W' a' b')))
  )
