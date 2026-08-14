------------------------------------------------------------------------
-- OCP-0009 — gcd's STEP FUNCTION.  SUBTRACTIVE EUCLID.
--
-- ★ SHARED BY BOTH KERNEL ROUTES, and that is the point: `…GcdLib` hands
--   it to `⊢amrecΠ`, `…GcdKernel` hands it to a hand-rolled bounded
--   auxiliary.  Factoring it out is what makes the comparison measure the
--   RECURSOR rather than the algorithm — otherwise the step, which is the
--   same work either way, swamps the difference.
--
--     gcd (a , 0)     = a
--     gcd (0 , b)     = b
--     gcd (a , b)     = gcd (a ∸ b , b)   if a > b
--     gcd (a , b)     = gcd (a , b ∸ a)   if a ≤ b
--
-- ★ THE USE SITE `WF-LIBRARY.md` ASKED FOR: *"a recursion whose
--   termination is NOT free, at a carrier that is NOT ℕ… a pair carrier
--   with a measure that is a real computation rather than a projection —
--   e.g. `μ (a , b) = a + b`."*  All three hold: `Σ' Nat Nat`, `a + b`,
--   and a descent that took `NbEPDirDBLibArith` + `NbEPDirDBLibArithComm` +
--   `NbEPDirDBLibArithMonus` to build.
--
-- ⚠ AND IT IS THE FUNCTION `⊢gcd-descend` WAS NOT.  That lemma is
--   `⊢div-descend` renamed and certifies the ONE-SIDED recursion
--   `gcd (suc m) (suc k) = gcd (m ∸ k) (suc k)`, which gives `gcd 3 5 = 5`.
--   Real gcd needs the COMPARISON, and the comparison is why there are
--   three nested splits below rather than one.
--
-- ★★ THREE SPLITS, AND EACH IS FORCED:
--     on `snd x`  — because `gcd (a , 0) = a` is a base case;
--     on `fst x`  — because `gcd (0 , b) = b` is a base case, and because
--                   `a ∸ b < a` is FALSE at `a = 0`, so both descents need
--                   both components to be successors;
--     on `a ∸ b`  — the COMPARISON.  ⚠ Its motive is CONSTANT: the branch
--                   needs to know only WHETHER `a ∸ b` is zero, never its
--                   value, and the kernel has no coproduct so a `natrec`
--                   with a constant motive IS the if-then-else.
--
-- ★ Everything here is built from VARIABLES, so every `subTy`/`subTm` at
--   a motive boundary COMPUTES — no `mot-at`/`mot-s`, no `wk-single`.
--   That is the one place this file is easier than the library modules.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdStep where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; subst; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; subTm; renTm; subTm-renTm; subTm-id; subTm-subTm; subTm-cong; extS
        ; Sub; Ren; Var; idₛ; renTm-renTm; _∘ᵣ_ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢⌜Nat⌝
        ; ty-Nat; ty-Hom; ty-El; ty-Π
        ; _≅ᵀ_; csymᵀ
        ; ξ-nsuc; ξ-Homˡ; ξ-natrecⁿ; ξ-natrecᶻ; βfst; βsnd
        ; _⟶_; _⟶*_; done; step; β; ξ-appˡ; natrec-zero; natrec-suc )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBVar using ( ren-as-sub )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ; ⟶*-ren; ⟶*-sub )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus; n1; n2; n3 )
open import poc.OCP0009.NbEPDirDBExamplesDiv
  using ( monusTm; ⊢monus; monus-zero; monus-suc; pred-zero; pred-suc
        ; monus-computes )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( aStepT )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asP )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoTm )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLTm )
open import poc.OCP0009.NbEPDirDBLibArithMonus
  using ( monusLtTm; ⊢desc-left; ⊢desc-right; pred* )

------------------------------------------------------------------------
-- ★ THE MEASURE — a real computation, not a projection.
------------------------------------------------------------------------

msr : {Γ : Cx} → RTm (Γ ∙)
msr = plusTm (fst (var vz)) (snd (var vz))

⊢msr : {Γ : Ctx} → (Γ ▹ PairT) ⊢ msr ∷ Nat
⊢msr = ⊢plus (⊢fst (⊢var here)) (⊢snd (⊢var here))

-- the IH at an explicit bound, and the "IH → answer" type the splits carry
gcdIH : {Γ : Cx} (μx : RTm Γ) → RTy Γ
gcdIH μx = aIHTat PairT ⌜Nat⌝ msr μx

⊢gcdIH : {Γ : Ctx} {μx : RTm ⌊ Γ ⌋} → Γ ⊢ μx ∷ Nat → Γ ⊢ty gcdIH μx
⊢gcdIH dμ =
  ty-Π ⊢PairT (ty-Π (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk dμ)) (ty-El ⊢⌜Nat⌝))

gcdG : {Γ : Cx} (μx : RTm Γ) → RTy Γ
gcdG μx = Π (gcdIH μx) (El ⌜Nat⌝)

⊢gcdG : {Γ : Ctx} {μx : RTm ⌊ Γ ⌋} → Γ ⊢ μx ∷ Nat → Γ ⊢ty gcdG μx
⊢gcdG dμ = ty-Π (⊢gcdIH dμ) (ty-El ⊢⌜Nat⌝)

------------------------------------------------------------------------
-- ★ the descent's conversion: the recursive call BUILDS a pair, so the
--   measure at it is `fst (pair p q) + snd (pair p q)`, two β-steps from
--   `p + q`.  ⚠ `plusTm m n = natrec n _ m` puts `m` in the SCRUTINEE and
--   `n` in the ZERO branch, hence `ξ-natrecⁿ` then `ξ-natrecᶻ`.
------------------------------------------------------------------------

descConv : {Γ : Cx} (p q u : RTm Γ) →
           Hom Nat (nsuc (plusTm (fst (pair p q)) (snd (pair p q)))) u
         ≅ᵀ Hom Nat (nsuc (plusTm p q)) u
descConv p q u =
  red→≅ᵀ (stepᵀ (ξ-Homˡ (ξ-nsuc (ξ-natrecⁿ (βfst p q))))
           (stepᵀ (ξ-Homˡ (ξ-nsuc (ξ-natrecᶻ (βsnd p q)))) doneᵀ))

------------------------------------------------------------------------
-- SPLIT 1 — on `snd x`.  ctx: [0]=n' [1]=x
------------------------------------------------------------------------

G1 : {Γ : Cx} → RTy (Γ ∙ ∙)
G1 = gcdG (plusTm (fst (var (vs vz))) (var vz))

⊢G1 : {Γ : Ctx} → ((Γ ▹ PairT) ▹ Nat) ⊢ty G1
⊢G1 = ⊢gcdG (⊢plus (⊢fst (⊢var (there here))) (⊢var here))

-- b = 0 : the answer is `a`, and the IH is discarded.
G1z : {Γ : Cx} → RTm (Γ ∙)
G1z = lam (fst (var (vs vz)))

⊢G1z : {Γ : Ctx} → (Γ ▹ PairT) ⊢ G1z ∷ gcdG (plusTm (fst (var vz)) nzero)
⊢G1z =
  ⊢lam (⊢gcdIH (⊢plus (⊢fst (⊢var here)) ⊢nzero))
       (asP (⊢fst (⊢var (there here))))

------------------------------------------------------------------------
-- SPLIT 2 — on `fst x`.  ctx: [0]=k' [1]=G1 [2]=n' [3]=x
------------------------------------------------------------------------

G2 : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙)
G2 = gcdG (plusTm (var vz) (nsuc (var (vs (vs vz)))))

⊢G2 : {Γ : Ctx} → ((((Γ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ⊢ty G2
⊢G2 = ⊢gcdG (⊢plus (⊢var here) (⊢nsuc (⊢var (there (there here)))))

-- a = 0 : the answer is `b`.  ctx after the ⊢lam: [0]=ih [1]=G1 [2]=n' [3]=x
G2z : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
G2z = lam (nsuc (var (vs (vs vz))))

⊢G2z : {Γ : Ctx} → (((Γ ▹ PairT) ▹ Nat) ▹ G1) ⊢ G2z
     ∷ gcdG (plusTm nzero (nsuc (var (vs vz))))
⊢G2z =
  ⊢lam (⊢gcdIH (⊢plus ⊢nzero (⊢nsuc (⊢var (there here)))))
       (asP (⊢nsuc (⊢var (there (there here)))))

------------------------------------------------------------------------
-- SPLIT 3 — the COMPARISON, on `a ∸ b`.  ⚠ CONSTANT MOTIVE: the branch
-- needs to know only WHETHER `a ∸ b` is zero, never its value.
-- ctx C4: [0]=G2 [1]=k' [2]=G1 [3]=n' [4]=x   so a = suc k', b = suc n'
------------------------------------------------------------------------

G3 : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙ ∙ ∙)
G3 = gcdG (plusTm (nsuc (var (vs (vs vz)))) (nsuc (var (vs (vs (vs (vs vz)))))))

⊢G3 : {Γ : Ctx} → ((((((Γ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) ▹ Nat) ⊢ty G3
⊢G3 =
  ⊢gcdG (⊢plus (⊢nsuc (⊢var (there (there here))))
               (⊢nsuc (⊢var (there (there (there (there here)))))))

-- a ≤ b : recurse at (a , b ∸ a).  SECOND component changes → ⊢desc-right.
-- ctx after the ⊢lam: [0]=ih [1]=G2 [2]=k' [3]=G1 [4]=n' [5]=x
G3z : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
G3z =
  lam (app (app (var vz)
                (pair (nsuc (var (vs (vs vz))))
                      (monusTm (nsuc (var (vs (vs (vs (vs vz))))))
                               (nsuc (var (vs (vs vz)))))))
           (plusMonoTm (monusLtTm (var (vs (vs (vs (vs vz))))) (var (vs (vs vz))))
                       (nsuc (var (vs (vs vz))))))

⊢G3z : {Γ : Ctx} → (((((Γ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) ⊢ G3z
     ∷ gcdG (plusTm (nsuc (var (vs vz))) (nsuc (var (vs (vs (vs vz))))))
⊢G3z =
  ⊢lam (⊢gcdIH (⊢plus (⊢nsuc (⊢var (there here)))
                      (⊢nsuc (⊢var (there (there (there here)))))))
    (⊢app (⊢app (⊢var here)
                (⊢pair ty-Nat (⊢nsuc dk) (⊢monus (⊢nsuc dn) (⊢nsuc dk))))
          (⊢conv (⊢desc-right dk dn)
                 (csymᵀ (descConv (nsuc (var (vs (vs vz))))
                                  (monusTm (nsuc (var (vs (vs (vs (vs vz))))))
                                           (nsuc (var (vs (vs vz)))))
                                  (plusTm (nsuc (var (vs (vs vz))))
                                          (nsuc (var (vs (vs (vs (vs vz))))))))))) 
  where
    dk = ⊢var (there (there here))
    dn = ⊢var (there (there (there (there here))))

-- a > b : recurse at (a ∸ b , b).  FIRST component changes → ⊢desc-left.
-- ctx after the ⊢lam: [0]=ih [1]=G3 [2]=d [3]=G2 [4]=k' [5]=G1 [6]=n' [7]=x
G3s : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
G3s =
  lam (app (app (var vz)
                (pair (monusTm (nsuc (var (vs (vs (vs (vs vz))))))
                               (nsuc (var (vs (vs (vs (vs (vs (vs vz)))))))))
                      (nsuc (var (vs (vs (vs (vs (vs (vs vz))))))))))
           (plusMonoLTm (monusTm (nsuc (var (vs (vs (vs (vs vz))))))
                                 (nsuc (var (vs (vs (vs (vs (vs (vs vz)))))))))
                        (nsuc (var (vs (vs (vs (vs vz))))))
                        (nsuc (var (vs (vs (vs (vs (vs (vs vz))))))))
                        (monusLtTm (var (vs (vs (vs (vs vz)))))
                                   (var (vs (vs (vs (vs (vs (vs vz))))))))))

⊢G3s : {Γ : Ctx} → (((((((Γ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) ▹ Nat) ▹ G3) ⊢ G3s
     ∷ gcdG (plusTm (nsuc (var (vs (vs (vs vz)))))
                    (nsuc (var (vs (vs (vs (vs (vs vz)))))))) 
⊢G3s =
  ⊢lam (⊢gcdIH (⊢plus (⊢nsuc (⊢var (there (there (there here)))))
                      (⊢nsuc (⊢var (there (there (there (there (there here)))))))))
    (⊢app (⊢app (⊢var here)
                (⊢pair ty-Nat (⊢monus (⊢nsuc dk) (⊢nsuc dn)) (⊢nsuc dn)))
          (⊢conv (⊢desc-left dk dn)
                 (csymᵀ (descConv (monusTm (nsuc KK) (nsuc NN)) (nsuc NN)
                                  (plusTm (nsuc KK) (nsuc NN))))))
  where
    KK = var (vs (vs (vs (vs vz))))
    NN = var (vs (vs (vs (vs (vs (vs vz))))))
    dk = ⊢var (there (there (there (there here))))
    dn = ⊢var (there (there (there (there (there (there here))))))

------------------------------------------------------------------------
-- ★★★ THE STEP, ASSEMBLED — three nested `natrec`s under one `lam`.
------------------------------------------------------------------------

-- ⚠ the BODY is named so that `β gcdBody x` pins its own source.  Splitting
--   a chain and substituting the halves needs each half's SOURCE fixed;
--   with `β _ x` the lam body becomes an unsolved meta once the halves are
--   no longer joined by a shared target.
-- ★ the two COMPOSITE branches, named.  Each `natrec-suc` in a reduction
--   chain takes the natrec's own two branches as arguments; leaving them
--   `_` is what makes a split chain's target an unsolved meta.  With these
--   names every step can be PINNED, so the target computes.
--   Contexts: the outer `natrec`'s successor branch sits under two extra
--   binders (predecessor + IH), hence Γ∙∙∙ then Γ∙⁵.
gcdInn2 : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
gcdInn2 = natrec G3z G3s
                 (monusTm (nsuc (var (vs vz)))
                          (nsuc (var (vs (vs (vs vz))))))

gcdInn1 : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
gcdInn1 = natrec G2z gcdInn2 (fst (var (vs (vs vz))))

gcdBody : {Γ : Cx} → RTm (Γ ∙)
gcdBody = natrec G1z gcdInn1 (snd (var vz))

gcdStp : {Γ : Cx} → RTm Γ
gcdStp = lam gcdBody

⊢gcdStp : {Γ : Ctx} → Γ ⊢ gcdStp ∷ aStepT PairT ⌜Nat⌝ msr
⊢gcdStp =
  ⊢lam ⊢PairT
    (⊢natrec ⊢G1 ⊢G1z
      (⊢natrec ⊢G2 ⊢G2z
        (⊢natrec ⊢G3 ⊢G3z ⊢G3s
                 (⊢monus (⊢nsuc (⊢var (there here)))
                         (⊢nsuc (⊢var (there (there (there here)))))))
        (⊢fst (⊢var (there (there here)))))
      (⊢snd (⊢var here)))

------------------------------------------------------------------------
-- ★★★ AND IT COMPUTES.  Type-correct is not the same as correct: this
--     repo already has ONE recorded case of a recursion that typechecked
--     and was not the intended function (`⊢gcd-descend`).  These four
--     reductions pin all four defining equations.
--
-- ⚠ These are the USER's half — how `amrecTm` unfolds TO the step is
--   `amrec-unfold-z`/`-s` in `LibAmrec`, already proven there.  Together
--   they cover `app gcdTm x`.
--
-- ⚠ CONCRETE numerals, not an arbitrary `a`: for an open `a` the final β
--   leaves `subTm (single ih) (w a)`, which is `a` only PROPOSITIONALLY
--   (`wk-single`).  At a numeral it computes.  Same note as `NbEPDirDBExamplesPairLib`.
------------------------------------------------------------------------

-- `1 ∸ 3 ⟶* 0`, which is what sends the comparison down the `a ≤ b` side
monus-1-3 : {Γ : Cx} → monusTm {Γ} n1 n3 ⟶* nzero
monus-1-3 =
  ⟶*-trans (monus-suc n1 n2)
    (⟶*-trans (pred* (⟶*-trans (monus-suc n1 n1)
                        (⟶*-trans (pred* (⟶*-trans (monus-suc n1 nzero)
                                            (⟶*-trans (pred* (monus-zero n1))
                                                      (pred-suc nzero))))
                                  pred-zero)))
              pred-zero)

-- ★ 1.  `gcd (a , 0) = a`
gcd-computes-b0 : (ih : RTm ε) → app (app gcdStp (pair n2 nzero)) ih ⟶* n2
gcd-computes-b0 ih =
  step (ξ-appˡ (β _ (pair n2 nzero)))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd n2 nzero) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done))
        (step (β _ ih) (step (βfst n2 nzero) done))))

-- ★ 2.  `gcd (0 , b) = b`
gcd-computes-a0 : (ih : RTm ε) → app (app gcdStp (pair nzero n2)) ih ⟶* n2
gcd-computes-a0 ih =
  step (ξ-appˡ (β _ (pair nzero n2)))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd nzero n2) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ n1) done))
        (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst nzero n2) done)))
          (⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done))
            (step (β _ ih) done)))))

------------------------------------------------------------------------
-- ★★★ GAP A, FIRST HALF — THE STEP'S EQUATIONS AT **VARIABLES**.
--
-- ⚠⚠ WHY THE LITERAL VERSIONS ABOVE PROVE LESS THAN THEY LOOK.  Each one
--   states `gcd (a , 0) = a` in a COMMENT but proves it at `a = 2`.  A
--   literal test cannot distinguish this step function from one that
--   returns `2` regardless, and that is exactly the class of defect that
--   already bit here once (the descent recursing on the wrong side).
--
-- ★ EQUATION 1 GENERALISES FOR FREE, and that is worth saying precisely:
--   its proof above never inspects `n2`.  It uses `βsnd` to see the SECOND
--   component is `0`, `natrec-zero` to take that branch, `β` to consume the
--   ignored IH, and `βfst` to project the FIRST component back out.  Not
--   one step looks inside `a`.  So the same proof term, with `n2` replaced
--   by a variable, is a proof for EVERY `a`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ THE GENERIC WEAKENING TRANSPORT.
--
-- ⚠⚠ EVERY mismatch in these reduction chains has ONE shape: a term `t`
--   that was WEAKENED into a deeper context (by the binders a `natrec-suc`
--   or a `lam` introduces) and then hit by substitutions that put it back.
--   The composite is pointwise the identity ON `t`'s VARIABLES — but only
--   PROPOSITIONALLY, so each occurrence needs a transport.
--
-- ★ THE POINT: it does not need one lemma per DEPTH.  Stated with the
--   substitution and the renaming abstract, a single lemma covers every
--   depth, because nested weakenings collapse (`renTm-renTm`) and nested
--   substitutions collapse (`subTm-subTm`) before it applies.  The caller
--   supplies only the pointwise fact, which is `refl` whenever the
--   composite computes.
--
--   This replaces the ad-hoc `wkS`/`wkS2` pair below — both are now
--   one-liners through it — and is what equations 3 and 4 will need at
--   depths 5 to 7.
------------------------------------------------------------------------

wkGen : {Γ Δ : Cx} {σ : Sub Δ Γ} {ρ : Ren Γ Δ} →
        ((x : Var Γ) → σ (ρ x) ≡ var x) →
        (t : RTm Γ) → subTm σ (renTm ρ t) ≡ t
wkGen h t = trans (subTm-renTm t) (trans (subTm-cong h t) (subTm-id t))

-- ★★ …and the version landing on a RENAMED target rather than on `t`.
--   ⚠ CONFIRMED (this typechecks): the `wkS` family is `single`-headed and
--   returns `t` EXACTLY; the composites that arise `extS`-headed return `t`
--   STILL WEAKENED.  Same three moves, one different endpoint —
--   `ren-as-sub` where `wkGen` uses `subTm-id`.
wkGenR : {Γ Δ Θ : Cx} {σ : Sub Δ Θ} {ρ : Ren Γ Δ} {ρ' : Ren Γ Θ} →
         ((x : Var Γ) → σ (ρ x) ≡ var (ρ' x)) →
         (t : RTm Γ) → subTm σ (renTm ρ t) ≡ renTm ρ' t
wkGenR {ρ' = ρ'} h t =
  trans (subTm-renTm t) (trans (subTm-cong h t) (sym (ren-as-sub ρ' t)))

-- the `extS`-headed companion the previous commit CONJECTURED — it holds.
wkE : {Γ : Cx} {v : RTm Γ} (t : RTm Γ) →
      subTm (extS (single v)) (renTm vs (renTm vs t)) ≡ renTm vs t
wkE t = trans (cong (subTm (extS (single _))) (renTm-renTm t))
              (wkGenR (λ x → refl) t)

-- ⚠ ONE TRANSPORT IS UNAVOIDABLE, and it is instructive.  At a LITERAL the
--   final projection lands on `n2` definitionally, because a numeral is
--   closed and both actions are inert on it.  At a VARIABLE the same step
--   lands on `subTm (single ih) (renTm vs a)` — propositionally `a`, but
--   not definitionally.  That single `≡` is the whole difference between
--   the literal test and the general theorem.
wkS : {Γ : Cx} {v : RTm Γ} (t : RTm Γ) → subTm (single v) (renTm vs t) ≡ t
wkS t = wkGen (λ x → refl) t

-- ★ `gcd (a , 0) = a` — for an ARBITRARY `a`, closed or open.
gcd-b0-var : {Γ : Cx} (a ih : RTm Γ) → app (app gcdStp (pair a nzero)) ih ⟶* a
gcd-b0-var a ih =
  subst (λ z → app (app gcdStp (pair a nzero)) ih ⟶* z) (wkS a)
    (step (ξ-appˡ (β _ (pair a nzero)))
      (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd a nzero) done)))
        (⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done))
          (step (β _ ih) (step (βfst _ nzero) done)))))

-- ⚠ EQUATION 2 DOES **NOT** GENERALISE THE SAME WAY, and the asymmetry is
--   forced by the algorithm, not by the proof.  `gcd (0 , b) = b` is
--   reached by SPLITTING ON `b`: the step must see `snd` is a SUCCESSOR
--   before it may look at `fst`.  At a variable `b` that `natrec` is stuck
--   (`natstk? b = true`), so no reduction sequence exists at all.
--   ⛔ NOT DONE: even one constructor in (`gcd (0 , suc b)`), the successor
--   branch threads the bound predecessor through several binders, so the
--   endpoint is not `nsuc b` up to `wkS` — it needs the branch body's own
--   substitution lemma.  Recorded rather than half-proved.

-- ⚠ THE TRANSPORT IS ONE BINDER DEEPER HERE, and that is the whole reason
--   equation 2 is harder than equation 1.  `natrec-suc` binds TWO variables
--   (the predecessor and the IH) before the branch runs, so `b` arrives
--   weakened TWICE and substituted twice.  The composite maps
--   `vs (vs x) ↦ var x` — pointwise the identity on `b`'s variables — but
--   only propositionally, so it needs its own lemma.
wkS2 : {Γ : Cx} {u v : RTm Γ} (t : RTm Γ) →
       subTm (single u) (subTm (extS (single v)) (renTm vs (renTm vs t))) ≡ t
-- ⚠ TWO substitutions, so one COLLAPSE is needed before `wkGen` applies:
--   `subTm-subTm` fuses them, `renTm-renTm` fuses the two weakenings, and
--   then the pointwise fact is `refl` again.  That is the general recipe at
--   any depth — collapse, then `wkGen`.
wkS2 {u = u} {v = v} t =
  trans (cong (subTm (single u)) (cong (subTm (extS (single v))) (renTm-renTm t)))
    (trans (subTm-subTm (renTm (vs ∘ᵣ vs) t))
      (wkGen (λ x → refl) t))

-- ★ depth THREE: `wkS2`'s shape wrapped in one more weaken-and-substitute.
--   Note it is built by COMPOSITION, not from scratch — collapse inward
--   with `wkS2`, then peel the outer layer with `wkS`.  That is how the
--   deeper instances the comparison branch needs are meant to be built.
wkS3 : {Γ : Cx} {u₁ u₂ v : RTm Γ} (t : RTm Γ) →
       subTm (single u₂)
         (renTm vs (subTm (single u₁)
           (subTm (extS (single v)) (renTm vs (renTm vs t))))) ≡ t
wkS3 {u₂ = u₂} t =
  trans (cong (λ z → subTm (single u₂) (renTm vs z)) (wkS2 t)) (wkS t)

-- ★ `gcd (0 , suc b) = suc b` — for an ARBITRARY `b`.
gcd-a0-var : {Γ : Cx} (b ih : RTm Γ) →
             app (app gcdStp (pair nzero (nsuc b))) ih ⟶* nsuc b
gcd-a0-var b ih =
  subst (λ z → app (app gcdStp (pair nzero (nsuc b))) ih ⟶* nsuc z) (wkS2 b)
    (step (ξ-appˡ (β _ (pair nzero (nsuc b))))
      (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd nzero (nsuc b)) done)))
        (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ b) done))
          (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst _ _) done)))
            (⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done))
              (step (β _ ih) done))))))

------------------------------------------------------------------------
-- ★★★★ EQUATION 3 — `a > b` recurses at `(a ∸ b , b)`, AT VARIABLES.
--
-- ⚠⚠ THE MOVE THAT MAKES IT WORK, after ~10 failed attempts fighting
--   weakening transports: PROVE IT AT VARIABLES, THEN SUBSTITUTE.
--
--   The transports existed only because `a'`/`b'` were arbitrary TERMS, so
--   `subTm σ (renTm ρ a')` reduced only PROPOSITIONALLY — and each fix
--   changed what Agda inferred, so the target moved.  With `a'`/`b'` taken
--   to be VARIABLES the very same composites COMPUTE, every transport
--   disappears, and the chain closes with no `subst` at all.  `⟶*-sub`
--   then recovers the general statement, because reduction is
--   substitution-stable.
--
-- ★ This is why the depth never mattered: it was never a bookkeeping
--   problem, it was a problem of proving the general case directly instead
--   of proving the generic one and instantiating.
------------------------------------------------------------------------

gtRHS : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
gtRHS ih A B = app (app ih (pair (monusTm (nsuc A) (nsuc B)) (nsuc B)))
                   (plusMonoLTm (monusTm (nsuc A) (nsuc B)) (nsuc A) (nsuc B)
                                (monusLtTm A B))

-- ⛔ ROUTE 3 (split the chain, substitute each half, splice the term-level
--   hypothesis) — ATTEMPTED, NOT LANDED, and the reason is now precise.
--
-- ★ The plan is sound and needs no transports.  What defeats it as written
--   is that `⟶*-sub σ : t ⟶* u → subTm σ t ⟶* subTm σ u` cannot have `t`
--   and `u` inferred FROM ITS RESULT: that would mean solving
--   `subTm σ t ≡ X` for `t`, i.e. higher-order unification.  So each half's
--   type must come from its argument — and an inline chain's target is a
--   meta.  ⚠ The intermediate CANNOT stay implicit here, though it could
--   under a bare `⟶*-trans`.
--
-- ⇒ THE INTERMEDIATE MUST BE WRITTEN, and it is findable rather than
--   guessable: pin each chain step's arguments (they are `gcdBody`'s own
--   nested branches, now named down to `G1z`/`G2z`/`G3z`/`G3s`) so the
--   target COMPUTES instead of remaining a meta, then read it off.  The
--   composite branches between them still need names for that.
--
-- ⇒ also needed: `σ3` must carry `d`, since the comparison's reduct appears
--   in the SECOND half.  Two variables are not enough.

-- ⛔ THE ARBITRARY-TERM FORM: still open, and here is the exact state.
--
-- ★ PROGRESS THAT STUCK: `gcdBody`/`gcdInn1`/`gcdInn2` are now named, so
--   every chain step CAN be pinned — `β gcdBody gX`, and
--   `natrec-suc (subTm (single gX) G1z) (subTm (extS (extS (single gX))) gcdInn1) b'`
--   both elaborate.  With the early steps pinned the target stops moving,
--   which was the thing that defeated the first ten attempts.
--
-- ⛔ WHAT REMAINS: the hypothesis `mh` must be restated about the
--   substituted `a'`.  The shape is now STABLE and known —
--     renTm vs (subTm (single U) (subTm (extS (single b')) (renTm vs (renTm vs a'))))
--   i.e. `renTm vs` of `wkS2`'s core, so ≡ `renTm vs a'` — but the
--   transport keeps landing at the wrong context level (`_Γ ∙ != Γ`), so
--   `⟶*-ren vs mh` composed with `cong (renTm vs) (wkS2 a')` does not fit
--   as written.  It is one correctly-levelled transport away.
--
-- ⚠ ROUTE 3 (split + substitute + splice) is ALSO viable and was carried
--   further than this: with the steps pinned, `gtPart1`'s target computes
--   and prints in full (~1750 chars).  Pasting it as an explicit type
--   would close that route mechanically — rejected here only because a
--   1750-character type is not something this POC should carry.
------------------------------------------------------------------------

-- the GENERIC instance: `a'`/`b'` are the two outermost variables
gcd-gt-gen : {Γ : Cx} (d ih : RTm (Γ ∙ ∙)) →
             monusTm (nsuc (var (vs vz))) (nsuc (var vz)) ⟶* nsuc d →
             app (app gcdStp (pair (nsuc (var (vs vz))) (nsuc (var vz)))) ih
           ⟶* gtRHS ih (var (vs vz)) (var vz)
gcd-gt-gen d ih mh =
  step (ξ-appˡ (β _ (pair (nsuc (var (vs vz))) (nsuc (var vz)))))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd _ _) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ _) done))
        (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst _ _) done)))
          (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ _) done))
            (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ mh))
              (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ _) done))
                (step (β _ ih) done)))))))

------------------------------------------------------------------------
-- ★★★★ EQUATION 4 — `a ≤ b` recurses at `(a , b ∸ a)`, AT VARIABLES.
--   Same shape, other branch: the comparison reaching ZERO selects `G3z`.
------------------------------------------------------------------------

leRHS : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
leRHS ih A B = app (app ih (pair (nsuc A) (monusTm (nsuc B) (nsuc A))))
                   (plusMonoTm (monusLtTm B A) (nsuc A))

gcd-le-gen : {Γ : Cx} (ih : RTm (Γ ∙ ∙)) →
             monusTm (nsuc (var (vs vz))) (nsuc (var vz)) ⟶* nzero →
             app (app gcdStp (pair (nsuc (var (vs vz))) (nsuc (var vz)))) ih
           ⟶* leRHS ih (var (vs vz)) (var vz)
gcd-le-gen ih mh =
  step (ξ-appˡ (β _ (pair (nsuc (var (vs vz))) (nsuc (var vz)))))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd _ _) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ _) done))
        (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst _ _) done)))
          (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ _) done))
            (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ mh))
              (⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done))
                (step (β _ ih) done)))))))

------------------------------------------------------------------------
-- ★ WHAT THE TWO LEMMAS ABOVE DO AND DO NOT SAY.
--
-- ⛔⛔ THEY ARE **VACUOUS**.  Found by asking "what exercises these?" —
--    nothing does, and the reason is fatal: THEIR PREMISE CANNOT BE
--    SATISFIED AT VARIABLES.
--
--    `monusTm m n = natrec m (predTm (var vz)) n` recurses on its SECOND
--    argument.  So `monusTm (nsuc A) (nsuc B)` steps to
--    `predTm (monusTm (nsuc A) B)`, and with `B` a VARIABLE that inner
--    `natrec` is stuck; `predTm` of a stuck term is another stuck
--    `natrec`.  It reaches neither `nsuc d` nor `nzero`.  So both
--    hypotheses are uninhabitable exactly where the lemmas are stated, and
--    an implication with an unsatisfiable premise proves NOTHING — the
--    same trap as [[subti-postulate-was-false]], one layer out.
--
-- ⚠ THE LESSON: `--safe`, zero holes and a green build do not make a
--    statement meaningful.  "Proved at variables" was the goal, and these
--    are literally that — but making the COMPARISON a hypothesis moved the
--    whole content into a premise that variables cannot discharge.  The
--    literal lemmas below are NOT instances of these; they are genuine but
--    only at literals.
--
-- ⇒ WHAT IS ACTUALLY STILL MISSING for equations 3 and 4: the
--   arbitrary-TERM form, where the premise CAN be discharged by the
--   caller (concrete arguments compute).  That is the statement I failed
--   to prove, and these two do not stand in for it.
--
-- ⛔ They do NOT immediately give the arbitrary-TERM form
--    `(a' b' : RTm Γ) → … ⟶* gtRHS ih a' b'`.  `⟶*-sub` transports the
--    CONCLUSION from the generic instance to any instance, but the
--    HYPOTHESIS would have to travel the other way — and at variables the
--    generic `monusTm` is stuck, so there is nothing to supply.  Any
--    concrete instance can discharge it by computation; a symbolic one
--    needs the comparison decided first, which is an induction on both
--    components.
------------------------------------------------------------------------

-- ★★ 3.  a > b : `gcd (3 , 1)` really does recurse at `(3 ∸ 1 , 1)` —
--     SUBTRACT b FROM a, KEEP b.  ⚠ This is the equation a gcd-class spec
--     error lands on, and the one `⊢gcd-descend`'s recursion got wrong.
gcd-recurses-left : (ih : RTm ε) →
                    app (app gcdStp (pair n3 n1)) ih
                  ⟶* app (app ih (pair (monusTm n3 n1) n1))
                         (plusMonoLTm (monusTm n3 n1) n3 n1 (monusLtTm n2 nzero))
gcd-recurses-left ih =
  step (ξ-appˡ (β _ (pair n3 n1)))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd n3 n1) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ nzero) done))
        (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst n3 n1) done)))
          (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ n2) done))
            (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ monus-computes))
              (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ n1) done))
                (step (β _ ih) done)))))))

-- ★★ 4.  a ≤ b : `gcd (1 , 3)` recurses at `(1 , 3 ∸ 1)` — KEEP a,
--     SUBTRACT a FROM b.  The comparison really does pick the other side.
gcd-recurses-right : (ih : RTm ε) →
                     app (app gcdStp (pair n1 n3)) ih
                   ⟶* app (app ih (pair n1 (monusTm n3 n1)))
                          (plusMonoTm (monusLtTm n2 nzero) n1)
gcd-recurses-right ih =
  step (ξ-appˡ (β _ (pair n1 n3)))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βsnd n1 n3) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ n2) done))
        (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst n1 n3) done)))
          (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ nzero) done))
            (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ monus-1-3))
              (⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done))
                (step (β _ ih) done)))))))

------------------------------------------------------------------------
-- ★ the measure at (2,0), reduced.  SHARED by both kernel routes: each
--   needs it to select the auxiliary's successor branch.
------------------------------------------------------------------------

-- `μ (2 , 0) = 2 + 0 ⟶* suc 1`, which is what selects the successor case
plus-2-0 : {Γ : Cx} → plusTm {Γ} n2 nzero ⟶* n2
plus-2-0 =
  step (natrec-suc _ _ _)
    (step (ξ-nsuc (natrec-suc _ _ _))
      (step (ξ-nsuc (ξ-nsuc (natrec-zero _ _))) done))

-- ⚠ pinned at `ε`: the numerals are context-polymorphic, so an inline
--   `pair n2 nzero` leaves its context a meta.
X20 : RTm ε
X20 = pair n2 nzero

msr-2-0 : subTm (single X20) msr ⟶* nsuc n1
msr-2-0 =
  ⟶*-trans (⟶*-natrecⁿ (step (βfst n2 nzero) done))
    (⟶*-trans (step (ξ-natrecᶻ (βsnd n2 nzero)) done) plus-2-0)
