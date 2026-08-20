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

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; subst; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; subTm; subTy; renTm; subTm-renTm; subTm-id; subTm-subTm; subTm-cong; extS
        ; Sub; Ren; Var; idₛ; renTm-renTm; _∘ᵣ_ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢⌜Nat⌝
        ; ty-Nat; ty-Hom; ty-El; ty-Π
        ; _≅ᵀ_; csymᵀ
        ; ξ-nsuc; ξ-Homˡ; ξ-natrecⁿ; ξ-natrecᶻ; βfst; βsnd
        ; _⟶_; _⟶*_; done; step; β; ξ-appˡ; natrec-zero; natrec-suc )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBVar using ( ren-as-sub; wk-sub-tm )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ; ⟶*-ren; ⟶*-sub )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus; n1; n2; n3 )
open import poc.OCP0009.NbEPDirDBExamplesDiv
  using ( monusTm; ⊢monus; monus-zero; monus-suc; pred-zero; pred-suc
        ; monus-computes )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( aStepT; aIHTat-sub )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asP )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoTm )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLTm; plusMonoLTm-sub )
open import poc.OCP0009.NbEPDirDBLibArithMonus
  using ( monusLtTm; monusLtTm-sub; ⊢desc-left; ⊢desc-right; pred* )

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

-- ★ SUBSTITUTING INTO THE MOTIVE-FORMER MOVES ONLY ITS PARAMETER.
--   `gcdG μ = Π (gcdIH μ) (El ⌜Nat⌝)` and `gcdIH μ = aIHTat PairT ⌜Nat⌝ msr μ`,
--   so `aIHTat-sub` does all the work: `PairT`/`⌜Nat⌝` are closed and `msr`
--   mentions only `vz`, which `extS σ` fixes, so all three ride through.
--
-- ⚠ NEEDED wherever a reduction's residue has to be read back as a motive —
--   a five-level substitution stack collapses by five of these.  Written at
--   its first use site (`…GcdLeMid`) and moved here, beside `gcdG`.
gcdG-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ : RTm Γ) →
           subTy σ (gcdG μ) ≡ gcdG (subTm σ μ)
gcdG-sub {σ = σ} μ = cong (λ T → Π T (El ⌜Nat⌝)) (aIHTat-sub PairT ⌜Nat⌝ msr μ)

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

-- ★★ THE SIBLING MOTIVE SLOTS ARE GENERALISED (`B`, `C`), 2026-08-16.
--   ⚠ Not gratuitous polymorphism: gcd's `StepExt` runs the SAME three
--   splits with the `Id`-motive `eqG …` where `⊢gcdStp` has `G1`/`G2`, and
--   these derivations must typecheck in both contexts.  They can, because
--   none of them ever LOOKS at that slot — every `there` below steps over
--   it to a `Nat` or the carrier.  Leaving `G1`/`G2` hard-wired would force
--   the caller to re-derive all of it.
⊢G2 : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} →
      ((((Γ ▹ PairT) ▹ Nat) ▹ B) ▹ Nat) ⊢ty G2
⊢G2 = ⊢gcdG (⊢plus (⊢var here) (⊢nsuc (⊢var (there (there here)))))

-- a = 0 : the answer is `b`.  ctx after the ⊢lam: [0]=ih [1]=G1 [2]=n' [3]=x
G2z : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
G2z = lam (nsuc (var (vs (vs vz))))

⊢G2z : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} →
       (((Γ ▹ PairT) ▹ Nat) ▹ B) ⊢ G2z
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

⊢G3 : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)} →
      ((((((Γ ▹ PairT) ▹ Nat) ▹ B) ▹ Nat) ▹ C) ▹ Nat) ⊢ty G3
⊢G3 =
  ⊢gcdG (⊢plus (⊢nsuc (⊢var (there (there here))))
               (⊢nsuc (⊢var (there (there (there (there here)))))))

-- a ≤ b : recurse at (a , b ∸ a).  SECOND component changes → ⊢desc-right.
-- ctx after the ⊢lam: [0]=ih [1]=G2 [2]=k' [3]=G1 [4]=n' [5]=x
--
-- ★ THE RECURSIVE CALL'S TWO ARGUMENTS ARE NAMED, and so is the
--   certificate's DERIVATION.  ⚠ Not cosmetic: the caller's `StepExt`
--   instantiates the pointwise hypothesis at exactly `(PAIRᶻ , CERTᶻ)` and
--   must supply BOTH their typings; inline, the certificate's derivation is
--   unreachable, and `subTm` does not invert so it cannot be recovered from
--   the branch afterwards.  Same reason `descS-peel` had to name the
--   library's certificate.  (2026-08-16, prerequisite 1 of gap A.)

-- the context the branch's BODY lives in — five binders plus the `⊢lam`'s
CΓz : (Γ : Ctx) (B : RTy (⌊ Γ ⌋ ∙ ∙)) (C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)) → Ctx
CΓz Γ B C = ((((( Γ ▹ PairT) ▹ Nat) ▹ B) ▹ Nat) ▹ C)
              ▹ gcdIH (plusTm (nsuc (var (vs vz))) (nsuc (var (vs (vs (vs vz))))))

-- [2]=k' and [4]=n' AT THE BODY'S DEPTH
KZ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
KZ = var (vs (vs vz))

NZ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
NZ = var (vs (vs (vs (vs vz))))

PAIRᶻ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
PAIRᶻ = pair (nsuc KZ) (monusTm (nsuc NZ) (nsuc KZ))

CERTᶻ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
CERTᶻ = plusMonoTm (monusLtTm NZ KZ) (nsuc KZ)

dkz : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)} → CΓz Γ B C ⊢ KZ ∷ Nat
dkz = ⊢var (there (there here))

dnz : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)} → CΓz Γ B C ⊢ NZ ∷ Nat
dnz = ⊢var (there (there (there (there here))))

⊢PAIRᶻ : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)} → CΓz Γ B C ⊢ PAIRᶻ ∷ PairT
⊢PAIRᶻ = ⊢pair ty-Nat (⊢nsuc dkz) (⊢monus (⊢nsuc dnz) (⊢nsuc dkz))

-- ★ the certificate, at the measure of the CALL, bounded by the measure of
--   the branch's own (split) carrier `suc k' + suc n'`.
⊢CERTᶻ : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)} → CΓz Γ B C ⊢ CERTᶻ
       ∷ Hom Nat (nsuc (plusTm (fst PAIRᶻ) (snd PAIRᶻ))) (plusTm (nsuc KZ) (nsuc NZ))
⊢CERTᶻ =
  ⊢conv (⊢desc-right dkz dnz)
        (csymᵀ (descConv (nsuc KZ) (monusTm (nsuc NZ) (nsuc KZ))
                         (plusTm (nsuc KZ) (nsuc NZ))))

G3z : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
G3z = lam (app (app (var vz) PAIRᶻ) CERTᶻ)

⊢G3z : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)} →
       (((((Γ ▹ PairT) ▹ Nat) ▹ B) ▹ Nat) ▹ C) ⊢ G3z
     ∷ gcdG (plusTm (nsuc (var (vs vz))) (nsuc (var (vs (vs (vs vz))))))
⊢G3z =
  ⊢lam (⊢gcdIH (⊢plus (⊢nsuc (⊢var (there here)))
                      (⊢nsuc (⊢var (there (there (there here)))))))
    (⊢app (⊢app (⊢var here) ⊢PAIRᶻ) ⊢CERTᶻ)

-- a > b : recurse at (a ∸ b , b).  FIRST component changes → ⊢desc-left.
-- ctx after the ⊢lam: [0]=ih [1]=G3 [2]=d [3]=G2 [4]=k' [5]=G1 [6]=n' [7]=x
-- ★ same treatment as `G3z` — see the note there.
CΓs : (Γ : Ctx) (B : RTy (⌊ Γ ⌋ ∙ ∙)) (C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙))
      (D : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)) → Ctx
CΓs Γ B C D = ((((((( Γ ▹ PairT) ▹ Nat) ▹ B) ▹ Nat) ▹ C) ▹ Nat) ▹ D)
                ▹ gcdIH (plusTm (nsuc (var (vs (vs (vs vz)))))
                                (nsuc (var (vs (vs (vs (vs (vs vz))))))))

-- [4]=k' and [6]=n' AT THE BODY'S DEPTH
KS : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
KS = var (vs (vs (vs (vs vz))))

NS : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
NS = var (vs (vs (vs (vs (vs (vs vz))))))

PAIRˢ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
PAIRˢ = pair (monusTm (nsuc KS) (nsuc NS)) (nsuc NS)

CERTˢ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
CERTˢ = plusMonoLTm (monusTm (nsuc KS) (nsuc NS)) (nsuc KS) (nsuc NS)
                    (monusLtTm KS NS)

dks : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)}
     {D : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)} → CΓs Γ B C D ⊢ KS ∷ Nat
dks = ⊢var (there (there (there (there here))))

dns : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)}
     {D : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)} → CΓs Γ B C D ⊢ NS ∷ Nat
dns = ⊢var (there (there (there (there (there (there here))))))

⊢PAIRˢ : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)}
     {D : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)} → CΓs Γ B C D ⊢ PAIRˢ ∷ PairT
⊢PAIRˢ = ⊢pair ty-Nat (⊢monus (⊢nsuc dks) (⊢nsuc dns)) (⊢nsuc dns)

⊢CERTˢ : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)}
     {D : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)} → CΓs Γ B C D ⊢ CERTˢ
       ∷ Hom Nat (nsuc (plusTm (fst PAIRˢ) (snd PAIRˢ))) (plusTm (nsuc KS) (nsuc NS))
⊢CERTˢ =
  ⊢conv (⊢desc-left dks dns)
        (csymᵀ (descConv (monusTm (nsuc KS) (nsuc NS)) (nsuc NS)
                         (plusTm (nsuc KS) (nsuc NS))))

G3s : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
G3s = lam (app (app (var vz) PAIRˢ) CERTˢ)

⊢G3s : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} {C : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙)}
       {D : RTy (⌊ Γ ⌋ ∙ ∙ ∙ ∙ ∙ ∙)} →
       (((((((Γ ▹ PairT) ▹ Nat) ▹ B) ▹ Nat) ▹ C) ▹ Nat) ▹ D) ⊢ G3s
     ∷ gcdG (plusTm (nsuc (var (vs (vs (vs vz)))))
                    (nsuc (var (vs (vs (vs (vs (vs vz))))))))
⊢G3s =
  ⊢lam (⊢gcdIH (⊢plus (⊢nsuc (⊢var (there (there (there here)))))
                      (⊢nsuc (⊢var (there (there (there (there (there here)))))))))
    (⊢app (⊢app (⊢var here) ⊢PAIRˢ) ⊢CERTˢ)

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

-- ★ THE THREE NESTED `⊢natrec`s, NAMED.  ⚠ Not cosmetic, and the same
--   lesson as `PAIRᶻ`/`CERTᶻ` above: `subTm` does not invert, so a caller
--   that needs one of these sub-derivations cannot recover it from
--   `⊢gcdStp`.  gcd's `StepExt` needs all three — each split has to re-type
--   its own `natrec` AT A VARIABLE SCRUTINEE (`⊢natrec-var`), which takes
--   exactly the motive and the two branch derivations.

⊢gcdInn2 : {Γ : Ctx} {B : RTy (⌊ Γ ⌋ ∙ ∙)} →
           ((((( Γ ▹ PairT) ▹ Nat) ▹ B) ▹ Nat) ▹ G2) ⊢ gcdInn2 ∷ subTy nrs G2
⊢gcdInn2 =
  ⊢natrec ⊢G3 ⊢G3z ⊢G3s
          (⊢monus (⊢nsuc (⊢var (there here)))
                  (⊢nsuc (⊢var (there (there (there here))))))

⊢gcdInn1 : {Γ : Ctx} → ((( Γ ▹ PairT) ▹ Nat) ▹ G1) ⊢ gcdInn1 ∷ subTy nrs G1
⊢gcdInn1 = ⊢natrec ⊢G2 ⊢G2z ⊢gcdInn2 (⊢fst (⊢var (there (there here))))

⊢gcdBody : {Γ : Ctx} →
           (Γ ▹ PairT) ⊢ gcdBody ∷ subTy (single (snd (var vz))) G1
⊢gcdBody = ⊢natrec ⊢G1 ⊢G1z ⊢gcdInn1 (⊢snd (⊢var here))

⊢gcdStp : {Γ : Ctx} → Γ ⊢ gcdStp ∷ aStepT PairT ⌜Nat⌝ msr
⊢gcdStp = ⊢lam ⊢PairT ⊢gcdBody

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
--   ⇒ so equation 2 is stated ONE CONSTRUCTOR IN, as `gcd (0 , suc b)`,
--     which IS reachable with `b` a genuine variable.
--   ★ DONE — see `gcd-a0-var` below.  The successor branch does thread the
--     bound predecessor through several binders, so the endpoint is `nsuc b`
--     only up to `wkS2` (depth TWO — `natrec-suc` binds the predecessor AND
--     the IH); that lemma is right below and the proof is one `subst`.

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

-- ★ depth THREE, the OTHER shape: two `extS`-layered substitutions over a
--   TRIPLE weakening.  This is the one the comparison branch's `b` slot
--   needs; `wkS3` above does not fit it (its renaming sits BETWEEN the two
--   substitutions, not under both).  Same recipe: collapse, then `wkGen`.
wkS2e : {Γ : Cx} {u₁ u₂ : RTm Γ} (t : RTm Γ) →
        subTm (extS (single u₂))
          (subTm (extS (extS (single u₁))) (renTm vs (renTm vs (renTm vs t))))
        ≡ renTm vs t
-- ⚠ NOT by the collapse recipe: fusing the renamings leaves a pointwise
--   goal that is FALSE at `vz` (the inner substitution's own slot).  The
--   working route is NATURALITY — `wk-sub-tm` walks each `extS` layer out
--   through its weakening, one layer at a time, and `wkS` finishes.
wkS2e {u₁ = u₁} {u₂ = u₂} t =
  trans (cong (subTm (extS (single u₂)))
              (trans (wk-sub-tm (extS (single u₁)) (renTm vs (renTm vs t)))
                     (cong (renTm vs)
                       (trans (wk-sub-tm (single u₁) (renTm vs t))
                              (cong (renTm vs) (wkS t))))))
    (trans (wk-sub-tm (single u₂) (renTm vs t)) (cong (renTm vs) (wkS t)))

-- ★ …and the depth-FOUR instance the `b` slot actually wants: `wkS2e`'s
--   shape with one more plain `single` on top.  By COMPOSITION again.
wkS3e : {Γ : Cx} {u₁ u₂ u₃ : RTm Γ} (t : RTm Γ) →
        subTm (single u₃)
          (subTm (extS (single u₂))
            (subTm (extS (extS (single u₁))) (renTm vs (renTm vs (renTm vs t)))))
        ≡ t
wkS3e {u₃ = u₃} t = trans (cong (subTm (single u₃)) (wkS2e t)) (wkS t)

-- ★★ READING A REDUCTION AS A TRACE.  `⟶*-trans` is associative, so a
--   RIGHT-ASSOCIATIVE infix version needs no grouping at all: an n-step
--   chain is n lines and ZERO nesting parens, instead of n nested
--   `⟶*-trans (…(…))` whose closing run has to be counted by hand.  The
--   intermediates stay IMPLICIT exactly as they were — this is only
--   notation, no new content.
infixr 5 _⟫_
_⟫_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
_⟫_ = ⟶*-trans

-- one reduction as a chain segment, so every line of a trace has the
-- same shape
one : {Γ : Cx} {t u : RTm Γ} → t ⟶ u → t ⟶* u
one r = step r done

-- ★★ THE PEEL FAMILY.  Each `pkN` walks ONE `extS` layer out through one
--   weakening (`wk-sub-tm`), and the `peelN`s are those composed.  This is
--   the shape the eliminator's leaf actually produces: N nested `natrec`
--   successor branches leave N stacked substitutions over N weakenings.
pk2 : {Γ : Cx} {u : RTm Γ} (t : RTm Γ) →
      subTm (extS (single u)) (renTm vs (renTm vs t)) ≡ renTm vs t
pk2 {u = u} t = trans (wk-sub-tm (single u) (renTm vs t)) (cong (renTm vs) (wkS t))

pk3 : {Γ : Cx} {u : RTm Γ} (t : RTm Γ) →
      subTm (extS (extS (single u))) (renTm vs (renTm vs (renTm vs t)))
      ≡ renTm vs (renTm vs t)
pk3 {u = u} t = trans (wk-sub-tm (extS (single u)) (renTm vs (renTm vs t)))
                      (cong (renTm vs) (pk2 t))

pk4 : {Γ : Cx} {u : RTm Γ} (t : RTm Γ) →
      subTm (extS (extS (extS (single u))))
        (renTm vs (renTm vs (renTm vs (renTm vs t))))
      ≡ renTm vs (renTm vs (renTm vs t))
pk4 {u = u} t = trans (wk-sub-tm (extS (extS (single u)))
                                 (renTm vs (renTm vs (renTm vs t))))
                      (cong (renTm vs) (pk3 t))

peel4 : {Γ : Cx} {u₁ u₂ u₃ u₄ : RTm Γ} (t : RTm Γ) →
        subTm (single u₄)
          (subTm (extS (single u₃))
            (subTm (extS (extS (single u₂)))
              (subTm (extS (extS (extS (single u₁))))
                (renTm vs (renTm vs (renTm vs (renTm vs t)))))))
        ≡ t
peel4 {u₂ = u₂} {u₃ = u₃} {u₄ = u₄} t =
  trans (cong (subTm (single u₄))
          (trans (cong (subTm (extS (single u₃)))
                   (trans (cong (subTm (extS (extS (single u₂)))) (pk4 t)) (pk3 t)))
                 (pk2 t)))
        (wkS t)

pk5 : {Γ : Cx} {u : RTm Γ} (t : RTm Γ) →
      subTm (extS (extS (extS (extS (single u)))))
        (renTm vs (renTm vs (renTm vs (renTm vs (renTm vs t)))))
      ≡ renTm vs (renTm vs (renTm vs (renTm vs t)))
pk5 {u = u} t = trans (wk-sub-tm (extS (extS (extS (single u))))
                                 (renTm vs (renTm vs (renTm vs (renTm vs t)))))
                      (cong (renTm vs) (pk4 t))

pk6 : {Γ : Cx} {u : RTm Γ} (t : RTm Γ) →
      subTm (extS (extS (extS (extS (extS (single u))))))
        (renTm vs (renTm vs (renTm vs (renTm vs (renTm vs (renTm vs t))))))
      ≡ renTm vs (renTm vs (renTm vs (renTm vs (renTm vs t))))
pk6 {u = u} t = trans (wk-sub-tm (extS (extS (extS (extS (single u)))))
                        (renTm vs (renTm vs (renTm vs (renTm vs (renTm vs t))))))
                      (cong (renTm vs) (pk5 t))

-- ★ …and depth SIX, which is what the SECOND argument's slot needs: `b`
--   sits under all six binders the three nested `natrec`s introduce.
peel6 : {Γ : Cx} {u₁ u₂ u₃ u₄ u₅ u₆ : RTm Γ} (t : RTm Γ) →
        subTm (single u₆)
          (subTm (extS (single u₅))
            (subTm (extS (extS (single u₄)))
              (subTm (extS (extS (extS (single u₃))))
                (subTm (extS (extS (extS (extS (single u₂)))))
                  (subTm (extS (extS (extS (extS (extS (single u₁))))))
                    (renTm vs (renTm vs (renTm vs
                      (renTm vs (renTm vs (renTm vs t)))))))))))
        ≡ t
peel6 {u₂ = u₂} {u₃ = u₃} {u₄ = u₄} {u₅ = u₅} {u₆ = u₆} t =
  trans (cong (subTm (single u₆))
          (trans (cong (subTm (extS (single u₅)))
                   (trans (cong (subTm (extS (extS (single u₄))))
                            (trans (cong (subTm (extS (extS (extS (single u₃)))))
                                     (trans (cong (subTm (extS (extS (extS (extS (single u₂))))))
                                              (pk6 t))
                                            (pk5 t)))
                                   (pk4 t)))
                          (pk3 t)))
                 (pk2 t)))
        (wkS t)

-- ⚠ three slots move at once in the leaf, so the transport needs a
--   three-argument congruence; the project has only `cong`.
cong₃g : {A B C D : Set} (f : A → B → C → D)
         {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} →
         a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃g f refl refl refl = refl

-- ⚠ …and the hypothesis moves in TWO slots at once.  Doing it as nested
--   `subst`s leaves the untouched slot as a `_` under a binder, which Agda
--   cannot solve; taking both equations at once keeps every implicit
--   first-order, so the use site pins them.
mhAt : {Γ : Cx} {A₁ A₂ B₁ B₂ r : RTm Γ} → A₁ ≡ A₂ → B₁ ≡ B₂ →
       monusTm (nsuc A₂) (nsuc B₂) ⟶* r →
       monusTm (nsuc A₁) (nsuc B₁) ⟶* r
mhAt refl refl h = h

-- ⚠ likewise for the chain's TARGET: `subst (λ z → _ ⟶* z)` leaves the
--   source as a meta Agda will not solve, because it only appears under a
--   `subTm`.  Taking the source implicitly lets the USE SITE supply it.
redAt : {Γ : Cx} {t u₁ u₂ : RTm Γ} → u₁ ≡ u₂ → t ⟶* u₁ → t ⟶* u₂
redAt refl h = h

-- ⚠ …and one that rewrites only the FUNCTION of an application, leaving the
--   argument alone.  `app` is a CONSTRUCTOR, so this `u` — unlike anything
--   under a `subTm` — really is recoverable by unification.
appAt : {Γ : Cx} {t f₁ f₂ : RTm Γ} (u : RTm Γ) → f₁ ≡ f₂ →
        t ⟶* app f₁ u → t ⟶* app f₂ u
appAt u refl h = h

-- ★★★ THE STEP EQUATIONS' SHAPE — SHARED by both recursive branches.  The certificate `c` is EXISTENTIAL, and
--   that is a deliberate statement of scope, not a dodge:
--
--   · WHAT IS CLAIMED: the step function, at `(suc a , suc b)` with the
--     descent `a ∸ b` landing on `suc d`, reduces to the RECURSIVE CALL
--     `ih (a ∸ b , suc b)`.  Both components are pinned exactly.  That is
--     the defining equation's computational content.
--   · WHAT IS NOT: which well-foundedness certificate the call carries.
--   · WHY NOT: `monusLtTm a b = natrec (reflTm a) (… w (w a) …) b` uses `a`
--     UNDER TWO BINDERS, so `subTm` does not commute with it definitionally.
--     Identifying the certificate needs substitution-naturality for every
--     arithmetic template (`commTm`, `plusMonoTm`, `trHomˡ/ʳ`, `congS`, …).
--     That suite is worth building, but it is a separate piece of work and
--     it is NOT what "gcd satisfies its defining equations" means.
-- ★★ THE CERTIFICATE SLOT'S CAST — the twin of `appAt`.
--
-- ⚠ `appAt` fixes the FUNCTION half of `app (app ih PAIR) CERT`; nothing
--   fixed the CERT half, so a `RecCall`'s certificate came out as `CERTˢ`
--   under EIGHT substitutions.  A caller that must TYPE it then cannot —
--   `subTm` does not invert — and RECONSTRUCTING the chain afterwards is
--   worse: asking Agda to accept the reconstruction as the same term runs
--   >40min (measured 2026-08-17, both at a use site and in `…GcdCert`).
--   ⭐ So put the clean form in AT CONSTRUCTION.  Then `recCert` IS
--   `gtCert a' b'`, which is `⊢desc-left`'s subject, and no comparison
--   exists anywhere.
certAt : {Γ : Cx} {t f u₁ u₂ : RTm Γ} → u₁ ≡ u₂ → t ⟶* app f u₁ → t ⟶* app f u₂
certAt refl h = h

gtCert : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
gtCert a' b' = plusMonoLTm (monusTm (nsuc a') (nsuc b')) (nsuc a') (nsuc b')
                           (monusLtTm a' b')

data RecCall {Γ : Cx} (t ih A B : RTm Γ) : Set where
  recCall : (c : RTm Γ) → t ⟶* app (app ih (pair A B)) c → RecCall t ih A B

-- ★ …and its projections, so a caller can feed the certificate to a lemma
--   that needs it as a FAMILY in `ih` (which `aux-cycle` does).
recCert : {Γ : Cx} {t ih A B : RTm Γ} → RecCall t ih A B → RTm Γ
recCert (recCall c _) = c

recRed : {Γ : Cx} {t ih A B : RTm Γ} (r : RecCall t ih A B) →
         t ⟶* app (app ih (pair A B)) (recCert r)
recRed (recCall c p) = p

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

-- ★★★★ THE ARBITRARY-TERM FORM.  Every chain step PINNED via
--   `gcdBody`/`gcdInn1`/`gcdInn2`, so the target is stable; the hypothesis
--   is carried to the substituted `a'` by `⟶*-ren` plus one `cong`.
gcd-gt-term : {Γ : Cx} (a' b' d ih : RTm Γ) →
              monusTm (nsuc a') (nsuc b') ⟶* nsuc d →
              RecCall (app (app gcdStp (pair (nsuc a') (nsuc b'))) ih) ih
                     (monusTm (nsuc a') (nsuc b')) (nsuc b')
gcd-gt-term {Γ} a' b' d ih mh = recCall (gtCert a' b') (certAt certEq
  --  each line is ONE reduction of the trace, read top to bottom
  ( one (ξ-appˡ (β gcdBody gX))                         -- unfold the step fn
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βsnd _ _)))               -- scrutinee snd = suc b
  ⟫ ⟶*-appˡ (one (natrec-suc (subTm (single gX) G1z)
                             (subTm (extS (extS (single gX))) gcdInn1) b'))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βfst _ _)))               -- scrutinee fst = suc a
  ⟫ ⟶*-appˡ (one (natrec-suc _ _ _))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (mhAt (wkS3 a') (wkS3e b') mh)) -- run the descent a∸b
  ⟫ ⟶*-appˡ (one (natrec-suc _ _ _))                    -- it hit suc d ⇒ G3s
  ⟫ appAt _                                             -- …and feed in ih
      (cong₃g (λ I A B → app I (pair (monusTm (nsuc A) (nsuc B)) (nsuc B)))
              refl
              (trans (peel4 {u₁ = R₂} {u₂ = d} {u₃ = R₃} {u₄ = ih} W)
                     (wkS2 {u = R₁} {v = b'} a'))
              (peel6 {u₁ = R₁} {u₂ = W} {u₃ = R₂}
                     {u₄ = d} {u₅ = R₃} {u₆ = ih} b'))
      (one (β _ ih))
  ))
  where
    gX : RTm Γ
    gX = pair (nsuc a') (nsuc b')

    -- ★★★ THE FOUR INTERMEDIATE SCRUTINEES, NAMED.  Agda cannot INFER these:
    --   they sit under `subTm`, and a substitution is a FUNCTION, so the
    --   unifier has nothing to invert — every attempt to leave them as `_`
    --   leaves an unsolved meta.  Named, each one is ordinary text, and note
    --   they nest: R₂ is written with R₁, R₃ with both.  That is the same
    --   move that made `gcdBody`'s branches pinnable, one level deeper.
    R₁ : RTm Γ
    R₁ = natrec (subTm (single gX) G1z)
                (subTm (extS (extS (single gX))) gcdInn1) b'

    -- the descent's first argument, `a ∸ b`, after the outer substitutions
    W : RTm Γ
    W = subTm (single R₁) (subTm (extS (single b')) (renTm vs (renTm vs a')))

    R₂ : RTm Γ
    R₂ = natrec (subTm (single R₁)
                  (subTm (extS (single b')) (subTm (extS (extS (single gX))) G2z)))
                (subTm (extS (extS (single R₁)))
                  (subTm (extS (extS (extS (single b'))))
                    (subTm (extS (extS (extS (extS (single gX))))) gcdInn2)))
                W

    R₃ : RTm Γ
    R₃ = natrec (subTm (single R₂)
                  (subTm (extS (single W))
                    (subTm (extS (extS (single R₁)))
                      (subTm (extS (extS (extS (single b'))))
                        (subTm (extS (extS (extS (extS (single gX))))) G3z)))))
                (subTm (extS (extS (single R₂)))
                  (subTm (extS (extS (extS (single W))))
                    (subTm (extS (extS (extS (extS (single R₁)))))
                      (subTm (extS (extS (extS (extS (extS (single b'))))))
                        (subTm (extS (extS (extS (extS (extS (extS (single gX)))))))
                               G3s)))))
                d


    ------------------------------------------------------------------------
    -- ★★★★ THE CERTIFICATE, IN CLEAN FORM — proved HERE, where `R₁`/`W`/
    --      `R₂`/`R₃` are already bound, so nothing is reconstructed.
    --
    -- ★ Push the substitution through the certificate by NATURALITY
    --   (`plusMonoLTm-sub`/`monusLtTm-sub`), one layer at a time, then peel
    --   the arguments with the SAME `peel4`/`peel6`/`wkS2` the `pair` slot
    --   uses above.  ⚠ Arguments passed EXPLICITLY: recovering `x` from
    --   `subTm σ x` needs `subTm` inverted, which is the whole problem.
    ------------------------------------------------------------------------

    τ₁ = extS (extS (extS (extS (extS (extS (extS (single gX)))))))
    τ₂ = extS (extS (extS (extS (extS (extS (single b'))))))
    τ₃ = extS (extS (extS (extS (extS (single R₁)))))
    τ₄ = extS (extS (extS (extS (single W))))
    τ₅ = extS (extS (extS (single R₂)))
    τ₆ = extS (extS (single d))
    τ₇ = extS (single R₃)
    τ₈ = single ih

    pushPM : {Γ₁ Γ₂ : Cx} {t x y c q : RTm Γ₁} → t ≡ plusMonoLTm x y c q →
             (σ : Sub Γ₁ Γ₂) →
             subTm σ t ≡ plusMonoLTm (subTm σ x) (subTm σ y) (subTm σ c) (subTm σ q)
    pushPM {x = x} {y = y} {c = c} {q = q} e σ =
      trans (cong (subTm σ) e) (plusMonoLTm-sub x y c q)

    pushML : {Γ₁ Γ₂ : Cx} {t x y : RTm Γ₁} → t ≡ monusLtTm x y → (σ : Sub Γ₁ Γ₂) →
             subTm σ t ≡ monusLtTm (subTm σ x) (subTm σ y)
    pushML {x = x} {y = y} e σ = trans (cong (subTm σ) e) (monusLtTm-sub x y)

    e1 = plusMonoLTm-sub {σ = τ₁} (monusTm (nsuc KS) (nsuc NS))
                         (nsuc KS) (nsuc NS) (monusLtTm KS NS)
    e2 = pushPM e1 τ₂
    e3 = pushPM e2 τ₃
    e4 = pushPM e3 τ₄
    e5 = pushPM e4 τ₅
    e6 = pushPM e5 τ₆
    e7 = pushPM e6 τ₇
    e8 = pushPM e7 τ₈

    f1 = monusLtTm-sub {σ = τ₁} KS NS
    f2 = pushML f1 τ₂
    f3 = pushML f2 τ₃
    f4 = pushML f3 τ₄
    f5 = pushML f4 τ₅
    f6 = pushML f5 τ₆
    f7 = pushML f6 τ₇
    f8 = pushML f7 τ₈

    pA = trans (peel4 {u₁ = R₂} {u₂ = d} {u₃ = R₃} {u₄ = ih} W)
               (wkS2 {u = R₁} {v = b'} a')
    pB = peel6 {u₁ = R₁} {u₂ = W} {u₃ = R₂}
               {u₄ = d} {u₅ = R₃} {u₆ = ih} b'

    congPM : {x x' y y' c c' q q' : RTm Γ} →
             x ≡ x' → y ≡ y' → c ≡ c' → q ≡ q' →
             plusMonoLTm x y c q ≡ plusMonoLTm x' y' c' q'
    congPM refl refl refl refl = refl

    certEq = trans e8 (congPM (cong₂ (λ A B → monusTm (nsuc A) (nsuc B)) pA pB)
                              (cong nsuc pA) (cong nsuc pB)
                              (trans f8 (cong₂ monusLtTm pA pB)))

-- ★★★ NON-VACUITY.  A conditional lemma proves NOTHING until its premise
--   is discharged — that is exactly what killed the earlier `gcd-gt-gen`
--   (see the ⛔ block below), so the equation above does not count until an
--   instance exists.  Here is one, and `d` in it is a genuine VARIABLE:
--   the equation is being used at a term, not at a numeral.
gt-mh-1 : {Γ : Cx} (d : RTm Γ) → monusTm (nsuc (nsuc d)) (nsuc nzero) ⟶* nsuc d
gt-mh-1 d = ⟶*-trans (monus-suc (nsuc (nsuc d)) nzero)
              (⟶*-trans (pred* (monus-zero (nsuc (nsuc d)))) (pred-suc (nsuc d)))

gcd-gt-at-1 : {Γ : Cx} (d ih : RTm Γ) →
              RecCall (app (app gcdStp (pair (nsuc (nsuc d)) (nsuc nzero))) ih) ih
                     (monusTm (nsuc (nsuc d)) (nsuc nzero)) (nsuc nzero)
gcd-gt-at-1 d ih = gcd-gt-term (nsuc d) nzero d ih (gt-mh-1 d)

-- ⚠ THE REACH, stated precisely so the result is not over-read: `mh` forces
--   the descent to LAND on a successor, and `monusTm` recurses on its
--   SECOND argument, so discharging it needs that second argument to be a
--   numeral.  Hence the equation is proved for an ARBITRARY `a` (any term,
--   here `suc d`) and a NUMERAL `b`.  That is strictly stronger than the
--   literal-only tests — `a` is no longer ground — and strictly weaker than
--   both arguments arbitrary, which `monusTm`'s recursion structure blocks
--   until a `⊢`-level (propositional) monus lemma replaces the reduction.

-- ★★★ THE ARBITRARY-TERM FORM: LANDED (`gcd-gt-term` above).  Kept here is
--   the record of WHAT MADE IT WORK, because two of the three obstacles
--   were mis-diagnosed for a long time.
--
-- 1. NAMING, not transports.  `gcdBody`/`gcdInn1`/`gcdInn2`, then
--    `R₁`/`R₂`/`R₃`/`W` in the `where` block.  Agda cannot INFER any of
--    these: they occur only under `subTm`, and a substitution is a
--    FUNCTION, so the unifier has nothing to invert.  Every "leave it as
--    `_`" attempt produced an unsolved meta, never a wrong one — that is
--    the signature of this failure mode, and it is what a dozen earlier
--    attempts kept re-discovering.
--
-- 2. NATURALITY, not collapse.  The peel family (`pk2`…`pk6`,
--    `peel4`/`peel6`) walks ONE `extS` layer out through ONE weakening via
--    `wk-sub-tm`.  The collapse recipe (`subTm-subTm` + `renTm-renTm` +
--    a pointwise `refl`) that `wkS2` uses does NOT extend here: fusing the
--    renamings leaves a pointwise goal that is FALSE at `vz`.
--
-- 3. HELPERS WITH THE RIGHT IMPLICITS.  `mhAt`/`redAt`/`appAt` exist for
--    one reason: a `subst` motive containing `_` under a binder is not
--    solvable, whereas the same equation taken as a first-order argument
--    lets the USE SITE supply everything.
--
-- ⚠ AND WHAT IS NOT CLAIMED: the certificate is existential (`RecCall`),
--   and `b` must be a numeral.  Both limits are stated where they bite —
--   see `RecCall`'s comment and the note after `gcd-gt-at-1`.
--
-- ⚠ ROUTE 3 (split + substitute + splice) was abandoned, not refuted.  It
--   also reaches the same wall: `subTm σ (gtRHS …) ≡ gtRHS …` needs
--   substitution-naturality for the arithmetic templates either way.
------------------------------------------------------------------------

-- ⚠ THE EARLIER GENERIC FORM (`gcd-gt-gen`, at the two outermost
--   VARIABLES) IS DELETED, not moved.  It was VACUOUS — `monusTm` recurses
--   on its second argument, so its `mh` premise cannot be discharged at a
--   variable `b` — and `gcd-gt-term` supersedes it at arbitrary terms with
--   a real instance (`gcd-gt-at-1`).  Keeping a vacuous lemma around only
--   invites it being cited as evidence.

------------------------------------------------------------------------
-- ★★★★ EQUATION 4 — `a ≤ b` recurses at `(a , b ∸ a)`, AT VARIABLES.
--   Same shape, other branch: the comparison reaching ZERO selects `G3z`.
------------------------------------------------------------------------

gcd-le-term : {Γ : Cx} (a' b' ih : RTm Γ) →
              monusTm (nsuc a') (nsuc b') ⟶* nzero →
              RecCall (app (app gcdStp (pair (nsuc a') (nsuc b'))) ih) ih
                      (nsuc a') (monusTm (nsuc b') (nsuc a'))
gcd-le-term {Γ} a' b' ih mh = recCall _
  --  identical trace to equation 3 until the descent lands: ZERO, not suc
  ( one (ξ-appˡ (β gcdBody gX))                         -- unfold the step fn
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βsnd _ _)))               -- scrutinee snd = suc b
  ⟫ ⟶*-appˡ (one (natrec-suc (subTm (single gX) G1z)
                             (subTm (extS (extS (single gX))) gcdInn1) b'))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βfst _ _)))               -- scrutinee fst = suc a
  ⟫ ⟶*-appˡ (one (natrec-suc _ _ _))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (mhAt (wkS3 a') (wkS3e b') mh)) -- run the descent a∸b
  ⟫ ⟶*-appˡ (one (natrec-zero _ _))                     -- it hit ZERO ⇒ G3z
  ⟫ appAt _                                             -- …and feed in ih
      (cong₃g (λ I A B → app I (pair (nsuc A) (monusTm (nsuc B) (nsuc A))))
              refl
              (trans (wkS2 {u = ih} {v = R₂} W)
                     (wkS2 {u = R₁} {v = b'} a'))
              (peel4 {u₁ = R₁} {u₂ = W} {u₃ = R₂} {u₄ = ih} b'))
      (one (β _ ih))
  )
  where
    gX : RTm Γ
    gX = pair (nsuc a') (nsuc b')

    R₁ : RTm Γ
    R₁ = natrec (subTm (single gX) G1z)
                (subTm (extS (extS (single gX))) gcdInn1) b'

    W : RTm Γ
    W = subTm (single R₁) (subTm (extS (single b')) (renTm vs (renTm vs a')))

    R₂ : RTm Γ
    R₂ = natrec (subTm (single R₁)
                  (subTm (extS (single b')) (subTm (extS (extS (single gX))) G2z)))
                (subTm (extS (extS (single R₁)))
                  (subTm (extS (extS (extS (single b'))))
                    (subTm (extS (extS (extS (extS (single gX))))) gcdInn2)))
                W

-- ★★★ NON-VACUITY for equation 4 — and note what it CANNOT be.
--
-- ⚠⚠ THE REACH HERE IS STRICTLY SHORTER THAN EQUATION 3's, and the reason
--   is structural, not laziness.  `mh` demands the descent reach ZERO.
--   With `b` a numeral the descent computes to `pred…pred (suc a)`, i.e.
--   to `a`, so `mh` forces `a ⟶* zero` — and a VARIABLE never reduces.
--   Equation 3 escaped this: it demands `⟶* suc d`, which `a := suc d`
--   satisfies with `d` a genuine variable.  So:
--
--     equation 3 : arbitrary `a` (a variable survives), numeral `b`
--     equation 4 : `a` and `b` both forced GROUND
--
--   ⇒ equation 4 at real variables is UNREACHABLE through a reduction
--     premise.  It needs the propositional route (a `⊢`-level monus/order
--     hypothesis instead of `⟶*`), which is the same work that lifts `b`
--     off numerals in equation 3.  The theorem above is stated at
--     arbitrary terms and is ready for that hypothesis; only the WITNESS
--     below is ground.
le-mh-1 : {Γ : Cx} → monusTm {Γ} (nsuc nzero) (nsuc nzero) ⟶* nzero
le-mh-1 = ⟶*-trans (monus-suc (nsuc nzero) nzero)
            (⟶*-trans (pred* (monus-zero (nsuc nzero))) (pred-suc nzero))

gcd-le-at-1 : {Γ : Cx} (ih : RTm Γ) →
              RecCall (app (app gcdStp (pair (nsuc nzero) (nsuc nzero))) ih) ih
                      (nsuc nzero) (monusTm (nsuc nzero) (nsuc nzero))
gcd-le-at-1 ih = gcd-le-term nzero nzero ih le-mh-1

leRHS : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
leRHS ih A B = app (app ih (pair (nsuc A) (monusTm (nsuc B) (nsuc A))))
                   (plusMonoTm (monusLtTm B A) (nsuc A))

-- ⚠ THE EARLIER GENERIC FORM (`gcd-le-gen`) IS DELETED for the same reason
--   `gcd-gt-gen` was: VACUOUS, and superseded by `gcd-le-term` above, which
--   is stated at arbitrary terms AND has an instance.

------------------------------------------------------------------------
-- ★ THE VACUITY POST-MORTEM (kept: the two lemmas it dissects are gone,
--   but the TRAP is the thing worth remembering).
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
