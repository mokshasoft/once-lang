------------------------------------------------------------------------
-- OCP-0009 — gcd's `StepExt`: THE CALLER'S HALF OF GAP A.
--
-- ★ WHAT THIS IS FOR.  `NbEPDirDBLibAmrec.irr-ind`/`amrec-unfold-Id` are
--   CONDITIONAL on `StepExt Δ A cM m stp` — "the step does not look at
--   WHICH ih it is given, only at what the ih computes".  The library half
--   is done; this module discharges the hypothesis for `gcdStp`, which is
--   the last thing between the tree and gap A (defining equations 3/4 at
--   VARIABLES rather than numerals).
--
-- ⚠ IT IS NOT ONE INSTANTIATION.  `StepExt` quantifies over an ARBITRARY
--   carrier `a` and `irr-ind` consumes it at a VARIABLE, but `gcdStp`
--   reduces only at a constructor-headed carrier: at a neutral `a` all
--   three scrutinees (`snd a`, `fst a`, `a ∸ b`) are stuck.  There is no
--   funext in this kernel, so the two stuck neutrals cannot be related by a
--   congruence.  The route is to SPLIT: `natrec` proves `P(t)` for a
--   neutral `t` perfectly well, so abstract each scrutinee out of the goal
--   and recurse on it.  Three nested splits, four leaves — two IH-free
--   (both sides literally equal) and two using the pointwise hypothesis
--   once each, at `(PAIRᶻ , CERTᶻ)` resp. `(PAIRˢ , CERTˢ)`.
--
-- ⚠⚠ AND THE SPLIT MOTIVES CARRY THE IHs — not an order hypothesis.
--   The 2026-08-15 design held `ih₁`/`ih₂` FIXED at `μ a` across the three
--   splits, and then hit a wall: a `natrec` on `snd a` hands its successor
--   branch a fresh `n'` but NOT the equation `snd a = nsuc n'`, so the
--   leaf's certificate — which `⊢CERTᶻ` states at `plusTm (nsuc k') (nsuc n')`
--   — could not be re-stated at `μ a`.  Its fix was to carry
--   `nsuc n' ≤ snd a` in the motive and rebuild by `ordtr` plus two-sided
--   monotonicity of `plusTm`.
--
--   ⭐ THAT WRINKLE DOES NOT ARISE HERE.  `⊢gcdStp`'s own three `natrec`
--   motives already carry `gcdG (plusTm …)`, i.e. the IH type AT THE
--   SPLIT-DEPENDENT BOUND — `G1` at `plusTm (fst x) z₁`, `G2` at
--   `plusTm z₂ (nsuc n')`, `G3` at `plusTm (nsuc k') (nsuc n')`.  Mirror
--   that: let the split motives quantify the two IHs and the pointwise
--   hypothesis internally, so each branch RECEIVES them at its own bound.
--   At the leaf the IH's bound is then literally `plusTm (nsuc k') (nsuc n')`
--   and `⊢CERTᶻ` is EXACTLY the certificate `⊢app` wants — no transport, no
--   rebuild, no order hypothesis.  `NbEPDirDBLibArithLe` is not needed on
--   this route; it stays as a general lemma.
--
--   ⚠ What makes this possible is `pwIntro` below, and nothing else: the
--   hypothesis has to be a TERM before it can ride a motive, and turning
--   the meta-level premise into a term is exactly what the 2026-08-16
--   renaming-indexed `StepPW` unblocked.
--
-- ★ STATUS.  Under construction — see the section markers.  Everything
--   above `THE PIECES` is built and green.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdStepExt where

-- ★ re-exported: these live in `…LibNatrec` now, but callers (A1/A2)
--   import them from here, so keep the name available.
open import poc.OCP0009.NbEPDirDBLibNatrec
  using ( ⊢natrec-var; Ren⊢-id ) public

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π; Id
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Ren; renTm; renTy; Sub; subTm; subTy; extR; extS; Id-cong₃
        ; subTy-renTy; renTy-subTy; subTy-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _∋_∷_; _⊢ty_; ⊢var; here; there; ⊢lam; ⊢app; ⊢nsuc; ⊢natrec
        ; ⊢fst; ⊢snd; ⊢nzero; ⊢idrefl; natrec-zero; natrec-suc
        ; ⊢conv; _≅ᵀ_; csymᵀ
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Id; ⊢⌜Nat⌝
        ; _⟶_; _⟶*_; done; step; β; ξ-appˡ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ∋-cast; Ren⊢; Ren⊢-ext; ren-ty; ren-lemma; ⊢[] )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; StepExt; StepPW; wR; renren; renTy-idR
        ; subrenTy; aIHTat-ren; aIHTat-sub; idOfRed )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w; sub-w²; sub-w³; ren-w )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asP )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; stepᵀ; doneᵀ; red→≅ᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBLibIHCall using ( appIHat )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; msr; ⊢msr; gcdIH; ⊢gcdIH; gcdG; ⊢gcdG
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1; ⊢gcdBody
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s; PAIRᶻ; ⊢PAIRᶻ; CERTᶻ; ⊢CERTᶻ
        ; PAIRˢ; ⊢PAIRˢ; CERTˢ; ⊢CERTˢ )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )

------------------------------------------------------------------------
-- ★ RENAMING-INVARIANCE OF THE STEP.
--
-- `StepExt` is CONTEXT-POLYMORPHIC: it states its conclusion about
-- `renTm ρ stp` at an arbitrary weakening `ρ` of the ambient context, so
-- every leaf below has to know that `gcdStp` is unmoved by one.  `gcdStp`
-- is closed, but "closed" is not a judgement this syntax has — what makes
-- it work is finer and cheaper: every variable in `gcdStp` sits under
-- strictly more binders than its own index, so each `extR` peels one `vs`
-- and `ρ` is never reached.  That is a COMPUTATION, not an induction.
--
-- ⚠ The `w (w a)` inside `monusLtTm` would NOT collapse for an abstract
--   `a` (`renTm` does not fuse definitionally), but gcd instantiates it at
--   a concrete variable, where it does.
------------------------------------------------------------------------

ren-gcdStp : {Γ Δ : Cx} (ρ : Ren Γ Δ) → renTm ρ gcdStp ≡ gcdStp
ren-gcdStp ρ = refl

------------------------------------------------------------------------
-- ★★ THE GOAL, IN THE FORM THE SPLITS WILL SEE IT.
--
-- `StepExt`'s conclusion is stated in `renTm ρ stp`, `renTm (extR ρ) cM`
-- and `subTm (single a) …` — none of which a caller wants to look at.  For
-- gcd all three COLLAPSE, and definitionally: `cM = ⌜Nat⌝` is closed, the
-- measure never reaches the conclusion, and the step is renaming-invariant
-- by `ren-gcdStp`.  This lemma is the receipt — it is the identity function,
-- and that it typechecks is the claim.
--
-- ⇒ everything below may be written about `app (app gcdStp a) ihᵢ` and
--   `El ⌜Nat⌝`, with no renaming residue anywhere.
------------------------------------------------------------------------

goal-shape : {Δ Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (a ih₁ ih₂ : RTm ⌊ Θ ⌋) →
             Prv Θ (Id (El ⌜Nat⌝) (app (app gcdStp a) ih₁)
                                  (app (app gcdStp a) ih₂)) →
             Prv Θ (Id (El (subTm (single a) (renTm (extR ρ) (⌜Nat⌝ {⌊ Δ ⌋ ∙}))))
                       (app (app (renTm ρ gcdStp) a) ih₁)
                       (app (app (renTm ρ gcdStp) a) ih₂))
goal-shape a ih₁ ih₂ p = p

------------------------------------------------------------------------
-- ★ THE FIRST REDUCTION — β at the carrier, once, under the `ih`.
--
-- ⚠ The body is NAMED (`gcdAt`), for the reason `gcdBody` is named in
--   `…GcdStep`: `β _ a` leaves the lam body an unsolved meta as soon as the
--   chain is split, and every split below splits this chain.
------------------------------------------------------------------------

gcdAt : {Γ : Cx} → RTm Γ → RTm Γ
gcdAt a = subTm (single a) gcdBody

-- ★ …and it IS the three-way `natrec`, definitionally.  `subTm` distributes
--   through `natrec` structurally, and the scrutinee `snd (var vz)` lands on
--   the carrier with nothing left over.
gcdAt-is : {Γ : Cx} (a : RTm Γ) →
           gcdAt a ≡ natrec (subTm (single a) G1z)
                            (subTm (extS (extS (single a))) gcdInn1)
                            (snd a)
gcdAt-is a = refl

red-β : {Γ : Cx} (a ih : RTm Γ) → app (app gcdStp a) ih ⟶* app (gcdAt a) ih
red-β a ih = step (ξ-appˡ (β gcdBody a)) done

------------------------------------------------------------------------
-- ★★★ INTERNALISING THE POINTWISE HYPOTHESIS — the linchpin.
--
-- ⚠ THIS IS WHAT THE 2026-08-16 GENERALISATION BOUGHT, and it is worth
--   more than the leaf instantiations it was scoped for.  With the premise
--   stated at `Θ` only, building this term was CIRCULAR: the two `⊢lam`s
--   put you at `Θ ▹ PairT ▹ Hom …`, and that is exactly where the premise
--   was unavailable.  Renaming-indexed, it is a two-line instantiation at
--   `ϑ = vs ∘ vs`.
--
-- ★ AND IT CHANGES THE WHOLE SPLIT DESIGN.  Once the hypothesis is a TERM,
--   it can ride the split motives as a `Π`-bound variable alongside the two
--   IHs — so each branch RECEIVES its own IHs at its own bound, exactly as
--   `⊢gcdStp`'s three `natrec` motives already carry `gcdG (plusTm …)`.
--   See the note on `eqG` below for why that removes the 2026-08-15 wrinkle
--   rather than solving it.
------------------------------------------------------------------------

-- ★ `vs` twice, fused.  ⚠ `renren`'s three renamings are all implicit and
--   none is determined by the argument, so this has to be pinned once and
--   reused — inline, it blocks on `renTm _ρ a != a`.
ww : {Γ : Cx} (t : RTm Γ) → w (w t) ≡ renTm (λ v → vs (vs v)) t
ww t = renren {ϑ = vs} {ρ = vs} {ρ' = λ v → vs (vs v)} (λ _ → refl) t

-- (`Ren⊢-id` moved to `…LibNatrec` — general, not gcd-specific.)

-- `(y : Pair) (q : μ y < μa) → ih₁ y q ≡ ih₂ y q`, INTERNALLY
-- ⚠ indexed by a RAW context `Cx`, not a `Ctx`: it carries no typing
--   information, and the split motives below need it at depths that are not
--   `⌊ _ ⌋` of anything.
pwT : {Γ : Cx} (μa i₁ i₂ : RTm Γ) → RTy Γ
pwT μa i₁ i₂ =
  Π PairT
    (Π (Hom Nat (nsuc msr) (w μa))
       (Id (El ⌜Nat⌝) (app (app (w (w i₁)) (var (vs vz))) (var vz))
                      (app (app (w (w i₂)) (var (vs vz))) (var vz))))

pwIntro : {Δ Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {a ih₁ ih₂ : RTm ⌊ Θ ⌋} →
          Θ ⊢ subTm (single a) msr ∷ Nat →
          StepPW Δ PairT ⌜Nat⌝ msr Θ ρ a ih₁ ih₂ →
          Prv Θ (pwT (subTm (single a) msr) ih₁ ih₂)
pwIntro {a = a} {ih₁ = ih₁} {ih₂ = ih₂} dμ pw =
  prv _ (⊢lam ⊢PairT
          (⊢lam (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk dμ))
                (⊢-cast idEq (prvOk inner))))
  where
    μa = subTm (single a) msr

    -- ★ ϑ = `vs ∘ vs`, in ONE step rather than as `w` twice — that is what
    --   makes the bridge to `ρ'` a `refl`.  The price is the `renren` below.
    inner = pw (wR (wR Ren⊢-id)) (λ v → refl) (var (vs vz)) (var vz)
               (⊢var (there here))
               (⊢-cast (cong (Hom Nat (nsuc (w msr))) (ww μa)) (⊢var here))

    idEq : Id (El ⌜Nat⌝) (app (app (renTm (λ v → vs (vs v)) ih₁) (var (vs vz))) (var vz))
                         (app (app (renTm (λ v → vs (vs v)) ih₂) (var (vs vz))) (var vz))
         ≡ Id (El ⌜Nat⌝) (app (app (w (w ih₁)) (var (vs vz))) (var vz))
                         (app (app (w (w ih₂)) (var (vs vz))) (var vz))
    idEq = Id-cong₃ refl
             (cong (λ z → app (app z (var (vs vz))) (var vz)) (sym (ww ih₁)))
             (cong (λ z → app (app z (var (vs vz))) (var vz)) (sym (ww ih₂)))

------------------------------------------------------------------------
-- ★★ A `natrec` RE-TYPED AT A VARIABLE SCRUTINEE.
--
-- Every one of the three splits needs the SAME thing: to state its motive
-- it must mention `natrec z s <recursion variable>`, and `ty-Id` will only
-- accept that if it is typed.  `⊢gcdStp` types each `natrec` at its own
-- scrutinee (`snd x`, `fst x`, `a ∸ b`), never at a variable.
--
-- ★ ONE LEMMA, THREE USES, and it is generic: weaken the whole `⊢natrec`
--   by one ambient binder and take the new variable as the scrutinee.  The
--   three peels below are the entire content — a motive, a zero branch and
--   a successor branch, each a `sub`-meets-`ren` commutation decided
--   variable-by-variable.
--
-- ⚠ Do NOT try to get this by substituting into `⊢gcdStp`.  Its scrutinee
--   is `snd x`, and no substitution turns that into a variable.
------------------------------------------------------------------------

-- (`nv-at`/`nv-z`/`nv-s`/`⊢natrec-var` moved to `…LibNatrec`.)

------------------------------------------------------------------------
-- ★ APPLYING AN IH to its two arguments — two `⊢app`s and one peel.
--   (`LibAmrec.appIH` is the same lemma, but it lives inside a
--   parameterised module and is stated in `aIHTat`'s slots.)
------------------------------------------------------------------------

-- ⚠ REPOINTED at `…LibIHCall.appIHat`, which is this at an ARBITRARY
--   carrier and motive.  The seven lines it replaced were the `PairT`/
--   `⌜Nat⌝`/`msr` instance of exactly that peel; the motive being CLOSED
--   is what collapses `El (subTm (single y) ⌜Nat⌝)` to `El ⌜Nat⌝`, and
--   that collapse is definitional, so the delegation needs no cast.
appGcdIH : {Γ : Ctx} {μ i y q : RTm ⌊ Γ ⌋} →
           Γ ⊢ i ∷ gcdIH μ → Γ ⊢ y ∷ PairT →
           Γ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) msr)) μ →
           Γ ⊢ app (app i y) q ∷ El ⌜Nat⌝
appGcdIH di dy dq = appIHat di dy dq

-- ★ `gcdIH`/`gcdG` past a weakening.  ⚠ NOT definitional: `gcdIH` hides a
--   `w μ` inside its `Hom`, so `renTy vs` has to fuse with it.  `aIHTat-ren`
--   already says this; PairT/⌜Nat⌝/msr all compute through it.
gcdIH-w : {Γ : Cx} (μ : RTm Γ) → renTy vs (gcdIH μ) ≡ gcdIH (w μ)
gcdIH-w μ = aIHTat-ren PairT ⌜Nat⌝ msr μ

gcdIH-w² : {Γ : Cx} (μ : RTm Γ) →
           renTy vs (renTy vs (gcdIH μ)) ≡ gcdIH (w (w μ))
gcdIH-w² μ = trans (cong (renTy vs) (gcdIH-w μ)) (gcdIH-w (w μ))

gcdIH-w³ : {Γ : Cx} (μ : RTm Γ) →
           renTy vs (renTy vs (renTy vs (gcdIH μ))) ≡ gcdIH (w (w (w μ)))
gcdIH-w³ μ = trans (cong (renTy vs) (gcdIH-w² μ)) (gcdIH-w (w (w μ)))

gcdG-w³ : {Γ : Cx} (μ : RTm Γ) →
          renTy vs (renTy vs (renTy vs (gcdG μ))) ≡ gcdG (w (w (w μ)))
gcdG-w³ μ = cong (λ T → Π T (El ⌜Nat⌝)) (gcdIH-w³ μ)

⊢pwT : {Γ : Ctx} {μa i₁ i₂ : RTm ⌊ Γ ⌋} →
       Γ ⊢ μa ∷ Nat → Γ ⊢ i₁ ∷ gcdIH μa → Γ ⊢ i₂ ∷ gcdIH μa →
       Γ ⊢ty pwT μa i₁ i₂
⊢pwT {μa = μa} dμ d₁ d₂ =
  ty-Π ⊢PairT
    (ty-Π (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk dμ))
          (ty-Id (ty-El ⊢⌜Nat⌝) (at d₁) (at d₂)))
  where
    at : {i : RTm ⌊ _ ⌋} → _ ⊢ i ∷ gcdIH μa → _
    at d = appGcdIH (⊢-cast (gcdIH-w² μa) (⊢wk (⊢wk d)))
                    (⊢var (there here)) (⊢var here)

------------------------------------------------------------------------
-- ★★★ `eqG` — THE `Id`-ANALOGUE OF `gcdG`.
--
--   gcdG μ  =  (ih : gcdIH μ) → Nat
--   eqG μ f =  (i₁ i₂ : gcdIH μ) → (i₁ ≐ i₂ pointwise) → f i₁ ≡ f i₂
--
-- ★ THE TWO IHs AND THE HYPOTHESIS ARE Π-BOUND, and that is the whole
--   design.  `⊢gcdStp`'s own motives already carry `gcdG (plusTm …)`, i.e.
--   the IH type at the SPLIT-DEPENDENT bound; mirroring that means every
--   branch receives its IHs at its own bound, and the recursive leaf's
--   certificate `⊢CERTᶻ` — stated at `plusTm (nsuc k') (nsuc n')` — is
--   then exactly what `⊢app` wants.  No transport, no order hypothesis.
--
-- ⚠ `f` is a PARAMETER, not Π-bound.  Quantifying it would make the
--   statement false: two different IHs do give different answers for an
--   arbitrary `f`.  It is the specific `natrec` that makes it true.
------------------------------------------------------------------------

eqG : {Γ : Cx} (μx f : RTm Γ) → RTy Γ
eqG μx f =
  Π (gcdIH μx)
    (Π (gcdIH (w μx))
       (Π (pwT (w (w μx)) (var (vs vz)) (var vz))
          (Id (El ⌜Nat⌝) (app (w (w (w f))) (var (vs (vs vz))))
                         (app (w (w (w f))) (var (vs vz))))))

⊢eqG : {Γ : Ctx} {μx f : RTm ⌊ Γ ⌋} →
       Γ ⊢ μx ∷ Nat → Γ ⊢ f ∷ gcdG μx → Γ ⊢ty eqG μx f
⊢eqG {μx = μx} {f = f} dμ df =
  ty-Π (⊢gcdIH dμ)
    (ty-Π (⊢gcdIH (⊢wk dμ))
      (ty-Π (⊢pwT (⊢wk (⊢wk dμ))
                  (⊢-cast (gcdIH-w² μx) (⊢var (there here)))
                  (⊢-cast (gcdIH-w (w μx)) (⊢var here)))
            -- ⚠ THE TWO IH VARIABLES NEED DIFFERENT PEELS.  Both land at
            --   `gcdIH (w (w (w μx)))`, but the first is `gcdIH μx` under
            --   three weakenings and the second is `gcdIH (w μx)` under two
            --   — the motive already weakened it once.  Sharing one helper
            --   between them does not typecheck.
            (ty-Id (ty-El ⊢⌜Nat⌝)
                   (⊢app df³ (⊢-cast (gcdIH-w³ μx) (⊢var (there (there here)))))
                   (⊢app df³ (⊢-cast (gcdIH-w² (w μx)) (⊢var (there here)))))))
  where
    df³ = ⊢-cast (gcdG-w³ μx) (⊢wk (⊢wk (⊢wk df)))

------------------------------------------------------------------------
-- ★★ SPLIT 1 — on `snd x`.  ctx: [0]=n' [1]=x
--
-- The motive mirrors `G1` exactly, with `gcdG` replaced by `eqG` and the
-- `natrec` re-typed at the recursion variable by `⊢natrec-var`.
------------------------------------------------------------------------

μ₁ : {Γ : Cx} → RTm (Γ ∙ ∙)
μ₁ = plusTm (fst (var (vs vz))) (var vz)

f₁ : {Γ : Cx} → RTm (Γ ∙ ∙)
f₁ = natrec (w G1z) (renTm (extR (extR vs)) gcdInn1) (var vz)

M₁ : {Γ : Cx} → RTy (Γ ∙ ∙)
M₁ = eqG μ₁ f₁

-- ⭐ THE THREE MOTIVE BOUNDARIES ARE `refl`.  Everything in `gcdStp` is
--   built from VARIABLES, so every `subTy`/`subTm` at a boundary COMPUTES
--   — the note in `…GcdStep`'s header, cashed in.  No `mot-at`, no
--   `wk-single`, no `eqG-sub` lemma.
probe₁-at : {Γ : Cx} → subTy (single (snd (var vz))) (M₁ {Γ}) ≡ eqG msr gcdBody
probe₁-at = refl

probe₁-z : {Γ : Cx} →
           subTy (single nzero) (M₁ {Γ})
         ≡ eqG (plusTm (fst (var vz)) nzero) (natrec G1z gcdInn1 nzero)
probe₁-z = refl

------------------------------------------------------------------------
-- ★ LEAF 1 — `snd x = 0`, so `gcd (a , 0) = a`.  IH-FREE.
--
-- ⭐ BOTH SIDES REDUCE TO THE SAME TERM, and literally: `G1z`'s body is
--   `fst <the carrier>`, and the carrier does not mention the `ih` the
--   `lam` just bound, so `subTm (single ihᵢ)` lands on the same thing for
--   `ih₁` and `ih₂`.  ⚠ That is why the discarded argument costs nothing
--   here — the usual `wk-single` tax is definitional at a concrete index.
------------------------------------------------------------------------

red₁z : {Γ : Cx} (i : RTm (Γ ∙ ∙ ∙ ∙)) →
        app (w (w (w (natrec (G1z {Γ}) gcdInn1 nzero)))) i
      ⟶* fst (var (vs (vs (vs vz))))
red₁z i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

leaf₁z : {Γ : Ctx} →
         Prv (Γ ▹ PairT)
             (eqG (plusTm (fst (var vz)) nzero) (natrec G1z gcdInn1 nzero))
leaf₁z =
  prv _ (⊢lam (⊢gcdIH dμ)
          (⊢lam (⊢gcdIH (⊢wk dμ))
            (⊢lam (⊢pwT (⊢wk (⊢wk dμ))
                        (⊢-cast (gcdIH-w² _) (⊢var (there here)))
                        (⊢-cast (gcdIH-w (w _)) (⊢var here)))
                  (prvOk idPrf))))
  where
    dμ = ⊢plus (⊢fst (⊢var here)) ⊢nzero
    idPrf = idOfRed (red₁z (var (vs (vs vz)))) (red₁z (var (vs vz)))
              (prv _ (⊢idrefl ⊢⌜Nat⌝
                        (asP (⊢fst (⊢var (there (there (there here))))))))

------------------------------------------------------------------------
-- ★★★ THE BRIDGE BETWEEN SPLITS — a reduction of `f` is a CONVERSION of
--     `eqG μ f`.
--
-- ⚠ WHY IT IS NEEDED.  Split 1's successor branch must inhabit
--   `subTy nrs M₁`, whose function slot is `natrec … (nsuc n')`.  Split 2
--   produces the same statement about that term's `natrec-suc` REDUCT.  The
--   two are not equal — only related by one step — so the branch cannot be
--   a cast.  ⭐ But `eqG` mentions `f` only inside an `Id`, under three
--   `Π`s, and the kernel has `ξ-Πʳ`, `ξ-Idˡ` and `ξ-Idʳ`, so the reduction
--   pushes all the way in and becomes a TYPE conversion.  One `⊢conv` per
--   split instead of re-lam-ing and bridging each `Id` by hand.
------------------------------------------------------------------------

eqG-red : {Γ : Cx} {μ f g : RTm Γ} → f ⟶* g → eqG μ f ≅ᵀ eqG μ g
eqG-red {f = f} {g = g} r =
  red→≅ᵀ (⟶ᵀ*-Πʳ (⟶ᵀ*-Πʳ (⟶ᵀ*-Πʳ
    (⟶ᵀ*-trans (⟶ᵀ*-Idˡ (⟶*-appˡ r³)) (⟶ᵀ*-Idʳ (⟶*-appˡ r³))))))
  where
    r³ = ⟶*-ren vs (⟶*-ren vs (⟶*-ren vs r))

------------------------------------------------------------------------
-- ★★ SPLIT 2 — on `fst x`.  ctx: [0]=k' [1]=M₁ [2]=n' [3]=x
------------------------------------------------------------------------

f₂ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙)
f₂ = natrec (w G2z) (renTm (extR (extR vs)) gcdInn2) (var vz)

-- ⭐ …and the two splits MEET, in one `natrec-suc` step.
probe₁-s : {Γ : Cx} →
           subTm nrs (f₁ {Γ})
         ⟶* subTm (single (fst (var (vs (vs vz))))) (f₂ {Γ})
probe₁-s = step (natrec-suc _ _ _) done

μ₂ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙)
μ₂ = plusTm (var vz) (nsuc (var (vs (vs vz))))

M₂ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙)
M₂ = eqG μ₂ f₂

-- split 1's successor context, which is split 2's base
Θ₂ : Ctx → Ctx
Θ₂ Γ = ((Γ ▹ PairT) ▹ Nat) ▹ M₁

probe₂-z : {Γ : Cx} →
           subTy (single nzero) (M₂ {Γ})
         ≡ eqG (plusTm nzero (nsuc (var (vs vz))))
               (natrec G2z (subTm (extS (extS (single nzero)))
                                  (renTm (extR (extR vs)) gcdInn2)) nzero)
probe₂-z = refl

------------------------------------------------------------------------
-- ★ LEAF 2 — `fst x = 0`, so `gcd (0 , b) = b`.  IH-FREE, same shape as
--   leaf 1: `G2z`'s body is `nsuc n'`, which does not mention the bound
--   `ih`, so both sides land on the same term.
------------------------------------------------------------------------

red₂z : {Γ : Cx} (sb : RTm (Γ ∙ ∙ ∙ ∙ ∙)) (i : RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)) →
        app (w (w (w (natrec (G2z {Γ}) sb nzero)))) i
      ⟶* nsuc (var (vs (vs (vs (vs vz)))))
red₂z sb i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

leaf₂z : {Γ : Ctx} → Prv (Θ₂ Γ) (subTy (single nzero) M₂)
leaf₂z =
  prv _ (⊢lam (⊢gcdIH dμ)
          (⊢lam (⊢gcdIH (⊢wk dμ))
            (⊢lam (⊢pwT (⊢wk (⊢wk dμ))
                        (⊢-cast (gcdIH-w² _) (⊢var (there here)))
                        (⊢-cast (gcdIH-w (w _)) (⊢var here)))
                  (prvOk idPrf))))
  where
    dμ = ⊢plus ⊢nzero (⊢nsuc (⊢var (there here)))
    idPrf = idOfRed (red₂z _ (var (vs (vs vz)))) (red₂z _ (var (vs vz)))
              (prv _ (⊢idrefl ⊢⌜Nat⌝
                        (asP (⊢nsuc (⊢var (there (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★★★ ELIMINATING THE INTERNAL POINTWISE HYPOTHESIS.
--
-- The mirror of `pwIntro`: two `⊢app`s and the peels they leave.  ⚠ The
-- `w`s are the whole cost — `pwT` states its body at the two binders'
-- depth, so every slot arrives under one or two weakenings that
-- `sub-w`/`wk-single` have to strip.  Both recursive leaves use this once.
------------------------------------------------------------------------

pwElim : {Γ : Ctx} {μ i₁ i₂ h y q : RTm ⌊ Γ ⌋} →
         Γ ⊢ h ∷ pwT μ i₁ i₂ → Γ ⊢ y ∷ PairT →
         Γ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) msr)) μ →
         Γ ⊢ app (app h y) q
           ∷ Id (El ⌜Nat⌝) (app (app i₁ y) q) (app (app i₂ y) q)
pwElim {μ = μ} {i₁ = i₁} {i₂ = i₂} {y = y} {q = q} dh dy dq =
  ⊢-cast eq2 (⊢app (⊢-cast eq1 (⊢app dh dy)) dq)
  where
    -- one binder in: the two IHs lose one `w`, the bound loses its `w`
    peel₁ : (t : RTm ⌊ _ ⌋) → subTm (extS (single y)) (w (w t)) ≡ w t
    peel₁ t = trans (sub-w {σ = single y} (w t))
                    (cong w (wk-single {v = y} t))

    eq1 = cong₂ (λ u f → Π (Hom Nat (nsuc (subTm (single y) msr)) u) f)
                (wk-single {v = y} μ)
                (Id-cong₃ refl
                  (cong (λ z → app (app z (w y)) (var vz)) (peel₁ i₁))
                  (cong (λ z → app (app z (w y)) (var vz)) (peel₁ i₂)))

    -- the second binder: both `w`s go
    peel₂ : (t : RTm ⌊ _ ⌋) → subTm (single q) (w t) ≡ t
    peel₂ t = wk-single {v = q} t

    eq2 = Id-cong₃ refl
            (cong₂ (λ z u → app (app z u) q) (peel₂ i₁) (peel₂ y))
            (cong₂ (λ z u → app (app z u) q) (peel₂ i₂) (peel₂ y))

-- ★ `pwT` past a weakening — needed because the hypothesis reaches each
--   leaf as a Π-BOUND VARIABLE, and `here` hands it back under a `renTy vs`.
pwT-w : {Γ : Cx} (μ i₁ i₂ : RTm Γ) →
        renTy vs (pwT μ i₁ i₂) ≡ pwT (w μ) (w i₁) (w i₂)
pwT-w μ i₁ i₂ =
  cong₂ (λ u f → Π PairT (Π (Hom Nat (nsuc msr) u) f))
        (ren-w μ)
        (Id-cong₃ refl (atv (wwr i₁)) (atv (wwr i₂)))
  where
    wwr : (t : RTm _) → renTm (extR (extR vs)) (w (w t)) ≡ w (w (w t))
    wwr t = trans (ren-w {ρ = extR vs} (w t)) (cong w (ren-w t))

    atv : {u u' : RTm _} → u ≡ u' →
          app (app u (var (vs vz))) (var vz) ≡ app (app u' (var (vs vz))) (var vz)
    atv e = cong (λ z → app (app z (var (vs vz))) (var vz)) e

------------------------------------------------------------------------
-- ★★ SPLIT 3 — the COMPARISON, on `a ∸ b`.  ctx: [0]=M₂ [1]=k' [2]=M₁ [3]=n' [4]=x
--
-- ⚠ CONSTANT MOTIVE, exactly as `G3` is: the branch needs to know only
--   WHETHER `a ∸ b` is zero, never its value.  So `μ₃` does not mention the
--   recursion variable and the two leaves get their IHs at the SAME bound,
--   `plusTm (nsuc k') (nsuc n')` — which is precisely the bound `⊢CERTᶻ`
--   and `⊢CERTˢ` are stated at.
------------------------------------------------------------------------

Θ₃ : Ctx → Ctx
Θ₃ Γ = (Θ₂ Γ ▹ Nat) ▹ M₂

μ₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
μ₃ = plusTm (nsuc (var (vs (vs vz)))) (nsuc (var (vs (vs (vs (vs vz))))))

f₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙)
f₃ = natrec (w G3z) (renTm (extR (extR vs)) G3s) (var vz)

M₃ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙ ∙ ∙)
M₃ = eqG μ₃ f₃

-- ⭐ splits 2 and 3 meet in one `natrec-suc` step too
probe₂-s : {Γ : Cx} →
           subTm nrs (f₂ {Γ})
         ⟶* subTm (single (monusTm (nsuc (var (vs vz)))
                                   (nsuc (var (vs (vs (vs vz))))))) (f₃ {Γ})
probe₂-s = step (natrec-suc _ _ _) done

