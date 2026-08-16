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

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π; Id
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Ren; renTm; renTy; Sub; subTm; subTy; extR; extS; Id-cong₃ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢lam; ⊢nsuc
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Id; ⊢⌜Nat⌝
        ; _⟶_; _⟶*_; done; step; β; ξ-appˡ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ∋-cast; Ren⊢ )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; StepExt; StepPW; wR; renren; renTy-idR )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; msr; ⊢msr; G1z; gcdInn1; gcdIH )

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

Ren⊢-id : {Γ : Ctx} → Ren⊢ Γ Γ (λ v → v)
Ren⊢-id {A = A} v = ∋-cast (sym (renTy-idR (λ _ → refl) A)) v

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
