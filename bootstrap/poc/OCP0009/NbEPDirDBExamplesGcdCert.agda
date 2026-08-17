------------------------------------------------------------------------
-- OCP-0009 — TYPING THE RECURSIVE CALL'S CERTIFICATE.
--
-- ★ THE PROBLEM.  gap A's recursive equation needs
--   `Δ ⊢ recCert (gcd-gt-term …) ∷ Hom Nat (nsuc (μ Y)) (μ X)`.  That
--   certificate is `CERTˢ` under EIGHT substitutions, and `subTm` does not
--   invert, so subject reduction cannot produce a typing for it.
--
-- ⚠⚠ AND PEELING IT IS THE WRONG MOVE — measured 2026-08-17.  Saying what
--   the certificate EQUALS (`≡ ⊢desc-left`'s subject) forces Agda to
--   normalise `plusMonoLTm` under all eight layers, i.e. through
--   `trHomʳ`/`trHomˡ`/`congS`/`commTm`/`jsub`.  Done inside `gcd-gt-term`
--   that took `…GcdStep` from 31s to over 10 MINUTES.
--
-- ⭐ THE FIX: DO NOT SAY WHAT IT EQUALS, SAY WHY IT IS WELL-TYPED.
--   `sub-lemma` acts on the DERIVATION, not on the term's normal form, so
--   applying it ONCE PER LAYER never normalises the certificate at all.
--   `⊢CERTˢ` (named in prerequisite 1) is the seed; eight `Sub⊢`s carry it
--   down.  The `sub`-naturality lemmas added to `…LibArithComm` are not
--   needed on this route — they stand on their own as library lemmas.
--
-- ★ AND THE `Sub⊢`s ARE THE REAL CONTENT: they demand typings for the
--   reduction's intermediate scrutinees `R₁`/`W`/`R₂`/`R₃`, i.e. exactly
--   what `⊢gcdStp` already knows about gcd's three nested `natrec`s, said
--   at a general scrutinee rather than at `snd x`/`fst x`/`a ∸ b`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdCert where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; sym; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Sub; subTm; subTy; extS; renTm; _∘ₛ_
        ; subTy-subTy; subTy-cong; subTm-subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢natrec; ⊢nzero; ⊢nsuc; ⊢conv; csymᵀ
        ; ⊢fst; ⊢snd; ⊢pair; ty-Nat )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; sub-ty; sub-lemma; Sub⊢; Sub⊢-ext; ⊢single; ⊢[] )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm )
open import poc.OCP0009.NbEPDirDBExamplesDiv using ( monusTm )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLTm; plusMonoLTm-sub )
open import poc.OCP0009.NbEPDirDBLibArithMonus
  using ( monusLtTm; monusLtTm-sub; ⊢desc-left )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( subren; renren )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2; wkS2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s
        ; CERTˢ; ⊢CERTˢ; PAIRˢ; KS; NS; gcdIH
        ; peel4; peel6; wkS2; descConv )

------------------------------------------------------------------------
-- ★★★ A `natrec`'s TYPING, TRANSPORTED ALONG A SUBSTITUTION.
--
-- ⚠ GENERAL — nothing gcd-specific here; it belongs beside `⊢natrec-var`
--   in the WF library (see FUTURE.md).  `⊢natrec-var` re-types a `natrec`
--   at a VARIABLE scrutinee; this one re-types it at an ARBITRARY scrutinee
--   under an arbitrary substitution of the ambient context, which is what a
--   reduction's intermediate scrutinees need.
--
-- ★ Two casts, and both are the same shape: a substitution meeting
--   `single nzero` resp. `nrs`, decided variable-by-variable.
------------------------------------------------------------------------

module _ {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {M : RTy (⌊ Γ ⌋ ∙)} where

  na-z : subTy (single nzero) (subTy (extS σ) M)
       ≡ subTy σ (subTy (single nzero) M)
  na-z = trans (subTy-subTy M) (trans (subTy-cong br M) (sym (subTy-subTy M)))
    where
      br : ∀ v → subTm (single nzero) (extS σ v) ≡ subTm σ (single nzero v)
      br vz     = refl
      br (vs u) = wk-single {v = nzero} (subTm σ (var u))

  na-s : subTy nrs (subTy (extS σ) M)
       ≡ subTy (extS (extS σ)) (subTy nrs M)
  na-s = trans (subTy-subTy M) (trans (subTy-cong br M) (sym (subTy-subTy M)))
    where
      br : ∀ v → subTm nrs (extS σ v) ≡ subTm (extS (extS σ)) (nrs v)
      br vz     = refl
      br (vs u) =
        trans (subren {σ = nrs} {ρ = vs} {ρ' = λ x → vs (vs x)}
                      (λ _ → refl) (subTm σ (var u)))
              (sym (renren {ϑ = vs} {ρ = vs} {ρ' = λ x → vs (vs x)}
                           (λ _ → refl) (subTm σ (var u))))

-- ★ TYPED SUBSTITUTIONS COMPOSE.  ⚠ Also general, also missing from
--   `…Subj`.  One line: substitute the derivation `σ⊢` gives, then fuse the
--   two `subTy`s.  Needed because the reduction's scrutinees live three and
--   five slots deep, so their `Sub⊢`s are composites.
Sub⊢-∘ : {Γ Δ Θ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {τ : Sub ⌊ Δ ⌋ ⌊ Θ ⌋} →
         Sub⊢ Γ Δ σ → Sub⊢ Δ Θ τ → Sub⊢ Γ Θ (τ ∘ₛ σ)
Sub⊢-∘ {σ = σ} {τ = τ} σ⊢ τ⊢ {A = A} v =
  ⊢-cast (subTy-subTy A) (sub-lemma (σ⊢ v) τ⊢)

-- ★ …and the lemma itself.  Three lines; the two casts above are all of it.
⊢natrec-at : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {M : RTy (⌊ Γ ⌋ ∙)}
             {z : RTm ⌊ Γ ⌋} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} {n : RTm ⌊ Δ ⌋} →
             (Γ ▹ Nat) ⊢ty M →
             Γ ⊢ z ∷ subTy (single nzero) M →
             ((Γ ▹ Nat) ▹ M) ⊢ s ∷ subTy nrs M →
             Sub⊢ Γ Δ σ → Δ ⊢ n ∷ Nat →
             Δ ⊢ natrec (subTm σ z) (subTm (extS (extS σ)) s) n
               ∷ subTy (single n) (subTy (extS σ) M)
⊢natrec-at dM dz ds σ⊢ dn =
  ⊢natrec (sub-ty dM (Sub⊢-ext σ⊢))
          (⊢-cast (sym na-z) (sub-lemma dz σ⊢))
          (⊢-cast (sym na-s) (sub-lemma ds (Sub⊢-ext (Sub⊢-ext σ⊢))))
          dn

------------------------------------------------------------------------
-- ★★ THE REDUCTION'S INTERMEDIATE SCRUTINEES, TYPED.
--
-- `R₁` is `gcd`'s outer `natrec` at the carrier `gX` and the PREDECESSOR
-- `b'` — i.e. the recursive call `natrec-suc` hands over.  ⭐ One line,
-- because `⊢natrec-at` takes exactly the data `⊢gcdStp` already names.
------------------------------------------------------------------------

module GcdCertAt {Δ : Ctx} {a' b' d : RTm ⌊ Δ ⌋}
                 (da : Δ ⊢ a' ∷ Nat) (db : Δ ⊢ b' ∷ Nat)
                 (dd : Δ ⊢ d ∷ Nat) where

  gX : RTm ⌊ Δ ⌋
  gX = pair (nsuc a') (nsuc b')

  ⊢gX : Δ ⊢ gX ∷ PairT
  ⊢gX = ⊢pair ty-Nat (⊢nsuc da) (⊢nsuc db)

  R₁ : RTm ⌊ Δ ⌋
  R₁ = natrec (subTm (single gX) G1z)
              (subTm (extS (extS (single gX))) gcdInn1) b'

  ⊢R₁ : Δ ⊢ R₁ ∷ subTy (single b') (subTy (extS (single gX)) G1)
  ⊢R₁ = ⊢natrec-at ⊢G1 ⊢G1z ⊢gcdInn1 (⊢single ⊢gX) db

  ------------------------------------------------------------------------
  -- ★ `W` — the descent's first argument, `a ∸ b`, after the outer
  --   substitutions.  ⚠ It is `a'` only PROPOSITIONALLY (`wkS2`), so the
  --   typing moves by `subst` on the TERM, not `⊢-cast` on the type.
  ------------------------------------------------------------------------

  W : RTm ⌊ Δ ⌋
  W = subTm (single R₁) (subTm (extS (single b')) (renTm vs (renTm vs a')))

  ⊢W : Δ ⊢ W ∷ Nat
  ⊢W = subst (λ t → Δ ⊢ t ∷ Nat) (sym (wkS2 {u = R₁} {v = b'} a')) da

  ------------------------------------------------------------------------
  -- ★ THE EIGHT SUBSTITUTION LAYERS, NAMED — one per slot of `CΓs`, in the
  --   order the reduction applied them.  Naming them is what keeps the rest
  --   of this module readable; spelled out, `σH` is a page wide.
  ------------------------------------------------------------------------

  σA : Sub (⌊ Δ ⌋ ∙) ⌊ Δ ⌋
  σA = single gX

  σB : Sub (⌊ Δ ⌋ ∙ ∙) ⌊ Δ ⌋
  σB = single b' ∘ₛ extS σA

  σC : Sub (⌊ Δ ⌋ ∙ ∙ ∙) ⌊ Δ ⌋
  σC = single R₁ ∘ₛ extS σB

  σA⊢ : Sub⊢ (Δ ▹ PairT) Δ σA
  σA⊢ = ⊢single ⊢gX

  σB⊢ : Sub⊢ ((Δ ▹ PairT) ▹ Nat) Δ σB
  σB⊢ = Sub⊢-∘ {σ = extS σA} {τ = single b'}
               (Sub⊢-ext {C = Nat} σA⊢) (⊢single db)

  σC⊢ : Sub⊢ (((Δ ▹ PairT) ▹ Nat) ▹ G1) Δ σC
  σC⊢ = Sub⊢-∘ {σ = extS σB} {τ = single R₁}
               (Sub⊢-ext {C = G1} σB⊢)
               (⊢single (⊢-cast (subTy-subTy {τ = single b'} {σ = extS σA} G1) ⊢R₁))

  ------------------------------------------------------------------------
  -- ★ …and the same one-liner at each deeper scrutinee.  ⚠ Every implicit
  --   substitution is PINNED: one that occurs only in APPLIED position is a
  --   higher-order pattern Agda solves partway and then blocks on.
  ------------------------------------------------------------------------

  R₂ : RTm ⌊ Δ ⌋
  R₂ = natrec (subTm σC G2z) (subTm (extS (extS σC)) gcdInn2) W

  ⊢R₂ : Δ ⊢ R₂ ∷ subTy (single W) (subTy (extS σC) G2)
  ⊢R₂ = ⊢natrec-at ⊢G2 ⊢G2z ⊢gcdInn2 σC⊢ ⊢W

  σD : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σD = single W ∘ₛ extS σC

  σD⊢ : Sub⊢ ((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) Δ σD
  σD⊢ = Sub⊢-∘ {σ = extS σC} {τ = single W}
               (Sub⊢-ext {C = Nat} σC⊢) (⊢single ⊢W)

  σE : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σE = single R₂ ∘ₛ extS σD

  σE⊢ : Sub⊢ (((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) Δ σE
  σE⊢ = Sub⊢-∘ {σ = extS σD} {τ = single R₂}
               (Sub⊢-ext {C = G2} σD⊢)
               (⊢single (⊢-cast (subTy-subTy {τ = single W} {σ = extS σC} G2) ⊢R₂))

  ------------------------------------------------------------------------
  -- ★ the LAST scrutinee, and the last three layers.
  ------------------------------------------------------------------------

  R₃ : RTm ⌊ Δ ⌋
  R₃ = natrec (subTm σE G3z) (subTm (extS (extS σE)) G3s) d

  ⊢R₃ : Δ ⊢ R₃ ∷ subTy (single d) (subTy (extS σE) G3)
  ⊢R₃ = ⊢natrec-at ⊢G3 ⊢G3z ⊢G3s σE⊢ dd

  σF : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σF = single d ∘ₛ extS σE

  σF⊢ : Sub⊢ ((((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) ▹ Nat) Δ σF
  σF⊢ = Sub⊢-∘ {σ = extS σE} {τ = single d}
               (Sub⊢-ext {C = Nat} σE⊢) (⊢single dd)

  σG : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σG = single R₃ ∘ₛ extS σF

  σG⊢ : Sub⊢ (((((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) ▹ Nat) ▹ G3) Δ σG
  σG⊢ = Sub⊢-∘ {σ = extS σF} {τ = single R₃}
               (Sub⊢-ext {C = G3} σF⊢)
               (⊢single (⊢-cast (subTy-subTy {τ = single d} {σ = extS σE} G3) ⊢R₃))

  ------------------------------------------------------------------------
  -- ★★★★ THE CERTIFICATE, TYPED — and `CERTˢ` was never normalised.
  --
  -- ⚠ The `ih` layer is a PARAMETER, not fixed here: `ih` is whatever the
  --   caller passes to the step, and its typing is what the caller has.
  ------------------------------------------------------------------------

  ⊢cert : {ih : RTm ⌊ Δ ⌋} →
          Δ ⊢ ih ∷ subTy σG (gcdIH (plusTm (nsuc (var (vs (vs (vs vz)))))
                                           (nsuc (var (vs (vs (vs (vs (vs vz))))))))) →
          Δ ⊢ subTm (single ih ∘ₛ extS σG) CERTˢ
            ∷ subTy (single ih ∘ₛ extS σG)
                    (Hom Nat (nsuc (plusTm (fst PAIRˢ) (snd PAIRˢ)))
                             (plusTm (nsuc KS) (nsuc NS)))
  ⊢cert {ih = ih} dih =
    sub-lemma ⊢CERTˢ
      (Sub⊢-∘ {σ = extS σG} {τ = single ih}
              (Sub⊢-ext {C = gcdIH (plusTm (nsuc (var (vs (vs (vs vz)))))
                                           (nsuc (var (vs (vs (vs (vs (vs vz))))))))}
                        σG⊢)
              (⊢single dih))

  ------------------------------------------------------------------------
  -- ⚠⚠ NOT DONE: THE NESTED FORM — and five routes are ruled out.
  --
  -- `⊢cert` above types the FUSED `subTm (single ih ∘ₛ extS σG) CERTˢ`;
  -- `recCert (gcd-gt-term …)` is EIGHT NESTED `subTm`s, and the caller
  -- needs the nested one.  Measured 2026-08-17, one agda at a time:
  --
  --   1. fuse nested → composite                    >10min (the comparison
  --      the derivation route exists to avoid)
  --   2. `sub-lemma` layer-by-layer, ONE term       OOM
  --   3. …with subject AND type written by hand     OOM  ⇒ not an
  --      inference artefact
  --   4. …as EIGHT SEPARATE Defs, with `⊢CERTˢ`'s
  --      `B`/`C`/`D` motive slots PINNED            1m37s + ONE honest type
  --      error — the NEAR MISS.  `⊢R₂` is typed at the composite `σC`
  --      where the chain wants it un-nested.
  --   5. bridging that with `exts-exts` + `subTy-subTy` over `G2`   OOM
  --   6. `opaque plusMonoLTm` as scaffolding, to separate "wrong" from
  --      "expensive"                                  OOM at 1m34s
  --
  -- ⭐⭐ ROUTE 6 FALSIFIED THE STATED CAUSE, and that is its value.  The
  --   claim was that the cost is `plusMonoLTm` unfolding.  Blocking that
  --   unfolding made `…GcdStep` 3x FASTER (22s → 7.7s, a real and separate
  --   win) and moved the only failure to the numeral demos, which need
  --   `subTm` to distribute INTO `plusMonoLTm` and were fixed by a local
  --   `unfolding` — but the certificate chain STILL OOM-killed.
  --
  --   ⇒ THE DOMINANT COST IS NOT THE ARITHMETIC.  It is that `σC`/`σD`/`σE`
  --   embed `R₁`/`R₂`/`R₃`, which embed `gcdInn1 → gcdInn2 → G3z`/`G3s` —
  --   the WHOLE gcd body.  Every `Sub⊢-ext` tower over a context holding
  --   those is expensive, and they cannot be made opaque because the
  --   reduction lemmas need them to compute.  All six routes fail for this
  --   one shared reason: each asks Agda to compare or normalise a type in
  --   which the gcd body sits inside a substitution.
  --
  -- ⚠ SO IT IS NOT A TACTIC PROBLEM.  A seventh tactic is not the answer;
  --   the FORMULATION has to change so the certificate is typed where the
  --   gcd body is not in the substitution.  Two candidates, both DESIGN
  --   DECISIONS about `RecCall`'s contract:
  --     (a) `gcd-gt-term` hands back a certificate already in
  --         `⊢desc-left`'s form AT CONSTRUCTION — restate the reduction so
  --         the clean form is what the chain PRODUCES rather than something
  --         recovered afterwards.  (`certAt` was heading here before it hit
  --         the `β`-inference wall; the fix there was an unsignatured
  --         `chain`, which is known to work.)
  --     (b) state gcd's recursive equation with the certificate typing as
  --         an explicit HYPOTHESIS, discharged separately at a site where
  --         the gcd body is not in scope.
  --
  -- ⭐ ROUTE 4 IS THE ONE TO RESUME FROM.  Its diagnosis also explains the
  --   earlier OOMs: `⊢CERTˢ` GENERALISES its sibling motive slots — the very
  --   generalisation that let gcd's `StepExt` reuse it — so left implicit
  --   they are metas, and unsolved metas across eight layers is what blew
  --   the heap.  Pinned, layer 1 alone is 8.5s.
  --
  -- ⚠ THE COST IS `plusMonoLTm` UNFOLDING, always: through
  --   `trHomʳ`/`trHomˡ`/`congS`/`commTm`/`jsub`.  Two untried angles —
  --   (a) push the substitutions through the SMALL motives first
  --   (`⊢G2`/`⊢G2z`/`⊢gcdInn2` layer by layer, then a plain `⊢natrec` at
  --   the bottom), needing an `na-z`/`na-s` cast per layer; or (b) make the
  --   certificate OPAQUE (`abstract`), since no caller of the certificate
  --   needs to see inside it — only its type matters.  (b) is a change to a
  --   shared library's abstraction boundary and is a DESIGN DECISION.
  --
  -- ⭐ What IS established: the certificate is typeable by DERIVATION at
  --   6.2s, and every ingredient (`⊢R₁`/`⊢W`/`⊢R₂`/`⊢R₃`, the eight typed
  --   layers) is green and cheap.  What is missing is only the SHAPE the
  --   reduction hands over, not the mathematics.
  ------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★★★ THE REFORMULATION — THE CERTIFICATE IN CLEAN FORM, AS A TERM.
--
-- ⚠ WHAT CHANGED, AND WHY IT SHOULD WORK WHERE SIX ROUTES DID NOT.
--   Every earlier route asked Agda to compare or normalise a TYPE in which
--   the gcd body sat inside a substitution.  This asks for a TERM equation
--   at a RAW context — no `Ctx`, no typing, nothing that can pull in a
--   derivation — and with `plusMonoLTm` OPAQUE the certificate is five
--   nodes per layer instead of its whole unfolding.
--
-- ★ THE SUBSTITUTION STILL MOVES, by `plusMonoLTm-sub`/`monusLtTm-sub`.
--   Those are the naturality lemmas built earlier and then set aside as
--   "not needed on this route" — under opacity they are exactly the tool
--   that makes it affordable.  ⭐ The equations that used to come free from
--   computation are theorems now, and stating them once is the whole cost.
------------------------------------------------------------------------

module GcdCertEq {Γ : Cx} (a' b' d ih : RTm Γ) where

  gXᵣ : RTm Γ
  gXᵣ = pair (nsuc a') (nsuc b')

  R₁ᵣ : RTm Γ
  R₁ᵣ = natrec (subTm (single gXᵣ) G1z)
               (subTm (extS (extS (single gXᵣ))) gcdInn1) b'

  Wᵣ : RTm Γ
  Wᵣ = subTm (single R₁ᵣ) (subTm (extS (single b')) (renTm vs (renTm vs a')))

  R₂ᵣ : RTm Γ
  R₂ᵣ = natrec (subTm (single R₁ᵣ)
                 (subTm (extS (single b')) (subTm (extS (extS (single gXᵣ))) G2z)))
               (subTm (extS (extS (single R₁ᵣ)))
                 (subTm (extS (extS (extS (single b'))))
                   (subTm (extS (extS (extS (extS (single gXᵣ))))) gcdInn2)))
               Wᵣ

  R₃ᵣ : RTm Γ
  R₃ᵣ = natrec (subTm (single R₂ᵣ)
                 (subTm (extS (single Wᵣ))
                   (subTm (extS (extS (single R₁ᵣ)))
                     (subTm (extS (extS (extS (single b'))))
                       (subTm (extS (extS (extS (extS (single gXᵣ))))) G3z)))))
               (subTm (extS (extS (single R₂ᵣ)))
                 (subTm (extS (extS (extS (single Wᵣ))))
                   (subTm (extS (extS (extS (extS (single R₁ᵣ)))))
                     (subTm (extS (extS (extS (extS (extS (single b'))))))
                       (subTm (extS (extS (extS (extS (extS (extS (single gXᵣ)))))))
                              G3s)))))
               d

  -- the eight layers, innermost first
  τ₁ = extS (extS (extS (extS (extS (extS (extS (single gXᵣ)))))))
  τ₂ = extS (extS (extS (extS (extS (extS (single b'))))))
  τ₃ = extS (extS (extS (extS (extS (single R₁ᵣ)))))
  τ₄ = extS (extS (extS (extS (single Wᵣ))))
  τ₅ = extS (extS (extS (single R₂ᵣ)))
  τ₆ = extS (extS (single d))
  τ₇ = extS (single R₃ᵣ)
  τ₈ = single ih

  -- ★ ONE LAYER of each template's naturality.  ⚠ The implicits ARE
  --   inferable here, unlike the earlier `pmStep`, because the chain is
  --   built bottom-up from a fully explicit first step — each `e`'s type
  --   determines the next one's arguments.
  pushPM : {Γ₁ Γ₂ : Cx} {t x y c q : RTm Γ₁} → t ≡ plusMonoLTm x y c q →
           (σ : Sub Γ₁ Γ₂) →
           subTm σ t ≡ plusMonoLTm (subTm σ x) (subTm σ y) (subTm σ c) (subTm σ q)
  pushPM {x = x} {y = y} {c = c} {q = q} e σ =
    trans (cong (subTm σ) e) (plusMonoLTm-sub x y c q)

  pushML : {Γ₁ Γ₂ : Cx} {t x y : RTm Γ₁} → t ≡ monusLtTm x y → (σ : Sub Γ₁ Γ₂) →
           subTm σ t ≡ monusLtTm (subTm σ x) (subTm σ y)
  -- ⚠ ARGS EXPLICIT.  `plusMonoLTm` is OPAQUE so its arguments are
  --   readable off the RHS and `_ _ _ _` suffices; `monusLtTm` is
  --   TRANSPARENT, so the RHS unfolds and inversion fails (measured).
  --   ⭐ A neat demonstration of what opacity buys: rigid heads make
  --   unification work.
  pushML {x = x} {y = y} e σ =
    trans (cong (subTm σ) e) (monusLtTm-sub x y)

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

  ------------------------------------------------------------------------
  -- ★ THE ARGUMENT PEELS — the SAME two the `pair` slot already uses in
  --   `gcd-gt-term`, and they apply for the same reason: `KS` sits at index
  --   4, so `τ₄` fills it with `w⁴ W` and the four layers above peel it
  --   (`peel4`), then `W` IS `a'` (`wkS2`); `NS` sits at index 6, filled by
  --   `τ₂`, peeled by the six above (`peel6`).
  ------------------------------------------------------------------------

  pKS : subTm τ₈ (subTm τ₇ (subTm τ₆ (subTm τ₅ (subTm τ₄
          (subTm τ₃ (subTm τ₂ (subTm τ₁ KS))))))) ≡ a'
  pKS = trans (peel4 {u₁ = R₂ᵣ} {u₂ = d} {u₃ = R₃ᵣ} {u₄ = ih} Wᵣ)
              (wkS2 {u = R₁ᵣ} {v = b'} a')

  pNS : subTm τ₈ (subTm τ₇ (subTm τ₆ (subTm τ₅ (subTm τ₄
          (subTm τ₃ (subTm τ₂ (subTm τ₁ NS))))))) ≡ b'
  pNS = peel6 {u₁ = R₁ᵣ} {u₂ = Wᵣ} {u₃ = R₂ᵣ}
              {u₄ = d} {u₅ = R₃ᵣ} {u₆ = ih} b'

  congPM : {x x' y y' c c' q q' : RTm Γ} →
           x ≡ x' → y ≡ y' → c ≡ c' → q ≡ q' →
           plusMonoLTm x y c q ≡ plusMonoLTm x' y' c' q'
  congPM refl refl refl refl = refl

  ------------------------------------------------------------------------
  -- ★★★★★ THE CERTIFICATE, IN CLEAN FORM.
  --
  --   the reduction's certificate  ≡  plusMonoLTm (a∸b) a b (a<b)
  --
  -- ⭐ which is EXACTLY `⊢desc-left`'s subject — so typing it is now one
  --   `⊢desc-left`, with no peel and no normalisation of the big term.
  ------------------------------------------------------------------------

  certEq : subTm τ₈ (subTm τ₇ (subTm τ₆ (subTm τ₅ (subTm τ₄
             (subTm τ₃ (subTm τ₂ (subTm τ₁ CERTˢ)))))))
         ≡ plusMonoLTm (monusTm (nsuc a') (nsuc b')) (nsuc a') (nsuc b')
                       (monusLtTm a' b')
  certEq =
    trans e8 (congPM (cong₂ (λ A B → monusTm (nsuc A) (nsuc B)) pKS pNS)
                     (cong nsuc pKS)
                     (cong nsuc pNS)
                     (trans f8 (cong₂ monusLtTm pKS pNS)))

------------------------------------------------------------------------
-- ★★★★★★ …AND THE CERTIFICATE IS TYPED.  ONE `⊢desc-left`.
--
-- ⭐ Compare with what this replaces: an eight-layer `sub-lemma` tower that
--   OOM-killed, and before that a peel that ran past ten minutes.  Once the
--   certificate is in `⊢desc-left`'s own form, its typing is the derivation
--   that `⊢G3s` already builds — `descConv` just moves the measure across
--   the pair's projections, exactly as `⊢CERTˢ` does.
------------------------------------------------------------------------

module GcdCertTy {Δ : Ctx} {a' b' d : RTm ⌊ Δ ⌋}
                 (da : Δ ⊢ a' ∷ Nat) (db : Δ ⊢ b' ∷ Nat) (ih : RTm ⌊ Δ ⌋) where

  open GcdCertEq a' b' d ih public

  PAIRᶠ : RTm ⌊ Δ ⌋
  PAIRᶠ = pair (monusTm (nsuc a') (nsuc b')) (nsuc b')

  ⊢certClean : Δ ⊢ subTm τ₈ (subTm τ₇ (subTm τ₆ (subTm τ₅ (subTm τ₄
                 (subTm τ₃ (subTm τ₂ (subTm τ₁ CERTˢ)))))))
               ∷ Hom Nat (nsuc (plusTm (fst PAIRᶠ) (snd PAIRᶠ)))
                         (plusTm (nsuc a') (nsuc b'))
  ⊢certClean =
    subst (λ t → Δ ⊢ t ∷ Hom Nat (nsuc (plusTm (fst PAIRᶠ) (snd PAIRᶠ)))
                                 (plusTm (nsuc a') (nsuc b')))
          (sym certEq)
          (⊢conv (⊢desc-left da db)
                 (csymᵀ (descConv (monusTm (nsuc a') (nsuc b')) (nsuc b')
                                  (plusTm (nsuc a') (nsuc b')))))
