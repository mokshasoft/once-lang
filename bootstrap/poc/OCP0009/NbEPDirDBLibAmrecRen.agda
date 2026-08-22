------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — THE RECURSOR'S RENAMING LAWS.
--
-- ⚠⚠ WHY THIS IS A SEPARATE MODULE, AND IT IS A MEASUREMENT, NOT TASTE.
--   These lemmas began life inside `…LibAmrec`.  Adding them there —
--   ~460 lines — made the combined `…ExamplesGcdLeEq` + `…GcdLeMid` build
--   OOM.  Controlled comparison, same build, only `…LibAmrec` differing:
--
--       pre-`-ren`  (3383 lines)   EXIT 0    6m27s
--       with them   (3847 lines)   EXIT 143  OOM at 1m9s
--
--   ⇒ ADDING LEMMAS TO A HEAVILY-IMPORTED MODULE COSTS ITS CLIENTS MEMORY
--     EVEN WHEN THEY NEVER USE THEM.  That build was already at 6m27s and
--     near the ceiling; the additions pushed it over.  Splitting them out
--     means only the clients that need the laws pay for them.
--
-- ★ WHAT IS HERE, and it is self-contained: every construction below is
--   TOP-LEVEL and parameterised, referring to nothing inside `AmT`/`AmTΠ`.
--
--     ihZ' descS' ihS' aZBr' aSBr' aAuxTm' amrecTm' auxIH' ihS-atP'
--     …and their `-ren` laws
--     `StepExt-ren`  — the side condition transports
--     `AmTΠ-at`      — the recursor's module AT a renamed context
--
-- ★★ WHY THEY EXIST.  The irrelevance layer takes `x y : RTm ⌊ Δ ⌋` —
--   CONTEXT renaming-indexed, ARGUMENTS not.  `amrec-ind`'s `IndPW`
--   quantifies over an arbitrary `y : RTm ⌊ Θ ⌋`, so it cannot be stated
--   through `AmTΠ Δ …`.  Instantiating at `Θ` makes that module's own `Δ`
--   BE `Θ`, and these laws connect the instantiation back to `renTm ρ` of
--   the original.  ⇒ the irrelevance layer is REUSED, never generalised.
--
-- ⚠ `AmTΠ`'s OWN definitions are NOT repointed at the primed forms — that
--   is what caused the OOM above, because a module parameter is shared
--   while an explicit argument is repeated at every occurrence.  The two
--   agree DEFINITIONALLY (verified in `…SpikeAgree`), so the laws apply
--   regardless.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibAmrecRen where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U; Id
        ; RTm; var; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTy-renTy; subTy-id; subTm-renTm; subTm-id; subTm-cong
        ; renTm-renTm; renTy-renTy; renTm-cong; renTy-cong; subTy-cong; idₛ
        ; renTy-subTy; renTm-subTm; ordtr-cong₅; Id-cong₃ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _∋_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; _⟶*_; done; step; β; ξ-appˡ; natrec-zero; natrec-suc
        ; ⊢lam; ⊢app; _⊢ty_; ⊢conv; csymᵀ; ctrnᵀ; ⊢⌜Id⌝; El-⌜Id⌝
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Id; wk-single )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; ⟶ᵀ*-Homʳ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ∋-cast; ren-ty; ren-lemma; Ren⊢; Ren⊢-ext
        ; sub-ty; sub-lemma; Sub⊢; Sub⊢-ext; ⊢single )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibOrd using ( ⊢strong-base'; ⊢strong-step )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; ⊢wkᶠ; cong₃; cong₄; sub-w; sub-w²; sub-w³; sub-w⁴; ren-w; wk-singleTy; wᶠ-single
        ; wᶠ¹-single; wᶠ²-single; nrs-wTy; wᶠ-nrs; ren-wTy; ren-wᶠ; sub-wTy; wᶠ-sub
        ; ren-sub; ren-w²; ren-w³; nrs-w; cong₅; cong₆; _∙^_; w^; wTy^; wᶠ^ )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat; aIHT; aIHT-ren; aIHT-fit )
-- (`…LibNatVal` import DELETED 2026-08-21 — it was DEAD: none of
--  `NatVal`/`nv-zero`/`nv-suc`/`natEval` occurred anywhere in this file,
--  yet it propagated the canonicity stack to every client.)
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢[] )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBLibAmrec

------------------------------------------------------------------------
-- ★★★ THE TERM-LEVEL CONSTRUCTIONS, PARAMETERISED — and their `-ren` laws.
--
-- ⚠⚠ THE MODULE'S OWN BODIES ARE **NOT** REPOINTED AT THESE — MEASURED
--   2026-08-20.  Repointing them made `…ExamplesGcdLeMid` OOM (exit 143,
--   uncontended, 1m2s); with the bodies left alone it is 8.4s.
--
--   `aZBr` takes its parameters from the MODULE — shared, implicit at
--   every occurrence — while `aZBr' (w stp) (wᶠ cM) (wᶠ m)` carries them
--   EXPLICITLY at every occurrence, inflating the elaborated term.  Only
--   the two modules already nearest the ceiling noticed.
--
--   ⇒ PARAMETERISING A MODULE-LEVEL DEFINITION IS NOT FREE: it moves
--     shared parameters into every use site.  State the laws on the
--     parameterised form; leave the definitions alone.  The two agree
--     definitionally, so the laws still apply.
--
-- ⚠ THE ASYMMETRY THIS FIXES.  The TYPE-level constructions are already
--   top-level and parameterised, with commutation laws: `aAuxB`/`aAuxB-ren`,
--   `aStepT`/`aStepT-ren`, `aIHT`/`aIHT-ren`.  The TERM-level ones —
--   `ihZ`, `ihS`, `aZBr`, `aSBr`, `aAuxTm`, `amrecTm` — are defined INSIDE
--   `AmT`/`AmTΠ` against the module's parameters, so nothing can say how
--   they behave under a renaming.
--
-- ★ WHY THAT MATTERS.  `amrec-ind`'s `IndPW` premise quantifies over an
--   ARBITRARY `y : RTm ⌊ Θ' ⌋`, but the irrelevance layer (`irrT`,
--   `irrElim`, `irr-ind`) takes `x y : RTm ⌊ Δ ⌋` — the CONTEXT is
--   renaming-indexed, the ARGUMENTS are not.  The way to reach `Θ'`-level
--   arguments is to INSTANTIATE the module at `Θ'` (which `AmTΠ` already
--   does internally, opening `AmT` at `Δ ▹ A`), and then these `-ren` laws
--   are what connect that instantiation back to `renTm ρ` of this one.
--
-- ⇒ this is the same technique the module already uses, applied one level
--   down.  It is NOT a generalisation of the irrelevance layer — that
--   would widen the largest piece of this file; this reuses it as-is.
------------------------------------------------------------------------

ihZ' : {Γ : Cx} (cM m : RTm (Γ ∙)) → RTm ((Γ ∙) ∙)
ihZ' cM m =
  lam (lam (absurd (w (wᶠ (wᶠ cM)))
                   (ordtr (nsuc (w (wᶠ (wᶠ m)))) (w (w (w m))) nzero
                          (var vz) (var (vs (vs vz))))))

-- the `w ∘ wᶠ ∘ wᶠ` spine, pushed through a renaming
wwᶠ²-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
           renTm (extR (extR (extR (extR ρ)))) (w (wᶠ (wᶠ t)))
         ≡ w (wᶠ (wᶠ (renTm (extR ρ) t)))
wwᶠ²-ren {ρ = ρ} t =
  trans (ren-w {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ t)))
        (cong w (trans (ren-wᶠ {ρ = extR ρ} (wᶠ t))
                       (cong wᶠ (ren-wᶠ {ρ = ρ} t))))

ihZ-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cM m : RTm (Γ ∙)) →
          renTm (extR (extR ρ)) (ihZ' cM m)
        ≡ ihZ' (renTm (extR ρ) cM) (renTm (extR ρ) m)
ihZ-ren {ρ = ρ} cM m =
  cong₃ (λ c u v → lam (lam (absurd c (ordtr (nsuc u) v nzero
                                             (var vz) (var (vs (vs vz)))))))
        (wwᶠ²-ren {ρ = ρ} cM) (wwᶠ²-ren {ρ = ρ} m) (ren-w³ {ρ = extR ρ} m)

-- ★ two more spine peels, same construction as `wwᶠ²-ren`
wwᶠ⁴-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
           renTm (extR (extR (extR (extR (extR (extR ρ))))))
                 (w (wᶠ (wᶠ (wᶠ (wᶠ t)))))
         ≡ w (wᶠ (wᶠ (wᶠ (wᶠ (renTm (extR ρ) t)))))
wwᶠ⁴-ren {ρ = ρ} t =
  trans (ren-w {ρ = extR (extR (extR (extR (extR ρ))))} (wᶠ (wᶠ (wᶠ (wᶠ t)))))
        (cong w (trans (ren-wᶠ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ (wᶠ t))))
                 (cong wᶠ (trans (ren-wᶠ {ρ = extR (extR ρ)} (wᶠ (wᶠ t)))
                           (cong wᶠ (trans (ren-wᶠ {ρ = extR ρ} (wᶠ t))
                                     (cong wᶠ (ren-wᶠ {ρ = ρ} t))))))))

w³wᶠ²-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
            renTm (extR (extR (extR (extR (extR (extR ρ))))))
                  (w (w (w (wᶠ (wᶠ t)))))
          ≡ w (w (w (wᶠ (wᶠ (renTm (extR ρ) t)))))
w³wᶠ²-ren {ρ = ρ} t =
  trans (ren-w³ {ρ = extR (extR (extR ρ))} (wᶠ (wᶠ t)))
        (cong (λ z → w (w (w z)))
              (trans (ren-wᶠ {ρ = extR ρ} (wᶠ t)) (cong wᶠ (ren-wᶠ {ρ = ρ} t))))

ren-w⁴ : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
         renTm (extR (extR (extR (extR ρ)))) (w (w (w (w t))))
       ≡ w (w (w (w (renTm ρ t))))
ren-w⁴ {ρ = ρ} t = trans (ren-w {ρ = extR (extR (extR ρ))} (w (w (w t))))
                         (cong w (ren-w³ t))

-- ★★ the SUCCESSOR side: `descS` depends only on the measure.
descS' : {Γ : Cx} (m : RTm (Γ ∙)) → RTm ((((((Γ ∙) ∙) ∙) ∙) ∙) ∙)
descS' m =
  ordtr (nsuc (w (wᶠ (wᶠ (wᶠ (wᶠ m)))))) (w (w (w (wᶠ (wᶠ m)))))
        (nsuc (var (vs (vs (vs (vs (vs vz))))))) (var vz) (var (vs (vs vz)))

descS-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (m : RTm (Γ ∙)) →
            renTm (extR (extR (extR (extR (extR (extR ρ)))))) (descS' m)
          ≡ descS' (renTm (extR ρ) m)
descS-ren {ρ = ρ} m =
  cong₂ (λ u v → ordtr (nsuc u) v (nsuc (var (vs (vs (vs (vs (vs vz)))))))
                       (var vz) (var (vs (vs vz))))
        (wwᶠ⁴-ren {ρ = ρ} m) (w³wᶠ²-ren {ρ = ρ} m)

ihS' : {Γ : Cx} (m : RTm (Γ ∙)) → RTm ((((Γ ∙) ∙) ∙) ∙)
ihS' m = lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) (descS' m)))

ihS-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (m : RTm (Γ ∙)) →
          renTm (extR (extR (extR (extR ρ)))) (ihS' m)
        ≡ ihS' (renTm (extR ρ) m)
ihS-ren {ρ = ρ} m =
  cong (λ d → lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz))) d)))
       (descS-ren {ρ = ρ} m)

-- ★★★ …and the two AUXILIARY BRANCHES.
aZBr' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙)) → RTm Γ
aZBr' stp cM m = lam (lam (app (app (w (w stp)) (var (vs vz))) (ihZ' cM m)))

aZBr-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (stp : RTm Γ) (cM m : RTm (Γ ∙)) →
           renTm ρ (aZBr' stp cM m)
         ≡ aZBr' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
aZBr-ren {ρ = ρ} stp cM m =
  cong₂ (λ s i → lam (lam (app (app s (var (vs vz))) i)))
        (ren-w² {ρ = ρ} stp) (ihZ-ren {ρ = ρ} cM m)

aSBr' : {Γ : Cx} (stp : RTm Γ) (m : RTm (Γ ∙)) → RTm ((Γ ∙) ∙)
aSBr' stp m =
  lam (lam (app (app (w (w (w (w stp)))) (var (vs vz))) (ihS' m)))

aSBr-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (stp : RTm Γ) (m : RTm (Γ ∙)) →
           renTm (extR (extR ρ)) (aSBr' stp m)
         ≡ aSBr' (renTm ρ stp) (renTm (extR ρ) m)
aSBr-ren {ρ = ρ} stp m =
  cong₂ (λ s i → lam (lam (app (app s (var (vs vz))) i)))
        (ren-w⁴ {ρ = ρ} stp) (ihS-ren {ρ = ρ} m)

-- ★★★★ THE AUXILIARY AND THE RECURSOR — the top of the chain.
--
-- ⚠ `amrecTm` is built from the auxiliary AT THE EXTENDED CONTEXT: `AmTΠ`
--   opens `AmT` at `Δ ▹ A` with `(w stp) (wᶠ cM) (wᶠ m)`, so the
--   parameterised form carries those weakenings explicitly.
aAuxTm' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) → RTm Γ
aAuxTm' stp cM m n = natrec (aZBr' stp cM m) (aSBr' stp m) n

aAuxTm-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ}
             (stp : RTm Γ) (cM m : RTm (Γ ∙)) (n : RTm Γ) →
             renTm ρ (aAuxTm' stp cM m n)
           ≡ aAuxTm' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                     (renTm ρ n)
aAuxTm-ren {ρ = ρ} stp cM m n =
  cong₂ (λ z sb → natrec z sb (renTm ρ n))
        (aZBr-ren {ρ = ρ} stp cM m) (aSBr-ren {ρ = ρ} stp m)

amrecTm' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙)) → RTm Γ
amrecTm' stp cM m =
  lam (app (app (aAuxTm' (w stp) (wᶠ cM) (wᶠ m) m) (var vz)) (reflTm m))

-- ⭐ `reflTm` needs no law: `reflTm t = natrec unit (var vz) t`, and both
--   `unit` and `var vz` are renaming-invariant, so it commutes
--   DEFINITIONALLY.
amrecTm-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (stp : RTm Γ) (cM m : RTm (Γ ∙)) →
              renTm ρ (amrecTm' stp cM m)
            ≡ amrecTm' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
amrecTm-ren {ρ = ρ} stp cM m =
  cong (λ a → lam (app (app a (var vz)) (reflTm (renTm (extR ρ) m))))
       (trans (aAuxTm-ren {ρ = extR ρ} (w stp) (wᶠ cM) (wᶠ m) m)
              (cong₃ (λ s c μ → aAuxTm' s c μ (renTm (extR ρ) m))
                     (ren-w {ρ = ρ} stp)
                     (ren-wᶠ {ρ = ρ} cM)
                     (ren-wᶠ {ρ = ρ} m)))

-- ★★ RENAMING PAST A SUBSTITUTION — the condition, and how it LIFTS.
--
-- ⚠ A DIFFERENT SHAPE from the `-ren` family above.  Those pushed a
--   renaming past WEAKENINGS (`ren-w`/`ren-wᶠ`), where every leaf was
--   structural.  The recursive-call HANDLE is five nested SUBSTITUTIONS,
--   so it needs `rensub`, whose side condition must be supplied at each
--   level.  ⭐ Supplying it once and LIFTING beats writing five.
ren-single : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (t : RTm Γ) →
             (v : Var (Γ ∙)) →
             renTm ρ (single t v) ≡ single (renTm ρ t) (extR ρ v)
ren-single t vz     = refl
ren-single t (vs u) = refl

ren-cond-ext : {Γ Γ' Γ'' Γ₃ : Cx} {σ : Sub Γ Γ'} {ϑ : Ren Γ' Γ''}
               {σ' : Sub Γ₃ Γ''} {ϑ' : Ren Γ Γ₃} →
               (∀ v → renTm ϑ (σ v) ≡ σ' (ϑ' v)) →
               (∀ v → renTm (extR ϑ) (extS σ v) ≡ extS σ' (extR ϑ' v))
ren-cond-ext h vz     = refl
ren-cond-ext {σ = σ} h (vs u) = trans (ren-w (σ u)) (cong w (h u))

-- ★★★ THE AUXILIARY AT AN ARGUMENT — `auxIH`, parameterised.
--
-- ⚠ Note the shifted parameters: `AmTΠ` opens `AmT` at `Δ ▹ A`, so the
--   branches are built from `(w stp) (wᶠ cM) (wᶠ m)`.
auxIH' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙)) (x k : RTm Γ) → RTm Γ
auxIH' stp cM m x k =
  natrec (subTm (single x) (aZBr' (w stp) (wᶠ cM) (wᶠ m)))
         (subTm (extS (extS (single x))) (aSBr' (w stp) (wᶠ m)))
         k

auxIH-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ}
            (stp : RTm Γ) (cM m : RTm (Γ ∙)) (x k : RTm Γ) →
            renTm ρ (auxIH' stp cM m x k)
          ≡ auxIH' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                   (renTm ρ x) (renTm ρ k)
auxIH-ren {ρ = ρ} stp cM m x k =
  cong₂ (λ z sb → natrec z sb (renTm ρ k))
    -- zero branch: one `rensub`, then `aZBr-ren`, then the three spine peels
    (trans (rensub (ren-single {ρ = ρ} x) (aZBr' (w stp) (wᶠ cM) (wᶠ m)))
           (cong (subTm (single (renTm ρ x)))
                 (trans (aZBr-ren {ρ = extR ρ} (w stp) (wᶠ cM) (wᶠ m))
                        (cong₃ aZBr' (ren-w {ρ = ρ} stp)
                                     (ren-wᶠ {ρ = ρ} cM)
                                     (ren-wᶠ {ρ = ρ} m)))))
    -- successor branch: the SAME condition, LIFTED twice
    (trans (rensub (ren-cond-ext (ren-cond-ext (ren-single {ρ = ρ} x)))
                   (aSBr' (w stp) (wᶠ m)))
           (cong (subTm (extS (extS (single (renTm ρ x)))))
                 (trans (aSBr-ren {ρ = extR ρ} (w stp) (wᶠ m))
                        (cong₂ aSBr' (ren-w {ρ = ρ} stp)
                                     (ren-wᶠ {ρ = ρ} m)))))

-- ★★★★ THE RECURSIVE-CALL HANDLE, parameterised — five nested
--   substitutions over `ihS` and `auxIH`.
ihS-atP' : {Γ : Cx} (stp : RTm Γ) (cM m : RTm (Γ ∙))
           (x a k p : RTm Γ) → RTm Γ
ihS-atP' stp cM m x a k p =
  subTm (single p)
    (subTm (extS (single a))
      (subTm (extS (extS (single (auxIH' stp cM m x k))))
        (subTm (extS (extS (extS (single k))))
          (subTm (extS (extS (extS (extS (single x))))) (ihS' (wᶠ m))))))

-- ★ …AND ITS RENAMING LAW.  Five `rensub`s, and the side condition for
--   each is the SAME `ren-single` LIFTED by `ren-cond-ext` — which is the
--   whole reason that helper exists.  `auxIH-ren` and `ihS-ren` close the
--   two leaves.
ihS-atP-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (stp : RTm Γ) (cM m : RTm (Γ ∙))
              (x a k p : RTm Γ) →
              renTm ρ (ihS-atP' stp cM m x a k p)
            ≡ ihS-atP' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                       (renTm ρ x) (renTm ρ a) (renTm ρ k) (renTm ρ p)
ihS-atP-ren {ρ = ρ} stp cM m x a k p =
  trans (rensub (ren-single {ρ = ρ} p) T1)
    (cong (subTm (single (renTm ρ p)))
      (trans (rensub (ren-cond-ext (ren-single {ρ = ρ} a)) T2)
        (cong (subTm (extS (single (renTm ρ a))))
          (trans (rensub (ren-cond-ext (ren-cond-ext
                            (ren-single {ρ = ρ} auxT))) T3)
            (trans (cong (λ z → subTm (extS (extS (single z)))
                                  (renTm (extR (extR (extR ρ))) T3))
                         (auxIH-ren {ρ = ρ} stp cM m x k))
              (cong (subTm (extS (extS (single auxT'))))
                (trans (rensub (ren-cond-ext (ren-cond-ext (ren-cond-ext
                                  (ren-single {ρ = ρ} k)))) T4)
                  (cong (subTm (extS (extS (extS (single (renTm ρ k))))))
                    (trans (rensub (ren-cond-ext (ren-cond-ext (ren-cond-ext
                                      (ren-cond-ext (ren-single {ρ = ρ} x))))) T5)
                      (cong (subTm (extS (extS (extS (extS
                                      (single (renTm ρ x)))))))
                        (trans (ihS-ren {ρ = extR ρ} (wᶠ m))
                               (cong ihS' (ren-wᶠ {ρ = ρ} m)))))))))))))
  where
    -- ⚠ NAMED, not `_`.  `rensub` takes its subject EXPLICITLY, and at
    --   these depths inference cannot recover it — the meta ends up
    --   blocked on the very term it is meant to determine.
    auxT  = auxIH' stp cM m x k
    auxT' = auxIH' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                   (renTm ρ x) (renTm ρ k)
    T5 = ihS' (wᶠ m)
    T4 = subTm (extS (extS (extS (extS (single x))))) T5
    T3 = subTm (extS (extS (extS (single k)))) T4
    T2 = subTm (extS (extS (single auxT))) T3
    T1 = subTm (extS (single a)) T2


------------------------------------------------------------------------
-- ★★★ `StepExt` TRANSPORTS ALONG A TYPED RENAMING.
--
-- ★ DERIVABLE, not a new assumption: `StepExt` is ALREADY quantified over
--   renamings, so this instantiates the original at the COMPOSITE
--   `κ = ϑ ∘ ρ` and re-associates.  `Ren⊢-comp` composes the typed
--   renamings; every other step is `renren`/`renrenTy` turning
--   `renTm ϑ (renTm ρ t)` into `renTm κ t`.
--
-- ⚠ THE DIRECTIONS MATTER AND ARE EASY TO GET BACKWARDS.  `renren h`
--   points FROM the separately-applied form TO the composite.  So the
--   PREMISES (which arrive separately-applied) cast FORWARD, and the
--   CONCLUSION (which `ext` gives at the composite) casts BACK with `sym`.
--
-- ⚠⚠ `StepPW` is the hard part: doubly renaming-indexed with its OWN
--   coherence condition.  The transport calls the given `pw` at
--   `ρ³ := ϑ³ ∘ ϑ`, where its condition is `refl` and therefore always
--   available, and then re-expresses the RESULT at `σ³` using `br`.
------------------------------------------------------------------------

StepExt-ren : {Δ Θ : Ctx} {A : RTy ⌊ Δ ⌋} {cM m : RTm (⌊ Δ ⌋ ∙)}
              {stp : RTm ⌊ Δ ⌋} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} →
              Ren⊢ Δ Θ ρ → StepExt Δ A cM m stp →
              StepExt Θ (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                        (renTm ρ stp)
StepExt-ren {A = A} {cM = cM} {m = m} {stp = stp} {ρ = ρ} ρ⊢ ext
            {Θ''} {ϑ} ϑ⊢ a ih₁ ih₂ da d₁ d₂ pw =
  prv-cast
    (cong₃ (λ c e₁ e₂ → Id (El c) e₁ e₂)
           (cong (subTm (single a)) (sym cMeq))
           (cong (λ z → app (app z a) ih₁) (sym seq))
           (cong (λ z → app (app z a) ih₂) (sym seq)))
    (ext (Ren⊢-comp ρ⊢ ϑ⊢ (λ v → refl)) a ih₁ ih₂
         (⊢-cast Aeq da) (⊢-cast ihEq d₁) (⊢-cast ihEq d₂) pw')
  where
    -- `renren`/`renrenTy` at the pointwise-refl condition: separate ⇒ composite
    Aeq  = renrenTy {ϑ = ϑ} {ρ = ρ} (λ v → refl) A
    cMeq = renren (extcondR {ϑ = ϑ} {ρ = ρ} (λ v → refl)) cM
    meq  = renren (extcondR {ϑ = ϑ} {ρ = ρ} (λ v → refl)) m
    seq  = renren {ϑ = ϑ} {ρ = ρ} (λ v → refl) stp

    ihEq = cong₄ aIHTat Aeq cMeq meq (cong (subTm (single a)) meq)

    -- ⚠ SIGNED and PINNED: as a bare lambda, `StepPW`'s three implicit
    --   renamings cannot be solved — the coherence mentions a bound
    --   variable, so the meta may not depend on it.
    pw' : StepPW _ A cM m Θ'' (λ v → ϑ (ρ v)) a ih₁ ih₂
    pw' {Θ³} {ϑ³} {σ³} ϑ³⊢ br y q dy dq =
      prv-cast
        (cong (λ c → Id (El (subTm (single y) c))
                        (app (app (renTm ϑ³ ih₁) y) q)
                        (app (app (renTm ϑ³ ih₂) y) q))
              (renren (extcondR br) cM))
        (pw {Θ³} {ϑ³} {λ v → ϑ³ (ϑ v)} ϑ³⊢ (λ v → refl) y q
            (⊢-cast (sym (renrenTy br A)) dy)
            (⊢-cast (cong₂ (λ u v → Hom Nat (nsuc (subTm (single y) u))
                                            (renTm ϑ³ (subTm (single a) v)))
                           (sym (renren (extcondR br) m)) (sym meq))
                    dq))


------------------------------------------------------------------------
-- ★★★★★ `AmTΠ` AT A RENAMED CONTEXT — route (b)'s payoff.
--
-- ⚠ WHAT THIS BUYS.  The irrelevance layer (`irrT`, `irrElim`, `irr-ind`)
--   takes `x y : RTm ⌊ Δ ⌋` — the CONTEXT is renaming-indexed, the
--   ARGUMENTS are not.  `amrec-ind`'s `IndPW` quantifies over an ARBITRARY
--   `y : RTm ⌊ Θ ⌋`, so it cannot be stated through `AmTΠ Δ …`.
--
-- ★ Instantiating the module at `Θ` makes that module's OWN `Δ` be `Θ`,
--   so its irrelevance applies to `Θ`-level arguments with NO change to
--   the irrelevance layer itself — the largest piece of this file is
--   REUSED, not generalised.
--
-- ★★ AND THE CONNECTION BACK is the `-ren` family: `amrecTm-ren` says this
--   instantiation's recursor IS `renTm ρ` of the original's, so facts
--   proved here transport to statements about `renTm ρ amrecTm`.
--
-- ⭐ The idiom is the module's own: `AmTΠ` already opens `AmT` at `Δ ▹ A`
--   with renamed parameters, bridged by `aStepT-ren`.  This is that, at an
--   arbitrary typed renaming.
------------------------------------------------------------------------

module AmTΠ-at {Δ Θ : Ctx} (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙))
               (stp : RTm ⌊ Δ ⌋)
               (dA   : Δ ⊢ty A)
               (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
               (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
               (dstp : Δ ⊢ stp ∷ aStepT A cM m)
               {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (ρ⊢ : Ren⊢ Δ Θ ρ)
               where

  open AmTΠ Θ (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m) (renTm ρ stp)
            (ren-ty dA ρ⊢)
            (ren-lemma dcM (Ren⊢-ext ρ⊢))
            (ren-lemma dm  (Ren⊢-ext ρ⊢))
            (⊢-cast (aStepT-ren A cM m) (ren-lemma dstp ρ⊢))
            public

  -- ★ the side condition its lemmas need, transported rather than assumed
  extΘ : StepExt Δ A cM m stp →
         StepExt Θ (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                   (renTm ρ stp)
  extΘ = StepExt-ren ρ⊢
