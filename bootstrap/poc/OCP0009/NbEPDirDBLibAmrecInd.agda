------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — `amrec-ind`: INDUCTION OVER THE MEASURE RECURSOR.
--
-- ⚠ PROMOTED FROM `…SpikeAmrecInd` 2026-08-21, the day it was finished.
--   Standing rule: finished library material does not live in a Spike, and
--   every branch of it is exercised by an `…Examples*` module — here
--   `…ExamplesAmrecInd`.  `sweep.sh` classifies `Spike*` as PROBES, which
--   are "reported, never fail the sweep", so a result left in one is not
--   actually guarded.
--
-- ★ THE ENTRY POINT is `Concl.amrecInd`.  A client owes `StepExt` (the step
--   respects pointwise equality of handles) and `IndStep`, and nothing else.
--
-- ★ THE HISTORY BELOW IS KEPT because it is the reason the shape is what it
--   is — 43 logged attempts (`AMREC-IND-LOG.md`).
--
-- ★ WHY THIS ORDER (STATE IT BEFORE PROVING IT).
--
--   Gap A's expensive failures came from committing to a
--   SHAPE and then fighting it — 52 attempts, seven on one derivation.  So
--   write the statement, check it is WELL-FORMED, and only then prove it.
--   A malformed statement is cheap to find here and expensive to find with
--   a half-built proof on top of it.
--
-- ★★ THE MOTIVE IS A CODE IN **TWO** SLOTS, and both are forced:
--
--       ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U
--          ↑ the ARGUMENT      ↑ the RESULT
--
--   `gcd (a,b) ∣ a` mentions the input pair AND the output, so a motive
--   over the result alone cannot state gap B's obligation.  And it must be
--   a CODE, not an `RTy`, because `⊢jsub` transports code families — the
--   constraint that forced certificate irrelevance in `amrec-unfold-Id`.
--   ⚠ `dvdT` clears it: `⊢dvdCode` is green.
--
-- ⚠ SLOT ORDER IS NOT FREE.  `single` fills the TOP slot, so the RESULT
--   must be substituted first and the ARGUMENT second.  Writing it the
--   other way round needs a substitution-composition lemma for no gain.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibAmrecInd where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; RTm; El; U; Nat; Hom; Π; var; vz; vs; Var; app; nsuc; nzero; natrec
        ; lam; absurd; jsub; Id; ⌜Id⌝; idrefl; ⌜Id⌝-cong₃; ordtr; unit
        ; subTm; subTy; renTy; renTm; Ren; extR; extS; renTy-renTy; Sub
        ; subTm-subTm; subTm-renTm; subTm-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢app; ⊢nsuc; ⊢lam; ⊢nzero; nrs; ⊢jsub
        ; ty-El; ty-Π; ty-Hom; ty-Nat
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢conv; csymᵀ; credᵀ; El-⌜Id⌝; ⊢ordtr
        ; Hom-Nat-ss; ⊢natrec )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ⊢[]; Ren⊢; Ren⊢-ext; ren-lemma; ren-ty
        ; Sub⊢; Sub⊢-ext; ⊢single; sub-lemma; wk-cancel-tm )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat; aIHT; aIHT-fit )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; wᶠ¹-single; ⊢wkᶠ; sub-w; cong₃; cong₄; ren-sub )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( aStepT; aStepT-ren; Prv; prv; prvOk; prvTm; StepExt; idOfRed
        ; prv-cast; wR; Ren⊢-comp; renren; renrenTy; extcondR; sub1-ren
        ; subren; subrenTy; extcond; renTy-idR; renTm-idR; ren-subTy'
        ; module AmTΠ )
open import poc.OCP0009.NbEPDirDBLibAmrecRen
  using ( amrecTm'; amrecTm-ren; ihS-atP'; ihS-atP-ren; StepExt-ren )
open import poc.OCP0009.NbEPDirDBLibOrd using ( ⊢strong-base )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; ⊢le-suc; reflTm )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBLibNatrec using ( Ren⊢-id )

------------------------------------------------------------------------
-- ★★ `Id` SYMMETRY, AT THE `Prv` LEVEL.
--
-- ⚠ WHY IT IS RESTATED HERE.  `…ExamplesId` already derives `⊢sym`, and
--   nothing in that derivation is example-specific — it uses only the
--   kernel.  But a LIBRARY may not import an EXAMPLE (the 2026-08-21
--   inversion), and this spike is library material.  ⇒ restate the four
--   lines here; hoist BOTH to a Lib module at consolidation, and let
--   `…ExamplesId` keep its own copy as the acceptance test.
--
-- ★ WHY STEP 6 NEEDS IT AT ALL.  `ihCall-amrec` points FROM the handle's
--   call TO `amrec y`, while `⊢transportP` carries the motive ALONG a
--   path — and the induction hypothesis arrives at the `amrec y` end.
--   ⇒ the path has to be turned round exactly once.
------------------------------------------------------------------------

symTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
symTm c t p = jsub (⌜Id⌝ (renTm vs c) (var vz) (renTm vs t)) p (idrefl c t)

⊢symId : {Γ : Ctx} {c t u p : RTm ⌊ Γ ⌋} →
         Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
         Γ ⊢ p ∷ Id (El c) t u →
         Γ ⊢ symTm c t p ∷ Id (El c) u t
⊢symId {c = c} {t = t} {u = u} {p = p} dc dt du dp =
  ⊢conv
    (⊢-cast (cong El (⌜Id⌝-cong₃ (wk-cancel-tm u c) refl (wk-cancel-tm u t)))
      (⊢jsub (⊢⌜Id⌝ (⊢wk dc) (⊢var here) (⊢wk dt))
             dt du dp
             (⊢-cast (cong El (sym (⌜Id⌝-cong₃ (wk-cancel-tm t c) refl
                                               (wk-cancel-tm t t))))
                     (⊢conv (⊢idrefl dc dt)
                            (csymᵀ (credᵀ (El-⌜Id⌝ c t t)))))))
    (credᵀ (El-⌜Id⌝ c u t))

prvSym : {Γ : Ctx} {c t u : RTm ⌊ Γ ⌋} →
         Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
         Prv Γ (Id (El c) t u) → Prv Γ (Id (El c) u t)
prvSym {c = c} {t = t} dc dt du (prv e d) = prv (symTm c t e) (⊢symId dc dt du d)

module Stmt (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
            (dA   : Δ ⊢ty A)
            (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
            (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
            (dstp : Δ ⊢ stp ∷ aStepT A cM m)
            where

  open AmTΠ Δ A cM m stp dA dcM dm dstp using ( amrecTm; ⊢amrecΠ )

  ------------------------------------------------------------------------
  -- ★ THE RECURSIVE VALUE, AT THE BOUND ARGUMENT.  `amrec` applied to the
  --   `A`-slot's own variable — this is what the motive's result slot gets
  --   filled with.
  ------------------------------------------------------------------------

  valAt : RTm (⌊ Δ ⌋ ∙)
  valAt = app (w amrecTm) (var vz)

  ⊢valAt : (Δ ▹ A) ⊢ valAt ∷ El cM
  ⊢valAt = ⊢-cast (cong El (wᶠ¹-single cM)) (⊢app (⊢wk ⊢amrecΠ) (⊢var here))

  ------------------------------------------------------------------------
  -- ★★ THE GOAL TYPE: `P` at the argument `x` and the value `amrec x`.
  ------------------------------------------------------------------------

  IndAt : RTm ((⌊ Δ ⌋ ∙) ∙) → RTm ⌊ Δ ⌋ → RTy ⌊ Δ ⌋
  IndAt P x = El (subTm (single x) (subTm (single valAt) P))

  -- ★ …and it IS a type, whenever `P` is a code and `x` an element.
  ⊢IndAt : {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
           ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
           {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
           Δ ⊢ty IndAt P x
  ⊢IndAt dP dx = ty-El (⊢[] (⊢[] dP ⊢valAt) dx)

------------------------------------------------------------------------
-- ★★★ THE MOTIVE, APPLIED — under an ambient renaming.
--
-- Every premise below states `P` at some (argument, result) pair in some
-- context reached by a renaming, so this is factored once.
--
-- ⚠ SLOT ORDER, again: `single` fills the TOP slot, so the RESULT goes in
--   first and the ARGUMENT second.  Same convention as `IndAt`.
------------------------------------------------------------------------

-- ⚠⚠ THE ARGUMENT SLOT MUST BE FILLED **FIRST**, AND THE REASON IS A
--   DEPENDENCY, not a convention.  The RESULT slot's type is `El cM`,
--   which DEPENDS on the argument slot.  So substituting the result first
--   is type-correct only when the value is written as a function of the
--   argument VARIABLE — and an arbitrary `val` is not.
--
--   ⭐ `IndAt` gets away with the other order precisely because its
--   `valAt = app (w amrecTm) (var vz)` IS such a function.  That is a
--   special case, not the general rule, and reading it as the rule was
--   attempt 1's mistake: the wrong order still checks as a TERM operation
--   (attempt 3 was green) and only fails when a TYPING is demanded of it.
--
-- ⇒ `extS (single y)` fills the argument and keeps the result slot open;
--   `single val` then closes it, at the now-instantiated type `El cM[y]`.
-- ★★ …and the motive with the ARGUMENT filled but the RESULT SLOT STILL
--   OPEN.  ⭐ This is the piece `⊢jsub` wants: it transports a CODE FAMILY
--   over the type being equated, and here that type is the recursor's
--   result.  Factoring it out is what makes the successor branch's
--   transport a single `⊢jsub` instead of a bespoke construction.
PFam : {Γ Γ' : Cx} (ρ : Ren Γ Γ') (P : RTm ((Γ ∙) ∙)) (y : RTm Γ') → RTm (Γ' ∙)
PFam ρ P y = subTm (extS (single y)) (renTm (extR (extR ρ)) P)

PAtR : {Γ Γ' : Cx} (ρ : Ren Γ Γ') (P : RTm ((Γ ∙) ∙)) (y val : RTm Γ') → RTm Γ'
PAtR ρ P y val = subTm (single val) (PFam ρ P y)

------------------------------------------------------------------------
-- ★★★ …AND ITS SUBSTITUTION LAW, GENERIC IN σ.
--
-- ⭐ Stated with a POINTWISE side condition, exactly like `irrT-sub`.  One
--   lemma then serves every instantiation — the `natrec`'s zero branch
--   (`single nzero`), its successor branch (`nrs`), and any later client —
--   instead of one bespoke peel per branch.
--
-- ★ THE RECIPE: both sides are `subTm _ P` once the nested substitutions
--   are FLATTENED (`subTm-renTm` then `subTm-subTm`), so the whole proof
--   is one `subTm-cong` over a THREE-CASE bridge:
--     vz        the result slot   — both sides give `subTm σ val`
--     vs vz     the argument slot — both give `subTm σ y`, via `wk-single`
--     vs (vs v) the ambient       — closed by the side condition `h`
------------------------------------------------------------------------

PAtR-sub : {Γ Γ' Γ'' : Cx} {σ : Sub Γ' Γ''} (ρ : Ren Γ Γ') (ρ' : Ren Γ Γ'') →
           (∀ v → σ (ρ v) ≡ var (ρ' v)) →
           (P : RTm ((Γ ∙) ∙)) (y val : RTm Γ') →
           subTm σ (PAtR ρ P y val)
         ≡ PAtR ρ' P (subTm σ y) (subTm σ val)
PAtR-sub {σ = σ} ρ ρ' h P y val =
  trans (cong (subTm σ) (cong (subTm (single val)) (subTm-renTm P)))
    (trans (cong (subTm σ) (subTm-subTm P))
      (trans (subTm-subTm P)
        (trans (subTm-cong bridge P)
          (trans (sym (subTm-subTm P))
                 (cong (subTm (single (subTm σ val))) (sym (subTm-renTm P)))))))
  where
    bridge : ∀ v → _
    bridge vz          = refl
    bridge (vs vz)     = trans (cong (subTm σ) (wk-single {v = val} y))
                               (sym (wk-single {v = subTm σ val} (subTm σ y)))
    bridge (vs (vs v)) = h v

------------------------------------------------------------------------
-- ★★★ THE INDUCTION HYPOTHESIS, POINTWISE — `P` holds of EVERY recursive
--   call the handle `ih` can make.
--
-- ⚠ DOUBLY RENAMING-INDEXED, exactly like `StepPW`, and for the same
--   reason: the caller instantiates it under further binders, so a
--   `Θ`-only statement is not general enough.  The coherence condition
--   `ϑ ∘ ρ ≡ ρ'` is what lets the two renamings be related at all.
--   ⭐ Recorded 2026-08-16 as "StepExt's premise must be renaming-indexed";
--   the same applies here and is cheaper to get right the first time.
------------------------------------------------------------------------

IndPW : (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙))
        (P : RTm ((⌊ Δ ⌋ ∙) ∙))
        (Θ : Ctx) (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (a ih : RTm ⌊ Θ ⌋) → Set
IndPW Δ A cM m P Θ ρ a ih =
  {Θ' : Ctx} {ϑ : Ren ⌊ Θ ⌋ ⌊ Θ' ⌋} {ρ' : Ren ⌊ Δ ⌋ ⌊ Θ' ⌋} →
  Ren⊢ Θ Θ' ϑ → (∀ v → ϑ (ρ v) ≡ ρ' v) →
  (y q : RTm ⌊ Θ' ⌋) →
  Θ' ⊢ y ∷ renTy ρ' A →
  Θ' ⊢ q ∷ Hom Nat (nsuc (subTm (single y) (renTm (extR ρ') m)))
                   (renTm ϑ (subTm (single a) (renTm (extR ρ) m))) →
  Prv Θ' (El (PAtR ρ' P y (app (app (renTm ϑ ih) y) q)))

------------------------------------------------------------------------
-- ★★★★ THE STEP PREMISE — the caller's half, and the ONLY thing a client
--   of `amrec-ind` should have to discharge.
--
--   "if `P` holds of every recursive call, it holds of the step's result"
--
-- ★ COMPARE `StepExt`, which says the step RESPECTS pointwise equality of
--   handles.  This says it PRESERVES a predicate.  Same shape, different
--   payload — which is the evidence that the shape is the right one.
------------------------------------------------------------------------

IndStep : (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
          (P : RTm ((⌊ Δ ⌋ ∙) ∙)) → Set
IndStep Δ A cM m stp P =
  {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
  (a ih : RTm ⌊ Θ ⌋) →
  Θ ⊢ a ∷ renTy ρ A →
  Θ ⊢ ih ∷ aIHTat (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                  (subTm (single a) (renTm (extR ρ) m)) →
  IndPW Δ A cM m P Θ ρ a ih →
  Prv Θ (El (PAtR ρ P a (app (app (renTm ρ stp) a) ih)))

------------------------------------------------------------------------
-- ★★★★★ …AND THE COMBINATOR'S FULL TYPE.
--
-- Stated as a `Set` so the SPECIFICATION can be checked well-formed
-- before any of it is proved, and so a client can take it as a PARAMETER
-- and be written against it while the proof is still open.  (`--safe`
-- forbids `postulate`, which is the usual way to do this; a parameter is
-- the honest substitute and is strictly better — it cannot leak into
-- anything that does not ask for it.)
--
-- ⚠ WHAT IS AND IS NOT ESTABLISHED HERE.  This is a well-formed STATEMENT
--   and nothing more.  No instance exists, so nothing below is yet
--   evidence that any function has the property — exactly the status
--   `StepExt` had before `…GcdStepExtA` discharged it.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ AND THE TYPING THAT DECIDES THE ORDER.  If `PAtR` is well-ordered
--   this goes through; if not, no arrangement of casts saves it, because
--   the mismatch is a genuine dependency.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ `AmTΠ` PLUS THE HANDLE'S TYPING — and the same module AT A RENAMED
--   CONTEXT.
--
-- ⚠ WHY NOT `AmTΠ-at`.  Step 6 needs `⊢ihS-atP` at `Θ'` as well as at `Δ`,
--   and `⊢ihS-atP` is not in `…LibAmrec`.  Opening `AmTΠ-at` AND a second
--   module carrying `⊢ihS-atP` would instantiate `AmTΠ` twice at the same
--   parameters; extending the instantiation once does not.
--
-- ⚠ AND `⊢ihS-atP` IS NOT PUT IN `…LibAmrec`.  That module is a measured
--   OOM hazard for its clients (see `…LibAmrecRen`'s header: +460 lines
--   turned a 6m27s build into an OOM).  It goes there at consolidation,
--   with a measurement, not before.
------------------------------------------------------------------------

module Handle (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
              (dA   : Δ ⊢ty A)
              (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
              (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
              (dstp : Δ ⊢ stp ∷ aStepT A cM m)
              where

  open AmTΠ Δ A cM m stp dA dcM dm dstp public

  ------------------------------------------------------------------------
  -- ★★★ THE HANDLE, TYPED — `ihS-atP` is `ihS-atR` AT THE IDENTITY.
  --
  -- ⚠ WHY IT WAS MISSING.  The library types `ihS-atR` — the handle at an
  --   ARBITRARY renaming — because the irrelevance layer consumes it under
  --   binders.  Nobody had needed the un-renamed twin, so `⊢ihS-atP` did
  --   not exist.  Step 6 needs it TWICE: `⊢transportP` demands a typing of
  --   BOTH endpoints of the path, and one endpoint is the handle's call.
  --
  -- ★ The peel is `descS-at-idR`'s, verbatim: `auxAt idR x k` collapses to
  --   `auxIH x k`, and the `renTm (extR⁴ idR)` layer vanishes.  Nothing
  --   here is content; it is the standing identity-renaming tax.
  ------------------------------------------------------------------------

  extR⁴-idR : ∀ v → extR (extR (extR (extR idR))) v ≡ v
  extR⁴-idR = extR-id (extR-id (extR-id (extR-id (λ v → refl))))

  ihS-atP-id : (x a k p : RTm ⌊ Δ ⌋) →
               ihS-atR idR x a k p ≡ ihS-atP x a k p
  ihS-atP-id x a k p =
    cong₂ (λ u t → subTm (single p)
                     (subTm (extS (single a))
                       (subTm (extS (extS (single u)))
                         (subTm (extS (extS (extS (single k)))) t))))
          (auxAt-id x k)
          (renTm-idR extR⁴-idR
                     (subTm (extS (extS (extS (extS (single x))))) ihS))

  Aid : renTy idR A ≡ A
  Aid = renTy-idR (λ v → refl) A

  cMid : renTm (extR idR) cM ≡ cM
  cMid = renTm-idR (extR-id (λ v → refl)) cM

  ⊢ihS-atP : {x a k p : RTm ⌊ Δ ⌋} →
             Δ ⊢ x ∷ A → Δ ⊢ k ∷ Nat → Δ ⊢ a ∷ A →
             Δ ⊢ p ∷ Hom Nat (subTm (single a) m) (nsuc k) →
             Δ ⊢ ihS-atP x a k p ∷ aIHTat A cM m (subTm (single a) m)
  ⊢ihS-atP {x = x} {a = a} {k = k} {p = p} dx dk da dp =
    subst (λ t → Δ ⊢ t ∷ aIHTat A cM m (subTm (single a) m))
          (ihS-atP-id x a k p)
          (⊢-cast (cong₄ aIHTat Aid cMid mId (cong (subTm (single a)) mId))
                  (⊢ihS-atR Ren⊢-id dx dk
                            (⊢-cast (sym Aid) da)
                            (⊢-cast (cong (λ t → Hom Nat (subTm (single a) t)
                                                         (nsuc k))
                                          (sym mId))
                                    dp)))


module Handle-at {Δ Θ : Ctx} (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙))
                 (stp : RTm ⌊ Δ ⌋)
                 (dA   : Δ ⊢ty A)
                 (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
                 (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
                 (dstp : Δ ⊢ stp ∷ aStepT A cM m)
                 {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (ρ⊢ : Ren⊢ Δ Θ ρ)
                 where

  open Handle Θ (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m) (renTm ρ stp)
              (ren-ty dA ρ⊢)
              (ren-lemma dcM (Ren⊢-ext ρ⊢))
              (ren-lemma dm  (Ren⊢-ext ρ⊢))
              (⊢-cast (aStepT-ren A cM m) (ren-lemma dstp ρ⊢))
              public

  -- ★ the side condition, transported rather than assumed (`AmTΠ-at.extΘ`)
  extΘ : StepExt Δ A cM m stp →
         StepExt Θ (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                   (renTm ρ stp)
  extΘ = StepExt-ren ρ⊢


module Typing (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
              (dA   : Δ ⊢ty A)
              (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
              (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
              (dstp : Δ ⊢ stp ∷ aStepT A cM m)
              where

  open Handle Δ A cM m stp dA dcM dm dstp
    using ( amrecTm; ⊢amrecΠ; ⊢amrecPt; idR; auxAt; auxAt-id; auxIH
          ; ihS; ihS-atP; ihS-atR; ⊢ihS-atR; ⊢ihS-atP; ih-app
          ; amrec-β; irrT; irrT-sub; irrElim; irr-ind; descS-at; ⊢descS-at
          ; ihCall-amrec; amrec-unfold-Id; mId; extR-id; Aid; cMid )

  -- ★★ the family with the RESULT SLOT OPEN — what `⊢jsub` transports.
  ⊢PFam : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
          {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
          ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
          {y : RTm ⌊ Θ ⌋} → Θ ⊢ y ∷ renTy ρ A →
          (Θ ▹ El (subTm (single y) (renTm (extR ρ) cM))) ⊢ PFam ρ P y ∷ U
  ⊢PFam ρ⊢ dP dy =
    sub-lemma (ren-lemma dP (Ren⊢-ext (Ren⊢-ext ρ⊢)))
              (Sub⊢-ext (⊢single dy))

  ⊢PAtR : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
          {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
          ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
          {y val : RTm ⌊ Θ ⌋} →
          Θ ⊢ y ∷ renTy ρ A →
          Θ ⊢ val ∷ El (subTm (single y) (renTm (extR ρ) cM)) →
          Θ ⊢ PAtR ρ P y val ∷ U
  ⊢PAtR ρ⊢ dP dy dval = ⊢[] (⊢PFam ρ⊢ dP dy) dval

  ------------------------------------------------------------------------
  -- ★★★★★ STEP 5 — TRANSPORTING THE MOTIVE ALONG THE UNFOLDING.
  --
  -- The successor branch gets `P` at the STEP's result and needs it at
  -- `amrec`'s.  `amrec-unfold-Id` supplies the `Id` between them; this
  -- moves `P` across it.
  --
  -- ⭐ AND IT IS A DIRECT `⊢jsub`, because `PFam` is exactly the shape
  --   `⊢jsub` transports: a CODE FAMILY over the type being equated, which
  --   here is the recursor's result type `El cM[y]`.  Factoring `PFam` out
  --   of `PAtR` turned the piece I had flagged as the expensive one into a
  --   single application.
  --
  -- ⚠ Gap A's equation 4 needed `congAt` plus a hand-built one-hole context
  --   for the same job.  The difference is not cleverness — it is that the
  --   motive here was designed as a CODE from the start, so `⊢jsub` applies
  --   without an encoding step.
  ------------------------------------------------------------------------

  ⊢transportP : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
                {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
                ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
                {y t u p e : RTm ⌊ Θ ⌋} →
                Θ ⊢ y ∷ renTy ρ A →
                Θ ⊢ t ∷ El (subTm (single y) (renTm (extR ρ) cM)) →
                Θ ⊢ u ∷ El (subTm (single y) (renTm (extR ρ) cM)) →
                Θ ⊢ p ∷ Id (El (subTm (single y) (renTm (extR ρ) cM))) t u →
                Θ ⊢ e ∷ El (PAtR ρ P y t) →
                Θ ⊢ jsub (PFam ρ P y) p e ∷ El (PAtR ρ P y u)
  ⊢transportP ρ⊢ dP dy dt du dp de = ⊢jsub (⊢PFam ρ⊢ dP dy) dt du dp de

  ------------------------------------------------------------------------
  -- ★★★★★ STEP 6 — `IndPW` FROM THE `natrec`'s INDUCTION HYPOTHESIS.
  --
  -- ⚠ STATED FIRST, PROVED SECOND — the discipline that caught attempt 1's
  --   slot order and the `μ x < n` shift, both before any proof was built
  --   on them.
  --
  -- ★ THE SEMANTIC CONTENT OF THE `natrec`'s IH, as a renaming-indexed
  --   `Set`: "P holds at (y, amrec y) for every `y` whose measure is BELOW
  --   the bound `k`".  The `natrec` supplies this as a TERM of type
  --   `IndB P`; `IHAt` is what that term MEANS, in the form the successor
  --   branch can consume.
  ------------------------------------------------------------------------

  IHAt : {Θ : Ctx} (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (P : RTm ((⌊ Δ ⌋ ∙) ∙))
         (k : RTm ⌊ Θ ⌋) → Set
  IHAt {Θ} ρ P k =
    {Θ' : Ctx} {ϑ : Ren ⌊ Θ ⌋ ⌊ Θ' ⌋} {ρ' : Ren ⌊ Δ ⌋ ⌊ Θ' ⌋} →
    Ren⊢ Θ Θ' ϑ → (∀ v → ϑ (ρ v) ≡ ρ' v) →
    (y c : RTm ⌊ Θ' ⌋) →
    Θ' ⊢ y ∷ renTy ρ' A →
    Θ' ⊢ c ∷ Hom Nat (nsuc (subTm (single y) (renTm (extR ρ') m)))
                     (renTm ϑ k) →
    Prv Θ' (El (PAtR ρ' P y (app (renTm ρ' amrecTm) y)))

  ------------------------------------------------------------------------
  -- ★★ …AND WHAT STEP 6 MUST PRODUCE.
  --
  -- ⚠ THE GAP BETWEEN THEM, which is the whole content of step 6:
  --   `IHAt` speaks about `amrec y`; `IndPW` speaks about the HANDLE's
  --   call `app (app (renTm ϑ ih) y) q`.  Those are not syntactically the
  --   same term — `ih-app` reduces the handle to the AUXILIARY at bound
  --   `k`, while `amrec-β` reduces `amrec y` to the auxiliary at ITS OWN
  --   bound `μ y`.
  --
  -- ★ `ihCall-amrec` — now exported by `AmTΠ-at`, hence available at ANY
  --   renaming — is exactly that equation, and `⊢transportP` moves `P`
  --   across it.  ⇒ step 6 is: instantiate the IH, then transport.
  --
  -- ⚠ AND THE CERTIFICATE HAS TO BE BUILT: `IndPW` hands over
  --   `q : nsuc (μ y) ≤ μ a`, while `IHAt` wants `nsuc (μ y) ≤ k`.  The
  --   successor branch's own hypothesis gives `μ a ≤ k`, so the two
  --   compose by `⊢trans` — the ORDER computing again.
  ------------------------------------------------------------------------

  -- ★ `ihCall-amrec` MOVED into `AmTΠ` (`…LibAmrec`) 2026-08-20, so that
  --   `AmTΠ-at` exports it — i.e. so the bridge is available at a RENAMED
  --   context, which is what `IndPW` needs.  Re-exported by the `open`
  --   above.



  ------------------------------------------------------------------------
  -- ★★★★★★ STEP 6, PROVED — `IndPW` FROM THE `natrec`'s IH.
  --
  -- ★ THE SHAPE, four moves and no more:
  --     1. `ihCall-amrec` at `Θ'`   the handle's call IS `amrec y`
  --     2. `prvSym`                 …turned round, because the IH lands at
  --                                 the `amrec y` end and the goal is at
  --                                 the call end
  --     3. `⊢transportP`            carry `P` across it
  --     4. `ihS-atP-ren`            re-express `Θ'`'s handle as `renTm ϑ`
  --                                 of `Θ`'s, which is what `IndPW` says
  --
  -- ⚠ THE CERTIFICATE IS BUILT, NOT INHERITED.  `IndPW` hands over
  --   `q : nsuc (μ y) ≤ ϑ (μ a)` and `IHAt` wants `nsuc (μ y) ≤ ϑ k`, so
  --   the caller must supply `pk : μ a ≤ k` as well as the `p : μ a ≤ suc k`
  --   the handle itself carries.  ⭐ BOTH are on the successor branch's
  --   hypothesis `nsuc (μ a) ≤ suc k`: the order COMPUTES, so that IS
  --   `μ a ≤ k`, and `p` is one `⊢le-suc` above it.  Taking the two
  --   separately keeps this lemma independent of how they are derived.
  --
  -- ⚠ `ih` IS NOT ABSTRACT HERE, and it cannot be.  `IndPW` quantifies over
  --   an arbitrary handle, but the bridge is a fact about THE handle the
  --   successor branch builds — so step 6 is stated at `ihS-atP` and the
  --   `IndStep` client instantiates `IndPW`'s `ih` to it.
  --
  -- ⚠ STATED WITH THE **PRIMED** HANDLE (`ihS-atP'`), not `Handle-at`'s.
  --   The two agree definitionally (`…SpikeAgree`), and the primed form is
  --   a top-level name, so the statement does not drag a module
  --   instantiation into every client's type.
  ------------------------------------------------------------------------

  ihToPW : StepExt Δ A cM m stp →
           {P : RTm ((⌊ Δ ⌋ ∙) ∙)} → ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
           {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} → Ren⊢ Δ Θ ρ →
           (a k p pk : RTm ⌊ Θ ⌋) →
           Θ ⊢ a ∷ renTy ρ A → Θ ⊢ k ∷ Nat →
           Θ ⊢ p  ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) (nsuc k) →
           Θ ⊢ pk ∷ Hom Nat (subTm (single a) (renTm (extR ρ) m)) k →
           IHAt ρ P k →
           IndPW Δ A cM m P Θ ρ a
                 (ihS-atP' (renTm ρ stp) (renTm (extR ρ) cM) (renTm (extR ρ) m)
                           a a k p)
  ihToPW ext {P = P} dP {Θ = Θ} {ρ = ρ} ρ⊢ a k p pk da dk dp dpk ihA
         {Θ' = Θ'} {ϑ = ϑ} {ρ' = ρ'} ϑ⊢ br y q dy dq =
    prv-cast (cong (λ t → El (PAtR ρ' P y (app (app t y) q))) (sym handleEq))
             (prv _ (⊢transportP ρ'⊢ dP dy dAmr dCall
                                 (prvOk pathBack) (prvOk baseAt)))
    where
      ρ'⊢ : Ren⊢ Δ Θ' ρ'
      ρ'⊢ = Ren⊢-comp ρ⊢ ϑ⊢ br

      -- ★ the recursor's whole apparatus, AT `Θ'` — irrelevance included.
      module R = Handle-at A cM m stp dA dcM dm dstp ρ'⊢

      Aρ'  = renTy ρ' A
      cMρ' = renTm (extR ρ') cM
      mρ'  = renTm (extR ρ') m

      ϑa = renTm ϑ a
      ϑk = renTm ϑ k
      ϑp = renTm ϑ p

      μy = subTm (single y) mρ'
      μa = subTm (single ϑa) mρ'

      -- ⚠ the ONE naturality fact everything below casts by: the measure
      --   at a renamed carrier.  `IndPW` states it as `renTm ϑ (μ a)`;
      --   every lemma at `Θ'` wants it as `μ (ϑ a)`.
      μEq : renTm ϑ (subTm (single a) (renTm (extR ρ) m)) ≡ μa
      μEq = sub1-ren ρ ρ' br a m

      dcM' : (Θ' ▹ Aρ') ⊢ cMρ' ∷ U
      dcM' = ren-lemma dcM (Ren⊢-ext ρ'⊢)

      dm' : (Θ' ▹ Aρ') ⊢ mρ' ∷ Nat
      dm' = ren-lemma dm (Ren⊢-ext ρ'⊢)

      dϑa : Θ' ⊢ ϑa ∷ Aρ'
      dϑa = ⊢-cast (renrenTy {ϑ = ϑ} {ρ = ρ} {ρ' = ρ'} br A) (ren-lemma da ϑ⊢)

      dϑk : Θ' ⊢ ϑk ∷ Nat
      dϑk = ren-lemma dk ϑ⊢

      dϑp : Θ' ⊢ ϑp ∷ Hom Nat μa (nsuc ϑk)
      dϑp = ⊢-cast (cong (λ t → Hom Nat t (nsuc ϑk)) μEq) (ren-lemma dp ϑ⊢)

      dϑpk : Θ' ⊢ renTm ϑ pk ∷ Hom Nat μa ϑk
      dϑpk = ⊢-cast (cong (λ t → Hom Nat t ϑk) μEq) (ren-lemma dpk ϑ⊢)

      dq' : Θ' ⊢ q ∷ Hom Nat (nsuc μy) μa
      dq' = ⊢-cast (cong (Hom Nat (nsuc μy)) μEq) dq

      dμy : Θ' ⊢ μy ∷ Nat
      dμy = ⊢[] dm' dy

      dμa : Θ' ⊢ μa ∷ Nat
      dμa = ⊢[] dm' dϑa

      dcU : Θ' ⊢ subTm (single y) cMρ' ∷ U
      dcU = ⊢[] dcM' dy

      -- ★★ THE CERTIFICATE THE IH WANTS, COMPOSED: `nsuc (μ y) ≤ μ a` and
      --    `μ a ≤ k`, both at `Θ'`, chained by the order's transport.
      cTm : RTm ⌊ Θ' ⌋
      cTm = ordtr (nsuc μy) μa ϑk q (renTm ϑ pk)

      dc : Θ' ⊢ cTm ∷ Hom Nat (nsuc μy) ϑk
      dc = ⊢ordtr (⊢nsuc dμy) dμa dϑk dq' dϑpk

      -- 1. the IH, instantiated — `P` at `(y , amrec y)`
      base : Prv Θ' (El (PAtR ρ' P y (app (renTm ρ' amrecTm) y)))
      base = ihA ϑ⊢ br y cTm dy dc

      -- ⚠ `amrecTm` at `Θ'` is `renTm ρ'` of the one at `Δ` — the `-ren`
      --   family's whole point, and the reason `IHAt` could be stated
      --   about `renTm ρ' amrecTm` in the first place.
      amrEq : renTm ρ' amrecTm ≡ R.amrecTm
      amrEq = amrecTm-ren {ρ = ρ'} stp cM m

      baseAt : Prv Θ' (El (PAtR ρ' P y (app R.amrecTm y)))
      baseAt = prv-cast (cong (λ t → El (PAtR ρ' P y (app t y))) amrEq) base

      dAmr : Θ' ⊢ app R.amrecTm y ∷ El (subTm (single y) cMρ')
      dAmr = R.⊢amrecPt dy

      -- 2. the handle, TYPED, and its call — `⊢transportP` needs BOTH
      --    endpoints of the path typed, and this is the far one.
      dIH : Θ' ⊢ R.ihS-atP ϑa ϑa ϑk ϑp ∷ aIHTat Aρ' cMρ' mρ' μa
      dIH = R.⊢ihS-atP dϑa dϑk dϑa dϑp

      -- ⚠ the Π-peel: `aIHTat` puts the result code under BOTH binders, so
      --   applying it twice leaves `cM[y]` behind one `sub-w` and one
      --   `wk-single`.  Nothing here is content.
      homPeel = cong (λ t → Π (Hom Nat (nsuc μy) t)
                              (El (subTm (extS (single y)) (w cMρ'))))
                     (wk-single {v = y} μa)

      cmPeel : subTm (single q) (subTm (extS (single y)) (w cMρ'))
             ≡ subTm (single y) cMρ'
      cmPeel = trans (cong (subTm (single q)) (sub-w cMρ'))
                     (wk-single {v = q} (subTm (single y) cMρ'))

      dCall : Θ' ⊢ app (app (R.ihS-atP ϑa ϑa ϑk ϑp) y) q
                ∷ El (subTm (single y) cMρ')
      dCall = ⊢-cast (cong El cmPeel)
                     (⊢app (⊢-cast homPeel (⊢app dIH dy)) dq')

      -- 3. THE BRIDGE, at `Θ'` — and turned round.
      bridge : Prv Θ' (Id (El (subTm (single y) cMρ'))
                          (app (app (R.ihS-atP ϑa ϑa ϑk ϑp) y) q)
                          (app R.amrecTm y))
      bridge = R.ihCall-amrec (R.extΘ ext) dϑa dϑk dϑp dy dq'

      pathBack : Prv Θ' (Id (El (subTm (single y) cMρ'))
                            (app R.amrecTm y)
                            (app (app (R.ihS-atP ϑa ϑa ϑk ϑp) y) q))
      pathBack = prvSym dcU dCall dAmr bridge

      -- 4. …and `Θ'`'s handle IS `renTm ϑ` of `Θ`'s.
      handleEq : renTm ϑ (ihS-atP' (renTm ρ stp) (renTm (extR ρ) cM)
                                   (renTm (extR ρ) m) a a k p)
               ≡ R.ihS-atP ϑa ϑa ϑk ϑp
      handleEq =
        trans (ihS-atP-ren {ρ = ϑ} (renTm ρ stp) (renTm (extR ρ) cM)
                           (renTm (extR ρ) m) a a k p)
              (cong₃ (λ sf cf mf → ihS-atP' sf cf mf ϑa ϑa ϑk ϑp)
                     (renren {ϑ = ϑ} {ρ = ρ} {ρ' = ρ'} br stp)
                     (renren {ϑ = extR ϑ} {ρ = extR ρ} {ρ' = extR ρ'}
                             (extcondR {ϑ = ϑ} {ρ = ρ} {ρ' = ρ'} br) cM)
                     (renren {ϑ = extR ϑ} {ρ = extR ρ} {ρ' = extR ρ'}
                             (extcondR {ϑ = ϑ} {ρ = ρ} {ρ' = ρ'} br) m))

  ------------------------------------------------------------------------
  -- ★★★★ THE BOUNDED STATEMENT — what the `natrec` on the measure bound
  --   actually inducts over:
  --
  --     "for every `x : A` with `μ x ≤ n`,  P holds at (x, amrec x)"
  --
  --   It lives at `Δ ▹ Nat`, the bound being that `Nat`.  Inside the two
  --   `Π`s the slots read  [0]=c  [1]=x  [2]=n.
  --
  -- ⚠ `μ x` is `wᶠ m`, NOT a substitution.  `m`'s own slot 0 IS the
  --   `A`-argument, and `wᶠ` inserts the BOUND at slot 1 while leaving that
  --   argument where it is — so the measure lands on `x` with no
  --   substitution at all.
  --
  -- ⚠⚠ THE CERTIFICATE IS `μ x < n`, NOT `μ x ≤ n`, AND THAT IS FORCED.
  --   With `≤`, the ZERO branch has to prove the statement at `μ x ≤ 0` —
  --   which is SATISFIABLE (the measure really can be 0), so it needs an
  --   unfolding there.  The only zero unfolding in the library is
  --   `amrec-unfold-z`, and it is REDUCTION-based: its premise is
  --   `μ x ⟶* nzero`, which a VARIABLE never satisfies.  That is precisely
  --   the wall gap A's equation 4 hit, and there is no `Id`-valued zero
  --   analogue of `amrec-unfold-Id` to escape through.
  --
  --   With `<`, the zero branch is `nsuc (μ x) ≤ 0`, which COMPUTES to
  --   `base` — ex falso, no unfolding needed.  Same trick as
  --   `⊢strong-base`, and the reason the order being a COMPUTING relation
  --   pays off.  The successor branch then reads `nsuc (μ x) ≤ suc k`,
  --   i.e. `μ x ≤ k`, which `⊢le-suc` widens to the `μ x ≤ suc k` that
  --   `amrec-unfold-Id` wants.
  ------------------------------------------------------------------------

  -- ★★ GENERIC IN THE AMBIENT RENAMING, so ONE substitution law serves
  --   every instantiation.  ⭐ Exactly `irrT`'s design — `irrT θ x y n₁ n₂`
  --   carries its own `θ` for the same reason, and `irrT-sub` is then one
  --   lemma instead of one per depth.
  θ₂ : {Γ' : Cx} → Ren ⌊ Δ ⌋ Γ' → Ren ⌊ Δ ⌋ ((Γ' ∙) ∙)
  θ₂ θ v = vs (vs (θ v))

  IndBAt : {Γ' : Cx} (θ : Ren ⌊ Δ ⌋ Γ') (P : RTm ((⌊ Δ ⌋ ∙) ∙))
           (n : RTm Γ') → RTy Γ'
  IndBAt θ P n =
    Π (renTy θ A)
      (Π (Hom Nat (nsuc (renTm (extR θ) m)) (w n))
         (El (PAtR (θ₂ θ) P (var (vs vz))
                (app (renTm (θ₂ θ) amrecTm) (var (vs vz))))))

  -- the bound as `natrec` sees it: ambient `vs`, bound `var vz`
  IndB : RTm ((⌊ Δ ⌋ ∙) ∙) → RTy (⌊ Δ ⌋ ∙)
  IndB P = IndBAt vs P (var vz)

  -- ★ the ambient renaming: `θ₂` at the `natrec` instantiation.
  ρ₃ : Ren ⌊ Δ ⌋ ⌊ ((Δ ▹ Nat) ▹ renTy vs A) ▹ Hom Nat (nsuc (wᶠ m)) (var (vs vz)) ⌋
  ρ₃ = θ₂ vs

  -- ★ the ambient renaming, typed: three weakenings off `Δ`.
  ρ₃⊢ : Ren⊢ Δ (((Δ ▹ Nat) ▹ renTy vs A) ▹ Hom Nat (nsuc (wᶠ m)) (var (vs vz))) ρ₃
  ρ₃⊢ = wR (wR there)

  ------------------------------------------------------------------------
  -- ★★★★★ `IndBAt-sub` — THE SUBSTITUTION LAW, GENERIC IN σ.
  --
  -- ONE lemma for BOTH `natrec` branches: the zero branch instantiates it
  -- at `single nzero`, the successor branch at `nrs`.  Writing them
  -- separately (as first sketched) would have been two bespoke peels with
  -- the same content.
  --
  -- ★ Straight `cong₂` down the structure — `Π`, `Π`, `El` — bottoming out
  --   in `subrenTy`/`subren` for the renamed pieces, `sub-w` for the bound,
  --   and `PAtR-sub` for the motive.  Nothing here is deep; it is the
  --   standing "-sub law per type former" tax, paid once.
  --
  -- ⚠ EVERY implicit σ/ρ/ρ' here IS PINNED — on `subren`, on `extcond`,
  --   and on `cond₂`.  They occur only under an APPLICATION of a meta
  --   (`_σ (_θ v) = σ (θ v)`), which is higher-order unification and Agda
  --   will not decompose it.  The standing rule in this codebase; it costs
  --   exactly one round every time it is forgotten, and it was forgotten
  --   twice here.
  ------------------------------------------------------------------------

  -- the side condition, pushed under the motive's two binders
  cond₂ : {Γ' Γ'' : Cx} {σ : Sub Γ' Γ''} {θ : Ren ⌊ Δ ⌋ Γ'} {θ' : Ren ⌊ Δ ⌋ Γ''} →
          (∀ v → σ (θ v) ≡ var (θ' v)) →
          (∀ v → extS (extS σ) (θ₂ θ v) ≡ var (θ₂ θ' v))
  cond₂ h v = cong (λ t → renTm vs (renTm vs t)) (h v)

  IndBAt-sub : {Γ' Γ'' : Cx} {σ : Sub Γ' Γ''}
               (θ : Ren ⌊ Δ ⌋ Γ') (θ' : Ren ⌊ Δ ⌋ Γ'') →
               (h : ∀ v → σ (θ v) ≡ var (θ' v)) →
               (P : RTm ((⌊ Δ ⌋ ∙) ∙)) (n : RTm Γ') →
               subTy σ (IndBAt θ P n) ≡ IndBAt θ' P (subTm σ n)
  IndBAt-sub {σ = σ} θ θ' h P n =
    cong₂ Π (subrenTy h A)
      (cong₂ Π (cong₂ (λ u v → Hom Nat (nsuc u) v)
                      (subren {σ = extS σ} {ρ = extR θ} {ρ' = extR θ'}
                              (extcond {σ = σ} {ρ = θ} {ρ' = θ'} h) m)
                      (sub-w n))
               (cong El
                  (trans (PAtR-sub (θ₂ θ) (θ₂ θ')
                                   (cond₂ {σ = σ} {θ = θ} {θ' = θ'} h) P
                                   (var (vs vz))
                                   (app (renTm (θ₂ θ) amrecTm) (var (vs vz))))
                         (cong (λ t → PAtR (θ₂ θ') P (var (vs vz))
                                            (app t (var (vs vz))))
                               (subren {σ = extS (extS σ)} {ρ = θ₂ θ} {ρ' = θ₂ θ'}
                                       (cond₂ {σ = σ} {θ = θ} {θ' = θ'} h)
                                       amrecTm)))))

  ------------------------------------------------------------------------
  -- ★★★ …AND ITS RENAMING LAW, FOR FREE.  A renaming IS a substitution
  --   (`ren-subTy'`), so `IndBAt-sub` covers this too — no second
  --   induction, no `-ren` twin.  ⭐ The dividend of stating `IndBAt-sub`
  --   generically in σ rather than per branch.
  ------------------------------------------------------------------------

  IndBAt-ren : {Γ' Γ'' : Cx} {ϑ : Ren Γ' Γ''}
               (θ : Ren ⌊ Δ ⌋ Γ') (θ' : Ren ⌊ Δ ⌋ Γ'') →
               (∀ v → ϑ (θ v) ≡ θ' v) →
               (P : RTm ((⌊ Δ ⌋ ∙) ∙)) (n : RTm Γ') →
               renTy ϑ (IndBAt θ P n) ≡ IndBAt θ' P (renTm ϑ n)
  IndBAt-ren {ϑ = ϑ} θ θ' h P n =
    trans (ren-subTy' (IndBAt θ P n))
      (trans (IndBAt-sub {σ = λ x → var (ϑ x)} θ θ' (λ v → cong var (h v)) P n)
             (cong (IndBAt θ' P) (sym (ren-sub n))))

  ------------------------------------------------------------------------
  -- ★★★★★ THE `natrec`'s IH, READ AS `IHAt` — the OBJECT-level term
  --   becomes the META-level hypothesis step 6 consumes.
  --
  -- ★ This is the other half of the seam step 6 sits on.  `⊢natrec` hands
  --   the successor branch a VARIABLE of type `IndBAt ρ P k`; `ihToPW`
  --   wants an Agda function.  Bridging them is: rename the variable along
  --   the ambient renaming (`IndBAt-ren`), then APPLY it — to the carrier
  --   and to the certificate.  Nothing else.
  --
  -- ⚠ THE PEEL IS `PAtR-sub` TWICE, AT THE TWO Π-BINDERS, and both side
  --   conditions are `refl`: `extS (single y)` and `single c` both meet the
  --   ambient tower `θ₂ ρ'` at a VARIABLE.  ⭐ Same observation the
  --   pointwise calculus is built on — a substitution that meets a
  --   renaming is another renaming.
  ------------------------------------------------------------------------

  ihFromTm : {Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋}
             {P : RTm ((⌊ Δ ⌋ ∙) ∙)} {k ihv : RTm ⌊ Θ ⌋} →
             Θ ⊢ ihv ∷ IndBAt ρ P k →
             IHAt ρ P k
  ihFromTm {ρ = ρ} {P = P} {k = k} {ihv = ihv} dih
           {Θ' = Θ'} {ϑ = ϑ} {ρ' = ρ'} ϑ⊢ br y c dy dc =
    prv _ (⊢-cast (cong El peel)
                  (⊢app (⊢-cast homPeel (⊢app dih' dy)) dc))
    where
      dih' : Θ' ⊢ renTm ϑ ihv ∷ IndBAt ρ' P (renTm ϑ k)
      dih' = ⊢-cast (IndBAt-ren ρ ρ' br P k) (ren-lemma dih ϑ⊢)

      -- the ambient renaming ONE binder up — where the two peels meet
      wρ' : Ren ⌊ Δ ⌋ (⌊ Θ' ⌋ ∙)
      wρ' v = vs (ρ' v)

      br₁ : ∀ v → extS (single y) (θ₂ ρ' v) ≡ var (wρ' v)
      br₁ v = refl

      br₂ : ∀ v → single c (wρ' v) ≡ var (ρ' v)
      br₂ v = refl

      VZ = app (renTm (θ₂ ρ') amrecTm) (var (vs vz))

      homPeel = cong (λ t → Π (Hom Nat (nsuc (subTm (single y)
                                                    (renTm (extR ρ') m))) t)
                              (El (subTm (extS (single y))
                                    (PAtR (θ₂ ρ') P (var (vs vz)) VZ))))
                     (wk-single {v = y} (renTm ϑ k))

      amrecPeel : subTm (single c)
                    (subTm (extS (single y)) (renTm (θ₂ ρ') amrecTm))
                ≡ renTm ρ' amrecTm
      amrecPeel =
        trans (cong (subTm (single c))
                    (subren {σ = extS (single y)} {ρ = θ₂ ρ'} {ρ' = wρ'}
                            br₁ amrecTm))
              (subren {σ = single c} {ρ = wρ'} {ρ' = ρ'} br₂ amrecTm)

      peel : subTm (single c)
               (subTm (extS (single y)) (PAtR (θ₂ ρ') P (var (vs vz)) VZ))
           ≡ PAtR ρ' P y (app (renTm ρ' amrecTm) y)
      peel =
        trans (cong (subTm (single c))
                    (PAtR-sub {σ = extS (single y)} (θ₂ ρ') wρ' br₁ P
                              (var (vs vz)) VZ))
          (trans (PAtR-sub {σ = single c} wρ' ρ' br₂ P
                           (subTm (extS (single y)) (var (vs vz)))
                           (subTm (extS (single y)) VZ))
                 (cong₂ (λ u v → PAtR ρ' P u (app v u))
                        (wk-single {v = c} y)
                        amrecPeel))

  ------------------------------------------------------------------------
  -- ★★★★★ THE ZERO BRANCH — EX FALSO, exactly as the shifted certificate
  --   promised.  At `n := 0` the hypothesis is `nsuc (μ x) ≤ 0`, the order
  --   COMPUTES to `base`, and `⊢strong-base` discharges it.  No unfolding,
  --   no reduction premise on the measure.
  --
  -- ⚠ `subTy (single nzero)` lands the ambient renaming at the IDENTITY,
  --   so `IndBAt-sub` is instantiated at `θ' := idR` and the `renTy idR A`
  --   that comes back needs `renTy-idR`.  That is bookkeeping, not content.
  ------------------------------------------------------------------------

  -- ⚠ `idR` is NOT defined here — `AmTΠ` already exports it, and defining
  --   a second one makes every use ambiguous.  Same lesson as `mId`.

  zbrTm : RTm ((⌊ Δ ⌋ ∙) ∙) → RTm ⌊ Δ ⌋
  zbrTm P = lam (lam (absurd (PAtR (θ₂ idR) P (var (vs vz))
                                (app (renTm (θ₂ idR) amrecTm) (var (vs vz))))
                             (var vz)))

  ⊢zbr : {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
         ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
         Δ ⊢ zbrTm P ∷ subTy (single nzero) (IndB P)
  ⊢zbr {P = P} dP =
    ⊢-cast (sym (IndBAt-sub {σ = single nzero} vs idR (λ v → refl) P (var vz)))
      (⊢lam dA'
        (⊢lam (ty-Hom ty-Nat (⊢nsuc dμ) ⊢nzero)
              (⊢strong-base (⊢PAtR ρ₂⊢ dP dy (⊢app (ren-lemma ⊢amrecΠ ρ₂⊢) dy))
                            (⊢var here))))
    where
      -- ⚠ `⊢-cast` moves a TERM judgement's type; this is a `⊢ty`
      --   judgement, so it needs `subst`.  Standing distinction in this
      --   codebase, and easy to reach for the wrong one.
      dA' : Δ ⊢ty renTy idR A
      dA' = subst (λ T → Δ ⊢ty T) (sym (renTy-idR (λ v → refl) A)) dA

      dμ : (Δ ▹ renTy idR A) ⊢ renTm (extR idR) m ∷ Nat
      dμ = ren-lemma dm (Ren⊢-ext Ren⊢-id)

      ρ₂⊢ : Ren⊢ Δ ((Δ ▹ renTy idR A)
                      ▹ Hom Nat (nsuc (renTm (extR idR) m)) (w nzero))
                  (θ₂ idR)
      ρ₂⊢ = wR (wR Ren⊢-id)

      dyEq : renTy vs (renTy vs (renTy idR A)) ≡ renTy (θ₂ idR) A
      dyEq = trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A)

      dy = ⊢-cast dyEq (⊢var (there here))

  ⊢IndB : {P : RTm ((⌊ Δ ⌋ ∙) ∙)} →
          ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
          (Δ ▹ Nat) ⊢ty IndB P
  ⊢IndB dP =
    ty-Π (ren-ty dA there)
      (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢wkᶠ dm)) (⊢var (there here)))
         (ty-El (⊢PAtR ρ₃⊢ dP dy (⊢app (ren-lemma ⊢amrecΠ ρ₃⊢) dy))))
    where
      -- ⚠ THE VARIABLE'S TYPE IS THE COMPOSITE, NOT THE CONTEXT'S.
      --   `⊢var (there here)` yields `renTy vs (renTy vs (renTy vs A))`,
      --   while `⊢PAtR` and `⊢app` both want `renTy ρ₃ A`.  Equal only up
      --   to `renTy-renTy`, twice — the same fusion `wR` does internally
      --   with `∋-cast`.
      dyEq : renTy vs (renTy vs (renTy vs A)) ≡ renTy ρ₃ A
      dyEq = trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A)

      dy = ⊢-cast dyEq (⊢var (there here))


  ------------------------------------------------------------------------
  -- ★★★★★★ THE SUCCESSOR BRANCH.
  --
  -- ★ THE SHAPE, and every ingredient is now on the shelf:
  --     1. `IndBAt-sub` at `σ := nrs`   the peel — the SAME law the zero
  --                                    branch used at `single nzero`
  --     2. `Hom-Nat-ss`                the hypothesis `nsuc (μ x) ≤ suc K`
  --                                    COMPUTES to `μ x ≤ K`
  --     3. `⊢le-suc`                   …widened to the `μ x ≤ suc K` the
  --                                    handle carries
  --     4. `ihFromTm` + `ihToPW`       the `natrec`'s IH, as `IndPW`
  --     5. the client's `IndStep`      `P` at the STEP's result
  --     6. `amrec-unfold-Id` + `prvSym` + `⊢transportP`
  --                                    …carried back to `amrec x`
  --
  -- ⭐ NOTE WHAT DID **NOT** HAPPEN: no bespoke peel, no second
  --   substitution law, no `nv-s`/`na-s` twin.  `IndBAt-sub` generic in σ
  --   serves both branches, exactly as 2026-08-21 predicted.
  --
  -- ⚠ THE ORDER COMPUTING IS LOAD-BEARING TWICE OVER.  The zero branch is
  --   ex falso because `Hom Nat (nsuc k) nzero ⟶ᵀ base`; this branch reads
  --   its hypothesis as `μ x ≤ K` because `Hom Nat (nsuc a) (nsuc b) ⟶ᵀ
  --   Hom Nat a b`.  Neither is a lemma.  That is the whole argument for
  --   the `<`-shifted certificate.
  ------------------------------------------------------------------------

  sbr : StepExt Δ A cM m stp →
        {P : RTm ((⌊ Δ ⌋ ∙) ∙)} → ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
        IndStep Δ A cM m stp P →
        Prv ((Δ ▹ Nat) ▹ IndB P) (subTy nrs (IndB P))
  sbr ext {P = P} dP istep =
    prv _ (⊢-cast (sym goalTy)
            (⊢lam (ren-ty dA ρ₂⊢)
              (⊢lam (ty-Hom ty-Nat (⊢nsuc dm₃) (⊢nsuc dK₃)) bodyGoal)))
    where
      -- the three contexts the branch lives in, as renamings off `Δ`
      ρ₂ : Ren ⌊ Δ ⌋ ⌊ (Δ ▹ Nat) ▹ IndB P ⌋
      ρ₂ v = vs (vs v)

      ρ₂⊢ : Ren⊢ Δ ((Δ ▹ Nat) ▹ IndB P) ρ₂
      ρ₂⊢ = wR there

      ρ₃ᵇ : Ren ⌊ Δ ⌋ ((⌊ Δ ⌋ ∙ ∙) ∙)
      ρ₃ᵇ v = vs (ρ₂ v)

      -- the bound the branch is proving AT: `suc K`, with `K` the
      -- `natrec`'s predecessor variable.
      NN : RTm ⌊ (Δ ▹ Nat) ▹ IndB P ⌋
      NN = nsuc (var (vs vz))

      -- ★ THE PEEL — `IndBAt-sub` at `σ := nrs`, and nothing else.
      goalTy : subTy nrs (IndB P) ≡ IndBAt ρ₂ P NN
      goalTy = IndBAt-sub {σ = nrs} vs ρ₂ (λ v → refl) P (var vz)

      dm₃ = ren-lemma dm (Ren⊢-ext ρ₂⊢)
      dK₃ = ⊢var (there (there here))

  -- ⚠ from here on everything lives at `Γ₄`, the branch's own context:
  --     [0] = the certificate  [1] = the carrier  [2] = the IH  [3] = K
      Γ₄ : Ctx
      Γ₄ = (((Δ ▹ Nat) ▹ IndB P) ▹ renTy ρ₂ A)
             ▹ Hom Nat (nsuc (renTm (extR ρ₂) m)) (w NN)

      ρ₄ : Ren ⌊ Δ ⌋ ⌊ Γ₄ ⌋
      ρ₄ = θ₂ ρ₂

      ρ₄⊢ : Ren⊢ Δ Γ₄ ρ₄
      ρ₄⊢ = wR (wR ρ₂⊢)

      module R₄ = Handle-at A cM m stp dA dcM dm dstp ρ₄⊢

      Aρ  = renTy ρ₄ A
      cMρ = renTm (extR ρ₄) cM
      mρ  = renTm (extR ρ₄) m

      X  = var (vs vz)
      K₄ = var (vs (vs (vs vz)))
      μX = subTm (single X) mρ

      dXeq : renTy vs (renTy vs (renTy ρ₂ A)) ≡ Aρ
      dXeq = trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A)

      dX : Γ₄ ⊢ X ∷ Aρ
      dX = ⊢-cast dXeq (⊢var (there here))

      dK₄ : Γ₄ ⊢ K₄ ∷ Nat
      dK₄ = ⊢var (there (there (there here)))

      dm₄ = ren-lemma dm (Ren⊢-ext ρ₄⊢)
      dcM₄ = ren-lemma dcM (Ren⊢-ext ρ₄⊢)

      dμX : Γ₄ ⊢ μX ∷ Nat
      dμX = ⊢[] dm₄ dX

      dcU : Γ₄ ⊢ subTm (single X) cMρ ∷ U
      dcU = ⊢[] dcM₄ dX

      -- ⚠ THE MEASURE ARRIVES AT THE WRONG SPELLING.  The Π-binder's type
      --   says `renTm vs (renTm (extR ρ₂) m)`; every lemma below wants
      --   `subTm (single X) (renTm (extR ρ₄) m)`.  Both are `m` with slot 0
      --   at `X` and the ambient at `ρ₄` — one `renren`, one `subren`.
      κ : Ren (⌊ Δ ⌋ ∙) ⌊ Γ₄ ⌋
      κ vz     = vs vz
      κ (vs v) = ρ₄ v

      hκ₁ : ∀ v → vs (extR ρ₂ v) ≡ κ v
      hκ₁ vz     = refl
      hκ₁ (vs v) = refl

      hκ₂ : ∀ v → single X (extR ρ₄ v) ≡ var (κ v)
      hκ₂ vz     = refl
      hκ₂ (vs v) = refl

      mBridge : renTm vs (renTm (extR ρ₂) m) ≡ μX
      mBridge =
        trans (renren {ϑ = vs} {ρ = extR ρ₂} {ρ' = κ} hκ₁ m)
              (sym (subren {σ = single X} {ρ = extR ρ₄} {ρ' = κ} hκ₂ m))

      -- 2. the hypothesis, and the ORDER COMPUTING it down one successor
      dcert : Γ₄ ⊢ var vz ∷ Hom Nat (nsuc μX) (nsuc K₄)
      dcert = ⊢-cast (cong (λ t → Hom Nat (nsuc t) (nsuc K₄)) mBridge)
                     (⊢var here)

      dpk : Γ₄ ⊢ var vz ∷ Hom Nat μX K₄
      dpk = ⊢conv dcert (red→≅ᵀ (stepᵀ (Hom-Nat-ss μX K₄) doneᵀ))

      -- 3. …and widened to the bound the handle carries
      pTm : RTm ⌊ Γ₄ ⌋
      pTm = ordtr μX K₄ (nsuc K₄) (var vz) (natrec unit (var vz) K₄)

      dp : Γ₄ ⊢ pTm ∷ Hom Nat μX (nsuc K₄)
      dp = ⊢ordtr dμX dK₄ (⊢nsuc dK₄) dpk (⊢le-suc dK₄)

      -- 4. the `natrec`'s IH — the VARIABLE, read as `IHAt`
      ihvEq : renTy vs (renTy vs (renTy vs (IndB P))) ≡ IndBAt ρ₄ P K₄
      ihvEq =
        trans (cong (λ T → renTy vs (renTy vs T))
                    (IndBAt-ren {ϑ = vs} vs ρ₂ (λ v → refl) P (var vz)))
          (trans (cong (renTy vs)
                       (IndBAt-ren {ϑ = vs} ρ₂ ρ₃ᵇ (λ v → refl) P (var (vs vz))))
                 (IndBAt-ren {ϑ = vs} ρ₃ᵇ ρ₄ (λ v → refl) P (var (vs (vs vz)))))

      dIHv : Γ₄ ⊢ var (vs (vs vz)) ∷ IndBAt ρ₄ P K₄
      dIHv = ⊢-cast ihvEq (⊢var (there (there here)))

      -- 5. the handle, and the client's step premise
      H : RTm ⌊ Γ₄ ⌋
      H = ihS-atP' (renTm ρ₄ stp) cMρ mρ X X K₄ pTm

      dH : Γ₄ ⊢ H ∷ aIHTat Aρ cMρ mρ μX
      dH = R₄.⊢ihS-atP dX dK₄ dX dp

      stepPrv : Prv Γ₄ (El (PAtR ρ₄ P X (app (app (renTm ρ₄ stp) X) H)))
      stepPrv = istep ρ₄⊢ X H dX dH
                      (ihToPW ext dP ρ₄⊢ X K₄ pTm (var vz) dX dK₄ dp dpk
                              -- ⚠ PINNED: `IHAt`/`IndBAt` are DEFINED, so
                              --   Agda unfolds instead of decomposing, and
                              --   `P` lands under two renamings.
                              (ihFromTm {Θ = Γ₄} {ρ = ρ₄} {P = P} {k = K₄}
                                        {ihv = var (vs (vs vz))} dIHv))

      -- 6. …carried back to `amrec X`
      dstp₄ : Γ₄ ⊢ renTm ρ₄ stp ∷ aStepT Aρ cMρ mρ
      dstp₄ = ⊢-cast (aStepT-ren A cM m) (ren-lemma dstp ρ₄⊢)

      fitPeel = cong (λ T → Π T (El (subTm (extS (single X)) (w cMρ))))
                     (aIHT-fit {X = X} Aρ cMρ mρ)

      cmPeel : subTm (single H) (subTm (extS (single X)) (w cMρ))
             ≡ subTm (single X) cMρ
      cmPeel = trans (cong (subTm (single H)) (sub-w cMρ))
                     (wk-single {v = H} (subTm (single X) cMρ))

      dStepRes : Γ₄ ⊢ app (app (renTm ρ₄ stp) X) H ∷ El (subTm (single X) cMρ)
      dStepRes = ⊢-cast (cong El cmPeel)
                        (⊢app (⊢-cast fitPeel (⊢app dstp₄ dX)) dH)

      dAmr : Γ₄ ⊢ app R₄.amrecTm X ∷ El (subTm (single X) cMρ)
      dAmr = R₄.⊢amrecPt dX

      unfold : Prv Γ₄ (Id (El (subTm (single X) cMρ))
                          (app R₄.amrecTm X)
                          (app (app (renTm ρ₄ stp) X) H))
      unfold = R₄.amrec-unfold-Id (R₄.extΘ ext) dX dK₄ dp

      pathFwd : Prv Γ₄ (Id (El (subTm (single X) cMρ))
                           (app (app (renTm ρ₄ stp) X) H)
                           (app R₄.amrecTm X))
      pathFwd = prvSym dcU dAmr dStepRes unfold

      amrEq : renTm ρ₄ amrecTm ≡ R₄.amrecTm
      amrEq = amrecTm-ren {ρ = ρ₄} stp cM m

      bodyGoal : Γ₄ ⊢ jsub (PFam ρ₄ P X) (prvTm pathFwd) (prvTm stepPrv)
                   ∷ El (PAtR ρ₄ P X (app (renTm ρ₄ amrecTm) X))
      bodyGoal =
        ⊢-cast (cong (λ t → El (PAtR ρ₄ P X (app t X))) (sym amrEq))
               (⊢transportP ρ₄⊢ dP dX dStepRes dAmr
                            (prvOk pathFwd) (prvOk stepPrv))

  ------------------------------------------------------------------------
  -- ★★★★★★★ `amrec-ind` — ASSEMBLED, AND INSTANTIATED.
  --
  -- ⚠⚠ THIS IS THE NON-VACUITY CHECK, AND IT IS THE POINT OF THE
  --   DEFINITION.  A combinator whose premise is unsatisfiable typechecks
  --   green and proves nothing — that is exactly how `lexrec` died.  So the
  --   `natrec` is not merely built; it is INSTANTIATED at `n := suc (μ x)`
  --   and APPLIED to `x` and a certificate, and the certificate is
  --   `⊢le-refl` at `suc (μ x)` — an inhabitant that plainly exists.
  --
  -- ⭐ THAT is what makes `IndB P` non-vacuous: `nsuc (μ x) ≤ nsuc (μ x)`
  --   is reflexivity, not an assumption.  The bound is chosen to make the
  --   STRICT certificate `μ x < n` satisfiable at the very `x` being
  --   proved about — which is the whole reason the shift to `<` cost
  --   nothing at the top level while buying the ex-falso zero branch.
  --
  -- ★ AND THE APPLICATION IS `ihFromTm`, REUSED.  Reading the `natrec`'s
  --   result as a meta-level hypothesis and reading the successor branch's
  --   IH variable as one are the SAME operation — so the final application
  --   needs no new peel.
  ------------------------------------------------------------------------

  amrecInd : StepExt Δ A cM m stp →
             {P : RTm ((⌊ Δ ⌋ ∙) ∙)} → ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
             IndStep Δ A cM m stp P →
             {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
             Prv Δ (El (subTm (single x)
                        (subTm (single (app (w amrecTm) (var vz))) P)))
  amrecInd ext {P = P} dP istep {x = x} dx =
    prv-cast (cong El finalEq)
      (ihFromTm {Θ = Δ} {ρ = idR} {P = P} {k = N} {ihv = ntTm} dnat'
                {Θ' = Δ} {ϑ = idR} {ρ' = idR} Ren⊢-id (λ v → refl)
                x (reflTm N) dx' dcert)
    where
      μx = subTm (single x) m
      dμx = ⊢[] dm dx

      -- ★★ THE BOUND: one above the measure of the very carrier in hand.
      N = nsuc μx
      dN = ⊢nsuc dμx

      sb = sbr ext dP istep

      ntTm = natrec (zbrTm P) (prvTm sb) N

      dnat : Δ ⊢ ntTm ∷ subTy (single N) (IndB P)
      dnat = ⊢natrec (⊢IndB dP) (⊢zbr dP) (prvOk sb) dN

      -- the same peel the zero branch used, at `single N` instead of
      -- `single nzero` — `IndBAt-sub` generic in σ, a third time.
      dnat' : Δ ⊢ ntTm ∷ IndBAt idR P N
      dnat' = ⊢-cast (IndBAt-sub {σ = single N} vs idR (λ v → refl) P (var vz))
                     dnat

      dx' : Δ ⊢ x ∷ renTy idR A
      dx' = ⊢-cast (sym Aid) dx

      -- ★ THE CERTIFICATE, AND IT IS REFLEXIVITY.
      dcert : Δ ⊢ reflTm N
                ∷ Hom Nat (nsuc (subTm (single x) (renTm (extR idR) m)))
                          (renTm idR N)
      dcert = ⊢-cast (cong₂ (λ u v → Hom Nat (nsuc (subTm (single x) u)) v)
                            (sym mId)
                            (sym (renTm-idR (λ v → refl) N)))
                     (⊢le-refl dN)

      -- ⚠ …and the last peel: `PAtR` at the IDENTITY ambient renaming IS
      --   the statement's own `IndAt`.  The two differ only in WHICH slot
      --   is filled first — `IndAt` puts the recursive value in as a
      --   FUNCTION of the carrier variable (`valAt`), `PAtR` puts it in
      --   already applied.  Three cases, and the `vz` one is `wk-single`.
      extR²id : ∀ v → extR (extR idR) v ≡ v
      extR²id = extR-id (extR-id (λ v → refl))

      VX = app amrecTm x

      bridge : ∀ v → _
      bridge vz          = cong (λ t → app t x)
                                (sym (wk-single {v = x} amrecTm))
      bridge (vs vz)     = wk-single {v = VX} x
      bridge (vs (vs v)) = refl

      finalEq : PAtR idR P x (app (renTm idR amrecTm) x)
              ≡ subTm (single x)
                  (subTm (single (app (w amrecTm) (var vz))) P)
      finalEq =
        trans (cong (λ Q → subTm (single (app (renTm idR amrecTm) x))
                             (subTm (extS (single x)) Q))
                    (renTm-idR extR²id P))
          (trans (cong (λ t → subTm (single (app t x))
                                (subTm (extS (single x)) P))
                       (renTm-idR (λ v → refl) amrecTm))
            (trans (subTm-subTm P)
                   (trans (subTm-cong bridge P) (sym (subTm-subTm P)))))

  ------------------------------------------------------------------------
  -- ✅ THE ZERO BRANCH IS PROVED — `⊢zbr`, above.  (This block is kept for
  -- the REASONING; the blocker it describes was dissolved, not worked around.)
  --
  -- ★ THE PROOF ITSELF IS SETTLED, and it is three lines:
  --
  --     ⊢lam dA (⊢lam <the Hom is a type> (⊢strong-base <P as a code> (⊢var here)))
  --
  --   At `n := 0` the hypothesis is `nsuc (μ x) ≤ 0`, the ORDER COMPUTES
  --   (`Hom Nat (nsuc k) nzero ⟶ᵀ base`), and `⊢strong-base` discharges it.
  --   No `amrec` unfolding, no reduction premise on the measure — which is
  --   exactly why the certificate was shifted to `μ x < n`.
  --
  -- ⚠ WHAT BLOCKS IT IS BOOKKEEPING, NOT CONTENT: `subTy (single nzero)`
  --   COLLAPSES A SLOT.  `IndB`'s body sits under THREE binders (n, x, c);
  --   after the bound is substituted away it sits under TWO.  So the branch
  --   needs its own renaming `ρ₂ = vs ∘ vs`, and a FUSION lemma relating
  --
  --       subTm (extS (extS (single nzero))) (renTm (extR (extR ρ₃)) P)
  --     ≡ renTm (extR (extR ρ₂)) P
  --
  --   ⇒ this is exactly the `nv-z` / `na-z` shape in `…LibNatrec`, which
  --     exists for `natrec`'s ordinary motive but not for `IndB`.  The
  --     successor branch will need the `nv-s` twin.  Both are `subren`
  --     fusions and neither is deep — but they are the next real work, and
  --     writing the branch before them just fights the peel.
  --
  -- ⇒ RESOLVED, and better than planned: `IndB-z`/`IndB-s` were never
  --   written.  `IndBAt-sub` is GENERIC IN σ, so the zero branch is its
  --   instance at `σ := single nzero` and the successor branch will be its
  --   instance at `σ := single (nsuc …)`.  ONE law, not two bespoke peels.
  --   ⇒ NEXT is the SUCCESSOR branch and step 6 (`IHAt`), not more peels.
  ------------------------------------------------------------------------

module Concl (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
             (dA   : Δ ⊢ty A)
             (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
             (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
             (dstp : Δ ⊢ stp ∷ aStepT A cM m)
             where

  open Stmt Δ A cM m stp dA dcM dm dstp using ( IndAt )

  AmrecInd : RTm ((⌊ Δ ⌋ ∙) ∙) → Set
  AmrecInd P =
    ((Δ ▹ A) ▹ El cM) ⊢ P ∷ U →
    IndStep Δ A cM m stp P →
    {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
    Prv Δ (IndAt P x)

  ------------------------------------------------------------------------
  -- ✅✅✅ …AND IT IS INHABITED.  The `Set` above was written 2026-08-19 as
  -- a SPECIFICATION, with the explicit note that "no instance exists, so
  -- nothing below is yet evidence".  It exists now.
  --
  -- ⚠ THE SIDE CONDITION IS REAL AND IS NOT FREE: `StepExt` — the step
  --   respects pointwise equality of handles — is the same premise gcd had
  --   to discharge (`gcdStepExt`).  A client of `amrec-ind` owes `StepExt`
  --   and `IndStep`, and nothing else.
  ------------------------------------------------------------------------

  amrecInd : StepExt Δ A cM m stp →
             {P : RTm ((⌊ Δ ⌋ ∙) ∙)} → AmrecInd P
  amrecInd = Typing.amrecInd Δ A cM m stp dA dcM dm dstp
