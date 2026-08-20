------------------------------------------------------------------------
-- OCP-0009 — `amrec-ind`, ATTEMPT 1: STATE IT BEFORE PROVING IT.
--
-- ★ WHY THIS ORDER.  Gap A's expensive failures came from committing to a
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
module poc.OCP0009.NbEPDirDBSpikeAmrecInd where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; RTm; El; U; Nat; Hom; Π; var; vz; vs; Var; app; nsuc; nzero; natrec
        ; lam; absurd; jsub; Id
        ; subTm; subTy; renTy; renTm; Ren; extR; extS; renTy-renTy; Sub
        ; subTm-subTm; subTm-renTm; subTm-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢app; ⊢nsuc; ⊢lam; ⊢nzero; nrs; ⊢jsub
        ; ty-El; ty-Π; ty-Hom; ty-Nat )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ⊢[]; Ren⊢; Ren⊢-ext; ren-lemma; ren-ty
        ; Sub⊢; Sub⊢-ext; ⊢single; sub-lemma )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; wᶠ; wᶠ¹-single; ⊢wkᶠ; sub-w; cong₃ )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( aStepT; Prv; prv; prvOk; prvTm; StepExt; idOfRed; prv-cast; wR
        ; subren; subrenTy; extcond; renTy-idR; renTm-idR; module AmTΠ )
open import poc.OCP0009.NbEPDirDBLibOrd using ( ⊢strong-base )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibNatrec using ( Ren⊢-id )

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

module Typing (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
              (dA   : Δ ⊢ty A)
              (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
              (dm   : (Δ ▹ A) ⊢ m ∷ Nat)
              (dstp : Δ ⊢ stp ∷ aStepT A cM m)
              where

  open AmTΠ Δ A cM m stp dA dcM dm dstp
    using ( amrecTm; ⊢amrecΠ; idR; auxAt; auxAt-id; auxIH; ihS-atP; ih-app
          ; amrec-β; irrT; irrT-sub; irrElim; irr-ind; descS-at; ⊢descS-at
          ; mId; extR-id )

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
  -- ★★★★★ THE BRIDGE — THE IH HANDLE'S CALLS **ARE** `amrec`.
  --
  -- Step 6 needs `P` of every call the handle makes.  Those calls are NOT
  -- syntactically `amrec y`: `ih-app` reduces them to the AUXILIARY at the
  -- bound `k`, while `amrec-β` reduces `amrec y` to the auxiliary at ITS
  -- OWN bound `μ y`.  Different bounds, different certificates.
  --
  -- ★ `irrElim` equates exactly those two — that is what certificate
  --   irrelevance IS — so the bridge is `ih-app` on the left, `amrec-β` on
  --   the right, and irrelevance in the middle.
  --
  -- ⚠ NO PACKAGED VERSION EXISTED.  `…GcdRec`'s `s2` builds this inline for
  --   gcd.  It belongs in the library: EVERY inductive proof over `amrec`
  --   needs it, and rebuilding it per client is the amortisation failure
  --   this whole exercise is about.
  ------------------------------------------------------------------------

  ihCall-amrec : StepExt Δ A cM m stp →
                 {x k p : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A → Δ ⊢ k ∷ Nat →
                 Δ ⊢ p ∷ Hom Nat (subTm (single x) m) (nsuc k) →
                 {y q : RTm ⌊ Δ ⌋} → Δ ⊢ y ∷ A →
                 Δ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) m))
                                 (subTm (single x) m) →
                 Prv Δ (Id (El (subTm (single y) cM))
                           (app (app (ihS-atP x x k p) y) q)
                           (app amrecTm y))
  ihCall-amrec ext {x = x} {k = k} {p = p} dx dk dp {y = y} {q = q} dy dq =
    idOfRed (ih-app x x k p y q) (amrec-β y)
            (prv-cast idEq
              (irrElim dAt y (descS-at x x k p y q) (reflTm μy) dy' dc₁ dc₂))
    where
      μx = subTm (single x) m
      μy = subTm (single y) m
      dμx = ⊢[] dm dx
      dμy = ⊢[] dm dy

      -- the irrelevance witness at the two bounds `k` and `μ y`
      dAt : Δ ⊢ app (prvTm (irr-ind ext dx dy dk)) μy ∷ irrT idR x y k μy
      dAt = ⊢-cast (trans (irrT-sub vs idR (λ v → refl) x y (w k) (var vz))
                          (cong (λ u → irrT idR x y u μy) (wk-single {v = μy} k)))
                   (⊢app (prvOk (irr-ind ext dx dy dk)) dμy)

      dy' = ⊢-cast (sym (renTy-idR (λ v → refl) A)) dy

      -- ⚠ both certificates need `mId` — the measure's identity renaming
      --   does not vanish at an abstract `m`.
      dc₁ = ⊢-cast (cong (λ z → Hom Nat (subTm (single y) z) k) (sym mId))
                   (⊢descS-at dμy dμx dk dq dp)
      dc₂ = ⊢-cast (cong (λ z → Hom Nat (subTm (single y) z) μy) (sym mId))
                   (⊢le-refl dμy)

      idEq = cong₃ (λ c e₁ e₂ → Id (El c) e₁ e₂)
                   (cong (subTm (single y))
                         (renTm-idR (extR-id (λ v → refl)) cM))
                   (cong (λ z → app (app z y) (descS-at x x k p y q))
                         (auxAt-id x k))
                   (cong (λ z → app (app z y) (reflTm μy)) (auxAt-id y μy))


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
  -- ⚠⚠⚠ THE ZERO BRANCH — DRAFTED, AND BLOCKED ON A PEEL.  NOT PROVED.
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
  -- ⇒ NEXT: `IndB-z` and `IndB-s`, then the two branches, then `⊢natrec`.
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
