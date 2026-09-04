------------------------------------------------------------------------
-- OCP-0009 — THE `natrec` RE-TYPING LIBRARY.
--
-- ★ WHY THIS MODULE EXISTS.  These lemmas were written inside gcd EXAMPLE
--   modules but are entirely general, and both carried headers saying so:
--   `…GcdCert` says of `na-z`/`na-s` "GENERAL — nothing gcd-specific here;
--   it belongs beside `⊢natrec-var` in the WF library", and of `Sub⊢-∘`
--   "Also general, also missing from `…Subj`".  Living in an example made
--   them invisible: BOTH were rediscovered the hard way while typing
--   equation 4, after starting to rebuild them from scratch.
--
-- ★★ WHAT IS HERE.  Three ways to type a `natrec` whose motive or branches
--    have moved, plus the composition its `Sub⊢`s need:
--
--      ⊢natrec-var  — at a VARIABLE scrutinee (branches weakened)
--      ⊢natrec-at   — at an ARBITRARY scrutinee, branches under a
--                     substitution; bundles the `na-z`/`na-s` casts
--      na-z / na-s  — the two casts themselves, if a caller needs them raw
--      Sub⊢-∘       — typed substitutions compose (needed when the
--                     scrutinees live several slots deep, so their `Sub⊢`s
--                     are composites)
--
-- ⚠ `subTm` DOES NOT INVERT, so none of these can be recovered from a
--   derivation of the whole term — that is why they must exist separately.
--   See `…GcdStep`'s note at `⊢gcdInn2`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Natrec where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTy; RTm; Nat; natrec; var; vz; vs; nzero
        ; Ren; Sub; renTy; renTm; subTy; subTm; extR; extS; _∘ₛ_
        ; subTy-renTy; renTy-subTy; subTy-cong; subTy-subTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs; _⊢_∷_; _⊢ty_; ⊢natrec; ⊢var; here; wk-single; nzero; subTy )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢-cast; ⊢wk; ren-ty; ren-lemma; Ren⊢-ext
        ; Sub⊢; Sub⊢-ext; sub-ty; sub-lemma; Ren⊢; ∋-cast )
open import DirectedHoTT.Lib.Wk using ( w; cong₃; sub-w )
open import DirectedHoTT.Lib.Amrec using ( wR; subren; renren; subrenTy; renTy-idR; rensub; Prv; prv; prvOk )

-- ★ the identity typed renaming — also general, also from an example
Ren⊢-id : {Γ : Ctx} → Ren⊢ Γ Γ (λ v → v)
Ren⊢-id {A = A} v = ∋-cast (sym (renTy-idR (λ _ → refl) A)) v

------------------------------------------------------------------------
-- ★ AT A VARIABLE SCRUTINEE.  Each `natrec` split has to re-type its own
--   `natrec`; this takes exactly the motive and the two branches.
------------------------------------------------------------------------

module _ {Γ : Ctx} {M : RTy (⌊ Γ ⌋ ∙)} where

  -- the motive, at the new variable — collapses to `M` itself
  nv-at : subTy (single (var vz)) (renTy (extR vs) M) ≡ M
  nv-at = trans (subrenTy br M) (renTy-idR (λ _ → refl) M)
    where
      br : ∀ v → single (var vz) (extR vs v) ≡ var v
      br vz     = refl
      br (vs u) = refl

  -- the zero branch: `subTy` past the weakening
  nv-z : subTy (single nzero) (renTy (extR vs) M)
       ≡ renTy vs (subTy (single nzero) M)
  nv-z = trans (subTy-renTy M) (trans (subTy-cong br M) (sym (renTy-subTy M)))
    where
      br : ∀ v → single nzero (extR vs v) ≡ renTm vs (single nzero v)
      br vz     = refl
      br (vs u) = refl

  -- the successor branch: same commutation, one binder deeper
  nv-s : subTy nrs (renTy (extR vs) M)
       ≡ renTy (extR (extR vs)) (subTy nrs M)
  nv-s = trans (subTy-renTy M) (trans (subTy-cong br M) (sym (renTy-subTy M)))
    where
      br : ∀ v → nrs (extR vs v) ≡ renTm (extR (extR vs)) (nrs v)
      br vz     = refl
      br (vs u) = refl

------------------------------------------------------------------------
-- ★★ THE SAME, WITH THE NEW SLOT'S TYPE FREE.
--
-- ⚠ WHY THIS IS NEEDED, and it was not obvious.  `nv-at`/`nv-z`/`nv-s` are
--   already generic in the slot — they speak only about `renTy (extR vs)`,
--   which does not care WHAT was pushed on.  Only the CONCLUSION of
--   `⊢natrec-var` hardcodes `Nat`.
--
-- ★ AND `⊢congAt` IS EXACTLY THE CLIENT.  Its family is typed in
--   `Γ ▹ El ⌜Nat⌝`, because `⊢jsub`'s family lives over the IDENTITY's type
--   and `IdN` is `Id (El ⌜Nat⌝) _ _`.  With `Nat` baked in, gcd's one-hole
--   context could not be handed to it at all.
--
-- ⇒ the scrutinee's derivation becomes a PARAMETER, which is also what lets
--   the caller insert the `El ⌜Nat⌝ → Nat` conversion.
------------------------------------------------------------------------

⊢natrec-var-at :
  {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {M : RTy (⌊ Γ ⌋ ∙)}
  {z : RTm ⌊ Γ ⌋} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} →
  (Γ ▹ A) ⊢ var vz ∷ Nat →
  (Γ ▹ Nat) ⊢ty M →
  Γ ⊢ z ∷ subTy (single nzero) M →
  ((Γ ▹ Nat) ▹ M) ⊢ s ∷ subTy nrs M →
  (Γ ▹ A) ⊢ natrec (w z) (renTm (extR (extR vs)) s) (var vz) ∷ M
⊢natrec-var-at {M = M} dn dM dz ds =
  ⊢-cast nv-at
    (⊢natrec (ren-ty dM (Ren⊢-ext wR-id))
             (⊢-cast (sym nv-z) (⊢wk dz))
             (⊢-cast (sym nv-s) (ren-lemma ds (Ren⊢-ext (Ren⊢-ext wR-id))))
             dn)
  where wR-id = wR Ren⊢-id

⊢natrec-var :
  {Γ : Ctx} {M : RTy (⌊ Γ ⌋ ∙)} {z : RTm ⌊ Γ ⌋} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} →
  (Γ ▹ Nat) ⊢ty M →
  Γ ⊢ z ∷ subTy (single nzero) M →
  ((Γ ▹ Nat) ▹ M) ⊢ s ∷ subTy nrs M →
  (Γ ▹ Nat) ⊢ natrec (w z) (renTm (extR (extR vs)) s) (var vz) ∷ M
⊢natrec-var = ⊢natrec-var-at (⊢var here)


------------------------------------------------------------------------
-- ★ AT AN ARBITRARY SCRUTINEE, under a substitution of the ambient
--   context — what a reduction's intermediate scrutinees need.
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
-- ★★★ AT A VARIABLE SCRUTINEE, *UNDER A SUBSTITUTION* — and ITERABLE.
--
-- ★ WHY THIS BELONGS HERE AND NOT AT THE CALL SITE.  A client that pushes a
--   `⊢natrec-var` typing down a substitution stack by hand pays the
--   `na-z`/`na-s` commutations AT ITS OWN CONCRETE TYPES.  For gcd that is
--   a five-fold substituted `G3` — measured OOM twice (2m04s as one term,
--   1m50s split into five `Def`s, in a module that otherwise checks in
--   ~15s).  Proved HERE, the same commutations happen ONCE at an ABSTRACT
--   σ, where they are small.
--
-- ⚠ THIS ONE DOES NOT ITERATE — it CONSUMES the three pieces and yields
--   one derivation.  `⊢natrec-var-tr` below is the iterable form.
--
-- ⚠ This is `⊢natrec-at`'s body with `⊢natrec-var` in place of `⊢natrec` —
--   the two differ only in whether the scrutinee is the hole or arbitrary.
------------------------------------------------------------------------

⊢natrec-var-push :
  {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {M : RTy (⌊ Γ ⌋ ∙)}
  {z : RTm ⌊ Γ ⌋} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} →
  Sub⊢ Γ Δ σ →
  (Γ ▹ Nat) ⊢ty M →
  Γ ⊢ z ∷ subTy (single nzero) M →
  ((Γ ▹ Nat) ▹ M) ⊢ s ∷ subTy nrs M →
  (Δ ▹ Nat) ⊢ natrec (w (subTm σ z))
                     (renTm (extR (extR vs)) (subTm (extS (extS σ)) s))
                     (var vz)
    ∷ subTy (extS σ) M
⊢natrec-var-push σ⊢ dM dz ds =
  ⊢natrec-var (sub-ty dM (Sub⊢-ext σ⊢))
              (⊢-cast (sym na-z) (sub-lemma dz σ⊢))
              (⊢-cast (sym na-s) (sub-lemma ds (Sub⊢-ext (Sub⊢-ext σ⊢))))

------------------------------------------------------------------------
-- ★★★ …AND THE ITERABLE FORM.  Takes a `natrec`-at-a-variable TYPING and
--     transports it along a substitution, so an n-deep stack is n
--     applications.  This is what a client with a deep stack wants;
--     `⊢natrec-var-push` above CONSUMES the three pieces and cannot chain.
--
-- ⚠ The pointwise identity is NOT `refl`.  `vz`/`vs vz` are; the deep case
--   needs renaming FUSION — `renTm (extR² vs) (w (w t)) ≡ w (w (w t))` —
--   which is two `renren`s.  Proved HERE at an abstract σ, where it is
--   small; a client would prove it at its own concrete types.
------------------------------------------------------------------------

-- w² and w³ as single renamings, so `renren` can fuse through them
w²-fuse : {Γ : Cx} (t : RTm Γ) → w (w t) ≡ renTm (λ v → vs (vs v)) t
w²-fuse t = renren {ϑ = vs} {ρ = vs} {ρ' = λ v → vs (vs v)} (λ _ → refl) t

w³-fuse : {Γ : Cx} (t : RTm Γ) →
          w (w (w t)) ≡ renTm (λ v → vs (vs (vs v))) t
w³-fuse t =
  trans (cong w (w²-fuse t))
        (renren {ϑ = vs} {ρ = λ v → vs (vs v)} {ρ' = λ v → vs (vs (vs v))}
                (λ _ → refl) t)

⊢natrec-var-tr :
  {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {M : RTy (⌊ Γ ⌋ ∙)}
  {z : RTm ⌊ Γ ⌋} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} →
  Sub⊢ Γ Δ σ →
  (Γ ▹ Nat) ⊢ natrec (w z) (renTm (extR (extR vs)) s) (var vz) ∷ M →
  (Δ ▹ Nat) ⊢ natrec (w (subTm σ z))
                     (renTm (extR (extR vs)) (subTm (extS (extS σ)) s))
                     (var vz)
    ∷ subTy (extS σ) M
-- ⚠ the `subst` motive must be PINNED — neither the context nor the type
--   is determined by the equation being transported along.
⊢natrec-var-tr {Δ = Δ} {σ = σ} {M = M} {z = z} {s = s} σ⊢ d =
  subst (λ t → (Δ ▹ Nat) ⊢ t ∷ subTy (extS σ) M) tm-eq
        (sub-lemma d (Sub⊢-ext σ⊢))
  where
    br : ∀ v → renTm (extR (extR vs)) (extS (extS σ) v)
             ≡ extS (extS (extS σ)) (extR (extR vs) v)
    br vz          = refl
    br (vs vz)     = refl
    br (vs (vs u)) =
      trans (cong (renTm (extR (extR vs))) (w²-fuse (σ u)))
            (trans (renren {ϑ = extR (extR vs)} {ρ = λ v → vs (vs v)}
                           {ρ' = λ v → vs (vs (vs v))} (λ _ → refl) (σ u))
                   (sym (w³-fuse (σ u))))

    tm-eq : subTm (extS σ) (natrec (w z) (renTm (extR (extR vs)) s) (var vz))
          ≡ natrec (w (subTm σ z))
                   (renTm (extR (extR vs)) (subTm (extS (extS σ)) s))
                   (var vz)
    tm-eq = cong₃ natrec (sub-w z)
              (sym (rensub {σ = extS (extS σ)} {ϑ = extR (extR vs)}
                           {σ' = extS (extS (extS σ))} {ϑ' = extR (extR vs)}
                           br s))
              refl

------------------------------------------------------------------------
-- ★ `natrec` AT THE `Prv` LEVEL.
--
-- ⚠ LIFTED 2026-08-22 from `…Examples/Gcd/IndG.Plumb`, where the shape
--   `prv _ (⊢natrec ⊢M (prvOk z) (prvOk s) n)` occurred THREE times
--   (`split3`, `split2`, `ind`).  It says nothing about gcd and nothing
--   about motives — it is `⊢natrec` with the term existentially packaged.
--
-- ★ AND PACKAGING IS NOT COSMETIC.  Keeping the branch terms inside `Prv`
--   is what stops a large proof term reaching a TYPE; naming one there
--   OOM-killed `Examples/Gcd/MaxSpec` at 220s where the `Prv` form builds
--   in 77s (`PERF.md` §6).
------------------------------------------------------------------------

prvNatrec : {Γ : Ctx} {M : RTy (⌊ Γ ⌋ ∙)} {n : RTm ⌊ Γ ⌋} →
            (Γ ▹ Nat) ⊢ty M →
            Prv Γ (subTy (single nzero) M) →
            Prv ((Γ ▹ Nat) ▹ M) (subTy nrs M) →
            Γ ⊢ n ∷ Nat →
            Prv Γ (subTy (single n) M)
prvNatrec dM z s dn = prv _ (⊢natrec dM (prvOk z) (prvOk s) dn)
