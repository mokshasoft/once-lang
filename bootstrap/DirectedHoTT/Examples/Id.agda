------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, the SYMMETRIC former: subst / rewrite / sym /
-- trans / cong as object-language proofs.  THE ACCEPTANCE TEST for the
-- two-former landing (SPIKE-TWOFORMER.md): this file is written FIRST
-- and the kernel is landed under it until it greens.
--
--   ★ `⊢subst`  — REWRITE, the workhorse: coerce `e : El (d[t])` to
--     `El (d[u])` along `p : Id A t u` — at an UNRESTRICTED family
--     (no variance key: what symmetry buys).
--   ★ `subst-computes` — rewriting along a reflexivity is free: the
--     J-rule fires in one step.
--   ★ `⊢sym`    — DERIVED, not primitive: `jsub` at the family
--     `λy. Id y t`, seeded with reflexivity.
--   ★ `sym-computes` — `sym` at a reflexivity computes back to it.
--   ★ `⊢transId` — DERIVED transitivity: the family `λy. Id a y`.
--   ★ `⊢congId`  — DERIVED congruence: a body's action on an
--     identification is a THEOREM here (the directed axis needed a
--     former, `ap`; the symmetric axis gets it from `jsub` alone).
--   ★ `⊢idtohom` — the REFLECTION welding the axes: every
--     identification yields a hom, with zero new rules.
--
-- `--safe`, zero postulates, zero holes (once green).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Id where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom; Id
        ; RTm; var; lam; app; ⌜base⌝; ⌜Hom⌝; ⌜Id⌝; hrefl; idrefl; jsub
        ; renTm; renTy; subTm; ⌜Id⌝-cong₃; ⌜Hom⌝-cong₃ )
open import DirectedHoTT.Spec.Variance
  using ( occ-ren-tm; avoids-wk )
open import DirectedHoTT.Spec.Typing
  using ( single; _⟶_; _⟶*_; done; step
        ; jsub-refl
        ; _⟶ᵀ_; El-⌜Id⌝; El-⌜Hom⌝
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; here
        ; _⊢_∷_; ⊢var; ⊢⌜base⌝; ⊢⌜Id⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢idrefl; ⊢jsub; ⊢conv )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢wk; wk-cancel-tm; ⊢-cast; ⊢[] )

------------------------------------------------------------------------
-- 1. ★ SUBST / REWRITE — the workhorse, verbatim: `jsub` IS `subst`.
--    The family `d` is an arbitrary code with `vz` free — no variance
--    side-condition, no stability key.
------------------------------------------------------------------------

⊢subst : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {d : RTm (⌊ Γ ⌋ ∙)} {t u p e : RTm ⌊ Γ ⌋} →
         (Γ ▹ A) ⊢ d ∷ U →
         Γ ⊢ t ∷ A → Γ ⊢ u ∷ A →
         Γ ⊢ p ∷ Id A t u →
         Γ ⊢ e ∷ El (subTm (single t) d) →
         Γ ⊢ jsub d p e ∷ El (subTm (single u) d)
⊢subst dd dt du dp de = ⊢jsub dd dt du dp de

-- rewriting along a reflexivity is FREE — one step:
subst-computes : {Γ : Cx} (d : RTm (Γ ∙)) (c s e : RTm Γ) →
                 jsub d (idrefl c s) e ⟶ e
subst-computes d c s e = jsub-refl d c s e

------------------------------------------------------------------------
-- 2. ★ SYM — derived: `jsub` at the family `λy. Id y t`, seeded with
--    reflexivity.  The family's code: `⌜Id⌝ (wk c) (var vz) (wk t)`.
------------------------------------------------------------------------

symTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
symTm c t p = jsub (⌜Id⌝ (renTm vs c) (var vz) (renTm vs t)) p (idrefl c t)

⊢sym : {Γ : Ctx} {c t u p : RTm ⌊ Γ ⌋} →
       Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
       Γ ⊢ p ∷ Id (El c) t u →
       Γ ⊢ symTm c t p ∷ Id (El c) u t
⊢sym {c = c} {t = t} {u = u} {p = p} dc dt du dp =
  ⊢conv
    (⊢-cast (cong El (⌜Id⌝-cong₃ (wk-cancel-tm u c) refl (wk-cancel-tm u t)))
      (⊢jsub (⊢⌜Id⌝ (⊢wk dc) (⊢var here) (⊢wk dt))
             dt du dp
             (⊢-cast (cong El (sym (⌜Id⌝-cong₃ (wk-cancel-tm t c) refl
                                               (wk-cancel-tm t t))))
                     (⊢conv (⊢idrefl dc dt)
                            (csymᵀ (credᵀ (El-⌜Id⌝ c t t)))))))
    (credᵀ (El-⌜Id⌝ c u t))

-- ...and `sym` at a reflexivity computes back to a reflexivity — the
-- J-rule fires on the DERIVED operation in one step:
sym-computes : {Γ : Cx} (c t c₂ s : RTm Γ) →
               symTm c t (idrefl c₂ s) ⟶ idrefl c t
sym-computes c t c₂ s =
  jsub-refl (⌜Id⌝ (renTm vs c) (var vz) (renTm vs t)) c₂ s (idrefl c t)

------------------------------------------------------------------------
-- 3. ★ TRANS — derived: the family `λy. Id a y` (the composition
--    pattern, now symmetric).
------------------------------------------------------------------------

transTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
transTm c a q p = jsub (⌜Id⌝ (renTm vs c) (renTm vs a) (var vz)) q p

⊢transId : {Γ : Ctx} {c a t u p q : RTm ⌊ Γ ⌋} →
           Γ ⊢ c ∷ U → Γ ⊢ a ∷ El c →
           Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
           Γ ⊢ p ∷ Id (El c) a t →
           Γ ⊢ q ∷ Id (El c) t u →
           Γ ⊢ transTm c a q p ∷ Id (El c) a u
⊢transId {c = c} {a = a} {t = t} {u = u} dc da dt du dp dq =
  ⊢conv
    (⊢-cast (cong El (⌜Id⌝-cong₃ (wk-cancel-tm u c) (wk-cancel-tm u a) refl))
      (⊢jsub (⊢⌜Id⌝ (⊢wk dc) (⊢wk da) (⊢var here))
             dt du dq
             (⊢-cast (cong El (sym (⌜Id⌝-cong₃ (wk-cancel-tm t c)
                                               (wk-cancel-tm t a) refl)))
                     (⊢conv dp (csymᵀ (credᵀ (El-⌜Id⌝ c a t)))))))
    (credᵀ (El-⌜Id⌝ c a u))

------------------------------------------------------------------------
-- 4. ★ CONG — derived, a THEOREM: the family `λy. Id cB b[t]ʷ b[y]`,
--    seeded with reflexivity at `b[t]`.  (The directed axis needed a
--    FORMER for this; the symmetric axis gets it from `jsub`.)
------------------------------------------------------------------------

congTm : {Γ : Cx} → RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ → RTm Γ
congTm cB b cA t p =
  jsub (⌜Id⌝ (renTm vs cB)
             (renTm vs (subTm (single t) b))
             b)
       p
       (idrefl cB (subTm (single t) b))

⊢congId : {Γ : Ctx} {cA cB : RTm ⌊ Γ ⌋} {b : RTm (⌊ Γ ⌋ ∙)} {t u p : RTm ⌊ Γ ⌋} →
          Γ ⊢ cA ∷ U → Γ ⊢ cB ∷ U →
          (Γ ▹ El cA) ⊢ b ∷ El (renTm vs cB) →
          Γ ⊢ t ∷ El cA → Γ ⊢ u ∷ El cA →
          Γ ⊢ p ∷ Id (El cA) t u →
          Γ ⊢ congTm cB b cA t p
            ∷ Id (El cB) (subTm (single t) b) (subTm (single u) b)
⊢congId {cA = cA} {cB = cB} {b = b} {t = t} {u = u} dcA dcB db dt du dp =
  ⊢conv
    (⊢-cast (cong El (⌜Id⌝-cong₃ (wk-cancel-tm u cB)
                                 (wk-cancel-tm u (subTm (single t) b)) refl))
      (⊢jsub (⊢⌜Id⌝ (⊢wk dcB) (⊢wk dbt) db)
             dt du dp
             (⊢-cast (cong El (sym (⌜Id⌝-cong₃ (wk-cancel-tm t cB)
                                               (wk-cancel-tm t (subTm (single t) b))
                                               refl)))
                     (⊢conv (⊢idrefl dcB dbt)
                            (csymᵀ (credᵀ (El-⌜Id⌝ cB (subTm (single t) b)
                                                      (subTm (single t) b))))))))
    (credᵀ (El-⌜Id⌝ cB (subTm (single t) b) (subTm (single u) b)))
  where
  dbt : _ ⊢ subTm (single t) b ∷ El cB
  dbt = ⊢-cast (cong El (wk-cancel-tm t cB)) (⊢[] db dt)

------------------------------------------------------------------------
-- 5. ★ THE REFLECTION — every identification yields a hom; the two
--    axes weld with zero new rules.
------------------------------------------------------------------------

idtohomTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
idtohomTm c t p = jsub (⌜Hom⌝ (renTm vs c) (renTm vs t) (var vz)) p (hrefl c t)

⊢idtohom : {Γ : Ctx} {c t u p : RTm ⌊ Γ ⌋} →
           Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
           Γ ⊢ p ∷ Id (El c) t u →
           Γ ⊢ idtohomTm c t p ∷ Hom (El c) t u
⊢idtohom {c = c} {t = t} {u = u} dc dt du dp =
  ⊢conv
    (⊢-cast (cong El (⌜Hom⌝-cong₃ (wk-cancel-tm u c) (wk-cancel-tm u t) refl))
      (⊢jsub (⊢⌜Hom⌝ (⊢wk dc) (⊢wk dt) (⊢var here))
             dt du dp
             (⊢-cast (cong El (sym (⌜Hom⌝-cong₃ (wk-cancel-tm t c)
                                                (wk-cancel-tm t t) refl)))
                     (⊢conv (⊢hrefl dc dt)
                            (csymᵀ (credᵀ (El-⌜Hom⌝ c t t)))))))
    (credᵀ (El-⌜Hom⌝ c t u))

-- ...and reflecting a reflexivity computes to the directed reflexivity:
idtohom-computes : {Γ : Cx} (c t : RTm Γ) →
                   idtohomTm c t (idrefl c t) ⟶ hrefl c t
idtohom-computes c t =
  jsub-refl (⌜Hom⌝ (renTm vs c) (renTm vs t) (var vz)) c t (hrefl c t)
