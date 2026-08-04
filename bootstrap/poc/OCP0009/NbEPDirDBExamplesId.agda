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
module poc.OCP0009.NbEPDirDBExamplesId where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom; Id
        ; RTm; var; lam; app; ⌜base⌝; ⌜Hom⌝; ⌜Id⌝; hrefl; idrefl; jsub
        ; renTm; renTy; subTm; ⌜Id⌝-cong₃ )
open import poc.OCP0009.NbEPDirDBVar
  using ( occ-ren-tm; avoids-wk )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶_; _⟶*_; done; step
        ; jsub-refl
        ; _⟶ᵀ_; El-⌜Id⌝; El-⌜Hom⌝
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; here
        ; _⊢_∷_; ⊢var; ⊢⌜base⌝; ⊢⌜Id⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢idrefl; ⊢jsub; ⊢conv )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; wk-cancel-tm )

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
    (⊢jsub (⊢⌜Id⌝ (⊢wk dc) (⊢var here) (⊢wk dt))
           dt du dp
           -- seed: `idrefl c t ∷ Id (El c) t t`, converted to the
           -- motive instance at `t` (wk-cancel arithmetic + El-⌜Id⌝;
           -- exact cast lands with the greening walk)
           (⊢conv (⊢idrefl dc dt) (csymᵀ (credᵀ (El-⌜Id⌝ c t t)))))
    (credᵀ (El-⌜Id⌝ c u t))

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
    (⊢jsub (⊢⌜Id⌝ (⊢wk dc) (⊢wk da) (⊢var here))
           dt du dq
           (⊢conv dp (csymᵀ (credᵀ (El-⌜Id⌝ c a t)))))
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
    (⊢jsub (⊢⌜Id⌝ (⊢wk dcB) (⊢wk-tm-b-instance) db)
           dt du dp
           (⊢conv (⊢idrefl dcB (⊢b-at-t)) (csymᵀ (credᵀ (El-⌜Id⌝ cB _ _)))))
    (credᵀ (El-⌜Id⌝ cB _ _))
  where
  -- the two obligations the greening walk discharges with the
  -- ⊢[]-instance and wk-cancel arithmetic (Subj machinery):
  ⊢wk-tm-b-instance = ⊢wk (⊢[]-b-at dt)  -- b[t], weakened
  ⊢b-at-t           = ⊢[]-b-at dt        -- Γ ⊢ b[t] ∷ El cB
  ⊢[]-b-at : _ → _                       -- placeholder shape; greening fills
  ⊢[]-b-at = λ d → d

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
    (⊢jsub (⊢⌜Hom⌝ (⊢wk dc) (⊢wk dt) (⊢var here))
           dt du dp
           (⊢conv (⊢hrefl dc dt) (csymᵀ (credᵀ (El-⌜Hom⌝ c t t)))))
    (credᵀ (El-⌜Hom⌝ c t u))

-- ...and reflecting a reflexivity computes to the directed reflexivity:
idtohom-computes : {Γ : Cx} (c t : RTm Γ) →
                   idtohomTm c t (idrefl c t) ⟶ hrefl c t
idtohom-computes c t =
  jsub-refl (⌜Hom⌝ (renTm vs c) (renTm vs t) (var vz)) c t (hrefl c t)
