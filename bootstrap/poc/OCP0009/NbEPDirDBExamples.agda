------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES: proving IN the dHoTT kernel, today.
--
-- The kernel is a deep embedding, so "programs and proofs in the object
-- language" are ordinary Agda values: a proof is a typing derivation, a
-- computation is a `⟶*`-chain.  No porting to Once needed.  This module
-- exercises what the directed fragment CAN do —
--
--   ★ `⊢trans`  — directed COMPOSITION of homs, as a typed kernel term:
--     `tr` at the composition motive IS `trans`.  (What J/`tr` bought.)
--   ★ `⊢runit`  — composition with an identity path computes away
--     DEFINITIONALLY (`tr-J-base`): the right unit law is a reduction.
--   ★ `⊢idU`, `univalence-computes` — a λ-term IS a universe path, and
--     transporting along it IS applying it (two β-like steps).
--   ★ `pw-unfolds` — a reflexivity at a function code unfolds to the
--     pointwise family of reflexivities.
--   ★ `base-empty` — the kernel proves its own ex falso: no closed
--     `base`-inhabitant (G2's consistency, applied).
--
-- — and documents, at each gap, what CANNOT be written (the roadmap's
-- forcing functions):
--
--   ✗ `sym`   : unwritable — its motive is `Neg`, not `Pos`
--     (`NbEPDirDBVar`'s negative control); no derivation exists.
--   ✗ `cong`  : unwritable — there is NO former for a function's action
--     on a hom, and `tr`'s motives cannot have `f (var vz)` targets
--     (the directed-`ap` gap; see the two-former plan).
--   ✗ `subst` : `tr` is licensed at `PosC` motives only — transport at
--     an arbitrary family is exactly what directedness forbids.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamples where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr
        ; renTm; renTy; subTm; ⌜Hom⌝-cong₃ )
open import poc.OCP0009.NbEPDirDBVar
  using ( occ-ren-tm; avoids-wk )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶_; _⟶*_; done; step
        ; β; tr-taut; tr-J-base; hrefl-pw
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Hom⌝; Hom-U
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; here
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢hrefl; ⊢tr; ⊢conv
        ; _⊢ty_; ty-base; ty-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBCanon using ( consistency )

------------------------------------------------------------------------
-- 1. ★ DIRECTED COMPOSITION — `trans`, the first real theorem one
--    proves in any path calculus.  In the directed kernel it is not a
--    new primitive: `tr` at the composition motive
--    `⌜Hom⌝ (wk c) (wk a) (var vz)` transports "a hom out of `a`"
--    along `q`, i.e. POST-COMPOSES.  The two `subst`s below are the
--    weakening-cancellation arithmetic (`wk-single`), nothing more.
------------------------------------------------------------------------

comp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
comp c a q p = tr (⌜Hom⌝ (renTm vs c) (renTm vs a) (var vz)) q p

⊢trans : {Γ : Ctx} {c a t u p q : RTm ⌊ Γ ⌋} →
         Γ ⊢ c ∷ U → Γ ⊢ a ∷ El c →
         Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
         Γ ⊢ p ∷ Hom (El c) a t →
         Γ ⊢ q ∷ Hom (El c) t u →
         Γ ⊢ comp c a q p ∷ Hom (El c) a u
⊢trans {c = c} {a} {t} {u} {p} {q} dc da dt du dp dq =
  ⊢conv
    (⊢tr (⊢wk dc) (⊢wk da) (⊢var here)
         (occ-ren-tm avoids-wk c) (occ-ren-tm avoids-wk a)
         dt du dq
         (subst (λ z → _ ⊢ p ∷ El z) (sym (motive-at t))
                (⊢conv dp (csymᵀ (credᵀ (El-⌜Hom⌝ c a t))))))
    (subst (λ z → El z ≅ᵀ Hom (El c) a u) (sym (motive-at u))
           (credᵀ (El-⌜Hom⌝ c a u)))
  where
  motive-at : (w : RTm ⌊ _ ⌋) →
              subTm (single w) (⌜Hom⌝ (renTm vs c) (renTm vs a) (var vz))
              ≡ ⌜Hom⌝ c a w
  motive-at w = ⌜Hom⌝-cong₃ (wk-single c) (wk-single a) refl

------------------------------------------------------------------------
-- 2. ★ THE RIGHT UNIT LAW IS A REDUCTION.  Composing with the identity
--    path at a stable code computes away by J (`tr-J-base`): not a
--    propositional lemma — a definitional equality.
------------------------------------------------------------------------

runit : {Γ : Cx} (a t p : RTm Γ) →
        comp ⌜base⌝ a (hrefl ⌜base⌝ t) p ⟶ p
runit a t p = tr-J-base _ _ _ t p

-- ...and the composite is well-typed at exactly the composed hom's type
-- (instantiate `⊢trans` at `q := hrefl ⌜base⌝ t`).
⊢runit : {Γ : Ctx} {a t p : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ El ⌜base⌝ → Γ ⊢ t ∷ El ⌜base⌝ →
         Γ ⊢ p ∷ Hom (El ⌜base⌝) a t →
         Γ ⊢ comp ⌜base⌝ a (hrefl ⌜base⌝ t) p ∷ Hom (El ⌜base⌝) a t
⊢runit da dt dp = ⊢trans ⊢⌜base⌝ da dt dt dp (⊢hrefl ⊢⌜base⌝ dt)

------------------------------------------------------------------------
-- 3. ★ DIRECTED UNIVALENCE COMPUTES.  A λ-term IS a universe path
--    (`Hom U` unfolds to a function type), and transporting along it
--    IS applying it: `tr` at the tautological motive fires `tr-taut`,
--    then β.  Two steps from "transport along this path" to "the
--    function's value".
------------------------------------------------------------------------

⊢idU : ◇ ⊢ lam (var vz) ∷ Hom U ⌜base⌝ ⌜base⌝
⊢idU = ⊢conv (⊢lam (ty-El ⊢⌜base⌝) (⊢var here))
             (csymᵀ (credᵀ (Hom-U ⌜base⌝ ⌜base⌝)))

univalence-computes :
  {Γ : Cx} (e : RTm Γ) →
  tr (var vz) (lam (var vz)) e ⟶* e
univalence-computes e =
  step (tr-taut (var vz) e) (step (β (var vz) e) done)

------------------------------------------------------------------------
-- 4. ★ POINTWISE REFLEXIVITY.  A reflexivity at a FUNCTION code is not
--    stuck: it unfolds to the family of reflexivities at the codomain,
--    one per argument (`hrefl-pw`; `pwBody` computes the body code).
------------------------------------------------------------------------

pw-unfolds : {Γ : Cx} (f : RTm Γ) →
             hrefl (⌜Π⌝ ⌜base⌝ ⌜base⌝) f ⟶
             lam (hrefl ⌜base⌝ (app (renTm vs f) (var vz)))
pw-unfolds f = hrefl-pw (⌜Π⌝ ⌜base⌝ ⌜base⌝) f refl

------------------------------------------------------------------------
-- 5. ★ EX FALSO, INTERNALLY USABLE.  G2's consistency theorem, applied:
--    any closed kernel term claimed to inhabit `base` is a meta-level
--    absurdity — the kernel's own empty type works.
------------------------------------------------------------------------

base-empty : {t : RTm ε} → ◇ ⊢ t ∷ base → ⊥
base-empty = consistency

------------------------------------------------------------------------
-- 6. ✗ THE GAPS, demonstrated by absence (the roadmap's forcing
--    functions — see memory `two-former-kernel-direction`):
--
--    `sym p` for `p : Hom (El c) t u`: there is no term to write.  The
--    only transport motives are `PosC`'s (`var vz`, `⌜Hom⌝ c a (var vz)`)
--    and sym's motive `Hom _ (var vz) b` is `Neg` — NbEPDirDBVar's
--    negative control proves no `Pos` derivation exists.
--
--    `cong f p : Hom _ (f t) (f u)`: no former acts on homs; a motive
--    `⌜Hom⌝ c a (app f (var vz))` is outside `PosC` (the target must be
--    the bare variable).  This is the directed-`ap` gap: even the
--    `⊢trans` chains above cannot be built UNDER a constructor.
--
--    `subst P eq`: transport at an arbitrary family — forbidden by
--    directedness itself (arbitrary families have no variance), fixed
--    only by the two-former kernel (`Id` + J alongside `Hom`).
------------------------------------------------------------------------
