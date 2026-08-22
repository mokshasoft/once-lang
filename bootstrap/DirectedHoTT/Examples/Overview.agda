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
--   ★ `⊢cong`, `cong-computes` — CLOSED (the directed-`ap` landing):
--     a body's action on a hom is a former, and J computes at
--     reflexivities.
--   ✗ `subst` : `tr` is licensed at `PosC` motives only — transport at
--     an arbitrary family is exactly what directedness forbids.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Overview where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst; ⊥ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; renTm; renTy; subTm; ⌜Hom⌝-cong₃ )
open import DirectedHoTT.Spec.Variance
  using ( occ-ren-tm; avoids-wk; NoNatC; nonatc-ren; nnc-base )
open import DirectedHoTT.Spec.Typing
  using ( single; _⟶_; _⟶*_; done; step
        ; β; tr-taut; tr-J-base; hrefl-pw; ap-J
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Hom⌝; Hom-U
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; here
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢hrefl; ⊢tr; ⊢ap; ⊢conv
        ; _⊢ty_; ty-base; ty-El; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Metatheory.Canonicity using ( consistency )

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

-- ★ WF stage C: composition inherits `⊢tr`'s restriction — the ambient
-- code must not be ⌜Nat⌝-headed.  At an ORDERED ambient composition is
-- ≤-transitivity, which needs the endpoints in the term; that is the
-- separate `ordtr` former (ARCHITECTURE.md).
⊢trans : {Γ : Ctx} {c a t u p q : RTm ⌊ Γ ⌋} →
         Γ ⊢ c ∷ U → Γ ⊢ a ∷ El c → NoNatC c →
         Γ ⊢ t ∷ El c → Γ ⊢ u ∷ El c →
         Γ ⊢ p ∷ Hom (El c) a t →
         Γ ⊢ q ∷ Hom (El c) t u →
         Γ ⊢ comp c a q p ∷ Hom (El c) a u
⊢trans {c = c} {a} {t} {u} {p} {q} dc da nc dt du dp dq =
  ⊢conv
    (⊢tr (⊢wk dc) (⊢wk da) (⊢var here) (nonatc-ren vs nc)
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
⊢runit da dt dp = ⊢trans ⊢⌜base⌝ da nnc-base dt dt dp (⊢hrefl ⊢⌜base⌝ dt)

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
-- 6. ★ `cong` — CLOSED by the directed-`ap` landing (2026-08-04).
--    A body's action on a hom, as a typed kernel term: the source
--    ambient is FLAT (`base` here — the ℕ-analogue), the target code
--    annotates the result, and J computes at reflexivities.
------------------------------------------------------------------------

⊢cong : {Γ : Ctx} {cB : RTm ⌊ Γ ⌋} {b : RTm (⌊ Γ ⌋ ∙)} {t u p : RTm ⌊ Γ ⌋} →
        Γ ⊢ cB ∷ U →
        (Γ ▹ El ⌜base⌝) ⊢ b ∷ El (renTm vs cB) →
        Γ ⊢ t ∷ El ⌜base⌝ → Γ ⊢ u ∷ El ⌜base⌝ →
        Γ ⊢ p ∷ Hom (El ⌜base⌝) t u →
        Γ ⊢ ap cB b p
          ∷ Hom (El cB) (subTm (single t) b) (subTm (single u) b)
⊢cong dcB db dt du dp = ⊢ap ⊢⌜base⌝ refl dcB db dt du dp

-- ...and `cong` at a reflexivity COMPUTES — J fires in one step:
cong-computes : {Γ : Cx} (cB : RTm Γ) (b : RTm (Γ ∙)) (s : RTm Γ) →
                ap cB b (hrefl ⌜base⌝ s) ⟶ hrefl cB (subTm (single s) b)
cong-computes cB b s = ap-J cB b ⌜base⌝ s refl

------------------------------------------------------------------------
-- 7. ✗ THE REMAINING GAPS, demonstrated by absence (the roadmap's
--    forcing functions — see memory `two-former-kernel-direction`):
--
--    `sym p` for `p : Hom (El c) t u`: there is no term to write.  The
--    only transport motives are `PosC`'s (`var vz`, `⌜Hom⌝ c a (var vz)`)
--    and sym's motive `Hom _ (var vz) b` is `Neg` — NbEPDirDBVar's
--    negative control proves no `Pos` derivation exists.
--
--    `subst P eq`: transport at an arbitrary family — forbidden by
--    directedness itself (arbitrary families have no variance), fixed
--    only by the two-former kernel (`Id` + J alongside `Hom`).
--
--    `ap` at Σ-typed and function-typed SOURCES: deliberately deferred
--    (the flat-source key) — Σ-memberships carry componentwise
--    structure the path argument cannot supply, and lam-path `ap` is
--    higher-order cong (whiskering); both join the G3 Σ-frontier
--    ledger.
------------------------------------------------------------------------
