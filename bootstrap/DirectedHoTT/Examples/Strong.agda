------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE E: THE SHOWCASE.
--
-- Everything here is an OBJECT-LANGUAGE term, type-checked by the
-- kernel.  Nothing is a meta-level Agda proof about the kernel.
--
--   ★ `⊢le-refl`   — `m ≤ m` at an OPEN natural, by ordinary `natrec`.
--                    The successor case is JUST THE IH, because
--                    `Hom Nat (suc m) (suc m)` COMPUTES to `Hom Nat m m`.
--   ★ `⊢le-suc`    — `m ≤ suc m`, same shape.
--   ★ the strong-induction skeleton: `⊢sind-base` / `⊢sind-step`, the
--     two branches `natrec` needs, both discharged by stage D + E.
--
-- ⚠ NO `Acc`, NO fuel, NO `TERMINATING`, and no measure anywhere: the
--   recursion is `natrec`'s own structural one, and the ORDER is the
--   thing that reduces.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Strong where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; Π; lam; app; renTy; subTy )
open import DirectedHoTT.Spec.Typing
  using ( _⟶ᵀ_; El-⌜Hom⌝; El-⌜Nat⌝; ξ-Homᵀ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; ⊢unit; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢absurd; ⊢ordtr; ⊢⌜Hom⌝; ⊢⌜Nat⌝
        ; ⊢lam; ⊢app; there; nrs; single
        ; _⊢ty_; ty-El; ty-Nat; ty-U; ty-Π; ty-Hom; wk-single )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
------------------------------------------------------------------------
-- ★ THE PRIMITIVES NOW LIVE IN `…LibStrong` — the ⌜Hom⌝/⌜Nat⌝ bridge and
--   the two everyday ≤-lemmas.  Seven `Lib*` modules build on them, so a
--   library was importing an example.
--
-- ⚠ NOT re-exported.  Clients import the primitives from `…LibStrong`
--   directly, so nothing inherits this module's closure to reach them.
------------------------------------------------------------------------

open import DirectedHoTT.Lib.Strong
  using ( El-homNat; natAsEl; elAsNat
        ; reflMot; reflTm; ⊢reflMot; ⊢le-refl-z; ⊢le-refl-s; ⊢le-refl
        ; sucMot; ⊢sucMot; ⊢le-suc )

------------------------------------------------------------------------
-- ★★★ 3. THE CROWN JEWEL: STRONG INDUCTION, ASSEMBLED.
--
--     sind : ((m : Nat) → ((k : Nat) → k < m → P k) → P m)
--          → (m : Nat) → P m
--
--   proved via the standard bounded auxiliary, BY ORDINARY `natrec`:
--
--     aux : (n : Nat) → (m : Nat) → m ≤ n → P m
--
--   ★ WHY THE MOTIVE AND THE STEP LIVE IN THE CONTEXT.  They could be
--     Agda-level parameters, but then every use under a binder needs
--     `⊢wk` plus a substitution lemma to push `renTm vs` back through
--     `subTm`.  As CONTEXT VARIABLES they are `var (vs …)`, and every
--     substitution obligation `natrec` generates COMPUTES — the proof
--     carries no plumbing at all.  `cP : Π Nat U` is the motive code
--     family, so `P t` is `El (app cP t)`.
--
--   ★ `k < m` IS `Hom Nat (nsuc k) m`.  There is no separate `<`.
------------------------------------------------------------------------


-- ── the two context entries ───────────────────────────────────────────
-- `cP : Π Nat U` (the motive code family) and `stp` (the step).

-- `(k : Nat) → k < m → P k`, in a context where vz = m, vs vz = cP.
IHT : RTy (ε ∙ ∙)
IHT = Π Nat (Π (Hom Nat (nsuc (var vz)) (var (vs vz)))
               (El (app (var (vs (vs (vs vz)))) (var (vs vz)))))

-- `(m : Nat) → ((k : Nat) → k < m → P k) → P m`, with vz = cP.
StepT : RTy (ε ∙)
StepT = Π Nat (Π IHT (El (app (var (vs (vs vz))) (var (vs vz)))))

Γ₁ : Ctx
Γ₁ = (◇ ▹ Π Nat U) ▹ StepT

-- the two hypotheses, as variables.
⊢cP : Γ₁ ⊢ var (vs vz) ∷ Π Nat U
⊢cP = ⊢var (there here)

⊢stp : Γ₁ ⊢ var vz ∷ renTy vs StepT
⊢stp = ⊢var here

-- ── the `natrec` motive: `(m : Nat) → m ≤ n → P m`, with vz = n ──────
auxMot : RTy (ε ∙ ∙ ∙)
auxMot = Π Nat (Π (Hom Nat (var vz) (var (vs vz)))
                  (El (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))))

-- ── the two branches, lifted to top level so each gets a derivation ──

-- n = 0: `m ≤ 0` and `k < m` compose to `k < 0`, which COMPUTES to
-- `base`; ex falso then inhabits `P k`.
zBr : RTm (ε ∙ ∙)
zBr = lam (lam (app (app (var (vs (vs vz))) (var (vs vz)))
                    (lam (lam (absurd
                      (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))
                      (ordtr (nsuc (var (vs vz))) (var (vs (vs (vs vz))))
                             nzero (var vz) (var (vs (vs vz)))))))))

-- n = suc n': `k < m` and `m ≤ suc n'` give `k ≤ n'`, so the IH applies.
sBr : RTm (ε ∙ ∙ ∙ ∙)
sBr = lam (lam (app (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))
                    (lam (lam (app
                      (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))
                      (ordtr (nsuc (var (vs vz))) (var (vs (vs (vs vz))))
                             (nsuc (var (vs (vs (vs (vs (vs vz)))))))
                             (var vz) (var (vs (vs vz)))))))))

auxTm : RTm (ε ∙ ∙) → RTm (ε ∙ ∙)
auxTm n = natrec zBr sBr n

-- ── the derivations ──────────────────────────────────────────────────

⊢auxMot : (Γ₁ ▹ Nat) ⊢ty auxMot
⊢auxMot =
  ty-Π ty-Nat
    (ty-Π (ty-Hom ty-Nat (⊢var here) (⊢var (there here)))
          (ty-El (⊢app (⊢var (there (there (there (there here)))))
                       (⊢var (there here)))))

-- ★★ stage D and stage E working together, and the branch the older §4
--    wrongly said needed stage D alone.
⊢zBr : Γ₁ ⊢ zBr ∷ subTy (single nzero) auxMot
⊢zBr =
  ⊢lam ty-Nat
    (⊢lam (ty-Hom ty-Nat (⊢var here) ⊢nzero)
      (⊢app (⊢app (⊢var (there (there here))) (⊢var (there here)))
            (⊢lam ty-Nat
              (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢var here))
                                   (⊢var (there (there here))))
                (⊢absurd
                  (⊢app (⊢var (there (there (there (there (there here))))))
                        (⊢var (there here)))
                  (⊢conv (⊢ordtr (⊢nsuc (⊢var (there here)))
                                 (⊢var (there (there (there here))))
                                 ⊢nzero
                                 (⊢var here)
                                 (⊢var (there (there here))))
                         (red→≅ᵀ (stepᵀ (Hom-Nat-sz (var (vs vz)))
                                        doneᵀ))))))))

-- ★★★ THE STEP.  `ordtr` composes `k < m` with `m ≤ suc n'` to
--     `k < suc n'`, i.e. `suc k ≤ suc n'` — and the ORDER COMPUTES that
--     to `k ≤ n'` in ONE reduction (`Hom-Nat-ss`).  So the IH, which
--     wants exactly `k ≤ n'`, applies with no lemma in between.  This
--     is the whole `Acc`-free descent, in five tokens of conversion.
⊢sBr : ((Γ₁ ▹ Nat) ▹ auxMot) ⊢ sBr ∷ subTy nrs auxMot
⊢sBr =
  ⊢lam ty-Nat
    (⊢lam (ty-Hom ty-Nat (⊢var here) (⊢nsuc (⊢var (there (there here)))))
      (⊢app (⊢app (⊢var (there (there (there (there here)))))
                  (⊢var (there here)))
            (⊢lam ty-Nat
              (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢var here))
                                   (⊢var (there (there here))))
                (⊢app (⊢app (⊢var (there (there (there (there here)))))
                            (⊢var (there here)))
                      (⊢conv (⊢ordtr (⊢nsuc (⊢var (there here)))
                                     (⊢var (there (there (there here))))
                                     (⊢nsuc (⊢var (there (there (there
                                       (there (there here)))))))
                                     (⊢var here)
                                     (⊢var (there (there here))))
                             (red→≅ᵀ (stepᵀ (Hom-Nat-ss
                                              (var (vs vz))
                                              (var (vs (vs (vs (vs (vs vz)))))))
                                            doneᵀ))))))))

-- ★★★ THE BOUNDED AUXILIARY.  Ordinary `natrec` on the BOUND.
⊢aux : {n : RTm ⌊ Γ₁ ⌋} → Γ₁ ⊢ n ∷ Nat →
       Γ₁ ⊢ auxTm n ∷ subTy (single n) auxMot
⊢aux dn = ⊢natrec ⊢auxMot ⊢zBr ⊢sBr dn

-- ★★★★ AND THE CROWN JEWEL ITSELF.  Instantiate the bound at `m` and
--      discharge `m ≤ m` with §1's reflexivity:
--
--        sind m = aux m m (le-refl m)  :  P m
--
--      That is COURSE-OF-VALUES INDUCTION, derived inside the language
--      from ordinary `natrec` — no `Acc`, no fuel, no `TERMINATING`, no
--      measure, and no well-foundedness argument anywhere.  The bound
--      does the work `Acc` normally does, and the ORDER's own
--      computation is what makes the descent typecheck.
sindTm : RTm (ε ∙ ∙) → RTm (ε ∙ ∙)
sindTm m = app (app (auxTm m) m) (reflTm m)

⊢sind : {m : RTm ⌊ Γ₁ ⌋} → Γ₁ ⊢ m ∷ Nat →
        Γ₁ ⊢ sindTm m ∷ El (app (var (vs vz)) m)
-- ⚠ the ONE plumbing step in the whole construction: Agda computes every
-- substitution `natrec`/`app` generate except `subTm (single v) (renTm vs m)`,
-- which is `wk-single` — substituting into a weakened term is the identity.
⊢sind {m = m} dm =
  subst (λ z → Γ₁ ⊢ sindTm m ∷ El (app (var (vs vz)) z))
        (wk-single m)
        (⊢app (⊢app (⊢aux dm) dm)
              (subst (λ z → Γ₁ ⊢ reflTm m ∷ Hom Nat m z)
                     (sym (wk-single m)) (⊢le-refl dm)))
