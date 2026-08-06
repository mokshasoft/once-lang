------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE E: LEXICOGRAPHIC RECURSION.
--
-- Verifies the ARCHITECTURE.md claim that the remaining WF-axis induction
-- forms are DERIVABLE, not new kernel formers.  Nothing here is added to
-- `RTm`/`RTy`/`_⊢_∷_` — this is an object-language DEFINITION built from
-- `natrec`, `ordtr`, `absurd` and Π, so it cannot affect soundness.
--
--     lexrec : ((x : Nat) → ((y) → μ₁ y < μ₁ x → P y)
--                         → ((y) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y)
--                         → P x)
--            → (x : Nat) → P x
--
-- ★ TWO DESIGN POINTS THAT MAKE IT CHEAP ON THIS KERNEL:
--   * the descent is stated with `<` and `≤` — both COMPUTING `Hom Nat` —
--     so NO equality on ℕ is needed (which would drag in `Id`/`jsub`);
--   * TWO recursor arguments instead of one disjunction, so NO COPRODUCT
--     is needed — `RTy` has none.
--
-- ★ THE CARRIER IS `Nat`, deliberately.  Carrier-genericity is verified
--   SEPARATELY by `⊢amrec` (NbEPDirDBExamplesDogfood), which generalises
--   to any `A : U` with its proof UNCHANGED.  What is in doubt here is the
--   NESTING structure, and that is what this file tests.
--
-- ⚠ NO `Acc`, NO fuel, NO `TERMINATING`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLex where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; Π; lam; app; renTy; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢absurd; ⊢ordtr
        ; _⊢ty_; ty-El; ty-Nat; ty-U; ty-Π; ty-Hom )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong
  using ( El-homNat; ⊢le-refl; reflTm )

------------------------------------------------------------------------
-- 1. THE CONTEXT.  `cP : Nat → U` (motive), `μ₁ μ₂ : Nat → Nat` (the two
--    measures), `stp` (the step).  Context variables, so every
--    substitution `natrec`/`app` generates COMPUTES.
------------------------------------------------------------------------

-- `(y : Nat) → μ₁ y < μ₁ x → P y`   — vz = x, vs = μ₂, vs² = μ₁, vs³ = cP
REC1T : RTy (ε ∙ ∙ ∙ ∙)
REC1T =
  Π Nat (Π (Hom Nat (nsuc (app (var (vs (vs (vs vz)))) (var vz)))
                    (app (var (vs (vs (vs vz)))) (var (vs vz))))
           (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))))

-- `(y : Nat) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`
-- vz = rec1, vs = x, vs² = μ₂, vs³ = μ₁, vs⁴ = cP
REC2T : RTy (ε ∙ ∙ ∙ ∙ ∙)
REC2T =
  Π Nat (Π (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var vz))
                    (app (var (vs (vs (vs (vs vz))))) (var (vs (vs vz)))))
           (Π (Hom Nat (nsuc (app (var (vs (vs (vs (vs vz))))) (var (vs vz))))
                       (app (var (vs (vs (vs (vs vz))))) (var (vs (vs (vs vz))))))
              (El (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))))))

-- vz = μ₂, vs = μ₁, vs² = cP
LStepT : RTy (ε ∙ ∙ ∙)
LStepT =
  Π Nat (Π REC1T (Π REC2T
    (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs (vs vz)))))))

Γ₅ : Ctx
Γ₅ = (((◇ ▹ Π Nat U) ▹ Π Nat Nat) ▹ Π Nat Nat) ▹ LStepT

------------------------------------------------------------------------
-- 2. THE DOUBLY-BOUNDED AUXILIARY.
--
--      aux : (n₁ : Nat) → (n₂ : Nat) → (x : Nat)
--          → μ₁ x ≤ n₁ → μ₂ x ≤ n₂ → P x
--
--    by `natrec` on n₁, and INSIDE the branches, `natrec` on n₂.  That
--    nesting IS the lexicographic order: a `rec₁` call decreases n₁ and
--    RESETS n₂; a `rec₂` call keeps n₁ and decreases n₂.
--
--    vz = n₁, vs = stp, vs² = μ₂, vs³ = μ₁, vs⁴ = cP
------------------------------------------------------------------------

lexAuxMot : RTy (ε ∙ ∙ ∙ ∙ ∙)
lexAuxMot =
  Π Nat (Π Nat
    (Π (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var vz))
                (var (vs (vs vz))))
       (Π (Hom Nat (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs vz)))
                   (var (vs (vs vz))))
          (El (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                   (var (vs (vs vz))))))))

------------------------------------------------------------------------
-- ⚠⚠ CHECKPOINT — THE STATEMENT IS VERIFIED, THE DERIVATION IS NOT.
--
-- Everything above TYPECHECKS: `REC1T`, `REC2T`, `LStepT`, `Γ₅` and
-- `lexAuxMot` are well-formed, which settles the part most likely to be
-- wrong — that the lexicographic descent is EXPRESSIBLE in this kernel
-- with no equality on ℕ and no coproduct.
--
-- What remains is the derivation, and it is a LARGE mechanical build:
-- four branches at 10–14 de Bruijn levels.  Structure, fully worked out:
--
--   aux : (n₁ n₂ x : Nat) → μ₁ x ≤ n₁ → μ₂ x ≤ n₂ → P x
--       = natrec on n₁, and INSIDE EACH BRANCH a natrec on n₂.
--
--   ★ that nesting IS the lexicographic order: a `rec₁` call decreases
--     n₁ and RESETS n₂ to `μ₂ y`; a `rec₂` call keeps n₁ and decreases
--     n₂.  Both branches of the OUTER recursion need the inner one —
--     at n₁ = 0, `rec₁` is vacuous but `rec₂` still recurses on μ₂.
--
--   the four branches, and how each discharges its obligations:
--     (0,0)  rec₁ : μ₁ y < μ₁ x ≤ 0        → ordtr, then `absurd`
--            rec₂ : μ₂ y < μ₂ x ≤ 0        → ordtr, then `absurd`
--     (0,S)  rec₁ : as above, `absurd`
--            rec₂ : μ₂ y < μ₂ x ≤ suc n₂'  → ordtr + Hom-Nat-ss → IH₂
--     (S,0)  rec₁ : μ₁ y < μ₁ x ≤ suc n₁'  → ordtr + Hom-Nat-ss → IH₁
--            rec₂ : `absurd`
--     (S,S)  rec₁ → IH₁ (bound n₁' , μ₂ y) ; rec₂ → IH₂ (bound n₁ , n₂')
--
--   then  lexrec x = aux (μ₁ x) (μ₂ x) x (le-refl _) (le-refl _).
--
-- ★ EVERY obligation above is a move already MACHINE-CHECKED elsewhere in
--   this POC: `ordtr` composition (⊢monus-le), `Hom-Nat-ss` peeling
--   (⊢strong-step), and `absurd` at a collapsed order (⊢strong-base').
--   Nothing new is required from the kernel — which is the claim under
--   test — but "assembles as expected" is NOT yet verified, and the
--   `ordtr` checkpoint is the standing reminder that mechanical-looking
--   remainders can hide real work.
------------------------------------------------------------------------
