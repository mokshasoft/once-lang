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
module poc.OCP0009.NbEPDirDBExamplesLexC where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; Π; lam; app; renTy; renTm; subTy; extS; extR )
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
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBExamplesStrong
  using ( El-homNat; ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd
  using ( ⊢strong-base'; ⊢strong-step )

------------------------------------------------------------------------
-- ★★ OPTION C: THERE IS NO Γ₅.
--
-- The ambient context is a PARAMETER `Δ`, and the carrier, motive,
-- measures and step are Agda-level TERMS with supplied derivations,
-- weakened per binder with `⊢wk`.  Measured (SpikeCostS13, same
-- derivation throughout):
--
--     Γ₅ = 5 slots, generic carrier   42.5 s / 3.91 GB
--     Γ₅ = 4 slots, ℕ carrier          8.5 s / 0.86 GB
--     Γ₅ = 4 slots, generic carrier    8.4 s / 0.88 GB
--     ambient ABSTRACT (this)          4.1 s / 0.49 GB
--
-- ★ Cost is ~1.7× per CONTEXT SLOT (SPIKE-COST.md), so removing all four
--   is the whole game.  With Δ abstract, `⌊ Δ ⌋` is a variable rather than
--   a concrete unary numeral, and only the derivation's own binders count.
--
-- ★★ AND IT REMOVES THE INSTANTIATION PROBLEM.  With `Γ₅` there was no way
--   to use the combinator at a concrete carrier: `sub-lemma` needs a σ for
--   every slot, but the STEP could not be one — Ackermann's step must
--   build pairs, which needs the carrier concrete, which is exactly what
--   the abstract Γ₅ denied.  Here instantiation is just APPLICATION.
------------------------------------------------------------------------

w : {Γ : Cx} → RTm Γ → RTm (Γ ∙)
w = renTm vs

------------------------------------------------------------------------
-- ★ THE TYPES, as combinators over the data.  Every binder's weakening is
--   written out here ONCE, which is what `auxBody` already did for the
--   motive — see its note below.  Abstract terms do not compute, so the
--   weakenings must be syntactically present rather than left to reduce.
------------------------------------------------------------------------

auxBody : {Γ : Cx} (cA cP μ₁ μ₂ b₁ b₂ : RTm Γ) → RTy Γ
auxBody cA cP μ₁ μ₂ b₁ b₂ =
  Π (El cA)
    (Π (Hom Nat (app (w μ₁) (var vz)) (w b₁))
       (Π (Hom Nat (app (w (w μ₂)) (var (vs vz))) (w (w b₂)))
          (El (app (w (w (w cP))) (var (vs (vs vz)))))))

-- `(y : A) → μ₁ y < μ₁ x → P y`
rec1T : {Γ : Cx} (cA cP μ₁ x : RTm Γ) → RTy Γ
rec1T cA cP μ₁ x =
  Π (El cA)
    (Π (Hom Nat (nsuc (app (w μ₁) (var vz))) (app (w μ₁) (w x)))
       (El (app (w (w cP)) (var (vs vz)))))

-- `(y : A) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`
rec2T : {Γ : Cx} (cA cP μ₁ μ₂ x : RTm Γ) → RTy Γ
rec2T cA cP μ₁ μ₂ x =
  Π (El cA)
    (Π (Hom Nat (app (w μ₁) (var vz)) (app (w μ₁) (w x)))
       (Π (Hom Nat (nsuc (app (w (w μ₂)) (var (vs vz)))) (app (w (w μ₂)) (w (w x))))
          (El (app (w (w (w cP))) (var (vs (vs vz)))))))

-- `(x : A) → rec₁ → rec₂ → P x`
lStepT : {Γ : Cx} (cA cP μ₁ μ₂ : RTm Γ) → RTy Γ
lStepT cA cP μ₁ μ₂ =
  Π (El cA)
    (Π (rec1T (w cA) (w cP) (w μ₁) (var vz))
       (Π (rec2T (w (w cA)) (w (w cP)) (w (w μ₁)) (w (w μ₂)) (var (vs vz)))
          (El (app (w (w (w cP))) (var (vs (vs vz)))))))

------------------------------------------------------------------------
-- THE COMBINATOR, over an arbitrary ambient context.
------------------------------------------------------------------------

module Lx (Δ : Ctx) (cA cP μ₁ μ₂ stp : RTm ⌊ Δ ⌋)
          (dcA  : Δ ⊢ cA  ∷ U)
          (dcP  : Δ ⊢ cP  ∷ Π (El cA) U)
          (dμ₁  : Δ ⊢ μ₁  ∷ Π (El cA) Nat)
          (dμ₂  : Δ ⊢ μ₂  ∷ Π (El cA) Nat)
          (dstp : Δ ⊢ stp ∷ lStepT cA cP μ₁ μ₂)
          where

  -- vz = n₂', vs = n₁
  lexAuxMot : RTy (⌊ Δ ⌋ ∙)
  lexAuxMot =
    Π Nat (auxBody (w (w (cA))) (w (w (cP))) (w (w (μ₁))) (w (w (μ₂))) (var (vs vz)) (var vz))

  -- the n₁ = 0 motive: μ₁ bound is 0
  M0lex : RTy (⌊ Δ ⌋ ∙ ∙)
  M0lex = auxBody (w (w (cA))) (w (w (cP))) (w (w (μ₁))) (w (w (μ₂))) nzero (var vz)

  -- the n₁ = suc motive: μ₁ bound is `suc n₁'`
  M1lex : RTy (⌊ Δ ⌋ ∙ ∙ ∙ ∙)
  M1lex = auxBody (w (w (w (w (cA))))) (w (w (w (w (cP))))) (w (w (w (w (μ₁))))) (w (w (w (w (μ₂))))) (nsuc (var (vs (vs (vs vz))))) (var vz)

  lexZZ : RTm (⌊ Δ ⌋ ∙)
  lexZZ =
    lam (lam (lam (app (app (app (w (w (w (w stp)))) (var (vs (vs vz)))) (lam (lam (absurd (app (w (w (w (w (w (w (cP))))))) (var (vs vz))) (ordtr (nsuc (app (w (w (w (w (w (w (μ₁))))))) (var (vs vz)))) (app (w (w (w (w (w (w (μ₁))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz))))))))) (lam (lam (lam (absurd (app (w (w (w (w (w (w (w (cP)))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (w (w (w (w (w (w (w (μ₂)))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (μ₂)))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))))))

  lexZS : RTm (⌊ Δ ⌋ ∙ ∙ ∙)
  lexZS =
    lam (lam (lam (app (app (app (w (w (w (w (w (w stp)))))) (var (vs (vs vz)))) (lam (lam (absurd (app (w (w (w (w (w (w (w (w (cP))))))))) (var (vs vz))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w (μ₁))))))))) (var (vs vz)))) (app (w (w (w (w (w (w (w (w (μ₁))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz))))))))) (lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (ordtr (app (w (w (w (w (w (w (w (w (w (μ₁)))))))))) (var (vs (vs vz)))) (app (w (w (w (w (w (w (w (w (w (μ₁)))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var (vs vz)) (var (vs (vs (vs (vs vz))))))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w (w (μ₂)))))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (w (w (μ₂)))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))))))))))

  lexSZ : RTm (⌊ Δ ⌋ ∙ ∙ ∙)
  lexSZ =
    lam (lam (lam (app (app (app (w (w (w (w (w (w stp)))))) (var (vs (vs vz)))) (lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (app (w (w (w (w (w (w (w (w (μ₂))))))))) (var (vs vz)))) (var (vs vz))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w (μ₁))))))))) (var (vs vz)))) (app (w (w (w (w (w (w (w (w (μ₁))))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz)))))) (natrec unit (var vz) (app (w (w (w (w (w (w (w (w (μ₂))))))))) (var (vs vz)))))))) (lam (lam (lam (absurd (app (w (w (w (w (w (w (w (w (w (cP)))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w (w (μ₂)))))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (w (w (μ₂)))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))))))

  lexSS : RTm (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙)
  lexSS =
    lam (lam (lam (app (app (app (w (w (w (w (w (w (w (w stp)))))))) (var (vs (vs vz)))) (lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (app (w (w (w (w (w (w (w (w (w (w (μ₂))))))))))) (var (vs vz)))) (var (vs vz))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w (w (w (μ₁))))))))))) (var (vs vz)))) (app (w (w (w (w (w (w (w (w (w (w (μ₁))))))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var vz) (var (vs (vs (vs vz)))))) (natrec unit (var vz) (app (w (w (w (w (w (w (w (w (w (w (μ₂))))))))))) (var (vs vz)))))))) (lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (ordtr (app (w (w (w (w (w (w (w (w (w (w (w (μ₁)))))))))))) (var (vs (vs vz)))) (app (w (w (w (w (w (w (w (w (w (w (w (μ₁)))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz)) (var (vs (vs (vs (vs vz))))))) (ordtr (nsuc (app (w (w (w (w (w (w (w (w (w (w (w (μ₂)))))))))))) (var (vs (vs vz))))) (app (w (w (w (w (w (w (w (w (w (w (w (μ₂)))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))))))))))

  lexZBr : RTm ⌊ Δ ⌋
  lexZBr = lam (natrec lexZZ lexZS (var vz))

  lexSBr : RTm (⌊ Δ ⌋ ∙ ∙)
  lexSBr = lam (natrec lexSZ lexSS (var vz))

  lexAuxTm : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  lexAuxTm n = natrec lexZBr lexSBr n

  ------------------------------------------------------------------------
  -- MOTIVE WELL-FORMEDNESS — `⊢natrec` demands `(Γ ▹ Nat) ⊢ty M`.
  ------------------------------------------------------------------------

  ⊢lexAuxMot : (Δ ▹ Nat) ⊢ty lexAuxMot
  ⊢lexAuxMot =
    ty-Π ty-Nat (ty-Π (ty-El (⊢wk (⊢wk (dcA)))) (ty-Π (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (dμ₁)))) (⊢var here)) (⊢var (there (there here)))) (ty-Π (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (dμ₂))))) (⊢var (there here))) (⊢var (there (there here)))) (ty-El (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dcP)))))) (⊢var (there (there here))))))))

  ⊢M0lex : ((Δ ▹ Nat) ▹ Nat) ⊢ty M0lex
  ⊢M0lex =
    ty-Π (ty-El (⊢wk (⊢wk (dcA)))) (ty-Π (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (dμ₁)))) (⊢var here)) ⊢nzero) (ty-Π (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (dμ₂))))) (⊢var (there here))) (⊢var (there (there here)))) (ty-El (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dcP)))))) (⊢var (there (there here)))))))

  ⊢M1lex : ((((Δ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ Nat) ⊢ty M1lex
  ⊢M1lex =
    ty-Π (ty-El (⊢wk (⊢wk (⊢wk (⊢wk (dcA)))))) (ty-Π (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₁)))))) (⊢var here)) (⊢nsuc (⊢var (there (there (there (there here))))))) (ty-Π (ty-Hom ty-Nat (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dμ₂))))))) (⊢var (there here))) (⊢var (there (there here)))) (ty-El (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (dcP)))))))) (⊢var (there (there here)))))))
