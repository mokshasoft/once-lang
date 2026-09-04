------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — LEXICOGRAPHIC RECURSION, THE TYPE LAYER.
--
-- ⚠ NOT the entry point.  Callers import `NbEPDirDBLibLexrec`, which
--   re-exports everything here and adds the assembly.  This module is
--   split out only because the four branches each need it and Agda's
--   traversal phases are per-module.
--
-- ★ THE QUESTION THIS EXISTS TO ANSWER.  Option C's lexrec died at branch
--   (S,S): `LexCSS1` and `LexCSS2` each OOM at the 5.5 GB cap, both halves,
--   even under `+RTS -c`.  That was the codes-and-functions interface.
--   Families removes every `app` from the types and collapses the fitting
--   to one lemma per spine, so the elaborated terms should be markedly
--   smaller.  Does (S,S) fit?
--
-- ⚠ THIS FILE IS THE TYPE LAYER ONLY — no branch, no derivation.  It is
--   step 1 of the gate: establish that lexrec's four types EXIST under
--   families and see how much `LibRec` already supplies, before spending
--   anything on a branch.
--
-- ★ AND THE FIRST ANSWER IS FREE: `rec₁`'s type IS `aIHT`, the measure
--   recursor's IH, verbatim.  Only `rec₂` (two descents) and `lStepT` are
--   new, which is the concrete form of "these are one abstraction".
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexrecT where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; absurd; ordtr
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTy-renTy; renTy-subTy; subTm-renTm; renTm-subTm; subTm-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El; ty-Π; wk-single )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; ren-ty; ren-lemma; Ren⊢-ext )
open import DirectedHoTT.Lib.Ord using ( ⊢strong-base'; ⊢strong-step )
open import DirectedHoTT.Lib.Wk
  using ( w; wᶠ; cong₃; cong₄; cong₅; cong₆; sub-w; sub-w²; ren-w; ren-w²
        ; wk-singleTy; wᶠ-single; ren-wTy; ren-wᶠ; nrs-wTy; wᶠ-nrs )
open import DirectedHoTT.Lib.Rec using ( aIHTat; aIHT; aIHT-ren; aIHT-fit )
open import DirectedHoTT.Lib.Wk
  using ( w^; wTy^; wᶠ^; ⊢wkᶠ; wᶠ³-single; sub-wTy; wᶠ-sub )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

------------------------------------------------------------------------
-- ★ rec₁ is aIHT.  Nothing to define.
--
--     rec₁ = (y : A) → μ₁ y < μ₁ x → P y   =   aIHT A cM m₁
------------------------------------------------------------------------

rec1T : {Γ : Cx} (A : RTy Γ) (cM m₁ : RTm (Γ ∙)) → RTy (Γ ∙)
rec1T = aIHT

------------------------------------------------------------------------
-- rec₂ — `(y : A) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`.
--
-- TWO descents, so two `Hom` binders; the second measure and the motive
-- each pick up one more weakening as they pass the first.
------------------------------------------------------------------------

rec2Tat' : {Γ : Cx} (A : RTy Γ) (m₁ b₁ : RTm (Γ ∙))
           (m₂ b₂ : RTm ((Γ ∙) ∙)) (cm : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
rec2Tat' A m₁ b₁ m₂ b₂ cm =
  Π A (Π (Hom Nat m₁ b₁) (Π (Hom Nat (nsuc m₂) b₂) (El cm)))

-- at an EXPLICIT pair of bounds (D8: the bounds must be nameable)
rec2Tat : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) (μ₁x μ₂x : RTm Γ) → RTy Γ
rec2Tat A cM m₁ m₂ μ₁x μ₂x =
  rec2Tat' A m₁ (w μ₁x) (w m₂) (w (w μ₂x)) (w (w cM))

-- …and at the binder where the carrier variable IS `x`, so the bounds are
-- the measure families themselves.
rec2T : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) → RTy (Γ ∙)
rec2T A cM m₁ m₂ =
  rec2Tat (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) m₁ m₂

-- ★★ rec₂'s FITTING LEMMA — the twin of `aIHT-fit`, and like it there is
--    ONE per spine rather than one per argument.  Six peels, all of them
--    the eta lemmas or `wᶠ-single`; not an `app` in sight.
rec2T-fit : {Γ : Cx} {X : RTm Γ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) →
            subTy (single X) (rec2T A cM m₁ m₂)
          ≡ rec2Tat A cM m₁ m₂ (subTm (single X) m₁) (subTm (single X) m₂)
rec2T-fit {X = X} A cM m₁ m₂ =
  cong₆ rec2Tat' (wk-singleTy A) (wᶠ-single m₁) (sub-w m₁)
        (trans (sub-w {σ = extS (single X)} (wᶠ m₂)) (cong w (wᶠ-single m₂)))
        (sub-w² {σ = single X} m₂)
        (trans (sub-w² {σ = extS (single X)} (wᶠ cM))
               (cong (λ z → w (w z)) (wᶠ-single cM)))

------------------------------------------------------------------------
-- the step — `(x : A) → rec₁ → rec₂ → P x`
------------------------------------------------------------------------

lStepT' : {Γ : Cx} (A : RTy Γ) (r₁ : RTy (Γ ∙)) (r₂ : RTy ((Γ ∙) ∙))
          (cm : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
lStepT' A r₁ r₂ cm = Π A (Π r₁ (Π r₂ (El cm)))

lStepT : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) → RTy Γ
lStepT A cM m₁ m₂ =
  lStepT' A (rec1T A cM m₁) (renTy vs (rec2T A cM m₁ m₂)) (w (w cM))

------------------------------------------------------------------------
-- the doubly-bounded auxiliary's body — `(x : A) → μ₁ x ≤ n₁ → μ₂ x ≤ n₂
-- → P x`.  This is `aAuxB` with a second bound.
------------------------------------------------------------------------

auxB' : {Γ : Cx} (A : RTy Γ) (m₁ b₁ : RTm (Γ ∙))
        (m₂ b₂ : RTm ((Γ ∙) ∙)) (cm : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
auxB' A m₁ b₁ m₂ b₂ cm =
  Π A (Π (Hom Nat m₁ b₁) (Π (Hom Nat m₂ b₂) (El cm)))

auxB : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) (n₁ n₂ : RTm Γ) → RTy Γ
auxB A cM m₁ m₂ n₁ n₂ =
  auxB' A m₁ (w n₁) (w m₂) (w (w n₂)) (w (w cM))

-- ★ the naturality: only the two BOUNDS can move, exactly as for `aAuxB`.
auxB-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙))
           (n₁ n₂ : RTm Γ) →
           subTy σ (auxB A cM m₁ m₂ n₁ n₂)
         ≡ auxB (subTy σ A) (subTm (extS σ) cM) (subTm (extS σ) m₁)
                (subTm (extS σ) m₂) (subTm σ n₁) (subTm σ n₂)
auxB-sub {σ = σ} A cM m₁ m₂ n₁ n₂ =
  cong₆ auxB' refl refl (sub-w n₁)
        (sub-w {σ = extS σ} m₂)
        (sub-w² {σ = σ} n₂)
        (sub-w² {σ = extS σ} cM)

auxB-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙))
           (n₁ n₂ : RTm Γ) →
           renTy ρ (auxB A cM m₁ m₂ n₁ n₂)
         ≡ auxB (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m₁)
                (renTm (extR ρ) m₂) (renTm ρ n₁) (renTm ρ n₂)
auxB-ren {ρ = ρ} A cM m₁ m₂ n₁ n₂ =
  cong₆ auxB' refl refl (ren-w n₁)
        (ren-w {ρ = extR ρ} m₂)
        (ren-w² {ρ = ρ} n₂)
        (ren-w² {ρ = extR ρ} cM)

-- ★ D5 again: the AUXILIARY's ladder, indexed.  (0,S)'s inner IH sits
--   seven ⊢wks down; (S,S)'s will sit deeper, and this covers both.
auxB-w^ : {Γ : Cx} (n : ℕ) (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙))
          (n₁ n₂ : RTm Γ) →
          wTy^ n (auxB A cM m₁ m₂ n₁ n₂)
        ≡ auxB (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m₁) (wᶠ^ n m₂) (w^ n n₁) (w^ n n₂)
auxB-w^ zero    A cM m₁ m₂ n₁ n₂ = refl
auxB-w^ (suc n) A cM m₁ m₂ n₁ n₂ =
  trans (cong (renTy vs) (auxB-w^ n A cM m₁ m₂ n₁ n₂))
        (auxB-ren (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m₁) (wᶠ^ n m₂)
                  (w^ n n₁) (w^ n n₂))

------------------------------------------------------------------------
-- ★ THE `⊢wk` NATURALITY the branches need: `⊢wk`ing the step leaves a
--   `renTy` OUTSIDE `lStepT`, and Agda pushes it into the Π-chain instead
--   of reassociating.  Same obstruction every branch hits.
------------------------------------------------------------------------

rec2T-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) →
            renTy (extR ρ) (rec2T A cM m₁ m₂)
          ≡ rec2T (renTy ρ A) (renTm (extR ρ) cM)
                  (renTm (extR ρ) m₁) (renTm (extR ρ) m₂)
rec2T-ren {ρ = ρ} A cM m₁ m₂ =
  cong₆ rec2Tat' (ren-wTy A) (ren-wᶠ m₁) (ren-w {ρ = extR ρ} m₁)
        (trans (ren-w {ρ = extR (extR ρ)} (wᶠ m₂)) (cong w (ren-wᶠ m₂)))
        (trans (ren-w {ρ = extR (extR ρ)} (w m₂)) (cong w (ren-w {ρ = extR ρ} m₂)))
        (trans (ren-w {ρ = extR (extR (extR ρ))} (w (wᶠ cM)))
               (cong w (trans (ren-w {ρ = extR (extR ρ)} (wᶠ cM)) (cong w (ren-wᶠ cM)))))

lStepT-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) →
             renTy ρ (lStepT A cM m₁ m₂)
           ≡ lStepT (renTy ρ A) (renTm (extR ρ) cM)
                    (renTm (extR ρ) m₁) (renTm (extR ρ) m₂)
lStepT-ren {ρ = ρ} A cM m₁ m₂ =
  cong₄ lStepT' refl
    (aIHT-ren A cM m₁)
    (trans (ren-wTy (rec2T A cM m₁ m₂)) (cong (renTy vs) (rec2T-ren A cM m₁ m₂)))
    (trans (ren-w {ρ = extR (extR ρ)} (w cM)) (cong w (ren-w {ρ = extR ρ} cM)))

-- ★ D5 applied to lexrec: the ladder, INDEXED.  Every branch ⊢wks the step
--   a different number of times — (0,S) six, (S,S) eight — and this covers
--   all of them.
lStepT-w^ : {Γ : Cx} (n : ℕ) (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) →
            wTy^ n (lStepT A cM m₁ m₂)
          ≡ lStepT (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m₁) (wᶠ^ n m₂)
lStepT-w^ zero    A cM m₁ m₂ = refl
lStepT-w^ (suc n) A cM m₁ m₂ =
  trans (cong (renTy vs) (lStepT-w^ n A cM m₁ m₂))
        (lStepT-ren (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m₁) (wᶠ^ n m₂))

------------------------------------------------------------------------
-- THE MOTIVES.  lexrec's auxiliary is DOUBLY bounded and recursed by
-- NESTED `natrec` — outer on n₁, inner on n₂ — so there are three:
--
--   lexMot   the OUTER motive, `Π Nat (auxB … n₁ n₂)`, quantifying n₂
--   M0lex    the inner motive at n₁ = 0
--   M1lex    the inner motive at n₁ = suc n₁'
--
-- ⚠ THE μ₁-BOUND MUST BE A PARAMETER of `lexMot`, exactly as `auxMotB`
--   needed under codes-and-functions and for the same reason: `renTy vs`
--   does NOT preserve the `var (vs vz)` that writing the bound inline
--   would produce.  Families change the DATA's presentation, not this.
------------------------------------------------------------------------

lexMot : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) (b₁ : RTm Γ) → RTy Γ
lexMot A cM m₁ m₂ b₁ =
  Π Nat (auxB (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (w b₁) (var vz))

-- ★ and the OUTER motive's ladder.  (S,S) reads the outer IH out of the
--   context under nine ⊢wks, so `lexMot` needs the same treatment `auxB`
--   and `lStepT` got — indexed, not enumerated.
lexMot-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙))
             (b₁ : RTm Γ) →
             renTy ρ (lexMot A cM m₁ m₂ b₁)
           ≡ lexMot (renTy ρ A) (renTm (extR ρ) cM) (renTm (extR ρ) m₁)
                    (renTm (extR ρ) m₂) (renTm ρ b₁)
lexMot-ren {ρ = ρ} A cM m₁ m₂ b₁ =
  cong (Π Nat)
    (trans (auxB-ren {ρ = extR ρ} (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂)
                     (w b₁) (var vz))
           (cong₆ auxB (ren-wTy A) (ren-wᶠ cM) (ren-wᶠ m₁) (ren-wᶠ m₂)
                       (ren-w b₁) refl))

lexMot-w^ : {Γ : Cx} (n : ℕ) (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) (b₁ : RTm Γ) →
            wTy^ n (lexMot A cM m₁ m₂ b₁)
          ≡ lexMot (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m₁) (wᶠ^ n m₂) (w^ n b₁)
lexMot-w^ zero    A cM m₁ m₂ b₁ = refl
lexMot-w^ (suc n) A cM m₁ m₂ b₁ =
  trans (cong (renTy vs) (lexMot-w^ n A cM m₁ m₂ b₁))
        (lexMot-ren (wTy^ n A) (wᶠ^ n cM) (wᶠ^ n m₁) (wᶠ^ n m₂) (w^ n b₁))

-- ★★ THE OUTER MOTIVE'S FIT — the ASSEMBLY's load-bearing lemma, and the
--    twin of `aIHT-fit`/`rec2T-fit`: instantiating `lexMot` at a bound.
--    Four peels and two `refl`s; the μ₁-bound becomes `w X` and the
--    μ₂-bound stays the `Π Nat`'s own variable, which is exactly the
--    "n₂ is unconstrained when n₁ drops" of the lexicographic order.
lexMot-fit : {Γ : Cx} {X : RTm Γ} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) →
             subTy (single X) (lexMot (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (var vz))
           ≡ lexMot A cM m₁ m₂ X
lexMot-fit {X = X} A cM m₁ m₂ =
  cong (Π Nat)
    (trans (auxB-sub {σ = extS (single X)} (renTy vs (renTy vs A))
                     (wᶠ (wᶠ cM)) (wᶠ (wᶠ m₁)) (wᶠ (wᶠ m₂))
                     (var (vs vz)) (var vz))
           (cong₆ auxB
             (trans (sub-wTy {σ = single X} (renTy vs A))
                    (cong (renTy vs) (wk-singleTy A)))
             (trans (wᶠ-sub {σ = single X} (wᶠ cM)) (cong wᶠ (wᶠ-single cM)))
             (trans (wᶠ-sub {σ = single X} (wᶠ m₁)) (cong wᶠ (wᶠ-single m₁)))
             (trans (wᶠ-sub {σ = single X} (wᶠ m₂)) (cong wᶠ (wᶠ-single m₂)))
             refl refl))

-- ★ and its `nrs` instance, which is the OUTER STEP's boundary.  Same six
--   slots; only the μ₁-bound moves, to `suc n₁'`.
lexMot-nrs : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) →
             subTy nrs (lexMot (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (var vz))
           ≡ Π Nat (auxB (renTy vs (renTy vs (renTy vs A)))
                         (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m₁))) (wᶠ (wᶠ (wᶠ m₂)))
                         (nsuc (var (vs (vs vz)))) (var vz))
lexMot-nrs A cM m₁ m₂ =
  cong (Π Nat)
    (trans (auxB-sub {σ = extS nrs} (renTy vs (renTy vs A))
                     (wᶠ (wᶠ cM)) (wᶠ (wᶠ m₁)) (wᶠ (wᶠ m₂))
                     (var (vs vz)) (var vz))
           (cong₆ auxB
             (trans (sub-wTy {σ = nrs} (renTy vs A))
                    (cong (renTy vs) (nrs-wTy A)))
             (trans (wᶠ-sub {σ = nrs} (wᶠ cM)) (cong wᶠ (wᶠ-nrs cM)))
             (trans (wᶠ-sub {σ = nrs} (wᶠ m₁)) (cong wᶠ (wᶠ-nrs m₁)))
             (trans (wᶠ-sub {σ = nrs} (wᶠ m₂)) (cong wᶠ (wᶠ-nrs m₂)))
             refl refl))

-- the inner motives: the μ₂-bound is the inner natrec's variable, and the
-- μ₁-bound is `0` or `suc n₁'` respectively.
M0lex : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) → RTy (Γ ∙)
M0lex A cM m₁ m₂ =
  auxB (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) nzero (var vz)

M1lex : {Γ : Cx} (A : RTy Γ) (cM m₁ m₂ : RTm (Γ ∙)) (b₁ : RTm Γ) → RTy (Γ ∙)
M1lex A cM m₁ m₂ b₁ =
  auxB (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (nsuc (w b₁)) (var vz)
