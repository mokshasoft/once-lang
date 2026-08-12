------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — LEXREC BRANCH (0,S).
--
-- n₁ = 0 collapses rec₁ into `absurd`; n₂ = suc n₂' makes rec₂ invoke the
-- INNER IH, which is a context variable under seven ⊢wks.  The two
-- descents are `⊢ordtr` (μ₁ y ≤ 0) and `⊢strong-step` (μ₂ y ≤ n₂') — the
-- latter IS the lexicographic descent.
--
-- ⚠ THE MEASURED BRANCH.  Under codes-and-functions the same branch is
--   `…ExamplesLexCZS`, 48.7 s / 4.35 GB, against 8.8 s / 0.71 GB here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibLexrecZS where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; absurd; ordtr
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTy-renTy; renTy-subTy; subTm-renTm; renTm-subTm; subTm-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El; ty-Π )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ren-ty; ren-lemma; Ren⊢-ext )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base'; ⊢strong-step )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; cong₃; cong₄; cong₅; cong₆; sub-w; sub-w²; ren-w; ren-w²
        ; wk-singleTy; wᶠ-single; ren-wTy; ren-wᶠ; nrs-wTy; wᶠ-nrs )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat; aIHT; aIHT-ren; aIHT-fit )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w^; wTy^; wᶠ^; ⊢wkᶠ; wᶠ³-single; sub-wTy; wᶠ-sub )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
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

------------------------------------------------------------------------
-- ★ GATE STEP 2b — BRANCH (0,S).  The motive boundary first: `⊢natrec`'s
--   STEP demands `subTy nrs M0lex`, and the three ⊢lams build the `auxB`
--   form.  Under codes-and-functions this needed `auxBody-sub` plus four
--   `wk-single`s; here only the two BOUNDS can move.
------------------------------------------------------------------------

module ZS (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m₁ m₂ : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
           (dA   : Δ ⊢ty A)
           (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
           (dm₁  : (Δ ▹ A) ⊢ m₁ ∷ Nat)
           (dm₂  : (Δ ▹ A) ⊢ m₂ ∷ Nat)
           (dstp : Δ ⊢ stp ∷ lStepT A cM m₁ m₂)
           where

  -- the inner motive at n₁ = 0, over (Δ ▹ Nat[n₂])
  mot : RTy ((⌊ Δ ⌋ ∙) ∙)
  mot = M0lex (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂)

  -- ★ the boundary.  `nrs` moves only `n₂'`; the μ₁-bound is the literal
  --   `nzero` and A/cM/m₁/m₂ cannot move — they are already at depth.
  mot-s : subTy nrs mot
        ≡ auxB (renTy vs (renTy vs (renTy vs A)))
               (wᶠ (wᶠ (wᶠ cM))) (wᶠ (wᶠ (wᶠ m₁))) (wᶠ (wᶠ (wᶠ m₂)))
               nzero (nsuc (var (vs vz)))
  mot-s =
    trans (auxB-sub {σ = nrs} (renTy vs (renTy vs A)) (wᶠ (wᶠ cM))
                    (wᶠ (wᶠ m₁)) (wᶠ (wᶠ m₂)) nzero (var vz))
          (cong₆ auxB (nrs-wTy (renTy vs A)) (wᶠ-nrs (wᶠ cM))
                      (wᶠ-nrs (wᶠ m₁)) (wᶠ-nrs (wᶠ m₂)) refl refl)

  ------------------------------------------------------------------------
  -- ★ rec₁ — VACUOUS at (0,S): `μ₁ y < μ₁ x ≤ 0`.
  --
  --   The branch context is `((Δ ▹ Nat) ▹ Nat) ▹ mot` plus three ⊢lams
  --   (x, le, lt) — six slots above Δ.  `x` is `var (vs (vs vz))`, so the
  --   ⊢app fit is `aIHT-fit` (rec₁'s fit is amrec's), and that fit's bound
  --   is `w (w (wᶠ³ m₁))` by `wᶠ³-single`.
  ------------------------------------------------------------------------

  BCtx : Ctx
  BCtx = ((((((Δ ▹ Nat) ▹ Nat) ▹ mot)
             ▹ renTy vs (renTy vs (renTy vs A)))
             ▹ Hom Nat (wᶠ (wᶠ (wᶠ m₁))) nzero)
             ▹ Hom Nat (w (wᶠ (wᶠ (wᶠ m₂)))) (nsuc (var (vs (vs (vs vz))))))

  -- ⚠ `rec1tm` NOT WRITTEN.  The scaffolding above is sound; the term is
  --   not, and I will not leave a guessed one here.  What is known:
  --     * the ⊢app fit is `aIHT-fit` (rec₁'s fit is amrec's);
  --     * its bound is `w (w (wᶠ³ m₁))`, by `wᶠ³-single` at `t := wᶠ³ m₁`;
  --     * the body is `⊢strong-base'`, the shape of AmrecT's `⊢ihZ`.
  --   ⚠ AND THE TOWER DEPTHS MUST BE DERIVED FROM `BCtx`, NOT GUESSED —
  --   every failed attempt in this file and in the amrec branches was a
  --   miscounted weakening, never a design problem.  Probe each binder.

  -- ★ read off PROBE 1's goal rather than guessed: the goal was
  --     Π (wTy^ 6 A) (Π (Hom Nat (nsuc (wᶠ^ 6 m₁))
  --                              (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
  --                     (El (w (wᶠ^ 6 cM))))
  --   so the term is two ⊢lams over an `absurd` at `w (wᶠ^ 6 cM)`, and the
  --   `ordtr`'s endpoints are that Hom's, each weakened once by the second
  --   binder.  ⚠ Note `μ₁ x` stays in its SUBSTITUTED form — matching the
  --   goal exactly costs nothing here and avoids a cast in the term.
  rec1tm : RTm ⌊ BCtx ⌋
  rec1tm =
    lam (lam (absurd (w (wᶠ^ 6 cM))
                     (ordtr (nsuc (w (wᶠ^ 6 m₁)))
                            (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
                            nzero (var vz) (var (vs (vs (vs vz)))))))

  -- ⊢rec1's TYPE, verified to agree with the term above (probe 2 rejected
  -- only the subject, never the type):
  --
  --   BCtx ⊢ rec1tm ∷ aIHTat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁)
  --                          (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
  --
  ------------------------------------------------------------------------
  -- ★ PROBE 3 — `dmX` ALONE.  The handoff's instruction: this premise is
  --   where ⊢rec1 failed, so it is derived by itself before anything is
  --   assembled around it.
  ------------------------------------------------------------------------

  -- ⚠ AND THE ANSWER WAS THE `sym`, NOT THE COUNT.  `⊢wk³ (⊢wkᶠ³ dm₁)` —
  --   the count the previous session guessed — is right; what was wrong is
  --   which way the `subst` runs.  `⊢wkᶠ³` lands exactly on `BCtx`'s first
  --   FOUR slots (Nat, Nat, mot, wTy³ A), and the remaining three `⊢wk`s
  --   climb the two `Hom`s and the `y` binder.  ⭐ This is the third time a
  --   derivation failure here was bookkeeping and not design.
  dmX : (BCtx ▹ wTy^ 6 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁)) ∷ Nat
  dmX = subst (λ z → (BCtx ▹ wTy^ 6 A) ⊢ z ∷ Nat)
              (sym (cong w (wᶠ³-single (wᶠ^ 3 m₁))))
              (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁))))))

  ------------------------------------------------------------------------
  -- the other three premises, each nameable on its own
  ------------------------------------------------------------------------

  tyA₆ : BCtx ⊢ty wTy^ 6 A
  tyA₆ = ren-ty (ren-ty (ren-ty (ren-ty (ren-ty (ren-ty dA there) there)
                                        there) there) there) there

  dk : (BCtx ▹ wTy^ 6 A) ⊢ wᶠ^ 6 m₁ ∷ Nat
  dk = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁)))))

  dC : ((BCtx ▹ wTy^ 6 A)
          ▹ Hom Nat (nsuc (wᶠ^ 6 m₁))
                    (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
       ⊢ w (wᶠ^ 6 cM) ∷ U
  dC = ⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dcM))))))

  -- ⚠ the ONE cast: `le` comes out of the context in the UNSUBSTITUTED
  --   form `w⁴ (wᶠ³ m₁)` while the term carries `μ₁ x` substituted, and
  --   `wᶠ³-single` is exactly the bridge between them.  Same shape as
  --   `LibAmrec.⊢ihZ`'s `dlt`, one level deeper.
  dle : ((BCtx ▹ wTy^ 6 A)
           ▹ Hom Nat (nsuc (wᶠ^ 6 m₁))
                     (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
        ⊢ var (vs (vs (vs vz)))
        ∷ Hom Nat (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁)))) nzero
  dle = ⊢-cast (cong (λ z → Hom Nat (w (w z)) nzero)
                     (sym (wᶠ³-single (wᶠ^ 3 m₁))))
               (⊢var (there (there (there here))))

  ------------------------------------------------------------------------
  -- ★★ ⊢rec1 — the (0,S) branch's FIRST recursor argument, derived.
  --
  --   The type is forced: the step's rec₁ slot is `rec1T = aIHT`, and the
  --   ⊢app at `x = var (vs (vs vz))` fits it with `aIHT-fit`, whose output
  --   is `aIHTat …` at the SUBSTITUTED bound.  So this statement is the one
  --   the branch will consume, not a convenient variant of it.
  ------------------------------------------------------------------------

  ⊢rec1 : BCtx ⊢ rec1tm
        ∷ aIHTat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁)
                 (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
  ⊢rec1 =
    ⊢lam tyA₆
      (⊢lam (ty-Hom ty-Nat (⊢nsuc dk) dmX)
        (⊢strong-base' dC (⊢wk dk) (⊢wk dmX) (⊢var here) dle))

  ------------------------------------------------------------------------
  -- ★★★ GATE STEP 2c — `⊢rec2`, THE REAL RECURSIVE CALL.
  --
  --   n₁ = 0 still collapses rec₁ into `absurd`, but n₂ = suc n₂' makes
  --   rec₂ INVOKE the inner IH, and that IH is a context VARIABLE whose
  --   type is `renTy vs⁷ mot` — seven ⊢wks' worth of `renTy` sitting
  --   OUTSIDE the Π-chain.  This is the obstruction (0,0) never paid.
  --
  --   THE TWO DESCENTS rec₂ discharges to make the call:
  --     μ₁ y ≤ 0   plain `⊢ordtr` — μ₁ y ≤ μ₁ x and μ₁ x ≤ 0;
  --     μ₂ y ≤ n₂' `⊢strong-step` — μ₂ y < μ₂ x and μ₂ x ≤ suc n₂'.
  --   The second one IS the lexicographic descent: n₁ held, n₂ down.
  ------------------------------------------------------------------------

  -- the second measure's premises, mirroring `dk`/`dmX` exactly
  dk₂ : (BCtx ▹ wTy^ 6 A) ⊢ wᶠ^ 6 m₂ ∷ Nat
  dk₂ = ⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂)))))

  dmX₂ : (BCtx ▹ wTy^ 6 A) ⊢ w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂)) ∷ Nat
  dmX₂ = subst (λ z → (BCtx ▹ wTy^ 6 A) ⊢ z ∷ Nat)
               (sym (cong w (wᶠ³-single (wᶠ^ 3 m₂))))
               (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂))))))

  -- ★ the inner IH's own type, reassociated out of seven ⊢wks.  Under
  --   codes-and-functions this was `auxBody-w⁷`, a hand-written rung;
  --   here it is `auxB-w^ 7` and the same three lines cover (S,S) too.
  IH-w⁷ : wTy^ 7 mot
        ≡ auxB (wTy^ 9 A) (wᶠ^ 9 cM) (wᶠ^ 9 m₁) (wᶠ^ 9 m₂)
               nzero (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  IH-w⁷ = auxB-w^ 7 (wTy^ 2 A) (wᶠ^ 2 cM) (wᶠ^ 2 m₁) (wᶠ^ 2 m₂) nzero (var vz)

  -- the two descent TERMS.  Named because both appear inside the spine's
  -- substitutions, so the cancellation lemmas have to mention them.
  lt₁ZS : RTm (⌊ BCtx ⌋ ∙ ∙ ∙)
  lt₁ZS = ordtr (w (w (wᶠ^ 6 m₁))) (w (w (w (w (w (wᶠ^ 3 m₁)))))) nzero
                (var (vs vz)) (var (vs (vs (vs (vs vz)))))

  lt₂ZS : RTm (⌊ BCtx ⌋ ∙ ∙ ∙)
  lt₂ZS = ordtr (nsuc (w (w (wᶠ^ 6 m₂)))) (w (w (w (w (w (wᶠ^ 3 m₂))))))
                (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                (var vz) (var (vs (vs (vs vz))))

  rec2tm : RTm ⌊ BCtx ⌋
  rec2tm =
    lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz)))))))
                                 (var (vs (vs vz))))
                            lt₁ZS)
                       lt₂ZS)))

  ------------------------------------------------------------------------
  -- the IH spine's three fits.  ★ ONE lemma per argument, and each is
  -- `wᶠ³-single` composed with the eta lemmas — no `app`, so no β.
  ------------------------------------------------------------------------

  μ₁-fit : subTm (single (var (vs (vs vz)))) (wᶠ^ 9 m₁) ≡ w (w (wᶠ^ 6 m₁))
  μ₁-fit = wᶠ³-single (wᶠ^ 6 m₁)

  -- μ₂'s slot is under a binder, so it peels with `sub-w` first
  μ₂-fit : subTm (single lt₁ZS)
             (subTm (extS (single (var (vs (vs vz))))) (w (wᶠ^ 9 m₂)))
         ≡ w (w (wᶠ^ 6 m₂))
  μ₂-fit =
    trans (cong (subTm (single lt₁ZS))
                (trans (sub-w {σ = single (var (vs (vs vz)))} (wᶠ^ 9 m₂))
                       (cong w (wᶠ³-single (wᶠ^ 6 m₂)))))
          (wk-single {v = lt₁ZS} (w (w (wᶠ^ 6 m₂))))

  -- the motive's cancellation down the IH spine: wᶠ⁹ cM → wᶠ⁶ cM
  ihCancel : subTm (single lt₂ZS)
               (subTm (extS (single lt₁ZS))
                 (subTm (extS (extS (single (var (vs (vs vz))))))
                        (w (w (wᶠ^ 9 cM)))))
           ≡ w (w (wᶠ^ 6 cM))
  ihCancel =
    trans (cong (λ z → subTm (single lt₂ZS) (subTm (extS (single lt₁ZS)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (wᶠ^ 9 cM))
                       (cong (λ z → w (w z)) (wᶠ³-single (wᶠ^ 6 cM)))))
          (trans (cong (subTm (single lt₂ZS))
                       (trans (sub-w {σ = single lt₁ZS} (w (w (w (wᶠ^ 6 cM)))))
                              (cong w (wk-single {v = lt₁ZS} (w (w (wᶠ^ 6 cM)))))))
                 (wk-single {v = lt₂ZS} (w (w (wᶠ^ 6 cM)))))

  ------------------------------------------------------------------------
  -- the descents, derived
  ------------------------------------------------------------------------

  ⊢lt₁ZS : ((((BCtx ▹ wTy^ 6 A)
                ▹ Hom Nat (wᶠ^ 6 m₁)
                          (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
                ▹ Hom Nat (nsuc (w (wᶠ^ 6 m₂)))
                          (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂))))))
           ⊢ lt₁ZS ∷ Hom Nat (w (w (wᶠ^ 6 m₁))) nzero
  ⊢lt₁ZS =
    ⊢ordtr (⊢wk (⊢wk dk))
           (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁))))))))
           ⊢nzero
           (⊢-cast (cong (λ z → Hom Nat (w (w (wᶠ^ 6 m₁))) (w (w (w z))))
                         (wᶠ³-single (wᶠ^ 3 m₁)))
                   (⊢var (there here)))
           (⊢var (there (there (there (there here)))))

  ⊢lt₂ZS : ((((BCtx ▹ wTy^ 6 A)
                ▹ Hom Nat (wᶠ^ 6 m₁)
                          (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))))
                ▹ Hom Nat (nsuc (w (wᶠ^ 6 m₂)))
                          (w (w (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂))))))
           ⊢ lt₂ZS
           ∷ Hom Nat (w (w (wᶠ^ 6 m₂)))
                     (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
  ⊢lt₂ZS =
    ⊢strong-step (⊢wk (⊢wk dk₂))
                 (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂))))))))
                 (⊢var (there (there (there (there (there (there (there here))))))))
                 (⊢-cast (cong (λ z → Hom Nat (nsuc (w (w (wᶠ^ 6 m₂)))) (w (w (w z))))
                               (wᶠ³-single (wᶠ^ 3 m₂)))
                         (⊢var here))
                 (⊢var (there (there (there here))))

  ------------------------------------------------------------------------
  -- ★★ ⊢rec2, ASSEMBLED.
  ------------------------------------------------------------------------

  ⊢rec2 : BCtx ⊢ rec2tm
        ∷ rec2Tat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
                  (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂))
  ⊢rec2 =
    ⊢lam tyA₆
      (⊢lam (ty-Hom ty-Nat dk dmX)
        (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢wk dk₂)) (⊢wk dmX₂))
          (⊢-cast (cong El ihCancel)
            (⊢app (⊢app (⊢app (⊢-cast IH-w⁷
                                 (⊢var (there (there (there (there (there (there here))))))))
                               (⊢var (there (there here))))
                        (⊢-cast (sym (cong (λ z → Hom Nat z nzero) μ₁-fit)) ⊢lt₁ZS))
                  (⊢-cast (sym (cong (λ z → Hom Nat z (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                                     μ₂-fit))
                          ⊢lt₂ZS)))))

  ------------------------------------------------------------------------
  -- ★★★ GATE STEP 2d — BRANCH (0,S), ASSEMBLED.  ⚠ THIS IS THE NUMBER.
  --
  --   The same branch under codes-and-functions is `…ExamplesLexCZS`,
  --   47.2 s / 4.43 GB, and that module's cost is almost entirely these
  --   two derivations.  Everything cheap built before this point bore on
  --   nothing; the ratio measured here is what decides (S,S).
  ------------------------------------------------------------------------

  lexZS : RTm (⌊ Δ ⌋ ∙ ∙ ∙)
  lexZS =
    lam (lam (lam (app (app (app (w^ 6 stp) (var (vs (vs vz)))) rec1tm) rec2tm)))

  -- the step, six levels down — `lStepT-w^` covers every branch depth
  stp-w⁶ : wTy^ 6 (lStepT A cM m₁ m₂)
         ≡ lStepT (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)
  stp-w⁶ = lStepT-w^ 6 A cM m₁ m₂

  -- rec₁'s slot: `aIHT-fit`, unchanged — rec₁'s fit IS amrec's.
  rec1-fit : subTy (single (var (vs (vs vz))))
                   (rec1T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁))
           ≡ aIHTat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁)
                    (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
  rec1-fit = aIHT-fit (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁)

  -- rec₂'s slot: one `sub-wTy` to get the rec₁ binder's weakening out of
  -- the way, one `wk-singleTy` to cancel it, then `rec2T-fit`.
  rec2-fit : subTy (single rec1tm)
               (subTy (extS (single (var (vs (vs vz)))))
                      (renTy vs (rec2T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂))))
           ≡ rec2Tat (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₁))
                     (subTm (single (var (vs (vs vz)))) (wᶠ^ 6 m₂))
  rec2-fit =
    trans (cong (subTy (single rec1tm))
                (sub-wTy {σ = single (var (vs (vs vz)))}
                         (rec2T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂))))
          (trans (wk-singleTy {v = rec1tm}
                    (subTy (single (var (vs (vs vz))))
                           (rec2T (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂))))
                 (rec2T-fit (wTy^ 6 A) (wᶠ^ 6 cM) (wᶠ^ 6 m₁) (wᶠ^ 6 m₂)))

  -- the outer spine's cancellation: wᶠ⁶ cM peeled by the step's three ⊢apps
  cMcancel : subTm (single rec2tm)
               (subTm (extS (single rec1tm))
                 (subTm (extS (extS (single (var (vs (vs vz))))))
                        (w (w (wᶠ^ 6 cM)))))
           ≡ w (w (wᶠ^ 3 cM))
  cMcancel =
    trans (cong (λ z → subTm (single rec2tm) (subTm (extS (single rec1tm)) z))
                (trans (sub-w² {σ = single (var (vs (vs vz)))} (wᶠ^ 6 cM))
                       (cong (λ z → w (w z)) (wᶠ³-single (wᶠ^ 3 cM)))))
          (trans (cong (subTm (single rec2tm))
                       (trans (sub-w {σ = single rec1tm} (w (w (w (wᶠ^ 3 cM)))))
                              (cong w (wk-single {v = rec1tm} (w (w (wᶠ^ 3 cM)))))))
                 (wk-single {v = rec2tm} (w (w (wᶠ^ 3 cM)))))

  ⊢lexZS : (((Δ ▹ Nat) ▹ Nat) ▹ mot) ⊢ lexZS ∷ subTy nrs mot
  ⊢lexZS =
    ⊢-cast (sym mot-s)
      (⊢lam (ren-ty (ren-ty (ren-ty dA there) there) there)
        (⊢lam (ty-Hom ty-Nat (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁))) ⊢nzero)
          (⊢lam (ty-Hom ty-Nat (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂))))
                        (⊢nsuc (⊢var (there (there (there here))))))
            (⊢-cast (cong El cMcancel)
              (⊢app (⊢app (⊢app (⊢-cast stp-w⁶
                                   (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dstp)))))))
                                 (⊢var (there (there here))))
                          (⊢-cast (sym rec1-fit) ⊢rec1))
                    (⊢-cast (sym rec2-fit) ⊢rec2))))))
