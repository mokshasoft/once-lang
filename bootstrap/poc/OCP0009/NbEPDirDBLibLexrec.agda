------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — LEXICOGRAPHIC RECURSION.  ★ ENTRY POINT.
--
--     lexrec : ((x : A) → ((y : A) → μ₁ y < μ₁ x → P y)
--                       → ((y : A) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y)
--                       → P x)
--            → (x : A) → P x
--
-- THE THREE LAYERS, outward:
--
--   inner natrec  on n₂, twice — once under the outer ZERO branch with
--                 motive `mot`, once under the outer STEP branch with
--                 motive `imot`.  Branches (0,0)/(0,S) and (S,0)/(S,S).
--   outer natrec  on n₁, motive `omot = lexMot …`, whose body is
--                 `Π Nat …` — n₂ is quantified INSIDE, which is precisely
--                 "when μ₁ drops, μ₂ is unconstrained".
--   ⊢lexrecΠ      the module applied to ITSELF at `Δ ▹ A`, so the two
--                 bounds are the measure families `m₁`/`m₂` themselves
--                 and both order obligations are REFLEXIVITY.
--
-- ★ Same shape as `LibAmrec`'s `AmT`/`AmTΠ`, one bound wider.  The
--   conclusion is `Π A (El cM)` — no `app`, no β-redex, exactly as D4
--   predicted and `⊢amrecΠ` already delivers.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibLexrec where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; lam; app; natrec; absurd; ordtr
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El; ty-Π; wk-single )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ren-ty )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; wᶠ; cong₆; sub-w; sub-w²; wk-singleTy; wᶠ-single
        ; wᶠ¹-single; w^; wTy^; wᶠ^; ⊢wkᶠ )
-- ★ THE PUBLIC ENTRY POINT.  A caller imports THIS module and nothing
--   else: the type layer is re-exported, the four branches are private
--   implementation.  They are separate files only because Agda's
--   traversal phases are per-module and branch (S,S) alone is 1.7 GB.
open import poc.OCP0009.NbEPDirDBLibLexrecT public
open import poc.OCP0009.NbEPDirDBLibLexrecZZ using ( module ZZ )
open import poc.OCP0009.NbEPDirDBLibLexrecZS using ( module ZS )
open import poc.OCP0009.NbEPDirDBLibLexrecSZ using ( module SZ )
open import poc.OCP0009.NbEPDirDBLibLexrecSS using ( module SS )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

------------------------------------------------------------------------
-- THE BOUNDED AUXILIARY, over an arbitrary ambient `Δ`.
------------------------------------------------------------------------

module Asm (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m₁ m₂ : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
           (dA   : Δ ⊢ty A)
           (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
           (dm₁  : (Δ ▹ A) ⊢ m₁ ∷ Nat)
           (dm₂  : (Δ ▹ A) ⊢ m₂ ∷ Nat)
           (dstp : Δ ⊢ stp ∷ lStepT A cM m₁ m₂)
           where

  open ZZ Δ A cM m₁ m₂ stp dA dcM dm₁ dm₂ dstp using ( mot; lexZZ; ⊢lexZZ )
  open ZS Δ A cM m₁ m₂ stp dA dcM dm₁ dm₂ dstp using ( lexZS; ⊢lexZS )
  open SZ Δ A cM m₁ m₂ stp dA dcM dm₁ dm₂ dstp using ( omot; imot; lexSZ; ⊢lexSZ )
  open SS Δ A cM m₁ m₂ stp dA dcM dm₁ dm₂ dstp using ( lexSS; ⊢lexSS )

  ------------------------------------------------------------------------
  -- the three motives are WELL-FORMED.  ⚠ `⊢natrec` demands this and the
  --   branches never did — it is the one obligation the branch modules
  --   left to the assembly.
  ------------------------------------------------------------------------

  ⊢mot : ((Δ ▹ Nat) ▹ Nat) ⊢ty mot
  ⊢mot =
    ty-Π (ren-ty (ren-ty dA there) there)
      (ty-Π (ty-Hom ty-Nat (⊢wkᶠ (⊢wkᶠ dm₁)) ⊢nzero)
        (ty-Π (ty-Hom ty-Nat (⊢wk (⊢wkᶠ (⊢wkᶠ dm₂)))
                      (⊢var (there (there here))))
              (ty-El (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ dcM)))))))

  ⊢imot : ((((Δ ▹ Nat) ▹ omot) ▹ Nat) ▹ Nat) ⊢ty imot
  ⊢imot =
    ty-Π (ren-ty (ren-ty (ren-ty (ren-ty dA there) there) there) there)
      (ty-Π (ty-Hom ty-Nat (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₁))))
                    (⊢nsuc (⊢var (there (there (there (there here)))))))
        (ty-Π (ty-Hom ty-Nat (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dm₂)))))
                      (⊢var (there (there here))))
              (ty-El (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ (⊢wkᶠ dcM)))))))))

  ⊢omot : (Δ ▹ Nat) ⊢ty omot
  ⊢omot =
    ty-Π ty-Nat
      (ty-Π (ren-ty (ren-ty dA there) there)
        (ty-Π (ty-Hom ty-Nat (⊢wkᶠ (⊢wkᶠ dm₁)) (⊢var (there (there here))))
          (ty-Π (ty-Hom ty-Nat (⊢wk (⊢wkᶠ (⊢wkᶠ dm₂)))
                        (⊢var (there (there here))))
                (ty-El (⊢wk (⊢wk (⊢wkᶠ (⊢wkᶠ dcM))))))))

  ------------------------------------------------------------------------
  -- ★ THE OUTER ZERO BRANCH — `lam` over the inner recursor at n₁ = 0.
  --   Its two branches are (0,0) and (0,S).
  ------------------------------------------------------------------------

  mot-at-vz : subTy (single (var vz)) mot
            ≡ auxB (wTy^ 1 A) (wᶠ^ 1 cM) (wᶠ^ 1 m₁) (wᶠ^ 1 m₂) nzero (var vz)
  mot-at-vz =
    trans (auxB-sub {σ = single (var vz)} (wTy^ 2 A) (wᶠ^ 2 cM) (wᶠ^ 2 m₁)
                    (wᶠ^ 2 m₂) nzero (var vz))
          (cong₆ auxB (wk-singleTy {v = var vz} (wTy^ 1 A))
                      (wᶠ-single {v = var vz} (wᶠ^ 1 cM))
                      (wᶠ-single {v = var vz} (wᶠ^ 1 m₁))
                      (wᶠ-single {v = var vz} (wᶠ^ 1 m₂)) refl refl)

  omot-z : subTy (single nzero) omot
         ≡ Π Nat (auxB (wTy^ 1 A) (wᶠ^ 1 cM) (wᶠ^ 1 m₁) (wᶠ^ 1 m₂)
                       nzero (var vz))
  omot-z = lexMot-fit {X = nzero} A cM m₁ m₂

  lexZ : RTm ⌊ Δ ⌋
  lexZ = lam (natrec lexZZ lexZS (var vz))

  ⊢lexZ : Δ ⊢ lexZ ∷ subTy (single nzero) omot
  ⊢lexZ =
    ⊢-cast (sym omot-z)
      (⊢lam ty-Nat
        (⊢-cast mot-at-vz (⊢natrec ⊢mot ⊢lexZZ ⊢lexZS (⊢var here))))

  ------------------------------------------------------------------------
  -- ★ THE OUTER STEP BRANCH — the inner recursor at n₁ = suc n₁'.
  --   Its two branches are (S,0) and (S,S).
  ------------------------------------------------------------------------

  imot-at-vz : subTy (single (var vz)) imot
             ≡ auxB (wTy^ 3 A) (wᶠ^ 3 cM) (wᶠ^ 3 m₁) (wᶠ^ 3 m₂)
                    (nsuc (var (vs (vs vz)))) (var vz)
  imot-at-vz =
    trans (auxB-sub {σ = single (var vz)} (wTy^ 4 A) (wᶠ^ 4 cM) (wᶠ^ 4 m₁)
                    (wᶠ^ 4 m₂) (nsuc (var (vs (vs (vs vz))))) (var vz))
          (cong₆ auxB (wk-singleTy {v = var vz} (wTy^ 3 A))
                      (wᶠ-single {v = var vz} (wᶠ^ 3 cM))
                      (wᶠ-single {v = var vz} (wᶠ^ 3 m₁))
                      (wᶠ-single {v = var vz} (wᶠ^ 3 m₂)) refl refl)

  omot-s : subTy nrs omot
         ≡ Π Nat (auxB (wTy^ 3 A) (wᶠ^ 3 cM) (wᶠ^ 3 m₁) (wᶠ^ 3 m₂)
                       (nsuc (var (vs (vs vz)))) (var vz))
  omot-s = lexMot-nrs A cM m₁ m₂

  lexS : RTm (⌊ Δ ⌋ ∙ ∙)
  lexS = lam (natrec lexSZ lexSS (var vz))

  ⊢lexS : ((Δ ▹ Nat) ▹ omot) ⊢ lexS ∷ subTy nrs omot
  ⊢lexS =
    ⊢-cast (sym omot-s)
      (⊢lam ty-Nat
        (⊢-cast imot-at-vz (⊢natrec ⊢imot ⊢lexSZ ⊢lexSS (⊢var here))))

  ------------------------------------------------------------------------
  -- ★★ THE DOUBLY-BOUNDED AUXILIARY, at an arbitrary μ₁-bound.
  ------------------------------------------------------------------------

  lexAuxTm : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  lexAuxTm n = natrec lexZ lexS n

  ⊢lexAux : {n : RTm ⌊ Δ ⌋} → Δ ⊢ n ∷ Nat →
            Δ ⊢ lexAuxTm n ∷ lexMot A cM m₁ m₂ n
  ⊢lexAux dn =
    ⊢-cast (lexMot-fit A cM m₁ m₂) (⊢natrec ⊢omot ⊢lexZ ⊢lexS dn)

------------------------------------------------------------------------
-- ★★★ THE COMBINATOR ITSELF, Π-TYPED.
--
-- `Asm` is instantiated at `Δ ▹ A` — the module applies to ITSELF at a
-- deeper context, which is what parameterising over `Δ` buys (D2).
--
-- ★★ AND BOTH BOUNDS ARE LITERALLY `m₁` AND `m₂`.  With the measures
--    pre-applied, "the auxiliary at (μ₁ x, μ₂ x)" is `app (lexAuxTm m₁) m₂`
--    — no application to build them, and both typing premises are `dm₁`
--    and `dm₂` themselves, unweakened.
------------------------------------------------------------------------

module LxΠ (Δ : Ctx) (A : RTy ⌊ Δ ⌋) (cM m₁ m₂ : RTm (⌊ Δ ⌋ ∙)) (stp : RTm ⌊ Δ ⌋)
           (dA   : Δ ⊢ty A)
           (dcM  : (Δ ▹ A) ⊢ cM ∷ U)
           (dm₁  : (Δ ▹ A) ⊢ m₁ ∷ Nat)
           (dm₂  : (Δ ▹ A) ⊢ m₂ ∷ Nat)
           (dstp : Δ ⊢ stp ∷ lStepT A cM m₁ m₂)
           where

  open Asm (Δ ▹ A) (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) (w stp)
           (ren-ty dA there) (⊢wkᶠ dcM) (⊢wkᶠ dm₁) (⊢wkᶠ dm₂)
           (⊢-cast (lStepT-ren A cM m₁ m₂) (⊢wk dstp)) public

  lexrecTm : RTm ⌊ Δ ⌋
  lexrecTm =
    lam (app (app (app (app (lexAuxTm m₁) m₂) (var vz)) (reflTm m₁)) (reflTm m₂))

  -- instantiating the `Π Nat` at the SECOND bound: four peels, and the
  -- μ₁-bound's `w m₁` collapses to `m₁`.
  fit-n₂ : subTy (single m₂)
             (auxB (renTy vs (renTy vs A)) (wᶠ (wᶠ cM)) (wᶠ (wᶠ m₁))
                   (wᶠ (wᶠ m₂)) (w m₁) (var vz))
         ≡ auxB (renTy vs A) (wᶠ cM) (wᶠ m₁) (wᶠ m₂) m₁ m₂
  fit-n₂ =
    trans (auxB-sub {σ = single m₂} (renTy vs (renTy vs A)) (wᶠ (wᶠ cM))
                    (wᶠ (wᶠ m₁)) (wᶠ (wᶠ m₂)) (w m₁) (var vz))
          (cong₆ auxB (wk-singleTy {v = m₂} (renTy vs A))
                      (wᶠ-single {v = m₂} (wᶠ cM))
                      (wᶠ-single {v = m₂} (wᶠ m₁))
                      (wᶠ-single {v = m₂} (wᶠ m₂))
                      (wk-single {v = m₂} m₁) refl)

  -- ★ the μ₂-order slot's two endpoints, after `x` and the μ₁-proof have
  --   been substituted.  BOTH land on `m₂`, so the obligation is `m₂ ≤ m₂`.
  fit-r₂ˡ : subTm (single (reflTm m₁))
              (subTm (extS (single (var vz))) (w (wᶠ m₂)))
          ≡ m₂
  fit-r₂ˡ =
    trans (cong (subTm (single (reflTm m₁)))
                (trans (sub-w {σ = single (var vz)} (wᶠ m₂))
                       (cong w (wᶠ¹-single m₂))))
          (wk-single {v = reflTm m₁} m₂)

  fit-r₂ʳ : subTm (single (reflTm m₁))
              (subTm (extS (single (var vz))) (w (w m₂)))
          ≡ m₂
  fit-r₂ʳ =
    trans (cong (subTm (single (reflTm m₁)))
                (trans (sub-w {σ = single (var vz)} (w m₂))
                       (cong w (wk-single {v = var vz} m₂))))
          (wk-single {v = reflTm m₁} m₂)

  -- the motive's cancellation down the auxiliary's three remaining ⊢apps
  cancelΠ : subTm (single (reflTm m₂))
              (subTm (extS (single (reflTm m₁)))
                (subTm (extS (extS (single (var vz)))) (w (w (wᶠ cM)))))
          ≡ cM
  cancelΠ =
    trans (cong (λ z → subTm (single (reflTm m₂))
                         (subTm (extS (single (reflTm m₁))) z))
                (trans (sub-w² {σ = single (var vz)} (wᶠ cM))
                       (cong (λ z → w (w z)) (wᶠ¹-single cM))))
          (trans (cong (subTm (single (reflTm m₂)))
                       (trans (sub-w {σ = single (reflTm m₁)} (w cM))
                              (cong w (wk-single {v = reflTm m₁} cM))))
                 (wk-single {v = reflTm m₂} cM))

  -- ★★ THE Π FORM.  Codomain `El cM` — the motive is already applied.
  ⊢lexrecΠ : Δ ⊢ lexrecTm ∷ Π A (El cM)
  ⊢lexrecΠ =
    ⊢lam dA
      (⊢-cast (cong El cancelΠ)
        (⊢app (⊢app (⊢app (⊢-cast fit-n₂ (⊢app (⊢lexAux dm₁) dm₂))
                           (⊢var here))
                    (⊢-cast (sym (cong₂ (λ a b → Hom Nat a b)
                                        (wᶠ¹-single m₁)
                                        (wk-single {v = var vz} m₁)))
                            (⊢le-refl dm₁)))
              (⊢-cast (sym (cong₂ (λ a b → Hom Nat a b) fit-r₂ˡ fit-r₂ʳ))
                      (⊢le-refl dm₂))))

  -- ★ …and the POINTWISE form, DERIVED — and like amrec's it needs NO
  --   CAST, because `P x` is `subTy (single x) (El cM)` definitionally.
  ⊢lexrecPt : {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ A →
              Δ ⊢ app lexrecTm x ∷ subTy (single x) (El cM)
  ⊢lexrecPt dx = ⊢app ⊢lexrecΠ dx
