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

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; Ren; Π; lam; app; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTm-renTm; renTm-subTm; renTm-renTm )
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
-- ★★ THE NATURALITY KIT — what option C has to pay for.
--
-- With `Γ₅` the data were context VARIABLES, so `subTy σ` on them was a
-- LOOKUP and motive instantiation COMPUTED.  With abstract terms it does
-- not: `⊢natrec` applies `subTy (single v)` to a motive, and that has to
-- push through the weakenings written into `auxBody` — and
--     subTm (single v) (renTm vs a) ≡ a
-- is `wk-single`, PROPOSITIONAL, not definitional.
--
-- ★ It all reduces to ONE lemma: substitution commutes with weakening.
--   Everything else is congruence, because `subTy` already distributes
--   over Π/Hom/El definitionally — which is exactly the "no Beck–Chevalley
--   obstruction" headline in NbEPDirDBPi.
------------------------------------------------------------------------

cong₆ : {A B C D E F G : Set} (f : A → B → C → D → E → F → G)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {h h' : F} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → h ≡ h' →
        f a b c d e h ≡ f a' b' c' d' e' h'
cong₆ f refl refl refl refl refl refl = refl

cong₅ : {A B C D E F : Set} (f : A → B → C → D → E → F)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' →
        f a b c d e ≡ f a' b' c' d' e'
cong₅ f refl refl refl refl refl = refl

cong₄ : {A B C D E : Set} (f : A → B → C → D → E)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
cong₄ f refl refl refl refl = refl

-- ★ THE lemma.  `extS σ ₛ∘ᵣ vs` and `vs ᵣ∘ₛ σ` are the same function by
--   eta — `extS σ (vs x)` IS `renTm vs (σ x)` — so the two fusion lemmas
--   meet in the middle and this is a two-step `trans`.
sub-w : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm Γ) →
        subTm (extS σ) (w t) ≡ w (subTm σ t)
sub-w t = trans (subTm-renTm t) (sym (renTm-subTm t))

sub-w² : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm Γ) →
         subTm (extS (extS σ)) (w (w t)) ≡ w (w (subTm σ t))
sub-w² {σ = σ} t = trans (sub-w {σ = extS σ} (w t)) (cong w (sub-w t))

sub-w³ : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm Γ) →
         subTm (extS (extS (extS σ))) (w (w (w t))) ≡ w (w (w (subTm σ t)))
sub-w³ {σ = σ} t = trans (sub-w {σ = extS (extS σ)} (w (w t))) (cong w (sub-w² t))


------------------------------------------------------------------------
-- ★ THE TYPES, as combinators over the data.  Every binder's weakening is
--   written out here ONCE, which is what `auxBody` already did for the
--   motive — see its note below.  Abstract terms do not compute, so the
--   weakenings must be syntactically present rather than left to reduce.
------------------------------------------------------------------------

-- ★ the PRE-WEAKENED form: each argument already sits at the depth where
--   it is used, so `subTy σ` distributes into it by `refl` (auxBody'-sub).
auxBody' : {Γ : Cx} (cA : RTm Γ) (m₁ c₁ : RTm (Γ ∙))
           (m₂ c₂ : RTm ((Γ ∙) ∙)) (cp : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
auxBody' cA m₁ c₁ m₂ c₂ cp =
  Π (El cA)
    (Π (Hom Nat (app m₁ (var vz)) c₁)
       (Π (Hom Nat (app m₂ (var (vs vz))) c₂)
          (El (app cp (var (vs (vs vz)))))))

auxBody : {Γ : Cx} (cA cP μ₁ μ₂ b₁ b₂ : RTm Γ) → RTy Γ
auxBody cA cP μ₁ μ₂ b₁ b₂ =
  auxBody' cA (w μ₁) (w b₁) (w (w μ₂)) (w (w b₂)) (w (w (w cP)))


-- substitution distributes into the PRE-WEAKENED form definitionally
auxBody'-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (cA : RTm Γ) (m₁ c₁ : RTm (Γ ∙))
               (m₂ c₂ : RTm ((Γ ∙) ∙)) (cp : RTm (((Γ ∙) ∙) ∙)) →
               subTy σ (auxBody' cA m₁ c₁ m₂ c₂ cp)
             ≡ auxBody' (subTm σ cA)
                        (subTm (extS σ) m₁) (subTm (extS σ) c₁)
                        (subTm (extS (extS σ)) m₂) (subTm (extS (extS σ)) c₂)
                        (subTm (extS (extS (extS σ))) cp)
auxBody'-sub _ _ _ _ _ _ = refl

-- ★ and hence the one the branches actually need
auxBody-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (cA cP μ₁ μ₂ b₁ b₂ : RTm Γ) →
              subTy σ (auxBody cA cP μ₁ μ₂ b₁ b₂)
            ≡ auxBody (subTm σ cA) (subTm σ cP) (subTm σ μ₁) (subTm σ μ₂)
                      (subTm σ b₁) (subTm σ b₂)
auxBody-sub {σ = σ} cA cP μ₁ μ₂ b₁ b₂ =
  trans (auxBody'-sub cA (w μ₁) (w b₁) (w (w μ₂)) (w (w b₂)) (w (w (w cP))))
        (cong₆ auxBody' refl (sub-w μ₁) (sub-w b₁)
                             (sub-w² μ₂) (sub-w² b₂) (sub-w³ cP))


-- ★ the same lemma for RENAMINGS — `⊢wk` weakens by a renaming, so the
--   branch assemblies need this flavour and not the substitution one.
--   `extR ρ ∘ᵣ vs` and `vs ∘ᵣ ρ` again agree by eta.
ren-w : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
        renTm (extR ρ) (w t) ≡ w (renTm ρ t)
ren-w t = trans (renTm-renTm t) (sym (renTm-renTm t))

ren-w² : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
         renTm (extR (extR ρ)) (w (w t)) ≡ w (w (renTm ρ t))
ren-w² {ρ = ρ} t = trans (ren-w {ρ = extR ρ} (w t)) (cong w (ren-w t))

ren-w³ : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
         renTm (extR (extR (extR ρ))) (w (w (w t))) ≡ w (w (w (renTm ρ t)))
ren-w³ {ρ = ρ} t = trans (ren-w {ρ = extR (extR ρ)} (w (w t))) (cong w (ren-w² t))

auxBody-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ₁ μ₂ b₁ b₂ : RTm Γ) →
              renTy ρ (auxBody cA cP μ₁ μ₂ b₁ b₂)
            ≡ auxBody (renTm ρ cA) (renTm ρ cP) (renTm ρ μ₁) (renTm ρ μ₂)
                      (renTm ρ b₁) (renTm ρ b₂)
auxBody-ren cA cP μ₁ μ₂ b₁ b₂ =
  cong₆ auxBody' refl (ren-w μ₁) (ren-w b₁) (ren-w² μ₂) (ren-w² b₂) (ren-w³ cP)

-- `(y : A) → μ₁ y < μ₁ x → P y`
rec1T' : {Γ : Cx} (cA : RTm Γ) (m₁ x' : RTm (Γ ∙)) (cp : RTm ((Γ ∙) ∙)) → RTy Γ
rec1T' cA m₁ x' cp =
  Π (El cA)
    (Π (Hom Nat (nsuc (app m₁ (var vz))) (app m₁ x'))
       (El (app cp (var (vs vz)))))

rec1T : {Γ : Cx} (cA cP μ₁ x : RTm Γ) → RTy Γ
rec1T cA cP μ₁ x = rec1T' cA (w μ₁) (w x) (w (w cP))

rec1T-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (cA cP μ₁ x : RTm Γ) →
            subTy σ (rec1T cA cP μ₁ x)
          ≡ rec1T (subTm σ cA) (subTm σ cP) (subTm σ μ₁) (subTm σ x)
rec1T-sub cA cP μ₁ x = cong₄ rec1T' refl (sub-w μ₁) (sub-w x) (sub-w² cP)

rec1T-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ₁ x : RTm Γ) →
            renTy ρ (rec1T cA cP μ₁ x)
          ≡ rec1T (renTm ρ cA) (renTm ρ cP) (renTm ρ μ₁) (renTm ρ x)
rec1T-ren cA cP μ₁ x = cong₄ rec1T' refl (ren-w μ₁) (ren-w x) (ren-w² cP)

-- `(y : A) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`
rec2T' : {Γ : Cx} (cA : RTm Γ) (m₁ x₁ : RTm (Γ ∙))
         (m₂ x₂ : RTm ((Γ ∙) ∙)) (cp : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
rec2T' cA m₁ x₁ m₂ x₂ cp =
  Π (El cA)
    (Π (Hom Nat (app m₁ (var vz)) (app m₁ x₁))
       (Π (Hom Nat (nsuc (app m₂ (var (vs vz)))) (app m₂ x₂))
          (El (app cp (var (vs (vs vz)))))))

rec2T : {Γ : Cx} (cA cP μ₁ μ₂ x : RTm Γ) → RTy Γ
rec2T cA cP μ₁ μ₂ x =
  rec2T' cA (w μ₁) (w x) (w (w μ₂)) (w (w x)) (w (w (w cP)))

rec2T-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (cA cP μ₁ μ₂ x : RTm Γ) →
            subTy σ (rec2T cA cP μ₁ μ₂ x)
          ≡ rec2T (subTm σ cA) (subTm σ cP) (subTm σ μ₁) (subTm σ μ₂) (subTm σ x)
rec2T-sub cA cP μ₁ μ₂ x =
  cong₆ rec2T' refl (sub-w μ₁) (sub-w x) (sub-w² μ₂) (sub-w² x) (sub-w³ cP)

rec2T-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ₁ μ₂ x : RTm Γ) →
            renTy ρ (rec2T cA cP μ₁ μ₂ x)
          ≡ rec2T (renTm ρ cA) (renTm ρ cP) (renTm ρ μ₁) (renTm ρ μ₂) (renTm ρ x)
rec2T-ren cA cP μ₁ μ₂ x =
  cong₆ rec2T' refl (ren-w μ₁) (ren-w x) (ren-w² μ₂) (ren-w² x) (ren-w³ cP)

-- `(x : A) → rec₁ → rec₂ → P x`
lStepT' : {Γ : Cx} (cA : RTm Γ) (r₁ : RTy (Γ ∙)) (r₂ : RTy ((Γ ∙) ∙))
          (cp : RTm (((Γ ∙) ∙) ∙)) → RTy Γ
lStepT' cA r₁ r₂ cp =
  Π (El cA) (Π r₁ (Π r₂ (El (app cp (var (vs (vs vz)))))))

lStepT : {Γ : Cx} (cA cP μ₁ μ₂ : RTm Γ) → RTy Γ
lStepT cA cP μ₁ μ₂ =
  lStepT' cA (rec1T (w cA) (w cP) (w μ₁) (var vz))
             (rec2T (w (w cA)) (w (w cP)) (w (w μ₁)) (w (w μ₂)) (var (vs vz)))
             (w (w (w cP)))

-- ★ NEEDED BY EVERY BRANCH ASSEMBLY.  `⊢wk`ing the step gives
--   `renTy vs (lStepT …)`, which Agda pushes INTO the Π-chain rather than
--   reassociating; without this the motive arrives as
--   `renTm (extR³ vs)ⁿ (w³ cP)` and the ⊢app spine's substitutions have
--   nothing to cancel against.
lStepT-ren : {Γ Δ : Cx} {ρ : Ren Γ Δ} (cA cP μ₁ μ₂ : RTm Γ) →
             renTy ρ (lStepT cA cP μ₁ μ₂)
           ≡ lStepT (renTm ρ cA) (renTm ρ cP) (renTm ρ μ₁) (renTm ρ μ₂)
lStepT-ren {ρ = ρ} cA cP μ₁ μ₂ =
  cong₄ lStepT' refl
    (trans (rec1T-ren (w cA) (w cP) (w μ₁) (var vz))
           (cong₄ rec1T (ren-w cA) (ren-w cP) (ren-w μ₁) refl))
    (trans (rec2T-ren (w (w cA)) (w (w cP)) (w (w μ₁)) (w (w μ₂)) (var (vs vz)))
           (cong₅ rec2T (ren-w² cA) (ren-w² cP) (ren-w² μ₁) (ren-w² μ₂) refl))
    (ren-w³ cP)

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
