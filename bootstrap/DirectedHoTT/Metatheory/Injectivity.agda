------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 26 — (B2, part 1) Π-INJECTIVITY of conversion
--                            (type-level confluence)
--
-- `NbEPDirDBSR` (dHoTT-24) scoped general subject reduction on exactly one
-- obstruction: inverting `⊢ lam t ∷ Π A B` through `⊢conv` needs Π-injectivity
-- of conversion, `Π A B ≅ᵀ Π A' B' → A ≅ᵀ A' × B ≅ᵀ B'`, which follows from
-- confluence. Confluence of terms is now proven (`NbEPDirDBConf`, dHoTT-25);
-- this module lifts it to TYPES and derives Π-injectivity — removing the
-- ceiling.
--
-- Type reduction has no top-level redex (β lives only at terms, reached via
-- `El`), so type confluence is the structural companion of term confluence:
-- parallel type reduction `_⟹ᵀ_` reuses the TERM triangle (`⟹-⁺`) at `El`
-- leaves. Then:
--   * `confluentᵀ` / `church-rosserᵀ` — confluence and joinability for types.
--   * `Π-reduct` — a reduct of `Π A B` is `Π A'' B''` with `A ⟶ᵀ* A''`,
--     `B ⟶ᵀ* B''` (Π-shape is preserved: only `ξ-Πˡ`/`ξ-Πʳ` apply).
--   * `Π-inj` — Π-INJECTIVITY OF CONVERSION. The dHoTT-24 ceiling, discharged.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Injectivity where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; Σ; _,_; _×_ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; base; U; Π; Σ'; El; Hom; RTm; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub
        ; var; lam; app; pair; fst; snd; absurd; ordtr; vz; vs; renTm
        ; Unit; Nat; unit; nzero; nsuc; natrec; ⌜Nat⌝; ⌜Unit⌝; ⌜Mu⌝
        ; Desc; Mu; con; elim
        ; IMu; icon; ielim; ⌜IMu⌝; ICon; IDesc; iι; iρ; iκ; inil; _◂_; ipayTy; ilookupD; _∈ID_; hereID; thereID; iihs; ifields; εwkTm )
open import DirectedHoTT.Spec.Typing
  using ( _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝
        ; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; El-⌜Id⌝; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜Mu⌝
        ; El-⌜IMu⌝; ξ-IMu
        ; ξ-idreflᶜ; ξ-idreflᵃ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ
        ; _⟶*_; done; step
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ
        ; _≅_; cred; crfl; csym; ctrn; hom→≅ )
open import DirectedHoTT.Metatheory.Confluence
  using ( _⟹_; pvar; plam; papp; pβ; ppair; pabsurd; pfst; psnd; pβfst; pβsnd
        ; p⌜base⌝; p⌜Π⌝; p⌜Σ⌝; p⌜Hom⌝; phrefl
        ; ptr; ptr-J-base; ptr-J-Σ; ptr-taut
        ; phrefl-pw; ptr-J-Hom; ptr-pw; pap; pap-J; p⌜Id⌝; pidrefl; pjsub; pjsub-refl
        ; ptr-J-Id; punit; pnzero; pnsuc; pnatrec; pnatrec-zero; pnatrec-suc
        ; p⌜Nat⌝; p⌜Unit⌝; ptr-J-Unit; p⌜Mu⌝; ptr-J-Mu; ptr-J-IMu
        ; pordtr; pordtr-z; pordtr-szz; pordtr-ssz; pordtr-szs; pordtr-sss
        ; ⟶*-nsuc
        ; _⁺; ⟹-refl; ⟹-⁺; ⟶→⟹; ⟹→⟶*; ⟶*-trans
        ; ⟹-ren; ⟶*-ren; ⟶*-appˡ
        ; pcon; pelim; pι
        ; p⌜IMu⌝; picon; pielim; pιi )

open import DirectedHoTT.Metatheory.Confluence
  using ( _⟹ᵀ_; pbase; pU; pUnit; pNat; pMu; pEl; pΠ; pΣ; pEl-⌜base⌝; pEl-⌜Π⌝; pEl-⌜Σ⌝; pEl-⌜Hom⌝; pHom; pHom-U; pHom-Nat-z; pHom-Nat-sz; pHom-Nat-ss; pHom-Π; pId; pEl-⌜Nat⌝; pEl-⌜Unit⌝; pEl-⌜Mu⌝; pIMu; pEl-⌜IMu⌝; pEl-⌜Id⌝; ⟹ᵀ-refl; ⟶ᵀ→⟹ᵀ; ⟹ᵀ→⟶ᵀ*; _⁺ᵀ; ⟹ᵀ-⁺ ) public

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Type multi-step reduction and its congruences.
------------------------------------------------------------------------


-- ★ `_⟶ᵀ*_`, its congruences and `red→≅ᵀ` moved to `Metatheory/RedCong`
--   (they are folds, and `TySub` needs them without the injectivity proof);
--   re-exported here so this module's own callers are unaffected.
open import DirectedHoTT.Metatheory.RedCong public











-- the two-former kernel: reducts of `Id` are `Id`-forms, componentwise
-- (Id is INERT — only the three ξ-rules exist).
Id-reduct : {A : RTy Γ} {t u : RTm Γ} {C : RTy Γ} → Id A t u ⟶ᵀ* C →
            Σ (RTy Γ) (λ A' → Σ (RTm Γ) (λ t' → Σ (RTm Γ) (λ u' →
              (C ≡ Id A' t' u') ×
              ((A ⟶ᵀ* A') × ((t ⟶* t') × (u ⟶* u'))))))
Id-reduct doneᵀ = _ , (_ , (_ , (refl , (doneᵀ , (done , done)))))
Id-reduct (stepᵀ (ξ-Idᵀ r) rest) with Id-reduct rest
... | A' , (t' , (u' , (eq , (rA , (rt , ru))))) =
      A' , (t' , (u' , (eq , (stepᵀ r rA , (rt , ru)))))
Id-reduct (stepᵀ (ξ-Idˡ r) rest) with Id-reduct rest
... | A' , (t' , (u' , (eq , (rA , (rt , ru))))) =
      A' , (t' , (u' , (eq , (rA , (step r rt , ru)))))
Id-reduct (stepᵀ (ξ-Idʳ r) rest) with Id-reduct rest
... | A' , (t' , (u' , (eq , (rA , (rt , ru))))) =
      A' , (t' , (u' , (eq , (rA , (rt , step r ru)))))





------------------------------------------------------------------------
-- ★ SPIKE (PLAN-BIDI S1): parallel TYPE reduction, its development and
--   triangle MOVED to `Metatheory/Confluence` — a term (`natrecᴹ`) now
--   carries a type, so the term development needs them mutually.
--   Re-exported below; every importer is unchanged.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Diamond → confluence → Church–Rosser, for types.
------------------------------------------------------------------------

diamondᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → A ⟹ᵀ C →
           Σ (RTy _) (λ D → (B ⟹ᵀ D) × (C ⟹ᵀ D))
diamondᵀ {A = A} pu pv = (A ⁺ᵀ) , (⟹ᵀ-⁺ pu , ⟹ᵀ-⁺ pv)

infix 3 _⟹ᵀ*_
data _⟹ᵀ*_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  pdoneᵀ : {A : RTy Γ} → A ⟹ᵀ* A
  pstepᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → B ⟹ᵀ* C → A ⟹ᵀ* C

stripᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → A ⟹ᵀ* C →
         Σ (RTy _) (λ D → (B ⟹ᵀ* D) × (C ⟹ᵀ D))
stripᵀ pu pdoneᵀ = _ , (pdoneᵀ , pu)
stripᵀ pu (pstepᵀ pv pv*) with diamondᵀ pu pv
... | w₁ , (u⟹w₁ , v₁⟹w₁) with stripᵀ v₁⟹w₁ pv*
...   | w , (w₁⟹*w , v⟹w) = w , (pstepᵀ u⟹w₁ w₁⟹*w , v⟹w)

confluent⟹ᵀ : {A B C : RTy Γ} → A ⟹ᵀ* B → A ⟹ᵀ* C →
              Σ (RTy _) (λ D → (B ⟹ᵀ* D) × (C ⟹ᵀ* D))
confluent⟹ᵀ pdoneᵀ pv = _ , (pv , pdoneᵀ)
confluent⟹ᵀ (pstepᵀ pu pu*) pv with stripᵀ pu pv
... | w₁ , (u₁⟹*w₁ , v⟹w₁) with confluent⟹ᵀ pu* u₁⟹*w₁
...   | w , (u⟹*w , w₁⟹*w) = w , (u⟹*w , pstepᵀ v⟹w₁ w₁⟹*w)

⟶ᵀ*→⟹ᵀ* : {A B : RTy Γ} → A ⟶ᵀ* B → A ⟹ᵀ* B
⟶ᵀ*→⟹ᵀ* doneᵀ       = pdoneᵀ
⟶ᵀ*→⟹ᵀ* (stepᵀ r p) = pstepᵀ (⟶ᵀ→⟹ᵀ r) (⟶ᵀ*→⟹ᵀ* p)

⟹ᵀ*→⟶ᵀ* : {A B : RTy Γ} → A ⟹ᵀ* B → A ⟶ᵀ* B
⟹ᵀ*→⟶ᵀ* pdoneᵀ        = doneᵀ
⟹ᵀ*→⟶ᵀ* (pstepᵀ p ps) = ⟶ᵀ*-trans (⟹ᵀ→⟶ᵀ* p) (⟹ᵀ*→⟶ᵀ* ps)

confluentᵀ : {A B C : RTy Γ} → A ⟶ᵀ* B → A ⟶ᵀ* C →
             Σ (RTy _) (λ D → (B ⟶ᵀ* D) × (C ⟶ᵀ* D))
confluentᵀ p q with confluent⟹ᵀ (⟶ᵀ*→⟹ᵀ* p) (⟶ᵀ*→⟹ᵀ* q)
... | w , (uw , vw) = w , (⟹ᵀ*→⟶ᵀ* uw , ⟹ᵀ*→⟶ᵀ* vw)

church-rosserᵀ : {A B : RTy Γ} → A ≅ᵀ B → Σ (RTy _) (λ C → (A ⟶ᵀ* C) × (B ⟶ᵀ* C))
church-rosserᵀ (credᵀ r)   = _ , (stepᵀ r doneᵀ , doneᵀ)
church-rosserᵀ crflᵀ       = _ , (doneᵀ , doneᵀ)
church-rosserᵀ (csymᵀ c) with church-rosserᵀ c
... | w , (aw , bw) = w , (bw , aw)
church-rosserᵀ (ctrnᵀ c d) with church-rosserᵀ c | church-rosserᵀ d
... | w₁ , (aw₁ , mw₁) | w₂ , (mw₂ , bw₂) with confluentᵀ mw₁ mw₂
...   | w , (w₁w , w₂w) = w , (⟶ᵀ*-trans aw₁ w₁w , ⟶ᵀ*-trans bw₂ w₂w)

------------------------------------------------------------------------
-- Π-shape is preserved by reduction, and Π-INJECTIVITY of conversion.
------------------------------------------------------------------------

record ΠRed {Γ} (A : RTy Γ) (B : RTy (Γ ∙)) (C : RTy Γ) : Set where
  constructor mkΠRed
  field
    A'' : RTy Γ
    B'' : RTy (Γ ∙)
    eqC : C ≡ Π A'' B''
    rA  : A ⟶ᵀ* A''
    rB  : B ⟶ᵀ* B''

Π-reduct : {A : RTy Γ} {B : RTy (Γ ∙)} {C : RTy Γ} → Π A B ⟶ᵀ* C → ΠRed A B C
Π-reduct {A = A} {B} doneᵀ = mkΠRed A B refl doneᵀ doneᵀ
Π-reduct (stepᵀ (ξ-Πˡ r) rest) with Π-reduct rest
... | mkΠRed A'' B'' eqC rA rB = mkΠRed A'' B'' eqC (stepᵀ r rA) rB
Π-reduct (stepᵀ (ξ-Πʳ r) rest) with Π-reduct rest
... | mkΠRed A'' B'' eqC rA rB = mkΠRed A'' B'' eqC rA (stepᵀ r rB)


-- Π constructor is injective for `≡`.
Πinj≡ : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → Π A B ≡ Π A' B' → (A ≡ A') × (B ≡ B')
Πinj≡ refl = refl , refl

------------------------------------------------------------------------
-- ★ Mu-INJECTIVITY.  Cheaper than Π's: `Mu D` is INERT — no `_⟶ᵀ_` rule
--   has it as subject — so it is its own only reduct, and Church–Rosser
--   collapses immediately.
------------------------------------------------------------------------

Muinj≡ : {D D' : Desc} → Mu {Γ} D ≡ Mu D' → D ≡ D'
Muinj≡ refl = refl

IMuinj≡ : {D D' : IDesc} {I I' : RTy ε} {i i' : RTm Γ} →
          IMu {Γ} D I i ≡ IMu D' I' i' → (D ≡ D') × ((I ≡ I') × (i ≡ i'))
IMuinj≡ refl = (refl , (refl , refl))

Mu-reduct : {D : Desc} {C : RTy Γ} → Mu D ⟶ᵀ* C → C ≡ Mu D
Mu-reduct doneᵀ        = refl
Mu-reduct (stepᵀ () _)

Mu-inj : {D D' : Desc} → Mu {Γ} D ≅ᵀ Mu D' → D ≡ D'
Mu-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) = Muinj≡ (trans (sym (Mu-reduct r₁)) (Mu-reduct r₂))

-- ★ `IMu` is NOT inert, so `IMu-reduct` cannot be `Mu-reduct`'s `stepᵀ ()`.
--   Only `ξ-IMu` applies, so the SHAPE is preserved and the index reduces —
--   the `Π-reduct` pattern, with one moving part instead of two.
record IMuRed {Γ : Cx} (D : IDesc) (I : RTy ε) (i : RTm Γ) (C : RTy Γ) : Set where
  constructor mkIMuRed
  field
    idx   : RTm Γ
    eq    : C ≡ IMu D I idx
    ridx  : i ⟶* idx

IMu-reduct : {D : IDesc} {I : RTy ε} {i : RTm Γ} {C : RTy Γ} →
             IMu D I i ⟶ᵀ* C → IMuRed D I i C
IMu-reduct doneᵀ = mkIMuRed _ refl done
IMu-reduct (stepᵀ (ξ-IMu r) p) with IMu-reduct p
... | mkIMuRed j eq rj = mkIMuRed j eq (step r rj)

-- ⚠ the index is only ≅, not ≡ — it is a TERM and it reduces.  That is the
--   whole difference from `Mu-inj`, and it is why `⊢ielim` can retype its
--   scrutinee across `ξ-ielimⁱ`.
IMu-inj : {D D' : IDesc} {I I' : RTy ε} {i i' : RTm Γ} →
          IMu {Γ} D I i ≅ᵀ IMu D' I' i' →
          (D ≡ D') × ((I ≡ I') × (i ≅ i'))
IMu-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with IMu-reduct r₁ | IMu-reduct r₂
...   | mkIMuRed j₁ eq₁ rj₁ | mkIMuRed j₂ eq₂ rj₂ with IMuinj≡ (trans (sym eq₁) eq₂)
...     | (eqD , (eqI , eqj)) =
          (eqD , (eqI , ctrn (hom→≅ rj₁)
                             (csym (hom→≅ (subst (_ ⟶*_) (sym eqj) rj₂)))))

-- ★ Π-INJECTIVITY OF CONVERSION — dHoTT-24's scoped ceiling, discharged.
Π-inj : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} →
        Π A B ≅ᵀ Π A' B' → (A ≅ᵀ A') × (B ≅ᵀ B')
Π-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with Π-reduct r₁ | Π-reduct r₂
...   | mkΠRed A₁ B₁ eq₁ rA₁ rB₁ | mkΠRed A₂ B₂ eq₂ rA₂ rB₂
        with Πinj≡ (trans (sym eq₁) eq₂)
...       | (eqA , eqB) =
            ctrnᵀ (red→≅ᵀ rA₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqA) rA₂)))
          , ctrnᵀ (red→≅ᵀ rB₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqB) rB₂)))

------------------------------------------------------------------------
-- Σ-injectivity (mirrors Π-injectivity) — for `⊢fst`/`⊢snd` inversion (A1).
------------------------------------------------------------------------

record ΣRed {Γ} (A : RTy Γ) (B : RTy (Γ ∙)) (C : RTy Γ) : Set where
  constructor mkΣRed
  field
    A'' : RTy Γ
    B'' : RTy (Γ ∙)
    eqC : C ≡ Σ' A'' B''
    rA  : A ⟶ᵀ* A''
    rB  : B ⟶ᵀ* B''

Σ-reduct : {A : RTy Γ} {B : RTy (Γ ∙)} {C : RTy Γ} → Σ' A B ⟶ᵀ* C → ΣRed A B C
Σ-reduct {A = A} {B} doneᵀ = mkΣRed A B refl doneᵀ doneᵀ
Σ-reduct (stepᵀ (ξ-Σˡ r) rest) with Σ-reduct rest
... | mkΣRed A'' B'' eqC rA rB = mkΣRed A'' B'' eqC (stepᵀ r rA) rB
Σ-reduct (stepᵀ (ξ-Σʳ r) rest) with Σ-reduct rest
... | mkΣRed A'' B'' eqC rA rB = mkΣRed A'' B'' eqC rA (stepᵀ r rB)

Σinj≡ : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → Σ' A B ≡ Σ' A' B' → (A ≡ A') × (B ≡ B')
Σinj≡ refl = refl , refl

Σ-inj : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} →
        Σ' A B ≅ᵀ Σ' A' B' → (A ≅ᵀ A') × (B ≅ᵀ B')
Σ-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with Σ-reduct r₁ | Σ-reduct r₂
...   | mkΣRed A₁ B₁ eq₁ rA₁ rB₁ | mkΣRed A₂ B₂ eq₂ rA₂ rB₂
        with Σinj≡ (trans (sym eq₁) eq₂)
...       | (eqA , eqB) =
            ctrnᵀ (red→≅ᵀ rA₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqA) rA₂)))
          , ctrnᵀ (red→≅ᵀ rB₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqB) rB₂)))
