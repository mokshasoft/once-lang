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
  using ( _≡_; refl; sym; trans; subst; Σ; _,_; _×_ ; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; base; U; Π; Σ'; El; Hom; RTm; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub; var; lam; app; pair
        ; fst; snd; absurd; ordtr; vz; vs; renTm; Unit; Nat; unit; nzero; nsuc
        ; natrec; ⌜Nat⌝; ⌜Unit⌝; Desc; con; IMu; ielim; ⌜IMu⌝; εwkTm; Fin
        ; ⌜Fin⌝; DIh; dι; dσ; dρ; renTy; extR; extS; Ren; cong₄; Sub; subTy
        ; subTm; dpay; dih; fzero; fsuc; fcase; fcase0; psplit )
open import DirectedHoTT.Spec.Typing
  using ( _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ
        ; ξ-Σʳ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; El-⌜Id⌝; ξ-Idᵀ; ξ-Idˡ
        ; ξ-Idʳ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; Hom-Nat-z; Hom-Nat-sz
        ; Hom-Nat-ss; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜IMu⌝; ξ-idreflᶜ; ξ-idreflᵃ
        ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; _⟶*_; done; step; _≅ᵀ_; credᵀ; crflᵀ
        ; csymᵀ; ctrnᵀ; _≅_; cred; crfl; csym; ctrn; hom→≅; iinst; El-⌜Fin⌝
        ; DIh-ι; DIh-σ; DIh-ρ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-DIhᴰ; ξ-DIhᴹ
        ; ξ-DIhᶜ; ξ-DIhᵖ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι; dih-σ; dih-ρ
        ; fcase-z; fcase-s; psplit-β; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-con
        ; ξ-ielimᴰ; ξ-ielimⁱ; ξ-ielimᵉ; ξ-ielimᵗ; ξ-dι; ξ-dσˢ; ξ-dσᶠ; ξ-dρʲ
        ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dpayⁱ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ
        ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ
        ; ξ-psplitᵍ; tr-J-IMu; tr-J-Fin; single )
open import DirectedHoTT.Metatheory.Confluence
  using ( _⟹_; pvar; plam; papp; pβ; ppair; pabsurd; pfst; psnd; pβfst; pβsnd
        ; p⌜base⌝; p⌜Π⌝; p⌜Σ⌝; p⌜Hom⌝; phrefl; ptr; ptr-J-base; ptr-J-Σ
        ; ptr-taut; phrefl-pw; ptr-J-Hom; ptr-pw; pap; pap-J; p⌜Id⌝; pidrefl
        ; pjsub; pjsub-refl; ptr-J-Id; punit; pnzero; pnsuc; pnatrec
        ; pnatrec-zero; pnatrec-suc; p⌜Nat⌝; p⌜Unit⌝; ptr-J-Unit; ptr-J-IMu
        ; pordtr; pordtr-z; pordtr-szz; pordtr-ssz; pordtr-szs; pordtr-sss; _⁺
        ; ⟹-refl; ⟹-⁺; ⟶→⟹; ⟹→⟶*; ⟹-ren; pcon; pι; p⌜IMu⌝; pielim; ⟹-sub
        ; ⟹-exts; pdι; pdσ; pdρ; pdpay; pdpay-ι; pdpay-σ; pdpay-ρ; pdih
        ; pdih-ι; pdih-σ; pdih-ρ; pfzero; pfsuc; pfcase; pfcase-z; pfcase-s
        ; pfcase0; ppsplit; ppsplit-β; ptr-J-Fin; p⌜Fin⌝; single2-⟹; single-⟹ )

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
-- the levitated `DIh-ρ` rule's type-level development needs typing-free
--   renaming/substitution facts about `iinst`/`wk2`.
open import DirectedHoTT.Metatheory.TySub
  using ( ⟶ᵀ*-sub'; iinst-mono; iinst-monoˢ; ⟶ᵀ*-ren; iinst-ren; wk2-renTy )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( iinst-sub; wk2-subTy; wk-sub )











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
-- Parallel type reduction; reuses the TERM triangle at `El` leaves.
------------------------------------------------------------------------

infix 3 _⟹ᵀ_
data _⟹ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  pbase : base {Γ} ⟹ᵀ base
  pU    : U {Γ} ⟹ᵀ U
  -- ★ WF stage A: Unit/Nat are INERT type formers — nullary congruences.
  pUnit : Unit {Γ} ⟹ᵀ Unit
  pNat  : Nat {Γ} ⟹ᵀ Nat
  pEl   : {t t' : RTm Γ} → t ⟹ t' → El t ⟹ᵀ El t'
  pΠ    : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → A ⟹ᵀ A' → B ⟹ᵀ B' → Π A B ⟹ᵀ Π A' B'
  pΣ    : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → A ⟹ᵀ A' → B ⟹ᵀ B' → Σ' A B ⟹ᵀ Σ' A' B'
  pEl-⌜base⌝ : El (⌜base⌝ {Γ}) ⟹ᵀ base
  pEl-⌜Π⌝ : {c c' : RTm Γ} {d d' : RTm (Γ ∙)} →
            c ⟹ c' → d ⟹ d' → El (⌜Π⌝ c d) ⟹ᵀ Π (El c') (El d')
  pEl-⌜Σ⌝ : {c c' : RTm Γ} {d d' : RTm (Γ ∙)} →
            c ⟹ c' → d ⟹ d' → El (⌜Σ⌝ c d) ⟹ᵀ Σ' (El c') (El d')
  pEl-⌜Hom⌝ : {c c' a a' b b' : RTm Γ} →
              c ⟹ c' → a ⟹ a' → b ⟹ b' →
              El (⌜Hom⌝ c a b) ⟹ᵀ Hom (El c') a' b'
  -- W2: `Hom` congruence, and its two unfoldings (`SpikeHomTy` promoted).
  pHom : {A A' : RTy Γ} {t t' u u' : RTm Γ} →
         A ⟹ᵀ A' → t ⟹ t' → u ⟹ u' → Hom A t u ⟹ᵀ Hom A' t' u'
  pHom-U : {c c' d d' : RTm Γ} →
           c ⟹ c' → d ⟹ d' → Hom U c d ⟹ᵀ Π (El c') (El (renTm vs d'))
  -- ★★ WF stage B: THE COMPUTING ORDER, as parallel steps.  Unlike
  -- `pHom-U`/`pHom-Π` these are keyed on the ENDPOINTS, so the
  -- development `_⁺ᵀ` dispatches on the endpoints' numeral heads.
  pHom-Nat-z  : {n n' : RTm Γ} → n ⟹ n' → Hom Nat nzero n ⟹ᵀ Unit
  pHom-Nat-sz : {m m' : RTm Γ} → m ⟹ m' → Hom Nat (nsuc m) nzero ⟹ᵀ base
  pHom-Nat-ss : {m m' n n' : RTm Γ} → m ⟹ m' → n ⟹ n' →
                Hom Nat (nsuc m) (nsuc n) ⟹ᵀ Hom Nat m' n'
  pHom-Π : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} {f f' g g' : RTm Γ} →
           A ⟹ᵀ A' → B ⟹ᵀ B' → f ⟹ f' → g ⟹ g' →
           Hom (Π A B) f g ⟹ᵀ
           Π A' (Hom B' (app (renTm vs f') (var vz)) (app (renTm vs g') (var vz)))
  -- the two-former kernel: `Id` is INERT — congruence + decode only.
  pId : {A A' : RTy Γ} {t t' u u' : RTm Γ} →
        A ⟹ᵀ A' → t ⟹ t' → u ⟹ u' → Id A t u ⟹ᵀ Id A' t' u'
  pEl-⌜Nat⌝  : El (⌜Nat⌝ {Γ}) ⟹ᵀ Nat
  pEl-⌜Unit⌝ : El (⌜Unit⌝ {Γ}) ⟹ᵀ Unit
  -- ★★ LEVITATED FAMILIES.  `IMu`/`Desc` carry terms (congruences); `DIh`
  --   computes on its telescope head, the three parallel roots.
  pIMu      : {I I' D D' i i' : RTm Γ} → I ⟹ I' → D ⟹ D' → i ⟹ i' →
              IMu I D i ⟹ᵀ IMu I' D' i'
  pEl-⌜IMu⌝ : {I I' D D' i i' : RTm Γ} → I ⟹ I' → D ⟹ D' → i ⟹ i' →
              El (⌜IMu⌝ I D i) ⟹ᵀ IMu I' D' i'
  pDesc     : {I I' : RTm Γ} → I ⟹ I' → Desc I ⟹ᵀ Desc I'
  pFin      : {n : ℕ} → Fin {Γ} n ⟹ᵀ Fin n
  pEl-⌜Fin⌝ : {n : ℕ} → El (⌜Fin⌝ {Γ} n) ⟹ᵀ Fin n
  pDIh      : {D D' C C' p p' : RTm Γ} {M M' : RTy ((Γ ∙) ∙)} →
              D ⟹ D' → M ⟹ᵀ M' → C ⟹ C' → p ⟹ p' → DIh D M C p ⟹ᵀ DIh D' M' C' p'
  pDIh-ι    : {D j p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → DIh D M (dι j) p ⟹ᵀ Unit
  pDIh-σ    : {D D' S f f' p p' : RTm Γ} {M M' : RTy ((Γ ∙) ∙)} →
              D ⟹ D' → M ⟹ᵀ M' → f ⟹ f' → p ⟹ p' →
              DIh D M (dσ S f) p ⟹ᵀ DIh D' M' (app f' (fst p')) (snd p')
  pDIh-ρ    : {D D' j j' C C' p p' : RTm Γ} {M M' : RTy ((Γ ∙) ∙)} →
              D ⟹ D' → M ⟹ᵀ M' → j ⟹ j' → C ⟹ C' → p ⟹ p' →
              DIh D M (dρ j C) p ⟹ᵀ
              Σ' (iinst j' (fst p') M')
                 (DIh (renTm vs D') (renTy (extR (extR vs)) M') (renTm vs C') (snd (renTm vs p')))
  pEl-⌜Id⌝ : {c c' a a' b b' : RTm Γ} →
             c ⟹ c' → a ⟹ a' → b ⟹ b' →
             El (⌜Id⌝ c a b) ⟹ᵀ Id (El c') a' b'

⟹ᵀ-refl : (A : RTy Γ) → A ⟹ᵀ A
⟹ᵀ-refl base     = pbase
⟹ᵀ-refl Unit     = pUnit
⟹ᵀ-refl Nat      = pNat
⟹ᵀ-refl (El t)   = pEl (⟹-refl t)
⟹ᵀ-refl (IMu I D i) = pIMu (⟹-refl I) (⟹-refl D) (⟹-refl i)
⟹ᵀ-refl (Desc I) = pDesc (⟹-refl I)
⟹ᵀ-refl (Fin n) = pFin
⟹ᵀ-refl (DIh D M C p) = pDIh (⟹-refl D) (⟹ᵀ-refl M) (⟹-refl C) (⟹-refl p)
⟹ᵀ-refl U        = pU
⟹ᵀ-refl (Π A B)  = pΠ (⟹ᵀ-refl A) (⟹ᵀ-refl B)
⟹ᵀ-refl (Id A t u) = pId (⟹ᵀ-refl A) (⟹-refl t) (⟹-refl u)
⟹ᵀ-refl (Σ' A B) = pΣ (⟹ᵀ-refl A) (⟹ᵀ-refl B)
⟹ᵀ-refl (Hom A t u) = pHom (⟹ᵀ-refl A) (⟹-refl t) (⟹-refl u)

⟶ᵀ→⟹ᵀ : {A B : RTy Γ} → A ⟶ᵀ B → A ⟹ᵀ B
⟶ᵀ→⟹ᵀ (Hom-Nat-z n)    = pHom-Nat-z (⟹-refl n)
⟶ᵀ→⟹ᵀ (Hom-Nat-sz m)   = pHom-Nat-sz (⟹-refl m)
⟶ᵀ→⟹ᵀ (Hom-Nat-ss m n) = pHom-Nat-ss (⟹-refl m) (⟹-refl n)
⟶ᵀ→⟹ᵀ El-⌜Nat⌝     = pEl-⌜Nat⌝
⟶ᵀ→⟹ᵀ El-⌜Unit⌝    = pEl-⌜Unit⌝
⟶ᵀ→⟹ᵀ El-⌜base⌝    = pEl-⌜base⌝
⟶ᵀ→⟹ᵀ El-⌜IMu⌝     = pEl-⌜IMu⌝ (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶ᵀ→⟹ᵀ El-⌜Fin⌝     = pEl-⌜Fin⌝
⟶ᵀ→⟹ᵀ (DIh-ι D M j p) = pDIh-ι
⟶ᵀ→⟹ᵀ (DIh-σ D M S f p) = pDIh-σ (⟹-refl D) (⟹ᵀ-refl M) (⟹-refl f) (⟹-refl p)
⟶ᵀ→⟹ᵀ (DIh-ρ D M j C p) = pDIh-ρ (⟹-refl D) (⟹ᵀ-refl M) (⟹-refl j) (⟹-refl C) (⟹-refl p)
⟶ᵀ→⟹ᵀ (ξ-IMuᴵ r) = pIMu (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-IMuᴰ r) = pIMu (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-IMuⁱ r) = pIMu (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶ᵀ→⟹ᵀ (ξ-Desc r) = pDesc (⟶→⟹ r)
⟶ᵀ→⟹ᵀ (ξ-DIhᴰ r) = pDIh (⟶→⟹ r) (⟹ᵀ-refl _) (⟹-refl _) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-DIhᴹ r) = pDIh (⟹-refl _) (⟶ᵀ→⟹ᵀ r) (⟹-refl _) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-DIhᶜ r) = pDIh (⟹-refl _) (⟹ᵀ-refl _) (⟶→⟹ r) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-DIhᵖ r) = pDIh (⟹-refl _) (⟹ᵀ-refl _) (⟹-refl _) (⟶→⟹ r)
⟶ᵀ→⟹ᵀ (El-⌜Π⌝ c d) = pEl-⌜Π⌝ (⟹-refl c) (⟹-refl d)
⟶ᵀ→⟹ᵀ (El-⌜Σ⌝ c d) = pEl-⌜Σ⌝ (⟹-refl c) (⟹-refl d)
⟶ᵀ→⟹ᵀ (El-⌜Hom⌝ c a b) = pEl-⌜Hom⌝ (⟹-refl c) (⟹-refl a) (⟹-refl b)
⟶ᵀ→⟹ᵀ (ξ-El r) = pEl (⟶→⟹ r)
⟶ᵀ→⟹ᵀ (ξ-Πˡ r) = pΠ (⟶ᵀ→⟹ᵀ r) (⟹ᵀ-refl _)
⟶ᵀ→⟹ᵀ (ξ-Πʳ r) = pΠ (⟹ᵀ-refl _) (⟶ᵀ→⟹ᵀ r)
⟶ᵀ→⟹ᵀ (ξ-Σˡ r) = pΣ (⟶ᵀ→⟹ᵀ r) (⟹ᵀ-refl _)
⟶ᵀ→⟹ᵀ (ξ-Σʳ r) = pΣ (⟹ᵀ-refl _) (⟶ᵀ→⟹ᵀ r)
⟶ᵀ→⟹ᵀ (Hom-U c d)     = pHom-U (⟹-refl c) (⟹-refl d)
⟶ᵀ→⟹ᵀ (Hom-Π A B f g) =
  pHom-Π (⟹ᵀ-refl A) (⟹ᵀ-refl B) (⟹-refl f) (⟹-refl g)
⟶ᵀ→⟹ᵀ (ξ-Homᵀ r) = pHom (⟶ᵀ→⟹ᵀ r) (⟹-refl _) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-Homˡ r) = pHom (⟹ᵀ-refl _) (⟶→⟹ r) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-Homʳ r) = pHom (⟹ᵀ-refl _) (⟹-refl _) (⟶→⟹ r)
⟶ᵀ→⟹ᵀ (El-⌜Id⌝ c a b) = pEl-⌜Id⌝ (⟹-refl c) (⟹-refl a) (⟹-refl b)
⟶ᵀ→⟹ᵀ (ξ-Idᵀ r) = pId (⟶ᵀ→⟹ᵀ r) (⟹-refl _) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-Idˡ r) = pId (⟹ᵀ-refl _) (⟶→⟹ r) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-Idʳ r) = pId (⟹ᵀ-refl _) (⟹-refl _) (⟶→⟹ r)

⟹ᵀ→⟶ᵀ* : {A B : RTy Γ} → A ⟹ᵀ B → A ⟶ᵀ* B
⟹ᵀ→⟶ᵀ* pEl-⌜Nat⌝  = stepᵀ El-⌜Nat⌝ doneᵀ
⟹ᵀ→⟶ᵀ* pEl-⌜Unit⌝ = stepᵀ El-⌜Unit⌝ doneᵀ
⟹ᵀ→⟶ᵀ* pbase    = doneᵀ
⟹ᵀ→⟶ᵀ* pUnit    = doneᵀ
⟹ᵀ→⟶ᵀ* pNat     = doneᵀ
⟹ᵀ→⟶ᵀ* pU       = doneᵀ
⟹ᵀ→⟶ᵀ* (pIMu a b c) =
  ⟶ᵀ*-trans (⟶ᵀ*-IMuᴵ (⟹→⟶* a)) (⟶ᵀ*-trans (⟶ᵀ*-IMuᴰ (⟹→⟶* b)) (⟶ᵀ*-IMu (⟹→⟶* c)))
⟹ᵀ→⟶ᵀ* (pEl-⌜IMu⌝ a b c) =
  stepᵀ El-⌜IMu⌝ (⟶ᵀ*-trans (⟶ᵀ*-IMuᴵ (⟹→⟶* a)) (⟶ᵀ*-trans (⟶ᵀ*-IMuᴰ (⟹→⟶* b)) (⟶ᵀ*-IMu (⟹→⟶* c))))
⟹ᵀ→⟶ᵀ* (pDesc a) = ⟶ᵀ*-Desc (⟹→⟶* a)
⟹ᵀ→⟶ᵀ* pFin = doneᵀ
⟹ᵀ→⟶ᵀ* pEl-⌜Fin⌝ = stepᵀ El-⌜Fin⌝ doneᵀ
⟹ᵀ→⟶ᵀ* (pDIh a m c d) =
  ⟶ᵀ*-trans (⟶ᵀ*-DIhᴰ (⟹→⟶* a)) (⟶ᵀ*-trans (⟶ᵀ*-DIhᴹ (⟹ᵀ→⟶ᵀ* m))
    (⟶ᵀ*-trans (⟶ᵀ*-DIhᶜ (⟹→⟶* c)) (⟶ᵀ*-DIhᵖ (⟹→⟶* d))))
⟹ᵀ→⟶ᵀ* (pDIh-ι {D = D} {j = j} {p = p} {M = M}) = stepᵀ (DIh-ι D M j p) doneᵀ
⟹ᵀ→⟶ᵀ* (pDIh-σ {D = D} {S = S} {f = f} {p = p} {M = M} a m c d) =
  stepᵀ (DIh-σ D M S f p)
    (⟶ᵀ*-trans (⟶ᵀ*-DIhᴰ (⟹→⟶* a)) (⟶ᵀ*-trans (⟶ᵀ*-DIhᴹ (⟹ᵀ→⟶ᵀ* m))
      (⟶ᵀ*-trans (⟶ᵀ*-DIhᶜ (⟶*-trans (⟶*-appˡ (⟹→⟶* c)) (⟶*-appʳ (⟶*-fst (⟹→⟶* d)))))
                 (⟶ᵀ*-DIhᵖ (⟶*-snd (⟹→⟶* d))))))
⟹ᵀ→⟶ᵀ* (pDIh-ρ {D = D} {j = j} {j'} {C = C} {p = p} {p'} {M = M} {M'} a m b c d) =
  stepᵀ (DIh-ρ D M j C p)
    (⟶ᵀ*-trans
      (⟶ᵀ*-Σˡ (⟶ᵀ*-trans (⟶ᵀ*-sub' (single (fst p)) (⟶ᵀ*-sub' (extS (single j)) (⟹ᵀ→⟶ᵀ* m)))
                (⟶ᵀ*-trans (iinst-mono M' (fst p) (⟹→⟶* b)) (iinst-monoˢ M' j' (⟶*-fst (⟹→⟶* d))))))
      (⟶ᵀ*-Σʳ (⟶ᵀ*-trans (⟶ᵀ*-DIhᴰ (⟶*-ren vs (⟹→⟶* a)))
                (⟶ᵀ*-trans (⟶ᵀ*-DIhᴹ (⟶ᵀ*-ren (extR (extR vs)) (⟹ᵀ→⟶ᵀ* m)))
                  (⟶ᵀ*-trans (⟶ᵀ*-DIhᶜ (⟶*-ren vs (⟹→⟶* c)))
                             (⟶ᵀ*-DIhᵖ (⟶*-snd (⟶*-ren vs (⟹→⟶* d)))))))))
⟹ᵀ→⟶ᵀ* (pEl p)  = ⟶ᵀ*-El (⟹→⟶* p)
⟹ᵀ→⟶ᵀ* (pΠ p q) = ⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟹ᵀ→⟶ᵀ* p)) (⟶ᵀ*-Πʳ (⟹ᵀ→⟶ᵀ* q))
⟹ᵀ→⟶ᵀ* (pΣ p q) = ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (⟹ᵀ→⟶ᵀ* p)) (⟶ᵀ*-Σʳ (⟹ᵀ→⟶ᵀ* q))
⟹ᵀ→⟶ᵀ* pEl-⌜base⌝ = stepᵀ El-⌜base⌝ doneᵀ
⟹ᵀ→⟶ᵀ* (pEl-⌜Π⌝ {c = c} {d = d} p q) =
  stepᵀ (El-⌜Π⌝ c d)
    (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟶ᵀ*-El (⟹→⟶* p))) (⟶ᵀ*-Πʳ (⟶ᵀ*-El (⟹→⟶* q))))
⟹ᵀ→⟶ᵀ* (pEl-⌜Σ⌝ {c = c} {d = d} p q) =
  stepᵀ (El-⌜Σ⌝ c d)
    (⟶ᵀ*-trans (⟶ᵀ*-Σˡ (⟶ᵀ*-El (⟹→⟶* p))) (⟶ᵀ*-Σʳ (⟶ᵀ*-El (⟹→⟶* q))))
⟹ᵀ→⟶ᵀ* (pEl-⌜Hom⌝ {c = c} {c'} {a} {a'} {b} {b'} p q r) =
  stepᵀ (El-⌜Hom⌝ c a b)
    (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (⟶ᵀ*-El (⟹→⟶* p)))
               (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟹→⟶* q)) (⟶ᵀ*-Homʳ (⟹→⟶* r))))
⟹ᵀ→⟶ᵀ* (pEl-⌜Id⌝ {c = c} {c'} {a} {a'} {b} {b'} p q r) =
  stepᵀ (El-⌜Id⌝ c a b)
    (⟶ᵀ*-trans (⟶ᵀ*-Idᵀ (⟶ᵀ*-El (⟹→⟶* p)))
               (⟶ᵀ*-trans (⟶ᵀ*-Idˡ (⟹→⟶* q)) (⟶ᵀ*-Idʳ (⟹→⟶* r))))
⟹ᵀ→⟶ᵀ* (pId p q r) =
  ⟶ᵀ*-trans (⟶ᵀ*-Idᵀ (⟹ᵀ→⟶ᵀ* p))
    (⟶ᵀ*-trans (⟶ᵀ*-Idˡ (⟹→⟶* q)) (⟶ᵀ*-Idʳ (⟹→⟶* r)))
⟹ᵀ→⟶ᵀ* (pHom p q r) =
  ⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (⟹ᵀ→⟶ᵀ* p))
    (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟹→⟶* q)) (⟶ᵀ*-Homʳ (⟹→⟶* r)))
⟹ᵀ→⟶ᵀ* (pHom-Nat-z {n = n} p)    = stepᵀ (Hom-Nat-z n) doneᵀ
⟹ᵀ→⟶ᵀ* (pHom-Nat-sz {m = m} p)   = stepᵀ (Hom-Nat-sz m) doneᵀ
⟹ᵀ→⟶ᵀ* (pHom-Nat-ss {m = m} {n = n} p q) =
  stepᵀ (Hom-Nat-ss m n)
    (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟹→⟶* p)) (⟶ᵀ*-Homʳ (⟹→⟶* q)))
⟹ᵀ→⟶ᵀ* (pHom-U {c = c} {d = d} p q) =
  stepᵀ (Hom-U c d)
    (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟶ᵀ*-El (⟹→⟶* p)))
               (⟶ᵀ*-Πʳ (⟶ᵀ*-El (⟶*-ren vs (⟹→⟶* q)))))
⟹ᵀ→⟶ᵀ* (pHom-Π {A = A} {B = B} {f = f} {g = g} pA pB pf pg) =
  stepᵀ (Hom-Π A B f g)
    (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟹ᵀ→⟶ᵀ* pA))
      (⟶ᵀ*-Πʳ (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (⟹ᵀ→⟶ᵀ* pB))
        (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pf))))
                   (⟶ᵀ*-Homʳ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pg))))))))

------------------------------------------------------------------------
-- ★ LEVITATION: parallel type reduction is stable under renaming and
--   (pointwise-parallel) substitution — `DIh-ρ`'s triangle case needs it.
------------------------------------------------------------------------

⟹ᵀ-ren : {Δ : Cx} (ρ : Ren Γ Δ) {A B : RTy Γ} → A ⟹ᵀ B → renTy ρ A ⟹ᵀ renTy ρ B
⟹ᵀ-ren ρ pbase = pbase
⟹ᵀ-ren ρ pU = pU
⟹ᵀ-ren ρ pUnit = pUnit
⟹ᵀ-ren ρ pNat = pNat
⟹ᵀ-ren ρ pFin = pFin
⟹ᵀ-ren ρ (pEl a) = pEl (⟹-ren ρ a)
⟹ᵀ-ren ρ (pΠ a b) = pΠ (⟹ᵀ-ren ρ a) (⟹ᵀ-ren (extR ρ) b)
⟹ᵀ-ren ρ (pΣ a b) = pΣ (⟹ᵀ-ren ρ a) (⟹ᵀ-ren (extR ρ) b)
⟹ᵀ-ren ρ pEl-⌜base⌝ = pEl-⌜base⌝
⟹ᵀ-ren ρ (pEl-⌜Π⌝ a b) = pEl-⌜Π⌝ (⟹-ren ρ a) (⟹-ren (extR ρ) b)
⟹ᵀ-ren ρ (pEl-⌜Σ⌝ a b) = pEl-⌜Σ⌝ (⟹-ren ρ a) (⟹-ren (extR ρ) b)
⟹ᵀ-ren ρ (pEl-⌜Hom⌝ a b c) = pEl-⌜Hom⌝ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)
⟹ᵀ-ren ρ (pHom a b c) = pHom (⟹ᵀ-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)
⟹ᵀ-ren ρ (pHom-U {c = c} {c'} {d = d} {d'} a b) =
  subst (λ z → renTy ρ (Hom U c d) ⟹ᵀ Π (El (renTm ρ c')) (El z)) (sym (wk-ren ρ d'))
        (pHom-U (⟹-ren ρ a) (⟹-ren ρ b))
⟹ᵀ-ren ρ (pHom-Nat-z a) = pHom-Nat-z (⟹-ren ρ a)
⟹ᵀ-ren ρ (pHom-Nat-sz a) = pHom-Nat-sz (⟹-ren ρ a)
⟹ᵀ-ren ρ (pHom-Nat-ss a b) = pHom-Nat-ss (⟹-ren ρ a) (⟹-ren ρ b)
⟹ᵀ-ren ρ (pHom-Π {A = A} {A'} {B = B} {B'} {f = f} {f'} {g = g} {g'} a b c d) =
  subst (λ Z → renTy ρ (Hom (Π A B) f g) ⟹ᵀ Z)
        (cong₂ (λ x y → Π (renTy ρ A')
                         (Hom (renTy (extR ρ) B') (app x (var vz)) (app y (var vz))))
               (sym (wk-ren ρ f')) (sym (wk-ren ρ g')))
        (pHom-Π (⟹ᵀ-ren ρ a) (⟹ᵀ-ren (extR ρ) b) (⟹-ren ρ c) (⟹-ren ρ d))
⟹ᵀ-ren ρ (pId a b c) = pId (⟹ᵀ-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)
⟹ᵀ-ren ρ pEl-⌜Nat⌝ = pEl-⌜Nat⌝
⟹ᵀ-ren ρ pEl-⌜Unit⌝ = pEl-⌜Unit⌝
⟹ᵀ-ren ρ (pIMu a b c) = pIMu (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)
⟹ᵀ-ren ρ (pEl-⌜IMu⌝ a b c) = pEl-⌜IMu⌝ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)
⟹ᵀ-ren ρ (pDesc a) = pDesc (⟹-ren ρ a)
⟹ᵀ-ren ρ pEl-⌜Fin⌝ = pEl-⌜Fin⌝
⟹ᵀ-ren ρ (pDIh a m c d) = pDIh (⟹-ren ρ a) (⟹ᵀ-ren (extR (extR ρ)) m) (⟹-ren ρ c) (⟹-ren ρ d)
⟹ᵀ-ren ρ pDIh-ι = pDIh-ι
⟹ᵀ-ren ρ (pDIh-σ a m c d) = pDIh-σ (⟹-ren ρ a) (⟹ᵀ-ren (extR (extR ρ)) m) (⟹-ren ρ c) (⟹-ren ρ d)
⟹ᵀ-ren ρ (pDIh-ρ {D = D} {D'} {j = j} {j'} {C = C} {C'} {p = p} {p'} {M = M} {M'} a m b c d) =
  subst (λ Z → renTy ρ (DIh D M (dρ j C) p) ⟹ᵀ Z)
        (sym (cong₂ Σ' (iinst-ren ρ M' j' (fst p'))
                        (cong₄ (λ w x y z → DIh w x y (snd z)) (wk-ren ρ D') (wk2-renTy ρ M') (wk-ren ρ C') (wk-ren ρ p'))))
        (pDIh-ρ (⟹-ren ρ a) (⟹ᵀ-ren (extR (extR ρ)) m) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d))
⟹ᵀ-ren ρ (pEl-⌜Id⌝ a b c) = pEl-⌜Id⌝ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)

⟹ᵀ-sub : {Δ : Cx} {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟹ σ' x) →
         {A B : RTy Γ} → A ⟹ᵀ B → subTy σ A ⟹ᵀ subTy σ' B
⟹ᵀ-sub h pbase = pbase
⟹ᵀ-sub h pU = pU
⟹ᵀ-sub h pUnit = pUnit
⟹ᵀ-sub h pNat = pNat
⟹ᵀ-sub h pFin = pFin
⟹ᵀ-sub h (pEl a) = pEl (⟹-sub h a)
⟹ᵀ-sub h (pΠ a b) = pΠ (⟹ᵀ-sub h a) (⟹ᵀ-sub (⟹-exts h) b)
⟹ᵀ-sub h (pΣ a b) = pΣ (⟹ᵀ-sub h a) (⟹ᵀ-sub (⟹-exts h) b)
⟹ᵀ-sub h pEl-⌜base⌝ = pEl-⌜base⌝
⟹ᵀ-sub h (pEl-⌜Π⌝ a b) = pEl-⌜Π⌝ (⟹-sub h a) (⟹-sub (⟹-exts h) b)
⟹ᵀ-sub h (pEl-⌜Σ⌝ a b) = pEl-⌜Σ⌝ (⟹-sub h a) (⟹-sub (⟹-exts h) b)
⟹ᵀ-sub h (pEl-⌜Hom⌝ a b c) = pEl-⌜Hom⌝ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c)
⟹ᵀ-sub h (pHom a b c) = pHom (⟹ᵀ-sub h a) (⟹-sub h b) (⟹-sub h c)
⟹ᵀ-sub {σ = σ} {σ'} h (pHom-U {c = c} {c'} {d = d} {d'} a b) =
  subst (λ z → subTy σ (Hom U c d) ⟹ᵀ Π (El (subTm σ' c')) (El z)) (sym (wk-sub σ' d'))
        (pHom-U (⟹-sub h a) (⟹-sub h b))
⟹ᵀ-sub h (pHom-Nat-z a) = pHom-Nat-z (⟹-sub h a)
⟹ᵀ-sub h (pHom-Nat-sz a) = pHom-Nat-sz (⟹-sub h a)
⟹ᵀ-sub h (pHom-Nat-ss a b) = pHom-Nat-ss (⟹-sub h a) (⟹-sub h b)
⟹ᵀ-sub {σ = σ} {σ'} h (pHom-Π {A = A} {A'} {B = B} {B'} {f = f} {f'} {g = g} {g'} a b c d) =
  subst (λ Z → subTy σ (Hom (Π A B) f g) ⟹ᵀ Z)
        (cong₂ (λ x y → Π (subTy σ' A')
                         (Hom (subTy (extS σ') B') (app x (var vz)) (app y (var vz))))
               (sym (wk-sub σ' f')) (sym (wk-sub σ' g')))
        (pHom-Π (⟹ᵀ-sub h a) (⟹ᵀ-sub (⟹-exts h) b) (⟹-sub h c) (⟹-sub h d))
⟹ᵀ-sub h (pId a b c) = pId (⟹ᵀ-sub h a) (⟹-sub h b) (⟹-sub h c)
⟹ᵀ-sub h pEl-⌜Nat⌝ = pEl-⌜Nat⌝
⟹ᵀ-sub h pEl-⌜Unit⌝ = pEl-⌜Unit⌝
⟹ᵀ-sub h (pIMu a b c) = pIMu (⟹-sub h a) (⟹-sub h b) (⟹-sub h c)
⟹ᵀ-sub h (pEl-⌜IMu⌝ a b c) = pEl-⌜IMu⌝ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c)
⟹ᵀ-sub h (pDesc a) = pDesc (⟹-sub h a)
⟹ᵀ-sub h pEl-⌜Fin⌝ = pEl-⌜Fin⌝
⟹ᵀ-sub h (pDIh a m c d) = pDIh (⟹-sub h a) (⟹ᵀ-sub (⟹-exts (⟹-exts h)) m) (⟹-sub h c) (⟹-sub h d)
⟹ᵀ-sub h pDIh-ι = pDIh-ι
⟹ᵀ-sub h (pDIh-σ a m c d) = pDIh-σ (⟹-sub h a) (⟹ᵀ-sub (⟹-exts (⟹-exts h)) m) (⟹-sub h c) (⟹-sub h d)
⟹ᵀ-sub {σ = σ} {σ'} h (pDIh-ρ {D = D} {D'} {j = j} {j'} {C = C} {C'} {p = p} {p'} {M = M} {M'} a m b c d) =
  subst (λ Z → subTy σ (DIh D M (dρ j C) p) ⟹ᵀ Z)
        (sym (cong₂ Σ' (iinst-sub σ' M' j' (fst p'))
                        (cong₄ (λ w x y z → DIh w x y (snd z)) (wk-sub σ' D') (wk2-subTy σ' M') (wk-sub σ' C') (wk-sub σ' p'))))
        (pDIh-ρ (⟹-sub h a) (⟹ᵀ-sub (⟹-exts (⟹-exts h)) m) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d))
⟹ᵀ-sub h (pEl-⌜Id⌝ a b c) = pEl-⌜Id⌝ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c)

------------------------------------------------------------------------
-- Complete development + triangle for types.
------------------------------------------------------------------------

_⁺ᵀ : RTy Γ → RTy Γ
base ⁺ᵀ         = base
Unit ⁺ᵀ         = Unit
Nat ⁺ᵀ          = Nat
IMu I D i ⁺ᵀ = IMu (I ⁺) (D ⁺) (i ⁺)
Desc I ⁺ᵀ = Desc (I ⁺)
Fin n ⁺ᵀ = Fin n
DIh D M (dι j) p ⁺ᵀ = Unit
DIh D M (dσ S f) p ⁺ᵀ = DIh (D ⁺) (M ⁺ᵀ) (app (f ⁺) (fst (p ⁺))) (snd (p ⁺))
DIh D M (dρ j C) p ⁺ᵀ =
  Σ' (iinst (j ⁺) (fst (p ⁺)) (M ⁺ᵀ))
     (DIh (renTm vs (D ⁺)) (renTy (extR (extR vs)) (M ⁺ᵀ)) (renTm vs (C ⁺)) (snd (renTm vs (p ⁺))))
DIh D M C p ⁺ᵀ = DIh (D ⁺) (M ⁺ᵀ) (C ⁺) (p ⁺)
El (⌜IMu⌝ I D i) ⁺ᵀ = IMu (I ⁺) (D ⁺) (i ⁺)
El (⌜Fin⌝ n) ⁺ᵀ = Fin n
El (con c) ⁺ᵀ = El (con c ⁺)
El (dι j) ⁺ᵀ = El (dι j ⁺)
El (dσ S f) ⁺ᵀ = El (dσ S f ⁺)
El (dρ j C) ⁺ᵀ = El (dρ j C ⁺)
El (dpay I D C i) ⁺ᵀ = El (dpay I D C i ⁺)
El (dih D e C p) ⁺ᵀ = El (dih D e C p ⁺)
El fzero ⁺ᵀ = El (fzero ⁺)
El (fsuc t) ⁺ᵀ = El (fsuc t ⁺)
El (fcase t a b) ⁺ᵀ = El (fcase t a b ⁺)
El (fcase0 t) ⁺ᵀ = El (fcase0 t ⁺)
El (psplit b q) ⁺ᵀ = El (psplit b q ⁺)
U ⁺ᵀ            = U
El (var x) ⁺ᵀ   = El (var x ⁺)
El (lam t) ⁺ᵀ   = El (lam t ⁺)
El (app f a) ⁺ᵀ = El (app f a ⁺)
El (pair a b) ⁺ᵀ = El (pair a b ⁺)
El (absurd c e) ⁺ᵀ = El (absurd c e ⁺)
El (ordtr a t u p q) ⁺ᵀ = El (ordtr a t u p q ⁺)
El (fst p) ⁺ᵀ   = El (fst p ⁺)
El (snd p) ⁺ᵀ   = El (snd p ⁺)
El (ielim D i ms t) ⁺ᵀ = El (ielim D i ms t ⁺)
El ⌜Nat⌝ ⁺ᵀ     = Nat
El ⌜Unit⌝ ⁺ᵀ    = Unit
El ⌜base⌝ ⁺ᵀ    = base
El (⌜Π⌝ c d) ⁺ᵀ = Π (El (c ⁺)) (El (d ⁺))
El (⌜Σ⌝ c d) ⁺ᵀ = Σ' (El (c ⁺)) (El (d ⁺))
El (⌜Hom⌝ c a b) ⁺ᵀ = Hom (El (c ⁺)) (a ⁺) (b ⁺)
El (⌜Id⌝ c a b) ⁺ᵀ  = Id (El (c ⁺)) (a ⁺) (b ⁺)
El unit ⁺ᵀ          = El (unit ⁺)
El nzero ⁺ᵀ         = El (nzero ⁺)
El (nsuc n) ⁺ᵀ      = El (nsuc n ⁺)
El (natrec z s n) ⁺ᵀ = El (natrec z s n ⁺)
El (idrefl c t) ⁺ᵀ  = El (idrefl c t ⁺)
El (jsub d p e) ⁺ᵀ  = El (jsub d p e ⁺)
El (hrefl c t) ⁺ᵀ   = El (hrefl c t ⁺)
El (tr d p e) ⁺ᵀ    = El (tr d p e ⁺)
El (ap c b p) ⁺ᵀ    = El (ap c b p ⁺)
El (con p) ⁺ᵀ       = El (con p ⁺)
El (dι j) ⁺ᵀ        = El (dι j ⁺)
El (dσ S f) ⁺ᵀ      = El (dσ S f ⁺)
El (dρ j C) ⁺ᵀ      = El (dρ j C ⁺)
El (dpay I D C i) ⁺ᵀ = El (dpay I D C i ⁺)
El (dih D e C p) ⁺ᵀ = El (dih D e C p ⁺)
El fzero ⁺ᵀ         = El (fzero ⁺)
El (fsuc t) ⁺ᵀ      = El (fsuc t ⁺)
El (fcase t a b) ⁺ᵀ = El (fcase t a b ⁺)
El (fcase0 t) ⁺ᵀ    = El (fcase0 t ⁺)
El (psplit b q) ⁺ᵀ  = El (psplit b q ⁺)
Π A B ⁺ᵀ        = Π (A ⁺ᵀ) (B ⁺ᵀ)
Σ' A B ⁺ᵀ       = Σ' (A ⁺ᵀ) (B ⁺ᵀ)
-- W2: `Hom` develops by the head of its TYPE argument.  Where the head is
-- already `U`/`Π` the unfolding fires (with components developed); where it
-- is an `El` code the development DECODES ONLY — one parallel step cannot
-- both decode and unfold, the same one-step-behind pattern `El` itself uses.
Hom base t u ⁺ᵀ        = Hom base (t ⁺) (u ⁺)
Hom Unit t u ⁺ᵀ        = Hom Unit (t ⁺) (u ⁺)
-- ★★ WF stage B: `Hom` at `Nat` develops by the ENDPOINTS' numeral
-- heads — this is the only `_⁺ᵀ` clause that dispatches on endpoints
-- rather than on the ambient, and it is exactly what makes `Nat` an
-- ORDERED inductive.
Hom Nat nzero u ⁺ᵀ            = Unit
Hom Nat (nsuc m) nzero ⁺ᵀ     = base
Hom Nat (nsuc m) (nsuc n) ⁺ᵀ  = Hom Nat (m ⁺) (n ⁺)
Hom Nat t u ⁺ᵀ                = Hom Nat (t ⁺) (u ⁺)
Hom U c d ⁺ᵀ           = Π (El (c ⁺)) (El (renTm vs (d ⁺)))
Hom (Π A B) f g ⁺ᵀ     =
  Π (A ⁺ᵀ) (Hom (B ⁺ᵀ) (app (renTm vs (f ⁺)) (var vz))
                       (app (renTm vs (g ⁺)) (var vz)))
Hom (Σ' A B) t u ⁺ᵀ    = Hom (Σ' (A ⁺ᵀ) (B ⁺ᵀ)) (t ⁺) (u ⁺)
Hom (El e) t u ⁺ᵀ      = Hom ((El e) ⁺ᵀ) (t ⁺) (u ⁺)
Hom (Hom A a b) t u ⁺ᵀ = Hom ((Hom A a b) ⁺ᵀ) (t ⁺) (u ⁺)
Hom (Id A a b) t u ⁺ᵀ  = Hom ((Id A a b) ⁺ᵀ) (t ⁺) (u ⁺)
-- the two-former kernel: `Id` is INERT — a UNIFORM development row, no
-- head dispatch at all.
Hom (IMu I D i) t u ⁺ᵀ = Hom (IMu (I ⁺) (D ⁺) (i ⁺)) (t ⁺) (u ⁺)
Hom (Desc I) t u ⁺ᵀ = Hom (Desc (I ⁺)) (t ⁺) (u ⁺)
Hom (Fin n) t u ⁺ᵀ = Hom (Fin n) (t ⁺) (u ⁺)
Hom (DIh D M C p) t u ⁺ᵀ = Hom ((DIh D M C p) ⁺ᵀ) (t ⁺) (u ⁺)
Id A t u ⁺ᵀ = Id (A ⁺ᵀ) (t ⁺) (u ⁺)

⟹ᵀ-⁺ : {A B : RTy Γ} → A ⟹ᵀ B → B ⟹ᵀ A ⁺ᵀ
⟹ᵀ-⁺ pbase          = pbase
⟹ᵀ-⁺ pU             = pU
⟹ᵀ-⁺ pEl-⌜Nat⌝      = pNat
⟹ᵀ-⁺ pEl-⌜Unit⌝     = pUnit
⟹ᵀ-⁺ pUnit          = pUnit
⟹ᵀ-⁺ pNat           = pNat
⟹ᵀ-⁺ (pEl w@(pcon _))    = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) w@(pcon _)) =
  pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ w)
⟹ᵀ-⁺ (pHom pNat w@(pcon _) pu)    = pHom pNat (⟹-⁺ w) (⟹-⁺ pu)
⟹ᵀ-⁺ (pEl w@punit)  = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@pnzero) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pnsuc _))  = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pnatrec _ _ _))      = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pnatrec-zero _ _))   = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pnatrec-suc _ _ _))  = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl (pvar x)) = pEl (⟹-⁺ (pvar x))
⟹ᵀ-⁺ (pEl (plam p)) = pEl (⟹-⁺ (plam p))
⟹ᵀ-⁺ (pEl (papp p q)) = pEl (⟹-⁺ (papp p q))
⟹ᵀ-⁺ (pEl (pβ p q))  = pEl (⟹-⁺ (pβ p q))
⟹ᵀ-⁺ (pEl (ppair p q)) = pEl (⟹-⁺ (ppair p q))
⟹ᵀ-⁺ (pEl w@(pabsurd _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pordtr _ _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@pordtr-z) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pordtr-szz _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pordtr-ssz _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pordtr-szs _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pordtr-sss _ _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl (pfst p))  = pEl (⟹-⁺ (pfst p))
⟹ᵀ-⁺ (pEl (psnd p))  = pEl (⟹-⁺ (psnd p))
⟹ᵀ-⁺ (pEl (pβfst p q)) = pEl (⟹-⁺ (pβfst p q))
⟹ᵀ-⁺ (pEl (pβsnd p q)) = pEl (⟹-⁺ (pβsnd p q))
⟹ᵀ-⁺ (pEl p⌜Nat⌝)    = pEl-⌜Nat⌝
⟹ᵀ-⁺ (pEl p⌜Unit⌝)   = pEl-⌜Unit⌝
⟹ᵀ-⁺ (pEl w@(ptr-J-Unit _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl p⌜base⌝)   = pEl-⌜base⌝
⟹ᵀ-⁺ (pEl (p⌜Π⌝ p q)) = pEl-⌜Π⌝ (⟹-⁺ p) (⟹-⁺ q)
⟹ᵀ-⁺ (pEl (p⌜Σ⌝ p q)) = pEl-⌜Σ⌝ (⟹-⁺ p) (⟹-⁺ q)
⟹ᵀ-⁺ (pEl (p⌜Hom⌝ p q r)) = pEl-⌜Hom⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
⟹ᵀ-⁺ (pEl (p⌜Id⌝ p q r)) = pEl-⌜Id⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
⟹ᵀ-⁺ (pEl w@(phrefl _ _))      = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr _ _ _))       = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-J-base _))    = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-J-Σ _))       = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-taut _ _))    = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(phrefl-pw _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-J-Hom _ _))   = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-pw _ _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-J-Id _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pcon _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pielim _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pι _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdι _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdσ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdρ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdpay _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdpay-ι _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdpay-σ _ _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdpay-ρ _ _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdih _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@pdih-ι) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdih-σ _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pdih-ρ _ _ _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@pfzero) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pfsuc _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pfcase _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pfcase-z _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pfcase-s _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pfcase0 _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ppsplit _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ppsplit-β _ _ _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-J-Fin _)) = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pap _ _ _))        = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pap-J _ _ _ _))    = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pidrefl _ _))      = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pjsub _ _ _))      = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(pjsub-refl _))     = pEl (⟹-⁺ w)
-- ★ a J-step under `El` is just a term step: the code is not the head.
⟹ᵀ-⁺ (pEl w@(ptr-J-IMu _))       = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pΠ p q)       = pΠ (⟹ᵀ-⁺ p) (⟹ᵀ-⁺ q)
⟹ᵀ-⁺ (pΣ p q)       = pΣ (⟹ᵀ-⁺ p) (⟹ᵀ-⁺ q)
⟹ᵀ-⁺ pEl-⌜base⌝     = pbase
⟹ᵀ-⁺ (pEl-⌜Π⌝ p q)  = pΠ (pEl (⟹-⁺ p)) (pEl (⟹-⁺ q))
⟹ᵀ-⁺ (pEl-⌜Σ⌝ p q)  = pΣ (pEl (⟹-⁺ p)) (pEl (⟹-⁺ q))
-- W2: the `Hom` triangle, dispatching on the type argument's evidence.
-- Only two cases are non-uniform — the heads whose development UNFOLDS.
⟹ᵀ-⁺ (pHom pU pt pu)         = pHom-U (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pΠ pA pB) pt pu) =
  pHom-Π (⟹ᵀ-⁺ pA) (⟹ᵀ-⁺ pB) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pbase pt pu)      = pHom pbase (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pUnit pt pu)      = pHom pUnit (⟹-⁺ pt) (⟹-⁺ pu)
-- ★ WF stage B: the endpoint case tree.  `pnzero` on the left is
-- decisive (the zero rule ignores the right endpoint); a `pnsuc`
-- left endpoint then splits the right one.  Everything else is
-- the plain congruence.
⟹ᵀ-⁺ (pHom pNat pnzero pu) = pHom-Nat-z (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pnzero) = pHom-Nat-sz (⟹-⁺ pm)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) (pnsuc pn)) = pHom-Nat-ss (⟹-⁺ pm) (⟹-⁺ pn)
-- ★ stage D: `absurd` is not a numeral, so no order rule fires and the
-- order-hom stays put.
⟹ᵀ-⁺ (pHom pNat pt@(pabsurd _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pordtr _ _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@pordtr-z pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pordtr-szz _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pordtr-ssz _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pordtr-szs _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pordtr-sss _ _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pabsurd _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pordtr _ _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@pordtr-z) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pordtr-szz _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pordtr-ssz _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pordtr-szs _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pordtr-sss _ _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pvar _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(plam _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(papp _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pβ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ppair _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pfst _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(psnd _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pβfst _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pβsnd _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@p⌜Nat⌝) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@p⌜Unit⌝) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-J-IMu _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-J-Unit _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@p⌜base⌝) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(p⌜Π⌝ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(p⌜Σ⌝ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(p⌜Hom⌝ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(phrefl _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-J-base _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-J-Σ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-J-Id _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-taut _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(phrefl-pw _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-J-Hom _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-pw _ _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pap _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pap-J _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(p⌜Id⌝ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pidrefl _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pjsub _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pjsub-refl _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@punit) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pnatrec _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pnatrec-zero _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pnatrec-suc _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pcon _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(p⌜IMu⌝ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@p⌜Fin⌝) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pielim _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pι _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdι _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdσ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdρ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdpay _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdpay-ι _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdpay-σ _ _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdpay-ρ _ _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdih _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@pdih-ι) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdih-σ _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pdih-ρ _ _ _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@pfzero) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pfsuc _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pfcase _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pfcase-z _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pfcase-s _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(pfcase0 _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ppsplit _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ppsplit-β _ _ _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat (pnsuc pm) pu@(ptr-J-Fin _)) = pHom pNat (pnsuc (⟹-⁺ pm)) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pvar _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(plam _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(papp _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pβ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ppair _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pfst _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(psnd _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pβfst _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pβsnd _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@p⌜Nat⌝ pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@p⌜Unit⌝ pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-J-IMu _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-J-Unit _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@p⌜base⌝ pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(p⌜Π⌝ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(p⌜Σ⌝ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(p⌜Hom⌝ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(phrefl _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-J-base _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-J-Σ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-J-Id _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-taut _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(phrefl-pw _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-J-Hom _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-pw _ _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pap _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pap-J _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(p⌜Id⌝ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pidrefl _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pjsub _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pjsub-refl _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@punit pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pnatrec _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pnatrec-zero _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pnatrec-suc _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pcon _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(p⌜IMu⌝ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@p⌜Fin⌝ pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pielim _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pι _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdι _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdσ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdρ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdpay _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdpay-ι _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdpay-σ _ _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdpay-ρ _ _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdih _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@pdih-ι pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdih-σ _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pdih-ρ _ _ _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@pfzero pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pfsuc _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pfcase _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pfcase-z _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pfcase-s _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(pfcase0 _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ppsplit _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ppsplit-β _ _ _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pNat pt@(ptr-J-Fin _) pu) = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pΣ pA pB) pt pu) =
  pHom (pΣ (⟹ᵀ-⁺ pA) (⟹ᵀ-⁺ pB)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl pe) pt pu)   =
  pHom (⟹ᵀ-⁺ (pEl pe)) (⟹-⁺ pt) (⟹-⁺ pu)
-- one parallel step cannot both DECODE the ambient and dispatch on the
-- endpoints — the same one-step-behind principle `El` itself uses.
⟹ᵀ-⁺ (pHom pEl-⌜Nat⌝ pt pu)  = pHom pNat (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pEl-⌜Unit⌝ pt pu) = pHom pUnit (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pEl-⌜base⌝ pt pu) =
  pHom (⟹ᵀ-⁺ pEl-⌜base⌝) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl-⌜Π⌝ p q) pt pu) =
  pHom (⟹ᵀ-⁺ (pEl-⌜Π⌝ p q)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl-⌜Σ⌝ p q) pt pu) =
  pHom (⟹ᵀ-⁺ (pEl-⌜Σ⌝ p q)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl-⌜Hom⌝ p q r) pt pu) =
  pHom (⟹ᵀ-⁺ (pEl-⌜Hom⌝ p q r)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pHom pA pa pb) pt pu) =
  pHom (⟹ᵀ-⁺ (pHom pA pa pb)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pHom-Nat-z _) pt pu) =
  pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pHom-Nat-sz _) pt pu) =
  pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pHom-Nat-ss _ _) pt pu) =
  pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom-Nat-z pn)     = pUnit
⟹ᵀ-⁺ (pHom-Nat-sz pm)    = pbase
⟹ᵀ-⁺ (pHom-Nat-ss pm pn) = pHom pNat (⟹-⁺ pm) (⟹-⁺ pn)
⟹ᵀ-⁺ (pHom (pHom-U p q) pt pu) =
  pHom (⟹ᵀ-⁺ (pHom-U p q)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pHom-Π pA pB pf pg) pt pu) =
  pHom (⟹ᵀ-⁺ (pHom-Π pA pB pf pg)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pId pA pa pb) pt pu) =
  pHom (⟹ᵀ-⁺ (pId pA pa pb)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl-⌜Id⌝ p q r) pt pu) =
  pHom (⟹ᵀ-⁺ (pEl-⌜Id⌝ p q r)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pId pA pt pu) = pId (⟹ᵀ-⁺ pA) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pEl-⌜Id⌝ p q r) = pId (pEl (⟹-⁺ p)) (⟹-⁺ q) (⟹-⁺ r)
⟹ᵀ-⁺ (pEl-⌜Hom⌝ p q r) = pHom (pEl (⟹-⁺ p)) (⟹-⁺ q) (⟹-⁺ r)
⟹ᵀ-⁺ (pHom-U p q) = pΠ (pEl (⟹-⁺ p)) (pEl (⟹-ren vs (⟹-⁺ q)))
⟹ᵀ-⁺ (pHom-Π pA pB pf pg) =
  pΠ (⟹ᵀ-⁺ pA)
     (pHom (⟹ᵀ-⁺ pB) (papp (⟹-ren vs (⟹-⁺ pf)) (pvar vz))
                     (papp (⟹-ren vs (⟹-⁺ pg)) (pvar vz)))

------------------------------------------------------------------------
-- Diamond → confluence → Church–Rosser, for types.
-- ★★ LEVITATION: the family type formers and the hypotheses type.
⟹ᵀ-⁺ (pIMu a b c) = pIMu (⟹-⁺ a) (⟹-⁺ b) (⟹-⁺ c)
⟹ᵀ-⁺ (pEl-⌜IMu⌝ a b c) = pIMu (⟹-⁺ a) (⟹-⁺ b) (⟹-⁺ c)
⟹ᵀ-⁺ (pEl (p⌜IMu⌝ a b c)) = pEl-⌜IMu⌝ (⟹-⁺ a) (⟹-⁺ b) (⟹-⁺ c)
⟹ᵀ-⁺ (pDesc a) = pDesc (⟹-⁺ a)
⟹ᵀ-⁺ pFin = pFin
⟹ᵀ-⁺ pEl-⌜Fin⌝ = pFin
⟹ᵀ-⁺ (pEl p⌜Fin⌝) = pEl-⌜Fin⌝
⟹ᵀ-⁺ (pDIh pD pM (pdι pj) pp) = pDIh-ι
⟹ᵀ-⁺ (pDIh pD pM (pdσ pS pf) pp) = pDIh-σ (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ pf) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM (pdρ pj pC) pp) = pDIh-ρ (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ pj) (⟹-⁺ pC) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pvar _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(plam _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(papp _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pβ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ppair _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pabsurd _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pordtr _ _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@pordtr-z pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pordtr-szz _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pordtr-ssz _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pordtr-szs _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pordtr-sss _ _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pfst _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(psnd _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pβfst _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pβsnd _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@p⌜base⌝ pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(p⌜Π⌝ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(p⌜Σ⌝ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(p⌜Hom⌝ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(phrefl _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-J-base _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@p⌜Nat⌝ pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@p⌜Unit⌝ pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-J-Unit _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-J-IMu _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-J-Fin _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-J-Σ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-J-Id _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-taut _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(phrefl-pw _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-J-Hom _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ptr-pw _ _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pap _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pap-J _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(p⌜Id⌝ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pidrefl _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pjsub _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pjsub-refl _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@punit pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@pnzero pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pnsuc _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pnatrec _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pnatrec-zero _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pnatrec-suc _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(p⌜IMu⌝ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@p⌜Fin⌝ pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pcon _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pielim _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pι _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pdpay _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pdpay-ι _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pdpay-σ _ _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pdpay-ρ _ _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pdih _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@pdih-ι pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pdih-σ _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pdih-ρ _ _ _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@pfzero pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pfsuc _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pfcase _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pfcase-z _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pfcase-s _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(pfcase0 _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ppsplit _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ (pDIh pD pM w@(ppsplit-β _ _ _) pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (⟹-⁺ w) (⟹-⁺ pp)
⟹ᵀ-⁺ pDIh-ι = pUnit
⟹ᵀ-⁺ (pDIh-σ pD pM pf pp) = pDIh (⟹-⁺ pD) (⟹ᵀ-⁺ pM) (papp (⟹-⁺ pf) (pfst (⟹-⁺ pp))) (psnd (⟹-⁺ pp))
⟹ᵀ-⁺ (pDIh-ρ pD pM pj pC pp) =
  pΣ (⟹ᵀ-sub (single-⟹ (pfst (⟹-⁺ pp))) (⟹ᵀ-sub (⟹-exts (single-⟹ (⟹-⁺ pj))) (⟹ᵀ-⁺ pM)))
     (pDIh (⟹-ren vs (⟹-⁺ pD)) (⟹ᵀ-ren (extR (extR vs)) (⟹ᵀ-⁺ pM))
           (⟹-ren vs (⟹-⁺ pC)) (psnd (⟹-ren vs (⟹-⁺ pp))))
⟹ᵀ-⁺ (pHom w@(pIMu _ _ _) pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pEl-⌜IMu⌝ _ _ _) pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pDesc _) pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@pFin pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@pEl-⌜Fin⌝ pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pDIh _ _ _ _) pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@pDIh-ι pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pDIh-σ _ _ _ _) pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom w@(pDIh-ρ _ _ _ _ _) pt pu) = pHom (⟹ᵀ-⁺ w) (⟹-⁺ pt) (⟹-⁺ pu)

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

-- ★ LEVITATION: `IMu` carries THREE terms (index code, description,
--   index), each may reduce; `Desc` one; `Fin` is inert.
IMuinj≡ : {I I' D D' i i' : RTm Γ} →
          IMu I D i ≡ IMu I' D' i' → (I ≡ I') × ((D ≡ D') × (i ≡ i'))
IMuinj≡ refl = (refl , (refl , refl))

record IMuRed {Γ : Cx} (I D i : RTm Γ) (C : RTy Γ) : Set where
  constructor mkIMuRed
  field
    cod  : RTm Γ
    desc : RTm Γ
    idx  : RTm Γ
    eq   : C ≡ IMu cod desc idx
    rcod : I ⟶* cod
    rdes : D ⟶* desc
    ridx : i ⟶* idx

IMu-reduct : {I D i : RTm Γ} {C : RTy Γ} → IMu I D i ⟶ᵀ* C → IMuRed I D i C
IMu-reduct doneᵀ = mkIMuRed _ _ _ refl done done done
IMu-reduct (stepᵀ (ξ-IMuᴵ r) p) with IMu-reduct p
... | mkIMuRed a b c eq ra rb rc = mkIMuRed a b c eq (step r ra) rb rc
IMu-reduct (stepᵀ (ξ-IMuᴰ r) p) with IMu-reduct p
... | mkIMuRed a b c eq ra rb rc = mkIMuRed a b c eq ra (step r rb) rc
IMu-reduct (stepᵀ (ξ-IMuⁱ r) p) with IMu-reduct p
... | mkIMuRed a b c eq ra rb rc = mkIMuRed a b c eq ra rb (step r rc)

-- ⚠ all three only ≅, not ≡ — they are TERMS and they reduce.
IMu-inj : {I I' D D' i i' : RTm Γ} →
          IMu I D i ≅ᵀ IMu I' D' i' → (I ≅ I') × ((D ≅ D') × (i ≅ i'))
IMu-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with IMu-reduct r₁ | IMu-reduct r₂
...   | mkIMuRed a₁ b₁ c₁ eq₁ ra₁ rb₁ rc₁ | mkIMuRed a₂ b₂ c₂ eq₂ ra₂ rb₂ rc₂
        with IMuinj≡ (trans (sym eq₁) eq₂)
...       | (ea , (eb , ec)) =
            ctrn (hom→≅ ra₁) (csym (hom→≅ (subst (_ ⟶*_) (sym ea) ra₂)))
          , (ctrn (hom→≅ rb₁) (csym (hom→≅ (subst (_ ⟶*_) (sym eb) rb₂)))
          , ctrn (hom→≅ rc₁) (csym (hom→≅ (subst (_ ⟶*_) (sym ec) rc₂))))

Desc-reduct : {I : RTm Γ} {C : RTy Γ} → Desc I ⟶ᵀ* C → Σ (RTm Γ) (λ J → (C ≡ Desc J) × (I ⟶* J))
Desc-reduct doneᵀ = _ , (refl , done)
Desc-reduct (stepᵀ (ξ-Desc r) p) with Desc-reduct p
... | J , (eq , rJ) = J , (eq , step r rJ)

Descinj≡ : {I I' : RTm Γ} → Desc I ≡ Desc I' → I ≡ I'
Descinj≡ refl = refl

Desc-inj : {I I' : RTm Γ} → Desc I ≅ᵀ Desc I' → I ≅ I'
Desc-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with Desc-reduct r₁ | Desc-reduct r₂
...   | J₁ , (eq₁ , rJ₁) | J₂ , (eq₂ , rJ₂) =
        ctrn (hom→≅ rJ₁) (csym (hom→≅ (subst (_ ⟶*_) (sym (Descinj≡ (trans (sym eq₁) eq₂))) rJ₂)))

Fin-reduct : {n : ℕ} {C : RTy Γ} → Fin n ⟶ᵀ* C → C ≡ Fin n
Fin-reduct doneᵀ = refl
Fin-reduct (stepᵀ () _)

Fininj≡ : {n n' : ℕ} → Fin {Γ} n ≡ Fin n' → n ≡ n'
Fininj≡ refl = refl

Fin-inj : {n n' : ℕ} → Fin {Γ} n ≅ᵀ Fin n' → n ≡ n'
Fin-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) = Fininj≡ (trans (sym (Fin-reduct r₁)) (Fin-reduct r₂))

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
