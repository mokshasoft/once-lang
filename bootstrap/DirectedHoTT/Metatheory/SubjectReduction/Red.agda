-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 28 — (B2, part 2) SUBJECT REDUCTION, completed
--
-- The mechanical closing of subject reduction, on the Π-injectivity of
-- `NbEPDirDBInj` (dHoTT-26). Everything here is confluence-free and reuses the
-- strict substitution laws of `NbEPDirDBPi`/`NbEPDirDBSR`/`NbEPDirDBConf`.
--
--   * Type-level commute/cancel lemmas (`wk-cancel`, `subTy-comm`,
--     `ren-wk-comm`, `ren-comm-ty`, `exts-wk-ty`) — all via the type fusion
--     lemmas + refl/`sub-comm` bridges.
--   * `⟶ᵀ-ren`/`≅ᵀ-ren` — conversion survives renaming; `subTy-monoˢ` — types
--     are monotone in the substitution.
--   * `ren-lemma` / `sub-lemma` — TYPED renaming and substitution preserve
--     typing (the `⊢ˢ`/`Ren⊢` judgments + the ext-lemmas), and `⊢[]` — single
--     substitution preserves typing (what β needs).
--   * `gen-lam` / `gen-app` — generation (inversion through `⊢conv`).
--   * **`sr`** — SUBJECT REDUCTION: `Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A`. The β case
--     converts the argument to the λ's domain and the result type (via
--     `Π-inj`), sidestepping context conversion entirely.
--
-- With this, dHoTT-24's scoped ceiling is fully lifted: the kernel enjoys
-- subject reduction. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs; _<ˢ_; _<ˢ?_ )
module DirectedHoTT.Metatheory.SubjectReduction.Red (𝒮 : Defs) where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ ; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; Thin; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var
        ; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝
        ; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub; Id-cong₃; ⌜Id⌝-cong₃
        ; jsub-cong₃; Unit; Nat; unit; nzero; nsuc; natrec; ⌜Nat⌝; ⌜Unit⌝; Ren
        ; extR; renTm; renTy; Sub; extS; subTm; subTy; idₛ; _∘ᵣ_; _ₛ∘ᵣ_; _ᵣ∘ₛ_
        ; _∘ₛ_; subTy-renTy; renTy-subTy; subTy-subTy; renTy-renTy; subTy-cong
        ; renTy-cong; subTy-id; subTm-renTm; subTm-id; subTm-cong; renTm-renTm
        ; renTm-subTm; ⌜Hom⌝-cong₃; Hom-cong₃; ordtr-cong₅; Desc; con; dι; dρ
        ; IMu; ielim; ⌜IMu⌝; εwkTy; εwk-ren; εwk-sub; εwkTm; εwkTm-ren
        ; εwkTm-sub; subTm-subTm
        ; DIh; Fin; ⌜Fin⌝; dσ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit; cong₄; cong₃
        ; ref )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; _∨_; occTm; ∨-false; ∨-false₁; ∨-false₂; occ-ren-eq
        ; occ-sub; eqv; Avoids; occ-ren-tm; avoids-wk; PosC; posc-var
        ; posc-Hom; posc-ren; posc-sub; pw?; stkC?; pwDom; pwBody; pwShift
        ; pw?-sub; stkC?-sub; pwBody-sub; pwDom-sub; pwBody-occ; ren-as-sub
        ; avoids-pwShift; subTm-occ; stkC?-ren; wk-ren-tm; wk-sub-tm; flat?
        ; flat→stk; flat?-ren; flat?-sub; NoNatC; nnc-base; nnc-Unit; nnc-Fin; nnc-Π
        ; nnc-Σ; nnc-Hom; nnc-Id; nonatc-ren; nonatc-sub; nonatc-pwBody; stkA?
        ; stkA?-ren; stkA?-sub; stkC?→stkA?; NoNatHd; nnh-base; nnh-Unit
        ; nnh-Σ; nnh-Id; nnh-Π; nnh-Hom; nnh-IMu; nonatc→hd; stkC?→hd
        ; occ-εwkTm
        ; nnh-Fin )
open import DirectedHoTT.Spec.Reduction 𝒮
  using ( single; nrs; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ
        ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; _⟶_; β; βfst
        ; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ
        ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss; ξ-ordtrᵃ
        ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ
        ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; tr-J-base; tr-J-Σ; tr-J-Id; tr-J-Unit; tr-J-IMu
        ; tr-taut; hrefl-pw; hrefl-Nat-z; hrefl-Nat-s; tr-J-Hom; tr-pw; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜IMu⌝
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ
        ; ξ-trᵉ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ
        ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; El-⌜Id⌝
        ; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ
        ; ξ-natrecˢ; ξ-natrecⁿ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss; _⟶*_; done
        ; step; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_
        ; here; there; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢absurd
        ; ⊢ordtr; ⊢trU; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢ap; ⊢conv
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec; ⊢⌜Nat⌝
        ; ⊢⌜Unit⌝; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom; ty-Id
        ; ty-Unit; ty-Nat; ⊢ctx_; c-◇; c-▹; ξ-con; ξ-ielimⁱ; ξ-ielimᵗ; ⊢con
        ; wk-single; iinst; ty-IMu; ⊢ielim; ⊢⌜IMu⌝; _≅_; csym; ctrn; cred
        ; crfl
        ; El-⌜Fin⌝; DIh-ι; DIh-σ; DIh-ρ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-Fin; ξ-⌜Fin⌝; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dσˢ; ξ-dσᶠ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ; ξ-psplitᵍ; tr-J-Fin; ⊢⌜Fin⌝; ⊢dι; ⊢dσ; ⊢dρ; ⊢dpay; ⊢dih; ⊢fzero; ⊢fsuc; ⊢fcase; ⊢fcase0; ⊢psplit; ty-Desc; ty-DIh; ty-Fin; MethTy; motCtx; methS; wk2M; single2; pairS; fsucS; DescF
        ; δref; ⊢ref )
import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 as ᴵSubjectReductionBase
open ᴵSubjectReductionBase using ( ≅ᵀ-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.Confluence 𝒮
  using ( ⟶-ren; ⟶*-ren; ⟶*-appʳ; ren-comm; subTm-monoˢ; extS-mono; single-mono
        ; stkC?-red; stkA?-red; church-rosser
        ; ⟶*-trans; ⟶*-dpayᴵ; ⟶*-dpayᴰ; ⟶*-dpayᶜ; ⟶*-appˡ )
open ᴵSubjectReductionBase using ( sub-comm; ⟶ᵀ-sub )
open import DirectedHoTT.Metatheory.Injectivity 𝒮
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El
        ; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ
        ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; red→≅ᵀ; Π-inj; Σ-inj
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; Id-reduct
        ; church-rosserᵀ; Π-reduct; ΠRed; mkΠRed
        ; ⟶ᵀ*-IMu; IMu-inj; IMu-reduct; IMuRed; mkIMuRed
        ; Desc-inj; Fin-inj; nsuc-inj≅; Fin-cong≅; ⟶ᵀ*-Desc )

private
  variable
    Γ Δ : Cx


------------------------------------------------------------------------
-- ★★★ THE STRUCTURAL TYPING LEMMAS MOVED TO `Metatheory/TySub` and are
--   re-exported here, so every existing importer is unaffected.
--
-- ⚠⚠ THE REASON IS A CONSUMPTION MISMATCH, MEASURED.  ~100 modules import
--   this one; roughly NINETY use exactly ONE name from it — `⊢wk` — and
--   only EIGHT want `sr`/`sr*`/the indexed-ι lemmas it is named for.  This
--   module depends on `Confluence` (8.9 MB) and `Injectivity` (5.4 MB), so
--   the ninety were deserializing the whole confluence proof to weaken a
--   derivation.  `--profile=all`: ~70% deserialization, ~0ms typing.
--
-- ★ WHAT STAYS: the reduct analyses below (the only users of `Π-reduct`
--   and `church-rosserᵀ`), `ipayTy-conv` (the only user of
--   `church-rosser`), generation, the pw decode joins, `sr`, `sr*` and
--   the ι/indexed-ι lemmas.  Everything else is in `TySub`.
------------------------------------------------------------------------

open import DirectedHoTT.Metatheory.TySub.Red 𝒮
open import DirectedHoTT.Metatheory.RedCong 𝒮


------------------------------------------------------------------------
-- Reduct analyses for `sr`'s J and taut cases.  A `Hom` whose ambient
-- satisfies a reduction-closed, U/Π-free predicate never unfolds, so its
-- reducts are `Hom`s with componentwise reductions; a `Hom` that reduces
-- to a `Π` did unfold exactly once, via `Hom-U` or `Hom-Π`.
------------------------------------------------------------------------

-- ★★ WF stage B: the ambient guard.  The order rules fire ONLY at a
-- `Nat` ambient, so every ambient-generic Hom-inversion lemma below
-- needs to know its ambient will never BECOME `Nat`.
--
-- ★★ WF stage C, THE CONVERGENCE.  Stage B could write the blanket
-- `nn-El : NoNat (El c)` — no code decoded to `Nat`, so the whole
-- `El`-ambient theory of stages 1–A was untouched.  `⌜Nat⌝ ∈ U` kills
-- that: `El ⌜Nat⌝ ⟶ᵀ Nat`, so `nonat-red nn-El El-⌜Nat⌝` is an
-- unfillable hole and `NoNat` is no longer preserved by `⟶ᵀ`.
--
-- The repair is to say what is TRUE rather than what was convenient:
-- an `El` ambient is Nat-free exactly when its CODE is
-- constructor-headed at something other than ⌜Nat⌝.  That property
-- (`NoNatC`) IS reduction-closed — constructor-headed codes only ever
-- develop under their own congruences — so `nonat-red` goes through
-- again, and only a ⌜Nat⌝-headed ambient is excluded, which is the
-- true statement.  Every consumer already knows its code head
-- concretely (the `tr-J-base`/`-Σ`/`-Id`/`-Hom`/`-Unit` cases of `sr`),
-- or knows `stkC? c ≡ true`, which implies it (`stkC?→NoNatC`, in
-- NbEPDirDBVar alongside the datatype itself).
--
-- constructor-headed codes stay constructor-headed: the only rules
-- with a ⌜Π⌝/⌜Σ⌝/⌜Hom⌝/⌜Id⌝ redex are that former's own congruences,
-- and ⌜base⌝/⌜Unit⌝ are normal.
-- ★ the SHALLOW peer: a constructor-headed non-⌜Nat⌝ code only ever
-- develops in its COMPONENTS, so the head survives reduction.  This is
-- all `nn-El` needs, and unlike `nonatc-red` it says nothing about the
-- spine — which is what lets `⌜Hom⌝ ⌜Nat⌝ a b` through.
nonathd-red : {c c' : RTm Γ} → NoNatHd c → c ⟶ c' → NoNatHd c'
nonathd-red nnh-base ()
nonathd-red nnh-Unit ()
nonathd-red nnh-Fin (ξ-⌜Fin⌝ _) = nnh-Fin
nonathd-red nnh-IMu (ξ-⌜IMu⌝ᴵ _) = nnh-IMu
nonathd-red nnh-IMu (ξ-⌜IMu⌝ᴰ _) = nnh-IMu
nonathd-red nnh-IMu (ξ-⌜IMu⌝ⁱ _) = nnh-IMu
nonathd-red nnh-Σ (ξ-⌜Σ⌝ˡ _) = nnh-Σ
nonathd-red nnh-Σ (ξ-⌜Σ⌝ʳ _) = nnh-Σ
nonathd-red nnh-Id (ξ-⌜Id⌝ᶜ _) = nnh-Id
nonathd-red nnh-Id (ξ-⌜Id⌝ˡ _) = nnh-Id
nonathd-red nnh-Id (ξ-⌜Id⌝ʳ _) = nnh-Id
nonathd-red nnh-Π (ξ-⌜Π⌝ˡ _) = nnh-Π
nonathd-red nnh-Π (ξ-⌜Π⌝ʳ _) = nnh-Π
nonathd-red nnh-Hom (ξ-⌜Hom⌝ᶜ _) = nnh-Hom
nonathd-red nnh-Hom (ξ-⌜Hom⌝ˡ _) = nnh-Hom
nonathd-red nnh-Hom (ξ-⌜Hom⌝ʳ _) = nnh-Hom

nonatc-red : {c c' : RTm Γ} → NoNatC c → c ⟶ c' → NoNatC c'
nonatc-red nnc-base ()
nonatc-red nnc-Unit ()
nonatc-red nnc-Fin (ξ-⌜Fin⌝ _) = nnc-Fin
nonatc-red nnc-Σ (ξ-⌜Σ⌝ˡ _) = nnc-Σ
nonatc-red nnc-Σ (ξ-⌜Σ⌝ʳ _) = nnc-Σ
nonatc-red nnc-Id (ξ-⌜Id⌝ᶜ _) = nnc-Id
nonatc-red nnc-Id (ξ-⌜Id⌝ˡ _) = nnc-Id
nonatc-red nnc-Id (ξ-⌜Id⌝ʳ _) = nnc-Id
nonatc-red (nnc-Π nd) (ξ-⌜Π⌝ˡ _) = nnc-Π nd
nonatc-red (nnc-Π nd) (ξ-⌜Π⌝ʳ r) = nnc-Π (nonatc-red nd r)
nonatc-red (nnc-Hom nc) (ξ-⌜Hom⌝ᶜ r) = nnc-Hom (nonatc-red nc r)
nonatc-red (nnc-Hom nc) (ξ-⌜Hom⌝ˡ _) = nnc-Hom nc
nonatc-red (nnc-Hom nc) (ξ-⌜Hom⌝ʳ _) = nnc-Hom nc

data NoNat {Γ} : RTy Γ → Set where
  nn-base : NoNat (base {Γ})
  nn-U    : NoNat (U {Γ})
  nn-Unit : NoNat (Unit {Γ})
  nn-El   : {c : RTm Γ} → NoNatHd c → NoNat (El c)
  nn-Π    : {F : RTy Γ} {G : RTy (Γ ∙)} → NoNat (Π F G)
  nn-Σ    : {F : RTy Γ} {G : RTy (Γ ∙)} → NoNat (Σ' F G)
  nn-Hom  : {H : RTy Γ} {a b : RTm Γ} → NoNat (Hom H a b)
  nn-Id   : {A : RTy Γ} {t u : RTm Γ} → NoNat (Id A t u)
  -- ⚠ NOT closed by an absurd reduction — the family's three slots are
  --   terms and step, so `nonat-red` has real rows below.
  nn-IMu  : {I D i : RTm Γ} → NoNat (IMu I D i)
  nn-Fin  : {n : RTm Γ} → NoNat (Fin n)

nonat-red : {A A' : RTy Γ} → NoNat A → A ⟶ᵀ A' → NoNat A'
nonat-red nn-base ()
nonat-red nn-U ()
nonat-red nn-Unit ()
nonat-red nn-Fin (ξ-Fin _) = nn-Fin
nonat-red (nn-El _)  El-⌜base⌝        = nn-base
nonat-red (nn-El _)  (El-⌜Π⌝ _ _)     = nn-Π
nonat-red (nn-El _)  (El-⌜Σ⌝ _ _)     = nn-Σ
nonat-red (nn-El _)  (El-⌜Hom⌝ _ _ _) = nn-Hom
nonat-red (nn-El _)  (El-⌜Id⌝ _ _ _)  = nn-Id
nonat-red (nn-El _)  El-⌜Unit⌝        = nn-Unit
nonat-red (nn-El _)  El-⌜Fin⌝         = nn-Fin
nonat-red (nn-El _)  El-⌜IMu⌝         = nn-IMu
nonat-red nn-IMu     (ξ-IMuᴵ _)       = nn-IMu
nonat-red nn-IMu     (ξ-IMuᴰ _)       = nn-IMu
nonat-red nn-IMu     (ξ-IMuⁱ _)       = nn-IMu
-- ★★ THE excluded case, and the only one: a ⌜Nat⌝-headed ambient.
nonat-red (nn-El ()) El-⌜Nat⌝
nonat-red (nn-El nc) (ξ-El r)        = nn-El (nonathd-red nc r)
nonat-red nn-Π (ξ-Πˡ _) = nn-Π
nonat-red nn-Π (ξ-Πʳ _) = nn-Π
nonat-red nn-Σ (ξ-Σˡ _) = nn-Σ
nonat-red nn-Σ (ξ-Σʳ _) = nn-Σ
nonat-red nn-Hom (Hom-U _ _)      = nn-Π
nonat-red nn-Hom (Hom-Π _ _ _ _)  = nn-Π
nonat-red nn-Hom (Hom-Nat-z _)    = nn-Unit
nonat-red nn-Hom (Hom-Nat-sz _)   = nn-base
nonat-red nn-Hom (Hom-Nat-ss _ _) = nn-Hom
nonat-red nn-Hom (ξ-Homᵀ _) = nn-Hom
nonat-red nn-Hom (ξ-Homˡ _) = nn-Hom
nonat-red nn-Hom (ξ-Homʳ _) = nn-Hom
nonat-red nn-Id (ξ-Idᵀ _) = nn-Id
nonat-red nn-Id (ξ-Idˡ _) = nn-Id
nonat-red nn-Id (ξ-Idʳ _) = nn-Id

Hom-nf-Unit : {A : RTy Γ} {t u : RTm Γ} → Unit {Γ} ⟶ᵀ* Hom A t u → ⊥
Hom-nf-Unit (stepᵀ () _)

Hom-nf-base : {A : RTy Γ} {t u : RTm Γ} → base {Γ} ⟶ᵀ* Hom A t u → ⊥
Hom-nf-base (stepᵀ () _)

-- ★ WF stage C: `Nat` is inert, so it is its own only reduct.
Nat-reduct : {C : RTy Γ} → Nat {Γ} ⟶ᵀ* C → C ≡ Nat
Nat-reduct doneᵀ = refl
Nat-reduct (stepᵀ () _)

-- ★ a `Hom`-to-`Hom` reduction transports `NoNat` FORWARD along the
-- ambient: it is `nonat-red` iterated, with the order rules refuted at
-- the source (they need a `Nat` ambient, which `NoNat` denies).
homAmb→ : {A A' : RTy Γ} {t u t' u' : RTm Γ} →
          Hom A t u ⟶ᵀ* Hom A' t' u' → NoNat A → NoNat A'
homAmb→ doneᵀ nn = nn
homAmb→ (stepᵀ (ξ-Homᵀ r) rest) nn = homAmb→ rest (nonat-red nn r)
homAmb→ (stepᵀ (ξ-Homˡ r) rest) nn = homAmb→ rest nn
homAmb→ (stepᵀ (ξ-Homʳ r) rest) nn = homAmb→ rest nn
homAmb→ (stepᵀ (Hom-U _ _) rest) nn with Π-reduct rest
... | mkΠRed _ _ () _ _
homAmb→ (stepᵀ (Hom-Π _ _ _ _) rest) nn with Π-reduct rest
... | mkΠRed _ _ () _ _
homAmb→ (stepᵀ (Hom-Nat-z _) rest) ()
homAmb→ (stepᵀ (Hom-Nat-sz _) rest) ()
homAmb→ (stepᵀ (Hom-Nat-ss _ _) rest) ()

-- ⚠ WF stage C: there is deliberately NO backward `homAmb←`, and no
-- `red→nonat`.  Stage B could pull `NoNat` back along a reduction
-- because "the type steps, therefore it is not `Nat`" was as strong as
-- `NoNat` itself; with the code-head index that shortcut is FALSE
-- (`El ⌜Nat⌝` steps, and is not Nat-free), and a general backward
-- transport is false too — a redex can reduce to a constructor-headed
-- code, so `NoNat (El c')` says nothing about `El c`.  Backward is not
-- needed: keying the inversion below on the TARGET ambient is what the
-- consumers actually have.
record HomRed {Γ} (A : RTy Γ) (t u : RTm Γ)
              (A' : RTy Γ) (t' u' : RTm Γ) : Set where
  constructor mkHomRed
  field
    rA : A ⟶ᵀ* A'
    rt : t ⟶* t'
    ru : u ⟶* u'

-- ★★ WF stage C: keyed on the TARGET ambient.  Stage B keyed it on the
-- source, which needed `NoNat` pulled backward along the church-rosser
-- leg — no longer available (see above), and no longer necessary: if an
-- order rule ever fires, `Hom-Nat-z`/`-sz` leave the `Hom` for good
-- (`Unit`/`base` are inert) and `Hom-Nat-ss` pins the ambient at `Nat`,
-- so landing on a Nat-FREE ambient already testifies that none fired.
-- The `ξ-Homᵀ` case now carries no guard at all.
Hom-to-Hom : {A A' : RTy Γ} {t u t' u' : RTm Γ} → NoNat A' →
             Hom A t u ⟶ᵀ* Hom A' t' u' → HomRed A t u A' t' u'
Hom-to-Hom nn doneᵀ = mkHomRed doneᵀ done done
Hom-to-Hom nn (stepᵀ (ξ-Homᵀ r) rest) with Hom-to-Hom nn rest
... | mkHomRed rA rt ru = mkHomRed (stepᵀ r rA) rt ru
Hom-to-Hom nn (stepᵀ (ξ-Homˡ r) rest) with Hom-to-Hom nn rest
... | mkHomRed rA rt ru = mkHomRed rA (step r rt) ru
Hom-to-Hom nn (stepᵀ (ξ-Homʳ r) rest) with Hom-to-Hom nn rest
... | mkHomRed rA rt ru = mkHomRed rA rt (step r ru)
Hom-to-Hom nn (stepᵀ (Hom-U c d) rest) with Π-reduct rest
... | mkΠRed _ _ () _ _
Hom-to-Hom nn (stepᵀ (Hom-Π A B f g) rest) with Π-reduct rest
... | mkΠRed _ _ () _ _
Hom-to-Hom nn (stepᵀ (Hom-Nat-z _) rest) with Hom-nf-Unit rest
... | ()
Hom-to-Hom nn (stepᵀ (Hom-Nat-sz _) rest) with Hom-nf-base rest
... | ()
-- the peeling rule keeps the ambient at `Nat`, and `Nat` is inert — so
-- the target ambient IS `Nat`, which `NoNat` refutes.
Hom-to-Hom nn (stepᵀ (Hom-Nat-ss _ _) rest) with Hom-to-Hom nn rest
... | mkHomRed rA rt ru with Nat-reduct rA
Hom-to-Hom () (stepᵀ (Hom-Nat-ss _ _) rest) | mkHomRed rA rt ru | refl

-- reducts of a `Hom` type are `Hom`- or `Π`-headed (promoted from
-- `SpikeTrLR`): what refutes the base/U/ne/Σ' interps of a path's type
-- in `fund`'s `tr` cases.
data HomΠShape {Γ : Cx} : RTy Γ → Set where
  hsΠ : {F : RTy Γ} {G : RTy (Γ ∙)} → HomΠShape (Π F G)
  hsH : {H : RTy Γ} {a b : RTm Γ} → HomΠShape (Hom H a b)
  -- ★ WF stage B: the order rules add two more possible shapes.  Every
  -- CONSUMER is a refutation at a specific shape (`U`, `Σ'`, `Id`, …),
  -- and `Unit`/`base` match none of those — so the extra arms cost the
  -- consumers nothing.  The one real casualty is `Hombase-clash`,
  -- which is now FALSE in general and correctly so (`Hom Nat 2 1`
  -- REDUCES to `base`); it is refined to an `El` ambient below.
  hsUnit : HomΠShape (Unit {Γ})
  hsBase : HomΠShape (base {Γ})

Π-shape : {Γ : Cx} {F : RTy Γ} {G : RTy (Γ ∙)} {C : RTy Γ} →
          Π F G ⟶ᵀ* C → HomΠShape C
Π-shape doneᵀ                 = hsΠ
Π-shape (stepᵀ (ξ-Πˡ r) rest) = Π-shape rest
Π-shape (stepᵀ (ξ-Πʳ r) rest) = Π-shape rest

hom-shape : {Γ : Cx} {A : RTy Γ} {t u : RTm Γ} {C : RTy Γ} →
            Hom A t u ⟶ᵀ* C → HomΠShape C
hom-shape doneᵀ                    = hsH
hom-shape (stepᵀ (ξ-Homᵀ r) rest)  = hom-shape rest
hom-shape (stepᵀ (ξ-Homˡ r) rest)  = hom-shape rest
hom-shape (stepᵀ (ξ-Homʳ r) rest)  = hom-shape rest
hom-shape (stepᵀ (Hom-U c d) rest)     = Π-shape rest
hom-shape (stepᵀ (Hom-Π A B f g) rest) = Π-shape rest
hom-shape (stepᵀ (Hom-Nat-z n) doneᵀ)        = hsUnit
hom-shape (stepᵀ (Hom-Nat-z n) (stepᵀ () _))
hom-shape (stepᵀ (Hom-Nat-sz m) doneᵀ)       = hsBase
hom-shape (stepᵀ (Hom-Nat-sz m) (stepᵀ () _))
hom-shape (stepᵀ (Hom-Nat-ss m n) rest)      = hom-shape rest


-- ★ WF stage B: the SHARP shape lemma.  `hom-shape` had to gain
-- `Unit`/`base` arms because a `Nat`-ambient hom really does reduce to
-- them; at every ambient that is not `Nat` the old two-shape
-- conclusion still holds, and `fund`'s `⊢trU` case (ambient pinned to
-- `U`) needs exactly that.
data HomΠShapeN {Γ : Cx} : RTy Γ → Set where
  hsnΠ : {F : RTy Γ} {G : RTy (Γ ∙)} → HomΠShapeN (Π F G)
  hsnH : {H : RTy Γ} {a b : RTm Γ} → HomΠShapeN (Hom H a b)

Π-shapeN : {Γ : Cx} {F : RTy Γ} {G : RTy (Γ ∙)} {C : RTy Γ} →
           Π F G ⟶ᵀ* C → HomΠShapeN C
Π-shapeN doneᵀ                 = hsnΠ
Π-shapeN (stepᵀ (ξ-Πˡ r) rest) = Π-shapeN rest
Π-shapeN (stepᵀ (ξ-Πʳ r) rest) = Π-shapeN rest

hom-shapeN : {Γ : Cx} {A : RTy Γ} {t u : RTm Γ} {C : RTy Γ} →
             NoNat A → Hom A t u ⟶ᵀ* C → HomΠShapeN C
hom-shapeN nn doneᵀ                    = hsnH
hom-shapeN nn (stepᵀ (ξ-Homᵀ r) rest)  = hom-shapeN (nonat-red nn r) rest
hom-shapeN nn (stepᵀ (ξ-Homˡ r) rest)  = hom-shapeN nn rest
hom-shapeN nn (stepᵀ (ξ-Homʳ r) rest)  = hom-shapeN nn rest
hom-shapeN nn (stepᵀ (Hom-U c d) rest)     = Π-shapeN rest
hom-shapeN nn (stepᵀ (Hom-Π A B f g) rest) = Π-shapeN rest
hom-shapeN () (stepᵀ (Hom-Nat-z _) rest)
hom-shapeN () (stepᵀ (Hom-Nat-sz _) rest)
hom-shapeN () (stepᵀ (Hom-Nat-ss _ _) rest)

homred-inv : {P : RTy Γ → Set} →
             (∀ {X Y : RTy Γ} → P X → X ⟶ᵀ Y → P Y) →
             (P U → ⊥) →
             (∀ {F : RTy Γ} {G : RTy (Γ ∙)} → P (Π F G) → ⊥) →
             {- ★ WF stage B: …and the ambient is not `Nat`. -}
             (P (Nat {Γ}) → ⊥) →
             {A : RTy Γ} {t u : RTm Γ} {C : RTy Γ} →
             P A → Hom A t u ⟶ᵀ* C →
             Σ (RTy Γ) (λ A' → Σ (RTm Γ) (λ t' → Σ (RTm Γ) (λ u' →
               (C ≡ Hom A' t' u') × ((t ⟶* t') × (u ⟶* u')))))
homred-inv pres noU noΠ noN pA doneᵀ = _ , (_ , (_ , (refl , (done , done))))
homred-inv pres noU noΠ noN pA (stepᵀ (ξ-Homᵀ r) rest) =
  homred-inv pres noU noΠ noN (pres pA r) rest
homred-inv pres noU noΠ noN pA (stepᵀ (ξ-Homˡ r) rest)
  with homred-inv pres noU noΠ noN pA rest
... | A' , (t' , (u' , (eq , (rt , ru)))) =
      A' , (t' , (u' , (eq , (step r rt , ru))))
homred-inv pres noU noΠ noN pA (stepᵀ (ξ-Homʳ r) rest)
  with homred-inv pres noU noΠ noN pA rest
... | A' , (t' , (u' , (eq , (rt , ru)))) =
      A' , (t' , (u' , (eq , (rt , step r ru))))
homred-inv pres noU noΠ noN pA (stepᵀ (Hom-U c d) rest) with noU pA
... | ()
homred-inv pres noU noΠ noN pA (stepᵀ (Hom-Π A B f g) rest) with noΠ pA
... | ()
homred-inv pres noU noΠ noN pA (stepᵀ (Hom-Nat-z _) rest) with noN pA
... | ()
homred-inv pres noU noΠ noN pA (stepᵀ (Hom-Nat-sz _) rest) with noN pA
... | ()
homred-inv pres noU noΠ noN pA (stepᵀ (Hom-Nat-ss _ _) rest) with noN pA
... | ()

data BaseAmb {Γ} : RTy Γ → Set where
  ba-el   : BaseAmb (El (⌜base⌝ {Γ}))
  ba-base : BaseAmb (base {Γ})

baseamb-red : {X Y : RTy Γ} → BaseAmb X → X ⟶ᵀ Y → BaseAmb Y
baseamb-red ba-el El-⌜base⌝ = ba-base
baseamb-red ba-el (ξ-El ())
baseamb-red ba-base ()

data ΣAmb {Γ} : RTy Γ → Set where
  sa-el : {c : RTm Γ} {d : RTm (Γ ∙)} → ΣAmb (El (⌜Σ⌝ c d))
  sa-Σ  : {A : RTy Γ} {B : RTy (Γ ∙)} → ΣAmb (Σ' A B)

σamb-red : {X Y : RTy Γ} → ΣAmb X → X ⟶ᵀ Y → ΣAmb Y
σamb-red sa-el (El-⌜Σ⌝ c d)      = sa-Σ
σamb-red sa-el (ξ-El (ξ-⌜Σ⌝ˡ r)) = sa-el
σamb-red sa-el (ξ-El (ξ-⌜Σ⌝ʳ r)) = sa-el
σamb-red sa-Σ  (ξ-Σˡ r)          = sa-Σ
σamb-red sa-Σ  (ξ-Σʳ r)          = sa-Σ

U-reduct : {C : RTy Γ} → U ⟶ᵀ* C → C ≡ U
U-reduct doneᵀ        = refl
U-reduct (stepᵀ () _)

data HomToΠ {Γ} (A : RTy Γ) (t u : RTm Γ)
            (P : RTy Γ) (Q : RTy (Γ ∙)) : Set where
  via-U : {t₁ u₁ : RTm Γ} →
          A ⟶ᵀ* U → t ⟶* t₁ → u ⟶* u₁ →
          El t₁ ⟶ᵀ* P → El (renTm vs u₁) ⟶ᵀ* Q →
          HomToΠ A t u P Q
  via-Π : {F : RTy Γ} {G : RTy (Γ ∙)} →
          A ⟶ᵀ* Π F G →
          HomToΠ A t u P Q

hom-to-Π : {A : RTy Γ} {t u : RTm Γ} {P : RTy Γ} {Q : RTy (Γ ∙)} → NoNat A →
           Hom A t u ⟶ᵀ* Π P Q → HomToΠ A t u P Q
hom-to-Π nn (stepᵀ (ξ-Homᵀ r) rest) with hom-to-Π (nonat-red nn r) rest
... | via-U rA rt ru rP rQ = via-U (stepᵀ r rA) rt ru rP rQ
... | via-Π rA             = via-Π (stepᵀ r rA)
hom-to-Π nn (stepᵀ (ξ-Homˡ r) rest) with hom-to-Π nn rest
... | via-U rA rt ru rP rQ = via-U rA (step r rt) ru rP rQ
... | via-Π rA             = via-Π rA
hom-to-Π nn (stepᵀ (ξ-Homʳ r) rest) with hom-to-Π nn rest
... | via-U rA rt ru rP rQ = via-U rA rt (step r ru) rP rQ
... | via-Π rA             = via-Π rA
hom-to-Π nn (stepᵀ (Hom-U c d) rest) with Π-reduct rest
... | mkΠRed _ _ refl rP rQ = via-U doneᵀ done done rP rQ
hom-to-Π nn (stepᵀ (Hom-Π A B f g) rest) = via-Π doneᵀ
hom-to-Π () (stepᵀ (Hom-Nat-z _) rest)
hom-to-Π () (stepᵀ (Hom-Nat-sz _) rest)
hom-to-Π () (stepᵀ (Hom-Nat-ss _ _) rest)

-- transporting the payload's type across convertible endpoints
mono-El[] : (d₀ : RTm (Γ ∙)) {t w : RTm Γ} → t ⟶* w →
            El (subTm (single t) d₀) ≅ᵀ El (subTm (single w) d₀)
mono-El[] d₀ r = red→≅ᵀ (⟶ᵀ*-El (subTm-monoˢ (single-mono r) d₀))

-- inversion of a step on a `⌜Hom⌝`-headed term
data HomStep {Γ} (c a m : RTm Γ) : RTm Γ → Set where
  hsᶜ : {c' : RTm Γ} → c ⟶ c' → HomStep c a m (⌜Hom⌝ c' a m)
  hsˡ : {a' : RTm Γ} → a ⟶ a' → HomStep c a m (⌜Hom⌝ c a' m)
  hsʳ : {m' : RTm Γ} → m ⟶ m' → HomStep c a m (⌜Hom⌝ c a m')

hom-step : {c a m x : RTm Γ} → ⌜Hom⌝ c a m ⟶ x → HomStep c a m x
hom-step (ξ-⌜Hom⌝ᶜ r) = hsᶜ r
hom-step (ξ-⌜Hom⌝ˡ r) = hsˡ r
hom-step (ξ-⌜Hom⌝ʳ r) = hsʳ r


------------------------------------------------------------------------
-- ★★ LEVITATION: the substitution facts the levitated rules need.
--   All are σ-calculus: fuse, then compare pointwise.
------------------------------------------------------------------------

-- a term conversion lifts through any reduction-monotone type context.
conv-lift : {Γ : Cx} (F : RTm Γ → RTy Γ) → (∀ {a b} → a ⟶* b → F a ⟶ᵀ* F b) →
            {a b : RTm Γ} → a ≅ b → F a ≅ᵀ F b
conv-lift F m c with church-rosser c
... | w , (r₁ , r₂) = ctrnᵀ (red→≅ᵀ (m r₁)) (csymᵀ (red→≅ᵀ (m r₂)))

El-≅ : {Γ : Cx} {a b : RTm Γ} → a ≅ b → El a ≅ᵀ El b
El-≅ = conv-lift El ⟶ᵀ*-El

Desc-≅ : {Γ : Cx} {a b : RTm Γ} → a ≅ b → Desc a ≅ᵀ Desc b
Desc-≅ = conv-lift Desc ⟶ᵀ*-Desc

-- `dσ`'s branch applied to the fresh payload variable
wk-app-vzᵗ : {Γ : Cx} (t : RTm Γ) →
            subTm (single (var vz)) (renTm (extR vs) (renTm vs t)) ≡ renTm vs t
wk-app-vzᵗ t =
  trans (cong (subTm (single (var vz)))
              (trans (renTm-renTm t) (sym (renTm-renTm {ρ' = vs} {ρ = vs} t))))
        (wk-cancel-tm (var vz) (renTm vs t))

-- two weakenings, then the method's two instantiations, cancel
ww-cancel : {Γ : Cx} (a b t : RTm Γ) →
            subTm (single a) (subTm (extS (single b)) (renTm vs (renTm vs t))) ≡ t
ww-cancel a b t =
  trans (subTm-subTm (renTm vs (renTm vs t)))
    (trans (subTm-renTm (renTm vs t))
      (trans (subTm-renTm t) (trans (subTm-cong (λ _ → refl) t) (subTm-id t))))

-- the method's hypothesis motive, instantiated at `i` then `p`, is `M`
wk2M-cancel : {Γ : Cx} (p i : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
              subTy (extS (extS (single p))) (subTy (extS (extS (extS (single i)))) (wk2M M)) ≡ M
wk2M-cancel p i M =
  trans (subTy-subTy (wk2M M))
    (trans (subTy-renTy M)
      (trans (subTy-cong (λ { vz → refl ; (vs vz) → refl ; (vs (vs y)) → refl }) M)
             (subTy-id M)))

-- the method's conclusion, at `i`, `p`, `h`, is the motive at `con p`
meth-inst : {Γ : Cx} (h p i : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
            subTy (single h) (subTy (extS (single p)) (subTy (extS (extS (single i))) (subTy methS M)))
            ≡ iinst i (con p) M
meth-inst h p i M =
  trans (cong (subTy (single h)) (cong (subTy (extS (single p))) (subTy-subTy M)))
    (trans (cong (subTy (single h)) (subTy-subTy M))
      (trans (subTy-subTy M)
        (trans (subTy-cong ptw M) (sym (subTy-subTy M)))))
  where
  ptw : ∀ x → (single h ∘ₛ (extS (single p) ∘ₛ (extS (extS (single i)) ∘ₛ methS))) x
              ≡ (single (con p) ∘ₛ extS (single i)) x
  ptw vz          = cong con (wk-cancel-tm h p)
  ptw (vs vz)     = trans (ww-cancel h p i) (sym (wk-cancel-tm (con p) i))
  ptw (vs (vs y)) = refl

-- `fcase`'s successor branch, instantiated at the predecessor
fsucS-inst : {Γ : Cx} (t : RTm Γ) (P : RTy (Γ ∙)) →
             subTy (single t) (subTy fsucS P) ≡ subTy (single (fsuc t)) P
fsucS-inst t P =
  trans (subTy-subTy P) (subTy-cong (λ { vz → refl ; (vs x) → refl }) P)

-- `psplit`'s body, instantiated at both halves
pairS-inst : {Γ : Cx} (x y : RTm Γ) (P : RTy (Γ ∙)) →
             subTy (single2 x y) (subTy pairS P) ≡ subTy (single (pair x y)) P
pairS-inst x y P =
  trans (subTy-subTy P) (subTy-cong (λ { vz → refl ; (vs z) → refl }) P)

s2-wk : {Γ : Cx} (x y : RTm Γ) (B : RTy (Γ ∙)) →
        subTy (single2 x y) (renTy vs B) ≡ subTy (single x) B
s2-wk x y B = trans (subTy-renTy B) (subTy-cong (λ { vz → refl ; (vs z) → refl }) B)

s2-cancel : {Γ : Cx} (x y : RTm Γ) (A : RTy Γ) →
            subTy (single2 x y) (renTy vs (renTy vs A)) ≡ A
s2-cancel x y A =
  trans (subTy-renTy (renTy vs A))
    (trans (subTy-renTy A) (trans (subTy-cong (λ _ → refl) A) (subTy-id A)))

-- the payload of `p : El (dpay I D (D i))` (the fibre over `i`) at
--   `i ≅ i'`, `I ≅ I'`, `D ≅ D'`
dpay-≅ : {Γ : Cx} {I I' D D' i i' : RTm Γ} → I ≅ I' → D ≅ D' → i ≅ i' →
         El (dpay I D (app D i)) ≅ᵀ El (dpay I' D' (app D' i'))
dpay-≅ {I' = I'} {D = D} {D' = D'} {i = i} {i' = i'} cI cD ci =
  ctrnᵀ (conv-lift (λ x → El (dpay x D (app D i))) (λ r → ⟶ᵀ*-El (⟶*-dpayᴵ r)) cI)
    (ctrnᵀ (conv-lift (λ x → El (dpay I' x (app x i)))
                      (λ r → ⟶ᵀ*-El (⟶*-trans (⟶*-dpayᴰ r) (⟶*-dpayᶜ (⟶*-appˡ r)))) cD)
           (conv-lift (λ x → El (dpay I' D' (app D' x))) (λ r → ⟶ᵀ*-El (⟶*-dpayᶜ (⟶*-appʳ r))) ci))

-- ★ D074: a stepped index code steps the type of its descriptions
DescF-step : {Γ : Cx} {I I' : RTm Γ} → I ⟶ I' → DescF I ≅ᵀ DescF I'
DescF-step r = ctrnᵀ (credᵀ (ξ-Πˡ (ξ-El r))) (credᵀ (ξ-Πʳ (ξ-Desc (⟶-ren vs r))))


------------------------------------------------------------------------
-- ★ W2b (G1) — the pw DECODE JOINS (promoted from SpikeCanon), the
-- stable-code ambient analysis, and the typing lemmas the three new
-- rules' subject-reduction cases assemble from.
------------------------------------------------------------------------

-- `Hom` over a pw-able code's decoding reduces to a Π whose body is
-- ALSO reached from the pointwise-body code's decoding (a JOIN — on
-- deeper spines the left side unfolds one `El-⌜Hom⌝` step further).
pw-Hom-decode :
  (C : RTm Γ) → pw? C ≡ true → (x y : RTm Γ) →
  Σ (RTy (Γ ∙)) (λ Body →
    (Hom (El C) x y ⟶ᵀ* Π (El (pwDom C)) Body)
    × (Hom (El (pwBody C)) (app (renTm vs x) (var vz))
                           (app (renTm vs y) (var vz)) ⟶ᵀ* Body))
pw-Hom-decode (var v) () x y
pw-Hom-decode (lam t) () x y
pw-Hom-decode (app t u) () x y
pw-Hom-decode (pair a b) () x y
pw-Hom-decode (fst t) () x y
pw-Hom-decode (snd t) () x y
pw-Hom-decode ⌜base⌝ () x y
pw-Hom-decode (⌜Π⌝ γ δ) h x y =
  ( Hom (El δ) (app (renTm vs x) (var vz)) (app (renTm vs y) (var vz))
  , ( stepᵀ (ξ-Homᵀ (El-⌜Π⌝ γ δ))
      (stepᵀ (Hom-Π (El γ) (El δ) x y) doneᵀ)
    , doneᵀ ) )
pw-Hom-decode (⌜Σ⌝ c d) () x y
pw-Hom-decode (⌜Hom⌝ C a b) h x y with pw-Hom-decode C h a b
... | Body' , (c₁ , c₂) =
  ( Hom Body' (app (renTm vs x) (var vz)) (app (renTm vs y) (var vz))
  , ( stepᵀ (ξ-Homᵀ (El-⌜Hom⌝ C a b))
      (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ c₁)
        (stepᵀ (Hom-Π (El (pwDom C)) Body' x y) doneᵀ))
    , stepᵀ (ξ-Homᵀ (El-⌜Hom⌝ (pwBody C)
                              (app (renTm vs a) (var vz))
                              (app (renTm vs b) (var vz))))
            (⟶ᵀ*-Homᵀ c₂) ) )
pw-Hom-decode (hrefl c t) () x y
pw-Hom-decode (tr d p e) () x y

-- ...and the same join for the bare decoding.
pw-El-decode :
  (C : RTm Γ) → pw? C ≡ true →
  Σ (RTy (Γ ∙)) (λ Body →
    (El C ⟶ᵀ* Π (El (pwDom C)) Body) × (El (pwBody C) ⟶ᵀ* Body))
pw-El-decode (var v) ()
pw-El-decode (lam t) ()
pw-El-decode (app t u) ()
pw-El-decode (pair a b) ()
pw-El-decode (fst t) ()
pw-El-decode (snd t) ()
pw-El-decode ⌜base⌝ ()
pw-El-decode (⌜Π⌝ γ δ) h =
  ( El δ , ( stepᵀ (El-⌜Π⌝ γ δ) doneᵀ , doneᵀ ) )
pw-El-decode (⌜Σ⌝ c d) ()
pw-El-decode (⌜Hom⌝ C a b) h with pw-Hom-decode C h a b
... | Body' , (c₁ , c₂) =
  ( Body'
  , ( stepᵀ (El-⌜Hom⌝ C a b) c₁
    , stepᵀ (El-⌜Hom⌝ (pwBody C)
                      (app (renTm vs a) (var vz))
                      (app (renTm vs b) (var vz))) c₂ ) )
pw-El-decode (hrefl c t) ()
pw-El-decode (tr d p e) ()

-- STABLE-CODE AMBIENTS (the `BaseAmb`/`ΣAmb` pattern, powered by
-- `stkC?-red`): the decoded type of a `stkC?` code never reaches `U`
-- or `Π` — what `tr-J-Hom`'s sr feeds `homred-inv`.
data StkAmb {Γ : Cx} : RTy Γ → Set where
  st-el   : {c : RTm Γ} → stkA? c ≡ true → StkAmb (El c)
  st-base : StkAmb base
  st-Σ    : {A : RTy Γ} {B : RTy (Γ ∙)} → StkAmb (Σ' A B)
  st-hom  : {H : RTy Γ} {a b : RTm Γ} → StkAmb H → StkAmb (Hom H a b)
  st-Id   : {A : RTy Γ} {t u : RTm Γ} → StkAmb (Id A t u)
  -- ★ WF stage C: `⌜Unit⌝` IS a stable code, so its decode joins the
  -- stable ambients.
  st-Unit : StkAmb (Unit {Γ})
  -- ★ `IMu I D i` is never `U`, never `Π` — but its slots reduce, so
  --   it is INERT-SHAPED, not inert.  `Fin n` is inert.
  st-IMu  : {I D i : RTm Γ} → StkAmb (IMu I D i)
  st-Fin  : {n : RTm Γ} → StkAmb (Fin n)
  -- ★★ SpikeNatJ: `Nat` IS a stable ambient.  `StkAmb A` means "A never
  -- becomes `U` or `Π`", NOT "A is stuck" — that second notion is LR's
  -- `StkHd`, and the two must not be confused.  `Nat` is inert, and a
  -- `Hom` over it computes only to `Unit`/`base`/`Hom Nat _ _`, none of
  -- which is a Π — so the order rules are absorbed below rather than
  -- refuted.  This is why the key is `stkA?`, not `stkC?`.
  st-Nat  : StkAmb (Nat {Γ})

stamb-red : {A A' : RTy Γ} → StkAmb A → A ⟶ᵀ A' → StkAmb A'
stamb-red (st-el {c = ⌜base⌝} k) El-⌜base⌝ = st-base
stamb-red (st-el {c = ⌜Σ⌝ c d} k) (El-⌜Σ⌝ _ _) = st-Σ
stamb-red (st-el {c = ⌜Id⌝ c a b} k) (El-⌜Id⌝ _ _ _) = st-Id
stamb-red (st-el {c = ⌜Unit⌝} k) El-⌜Unit⌝ = st-Unit
stamb-red (st-el {c = ⌜Fin⌝ _} k) El-⌜Fin⌝ = st-Fin
stamb-red (st-el {c = ⌜IMu⌝ _ _ _} k) El-⌜IMu⌝ = st-IMu
stamb-red st-IMu (ξ-IMuᴵ r) = st-IMu
stamb-red st-IMu (ξ-IMuᴰ r) = st-IMu
stamb-red st-IMu (ξ-IMuⁱ r) = st-IMu
stamb-red st-Fin (ξ-Fin r) = st-Fin
stamb-red (st-el {c = ⌜Nat⌝} k) El-⌜Nat⌝ = st-Nat
stamb-red st-Nat ()
stamb-red st-Unit ()
stamb-red st-Id (ξ-Idᵀ r) = st-Id
stamb-red st-Id (ξ-Idˡ r) = st-Id
stamb-red st-Id (ξ-Idʳ r) = st-Id
stamb-red (st-el {c = ⌜Π⌝ c d} ()) (El-⌜Π⌝ _ _)
stamb-red (st-el {c = ⌜Hom⌝ c a b} k) (El-⌜Hom⌝ _ _ _) =
  st-hom (st-el k)
stamb-red (st-el k) (ξ-El r) = st-el (stkA?-red r k)
stamb-red st-Σ (ξ-Σˡ r) = st-Σ
stamb-red st-Σ (ξ-Σʳ r) = st-Σ
stamb-red (st-hom sh) (ξ-Homᵀ r) = st-hom (stamb-red sh r)
stamb-red (st-hom sh) (ξ-Homˡ r) = st-hom sh
stamb-red (st-hom sh) (ξ-Homʳ r) = st-hom sh
stamb-red (st-hom ()) (Hom-U _ _)
stamb-red (st-hom ()) (Hom-Π _ _ _ _)
-- ★★ the ORDER RULES, absorbed: a `Nat`-ambient hom leaves for `Unit`
-- or `base` (both inert) or peels back to a `Nat`-ambient hom.  None is
-- a Π, which is all `StkAmb` claims.
stamb-red (st-hom st-Nat) (Hom-Nat-z _)    = st-Unit
stamb-red (st-hom st-Nat) (Hom-Nat-sz _)   = st-base
stamb-red (st-hom st-Nat) (Hom-Nat-ss _ _) = st-hom st-Nat

stamb-noU : StkAmb (U {Γ}) → ⊥
stamb-noU ()

stamb-noΠ : {F : RTy Γ} {G : RTy (Γ ∙)} → StkAmb (Π F G) → ⊥
stamb-noΠ ()

-- ★★ SpikeNatJ: `StkAmb` alone no longer excludes `Nat` — `st-Nat` is
-- a constructor now, because `StkAmb` claims "never Π/U", not "stuck".
-- `homred-inv` genuinely NEEDS the ambient to be non-`Nat` (a `Nat`
-- ambient's hom leaves for `Unit`/`base` and stops being a hom at
-- all), so its predicate is the CONJUNCTION with `NoNat`.  Every call
-- site already had both facts to hand.
StkNN : RTy Γ → Set
StkNN A = StkAmb A × NoNat A

stknn-red : {A A' : RTy Γ} → StkNN A → A ⟶ᵀ A' → StkNN A'
stknn-red (sa , nn) r = (stamb-red sa r , nonat-red nn r)

stknn-noU : StkNN (U {Γ}) → ⊥
stknn-noU (() , _)

stknn-noΠ : {F : RTy Γ} {G : RTy (Γ ∙)} → StkNN (Π F G) → ⊥
stknn-noΠ (() , _)

stknn-noN : StkNN (Nat {Γ}) → ⊥
stknn-noN (_ , ())

-- conversion is a congruence at the `Hom` ambient.
≅ᵀ-Homᵀ : {A B : RTy Γ} {t u : RTm Γ} →
          A ≅ᵀ B → Hom A t u ≅ᵀ Hom B t u
≅ᵀ-Homᵀ (credᵀ r)   = credᵀ (ξ-Homᵀ r)
≅ᵀ-Homᵀ crflᵀ       = crflᵀ
≅ᵀ-Homᵀ (csymᵀ c)   = csymᵀ (≅ᵀ-Homᵀ c)
≅ᵀ-Homᵀ (ctrnᵀ c d) = ctrnᵀ (≅ᵀ-Homᵀ c) (≅ᵀ-Homᵀ d)

-- instantiating a weakened TYPE at the fresh variable is the identity
-- (the `wk-inst` pattern, at `RTy`).
wk-inst-ty : (B : RTy (Γ ∙)) →
             subTy (single (var vz)) (renTy (extR vs) B) ≡ B
wk-inst-ty B =
  trans (subTy-renTy B) (trans (subTy-cong bridge B) (subTy-id B))
  where
  bridge : ∀ x → (single (var vz) ₛ∘ᵣ extR vs) x ≡ var x
  bridge vz     = refl
  bridge (vs x) = refl
