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
module DirectedHoTT.Metatheory.SubjectReduction where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ ; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var
        ; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝
        ; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub; Id-cong₃; ⌜Id⌝-cong₃
        ; jsub-cong₃; Unit; Nat; unit; nzero; nsuc; natrec; ⌜Nat⌝; ⌜Unit⌝
        ; ⌜Mu⌝; Ren; extR; renTm; renTy; Sub; extS; subTm; subTy; idₛ; _∘ᵣ_
        ; _ₛ∘ᵣ_; _ᵣ∘ₛ_; _∘ₛ_; subTy-renTy; renTy-subTy; subTy-subTy
        ; renTy-renTy; subTy-cong; renTy-cong; subTy-id; subTm-renTm
        ; subTm-id; subTm-cong; renTm-renTm; renTm-subTm; ⌜Hom⌝-cong₃
        ; Hom-cong₃; ordtr-cong₅; Desc; Mu; con; elim; lookupD; sel; fields
        ; DCon; dι; dρ; dκ; dnil; _◃_; payTy; payTy-ren; payTy-sub; _∈D_
        ; hereD; thereD; ihs; IMu; icon; ielim; ⌜IMu⌝; ICon; IDesc; iι; iρ
        ; iκ; inil; _◂_; ipayTy; ilookupD; _∈ID_; hereID; thereID; iihs
        ; ifields; εwkTy; εwk-ren; εwk-sub; εwkTm; εwkTm-ren; εwkTm-sub
        ; ipayTy-ren; ipayTy-sub; iext; isingle; ipayTy-cong; subTm-subTm
        ; iext-ren; iext-sub; ipayTy-renⁱ; ipayTy-subⁱ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; _∨_; occTm; ∨-false; ∨-false₁; ∨-false₂
        ; occ-ren-eq; occ-sub; eqv; Avoids; occ-ren-tm; avoids-wk
        ; PosC; posc-var; posc-Hom; posc-ren; posc-sub
        ; pw?; stkC?; pwDom; pwBody; pwShift
        ; pw?-sub; stkC?-sub; pwBody-sub; pwDom-sub
        ; pwBody-occ; ren-as-sub; avoids-pwShift; subTm-occ
        ; stkC?-ren; wk-ren-tm; wk-sub-tm; flat?; flat→stk; flat?-ren; flat?-sub
        ; NoNatC; nnc-base; nnc-Unit; nnc-Π; nnc-Σ; nnc-Hom; nnc-Id
        ; nonatc-ren; nonatc-sub; nonatc-pwBody
        ; stkA?; stkA?-ren; stkA?-sub; stkC?→stkA?
        ; NoNatHd; nnh-base; nnh-Unit; nnh-Σ; nnh-Id; nnh-Π; nnh-Hom; nnh-Mu; nnh-IMu
        ; nonatc→hd; stkC?→hd
        ; occ-sel; occ-fields; occ-ifields; occ-iihs; occ-εwkTm )
open import DirectedHoTT.Spec.Typing
  using ( single; nrs; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝
        ; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss
        ; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; tr-J-base; tr-J-Σ; tr-J-Id; tr-J-Unit; tr-J-Mu; tr-J-IMu; tr-taut; hrefl-pw; tr-J-Hom; tr-pw
        ; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜Mu⌝
        ; El-⌜IMu⌝; ξ-IMu
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ
        ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; El-⌜Id⌝; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ
        ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _⟶*_; done; step
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢absurd; ⊢ordtr; ⊢trU
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢ap; ⊢conv
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec; ⊢⌜Nat⌝; ⊢⌜Unit⌝; ⊢⌜Mu⌝
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom; ty-Id; ty-Unit; ty-Nat
        ; ⊢ctx_; c-◇; c-▹
        ; ι-elim; ξ-con; ξ-elimᵐ; ξ-elimᵗ
        ; ι-ielim; ξ-icon; ξ-ielimⁱ; ξ-ielimᵐ; ξ-ielimᵗ; ξ-⌜IMu⌝
        ; ihTy; atCon; conS; methTy; methsTy; methsTyFrom; atCon-inst; ty-Mu; ⊢con; ⊢elim
        ; DescWf
        ; wk-single; iinst; iihTy; iconS; iatCon; iatCon-inst
        ; imethTy; imethsTy; imethsTyFrom; IDescWf
        ; ty-IMu; ⊢icon; ⊢ielim; ⊢⌜IMu⌝; IConWf; iwf-ρ; iwf-κ; IDescWfFrom; idwf-cons; idwf-nil; _≅_; csym; ctrn; cred; crfl )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ≅ᵀ-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶-ren; ⟶*-ren; ⟶*-appʳ; ren-comm; subTm-monoˢ; extS-mono; single-mono
        ; stkC?-red; stkA?-red; church-rosser )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( sub-comm; ⟶ᵀ-sub )
open import DirectedHoTT.Metatheory.Injectivity
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El
        ; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ
        ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; red→≅ᵀ; Π-inj; Σ-inj
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; Id-reduct
        ; church-rosserᵀ; Π-reduct; ΠRed; mkΠRed
        ; Mu-inj; ⟶ᵀ*-IMu; IMu-inj; IMu-reduct; IMuRed; mkIMuRed )

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

open import DirectedHoTT.Metatheory.TySub public

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
nonathd-red nnh-IMu (ξ-⌜IMu⌝ _) = nnh-IMu
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
  nn-Mu   : {Dᵐ : Desc} → NoNat (Mu {Γ} Dᵐ)
  -- ⚠ unlike `nn-Mu`, this one is NOT closed by an absurd reduction —
  --   `ξ-IMu` steps the index, so `nonat-red` has a real row below.
  nn-IMu  : {D : IDesc} {I : RTy ε} {i : RTm Γ} → NoNat (IMu D I i)

nonat-red : {A A' : RTy Γ} → NoNat A → A ⟶ᵀ A' → NoNat A'
nonat-red nn-base ()
nonat-red nn-U ()
nonat-red nn-Unit ()
nonat-red nn-Mu ()
nonat-red (nn-El _)  El-⌜base⌝        = nn-base
nonat-red (nn-El _)  (El-⌜Π⌝ _ _)     = nn-Π
nonat-red (nn-El _)  (El-⌜Σ⌝ _ _)     = nn-Σ
nonat-red (nn-El _)  (El-⌜Hom⌝ _ _ _) = nn-Hom
nonat-red (nn-El _)  (El-⌜Id⌝ _ _ _)  = nn-Id
nonat-red (nn-El _)  El-⌜Unit⌝        = nn-Unit
nonat-red (nn-El _)  El-⌜Mu⌝          = nn-Mu
nonat-red (nn-El _)  El-⌜IMu⌝         = nn-IMu
nonat-red nn-IMu     (ξ-IMu _)        = nn-IMu
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


-- lifting an index CONVERSION to the payload type, via church-rosser.
ipayTy-conv : (D : IDesc) (I : RTy ε) (C : ICon (ε ∙)) {i i' : RTm Γ} →
              i ≅ i' → ipayTy D I (isingle i) C ≅ᵀ ipayTy D I (isingle i') C
ipayTy-conv D I C c with church-rosser c
... | w , (ri , ri') =
      -- ⚠ THE ENVIRONMENTS MUST BE PINNED.  `isingle` is a DEFINED
      --   function, so it is not injective and Agda cannot solve
      --   `σ' vz = w` for `σ'`.  Same trap as `IHAt`/`IndPW`.
      ctrnᵀ (red→≅ᵀ (ipayTy-mono D I {σ = isingle _} {σ' = isingle w} C
                                 (λ { vz → ri })))
            (csymᵀ (red→≅ᵀ (ipayTy-mono D I {σ = isingle _} {σ' = isingle w} C
                                        (λ { vz → ri' }))))

------------------------------------------------------------------------
-- Generation (inversion through `⊢conv`).
------------------------------------------------------------------------

gen-lam : {Γ : Ctx} {s : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} → Γ ⊢ lam s ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (C ≅ᵀ Π A B) × ((Γ ⊢ty A) × ((Γ ▹ A) ⊢ s ∷ B))))
-- ⚠ now also returns the DOMAIN's well-formedness: `sr`'s `ξ-lam` case
-- reconstructs a `⊢lam`, which needs it (2026-07-30, option A).
gen-lam (⊢lam dA d) = _ , (_ , (crflᵀ , (dA , d)))
gen-lam (⊢conv d c) with gen-lam d
... | A , (B , (c' , (dA , ds))) = A , (B , (ctrnᵀ (csymᵀ c) c' , (dA , ds)))

gen-app : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ app t u ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ t ∷ Π A B) × ((Γ ⊢ u ∷ A) × (C ≅ᵀ subTy (single u) B))))
gen-app (⊢app d₁ d₂) = _ , (_ , (d₁ , (d₂ , crflᵀ)))
gen-app (⊢conv d c) with gen-app d
... | A , (B , (d₁ , (d₂ , c'))) = A , (B , (d₁ , (d₂ , ctrnᵀ (csymᵀ c) c')))

gen-pair : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ pair a b ∷ C →
           Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
             (C ≅ᵀ Σ' A B) ×
             (((Γ ▹ A) ⊢ty B) × ((Γ ⊢ a ∷ A) × (Γ ⊢ b ∷ subTy (single a) B)))))
-- ⚠ likewise returns the CODOMAIN's well-formedness, for `sr`'s `ξ-pair*`.
gen-pair (⊢pair dB da db) = _ , (_ , (crflᵀ , (dB , (da , db))))
gen-pair (⊢conv d c) with gen-pair d
... | A , (B , (c' , (dB , (da , db)))) =
      A , (B , (ctrnᵀ (csymᵀ c) c' , (dB , (da , db))))

gen-fst : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fst p ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ p ∷ Σ' A B) × (C ≅ᵀ A)))
gen-fst (⊢fst d) = _ , (_ , (d , crflᵀ))
gen-fst (⊢conv d c) with gen-fst d
... | A , (B , (dp , c')) = A , (B , (dp , ctrnᵀ (csymᵀ c) c'))

gen-snd : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ snd p ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B →
            (Γ ⊢ p ∷ Σ' A B) × (C ≅ᵀ subTy (single (fst p)) B)))
gen-snd (⊢snd d) = _ , (_ , (d , crflᵀ))
gen-snd (⊢conv d c) with gen-snd d
... | A , (B , (dp , c')) = A , (B , (dp , ctrnᵀ (csymᵀ c) c'))

gen-⌜Π⌝ : {Γ : Ctx} {c : RTm ⌊ Γ ⌋} {d : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
          Γ ⊢ ⌜Π⌝ c d ∷ C →
          (Γ ⊢ c ∷ U) × (((Γ ▹ El c) ⊢ d ∷ U) × (C ≅ᵀ U))
gen-⌜Π⌝ (⊢⌜Π⌝ dc dd) = dc , (dd , crflᵀ)
gen-⌜Π⌝ (⊢conv d c) with gen-⌜Π⌝ d
... | (dc , (dd , c')) = dc , (dd , ctrnᵀ (csymᵀ c) c')

gen-⌜Σ⌝ : {Γ : Ctx} {c : RTm ⌊ Γ ⌋} {d : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
          Γ ⊢ ⌜Σ⌝ c d ∷ C →
          (Γ ⊢ c ∷ U) × (((Γ ▹ El c) ⊢ d ∷ U) × (C ≅ᵀ U))
gen-⌜Σ⌝ (⊢⌜Σ⌝ dc dd) = dc , (dd , crflᵀ)
gen-⌜Σ⌝ (⊢conv d c) with gen-⌜Σ⌝ d
... | (dc , (dd , c')) = dc , (dd , ctrnᵀ (csymᵀ c) c')

gen-var : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ var x ∷ C →
          Σ (RTy ⌊ Γ ⌋) (λ A → (Γ ∋ x ∷ A) × (C ≅ᵀ A))
gen-var (⊢var v) = _ , (v , crflᵀ)
gen-var (⊢conv d c) with gen-var d
... | A , (v , c') = A , (v , ctrnᵀ (csymᵀ c) c')

gen-⌜Hom⌝ : {Γ : Ctx} {c a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ ⌜Hom⌝ c a b ∷ C →
            (Γ ⊢ c ∷ U) × ((Γ ⊢ a ∷ El c) × ((Γ ⊢ b ∷ El c) × (C ≅ᵀ U)))
gen-⌜Hom⌝ (⊢⌜Hom⌝ dc da db) = dc , (da , (db , crflᵀ))
gen-⌜Hom⌝ (⊢conv d c) with gen-⌜Hom⌝ d
... | (dc , (da , (db , c'))) = dc , (da , (db , ctrnᵀ (csymᵀ c) c'))

-- ★ stage D: ex falso inverts like `hrefl` — the code determines the
-- type, so the conversion is the only thing `⊢conv` can have added.
gen-absurd : {Γ : Ctx} {c e₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ absurd c e₀ ∷ C →
             (Γ ⊢ c ∷ U) × ((Γ ⊢ e₀ ∷ base) × (C ≅ᵀ El c))
gen-absurd (⊢absurd dc de) = dc , (de , crflᵀ)
gen-absurd (⊢conv d c) with gen-absurd d
... | (dc , (de , c')) = dc , (de , ctrnᵀ (csymᵀ c) c')

-- ★ the order's inversion.  `⊢ordtr`'s result type `Hom Nat a u` is
-- FIXED by the rule (no motive to guess), so unlike `gen-natrec` there
-- is nothing existential to recover — five premises and a conversion.
gen-ordtr : {Γ : Ctx} {a t u p q : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ ordtr a t u p q ∷ C →
            (Γ ⊢ a ∷ Nat) × ((Γ ⊢ t ∷ Nat) × ((Γ ⊢ u ∷ Nat) ×
            ((Γ ⊢ p ∷ Hom Nat a t) × ((Γ ⊢ q ∷ Hom Nat t u) ×
             (C ≅ᵀ Hom Nat a u)))))
gen-ordtr (⊢ordtr da dt du dp dq) =
  da , (dt , (du , (dp , (dq , crflᵀ))))
gen-ordtr (⊢conv d c) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , c')))) =
      da , (dt , (du , (dp , (dq , ctrnᵀ (csymᵀ c) c'))))

gen-hrefl : {Γ : Ctx} {c t₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ hrefl c t₀ ∷ C →
            (Γ ⊢ c ∷ U) × ((Γ ⊢ t₀ ∷ El c) × (C ≅ᵀ Hom (El c) t₀ t₀))
gen-hrefl (⊢hrefl dc dt) = dc , (dt , crflᵀ)
gen-hrefl (⊢conv d c) with gen-hrefl d
... | (dc , (dt , c')) = dc , (dt , ctrnᵀ (csymᵀ c) c')

gen-⌜Id⌝ : {Γ : Ctx} {c a b : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ ⌜Id⌝ c a b ∷ C →
           (Γ ⊢ c ∷ U) × ((Γ ⊢ a ∷ El c) × ((Γ ⊢ b ∷ El c) × (C ≅ᵀ U)))
gen-⌜Id⌝ (⊢⌜Id⌝ dc da db) = dc , (da , (db , crflᵀ))
gen-⌜Id⌝ (⊢conv d c) with gen-⌜Id⌝ d
... | (dc , (da , (db , c'))) = dc , (da , (db , ctrnᵀ (csymᵀ c) c'))

-- ★ WF stage A generation lemmas.
gen-nsuc : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ nsuc n ∷ C → (Γ ⊢ n ∷ Nat) × (C ≅ᵀ Nat)
gen-nsuc (⊢nsuc dn)  = dn , crflᵀ
gen-nsuc (⊢conv d c) with gen-nsuc d
... | (dn , c') = dn , ctrnᵀ (csymᵀ c) c'

gen-natrec : {Γ : Ctx} {z : RTm ⌊ Γ ⌋} {s₀ : RTm ((⌊ Γ ⌋ ∙) ∙)}
             {n : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ natrec z s₀ n ∷ C →
             Σ (RTy (⌊ Γ ⌋ ∙)) (λ M →
               ((Γ ▹ Nat) ⊢ty M) ×
               ((Γ ⊢ z ∷ subTy (single nzero) M) ×
               ((((Γ ▹ Nat) ▹ M) ⊢ s₀ ∷ subTy nrs M) ×
               ((Γ ⊢ n ∷ Nat) × (C ≅ᵀ subTy (single n) M)))))
gen-natrec (⊢natrec dM dz ds dn) = _ , (dM , (dz , (ds , (dn , crflᵀ))))
gen-natrec (⊢conv d c) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , c')))) =
      M , (dM , (dz , (ds , (dn , ctrnᵀ (csymᵀ c) c'))))

gen-idrefl : {Γ : Ctx} {c t₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ idrefl c t₀ ∷ C →
             (Γ ⊢ c ∷ U) × ((Γ ⊢ t₀ ∷ El c) × (C ≅ᵀ Id (El c) t₀ t₀))
gen-idrefl (⊢idrefl dc dt) = dc , (dt , crflᵀ)
gen-idrefl (⊢conv d c) with gen-idrefl d
... | (dc , (dt , c')) = dc , (dt , ctrnᵀ (csymᵀ c) c')

gen-jsub : {Γ : Ctx} {d₀ : RTm (⌊ Γ ⌋ ∙)} {p e : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ jsub d₀ p e ∷ C →
           Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTm ⌊ Γ ⌋) (λ t → Σ (RTm ⌊ Γ ⌋) (λ u →
             (((Γ ▹ A) ⊢ d₀ ∷ U) ×
             ((Γ ⊢ t ∷ A) × ((Γ ⊢ u ∷ A) ×
             ((Γ ⊢ p ∷ Id A t u) ×
             ((Γ ⊢ e ∷ El (subTm (single t) d₀)) ×
              (C ≅ᵀ El (subTm (single u) d₀))))))))))
gen-jsub (⊢jsub dd dt du dp de) =
  _ , (_ , (_ , (dd , (dt , (du , (dp , (de , crflᵀ)))))))
gen-jsub (⊢conv d c) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , c'))))))) =
      A , (t , (u , (dd , (dt , (du , (dp , (de , ctrnᵀ (csymᵀ c) c')))))))

gen-ap : {Γ : Ctx} {cB : RTm ⌊ Γ ⌋} {b : RTm (⌊ Γ ⌋ ∙)} {p : RTm ⌊ Γ ⌋}
         {C : RTy ⌊ Γ ⌋} → Γ ⊢ ap cB b p ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ cA → Σ (RTm ⌊ Γ ⌋) (λ t → Σ (RTm ⌊ Γ ⌋) (λ u →
           (Γ ⊢ cA ∷ U) × ((flat? cA ≡ true) × ((Γ ⊢ cB ∷ U) ×
           (((Γ ▹ El cA) ⊢ b ∷ El (renTm vs cB)) ×
           ((Γ ⊢ t ∷ El cA) × ((Γ ⊢ u ∷ El cA) ×
           ((Γ ⊢ p ∷ Hom (El cA) t u) ×
           (C ≅ᵀ Hom (El cB) (subTm (single t) b) (subTm (single u) b)))))))))))
gen-ap (⊢ap dcA key dcB db dt du dp) =
  _ , (_ , (_ , (dcA , (key , (dcB , (db , (dt , (du , (dp , crflᵀ)))))))))
gen-ap (⊢conv d c) with gen-ap d
... | cA , (t , (u , (dcA , (key , (dcB , (db , (dt , (du , (dp , c'))))))))) =
      cA , (t , (u , (dcA , (key , (dcB , (db ,
        (dt , (du , (dp , ctrnᵀ (csymᵀ c) c')))))))))


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
  -- ★ `Mu D` is inert: never `U`, never `Π`.
  st-Mu   : {Dᵐ : Desc} → StkAmb (Mu {Γ} Dᵐ)
  -- ★ `IMu D I i` is likewise never `U`, never `Π` — but its index
  --   reduces, so it is INERT-SHAPED, not inert.
  st-IMu  : {D : IDesc} {I : RTy ε} {i : RTm Γ} → StkAmb (IMu D I i)
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
stamb-red (st-el {c = ⌜Mu⌝ _} k) El-⌜Mu⌝ = st-Mu
stamb-red (st-el {c = ⌜IMu⌝ _ _ _} k) El-⌜IMu⌝ = st-IMu
stamb-red st-IMu (ξ-IMu r) = st-IMu
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

-- CONTEXT CONVERSION at the top entry — payable through `sub-lemma`
-- with the identity substitution (the derivation's var-here uses the
-- conversion; everything else is untouched).
ctx-conv : {Γ : Ctx} {A A' : RTy ⌊ Γ ⌋} {t : RTm (⌊ Γ ⌋ ∙)}
           {D : RTy (⌊ Γ ⌋ ∙)} →
           (Γ ▹ A) ⊢ t ∷ D → A' ≅ᵀ A → (Γ ▹ A') ⊢ t ∷ D
ctx-conv {Γ = Γ} {A = A} {A' = A'} {t = t} {D = D} d cA =
  subst₂-⊢ (subTm-id t) (subTy-id D) (sub-lemma d idσ⊢)
  where
  subst₂-⊢ : {Δ : Ctx} {t₁ t₂ : RTm ⌊ Δ ⌋} {D₁ D₂ : RTy ⌊ Δ ⌋} →
             t₁ ≡ t₂ → D₁ ≡ D₂ → Δ ⊢ t₁ ∷ D₁ → Δ ⊢ t₂ ∷ D₂
  subst₂-⊢ refl refl d₀ = d₀
  idσ⊢ : Sub⊢ (Γ ▹ A) (Γ ▹ A') idₛ
  idσ⊢ here = ⊢-cast (sym (subTy-id _))
                     (⊢conv (⊢var here) (≅ᵀ-ren vs cA))
  idσ⊢ (there v) = ⊢-cast (sym (subTy-id _)) (⊢var (there v))

-- ★ the WORKHORSE: a member of a pw-able decoded type, weakened and
-- applied at the fresh domain variable, lands in the pointwise body.
pw-app : {Γ : Ctx} {C : RTm ⌊ Γ ⌋} {w : RTm ⌊ Γ ⌋} →
         Γ ⊢ w ∷ El C → (key : pw? C ≡ true) →
         (Γ ▹ El (pwDom C)) ⊢ app (renTm vs w) (var vz) ∷ El (pwBody C)
pw-app {Γ = Γ} {C = C} {w = w} dw key with pw-El-decode C key
... | Body , (ch₁ , ch₂) =
  ⊢conv
    (⊢-cast (wk-inst-ty Body)
      (⊢app (⊢conv (⊢wk dw) (red→≅ᵀ (⟶ᵀ*-ren vs ch₁))) (⊢var here)))
    (csymᵀ (red→≅ᵀ ch₂))

-- typing of the pointwise dom/body codes, by spine induction.
pw-gen : {Γ : Ctx} {C : RTm ⌊ Γ ⌋} →
         Γ ⊢ C ∷ U → (key : pw? C ≡ true) →
         (Γ ⊢ pwDom C ∷ U) × ((Γ ▹ El (pwDom C)) ⊢ pwBody C ∷ U)
pw-gen {C = var v} d ()
pw-gen {C = lam t} d ()
pw-gen {C = app t u} d ()
pw-gen {C = pair a b} d ()
pw-gen {C = fst t} d ()
pw-gen {C = snd t} d ()
pw-gen {C = ⌜base⌝} d ()
pw-gen {C = ⌜Π⌝ γ δ} d key with gen-⌜Π⌝ d
... | (dγ , (dδ , _)) = dγ , dδ
pw-gen {C = ⌜Σ⌝ c d₁} d ()
pw-gen {C = ⌜Hom⌝ C a b} d key with gen-⌜Hom⌝ d
... | (dC , (da , (db , _))) with pw-gen dC key
...   | (dDom , dBody) =
      dDom , ⊢⌜Hom⌝ dBody (pw-app da key) (pw-app db key)
pw-gen {C = hrefl c t} d ()
pw-gen {C = tr d₁ p e} d ()

-- Inversion for `⊢tr` (stage 2: the composition motive, pinned in the
-- rule).  `deq` records that ANY typeable `tr`-motive has that shape.
record TrInv (Γ : Ctx) (d₀ : RTm (⌊ Γ ⌋ ∙)) (p e : RTm ⌊ Γ ⌋)
             (C : RTy ⌊ Γ ⌋) : Set where
  constructor mkTrInv
  field
    cM aM : RTm (⌊ Γ ⌋ ∙)
    deq  : d₀ ≡ ⌜Hom⌝ cM aM (var vz)
    A    : RTy ⌊ Γ ⌋
    t u  : RTm ⌊ Γ ⌋
    dcM  : (Γ ▹ A) ⊢ cM ∷ U
    daM  : (Γ ▹ A) ⊢ aM ∷ El cM
    dvM  : (Γ ▹ A) ⊢ var vz ∷ El cM
    ncM  : NoNatC cM
    hcM  : occTm vz cM ≡ false
    haM  : occTm vz aM ≡ false
    dt   : Γ ⊢ t ∷ A
    du   : Γ ⊢ u ∷ A
    dp   : Γ ⊢ p ∷ Hom A t u
    de   : Γ ⊢ e ∷ El (subTm (single t) (⌜Hom⌝ cM aM (var vz)))
    cC   : C ≅ᵀ El (subTm (single u) (⌜Hom⌝ cM aM (var vz)))

-- ...and the TAUT rule's inversion (`⊢trU`, motive pinned `var vz`).
record TrInvU (Γ : Ctx) (d₀ : RTm (⌊ Γ ⌋ ∙)) (p e : RTm ⌊ Γ ⌋)
              (C : RTy ⌊ Γ ⌋) : Set where
  constructor mkTrInvU
  field
    deq : d₀ ≡ var vz
    t u : RTm ⌊ Γ ⌋
    dt  : Γ ⊢ t ∷ U
    du  : Γ ⊢ u ∷ U
    dp  : Γ ⊢ p ∷ Hom U t u
    de  : Γ ⊢ e ∷ El t
    cC  : C ≅ᵀ El u

data TrGen (Γ : Ctx) (d₀ : RTm (⌊ Γ ⌋ ∙)) (p e : RTm ⌊ Γ ⌋)
           (C : RTy ⌊ Γ ⌋) : Set where
  tgC : TrInv  Γ d₀ p e C → TrGen Γ d₀ p e C
  tgU : TrInvU Γ d₀ p e C → TrGen Γ d₀ p e C

gen-tr : {Γ : Ctx} {d₀ : RTm (⌊ Γ ⌋ ∙)} {p e : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
         Γ ⊢ tr d₀ p e ∷ C → TrGen Γ d₀ p e C
gen-tr (⊢tr dc da dv nc hc ha dt du dp de) =
  tgC (mkTrInv _ _ refl _ _ _ dc da dv nc hc ha dt du dp de crflᵀ)
gen-tr (⊢trU dt du dp de) = tgU (mkTrInvU refl _ _ dt du dp de crflᵀ)
gen-tr (⊢conv d c) with gen-tr d
... | tgC (mkTrInv cM aM deq A t u dc da dv nc hc ha dt du dp de cC) =
      tgC (mkTrInv cM aM deq A t u dc da dv nc hc ha dt du dp de
                   (ctrnᵀ (csymᵀ c) cC))
... | tgU (mkTrInvU deq t u dt du dp de cC) =
      tgU (mkTrInvU deq t u dt du dp de (ctrnᵀ (csymᵀ c) cC))

------------------------------------------------------------------------
-- ★ SUBJECT REDUCTION.
------------------------------------------------------------------------

sr : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → t ⟶ u → Γ ⊢ u ∷ A
-- ★★★ REAL INVERSIONS.  These REPLACE the `⊥`-valued placeholders that
--   stood here while `⊢con`/`⊢elim` did not exist.  The placeholders made
--   subject reduction at ι VACUOUS; these make it provable.
gen-con : {Γ : Ctx} {k : ℕ} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
          Γ ⊢ con k p ∷ C →
          Σ Desc (λ D → DescWf D × ((k ∈D D) ×
                        ((Γ ⊢ p ∷ payTy D (lookupD D k)) × (C ≅ᵀ Mu D))))
gen-con (⊢con {D = D} w i dp) = D , (w , (i , (dp , crflᵀ)))
gen-con (⊢conv d c) with gen-con d
... | D , (w , (i , (dp , c'))) = D , (w , (i , (dp , ctrnᵀ (csymᵀ c) c')))

gen-elim : {Γ : Ctx} {D : Desc} {ms t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ elim D ms t ∷ C →
           Σ (RTy (⌊ Γ ⌋ ∙)) (λ M → DescWf D ×
             (((Γ ▹ Mu D) ⊢ty M) ×
             ((Γ ⊢ ms ∷ methsTy D M D) ×
             ((Γ ⊢ t ∷ Mu D) × (C ≅ᵀ subTy (single t) M)))))
gen-elim (⊢elim {M = M} w dM dms dt) = M , (w , (dM , (dms , (dt , crflᵀ))))
gen-elim (⊢conv d c) with gen-elim d
... | M , (w , (dM , (dms , (dt , c')))) =
      M , (w , (dM , (dms , (dt , ctrnᵀ (csymᵀ c) c'))))

-- ★ the INDEXED generation lemmas.  Same two-clause shape as `gen-con`/
--   `gen-elim`: the rule itself, then `⊢conv` composing the conversion.
gen-icon : {Γ : Ctx} {k : ℕ} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
           Γ ⊢ icon k p ∷ C →
           Σ IDesc (λ D → Σ (RTy ε) (λ I → Σ (RTm ⌊ Γ ⌋) (λ i →
             IDescWf I D × ((k ∈ID D) ×
             ((Γ ⊢ i ∷ εwkTy I) ×
             ((Γ ⊢ p ∷ ipayTy D I (isingle i) (ilookupD D k)) × (C ≅ᵀ IMu D I i)))))))
gen-icon (⊢icon {D = D} {I = I} {i = i} w kin di dp) =
  D , (I , (i , (w , (kin , (di , (dp , crflᵀ))))))
gen-icon (⊢conv d c) with gen-icon d
... | D , (I , (i , (w , (kin , (di , (dp , c')))))) =
      D , (I , (i , (w , (kin , (di , (dp , ctrnᵀ (csymᵀ c) c'))))))

gen-ielim : {Γ : Ctx} {D : IDesc} {i ms t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ ielim D i ms t ∷ C →
            Σ (RTy ((⌊ Γ ⌋ ∙) ∙)) (λ M → Σ (RTy ε) (λ I →
              IDescWf I D ×
              ((((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M) ×
              ((Γ ⊢ i ∷ εwkTy I) ×
              ((Γ ⊢ ms ∷ imethsTy D I M D) ×
              ((Γ ⊢ t ∷ IMu D I i) × (C ≅ᵀ iinst i t M)))))))
gen-ielim (⊢ielim {I = I} {M = M} w dM di dms dt) =
  M , (I , (w , (dM , (di , (dms , (dt , crflᵀ))))))
gen-ielim (⊢conv d c) with gen-ielim d
... | M , (I , (w , (dM , (di , (dms , (dt , c')))))) =
      M , (I , (w , (dM , (di , (dms , (dt , ctrnᵀ (csymᵀ c) c'))))))

gen-⌜IMu⌝ : {Γ : Ctx} {D : IDesc} {I : RTy ε} {i : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ ⌜IMu⌝ D I i ∷ C →
            (IDescWf I D) × ((Γ ⊢ i ∷ εwkTy I) × (C ≅ᵀ U))
gen-⌜IMu⌝ (⊢⌜IMu⌝ w di) = w , (di , crflᵀ)
gen-⌜IMu⌝ (⊢conv d c) with gen-⌜IMu⌝ d
... | w , (di , c') = w , (di , ctrnᵀ (csymᵀ c) c')

------------------------------------------------------------------------
-- ★★★ THE TWO LEMMAS ι NEEDS.  Ported from gate 5c (`SpikeIotaTup`).
------------------------------------------------------------------------

-- ⚠ the kernel's `_≡_` has NO fixity declaration, so it defaults to 20 —
--   TIGHTER than `_+_`'s infixl 6.  Without these parens `j + suc k ≡ …`
--   parses as `j + (suc k ≡ …)`.

-- ★ `sel k` extracts method `k` AT ITS OWN TAG.  ⚠ the `k ∈D E` premise
--   is what makes the `dnil` case impossible — without it this lemma is
--   FALSE, which is gate 5's Q21 finding.
sel-ty : {Γ : Ctx} (D : Desc) (M : RTy (⌊ Γ ⌋ ∙)) (E : Desc)
         (j k : ℕ) (ms : RTm ⌊ Γ ⌋) → k ∈D E →
         Γ ⊢ ms ∷ methsTyFrom D M j E →
         Γ ⊢ sel k ms ∷ methTy D (j + k) (lookupD E k) M
sel-ty {Γ} D M (C ◃ E) j zero ms hereD hms =
  ⊢-cast (cong (λ n → methTy D n C M) (sym (+zero j))) (⊢fst hms)
  where
    +zero : (n : ℕ) → (n + zero) ≡ n
    +zero zero    = refl
    +zero (suc n) = cong suc (+zero n)
sel-ty {Γ} D M (C ◃ E) j (suc k) ms (thereD i) hms =
  ⊢-cast (cong (λ n → methTy D n (lookupD E k) M) (sym (+-suc j k)))
         (sel-ty D M E (suc j) k (snd ms) i
                 (⊢-cast (wk-sub-single (methsTyFrom D M (suc j) E) (fst ms))
                         (⊢snd hms)))
  where
    wk-sub-single : (A : RTy ⌊ Γ ⌋) (u : RTm ⌊ Γ ⌋) →
                    subTy (single u) (renTy vs A) ≡ A
    wk-sub-single A u =
      trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))

-- ★ the IH tuple's TYPE is well-formed.
--
-- ⚠⚠ NEEDED BECAUSE THE KERNEL'S `⊢pair` CARRIES A `⊢ty` PREMISE that the
--   gate-5c spike's did not — I chose the spike's rules myself, so it
--   could validate the SHAPE of the design and still miss the kernel's
--   SIDE CONDITIONS.  A self-contained spike cannot catch this.
--
-- ★ `ihTy-wf` does NOT drag in description well-formedness (PLAN §4):
--   `ihTy` SKIPS `dκ` fields entirely, so no `εwkTy A` ever appears in it,
--   and it needs `payTy` INHABITED, not well-formed.
--   ⚠ `ihs-ty` BELOW IS DIFFERENT: it builds an `⊢elim` at each `dρ`
--   field, and `⊢elim` now carries a `DescWf` premise — so §4 does reach
--   that one.  It is threaded, not re-derived.
ihTy-wf : {Γ : Ctx} (D : Desc) (M : RTy (⌊ Γ ⌋ ∙)) (C : DCon) (p : RTm ⌊ Γ ⌋) →
          (Γ ▹ Mu D) ⊢ty M → Γ ⊢ p ∷ payTy D C → Γ ⊢ty ihTy D C p M
ihTy-wf D M dι       p dM hp = ty-Unit
ihTy-wf {Γ} D M (dρ C) p dM hp =
  ty-Σ (sub-ty dM (⊢single (⊢fst hp)))
       (ren-ty (ihTy-wf D M C (snd p) dM htail) there)
  where
    htail : Γ ⊢ snd p ∷ payTy D C
    htail = ⊢-cast (payTy-sub (single (fst p)) D C) (⊢snd hp)
ihTy-wf {Γ} D M (dκ A C) p dM hp =
  ihTy-wf D M C (snd p) dM
          (⊢-cast (payTy-sub (single (fst p)) D C) (⊢snd hp))

-- ★ the IH tuple inhabits its type.  ⚠ `dρ` contributes an IH, `dκ` NONE.
ihs-ty : {Γ : Ctx} (D : Desc) (M : RTy (⌊ Γ ⌋ ∙)) (ms : RTm ⌊ Γ ⌋)
         (C : DCon) (p : RTm ⌊ Γ ⌋) →
         DescWf D →
         (Γ ▹ Mu D) ⊢ty M →
         Γ ⊢ ms ∷ methsTy D M D →
         Γ ⊢ p ∷ payTy D C →
         Γ ⊢ ihs D ms C p ∷ ihTy D C p M
ihs-ty D M ms dι       p w dM hms hp = ⊢unit
ihs-ty {Γ} D M ms (dρ C) p w dM hms hp =
  ⊢pair (ren-ty (ihTy-wf D M C (snd p) dM htail) there)
        (⊢elim w dM hms (⊢fst hp))
        (⊢-cast (sym (wk-sub-single (ihTy D C (snd p) M) (elim D ms (fst p))))
                (ihs-ty D M ms C (snd p) w dM hms htail))
  where
    wk-sub-single : (A : RTy ⌊ Γ ⌋) (u : RTm ⌊ Γ ⌋) →
                    subTy (single u) (renTy vs A) ≡ A
    wk-sub-single A u =
      trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))
    htail : Γ ⊢ snd p ∷ payTy D C
    htail = ⊢-cast (payTy-sub (single (fst p)) D C) (⊢snd hp)
ihs-ty {Γ} D M ms (dκ A C) p w dM hms hp =
  ihs-ty D M ms C (snd p) w dM hms
         (⊢-cast (payTy-sub (single (fst p)) D C) (⊢snd hp))

-- ★ the five indexed-ι lemmas moved to `Metatheory/TySub` (their cone
--   touches neither `sr` nor `gen-*`); re-exported from there.

-- ★★★ OBLIGATION (c) — THE IH TUPLE, AT THE RECURSIVE FIELDS' OWN INDICES.
--
-- ⚠⚠ THIS WAS FALSE UNDER THE OLD FORMULATION (PLAN-INDEXED §9.1), not
--   merely unproven: the tuple `ms` was typed at ONE index while the
--   recursive call below needs it at `subTm σ j`.  With methods
--   index-quantified, `ms ∷ imethsTy D I M D` mentions no index and the
--   SAME tuple serves every recursive field.  That is the whole fix.
--
-- ⚠ the environment must be WELL-TYPED against the telescope (`Sub⊢ Θ Γ σ`)
--   — that is what turns `IConWf`'s `Θ ⊢ j ∷ εwkTy I` into the
--   `Γ ⊢ subTm σ j ∷ εwkTy I` that `⊢ielim` demands.
iihs-ty : {Γ Θ : Ctx} (D : IDesc) (I : RTy ε) (M : RTy ((⌊ Γ ⌋ ∙) ∙))
          (ms : RTm ⌊ Γ ⌋) (σ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋) (C : ICon ⌊ Θ ⌋)
          (p : RTm ⌊ Γ ⌋) →
          IDescWf I D →
          IConWf D I Θ C →
          Sub⊢ Θ Γ σ →
          ((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M →
          Γ ⊢ ms ∷ imethsTy D I M D →
          Γ ⊢ p ∷ ipayTy D I σ C →
          Γ ⊢ iihs D ms σ C p ∷ iihTy D I σ C p M
iihs-ty D I M ms σ iι p wD wC hσ dM hms hp = ⊢unit
iihs-ty {Γ} {Θ} D I M ms σ (iρ j C) p wD (iwf-ρ .j dj wC) hσ dM hms hp =
  ⊢pair (ren-ty (iihTy-wf D I M (iext σ (fst p)) C (snd p) wC
                          (iext-Sub⊢ hσ (⊢fst hp)) dM
                          (⊢-cast (ipayTy-sub-single D I σ (fst p) C) (⊢snd hp)))
                there)
        (⊢ielim wD dM
                (⊢-cast (εwk-sub σ I) (sub-lemma dj hσ))
                hms
                (⊢fst hp))
        (⊢-cast (sym (wk-sub-single
                        (iihTy D I (iext σ (fst p)) C (snd p) M)
                        (ielim D (subTm σ j) ms (fst p))))
                (iihs-ty D I M ms (iext σ (fst p)) C (snd p) wD wC
                         (iext-Sub⊢ hσ (⊢fst hp)) dM hms
                         (⊢-cast (ipayTy-sub-single D I σ (fst p) C) (⊢snd hp))))
  where
    wk-sub-single : (A : RTy ⌊ Γ ⌋) (u : RTm ⌊ Γ ⌋) →
                    subTy (single u) (renTy vs A) ≡ A
    wk-sub-single A u =
      trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))
iihs-ty D I M ms σ (iκ κ C) p wD (iwf-κ .κ _ dcode wC) hσ dM hms hp =
  iihs-ty D I M ms (iext σ (fst p)) C (snd p) wD wC
          (iext-Sub⊢ hσ (⊢fst hp)) dM hms
          (⊢-cast (ipayTy-sub-single D I σ (fst p) C) (⊢snd hp))

-- ★★★ INDUCTIVE TYPES: SUBJECT REDUCTION AT ι.
--
-- This is the obligation the ι-rule has carried since it landed, and the
-- one the `⊥-elim` placeholder stood in for.  Every piece is now present:
--
--   Mu-inj    reconciles the description `gen-elim` reports with the one
--             `gen-con` reports  (cheap: `Mu` is INERT)
--   sel-ty    method `k` out of the tuple, AT ITS OWN TAG (needs `k ∈D D`)
--   ihs-ty    the IH tuple inhabits `ihTy`
--   atCon-inst  the re-based motive lands at `M [ con k p ]` — NO η
-- ★★★ THE INDEXED REDUCTION RULES.
--
-- ⚠ `ξ-ielimⁱ` is where `ξ-IMu` earns its place: the index steps, so the
--   SCRUTINEE'S TYPE `IMu D I i` steps with it, and `dt` must be
--   re-typed by conversion.  Without that congruence this case has no
--   proof — which is why the rule was added (PLAN-INDEXED §9, `ξ-IMu`).
--   The RESULT type moves too, hence `iinst-mono`.  ⚠ the METHODS do NOT
--   move: after §9.1 `imethsTy` names no index at all.
sr d (ξ-icon r) with gen-icon d
... | D , (I , (i , (w , (kin , (di , (dp , cIMu))))))
      = ⊢conv (⊢icon w kin di (sr dp r)) (csymᵀ cIMu)
sr d (ξ-⌜IMu⌝ r) with gen-⌜IMu⌝ d
... | w , (di , cU) = ⊢conv (⊢⌜IMu⌝ w (sr di r)) (csymᵀ cU)
sr d (ξ-ielimᵐ r) with gen-ielim d
... | M , (I , (w , (dM , (di , (dms , (dt , cC))))))
      = ⊢conv (⊢ielim w dM di (sr dms r) dt) (csymᵀ cC)
sr d (ξ-ielimᵗ {i = i} r) with gen-ielim d
... | M , (I , (w , (dM , (di , (dms , (dt , cC))))))
      = ⊢conv (⊢ielim w dM di dms (sr dt r))
              (csymᵀ (ctrnᵀ cC (red→≅ᵀ (iinst-monoˢ M i (step r done)))))
sr {Γ = Γ} d (ξ-ielimⁱ {i = i} {i' = i'} r) with gen-ielim d
... | M , (I , (w , (dM , (di , (dms , (dt , cC))))))
      = ⊢conv (⊢ielim w dM (sr di r) dms
                      (⊢conv dt (credᵀ (ξ-IMu r))))
              (csymᵀ (ctrnᵀ cC (red→≅ᵀ (iinst-mono M _ (step r done)))))
-- ★★★ SUBJECT REDUCTION AT THE INDEXED ι.
--
-- Mirrors `ι-elim` with ONE extra application — the INDEX, which is the
-- binder §9.1 added to `imethTy`.  And with one step the non-indexed rule
-- never needs: `IMu-inj` yields `i ≅ i''` (a CONVERSION, because `IMu`
-- carries a reducible index) where `Mu-inj` yields `D ≡ D'`, so the
-- payload derivation must be TRANSPORTED before it can be applied.
sr {Γ = Γ} d (ι-ielim D i ms k p) with gen-ielim d
... | M , (I , (w , (dM , (di , (dms , (dt , cC)))))) with gen-icon dt
...   | D' , (I' , (i'' , (w' , (kin , (di'' , (dp , cIMu))))))
        with IMu-inj cIMu
...     | (refl , (refl , ci)) =
          ⊢conv (⊢-cast step3
                   (⊢app (⊢-cast step2
                            (⊢app (⊢-cast step1 (⊢app hsel di)) dp'))
                         (iihs-ty D I M ms (isingle i) (ilookupD D k) p
                                  w (ilookupD-wf k w kin) (isingle-Sub⊢ di)
                                  dM dms dp')))
                (csymᵀ cC)
  where
    C₀ : ICon (ε ∙)
    C₀ = ilookupD D k

    -- ⚠ THE TRANSPORT the non-indexed ι does not need.
    dp' : Γ ⊢ p ∷ ipayTy D I (isingle i) C₀
    dp' = ⊢conv dp (ipayTy-conv D I C₀ (csym ci))

    hsel : Γ ⊢ sel k ms ∷ imethTy D I k C₀ M
    hsel = isel-ty D I M D zero k ms kin dms

    step1 : subTy (single i)
              (Π (ipayTy D I (isingle (var vz)) C₀)
                 (Π (iihTy D I (isingle (var (vs vz))) C₀ (var vz)
                           (renTy (extR (extR vs)) (renTy (extR (extR vs)) M)))
                    (renTy vs (iatCon k (var vz) (renTy (extR (extR vs)) M)))))
              ≡ Π (ipayTy D I (isingle i) C₀)
                  (subTy (extS (single i))
                     (Π (iihTy D I (isingle (var (vs vz))) C₀ (var vz)
                               (renTy (extR (extR vs)) (renTy (extR (extR vs)) M)))
                        (renTy vs (iatCon k (var vz) (renTy (extR (extR vs)) M)))))
    -- ⚠ the codomain must be WRITTEN OUT.  With `_` Agda has to invert
    --   `λ z → Π z ?` against the goal, which it cannot: the meta is
    --   blocked on the very equation this `cong` is producing.
    step1 = cong (λ z →
                   Π z (subTy (extS (single i))
                          (Π (iihTy D I (isingle (var (vs vz))) C₀ (var vz)
                                    (renTy (extR (extR vs))
                                           (renTy (extR (extR vs)) M)))
                             (renTy vs (iatCon k (var vz)
                                                (renTy (extR (extR vs)) M))))))
                 (trans (ipayTy-sub (single i) D I (isingle (var vz)) C₀)
                        (ipayTy-cong D I C₀ (λ { vz → refl })))

    step2 : subTy (single p)
              (subTy (extS (single i))
                 (Π (iihTy D I (isingle (var (vs vz))) C₀ (var vz)
                           (renTy (extR (extR vs)) (renTy (extR (extR vs)) M)))
                    (renTy vs (iatCon k (var vz) (renTy (extR (extR vs)) M)))))
              ≡ Π (iihTy D I (isingle i) C₀ p M)
                  (renTy vs (subTy (single p) (iatCon k i M)))

    -- the motive survives BOTH substitutions: each cancels one of the two
    -- weakenings written into `imethTy`.
    mcancel : subTy (extS (extS (single p)))
                (subTy (extS (extS (extS (single i))))
                   (renTy (extR (extR vs)) (renTy (extR (extR vs)) M)))
                ≡ M
    -- ⚠ FUSE, THEN CHECK POINTWISE.  Hand-deriving which `extS` cancels
    --   which `extR` at this depth is where I kept going wrong; composing
    --   everything into ONE substitution and letting `subTy-cong` check
    --   the three variable cases is both shorter and self-checking — if
    --   the weakening tower in `imethTy` were off, THIS is where Agda
    --   would say so rather than somewhere three lemmas later.
    mcancel =
      trans (subTy-subTy (renTy (extR (extR vs)) (renTy (extR (extR vs)) M)))
      (trans (subTy-renTy (renTy (extR (extR vs)) M))
      (trans (subTy-renTy M)
      (trans (subTy-cong (λ { vz → refl ; (vs vz) → refl
                            ; (vs (vs x)) → refl }) M)
             (subTy-id M))))

    compA : subTy (single p)
              (subTy (extS (single i))
                 (iihTy D I (isingle (var (vs vz))) C₀ (var vz)
                        (renTy (extR (extR vs)) (renTy (extR (extR vs)) M))))
              ≡ iihTy D I (isingle i) C₀ p M
    -- ⚠ FIFTH pointwise bridge.  `iihTy-sub` returns the environment
    --   `λ x → subTm τ (σ x)`; the next step names `isingle (renTm vs i)`.
    --   Pointwise equal, definitionally distinct — so `iihTy-cong` has to
    --   sit BETWEEN the two `iihTy-sub` applications, not after them.
    compA =
      trans (cong (subTy (single p))
                  (trans (iihTy-sub (extS (single i)) D I
                                    (isingle (var (vs vz))) C₀ (var vz)
                                    (renTy (extR (extR vs))
                                           (renTy (extR (extR vs)) M)))
                         (iihTy-cong D I C₀ (var vz)
                            (subTy (extS (extS (extS (single i))))
                               (renTy (extR (extR vs))
                                      (renTy (extR (extR vs)) M)))
                            (λ { vz → refl }))))
            (trans (iihTy-sub (single p) D I (isingle (renTm vs i))
                              C₀ (var vz)
                              (subTy (extS (extS (extS (single i))))
                                 (renTy (extR (extR vs))
                                        (renTy (extR (extR vs)) M))))
                   (trans (iihTy-cong D I C₀ p
                             (subTy (extS (extS (single p)))
                                (subTy (extS (extS (extS (single i))))
                                   (renTy (extR (extR vs))
                                          (renTy (extR (extR vs)) M))))
                             (λ { vz → wk-single i }))
                          (cong (iihTy D I (isingle i) C₀ p) mcancel)))

    compB : subTy (extS (single p))
              (subTy (extS (extS (single i)))
                 (renTy vs (iatCon k (var vz) (renTy (extR (extR vs)) M))))
              ≡ renTy vs (subTy (single p) (iatCon k i M))
    -- ⚠ FUSE BOTH SIDES to `subTy θ M`, then compare θ pointwise — the
    --   same move that settled `mcancel`.  LHS: two substitutions over a
    --   weakened `iatCon`; RHS: the substituted `iatCon`, weakened.  Three
    --   variable cases, and `iconS`'s `vz` row is the only one with content.
    -- ⚠ REWRITTEN.  Fusing everything to a pointwise comparison of the
    --   two composites did NOT work: at `vs vz` they are genuinely
    --   different shapes.  Going through `iatCon-sub` — a lemma already
    --   proved for the naturality layer — instead of re-deriving the
    --   substitution algebra by hand is both shorter and correct.
    -- ⚠ CONTEXT-POLYMORPHIC: applied at two different depths below, so it
    --   must not be pinned to `⌊ Γ ⌋`.
    exts-wk : {Θ Δ : Cx} (σ : Sub Θ Δ) (A : RTy Θ) →
              subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A)
    exts-wk σ A = trans (subTy-renTy A) (sym (renTy-subTy A))

    wkcancel : subTy (extS (extS (single i)))
                     (renTy (extR (extR vs)) M) ≡ M
    wkcancel =
      trans (subTy-renTy M)
            (trans (subTy-cong (λ { vz → refl ; (vs vz) → refl
                                  ; (vs (vs x)) → refl }) M)
                   (subTy-id M))

    compB =
      trans (cong (subTy (extS (single p)))
                  (exts-wk (extS (single i))
                           (iatCon k (var vz) (renTy (extR (extR vs)) M))))
            (trans (exts-wk (single p)
                      (subTy (extS (single i))
                             (iatCon k (var vz) (renTy (extR (extR vs)) M))))
                   (cong (renTy vs)
                      (cong (subTy (single p))
                         (trans (iatCon-sub (single i) k (var vz)
                                            (renTy (extR (extR vs)) M))
                                (cong (iatCon k i) wkcancel)))))

    -- ⚠ BOTH substitutions land on a Π, so this is `cong₂ Π` over the two
    --   components.  The domain is the IH tuple's type (which is exactly
    --   what `iihs-ty` produces); the codomain is the re-based motive,
    --   which `step3` then closes with `iatCon-inst`.
    step2 = cong₂ Π compA compB

    wk-sub-single : (A : RTy ⌊ Γ ⌋) (u : RTm ⌊ Γ ⌋) →
                    subTy (single u) (renTy vs A) ≡ A
    wk-sub-single A u =
      trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))

    step3 : subTy (single (iihs D ms (isingle i) C₀ p))
                  (renTy vs (subTy (single p) (iatCon k i M)))
              ≡ iinst i (icon k p) M
    step3 = trans (wk-sub-single (subTy (single p) (iatCon k i M))
                                 (iihs D ms (isingle i) C₀ p))
                  (iatCon-inst k i M p)

sr {Γ = Γ} d (ι-elim D ms k p) with gen-elim d
... | M , (w , (dM , (dms , (dt , cC)))) with gen-con dt
...   | D' , (w' , (i , (dp , cMu))) with Mu-inj cMu
...     | refl =
          ⊢conv (⊢-cast step3 (⊢app (⊢-cast step2 (⊢app hsel dp))
                                    (ihs-ty D M ms (lookupD D k) p w dM dms dp)))
                (csymᵀ cC)
  where
    wk-single-id : (p : RTm ⌊ Γ ⌋) (M : RTy (⌊ Γ ⌋ ∙)) →
                   subTy (extS (single p)) (renTy (extR vs) M) ≡ M
    wk-single-id p M =
      trans (subTy-renTy M)
            (trans (subTy-cong (λ { vz → refl ; (vs x) → refl }) M) (subTy-id M))

    hsel : Γ ⊢ sel k ms ∷ methTy D k (lookupD D k) M
    hsel = sel-ty D M D zero k ms i dms



    -- the payload substitution, pushed through both components
    step2 : subTy (single p)
              (Π (ihTy D (lookupD D k) (var vz) (renTy (extR vs) M))
                 (renTy vs (atCon k M)))
              ≡ Π (ihTy D (lookupD D k) p M)
                  (renTy vs (subTy (single p) (atCon k M)))
    step2 =
      cong₂ Π (trans (ihTy-sub (single p) D (lookupD D k) (var vz)
                               (renTy (extR vs) M))
                     (cong (ihTy D (lookupD D k) p) (wk-single-id p M)))
              (trans (subTy-renTy (atCon k M))
                     (sym (renTy-subTy (atCon k M))))

    wk-sub-single : (A : RTy ⌊ Γ ⌋) (u : RTm ⌊ Γ ⌋) →
                    subTy (single u) (renTy vs A) ≡ A
    wk-sub-single A u =
      trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))

    step3 : subTy (single (ihs D ms (lookupD D k) p))
                  (renTy vs (subTy (single p) (atCon k M)))
              ≡ subTy (single (con k p)) M
    step3 = trans (wk-sub-single (subTy (single p) (atCon k M))
                                 (ihs D ms (lookupD D k) p))
                  (atCon-inst k M p)


-- ★★ INDUCTIVE TYPES: the three CONGRUENCES.  Each is a plain rebuild;
-- only the SCRUTINEE case moves the motive, and it moves it exactly as
-- `ξ-natrecⁿ` does.
sr d (ξ-con r) with gen-con d
... | D , (w , (i , (dp , cMu))) = ⊢conv (⊢con w i (sr dp r)) (csymᵀ cMu)
sr d (ξ-elimᵐ r) with gen-elim d
... | M , (w , (dM , (dms , (dt , cC)))) =
      ⊢conv (⊢elim w dM (sr dms r) dt) (csymᵀ cC)
sr d (ξ-elimᵗ {t = t} r) with gen-elim d
... | M , (w , (dM , (dms , (dt , cC)))) =
      ⊢conv (⊢elim w dM dms (sr dt r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) M))))
sr d (ξ-nsuc r) with gen-nsuc d
... | (dn , cC) = ⊢conv (⊢nsuc (sr dn r)) (csymᵀ cC)
sr d (natrec-zero z s₀) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) = ⊢conv dz (csymᵀ cC)
sr d (natrec-suc z s₀ n) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) with gen-nsuc dn
...   | (dn' , _) =
      ⊢conv (⊢-cast (natrec-step-ty M (natrec z s₀ n) n)
              (⊢[] (sub-lemma ds (Sub⊢-ext (⊢single dn')))
                   (⊢natrec dM dz ds dn')))
            (csymᵀ cC)
sr d (ξ-natrecᶻ r) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) =
      ⊢conv (⊢natrec dM (sr dz r) ds dn) (csymᵀ cC)
sr d (ξ-natrecˢ r) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) =
      ⊢conv (⊢natrec dM dz (sr ds r) dn) (csymᵀ cC)
sr d (ξ-natrecⁿ r) with gen-natrec d
... | M , (dM , (dz , (ds , (dn , cC)))) =
      ⊢conv (⊢natrec dM dz ds (sr dn r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) M))))
-- ★★ stage D: ex falso preserves typing under both congruences.  The
-- code determines the result type, so the scrutinee case is a plain
-- rebuild and the code case rides `ξ-El`.
sr d (ξ-absurdᶜ r) with gen-absurd d
... | dc , (de , cv) =
      ⊢conv (⊢absurd (sr dc r) de)
            (ctrnᵀ (csymᵀ (credᵀ (ξ-El r))) (csymᵀ cv))
sr d (ξ-absurdᵉ r) with gen-absurd d
... | dc , (de , cv) = ⊢conv (⊢absurd dc (sr de r)) (csymᵀ cv)
-- ★ SUBJECT REDUCTION FOR THE ORDER.  Four of the five rules change
-- the result type, and each is repaired by the SAME computing order
-- that fired the rule — this is the payoff of `Hom Nat` computing.
--
--   ordtr-z   ↦ `Hom Nat nzero u` IS `Unit`, so `unit` fits.
--   ordtr-szz ↦ `p` already has the goal type verbatim.
--   ordtr-ssz ↦ ⚠ `q : Hom Nat (nsuc t) nzero` but the goal is
--               `Hom Nat (nsuc a) nzero` — DIFFERENT terms.  The rule
--               is sound only because BOTH collapse to `base` under
--               `Hom-Nat-sz`; that is the whole justification.
--   ordtr-szs ↦ ex falso, at the code whose `El` is the goal.
--   ordtr-sss ↦ peel `nsuc` off all three bounds via `Hom-Nat-ss`.
sr d (ordtr-z t u p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv ⊢unit (csymᵀ (ctrnᵀ cv (credᵀ (Hom-Nat-z u))))
sr d (ordtr-szz a p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) = ⊢conv dp (csymᵀ cv)
sr d (ordtr-ssz a t p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv dq (ctrnᵀ (credᵀ (Hom-Nat-sz t))
                      (ctrnᵀ (csymᵀ (credᵀ (Hom-Nat-sz a))) (csymᵀ cv)))
sr d (ordtr-szs a u p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) with gen-nsuc da | gen-nsuc du
...   | da' , _ | du' , _ =
        ⊢conv (⊢absurd (⊢⌜Hom⌝ ⊢⌜Nat⌝
                          (⊢conv da' (csymᵀ (credᵀ El-⌜Nat⌝)))
                          (⊢conv du' (csymᵀ (credᵀ El-⌜Nat⌝))))
                       (⊢conv dp (credᵀ (Hom-Nat-sz a))))
              (ctrnᵀ (credᵀ (El-⌜Hom⌝ _ _ _))
                (ctrnᵀ (credᵀ (ξ-Homᵀ El-⌜Nat⌝))
                  (ctrnᵀ (csymᵀ (credᵀ (Hom-Nat-ss a u))) (csymᵀ cv))))
sr d (ordtr-sss a t u p q) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) with gen-nsuc da | gen-nsuc dt | gen-nsuc du
...   | da' , _ | dt' , _ | du' , _ =
        ⊢conv (⊢ordtr da' dt' du'
                 (⊢conv dp (credᵀ (Hom-Nat-ss a t)))
                 (⊢conv dq (credᵀ (Hom-Nat-ss t u))))
              (ctrnᵀ (csymᵀ (credᵀ (Hom-Nat-ss a u))) (csymᵀ cv))
-- the congruences.  Only ᵃ and ᵘ move the result type (they are its
-- endpoints); ᵗ, ᵖ and q leave it alone.
sr d (ξ-ordtrᵃ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr (sr da r) dt du (⊢conv dp (credᵀ (ξ-Homˡ r))) dq)
            (csymᵀ (ctrnᵀ cv (credᵀ (ξ-Homˡ r))))
sr d (ξ-ordtrᵗ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da (sr dt r) du
               (⊢conv dp (credᵀ (ξ-Homʳ r))) (⊢conv dq (credᵀ (ξ-Homˡ r))))
            (csymᵀ cv)
sr d (ξ-ordtrᵘ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da dt (sr du r) dp (⊢conv dq (credᵀ (ξ-Homʳ r))))
            (csymᵀ (ctrnᵀ cv (credᵀ (ξ-Homʳ r))))
sr d (ξ-ordtrᵖ r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da dt du (sr dp r) dq) (csymᵀ cv)
sr d (ξ-ordtrq r) with gen-ordtr d
... | da , (dt , (du , (dp , (dq , cv)))) =
      ⊢conv (⊢ordtr da dt du dp (sr dq r)) (csymᵀ cv)
sr d (β s a) with gen-app d
... | A₀ , (B₀ , (d-lam , (d-a , cC))) with gen-lam d-lam
...   | A₁ , (B₁ , (cΠ , (tyA₁ , d-s))) with Π-inj cΠ
...     | (cA , cB) =
          ⊢conv (⊢[] d-s (⊢conv d-a cA))
                (ctrnᵀ (≅ᵀ-sub (single a) (csymᵀ cB)) (csymᵀ cC))
sr d (ξ-lam r) with gen-lam d
... | A₀ , (B₀ , (cΠ , (tyA₀ , d-s))) =
      ⊢conv (⊢lam tyA₀ (sr d-s r)) (csymᵀ cΠ)
sr d (ξ-appˡ r) with gen-app d
... | A₀ , (B₀ , (d-t , (d-u , cC))) = ⊢conv (⊢app (sr d-t r) d-u) (csymᵀ cC)
sr d (ξ-appʳ {u = u} {u' = u'} r) with gen-app d
... | A₀ , (B₀ , (d-t , (d-u , cC))) =
      ⊢conv (⊢app d-t (sr d-u r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) B₀))))
sr d (βfst a b) with gen-fst d
... | A₀ , (B₀ , (d-pair , cC)) with gen-pair d-pair
...   | A₁ , (B₁ , (cΣ , (tyB₁ , (d-a , d-b)))) with Σ-inj cΣ
...     | (cA , cB) = ⊢conv d-a (csymᵀ (ctrnᵀ cC cA))
sr d (βsnd a b) with gen-snd d
... | A₀ , (B₀ , (d-pair , cC)) with gen-pair d-pair
...   | A₁ , (B₁ , (cΣ , (tyB₁ , (d-a , d-b)))) with Σ-inj cΣ
...     | (cA , cB) =
          ⊢conv d-b
            (csymᵀ (ctrnᵀ cC
              (ctrnᵀ (red→≅ᵀ (subTy-monoˢ (single-mono (step (βfst a b) done)) B₀))
                     (≅ᵀ-sub (single a) cB))))
sr d (ξ-pairˡ r) with gen-pair d
... | A₀ , (B₀ , (cΣ , (tyB₀ , (d-a , d-b)))) =
      ⊢conv (⊢pair tyB₀ (sr d-a r)
              (⊢conv d-b (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) B₀))))
            (csymᵀ cΣ)
sr d (ξ-pairʳ r) with gen-pair d
... | A₀ , (B₀ , (cΣ , (tyB₀ , (d-a , d-b)))) =
      ⊢conv (⊢pair tyB₀ d-a (sr d-b r)) (csymᵀ cΣ)
sr d (ξ-fst r) with gen-fst d
... | A₀ , (B₀ , (d-p , cC)) = ⊢conv (⊢fst (sr d-p r)) (csymᵀ cC)
sr d (ξ-snd r) with gen-snd d
... | A₀ , (B₀ , (d-p , cC)) =
      ⊢conv (⊢snd (sr d-p r))
        (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step (ξ-fst r) done)) B₀))))
sr d (ξ-⌜Π⌝ˡ r) with gen-⌜Π⌝ d
... | (dc , (dd , cU)) =
      ⊢conv (⊢⌜Π⌝ (sr dc r) (conv-ctx (credᵀ (ξ-El r)) dd)) (csymᵀ cU)
sr d (ξ-⌜Π⌝ʳ r) with gen-⌜Π⌝ d
... | (dc , (dd , cU)) = ⊢conv (⊢⌜Π⌝ dc (sr dd r)) (csymᵀ cU)
sr d (ξ-⌜Σ⌝ˡ r) with gen-⌜Σ⌝ d
... | (dc , (dd , cU)) =
      ⊢conv (⊢⌜Σ⌝ (sr dc r) (conv-ctx (credᵀ (ξ-El r)) dd)) (csymᵀ cU)
sr d (ξ-⌜Σ⌝ʳ r) with gen-⌜Σ⌝ d
... | (dc , (dd , cU)) = ⊢conv (⊢⌜Σ⌝ dc (sr dd r)) (csymᵀ cU)
-- `tr`-rule reductions (stage 2).  The J cases extract the endpoint
-- conversion a canonical identity path witnesses via confluence
-- (stuck-ambient `Hom`s never unfold, so reducts decompose
-- componentwise); the taut case is VACUOUS in the base judgment — the
-- rule pins the motive to a `⌜Hom⌝`, never `var vz`.
sr d (tr-J-base cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with homred-inv baseamb-red (λ ()) (λ ()) (λ ()) ba-el rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-base))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
sr d (tr-J-Σ cm am mm c₁ c₂ s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with homred-inv σamb-red (λ ()) (λ ()) (λ ()) sa-el rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Σ))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★ the TAUT redex — REAL in the base judgment now (`⊢trU`).  The
-- pinned `U` ambient makes the `via-Π` arm a one-line `U-reduct` clash
-- (the staged proof needed a `gen-var` renaming dance here).
-- ★ W2b: `hrefl` at a pw-able code unfolds pointwise — the LHS/RHS
-- types convert through the `pw-Hom-decode` join.
sr d (hrefl-pw C s key) with gen-hrefl d
... | (dc , (ds , cH)) with pw-gen dc key | pw-Hom-decode C key s s
...   | (dDom , dBody) | Body , (ch₁ , ch₂) =
      ⊢conv (⊢lam (ty-El dDom) (⊢hrefl dBody (pw-app ds key)))
            (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Πʳ ch₂))
                   (csymᵀ (ctrnᵀ cH (red→≅ᵀ ch₁))))
-- ★ W2b: J at stable ⌜Hom⌝ codes — the endpoint conversion extracted
-- via confluence against the `StkAmb` analysis (stable-code decodings
-- never unfold to Π/U, so reducts decompose componentwise).
sr d (tr-J-Id cm am mm c₁ a₁ b₁ s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Id⌝ c₁ a₁ b₁} refl , nn-El nnh-Id) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Id))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★ WF stage C: J at ⌜Unit⌝ — the `tr-J-Id` case verbatim, at the other
-- stable datatype code.  (There is NO `tr-J-Nat` peer: `⌜Nat⌝` is not
-- `stkC?`, and `Hom Nat` computes, so J there is unsound — see
-- `stkC?` in NbEPDirDBVar.)
sr d (tr-J-Unit cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Unit⌝} refl , nn-El nnh-Unit) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Unit))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★ §10.4's subject-reduction obligation.  `tr-J-Mu`'s proof VERBATIM:
--   the only input that differs is the stuck-ambient witness, which is
--   `st-el {c = ⌜IMu⌝ …} refl` (that is `stkC? (⌜IMu⌝ …) = true`) paired
--   with `nn-El nnh-IMu`.
sr d (tr-J-IMu {D = Dⁱ} {I = Iⁱ} {iˣ = iˣ} cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜IMu⌝ Dⁱ Iⁱ iˣ} refl , nn-El nnh-IMu) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-IMu))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
sr d (tr-J-Mu {D = Dᵐ} cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Mu⌝ Dᵐ} refl , nn-El nnh-Mu) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Mu))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
sr d (tr-J-Hom cm am mm c₁ a₁ b₁ s e₀ key) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Hom⌝ c₁ a₁ b₁} key , nn-El nnh-Hom) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR)
                            (nn-El nnh-Hom))
                   (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...         | mkHomRed rA rt ru =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rt)
                         (ctrnᵀ (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₁))
                           (ctrnᵀ (mono-El[] (⌜Hom⌝ cm am mm) rs₂)
                             (csymᵀ (mono-El[] (⌜Hom⌝ cm am mm) ru)))))
                       (csymᵀ cC))
-- ★★ W2b: POINTWISE TRANSPORT preserves typing.  The rebuilt term is a
-- lambda whose body is ANOTHER composition-motive `⊢tr` instance at the
-- pointwise body code — assembled from `pw-app`/`pw-gen`, the decode
-- joins, and raw↔typed bridges (the rule's `pwShift`-renamed motive
-- equals the weakened pointwise body of the SUBSTITUTED code, because
-- the motive's components are vz-free).
sr {Γ = Γ} d (tr-pw c a f e₀ key) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-var dvM
...   | _ , (here , cv) =
      ⊢conv
        (⊢-cast
          (cong (Π (El (pwDom C₀)))
                (cong El (⌜Hom⌝-cong₃ (inst-c u') (inst-a u') refl)))
          (⊢lam (ty-El dDom) inner))
        (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Πʳ (stepᵀ (El-⌜Hom⌝ (pwBody C₀) W u') chU₂)))
               (csymᵀ (ctrnᵀ cC'
                         (ctrnᵀ (credᵀ (El-⌜Hom⌝ C₀ A₀ u))
                                (red→≅ᵀ chU₁)))))
  where
  C₀ A₀ : RTm ⌊ Γ ⌋
  C₀ = subTm (single t) c
  A₀ = subTm (single t) a
  keyT : pw? C₀ ≡ true
  keyT = pw?-sub (single t) c key

  cA : A ≅ᵀ El C₀
  cA = csymᵀ (subst (λ z → El C₀ ≅ᵀ z) (wk-cancel t A)
                    (≅ᵀ-sub (single t) cv))

  dC₀ : Γ ⊢ C₀ ∷ U
  dC₀ = ⊢[] dcM dt
  dA₀ : Γ ⊢ A₀ ∷ El C₀
  dA₀ = ⊢[] daM dt

  D : RTy ⌊ Γ ⌋
  D = El (pwDom C₀)
  ΓD : Ctx
  ΓD = Γ ▹ D
  A″ : RTy (⌊ Γ ⌋ ∙)
  A″ = El (pwBody C₀)
  ΓDA : Ctx
  ΓDA = ΓD ▹ A″

  genC = pw-gen dC₀ keyT
  dDom : Γ ⊢ pwDom C₀ ∷ U
  dDom = Σ.fst genC
  dBody : ΓD ⊢ pwBody C₀ ∷ U
  dBody = Σ.snd genC

  -- raw-rule ↔ typed-form bridges
  eq-c-in : renTm pwShift (pwBody c) ≡ renTm vs (pwBody C₀)
  eq-c-in =
    trans (ren-as-sub pwShift (pwBody c))
      (trans (subTm-occ (pwBody c) agree)
        (trans (sym (renTm-subTm (pwBody c)))
               (cong (renTm vs) (sym (pwBody-sub (single t) c key)))))
    where
    dead : occTm (vs vz) (pwBody c) ≡ false
    dead = pwBody-occ c key hcM
    agree : ∀ y → occTm y (pwBody c) ≡ true →
            var (pwShift y) ≡ (vs ᵣ∘ₛ extS (single t)) y
    agree vz o = refl
    agree (vs vz) o with trans (sym o) dead
    ... | ()
    agree (vs (vs i)) o = refl

  a-comp : renTm vs a ≡ renTm vs (renTm vs A₀)
  a-comp = trans (ren-as-sub vs a)
             (trans (subTm-occ a agree)
               (sym (trans (renTm-renTm A₀) (renTm-subTm a))))
    where
    agree : ∀ y → occTm y a ≡ true →
            var (vs y) ≡ ((vs ∘ᵣ vs) ᵣ∘ₛ single t) y
    agree vz o with trans (sym o) haM
    ... | ()
    agree (vs i) o = refl

  eq-a-in : app (renTm vs a) (var (vs vz))
            ≡ renTm vs (app (renTm vs A₀) (var vz))
  eq-a-in = cong (λ z → app z (var (vs vz))) a-comp

  -- endpoint agreement (the motive's components are endpoint-blind)
  eq-cu : subTm (single u) c ≡ C₀
  eq-cu = subTm-occ c agree
    where
    agree : ∀ y → occTm y c ≡ true → single u y ≡ single t y
    agree vz o with trans (sym o) hcM
    ... | ()
    agree (vs i) o = refl
  eq-au : subTm (single u) a ≡ A₀
  eq-au = subTm-occ a agree
    where
    agree : ∀ y → occTm y a ≡ true → single u y ≡ single t y
    agree vz o with trans (sym o) haM
    ... | ()
    agree (vs i) o = refl

  W t' u' : RTm (⌊ Γ ⌋ ∙)
  W  = app (renTm vs A₀) (var vz)
  t' = app (renTm vs t) (var vz)
  u' = app (renTm vs u) (var vz)

  cdU = pw-Hom-decode C₀ keyT A₀ u
  BodyU : RTy (⌊ Γ ⌋ ∙)
  BodyU = Σ.fst cdU
  chU₁ : Hom (El C₀) A₀ u ⟶ᵀ* Π (El (pwDom C₀)) BodyU
  chU₁ = Σ.fst (Σ.snd cdU)
  chU₂ : Hom (El (pwBody C₀)) W u' ⟶ᵀ* BodyU
  chU₂ = Σ.snd (Σ.snd cdU)

  cdP = pw-Hom-decode C₀ keyT t u
  BodyP : RTy (⌊ Γ ⌋ ∙)
  BodyP = Σ.fst cdP
  chP₁ : Hom (El C₀) t u ⟶ᵀ* Π (El (pwDom C₀)) BodyP
  chP₁ = Σ.fst (Σ.snd cdP)
  chP₂ : Hom (El (pwBody C₀)) t' u' ⟶ᵀ* BodyP
  chP₂ = Σ.snd (Σ.snd cdP)

  inst-c : (w : RTm (⌊ Γ ⌋ ∙)) →
           subTm (single w) (renTm pwShift (pwBody c)) ≡ pwBody C₀
  inst-c w = trans (cong (subTm (single w)) eq-c-in)
                   (wk-cancel-tm w (pwBody C₀))
  inst-a : (w : RTm (⌊ Γ ⌋ ∙)) →
           subTm (single w) (app (renTm vs a) (var (vs vz))) ≡ W
  inst-a w =
    cong (λ z → app z (var vz))
         (trans (cong (subTm (single w)) a-comp)
                (wk-cancel-tm w (renTm vs A₀)))

  dc-in : ΓDA ⊢ renTm pwShift (pwBody c) ∷ U
  dc-in = subst (λ z → ΓDA ⊢ z ∷ U) (sym eq-c-in)
                (⊢wk {Γ = ΓD} {B = A″} dBody)

  da-in : ΓDA ⊢ app (renTm vs a) (var (vs vz))
              ∷ El (renTm pwShift (pwBody c))
  da-in = ⊢-cast (cong El (sym eq-c-in))
            (subst (λ z → ΓDA ⊢ z ∷ El (renTm vs (pwBody C₀)))
                   (sym eq-a-in)
                   (⊢wk {Γ = ΓD} {B = A″} (pw-app dA₀ keyT)))

  dv-in : ΓDA ⊢ var vz ∷ El (renTm pwShift (pwBody c))
  dv-in = ⊢-cast (cong El (sym eq-c-in)) (⊢var here)

  hc-in : occTm vz (renTm pwShift (pwBody c)) ≡ false
  hc-in = occ-ren-tm avoids-pwShift (pwBody c)

  ha-in : occTm vz (app (renTm vs a) (var (vs vz))) ≡ false
  ha-in = ∨-false (occ-ren-tm avoids-wk a) refl

  dt-in : ΓD ⊢ t' ∷ A″
  dt-in = pw-app (⊢conv dt cA) keyT
  du-in : ΓD ⊢ u' ∷ A″
  du-in = pw-app (⊢conv du cA) keyT

  glam = gen-lam dp
  A₁ : RTy ⌊ Γ ⌋
  A₁ = Σ.fst glam
  B₁ : RTy (⌊ Γ ⌋ ∙)
  B₁ = Σ.fst (Σ.snd glam)
  cΠ : Hom A t u ≅ᵀ Π A₁ B₁
  cΠ = Σ.fst (Σ.snd (Σ.snd glam))
  tyA₁ : Γ ⊢ty A₁
  tyA₁ = Σ.fst (Σ.snd (Σ.snd (Σ.snd glam)))
  d-f : (Γ ▹ A₁) ⊢ f ∷ B₁
  d-f = Σ.snd (Σ.snd (Σ.snd (Σ.snd glam)))

  cΠ' : Π A₁ B₁ ≅ᵀ Π (El (pwDom C₀)) BodyP
  cΠ' = ctrnᵀ (csymᵀ cΠ) (ctrnᵀ (≅ᵀ-Homᵀ cA) (red→≅ᵀ chP₁))

  dp-in : ΓD ⊢ f ∷ Hom A″ t' u'
  dp-in = ⊢conv (ctx-conv d-f (csymᵀ (Σ.fst (Π-inj cΠ'))))
                (ctrnᵀ (Σ.snd (Π-inj cΠ')) (csymᵀ (red→≅ᵀ chP₂)))

  de-in : ΓD ⊢ app (renTm vs e₀) (var vz)
             ∷ El (subTm (single t')
                     (⌜Hom⌝ (renTm pwShift (pwBody c))
                            (app (renTm vs a) (var (vs vz)))
                            (var vz)))
  de-in = ⊢-cast
            (cong El (sym (⌜Hom⌝-cong₃ (inst-c t') (inst-a t') refl)))
            (pw-app de keyT)

  inner : ΓD ⊢ tr (⌜Hom⌝ (renTm pwShift (pwBody c))
                         (app (renTm vs a) (var (vs vz)))
                         (var vz))
                  f (app (renTm vs e₀) (var vz))
             ∷ El (subTm (single u')
                     (⌜Hom⌝ (renTm pwShift (pwBody c))
                            (app (renTm vs a) (var (vs vz)))
                            (var vz)))
  -- ★ the hereditary premise earns its keep here: `tr-pw` rewrites the
  -- motive code to `pwBody c`, and `nonatc-pwBody` is exactly what says
  -- that stays Nat-free.
  inner = ⊢tr dc-in da-in dv-in
              (nonatc-ren pwShift (nonatc-pwBody c ncM key))
              hc-in ha-in dt-in du-in dp-in de-in

  eq→≅ᵀ : {X Y : RTy ⌊ Γ ⌋} → X ≡ Y → X ≅ᵀ Y
  eq→≅ᵀ refl = crflᵀ

  cC' = ctrnᵀ cC (eq→≅ᵀ (cong El (⌜Hom⌝-cong₃ eq-cu eq-au refl)))
sr d (tr-taut f e₀) with gen-tr d
... | tgC (mkTrInv cM aM () A t u dcM daM dvM ncM hcM haM dt du dp de cC)
... | tgU (mkTrInvU refl t u dt du dp de cC) with gen-lam dp
...   | A₁ , (B₁ , (cΠ , (tyA₁ , d-f))) with church-rosserᵀ cΠ
...     | W , (rL , rR) with Π-reduct rR
...       | mkΠRed P₂ Q₂ eqW rP rQ
            with hom-to-Π nn-U (subst (Hom U t u ⟶ᵀ*_) eqW rL)
...         | via-Π rA with U-reduct rA
...           | ()
sr d (tr-taut f e₀) | tgU (mkTrInvU refl t u dt du dp de cC)
    | A₁ , (B₁ , (cΠ , (tyA₁ , d-f))) | W , (rL , rR)
    | mkΠRed P₂ Q₂ eqW rP rQ | via-U rA rt ru rEt rEu =
      ⊢conv
        (⊢-cast (cong El (wk-cancel-tm e₀ u))
          (⊢conv
            (⊢app (⊢lam tyA₁ d-f)
              (⊢conv de
                (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El rt) rEt))
                       (csymᵀ (red→≅ᵀ rP)))))
            (≅ᵀ-sub (single e₀)
              (ctrnᵀ (red→≅ᵀ rQ)
                     (csymᵀ (red→≅ᵀ
                       (⟶ᵀ*-trans (⟶ᵀ*-El (⟶*-ren vs ru)) rEu)))))))
        (csymᵀ cC)
-- congruence cases for the three new formers.
sr d (ξ-⌜Hom⌝ᶜ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) =
      ⊢conv (⊢⌜Hom⌝ (sr dc r) (⊢conv da (credᵀ (ξ-El r)))
                    (⊢conv db (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-⌜Hom⌝ˡ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Hom⌝ dc (sr da r) db) (csymᵀ cU)
sr d (ξ-⌜Hom⌝ʳ r) with gen-⌜Hom⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Hom⌝ dc da (sr db r)) (csymᵀ cU)
sr d (ξ-hreflᶜ r) with gen-hrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢hrefl (sr dc r) (⊢conv dt (credᵀ (ξ-El r))))
            (csymᵀ (ctrnᵀ cH (credᵀ (ξ-Homᵀ (ξ-El r)))))
sr d (ξ-hreflᵃ r) with gen-hrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢hrefl dc (sr dt r))
            (csymᵀ (ctrnᵀ cH (ctrnᵀ (credᵀ (ξ-Homˡ r)) (credᵀ (ξ-Homʳ r)))))
sr d (ξ-trᵈ r) with gen-tr d
... | tgU (mkTrInvU refl t u dt du dp de cC) with r
...   | ()
sr d (ξ-trᵈ r) | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
  with hom-step r
...   | hsᶜ rc =
        ⊢conv (⊢tr (sr dcM rc) (⊢conv daM (credᵀ (ξ-El rc)))
                   (⊢conv dvM (credᵀ (ξ-El rc)))
                   (nonatc-red ncM rc) (occ-red rc hcM) haM dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
              (csymᵀ (ctrnᵀ cC (credᵀ (ξ-El (⟶-sub (single u) r)))))
...   | hsˡ ra =
        ⊢conv (⊢tr dcM (sr daM ra) dvM ncM hcM (occ-red ra haM) dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
              (csymᵀ (ctrnᵀ cC (credᵀ (ξ-El (⟶-sub (single u) r)))))
...   | hsʳ ()
sr d (ξ-trᵖ r) with gen-tr d
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC) =
      ⊢conv (⊢tr dcM daM dvM ncM hcM haM dt du (sr dp r) de) (csymᵀ cC)
... | tgU (mkTrInvU refl t u dt du dp de cC) =
      ⊢conv (⊢trU dt du (sr dp r) de) (csymᵀ cC)
sr d (ξ-trᵉ r) with gen-tr d
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC) =
      ⊢conv (⊢tr dcM daM dvM ncM hcM haM dt du dp (sr de r)) (csymᵀ cC)
... | tgU (mkTrInvU refl t u dt du dp de cC) =
      ⊢conv (⊢trU dt du dp (sr de r)) (csymᵀ cC)
-- ★ directed `ap` (SpikeAp).  The J case extracts the endpoint
-- conversions via confluence against the STABLE source ambient (the
-- typing key): both sides decompose componentwise, and the body's
-- substitution instances ride the endpoint chains.
sr d (ap-J cB b c₁ s key) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC)))))))))
      with gen-hrefl dp
...   | (dc₁ , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = cA} (stkC?→stkA? cA (flat→stk cA keyA))
                          , nn-El (stkC?→hd cA (flat→stk cA keyA))) rL
...       | A₂ , (t₁ , (u₁ , (eqW , (rt , ru))))
            with Hom-to-Hom
                   (homAmb→ (subst (Hom (El cA) t u ⟶ᵀ*_) eqW rL)
                            (nn-El (stkC?→hd cA (flat→stk cA keyA))))
                   (subst (Hom (El cA) t u ⟶ᵀ*_) eqW rL)
              |  Hom-to-Hom
                   (homAmb→ (subst (Hom (El cA) t u ⟶ᵀ*_) eqW rL)
                            (nn-El (stkC?→hd cA (flat→stk cA keyA))))
                   (subst (Hom (El _) s s ⟶ᵀ*_) eqW rR)
...         | mkHomRed rAL rt' ru' | mkHomRed rAR rs₁ rs₂ =
              ⊢conv
                (⊢hrefl dcB
                  (⊢-cast (cong El (wk-cancel-tm s cB))
                    (⊢[] db
                      (⊢conv ds (ctrnᵀ (red→≅ᵀ rAR)
                                       (csymᵀ (red→≅ᵀ rAL)))))))
                (ctrnᵀ
                  (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Homˡ (subTm-monoˢ (single-mono rs₁) b)))
                    (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Homʳ (subTm-monoˢ (single-mono rs₂) b)))
                      (ctrnᵀ (csymᵀ (red→≅ᵀ (⟶ᵀ*-Homʳ (subTm-monoˢ (single-mono ru) b))))
                             (csymᵀ (red→≅ᵀ (⟶ᵀ*-Homˡ (subTm-monoˢ (single-mono rt) b)))))))
                  (csymᵀ cC))
sr d (ξ-apᶜ r) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC))))))))) =
      ⊢conv (⊢ap dcA keyA (sr dcB r)
                 (⊢conv db (credᵀ (ξ-El (⟶-ren vs r))))
                 dt du dp)
            (ctrnᵀ (csymᵀ (credᵀ (ξ-Homᵀ (ξ-El r)))) (csymᵀ cC))
sr d (ξ-apᵇ {b = b} {b' = b'} r) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC))))))))) =
      ⊢conv (⊢ap dcA keyA dcB (sr db r) dt du dp)
            (ctrnᵀ
              (csymᵀ (red→≅ᵀ
                (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (step (⟶-sub (single t) r) done))
                           (⟶ᵀ*-Homʳ (step (⟶-sub (single u) r) done)))))
              (csymᵀ cC))
sr d (ξ-apᵖ r) with gen-ap d
... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC))))))))) =
      ⊢conv (⊢ap dcA keyA dcB db dt du (sr dp r)) (csymᵀ cC)
-- ★ the two-former kernel.  `jsub-refl`'s endpoint conversion is the
-- `tr-J-base` pattern with the EASIER decomposition (`Id-reduct`:
-- Id is inert, both church-rosser arms split componentwise).
sr d (jsub-refl dM c₁ s e₀) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) with gen-idrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR) with Id-reduct rL | Id-reduct rR
...       | A₁ , (t₁ , (u₁ , (eqW , (rA , (rt , ru)))))
          | A₂ , (s₁ , (s₂ , (eqW' , (rA' , (rs₁ , rs₂)))))
            with trans (sym eqW) eqW'
...         | refl =
              ⊢conv de
                (ctrnᵀ (ctrnᵀ (mono-El[] dM rt)
                         (ctrnᵀ (csymᵀ (mono-El[] dM rs₁))
                           (ctrnᵀ (mono-El[] dM rs₂)
                             (csymᵀ (mono-El[] dM ru)))))
                       (csymᵀ cC))
sr d (ξ-jsubᵈ r) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) =
      ⊢conv (⊢jsub (sr dd r) dt du dp
                   (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
            (ctrnᵀ (csymᵀ (credᵀ (ξ-El (⟶-sub (single u) r)))) (csymᵀ cC))
sr d (ξ-jsubᵖ r) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) =
      ⊢conv (⊢jsub dd dt du (sr dp r) de) (csymᵀ cC)
sr d (ξ-jsubᵉ r) with gen-jsub d
... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC))))))) =
      ⊢conv (⊢jsub dd dt du dp (sr de r)) (csymᵀ cC)
sr d (ξ-⌜Id⌝ᶜ r) with gen-⌜Id⌝ d
... | (dc , (da , (db , cU))) =
      ⊢conv (⊢⌜Id⌝ (sr dc r) (⊢conv da (credᵀ (ξ-El r)))
                   (⊢conv db (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-⌜Id⌝ˡ r) with gen-⌜Id⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Id⌝ dc (sr da r) db) (csymᵀ cU)
sr d (ξ-⌜Id⌝ʳ r) with gen-⌜Id⌝ d
... | (dc , (da , (db , cU))) = ⊢conv (⊢⌜Id⌝ dc da (sr db r)) (csymᵀ cU)
sr d (ξ-idreflᶜ r) with gen-idrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢idrefl (sr dc r) (⊢conv dt (credᵀ (ξ-El r))))
            (csymᵀ (ctrnᵀ cH (credᵀ (ξ-Idᵀ (ξ-El r)))))
sr d (ξ-idreflᵃ r) with gen-idrefl d
... | (dc , (dt , cH)) =
      ⊢conv (⊢idrefl dc (sr dt r))
            (csymᵀ (ctrnᵀ cH (ctrnᵀ (credᵀ (ξ-Idˡ r)) (credᵀ (ξ-Idʳ r)))))

------------------------------------------------------------------------
-- Type preservation for MULTI-step reduction — the immediate corollary.
------------------------------------------------------------------------

sr* : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ A → t ⟶* u → Γ ⊢ u ∷ A
sr* d done       = d
sr* d (step r p) = sr* (sr d r) p
