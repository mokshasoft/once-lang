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
        ; DIh; Fin; ⌜Fin⌝; dσ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit; cong₄; cong₃ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; _∨_; occTm; ∨-false; ∨-false₁; ∨-false₂; occ-ren-eq
        ; occ-sub; eqv; Avoids; occ-ren-tm; avoids-wk; PosC; posc-var
        ; posc-Hom; posc-ren; posc-sub; pw?; stkC?; pwDom; pwBody; pwShift
        ; pw?-sub; stkC?-sub; pwBody-sub; pwDom-sub; pwBody-occ; ren-as-sub
        ; avoids-pwShift; subTm-occ; stkC?-ren; wk-ren-tm; wk-sub-tm; flat?
        ; flat→stk; flat?-ren; flat?-sub; NoNatC; nnc-base; nnc-Unit; nnc-Π
        ; nnc-Σ; nnc-Hom; nnc-Id; nonatc-ren; nonatc-sub; nonatc-pwBody; stkA?
        ; stkA?-ren; stkA?-sub; stkC?→stkA?; NoNatHd; nnh-base; nnh-Unit
        ; nnh-Σ; nnh-Id; nnh-Π; nnh-Hom; nnh-IMu; nonatc→hd; stkC?→hd
        ; occ-εwkTm
        ; nnh-Fin )
open import DirectedHoTT.Spec.Typing
  using ( single; nrs; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ
        ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; _⟶_; β; βfst
        ; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ
        ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss; ξ-ordtrᵃ
        ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ
        ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; tr-J-base; tr-J-Σ; tr-J-Id; tr-J-Unit; tr-J-IMu
        ; tr-taut; hrefl-pw; tr-J-Hom; tr-pw; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜IMu⌝
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
        ; El-⌜Fin⌝; DIh-ι; DIh-σ; DIh-ρ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dι; ξ-dσˢ; ξ-dσᶠ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dpayⁱ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ; ξ-psplitᵍ; tr-J-Fin; ⊢⌜Fin⌝; ⊢dι; ⊢dσ; ⊢dρ; ⊢dpay; ⊢dih; ⊢fzero; ⊢fsuc; ⊢fcase; ⊢fcase0; ⊢psplit; ty-Desc; ty-DIh; ty-Fin; MethTy; motCtx; methS; wk2M; single2; pairS; fsucS )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ≅ᵀ-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶-ren; ⟶*-ren; ⟶*-appʳ; ren-comm; subTm-monoˢ; extS-mono; single-mono
        ; stkC?-red; stkA?-red; church-rosser
        ; ⟶*-trans; ⟶*-dpayᴵ; ⟶*-dpayᴰ; ⟶*-dpayᶜ; ⟶*-dpayⁱ )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( sub-comm; ⟶ᵀ-sub )
open import DirectedHoTT.Metatheory.Injectivity
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El
        ; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ
        ; ⟶ᵀ*-Homᵀ; ⟶ᵀ*-Homˡ; ⟶ᵀ*-Homʳ; red→≅ᵀ; Π-inj; Σ-inj
        ; ⟶ᵀ*-Idᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; Id-reduct
        ; church-rosserᵀ; Π-reduct; ΠRed; mkΠRed
        ; ⟶ᵀ*-IMu; IMu-inj; IMu-reduct; IMuRed; mkIMuRed
        ; Desc-inj; Fin-inj; ⟶ᵀ*-Desc )

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
nonathd-red nnh-Fin ()
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
  nn-Fin  : {n : ℕ} → NoNat (Fin {Γ} n)

nonat-red : {A A' : RTy Γ} → NoNat A → A ⟶ᵀ A' → NoNat A'
nonat-red nn-base ()
nonat-red nn-U ()
nonat-red nn-Unit ()
nonat-red nn-Fin ()
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

-- application with the argument typed at a propositionally equal domain;
--   leaves the codomain for Agda to read off the function's type.
⊢app-cast : {Γ : Ctx} {A A' : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} {t u : RTm ⌊ Γ ⌋} →
            A ≡ A' → Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A' → Γ ⊢ app t u ∷ subTy (single u) B
⊢app-cast refl dt du = ⊢app dt du

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

-- the two-slot single substitution as a typed substitution
⊢single2 : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} {x y : RTm ⌊ Γ ⌋} →
           Γ ⊢ x ∷ A → Γ ⊢ y ∷ subTy (single x) B → Sub⊢ ((Γ ▹ A) ▹ B) Γ (single2 x y)
⊢single2 {B = B} {x = x} {y = y} dx dy here = ⊢-cast (sym (s2-wk x y B)) dy
⊢single2 {A = A} {x = x} {y = y} dx dy (there here) = ⊢-cast (sym (s2-cancel x y A)) dx
⊢single2 {x = x} {y = y} dx dy (there (there {A = A₀} v)) =
  ⊢-cast (sym (s2-cancel x y A₀)) (⊢var v)

-- the payload of `p : El (dpay I D C i)` at `i ≅ i'`, `I ≅ I'`, `D ≅ D'`
dpay-≅ : {Γ : Cx} {I I' D D' i i' : RTm Γ} → I ≅ I' → D ≅ D' → i ≅ i' →
         El (dpay I D D i) ≅ᵀ El (dpay I' D' D' i')
dpay-≅ {I' = I'} {D = D} {D' = D'} {i = i} {i' = i'} cI cD ci =
  ctrnᵀ (conv-lift (λ x → El (dpay x D D i)) (λ r → ⟶ᵀ*-El (⟶*-dpayᴵ r)) cI)
    (ctrnᵀ (conv-lift (λ x → El (dpay I' x x i))
                      (λ r → ⟶ᵀ*-El (⟶*-trans (⟶*-dpayᴰ r) (⟶*-dpayᶜ r))) cD)
           (conv-lift (λ x → El (dpay I' D' D' x)) (λ r → ⟶ᵀ*-El (⟶*-dpayⁱ r)) ci))

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
  -- ★ `IMu I D i` is never `U`, never `Π` — but its slots reduce, so
  --   it is INERT-SHAPED, not inert.  `Fin n` is inert.
  st-IMu  : {I D i : RTm Γ} → StkAmb (IMu I D i)
  st-Fin  : {n : ℕ} → StkAmb (Fin {Γ} n)
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
stamb-red st-Fin ()
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
-- ★★ LEVITATION: generation lemmas for the levitated formers — the rule,
--   then `⊢conv` composing the conversion (the file's two-clause shape).
gen-con : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ con p ∷ C →
          Σ (RTm ⌊ Γ ⌋) (λ I → Σ (RTm ⌊ Γ ⌋) (λ D → Σ (RTm ⌊ Γ ⌋) (λ i →
            (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ Desc I) × ((Γ ⊢ i ∷ El I) ×
            ((Γ ⊢ p ∷ El (dpay I D D i)) × (C ≅ᵀ IMu I D i)))))))
gen-con (⊢con dI dD di dp) = _ , (_ , (_ , (dI , (dD , (di , (dp , crflᵀ))))))
gen-con (⊢conv d c) with gen-con d
... | I , (D , (i , (dI , (dD , (di , (dp , c')))))) =
      I , (D , (i , (dI , (dD , (di , (dp , ctrnᵀ (csymᵀ c) c'))))))

gen-ielim : {Γ : Ctx} {D i e t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ielim D i e t ∷ C →
            Σ (RTm ⌊ Γ ⌋) (λ I → Σ (RTy ((⌊ Γ ⌋ ∙) ∙)) (λ M →
              (Γ ⊢ D ∷ Desc I) × ((motCtx Γ I D ⊢ty M) ×
              ((Γ ⊢ e ∷ MethTy I D M) × ((Γ ⊢ i ∷ El I) ×
              ((Γ ⊢ t ∷ IMu I D i) × (C ≅ᵀ iinst i t M)))))))
gen-ielim (⊢ielim dD dM de di dt) = _ , (_ , (dD , (dM , (de , (di , (dt , crflᵀ))))))
gen-ielim (⊢conv d c) with gen-ielim d
... | I , (M , (dD , (dM , (de , (di , (dt , c')))))) =
      I , (M , (dD , (dM , (de , (di , (dt , ctrnᵀ (csymᵀ c) c'))))))

gen-⌜IMu⌝ : {Γ : Ctx} {I D i : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜IMu⌝ I D i ∷ C →
            (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ Desc I) × ((Γ ⊢ i ∷ El I) × (C ≅ᵀ U)))
gen-⌜IMu⌝ (⊢⌜IMu⌝ dI dD di) = dI , (dD , (di , crflᵀ))
gen-⌜IMu⌝ (⊢conv d c) with gen-⌜IMu⌝ d
... | dI , (dD , (di , c')) = dI , (dD , (di , ctrnᵀ (csymᵀ c) c'))

gen-dι : {Γ : Ctx} {j : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dι j ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ I → (Γ ⊢ I ∷ U) × ((Γ ⊢ j ∷ El I) × (C ≅ᵀ Desc I)))
gen-dι (⊢dι dI dj) = _ , (dI , (dj , crflᵀ))
gen-dι (⊢conv d c) with gen-dι d
... | I , (dI , (dj , c')) = I , (dI , (dj , ctrnᵀ (csymᵀ c) c'))

gen-dσ : {Γ : Ctx} {S f : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dσ S f ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ I → (Γ ⊢ I ∷ U) × ((Γ ⊢ S ∷ U) ×
           ((Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I))) × (C ≅ᵀ Desc I))))
gen-dσ (⊢dσ dI dS df) = _ , (dI , (dS , (df , crflᵀ)))
gen-dσ (⊢conv d c) with gen-dσ d
... | I , (dI , (dS , (df , c'))) = I , (dI , (dS , (df , ctrnᵀ (csymᵀ c) c')))

gen-dρ : {Γ : Ctx} {j C₀ : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dρ j C₀ ∷ C →
         Σ (RTm ⌊ Γ ⌋) (λ I → (Γ ⊢ I ∷ U) × ((Γ ⊢ j ∷ El I) × ((Γ ⊢ C₀ ∷ Desc I) × (C ≅ᵀ Desc I))))
gen-dρ (⊢dρ dI dj dC) = _ , (dI , (dj , (dC , crflᵀ)))
gen-dρ (⊢conv d c) with gen-dρ d
... | I , (dI , (dj , (dC , c'))) = I , (dI , (dj , (dC , ctrnᵀ (csymᵀ c) c')))

gen-dpay : {Γ : Ctx} {I D C₀ i : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dpay I D C₀ i ∷ C →
           (Γ ⊢ I ∷ U) × ((Γ ⊢ D ∷ Desc I) × ((Γ ⊢ C₀ ∷ Desc I) × ((Γ ⊢ i ∷ El I) × (C ≅ᵀ U))))
gen-dpay (⊢dpay dI dD dC di) = dI , (dD , (dC , (di , crflᵀ)))
gen-dpay (⊢conv d c) with gen-dpay d
... | dI , (dD , (dC , (di , c'))) = dI , (dD , (dC , (di , ctrnᵀ (csymᵀ c) c')))

gen-dih : {Γ : Ctx} {D e C₀ p : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ dih D e C₀ p ∷ C →
          Σ (RTm ⌊ Γ ⌋) (λ I → Σ (RTy ((⌊ Γ ⌋ ∙) ∙)) (λ M → Σ (RTm ⌊ Γ ⌋) (λ i →
            (Γ ⊢ D ∷ Desc I) × ((motCtx Γ I D ⊢ty M) × ((Γ ⊢ e ∷ MethTy I D M) ×
            ((Γ ⊢ C₀ ∷ Desc I) × ((Γ ⊢ i ∷ El I) ×
            ((Γ ⊢ p ∷ El (dpay I D C₀ i)) × (C ≅ᵀ DIh D M C₀ p)))))))))
gen-dih (⊢dih dD dM de dC di dp) = _ , (_ , (_ , (dD , (dM , (de , (dC , (di , (dp , crflᵀ))))))))
gen-dih (⊢conv d c) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , c')))))))) =
      I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , ctrnᵀ (csymᵀ c) c'))))))))

gen-fsuc : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fsuc t ∷ C →
           Σ ℕ (λ n → (Γ ⊢ t ∷ Fin n) × (C ≅ᵀ Fin (suc n)))
gen-fsuc (⊢fsuc dt) = _ , (dt , crflᵀ)
gen-fsuc (⊢conv d c) with gen-fsuc d
... | n , (dt , c') = n , (dt , ctrnᵀ (csymᵀ c) c')

gen-fcase : {Γ : Ctx} {t a : RTm ⌊ Γ ⌋} {b : RTm (⌊ Γ ⌋ ∙)} {C : RTy ⌊ Γ ⌋} →
            Γ ⊢ fcase t a b ∷ C →
            Σ ℕ (λ n → Σ (RTy (⌊ Γ ⌋ ∙)) (λ P →
              ((Γ ▹ Fin (suc n)) ⊢ty P) × ((Γ ⊢ t ∷ Fin (suc n)) ×
              ((Γ ⊢ a ∷ subTy (single fzero) P) × (((Γ ▹ Fin n) ⊢ b ∷ subTy fsucS P) ×
              (C ≅ᵀ subTy (single t) P))))))
gen-fcase (⊢fcase dP dt da db) = _ , (_ , (dP , (dt , (da , (db , crflᵀ)))))
gen-fcase (⊢conv d c) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , c'))))) = n , (P , (dP , (dt , (da , (db , ctrnᵀ (csymᵀ c) c')))))

gen-fcase0 : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fcase0 t ∷ C →
             Σ (RTy (⌊ Γ ⌋ ∙)) (λ P → ((Γ ▹ Fin zero) ⊢ty P) × ((Γ ⊢ t ∷ Fin zero) ×
               (C ≅ᵀ subTy (single t) P)))
gen-fcase0 (⊢fcase0 dP dt) = _ , (dP , (dt , crflᵀ))
gen-fcase0 (⊢conv d c) with gen-fcase0 d
... | P , (dP , (dt , c')) = P , (dP , (dt , ctrnᵀ (csymᵀ c) c'))

gen-psplit : {Γ : Ctx} {b : RTm ((⌊ Γ ⌋ ∙) ∙)} {q : RTm ⌊ Γ ⌋} {C : RTy ⌊ Γ ⌋} →
             Γ ⊢ psplit b q ∷ C →
             Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTy (⌊ Γ ⌋ ∙)) (λ B → Σ (RTy (⌊ Γ ⌋ ∙)) (λ P →
               ((Γ ▹ Σ' A B) ⊢ty P) × ((Γ ⊢ q ∷ Σ' A B) ×
               ((((Γ ▹ A) ▹ B) ⊢ b ∷ subTy pairS P) × (C ≅ᵀ subTy (single q) P))))))
gen-psplit (⊢psplit dP dq db) = _ , (_ , (_ , (dP , (dq , (db , crflᵀ)))))
gen-psplit (⊢conv d c) with gen-psplit d
... | A , (B , (P , (dP , (dq , (db , c'))))) = A , (B , (P , (dP , (dq , (db , ctrnᵀ (csymᵀ c) c')))))

-- ★★ THE PAYLOAD'S σ AND ρ STEPS: a payload of a `dσ`/`dρ` telescope is a
--   pair; its halves are typed at the chosen branch / the recursive field
--   and the rest.  Used by `sr` at `dih-σ`/`dih-ρ` and by `srᵀ` at
--   `DIh-σ`/`DIh-ρ` (Validity).
dσ-step : {Γ : Ctx} {I D S f i p : RTm ⌊ Γ ⌋} →
          Γ ⊢ dσ S f ∷ Desc I → Γ ⊢ p ∷ El (dpay I D (dσ S f) i) →
          (Γ ⊢ app f (fst p) ∷ Desc I) × (Γ ⊢ snd p ∷ El (dpay I D (app f (fst p)) i))
dσ-step {I = I} {D = D} {S = S} {f = f} {i = i} {p = p} dC dp with gen-dσ dC
... | I₀ , (dI₀ , (dS , (df , c))) =
      ⊢conv (⊢-cast (cong Desc (wk-cancel-tm (fst p) I₀)) (⊢app df (⊢fst dp'))) (csymᵀ c)
    , ⊢-cast (cong₄ (λ a b g k → El (dpay a b (app g (fst p)) k))
                    (wk-cancel-tm (fst p) I) (wk-cancel-tm (fst p) D)
                    (wk-cancel-tm (fst p) f) (wk-cancel-tm (fst p) i))
             (⊢snd dp')
  where
  dp' = ⊢conv dp (ctrnᵀ (credᵀ (ξ-El (dpay-σ I D S f i))) (credᵀ (El-⌜Σ⌝ _ _)))

dρ-step : {Γ : Ctx} {I D j C i p : RTm ⌊ Γ ⌋} →
          Γ ⊢ dρ j C ∷ Desc I → Γ ⊢ p ∷ El (dpay I D (dρ j C) i) →
          (Γ ⊢ j ∷ El I) × ((Γ ⊢ C ∷ Desc I) ×
          ((Γ ⊢ fst p ∷ IMu I D j) × (Γ ⊢ snd p ∷ El (dpay I D C i))))
dρ-step {I = I} {D = D} {j = j} {C = C} {i = i} {p = p} dC dp with gen-dρ dC
... | I₀ , (_ , (dj , (dC₀ , c))) =
      ⊢conv dj (El-≅ (csym (Desc-inj c)))
    , (⊢conv dC₀ (csymᵀ c)
    , (⊢conv (⊢fst dp') (credᵀ El-⌜IMu⌝)
    , ⊢-cast (cong₄ (λ a b g k → El (dpay a b g k))
                    (wk-cancel-tm (fst p) I) (wk-cancel-tm (fst p) D)
                    (wk-cancel-tm (fst p) C) (wk-cancel-tm (fst p) i))
             (⊢snd dp')))
  where
  dp' = ⊢conv dp (ctrnᵀ (credᵀ (ξ-El (dpay-ρ I D j C i))) (credᵀ (El-⌜Σ⌝ _ _)))

------------------------------------------------------------------------
-- ★★★ LEVITATED INDUCTIVE FAMILIES: the reduction rules.
------------------------------------------------------------------------

-- the payload CODE computes; each reduct is a code again.
sr d (dpay-ι I D j i) with gen-dpay d
... | dI , (dD , (dC , (di , cU))) with gen-dι dC
...   | I₀ , (_ , (dj , c)) =
        ⊢conv (⊢⌜Id⌝ dI (⊢conv dj (El-≅ (csym (Desc-inj c)))) di) (csymᵀ cU)
sr d (dpay-σ I D S f i) with gen-dpay d
... | dI , (dD , (dC , (di , cU))) with gen-dσ dC
...   | I₀ , (dI₀ , (dS , (df , c))) =
        ⊢conv (⊢⌜Σ⌝ dS
                (⊢dpay (⊢wk dI) (⊢wk dD)
                       (⊢conv (⊢-cast (cong Desc (wk-app-vzᵗ I₀)) (⊢app (⊢wk df) (⊢var here)))
                              (≅ᵀ-ren vs (csymᵀ c)))
                       (⊢wk di)))
              (csymᵀ cU)
sr d (dpay-ρ I D j C i) with gen-dpay d
... | dI , (dD , (dC , (di , cU))) with gen-dρ dC
...   | I₀ , (_ , (dj , (dC₀ , c))) =
        ⊢conv (⊢⌜Σ⌝ (⊢⌜IMu⌝ dI dD (⊢conv dj (El-≅ (csym (Desc-inj c)))))
                    (⊢dpay (⊢wk dI) (⊢wk dD) (⊢wk (⊢conv dC₀ (csymᵀ c))) (⊢wk di)))
              (csymᵀ cU)
-- the hypotheses: none at `dι`, the chosen branch's at `dσ`, one
--   recursive call AT ITS OWN INDEX plus the rest at `dρ`.
sr d (dih-ι D e j p) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , cC)))))))) =
      ⊢conv ⊢unit (csymᵀ (ctrnᵀ cC (credᵀ (DIh-ι D M j p))))
sr d (dih-σ D e S f p) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , cC)))))))) with dσ-step dC dp
...   | dC' , dsnd =
        ⊢conv (⊢dih dD dM de dC' di dsnd) (csymᵀ (ctrnᵀ cC (credᵀ (DIh-σ D M S f p))))
sr d (dih-ρ D e j C p) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , cC)))))))) with dρ-step dC dp
...   | dj , (dC' , (dfst , dsnd)) =
        ⊢conv (⊢pair (ren-ty (ty-DIh dD dM dC' di dsnd) there)
                     (⊢ielim dD dM de dj dfst)
                     (⊢-cast (sym (wk-cancel _ _)) (⊢dih dD dM de dC' di dsnd)))
              (csymᵀ (ctrnᵀ cC (credᵀ (DIh-ρ D M j C p))))
-- ★★★ ι.  `IMu-inj` reconciles the constructor's family with the
--   eliminator's (three CONVERSIONS — every slot is a term), the payload
--   is transported once, and the method is applied to index, payload and
--   hypotheses.  The result type is the motive at `con p` by σ-calculus
--   alone (`meth-inst`) — no η.
sr d (ι D i e p) with gen-ielim d
... | I , (M , (dD , (dM , (de , (di , (dt , cC)))))) with gen-con dt
...   | I' , (D' , (i' , (dI' , (dD' , (di' , (dp , cIMu)))))) with IMu-inj cIMu
...     | cI , (cD , ci) =
          ⊢conv (⊢-cast (meth-inst (dih D e D p) p i M)
                  (⊢app-cast (cong₄ DIh (ww-cancel p i D) (wk2M-cancel p i M)
                                        (ww-cancel p i D) refl)
                    (⊢app-cast (cong₃ (λ a b c' → El (dpay a b c' i))
                                      (wk-cancel-tm i I) (wk-cancel-tm i D) (wk-cancel-tm i D))
                      (⊢app de di) dp₁)
                    (⊢dih dD dM de dD di dp₁)))
                (csymᵀ cC)
  where
  dp₁ = ⊢conv dp (dpay-≅ (csym cI) (csym cD) (csym ci))
-- tags and pairs
sr d (fcase-z a b) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) = ⊢conv da (csymᵀ cC)
sr d (fcase-s t a b) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) with gen-fsuc dt
...   | n' , (dt' , c') with Fin-inj c'
...     | refl = ⊢conv (⊢-cast (fsucS-inst t P) (⊢[] db dt')) (csymᵀ cC)
sr d (psplit-β b x y) with gen-psplit d
... | A , (B , (P , (dP , (dq , (db , cC))))) with gen-pair dq
...   | A' , (B' , (cΣ , (dB' , (dx , dy)))) with Σ-inj (csymᵀ cΣ)
...     | cA , cB =
          ⊢conv (⊢-cast (pairS-inst x y P)
                  (sub-lemma db (⊢single2 (⊢conv dx cA) (⊢conv dy (≅ᵀ-sub (single x) cB)))))
                (csymᵀ cC)
-- ★★ the CONGRUENCES.  A stepped description/index/code that occurs in a
--   premise's TYPE is carried there by conversion.
sr d (ξ-⌜IMu⌝ᴵ r) with gen-⌜IMu⌝ d
... | dI , (dD , (di , cU)) =
      ⊢conv (⊢⌜IMu⌝ (sr dI r) (⊢conv dD (credᵀ (ξ-Desc r))) (⊢conv di (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-⌜IMu⌝ᴰ r) with gen-⌜IMu⌝ d
... | dI , (dD , (di , cU)) = ⊢conv (⊢⌜IMu⌝ dI (sr dD r) di) (csymᵀ cU)
sr d (ξ-⌜IMu⌝ⁱ r) with gen-⌜IMu⌝ d
... | dI , (dD , (di , cU)) = ⊢conv (⊢⌜IMu⌝ dI dD (sr di r)) (csymᵀ cU)
sr d (ξ-con r) with gen-con d
... | I , (D , (i , (dI , (dD , (di , (dp , c)))))) = ⊢conv (⊢con dI dD di (sr dp r)) (csymᵀ c)
sr d (ξ-ielimᴰ r) with gen-ielim d
... | I , (M , (dD , (dM , (de , (di , (dt , cC)))))) =
      ⊢conv (⊢ielim (sr dD r) (conv-ctxᵀ (credᵀ (ξ-IMuᴰ (⟶-ren vs r))) dM)
                    (⊢conv de (red→≅ᵀ (MethTy-monoᴰ I M (step r done))))
                    di (⊢conv dt (credᵀ (ξ-IMuᴰ r))))
            (csymᵀ cC)
sr d (ξ-ielimⁱ r) with gen-ielim d
... | I , (M , (dD , (dM , (de , (di , (dt , cC)))))) =
      ⊢conv (⊢ielim dD dM de (sr di r) (⊢conv dt (credᵀ (ξ-IMuⁱ r))))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (iinst-mono M _ (step r done)))))
sr d (ξ-ielimᵉ r) with gen-ielim d
... | I , (M , (dD , (dM , (de , (di , (dt , cC)))))) =
      ⊢conv (⊢ielim dD dM (sr de r) di dt) (csymᵀ cC)
sr d (ξ-ielimᵗ {i = i} r) with gen-ielim d
... | I , (M , (dD , (dM , (de , (di , (dt , cC)))))) =
      ⊢conv (⊢ielim dD dM de di (sr dt r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (iinst-monoˢ M i (step r done)))))
sr d (ξ-dι r) with gen-dι d
... | I , (dI , (dj , c)) = ⊢conv (⊢dι dI (sr dj r)) (csymᵀ c)
sr d (ξ-dσˢ r) with gen-dσ d
... | I , (dI , (dS , (df , c))) =
      ⊢conv (⊢dσ dI (sr dS r) (⊢conv df (credᵀ (ξ-Πˡ (ξ-El r))))) (csymᵀ c)
sr d (ξ-dσᶠ r) with gen-dσ d
... | I , (dI , (dS , (df , c))) = ⊢conv (⊢dσ dI dS (sr df r)) (csymᵀ c)
sr d (ξ-dρʲ r) with gen-dρ d
... | I , (dI , (dj , (dC , c))) = ⊢conv (⊢dρ dI (sr dj r) dC) (csymᵀ c)
sr d (ξ-dρᶜ r) with gen-dρ d
... | I , (dI , (dj , (dC , c))) = ⊢conv (⊢dρ dI dj (sr dC r)) (csymᵀ c)
sr d (ξ-dpayᴵ r) with gen-dpay d
... | dI , (dD , (dC , (di , cU))) =
      ⊢conv (⊢dpay (sr dI r) (⊢conv dD (credᵀ (ξ-Desc r))) (⊢conv dC (credᵀ (ξ-Desc r)))
                   (⊢conv di (credᵀ (ξ-El r))))
            (csymᵀ cU)
sr d (ξ-dpayᴰ r) with gen-dpay d
... | dI , (dD , (dC , (di , cU))) = ⊢conv (⊢dpay dI (sr dD r) dC di) (csymᵀ cU)
sr d (ξ-dpayᶜ r) with gen-dpay d
... | dI , (dD , (dC , (di , cU))) = ⊢conv (⊢dpay dI dD (sr dC r) di) (csymᵀ cU)
sr d (ξ-dpayⁱ r) with gen-dpay d
... | dI , (dD , (dC , (di , cU))) = ⊢conv (⊢dpay dI dD dC (sr di r)) (csymᵀ cU)
sr d (ξ-dihᴰ r) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , cC)))))))) =
      ⊢conv (⊢dih (sr dD r) (conv-ctxᵀ (credᵀ (ξ-IMuᴰ (⟶-ren vs r))) dM)
                  (⊢conv de (red→≅ᵀ (MethTy-monoᴰ I M (step r done))))
                  dC di (⊢conv dp (credᵀ (ξ-El (ξ-dpayᴰ r)))))
            (csymᵀ (ctrnᵀ cC (credᵀ (ξ-DIhᴰ r))))
sr d (ξ-dihᵉ r) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , cC)))))))) =
      ⊢conv (⊢dih dD dM (sr de r) dC di dp) (csymᵀ cC)
sr d (ξ-dihᶜ r) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , cC)))))))) =
      ⊢conv (⊢dih dD dM de (sr dC r) di (⊢conv dp (credᵀ (ξ-El (ξ-dpayᶜ r)))))
            (csymᵀ (ctrnᵀ cC (credᵀ (ξ-DIhᶜ r))))
sr d (ξ-dihᵖ r) with gen-dih d
... | I , (M , (i , (dD , (dM , (de , (dC , (di , (dp , cC)))))))) =
      ⊢conv (⊢dih dD dM de dC di (sr dp r)) (csymᵀ (ctrnᵀ cC (credᵀ (ξ-DIhᵖ r))))
sr d (ξ-fsuc r) with gen-fsuc d
... | n , (dt , c) = ⊢conv (⊢fsuc (sr dt r)) (csymᵀ c)
sr d (ξ-fcaseᵗ r) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) =
      ⊢conv (⊢fcase dP (sr dt r) da db)
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) P))))
sr d (ξ-fcaseᵃ r) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) = ⊢conv (⊢fcase dP dt (sr da r) db) (csymᵀ cC)
sr d (ξ-fcaseᵇ r) with gen-fcase d
... | n , (P , (dP , (dt , (da , (db , cC))))) = ⊢conv (⊢fcase dP dt da (sr db r)) (csymᵀ cC)
sr d (ξ-fcase0 r) with gen-fcase0 d
... | P , (dP , (dt , cC)) =
      ⊢conv (⊢fcase0 dP (sr dt r))
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) P))))
sr d (ξ-psplitᵇ r) with gen-psplit d
... | A , (B , (P , (dP , (dq , (db , cC))))) = ⊢conv (⊢psplit dP dq (sr db r)) (csymᵀ cC)
sr d (ξ-psplitᵍ r) with gen-psplit d
... | A , (B , (P , (dP , (dq , (db , cC))))) =
      ⊢conv (⊢psplit dP (sr dq r) db)
            (csymᵀ (ctrnᵀ cC (red→≅ᵀ (subTy-monoˢ (single-mono (step r done)) P))))

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
-- ★ §10.4's subject-reduction obligation.  `tr-J-Unit`'s proof VERBATIM:
--   the only input that differs is the stuck-ambient witness, which is
--   `st-el {c = ⌜IMu⌝ …} refl` (that is `stkC? (⌜IMu⌝ …) = true`) paired
--   with `nn-El nnh-IMu`.
sr d (tr-J-IMu {I = Iⁱ} {D = Dⁱ} {iˣ = iˣ} cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜IMu⌝ Iⁱ Dⁱ iˣ} refl , nn-El nnh-IMu) rR
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
-- ★ tags: `Hom (Fin n)` computes nothing either — the same proof.
sr d (tr-J-Fin {n = n} cm am mm s e₀) with gen-tr d
... | tgU (mkTrInvU () t u dt du dp de cC)
... | tgC (mkTrInv cM aM refl A t u dcM daM dvM ncM hcM haM dt du dp de cC)
      with gen-hrefl dp
...   | (dc , (ds , cH)) with church-rosserᵀ cH
...     | W , (rL , rR)
          with homred-inv stknn-red stknn-noU stknn-noΠ stknn-noN
                          (st-el {c = ⌜Fin⌝ n} refl , nn-El nnh-Fin) rR
...       | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
            with Hom-to-Hom
                   (homAmb→ (subst (λ z → _ ⟶ᵀ* z) eqW rR) (nn-El nnh-Fin))
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
