------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 25 — (B1) CONFLUENCE (Church–Rosser) of the dependent
--                            de Bruijn calculus
--
-- ⚠⚠ THIS MODULE NEEDS THE COMPACTING COLLECTOR.  Check it with
--
--       AGDA_RTS="-A64m -c" ./check.sh DirectedHoTT/Metatheory/Confluence.agda
--
--   (`sweep.sh` greps that phrase from these first 40 lines and uses `-c`.)
--   It crossed the line when `tr-J-IMu` landed (PLAN-INDEXED §10.4): the
--   rule adds one parallel-reduction constructor and `⟹-⁺` grows a row
--   per context, which is where the module's memory goes.
--
-- The gateway metatheorem (HANDOFF §3 Tier B). Confluence of `_⟶_` on `RTm`,
-- by the Takahashi complete-development method (parallel reduction + the
-- triangle lemma), the same technique the repo already uses for the point-free
-- side (`normalizer.Syntax.CCC._⟹_` + diamond), ported to de Bruijn λ.
--
--   * `_⟹_` — parallel reduction (reduce many redexes at once), `⟹-refl`,
--     `⟶→⟹`, `⟹→⟶*` (the two inclusions `⟶ ⊆ ⟹ ⊆ ⟶*`).
--   * `⟹-ren` / `⟹-sub` — parallel reduction is stable under renaming and
--     (pointwise-parallel) substitution; the β cases use `ren-comm` / `sub-comm`
--     (the substitution-commutes lemmas of `NbEPDirDBPi`/`NbEPDirDBSR`).
--   * `_⁺` / `⟹-⁺` — the COMPLETE DEVELOPMENT and the TRIANGLE: every parallel
--     reduct of `t` reduces (in one parallel step) to `t⁺`. Diamond is immediate.
--   * `confluent` — CONFLUENCE of `⟶*`: `t ⟶* u → t ⟶* v → ∃w. u ⟶* w × v ⟶* w`.
--   * `church-rosser` — CONVERTIBLE terms are JOINABLE: `t ≅ u → ∃w. t ⟶* w ×
--     u ⟶* w`. This is what unblocks Π-injectivity of conversion (and hence
--     general subject reduction, dHoTT-24's scoped ceiling) in the next slice.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Confluence where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app; pair; fst; snd; absurd; ordtr
        ; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub
        ; unit; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝; ⌜Mu⌝; subTm-subTm
        ; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃
        ; Ren; extR; renTm; renTm-renTm; renTm-cong
        ; Sub; extS; subTm; renTm-subTm; subTm-renTm; subTm-cong
        ; _ᵣ∘ₛ_; _ₛ∘ᵣ_; _∘ᵣ_
        ; Desc; DCon; dι; dρ; dκ; con; elim; lookupD; sel; fields; ren-fields; ren-sel; sub-fields; sub-sel
        ; ihs
        ; IMu; icon; ielim; ⌜IMu⌝; ICon; IDesc; iι; iρ; iκ; inil; _◂_; ipayTy; ilookupD; _∈ID_; hereID; thereID; iihs; ifields; εwkTm
        ; RTy
        ; ren-ifields; sub-ifields; ren-iihs; sub-iihs; ren-ifieldsⁱ; sub-ifieldsⁱ; isingle; iext )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; pw?; stkC?; stkA?; pwBody; pwShift
        ; pw?-ren; stkC?-ren; stkA?-ren; pwBody-ren
        ; pw?-sub; stkC?-sub; stkA?-sub; pwBody-sub; pw⊥stk; pw⊥stkA
        ; stkC?→stkA? )
open import DirectedHoTT.Spec.Typing
  using ( single; swp; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss
        ; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; tr-J-base; tr-J-Σ; tr-J-Id; tr-taut; hrefl-pw; tr-J-Hom; tr-pw
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ
        ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ
        ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ
        ; tr-J-Unit; tr-J-Mu; tr-J-IMu; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜Mu⌝
        ; _⟶*_; done; step
        ; _≅_; cred; crfl; csym; ctrn
        ; ι-elim; ξ-con; ξ-elimᵐ; ξ-elimᵗ
        ; ι-ielim; ξ-icon; ξ-ielimⁱ; ξ-ielimᵐ; ξ-ielimᵗ; ξ-⌜IMu⌝; El-⌜IMu⌝ )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( sub-comm; sub-comm-ext; ⟶-sub; wk-sub; wk₁-sub; swp-sub; pwShift-sub )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- Multi-step reduction: transitivity + congruences.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ THE CONGRUENCES MOVED TO `Metatheory/RedCong` 2026-09-04, and
--   re-exported here so every existing importer is unaffected.
--
-- ⚠⚠ THE REASON IS MEASURED, NOT AESTHETIC.  This module's interface is
--   8.7 MB — the largest in the development — and 11 `Lib` modules pull
--   it in, so every knot module loads it.  What they use is the ~15
--   structural congruences; the rest is `⟹-⁺` and the confluence proof,
--   which the knot never mentions.  And `--profile=all` says ~70% of a
--   knot module's time is DESERIALIZATION (`Knot/Census`: 3,948ms of
--   5,811ms, against 2ms of TYPING).  ⇒ what the knot must READ is the
--   dominant cost, and this is the one lever that touches it.
------------------------------------------------------------------------

open import DirectedHoTT.Metatheory.RedCong public

------------------------------------------------------------------------
-- Renaming commutes with single substitution, and reduction survives renaming.
------------------------------------------------------------------------

infix 3 _⟹_
data _⟹_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  pvar  : (x : Var Γ) → var x ⟹ var x
  plam  : {t t' : RTm (Γ ∙)} → t ⟹ t' → lam t ⟹ lam t'
  papp  : {t t' u u' : RTm Γ} → t ⟹ t' → u ⟹ u' → app t u ⟹ app t' u'
  pβ    : {t t' : RTm (Γ ∙)} {u u' : RTm Γ} →
          t ⟹ t' → u ⟹ u' → app (lam t) u ⟹ subTm (single u') t'
  ppair : {a a' b b' : RTm Γ} → a ⟹ a' → b ⟹ b' → pair a b ⟹ pair a' b'
  -- ★ stage D: ex falso has no root rule, so it is pure congruence.
  pabsurd : {c c' e e' : RTm Γ} → c ⟹ c' → e ⟹ e' → absurd c e ⟹ absurd c' e'
  -- ★★ ORDER TRANSPORT: congruence plus the five roots.
  pordtr : {a a' t t' u u' p p' q q' : RTm Γ} →
           a ⟹ a' → t ⟹ t' → u ⟹ u' → p ⟹ p' → q ⟹ q' →
           ordtr a t u p q ⟹ ordtr a' t' u' p' q'
  pordtr-z   : {t u p q : RTm Γ} → ordtr nzero t u p q ⟹ unit
  pordtr-szz : {a p p' q : RTm Γ} → p ⟹ p' →
               ordtr (nsuc a) nzero nzero p q ⟹ p'
  pordtr-ssz : {a t p q q' : RTm Γ} → q ⟹ q' →
               ordtr (nsuc a) (nsuc t) nzero p q ⟹ q'
  pordtr-szs : {a a' u u' p p' q : RTm Γ} → a ⟹ a' → u ⟹ u' → p ⟹ p' →
               ordtr (nsuc a) nzero (nsuc u) p q ⟹ absurd (⌜Hom⌝ ⌜Nat⌝ a' u') p'
  pordtr-sss : {a a' t t' u u' p p' q q' : RTm Γ} →
               a ⟹ a' → t ⟹ t' → u ⟹ u' → p ⟹ p' → q ⟹ q' →
               ordtr (nsuc a) (nsuc t) (nsuc u) p q ⟹ ordtr a' t' u' p' q'
  pfst  : {p p' : RTm Γ} → p ⟹ p' → fst p ⟹ fst p'
  psnd  : {p p' : RTm Γ} → p ⟹ p' → snd p ⟹ snd p'
  pβfst : {a a' b b' : RTm Γ} → a ⟹ a' → b ⟹ b' → fst (pair a b) ⟹ a'
  pβsnd : {a a' b b' : RTm Γ} → a ⟹ a' → b ⟹ b' → snd (pair a b) ⟹ b'
  p⌜base⌝ : ⌜base⌝ {Γ} ⟹ ⌜base⌝
  p⌜Π⌝ : {c c' : RTm Γ} {d d' : RTm (Γ ∙)} → c ⟹ c' → d ⟹ d' → ⌜Π⌝ c d ⟹ ⌜Π⌝ c' d'
  p⌜Σ⌝ : {c c' : RTm Γ} {d d' : RTm (Γ ∙)} → c ⟹ c' → d ⟹ d' → ⌜Σ⌝ c d ⟹ ⌜Σ⌝ c' d'
  -- W2 eliminator: congruences for the three new formers, plus the six
  -- root rules (`hrefl`-unfold and the five path-keyed `tr` rules).
  -- Discarding rules (the three Js) carry premises only for what the
  -- RHS mentions — the standard Takahashi shape.
  p⌜Hom⌝ : {c c' a a' b b' : RTm Γ} → c ⟹ c' → a ⟹ a' → b ⟹ b' →
           ⌜Hom⌝ c a b ⟹ ⌜Hom⌝ c' a' b'
  phrefl : {c c' t t' : RTm Γ} → c ⟹ c' → t ⟹ t' → hrefl c t ⟹ hrefl c' t'
  ptr : {d d' : RTm (Γ ∙)} {p p' e e' : RTm Γ} →
        d ⟹ d' → p ⟹ p' → e ⟹ e' → tr d p e ⟹ tr d' p' e'
  ptr-J-base : {c a m : RTm (Γ ∙)} {s e e' : RTm Γ} →
               e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl ⌜base⌝ s) e ⟹ e'
  p⌜Nat⌝  : ⌜Nat⌝ {Γ} ⟹ ⌜Nat⌝
  p⌜Unit⌝ : ⌜Unit⌝ {Γ} ⟹ ⌜Unit⌝
  p⌜Mu⌝   : {Dᵐ : Desc} → ⌜Mu⌝ {Γ} Dᵐ ⟹ ⌜Mu⌝ Dᵐ
  ptr-J-Unit : {c a m : RTm (Γ ∙)} {s e e' : RTm Γ} →
               e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s) e ⟹ e'
  -- ★ INDUCTIVE TYPES: `⌜Mu⌝`'s J rule, parallel form.  `Dᵐ` rather than
  --   `D` throughout — this file already binds `D` for the description in
  --   `elim D ms t`, and a clash there is silent.
  ptr-J-Mu : {Dᵐ : Desc} {c a m : RTm (Γ ∙)} {s e e' : RTm Γ} →
             e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl (⌜Mu⌝ Dᵐ) s) e ⟹ e'
  -- ★ §10.4's obligation in parallel form.  ⚠ the INDEX is not tracked:
  --   the rule discards the path whole, exactly as `ptr-J-Mu` discards
  --   the description.
  ptr-J-IMu : {Dⁱ : IDesc} {Iⁱ : RTy ε} {iˣ : RTm Γ}
              {c a m : RTm (Γ ∙)} {s e e' : RTm Γ} →
              e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ Dⁱ Iⁱ iˣ) s) e ⟹ e'
  ptr-J-Σ : {c a m : RTm (Γ ∙)} {c₁ : RTm Γ} {c₂ : RTm (Γ ∙)} {s e e' : RTm Γ} →
            e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e ⟹ e'
  ptr-J-Id : {c a m : RTm (Γ ∙)} {c₁ a₁ b₁ s e e' : RTm Γ} →
             e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e ⟹ e'
  ptr-taut : {f f' : RTm (Γ ∙)} {e e' : RTm Γ} → f ⟹ f' → e ⟹ e' →
             tr (var vz) (lam f) e ⟹ app (lam f') e'
  -- W2b (SpikeCanon): the three canonicity rules, Boolean-keyed.
  phrefl-pw : {C C' s s' : RTm Γ} → pw? C ≡ true → C ⟹ C' → s ⟹ s' →
              hrefl C s ⟹
              lam (hrefl (pwBody C') (app (renTm vs s') (var vz)))
  -- ★★ key is `stkA?`, mirroring `tr-J-Hom` (SpikeNatJ split).
  ptr-J-Hom : {c a m : RTm (Γ ∙)} {c₁ a₁ b₁ s e e' : RTm Γ} →
              stkA? c₁ ≡ true → e ⟹ e' →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e ⟹ e'
  ptr-pw    : {c c' a a' f f' : RTm (Γ ∙)} {e e' : RTm Γ} →
              pw? c ≡ true → c ⟹ c' → a ⟹ a' → f ⟹ f' → e ⟹ e' →
              tr (⌜Hom⌝ c a (var vz)) (lam f) e ⟹
              lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c'))
                             (app (renTm vs a') (var (vs vz)))
                             (var vz))
                      f'
                      (app (renTm vs e') (var vz)))
  -- directed `ap` (SpikeAp): congruence + the stable-code J root
  -- (premises only for what the RHS mentions — the Takahashi shape).
  pap   : {cB cB' : RTm Γ} {b b' : RTm (Γ ∙)} {p p' : RTm Γ} →
          cB ⟹ cB' → b ⟹ b' → p ⟹ p' → ap cB b p ⟹ ap cB' b' p'
  pap-J : {cB cB' : RTm Γ} {b b' : RTm (Γ ∙)} {c₁ s s' : RTm Γ} →
          stkC? c₁ ≡ true → cB ⟹ cB' → b ⟹ b' → s ⟹ s' →
          ap cB b (hrefl c₁ s) ⟹ hrefl cB' (subTm (single s') b')
  -- the two-former kernel: congruences + the UNKEYED J root.
  p⌜Id⌝  : {c c' a a' b b' : RTm Γ} → c ⟹ c' → a ⟹ a' → b ⟹ b' →
           ⌜Id⌝ c a b ⟹ ⌜Id⌝ c' a' b'
  pidrefl : {c c' t t' : RTm Γ} → c ⟹ c' → t ⟹ t' →
            idrefl c t ⟹ idrefl c' t'
  pjsub  : {d d' : RTm (Γ ∙)} {p p' e e' : RTm Γ} →
           d ⟹ d' → p ⟹ p' → e ⟹ e' → jsub d p e ⟹ jsub d' p' e'
  pjsub-refl : {d : RTm (Γ ∙)} {c s e e' : RTm Γ} →
               e ⟹ e' → jsub d (idrefl c s) e ⟹ e'
  -- ★ WF stage A: Unit and Nat — congruences plus the recursor's two
  -- numeral-keyed firings (developed componentwise, the pβ pattern).
  punit  : unit {Γ} ⟹ unit
  pnzero : nzero {Γ} ⟹ nzero
  pnsuc  : {n n' : RTm Γ} → n ⟹ n' → nsuc n ⟹ nsuc n'
  pnatrec : {z z' : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
            z ⟹ z' → s ⟹ s' → n ⟹ n' →
            natrec z s n ⟹ natrec z' s' n'
  pnatrec-zero : {z z' : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} →
                 z ⟹ z' → s ⟹ s' → natrec z s nzero ⟹ z'
  pnatrec-suc : {z z' : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
                z ⟹ z' → s ⟹ s' → n ⟹ n' →
                natrec z s (nsuc n) ⟹
                subTm (single (natrec z' s' n')) (subTm (extS (single n')) s')
  -- ★ INDUCTIVE TYPES: two congruences plus the ι root, developed
  -- componentwise (the `pβ`/`pnatrec-suc` shape).
  pcon  : {k : ℕ} {p p' : RTm Γ} → p ⟹ p' → con k p ⟹ con k p'
  pelim : {D : Desc} {ms ms' t t' : RTm Γ} →
          ms ⟹ ms' → t ⟹ t' → elim D ms t ⟹ elim D ms' t'
  pι    : {D : Desc} {ms ms' : RTm Γ} {k : ℕ} {p p' : RTm Γ} →
          ms ⟹ ms' → p ⟹ p' →
          elim D ms (con k p) ⟹ fields D ms' (lookupD D k) (sel k ms') p'

  -- ★★★ their INDEXED twins.  ⚠ `pιi` is what showed that `iihs`/`ifields`
  --   must NOT carry the index TYPE: its conclusion would have mentioned an
  --   `I` that `ielim D i ms (icon k p)` cannot determine.
  p⌜IMu⌝ : {D : IDesc} {I : RTy ε} {i i' : RTm Γ} →
           i ⟹ i' → ⌜IMu⌝ D I i ⟹ ⌜IMu⌝ D I i'
  picon  : {k : ℕ} {p p' : RTm Γ} → p ⟹ p' → icon k p ⟹ icon k p'
  pielim : {D : IDesc} {i i' ms ms' t t' : RTm Γ} →
           i ⟹ i' → ms ⟹ ms' → t ⟹ t' → ielim D i ms t ⟹ ielim D i' ms' t'
  pιi    : {D : IDesc} {i i' ms ms' : RTm Γ} {k : ℕ} {p p' : RTm Γ} →
           i ⟹ i' → ms ⟹ ms' → p ⟹ p' →
           ielim D i ms (icon k p) ⟹
             ifields D i' ms' (isingle i') (ilookupD D k) (sel k ms') p'

-- ★ `sel` and `fields` are METALEVEL, so their ⟹-congruences are lemmas
--   rather than constructors — `pι`'s right-hand side mentions both, and
--   every use of `pι` in the triangle needs them.
p-sel : (k : ℕ) {ms ms' : RTm Γ} → ms ⟹ ms' → sel k ms ⟹ sel k ms'
p-sel zero    pms = pfst pms
p-sel (suc k) pms = p-sel k (psnd pms)

p-ihs : {D : Desc} {ms ms' : RTm Γ} (C : DCon) {p p' : RTm Γ} →
        ms ⟹ ms' → p ⟹ p' → ihs D ms C p ⟹ ihs D ms' C p'
p-ihs dι       pms pp = punit
p-ihs (dρ C)   pms pp =
  ppair (pelim pms (pfst pp)) (p-ihs C pms (psnd pp))
p-ihs (dκ A C) pms pp = p-ihs C pms (psnd pp)

p-fields : {D : Desc} {ms ms' : RTm Γ} (C : DCon) {m m' p p' : RTm Γ} →
           ms ⟹ ms' → m ⟹ m' → p ⟹ p' →
           fields D ms C m p ⟹ fields D ms' C m' p'
p-fields C pms pm pp = papp (papp pm pp) (p-ihs C pms pp)

⟹-refl : (t : RTm Γ) → t ⟹ t
⟹-refl ⌜Nat⌝      = p⌜Nat⌝
⟹-refl ⌜Unit⌝     = p⌜Unit⌝
⟹-refl (⌜Mu⌝ Dᵐ)  = p⌜Mu⌝
⟹-refl unit       = punit
⟹-refl nzero      = pnzero
⟹-refl (nsuc n)   = pnsuc (⟹-refl n)
⟹-refl (con k p)  = pcon (⟹-refl p)
⟹-refl (elim D ms t) = pelim (⟹-refl ms) (⟹-refl t)
⟹-refl (icon k p)  = picon (⟹-refl p)
⟹-refl (ielim D i ms t) = pielim (⟹-refl i) (⟹-refl ms) (⟹-refl t)
⟹-refl (⌜IMu⌝ D I i) = p⌜IMu⌝ (⟹-refl i)
⟹-refl (natrec z s n) = pnatrec (⟹-refl z) (⟹-refl s) (⟹-refl n)
⟹-refl (var x)    = pvar x
⟹-refl (lam t)    = plam (⟹-refl t)
⟹-refl (app t u)  = papp (⟹-refl t) (⟹-refl u)
⟹-refl (pair a b) = ppair (⟹-refl a) (⟹-refl b)
⟹-refl (absurd c e) = pabsurd (⟹-refl c) (⟹-refl e)
⟹-refl (ordtr a t u p q) =
  pordtr (⟹-refl a) (⟹-refl t) (⟹-refl u) (⟹-refl p) (⟹-refl q)
⟹-refl (fst p)    = pfst (⟹-refl p)
⟹-refl (snd p)    = psnd (⟹-refl p)
⟹-refl ⌜base⌝     = p⌜base⌝
⟹-refl (⌜Π⌝ c d)  = p⌜Π⌝ (⟹-refl c) (⟹-refl d)
⟹-refl (⌜Σ⌝ c d)  = p⌜Σ⌝ (⟹-refl c) (⟹-refl d)
⟹-refl (⌜Hom⌝ c a b) = p⌜Hom⌝ (⟹-refl c) (⟹-refl a) (⟹-refl b)
⟹-refl (hrefl c t)   = phrefl (⟹-refl c) (⟹-refl t)
⟹-refl (ap c b p)  = pap (⟹-refl c) (⟹-refl b) (⟹-refl p)
⟹-refl (⌜Id⌝ c a b) = p⌜Id⌝ (⟹-refl c) (⟹-refl a) (⟹-refl b)
⟹-refl (idrefl c t) = pidrefl (⟹-refl c) (⟹-refl t)
⟹-refl (jsub d p e) = pjsub (⟹-refl d) (⟹-refl p) (⟹-refl e)
⟹-refl (tr d p e)    = ptr (⟹-refl d) (⟹-refl p) (⟹-refl e)

-- W2b: the keys and the body function move along PARALLEL steps too —
-- what the triangle's helper rows consume.
pw?-⟹ : {C C' : RTm Γ} → C ⟹ C' → pw? C ≡ true → pw? C' ≡ true
pw?-⟹ (pvar _) ()
pw?-⟹ (plam _) ()
pw?-⟹ (papp _ _) ()
pw?-⟹ (pβ _ _) ()
pw?-⟹ (ppair _ _) ()
pw?-⟹ (pabsurd _ _) ()
pw?-⟹ (pfst _) ()
pw?-⟹ (psnd _) ()
pw?-⟹ (pβfst _ _) ()
pw?-⟹ (pβsnd _ _) ()
pw?-⟹ p⌜base⌝ ()
pw?-⟹ (p⌜Π⌝ _ _) h = refl
pw?-⟹ (p⌜Σ⌝ _ _) ()
pw?-⟹ (p⌜Hom⌝ pc _ _) h = pw?-⟹ pc h
pw?-⟹ (phrefl _ _) ()
pw?-⟹ (phrefl-pw _ _ _) ()
pw?-⟹ (ptr _ _ _) ()
pw?-⟹ (ptr-J-base _) ()
pw?-⟹ (p⌜Nat⌝) ()
pw?-⟹ (p⌜Unit⌝) ()
pw?-⟹ (p⌜Mu⌝) ()
pw?-⟹ (ptr-J-Unit _) ()
pw?-⟹ (ptr-J-IMu _) ()
pw?-⟹ (ptr-J-Mu _) ()
pw?-⟹ (ptr-J-Σ _) ()
pw?-⟹ (ptr-J-Hom _ _) ()
pw?-⟹ (pap _ _ _) ()
pw?-⟹ (pap-J _ _ _ _) ()
pw?-⟹ (p⌜Id⌝ _ _ _) ()
pw?-⟹ (pidrefl _ _) ()
pw?-⟹ (pjsub _ _ _) ()
pw?-⟹ (pjsub-refl _) ()
pw?-⟹ (ptr-J-Id _) ()
pw?-⟹ (ptr-taut _ _) ()
pw?-⟹ (ptr-pw _ _ _ _ _) ()
pw?-⟹ (punit) ()
pw?-⟹ (pnzero) ()
pw?-⟹ (pnsuc _) ()
pw?-⟹ (pnatrec _ _ _) ()
pw?-⟹ (pnatrec-zero _ _) ()
pw?-⟹ (pnatrec-suc _ _ _) ()

-- ★ the `stkA?` peer for parallel reduction (SpikeNatJ split).
stkA?-⟹ : {C C' : RTm Γ} → C ⟹ C' → stkA? C ≡ true → stkA? C' ≡ true
stkA?-⟹ (pvar _) ()
stkA?-⟹ (plam _) ()
stkA?-⟹ (papp _ _) ()
stkA?-⟹ (pβ _ _) ()
stkA?-⟹ (ppair _ _) ()
stkA?-⟹ (pabsurd _ _) ()
stkA?-⟹ (pfst _) ()
stkA?-⟹ (psnd _) ()
stkA?-⟹ (pβfst _ _) ()
stkA?-⟹ (pβsnd _ _) ()
stkA?-⟹ p⌜base⌝ h = refl
stkA?-⟹ (p⌜Π⌝ _ _) ()
stkA?-⟹ (p⌜Σ⌝ _ _) h = refl
stkA?-⟹ (p⌜Hom⌝ pc _ _) h = stkA?-⟹ pc h
stkA?-⟹ (phrefl _ _) ()
stkA?-⟹ (phrefl-pw _ _ _) ()
stkA?-⟹ (ptr _ _ _) ()
stkA?-⟹ (ptr-J-base _) ()
stkA?-⟹ (p⌜Nat⌝) h = refl
stkA?-⟹ (p⌜Unit⌝) h = refl
stkA?-⟹ (p⌜Mu⌝) h = refl
stkA?-⟹ (ptr-J-Unit _) ()
stkA?-⟹ (p⌜IMu⌝ _) h = refl
stkA?-⟹ (ptr-J-IMu _) ()
stkA?-⟹ (ptr-J-Mu _) ()
stkA?-⟹ (ptr-J-Σ _) ()
stkA?-⟹ (ptr-J-Hom _ _) ()
stkA?-⟹ (pap _ _ _) ()
stkA?-⟹ (pap-J _ _ _ _) ()
stkA?-⟹ (p⌜Id⌝ _ _ _) h = refl
stkA?-⟹ (pidrefl _ _) ()
stkA?-⟹ (pjsub _ _ _) ()
stkA?-⟹ (pjsub-refl _) ()
stkA?-⟹ (ptr-J-Id _) ()
stkA?-⟹ (ptr-taut _ _) ()
stkA?-⟹ (ptr-pw _ _ _ _ _) ()
stkA?-⟹ (punit) ()
stkA?-⟹ (pnzero) ()
stkA?-⟹ (pnsuc _) ()
stkA?-⟹ (pnatrec _ _ _) ()
stkA?-⟹ (pnatrec-zero _ _) ()
stkA?-⟹ (pnatrec-suc _ _ _) ()

stkC?-⟹ : {C C' : RTm Γ} → C ⟹ C' → stkC? C ≡ true → stkC? C' ≡ true
stkC?-⟹ (pvar _) ()
stkC?-⟹ (plam _) ()
stkC?-⟹ (papp _ _) ()
stkC?-⟹ (pβ _ _) ()
stkC?-⟹ (ppair _ _) ()
stkC?-⟹ (pabsurd _ _) ()
stkC?-⟹ (pfst _) ()
stkC?-⟹ (psnd _) ()
stkC?-⟹ (pβfst _ _) ()
stkC?-⟹ (pβsnd _ _) ()
stkC?-⟹ p⌜base⌝ h = refl
stkC?-⟹ (p⌜Π⌝ _ _) ()
stkC?-⟹ (p⌜Σ⌝ _ _) h = refl
stkC?-⟹ (p⌜Hom⌝ pc _ _) h = stkA?-⟹ pc h
stkC?-⟹ (phrefl _ _) ()
stkC?-⟹ (phrefl-pw _ _ _) ()
stkC?-⟹ (ptr _ _ _) ()
stkC?-⟹ (ptr-J-base _) ()
stkC?-⟹ (p⌜Nat⌝) ()
stkC?-⟹ (p⌜Unit⌝) h = refl
stkC?-⟹ (p⌜Mu⌝) h = refl
stkC?-⟹ (ptr-J-Unit _) ()
stkC?-⟹ (p⌜IMu⌝ _) h = refl
stkC?-⟹ (ptr-J-Mu _) ()
stkC?-⟹ (ptr-J-Σ _) ()
stkC?-⟹ (ptr-J-Hom _ _) ()
stkC?-⟹ (pap _ _ _) ()
stkC?-⟹ (pap-J _ _ _ _) ()
stkC?-⟹ (p⌜Id⌝ _ _ _) h = refl
stkC?-⟹ (pidrefl _ _) ()
stkC?-⟹ (pjsub _ _ _) ()
stkC?-⟹ (pjsub-refl _) ()
stkC?-⟹ (ptr-J-Id _) ()
stkC?-⟹ (ptr-taut _ _) ()
stkC?-⟹ (ptr-pw _ _ _ _ _) ()
stkC?-⟹ (punit) ()
stkC?-⟹ (pnzero) ()
stkC?-⟹ (pnsuc _) ()
stkC?-⟹ (pnatrec _ _ _) ()
stkC?-⟹ (pnatrec-zero _ _) ()
stkC?-⟹ (pnatrec-suc _ _ _) ()



⟶→⟹ : {t u : RTm Γ} → t ⟶ u → t ⟹ u
⟶→⟹ (tr-J-Unit _ _ _ _ e) = ptr-J-Unit (⟹-refl e)
⟶→⟹ (tr-J-Mu _ _ _ _ e)   = ptr-J-Mu (⟹-refl e)
⟶→⟹ (tr-J-IMu _ _ _ _ e)  = ptr-J-IMu (⟹-refl e)
⟶→⟹ (natrec-zero z s)  = pnatrec-zero (⟹-refl z) (⟹-refl s)
⟶→⟹ (natrec-suc z s n) = pnatrec-suc (⟹-refl z) (⟹-refl s) (⟹-refl n)
⟶→⟹ (ξ-nsuc r)    = pnsuc (⟶→⟹ r)
⟶→⟹ (ξ-natrecᶻ r) = pnatrec (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-natrecˢ r) = pnatrec (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-natrecⁿ r) = pnatrec (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ι-elim D ms k p) = pι (⟹-refl ms) (⟹-refl p)
⟶→⟹ (ξ-con r)   = pcon   (⟶→⟹ r)
⟶→⟹ (ξ-elimᵐ r) = pelim  (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-elimᵗ r) = pelim  (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ι-ielim D i ms k p) = pιi (⟹-refl i) (⟹-refl ms) (⟹-refl p)
⟶→⟹ (ξ-icon r)    = picon  (⟶→⟹ r)
⟶→⟹ (ξ-ielimⁱ r)  = pielim (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-ielimᵐ r)  = pielim (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-ielimᵗ r)  = pielim (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-⌜IMu⌝ r)   = p⌜IMu⌝ (⟶→⟹ r)
⟶→⟹ (β t u)     = pβ (⟹-refl t) (⟹-refl u)
⟶→⟹ (βfst a b)  = pβfst (⟹-refl a) (⟹-refl b)
⟶→⟹ (βsnd a b)  = pβsnd (⟹-refl a) (⟹-refl b)
⟶→⟹ (ξ-lam r)   = plam (⟶→⟹ r)
⟶→⟹ (ξ-appˡ r)  = papp (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-appʳ r)  = papp (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-pairˡ r) = ppair (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-pairʳ r) = ppair (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ordtr-z t u p q)     = pordtr-z
⟶→⟹ (ordtr-szz a p q)     = pordtr-szz (⟹-refl _)
⟶→⟹ (ordtr-ssz a t p q)   = pordtr-ssz (⟹-refl _)
⟶→⟹ (ordtr-szs a u p q)   = pordtr-szs (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ordtr-sss a t u p q) =
  pordtr-sss (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-ordtrᵃ r) = pordtr (⟶→⟹ r) (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-ordtrᵗ r) = pordtr (⟹-refl _) (⟶→⟹ r) (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-ordtrᵘ r) = pordtr (⟹-refl _) (⟹-refl _) (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-ordtrᵖ r) = pordtr (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-ordtrq r) = pordtr (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-absurdᶜ r) = pabsurd (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-absurdᵉ r) = pabsurd (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-fst r)   = pfst (⟶→⟹ r)
⟶→⟹ (ξ-snd r)   = psnd (⟶→⟹ r)
⟶→⟹ (ξ-⌜Π⌝ˡ r) = p⌜Π⌝ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-⌜Π⌝ʳ r) = p⌜Π⌝ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-⌜Σ⌝ˡ r) = p⌜Σ⌝ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-⌜Σ⌝ʳ r) = p⌜Σ⌝ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (tr-J-base c a m s e)    = ptr-J-base (⟹-refl e)
⟶→⟹ (tr-J-Σ c a m c₁ c₂ s e) = ptr-J-Σ (⟹-refl e)
⟶→⟹ (tr-J-Id c a m c₁ a₁ b₁ s e) = ptr-J-Id (⟹-refl e)
⟶→⟹ (tr-taut f e)        = ptr-taut (⟹-refl f) (⟹-refl e)
⟶→⟹ (hrefl-pw C t key) = phrefl-pw key (⟹-refl C) (⟹-refl t)
⟶→⟹ (tr-J-Hom c a m c₁ a₁ b₁ t e key) = ptr-J-Hom key (⟹-refl e)
⟶→⟹ (tr-pw c a f e key) =
  ptr-pw key (⟹-refl c) (⟹-refl a) (⟹-refl f) (⟹-refl e)
⟶→⟹ (ξ-⌜Hom⌝ᶜ r) = p⌜Hom⌝ (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-⌜Hom⌝ˡ r) = p⌜Hom⌝ (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-⌜Hom⌝ʳ r) = p⌜Hom⌝ (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-hreflᶜ r) = phrefl (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-hreflᵃ r) = phrefl (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-trᵈ r)    = ptr (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-trᵖ r)    = ptr (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-trᵉ r)    = ptr (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ap-J cB b c₁ s key) =
  pap-J key (⟹-refl cB) (⟹-refl b) (⟹-refl s)
⟶→⟹ (ξ-apᶜ r) = pap (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-apᵇ r) = pap (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-apᵖ r) = pap (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (jsub-refl d c s e) = pjsub-refl (⟹-refl e)
⟶→⟹ (ξ-⌜Id⌝ᶜ r) = p⌜Id⌝ (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-⌜Id⌝ˡ r) = p⌜Id⌝ (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-⌜Id⌝ʳ r) = p⌜Id⌝ (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-idreflᶜ r) = pidrefl (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-idreflᵃ r) = pidrefl (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-jsubᵈ r) = pjsub (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-jsubᵖ r) = pjsub (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-jsubᵉ r) = pjsub (⟹-refl _) (⟹-refl _) (⟶→⟹ r)

⟹→⟶* : {t u : RTm Γ} → t ⟹ u → t ⟶* u
⟹→⟶* p⌜Nat⌝     = done
⟹→⟶* p⌜Unit⌝    = done
⟹→⟶* p⌜Mu⌝      = done
⟹→⟶* punit      = done
⟹→⟶* pnzero     = done
⟹→⟶* (pnsuc p)  = ⟶*-nsuc (⟹→⟶* p)
⟹→⟶* (pcon p)   = ⟶*-con (⟹→⟶* p)
⟹→⟶* (pelim pms pt) =
  ⟶*-trans (⟶*-elimᵐ (⟹→⟶* pms)) (⟶*-elimᵗ (⟹→⟶* pt))
⟹→⟶* (picon p)  = ⟶*-icon (⟹→⟶* p)
⟹→⟶* (p⌜IMu⌝ p) = ⟶*-⌜IMu⌝ (⟹→⟶* p)
⟹→⟶* (pielim pi pms pt) =
  ⟶*-trans (⟶*-ielimⁱ (⟹→⟶* pi))
           (⟶*-trans (⟶*-ielimᵐ (⟹→⟶* pms)) (⟶*-ielimᵗ (⟹→⟶* pt)))
⟹→⟶* (pι {D = D} {ms = ms} {k = k} {p = p} pms pp) =
  step (ι-elim D ms k p)
       (⟶*-fields D (lookupD D k) (⟹→⟶* pms)
                  (⟶*-sel k (⟹→⟶* pms)) (⟹→⟶* pp))
⟹→⟶* (pιi {D = D} {i = i} {ms = ms} {k = k} {p = p} pi pms pp) =
  step (ι-ielim D i ms k p)
       (⟶*-ifields D (ilookupD D k) (⟹→⟶* pi)
                   (λ { vz → ⟹→⟶* pi }) (⟹→⟶* pms)
                   (⟶*-sel k (⟹→⟶* pms)) (⟹→⟶* pp))
⟹→⟶* (pnatrec pz ps pn) =
  ⟶*-trans (⟶*-natrecᶻ (⟹→⟶* pz))
           (⟶*-trans (⟶*-natrecˢ (⟹→⟶* ps)) (⟶*-natrecⁿ (⟹→⟶* pn)))
⟹→⟶* (pnatrec-zero {z = z} {s = s} pz ps) =
  step (natrec-zero z s) (⟹→⟶* pz)
⟹→⟶* (pnatrec-suc {z = z} {z'} {s = s} {s'} {n = n} {n'} pz ps pn) =
  step (natrec-suc z s n)
    (⟶*-trans
      (⟶*-sub (single (natrec z s n))
        (⟶*-trans (⟶*-sub (extS (single n)) (⟹→⟶* ps))
                  (subTm-monoˢ (extS-mono (single-mono (⟹→⟶* pn))) s')))
      (subTm-monoˢ (single-mono
          (⟶*-trans (⟶*-natrecᶻ (⟹→⟶* pz))
            (⟶*-trans (⟶*-natrecˢ (⟹→⟶* ps)) (⟶*-natrecⁿ (⟹→⟶* pn)))))
        (subTm (extS (single n')) s')))
⟹→⟶* (pvar x)  = done
⟹→⟶* (plam p)  = ⟶*-lam (⟹→⟶* p)
⟹→⟶* (papp p q) =
  ⟶*-trans (⟶*-appˡ (⟹→⟶* p)) (⟶*-appʳ (⟹→⟶* q))
⟹→⟶* (pβ {t = t} {t' = t'} {u = u} {u' = u'} p q) =
  step (β t u)
       (⟶*-trans (⟶*-sub (single u) (⟹→⟶* p))
                 (subTm-monoˢ (single-mono (⟹→⟶* q)) t'))
⟹→⟶* (ppair p q) =
  ⟶*-trans (⟶*-pairˡ (⟹→⟶* p)) (⟶*-pairʳ (⟹→⟶* q))
⟹→⟶* (pordtr pa pt pu pp pq) =
  ⟶*-trans (⟶*-ordtrᵃ (⟹→⟶* pa))
   (⟶*-trans (⟶*-ordtrᵗ (⟹→⟶* pt))
    (⟶*-trans (⟶*-ordtrᵘ (⟹→⟶* pu))
     (⟶*-trans (⟶*-ordtrᵖ (⟹→⟶* pp)) (⟶*-ordtrq (⟹→⟶* pq)))))
⟹→⟶* pordtr-z = step (ordtr-z _ _ _ _) done
⟹→⟶* (pordtr-szz pp) = step (ordtr-szz _ _ _) (⟹→⟶* pp)
⟹→⟶* (pordtr-ssz pq) = step (ordtr-ssz _ _ _ _) (⟹→⟶* pq)
⟹→⟶* (pordtr-szs pa pu pp) =
  step (ordtr-szs _ _ _ _)
    (⟶*-trans (⟶*-absurdᶜ (⟶*-⌜Hom⌝ˡ (⟹→⟶* pa)))
     (⟶*-trans (⟶*-absurdᶜ (⟶*-⌜Hom⌝ʳ (⟹→⟶* pu))) (⟶*-absurdᵉ (⟹→⟶* pp))))
⟹→⟶* (pordtr-sss pa pt pu pp pq) =
  step (ordtr-sss _ _ _ _ _)
    (⟶*-trans (⟶*-ordtrᵃ (⟹→⟶* pa))
     (⟶*-trans (⟶*-ordtrᵗ (⟹→⟶* pt))
      (⟶*-trans (⟶*-ordtrᵘ (⟹→⟶* pu))
       (⟶*-trans (⟶*-ordtrᵖ (⟹→⟶* pp)) (⟶*-ordtrq (⟹→⟶* pq))))))
⟹→⟶* (pabsurd pc pe) =
  ⟶*-trans (⟶*-absurdᶜ (⟹→⟶* pc)) (⟶*-absurdᵉ (⟹→⟶* pe))
⟹→⟶* (pfst p) = ⟶*-fst (⟹→⟶* p)
⟹→⟶* (psnd p) = ⟶*-snd (⟹→⟶* p)
⟹→⟶* (pβfst {a = a} {b = b} p q) = step (βfst a b) (⟹→⟶* p)
⟹→⟶* (pβsnd {a = a} {b = b} p q) = step (βsnd a b) (⟹→⟶* q)
⟹→⟶* p⌜base⌝ = done
⟹→⟶* (p⌜Π⌝ p q) =
  ⟶*-trans (⟶*-⌜Π⌝ˡ (⟹→⟶* p)) (⟶*-⌜Π⌝ʳ (⟹→⟶* q))
⟹→⟶* (p⌜Σ⌝ p q) =
  ⟶*-trans (⟶*-⌜Σ⌝ˡ (⟹→⟶* p)) (⟶*-⌜Σ⌝ʳ (⟹→⟶* q))
⟹→⟶* (p⌜Hom⌝ p q r) =
  ⟶*-trans (⟶*-⌜Hom⌝ᶜ (⟹→⟶* p))
           (⟶*-trans (⟶*-⌜Hom⌝ˡ (⟹→⟶* q)) (⟶*-⌜Hom⌝ʳ (⟹→⟶* r)))
⟹→⟶* (phrefl p q) =
  ⟶*-trans (⟶*-hreflᶜ (⟹→⟶* p)) (⟶*-hreflᵃ (⟹→⟶* q))
⟹→⟶* (ptr p q r) =
  ⟶*-trans (⟶*-trᵈ (⟹→⟶* p))
           (⟶*-trans (⟶*-trᵖ (⟹→⟶* q)) (⟶*-trᵉ (⟹→⟶* r)))
⟹→⟶* (ptr-J-Unit {c = c} {a} {m} {s} {e} p) =
  step (tr-J-Unit c a m s e) (⟹→⟶* p)
⟹→⟶* (ptr-J-Mu {c = c} {a} {m} {s} {e} p) =
  step (tr-J-Mu c a m s e) (⟹→⟶* p)
⟹→⟶* (ptr-J-IMu {c = c} {a} {m} {s} {e} p) =
  step (tr-J-IMu c a m s e) (⟹→⟶* p)
⟹→⟶* (ptr-J-base {c = c} {a} {m} {s} {e} p) =
  step (tr-J-base c a m s e) (⟹→⟶* p)
⟹→⟶* (ptr-J-Σ {c = c} {a} {m} {c₁} {c₂} {s} {e} p) =
  step (tr-J-Σ c a m c₁ c₂ s e) (⟹→⟶* p)
⟹→⟶* (ptr-J-Id {c = c} {a} {m} {c₁} {a₁} {b₁} {s} {e} p) =
  step (tr-J-Id c a m c₁ a₁ b₁ s e) (⟹→⟶* p)
⟹→⟶* (ptr-taut {f = f} {f'} {e} {e'} p q) =
  step (tr-taut f e)
       (⟶*-trans (⟶*-appˡ (⟶*-lam (⟹→⟶* p))) (⟶*-appʳ (⟹→⟶* q)))
⟹→⟶* (phrefl-pw {C = C} {C'} {s = t} {t'} key pC pt) =
  step (hrefl-pw C t key)
       (⟶*-lam
         (⟶*-trans (⟶*-hreflᶜ (pwBody-red* key (⟹→⟶* pC)))
                   (⟶*-hreflᵃ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pt))))))
⟹→⟶* (ptr-J-Hom {c = c} {a} {m} {c₁} {a₁} {b₁} {s = t} {e} key pe) =
  step (tr-J-Hom c a m c₁ a₁ b₁ t e key) (⟹→⟶* pe)
⟹→⟶* (ptr-pw {c = c} {c'} {a} {a'} {f} {f'} {e} {e'} key pc pa pf pe) =
  step (tr-pw c a f e key)
       (⟶*-lam
         (⟶*-trans
           (⟶*-trᵈ
             (⟶*-trans
               (⟶*-⌜Hom⌝ᶜ (⟶*-ren pwShift (pwBody-red* key (⟹→⟶* pc))))
               (⟶*-⌜Hom⌝ˡ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pa))))))
           (⟶*-trans (⟶*-trᵖ (⟹→⟶* pf))
                     (⟶*-trᵉ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pe)))))))
⟹→⟶* (pap p q r) =
  ⟶*-trans (⟶*-apᶜ (⟹→⟶* p))
           (⟶*-trans (⟶*-apᵇ (⟹→⟶* q)) (⟶*-apᵖ (⟹→⟶* r)))
⟹→⟶* (p⌜Id⌝ p q r) =
  ⟶*-trans (⟶*-⌜Id⌝ᶜ (⟹→⟶* p))
           (⟶*-trans (⟶*-⌜Id⌝ˡ (⟹→⟶* q)) (⟶*-⌜Id⌝ʳ (⟹→⟶* r)))
⟹→⟶* (pidrefl p q) =
  ⟶*-trans (⟶*-idreflᶜ (⟹→⟶* p)) (⟶*-idreflᵃ (⟹→⟶* q))
⟹→⟶* (pjsub p q r) =
  ⟶*-trans (⟶*-jsubᵈ (⟹→⟶* p))
           (⟶*-trans (⟶*-jsubᵖ (⟹→⟶* q)) (⟶*-jsubᵉ (⟹→⟶* r)))
⟹→⟶* (pjsub-refl {d = d} {c} {s} {e} p) =
  step (jsub-refl d c s e) (⟹→⟶* p)
⟹→⟶* (pap-J {cB = cB} {cB'} {b} {b'} {c₁} {s = t} {s' = t'} key p q r) =
  step (ap-J cB b c₁ t key)
       (⟶*-trans (⟶*-hreflᶜ (⟹→⟶* p))
                 (⟶*-hreflᵃ
                   (⟶*-trans (⟶*-sub (single t) (⟹→⟶* q))
                             (subTm-monoˢ (single-mono (⟹→⟶* r)) b'))))

------------------------------------------------------------------------
-- Parallel reduction is stable under renaming and substitution.
------------------------------------------------------------------------

⟹-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ⟹ u → renTm ρ t ⟹ renTm ρ u
⟹-ren ρ (pvar x)  = pvar (ρ x)
⟹-ren ρ (plam p)  = plam (⟹-ren (extR ρ) p)
⟹-ren ρ (papp p q) = papp (⟹-ren ρ p) (⟹-ren ρ q)
⟹-ren ρ (pβ {t = t} {t' = t'} {u = u} {u' = u'} p q) =
  subst (λ z → renTm ρ (app (lam t) u) ⟹ z)
        (sym (ren-comm ρ t' u'))
        (pβ (⟹-ren (extR ρ) p) (⟹-ren ρ q))
⟹-ren ρ p⌜Nat⌝     = p⌜Nat⌝
⟹-ren ρ p⌜Unit⌝    = p⌜Unit⌝
⟹-ren ρ p⌜Mu⌝      = p⌜Mu⌝
⟹-ren ρ (ptr-J-Unit p) = ptr-J-Unit (⟹-ren ρ p)
⟹-ren ρ (ptr-J-Mu p)   = ptr-J-Mu (⟹-ren ρ p)
⟹-ren ρ (ptr-J-IMu p)  = ptr-J-IMu (⟹-ren ρ p)
⟹-ren ρ punit      = punit
⟹-ren ρ pnzero     = pnzero
⟹-ren ρ (pnsuc p)  = pnsuc (⟹-ren ρ p)
⟹-ren ρ (pcon p)   = pcon (⟹-ren ρ p)
⟹-ren ρ (pelim pms pt) = pelim (⟹-ren ρ pms) (⟹-ren ρ pt)
⟹-ren ρ (picon p)  = picon  (⟹-ren ρ p)
⟹-ren ρ (p⌜IMu⌝ p) = p⌜IMu⌝ (⟹-ren ρ p)
⟹-ren ρ (pielim pi pms pt) = pielim (⟹-ren ρ pi) (⟹-ren ρ pms) (⟹-ren ρ pt)
⟹-ren ρ (pιi {D = D} {i = i} {i'} {ms = ms} {ms'} {k = k} {p = p} {p'} pi pms pp) =
  subst (ielim D (renTm ρ i) (renTm ρ ms) (icon k (renTm ρ p)) ⟹_)
        (sym (trans (ren-ifieldsⁱ ρ D i' ms' (ilookupD D k) (sel k ms') p')
                    (cong (λ w → ifields D (renTm ρ i') (renTm ρ ms')
                                          (isingle (renTm ρ i'))
                                          (ilookupD D k) w (renTm ρ p'))
                          (ren-sel ρ k ms'))))
        (pιi (⟹-ren ρ pi) (⟹-ren ρ pms) (⟹-ren ρ pp))
⟹-ren ρ (pι {D = D} {ms = ms} {ms'} {k = k} {p = p} {p'} pms pp) =
  subst (elim D (renTm ρ ms) (con k (renTm ρ p)) ⟹_)
        (sym (trans (ren-fields ρ D ms' (lookupD D k) (sel k ms') p')
                    (cong (λ w → fields D (renTm ρ ms') (lookupD D k) w (renTm ρ p'))
                          (ren-sel ρ k ms'))))
        (pι (⟹-ren ρ pms) (⟹-ren ρ pp))
⟹-ren ρ (pnatrec pz ps pn) =
  pnatrec (⟹-ren ρ pz) (⟹-ren (extR (extR ρ)) ps) (⟹-ren ρ pn)
⟹-ren ρ (pnatrec-zero pz ps) =
  pnatrec-zero (⟹-ren ρ pz) (⟹-ren (extR (extR ρ)) ps)
⟹-ren ρ (pnatrec-suc {z = z} {z'} {s = s} {s'} {n = n} {n'} pz ps pn) =
  subst (λ w → natrec (renTm ρ z) (renTm (extR (extR ρ)) s)
                      (nsuc (renTm ρ n)) ⟹ w)
        (sym (trans (ren-comm ρ (subTm (extS (single n')) s') (natrec z' s' n'))
                    (cong (subTm (single (natrec (renTm ρ z')
                                                 (renTm (extR (extR ρ)) s')
                                                 (renTm ρ n'))))
                          (ren-comm-ext ρ s' n'))))
        (pnatrec-suc (⟹-ren ρ pz) (⟹-ren (extR (extR ρ)) ps) (⟹-ren ρ pn))
⟹-ren ρ (ppair p q) = ppair (⟹-ren ρ p) (⟹-ren ρ q)
⟹-ren ρ (pordtr pa pt pu pp pq) =
  pordtr (⟹-ren ρ pa) (⟹-ren ρ pt) (⟹-ren ρ pu) (⟹-ren ρ pp) (⟹-ren ρ pq)
⟹-ren ρ pordtr-z = pordtr-z
⟹-ren ρ (pordtr-szz pp) = pordtr-szz (⟹-ren ρ pp)
⟹-ren ρ (pordtr-ssz pq) = pordtr-ssz (⟹-ren ρ pq)
⟹-ren ρ (pordtr-szs pa pu pp) = pordtr-szs (⟹-ren ρ pa) (⟹-ren ρ pu) (⟹-ren ρ pp)
⟹-ren ρ (pordtr-sss pa pt pu pp pq) =
  pordtr-sss (⟹-ren ρ pa) (⟹-ren ρ pt) (⟹-ren ρ pu) (⟹-ren ρ pp) (⟹-ren ρ pq)
⟹-ren ρ (pabsurd pc pe) = pabsurd (⟹-ren ρ pc) (⟹-ren ρ pe)
⟹-ren ρ (pfst p)    = pfst (⟹-ren ρ p)
⟹-ren ρ (psnd p)    = psnd (⟹-ren ρ p)
⟹-ren ρ (pβfst p q) = pβfst (⟹-ren ρ p) (⟹-ren ρ q)
⟹-ren ρ (pβsnd p q) = pβsnd (⟹-ren ρ p) (⟹-ren ρ q)
⟹-ren ρ p⌜base⌝     = p⌜base⌝
⟹-ren ρ (p⌜Π⌝ p q)  = p⌜Π⌝ (⟹-ren ρ p) (⟹-ren (extR ρ) q)
⟹-ren ρ (p⌜Σ⌝ p q)  = p⌜Σ⌝ (⟹-ren ρ p) (⟹-ren (extR ρ) q)
⟹-ren ρ (p⌜Hom⌝ p q r) = p⌜Hom⌝ (⟹-ren ρ p) (⟹-ren ρ q) (⟹-ren ρ r)
⟹-ren ρ (phrefl p q)   = phrefl (⟹-ren ρ p) (⟹-ren ρ q)
⟹-ren ρ (ptr p q r) = ptr (⟹-ren (extR ρ) p) (⟹-ren ρ q) (⟹-ren ρ r)
⟹-ren ρ (ptr-J-base p) = ptr-J-base (⟹-ren ρ p)
⟹-ren ρ (ptr-J-Σ p)    = ptr-J-Σ (⟹-ren ρ p)
⟹-ren ρ (ptr-J-Id p)   = ptr-J-Id (⟹-ren ρ p)
⟹-ren ρ (ptr-taut p q) = ptr-taut (⟹-ren (extR ρ) p) (⟹-ren ρ q)
⟹-ren ρ (phrefl-pw {C = C} {C'} {s = t} {t'} key pC pt) =
  subst (λ z → hrefl (renTm ρ C) (renTm ρ t) ⟹ z)
        (cong₂ (λ x y → lam (hrefl x (app y (var vz))))
               (pwBody-ren ρ C' (pw?-⟹ pC key)) (sym (wk-ren ρ t')))
        (phrefl-pw (trans (pw?-ren ρ C) key)
                   (⟹-ren ρ pC) (⟹-ren ρ pt))
⟹-ren ρ (ptr-J-Hom {c₁ = c₁} key pe) =
  ptr-J-Hom (trans (stkA?-ren ρ c₁) key) (⟹-ren ρ pe)
⟹-ren ρ (ptr-pw {c = c} {c'} {a} {a'} {f} {f'} {e} {e'} key pc pa pf pe) =
  subst (λ z → tr (⌜Hom⌝ (renTm (extR ρ) c) (renTm (extR ρ) a) (var vz))
                  (lam (renTm (extR ρ) f)) (renTm ρ e) ⟹ z)
        (cong lam
          (tr-cong₃
            (⌜Hom⌝-cong₃
              (trans (cong (renTm pwShift)
                           (pwBody-ren (extR ρ) c' (pw?-⟹ pc key)))
                     (sym (pwShift-ren ρ (pwBody c'))))
              (cong (λ z → app z (var (vs vz))) (sym (wk-ren (extR ρ) a')))
              refl)
            refl
            (cong (λ z → app z (var vz)) (sym (wk-ren ρ e')))))
        (ptr-pw (trans (pw?-ren (extR ρ) c) key)
                (⟹-ren (extR ρ) pc) (⟹-ren (extR ρ) pa)
                (⟹-ren (extR ρ) pf) (⟹-ren ρ pe))
⟹-ren ρ (pap p q r) = pap (⟹-ren ρ p) (⟹-ren (extR ρ) q) (⟹-ren ρ r)
⟹-ren ρ (p⌜Id⌝ p q r) = p⌜Id⌝ (⟹-ren ρ p) (⟹-ren ρ q) (⟹-ren ρ r)
⟹-ren ρ (pidrefl p q) = pidrefl (⟹-ren ρ p) (⟹-ren ρ q)
⟹-ren ρ (pjsub p q r) = pjsub (⟹-ren (extR ρ) p) (⟹-ren ρ q) (⟹-ren ρ r)
⟹-ren ρ (pjsub-refl p) = pjsub-refl (⟹-ren ρ p)
⟹-ren ρ (pap-J {cB = cB} {cB'} {b} {b'} {c₁} {s = t} {t'} key p q r) =
  subst (λ z → renTm ρ (ap cB b (hrefl c₁ t)) ⟹ hrefl (renTm ρ cB') z)
        (sym (ren-comm ρ b' t'))
        (pap-J (trans (stkC?-ren ρ c₁) key)
               (⟹-ren ρ p) (⟹-ren (extR ρ) q) (⟹-ren ρ r))

pwBody-⟹ : {C C' : RTm Γ} → C ⟹ C' → pw? C ≡ true →
            pwBody C ⟹ pwBody C'
pwBody-⟹ (pvar _) ()
pwBody-⟹ (plam _) ()
pwBody-⟹ (papp _ _) ()
pwBody-⟹ (pβ _ _) ()
pwBody-⟹ (ppair _ _) ()
pwBody-⟹ (pabsurd _ _) ()
pwBody-⟹ (pfst _) ()
pwBody-⟹ (psnd _) ()
pwBody-⟹ (pβfst _ _) ()
pwBody-⟹ (pβsnd _ _) ()
pwBody-⟹ p⌜base⌝ ()
pwBody-⟹ (p⌜Π⌝ pγ pδ) h = pδ
pwBody-⟹ (p⌜Σ⌝ _ _) ()
pwBody-⟹ (p⌜Hom⌝ pc pa pb) h =
  p⌜Hom⌝ (pwBody-⟹ pc h)
         (papp (⟹-ren vs pa) (pvar vz))
         (papp (⟹-ren vs pb) (pvar vz))
pwBody-⟹ (phrefl _ _) ()
pwBody-⟹ (phrefl-pw _ _ _) ()
pwBody-⟹ (ptr _ _ _) ()
pwBody-⟹ (ptr-J-base _) ()
pwBody-⟹ (p⌜Nat⌝) ()
pwBody-⟹ (p⌜Unit⌝) ()
pwBody-⟹ (p⌜Mu⌝) ()
pwBody-⟹ (ptr-J-Unit _) ()
pwBody-⟹ (ptr-J-IMu _) ()
pwBody-⟹ (ptr-J-Mu _) ()
pwBody-⟹ (ptr-J-Σ _) ()
pwBody-⟹ (ptr-J-Hom _ _) ()
pwBody-⟹ (pap _ _ _) ()
pwBody-⟹ (pap-J _ _ _ _) ()
pwBody-⟹ (p⌜Id⌝ _ _ _) ()
pwBody-⟹ (pidrefl _ _) ()
pwBody-⟹ (pjsub _ _ _) ()
pwBody-⟹ (pjsub-refl _) ()
pwBody-⟹ (ptr-J-Id _) ()
pwBody-⟹ (ptr-taut _ _) ()
pwBody-⟹ (ptr-pw _ _ _ _ _) ()
pwBody-⟹ (punit) ()
pwBody-⟹ (pnzero) ()
pwBody-⟹ (pnsuc _) ()
pwBody-⟹ (pnatrec _ _ _) ()
pwBody-⟹ (pnatrec-zero _ _) ()
pwBody-⟹ (pnatrec-suc _ _ _) ()

⟹-exts : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟹ σ' x) →
         ∀ (x : Var (Γ ∙)) → extS σ x ⟹ extS σ' x
⟹-exts h vz     = pvar vz
⟹-exts h (vs x) = ⟹-ren vs (h x)

⟹-sub : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟹ σ' x) →
        {t u : RTm Γ} → t ⟹ u → subTm σ t ⟹ subTm σ' u
⟹-sub h (pvar x)  = h x
⟹-sub h (plam p)  = plam (⟹-sub (⟹-exts h) p)
⟹-sub h (papp p q) = papp (⟹-sub h p) (⟹-sub h q)
⟹-sub {σ = σ} {σ'} h (pβ {t = t} {t' = t'} {u = u} {u' = u'} p q) =
  subst (λ z → subTm σ (app (lam t) u) ⟹ z)
        (sym (sub-comm σ' t' u'))
        (pβ (⟹-sub (⟹-exts h) p) (⟹-sub h q))
⟹-sub h p⌜Nat⌝     = p⌜Nat⌝
⟹-sub h p⌜Unit⌝    = p⌜Unit⌝
⟹-sub h p⌜Mu⌝      = p⌜Mu⌝
⟹-sub h (ptr-J-Unit p) = ptr-J-Unit (⟹-sub h p)
⟹-sub h (ptr-J-Mu p)   = ptr-J-Mu (⟹-sub h p)
⟹-sub h (ptr-J-IMu p)  = ptr-J-IMu (⟹-sub h p)
⟹-sub h punit      = punit
⟹-sub h pnzero     = pnzero
⟹-sub h (pnsuc p)  = pnsuc (⟹-sub h p)
⟹-sub h (pcon p)   = pcon (⟹-sub h p)
⟹-sub h (pelim pms pt) = pelim (⟹-sub h pms) (⟹-sub h pt)
⟹-sub h (picon p)  = picon  (⟹-sub h p)
⟹-sub h (p⌜IMu⌝ p) = p⌜IMu⌝ (⟹-sub h p)
⟹-sub h (pielim pi pms pt) = pielim (⟹-sub h pi) (⟹-sub h pms) (⟹-sub h pt)
⟹-sub {σ = σ} {σ'} h (pιi {D = D} {i = i} {i'} {ms = ms} {ms'} {k = k} {p = p} {p'} pi pms pp) =
  subst (λ w → subTm σ (ielim D i ms (icon k p)) ⟹ w)
        (sym (trans (sub-ifieldsⁱ σ' D i' ms' (ilookupD D k) (sel k ms') p')
                    (cong (λ w → ifields D (subTm σ' i') (subTm σ' ms')
                                          (isingle (subTm σ' i'))
                                          (ilookupD D k) w (subTm σ' p'))
                          (sub-sel σ' k ms'))))
        (pιi (⟹-sub h pi) (⟹-sub h pms) (⟹-sub h pp))
⟹-sub {σ = σ} {σ'} h (pι {D = D} {ms = ms} {ms'} {k = k} {p = p} {p'} pms pp) =
  subst (λ w → subTm σ (elim D ms (con k p)) ⟹ w)
        (sym (trans (sub-fields σ' D ms' (lookupD D k) (sel k ms') p')
                    (cong (λ w → fields D (subTm σ' ms') (lookupD D k) w (subTm σ' p'))
                          (sub-sel σ' k ms'))))
        (pι (⟹-sub h pms) (⟹-sub h pp))
⟹-sub h (pnatrec pz ps pn) =
  pnatrec (⟹-sub h pz) (⟹-sub (⟹-exts (⟹-exts h)) ps) (⟹-sub h pn)
⟹-sub h (pnatrec-zero pz ps) =
  pnatrec-zero (⟹-sub h pz) (⟹-sub (⟹-exts (⟹-exts h)) ps)
⟹-sub {σ = σ} {σ'} h (pnatrec-suc {z = z} {z'} {s = s} {s'} {n = n} {n'} pz ps pn) =
  subst (λ w → subTm σ (natrec z s (nsuc n)) ⟹ w)
        (sym (trans (sub-comm σ' (subTm (extS (single n')) s') (natrec z' s' n'))
                    (cong (subTm (single (natrec (subTm σ' z')
                                                 (subTm (extS (extS σ')) s')
                                                 (subTm σ' n'))))
                          (sub-comm-ext σ' s' n'))))
        (pnatrec-suc (⟹-sub h pz) (⟹-sub (⟹-exts (⟹-exts h)) ps) (⟹-sub h pn))
⟹-sub h (ppair p q) = ppair (⟹-sub h p) (⟹-sub h q)
⟹-sub h (pordtr pa pt pu pp pq) =
  pordtr (⟹-sub h pa) (⟹-sub h pt) (⟹-sub h pu) (⟹-sub h pp) (⟹-sub h pq)
⟹-sub h pordtr-z = pordtr-z
⟹-sub h (pordtr-szz pp) = pordtr-szz (⟹-sub h pp)
⟹-sub h (pordtr-ssz pq) = pordtr-ssz (⟹-sub h pq)
⟹-sub h (pordtr-szs pa pu pp) = pordtr-szs (⟹-sub h pa) (⟹-sub h pu) (⟹-sub h pp)
⟹-sub h (pordtr-sss pa pt pu pp pq) =
  pordtr-sss (⟹-sub h pa) (⟹-sub h pt) (⟹-sub h pu) (⟹-sub h pp) (⟹-sub h pq)
⟹-sub h (pabsurd pc pe) = pabsurd (⟹-sub h pc) (⟹-sub h pe)
⟹-sub h (pfst p)    = pfst (⟹-sub h p)
⟹-sub h (psnd p)    = psnd (⟹-sub h p)
⟹-sub h (pβfst p q) = pβfst (⟹-sub h p) (⟹-sub h q)
⟹-sub h (pβsnd p q) = pβsnd (⟹-sub h p) (⟹-sub h q)
⟹-sub h p⌜base⌝     = p⌜base⌝
⟹-sub h (p⌜Π⌝ p q)  = p⌜Π⌝ (⟹-sub h p) (⟹-sub (⟹-exts h) q)
⟹-sub h (p⌜Σ⌝ p q)  = p⌜Σ⌝ (⟹-sub h p) (⟹-sub (⟹-exts h) q)
⟹-sub h (p⌜Hom⌝ p q r) = p⌜Hom⌝ (⟹-sub h p) (⟹-sub h q) (⟹-sub h r)
⟹-sub h (phrefl p q)   = phrefl (⟹-sub h p) (⟹-sub h q)
⟹-sub h (ptr p q r) = ptr (⟹-sub (⟹-exts h) p) (⟹-sub h q) (⟹-sub h r)
⟹-sub h (ptr-J-base p) = ptr-J-base (⟹-sub h p)
⟹-sub h (ptr-J-Σ p)    = ptr-J-Σ (⟹-sub h p)
⟹-sub h (ptr-J-Id p)   = ptr-J-Id (⟹-sub h p)
⟹-sub h (ptr-taut p q) = ptr-taut (⟹-sub (⟹-exts h) p) (⟹-sub h q)
⟹-sub {σ = σ} {σ'} h (phrefl-pw {C = C} {C'} {s = t} {t'} key pC pt) =
  subst (λ z → hrefl (subTm σ C) (subTm σ t) ⟹ z)
        (cong₂ (λ x y → lam (hrefl x (app y (var vz))))
               (pwBody-sub σ' C' (pw?-⟹ pC key))
               (sym (wk-sub σ' t')))
        (phrefl-pw (pw?-sub σ C key) (⟹-sub h pC) (⟹-sub h pt))
⟹-sub {σ = σ} {σ'} h (ptr-J-Hom {c₁ = c₁} key pe) =
  ptr-J-Hom (stkA?-sub σ c₁ key) (⟹-sub h pe)
⟹-sub {σ = σ} {σ'} h (ptr-pw {c = c} {c'} {a} {a'} {f} {f'} {e} {e'} key pc pa pf pe) =
  subst (λ z → tr (⌜Hom⌝ (subTm (extS σ) c) (subTm (extS σ) a) (var vz))
                  (lam (subTm (extS σ) f)) (subTm σ e) ⟹ z)
        (cong lam
          (tr-cong₃
            (⌜Hom⌝-cong₃
              (trans (cong (renTm pwShift)
                           (pwBody-sub (extS σ') c' (pw?-⟹ pc key)))
                     (sym (pwShift-sub σ' (pwBody c'))))
              (cong (λ z → app z (var (vs vz))) (sym (wk-sub (extS σ') a')))
              refl)
            refl
            (cong (λ z → app z (var vz)) (sym (wk-sub σ' e')))))
        (ptr-pw (pw?-sub (extS σ) c key)
                (⟹-sub (⟹-exts h) pc) (⟹-sub (⟹-exts h) pa)
                (⟹-sub (⟹-exts h) pf) (⟹-sub h pe))
⟹-sub h (pap p q r) = pap (⟹-sub h p) (⟹-sub (⟹-exts h) q) (⟹-sub h r)
⟹-sub h (p⌜Id⌝ p q r) = p⌜Id⌝ (⟹-sub h p) (⟹-sub h q) (⟹-sub h r)
⟹-sub h (pidrefl p q) = pidrefl (⟹-sub h p) (⟹-sub h q)
⟹-sub h (pjsub p q r) = pjsub (⟹-sub (⟹-exts h) p) (⟹-sub h q) (⟹-sub h r)
⟹-sub h (pjsub-refl p) = pjsub-refl (⟹-sub h p)
⟹-sub {σ = σ} {σ'} h (pap-J {cB = cB} {cB'} {b} {b'} {c₁} {s = t} {t'} key p q r) =
  subst (λ z → subTm σ (ap cB b (hrefl c₁ t)) ⟹ hrefl (subTm σ' cB') z)
        (sym (sub-comm σ' b' t'))
        (pap-J (stkC?-sub σ c₁ key)
               (⟹-sub h p) (⟹-sub (⟹-exts h) q) (⟹-sub h r))

-- ⚠ PLACED AFTER `⟹-sub`: a recursive field's index is an arbitrary
--   telescope term, so the `iρ` row moves it with `⟹-sub pσ (⟹-refl j)`.
--   The old `iρ f` needed only `papp (⟹-refl (εwkTm f)) pi` and could
--   live much earlier.  Do not hoist this back up.

-- ★ the INDEXED twins of `p-ihs`/`p-fields`.  Same reason they are lemmas and
--   not constructors: `iihs`/`ifields`/`sel` are metalevel, so `pιi`'s
--   right-hand side is built, not matched.  The `iρ` row is where the index
--   moves: the recursive call sits at `app (εwkTm f) i`, so the shift term
--   rides along by reflexivity and only `i` actually steps.
p-iihs : {D : IDesc} {ms ms' : RTm Γ} {Θ : Cx} {σ σ' : Sub Θ Γ}
         (C : ICon Θ) {p p' : RTm Γ} →
         (∀ x → σ x ⟹ σ' x) → ms ⟹ ms' → p ⟹ p' →
         iihs D ms σ C p ⟹ iihs D ms' σ' C p'
p-iihs iι       pσ pms pp = punit
p-iihs (iρ j C) pσ pms pp =
  ppair (pielim (⟹-sub pσ (⟹-refl j)) pms (pfst pp))
        (p-iihs C (λ { vz → pfst pp ; (vs x) → pσ x }) pms (psnd pp))
p-iihs (iκ κ C) pσ pms pp =
  p-iihs C (λ { vz → pfst pp ; (vs x) → pσ x }) pms (psnd pp)

p-ifields : {D : IDesc} {i i' ms ms' : RTm Γ} {Θ : Cx} {σ σ' : Sub Θ Γ}
            (C : ICon Θ) {m m' p p' : RTm Γ} →
            i ⟹ i' → (∀ x → σ x ⟹ σ' x) → ms ⟹ ms' → m ⟹ m' → p ⟹ p' →
            ifields D i ms σ C m p ⟹ ifields D i' ms' σ' C m' p'
p-ifields C pi pσ pms pm pp =
  papp (papp (papp pm pi) pp) (p-iihs C pσ pms pp)

single-⟹ : {u u' : RTm Γ} → u ⟹ u' →
           (x : Var (Γ ∙)) → single u x ⟹ single u' x
single-⟹ p vz     = p
single-⟹ p (vs x) = pvar x

------------------------------------------------------------------------
-- The complete development, and the triangle: `t ⟹ u → u ⟹ t⁺`.
------------------------------------------------------------------------

-- (the J decision is PATH-major then motive-major: `_⁺` discriminates
-- the path, and the two helpers discriminate the ⌜Hom⌝-keyed motive —
-- keeping every congruence row reducible at generic sub-shapes)
_⁺ : RTm Γ → RTm Γ
trB⁺ trU1⁺ : RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
trMu1⁺ᵈ : Desc → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
trIMu1⁺ᵈ : IDesc → RTy ε → RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
trI⁺ : RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
trS⁺ : RTm (Γ ∙) → RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
-- W2b helpers: `hr⁺` takes the DEVELOPED code/arg (the Boolean decided
-- on the original); `trH⁺`/`trP⁺` discriminate the motive, then their
-- `K`-helpers the Boolean key — every congruence row stays reducible.
hr⁺ : 𝔹 → RTm Γ → RTm Γ → RTm Γ
trH⁺ : RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
trHK⁺ : 𝔹 → RTm (Γ ∙) → RTm (Γ ∙) → RTm (Γ ∙) →
        RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
apH⁺ : 𝔹 → RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
trP⁺ : RTm (Γ ∙) → RTm (Γ ∙) → RTm (Γ ∙) → RTm (Γ ∙) → RTm Γ → RTm Γ
trPK⁺ : 𝔹 → RTm (Γ ∙) → RTm (Γ ∙) → RTm (Γ ∙) → RTm Γ → RTm Γ
-- ⚠ THE ORDER HELPERS EXIST FOR REDUCTION, NOT FOR TASTE.  `ordtr`'s
-- five rules discriminate THREE arguments, and clauses that match them
-- POSITIONALLY leave `_⁺` stuck: on `ordtr (nsuc n) t (var x) p q` with
-- `t` a variable, Agda cannot decide the `t ≡ nzero` clause, so `_⁺`
-- does not reduce and no congruence row typechecks.  Dispatching ONE
-- argument at a time, each level with its own catch-all, keeps `_⁺`
-- reducible as soon as the RELEVANT argument's head is known.  Same
-- reason `trH⁺`/`trHK⁺`/`apH⁺` above exist.
ord⁺  : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ordZ⁺ : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ordS⁺ : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
var x ⁺            = var x
lam t ⁺            = lam (t ⁺)
pair a b ⁺         = pair (a ⁺) (b ⁺)
app (lam t) u ⁺    = subTm (single (u ⁺)) (t ⁺)
app (var x) u ⁺    = app (var x ⁺) (u ⁺)
app (app f a) u ⁺  = app (app f a ⁺) (u ⁺)
app (ordtr a t u p q) w ⁺ = app (ordtr a t u p q ⁺) (w ⁺)
app (absurd c f) u ⁺ = app (absurd (c ⁺) (f ⁺)) (u ⁺)
app (pair a b) u ⁺ = app (pair a b ⁺) (u ⁺)
app (fst p) u ⁺    = app (fst p ⁺) (u ⁺)
app (snd p) u ⁺    = app (snd p ⁺) (u ⁺)
app ⌜Nat⌝ u ⁺      = app (⌜Nat⌝ ⁺) (u ⁺)
app ⌜Unit⌝ u ⁺     = app (⌜Unit⌝ ⁺) (u ⁺)
app (⌜Mu⌝ Dᵐ) u ⁺  = app ((⌜Mu⌝ Dᵐ) ⁺) (u ⁺)
app ⌜base⌝ u ⁺     = app (⌜base⌝ ⁺) (u ⁺)
app unit u ⁺       = app (unit ⁺) (u ⁺)
app nzero u ⁺      = app (nzero ⁺) (u ⁺)
app (nsuc n) u ⁺   = app (nsuc n ⁺) (u ⁺)
app (natrec z s n) u ⁺ = app (natrec z s n ⁺) (u ⁺)
app (⌜Π⌝ c d) u ⁺  = app (⌜Π⌝ c d ⁺) (u ⁺)
app (⌜Σ⌝ c d) u ⁺  = app (⌜Σ⌝ c d ⁺) (u ⁺)
app (⌜Hom⌝ c a b) u ⁺ = app (⌜Hom⌝ c a b ⁺) (u ⁺)
app (hrefl c t) u ⁺   = app (hrefl c t ⁺) (u ⁺)
app (tr d p e) u ⁺    = app (tr d p e ⁺) (u ⁺)
app (ap c b p) u ⁺    = app (ap c b p ⁺) (u ⁺)
app (⌜Id⌝ c a b) u ⁺  = app (⌜Id⌝ c a b ⁺) (u ⁺)
app (idrefl c t) u ⁺  = app (idrefl c t ⁺) (u ⁺)
app (jsub d p e) u ⁺  = app (jsub d p e ⁺) (u ⁺)
app (con k c) u ⁺     = app (con k c ⁺) (u ⁺)
app (elim D ms t) u ⁺ = app (elim D ms t ⁺) (u ⁺)
app (icon k p) u ⁺ = app (icon k p ⁺) (u ⁺)
app (ielim D i ms t) u ⁺ = app (ielim D i ms t ⁺) (u ⁺)
app (⌜IMu⌝ D I i) u ⁺ = app (⌜IMu⌝ D I i ⁺) (u ⁺)
fst (pair a b) ⁺   = a ⁺
fst (var x) ⁺      = fst (var x ⁺)
fst (lam t) ⁺      = fst (lam t ⁺)
fst (app f a) ⁺    = fst (app f a ⁺)
fst (fst p) ⁺      = fst (fst p ⁺)
fst (snd p) ⁺      = fst (snd p ⁺)
fst ⌜Nat⌝ ⁺        = fst (⌜Nat⌝ ⁺)
fst ⌜Unit⌝ ⁺       = fst (⌜Unit⌝ ⁺)
fst (⌜Mu⌝ Dᵐ) ⁺    = fst ((⌜Mu⌝ Dᵐ) ⁺)
fst ⌜base⌝ ⁺       = fst (⌜base⌝ ⁺)
fst unit ⁺         = fst (unit ⁺)
fst nzero ⁺        = fst (nzero ⁺)
fst (nsuc n) ⁺     = fst (nsuc n ⁺)
fst (ordtr a t u p q) ⁺ = fst (ordtr a t u p q ⁺)
fst (absurd c f) ⁺ = fst (absurd (c ⁺) (f ⁺))
fst (natrec z s n) ⁺ = fst (natrec z s n ⁺)
fst (⌜Π⌝ c d) ⁺    = fst (⌜Π⌝ c d ⁺)
fst (⌜Σ⌝ c d) ⁺    = fst (⌜Σ⌝ c d ⁺)
fst (⌜Hom⌝ c a b) ⁺ = fst (⌜Hom⌝ c a b ⁺)
fst (hrefl c t) ⁺   = fst (hrefl c t ⁺)
fst (tr d p e) ⁺    = fst (tr d p e ⁺)
fst (ap c b p) ⁺    = fst (ap c b p ⁺)
fst (⌜Id⌝ c a b) ⁺  = fst (⌜Id⌝ c a b ⁺)
fst (idrefl c t) ⁺  = fst (idrefl c t ⁺)
fst (jsub d p e) ⁺  = fst (jsub d p e ⁺)
fst (con k c) ⁺     = fst (con k c ⁺)
fst (elim D ms t) ⁺ = fst (elim D ms t ⁺)
fst (icon k p) ⁺ = fst (icon k p ⁺)
fst (ielim D i ms t) ⁺ = fst (ielim D i ms t ⁺)
fst (⌜IMu⌝ D I i) ⁺ = fst (⌜IMu⌝ D I i ⁺)
snd (pair a b) ⁺   = b ⁺
snd (var x) ⁺      = snd (var x ⁺)
snd (lam t) ⁺      = snd (lam t ⁺)
snd (app f a) ⁺    = snd (app f a ⁺)
snd (fst p) ⁺      = snd (fst p ⁺)
snd (snd p) ⁺      = snd (snd p ⁺)
snd ⌜Nat⌝ ⁺        = snd (⌜Nat⌝ ⁺)
snd ⌜Unit⌝ ⁺       = snd (⌜Unit⌝ ⁺)
snd (⌜Mu⌝ Dᵐ) ⁺    = snd ((⌜Mu⌝ Dᵐ) ⁺)
snd ⌜base⌝ ⁺       = snd (⌜base⌝ ⁺)
snd unit ⁺         = snd (unit ⁺)
snd nzero ⁺        = snd (nzero ⁺)
snd (nsuc n) ⁺     = snd (nsuc n ⁺)
snd (ordtr a t u p q) ⁺ = snd (ordtr a t u p q ⁺)
snd (absurd c f) ⁺ = snd (absurd (c ⁺) (f ⁺))
snd (natrec z s n) ⁺ = snd (natrec z s n ⁺)
snd (⌜Π⌝ c d) ⁺    = snd (⌜Π⌝ c d ⁺)
snd (⌜Σ⌝ c d) ⁺    = snd (⌜Σ⌝ c d ⁺)
snd (⌜Hom⌝ c a b) ⁺ = snd (⌜Hom⌝ c a b ⁺)
snd (hrefl c t) ⁺   = snd (hrefl c t ⁺)
snd (tr d p e) ⁺    = snd (tr d p e ⁺)
snd (ap c b p) ⁺    = snd (ap c b p ⁺)
snd (⌜Id⌝ c a b) ⁺  = snd (⌜Id⌝ c a b ⁺)
snd (idrefl c t) ⁺  = snd (idrefl c t ⁺)
snd (jsub d p e) ⁺  = snd (jsub d p e ⁺)
snd (con k c) ⁺     = snd (con k c ⁺)
snd (elim D ms t) ⁺ = snd (elim D ms t ⁺)
snd (icon k p) ⁺ = snd (icon k p ⁺)
snd (ielim D i ms t) ⁺ = snd (ielim D i ms t ⁺)
snd (⌜IMu⌝ D I i) ⁺ = snd (⌜IMu⌝ D I i ⁺)
⌜Nat⌝ ⁺            = ⌜Nat⌝
⌜Unit⌝ ⁺           = ⌜Unit⌝
(⌜Mu⌝ Dᵐ) ⁺        = ⌜Mu⌝ Dᵐ
⌜base⌝ ⁺           = ⌜base⌝
⌜Π⌝ c d ⁺          = ⌜Π⌝ (c ⁺) (d ⁺)
⌜Σ⌝ c d ⁺          = ⌜Σ⌝ (c ⁺) (d ⁺)
⌜Hom⌝ c a b ⁺      = ⌜Hom⌝ (c ⁺) (a ⁺) (b ⁺)
-- `hrefl` — W2b: unfolds POINTWISE at pw-able codes (the Boolean is
-- decided on the ORIGINAL code; the pieces are developed).
hrefl c f ⁺         = hr⁺ (pw? c) (c ⁺) (f ⁺)
-- `tr` — the five path-keyed rules (SpikeTr), then congruence.  The
-- clause order encodes the case tree: split the path first (J fires on
-- canonical `hrefl` — head-stable stuck codes only), then the motive
-- (taut at `var vz`, pointwise composition at a `⌜Π⌝`-ambient `⌜Hom⌝`).
-- ⚠ NO ⌜Nat⌝ row: J is disabled there, so a `hrefl ⌜Nat⌝` path falls
-- through to the congruence at the bottom of this tree.
tr d (hrefl ⌜Unit⌝ s) e ⁺        = trU1⁺ d s e
tr d (hrefl (⌜Mu⌝ Dᵐ) s) e ⁺     = trMu1⁺ᵈ Dᵐ d s e
tr d (hrefl (⌜IMu⌝ Dⁱ Iⁱ iˣ) s) e ⁺ = trIMu1⁺ᵈ Dⁱ Iⁱ iˣ d s e
tr d (hrefl ⌜base⌝ s) e ⁺        = trB⁺ d s e
tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e ⁺   = trS⁺ d c₁ c₂ s e
tr d (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e ⁺ = trI⁺ d c₁ a₁ b₁ s e
tr d (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e ⁺ = trH⁺ d c₁ a₁ b₁ s e
tr (var vz) (lam f) e ⁺          = app (lam (f ⁺)) (e ⁺)
tr (⌜Hom⌝ c a m) (lam f) e ⁺     = trP⁺ c a m f e
tr d p e ⁺ = tr (d ⁺) (p ⁺) (e ⁺)
-- `ap` — J fires on canonical `hrefl` at head-stable codes only (the
-- same discrimination as `tr`'s path analysis, minus the motive).
-- (likewise no ⌜Nat⌝ row here — `ap-J` shares `stkC?` as its key.)
ap cB b (hrefl ⌜Unit⌝ s) ⁺        = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜Mu⌝ Dᵐ) s) ⁺     = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜IMu⌝ Dⁱ Iⁱ iˣ) s) ⁺ = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl ⌜base⌝ s) ⁺        = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜Σ⌝ c₁ c₂) s) ⁺   = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜Id⌝ c₁ a₁ b₁) s) ⁺ = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) ⁺ = apH⁺ (stkA? c₁) cB b c₁ a₁ b₁ s
ap cB b p ⁺ = ap (cB ⁺) (b ⁺) (p ⁺)
-- the two-former kernel: Id is inert (congruences), and jsub's J is
-- UNKEYED — the refl-path row fires unconditionally.
ordtr a t u p q ⁺ = ord⁺ a t u p q
absurd c e ⁺ = absurd (c ⁺) (e ⁺)
⌜Id⌝ c a b ⁺ = ⌜Id⌝ (c ⁺) (a ⁺) (b ⁺)
idrefl c t ⁺ = idrefl (c ⁺) (t ⁺)
jsub d (idrefl c s) e ⁺ = e ⁺
jsub d p e ⁺ = jsub (d ⁺) (p ⁺) (e ⁺)
-- ★ WF stage A: the recursor develops by the numeral head; everything
-- else is congruence.
unit ⁺  = unit
nzero ⁺ = nzero
nsuc n ⁺ = nsuc (n ⁺)
natrec z s nzero ⁺ = z ⁺
natrec z s (nsuc n) ⁺ =
  subTm (single (natrec (z ⁺) (s ⁺) (n ⁺))) (subTm (extS (single (n ⁺))) (s ⁺))
natrec z s n ⁺ = natrec (z ⁺) (s ⁺) (n ⁺)
-- ★ INDUCTIVE TYPES: `elim` develops by the SCRUTINEE's head, exactly as
-- `natrec` does — one keyed row, then congruence.
con k c ⁺ = con k (c ⁺)
elim D ms (con k c) ⁺ = fields D (ms ⁺) (lookupD D k) (sel k (ms ⁺)) (c ⁺)
elim D ms t ⁺ = elim D (ms ⁺) (t ⁺)
icon k c ⁺ = icon k (c ⁺)
⌜IMu⌝ D I i ⁺ = ⌜IMu⌝ D I (i ⁺)
ielim D i ms (icon k c) ⁺ =
  ifields D (i ⁺) (ms ⁺) (isingle (i ⁺)) (ilookupD D k) (sel k (ms ⁺)) (c ⁺)
ielim D i ms t ⁺ = ielim D (i ⁺) (ms ⁺) (t ⁺)

trB⁺ (⌜Hom⌝ c a m) s e = e ⁺
trB⁺ d s e = tr (d ⁺) (hrefl ⌜base⌝ (s ⁺)) (e ⁺)

trU1⁺ (⌜Hom⌝ c a m) s e = e ⁺
trU1⁺ d s e = tr (d ⁺) (hrefl ⌜Unit⌝ (s ⁺)) (e ⁺)

-- ⚠ `trMu1⁺` must be given the DESCRIPTION, since the rebuilt `hrefl`
--   mentions it; `trU1⁺` needs no such argument because `⌜Unit⌝` is nullary.
trMu1⁺ᵈ Dᵐ (⌜Hom⌝ c a m) s e = e ⁺
trMu1⁺ᵈ Dᵐ d s e = tr (d ⁺) (hrefl (⌜Mu⌝ Dᵐ) (s ⁺)) (e ⁺)
-- ⚠ THREE carried arguments, not one: `⌜IMu⌝` holds the description, the
--   index TYPE and the index TERM, and the congruence row mentions all
--   three (`trMu1⁺ᵈ` needs only `Dᵐ`).
trIMu1⁺ᵈ Dⁱ Iⁱ iˣ (⌜Hom⌝ c a m) s e = e ⁺
trIMu1⁺ᵈ Dⁱ Iⁱ iˣ d s e = tr (d ⁺) (hrefl (⌜IMu⌝ Dⁱ Iⁱ (iˣ ⁺)) (s ⁺)) (e ⁺)

trS⁺ (⌜Hom⌝ c a m) c₁ c₂ s e = e ⁺
trS⁺ d c₁ c₂ s e = tr (d ⁺) (hrefl (⌜Σ⌝ (c₁ ⁺) (c₂ ⁺)) (s ⁺)) (e ⁺)

trI⁺ (⌜Hom⌝ c a m) c₁ a₁ b₁ s e = e ⁺
trI⁺ d c₁ a₁ b₁ s e = tr (d ⁺) (hrefl (⌜Id⌝ (c₁ ⁺) (a₁ ⁺) (b₁ ⁺)) (s ⁺)) (e ⁺)

hr⁺ true  C T = lam (hrefl (pwBody C) (app (renTm vs T) (var vz)))
hr⁺ false C T = hrefl C T

trH⁺ (⌜Hom⌝ c a m) c₁ a₁ b₁ s e = trHK⁺ (stkA? c₁) c a m c₁ a₁ b₁ s e
trH⁺ d c₁ a₁ b₁ s e =
  tr (d ⁺) (hr⁺ (pw? c₁) (⌜Hom⌝ (c₁ ⁺) (a₁ ⁺) (b₁ ⁺)) (s ⁺)) (e ⁺)

trHK⁺ true  c a m c₁ a₁ b₁ s e = e ⁺
trHK⁺ false c a m c₁ a₁ b₁ s e =
  tr (⌜Hom⌝ (c ⁺) (a ⁺) (m ⁺))
     (hr⁺ (pw? c₁) (⌜Hom⌝ (c₁ ⁺) (a₁ ⁺) (b₁ ⁺)) (s ⁺)) (e ⁺)

apH⁺ true  cB b c₁ a₁ b₁ s = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
apH⁺ false cB b c₁ a₁ b₁ s =
  ap (cB ⁺) (b ⁺) (hr⁺ (pw? c₁) (⌜Hom⌝ (c₁ ⁺) (a₁ ⁺) (b₁ ⁺)) (s ⁺))

trP⁺ c a (var vz) f e = trPK⁺ (pw? c) c a f e
trP⁺ c a m f e = tr (⌜Hom⌝ (c ⁺) (a ⁺) (m ⁺)) (lam (f ⁺)) (e ⁺)

trPK⁺ true  c a f e =
  lam (tr (⌜Hom⌝ (renTm pwShift (pwBody (c ⁺)))
                 (app (renTm vs (a ⁺)) (var (vs vz)))
                 (var vz))
          (f ⁺)
          (app (renTm vs (e ⁺)) (var vz)))
trPK⁺ false c a f e = tr (⌜Hom⌝ (c ⁺) (a ⁺) (var vz)) (lam (f ⁺)) (e ⁺)

-- the order's development, dispatching `a`, then `u`, then `t`.  Only
-- `ord⁺`'s first clause can fire on a non-`nsuc` bound, so the two
-- inner helpers never see one.
--
-- ⚠ peel ONCE.  Takahashi's development fires the redexes present in
-- the ORIGINAL term; the `ordtr a t u p q` that `ordS⁺`'s `nsuc` row
-- exposes is a NEW redex created by the step, and re-firing it there
-- breaks the triangle.
ord⁺ nzero t u p q          = unit
ord⁺ (nsuc a) t nzero p q    = ordZ⁺ a t p q
ord⁺ (nsuc a) t (nsuc u) p q = ordS⁺ a t u p q
ord⁺ a t u p q               = ordtr (a ⁺) (t ⁺) (u ⁺) (p ⁺) (q ⁺)

ordZ⁺ a nzero p q    = p ⁺
ordZ⁺ a (nsuc t) p q = q ⁺
ordZ⁺ a t p q        = ordtr (nsuc (a ⁺)) (t ⁺) nzero (p ⁺) (q ⁺)

ordS⁺ a nzero u p q    = absurd (⌜Hom⌝ ⌜Nat⌝ (a ⁺) (u ⁺)) (p ⁺)
ordS⁺ a (nsuc t) u p q = ordtr (a ⁺) (t ⁺) (u ⁺) (p ⁺) (q ⁺)
ordS⁺ a t u p q        = ordtr (nsuc (a ⁺)) (t ⁺) (nsuc (u ⁺)) (p ⁺) (q ⁺)

-- the triangle's Boolean dispatchers: given the developed pieces and
-- the key's transport, land in the right `hr⁺`/`trHK⁺`/`trPK⁺` branch.
hr-tri : {C' X s' Y : RTm Γ} (b : 𝔹) → (b ≡ true → pw? C' ≡ true) →
         C' ⟹ X → s' ⟹ Y → hrefl C' s' ⟹ hr⁺ b X Y
hr-tri true  kf px py = phrefl-pw (kf refl) px py
hr-tri false kf px py = phrefl px py

trHK-tri : {c c' a a' m m' : RTm (Γ ∙)}
           {c₁ c₁' a₁ a₁' b₁ b₁' s s' e e' : RTm Γ}
           (b : 𝔹) → (b ≡ true → stkA? c₁' ≡ true) →
           (pw? c₁ ≡ true → pw? c₁' ≡ true) →
           c' ⟹ (c ⁺) → a' ⟹ (a ⁺) → m' ⟹ (m ⁺) →
           c₁' ⟹ (c₁ ⁺) → a₁' ⟹ (a₁ ⁺) → b₁' ⟹ (b₁ ⁺) →
           s' ⟹ (s ⁺) → e' ⟹ (e ⁺) →
           tr (⌜Hom⌝ c' a' m') (hrefl (⌜Hom⌝ c₁' a₁' b₁') s') e' ⟹
           trHK⁺ b c a m c₁ a₁ b₁ s e
trHK-tri true  kS kP pc pa pm pc₁ pa₁ pb₁ ps pe = ptr-J-Hom (kS refl) pe
trHK-tri {c₁ = c₁} false kS kP pc pa pm pc₁ pa₁ pb₁ ps pe =
  ptr (p⌜Hom⌝ pc pa pm)
      (hr-tri (pw? c₁) kP (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe

trPK-tri : {c c' a a' f f' : RTm (Γ ∙)} {e e' : RTm Γ}
           (b : 𝔹) → (b ≡ true → pw? c' ≡ true) →
           c' ⟹ (c ⁺) → a' ⟹ (a ⁺) → f' ⟹ (f ⁺) → e' ⟹ (e ⁺) →
           tr (⌜Hom⌝ c' a' (var vz)) (lam f') e' ⟹ trPK⁺ b c a f e
trPK-tri true  kf pc pa pf pe = ptr-pw (kf refl) pc pa pf pe
trPK-tri false kf pc pa pf pe = ptr (p⌜Hom⌝ pc pa (pvar vz)) (plam pf) pe

apH-tri : {cB cB' : RTm Γ} {b b' : RTm (Γ ∙)}
          {c₁ c₁' a₁ a₁' b₁ b₁' s s' : RTm Γ}
          (k : 𝔹) → (k ≡ true → stkA? c₁' ≡ true) →
          (pw? c₁ ≡ true → pw? c₁' ≡ true) →
          cB' ⟹ (cB ⁺) → b' ⟹ (b ⁺) →
          c₁' ⟹ (c₁ ⁺) → a₁' ⟹ (a₁ ⁺) → b₁' ⟹ (b₁ ⁺) → s' ⟹ (s ⁺) →
          ap cB' b' (hrefl (⌜Hom⌝ c₁' a₁' b₁') s') ⟹ apH⁺ k cB b c₁ a₁ b₁ s
apH-tri true  kS kP pcB pb pc₁ pa₁ pb₁ ps = pap-J (kS refl) pcB pb ps
apH-tri {c₁ = c₁} false kS kP pcB pb pc₁ pa₁ pb₁ ps =
  pap pcB pb (hr-tri (pw? c₁) kP (p⌜Hom⌝ pc₁ pa₁ pb₁) ps)

⟹-⁺ : {t u : RTm Γ} → t ⟹ u → u ⟹ t ⁺
⟹-⁺ (pvar x)               = pvar x
⟹-⁺ (plam p)               = plam (⟹-⁺ p)
⟹-⁺ (ppair p q)            = ppair (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (papp (pvar x) q)      = papp (pvar x) (⟹-⁺ q)
⟹-⁺ (papp (plam p) q)      = pβ (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (papp (papp p₁ p₂) q)  = papp (⟹-⁺ (papp p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (papp (pβ p₁ p₂) q)    = papp (⟹-⁺ (pβ p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (papp (ppair p₁ p₂) q) = papp (⟹-⁺ (ppair p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (papp (pfst p₁) q)     = papp (⟹-⁺ (pfst p₁)) (⟹-⁺ q)
⟹-⁺ (papp (psnd p₁) q)     = papp (⟹-⁺ (psnd p₁)) (⟹-⁺ q)
⟹-⁺ (papp (pβfst p₁ p₂) q) = papp (⟹-⁺ (pβfst p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (papp (pβsnd p₁ p₂) q) = papp (⟹-⁺ (pβsnd p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (papp p⌜base⌝ q)       = papp (⟹-⁺ p⌜base⌝) (⟹-⁺ q)
⟹-⁺ (papp (p⌜Π⌝ p₁ p₂) q)  = papp (⟹-⁺ (p⌜Π⌝ p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (papp (p⌜Σ⌝ p₁ p₂) q)  = papp (⟹-⁺ (p⌜Σ⌝ p₁ p₂)) (⟹-⁺ q)
-- ★★ ORDER TRANSPORT.  The five roots fire when the SOURCE endpoints
-- are numerals; `nzero`/`nsuc` sources admit only `pnzero`/`pnsuc`, so
-- matching the derivation shallowly pins the targets too.
-- ★ ordtr as a SCRUTINEE: nothing fires, so every wrapper is
-- congruence.
⟹-⁺ (papp w@(pordtr _ _ _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@pordtr-z q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pordtr-szz _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pordtr-ssz _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pordtr-szs _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pordtr-sss _ _ _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (pfst w@(pordtr _ _ _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@pordtr-z) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pordtr-szz _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pordtr-ssz _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pordtr-szs _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pordtr-sss _ _ _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (psnd w@(pordtr _ _ _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@pordtr-z) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pordtr-szz _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pordtr-ssz _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pordtr-szs _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pordtr-sss _ _ _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (ptr pd w@(pordtr _ _ _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@pordtr-z pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pordtr-szz _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pordtr-ssz _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pordtr-szs _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pordtr-sss _ _ _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pap pcB pb w@(pordtr _ _ _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@pordtr-z) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pordtr-szz _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pordtr-ssz _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pordtr-szs _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pordtr-sss _ _ _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pjsub pd w@(pordtr _ _ _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@pordtr-z pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pordtr-szz _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pordtr-ssz _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pordtr-szs _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pordtr-sss _ _ _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pnatrec pz pw w@(pordtr _ _ _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ pw) (⟹-⁺ w)
⟹-⁺ (pnatrec pz pw w@pordtr-z) = pnatrec (⟹-⁺ pz) (⟹-⁺ pw) (⟹-⁺ w)
⟹-⁺ (pnatrec pz pw w@(pordtr-szz _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ pw) (⟹-⁺ w)
⟹-⁺ (pnatrec pz pw w@(pordtr-ssz _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ pw) (⟹-⁺ w)
⟹-⁺ (pnatrec pz pw w@(pordtr-szs _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ pw) (⟹-⁺ w)
⟹-⁺ (pnatrec pz pw w@(pordtr-sss _ _ _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ pw) (⟹-⁺ w)
-- an `ordtr` MOTIVE is neither `var vz` (taut) nor a pw-able ⌜Hom⌝,
-- so every path shape is congruence.
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl (p⌜Σ⌝ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl (p⌜Id⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr _ _ _ _ _) v@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl (p⌜Σ⌝ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl (p⌜Id⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@pordtr-z v@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl (p⌜Σ⌝ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl (p⌜Id⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szz _) v@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl (p⌜Σ⌝ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl (p⌜Id⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-ssz _) v@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl (p⌜Σ⌝ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl (p⌜Id⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-szs _ _ _) v@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl (p⌜Σ⌝ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl (p⌜Id⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pordtr-sss _ _ _ _ _) v@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
-- an `ordtr` as a path CODE is neither `pw?` nor `stkC?`, and as the
-- endpoint of a pw motive it is not `var vz` — congruence throughout.
⟹-⁺ (ptr pd w@(phrefl (pordtr _ _ _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ _ _ (pordtr _ _ _ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (pap pcB pb w@(phrefl (pordtr _ _ _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (ptr pd w@(phrefl pordtr-z _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ _ _ pordtr-z) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (pap pcB pb w@(phrefl pordtr-z _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (ptr pd w@(phrefl (pordtr-szz _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ _ _ (pordtr-szz _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (pap pcB pb w@(phrefl (pordtr-szz _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (ptr pd w@(phrefl (pordtr-ssz _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ _ _ (pordtr-ssz _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (pap pcB pb w@(phrefl (pordtr-ssz _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (ptr pd w@(phrefl (pordtr-szs _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ _ _ (pordtr-szs _ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (pap pcB pb w@(phrefl (pordtr-szs _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (ptr pd w@(phrefl (pordtr-sss _ _ _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ _ _ (pordtr-sss _ _ _ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (pap pcB pb w@(phrefl (pordtr-sss _ _ _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pordtr z0@(pvar x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(plam x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(papp x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pβ x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ppair x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pabsurd x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pordtr x x₁ x₂ x₃ x₄) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@pordtr-z z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pordtr-szz x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pordtr-ssz x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pordtr-szs x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pordtr-sss x x₁ x₂ x₃ x₄) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pfst x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(psnd x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pβfst x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pβsnd x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@p⌜base⌝ z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(p⌜Π⌝ x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(p⌜Σ⌝ x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(p⌜Hom⌝ x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(phrefl x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-J-base x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@p⌜Nat⌝ z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@p⌜Unit⌝ z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@p⌜Mu⌝ z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(p⌜IMu⌝ _) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-J-Unit x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-J-Mu x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-J-IMu x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-J-Σ x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-J-Id x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-taut x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(phrefl-pw x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-J-Hom x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(ptr-pw x x₁ x₂ x₃ x₄) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pap x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pap-J x x₁ x₂ x₃) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(p⌜Id⌝ x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pidrefl x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pjsub x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pjsub-refl x) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@punit z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pvar x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(plam x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(papp x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pβ x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ppair x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pabsurd x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pordtr x₂ x₃ x₄ x₅ x₆) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@pordtr-z z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pordtr-szz x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pordtr-ssz x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pordtr-szs x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pordtr-sss x₂ x₃ x₄ x₅ x₆) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pfst x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(psnd x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pβfst x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pβsnd x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@p⌜base⌝ z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(p⌜Π⌝ x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(p⌜Σ⌝ x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(p⌜Hom⌝ x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(phrefl x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-J-base x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@p⌜Nat⌝ z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@p⌜Unit⌝ z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@p⌜Mu⌝ z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(p⌜IMu⌝ _) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-J-Unit x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-J-Mu x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-J-IMu x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-J-Σ x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-J-Id x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-taut x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(phrefl-pw x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-J-Hom x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(ptr-pw x₂ x₃ x₄ x₅ x₆) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pap x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pap-J x₂ x₃ x₄ x₅) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(p⌜Id⌝ x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pidrefl x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pjsub x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pjsub-refl x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@punit z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pvar x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(plam x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(papp x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pβ x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ppair x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pabsurd x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr x₁ x₂ x₃ x₄ x₅) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@pordtr-z z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-szz x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-ssz x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-szs x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-sss x₁ x₂ x₃ x₄ x₅) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pfst x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(psnd x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pβfst x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pβsnd x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜base⌝ z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Π⌝ x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Σ⌝ x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Hom⌝ x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(phrefl x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-base x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜Nat⌝ z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜Unit⌝ z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜Mu⌝ z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜IMu⌝ _) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Unit x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Mu x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-IMu x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Σ x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Id x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-taut x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(phrefl-pw x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Hom x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-pw x₁ x₂ x₃ x₄ x₅) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pap x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pap-J x₁ x₂ x₃ x₄) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Id⌝ x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pidrefl x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pjsub x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pjsub-refl x₁) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@punit z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pnatrec x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pnatrec-zero x₁ x₂) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pnatrec-suc x₁ x₂ x₃) z2@pnzero z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pvar x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(plam x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(papp x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pβ x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ppair x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pabsurd x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr x₁ x₂ x₃ x₄ x₅) z2@(pnsuc x₆) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@pordtr-z z2@(pnsuc x₁) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-szz x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-ssz x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-szs x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pordtr-sss x₁ x₂ x₃ x₄ x₅) z2@(pnsuc x₆) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pfst x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(psnd x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pβfst x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pβsnd x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜base⌝ z2@(pnsuc x₁) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Π⌝ x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Σ⌝ x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Hom⌝ x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(phrefl x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-base x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜Nat⌝ z2@(pnsuc x₁) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜Unit⌝ z2@(pnsuc x₁) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@p⌜Mu⌝ z2@(pnsuc x₁) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜IMu⌝ _) z2@(pnsuc x₁) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Unit x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Mu x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-IMu x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Σ x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Id x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-taut x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(phrefl-pw x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-J-Hom x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(ptr-pw x₁ x₂ x₃ x₄ x₅) z2@(pnsuc x₆) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pap x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pap-J x₁ x₂ x₃ x₄) z2@(pnsuc x₅) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(p⌜Id⌝ x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pidrefl x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pjsub x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pjsub-refl x₁) z2@(pnsuc x₂) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@punit z2@(pnsuc x₁) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pnatrec x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pnatrec-zero x₁ x₂) z2@(pnsuc x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1@(pnatrec-suc x₁ x₂ x₃) z2@(pnsuc x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pnatrec x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pnatrec-zero x₂ x₃) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnsuc x) z1 z2@(pnatrec-suc x₂ x₃ x₄) z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnatrec x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnatrec-zero x x₁) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr z0@(pnatrec-suc x x₁ x₂) z1 z2 z3 z4) = pordtr (⟹-⁺ z0) (⟹-⁺ z1) (⟹-⁺ z2) (⟹-⁺ z3) (⟹-⁺ z4)
⟹-⁺ (pordtr pnzero pt pu pp pq) = pordtr-z
⟹-⁺ (pordtr (pnsuc pa) pnzero pnzero pp pq) = pordtr-szz (⟹-⁺ pp)
⟹-⁺ (pordtr (pnsuc pa) (pnsuc pt) pnzero pp pq) = pordtr-ssz (⟹-⁺ pq)
⟹-⁺ (pordtr (pnsuc pa) pnzero (pnsuc pu) pp pq) =
  pordtr-szs (⟹-⁺ pa) (⟹-⁺ pu) (⟹-⁺ pp)
-- the peel is a RECURSIVE development: `_⁺` fires again on the peeled
-- endpoints, so the triangle is the same lemma one layer down.
⟹-⁺ (pordtr (pnsuc pa) (pnsuc pt) (pnsuc pu) pp pq) =
  pordtr-sss (⟹-⁺ pa) (⟹-⁺ pt) (⟹-⁺ pu) (⟹-⁺ pp) (⟹-⁺ pq)
-- ★ the five rows above are the WHOLE keying story.  A `nzero`/`nsuc`
-- SOURCE admits only `pnzero`/`pnsuc`, so matching the DERIVATION
-- shallowly pins the target too — no Boolean key, no `subst`, and one
-- generic congruence covers every other bound.
⟹-⁺ pordtr-z = ⟹-refl _
⟹-⁺ (pordtr-szz pp) = ⟹-⁺ pp
⟹-⁺ (pordtr-ssz pq) = ⟹-⁺ pq
⟹-⁺ (pordtr-szs pa pu pp) = pabsurd (p⌜Hom⌝ p⌜Nat⌝ (⟹-⁺ pa) (⟹-⁺ pu)) (⟹-⁺ pp)
⟹-⁺ (pordtr-sss pa pt pu pp pq) =
  pordtr (⟹-⁺ pa) (⟹-⁺ pt) (⟹-⁺ pu) (⟹-⁺ pp) (⟹-⁺ pq)
⟹-⁺ (pabsurd pc pe)        = pabsurd (⟹-⁺ pc) (⟹-⁺ pe)
⟹-⁺ (papp w@(pabsurd _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (pfst w@(pabsurd _ _))   = pfst (⟹-⁺ w)
⟹-⁺ (psnd w@(pabsurd _ _))   = psnd (⟹-⁺ w)
⟹-⁺ (pfst (pvar x))        = pfst (pvar x)
⟹-⁺ (pfst (plam p))        = pfst (⟹-⁺ (plam p))
⟹-⁺ (pfst (papp p₁ p₂))    = pfst (⟹-⁺ (papp p₁ p₂))
⟹-⁺ (pfst (pβ p₁ p₂))      = pfst (⟹-⁺ (pβ p₁ p₂))
⟹-⁺ (pfst (ppair p₁ p₂))   = pβfst (⟹-⁺ p₁) (⟹-⁺ p₂)
⟹-⁺ (pfst (pfst p₁))       = pfst (⟹-⁺ (pfst p₁))
⟹-⁺ (pfst (psnd p₁))       = pfst (⟹-⁺ (psnd p₁))
⟹-⁺ (pfst (pβfst p₁ p₂))   = pfst (⟹-⁺ (pβfst p₁ p₂))
⟹-⁺ (pfst (pβsnd p₁ p₂))   = pfst (⟹-⁺ (pβsnd p₁ p₂))
⟹-⁺ (pfst p⌜base⌝)         = pfst (⟹-⁺ p⌜base⌝)
⟹-⁺ (pfst (p⌜Π⌝ p₁ p₂))    = pfst (⟹-⁺ (p⌜Π⌝ p₁ p₂))
⟹-⁺ (pfst (p⌜Σ⌝ p₁ p₂))    = pfst (⟹-⁺ (p⌜Σ⌝ p₁ p₂))
⟹-⁺ (psnd (pvar x))        = psnd (pvar x)
⟹-⁺ (psnd (plam p))        = psnd (⟹-⁺ (plam p))
⟹-⁺ (psnd (papp p₁ p₂))    = psnd (⟹-⁺ (papp p₁ p₂))
⟹-⁺ (psnd (pβ p₁ p₂))      = psnd (⟹-⁺ (pβ p₁ p₂))
⟹-⁺ (psnd (ppair p₁ p₂))   = pβsnd (⟹-⁺ p₁) (⟹-⁺ p₂)
⟹-⁺ (psnd (pfst p₁))       = psnd (⟹-⁺ (pfst p₁))
⟹-⁺ (psnd (psnd p₁))       = psnd (⟹-⁺ (psnd p₁))
⟹-⁺ (psnd (pβfst p₁ p₂))   = psnd (⟹-⁺ (pβfst p₁ p₂))
⟹-⁺ (psnd (pβsnd p₁ p₂))   = psnd (⟹-⁺ (pβsnd p₁ p₂))
⟹-⁺ (psnd p⌜base⌝)         = psnd (⟹-⁺ p⌜base⌝)
⟹-⁺ (psnd (p⌜Π⌝ p₁ p₂))    = psnd (⟹-⁺ (p⌜Π⌝ p₁ p₂))
⟹-⁺ (psnd (p⌜Σ⌝ p₁ p₂))    = psnd (⟹-⁺ (p⌜Σ⌝ p₁ p₂))
⟹-⁺ p⌜Nat⌝                 = p⌜Nat⌝
⟹-⁺ p⌜Unit⌝                = p⌜Unit⌝
⟹-⁺ p⌜Mu⌝                = p⌜Mu⌝
⟹-⁺ (p⌜IMu⌝ p)             = p⌜IMu⌝ (⟹-⁺ p)
⟹-⁺ punit                  = punit
⟹-⁺ pnzero                 = pnzero
⟹-⁺ (pnsuc p)              = pnsuc (⟹-⁺ p)
⟹-⁺ (pnatrec pz ps pnzero)     = pnatrec-zero (⟹-⁺ pz) (⟹-⁺ ps)
⟹-⁺ (pnatrec pz ps pn@(pvar _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(plam _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(papp _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pβ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ppair _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pfst _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(psnd _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pβfst _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pβsnd _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@p⌜base⌝) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(p⌜Π⌝ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(p⌜Σ⌝ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(p⌜Hom⌝ _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(phrefl _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-J-base _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(p⌜Nat⌝)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(p⌜Unit⌝)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(p⌜Mu⌝)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@((p⌜IMu⌝ _))) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-J-Unit _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-J-Mu _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-J-IMu _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-J-Σ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-J-Id _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-taut _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(phrefl-pw _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-J-Hom _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(ptr-pw _ _ _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pap _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pap-J _ _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(p⌜Id⌝ _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pidrefl _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pjsub _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pjsub-refl _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@punit) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pnatrec _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pnatrec-zero _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps pn@(pnatrec-suc _ _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec pz ps (pnsuc pm)) = pnatrec-suc (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pm)
⟹-⁺ (pnatrec-zero pz ps)   = ⟹-⁺ pz
⟹-⁺ (pnatrec-suc pz ps pn) =
  ⟹-sub (single-⟹ (pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)))
        (⟹-sub (⟹-exts (single-⟹ (⟹-⁺ pn))) (⟹-⁺ ps))
⟹-⁺ (pβ p q)               = ⟹-sub (single-⟹ (⟹-⁺ q)) (⟹-⁺ p)
⟹-⁺ (pβfst p q)            = ⟹-⁺ p
⟹-⁺ (pβsnd p q)            = ⟹-⁺ q
⟹-⁺ p⌜base⌝                = p⌜base⌝
⟹-⁺ (p⌜Π⌝ p q)             = p⌜Π⌝ (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (p⌜Σ⌝ p q)             = p⌜Σ⌝ (⟹-⁺ p) (⟹-⁺ q)
-- W2 formers as `app`/`fst`/`snd` heads — plain congruence (as-patterns
-- keep every recursive call on a strict subterm for the termination
-- checker; the pattern's only job is to pin the head so `_⁺` reduces).
⟹-⁺ (papp w@(p⌜Hom⌝ _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(phrefl _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-J-base _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(p⌜Nat⌝) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(p⌜Unit⌝) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(p⌜Mu⌝) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@((p⌜IMu⌝ _)) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-J-Unit _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-J-Mu _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-J-IMu _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-J-Σ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-taut _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(phrefl-pw _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-J-Hom _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-pw _ _ _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(punit) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pnzero) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pnsuc _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pnatrec _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pnatrec-zero _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pnatrec-suc _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(ptr-J-Id _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(p⌜Id⌝ _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pidrefl _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pjsub _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pjsub-refl _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pap _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (papp w@(pap-J _ _ _ _) q) = papp (⟹-⁺ w) (⟹-⁺ q)
⟹-⁺ (pfst w@(p⌜Hom⌝ _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(phrefl _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-base _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(p⌜Nat⌝)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(p⌜Unit⌝)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(p⌜Mu⌝)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@((p⌜IMu⌝ _))) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-Unit _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-Mu _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-IMu _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-Σ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-taut _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(phrefl-pw _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-Hom _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-pw _ _ _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(punit)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pnzero)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pnsuc _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pnatrec _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pnatrec-zero _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pnatrec-suc _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-Id _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(p⌜Id⌝ _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pidrefl _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pjsub _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pjsub-refl _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pap _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(pap-J _ _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (psnd w@(p⌜Hom⌝ _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(phrefl _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-base _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(p⌜Nat⌝)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(p⌜Unit⌝)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(p⌜Mu⌝)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@((p⌜IMu⌝ _))) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-Unit _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-Mu _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-IMu _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-Σ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-taut _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(phrefl-pw _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-Hom _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-pw _ _ _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(punit)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pnzero)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pnsuc _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pnatrec _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pnatrec-zero _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pnatrec-suc _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-Id _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(p⌜Id⌝ _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pidrefl _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pjsub _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pjsub-refl _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pap _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(pap-J _ _ _ _)) = psnd (⟹-⁺ w)
-- `⌜Hom⌝` — congruence only.
⟹-⁺ (p⌜Hom⌝ p q r)         = p⌜Hom⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
-- `hrefl` — W2b: dispatch on the pw-key via `hr-tri`.
⟹-⁺ (phrefl p q) = hr-tri _ (pw?-⟹ p) (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (phrefl-pw {C = C} {C'} {s = t} {t'} key pC pt) =
  subst (λ b → lam (hrefl (pwBody C') (app (renTm vs t') (var vz)))
               ⟹ hr⁺ b (C ⁺) (t ⁺))
        (sym key)
        (plam (phrefl (pwBody-⟹ (⟹-⁺ pC) (pw?-⟹ pC key))
                      (papp (⟹-ren vs (⟹-⁺ pt)) (pvar vz))))
-- the five `tr` roots.
⟹-⁺ (ptr-J-Unit p)  = ⟹-⁺ p
⟹-⁺ (ptr-J-Mu p)  = ⟹-⁺ p
⟹-⁺ (ptr-J-IMu p)  = ⟹-⁺ p
⟹-⁺ (ptr-J-base p)  = ⟹-⁺ p
⟹-⁺ (ptr-J-Σ p)     = ⟹-⁺ p
⟹-⁺ (ptr-J-Id p) = ⟹-⁺ p
⟹-⁺ (ptr-taut p q)  = papp (plam (⟹-⁺ p)) (⟹-⁺ q)
⟹-⁺ (ptr-J-Hom {c₁ = c₁} key pe) =
  subst (λ b → _ ⟹ trHK⁺ b _ _ _ c₁ _ _ _ _) (sym key) (⟹-⁺ pe)
⟹-⁺ (ptr-pw {c = c} {a = a} {f = f} {e = e} key pc pa pf pe) =
  subst (λ b → _ ⟹ trPK⁺ b c a f e) (sym key)
        (plam (ptr (p⌜Hom⌝ (⟹-ren pwShift
                             (pwBody-⟹ (⟹-⁺ pc) (pw?-⟹ pc key)))
                           (papp (⟹-ren vs (⟹-⁺ pa)) (pvar (vs vz)))
                           (pvar vz))
                   (⟹-⁺ pf)
                   (papp (⟹-ren vs (⟹-⁺ pe)) (pvar vz))))
-- `tr` congruence — mirroring `_⁺`'s tree: the path's derivation
-- discriminates first (J at the three stable stuck codes), then the
-- motive (taut at `var vz`, pointwise at the `⌜Π⌝`-ambient `⌜Hom⌝`).
-- J's stable codes — the MOTIVE discriminates too (J is
-- ⌜Hom⌝-motive-keyed): `p⌜Hom⌝` motives take the J leaf, everything
-- else is congruence (the redex does not exist there).
-- ★ stage C: NO J at a `p⌜Nat⌝` path.  `stkC? ⌜Nat⌝ = false` — `Hom Nat`
-- COMPUTES, so a `hrefl ⌜Nat⌝` does not pin its endpoints and J there is
-- unsound (see `stkC?`'s note in NbEPDirDBVar).  The motive case tree the
-- other codes need therefore collapses to ONE congruence clause.
⟹-⁺ (ptr pd w@(phrefl p⌜Nat⌝ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) (phrefl p⌜Unit⌝ ps) pe) = ptr-J-Unit (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) (phrefl p⌜Mu⌝ ps) pe) = ptr-J-Mu (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) (phrefl (p⌜IMu⌝ _) ps) pe) = ptr-J-IMu (⟹-⁺ pe)
⟹-⁺ (ptr u@(pvar _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pvar _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pvar _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Unit _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Mu _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Mu _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-IMu _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-IMu _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Unit⌝) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Mu⌝) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@((p⌜IMu⌝ _)) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) w@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) w@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) w@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) (phrefl p⌜base⌝ ps) pe) = ptr-J-base (⟹-⁺ pe)
⟹-⁺ (ptr u@(pvar _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Unit⌝) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Mu⌝) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@((p⌜IMu⌝ _)) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Unit _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Mu _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-IMu _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) w@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) (phrefl (p⌜Σ⌝ p₁ p₂) ps) pe) = ptr-J-Σ (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) (phrefl (p⌜Id⌝ p₁ p₂ p₃) ps) pe) = ptr-J-Id (⟹-⁺ pe)
⟹-⁺ (ptr u@(pvar _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pvar _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Unit⌝) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Mu⌝) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@((p⌜IMu⌝ _)) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Unit _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Mu _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-IMu _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Unit⌝) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Mu⌝) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@((p⌜IMu⌝ _)) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Unit _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Mu _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-IMu _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) w@(phrefl (p⌜Σ⌝ p₁ p₂) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
-- W2b: `⌜Hom⌝`-code paths — J-Hom at ⌜Hom⌝ motives (Boolean-dispatched
-- on `stkC?`), congruence elsewhere (the path piece re-dispatches on
-- the inner code's pw-key via `hr-tri`).
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) =
  trHK-tri _ (stkA?-⟹ pc₁) (pw?-⟹ pc₁)
           (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ pm)
           (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁) (⟹-⁺ ps) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pvar _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Unit⌝) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Mu⌝) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@((p⌜IMu⌝ _)) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Unit _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Mu _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-IMu _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) (phrefl (p⌜Hom⌝ pc₁ pa₁ pb₁) ps) pe) = ptr (⟹-⁺ u) (hr-tri _ (pw?-⟹ pc₁) (p⌜Hom⌝ (⟹-⁺ pc₁) (⟹-⁺ pa₁) (⟹-⁺ pb₁)) (⟹-⁺ ps)) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (p⌜Π⌝ _ _) _) pe) =
  ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
-- ★ stage D: nothing fires around ex falso.  As a MOTIVE it is neither
-- `var vz` (taut) nor a pw-able ⌜Hom⌝; as a PATH it is neither `lam`
-- nor `hrefl`; as a path CODE it is neither `pw?` nor `stkC?`.  All
-- four configurations are pure congruence.
⟹-⁺ (ptr w@(pabsurd _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
-- the other eliminators, likewise: `absurd` is not a canonical
-- scrutinee for any of them.
⟹-⁺ (pap pcB pb w@(pabsurd _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pabsurd _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pjsub pd w@(pabsurd _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pnatrec pz pw w@(pabsurd _ _)) = pnatrec (⟹-⁺ pz) (⟹-⁺ pw) (⟹-⁺ w)
-- …and with a J-able path code: the J rules all require a ⌜Hom⌝ MOTIVE,
-- which `absurd` is not, so these are congruence too.
⟹-⁺ (ptr w@(pabsurd _ _) v@(phrefl p⌜base⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pabsurd _ _) v@(phrefl p⌜Unit⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pabsurd _ _) v@(phrefl p⌜Mu⌝ _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pabsurd _ _) v@(phrefl (p⌜IMu⌝ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pabsurd _ _) v@(phrefl (p⌜Σ⌝ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pabsurd _ _) v@(phrefl (p⌜Id⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pabsurd _ _) v@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ _ _ (pabsurd _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pabsurd _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pabsurd _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pvar _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (plam _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (papp _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pβ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ppair _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pfst _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (psnd _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pβfst _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pβsnd _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (phrefl _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-J-base _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-J-Unit _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-J-Mu _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-J-IMu _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-J-Σ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-taut _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (phrefl-pw _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-J-Hom _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-pw _ _ _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (punit) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pnzero) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pnsuc _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pnatrec _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pnatrec-zero _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pnatrec-suc _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (ptr-J-Id _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pidrefl _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pjsub _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pjsub-refl _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pap _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (pap-J _ _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
-- W2b: the path itself fires `hrefl-pw` (a pw-able code — only ⌜Π⌝-
-- or ⌜Hom⌝-headed, by the key).  ⌜Π⌝ codes take the whole-term
-- congruence row; ⌜Hom⌝ codes go through `trH⁺`, where a ⌜Hom⌝ motive
-- needs the key rewritten by `pw⊥stk` (a pw code is never stk).
⟹-⁺ (ptr pd w@(phrefl-pw {C = ⌜Π⌝ _ _} _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa pm) w@(phrefl-pw {C = ⌜Hom⌝ c₁ a₁ b₁} key _ _) pe) =
  subst (λ b → _ ⟹ trHK⁺ b _ _ _ c₁ a₁ b₁ _ _) (sym (pw⊥stkA c₁ key))
        (ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ pm)) (⟹-⁺ w) (⟹-⁺ pe))
⟹-⁺ (ptr u@(pvar _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(plam _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(papp _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ppair _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pfst _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(psnd _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβfst _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pβsnd _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@p⌜base⌝ w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Π⌝ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Σ⌝ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(phrefl-pw _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Nat⌝) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pabsurd _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Unit⌝) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Mu⌝) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@((p⌜IMu⌝ _)) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Unit _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Mu _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-IMu _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Σ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Hom _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-taut _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-pw _ _ _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(punit) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnzero) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnsuc _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-zero _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pnatrec-suc _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(ptr-J-Id _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(p⌜Id⌝ _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pidrefl _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pjsub-refl _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr u@(pap-J _ _ _ _) w@(phrefl-pw {C = ⌜Hom⌝ _ _ _} _ _ _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (var _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (lam _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (app _ _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (pair _ _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (fst _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (snd _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = ⌜base⌝} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (⌜Σ⌝ _ _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (hrefl _ _)} () _ _) pe)
⟹-⁺ (ptr pd (phrefl-pw {C = (tr _ _ _)} () _ _) pe)
-- Path is a lambda — split the motive.
⟹-⁺ (ptr (pvar vz) (plam pf) pe)     = ptr-taut (⟹-⁺ pf) (⟹-⁺ pe)
-- W2b: a lam path at a ⌜Hom⌝ motive — pointwise transport fires iff
-- the endpoint is the LITERAL `var vz` and the code is pw-able.
⟹-⁺ (ptr (p⌜Hom⌝ pc pa (pvar vz)) (plam pf) pe) =
  trPK-tri _ (pw?-⟹ pc) (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ pf) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pvar (vs _))) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(plam _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(papp _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pβ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ppair _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pfst _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(psnd _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pβfst _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pβsnd _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@p⌜base⌝) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(p⌜Π⌝ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(p⌜Σ⌝ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(p⌜Hom⌝ _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(phrefl _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(phrefl-pw _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-J-base _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(p⌜Nat⌝)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(p⌜Unit⌝)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(p⌜Mu⌝)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@((p⌜IMu⌝ _))) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-J-Unit _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-J-Mu _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-J-IMu _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-J-Σ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-J-Hom _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-taut _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-pw _ _ _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(punit)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pnzero)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pnsuc _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pnatrec _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pnatrec-zero _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pnatrec-suc _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(ptr-J-Id _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(p⌜Id⌝ _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pidrefl _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pjsub _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pjsub-refl _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pap _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr (p⌜Hom⌝ pc pa u@(pap-J _ _ _ _)) v@(plam _) pe) = ptr (p⌜Hom⌝ (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ u)) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pvar (vs _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(plam _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(papp _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pβ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ppair _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pfst _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(psnd _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pβfst _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pβsnd _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜base⌝) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Π⌝ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Σ⌝ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(phrefl _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-J-base _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Nat⌝) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Unit⌝) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Mu⌝) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@((p⌜IMu⌝ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-J-Unit _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-J-Mu _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-J-IMu _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-J-Σ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-taut _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(phrefl-pw _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-J-Hom _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-pw _ _ _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(punit) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pnzero) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pnsuc _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pnatrec _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pnatrec-zero _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pnatrec-suc _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(ptr-J-Id _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Id⌝ _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pidrefl _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pjsub _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pjsub-refl _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pap _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pap-J _ _ _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
-- Path in any other shape — plain congruence.
⟹-⁺ (ptr pd w@(pvar _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(papp _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pβ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ppair _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pfst _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(psnd _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pβfst _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pβsnd _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜base⌝) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜Π⌝ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜Σ⌝ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜Hom⌝ _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-J-base _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜Nat⌝) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜Unit⌝) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜Mu⌝) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@((p⌜IMu⌝ _)) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-J-Unit _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-J-Mu _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-J-IMu _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-J-Σ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-taut _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-J-Hom _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-pw _ _ _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(punit) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pnzero) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pnsuc _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pnatrec _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pnatrec-zero _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pnatrec-suc _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(ptr-J-Id _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(p⌜Id⌝ _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pidrefl _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pjsub _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pjsub-refl _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pap _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(pap-J _ _ _ _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)

-- `ap` — mirroring `_⁺`'s tree: J at the three stable stuck path codes,
-- congruence elsewhere.  (`pap`/`pap-J`-rooted arguments inside OTHER
-- eliminators' congruence enumerations are appended to those blocks.)
-- ⚠ `pap-J` at ⌜Nat⌝ is ABSURD: its key is `stkC? c₁ ≡ true`, and
-- `stkC? ⌜Nat⌝ = false`.
⟹-⁺ (pap-J {c₁ = ⌜Nat⌝} () _ _ _)
⟹-⁺ (pap-J {c₁ = ⌜Unit⌝} key pcB pb ps) =
  phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb))
⟹-⁺ (pap-J {c₁ = ⌜Mu⌝ _} key pcB pb ps) =
  phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb))
⟹-⁺ (pap-J {c₁ = ⌜IMu⌝ _ _ _} key pcB pb ps) =
  phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb))
⟹-⁺ (pap-J {c₁ = ⌜base⌝} key pcB pb ps) =
  phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb))
⟹-⁺ (pap-J {c₁ = ⌜Σ⌝ _ _} key pcB pb ps) =
  phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb))
⟹-⁺ (pap-J {c₁ = ⌜Id⌝ _ _ _} key pcB pb ps) =
  phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb))
⟹-⁺ (pap-J {c₁ = ⌜Hom⌝ c₁ a₁ b₁} key pcB pb ps) =
  subst (λ k → _ ⟹ apH⁺ k _ _ c₁ a₁ b₁ _) (sym key)
        (phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb)))
⟹-⁺ (pap-J {c₁ = var _} () _ _ _)
⟹-⁺ (pap-J {c₁ = lam _} () _ _ _)
⟹-⁺ (pap-J {c₁ = app _ _} () _ _ _)
⟹-⁺ (pap-J {c₁ = pair _ _} () _ _ _)
⟹-⁺ (pap-J {c₁ = fst _} () _ _ _)
⟹-⁺ (pap-J {c₁ = snd _} () _ _ _)
⟹-⁺ (pap-J {c₁ = ⌜Π⌝ _ _} () _ _ _)
⟹-⁺ (pap-J {c₁ = hrefl _ _} () _ _ _)
⟹-⁺ (pap-J {c₁ = tr _ _ _} () _ _ _)
⟹-⁺ (pap-J {c₁ = ap _ _ _} () _ _ _)
⟹-⁺ (pap-J {c₁ = idrefl _ _} () _ _ _)
⟹-⁺ (pap-J {c₁ = jsub _ _ _} () _ _ _)
-- congruence: path-derivation roots whose SOURCE is not an hrefl.
⟹-⁺ (pap pcB pb w@(pvar _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(plam _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(papp _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pβ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ppair _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pfst _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(psnd _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pβfst _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pβsnd _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@p⌜base⌝) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(p⌜Π⌝ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(p⌜Σ⌝ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(p⌜Hom⌝ _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-J-base _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(p⌜Nat⌝)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(p⌜Unit⌝)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(p⌜Mu⌝)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@((p⌜IMu⌝ _))) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-J-Unit _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-J-Mu _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-J-IMu _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-J-Σ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-taut _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-J-Hom _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-pw _ _ _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(punit)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pnzero)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pnsuc _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pnatrec _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pnatrec-zero _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pnatrec-suc _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(ptr-J-Id _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(p⌜Id⌝ _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pidrefl _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pjsub _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pjsub-refl _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pap _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(pap-J _ _ _ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
-- hrefl paths: the CODE's derivation root decides the ⁺-branch.
-- ⚠ ⌜Nat⌝ is NOT `stkC?`, so `ap-J` does not fire here either — same
-- reason, same key.  Congruence.
⟹-⁺ (pap pcB pb w@(phrefl p⌜Nat⌝ _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb (phrefl p⌜Unit⌝ ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl p⌜Mu⌝ ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl (p⌜IMu⌝ _) ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl p⌜base⌝ ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl (p⌜Σ⌝ _ _) ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl (p⌜Id⌝ _ _ _) ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl (p⌜Hom⌝ pc pa pz) ps)) =
  apH-tri _ (stkA?-⟹ pc) (pw?-⟹ pc)
          (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ pc) (⟹-⁺ pa) (⟹-⁺ pz) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb w@(phrefl (pvar _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (plam _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (papp _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pβ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ppair _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pfst _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (psnd _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pβfst _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pβsnd _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (p⌜Π⌝ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (phrefl _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (phrefl-pw _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-J-base _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-J-Unit _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-J-Mu _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-J-IMu _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-J-Σ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-taut _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-J-Hom _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-pw _ _ _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (punit) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pnzero) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pnsuc _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pnatrec _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pnatrec-zero _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pnatrec-suc _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (ptr-J-Id _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pidrefl _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pjsub _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pjsub-refl _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pap _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl (pap-J _ _ _ _) _)) = pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
-- pw-unfolding paths: ⌜Π⌝ codes take the congruence row; ⌜Hom⌝ codes
-- go through `apH⁺` with the key rewritten by `pw⊥stk`.
⟹-⁺ (pap pcB pb w@(phrefl-pw {C = ⌜Π⌝ _ _} _ _ _)) =
  pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w)
⟹-⁺ (pap pcB pb w@(phrefl-pw {C = ⌜Hom⌝ c₁ a₁ b₁} key _ _)) =
  subst (λ k → _ ⟹ apH⁺ k _ _ c₁ a₁ b₁ _) (sym (pw⊥stkA c₁ key))
        (pap (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ w))
-- `jsub` — the UNKEYED J: idrefl-sourced paths fire unconditionally,
-- everything else is congruence.
⟹-⁺ (pjsub-refl p) = ⟹-⁺ p
⟹-⁺ (pjsub pd (pidrefl pc ps) pe) = pjsub-refl (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pvar _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(plam _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(papp _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pβ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ppair _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pfst _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(psnd _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pβfst _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pβsnd _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@p⌜base⌝ pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(p⌜Π⌝ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(p⌜Σ⌝ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(p⌜Hom⌝ _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(p⌜Id⌝ _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(phrefl _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(phrefl-pw _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-J-base _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(p⌜Nat⌝) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(p⌜Unit⌝) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(p⌜Mu⌝) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@((p⌜IMu⌝ _)) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-J-Unit _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-J-Mu _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-J-IMu _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-J-Σ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-taut _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-J-Hom _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-pw _ _ _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(punit) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pnzero) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pnsuc _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pnatrec _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pnatrec-zero _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pnatrec-suc _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(ptr-J-Id _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pap _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pap-J _ _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pjsub _ _ _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
⟹-⁺ (pjsub pd w@(pjsub-refl _) pe) = pjsub (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
-- `⌜Id⌝` / `idrefl` — congruence only.
⟹-⁺ (p⌜Id⌝ p q r) = p⌜Id⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
⟹-⁺ (pidrefl p q) = pidrefl (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ {t = app (con x t) t₁} (papp w1@(pcon x₁) x₂) =
  papp (⟹-⁺ w1) (⟹-⁺ x₂)
⟹-⁺ {t = app (elim x t t₁) t₂} (papp w1@(pelim x₁ x₂) x₃) =
  papp (⟹-⁺ w1) (⟹-⁺ x₃)
⟹-⁺ {t = app (elim x t (con k p)) t₁} (papp w1@(pι x₁ x₂) x₃) =
  papp (⟹-⁺ w1) (⟹-⁺ x₃)
⟹-⁺ {t = app (icon x t) t₁} (papp w1@(picon x₁) x₂) =
  papp (⟹-⁺ w1) (⟹-⁺ x₂)
⟹-⁺ {t = app (⌜IMu⌝ x x₁ t) t₂} (papp w1@(p⌜IMu⌝ x₂) x₃) =
  papp (⟹-⁺ w1) (⟹-⁺ x₃)
⟹-⁺ {t = app (ielim x t t₁ t₂) t₃} (papp w1@(pielim x₁ x₂ x₃) x₄) =
  papp (⟹-⁺ w1) (⟹-⁺ x₄)
⟹-⁺ {t = app (ielim x t t₁ (icon k p)) t₂} (papp w1@(pιi x₁ x₂ x₃) x₄) =
  papp (⟹-⁺ w1) (⟹-⁺ x₄)
⟹-⁺ {t = ordtr (nsuc t) (con x t₁) nzero t₂ t₃} (pordtr w1@(pnsuc x₁) w2@(pcon x₂) w3@pnzero x₃ x₄) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₃) (⟹-⁺ x₄)
⟹-⁺ {t = ordtr (nsuc t) (elim x t₁ t₂) nzero t₃ t₄} (pordtr w1@(pnsuc x₁) w2@(pelim x₂ x₃) w3@pnzero x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (nsuc t) (elim x t₁ (con k p)) nzero t₂ t₃} (pordtr w1@(pnsuc x₁) w2@(pι x₂ x₃) w3@pnzero x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (nsuc t) (icon x t₁) nzero t₂ t₃} (pordtr w1@(pnsuc x₁) w2@(picon x₂) w3@pnzero x₃ x₄) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₃) (⟹-⁺ x₄)
⟹-⁺ {t = ordtr (nsuc t) (⌜IMu⌝ x x₁ t₁) nzero t₂ t₃} (pordtr w1@(pnsuc x₂) w2@(p⌜IMu⌝ x₃) w3@pnzero x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (nsuc t) (ielim x t₁ t₂ t₃) nzero t₄ t₅} (pordtr w1@(pnsuc x₁) w2@(pielim x₂ x₃ x₄) w3@pnzero x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (nsuc t) (ielim x t₁ t₂ (icon k p)) nzero t₃ t₄} (pordtr w1@(pnsuc x₁) w2@(pιi x₂ x₃ x₄) w3@pnzero x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (nsuc t) (con x t₁) (nsuc t₂) t₃ t₄} (pordtr w1@(pnsuc x₁) w2@(pcon x₂) w3@(pnsuc x₃) x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (nsuc t) (elim x t₁ t₂) (nsuc t₃) t₄ t₅} (pordtr w1@(pnsuc x₁) w2@(pelim x₂ x₃) w3@(pnsuc x₄) x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (nsuc t) (elim x t₁ (con k p)) (nsuc t₂) t₃ t₄} (pordtr w1@(pnsuc x₁) w2@(pι x₂ x₃) w3@(pnsuc x₄) x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (nsuc t) (icon x t₁) (nsuc t₆) t₂ t₃} (pordtr w1@(pnsuc x₁) w2@(picon x₂) w3@(pnsuc x₇) x₃ x₄) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₃) (⟹-⁺ x₄)
⟹-⁺ {t = ordtr (nsuc t) (⌜IMu⌝ x x₁ t₁) (nsuc t₆) t₂ t₃} (pordtr w1@(pnsuc x₂) w2@(p⌜IMu⌝ x₃) w3@(pnsuc x₇) x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (nsuc t) (ielim x t₁ t₂ t₃) (nsuc t₆) t₄ t₅} (pordtr w1@(pnsuc x₁) w2@(pielim x₂ x₃ x₄) w3@(pnsuc x₇) x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (nsuc t) (ielim x t₁ t₂ (icon k p)) (nsuc t₆) t₃ t₄} (pordtr w1@(pnsuc x₁) w2@(pιi x₂ x₃ x₄) w3@(pnsuc x₇) x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ w3) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (nsuc t) t₁ (con x t₂) t₃ t₄} (pordtr w1@(pnsuc x₁) x₂ w2@(pcon x₃) x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ w2) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (nsuc t) t₁ (elim x t₂ t₃) t₄ t₅} (pordtr w1@(pnsuc x₁) x₂ w2@(pelim x₃ x₄) x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ w2) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (nsuc t) t₁ (elim x t₂ (con k p)) t₃ t₄} (pordtr w1@(pnsuc x₁) x₂ w2@(pι x₃ x₄) x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ w2) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (con x t) t₁ t₂ t₃ t₄} (pordtr w1@(pcon x₁) x₂ x₃ x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ x₃) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (elim x t t₁) t₂ t₃ t₄ t₅} (pordtr w1@(pelim x₁ x₂) x₃ x₄ x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₃) (⟹-⁺ x₄) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (elim x t (con k p)) t₁ t₂ t₃ t₄} (pordtr w1@(pι x₁ x₂) x₃ x₄ x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₃) (⟹-⁺ x₄) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = fst (con x t)} (pfst w1@(pcon x₁)) =
  pfst (⟹-⁺ w1)
⟹-⁺ {t = fst (elim x t t₁)} (pfst w1@(pelim x₁ x₂)) =
  pfst (⟹-⁺ w1)
⟹-⁺ {t = fst (elim x t (con k p))} (pfst w1@(pι x₁ x₂)) =
  pfst (⟹-⁺ w1)
⟹-⁺ {t = snd (con x t)} (psnd w1@(pcon x₁)) =
  psnd (⟹-⁺ w1)
⟹-⁺ {t = snd (elim x t t₁)} (psnd w1@(pelim x₁ x₂)) =
  psnd (⟹-⁺ w1)
⟹-⁺ {t = snd (elim x t (con k p))} (psnd w1@(pι x₁ x₂)) =
  psnd (⟹-⁺ w1)
⟹-⁺ {t = tr (⌜Hom⌝ c a (con k p)) (lam t) t₁} (ptr w1@(p⌜Hom⌝ x x₁ (pcon x₂)) w2@(plam x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜Hom⌝ c a (elim D ms t)) (lam t₁) t₂} (ptr w1@(p⌜Hom⌝ x x₁ (pelim x₂ x₃)) w2@(plam x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜Hom⌝ c a (elim D ms (con k p))) (lam t) t₁} (ptr w1@(p⌜Hom⌝ x x₁ (pι x₂ x₃)) w2@(plam x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (con k p) (lam t) t₁} (ptr w1@(pcon x) w2@(plam x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (elim D ms t) (lam t₁) t₂} (ptr w1@(pelim x x₁) w2@(plam x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (elim D ms (con k p)) (lam t) t₁} (ptr w1@(pι x x₁) w2@(plam x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (var x) (hrefl (con x₁ t) t₁) t₂} (ptr w1@(pvar x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (var x) (hrefl (elim x₁ t t₁) t₂) t₃} (ptr w1@(pvar x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (var x) (hrefl (elim x₁ t (con k p)) t₁) t₂} (ptr w1@(pvar x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (lam t) (hrefl (con x t₁) t₂) t₃} (ptr w1@(plam x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (lam t) (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@(plam x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (lam t) (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@(plam x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (app t u) (hrefl (con x t₁) t₂) t₃} (ptr w1@(papp x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (app t u) (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@(papp x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (app t u) (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@(papp x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (app (lam t) u) (hrefl (con x t₁) t₂) t₃} (ptr w1@(pβ x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (app (lam t) u) (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@(pβ x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (app (lam t) u) (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@(pβ x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (pair a b) (hrefl (con x t) t₁) t₂} (ptr w1@(ppair x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (pair a b) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ppair x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (pair a b) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ppair x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (absurd c e) (hrefl (con x t) t₁) t₂} (ptr w1@(pabsurd x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (absurd c e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pabsurd x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (absurd c e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pabsurd x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ordtr a t u p q) (hrefl (con k p₁) t₁) t₂} (ptr w1@(pordtr x x₁ x₂ x₃ x₄) w2@(phrefl (pcon x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr a t u p q) (hrefl (elim D ms t₁) t₂) t₃} (ptr w1@(pordtr x x₁ x₂ x₃ x₄) w2@(phrefl (pelim x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ordtr a t u p q) (hrefl (elim D ms (con k p₁)) t₁) t₂} (ptr w1@(pordtr x x₁ x₂ x₃ x₄) w2@(phrefl (pι x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ordtr .nzero t u p q) (hrefl (con k p₁) t₁) t₂} (ptr w1@pordtr-z w2@(phrefl (pcon x) x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (ordtr .nzero t u p q) (hrefl (elim D ms t₁) t₂) t₃} (ptr w1@pordtr-z w2@(phrefl (pelim x x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr .nzero t u p q) (hrefl (elim D ms (con k p₁)) t₁) t₂} (ptr w1@pordtr-z w2@(phrefl (pι x x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero .nzero p q) (hrefl (con k p₁) t) t₁} (ptr w1@(pordtr-szz x) w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero .nzero p q) (hrefl (elim D ms t) t₁) t₂} (ptr w1@(pordtr-szz x) w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero .nzero p q) (hrefl (elim D ms (con k p₁)) t) t₁} (ptr w1@(pordtr-szz x) w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) .nzero p q) (hrefl (con k p₁) t₁) t₂} (ptr w1@(pordtr-ssz x) w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) .nzero p q) (hrefl (elim D ms t₁) t₂) t₃} (ptr w1@(pordtr-ssz x) w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) .nzero p q) (hrefl (elim D ms (con k p₁)) t₁) t₂} (ptr w1@(pordtr-ssz x) w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero (nsuc u) p q) (hrefl (con k p₁) t) t₁} (ptr w1@(pordtr-szs x x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero (nsuc u) p q) (hrefl (elim D ms t) t₁) t₂} (ptr w1@(pordtr-szs x x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero (nsuc u) p q) (hrefl (elim D ms (con k p₁)) t) t₁} (ptr w1@(pordtr-szs x x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) (nsuc u) p q) (hrefl (con k p₁) t₁) t₂} (ptr w1@(pordtr-sss x x₁ x₂ x₃ x₄) w2@(phrefl (pcon x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) (nsuc u) p q) (hrefl (elim D ms t₁) t₂) t₃} (ptr w1@(pordtr-sss x x₁ x₂ x₃ x₄) w2@(phrefl (pelim x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) (nsuc u) p q) (hrefl (elim D ms (con k p₁)) t₁) t₂} (ptr w1@(pordtr-sss x x₁ x₂ x₃ x₄) w2@(phrefl (pι x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (fst p) (hrefl (con x t) t₁) t₂} (ptr w1@(pfst x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (fst p) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pfst x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (fst p) (hrefl (elim x t (con k p₁)) t₁) t₂} (ptr w1@(pfst x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (snd p) (hrefl (con x t) t₁) t₂} (ptr w1@(psnd x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (snd p) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(psnd x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (snd p) (hrefl (elim x t (con k p₁)) t₁) t₂} (ptr w1@(psnd x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (fst (pair a b)) (hrefl (con x t) t₁) t₂} (ptr w1@(pβfst x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (fst (pair a b)) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pβfst x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (fst (pair a b)) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pβfst x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (snd (pair a b)) (hrefl (con x t) t₁) t₂} (ptr w1@(pβsnd x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (snd (pair a b)) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pβsnd x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (snd (pair a b)) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pβsnd x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr t (hrefl (con x t₁) t₂) t₃} (ptr w1@p⌜base⌝ w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@p⌜base⌝ w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@p⌜base⌝ w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜Π⌝ c d) (hrefl (con x t) t₁) t₂} (ptr w1@(p⌜Π⌝ x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜Π⌝ c d) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(p⌜Π⌝ x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Π⌝ c d) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(p⌜Π⌝ x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Σ⌝ c d) (hrefl (con x t) t₁) t₂} (ptr w1@(p⌜Σ⌝ x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜Σ⌝ c d) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(p⌜Σ⌝ x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Σ⌝ c d) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(p⌜Σ⌝ x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Hom⌝ c a b) (hrefl (con x t) t₁) t₂} (ptr w1@(p⌜Hom⌝ x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Hom⌝ c a b) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(p⌜Hom⌝ x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (⌜Hom⌝ c a b) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(p⌜Hom⌝ x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (hrefl c t) (hrefl (con x t₁) t₂) t₃} (ptr w1@(phrefl x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (hrefl c t) (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@(phrefl x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (hrefl c t) (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@(phrefl x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr d p e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr d p e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr d p e) (hrefl (elim x t (con k p₁)) t₁) t₂} (ptr w1@(ptr x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜base⌝ s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-J-base x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜base⌝ s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-J-base x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜base⌝ s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-J-base x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (con x t₁) t₂) t₃} (ptr w1@p⌜Nat⌝ w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@p⌜Nat⌝ w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@p⌜Nat⌝ w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (con x t₁) t₂) t₃} (ptr w1@p⌜Unit⌝ w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (con x t₁) t₂) t₃} (ptr w1@p⌜Mu⌝ w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@p⌜Unit⌝ w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@p⌜Mu⌝ w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@p⌜Unit⌝ w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
-- ★ the CROSS cases: a `⌜Unit⌝` motive with a `⌜Mu⌝` path code and vice
--   versa.  A per-code mirror cannot produce these — it rewrites every
--   occurrence in a clause at once — and no J rule fires at either, since
--   J needs a ⌜Hom⌝ MOTIVE.  So all four are the generic congruence.
⟹-⁺ (ptr w1@p⌜Unit⌝ w2@(phrefl p⌜Mu⌝ x) x₁) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₁)
⟹-⁺ (ptr w1@p⌜Unit⌝ w2@(phrefl (p⌜IMu⌝ _) x) x₁) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₁)
⟹-⁺ (ptr w1@p⌜Mu⌝ w2@(phrefl p⌜Unit⌝ x) x₁) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₁)
⟹-⁺ (ptr w1@(p⌜IMu⌝ _) w2@(phrefl p⌜Unit⌝ x) x₁) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₁)
⟹-⁺ (ptr w1@(ptr-J-Unit x) w2@(phrefl p⌜Mu⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ (ptr w1@(ptr-J-Unit x) w2@(phrefl (p⌜IMu⌝ _) x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ (ptr w1@(ptr-J-Mu x) w2@(phrefl p⌜Unit⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ (ptr w1@(ptr-J-IMu x) w2@(phrefl p⌜Unit⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr t (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@p⌜Mu⌝ w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜Unit⌝ s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-J-Unit x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .(⌜Mu⌝ _) s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-J-Mu x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .(⌜IMu⌝ _ _ _) s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-J-IMu x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜Unit⌝ s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-J-Unit x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .(⌜Mu⌝ _) s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-J-Mu x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .(⌜IMu⌝ _ _ _) s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-J-IMu x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜Unit⌝ s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-J-Unit x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .(⌜Mu⌝ _) s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-J-Mu x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .(⌜IMu⌝ _ _ _) s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-J-IMu x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-J-Σ x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-J-Σ x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-J-Σ x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-J-Id x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-J-Id x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-J-Id x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr .(var vz) (lam f) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-taut x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr .(var vz) (lam f) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-taut x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr .(var vz) (lam f) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-taut x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (hrefl C s) (hrefl (con x t) t₁) t₂} (ptr w1@(phrefl-pw x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (hrefl C s) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(phrefl-pw x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (hrefl C s) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(phrefl-pw x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-J-Hom x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-J-Hom x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-J-Hom x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a .(var vz)) (lam f) e) (hrefl (con x t) t₁) t₂} (ptr w1@(ptr-pw x₁ x₂ x₃ x₄ x₅) w2@(phrefl (pcon x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a .(var vz)) (lam f) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(ptr-pw x₁ x₂ x₃ x₄ x₅) w2@(phrefl (pelim x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a .(var vz)) (lam f) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(ptr-pw x₁ x₂ x₃ x₄ x₅) w2@(phrefl (pι x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (ap cB b p) (hrefl (con x t) t₁) t₂} (ptr w1@(pap x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ap cB b p) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pap x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ap cB b p) (hrefl (elim x t (con k p₁)) t₁) t₂} (ptr w1@(pap x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ap cB b (hrefl c₁ s)) (hrefl (con x t) t₁) t₂} (ptr w1@(pap-J x₁ x₂ x₃ x₄) w2@(phrefl (pcon x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ap cB b (hrefl c₁ s)) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pap-J x₁ x₂ x₃ x₄) w2@(phrefl (pelim x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ap cB b (hrefl c₁ s)) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pap-J x₁ x₂ x₃ x₄) w2@(phrefl (pι x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (⌜Id⌝ c a b) (hrefl (con x t) t₁) t₂} (ptr w1@(p⌜Id⌝ x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Id⌝ c a b) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(p⌜Id⌝ x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (⌜Id⌝ c a b) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(p⌜Id⌝ x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (idrefl c t) (hrefl (con x t₁) t₂) t₃} (ptr w1@(pidrefl x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (idrefl c t) (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@(pidrefl x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (idrefl c t) (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@(pidrefl x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (jsub d p e) (hrefl (con x t) t₁) t₂} (ptr w1@(pjsub x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (jsub d p e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pjsub x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (jsub d p e) (hrefl (elim x t (con k p₁)) t₁) t₂} (ptr w1@(pjsub x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (jsub d (idrefl c s) e) (hrefl (con x t) t₁) t₂} (ptr w1@(pjsub-refl x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (jsub d (idrefl c s) e) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pjsub-refl x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (jsub d (idrefl c s) e) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pjsub-refl x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (con x t₁) t₂) t₃} (ptr w1@punit w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@punit w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@punit w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (con x t₁) t₂) t₃} (ptr w1@pnzero w2@(phrefl (pcon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@pnzero w2@(phrefl (pelim x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@pnzero w2@(phrefl (pι x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (nsuc n) (hrefl (con x t) t₁) t₂} (ptr w1@(pnsuc x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (nsuc n) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pnsuc x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (nsuc n) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pnsuc x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (natrec z s n) (hrefl (con x t) t₁) t₂} (ptr w1@(pnatrec x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (natrec z s n) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pnatrec x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (natrec z s n) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pnatrec x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (natrec z s .nzero) (hrefl (con x t) t₁) t₂} (ptr w1@(pnatrec-zero x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (natrec z s .nzero) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pnatrec-zero x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (natrec z s .nzero) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pnatrec-zero x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (natrec z s (nsuc n)) (hrefl (con x t) t₁) t₂} (ptr w1@(pnatrec-suc x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (natrec z s (nsuc n)) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pnatrec-suc x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (natrec z s (nsuc n)) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(pnatrec-suc x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (con k p) (hrefl ⌜base⌝ t) t₁} (ptr w1@(pcon x) w2@(phrefl p⌜base⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (con k p) (hrefl (⌜Σ⌝ t t₁) t₂) t₃} (ptr w1@(pcon x) w2@(phrefl (p⌜Σ⌝ x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (con k p) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pcon x) w2@(phrefl (p⌜Hom⌝ x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (con k p) (hrefl (⌜Id⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pcon x) w2@(phrefl (p⌜Id⌝ x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (con k p) (hrefl (con x t) t₁) t₂} (ptr w1@(pcon x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (con k p) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pcon x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (con k p) (hrefl (elim x t (con k₁ p₁)) t₁) t₂} (ptr w1@(pcon x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (con k p) (hrefl ⌜Unit⌝ t) t₁} (ptr w1@(pcon x) w2@(phrefl p⌜Unit⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (con k p) (hrefl (⌜Mu⌝ Dᵐ) t) t₁} (ptr w1@(pcon x) w2@(phrefl p⌜Mu⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (con k p) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pcon x) w2@(phrefl-pw x₁ x₂ x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (elim D ms t) (hrefl ⌜base⌝ t₁) t₂} (ptr w1@(pelim x x₁) w2@(phrefl p⌜base⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (elim D ms t) (hrefl (⌜Σ⌝ t₁ t₂) t₃) t₄} (ptr w1@(pelim x x₁) w2@(phrefl (p⌜Σ⌝ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms t) (hrefl (⌜Hom⌝ t₁ t₂ t₃) t₄) t₅} (ptr w1@(pelim x x₁) w2@(phrefl (p⌜Hom⌝ x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms t) (hrefl (⌜Id⌝ t₁ t₂ t₃) t₄) t₅} (ptr w1@(pelim x x₁) w2@(phrefl (p⌜Id⌝ x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms t) (hrefl (con x t₁) t₂) t₃} (ptr w1@(pelim x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms t) (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@(pelim x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms t) (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@(pelim x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms t) (hrefl ⌜Unit⌝ t₁) t₂} (ptr w1@(pelim x x₁) w2@(phrefl p⌜Unit⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (elim D ms t) (hrefl (⌜Mu⌝ Dᵐ) t₁) t₂} (ptr w1@(pelim x x₁) w2@(phrefl p⌜Mu⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (elim D ms t) (hrefl (⌜Hom⌝ t₁ t₂ t₃) t₄) t₅} (ptr w1@(pelim x x₁) w2@(phrefl-pw x₂ x₃ x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl ⌜base⌝ t) t₁} (ptr w1@(pι x x₁) w2@(phrefl p⌜base⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (⌜Σ⌝ t t₁) t₂) t₃} (ptr w1@(pι x x₁) w2@(phrefl (p⌜Σ⌝ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pι x x₁) w2@(phrefl (p⌜Hom⌝ x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (⌜Id⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pι x x₁) w2@(phrefl (p⌜Id⌝ x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (con x t) t₁) t₂} (ptr w1@(pι x₁ x₂) w2@(phrefl (pcon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pι x₁ x₂) w2@(phrefl (pelim x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (elim x t (con k₁ p₁)) t₁) t₂} (ptr w1@(pι x₁ x₂) w2@(phrefl (pι x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl ⌜Unit⌝ t) t₁} (ptr w1@(pι x x₁) w2@(phrefl p⌜Unit⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (⌜Mu⌝ Dᵐ) t) t₁} (ptr w1@(pι x x₁) w2@(phrefl p⌜Mu⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pι x x₁) w2@(phrefl-pw x₂ x₃ x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (con x t₁) t₂} (ptr x₁ w1@(pcon x₂) x₃) =
  ptr (⟹-⁺ x₁) (⟹-⁺ w1) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (elim x t₁ t₂) t₃} (ptr x₁ w1@(pelim x₂ x₃) x₄) =
  ptr (⟹-⁺ x₁) (⟹-⁺ w1) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (elim x t₁ (con k p)) t₂} (ptr x₁ w1@(pι x₂ x₃) x₄) =
  ptr (⟹-⁺ x₁) (⟹-⁺ w1) (⟹-⁺ x₄)
⟹-⁺ {t = ap t t₁ (hrefl (con x t₂) t₃)} (pap x₁ x₂ w1@(phrefl (pcon x₃) x₄)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = ap t t₁ (hrefl (elim x t₂ t₃) t₄)} (pap x₁ x₂ w1@(phrefl (pelim x₃ x₄) x₅)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = ap t t₁ (hrefl (elim x t₂ (con k p)) t₃)} (pap x₁ x₂ w1@(phrefl (pι x₃ x₄) x₅)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = ap t t₁ (con x t₂)} (pap x₁ x₂ w1@(pcon x₃)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = ap t t₁ (elim x t₂ t₃)} (pap x₁ x₂ w1@(pelim x₃ x₄)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = ap t t₁ (elim x t₂ (con k p))} (pap x₁ x₂ w1@(pι x₃ x₄)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = jsub t (con x t₁) t₂} (pjsub x₁ w1@(pcon x₂) x₃) =
  pjsub (⟹-⁺ x₁) (⟹-⁺ w1) (⟹-⁺ x₃)
⟹-⁺ {t = jsub t (elim x t₁ t₂) t₃} (pjsub x₁ w1@(pelim x₂ x₃) x₄) =
  pjsub (⟹-⁺ x₁) (⟹-⁺ w1) (⟹-⁺ x₄)
⟹-⁺ {t = jsub t (elim x t₁ (con k p)) t₂} (pjsub x₁ w1@(pι x₂ x₃) x₄) =
  pjsub (⟹-⁺ x₁) (⟹-⁺ w1) (⟹-⁺ x₄)
⟹-⁺ {t = natrec t t₁ (con x t₂)} (pnatrec x₁ x₂ w1@(pcon x₃)) =
  pnatrec (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = natrec t t₁ (elim x t₂ t₃)} (pnatrec x₁ x₂ w1@(pelim x₃ x₄)) =
  pnatrec (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)
⟹-⁺ {t = natrec t t₁ (elim x t₂ (con k p))} (pnatrec x₁ x₂ w1@(pι x₃ x₄)) =
  pnatrec (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w1)

------------------------------------------------------------------------
-- ★ INDUCTIVE TYPES — the triangle's three new rows.
--
-- ⚠ `pelim` SPLITS ON THE SCRUTINEE'S TERM SHAPE, not on its derivation.
--   `_⁺` distinguishes only `con` from everything else, so one clause per
--   RTm former (26) suffices where a split on `_⟹_`'s constructors would
--   have cost ~60.  `pnatrec` above could not use the trick: its `_⁺` keys
--   on TWO numeral heads, so the split has to see both.
------------------------------------------------------------------------
⟹-⁺ (pcon pp) = pcon (⟹-⁺ pp)
-- the ι root: `fields`/`sel` are metalevel, so the development runs
-- through their congruence LEMMAS rather than a constructor.
⟹-⁺ (pι {D = D} {k = k} pms pp) =
  p-fields (lookupD D k) (⟹-⁺ pms) (p-sel k (⟹-⁺ pms)) (⟹-⁺ pp)
-- ★ the one that fires: a `con` scrutinee turns congruence into the root.
⟹-⁺ (pelim {t = con k c} pms (pcon pp)) = pι (⟹-⁺ pms) (⟹-⁺ pp)
⟹-⁺ (pelim {t = (var x)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (lam t)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (app f a)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (pair a b)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (absurd c e)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (ordtr a t u p q)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (fst p)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (snd p)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = ⌜base⌝} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (⌜Π⌝ c d)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (⌜Σ⌝ c d)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (⌜Hom⌝ c a b)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (hrefl c t)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (tr d p e)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (ap c b p)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (⌜Id⌝ c a b)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (idrefl c t)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (jsub d p e)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = unit} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = nzero} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (nsuc n)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (natrec z s w)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = ⌜Nat⌝} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = ⌜Unit⌝} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = ⌜Mu⌝ _} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pelim {t = (elim D₁ ms₁ t₁)} pms pt) = pelim (⟹-⁺ pms) (⟹-⁺ pt)

-- ★★ THE TRIANGLE PROPERTY FOR THE INDEXED FORMERS — 241 cells.
--
-- ⚠ GENERATED FROM AGDA'S OWN MISSING-CASE OUTPUT, not hand-written: the
--   new formers multiply into every argument position of `ordtr`, `fst`,
--   `snd`, `tr` and `hrefl`, and the existing con/elim grid is 210 cells.
--   Every RHS has the SAME shape — the outer congruence applied to `⟹-⁺`
--   of each argument — which is why generating them is safe: there is no
--   per-case reasoning to get wrong, only bookkeeping to get exhaustive.
--   ⭐ The one case with CONTENT is `_⁺`'s head clause for `ielim`, which
--     FIRES the ι-redex; that is what makes `_⁺` the COMPLETE development.

⟹-⁺ {t = ordtr (nsuc t) t₁ (icon x t₂) t₃ t₄} (pordtr w1@(pnsuc x₁) x₂ w3@(picon x₃) x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ w3) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (nsuc t) t₁ (ielim x t₂ t₃ t₄) t₅ t₆} (pordtr w1@(pnsuc x₁) x₂ w3@(pielim x₃ x₄ x₅) x₆ x₇) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ w3) (⟹-⁺ x₆) (⟹-⁺ x₇)
⟹-⁺ {t = ordtr (nsuc t) t₁ (ielim x t₂ t₃ (icon k p)) t₄ t₅} (pordtr w1@(pnsuc x₁) x₂ w3@(pιi x₃ x₄ x₅) x₆ x₇) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ w3) (⟹-⁺ x₆) (⟹-⁺ x₇)
⟹-⁺ {t = ordtr (nsuc t) t₁ (⌜IMu⌝ x x₁ t₂) t₃ t₄} (pordtr w1@(pnsuc x₂) x₃ w3@(p⌜IMu⌝ x₄) x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₃) (⟹-⁺ w3) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = ordtr (icon x t) t₁ t₂ t₃ t₄} (pordtr w1@(picon x₁) x₂ x₃ x₄ x₅) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₂) (⟹-⁺ x₃) (⟹-⁺ x₄) (⟹-⁺ x₅)
⟹-⁺ {t = ordtr (ielim x t t₁ t₂) t₃ t₄ t₅ t₆} (pordtr w1@(pielim x₁ x₂ x₃) x₄ x₅ x₆ x₇) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₄) (⟹-⁺ x₅) (⟹-⁺ x₆) (⟹-⁺ x₇)
⟹-⁺ {t = ordtr (ielim x t t₁ (icon k p)) t₂ t₃ t₄ t₅} (pordtr w1@(pιi x₁ x₂ x₃) x₄ x₅ x₆ x₇) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₄) (⟹-⁺ x₅) (⟹-⁺ x₆) (⟹-⁺ x₇)
⟹-⁺ {t = ordtr (⌜IMu⌝ x x₁ t) t₁ t₂ t₃ t₄} (pordtr w1@(p⌜IMu⌝ x₂) x₃ x₄ x₅ x₆) =
  pordtr (⟹-⁺ w1) (⟹-⁺ x₃) (⟹-⁺ x₄) (⟹-⁺ x₅) (⟹-⁺ x₆)
⟹-⁺ {t = fst (icon x t)} (pfst w1@(picon x₁)) =
  pfst (⟹-⁺ w1)
⟹-⁺ {t = fst (ielim x t t₁ t₂)} (pfst w1@(pielim x₁ x₂ x₃)) =
  pfst (⟹-⁺ w1)
⟹-⁺ {t = fst (ielim x t t₁ (icon k p))} (pfst w1@(pιi x₁ x₂ x₃)) =
  pfst (⟹-⁺ w1)
⟹-⁺ {t = fst (⌜IMu⌝ x x₁ t)} (pfst w1@(p⌜IMu⌝ x₂)) =
  pfst (⟹-⁺ w1)
⟹-⁺ {t = snd (icon x t)} (psnd w1@(picon x₁)) =
  psnd (⟹-⁺ w1)
⟹-⁺ {t = snd (ielim x t t₁ t₂)} (psnd w1@(pielim x₁ x₂ x₃)) =
  psnd (⟹-⁺ w1)
⟹-⁺ {t = snd (ielim x t t₁ (icon k p))} (psnd w1@(pιi x₁ x₂ x₃)) =
  psnd (⟹-⁺ w1)
⟹-⁺ {t = snd (⌜IMu⌝ x x₁ t)} (psnd w1@(p⌜IMu⌝ x₂)) =
  psnd (⟹-⁺ w1)
⟹-⁺ {t = tr (⌜Hom⌝ c a (⌜IMu⌝ D I i)) (lam t) t₁} (ptr w1@(p⌜Hom⌝ x x₁ (p⌜IMu⌝ x₂)) w2@(plam x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜Hom⌝ c a (icon k p)) (lam t) t₁} (ptr w1@(p⌜Hom⌝ x x₁ (picon x₂)) w2@(plam x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜Hom⌝ c a (ielim D i ms t)) (lam t₁) t₂} (ptr w1@(p⌜Hom⌝ x x₁ (pielim x₂ x₃ x₄)) w2@(plam x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Hom⌝ c a (ielim D i ms (icon k p))) (lam t) t₁} (ptr w1@(p⌜Hom⌝ x x₁ (pιi x₂ x₃ x₄)) w2@(plam x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (lam t) t₁} (ptr w1@(p⌜IMu⌝ x) w2@(plam x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (icon k p) (lam t) t₁} (ptr w1@(picon x) w2@(plam x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (ielim D i ms t) (lam t₁) t₂} (ptr w1@(pielim x x₁ x₂) w2@(plam x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (lam t) t₁} (ptr w1@(pιi x x₁ x₂) w2@(plam x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (var x) (hrefl (icon x₁ t) t₁) t₂} (ptr w1@(pvar x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (var x) (hrefl (ielim x₁ t t₁ t₂) t₃) t₄} (ptr w1@(pvar x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (var x) (hrefl (ielim x₁ t t₁ (icon k p)) t₂) t₃} (ptr w1@(pvar x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (var x) (hrefl (⌜IMu⌝ x₁ x₂ t) t₁) t₂} (ptr w1@(pvar x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (lam t) (hrefl (icon x t₁) t₂) t₃} (ptr w1@(plam x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (lam t) (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr w1@(plam x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (lam t) (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr w1@(plam x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (lam t) (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr w1@(plam x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (app t u) (hrefl (icon x t₁) t₂) t₃} (ptr w1@(papp x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (app t u) (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr w1@(papp x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (app t u) (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr w1@(papp x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (app t u) (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr w1@(papp x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (app (lam t) u) (hrefl (icon x t₁) t₂) t₃} (ptr w1@(pβ x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (app (lam t) u) (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr w1@(pβ x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (app (lam t) u) (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr w1@(pβ x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (app (lam t) u) (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr w1@(pβ x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (pair a b) (hrefl (icon x t) t₁) t₂} (ptr w1@(ppair x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (pair a b) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ppair x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (pair a b) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ppair x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (pair a b) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ppair x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (absurd c e) (hrefl (icon x t) t₁) t₂} (ptr w1@(pabsurd x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (absurd c e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pabsurd x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (absurd c e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pabsurd x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (absurd c e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pabsurd x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ordtr a t u p q) (hrefl (⌜IMu⌝ D I i) t₁) t₂} (ptr w1@(pordtr x x₁ x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr a t u p q) (hrefl (icon k p₁) t₁) t₂} (ptr w1@(pordtr x x₁ x₂ x₃ x₄) w2@(phrefl (picon x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr a t u p q) (hrefl (ielim D i ms t₁) t₂) t₃} (ptr w1@(pordtr x x₁ x₂ x₃ x₄) w2@(phrefl (pielim x₅ x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (ordtr a t u p q) (hrefl (ielim D i ms (icon k p₁)) t₁) t₂} (ptr w1@(pordtr x x₁ x₂ x₃ x₄) w2@(phrefl (pιi x₅ x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (ordtr .nzero t u p q) (hrefl (⌜IMu⌝ D I i) t₁) t₂} (ptr n1@pordtr-z w2@(phrefl (p⌜IMu⌝ x) x₁) x₂) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (ordtr .nzero t u p q) (hrefl (icon k p₁) t₁) t₂} (ptr n1@pordtr-z w2@(phrefl (picon x) x₁) x₂) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (ordtr .nzero t u p q) (hrefl (ielim D i ms t₁) t₂) t₃} (ptr n1@pordtr-z w2@(phrefl (pielim x x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ordtr .nzero t u p q) (hrefl (ielim D i ms (icon k p₁)) t₁) t₂} (ptr n1@pordtr-z w2@(phrefl (pιi x x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero .nzero p q) (hrefl (⌜IMu⌝ D I i) t) t₁} (ptr w1@(pordtr-szz x) w2@(phrefl (p⌜IMu⌝ x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero .nzero p q) (hrefl (icon k p₁) t) t₁} (ptr w1@(pordtr-szz x) w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero .nzero p q) (hrefl (ielim D i ms t) t₁) t₂} (ptr w1@(pordtr-szz x) w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero .nzero p q) (hrefl (ielim D i ms (icon k p₁)) t) t₁} (ptr w1@(pordtr-szz x) w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) .nzero p q) (hrefl (⌜IMu⌝ D I i) t₁) t₂} (ptr w1@(pordtr-ssz x) w2@(phrefl (p⌜IMu⌝ x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) .nzero p q) (hrefl (icon k p₁) t₁) t₂} (ptr w1@(pordtr-ssz x) w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) .nzero p q) (hrefl (ielim D i ms t₁) t₂) t₃} (ptr w1@(pordtr-ssz x) w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) .nzero p q) (hrefl (ielim D i ms (icon k p₁)) t₁) t₂} (ptr w1@(pordtr-ssz x) w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero (nsuc u) p q) (hrefl (⌜IMu⌝ D I i) t) t₁} (ptr w1@(pordtr-szs x x₁ x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero (nsuc u) p q) (hrefl (icon k p₁) t) t₁} (ptr w1@(pordtr-szs x x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero (nsuc u) p q) (hrefl (ielim D i ms t) t₁) t₂} (ptr w1@(pordtr-szs x x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr (nsuc a) .nzero (nsuc u) p q) (hrefl (ielim D i ms (icon k p₁)) t) t₁} (ptr w1@(pordtr-szs x x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) (nsuc u) p q) (hrefl (⌜IMu⌝ D I i) t₁) t₂} (ptr w1@(pordtr-sss x x₁ x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) (nsuc u) p q) (hrefl (icon k p₁) t₁) t₂} (ptr w1@(pordtr-sss x x₁ x₂ x₃ x₄) w2@(phrefl (picon x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) (nsuc u) p q) (hrefl (ielim D i ms t₁) t₂) t₃} (ptr w1@(pordtr-sss x x₁ x₂ x₃ x₄) w2@(phrefl (pielim x₅ x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (ordtr (nsuc a) (nsuc t) (nsuc u) p q) (hrefl (ielim D i ms (icon k p₁)) t₁) t₂} (ptr w1@(pordtr-sss x x₁ x₂ x₃ x₄) w2@(phrefl (pιi x₅ x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (fst p) (hrefl (icon x t) t₁) t₂} (ptr w1@(pfst x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (fst p) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pfst x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (fst p) (hrefl (ielim x t t₁ (icon k p₁)) t₂) t₃} (ptr w1@(pfst x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (fst p) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pfst x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (snd p) (hrefl (icon x t) t₁) t₂} (ptr w1@(psnd x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (snd p) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(psnd x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (snd p) (hrefl (ielim x t t₁ (icon k p₁)) t₂) t₃} (ptr w1@(psnd x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (snd p) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(psnd x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (fst (pair a b)) (hrefl (icon x t) t₁) t₂} (ptr w1@(pβfst x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (fst (pair a b)) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pβfst x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (fst (pair a b)) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pβfst x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (fst (pair a b)) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pβfst x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (snd (pair a b)) (hrefl (icon x t) t₁) t₂} (ptr w1@(pβsnd x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (snd (pair a b)) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pβsnd x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (snd (pair a b)) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pβsnd x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (snd (pair a b)) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pβsnd x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr t (hrefl (icon x t₁) t₂) t₃} (ptr n1@p⌜base⌝ w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr n1@p⌜base⌝ w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr n1@p⌜base⌝ w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr n1@p⌜base⌝ w2@(phrefl (p⌜IMu⌝ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜Π⌝ c d) (hrefl (icon x t) t₁) t₂} (ptr w1@(p⌜Π⌝ x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜Π⌝ c d) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(p⌜Π⌝ x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (⌜Π⌝ c d) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(p⌜Π⌝ x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (⌜Π⌝ c d) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(p⌜Π⌝ x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Σ⌝ c d) (hrefl (icon x t) t₁) t₂} (ptr w1@(p⌜Σ⌝ x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜Σ⌝ c d) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(p⌜Σ⌝ x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (⌜Σ⌝ c d) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(p⌜Σ⌝ x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (⌜Σ⌝ c d) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(p⌜Σ⌝ x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Hom⌝ c a b) (hrefl (icon x t) t₁) t₂} (ptr w1@(p⌜Hom⌝ x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Hom⌝ c a b) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(p⌜Hom⌝ x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (⌜Hom⌝ c a b) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(p⌜Hom⌝ x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (hrefl c t) (hrefl (icon x t₁) t₂) t₃} (ptr w1@(phrefl x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (hrefl c t) (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr w1@(phrefl x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (hrefl c t) (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr w1@(phrefl x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (hrefl c t) (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr w1@(phrefl x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr d p e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr d p e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (tr d p e) (hrefl (ielim x t t₁ (icon k p₁)) t₂) t₃} (ptr w1@(ptr x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (tr d p e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜base⌝ s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-J-base x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜base⌝ s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-J-base x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜base⌝ s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-J-base x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜base⌝ s) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-J-base x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (icon x t₁) t₂) t₃} (ptr n1@p⌜Nat⌝ w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr n1@p⌜Nat⌝ w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr n1@p⌜Nat⌝ w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr n1@p⌜Nat⌝ w2@(phrefl (p⌜IMu⌝ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (icon x t₁) t₂) t₃} (ptr n1@p⌜Unit⌝ w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr n1@p⌜Unit⌝ w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr n1@p⌜Unit⌝ w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr n1@p⌜Unit⌝ w2@(phrefl (p⌜IMu⌝ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜Mu⌝ Dᵐ) (hrefl (icon x t) t₁) t₂} (ptr n1@p⌜Mu⌝ w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (⌜Mu⌝ Dᵐ) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr n1@p⌜Mu⌝ w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜Mu⌝ Dᵐ) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr n1@p⌜Mu⌝ w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜Mu⌝ Dᵐ) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr n1@p⌜Mu⌝ w2@(phrefl (p⌜IMu⌝ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜Unit⌝ s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-J-Unit x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜Unit⌝ s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-J-Unit x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜Unit⌝ s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-J-Unit x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl .⌜Unit⌝ s) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-J-Unit x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Mu⌝ Dᵐ) s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-J-Mu x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ _ _ _) s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-J-IMu x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Mu⌝ Dᵐ) s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-J-Mu x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ _ _ _) s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-J-IMu x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Mu⌝ Dᵐ) s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-J-Mu x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ _ _ _) s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-J-IMu x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Mu⌝ Dᵐ) s) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-J-Mu x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-J-Σ x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-J-Σ x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-J-Σ x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-J-Σ x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-J-Id x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-J-Id x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-J-Id x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-J-Id x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr .(var vz) (lam f) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-taut x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr .(var vz) (lam f) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-taut x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr .(var vz) (lam f) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-taut x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr .(var vz) (lam f) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-taut x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (hrefl C s) (hrefl (icon x t) t₁) t₂} (ptr w1@(phrefl-pw x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (hrefl C s) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(phrefl-pw x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (hrefl C s) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(phrefl-pw x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (hrefl C s) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(phrefl-pw x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-J-Hom x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-J-Hom x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-J-Hom x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-J-Hom x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a .(var vz)) (lam f) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(ptr-pw x₁ x₂ x₃ x₄ x₅) w2@(phrefl (picon x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a .(var vz)) (lam f) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(ptr-pw x₁ x₂ x₃ x₄ x₅) w2@(phrefl (pielim x₆ x₇ x₈) x₉) x₁₀) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₁₀)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a .(var vz)) (lam f) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(ptr-pw x₁ x₂ x₃ x₄ x₅) w2@(phrefl (pιi x₆ x₇ x₈) x₉) x₁₀) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₁₀)
⟹-⁺ {t = tr (tr (⌜Hom⌝ c a .(var vz)) (lam f) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(ptr-pw x₂ x₃ x₄ x₅ x₆) w2@(phrefl (p⌜IMu⌝ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (ap cB b p) (hrefl (icon x t) t₁) t₂} (ptr w1@(pap x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ap cB b p) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pap x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ap cB b p) (hrefl (ielim x t t₁ (icon k p₁)) t₂) t₃} (ptr w1@(pap x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ap cB b p) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pap x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ap cB b (hrefl c₁ s)) (hrefl (icon x t) t₁) t₂} (ptr w1@(pap-J x₁ x₂ x₃ x₄) w2@(phrefl (picon x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ap cB b (hrefl c₁ s)) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pap-J x₁ x₂ x₃ x₄) w2@(phrefl (pielim x₅ x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (ap cB b (hrefl c₁ s)) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pap-J x₁ x₂ x₃ x₄) w2@(phrefl (pιi x₅ x₆ x₇) x₈) x₉) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₉)
⟹-⁺ {t = tr (ap cB b (hrefl c₁ s)) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pap-J x₂ x₃ x₄ x₅) w2@(phrefl (p⌜IMu⌝ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (⌜Id⌝ c a b) (hrefl (icon x t) t₁) t₂} (ptr w1@(p⌜Id⌝ x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜Id⌝ c a b) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(p⌜Id⌝ x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (⌜Id⌝ c a b) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(p⌜Id⌝ x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (⌜Id⌝ c a b) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(p⌜Id⌝ x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (idrefl c t) (hrefl (icon x t₁) t₂) t₃} (ptr w1@(pidrefl x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (idrefl c t) (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr w1@(pidrefl x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (idrefl c t) (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr w1@(pidrefl x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (idrefl c t) (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr w1@(pidrefl x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (jsub d p e) (hrefl (icon x t) t₁) t₂} (ptr w1@(pjsub x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (jsub d p e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pjsub x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (jsub d p e) (hrefl (ielim x t t₁ (icon k p₁)) t₂) t₃} (ptr w1@(pjsub x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (jsub d p e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pjsub x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (jsub d (idrefl c s) e) (hrefl (icon x t) t₁) t₂} (ptr w1@(pjsub-refl x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (jsub d (idrefl c s) e) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pjsub-refl x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (jsub d (idrefl c s) e) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pjsub-refl x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (jsub d (idrefl c s) e) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pjsub-refl x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (icon x t₁) t₂) t₃} (ptr n1@punit w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr n1@punit w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr n1@punit w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr n1@punit w2@(phrefl (p⌜IMu⌝ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr t (hrefl (icon x t₁) t₂) t₃} (ptr n1@pnzero w2@(phrefl (picon x₁) x₂) x₃) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr n1@pnzero w2@(phrefl (pielim x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr n1@pnzero w2@(phrefl (pιi x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr n1@pnzero w2@(phrefl (p⌜IMu⌝ x₂) x₃) x₄) =
  ptr (⟹-⁺ n1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (nsuc n) (hrefl (icon x t) t₁) t₂} (ptr w1@(pnsuc x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (nsuc n) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pnsuc x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (nsuc n) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pnsuc x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (nsuc n) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pnsuc x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (natrec z s n) (hrefl (icon x t) t₁) t₂} (ptr w1@(pnatrec x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (natrec z s n) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pnatrec x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (natrec z s n) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pnatrec x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (natrec z s n) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pnatrec x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (natrec z s .nzero) (hrefl (icon x t) t₁) t₂} (ptr w1@(pnatrec-zero x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (natrec z s .nzero) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pnatrec-zero x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (natrec z s .nzero) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pnatrec-zero x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (natrec z s .nzero) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pnatrec-zero x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (natrec z s (nsuc n)) (hrefl (icon x t) t₁) t₂} (ptr w1@(pnatrec-suc x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (natrec z s (nsuc n)) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pnatrec-suc x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (natrec z s (nsuc n)) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(pnatrec-suc x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (natrec z s (nsuc n)) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pnatrec-suc x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (con k p) (hrefl (icon x t) t₁) t₂} (ptr w1@(pcon x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (con k p) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pcon x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (con k p) (hrefl (ielim x t t₁ (icon k₁ p₁)) t₂) t₃} (ptr w1@(pcon x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (con k p) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pcon x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms t) (hrefl (icon x t₁) t₂) t₃} (ptr w1@(pelim x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms t) (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr w1@(pelim x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (elim D ms t) (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr w1@(pelim x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (elim D ms t) (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr w1@(pelim x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (icon x t) t₁) t₂} (ptr w1@(pι x₁ x₂) w2@(phrefl (picon x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pι x₁ x₂) w2@(phrefl (pielim x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (ielim x t t₁ (icon k₁ p₁)) t₂) t₃} (ptr w1@(pι x₁ x₂) w2@(phrefl (pιi x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (elim D ms (con k p)) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pι x₂ x₃) w2@(phrefl (p⌜IMu⌝ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl ⌜base⌝ t) t₁} (ptr w1@(p⌜IMu⌝ x) w2@(phrefl p⌜base⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (⌜Σ⌝ t t₁) t₂) t₃} (ptr w1@(p⌜IMu⌝ x) w2@(phrefl (p⌜Σ⌝ x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(p⌜IMu⌝ x) w2@(phrefl (p⌜Hom⌝ x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (⌜Id⌝ t t₁ t₂) t₃) t₄} (ptr w1@(p⌜IMu⌝ x) w2@(phrefl (p⌜Id⌝ x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (con x t) t₁) t₂} (ptr w1@(p⌜IMu⌝ x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(p⌜IMu⌝ x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (elim x t (con k p)) t₁) t₂} (ptr w1@(p⌜IMu⌝ x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (icon x t) t₁) t₂} (ptr w1@(p⌜IMu⌝ x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(p⌜IMu⌝ x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (ielim x t t₁ (icon k p)) t₂) t₃} (ptr w1@(p⌜IMu⌝ x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (⌜Mu⌝ x) t) t₁} (ptr w1@(p⌜IMu⌝ x₁) w2@(phrefl p⌜Mu⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(p⌜IMu⌝ x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl ⌜Unit⌝ t) t₁} (ptr w1@(p⌜IMu⌝ x) w2@(phrefl p⌜Unit⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (⌜IMu⌝ D I i) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(p⌜IMu⌝ x) w2@(phrefl-pw x₁ x₂ x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (icon k p) (hrefl ⌜base⌝ t) t₁} (ptr w1@(picon x) w2@(phrefl p⌜base⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (icon k p) (hrefl (⌜Σ⌝ t t₁) t₂) t₃} (ptr w1@(picon x) w2@(phrefl (p⌜Σ⌝ x₁ x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (icon k p) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(picon x) w2@(phrefl (p⌜Hom⌝ x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (icon k p) (hrefl (⌜Id⌝ t t₁ t₂) t₃) t₄} (ptr w1@(picon x) w2@(phrefl (p⌜Id⌝ x₁ x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (icon k p) (hrefl (con x t) t₁) t₂} (ptr w1@(picon x₁) w2@(phrefl (pcon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (icon k p) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(picon x₁) w2@(phrefl (pelim x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (icon k p) (hrefl (elim x t (con k₁ p₁)) t₁) t₂} (ptr w1@(picon x₁) w2@(phrefl (pι x₂ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (icon k p) (hrefl (icon x t) t₁) t₂} (ptr w1@(picon x₁) w2@(phrefl (picon x₂) x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (icon k p) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(picon x₁) w2@(phrefl (pielim x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (icon k p) (hrefl (ielim x t t₁ (icon k₁ p₁)) t₂) t₃} (ptr w1@(picon x₁) w2@(phrefl (pιi x₂ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (icon k p) (hrefl (⌜Mu⌝ x) t) t₁} (ptr w1@(picon x₁) w2@(phrefl p⌜Mu⌝ x₂) x₃) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr (icon k p) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(picon x₂) w2@(phrefl (p⌜IMu⌝ x₃) x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (icon k p) (hrefl ⌜Unit⌝ t) t₁} (ptr w1@(picon x) w2@(phrefl p⌜Unit⌝ x₁) x₂) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₂)
⟹-⁺ {t = tr (icon k p) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(picon x) w2@(phrefl-pw x₁ x₂ x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl ⌜base⌝ t₁) t₂} (ptr w1@(pielim x x₁ x₂) w2@(phrefl p⌜base⌝ x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (⌜Σ⌝ t₁ t₂) t₃) t₄} (ptr w1@(pielim x x₁ x₂) w2@(phrefl (p⌜Σ⌝ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (⌜Hom⌝ t₁ t₂ t₃) t₄) t₅} (ptr w1@(pielim x x₁ x₂) w2@(phrefl (p⌜Hom⌝ x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (⌜Id⌝ t₁ t₂ t₃) t₄) t₅} (ptr w1@(pielim x x₁ x₂) w2@(phrefl (p⌜Id⌝ x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (con x t₁) t₂) t₃} (ptr w1@(pielim x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (elim x t₁ t₂) t₃) t₄} (ptr w1@(pielim x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (elim x t₁ (con k p)) t₂) t₃} (ptr w1@(pielim x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (icon x t₁) t₂) t₃} (ptr w1@(pielim x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (ielim x t₁ t₂ t₃) t₄) t₅} (ptr w1@(pielim x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (ielim x t₁ t₂ (icon k p)) t₃) t₄} (ptr w1@(pielim x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (⌜Mu⌝ x) t₁) t₂} (ptr w1@(pielim x₁ x₂ x₃) w2@(phrefl p⌜Mu⌝ x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (⌜IMu⌝ x x₁ t₁) t₂) t₃} (ptr w1@(pielim x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl ⌜Unit⌝ t₁) t₂} (ptr w1@(pielim x x₁ x₂) w2@(phrefl p⌜Unit⌝ x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ielim D i ms t) (hrefl (⌜Hom⌝ t₁ t₂ t₃) t₄) t₅} (ptr w1@(pielim x x₁ x₂) w2@(phrefl-pw x₃ x₄ x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl ⌜base⌝ t) t₁} (ptr w1@(pιi x x₁ x₂) w2@(phrefl p⌜base⌝ x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (⌜Σ⌝ t t₁) t₂) t₃} (ptr w1@(pιi x x₁ x₂) w2@(phrefl (p⌜Σ⌝ x₃ x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pιi x x₁ x₂) w2@(phrefl (p⌜Hom⌝ x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (⌜Id⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pιi x x₁ x₂) w2@(phrefl (p⌜Id⌝ x₃ x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (con x t) t₁) t₂} (ptr w1@(pιi x₁ x₂ x₃) w2@(phrefl (pcon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (elim x t t₁) t₂) t₃} (ptr w1@(pιi x₁ x₂ x₃) w2@(phrefl (pelim x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (elim x t (con k₁ p₁)) t₁) t₂} (ptr w1@(pιi x₁ x₂ x₃) w2@(phrefl (pι x₄ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (icon x t) t₁) t₂} (ptr w1@(pιi x₁ x₂ x₃) w2@(phrefl (picon x₄) x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (ielim x t t₁ t₂) t₃) t₄} (ptr w1@(pιi x₁ x₂ x₃) w2@(phrefl (pielim x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (ielim x t t₁ (icon k₁ p₁)) t₂) t₃} (ptr w1@(pιi x₁ x₂ x₃) w2@(phrefl (pιi x₄ x₅ x₆) x₇) x₈) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₈)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (⌜Mu⌝ x) t) t₁} (ptr w1@(pιi x₁ x₂ x₃) w2@(phrefl p⌜Mu⌝ x₄) x₅) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (⌜IMu⌝ x x₁ t) t₁) t₂} (ptr w1@(pιi x₂ x₃ x₄) w2@(phrefl (p⌜IMu⌝ x₅) x₆) x₇) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₇)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl ⌜Unit⌝ t) t₁} (ptr w1@(pιi x x₁ x₂) w2@(phrefl p⌜Unit⌝ x₃) x₄) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = tr (ielim D i ms (icon k p)) (hrefl (⌜Hom⌝ t t₁ t₂) t₃) t₄} (ptr w1@(pιi x x₁ x₂) w2@(phrefl-pw x₃ x₄ x₅) x₆) =
  ptr (⟹-⁺ w1) (⟹-⁺ w2) (⟹-⁺ x₆)
⟹-⁺ {t = tr t (icon x t₁) t₂} (ptr x₁ w2@(picon x₂) x₃) =
  ptr (⟹-⁺ x₁) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = tr t (ielim x t₁ t₂ t₃) t₄} (ptr x₁ w2@(pielim x₂ x₃ x₄) x₅) =
  ptr (⟹-⁺ x₁) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (ielim x t₁ t₂ (icon k p)) t₃} (ptr x₁ w2@(pιi x₂ x₃ x₄) x₅) =
  ptr (⟹-⁺ x₁) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = tr t (⌜IMu⌝ x x₁ t₁) t₂} (ptr x₂ w2@(p⌜IMu⌝ x₃) x₄) =
  ptr (⟹-⁺ x₂) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = ap t t₁ (hrefl (icon x t₂) t₃)} (pap x₁ x₂ w3@(phrefl (picon x₃) x₄)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = ap t t₁ (hrefl (ielim x t₂ t₃ t₄) t₅)} (pap x₁ x₂ w3@(phrefl (pielim x₃ x₄ x₅) x₆)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = ap t t₁ (hrefl (ielim x t₂ t₃ (icon k p)) t₄)} (pap x₁ x₂ w3@(phrefl (pιi x₃ x₄ x₅) x₆)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = ap t t₁ (icon x t₂)} (pap x₁ x₂ w3@(picon x₃)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = ap t t₁ (ielim x t₂ t₃ t₄)} (pap x₁ x₂ w3@(pielim x₃ x₄ x₅)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = ap t t₁ (ielim x t₂ t₃ (icon k p))} (pap x₁ x₂ w3@(pιi x₃ x₄ x₅)) =
  pap (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = ap t t₁ (⌜IMu⌝ x x₁ t₂)} (pap x₂ x₃ w3@(p⌜IMu⌝ x₄)) =
  pap (⟹-⁺ x₂) (⟹-⁺ x₃) (⟹-⁺ w3)
⟹-⁺ {t = jsub t (icon x t₁) t₂} (pjsub x₁ w2@(picon x₂) x₃) =
  pjsub (⟹-⁺ x₁) (⟹-⁺ w2) (⟹-⁺ x₃)
⟹-⁺ {t = jsub t (ielim x t₁ t₂ t₃) t₄} (pjsub x₁ w2@(pielim x₂ x₃ x₄) x₅) =
  pjsub (⟹-⁺ x₁) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = jsub t (ielim x t₁ t₂ (icon k p)) t₃} (pjsub x₁ w2@(pιi x₂ x₃ x₄) x₅) =
  pjsub (⟹-⁺ x₁) (⟹-⁺ w2) (⟹-⁺ x₅)
⟹-⁺ {t = jsub t (⌜IMu⌝ x x₁ t₁) t₂} (pjsub x₂ w2@(p⌜IMu⌝ x₃) x₄) =
  pjsub (⟹-⁺ x₂) (⟹-⁺ w2) (⟹-⁺ x₄)
⟹-⁺ {t = natrec t t₁ (icon x t₂)} (pnatrec x₁ x₂ w3@(picon x₃)) =
  pnatrec (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = natrec t t₁ (ielim x t₂ t₃ t₄)} (pnatrec x₁ x₂ w3@(pielim x₃ x₄ x₅)) =
  pnatrec (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = natrec t t₁ (ielim x t₂ t₃ (icon k p))} (pnatrec x₁ x₂ w3@(pιi x₃ x₄ x₅)) =
  pnatrec (⟹-⁺ x₁) (⟹-⁺ x₂) (⟹-⁺ w3)
⟹-⁺ {t = natrec t t₁ (⌜IMu⌝ x x₁ t₂)} (pnatrec x₂ x₃ w3@(p⌜IMu⌝ x₄)) =
  pnatrec (⟹-⁺ x₂) (⟹-⁺ x₃) (⟹-⁺ w3)
⟹-⁺ {t = elim x t (⌜IMu⌝ D I i)} (pelim x₁ w2@(p⌜IMu⌝ x₂)) =
  pelim (⟹-⁺ x₁) (⟹-⁺ w2)
⟹-⁺ {t = elim x t (icon k p)} (pelim x₁ w2@(picon x₂)) =
  pelim (⟹-⁺ x₁) (⟹-⁺ w2)
⟹-⁺ {t = elim x t (ielim D i ms t₁)} (pelim x₁ w2@(pielim x₂ x₃ x₄)) =
  pelim (⟹-⁺ x₁) (⟹-⁺ w2)
⟹-⁺ {t = elim x t (ielim D i ms (icon k p))} (pelim x₁ w2@(pιi x₂ x₃ x₄)) =
  pelim (⟹-⁺ x₁) (⟹-⁺ w2)
⟹-⁺ {t = icon x t} (picon x₁) =
  picon (⟹-⁺ x₁)
-- ★ the indexed ι root, mirroring `pι` above: `ifields`/`sel` are metalevel,
-- so the development runs through their congruence LEMMAS.
⟹-⁺ (pιi {D = D} {k = k} pi pms pp) =
  p-ifields (ilookupD D k) (⟹-⁺ pi) (λ { vz → ⟹-⁺ pi })
            (⟹-⁺ pms) (p-sel k (⟹-⁺ pms)) (⟹-⁺ pp)
-- ★ the one that fires: an `icon` scrutinee turns congruence into the root.
-- ⚠ the rest must ENUMERATE the scrutinee — `_⁺` splits on `icon` first, so a
--   variable there leaves `ielim D i ms t ⁺` stuck and the RHS untypeable.
⟹-⁺ (pielim {t = icon k c} pi pms (picon pp)) = pιi (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pp)
⟹-⁺ (pielim {t = (var x)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (lam t)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (app f a)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (pair a b)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (absurd c e)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (ordtr a t u p q)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (fst p)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (snd p)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = ⌜base⌝} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (⌜Π⌝ c d)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (⌜Σ⌝ c d)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (⌜Hom⌝ c a b)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (hrefl c t)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (tr d p e)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (ap c b p)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (⌜Id⌝ c a b)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (idrefl c t)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (jsub d p e)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = unit} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = nzero} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (nsuc n)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (natrec z s w)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = ⌜Nat⌝} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = ⌜Unit⌝} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = ⌜Mu⌝ _} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (con k c)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (elim D₁ ms₁ t₁)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (ielim D₁ i₁ ms₁ t₁)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ (pielim {t = (⌜IMu⌝ D₁ I₁ i₁)} pi pms pt) = pielim (⟹-⁺ pi) (⟹-⁺ pms) (⟹-⁺ pt)
⟹-⁺ {t = ⌜IMu⌝ x x₁ t} (p⌜IMu⌝ x₂) =
  p⌜IMu⌝ (⟹-⁺ x₂)

------------------------------------------------------------------------
-- Diamond (from the triangle), then confluence of `⟹*`, then of `⟶*`.
------------------------------------------------------------------------

diamond : {t u v : RTm Γ} → t ⟹ u → t ⟹ v →
          Σ (RTm _) (λ w → (u ⟹ w) × (v ⟹ w))
diamond {t = t} pu pv = (t ⁺) , (⟹-⁺ pu , ⟹-⁺ pv)

infix 3 _⟹*_
data _⟹*_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  pdone : {t : RTm Γ} → t ⟹* t
  pstep : {t u v : RTm Γ} → t ⟹ u → u ⟹* v → t ⟹* v

strip : {t u v : RTm Γ} → t ⟹ u → t ⟹* v →
        Σ (RTm _) (λ w → (u ⟹* w) × (v ⟹ w))
strip pu pdone = _ , (pdone , pu)
strip pu (pstep pv pv*) with diamond pu pv
... | w₁ , (u⟹w₁ , v₁⟹w₁) with strip v₁⟹w₁ pv*
...   | w , (w₁⟹*w , v⟹w) = w , (pstep u⟹w₁ w₁⟹*w , v⟹w)

confluent⟹ : {t u v : RTm Γ} → t ⟹* u → t ⟹* v →
             Σ (RTm _) (λ w → (u ⟹* w) × (v ⟹* w))
confluent⟹ pdone pv = _ , (pv , pdone)
confluent⟹ (pstep pu pu*) pv with strip pu pv
... | w₁ , (u₁⟹*w₁ , v⟹w₁) with confluent⟹ pu* u₁⟹*w₁
...   | w , (u⟹*w , w₁⟹*w) = w , (u⟹*w , pstep v⟹w₁ w₁⟹*w)

⟶*→⟹* : {t u : RTm Γ} → t ⟶* u → t ⟹* u
⟶*→⟹* done       = pdone
⟶*→⟹* (step r p) = pstep (⟶→⟹ r) (⟶*→⟹* p)

⟹*→⟶* : {t u : RTm Γ} → t ⟹* u → t ⟶* u
⟹*→⟶* pdone        = done
⟹*→⟶* (pstep p ps) = ⟶*-trans (⟹→⟶* p) (⟹*→⟶* ps)

-- CONFLUENCE of `⟶*`.
confluent : {t u v : RTm Γ} → t ⟶* u → t ⟶* v →
            Σ (RTm _) (λ w → (u ⟶* w) × (v ⟶* w))
confluent p q with confluent⟹ (⟶*→⟹* p) (⟶*→⟹* q)
... | w , (uw , vw) = w , (⟹*→⟶* uw , ⟹*→⟶* vw)

-- CHURCH–ROSSER: convertible terms are joinable. Unblocks Π-injectivity (B2).
church-rosser : {t u : RTm Γ} → t ≅ u → Σ (RTm _) (λ w → (t ⟶* w) × (u ⟶* w))
church-rosser (cred r)   = _ , (step r done , done)
church-rosser crfl       = _ , (done , done)
church-rosser (csym c) with church-rosser c
... | w , (tw , uw) = w , (uw , tw)
church-rosser (ctrn c d) with church-rosser c | church-rosser d
... | w₁ , (tw₁ , u₀w₁) | w₂ , (u₀w₂ , uw₂) with confluent u₀w₁ u₀w₂
...   | w , (w₁w , w₂w) = w , (⟶*-trans tw₁ w₁w , ⟶*-trans uw₂ w₂w)
