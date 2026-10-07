-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import DirectedHoTT.Spec.Syntax using ( Defs; _<ˢ_; _<ˢ?_ )
module DirectedHoTT.Metatheory.Confluence (𝒮 : Defs) where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_; ⊥; ⊥-elim; Dec; yes; no )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app; pair; fst; snd; absurd
        ; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub
        ; unit; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝; subTm-subTm
        ; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃; Ren; extR
        ; renTm; renTm-renTm; renTm-cong; Sub; extS; subTm; renTm-subTm
        ; subTm-renTm; subTm-cong; _ᵣ∘ₛ_; _ₛ∘ᵣ_; _∘ᵣ_; dι; dρ; con; IMu; ielim
        ; ⌜IMu⌝; εwkTm; RTy; ⌜Fin⌝; dσ; dpay; dih; fzero; fsuc; fcase; fcase0
        ; psplit; cong₄; cong₃
        ; ref; εwkTm-ren; εwkTm-sub; Defs; _<ˢ_; _<ˢ?_
        ; εsub )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; pw?; stkC?; stkA?; pwBody; pwShift; pw?-ren
        ; stkC?-ren; stkA?-ren; pwBody-ren; pw?-sub; stkC?-sub; stkA?-sub
        ; pwBody-sub; pw⊥stk; pw⊥stkA; stkC?→stkA?; stk⊥pw; stkA?⊥pw )
open import DirectedHoTT.Spec.Reduction 𝒮
  using ( single; swp; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ
        ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz
        ; ordtr-szs; ordtr-sss; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ
        ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; tr-J-base
        ; tr-J-Σ; tr-J-Id; tr-taut; hrefl-pw; hrefl-Nat-z; hrefl-Nat-s; tr-J-Hom; tr-pw; ξ-⌜Hom⌝ᶜ
        ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ap-J
        ; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-⌜Fin⌝; ξ-idreflᶜ
        ; ξ-idreflᵃ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; natrec-zero; natrec-suc
        ; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ; tr-J-Unit; tr-J-IMu
        ; El-⌜Nat⌝; El-⌜Unit⌝; _⟶*_; done; step; _≅_; cred; crfl; csym; ctrn
        ; ξ-con; ξ-ielimⁱ; ξ-ielimᵗ; El-⌜IMu⌝; ι; dpay-ι; dpay-σ; dpay-ρ
        ; dih-ι; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β; tr-J-Fin; single2
        ; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dσˢ; ξ-dσᶠ
        ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ
        ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ
        ; ξ-psplitᵍ
        ; δref )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮
  using ( sub-comm; sub-comm-ext; ⟶-sub; wk-sub; wk₁-sub; swp-sub; pwShift-sub
        ; sub-comm2 )

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

open import DirectedHoTT.Metatheory.RedCong 𝒮

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
  ptr-J-Unit : {c a m : RTm (Γ ∙)} {s e e' : RTm Γ} →
               e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s) e ⟹ e'
  -- ★ §10.4's obligation in parallel form: the J rule at a family code
  --   discards the path whole.
  ptr-J-IMu : {Iⁱ Dⁱ iˣ : RTm Γ} {c a m : RTm (Γ ∙)} {s e e' : RTm Γ} →
              e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ Iⁱ Dⁱ iˣ) s) e ⟹ e'
  ptr-J-Fin : {n : RTm Γ} {c a m : RTm (Γ ∙)} {s e e' : RTm Γ} →
              e ⟹ e' → tr (⌜Hom⌝ c a m) (hrefl (⌜Fin⌝ n) s) e ⟹ e'
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
  -- ★ F6: the order's reflexivity computes with its type.
  phrefl-Nat-z : hrefl ⌜Nat⌝ (nzero {Γ}) ⟹ unit
  phrefl-Nat-s : {m m' : RTm Γ} → m ⟹ m' → hrefl ⌜Nat⌝ (nsuc m) ⟹ hrefl ⌜Nat⌝ m'
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
  -- ★★ LEVITATED FAMILIES: congruences, plus the roots developed
  --   componentwise (the `pβ`/`pnatrec-suc` shape; a discarding rule
  --   carries premises only for what its right-hand side mentions).
  p⌜IMu⌝ : {I I' D D' i i' : RTm Γ} → I ⟹ I' → D ⟹ D' → i ⟹ i' →
           ⌜IMu⌝ I D i ⟹ ⌜IMu⌝ I' D' i'
  p⌜Fin⌝ : {n n' : RTm Γ} → n ⟹ n' → ⌜Fin⌝ n ⟹ ⌜Fin⌝ n'
  pcon   : {p p' : RTm Γ} → p ⟹ p' → con p ⟹ con p'
  pielim : {D D' i i' e e' t t' : RTm Γ} →
           D ⟹ D' → i ⟹ i' → e ⟹ e' → t ⟹ t' → ielim D i e t ⟹ ielim D' i' e' t'
  pι     : {D D' i i' e e' p p' : RTm Γ} →
           D ⟹ D' → i ⟹ i' → e ⟹ e' → p ⟹ p' →
           ielim D i e (con p) ⟹ app (app (app e' i') p') (dih D' e' (app D' i') p')
  pdι    : dι {Γ} ⟹ dι
  pdσ    : {S S' f f' : RTm Γ} → S ⟹ S' → f ⟹ f' → dσ S f ⟹ dσ S' f'
  pdρ    : {j j' C C' : RTm Γ} → j ⟹ j' → C ⟹ C' → dρ j C ⟹ dρ j' C'
  pdpay  : {I I' D D' C C' : RTm Γ} →
           I ⟹ I' → D ⟹ D' → C ⟹ C' → dpay I D C ⟹ dpay I' D' C'
  pdpay-ι : {I D : RTm Γ} → dpay I D dι ⟹ ⌜Unit⌝
  pdpay-σ : {I I' D D' S S' f f' : RTm Γ} →
            I ⟹ I' → D ⟹ D' → S ⟹ S' → f ⟹ f' →
            dpay I D (dσ S f) ⟹
            ⌜Σ⌝ S' (dpay (renTm vs I') (renTm vs D') (app (renTm vs f') (var vz)))
  pdpay-ρ : {I I' D D' j j' C C' : RTm Γ} →
            I ⟹ I' → D ⟹ D' → j ⟹ j' → C ⟹ C' →
            dpay I D (dρ j C) ⟹
            ⌜Σ⌝ (⌜IMu⌝ I' D' j') (dpay (renTm vs I') (renTm vs D') (renTm vs C'))
  pdih   : {D D' e e' C C' p p' : RTm Γ} →
           D ⟹ D' → e ⟹ e' → C ⟹ C' → p ⟹ p' → dih D e C p ⟹ dih D' e' C' p'
  pdih-ι : {D e p : RTm Γ} → dih D e dι p ⟹ unit
  pdih-σ : {D D' e e' S f f' p p' : RTm Γ} →
           D ⟹ D' → e ⟹ e' → f ⟹ f' → p ⟹ p' →
           dih D e (dσ S f) p ⟹ dih D' e' (app f' (fst p')) (snd p')
  pdih-ρ : {D D' e e' j j' C C' p p' : RTm Γ} →
           D ⟹ D' → e ⟹ e' → j ⟹ j' → C ⟹ C' → p ⟹ p' →
           dih D e (dρ j C) p ⟹ pair (ielim D' j' e' (fst p')) (dih D' e' C' (snd p'))
  pfzero : fzero {Γ} ⟹ fzero
  pfsuc  : {t t' : RTm Γ} → t ⟹ t' → fsuc t ⟹ fsuc t'
  pfcase : {t t' a a' : RTm Γ} {b b' : RTm (Γ ∙)} →
           t ⟹ t' → a ⟹ a' → b ⟹ b' → fcase t a b ⟹ fcase t' a' b'
  pfcase-z : {a a' : RTm Γ} {b : RTm (Γ ∙)} → a ⟹ a' → fcase fzero a b ⟹ a'
  pfcase-s : {t t' a : RTm Γ} {b b' : RTm (Γ ∙)} → t ⟹ t' → b ⟹ b' →
             fcase (fsuc t) a b ⟹ subTm (single t') b'
  pfcase0 : {t t' : RTm Γ} → t ⟹ t' → fcase0 t ⟹ fcase0 t'
  ppsplit : {b b' : RTm ((Γ ∙) ∙)} {q q' : RTm Γ} → b ⟹ b' → q ⟹ q' →
            psplit b q ⟹ psplit b' q'
  ppsplit-β : {b b' : RTm ((Γ ∙) ∙)} {x x' y y' : RTm Γ} →
              b ⟹ b' → x ⟹ x' → y ⟹ y' →
              psplit b (pair x y) ⟹ subTm (single2 x' y') b'
  -- ★ definitions: inert, or δ with the body developed
  pref : {d : ℕ} → ref {Γ} d ⟹ ref d
  -- ★ δ unfolds a projection (PLAN-REF): the body is the SIGNATURE's, not a
  --   subterm, so the parallel step does not reduce inside it
  pdelta : {d : ℕ} → d <ˢ Defs.size 𝒮 → ref {Γ} d ⟹ εwkTm (Defs.body 𝒮 d)

⟹-refl : (t : RTm Γ) → t ⟹ t
⟹-refl ⌜Nat⌝      = p⌜Nat⌝
⟹-refl ⌜Unit⌝     = p⌜Unit⌝
⟹-refl unit       = punit
⟹-refl nzero      = pnzero
⟹-refl (nsuc n)   = pnsuc (⟹-refl n)
⟹-refl (⌜IMu⌝ I D i) = p⌜IMu⌝ (⟹-refl I) (⟹-refl D) (⟹-refl i)
⟹-refl (⌜Fin⌝ n) = p⌜Fin⌝ (⟹-refl n)
⟹-refl (con p) = pcon (⟹-refl p)
⟹-refl (ielim D i e t) = pielim (⟹-refl D) (⟹-refl i) (⟹-refl e) (⟹-refl t)
⟹-refl dι = pdι
⟹-refl (dσ S f) = pdσ (⟹-refl S) (⟹-refl f)
⟹-refl (dρ j C) = pdρ (⟹-refl j) (⟹-refl C)
⟹-refl (dpay I D C) = pdpay (⟹-refl I) (⟹-refl D) (⟹-refl C)
⟹-refl (dih D e C p) = pdih (⟹-refl D) (⟹-refl e) (⟹-refl C) (⟹-refl p)
⟹-refl fzero = pfzero
⟹-refl (fsuc t) = pfsuc (⟹-refl t)
⟹-refl (fcase t a b) = pfcase (⟹-refl t) (⟹-refl a) (⟹-refl b)
⟹-refl (fcase0 t) = pfcase0 (⟹-refl t)
⟹-refl (psplit b q) = ppsplit (⟹-refl b) (⟹-refl q)
⟹-refl (ref d) = pref
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
-- split on the SOURCE's head first: a non-key head is refuted on the key
-- alone, a key head admits one derivation constructor (2026-09-30: the
-- derivation-first form spent ~25 s unifying all 72 constructors' indices).
pw?-⟹ : {C C' : RTm Γ} → C ⟹ C' → pw? C ≡ true → pw? C' ≡ true
pw?-⟹ {C = var _} _ ()
pw?-⟹ {C = lam _} _ ()
pw?-⟹ {C = app _ _} _ ()
pw?-⟹ {C = pair _ _} _ ()
pw?-⟹ {C = absurd _ _} _ ()
pw?-⟹ {C = ordtr _ _ _ _ _} _ ()
pw?-⟹ {C = fst _} _ ()
pw?-⟹ {C = snd _} _ ()
pw?-⟹ {C = ⌜base⌝} _ ()
pw?-⟹ {C = ⌜Π⌝ _ _} (p⌜Π⌝ _ _) h = refl
pw?-⟹ {C = ⌜Σ⌝ _ _} _ ()
pw?-⟹ {C = ⌜Hom⌝ _ _ _} (p⌜Hom⌝ pc _ _) h = pw?-⟹ pc h
pw?-⟹ {C = hrefl _ _} _ ()
pw?-⟹ {C = tr _ _ _} _ ()
pw?-⟹ {C = ap _ _ _} _ ()
pw?-⟹ {C = ⌜Id⌝ _ _ _} _ ()
pw?-⟹ {C = idrefl _ _} _ ()
pw?-⟹ {C = jsub _ _ _} _ ()
pw?-⟹ {C = unit} _ ()
pw?-⟹ {C = nzero} _ ()
pw?-⟹ {C = nsuc _} _ ()
pw?-⟹ {C = natrec _ _ _} _ ()
pw?-⟹ {C = con _} _ ()
pw?-⟹ {C = ielim _ _ _ _} _ ()
pw?-⟹ {C = dι} _ ()
pw?-⟹ {C = dσ _ _} _ ()
pw?-⟹ {C = dρ _ _} _ ()
pw?-⟹ {C = dpay _ _ _} _ ()
pw?-⟹ {C = dih _ _ _ _} _ ()
pw?-⟹ {C = fzero} _ ()
pw?-⟹ {C = fsuc _} _ ()
pw?-⟹ {C = fcase _ _ _} _ ()
pw?-⟹ {C = fcase0 _} _ ()
pw?-⟹ {C = psplit _ _} _ ()
pw?-⟹ {C = ⌜Nat⌝} _ ()
pw?-⟹ {C = ⌜IMu⌝ _ _ _} _ ()
pw?-⟹ {C = ⌜Fin⌝ _} _ ()
pw?-⟹ {C = ⌜Unit⌝} _ ()

-- ★ the `stkA?` peer for parallel reduction (SpikeNatJ split).
-- split on the SOURCE's head first: a non-key head is refuted on the key
-- alone, a key head admits one derivation constructor (2026-09-30: the
-- derivation-first form spent ~25 s unifying all 72 constructors' indices).
stkA?-⟹ : {C C' : RTm Γ} → C ⟹ C' → stkA? C ≡ true → stkA? C' ≡ true
stkA?-⟹ {C = var _} _ ()
stkA?-⟹ {C = lam _} _ ()
stkA?-⟹ {C = app _ _} _ ()
stkA?-⟹ {C = pair _ _} _ ()
stkA?-⟹ {C = absurd _ _} _ ()
stkA?-⟹ {C = ordtr _ _ _ _ _} _ ()
stkA?-⟹ {C = fst _} _ ()
stkA?-⟹ {C = snd _} _ ()
stkA?-⟹ {C = ⌜base⌝} p⌜base⌝ h = refl
stkA?-⟹ {C = ⌜Π⌝ _ _} _ ()
stkA?-⟹ {C = ⌜Σ⌝ _ _} (p⌜Σ⌝ _ _) h = refl
stkA?-⟹ {C = ⌜Hom⌝ _ _ _} (p⌜Hom⌝ pc _ _) h = stkA?-⟹ pc h
stkA?-⟹ {C = hrefl _ _} _ ()
stkA?-⟹ {C = tr _ _ _} _ ()
stkA?-⟹ {C = ap _ _ _} _ ()
stkA?-⟹ {C = ⌜Id⌝ _ _ _} (p⌜Id⌝ _ _ _) h = refl
stkA?-⟹ {C = idrefl _ _} _ ()
stkA?-⟹ {C = jsub _ _ _} _ ()
stkA?-⟹ {C = unit} _ ()
stkA?-⟹ {C = nzero} _ ()
stkA?-⟹ {C = nsuc _} _ ()
stkA?-⟹ {C = natrec _ _ _} _ ()
stkA?-⟹ {C = con _} _ ()
stkA?-⟹ {C = ielim _ _ _ _} _ ()
stkA?-⟹ {C = dι} _ ()
stkA?-⟹ {C = dσ _ _} _ ()
stkA?-⟹ {C = dρ _ _} _ ()
stkA?-⟹ {C = dpay _ _ _} _ ()
stkA?-⟹ {C = dih _ _ _ _} _ ()
stkA?-⟹ {C = fzero} _ ()
stkA?-⟹ {C = fsuc _} _ ()
stkA?-⟹ {C = fcase _ _ _} _ ()
stkA?-⟹ {C = fcase0 _} _ ()
stkA?-⟹ {C = psplit _ _} _ ()
stkA?-⟹ {C = ⌜Nat⌝} p⌜Nat⌝ h = refl
stkA?-⟹ {C = ⌜IMu⌝ _ _ _} (p⌜IMu⌝ _ _ _) h = refl
stkA?-⟹ {C = ⌜Fin⌝ _} (p⌜Fin⌝ _) h = refl
stkA?-⟹ {C = ⌜Unit⌝} p⌜Unit⌝ h = refl

-- split on the SOURCE's head first: a non-key head is refuted on the key
-- alone, a key head admits one derivation constructor (2026-09-30: the
-- derivation-first form spent ~25 s unifying all 72 constructors' indices).
stkC?-⟹ : {C C' : RTm Γ} → C ⟹ C' → stkC? C ≡ true → stkC? C' ≡ true
stkC?-⟹ {C = var _} _ ()
stkC?-⟹ {C = lam _} _ ()
stkC?-⟹ {C = app _ _} _ ()
stkC?-⟹ {C = pair _ _} _ ()
stkC?-⟹ {C = absurd _ _} _ ()
stkC?-⟹ {C = ordtr _ _ _ _ _} _ ()
stkC?-⟹ {C = fst _} _ ()
stkC?-⟹ {C = snd _} _ ()
stkC?-⟹ {C = ⌜base⌝} p⌜base⌝ h = refl
stkC?-⟹ {C = ⌜Π⌝ _ _} _ ()
stkC?-⟹ {C = ⌜Σ⌝ _ _} (p⌜Σ⌝ _ _) h = refl
stkC?-⟹ {C = ⌜Hom⌝ _ _ _} (p⌜Hom⌝ pc _ _) h = stkA?-⟹ pc h
stkC?-⟹ {C = hrefl _ _} _ ()
stkC?-⟹ {C = tr _ _ _} _ ()
stkC?-⟹ {C = ap _ _ _} _ ()
stkC?-⟹ {C = ⌜Id⌝ _ _ _} (p⌜Id⌝ _ _ _) h = refl
stkC?-⟹ {C = idrefl _ _} _ ()
stkC?-⟹ {C = jsub _ _ _} _ ()
stkC?-⟹ {C = unit} _ ()
stkC?-⟹ {C = nzero} _ ()
stkC?-⟹ {C = nsuc _} _ ()
stkC?-⟹ {C = natrec _ _ _} _ ()
stkC?-⟹ {C = con _} _ ()
stkC?-⟹ {C = ielim _ _ _ _} _ ()
stkC?-⟹ {C = dι} _ ()
stkC?-⟹ {C = dσ _ _} _ ()
stkC?-⟹ {C = dρ _ _} _ ()
stkC?-⟹ {C = dpay _ _ _} _ ()
stkC?-⟹ {C = dih _ _ _ _} _ ()
stkC?-⟹ {C = fzero} _ ()
stkC?-⟹ {C = fsuc _} _ ()
stkC?-⟹ {C = fcase _ _ _} _ ()
stkC?-⟹ {C = fcase0 _} _ ()
stkC?-⟹ {C = psplit _ _} _ ()
stkC?-⟹ {C = ⌜Nat⌝} _ ()
stkC?-⟹ {C = ⌜IMu⌝ _ _ _} (p⌜IMu⌝ _ _ _) h = refl
stkC?-⟹ {C = ⌜Fin⌝ _} (p⌜Fin⌝ _) h = refl
stkC?-⟹ {C = ⌜Unit⌝} p⌜Unit⌝ h = refl



⟶→⟹ : {t u : RTm Γ} → t ⟶ u → t ⟹ u
⟶→⟹ (tr-J-Unit _ _ _ _ e) = ptr-J-Unit (⟹-refl e)
⟶→⟹ (tr-J-Fin _ _ _ _ e)  = ptr-J-Fin (⟹-refl e)
⟶→⟹ (ι D i e p) = pι (⟹-refl D) (⟹-refl i) (⟹-refl e) (⟹-refl p)
⟶→⟹ (dpay-ι I D) = pdpay-ι
⟶→⟹ (dpay-σ I D S f) = pdpay-σ (⟹-refl I) (⟹-refl D) (⟹-refl S) (⟹-refl f)
⟶→⟹ (dpay-ρ I D j C) = pdpay-ρ (⟹-refl I) (⟹-refl D) (⟹-refl j) (⟹-refl C)
⟶→⟹ (dih-ι D e p) = pdih-ι
⟶→⟹ (dih-σ D e S f p) = pdih-σ (⟹-refl D) (⟹-refl e) (⟹-refl f) (⟹-refl p)
⟶→⟹ (dih-ρ D e j C p) = pdih-ρ (⟹-refl D) (⟹-refl e) (⟹-refl j) (⟹-refl C) (⟹-refl p)
⟶→⟹ (fcase-z a b) = pfcase-z (⟹-refl a)
⟶→⟹ (fcase-s t a b) = pfcase-s (⟹-refl t) (⟹-refl b)
⟶→⟹ (psplit-β b x y) = ppsplit-β (⟹-refl b) (⟹-refl x) (⟹-refl y)
⟶→⟹ (δref d p) = pdelta p
⟶→⟹ (ξ-⌜IMu⌝ᴵ r) = p⌜IMu⌝ (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-⌜IMu⌝ᴰ r) = p⌜IMu⌝ (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-⌜IMu⌝ⁱ r) = p⌜IMu⌝ (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-con r) = pcon (⟶→⟹ r)
⟶→⟹ (ξ-ielimᴰ r) = pielim (⟶→⟹ r) (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-ielimⁱ r) = pielim (⟹-refl _) (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-ielimᵉ r) = pielim (⟹-refl _) (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-ielimᵗ r) = pielim (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-dσˢ r) = pdσ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-dσᶠ r) = pdσ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-dρʲ r) = pdρ (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-dρᶜ r) = pdρ (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-dpayᴵ r) = pdpay (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-dpayᴰ r) = pdpay (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-dpayᶜ r) = pdpay (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-dihᴰ r) = pdih (⟶→⟹ r) (⟹-refl _) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-dihᵉ r) = pdih (⟹-refl _) (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-dihᶜ r) = pdih (⟹-refl _) (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-dihᵖ r) = pdih (⟹-refl _) (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-fsuc r) = pfsuc (⟶→⟹ r)
⟶→⟹ (ξ-fcaseᵗ r) = pfcase (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-fcaseᵃ r) = pfcase (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-fcaseᵇ r) = pfcase (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-fcase0 r) = pfcase0 (⟶→⟹ r)
⟶→⟹ (ξ-psplitᵇ r) = ppsplit (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-psplitᵍ r) = ppsplit (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (tr-J-IMu _ _ _ _ e)  = ptr-J-IMu (⟹-refl e)
⟶→⟹ (natrec-zero z s)  = pnatrec-zero (⟹-refl z) (⟹-refl s)
⟶→⟹ (natrec-suc z s n) = pnatrec-suc (⟹-refl z) (⟹-refl s) (⟹-refl n)
⟶→⟹ (ξ-nsuc r)    = pnsuc (⟶→⟹ r)
⟶→⟹ (ξ-⌜Fin⌝ r)   = p⌜Fin⌝ (⟶→⟹ r)
⟶→⟹ (ξ-natrecᶻ r) = pnatrec (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-natrecˢ r) = pnatrec (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-natrecⁿ r) = pnatrec (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
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
⟶→⟹ hrefl-Nat-z        = phrefl-Nat-z
⟶→⟹ (hrefl-Nat-s m)    = phrefl-Nat-s (⟹-refl m)
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
⟹→⟶* punit      = done
⟹→⟶* pnzero     = done
⟹→⟶* (pnsuc p)  = ⟶*-nsuc (⟹→⟶* p)
⟹→⟶* (p⌜IMu⌝ pI pD pi) =
  ⟶*-trans (⟶*-⌜IMu⌝ᴵ (⟹→⟶* pI)) (⟶*-trans (⟶*-⌜IMu⌝ᴰ (⟹→⟶* pD)) (⟶*-⌜IMu⌝ⁱ (⟹→⟶* pi)))
⟹→⟶* (p⌜Fin⌝ p) = ⟶*-⌜Fin⌝ (⟹→⟶* p)
⟹→⟶* (pcon p) = ⟶*-con (⟹→⟶* p)
⟹→⟶* (pielim pD pi pe pt) =
  ⟶*-trans (⟶*-ielimᴰ (⟹→⟶* pD)) (⟶*-trans (⟶*-ielimⁱ (⟹→⟶* pi))
    (⟶*-trans (⟶*-ielimᵉ (⟹→⟶* pe)) (⟶*-ielimᵗ (⟹→⟶* pt))))
⟹→⟶* (pι {D = D} {i = i} {e = e} {p = p} pD pi pe pp) =
  step (ι D i e p)
    (⟶*-trans (⟶*-appˡ (⟶*-trans (⟶*-appˡ (⟶*-trans (⟶*-appˡ (⟹→⟶* pe)) (⟶*-appʳ (⟹→⟶* pi))))
                                  (⟶*-appʳ (⟹→⟶* pp))))
              (⟶*-appʳ (⟶*-trans (⟶*-dihᴰ (⟹→⟶* pD)) (⟶*-trans (⟶*-dihᵉ (⟹→⟶* pe))
                        (⟶*-trans (⟶*-dihᶜ (⟶*-trans (⟶*-appˡ (⟹→⟶* pD)) (⟶*-appʳ (⟹→⟶* pi))))
                                  (⟶*-dihᵖ (⟹→⟶* pp)))))))
⟹→⟶* pdι = done
⟹→⟶* (pdσ pS pf) = ⟶*-trans (⟶*-dσˢ (⟹→⟶* pS)) (⟶*-dσᶠ (⟹→⟶* pf))
⟹→⟶* (pdρ pj pC) = ⟶*-trans (⟶*-dρʲ (⟹→⟶* pj)) (⟶*-dρᶜ (⟹→⟶* pC))
⟹→⟶* (pdpay pI pD pC) =
  ⟶*-trans (⟶*-dpayᴵ (⟹→⟶* pI)) (⟶*-trans (⟶*-dpayᴰ (⟹→⟶* pD)) (⟶*-dpayᶜ (⟹→⟶* pC)))
⟹→⟶* (pdpay-ι {I = I} {D = D}) = step (dpay-ι I D) done
⟹→⟶* (pdpay-σ {I = I} {D = D} {S = S} {f = f} pI pD pS pf) =
  step (dpay-σ I D S f)
    (⟶*-trans (⟶*-⌜Σ⌝ˡ (⟹→⟶* pS))
      (⟶*-⌜Σ⌝ʳ (⟶*-trans (⟶*-dpayᴵ (⟶*-ren vs (⟹→⟶* pI)))
                 (⟶*-trans (⟶*-dpayᴰ (⟶*-ren vs (⟹→⟶* pD)))
                           (⟶*-dpayᶜ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pf))))))))
⟹→⟶* (pdpay-ρ {I = I} {D = D} {j = j} {C = C} pI pD pj pC) =
  step (dpay-ρ I D j C)
    (⟶*-trans (⟶*-⌜Σ⌝ˡ (⟶*-trans (⟶*-⌜IMu⌝ᴵ (⟹→⟶* pI))
                          (⟶*-trans (⟶*-⌜IMu⌝ᴰ (⟹→⟶* pD)) (⟶*-⌜IMu⌝ⁱ (⟹→⟶* pj)))))
      (⟶*-⌜Σ⌝ʳ (⟶*-trans (⟶*-dpayᴵ (⟶*-ren vs (⟹→⟶* pI)))
                 (⟶*-trans (⟶*-dpayᴰ (⟶*-ren vs (⟹→⟶* pD)))
                           (⟶*-dpayᶜ (⟶*-ren vs (⟹→⟶* pC)))))))
⟹→⟶* (pdih pD pe pC pp) =
  ⟶*-trans (⟶*-dihᴰ (⟹→⟶* pD)) (⟶*-trans (⟶*-dihᵉ (⟹→⟶* pe))
    (⟶*-trans (⟶*-dihᶜ (⟹→⟶* pC)) (⟶*-dihᵖ (⟹→⟶* pp))))
⟹→⟶* (pdih-ι {D = D} {e = e} {p = p}) = step (dih-ι D e p) done
⟹→⟶* (pdih-σ {D = D} {e = e} {S = S} {f = f} {p = p} pD pe pf pp) =
  step (dih-σ D e S f p)
    (⟶*-trans (⟶*-dihᴰ (⟹→⟶* pD)) (⟶*-trans (⟶*-dihᵉ (⟹→⟶* pe))
      (⟶*-trans (⟶*-dihᶜ (⟶*-trans (⟶*-appˡ (⟹→⟶* pf)) (⟶*-appʳ (⟶*-fst (⟹→⟶* pp)))))
                (⟶*-dihᵖ (⟶*-snd (⟹→⟶* pp))))))
⟹→⟶* (pdih-ρ {D = D} {e = e} {j = j} {C = C} {p = p} pD pe pj pC pp) =
  step (dih-ρ D e j C p)
    (⟶*-trans (⟶*-pairˡ (⟶*-trans (⟶*-ielimᴰ (⟹→⟶* pD)) (⟶*-trans (⟶*-ielimⁱ (⟹→⟶* pj))
                          (⟶*-trans (⟶*-ielimᵉ (⟹→⟶* pe)) (⟶*-ielimᵗ (⟶*-fst (⟹→⟶* pp)))))))
              (⟶*-pairʳ (⟶*-trans (⟶*-dihᴰ (⟹→⟶* pD)) (⟶*-trans (⟶*-dihᵉ (⟹→⟶* pe))
                          (⟶*-trans (⟶*-dihᶜ (⟹→⟶* pC)) (⟶*-dihᵖ (⟶*-snd (⟹→⟶* pp))))))))
⟹→⟶* pfzero = done
⟹→⟶* (pfsuc p) = ⟶*-fsuc (⟹→⟶* p)
⟹→⟶* (pfcase pt pa pb) =
  ⟶*-trans (⟶*-fcaseᵗ (⟹→⟶* pt)) (⟶*-trans (⟶*-fcaseᵃ (⟹→⟶* pa)) (⟶*-fcaseᵇ (⟹→⟶* pb)))
⟹→⟶* (pfcase-z {a = a} {b = b} pa) = step (fcase-z a b) (⟹→⟶* pa)
⟹→⟶* (pfcase-s {t = t} {t'} {a = a} {b = b} {b'} pt pb) =
  step (fcase-s t a b)
       (⟶*-trans (⟶*-sub (single t) (⟹→⟶* pb))
                 (subTm-monoˢ (single-mono (⟹→⟶* pt)) b'))
⟹→⟶* (pfcase0 p) = ⟶*-fcase0 (⟹→⟶* p)
⟹→⟶* pref = done
⟹→⟶* (pdelta {d = d} p) = step (δref d p) done
⟹→⟶* (ppsplit pb pq) = ⟶*-trans (⟶*-psplitᵇ (⟹→⟶* pb)) (⟶*-psplitᵍ (⟹→⟶* pq))
⟹→⟶* (ppsplit-β {b = b} {b'} {x = x} {x'} {y = y} {y'} pb px py) =
  step (psplit-β b x y)
       (⟶*-trans (⟶*-sub (single2 x y) (⟹→⟶* pb))
                 (subTm-monoˢ (λ { vz → ⟹→⟶* py ; (vs vz) → ⟹→⟶* px ; (vs (vs z)) → done }) b'))
⟹→⟶* (ptr-J-Fin {c = c} {a} {m} {s} {e} p) =
  step (tr-J-Fin c a m s e) (⟹→⟶* p)
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
⟹→⟶* phrefl-Nat-z = step hrefl-Nat-z done
⟹→⟶* (phrefl-Nat-s {m = m} p) = step (hrefl-Nat-s m) (⟶*-hreflᵃ (⟹→⟶* p))
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
⟹-ren ρ (ptr-J-Unit p) = ptr-J-Unit (⟹-ren ρ p)
⟹-ren ρ (p⌜IMu⌝ a b c) = p⌜IMu⌝ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)
⟹-ren ρ (p⌜Fin⌝ p) = p⌜Fin⌝ (⟹-ren ρ p)
⟹-ren ρ (pcon a) = pcon (⟹-ren ρ a)
⟹-ren ρ (pielim a b c d) = pielim (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d)
⟹-ren ρ (pι a b c d) = pι (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d)
⟹-ren ρ pdι = pdι
⟹-ren ρ (pdσ a b) = pdσ (⟹-ren ρ a) (⟹-ren ρ b)
⟹-ren ρ (pdρ a b) = pdρ (⟹-ren ρ a) (⟹-ren ρ b)
⟹-ren ρ (pdpay a b c) = pdpay (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c)
⟹-ren ρ pdpay-ι = pdpay-ι
⟹-ren ρ (pdpay-σ {I = I} {I'} {D = D} {D'} {S = S₀} {S'} {f = f} {f'} a b c d) =
  subst (λ z → renTm ρ (dpay I D (dσ S₀ f)) ⟹ z)
        (sym (cong₃ (λ w x y → ⌜Σ⌝ (renTm ρ S') (dpay w x (app y (var vz))))
                    (wk-ren ρ I') (wk-ren ρ D') (wk-ren ρ f')))
        (pdpay-σ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d))
⟹-ren ρ (pdpay-ρ {I = I} {I'} {D = D} {D'} {j = j} {j'} {C = C} {C'} a b c d) =
  subst (λ z → renTm ρ (dpay I D (dρ j C)) ⟹ z)
        (sym (cong₃ (λ w x y → ⌜Σ⌝ (⌜IMu⌝ (renTm ρ I') (renTm ρ D') (renTm ρ j')) (dpay w x y))
                    (wk-ren ρ I') (wk-ren ρ D') (wk-ren ρ C')))
        (pdpay-ρ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d))
⟹-ren ρ (pdih a b c d) = pdih (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d)
⟹-ren ρ pdih-ι = pdih-ι
⟹-ren ρ (pdih-σ a b c d) = pdih-σ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d)
⟹-ren ρ (pdih-ρ a b c d e) = pdih-ρ (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren ρ c) (⟹-ren ρ d) (⟹-ren ρ e)
⟹-ren ρ pfzero = pfzero
⟹-ren ρ (pfsuc a) = pfsuc (⟹-ren ρ a)
⟹-ren ρ (pfcase a b c) = pfcase (⟹-ren ρ a) (⟹-ren ρ b) (⟹-ren (extR ρ) c)
⟹-ren ρ (pfcase-z a) = pfcase-z (⟹-ren ρ a)
⟹-ren ρ (pfcase-s {t = t} {t'} {a = a} {b = b} {b'} pt pb) =
  subst (λ z → renTm ρ (fcase (fsuc t) a b) ⟹ z)
        (sym (ren-comm ρ b' t'))
        (pfcase-s (⟹-ren ρ pt) (⟹-ren (extR ρ) pb))
⟹-ren ρ (pfcase0 a) = pfcase0 (⟹-ren ρ a)
⟹-ren ρ pref = pref
⟹-ren ρ (pdelta {d = d} p) = subst (λ z → ref d ⟹ z) (sym (εwkTm-ren ρ (Defs.body 𝒮 d))) (pdelta p)
⟹-ren ρ (ppsplit a b) = ppsplit (⟹-ren (extR (extR ρ)) a) (⟹-ren ρ b)
⟹-ren ρ (ppsplit-β {b = b} {b'} {x = x} {x'} {y = y} {y'} pb px py) =
  subst (λ z → renTm ρ (psplit b (pair x y)) ⟹ z)
        (sym (ren-comm2 ρ b' x' y'))
        (ppsplit-β (⟹-ren (extR (extR ρ)) pb) (⟹-ren ρ px) (⟹-ren ρ py))
⟹-ren ρ (ptr-J-IMu a) = ptr-J-IMu (⟹-ren ρ a)
⟹-ren ρ (ptr-J-Fin a) = ptr-J-Fin (⟹-ren ρ a)
⟹-ren ρ punit      = punit
⟹-ren ρ pnzero     = pnzero
⟹-ren ρ (pnsuc p)  = pnsuc (⟹-ren ρ p)
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
⟹-ren ρ phrefl-Nat-z     = phrefl-Nat-z
⟹-ren ρ (phrefl-Nat-s p) = phrefl-Nat-s (⟹-ren ρ p)
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

-- split on the SOURCE's head first: a non-key head is refuted on the key
-- alone, a key head admits one derivation constructor (2026-09-30: the
-- derivation-first form spent ~25 s unifying all 72 constructors' indices).
pwBody-⟹ : {C C' : RTm Γ} → C ⟹ C' → pw? C ≡ true →
            pwBody C ⟹ pwBody C'
pwBody-⟹ {C = var _} _ ()
pwBody-⟹ {C = lam _} _ ()
pwBody-⟹ {C = app _ _} _ ()
pwBody-⟹ {C = pair _ _} _ ()
pwBody-⟹ {C = absurd _ _} _ ()
pwBody-⟹ {C = ordtr _ _ _ _ _} _ ()
pwBody-⟹ {C = fst _} _ ()
pwBody-⟹ {C = snd _} _ ()
pwBody-⟹ {C = ⌜base⌝} _ ()
pwBody-⟹ {C = ⌜Π⌝ _ _} (p⌜Π⌝ pγ pδ) h = pδ
pwBody-⟹ {C = ⌜Σ⌝ _ _} _ ()
pwBody-⟹ {C = ⌜Hom⌝ _ _ _} (p⌜Hom⌝ pc pa pb) h =
  p⌜Hom⌝ (pwBody-⟹ pc h)
         (papp (⟹-ren vs pa) (pvar vz))
         (papp (⟹-ren vs pb) (pvar vz))
pwBody-⟹ {C = hrefl _ _} _ ()
pwBody-⟹ {C = tr _ _ _} _ ()
pwBody-⟹ {C = ap _ _ _} _ ()
pwBody-⟹ {C = ⌜Id⌝ _ _ _} _ ()
pwBody-⟹ {C = idrefl _ _} _ ()
pwBody-⟹ {C = jsub _ _ _} _ ()
pwBody-⟹ {C = unit} _ ()
pwBody-⟹ {C = nzero} _ ()
pwBody-⟹ {C = nsuc _} _ ()
pwBody-⟹ {C = natrec _ _ _} _ ()
pwBody-⟹ {C = con _} _ ()
pwBody-⟹ {C = ielim _ _ _ _} _ ()
pwBody-⟹ {C = dι} _ ()
pwBody-⟹ {C = dσ _ _} _ ()
pwBody-⟹ {C = dρ _ _} _ ()
pwBody-⟹ {C = dpay _ _ _} _ ()
pwBody-⟹ {C = dih _ _ _ _} _ ()
pwBody-⟹ {C = fzero} _ ()
pwBody-⟹ {C = fsuc _} _ ()
pwBody-⟹ {C = fcase _ _ _} _ ()
pwBody-⟹ {C = fcase0 _} _ ()
pwBody-⟹ {C = psplit _ _} _ ()
pwBody-⟹ {C = ⌜Nat⌝} _ ()
pwBody-⟹ {C = ⌜IMu⌝ _ _ _} _ ()
pwBody-⟹ {C = ⌜Fin⌝ _} _ ()
pwBody-⟹ {C = ⌜Unit⌝} _ ()

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
⟹-sub h (ptr-J-Unit p) = ptr-J-Unit (⟹-sub h p)
⟹-sub h (p⌜IMu⌝ a b c) = p⌜IMu⌝ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c)
⟹-sub h (p⌜Fin⌝ p) = p⌜Fin⌝ (⟹-sub h p)
⟹-sub h (pcon a) = pcon (⟹-sub h a)
⟹-sub h (pielim a b c d) = pielim (⟹-sub h a) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d)
⟹-sub h (pι a b c d) = pι (⟹-sub h a) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d)
⟹-sub h pdι = pdι
⟹-sub h (pdσ a b) = pdσ (⟹-sub h a) (⟹-sub h b)
⟹-sub h (pdρ a b) = pdρ (⟹-sub h a) (⟹-sub h b)
⟹-sub h (pdpay a b c) = pdpay (⟹-sub h a) (⟹-sub h b) (⟹-sub h c)
⟹-sub h pdpay-ι = pdpay-ι
⟹-sub {σ = σ} {σ'} h (pdpay-σ {I = I} {I'} {D = D} {D'} {S = S₀} {S'} {f = f} {f'} a b c d) =
  subst (λ z → subTm σ (dpay I D (dσ S₀ f)) ⟹ z)
        (sym (cong₃ (λ w x y → ⌜Σ⌝ (subTm σ' S') (dpay w x (app y (var vz))))
                    (wk-sub σ' I') (wk-sub σ' D') (wk-sub σ' f')))
        (pdpay-σ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d))
⟹-sub {σ = σ} {σ'} h (pdpay-ρ {I = I} {I'} {D = D} {D'} {j = j} {j'} {C = C} {C'} a b c d) =
  subst (λ z → subTm σ (dpay I D (dρ j C)) ⟹ z)
        (sym (cong₃ (λ w x y → ⌜Σ⌝ (⌜IMu⌝ (subTm σ' I') (subTm σ' D') (subTm σ' j')) (dpay w x y))
                    (wk-sub σ' I') (wk-sub σ' D') (wk-sub σ' C')))
        (pdpay-ρ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d))
⟹-sub h (pdih a b c d) = pdih (⟹-sub h a) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d)
⟹-sub h pdih-ι = pdih-ι
⟹-sub h (pdih-σ a b c d) = pdih-σ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d)
⟹-sub h (pdih-ρ a b c d e) = pdih-ρ (⟹-sub h a) (⟹-sub h b) (⟹-sub h c) (⟹-sub h d) (⟹-sub h e)
⟹-sub h pfzero = pfzero
⟹-sub h (pfsuc a) = pfsuc (⟹-sub h a)
⟹-sub h (pfcase a b c) = pfcase (⟹-sub h a) (⟹-sub h b) (⟹-sub (⟹-exts h) c)
⟹-sub h (pfcase-z a) = pfcase-z (⟹-sub h a)
⟹-sub {σ = σ} {σ'} h (pfcase-s {t = t} {t'} {a = a} {b = b} {b'} pt pb) =
  subst (λ z → subTm σ (fcase (fsuc t) a b) ⟹ z)
        (sym (sub-comm σ' b' t'))
        (pfcase-s (⟹-sub h pt) (⟹-sub (⟹-exts h) pb))
⟹-sub h (pfcase0 a) = pfcase0 (⟹-sub h a)
⟹-sub h pref = pref
⟹-sub {σ' = σ'} h (pdelta {d = d} p) = subst (λ z → ref d ⟹ z) (sym (εwkTm-sub σ' (Defs.body 𝒮 d))) (pdelta p)
⟹-sub h (ppsplit a b) = ppsplit (⟹-sub (⟹-exts (⟹-exts h)) a) (⟹-sub h b)
⟹-sub {σ = σ} {σ'} h (ppsplit-β {b = b} {b'} {x = x} {x'} {y = y} {y'} pb px py) =
  subst (λ z → subTm σ (psplit b (pair x y)) ⟹ z)
        (sym (sub-comm2 σ' b' x' y'))
        (ppsplit-β (⟹-sub (⟹-exts (⟹-exts h)) pb) (⟹-sub h px) (⟹-sub h py))
⟹-sub h (ptr-J-IMu a) = ptr-J-IMu (⟹-sub h a)
⟹-sub h (ptr-J-Fin a) = ptr-J-Fin (⟹-sub h a)
⟹-sub h punit      = punit
⟹-sub h pnzero     = pnzero
⟹-sub h (pnsuc p)  = pnsuc (⟹-sub h p)
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
⟹-sub h phrefl-Nat-z     = phrefl-Nat-z
⟹-sub h (phrefl-Nat-s p) = phrefl-Nat-s (⟹-sub h p)
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

single-⟹ : {u u' : RTm Γ} → u ⟹ u' →
           (x : Var (Γ ∙)) → single u x ⟹ single u' x
single-⟹ p vz     = p
single-⟹ p (vs x) = pvar x

single2-⟹ : {x x' y y' : RTm Γ} → x ⟹ x' → y ⟹ y' →
            (z : Var ((Γ ∙) ∙)) → single2 x y z ⟹ single2 x' y' z
single2-⟹ px py vz          = py
single2-⟹ px py (vs vz)     = px
single2-⟹ px py (vs (vs z)) = pvar z

------------------------------------------------------------------------
-- The complete development, and the triangle: `t ⟹ u → u ⟹ t⁺`.
--
-- ★ REDEX VIEWS (2026-09-30).  Each eliminator decides its redex by a
--   VIEW of its ORIGINAL scrutinee — `lam`, `pair`, a numeral, `idrefl`,
--   `con`, a tag, a telescope head, the `tr`/`ap` path shapes — computed
--   by a one-level function with a catch-all.  `_⁺` develops THROUGH the
--   view, and reads the redex's pieces off the DEVELOPED subterms
--   (`lam b ⁺ = lam (b ⁺)`), so it stays structurally recursive; the
--   Boolean keys (`pw?`, `stkA?`, `stkC?`) are still decided on the
--   original, as Takahashi requires.
--
--   The views are NON-EXCLUSIVE: the catch-all constructor claims
--   nothing, because a congruence step is always a valid parallel step.
--   So every triangle helper below holds for ANY view value, and `⟹-⁺`
--   has ONE clause per `_⟹_` constructor.
--
--   ⚠ WHY.  `_⁺` used to end each eliminator with a catch-all congruence
--   clause, which reduces only once the scrutinee's HEAD is known — so
--   the triangle split every scrutinee's derivation on every head,
--   recursively: 3 232 clauses, and 377 s of termination checking and
--   elaboration per cold build (the 2026-09-30 profile, the build's
--   largest site).  At every concrete head `_⁺` has the same normal forms
--   as before.
------------------------------------------------------------------------

private
  bool-⊥ : {A : Set} → true ≡ false → A
  bool-⊥ ()

-- ── the views ──────────────────────────────────────────────────────────

data LamV {Γ : Cx} : RTm Γ → Set where
  isLam  : (b : RTm (Γ ∙)) → LamV (lam b)
  notLam : {t : RTm Γ} → LamV t

lamV : (t : RTm Γ) → LamV t
lamV (lam b) = isLam b
lamV _       = notLam

data PairV {Γ : Cx} : RTm Γ → Set where
  isPair  : (a b : RTm Γ) → PairV (pair a b)
  notPair : {t : RTm Γ} → PairV t

pairV : (t : RTm Γ) → PairV t
pairV (pair a b) = isPair a b
pairV _          = notPair

-- ★ F6: an `hrefl` at the order, at a numeral head (`hrefl-Nat-z/s`)
data HrV {Γ : Cx} : RTm Γ → RTm Γ → Set where
  hvZ : HrV ⌜Nat⌝ nzero
  hvS : (m : RTm Γ) → HrV ⌜Nat⌝ (nsuc m)
  hvO : {c t : RTm Γ} → HrV c t

hrV : (c t : RTm Γ) → HrV c t
hrV ⌜Nat⌝ nzero    = hvZ
hrV ⌜Nat⌝ (nsuc m) = hvS m
hrV _     _        = hvO

data NatV {Γ : Cx} : RTm Γ → Set where
  isZ    : NatV nzero
  isS    : (n : RTm Γ) → NatV (nsuc n)
  notNat : {t : RTm Γ} → NatV t

natV : (t : RTm Γ) → NatV t
natV nzero    = isZ
natV (nsuc n) = isS n
natV _        = notNat

data IdreflV {Γ : Cx} : RTm Γ → Set where
  isIdrefl  : (c s : RTm Γ) → IdreflV (idrefl c s)
  notIdrefl : {t : RTm Γ} → IdreflV t

idreflV : (t : RTm Γ) → IdreflV t
idreflV (idrefl c s) = isIdrefl c s
idreflV _            = notIdrefl

data ConV {Γ : Cx} : RTm Γ → Set where
  isCon  : (p : RTm Γ) → ConV (con p)
  notCon : {t : RTm Γ} → ConV t

conV : (t : RTm Γ) → ConV t
conV (con p) = isCon p
conV _       = notCon

data FinV {Γ : Cx} : RTm Γ → Set where
  isFz   : FinV fzero
  isFs   : (t : RTm Γ) → FinV (fsuc t)
  notFin : {t : RTm Γ} → FinV t

finV : (t : RTm Γ) → FinV t
finV fzero    = isFz
finV (fsuc t) = isFs t
finV _        = notFin

data DescV {Γ : Cx} : RTm Γ → Set where
  isι     : DescV dι
  isσ     : (S f : RTm Γ) → DescV (dσ S f)
  isρ     : (j C : RTm Γ) → DescV (dρ j C)
  notDesc : {t : RTm Γ} → DescV t

descV : (t : RTm Γ) → DescV t
descV dι       = isι
descV (dσ S f) = isσ S f
descV (dρ j C) = isρ j C
descV _        = notDesc

-- the codes `tr`'s J fires at: the six stable heads unconditionally,
-- `⌜Hom⌝` under `stkA?` of its ambient (`jcKey`).  ⌜Nat⌝ is not here —
-- J is disabled at an ordered ambient (WF stage C).
data JC {Γ : Cx} : RTm Γ → Set where
  jcUnit : JC ⌜Unit⌝
  jcIMu  : (I D i : RTm Γ) → JC (⌜IMu⌝ I D i)
  jcFin  : (n : RTm Γ) → JC (⌜Fin⌝ n)
  jcBase : JC ⌜base⌝
  jcΣ    : (c : RTm Γ) (d : RTm (Γ ∙)) → JC (⌜Σ⌝ c d)
  jcId   : (c a b : RTm Γ) → JC (⌜Id⌝ c a b)
  jcHom  : (c a b : RTm Γ) → JC (⌜Hom⌝ c a b)

jcKey : {C : RTm Γ} → JC C → 𝔹
jcKey (jcHom c _ _) = stkA? c
jcKey _             = true

-- `tr`: J on a canonical path at a ⌜Hom⌝ motive, the tautological
-- motive, the pointwise composition — or congruence.
data TrV {Γ : Cx} : RTm (Γ ∙) → RTm Γ → Set where
  trJ    : (c a m : RTm (Γ ∙)) {C : RTm Γ} → JC C → (s : RTm Γ) → TrV (⌜Hom⌝ c a m) (hrefl C s)
  trTaut : (f : RTm (Γ ∙)) → TrV (var vz) (lam f)
  trPw   : (c a f : RTm (Γ ∙)) → TrV (⌜Hom⌝ c a (var vz)) (lam f)
  trCong : {d : RTm (Γ ∙)} {p : RTm Γ} → TrV d p

trV : (d : RTm (Γ ∙)) (p : RTm Γ) → TrV d p
trV (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s)          = trJ c a m jcUnit s
trV (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ I D i) s)   = trJ c a m (jcIMu I D i) s
trV (⌜Hom⌝ c a m) (hrefl (⌜Fin⌝ n) s)       = trJ c a m (jcFin n) s
trV (⌜Hom⌝ c a m) (hrefl ⌜base⌝ s)          = trJ c a m jcBase s
trV (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s)     = trJ c a m (jcΣ c₁ c₂) s
trV (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) = trJ c a m (jcId c₁ a₁ b₁) s
trV (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) = trJ c a m (jcHom c₁ a₁ b₁) s
trV (var vz) (lam f)                        = trTaut f
trV (⌜Hom⌝ c a (var vz)) (lam f)            = trPw c a f
trV _ _                                     = trCong

-- `ap`: J on a canonical path at a stable code (`stkC?`) — or congruence.
data ApV {Γ : Cx} : RTm Γ → Set where
  apJ    : (C s : RTm Γ) → ApV (hrefl C s)
  apCong : {p : RTm Γ} → ApV p

apV : (p : RTm Γ) → ApV p
apV (hrefl C s) = apJ C s
apV _           = apCong

-- ── the developments, at DEVELOPED pieces ──────────────────────────────

-- W2b: `hrefl` unfolds POINTWISE at pw-able codes (the Boolean decided
-- on the ORIGINAL code; the pieces developed).
hr⁺ : 𝔹 → RTm Γ → RTm Γ → RTm Γ
hr⁺ true  C T = lam (hrefl (pwBody C) (app (renTm vs T) (var vz)))
hr⁺ false C T = hrefl C T

-- …and at the order (the view decided on the ORIGINAL term)
hrK : {c t : RTm Γ} → HrV c t → 𝔹 → RTm Γ → RTm Γ → RTm Γ
hrK hvZ     b C T        = unit
hrK (hvS _) b C (nsuc M) = hrefl ⌜Nat⌝ M
hrK (hvS _) b C T        = hrefl C T
hrK hvO     b C T        = hr⁺ b C T

-- a code that is not `⌜Nat⌝` is no order code (`pw?`/`stkC?` both refute it)
hrK-not : {c t : RTm Γ} {b : 𝔹} {C T : RTm Γ} → (c ≡ ⌜Nat⌝ → ⊥) → hrK (hrV c t) b C T ≡ hr⁺ b C T
hrK-not {c = ⌜Nat⌝} n = ⊥-elim (n refl)
hrK-not {c = var _} _ = refl
hrK-not {c = lam _} _ = refl
hrK-not {c = app _ _} _ = refl
hrK-not {c = pair _ _} _ = refl
hrK-not {c = absurd _ _} _ = refl
hrK-not {c = ordtr _ _ _ _ _} _ = refl
hrK-not {c = fst _} _ = refl
hrK-not {c = snd _} _ = refl
hrK-not {c = ⌜base⌝} _ = refl
hrK-not {c = ⌜Π⌝ _ _} _ = refl
hrK-not {c = ⌜Σ⌝ _ _} _ = refl
hrK-not {c = ⌜Hom⌝ _ _ _} _ = refl
hrK-not {c = hrefl _ _} _ = refl
hrK-not {c = tr _ _ _} _ = refl
hrK-not {c = ap _ _ _} _ = refl
hrK-not {c = ⌜Id⌝ _ _ _} _ = refl
hrK-not {c = idrefl _ _} _ = refl
hrK-not {c = jsub _ _ _} _ = refl
hrK-not {c = unit} _ = refl
hrK-not {c = nzero} _ = refl
hrK-not {c = nsuc _} _ = refl
hrK-not {c = natrec _ _ _} _ = refl
hrK-not {c = con _} _ = refl
hrK-not {c = ielim _ _ _ _} _ = refl
hrK-not {c = dι} _ = refl
hrK-not {c = dσ _ _} _ = refl
hrK-not {c = dρ _ _} _ = refl
hrK-not {c = dpay _ _ _} _ = refl
hrK-not {c = dih _ _ _ _} _ = refl
hrK-not {c = fzero} _ = refl
hrK-not {c = fsuc _} _ = refl
hrK-not {c = fcase _ _ _} _ = refl
hrK-not {c = fcase0 _} _ = refl
hrK-not {c = psplit _ _} _ = refl
hrK-not {c = ⌜IMu⌝ _ _ _} _ = refl
hrK-not {c = ⌜Fin⌝ _} _ = refl
hrK-not {c = ⌜Unit⌝} _ = refl
hrK-not {c = ref _} _ = refl

pw-notNat : {c : RTm Γ} → pw? c ≡ true → c ≡ ⌜Nat⌝ → ⊥
pw-notNat () refl

stk-notNat : {c : RTm Γ} → stkC? c ≡ true → c ≡ ⌜Nat⌝ → ⊥
stk-notNat () refl

hrK-pw : {c t : RTm Γ} {b : 𝔹} {C T : RTm Γ} → pw? c ≡ true → hrK (hrV c t) b C T ≡ hr⁺ b C T
hrK-pw {c = c} {t} k = hrK-not {c = c} {t = t} (pw-notNat k)

hrK-stk : {c t : RTm Γ} {b : 𝔹} {C T : RTm Γ} → stkC? c ≡ true → hrK (hrV c t) b C T ≡ hr⁺ b C T
hrK-stk {c = c} {t} k = hrK-not {c = c} {t = t} (stk-notNat k)

appK : {t : RTm Γ} → LamV t → RTm Γ → RTm Γ → RTm Γ
appK (isLam _) (lam b') u' = subTm (single u') b'
appK _         t'       u' = app t' u'

fstK sndK : {p : RTm Γ} → PairV p → RTm Γ → RTm Γ
fstK (isPair _ _) (pair a' _) = a'
fstK _            p'          = fst p'
sndK (isPair _ _) (pair _ b') = b'
sndK _            p'          = snd p'

psK : {q : RTm Γ} → PairV q → RTm ((Γ ∙) ∙) → RTm Γ → RTm Γ
psK (isPair _ _) b' (pair x' y') = subTm (single2 x' y') b'
psK _            b' q'           = psplit b' q'

natK : {n : RTm Γ} → NatV n → RTm Γ → RTm ((Γ ∙) ∙) → RTm Γ → RTm Γ
natK isZ     z' s' n'        = z'
natK (isS _) z' s' (nsuc n') = subTm (single (natrec z' s' n')) (subTm (extS (single n')) s')
natK _       z' s' n'        = natrec z' s' n'

jsK : {p : RTm Γ} → IdreflV p → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
jsK (isIdrefl _ _) d' p' e' = e'
jsK _              d' p' e' = jsub d' p' e'

ielK : {t : RTm Γ} → ConV t → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ielK (isCon _) D' i' e' (con p') = app (app (app e' i') p') (dih D' e' (app D' i') p')
ielK _         D' i' e' t'       = ielim D' i' e' t'

fcK : {t : RTm Γ} → FinV t → RTm Γ → RTm Γ → RTm (Γ ∙) → RTm Γ
fcK isFz     t'        a' b' = a'
fcK (isFs _) (fsuc t') a' b' = subTm (single t') b'
fcK _        t'        a' b' = fcase t' a' b'

dpK : {C : RTm Γ} → DescV C → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dpK isι       I' D' C'         = ⌜Unit⌝
dpK (isσ _ _) I' D' (dσ S' f') =
  ⌜Σ⌝ S' (dpay (renTm vs I') (renTm vs D') (app (renTm vs f') (var vz)))
dpK (isρ _ _) I' D' (dρ j' C') =
  ⌜Σ⌝ (⌜IMu⌝ I' D' j') (dpay (renTm vs I') (renTm vs D') (renTm vs C'))
dpK _         I' D' C'         = dpay I' D' C'

dihK : {C : RTm Γ} → DescV C → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dihK isι       D' e' C'         p' = unit
dihK (isσ _ _) D' e' (dσ S' f') p' = dih D' e' (app f' (fst p')) (snd p')
dihK (isρ _ _) D' e' (dρ j' C') p' = pair (ielim D' j' e' (fst p')) (dih D' e' C' (snd p'))
dihK _         D' e' C'         p' = dih D' e' C' p'

-- the order dispatches `a`, then `u`, then `t`.
-- ⚠ peel ONCE.  Takahashi's development fires the redexes present in
-- the ORIGINAL term; the `ordtr a t u p q` that the `nsuc` row exposes is
-- a NEW redex created by the step, and re-firing it breaks the triangle.
ordK : {a t u : RTm Γ} → NatV a → NatV u → NatV t → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ordK isZ     _       _       a'         t'         u'         p' q' = unit
ordK (isS _) isZ     isZ     a'         t'         u'         p' q' = p'
ordK (isS _) isZ     (isS _) a'         t'         u'         p' q' = q'
ordK (isS _) (isS _) isZ     (nsuc a'') t'         (nsuc u'') p' q' = absurd (⌜Hom⌝ ⌜Nat⌝ a'' u'') p'
ordK (isS _) (isS _) (isS _) (nsuc a'') (nsuc t'') (nsuc u'') p' q' = ordtr a'' t'' u'' p' q'
ordK _       _       _       a'         t'         u'         p' q' = ordtr a' t' u' p' q'

jK : 𝔹 → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
jK true  d' p' e' = e'
jK false d' p' e' = tr d' p' e'

pwK : 𝔹 → RTm (Γ ∙) → RTm (Γ ∙) → RTm (Γ ∙) → RTm Γ → RTm Γ
pwK true  c' a' f' e' =
  lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c')) (app (renTm vs a') (var (vs vz))) (var vz))
          f'
          (app (renTm vs e') (var vz)))
pwK false c' a' f' e' = tr (⌜Hom⌝ c' a' (var vz)) (lam f') e'

trK : {d : RTm (Γ ∙)} {p : RTm Γ} → TrV d p → RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
trK (trJ _ _ _ jc _) d'                p'       e' = jK (jcKey jc) d' p' e'
trK (trTaut _)       d'                (lam f') e' = app (lam f') e'
trK (trPw c _ _)     (⌜Hom⌝ c' a' _)   (lam f') e' = pwK (pw? c) c' a' f' e'
trK _                d'                p'       e' = tr d' p' e'

apJK : 𝔹 → RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ
apJK true cB' b' (hrefl _ s') = hrefl cB' (subTm (single s') b')
apJK _    cB' b' p'           = ap cB' b' p'

apK : {p : RTm Γ} → ApV p → RTm Γ → RTm (Γ ∙) → RTm Γ → RTm Γ
apK (apJ C _) cB' b' p' = apJK (stkC? C) cB' b' p'
apK apCong    cB' b' p' = ap cB' b' p'

-- ★ a reference develops to its unfolding when it is in the signature
--   (PLAN-REF): ONE δ step, the body not developed — its only parallel
--   reducts are itself and that unfolding, so the triangle needs no
--   recursion into the signature
refDev : (d : ℕ) → Dec (d <ˢ Defs.size 𝒮) → RTm Γ
refDev d (yes _) = εwkTm (Defs.body 𝒮 d)
refDev d (no _)  = ref d

-- ── the complete development ───────────────────────────────────────────

_⁺ : RTm Γ → RTm Γ
var x ⁺            = var x
lam t ⁺            = lam (t ⁺)
pair a b ⁺         = pair (a ⁺) (b ⁺)
app t u ⁺          = appK (lamV t) (t ⁺) (u ⁺)
ref d ⁺            = refDev d (d <ˢ? Defs.size 𝒮)
fst p ⁺            = fstK (pairV p) (p ⁺)
snd p ⁺            = sndK (pairV p) (p ⁺)
⌜Nat⌝ ⁺            = ⌜Nat⌝
⌜Unit⌝ ⁺           = ⌜Unit⌝
⌜base⌝ ⁺           = ⌜base⌝
⌜Π⌝ c d ⁺          = ⌜Π⌝ (c ⁺) (d ⁺)
⌜Σ⌝ c d ⁺          = ⌜Σ⌝ (c ⁺) (d ⁺)
⌜Hom⌝ c a b ⁺      = ⌜Hom⌝ (c ⁺) (a ⁺) (b ⁺)
hrefl c f ⁺        = hrK (hrV c f) (pw? c) (c ⁺) (f ⁺)
tr d p e ⁺         = trK (trV d p) (d ⁺) (p ⁺) (e ⁺)
ap cB b p ⁺        = apK (apV p) (cB ⁺) (b ⁺) (p ⁺)
ordtr a t u p q ⁺  = ordK (natV a) (natV u) (natV t) (a ⁺) (t ⁺) (u ⁺) (p ⁺) (q ⁺)
absurd c e ⁺       = absurd (c ⁺) (e ⁺)
⌜Id⌝ c a b ⁺       = ⌜Id⌝ (c ⁺) (a ⁺) (b ⁺)
idrefl c t ⁺       = idrefl (c ⁺) (t ⁺)
jsub d p e ⁺       = jsK (idreflV p) (d ⁺) (p ⁺) (e ⁺)
unit ⁺             = unit
nzero ⁺            = nzero
nsuc n ⁺           = nsuc (n ⁺)
natrec z s n ⁺     = natK (natV n) (z ⁺) (s ⁺) (n ⁺)
⌜IMu⌝ I D i ⁺      = ⌜IMu⌝ (I ⁺) (D ⁺) (i ⁺)
⌜Fin⌝ n ⁺          = ⌜Fin⌝ (n ⁺)
con c ⁺            = con (c ⁺)
ielim D i e t ⁺    = ielK (conV t) (D ⁺) (i ⁺) (e ⁺) (t ⁺)
dι ⁺               = dι
dσ S f ⁺           = dσ (S ⁺) (f ⁺)
dρ j C ⁺           = dρ (j ⁺) (C ⁺)
dpay I D C ⁺       = dpK (descV C) (I ⁺) (D ⁺) (C ⁺)
dih D e C p ⁺      = dihK (descV C) (D ⁺) (e ⁺) (C ⁺) (p ⁺)
fzero ⁺            = fzero
fsuc t ⁺           = fsuc (t ⁺)
fcase t a b ⁺      = fcK (finV t) (t ⁺) (a ⁺) (b ⁺)
fcase0 t ⁺         = fcase0 (t ⁺)
psplit b q ⁺       = psK (pairV q) (b ⁺) (q ⁺)

tri-ref : (d : ℕ) (q : Dec (d <ˢ Defs.size 𝒮)) → ref {Γ} d ⟹ refDev d q
tri-ref d (yes p) = pdelta p
tri-ref d (no _)  = pref

tri-δ : (d : ℕ) → d <ˢ Defs.size 𝒮 → (q : Dec (d <ˢ Defs.size 𝒮)) →
        εwkTm {Γ} (Defs.body 𝒮 d) ⟹ refDev d q
tri-δ d p (yes _) = ⟹-refl _
tri-δ d p (no ¬p) = ⊥-elim (¬p p)

-- ── the triangle, one helper per eliminator ────────────────────────────
-- Each takes the view, the scrutinee's step, and the IHs; the redex
-- constructor pins the step's shape, and anything else is congruence.

hr-tri : {C' X s' Y : RTm Γ} (b : 𝔹) → (b ≡ true → pw? C' ≡ true) →
         C' ⟹ X → s' ⟹ Y → hrefl C' s' ⟹ hr⁺ b X Y
hr-tri true  kf px py = phrefl-pw (kf refl) px py
hr-tri false kf px py = phrefl px py

-- ★ F6: the order's reflexivity
tri-hr : {c c' f f' X Y : RTm Γ} (v : HrV c f) → c ⟹ c' → f ⟹ f' →
         (pw? c ≡ true → pw? c' ≡ true) → c' ⟹ X → f' ⟹ Y → hrefl c' f' ⟹ hrK v (pw? c) X Y
tri-hr hvZ     p⌜Nat⌝ pnzero    kf rx ry        = phrefl-Nat-z
tri-hr (hvS _) p⌜Nat⌝ (pnsuc _) kf rx (pnsuc r) = phrefl-Nat-s r
tri-hr hvO     _      _         kf rx ry        = hr-tri _ kf rx ry

tri-app : {t t' u' U : RTm Γ} (v : LamV t) → t ⟹ t' → t' ⟹ t ⁺ → u' ⟹ U →
          app t' u' ⟹ appK v (t ⁺) U
tri-app (isLam _) (plam _) (plam r) q = pβ r q
tri-app notLam    _        r        q = papp r q

tri-fst : {p p' : RTm Γ} (v : PairV p) → p ⟹ p' → p' ⟹ p ⁺ → fst p' ⟹ fstK v (p ⁺)
tri-fst (isPair _ _) (ppair _ _) (ppair ra rb) = pβfst ra rb
tri-fst notPair      _           r             = pfst r

tri-snd : {p p' : RTm Γ} (v : PairV p) → p ⟹ p' → p' ⟹ p ⁺ → snd p' ⟹ sndK v (p ⁺)
tri-snd (isPair _ _) (ppair _ _) (ppair ra rb) = pβsnd ra rb
tri-snd notPair      _           r             = psnd r

tri-ps : {q q' : RTm Γ} {b' B : RTm ((Γ ∙) ∙)} (v : PairV q) → q ⟹ q' →
         b' ⟹ B → q' ⟹ q ⁺ → psplit b' q' ⟹ psK v B (q ⁺)
tri-ps (isPair _ _) (ppair _ _) rb (ppair rx ry) = ppsplit-β rb rx ry
tri-ps notPair      _           rb rq            = ppsplit rb rq

tri-nat : {n n' z' Z : RTm Γ} {s' S : RTm ((Γ ∙) ∙)} (v : NatV n) → n ⟹ n' →
          z' ⟹ Z → s' ⟹ S → n' ⟹ n ⁺ → natrec z' s' n' ⟹ natK v Z S (n ⁺)
tri-nat isZ     pnzero    rz rs _          = pnatrec-zero rz rs
tri-nat (isS _) (pnsuc _) rz rs (pnsuc rn) = pnatrec-suc rz rs rn
tri-nat notNat  _         rz rs rn         = pnatrec rz rs rn

tri-js : {p p' e' E : RTm Γ} {d' D : RTm (Γ ∙)} (v : IdreflV p) → p ⟹ p' →
         d' ⟹ D → e' ⟹ E → p' ⟹ p ⁺ → jsub d' p' e' ⟹ jsK v D (p ⁺) E
tri-js (isIdrefl _ _) (pidrefl _ _) rd re _  = pjsub-refl re
tri-js notIdrefl      _             rd re rp = pjsub rd rp re

tri-iel : {t t' D' D'' i' I e' E : RTm Γ} (v : ConV t) → t ⟹ t' →
          D' ⟹ D'' → i' ⟹ I → e' ⟹ E → t' ⟹ t ⁺ →
          ielim D' i' e' t' ⟹ ielK v D'' I E (t ⁺)
tri-iel (isCon _) (pcon _) rD ri re (pcon rp) = pι rD ri re rp
tri-iel notCon    _        rD ri re rt        = pielim rD ri re rt

tri-fc : {t t' a' A : RTm Γ} {b' B : RTm (Γ ∙)} (v : FinV t) → t ⟹ t' →
         a' ⟹ A → b' ⟹ B → t' ⟹ t ⁺ → fcase t' a' b' ⟹ fcK v (t ⁺) A B
tri-fc isFz     pfzero    ra rb _          = pfcase-z ra
tri-fc (isFs _) (pfsuc _) ra rb (pfsuc rt) = pfcase-s rt rb
tri-fc notFin   _         ra rb rt         = pfcase rt ra rb

tri-dp : {C C' I' I'' D' D'' : RTm Γ} (v : DescV C) → C ⟹ C' →
         I' ⟹ I'' → D' ⟹ D'' → C' ⟹ C ⁺ → dpay I' D' C' ⟹ dpK v I'' D'' (C ⁺)
tri-dp isι       pdι       rI rD _           = pdpay-ι
tri-dp (isσ _ _) (pdσ _ _) rI rD (pdσ rS rf) = pdpay-σ rI rD rS rf
tri-dp (isρ _ _) (pdρ _ _) rI rD (pdρ rj rC) = pdpay-ρ rI rD rj rC
tri-dp notDesc   _         rI rD rC          = pdpay rI rD rC

tri-dih : {C C' D' D'' e' E p' P : RTm Γ} (v : DescV C) → C ⟹ C' →
          D' ⟹ D'' → e' ⟹ E → p' ⟹ P → C' ⟹ C ⁺ →
          dih D' e' C' p' ⟹ dihK v D'' E (C ⁺) P
tri-dih isι       pdι       rD re rp _           = pdih-ι
tri-dih (isσ _ _) (pdσ _ _) rD re rp (pdσ rS rf) = pdih-σ rD re rf rp
tri-dih (isρ _ _) (pdρ _ _) rD re rp (pdρ rj rC) = pdih-ρ rD re rj rC rp
tri-dih notDesc   _         rD re rp rC          = pdih rD re rC rp

tri-ord : {a a' t t' u u' p' P q' Q : RTm Γ}
          (va : NatV a) (vu : NatV u) (vt : NatV t) → a ⟹ a' → t ⟹ t' → u ⟹ u' →
          a' ⟹ a ⁺ → t' ⟹ t ⁺ → u' ⟹ u ⁺ → p' ⟹ P → q' ⟹ Q →
          ordtr a' t' u' p' q' ⟹ ordK va vu vt (a ⁺) (t ⁺) (u ⁺) P Q
tri-ord isZ     _       _       pnzero    _         _         _          _          _          rp rq = pordtr-z
tri-ord (isS _) isZ     isZ     (pnsuc _) pnzero    pnzero    _          _          _          rp rq = pordtr-szz rp
tri-ord (isS _) isZ     (isS _) (pnsuc _) (pnsuc _) pnzero    _          _          _          rp rq = pordtr-ssz rq
tri-ord (isS _) (isS _) isZ     (pnsuc _) pnzero    (pnsuc _) (pnsuc ra) _          (pnsuc ru) rp rq = pordtr-szs ra ru rp
tri-ord (isS _) (isS _) (isS _) (pnsuc _) (pnsuc _) (pnsuc _) (pnsuc ra) (pnsuc rt) (pnsuc ru) rp rq = pordtr-sss ra rt ru rp rq
tri-ord (isS _) isZ     notNat  _         _         _         ra         rt         ru         rp rq = pordtr ra rt ru rp rq
tri-ord (isS _) (isS _) notNat  _         _         _         ra         rt         ru         rp rq = pordtr ra rt ru rp rq
tri-ord (isS _) notNat  _       _         _         _         ra         rt         ru         rp rq = pordtr ra rt ru rp rq
tri-ord notNat  _       _       _         _         _         ra         rt         ru         rp rq = pordtr ra rt ru rp rq

-- `tr` at a ⌜Hom⌝ code: J under `stkA?`; a pw-able path is refuted by
-- the same key (`stkA?⊥pw`).
tri-trJH : {c a m d' D : RTm (Γ ∙)} {c₁ a₁ b₁ s p' P e' E : RTm Γ} (k : 𝔹) → stkA? c₁ ≡ k →
           ⌜Hom⌝ c a m ⟹ d' → hrefl (⌜Hom⌝ c₁ a₁ b₁) s ⟹ p' →
           d' ⟹ D → p' ⟹ P → e' ⟹ E → tr d' p' e' ⟹ jK k D P E
tri-trJH false _ _ _ rd rp re = ptr rd rp re
tri-trJH true  ek (p⌜Hom⌝ _ _ _) (phrefl (p⌜Hom⌝ pc₁ _ _) _) _ _ re = ptr-J-Hom (stkA?-⟹ pc₁ ek) re
tri-trJH {c₁ = c₁} true ek (p⌜Hom⌝ _ _ _) (phrefl-pw w _ _) _ _ _ =
  bool-⊥ (trans (sym w) (stkA?⊥pw c₁ ek))

pwTri : {c₁ C' a₁ A' f₁ F' : RTm (Γ ∙)} {e₁ E : RTm Γ} (b : 𝔹) → (b ≡ true → pw? c₁ ≡ true) →
        c₁ ⟹ C' → a₁ ⟹ A' → f₁ ⟹ F' → e₁ ⟹ E →
        tr (⌜Hom⌝ c₁ a₁ (var vz)) (lam f₁) e₁ ⟹ pwK b C' A' F' E
pwTri true  kf rc ra rf re = ptr-pw (kf refl) rc ra rf re
pwTri false kf rc ra rf re = ptr (p⌜Hom⌝ rc ra (pvar vz)) (plam rf) re

tri-tr : {d d' : RTm (Γ ∙)} {p p' e' E : RTm Γ} (v : TrV d p) → d ⟹ d' → p ⟹ p' →
         d' ⟹ d ⁺ → p' ⟹ p ⁺ → e' ⟹ E → tr d' p' e' ⟹ trK v (d ⁺) (p ⁺) E
tri-tr (trJ _ _ _ jcUnit _)         (p⌜Hom⌝ _ _ _) (phrefl p⌜Unit⌝ _)         _ _ re = ptr-J-Unit re
tri-tr (trJ _ _ _ jcUnit _)         _ (phrefl-pw () _ _)                      _ _ _
tri-tr (trJ _ _ _ (jcIMu _ _ _) _)  (p⌜Hom⌝ _ _ _) (phrefl (p⌜IMu⌝ _ _ _) _)  _ _ re = ptr-J-IMu re
tri-tr (trJ _ _ _ (jcIMu _ _ _) _)  _ (phrefl-pw () _ _)                      _ _ _
tri-tr (trJ _ _ _ (jcFin _) _)      (p⌜Hom⌝ _ _ _) (phrefl (p⌜Fin⌝ _) _)      _ _ re = ptr-J-Fin re
tri-tr (trJ _ _ _ (jcFin _) _)      _ (phrefl-pw () _ _)                      _ _ _
tri-tr (trJ _ _ _ jcBase _)         (p⌜Hom⌝ _ _ _) (phrefl p⌜base⌝ _)         _ _ re = ptr-J-base re
tri-tr (trJ _ _ _ jcBase _)         _ (phrefl-pw () _ _)                      _ _ _
tri-tr (trJ _ _ _ (jcΣ _ _) _)      (p⌜Hom⌝ _ _ _) (phrefl (p⌜Σ⌝ _ _) _)      _ _ re = ptr-J-Σ re
tri-tr (trJ _ _ _ (jcΣ _ _) _)      _ (phrefl-pw () _ _)                      _ _ _
tri-tr (trJ _ _ _ (jcId _ _ _) _)   (p⌜Hom⌝ _ _ _) (phrefl (p⌜Id⌝ _ _ _) _)   _ _ re = ptr-J-Id re
tri-tr (trJ _ _ _ (jcId _ _ _) _)   _ (phrefl-pw () _ _)                      _ _ _
tri-tr (trJ _ _ _ (jcHom c₁ _ _) _) pd pp rd rp re = tri-trJH (stkA? c₁) refl pd pp rd rp re
tri-tr (trTaut _) (pvar _) (plam _) _ (plam rf) re = ptr-taut rf re
tri-tr (trPw c _ _) (p⌜Hom⌝ pc _ (pvar _)) (plam _) (p⌜Hom⌝ rc ra _) (plam rf) re =
  pwTri (pw? c) (pw?-⟹ pc) rc ra rf re
tri-tr trCong _ _ rd rp re = ptr rd rp re

-- `ap` at a canonical path: J under `stkC?`; a pw-able path is refuted by
-- the same key (`stk⊥pw`).
tri-apJ : {C s p' cB' CB X S : RTm Γ} {b' B : RTm (Γ ∙)} (k w : 𝔹) → stkC? C ≡ k → pw? C ≡ w →
          hrefl C s ⟹ p' → cB' ⟹ CB → b' ⟹ B → p' ⟹ hr⁺ w X S →
          ap cB' b' p' ⟹ apJK k CB B (hr⁺ w X S)
tri-apJ false _     _  _  _                  rcB rb rp            = pap rcB rb rp
tri-apJ {C = C} true true ek ew _            _   _  _             = bool-⊥ (trans (sym ew) (stk⊥pw C ek))
tri-apJ true  false ek ew (phrefl pC _)      rcB rb (phrefl _ rs) = pap-J (stkC?-⟹ pC ek) rcB rb rs
tri-apJ true  false ek ew (phrefl-pw w _ _)  _   _  _             = bool-⊥ (trans (sym w) ew)
tri-apJ true  false ek ew (phrefl pC _)      _   _  (phrefl-Nat-s _) with stkC?-⟹ pC ek
... | ()
tri-apJ true  false () ew phrefl-Nat-z       _   _  _
tri-apJ true  false () ew (phrefl-Nat-s _)   _   _  _

-- the key decided first: at a stable code the development is no order step
tri-apS : {C s p' cB' CB X S : RTm Γ} {b' B : RTm (Γ ∙)} (k : 𝔹) → stkC? C ≡ k →
          hrefl C s ⟹ p' → cB' ⟹ CB → b' ⟹ B → p' ⟹ hrK (hrV C s) (pw? C) X S →
          ap cB' b' p' ⟹ apJK k CB B (hrK (hrV C s) (pw? C) X S)
tri-apS false _  _  rcB rb rp = pap rcB rb rp
tri-apS {C = C} {s} {p'} {cB'} {CB} {X} {S} {b'} {B} true ek pp rcB rb rp =
  subst (λ z → ap cB' b' p' ⟹ apJK true CB B z) (sym eq)
        (tri-apJ true (pw? C) ek refl pp rcB rb (subst (λ z → p' ⟹ z) eq rp))
  where eq = hrK-stk {c = C} {t = s} {b = pw? C} {C = X} {T = S} ek

tri-ap : {p p' cB' CB : RTm Γ} {b' B : RTm (Γ ∙)} (v : ApV p) → p ⟹ p' →
         cB' ⟹ CB → b' ⟹ B → p' ⟹ p ⁺ → ap cB' b' p' ⟹ apK v CB B (p ⁺)
tri-ap (apJ C s) pp rcB rb rp = tri-apS (stkC? C) refl pp rcB rb rp
tri-ap apCong    _  rcB rb rp = pap rcB rb rp

-- `ap-J`'s own row: its key fixes both Booleans.
rootAp : {k w : 𝔹} {CB X S Y : RTm Γ} {B : RTm (Γ ∙)} → k ≡ true → w ≡ false →
         Y ⟹ hrefl CB (subTm (single S) B) → Y ⟹ apJK k CB B (hr⁺ w X S)
rootAp refl refl r = r

-- ── the triangle ───────────────────────────────────────────────────────

⟹-⁺ : {t u : RTm Γ} → t ⟹ u → u ⟹ t ⁺
⟹-⁺ (pvar x)               = pvar x
⟹-⁺ (plam p)               = plam (⟹-⁺ p)
⟹-⁺ (pref {d = d})         = tri-ref d (d <ˢ? Defs.size 𝒮)
⟹-⁺ (pdelta {d = d} p)     = tri-δ d p (d <ˢ? Defs.size 𝒮)
⟹-⁺ (ppair p q)            = ppair (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (papp {t = t} p q)     = tri-app (lamV t) p (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (pβ p q)               = ⟹-sub (single-⟹ (⟹-⁺ q)) (⟹-⁺ p)
⟹-⁺ (pabsurd pc pe)        = pabsurd (⟹-⁺ pc) (⟹-⁺ pe)
⟹-⁺ (pordtr {a = a} {t = t} {u = u} pa pt pu pp pq) =
  tri-ord (natV a) (natV u) (natV t) pa pt pu (⟹-⁺ pa) (⟹-⁺ pt) (⟹-⁺ pu) (⟹-⁺ pp) (⟹-⁺ pq)
⟹-⁺ pordtr-z = ⟹-refl _
⟹-⁺ (pordtr-szz pp) = ⟹-⁺ pp
⟹-⁺ (pordtr-ssz pq) = ⟹-⁺ pq
⟹-⁺ (pordtr-szs pa pu pp) = pabsurd (p⌜Hom⌝ p⌜Nat⌝ (⟹-⁺ pa) (⟹-⁺ pu)) (⟹-⁺ pp)
⟹-⁺ (pordtr-sss pa pt pu pp pq) =
  pordtr (⟹-⁺ pa) (⟹-⁺ pt) (⟹-⁺ pu) (⟹-⁺ pp) (⟹-⁺ pq)
⟹-⁺ (pfst {p = p} q)       = tri-fst (pairV p) q (⟹-⁺ q)
⟹-⁺ (psnd {p = p} q)       = tri-snd (pairV p) q (⟹-⁺ q)
⟹-⁺ (pβfst p q)            = ⟹-⁺ p
⟹-⁺ (pβsnd p q)            = ⟹-⁺ q
⟹-⁺ p⌜base⌝                = p⌜base⌝
⟹-⁺ (p⌜Π⌝ p q)             = p⌜Π⌝ (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (p⌜Σ⌝ p q)             = p⌜Σ⌝ (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (p⌜Hom⌝ p q r)         = p⌜Hom⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
⟹-⁺ (phrefl {c = c} {t = f} p q) = tri-hr (hrV c f) p q (pw?-⟹ p) (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ phrefl-Nat-z           = punit
⟹-⁺ (phrefl-Nat-s p)       = phrefl p⌜Nat⌝ (⟹-⁺ p)
⟹-⁺ (phrefl-pw {C = C} {C'} {s = t} {t'} key pC pt) =
  subst (λ z → lam (hrefl (pwBody C') (app (renTm vs t') (var vz))) ⟹ z)
        (sym (hrK-pw {c = C} {t = t} {b = pw? C} {C = C ⁺} {T = t ⁺} key))
  (subst (λ b → lam (hrefl (pwBody C') (app (renTm vs t') (var vz)))
               ⟹ hr⁺ b (C ⁺) (t ⁺))
        (sym key)
        (plam (phrefl (pwBody-⟹ (⟹-⁺ pC) (pw?-⟹ pC key))
                      (papp (⟹-ren vs (⟹-⁺ pt)) (pvar vz)))))
⟹-⁺ (ptr {d = d} {p = p} pd pp pe) = tri-tr (trV d p) pd pp (⟹-⁺ pd) (⟹-⁺ pp) (⟹-⁺ pe)
⟹-⁺ (ptr-J-base p)         = ⟹-⁺ p
⟹-⁺ (ptr-J-Unit p)         = ⟹-⁺ p
⟹-⁺ (ptr-J-IMu p)          = ⟹-⁺ p
⟹-⁺ (ptr-J-Fin p)          = ⟹-⁺ p
⟹-⁺ (ptr-J-Σ p)            = ⟹-⁺ p
⟹-⁺ (ptr-J-Id p)           = ⟹-⁺ p
⟹-⁺ (ptr-J-Hom {c = c} {a} {m} {c₁} {a₁} {b₁} {s} {e} key pe) =
  subst (λ b → _ ⟹ jK b (⌜Hom⌝ c a m ⁺) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s ⁺) (e ⁺)) (sym key) (⟹-⁺ pe)
⟹-⁺ (ptr-taut p q)         = papp (plam (⟹-⁺ p)) (⟹-⁺ q)
⟹-⁺ (ptr-pw {c = c} {a = a} {f = f} {e = e} key pc pa pf pe) =
  subst (λ b → _ ⟹ pwK b (c ⁺) (a ⁺) (f ⁺) (e ⁺)) (sym key)
        (plam (ptr (p⌜Hom⌝ (⟹-ren pwShift
                             (pwBody-⟹ (⟹-⁺ pc) (pw?-⟹ pc key)))
                           (papp (⟹-ren vs (⟹-⁺ pa)) (pvar (vs vz)))
                           (pvar vz))
                   (⟹-⁺ pf)
                   (papp (⟹-ren vs (⟹-⁺ pe)) (pvar vz))))
⟹-⁺ p⌜Nat⌝                 = p⌜Nat⌝
⟹-⁺ p⌜Unit⌝                = p⌜Unit⌝
⟹-⁺ (pap {p = p} pcB pb pp) = tri-ap (apV p) pp (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ pp)
⟹-⁺ (pap-J {cB' = cB'} {b' = b'} {c₁ = C} {s} {s'} key pcB pb ps) =
  subst (λ z → hrefl cB' (subTm (single s') b') ⟹ apJK (stkC? C) _ _ z)
        (sym (hrK-stk {c = C} {t = s} {b = pw? C} {C = C ⁺} {T = s ⁺} key))
        (rootAp key (stk⊥pw C key) (phrefl (⟹-⁺ pcB) (⟹-sub (single-⟹ (⟹-⁺ ps)) (⟹-⁺ pb))))
⟹-⁺ (p⌜Id⌝ p q r)          = p⌜Id⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
⟹-⁺ (pidrefl p q)          = pidrefl (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (pjsub {p = p} pd pp pe) = tri-js (idreflV p) pp (⟹-⁺ pd) (⟹-⁺ pe) (⟹-⁺ pp)
⟹-⁺ (pjsub-refl p)         = ⟹-⁺ p
⟹-⁺ punit                  = punit
⟹-⁺ pnzero                 = pnzero
⟹-⁺ (pnsuc p)              = pnsuc (⟹-⁺ p)
⟹-⁺ (pnatrec {n = n} pz ps pn) = tri-nat (natV n) pn (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)
⟹-⁺ (pnatrec-zero pz ps)   = ⟹-⁺ pz
⟹-⁺ (pnatrec-suc pz ps pn) =
  ⟹-sub (single-⟹ (pnatrec (⟹-⁺ pz) (⟹-⁺ ps) (⟹-⁺ pn)))
        (⟹-sub (⟹-exts (single-⟹ (⟹-⁺ pn))) (⟹-⁺ ps))
⟹-⁺ (p⌜IMu⌝ a b c)         = p⌜IMu⌝ (⟹-⁺ a) (⟹-⁺ b) (⟹-⁺ c)
⟹-⁺ (p⌜Fin⌝ p)             = p⌜Fin⌝ (⟹-⁺ p)
⟹-⁺ (pcon pp)              = pcon (⟹-⁺ pp)
⟹-⁺ (pielim {t = t} pD pi pe pt) = tri-iel (conV t) pt (⟹-⁺ pD) (⟹-⁺ pi) (⟹-⁺ pe) (⟹-⁺ pt)
⟹-⁺ (pι pD pi pe pp) =
  papp (papp (papp (⟹-⁺ pe) (⟹-⁺ pi)) (⟹-⁺ pp))
       (pdih (⟹-⁺ pD) (⟹-⁺ pe) (papp (⟹-⁺ pD) (⟹-⁺ pi)) (⟹-⁺ pp))
⟹-⁺ pdι                    = pdι
⟹-⁺ (pdσ a b)              = pdσ (⟹-⁺ a) (⟹-⁺ b)
⟹-⁺ (pdρ a b)              = pdρ (⟹-⁺ a) (⟹-⁺ b)
⟹-⁺ (pdpay {C = C} pI pD pC) = tri-dp (descV C) pC (⟹-⁺ pI) (⟹-⁺ pD) (⟹-⁺ pC)
⟹-⁺ pdpay-ι = p⌜Unit⌝
⟹-⁺ (pdpay-σ pI pD pS pf) =
  p⌜Σ⌝ (⟹-⁺ pS) (pdpay (⟹-ren vs (⟹-⁺ pI)) (⟹-ren vs (⟹-⁺ pD))
                        (papp (⟹-ren vs (⟹-⁺ pf)) (pvar vz)))
⟹-⁺ (pdpay-ρ pI pD pj pC) =
  p⌜Σ⌝ (p⌜IMu⌝ (⟹-⁺ pI) (⟹-⁺ pD) (⟹-⁺ pj))
       (pdpay (⟹-ren vs (⟹-⁺ pI)) (⟹-ren vs (⟹-⁺ pD)) (⟹-ren vs (⟹-⁺ pC)))
⟹-⁺ (pdih {C = C} pD pe pC pp) = tri-dih (descV C) pC (⟹-⁺ pD) (⟹-⁺ pe) (⟹-⁺ pp) (⟹-⁺ pC)
⟹-⁺ pdih-ι = punit
⟹-⁺ (pdih-σ pD pe pf pp) = pdih (⟹-⁺ pD) (⟹-⁺ pe) (papp (⟹-⁺ pf) (pfst (⟹-⁺ pp))) (psnd (⟹-⁺ pp))
⟹-⁺ (pdih-ρ pD pe pj pC pp) =
  ppair (pielim (⟹-⁺ pD) (⟹-⁺ pj) (⟹-⁺ pe) (pfst (⟹-⁺ pp)))
        (pdih (⟹-⁺ pD) (⟹-⁺ pe) (⟹-⁺ pC) (psnd (⟹-⁺ pp)))
⟹-⁺ pfzero                 = pfzero
⟹-⁺ (pfsuc a)              = pfsuc (⟹-⁺ a)
⟹-⁺ (pfcase {t = t} pt pa pb) = tri-fc (finV t) pt (⟹-⁺ pa) (⟹-⁺ pb) (⟹-⁺ pt)
⟹-⁺ (pfcase-z pa)          = ⟹-⁺ pa
⟹-⁺ (pfcase-s pt pb)       = ⟹-sub (single-⟹ (⟹-⁺ pt)) (⟹-⁺ pb)
⟹-⁺ (pfcase0 a)            = pfcase0 (⟹-⁺ a)
⟹-⁺ (ppsplit {q = q} pb pq) = tri-ps (pairV q) pq (⟹-⁺ pb) (⟹-⁺ pq)
⟹-⁺ (ppsplit-β pb px py)   = ⟹-sub (single2-⟹ (⟹-⁺ px) (⟹-⁺ py)) (⟹-⁺ pb)

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
