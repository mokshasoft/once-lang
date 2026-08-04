------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 25 — (B1) CONFLUENCE (Church–Rosser) of the dependent
--                            de Bruijn calculus
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
module poc.OCP0009.NbEPDirDBConf where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app; pair; fst; snd
        ; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub
        ; unit; nzero; nsuc; natrec; natrec-cong₃; subTm-subTm
        ; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃
        ; Ren; extR; renTm; renTm-renTm; renTm-cong
        ; Sub; extS; subTm; renTm-subTm; subTm-renTm; subTm-cong
        ; _ᵣ∘ₛ_; _ₛ∘ᵣ_; _∘ᵣ_ )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; pw?; stkC?; pwBody; pwShift
        ; pw?-ren; stkC?-ren; pwBody-ren
        ; pw?-sub; stkC?-sub; pwBody-sub; pw⊥stk )
open import poc.OCP0009.NbEPDirDBType
  using ( single; swp; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; tr-J-base; tr-J-Σ; tr-J-Id; tr-taut; hrefl-pw; tr-J-Hom; tr-pw
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ
        ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ
        ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ
        ; _⟶*_; done; step
        ; _≅_; cred; crfl; csym; ctrn )
open import poc.OCP0009.NbEPDirDBSR
  using ( sub-comm; sub-comm-ext; ⟶-sub; wk-sub; wk₁-sub; swp-sub; pwShift-sub )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- Multi-step reduction: transitivity + congruences.
------------------------------------------------------------------------

⟶*-trans : {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
⟶*-trans done       q = q
⟶*-trans (step r p) q = step r (⟶*-trans p q)

⟶*-lam : {t t' : RTm (Γ ∙)} → t ⟶* t' → lam t ⟶* lam t'
⟶*-lam done       = done
⟶*-lam (step r p) = step (ξ-lam r) (⟶*-lam p)

⟶*-appˡ : {t t' u : RTm Γ} → t ⟶* t' → app t u ⟶* app t' u
⟶*-appˡ done       = done
⟶*-appˡ (step r p) = step (ξ-appˡ r) (⟶*-appˡ p)

⟶*-appʳ : {t u u' : RTm Γ} → u ⟶* u' → app t u ⟶* app t u'
⟶*-appʳ done       = done
⟶*-appʳ (step r p) = step (ξ-appʳ r) (⟶*-appʳ p)

⟶*-pairˡ : {a a' b : RTm Γ} → a ⟶* a' → pair a b ⟶* pair a' b
⟶*-pairˡ done       = done
⟶*-pairˡ (step r p) = step (ξ-pairˡ r) (⟶*-pairˡ p)

⟶*-pairʳ : {a b b' : RTm Γ} → b ⟶* b' → pair a b ⟶* pair a b'
⟶*-pairʳ done       = done
⟶*-pairʳ (step r p) = step (ξ-pairʳ r) (⟶*-pairʳ p)

⟶*-fst : {p p' : RTm Γ} → p ⟶* p' → fst p ⟶* fst p'
⟶*-fst done       = done
⟶*-fst (step r q) = step (ξ-fst r) (⟶*-fst q)

⟶*-snd : {p p' : RTm Γ} → p ⟶* p' → snd p ⟶* snd p'
⟶*-snd done       = done
⟶*-snd (step r q) = step (ξ-snd r) (⟶*-snd q)

⟶*-⌜Π⌝ˡ : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶* c' → ⌜Π⌝ c d ⟶* ⌜Π⌝ c' d
⟶*-⌜Π⌝ˡ done       = done
⟶*-⌜Π⌝ˡ (step r p) = step (ξ-⌜Π⌝ˡ r) (⟶*-⌜Π⌝ˡ p)

⟶*-⌜Π⌝ʳ : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶* d' → ⌜Π⌝ c d ⟶* ⌜Π⌝ c d'
⟶*-⌜Π⌝ʳ done       = done
⟶*-⌜Π⌝ʳ (step r p) = step (ξ-⌜Π⌝ʳ r) (⟶*-⌜Π⌝ʳ p)

⟶*-⌜Σ⌝ˡ : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶* c' → ⌜Σ⌝ c d ⟶* ⌜Σ⌝ c' d
⟶*-⌜Σ⌝ˡ done       = done
⟶*-⌜Σ⌝ˡ (step r p) = step (ξ-⌜Σ⌝ˡ r) (⟶*-⌜Σ⌝ˡ p)

⟶*-⌜Σ⌝ʳ : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶* d' → ⌜Σ⌝ c d ⟶* ⌜Σ⌝ c d'
⟶*-⌜Σ⌝ʳ done       = done
⟶*-⌜Σ⌝ʳ (step r p) = step (ξ-⌜Σ⌝ʳ r) (⟶*-⌜Σ⌝ʳ p)

⟶*-⌜Hom⌝ᶜ : {c c' a b : RTm Γ} → c ⟶* c' → ⌜Hom⌝ c a b ⟶* ⌜Hom⌝ c' a b
⟶*-⌜Hom⌝ᶜ done       = done
⟶*-⌜Hom⌝ᶜ (step r p) = step (ξ-⌜Hom⌝ᶜ r) (⟶*-⌜Hom⌝ᶜ p)

⟶*-⌜Hom⌝ˡ : {c a a' b : RTm Γ} → a ⟶* a' → ⌜Hom⌝ c a b ⟶* ⌜Hom⌝ c a' b
⟶*-⌜Hom⌝ˡ done       = done
⟶*-⌜Hom⌝ˡ (step r p) = step (ξ-⌜Hom⌝ˡ r) (⟶*-⌜Hom⌝ˡ p)

⟶*-⌜Hom⌝ʳ : {c a b b' : RTm Γ} → b ⟶* b' → ⌜Hom⌝ c a b ⟶* ⌜Hom⌝ c a b'
⟶*-⌜Hom⌝ʳ done       = done
⟶*-⌜Hom⌝ʳ (step r p) = step (ξ-⌜Hom⌝ʳ r) (⟶*-⌜Hom⌝ʳ p)

⟶*-hreflᶜ : {c c' t : RTm Γ} → c ⟶* c' → hrefl c t ⟶* hrefl c' t
⟶*-hreflᶜ done       = done
⟶*-hreflᶜ (step r p) = step (ξ-hreflᶜ r) (⟶*-hreflᶜ p)

⟶*-hreflᵃ : {c t t' : RTm Γ} → t ⟶* t' → hrefl c t ⟶* hrefl c t'
⟶*-hreflᵃ done       = done
⟶*-hreflᵃ (step r p) = step (ξ-hreflᵃ r) (⟶*-hreflᵃ p)

⟶*-trᵈ : {d d' : RTm (Γ ∙)} {p e : RTm Γ} → d ⟶* d' → tr d p e ⟶* tr d' p e
⟶*-trᵈ done       = done
⟶*-trᵈ (step r q) = step (ξ-trᵈ r) (⟶*-trᵈ q)

⟶*-trᵖ : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → p ⟶* p' → tr d p e ⟶* tr d p' e
⟶*-trᵖ done       = done
⟶*-trᵖ (step r q) = step (ξ-trᵖ r) (⟶*-trᵖ q)

⟶*-trᵉ : {d : RTm (Γ ∙)} {p e e' : RTm Γ} → e ⟶* e' → tr d p e ⟶* tr d p e'
⟶*-trᵉ done       = done
⟶*-trᵉ (step r q) = step (ξ-trᵉ r) (⟶*-trᵉ q)

⟶*-apᶜ : {c c' : RTm Γ} {b : RTm (Γ ∙)} {p : RTm Γ} → c ⟶* c' → ap c b p ⟶* ap c' b p
⟶*-apᶜ done       = done
⟶*-apᶜ (step r q) = step (ξ-apᶜ r) (⟶*-apᶜ q)

⟶*-apᵇ : {c : RTm Γ} {b b' : RTm (Γ ∙)} {p : RTm Γ} → b ⟶* b' → ap c b p ⟶* ap c b' p
⟶*-apᵇ done       = done
⟶*-apᵇ (step r q) = step (ξ-apᵇ r) (⟶*-apᵇ q)

⟶*-apᵖ : {c : RTm Γ} {b : RTm (Γ ∙)} {p p' : RTm Γ} → p ⟶* p' → ap c b p ⟶* ap c b p'
⟶*-apᵖ done       = done
⟶*-apᵖ (step r q) = step (ξ-apᵖ r) (⟶*-apᵖ q)

⟶*-⌜Id⌝ᶜ : {c c' a b : RTm Γ} → c ⟶* c' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c' a b
⟶*-⌜Id⌝ᶜ done       = done
⟶*-⌜Id⌝ᶜ (step r q) = step (ξ-⌜Id⌝ᶜ r) (⟶*-⌜Id⌝ᶜ q)

⟶*-⌜Id⌝ˡ : {c a a' b : RTm Γ} → a ⟶* a' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c a' b
⟶*-⌜Id⌝ˡ done       = done
⟶*-⌜Id⌝ˡ (step r q) = step (ξ-⌜Id⌝ˡ r) (⟶*-⌜Id⌝ˡ q)

⟶*-⌜Id⌝ʳ : {c a b b' : RTm Γ} → b ⟶* b' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c a b'
⟶*-⌜Id⌝ʳ done       = done
⟶*-⌜Id⌝ʳ (step r q) = step (ξ-⌜Id⌝ʳ r) (⟶*-⌜Id⌝ʳ q)

⟶*-idreflᶜ : {c c' t : RTm Γ} → c ⟶* c' → idrefl c t ⟶* idrefl c' t
⟶*-idreflᶜ done       = done
⟶*-idreflᶜ (step r q) = step (ξ-idreflᶜ r) (⟶*-idreflᶜ q)

⟶*-idreflᵃ : {c t t' : RTm Γ} → t ⟶* t' → idrefl c t ⟶* idrefl c t'
⟶*-idreflᵃ done       = done
⟶*-idreflᵃ (step r q) = step (ξ-idreflᵃ r) (⟶*-idreflᵃ q)

⟶*-jsubᵈ : {d d' : RTm (Γ ∙)} {p e : RTm Γ} → d ⟶* d' → jsub d p e ⟶* jsub d' p e
⟶*-jsubᵈ done       = done
⟶*-jsubᵈ (step r q) = step (ξ-jsubᵈ r) (⟶*-jsubᵈ q)

⟶*-jsubᵖ : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → p ⟶* p' → jsub d p e ⟶* jsub d p' e
⟶*-jsubᵖ done       = done
⟶*-jsubᵖ (step r q) = step (ξ-jsubᵖ r) (⟶*-jsubᵖ q)

⟶*-jsubᵉ : {d : RTm (Γ ∙)} {p e e' : RTm Γ} → e ⟶* e' → jsub d p e ⟶* jsub d p e'
⟶*-jsubᵉ done       = done
⟶*-jsubᵉ (step r q) = step (ξ-jsubᵉ r) (⟶*-jsubᵉ q)

⟶*-nsuc : {n n' : RTm Γ} → n ⟶* n' → nsuc n ⟶* nsuc n'
⟶*-nsuc done       = done
⟶*-nsuc (step r q) = step (ξ-nsuc r) (⟶*-nsuc q)

⟶*-natrecᶻ : {z z' : RTm Γ} {s : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
             z ⟶* z' → natrec z s n ⟶* natrec z' s n
⟶*-natrecᶻ done       = done
⟶*-natrecᶻ (step r q) = step (ξ-natrecᶻ r) (⟶*-natrecᶻ q)

⟶*-natrecˢ : {z : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
             s ⟶* s' → natrec z s n ⟶* natrec z s' n
⟶*-natrecˢ done       = done
⟶*-natrecˢ (step r q) = step (ξ-natrecˢ r) (⟶*-natrecˢ q)

⟶*-natrecⁿ : {z : RTm Γ} {s : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
             n ⟶* n' → natrec z s n ⟶* natrec z s n'
⟶*-natrecⁿ done       = done
⟶*-natrecⁿ (step r q) = step (ξ-natrecⁿ r) (⟶*-natrecⁿ q)

⟶*-sub : (σ : Sub Γ Δ) {t u : RTm Γ} → t ⟶* u → subTm σ t ⟶* subTm σ u
⟶*-sub σ done       = done
⟶*-sub σ (step r p) = step (⟶-sub σ r) (⟶*-sub σ p)

------------------------------------------------------------------------
-- Renaming commutes with single substitution, and reduction survives renaming.
------------------------------------------------------------------------

ren-comm : (ρ : Ren Γ Δ) (t : RTm (Γ ∙)) (u : RTm Γ) →
           renTm ρ (subTm (single u) t) ≡
           subTm (single (renTm ρ u)) (renTm (extR ρ) t)
ren-comm {Γ} ρ t u =
  trans (renTm-subTm t) (trans (subTm-cong bridge t) (sym (subTm-renTm t)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           (ρ ᵣ∘ₛ single u) x ≡ (single (renTm ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

-- The pure-renaming commutation bridges (all pointwise-definitional):
-- weakening, weakening-under-a-binder, and the top-two-variable swap
-- each commute with an arbitrary lifted renaming.
wk-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
         renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
wk-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong (λ _ → refl) t) (sym (renTm-renTm t)))

-- ★ WF stage A: `ren-comm` one binder down (the renaming analog of
-- `sub-comm-ext`) — for the recursor's step substitution.
ren-comm-ext : (ρ : Ren Γ Δ) (s : RTm ((Γ ∙) ∙)) (n : RTm Γ) →
               renTm (extR ρ) (subTm (extS (single n)) s) ≡
               subTm (extS (single (renTm ρ n))) (renTm (extR (extR ρ)) s)
ren-comm-ext {Γ} ρ s n =
  trans (renTm-subTm s) (trans (subTm-cong bridge s) (sym (subTm-renTm s)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           renTm (extR ρ) (extS (single n) x) ≡
           extS (single (renTm ρ n)) (extR (extR ρ) x)
  bridge vz          = refl
  bridge (vs vz)     = wk-ren ρ n
  bridge (vs (vs x)) = refl

wk₁-ren : (ρ : Ren Γ Δ) (t : RTm (Γ ∙)) →
          renTm (extR (extR ρ)) (renTm (extR vs) t) ≡
          renTm (extR vs) (renTm (extR ρ) t)
wk₁-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong ptw t) (sym (renTm-renTm t)))
  where
  ptw : ∀ x → (extR (extR ρ) ∘ᵣ extR vs) x ≡ (extR vs ∘ᵣ extR ρ) x
  ptw vz     = refl
  ptw (vs z) = refl

swp-ren : (ρ : Ren Γ Δ) (t : RTm ((Γ ∙) ∙)) →
          renTm (extR (extR ρ)) (renTm swp t) ≡
          renTm swp (renTm (extR (extR ρ)) t)
swp-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong ptw t) (sym (renTm-renTm t)))
  where
  ptw : ∀ x → (extR (extR ρ) ∘ᵣ swp) x ≡ (swp ∘ᵣ extR (extR ρ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs z)) = refl

-- ...and the same against `pwShift` (W2b).
pwShift-ren : (ρ : Ren Γ Δ) (t : RTm ((Γ ∙) ∙)) →
              renTm (extR (extR ρ)) (renTm pwShift t) ≡
              renTm pwShift (renTm (extR (extR ρ)) t)
pwShift-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong ptw t) (sym (renTm-renTm t)))
  where
  ptw : ∀ x → (extR (extR ρ) ∘ᵣ pwShift) x ≡ (pwShift ∘ᵣ extR (extR ρ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs z)) = refl

⟶-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ⟶ u → renTm ρ t ⟶ renTm ρ u
⟶-ren ρ (β t u)    =
  subst (λ z → renTm ρ (app (lam t) u) ⟶ z)
        (sym (ren-comm ρ t u))
        (β (renTm (extR ρ) t) (renTm ρ u))
⟶-ren ρ (βfst a b)  = βfst (renTm ρ a) (renTm ρ b)
⟶-ren ρ (βsnd a b)  = βsnd (renTm ρ a) (renTm ρ b)
⟶-ren ρ (ξ-lam r)   = ξ-lam (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-appˡ r)  = ξ-appˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-appʳ r)  = ξ-appʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-pairˡ r) = ξ-pairˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-pairʳ r) = ξ-pairʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-fst r)   = ξ-fst (⟶-ren ρ r)
⟶-ren ρ (ξ-snd r)   = ξ-snd (⟶-ren ρ r)
⟶-ren ρ (natrec-zero z s) =
  natrec-zero (renTm ρ z) (renTm (extR (extR ρ)) s)
⟶-ren ρ (natrec-suc z s n) =
  subst (λ w → natrec (renTm ρ z) (renTm (extR (extR ρ)) s)
                      (nsuc (renTm ρ n)) ⟶ w)
        (sym (trans (ren-comm ρ (subTm (extS (single n)) s) (natrec z s n))
                    (cong (subTm (single (natrec (renTm ρ z)
                                                 (renTm (extR (extR ρ)) s)
                                                 (renTm ρ n))))
                          (ren-comm-ext ρ s n))))
        (natrec-suc (renTm ρ z) (renTm (extR (extR ρ)) s) (renTm ρ n))
⟶-ren ρ (ξ-nsuc r)    = ξ-nsuc (⟶-ren ρ r)
⟶-ren ρ (ξ-natrecᶻ r) = ξ-natrecᶻ (⟶-ren ρ r)
⟶-ren ρ (ξ-natrecˢ r) = ξ-natrecˢ (⟶-ren (extR (extR ρ)) r)
⟶-ren ρ (ξ-natrecⁿ r) = ξ-natrecⁿ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Π⌝ˡ r) = ξ-⌜Π⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Π⌝ʳ r) = ξ-⌜Π⌝ʳ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-⌜Σ⌝ˡ r) = ξ-⌜Σ⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Σ⌝ʳ r) = ξ-⌜Σ⌝ʳ (⟶-ren (extR ρ) r)
⟶-ren ρ (tr-J-base c a m s e) =
  tr-J-base (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
            (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-J-Σ c a m c₁ c₂ s e) =
  tr-J-Σ (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
         (renTm ρ c₁) (renTm (extR ρ) c₂)
         (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-taut f e) = tr-taut (renTm (extR ρ) f) (renTm ρ e)
⟶-ren ρ (hrefl-pw C t key) =
  subst (λ z → hrefl (renTm ρ C) (renTm ρ t) ⟶ z)
        (cong₂ (λ x y → lam (hrefl x (app y (var vz))))
               (pwBody-ren ρ C key) (sym (wk-ren ρ t)))
        (hrefl-pw (renTm ρ C) (renTm ρ t)
                  (trans (pw?-ren ρ C) key))
⟶-ren ρ (tr-J-Hom c a m c₁ a₁ b₁ t e key) =
  tr-J-Hom (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
           (renTm ρ c₁) (renTm ρ a₁) (renTm ρ b₁)
           (renTm ρ t) (renTm ρ e) (trans (stkC?-ren ρ c₁) key)
⟶-ren ρ (tr-pw c a f e key) =
  subst (λ z → tr (⌜Hom⌝ (renTm (extR ρ) c) (renTm (extR ρ) a) (var vz))
                  (lam (renTm (extR ρ) f)) (renTm ρ e) ⟶ z)
        (cong lam
          (tr-cong₃
            (⌜Hom⌝-cong₃
              (trans (cong (renTm pwShift) (pwBody-ren (extR ρ) c key))
                     (sym (pwShift-ren ρ (pwBody c))))
              (cong (λ z → app z (var (vs vz))) (sym (wk-ren (extR ρ) a)))
              refl)
            refl
            (cong (λ z → app z (var vz)) (sym (wk-ren ρ e)))))
        (tr-pw (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) f)
               (renTm ρ e) (trans (pw?-ren (extR ρ) c) key))
⟶-ren ρ (ξ-⌜Hom⌝ᶜ r) = ξ-⌜Hom⌝ᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Hom⌝ˡ r) = ξ-⌜Hom⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Hom⌝ʳ r) = ξ-⌜Hom⌝ʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-hreflᶜ r) = ξ-hreflᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-hreflᵃ r) = ξ-hreflᵃ (⟶-ren ρ r)
⟶-ren ρ (ξ-trᵈ r)    = ξ-trᵈ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-trᵖ r)    = ξ-trᵖ (⟶-ren ρ r)
⟶-ren ρ (ξ-trᵉ r)    = ξ-trᵉ (⟶-ren ρ r)
⟶-ren ρ (ap-J cB b c₁ s key) =
  subst (λ z → ap (renTm ρ cB) (renTm (extR ρ) b)
                  (hrefl (renTm ρ c₁) (renTm ρ s))
               ⟶ hrefl (renTm ρ cB) z)
        (sym (ren-comm ρ b s))
        (ap-J (renTm ρ cB) (renTm (extR ρ) b) (renTm ρ c₁) (renTm ρ s)
              (trans (stkC?-ren ρ c₁) key))
⟶-ren ρ (ξ-apᶜ r) = ξ-apᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-apᵇ r) = ξ-apᵇ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-apᵖ r) = ξ-apᵖ (⟶-ren ρ r)
⟶-ren ρ (tr-J-Id c a m c₁ a₁ b₁ s e) =
  tr-J-Id (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
          (renTm ρ c₁) (renTm ρ a₁) (renTm ρ b₁) (renTm ρ s) (renTm ρ e)
⟶-ren ρ (jsub-refl d c s e) =
  jsub-refl (renTm (extR ρ) d) (renTm ρ c) (renTm ρ s) (renTm ρ e)
⟶-ren ρ (ξ-⌜Id⌝ᶜ r) = ξ-⌜Id⌝ᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Id⌝ˡ r) = ξ-⌜Id⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Id⌝ʳ r) = ξ-⌜Id⌝ʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-idreflᶜ r) = ξ-idreflᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-idreflᵃ r) = ξ-idreflᵃ (⟶-ren ρ r)
⟶-ren ρ (ξ-jsubᵈ r) = ξ-jsubᵈ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-jsubᵖ r) = ξ-jsubᵖ (⟶-ren ρ r)
⟶-ren ρ (ξ-jsubᵉ r) = ξ-jsubᵉ (⟶-ren ρ r)

⟶*-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ⟶* u → renTm ρ t ⟶* renTm ρ u
⟶*-ren ρ done       = done
⟶*-ren ρ (step r p) = step (⟶-ren ρ r) (⟶*-ren ρ p)

-- W2b: the classifier keys are closed under reduction, and the body
-- function maps a code's step to steps of the body — the content of
-- the hrefl-pw/ξ-hreflᶜ and tr-pw/ξ-trᵈ critical-pair joins.
pw?-red : {C C' : RTm Γ} → C ⟶ C' → pw? C ≡ true → pw? C' ≡ true
pw?-red (β _ _) ()
pw?-red (βfst _ _) ()
pw?-red (βsnd _ _) ()
pw?-red (ξ-lam _) ()
pw?-red (ξ-appˡ _) ()
pw?-red (ξ-appʳ _) ()
pw?-red (ξ-pairˡ _) ()
pw?-red (ξ-pairʳ _) ()
pw?-red (ξ-fst _) ()
pw?-red (ξ-snd _) ()
pw?-red (ξ-⌜Π⌝ˡ r) h = refl
pw?-red (ξ-⌜Π⌝ʳ r) h = refl
pw?-red (ξ-⌜Σ⌝ˡ _) ()
pw?-red (ξ-⌜Σ⌝ʳ _) ()
pw?-red (ξ-⌜Hom⌝ᶜ r) h = pw?-red r h
pw?-red (ξ-⌜Hom⌝ˡ r) h = h
pw?-red (ξ-⌜Hom⌝ʳ r) h = h
pw?-red (ξ-hreflᶜ _) ()
pw?-red (ξ-hreflᵃ _) ()
pw?-red (hrefl-pw _ _ _) ()
pw?-red (tr-J-base _ _ _ _ _) ()
pw?-red (tr-J-Σ _ _ _ _ _ _ _) ()
pw?-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
pw?-red (tr-taut _ _) ()
pw?-red (tr-pw _ _ _ _ _) ()
pw?-red (ξ-trᵈ _) ()
pw?-red (ξ-trᵖ _) ()
pw?-red (ξ-trᵉ _) ()

stkC?-red : {C C' : RTm Γ} → C ⟶ C' → stkC? C ≡ true → stkC? C' ≡ true
stkC?-red (β _ _) ()
stkC?-red (βfst _ _) ()
stkC?-red (βsnd _ _) ()
stkC?-red (ξ-lam _) ()
stkC?-red (ξ-appˡ _) ()
stkC?-red (ξ-appʳ _) ()
stkC?-red (ξ-pairˡ _) ()
stkC?-red (ξ-pairʳ _) ()
stkC?-red (ξ-fst _) ()
stkC?-red (ξ-snd _) ()
stkC?-red (ξ-⌜Π⌝ˡ _) ()
stkC?-red (ξ-⌜Π⌝ʳ _) ()
stkC?-red (ξ-⌜Σ⌝ˡ r) h = refl
stkC?-red (ξ-⌜Σ⌝ʳ r) h = refl
stkC?-red (ξ-⌜Hom⌝ᶜ r) h = stkC?-red r h
stkC?-red (ξ-⌜Id⌝ᶜ r) h = refl
stkC?-red (ξ-⌜Id⌝ˡ r) h = refl
stkC?-red (ξ-⌜Id⌝ʳ r) h = refl
stkC?-red (ξ-⌜Hom⌝ˡ r) h = h
stkC?-red (ξ-⌜Hom⌝ʳ r) h = h
stkC?-red (ξ-hreflᶜ _) ()
stkC?-red (ξ-hreflᵃ _) ()
stkC?-red (hrefl-pw _ _ _) ()
stkC?-red (tr-J-base _ _ _ _ _) ()
stkC?-red (tr-J-Σ _ _ _ _ _ _ _) ()
stkC?-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
stkC?-red (tr-taut _ _) ()
stkC?-red (tr-pw _ _ _ _ _) ()
stkC?-red (ξ-trᵈ _) ()
stkC?-red (ξ-trᵖ _) ()
stkC?-red (ξ-trᵉ _) ()

pwBody-red : {C C' : RTm Γ} → C ⟶ C' → pw? C ≡ true →
             pwBody C ⟶* pwBody C'
pwBody-red (β _ _) ()
pwBody-red (βfst _ _) ()
pwBody-red (βsnd _ _) ()
pwBody-red (ξ-lam _) ()
pwBody-red (ξ-appˡ _) ()
pwBody-red (ξ-appʳ _) ()
pwBody-red (ξ-pairˡ _) ()
pwBody-red (ξ-pairʳ _) ()
pwBody-red (ξ-fst _) ()
pwBody-red (ξ-snd _) ()
pwBody-red (ξ-⌜Π⌝ˡ r) h = done
pwBody-red (ξ-⌜Π⌝ʳ r) h = step r done
pwBody-red (ξ-⌜Σ⌝ˡ _) ()
pwBody-red (ξ-⌜Σ⌝ʳ _) ()
pwBody-red (ξ-⌜Hom⌝ᶜ r) h = ⟶*-⌜Hom⌝ᶜ (pwBody-red r h)
pwBody-red (ξ-⌜Hom⌝ˡ r) h = step (ξ-⌜Hom⌝ˡ (ξ-appˡ (⟶-ren vs r))) done
pwBody-red (ξ-⌜Hom⌝ʳ r) h = step (ξ-⌜Hom⌝ʳ (ξ-appˡ (⟶-ren vs r))) done
pwBody-red (ξ-hreflᶜ _) ()
pwBody-red (ξ-hreflᵃ _) ()
pwBody-red (hrefl-pw _ _ _) ()
pwBody-red (tr-J-base _ _ _ _ _) ()
pwBody-red (tr-J-Σ _ _ _ _ _ _ _) ()
pwBody-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
pwBody-red (tr-taut _ _) ()
pwBody-red (tr-pw _ _ _ _ _) ()
pwBody-red (ξ-trᵈ _) ()
pwBody-red (ξ-trᵖ _) ()
pwBody-red (ξ-trᵉ _) ()

pwBody-red* : {C C' : RTm Γ} → pw? C ≡ true → C ⟶* C' →
              pwBody C ⟶* pwBody C'
pwBody-red* h done       = done
pwBody-red* h (step r p) =
  ⟶*-trans (pwBody-red r h) (pwBody-red* (pw?-red r h) p)


------------------------------------------------------------------------
-- Substitution is monotone in the substitution (pointwise `⟶*`).
------------------------------------------------------------------------

extS-mono : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟶* σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ⟶* extS σ' x
extS-mono h vz     = done
extS-mono h (vs x) = ⟶*-ren vs (h x)

subTm-monoˢ : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟶* σ' x) →
              (t : RTm Γ) → subTm σ t ⟶* subTm σ' t
subTm-monoˢ h (var x)   = h x
subTm-monoˢ h (lam t)   = ⟶*-lam (subTm-monoˢ (extS-mono h) t)
subTm-monoˢ h (app t u) =
  ⟶*-trans (⟶*-appˡ (subTm-monoˢ h t)) (⟶*-appʳ (subTm-monoˢ h u))
subTm-monoˢ h (pair a b) =
  ⟶*-trans (⟶*-pairˡ (subTm-monoˢ h a)) (⟶*-pairʳ (subTm-monoˢ h b))
subTm-monoˢ h (fst p) = ⟶*-fst (subTm-monoˢ h p)
subTm-monoˢ h (snd p) = ⟶*-snd (subTm-monoˢ h p)
subTm-monoˢ h ⌜base⌝  = done
subTm-monoˢ h (⌜Π⌝ c d) =
  ⟶*-trans (⟶*-⌜Π⌝ˡ (subTm-monoˢ h c)) (⟶*-⌜Π⌝ʳ (subTm-monoˢ (extS-mono h) d))
subTm-monoˢ h (⌜Σ⌝ c d) =
  ⟶*-trans (⟶*-⌜Σ⌝ˡ (subTm-monoˢ h c)) (⟶*-⌜Σ⌝ʳ (subTm-monoˢ (extS-mono h) d))
subTm-monoˢ h (⌜Hom⌝ c a b) =
  ⟶*-trans (⟶*-⌜Hom⌝ᶜ (subTm-monoˢ h c))
           (⟶*-trans (⟶*-⌜Hom⌝ˡ (subTm-monoˢ h a))
                     (⟶*-⌜Hom⌝ʳ (subTm-monoˢ h b)))
subTm-monoˢ h (hrefl c t) =
  ⟶*-trans (⟶*-hreflᶜ (subTm-monoˢ h c)) (⟶*-hreflᵃ (subTm-monoˢ h t))
subTm-monoˢ h (tr d p e) =
  ⟶*-trans (⟶*-trᵈ (subTm-monoˢ (extS-mono h) d))
           (⟶*-trans (⟶*-trᵖ (subTm-monoˢ h p)) (⟶*-trᵉ (subTm-monoˢ h e)))
subTm-monoˢ h (ap c b p) =
  ⟶*-trans (⟶*-apᶜ (subTm-monoˢ h c))
           (⟶*-trans (⟶*-apᵇ (subTm-monoˢ (extS-mono h) b))
                     (⟶*-apᵖ (subTm-monoˢ h p)))
subTm-monoˢ h (⌜Id⌝ c a b) =
  ⟶*-trans (⟶*-⌜Id⌝ᶜ (subTm-monoˢ h c))
           (⟶*-trans (⟶*-⌜Id⌝ˡ (subTm-monoˢ h a))
                     (⟶*-⌜Id⌝ʳ (subTm-monoˢ h b)))
subTm-monoˢ h (idrefl c t) =
  ⟶*-trans (⟶*-idreflᶜ (subTm-monoˢ h c)) (⟶*-idreflᵃ (subTm-monoˢ h t))
subTm-monoˢ h unit     = done
subTm-monoˢ h nzero    = done
subTm-monoˢ h (nsuc n) = ⟶*-nsuc (subTm-monoˢ h n)
subTm-monoˢ h (natrec z s n) =
  ⟶*-trans (⟶*-natrecᶻ (subTm-monoˢ h z))
           (⟶*-trans (⟶*-natrecˢ (subTm-monoˢ (extS-mono (extS-mono h)) s))
                     (⟶*-natrecⁿ (subTm-monoˢ h n)))
subTm-monoˢ h (jsub d p e) =
  ⟶*-trans (⟶*-jsubᵈ (subTm-monoˢ (extS-mono h) d))
           (⟶*-trans (⟶*-jsubᵖ (subTm-monoˢ h p))
                     (⟶*-jsubᵉ (subTm-monoˢ h e)))

single-mono : {u u' : RTm Γ} → u ⟶* u' →
              ∀ (x : Var (Γ ∙)) → single u x ⟶* single u' x
single-mono p vz     = p
single-mono p (vs x) = done

------------------------------------------------------------------------
-- Parallel reduction, reflexivity, and the two inclusions.
------------------------------------------------------------------------

infix 3 _⟹_
data _⟹_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  pvar  : (x : Var Γ) → var x ⟹ var x
  plam  : {t t' : RTm (Γ ∙)} → t ⟹ t' → lam t ⟹ lam t'
  papp  : {t t' u u' : RTm Γ} → t ⟹ t' → u ⟹ u' → app t u ⟹ app t' u'
  pβ    : {t t' : RTm (Γ ∙)} {u u' : RTm Γ} →
          t ⟹ t' → u ⟹ u' → app (lam t) u ⟹ subTm (single u') t'
  ppair : {a a' b b' : RTm Γ} → a ⟹ a' → b ⟹ b' → pair a b ⟹ pair a' b'
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
  ptr-J-Hom : {c a m : RTm (Γ ∙)} {c₁ a₁ b₁ s e e' : RTm Γ} →
              stkC? c₁ ≡ true → e ⟹ e' →
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

⟹-refl : (t : RTm Γ) → t ⟹ t
⟹-refl unit       = punit
⟹-refl nzero      = pnzero
⟹-refl (nsuc n)   = pnsuc (⟹-refl n)
⟹-refl (natrec z s n) = pnatrec (⟹-refl z) (⟹-refl s) (⟹-refl n)
⟹-refl (var x)    = pvar x
⟹-refl (lam t)    = plam (⟹-refl t)
⟹-refl (app t u)  = papp (⟹-refl t) (⟹-refl u)
⟹-refl (pair a b) = ppair (⟹-refl a) (⟹-refl b)
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

stkC?-⟹ : {C C' : RTm Γ} → C ⟹ C' → stkC? C ≡ true → stkC? C' ≡ true
stkC?-⟹ (pvar _) ()
stkC?-⟹ (plam _) ()
stkC?-⟹ (papp _ _) ()
stkC?-⟹ (pβ _ _) ()
stkC?-⟹ (ppair _ _) ()
stkC?-⟹ (pfst _) ()
stkC?-⟹ (psnd _) ()
stkC?-⟹ (pβfst _ _) ()
stkC?-⟹ (pβsnd _ _) ()
stkC?-⟹ p⌜base⌝ h = refl
stkC?-⟹ (p⌜Π⌝ _ _) ()
stkC?-⟹ (p⌜Σ⌝ _ _) h = refl
stkC?-⟹ (p⌜Hom⌝ pc _ _) h = stkC?-⟹ pc h
stkC?-⟹ (phrefl _ _) ()
stkC?-⟹ (phrefl-pw _ _ _) ()
stkC?-⟹ (ptr _ _ _) ()
stkC?-⟹ (ptr-J-base _) ()
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
⟶→⟹ (natrec-zero z s)  = pnatrec-zero (⟹-refl z) (⟹-refl s)
⟶→⟹ (natrec-suc z s n) = pnatrec-suc (⟹-refl z) (⟹-refl s) (⟹-refl n)
⟶→⟹ (ξ-nsuc r)    = pnsuc (⟶→⟹ r)
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
⟹→⟶* punit      = done
⟹→⟶* pnzero     = done
⟹→⟶* (pnsuc p)  = ⟶*-nsuc (⟹→⟶* p)
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
  ptr-J-Hom (trans (stkC?-ren ρ c₁) key) (⟹-ren ρ pe)
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
  ptr-J-Hom (stkC?-sub σ c₁ key) (⟹-sub h pe)
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

------------------------------------------------------------------------
-- The complete development, and the triangle: `t ⟹ u → u ⟹ t⁺`.
------------------------------------------------------------------------

-- (the J decision is PATH-major then motive-major: `_⁺` discriminates
-- the path, and the two helpers discriminate the ⌜Hom⌝-keyed motive —
-- keeping every congruence row reducible at generic sub-shapes)
_⁺ : RTm Γ → RTm Γ
trB⁺ : RTm (Γ ∙) → RTm Γ → RTm Γ → RTm Γ
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
var x ⁺            = var x
lam t ⁺            = lam (t ⁺)
pair a b ⁺         = pair (a ⁺) (b ⁺)
app (lam t) u ⁺    = subTm (single (u ⁺)) (t ⁺)
app (var x) u ⁺    = app (var x ⁺) (u ⁺)
app (app f a) u ⁺  = app (app f a ⁺) (u ⁺)
app (pair a b) u ⁺ = app (pair a b ⁺) (u ⁺)
app (fst p) u ⁺    = app (fst p ⁺) (u ⁺)
app (snd p) u ⁺    = app (snd p ⁺) (u ⁺)
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
fst (pair a b) ⁺   = a ⁺
fst (var x) ⁺      = fst (var x ⁺)
fst (lam t) ⁺      = fst (lam t ⁺)
fst (app f a) ⁺    = fst (app f a ⁺)
fst (fst p) ⁺      = fst (fst p ⁺)
fst (snd p) ⁺      = fst (snd p ⁺)
fst ⌜base⌝ ⁺       = fst (⌜base⌝ ⁺)
fst unit ⁺         = fst (unit ⁺)
fst nzero ⁺        = fst (nzero ⁺)
fst (nsuc n) ⁺     = fst (nsuc n ⁺)
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
snd (pair a b) ⁺   = b ⁺
snd (var x) ⁺      = snd (var x ⁺)
snd (lam t) ⁺      = snd (lam t ⁺)
snd (app f a) ⁺    = snd (app f a ⁺)
snd (fst p) ⁺      = snd (fst p ⁺)
snd (snd p) ⁺      = snd (snd p ⁺)
snd ⌜base⌝ ⁺       = snd (⌜base⌝ ⁺)
snd unit ⁺         = snd (unit ⁺)
snd nzero ⁺        = snd (nzero ⁺)
snd (nsuc n) ⁺     = snd (nsuc n ⁺)
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
tr d (hrefl ⌜base⌝ s) e ⁺        = trB⁺ d s e
tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e ⁺   = trS⁺ d c₁ c₂ s e
tr d (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e ⁺ = trI⁺ d c₁ a₁ b₁ s e
tr d (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e ⁺ = trH⁺ d c₁ a₁ b₁ s e
tr (var vz) (lam f) e ⁺          = app (lam (f ⁺)) (e ⁺)
tr (⌜Hom⌝ c a m) (lam f) e ⁺     = trP⁺ c a m f e
tr d p e ⁺ = tr (d ⁺) (p ⁺) (e ⁺)
-- `ap` — J fires on canonical `hrefl` at head-stable codes only (the
-- same discrimination as `tr`'s path analysis, minus the motive).
ap cB b (hrefl ⌜base⌝ s) ⁺        = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜Σ⌝ c₁ c₂) s) ⁺   = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜Id⌝ c₁ a₁ b₁) s) ⁺ = hrefl (cB ⁺) (subTm (single (s ⁺)) (b ⁺))
ap cB b (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) ⁺ = apH⁺ (stkC? c₁) cB b c₁ a₁ b₁ s
ap cB b p ⁺ = ap (cB ⁺) (b ⁺) (p ⁺)
-- the two-former kernel: Id is inert (congruences), and jsub's J is
-- UNKEYED — the refl-path row fires unconditionally.
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

trB⁺ (⌜Hom⌝ c a m) s e = e ⁺
trB⁺ d s e = tr (d ⁺) (hrefl ⌜base⌝ (s ⁺)) (e ⁺)

trS⁺ (⌜Hom⌝ c a m) c₁ c₂ s e = e ⁺
trS⁺ d c₁ c₂ s e = tr (d ⁺) (hrefl (⌜Σ⌝ (c₁ ⁺) (c₂ ⁺)) (s ⁺)) (e ⁺)

trI⁺ (⌜Hom⌝ c a m) c₁ a₁ b₁ s e = e ⁺
trI⁺ d c₁ a₁ b₁ s e = tr (d ⁺) (hrefl (⌜Id⌝ (c₁ ⁺) (a₁ ⁺) (b₁ ⁺)) (s ⁺)) (e ⁺)

hr⁺ true  C T = lam (hrefl (pwBody C) (app (renTm vs T) (var vz)))
hr⁺ false C T = hrefl C T

trH⁺ (⌜Hom⌝ c a m) c₁ a₁ b₁ s e = trHK⁺ (stkC? c₁) c a m c₁ a₁ b₁ s e
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

-- the triangle's Boolean dispatchers: given the developed pieces and
-- the key's transport, land in the right `hr⁺`/`trHK⁺`/`trPK⁺` branch.
hr-tri : {C' X s' Y : RTm Γ} (b : 𝔹) → (b ≡ true → pw? C' ≡ true) →
         C' ⟹ X → s' ⟹ Y → hrefl C' s' ⟹ hr⁺ b X Y
hr-tri true  kf px py = phrefl-pw (kf refl) px py
hr-tri false kf px py = phrefl px py

trHK-tri : {c c' a a' m m' : RTm (Γ ∙)}
           {c₁ c₁' a₁ a₁' b₁ b₁' s s' e e' : RTm Γ}
           (b : 𝔹) → (b ≡ true → stkC? c₁' ≡ true) →
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
          (k : 𝔹) → (k ≡ true → stkC? c₁' ≡ true) →
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
⟹-⁺ (ptr u@(ptr-J-base _) w@(phrefl (p⌜Id⌝ p₁ p₂ p₃) _) pe) = ptr (⟹-⁺ u) (⟹-⁺ w) (⟹-⁺ pe)
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
  trHK-tri _ (stkC?-⟹ pc₁) (pw?-⟹ pc₁)
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
  subst (λ b → _ ⟹ trHK⁺ b _ _ _ c₁ a₁ b₁ _ _) (sym (pw⊥stk c₁ key))
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
⟹-⁺ (pap pcB pb (phrefl p⌜base⌝ ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl (p⌜Σ⌝ _ _) ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl (p⌜Id⌝ _ _ _) ps)) =
  pap-J refl (⟹-⁺ pcB) (⟹-⁺ pb) (⟹-⁺ ps)
⟹-⁺ (pap pcB pb (phrefl (p⌜Hom⌝ pc pa pz) ps)) =
  apH-tri _ (stkC?-⟹ pc) (pw?-⟹ pc)
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
  subst (λ k → _ ⟹ apH⁺ k _ _ c₁ a₁ b₁ _) (sym (pw⊥stk c₁ key))
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
