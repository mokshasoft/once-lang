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
  using ( _≡_; refl; sym; trans; subst; cong; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app; pair; fst; snd
        ; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ⌜Hom⌝-cong₃; tr-cong₃
        ; Ren; extR; renTm; renTm-renTm; renTm-cong
        ; Sub; extS; subTm; renTm-subTm; subTm-renTm; subTm-cong
        ; _ᵣ∘ₛ_; _ₛ∘ᵣ_; _∘ᵣ_ )
open import poc.OCP0009.NbEPDirDBType
  using ( single; swp; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; tr-J-base; tr-J-Σ; tr-taut
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; _⟶*_; done; step
        ; _≅_; cred; crfl; csym; ctrn )
open import poc.OCP0009.NbEPDirDBSR
  using ( sub-comm; ⟶-sub; wk-sub; wk₁-sub; swp-sub )

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
⟶-ren ρ (ξ-⌜Π⌝ˡ r) = ξ-⌜Π⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Π⌝ʳ r) = ξ-⌜Π⌝ʳ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-⌜Σ⌝ˡ r) = ξ-⌜Σ⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Σ⌝ʳ r) = ξ-⌜Σ⌝ʳ (⟶-ren (extR ρ) r)
⟶-ren ρ (tr-J-base d s e) =
  tr-J-base (renTm (extR ρ) d) (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-J-Σ d c₁ c₂ s e) =
  tr-J-Σ (renTm (extR ρ) d) (renTm ρ c₁) (renTm (extR ρ) c₂)
         (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-taut f e) = tr-taut (renTm (extR ρ) f) (renTm ρ e)
⟶-ren ρ (ξ-⌜Hom⌝ᶜ r) = ξ-⌜Hom⌝ᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Hom⌝ˡ r) = ξ-⌜Hom⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Hom⌝ʳ r) = ξ-⌜Hom⌝ʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-hreflᶜ r) = ξ-hreflᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-hreflᵃ r) = ξ-hreflᵃ (⟶-ren ρ r)
⟶-ren ρ (ξ-trᵈ r)    = ξ-trᵈ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-trᵖ r)    = ξ-trᵖ (⟶-ren ρ r)
⟶-ren ρ (ξ-trᵉ r)    = ξ-trᵉ (⟶-ren ρ r)

⟶*-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ⟶* u → renTm ρ t ⟶* renTm ρ u
⟶*-ren ρ done       = done
⟶*-ren ρ (step r p) = step (⟶-ren ρ r) (⟶*-ren ρ p)

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
  ptr-J-base : {d : RTm (Γ ∙)} {s e e' : RTm Γ} →
               e ⟹ e' → tr d (hrefl ⌜base⌝ s) e ⟹ e'
  ptr-J-Σ : {d : RTm (Γ ∙)} {c₁ : RTm Γ} {c₂ : RTm (Γ ∙)} {s e e' : RTm Γ} →
            e ⟹ e' → tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e ⟹ e'
  ptr-taut : {f f' : RTm (Γ ∙)} {e e' : RTm Γ} → f ⟹ f' → e ⟹ e' →
             tr (var vz) (lam f) e ⟹ app (lam f') e'

⟹-refl : (t : RTm Γ) → t ⟹ t
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
⟹-refl (tr d p e)    = ptr (⟹-refl d) (⟹-refl p) (⟹-refl e)

⟶→⟹ : {t u : RTm Γ} → t ⟶ u → t ⟹ u
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
⟶→⟹ (tr-J-base d s e)    = ptr-J-base (⟹-refl e)
⟶→⟹ (tr-J-Σ d c₁ c₂ s e) = ptr-J-Σ (⟹-refl e)
⟶→⟹ (tr-taut f e)        = ptr-taut (⟹-refl f) (⟹-refl e)
⟶→⟹ (ξ-⌜Hom⌝ᶜ r) = p⌜Hom⌝ (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-⌜Hom⌝ˡ r) = p⌜Hom⌝ (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-⌜Hom⌝ʳ r) = p⌜Hom⌝ (⟹-refl _) (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-hreflᶜ r) = phrefl (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-hreflᵃ r) = phrefl (⟹-refl _) (⟶→⟹ r)
⟶→⟹ (ξ-trᵈ r)    = ptr (⟶→⟹ r) (⟹-refl _) (⟹-refl _)
⟶→⟹ (ξ-trᵖ r)    = ptr (⟹-refl _) (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-trᵉ r)    = ptr (⟹-refl _) (⟹-refl _) (⟶→⟹ r)

⟹→⟶* : {t u : RTm Γ} → t ⟹ u → t ⟶* u
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
⟹→⟶* (ptr-J-base {d = d} {s} {e} p)          = step (tr-J-base d s e) (⟹→⟶* p)
⟹→⟶* (ptr-J-Σ {d = d} {c₁} {c₂} {s} {e} p)   = step (tr-J-Σ d c₁ c₂ s e) (⟹→⟶* p)
⟹→⟶* (ptr-taut {f = f} {f'} {e} {e'} p q) =
  step (tr-taut f e)
       (⟶*-trans (⟶*-appˡ (⟶*-lam (⟹→⟶* p))) (⟶*-appʳ (⟹→⟶* q)))

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
⟹-ren ρ (ptr-taut p q) = ptr-taut (⟹-ren (extR ρ) p) (⟹-ren ρ q)

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
⟹-sub h (ptr-taut p q) = ptr-taut (⟹-sub (⟹-exts h) p) (⟹-sub h q)

single-⟹ : {u u' : RTm Γ} → u ⟹ u' →
           (x : Var (Γ ∙)) → single u x ⟹ single u' x
single-⟹ p vz     = p
single-⟹ p (vs x) = pvar x

------------------------------------------------------------------------
-- The complete development, and the triangle: `t ⟹ u → u ⟹ t⁺`.
------------------------------------------------------------------------

_⁺ : RTm Γ → RTm Γ
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
app (⌜Π⌝ c d) u ⁺  = app (⌜Π⌝ c d ⁺) (u ⁺)
app (⌜Σ⌝ c d) u ⁺  = app (⌜Σ⌝ c d ⁺) (u ⁺)
app (⌜Hom⌝ c a b) u ⁺ = app (⌜Hom⌝ c a b ⁺) (u ⁺)
app (hrefl c t) u ⁺   = app (hrefl c t ⁺) (u ⁺)
app (tr d p e) u ⁺    = app (tr d p e ⁺) (u ⁺)
fst (pair a b) ⁺   = a ⁺
fst (var x) ⁺      = fst (var x ⁺)
fst (lam t) ⁺      = fst (lam t ⁺)
fst (app f a) ⁺    = fst (app f a ⁺)
fst (fst p) ⁺      = fst (fst p ⁺)
fst (snd p) ⁺      = fst (snd p ⁺)
fst ⌜base⌝ ⁺       = fst (⌜base⌝ ⁺)
fst (⌜Π⌝ c d) ⁺    = fst (⌜Π⌝ c d ⁺)
fst (⌜Σ⌝ c d) ⁺    = fst (⌜Σ⌝ c d ⁺)
fst (⌜Hom⌝ c a b) ⁺ = fst (⌜Hom⌝ c a b ⁺)
fst (hrefl c t) ⁺   = fst (hrefl c t ⁺)
fst (tr d p e) ⁺    = fst (tr d p e ⁺)
snd (pair a b) ⁺   = b ⁺
snd (var x) ⁺      = snd (var x ⁺)
snd (lam t) ⁺      = snd (lam t ⁺)
snd (app f a) ⁺    = snd (app f a ⁺)
snd (fst p) ⁺      = snd (fst p ⁺)
snd (snd p) ⁺      = snd (snd p ⁺)
snd ⌜base⌝ ⁺       = snd (⌜base⌝ ⁺)
snd (⌜Π⌝ c d) ⁺    = snd (⌜Π⌝ c d ⁺)
snd (⌜Σ⌝ c d) ⁺    = snd (⌜Σ⌝ c d ⁺)
snd (⌜Hom⌝ c a b) ⁺ = snd (⌜Hom⌝ c a b ⁺)
snd (hrefl c t) ⁺   = snd (hrefl c t ⁺)
snd (tr d p e) ⁺    = snd (tr d p e ⁺)
⌜base⌝ ⁺           = ⌜base⌝
⌜Π⌝ c d ⁺          = ⌜Π⌝ (c ⁺) (d ⁺)
⌜Σ⌝ c d ⁺          = ⌜Σ⌝ (c ⁺) (d ⁺)
⌜Hom⌝ c a b ⁺      = ⌜Hom⌝ (c ⁺) (a ⁺) (b ⁺)
-- `hrefl` is operationally inert (its unfold family is deferred to the
-- canonicity package) — congruence only.
hrefl c f ⁺         = hrefl (c ⁺) (f ⁺)
-- `tr` — the five path-keyed rules (SpikeTr), then congruence.  The
-- clause order encodes the case tree: split the path first (J fires on
-- canonical `hrefl` — head-stable stuck codes only), then the motive
-- (taut at `var vz`, pointwise composition at a `⌜Π⌝`-ambient `⌜Hom⌝`).
tr d (hrefl ⌜base⌝ s) e ⁺        = e ⁺
tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e ⁺   = e ⁺
tr (var vz) (lam f) e ⁺          = app (lam (f ⁺)) (e ⁺)
tr d p e ⁺ = tr (d ⁺) (p ⁺) (e ⁺)

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
⟹-⁺ (pfst w@(p⌜Hom⌝ _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(phrefl _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr _ _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-base _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-J-Σ _)) = pfst (⟹-⁺ w)
⟹-⁺ (pfst w@(ptr-taut _ _)) = pfst (⟹-⁺ w)
⟹-⁺ (psnd w@(p⌜Hom⌝ _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(phrefl _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr _ _ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-base _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-J-Σ _)) = psnd (⟹-⁺ w)
⟹-⁺ (psnd w@(ptr-taut _ _)) = psnd (⟹-⁺ w)
-- `⌜Hom⌝` — congruence only.
⟹-⁺ (p⌜Hom⌝ p q r)         = p⌜Hom⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
-- `hrefl` — inert: congruence only.
⟹-⁺ (phrefl p q) = phrefl (⟹-⁺ p) (⟹-⁺ q)
-- the five `tr` roots.
⟹-⁺ (ptr-J-base p)  = ⟹-⁺ p
⟹-⁺ (ptr-J-Σ p)     = ⟹-⁺ p
⟹-⁺ (ptr-taut p q)  = papp (plam (⟹-⁺ p)) (⟹-⁺ q)
-- `tr` congruence — mirroring `_⁺`'s tree: the path's derivation
-- discriminates first (J at the three stable stuck codes), then the
-- motive (taut at `var vz`, pointwise at the `⌜Π⌝`-ambient `⌜Hom⌝`).
⟹-⁺ (ptr pd (phrefl p⌜base⌝ ps) pe)           = ptr-J-base (⟹-⁺ pe)
⟹-⁺ (ptr pd (phrefl (p⌜Σ⌝ p₁ p₂) ps) pe)      = ptr-J-Σ (⟹-⁺ pe)
⟹-⁺ (ptr pd w@(phrefl (p⌜Hom⌝ _ _ _) _) pe) = ptr (⟹-⁺ pd) (⟹-⁺ w) (⟹-⁺ pe)
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
-- Path is a lambda — split the motive.
⟹-⁺ (ptr (pvar vz) (plam pf) pe)     = ptr-taut (⟹-⁺ pf) (⟹-⁺ pe)
⟹-⁺ (ptr w@(pvar (vs _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (pvar vz)) v@(plam _) pe) =
  ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (pvar (vs _))) v@(plam _) pe) =
  ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (plam _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (papp _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (pβ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (ppair _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (pfst _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (psnd _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (pβfst _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (pβsnd _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (p⌜base⌝)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (p⌜Π⌝ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (p⌜Σ⌝ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (p⌜Hom⌝ _ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (phrefl _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (ptr _ _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (ptr-J-base _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (ptr-J-Σ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Π⌝ _ _) _ (ptr-taut _ _)) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (pvar _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (plam _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (papp _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (pβ _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (ppair _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (pfst _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (psnd _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (pβfst _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (pβsnd _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜base⌝) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Σ⌝ _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (p⌜Hom⌝ _ _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (phrefl _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (ptr _ _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (ptr-J-base _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (ptr-J-Σ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
⟹-⁺ (ptr w@(p⌜Hom⌝ (ptr-taut _ _) _ _) v@(plam _) pe) = ptr (⟹-⁺ w) (⟹-⁺ v) (⟹-⁺ pe)
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
