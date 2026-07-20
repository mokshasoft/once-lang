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
  using ( _≡_; refl; sym; trans; subst; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app; Ren; extR; renTm
        ; Sub; extS; subTm; renTm-subTm; subTm-renTm; subTm-cong
        ; _ᵣ∘ₛ_; _ₛ∘ᵣ_ )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶_; β; ξ-lam; ξ-appˡ; ξ-appʳ; _⟶*_; done; step
        ; _≅_; cred; crfl; csym; ctrn )
open import poc.OCP0009.NbEPDirDBSR using ( sub-comm; ⟶-sub )

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

⟶-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ⟶ u → renTm ρ t ⟶ renTm ρ u
⟶-ren ρ (β t u)    =
  subst (λ z → renTm ρ (app (lam t) u) ⟶ z)
        (sym (ren-comm ρ t u))
        (β (renTm (extR ρ) t) (renTm ρ u))
⟶-ren ρ (ξ-lam r)  = ξ-lam (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-appˡ r) = ξ-appˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-appʳ r) = ξ-appʳ (⟶-ren ρ r)

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

single-mono : {u u' : RTm Γ} → u ⟶* u' →
              ∀ (x : Var (Γ ∙)) → single u x ⟶* single u' x
single-mono p vz     = p
single-mono p (vs x) = done

------------------------------------------------------------------------
-- Parallel reduction, reflexivity, and the two inclusions.
------------------------------------------------------------------------

infix 3 _⟹_
data _⟹_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  pvar : (x : Var Γ) → var x ⟹ var x
  plam : {t t' : RTm (Γ ∙)} → t ⟹ t' → lam t ⟹ lam t'
  papp : {t t' u u' : RTm Γ} → t ⟹ t' → u ⟹ u' → app t u ⟹ app t' u'
  pβ   : {t t' : RTm (Γ ∙)} {u u' : RTm Γ} →
         t ⟹ t' → u ⟹ u' → app (lam t) u ⟹ subTm (single u') t'

⟹-refl : (t : RTm Γ) → t ⟹ t
⟹-refl (var x)   = pvar x
⟹-refl (lam t)   = plam (⟹-refl t)
⟹-refl (app t u) = papp (⟹-refl t) (⟹-refl u)

⟶→⟹ : {t u : RTm Γ} → t ⟶ u → t ⟹ u
⟶→⟹ (β t u)    = pβ (⟹-refl t) (⟹-refl u)
⟶→⟹ (ξ-lam r)  = plam (⟶→⟹ r)
⟶→⟹ (ξ-appˡ r) = papp (⟶→⟹ r) (⟹-refl _)
⟶→⟹ (ξ-appʳ r) = papp (⟹-refl _) (⟶→⟹ r)

⟹→⟶* : {t u : RTm Γ} → t ⟹ u → t ⟶* u
⟹→⟶* (pvar x)  = done
⟹→⟶* (plam p)  = ⟶*-lam (⟹→⟶* p)
⟹→⟶* (papp p q) =
  ⟶*-trans (⟶*-appˡ (⟹→⟶* p)) (⟶*-appʳ (⟹→⟶* q))
⟹→⟶* (pβ {t = t} {t' = t'} {u = u} {u' = u'} p q) =
  step (β t u)
       (⟶*-trans (⟶*-sub (single u) (⟹→⟶* p))
                 (subTm-monoˢ (single-mono (⟹→⟶* q)) t'))

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

single-⟹ : {u u' : RTm Γ} → u ⟹ u' →
           (x : Var (Γ ∙)) → single u x ⟹ single u' x
single-⟹ p vz     = p
single-⟹ p (vs x) = pvar x

------------------------------------------------------------------------
-- The complete development, and the triangle: `t ⟹ u → u ⟹ t⁺`.
------------------------------------------------------------------------

_⁺ : RTm Γ → RTm Γ
var x ⁺           = var x
lam t ⁺           = lam (t ⁺)
app (lam t) u ⁺   = subTm (single (u ⁺)) (t ⁺)
app (var x) u ⁺   = app (var x) (u ⁺)
app (app f a) u ⁺ = app (app f a ⁺) (u ⁺)

⟹-⁺ : {t u : RTm Γ} → t ⟹ u → u ⟹ t ⁺
⟹-⁺ (pvar x)              = pvar x
⟹-⁺ (plam p)              = plam (⟹-⁺ p)
⟹-⁺ (papp (pvar x) q)     = papp (pvar x) (⟹-⁺ q)
⟹-⁺ (papp (plam p) q)     = pβ (⟹-⁺ p) (⟹-⁺ q)
⟹-⁺ (papp (papp p₁ p₂) q) = papp (⟹-⁺ (papp p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (papp (pβ p₁ p₂) q)   = papp (⟹-⁺ (pβ p₁ p₂)) (⟹-⁺ q)
⟹-⁺ (pβ p q)              = ⟹-sub (single-⟹ (⟹-⁺ q)) (⟹-⁺ p)

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
