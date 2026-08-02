------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 27 — (A2) the DIRECTED IDENTITY TYPE over the
--                            dependent-kernel terms: directed `J`, `no-sym`
--
-- The distinctively dHoTT piece (HANDOFF §3 Tier A2). `NbEPDirJ` (dHoTT-1)
-- established that `Hom = ⟶*` is a DIRECTED identity type — with directed `J`
-- and `sym` REFUTED — but over the CCC point-free terms. This module carries
-- that story to the actual DEPENDENT-KERNEL terms (`RTm`, `NbEPDirDBType`),
-- so the directed identity type reasons about transformations of the SAME
-- terms the typing judgment types.
--
--   * `J⟶` — directed path induction on `Hom t u = t ⟶* u` (`done ↦ refl`),
--     and `J-tgt` (based at the target, structural).
--   * `no-sym` — symmetry is REFUTED (not merely absent): a global
--     `Hom t u → Hom u t` would reverse an irreversible β-step. `var`s are
--     stuck (`var-stuck`), so the reduct of a redex cannot reduce back.
--   * `transport⟶` / `yo` — directed transport (costs step-covariance of the
--     motive) and the covariant Yoneda action; every map covariant, no `sym`.
--
-- Honest ceiling: `Hom` here is the META relation `⟶*`, not yet an
-- object-language `RTy` former with `refl : RTm` and `J` as TYPING rules —
-- full internalization needs extending `RTy`/`RTm` (and the conversion rule to
-- see `refl`). This module settles the ELIMINATION principle over the kernel's
-- terms; the syntactic former is the remaining step. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBIdJ where

open import normalizer.Syntax.Types using ( _≡_; refl; ¬_; ⊥ )
open import poc.OCP0009.NbEPDirDBPi using ( Cx; ε; _∙; Var; vz; RTm; var; lam; app )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; β; _⟶*_; done; step; Hom⟶ )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Directed path induction: `Hom⟶` IS a directed identity type.
------------------------------------------------------------------------

J⟶ : (P : (t u : RTm Γ) → Hom⟶ t u → Set)
   → (∀ t → P t t done)
   → (∀ {t u v} (s : t ⟶ u) (p : Hom⟶ u v) → P u v p → P t v (step s p))
   → ∀ {t u} (p : Hom⟶ t u) → P t u p
J⟶ P prefl pstep done       = prefl _
J⟶ P prefl pstep (step s p) = pstep s p (J⟶ P prefl pstep p)

-- Based at the target (structural, because chains grow at the source).
J-tgt : {v : RTm Γ} (P : ∀ t → Hom⟶ t v → Set)
      → P v done
      → (∀ {t u} (s : t ⟶ u) (p : Hom⟶ u v) → P u p → P t (step s p))
      → ∀ {t} (p : Hom⟶ t v) → P t p
J-tgt P prefl pstep done       = prefl
J-tgt P prefl pstep (step s p) = pstep s p (J-tgt P prefl pstep p)

------------------------------------------------------------------------
-- NO SYM — refuted. Variables are stuck, so an irreversible β cannot reverse.
------------------------------------------------------------------------

var-stuck : {x : Var Γ} {u : RTm Γ} → var x ⟶ u → ⊥
var-stuck ()

-- A concrete irreversible pass: `(λx.x) y ⟶ y`, and `y` (a variable) is stuck.
βid : app (lam (var vz)) (var vz) ⟶ var (vz {ε})
βid = β (var vz) (var vz)

opt : Hom⟶ (app (lam (var vz)) (var vz)) (var (vz {ε}))
opt = step βid done

no-back : ¬ Hom⟶ (var (vz {ε})) (app (lam (var vz)) (var vz))
no-back (step s _) = var-stuck s

no-sym : ¬ ({Γ : Cx} {t u : RTm Γ} → Hom⟶ t u → Hom⟶ u t)
no-sym symH = no-back (symH opt)

------------------------------------------------------------------------
-- Directed transport — not free; it costs STEP-COVARIANCE of the motive.
------------------------------------------------------------------------

transport⟶ : (P : RTm Γ → Set)
           → (∀ {u v} → u ⟶ v → P u → P v)
           → ∀ {t u} → Hom⟶ t u → P t → P u
transport⟶ P cov done       x = x
transport⟶ P cov (step s p) x = transport⟶ P cov p (cov s x)

-- The canonical covariant family is the hom-family itself (Yoneda action).
snoc : {t u v : RTm Γ} → Hom⟶ t u → u ⟶ v → Hom⟶ t v
snoc done       s = step s done
snoc (step s₀ p) s = step s₀ (snoc p s)

yo : {t u v : RTm Γ} → Hom⟶ u v → Hom⟶ t u → Hom⟶ t v
yo q = transport⟶ (Hom⟶ _) (λ s r → snoc r s) q
