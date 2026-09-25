------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ ERASURE IS SOUND: the annotated kernel means the
--                      unannotated one.  (PLAN-BIDI §3d)
--
--       erase : Γ ⊢ᴬ t ∷ A → ⌈ Γ ⌉ᶜ ⊢ ⌈ t ⌉ ∷ ⌈ A ⌉ᵀ
--
-- ★ THIS IS THE WHOLE BRIDGE.  Every metatheorem of `RTm` now applies to
--   the annotated kernel through it — consistency is below, one line.
--   Conversion needs no bridge at all: `⊢ᴬconv` IS `⊢conv` on erasures.
--
-- ★ The only content is substitution: a rule whose conclusion substitutes
--   into an `ATy` erases to the `⊢` rule whose conclusion substitutes into
--   the erasure — `era-subTy`/`era-subTm`, stated against a pointwise-equal
--   `RTm` substitution, close each such case with one cast.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Erasure where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong; subst; ⊥ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.TypingA
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast )
open import DirectedHoTT.Metatheory.Canonicity using ( consistency )

private
  variable
    Γ : ACtx

-- the erasures of the two annotated substitutions the rules use
-- (public: the checker states its targets through them)
module _ where
  single-era : {Δ : Cx} (u : ATm Δ) → ∀ x → ⌈ singleᴬ u x ⌉ ≡ single ⌈ u ⌉ x
  single-era u vz     = refl
  single-era u (vs x) = refl

  nrs-era : {Δ : Cx} → ∀ (x : Var (Δ ∙)) → ⌈ nrsᴬ x ⌉ ≡ nrs x
  nrs-era vz     = refl
  nrs-era (vs x) = refl

  sub1 : {Δ : Cx} (u : ATm Δ) (B : ATy (Δ ∙)) →
         ⌈ subTyᴬ (singleᴬ u) B ⌉ᵀ ≡ subTy (single ⌈ u ⌉) ⌈ B ⌉ᵀ
  sub1 u B = era-subTy (singleᴬ u) (single ⌈ u ⌉) (single-era u) B

  sub1ᵗ : {Δ : Cx} (u : ATm Δ) (d : ATm (Δ ∙)) →
          ⌈ subTmᴬ (singleᴬ u) d ⌉ ≡ subTm (single ⌈ u ⌉) ⌈ d ⌉
  sub1ᵗ u d = era-subTm (singleᴬ u) (single ⌈ u ⌉) (single-era u) d

erase-∋ : {x : Var ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → Γ ∋ᴬ x ∷ A → ⌈ Γ ⌉ᶜ ∋ x ∷ ⌈ A ⌉ᵀ
erase-∋ {Γ = Γ ▹ᴬ A} (hereᴬ {A = A}) =
  subst (λ Z → ⌈ Γ ▹ᴬ A ⌉ᶜ ∋ vz ∷ Z) (sym (era-renTy vs A)) (here {A = ⌈ A ⌉ᵀ})
erase-∋ {Γ = Γ ▹ᴬ B} (thereᴬ {A = A} {x = x} v) =
  subst (λ Z → ⌈ Γ ▹ᴬ B ⌉ᶜ ∋ vs x ∷ Z) (sym (era-renTy vs A))
        (there {A = ⌈ A ⌉ᵀ} {B = ⌈ B ⌉ᵀ} (erase-∋ v))

erase    : {t : ATm ⌊ Γ ⌋ᴬ} {A : ATy ⌊ Γ ⌋ᴬ} → Γ ⊢ᴬ t ∷ A → ⌈ Γ ⌉ᶜ ⊢ ⌈ t ⌉ ∷ ⌈ A ⌉ᵀ
erase-ty : {A : ATy ⌊ Γ ⌋ᴬ} → Γ ⊢tyᴬ A → ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ

erase (⊢ᴬvar v) = ⊢var (erase-∋ v)
erase (⊢ᴬlam dA d) = ⊢lam (erase-ty dA) (erase d)
erase (⊢ᴬapp {B = B} {u = u} d₁ d₂) =
  ⊢-cast (sym (sub1 u B)) (⊢app (erase d₁) (erase d₂))
erase (⊢ᴬpair {B = B} {a = a} dB da db) =
  ⊢pair (erase-ty dB) (erase da) (⊢-cast (sub1 a B) (erase db))
erase (⊢ᴬabsurd dc de) = ⊢absurd (erase dc) (erase de)
erase (⊢ᴬordtr da dt du dp dq) =
  ⊢ordtr (erase da) (erase dt) (erase du) (erase dp) (erase dq)
erase (⊢ᴬfst d) = ⊢fst (erase d)
erase (⊢ᴬsnd {B = B} {p = p} d) = ⊢-cast (sym (sub1 (fst p) B)) (⊢snd (erase d))
erase ⊢ᴬ⌜base⌝ = ⊢⌜base⌝
erase (⊢ᴬ⌜Π⌝ dc dd) = ⊢⌜Π⌝ (erase dc) (erase dd)
erase (⊢ᴬ⌜Σ⌝ dc dd) = ⊢⌜Σ⌝ (erase dc) (erase dd)
erase (⊢ᴬ⌜Hom⌝ dc da db) = ⊢⌜Hom⌝ (erase dc) (erase da) (erase db)
erase (⊢ᴬhrefl dc dt) = ⊢hrefl (erase dc) (erase dt)
erase (⊢ᴬtrU dt du dp de) = ⊢trU (erase dt) (erase du) (erase dp) (erase de)
erase (⊢ᴬtr {c = c} {a = a} {t = t} {u = u} dA dc da dvz nn o₁ o₂ dt du dp de) =
  ⊢-cast (cong El (sym (sub1ᵗ u (⌜Hom⌝ c a (var vz)))))
    (⊢tr (erase dc) (erase da) (erase dvz) nn o₁ o₂ (erase dt) (erase du) (erase dp)
         (⊢-cast (cong El (sub1ᵗ t (⌜Hom⌝ c a (var vz)))) (erase de)))
erase (⊢ᴬap {cB = cB} {b = b} {t = t} {u = u} dcA fl dcB db dt du dp) =
  ⊢-cast (cong₂' (sym (sub1ᵗ t b)) (sym (sub1ᵗ u b)))
    (⊢ap (erase dcA) fl (erase dcB)
         (⊢-cast (cong El (era-renTm vs cB)) (erase db))
         (erase dt) (erase du) (erase dp))
  where
  cong₂' : ∀ {x x' y y'} → x ≡ x' → y ≡ y' → Hom (El ⌈ cB ⌉) x y ≡ Hom (El ⌈ cB ⌉) x' y'
  cong₂' refl refl = refl
erase (⊢ᴬ⌜Id⌝ dc da db) = ⊢⌜Id⌝ (erase dc) (erase da) (erase db)
erase ⊢ᴬ⌜Nat⌝ = ⊢⌜Nat⌝
erase (⊢ᴬ⌜Mu⌝ w) = ⊢⌜Mu⌝ w
erase ⊢ᴬ⌜Unit⌝ = ⊢⌜Unit⌝
erase (⊢ᴬidrefl dc dt) = ⊢idrefl (erase dc) (erase dt)
erase (⊢ᴬjsub {d = d} {t = t} {u = u} dA dd dt du dp de) =
  ⊢-cast (cong El (sym (sub1ᵗ u d)))
    (⊢jsub (erase dd) (erase dt) (erase du) (erase dp)
           (⊢-cast (cong El (sub1ᵗ t d)) (erase de)))
erase ⊢ᴬunit = ⊢unit
erase ⊢ᴬnzero = ⊢nzero
erase (⊢ᴬnsuc d) = ⊢nsuc (erase d)
erase (⊢ᴬnatrec {M = M} {n = n} dM dz ds dn) =
  ⊢-cast (sym (sub1 n M))
    (⊢natrec (erase-ty dM)
             (⊢-cast (sub1 nzero M) (erase dz))
             (⊢-cast (era-subTy nrsᴬ nrs nrs-era M) (erase ds))
             (erase dn))
erase (⊢ᴬconv d c) = ⊢conv (erase d) c

erase-ty tyᴬ-base = ty-base
erase-ty tyᴬ-U    = ty-U
erase-ty (tyᴬ-Π dA dB) = ty-Π (erase-ty dA) (erase-ty dB)
erase-ty (tyᴬ-Σ dA dB) = ty-Σ (erase-ty dA) (erase-ty dB)
erase-ty (tyᴬ-El dc) = ty-El (erase dc)
erase-ty (tyᴬ-Id dA dt du) = ty-Id (erase-ty dA) (erase dt) (erase du)
erase-ty tyᴬ-Unit = ty-Unit
erase-ty tyᴬ-Nat  = ty-Nat
erase-ty (tyᴬ-Mu w) = ty-Mu w
erase-ty (tyᴬ-Hom dA dt du) = ty-Hom (erase-ty dA) (erase dt) (erase du)

------------------------------------------------------------------------
-- ★ The first transferred theorem: the annotated kernel is CONSISTENT.
------------------------------------------------------------------------

consistencyᴬ : {t : ATm ε} → ◇ᴬ ⊢ᴬ t ∷ base → ⊥
consistencyᴬ d = consistency (erase d)
