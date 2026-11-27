-- SPIKE (SPIKE-GENERIC-SYNTAX S8): the generic reduction at the REAL kernel
-- signature (`Spec/Syntax`'s KSig), with three contractions: β (substitution),
-- natrec's zero rule (a nested inversion), and a GUARDED transport rule with a
-- side condition (the shape of the kernel's non-uniform rules). Each rule
-- supplies only its own content: that renaming preserves and reflects it.
-- Congruence, SN anti-renaming and reduction reflection come from `tmp.RedGen`.

{-# OPTIONS --safe #-}
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Scope
open import DirectedHoTT.Spec.Syntax
import DirectedHoTT.Spec.Bind as G
open import tmp.RedGen KSig
module tmp.RedKern where
open G.Trav KSig using ( ren; sub; single; renK; renS; ext; module SynK )
open G using ( _,ᶠ_; ⟨⟩ )
open G._⊗_ using ( fstᶠ; sndᶠ )

private variable Γ Δ : Cx

------------------------------------------------------------------------
-- A side condition that asks ONE question of the tag (so renaming keeps it)
------------------------------------------------------------------------

flatTag : KCon tm → Bool
flatTag `⌜Nat⌝ = true
flatTag _      = false

flat? : RTm Γ → Bool
flat? (var x)       = false
flat? (KS.node c _) = flatTag c

flat?-ren : (ρ : Var Γ → Var Δ) (c : RTm Γ) → flat? (ren ρ c) ≡ flat? c
flat?-ren ρ (var x)       = refl
flat?-ren ρ (KS.node c _) = refl

------------------------------------------------------------------------
-- The contractions (the content)
------------------------------------------------------------------------

infix 4 _▷_
data _▷_ : ∀ {s Γ} → G.Tm KSig s Γ → G.Tm KSig s Γ → Set where
  β   : ∀ {Γ} {b : RTm (Γ ∙)} {a : RTm Γ} → app (lam b) a ▷ sub (single a) b
  ι0  : ∀ {Γ} {z : RTm Γ} {s : RTm ((Γ ∙) ∙)} → natrec z s nzero ▷ z
  trF : ∀ {Γ} {d : RTm (Γ ∙)} {c t e : RTm Γ} → flat? c ≡ true → tr d (hrefl c t) e ▷ e

private
  cast▷ : ∀ {s Γ} {a b b′ : G.Tm KSig s Γ} → b ≡ b′ → a ▷ b → a ▷ b′
  cast▷ refl r = r

-- renaming PRESERVES each contraction
▷-ren : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {a b : G.Tm KSig s Γ} → a ▷ b → ren ρ a ▷ ren ρ b
▷-ren ρ (β {b = b} {a}) = cast▷ (sym (SynK.trav-single renK renS ρ a b)) β
▷-ren ρ ι0              = ι0
▷-ren ρ (trF {c = c} h) = trF (trans (flat?-ren ρ c) h)

-- renaming REFLECTS each contraction: explicit inversion through `ren-node`,
-- never Agda inverting the traversal
▷-anti : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {a b : G.Tm KSig s Δ} → a ▷ b → (t : G.Tm KSig s Γ) → a ≡ ren ρ t
       → Σ (G.Tm KSig s Γ) (λ u → (t ▷ u) × (b ≡ ren ρ u))
▷-anti ρ (β {b = b} {a}) t e with ren-node ρ t (sym e)
... | (z₁ ,ᶠ z₂ ,ᶠ ⟨⟩) , (refl , e₂) with ren-node ρ z₁ (cong fstᶠ e₂)
...   | (w ,ᶠ ⟨⟩) , (refl , e₃) =
        sub (single z₂) w ,
        (β , trans (cong₂′ (λ x y → sub (single x) y) (sym (cong (λ p → fstᶠ (sndᶠ p)) e₂)) (sym (cong fstᶠ e₃)))
                   (sym (SynK.trav-single renK renS ρ z₂ w)))
  where
  cong₂′ : ∀ {A B C : Set} (f : A → B → C) {x x′ y y′} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
  cong₂′ f refl refl = refl
▷-anti ρ ι0 t e with ren-node ρ t (sym e)
... | (z₀ ,ᶠ s₀ ,ᶠ n₀ ,ᶠ ⟨⟩) , (refl , e₂) with ren-node ρ n₀ (cong (λ p → fstᶠ (sndᶠ (sndᶠ p))) e₂)
...   | ⟨⟩ , (refl , _) = z₀ , (ι0 , sym (cong fstᶠ e₂))
▷-anti ρ (trF {c = c} h) t e with ren-node ρ t (sym e)
... | (d₀ ,ᶠ p₀ ,ᶠ e₀ ,ᶠ ⟨⟩) , (refl , e₂) with ren-node ρ p₀ (cong (λ p → fstᶠ (sndᶠ p)) e₂)
...   | (c₀ ,ᶠ t₀ ,ᶠ ⟨⟩) , (refl , e₃) =
        e₀ , (trF (trans (sym (flat?-ren ρ c₀)) (trans (cong flat? (cong fstᶠ e₃)) h)) ,
              sym (cong (λ p → fstᶠ (sndᶠ (sndᶠ p))) e₂))

------------------------------------------------------------------------
-- ★ The theorems, at the kernel's syntax, with NO per-former congruence
--   clause anywhere: the generic congruence plus the three rules above.
------------------------------------------------------------------------

open Red _▷_
open Forward ▷-ren
open Backward ▷-anti

-- renaming reflects reduction
reflect : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {a b : G.Tm KSig s Δ} → a ⟶ b → (t : G.Tm KSig s Γ) → a ≡ ren ρ t
        → Σ (G.Tm KSig s Γ) (λ u → (t ⟶ u) × (b ≡ ren ρ u))
reflect = ⟶-anti

-- SN is closed under anti-renaming
sn-anti : ∀ {s Γ Δ} (ρ : Var Γ → Var Δ) {t : G.Tm KSig s Γ} → SN (ren ρ t) → SN t
sn-anti ρ {t} h = SN-anti ρ h t refl
