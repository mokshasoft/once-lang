{-# OPTIONS --safe --termination-depth=3 #-}
module tmp.TermProbe6 where
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Scope
data ⊤ : Set where tt : ⊤
data _×_ (A B : Set) : Set where _,_ : A → B → A × B
infixr 4 _,_
data S : Set where ty tm : S
data C : S → Set where hom pi : C ty ; lam : C tm
data F : Set where fld : S → ℕ → F
_⋯_ : Cx → ℕ → Cx
Γ ⋯ zero = Γ
Γ ⋯ suc k = (Γ ⋯ k) ∙
ar : ∀ {s} → C s → List F
ar hom = fld ty 0 ∷ fld tm 0 ∷ fld tm 0 ∷ [] ; ar pi = fld ty 0 ∷ fld ty 1 ∷ [] ; ar lam = fld tm 1 ∷ []
data Tm : S → Cx → Set
⟦_⟧ : List F → Cx → Set
data Tm where
  var  : ∀ {Γ} → Var Γ → Tm tm Γ
  node : ∀ {s Γ} (c : C s) → ⟦ ar c ⟧ Γ → Tm s Γ
⟦ [] ⟧ Γ                 = ⊤


⟦ fld s k ∷ fs ⟧ Γ = Tm s (Γ ⋯ k) × ⟦ fs ⟧ Γ
pattern Hom {Γ} A t u = node {Γ = Γ} hom (A , t , u , tt)
pattern Π {Γ} A B = node {Γ = Γ} pi (A , B , tt)
private variable Γ : Cx
f6 : Tm ty Γ → Tm ty Γ
f6 (Hom (Π A B) t u) = Hom (f6 (Π A B)) t u
f6 (Π A B) = Π (f6 A) (f6 B)
f6 A = A
