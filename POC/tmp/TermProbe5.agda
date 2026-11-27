{-# OPTIONS --safe #-}
module tmp.TermProbe5 where
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Scope
data ⊤ : Set where tt : ⊤
data _×_ (A B : Set) : Set where _,_ : A → B → A × B
infixr 4 _,_
data S : Set where ty tm : S
data C : S → Set where hom pi : C ty ; lam : C tm
data F : Set where fld : S → ℕ → F
ar : ∀ {s} → C s → List F
ar hom = fld ty 0 ∷ fld tm 0 ∷ fld tm 0 ∷ [] ; ar pi = fld ty 0 ∷ fld ty 1 ∷ [] ; ar lam = fld tm 1 ∷ []
private variable Γ : Cx
-- (5b) indexed, but NO binder shift in the field types
module B where
  data Tm : S → Cx → Set
  ⟦_⟧ : List F → Cx → Set
  data Tm where
    node : ∀ {s Γ} (c : C s) → ⟦ ar c ⟧ Γ → Tm s Γ
  ⟦ [] ⟧ Γ          = ⊤
  ⟦ fld s k ∷ fs ⟧ Γ = Tm s Γ × ⟦ fs ⟧ Γ
  f6 : Tm ty Γ → Tm ty Γ
  f6 (node hom (node pi (A , B , tt) , t , u , tt)) = node hom (f6 (node pi (A , B , tt)) , t , u , tt)
  f6 (node pi (A , B , tt)) = node pi (f6 A , f6 B , tt)
  f6 A = A
-- (5c) binders as a constructor-headed WRAPPER: no function in any index
module W where
  data Tm : S → Cx → Set
  data Bnd (s : S) : ℕ → Cx → Set
  ⟦_⟧ : List F → Cx → Set
  data Tm where
    node : ∀ {s Γ} (c : C s) → ⟦ ar c ⟧ Γ → Tm s Γ
  data Bnd s where
    b0 : ∀ {Γ} → Tm s Γ → Bnd s zero Γ
    bS : ∀ {k Γ} → Bnd s k (Γ ∙) → Bnd s (suc k) Γ
  ⟦ [] ⟧ Γ          = ⊤
  ⟦ fld s k ∷ fs ⟧ Γ = Bnd s k Γ × ⟦ fs ⟧ Γ
  pattern Π A B = node pi (b0 A , bS (b0 B) , tt)
  pattern Hom A t u = node hom (b0 A , b0 t , b0 u , tt)
  f6 : Tm ty Γ → Tm ty Γ
  f6 (Hom (Π A B) t u) = Hom (f6 (Π A B)) t u
  f6 (Π A B) = Π (f6 A) (f6 B)
  f6 A = A
