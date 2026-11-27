{-# OPTIONS --safe #-}
module tmp.TermProbe8 where
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.Equality using ( _≡_; refl )
open import DirectedHoTT.Spec.Scope
-- (8) RECORD products with eta (U7 otherwise)
record ⟨⟩ᶠ : Set where
  constructor ⟨⟩
infixr 4 _,_
record _⊗_ (A B : Set) : Set where
  constructor _,_
  field fst : A ; snd : B
data S : Set where ty tm : S
data C : S → Set where hom pi : C ty ; lam ref nat : C tm
data F : Set where fld : S → ℕ → F ; fnat : F
_⋯_ : Cx → ℕ → Cx
Γ ⋯ zero = Γ
Γ ⋯ suc k = (Γ ⋯ k) ∙
ar : ∀ {s} → C s → List F
ar hom = fld ty 0 ∷ fld tm 0 ∷ fld tm 0 ∷ [] ; ar pi = fld ty 0 ∷ fld ty 1 ∷ []
ar lam = fld tm 1 ∷ [] ; ar ref = fnat ∷ [] ; ar nat = []
data Tm : S → Cx → Set
⟦_⟧ : List F → Cx → Set
data Tm where
  var  : ∀ {Γ} → Var Γ → Tm tm Γ
  node : ∀ {s Γ} (c : C s) → ⟦ ar c ⟧ Γ → Tm s Γ
⟦ [] ⟧ Γ                 = ⟨⟩ᶠ
⟦ fld s zero ∷ fs ⟧ Γ    = Tm s Γ ⊗ ⟦ fs ⟧ Γ
⟦ fld s (suc k) ∷ fs ⟧ Γ = Tm s ((Γ ⋯ k) ∙) ⊗ ⟦ fs ⟧ Γ
⟦ fnat ∷ fs ⟧ Γ          = ℕ ⊗ ⟦ fs ⟧ Γ
pattern Hom {Γ} A t u = node {Γ = Γ} hom (A , t , u , ⟨⟩)
pattern Π {Γ} A B = node {Γ = Γ} pi (A , B , ⟨⟩)
pattern Lam {Γ} t = node {Γ = Γ} lam (t , ⟨⟩)
pattern Ref {Γ} d = node {Γ = Γ} ref (d , ⟨⟩)
pattern Natc {Γ} = node {Γ = Γ} nat ⟨⟩
private variable Γ : Cx
-- termination: a rebuilt subterm, then its fields
f6 : Tm ty Γ → Tm ty Γ
f6 (Hom (Π A B) t u) = Hom (f6 (Π A B)) t u
f6 (Π A B) = Π (f6 A) (f6 B)
f6 A = A
-- coverage: cases refuted by COMPUTATION, with no clause for them
ok? : Tm tm Γ → Bool
ok? (Ref d) = false
ok? Natc    = false
ok? _       = true
g : (t : Tm tm Γ) → ok? t ≡ true → Bool
g (var x) h = true
g (Lam t) h = true
