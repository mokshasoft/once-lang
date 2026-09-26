{-# OPTIONS --safe #-}
-- SPIKE-LEVITATION: generic syntax over an operator table (binder count per
-- argument), one traversal, and the σ-calculus lemmas — ONCE, for S2 and S3.
module tmp.LevSyn where

open import Agda.Builtin.Nat      using ( Nat; zero; suc; _+_ ) public
open import Agda.Builtin.List     using ( List; []; _∷_ ) public
open import Agda.Builtin.Equality using ( _≡_; refl ) public

private variable
  A B C : Set
  x y z : A

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {x x' : A} {y y' : B} (f : A → B → C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl q = q

sym : x ≡ y → y ≡ x
sym refl = refl

data Fin : Nat → Set where
  fz : {n : Nat} → Fin (suc n)
  fs : {n : Nat} → Fin n → Fin (suc n)

module Syntax (Op : Set) (ar : Op → List Nat) where

  data Tm (n : Nat) : Set
  data Args (n : Nat) : List Nat → Set

  data Tm n where
    var  : Fin n → Tm n
    node : (o : Op) → Args n (ar o) → Tm n

  data Args n where
    []  : Args n []
    _∷_ : {k : Nat} {ks : List Nat} → Tm (k + n) → Args n ks → Args n (k ∷ ks)

  variable
    m n : Nat
    ks  : List Nat

  -- ═══ one traversal ═══════════════════════════════════════════════════════
  ext : (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
  ext ρ fz     = fz
  ext ρ (fs i) = fs (ρ i)

  extN : (k : Nat) → (Fin m → Fin n) → Fin (k + m) → Fin (k + n)
  extN zero    ρ = ρ
  extN (suc k) ρ = ext (extN k ρ)

  ren  : (Fin m → Fin n) → Tm m → Tm n
  renA : (Fin m → Fin n) → Args m ks → Args n ks
  ren ρ (var i)     = var (ρ i)
  ren ρ (node o as) = node o (renA ρ as)
  renA ρ []               = []
  renA ρ (_∷_ {k} t as)   = ren (extN k ρ) t ∷ renA ρ as

  wk : Tm n → Tm (suc n)
  wk = ren fs

  exts : (Fin m → Tm n) → Fin (suc m) → Tm (suc n)
  exts σ fz     = var fz
  exts σ (fs i) = wk (σ i)

  extsN : (k : Nat) → (Fin m → Tm n) → Fin (k + m) → Tm (k + n)
  extsN zero    σ = σ
  extsN (suc k) σ = exts (extsN k σ)

  sub  : (Fin m → Tm n) → Tm m → Tm n
  subA : (Fin m → Tm n) → Args m ks → Args n ks
  sub σ (var i)     = σ i
  sub σ (node o as) = node o (subA σ as)
  subA σ []             = []
  subA σ (_∷_ {k} t as) = sub (extsN k σ) t ∷ subA σ as

  sg : Tm n → Fin (suc n) → Tm n
  sg u fz     = u
  sg u (fs i) = var i

  _[_] : Tm (suc n) → Tm n → Tm n
  b [ u ] = sub (sg u) b

  -- ═══ the σ-calculus lemmas (generic, once) ═══════════════════════════════
  _≗_ : {X : Set} (f g : Fin m → X) → Set
  f ≗ g = ∀ i → f i ≡ g i

  module _ {m n : Nat} where
   extN-cong : (k : Nat) {ρ ρ' : Fin m → Fin n} → ρ ≗ ρ' → extN k ρ ≗ extN k ρ'
   extN-cong zero    h i      = h i
   extN-cong (suc k) h fz     = refl
   extN-cong (suc k) h (fs i) = cong fs (extN-cong k h i)

  ren-cong  : {ρ ρ' : Fin m → Fin n} → ρ ≗ ρ' → (t : Tm m) → ren ρ t ≡ ren ρ' t
  renA-cong : {ρ ρ' : Fin m → Fin n} → ρ ≗ ρ' → (as : Args m ks) → renA ρ as ≡ renA ρ' as
  ren-cong h (var i)     = cong var (h i)
  ren-cong h (node o as) = cong (node o) (renA-cong h as)
  renA-cong h []             = refl
  renA-cong h (_∷_ {k} t as) = cong₂ _∷_ (ren-cong (extN-cong k h) t) (renA-cong h as)

  extN-comp : {l m n : Nat} (k : Nat) (ρ : Fin m → Fin n) (ρ' : Fin l → Fin m) →
              (λ i → extN k ρ (extN k ρ' i)) ≗ extN k (λ i → ρ (ρ' i))
  extN-comp zero    ρ ρ' i      = refl
  extN-comp (suc k) ρ ρ' fz     = refl
  extN-comp (suc k) ρ ρ' (fs i) = cong fs (extN-comp k ρ ρ' i)

  ren-ren  : {l : Nat} (ρ : Fin m → Fin n) (ρ' : Fin l → Fin m) (t : Tm l) →
             ren ρ (ren ρ' t) ≡ ren (λ i → ρ (ρ' i)) t
  renA-ren : {l : Nat} (ρ : Fin m → Fin n) (ρ' : Fin l → Fin m) (as : Args l ks) →
             renA ρ (renA ρ' as) ≡ renA (λ i → ρ (ρ' i)) as
  ren-ren ρ ρ' (var i)     = refl
  ren-ren ρ ρ' (node o as) = cong (node o) (renA-ren ρ ρ' as)
  renA-ren ρ ρ' []             = refl
  renA-ren ρ ρ' (_∷_ {k} t as) =
    cong₂ _∷_ (trans (ren-ren (extN k ρ) (extN k ρ') t) (ren-cong (extN-comp k ρ ρ') t))
              (renA-ren ρ ρ' as)

  extsN-cong : (k : Nat) {σ σ' : Fin m → Tm n} → σ ≗ σ' → extsN k σ ≗ extsN k σ'
  extsN-cong zero    h i      = h i
  extsN-cong (suc k) h fz     = refl
  extsN-cong (suc k) h (fs i) = cong wk (extsN-cong k h i)

  sub-cong  : {σ σ' : Fin m → Tm n} → σ ≗ σ' → (t : Tm m) → sub σ t ≡ sub σ' t
  subA-cong : {σ σ' : Fin m → Tm n} → σ ≗ σ' → (as : Args m ks) → subA σ as ≡ subA σ' as
  sub-cong h (var i)     = h i
  sub-cong h (node o as) = cong (node o) (subA-cong h as)
  subA-cong h []             = refl
  subA-cong h (_∷_ {k} t as) = cong₂ _∷_ (sub-cong (extsN-cong k h) t) (subA-cong h as)

  extsN-extN : {l : Nat} (k : Nat) (σ : Fin m → Tm n) (ρ : Fin l → Fin m) →
               (λ i → extsN k σ (extN k ρ i)) ≗ extsN k (λ i → σ (ρ i))
  extsN-extN zero    σ ρ i      = refl
  extsN-extN (suc k) σ ρ fz     = refl
  extsN-extN (suc k) σ ρ (fs i) = cong wk (extsN-extN k σ ρ i)

  sub-ren  : {l : Nat} (σ : Fin m → Tm n) (ρ : Fin l → Fin m) (t : Tm l) →
             sub σ (ren ρ t) ≡ sub (λ i → σ (ρ i)) t
  subA-ren : {l : Nat} (σ : Fin m → Tm n) (ρ : Fin l → Fin m) (as : Args l ks) →
             subA σ (renA ρ as) ≡ subA (λ i → σ (ρ i)) as
  sub-ren σ ρ (var i)     = refl
  sub-ren σ ρ (node o as) = cong (node o) (subA-ren σ ρ as)
  subA-ren σ ρ []             = refl
  subA-ren σ ρ (_∷_ {k} t as) =
    cong₂ _∷_ (trans (sub-ren (extsN k σ) (extN k ρ) t) (sub-cong (extsN-extN k σ ρ) t))
              (subA-ren σ ρ as)

  -- renaming commutes past one binder
  ren-wk : {l : Nat} (ρ : Fin l → Fin m) (t : Tm l) → ren (ext ρ) (wk t) ≡ wk (ren ρ t)
  ren-wk ρ t = trans (ren-ren (ext ρ) fs t) (sym (ren-ren fs ρ t))

  extN-extsN : {l : Nat} (k : Nat) (ρ : Fin m → Fin n) (σ : Fin l → Tm m) →
               (λ i → ren (extN k ρ) (extsN k σ i)) ≗ extsN k (λ i → ren ρ (σ i))
  extN-extsN zero    ρ σ i      = refl
  extN-extsN (suc k) ρ σ fz     = refl
  extN-extsN (suc k) ρ σ (fs i) =
    trans (ren-wk (extN k ρ) (extsN k σ i)) (cong wk (extN-extsN k ρ σ i))

  ren-sub  : {l : Nat} (ρ : Fin m → Fin n) (σ : Fin l → Tm m) (t : Tm l) →
             ren ρ (sub σ t) ≡ sub (λ i → ren ρ (σ i)) t
  renA-sub : {l : Nat} (ρ : Fin m → Fin n) (σ : Fin l → Tm m) (as : Args l ks) →
             renA ρ (subA σ as) ≡ subA (λ i → ren ρ (σ i)) as
  ren-sub ρ σ (var i)     = refl
  ren-sub ρ σ (node o as) = cong (node o) (renA-sub ρ σ as)
  renA-sub ρ σ []             = refl
  renA-sub ρ σ (_∷_ {k} t as) =
    cong₂ _∷_ (trans (ren-sub (extN k ρ) (extsN k σ) t) (sub-cong (extN-extsN k ρ σ) t))
              (renA-sub ρ σ as)

  -- ★ LEMMA W — substitution commutes past ONE binder (the only lemma the
  --   description operators' rules need)
  sub-wk : (σ : Fin m → Tm n) (t : Tm m) → sub (exts σ) (wk t) ≡ wk (sub σ t)
  sub-wk σ t = trans (sub-ren (exts σ) fs t) (sym (ren-sub fs σ t))

  extsN-sub : {l : Nat} (k : Nat) (σ : Fin m → Tm n) (τ : Fin l → Tm m) →
              (λ i → sub (extsN k σ) (extsN k τ i)) ≗ extsN k (λ i → sub σ (τ i))
  extsN-sub zero    σ τ i      = refl
  extsN-sub (suc k) σ τ fz     = refl
  extsN-sub (suc k) σ τ (fs i) =
    trans (sub-wk (extsN k σ) (extsN k τ i)) (cong wk (extsN-sub k σ τ i))

  sub-sub  : {l : Nat} (σ : Fin m → Tm n) (τ : Fin l → Tm m) (t : Tm l) →
             sub σ (sub τ t) ≡ sub (λ i → sub σ (τ i)) t
  subA-sub : {l : Nat} (σ : Fin m → Tm n) (τ : Fin l → Tm m) (as : Args l ks) →
             subA σ (subA τ as) ≡ subA (λ i → sub σ (τ i)) as
  sub-sub σ τ (var i)     = refl
  sub-sub σ τ (node o as) = cong (node o) (subA-sub σ τ as)
  subA-sub σ τ []             = refl
  subA-sub σ τ (_∷_ {k} t as) =
    cong₂ _∷_ (trans (sub-sub (extsN k σ) (extsN k τ) t) (sub-cong (extsN-sub k σ τ) t))
              (subA-sub σ τ as)

  extsN-var : (k : Nat) → extsN {m} k var ≗ var
  extsN-var zero    i      = refl
  extsN-var (suc k) fz     = refl
  extsN-var (suc k) (fs i) = cong wk (extsN-var k i)

  sub-var  : (t : Tm m) → sub var t ≡ t
  subA-var : (as : Args m ks) → subA var as ≡ as
  sub-var (var i)     = refl
  sub-var (node o as) = cong (node o) (subA-var as)
  subA-var []             = refl
  subA-var (_∷_ {k} t as) = cong₂ _∷_ (trans (sub-cong (extsN-var k) t) (sub-var t)) (subA-var as)

  -- ★ LEMMA B — β commutes with substitution
  sub-β : (σ : Fin m → Tm n) (b : Tm (suc m)) (u : Tm m) →
          sub σ (b [ u ]) ≡ (sub (exts σ) b) [ sub σ u ]
  sub-β σ b u =
    trans (sub-sub σ (sg u) b)
   (trans (sub-cong pt b)
          (sym (sub-sub (sg (sub σ u)) (exts σ) b)))
    where
    pt : (λ i → sub σ (sg u i)) ≗ (λ i → sub (sg (sub σ u)) (exts σ i))
    pt fz     = refl
    pt (fs i) = sym (trans (sub-ren (sg (sub σ u)) fs (σ i)) (sub-var (σ i)))


  -- renaming IS substitution by variables
  extsN-var-ren : {m n : Nat} (k : Nat) (ρ : Fin m → Fin n) →
                  extsN k (λ x → var (ρ x)) ≗ (λ x → var (extN k ρ x))
  extsN-var-ren zero    ρ x      = refl
  extsN-var-ren (suc k) ρ fz     = refl
  extsN-var-ren (suc k) ρ (fs x) = cong wk (extsN-var-ren k ρ x)

  ren-as-sub  : {m n : Nat} (ρ : Fin m → Fin n) (t : Tm m) → sub (λ x → var (ρ x)) t ≡ ren ρ t
  renA-as-sub : {m n : Nat} {ks : List Nat} (ρ : Fin m → Fin n) (as : Args m ks) →
                subA (λ x → var (ρ x)) as ≡ renA ρ as
  ren-as-sub ρ (var x)     = refl
  ren-as-sub ρ (node o as) = cong (node o) (renA-as-sub ρ as)
  renA-as-sub ρ []             = refl
  renA-as-sub ρ (_∷_ {k} t as) =
    cong₂ _∷_ (trans (sub-cong (extsN-var-ren k ρ) t) (ren-as-sub (extN k ρ) t)) (renA-as-sub ρ as)

  -- ★ the two normalisers every weakening/cancellation reduces to
  --   (the pointwise premise is `λ _ → refl` for concrete σ, ρ)
  subRen : {l m n : Nat} (σ : Fin m → Tm n) (ρ : Fin l → Fin m) (ρ' : Fin l → Fin n) →
           (∀ x → σ (ρ x) ≡ var (ρ' x)) → (t : Tm l) → sub σ (ren ρ t) ≡ ren ρ' t
  subRen σ ρ ρ' h t = trans (sub-ren σ ρ t) (trans (sub-cong h t) (ren-as-sub ρ' t))

  subRenA : {l m n : Nat} {ks : List Nat} (σ : Fin m → Tm n) (ρ : Fin l → Fin m) (ρ' : Fin l → Fin n) →
            (∀ x → σ (ρ x) ≡ var (ρ' x)) → (as : Args l ks) → subA σ (renA ρ as) ≡ renA ρ' as
  subRenA σ ρ ρ' h as = trans (subA-ren σ ρ as) (trans (subA-cong h as) (renA-as-sub ρ' as))

  renRen : {l m n : Nat} (ρ : Fin m → Fin n) (ρ' : Fin l → Fin m) (ρ'' : Fin l → Fin n) →
           (∀ x → ρ (ρ' x) ≡ ρ'' x) → (t : Tm l) → ren ρ (ren ρ' t) ≡ ren ρ'' t
  renRen ρ ρ' ρ'' h t = trans (ren-ren ρ ρ' t) (ren-cong h t)

  renRenA : {l m n : Nat} {ks : List Nat} (ρ : Fin m → Fin n) (ρ' : Fin l → Fin m) (ρ'' : Fin l → Fin n) →
            (∀ x → ρ (ρ' x) ≡ ρ'' x) → (as : Args l ks) → renA ρ (renA ρ' as) ≡ renA ρ'' as
  renRenA ρ ρ' ρ'' h as = trans (renA-ren ρ ρ' as) (renA-cong h as)
