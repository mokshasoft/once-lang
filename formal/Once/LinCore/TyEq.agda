------------------------------------------------------------------------
-- Once.LinCore.TyEq — a Boolean equality of the core's types, sound and complete.
--
-- ★ D487: the universe's type lists are deduplicated by it (`Keys.close`), so a type has ONE
-- copy block and ONE free block, and a cell type one pair of trampolines, however many times
-- the program mentions it; a type's place is FOUND by it (`Keys.find`: a search of the shared
-- list, its existence a lazy witness, never computed).
--
-- A type is encoded as a tree (`enc`: a tag and four children, unused ones a leaf), with a
-- total decoder (`dec (enc T) ≡ T`, one clause per constructor), so the encoding is injective
-- by `cong dec`; equality of trees compares tags and children. No clause per pair of
-- constructors.
--
-- `--safe --guardedness`, no postulates, no holes.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.TyEq (fmt : TargetNum) where

open import Data.Bool using (Bool; true; false; _∧_; T)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Once.LinCore.Flat using (Base; int; float)
open import Once.LinCore.Core fmt

-- trees: a leaf, or a tag and four children
data Tr : Set where
  lf : Tr
  nd : ℕ → Tr → Tr → Tr → Tr → Tr

eqTr : Tr → Tr → Bool
eqTr lf               lf                   = true
eqTr (nd n a b c d)   (nd m a′ b′ c′ d′)   = (n ≡ᵇ m) ∧ (eqTr a a′ ∧ (eqTr b b′ ∧ (eqTr c c′ ∧ eqTr d d′)))
eqTr lf               (nd _ _ _ _ _)       = false
eqTr (nd _ _ _ _ _)   lf                   = false

private
  ∧-l : ∀ a {b} → (a ∧ b) ≡ true → a ≡ true
  ∧-l true  _ = refl
  ∧-l false ()

  ∧-r : ∀ a {b} → (a ∧ b) ≡ true → b ≡ true
  ∧-r true  e = e
  ∧-r false ()

  ∧-i : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
  ∧-i refl refl = refl

  toT : ∀ b → b ≡ true → T b
  toT true _ = tt

  ≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

eqTr-ok : ∀ t u → eqTr t u ≡ true → t ≡ u
eqTr-ok lf lf _ = refl
eqTr-ok (nd n a b c d) (nd m a′ b′ c′ d′) e =
  let e₁ = ∧-r (n ≡ᵇ m) e ; e₂ = ∧-r (eqTr a a′) e₁ ; e₃ = ∧-r (eqTr b b′) e₂
  in trans (cong₂ (λ n′ a″ → nd n′ a″ b c d) (≡ᵇ⇒≡ n m (toT (n ≡ᵇ m) (∧-l (n ≡ᵇ m) e))) (eqTr-ok a a′ (∧-l (eqTr a a′) e₁)))
     (trans (cong₂ (λ b″ c″ → nd m a′ b″ c″ d) (eqTr-ok b b′ (∧-l (eqTr b b′) e₂)) (eqTr-ok c c′ (∧-l (eqTr c c′) e₃)))
            (cong (nd m a′ b′ c′) (eqTr-ok d d′ (∧-r (eqTr c c′) e₃))))
eqTr-ok lf (nd _ _ _ _ _) ()
eqTr-ok (nd _ _ _ _ _) lf ()

eqTr-refl : ∀ t → eqTr t t ≡ true
eqTr-refl lf             = refl
eqTr-refl (nd n a b c d) = ∧-i (≡ᵇ-refl n) (∧-i (eqTr-refl a) (∧-i (eqTr-refl b) (∧-i (eqTr-refl c) (eqTr-refl d))))

-- a tag with no children
tag : ℕ → Tr
tag n = nd n lf lf lf lf

tagOf : Tr → ℕ
tagOf lf               = 0
tagOf (nd n _ _ _ _)   = n

-- the encodings
encB : Base → Tr
encB int   = tag 0
encB float = tag 1

pickB : ℕ → Base
pickB zero          = int
pickB (suc zero)    = float
pickB (suc (suc _)) = int

decB : Tr → Base
decB t = pickB (tagOf t)

encK : Kd → Tr
encK once = tag 0
encK many = tag 1

pickK : ℕ → Kd
pickK zero          = once
pickK (suc zero)    = many
pickK (suc (suc _)) = once

decK : Tr → Kd
decK t = pickK (tagOf t)

encG : Gr → Tr
encG act = tag 0
encG eff = tag 1

pickG : ℕ → Gr
pickG zero          = act
pickG (suc zero)    = eff
pickG (suc (suc _)) = act

decG : Tr → Gr
decG t = pickG (tagOf t)

encF : LF → Tr
encF Idf      = tag 0
encF Kone     = tag 1
encF Kzero    = tag 2
encF (Kb b)   = nd 3 (encB b) lf lf lf
encF (Kμ F)   = nd 4 (encF F) lf lf lf
encF (F ⊕f G) = nd 5 (encF F) (encF G) lf lf
encF (F ⊗f G) = nd 6 (encF F) (encF G) lf lf

-- a functor from a tag and its children's decodings
pickF : ℕ → LF → LF → Base → LF
pickF zero                                        F G b = Idf
pickF (suc zero)                                  F G b = Kone
pickF (suc (suc zero))                            F G b = Kzero
pickF (suc (suc (suc zero)))                      F G b = Kb b
pickF (suc (suc (suc (suc zero))))                F G b = Kμ F
pickF (suc (suc (suc (suc (suc zero)))))          F G b = F ⊕f G
pickF (suc (suc (suc (suc (suc (suc zero))))))    F G b = F ⊗f G
pickF (suc (suc (suc (suc (suc (suc (suc _))))))) F G b = Idf

decF : Tr → LF
decF lf               = Idf
decF (nd n a b _ _)   = pickF n (decF a) (decF b) (decB a)

enc : LTy → Tr
enc One          = tag 0
enc Zero         = tag 1
enc (A ⊗t B)     = nd 2 (enc A) (enc B) lf lf
enc (A ⊕t B)     = nd 3 (enc A) (enc B) lf lf
enc (Ct l X)     = nd 4 (tag l) (enc X) lf lf
enc (Fn k g A B) = nd 5 (encK k) (encG g) (enc A) (enc B)
enc (Nu F)       = nd 6 (encF F) lf lf lf
enc (μt F)       = nd 7 (encF F) lf lf lf
enc (Bt b)       = nd 8 (encB b) lf lf lf

-- a type from a tag and its children's decodings (each child read every way a constructor needs)
record Kids : Set where
  constructor kids
  field
    t₁ t₂ t₃ t₄ : LTy
    f₁ : LF
    b₁ : Base
    k₁ : Kd
    g₂ : Gr
    l₁ : ℕ

pickT : ℕ → Kids → LTy
pickT zero                                                    κ = One
pickT (suc zero)                                              κ = Zero
pickT (suc (suc zero))                                        κ = Kids.t₁ κ ⊗t Kids.t₂ κ
pickT (suc (suc (suc zero)))                                  κ = Kids.t₁ κ ⊕t Kids.t₂ κ
pickT (suc (suc (suc (suc zero))))                            κ = Ct (Kids.l₁ κ) (Kids.t₂ κ)
pickT (suc (suc (suc (suc (suc zero)))))                      κ = Fn (Kids.k₁ κ) (Kids.g₂ κ) (Kids.t₃ κ) (Kids.t₄ κ)
pickT (suc (suc (suc (suc (suc (suc zero))))))                κ = Nu (Kids.f₁ κ)
pickT (suc (suc (suc (suc (suc (suc (suc zero)))))))          κ = μt (Kids.f₁ κ)
pickT (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))    κ = Bt (Kids.b₁ κ)
pickT (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))) κ = One

dec : Tr → LTy
dec lf               = One
dec (nd n a b c d)   = pickT n (kids (dec a) (dec b) (dec c) (dec d) (decF a) (decB a) (decK a) (decG b) (tagOf a))

decB-enc : ∀ b → decB (encB b) ≡ b
decB-enc int   = refl
decB-enc float = refl

decK-enc : ∀ k → decK (encK k) ≡ k
decK-enc once = refl
decK-enc many = refl

decG-enc : ∀ g → decG (encG g) ≡ g
decG-enc act = refl
decG-enc eff = refl

decF-enc : ∀ F → decF (encF F) ≡ F
decF-enc Idf      = refl
decF-enc Kone     = refl
decF-enc Kzero    = refl
decF-enc (Kb b)   = cong Kb (decB-enc b)
decF-enc (Kμ F)   = cong Kμ (decF-enc F)
decF-enc (F ⊕f G) = cong₂ _⊕f_ (decF-enc F) (decF-enc G)
decF-enc (F ⊗f G) = cong₂ _⊗f_ (decF-enc F) (decF-enc G)

dec-enc : ∀ T → dec (enc T) ≡ T
dec-enc One          = refl
dec-enc Zero         = refl
dec-enc (A ⊗t B)     = cong₂ _⊗t_ (dec-enc A) (dec-enc B)
dec-enc (A ⊕t B)     = cong₂ _⊕t_ (dec-enc A) (dec-enc B)
dec-enc (Ct l X)     = cong (Ct l) (dec-enc X)
dec-enc (Fn k g A B) = trans (cong₂ (λ k′ g′ → Fn k′ g′ (dec (enc A)) (dec (enc B))) (decK-enc k) (decG-enc g))
                             (cong₂ (Fn k g) (dec-enc A) (dec-enc B))
dec-enc (Nu F)       = cong Nu (decF-enc F)
dec-enc (μt F)       = cong μt (decF-enc F)
dec-enc (Bt b)       = cong Bt (decB-enc b)

-- ★ the equality: sound and complete
eqT : LTy → LTy → Bool
eqT A B = eqTr (enc A) (enc B)

eqT-ok : ∀ A B → eqT A B ≡ true → A ≡ B
eqT-ok A B e = trans (sym (dec-enc A)) (trans (cong dec (eqTr-ok (enc A) (enc B) e)) (dec-enc B))

eqT-refl : ∀ A → eqT A A ≡ true
eqT-refl A = eqTr-refl (enc A)
