{-# OPTIONS --safe #-}
module tmp.TermProbe3 where
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
data C : Set where hom pi el : C
-- (4) fields as a COMPUTED PRODUCT (no indices): data products, ⊤ at the end
data ⊤ : Set where tt : ⊤
data _×_ (A B : Set) : Set where _,_ : A → B → A × B
infixr 4 _,_
module U4 where
  ar : C → List ℕ
  ar hom = 0 ∷ 0 ∷ 0 ∷ [] ; ar pi = 0 ∷ 1 ∷ [] ; ar el = 0 ∷ []
  data T : Set
  ⟦_⟧ : List ℕ → Set
  data T where node : (c : C) → ⟦ ar c ⟧ → T
  ⟦ [] ⟧     = ⊤
  ⟦ n ∷ ns ⟧ = T × ⟦ ns ⟧
  f : T → T
  f (node hom (node pi (a , b , tt) , r)) = f (node pi (a , b , tt))
  f (node pi (a , b , tt)) = f a
  f t = t
  -- a generic traversal over it terminates too
  mapT : (T → T) → T → T
  mapF : (ns : List ℕ) → (T → T) → ⟦ ns ⟧ → ⟦ ns ⟧
  mapT g (node c xs) = g (node c (mapF (ar c) g xs))
  mapF [] g tt = tt
  mapF (n ∷ ns) g (x , xs) = mapT g x , mapF ns g xs
