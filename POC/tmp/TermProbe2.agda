{-# OPTIONS --safe #-}
module tmp.TermProbe2 where
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
data C : Set where hom pi el : C
-- (1) untyped nodes, untyped argument lists
module U1 where
  data T : Set
  data L : Set
  data T where node : C → L → T
  data L where nil : L ; cons : T → L → L
  f : T → T
  f (node hom (cons (node pi (cons a (cons b nil))) r)) = f (node pi (cons a (cons b nil)))
  f (node pi (cons a (cons b nil))) = f a
  f t = t
-- (2) argument list indexed by a plain list of naturals
module U2 where
  data T : Set
  data L : List ℕ → Set
  data T where node : C → (ns : List ℕ) → L ns → T
  data L where nil : L [] ; cons : ∀ {n ns} → T → L ns → L (n ∷ ns)
  f : T → T
  f (node hom _ (cons (node pi ns (cons a (cons b nil))) r)) = f (node pi ns (cons a (cons b nil)))
  f (node pi _ (cons a (cons b nil))) = f a
  f t = t
-- (3) argument list indexed by a list COMPUTED from the constructor
module U3 where
  ar : C → List ℕ
  ar hom = 0 ∷ 0 ∷ 0 ∷ [] ; ar pi = 0 ∷ 1 ∷ [] ; ar el = 0 ∷ []
  data T : Set
  data L : List ℕ → Set
  data T where node : (c : C) → L (ar c) → T
  data L where nil : L [] ; cons : ∀ {n ns} → T → L ns → L (n ∷ ns)
  f : T → T
  f (node hom (cons (node pi (cons a (cons b nil))) r)) = f (node pi (cons a (cons b nil)))
  f (node pi (cons a (cons b nil))) = f a
  f t = t
