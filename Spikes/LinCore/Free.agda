-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Free — plan 0.146 A14½: THE FREE MONOID, as traces use it.
--
-- A trace is a word in the free monoid on events (`List`, `++`, `[]`). Every
-- consumer of traces is given on ONE event and lifted by the free monoid's
-- universal property:
--
--   * a homomorphism into another free monoid: `concatMap f` (what the world
--     sees, the trace without temporaries, one block's lifetime);
--   * an action on a state: `foldl g` (the heap, the ledger of temporaries);
--   * where a partial action is defined: `Along pre g` (each event's
--     precondition holds at the state it meets — `OK`, `TOK`).
--
-- Their laws are proved here once: on concatenations, on prefixes, and on a
-- WEAVE that adds letters the consumer does not see.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_; concatMap; foldl)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)

module LinCore.Free where

private
  variable
    X Y Z A : Set

------------------------------------------------------------------------
-- PREFIXES
------------------------------------------------------------------------

-- one list is a prefix of another
infix 4 _≼_
data _≼_ {X : Set} : List X → List X → Set where
  []≼ : ∀ {t} → [] ≼ t
  ∷≼  : ∀ {x t t′} → t ≼ t′ → (x ∷ t) ≼ (x ∷ t′)

++-≼ : ∀ (l : List X) {a b} → a ≼ b → (l ++ a) ≼ (l ++ b)
++-≼ []      q = q
++-≼ (x ∷ l) q = ∷≼ (++-≼ l q)

------------------------------------------------------------------------
-- WEAVES: letters from `Y`, injected, put between the letters of a word
------------------------------------------------------------------------

data Weave {X Y : Set} (inj : Y → X) : List X → List Y → List X → Set where
  w-[]  : Weave inj [] [] []
  w-run : ∀ {x t ts t′} → Weave inj t ts t′ → Weave inj (x ∷ t) ts (x ∷ t′)
  w-tmp : ∀ {y t ts t′} → Weave inj t ts t′ → Weave inj t (y ∷ ts) (inj y ∷ t′)

------------------------------------------------------------------------
-- HOMOMORPHISMS INTO A FREE MONOID: `concatMap f`
------------------------------------------------------------------------

cmap-++ : ∀ (f : X → List Y) xs ys → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
cmap-++ f []       ys = refl
cmap-++ f (x ∷ xs) ys = trans (cong (f x ++_) (cmap-++ f xs ys)) (sym (++-assoc (f x) (concatMap f xs) (concatMap f ys)))

cmap-≼ : ∀ (f : X → List Y) {xs ys} → xs ≼ ys → concatMap f xs ≼ concatMap f ys
cmap-≼ f []≼          = []≼
cmap-≼ f (∷≼ {x} q)   = ++-≼ (f x) (cmap-≼ f q)

-- letters it sends to the unit are invisible to it
cmap-weave : ∀ {inj : Y → X} (f : X → List Z) → (∀ y → f (inj y) ≡ [])
           → ∀ {t ts t′} → Weave inj t ts t′ → concatMap f t′ ≡ concatMap f t
cmap-weave f e w-[]               = refl
cmap-weave f e (w-run {x = x} w)  = cong (f x ++_) (cmap-weave f e w)
cmap-weave f e (w-tmp {y = y} {t′ = t′} w) = trans (cong (_++ concatMap f t′) (e y)) (cmap-weave f e w)

-- a word of such letters is sent to the unit; a word of letters it keeps, to itself
cmap-nil : ∀ (f : X → List Y) {xs} → All (λ x → f x ≡ []) xs → concatMap f xs ≡ []
cmap-nil f []       = refl
cmap-nil f {_ ∷ xs} (e ∷ es) = trans (cong (_++ concatMap f xs) e) (cmap-nil f es)

cmap-id : ∀ (f : X → List X) {xs} → All (λ x → f x ≡ x ∷ []) xs → concatMap f xs ≡ xs
cmap-id f {x ∷ xs} (e ∷ es) = trans (cong (_++ concatMap f xs) e) (cong (x ∷_) (cmap-id f es))
cmap-id f []                = refl

------------------------------------------------------------------------
-- ACTIONS: `foldl g` (the law on `++` is stdlib's `foldl-++`)
------------------------------------------------------------------------

foldl-weave : ∀ {inj : Y → X} (g : A → X → A) → (∀ a y → g a (inj y) ≡ a)
            → ∀ {t ts t′} → Weave inj t ts t′ → ∀ a → foldl g a t′ ≡ foldl g a t
foldl-weave g e w-[]              a = refl
foldl-weave g e (w-run {x = x} w) a = foldl-weave g e w (g a x)
foldl-weave g e (w-tmp {y = y} {t′ = t′} w) a = trans (cong (λ b → foldl g b t′) (e a y)) (foldl-weave g e w a)

------------------------------------------------------------------------
-- WHERE A PARTIAL ACTION IS DEFINED: each letter's precondition holds at the
-- state the action has reached
------------------------------------------------------------------------

Along : (X → A → Set) → (A → X → A) → List X → A → Set
Along pre g []       a = ⊤
Along pre g (x ∷ xs) a = pre x a × Along pre g xs (g a x)

module _ {pre : X → A → Set} {g : A → X → A} where

  Along-++ : ∀ xs ys a → Along pre g xs a → Along pre g ys (foldl g a xs) → Along pre g (xs ++ ys) a
  Along-++ []       ys a _        q = q
  Along-++ (x ∷ xs) ys a (p , ps) q = (p , Along-++ xs ys (g a x) ps q)

  Along-≼ : ∀ {xs ys a} → xs ≼ ys → Along pre g ys a → Along pre g xs a
  Along-≼ []≼      _        = tt
  Along-≼ (∷≼ q)   (p , ps) = (p , Along-≼ q ps)

  -- letters that act as the identity and ask nothing may be woven in
  Along-weave : ∀ {inj : Y → X} → (∀ a y → g a (inj y) ≡ a) → (∀ a y → pre (inj y) a)
              → ∀ {t ts t′} → Weave inj t ts t′ → ∀ a → Along pre g t a → Along pre g t′ a
  Along-weave e p w-[]       a _         = tt
  Along-weave e p (w-run w)  a (q , qs)  = (q , Along-weave e p w _ qs)
  Along-weave e p (w-tmp {y = y} w) a qs =
    (p a y , subst (Along pre g _) (sym (e a y)) (Along-weave e p w a qs))

  -- a relation the action and its preconditions respect is respected by
  -- the whole partial action (`TOK-ext`: equal ledgers; `TOK-mono`: larger)
  Along-pres : (R : A → A → Set) → (∀ x {a b} → R a b → pre x a → pre x b)
             → (∀ x {a b} → R a b → R (g a x) (g b x))
             → ∀ xs {a b} → R a b → Along pre g xs a → Along pre g xs b
  Along-pres R p r []       ab _        = tt
  Along-pres R p r (x ∷ xs) ab (q , qs) = (p x ab q , Along-pres R p r xs (r x ab) qs)

  -- letters that act as the identity and ask nothing
  Along-all : ∀ {P : X → Set} → (∀ {x} → P x → ∀ a → pre x a) → (∀ {x} → P x → ∀ a → g a x ≡ a)
            → ∀ {xs} → All P xs → ∀ a → Along pre g xs a
  Along-all p e []        a = tt
  Along-all p e (px ∷ ps) a = (p px a , subst (Along pre g _) (sym (e px a)) (Along-all p e ps a))

foldl-pres : ∀ (R : A → A → Set) (g : A → X → A) → (∀ x {a b} → R a b → R (g a x) (g b x))
           → ∀ xs {a b} → R a b → R (foldl g a xs) (foldl g b xs)
foldl-pres R g r []       ab = ab
foldl-pres R g r (x ∷ xs) ab = foldl-pres R g r xs (r x ab)

foldl-all : ∀ {P : X → Set} (g : A → X → A) → (∀ {x} → P x → ∀ a → g a x ≡ a)
          → ∀ {xs} → All P xs → ∀ a → foldl g a xs ≡ a
foldl-all g e []        a = refl
foldl-all g e {_ ∷ xs} (px ∷ ps) a = trans (cong (λ b → foldl g b xs) (e px a)) (foldl-all g e ps a)

-- a homomorphism whose every letter's image satisfies `P`
cmap-All : ∀ {P : Y → Set} (f : X → List Y) → (∀ x → All P (f x)) → ∀ xs → All P (concatMap f xs)
cmap-All f p []       = []
cmap-All f p (x ∷ xs) = ++⁺ (p x) (cmap-All f p xs)
