-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceMonadLaws — the lemmas about `Once.Denotation.TraceMonad`, moved out so that module
-- stays definitions only (plan 0.113 A1/B4; D140: the Spec closure is proof-free).
------------------------------------------------------------------------

module Once.Denotation.TraceMonadLaws where

open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (0∸n≡0)
open import Data.List using (List; []; _∷_; _++_; length; take; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Once.Postulates using (extensionality)
open import Once.Res using (Res; stopped; returns; is-stopped; Res-rel; rel-stopped; rel-returns)
open import Once.Type using (Type; isUnit?) renaming (Unit to UnitT)
import Once.Type as Ty
open import Once.Functor.Translate using (IsBaseType)
open import Once.CanonicalName using (CanonicalName; showCanonical; gen)
open import Relation.Nullary using (Dec; yes; no)
import Data.List.Membership.DecPropositional as DecMem
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Functor.Translate using (base-Unit)
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Denotation.Trace using (SigOpEvent; mk-event)
open import Once.SigOp.Info using (FFIAnswers)
open import Once.Spec.Contract using (Key; key; kdom; kcod; _∈K?_; ISig; valueKeys; answerKeys; Impl; answerI; pureI)
open import Once.Denotation.TraceMonad
open CallOp
open HaltOp
open Interp

>>=T-identityˡ : ∀ {X Y : Set} (x : X) (f : X → T Y) → (returnT x >>=T f) ≡ f x

>>=T-identityˡ x f = refl

>>=T-identityʳ : ∀ {X : Set} (m : T X) → (m >>=T returnT) ≡ m

>>=T-identityʳ (ret x)      = refl

>>=T-identityʳ (call o a k) = cong (call o a) (extensionality λ b → >>=T-identityʳ (k b))

>>=T-identityʳ (halt o a)   = refl

>>=T-assoc : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z)
           → ((m >>=T f) >>=T g) ≡ (m >>=T λ x → f x >>=T g)

>>=T-assoc (ret x)      f g = refl

>>=T-assoc (call o a k) f g = cong (call o a) (extensionality λ b → >>=T-assoc (k b) f g)

>>=T-assoc (halt o a)   f g = refl

>>=T-cong : ∀ {X Y : Set} (m : T X) {f g : X → T Y} → (∀ x → f x ≡ g x) → (m >>=T f) ≡ (m >>=T g)

>>=T-cong m h = cong (m >>=T_) (extensionality h)

fmapT-id : ∀ {X} (m : T X) → fmapT (λ x → x) m ≡ m

fmapT-id = >>=T-identityʳ

fmapT-∘ : ∀ {X Y Z} (g : Y → Z) (f : X → Y) (m : T X) → fmapT g (fmapT f m) ≡ fmapT (λ x → g (f x)) m

fmapT-∘ g f m = >>=T-assoc m _ _

fmapT-cong : ∀ {X Y} {f g : X → Y} → (∀ x → f x ≡ g x) → (m : T X) → fmapT f m ≡ fmapT g m

fmapT-cong h m = >>=T-cong m λ x → cong ret (h x)

fmapT->>=T : ∀ {X Y Z : Set} (g : X → Y) (m : T X) (f : Y → T Z) → (fmapT g m >>=T f) ≡ (m >>=T λ x → f (g x))

fmapT->>=T g m f = >>=T-assoc m _ f

>>=T-fmapT : ∀ {X Y Z : Set} (g : Y → Z) (m : T X) (f : X → T Y) → fmapT g (m >>=T f) ≡ (m >>=T λ x → fmapT g (f x))

>>=T-fmapT g m f = >>=T-assoc m f _

length-take-≤ : ∀ k (xs : List SigOpEvent) → length (take k xs) ≤ k

length-take-≤ zero    _        = z≤n

length-take-≤ (suc _) []       = z≤n

length-take-≤ (suc k) (_ ∷ xs) = s≤s (length-take-≤ k xs)

take-sat : ∀ k (xs : List SigOpEvent) → length (take k xs) < k → take (suc k) xs ≡ take k xs

take-sat (suc _) []       _        = refl

take-sat (suc k) (x ∷ xs) (s≤s lt) = cong (x ∷_) (take-sat k xs lt)

take-coh : ∀ k (xs : List SigOpEvent) → ∃[ rest ] (take (suc k) xs ≡ take k xs ++ rest)

take-coh zero    []       = [] , refl

take-coh (suc k) []       = [] , refl

take-coh zero    (x ∷ xs) = [ x ] , refl

take-coh (suc k) (x ∷ xs) = proj₁ (take-coh k xs) , cong (x ∷_) (proj₂ (take-coh k xs))

take-pf : ∀ (xs : List SigOpEvent) → PrefixFamily (λ n → take n xs)

take-pf xs = prefixFamily (λ k → length-take-≤ k xs) (λ k → take-sat k xs) (λ k → take-coh k xs)

projTrace-pf : ∀ {X} (ι : Interp) (m : T X) → PrefixFamily (projTrace ι m)

projTrace-pf ι m = take-pf (eventsT ι m)

resVal-returns : ∀ {X} (r : Res X) (p : Returns? r) → r ≡ returns (resVal r p)

resVal-returns (returns x) _ = refl

RelT′-bind : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             {m : T X} {m′ : T X′} {f : X → T Y} {f′ : X′ → T Y′}
           → RelT′ R m m′ → (∀ x x′ → R x x′ → RelT′ S (f x) (f′ x′))
           → RelT′ S (m >>=T f) (m′ >>=T f′)

RelT′-bind R S (rel-ret r)  hf = hf _ _ r

RelT′-bind R S (rel-call h) hf = rel-call λ b → RelT′-bind R S (h b) hf

RelT′-bind R S rel-halt     hf = rel-halt

RelT′-fmap : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             {g : X → Y} {g′ : X′ → Y′} {m : T X} {m′ : T X′}
           → (∀ x x′ → R x x′ → S (g x) (g′ x′))
           → RelT′ R m m′ → RelT′ S (fmapT g m) (fmapT g′ m′)

RelT′-fmap R S hg rm = RelT′-bind R S rm λ x x′ r → rel-ret (hg x x′ r)

RelT′-refl : ∀ {X : Set} {R : X → X → Set} → (∀ x → R x x) → (m : T X) → RelT′ R m m

RelT′-refl hr (ret x)      = rel-ret (hr x)

RelT′-refl hr (call o a k) = rel-call λ b → RelT′-refl hr (k b)

RelT′-refl hr (halt o a)   = rel-halt

-- At a functional relation, relatedness IS an equation.
RelT′-≡ : ∀ {X Y : Set} (g : X → Y) {m : T X} {m′ : T Y}
        → RelT′ (λ x y → g x ≡ y) m m′ → fmapT g m ≡ m′

RelT′-≡ g (rel-ret refl) = refl

RelT′-≡ g (rel-call h)   = cong (call _ _) (extensionality λ b → RelT′-≡ g (h b))

RelT′-≡ g rel-halt       = refl

≡-RelT′ : ∀ {X Y : Set} (g : X → Y) (m : T X) {m′ : T Y}
        → fmapT g m ≡ m′ → RelT′ (λ x y → g x ≡ y) m m′

≡-RelT′ g m refl = to-fmap m
  where
    to-fmap : (m : T _) → RelT′ (λ x y → g x ≡ y) m (fmapT g m)
    to-fmap (ret x)      = rel-ret refl
    to-fmap (call o a k) = rel-call λ b → to-fmap (k b)
    to-fmap (halt o a)   = rel-halt

-- Related computations RUN alike: against any interpretation, from any
-- history, they make the same calls and end relatedly.
RelT′-events : ∀ {X Y : Set} {R : X → Y → Set} (ι : Interp) (h : List SigOpEvent) {m : T X} {m′ : T Y}
             → RelT′ R m m′ → proj₁ (run ι h m) ≡ proj₁ (run ι h m′)

RelT′-events ι h (rel-ret _)  = refl

RelT′-events ι h (rel-call {o} {a} hk) = go (callAnswer ι h o a)
  where go : (mb : Maybe M.⟦ ccod o ⟧) → proj₁ (run-call ι h o a _ mb) ≡ proj₁ (run-call ι h o a _ mb)
        go (just b) = cong (callEvent o a ∷_) (RelT′-events ι (h ++ [ callEvent o a ]) (hk b))
        go nothing  = refl

RelT′-events ι h rel-halt     = refl

RelT′-result : ∀ {X Y : Set} {R : X → Y → Set} (ι : Interp) (h : List SigOpEvent) {m : T X} {m′ : T Y}
             → RelT′ R m m′ → RelRes R (resultAt ι h m) (resultAt ι h m′)

RelT′-result ι h (rel-ret r)  = rel-returns r

RelT′-result ι h (rel-call {o} {a} hk) = go (callAnswer ι h o a)
  where go : (mb : Maybe M.⟦ ccod o ⟧) → RelRes _ (proj₂ (run-call ι h o a _ mb)) (proj₂ (run-call ι h o a _ mb))
        go (just b) = RelT′-result ι (h ++ [ callEvent o a ]) (hk b)
        go nothing  = rel-stopped

RelT′-result ι h rel-halt     = rel-stopped

take-++-split : ∀ {A : Set} (k : ℕ) (as bs : List A)
              → take k (as ++ bs) ≡ take k as ++ take (k ∸ length as) bs

take-++-split zero    as       bs = sym (cong (λ m → take m bs) (0∸n≡0 (length as)))

take-++-split (suc k) []       bs = refl

take-++-split (suc k) (a ∷ as) bs = cong (a ∷_) (take-++-split k as bs)

minus-take : ∀ {A : Set} (k : ℕ) (as : List A)
           → k ∸ length (take k as) ≡ k ∸ length as

minus-take zero    as       = sym (0∸n≡0 (length as))

minus-take (suc k) []       = refl

minus-take (suc k) (a ∷ as) = minus-take k as

take-++-threaded : ∀ {A : Set} (k : ℕ) (as bs : List A)
                 → take k (as ++ bs)
                   ≡ take k as ++ take (k ∸ length (take k as)) bs

take-++-threaded k as bs =
  trans (take-++-split k as bs)
        (cong (λ m → take k as ++ take m bs) (sym (minus-take k as)))

-- THE RUN OF A BIND IS THE RUNS OF ITS PARTS, the history threaded.
mutual
  run-bind : ∀ {X Y} (ι : Interp) (h : List SigOpEvent) (m : T X) (f : X → T Y)
           → run ι h (m >>=T f) ≡ then ι h (run ι h m) f
  run-bind ι h (ret x)      f = cong (λ hh → run ι hh (f x)) (sym (++-identityʳ h))
  run-bind ι h (call o a k) f = run-bind-call ι h o a k f (callAnswer ι h o a)
  run-bind ι h (halt o a)   f = refl

  run-bind-call : ∀ {X Y} (ι : Interp) (h : List SigOpEvent) (o : CallOp) (a : M.⟦ cdom o ⟧)
                    (k : M.⟦ ccod o ⟧ → T X) (f : X → T Y) (mb : Maybe M.⟦ ccod o ⟧)
                → run-call ι h o a (λ b → k b >>=T f) mb ≡ then ι h (run-call ι h o a k mb) f
  run-bind-call ι h o a k f (just b) =
    trans (cong (consE (callEvent o a)) (run-bind ι (h ++ [ callEvent o a ]) (k b) f))
          (cons-then ι h (callEvent o a)
             (proj₁ (run ι (h ++ [ callEvent o a ]) (k b))) (proj₂ (run ι (h ++ [ callEvent o a ]) (k b))) f)
  run-bind-call ι h o a k f nothing = refl

  cons-then : ∀ {X Y} ι h e es (r : Res X) (f : X → T Y)
            → consE e (then ι (h ++ [ e ]) (es , r) f) ≡ then ι h (consE e (es , r)) f
  cons-then ι h e es stopped     f = refl
  cons-then ι h e es (returns x) f = cong (λ hh → appE (e ∷ es) (run ι hh (f x))) (++-assoc h [ e ] es)
