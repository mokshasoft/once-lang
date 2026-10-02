-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spike.ITree — plan 0.105 phase 1: the POC for "a computation is an
-- interaction tree". Outside the apex; nothing imports it.
--
-- What it must show (the plan's gate):
--   1. the tree is a monad, postulate-free (extensionality is the
--      development's one standing axiom);
--   2. running a tree against an interpretation gives the event trace, and
--      running a bind is running its parts with the history threaded;
--   3. the budget observable (D058) is a prefix family;
--   4. the instances: no operations is a value (D250's pure); operations
--      answering ⊤ are today's Writer `T`; a halting operation stops
--      (0.98's `stopped`), with no continuation to run.
--
-- The tree is INDUCTIVE: Once is total, so every computation makes finitely
-- many calls (today's traces are all `capN n` of a finite list). It branches
-- over answers (a W-type), which is what lets an input differ.
------------------------------------------------------------------------

module Once.Spike.ITree where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; _∸_)
open import Data.List using (List; []; _∷_; _++_; length; take; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Postulates using (extensionality)
open import Once.Res using (Res; returns; stopped)

------------------------------------------------------------------------
-- An operation signature: what may be called, with what, answering what.
------------------------------------------------------------------------

-- Two kinds of operation, read off the declared codomain: an ANSWERING one
-- (a data or `Unit` codomain) continues with its answer; a HALTING one (a
-- `Void` codomain, D225) has no continuation at all. Interpretations answer
-- every answering call and are never asked a halting one, so "the world
-- answers; stopping is exactly at `Void`" (plan 0.105 decision 3) holds by
-- construction.
record Sig : Set₁ where
  field
    Op   : Set
    Arg  : Op → Set
    Ans  : Op → Set
    HOp  : Set
    HArg : HOp → Set
open Sig public

module _ (S : Sig) where

  data Tree (X : Set) : Set where
    ret  : X → Tree X
    call : (o : Op S) → Arg S o → (Ans S o → Tree X) → Tree X
    halt : (o : HOp S) → HArg S o → Tree X

  ----------------------------------------------------------------------
  -- 1. The monad
  ----------------------------------------------------------------------

  infixl 1 _>>=_
  _>>=_ : ∀ {X Y} → Tree X → (X → Tree Y) → Tree Y
  ret x      >>= f = f x
  call o a k >>= f = call o a (λ b → k b >>= f)
  halt o a   >>= f = halt o a

  fmap : ∀ {X Y} → (X → Y) → Tree X → Tree Y
  fmap g t = t >>= λ x → ret (g x)

  bind-identityˡ : ∀ {X Y} (x : X) (f : X → Tree Y) → (ret x >>= f) ≡ f x
  bind-identityˡ x f = refl

  bind-identityʳ : ∀ {X} (t : Tree X) → (t >>= ret) ≡ t
  bind-identityʳ (ret x)      = refl
  bind-identityʳ (call o a k) = cong (call o a) (extensionality λ b → bind-identityʳ (k b))
  bind-identityʳ (halt o a)   = refl

  bind-assoc : ∀ {X Y Z} (t : Tree X) (f : X → Tree Y) (g : Y → Tree Z)
             → ((t >>= f) >>= g) ≡ (t >>= λ x → f x >>= g)
  bind-assoc (ret x)      f g = refl
  bind-assoc (call o a k) f g = cong (call o a) (extensionality λ b → bind-assoc (k b) f g)
  bind-assoc (halt o a)   f g = refl

  ----------------------------------------------------------------------
  -- 2. Running against an interpretation
  --
  -- An event is a call: the operation and its argument (D058's observable).
  -- An interpretation answers an answering call, given the calls before it;
  -- what it answers is the interpretation's business (its contract).
  ----------------------------------------------------------------------

  Event : Set
  Event = Σ (Op S) (Arg S) ⊎ Σ (HOp S) (HArg S)

  Interp : Set
  Interp = List Event → (o : Op S) → Arg S o → Ans S o

  -- The events a run makes, and how it ended.
  Run : Set → Set
  Run X = List Event × Res X

  -- Prefixing and appending events (by projections, so η applies).
  consE : ∀ {X} → Event → Run X → Run X
  consE e r = (e ∷ proj₁ r) , proj₂ r

  appE : ∀ {X} → List Event → Run X → Run X
  appE es r = (es ++ proj₁ r) , proj₂ r

  run : ∀ {X} → Interp → List Event → Tree X → Run X
  run ι h (ret x)      = [] , returns x
  run ι h (call o a k) = consE (inj₁ (o , a)) (run ι (h ++ [ inj₁ (o , a) ]) (k (ι h o a)))
  run ι h (halt o a)   = [ inj₂ (o , a) ] , stopped

  -- Sequencing: the second run sees the first's events.
  then : ∀ {X Y} → Interp → List Event → Run X → (X → Tree Y) → Run Y
  then ι h r f = thenRes ι h (proj₁ r) (proj₂ r) f
    where
      thenRes : ∀ {X Y} → Interp → List Event → List Event → Res X → (X → Tree Y) → Run Y
      thenRes ι h es stopped     f = es , stopped
      thenRes ι h es (returns x) f = appE es (run ι (h ++ es) (f x))

  -- THE RUN OF A BIND IS THE RUNS OF ITS PARTS, the history threaded.
  mutual
    run-bind : ∀ {X Y} (ι : Interp) (h : List Event) (t : Tree X) (f : X → Tree Y)
             → run ι h (t >>= f) ≡ then ι h (run ι h t) f
    run-bind ι h (ret x)      f = cong (λ hh → run ι hh (f x)) (sym (++-identityʳ h))
    run-bind ι h (call o a k) f =
      let e = inj₁ (o , a) ; r = run ι (h ++ [ e ]) (k (ι h o a)) in
      trans (cong (consE e) (run-bind ι (h ++ [ e ]) (k (ι h o a)) f))
            (cons-then ι h e (proj₁ r) (proj₂ r) f)
    run-bind ι h (halt o a)   f = refl

    cons-then : ∀ {X Y} ι h e es (r : Res X) (f : X → Tree Y)
              → consE e (then ι (h ++ [ e ]) (es , r) f) ≡ then ι h (consE e (es , r)) f
    cons-then ι h e es stopped     f = refl
    cons-then ι h e es (returns x) f = cong (λ hh → appE (e ∷ es) (run ι hh (f x))) (++-assoc h [ e ] es)

  ----------------------------------------------------------------------
  -- 3. The budget observable (D058): the first n events of a run.
  ----------------------------------------------------------------------

  obs : ∀ {X} → Interp → Tree X → ℕ → List Event
  obs ι t n = take n (proj₁ (run ι [] t))

  -- A prefix family, because it is a cap of one finite list.
  obs-bounded : ∀ {X} ι (t : Tree X) n → length (obs ι t n) ≤ n
  obs-bounded ι t n = length-take-≤ n (proj₁ (run ι [] t))
    where
      length-take-≤ : ∀ k (xs : List Event) → length (take k xs) ≤ k
      length-take-≤ zero    xs       = Data.Nat.z≤n
      length-take-≤ (suc k) []       = Data.Nat.z≤n
      length-take-≤ (suc k) (x ∷ xs) = Data.Nat.s≤s (length-take-≤ k xs)

  obs-extends : ∀ {X} ι (t : Tree X) n → Σ (List Event) λ rest → obs ι t (suc n) ≡ obs ι t n ++ rest
  obs-extends ι t n = ext n (proj₁ (run ι [] t))
    where
      ext : ∀ k (xs : List Event) → Σ (List Event) λ rest → take (suc k) xs ≡ take k xs ++ rest
      ext zero    []       = [] , refl
      ext (suc k) []       = [] , refl
      ext zero    (x ∷ xs) = [ x ] , refl
      ext (suc k) (x ∷ xs) = proj₁ (ext k xs) , cong (x ∷_) (proj₂ (ext k xs))

------------------------------------------------------------------------
-- 4. The instances
------------------------------------------------------------------------

-- No operations: a tree is a value (D250's `pure`).
NoOps : Sig
NoOps = record { Op = ⊥ ; Arg = λ () ; Ans = λ () ; HOp = ⊥ ; HArg = λ () }

pure-value : ∀ {X} → Tree NoOps X → X
pure-value (ret x)       = x
pure-value (call () _ _)
pure-value (halt () _)

pure-iso : ∀ {X} (t : Tree NoOps X) → ret (pure-value t) ≡ t
pure-iso (ret x)       = refl
pure-iso (call () _ _)
pure-iso (halt () _)

-- A halting operation (`exit`) ends the run: no interpretation is asked, and
-- nothing after it runs (0.98's `stopped`, without a flag).
halts : ∀ {S : Sig} {X} (ι : Interp S) h (o : HOp S) (a : HArg S o)
      → proj₂ (run S ι h (halt {X = X} o a)) ≡ stopped
halts ι h o a = refl

halt-absorbs : ∀ {S : Sig} {X Y} (o : HOp S) (a : HArg S o) (f : X → Tree S Y)
             → (_>>=_ S (halt o a) f) ≡ halt o a
halt-absorbs o a f = refl

-- Operations answering ⊤ (output only) are today's Writer `T`: the answer
-- carries no information, so every interpretation gives the same run.
module _ (S : Sig) (unit : ∀ o → (b b′ : Ans S o) → b ≡ b′) where
  writer-indep : ∀ {X} (ι ι′ : Interp S) h (t : Tree S X) → run S ι h t ≡ run S ι′ h t
  writer-indep ι ι′ h (ret x)      = refl
  writer-indep ι ι′ h (call o a k) =
    trans (cong (λ b → consE S (inj₁ (o , a)) (run S ι (h ++ [ inj₁ (o , a) ]) (k b))) (unit o (ι h o a) (ι′ h o a)))
          (cong (consE S (inj₁ (o , a))) (writer-indep ι ι′ (h ++ [ inj₁ (o , a) ]) (k (ι′ h o a))))
  writer-indep ι ι′ h (halt o a)   = refl

-- Saturation: once a run has fewer events than the budget, more budget adds none.
module _ (S : Sig) where
  obs-saturating : ∀ {X} ι (t : Tree S X) n → length (obs S ι t n) Data.Nat.< n → obs S ι t (suc n) ≡ obs S ι t n
  obs-saturating ι t n = sat n (proj₁ (run S ι [] t))
    where
      sat : ∀ k (xs : List (Event S)) → length (take k xs) Data.Nat.< k → take (suc k) xs ≡ take k xs
      sat zero    xs       ()
      sat (suc k) []       _ = refl
      sat (suc k) (x ∷ xs) (Data.Nat.s≤s lt) = cong (x ∷_) (sat k xs lt)
