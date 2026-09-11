-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceMonad — the metatheoretic trace monad `T`.
--
-- Plan 0.46 (M1). `T` is the codomain of the denotational trace
-- semantics `⟦_⟧ᴰ`: an effectful arrow `A ⇒[ eff ] B` denotes the Kleisli
-- arrow `⟦A⟧ᴰ → T ⟦B⟧ᴰ`, so a closure already IS a trace-producing
-- function and `⟦apply⟧ (clo , a) = clo a` threads the trace with no
-- "running" and no fuel.
--
-- T X = ℕ → List SigOpEvent × X  — a budget-indexed Writer.
--
--   * The Writer component (`List SigOpEvent`) accumulates the EFFECTFUL
--     SigOp events, in order (pure SigOps `tell []`).
--   * The `ℕ` is the event-OBSERVATION DEPTH (D058): it is consumed ONLY
--     by the productive `Ana` unfold (one F-layer per decrement) and is
--     threaded inertly everywhere else. It is NOT a step-fuel and NOT a
--     termination device — `⟦_⟧ᴰ` is total by structural recursion on the
--     IR; the `ℕ` is a parameter the productive part reads. (Finite
--     computations — every `Cata`, every total closure — ignore it and
--     emit a finite list; the single top-level `Ana` grows the trace with
--     the depth, which is exactly the apex's `∀ n`.)
--
-- `T` is the Reader(ℕ) ⊗ Writer(List SigOpEvent) monad: total, --safe,
-- no co-data. The observable is `projTrace`.
------------------------------------------------------------------------

module Once.Denotation.TraceMonad where

open import Data.Nat using (ℕ; _∸_)
open import Data.List using (List; []; _++_; length; take)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Once.Denotation.Trace using (SigOpEvent)

------------------------------------------------------------------------
-- The monad.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

T : Set → Set
T X = ℕ → List SigOpEvent × X

infixl 1 _>>=T_ _>>T_

returnT : ∀ {X} → X → T X
returnT x _ = ([] , x)

-- Kleisli sequencing: run `m`, then `f x`, concatenating their events in
-- order. The budget is THREADED: `f` sees what `m` left, `n ∸ length es`.
-- That is what makes `length (projTrace (m >>=T f) n) ≤ n` hold — with a
-- shared `n` each side could independently spend the whole budget, and two
-- sequenced SigOps would emit 2 events at budget 1.
_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
(m >>=T f) n =
  let exr = m n
      eyr = f (proj₂ exr) (n ∸ length (proj₁ exr))
  in (proj₁ exr ++ proj₁ eyr , proj₂ eyr)

_>>T_ : ∀ {X Y} → T X → T Y → T Y
m >>T k = m >>=T λ _ → k

fmapT : ∀ {X Y} → (X → Y) → T X → T Y
fmapT g m n = (proj₁ (m n) , g (proj₂ (m n)))

-- Emit events (the Writer `tell`).
tell : List SigOpEvent → T ⊤
tell es k = (take k es , tt)

------------------------------------------------------------------------
-- Projections — the observable is `projTrace`.
------------------------------------------------------------------------

-- The trace (effectful SigOp events) at observation depth `n`.
projTrace : ∀ {X} → T X → ℕ → List SigOpEvent
projTrace m n = proj₁ (m n)

-- The value at observation depth `n` (internal; the apex observes only
-- the trace).
valueT : ∀ {X} → T X → ℕ → X
valueT m n = proj₂ (m n)

------------------------------------------------------------------------
-- Congruence at a fixed observation depth (the J-style bridge).
--
-- `(m >>=T f) k` reads `m` ONLY at `k`, so an equation between `m₁ k` and
-- `m₂ k` already determines the two binds at `k`. That is what this states.
--
-- WHY IT EXISTS. `rewrite` is `with`-abstraction, and a `with` cannot
-- generalise an occurrence sitting under a dependent `subst` chain — which is
-- exactly where the inner `⟦ e ⟧ˢ … k` sits in the `morph-app` denotation
-- (`subst T (cohᴰ B) (evalᴰ fmt ir (subst (λ z → z) (sym (cohᴰ A)) v))`).
-- Taking the equation as an explicit PARAMETER and consuming it with `cong`
-- sidesteps the abstraction entirely. Clauses whose wrapper is trivial
-- (`returnT (proj₁ v)` and friends) do not need this; clauses with a
-- subst-chain wrapper do.
bindAt : ∀ {X Y : Set} → (X → T Y) → ℕ → (List SigOpEvent × X) → (List SigOpEvent × Y)
bindAt f n exr =
  let k = n ∸ length (proj₁ exr)
  in (proj₁ exr ++ proj₁ (f (proj₂ exr) k) , proj₂ (f (proj₂ exr) k))

>>=T-at : ∀ {X Y : Set} (m : T X) (f : X → T Y) (n : ℕ) → (m >>=T f) n ≡ bindAt f n (m n)
>>=T-at m f n = refl

>>=T-cong-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f : X → T Y) (n : ℕ)
             → m₁ n ≡ m₂ n → (m₁ >>=T f) n ≡ (m₂ >>=T f) n
>>=T-cong-at f n eq = cong (bindAt f n) eq

-- | The NESTED-bind version: the two binds may differ in BOTH the monadic
--   value and the continuation. `app`-shaped clauses need this — their
--   continuation mentions the argument's denotation, which also changes.
--
--   The continuation premise is pointwise at EVERY budget: `bindAt` applies
--   the continuation at the REMAINDER `n ∸ length (proj₁ r)`, a budget the
--   caller cannot name before `r` is known. Quantifying over it keeps the
--   lemma free of extensionality while covering the budget actually used.
bindAt-cong : ∀ {X Y : Set} (f₁ f₂ : X → T Y) (n : ℕ) {r₁ r₂ : List SigOpEvent × X}
            → r₁ ≡ r₂
            → (∀ x k → f₁ x k ≡ f₂ x k)
            → bindAt f₁ n r₁ ≡ bindAt f₂ n r₂
bindAt-cong f₁ f₂ n {r} refl fe =
  cong₂ _,_ (cong (proj₁ r ++_) (cong proj₁ (fe (proj₂ r) _)))
            (cong proj₂ (fe (proj₂ r) _))

>>=T-cong₂-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f₁ f₂ : X → T Y) (n : ℕ)
              → m₁ n ≡ m₂ n
              → (∀ x k → f₁ x k ≡ f₂ x k)
              → (m₁ >>=T f₁) n ≡ (m₂ >>=T f₂) n
>>=T-cong₂-at f₁ f₂ n meq fe = bindAt-cong f₁ f₂ n meq fe

------------------------------------------------------------------------
-- The prefix-family invariant.
--
-- `Behavior` (the spec) says its `at` is "the first `n` events": bounded by
-- `n`, and extending as `n` grows. A `T`-computation is a producer of such a
-- family, so it owes the same two properties — plus a third that the two do
-- not imply and that sequencing needs:
--
--   `Saturating`: a computation that did NOT spend its whole budget is
--   FINISHED, so a larger budget changes nothing. Without it, `bnd` and
--   `coh` still admit a family that discards its events and starts over
--   (`at n = [a,b]`, `at (suc n) = [c,d,e]`): both are bounded, and `coh`'s
--   obligation is vacuous at no step. Sequencing reads the FIRST component's
--   value to build the second, so saturation is stated on the whole pair —
--   the value must not move either.
--
-- These are predicates, not fields of `T`: `T` has ~900 construction sites,
-- and the invariant is a theorem about `evalᴰ`, checked against the spec,
-- not an obligation discharged at every `returnT`.
------------------------------------------------------------------------

open import Data.Nat using (suc; _≤_; _<_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (m+[n∸m]≡n; +-mono-≤; ≤-trans; ≤-refl; m≤n⇒m<n∨m≡n; +-comm)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.Product using (∃-syntax; Σ; _×_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)

Bounded : ∀ {X} → T X → Set
Bounded m = ∀ k → length (projTrace m k) ≤ k

Saturating : ∀ {X} → T X → Set
Saturating m = ∀ k → length (projTrace m k) < k → m (suc k) ≡ m k

Coherent : ∀ {X} → T X → Set
Coherent m = ∀ k → ∃[ rest ] (projTrace m (suc k) ≡ projTrace m k ++ rest)

-- A computation satisfying all three. Sequencing preserves it (below), which
-- is the whole point: `Behavior`'s two fields are read off the top of a
-- derivation built from these.
record PrefixFamily {X : Set} (m : T X) : Set where
  constructor prefixFamily
  field
    bnd : Bounded m
    sat : Saturating m
    coh : Coherent m

open PrefixFamily public

------------------------------------------------------------------------
-- Sequencing preserves the invariant.
--
-- This is the lemma the threaded budget exists for. Both the threading and
-- `Saturating` are FORCED here, and the two cases show why:
--
--   * `bnd` needs the threading. With a shared `n` each side could spend the
--     whole budget and the sum would exceed it.
--   * `coh` splits on whether `m` spent everything. If it did, `f` gets
--     budget 0 and contributes nothing, so the composite IS `m`'s trace and
--     `m`'s own coherence carries it. If it did not, `m` is FINISHED
--     (`sat`), so growing the budget leaves `m`'s events AND value fixed and
--     hands the extra unit to `f` — where `f`'s coherence applies. Without
--     `sat` the second case is unprovable: `m`'s events could be replaced
--     wholesale, inserting new events BEFORE `f`'s.
------------------------------------------------------------------------

open import Data.Nat using (zero)
open import Data.Nat.Properties using (+-∸-assoc; m+n∸m≡n; ∸-monoˡ-≤; m≤m+n; ≤-reflexive; n∸n≡0; +-suc)
open import Data.List using (_∷_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong-app)

returnT-pf : ∀ {X} (x : X) → PrefixFamily (returnT x)
returnT-pf x = prefixFamily (λ _ → z≤n) (λ _ _ → refl) (λ _ → [] , refl)

-- `take` IS the prefix family on a fixed list: bounded by construction,
-- finished once the list runs out, and extending one element at a time.
-- Every event-emitting LEAF has this shape.
length-take-≤ : ∀ k (xs : List SigOpEvent) → length (take k xs) ≤ k
length-take-≤ zero    _        = z≤n
length-take-≤ (suc _) []       = z≤n
length-take-≤ (suc k) (_ ∷ xs) = s≤s (length-take-≤ k xs)

take-sat : ∀ k (xs : List SigOpEvent) → length (take k xs) < k → take (suc k) xs ≡ take k xs
take-sat (suc _) []       _        = refl
take-sat (suc k) (x ∷ xs) (s≤s h)  = cong (x ∷_) (take-sat k xs h)

take-coh : ∀ k (xs : List SigOpEvent) → ∃[ rest ] (take (suc k) xs ≡ take k xs ++ rest)
take-coh zero    []       = [] , refl
take-coh zero    (x ∷ _)  = x ∷ [] , refl
take-coh (suc k) []       = [] , refl
take-coh (suc k) (x ∷ xs) with take-coh k xs
... | r , eq = r , cong (x ∷_) eq

-- A leaf: emit (a prefix of) a FIXED list of events, with a value that does
-- not read the budget. `evalᴰ`'s SigOp clause is exactly this.
constT-pf : ∀ {X} (es : List SigOpEvent) (x : X) → PrefixFamily {X} (λ n → (take n es , x))
constT-pf es x =
  prefixFamily (λ k → length-take-≤ k es)
               (λ k h → cong (_, x) (take-sat k es h))
               (λ k → take-coh k es)

tell-pf : ∀ es → PrefixFamily (tell es)
tell-pf es = constT-pf es tt


-- The two facts about `∸` that the budget threading needs, named once.
suc∸ : ∀ {l k} → l ≤ k → suc k ∸ l ≡ suc (k ∸ l)
suc∸ {l} {k} l≤k = +-∸-assoc 1 l≤k

split-< : ∀ {l lf k} → l + lf < k → lf < k ∸ l
split-< {l} {lf} {k} h =
  subst (_≤ k ∸ l) (m+n∸m≡n l (suc lf))
    (∸-monoˡ-≤ l (subst (_≤ k) (sym (+-suc l lf)) h))

-- The continuation hypothesis is at the values `m` ACTUALLY produces, not at
-- every `x : X`. The proof only ever reads it there, and the stronger form is
-- unusable downstream: in a logical relation `f x` is a prefix family only
-- when `x` is well-behaved, which junk inhabitants of `X` need not be.
>>=T-pf : ∀ {X Y} (m : T X) (f : X → T Y)
        → PrefixFamily m → (∀ k → PrefixFamily (f (valueT m k))) → PrefixFamily (m >>=T f)
>>=T-pf m f pm pf = prefixFamily bnd′ sat′ coh′
  where
    lm : ℕ → ℕ
    lm k = length (projTrace m k)

    xv : ℕ → _
    xv k = valueT m k

    rest-of : ℕ → List SigOpEvent
    rest-of k = projTrace (f (xv k)) (k ∸ lm k)

    len-split : ∀ k → length (projTrace (m >>=T f) k) ≡ lm k + length (rest-of k)
    len-split k = length-++ (projTrace m k) {rest-of k}

    bnd′ : Bounded (m >>=T f)
    bnd′ k =
      subst (_≤ k) (sym (len-split k))
        (subst (lm k + length (rest-of k) ≤_) (m+[n∸m]≡n (bnd pm k))
          (+-mono-≤ (≤-refl {lm k}) (bnd (pf k) (k ∸ lm k))))

    sat′ : Saturating (m >>=T f)
    sat′ k h = seq (sat pm k lm<k) (sat (pf k) (k ∸ lm k) lf<k')
      where
        sum< : lm k + length (rest-of k) < k
        sum< = subst (_< k) (len-split k) h

        lm<k : lm k < k
        lm<k = ≤-trans (s≤s (m≤m+n (lm k) (length (rest-of k)))) sum<

        lf<k' : length (rest-of k) < k ∸ lm k
        lf<k' = split-< sum<

        -- Both components are finished, so the composite is: `m`'s pair is
        -- fixed (hence the continuation and its budget-offset are too), and
        -- `f` at the extra unit of budget agrees with `f` at the budget it had.
        seq : m (suc k) ≡ m k
            → f (xv k) (suc (k ∸ lm k)) ≡ f (xv k) (k ∸ lm k)
            → (m >>=T f) (suc k) ≡ (m >>=T f) k
        seq em ef =
          trans (cong (λ p → (proj₁ p ++ proj₁ (f (proj₂ p) (suc k ∸ length (proj₁ p)))
                             , proj₂ (f (proj₂ p) (suc k ∸ length (proj₁ p))))) em)
                (trans (cong (λ b → (projTrace m k ++ proj₁ (f (xv k) b)
                                    , proj₂ (f (xv k) b)))
                             (suc∸ (bnd pm k)))
                       (cong (λ r → (projTrace m k ++ proj₁ r , proj₂ r)) ef))

    coh′ : Coherent (m >>=T f)
    coh′ k = go (m≤n⇒m<n∨m≡n (bnd pm k))
      where
        -- `m` did NOT spend everything: it is finished, and the extra unit
        -- of budget goes to `f`.
        spare : lm k < k → ∃[ rest ] (projTrace (m >>=T f) (suc k) ≡ projTrace (m >>=T f) k ++ rest)
        spare lm<k with coh (pf k) (k ∸ lm k)
        ... | r , eqf = r ,
          trans (cong (λ p → proj₁ p ++ proj₁ (f (proj₂ p) (suc k ∸ length (proj₁ p))))
                      (sat pm k lm<k))
          (trans (cong (λ b → projTrace m k ++ proj₁ (f (xv k) b)) (suc∸ (bnd pm k)))
          (trans (cong (projTrace m k ++_) eqf)
                 (sym (++-assoc (projTrace m k) (rest-of k) r))))

        -- `m` spent the whole budget: `f` runs at 0 and contributes nothing,
        -- so the composite's trace IS `m`'s, and `m`'s coherence carries it.
        spent : lm k ≡ k → ∃[ rest ] (projTrace (m >>=T f) (suc k) ≡ projTrace (m >>=T f) k ++ rest)
        spent lm≡k with coh pm k
        ... | r , eqm = r ++ tailPart ,
          trans (cong (_++ tailPart) eqm)
          (trans (++-assoc (projTrace m k) r tailPart)
                 (cong (_++ (r ++ tailPart)) (sym nil-rest)))
          where
            tailPart : List SigOpEvent
            tailPart = rest-of (suc k)

            nil-rest : projTrace (m >>=T f) k ≡ projTrace m k
            nil-rest =
              trans (cong (projTrace m k ++_) (empty-at-0))
                    (++-identityʳ (projTrace m k))
              where
                empty-at-0 : rest-of k ≡ []
                empty-at-0 = len0 (bnd (pf k) (k ∸ lm k))
                  where
                    k∸lm≡0 : k ∸ lm k ≡ 0
                    k∸lm≡0 = subst (λ z → k ∸ z ≡ 0) (sym lm≡k) (n∸n≡0 k)

                    len0 : length (rest-of k) ≤ k ∸ lm k → rest-of k ≡ []
                    len0 h with rest-of k | subst (λ z → length (rest-of k) ≤ z) k∸lm≡0 h
                    ... | []    | _ = refl
                    ... | _ ∷ _ | ()

        go : lm k < k ⊎ lm k ≡ k → ∃[ rest ] (projTrace (m >>=T f) (suc k) ≡ projTrace (m >>=T f) k ++ rest)
        go (inj₁ p) = spare p
        go (inj₂ p) = spent p

------------------------------------------------------------------------
-- Related computations.
--
-- Two `T`s correspond when their traces agree and their values are related,
-- at EVERY budget. Adequacy proofs whose carrier is a computation (the cata
-- fold, since D179) need this plus its bind congruence; before the carrier
-- was a `List × value` pair, they split into a trace half and a value half
-- and reconciled the two by hand.
------------------------------------------------------------------------

RelT′ : ∀ {X Y : Set} (R : X → Y → Set) → T X → T Y → Set
RelT′ R l r = ∀ k → (projTrace l k ≡ projTrace r k) × R (valueT l k) (valueT r k)

-- Bind preserves it. The two sides run their continuations at their OWN
-- remaining budgets; those budgets are computed from the head traces, which
-- the relation already equates — so no extra assumption is needed, exactly as
-- in `RelT-bind`.
RelT′-bind : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             (m : T X) (m′ : T X′) (f : X → T Y) (f′ : X′ → T Y′)
           → RelT′ R m m′
           → (∀ k → RelT′ S (f (valueT m k)) (f′ (valueT m′ k)))
           → RelT′ S (m >>=T f) (m′ >>=T f′)
RelT′-bind R S m m′ f f′ rm rf k =
    ( cong₂ _++_ (proj₁ (rm k))
        (trans (proj₁ (rf k kL)) (cong (λ es → projTrace (f′ (valueT m′ k)) (k ∸ length es)) (proj₁ (rm k))))
    , subst (λ j → S (valueT (f (valueT m k)) kL) (valueT (f′ (valueT m′ k)) j))
            keq (proj₂ (rf k kL)) )
  where
    kL = k ∸ length (projTrace m k)

    keq : kL ≡ k ∸ length (projTrace m′ k)
    keq = cong (λ es → k ∸ length es) (proj₁ (rm k))

------------------------------------------------------------------------
-- THE MONAD LAWS.
--
-- These were never stated for `T` — the module had congruence helpers
-- (`bindAt`, `>>=T-cong-at`) but no laws, so "T is a monad" was an
-- unchecked claim. Threading the budget is what made it worth checking:
-- with the old shared-budget bind every law was `++`-reasoning alone,
-- whereas now the budget arithmetic participates (see `>>=T-assoc`).
------------------------------------------------------------------------

-- Left identity: `returnT` spends nothing, and `k ∸ 0` is `k`, so this is
-- definitional even with threading.
>>=T-identityˡ : ∀ {X Y : Set} (x : X) (f : X → T Y) (k : ℕ)
               → (returnT x >>=T f) k ≡ f x k
>>=T-identityˡ x f k = refl

-- Right identity: needs `++-identityʳ`, since the bind appends `returnT`'s
-- empty trace.
>>=T-identityʳ : ∀ {X : Set} (m : T X) (k : ℕ)
               → (m >>=T returnT) k ≡ m k
>>=T-identityʳ m k = cong₂ _,_ (++-identityʳ (projTrace m k)) refl

------------------------------------------------------------------------
-- Associativity.
--
-- Still true with the threaded budget, but no longer DEFINITIONAL: the
-- left-nested form charges `g` the budget `k ∸ (|es f| + |es g|)` while the
-- right-nested form charges it `(k ∸ |es f|) ∸ |es g|`. Those agree by
-- `∸-+-assoc`, which is exactly the arithmetic the threading introduced.
------------------------------------------------------------------------

open import Data.Nat.Properties using (∸-+-assoc)

>>=T-assoc : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z) (k : ℕ)
           → ((m >>=T f) >>=T g) k ≡ (m >>=T (λ x → f x >>=T g)) k
>>=T-assoc m f g k = cong₂ _,_ tr vl
  where
    es-m = projTrace m k
    k₁   = k ∸ length es-m
    es-f = projTrace (f (valueT m k)) k₁
    k₂   = k₁ ∸ length es-f

    budget : k ∸ length (es-m ++ es-f) ≡ k₂
    budget = trans (cong (k ∸_) (length-++ es-m {es-f})) (sym (∸-+-assoc k (length es-m) (length es-f)))

    tr : projTrace ((m >>=T f) >>=T g) k ≡ projTrace (m >>=T (λ x → f x >>=T g)) k
    es-g = projTrace (g (valueT (f (valueT m k)) k₁)) k₂

    tr = trans (cong (λ j → (es-m ++ es-f) ++ projTrace (g (valueT (f (valueT m k)) k₁)) j) budget)
               (++-assoc es-m es-f es-g)

    vl : valueT ((m >>=T f) >>=T g) k ≡ valueT (m >>=T (λ x → f x >>=T g)) k
    vl = cong (λ j → valueT (g (valueT (f (valueT m k)) k₁)) j) budget

-- Binding a PURE continuation is a map. The `++ []` residual these proofs
-- keep tripping over is exactly this: `⟨ f , g ⟩` ends in `returnT (b , c)`,
-- and under a threaded budget the residual shifts the NEXT continuation's
-- budget too, so rewriting the trace alone no longer suffices.
>>=T-map : ∀ {X Y : Set} (m : T X) (g : X → Y) (k : ℕ)
         → (m >>=T (λ x → returnT (g x))) k ≡ fmapT g m k
>>=T-map m g k = cong₂ _,_ (++-identityʳ (projTrace m k)) refl

-- Binding after a map is binding the composite. `fmapT` touches neither the
-- trace nor the budget, so this is definitional.
fmapT->>=T : ∀ {X Y Z : Set} (g : X → Y) (m : T X) (f : Y → T Z) (k : ℕ)
           → (fmapT g m >>=T f) k ≡ (m >>=T (λ x → f (g x))) k
fmapT->>=T g m f k = refl

------------------------------------------------------------------------
-- "T is a monad", as a CHECKED claim rather than a name.
--
-- `T`/`returnT`/`_>>=T_` are plain definitions: nothing about them obliged
-- anyone to prove a law, and this module asserted monadhood in its title and
-- header for the whole of its life without it being verified. (Stdlib's
-- `RawMonad` would not have helped — it is law-free by design.)
--
-- Bundling the laws and INSTANTIATING the bundle is what makes the claim
-- load-bearing: change `_>>=T_` in a way that breaks a law and `T-isMonad`
-- stops typechecking. Same correction D114 made for `Once.Denotation.Trace`,
-- and the same one `Behavior`'s record made for "the first `n` events".
--
-- The laws are stated POINTWISE in the budget, not as function equalities,
-- because this module takes no extensionality axiom (`Value.Laws` keeps that
-- separation for the same reason). Consumers with `funext` lift them.
------------------------------------------------------------------------

-- Extend the structure stdlib DOES provide, so the operations are forced into
-- the standard shape and the laws below are stated about THIS instance rather
-- than about free-floating names that could drift from it.
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

T-rawFunctor : RawFunctor T
T-rawFunctor = record { _<$>_ = fmapT }

T-rawApplicative : RawApplicative T
T-rawApplicative = record
  { rawFunctor = T-rawFunctor
  ; pure       = returnT
  ; _<*>_      = λ mf mx → mf >>=T λ f → mx >>=T λ x → returnT (f x)
  }

T-rawMonad : RawMonad T
T-rawMonad = record { rawApplicative = T-rawApplicative ; _>>=_ = _>>=T_ }

-- …and the laws stdlib does NOT provide. `RawMonad` is law-free by design, so
-- "T is a monad" was never checked by instantiating it; these three fields are
-- what make the claim real. Stated over `T-rawMonad`'s own operations, so a
-- change to `_>>=T_` that breaks a law stops `T-isMonad` from typechecking.
module _ where
  open RawMonad T-rawMonad using (_>>=_; pure)

  record IsMonadT : Set₁ where
    field
      identityˡ : ∀ {X Y : Set} (x : X) (f : X → T Y) (k : ℕ)
                → (pure x >>= f) k ≡ f x k
      identityʳ : ∀ {X : Set} (m : T X) (k : ℕ)
                → (m >>= pure) k ≡ m k
      assoc     : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z) (k : ℕ)
                → ((m >>= f) >>= g) k ≡ (m >>= (λ x → f x >>= g)) k

  T-isMonad : IsMonadT
  T-isMonad = record
    { identityˡ = >>=T-identityˡ
    ; identityʳ = >>=T-identityʳ
    ; assoc     = >>=T-assoc
    }
