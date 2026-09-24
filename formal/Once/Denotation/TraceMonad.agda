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
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Once.Res using (Res; stopped; returns; is-stopped; mapRes; Res-rel)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Once.Denotation.Trace using (SigOpEvent)

------------------------------------------------------------------------
-- The monad.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

-- plan 0.97: THE BUDGET IS A LENS, NOT A PARAMETER.
--
-- A computation IS a trace family, a termination fact and a value. The budget
-- truncates the VIEW of the trace; it does not change what the computation is.
-- So the value and the stop flag carry no budget, and "the value does not
-- drift with the budget" / "stoppedness does not drift with the budget" are
-- not theorems to prove at every producer — they are UNSTATABLE.
--
-- The previous shape `ℕ → List SigOpEvent × X` could not say that. It let a
-- computation's value depend on how long it was watched, and the sequencing
-- proof then needed two new invariants to rule out a behaviour nothing ever
-- wanted (plan 0.97 §5b).
--
-- `Stopped` is a flag rather than a `Maybe` on the value because `Halts`
-- forces `B ≡ Unit`: the value after a stop is `tt` regardless.
Stopped : Set
Stopped = Bool

-- plan 0.98: A COMPUTATION'S RESULT IS `Res` — a value, or the program ended.
--
-- 0.97 carried a `Stopped` flag beside a TOTAL value, on the grounds that
-- `Halts` forced `B ≡ Unit` so "the value after a stop is `tt` regardless".
-- That was the lie this plan removes: a halting SigOp has NO result, and
-- while the value was total every obligation mentioning it had to carry a
-- premise remembering not to look. With the value inside `Res`,
-- "stopped ⇒ no result" is a TYPING fact, not a premise.
record T (X : Set) : Set where
  constructor mkT
  field
    trT  : ℕ → List SigOpEvent
    resT : Res X

-- The budget view. A PAIR again — the result carries its own stoppedness, so
-- there is no third component to thread.
atT : ∀ {X} → T X → ℕ → List SigOpEvent × Res X
atT m n = (T.trT m n , T.resT m)

infixl 1 _>>=T_ _>>T_

returnT : ∀ {X} → X → T X
returnT x = mkT (λ _ → []) (returns x)

-- `returnT` for a result that may not exist: a SILENT computation carrying the
-- given `Res` verbatim. `returnT x ≡ resT-lift (returns x)` definitionally, and
-- the stopped case is the one `returnT` cannot express.
resT-lift : ∀ {X} → Res X → T X
resT-lift r = mkT (λ _ → []) r

-- Kleisli sequencing: run `m`, then `f x`, concatenating their events in
-- order. The budget is THREADED: `f` sees what `m` left, `n ∸ length es`.
-- That is what makes `length (projTrace (m >>=T f) n) ≤ n` hold — with a
-- shared `n` each side could independently spend the whole budget, and two
-- sequenced SigOps would emit 2 events at budget 1.
--
-- plan 0.98: a STOPPED computation NEVER BUILDS its continuation. `join-es`
-- and `join-st` are gone — they existed only to construct the sequel and then
-- discard it. Dispatched through a top-level helper on the `Res` rather than a
-- `with`, so it reduces on a constructor and stays STUCK — rather than wrong —
-- on a variable.
bindRes : ∀ {X Y} → (ℕ → List SigOpEvent) → Res X → (X → T Y) → T Y
bindRes tr stopped     f = mkT tr stopped
bindRes tr (returns x) f =
  mkT (λ n → tr n ++ T.trT (f x) (n ∸ length (tr n))) (T.resT (f x))

_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
m >>=T f = bindRes (T.trT m) (T.resT m) f

_>>T_ : ∀ {X Y} → T X → T Y → T Y
m >>T k = m >>=T λ _ → k

fmapT : ∀ {X Y} → (X → Y) → T X → T Y
fmapT g m = mkT (T.trT m) (mapRes g (T.resT m))

-- Emit events (the Writer `tell`).
tell : List SigOpEvent → T ⊤
tell es = mkT (λ k → take k es) (returns tt)

------------------------------------------------------------------------
-- Projections — the observable is `projTrace`.
------------------------------------------------------------------------

-- The trace (effectful SigOp events) at observation depth `n`.
projTrace : ∀ {X} → T X → ℕ → List SigOpEvent
projTrace m n = T.trT m n

-- Did the computation stop? Budget-free, read off the result.
stoppedT : ∀ {X} → T X → ℕ → Stopped
stoppedT m _ = is-stopped (T.resT m)

------------------------------------------------------------------------
-- THE VALUE — available only when the computation RETURNS (plan 0.98).
--
-- The premise is an IMPLICIT OF RECORD TYPE. Agda solves such a meta by eta,
-- so `valueT m k` typechecks UNCHANGED wherever the result reduces to
-- `returns` — which is every non-stopping constructor — and leaves an
-- UNSOLVED META exactly where the computation can genuinely stop. An unsolved
-- meta is reported alongside every other one instead of aborting the module,
-- so the migration surfaces all the real sites in ONE pass rather than one
-- per build. The discrimination the type makes is the discrimination the plan
-- is about.
------------------------------------------------------------------------

Returns? : ∀ {X} → Res X → Set
Returns? stopped     = ⊥
Returns? (returns _) = ⊤

resVal : ∀ {X} (r : Res X) → Returns? r → X
resVal (returns x) _ = x
resVal stopped     ()

-- The budget argument is KEPT and IGNORED: the value does not depend on it.
valueT : ∀ {X} (m : T X) (k : ℕ) {p : Returns? (T.resT m)} → X
valueT m k {p} = resVal (T.resT m) p

-- plan 0.98: THE TWO BRIDGES BETWEEN `valueT` AND THE `Res` IT READS.
--
-- A producer that only knows the boolean ("this shape does not stop") still
-- has to hand `valueT` its witness: `Returns?-of` is that step. And a consumer
-- whose obligation BINDS the value (`place`) has to identify it with the one
-- the producer placed: `resVal-returns` says the result IS `returns` of what
-- `valueT` reads, so `returns-inj` finishes the identification. Neither is an
-- assumption — both are one-clause case splits.
Returns?-of : ∀ {X} {r : Res X} → is-stopped r ≡ false → Returns? r
Returns?-of {r = returns _} _ = tt

resVal-returns : ∀ {X} (r : Res X) (p : Returns? r) → r ≡ returns (resVal r p)
resVal-returns (returns x) _ = refl

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
bindResAt : ∀ {X Y : Set} → (X → T Y) → ℕ → List SigOpEvent → Res X
          → List SigOpEvent × Res Y
bindResAt f n es stopped     = (es , stopped)
bindResAt f n es (returns x) = (es ++ T.trT (f x) (n ∸ length es) , T.resT (f x))

bindAt : ∀ {X Y : Set} → (X → T Y) → ℕ
       → (List SigOpEvent × Res X) → (List SigOpEvent × Res Y)
bindAt f n er = bindResAt f n (proj₁ er) (proj₂ er)

-- plan 0.98: no longer `refl` — both sides dispatch on the result, so the
-- bridge is the two-case split rather than a shared `join-*` application.
bindRes-at : ∀ {X Y : Set} (tr : ℕ → List SigOpEvent) (r : Res X)
             (f : X → T Y) (n : ℕ)
           → atT (bindRes tr r f) n ≡ bindResAt f n (tr n) r
bindRes-at tr stopped     f n = refl
bindRes-at tr (returns x) f n = refl

>>=T-at : ∀ {X Y : Set} (m : T X) (f : X → T Y) (n : ℕ)
        → atT (m >>=T f) n ≡ bindAt f n (atT m n)
>>=T-at m f n = bindRes-at (T.trT m) (T.resT m) f n

>>=T-cong-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f : X → T Y) (n : ℕ)
             → atT m₁ n ≡ atT m₂ n → atT (m₁ >>=T f) n ≡ atT (m₂ >>=T f) n
>>=T-cong-at {m₁ = m₁} {m₂} f n eq =
  trans (>>=T-at m₁ f n) (trans (cong (bindAt f n) eq) (sym (>>=T-at m₂ f n)))

-- | The NESTED-bind version: the two binds may differ in BOTH the monadic
--   value and the continuation. `app`-shaped clauses need this — their
--   continuation mentions the argument's denotation, which also changes.
bindResAt-cong : ∀ {X Y : Set} (f₁ f₂ : X → T Y) (n : ℕ)
                 (es : List SigOpEvent) (r : Res X)
               → (∀ x → f₁ x ≡ f₂ x)
               → bindResAt f₁ n es r ≡ bindResAt f₂ n es r
bindResAt-cong f₁ f₂ n es stopped     fe = refl
bindResAt-cong f₁ f₂ n es (returns x) fe =
  cong (λ fy → (es ++ T.trT fy (n ∸ length es) , T.resT fy)) (fe x)

bindAt-cong : ∀ {X Y : Set} (f₁ f₂ : X → T Y) (n : ℕ)
                {r₁ r₂ : List SigOpEvent × Res X}
            → r₁ ≡ r₂
            → (∀ x → f₁ x ≡ f₂ x)
            → bindAt f₁ n r₁ ≡ bindAt f₂ n r₂
bindAt-cong f₁ f₂ n {r} refl fe = bindResAt-cong f₁ f₂ n (proj₁ r) (proj₂ r) fe

>>=T-cong₂-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f₁ f₂ : X → T Y) (n : ℕ)
              → atT m₁ n ≡ atT m₂ n
              → (∀ x → f₁ x ≡ f₂ x)
              → atT (m₁ >>=T f₁) n ≡ atT (m₂ >>=T f₂) n
>>=T-cong₂-at {m₁ = m₁} {m₂} f₁ f₂ n meq fe =
  trans (>>=T-at m₁ f₁ n)
        (trans (bindAt-cong f₁ f₂ n meq fe) (sym (>>=T-at m₂ f₂ n)))

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

-- Stated on the TRACE, which is all it was ever about. The old form said
-- `m (suc k) ≡ m k` — equality of whole computations — and so quietly
-- asserted that the value does not move either. With the value budget-free
-- that half is now structural, and what remains is the real content.
Saturating : ∀ {X} → T X → Set
Saturating m = ∀ k → length (projTrace m k) < k → projTrace m (suc k) ≡ projTrace m k

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
open import Data.Nat.Properties using (+-∸-assoc; m+n∸m≡n; ∸-monoˡ-≤; m≤m+n; ≤-reflexive; n∸n≡0; +-suc; 0∸n≡0)
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
constT-pf : ∀ {X} (es : List SigOpEvent) (r : Res X)
          → PrefixFamily {X} (mkT (λ n → take n es) r)
constT-pf es r =
  prefixFamily (λ k → length-take-≤ k es)
               (λ k h → take-sat k es h)
               (λ k → take-coh k es)

tell-pf : ∀ es → PrefixFamily (tell es)
tell-pf es = constT-pf es (returns tt)


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
-- plan 0.98: the dispatch is on the RESULT, and the stopped case is now
-- literally `m`'s own family — the composite IS `m`, because no sequel was
-- built. The continuation hypothesis is correspondingly weaker and more
-- honest: it is owed only AT THE VALUE `m` actually produces, and only when
-- there is one.
-- `PrefixFamily` is indexed by the computation, but all three of its fields
-- mention only `projTrace` — so a family transports along any change of the
-- RESULT, which is what the stopped case of `bindRes` needs (its trace is the
-- head's, at the sequel's type).
pf-retype : ∀ {X Y} (tr : ℕ → List SigOpEvent) (rx : Res X) (ry : Res Y)
          → PrefixFamily (mkT tr rx) → PrefixFamily (mkT tr ry)
pf-retype tr rx ry p = prefixFamily (bnd p) (sat p) (coh p)

bindRes-pf : ∀ {X Y} (tr : ℕ → List SigOpEvent) (r : Res X) (f : X → T Y)
           → PrefixFamily (mkT tr r)
           → (∀ x → r ≡ returns x → PrefixFamily (f x))
           → PrefixFamily (bindRes tr r f)
bindRes-pf tr stopped     f pm pf = pf-retype tr stopped stopped pm
bindRes-pf tr (returns x) f pm pf = prefixFamily bnd′ sat′ coh′
  where
    fy : T _
    fy = f x

    pfy : PrefixFamily fy
    pfy = pf x refl

    lm : ℕ → ℕ
    lm k = length (tr k)

    rest-of : ℕ → List SigOpEvent
    rest-of k = projTrace fy (k ∸ lm k)

    len-split : ∀ k → length (tr k ++ rest-of k) ≡ lm k + length (rest-of k)
    len-split k = length-++ (tr k) {rest-of k}

    bnd′ : Bounded (bindRes tr (returns x) f)
    bnd′ k =
      subst (_≤ k) (sym (len-split k))
        (subst (lm k + length (rest-of k) ≤_) (m+[n∸m]≡n (bnd pm k))
          (+-mono-≤ (≤-refl {lm k}) (bnd pfy (k ∸ lm k))))

    sat′ : Saturating (bindRes tr (returns x) f)
    sat′ k h = cong₂ _++_ satm restEq
      where
        sum< : lm k + length (rest-of k) < k
        sum< = subst (_< k) (len-split k) h
        lm<k : lm k < k
        lm<k = ≤-trans (s≤s (m≤m+n (lm k) (length (rest-of k)))) sum<
        lf<k′ : length (rest-of k) < k ∸ lm k
        lf<k′ = split-< sum<
        satm : tr (suc k) ≡ tr k
        satm = sat pm k lm<k
        restEq : rest-of (suc k) ≡ rest-of k
        restEq =
          trans (cong (λ es → projTrace fy (suc k ∸ length es)) satm)
                (trans (cong (projTrace fy) (suc∸ (bnd pm k)))
                       (sat pfy (k ∸ lm k) lf<k′))

    coh′ : Coherent (bindRes tr (returns x) f)
    coh′ k = go (m≤n⇒m<n∨m≡n (bnd pm k))
      where
        -- `m` did NOT spend everything: it is finished, and the extra unit of
        -- budget goes to `f`.
        spare : lm k < k
              → ∃[ rest ] (tr (suc k) ++ rest-of (suc k)
                           ≡ (tr k ++ rest-of k) ++ rest)
        spare lm<k with coh pfy (k ∸ lm k)
        ... | r , eqf = r ,
          trans (cong₂ _++_ (sat pm k lm<k)
                   (trans (cong (λ es → projTrace fy (suc k ∸ length es)) (sat pm k lm<k))
                          (trans (cong (projTrace fy) (suc∸ (bnd pm k))) eqf)))
                (sym (++-assoc (tr k) (rest-of k) r))

        -- `m` spent the whole budget: `f` runs at 0 and contributes nothing,
        -- so the composite's trace IS `m`'s and `m`'s coherence carries it.
        spent : lm k ≡ k
              → ∃[ rest ] (tr (suc k) ++ rest-of (suc k)
                           ≡ (tr k ++ rest-of k) ++ rest)
        spent lm≡k with coh pm k
        ... | r , eqm = r ++ tailPart ,
          trans (cong (_++ tailPart) eqm)
          (trans (++-assoc (tr k) r tailPart)
                 (cong (_++ (r ++ tailPart)) (sym nil-rest)))
          where
            tailPart : List SigOpEvent
            tailPart = rest-of (suc k)

            empty-at-0 : rest-of k ≡ []
            empty-at-0 = len0 (bnd pfy (k ∸ lm k))
              where
                k∸lm≡0 : k ∸ lm k ≡ 0
                k∸lm≡0 = subst (λ z → k ∸ z ≡ 0) (sym lm≡k) (n∸n≡0 k)

                len0 : length (rest-of k) ≤ k ∸ lm k → rest-of k ≡ []
                len0 h with rest-of k | subst (λ z → length (rest-of k) ≤ z) k∸lm≡0 h
                ... | []    | _ = refl
                ... | _ ∷ _ | ()

            nil-rest : tr k ++ rest-of k ≡ tr k
            nil-rest =
              trans (cong (tr k ++_) empty-at-0)
                    (++-identityʳ (tr k))

        go : lm k < k ⊎ lm k ≡ k
           → ∃[ rest ] (tr (suc k) ++ rest-of (suc k)
                        ≡ (tr k ++ rest-of k) ++ rest)
        go (inj₁ h) = spare h
        go (inj₂ h) = spent h

>>=T-pf : ∀ {X Y} (m : T X) (f : X → T Y)
        → PrefixFamily m
        → (∀ x → T.resT m ≡ returns x → PrefixFamily (f x))
        → PrefixFamily (m >>=T f)
>>=T-pf m f pm pf = bindRes-pf (T.trT m) (T.resT m) f pm pf

------------------------------------------------------------------------
-- CORRESPONDENCE OF TWO COMPUTATIONS.
--
-- Two `T`s correspond when their traces agree, their STOP FLAGS agree, and
-- their values are related. Adequacy proofs whose carrier is a computation
-- (the cata fold, since D179) need this plus its bind congruence.
--
-- plan 0.97: the flag half is not decoration — `_>>=T_`'s trace is
-- `join-es (stT m) …`, so without it the bind congruence below cannot
-- conclude the two composite traces agree. Adding the stop channel to `T`
-- forced the relation to carry it.
------------------------------------------------------------------------

-- plan 0.98: the relation on RESULTS. Two computations correspond when their
-- traces agree and their results do — and two results correspond only if they
-- agree on whether the program ended.
--
-- This IS `Once.Res.Res-rel`, not a second copy of it. The first cut of 0.98
-- wrote the four clauses out again here; that made `RelT′` (this module) and
-- `RelT` (`MeaningRelation`, stated with `Res-rel`) non-convertible even
-- though they say the same thing, and this module then used BOTH names —
-- `bindRes-rel` below already reads `Res-rel`. One definition, and the local
-- name is kept only because the bind congruence below is stated with it.
RelRes : ∀ {X Y : Set} (R : X → Y → Set) → Res X → Res Y → Set
RelRes R = Res-rel R

-- | Reading a `RelRes` at the two values it relates. Every consumer of
--   `RelT′-bind` needs this — the continuation hypothesis is owed only where
--   both sides returned, and it is the `≡ returns _` premises that SUPPLY the
--   values — so it sits here beside the relation rather than being rewritten
--   in each proof module.
RelRes-value : ∀ {X Y : Set} {R : X → Y → Set} {r : Res X} {r′ : Res Y} {x y}
             → RelRes R r r′ → r ≡ returns x → r′ ≡ returns y → R x y
RelRes-value rr refl refl = rr

RelT′ : ∀ {X Y : Set} (R : X → Y → Set) → T X → T Y → Set
RelT′ R l r = ∀ k → (projTrace l k ≡ projTrace r k)
                  × RelRes R (T.resT l) (T.resT r)

-- Bind preserves it. The two sides run their continuations at their OWN
-- remaining budgets; those budgets are computed from the head traces, which
-- the relation already equates — so no extra assumption is needed.
--
-- plan 0.98: the continuation hypothesis is owed only where BOTH sides
-- return, and at the values they actually produce. A stopped head discharges
-- the whole thing from the head's own agreement, because neither side built a
-- sequel.
RelRes-bind : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
              (tr : ℕ → List SigOpEvent) (tr′ : ℕ → List SigOpEvent)
              (r : Res X) (r′ : Res X′) (f : X → T Y) (f′ : X′ → T Y′) (k : ℕ)
            → (∀ j → tr j ≡ tr′ j)
            → RelRes R r r′
            → (∀ x x′ → r ≡ returns x → r′ ≡ returns x′ → RelT′ S (f x) (f′ x′))
            → (projTrace (bindRes tr r f) k ≡ projTrace (bindRes tr′ r′ f′) k)
              × RelRes S (T.resT (bindRes tr r f)) (T.resT (bindRes tr′ r′ f′))
RelRes-bind R S tr tr′ stopped     stopped     f f′ k te rr rf = (te k , tt)
RelRes-bind R S tr tr′ stopped     (returns _) f f′ k te ()
RelRes-bind R S tr tr′ (returns _) stopped     f f′ k te ()
RelRes-bind R S tr tr′ (returns x) (returns y) f f′ k te rr rf =
  ( cong₂ _++_ (te k)
      (trans (proj₁ (rf x y refl refl (k ∸ length (tr k))))
             (cong (λ es → projTrace (f′ y) (k ∸ length es)) (te k)))
  , proj₂ (rf x y refl refl (k ∸ length (tr k))) )

RelT′-bind : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             (m : T X) (m′ : T X′) (f : X → T Y) (f′ : X′ → T Y′)
           → RelT′ R m m′
           → (∀ x x′ → T.resT m ≡ returns x → T.resT m′ ≡ returns x′
                     → RelT′ S (f x) (f′ x′))
           → RelT′ S (m >>=T f) (m′ >>=T f′)
RelT′-bind R S m m′ f f′ rm rf k =
  RelRes-bind R S (T.trT m) (T.trT m′) (T.resT m) (T.resT m′) f f′ k
              (λ j → proj₁ (rm j)) (proj₂ (rm k)) rf

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
-- plan 0.97: the three laws now also have to move the STOP flag, and each
-- does so by the same three-way dispatch — `a` stopped swallows everything
-- after it, `b` stopped swallows what is after `b`, and otherwise the old
-- `++`/budget reasoning applies unchanged.
-- plan 0.98: `join-st-idʳ`/`join-es-idʳ`/`join-st-assoc` are GONE. They were
-- the arithmetic of discarding a sequel that had been built anyway; with
-- `bindRes` the sequel is never built, so each law is a two-case split whose
-- stopped branch is `refl`.

-- Left identity: `returnT` spends nothing and stops nothing, so this is
-- definitional even with threading.
>>=T-identityˡ : ∀ {X Y : Set} (x : X) (f : X → T Y) (k : ℕ)
               → atT (returnT x >>=T f) k ≡ atT (f x) k
>>=T-identityˡ x f k = refl

-- Right identity: needs `++-identityʳ` on the trace and `join-st-idʳ` on the
-- flag, since the bind appends `returnT`'s empty trace and its `false`.
>>=T-identityʳ : ∀ {X : Set} (m : T X) (k : ℕ)
               → atT (m >>=T returnT) k ≡ atT m k
bindRes-idʳ : ∀ {X : Set} (tr : ℕ → List SigOpEvent) (r : Res X) (k : ℕ)
            → atT (bindRes tr r returnT) k ≡ (tr k , r)
bindRes-idʳ tr stopped     k = refl
bindRes-idʳ tr (returns x) k = cong (_, returns x) (++-identityʳ (tr k))

>>=T-identityʳ m k = bindRes-idʳ (T.trT m) (T.resT m) k

-- Right identity, GENERALISED: binding with a `returnT` of anything is `fmapT`.
-- 0.97 needed this shape at every pair-build residual and spelled it as
-- `join-es-idʳ`/`join-st-idʳ` applied separately to the trace and the flag —
-- two lemmas because the triple had two components to fix up. With `Res` it
-- is one statement, and its stopped branch is `refl`: no sequel was built, so
-- there is no `++ []` to remove.
bindRes-mapʳ : ∀ {X Y : Set} (tr : ℕ → List SigOpEvent) (r : Res X)
                 (h : X → Y) (k : ℕ)
             → atT (bindRes tr r (λ x → returnT (h x))) k ≡ (tr k , mapRes h r)
bindRes-mapʳ tr stopped     h k = refl
bindRes-mapʳ tr (returns x) h k = cong (_, returns (h x)) (++-identityʳ (tr k))

-- BIND IS A CONGRUENCE FOR THE RESULT RELATION.
--
-- plan 0.98: this is what an adequacy relation needs in place of 0.97's
-- separate trace-equal / flag-equal / value-related triple. `Res-rel` says the
-- two computations stop together or return related values — ONE fact — and a
-- bind of related heads with related continuations preserves it. The stopped
-- case is `tt` with no continuation to mention, because neither side built
-- one; only the returning case carries the budget transport, and the budgets
-- agree because the head traces do.
bindRes-rel : ∀ {X Y : Set} (R : X → X → Set) (S : Y → Y → Set)
                (tr₁ tr₂ : ℕ → List SigOpEvent) (r₁ r₂ : Res X)
                (f g : X → T Y) (n : ℕ)
            → tr₁ n ≡ tr₂ n
            → Res-rel R r₁ r₂
            → (∀ {a b} → R a b → ∀ j → (projTrace (f a) j ≡ projTrace (g b) j)
                                     × Res-rel S (T.resT (f a)) (T.resT (g b)))
            → (projTrace (bindRes tr₁ r₁ f) n ≡ projTrace (bindRes tr₂ r₂ g) n)
              × Res-rel S (T.resT (bindRes tr₁ r₁ f)) (T.resT (bindRes tr₂ r₂ g))
bindRes-rel R S tr₁ tr₂ stopped     stopped     f g n te rr rk = te , tt
bindRes-rel R S tr₁ tr₂ stopped     (returns _) f g n te ()  rk
bindRes-rel R S tr₁ tr₂ (returns _) stopped     f g n te ()  rk
bindRes-rel R S tr₁ tr₂ (returns a) (returns b) f g n te rr rk =
    cong₂ _++_ te
      (trans (proj₁ (rk rr (n ∸ length (tr₁ n))))
             (cong (projTrace (g b)) (cong (λ es → n ∸ length es) te)))
  , proj₂ (rk rr 0)

-- The TRACE half of `bindRes-mapʳ`, for the many sites whose subject is only
-- the trace. Stopped: nothing was appended. Returns: one `++-identityʳ`.
bindRes-trʳ : ∀ {X Y : Set} (tr : ℕ → List SigOpEvent) (r : Res X)
                (h : X → Y) (k : ℕ)
            → projTrace (bindRes tr r (λ x → returnT (h x))) k ≡ tr k
bindRes-trʳ tr stopped     h k = refl
bindRes-trʳ tr (returns x) h k = ++-identityʳ (tr k)

>>=T-mapʳ : ∀ {X Y : Set} (m : T X) (h : X → Y) (k : ℕ)
          → atT (m >>=T (λ x → returnT (h x))) k ≡ atT (fmapT h m) k
>>=T-mapʳ m h k = bindRes-mapʳ (T.trT m) (T.resT m) h k

------------------------------------------------------------------------
-- Associativity.
--
-- Still true with the threaded budget, but no longer DEFINITIONAL: the
-- left-nested form charges `g` the budget `k ∸ (|es f| + |es g|)` while the
-- right-nested form charges it `(k ∸ |es f|) ∸ |es g|`. Those agree by
-- `∸-+-assoc`, which is exactly the arithmetic the threading introduced —
-- and only in the case where NEITHER earlier computation stopped, because a
-- stop makes both sides the earlier trace outright.
------------------------------------------------------------------------

open import Data.Nat.Properties using (∸-+-assoc)

-- plan 0.98: a two-level split on the RESULTS, and both stopped branches are
-- `refl` — a stop makes each side the earlier trace outright, because no
-- sequel was constructed on either. Only the both-return case carries the
-- budget arithmetic that the threading introduced.
>>=T-assoc : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z) (k : ℕ)
           → atT ((m >>=T f) >>=T g) k ≡ atT (m >>=T (λ x → f x >>=T g)) k
>>=T-assoc m f g k = go (T.resT m)
  where
    go : (r : Res _)
       → atT (bindRes (T.trT (bindRes (T.trT m) r f))
                      (T.resT (bindRes (T.trT m) r f)) g) k
         ≡ atT (bindRes (T.trT m) r (λ x → f x >>=T g)) k
    go stopped     = refl
    go (returns x) = inner (T.resT (f x))
      where
        es-m = T.trT m
        fy   = f x
        inner : (r' : Res _)
              → atT (bindRes (λ n → es-m n ++ T.trT fy (n ∸ length (es-m n)))
                             r' g) k
                ≡ atT (mkT (λ n → es-m n
                              ++ T.trT (bindRes (T.trT fy) r' g)
                                       (n ∸ length (es-m n)))
                           (T.resT (bindRes (T.trT fy) r' g))) k
        inner stopped     = refl
        inner (returns y) =
          cong (_, T.resT (g y))
            (trans (cong (λ j → (es-m k ++ T.trT fy (k ∸ length (es-m k)))
                                  ++ T.trT (g y) j) budget)
                   (++-assoc (es-m k) (T.trT fy (k ∸ length (es-m k)))
                             (T.trT (g y) ((k ∸ length (es-m k))
                                            ∸ length (T.trT fy (k ∸ length (es-m k)))))))
          where
            budget : k ∸ length (es-m k ++ T.trT fy (k ∸ length (es-m k)))
                   ≡ (k ∸ length (es-m k))
                       ∸ length (T.trT fy (k ∸ length (es-m k)))
            budget =
              trans (cong (k ∸_) (length-++ (es-m k) {T.trT fy (k ∸ length (es-m k))}))
                    (sym (∸-+-assoc k (length (es-m k))
                                      (length (T.trT fy (k ∸ length (es-m k))))))

-- Binding a PURE continuation is a map. The `++ []` residual these proofs
-- keep tripping over is exactly this: `⟨ f , g ⟩` ends in `returnT (b , c)`,
-- and under a threaded budget the residual shifts the NEXT continuation's
-- budget too, so rewriting the trace alone no longer suffices.
>>=T-map : ∀ {X Y : Set} (m : T X) (g : X → Y) (k : ℕ)
         → atT (m >>=T (λ x → returnT (g x))) k ≡ atT (fmapT g m) k
bindRes-map : ∀ {X Y : Set} (tr : ℕ → List SigOpEvent) (r : Res X)
              (g : X → Y) (k : ℕ)
            → atT (bindRes tr r (λ x → returnT (g x))) k
              ≡ (tr k , mapRes g r)
bindRes-map tr stopped     g k = refl
bindRes-map tr (returns x) g k = cong (_, returns (g x)) (++-identityʳ (tr k))

>>=T-map m g k = bindRes-map (T.trT m) (T.resT m) g k

-- Binding after a map is binding the composite. `fmapT` touches neither the
-- trace nor the budget, so this is definitional.
fmapT->>=T : ∀ {X Y Z : Set} (g : X → Y) (m : T X) (f : Y → T Z) (k : ℕ)
           → atT (fmapT g m >>=T f) k ≡ atT (m >>=T (λ x → f (g x))) k
-- plan 0.98: no longer definitional — both sides dispatch on the result, so
-- it is the two-case split (each case `refl`).
bindRes-map-fusion : ∀ {X Y Z : Set} (tr : ℕ → List SigOpEvent) (r : Res X)
                     (g : X → Y) (f : Y → T Z) (k : ℕ)
                   → atT (bindRes tr (mapRes g r) f) k
                     ≡ atT (bindRes tr r (λ x → f (g x))) k
bindRes-map-fusion tr stopped     g f k = refl
bindRes-map-fusion tr (returns x) g f k = refl

fmapT->>=T g m f k = bindRes-map-fusion (T.trT m) (T.resT m) g f k

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
                → atT (pure x >>= f) k ≡ atT (f x) k
      identityʳ : ∀ {X : Set} (m : T X) (k : ℕ)
                → atT (m >>= pure) k ≡ atT m k
      assoc     : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z) (k : ℕ)
                → atT ((m >>= f) >>= g) k ≡ atT (m >>= (λ x → f x >>= g)) k

  T-isMonad : IsMonadT
  T-isMonad = record
    { identityˡ = >>=T-identityˡ
    ; identityʳ = >>=T-identityʳ
    ; assoc     = >>=T-assoc
    }

------------------------------------------------------------------------
-- D203: THE EVENT-CONCATENATION STEP.
--
-- `comp-traces-agree`'s comment parked this as "its own piece of work", and
-- it is the same step `⟨ f , g ⟩`'s trace half needs, because both denote a
-- BIND: `projTrace (m >>=T f) n` is definitionally
-- `projTrace m n ++ projTrace (f …) (n ∸ length (projTrace m n))` — a
-- THREADED budget — while the machine side is a flat chain observed with
-- `take k`. These two lemmas are the whole reconciliation.
--
-- Note what is NOT needed: `Bounded`. The obvious route is "the denotation
-- spends at most its budget, so `take k` is the identity on it", but the
-- budgets line up without that, because `minus-take` says the residual
-- budget cannot tell whether the prefix was truncated.
------------------------------------------------------------------------

-- `take` distributes over `++`, with the second half seeing what the first
-- left. Three clauses; the `suc k , []` case is where the `∸ 0` appears.
take-++-split : ∀ {A : Set} (k : ℕ) (as bs : List A)
              → take k (as ++ bs) ≡ take k as ++ take (k ∸ length as) bs
-- `0 ∸ n` does NOT reduce: stdlib's `_∸_` recurses on its SECOND argument, so
-- the zero cases need `0∸n≡0` rather than `refl`.
take-++-split zero    as       bs = sym (cong (λ m → take m bs) (0∸n≡0 (length as)))
take-++-split (suc k) []       bs = refl
take-++-split (suc k) (a ∷ as) bs = cong (a ∷_) (take-++-split k as bs)

-- THE KEY FACT, and the reason no boundedness hypothesis is required: the
-- residual budget is blind to truncation. If `as` is shorter than `k` the
-- `take` does nothing; if it is longer, both sides are `0`.
minus-take : ∀ {A : Set} (k : ℕ) (as : List A)
           → k ∸ length (take k as) ≡ k ∸ length as
minus-take zero    as       = sym (0∸n≡0 (length as))
minus-take (suc k) []       = refl
minus-take (suc k) (a ∷ as) = minus-take k as

-- The form the two consumers want: a flat chain split at `take k`, with the
-- tail's budget computed from the PREFIX — which is what the bind threads.
take-++-threaded : ∀ {A : Set} (k : ℕ) (as bs : List A)
                 → take k (as ++ bs)
                   ≡ take k as ++ take (k ∸ length (take k as)) bs
take-++-threaded k as bs =
  trans (take-++-split k as bs)
        (cong (λ m → take k as ++ take m bs) (sym (minus-take k as)))
