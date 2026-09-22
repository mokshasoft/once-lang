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
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Once.Denotation.Trace using (SigOpEvent)

------------------------------------------------------------------------
-- The monad.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

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

record T (X : Set) : Set where
  constructor mkT
  field
    trT : ℕ → List SigOpEvent
    stT : Stopped
    vlT : X

-- The old shape, for the sites that read all three at a budget.
atT : ∀ {X} → T X → ℕ → List SigOpEvent × Stopped × X
atT m n = (T.trT m n , T.stT m , T.vlT m)

infixl 1 _>>=T_ _>>T_

returnT : ∀ {X} → X → T X
returnT x = mkT (λ _ → []) false x

-- Kleisli sequencing: run `m`, then `f x`, concatenating their events in
-- order. The budget is THREADED: `f` sees what `m` left, `n ∸ length es`.
-- That is what makes `length (projTrace (m >>=T f) n) ≤ n` hold — with a
-- shared `n` each side could independently spend the whole budget, and two
-- sequenced SigOps would emit 2 events at budget 1.
-- A STOPPED computation swallows its continuation's EVENTS. Its value is
-- still the continuation's — it must be, to stay total — but nothing observes
-- a value after a stop, and `Halts` makes it `tt` anyway.
join-es : Stopped → List SigOpEvent → List SigOpEvent → List SigOpEvent
join-es true  es _  = es
join-es false es ef = es ++ ef

join-tr : Stopped → (ℕ → List SigOpEvent) → (ℕ → List SigOpEvent)
        → ℕ → List SigOpEvent
join-tr b tm tf n = join-es b (tm n) (tf (n ∸ length (tm n)))

join-st : Stopped → Stopped → Stopped
join-st true  _ = true
join-st false b = b

_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
m >>=T f =
  let fy = f (T.vlT m)
  in mkT (join-tr (T.stT m) (T.trT m) (T.trT fy))
         (join-st (T.stT m) (T.stT fy))
         (T.vlT fy)

_>>T_ : ∀ {X Y} → T X → T Y → T Y
m >>T k = m >>=T λ _ → k

fmapT : ∀ {X Y} → (X → Y) → T X → T Y
fmapT g m = mkT (T.trT m) (T.stT m) (g (T.vlT m))

-- Emit events (the Writer `tell`).
tell : List SigOpEvent → T ⊤
tell es = mkT (λ k → take k es) false tt

------------------------------------------------------------------------
-- Projections — the observable is `projTrace`.
------------------------------------------------------------------------

-- The trace (effectful SigOp events) at observation depth `n`.
projTrace : ∀ {X} → T X → ℕ → List SigOpEvent
projTrace m n = T.trT m n

-- The value at observation depth `n` (internal; the apex observes only
-- the trace).
-- The budget argument is KEPT and IGNORED: the value does not depend on it.
-- Keeping the arity leaves every `ResultPlace … (valueT … k)` site in plan
-- 0.88's discharged clauses compiling untouched.
valueT : ∀ {X} → T X → ℕ → X
valueT m _ = T.vlT m

-- Did the computation stop? Budget-free, by the shape of `T`.
stoppedT : ∀ {X} → T X → ℕ → Stopped
stoppedT m _ = T.stT m

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
bindAt : ∀ {X Y : Set} → (X → T Y) → ℕ
       → (List SigOpEvent × Stopped × X) → (List SigOpEvent × Stopped × Y)
bindAt f n exr =
  let es = proj₁ exr
      b  = proj₁ (proj₂ exr)
      fy = f (proj₂ (proj₂ exr))
  in ( join-es b es (T.trT fy (n ∸ length es))
     , join-st b (T.stT fy)
     , T.vlT fy )

>>=T-at : ∀ {X Y : Set} (m : T X) (f : X → T Y) (n : ℕ)
        → atT (m >>=T f) n ≡ bindAt f n (atT m n)
>>=T-at m f n = refl

>>=T-cong-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f : X → T Y) (n : ℕ)
             → atT m₁ n ≡ atT m₂ n → atT (m₁ >>=T f) n ≡ atT (m₂ >>=T f) n
>>=T-cong-at f n eq = cong (bindAt f n) eq

-- | The NESTED-bind version: the two binds may differ in BOTH the monadic
--   value and the continuation. `app`-shaped clauses need this — their
--   continuation mentions the argument's denotation, which also changes.
--
--   The continuation premise is pointwise at EVERY budget: `bindAt` applies
--   the continuation at the REMAINDER `n ∸ length (proj₁ r)`, a budget the
--   caller cannot name before `r` is known. Quantifying over it keeps the
--   lemma free of extensionality while covering the budget actually used.
bindAt-cong : ∀ {X Y : Set} (f₁ f₂ : X → T Y) (n : ℕ)
                {r₁ r₂ : List SigOpEvent × Stopped × X}
            → r₁ ≡ r₂
            → (∀ x → f₁ x ≡ f₂ x)
            → bindAt f₁ n r₁ ≡ bindAt f₂ n r₂
bindAt-cong f₁ f₂ n {r} refl fe =
  cong (λ fy → ( join-es (proj₁ (proj₂ r)) (proj₁ r)
                         (T.trT fy (n ∸ length (proj₁ r)))
               , join-st (proj₁ (proj₂ r)) (T.stT fy)
               , T.vlT fy ))
       (fe (proj₂ (proj₂ r)))

>>=T-cong₂-at : ∀ {X Y : Set} {m₁ m₂ : T X} (f₁ f₂ : X → T Y) (n : ℕ)
              → atT m₁ n ≡ atT m₂ n
              → (∀ x → f₁ x ≡ f₂ x)
              → atT (m₁ >>=T f₁) n ≡ atT (m₂ >>=T f₂) n
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
constT-pf : ∀ {X} (es : List SigOpEvent) (st : Stopped) (x : X)
          → PrefixFamily {X} (mkT (λ n → take n es) st x)
constT-pf es st x =
  prefixFamily (λ k → length-take-≤ k es)
               (λ k h → take-sat k es h)
               (λ k → take-coh k es)

tell-pf : ∀ es → PrefixFamily (tell es)
tell-pf es = constT-pf es false tt


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
    -- plan 0.97: the continuation is ONE computation, not a family. `valueT`
    -- ignores its budget now, so `f (valueT m k)` is the same `f` argument at
    -- every `k` — which is the whole reason the stopped case below is a
    -- two-line dispatch rather than a cross-budget argument.
    fy : T _
    fy = f (T.vlT m)

    pfy : PrefixFamily fy
    pfy = pf 0

    lm : ℕ → ℕ
    lm k = length (projTrace m k)

    rest-of : ℕ → List SigOpEvent
    rest-of k = projTrace fy (k ∸ lm k)

    len-split : ∀ k → length (projTrace m k ++ rest-of k) ≡ lm k + length (rest-of k)
    len-split k = length-++ (projTrace m k) {rest-of k}

    -- Each field dispatches on the (budget-free) stop flag. STOPPED: the
    -- composite's trace IS `m`'s, so every obligation is `m`'s own.
    bnd-b : ∀ (b : Stopped) k → length (join-es b (projTrace m k) (rest-of k)) ≤ k
    bnd-b true  k = bnd pm k
    bnd-b false k =
      subst (_≤ k) (sym (len-split k))
        (subst (lm k + length (rest-of k) ≤_) (m+[n∸m]≡n (bnd pm k))
          (+-mono-≤ (≤-refl {lm k}) (bnd pfy (k ∸ lm k))))

    bnd′ : Bounded (m >>=T f)
    bnd′ k = bnd-b (T.stT m) k

    sat-b : ∀ (b : Stopped) k
          → length (join-es b (projTrace m k) (rest-of k)) < k
          → join-es b (projTrace m (suc k)) (rest-of (suc k))
            ≡ join-es b (projTrace m k) (rest-of k)
    sat-b true  k h = sat pm k h
    sat-b false k h = cong₂ _++_ satm restEq
      where
        sum< : lm k + length (rest-of k) < k
        sum< = subst (_< k) (len-split k) h
        lm<k : lm k < k
        lm<k = ≤-trans (s≤s (m≤m+n (lm k) (length (rest-of k)))) sum<
        lf<k′ : length (rest-of k) < k ∸ lm k
        lf<k′ = split-< sum<
        satm : projTrace m (suc k) ≡ projTrace m k
        satm = sat pm k lm<k
        restEq : rest-of (suc k) ≡ rest-of k
        restEq =
          trans (cong (λ es → projTrace fy (suc k ∸ length es)) satm)
                (trans (cong (projTrace fy) (suc∸ (bnd pm k)))
                       (sat pfy (k ∸ lm k) lf<k′))

    sat′ : Saturating (m >>=T f)
    sat′ k h = sat-b (T.stT m) k h

    coh-b : ∀ (b : Stopped) k
          → ∃[ rest ] (join-es b (projTrace m (suc k)) (rest-of (suc k))
                       ≡ join-es b (projTrace m k) (rest-of k) ++ rest)
    coh-b true  k = coh pm k
    coh-b false k = go (m≤n⇒m<n∨m≡n (bnd pm k))
      where
        -- `m` did NOT spend everything: it is finished, and the extra unit of
        -- budget goes to `f`.
        spare : lm k < k
              → ∃[ rest ] (projTrace m (suc k) ++ rest-of (suc k)
                           ≡ (projTrace m k ++ rest-of k) ++ rest)
        spare lm<k with coh pfy (k ∸ lm k)
        ... | r , eqf = r ,
          trans (cong₂ _++_ (sat pm k lm<k)
                   (trans (cong (λ es → projTrace fy (suc k ∸ length es)) (sat pm k lm<k))
                          (trans (cong (projTrace fy) (suc∸ (bnd pm k))) eqf)))
                (sym (++-assoc (projTrace m k) (rest-of k) r))

        -- `m` spent the whole budget: `f` runs at 0 and contributes nothing,
        -- so the composite's trace IS `m`'s and `m`'s coherence carries it.
        spent : lm k ≡ k
              → ∃[ rest ] (projTrace m (suc k) ++ rest-of (suc k)
                           ≡ (projTrace m k ++ rest-of k) ++ rest)
        spent lm≡k with coh pm k
        ... | r , eqm = r ++ tailPart ,
          trans (cong (_++ tailPart) eqm)
          (trans (++-assoc (projTrace m k) r tailPart)
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

            nil-rest : projTrace m k ++ rest-of k ≡ projTrace m k
            nil-rest =
              trans (cong (projTrace m k ++_) empty-at-0)
                    (++-identityʳ (projTrace m k))

        go : lm k < k ⊎ lm k ≡ k
           → ∃[ rest ] (projTrace m (suc k) ++ rest-of (suc k)
                        ≡ (projTrace m k ++ rest-of k) ++ rest)
        go (inj₁ h) = spare h
        go (inj₂ h) = spent h

    coh′ : Coherent (m >>=T f)
    coh′ k = coh-b (T.stT m) k

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
join-st-idʳ : ∀ b → join-st b false ≡ b
join-st-idʳ true  = refl
join-st-idʳ false = refl

join-es-idʳ : ∀ b es → join-es b es [] ≡ es
join-es-idʳ true  es = refl
join-es-idʳ false es = ++-identityʳ es

join-st-assoc : ∀ a b c → join-st (join-st a b) c ≡ join-st a (join-st b c)
join-st-assoc true  _     _ = refl
join-st-assoc false true  _ = refl
join-st-assoc false false _ = refl

-- Left identity: `returnT` spends nothing and stops nothing, so this is
-- definitional even with threading.
>>=T-identityˡ : ∀ {X Y : Set} (x : X) (f : X → T Y) (k : ℕ)
               → atT (returnT x >>=T f) k ≡ atT (f x) k
>>=T-identityˡ x f k = refl

-- Right identity: needs `++-identityʳ` on the trace and `join-st-idʳ` on the
-- flag, since the bind appends `returnT`'s empty trace and its `false`.
>>=T-identityʳ : ∀ {X : Set} (m : T X) (k : ℕ)
               → atT (m >>=T returnT) k ≡ atT m k
>>=T-identityʳ m k =
  cong₂ _,_ (join-es-idʳ (T.stT m) (projTrace m k))
            (cong₂ _,_ (join-st-idʳ (T.stT m)) refl)

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

>>=T-assoc : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z) (k : ℕ)
           → atT ((m >>=T f) >>=T g) k ≡ atT (m >>=T (λ x → f x >>=T g)) k
>>=T-assoc m f g k = cong₂ _,_ tr (cong₂ _,_ st refl)
  where
    fy   = f (T.vlT m)
    gy   = g (T.vlT fy)
    es-m = projTrace m k
    k₁   = k ∸ length es-m
    es-f = projTrace fy k₁
    k₂   = k₁ ∸ length es-f
    es-g = projTrace gy k₂

    budget : k ∸ length (es-m ++ es-f) ≡ k₂
    budget = trans (cong (k ∸_) (length-++ es-m {es-f}))
                   (sym (∸-+-assoc k (length es-m) (length es-f)))

    tr-b : ∀ (a b : Stopped)
         → join-es (join-st a b) (join-es a es-m es-f)
                   (projTrace gy (k ∸ length (join-es a es-m es-f)))
           ≡ join-es a es-m (join-es b es-f (projTrace gy k₂))
    tr-b true  _     = refl
    tr-b false true  = refl
    tr-b false false =
      trans (cong (λ j → (es-m ++ es-f) ++ projTrace gy j) budget)
            (++-assoc es-m es-f es-g)

    tr : projTrace ((m >>=T f) >>=T g) k ≡ projTrace (m >>=T (λ x → f x >>=T g)) k
    tr = tr-b (T.stT m) (T.stT fy)

    st : stoppedT ((m >>=T f) >>=T g) k ≡ stoppedT (m >>=T (λ x → f x >>=T g)) k
    st = join-st-assoc (T.stT m) (T.stT fy) (T.stT gy)

-- Binding a PURE continuation is a map. The `++ []` residual these proofs
-- keep tripping over is exactly this: `⟨ f , g ⟩` ends in `returnT (b , c)`,
-- and under a threaded budget the residual shifts the NEXT continuation's
-- budget too, so rewriting the trace alone no longer suffices.
>>=T-map : ∀ {X Y : Set} (m : T X) (g : X → Y) (k : ℕ)
         → atT (m >>=T (λ x → returnT (g x))) k ≡ atT (fmapT g m) k
>>=T-map m g k =
  cong₂ _,_ (join-es-idʳ (T.stT m) (projTrace m k))
            (cong₂ _,_ (join-st-idʳ (T.stT m)) refl)

-- Binding after a map is binding the composite. `fmapT` touches neither the
-- trace nor the budget, so this is definitional.
fmapT->>=T : ∀ {X Y Z : Set} (g : X → Y) (m : T X) (f : Y → T Z) (k : ℕ)
           → atT (fmapT g m >>=T f) k ≡ atT (m >>=T (λ x → f (g x))) k
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
